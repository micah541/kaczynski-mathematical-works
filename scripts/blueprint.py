#!/usr/bin/env python3
"""Blueprint map for the TJK project (the works of T. J. Kaczynski).

The companion paper (paper/main.tex) is the single source of truth for the
proof structure. Every numbered item carries leanblueprint-style annotations:

    \\label{lem:garding}
    \\lean{ShortTime.garding}          Lean declaration(s) formalizing the item
    \\uses{def:class, def:sobolev}     dependencies of the statement
    ... and \\uses{...} inside the proof for dependencies of the proof
    \\source{...}                      provenance of an imported Fact

Subcommands
    map    regenerate blueprint/map.md (dependency graph + status table)
    check  validate the map (dangling refs, cycles), forbid `axiom`s in the
           Lean sources, and verify that pinned statements are unchanged
    pin    record the current statement text of the given Lean declarations
           in blueprint/pinned.json (run only after the statements are approved)

Usage
    python scripts/blueprint.py map
    python scripts/blueprint.py check
    python scripts/blueprint.py pin TJK.Sutcliffe.two_digit_of_three_digit
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper" / "main.tex"
LEAN_DIR = ROOT / "TJK"
MAP_MD = ROOT / "blueprint" / "map.md"
PINNED = ROOT / "blueprint" / "pinned.json"

ENVS = ("definition", "lemma", "proposition", "theorem", "corollary", "fact", "mainthm")
LAYERS = {
    "sec:arith": "A Sutcliffe's problem",
    "sec:baire": "B Baire functions",
    "sec:plane": "C Arcs and crosscuts",
    "sec:cc": "D Curvilinear convergence",
    "sec:bf": "E Boundary functions",
    "sec:construct": "F Constructions",
    "sec:discont": "G Discontinuous functions",
    "sec:harmonic": "H Harmonic functions",
    "sec:cube": "I The cube",
    "app:variants": "Z Variants",
}


# --------------------------------------------------------------------------
# Paper parsing
# --------------------------------------------------------------------------
@dataclass
class Node:
    label: str
    kind: str
    title: str
    layer: str
    lean: list[str] = field(default_factory=list)
    uses_stmt: list[str] = field(default_factory=list)
    uses_proof: list[str] = field(default_factory=list)
    source: str = ""

    @property
    def uses(self) -> list[str]:
        seen: list[str] = []
        for u in self.uses_stmt + self.uses_proof:
            if u not in seen:
                seen.append(u)
        return seen


def _arg(cmd: str, text: str) -> list[str]:
    out: list[str] = []
    for m in re.finditer(r"\\" + cmd + r"\{([^}]*)\}", text):
        out += [s.strip() for s in m.group(1).split(",") if s.strip()]
    return out


def parse_paper() -> dict[str, Node]:
    tex = PAPER.read_text(encoding="utf-8")

    def inline(m: re.Match) -> str:
        f = PAPER.parent / (m.group(1) if m.group(1).endswith(".tex") else m.group(1) + ".tex")
        return f.read_text(encoding="utf-8")

    for _ in range(3):
        tex = re.sub(r"\\input\{([^}]*)\}", inline, tex)
    tex = re.sub(r"(?<!\\)%.*", "", tex)  # strip comments
    nodes: dict[str, Node] = {}
    order: list[str] = []

    # section markers -> layer
    markers = [(m.start(), m.group(1)) for m in re.finditer(r"\\label\{((?:sec|app):[^}]*)\}", tex)]

    def layer_at(pos: int) -> str:
        cur = ""
        for p, lab in markers:
            if p > pos:
                break
            if lab in LAYERS:
                cur = LAYERS[lab]
        return cur or "Intro"

    env_re = re.compile(
        r"\\begin\{(" + "|".join(ENVS) + r")\}(\[[^\[\]]*(?:\[[^\]]*\][^\[\]]*)*\])?(.*?)\\end\{\1\}",
        re.S,
    )
    for m in env_re.finditer(tex):
        kind, title, body = m.group(1), (m.group(2) or "")[1:-1], m.group(3)
        lab = re.search(r"\\label\{([^}]*)\}", body)
        if not lab:
            continue
        label = lab.group(1)
        if layer_at(m.start()) == "Intro":
            continue
        title = re.sub(r"\\cite(\[[^\]]*\])?\{[^}]*\}", "", title)
        title = title.replace("\\aa ", "å").replace("\\aa", "å").replace("--", "–").replace("~", " ")
        title = re.sub(r"[{}\\]", "", title).strip()
        n = Node(label, "theorem" if kind == "mainthm" else kind, title, layer_at(m.start()),
                 lean=_arg("lean", body), uses_stmt=_arg("uses", body),
                 source=" ".join(re.findall(r"\\source\{([^}]*)\}", body)))
        nodes[label] = n
        order.append(label)

        # a proof immediately following the statement belongs to it
        rest = tex[m.end():]
        pm = re.match(r"\s*\\begin\{proof\}(\[[^\]]*\])?(.*?)\\end\{proof\}", rest, re.S)
        if pm and not (pm.group(1) and "\\ref" in pm.group(1)):
            n.uses_proof += _arg("uses", pm.group(2))

    # detached proofs: \begin{proof}[Proof of Theorem~\ref{thm:A}]
    for pm in re.finditer(r"\\begin\{proof\}\[[^\]]*\\ref\{([^}]*)\}[^\]]*\](.*?)\\end\{proof\}", tex, re.S):
        if pm.group(1) in nodes:
            nodes[pm.group(1)].uses_proof += _arg("uses", pm.group(2))

    return {k: nodes[k] for k in order}


# --------------------------------------------------------------------------
# Lean scanning
# --------------------------------------------------------------------------
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\s+([^\s(:{\[]+)",
    re.M,
)


@dataclass
class Decl:
    name: str
    kind: str
    file: str
    statement: str
    has_sorry: bool
    block: str = ""
    uses_sorry: bool = False  # transitively, through other project declarations


IDENT_RE = re.compile(r"[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff\u2080-\u209c!?]*")


def propagate_sorry(decls: dict[str, "Decl"]) -> None:
    """Mark every declaration whose text mentions, directly or transitively, a project declaration
    with `sorry`. References are found textually by the last component of the name, so the result
    errs on the side of reporting a dependence."""
    by_short: dict[str, list[str]] = {}
    for full in decls:
        by_short.setdefault(full.split(".")[-1], []).append(full)
    refs: dict[str, set[str]] = {}
    for full, d in decls.items():
        toks = {t.split(".")[-1] for t in IDENT_RE.findall(d.block.replace(".", " ."))}
        toks |= {t.lstrip(".") for t in re.findall(r"\.[A-Za-z_][\w']*", d.block)}
        refs[full] = {r for t in toks for r in by_short.get(t, []) if r != full}
    tainted = {n for n, d in decls.items() if d.has_sorry}
    changed = True
    while changed:
        changed = False
        for n in decls:
            if n not in tainted and refs[n] & tainted:
                tainted.add(n)
                changed = True
    for n in tainted:
        decls[n].uses_sorry = True


def scan_lean() -> dict[str, Decl]:
    decls: dict[str, Decl] = {}
    if not LEAN_DIR.exists():
        return decls
    for path in sorted(LEAN_DIR.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        text_nc = re.sub(r"/-.*?-/", lambda m: " " * len(m.group(0)), text, flags=re.S)
        text_nc = re.sub(r"--.*", lambda m: " " * len(m.group(0)), text_nc)
        # namespace tracking
        ns_events = [(m.start(), "push", m.group(1)) for m in re.finditer(r"^namespace\s+(\S+)", text_nc, re.M)]
        ns_events += [(m.start(), "pop", m.group(1) or "") for m in re.finditer(r"^end(?:\s+(\S+))?\s*$", text_nc, re.M)]
        ns_events.sort()
        matches = list(DECL_RE.finditer(text_nc))
        for i, m in enumerate(matches):
            stack: list[str] = []
            for pos, ev, name in ns_events:
                if pos > m.start():
                    break
                if ev == "push":
                    stack += name.split(".")
                elif stack and (not name or stack[-len(name.split(".")):] == name.split(".")):
                    del stack[-max(1, len(name.split("."))) if name else -1:]
            short = m.group(2)
            full = short if short.startswith("_root_.") else ".".join(stack + [short])
            full = full.replace("_root_.", "")
            end = matches[i + 1].start() if i + 1 < len(matches) else len(text_nc)
            block = text_nc[m.start():end]
            # For theorems the pinned text is the statement (proofs may change freely).
            # For definitions, structures, etc. the body *is* the meaning, so pin all of it.
            stmt = block.split(":=", 1)[0] if m.group(1) in ("theorem", "lemma") else block
            # the declaration's own name is in the header; references are searched after it
            decls[full] = Decl(full, m.group(1), str(path.relative_to(ROOT)).replace("\\", "/"),
                               " ".join(stmt.split()), bool(re.search(r"\bsorry\b", block)),
                               block[m.end() - m.start():])
    propagate_sorry(decls)
    return decls


def status(node: Node, decls: dict[str, Decl]) -> str:
    if node.kind == "fact":
        return "imported"
    if not node.lean:
        return "unmapped"
    present = [decls.get(n) for n in node.lean]
    if not any(present):
        return "planned"
    if not all(present):
        return "partial"
    if any(d.has_sorry for d in present):
        return "sorry"
    if any(d.uses_sorry for d in present):
        return "conditional"
    return "defined" if node.kind == "definition" else "proved"


STATUS_STYLE = {
    "proved": "fill:#1f8a4c,color:#fff,stroke:#146236",
    "defined": "fill:#b7e1c5,color:#123,stroke:#4c9a68",
    "sorry": "fill:#f2c14e,color:#222,stroke:#b8902e",
    "conditional": "fill:#d9ead3,color:#222,stroke:#b8902e,stroke-dasharray: 4 2",
    "partial": "fill:#f7dd9b,color:#222,stroke:#b8902e",
    "planned": "fill:#eeeeee,color:#333,stroke:#999",
    "imported": "fill:#dbe8f6,color:#1c3a5e,stroke:#6b8fb8",
    "unmapped": "fill:#fbe3e3,color:#6b1c1c,stroke:#c77",
}
STATUS_TEXT = {
    "proved": "proved (no `sorry`)",
    "defined": "definition written in Lean",
    "sorry": "stated in Lean, proof is `sorry`",
    "conditional": "proof written, but it uses a declaration that still has `sorry`",
    "partial": "some Lean declarations exist",
    "planned": "Lean name reserved, not yet stated",
    "imported": "imported fact (Mathlib / library)",
    "unmapped": "no Lean name assigned",
}


def mid(label: str) -> str:
    return re.sub(r"[^A-Za-z0-9]", "_", label)


def render_map(nodes: dict[str, Node], decls: dict[str, Decl]) -> str:
    st = {k: status(n, decls) for k, n in nodes.items()}
    counts: dict[str, int] = {}
    for s in st.values():
        counts[s] = counts.get(s, 0) + 1

    lines = [
        "# Blueprint map",
        "",
        "<!-- Generated by `python scripts/blueprint.py map` from the annotations in",
        "     paper/main.tex and the declarations in TJK/. Do not edit by hand. -->",
        "",
        "Every node is a numbered item of the [companion paper](../paper/main.pdf). "
        "Arrows point from an item to the items it depends on. "
        "Colours give the formalization status.",
        "",
        "| Status | Meaning | Count |",
        "|---|---|---|",
    ]
    for s in ("proved", "defined", "conditional", "sorry", "partial", "planned", "imported",
              "unmapped"):
        if counts.get(s):
            lines.append(f"| `{s}` | {STATUS_TEXT[s]} | {counts[s]} |")
    lines += ["", "```mermaid", "flowchart BT"]
    by_layer: dict[str, list[str]] = {}
    for k, n in nodes.items():
        by_layer.setdefault(n.layer, []).append(k)
    for layer, labs in by_layer.items():
        lines.append(f'  subgraph {mid(layer)}["{layer}"]')
        for k in labs:
            n = nodes[k]
            name = n.title or n.kind.capitalize()
            lines.append(f'    {mid(k)}["{k}<br/><small>{name}</small>"]')
        lines.append("  end")
    for k, n in nodes.items():
        for u in n.uses:
            if u in nodes:
                lines.append(f"  {mid(k)} --> {mid(u)}")
    for s, style in STATUS_STYLE.items():
        members = [mid(k) for k in nodes if st[k] == s]
        if members:
            lines.append(f"  classDef {s} {style}")
            lines.append(f"  class {','.join(members)} {s}")
    lines += ["```", ""]

    for layer, labs in by_layer.items():
        lines += [f"## {layer}", "", "| Item | Kind | Lean | Depends on | Status |", "|---|---|---|---|---|"]
        for k in labs:
            n = nodes[k]
            lean = "<br/>".join(
                f"`{x}`" + (f" ([src]({'../' + decls[x].file}))" if x in decls else "") for x in n.lean
            ) or (n.source and f"*{n.source}*") or ""
            deps = ", ".join(f"`{u}`" for u in n.uses)
            title = f"{k}<br/>*{n.title}*" if n.title else k
            lines.append(f"| {title} | {n.kind} | {lean} | {deps} | `{st[k]}` |")
        lines.append("")
    return "\n".join(lines)


# --------------------------------------------------------------------------
# Checks and pinning
# --------------------------------------------------------------------------
def validate(nodes: dict[str, Node]) -> list[str]:
    errs = []
    for k, n in nodes.items():
        for u in n.uses:
            if u not in nodes:
                errs.append(f"{k}: \\uses unknown label {u!r}")
    # cycle detection
    state: dict[str, int] = {}

    def dfs(k: str, path: list[str]) -> None:
        state[k] = 1
        for u in nodes[k].uses:
            if u not in nodes:
                continue
            if state.get(u) == 1:
                errs.append("cycle: " + " -> ".join(path + [k, u]))
            elif not state.get(u):
                dfs(u, path + [k])
        state[k] = 2

    for k in nodes:
        if not state.get(k):
            dfs(k, [])
    return errs


def digest(stmt: str) -> str:
    return hashlib.sha256(stmt.encode()).hexdigest()[:16]


def cmd_check(nodes: dict[str, Node], decls: dict[str, Decl]) -> int:
    errs = validate(nodes)
    for d in decls.values():
        if d.kind == "axiom":
            errs.append(f"{d.file}: `axiom {d.name}` is not allowed")
    if PINNED.exists():
        pinned = json.loads(PINNED.read_text(encoding="utf-8"))
        for name, entry in pinned.items():
            d = decls.get(name)
            if d is None:
                errs.append(f"pinned declaration {name} no longer exists")
            elif digest(d.statement) != entry["sha"]:
                errs.append(f"pinned statement of {name} changed (was: {entry['statement']})")
    sorries = sorted(d.name for d in decls.values() if d.has_sorry)
    print(f"{len(nodes)} blueprint items, {len(decls)} Lean declarations, {len(sorries)} with sorry")
    for e in errs:
        print("ERROR:", e)
    return 1 if errs else 0


def cmd_pin(names: list[str], decls: dict[str, Decl]) -> int:
    pinned = json.loads(PINNED.read_text(encoding="utf-8")) if PINNED.exists() else {}
    for name in names:
        d = decls.get(name)
        if d is None:
            print("unknown declaration:", name)
            return 1
        pinned[name] = {"sha": digest(d.statement), "statement": d.statement, "file": d.file}
        print("pinned", name)
    PINNED.write_text(json.dumps(pinned, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


def main(argv: list[str]) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    cmd = argv[1] if len(argv) > 1 else "map"
    nodes, decls = parse_paper(), scan_lean()
    if cmd == "map":
        errs = validate(nodes)
        for e in errs:
            print("WARNING:", e)
        MAP_MD.parent.mkdir(exist_ok=True)
        MAP_MD.write_text(render_map(nodes, decls), encoding="utf-8", newline="\n")
        print(f"wrote {MAP_MD.relative_to(ROOT)} ({len(nodes)} items)")
        return 0
    if cmd == "check":
        return cmd_check(nodes, decls)
    if cmd == "pin":
        return cmd_pin(argv[2:], decls)
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
