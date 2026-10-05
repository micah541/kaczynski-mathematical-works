# Working on this repository

This project formalizes, in Lean 4, the mathematical works of T. J. Kaczynski: the 1967 dissertation
*Boundary functions*, five papers (J. Math. Mech. 1965 — known only via its review —, Michigan Math. J.
1966, Trans. AMS 137 and 141 (1969), Proc. AMS 23 (1969)) and the Math. Magazine note on Sutcliffe's
problem (1968). The source PDFs are in this directory; OCR text is in `txt/`, page images in `img/`
(both git-ignored).

## Sources of truth

- **`paper/main.tex`** (sections in `paper/sections/`) is the blueprint: one document proving every
  result. Every numbered item has `\lean{...}` and `\uses{...}`. Imported classical results are
  `fact` items with `\source{}`. Appendix B maps each source result to its blueprint item.
- **`blueprint/map.md`** is generated: `python scripts/blueprint.py map`. Never edit by hand.
- **`blueprint/pinned.json`** freezes the trusted statements: `TJK/Defs.lean`, the headline theorems
  in `TJK/MainTheorems.lean`, and the Sutcliffe definitions and main theorems.
- **`blueprint/DECISIONS.md`** logs judgment calls in the formal statements.

## Hard rules

1. **Never change a pinned declaration.** `python scripts/blueprint.py check` fails if you do. If a
   pinned definition is shown to be wrong, fix it, re-pin with `python scripts/blueprint.py pin <Decl>`,
   record the reason in `blueprint/DECISIONS.md`, and say so in your summary. Never weaken a theorem to
   make it provable.
2. **No new axioms.** No `axiom`, `native_decide`, `implemented_by`, `set_option maxHeartbeats 0`.
   Imported classical facts (Jordan curve theorem, Kierst's theorem, …) are ordinary Lean theorems
   whose proof may be `sorry`; results depending on them show as `conditional` in the map.
3. **Keep the paper and Lean in sync**: use the `\lean{}` names, fix the paper if a proof there is
   wrong, rerun `python scripts/blueprint.py map`.
4. Before finishing a unit of work, the touched files compile and `blueprint.py check` passes.

## Building on this machine (16 GB RAM, Windows)

- `.lake/packages` is a directory junction to `../MM/.lake/packages` (Mathlib v4.33.1, already
  built). Do not run `lake update`.
- Cap parallelism: `LEAN_NUM_THREADS=4`. Run at most one Lean build or check process at a time.
- **Fast checks: the shared REPL server.** `python scripts/leanrepl.py serve` (one instance only), then
  `python scripts/leanrepl.py import Mathlib` (env 0, about 5 minutes), then check a file with
  `python scripts/leanrepl.py check FILE --env N` (imports are stripped, so the environment must
  already contain them). `TJK/Defs.lean` checked in env 0 yields the env for files importing it. The
  server serializes requests, so several workers may share it.
- **Reliable per-file compile:** `bash scripts/compile1.sh TJK/Defs.lean TJK/Foo.lean` (writes
  `.olean`s like `lake build`).
- Use `PYTHONIOENCODING=utf-8` when running `blueprint.py` from bash (names contain `σ`, `δ`).

## Layout

- `TJK/Defs.lean` — trusted definitions (pinned).
- `TJK/MainTheorems.lean` — headline statements (pinned).
- `TJK/Sutcliffe.lean` — Section A, complete.
- Further files follow the blueprint sections: `TJK/Baire/`, `TJK/Plane/`, `TJK/McMillan/`,
  `TJK/BoundaryFn/`, `TJK/Construct/`, `TJK/Discont/`, `TJK/Harmonic/`, `TJK/Cube/`.

## Order of work

Pick an item of `blueprint/map.md` whose dependencies are `defined` or `proved`. State it in Lean
(with `sorry`) before proving items that use it. Sections B (Baire functions), F's geometry
(`lem:region-geometry`, special families, `thm:construct-C`) and G's measure theory
(`lem:th-lemma25`, `thm:th-thm9`) need no imported facts and are the natural next targets.
