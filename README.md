# The mathematical works of T. J. Kaczynski, formalized

A Lean 4 formalization project, with a blueprint paper, covering:

| Source | Topic | Blueprint |
|---|---|---|
| Math. Magazine 41 (1968) | Sutcliffe's digit-reversal conjecture | §A |
| J. Math. Mech. 14 (1965) (review only) | boundary functions in a disk; homeomorphisms | §§E, G |
| Michigan Math. J. 13 (1966) | McMillan's `F_σδ` theorem, cluster sets | §D |
| Dissertation, Michigan (1967) | boundary functions | §§B–G |
| Trans. AMS 141 (1969) | realizing `F_σδ` sets and boundary functions | §§B, F |
| Trans. AMS 137 (1969) | bounded harmonic functions | §H |
| Proc. AMS 23 (1969) | non-Borel set of curvilinear convergence in a cube | §I |

- **[`paper/main.pdf`](paper/main.pdf)**: one self-contained account proving every result, with
  `\lean{}`/`\uses{}` annotations.
- **[`blueprint/map.md`](blueprint/map.md)**: dependency graph and formalization status.
- **`TJK/Defs.lean`, `TJK/MainTheorems.lean`**: the pinned definitions and headline statements.

```sh
python scripts/blueprint.py map     # regenerate blueprint/map.md
python scripts/blueprint.py check   # dangling references, cycles, axioms, pinned statements
```

**Status (2026-10-13):** all 20 pinned headline theorems are proved in Lean and depend on no
`sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound` only).

See `CLAUDE.md` for build instructions and `blueprint/DECISIONS.md` for design decisions.
