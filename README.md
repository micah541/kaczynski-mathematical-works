# The Complete Mathematical Works of Theodore J. Kaczynski, formalized in Lean 4

This repository formalizes every published mathematical paper of Theodore J. Kaczynski, together
with his doctoral dissertation (1964–1969). Most of them are about how functions in the disk and the
half-plane behave at the boundary; the first is a new proof of Wedderburn's theorem. (Not included:
three short problems he posed in the *American Mathematical Monthly* and *Mathematics Magazine*.)
It contains:

- a **blueprint**: one self-contained mathematical document that proves every result of these works;
- a **Lean 4 formalization** of all of it (about 22,400 lines, on Mathlib);
- an **errata** ([`ERRATA.md`](ERRATA.md)) recording where the published proofs needed a correction,
  relied on outside theorems, or were replaced by different arguments.

## Status

All **21 pinned headline theorems** are proved, and no declaration in the project uses `sorry`.
Every headline theorem depends only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). The blueprint has 141 items, all formalized.

The results the sources quote from the literature are proved here, or the argument that used them
is replaced:
- the crosscut theorem (a form of the Jordan curve theorem for arcs across the disk);
- Tietze's arc theorem;
- the Poisson integral facts;
- Banach's theorem on Baire classes;
- an analytic non-Borel set;
- Bagemihl's ambiguous-point theorem for continuous functions.

Two deep theorems the sources use, the full Jordan curve theorem and Kierst's theorem, are avoided by
direct arguments (see [`ERRATA.md`](ERRATA.md), §2). Wedderburn's theorem is proved by Kaczynski's
argument, without Mathlib's own proof of it (Witt's), which is switched off in that file.

## The sources

| Source | Topic | Blueprint | Lean |
|---|---|---|---|
| *Amer. Math. Monthly* 71 (1964) | a group-theoretic proof of Wedderburn's theorem | §J | [`Wedderburn.lean`](TJK/Wedderburn.lean) |
| *Math. Magazine* 41 (1968) | Sutcliffe's digit-reversal conjecture | §A | [`Sutcliffe.lean`](TJK/Sutcliffe.lean) |
| *J. Math. Mech.* 14 (1965), known only from its review | boundary functions in the disk; homeomorphisms | §§E, G | [`BoundaryFn/`](TJK/BoundaryFn), [`Discont/`](TJK/Discont) |
| *Michigan Math. J.* 13 (1966) | McMillan's F<sub>σδ</sub> theorem; cluster sets | §D | [`McMillan/`](TJK/McMillan) |
| Dissertation, *Boundary functions*, Michigan (1967) | Baire classes of boundary functions | §§B–G, App. A | [`Baire/`](TJK/Baire), [`Discont/`](TJK/Discont), [`Variant.lean`](TJK/Variant.lean) |
| *Trans. AMS* 141 (1969) | realizing F<sub>σδ</sub> sets and boundary functions | §§B, F | [`Construct/`](TJK/Construct) |
| *Trans. AMS* 137 (1969) | boundary functions of bounded harmonic functions | §H | [`Harmonic/`](TJK/Harmonic) |
| *Proc. AMS* 23 (1969) | a non-Borel set of curvilinear convergence in a cube | §I | [`Cube/`](TJK/Cube) |

Shared plane topology (arcs, crosscuts) is in [`Plane/`](TJK/Plane).

## Headline theorems

The trusted statements are in [`TJK/Defs.lean`](TJK/Defs.lean) (definitions) and
[`TJK/MainTheorems.lean`](TJK/MainTheorems.lean) (statements). They are frozen by
[`blueprint/pinned.json`](blueprint/pinned.json), and `scripts/blueprint.py check` fails if any of them
changes. They include:

- **McMillan's theorem** and Kaczynski's generalization to cluster sets: the set of curvilinear
  convergence of a continuous function in the disk is F<sub>σδ</sub>.
- **Realization:** every F<sub>σδ</sub> subset of ℝ is the set of curvilinear convergence of a
  bounded continuous function in the half-plane. This answers McMillan's problem, with prescribed
  boundary functions (Trans. AMS 141, (F)).
- **Baire classes:** boundary functions are of honorary Baire class 2; a boundary function of a
  Baire class ξ function is of class ξ + 1 (dissertation, Theorem 8).
- **Homeomorphisms of the disk:** their boundary functions are continuous off a countable set
  (1965, Theorem 1).
- **Measure:** there are pairwise disjoint arcs, one at each point of ℝ, whose union is null
  (dissertation, Theorem 10), with its corollaries.
- **Bounded harmonic functions:** a bounded harmonic function with a boundary function that is not of
  Baire class 1, answering Bagemihl–Piranian's Problem 5. Also a first-category theorem for harmonic
  functions with bounded integral means.
- **The cube:** a bounded continuous function in a cube whose set of curvilinear convergence is not
  Borel.
- **Wedderburn's theorem**, by Kaczynski's proof: every finite division ring is commutative.
- **Sutcliffe's conjecture:** if base `n` has a 3-digit number that is multiplied by an integer when
  its digits are reversed, it also has a 2-digit one.

## Repository layout

- [`paper/main.pdf`](paper/main.pdf): the blueprint, typeset (source: `paper/main.tex`, `paper/sections/`). Each numbered item has `\lean{...}` (the
  Lean declarations) and `\uses{...}` (its dependencies). Appendix B maps every result of the
  sources to its blueprint item.
- `blueprint/map.md`: the generated dependency graph and per-item status.
- `blueprint/DECISIONS.md`: the design log, covering how statements were encoded and the repairs.
- `ERRATA.md`: the divergences from the published texts.
- `TJK/`: the Lean sources. `TJK.lean` imports everything.
- `scripts/blueprint.py`: blueprint tooling (`map`, `check`, `pin`).

## Building

You need [elan](https://github.com/leanprover/elan) (the Lean toolchain manager). The toolchain is
pinned in `lean-toolchain` (Lean v4.33.1) and Mathlib in `lakefile.toml` (v4.33.1).

```sh
git clone <this repository>
cd <repository>
lake exe cache get     # download prebuilt Mathlib (otherwise Mathlib takes hours to compile)
lake build             # build the formalization
```

A full build needs several GB of memory. On a small machine, limit parallelism with
`LEAN_NUM_THREADS=2`.

To check the axioms yourself, create a file containing

```lean
import TJK
#print axioms TJK.Harmonic.exists_bounded_harmonic_boundaryFn_not_baireOne
```

and run `lake env lean <file>`. Do the same for any declaration of `TJK/MainTheorems.lean`.

The blueprint tooling needs Python 3:

```sh
python scripts/blueprint.py check   # references, cycles, axioms, pinned statements
python scripts/blueprint.py map     # regenerate blueprint/map.md
```

To typeset the blueprint, run `latexmk -pdf main.tex` in `paper/`.

## How this was made

The blueprint and the formalization were written by Claude, Anthropic's AI model, working as an
orchestrator of Lean-writing agents under the direction of the repository owner. The agent
instructions are in [`CLAUDE.md`](CLAUDE.md). Every proof is checked by Lean. The blueprint's prose
proofs were also reviewed against the sources, and that review found the errors listed in
[`ERRATA.md`](ERRATA.md).

## License

Apache License 2.0 (see [`LICENSE`](LICENSE)), the license used by Mathlib. The original papers are
not included in this repository.
