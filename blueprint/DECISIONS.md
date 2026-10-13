# Design decisions

## 2026-10-05: blueprint written, reviewed, and initial statements pinned

**Blueprint.** `paper/main.tex` proves all results of the seven sources. Four independent reviews
(sections A–B, C–E, F, G–I + appendix) were run against the sources; they found one error (the
interior of a trapezoid must be taken relative to the strip, and sides with `a_i = b_i = ±∞` must be
excluded — fixed in `def:trapezoid`) and a number of gaps and missing `\uses`, all patched. Notable
points:

1. **1965 paper, Theorem 1** (homeomorphisms of the disk) is known only from its review. The
   blueprint proves a quantitative form (`thm:homeo`): jumps of size `≥ ε` occur at most `2π/ε` times.
2. **Dissertation, Lemma 10** intersects a closed set with an *open* complementary interval, which
   need not give a closed set (counterexample `E₁ = [-1,0]`, `E₂ = {0} ∪ {1/k}`). Repaired with the
   closure of the interval (`lem:th-lemma10`).
3. **Trans. AMS 141, (D)**: the constant `½` in `d(t)` is replaced by `¼` so that the strict inequality
   needed for the sup-defined moduli `d₁, d₂` holds.
4. **Sutcliffe's Theorems 2 and 3**, cited by the Math. Mag. note, are proved with explicit solutions
   (`n+1 = de`, `(a,c,k) = (e-1, n-e, d-1)`). Theorem 2 needs `n ≥ 4` (`n = 3` has no 2-digit
   solution although `4` is composite).

**Lean conventions (pinned in `TJK/Defs.lean`).**

1. Functions are total maps `ℂ → Y`; the domain `Ω` enters only through arcs (`γ \ {x} ⊆ Ω`) and
   `ContinuousOn f Ω`. Limits along an arc are `Tendsto f (𝓝[γ \ {x}] x) (𝓝 q)`.
2. A simple arc is the range of an injective `Path a b`.
3. Function classes on a subset `E` are stated for `E.restrict φ` (a function on the subtype).
4. Baire classes of all orders: inductive `BaireClass : Ordinal.{0} → (X → Y) → Prop`.
5. The Riemann sphere is the unit sphere of `EuclideanSpace ℝ (Fin 3)`, as in the sources.
6. "First category on the circle" is `IsMeagre` of the preimage in the subtype `circle` (every subset
   of the circle is nowhere dense in `ℂ`, so meagreness in `ℂ` would be vacuous).
7. Lebesgue measurability is `NullMeasurable` for `volume`; Borel is `MeasurableSet`.

## 2026-10-12: all 20 headline theorems proved without sorry

Every pinned headline theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
Imported Facts that were proved along the way: the Tietze arc lemma (Hausdorff spaces), the
crosscut theorem (continuous logarithms + homotopy lifting), Banach's theorem and the
Lebesgue–Hausdorff–Banach theorem, the Poisson facts (i)–(iii), a Vitali set, an analytic
non-Borel subset of ℝ. The cube lemma's dependence on Kierst's theorem and on normal functions was
removed by a new elementary proof (`lem:cube-lemma-elementary`, independently reviewed). The facts
`kierst`, `asymptotic_is_point_asymptotic`, `bagemihl_ambiguous_countable` (used only by a side
remark) and `jordan_accessible` remain as unused or side-remark `sorry`s.
