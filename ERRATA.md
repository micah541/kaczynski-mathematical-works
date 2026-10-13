# Errata and divergences

To formalize the mathematical works of Theodore J. Kaczynski in Lean 4, we wrote a blueprint
([`paper/main.tex`](paper/main.tex)) that proves every result in full. This file lists each place
where what we proved departs from the published text. Some are errors that needed a correction.
Some are steps the sources cite without proof, which we proved or routed around. Some are arguments
we replaced with different ones. The rest are items we did not formalize. None of the corrections
affects a main theorem.

Each entry names its blueprint label and Lean declaration. The design log is
[`blueprint/DECISIONS.md`](blueprint/DECISIONS.md).

**Sources.** *Math. Mag.* 41 (1968); *J. Math. Mech.* 14 (1965), known to us only through its review;
*Michigan Math. J.* 13 (1966); the dissertation *Boundary functions* (University of Michigan, 1967);
*Trans. AMS* 137 (1969); *Trans. AMS* 141 (1969); *Proc. AMS* 23 (1969).

## 1. Corrections

### 1.1 Complementary intervals give non-closed sets
*Dissertation, Lemma 10* (every F<sub>σ</sub> set is the union of a special family).

- **Source.** At each stage the new sets are `I ∩ E_{s+1}`, where `I` runs over the open
  complementary intervals of the earlier closed sets. These sets are claimed to be closed.
- **Problem.** A closed set intersected with an open interval need not be closed. Take
  `E₀ = [−1, 0]` and `E₁ = {0} ∪ {1/k : k ≥ 1}`, which split at 0. The complementary interval
  `(0, ∞)` of `E₀` gives `{1/k : k ≥ 1}`, which is not closed.
- **Fix.** Use the closed interval: `Ī ∩ E_{s+1}`. We also replaced the subsequence argument for
  "`E_{s+1}` meets only finitely many complementary intervals" with a shorter argument that counts
  classes.
- Blueprint `lem:th-lemma10`; Lean `TJK.Variant.exists_thesisSpecial_of_isFσ`.

### 1.2 The interior of a trapezoid
*Dissertation, definition of trapezoids before Lemmas 23–24 and Theorem 9.*

- **Source.** A trapezoid is any set between a closed trapezoid `T` and its interior. Its area is
  claimed to be half the sum of the lengths of its traces on `y = 0` and `y = 1`.
- **Problem.** The interior is taken in the plane, so it misses the two horizontal edges, and the
  area formula fails for sets that omit them. With infinite parameters, the degenerate sides
  `aᵢ = bᵢ = ±∞` also break the formula.
- **Fix.** Take the interior relative to the strip `0 ≤ y ≤ 1`, and exclude sides with
  `aᵢ = bᵢ = ±∞`. Theorem 9 is unaffected, because its proof only uses closed trapezoids with finite
  parameters.
- Blueprint `def:trapezoid`; Lean `TJK.Discont.closedTrapezoid`, `volume_closedTrapezoid`.

### 1.3 A constant in the modulus `d(t)`
*Trans. AMS 141, proof of (D)* (realizing an F<sub>σδ</sub> set with a prescribed boundary function).

- **Source.** The proof defines `d(t)` from the moduli of continuity `d₁, d₂` with a factor ½.
- **Problem.** `d₁` and `d₂` are defined as suprema. With the factor ½, the estimate on `|p − q|`
  reaches the supremum itself. The definition of the supremum then gives nothing, because a strict
  inequality is needed.
- **Fix.** Replace ½ by ¼: `d(t) = min{¼·D(t/2), t/4}`. The rest of the argument is unchanged.
- Blueprint `thm:construct-D`; Lean `TJK.Construct.exists_f_Q`.

### 1.4 Sutcliffe's Theorem 2 needs `n ≥ 4`
*Math. Mag. 41, as cited in the proofs of the Theorem and Corollary.*

- **Source.** The note cites Sutcliffe's Theorem 2: base `n` has a 2-digit solution exactly when
  `n + 1` is composite.
- **Problem.** The direction "`n + 1` composite ⇒ a 2-digit solution exists" fails for `n = 3`:
  4 is composite, but base 3 has no 2-digit solution.
- **Fix.** Kaczynski's own results are not affected. He treats `n = 2, 3` separately (his Lemma 2),
  and states his Corollary for `n > 3`. We prove both directions of Sutcliffe's Theorem 2 for
  `n ≥ 4`, with explicit solutions `(a, c, k) = (e − 1, n − e, d − 1)` when `n + 1 = de`.
- Blueprint `prop:sut-two-composite`, `prop:sut-explicit`; Lean `TJK.Sutcliffe`.

## 2. Steps that rely on outside theorems

The sources quote these results without proof. In each case we either proved the result or
replaced the argument that uses it.

### 2.1 The Jordan curve theorem, with accessibility
*Trans. AMS 137, Lemma* (used for the bounded harmonic counterexample).
The Lemma covers general Jordan domains along disjoint arcs of the circle. It glues their boundaries
into one Jordan curve and invokes the Jordan curve theorem, including accessibility of every
boundary point. For the domains actually built in the paper, we construct the accessing arc
directly: `s ↦ (1 − s)·e^{iθ(s)}`, bending around each domain that blocks the radius. This uses
only the separation property IV of the paper's intervals. The Jordan curve theorem is not used, and
the Lemma in its general form is not formalized.
Blueprint `lem:ha-access`; Lean `TJK.Harmonic.Intervals.accessible`.

### 2.2 Kierst's theorem and normal functions
*Proc. AMS 23, Lemma* (a continuous function on the half-plane with a non-Borel set of asymptotic
values). The proof combines Kierst's theorem on asymptotic values of holomorphic functions with the
Lehto–Virtanen and Bagemihl–Seidel results on normal functions. The paper remarks that an elementary
proof exists, but omits it as a "messy construction". We give a new elementary proof that uses only
the existence of an analytic non-Borel set. It builds the function on a binary tree of segments in
the half-plane. Kaczynski's argument is kept as a remark and is not formalized.
Blueprint `lem:cube-lemma-elementary`; Lean `TJK.Cube.Elementary.exists_s'`.

### 2.3 Bagemihl's ambiguous point theorem
*Michigan Math. J. 13, remark after Corollary 4.* The remark uses Bagemihl's theorem (1955): for an
arbitrary function on the disk, only countably many boundary points have two arcs with different
limits. The function in the remark is continuous, and that case has a short proof. Two disjoint
connected open subsets of the disk share at most three accessible boundary points, by the crosscut
theorem. Classifying the ambiguous points by countably many such pairs gives countability. The
general theorem is not needed and is not formalized.
Blueprint `lem:two-domains`, `fact:bagemihl`; Lean `TJK.accessible_two_domains`,
`TJK.ambiguous_countable`.

### 2.4 Other quoted results, now proved
- **Plane topology.** The crosscut theorem, proved via continuous logarithms and homotopy lifting,
  replaces the dissertation's "Figure 5" argument and the monotonicity of first hitting points.
  Tietze's theorem that path-connected Hausdorff spaces are arc-connected is also proved.
- **Analysis.** We proved the Poisson-integral facts: boundedness, boundary limits at continuity
  points, and the representation of harmonic functions whose `Lᵖ` means are bounded (`p > 1`). We
  also proved Banach's and the Lebesgue–Hausdorff–Banach theorems on Baire classes.
- **Set theory.** We proved that an analytic non-Borel subset of ℝ exists (via a universal analytic
  set and diagonalization) and that a Vitali set exists.
- **Trans. AMS 141.** Step (B)(III) cites a Bagemihl–McMillan theorem. We use the dissertation's
  approximation theorem instead, as the paper itself suggests. Step (F)(I) cites a corollary of
  invariance of domain. We write down the inverse maps explicitly. The Hausdorff extension theorems
  for Baire-one functions are proved.
- **Sutcliffe.** Sutcliffe's Theorems 2 and 3, used in the note, are proved with explicit solutions.

## 3. Different arguments

In these places the source is correct, but the formal proof follows a different route.

- **J. Math. Mech. 14, Theorem 1** (homeomorphisms of the disk; we have only the review's
  statement). We give a new proof of a quantitative form: the points where the boundary function
  has jumps of size at least `ε` number at most `2π/ε`. Blueprint `thm:homeo`.
- **Dissertation, Theorem 9.** The dissertation proves both inequalities for the measure of a union
  of disjoint segments at once, via Lemmas 23 and 24. We prove each inequality separately, more
  briefly.
- **Dissertation, example after Theorem 9.** For the null sets we take the Liouville numbers, a
  dense G<sub>δ</sub> null set. Baire's theorem is applied to an affine change of variable.
- **Trans. AMS 141, (XX).** For the existence of special functions we give a construction without
  recursion.
- **Trans. AMS 141, special families.** The paper also requires a special family to be nonempty.
  Nothing uses this, and we drop it.

## 4. Not formalized

| Item | Reason |
|---|---|
| Dissertation, unsolved problems 1–5; Trans. AMS 141, Problems 1–2; Proc. AMS 23, Problem | Open questions in the source. |
| J. Math. Mech. 14, remarks on three dimensions | Not stated as a theorem. Section I treats the three-dimensional case. |
| Trans. AMS 137, Lemma in full generality | Needs the Jordan curve theorem. The case used in the paper is proved directly. |
| Proc. AMS 23, Kaczynski's proof of the Lemma | Needs Kierst's theorem and normal functions. The Lemma is proved by the elementary argument. |
| Bagemihl's theorem for arbitrary functions | Only the continuous case is used, and that case is proved. |
