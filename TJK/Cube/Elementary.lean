import Mathlib
import TJK.Defs

/-!
# An elementary proof of the cube lemma (blueprint `lem:cube-lemma-elementary`)

SKELETON (first pass). This file proves `exists_s'`, a copy of `TJK.Cube.exists_s`
(`lem:cube-lemma`), without Kierst's theorem and without normal functions: only the existence of
an analytic non-Borel set (`exists_analytic_not_borel'`, a copy of `fact:analytic-nonborel`) and
plane geometry. See the subsection "An elementary proof of the lemma" of
`paper/sections/I-cube.tex`.

The file does not import `TJK.Cube.Basic`, so `def:asymptotic` is repeated here with primed names
(`IsAsymptoticValue'`, `IsPointAsymptoticValue'`), with bodies identical to those of
`TJK.Cube.IsAsymptoticValue`, `TJK.Cube.IsPointAsymptoticValue`. (Planned refactor: move
`def:asymptotic` and `fact:analytic-nonborel` to a small file imported by both.)

Notation (as in the blueprint):
* words `u : Word = List Bool`, the first letter being the most significant binary digit;
  `left u = x_u`, `width u = 2^{-|u|}`, `mid u = μ_u`, `node u = c_u = μ_u + i 2^{-|u|}`;
* `edge u = e_u = [c_{u⁻}, c_u]` (for `u = []` this is the point `c_∅`, harmless);
* `dd u z = dist(z, e_u) / Im z`;
* `kappa u = κ(u)`, `ell u = ℓ(u)`, `enc σ = β_σ`;
* `R`, `Ψ` and `sFun` are `R`, `Ψ` and `s = R + (i/2) Ψ`.

Every `sorry` below is a planned proof step (marked `-- TODO`).
-/

open _root_.Set Filter Topology Metric

namespace TJK.Cube.Elementary

/-! ### `def:asymptotic` (copies of the definitions in `TJK.Cube.Basic`) -/

section Asymptotic

variable {E : Type*} [PseudoMetricSpace E] {Y : Type*} [TopologicalSpace Y]

/-- Copy of `TJK.Cube.IsAsymptoticValue`. -/
def IsAsymptoticValue' (Ω : Set E) (f : E → Y) (a : Y) : Prop :=
  ∃ v : ℝ → E, ContinuousOn v (Ico 0 1) ∧ MapsTo v (Ico 0 1) Ω ∧
    Tendsto (fun t => infDist (v t) Ωᶜ) (𝓝[<] 1) (𝓝 0) ∧ Tendsto (f ∘ v) (𝓝[<] 1) (𝓝 a)

/-- Copy of `TJK.Cube.IsPointAsymptoticValue`. -/
def IsPointAsymptoticValue' (Ω : Set E) (f : E → Y) (p : E) (a : Y) : Prop :=
  p ∈ frontier Ω ∧ ∃ v : ℝ → E, ContinuousOn v (Ico 0 1) ∧ MapsTo v (Ico 0 1) Ω ∧
    Tendsto v (𝓝[<] 1) (𝓝 p) ∧ Tendsto (f ∘ v) (𝓝[<] 1) (𝓝 a)

theorem IsPointAsymptoticValue'.isAsymptoticValue' {Ω : Set E} {f : E → Y} {p : E} {a : Y}
    (h : IsPointAsymptoticValue' Ω f p a) : IsAsymptoticValue' Ω f a := by
  obtain ⟨hp, v, hc, hm, hv, hf⟩ := h
  refine ⟨v, hc, hm, ?_, hf⟩
  have h0 : infDist p Ωᶜ = 0 := by
    apply infDist_zero_of_mem_closure
    rw [← frontier_compl] at hp
    exact frontier_subset_closure hp
  rw [← h0]
  exact ((continuous_infDist_pt _).tendsto p).comp hv

end Asymptotic

/-! ### The analytic set -/

/-- Copy of `TJK.Cube.exists_analytic_not_borel` (`fact:analytic-nonborel`). TODO: prove it
(universal analytic set in `𝒩 × 𝒩`, `𝒩 = ℕ → ℕ`, diagonalization, Suslin's theorem
`MeasureTheory.AnalyticSet.measurableSet_of_compl` is NOT needed; transfer to `ℝ` with
`MeasureTheory.exists_measurableEmbedding_real`), or import it from a shared file. -/
theorem exists_analytic_not_borel' :
    ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A := by
  sorry -- TODO (imported fact)

/-- An analytic non-Borel `A ⊆ (-1/2, 1/2)`, presented as the range of a continuous
`g : 𝒩 → ℝ`: take `φ(A₀)`, `φ a = a / (2 (1 + |a|))`. -/
theorem exists_g : ∃ g : (ℕ → ℕ) → ℝ, Continuous g ∧ range g ⊆ Ioo (-1 / 2) (1 / 2) ∧
    ¬ MeasurableSet (range g) := by
  sorry -- TODO (easy: image of an analytic set, injectivity of `φ`)

/-! ### Words and the dyadic skeleton -/

/-- Finite binary words; the first letter is the most significant digit. -/
abbrev Word := List Bool

/-- `x_u = ∑ u_i 2^{-i-1}`, the left endpoint of `I_u`. -/
noncomputable def left : Word → ℝ
  | [] => 0
  | b :: u => ((if b then 1 else 0) + left u) / 2

/-- `2^{-|u|}`, the length of `I_u`. -/
noncomputable def width (u : Word) : ℝ := (2 : ℝ)⁻¹ ^ u.length

/-- The dyadic interval `I_u = [x_u, x_u + 2^{-|u|}]`. -/
def Iu (u : Word) : Set ℝ := Icc (left u) (left u + width u)

/-- The midpoint `μ_u` of `I_u`. -/
noncomputable def mid (u : Word) : ℝ := left u + width u / 2

/-- The node `c_u = μ_u + i 2^{-|u|}`. -/
noncomputable def node (u : Word) : ℂ := ⟨mid u, width u⟩

/-- The edge `e_u = [c_{u⁻}, c_u]`. -/
def edge (u : Word) : Set ℂ := segment ℝ (node u.dropLast) (node u)

/-- `d_u(z) = dist(z, e_u) / Im z`. -/
noncomputable def dd (u : Word) (z : ℂ) : ℝ := infDist z (edge u) / z.im

/-- The prefix `β|m` of an infinite word. -/
def pre (β : ℕ → Bool) (m : ℕ) : Word := List.ofFn fun i : Fin m => β i

/-- The point `∑ β_i 2^{-i-1} = lim μ_{β|m}` of `[0, 1]`. -/
noncomputable def limPt (β : ℕ → Bool) : ℝ := ∑' i, (if β i then (2 : ℝ)⁻¹ ^ (i + 1) else 0)

/-! #### Geometry (G1)–(G7) -/

/-- (G1) heights on `e_u`. -/
theorem im_mem_of_mem_edge {u : Word} {p : ℂ} (hp : p ∈ edge u) :
    width u ≤ p.im ∧ p.im ≤ 2 * width u := by
  sorry -- TODO

/-- (G2) for `|v| > k`, points of `e_v` lie over `I_{v|k}`, at distance `≥ Im p / 4` from
`2^{-k} ℤ`. -/
theorem re_mem_of_mem_edge {v : Word} {k : ℕ} (hk : k < v.length) {p : ℂ} (hp : p ∈ edge v) :
    p.re ∈ Iu (v.take k) ∧ ∀ n : ℤ, p.im / 4 ≤ |p.re - n * (2 : ℝ)⁻¹ ^ k| := by
  sorry -- TODO

/-- (G3) edges below `u1` lie to the right of `μ_u`, edges below `u0` to its left. -/
theorem mid_le_re_of_mem_edge {u v : Word} (huv : u ++ [true] <+: v) {p : ℂ} (hp : p ∈ edge v) :
    mid u ≤ p.re := by
  sorry -- TODO

theorem re_le_mid_of_mem_edge {u v : Word} (huv : u ++ [false] <+: v) {p : ℂ}
    (hp : p ∈ edge v) : p.re ≤ mid u := by
  sorry -- TODO

/-- (G4) separation by a vertical line. -/
theorem sep_of_re {p p' : ℂ} {q : ℝ} (hp : q ≤ p.re) (hp' : p'.re ≤ q - p'.im / 4) :
    max p.im p'.im / 8 ≤ ‖p - p'‖ := by
  sorry -- TODO (two cases, `Complex.abs_re_le_norm`, `Complex.abs_im_le_norm`)

/-- Two edges are separated (at scale `Im / 8`). -/
def Separated (v w : Word) : Prop :=
  ∀ p ∈ edge v, ∀ p' ∈ edge w, max p.im p'.im / 8 ≤ ‖p - p'‖

theorem Separated.symm {v w : Word} (h : Separated v w) : Separated w v := fun p hp p' hp' => by
  rw [max_comm, ← norm_neg, neg_sub]; exact h p' hp' p hp

/-- (G5a) -/
theorem separated_of_take_ne {v w : Word} {k : ℕ} (hv : k < v.length) (hw : k < w.length)
    (hne : v.take k ≠ w.take k) : Separated v w := by
  sorry -- TODO (G2 + G4)

/-- (G5b) -/
theorem separated_of_one_zero {u v w : Word} (hv : u ++ [true] <+: v)
    (hw : u ++ [false] <+: w) (hlen : u.length + 1 < w.length) : Separated v w := by
  sorry -- TODO (G3 + G2 + G4)

/-- (G6) -/
theorem dd_gt_of_separated {v w : Word} (h : Separated v w) {z : ℂ} (hz : 0 < z.im)
    (hv : dd v z < 1 / 32) : 1 / 12 < dd w z := by
  sorry -- TODO

/-- (G7) -/
theorem one_le_dd_of_length_le {w : Word} {k : ℕ} (hw : w.length ≤ k) {z : ℂ} (hz : 0 < z.im)
    (hzk : z.im < (2 : ℝ)⁻¹ ^ (k + 1)) : 1 ≤ dd w z := by
  sorry -- TODO (G1)

/-! ### Coding `𝒩 = ℕ → ℕ` by binary words -/

/-- One letter of the block decomposition: `1` closes a block, `0` lengthens the open one. -/
def step (s : List ℕ × ℕ) (b : Bool) : List ℕ × ℕ :=
  if b then (s.1 ++ [s.2], 0) else (s.1, s.2 + 1)

/-- `(κ(u), r)` for `u = 0^{k₀} 1 ⋯ 0^{k_{j-1}} 1 0^r`. -/
def blocks (u : Word) : List ℕ × ℕ := u.foldl step ([], 0)

/-- `κ(u) = (k₀, …, k_{j-1})`. -/
def kappa (u : Word) : List ℕ := (blocks u).1

/-- `ℓ(u) = |u| - r`, the length of the longest prefix of `u` ending in `1`. -/
def ell (u : Word) : ℕ := u.length - (blocks u).2

/-- The cylinder `N_κ = {σ : κ ⊑ σ}`. -/
def cyl (κ : List ℕ) : Set (ℕ → ℕ) := {σ | ∀ i (h : i < κ.length), σ i = κ[i]}

/-- `κ 0^∞`. -/
def ext0 (κ : List ℕ) : ℕ → ℕ := fun i => κ.getD i 0

/-- `β_σ = 0^{σ₀} 1 0^{σ₁} 1 ⋯`: position `n` carries a `1` iff `n + 1 = ∑_{i ≤ j} (σ i + 1)` for some
`j` (necessarily `j ≤ n`). -/
def enc (σ : ℕ → ℕ) : ℕ → Bool := fun n =>
  decide (∃ j < n + 1, ∑ i ∈ Finset.range (j + 1), (σ i + 1) = n + 1)

theorem kappa_mono {u v : Word} (h : u <+: v) : kappa u <+: kappa v := by
  sorry -- TODO (`List.foldl_append`)

theorem length_kappa_le_ell (u : Word) : (kappa u).length ≤ ell u := by
  sorry -- TODO

theorem ext0_mem_cyl (κ : List ℕ) : ext0 κ ∈ cyl κ := by
  sorry -- TODO

theorem cyl_anti {κ κ' : List ℕ} (h : κ <+: κ') : cyl κ' ⊆ cyl κ := by
  sorry -- TODO

theorem kappa_pre_enc (σ : ℕ → ℕ) (m : ℕ) : σ ∈ cyl (kappa (pre (enc σ) m)) := by
  sorry -- TODO

theorem tendsto_length_kappa_pre_enc (σ : ℕ → ℕ) :
    Tendsto (fun m => (kappa (pre (enc σ) m)).length) atTop atTop := by
  sorry -- TODO

/-- A branch with infinitely many `1`s codes some `σ`. -/
theorem exists_enc_eq {β : ℕ → Bool} (hβ : {n | β n = true}.Infinite) : ∃ σ, enc σ = β := by
  sorry -- TODO (block lengths via `Nat.nth`)

/-- A branch with finitely many `1`s is `t 0^∞` with `t` empty or ending in `1`. -/
theorem exists_zeros {β : ℕ → Bool} (hβ : {n | β n = true}.Finite) :
    ∃ n, (∀ i ≥ n, β i = false) ∧ ∀ i ≥ n, ell (pre β i) = n := by
  sorry -- TODO

/-! ### The function `s` -/

section Fun

variable (g : (ℕ → ℕ) → ℝ)

/-- `r_u = g(κ(u) 0^∞)`. -/
noncomputable def rr (u : Word) : ℝ := g (ext0 (kappa u))

/-- `ψ_u = 1 / (ℓ(u) + 2)`. -/
noncomputable def psi (u : Word) : ℝ := 1 / (ell u + 2)

/-- `R(z) = min {1/2, inf_u (r_u + 12 d_u(z))}`. -/
noncomputable def R (z : ℂ) : ℝ := min (1 / 2) (⨅ u : Word, (rr g u + 12 * dd u z))

/-- `Ψ(z) = min {1, inf_u (ψ_u + 16 d_u(z))}`. -/
noncomputable def Ψ (z : ℂ) : ℝ := min 1 (⨅ u : Word, (psi u + 16 * dd u z))

/-- `s = R + (i/2) Ψ`. -/
noncomputable def sFun (z : ℂ) : ℂ := ⟨R g z, Ψ z / 2⟩

/-- Infima of `c_u + K dist(z, S_u) / Im z` over a family of subsets of a bounded set, with
bounded `c_u`, are continuous on `ℍ` (locally uniformly Lipschitz family). -/
theorem continuousOn_iInf_dd {ι : Type*} [Nonempty ι] (c : ι → ℝ) (S : ι → Set ℂ) (K : ℝ)
    (hK : 0 ≤ K) (hc : ∃ C, ∀ i, |c i| ≤ C) (hS : ∃ M, ∀ i, ∀ p ∈ S i, ‖p‖ ≤ M)
    (hne : ∀ i, (S i).Nonempty) :
    ContinuousOn (fun z : ℂ => ⨅ i, (c i + K * (infDist z (S i) / z.im))) upper := by
  sorry -- TODO

theorem continuousOn_sFun (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) : ContinuousOn (sFun g) upper := by
  sorry -- TODO (from `continuousOn_iInf_dd`)

theorem norm_sFun_lt_one (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) (z : ℂ) (hz : 0 < z.im) :
    ‖sFun g z‖ < 1 := by
  sorry -- TODO (`R ∈ [-1/2, 1/2]`, `Ψ ∈ [0, 1]`)

/-- Claim L (first part): near an edge below `u`, all edges within `1/12` lie below `u`. -/
theorem claimL_below {u v w : Word} {z : ℂ} (hz : 0 < z.im)
    (hzk : z.im < (2 : ℝ)⁻¹ ^ (u.length + 1)) (huv : u <+: v) (hlen : u.length < v.length)
    (hv : dd v z < 1 / 32) (hw : dd w z ≤ 1 / 12) : u <+: w ∧ u.length < w.length := by
  sorry -- TODO (G7, G5a, G6)

/-- Claim L (second part): the lower bound for `R`. -/
theorem claimL_R {u v : Word} {z : ℂ} (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) (hz : 0 < z.im)
    (hzk : z.im < (2 : ℝ)⁻¹ ^ (u.length + 1)) (huv : u <+: v) (hlen : u.length < v.length)
    (hv : dd v z < 1 / 32) {a : ℝ} (ha : a ≤ 1 / 2)
    (hr : ∀ w : Word, u <+: w → u.length < w.length → a ≤ rr g w) : a ≤ R g z := by
  sorry -- TODO

end Fun

/-! ### Point asymptotic values along branches -/

/-- The ramp `ρ_m(y) = min 1 (max 0 (2 - 2^m y))`. -/
noncomputable def ramp (m : ℕ) (y : ℝ) : ℝ := min 1 (max 0 (2 - 2 ^ m * y))

/-- `X(y) = μ_∅ + ∑_{m ≥ 1} (μ_{β|m} - μ_{β|m-1}) ρ_m(y)`. -/
noncomputable def branchX (β : ℕ → Bool) (y : ℝ) : ℝ :=
  mid [] + ∑' m : ℕ, (mid (pre β (m + 1)) - mid (pre β m)) * ramp (m + 1) y

theorem continuous_branchX (β : ℕ → Bool) : Continuous (branchX β) := by
  sorry -- TODO (`continuous_tsum`, bound `2^{-m-2}`)

theorem branchX_mem_edge (β : ℕ → Bool) {m : ℕ} {y : ℝ} (hy : (2 : ℝ)⁻¹ ^ (m + 1) ≤ y)
    (hy' : y ≤ (2 : ℝ)⁻¹ ^ m) : (⟨branchX β y, y⟩ : ℂ) ∈ edge (pre β (m + 1)) := by
  sorry -- TODO

theorem tendsto_branchX (β : ℕ → Bool) :
    Tendsto (branchX β) (𝓝[>] 0) (𝓝 (limPt β)) := by
  sorry -- TODO

/-- Step 1: every `g σ` is a point asymptotic value of `s`, at `limPt (enc σ)`. -/
theorem isPointAsymptoticValue_g (hgc : Continuous g) (hg : range g ⊆ Ioo (-1 / 2) (1 / 2))
    (σ : ℕ → ℕ) : IsPointAsymptoticValue' upper (sFun g) (limPt (enc σ) : ℂ) (g σ : ℂ) := by
  sorry -- TODO

/-! ### Asymptotic values -/

/-- `Ω_k(u)`, `|u| = k`. -/
def Om (u : Word) : Set ℂ :=
  {z | 0 < z.im ∧ z.im < (2 : ℝ)⁻¹ ^ (u.length + 1) ∧
    ∃ v, u <+: v ∧ u.length < v.length ∧ dd v z < 1 / 32}

/-- Tail argument: along a path with `Im → 0` and `Ψ → 0` there is a branch `β` such that each
tail eventually lies in `Ω_k(β|k)`; the path tends to `limPt β`. -/
theorem exists_branch {v : ℝ → ℂ} (hvc : ContinuousOn v (Ico 0 1)) (hvm : MapsTo v (Ico 0 1) upper)
    (him : Tendsto (fun t => (v t).im) (𝓝[<] 1) (𝓝 0))
    (hΨ : Tendsto (fun t => Ψ (v t)) (𝓝[<] 1) (𝓝 0)) :
    ∃ β : ℕ → Bool, (∀ k, ∀ᶠ t in 𝓝[<] 1, v t ∈ Om (pre β k)) ∧
      Tendsto v (𝓝[<] 1) (𝓝 (limPt β : ℂ)) := by
  sorry -- TODO (components: `Om u`, `|u| = k`, open and pairwise disjoint)

/-- Case 2: no path with `Ψ → 0` follows a branch `t 0^∞`. -/
theorem not_finite_branch {v : ℝ → ℂ} (hvc : ContinuousOn v (Ico 0 1))
    (hvm : MapsTo v (Ico 0 1) upper) (hΨ : Tendsto (fun t => Ψ (v t)) (𝓝[<] 1) (𝓝 0))
    {β : ℕ → Bool} (hβ : ∀ k, ∀ᶠ t in 𝓝[<] 1, v t ∈ Om (pre β k)) :
    {n | β n = true}.Infinite := by
  sorry -- TODO (the sets `S_i`, (G5b), (G6))

/-- Step 2: a real asymptotic value of `s` is a point asymptotic value and lies in `range g`. -/
theorem mem_range_of_isAsymptoticValue (hgc : Continuous g)
    (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) {b : ℝ}
    (hb : IsAsymptoticValue' upper (sFun g) (b : ℂ)) :
    b ∈ range g ∧ ∃ p, IsPointAsymptoticValue' upper (sFun g) p (b : ℂ) := by
  sorry -- TODO (`exists_branch`, `not_finite_branch`, `exists_enc_eq`, Claim L)

/-! ### `lem:cube-lemma-elementary` -/

/-- `lem:cube-lemma-elementary`: the statement of `TJK.Cube.exists_s` (with the primed copies of
`def:asymptotic`), proved from `fact:analytic-nonborel` alone. -/
theorem exists_s' : ∃ s : ℂ → ℂ, ContinuousOn s upper ∧ (∀ z, ‖s z‖ < 1) ∧
    {b : ℝ | b ∈ Ioo (-1) 1 ∧ IsAsymptoticValue' upper s (b : ℂ)} =
      {b : ℝ | b ∈ Ioo (-1) 1 ∧ ∃ p, IsPointAsymptoticValue' upper s p (b : ℂ)} ∧
    ¬ MeasurableSet {b : ℝ | b ∈ Ioo (-1) 1 ∧ IsAsymptoticValue' upper s (b : ℂ)} := by
  sorry -- TODO: `s z = sFun g z` for `0 < z.im` and `0` otherwise (`‖s z‖ < 1` for all `z`);
  -- both sets equal `range g` by `isPointAsymptoticValue_g`, `mem_range_of_isAsymptoticValue`.

end TJK.Cube.Elementary
