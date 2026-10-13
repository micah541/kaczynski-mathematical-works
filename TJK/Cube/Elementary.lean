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

/-! Elementary facts about `left`, `width`, `mid`, `node`. -/

theorem width_pos (u : Word) : 0 < width u := by unfold width; positivity

theorem width_append (u w : Word) : width (u ++ w) = width u * width w := by
  simp [width, pow_add]

theorem width_cons (b : Bool) (u : Word) : width (b :: u) = width u / 2 := by
  simp [width, pow_succ]; ring

theorem left_append (u w : Word) : left (u ++ w) = left u + width u * left w := by
  induction u with
  | nil => simp [left, width]
  | cons b u ih => simp only [List.cons_append, left, ih, width_cons]; ring

theorem left_nonneg (u : Word) : 0 ≤ left u := by
  induction u with
  | nil => simp [left]
  | cons b u ih => rw [left]; split_ifs <;> positivity

theorem left_add_width_le (u : Word) : left u + width u ≤ 1 := by
  induction u with
  | nil => simp [left, width]
  | cons b u ih => rw [left, width_cons]; have := left_nonneg u; split_ifs <;> linarith

theorem left_singleton (b : Bool) : left [b] = (if b then 1 else 0) / 2 := by
  simp [left]

/-- `x_u` is an integer multiple of `2^{-|u|}`. -/
theorem exists_left_eq (u : Word) : ∃ m : ℕ, left u = m * (2 : ℝ)⁻¹ ^ u.length := by
  induction u with
  | nil => exact ⟨0, by simp [left]⟩
  | cons b u ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨(if b then 1 else 0) * 2 ^ u.length + m, ?_⟩
    have h2 : (2 : ℝ) ^ u.length * (2 : ℝ)⁻¹ ^ u.length = 1 := by
      rw [← mul_pow]; norm_num
    rw [left, hm, List.length_cons, pow_succ]
    split_ifs
    · push_cast; linear_combination (-1 / 2 : ℝ) * h2
    · push_cast; ring

theorem left_le_of_prefix {u v : Word} (h : u <+: v) :
    left u ≤ left v ∧ left v + width v ≤ left u + width u := by
  obtain ⟨w, rfl⟩ := h
  rw [left_append, width_append]
  have := left_nonneg w; have := left_add_width_le w; have := width_pos u
  constructor <;> nlinarith

theorem width_dropLast {v : Word} (hv : v ≠ []) : width v.dropLast = 2 * width v := by
  conv_rhs => rw [← List.dropLast_append_getLast hv]
  rw [width_append]; simp [width]; ring

theorem prefix_dropLast_of_lt {x v : Word} (h : x <+: v) (hl : x.length < v.length) :
    x <+: v.dropLast := by
  rw [List.prefix_iff_eq_take.1 h, List.dropLast_eq_take]
  rw [show v.take x.length = (v.take (v.length - 1)).take x.length by
    rw [List.take_take]; congr 1; omega]
  exact List.take_prefix _ _

theorem edge_nonempty (u : Word) : (edge u).Nonempty := ⟨_, left_mem_segment ℝ _ _⟩

/-- Real parts on `e_v` for a prefix `w` of `v⁻`. -/
theorem edge_re_bounds {v w : Word} (hv : v ≠ []) (hw : w <+: v.dropLast) {p : ℂ}
    (hp : p ∈ edge v) :
    left w + width v / 2 ≤ p.re ∧ p.re ≤ left w + width w - width v / 2 := by
  have hd := width_dropLast hv
  have hwv : w <+: v := hw.trans (List.dropLast_prefix v)
  obtain ⟨a1, a2⟩ := left_le_of_prefix hw
  obtain ⟨b1, b2⟩ := left_le_of_prefix hwv
  have hpos := width_pos v
  have e1 : (node v.dropLast).re = left v.dropLast + width v := by
    simp only [node, mid, hd]; ring
  have e2 : (node v).re = left v + width v / 2 := by simp [node, mid]
  constructor
  · exact (convex_halfSpace_re_ge (left w + width v / 2)).segment_subset
      (show left w + width v / 2 ≤ (node v.dropLast).re by rw [e1]; linarith)
      (show left w + width v / 2 ≤ (node v).re by rw [e2]; linarith) hp
  · exact (convex_halfSpace_re_le (left w + width w - width v / 2)).segment_subset
      (show (node v.dropLast).re ≤ left w + width w - width v / 2 by rw [e1]; linarith)
      (show (node v).re ≤ left w + width w - width v / 2 by rw [e2]; linarith) hp

theorem dist_im_le (z p : ℂ) : |z.im - p.im| ≤ dist z p := by
  rw [Complex.dist_eq]; simpa using Complex.abs_im_le_norm (z - p)

/-- (G1) heights on `e_u`. -/
theorem im_mem_of_mem_edge {u : Word} {p : ℂ} (hp : p ∈ edge u) :
    width u ≤ p.im ∧ p.im ≤ 2 * width u := by
  have hw := width_pos u
  have h1 : width u ≤ width u.dropLast ∧ width u.dropLast ≤ 2 * width u := by
    rcases eq_or_ne u [] with rfl | hu
    · simp [width]
    · rw [width_dropLast hu]; constructor <;> linarith
  constructor
  · exact (convex_halfSpace_im_ge (width u)).segment_subset
      (show width u ≤ (node u.dropLast).im from h1.1)
      (show width u ≤ (node u).im from le_rfl) hp
  · exact (convex_halfSpace_im_le (2 * width u)).segment_subset
      (show (node u.dropLast).im ≤ 2 * width u from h1.2)
      (show (node u).im ≤ 2 * width u by simp only [node]; linarith) hp

/-- (G2) for `|v| > k`, points of `e_v` lie over `I_{v|k}`, at distance `≥ Im p / 4` from
`2^{-k} ℤ`. -/
theorem re_mem_of_mem_edge {v : Word} {k : ℕ} (hk : k < v.length) {p : ℂ} (hp : p ∈ edge v) :
    p.re ∈ Iu (v.take k) ∧ ∀ n : ℤ, p.im / 4 ≤ |p.re - n * (2 : ℝ)⁻¹ ^ k| := by
  have hv : v ≠ [] := by rintro rfl; simp at hk
  have hlen : (v.take k).length = k := List.length_take_of_le hk.le
  have hpre : v.take k <+: v.dropLast :=
    prefix_dropLast_of_lt (List.take_prefix _ _) (by omega)
  obtain ⟨h1, h2⟩ := edge_re_bounds hv hpre hp
  have hw := width_pos v
  have him := (im_mem_of_mem_edge hp).2
  obtain ⟨m, hm⟩ := exists_left_eq (v.take k)
  rw [hlen] at hm
  have hwk : width (v.take k) = (2 : ℝ)⁻¹ ^ k := by rw [width, hlen]
  refine ⟨⟨by linarith, by linarith⟩, fun n => ?_⟩
  have hpow : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  rcases le_or_gt n (m : ℤ) with hn | hn
  · have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
    have : (n : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ left (v.take k) := by
      rw [hm]; exact mul_le_mul_of_nonneg_right hn' hpow.le
    rw [abs_of_nonneg (by linarith)]; linarith
  · have hn' : (m : ℝ) + 1 ≤ n := by
      have : (m : ℤ) + 1 ≤ n := hn
      exact_mod_cast this
    have : left (v.take k) + width (v.take k) ≤ (n : ℝ) * (2 : ℝ)⁻¹ ^ k := by
      rw [hm, hwk, ← add_one_mul]; exact mul_le_mul_of_nonneg_right hn' hpow.le
    rw [abs_of_nonpos (by linarith)]; linarith

/-- (G3) edges below `u1` lie to the right of `μ_u`, edges below `u0` to its left. -/
theorem mid_le_re_of_mem_edge {u v : Word} (huv : u ++ [true] <+: v) {p : ℂ} (hp : p ∈ edge v) :
    mid u ≤ p.re := by
  have key : ∀ x : Word, u ++ [true] <+: x → mid u ≤ mid x := by
    intro x hx
    have h1 := (left_le_of_prefix hx).1
    rw [left_append, left_singleton] at h1
    have := width_pos x
    simp only [mid] at *; simp at h1; linarith
  obtain ⟨w, rfl⟩ := huv
  have e2 : mid u ≤ (node (u ++ [true] ++ w)).re := key _ (List.prefix_append _ _)
  have e1 : mid u ≤ (node (u ++ [true] ++ w).dropLast).re := by
    rcases w.eq_nil_or_concat with rfl | ⟨w', b, rfl⟩
    · simp [node]
    · rw [List.concat_eq_append, ← List.append_assoc, List.dropLast_concat]; exact key _ (List.prefix_append _ _)
  exact (convex_halfSpace_re_ge (mid u)).segment_subset e1 e2 hp

theorem re_le_mid_of_mem_edge {u v : Word} (huv : u ++ [false] <+: v) {p : ℂ}
    (hp : p ∈ edge v) : p.re ≤ mid u := by
  have key : ∀ x : Word, u ++ [false] <+: x → mid x ≤ mid u := by
    intro x hx
    have h1 := (left_le_of_prefix hx).2
    have hw1 : width [false] = 1 / 2 := by simp [width]
    rw [left_append, left_singleton, width_append, hw1] at h1
    have := width_pos x
    simp only [mid] at *; simp at h1; linarith
  obtain ⟨w, rfl⟩ := huv
  have e2 : (node (u ++ [false] ++ w)).re ≤ mid u := key _ (List.prefix_append _ _)
  have e1 : (node (u ++ [false] ++ w).dropLast).re ≤ mid u := by
    rcases w.eq_nil_or_concat with rfl | ⟨w', b, rfl⟩
    · simp [node]
    · rw [List.concat_eq_append, ← List.append_assoc, List.dropLast_concat]; exact key _ (List.prefix_append _ _)
  exact (convex_halfSpace_re_le (mid u)).segment_subset e1 e2 hp

/-- (G4) separation by a vertical line. -/
theorem sep_of_re {p p' : ℂ} {q : ℝ} (hp : q ≤ p.re) (hp' : p'.re ≤ q - p'.im / 4) :
    max p.im p'.im / 8 ≤ ‖p - p'‖ := by
  have h1 : |p.re - p'.re| ≤ ‖p - p'‖ := by simpa using Complex.abs_re_le_norm (p - p')
  have h2 : |p.im - p'.im| ≤ ‖p - p'‖ := by simpa using Complex.abs_im_le_norm (p - p')
  have h3 := le_abs_self (p.re - p'.re)
  have h4 := le_abs_self (p.im - p'.im)
  have h0 := norm_nonneg (p - p')
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8), max_le_iff]
  constructor <;> linarith

/-- Two edges are separated (at scale `Im / 8`). -/
def Separated (v w : Word) : Prop :=
  ∀ p ∈ edge v, ∀ p' ∈ edge w, max p.im p'.im / 8 ≤ ‖p - p'‖

theorem Separated.symm {v w : Word} (h : Separated v w) : Separated w v := fun p hp p' hp' => by
  rw [max_comm, ← norm_neg, neg_sub]; exact h p' hp' p hp

/-- The first difference of two words. -/
theorem exists_split_of_take_ne {v w : Word} {k : ℕ} (hv : k ≤ v.length) (hw : k ≤ w.length)
    (hne : v.take k ≠ w.take k) :
    ∃ u b, u.length < k ∧ u ++ [b] <+: v ∧ u ++ [!b] <+: w := by
  induction k generalizing v w with
  | zero => simp at hne
  | succ k ih =>
    obtain ⟨a, v, rfl⟩ : ∃ a v', v = a :: v' := List.exists_cons_of_ne_nil (by rintro rfl; simp at hv)
    obtain ⟨c, w, rfl⟩ : ∃ c w', w = c :: w' := List.exists_cons_of_ne_nil (by rintro rfl; simp at hw)
    by_cases hac : a = c
    · subst hac
      simp only [List.take_succ_cons, ne_eq, List.cons.injEq, true_and] at hne
      simp only [List.length_cons] at hv hw
      obtain ⟨u, b, hu, h1, h2⟩ := ih (by omega) (by omega) hne
      exact ⟨a :: u, b, by simp; omega, by simpa using h1, by simpa using h2⟩
    · refine ⟨[], a, by simp, by simp, ?_⟩
      cases a <;> cases c <;> simp_all

/-- (G5b) -/
theorem separated_of_one_zero {u v w : Word} (hv : u ++ [true] <+: v)
    (hw : u ++ [false] <+: w) (hlen : u.length + 1 < w.length) : Separated v w := by
  intro p hp p' hp'
  apply sep_of_re (mid_le_re_of_mem_edge hv hp)
  have hw0 : w ≠ [] := by rintro rfl; simp at hlen
  have hpre : u ++ [false] <+: w.dropLast := prefix_dropLast_of_lt hw (by simp; omega)
  obtain ⟨-, h2⟩ := edge_re_bounds hw0 hpre hp'
  have him := (im_mem_of_mem_edge hp').2
  have e : left (u ++ [false]) + width (u ++ [false]) = mid u := by
    rw [left_append, left_singleton, width_append]; simp [mid, width]; ring
  linarith

/-- (G5a) -/
theorem separated_of_take_ne {v w : Word} {k : ℕ} (hv : k < v.length) (hw : k < w.length)
    (hne : v.take k ≠ w.take k) : Separated v w := by
  obtain ⟨u, b, hu, hv', hw'⟩ := exists_split_of_take_ne hv.le hw.le hne
  cases b with
  | true => exact separated_of_one_zero hv' hw' (by omega)
  | false => exact (separated_of_one_zero hw' hv' (by omega)).symm

/-- (G6) -/
theorem dd_gt_of_separated {v w : Word} (h : Separated v w) {z : ℂ} (hz : 0 < z.im)
    (hv : dd v z < 1 / 32) : 1 / 12 < dd w z := by
  unfold dd at *
  rw [div_lt_iff₀ hz] at hv
  obtain ⟨p, hp, hzp⟩ := (Metric.infDist_lt_iff (edge_nonempty v)).1 hv
  have hpim := dist_im_le z p
  have hpim' := le_abs_self (z.im - p.im)
  have key : 23 / 256 * z.im ≤ infDist z (edge w) := by
    rw [Metric.le_infDist (edge_nonempty w)]
    intro p' hp'
    have h1 := h p hp p' hp'
    have h2 : dist p p' ≤ dist p z + dist z p' := dist_triangle _ _ _
    rw [dist_comm p z, dist_eq_norm p p'] at h2
    have h3 : p.im ≤ max p.im p'.im := le_max_left _ _
    linarith
  rw [lt_div_iff₀ hz]; linarith

/-- (G7) -/
theorem one_le_dd_of_length_le {w : Word} {k : ℕ} (hw : w.length ≤ k) {z : ℂ} (hz : 0 < z.im)
    (hzk : z.im < (2 : ℝ)⁻¹ ^ (k + 1)) : 1 ≤ dd w z := by
  unfold dd
  rw [le_div_iff₀ hz, one_mul, Metric.le_infDist (edge_nonempty w)]
  intro p hp
  have h1 := (im_mem_of_mem_edge hp).1
  have h2 : (2 : ℝ)⁻¹ ^ k ≤ width w := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
  have h3 : (2 : ℝ)⁻¹ ^ (k + 1) = (2 : ℝ)⁻¹ ^ k / 2 := by rw [pow_succ]; ring
  have h4 := dist_im_le z p
  have h5 := neg_abs_le (z.im - p.im)
  linarith

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

theorem foldl_step_fst_prefix (s : List ℕ × ℕ) (w : Word) : s.1 <+: (w.foldl step s).1 := by
  induction w generalizing s with
  | nil => exact List.prefix_refl _
  | cons b w ih =>
    rw [List.foldl_cons]
    refine List.IsPrefix.trans ?_ (ih _)
    unfold step; split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

theorem foldl_step_len (s : List ℕ × ℕ) (w : Word) :
    (w.foldl step s).1.length + (w.foldl step s).2 ≤ s.1.length + s.2 + w.length := by
  induction w generalizing s with
  | nil => simp
  | cons b w ih =>
    rw [List.foldl_cons]; refine (ih _).trans ?_
    unfold step; split_ifs <;> simp <;> omega

theorem kappa_mono {u v : Word} (h : u <+: v) : kappa u <+: kappa v := by
  obtain ⟨w, rfl⟩ := h
  unfold kappa blocks; rw [List.foldl_append]; exact foldl_step_fst_prefix _ _

theorem length_kappa_le_ell (u : Word) : (kappa u).length ≤ ell u := by
  have := foldl_step_len ([], 0) u
  unfold kappa ell blocks; simp at this; omega

theorem ext0_mem_cyl (κ : List ℕ) : ext0 κ ∈ cyl κ := fun i hi => by
  simp [ext0, List.getElem?_eq_getElem hi]

theorem cyl_anti {κ κ' : List ℕ} (h : κ <+: κ') : cyl κ' ⊆ cyl κ := fun σ hσ i hi => by
  rw [hσ i (lt_of_lt_of_le hi h.length_le), h.getElem hi]

theorem length_pre (β : ℕ → Bool) (m : ℕ) : (pre β m).length = m := by simp [pre]

theorem pre_succ (β : ℕ → Bool) (m : ℕ) : pre β (m + 1) = pre β m ++ [β m] := by
  rw [pre, pre, List.ofFn_succ_last]
  simp only [Fin.val_castSucc, Fin.val_last]

theorem blocks_pre_succ (β : ℕ → Bool) (m : ℕ) :
    blocks (pre β (m + 1)) = step (blocks (pre β m)) (β m) := by
  rw [pre_succ, blocks, List.foldl_append]; rfl

/-- The partial sums `∑_{i < j} (σ i + 1)`: the `j`-th `1` of `β_σ` (counting from `0`) is at
position `partSum σ (j + 1) - 1`. -/
def partSum (σ : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, (σ i + 1)

theorem partSum_succ (σ : ℕ → ℕ) (j : ℕ) : partSum σ (j + 1) = partSum σ j + σ j + 1 := by
  simp [partSum, Finset.sum_range_succ]; ring

theorem partSum_strictMono (σ : ℕ → ℕ) : StrictMono (partSum σ) :=
  strictMono_nat_of_lt_succ fun j => by rw [partSum_succ]; omega

theorem le_partSum (σ : ℕ → ℕ) (j : ℕ) : j ≤ partSum σ j := by
  induction j with
  | zero => simp [partSum]
  | succ j ih => rw [partSum_succ]; omega

theorem enc_eq_true {σ : ℕ → ℕ} {n : ℕ} :
    enc σ n = true ↔ ∃ j, partSum σ (j + 1) = n + 1 := by
  unfold enc
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨j, -, hj⟩; exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    have := le_partSum σ (j + 1)
    exact ⟨j, by omega, hj⟩

/-- The state of the block decomposition along `β_σ`. -/
theorem blocks_pre_enc (σ : ℕ → ℕ) (m : ℕ) :
    ∃ j, blocks (pre (enc σ) m) = (List.ofFn fun i : Fin j => σ i, m - partSum σ j) ∧
      partSum σ j ≤ m ∧ m < partSum σ (j + 1) := by
  induction m with
  | zero => exact ⟨0, by simp [blocks, pre, partSum]⟩
  | succ m ih =>
    obtain ⟨j, hb, h1, h2⟩ := ih
    have hs := partSum_succ σ j
    have hs' := partSum_succ σ (j + 1)
    rw [blocks_pre_succ, hb]
    by_cases hm : m + 1 = partSum σ (j + 1)
    · have he : enc σ m = true := enc_eq_true.2 ⟨j, hm.symm⟩
      refine ⟨j + 1, ?_, by omega, by omega⟩
      rw [he, List.ofFn_succ_last]
      simp only [step, if_true, Fin.val_castSucc, Fin.val_last, Prod.mk.injEq]
      constructor
      · congr 2; omega
      · omega
    · have he : enc σ m = false := by
        rw [Bool.eq_false_iff, ne_eq, enc_eq_true]
        rintro ⟨j', hj'⟩
        rcases lt_trichotomy j' j with h | rfl | h
        · have := (partSum_strictMono σ).monotone (show j' + 1 ≤ j by omega)
          omega
        · omega
        · have := (partSum_strictMono σ).monotone (show j + 1 + 1 ≤ j' + 1 by omega)
          omega
      refine ⟨j, ?_, by omega, by omega⟩
      rw [he]
      simp only [step, Bool.false_eq_true, if_false, Prod.mk.injEq, true_and]
      omega

theorem kappa_pre_enc (σ : ℕ → ℕ) (m : ℕ) : σ ∈ cyl (kappa (pre (enc σ) m)) := by
  obtain ⟨j, hb, -, -⟩ := blocks_pre_enc σ m
  have hk : kappa (pre (enc σ) m) = List.ofFn fun i : Fin j => σ i := by rw [kappa, hb]
  rw [hk]
  intro i hi
  simp

theorem tendsto_length_kappa_pre_enc (σ : ℕ → ℕ) :
    Tendsto (fun m => (kappa (pre (enc σ) m)).length) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨partSum σ N, fun m hm => ?_⟩
  obtain ⟨j, hb, h1, h2⟩ := blocks_pre_enc σ m
  simp only [kappa, hb, List.length_ofFn]
  by_contra h
  have := (partSum_strictMono σ).monotone (show j + 1 ≤ N by omega)
  omega

/-- A branch with infinitely many `1`s codes some `σ`. -/
theorem exists_enc_eq {β : ℕ → Bool} (hβ : {n | β n = true}.Infinite) : ∃ σ, enc σ = β := by
  set p := Nat.nth (fun n => β n = true) with hp
  have hmono : StrictMono p := Nat.nth_strictMono hβ
  have hmem : ∀ j, β (p j) = true := Nat.nth_mem_of_infinite hβ
  have hrange : Set.range p = {n | β n = true} := Nat.range_nth_of_infinite hβ
  let σ : ℕ → ℕ := fun j => p j - (if j = 0 then 0 else p (j - 1) + 1)
  have hσ : ∀ j, partSum σ (j + 1) = p j + 1 := by
    intro j
    induction j with
    | zero => simp [partSum, σ]
    | succ j ih =>
      rw [partSum_succ, ih]
      have := hmono (show j < j + 1 by omega)
      simp only [σ, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      omega
  refine ⟨σ, funext fun n => ?_⟩
  rw [Bool.eq_iff_iff, enc_eq_true]
  simp only [hσ, Nat.add_right_cancel_iff]
  constructor
  · rintro ⟨j, rfl⟩; exact hmem j
  · intro h
    have : n ∈ Set.range p := by rw [hrange]; exact h
    exact this

/-- A branch with finitely many `1`s is `t 0^∞` with `t` empty or ending in `1`. -/
theorem exists_zeros {β : ℕ → Bool} (hβ : {n | β n = true}.Finite) :
    ∃ n, (∀ i ≥ n, β i = false) ∧ ∀ i ≥ n, ell (pre β i) = n := by
  classical
  obtain ⟨N, hN⟩ := hβ.bddAbove
  have hex : ∃ n, ∀ i ≥ n, β i = false := ⟨N + 1, fun i hi => by
    by_contra h
    have := hN (show i ∈ {n | β n = true} by simpa using h)
    omega⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have hn : ell (pre β (Nat.find hex)) = Nat.find hex := by
    rcases h : Nat.find hex with _ | m
    · simp [ell, pre, blocks]
    · have hm : β m = true := by
        have := Nat.find_min hex (show m < Nat.find hex by omega)
        push Not at this
        obtain ⟨i, hi, hβi⟩ := this
        rcases eq_or_lt_of_le hi with rfl | hi'
        · simpa using hβi
        · exact absurd (Nat.find_spec hex i (by omega)) hβi
      rw [ell, blocks_pre_succ, hm, length_pre]
      simp [step]
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact hn
  | succ i hi ih =>
    rw [ell, blocks_pre_succ, Nat.find_spec hex i hi, length_pre]
    rw [ell, length_pre] at ih
    simp only [step, Bool.false_eq_true, if_false]
    omega

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

end Fun

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
