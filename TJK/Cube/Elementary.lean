import Mathlib
import TJK.Defs
import TJK.Cube.AnalyticNonBorel

/-!
# An elementary proof of the cube lemma (blueprint `lem:cube-lemma-elementary`)

This file proves `exists_s'`, a copy of `TJK.Cube.exists_s`
(`lem:cube-lemma`), without Kierst's theorem and without normal functions: only the existence of
an analytic non-Borel set (`TJK.Cube.exists_analytic_not_borel'`, `fact:analytic-nonborel`, proved
in `TJK/Cube/AnalyticNonBorel.lean`) and plane geometry. See the subsection "An elementary proof of the lemma" of
`paper/sections/I-cube.tex`.

The file does not import `TJK.Cube.Basic`, so `def:asymptotic` is repeated here with primed names
(`IsAsymptoticValue'`, `IsPointAsymptoticValue'`), with bodies identical to those of
`TJK.Cube.IsAsymptoticValue`, `TJK.Cube.IsPointAsymptoticValue`. (Planned refactor: move
`def:asymptotic` to a small file imported by both.)

Notation (as in the blueprint):
* words `u : Word = List Bool`, the first letter being the most significant binary digit;
  `left u = x_u`, `width u = 2^{-|u|}`, `mid u = μ_u`, `node u = c_u = μ_u + i 2^{-|u|}`;
* `edge u = e_u = [c_{u⁻}, c_u]` (for `u = []` this is the point `c_∅`, harmless);
* `dd u z = dist(z, e_u) / Im z`;
* `kappa u = κ(u)`, `ell u = ℓ(u)`, `enc σ = β_σ`;
* `R`, `Ψ` and `sFun` are `R`, `Ψ` and `s = R + (i/2) Ψ`.

The file is sorry-free.
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

/-! `fact:analytic-nonborel` is `TJK.Cube.exists_analytic_not_borel'`
(file `TJK/Cube/AnalyticNonBorel.lean`). -/

/-- An analytic non-Borel `A ⊆ (-1/2, 1/2)`, presented as the range of a continuous
`g : 𝒩 → ℝ`: the image of an analytic non-Borel `A₀ ⊆ ℝ` under a homeomorphism of `ℝ` onto
`(-1/2, 1/2)`. -/
theorem exists_g : ∃ g : (ℕ → ℕ) → ℝ, Continuous g ∧ range g ⊆ Ioo (-1 / 2) (1 / 2) ∧
    ¬ MeasurableSet (range g) := by
  obtain ⟨A₀, hA, hnm⟩ := exists_analytic_not_borel'
  set e := orderIsoIooNegOneOne ℝ
  let φ : ℝ → ℝ := fun a => (e a : ℝ) / 2
  have hφc : Continuous φ := (continuous_subtype_val.comp e.continuous).div_const _
  have hφi : Function.Injective φ := fun a b h => by
    have : (e a : ℝ) = e b := by simpa [φ] using h
    exact e.injective (Subtype.ext this)
  have hφr : ∀ a, φ a ∈ Ioo (-1 / 2) (1 / 2) := fun a => by
    have := (e a).2
    simp only [mem_Ioo, φ] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hA' := hA.image_of_continuous hφc
  rw [MeasureTheory.AnalyticSet] at hA'
  rcases hA' with h | ⟨g, hgc, hgr⟩
  · exfalso
    rw [image_eq_empty] at h
    exact hnm (h ▸ MeasurableSet.empty)
  · refine ⟨g, hgc, ?_, fun hm => hnm ?_⟩
    · rw [hgr]; rintro _ ⟨a, -, rfl⟩; exact hφr a
    · have := hφc.measurable (hgr ▸ hm)
      rwa [hφi.preimage_image] at this

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

/-- The Lipschitz estimate behind `continuousOn_iInf_dd`. -/
theorem abs_infDist_div_sub_le {S : Set ℂ} {M η : ℝ} (hS : ∀ p ∈ S, ‖p‖ ≤ M) (hne : S.Nonempty)
    {z z₀ : ℂ} (hη : 0 < η) (hz : η ≤ z.im) (hz₀ : η ≤ z₀.im) :
    |infDist z S / z.im - infDist z₀ S / z₀.im| ≤
      (1 / η + (‖z₀‖ + M) / η ^ 2) * dist z z₀ := by
  obtain ⟨p, hp⟩ := hne
  have hy : 0 < z.im := hη.trans_le hz
  have hy₀ : 0 < z₀.im := hη.trans_le hz₀
  have ha₀ : infDist z₀ S ≤ ‖z₀‖ + M := by
    refine (infDist_le_dist_of_mem hp).trans ?_
    rw [dist_eq_norm]; exact (norm_sub_le _ _).trans (by linarith [hS p hp])
  have ha₀' : 0 ≤ infDist z₀ S := infDist_nonneg
  have h1 : |infDist z S - infDist z₀ S| ≤ dist z z₀ := by
    rw [abs_sub_le_iff]; constructor
    · linarith [infDist_le_infDist_add_dist (x := z) (y := z₀) (s := S)]
    · linarith [infDist_le_infDist_add_dist (x := z₀) (y := z) (s := S), dist_comm z z₀]
  have h2 : |z.im - z₀.im| ≤ dist z z₀ := by
    rw [Complex.dist_eq]; simpa using Complex.abs_im_le_norm (z - z₀)
  have e : infDist z S / z.im - infDist z₀ S / z₀.im =
      (infDist z S - infDist z₀ S) / z.im + infDist z₀ S * (z₀.im - z.im) / (z.im * z₀.im) := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_div, abs_mul, abs_of_pos hy, abs_of_pos (mul_pos hy hy₀),
    abs_of_nonneg ha₀', abs_sub_comm z₀.im]
  have hd := dist_nonneg (x := z) (y := z₀)
  have t1 : |infDist z S - infDist z₀ S| / z.im ≤ dist z z₀ / η := by
    rw [div_le_div_iff₀ hy hη]; nlinarith [abs_nonneg (infDist z S - infDist z₀ S)]
  have t2 : infDist z₀ S * |z.im - z₀.im| / (z.im * z₀.im) ≤ (‖z₀‖ + M) * dist z z₀ / η ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos hy hy₀) (by positivity)]
    have : infDist z₀ S * |z.im - z₀.im| ≤ (‖z₀‖ + M) * dist z z₀ :=
      mul_le_mul ha₀ h2 (abs_nonneg _) (ha₀'.trans ha₀)
    have : η ^ 2 ≤ z.im * z₀.im := by rw [sq]; exact mul_le_mul hz hz₀ hη.le hy.le
    have : 0 ≤ (‖z₀‖ + M) * dist z z₀ := (mul_nonneg (ha₀'.trans ha₀) hd)
    nlinarith [mul_nonneg ha₀' (abs_nonneg (z.im - z₀.im))]
  calc _ ≤ dist z z₀ / η + (‖z₀‖ + M) * dist z z₀ / η ^ 2 := add_le_add t1 t2
    _ = _ := by ring

/-- Infima of `c_u + K dist(z, S_u) / Im z` over a family of subsets of a bounded set, with
bounded `c_u`, are continuous on `ℍ` (locally uniformly Lipschitz family). -/
theorem continuousOn_iInf_dd {ι : Type*} [Nonempty ι] (c : ι → ℝ) (S : ι → Set ℂ) (K : ℝ)
    (hK : 0 ≤ K) (hc : ∃ C, ∀ i, |c i| ≤ C) (hS : ∃ M, ∀ i, ∀ p ∈ S i, ‖p‖ ≤ M)
    (hne : ∀ i, (S i).Nonempty) :
    ContinuousOn (fun z : ℂ => ⨅ i, (c i + K * (infDist z (S i) / z.im))) upper := by
  obtain ⟨C, hC⟩ := hc
  obtain ⟨M, hM⟩ := hS
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  set η := z₀.im / 2 with hηdef
  have hη : 0 < η := by positivity
  set L := K * (1 / η + (‖z₀‖ + M) / η ^ 2) with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ ‖z₀‖ + M := by
      obtain ⟨p, hp⟩ := hne (Classical.arbitrary ι)
      linarith [hM _ p hp, norm_nonneg z₀, norm_nonneg p]
    positivity
  refine ⟨min η (ε / (L + 1)), by positivity, fun z hz => ?_⟩
  have hz1 : dist z z₀ < η := hz.trans_le (min_le_left _ _)
  have hz2 : dist z z₀ < ε / (L + 1) := hz.trans_le (min_le_right _ _)
  have hzim : η ≤ z.im := by
    have : |z.im - z₀.im| ≤ dist z z₀ := by
      rw [Complex.dist_eq]; simpa using Complex.abs_im_le_norm (z - z₀)
    have := neg_abs_le (z.im - z₀.im)
    linarith
  have hy : 0 < z.im := hη.trans_le hzim
  have hlip : ∀ i, |(c i + K * (infDist z (S i) / z.im)) - (c i + K * (infDist z₀ (S i) / z₀.im))|
      ≤ L * dist z z₀ := fun i => by
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hK, hL, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (abs_infDist_div_sub_le (hM i) (hne i) hη hzim (by linarith)) hK
  have hbdd : ∀ w : ℂ, 0 < w.im → BddBelow (range fun i => c i + K * (infDist w (S i) / w.im)) :=
    fun w hw => ⟨-C, by
      rintro _ ⟨i, rfl⟩
      have := neg_abs_le (c i)
      have : 0 ≤ K * (infDist w (S i) / w.im) := mul_nonneg hK (div_nonneg infDist_nonneg hw.le)
      linarith [hC i]⟩
  have key : ∀ i, |(c i + K * (infDist z (S i) / z.im)) - (c i + K * (infDist z₀ (S i) / z₀.im))|
      ≤ L * dist z z₀ := hlip
  have hd : L * dist z z₀ < ε := by
    rw [lt_div_iff₀ (by linarith)] at hz2
    nlinarith [dist_nonneg (x := z) (y := z₀)]
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · have : (⨅ i, (c i + K * (infDist z (S i) / z.im))) ≤
        (⨅ i, (c i + K * (infDist z₀ (S i) / z₀.im))) + L * dist z z₀ := by
      rw [← sub_le_iff_le_add]
      refine le_ciInf fun i => ?_
      rw [sub_le_iff_le_add]
      refine (ciInf_le (hbdd z hy) i).trans ?_
      have := (abs_sub_le_iff.1 (key i)).1
      linarith
    linarith
  · have : (⨅ i, (c i + K * (infDist z₀ (S i) / z₀.im))) ≤
        (⨅ i, (c i + K * (infDist z (S i) / z.im))) + L * dist z z₀ := by
      rw [← sub_le_iff_le_add]
      refine le_ciInf fun i => ?_
      rw [sub_le_iff_le_add]
      refine (ciInf_le (hbdd z₀ hz₀') i).trans ?_
      have := (abs_sub_le_iff.1 (key i)).2
      linarith
    linarith

theorem mid_mem_Icc (u : Word) : 0 ≤ mid u ∧ mid u ≤ 1 := by
  have := left_nonneg u; have := left_add_width_le u; have := width_pos u
  unfold mid; constructor <;> linarith

theorem width_le_one (u : Word) : width u ≤ 1 := by
  unfold width; exact pow_le_one₀ (by norm_num) (by norm_num)

theorem norm_node_le (u : Word) : ‖node u‖ ≤ 2 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  obtain ⟨h1, h2⟩ := mid_mem_Icc u
  have := width_pos u; have := width_le_one u
  simp only [node]
  rw [abs_of_nonneg h1, abs_of_pos (by assumption)]; linarith

theorem norm_le_of_mem_edge {u : Word} {p : ℂ} (hp : p ∈ edge u) : ‖p‖ ≤ 2 := by
  have := (convex_closedBall (0 : ℂ) 2).segment_subset
    (mem_closedBall_zero_iff.2 (norm_node_le u.dropLast))
    (mem_closedBall_zero_iff.2 (norm_node_le u)) hp
  exact mem_closedBall_zero_iff.1 this

theorem dd_nonneg (u : Word) {z : ℂ} (hz : 0 < z.im) : 0 ≤ dd u z :=
  div_nonneg infDist_nonneg hz.le

theorem dd_eq_zero_of_mem {u : Word} {z : ℂ} (hz : z ∈ edge u) : dd u z = 0 := by
  simp [dd, infDist_zero_of_mem hz]

theorem rr_mem {u : Word} (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) : rr g u ∈ Ioo (-1 / 2) (1 / 2) :=
  hg (mem_range_self _)

theorem psi_pos (u : Word) : 0 < psi u := by unfold psi; positivity

theorem psi_le (u : Word) : psi u ≤ 1 / 2 := by
  unfold psi; gcongr; linarith [Nat.cast_nonneg (α := ℝ) (ell u)]

theorem bddBelow_R (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) {z : ℂ} (hz : 0 < z.im) :
    BddBelow (range fun u : Word => rr g u + 12 * dd u z) :=
  ⟨-1 / 2, by
    rintro _ ⟨u, rfl⟩
    linarith [(rr_mem g hg (u := u)).1, dd_nonneg u hz]⟩

theorem bddBelow_Ψ {z : ℂ} (hz : 0 < z.im) :
    BddBelow (range fun u : Word => psi u + 16 * dd u z) :=
  ⟨0, by
    rintro _ ⟨u, rfl⟩
    linarith [psi_pos u, dd_nonneg u hz]⟩

theorem R_le_rr (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) {z : ℂ} (hz : 0 < z.im) (u : Word) :
    R g z ≤ rr g u + 12 * dd u z :=
  (min_le_right _ _).trans (ciInf_le (bddBelow_R g hg hz) u)

theorem Ψ_le_psi {z : ℂ} (hz : 0 < z.im) (u : Word) : Ψ z ≤ psi u + 16 * dd u z :=
  (min_le_right _ _).trans (ciInf_le (bddBelow_Ψ hz) u)

theorem R_mem (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) {z : ℂ} (hz : 0 < z.im) :
    -1 / 2 ≤ R g z ∧ R g z ≤ 1 / 2 := by
  refine ⟨le_min (by norm_num) (le_ciInf fun u => ?_), min_le_left _ _⟩
  linarith [(rr_mem g hg (u := u)).1, dd_nonneg u hz]

theorem Ψ_mem {z : ℂ} (hz : 0 < z.im) : 0 ≤ Ψ z ∧ Ψ z ≤ 1 := by
  refine ⟨le_min (by norm_num) (le_ciInf fun u => ?_), min_le_left _ _⟩
  linarith [psi_pos u, dd_nonneg u hz]

theorem continuousOn_sFun (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) : ContinuousOn (sFun g) upper := by
  have hR : ContinuousOn (R g) upper := by
    refine continuous_min.comp_continuousOn (continuousOn_const.prodMk ?_)
    refine continuousOn_iInf_dd (rr g) edge 12 (by norm_num) ⟨1 / 2, fun u => ?_⟩
      ⟨2, fun u p hp => norm_le_of_mem_edge hp⟩ edge_nonempty
    have := rr_mem g hg (u := u)
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hΨ : ContinuousOn Ψ upper := by
    refine continuous_min.comp_continuousOn (continuousOn_const.prodMk ?_)
    refine continuousOn_iInf_dd psi edge 16 (by norm_num) ⟨1, fun u => ?_⟩
      ⟨2, fun u p hp => norm_le_of_mem_edge hp⟩ edge_nonempty
    rw [abs_of_pos (psi_pos u)]; linarith [psi_le u]
  have e : sFun g = fun z => (R g z : ℂ) + ((Ψ z / 2 : ℝ) : ℂ) * Complex.I := by
    funext z; apply Complex.ext <;> simp [sFun]
  rw [e]
  exact (Complex.continuous_ofReal.comp_continuousOn hR).add
    ((Complex.continuous_ofReal.comp_continuousOn (hΨ.div_const 2)).mul continuousOn_const)

theorem norm_sFun_lt_one (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) (z : ℂ) (hz : 0 < z.im) :
    ‖sFun g z‖ < 1 := by
  obtain ⟨h1, h2⟩ := R_mem g hg hz
  obtain ⟨h3, h4⟩ := Ψ_mem hz
  rw [← sq_lt_one_iff₀ (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
  simp only [sFun]
  nlinarith

/-- Claim L (first part): near an edge below `u`, all edges within `1/12` lie below `u`. -/
theorem claimL_below {u v w : Word} {z : ℂ} (hz : 0 < z.im)
    (hzk : z.im < (2 : ℝ)⁻¹ ^ (u.length + 1)) (huv : u <+: v) (hlen : u.length < v.length)
    (hv : dd v z < 1 / 32) (hw : dd w z ≤ 1 / 12) : u <+: w ∧ u.length < w.length := by
  have hwl : u.length < w.length := by
    by_contra h
    have := one_le_dd_of_length_le (not_lt.1 h) hz hzk
    linarith
  have hu : u = v.take u.length := List.prefix_iff_eq_take.1 huv
  refine ⟨?_, hwl⟩
  by_contra h
  have hne : v.take u.length ≠ w.take u.length := by
    rw [← hu]; intro h'; exact h (h' ▸ List.take_prefix _ _)
  have := dd_gt_of_separated (separated_of_take_ne hlen hwl hne) hz hv
  linarith

/-- Claim L (second part): the lower bound for `R`. -/
theorem claimL_R {u v : Word} {z : ℂ} (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) (hz : 0 < z.im)
    (hzk : z.im < (2 : ℝ)⁻¹ ^ (u.length + 1)) (huv : u <+: v) (hlen : u.length < v.length)
    (hv : dd v z < 1 / 32) {a : ℝ} (ha : a ≤ 1 / 2)
    (hr : ∀ w : Word, u <+: w → u.length < w.length → a ≤ rr g w) : a ≤ R g z := by
  refine le_min ha (le_ciInf fun w => ?_)
  rcases le_or_gt (dd w z) (1 / 12) with h | h
  · obtain ⟨h1, h2⟩ := claimL_below hz hzk huv hlen hv h
    linarith [hr w h1 h2, dd_nonneg w hz]
  · linarith [(rr_mem g hg (u := w)).1]


/-! ### Point asymptotic values along branches -/

/-- The ramp `ρ_m(y) = min 1 (max 0 (2 - 2^m y))`. -/
noncomputable def ramp (m : ℕ) (y : ℝ) : ℝ := min 1 (max 0 (2 - 2 ^ m * y))

/-- `X(y) = μ_∅ + ∑_{m ≥ 1} (μ_{β|m} - μ_{β|m-1}) ρ_m(y)`. -/
noncomputable def branchX (β : ℕ → Bool) (y : ℝ) : ℝ :=
  mid [] + ∑' m : ℕ, (mid (pre β (m + 1)) - mid (pre β m)) * ramp (m + 1) y

theorem width_pre (β : ℕ → Bool) (m : ℕ) : width (pre β m) = (2 : ℝ)⁻¹ ^ m := by
  rw [width, length_pre]

theorem left_pre (β : ℕ → Bool) (m : ℕ) :
    left (pre β m) = ∑ i ∈ Finset.range m, (if β i then (2 : ℝ)⁻¹ ^ (i + 1) else 0) := by
  induction m with
  | zero => simp [pre, left]
  | succ m ih =>
    rw [pre_succ, left_append, ih, width_pre, left_singleton, Finset.sum_range_succ, pow_succ]
    split_ifs <;> ring

theorem mid_pre (β : ℕ → Bool) (m : ℕ) :
    mid (pre β m) = left (pre β m) + (2 : ℝ)⁻¹ ^ (m + 1) := by
  rw [mid, width_pre, pow_succ]; ring

/-- `μ_{β|m+1} - μ_{β|m} = ±2^{-m-2}`. -/
theorem abs_mid_pre_succ_sub (β : ℕ → Bool) (m : ℕ) :
    |mid (pre β (m + 1)) - mid (pre β m)| = (2 : ℝ)⁻¹ ^ (m + 2) := by
  rw [mid_pre, mid_pre, left_pre, left_pre, Finset.sum_range_succ]
  have h : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (m + 2) := by positivity
  split_ifs
  · rw [show ∀ a : ℝ, a + (2 : ℝ)⁻¹ ^ (m + 1) + (2 : ℝ)⁻¹ ^ (m + 1 + 1) - (a + (2 : ℝ)⁻¹ ^ (m + 1))
      = (2 : ℝ)⁻¹ ^ (m + 2) from fun a => by ring, abs_of_pos h]
  · rw [show ∀ a : ℝ, a + 0 + (2 : ℝ)⁻¹ ^ (m + 1 + 1) - (a + (2 : ℝ)⁻¹ ^ (m + 1))
      = -(2 : ℝ)⁻¹ ^ (m + 2) from fun a => by ring, abs_neg, abs_of_pos h]

theorem ramp_mem (m : ℕ) (y : ℝ) : 0 ≤ ramp m y ∧ ramp m y ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem two_pow_mul_inv_two_pow (m : ℕ) : (2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ m = 1 := by
  rw [← mul_pow]; norm_num

theorem ramp_eq_one {j m : ℕ} (hj : j ≤ m) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ (2 : ℝ)⁻¹ ^ m) :
    ramp j y = 1 := by
  have h1 : (2 : ℝ) ^ j ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj
  have h2 : (2 : ℝ) ^ m * y ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 ^ m)
    rwa [two_pow_mul_inv_two_pow] at this
  have h3 : (2 : ℝ) ^ j * y ≤ 2 ^ m * y := mul_le_mul_of_nonneg_right h1 hy0
  unfold ramp
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

theorem ramp_eq_zero {j m : ℕ} (hj : m + 2 ≤ j) {y : ℝ} (hy : (2 : ℝ)⁻¹ ^ (m + 1) ≤ y) :
    ramp j y = 0 := by
  have h1 : (2 : ℝ) ^ (m + 2) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have h2 : 2 ≤ (2 : ℝ) ^ (m + 2) * y := by
    have e : (2 : ℝ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
    have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 ^ (m + 1))
    rw [two_pow_mul_inv_two_pow] at this
    rw [e]; linarith
  have h3 : (2 : ℝ) ^ (m + 2) * y ≤ 2 ^ j * y :=
    mul_le_mul_of_nonneg_right h1 (le_trans (by positivity) hy)
  unfold ramp
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

theorem ramp_eq {m : ℕ} {y : ℝ} (hy : (2 : ℝ)⁻¹ ^ (m + 1) ≤ y) (hy' : y ≤ (2 : ℝ)⁻¹ ^ m) :
    ramp (m + 1) y = 2 - 2 ^ (m + 1) * y ∧ 0 ≤ 2 - 2 ^ (m + 1) * y ∧
      2 - 2 ^ (m + 1) * y ≤ 1 := by
  have h1 : 1 ≤ (2 : ℝ) ^ (m + 1) * y := by
    have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 ^ (m + 1))
    rwa [two_pow_mul_inv_two_pow] at this
  have h2 : (2 : ℝ) ^ (m + 1) * y ≤ 2 := by
    have e : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
    have := mul_le_mul_of_nonneg_left hy' (by positivity : (0 : ℝ) ≤ 2 ^ m)
    rw [two_pow_mul_inv_two_pow] at this
    rw [e]; linarith
  refine ⟨?_, by linarith, by linarith⟩
  unfold ramp
  rw [max_eq_right (by linarith), min_eq_right (by linarith)]

/-- On the level `[2^{-m-1}, 2^{-m}]`, `X` interpolates between `μ_{β|m}` and `μ_{β|m+1}`. -/
theorem branchX_eq (β : ℕ → Bool) {m : ℕ} {y : ℝ} (hy : (2 : ℝ)⁻¹ ^ (m + 1) ≤ y)
    (hy' : y ≤ (2 : ℝ)⁻¹ ^ m) :
    branchX β y = mid (pre β m) + (mid (pre β (m + 1)) - mid (pre β m)) * ramp (m + 1) y := by
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  unfold branchX
  rw [tsum_eq_sum (s := Finset.range (m + 1)) (fun j hj => by
    rw [Finset.mem_range, not_lt] at hj
    rw [ramp_eq_zero (by omega) hy, mul_zero]), Finset.sum_range_succ]
  have : ∑ j ∈ Finset.range m, (mid (pre β (j + 1)) - mid (pre β j)) * ramp (j + 1) y =
      ∑ j ∈ Finset.range m, (mid (pre β (j + 1)) - mid (pre β j)) :=
    Finset.sum_congr rfl fun j hj => by
      rw [ramp_eq_one (Finset.mem_range.1 hj) hy0 hy', mul_one]
  rw [this, Finset.sum_range_sub (fun j => mid (pre β j))]
  simp only [pre, List.ofFn_zero]
  ring

theorem continuous_branchX (β : ℕ → Bool) : Continuous (branchX β) := by
  unfold branchX
  refine continuous_const.add (continuous_tsum (u := fun m => (2 : ℝ)⁻¹ ^ m) (fun m => ?_)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) (fun m y => ?_))
  · unfold ramp; fun_prop
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mid_pre_succ_sub,
      abs_of_nonneg (ramp_mem _ _).1]
    have h1 := (ramp_mem (m + 1) y).2
    have h2 : (2 : ℝ)⁻¹ ^ (m + 2) ≤ (2 : ℝ)⁻¹ ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h3 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (m + 2) := by positivity
    nlinarith

theorem dropLast_pre_succ (β : ℕ → Bool) (m : ℕ) : (pre β (m + 1)).dropLast = pre β m := by
  rw [pre_succ, List.dropLast_concat]

theorem branchX_mem_edge (β : ℕ → Bool) {m : ℕ} {y : ℝ} (hy : (2 : ℝ)⁻¹ ^ (m + 1) ≤ y)
    (hy' : y ≤ (2 : ℝ)⁻¹ ^ m) : (⟨branchX β y, y⟩ : ℂ) ∈ edge (pre β (m + 1)) := by
  obtain ⟨hr, h0, h1⟩ := ramp_eq hy hy'
  set l := 2 - 2 ^ (m + 1) * y with hl
  rw [edge, dropLast_pre_succ]
  refine ⟨1 - l, l, by linarith, h0, by ring, ?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, node]
    rw [branchX_eq β hy hy', hr]; ring
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, node, width_pre]
    have := two_pow_mul_inv_two_pow m
    rw [hl, pow_succ, pow_succ]
    linear_combination y * this

theorem pre_prefix (β : ℕ → Bool) {k n : ℕ} (h : k ≤ n) : pre β k <+: pre β n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => rw [pre_succ]; exact ih.trans (List.prefix_append _ _)

theorem abs_limPt_sub_mid_pre (β : ℕ → Bool) (m : ℕ) :
    |limPt β - mid (pre β m)| ≤ (2 : ℝ)⁻¹ ^ (m + 1) := by
  set f : ℕ → ℝ := fun i => if β i then (2 : ℝ)⁻¹ ^ (i + 1) else 0 with hf
  have hb : ∀ i, 0 ≤ f i ∧ f i ≤ (2 : ℝ)⁻¹ ^ (i + 1) := fun i => by
    simp only [hf]; split_ifs <;> refine ⟨?_, ?_⟩ <;> first | positivity | exact le_rfl
  have hg : Summable fun i : ℕ => (2 : ℝ)⁻¹ ^ (i + 1) := by
    simp_rw [pow_succ]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hs : Summable f := Summable.of_nonneg_of_le (fun i => (hb i).1) (fun i => (hb i).2) hg
  have e := hs.sum_add_tsum_nat_add m
  have hT0 : 0 ≤ ∑' i, f (i + m) := tsum_nonneg fun i => (hb _).1
  have hT1 : ∑' i, f (i + m) ≤ (2 : ℝ)⁻¹ ^ m := by
    have hg' : Summable fun i : ℕ => (2 : ℝ)⁻¹ ^ (i + m + 1) :=
      ((summable_nat_add_iff m).2 hg).congr fun i => by ring_nf
    calc ∑' i, f (i + m) ≤ ∑' i : ℕ, (2 : ℝ)⁻¹ ^ (i + m + 1) :=
          Summable.tsum_le_tsum (fun i => (hb _).2) ((summable_nat_add_iff m).2 hs) hg'
      _ = (2 : ℝ)⁻¹ ^ m := by
          simp_rw [show ∀ i : ℕ, (2 : ℝ)⁻¹ ^ (i + m + 1) = (2 : ℝ)⁻¹ ^ (m + 1) * (2 : ℝ)⁻¹ ^ i
            from fun i => by ring]
          rw [tsum_mul_left, tsum_geometric_inv_two, pow_succ]; ring
  have hl : limPt β = left (pre β m) + ∑' i, f (i + m) := by
    rw [limPt, left_pre, ← e]
  rw [hl, mid_pre]
  have : (2 : ℝ)⁻¹ ^ m = 2 * (2 : ℝ)⁻¹ ^ (m + 1) := by rw [pow_succ]; ring
  rw [abs_le]; constructor <;> linarith

/-- Every `y ∈ (0, 1]` lies on some level `[2^{-m-1}, 2^{-m}]`. -/
theorem exists_level {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∃ m : ℕ, (2 : ℝ)⁻¹ ^ (m + 1) ≤ y ∧ y ≤ (2 : ℝ)⁻¹ ^ m := by
  classical
  have hex : ∃ m : ℕ, (2 : ℝ)⁻¹ ^ (m + 1) ≤ y := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hy (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨n, le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | k
  · simpa using hy1
  · have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact (not_le.1 this).le

theorem le_of_level {m N : ℕ} {y : ℝ} (hy : (2 : ℝ)⁻¹ ^ (m + 1) ≤ y) (hN : y < (2 : ℝ)⁻¹ ^ N) :
    N ≤ m := by
  by_contra h
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) (show m + 1 ≤ N by omega)
  linarith

theorem tendsto_branchX (β : ℕ → Bool) :
    Tendsto (branchX β) (𝓝[>] 0) (𝓝 (limPt β)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (ε / 2) by positivity)] with y hy
  obtain ⟨m, hm, hm'⟩ := exists_level hy.1 (hy.2.le.trans (min_le_left _ _))
  have hyε : y < ε / 2 := hy.2.trans_le (min_le_right _ _)
  rw [Real.dist_eq, branchX_eq β hm hm']
  have h1 := abs_limPt_sub_mid_pre β m
  have h2 := abs_mid_pre_succ_sub β m
  obtain ⟨h3, h4⟩ := ramp_mem (m + 1) y
  have h5 : |(mid (pre β (m + 1)) - mid (pre β m)) * ramp (m + 1) y| ≤ (2 : ℝ)⁻¹ ^ (m + 2) := by
    rw [abs_mul, h2, abs_of_nonneg h3]
    exact mul_le_of_le_one_right (by positivity) h4
  have e1 : (2 : ℝ)⁻¹ ^ (m + 2) = (2 : ℝ)⁻¹ ^ (m + 1) / 2 := by rw [pow_succ _ (m + 1)]; ring
  have := abs_sub_le (mid (pre β m) + (mid (pre β (m + 1)) - mid (pre β m)) * ramp (m + 1) y)
    (mid (pre β m)) (limPt β)
  rw [add_sub_cancel_left, abs_sub_comm (mid _)] at this
  linarith

/-- `ψ_{β_σ|m} → 0`. -/
theorem tendsto_psi_pre_enc (σ : ℕ → ℕ) :
    Tendsto (fun m => psi (pre (enc σ) m)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_length_kappa_pre_enc σ)
  refine squeeze_zero (fun m => (psi_pos _).le) (fun m => ?_) h
  simp only [Function.comp, psi]
  have := length_kappa_le_ell (pre (enc σ) m)
  have : ((kappa (pre (enc σ) m)).length : ℝ) ≤ ell (pre (enc σ) m) := by exact_mod_cast this
  gcongr; linarith

/-- Continuity of `g` at `σ` in terms of cylinders. -/
theorem exists_cyl_of_continuous (hgc : Continuous g) (σ : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, ∀ τ : ℕ → ℕ, (∀ i < j, τ i = σ i) → |g τ - g σ| < ε := by
  have hU : g ⁻¹' ball (g σ) ε ∈ 𝓝 σ :=
    hgc.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε)
  obtain ⟨t, ⟨x, n, rfl⟩, hσ, ht⟩ := (PiNat.isTopologicalBasis_cylinders (E := fun _ : ℕ => ℕ)).mem_nhds_iff.1 hU
  refine ⟨n, fun τ hτ => ?_⟩
  have hτ' : τ ∈ PiNat.cylinder x n := by
    rw [← PiNat.mem_cylinder_iff_eq.1 hσ]; exact PiNat.mem_cylinder_iff.2 hτ
  have := ht hτ'
  rwa [mem_preimage, mem_ball, Real.dist_eq] at this

/-- Step 1: every `g σ` is a point asymptotic value of `s`, at `limPt (enc σ)`. -/
theorem isPointAsymptoticValue_g (hgc : Continuous g) (hg : range g ⊆ Ioo (-1 / 2) (1 / 2))
    (σ : ℕ → ℕ) : IsPointAsymptoticValue' upper (sFun g) (limPt (enc σ) : ℂ) (g σ : ℂ) := by
  set β := enc σ with hβ
  set z : ℝ → ℂ := fun y => (branchX β y : ℂ) + (y : ℂ) * Complex.I with hz
  have hzmk : ∀ y, z y = ⟨branchX β y, y⟩ := fun y => by apply Complex.ext <;> simp [hz]
  have hzim : ∀ y, (z y).im = y := fun y => by simp [hz]
  -- the level of small `y`
  have hlev : ∀ N : ℕ, ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < y ∧ ∃ m, N ≤ m ∧
      z y ∈ edge (pre β (m + 1)) ∧ y < (2 : ℝ)⁻¹ ^ N := fun N => by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ N by positivity)] with y hy
    have hy1 : y ≤ 1 := hy.2.le.trans (pow_le_one₀ (by norm_num) (by norm_num))
    obtain ⟨m, hm, hm'⟩ := exists_level hy.1 hy1
    exact ⟨hy.1, m, le_of_level hm hy.2, by rw [hzmk]; exact branchX_mem_edge β hm hm', hy.2⟩
  -- `Ψ → 0`
  have hΨ : Tendsto (fun y => Ψ (z y)) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((tendsto_order.1 (tendsto_psi_pre_enc σ)).2 ε hε)
    filter_upwards [hlev N] with y hyl
    obtain ⟨hy, m, hm, hmem, -⟩ := hyl
    have hy' : 0 < (z y).im := by rw [hzim]; exact hy
    have h1 := Ψ_le_psi hy' (pre β (m + 1))
    rw [dd_eq_zero_of_mem hmem, mul_zero, add_zero] at h1
    have h2 := hN (m + 1) (by omega)
    have h3 := (Ψ_mem hy').1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h3]
    linarith
  -- `R → g σ`
  have hR : Tendsto (fun y => R g (z y)) (𝓝[>] 0) (𝓝 (g σ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_cyl_of_continuous g hgc σ (half_pos hε)
    obtain ⟨k, hk⟩ := (tendsto_atTop.1 (tendsto_length_kappa_pre_enc σ) j).exists
    have key : ∀ w : Word, pre β k <+: w → |rr g w - g σ| < ε / 2 := fun w hw => by
      apply hj
      intro i hi
      have hi' : i < (kappa (pre β k)).length := lt_of_lt_of_le hi hk
      rw [hβ] at hw
      have h1 := cyl_anti (kappa_mono hw) (ext0_mem_cyl (kappa w)) i hi'
      have h2 := kappa_pre_enc σ k i hi'
      rw [h1, h2]
    have hgσ := hg (mem_range_self σ)
    filter_upwards [hlev (k + 1)] with y hyl
    obtain ⟨hy, m, hm, hmem, hyk⟩ := hyl
    have hy' : 0 < (z y).im := by rw [hzim]; exact hy
    have hpre : pre β k <+: pre β (m + 1) := pre_prefix β (by omega)
    have hup := R_le_rr g hg hy' (pre β (m + 1))
    rw [dd_eq_zero_of_mem hmem, mul_zero, add_zero] at hup
    have hup' := key _ hpre
    have hlow : g σ - ε / 2 ≤ R g (z y) := by
      refine claimL_R g hg hy' (by rw [hzim, length_pre]; exact hyk) hpre
        (by rw [length_pre, length_pre]; omega) (by rw [dd_eq_zero_of_mem hmem]; norm_num)
        (by linarith [hgσ.2]) fun w hw _ => ?_
      linarith [(abs_lt.1 (key w hw)).1]
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [(abs_lt.1 hup').2]
  -- the path
  have hsub : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.2 (mem_Iio.1 ht)
  refine ⟨by rw [Complex.frontier_setOfPred_lt_im]; simp, fun t => z (1 - t), ?_, ?_, ?_, ?_⟩
  · exact (((Complex.continuous_ofReal.comp (continuous_branchX β)).add
      (Complex.continuous_ofReal.mul continuous_const)).comp
      (continuous_const.sub continuous_id)).continuousOn
  · intro t ht
    show 0 < (z (1 - t)).im
    rw [hzim]; exact sub_pos.2 ht.2
  · have h1 := (Complex.continuous_ofReal.tendsto _).comp ((tendsto_branchX β).comp hsub)
    have h2 : Tendsto (fun t : ℝ => ((1 - t : ℝ) : ℂ) * Complex.I) (𝓝[<] 1) (𝓝 ((0 : ℝ) * Complex.I)) := by
      refine ((Complex.continuous_ofReal.tendsto _).comp ?_).mul_const _
      exact tendsto_nhdsWithin_iff.1 hsub |>.1
    have := h1.add h2
    simpa [hz] using this
  · have e : ∀ w : ℂ, sFun g w = (R g w : ℂ) + ((Ψ w / 2 : ℝ) : ℂ) * Complex.I := fun w => by
      apply Complex.ext <;> simp [sFun]
    have h1 := (Complex.continuous_ofReal.tendsto _).comp (hR.comp hsub)
    have h2 := ((Complex.continuous_ofReal.tendsto _).comp ((hΨ.comp hsub).div_const 2)).mul_const
      Complex.I
    have := h1.add h2
    simp only [zero_div, Complex.ofReal_zero, zero_mul, add_zero] at this
    refine this.congr fun t => ?_
    simp only [Function.comp, e]

/-! ### Asymptotic values -/

/-- `Ω_k(u)`, `|u| = k`. -/
def Om (u : Word) : Set ℂ :=
  {z | 0 < z.im ∧ z.im < (2 : ℝ)⁻¹ ^ (u.length + 1) ∧
    ∃ v, u <+: v ∧ u.length < v.length ∧ dd v z < 1 / 32}

theorem infDist_upper_compl' {z : ℂ} (hz : 0 ≤ z.im) : infDist z upperᶜ = z.im := by
  apply le_antisymm
  · have hmem : (z.re : ℂ) ∈ upperᶜ := by simp
    refine (infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
    have : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
    rw [dist_eq_norm, this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hz]
  · refine (le_infDist ⟨0, by simp⟩).2 fun w hw => ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hw
    rw [dist_eq_norm]
    have := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im] at this
    linarith [le_abs_self (z.im - w.im)]

theorem eventually_dd_lt {w : Word} {z : ℂ} {c : ℝ} (hz : 0 < z.im) (h : dd w z < c) :
    ∀ᶠ z' in 𝓝 z, 0 < z'.im ∧ dd w z' < c := by
  have h1 : ∀ᶠ z' in 𝓝 z, 0 < z'.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  have hc : ContinuousAt (fun z' : ℂ => infDist z' (edge w) / z'.im) z :=
    (continuous_infDist_pt _).continuousAt.div Complex.continuous_im.continuousAt hz.ne'
  have h2 : ∀ᶠ z' in 𝓝 z, dd w z' < c := hc.eventually_lt continuousAt_const h
  exact h1.and h2

theorem isOpen_Om (u : Word) : IsOpen (Om u) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨h0, h1, v, hv1, hv2, hd⟩
  have h3 : ∀ᶠ z' in 𝓝 z, z'.im < (2 : ℝ)⁻¹ ^ (u.length + 1) :=
    (isOpen_lt Complex.continuous_im continuous_const).mem_nhds h1
  filter_upwards [eventually_dd_lt h0 hd, h3] with z' hz' h3'
  exact ⟨hz'.1, h3', v, hv1, hv2, hz'.2⟩

theorem prefix_of_mem_Om {u u' : Word} {z : ℂ} (hz : z ∈ Om u) (hz' : z ∈ Om u')
    (hl : u.length ≤ u'.length) : u <+: u' := by
  obtain ⟨h0, h1, v, hv1, hv2, hd⟩ := hz
  obtain ⟨-, -, v', hv1', -, hd'⟩ := hz'
  have := (claimL_below h0 h1 hv1 hv2 hd (by linarith : dd v' z ≤ 1 / 12)).1
  exact List.prefix_of_prefix_length_le this hv1' hl

theorem exists_lt_of_Ψ_lt {z : ℂ} {c : ℝ} (hc : c ≤ 1) (h : Ψ z < c) :
    ∃ w, psi w + 16 * dd w z < c := by
  have e : Ψ z = min 1 (⨅ u : Word, (psi u + 16 * dd u z)) := rfl
  have : (⨅ u : Word, (psi u + 16 * dd u z)) < c := by
    by_contra h'
    rw [e] at h
    exact (not_lt.2 (le_min hc (not_lt.1 h'))) h
  exact exists_lt_of_ciInf_lt this

theorem exists_mem_Om {z : ℂ} {k : ℕ} (hz : 0 < z.im) (hzk : z.im < (2 : ℝ)⁻¹ ^ (k + 1))
    (hΨ : Ψ z < 1 / 2) : ∃ u : Word, u.length = k ∧ z ∈ Om u := by
  obtain ⟨w, hw⟩ := exists_lt_of_Ψ_lt (by norm_num) hΨ
  have hd : dd w z < 1 / 32 := by linarith [psi_pos w]
  have hwl : k < w.length := by
    by_contra h
    have := one_le_dd_of_length_le (not_lt.1 h) hz hzk
    linarith
  have hl := List.length_take_of_le hwl.le
  refine ⟨w.take k, hl, hz, ?_, w, List.take_prefix _ _, ?_, hd⟩
  · rw [hl]; exact hzk
  · rw [hl]; exact hwl

/-- A connected tail inside a disjoint union of open sets lies in one of them. -/
theorem exists_eventually_mem {ι : Type*} (O : ι → Set ℂ) (hO : ∀ i, IsOpen (O i))
    (hd : Pairwise fun i j => Disjoint (O i) (O j)) {v : ℝ → ℂ}
    (hvc : ContinuousOn v (Ico 0 1)) (hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), ∃ i, v t ∈ O i) :
    ∃ i, ∀ᶠ t in 𝓝[<] (1 : ℝ), v t ∈ O i := by
  obtain ⟨t0, ht0, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have ht0' : t0 < 1 := ht0
  set t1 := (max t0 0 + 1) / 2 with ht1
  have hm1 := le_max_left t0 0
  have hm2 := le_max_right t0 0
  have hm3 : max t0 0 < 1 := max_lt ht0' one_pos
  have ht1a : t0 < t1 := by rw [ht1]; linarith
  have ht1b : 0 ≤ t1 := by rw [ht1]; linarith
  have ht1c : t1 < 1 := by rw [ht1]; linarith
  obtain ⟨i, hi⟩ : ∃ i, v t1 ∈ O i := hsub ⟨ht1a, ht1c⟩
  have hpc : IsPreconnected (v '' Ico t1 1) :=
    isPreconnected_Ico.image v (hvc.mono (Ico_subset_Ico_left ht1b))
  have hU : v '' Ico t1 1 ⊆ O i ∪ ⋃ j : {j // j ≠ i}, O j.1 := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨j, hj⟩ : ∃ j, v t ∈ O j := hsub ⟨ht1a.trans_le ht.1, ht.2⟩
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.2 ⟨⟨j, hji⟩, hj⟩)
  have hsub' := hpc.subset_left_of_subset_union (hO i) (isOpen_iUnion fun j : {j // j ≠ i} => hO j.1)
    (disjoint_iUnion_right.2 fun j : {j // j ≠ i} => hd (Ne.symm j.2)) hU
    ⟨v t1, ⟨t1, ⟨le_rfl, ht1c⟩, rfl⟩, hi⟩
  refine ⟨i, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT ht1c] with t ht
  exact hsub' ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩

theorem take_pre (β : ℕ → Bool) {j m : ℕ} (h : j ≤ m) : (pre β m).take j = pre β j := by
  have := List.prefix_iff_eq_take.1 (pre_prefix β h)
  rw [length_pre] at this
  exact this.symm

theorem dist_limPt_lt {β : ℕ → Bool} {k : ℕ} {z : ℂ} (hz : z ∈ Om (pre β k)) :
    dist z (limPt β : ℂ) < 2 * (2 : ℝ)⁻¹ ^ k := by
  obtain ⟨h0, h1, w, hw1, hw2, hd⟩ := hz
  rw [length_pre] at h1 hw2
  have hd' : infDist z (edge w) < z.im / 32 := by
    unfold dd at hd; rw [div_lt_iff₀ h0] at hd; linarith
  obtain ⟨p, hp, hzp⟩ := (Metric.infDist_lt_iff (edge_nonempty w)).1 hd'
  have hre := (re_mem_of_mem_edge hw2 hp).1
  have e : w.take k = pre β k := by
    have := List.prefix_iff_eq_take.1 hw1
    rw [length_pre] at this
    exact this.symm
  rw [e] at hre
  obtain ⟨hp1, hp2⟩ := hre
  have hre' : |z.re - p.re| ≤ dist z p := by
    rw [Complex.dist_eq]; simpa using Complex.abs_re_le_norm (z - p)
  have hlim := abs_limPt_sub_mid_pre β k
  have hw := width_pre β k
  have hpow : (2 : ℝ)⁻¹ ^ (k + 1) = (2 : ℝ)⁻¹ ^ k / 2 := by rw [pow_succ]; ring
  have hm : mid (pre β k) = left (pre β k) + width (pre β k) / 2 := rfl
  have hn : dist z (limPt β : ℂ) ≤ |z.re - limPt β| + |z.im| := by
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp
  rw [abs_of_pos h0] at hn
  have h3 := abs_sub_le z.re p.re (limPt β)
  have h4 : |p.re - limPt β| ≤ (2 : ℝ)⁻¹ ^ k / 2 + (2 : ℝ)⁻¹ ^ (k + 1) := by
    rw [abs_le] at hlim ⊢; constructor <;> linarith [hlim.1, hlim.2]
  have h5 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  linarith

/-- Tail argument: along a path with `Im → 0` and `Ψ → 0` there is a branch `β` such that each
tail eventually lies in `Ω_k(β|k)`; the path tends to `limPt β`. -/
theorem exists_branch {v : ℝ → ℂ} (hvc : ContinuousOn v (Ico 0 1)) (hvm : MapsTo v (Ico 0 1) upper)
    (him : Tendsto (fun t => (v t).im) (𝓝[<] 1) (𝓝 0))
    (hΨ : Tendsto (fun t => Ψ (v t)) (𝓝[<] 1) (𝓝 0)) :
    ∃ β : ℕ → Bool, (∀ k, ∀ᶠ t in 𝓝[<] 1, v t ∈ Om (pre β k)) ∧
      Tendsto v (𝓝[<] 1) (𝓝 (limPt β : ℂ)) := by
  have hk : ∀ k : ℕ, ∃ u : {u : Word // u.length = k}, ∀ᶠ t in 𝓝[<] (1 : ℝ), v t ∈ Om u.1 := by
    intro k
    apply exists_eventually_mem (fun u : {u : Word // u.length = k} => Om u.1)
      (fun u => isOpen_Om u.1) _ hvc
    · have h1 : ∀ᶠ t in 𝓝[<] (1 : ℝ), (v t).im < (2 : ℝ)⁻¹ ^ (k + 1) :=
        (tendsto_order.1 him).2 _ (by positivity)
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), Ψ (v t) < 1 / 2 := (tendsto_order.1 hΨ).2 _ (by norm_num)
      filter_upwards [h1, h2, Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht1 ht2 ht3
      obtain ⟨u, hu, hz⟩ := exists_mem_Om (hvm ⟨ht3.1.le, ht3.2⟩) ht1 ht2
      exact ⟨⟨u, hu⟩, hz⟩
    · rintro ⟨u, hu⟩ ⟨u', hu'⟩ hne
      refine Set.disjoint_left.2 fun z hz hz' => hne (Subtype.ext ?_)
      exact List.IsPrefix.eq_of_length (prefix_of_mem_Om hz hz' (by rw [hu, hu']))
        (by rw [hu, hu'])
  choose U hU using hk
  have hpre : ∀ j k, j ≤ k → (U j).1 <+: (U k).1 := by
    intro j k hjk
    obtain ⟨t, h1, h2⟩ := ((hU j).and (hU k)).exists
    exact prefix_of_mem_Om h1 h2 (by rw [(U j).2, (U k).2]; exact hjk)
  let β : ℕ → Bool := fun n => (U (n + 1)).1.getD n false
  have hβ : ∀ k, pre β k = (U k).1 := by
    intro k
    apply List.ext_getElem (by rw [length_pre, (U k).2])
    intro i h1 h2
    rw [length_pre] at h1
    simp only [pre, List.getElem_ofFn]
    have hi : i < (U (i + 1)).1.length := by rw [(U (i + 1)).2]; omega
    show (U (i + 1)).1.getD i false = _
    rw [List.getD_eq_getElem _ _ hi]
    exact (hpre (i + 1) k (by omega)).getElem hi
  refine ⟨β, fun k => by rw [hβ k]; exact hU k, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (2 : ℝ)⁻¹ < 1)
  filter_upwards [hU k] with t ht
  rw [← hβ k] at ht
  have := dist_limPt_lt ht
  linarith

/-- The side region `S_i = {z : ∃ w ⊒ (β|i) 1, d_w(z) < 1/32}`. -/
def Side (β : ℕ → Bool) (i : ℕ) : Set ℂ :=
  {z | 0 < z.im ∧ ∃ w, pre β i ++ [true] <+: w ∧ dd w z < 1 / 32}

theorem isOpen_Side (β : ℕ → Bool) (i : ℕ) : IsOpen (Side β i) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨h0, w, hw, hd⟩
  filter_upwards [eventually_dd_lt h0 hd] with z' hz'
  exact ⟨hz'.1, w, hw, hz'.2⟩

/-- Case 2: no path with `Ψ → 0` follows a branch `t 0^∞`. -/
theorem not_finite_branch {v : ℝ → ℂ} (hvc : ContinuousOn v (Ico 0 1))
    (_hvm : MapsTo v (Ico 0 1) upper) (hΨ : Tendsto (fun t => Ψ (v t)) (𝓝[<] 1) (𝓝 0))
    {β : ℕ → Bool} (hβ : ∀ k, ∀ᶠ t in 𝓝[<] 1, v t ∈ Om (pre β k)) :
    {n | β n = true}.Infinite := by
  by_contra hfin
  rw [not_infinite] at hfin
  obtain ⟨n, hzero, hell⟩ := exists_zeros hfin
  have hpsi : ∀ m ≥ n, psi (pre β m) = 1 / (n + 2) := fun m hm => by rw [psi, hell m hm]
  have hsep : ∀ i ≥ n, ∀ w w' : Word, pre β i ++ [true] <+: w → pre β (i + 1) <+: w' →
      i + 1 < w'.length → Separated w w' := by
    intro i hi w w' hw hw' hl
    rw [pre_succ, hzero i hi] at hw'
    exact separated_of_one_zero hw hw' (by rw [length_pre]; omega)
  have hSd0 : ∀ i j, i < j → Disjoint (Side β (n + i)) (Side β (n + j)) := by
    intro i j h
    refine Set.disjoint_left.2 fun z hz hz' => ?_
    obtain ⟨h0, w, hw, hd⟩ := hz
    obtain ⟨-, w', hw', hd'⟩ := hz'
    have h1 : pre β (n + i + 1) <+: w' :=
      (pre_prefix β (by omega : n + i + 1 ≤ n + j)).trans ((List.prefix_append _ _).trans hw')
    have hl : n + i + 1 < w'.length := by
      have := hw'.length_le; simp [length_pre] at this; omega
    have := dd_gt_of_separated (hsep (n + i) (by omega) w w' hw h1 hl) h0 hd
    linarith
  have hSd : Pairwise fun i j => Disjoint (Side β (n + i)) (Side β (n + j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hSd0 i j h
    · exact (hSd0 j i h).symm
  have hc0 : (0 : ℝ) < 1 / (n + 2) := by positivity
  have hc1 : (1 : ℝ) / (n + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), ∃ j, v t ∈ Side β (n + j) := by
    have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), Ψ (v t) < 1 / (n + 2) / 2 :=
      (tendsto_order.1 hΨ).2 _ (by positivity)
    filter_upwards [hβ n, h2] with t ht ht2
    obtain ⟨h0, h1, v0, hv1, hv2, hd0⟩ := ht
    obtain ⟨w, hw⟩ := exists_lt_of_Ψ_lt (by linarith) ht2
    have hdw : dd w (v t) < 1 / 32 := by linarith [psi_pos w]
    have hpw : psi w < 1 / (n + 2) / 2 := by linarith [dd_nonneg w h0]
    obtain ⟨hnw, hlw⟩ := claimL_below h0 h1 hv1 hv2 hd0 (by linarith : dd w (v t) ≤ 1 / 12)
    rw [length_pre] at hlw
    have hne' : w ≠ pre β w.length := by
      intro h; rw [h, hpsi _ hlw.le] at hpw; linarith
    have hne : w.take w.length ≠ (pre β w.length).take w.length := by
      rwa [List.take_length, take_pre β le_rfl]
    obtain ⟨u, b, hu, hub, hub'⟩ :=
      exists_split_of_take_ne le_rfl (length_pre β w.length).ge hne
    have hu1 : u <+: pre β w.length := (List.prefix_append _ _).trans hub'
    have e : u = pre β u.length := by
      rw [← take_pre β hu.le]; exact List.prefix_iff_eq_take.1 hu1
    have hbu : β u.length = !b := by
      have := hub'.getElem (by simp : u.length < (u ++ [!b]).length)
      simp [pre] at this
      simp [this]
    have hnu : n ≤ u.length := by
      by_contra h
      have h3 : pre β (u.length + 1) <+: w :=
        (pre_prefix β (by omega : u.length + 1 ≤ n)).trans hnw
      rw [pre_succ, ← e, hbu] at h3
      have h4 := h3.getElem (by simp : u.length < (u ++ [!b]).length)
      have h5 := hub.getElem (by simp : u.length < (u ++ [b]).length)
      simp at h4 h5
      rw [← h5] at h4
      cases b <;> simp at h4
    have hb : b = true := by
      have := hzero _ hnu
      rw [hbu] at this
      simpa using this
    refine ⟨u.length - n, h0, w, ?_, hdw⟩
    rw [show n + (u.length - n) = u.length by omega, ← e, ← hb]
    exact hub
  obtain ⟨j, hj⟩ := exists_eventually_mem (fun j => Side β (n + j)) (fun j => isOpen_Side β _)
    hSd hvc hev
  obtain ⟨t, ht1, ht2⟩ := (hj.and (hβ (n + j + 1))).exists
  obtain ⟨h0, w, hw, hd⟩ := ht1
  obtain ⟨-, -, w', hw', hl', hd'⟩ := ht2
  rw [length_pre] at hl'
  have := dd_gt_of_separated (hsep (n + j) (by omega) w w' hw hw' hl') h0 hd
  linarith

/-- Step 2: a real asymptotic value of `s` is a point asymptotic value and lies in `range g`. -/
theorem mem_range_of_isAsymptoticValue (hgc : Continuous g)
    (hg : range g ⊆ Ioo (-1 / 2) (1 / 2)) {b : ℝ}
    (hb : IsAsymptoticValue' upper (sFun g) (b : ℂ)) :
    b ∈ range g ∧ ∃ p, IsPointAsymptoticValue' upper (sFun g) p (b : ℂ) := by
  obtain ⟨v, hvc, hvm, hvd, hvf⟩ := hb
  have hI01 : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
  have him : Tendsto (fun t => (v t).im) (𝓝[<] 1) (𝓝 0) := by
    refine hvd.congr' ?_
    filter_upwards [hI01] with t ht
    exact infDist_upper_compl' (hvm ⟨ht.1.le, ht.2⟩).le
  have hR : Tendsto (fun t => R g (v t)) (𝓝[<] 1) (𝓝 b) := by
    have := (Complex.continuous_re.tendsto _).comp hvf
    simpa [Function.comp_def, sFun] using this
  have hΨ2 : Tendsto (fun t => Ψ (v t) / 2) (𝓝[<] 1) (𝓝 0) := by
    have := (Complex.continuous_im.tendsto _).comp hvf
    simpa [Function.comp_def, sFun] using this
  have hΨ : Tendsto (fun t => Ψ (v t)) (𝓝[<] 1) (𝓝 0) := by
    have := hΨ2.const_mul 2
    simp only [mul_zero] at this
    exact this.congr fun t => by ring
  obtain ⟨β, hβ, hlim⟩ := exists_branch hvc hvm him hΨ
  obtain ⟨σ, hσ⟩ := exists_enc_eq (not_finite_branch hvc hvm hΨ hβ)
  have hfront : ((limPt β : ℝ) : ℂ) ∈ frontier upper := by
    rw [Complex.frontier_setOfPred_lt_im]; simp
  refine ⟨?_, limPt β, hfront, v, hvc, hvm, hlim, hvf⟩
  have hR' : Tendsto (fun t => R g (v t)) (𝓝[<] 1) (𝓝 (g σ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_cyl_of_continuous g hgc σ (half_pos hε)
    obtain ⟨k, hk⟩ := (tendsto_atTop.1 (tendsto_length_kappa_pre_enc σ) j).exists
    have key : ∀ w : Word, pre β k <+: w → |rr g w - g σ| < ε / 2 := fun w hw => by
      apply hj
      intro i hi
      have hi' : i < (kappa (pre (enc σ) k)).length := lt_of_lt_of_le hi hk
      rw [← hσ] at hw
      have h1 := cyl_anti (kappa_mono hw) (ext0_mem_cyl (kappa w)) i hi'
      have h2 := kappa_pre_enc σ k i hi'
      rw [h1, h2]
    have hgσ := hg (mem_range_self σ)
    have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), Ψ (v t) < min (ε / 2) (1 / 2) :=
      (tendsto_order.1 hΨ).2 _ (by positivity)
    filter_upwards [hβ k, h2] with t ht hψ
    obtain ⟨h0, h1, v0, hv1, hv2, hd0⟩ := ht
    have hlow : g σ - ε / 2 ≤ R g (v t) := by
      refine claimL_R g hg h0 h1 hv1 hv2 hd0 (by linarith [hgσ.2]) fun w hw _ => ?_
      linarith [(abs_lt.1 (key w hw)).1]
    have hm1 := min_le_left (ε / 2) (1 / 2)
    have hm2 := min_le_right (ε / 2) (1 / 2)
    obtain ⟨w, hw⟩ := exists_lt_of_Ψ_lt (by linarith) hψ
    have hdw : dd w (v t) ≤ 1 / 12 := by linarith [psi_pos w]
    have hww := (claimL_below h0 h1 hv1 hv2 hd0 hdw).1
    have hup := R_le_rr g hg h0 w
    have := (abs_lt.1 (key w hww)).2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [psi_pos w, dd_nonneg w h0]
  exact ⟨σ, (tendsto_nhds_unique hR hR').symm⟩

end Fun

/-! ### `lem:cube-lemma-elementary` -/

theorem isAsymptoticValue'_congr {f f' : ℂ → ℂ} (h : EqOn f f' upper) {a : ℂ} :
    IsAsymptoticValue' upper f a ↔ IsAsymptoticValue' upper f' a := by
  constructor <;> rintro ⟨v, hc, hm, hd, hf⟩ <;> refine ⟨v, hc, hm, hd, hf.congr' ?_⟩ <;>
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  · exact h (hm ⟨ht.1.le, ht.2⟩)
  · exact (h (hm ⟨ht.1.le, ht.2⟩)).symm

theorem isPointAsymptoticValue'_congr {f f' : ℂ → ℂ} (h : EqOn f f' upper) {p a : ℂ} :
    IsPointAsymptoticValue' upper f p a ↔ IsPointAsymptoticValue' upper f' p a := by
  constructor <;> rintro ⟨hp, v, hc, hm, hd, hf⟩ <;> refine ⟨hp, v, hc, hm, hd, hf.congr' ?_⟩ <;>
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  · exact h (hm ⟨ht.1.le, ht.2⟩)
  · exact (h (hm ⟨ht.1.le, ht.2⟩)).symm

/-- `lem:cube-lemma-elementary`: the statement of `TJK.Cube.exists_s` (with the primed copies of
`def:asymptotic`), proved from `fact:analytic-nonborel` alone. -/
theorem exists_s' : ∃ s : ℂ → ℂ, ContinuousOn s upper ∧ (∀ z, ‖s z‖ < 1) ∧
    {b : ℝ | b ∈ Ioo (-1) 1 ∧ IsAsymptoticValue' upper s (b : ℂ)} =
      {b : ℝ | b ∈ Ioo (-1) 1 ∧ ∃ p, IsPointAsymptoticValue' upper s p (b : ℂ)} ∧
    ¬ MeasurableSet {b : ℝ | b ∈ Ioo (-1) 1 ∧ IsAsymptoticValue' upper s (b : ℂ)} := by
  obtain ⟨g, hgc, hgr, hgm⟩ := exists_g
  obtain ⟨s, hs⟩ : ∃ s : ℂ → ℂ, s = fun z => if 0 < z.im then sFun g z else 0 := ⟨_, rfl⟩
  have hEq : EqOn s (sFun g) upper := fun z hz => by
    rw [hs]; exact if_pos hz
  have hmem : ∀ σ, g σ ∈ Ioo (-1 : ℝ) 1 := fun σ => by
    have := hgr (mem_range_self σ)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have e1 : {b : ℝ | b ∈ Ioo (-1) 1 ∧ IsAsymptoticValue' upper s (b : ℂ)} = range g := by
    ext b
    simp only [mem_ofPred_eq, isAsymptoticValue'_congr hEq]
    constructor
    · rintro ⟨-, hb⟩; exact (mem_range_of_isAsymptoticValue g hgc hgr hb).1
    · rintro ⟨σ, rfl⟩
      exact ⟨hmem σ, (isPointAsymptoticValue_g g hgc hgr σ).isAsymptoticValue'⟩
  have e2 : {b : ℝ | b ∈ Ioo (-1) 1 ∧ ∃ p, IsPointAsymptoticValue' upper s p (b : ℂ)} =
      range g := by
    ext b
    simp only [mem_ofPred_eq, isPointAsymptoticValue'_congr hEq]
    constructor
    · rintro ⟨-, p, hp⟩
      exact (mem_range_of_isAsymptoticValue g hgc hgr hp.isAsymptoticValue').1
    · rintro ⟨σ, rfl⟩
      exact ⟨hmem σ, _, isPointAsymptoticValue_g g hgc hgr σ⟩
  refine ⟨s, (continuousOn_sFun g hgr).congr hEq, fun z => ?_, by rw [e1, e2], by
    rw [e1]; exact hgm⟩
  rw [hs]
  dsimp only
  split_ifs with hz
  · exact norm_sFun_lt_one g hgr z hz
  · simp

end TJK.Cube.Elementary
