import Mathlib
import TJK.Defs
import TJK.Baire.Basic
import TJK.Baire.Approx
import TJK.Construct.Regions
import TJK.Construct.K

/-!
# The function `h` (blueprint §F, `thm:construct-B`)

Formalizes `thm:construct-B` of `paper/sections/F-construct.tex`: for `E ⊆ (-1, 1)` and
`φ : E → ℝ^m` of honorary Baire class `≤ 2` there is a continuous `h` on the upper half-plane
that tends to `φ(p)` along a segment at each `p ∈ E` of slope `< √2 - 1` (hence inside the Stolz
angle `s(p, 1, 3π/8)`); if `φ` is bounded, `h` can be taken bounded.

Points `⟨x, y⟩` are complex numbers with `x = z.re`, `y = z.im`. The segment at `p` with slope
`c` is `y ↦ (p + c y) + i y`, `0 < y`.

Compared with the blueprint: the left inverse `u` is written directly as
`u(x, y) = sup {p : p + y·c(p) ≤ x}` (continuity in `x` as in `lem:monotone-inverse`, joint
continuity from `|c| ≤ 1`), the enumeration of the countable set may be partial, and `h₀` is
written with hat functions in `1/y`.
-/

open _root_.Set Filter Topology Real

namespace TJK.Construct

/-! ### An explicit monotone left inverse -/

/-- The left inverse `t ↦ sup ({-1} ∪ {x ∈ (-1, 1) : f x ≤ t})` of `lem:monotone-inverse` (a). -/
noncomputable def leftInv (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup (insert (-1) {x | x ∈ Ioo (-1 : ℝ) 1 ∧ f x ≤ t})

theorem leftInv_bddAbove (f : ℝ → ℝ) (t : ℝ) :
    BddAbove (insert (-1) {x | x ∈ Ioo (-1 : ℝ) 1 ∧ f x ≤ t}) := by
  refine ⟨1, ?_⟩
  rintro x (rfl | ⟨hx, -⟩)
  · norm_num
  · exact hx.2.le

theorem leftInv_mem (f : ℝ → ℝ) (t : ℝ) : leftInv f t ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_csSup (leftInv_bddAbove f t) (mem_insert _ _),
    csSup_le ⟨-1, mem_insert _ _⟩ fun x hx => by
      rcases hx with rfl | ⟨hx, -⟩
      · norm_num
      · exact hx.2.le⟩

theorem leftInv_le_leftInv {f f' : ℝ → ℝ} {t t' : ℝ}
    (h : ∀ x ∈ Ioo (-1 : ℝ) 1, f' x ≤ t' → f x ≤ t) : leftInv f' t' ≤ leftInv f t :=
  csSup_le_csSup (leftInv_bddAbove f t) ⟨-1, mem_insert _ _⟩
    (insert_subset_insert fun x ⟨hx, h'⟩ => ⟨hx, h x hx h'⟩)

theorem leftInv_mono (f : ℝ → ℝ) : Monotone (leftInv f) := fun _ _ hst =>
  leftInv_le_leftInv fun _ _ h => h.trans hst

theorem leftInv_eq {f : ℝ → ℝ} {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) (h1 : f s ≤ t)
    (h2 : ∀ q ∈ Ioo (-1 : ℝ) 1, s < q → t < f q) : leftInv f t = s := by
  refine IsGreatest.csSup_eq ⟨Or.inr ⟨hs, h1⟩, ?_⟩
  rintro q (rfl | ⟨hq, hfq⟩)
  · exact hs.1.le
  · by_contra hlt
    exact absurd hfq (not_le.2 (h2 q hq (not_le.1 hlt)))

theorem continuous_leftInv {f : ℝ → ℝ} (hf : StrictMonoOn f (Ioo (-1) 1)) :
    Continuous (leftInv f) := by
  have hinv : ∀ x ∈ Ioo (-1 : ℝ) 1, leftInv f (f x) = x := fun x hx =>
    leftInv_eq hx le_rfl fun q hq hxq => hf hx hq hxq
  let G : ℝ → Icc (-1 : ℝ) 1 := fun t => ⟨leftInv f t, leftInv_mem f t⟩
  have hG : Monotone G := fun s t hst => leftInv_mono f hst
  have : Nontrivial (Icc (-1 : ℝ) 1) :=
    ⟨⟨⟨-1, by norm_num⟩, ⟨1, by norm_num⟩, by simp [Subtype.ext_iff]; norm_num⟩⟩
  have hdense : DenseRange G := by
    refine dense_of_exists_between fun a b hab => ?_
    have hab' : (a : ℝ) < b := hab
    have hc : ((a : ℝ) + b) / 2 ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [a.2.1], by linarith [b.2.2]⟩
    refine ⟨G (f (((a : ℝ) + b) / 2)), mem_range_self _, ?_, ?_⟩
    · change (a : ℝ) < leftInv f (f _)
      rw [hinv _ hc]; linarith
    · change leftInv f (f _) < (b : ℝ)
      rw [hinv _ hc]; linarith
  exact continuous_subtype_val.comp (hG.continuous_of_denseRange hdense)

/-! ### The jump function `c(x) = Σ_{s_n < x} w(n)` -/

/-- The weights `w(n) = 2^{-(n+3)}`, with sum `1/4`. -/
noncomputable def wt (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 3)

theorem wt_pos (n : ℕ) : 0 < wt n := by unfold wt; positivity

theorem wt_le (n : ℕ) : wt n ≤ 1 / 8 := by
  unfold wt
  rw [pow_add]
  have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

theorem summable_wt : Summable wt := by
  have : wt = fun n => (1 / 8 : ℝ) * (1 / 2) ^ n := by
    funext n; unfold wt; rw [pow_add]; norm_num; ring
  rw [this]
  exact summable_geometric_two.mul_left _

theorem tsum_wt : ∑' n, wt n = 1 / 4 := by
  have : wt = fun n => (1 / 8 : ℝ) * (1 / 2) ^ n := by
    funext n; unfold wt; rw [pow_add]; norm_num; ring
  rw [this, tsum_mul_left, tsum_geometric_two]
  norm_num

/-- `c(p) = Σ_{s n < p} w(n)`; the blueprint's `f` is `p ↦ p + c(p)`. -/
noncomputable def jump (s : ℕ → ℝ) (p : ℝ) : ℝ := ∑' n, if s n < p then wt n else 0

theorem summable_jump (s : ℕ → ℝ) (p : ℝ) :
    Summable fun n => if s n < p then wt n else 0 :=
  summable_wt.of_nonneg_of_le (fun n => by split_ifs <;> simp [(wt_pos n).le])
    (fun n => by split_ifs <;> simp [(wt_pos n).le])

theorem jump_nonneg (s : ℕ → ℝ) (p : ℝ) : 0 ≤ jump s p :=
  tsum_nonneg fun n => by split_ifs <;> simp [(wt_pos n).le]

theorem jump_le (s : ℕ → ℝ) (p : ℝ) : jump s p ≤ 1 / 4 := by
  rw [← tsum_wt]
  exact (summable_jump s p).tsum_le_tsum (fun n => by split_ifs <;> simp [(wt_pos n).le])
    summable_wt

theorem jump_mono (s : ℕ → ℝ) : Monotone (jump s) := fun p q hpq =>
  (summable_jump s p).tsum_le_tsum
    (fun n => by
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (h1.trans_le hpq) h2
      · exact (wt_pos n).le
      · exact le_rfl)
    (summable_jump s q)

theorem jump_add_le (s : ℕ → ℝ) {n : ℕ} {q : ℝ} (h : s n < q) :
    jump s (s n) + wt n ≤ jump s q := by
  have h1 : jump s (s n) + wt n =
      ∑' k, ((if s k < s n then wt k else 0) + if k = n then wt k else 0) := by
    rw [(summable_jump s (s n)).tsum_add (summable_of_ne_finset_zero (s := {n})
      (fun k hk => by simp at hk; simp [hk])), tsum_ite_eq]
    rfl
  rw [h1]
  refine Summable.tsum_le_tsum (fun k => ?_)
    ((summable_jump s (s n)).add (summable_of_ne_finset_zero (s := {n})
      (fun k hk => by simp at hk; simp [hk])))
    (summable_jump s q)
  by_cases hk : k = n
  · subst hk; simp [h]
  · simp only [hk, if_false, add_zero]
    split_ifs with h2 h3
    · exact le_rfl
    · exact absurd (h2.trans h) h3
    · exact (wt_pos k).le
    · exact le_rfl

/-! ### The function `u` -/

theorem strictMono_add_mul_jump (s : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    StrictMono fun p => p + a * jump s p := fun p q hpq => by
  have := mul_le_mul_of_nonneg_left (jump_mono s hpq.le) ha
  dsimp only; linarith

/-- `u(x, y) = sup {p ∈ (-1, 1) : p + y·c(p) ≤ x}` (with `y` replaced by `max y 0`): the point
`p` whose segment of slope `c(p)` passes through `⟨x, y⟩`. -/
noncomputable def lineU (s : ℕ → ℝ) (z : ℂ) : ℝ :=
  leftInv (fun p => p + max z.im 0 * jump s p) z.re

theorem leftInv_le_leftInv_add (s : ℕ → ℝ) (a a' x : ℝ) :
    leftInv (fun p => p + a' * jump s p) x ≤
      leftInv (fun p => p + a * jump s p) (x + |a - a'|) := by
  refine leftInv_le_leftInv fun p _ hp => ?_
  have h0 := jump_nonneg s p
  have h1 : jump s p ≤ 1 := (jump_le s p).trans (by norm_num)
  have h2 : (a - a') * jump s p ≤ |a - a'| * jump s p :=
    mul_le_mul_of_nonneg_right (le_abs_self _) h0
  have h3 : |a - a'| * jump s p ≤ |a - a'| := mul_le_of_le_one_right (abs_nonneg _) h1
  nlinarith

theorem continuous_lineU (s : ℕ → ℝ) : Continuous (lineU s) := by
  rw [Metric.continuous_iff]
  intro z₀ ε hε
  set a₀ := max z₀.im 0
  have hg : Continuous (leftInv fun p => p + a₀ * jump s p) :=
    continuous_leftInv ((strictMono_add_mul_jump s (le_max_right z₀.im 0)).strictMonoOn _)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hg z₀.re ε hε
  refine ⟨δ / 2, half_pos hδ, fun z hz => ?_⟩
  rw [Complex.dist_eq] at hz
  have hre : |z.re - z₀.re| < δ / 2 :=
    (Complex.abs_re_le_norm (z - z₀)).trans_lt (by simpa using hz)
  have him : |z.im - z₀.im| < δ / 2 :=
    (Complex.abs_im_le_norm (z - z₀)).trans_lt (by simpa using hz)
  have ha : |max z.im 0 - a₀| ≤ δ / 2 := (abs_max_sub_max_le_abs _ _ _).trans him.le
  have h1 : lineU s z ≤ leftInv (fun p => p + a₀ * jump s p) (z.re + δ / 2) :=
    (leftInv_le_leftInv_add s a₀ (max z.im 0) z.re).trans
      (leftInv_mono _ (by rw [abs_sub_comm] at ha; linarith))
  have h2 : leftInv (fun p => p + a₀ * jump s p) (z.re - δ / 2) ≤ lineU s z :=
    (leftInv_le_leftInv_add s (max z.im 0) a₀ (z.re - δ / 2)).trans
      (leftInv_mono _ (by linarith))
  have h3 := hδε (z.re + δ / 2) (by rw [Real.dist_eq, abs_lt] at *; constructor <;> linarith)
  have h4 := hδε (z.re - δ / 2) (by rw [Real.dist_eq, abs_lt] at *; constructor <;> linarith)
  have h5 : lineU s z₀ = leftInv (fun p => p + a₀ * jump s p) z₀.re := rfl
  rw [Real.dist_eq, abs_lt] at h3 h4 ⊢
  rw [h5]
  constructor <;> linarith

/-- The point at height `y` of the segment at `p` with slope `c`. -/
noncomputable def seg (p c y : ℝ) : ℂ := ((p + c * y : ℝ) : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem seg_re (p c y : ℝ) : (seg p c y).re = p + c * y := by simp [seg]

@[simp] theorem seg_im (p c y : ℝ) : (seg p c y).im = y := by simp [seg]

/-- `u` is constant `= p` along the segment at `p` of slope `c`, whenever `c(p) ≤ c ≤ c(q)` for
`q > p`. -/
theorem lineU_seg (s : ℕ → ℝ) {p c y : ℝ} (hp : p ∈ Ioo (-1 : ℝ) 1) (hy : 0 < y)
    (hc1 : jump s p ≤ c) (hc2 : ∀ q, p < q → c ≤ jump s q) :
    lineU s (seg p c y) = p := by
  unfold lineU
  rw [seg_re, seg_im, max_eq_left hy.le]
  refine leftInv_eq hp ?_ fun q _ hpq => ?_
  · have := mul_le_mul_of_nonneg_left hc1 hy.le
    linarith
  · have := mul_le_mul_of_nonneg_left (hc2 q hpq) hy.le
    linarith

/-! ### Hat functions and interpolation -/

/-- The hat function `max 0 (1 - |t|)`. -/
noncomputable def hat (t : ℝ) : ℝ := max 0 (1 - |t|)

theorem continuous_hat : Continuous hat := by unfold hat; fun_prop

theorem hat_nonneg (t : ℝ) : 0 ≤ hat t := le_max_left _ _

theorem hat_eq_zero {t : ℝ} (h : 1 ≤ |t|) : hat t = 0 := max_eq_left (by linarith)

theorem sum_hat (t : ℝ) (ht : 0 ≤ t) (K : ℕ) :
    ∑ n ∈ Finset.range K, hat (t - n) = min 1 (max 0 (K - t)) := by
  induction K with
  | zero => simp [ht]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    unfold hat
    have key : ∀ a : ℝ, min 1 (max 0 a) + max 0 (1 - |a|) = min 1 (max 0 (a + 1)) := by
      intro a
      rcases le_total 0 a with h | h
      · rw [abs_of_nonneg h]
        rcases le_total a 1 with h' | h'
        · rw [max_eq_right h, min_eq_right h', max_eq_right (by linarith),
            max_eq_right (by linarith), min_eq_left (by linarith)]
          ring
        · rw [max_eq_right h, min_eq_left h', max_eq_left (by linarith),
            max_eq_right (by linarith), min_eq_left (by linarith)]
          ring
      · rw [abs_of_nonpos h, max_eq_left h, min_eq_right zero_le_one]
        rcases le_total a (-1) with h' | h'
        · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
          simp
        · rw [max_eq_right (by linarith), max_eq_right (by linarith),
            min_eq_right (by linarith)]
          ring
    have := key (K - t)
    rw [abs_sub_comm] at this
    convert this using 3; ring

/-- Interpolating a convergent sequence by hat functions gives a function convergent at `∞`. -/
theorem tendsto_tsum_hat {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {a : ℕ → V}
    {L : V} (ha : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => ∑' n : ℕ, hat (t - n) • a n) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (half_pos hε)
  refine ⟨N + 1, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  set K := ⌊t⌋₊ + 2
  have hK : t + 1 < K := by
    have := Nat.lt_floor_add_one t
    simp only [K]; push_cast; linarith
  have hzero : ∀ n ∉ Finset.range K, hat (t - n) = 0 := fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    have : (K : ℝ) ≤ n := by exact_mod_cast hn
    exact hat_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)
  rw [tsum_eq_sum (s := Finset.range K) fun n hn => by rw [hzero n hn, zero_smul]]
  have hsum : ∑ n ∈ Finset.range K, hat (t - n) = 1 := by
    rw [sum_hat t ht0, max_eq_right (by linarith), min_eq_left (by linarith)]
  have hdiff : ∑ n ∈ Finset.range K, hat (t - n) • a n - L =
      ∑ n ∈ Finset.range K, hat (t - n) • (a n - L) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  rw [dist_eq_norm, hdiff]
  refine lt_of_le_of_lt (norm_sum_le _ _) ?_
  calc ∑ n ∈ Finset.range K, ‖hat (t - n) • (a n - L)‖
      ≤ ∑ n ∈ Finset.range K, hat (t - n) * (ε / 2) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (hat_nonneg _)]
        by_cases hn : N ≤ n
        · exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact (hN n hn).le)
            (hat_nonneg _)
        · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast (not_le.1 hn)
          rw [hat_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)]
          simp
    _ = ε / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    _ < ε := half_lt_self hε

/-! ### Locally finite sums on the upper half-plane -/

theorem isOpen_upper : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im

theorem continuousOn_tsum_upper {V : Type*} [NormedAddCommGroup V] {A : ℕ → ℂ → V}
    (hA : ∀ n, ContinuousOn (A n) upper)
    (h0 : ∀ (n : ℕ) (z : ℂ), 0 < z.im → z.im⁻¹ + 1 ≤ n → A n z = 0) :
    ContinuousOn (fun z => ∑' n, A n z) upper := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  obtain ⟨K, hK⟩ := exists_nat_ge (2 / z₀.im + 1)
  have hmem : {z : ℂ | z₀.im / 2 < z.im} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp; linarith)
  have hEq : (fun z => ∑' n, A n z) =ᶠ[𝓝 z₀] fun z => ∑ n ∈ Finset.range K, A n z := by
    filter_upwards [hmem] with z hz
    have hz' : z₀.im / 2 < z.im := hz
    have hzpos : 0 < z.im := by linarith
    refine tsum_eq_sum fun n hn => h0 n z hzpos ?_
    simp only [Finset.mem_range, not_lt] at hn
    have hn' : (K : ℝ) ≤ n := by exact_mod_cast hn
    have : z.im⁻¹ < 2 / z₀.im := by
      rw [inv_eq_one_div, div_lt_div_iff₀ hzpos hz₀']
      linarith
    linarith
  have hc : ContinuousAt (fun z => ∑ n ∈ Finset.range K, A n z) z₀ :=
    (continuousOn_finsetSum _ fun n _ => hA n).continuousAt (isOpen_upper.mem_nhds hz₀)
  exact (hc.congr hEq.symm).continuousWithinAt

/-! ### The function `h₀` -/

section HZero

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `h₀(z) = Σ_n hat(1/y - n) g_n(u(z))`: on `1/(n+1) ≤ y ≤ 1/n` it interpolates linearly (in
`1/y`) between `g_n(u(z))` and `g_{n+1}(u(z))`. -/
noncomputable def hZero (s : ℕ → ℝ) (G : ℕ → ℝ → V) (z : ℂ) : V :=
  ∑' n : ℕ, hat (z.im⁻¹ - n) • G n (lineU s z)

theorem continuousOn_hZero (s : ℕ → ℝ) {G : ℕ → ℝ → V} (hG : ∀ n, Continuous (G n)) :
    ContinuousOn (hZero s G) upper := by
  refine continuousOn_tsum_upper (fun n => ?_) fun n z hz hn => ?_
  · refine ContinuousOn.smul (continuous_hat.comp_continuousOn ?_)
      ((hG n).comp (continuous_lineU s)).continuousOn
    exact (ContinuousOn.inv₀ (by fun_prop) fun z hz => ne_of_gt hz).sub continuousOn_const
  · rw [hat_eq_zero, zero_smul]
    rw [abs_of_neg (by linarith)]
    linarith

theorem tendsto_hZero_seg (s : ℕ → ℝ) {G : ℕ → ℝ → V} {p c : ℝ} {L : V}
    (hu : ∀ y, 0 < y → lineU s (seg p c y) = p) (hG : Tendsto (fun n => G n p) atTop (𝓝 L)) :
    Tendsto (fun y => hZero s G (seg p c y)) (𝓝[>] 0) (𝓝 L) := by
  refine ((tendsto_tsum_hat hG).comp tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Function.comp, hZero, seg_im, hu y hy]

end HZero

/-! ### The corrections `Λ_n` -/

/-- The tent over the gap `(c(s n), c(s n) + w(n))`, with peak `1` at its midpoint. -/
noncomputable def tent (s : ℕ → ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  max 0 (1 - |2 * τ - 2 * jump s (s n) - wt n| / wt n)

theorem continuous_tent (s : ℕ → ℝ) (n : ℕ) : Continuous (tent s n) := by
  unfold tent; fun_prop

theorem tent_eq_zero_of_le {s : ℕ → ℝ} {n : ℕ} {τ : ℝ} (h : τ ≤ jump s (s n)) :
    tent s n τ = 0 := by
  have hw := wt_pos n
  refine max_eq_left ?_
  rw [sub_nonpos, le_div_iff₀ hw, one_mul, abs_of_nonpos (by linarith)]
  linarith

theorem tent_eq_zero_of_ge {s : ℕ → ℝ} {n : ℕ} {τ : ℝ} (h : jump s (s n) + wt n ≤ τ) :
    tent s n τ = 0 := by
  have hw := wt_pos n
  refine max_eq_left ?_
  rw [sub_nonpos, le_div_iff₀ hw, one_mul, abs_of_nonneg (by linarith)]
  linarith

theorem tent_mid (s : ℕ → ℝ) (n : ℕ) : tent s n (jump s (s n) + wt n / 2) = 1 := by
  unfold tent
  have : 2 * (jump s (s n) + wt n / 2) - 2 * jump s (s n) - wt n = 0 := by ring
  rw [this]
  simp

section Corr

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The correction `Λ_n(z) = max(0, 1 - n y) · tent_n((x - s_n)/y) · z_n`. -/
noncomputable def corr (s : ℕ → ℝ) (zz : ℕ → V) (n : ℕ) (z : ℂ) : V :=
  (max 0 (1 - n * z.im) * tent s n ((z.re - s n) / z.im)) • zz n

theorem continuousOn_corr (s : ℕ → ℝ) (zz : ℕ → V) (n : ℕ) :
    ContinuousOn (corr s zz n) upper := by
  refine ContinuousOn.smul (ContinuousOn.mul (by fun_prop)
    ((continuous_tent s n).comp_continuousOn ?_)) continuousOn_const
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ne_of_gt hz

theorem corr_eq_zero_of_large (s : ℕ → ℝ) (zz : ℕ → V) {n : ℕ} {z : ℂ} (hz : 0 < z.im)
    (hn : z.im⁻¹ + 1 ≤ n) : corr s zz n z = 0 := by
  have : 1 ≤ n * z.im := by
    have := mul_le_mul_of_nonneg_right hn hz.le
    rw [add_mul, inv_mul_cancel₀ hz.ne'] at this
    linarith
  unfold corr
  rw [max_eq_left (by linarith), zero_mul, zero_smul]

/-- On the segment at `p` of slope `c(p)` every correction vanishes. -/
theorem corr_seg (s : ℕ → ℝ) (zz : ℕ → V) (n : ℕ) {p y : ℝ} (hy : 0 < y) :
    corr s zz n (seg p (jump s p) y) = 0 := by
  unfold corr
  rw [seg_re, seg_im]
  suffices tent s n ((p + jump s p * y - s n) / y) = 0 by rw [this, mul_zero, zero_smul]
  have hτ : (p + jump s p * y - s n) / y = (p - s n) / y + jump s p := by
    field_simp; ring
  rw [hτ]
  rcases lt_or_ge (s n) p with h | h
  · apply tent_eq_zero_of_ge
    have := jump_add_le s h
    have : 0 < (p - s n) / y := div_pos (by linarith) hy
    linarith
  · apply tent_eq_zero_of_le
    have := jump_mono s h
    have : (p - s n) / y ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hy.le
    linarith

/-- On the segment at `s m` of slope `c(s m) + w(m)/2`, `Λ_n` vanishes if `s n ≠ s m`. -/
theorem corr_seg_mid_ne (s : ℕ → ℝ) (zz : ℕ → V) {n m : ℕ} {y : ℝ} (hy : 0 < y)
    (hne : s n ≠ s m) : corr s zz n (seg (s m) (jump s (s m) + wt m / 2) y) = 0 := by
  unfold corr
  rw [seg_re, seg_im]
  suffices tent s n ((s m + (jump s (s m) + wt m / 2) * y - s n) / y) = 0 by
    rw [this, mul_zero, zero_smul]
  have hτ : (s m + (jump s (s m) + wt m / 2) * y - s n) / y =
      (s m - s n) / y + jump s (s m) + wt m / 2 := by
    field_simp; ring
  rw [hτ]
  have hw := wt_pos m
  rcases lt_or_gt_of_ne hne with h | h
  · apply tent_eq_zero_of_ge
    have := jump_add_le s h
    have : 0 < (s m - s n) / y := div_pos (by linarith) hy
    linarith
  · apply tent_eq_zero_of_le
    have := jump_add_le s h
    have : (s m - s n) / y < 0 := div_neg_of_neg_of_pos (by linarith) hy
    linarith

theorem corr_seg_mid_self (s : ℕ → ℝ) (zz : ℕ → V) (m : ℕ) {y : ℝ} (hy : 0 < y) :
    corr s zz m (seg (s m) (jump s (s m) + wt m / 2) y) = max 0 (1 - m * y) • zz m := by
  unfold corr
  rw [seg_re, seg_im]
  have hτ : (s m + (jump s (s m) + wt m / 2) * y - s m) / y = jump s (s m) + wt m / 2 := by
    field_simp; ring
  rw [hτ, tent_mid, mul_one]

end Corr

/-! ### The theorem -/

theorem five_sixteenths_lt_sqrt_two_sub_one : (5 / 16 : ℝ) < √2 - 1 := by
  have : (21 / 16 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

/-- `thm:construct-B` (core): a continuous `h` on `ℍ` tending to `φ(p)` along a segment of slope
`c ∈ [0, √2 - 1)` at every `p ∈ E`. -/
theorem exists_h_aux {m : ℕ} {E : _root_.Set ℝ} (hE : E ⊆ Ioo (-1) 1)
    {φ : ℝ → (Fin m → ℝ)} (hφ : IsHonoraryBaireTwo (E.restrict φ)) :
    ∃ h : ℂ → (Fin m → ℝ), ContinuousOn h upper ∧ ∀ p ∈ E, ∃ c : ℝ, 0 ≤ c ∧ c < √2 - 1 ∧
      Tendsto (fun y => h (seg p c y)) (𝓝[>] 0) (𝓝 (φ p)) := by
  classical
  obtain ⟨N, hN, g, hg, hφg⟩ := hφ
  obtain ⟨G, hGc, hGt⟩ := ((baireOne_tfae g).out 0 2).1 hg
  set S : _root_.Set ℝ := Subtype.val '' N with hS
  obtain ⟨e, he⟩ := _root_.Set.countable_iff_exists_injOn.1 (hN.image Subtype.val)
  let s : ℕ → ℝ := fun n => if h : ∃ x ∈ S, e x = n then h.choose else 1
  have hs1 : ∀ x ∈ S, s (e x) = x := by
    intro x hx
    have h : ∃ y ∈ S, e y = e x := ⟨x, hx, rfl⟩
    simp only [s, dif_pos h]
    exact he h.choose_spec.1 hx h.choose_spec.2
  have hs2 : ∀ n, s n ∈ E → e (s n) = n := by
    intro n hn
    by_cases h : ∃ x ∈ S, e x = n
    · simp only [s, dif_pos h]; exact h.choose_spec.2
    · simp only [s, dif_neg h] at hn; exact absurd (hE hn).2 (lt_irrefl 1)
  let zz : ℕ → (Fin m → ℝ) := fun n => if h : s n ∈ E then φ (s n) - g ⟨s n, h⟩ else 0
  have hjump := jump_nonneg s
  have hjump' := jump_le s
  have h516 := five_sixteenths_lt_sqrt_two_sub_one
  refine ⟨fun z => hZero s G z + ∑' n, corr s zz n z,
    (continuousOn_hZero s hGc).add (continuousOn_tsum_upper (continuousOn_corr s zz)
      fun n z hz hn => corr_eq_zero_of_large s zz hz hn), fun p hp => ?_⟩
  have hpI := hE hp
  by_cases hpN : (⟨p, hp⟩ : E) ∈ N
  · -- `p = s k` is an exceptional point: use the slope `c(p) + w(k)/2`
    obtain ⟨k, rfl⟩ : ∃ k, s k = p := ⟨e p, hs1 p ⟨⟨p, hp⟩, hpN, rfl⟩⟩
    have hw := wt_pos k
    have hw' := wt_le k
    refine ⟨jump s (s k) + wt k / 2, by linarith [hjump (s k)],
      by linarith [hjump' (s k)], ?_⟩
    have h1 : Tendsto (fun y => hZero s G (seg (s k) (jump s (s k) + wt k / 2) y)) (𝓝[>] 0)
        (𝓝 (g ⟨s k, hp⟩)) :=
      tendsto_hZero_seg s (fun y hy => lineU_seg s hpI hy (by linarith)
        fun q hq => by linarith [jump_add_le s hq]) (hGt ⟨s k, hp⟩)
    have h2 : Tendsto (fun y => ∑' n, corr s zz n (seg (s k) (jump s (s k) + wt k / 2) y))
        (𝓝[>] 0) (𝓝 (zz k)) := by
      have hc : Tendsto (fun y : ℝ => max 0 (1 - k * y) • zz k) (𝓝[>] 0) (𝓝 (zz k)) := by
        have hcont : Continuous fun y : ℝ => max 0 (1 - k * y) • zz k := by fun_prop
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      refine hc.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [tsum_eq_single k, corr_seg_mid_self s zz k hy]
      intro n hn
      by_cases hnE : s n ∈ E
      · refine corr_seg_mid_ne s zz hy fun heq => hn ?_
        rw [← hs2 n hnE, heq, hs2 k hp]
      · simp [corr, zz, hnE]
    have h3 : g ⟨s k, hp⟩ + zz k = φ (s k) := by
      simp only [zz, dif_pos hp]; abel
    rw [← h3]
    exact h1.add h2
  · -- `p` is not exceptional: use the slope `c(p)`
    refine ⟨jump s p, hjump p, by linarith [hjump' p], ?_⟩
    have h1 : Tendsto (fun y => hZero s G (seg p (jump s p) y)) (𝓝[>] 0) (𝓝 (g ⟨p, hp⟩)) :=
      tendsto_hZero_seg s (fun y hy => lineU_seg s hpI hy le_rfl
        fun q hq => jump_mono s hq.le) (hGt ⟨p, hp⟩)
    have h3 : g ⟨p, hp⟩ = φ p := (hφg ⟨p, hp⟩ hpN).symm
    rw [← h3]
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [corr_seg s zz _ hy]

/-! ### The Stolz angle `s(p, 1, 3π/8)` -/

theorem cot_three_pi_div_eight : cot (3 * π / 8) = √2 - 1 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : 1 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : 0 < √(2 + √2) := Real.sqrt_pos.2 (by linarith)
  have key : √(2 - √2) = (√2 - 1) * √(2 + √2) := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ √2 - 1), ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    linear_combination (-√2) * h2
  rw [cot_eq_cos_div_sin, show 3 * π / 8 = π / 2 - π / 8 by ring, cos_pi_div_two_sub,
    sin_pi_div_two_sub, sin_pi_div_eight, cos_pi_div_eight, key]
  field_simp

/-- A segment of slope `|c| < √2 - 1 = cot(3π/8)` at `p` lies in `s(p, 1, 3π/8)` below
height `1`. -/
theorem seg_mem_stolz {p c y : ℝ} (hc : |c| < √2 - 1) (hy : 0 < y) (hy1 : y < 1) :
    seg p c y ∈ stolz p 1 (3 * π / 8) := by
  refine ⟨by simpa using hy, by simpa using hy1, ?_⟩
  rw [seg_re, seg_im, cot_three_pi_div_eight, add_sub_cancel_left, abs_mul, abs_of_pos hy,
    mul_comm y]
  exact mul_lt_mul_of_pos_right hc hy

/-- `thm:construct-B`: for `E ⊆ (-1, 1)` and `φ : E → ℝ^m` of honorary Baire class `≤ 2` there is
`h`, continuous on `ℍ`, such that at each `p ∈ E`, `h → φ(p)` along the segment
`y ↦ (p + c y) + i y` for some `|c| < √2 - 1` (which lies in `s(p, 1, 3π/8)` for `0 < y < 1`,
see `seg_mem_stolz`). -/
theorem exists_h {m : ℕ} {E : _root_.Set ℝ} (hE : E ⊆ Ioo (-1) 1)
    {φ : ℝ → (Fin m → ℝ)} (hφ : IsHonoraryBaireTwo (E.restrict φ)) :
    ∃ h : ℂ → (Fin m → ℝ), ContinuousOn h upper ∧ ∀ p ∈ E, ∃ c : ℝ, |c| < √2 - 1 ∧
      Tendsto (fun y : ℝ => h (((p + c * y : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0)
        (𝓝 (φ p)) := by
  obtain ⟨h, hc, hlim⟩ := exists_h_aux hE hφ
  refine ⟨h, hc, fun p hp => ?_⟩
  obtain ⟨c, hc0, hc1, ht⟩ := hlim p hp
  exact ⟨c, by rwa [abs_of_nonneg hc0], ht⟩

/-- `thm:construct-B`, bounded case: if `‖φ‖ ≤ B` on `E`, then `h` can be taken with
`‖h‖ ≤ B`. -/
theorem exists_h_bounded {m : ℕ} {E : _root_.Set ℝ} (hE : E ⊆ Ioo (-1) 1)
    {φ : ℝ → (Fin m → ℝ)} (hφ : IsHonoraryBaireTwo (E.restrict φ)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ p ∈ E, ‖φ p‖ ≤ B) :
    ∃ h : ℂ → (Fin m → ℝ), ContinuousOn h upper ∧ (∀ z, ‖h z‖ ≤ B) ∧
      ∀ p ∈ E, ∃ c : ℝ, |c| < √2 - 1 ∧
        Tendsto (fun y : ℝ => h (((p + c * y : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0)
          (𝓝 (φ p)) := by
  obtain ⟨h, hc, hlim⟩ := exists_h hE hφ
  let cl : (Fin m → ℝ) → (Fin m → ℝ) := fun v i => max (-B) (min B (v i))
  have hcl : Continuous cl := by fun_prop
  have hfix : ∀ p ∈ E, cl (φ p) = φ p := fun p hp => by
    funext i
    have := (norm_le_pi_norm (φ p) i).trans (hB p hp)
    rw [Real.norm_eq_abs, abs_le] at this
    simp only [cl]
    rw [min_eq_right this.2, max_eq_right this.1]
  refine ⟨cl ∘ h, hcl.comp_continuousOn hc, fun z => (pi_norm_le_iff_of_nonneg hB0).2 fun i => ?_,
    fun p hp => ?_⟩
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · obtain ⟨c, hc, ht⟩ := hlim p hp
    refine ⟨c, hc, ?_⟩
    rw [← hfix p hp]
    exact (hcl.tendsto _).comp ht

end TJK.Construct
