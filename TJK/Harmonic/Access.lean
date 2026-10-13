import TJK.Harmonic.Example

/-!
# Accessibility of the boundary points, and the example (blueprint §H)

Source: Kaczynski, Trans. AMS 137 (1969). We formalize

* `lem:ha-access` (`Intervals.accessible`): every point of `C \ ⋃ I_n*` is accessible by a simple
  arc in `𝔻 \ ⋃ Ω̄_n`, for the concrete domains `Ω_n` of `lem:ha-estimates`. The arc is explicit,
  `s ↦ (1 - s) e^{iθ(s)}`, so this does not use the Jordan curve theorem;
* `thm:ha-example` (`exists_bounded_harmonic_boundaryFn_not_baireOne'`).
-/

namespace TJK.Harmonic

open _root_.Set Filter Topology Metric Function MeasureTheory Complex
open scoped Real

/-! ### Fourth roots -/

/-- `qr s = s^{1/4}` (for `s ≥ 0`). -/
noncomputable def qr (s : ℝ) : ℝ := √(√s)

theorem qr_nonneg (s : ℝ) : 0 ≤ qr s := Real.sqrt_nonneg _

theorem qr_pos {s : ℝ} (hs : 0 < s) : 0 < qr s := Real.sqrt_pos.2 (Real.sqrt_pos.2 hs)

theorem qr_pow_four {s : ℝ} (hs : 0 ≤ s) : qr s ^ 4 = s := by
  unfold qr
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hs]

theorem qr_mono {s t : ℝ} (h : s ≤ t) : qr s ≤ qr t :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

theorem vq_one_sub (s : ℝ) : vq (1 - s) = qr s := by simp [vq, qr]

@[fun_prop] theorem continuous_qr : Continuous qr := by unfold qr; fun_prop

theorem qr_zero : qr 0 = 0 := by simp [qr]

theorem qr_pow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : qr (a ^ n) = qr a ^ n := by
  rw [← pow_left_inj₀ (qr_nonneg _) (pow_nonneg (qr_nonneg a) n) (by norm_num : (4 : ℕ) ≠ 0),
    qr_pow_four (pow_nonneg ha n), ← pow_mul, mul_comm, pow_mul, qr_pow_four ha]

theorem qr_half_lt_one : qr (1 / 2) < 1 := by
  rw [← pow_lt_pow_iff_left₀ (qr_nonneg _) zero_le_one (by norm_num : (4 : ℕ) ≠ 0),
    qr_pow_four (by norm_num)]
  norm_num

namespace Intervals

variable (d : Intervals)

theorem qr_ε_lt_one (n : ℕ) : qr (d.ε n) < 1 := by
  have := d.ε_le_quarter n
  rw [← pow_lt_pow_iff_left₀ (qr_nonneg _) zero_le_one (by norm_num : (4 : ℕ) ≠ 0),
    qr_pow_four (d.ε_pos n).le]
  linarith

/-- Polar description of `Ω̄_k`: a point `r e^{iφ}`, `r > 0`, of `Ω̄_k` has `1 - ε_k ≤ r` and
`e^{iφ} = e^{iψ}` with `ψ ∈ [α_k - v, β_k + v]`, `v = (1 - r)^{1/4}`, within `v` of `[α_k, β_k]`. -/
theorem mem_closure_polar (k : ℕ) {r φ : ℝ} (hr : 0 < r)
    (h : (r : ℂ) * expI φ ∈ closure (d.Ω k)) :
    1 - d.ε k ≤ r ∧ ∃ ψ, expI φ = expI ψ ∧ ψ ∈ Icc (d.α k - vq r) (d.β k + vq r) ∧
      ∃ b ∈ Icc (d.α k) (d.β k), |ψ - b| ≤ vq r := by
  rw [d.closure_Ω] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hx2 : 0 < x.2 := by linarith [hx.2.1, d.one_sub_ε_pos k]
  have hr' : x.2 = r := by
    have := congrArg norm hxe
    rwa [d.norm_H k hx2.le, norm_mul, norm_expI, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr.le] at this
  subst hr'
  refine ⟨hx.2.1, d.θ k x.1 x.2, ?_, d.θ_mem k hx.1, d.exists_near k hx.1⟩
  unfold H at hxe
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hx2.ne') hxe).symm

/-! ### Blockers -/

/-- `d⁺_n ∈ [0, 2π)`, with `e^{iθ₀} = e^{i(β_n + d⁺_n)}`. -/
noncomputable def dp (θ₀ : ℝ) (n : ℕ) : ℝ := toIcoMod Real.two_pi_pos 0 (θ₀ - d.β n)

/-- `d⁻_n ∈ [0, 2π)`, with `e^{iθ₀} = e^{i(α_n - d⁻_n)}`. -/
noncomputable def dm (θ₀ : ℝ) (n : ℕ) : ℝ := toIcoMod Real.two_pi_pos 0 (d.α n - θ₀)

theorem dp_mem (θ₀ : ℝ) (n : ℕ) : d.dp θ₀ n ∈ Ico 0 (2 * π) := by
  have := toIcoMod_mem_Ico Real.two_pi_pos 0 (θ₀ - d.β n); rwa [zero_add] at this

theorem dm_mem (θ₀ : ℝ) (n : ℕ) : d.dm θ₀ n ∈ Ico 0 (2 * π) := by
  have := toIcoMod_mem_Ico Real.two_pi_pos 0 (d.α n - θ₀); rwa [zero_add] at this

theorem expI_dp (θ₀ : ℝ) (n : ℕ) (x : ℝ) : expI (θ₀ + x) = expI (d.β n + d.dp θ₀ n + x) := by
  have := self_sub_toIcoMod Real.two_pi_pos 0 (θ₀ - d.β n)
  rw [zsmul_eq_mul] at this
  rw [show θ₀ + x = d.β n + d.dp θ₀ n + x +
    (toIcoDiv Real.two_pi_pos 0 (θ₀ - d.β n) : ℝ) * (2 * π) by unfold dp; linarith,
    expI_add_int_mul]

theorem expI_dm (θ₀ : ℝ) (n : ℕ) (x : ℝ) : expI (θ₀ + x) = expI (d.α n - d.dm θ₀ n + x) := by
  have := self_sub_toIcoMod Real.two_pi_pos 0 (d.α n - θ₀)
  rw [zsmul_eq_mul] at this
  rw [show θ₀ + x = d.α n - d.dm θ₀ n + x +
    ((-toIcoDiv Real.two_pi_pos 0 (d.α n - θ₀) : ℤ) : ℝ) * (2 * π) by
      push_cast; unfold dm; linarith, expI_add_int_mul]

theorem expI_eq_dp (θ₀ : ℝ) (n : ℕ) : expI (d.β n + d.dp θ₀ n) = expI θ₀ := by
  simpa using (d.expI_dp θ₀ n 0).symm

theorem expI_eq_dm (θ₀ : ℝ) (n : ℕ) : expI (d.α n - d.dm θ₀ n) = expI θ₀ := by
  simpa using (d.expI_dm θ₀ n 0).symm

/-- `n` cannot be both a `+`blocker and a `-`blocker. -/
theorem not_both (θ₀ : ℝ) (n : ℕ) (h1 : d.dp θ₀ n ≤ qr (d.ε n)) (h2 : d.dm θ₀ n ≤ qr (d.ε n)) :
    False := by
  have e2 : expI (d.α n - d.dm θ₀ n + ((1 : ℤ) : ℝ) * (2 * π)) = expI θ₀ := by
    rw [expI_add_int_mul, d.expI_eq_dm]
  have hp := d.dp_mem θ₀ n; have hm := d.dm_mem θ₀ n
  have hq := d.qr_ε_lt_one n; have hb := d.β_sub_α_le n; have hab := d.α_lt_β n
  have := eq_of_expI_eq (e2.trans (d.expI_eq_dp θ₀ n).symm) (by
    rw [abs_lt]; push_cast; constructor <;> linarith [Real.pi_gt_three, hp.1, hm.1, hp.2, hm.2])
  push_cast at this
  linarith [Real.pi_gt_three, hp.1, hm.1]

/-- The sign of a blocker: `1` for a `+`blocker, `-1` for a `-`blocker, `0` otherwise. -/
noncomputable def sg (θ₀ : ℝ) (n : ℕ) : ℝ :=
  if d.dp θ₀ n ≤ qr (d.ε n) then 1 else if d.dm θ₀ n ≤ qr (d.ε n) then -1 else 0

/-- `d_n`: `d⁺_n` for a `+`blocker, `d⁻_n` otherwise. -/
noncomputable def dd (θ₀ : ℝ) (n : ℕ) : ℝ :=
  if d.dp θ₀ n ≤ qr (d.ε n) then d.dp θ₀ n else d.dm θ₀ n

theorem dd_nonneg (θ₀ : ℝ) (n : ℕ) : 0 ≤ d.dd θ₀ n := by
  unfold dd; split_ifs
  · exact (d.dp_mem θ₀ n).1
  · exact (d.dm_mem θ₀ n).1

theorem sg_cases (θ₀ : ℝ) (n : ℕ) (h : d.sg θ₀ n ≠ 0) :
    (d.sg θ₀ n = 1 ∧ d.dd θ₀ n = d.dp θ₀ n ∧ d.dp θ₀ n ≤ qr (d.ε n)) ∨
      (d.sg θ₀ n = -1 ∧ d.dd θ₀ n = d.dm θ₀ n ∧ d.dm θ₀ n ≤ qr (d.ε n)) := by
  unfold sg dd at *
  split_ifs at h ⊢ with h1 h2
  · exact Or.inl ⟨rfl, rfl, h1⟩
  · exact Or.inr ⟨rfl, rfl, h2⟩
  · exact absurd rfl h

theorem abs_sg_le (θ₀ : ℝ) (n : ℕ) : |d.sg θ₀ n| ≤ 1 := by
  unfold sg; split_ifs <;> norm_num

/-- A blocker has an endpoint of `I_n` within `d_n ≤ ε_n^{1/4}` of `e^{iθ₀}`. -/
theorem endpoint (θ₀ : ℝ) (n : ℕ) (h : d.sg θ₀ n ≠ 0) :
    ∃ p ∈ Icc (d.α n) (d.β n), ‖expI p - expI θ₀‖ ≤ d.dd θ₀ n ∧ d.dd θ₀ n ≤ qr (d.ε n) := by
  have hab := d.α_lt_β n
  rcases d.sg_cases θ₀ n h with ⟨-, hD, hle⟩ | ⟨-, hD, hle⟩
  · refine ⟨d.β n, ⟨hab.le, le_rfl⟩, ?_, hD ▸ hle⟩
    rw [hD, ← d.expI_eq_dp θ₀ n]
    refine (norm_expI_sub_le _ _).trans ?_
    rw [abs_le]; constructor <;> linarith [(d.dp_mem θ₀ n).1]
  · refine ⟨d.α n, ⟨le_rfl, hab.le⟩, ?_, hD ▸ hle⟩
    rw [hD, ← d.expI_eq_dm θ₀ n]
    refine (norm_expI_sub_le _ _).trans ?_
    rw [abs_le]; constructor <;> linarith [(d.dm_mem θ₀ n).1]

/-! ### The angle function -/

/-- `ρ_n(s) = max(0, min(1, 2 - s/ε_n))`. -/
noncomputable def ρ (n : ℕ) (s : ℝ) : ℝ := max 0 (min 1 (2 - s / d.ε n))

theorem ρ_nonneg (n : ℕ) (s : ℝ) : 0 ≤ d.ρ n s := le_max_left _ _

theorem ρ_le_one (n : ℕ) (s : ℝ) : d.ρ n s ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem ρ_eq_one (n : ℕ) {s : ℝ} (hs : s ≤ d.ε n) : d.ρ n s = 1 := by
  have h1 : 1 ≤ 2 - s / d.ε n := by
    have : s / d.ε n ≤ 1 := (div_le_one (d.ε_pos n)).2 hs
    linarith
  unfold ρ; rw [min_eq_left h1, max_eq_right zero_le_one]

theorem lt_of_ρ_pos (n : ℕ) {s : ℝ} (h : 0 < d.ρ n s) : s < 2 * d.ε n := by
  by_contra h'
  push Not at h'
  have h2 : 2 - s / d.ε n ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ (d.ε_pos n)]; linarith
  have : d.ρ n s = 0 := by unfold ρ; exact max_eq_left ((min_le_right _ _).trans h2)
  linarith

@[fun_prop] theorem continuous_ρ (n : ℕ) : Continuous (d.ρ n) := by unfold ρ; fun_prop

/-- The angular displacement `δ_n(s) = ± max(0, 2 ρ_n(s) s^{1/4} - d_n)` for a `±`blocker. -/
noncomputable def δ (θ₀ : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  d.sg θ₀ n * max 0 (2 * d.ρ n s * qr s - d.dd θ₀ n)

/-- `n` is active at depth `s`: a blocker with `δ_n(s) ≠ 0`. -/
def Active (θ₀ : ℝ) (n : ℕ) (s : ℝ) : Prop :=
  d.sg θ₀ n ≠ 0 ∧ d.dd θ₀ n < 2 * d.ρ n s * qr s

@[fun_prop] theorem continuous_δ (θ₀ : ℝ) (n : ℕ) : Continuous (d.δ θ₀ n) := by
  unfold δ; fun_prop

theorem active_of_δ_ne {θ₀ s : ℝ} {n : ℕ} (h : d.δ θ₀ n s ≠ 0) : d.Active θ₀ n s := by
  unfold δ at h
  refine ⟨left_ne_zero_of_mul h, ?_⟩
  have := right_ne_zero_of_mul h
  by_contra h'
  push Not at h'
  exact this (max_eq_left (by linarith))

theorem Active.lt {θ₀ s : ℝ} {n : ℕ} (h : d.Active θ₀ n s) : d.dd θ₀ n < 2 * qr s := by
  have := d.ρ_le_one n s; have := qr_nonneg s
  nlinarith [h.2]

theorem Active.ρ_pos {θ₀ s : ℝ} {n : ℕ} (h : d.Active θ₀ n s) : 0 < d.ρ n s := by
  have := d.dd_nonneg θ₀ n; have := qr_nonneg s; have := d.ρ_nonneg n s
  by_contra h'
  push Not at h'
  nlinarith [h.2]

theorem Active.pos {θ₀ s : ℝ} {n : ℕ} (h : d.Active θ₀ n s) : 0 < s := by
  have := d.dd_nonneg θ₀ n; have := d.ρ_le_one n s; have := d.ρ_nonneg n s
  have hq : 0 < qr s := by nlinarith [h.2, qr_nonneg s]
  by_contra h'
  push Not at h'
  rw [qr, Real.sqrt_eq_zero'.2 h', Real.sqrt_zero] at hq
  exact lt_irrefl _ hq

theorem Active.lt_two_ε {θ₀ s : ℝ} {n : ℕ} (h : d.Active θ₀ n s) : s < 2 * d.ε n :=
  d.lt_of_ρ_pos n (Active.ρ_pos d h)

theorem δ_zero (θ₀ : ℝ) (n : ℕ) : d.δ θ₀ n 0 = 0 := by
  unfold δ
  rw [qr_zero, mul_zero, zero_sub, max_eq_left (by linarith [d.dd_nonneg θ₀ n]), mul_zero]

theorem abs_δ_le (θ₀ : ℝ) (n : ℕ) (s : ℝ) : |d.δ θ₀ n s| ≤ 2 * qr (2 * d.ε n) := by
  by_cases h : d.δ θ₀ n s = 0
  · rw [h, abs_zero]; exact mul_nonneg zero_le_two (qr_nonneg _)
  have ha := d.active_of_δ_ne h
  have hs := qr_mono (Active.lt_two_ε d ha).le
  have hpos : 0 < 2 * d.ρ n s * qr s - d.dd θ₀ n := by linarith [ha.2]
  unfold δ
  rw [abs_mul, max_eq_right hpos.le, abs_of_pos hpos]
  have := d.dd_nonneg θ₀ n; have := d.ρ_le_one n s; have := qr_nonneg s
  calc |d.sg θ₀ n| * (2 * d.ρ n s * qr s - d.dd θ₀ n) ≤ 1 * (2 * d.ρ n s * qr s - d.dd θ₀ n) :=
        mul_le_mul_of_nonneg_right (d.abs_sg_le θ₀ n) hpos.le
    _ ≤ 2 * qr (2 * d.ε n) := by nlinarith

theorem summable_bound : Summable fun n : ℕ => 2 * qr (1 / 2) * qr (1 / 2) ^ n :=
  (summable_geometric_of_lt_one (qr_nonneg _) qr_half_lt_one).mul_left _

theorem qr_two_ε_le (n : ℕ) : 2 * qr (2 * d.ε n) ≤ 2 * qr (1 / 2) * qr (1 / 2) ^ n := by
  have h : 2 * d.ε n ≤ (1 / 2) ^ (n + 1) := by
    have := d.ε_le n
    rw [pow_succ] at this ⊢
    rw [pow_succ] at this
    linarith
  have := qr_mono h
  rw [qr_pow (by norm_num), pow_succ] at this
  nlinarith [qr_nonneg (1 / 2), pow_nonneg (qr_nonneg (1 / 2)) n]

/-- The angle `θ(s) = θ₀ + ∑ δ_n(s)`. -/
noncomputable def angle (θ₀ s : ℝ) : ℝ := θ₀ + ∑' n, d.δ θ₀ n s

theorem continuous_angle (θ₀ : ℝ) : Continuous (d.angle θ₀) := by
  unfold angle
  refine continuous_const.add (continuous_tsum (fun n => d.continuous_δ θ₀ n) summable_bound
    fun n s => ?_)
  rw [Real.norm_eq_abs]
  exact (d.abs_δ_le θ₀ n s).trans (d.qr_two_ε_le n)

theorem angle_zero (θ₀ : ℝ) : d.angle θ₀ 0 = θ₀ := by
  simp [angle, δ_zero]

/-! ### The arc avoids the closed domains -/

/-- (b) At each depth `s` at most one blocker is active (by IV). -/
theorem active_unique {θ₀ s : ℝ} {h k : ℕ} (hh : d.Active θ₀ h s) (hk : d.Active θ₀ k s) :
    h = k := by
  wlog hlt : h < k generalizing h k
  · rcases lt_or_eq_of_le (not_lt.1 hlt) with h' | h'
    · exact (this hk hh h').symm
    · exact h'.symm
  exfalso
  obtain ⟨p, hp, hpd, -⟩ := d.endpoint θ₀ h hh.1
  obtain ⟨q, hq, hqd, hqe⟩ := d.endpoint θ₀ k hk.1
  have hsep : 4 * qr (d.ε k) ≤ ‖expI p - expI q‖ := d.sep h k hlt p hp q hq
  have htri : ‖expI p - expI q‖ ≤ ‖expI p - expI θ₀‖ + ‖expI q - expI θ₀‖ := by
    calc ‖expI p - expI q‖ = ‖(expI p - expI θ₀) - (expI q - expI θ₀)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have h1 := Active.lt d hh
  have h2 := Active.lt_two_ε d hk
  have hs0 := Active.pos d hk
  have h3 : 3 * qr (d.ε k) < 2 * qr s := by linarith
  have h4 := pow_lt_pow_left₀ h3 (mul_nonneg (by norm_num) (qr_nonneg _)) (by norm_num : 4 ≠ 0)
  rw [mul_pow, mul_pow, qr_pow_four (d.ε_pos k).le, qr_pow_four hs0.le] at h4
  linarith [d.ε_pos k]

/-- (a) If `(1 - s) ζ ∈ Ω̄_k`, `0 < s < 1`, then `k` is active at `s`. -/
theorem active_of_mem (θ₀ : ℝ) (hθ : ∀ n, expI θ₀ ∉ expI '' Ioo (d.α n) (d.β n)) {k : ℕ}
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (h : ((1 - s : ℝ) : ℂ) * expI θ₀ ∈ closure (d.Ω k)) : d.Active θ₀ k s := by
  obtain ⟨hsε, ψ, hψ, hψm, -⟩ := d.mem_closure_polar k (by linarith) h
  rw [vq_one_sub] at hψm
  have hsε' : s ≤ d.ε k := by linarith
  have hq := qr_mono hsε'
  have hq0 := qr_pos hs0
  have hρ := d.ρ_eq_one k hsε'
  have hlt1 := d.qr_ε_lt_one k
  have hp := d.dp_mem θ₀ k; have hm := d.dm_mem θ₀ k
  have hnot : ψ ∉ Ioo (d.α k) (d.β k) := fun hm => hθ k ⟨ψ, hm, hψ.symm⟩
  rcases le_or_gt (d.β k) ψ with hb | hb
  · have hdp : d.dp θ₀ k = ψ - d.β k := by
      have e1 : expI (d.β k + d.dp θ₀ k) = expI ψ := by rw [← hψ]; exact d.expI_eq_dp θ₀ k
      have := eq_of_expI_eq e1 (by
        rw [abs_lt]; constructor <;> linarith [hp.1, hp.2, hψm.2, Real.pi_gt_three])
      linarith
    have hle : d.dp θ₀ k ≤ qr (d.ε k) := by linarith [hψm.2]
    refine ⟨by simp [sg, hle], ?_⟩
    simp only [dd, if_pos hle, hρ]
    linarith [hψm.2]
  · have ha : ψ ≤ d.α k := by
      by_contra h'
      push Not at h'
      exact hnot ⟨h', hb⟩
    have hdm : d.dm θ₀ k = d.α k - ψ := by
      have e1 : expI (d.α k - d.dm θ₀ k) = expI ψ := by rw [← hψ]; exact d.expI_eq_dm θ₀ k
      have := eq_of_expI_eq e1 (by
        rw [abs_lt]; constructor <;> linarith [hm.1, hm.2, hψm.1, Real.pi_gt_three])
      linarith
    have hle : d.dm θ₀ k ≤ qr (d.ε k) := by linarith [hψm.1]
    have hnp : ¬ d.dp θ₀ k ≤ qr (d.ε k) := fun h' => d.not_both θ₀ k h' hle
    refine ⟨by simp [sg, hnp, hle], ?_⟩
    simp only [dd, if_neg hnp, hρ]
    linarith [hψm.1]

/-- The arc at depth `s`, displaced by `t` from an endpoint of `I_n` away from `I_n`, avoids every
`Ω̄_k`. -/
theorem not_mem_of_offset (n : ℕ) {s t φ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hs2 : s < 2 * d.ε n) (ht0 : 0 ≤ t) (ht : t ≤ 2 * qr s) (ht' : s ≤ d.ε n → t = 2 * qr s)
    (hφ : φ = d.β n + t ∨ φ = d.α n - t) (k : ℕ) :
    ((1 - s : ℝ) : ℂ) * expI φ ∉ closure (d.Ω k) := by
  intro h
  obtain ⟨hsε, ψ, hψ, hψm, b, hb, hψb⟩ := d.mem_closure_polar k (by linarith) h
  rw [vq_one_sub] at hψm hψb
  have hsε' : s ≤ d.ε k := by linarith
  have hq0 := qr_pos hs0
  have hq := qr_mono hsε'
  have hab := d.α_lt_β n
  rcases eq_or_ne k n with rfl | hkn
  · have ht2 := ht' hsε'
    have hlt1 := d.qr_ε_lt_one k
    have hba := d.β_sub_α_le k
    rcases hφ with rfl | rfl
    · have := eq_of_expI_eq hψ (by
        rw [abs_lt]; constructor <;> linarith [hψm.1, hψm.2, Real.pi_gt_three])
      linarith [hψm.2]
    · have := eq_of_expI_eq hψ (by
        rw [abs_lt]; constructor <;> linarith [hψm.1, hψm.2, Real.pi_gt_three])
      linarith [hψm.1]
  -- the chordal estimate `|e^{ip} - e^{ib}| ≤ 3 s^{1/4}`, `p` the endpoint of `I_n`
  obtain ⟨p, hp, hpφ⟩ : ∃ p ∈ Icc (d.α n) (d.β n), ‖expI φ - expI p‖ ≤ t := by
    rcases hφ with rfl | rfl
    · refine ⟨d.β n, ⟨hab.le, le_rfl⟩, (norm_expI_sub_le _ _).trans ?_⟩
      rw [add_sub_cancel_left, abs_of_nonneg ht0]
    · refine ⟨d.α n, ⟨le_rfl, hab.le⟩, (norm_expI_sub_le _ _).trans ?_⟩
      rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg ht0]
  have hψb' : ‖expI ψ - expI b‖ ≤ qr s := (norm_expI_sub_le _ _).trans hψb
  have hpb : ‖expI p - expI b‖ ≤ 3 * qr s := by
    calc ‖expI p - expI b‖ = ‖(expI ψ - expI b) - (expI φ - expI p)‖ := by rw [hψ]; ring_nf
      _ ≤ ‖expI ψ - expI b‖ + ‖expI φ - expI p‖ := norm_sub_le _ _
      _ ≤ 3 * qr s := by linarith
  rcases lt_or_gt_of_ne hkn with hkn | hkn
  · have hsep := d.sep k n hkn b hb p hp
    simp only at hsep
    rw [norm_sub_rev] at hsep
    have h3 : 4 * qr (d.ε n) ≤ 3 * qr s := hsep.trans hpb
    have h4 := pow_le_pow_left₀ (mul_nonneg (by norm_num) (qr_nonneg _)) h3 4
    rw [mul_pow, mul_pow, qr_pow_four (d.ε_pos n).le, qr_pow_four hs0.le] at h4
    linarith [d.ε_pos n]
  · have hsep : 4 * qr (d.ε k) ≤ ‖expI p - expI b‖ := d.sep n k hkn p hp b hb
    linarith [qr_pos (d.ε_pos k)]

/-- `Z(s) = (1 - s) e^{iθ(s)}` avoids every `Ω̄_k` for `0 < s < 1`. -/
theorem arc_not_mem (θ₀ : ℝ) (hθ : ∀ n, expI θ₀ ∉ expI '' Ioo (d.α n) (d.β n)) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (k : ℕ) :
    ((1 - s : ℝ) : ℂ) * expI (d.angle θ₀ s) ∉ closure (d.Ω k) := by
  by_cases hA : ∃ n, d.Active θ₀ n s
  · obtain ⟨n, hn⟩ := hA
    have hsum : ∑' m, d.δ θ₀ m s = d.δ θ₀ n s := tsum_eq_single n fun m hm => by
      by_contra h
      exact hm (d.active_unique (d.active_of_δ_ne h) hn)
    have hpos : 0 < 2 * d.ρ n s * qr s - d.dd θ₀ n := by linarith [hn.2]
    have hδ : d.δ θ₀ n s = d.sg θ₀ n * (2 * d.ρ n s * qr s - d.dd θ₀ n) := by
      unfold δ; rw [max_eq_right hpos.le]
    have ht0 : 0 ≤ 2 * d.ρ n s * qr s := by linarith [d.dd_nonneg θ₀ n]
    have ht : 2 * d.ρ n s * qr s ≤ 2 * qr s := by
      nlinarith [d.ρ_le_one n s, qr_nonneg s]
    have ht' : s ≤ d.ε n → 2 * d.ρ n s * qr s = 2 * qr s := fun h => by
      rw [d.ρ_eq_one n h, mul_one]
    rcases d.sg_cases θ₀ n hn.1 with ⟨h1, hD, -⟩ | ⟨h1, hD, -⟩
    · have : expI (d.angle θ₀ s) = expI (d.β n + 2 * d.ρ n s * qr s) := by
        rw [angle, hsum, hδ, h1, hD, d.expI_dp θ₀ n]; congr 1; ring
      rw [this]
      exact d.not_mem_of_offset n hs0 hs1 (Active.lt_two_ε d hn) ht0 ht ht' (Or.inl rfl) k
    · have : expI (d.angle θ₀ s) = expI (d.α n - 2 * d.ρ n s * qr s) := by
        rw [angle, hsum, hδ, h1, hD, d.expI_dm θ₀ n]; congr 1; ring
      rw [this]
      exact d.not_mem_of_offset n hs0 hs1 (Active.lt_two_ε d hn) ht0 ht ht' (Or.inr rfl) k
  · push Not at hA
    have hsum : ∑' m, d.δ θ₀ m s = 0 := by
      rw [show (fun m => d.δ θ₀ m s) = fun _ => 0 from
        funext fun m => by_contra fun h => hA m (d.active_of_δ_ne h)]
      exact tsum_zero
    rw [angle, hsum, add_zero]
    exact fun h => hA k (d.active_of_mem θ₀ hθ hs0 hs1 h)

/-- `lem:ha-access`: every point of `C \ ⋃ I_n*` is accessible by a simple arc in
`𝔻 \ ⋃ Ω̄_n`. The arc is `s ↦ (1 - s) e^{iθ(s)}`, `0 ≤ s ≤ 1/2`. -/
theorem accessible {ζ : ℂ} (hζ : ζ ∈ circle) (hζI : ∀ n, ζ ∉ expI '' Ioo (d.α n) (d.β n)) :
    ∃ γ, IsArcAt (disc \ ⋃ n, closure (d.Ω n)) ζ γ := by
  obtain ⟨θ₀, rfl⟩ : ∃ θ₀, expI θ₀ = ζ := ⟨arg ζ, expI_arg (mem_sphere_zero_iff_norm.1 hζ)⟩
  set Z : ℝ → ℂ := fun s => ((1 - s : ℝ) : ℂ) * expI (d.angle θ₀ s) with hZ
  have hZc : Continuous Z := by
    have := d.continuous_angle θ₀
    rw [hZ]; fun_prop
  have hnorm : ∀ s, s ≤ 1 → ‖Z s‖ = 1 - s := by
    intro s hs
    rw [hZ]; simp only
    rw [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hZ0 : Z 0 = expI θ₀ := by simp [hZ, d.angle_zero]
  let q : Path (expI θ₀) (Z (1 / 2)) :=
    { toFun := fun t => Z ((t : ℝ) / 2)
      continuous_toFun := hZc.comp (continuous_subtype_val.div_const 2)
      source' := by simpa using hZ0
      target' := by simp }
  have hq : ∀ t : unitInterval, q t = Z ((t : ℝ) / 2) := fun _ => rfl
  have hq_inj : Injective q := by
    intro a b hab
    rw [hq, hq] at hab
    have hn := congrArg norm hab
    rw [hnorm _ (by linarith [a.2.2]), hnorm _ (by linarith [b.2.2])] at hn
    exact Subtype.ext (by linarith)
  refine ⟨range q, Z (1 / 2), ⟨q, hq_inj, rfl⟩, ?_⟩
  rintro _ ⟨⟨t, rfl⟩, hne⟩
  have ht0 : (t : ℝ) ≠ 0 := by
    intro h0
    apply hne
    rw [mem_singleton_iff, hq, h0, zero_div, hZ0]
  have hs0 : 0 < (t : ℝ) / 2 := by
    have := lt_of_le_of_ne t.2.1 (Ne.symm ht0); positivity
  have hs1 : (t : ℝ) / 2 < 1 := by linarith [t.2.2]
  refine ⟨?_, ?_⟩
  · rw [hq, mem_ball_zero_iff, hnorm _ hs1.le]; linarith
  · simp only [mem_iUnion, not_exists]
    exact fun k => d.arc_not_mem θ₀ hζI hs0 hs1 k

end Intervals

/-- `thm:ha-example` (Kaczynski; answer to Bagemihl–Piranian's Problem 5): a bounded harmonic
function in the disc with a boundary function not of Baire class one. Same statement as the pinned
`TJK.Harmonic.exists_bounded_harmonic_boundaryFn_not_baireOne`. -/
theorem exists_bounded_harmonic_boundaryFn_not_baireOne' :
    ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f disc ∧ Bornology.IsBounded (f '' disc) ∧
      ∃ φ : ℂ → ℝ, IsBoundaryFunction disc f circle φ ∧ ¬ IsBaireOne (circle.restrict φ) := by
  have : Nonempty (Ioo (-π) π) := ⟨⟨0, by constructor <;> linarith [Real.pi_pos]⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Ioo (-π) π)
  obtain ⟨d, hcov⟩ := exists_intervals (fun n => (u n : ℝ)) (fun n => (u n).2)
  have hD := d.omega_jordan
  have hden : ∀ x y, -π ≤ x → x < y → y ≤ π →
      ∃ k, ∃ s ∈ Icc (d.α k) (d.β k), x < s ∧ s < y := by
    intro x y hx hxy hy
    have hopen : IsOpen {v : Ioo (-π) π | (v : ℝ) ∈ Ioo x y} :=
      isOpen_Ioo.preimage continuous_subtype_val
    obtain ⟨n, hn⟩ := hu.exists_mem_open hopen
      ⟨⟨(x + y) / 2, by linarith, by linarith⟩, by
        show (x + y) / 2 ∈ Ioo x y; constructor <;> linarith⟩
    obtain ⟨k, hk⟩ := hcov n
    exact ⟨k, u n, hk, hn.1, hn.2⟩
  classical
  let φ : ℂ → ℝ := fun ζ =>
    if (∃ n, ζ ∈ expI '' Ioo (d.α n) (d.β n)) ∨ (∃ n, ζ = expI (d.β n)) then 1 else 0
  refine ⟨d.f, d.f_harmonic.1, ?_, φ, ?_, ?_⟩
  · refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := 1)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_closedBall, Real.dist_eq, sub_zero]
    exact d.f_harmonic.2 z hz
  · intro ζ hζ
    by_cases h : (∃ n, ζ ∈ expI '' Ioo (d.α n) (d.β n)) ∨ (∃ n, ζ = expI (d.β n))
    · have hφ : φ ζ = 1 := if_pos h
      rw [hφ]
      rcases h with ⟨n, t, ht, rfl⟩ | ⟨n, rfl⟩
      · exact (asymptotic_at_endpoints d.f 1 t (d.β n) ht.2
          (by linarith [ht.1, d.α_gt n, d.β_lt n])
          fun s hs => d.f_tendsto_one ⟨by linarith [ht.1, hs.1], hs.2⟩).1
      · exact (asymptotic_at_endpoints d.f 1 (d.α n) (d.β n) (d.α_lt_β n)
          (by linarith [d.α_gt n, d.β_lt n]) fun s hs => d.f_tendsto_one hs).2
    · have hφ : φ ζ = 0 := if_neg h
      push Not at h
      obtain ⟨γ, hγ⟩ := d.accessible hζ h.1
      obtain ⟨b', harc, hsub⟩ := id hγ
      exact ⟨γ, ⟨b', harc, hsub.trans sdiff_subset⟩, hφ ▸ d.f_tendsto_zero_of_arc hγ hζ⟩
  · refine d.not_isBaireOne hden φ (fun n => if_neg ?_) (fun n => if_pos (Or.inr ⟨n, rfl⟩))
    have hαI : d.α n ∈ Ioc (-π) π := Ioo_subset_Ioc_self (hD.Icc_sub n ⟨le_rfl, (d.α_lt_β n).le⟩)
    rintro (⟨m, s, hs, hse⟩ | ⟨m, hm⟩)
    · have hsα := expI_injOn (Ioo_subset_Ioc_self (hD.Icc_sub m (Ioo_subset_Icc_self hs))) hαI hse
      have : m = n := hD.unique (Ioo_subset_Icc_self hs)
        (by rw [hsα]; exact ⟨le_rfl, (d.α_lt_β n).le⟩)
      subst this
      linarith [hs.1]
    · have hβm := expI_injOn hαI
        (Ioo_subset_Ioc_self (hD.Icc_sub m ⟨(d.α_lt_β m).le, le_rfl⟩)) hm
      have : n = m := hD.unique ⟨le_rfl, (d.α_lt_β n).le⟩
        (by rw [hβm]; exact ⟨(d.α_lt_β m).le, le_rfl⟩)
      subst this
      linarith [d.α_lt_β n]

end TJK.Harmonic
