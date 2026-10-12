import Mathlib
import TJK.Defs

/-!
# Poisson integrals on the unit disc (blueprint `fact:poisson` (ii), (iii))

This file imports only Mathlib and `TJK.Defs`, so that `TJK.Harmonic.Example` can import it.
`poisson'` is the same definition as `TJK.Harmonic.poisson` (definitionally equal), and the primed
theorems have the same statements as the imported facts `poisson_tendsto_of_continuousAt` and
`hp_radial_limit_poisson` of `TJK/Harmonic/Example.lean`.

* `poisson_tendsto_of_continuousAt'` (fact:poisson (ii)): proved, by the approximate-identity
  argument (positivity, total mass one, uniform smallness of the kernel away from `ζ₀`).
* `hp_radial_limit_poisson'` (fact:poisson (iii)): skeleton with named sublemmas.
-/

namespace TJK.Harmonic

open _root_.Set Filter Topology Metric Function MeasureTheory Complex
open scoped Real

/-- The Poisson integral `P[φ]` of a function on the unit circle (same as `poisson`). -/
noncomputable def poisson' (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage (fun ζ => poissonKernel 0 z ζ * φ ζ) 0 1

namespace PoissonAux

/-! ### The kernel along the unit circle -/

theorem poissonKernel_circleMap (z : ℂ) (θ : ℝ) :
    poissonKernel 0 z (circleMap 0 1 θ) = (1 - ‖z‖ ^ 2) / ‖circleMap 0 1 θ - z‖ ^ 2 := by
  simp [poissonKernel_def, norm_circleMap_zero]

theorem circleMap_sub_ne_zero {z : ℂ} (hz : z ∈ disc) (θ : ℝ) : circleMap 0 1 θ - z ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have := mem_ball_zero_iff.1 hz
  rw [← h, norm_circleMap_zero, abs_one] at this
  exact lt_irrefl _ this

theorem continuous_kernel {z : ℂ} (hz : z ∈ disc) :
    Continuous fun θ => poissonKernel 0 z (circleMap 0 1 θ) := by
  simp_rw [poissonKernel_circleMap]
  exact continuous_const.div (by fun_prop) fun θ =>
    pow_ne_zero 2 (norm_ne_zero_iff.2 (circleMap_sub_ne_zero hz θ))

theorem kernel_nonneg {z : ℂ} (hz : z ∈ disc) (θ : ℝ) :
    0 ≤ poissonKernel 0 z (circleMap 0 1 θ) := by
  rw [poissonKernel_circleMap]
  have := mem_ball_zero_iff.1 hz
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

/-- Total mass one. -/
theorem kernel_integral {z : ℂ} (hz : z ∈ disc) :
    (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 z (circleMap 0 1 θ) = 1 := by
  have h := (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)).circleAverage_poissonKernel_smul hz
  rw [Real.circleAverage_def, smul_eq_mul] at h
  simpa using h

/-- The kernel is uniformly small away from `ζ₀` when `z` is close to `ζ₀`. -/
theorem kernel_le_of_far {z ζ ζ₀ : ℂ} (hz : z ∈ disc) (hζ : ‖ζ‖ = 1) (hζ₀ : ‖ζ₀‖ = 1) {δ : ℝ}
    (hδ : 0 < δ) (hfar : δ ≤ ‖ζ - ζ₀‖) (hnear : ‖z - ζ₀‖ ≤ δ / 2) :
    poissonKernel 0 z ζ ≤ 8 * ‖z - ζ₀‖ / δ ^ 2 := by
  have hz1 := mem_ball_zero_iff.1 hz
  have hz0 := norm_nonneg z
  have h1 : 1 - ‖z‖ ≤ ‖z - ζ₀‖ := by
    have := norm_sub_norm_le ζ₀ z
    rw [hζ₀, norm_sub_rev] at this
    linarith
  have h2 : δ / 2 ≤ ‖ζ - z‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub ζ z ζ₀
    linarith
  have h3 : 0 < ‖ζ - z‖ := by linarith
  simp only [poissonKernel_def, sub_zero, hζ, one_pow]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : δ ^ 2 ≤ 4 * ‖ζ - z‖ ^ 2 := by nlinarith
  have h5 : 1 - ‖z‖ ^ 2 ≤ 2 * ‖z - ζ₀‖ := by nlinarith
  have h6 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
  calc (1 - ‖z‖ ^ 2) * δ ^ 2 ≤ (2 * ‖z - ζ₀‖) * (4 * ‖ζ - z‖ ^ 2) :=
        mul_le_mul h5 h4 (by positivity) (by positivity)
    _ = 8 * ‖z - ζ₀‖ * ‖ζ - z‖ ^ 2 := by ring

/-- `P[φ](z) - c = (2π)⁻¹ ∫ P(z, e^{iθ}) (φ(e^{iθ}) - c) dθ`. -/
theorem poisson'_sub_eq {φ : ℂ → ℝ} (hφ : CircleIntegrable φ 0 1) {z : ℂ} (hz : z ∈ disc)
    (c : ℝ) : poisson' φ z - c = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      poissonKernel 0 z (circleMap 0 1 θ) * (φ (circleMap 0 1 θ) - c) := by
  have hK := kernel_integral hz
  have hi1 : IntervalIntegrable
      (fun θ => poissonKernel 0 z (circleMap 0 1 θ) * φ (circleMap 0 1 θ)) volume 0 (2 * π) :=
    IntervalIntegrable.continuousOn_mul hφ (continuous_kernel hz).continuousOn
  have hi2 : IntervalIntegrable (fun θ => poissonKernel 0 z (circleMap 0 1 θ) * c)
      volume 0 (2 * π) :=
    ((continuous_kernel hz).mul continuous_const).intervalIntegrable _ _
  simp only [mul_sub]
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_mul_const, poisson',
    Real.circleAverage_def, smul_eq_mul, mul_sub, ← mul_assoc, hK, one_mul]

end PoissonAux

open PoissonAux in
/-- `fact:poisson` (ii): if `φ` is integrable on the circle, `S` has full measure on the circle,
`ζ₀ ∈ S` and `φ|_S` is continuous at `ζ₀`, then `P[φ]` has the general limit `φ ζ₀` at `ζ₀`. -/
theorem poisson_tendsto_of_continuousAt' (φ : ℂ → ℝ) (hφ : CircleIntegrable φ 0 1) (S : Set ℂ)
    (hS : ∀ᵐ θ, circleMap 0 1 θ ∈ S) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ S ∩ circle)
    (hc : ContinuousWithinAt φ (S ∩ circle) ζ₀) :
    Tendsto (poisson' φ) (𝓝[disc] ζ₀) (𝓝 (φ ζ₀)) := by
  have hζ₀1 : ‖ζ₀‖ = 1 := mem_sphere_zero_iff_norm.1 hζ₀.2
  set g : ℝ → ℝ := fun θ => φ (circleMap 0 1 θ) - φ ζ₀ with hg
  have hgi : IntervalIntegrable g volume 0 (2 * π) :=
    IntervalIntegrable.sub hφ intervalIntegrable_const
  set C : ℝ := (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, |g θ| with hC
  have hC0 : 0 ≤ C := mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg Real.two_pi_pos.le fun θ _ => abs_nonneg _)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hc (ε / 2) (by positivity)
  refine ⟨min (δ / 2) (ε * δ ^ 2 / (16 * (C + 1))), by positivity, fun z hz hzd => ?_⟩
  rw [dist_eq_norm] at hzd
  have hzd1 : ‖z - ζ₀‖ < δ / 2 := lt_of_lt_of_le hzd (min_le_left _ _)
  have hzd2 : ‖z - ζ₀‖ < ε * δ ^ 2 / (16 * (C + 1)) := lt_of_lt_of_le hzd (min_le_right _ _)
  rw [Real.dist_eq, poisson'_sub_eq hφ hz]
  set c : ℝ := 8 * ‖z - ζ₀‖ / δ ^ 2 with hcdef
  have hc0 : 0 ≤ c := by positivity
  set K : ℝ → ℝ := fun θ => poissonKernel 0 z (circleMap 0 1 θ) with hKdef
  have hKc : Continuous K := continuous_kernel hz
  have hpt : ∀ᵐ θ, |K θ * g θ| ≤ ε / 2 * K θ + c * |g θ| := by
    filter_upwards [hS] with θ hθ
    have hK0 : 0 ≤ K θ := kernel_nonneg hz θ
    rw [abs_mul, abs_of_nonneg hK0]
    by_cases hnear : ‖circleMap 0 1 θ - ζ₀‖ < δ
    · have h1 := hδc ⟨hθ, circleMap_mem_sphere 0 zero_le_one θ⟩ (by rwa [dist_eq_norm])
      rw [Real.dist_eq] at h1
      have h2 : K θ * |g θ| ≤ K θ * (ε / 2) := mul_le_mul_of_nonneg_left h1.le hK0
      nlinarith [abs_nonneg (g θ)]
    · have hfar := kernel_le_of_far hz (by simp [norm_circleMap_zero]) hζ₀1 hδ
        (not_lt.1 hnear) hzd1.le
      have h2 : K θ * |g θ| ≤ c * |g θ| := mul_le_mul_of_nonneg_right hfar (abs_nonneg (g θ))
      nlinarith
  have hi1 : IntervalIntegrable (fun θ => |K θ * g θ|) volume 0 (2 * π) :=
    (IntervalIntegrable.continuousOn_mul hgi hKc.continuousOn).abs
  have hi2 : IntervalIntegrable (fun θ => ε / 2 * K θ) volume 0 (2 * π) :=
    (continuous_const.mul hKc).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun θ => c * |g θ|) volume 0 (2 * π) := hgi.abs.const_mul c
  have hmono := intervalIntegral.integral_mono_ae Real.two_pi_pos.le hi1 (hi2.add hi3) hpt
  rw [intervalIntegral.integral_add hi2 hi3, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun θ => K θ * g θ) Real.two_pi_pos.le
  have hK1 := kernel_integral hz
  have hpi : 0 < (2 * π)⁻¹ := by positivity
  have hcC : c * C < ε / 2 := by
    have h1 : ‖z - ζ₀‖ * (16 * (C + 1)) < ε * δ ^ 2 := (lt_div_iff₀ (by positivity)).1 hzd2
    rw [hcdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (z - ζ₀)]
  calc |(2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, K θ * g θ|
      = (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, K θ * g θ| := by
        rw [abs_mul, abs_of_pos hpi]
    _ ≤ (2 * π)⁻¹ * (ε / 2 * (∫ θ in (0 : ℝ)..2 * π, K θ) + c * ∫ θ in (0 : ℝ)..2 * π, |g θ|) :=
        mul_le_mul_of_nonneg_left (habs.trans hmono) hpi.le
    _ = ε / 2 * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, K θ) + c * C := by rw [hC]; ring
    _ < ε := by rw [hK1]; linarith

/-! ### `fact:poisson` (iii): skeleton

Route (Hoffman, *Banach spaces of analytic functions*, pp. 32–38; Katznelson I.3):

* (A) `poisson'_radius`: Poisson formula on the circles `|ζ| = s < 1` (proved, from Mathlib's
  `HarmonicOnNhd.circleAverage_poissonKernel_smul`).
* (B) `unifInt_of_pMean`: Hölder: bounded `p`-means give `∫_E |u_s| ≤ C |E|^(1 - 1/p)` uniformly in
  `s` (uniform integrability with a modulus).
* (C) `exists_poisson_rep_of_unifInt`: the finite measures `u_s^± dθ` on the circle have a cluster
  point `(μ⁺, μ⁻)` as `s → 1` (Mathlib: `isCompact_setOfPred_finiteMeasure_le_of_compactSpace`);
  testing (A) against the continuous kernel `P(z, ·)` gives `u(z) = ∫ P(z, ·) d(μ⁺ - μ⁻)`; the
  modulus of (B) passes to the limit on compact sets, so `μ^± ≪ dθ`, and `ψ` is the difference of
  the Radon–Nikodym derivatives.
* (D) `poisson'_radial_tendsto_ae`: Fatou's theorem: `P[ψ]` has radial limit `ψ` at each Lebesgue
  point of `ψ ∘ circleMap` (D1, kernel estimate), and a.e. point is one (D2, Mathlib's
  `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`).
-/

namespace PoissonAux

theorem poissonKernel_smul {s : ℝ} (hs : s ≠ 0) (z ζ : ℂ) :
    poissonKernel 0 ((s : ℂ) * z) ((s : ℂ) * ζ) = poissonKernel 0 z ζ := by
  simp only [poissonKernel_def, sub_zero, ← mul_sub, norm_mul, Complex.norm_real, mul_pow,
    ← mul_sub]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (by simpa using hs))

/-- (A) The Poisson formula on the circle of radius `s < 1`, rescaled to the unit circle. -/
theorem poisson'_radius {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u disc) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) {z : ℂ} (hz : z ∈ disc) :
    u (s * z) = poisson' (fun ζ => u (s * ζ)) z := by
  have hsub : closedBall (0 : ℂ) s ⊆ disc := closedBall_subset_ball hs.2
  have hw : (s : ℂ) * z ∈ ball (0 : ℂ) s := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
    exact mul_lt_of_lt_one_right hs.1 (mem_ball_zero_iff.1 hz)
  have h := (hu.mono hsub).circleAverage_poissonKernel_smul hw
  rw [← h, poisson', Real.circleAverage_def, Real.circleAverage_def]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hc : circleMap 0 s θ = (s : ℂ) * circleMap 0 1 θ := by simp [circleMap]
  simp only [Pi.smul_apply', smul_eq_mul, hc, poissonKernel_smul hs.1.ne']

/-- (B) Hölder: bounded `p`-means, `p > 1`, give a uniform modulus of absolute continuity for the
integrals of `|u_s|` over sets of angles. Expected: 1 session. -/
theorem unifInt_of_pMean {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u disc) {p : ℝ}
    (hp : 1 < p) (hmean : ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
      ∫ θ in (0 : ℝ)..(2 * π), |u (r * Complex.exp (θ * Complex.I))| ^ p ≤ B) :
    ∃ C : ℝ, ∀ s ∈ Ico (0 : ℝ) 1, ∀ E : Set ℝ, MeasurableSet E →
      ∫ θ in E ∩ Ioc 0 (2 * π), |u (s * circleMap 0 1 θ)| ≤
        C * volume.real (E ∩ Ioc 0 (2 * π)) ^ (1 - 1 / p) := by
  sorry

/-- (C) A harmonic function whose circle restrictions are uniformly integrable (with a modulus
`C |E|^q`, `q > 0`) is the Poisson integral of an integrable function. Expected: 2–3 sessions
(compactness of finite measures, testing against `P(z, ·)`, absolute continuity of the limit,
Radon–Nikodym). -/
theorem exists_poisson_rep_of_unifInt {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u disc)
    {q C : ℝ} (hq : 0 < q)
    (hC : ∀ s ∈ Ico (0 : ℝ) 1, ∀ E : Set ℝ, MeasurableSet E →
      ∫ θ in E ∩ Ioc 0 (2 * π), |u (s * circleMap 0 1 θ)| ≤
        C * volume.real (E ∩ Ioc 0 (2 * π)) ^ q) :
    ∃ ψ : ℂ → ℝ, CircleIntegrable ψ 0 1 ∧ ∀ z ∈ disc, u z = poisson' ψ z := by
  sorry

/-- (D1) Fatou's theorem at a Lebesgue point of `g = ψ ∘ circleMap`. Expected: 1–2 sessions
(kernel bound `P_r(t) ≤ C min((1-r)⁻¹, (1-r)/t²)` and a layer-cake or dyadic estimate). -/
theorem poisson'_radial_tendsto_of_lebesgue {ψ : ℂ → ℝ} (hψ : CircleIntegrable ψ 0 1) {θ₀ : ℝ}
    (hθ₀ : Tendsto (fun h => ⨍ t in closedBall θ₀ h, |ψ (circleMap 0 1 t) - ψ (circleMap 0 1 θ₀)|)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => poisson' ψ (r * circleMap 0 1 θ₀)) (𝓝[<] 1)
      (𝓝 (ψ (circleMap 0 1 θ₀))) := by
  sorry

/-- (D2) Almost every angle is a Lebesgue point of `ψ ∘ circleMap` (Lebesgue differentiation on
`ℝ`; `ψ ∘ circleMap` is periodic and integrable on a period, hence locally integrable). -/
theorem ae_lebesgue_point {ψ : ℂ → ℝ} (hψ : CircleIntegrable ψ 0 1) :
    ∀ᵐ θ₀, Tendsto
      (fun h => ⨍ t in closedBall θ₀ h, |ψ (circleMap 0 1 t) - ψ (circleMap 0 1 θ₀)|)
      (𝓝[>] 0) (𝓝 0) := by
  set g : ℝ → ℝ := fun t => ψ (circleMap 0 1 t) with hg
  have hper : Periodic g (2 * π) := fun t => by simp only [hg, periodic_circleMap 0 1 t]
  have hII : ∀ a b, IntervalIntegrable g volume a b :=
    hper.intervalIntegrable₀ Real.two_pi_pos.ne' hψ
  have hloc : LocallyIntegrable g volume := fun x =>
    ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 (hII _ _)⟩
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1] with x hx
  have := hx (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id
    (by filter_upwards [self_mem_nhdsWithin] with j hj; simpa using (le_of_lt hj))
  simpa [Real.norm_eq_abs] using this

/-- (D) Fatou's theorem: the Poisson integral of an integrable function has radial limits equal to
the function almost everywhere. -/
theorem poisson'_radial_tendsto_ae {ψ : ℂ → ℝ} (hψ : CircleIntegrable ψ 0 1) :
    ∀ᵐ θ, Tendsto (fun r : ℝ => poisson' ψ (r * circleMap 0 1 θ)) (𝓝[<] 1)
      (𝓝 (ψ (circleMap 0 1 θ))) := by
  filter_upwards [ae_lebesgue_point hψ] with θ hθ using poisson'_radial_tendsto_of_lebesgue hψ hθ

end PoissonAux

open PoissonAux in
/-- `fact:poisson` (iii): a harmonic function in the disc with bounded `p`-th integral means,
`p > 1`, has radial limits almost everywhere on the circle, and it is the Poisson integral of its
(integrable) radial limit function. -/
theorem hp_radial_limit_poisson' (u : ℂ → ℝ) (hu : InnerProductSpace.HarmonicOnNhd u disc)
    (p : ℝ) (hp : 1 < p)
    (hmean : ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
      ∫ θ in (0 : ℝ)..(2 * π), |u (r * Complex.exp (θ * Complex.I))| ^ p ≤ B) :
    ∃ ψ : ℂ → ℝ, CircleIntegrable ψ 0 1 ∧
      (∀ᵐ θ, Tendsto (fun r : ℝ => u (r * circleMap 0 1 θ)) (𝓝[<] 1)
        (𝓝 (ψ (circleMap 0 1 θ)))) ∧
      ∀ z ∈ disc, u z = poisson' ψ z := by
  obtain ⟨C, hC⟩ := unifInt_of_pMean hu hp hmean
  have hq : 0 < 1 - 1 / p := by
    have : 1 / p < 1 := (div_lt_one (by linarith)).2 hp
    linarith
  obtain ⟨ψ, hψ, hrep⟩ := exists_poisson_rep_of_unifInt hu hq hC
  refine ⟨ψ, hψ, ?_, hrep⟩
  filter_upwards [poisson'_radial_tendsto_ae hψ] with θ hθ
  refine hθ.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with r hr
  refine (hrep _ ?_).symm
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1,
    norm_circleMap_zero, abs_one, mul_one]
  exact hr.2

end TJK.Harmonic
