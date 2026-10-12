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
* `hp_radial_limit_poisson'` (fact:poisson (iii)): proved, via the named sublemmas (A)–(D).
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
  modulus of (B) passes to the limit on closed sets, so `μ^± ≪ dθ`, and `ψ` is the difference of
  the Radon–Nikodym derivatives (proved: `exists_limit_density`).
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
integrals of `|u_s|` over sets of angles (Hölder with the indicator of `E`). -/
theorem unifInt_of_pMean {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u disc) {p : ℝ}
    (hp : 1 < p) (hmean : ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
      ∫ θ in (0 : ℝ)..(2 * π), |u (r * Complex.exp (θ * Complex.I))| ^ p ≤ B) :
    ∃ C : ℝ, ∀ s ∈ Ico (0 : ℝ) 1, ∀ E : Set ℝ, MeasurableSet E →
      ∫ θ in E ∩ Ioc 0 (2 * π), |u (s * circleMap 0 1 θ)| ≤
        C * volume.real (E ∩ Ioc 0 (2 * π)) ^ (1 - 1 / p) := by
  obtain ⟨B, hB⟩ := hmean
  set q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < q := hpq.symm.pos
  have hp0 : 0 < p := by linarith
  have h1q : 1 / q = 1 - 1 / p := by
    have := hpq.one_div_add_one_div
    rw [div_one] at this
    linarith
  refine ⟨max B 0 ^ (1 / p), fun s hs E hE => ?_⟩
  set S := Ioc (0 : ℝ) (2 * π) with hSdef
  set μ := volume.restrict S with hμ
  set f : ℝ → ℝ := fun θ => |u (s * circleMap 0 1 θ)| with hf
  have hcont : Continuous f := by
    have hc : Continuous fun θ : ℝ => (s : ℂ) * circleMap 0 1 θ :=
      continuous_const.mul (continuous_circleMap 0 1)
    refine continuous_abs.comp (hu.continuousOn.comp_continuous hc fun θ => ?_)
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1,
      norm_circleMap_zero, abs_one, mul_one]
    exact hs.2
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hfm : MemLp f (ENNReal.ofReal p) μ :=
    MemLp.of_bound hcont.aestronglyMeasurable M
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hM x (Ioc_subset_Icc_self hx))
  set g : ℝ → ℝ := E.indicator fun _ => (1 : ℝ) with hg
  have hgm : MemLp g (ENNReal.ofReal q) μ :=
    memLp_indicator_const _ hE (1 : ℝ) (Or.inr (measure_ne_top _ _))
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (Eventually.of_forall fun x => abs_nonneg _)
    (Eventually.of_forall fun x => by simp only [hg]; exact indicator_nonneg (fun _ _ => zero_le_one) x)
    hfm hgm
  have hL : ∫ θ, f θ * g θ ∂μ = ∫ θ in E ∩ S, f θ := by
    have : (fun θ => f θ * g θ) = E.indicator f := by
      funext θ
      by_cases h : θ ∈ E <;> simp [hg, h]
    rw [this, integral_indicator hE, hμ, Measure.restrict_restrict hE]
  have hR2 : ∫ θ, g θ ^ q ∂μ = volume.real (E ∩ S) := by
    have : (fun θ => g θ ^ q) = g := by
      funext θ
      by_cases h : θ ∈ E <;> simp [hg, h, hq0.ne']
    rw [this, hg]
    change ∫ x, E.indicator 1 x ∂μ = _
    rw [integral_indicator_one hE, hμ, measureReal_restrict_apply hE]
  have hR1 : ∫ θ, f θ ^ p ∂μ ≤ max B 0 := by
    have h := hB s hs
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
    refine le_trans (le_of_eq ?_) (h.trans (le_max_left _ _))
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp [hf, circleMap]
  have hR1' : (∫ θ, f θ ^ p ∂μ) ^ (1 / p) ≤ max B 0 ^ (1 / p) :=
    Real.rpow_le_rpow (integral_nonneg fun θ => Real.rpow_nonneg (abs_nonneg _) _) hR1
      (by positivity)
  rw [hL, hR2, h1q] at hH
  refine hH.trans (mul_le_mul_of_nonneg_right hR1' (Real.rpow_nonneg measureReal_nonneg _))

/-! ### (C): limits of the measures `u_s^± dθ` -/

open scoped ENNReal NNReal BoundedContinuousFunction

/-- The angle map to the unit circle, as a map into the subtype `sphere 0 1`. -/
noncomputable def angS (θ : ℝ) : sphere (0 : ℂ) 1 :=
  ⟨circleMap 0 1 θ, circleMap_mem_sphere 0 zero_le_one θ⟩

theorem continuous_angS : Continuous angS :=
  (continuous_circleMap 0 1).subtype_mk _

theorem measurable_angS : Measurable angS := continuous_angS.measurable

/-- Arc-length measure on the unit circle (total mass `2π`). -/
noncomputable def arcMeas : Measure (sphere (0 : ℂ) 1) :=
  (volume.restrict (Ioc 0 (2 * π))).map angS

instance : IsFiniteMeasure arcMeas :=
  ⟨by
    rw [arcMeas, Measure.map_apply measurable_angS MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩

theorem arcMeas_real_apply {A : Set (sphere (0 : ℂ) 1)} (hA : MeasurableSet A) :
    arcMeas.real A = volume.real (angS ⁻¹' A ∩ Ioc 0 (2 * π)) := by
  rw [measureReal_def, measureReal_def, arcMeas, Measure.map_apply measurable_angS hA,
    Measure.restrict_apply (measurable_angS hA)]

theorem isFiniteMeasure_angMeas {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc 0 (2 * π))) :
    IsFiniteMeasure (((volume.restrict (Ioc 0 (2 * π))).withDensity
      fun θ => ENNReal.ofReal (f θ)).map angS) := by
  have := isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  infer_instance

open Classical in
/-- The finite measure `f⁺ dθ` transported to the unit circle. -/
noncomputable def angMeas (f : ℝ → ℝ) : FiniteMeasure (sphere (0 : ℂ) 1) :=
  if hf : IntegrableOn f (Ioc 0 (2 * π)) then (⟨_, isFiniteMeasure_angMeas hf⟩ : FiniteMeasure _)
  else 0

theorem angMeas_coe {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc 0 (2 * π))) :
    (angMeas f : Measure (sphere (0 : ℂ) 1)) = ((volume.restrict (Ioc 0 (2 * π))).withDensity
      fun θ => ENNReal.ofReal (f θ)).map angS := by
  unfold angMeas
  exact congrArg Subtype.val (dif_pos hf)

theorem angMeas_apply_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc 0 (2 * π)))
    {A : Set (sphere (0 : ℂ) 1)} (hA : MeasurableSet A) :
    (angMeas f : Measure (sphere (0 : ℂ) 1)) A ≤
      ENNReal.ofReal (∫ θ in angS ⁻¹' A ∩ Ioc 0 (2 * π), |f θ|) := by
  rw [angMeas_coe hf, Measure.map_apply measurable_angS hA,
    withDensity_apply _ (measurable_angS hA),
    Measure.restrict_restrict (measurable_angS hA)]
  calc ∫⁻ θ in angS ⁻¹' A ∩ Ioc 0 (2 * π), ENNReal.ofReal (f θ)
      ≤ ∫⁻ θ in angS ⁻¹' A ∩ Ioc 0 (2 * π), ENNReal.ofReal |f θ| :=
        lintegral_mono fun θ => ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (hf.mono_set inter_subset_right).abs
        (ae_of_all _ fun θ => abs_nonneg _)).symm

theorem angMeas_integral {f : ℝ → ℝ} (hf : Continuous f) {g : sphere (0 : ℂ) 1 → ℝ}
    (hg : Continuous g) :
    ∫ x, g x ∂(angMeas f : Measure (sphere (0 : ℂ) 1)) =
      ∫ θ in Ioc 0 (2 * π), g (angS θ) * max (f θ) 0 := by
  rw [angMeas_coe hf.integrableOn_Ioc, integral_map measurable_angS.aemeasurable
    hg.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul
    hf.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext θ
  rw [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm]

/-- Cluster point along an ultrafilter `𝒰 ∋ [0, 1)` of the finite measures `(F s)⁺ dθ` on the
circle, for a family `F s` with the uniform modulus `C |E|^q`: the limit is absolutely continuous
(the modulus passes to closed sets via thickened indicators), so it has an integrable density
`ρ`. -/
theorem exists_limit_density {F : ℝ → ℝ → ℝ} (𝒰 : Ultrafilter ℝ) (hU : Ico (0 : ℝ) 1 ∈ 𝒰)
    (hFc : ∀ s ∈ Ico (0 : ℝ) 1, Continuous (F s)) {q C : ℝ} (hq : 0 < q)
    (hC : ∀ s ∈ Ico (0 : ℝ) 1, ∀ E : Set ℝ, MeasurableSet E →
      ∫ θ in E ∩ Ioc 0 (2 * π), |F s θ| ≤ C * volume.real (E ∩ Ioc 0 (2 * π)) ^ q) :
    ∃ ρ : sphere (0 : ℂ) 1 → ℝ, Measurable ρ ∧ Integrable ρ arcMeas ∧
      ∀ g : sphere (0 : ℂ) 1 →ᵇ ℝ,
        Tendsto (fun s => ∫ θ in Ioc 0 (2 * π), g (angS θ) * max (F s θ) 0) 𝒰
          (𝓝 (∫ θ in Ioc 0 (2 * π), g (angS θ) * ρ (angS θ))) := by
  have hFi : ∀ s ∈ Ico (0 : ℝ) 1, IntegrableOn (F s) (Ioc 0 (2 * π)) :=
    fun s hs => (hFc s hs).integrableOn_Ioc
  set M : ℝ≥0 := (C * (2 * π) ^ q).toNNReal with hM
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ∀ A, MeasurableSet A →
      (angMeas (F s) : Measure (sphere (0 : ℂ) 1)) A ≤ ENNReal.ofReal (C * arcMeas.real A ^ q) := by
    intro s hs A hA
    refine (angMeas_apply_le (hFi s hs) hA).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [arcMeas_real_apply hA]
    exact hC s hs _ (measurable_angS hA)
  have hmass : ∀ s ∈ Ico (0 : ℝ) 1, (angMeas (F s)).mass ≤ M := by
    intro s hs
    have h := hbound s hs univ MeasurableSet.univ
    rw [arcMeas_real_apply MeasurableSet.univ, preimage_univ, univ_inter,
      Real.volume_real_Ioc_of_le Real.two_pi_pos.le, sub_zero] at h
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass]
    exact h
  obtain ⟨μ, -, hμ⟩ := (isCompact_setOfPred_finiteMeasure_le_of_compactSpace
    (sphere (0 : ℂ) 1) M).ultrafilter_le_nhds (𝒰.map fun s => angMeas (F s)) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact Filter.mem_map.2 (Filter.mem_of_superset hU fun s hs => hmass s hs))
  have hT : Tendsto (fun s => angMeas (F s)) 𝒰 (𝓝 μ) := by
    rw [Ultrafilter.coe_map] at hμ
    exact hμ
  have hac : (μ : Measure (sphere (0 : ℂ) 1)) ≪ arcMeas := by
    refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
    have hK : ∀ K, IsClosed K → K ⊆ A → (μ : Measure (sphere (0 : ℂ) 1)) K = 0 := by
      intro K hKc hKA
      have hνK : arcMeas K = 0 := measure_mono_null hKA hA0
      have hδ : ∀ δ (hδ : 0 < δ), (μ : Measure (sphere (0 : ℂ) 1)) K ≤
          ENNReal.ofReal (C * arcMeas.real (thickening δ K) ^ q) := by
        intro δ hδ
        set g := thickenedIndicator hδ K
        have h1 : (μ : Measure (sphere (0 : ℂ) 1)) K ≤
            ∫⁻ x, g x ∂(μ : Measure (sphere (0 : ℂ) 1)) := by
          rw [← lintegral_indicator_one hKc.measurableSet]
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ K
          · simp [hx, g, thickenedIndicator_one hδ K hx]
          · simp [hx]
        have h2 := (FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.1 hT) g
        refine h1.trans (le_of_tendsto h2 ?_)
        filter_upwards [hU] with s hs
        calc ∫⁻ x, g x ∂(angMeas (F s) : Measure (sphere (0 : ℂ) 1))
            ≤ ∫⁻ x, (thickening δ K).indicator 1 x
                ∂(angMeas (F s) : Measure (sphere (0 : ℂ) 1)) := by
              refine lintegral_mono fun x => ?_
              by_cases hx : x ∈ thickening δ K
              · simp only [hx, indicator_of_mem, Pi.one_apply]
                exact_mod_cast thickenedIndicator_le_one hδ K x
              · simp [hx, g, thickenedIndicator_zero hδ K hx]
          _ = _ := lintegral_indicator_one isOpen_thickening.measurableSet
          _ ≤ _ := hbound s hs _ isOpen_thickening.measurableSet
      have hlim : Tendsto (fun δ => ENNReal.ofReal (C * arcMeas.real (thickening δ K) ^ q))
          (𝓝[>] 0) (𝓝 0) := by
        have h1 := tendsto_measure_thickening_of_isClosed (μ := arcMeas)
          ⟨1, one_pos, measure_ne_top _ _⟩ hKc
        rw [hνK] at h1
        have h2 : Tendsto (fun δ => arcMeas.real (thickening δ K)) (𝓝[>] 0) (𝓝 0) := by
          have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
          exact this
        have h3 : ContinuousAt (fun x : ℝ => ENNReal.ofReal (C * x ^ q)) 0 :=
          ENNReal.continuous_ofReal.continuousAt.comp
            ((Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).const_mul C)
        have h4 := h3.tendsto.comp h2
        rwa [Real.zero_rpow hq.ne', mul_zero, ENNReal.ofReal_zero] at h4
      exact nonpos_iff_eq_zero.1 (ge_of_tendsto hlim
        (eventually_nhdsWithin_of_forall fun δ hδ' => hδ δ hδ'))
    by_contra h
    obtain ⟨K, hKA, hKc, hlt⟩ := hA.exists_isClosed_lt_add
      (measure_ne_top (μ : Measure (sphere (0 : ℂ) 1)) A) h
    rw [hK K hKc hKA, zero_add] at hlt
    exact lt_irrefl _ hlt
  refine ⟨fun x => ((μ : Measure (sphere (0 : ℂ) 1)).rnDeriv arcMeas x).toReal,
    (Measure.measurable_rnDeriv _ _).ennreal_toReal,
    Measure.integrable_toReal_rnDeriv (μ := (μ : Measure (sphere (0 : ℂ) 1))),
    fun g => ?_⟩
  have h := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hT) g
  have hlimeq : ∫ x, g x ∂(μ : Measure (sphere (0 : ℂ) 1)) = ∫ θ in Ioc 0 (2 * π),
      g (angS θ) * ((μ : Measure (sphere (0 : ℂ) 1)).rnDeriv arcMeas (angS θ)).toReal := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
    rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)]
    conv_lhs => rw [arcMeas]
    rw [integral_map measurable_angS.aemeasurable ?_]
    · congr 1
      funext θ
      rw [smul_eq_mul, mul_comm]
      rfl
    · exact ((Measure.measurable_rnDeriv _ _).ennreal_toReal.mul
        g.continuous.measurable).aestronglyMeasurable
  rw [hlimeq] at h
  refine h.congr' ?_
  filter_upwards [hU] with s hs
  exact angMeas_integral (hFc s hs) g.continuous

/-- (C) A harmonic function whose circle restrictions are uniformly integrable (with a modulus
`C |E|^q`, `q > 0`) is the Poisson integral of an integrable function: the densities `ρ±` of
`exists_limit_density` for `±u_s` give `ψ = ρ⁺ - ρ⁻`, and testing (A) against the continuous
kernel `P(z, ·)` identifies `u(z)` with `P[ψ](z)`. -/
theorem exists_poisson_rep_of_unifInt {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u disc)
    {q C : ℝ} (hq : 0 < q)
    (hC : ∀ s ∈ Ico (0 : ℝ) 1, ∀ E : Set ℝ, MeasurableSet E →
      ∫ θ in E ∩ Ioc 0 (2 * π), |u (s * circleMap 0 1 θ)| ≤
        C * volume.real (E ∩ Ioc 0 (2 * π)) ^ q) :
    ∃ ψ : ℂ → ℝ, CircleIntegrable ψ 0 1 ∧ ∀ z ∈ disc, u z = poisson' ψ z := by
  classical
  set 𝒰 : Ultrafilter ℝ := Ultrafilter.of (𝓝[<] (1 : ℝ)) with h𝒰
  have hU1 : (𝒰 : Filter ℝ) ≤ 𝓝[<] 1 := Ultrafilter.of_le _
  have hU : Ico (0 : ℝ) 1 ∈ 𝒰 := hU1 (Ico_mem_nhdsLT zero_lt_one)
  have hUo : Ioo (0 : ℝ) 1 ∈ 𝒰 := hU1 (Ioo_mem_nhdsLT zero_lt_one)
  have hcont : ∀ s ∈ Ico (0 : ℝ) 1, Continuous fun θ => u (s * circleMap 0 1 θ) := by
    intro s hs
    have hc : Continuous fun θ : ℝ => (s : ℂ) * circleMap 0 1 θ :=
      continuous_const.mul (continuous_circleMap 0 1)
    refine hu.continuousOn.comp_continuous hc fun θ => ?_
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1,
      norm_circleMap_zero, abs_one, mul_one]
    exact hs.2
  obtain ⟨ρ₁, hρ₁m, hρ₁i, hρ₁⟩ := exists_limit_density (F := fun s θ => u (s * circleMap 0 1 θ))
    𝒰 hU hcont hq hC
  obtain ⟨ρ₂, hρ₂m, hρ₂i, hρ₂⟩ := exists_limit_density
    (F := fun s θ => -u (s * circleMap 0 1 θ)) 𝒰 hU (fun s hs => (hcont s hs).neg) hq
    (by simpa only [abs_neg] using hC)
  set ψ : ℂ → ℝ := fun ζ => if h : ζ ∈ sphere (0 : ℂ) 1 then ρ₁ ⟨ζ, h⟩ - ρ₂ ⟨ζ, h⟩ else 0
    with hψdef
  have hψ : ∀ θ, ψ (circleMap 0 1 θ) = ρ₁ (angS θ) - ρ₂ (angS θ) := fun θ => by
    simp only [ψ, dif_pos (circleMap_mem_sphere 0 zero_le_one θ)]
    rfl
  have hi₁ : IntegrableOn (fun θ => ρ₁ (angS θ)) (Ioc 0 (2 * π)) :=
    (integrable_map_measure hρ₁m.aestronglyMeasurable measurable_angS.aemeasurable).1 hρ₁i
  have hi₂ : IntegrableOn (fun θ => ρ₂ (angS θ)) (Ioc 0 (2 * π)) :=
    (integrable_map_measure hρ₂m.aestronglyMeasurable measurable_angS.aemeasurable).1 hρ₂i
  refine ⟨ψ, ?_, fun z hz => ?_⟩
  · rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
    simp only [hψ]
    exact hi₁.sub hi₂
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hKc : Continuous fun ζ : sphere (0 : ℂ) 1 => poissonKernel 0 z ζ := by
    simp only [poissonKernel_def, sub_zero]
    refine Continuous.div (by fun_prop) (by fun_prop) fun ζ => ?_
    have h1 : ‖(ζ : ℂ)‖ = 1 := norm_eq_of_mem_sphere ζ
    refine pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 fun h => ?_))
    rw [h] at h1
    linarith
  set K : sphere (0 : ℂ) 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨_, hKc⟩ with hKdef
  have hKθ : ∀ θ, K (angS θ) = poissonKernel 0 z (circleMap 0 1 θ) := fun θ => rfl
  have hKcont : Continuous fun θ => K (angS θ) := K.continuous.comp continuous_angS
  have h1 := ((hρ₁ K).sub (hρ₂ K)).const_mul (2 * π)⁻¹
  have hlim : Tendsto (fun s : ℝ => u (s * z)) 𝒰 (𝓝 (u z)) := by
    have hc : ContinuousAt (fun s : ℝ => u (s * z)) 1 :=
      ContinuousAt.comp_of_eq (hu.continuousOn.continuousAt (isOpen_ball.mem_nhds hz))
        (by fun_prop) (by simp)
    have := hc.tendsto
    simp only [Complex.ofReal_one, one_mul] at this
    exact this.mono_left (hU1.trans nhdsWithin_le_nhds)
  have hev : ∀ᶠ s : ℝ in (𝒰 : Filter ℝ), u ((s : ℂ) * z) = (2 * π)⁻¹ *
      ((∫ θ in Ioc 0 (2 * π), K (angS θ) * max (u (s * circleMap 0 1 θ)) 0) -
        ∫ θ in Ioc 0 (2 * π), K (angS θ) * max (-u (s * circleMap 0 1 θ)) 0) := by
    filter_upwards [hUo] with s hs
    have hc := hcont s (Ioo_subset_Ico_self hs)
    have i1 : IntegrableOn (fun θ => K (angS θ) * max (u (s * circleMap 0 1 θ)) 0)
        (Ioc 0 (2 * π)) := (hKcont.mul (hc.max continuous_const)).integrableOn_Ioc
    have i2 : IntegrableOn (fun θ => K (angS θ) * max (-u (s * circleMap 0 1 θ)) 0)
        (Ioc 0 (2 * π)) := (hKcont.mul (hc.neg.max continuous_const)).integrableOn_Ioc
    rw [poisson'_radius hu hs hz, poisson', Real.circleAverage_def, smul_eq_mul,
      intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_sub i1 i2]
    congr 2
    funext θ
    rw [hKθ, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  have h3 := h1.congr' (hev.mono fun s hs => hs.symm)
  rw [tendsto_nhds_unique hlim h3, poisson', Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ← integral_sub (hi₁.bdd_mul hKcont.aestronglyMeasurable
      (ae_of_all _ fun θ => K.norm_coe_le_norm _))
      (hi₂.bdd_mul hKcont.aestronglyMeasurable (ae_of_all _ fun θ => K.norm_coe_le_norm _))]
  congr 2
  funext θ
  rw [hψ, hKθ, mul_sub]

/-- Chord length on the unit circle: `|e^{iθ} - e^{iθ₀}| ≥ (2/π) |θ - θ₀|` for `|θ - θ₀| ≤ π`. -/
theorem chord_ge {θ θ₀ : ℝ} (ht : |θ - θ₀| ≤ π) :
    2 / π * |θ - θ₀| ≤ ‖circleMap 0 1 θ - circleMap 0 1 θ₀‖ := by
  have he : circleMap 0 1 θ - circleMap 0 1 θ₀ =
      Complex.exp (θ₀ * I) * (Complex.exp (I * ((θ - θ₀ : ℝ) : ℂ)) - 1) := by
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, mul_sub, mul_one,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  set x := θ - θ₀
  have hpi := Real.pi_pos
  rcases le_total 0 x with hx | hx
  · have h := Real.mul_le_sin (x := x / 2) (by linarith) (by rw [abs_of_nonneg hx] at ht; linarith)
    rw [abs_of_nonneg hx]
    have := le_abs_self (Real.sin (x / 2))
    have : 2 / π * x = 2 * (2 / π * (x / 2)) := by ring
    nlinarith
  · have h := Real.mul_le_sin (x := -x / 2) (by linarith)
      (by rw [abs_of_nonpos hx] at ht; linarith)
    rw [abs_of_nonpos hx]
    have h2 : Real.sin (-x / 2) = -Real.sin (x / 2) := by rw [neg_div, Real.sin_neg]
    have := neg_abs_le (Real.sin (x / 2))
    have : 2 / π * -x = 2 * (2 / π * (-x / 2)) := by ring
    nlinarith

/-- Radial kernel bound: `P(r e^{iθ₀}, e^{iθ}) ≤ 2π² (1-r) / max(1-r, |θ-θ₀|)²` for
`|θ - θ₀| ≤ π`. -/
theorem kernel_le_radial {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) {θ θ₀ : ℝ} (ht : |θ - θ₀| ≤ π) :
    poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ) ≤
      2 * π ^ 2 * (1 - r) / max (1 - r) |θ - θ₀| ^ 2 := by
  have hnz : ‖(r : ℂ) * circleMap 0 1 θ₀‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1, norm_circleMap_zero,
      abs_one, mul_one]
  rw [poissonKernel_circleMap, hnz]
  set D := ‖circleMap 0 1 θ - (r : ℂ) * circleMap 0 1 θ₀‖ with hD
  set d := ‖circleMap 0 1 θ - circleMap 0 1 θ₀‖ with hd
  have hD1 : 1 - r ≤ D := by
    have := norm_sub_norm_le (circleMap 0 1 θ) ((r : ℂ) * circleMap 0 1 θ₀)
    rwa [hnz, norm_circleMap_zero, abs_one] at this
  have hD2 : d ≤ D + (1 - r) := by
    have h := norm_sub_le_norm_sub_add_norm_sub (circleMap 0 1 θ) ((r : ℂ) * circleMap 0 1 θ₀)
      (circleMap 0 1 θ₀)
    have h2 : ‖(r : ℂ) * circleMap 0 1 θ₀ - circleMap 0 1 θ₀‖ = 1 - r := by
      rw [← sub_one_mul, norm_mul, norm_circleMap_zero, abs_one, mul_one, ← Complex.ofReal_one,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hr.2])]
      ring
    linarith
  have hchord := chord_ge ht
  have hpi := Real.pi_gt_three
  have hη : 0 < 1 - r := by linarith [hr.2]
  set m := max (1 - r) |θ - θ₀| with hm
  have hm0 : 0 < m := lt_of_lt_of_le hη (le_max_left _ _)
  have hmD : m ≤ π * D := by
    rw [hm, max_le_iff]
    constructor
    · nlinarith
    · have : 2 / π * |θ - θ₀| * π = 2 * |θ - θ₀| := by field_simp
      nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le hη hD1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 1 - r ^ 2 ≤ 2 * (1 - r) := by nlinarith [hr.1]
  have h2 : m ^ 2 ≤ π ^ 2 * D ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hm0.le hmD 2
  calc (1 - r ^ 2) * m ^ 2 ≤ (2 * (1 - r)) * (π ^ 2 * D ^ 2) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 2 * π ^ 2 * (1 - r) * D ^ 2 := by ring

/-- Dyadic decomposition of `min(1/η, η/t²)`. -/
theorem dyadic_aux {η t : ℝ} (hη : 0 < η) : ∀ N : ℕ, t ≤ 2 ^ N * η →
    ∃ k ≤ N, t ≤ 2 ^ k * η ∧ η / max η t ^ 2 ≤ 4 / ((2 ^ k) ^ 2 * η) := by
  intro N
  induction N with
  | zero =>
    intro h
    refine ⟨0, le_rfl, h, ?_⟩
    simp only [pow_zero, one_mul] at h ⊢
    rw [max_eq_left h, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  | succ n ih =>
    intro h
    by_cases h' : t ≤ 2 ^ n * η
    · obtain ⟨k, hk, hk'⟩ := ih h'
      exact ⟨k, hk.trans (Nat.le_succ n), hk'⟩
    · rw [not_le] at h'
      refine ⟨n + 1, le_rfl, h, ?_⟩
      have h2 : (0 : ℝ) < 2 ^ n * η := by positivity
      have hmt : 2 ^ n * η ≤ max η t := h'.le.trans (le_max_right _ _)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (2 ^ n * η) ^ 2 ≤ max η t ^ 2 := pow_le_pow_left₀ h2.le hmt 2
      have e : η * (((2 : ℝ) ^ (n + 1)) ^ 2 * η) = 4 * (2 ^ n * η) ^ 2 := by ring
      rw [e]
      linarith

/-- Main estimate for (D1): if `∫_{|t-θ₀|≤h} |ψ(e^{it}) - ψ(e^{iθ₀})| dt ≤ ε h` for `h ≤ δ`, then
`|P[ψ](r e^{iθ₀}) - ψ(e^{iθ₀})| ≤ π (8ε + (1-r) M / δ²)`, `M` the `L¹` distance on a period. -/
theorem poisson'_radial_est {ψ : ℂ → ℝ} (hψ : CircleIntegrable ψ 0 1) {θ₀ ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hF : ∀ h, 0 < h → h ≤ δ →
      ∫ t in closedBall θ₀ h, |ψ (circleMap 0 1 t) - ψ (circleMap 0 1 θ₀)| ≤ ε * h)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    |poisson' ψ (r * circleMap 0 1 θ₀) - ψ (circleMap 0 1 θ₀)| ≤
      π * (8 * ε + (1 - r) / δ ^ 2 *
        ∫ t in Ioc (θ₀ - π) (θ₀ + π), |ψ (circleMap 0 1 t) - ψ (circleMap 0 1 θ₀)|) := by
  set a := ψ (circleMap 0 1 θ₀) with ha
  set G : ℝ → ℝ := fun t => |ψ (circleMap 0 1 t) - a| with hG
  set S := Ioc (θ₀ - π) (θ₀ + π) with hS
  set M := ∫ t in S, G t with hM
  set η := 1 - r with hη
  have hη0 : 0 < η := by linarith [hr.2]
  have hpi := Real.pi_pos
  set z : ℂ := (r : ℂ) * circleMap 0 1 θ₀ with hz
  have hzd : z ∈ disc := by
    rw [mem_ball_zero_iff, hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1,
      norm_circleMap_zero, abs_one, mul_one]
    exact hr.2
  set K : ℝ → ℝ := fun θ => poissonKernel 0 z (circleMap 0 1 θ) with hK
  have hKc : Continuous K := continuous_kernel hzd
  have hK0 : ∀ θ, 0 ≤ K θ := kernel_nonneg hzd
  have hper : Periodic (fun t => ψ (circleMap 0 1 t)) (2 * π) := fun t => by
    simp only [periodic_circleMap 0 1 t]
  have hII : ∀ a b, IntervalIntegrable (fun t => ψ (circleMap 0 1 t)) volume a b :=
    hper.intervalIntegrable₀ Real.two_pi_pos.ne' hψ
  have hGII : ∀ a' b, IntervalIntegrable G volume a' b := fun a' b =>
    ((hII a' b).sub intervalIntegrable_const).abs
  have hloc : LocallyIntegrable G volume := fun x =>
    ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 (hGII _ _)⟩
  have hG0 : ∀ t, 0 ≤ G t := fun t => abs_nonneg _
  have hGS : IntegrableOn G S :=
    (hloc.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hKGS : IntegrableOn (fun θ => K θ * G θ) S :=
    ((hloc.integrableOn_isCompact isCompact_Icc).continuousOn_mul hKc.continuousOn
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  -- shift the period to `S`
  have h1 : |poisson' ψ z - a| ≤ (2 * π)⁻¹ * ∫ θ in S, K θ * G θ := by
    rw [poisson'_sub_eq hψ hzd a]
    have hFper : Periodic (fun θ => poissonKernel 0 z (circleMap 0 1 θ) *
        (ψ (circleMap 0 1 θ) - a)) (2 * π) := fun θ => by
      simp only [periodic_circleMap 0 1 θ]
    have h := hFper.intervalIntegral_add_eq 0 (θ₀ - π)
    rw [zero_add, show θ₀ - π + 2 * π = θ₀ + π by ring] at h
    rw [h, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hG, hK]
    rw [abs_mul, abs_of_nonneg (kernel_nonneg hzd θ)]
  -- dyadic majorant
  obtain ⟨N, hN⟩ : ∃ N : ℕ, δ ≤ 2 ^ N * η := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (δ / η) one_lt_two
    exact ⟨N, ((div_lt_iff₀ hη0).1 hN).le⟩
  set A : ℝ := 2 * π ^ 2 with hA
  set B : ℕ → Set ℝ := fun k => closedBall θ₀ (min (2 ^ k * η) δ) with hB
  set c : ℕ → ℝ := fun k => A * (4 / ((2 ^ k) ^ 2 * η)) with hc
  set bnd : ℝ → ℝ := fun θ =>
    (∑ k ∈ Finset.range (N + 1), c k * (B k).indicator G θ) + A * η / δ ^ 2 * G θ with hbnd
  have hc0 : ∀ k, 0 ≤ c k := fun k => by positivity
  have hpt : ∀ θ ∈ S, K θ * G θ ≤ bnd θ := by
    intro θ hθ
    have ht : |θ - θ₀| ≤ π := abs_sub_le_iff.2 ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have hKb : K θ ≤ A * η / max η |θ - θ₀| ^ 2 := kernel_le_radial hr ht
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range (N + 1), c k * (B k).indicator G θ :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (indicator_nonneg (fun t _ => hG0 t) θ)
    have hfar0 : 0 ≤ A * η / δ ^ 2 * G θ := mul_nonneg (by positivity) (hG0 θ)
    by_cases htδ : |θ - θ₀| ≤ δ
    · obtain ⟨k, hkN, htk, hk⟩ := dyadic_aux hη0 N (htδ.trans hN)
      have hθB : θ ∈ B k := by
        simp only [hB, mem_closedBall, Real.dist_eq]
        exact le_min htk htδ
      have hterm := Finset.single_le_sum (f := fun k => c k * (B k).indicator G θ)
        (fun k _ => mul_nonneg (hc0 k) (indicator_nonneg (fun t _ => hG0 t) θ))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hkN))
      simp only [indicator_of_mem hθB] at hterm
      have hKk : K θ ≤ c k := by
        calc K θ ≤ A * η / max η |θ - θ₀| ^ 2 := hKb
          _ = A * (η / max η |θ - θ₀| ^ 2) := by ring
          _ ≤ c k := mul_le_mul_of_nonneg_left hk (by positivity)
      calc K θ * G θ ≤ c k * G θ := mul_le_mul_of_nonneg_right hKk (hG0 θ)
        _ ≤ bnd θ := by simp only [hbnd]; linarith
    · rw [not_le] at htδ
      have hKf : K θ ≤ A * η / δ ^ 2 := by
        refine hKb.trans ?_
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hδ.le (htδ.le.trans (le_max_right _ _)) 2
      calc K θ * G θ ≤ A * η / δ ^ 2 * G θ := mul_le_mul_of_nonneg_right hKf (hG0 θ)
        _ ≤ bnd θ := by simp only [hbnd]; linarith
  have hind : ∀ k, Integrable ((B k).indicator G) (volume.restrict S) := fun k =>
    hGS.indicator measurableSet_closedBall
  have hbndI : IntegrableOn bnd S :=
    (integrable_finsetSum _ fun k _ => (hind k).const_mul (c k)).add (hGS.const_mul _)
  have hint : ∫ θ in S, bnd θ =
      (∑ k ∈ Finset.range (N + 1), c k * ∫ θ in S ∩ B k, G θ) + A * η / δ ^ 2 * M := by
    have hs : ∀ k ∈ Finset.range (N + 1), ∫ θ in S, c k * (B k).indicator G θ =
        c k * ∫ θ in S ∩ B k, G θ := fun k _ => by
      rw [integral_const_mul, setIntegral_indicator measurableSet_closedBall]
    simp only [hbnd]
    rw [integral_add (integrable_finsetSum _ fun k _ => (hind k).const_mul (c k))
      (hGS.const_mul _), integral_finsetSum _ (fun k _ => (hind k).const_mul (c k)),
      integral_const_mul, Finset.sum_congr rfl hs]
  have hBk : ∀ k, ∫ θ in S ∩ B k, G θ ≤ ε * (2 ^ k * η) := by
    intro k
    have hmin : 0 < min (2 ^ k * η) δ := lt_min (by positivity) hδ
    calc ∫ θ in S ∩ B k, G θ ≤ ∫ θ in B k, G θ :=
          setIntegral_mono_set (hloc.integrableOn_isCompact (isCompact_closedBall _ _))
            (Eventually.of_forall fun t => hG0 t) inter_subset_right.eventuallyLE
      _ ≤ ε * min (2 ^ k * η) δ := hF _ hmin (min_le_right _ _)
      _ ≤ ε * (2 ^ k * η) := mul_le_mul_of_nonneg_left (min_le_left _ _) hε
  have hsum : ∑ k ∈ Finset.range (N + 1), c k * ∫ θ in S ∩ B k, G θ ≤ A * (8 * ε) := by
    calc _ ≤ ∑ k ∈ Finset.range (N + 1), A * (4 * ε) * (1 / 2 : ℝ) ^ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          calc c k * ∫ θ in S ∩ B k, G θ ≤ c k * (ε * (2 ^ k * η)) :=
                mul_le_mul_of_nonneg_left (hBk k) (hc0 k)
            _ = A * (4 * ε) * (1 / 2 : ℝ) ^ k := by
                simp only [hc, one_div_pow]
                field_simp
      _ = A * (4 * ε) * ∑ k ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ A * (4 * ε) * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
      _ = A * (8 * ε) := by ring
  have hmain : ∫ θ in S, K θ * G θ ≤ A * (8 * ε) + A * η / δ ^ 2 * M := by
    calc ∫ θ in S, K θ * G θ ≤ ∫ θ in S, bnd θ :=
          setIntegral_mono_on hKGS hbndI measurableSet_Ioc hpt
      _ = _ := hint
      _ ≤ _ := add_le_add_left hsum _
  calc |poisson' ψ z - a| ≤ (2 * π)⁻¹ * ∫ θ in S, K θ * G θ := h1
    _ ≤ (2 * π)⁻¹ * (A * (8 * ε) + A * η / δ ^ 2 * M) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = π * (8 * ε + η / δ ^ 2 * M) := by
        simp only [hA]
        field_simp

/-- (D1) Fatou's theorem at a Lebesgue point of `g = ψ ∘ circleMap` (kernel bound
`kernel_le_radial`, dyadic majorant `dyadic_aux`, estimate `poisson'_radial_est`). -/
theorem poisson'_radial_tendsto_of_lebesgue {ψ : ℂ → ℝ} (hψ : CircleIntegrable ψ 0 1) {θ₀ : ℝ}
    (hθ₀ : Tendsto (fun h => ⨍ t in closedBall θ₀ h, |ψ (circleMap 0 1 t) - ψ (circleMap 0 1 θ₀)|)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => poisson' ψ (r * circleMap 0 1 θ₀)) (𝓝[<] 1)
      (𝓝 (ψ (circleMap 0 1 θ₀))) := by
  set a := ψ (circleMap 0 1 θ₀) with ha
  set M := ∫ t in Ioc (θ₀ - π) (θ₀ + π), |ψ (circleMap 0 1 t) - a| with hM
  have hM0 : 0 ≤ M := setIntegral_nonneg measurableSet_Ioc fun t _ => abs_nonneg _
  have hpi := Real.pi_pos
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hev := hθ₀.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (32 * π) by positivity))
  obtain ⟨δ', hδ', hδ'sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  set δ := min (δ' / 2) π with hδdef
  have hδ : 0 < δ := lt_min (by linarith [hδ'.out]) hpi
  have hF : ∀ h, 0 < h → h ≤ δ →
      ∫ t in closedBall θ₀ h, |ψ (circleMap 0 1 t) - a| ≤ ε / (16 * π) * h := by
    intro h hh hhδ
    have hin : h ∈ Ioo 0 δ' :=
      ⟨hh, by linarith [min_le_left (δ' / 2) π, hδ'.out]⟩
    have h2 := hδ'sub hin
    simp only [Set.mem_ofPred_eq] at h2
    rw [setAverage_eq, Real.volume_real_closedBall hh.le, smul_eq_mul,
      inv_mul_lt_iff₀ (by positivity)] at h2
    have : 2 * h * (ε / (32 * π)) = ε / (16 * π) * h := by field_simp; ring
    linarith
  refine ⟨min 1 (ε * δ ^ 2 / (2 * π * (M + 1))), by positivity, fun r hr hrd => ?_⟩
  have hr1 : r < 1 := hr
  rw [Real.dist_eq, abs_sub_lt_iff] at hrd
  have hρ1 := min_le_left 1 (ε * δ ^ 2 / (2 * π * (M + 1)))
  have hρ2 := min_le_right 1 (ε * δ ^ 2 / (2 * π * (M + 1)))
  have hr0 : 0 ≤ r := by linarith
  have hest := poisson'_radial_est hψ (by positivity : (0 : ℝ) ≤ ε / (16 * π)) hδ hF ⟨hr0, hr1⟩
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hest ?_
  have hη : (1 - r) * (2 * π * (M + 1)) < ε * δ ^ 2 :=
    (lt_div_iff₀ (by positivity)).1 (by linarith)
  have h3 : π * ((1 - r) / δ ^ 2 * M) < ε / 2 := by
    rw [div_mul_eq_mul_div, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have h4 : π * (8 * (ε / (16 * π))) = ε / 2 := by field_simp; ring
  linarith [mul_add π (8 * (ε / (16 * π))) ((1 - r) / δ ^ 2 * M)]

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
