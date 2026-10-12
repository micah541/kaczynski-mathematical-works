import Mathlib
import TJK.Defs
import TJK.Plane.Basic
import TJK.Baire.Sphere
import TJK.BoundaryFn.Fsigma
import TJK.Harmonic.Example

/-!
# Asymptotic values of harmonic functions with bounded `p`-means (blueprint §H)

Source: Kaczynski, Trans. AMS 137 (1969), Theorem and Corollaries. We prove

* `thm:ha-theorem` (`isMeagre_asymptotic_diff_generalLimit'`, the pinned statement);
* `cor:ha-corollary` (`isMeagre_discontinuity_boundaryFn`);
* `cor:ha-analytic` (`isMeagre_asymptotic_diff_generalLimit_holomorphic`),

from `fact:poisson` (ii), (iii), `cor:bf-honorary` and the Baire–Kuratowski theorem.
-/

namespace TJK.Harmonic

open _root_.Set Filter Topology Metric Function MeasureTheory Complex
open scoped Real

/-- A radial limit is a limit along an arc: the radius `[0, x]`. -/
theorem radial_arc {Y : Type*} [TopologicalSpace Y] {x : ℂ} (hx : x ∈ circle) {f : ℂ → Y}
    {L : Y} (h : Tendsto (fun r : ℝ => f (r * x)) (𝓝[<] 1) (𝓝 L)) :
    ∃ γ, IsArcAt disc x γ ∧ Tendsto f (𝓝[γ \ {x}] x) (𝓝 L) := by
  have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
  have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hx1; exact zero_ne_one hx1
  let q : Path x 0 :=
    { toFun := fun t => ((1 - (t : ℝ) : ℝ) : ℂ) * x
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hq_inj : Injective q := by
    intro a b hab
    have : ((1 - (a : ℝ) : ℝ) : ℂ) * x = ((1 - (b : ℝ) : ℝ) : ℂ) * x := hab
    have := mul_right_cancel₀ hx0 this
    have := Complex.ofReal_injective this
    exact Subtype.ext (by linarith)
  refine ⟨range q, ⟨0, ⟨q, hq_inj, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨⟨t, rfl⟩, hne⟩
    have ht0 : (t : ℝ) ≠ 0 := fun h0 => hne (by
      rw [mem_singleton_iff]; show ((1 - (t : ℝ) : ℝ) : ℂ) * x = x; rw [h0]; simp)
    have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
    show ((1 - (t : ℝ) : ℝ) : ℂ) * x ∈ disc
    rw [mem_ball_zero_iff, norm_mul, hx1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [t.2.2])]
    linarith
  · rw [IsArc.nhdsWithin_eq hq_inj, tendsto_map'_iff]
    have h1 : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] 0) (𝓝[<] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 (1 - 0)) :=
          (continuous_const.sub continuous_id).tendsto 0
        rw [sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        show 1 - t < 1
        linarith [mem_Ioi.1 ht]
    refine (h.comp h1).congr' ?_
    filter_upwards [Ioc_mem_nhdsGT one_pos] with t ht
    simp only [comp_apply]
    rw [Path.extend_apply q (Ioc_subset_Icc_self ht)]
    rfl

/-- Countable sets on the circle have measure zero. -/
theorem ae_circleMap_notMem {T : Set ℂ} (hT : T.Countable) :
    ∀ᵐ θ, circleMap 0 1 θ ∉ T := by
  have hc : (circleMap 0 1 ⁻¹' T).Countable := by
    rw [← biUnion_preimage_singleton]
    refine hT.biUnion fun p _ => ?_
    by_cases h : ∃ θ₀, circleMap 0 1 θ₀ = p
    · obtain ⟨θ₀, rfl⟩ := h
      refine (countable_range (fun k : ℤ => θ₀ + k * (2 * π))).mono ?_
      intro θ hθ
      simp only [mem_preimage, mem_singleton_iff] at hθ
      have : expI θ = expI θ₀ := by simpa [circleMap, expI] using hθ
      obtain ⟨k, hk⟩ := expI_eq_expI_iff.1 this
      exact ⟨k, hk.symm⟩
    · push Not at h
      convert countable_empty
      ext θ
      simp [h θ]
  exact measure_eq_zero_iff_ae_notMem.1 (hc.measure_zero volume)

/-- `thm:ha-theorem`: for a harmonic function with bounded `p`-th integral means (`p > 1`), the
points of the circle with an asymptotic value but no general limit form a set of the first
category. Same statement as the pinned `TJK.Harmonic.isMeagre_asymptotic_diff_generalLimit`. -/
theorem isMeagre_asymptotic_diff_generalLimit' (u : ℂ → ℝ)
    (hu : InnerProductSpace.HarmonicOnNhd u disc) (p : ℝ) (hp : 1 < p)
    (hmean : ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
      ∫ θ in (0 : ℝ)..(2 * Real.pi), |u (r * Complex.exp (θ * Complex.I))| ^ p ≤ B) :
    IsMeagre ((Subtype.val : circle → ℂ) ⁻¹'
      (curvConvSet disc circle u \ {ζ | ∃ L, Tendsto u (𝓝[disc] ζ) (𝓝 L)})) := by
  obtain ⟨ψ, hψ, hrad, hP⟩ := hp_radial_limit_poisson u hu p hp hmean
  set A := curvConvSet disc circle u with hAdef
  set S := {x : ℂ | x ∈ circle ∧ Tendsto (fun r : ℝ => u (r * x)) (𝓝[<] 1) (𝓝 (ψ x))} with hSdef
  have hSA : S ⊆ A := fun x hx => by
    obtain ⟨γ, hγ, hl⟩ := radial_arc hx.1 hx.2
    exact ⟨hx.1, γ, hγ, ψ x, hl⟩
  have hAc : A ⊆ circle := fun x hx => hx.1
  classical
  -- a boundary function on `A` extending the radial limits
  let φ₁ : ℂ → ℝ := fun x => if x ∈ S then ψ x else
    if h : x ∈ A then h.2.choose_spec.2.choose else 0
  have hφ₁ : IsBoundaryFunction disc u A φ₁ := by
    intro x hx
    by_cases hxS : x ∈ S
    · obtain ⟨γ, hγ, hl⟩ := radial_arc hxS.1 hxS.2
      refine ⟨γ, hγ, ?_⟩
      simp only [φ₁, if_pos hxS]
      exact hl
    · refine ⟨hx.2.choose, hx.2.choose_spec.1, ?_⟩
      simp only [φ₁, if_neg hxS, dif_pos hx]
      exact hx.2.choose_spec.2.choose_spec
  obtain ⟨N, hNc, g, hg, hNg⟩ :=
    BoundaryFn.isHonoraryBaireTwo_disc_real' u hu.continuousOn A hAc φ₁ hφ₁
  -- the modified boundary data `Φ = g` on `A`, `ψ` elsewhere
  let Φ : ℂ → ℝ := fun z => if h : z ∈ A then g ⟨z, h⟩ else ψ z
  have hae : ∀ᵐ θ, Φ (circleMap 0 1 θ) = ψ (circleMap 0 1 θ) := by
    filter_upwards [hrad, ae_circleMap_notMem (hNc.image Subtype.val)] with θ h1 h2
    have hS : circleMap 0 1 θ ∈ S := ⟨circleMap_mem_sphere 0 zero_le_one θ, h1⟩
    have hA := hSA hS
    have hN : (⟨circleMap 0 1 θ, hA⟩ : A) ∉ N := fun h => h2 ⟨_, h, rfl⟩
    simp only [Φ, dif_pos hA]
    rw [← hNg _ hN]
    exact if_pos hS
  have hΦint : CircleIntegrable Φ 0 1 := by
    unfold CircleIntegrable
    exact IntervalIntegrable.congr_ae hψ (ae_restrict_of_ae (hae.mono fun θ h => h.symm))
  have huΦ : ∀ z ∈ disc, u z = poisson Φ z := by
    intro z hz
    rw [hP z hz, poisson, poisson, Real.circleAverage_def, Real.circleAverage_def]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with θ h _
    rw [h]
  have hfull : ∀ᵐ θ, circleMap 0 1 θ ∈ A :=
    hrad.mono fun θ h => hSA ⟨circleMap_mem_sphere 0 zero_le_one θ, h⟩
  have key : ∀ y : A, ContinuousAt g y → ∃ L, Tendsto u (𝓝[disc] (y : ℂ)) (𝓝 L) := by
    intro y hy
    refine ⟨Φ y, ?_⟩
    have hc : ContinuousWithinAt Φ (A ∩ circle) y := by
      rw [inter_eq_left.2 hAc, continuousWithinAt_iff_continuousAt_domRestrict Φ y.2]
      have : A.domRestrict Φ = g := funext fun z => by
        simp [Φ, domRestrict, z.2]
      rw [this]
      exact hy
    have := poisson_tendsto_of_continuousAt Φ hΦint A hfull ⟨y.2, hAc y.2⟩ hc
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using (huΦ z hz).symm
  -- transport to the circle
  let E' : Set circle := Subtype.val ⁻¹' A
  let j : E' → A := fun y => ⟨y.1.1, y.2⟩
  let e : A → E' := fun y => ⟨⟨y.1, hAc y.2⟩, y.2⟩
  have hj : Continuous j := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he : Continuous e := (continuous_subtype_val.subtype_mk _).subtype_mk _
  have hm := isMeagre_of_isMeagre_subtype (hg.comp_continuous hj).meagre_discontinuity
  refine hm.mono ?_
  rintro x ⟨hxA, hxG⟩
  refine ⟨⟨x, hxA⟩, fun hcont => hxG ?_, rfl⟩
  have h2 : ContinuousAt ((g ∘ j) ∘ e) ⟨x.1, hxA⟩ := ContinuousAt.comp hcont he.continuousAt
  exact key ⟨x.1, hxA⟩ h2

/-- At a point with a general limit, a boundary function is continuous (relative to its set). -/
theorem continuousWithinAt_of_generalLimit {u : ℂ → ℝ} {E : Set ℂ} {φ : ℂ → ℝ}
    (hφ : IsBoundaryFunction disc u E φ) {x : ℂ} (hx : x ∈ E) {L : ℝ}
    (hL : Tendsto u (𝓝[disc] x) (𝓝 L)) : ContinuousWithinAt φ E x := by
  have hlim : ∀ y ∈ E, ∀ γ, IsArcAt disc y γ → 𝓝[γ \ {y}] y ≤ 𝓝[disc] y := by
    intro y _ γ hγ
    obtain ⟨_, _, hsub⟩ := hγ
    exact nhdsWithin_mono _ hsub
  have hφx : φ x = L := by
    obtain ⟨γ, hγ, hl⟩ := hφ x hx
    have := hγ.nhdsWithin_neBot
    exact tendsto_nhds_unique hl (hL.mono_left (hlim x hx γ hγ))
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.tendsto_nhdsWithin_nhds.1 hL (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun y hy hyx => ?_⟩
  obtain ⟨γ, hγ, hl⟩ := hφ y hy
  have := hγ.nhdsWithin_neBot
  have hev : ∀ᶠ z in 𝓝[γ \ {y}] y, dist (u z) L ≤ ε / 2 := by
    have h1 : ball x δ ∈ 𝓝[γ \ {y}] y :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (by rwa [mem_ball]))
    have h2 : disc ∈ 𝓝[γ \ {y}] y := hlim y hy γ hγ self_mem_nhdsWithin
    filter_upwards [h1, h2] with z hz1 hz2
    exact (hδu hz2 hz1).le
  have : dist (φ y) L ≤ ε / 2 :=
    le_of_tendsto ((continuous_id.dist continuous_const).tendsto (φ y) |>.comp hl) hev
  rw [hφx]
  linarith

/-- `cor:ha-corollary`: under the hypothesis of `thm:ha-theorem`, the discontinuities of a boundary
function `φ` on `E ⊆ C` (relative to `E`) form a set of the first category. -/
theorem isMeagre_discontinuity_boundaryFn (u : ℂ → ℝ)
    (hu : InnerProductSpace.HarmonicOnNhd u disc) (p : ℝ) (hp : 1 < p)
    (hmean : ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
      ∫ θ in (0 : ℝ)..(2 * Real.pi), |u (r * Complex.exp (θ * Complex.I))| ^ p ≤ B)
    (E : Set ℂ) (hE : E ⊆ circle) (φ : ℂ → ℝ) (hφ : IsBoundaryFunction disc u E φ) :
    IsMeagre ((Subtype.val : circle → ℂ) ⁻¹' {x | x ∈ E ∧ ¬ ContinuousWithinAt φ E x}) := by
  refine (isMeagre_asymptotic_diff_generalLimit' u hu p hp hmean).mono ?_
  rintro x ⟨hxE, hxc⟩
  obtain ⟨γ, hγ, hl⟩ := hφ x hxE
  refine ⟨⟨hE hxE, γ, hγ, φ x, hl⟩, ?_⟩
  rintro ⟨L, hL⟩
  exact hxc (continuousWithinAt_of_generalLimit hφ hxE hL)

/-- `cor:ha-analytic`: `thm:ha-theorem` and `cor:ha-corollary` for holomorphic functions with
bounded `p`-means, `p > 1`. -/
theorem isMeagre_asymptotic_diff_generalLimit_holomorphic (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F disc) (p : ℝ) (hp : 1 < p)
    (hmean : ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖F (r * Complex.exp (θ * Complex.I))‖ ^ p ≤ B) :
    IsMeagre ((Subtype.val : circle → ℂ) ⁻¹'
      (curvConvSet disc circle F \ {ζ | ∃ L, Tendsto F (𝓝[disc] ζ) (𝓝 L)})) ∧
    ∀ E ⊆ circle, ∀ φ : ℂ → ℂ, IsBoundaryFunction disc F E φ →
      IsMeagre ((Subtype.val : circle → ℂ) ⁻¹' {x | x ∈ E ∧ ¬ ContinuousWithinAt φ E x}) := by
  have han : ∀ x ∈ disc, AnalyticAt ℂ F x := fun x hx =>
    hF.analyticAt (isOpen_ball.mem_nhds hx)
  have hre : InnerProductSpace.HarmonicOnNhd (fun z => (F z).re) disc := fun x hx =>
    (han x hx).harmonicAt_re
  have him : InnerProductSpace.HarmonicOnNhd (fun z => (F z).im) disc := fun x hx =>
    (han x hx).harmonicAt_im
  obtain ⟨B, hB⟩ := hmean
  have hcont : ∀ r ∈ Ico (0 : ℝ) 1,
      Continuous fun θ : ℝ => F (r * Complex.exp (θ * Complex.I)) := by
    intro r hr
    refine hF.continuousOn.comp_continuous (by fun_prop) fun θ => ?_
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2
  have hp0 : 0 ≤ p := by linarith
  have hmean' : ∀ (h : ℂ → ℝ), (∀ w, |h w| ≤ ‖w‖) → Continuous h →
      ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
        ∫ θ in (0 : ℝ)..(2 * Real.pi), |h (F (r * Complex.exp (θ * Complex.I)))| ^ p ≤ B := by
    intro h hh hhc
    refine ⟨B, fun r hr => le_trans ?_ (hB r hr)⟩
    refine intervalIntegral.integral_mono_on Real.two_pi_pos.le ?_ ?_ fun θ _ =>
      Real.rpow_le_rpow (abs_nonneg _) (hh _) hp0
    · exact (((hhc.comp (hcont r hr)).abs).rpow_const fun _ => Or.inr hp0).intervalIntegrable _ _
    · exact (((hcont r hr).norm).rpow_const fun _ => Or.inr hp0).intervalIntegrable _ _
  have hmre := hmean' Complex.re Complex.abs_re_le_norm continuous_re
  have hmim := hmean' Complex.im Complex.abs_im_le_norm continuous_im
  constructor
  · refine ((isMeagre_asymptotic_diff_generalLimit' _ hre p hp hmre).union
      (isMeagre_asymptotic_diff_generalLimit' _ him p hp hmim)).mono ?_
    rintro x ⟨⟨hxc, γ, hγ, q, hq⟩, hxG⟩
    by_contra hcon
    simp only [mem_union, mem_preimage, mem_diff, mem_ofPred_eq, not_or, not_and,
      not_not] at hcon
    obtain ⟨a, ha⟩ := hcon.1 ⟨hxc, γ, hγ, q.re, (continuous_re.tendsto q).comp hq⟩
    obtain ⟨b, hb⟩ := hcon.2 ⟨hxc, γ, hγ, q.im, (continuous_im.tendsto q).comp hq⟩
    apply hxG
    refine ⟨a + b * I, ?_⟩
    have := ((continuous_ofReal.tendsto a).comp ha).add
      (((continuous_ofReal.tendsto b).comp hb).mul_const I)
    simpa [comp_def, Complex.re_add_im] using this
  · intro E hE φ hφ
    have hφre : IsBoundaryFunction disc (fun z => (F z).re) E (fun z => (φ z).re) := by
      intro x hx
      obtain ⟨γ, hγ, hl⟩ := hφ x hx
      exact ⟨γ, hγ, (continuous_re.tendsto _).comp hl⟩
    have hφim : IsBoundaryFunction disc (fun z => (F z).im) E (fun z => (φ z).im) := by
      intro x hx
      obtain ⟨γ, hγ, hl⟩ := hφ x hx
      exact ⟨γ, hγ, (continuous_im.tendsto _).comp hl⟩
    refine ((isMeagre_discontinuity_boundaryFn _ hre p hp hmre E hE _ hφre).union
      (isMeagre_discontinuity_boundaryFn _ him p hp hmim E hE _ hφim)).mono ?_
    rintro x ⟨hxE, hxc⟩
    by_contra hcon
    simp only [mem_union, mem_preimage, mem_ofPred_eq, not_or, not_and, not_not] at hcon
    apply hxc
    have h1 := hcon.1 hxE
    have h2 := hcon.2 hxE
    have hφe : φ = fun z => ((φ z).re : ℂ) + ((φ z).im : ℂ) * I :=
      funext fun z => (re_add_im _).symm
    rw [hφe]
    exact (continuous_ofReal.continuousAt.comp_continuousWithinAt h1).add
      ((continuous_ofReal.continuousAt.comp_continuousWithinAt h2).mul continuousWithinAt_const)

end TJK.Harmonic
