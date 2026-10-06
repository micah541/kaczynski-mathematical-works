import Mathlib
import TJK.Defs
import TJK.Baire.Basic
import TJK.Construct.Regions
import TJK.Construct.G
import TJK.Plane.Basic

/-!
# Realizing `F_σδ` sets as sets of curvilinear convergence (blueprint `thm:cc-realize`)

Dissertation Theorem 4: for every `F_σδ` set `A ⊆ ℝ` there is a bounded continuous `f` on `ℍ` with
`CC(f) = A`. Following the blueprint, `A' = Ψ_ℍ⁻¹(A) ⊆ X`, `g` is the function of
`thm:construct-A` (`exists_g`) for `A'`, `f₀ = g sin(1/y) + i g` on `Q°`, and
`f = f₀ ∘ Ψ_ℍ⁻¹`; `CC(f₀) = A'` and `lem:transfer` gives `CC(f) = A`.
-/

namespace TJK.Construct

open _root_.Set Filter Topology Metric Real

/-- `f₀ = g sin(1/y) + i g`. -/
noncomputable def fZero (g : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((g z * Real.sin (1 / z.im) : ℝ) : ℂ) + ((g z : ℝ) : ℂ) * Complex.I

@[simp] theorem fZero_re (g : ℂ → ℝ) (z : ℂ) : (fZero g z).re = g z * Real.sin (1 / z.im) := by
  simp only [fZero, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]; ring

@[simp] theorem fZero_im (g : ℂ → ℝ) (z : ℂ) : (fZero g z).im = g z := by
  simp only [fZero, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]; ring

theorem norm_fZero_le {g : ℂ → ℝ} {z : ℂ} (hz : 0 ≤ g z) : ‖fZero g z‖ ≤ 2 * g z := by
  calc ‖fZero g z‖ ≤ ‖((g z * Real.sin (1 / z.im) : ℝ) : ℂ)‖ + ‖((g z : ℝ) : ℂ) * Complex.I‖ :=
        norm_add_le _ _
    _ = |g z| * |Real.sin (1 / z.im)| + |g z| := by
        simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    _ ≤ |g z| * 1 + |g z| := by gcongr; exact Real.abs_sin_le_one _
    _ = 2 * g z := by rw [abs_of_nonneg hz]; ring

theorem openSquare_subset_upper : openSquare ⊆ upper := fun _ hz => hz.2.1

/-- Along an arc at a real point in a subset of `ℍ`, every small height is attained in every
member of the punctured neighbourhood filter. -/
theorem IsArcAt.exists_im_eq {Ω : Set ℂ} (hΩ : Ω ⊆ upper) {x : ℂ} (hx : x.im = 0) {γ : Set ℂ}
    (h : IsArcAt Ω x γ) {S : Set ℂ} (hS : S ∈ 𝓝[γ \ {x}] x) :
    ∃ y₀ > 0, ∀ y ∈ Ioc 0 y₀, ∃ z ∈ S, z.im = y := by
  obtain ⟨U, hUo, hxU, hUS⟩ := mem_nhdsWithin.1 hS
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo x hxU
  obtain ⟨C, hCγ, hC, hCb, hxC⟩ := h.exists_tail hr
  have hCS : C ⊆ S := fun z hz => hUS ⟨hball (hCb hz), hCγ hz⟩
  have hCup : ∀ z ∈ C, 0 < z.im := fun z hz => by
    obtain ⟨b, -, hsub⟩ := h
    exact hΩ (hsub (hCγ hz))
  obtain ⟨z₀, hz₀⟩ : C.Nonempty := closure_nonempty_iff.1 ⟨_, hxC⟩
  refine ⟨z₀.im, hCup z₀ hz₀, fun y hy => ?_⟩
  have h0 : (0 : ℝ) ∈ closure (Complex.im '' C) := by
    have := mem_closure_image Complex.continuous_im.continuousAt hxC
    rwa [hx] at this
  obtain ⟨_, ⟨w, hw, rfl⟩, hwd⟩ := Metric.mem_closure_iff.1 h0 y hy.1
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (hCup w hw)] at hwd
  obtain ⟨z, hz, hzy⟩ := (hC.image _ Complex.continuous_im.continuousOn).Icc_subset
    ⟨w, hw, rfl⟩ ⟨z₀, hz₀, rfl⟩ ⟨hwd.le, hy.2⟩
  exact ⟨z, hCS hz, hzy⟩

/-- The heart of `thm:cc-realize`: `CC(f₀) = A'` in `Q°` relative to `X`. -/
theorem curvConvSet_fZero {A' : Set ℝ} {g : ℂ → ℝ} (hgI : MapsTo g upper (Icc 0 1))
    (ha : ∀ x ∈ A', Tendsto g (𝓝[stolz x 1 (3 * π / 8)] (x : ℂ)) (𝓝 0))
    (hb : ∀ (x : ℝ) (γ : Set ℂ), IsArcAt upper (x : ℂ) γ →
      Tendsto g (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) → x ∈ A') :
    curvConvSet openSquare baseX (fZero g) = {z | z ∈ baseX ∧ z.re ∈ A'} := by
  ext z
  constructor
  · rintro ⟨hzB, γ, hγ, q, hq⟩
    obtain ⟨x, rfl⟩ : ∃ x : ℝ, (x : ℂ) = z :=
      ⟨z.re, Complex.ext (by simp) (by simp [hzB.2])⟩
    refine ⟨hzB, ?_⟩
    rw [Complex.ofReal_re]
    have hγ' : IsArcAt upper (x : ℂ) γ := by
      obtain ⟨b, hb', hsub⟩ := hγ
      exact ⟨b, hb', hsub.trans openSquare_subset_upper⟩
    have him : Tendsto g (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 q.im) := by
      have := (Complex.continuous_im.tendsto q).comp hq
      exact this.congr fun w => by simp
    have hre : Tendsto (fun w => g w * Real.sin (1 / w.im)) (𝓝[γ \ {(x : ℂ)}] (x : ℂ))
        (𝓝 q.re) := by
      have := (Complex.continuous_re.tendsto q).comp hq
      exact this.congr fun w => by simp
    have hd : q.im = 0 := by
      by_contra hd
      have hdpos : 0 < |q.im| := abs_pos.2 hd
      have hS : {w | |g w - q.im| < |q.im| / 4 ∧
          |g w * Real.sin (1 / w.im) - q.re| < |q.im| / 4} ∈ 𝓝[γ \ {(x : ℂ)}] (x : ℂ) := by
        have h1 := Metric.tendsto_nhds.1 him _ (by positivity : 0 < |q.im| / 4)
        have h2 := Metric.tendsto_nhds.1 hre _ (by positivity : 0 < |q.im| / 4)
        filter_upwards [h1, h2] with w hw1 hw2
        exact ⟨by rwa [Real.dist_eq] at hw1, by rwa [Real.dist_eq] at hw2⟩
      obtain ⟨y₀, hy₀, hy⟩ := IsArcAt.exists_im_eq openSquare_subset_upper
        (Complex.ofReal_im x) hγ hS
      obtain ⟨n, hn⟩ := exists_nat_gt ((1 / y₀ + π / 2) / (2 * π) + 1)
      have hpi := Real.pi_pos
      have hn' : 1 / y₀ + π / 2 < 2 * π * n := by
        have h1 : (1 / y₀ + π / 2) / (2 * π) < n := by linarith
        rw [div_lt_iff₀ (by positivity)] at h1
        linarith
      have hy₀' : 0 < 1 / y₀ := by positivity
      have hpos2 : 0 < 2 * π * n - π / 2 := by linarith
      have hy2le : 1 / (2 * π * n - π / 2) ≤ y₀ := by
        rw [div_le_iff₀ hpos2]
        have : 1 / y₀ * y₀ = 1 := by field_simp
        nlinarith
      have hy1le : 1 / (π / 2 + 2 * π * n) ≤ y₀ :=
        le_trans (one_div_le_one_div_of_le hpos2 (by linarith)) hy2le
      obtain ⟨z1, ⟨h1a, h1b⟩, hz1⟩ := hy _ ⟨by positivity, hy1le⟩
      obtain ⟨z2, ⟨h2a, h2b⟩, hz2⟩ := hy _ ⟨by positivity, hy2le⟩
      have hs1 : Real.sin (1 / z1.im) = 1 := by
        rw [hz1, one_div_one_div, show π / 2 + 2 * π * n = π / 2 + n * (2 * π) by ring,
          Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
      have hs2 : Real.sin (1 / z2.im) = -1 := by
        rw [hz2, one_div_one_div, show 2 * π * n - π / 2 = -(π / 2) + n * (2 * π) by ring,
          Real.sin_add_nat_mul_two_pi, Real.sin_neg, Real.sin_pi_div_two]
      rw [hs1, mul_one] at h1b
      rw [hs2, mul_neg_one] at h2b
      rw [abs_lt] at h1a h1b h2a h2b
      rcases le_total 0 q.im with h | h
      · rw [abs_of_nonneg h] at h1a h1b h2a h2b hdpos
        linarith [h1a.1, h1a.2, h1b.1, h1b.2, h2a.1, h2a.2, h2b.1, h2b.2]
      · rw [abs_of_nonpos h] at h1a h1b h2a h2b hdpos
        linarith [h1a.1, h1a.2, h1b.1, h1b.2, h2a.1, h2a.2, h2b.1, h2b.2]
    exact hb x γ hγ' (hd ▸ him)
  · rintro ⟨hzB, hzA⟩
    obtain ⟨x, rfl⟩ : ∃ x : ℝ, (x : ℂ) = z :=
      ⟨z.re, Complex.ext (by simp) (by simp [hzB.2])⟩
    rw [Complex.ofReal_re] at hzA
    have hxI : x ∈ Ioo (-1 : ℝ) 1 := by
      have := hzB.1; rwa [Complex.ofReal_re] at this
    -- the vertical segment from `x` to `x + i/2`
    let P : Path (x : ℂ) ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) :=
      ⟨⟨fun s => (x : ℂ) + (((s : ℝ) / 2 : ℝ) : ℂ) * Complex.I, by fun_prop⟩, by simp,
        by simp⟩
    have hPim : ∀ s : unitInterval, (P s).im = (s : ℝ) / 2 := fun s => by
      simp [P]
    have hPre : ∀ s : unitInterval, (P s).re = x := fun s => by
      simp [P]
    have hPinj : Function.Injective P := fun s t hst => by
      have := congrArg Complex.im hst
      rw [hPim, hPim] at this
      exact Subtype.ext (by linarith)
    have hsub : range P \ {(x : ℂ)} ⊆ stolz x 1 (3 * π / 8) ∩ openSquare := by
      rintro _ ⟨⟨s, rfl⟩, hs⟩
      have hs0 : (0 : ℝ) < s := by
        refine lt_of_le_of_ne s.2.1 fun h0 => hs ?_
        have : s = 0 := Subtype.ext h0.symm
        rw [this, mem_singleton_iff, P.source]
      have hcot : 0 < cot (3 * π / 8) :=
        cot_pos_of_lt_pi_div_two (by positivity) (by linarith [Real.pi_pos])
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hPim]; positivity
      · rw [hPim]; linarith [s.2.2]
      · rw [hPre, hPim, sub_self, abs_zero]; positivity
      · rw [hPre]; exact hxI
      · rw [hPim]; constructor <;> linarith [s.2.2]
    have harc : IsArcAt openSquare (x : ℂ) (range P) :=
      ⟨_, ⟨P, hPinj, rfl⟩, fun w hw => (hsub hw).2⟩
    refine ⟨hzB, range P, harc, 0, ?_⟩
    have hg0 : Tendsto g (𝓝[range P \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) :=
      (ha x hzA).mono_left (nhdsWithin_mono _ fun w hw => (hsub hw).1)
    refine squeeze_zero_norm' ?_ (by simpa using hg0.const_mul 2)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact norm_fZero_le (hgI (openSquare_subset_upper (hsub hw).2)).1

/-- Dissertation Theorem 4 (blueprint `thm:cc-realize`): every `F_σδ` subset of `ℝ` is the set of
curvilinear convergence of a bounded continuous function in the upper half-plane. -/
theorem exists_curvConvSet_eq_upperHalfPlane' (A : Set ℝ) (hA : IsFσδ A) :
    ∃ f : ℂ → ℂ, ContinuousOn f upper ∧ Bornology.IsBounded (f '' upper) ∧
      curvConvSet upper realAxis f = ((↑) : ℝ → ℂ) '' A := by
  set A' : Set ℝ := {u | u ∈ Ioo (-1) 1 ∧ Real.tan (π * u / 2) ∈ A} with hA'def
  have hA'X : A' ⊆ Ioo (-1) 1 := fun u hu => hu.1
  have hA' : IsFσδ A' := by
    let T : Ioo (-1 : ℝ) 1 → ℝ := fun u => Real.tan (π * u / 2)
    have hT : Continuous T :=
      Real.continuousOn_tan_Ioo.comp_continuous (by fun_prop) fun u => pi_mul_div_two_mem u.2
    have h1 : IsFσδ (T ⁻¹' A) := hA.preimage hT
    have h2 : IsFσδ (Ioo (-1 : ℝ) 1) := (IsOpen.isFσ isOpen_Ioo).isFσδ
    have := h2.of_subtype h1
    convert this using 1
    ext u
    constructor
    · rintro ⟨hu, huA⟩; exact ⟨⟨u, hu⟩, huA, rfl⟩
    · rintro ⟨⟨u, hu⟩, huA, rfl⟩; exact ⟨hu, huA⟩
  obtain ⟨g, hgc, hgI, ha, hb⟩ := exists_g hA' hA'X
  have hmaps : MapsTo chartHPH.symm upper openSquare := chartH_isChart.symm.mapsTo
  have hf0 : ContinuousOn (fZero g) openSquare := by
    have hgc' := hgc.mono openSquare_subset_upper
    have hsin : ContinuousOn (fun z : ℂ => Real.sin (1 / z.im)) openSquare :=
      Real.continuous_sin.comp_continuousOn
        (ContinuousOn.div continuousOn_const Complex.continuous_im.continuousOn
          fun z hz => (openSquare_subset_upper hz).ne')
    exact (Complex.continuous_ofReal.comp_continuousOn (hgc'.mul hsin)).add
      ((Complex.continuous_ofReal.comp_continuousOn hgc').mul continuousOn_const)
  refine ⟨fZero g ∘ chartHPH.symm, ?_, ?_, ?_⟩
  · exact hf0.comp (chartHPH.continuousOn_symm.mono chartH_isChart.symm.subset_source) hmaps
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff]
    have hgw := hgI (openSquare_subset_upper (hmaps hw))
    exact (norm_fZero_le hgw.1).trans (by linarith [hgw.2])
  · rw [transfer_curvConvSet chartH_isChart.symm, curvConvSet_fZero hgI ha hb]
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, chartHPH_symm_apply, mem_image]
    constructor
    · rintro ⟨hz, -, hzA⟩
      refine ⟨z.re, ?_, Complex.ext (by simp) (by simp [hz])⟩
      rw [chartHInv_re] at hzA
      have := hzA.2
      rwa [tan_pi_mul_two_div_pi_mul_arctan] at this
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Complex.ofReal_im x, ⟨?_, ?_⟩, ?_⟩
      · rw [chartHInv_re]; exact two_div_pi_mul_arctan_mem _
      · rw [chartHInv_im, Complex.ofReal_im, zero_div]
      · rw [chartHInv_re, Complex.ofReal_re]
        exact ⟨two_div_pi_mul_arctan_mem _, by rwa [tan_pi_mul_two_div_pi_mul_arctan]⟩

end TJK.Construct
