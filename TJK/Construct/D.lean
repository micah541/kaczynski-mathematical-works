import Mathlib
import TJK.Defs
import TJK.Construct.Regions
import TJK.Construct.G
import TJK.Construct.H
import TJK.Construct.K

/-!
# The function `f` on the square (blueprint §F, `thm:construct-D`)

For an `F_σδ` set `A ⊆ (-1, 1)` and a bounded `φ : A → ℂ` of honorary Baire class `≤ 2` we
construct `f = h + g k`, continuous and bounded on `Q = [-1, 1] × (0, 1]`, whose set of
curvilinear convergence in `Q° = (-1, 1) × (0, 1)` (relative to `X = (-1, 1) × {0}`) is `A`, and
which has `φ` as a boundary function. Here `g`, `h`, `k` are the functions of `thm:construct-A`
(`exists_g`), `thm:construct-B` (`exists_h_bounded`, transported to `ℂ ≅ ℝ²` in
`exists_h_complex`) and `thm:construct-C` (`exists_k`).

The modulus `d` is `d(t) = min (D(t/2)/4) (t/4)`, where `D(t)` is the supremum of the
`δ ∈ (0, 1]` that are moduli of uniform continuity, with tolerance `t`, of both `h` and `g` on
`[-1, 1] × [t, 1]`.

General facts proved here: `exists_exit_Icc` (the exit argument of `lem:subarc`(b) for a path
starting far away) and `exists_segArc` (a short segment of slope `c` at `x ∈ (-1, 1)` is an arc in
`Q°`, along which limits are limits in the height).
-/

namespace TJK.Construct

open _root_.Set Metric Real Filter Topology

/-- Exit argument: if `F` is continuous and `F 0` is at distance `≥ ρ > 0` from `F t₀`, there
is `s ∈ [0, t₀]` such that `F([s, t₀])` lies in the closed ball of radius `ρ` about `F t₀` and
`F s` is at distance `≥ ρ` from `F t₀`. -/
theorem exists_exit_Icc {E : Type*} [PseudoMetricSpace E] {F : ℝ → E} (hF : Continuous F)
    {t₀ ρ : ℝ} (ht₀ : 0 ≤ t₀) (hρ : 0 < ρ) (h0 : ρ ≤ dist (F 0) (F t₀)) :
    ∃ s ∈ Icc 0 t₀, F '' Icc s t₀ ⊆ closedBall (F t₀) ρ ∧ ρ ≤ dist (F s) (F t₀) := by
  set S := Icc 0 t₀ ∩ {t | ρ ≤ dist (F t) (F t₀)} with hS
  have hSc : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le continuous_const (hF.dist continuous_const))
  obtain ⟨s, ⟨hsI, hsρ⟩, hsmax⟩ := hSc.exists_isMaxOn ⟨0, ⟨le_rfl, ht₀⟩, h0⟩
    continuous_id.continuousOn
  have hst : s < t₀ := by
    refine lt_of_le_of_ne hsI.2 fun h => ?_
    rw [h, mem_ofPred_eq, dist_self] at hsρ
    linarith
  have hlt : F '' Ioc s t₀ ⊆ closedBall (F t₀) ρ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_closedBall]
    by_contra hc
    push Not at hc
    have := hsmax ⟨⟨hsI.1.trans ht.1.le, ht.2⟩, hc.le⟩
    simp only [mem_ofPred_eq, id] at this
    linarith [ht.1]
  refine ⟨s, hsI, ?_, hsρ⟩
  rintro _ ⟨t, ht, rfl⟩
  rcases ht.1.eq_or_lt with h | h
  · subst h
    have hcl : s ∈ closure (Ioc s t₀) := by
      rw [closure_Ioc hst.ne]; exact ⟨le_rfl, hst.le⟩
    exact closure_minimal hlt isClosed_closedBall (mem_closure_image hF.continuousAt hcl)
  · exact hlt ⟨t, ⟨h, ht.2⟩, rfl⟩

/-- A short segment of slope `|c| < √2 - 1` at `x ∈ (-1, 1)` is an arc at `x` in `Q°` inside the
Stolz angle `s(x, 1, 3π/8)`, and a limit along `y ↦ seg x c y` as `y → 0⁺` is a limit along the
arc. -/
theorem exists_segArc {x c : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hc : |c| < √2 - 1) :
    ∃ γ : Set ℂ, IsArcAt {z : ℂ | |z.re| < 1 ∧ 0 < z.im ∧ z.im < 1} (x : ℂ) γ ∧
      γ \ {(x : ℂ)} ⊆ stolz x 1 (3 * π / 8) ∧
      ∀ (F : ℂ → ℂ) (L : ℂ), Tendsto (fun y => F (seg x c y)) (𝓝[>] 0) (𝓝 L) →
        Tendsto F (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 L) := by
  have hx' : |x| < 1 := abs_lt.2 hx
  have hc1 : |c| < 1 := by
    have : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  set y₁ : ℝ := min (1 / 2) ((1 - |x|) / 2) with hy₁
  have hy₁pos : 0 < y₁ := lt_min (by norm_num) (by linarith)
  let P : Path (x : ℂ) (seg x c y₁) :=
    ⟨⟨fun t => seg x c (y₁ * (t : ℝ)), by unfold seg; fun_prop⟩, by simp [seg], by simp⟩
  have hPim : ∀ t : unitInterval, (P t).im = y₁ * t := fun t => by simp [P]
  have hPseg : ∀ t : unitInterval, P t = seg x c (P t).im := fun t => by rw [hPim]; rfl
  have hPinj : Function.Injective P := fun s t hst => by
    have := congrArg Complex.im hst
    rw [hPim, hPim] at this
    exact Subtype.ext (mul_left_cancel₀ hy₁pos.ne' this)
  have hmem : ∀ z ∈ range P \ {(x : ℂ)}, 0 < z.im ∧ z.im ≤ y₁ ∧ seg x c z.im = z := by
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    have ht0 : (0 : ℝ) < t := by
      refine lt_of_le_of_ne t.2.1 fun h0 => ht ?_
      have : t = 0 := Subtype.ext h0.symm
      rw [this, mem_singleton_iff, P.source]
    rw [hPim]
    exact ⟨mul_pos hy₁pos ht0, mul_le_of_le_one_right hy₁pos.le t.2.2, by rw [← hPim, ← hPseg]⟩
  have hsub : range P \ {(x : ℂ)} ⊆ stolz x 1 (3 * π / 8) := fun z hz => by
    obtain ⟨h0, h1, h2⟩ := hmem z hz
    rw [← h2]
    exact seg_mem_stolz hc h0 (by linarith [min_le_left (1 / 2 : ℝ) ((1 - |x|) / 2)])
  refine ⟨range P, ⟨_, ⟨P, hPinj, rfl⟩, fun z hz => ?_⟩, hsub, fun F L hF => ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hmem z hz
    have h3 := min_le_left (1 / 2 : ℝ) ((1 - |x|) / 2)
    have h4 := min_le_right (1 / 2 : ℝ) ((1 - |x|) / 2)
    refine ⟨?_, h0, by linarith⟩
    rw [← h2, seg_re]
    calc |x + c * z.im| ≤ |x| + |c| * z.im := by
          refine (abs_add_le _ _).trans (le_of_eq ?_); rw [abs_mul, abs_of_pos h0]
      _ ≤ |x| + 1 * z.im := by gcongr
      _ < 1 := by linarith
  · have him : Tendsto Complex.im (𝓝[range P \ {(x : ℂ)}] (x : ℂ)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (eventually_nhdsWithin_of_forall fun z hz => (hmem z hz).1)
      have := (Complex.continuous_im.tendsto (x : ℂ)).mono_left
        (nhdsWithin_le_nhds (s := range P \ {(x : ℂ)}))
      rwa [Complex.ofReal_im] at this
    refine (hF.comp him).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    simp only [Function.comp_apply, (hmem z hz).2.2]

/-- `thm:construct-B` for `ℂ`-valued `φ`, via `ℂ ≅ ℝ²`: a bounded `h`, continuous on `ℍ`, with
`h → φ(p)` along a segment of slope `|c| < √2 - 1` at each `p ∈ E`. -/
theorem exists_h_complex {E : Set ℝ} (hE : E ⊆ Ioo (-1) 1) {φ : ℝ → ℂ}
    (hφ : IsHonoraryBaireTwo (E.restrict φ)) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ p ∈ E, ‖φ p‖ ≤ B) :
    ∃ h : ℂ → ℂ, ContinuousOn h upper ∧ (∀ z, ‖h z‖ ≤ 2 * B) ∧
      ∀ p ∈ E, ∃ c : ℝ, |c| < √2 - 1 ∧
        Tendsto (fun y => h (seg p c y)) (𝓝[>] 0) (𝓝 (φ p)) := by
  let e : ℂ → (Fin 2 → ℝ) := fun z i => if i = 0 then z.re else z.im
  let e' : (Fin 2 → ℝ) → ℂ := fun v => (v 0 : ℂ) + (v 1 : ℂ) * Complex.I
  have he : Continuous e := continuous_pi fun i => by
    by_cases hi : i = 0
    · simp only [e, hi, if_true]; fun_prop
    · simp only [e, hi, if_false]; fun_prop
  have he' : Continuous e' := by fun_prop
  have hee : ∀ z, e' (e z) = z := fun z => by
    apply Complex.ext <;> simp [e, e']
  have hne : ∀ z, ‖e z‖ ≤ ‖z‖ := fun z => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    by_cases hi : i = 0
    · simp only [e, hi, if_true, Real.norm_eq_abs]; exact Complex.abs_re_le_norm z
    · simp only [e, hi, if_false, Real.norm_eq_abs]; exact Complex.abs_im_le_norm z
  have hne' : ∀ v, ‖e' v‖ ≤ 2 * ‖v‖ := fun v => by
    have h0 := norm_le_pi_norm v 0
    have h1 := norm_le_pi_norm v 1
    calc ‖e' v‖ ≤ ‖(v 0 : ℂ)‖ + ‖(v 1 : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = ‖v 0‖ + ‖v 1‖ := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
      _ ≤ 2 * ‖v‖ := by linarith
  have hφ' : IsHonoraryBaireTwo (E.restrict (e ∘ φ)) := by
    obtain ⟨N, hN, g, ⟨F, hFc, hFl⟩, hfg⟩ := hφ
    refine ⟨N, hN, e ∘ g, ⟨fun n => e ∘ F n, fun n => he.comp (hFc n),
      fun x => (he.tendsto _).comp (hFl x)⟩, fun x hx => ?_⟩
    exact congrArg e (hfg x hx)
  obtain ⟨h, hc, hb, hl⟩ := exists_h_bounded hE hφ' hB0 (fun p hp => (hne _).trans (hB p hp))
  refine ⟨e' ∘ h, he'.comp_continuousOn hc, fun z => (hne' _).trans (by linarith [hb z]),
    fun p hp => ?_⟩
  obtain ⟨c, hc, ht⟩ := hl p hp
  refine ⟨c, hc, ?_⟩
  have := (he'.tendsto _).comp ht
  simp only [Function.comp_apply, hee] at this
  exact this

/-- The modulus `d` of `thm:construct-D`: positive, weakly increasing, `d(a) ≤ a/4`, and points
of `[-1, 1] × [a/2, 1]` at distance `≤ 2 d(a)` have `h`- and `g`-values within `a/2`. -/
theorem exists_modulus {V : Type*} [PseudoMetricSpace V] {h : ℂ → V} {g : ℂ → ℝ}
    (hh : ContinuousOn h upper) (hg : ContinuousOn g upper) :
    ∃ d : ℝ → ℝ, (∀ t ∈ Ioc (0 : ℝ) 1, 0 < d t) ∧ MonotoneOn d (Ioc 0 1) ∧
      (∀ t ∈ Ioc (0 : ℝ) 1, d t ≤ t / 4) ∧
      ∀ a ∈ Ioc (0 : ℝ) 1, ∀ z₁ ∈ {z : ℂ | |z.re| ≤ 1 ∧ a / 2 ≤ z.im ∧ z.im ≤ 1},
        ∀ z₂ ∈ {z : ℂ | |z.re| ≤ 1 ∧ a / 2 ≤ z.im ∧ z.im ≤ 1}, dist z₁ z₂ ≤ 2 * d a →
          dist (h z₁) (h z₂) ≤ a / 2 ∧ dist (g z₁) (g z₂) ≤ a / 2 := by
  set K : ℝ → Set ℂ := fun t => {z : ℂ | |z.re| ≤ 1 ∧ t ≤ z.im ∧ z.im ≤ 1} with hK
  have hKc : ∀ t, IsCompact (K t) := fun t => by
    have : K t = Icc (-1) 1 ×ℂ Icc t 1 := by
      ext z; simp [K, Complex.mem_reProdIm, abs_le]
    rw [this]; exact isCompact_Icc.reProdIm isCompact_Icc
  have hKup : ∀ t, 0 < t → K t ⊆ upper := fun t ht z hz => ht.trans_le hz.2.1
  have hKmono : ∀ t t', t ≤ t' → K t' ⊆ K t := fun t t' htt z hz =>
    ⟨hz.1, htt.trans hz.2.1, hz.2.2⟩
  set P : ℝ → ℝ → Prop := fun t δ => ∀ z₁ ∈ K t, ∀ z₂ ∈ K t, dist z₁ z₂ < δ →
    dist (h z₁) (h z₂) ≤ t ∧ dist (g z₁) (g z₂) ≤ t with hP
  have hPex : ∀ t, 0 < t → ∃ δ > 0, P t δ := fun t ht => by
    obtain ⟨δ₁, hδ₁, h1⟩ := Metric.uniformContinuousOn_iff.1
      ((hKc t).uniformContinuousOn_of_continuous (hh.mono (hKup t ht))) t ht
    obtain ⟨δ₂, hδ₂, h2⟩ := Metric.uniformContinuousOn_iff.1
      ((hKc t).uniformContinuousOn_of_continuous (hg.mono (hKup t ht))) t ht
    exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z₁ hz₁ z₂ hz₂ hd =>
      ⟨(h1 z₁ hz₁ z₂ hz₂ (hd.trans_le (min_le_left _ _))).le,
        (h2 z₁ hz₁ z₂ hz₂ (hd.trans_le (min_le_right _ _))).le⟩⟩
  have hPmono : ∀ t t' δ δ', t ≤ t' → δ' ≤ δ → P t δ → P t' δ' :=
    fun t t' δ δ' htt hδ hPt z₁ hz₁ z₂ hz₂ hd => by
      obtain ⟨h1, h2⟩ := hPt z₁ (hKmono t t' htt hz₁) z₂ (hKmono t t' htt hz₂) (hd.trans_le hδ)
      exact ⟨h1.trans htt, h2.trans htt⟩
  set S : ℝ → Set ℝ := fun t => {δ | δ ∈ Ioc (0 : ℝ) 1 ∧ P t δ} with hS
  have hSne : ∀ t, 0 < t → (S t).Nonempty := fun t ht => by
    obtain ⟨δ, hδ, hPt⟩ := hPex t ht
    exact ⟨min δ 1, ⟨lt_min hδ one_pos, min_le_right _ _⟩,
      hPmono t t δ _ le_rfl (min_le_left _ _) hPt⟩
  have hSbdd : ∀ t, BddAbove (S t) := fun t => ⟨1, fun δ hδ => hδ.1.2⟩
  set D : ℝ → ℝ := fun t => sSup (S t) with hD
  have hDpos : ∀ t, 0 < t → 0 < D t := fun t ht => by
    obtain ⟨δ, hδ⟩ := hSne t ht
    exact hδ.1.1.trans_le (le_csSup (hSbdd t) hδ)
  have hDmono : ∀ t t', 0 < t → t ≤ t' → D t ≤ D t' := fun t t' ht htt =>
    csSup_le_csSup (hSbdd t') (hSne t ht) fun δ hδ => ⟨hδ.1, hPmono t t' δ δ htt le_rfl hδ.2⟩
  have hDP : ∀ t, 0 < t → ∀ δ, δ < D t → P t δ := fun t ht δ hδ => by
    obtain ⟨δ', hδ', hlt⟩ := exists_lt_of_lt_csSup (hSne t ht) hδ
    exact hPmono t t δ' δ le_rfl hlt.le hδ'.2
  refine ⟨fun t => min (D (t / 2) / 4) (t / 4), fun t ht => ?_, fun t ht t' ht' htt => ?_,
    fun t _ => min_le_right _ _, fun a ha z₁ hz₁ z₂ hz₂ hd => ?_⟩
  · exact lt_min (by linarith [hDpos (t / 2) (by linarith [ht.1])]) (by linarith [ht.1])
  · have := hDmono (t / 2) (t' / 2) (by linarith [ht.1]) (by linarith)
    exact min_le_min (by linarith) (by linarith)
  · have ha2 : 0 < a / 2 := by linarith [ha.1]
    have hDa := hDpos (a / 2) ha2
    refine hDP (a / 2) ha2 (3 * D (a / 2) / 4) (by linarith) z₁ hz₁ z₂ hz₂ ?_
    have := min_le_left (D (a / 2) / 4) (a / 4)
    linarith

/-- `thm:construct-D`: for `A ⊆ (-1, 1)` of class `F_σδ` and `φ : A → ℂ` bounded and of honorary
Baire class `≤ 2` there is `f`, continuous and bounded on `Q = [-1, 1] × (0, 1]`, whose set of
curvilinear convergence in `Q° = (-1, 1) × (0, 1)` relative to `X = (-1, 1) × {0}` is `A`, and
having `φ` as a boundary function on `A`. -/
theorem exists_f_Q {A : Set ℝ} (hA : IsFσδ A) (hAX : A ⊆ Ioo (-1) 1) {φ : ℝ → ℂ}
    (hφb : ∃ B, ∀ x ∈ A, ‖φ x‖ ≤ B) (hφ : IsHonoraryBaireTwo (A.restrict φ)) :
    ∃ f : ℂ → ℂ, ContinuousOn f {z | |z.re| ≤ 1 ∧ 0 < z.im ∧ z.im ≤ 1} ∧
      Bornology.IsBounded (f '' {z | |z.re| ≤ 1 ∧ 0 < z.im ∧ z.im ≤ 1}) ∧
      curvConvSet {z : ℂ | |z.re| < 1 ∧ 0 < z.im ∧ z.im < 1} (((↑) : ℝ → ℂ) '' Ioo (-1) 1) f =
        ((↑) : ℝ → ℂ) '' A ∧
      IsBoundaryFunction {z : ℂ | |z.re| < 1 ∧ 0 < z.im ∧ z.im < 1} f (((↑) : ℝ → ℂ) '' A)
        (fun z => φ z.re) := by
  obtain ⟨B, hB⟩ := hφb
  obtain ⟨h, hhc, hhb, hhl⟩ := exists_h_complex hAX hφ (le_max_right B 0)
    (fun p hp => (hB p hp).trans (le_max_left _ _))
  obtain ⟨g, hgc, hgI, hga, hgb⟩ := exists_g hA hAX
  obtain ⟨d, hdpos, hdmono, hdle, hdmod⟩ := exists_modulus hhc hgc
  obtain ⟨k, hkc, hkb, hk⟩ := exists_k hdpos hdmono
  set Qo : Set ℂ := {z : ℂ | |z.re| < 1 ∧ 0 < z.im ∧ z.im < 1} with hQo
  have hQoup : Qo ⊆ upper := fun z hz => hz.2.1
  set f : ℂ → ℂ := fun z => h z + (g z : ℂ) * k z with hf
  have hsqrt : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  -- the boundary function
  have hbf : ∀ x ∈ A, ∃ γ, IsArcAt Qo (x : ℂ) γ ∧
      Tendsto f (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 (φ x)) := fun x hx => by
    obtain ⟨c, hc, hlim⟩ := hhl x hx
    obtain ⟨γ, hγ, hγs, hγt⟩ := exists_segArc (hAX hx) hc
    refine ⟨γ, hγ, ?_⟩
    have h1 := hγt h (φ x) hlim
    have h2 : Tendsto g (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) :=
      (hga x hx).mono_left (nhdsWithin_mono _ hγs)
    have h3 : Tendsto (fun z => (g z : ℂ) * k z) (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) := by
      refine Tendsto.zero_mul_isBoundedUnder_le ?_ (isBoundedUnder_of ⟨√2, fun z => hkb z⟩)
      have := (Complex.continuous_ofReal.tendsto 0).comp h2
      rw [Complex.ofReal_zero] at this
      exact this
    simpa [f] using h1.add h3
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · -- continuity
    have hQup : {z : ℂ | |z.re| ≤ 1 ∧ 0 < z.im ∧ z.im ≤ 1} ⊆ upper := fun z hz => hz.2.1
    exact (hhc.mono hQup).add ((Complex.continuous_ofReal.comp_continuousOn (hgc.mono hQup)).mul
      (hkc.mono fun z hz => hz.2))
  · -- boundedness
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := 2 * max B 0 + √2)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_closedBall_zero_iff]
    have hgz := hgI hz.2.1
    calc ‖h z + (g z : ℂ) * k z‖ ≤ ‖h z‖ + |g z| * ‖k z‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * max B 0 + 1 * √2 := by
          gcongr
          · exact hhb z
          · rw [abs_of_nonneg hgz.1]; exact hgz.2
          · exact hkb z
      _ = 2 * max B 0 + √2 := by ring
  · ext z
    constructor
    · rintro ⟨⟨x, hxI, rfl⟩, γ, hγ, q, hq⟩
      refine ⟨x, hgb x γ ⟨hγ.choose, hγ.choose_spec.1, hγ.choose_spec.2.trans hQoup⟩ ?_, rfl⟩
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      set ε₁ := min ε 1 with hε₁
      have hε₁pos : 0 < ε₁ := lt_min hε one_pos
      have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
      obtain ⟨r, hr, hrq⟩ := Metric.tendsto_nhdsWithin_nhds.1 hq (ε₁ / 2) (by linarith)
      refine ⟨min (r / 2) (3 * ε₁ / 16), lt_min (by linarith) (by linarith),
        fun z₀ hz₀ hz₀x => ?_⟩
      have hz₀Q : z₀ ∈ Qo := hγ.choose_spec.2 hz₀
      have hgz₀ := hgI (hQoup hz₀Q)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hgz₀.1]
      refine lt_of_lt_of_le ?_ (min_le_left ε 1)
      by_contra hge
      push Not at hge
      -- the height `y` of `z₀` and the scale `a = 4y/3`
      set y := z₀.im with hy
      have hy0 : 0 < y := hz₀Q.2.1
      have hyx : y ≤ dist z₀ x := by
        have := Complex.abs_im_le_norm (z₀ - x)
        rw [← dist_eq_norm, Complex.sub_im, Complex.ofReal_im, sub_zero] at this
        exact (le_abs_self _).trans this
      have hyr : y < r / 2 := hyx.trans_lt (hz₀x.trans_le (min_le_left _ _))
      have hyε : y < 3 * ε₁ / 16 := hyx.trans_lt (hz₀x.trans_le (min_le_right _ _))
      set a := 4 * y / 3 with ha
      have haI : a ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
      have hda := hdpos a haI
      have hdle' : d a ≤ y / 3 := by linarith [hdle a haI]
      -- the exit argument
      obtain ⟨b, ⟨P, hPinj, hPr⟩, hγQ⟩ := hγ
      have hz₀γ := hz₀.1
      rw [← hPr] at hz₀γ
      obtain ⟨t₀, rfl⟩ := hz₀γ
      have hF0 : P.extend 0 = (x : ℂ) := P.extend_zero
      have hFt : P.extend t₀ = P t₀ := P.extend_extends' t₀
      obtain ⟨s, hs, hsub, hsρ⟩ := exists_exit_Icc P.continuous_extend t₀.2.1 hda
        (by rw [hF0, hFt, dist_comm]; linarith)
      rw [hFt] at hsub hsρ
      set C := P.extend '' Icc s t₀ with hC
      have hCγ : C ⊆ γ := by
        rw [← hPr, ← P.extend_range]; exact image_subset_range _ _
      have hCd : ∀ w ∈ C, dist w (P t₀) ≤ y / 3 := fun w hw => (hsub hw).trans hdle'
      have hCim : ∀ w ∈ C, a / 2 ≤ w.im ∧ w.im ≤ a := fun w hw => by
        have h1 := Complex.abs_im_le_norm (w - P t₀)
        rw [← dist_eq_norm, Complex.sub_im] at h1
        have h2 := (h1.trans (hCd w hw))
        rw [abs_le] at h2
        constructor <;> linarith [h2.1, h2.2]
      have hCx : ∀ w ∈ C, w ≠ (x : ℂ) := fun w hw h => by
        have := (hCim w hw).1
        rw [h, Complex.ofReal_im] at this
        linarith
      have hCQ : ∀ w ∈ C, w ∈ Qo := fun w hw => hγQ ⟨hCγ hw, hCx w hw⟩
      have hz₀C : P t₀ ∈ C := ⟨t₀, ⟨hs.2, le_rfl⟩, hFt⟩
      obtain ⟨p, hp, p', hp', hkpp⟩ := hk a haI C
        (isPreconnected_Icc.image _ P.continuous_extend.continuousOn)
        (fun w hw => ⟨(hCQ w hw).1.le, (hCQ w hw).2.1, (hCim w hw).2⟩)
        ⟨P.extend s, ⟨s, ⟨le_rfl, hs.2⟩, rfl⟩, P t₀, hz₀C, hsρ⟩
      -- the estimates
      have hCK : ∀ w ∈ C, w ∈ {z : ℂ | |z.re| ≤ 1 ∧ a / 2 ≤ z.im ∧ z.im ≤ 1} := fun w hw =>
        ⟨(hCQ w hw).1.le, (hCim w hw).1, (hCQ w hw).2.2.le⟩
      have hd1 : dist p p' ≤ 2 * d a := by
        have := dist_triangle_right p p' (P t₀)
        linarith [mem_closedBall.1 (hsub hp), mem_closedBall.1 (hsub hp')]
      have hd2 : ∀ w ∈ C, dist w (P t₀) ≤ 2 * d a := fun w hw => by
        have := mem_closedBall.1 (hsub hw); linarith
      have hhpp := (hdmod a haI p (hCK p hp) p' (hCK p' hp') hd1).1
      have hgp := (hdmod a haI p (hCK p hp) _ (hCK _ hz₀C) (hd2 p hp)).2
      have hgp' := (hdmod a haI p' (hCK p' hp') _ (hCK _ hz₀C) (hd2 p' hp')).2
      have hfar : ∀ w ∈ C, dist (f w) q < ε₁ / 2 := fun w hw => by
        refine hrq ⟨hCγ hw, hCx w hw⟩ ?_
        have := dist_triangle w (P t₀) x
        linarith [hCd w hw, hz₀x.trans_le (min_le_left _ _)]
      have hfpp : ‖f p - f p'‖ < ε₁ := by
        have := dist_triangle_right (f p) (f p') q
        rw [dist_eq_norm] at this
        linarith [hfar p hp, hfar p' hp']
      rw [Real.dist_eq] at hgp hgp'
      rw [dist_eq_norm] at hhpp
      set G := g (P t₀) with hG
      have key : (G : ℂ) * (k p - k p') = (f p - f p') - (h p - h p')
          - ((g p : ℂ) - G) * k p + ((g p' : ℂ) - G) * k p' := by
        simp only [f]; ring
      have hnorm : G * ‖k p - k p'‖ ≤ ‖f p - f p'‖ + ‖h p - h p'‖ + |g p - G| * √2
          + |g p' - G| * √2 := by
        have e1 : ‖(G : ℂ) * (k p - k p')‖ = G * ‖k p - k p'‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgz₀.1]
        have e2 : ‖((g p : ℂ) - G) * k p‖ ≤ |g p - G| * √2 := by
          rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hkb p) (abs_nonneg _)
        have e3 : ‖((g p' : ℂ) - G) * k p'‖ ≤ |g p' - G| * √2 := by
          rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hkb p') (abs_nonneg _)
        rw [← e1, key]
        refine (norm_add_le _ _).trans ?_
        refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
        refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
        linarith
      have h2 : 2 * ε₁ ≤ G * ‖k p - k p'‖ := by
        have := mul_le_mul hge hkpp zero_le_two hgz₀.1
        linarith
      have hsq0 : 0 ≤ √2 := Real.sqrt_nonneg 2
      have h3 : |g p - G| * √2 ≤ a / 2 * (3 / 2) := by
        exact mul_le_mul hgp hsqrt.le hsq0 (by linarith)
      have h4 : |g p' - G| * √2 ≤ a / 2 * (3 / 2) := by
        exact mul_le_mul hgp' hsqrt.le hsq0 (by linarith)
      linarith
    · rintro ⟨x, hxA, rfl⟩
      obtain ⟨γ, hγ, hlim⟩ := hbf x hxA
      exact ⟨⟨x, hAX hxA, rfl⟩, γ, hγ, φ x, hlim⟩
  · rintro _ ⟨x, hxA, rfl⟩
    simp only [Complex.ofReal_re]
    exact hbf x hxA

end TJK.Construct
