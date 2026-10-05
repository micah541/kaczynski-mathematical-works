import Mathlib
import TJK.Defs

/-!
# Monotone left inverses, a closed-graph criterion, and the function `k` (blueprint §F)

Formalizes `lem:monotone-inverse`, `lem:closed-graph` and `thm:construct-C` of
`paper/sections/F-construct.tex`.

Points `⟨x, y⟩` of the plane are complex numbers `z` with `x = z.re`, `y = z.im`. The function
`d : (0, 1] → (0, ∞)` of `thm:construct-C` is a function `ℝ → ℝ` whose hypotheses are only
imposed on `(0, 1]`.
-/

open Set Filter Topology Real

namespace TJK.Construct

/-! ### `lem:monotone-inverse` -/

/-- `lem:monotone-inverse` (a): a strictly increasing `f : (-1, 1) → ℝ` has a continuous weakly
increasing left inverse `f* : ℝ → [-1, 1]`. -/
theorem exists_monotone_leftInverse {f : ℝ → ℝ} (hf : StrictMonoOn f (Ioo (-1) 1)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Monotone g ∧ (∀ t, g t ∈ Icc (-1 : ℝ) 1) ∧
      ∀ x ∈ Ioo (-1 : ℝ) 1, g (f x) = x := by
  set S : ℝ → Set ℝ := fun t => insert (-1) {x | x ∈ Ioo (-1 : ℝ) 1 ∧ f x ≤ t} with hS
  have hne : ∀ t, (S t).Nonempty := fun t => ⟨-1, mem_insert _ _⟩
  have hub : ∀ t, ∀ x ∈ S t, x ≤ 1 := by
    rintro t x (rfl | ⟨hx, -⟩)
    · norm_num
    · exact hx.2.le
  have hbdd : ∀ t, BddAbove (S t) := fun t => ⟨1, hub t⟩
  set g : ℝ → ℝ := fun t => sSup (S t) with hg
  have hmem : ∀ t, g t ∈ Icc (-1 : ℝ) 1 := fun t =>
    ⟨le_csSup (hbdd t) (mem_insert _ _), csSup_le (hne t) (hub t)⟩
  have hmono : Monotone g := by
    intro s t hst
    refine csSup_le_csSup (hbdd t) (hne s) ?_
    rintro x (rfl | ⟨hx, hfx⟩)
    · exact mem_insert _ _
    · exact Or.inr ⟨hx, hfx.trans hst⟩
  have hinv : ∀ x ∈ Ioo (-1 : ℝ) 1, g (f x) = x := by
    intro x hx
    refine IsGreatest.csSup_eq ⟨Or.inr ⟨hx, le_rfl⟩, ?_⟩
    rintro y (rfl | ⟨hy, hfy⟩)
    · exact hx.1.le
    · exact (hf.le_iff_le hy hx).1 hfy
  refine ⟨g, ?_, hmono, hmem, hinv⟩
  let G : ℝ → Icc (-1 : ℝ) 1 := fun t => ⟨g t, hmem t⟩
  have hG : Monotone G := fun s t hst => hmono hst
  have : Nontrivial (Icc (-1 : ℝ) 1) :=
    ⟨⟨⟨-1, by norm_num⟩, ⟨1, by norm_num⟩, by simp [Subtype.ext_iff]; norm_num⟩⟩
  have hdense : DenseRange G := by
    refine dense_of_exists_between fun a b hab => ?_
    have hab' : (a : ℝ) < b := hab
    have hc : ((a : ℝ) + b) / 2 ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [a.2.1], by linarith [b.2.2]⟩
    refine ⟨G (f (((a : ℝ) + b) / 2)), mem_range_self _, ?_, ?_⟩
    · change (a : ℝ) < g (f _)
      rw [hinv _ hc]; linarith
    · change g (f _) < (b : ℝ)
      rw [hinv _ hc]; linarith
  exact continuous_subtype_val.comp (hG.continuous_of_denseRange hdense)

/-- `lem:monotone-inverse` (b): a strictly increasing `f : ℝ → ℝ` whose range is unbounded above
and below has a continuous weakly increasing left inverse. -/
theorem exists_monotone_leftInverse_real {f : ℝ → ℝ} (hf : StrictMono f)
    (hab : ¬BddAbove (range f)) (hbb : ¬BddBelow (range f)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Monotone g ∧ ∀ x, g (f x) = x := by
  set S : ℝ → Set ℝ := fun t => {x | f x ≤ t} with hS
  have hne : ∀ t, (S t).Nonempty := by
    intro t
    by_contra h
    refine hbb ⟨t, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_contra hx
    exact h ⟨x, (not_le.1 hx).le⟩
  have hbdd : ∀ t, BddAbove (S t) := by
    intro t
    have : ∃ x, t < f x := by
      by_contra h
      push Not at h
      exact hab ⟨t, by rintro _ ⟨x, rfl⟩; exact h x⟩
    obtain ⟨x₀, hx₀⟩ := this
    refine ⟨x₀, fun x hx => ?_⟩
    exact (hf.le_iff_le).1 ((show f x ≤ t from hx).trans hx₀.le)
  set g : ℝ → ℝ := fun t => sSup (S t) with hg
  have hmono : Monotone g := fun s t hst =>
    csSup_le_csSup (hbdd t) (hne s) fun x (hx : f x ≤ s) => show f x ≤ t from hx.trans hst
  have hinv : ∀ x, g (f x) = x := fun x =>
    IsGreatest.csSup_eq ⟨show f x ≤ f x from le_rfl, fun y (hy : f y ≤ f x) => hf.le_iff_le.1 hy⟩
  exact ⟨g, hmono.continuous_of_surjective fun x => ⟨f x, hinv x⟩, hmono, hinv⟩

/-! ### `lem:closed-graph` -/

/-- `lem:closed-graph`: if `u(pₙ) → y` in `[-∞, ∞]` along every convergent sequence `pₙ → p`
forces `y = u(p)` (in particular `y` is finite), then `u` is continuous. Stated for sequential
spaces, which include metric spaces. -/
theorem continuous_of_closedGraph {M : Type*} [TopologicalSpace M] [SequentialSpace M]
    {u : M → ℝ}
    (h : ∀ (p : ℕ → M) (x : M) (y : EReal), Tendsto p atTop (𝓝 x) →
      Tendsto (fun n => (u (p n) : EReal)) atTop (𝓝 y) → y = (u x : EReal)) :
    Continuous u := by
  rw [continuous_iff_seqContinuous]
  intro p x hp
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨y, -, φ, hφ, hy⟩ :=
    isCompact_univ.tendsto_subseq (x := fun n => (u (p (ns n)) : EReal)) fun _ => mem_univ _
  refine ⟨φ, ?_⟩
  have hpx : Tendsto (fun n => p (ns (φ n))) atTop (𝓝 x) :=
    hp.comp (hns.comp hφ.tendsto_atTop)
  have hyx := h _ x y hpx hy
  rw [hyx] at hy
  exact EReal.tendsto_coe.1 hy

/-! ### `thm:construct-C` -/

/-- A positive weakly increasing function on `(0, 1]` has a positive weakly increasing
`1`-Lipschitz minorant there, namely `p(x) = inf_{t ∈ (0, 1]} (d(t) + |x - t|)`. -/
theorem exists_lipschitz_monotoneOn_le {d : ℝ → ℝ} (hd_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < d t)
    (hd_mono : MonotoneOn d (Ioc 0 1)) :
    ∃ p : ℝ → ℝ, LipschitzWith 1 p ∧ MonotoneOn p (Ioc 0 1) ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, 0 < p x ∧ p x ≤ d x := by
  set P : ℝ → ℝ := fun x => ⨅ t : Ioc (0 : ℝ) 1, (d t + |x - t|) with hP
  have hbdd : ∀ x : ℝ, BddBelow (range fun t : Ioc (0 : ℝ) 1 => d t + |x - t|) := fun x =>
    ⟨0, by rintro _ ⟨t, rfl⟩; have := hd_pos t t.2; positivity⟩
  have hle : ∀ (x : ℝ) (t : Ioc (0 : ℝ) 1), P x ≤ d t + |x - t| := fun x t => ciInf_le (hbdd x) t
  have hself : ∀ (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1), P x ≤ d x := fun x hx => by
    simpa using hle x ⟨x, hx⟩
  have : Nonempty (Ioc (0 : ℝ) 1) := ⟨⟨1, by norm_num⟩⟩
  refine ⟨P, LipschitzWith.of_le_add fun x y => ?_, fun x hx y hy hxy => ?_,
    fun x hx => ⟨?_, hself x hx⟩⟩
  · have : P x - dist x y ≤ P y := le_ciInf fun t => by
      have h1 := hle x t
      have h2 := abs_sub_le x y (t : ℝ)
      rw [Real.dist_eq]; linarith
    linarith
  · refine le_ciInf fun t => ?_
    rcases le_or_gt (t : ℝ) x with htx | hxt
    · have h1 := hle x t
      rw [abs_of_nonneg (sub_nonneg.2 htx)] at h1
      rw [abs_of_nonneg (sub_nonneg.2 (htx.trans hxy))]
      linarith
    · have h1 := hself x hx
      have h2 := hd_mono hx t.2 hxt.le
      have h3 := abs_nonneg (y - (t : ℝ))
      linarith
  · have hx2 : x / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    refine lt_of_lt_of_le (lt_min (hd_pos _ hx2) (half_pos hx.1)) (le_ciInf fun t => ?_)
    rcases le_or_gt (x / 2) t with hxt | htx
    · have h1 := hd_mono hx2 t.2 hxt
      have h2 := abs_nonneg (x - t)
      have h3 := min_le_left (d (x / 2)) (x / 2)
      linarith
    · have h1 := hd_pos t t.2
      have h2 := le_abs_self (x - t)
      have h3 := min_le_right (d (x / 2)) (x / 2)
      linarith

/-- If a function continuous on a preconnected set takes two values at distance `≥ 2π`, then its
composition with `sin` takes every value of `sin`. -/
theorem exists_sin_eq_of_isPreconnected {X : Type*} [TopologicalSpace X] {γ : Set X}
    (hγ : IsPreconnected γ) {F : X → ℝ} (hF : ContinuousOn F γ) {z₁ z₂ : X} (h₁ : z₁ ∈ γ)
    (h₂ : z₂ ∈ γ) (h : 2 * π ≤ |F z₁ - F z₂|) (c : ℝ) : ∃ z ∈ γ, sin (F z) = sin c := by
  have hI := hγ.image F hF
  have key : ∀ u ∈ F '' γ, ∀ v ∈ F '' γ, u + 2 * π ≤ v → ∃ z ∈ γ, sin (F z) = sin c := by
    intro u hu v hv huv
    have hp : (0 : ℝ) < 2 * π := two_pi_pos
    have hw := toIcoMod_mem_Ico hp u c
    obtain ⟨z, hz, hzw⟩ := hI.Icc_subset hu hv ⟨hw.1, by linarith [hw.2]⟩
    refine ⟨z, hz, ?_⟩
    rw [hzw, ← self_sub_toIcoDiv_zsmul]
    exact Real.sin_periodic.sub_zsmul_eq _
  rcases le_abs'.1 h with h | h
  · exact key _ (mem_image_of_mem F h₁) _ (mem_image_of_mem F h₂) (by linarith)
  · exact key _ (mem_image_of_mem F h₂) _ (mem_image_of_mem F h₁) (by linarith)

/-- `thm:construct-C`: for `d : (0, 1] → (0, ∞)` weakly increasing there is a function `k`,
continuous on `ℝ × (0, 1]` and bounded by `√2`, such that every preconnected
`γ ⊆ [-1, 1] × (0, a]` with two points at distance `≥ d(a)` contains points `p, q` with
`|k(p) - k(q)| ≥ 2`. -/
theorem exists_k {d : ℝ → ℝ} (hd_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < d t)
    (hd_mono : MonotoneOn d (Ioc 0 1)) :
    ∃ k : ℂ → ℂ, ContinuousOn k {z | 0 < z.im ∧ z.im ≤ 1} ∧ (∀ z, ‖k z‖ ≤ √2) ∧
      ∀ a ∈ Ioc (0 : ℝ) 1, ∀ γ : Set ℂ, IsPreconnected γ →
        γ ⊆ {z | |z.re| ≤ 1 ∧ 0 < z.im ∧ z.im ≤ a} →
        (∃ z₁ ∈ γ, ∃ z₂ ∈ γ, d a ≤ dist z₁ z₂) → ∃ z ∈ γ, ∃ w ∈ γ, 2 ≤ ‖k z - k w‖ := by
  obtain ⟨p, hpL, hpm, hp⟩ := exists_lipschitz_monotoneOn_le (d := fun t => d t / 2)
    (fun t ht => half_pos (hd_pos t ht))
    (fun s hs t ht hst => by have := hd_mono hs ht hst; dsimp only; linarith)
  have hp_cont : Continuous p := hpL.continuous
  set m : ℝ → ℝ := fun y => min (p y) (min (y / 2) (p (y / 2) ^ 2 / 2)) with hm
  have hm_cont : Continuous m := by fun_prop
  have hhalf : ∀ y ∈ Ioc (0 : ℝ) 1, y / 2 ∈ Ioc (0 : ℝ) 1 := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hm_pos : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < m y := fun y hy =>
    lt_min (hp y hy).1 (lt_min (by linarith [hy.1])
      (by have := (hp _ (hhalf y hy)).1; positivity))
  have hm_mono : MonotoneOn m (Ioc 0 1) := by
    intro x hx y hy hxy
    refine min_le_min (hpm hx hy hxy) (min_le_min (by linarith) ?_)
    have h1 := (hp _ (hhalf x hx)).1
    have h2 : p (x / 2) ≤ p (y / 2) := hpm (hhalf x hx) (hhalf y hy) (by linarith)
    gcongr
  set S : Set ℂ := {z | 0 < z.im ∧ z.im ≤ 1} with hS
  set F : ℂ → ℝ := fun z => 2 * π / (z.im * m z.im) with hF
  set G : ℂ → ℝ := fun z => 4 * π * (z.re / p z.im) with hG
  have hFc : ContinuousOn F S :=
    continuousOn_const.div (by fun_prop) fun z hz => (mul_pos hz.1 (hm_pos _ hz)).ne'
  have hGc : ContinuousOn G S :=
    continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun z hz => (hp _ hz).1.ne')
  set k : ℂ → ℂ := fun z => (sin (F z) : ℂ) + (sin (G z) : ℂ) * Complex.I with hk
  have hkre : ∀ z w, (k z - k w).re = sin (F z) - sin (F w) := fun z w => by simp [hk, Complex.sin_ofReal_re]
  have hkim : ∀ z w, (k z - k w).im = sin (G z) - sin (G w) := fun z w => by simp [hk, Complex.sin_ofReal_re]
  refine ⟨k, ?_, ?_, ?_⟩
  · refine ContinuousOn.add ?_ ?_
    · exact Complex.continuous_ofReal.comp_continuousOn
        (Real.continuous_sin.comp_continuousOn hFc)
    · exact (Complex.continuous_ofReal.comp_continuousOn
        (Real.continuous_sin.comp_continuousOn hGc)).mul continuousOn_const
  · intro z
    rw [hk, Complex.norm_add_mul_I]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [sin_sq_le_one (F z), sin_sq_le_one (G z)]
  intro a ha γ hγ hsub ⟨z₁, h₁, z₂, h₂, hdist⟩
  wlog hy : z₂.im ≤ z₁.im generalizing z₁ z₂
  · exact this z₂ h₂ z₁ h₁ (by rwa [dist_comm]) (le_of_not_ge hy)
  have hγS : γ ⊆ S := fun z hz => ⟨(hsub hz).2.1, (hsub hz).2.2.trans ha.2⟩
  have hy₁ : z₁.im ∈ Ioc (0 : ℝ) 1 := hγS h₁
  have hy₂ : z₂.im ∈ Ioc (0 : ℝ) 1 := hγS h₂
  have hy₁a : z₁.im ≤ a := (hsub h₁).2.2
  by_cases h12 : m z₁.im ≤ z₁.im - z₂.im
  · -- the imaginary parts are far apart: `Re k` takes the values `±1`
    have hF2 : 2 * π ≤ |F z₁ - F z₂| := by
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      have hm₁ := hm_pos _ hy₁
      have hm₂ := hm_pos _ hy₂
      have hm21 : m z₂.im ≤ m z₁.im := hm_mono hy₂ hy₁ hy
      have hA : 2 * π / (z₂.im * m z₁.im) ≤ F z₂ :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hy₂.1 hm₂)
          (mul_le_mul_of_nonneg_left hm21 hy₂.1.le)
      have hB : 2 * π / (z₂.im * m z₁.im) - F z₁ =
          2 * π * (z₁.im - z₂.im) / (z₁.im * z₂.im * m z₁.im) := by
        have := hy₁.1.ne'
        have := hy₂.1.ne'
        have := hm₁.ne'
        simp only [hF]
        field_simp
      have hC : 2 * π ≤ 2 * π * (z₁.im - z₂.im) / (z₁.im * z₂.im * m z₁.im) := by
        rw [le_div_iff₀ (by have := hy₁.1; have := hy₂.1; positivity)]
        refine mul_le_mul_of_nonneg_left ?_ two_pi_pos.le
        have : z₁.im * z₂.im ≤ 1 := mul_le_one₀ hy₁.2 hy₂.1.le hy₂.2
        nlinarith
      linarith
    obtain ⟨z, hz, hz1⟩ := exists_sin_eq_of_isPreconnected hγ (hFc.mono hγS) h₁ h₂ hF2 (π / 2)
    obtain ⟨w, hw, hw1⟩ :=
      exists_sin_eq_of_isPreconnected hγ (hFc.mono hγS) h₁ h₂ hF2 (-(π / 2))
    refine ⟨z, hz, w, hw, ?_⟩
    have := Complex.abs_re_le_norm (k z - k w)
    rw [hkre, hz1, hw1, sin_neg, sin_pi_div_two] at this
    norm_num at this
    linarith
  · -- the imaginary parts are close: `Im k` takes the values `±1`
    push Not at h12
    set y₁ := z₁.im
    set y₂ := z₂.im
    have hmp : m y₁ ≤ p y₁ := min_le_left _ _
    have hmy : m y₁ ≤ y₁ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hmc : m y₁ ≤ p (y₁ / 2) ^ 2 / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hpd : p y₁ ≤ d y₁ / 2 := (hp _ hy₁).2
    have hda : d y₁ ≤ d a := hd_mono hy₁ ha hy₁a
    have hc := (hp _ (hhalf _ hy₁)).1
    have hp₁ : p (y₁ / 2) ≤ p y₁ := hpm (hhalf _ hy₁) hy₁ (by linarith [hy₁.1])
    have hp₂ : p (y₁ / 2) ≤ p y₂ := hpm (hhalf _ hy₁) hy₂ (by linarith)
    have hlip : |p y₁ - p y₂| ≤ y₁ - y₂ := by
      have := hpL.dist_le_mul y₁ y₂
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hy)] at this
      simpa using this
    -- the reciprocals of `p` are close
    have hrec : |1 / p y₁ - 1 / p y₂| ≤ 1 / 2 := by
      have hp1 : 0 < p y₁ := hc.trans_le hp₁
      have hp2 : 0 < p y₂ := hc.trans_le hp₂
      rw [div_sub_div _ _ hp1.ne' hp2.ne', abs_div, abs_of_pos (mul_pos hp1 hp2)]
      have hnum : |1 * p y₂ - p y₁ * 1| ≤ p (y₁ / 2) ^ 2 / 2 := by
        rw [abs_sub_comm]; simpa using hlip.trans (by linarith)
      have hden : p (y₁ / 2) * p (y₁ / 2) ≤ p y₁ * p y₂ :=
        mul_le_mul hp₁ hp₂ hc.le hp1.le
      calc |1 * p y₂ - p y₁ * 1| / (p y₁ * p y₂)
          ≤ (p (y₁ / 2) ^ 2 / 2) / (p (y₁ / 2) * p (y₁ / 2)) :=
            div_le_div₀ (by positivity) hnum (by positivity) hden
        _ = 1 / 2 := by field_simp
    -- the real parts are far apart
    have hx : p y₁ ≤ |z₁.re - z₂.re| := by
      have h1 : dist z₁ z₂ ≤ |z₁.re - z₂.re| + |y₁ - y₂| := by
        rw [Complex.dist_eq]
        simpa using Complex.norm_le_abs_re_add_abs_im (z₁ - z₂)
      rw [abs_of_nonneg (sub_nonneg.2 hy)] at h1
      linarith
    have hG2 : 2 * π ≤ |G z₁ - G z₂| := by
      have hp1 : 0 < p y₁ := hc.trans_le hp₁
      have h1 : 1 ≤ |z₁.re - z₂.re| / p y₁ := by rw [le_div_iff₀ hp1]; linarith
      have h2 : |z₂.re * (1 / p y₁ - 1 / p y₂)| ≤ 1 / 2 := by
        rw [abs_mul]
        have := (hsub h₂).1
        calc |z₂.re| * |1 / p y₁ - 1 / p y₂| ≤ 1 * (1 / 2) :=
              mul_le_mul this hrec (abs_nonneg _) zero_le_one
          _ = 1 / 2 := by ring
      have h3 : z₁.re / p y₁ - z₂.re / p y₂ =
          (z₁.re - z₂.re) / p y₁ + z₂.re * (1 / p y₁ - 1 / p y₂) := by ring
      have h4 : 1 / 2 ≤ |z₁.re / p y₁ - z₂.re / p y₂| := by
        rw [h3]
        have := abs_add_le ((z₁.re - z₂.re) / p y₁ + z₂.re * (1 / p y₁ - 1 / p y₂))
          (-(z₂.re * (1 / p y₁ - 1 / p y₂)))
        rw [abs_neg, add_neg_cancel_right, abs_div, abs_of_pos hp1] at this
        linarith
      have h5 : G z₁ - G z₂ = 4 * π * (z₁.re / p y₁ - z₂.re / p y₂) := by
        simp only [hG]; ring
      rw [h5, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
      nlinarith [pi_pos]
    obtain ⟨z, hz, hz1⟩ := exists_sin_eq_of_isPreconnected hγ (hGc.mono hγS) h₁ h₂ hG2 (π / 2)
    obtain ⟨w, hw, hw1⟩ :=
      exists_sin_eq_of_isPreconnected hγ (hGc.mono hγS) h₁ h₂ hG2 (-(π / 2))
    refine ⟨z, hz, w, hw, ?_⟩
    have := Complex.abs_im_le_norm (k z - k w)
    rw [hkim, hz1, hw1, sin_neg, sin_pi_div_two] at this
    norm_num at this
    linarith

end TJK.Construct
