import Mathlib
import TJK.Defs
import TJK.Plane.Basic
import TJK.Construct.K
import TJK.Cube.AnalyticNonBorel
import TJK.Cube.Elementary

/-!
# A cube with a non-Borel set of curvilinear convergence (blueprint §I)

Formalizes `paper/sections/I-cube.tex` (Kaczynski, Proc. AMS 23 (1969)):

* `def:asymptotic` (`IsAsymptoticValue`, `IsPointAsymptoticValue`);
* `fact:analytic-nonborel` (`exists_analytic_not_borel`, proved in
  `TJK/Cube/AnalyticNonBorel.lean`);
* `lem:cube-lemma` (`exists_s`), proved by the elementary argument of `TJK/Cube/Elementary.lean`
  (`TJK.Cube.Elementary.exists_s'`) instead of Kaczynski's proof via Kierst's theorem and
  normal functions (which are not formalized);
* `thm:cube` (`exists_not_measurableSet_curvConvSet'`), for the cube `openCube'`, which is
  definitionally `TJK.Cube.openCube` of `TJK/MainTheorems.lean`.

Points of the plane are complex numbers; points of space are elements of
`EuclideanSpace ℝ (Fin 3)`, with coordinates `P 0`, `P 1`, `P 2`.
-/

open _root_.Set Filter Topology Metric

namespace TJK.Cube

/-! ### `def:asymptotic` -/

section Asymptotic

variable {E : Type*} [PseudoMetricSpace E] {Y : Type*} [TopologicalSpace Y]

/-- `def:asymptotic`: `a` is an asymptotic value of `f` in `Ω`: there is a continuous
`v : [0, 1) → Ω` with `dist (v t, Ωᶜ) → 0` and `f (v t) → a` as `t → 1`. -/
def IsAsymptoticValue (Ω : Set E) (f : E → Y) (a : Y) : Prop :=
  ∃ v : ℝ → E, ContinuousOn v (Ico 0 1) ∧ MapsTo v (Ico 0 1) Ω ∧
    Tendsto (fun t => infDist (v t) Ωᶜ) (𝓝[<] 1) (𝓝 0) ∧ Tendsto (f ∘ v) (𝓝[<] 1) (𝓝 a)

/-- `def:asymptotic`: `a` is a point asymptotic value of `f` at `p ∈ ∂Ω`: there is a continuous
`v : [0, 1) → Ω` with `v t → p` and `f (v t) → a` as `t → 1`. -/
def IsPointAsymptoticValue (Ω : Set E) (f : E → Y) (p : E) (a : Y) : Prop :=
  p ∈ frontier Ω ∧ ∃ v : ℝ → E, ContinuousOn v (Ico 0 1) ∧ MapsTo v (Ico 0 1) Ω ∧
    Tendsto v (𝓝[<] 1) (𝓝 p) ∧ Tendsto (f ∘ v) (𝓝[<] 1) (𝓝 a)

/-- A point asymptotic value is an asymptotic value. -/
theorem IsPointAsymptoticValue.isAsymptoticValue {Ω : Set E} {f : E → Y} {p : E} {a : Y}
    (h : IsPointAsymptoticValue Ω f p a) : IsAsymptoticValue Ω f a := by
  obtain ⟨hp, v, hc, hm, hv, hf⟩ := h
  refine ⟨v, hc, hm, ?_, hf⟩
  have h0 : infDist p Ωᶜ = 0 := by
    apply infDist_zero_of_mem_closure
    rw [← frontier_compl] at hp
    exact frontier_subset_closure hp
  rw [← h0]
  exact ((continuous_infDist_pt _).tendsto p).comp hv

end Asymptotic

/-! ### Parameter bookkeeping -/

theorem tendsto_affine {t₀ : ℝ} (ht : t₀ < 1) :
    Tendsto (fun t : ℝ => t₀ + (1 - t₀) * t) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous (fun t : ℝ => t₀ + (1 - t₀) * t) := by fun_prop
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with t (ht' : t < 1)
    rw [mem_Iio]
    nlinarith

theorem mapsTo_affine {t₀ : ℝ} (ht : t₀ < 1) :
    MapsTo (fun t : ℝ => t₀ + (1 - t₀) * t) (Ico 0 1) (Ico t₀ 1) := fun t h =>
  ⟨by nlinarith [h.1], by nlinarith [h.2]⟩

theorem exists_Ico_of_eventually {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝[<] (1 : ℝ), P t) :
    ∃ t₀, 0 ≤ t₀ ∧ t₀ < 1 ∧ ∀ t ∈ Ico t₀ 1, P t := by
  obtain ⟨l, hl, hlP⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h
  have hl' : l < 1 := hl
  refine ⟨max ((l + 1) / 2) 0, le_max_right _ _, max_lt (by linarith) one_pos,
    fun t ht => hlP ⟨?_, ht.2⟩⟩
  have := le_max_left ((l + 1) / 2) 0
  linarith [ht.1]

theorem isPointAsymptoticValue_of_Ico {E : Type*} [PseudoMetricSpace E] {Y : Type*}
    [TopologicalSpace Y] {Ω : Set E} {f : E → Y} {p : E} {a : Y} (hp : p ∈ frontier Ω)
    {v : ℝ → E} {t₀ : ℝ} (ht : t₀ < 1) (hc : ContinuousOn v (Ico t₀ 1))
    (hm : MapsTo v (Ico t₀ 1) Ω) (hv : Tendsto v (𝓝[<] 1) (𝓝 p))
    (hf : Tendsto (f ∘ v) (𝓝[<] 1) (𝓝 a)) : IsPointAsymptoticValue Ω f p a := by
  refine ⟨hp, v ∘ fun t => t₀ + (1 - t₀) * t,
    hc.comp (by fun_prop : Continuous fun t : ℝ => t₀ + (1 - t₀) * t).continuousOn
      (mapsTo_affine ht), hm.comp (mapsTo_affine ht), hv.comp (tendsto_affine ht),
    hf.comp (tendsto_affine ht)⟩

theorem mem_frontier_of_tendsto {X : Type*} [TopologicalSpace X] {Ω : Set X} (hΩ : IsOpen Ω)
    {v : ℝ → X} {p : X} (hv : Tendsto v (𝓝[<] 1) (𝓝 p)) (hvΩ : ∀ᶠ t in 𝓝[<] 1, v t ∈ Ω)
    (hp : p ∉ Ω) : p ∈ frontier Ω := by
  rw [frontier, hΩ.interior_eq]
  exact ⟨mem_closure_of_tendsto hv hvΩ, hp⟩

/-- A function continuous on `[t₀, 1)` with a limit `p` at `1` gives a path from `v t₀` to `p`
whose germ at `1` is (a reparametrization of) that of `v`. -/
theorem exists_path_of_tendsto {X : Type*} [TopologicalSpace X] {v : ℝ → X} {t₀ : ℝ}
    (ht₀ : t₀ < 1) (hv : ContinuousOn v (Ico t₀ 1)) {p : X} (hp : Tendsto v (𝓝[<] 1) (𝓝 p)) :
    ∃ g : Path (v t₀) p, (∀ t : unitInterval, t ≠ 1 → g t ∈ v '' Ico t₀ 1) ∧
      map g.extend (𝓝[<] 1) ≤ map v (𝓝[<] 1) := by
  set φ : ℝ → ℝ := fun t => t₀ + (1 - t₀) * t with hφ
  have hφc : Continuous φ := by fun_prop
  set G : ℝ → X := fun t => if t < 1 then v (φ t) else p with hG
  have hGlt : ∀ t < 1, G t = v (φ t) := fun t h => if_pos h
  have hG1 : G 1 = p := if_neg (lt_irrefl 1)
  have hGc : ContinuousOn G (Icc 0 1) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with h | h
    · have hvφ : ContinuousWithinAt (v ∘ φ) (Ico 0 1) t :=
        (hv (φ t) (mapsTo_affine ht₀ ⟨ht.1, h⟩)).comp hφc.continuousWithinAt (mapsTo_affine ht₀)
      have h1 : ContinuousWithinAt G (Ico 0 1) t := by
        refine hvφ.congr (fun s hs => hGlt s hs.2) (hGlt t h)
      have h2 : Icc (0 : ℝ) 1 ∩ Iio 1 = Ico 0 1 := by
        ext s
        exact ⟨fun ⟨⟨a, _⟩, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨⟨a, c.le⟩, c⟩⟩
      rw [← h2] at h1
      exact (continuousWithinAt_inter (Iio_mem_nhds h)).1 h1
    · subst h
      have : ContinuousWithinAt G (Iio 1) 1 := by
        rw [ContinuousWithinAt, hG1]
        refine (hp.comp (tendsto_affine ht₀)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s (hs : s < 1)
        exact (hGlt s hs).symm
      exact (continuousWithinAt_Iio_iff_Iic.1 this).mono fun s hs => hs.2
  have hG0 : G 0 = v t₀ := by rw [hGlt 0 one_pos]; simp [hφ]
  let g : Path (v t₀) p := ⟨⟨fun t => G t, hGc.comp_continuous continuous_subtype_val
    fun t => t.2⟩, hG0, hG1⟩
  refine ⟨g, fun t ht => ?_, ?_⟩
  · have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h' => ht (Subtype.ext h')
    show G t ∈ _
    rw [hGlt _ ht1]
    exact ⟨_, mapsTo_affine ht₀ ⟨t.2.1, ht1⟩, rfl⟩
  · have : g.extend =ᶠ[𝓝[<] 1] v ∘ φ := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht'
      rw [g.extend_apply ⟨ht'.1.le, ht'.2.le⟩]
      exact hGlt t ht'.2
    rw [map_congr this, ← map_map]
    exact map_mono (tendsto_affine ht₀)

/-! ### The facts -/

/-- `fact:analytic-nonborel` (Souslin–Lusin): there is an analytic subset of `ℝ` that is not a
Borel set. Mathlib has analytic sets but not this example; proved in
`TJK.Cube.AnalyticNonBorel`. -/
theorem exists_analytic_not_borel :
    ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A :=
  exists_analytic_not_borel'

/-! ### `lem:cube-lemma` -/

/-- `ρ(w) = w / (1 + |w|)`, a homeomorphism of `ℂ` onto `𝔻` mapping `ℝ` onto `(-1, 1)`. -/
noncomputable def squash (w : ℂ) : ℂ := w / ((1 + ‖w‖ : ℝ) : ℂ)

/-- The inverse `u ↦ u / (1 - |u|)` of `squash`, on `𝔻`. -/
noncomputable def unsquash (u : ℂ) : ℂ := u / ((1 - ‖u‖ : ℝ) : ℂ)

/-- `squash` on the real line. -/
noncomputable def realSquash (a : ℝ) : ℝ := a / (1 + |a|)

theorem norm_squash (w : ℂ) : ‖squash w‖ = ‖w‖ / (1 + ‖w‖) := by
  rw [squash, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem norm_squash_lt_one (w : ℂ) : ‖squash w‖ < 1 := by
  rw [norm_squash, div_lt_one (by positivity)]; linarith

theorem unsquash_squash (w : ℂ) : unsquash (squash w) = w := by
  have hpos : 0 < 1 + ‖w‖ := by positivity
  have h1 : 1 - ‖squash w‖ = 1 / (1 + ‖w‖) := by
    rw [norm_squash]; field_simp; ring
  have hc : ((1 + ‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hc' : (1 + (‖w‖ : ℂ)) ≠ 0 := by exact_mod_cast hc
  rw [unsquash, h1, squash]
  push_cast
  field_simp

theorem squash_unsquash {u : ℂ} (hu : ‖u‖ < 1) : squash (unsquash u) = u := by
  have hpos : 0 < 1 - ‖u‖ := by linarith
  have h1 : 1 + ‖unsquash u‖ = 1 / (1 - ‖u‖) := by
    rw [unsquash, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    field_simp; ring
  have hc : ((1 - ‖u‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hc' : (1 - (‖u‖ : ℂ)) ≠ 0 := by exact_mod_cast hc
  rw [squash, h1, unsquash]
  push_cast
  field_simp

theorem continuous_squash : Continuous squash := by
  refine continuous_id.div (by fun_prop) fun w => ?_
  exact_mod_cast (show 0 < 1 + ‖w‖ by positivity).ne'

theorem continuousAt_unsquash {u : ℂ} (hu : ‖u‖ < 1) : ContinuousAt unsquash u :=
  continuousAt_id.div (by fun_prop) (by exact_mod_cast (sub_pos.2 hu).ne')

theorem squash_ofReal (a : ℝ) : squash a = (realSquash a : ℂ) := by
  rw [squash, realSquash, Complex.norm_real, Real.norm_eq_abs]; push_cast; rfl

theorem unsquash_ofReal (b : ℝ) : unsquash b = ((b / (1 - |b|) : ℝ) : ℂ) := by
  rw [unsquash, Complex.norm_real, Real.norm_eq_abs]; push_cast; rfl

theorem realSquash_injective : Function.Injective realSquash := fun a a' h => by
  have := congrArg unsquash (show squash a = squash a' by rw [squash_ofReal, squash_ofReal, h])
  rw [unsquash_squash, unsquash_squash] at this
  exact_mod_cast this

theorem continuous_realSquash : Continuous realSquash :=
  continuous_id.div (by fun_prop) fun a => (show 0 < 1 + |a| by positivity).ne'

theorem realSquash_mem (a : ℝ) : realSquash a ∈ Ioo (-1) 1 := by
  have h : |realSquash a| < 1 := by
    rw [realSquash, abs_div, abs_of_pos (show 0 < 1 + |a| by positivity),
      div_lt_one (by positivity)]
    linarith
  exact abs_lt.1 h

/-- `(x, y) ↦ (1 - y) e^{ix}` for `y ≤ 1`, and `0` for `y ≥ 1`. -/
noncomputable def wrap (z : ℂ) : ℂ :=
  ((max (1 - z.im) 0 : ℝ) : ℂ) * Complex.exp (z.re * Complex.I)

theorem continuous_wrap : Continuous wrap := by unfold wrap; fun_prop

theorem norm_wrap (z : ℂ) : ‖wrap z‖ = max (1 - z.im) 0 := by
  rw [wrap, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (le_max_right _ _)]

theorem wrap_mem_disc {z : ℂ} (hz : 0 < z.im) : wrap z ∈ disc := by
  rw [disc, mem_ball_zero_iff, norm_wrap]; exact max_lt (by linarith) one_pos

theorem infDist_wrap_le {z : ℂ} (hz : 0 < z.im) : infDist (wrap z) discᶜ ≤ z.im := by
  have hmem : Complex.exp (z.re * Complex.I) ∈ discᶜ := by
    simp [disc, Complex.norm_exp_ofReal_mul_I]
  refine (infDist_le_dist_of_mem hmem).trans ?_
  have : wrap z - Complex.exp (z.re * Complex.I) =
      ((max (1 - z.im) 0 - 1 : ℝ) : ℂ) * Complex.exp (z.re * Complex.I) := by
    rw [wrap]; push_cast; ring
  rw [dist_eq_norm, this, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [le_max_left (1 - z.im) 0],
    by linarith [max_le (show 1 - z.im ≤ 1 + z.im by linarith) (show (0 : ℝ) ≤ 1 + z.im by linarith)]⟩

theorem isOpen_upper : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im

theorem infDist_upper_compl {z : ℂ} (hz : 0 ≤ z.im) : infDist z upperᶜ = z.im := by
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

theorem I_ne_neg_I : Complex.I ≠ -Complex.I := by
  intro h
  have := congrArg Complex.im h
  simp at this
  norm_num at this

/-- `lem:cube-lemma`: a continuous `s : ℍ → 𝔻` whose real asymptotic values in `(-1, 1)` are
exactly its real point asymptotic values in `(-1, 1)`, and form a non-Borel set. -/
theorem exists_s : ∃ s : ℂ → ℂ, ContinuousOn s upper ∧ (∀ z, ‖s z‖ < 1) ∧
    {b : ℝ | b ∈ Ioo (-1) 1 ∧ IsAsymptoticValue upper s (b : ℂ)} =
      {b : ℝ | b ∈ Ioo (-1) 1 ∧ ∃ p, IsPointAsymptoticValue upper s p (b : ℂ)} ∧
    ¬ MeasurableSet {b : ℝ | b ∈ Ioo (-1) 1 ∧ IsAsymptoticValue upper s (b : ℂ)} :=
  -- the primed definitions of `TJK.Cube.Elementary` are definitionally the unprimed ones
  Elementary.exists_s'

/-! ### `thm:cube`: notation and auxiliary estimates -/

/-- The open cube `K° = (-1, 1) × (0, 1) × (-1, 1)`; definitionally `TJK.Cube.openCube`. -/
def openCube' : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v 0 ∈ Ioo (-1 : ℝ) 1 ∧ v 1 ∈ Ioo (0 : ℝ) 1 ∧ v 2 ∈ Ioo (-1 : ℝ) 1}

theorem isOpen_openCube' : IsOpen openCube' := by
  have h : ∀ i : Fin 3, Continuous fun v : EuclideanSpace ℝ (Fin 3) => v i := fun i => by
    fun_prop
  exact (isOpen_Ioo.preimage (h 0)).inter
    ((isOpen_Ioo.preimage (h 1)).inter (isOpen_Ioo.preimage (h 2)))

/-- The point `⟨x, y, z⟩` of space. -/
noncomputable def pt (x y z : ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![x, y, z]

@[simp] theorem pt_zero (x y z : ℝ) : pt x y z 0 = x := by simp [pt]
@[simp] theorem pt_one (x y z : ℝ) : pt x y z 1 = y := by simp [pt]
@[simp] theorem pt_two (x y z : ℝ) : pt x y z 2 = z := by simp [pt]

theorem continuous_pt : Continuous fun x : ℝ × ℝ × ℝ => pt x.1 x.2.1 x.2.2 := by
  unfold pt; fun_prop

/-- The projection `⟨x, y, z⟩ ↦ x + iy` to the plane. -/
noncomputable def proj (P : EuclideanSpace ℝ (Fin 3)) : ℂ := (P 0 : ℂ) + (P 1 : ℂ) * Complex.I

@[simp] theorem proj_re (P : EuclideanSpace ℝ (Fin 3)) : (proj P).re = P 0 := by simp [proj]
@[simp] theorem proj_im (P : EuclideanSpace ℝ (Fin 3)) : (proj P).im = P 1 := by simp [proj]

theorem continuous_proj : Continuous proj := by unfold proj; fun_prop

theorem abs_coord_sub_le (P Q : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    |P i - Q i| ≤ dist P Q := by
  have := PiLp.dist_apply_le P Q i
  rwa [Real.dist_eq] at this

/-- `g(x, y) = s(x / y, y)`. -/
noncomputable def gOf (s : ℂ → ℂ) (w : ℂ) : ℂ :=
  s (((w.re / w.im : ℝ) : ℂ) + (w.im : ℂ) * Complex.I)

/-- `f(x, y, z) = (g(x, y) - z) k(x, y)`. -/
noncomputable def fOf (s k : ℂ → ℂ) (P : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (gOf s (proj P) - (P 2 : ℂ)) * k (proj P)

theorem continuousOn_gOf {s : ℂ → ℂ} (hs : ContinuousOn s upper) : ContinuousOn (gOf s) upper := by
  refine hs.comp ?_ fun w hw => ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.continuousOn.div
      Complex.continuous_im.continuousOn fun w hw => ne_of_gt hw)).add (by fun_prop)
  · show 0 < (((w.re / w.im : ℝ) : ℂ) + (w.im : ℂ) * Complex.I).im
    simpa using hw

/-- `[-1, 1] × [t, 1]`. -/
def Kt (t : ℝ) : Set ℂ := {z | |z.re| ≤ 1 ∧ t ≤ z.im ∧ z.im ≤ 1}

theorem isCompact_Kt (t : ℝ) : IsCompact (Kt t) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  · refine isBounded_iff_forall_norm_le.2 ⟨2 + |t|, fun z hz => ?_⟩
    have h1 := Complex.norm_le_abs_re_add_abs_im z
    have h2 : |z.im| ≤ 1 + |t| := abs_le.2 ⟨by linarith [neg_abs_le t, hz.2.1], by
      linarith [abs_nonneg t, hz.2.2]⟩
    linarith [hz.1]

/-- `δ` is good for `g` at level `t`: points of `K t` closer than `δ` have `g`-values within `t`. -/
def Good (g : ℂ → ℂ) (t δ : ℝ) : Prop :=
  ∀ z ∈ Kt t, ∀ z' ∈ Kt t, dist z z' < δ → ‖g z - g z'‖ ≤ t

/-- `d₀(t)`: the supremum of the good `δ ∈ [0, 1]`. -/
noncomputable def d₀ (g : ℂ → ℂ) (t : ℝ) : ℝ := sSup {δ | δ ∈ Icc (0 : ℝ) 1 ∧ Good g t δ}

theorem bddAbove_good (g : ℂ → ℂ) (t : ℝ) : BddAbove {δ | δ ∈ Icc (0 : ℝ) 1 ∧ Good g t δ} :=
  ⟨1, fun _ hδ => hδ.1.2⟩

theorem zero_mem_good (g : ℂ → ℂ) (t : ℝ) : (0 : ℝ) ∈ {δ | δ ∈ Icc (0 : ℝ) 1 ∧ Good g t δ} :=
  ⟨⟨le_rfl, zero_le_one⟩, fun _ _ _ _ hd => absurd hd (not_lt.2 dist_nonneg)⟩

theorem d₀_monotone (g : ℂ → ℂ) : Monotone (d₀ g) := fun t t' htt =>
  csSup_le_csSup (bddAbove_good g t') ⟨0, zero_mem_good g t⟩ fun _ hδ =>
    ⟨hδ.1, fun z hz z' hz' hd =>
      (hδ.2 z ⟨hz.1, htt.trans hz.2.1, hz.2.2⟩ z' ⟨hz'.1, htt.trans hz'.2.1, hz'.2.2⟩ hd).trans
        htt⟩

theorem d₀_pos {g : ℂ → ℂ} (hg : ContinuousOn g upper) {t : ℝ} (ht : 0 < t) : 0 < d₀ g t := by
  have huc := (isCompact_Kt t).uniformContinuousOn_of_continuous
    (hg.mono fun z hz => show 0 < z.im from ht.trans_le hz.2.1)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc t ht
  have hmem : min δ 1 ∈ {δ | δ ∈ Icc (0 : ℝ) 1 ∧ Good g t δ} :=
    ⟨⟨le_min hδ.le zero_le_one, min_le_right _ _⟩, fun z hz z' hz' hd => by
      rw [← dist_eq_norm]
      exact (hδ' z hz z' hz' (hd.trans_le (min_le_left _ _))).le⟩
  exact (lt_min hδ one_pos).trans_le (le_csSup (bddAbove_good g t) hmem)

theorem good_of_lt_d₀ {g : ℂ → ℂ} {t : ℝ} {z z' : ℂ} (hz : z ∈ Kt t) (hz' : z' ∈ Kt t)
    (hd : dist z z' < d₀ g t) : ‖g z - g z'‖ ≤ t := by
  obtain ⟨δ, hδ, hlt⟩ := exists_lt_of_lt_csSup ⟨0, zero_mem_good g t⟩ hd
  exact hδ.2 z hz z' hz' hlt

/-- The function `d(t) = min (d₀(t/2)/2, t/4)` fed to `thm:construct-C`. -/
noncomputable def dOf (g : ℂ → ℂ) (t : ℝ) : ℝ := min (d₀ g (t / 2) / 2) (t / 4)

theorem dOf_pos {g : ℂ → ℂ} (hg : ContinuousOn g upper) {t : ℝ} (ht : 0 < t) : 0 < dOf g t :=
  lt_min (by have := d₀_pos hg (half_pos ht); linarith) (by linarith)

theorem dOf_mono (g : ℂ → ℂ) : MonotoneOn (dOf g) (Ioc 0 1) := fun x _ y _ hxy =>
  min_le_min (by have := d₀_monotone g (show x / 2 ≤ y / 2 by linarith); linarith)
    (by linarith)

/-- Inequality `(cube1)`. -/
theorem cube1 (c e₁ e₂ k₁ k₂ : ℂ) (h₁ : ‖k₁‖ ≤ 2) (h₂ : ‖k₂‖ ≤ 2) :
    ‖c‖ * ‖k₁ - k₂‖ - 2 * ‖e₁‖ - 2 * ‖e₂‖ ≤ ‖(c + e₁) * k₁ - (c + e₂) * k₂‖ := by
  set X := (c + e₁) * k₁ - (c + e₂) * k₂
  have h : c * (k₁ - k₂) = X - e₁ * k₁ + e₂ * k₂ := by simp only [X]; ring
  have h3 : ‖c‖ * ‖k₁ - k₂‖ ≤ ‖X‖ + ‖e₁‖ * ‖k₁‖ + ‖e₂‖ * ‖k₂‖ := by
    rw [← norm_mul, h, ← norm_mul, ← norm_mul]
    calc ‖X - e₁ * k₁ + e₂ * k₂‖ ≤ ‖X - e₁ * k₁‖ + ‖e₂ * k₂‖ := norm_add_le _ _
      _ ≤ ‖X‖ + ‖e₁ * k₁‖ + ‖e₂ * k₂‖ := by gcongr; exact norm_sub_le _ _
  nlinarith [norm_nonneg e₁, norm_nonneg e₂, mul_le_mul_of_nonneg_left h₁ (norm_nonneg e₁),
    mul_le_mul_of_nonneg_left h₂ (norm_nonneg e₂)]

/-- Points of a compact `γ` where a continuous `φ` is small are near `x₀`, if `φ > 0` on
`γ \ {x₀}`. -/
theorem exists_delta {X : Type*} [MetricSpace X] {γ : Set X} (hγ : IsCompact γ) {φ : X → ℝ}
    (hφ : Continuous φ) {x₀ : X} (hpos : ∀ P ∈ γ, P ≠ x₀ → 0 < φ P) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ P ∈ γ, φ P ≤ δ → dist P x₀ < r := by
  set C := γ ∩ (ball x₀ r)ᶜ with hC
  have hCc : IsCompact C := hγ.inter_right isOpen_ball.isClosed_compl
  have hmemC : ∀ P ∈ γ, ¬ dist P x₀ < r → P ∈ C := fun P hP h => ⟨hP, by simpa using h⟩
  rcases C.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun P hP _ => ?_⟩
    by_contra h
    have := hmemC P hP h
    rw [he] at this
    exact this
  · obtain ⟨P₀, hP₀, hmin⟩ := hCc.exists_isMinOn hne hφ.continuousOn
    have hP₀x : P₀ ≠ x₀ := fun h => hP₀.2 (by rw [h]; exact mem_ball_self hr)
    have := hpos P₀ hP₀.1 hP₀x
    refine ⟨φ P₀ / 2, by linarith, fun P hP hφP => ?_⟩
    by_contra h
    have := isMinOn_iff.1 hmin P (hmemC P hP h)
    linarith

/-- The key step of `thm:cube`: if `f` converges along an arc `γ` at `⟨0, 0, b⟩` in `K°`, then
`g(x, y) - z → 0` along `γ`. -/
theorem tendsto_sub_of_tendsto {s k : ℂ → ℂ} (hsc : ContinuousOn s upper)
    (hk2 : ∀ z, ‖k z‖ ≤ 2)
    (hk : ∀ a ∈ Ioc (0 : ℝ) 1, ∀ γ : Set ℂ, IsPreconnected γ →
        γ ⊆ {z | |z.re| ≤ 1 ∧ 0 < z.im ∧ z.im ≤ a} →
        (∃ z₁ ∈ γ, ∃ z₂ ∈ γ, dOf (gOf s) a ≤ dist z₁ z₂) → ∃ z ∈ γ, ∃ w ∈ γ, 2 ≤ ‖k z - k w‖)
    {b : ℝ} {γ : Set (EuclideanSpace ℝ (Fin 3))} (hγ : IsArcAt openCube' (pt 0 0 b) γ) {qv : ℂ}
    (hf : Tendsto (fOf s k) (𝓝[γ \ {pt 0 0 b}] (pt 0 0 b)) (𝓝 qv)) :
    Tendsto (fun P => gOf s (proj P) - (P 2 : ℂ)) (𝓝[γ \ {pt 0 0 b}] (pt 0 0 b)) (𝓝 0) := by
  set x₀ := pt 0 0 b with hx₀
  set G := gOf s with hG
  have hGc : ContinuousOn G upper := continuousOn_gOf hsc
  obtain ⟨e, ⟨q, hq, hrange⟩, hΩ⟩ := hγ
  have hγc : IsCompact γ := hrange ▸ isCompact_range q.continuous
  have hcube : ∀ P ∈ γ, P ≠ x₀ → P ∈ openCube' := fun P h h' => hΩ ⟨h, h'⟩
  have hx₀1 : x₀ 1 = 0 := by simp [hx₀]
  have hx₀2 : x₀ 2 = b := by simp [hx₀]
  have hprojx₀ : proj x₀ = 0 := by apply Complex.ext <;> simp [hx₀]
  have hextγ : ∀ τ ∈ Icc (0 : ℝ) 1, q.extend τ ∈ γ := fun τ hτ => by
    rw [← hrange, q.extend_apply hτ]; exact mem_range_self _
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- the Cauchy property of `f` along `γ`
  have hC := Metric.tendsto_nhds.1 hf (ε / 2) (by positivity)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hC
  obtain ⟨r₁, hr₁, hC⟩ := hC
  set r := min r₁ (ε / 16) with hr
  have hr0 : 0 < r := lt_min hr₁ (by positivity)
  obtain ⟨δ, hδ, hδγ⟩ := exists_delta hγc (φ := fun P => P 1) (by fun_prop)
    (fun P hP hne => (hcube P hP hne).2.1.1) hr0
  set η := min (3 * δ / 4) (min (3 * ε / 32) (3 / 4)) with hη
  have hη0 : 0 < η := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hη1 := min_le_left (3 * δ / 4) (min (3 * ε / 32) (3 / 4))
  have hη2 := min_le_right (3 * δ / 4) (min (3 * ε / 32) (3 / 4))
  have hη3 := min_le_left (3 * ε / 32) (3 / 4 : ℝ)
  have hη4 := min_le_right (3 * ε / 32) (3 / 4 : ℝ)
  have hev : ∀ᶠ P in 𝓝[γ \ {x₀}] x₀, P 1 < η ∧ P ∈ γ \ {x₀} := by
    refine Eventually.and (nhdsWithin_le_nhds ?_) self_mem_nhdsWithin
    have hc : Continuous fun P : EuclideanSpace ℝ (Fin 3) => P 1 := by fun_prop
    exact (hc.tendsto x₀).eventually (eventually_lt_nhds (by rw [hx₀1]; exact hη0))
  -- a point `P = Pₙ` of `γ` where `|g - z| ≥ ε`
  obtain ⟨P, hPε, hPη, hPγ, hPne⟩ := (hcon.and_eventually hev).exists
  have hPε' : ε ≤ ‖G (proj P) - (P 2 : ℂ)‖ := by
    rw [dist_zero_right] at hPε; exact not_lt.1 hPε
  have hPc := hcube P hPγ hPne
  obtain ⟨u, hu⟩ : P ∈ range q := hrange ▸ hPγ
  set tn : ℝ := (u : ℝ) with htn
  have htnP : q.extend tn = P := by rw [htn, q.extend_extends', hu]
  set a := 4 * P 1 / 3 with ha_def
  have hP1 : 0 < P 1 := hPc.2.1.1
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by linarith
  have haδ : a ≤ δ := by linarith
  have haε : a < ε / 8 := by linarith
  set Φ : ℝ → ℂ := fun t => proj (q.extend t) with hΦ
  have hΦc : Continuous Φ := continuous_proj.comp q.continuous_extend
  have hΦ0 : Φ 0 = 0 := by simp only [hΦ, q.extend_zero, hprojx₀]
  have hΦtn : Φ tn = proj P := by simp only [hΦ, htnP]
  have hdpos : 0 < dOf G a := dOf_pos hGc ha0
  have hd4 : dOf G a ≤ a / 4 := min_le_right _ _
  have hd0 : dOf G a < d₀ G (a / 2) := by
    have := d₀_pos hGc (half_pos ha0)
    have : dOf G a ≤ d₀ G (a / 2) / 2 := min_le_left _ _
    linarith
  have hdist : dOf G a ≤ dist (Φ 0) (Φ tn) := by
    rw [hΦ0, hΦtn, dist_zero_left]
    have := Complex.abs_im_le_norm (proj P)
    rw [proj_im, abs_of_pos hP1] at this
    linarith
  -- the subpath `γ*` from `Pₙ` to its first point at distance `d(a)`
  obtain ⟨t', ht', hmaps, hdt'⟩ := exists_exit_subpath hΦc.continuousOn hdpos hdist
  have hsubI : uIcc tn t' ⊆ Icc 0 1 := by
    refine (uIcc_subset_uIcc_left ht').trans ?_
    rw [uIcc_comm, uIcc_of_le u.2.1]
    exact Icc_subset_Icc le_rfl u.2.2
  have hpts : ∀ τ ∈ uIcc tn t', q.extend τ ∈ γ ∧ q.extend τ ≠ x₀ ∧ q.extend τ ∈ openCube' ∧
      a / 2 ≤ q.extend τ 1 ∧ q.extend τ 1 ≤ a ∧ dist (Φ τ) (proj P) ≤ dOf G a := by
    intro τ hτ
    have hd : dist (Φ τ) (proj P) ≤ dOf G a := by
      have := hmaps hτ; rwa [mem_closedBall, hΦtn] at this
    have him : |(Φ τ - proj P).im| ≤ dist (Φ τ) (proj P) := by
      rw [dist_eq_norm]; exact Complex.abs_im_le_norm _
    simp only [Complex.sub_im, hΦ, proj_im] at him
    have him' := abs_le.1 (him.trans (hd.trans hd4))
    have hmemγ := hextγ τ (hsubI hτ)
    have hne : q.extend τ ≠ x₀ := fun h => by
      have : q.extend τ 1 = 0 := by rw [h, hx₀1]
      linarith
    exact ⟨hmemγ, hne, hcube _ hmemγ hne, by linarith, by linarith, hd⟩
  have hΓsub : Φ '' uIcc tn t' ⊆ {z | |z.re| ≤ 1 ∧ 0 < z.im ∧ z.im ≤ a} := by
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨-, -, hc, h1, h2, -⟩ := hpts τ hτ
    simp only [hΦ, mem_ofPred_eq, proj_re, proj_im]
    exact ⟨(abs_lt.2 hc.1).le, by linarith, h2⟩
  obtain ⟨_, ⟨τ₁, hτ₁, rfl⟩, _, ⟨τ₂, hτ₂, rfl⟩, hkk⟩ := hk a ⟨ha0, ha1⟩ _
    (isPreconnected_uIcc.image _ hΦc.continuousOn) hΓsub
    ⟨Φ tn, mem_image_of_mem _ left_mem_uIcc, Φ t', mem_image_of_mem _ right_mem_uIcc,
      (hdt'.symm.trans (dist_comm _ _)).le⟩
  -- the estimates at the two points `P'ₙ, P''ₙ` given by `thm:construct-C`
  have hPr : dist P x₀ < r := hδγ P hPγ (by linarith)
  have hest : ∀ τ ∈ uIcc tn t', dist (fOf s k (q.extend τ)) qv < ε / 2 ∧
      ‖G (proj (q.extend τ)) - G (proj P)‖ ≤ a / 2 ∧ |q.extend τ 2 - P 2| ≤ ε / 8 := by
    intro τ hτ
    obtain ⟨hmemγ, hne, hc, h1, h2, hd⟩ := hpts τ hτ
    have hdx : dist (q.extend τ) x₀ < r := hδγ _ hmemγ (h2.trans haδ)
    refine ⟨hC (hdx.trans_le (min_le_left _ _)) ⟨hmemγ, hne⟩, ?_, ?_⟩
    · have hK1 : proj (q.extend τ) ∈ Kt (a / 2) :=
        ⟨by rw [proj_re]; exact (abs_lt.2 hc.1).le, by rw [proj_im]; exact h1,
          by rw [proj_im]; linarith⟩
      have hK2 : proj P ∈ Kt (a / 2) :=
        ⟨by rw [proj_re]; exact (abs_lt.2 hPc.1).le, by rw [proj_im]; linarith,
          by rw [proj_im]; linarith⟩
      exact good_of_lt_d₀ hK1 hK2 (hd.trans_lt hd0)
    · have h3 := abs_coord_sub_le (q.extend τ) x₀ 2
      have h4 := abs_coord_sub_le P x₀ 2
      rw [hx₀2] at h3 h4
      have : r ≤ ε / 16 := min_le_right _ _
      refine (abs_sub_le _ b _).trans ?_
      rw [abs_sub_comm b]
      linarith
  obtain ⟨hf1, hg1, hz1⟩ := hest τ₁ hτ₁
  obtain ⟨hf2, hg2, hz2⟩ := hest τ₂ hτ₂
  set c := G (proj P) - (P 2 : ℂ) with hc
  have he : ∀ Q : EuclideanSpace ℝ (Fin 3), ‖G (proj Q) - G (proj P)‖ ≤ a / 2 →
      |Q 2 - P 2| ≤ ε / 8 → ‖(G (proj Q) - (Q 2 : ℂ)) - c‖ ≤ a / 2 + ε / 8 := by
    intro Q h1 h2
    have : (G (proj Q) - (Q 2 : ℂ)) - c =
        (G (proj Q) - G (proj P)) - ((Q 2 - P 2 : ℝ) : ℂ) := by
      rw [hc]; push_cast; ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hineq := cube1 c ((G (proj (q.extend τ₁)) - (q.extend τ₁ 2 : ℂ)) - c)
    ((G (proj (q.extend τ₂)) - (q.extend τ₂ 2 : ℂ)) - c) (k (proj (q.extend τ₁)))
    (k (proj (q.extend τ₂))) (hk2 _) (hk2 _)
  have hX : ∀ X : ℂ, c + (X - c) = X := fun X => by ring
  rw [hX, hX] at hineq
  have hff : ‖fOf s k (q.extend τ₁) - fOf s k (q.extend τ₂)‖ < ε := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_right (fOf s k (q.extend τ₁)) (fOf s k (q.extend τ₂)) qv]
  have hck : ε * 2 ≤ ‖c‖ * ‖k (proj (q.extend τ₁)) - k (proj (q.extend τ₂))‖ :=
    mul_le_mul hPε' hkk (by norm_num) (norm_nonneg _)
  have he1 := he _ hg1 hz1
  have he2 := he _ hg2 hz2
  have hfeq : ‖fOf s k (q.extend τ₁) - fOf s k (q.extend τ₂)‖ =
      ‖(G (proj (q.extend τ₁)) - (q.extend τ₁ 2 : ℂ)) * k (proj (q.extend τ₁)) -
        (G (proj (q.extend τ₂)) - (q.extend τ₂ 2 : ℂ)) * k (proj (q.extend τ₂))‖ := rfl
  linarith

/-- If `f` converges along an arc at `⟨0, 0, b⟩` in `K°`, then `b` is an asymptotic value of
`s`. -/
theorem isAsymptoticValue_of_mem {s k : ℂ → ℂ} (hsc : ContinuousOn s upper)
    (hk2 : ∀ z, ‖k z‖ ≤ 2)
    (hk : ∀ a ∈ Ioc (0 : ℝ) 1, ∀ γ : Set ℂ, IsPreconnected γ →
        γ ⊆ {z | |z.re| ≤ 1 ∧ 0 < z.im ∧ z.im ≤ a} →
        (∃ z₁ ∈ γ, ∃ z₂ ∈ γ, dOf (gOf s) a ≤ dist z₁ z₂) → ∃ z ∈ γ, ∃ w ∈ γ, 2 ≤ ‖k z - k w‖)
    {b : ℝ} (hmem : pt 0 0 b ∈ curvConvSet openCube' (frontier openCube') (fOf s k)) :
    IsAsymptoticValue upper s (b : ℂ) := by
  obtain ⟨-, γ, hγ, qv, hf⟩ := hmem
  have hcore := tendsto_sub_of_tendsto hsc hk2 hk hγ hf
  set x₀ := pt 0 0 b with hx₀
  have h2 : Tendsto (fun P : EuclideanSpace ℝ (Fin 3) => (P 2 : ℂ)) (𝓝[γ \ {x₀}] x₀)
      (𝓝 (b : ℂ)) := by
    have hc : Continuous fun P : EuclideanSpace ℝ (Fin 3) => (P 2 : ℂ) := by fun_prop
    have := (hc.tendsto x₀).mono_left (nhdsWithin_le_nhds (s := γ \ {x₀}))
    simpa [hx₀] using this
  have hg : Tendsto (fun P => gOf s (proj P)) (𝓝[γ \ {x₀}] x₀) (𝓝 (b : ℂ)) := by
    have := hcore.add h2
    simpa using this
  obtain ⟨e, ⟨q, hq, hrange⟩, hΩ⟩ := hγ
  have hinj := Path.injOn_extend_of_injective hq
  set σ : EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun P => ((P 0 / P 1 : ℝ) : ℂ) + (P 1 : ℂ) * Complex.I with hσ
  have hgσ : ∀ P, gOf s (proj P) = s (σ P) := fun P => by simp [gOf, hσ]
  set v : ℝ → ℂ := fun t => σ (q.extend (1 - t)) with hv
  have hpt : ∀ t ∈ Ico (0 : ℝ) 1, q.extend (1 - t) ∈ γ \ {x₀} := by
    intro t ht
    have h1 : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine ⟨by rw [← hrange, q.extend_apply h1]; exact mem_range_self _, fun h => ?_⟩
    have : q.extend (1 - t) = q.extend 0 := by rw [h, q.extend_zero]
    have := hinj h1 ⟨le_rfl, zero_le_one⟩ this
    linarith [ht.2]
  have hpos : ∀ t ∈ Ico (0 : ℝ) 1, 0 < q.extend (1 - t) 1 := fun t ht =>
    (hΩ (hpt t ht)).2.1.1
  have hlim : Tendsto (fun t => q.extend (1 - t)) (𝓝[<] 1) (𝓝[γ \ {x₀}] x₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous fun t : ℝ => q.extend (1 - t) :=
        q.continuous_extend.comp (by fun_prop)
      have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
      simpa using this
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact hpt t ⟨ht.1.le, ht.2⟩
  have hc0 : Continuous fun P : EuclideanSpace ℝ (Fin 3) => P 0 := by fun_prop
  have hc1 : Continuous fun P : EuclideanSpace ℝ (Fin 3) => P 1 := by fun_prop
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hne : q.extend (1 - t) 1 ≠ 0 := (hpos t ht).ne'
    have hσc : ContinuousAt σ (q.extend (1 - t)) :=
      (Complex.continuous_ofReal.continuousAt.comp
        (hc0.continuousAt.div hc1.continuousAt hne)).add
        (Complex.continuous_ofReal.continuousAt.comp hc1.continuousAt |>.mul continuousAt_const)
    have hcont : Continuous fun t : ℝ => q.extend (1 - t) :=
      q.continuous_extend.comp (by fun_prop)
    exact (ContinuousAt.comp (f := fun t : ℝ => q.extend (1 - t)) hσc
      hcont.continuousAt).continuousWithinAt
  · intro t ht
    show 0 < (σ _).im
    simpa [hσ] using hpos t ht
  · have h1 : Tendsto (fun t => q.extend (1 - t) 1) (𝓝[<] 1) (𝓝 0) := by
      have := (hc1.tendsto x₀).comp (tendsto_nhdsWithin_iff.1 hlim).1
      simp only [hx₀, pt_one] at this
      exact this
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have him : (v t).im = q.extend (1 - t) 1 := by simp [hv, hσ]
    rw [infDist_upper_compl (by rw [him]; exact (hpos t ⟨ht.1.le, ht.2⟩).le), him]
  · exact (hg.comp hlim).congr fun t => hgσ _

/-- A point asymptotic value `b` of `s` gives a point `⟨0, 0, b⟩` of curvilinear convergence of
`f`. -/
theorem mem_of_isPointAsymptoticValue {s k : ℂ → ℂ} (hk2 : ∀ z, ‖k z‖ ≤ 2) {b : ℝ}
    (hb : b ∈ Ioo (-1) 1) {p : ℂ} (hp : IsPointAsymptoticValue upper s p (b : ℂ)) :
    pt 0 0 b ∈ curvConvSet openCube' (frontier openCube') (fOf s k) := by
  obtain ⟨hpf, v, hvc, hvm, hvp, hvf⟩ := hp
  have hI01 : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
  have hpim : p.im = 0 := by
    have h1 : ¬ 0 < p.im := by
      have := hpf.2; rwa [isOpen_upper.interior_eq] at this
    have h2 : 0 ≤ p.im := closure_lt_subset_le continuous_const Complex.continuous_im hpf.1
    linarith [not_lt.1 h1]
  set c : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => pt ((v t).re * (v t).im) (v t).im b with hc
  have hre : Tendsto (fun t => (v t).re) (𝓝[<] 1) (𝓝 p.re) :=
    (Complex.continuous_re.tendsto p).comp hvp
  have him : Tendsto (fun t => (v t).im) (𝓝[<] 1) (𝓝 0) := by
    have := (Complex.continuous_im.tendsto p).comp hvp
    rwa [hpim] at this
  have hmul : Tendsto (fun t => (v t).re * (v t).im) (𝓝[<] 1) (𝓝 0) := by
    simpa using hre.mul him
  have hct : Tendsto c (𝓝[<] 1) (𝓝 (pt 0 0 b)) :=
    (continuous_pt.tendsto (0, 0, b)).comp
      (hmul.prodMk_nhds (him.prodMk_nhds tendsto_const_nhds))
  have hcube_ev : ∀ᶠ t in 𝓝[<] 1, c t ∈ openCube' := by
    filter_upwards [hmul.eventually (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) one_pos),
      him.eventually (eventually_lt_nhds one_pos), hI01] with t h1 h2 h3
    show c t 0 ∈ Ioo (-1 : ℝ) 1 ∧ c t 1 ∈ Ioo (0 : ℝ) 1 ∧ c t 2 ∈ Ioo (-1 : ℝ) 1
    simp only [hc, pt_zero, pt_one, pt_two]
    exact ⟨h1, ⟨hvm ⟨h3.1.le, h3.2⟩, h2⟩, hb⟩
  have hnot : pt 0 0 b ∉ openCube' := fun h => by
    have := h.2.1.1
    simp at this
  have hfr : pt 0 0 b ∈ frontier openCube' :=
    mem_frontier_of_tendsto isOpen_openCube' hct hcube_ev hnot
  have hfc : Tendsto (fOf s k ∘ c) (𝓝[<] 1) (𝓝 0) := by
    have hsb : Tendsto (fun t => s (v t) - (b : ℂ)) (𝓝[<] 1) (𝓝 0) := by
      have := hvf.sub_const (b : ℂ)
      simpa using this
    refine squeeze_zero_norm' ?_ (by simpa using hsb.norm.mul_const 2)
    filter_upwards [hI01] with t ht
    have hy : (v t).im ≠ 0 := (hvm ⟨ht.1.le, ht.2⟩).ne'
    have hg : gOf s (proj (c t)) = s (v t) := by
      simp only [gOf, hc, proj_re, proj_im, pt_zero, pt_one]
      congr 1
      rw [mul_div_cancel_right₀ _ hy]
      exact Complex.re_add_im (v t)
    have h2 : c t 2 = b := by simp [hc]
    show ‖(gOf s (proj (c t)) - (c t 2 : ℂ)) * k (proj (c t))‖ ≤ ‖s (v t) - b‖ * 2
    rw [hg, h2, norm_mul]
    exact mul_le_mul_of_nonneg_left (hk2 _) (norm_nonneg _)
  obtain ⟨t₀, ht₀0, ht₀1, ht₀⟩ := exists_Ico_of_eventually hcube_ev
  have hcc : ContinuousOn c (Ico t₀ 1) := by
    have hv' : ContinuousOn v (Ico t₀ 1) := hvc.mono (Ico_subset_Ico_left ht₀0)
    exact continuous_pt.comp_continuousOn
      (((Complex.continuous_re.comp_continuousOn hv').mul
        (Complex.continuous_im.comp_continuousOn hv')).prodMk
        ((Complex.continuous_im.comp_continuousOn hv').prodMk continuousOn_const))
  obtain ⟨g, hg1, hgle⟩ := exists_path_of_tendsto ht₀1 hcc hct
  obtain ⟨γ, -, hγ, hle⟩ := exists_arcAt_of_path (Ω := openCube') g (fun t ht => by
    obtain ⟨t', ht', heq⟩ := hg1 t ht
    rw [← heq]
    exact ht₀ t' ht') hnot
  exact ⟨hfr, γ, hγ, 0, tendsto_of_nhdsWithin_le_map (hle.trans hgle) hfc⟩

/-- `thm:cube`: a bounded continuous complex function in the open cube whose set of curvilinear
convergence is not a Borel set. The statement of `TJK.Cube.exists_not_measurableSet_curvConvSet`,
with `openCube'` (definitionally `TJK.Cube.openCube`). -/
theorem exists_not_measurableSet_curvConvSet' :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℂ, ContinuousOn f openCube' ∧
      Bornology.IsBounded (f '' openCube') ∧
      ¬ MeasurableSet (curvConvSet openCube' (frontier openCube') f) := by
  obtain ⟨s, hsc, hsb, hEq, hEnm⟩ := exists_s
  have hgc := continuousOn_gOf hsc
  obtain ⟨k, hkc, hkb, hk⟩ := Construct.exists_k (d := dOf (gOf s))
    (fun t ht => dOf_pos hgc ht.1) (dOf_mono _)
  have hk2 : ∀ z, ‖k z‖ ≤ 2 := fun z => (hkb z).trans
    (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2])
  refine ⟨fOf s k, ?_, ?_, ?_⟩
  · have hm1 : MapsTo proj openCube' upper := fun P hP => by
      show 0 < (proj P).im
      rw [proj_im]; exact hP.2.1.1
    have hm2 : MapsTo proj openCube' {z | 0 < z.im ∧ z.im ≤ 1} := fun P hP =>
      ⟨by rw [proj_im]; exact hP.2.1.1, by rw [proj_im]; exact hP.2.1.2.le⟩
    exact ((hgc.comp continuous_proj.continuousOn hm1).sub
      (by fun_prop : Continuous fun P : EuclideanSpace ℝ (Fin 3) => (P 2 : ℂ)).continuousOn).mul
      (hkc.comp continuous_proj.continuousOn hm2)
  · refine isBounded_iff_forall_norm_le.2 ⟨4, ?_⟩
    rintro _ ⟨P, hP, rfl⟩
    have h1 : ‖gOf s (proj P) - (P 2 : ℂ)‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h0 : ‖gOf s (proj P)‖ < 1 := hsb _
      have := abs_lt.2 hP.2.2
      linarith
    rw [fOf, norm_mul]
    nlinarith [hk2 (proj P), norm_nonneg (gOf s (proj P) - (P 2 : ℂ)), norm_nonneg (k (proj P))]
  · intro hF
    apply hEnm
    have hset : {b : ℝ | b ∈ Ioo (-1) 1 ∧ IsAsymptoticValue upper s (b : ℂ)} =
        (fun b => pt 0 0 b) ⁻¹' curvConvSet openCube' (frontier openCube') (fOf s k) ∩
          Ioo (-1) 1 := by
      ext b
      constructor
      · rintro ⟨hb, hasy⟩
        have : b ∈ {b : ℝ | b ∈ Ioo (-1) 1 ∧ ∃ p, IsPointAsymptoticValue upper s p (b : ℂ)} := by
          rw [← hEq]; exact ⟨hb, hasy⟩
        obtain ⟨-, p, hp⟩ := this
        exact ⟨mem_of_isPointAsymptoticValue hk2 hb hp, hb⟩
      · rintro ⟨hmem, hb⟩
        exact ⟨hb, isAsymptoticValue_of_mem hsc hk2 hk hmem⟩
    rw [hset]
    have hpc : Continuous fun b : ℝ => pt 0 0 b :=
      continuous_pt.comp (by fun_prop : Continuous fun b : ℝ => ((0 : ℝ), (0 : ℝ), b))
    exact (hpc.measurable hF).inter measurableSet_Ioo

end TJK.Cube
