import Mathlib
import TJK.Defs
import TJK.Plane.Basic

/-!
# Boundary functions of homeomorphisms of the disk (blueprint §E, `thm:homeo`)

* `lem:disjoint-arcs` (`disjoint_boundaryArcs`): components of the complements of two crosscuts
  that are disjoint have boundary arcs with disjoint interiors;
* `lem:homeo-values` (`Homeo.boundaryFn_mem_circle`): curvilinear limits of a homeomorphism of `𝔻`
  onto itself lie on `C`;
* `thm:homeo` (`Homeo.card_mul_le_of_subset_jumpSet`, `Homeo.ncard_jumpSet_mul_le`,
  `Homeo.exists_countable_continuousOn'`): Theorem 1 of
  Kaczynski's 1965 paper. The set `jumpSet E φ ε` of points of `E` at which `φ` has jumps of size
  `≥ ε` has at most `2π/ε` points, so `φ` is continuous off a countable set.
-/

namespace TJK

open _root_.Set Filter Topology Metric Function

open scoped Real

/-! ### Disjoint boundary arcs (`lem:disjoint-arcs`) -/

/-- If `p ∉ σ` lies in the closure of a component `U` of `𝔻 \ σ` (`σ` closed), then `U` contains
`𝔻 ∩ S(r, p)` for some `r > 0`. -/
theorem disc_inter_ball_subset_of_mem_closure {σ : Set ℂ} (hσ : IsClosed σ) {u p : ℂ}
    (hp : p ∈ closure (connectedComponentIn (disc \ σ) u)) (hpσ : p ∉ σ) :
    ∃ r > 0, disc ∩ ball p r ⊆ connectedComponentIn (disc \ σ) u := by
  obtain ⟨r, hr, hrσ⟩ := Metric.isOpen_iff.1 hσ.isOpen_compl p hpσ
  obtain ⟨w, hwU, hw⟩ := Metric.mem_closure_iff.1 hp r hr
  have hwD := connectedComponentIn_subset _ _ hwU
  refine ⟨r, hr, ?_⟩
  rw [connectedComponentIn_eq hwU]
  refine (convex_disc_inter_ball p r).isPreconnected.subset_connectedComponentIn
    ⟨hwD.1, by rw [mem_ball, dist_comm]; exact hw⟩ fun z hz => ⟨hz.1, fun h => hrσ hz.2 h⟩

/-- Points of the open arc `circleArcOpen θ ℓ` (`ℓ ≤ 2π`) differ from its endpoints. -/
theorem expI_ne_of_mem_Ioo {θ ℓ t : ℝ} (hℓ : ℓ ≤ 2 * π) (ht : t ∈ Ioo θ (θ + ℓ)) :
    expI t ≠ expI θ ∧ expI t ≠ expI (θ + ℓ) := by
  have h1 : 0 < Real.sin ((t - θ) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2])
  have h2 : 0 < Real.sin ((θ + ℓ - t) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := norm_expI_sub_expI θ t
    rw [h, sub_self, norm_zero, abs_of_pos h1] at this
    linarith
  · have := norm_expI_sub_expI t (θ + ℓ)
    rw [h, sub_self, norm_zero, abs_of_pos h2] at this
    linarith

/-- `lem:disjoint-arcs`: let `σ, τ` be closed sets meeting `C` only in the endpoints of the arcs
`circleArc θ ℓ`, `circleArc θ' ℓ'` (e.g. crosscuts, `fact:crosscut`), and let `U, V` be disjoint
components of `𝔻 \ σ`, `𝔻 \ τ` with `closure U ∩ C = circleArc θ ℓ`,
`closure V ∩ C = circleArc θ' ℓ'`. Then the interiors of the two arcs are disjoint. -/
theorem disjoint_boundaryArcs {σ τ : Set ℂ} {θ ℓ θ' ℓ' : ℝ} (hℓ : ℓ ≤ 2 * π) (hℓ' : ℓ' ≤ 2 * π)
    (hσ : IsClosed σ) (hτ : IsClosed τ) (hσC : σ ∩ circle ⊆ {expI θ, expI (θ + ℓ)})
    (hτC : τ ∩ circle ⊆ {expI θ', expI (θ' + ℓ')}) {u v : ℂ}
    (hUV : Disjoint (connectedComponentIn (disc \ σ) u) (connectedComponentIn (disc \ τ) v))
    (hU : closure (connectedComponentIn (disc \ σ) u) ∩ circle = circleArc θ ℓ)
    (hV : closure (connectedComponentIn (disc \ τ) v) ∩ circle = circleArc θ' ℓ') :
    Disjoint (circleArcOpen θ ℓ) (circleArcOpen θ' ℓ') := by
  refine disjoint_left.2 ?_
  rintro p ⟨t, ht, rfl⟩ ⟨t', ht', hp⟩
  have hpU : expI t ∈ closure (connectedComponentIn (disc \ σ) u) :=
    (hU.symm ▸ ⟨t, Ioo_subset_Icc_self ht, rfl⟩ : expI t ∈ closure _ ∩ circle).1
  have hpV : expI t ∈ closure (connectedComponentIn (disc \ τ) v) :=
    (hV.symm ▸ ⟨t', Ioo_subset_Icc_self ht', hp⟩ : expI t ∈ closure _ ∩ circle).1
  have hpσ : expI t ∉ σ := fun h => by
    rcases hσC ⟨h, expI_mem_circle t⟩ with h' | h'
    · exact (expI_ne_of_mem_Ioo hℓ ht).1 h'
    · exact (expI_ne_of_mem_Ioo hℓ ht).2 h'
  have hpτ : expI t ∉ τ := fun h => by
    rw [← hp] at h
    rcases hτC ⟨h, expI_mem_circle t'⟩ with h' | h'
    · exact (expI_ne_of_mem_Ioo hℓ' ht').1 h'
    · exact (expI_ne_of_mem_Ioo hℓ' ht').2 h'
  obtain ⟨r, hr, hrU⟩ := disc_inter_ball_subset_of_mem_closure hσ hpU hpσ
  obtain ⟨r', hr', hrV⟩ := disc_inter_ball_subset_of_mem_closure hτ hpV hpτ
  obtain ⟨w, hwU, hw⟩ := Metric.mem_closure_iff.1 hpU (min r r') (lt_min hr hr')
  have hwD := (connectedComponentIn_subset _ _ hwU).1
  have hw' : w ∈ ball (expI t) r' := by
    rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hw (min_le_right _ _)
  exact disjoint_left.1 hUV hwU (hrV ⟨hwD, hw'⟩)

/-- Two distinct points of `C` are `e^{iθ}` and `e^{i(θ + ℓ)}` with `0 < ℓ < 2π`. -/
theorem exists_angles_of_ne {a b : ℂ} (ha : a ∈ circle) (hb : b ∈ circle) (hab : a ≠ b) :
    ∃ θ ℓ : ℝ, 0 < ℓ ∧ ℓ < 2 * π ∧ expI θ = a ∧ expI (θ + ℓ) = b := by
  have h1 := expI_arg (mem_sphere_zero_iff_norm.1 ha)
  have h2 := expI_arg (mem_sphere_zero_iff_norm.1 hb)
  set d := toIcoMod Real.two_pi_pos 0 (Complex.arg b - Complex.arg a) with hd
  have hdI := toIcoMod_mem_Ico Real.two_pi_pos 0 (Complex.arg b - Complex.arg a)
  rw [← hd, zero_add] at hdI
  have hk := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 (Complex.arg b - Complex.arg a)
  rw [← hd, zsmul_eq_mul] at hk
  have he : expI (Complex.arg a + d) = b := by
    rw [← h2, ← expI_add_int_mul (Complex.arg a + d)
      (toIcoDiv Real.two_pi_pos 0 (Complex.arg b - Complex.arg a))]
    congr 1; linarith
  have hd0 : 0 < d := by
    refine lt_of_le_of_ne hdI.1 fun h0 => hab ?_
    rw [← he, ← h0, add_zero, h1]
  exact ⟨Complex.arg a, d, hd0, hdI.2, h1, he⟩

/-! ### Homeomorphisms of the disk -/

namespace Homeo

section

variable (e : disc ≃ₜ disc)

open scoped Classical in
/-- The inverse of `e : 𝔻 ≃ₜ 𝔻` as a map `ℂ → ℂ` (extended by `0` off `𝔻`). -/
noncomputable def inv (w : ℂ) : ℂ := if h : w ∈ disc then (e.symm ⟨w, h⟩ : ℂ) else 0

theorem inv_mem {w : ℂ} (hw : w ∈ disc) : inv e w ∈ disc := by
  rw [inv, dif_pos hw]; exact (e.symm _).2

theorem continuousOn_inv : ContinuousOn (inv e) disc := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : disc.domRestrict (inv e) = fun w => (e.symm w : ℂ) := funext fun w => by
    simp only [domRestrict_apply, inv, dif_pos w.2]
  rw [this]
  exact continuous_subtype_val.comp e.symm.continuous

variable {e} {f : ℂ → ℂ} (hfe : ∀ z : disc, f z = e z)
include hfe

theorem mapsTo_disc {z : ℂ} (hz : z ∈ disc) : f z ∈ disc := by
  rw [show f z = e ⟨z, hz⟩ from hfe ⟨z, hz⟩]; exact (e _).2

theorem inv_apply {z : ℂ} (hz : z ∈ disc) : inv e (f z) = z := by
  have h1 : (⟨f z, mapsTo_disc hfe hz⟩ : disc) = e ⟨z, hz⟩ := Subtype.ext (hfe ⟨z, hz⟩)
  rw [inv, dif_pos (mapsTo_disc hfe hz), h1, Homeomorph.symm_apply_apply]

theorem apply_inv {w : ℂ} (hw : w ∈ disc) : f (inv e w) = w := by
  rw [inv, dif_pos hw, hfe, Homeomorph.apply_symm_apply]

theorem injOn_disc : InjOn f disc := fun z hz w hw h => by
  rw [← inv_apply hfe hz, h, inv_apply hfe hw]

theorem continuousOn_disc : ContinuousOn f disc := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : disc.domRestrict f = fun z => (e z : ℂ) := funext hfe
  rw [this]
  exact continuous_subtype_val.comp e.continuous

/-- `lem:homeo-values`: limits of `f` along arcs at points of `C` lie on `C`. -/
theorem boundaryFn_mem_circle {x q : ℂ} (hx : x ∈ circle) {γ : Set ℂ} (hγ : IsArcAt disc x γ)
    (hq : Tendsto f (𝓝[γ \ {x}] x) (𝓝 q)) : q ∈ circle := by
  have := hγ.nhdsWithin_neBot
  have hev : ∀ᶠ z in 𝓝[γ \ {x}] x, z ∈ disc := by
    obtain ⟨b, -, hΩ⟩ := hγ
    exact mem_of_superset self_mem_nhdsWithin hΩ
  have hq1 : q ∈ closure disc :=
    mem_closure_of_tendsto hq (hev.mono fun z hz => mapsTo_disc hfe hz)
  rw [closure_ball 0 one_ne_zero] at hq1
  rcases (mem_closedBall_zero_iff.1 hq1).lt_or_eq with h | h
  · exfalso
    have hqD : q ∈ disc := mem_ball_zero_iff.2 h
    have h1 : Tendsto (inv e ∘ f) (𝓝[γ \ {x}] x) (𝓝 (inv e q)) :=
      ((continuousOn_inv e).continuousAt (isOpen_ball.mem_nhds hqD)).tendsto.comp hq
    have h2 : Tendsto (inv e ∘ f) (𝓝[γ \ {x}] x) (𝓝 x) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
        (hev.mono fun z hz => (inv_apply hfe hz).symm)
    have hxD : x ∈ disc := tendsto_nhds_unique h2 h1 ▸ inv_mem e hqD
    exact (mem_ball_zero_iff.1 hxD).ne (mem_sphere_zero_iff_norm.1 hx)
  · exact mem_sphere_zero_iff_norm.2 h

end

end Homeo

/-! ### A crosscut near a point (`thm:homeo`, first step) -/

/-- If `σ ⊆ β ∪ K` with `K` closed and `x ∉ K`, limits along `β \ {x}` at `x` are limits along
`σ \ {x}`. -/
theorem tendsto_nhdsWithin_of_subset_union {Y : Type*} {σ β K : Set ℂ} {x : ℂ} (hK : IsClosed K)
    (hxK : x ∉ K) (hσ : σ ⊆ β ∪ K) {f : ℂ → Y} {l : Filter Y} (h : Tendsto f (𝓝[β \ {x}] x) l) :
    Tendsto f (𝓝[σ \ {x}] x) l :=
  h.mono_left (nhdsWithin_le_of_mem (mem_nhdsWithin.2 ⟨Kᶜ, hK.isOpen_compl, hxK,
    fun _ ⟨hzK, hzσ, hzx⟩ => ⟨(hσ hzσ).resolve_right hzK, hzx⟩⟩))

theorem not_mem_disc_of_mem_circle {x : ℂ} (hx : x ∈ circle) : x ∉ disc := fun h =>
  (mem_ball_zero_iff.1 h).ne (mem_sphere_zero_iff_norm.1 hx)

/-- `thm:homeo`, *a crosscut near `x`*: if `f → a` along an arc at `x ∈ C` and `f → a'` along an
arc at `x' ∈ C`, `0 < |x' - x| < δ/2`, there is a crosscut `σ` from `x` to `x'` inside a closed ball
`S̄(δ', x)`, `δ' < δ`, along which `f → a` at `x` and `f → a'` at `x'`. It is a simple arc in the
union of two subarcs of the given arcs and a segment (`fact:tietze-arc`). -/
theorem exists_crosscut_near {f : ℂ → ℂ} {x x' : ℂ} (hx : x ∈ circle) (hx' : x' ∈ circle)
    (hxx' : x ≠ x') {γ γ' : Set ℂ} (hγ : IsArcAt disc x γ) (hγ' : IsArcAt disc x' γ') {a a' : ℂ}
    (ha : Tendsto f (𝓝[γ \ {x}] x) (𝓝 a)) (ha' : Tendsto f (𝓝[γ' \ {x'}] x') (𝓝 a')) {δ : ℝ}
    (hd : dist x' x < δ / 2) :
    ∃ σ, IsArc σ x x' ∧ σ \ {x, x'} ⊆ disc ∧ (∃ δ', 0 < δ' ∧ δ' < δ ∧ σ ⊆ closedBall x δ') ∧
      Tendsto f (𝓝[σ \ {x}] x) (𝓝 a) ∧ Tendsto f (𝓝[σ \ {x'}] x') (𝓝 a') := by
  have hxD := not_mem_disc_of_mem_circle hx
  have hx'D := not_mem_disc_of_mem_circle hx'
  have hδ : 0 < δ := by linarith [dist_nonneg (x := x') (y := x)]
  obtain ⟨β, hβγ, hβ, hβf⟩ := hγ.exists_subarc_subset (ball_mem_nhds x (half_pos hδ))
  obtain ⟨β', hβγ', hβ', hβf'⟩ := hγ'.exists_subarc_subset (ball_mem_nhds x' (half_pos hδ))
  obtain ⟨u, hβu, hβD⟩ := hβ
  obtain ⟨v, hβv, hβD'⟩ := hβ'
  obtain ⟨p, hp, hpr⟩ := id hβu
  obtain ⟨p', hp', hpr'⟩ := id hβv
  have hu : u ∈ disc := hβD ⟨hβu.right_mem, fun h => hβu.ne (mem_singleton_iff.1 h).symm⟩
  have hv : v ∈ disc := hβD' ⟨hβv.right_mem, fun h => hβv.ne (mem_singleton_iff.1 h).symm⟩
  have hβb : β ⊆ ball x δ := fun z hz => ball_subset_ball (half_le_self hδ.le) (hβγ hz).2
  have hβb' : β' ⊆ ball x δ := fun z hz => by
    have := (hβγ' hz).2
    rw [mem_ball] at this ⊢
    linarith [dist_triangle z x' x]
  have hSD : segment ℝ u v ⊆ disc := (convex_ball 0 1).segment_subset hu hv
  have hSb : segment ℝ u v ⊆ ball x δ :=
    (convex_ball x δ).segment_subset (hβb hβu.right_mem) (hβb' hβv.right_mem)
  have hSc : IsCompact (segment ℝ u v) :=
    Path.range_segment u v ▸ isCompact_range (Path.segment u v).continuous
  set g : Path x x' := p.trans ((Path.segment u v).trans p'.symm) with hg
  have hgr : range g = β ∪ (segment ℝ u v ∪ β') := by
    rw [hg, Path.trans_range, Path.trans_range, Path.symm_range, Path.range_segment, hpr, hpr']
  obtain ⟨σ, hσg, hσ⟩ := exists_arc_in_path g hxx'
  rw [hgr] at hσg
  have hσb : σ ⊆ ball x δ := hσg.trans (union_subset hβb (union_subset hSb hβb'))
  obtain ⟨δ', hδ'δ, hσδ'⟩ := exists_lt_subset_ball hσ.isCompact.isClosed hσb
  have hδ'0 : 0 < δ' := by
    have := hσδ' hσ.left_mem
    rwa [mem_ball, dist_self] at this
  refine ⟨σ, hσ, ?_, ⟨δ', hδ'0, hδ'δ, hσδ'.trans ball_subset_closedBall⟩, ?_, ?_⟩
  · rintro z ⟨hz, hzxx⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzxx
    rcases hσg hz with h | h | h
    · exact hβD ⟨h, hzxx.1⟩
    · exact hSD h
    · exact hβD' ⟨h, hzxx.2⟩
  · refine tendsto_nhdsWithin_of_subset_union (K := segment ℝ u v ∪ β')
      (hSc.union (hpr' ▸ isCompact_range p'.continuous)).isClosed ?_ hσg (hβf ▸ ha)
    rintro (h | h)
    · exact hxD (hSD h)
    · exact hxD (hβD' ⟨h, hxx'⟩)
  · refine tendsto_nhdsWithin_of_subset_union (K := β ∪ segment ℝ u v)
      ((hpr ▸ isCompact_range p.continuous).union hSc).isClosed ?_ ?_ (hβf' ▸ ha')
    · rintro (h | h)
      · exact hx'D (hβD ⟨h, hxx'.symm⟩)
      · exact hx'D (hSD h)
    · intro z hz
      rcases hσg hz with h | h | h
      exacts [Or.inr (Or.inl h), Or.inr (Or.inr h), Or.inl h]

/-- `thm:homeo`, *the small component*: if a crosscut `σ` from `x` to `x'` lies in `S̄(δ', x)`,
`0 < δ' < 2`, some component of `𝔻 \ σ` lies in `S̄(δ', x)`. Indeed the connected set
`𝔻 \ S̄(δ', x)` (`lem:disc-geometry` (b)) misses `σ`, so lies in one of the two components
(`fact:crosscut`); the other one misses it. -/
theorem exists_component_subset_closedBall {σ : Set ℂ} {x x' : ℂ} (hx : x ∈ circle)
    (hx' : x' ∈ circle) (hxx' : x ≠ x') (hσ : IsArc σ x x') (hσD : σ \ {x, x'} ⊆ disc) {δ' : ℝ}
    (h0 : 0 < δ') (h2 : δ' < 2) (hσb : σ ⊆ closedBall x δ') :
    ∃ z ∈ disc \ σ, connectedComponentIn (disc \ σ) z ⊆ closedBall x δ' := by
  obtain ⟨θ, ℓ, hℓ0, hℓ2, rfl, rfl⟩ := exists_angles_of_ne hx hx' hxx'
  obtain ⟨z₁, hz₁, z₂, hz₂, hdisj, hall, -, -⟩ := crosscut_theorem hℓ0 hℓ2 hσ hσD
  obtain ⟨hD, -⟩ := isConnected_disc_diff_closedBall hx h0 h2
  obtain ⟨d, hd⟩ := hD.nonempty
  have hDσ : disc \ closedBall (expI θ) δ' ⊆ disc \ σ := fun z hz => ⟨hz.1, fun h => hz.2 (hσb h)⟩
  have hDc := hD.isPreconnected.subset_connectedComponentIn hd hDσ
  have key : ∀ z, Disjoint (connectedComponentIn (disc \ σ) z) (connectedComponentIn (disc \ σ) d) →
      connectedComponentIn (disc \ σ) z ⊆ closedBall (expI θ) δ' := fun z hz w hw => by
    by_contra hwb
    exact disjoint_left.1 hz hw (hDc ⟨(connectedComponentIn_subset _ _ hw).1, hwb⟩)
  rcases hall d (hDσ hd) with h | h
  · exact ⟨z₂, hz₂, key z₂ (h ▸ hdisj.symm)⟩
  · exact ⟨z₁, hz₁, key z₁ (h ▸ hdisj)⟩

/-- `thm:homeo`, *the arc of a component*: if `τ` is a crosscut from `a` to `a'`, the closure of
each component of `𝔻 \ τ` meets `C` in an arc `circleArc θ ℓ`, `0 < ℓ < 2π`, with endpoints
`a, a'` (`fact:crosscut`). -/
theorem exists_boundaryArc_of_crosscut {τ : Set ℂ} {a a' : ℂ} (ha : a ∈ circle)
    (ha' : a' ∈ circle) (haa' : a ≠ a') (hτ : IsArc τ a a') (hτD : τ \ {a, a'} ⊆ disc) {w : ℂ}
    (hw : w ∈ disc \ τ) :
    ∃ θ ℓ : ℝ, 0 < ℓ ∧ ℓ < 2 * π ∧ τ ∩ circle ⊆ {expI θ, expI (θ + ℓ)} ∧
      closure (connectedComponentIn (disc \ τ) w) ∩ circle = circleArc θ ℓ ∧
      ‖expI (θ + ℓ) - expI θ‖ = dist a a' := by
  obtain ⟨θ, ℓ, hℓ0, hℓ2, rfl, rfl⟩ := exists_angles_of_ne ha ha' haa'
  obtain ⟨z₁, -, z₂, -, -, hall, hfr₁, hfr₂⟩ := crosscut_theorem hℓ0 hℓ2 hτ hτD
  have hτC : τ ∩ circle ⊆ {expI θ, expI (θ + ℓ)} := fun y hy => by
    by_contra h
    exact not_mem_disc_of_mem_circle hy.2 (hτD ⟨hy.1, h⟩)
  have hsub : ∀ z, connectedComponentIn (disc \ τ) z ⊆ disc := fun z =>
    (connectedComponentIn_subset _ _).trans sdiff_subset
  have he : expI (θ + ℓ + (2 * π - ℓ)) = expI θ := by
    rw [show θ + ℓ + (2 * π - ℓ) = θ + ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      expI_add_int_mul]
  rcases hall w hw with h | h
  · refine ⟨θ, ℓ, hℓ0, hℓ2, hτC, ?_, by rw [dist_comm, dist_eq_norm]⟩
    rw [h]
    exact (closure_inter_circle_of_frontier hℓ0.le hτD (hsub z₁) hfr₁).1
  · refine ⟨θ + ℓ, 2 * π - ℓ, by linarith, by linarith, ?_, ?_, ?_⟩
    · rw [he, pair_comm]; exact hτC
    · rw [h]
      refine (closure_inter_circle_of_frontier (by linarith) ?_ (hsub z₂) hfr₂).1
      rw [he, pair_comm]; exact hτD
    · rw [he, dist_eq_norm]

namespace Homeo

variable {e : disc ≃ₜ disc} {f : ℂ → ℂ}

/-- `thm:homeo`, *images*: if `σ` is a crosscut from `x` to `x'` and `f → a`, `f → a'` along `σ` at
its ends, with `a ≠ a'` on `C`, then `τ = f(σ ∩ 𝔻) ∪ {a, a'}` is a crosscut from `a` to `a'`, and
`f` maps each component of `𝔻 \ σ` onto a component of `𝔻 \ τ` (we only need `⊇`). -/
theorem exists_image_crosscut (hfe : ∀ z : disc, f z = e z) {σ : Set ℂ} {x x' a a' : ℂ}
    (hx : x ∈ circle) (hx' : x' ∈ circle) (hxx' : x ≠ x') (hσ : IsArc σ x x')
    (hσD : σ \ {x, x'} ⊆ disc) (ha : a ∈ circle) (ha' : a' ∈ circle) (haa' : a ≠ a')
    (hfa : Tendsto f (𝓝[σ \ {x}] x) (𝓝 a)) (hfa' : Tendsto f (𝓝[σ \ {x'}] x') (𝓝 a')) :
    ∃ τ, IsArc τ a a' ∧ τ \ {a, a'} ⊆ disc ∧ ∀ z ∈ disc \ σ, f z ∈ disc \ τ ∧
      connectedComponentIn (disc \ τ) (f z) ⊆ f '' connectedComponentIn (disc \ σ) z := by
  have hxD := not_mem_disc_of_mem_circle hx
  have hx'D := not_mem_disc_of_mem_circle hx'
  have haD := not_mem_disc_of_mem_circle ha
  have ha'D := not_mem_disc_of_mem_circle ha'
  set G := update (update f x a) x' a' with hG
  have hGx : G x = a := by rw [hG, update_of_ne hxx', update_self]
  have hGx' : G x' = a' := by rw [hG, update_self]
  have hGD : ∀ z ∈ disc, G z = f z := fun z hz => by
    rw [hG, update_of_ne (fun h : z = x' => hx'D (h ▸ hz)),
      update_of_ne (fun h : z = x => hxD (h ▸ hz))]
  have hcase : ∀ y ∈ σ, y = x ∨ y = x' ∨ y ∈ disc := fun y hy => by
    by_cases h1 : y = x
    · exact Or.inl h1
    by_cases h2 : y = x'
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hσD ⟨hy, by simp [h1, h2]⟩))
  have hGcont : ContinuousOn G σ := by
    intro z hz
    rcases hcase z hz with rfl | rfl | hzD
    · rw [← continuousWithinAt_sdiff_singleton, ContinuousWithinAt, hGx]
      refine hfa.congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hxx')] with w hw hw'
      rw [hG, update_of_ne hw', update_of_ne hw.2]
    · rw [← continuousWithinAt_sdiff_singleton, ContinuousWithinAt, hGx']
      refine hfa'.congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (Ne.symm hxx'))] with w hw hw'
      rw [hG, update_of_ne hw.2, update_of_ne hw']
    · refine ContinuousAt.continuousWithinAt ?_
      have hev : G =ᶠ[𝓝 z] f := eventually_of_mem (isOpen_ball.mem_nhds hzD) hGD
      exact ((continuousOn_disc hfe).continuousAt (isOpen_ball.mem_nhds hzD)).congr hev.symm
  have hGinj : InjOn G σ := by
    intro z hz w hw h
    rcases hcase z hz with rfl | rfl | hzD <;> rcases hcase w hw with rfl | rfl | hwD
    · rfl
    · rw [hGx, hGx'] at h; exact absurd h haa'
    · rw [hGx, hGD w hwD] at h; exact absurd (h ▸ mapsTo_disc hfe hwD) haD
    · rw [hGx', hGx] at h; exact absurd h.symm haa'
    · rfl
    · rw [hGx', hGD w hwD] at h; exact absurd (h ▸ mapsTo_disc hfe hwD) ha'D
    · rw [hGx, hGD z hzD] at h; exact absurd (h.symm ▸ mapsTo_disc hfe hzD) haD
    · rw [hGx', hGD z hzD] at h; exact absurd (h.symm ▸ mapsTo_disc hfe hzD) ha'D
    · rw [hGD z hzD, hGD w hwD] at h; exact injOn_disc hfe hzD hwD h
  have hτ := hσ.image hGcont hGinj
  rw [hGx, hGx'] at hτ
  have hmem : ∀ z ∈ disc, f z ∈ G '' σ → z ∈ σ := by
    rintro z hzD ⟨y, hy, hyz⟩
    rcases hcase y hy with rfl | rfl | hyD
    · rw [hGx] at hyz; exact absurd (hyz ▸ mapsTo_disc hfe hzD) haD
    · rw [hGx'] at hyz; exact absurd (hyz ▸ mapsTo_disc hfe hzD) ha'D
    · rw [hGD y hyD] at hyz; exact injOn_disc hfe hyD hzD hyz ▸ hy
  refine ⟨G '' σ, hτ, ?_, fun z hz => ?_⟩
  · rintro _ ⟨⟨y, hy, rfl⟩, hya⟩
    rcases hcase y hy with rfl | rfl | hyD
    · exact absurd (by simp [hGx]) hya
    · exact absurd (by simp [hGx']) hya
    · rw [hGD y hyD]; exact mapsTo_disc hfe hyD
  have hfz : f z ∈ disc \ G '' σ := ⟨mapsTo_disc hfe hz.1, fun h => hz.2 (hmem z hz.1 h)⟩
  refine ⟨hfz, fun w hw => ?_⟩
  have hV := connectedComponentIn_subset (disc \ G '' σ) (f z)
  have hpre : IsPreconnected (inv e '' connectedComponentIn (disc \ G '' σ) (f z)) :=
    isPreconnected_connectedComponentIn.image _ ((continuousOn_inv e).mono (hV.trans sdiff_subset))
  have hsub : inv e '' connectedComponentIn (disc \ G '' σ) (f z) ⊆ disc \ σ := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hV hy
    refine ⟨inv_mem e hy'.1, fun h => hy'.2 ⟨inv e y, h, ?_⟩⟩
    rw [hGD _ (inv_mem e hy'.1), apply_inv hfe hy'.1]
  have hz' : z ∈ inv e '' connectedComponentIn (disc \ G '' σ) (f z) :=
    ⟨f z, mem_connectedComponentIn hfz, inv_apply hfe hz.1⟩
  exact ⟨inv e w, hpre.subset_connectedComponentIn hz' hsub ⟨w, hw, rfl⟩, apply_inv hfe (hV hw).1⟩

end Homeo

/-- The points of `E` at which `φ` has jumps of size at least `ε` (relative to `E`): the set `S_ε`
of `thm:homeo`. -/
def jumpSet (E : Set ℂ) (φ : ℂ → ℂ) (ε : ℝ) : Set ℂ :=
  {x | x ∈ E ∧ ∀ δ > 0, ∃ x' ∈ E, 0 < dist x' x ∧ dist x' x < δ ∧ ε ≤ dist (φ x') (φ x)}

namespace Homeo

variable {e : disc ≃ₜ disc} {f : ℂ → ℂ}

/-- `thm:homeo`, one jump: if `f → a` along an arc at `x ∈ C`, `f → a' ≠ a` along an arc at
`x' ∈ C`, and `0 < |x' - x| < δ/2 ≤ 1`, there is a crosscut `τ` and a component `V` of `𝔻 \ τ`
with `V ⊆ f(𝔻 ∩ S(δ, x))`, such that `closure V ∩ C` is an arc of chord length `|a - a'|` whose
endpoints are the only points of `τ` on `C`. -/
theorem exists_boundaryArc (hfe : ∀ z : disc, f z = e z) {x x' : ℂ} (hx : x ∈ circle)
    (hx' : x' ∈ circle) (hxx' : x ≠ x') {γ γ' : Set ℂ} (hγ : IsArcAt disc x γ)
    (hγ' : IsArcAt disc x' γ') {a a' : ℂ} (ha : Tendsto f (𝓝[γ \ {x}] x) (𝓝 a))
    (ha' : Tendsto f (𝓝[γ' \ {x'}] x') (𝓝 a')) (haa' : a ≠ a') {δ : ℝ} (hδ : δ ≤ 2)
    (hd : dist x' x < δ / 2) :
    ∃ τ : Set ℂ, ∃ v : ℂ, ∃ θ ℓ : ℝ, IsClosed τ ∧ 0 < ℓ ∧ ℓ < 2 * π ∧
      τ ∩ circle ⊆ {expI θ, expI (θ + ℓ)} ∧
      closure (connectedComponentIn (disc \ τ) v) ∩ circle = circleArc θ ℓ ∧
      ‖expI (θ + ℓ) - expI θ‖ = dist a a' ∧
      connectedComponentIn (disc \ τ) v ⊆ f '' (disc ∩ ball x δ) := by
  have haC := boundaryFn_mem_circle hfe hx hγ ha
  have ha'C := boundaryFn_mem_circle hfe hx' hγ' ha'
  obtain ⟨σ, hσ, hσD, ⟨δ', hδ'0, hδ'δ, hσb⟩, hfa, hfa'⟩ :=
    exists_crosscut_near hx hx' hxx' hγ hγ' ha ha' hd
  obtain ⟨z, hz, hzb⟩ :=
    exists_component_subset_closedBall hx hx' hxx' hσ hσD hδ'0 (by linarith) hσb
  obtain ⟨τ, hτ, hτD, himg⟩ :=
    exists_image_crosscut hfe hx hx' hxx' hσ hσD haC ha'C haa' hfa hfa'
  obtain ⟨hfz, hsub⟩ := himg z hz
  obtain ⟨θ, ℓ, hℓ0, hℓ2, hτC, hcl, hnorm⟩ :=
    exists_boundaryArc_of_crosscut haC ha'C haa' hτ hτD hfz
  refine ⟨τ, f z, θ, ℓ, hτ.isCompact.isClosed, hℓ0, hℓ2, hτC, hcl, hnorm,
    hsub.trans (image_mono fun w hw => ⟨(connectedComponentIn_subset _ _ hw).1, ?_⟩)⟩
  exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (hzb hw)) hδ'δ)

/-- `thm:homeo`, quantitative form: the jump set `S_ε` of a boundary function of a homeomorphism
of `𝔻` onto itself has at most `2π/ε` points; i.e. every finite subset `s ⊆ S_ε` has
`|s| ε ≤ 2π`. -/
theorem card_mul_le_of_subset_jumpSet (hfe : ∀ z : disc, f z = e z) {E : Set ℂ}
    (hE : E ⊆ circle) {φ : ℂ → ℂ} (hφ : IsBoundaryFunction disc f E φ) {ε : ℝ} (hε : 0 < ε)
    (s : Finset ℂ) (hs : ↑s ⊆ jumpSet E φ ε) : (s.card : ℝ) * ε ≤ 2 * π := by
  -- the balls `S(δ, x)`, `x ∈ s`, are pairwise disjoint
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * δ ≤ dist x y := by
    rw [eventually_all_finset]
    intro x _
    rw [eventually_all_finset]
    intro y _
    by_cases hxy : x = y
    · exact Eventually.of_forall fun _ h => absurd hxy h
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (dist_pos.2 hxy))] with δ hδ _
      linarith [hδ.2]
  obtain ⟨δ, hsep, hδ⟩ := (hev.and (Ioo_mem_nhdsGT one_pos)).exists
  have key : ∀ x, ∃ τ : Set ℂ, ∃ v : ℂ, ∃ θ ℓ : ℝ, x ∈ s → (IsClosed τ ∧ 0 < ℓ ∧ ℓ < 2 * π ∧
      τ ∩ circle ⊆ {expI θ, expI (θ + ℓ)} ∧
      closure (connectedComponentIn (disc \ τ) v) ∩ circle = circleArc θ ℓ ∧
      ε ≤ ‖expI (θ + ℓ) - expI θ‖ ∧
      connectedComponentIn (disc \ τ) v ⊆ f '' (disc ∩ ball x δ)) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨hxE, hjump⟩ := hs hx
      obtain ⟨x', hx'E, hpos, hlt, hge⟩ := hjump (δ / 2) (half_pos hδ.1)
      obtain ⟨γ, hγ, hfγ⟩ := hφ x hxE
      obtain ⟨γ', hγ', hfγ'⟩ := hφ x' hx'E
      have hxx' : x ≠ x' := fun h => by rw [h, dist_self] at hpos; exact lt_irrefl _ hpos
      have haa' : φ x ≠ φ x' := fun h => by rw [h, dist_self] at hge; linarith
      obtain ⟨τ, v, θ, ℓ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_boundaryArc hfe (hE hxE)
        (hE hx'E) hxx' hγ hγ' hfγ hfγ' haa' (by linarith [hδ.2]) hlt
      exact ⟨τ, v, θ, ℓ, fun _ => ⟨h1, h2, h3, h4, h5, by rw [h6, dist_comm]; exact hge, h7⟩⟩
    · exact ⟨∅, 0, 0, 0, fun h => absurd h hx⟩
  choose τ v θ ℓ hP using key
  refine TJK.card_mul_le_two_pi s θ ℓ (fun i hi => ⟨(hP i hi).2.1.le, (hP i hi).2.2.1.le⟩) ?_
    (fun i hi => (hP i hi).2.2.2.2.2.1)
  intro i hi j hj hij
  obtain ⟨hτi, -, hℓi, hτCi, hcli, -, hsubi⟩ := hP i hi
  obtain ⟨hτj, -, hℓj, hτCj, hclj, -, hsubj⟩ := hP j hj
  refine disjoint_boundaryArcs hℓi.le hℓj.le hτi hτj hτCi hτCj ?_ hcli hclj
  refine disjoint_left.2 fun w hwi hwj => ?_
  obtain ⟨z₁, ⟨hz₁D, hz₁b⟩, rfl⟩ := hsubi hwi
  obtain ⟨z₂, ⟨hz₂D, hz₂b⟩, hz₂⟩ := hsubj hwj
  obtain rfl := injOn_disc hfe hz₂D hz₁D hz₂
  have := hsep i hi j hj hij
  rw [mem_ball] at hz₁b hz₂b
  linarith [dist_triangle i z₂ j, dist_comm z₂ i]

/-- `thm:homeo`: the jump sets are finite. -/
theorem finite_jumpSet (hfe : ∀ z : disc, f z = e z) {E : Set ℂ} (hE : E ⊆ circle) {φ : ℂ → ℂ}
    (hφ : IsBoundaryFunction disc f E φ) {ε : ℝ} (hε : 0 < ε) : (jumpSet E φ ε).Finite := by
  by_contra h
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq h (⌈2 * π / ε⌉₊ + 1)
  have h1 := card_mul_le_of_subset_jumpSet hfe hE hφ hε t hts
  rw [htc] at h1
  push_cast at h1
  have h2 := Nat.le_ceil (2 * π / ε)
  rw [div_le_iff₀ hε] at h2
  nlinarith

/-- `thm:homeo`, quantitative form: `|S_ε| ε ≤ 2π`. -/
theorem ncard_jumpSet_mul_le (hfe : ∀ z : disc, f z = e z) {E : Set ℂ} (hE : E ⊆ circle)
    {φ : ℂ → ℂ} (hφ : IsBoundaryFunction disc f E φ) {ε : ℝ} (hε : 0 < ε) :
    ((jumpSet E φ ε).ncard : ℝ) * ε ≤ 2 * π := by
  have hfin := finite_jumpSet hfe hE hφ hε
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact card_mul_le_of_subset_jumpSet hfe hE hφ hε _ (by simp)

/-- `thm:homeo` (Theorem 1 of Kaczynski's 1965 paper): a boundary function of a homeomorphism of
the disk onto itself is continuous off a countable set. -/
theorem exists_countable_continuousOn' (e : disc ≃ₜ disc) (f : ℂ → ℂ)
    (hfe : ∀ z : disc, f z = e z) (E : Set ℂ) (hE : E ⊆ circle) (φ : ℂ → ℂ)
    (hφ : IsBoundaryFunction disc f E φ) :
    ∃ N ⊆ E, N.Countable ∧ ContinuousOn φ (E \ N) := by
  refine ⟨⋃ k : ℕ, jumpSet E φ (1 / (k + 1)), iUnion_subset fun k x hx => hx.1,
    countable_iUnion fun k => (finite_jumpSet hfe hE hφ (by positivity)).countable, ?_⟩
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hxk : ¬ ∀ δ > 0, ∃ x' ∈ E, 0 < dist x' x ∧ dist x' x < δ ∧
      1 / ((k : ℝ) + 1) ≤ dist (φ x') (φ x) := fun h => hx.2 (mem_iUnion.2 ⟨k, hx.1, h⟩)
  push Not at hxk
  obtain ⟨δ, hδ, hδx⟩ := hxk
  refine ⟨δ, hδ, fun {y} hy hyx => ?_⟩
  rcases eq_or_ne y x with rfl | hne
  · rw [dist_self]; exact hε
  · exact (hδx y hy.1 (dist_pos.2 hne) hyx).trans hk

end Homeo

end TJK
