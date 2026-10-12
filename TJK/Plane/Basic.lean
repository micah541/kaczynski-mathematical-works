import Mathlib
import TJK.Defs
import TJK.Plane.Arc
import TJK.Plane.JordanCrosscut

/-!
# Arcs, curvilinear limits, charts and transfer (blueprint §C, fact-free parts)

* `fact:tietze-arc` (`exists_arc_in_path`, imported, `sorry`) and `cor:path-arc`
  (`exists_arcAt_of_path`);
* `lem:subarc`, `lem:cluster`, `lem:open-components`;
* `def:charts`, `lem:charts` for the Cayley map `κ` and the charts `Ψ_ℍ`, `Ψ_𝔻`, packaged as
  `PartialHomeomorph`s satisfying `IsChart`;
* `lem:transfer`, `lem:locality`;
* `lem:disc-geometry`, with closed arcs of `C` written as `circleArc θ ℓ`;
* `fact:crosscut` (`crosscut_theorem`, imported, `sorry`).

The basic tool is `IsArc.nhdsWithin_eq`: along an arc `γ = q([0,1])` at `a = q 0`, the filter
`𝓝[γ \ {a}] a` is the image of `𝓝[>] 0` under the parametrization.
-/

namespace TJK

open _root_.Set Filter Topology Metric Function

/-! ### Arcs -/

section Arcs

variable {E : Type*} [TopologicalSpace E] {E' : Type*} [TopologicalSpace E']

theorem IsArc.symm {γ : Set E} {a b : E} (h : IsArc γ a b) : IsArc γ b a := by
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q.symm, hq.comp unitInterval.symm_involutive.injective, q.symm_range⟩

theorem IsArc.ne {γ : Set E} {a b : E} (h : IsArc γ a b) : a ≠ b := by
  obtain ⟨q, hq, -⟩ := h
  intro hab
  have : (0 : unitInterval) = 1 := hq (by rw [q.source, q.target, hab])
  exact zero_ne_one this

theorem IsArc.left_mem {γ : Set E} {a b : E} (h : IsArc γ a b) : a ∈ γ := by
  obtain ⟨q, -, rfl⟩ := h
  exact ⟨0, q.source⟩

theorem IsArc.right_mem {γ : Set E} {a b : E} (h : IsArc γ a b) : b ∈ γ :=
  h.symm.left_mem

theorem IsArc.isCompact {γ : Set E} {a b : E} (h : IsArc γ a b) : IsCompact γ := by
  obtain ⟨q, -, rfl⟩ := h
  exact isCompact_range q.continuous

theorem IsArc.isConnected {γ : Set E} {a b : E} (h : IsArc γ a b) : IsConnected γ := by
  obtain ⟨q, -, rfl⟩ := h
  exact isConnected_range q.continuous

theorem IsArcAt.mem {Ω : Set E} {x : E} {γ : Set E} (h : IsArcAt Ω x γ) : x ∈ γ := by
  obtain ⟨b, hb, -⟩ := h
  exact hb.left_mem

theorem IsArcAt.subset {Ω : Set E} {x : E} {γ : Set E} (h : IsArcAt Ω x γ) : γ ⊆ insert x Ω :=
  fun z hz => by
    obtain ⟨b, -, hΩ⟩ := h
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr (hΩ ⟨hz, hzx⟩)

/-- The parametrization of an arc, extended to `ℝ`, is injective on `[0, 1]`. -/
theorem Path.injOn_extend_of_injective {a b : E} {q : Path a b} (hq : Injective q) :
    InjOn q.extend (Icc 0 1) := fun x hx y hy hxy => by
  rw [q.extend_apply hx, q.extend_apply hy] at hxy
  exact congrArg Subtype.val (hq hxy)

theorem Path.range_eq_image_extend {a b : E} (q : Path a b) : range q = q.extend '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.2, q.extend_extends' t⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, (q.extend_apply ht).symm⟩

/-- **The basic filter identity.** Along an arc `q([0,1])` at `a = q 0`, the punctured neighbourhood
filter is the image of `𝓝[>] 0` under the (extended) parametrization. -/
theorem IsArc.nhdsWithin_eq [T2Space E] {a b : E} {q : Path a b} (hq : Injective q) :
    𝓝[range q \ {a}] a = map q.extend (𝓝[>] 0) := by
  have he : IsClosedEmbedding q := q.continuous.isClosedEmbedding hq
  have h1 : map q (𝓝[{0}ᶜ] 0) = 𝓝[q '' {0}ᶜ] (q 0) := he.isEmbedding.map_nhdsWithin_eq _ _
  rw [image_compl_eq_range_sdiff_image hq, image_singleton, q.source] at h1
  rw [← h1]
  have h2 : map Subtype.val (𝓝[{0}ᶜ] (0 : unitInterval)) = 𝓝[Ioc 0 1] (0 : ℝ) := by
    rw [IsEmbedding.subtypeVal.map_nhdsWithin_eq]
    congr 1
    ext t
    simp only [mem_image, mem_compl_iff, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨lt_of_le_of_ne s.2.1 fun h => hs (Subtype.ext h.symm), s.2.2⟩
    · rintro ⟨h0, h1⟩
      exact ⟨⟨t, h0.le, h1⟩, fun h => h0.ne' (congrArg Subtype.val h), rfl⟩
  have h3 : (q : unitInterval → E) = q.extend ∘ Subtype.val := funext fun t => (q.extend_extends' t).symm
  rw [h3, ← map_map, h2, nhdsWithin_Ioc_eq_nhdsGT zero_lt_one]

theorem IsArcAt.nhdsWithin_neBot {Ω : Set E} {x : E} {γ : Set E} [T2Space E] (h : IsArcAt Ω x γ) :
    (𝓝[γ \ {x}] x).NeBot := by
  obtain ⟨b, ⟨q, hq, rfl⟩, -⟩ := h
  rw [IsArc.nhdsWithin_eq hq]
  infer_instance

/-- The initial piece `q([0, δ])` of an arc is an arc. -/
theorem IsArc.initial {a b : E} {q : Path a b} (hq : Injective q) {δ : ℝ} (h0 : 0 < δ)
    (h1 : δ ≤ 1) : IsArc (q.extend '' Icc 0 δ) a (q.extend δ) := by
  have hm : ∀ s : unitInterval, δ * (s : ℝ) ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨mul_nonneg h0.le s.2.1, by nlinarith [s.2.1, s.2.2]⟩
  refine ⟨⟨⟨fun s => q.extend (δ * s),
    q.continuous_extend.comp (continuous_const.mul continuous_subtype_val)⟩, by simp, by simp⟩,
    ?_, ?_⟩
  · intro s t hst
    have := Path.injOn_extend_of_injective hq (hm s) (hm t) hst
    exact Subtype.ext (mul_left_cancel₀ h0.ne' this)
  · ext z
    simp only [Path.coe_mk_mk, mem_range, mem_image]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨δ * s, ⟨(hm s).1, by nlinarith [s.2.2]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t / δ, div_nonneg ht.1 h0.le, (div_le_one h0).2 ht.2⟩, ?_⟩
      simp only
      rw [mul_div_cancel₀ _ h0.ne']

/-- A subarc at the same point has the same punctured neighbourhood filter. -/
theorem IsArc.nhdsWithin_subarc [T2Space E] {γ γ' : Set E} {a b b' : E} (h : IsArc γ a b)
    (h' : IsArc γ' a b') (hsub : γ' ⊆ γ) : 𝓝[γ' \ {a}] a = 𝓝[γ \ {a}] a := by
  refine le_antisymm (nhdsWithin_mono _ (sdiff_subset_sdiff_left hsub)) (nhdsWithin_le_of_mem ?_)
  obtain ⟨q, hq, rfl⟩ := h
  have he : IsClosedEmbedding q := q.continuous.isClosedEmbedding hq
  -- the parameter set of `γ'` is an interval containing `0` and some `s₀ > 0`
  have hpre : IsPreconnected (q ⁻¹' γ') := by
    rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hsub]
    exact h'.isConnected.isPreconnected
  have hT : IsPreconnected (Subtype.val '' (q ⁻¹' γ')) :=
    hpre.image _ continuous_subtype_val.continuousOn
  obtain ⟨s, hs⟩ := hsub h'.right_mem
  have hs0 : (0 : ℝ) < s := by
    refine lt_of_le_of_ne s.2.1 fun h0 => h'.ne ?_
    have : s = 0 := Subtype.ext h0.symm
    rw [← hs, this, q.source]
  have hIcc : Icc (0 : ℝ) s ⊆ Subtype.val '' (q ⁻¹' γ') :=
    hT.Icc_subset ⟨0, by simp [q.source, h'.left_mem], rfl⟩ ⟨s, by simp [hs, h'.right_mem], rfl⟩
  rw [IsArc.nhdsWithin_eq hq, mem_map]
  filter_upwards [Ioo_mem_nhdsGT hs0] with t ht
  obtain ⟨u, hu, hut⟩ := hIcc ⟨ht.1.le, ht.2.le⟩
  refine ⟨?_, fun hta => ?_⟩
  · rw [← hut, q.extend_extends' u]
    exact hu
  · have h1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le.trans s.2.2⟩
    have := Path.injOn_extend_of_injective hq h1 ⟨le_rfl, zero_le_one⟩
      (by rw [hta, q.extend_zero])
    exact ht.1.ne' this

/-- `lem:subarc` (a): inside any neighbourhood of `x`, an arc at `x` has a subarc at `x`, with the
same punctured neighbourhood filter (so the same limits and cluster sets). -/
theorem IsArcAt.exists_subarc_subset [T2Space E] {Ω : Set E} {x : E} {γ : Set E}
    (h : IsArcAt Ω x γ) {W : Set E} (hW : W ∈ 𝓝 x) :
    ∃ γ' ⊆ γ ∩ W, IsArcAt Ω x γ' ∧ 𝓝[γ' \ {x}] x = 𝓝[γ \ {x}] x := by
  obtain ⟨b, hγ, hΩ⟩ := h
  obtain ⟨q, hq, rfl⟩ := id hγ
  have hc : Tendsto q.extend (𝓝 0) (𝓝 x) := by
    have := q.continuous_extend.tendsto 0
    rwa [q.extend_zero] at this
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.1 (hc hW)
  set δ' := min (δ / 2) 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min (by linarith) one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have harc := IsArc.initial hq hδ'0 hδ'1
  have hsub : q.extend '' Icc 0 δ' ⊆ range q := by
    rw [Path.range_eq_image_extend]
    exact image_mono (Icc_subset_Icc le_rfl hδ'1)
  refine ⟨_, subset_inter hsub ?_, ⟨_, harc, (sdiff_subset_sdiff_left hsub).trans hΩ⟩,
    IsArc.nhdsWithin_subarc hγ harc hsub⟩
  rintro _ ⟨t, ht, rfl⟩
  apply hδW
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  linarith [ht.2, min_le_left (δ / 2) 1]

/-- `lem:subarc` (a), second part: if `f → q` along `γ` and `V` is a neighbourhood of `q`, some
subarc at `x` inside `W` is mapped into `V` (apart from `x`). -/
theorem IsArcAt.tendsto_subarc [T2Space E] {Y : Type*} [TopologicalSpace Y] {Ω : Set E} {x : E}
    {γ : Set E} (h : IsArcAt Ω x γ) {f : E → Y} {l : Filter Y}
    (hf : Tendsto f (𝓝[γ \ {x}] x) l) {V : Set Y} (hV : V ∈ l) {W : Set E} (hW : W ∈ 𝓝 x) :
    ∃ γ' ⊆ γ ∩ W, IsArcAt Ω x γ' ∧ MapsTo f (γ' \ {x}) V := by
  obtain ⟨U, hUo, hxU, hUV⟩ := mem_nhdsWithin.1 (hf hV)
  obtain ⟨γ', hγ', harc, -⟩ := h.exists_subarc_subset (inter_mem hW (hUo.mem_nhds hxU))
  exact ⟨γ', fun z hz => ⟨(hγ' hz).1, (hγ' hz).2.1⟩, harc,
    fun z hz => hUV ⟨(hγ' hz.1).2.2, (hγ' hz.1).1, hz.2⟩⟩

/-- `lem:subarc` (a): the cluster set along a subarc at the same point is the same. -/
theorem IsArcAt.clusterSet_subarc [T2Space E] {Y : Type*} [TopologicalSpace Y] {Ω : Set E}
    {x : E} {γ γ' : Set E} (h : IsArcAt Ω x γ) (h' : IsArcAt Ω x γ') (hsub : γ' ⊆ γ)
    (f : E → Y) : clusterSet f γ' x = clusterSet f γ x := by
  obtain ⟨b, hb, -⟩ := h
  obtain ⟨b', hb', -⟩ := h'
  simp only [clusterSet, IsArc.nhdsWithin_subarc hb hb' hsub]

/-- `lem:subarc` (b): leaving a closed ball. If `|g(t₁) - g(t₀)| ≥ r > 0`, there is `t'` between
`t₀` and `t₁` with `|g(t') - g(t₀)| = r` and `g` maps the interval between `t₀` and `t'` into the
closed ball of radius `r` about `g(t₀)`. -/
theorem exists_exit_subpath {E : Type*} [PseudoMetricSpace E] {g : ℝ → E} {t₀ t₁ r : ℝ}
    (hg : ContinuousOn g (uIcc t₀ t₁)) (hr : 0 < r) (h₁ : r ≤ dist (g t₁) (g t₀)) :
    ∃ t' ∈ uIcc t₀ t₁, MapsTo g (uIcc t₀ t') (closedBall (g t₀) r) ∧ dist (g t') (g t₀) = r := by
  set φ : ℝ → ℝ := fun t => dist (g t) (g t₀) with hφ
  have hφc : ContinuousOn φ (uIcc t₀ t₁) := continuous_dist.comp_continuousOn (hg.prodMk continuousOn_const)
  set S := uIcc t₀ t₁ ∩ φ ⁻¹' Ici r with hS
  have hSc : IsCompact S := isCompact_uIcc.of_isClosed_subset
    (hφc.preimage_isClosed_of_isClosed isCompact_uIcc.isClosed isClosed_Ici) inter_subset_left
  obtain ⟨t', ht'S, ht'min⟩ := hSc.exists_isMinOn ⟨t₁, right_mem_uIcc, h₁⟩
    (continuous_id.sub continuous_const).abs.continuousOn
  have ht'I : t' ∈ uIcc t₀ t₁ := ht'S.1
  have hsubI : uIcc t₀ t' ⊆ uIcc t₀ t₁ := uIcc_subset_uIcc_left ht'I
  have key : ∀ t ∈ uIcc t₀ t', t ≠ t' → |t - t₀| < |t' - t₀| := by
    intro t ht htt
    rcases mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      exact lt_of_le_of_ne (by linarith) (fun h => htt (by linarith))
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      exact lt_of_le_of_ne (by linarith) (fun h => htt (by linarith))
  have hlt : ∀ t ∈ uIcc t₀ t', t ≠ t' → φ t < r := by
    intro t ht htt
    by_contra hcon
    have := ht'min ⟨hsubI ht, le_of_not_gt hcon⟩
    exact absurd this (not_le.2 (key t ht htt))
  have hφ0 : φ t₀ = 0 := dist_self _
  obtain ⟨c, hc, hcr⟩ : r ∈ φ '' uIcc t₀ t' := by
    refine intermediate_value_uIcc (hφc.mono hsubI) ?_
    rw [hφ0, uIcc_of_le (le_trans hr.le ht'S.2)]
    exact ⟨hr.le, ht'S.2⟩
  have hct : c = t' := by
    by_contra hct
    exact (hlt c hc hct).ne hcr
  subst hct
  refine ⟨c, ht'I, fun t ht => ?_, hcr⟩
  rw [mem_closedBall]
  by_cases htc : t = c
  · rw [htc]; exact hcr.le
  · exact (hlt t ht htc).le

/-- `lem:subarc` (c), general form: the subarc of `γ` from `x` to its first point on a closed set
`F ∌ x`. -/
theorem IsArcAt.exists_subarc_firstHit [T2Space E] {Ω : Set E} {x : E} {γ : Set E}
    (h : IsArcAt Ω x γ) {F : Set E} (hF : IsClosed F) (hx : x ∉ F) (hγF : (γ ∩ F).Nonempty) :
    ∃ γ' ⊆ γ, ∃ b ∈ F, IsArc γ' x b ∧ IsArcAt Ω x γ' ∧ γ' ∩ F = {b} ∧
      IsPreconnected (γ' \ {b}) := by
  obtain ⟨b₀, hγ, hΩ⟩ := h
  obtain ⟨q, hq, rfl⟩ := id hγ
  have hinj := Path.injOn_extend_of_injective hq
  set T := Icc (0 : ℝ) 1 ∩ q.extend ⁻¹' F with hT
  have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset
    (q.continuous_extend.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hF)
    inter_subset_left
  obtain ⟨z, ⟨t, rfl⟩, hzF⟩ := hγF
  obtain ⟨δ, hδT, hδmin⟩ := hTc.exists_isMinOn ⟨t, t.2, by
    simp only [mem_preimage, q.extend_extends']; exact hzF⟩ continuous_id.continuousOn
  have hδ0 : 0 < δ := by
    refine lt_of_le_of_ne hδT.1.1 fun h0 => hx ?_
    have := hδT.2
    rwa [← h0, mem_preimage, q.extend_zero] at this
  have harc := IsArc.initial hq hδ0 hδT.1.2
  have hsub : q.extend '' Icc 0 δ ⊆ range q := by
    rw [Path.range_eq_image_extend]
    exact image_mono (Icc_subset_Icc le_rfl hδT.1.2)
  have hdiff : q.extend '' Icc 0 δ \ {q.extend δ} = q.extend '' Ico 0 δ := by
    ext w
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hne⟩
      exact ⟨s, ⟨hs.1, lt_of_le_of_ne hs.2 fun h => hne (by rw [h]; rfl)⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨s, Ico_subset_Icc_self hs, rfl⟩, fun h => hs.2.ne ?_⟩
      exact hinj ⟨hs.1, hs.2.le.trans hδT.1.2⟩ hδT.1 h
  refine ⟨_, hsub, q.extend δ, hδT.2, harc, ⟨_, harc, (sdiff_subset_sdiff_left hsub).trans hΩ⟩,
    ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hsF⟩
      have : δ ≤ s := hδmin ⟨⟨hs.1, hs.2.trans hδT.1.2⟩, hsF⟩
      rw [mem_singleton_iff, le_antisymm hs.2 this]
    · rintro rfl
      exact ⟨⟨δ, ⟨hδ0.le, le_rfl⟩, rfl⟩, hδT.2⟩
  · rw [hdiff]
    exact isPreconnected_Ico.image _ q.continuous_extend.continuousOn

end Arcs

/-- `lem:subarc` (c): an arc at a real point `x` in `ℍ` meeting the line `Im z = c` has a subarc
from `x` to its first point `b` on that line; it lies in `0 ≤ Im z ≤ c`, and its points other than
`x`, `b` lie in `0 < Im z < c`. -/
theorem IsArcAt.exists_subarc_strip {x : ℂ} (hx : x.im = 0) {γ : Set ℂ} (h : IsArcAt upper x γ)
    {c : ℝ} (hc : 0 < c) (hγc : ∃ z ∈ γ, z.im = c) :
    ∃ γ' ⊆ γ, ∃ b : ℂ, b.im = c ∧ IsArc γ' x b ∧ IsArcAt upper x γ' ∧
      γ' ⊆ {z | 0 ≤ z.im ∧ z.im ≤ c} ∧ γ' \ {x, b} ⊆ {z | 0 < z.im ∧ z.im < c} := by
  have hF : IsClosed {z : ℂ | z.im = c} := isClosed_eq Complex.continuous_im continuous_const
  obtain ⟨γ', hsub, b, hbF, harc, hat, hγ'F, hpre⟩ := h.exists_subarc_firstHit hF
    (by simp only [mem_ofPred_eq, hx]; exact hc.ne) (by obtain ⟨z, hz, hzc⟩ := hγc; exact ⟨z, hz, hzc⟩)
  have hup : γ' \ {x} ⊆ upper := by obtain ⟨b', -, h'⟩ := hat; exact h'
  -- `Im` on the preconnected set `γ' \ {b}` takes the value `0` and avoids `c`
  have hlt : ∀ z ∈ γ' \ {b}, z.im < c := by
    intro z hz
    have hI : IsPreconnected (Complex.im '' (γ' \ {b})) :=
      hpre.image _ Complex.continuous_im.continuousOn
    have hxm : x ∈ γ' \ {b} :=
      ⟨harc.left_mem, fun h' => harc.ne (by rw [mem_singleton_iff] at h'; exact h')⟩
    by_contra hge
    have hsub' := hI.Icc_subset ⟨x, hxm, rfl⟩ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwc⟩ := hsub' (show c ∈ Icc x.im z.im by rw [hx]; exact ⟨hc.le, le_of_not_gt hge⟩)
    have : w ∈ γ' ∩ {z : ℂ | z.im = c} := ⟨hw.1, hwc⟩
    rw [hγ'F] at this
    exact hw.2 this
  refine ⟨γ', hsub, b, hbF, harc, hat, fun z hz => ?_, fun z hz => ?_⟩
  · by_cases hzb : z = b
    · subst hzb; exact ⟨hc.le.trans_eq hbF.symm, hbF.le⟩
    by_cases hzx : z = x
    · subst hzx; exact ⟨hx.ge, hx.le.trans hc.le⟩
    exact ⟨(hup ⟨hz, hzx⟩).le, (hlt z ⟨hz, hzb⟩).le⟩
  · have hzx : z ≠ x := fun h' => hz.2 (Or.inl h')
    have hzb : z ≠ b := fun h' => hz.2 (Or.inr h')
    exact ⟨hup ⟨hz.1, hzx⟩, hlt z ⟨hz.1, hzb⟩⟩

/-! ### Paths may replace arcs (`fact:tietze-arc`, `cor:path-arc`) -/

section PathArc

variable {E : Type*} [TopologicalSpace E] [T2Space E]

/-- `fact:tietze-arc` (Tietze 1919; every path-connected Hausdorff space is arc-connected): the
image of a path with distinct endpoints contains a simple arc with the same endpoints.
Imported fact; not in Mathlib. -/
theorem exists_arc_in_path {a b : E} (g : Path a b) (hab : a ≠ b) :
    ∃ γ ⊆ range g, IsArc γ a b :=
  exists_arc_in_path' g hab

/-- `cor:path-arc`: if `g(1) = p ∉ Ω` and `g(t) ∈ Ω` for `t < 1`, then `g([0,1])` contains an arc
`γ` at `p` with `𝓝[γ \ {p}] p ≤ map g (𝓝[<] 1)`; so limits of `f ∘ g` as `t → 1` are limits along
`γ` (`tendsto_of_nhdsWithin_le_map`), and cluster sets along `γ` are contained in those of
`f ∘ g` (`clusterSet_subset_of_nhdsWithin_le_map`). -/
theorem exists_arcAt_of_path {Ω : Set E} {a p : E} (g : Path a p)
    (hg : ∀ t : unitInterval, t ≠ 1 → g t ∈ Ω) (hp : p ∉ Ω) :
    ∃ γ ⊆ range g, IsArcAt Ω p γ ∧ 𝓝[γ \ {p}] p ≤ map g.extend (𝓝[<] 1) := by
  have hap : a ≠ p := by
    intro h
    have := hg 0 zero_ne_one
    rw [g.source, h] at this
    exact hp this
  obtain ⟨γ, hγg, hγ⟩ := exists_arc_in_path g hap
  have hΩ : γ \ {p} ⊆ Ω := by
    rintro z ⟨hz, hzp⟩
    obtain ⟨t, rfl⟩ := hγg hz
    exact hg t fun h => hzp (by rw [h, g.target]; rfl)
  refine ⟨γ, hγg, ⟨a, hγ.symm, hΩ⟩, fun S hS => ?_⟩
  rw [mem_map, mem_nhdsLT_iff_exists_Ioo_subset] at hS
  obtain ⟨l, hl, hlS⟩ := hS
  set K := g.extend '' Icc 0 (max l 0) with hK
  have hKc : IsCompact K := isCompact_Icc.image g.continuous_extend
  have hpK : p ∉ K := by
    rintro ⟨t, ht, htp⟩
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 (max_lt hl zero_lt_one)
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht1.le⟩
    rw [g.extend_apply htI] at htp
    exact hp (htp ▸ hg ⟨t, htI⟩ fun h => ht1.ne (congrArg Subtype.val h))
  rw [mem_nhdsWithin]
  refine ⟨Kᶜ, hKc.isClosed.isOpen_compl, hpK, ?_⟩
  rintro z ⟨hzK, hz, hzp⟩
  obtain ⟨t, rfl⟩ := hγg hz
  have ht : (t : ℝ) ∈ Ioo l 1 := by
    refine ⟨?_, lt_of_le_of_ne t.2.2 fun h => hzp ?_⟩
    · by_contra hle
      exact hzK ⟨t, ⟨t.2.1, le_max_of_le_left (le_of_not_gt hle)⟩, g.extend_extends' t⟩
    · have : t = 1 := Subtype.ext h
      rw [this, g.target]; rfl
  have := hlS ht
  rwa [mem_preimage, g.extend_extends'] at this

omit [T2Space E] in
theorem tendsto_of_nhdsWithin_le_map {Y : Type*} {γ : Set E} {p : E} {g : ℝ → E}
    (hle : 𝓝[γ \ {p}] p ≤ map g (𝓝[<] 1)) {f : E → Y} {l : Filter Y}
    (hf : Tendsto (f ∘ g) (𝓝[<] 1) l) : Tendsto f (𝓝[γ \ {p}] p) l :=
  (tendsto_map'_iff.2 hf).mono_left hle

omit [T2Space E] in
theorem clusterSet_subset_of_nhdsWithin_le_map {Y : Type*} [TopologicalSpace Y] {γ : Set E}
    {p : E} {g : ℝ → E} (hle : 𝓝[γ \ {p}] p ≤ map g (𝓝[<] 1)) (f : E → Y) :
    clusterSet f γ p ⊆ {q | MapClusterPt q (𝓝[<] 1) (f ∘ g)} := fun q hq => by
  have : map f (𝓝[γ \ {p}] p) ≤ map (f ∘ g) (𝓝[<] 1) := by
    rw [← map_map]; exact map_mono hle
  exact ClusterPt.mono hq this

end PathArc

/-! ### Cluster sets (`lem:cluster`) -/

section Cluster

/-- A decreasing intersection of compact preconnected sets is preconnected. -/
theorem isPreconnected_iInter_of_antitone {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : ℕ → Set X} (hK : Antitone K) (hc : ∀ n, IsCompact (K n))
    (hp : ∀ n, IsPreconnected (K n)) : IsPreconnected (⋂ n, K n) := by
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hsub hne hne'
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  set L := ⋂ n, K n with hL
  have hLc : IsCompact L :=
    (hc 0).of_isClosed_subset (isClosed_iInter fun n => (hc n).isClosed) (iInter_subset _ 0)
  have hdisj : Disjoint (L ∩ t) (L ∩ t') := by
    rw [disjoint_iff_inter_eq_empty, ← hempty]
    ext z; simp only [mem_inter_iff]; tauto
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hLc.inter_right ht) (hLc.inter_right ht') hdisj
  have hn : ∃ n, K n ⊆ U ∪ V := by
    by_contra hcon
    push Not at hcon
    have hne'' : ∀ n, (K n \ (U ∪ V)).Nonempty := fun n => by
      obtain ⟨z, hz, hz'⟩ := not_subset.1 (hcon n)
      exact ⟨z, hz, hz'⟩
    obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun n => K n \ (U ∪ V))
      (fun i j => ⟨max i j, sdiff_subset_sdiff_left (hK (le_max_left i j)),
        sdiff_subset_sdiff_left (hK (le_max_right i j))⟩) hne''
      (fun n => (hc n).diff (hU.union hV)) (fun n => (hc n).isClosed.sdiff (hU.union hV))
    rw [mem_iInter] at hz
    have hzL : z ∈ L := mem_iInter.2 fun n => (hz n).1
    rcases hsub hzL with h1 | h1
    · exact (hz 0).2 (Or.inl (hAU ⟨hzL, h1⟩))
    · exact (hz 0).2 (Or.inr (hBV ⟨hzL, h1⟩))
  obtain ⟨n, hn⟩ := hn
  obtain ⟨a, haL, hat⟩ := hne
  obtain ⟨b, hbL, hbt⟩ := hne'
  obtain ⟨z, -, hzU, hzV⟩ := hp n U V hU hV hn ⟨a, mem_iInter.1 haL n, hAU ⟨haL, hat⟩⟩
    ⟨b, mem_iInter.1 hbL n, hBV ⟨hbL, hbt⟩⟩
  exact hUV.ne_of_mem hzU hzV rfl

variable {E : Type*} [TopologicalSpace E] [T2Space E] {Y : Type*} [TopologicalSpace Y]
  {Ω : Set E} {x : E} {γ : Set E}

/-- `lem:cluster`: the cluster set along `γ` is the intersection of the closures of
`f(γ' \ {x})` over the subarcs `γ' ⊆ γ` at `x`. -/
theorem clusterSet_eq_iInter_subarc (h : IsArcAt Ω x γ) (f : E → Y) :
    clusterSet f γ x = ⋂ γ' ∈ {γ' | γ' ⊆ γ ∧ IsArcAt Ω x γ'}, closure (f '' (γ' \ {x})) := by
  ext y
  simp only [clusterSet, mem_ofPred_eq, MapClusterPt, clusterPt_iff_forall_mem_closure, mem_map,
    mem_iInter, and_imp]
  constructor
  · intro hy γ' hsub h'
    apply hy
    obtain ⟨b, hb, -⟩ := h
    obtain ⟨b', hb', -⟩ := h'
    rw [← IsArc.nhdsWithin_subarc hb hb' hsub]
    exact mem_of_superset self_mem_nhdsWithin (subset_preimage_image f _)
  · intro hy s hs
    obtain ⟨U, hUo, hxU, hUs⟩ := mem_nhdsWithin.1 hs
    obtain ⟨γ', hγ', h', -⟩ := h.exists_subarc_subset (hUo.mem_nhds hxU)
    refine closure_mono ?_ (hy γ' (fun z hz => (hγ' hz).1) h')
    rintro _ ⟨z, hz, rfl⟩
    exact hUs ⟨(hγ' hz.1).2, (hγ' hz.1).1, hz.2⟩

/-- `lem:cluster`: the cluster set is nonempty when the target is compact. -/
theorem clusterSet_nonempty [CompactSpace Y] (h : IsArcAt Ω x γ) (f : E → Y) :
    (clusterSet f γ x).Nonempty := by
  have := h.nhdsWithin_neBot
  exact exists_clusterPt_of_compactSpace _

omit [T2Space E] in
theorem isClosed_clusterSet (f : E → Y) : IsClosed (clusterSet f γ x) :=
  isClosed_setOfPred_clusterPt

omit [T2Space E] in
/-- `lem:cluster`: the cluster set is compact when the target is compact. -/
theorem isCompact_clusterSet [CompactSpace Y] (f : E → Y) : IsCompact (clusterSet f γ x) :=
  (isClosed_clusterSet f).isCompact

/-- `lem:cluster`: the cluster set of a continuous function into a compact Hausdorff space is
connected. -/
theorem isConnected_clusterSet [CompactSpace Y] [T2Space Y] (h : IsArcAt Ω x γ) {f : E → Y}
    (hf : ContinuousOn f Ω) : IsConnected (clusterSet f γ x) := by
  refine ⟨clusterSet_nonempty h f, ?_⟩
  obtain ⟨b, hγ, hΩ⟩ := h
  obtain ⟨q, hq, rfl⟩ := id hγ
  set T : ℕ → Set E := fun n => q.extend '' Ioo 0 (1 / ((n : ℝ) + 2)) with hT
  have hT1 : ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hTsub : ∀ n : ℕ, T n ⊆ range q \ {x} := by
    rintro n _ ⟨t, ht, rfl⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le.trans (hT1 n)⟩
    refine ⟨⟨⟨t, htI⟩, (q.extend_apply htI).symm⟩, fun hx => ht.1.ne' ?_⟩
    exact (Path.injOn_extend_of_injective hq ⟨le_rfl, zero_le_one⟩ htI
      (by rw [q.extend_zero]; exact hx.symm)).symm
  have hTmem : ∀ n : ℕ, T n ∈ 𝓝[range q \ {x}] x := fun n => by
    rw [IsArc.nhdsWithin_eq hq]
    exact mem_map.2 (mem_of_superset (Ioo_mem_nhdsGT (by positivity)) (subset_preimage_image _ _))
  have heq : clusterSet f (range q) x = ⋂ n, closure (f '' T n) := by
    ext y
    simp only [clusterSet, mem_ofPred_eq, MapClusterPt, clusterPt_iff_forall_mem_closure, mem_map,
      mem_iInter]
    constructor
    · exact fun hy n => hy _ (mem_of_superset (hTmem n) (subset_preimage_image f _))
    · intro hy s hs
      rw [IsArc.nhdsWithin_eq hq, mem_map] at hs
      obtain ⟨ε, hε, hεs⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.1 hs
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine closure_mono ?_ (hy n)
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact hεs ⟨ht.1, ht.2.trans (by
        have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith)⟩
  rw [heq]
  refine isPreconnected_iInter_of_antitone ?_ (fun n => isClosed_closure.isCompact) fun n => ?_
  · intro m n hmn
    refine closure_mono (image_mono (image_mono (Ioo_subset_Ioo le_rfl ?_)))
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : m + 2 ≤ n + 2))
  · refine IsPreconnected.closure (IsPreconnected.image ?_ _ (hf.mono ((hTsub n).trans hΩ)))
    exact isPreconnected_Ioo.image _ q.continuous_extend.continuousOn

/-- `lem:cluster`: `f → q` along `γ` iff the cluster set is `{q}` (compact Hausdorff target). -/
theorem tendsto_iff_clusterSet_eq_singleton [CompactSpace Y] [T2Space Y] (h : IsArcAt Ω x γ)
    (f : E → Y) (q : Y) : Tendsto f (𝓝[γ \ {x}] x) (𝓝 q) ↔ clusterSet f γ x = {q} := by
  have := h.nhdsWithin_neBot
  constructor
  · intro hf
    ext y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · exact eq_of_nhds_neBot (ClusterPt.mono hy hf)
    · rw [mem_singleton_iff] at hy; subst hy; exact hf.mapClusterPt
  · intro hc
    refine tendsto_nhds_of_unique_mapClusterPt fun y hy => ?_
    have : y ∈ clusterSet f γ x := hy
    rwa [hc] at this

/-- The cluster points of `Θ ∘ u` are the images of those of `u` (compact source, continuous
`Θ`). -/
theorem setOf_mapClusterPt_comp {α : Type*} {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [CompactSpace Y] {F : Filter α} {u : α → Y} {Θ : Y → Z} (hΘ : Continuous Θ) :
    {z | MapClusterPt z F (Θ ∘ u)} = Θ '' {y | MapClusterPt y F u} := by
  ext z
  constructor
  · intro hz
    have hz' : (𝓝 z ⊓ map Θ (map u F)).NeBot := by
      have : ClusterPt z (map (Θ ∘ u) F) := hz
      rwa [← map_map] at this
    rw [← Filter.push_pull', map_neBot_iff] at hz'
    obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace (comap Θ (𝓝 z) ⊓ map u F)
    refine ⟨y, hy.mono inf_le_right, eq_of_nhds_neBot ?_⟩
    have h1 : ClusterPt y (comap Θ (𝓝 z)) := hy.mono inf_le_left
    have h2 : (map Θ (𝓝 y ⊓ comap Θ (𝓝 z))).NeBot := (map_neBot_iff _).2 h1
    exact h2.mono (le_inf (map_mono inf_le_left |>.trans (hΘ.tendsto y))
      (map_mono inf_le_right |>.trans map_comap_le))
  · rintro ⟨y, hy, rfl⟩
    exact MapClusterPt.continuousAt_comp hΘ.continuousAt hy

omit [T2Space E] in
/-- `lem:cluster`: `C(Θ ∘ f, γ) = Θ(C(f, γ))` for continuous `Θ` on a compact space. -/
theorem clusterSet_comp [CompactSpace Y] {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    {Θ : Y → Z} (hΘ : Continuous Θ) (f : E → Y) :
    clusterSet (Θ ∘ f) γ x = Θ '' clusterSet f γ x :=
  setOf_mapClusterPt_comp hΘ

end Cluster

/-! ### Components of open sets (`lem:open-components`) -/

/-- `lem:open-components`: an open subset of a second countable, locally path-connected space
(such as `ℝⁿ`) has countably many components; they are open and path-connected, and every
preconnected subset of the open set lies in one of them. -/
theorem countable_connectedComponents_of_isOpen {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyPathConnectedSpace X] {U : Set X} (hU : IsOpen U) :
    {C | ∃ x ∈ U, connectedComponentIn U x = C}.Countable ∧
      (∀ x, IsOpen (connectedComponentIn U x)) ∧
      (∀ x ∈ U, IsPathConnected (connectedComponentIn U x)) ∧
      ∀ S ⊆ U, IsPreconnected S → ∀ x ∈ S, S ⊆ connectedComponentIn U x := by
  have hopen : ∀ x, IsOpen (connectedComponentIn U x) := fun x => hU.connectedComponentIn
  refine ⟨?_, hopen, fun x hx => ?_, fun S hS hc x hx => hc.subset_connectedComponentIn hx hS⟩
  · refine PairwiseDisjoint.countable_of_isOpen (s := id) ?_ ?_ ?_
    · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hne
      refine disjoint_left.2 fun z hzx hzy => hne ?_
      rw [connectedComponentIn_eq hzx, connectedComponentIn_eq hzy]
    · rintro _ ⟨x, -, rfl⟩; exact hopen x
    · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, mem_connectedComponentIn hx⟩
  · exact (hopen x).isConnected_iff_isPathConnected.1 (isConnected_connectedComponentIn_iff.2 hx)


/-! ### Transfer (`lem:transfer`) and locality (`lem:locality`) -/

section Transfer

variable {E : Type*} [TopologicalSpace E] [T2Space E] {E' : Type*} [TopologicalSpace E']
  [T2Space E']

omit [T2Space E] [T2Space E'] in
/-- A map continuous and injective on an arc maps it to an arc; the parametrizations correspond. -/
theorem Path.exists_map_of_injOn {a b : E} (q : Path a b) (hq : Injective q) {ψ : E → E'}
    (hc : ContinuousOn ψ (range q)) (hi : InjOn ψ (range q)) :
    ∃ q' : Path (ψ a) (ψ b), Injective q' ∧ range q' = ψ '' range q ∧
      q'.extend = ψ ∘ q.extend := by
  refine ⟨⟨⟨ψ ∘ q, hc.comp_continuous q.continuous fun t => mem_range_self t⟩, by simp, by simp⟩,
    fun s t hst => hq (hi (mem_range_self s) (mem_range_self t) hst), ?_, ?_⟩
  · ext z; simp [range_comp]
  · funext t
    simp only [Path.extend, comp_apply]
    rfl

omit [T2Space E] [T2Space E'] in
theorem IsArc.image {γ : Set E} {a b : E} (h : IsArc γ a b) {ψ : E → E'} (hc : ContinuousOn ψ γ)
    (hi : InjOn ψ γ) : IsArc (ψ '' γ) (ψ a) (ψ b) := by
  obtain ⟨q, hq, rfl⟩ := h
  obtain ⟨q', hq', hr, -⟩ := Path.exists_map_of_injOn q hq hc hi
  exact ⟨q', hq', hr⟩

/-- The punctured neighbourhood filter along an arc is carried to that along the image arc. -/
theorem IsArc.map_nhdsWithin {γ : Set E} {a b : E} (h : IsArc γ a b) {ψ : E → E'}
    (hc : ContinuousOn ψ γ) (hi : InjOn ψ γ) :
    map ψ (𝓝[γ \ {a}] a) = 𝓝[ψ '' γ \ {ψ a}] (ψ a) := by
  obtain ⟨q, hq, rfl⟩ := h
  obtain ⟨q', hq', hr, he⟩ := Path.exists_map_of_injOn q hq hc hi
  rw [← hr, IsArc.nhdsWithin_eq hq, IsArc.nhdsWithin_eq hq', he, map_map]

omit [T2Space E] [T2Space E'] in
theorem IsArcAt.image {Ω : Set E} {Ω' : Set E'} {x : E} {γ : Set E} (h : IsArcAt Ω x γ)
    {ψ : E → E'} (hc : ContinuousOn ψ γ) (hi : InjOn ψ γ) (hΩ : MapsTo ψ Ω Ω') :
    IsArcAt Ω' (ψ x) (ψ '' γ) := by
  obtain ⟨b, hb, hγΩ⟩ := h
  refine ⟨ψ b, hb.image hc hi, ?_⟩
  rintro _ ⟨⟨z, hz, rfl⟩, hzx⟩
  exact hΩ (hγΩ ⟨hz, fun h => hzx (by rw [mem_singleton_iff] at h ⊢; rw [h])⟩)

/-- `Ψ` is a homeomorphism of `Ω ∪ B` onto `Ω' ∪ B'` with `Ψ(Ω) = Ω'` (and `Ω ∩ B = ∅`,
`Ω' ∩ B' = ∅`): the hypothesis of `lem:transfer`. -/
structure IsChart (e : PartialHomeomorph E E') (Ω B : Set E) (Ω' B' : Set E') : Prop where
  source_eq : e.source = Ω ∪ B
  target_eq : e.target = Ω' ∪ B'
  image_eq : e '' Ω = Ω'
  disjoint : Disjoint Ω B
  disjoint' : Disjoint Ω' B'

namespace IsChart

omit [T2Space E] [T2Space E']

variable {e : PartialHomeomorph E E'} {Ω B : Set E} {Ω' B' : Set E'}

theorem subset_source (h : IsChart e Ω B Ω' B') : Ω ⊆ e.source :=
  h.source_eq ▸ subset_union_left

theorem boundary_subset_source (h : IsChart e Ω B Ω' B') : B ⊆ e.source :=
  h.source_eq ▸ subset_union_right

theorem subset_target (h : IsChart e Ω B Ω' B') : Ω' ⊆ e.target :=
  h.target_eq ▸ subset_union_left

theorem boundary_subset_target (h : IsChart e Ω B Ω' B') : B' ⊆ e.target :=
  h.target_eq ▸ subset_union_right

theorem mem_iff (h : IsChart e Ω B Ω' B') {z : E} (hz : z ∈ e.source) : e z ∈ Ω' ↔ z ∈ Ω := by
  constructor
  · intro hz'
    rw [← h.image_eq] at hz'
    obtain ⟨w, hw, hwz⟩ := hz'
    rwa [← e.injOn (h.subset_source hw) hz hwz]
  · intro hz'
    rw [← h.image_eq]
    exact mem_image_of_mem _ hz'

theorem mem_boundary_iff (h : IsChart e Ω B Ω' B') {z : E} (hz : z ∈ e.source) :
    e z ∈ B' ↔ z ∈ B := by
  have h1 := e.map_source hz
  rw [h.target_eq] at h1
  have h2 := hz
  rw [h.source_eq] at h2
  constructor
  · intro hB
    refine h2.resolve_left fun hΩ => ?_
    exact disjoint_left.1 h.disjoint' ((h.mem_iff hz).2 hΩ) hB
  · intro hB
    refine h1.resolve_left fun hΩ => ?_
    exact disjoint_left.1 h.disjoint ((h.mem_iff hz).1 hΩ) hB

theorem symm (h : IsChart e Ω B Ω' B') : IsChart e.symm Ω' B' Ω B where
  source_eq := by rw [e.symm_source, h.target_eq]
  target_eq := by rw [e.symm_target, h.source_eq]
  image_eq := by
    rw [← h.image_eq]
    exact e.toPartialEquiv.symm_image_image_of_subset_source h.subset_source
  disjoint := h.disjoint'
  disjoint' := h.disjoint

theorem mapsTo (h : IsChart e Ω B Ω' B') : MapsTo e Ω Ω' := fun _ hz =>
  (h.mem_iff (h.subset_source hz)).2 hz

/-- Arcs at `p ∈ Ω ∪ B` lie in the source of the chart. -/
theorem arc_subset_source (h : IsChart e Ω B Ω' B') {p : E} (hp : p ∈ e.source) {γ : Set E}
    (hγ : IsArcAt Ω p γ) : γ ⊆ e.source := fun z hz => by
  rcases hγ.subset hz with rfl | hz
  · exact hp
  · exact h.subset_source hz

end IsChart

variable {e : PartialHomeomorph E E'} {Ω B : Set E} {Ω' B' : Set E'}

omit [T2Space E] [T2Space E'] in
/-- `lem:transfer`: arcs correspond. -/
theorem transfer_isArcAt (h : IsChart e Ω B Ω' B') {p : E} (hp : p ∈ e.source) {γ : Set E}
    (hγ : γ ⊆ e.source) : IsArcAt Ω p γ ↔ IsArcAt Ω' (e p) (e '' γ) := by
  constructor
  · intro ha
    exact ha.image (e.continuousOn.mono hγ) (e.injOn.mono hγ) h.mapsTo
  · intro ha
    have hγ' : e '' γ ⊆ e.target := fun _ ⟨z, hz, hze⟩ => hze ▸ e.map_source (hγ hz)
    have := ha.image (e.continuousOn_symm.mono hγ') (e.symm.injOn.mono hγ') h.symm.mapsTo
    have heq : e.symm '' (e '' γ) = γ := e.toPartialEquiv.symm_image_image_of_subset_source hγ
    rwa [e.left_inv hp, heq] at this

/-- `lem:transfer`: limits along corresponding arcs agree. -/
theorem transfer_tendsto (h : IsChart e Ω B Ω' B') {p : E} (hp : p ∈ e.source) {γ : Set E}
    (hγ : IsArcAt Ω p γ) {Y : Type*} (f : E' → Y) (l : Filter Y) :
    Tendsto (f ∘ e) (𝓝[γ \ {p}] p) l ↔ Tendsto f (𝓝[e '' γ \ {e p}] (e p)) l := by
  have hs := h.arc_subset_source hp hγ
  obtain ⟨b, hb, -⟩ := hγ
  rw [← hb.map_nhdsWithin (e.continuousOn.mono hs) (e.injOn.mono hs), tendsto_map'_iff]

/-- `lem:transfer`: cluster sets along corresponding arcs agree. -/
theorem transfer_clusterSet (h : IsChart e Ω B Ω' B') {p : E} (hp : p ∈ e.source) {γ : Set E}
    (hγ : IsArcAt Ω p γ) {Y : Type*} [TopologicalSpace Y] (f : E' → Y) :
    clusterSet (f ∘ e) γ p = clusterSet f (e '' γ) (e p) := by
  have hs := h.arc_subset_source hp hγ
  obtain ⟨b, hb, -⟩ := hγ
  ext q
  simp only [clusterSet, mem_ofPred_eq, MapClusterPt]
  rw [← hb.map_nhdsWithin (e.continuousOn.mono hs) (e.injOn.mono hs), map_map]

/-- `lem:transfer`: `CC(f ∘ Ψ) = Ψ⁻¹(CC(f))`. -/
theorem transfer_curvConvSet (h : IsChart e Ω B Ω' B') {Y : Type*} [TopologicalSpace Y]
    (f : E' → Y) : curvConvSet Ω B (f ∘ e) = B ∩ e ⁻¹' curvConvSet Ω' B' f := by
  ext p
  constructor
  · rintro ⟨hpB, γ, hγ, q, hq⟩
    have hp := h.boundary_subset_source hpB
    exact ⟨hpB, (h.mem_boundary_iff hp).2 hpB, e '' γ,
      (transfer_isArcAt h hp (h.arc_subset_source hp hγ)).1 hγ, q,
      (transfer_tendsto h hp hγ f _).1 hq⟩
  · rintro ⟨hpB, -, γ', hγ', q, hq⟩
    have hp := h.boundary_subset_source hpB
    have hγ't : γ' ⊆ e.target :=
      h.symm.arc_subset_source (e.map_source hp) hγ'
    have hγ : e.symm '' γ' ⊆ e.source := fun _ ⟨z, hz, hze⟩ => hze ▸ e.map_target (hγ't hz)
    have himg : e '' (e.symm '' γ') = γ' := e.toPartialEquiv.image_symm_image_of_subset_target hγ't
    have harc : IsArcAt Ω p (e.symm '' γ') := by
      rw [transfer_isArcAt h hp hγ, himg]; exact hγ'
    exact ⟨hpB, _, harc, q, by rw [transfer_tendsto h hp harc, himg]; exact hq⟩

/-- `lem:transfer`: `φ` is a boundary function for `f` on `S' ⊆ B'` iff `φ ∘ Ψ` is one for
`f ∘ Ψ` on `Ψ⁻¹(S')`. -/
theorem transfer_isBoundaryFunction (h : IsChart e Ω B Ω' B') {Y : Type*} [TopologicalSpace Y]
    (f : E' → Y) {S' : Set E'} (hS' : S' ⊆ B') (φ : E' → Y) :
    IsBoundaryFunction Ω' f S' φ ↔
      IsBoundaryFunction Ω (f ∘ e) (e.source ∩ e ⁻¹' S') (φ ∘ e) := by
  constructor
  · rintro hφ p ⟨hp, hpS⟩
    obtain ⟨γ', hγ', hlim⟩ := hφ _ hpS
    have hγ't : γ' ⊆ e.target :=
      h.symm.arc_subset_source (e.map_source hp) hγ'
    have hγ : e.symm '' γ' ⊆ e.source := fun _ ⟨z, hz, hze⟩ => hze ▸ e.map_target (hγ't hz)
    have himg : e '' (e.symm '' γ') = γ' := e.toPartialEquiv.image_symm_image_of_subset_target hγ't
    have harc : IsArcAt Ω p (e.symm '' γ') := by
      rw [transfer_isArcAt h hp hγ, himg]; exact hγ'
    exact ⟨_, harc, by rw [transfer_tendsto h hp harc, himg]; exact hlim⟩
  · intro hφ x hx
    have hxt : x ∈ e.target := h.boundary_subset_target (hS' hx)
    have hp : e.symm x ∈ e.source := e.map_target hxt
    have hex : e (e.symm x) = x := e.right_inv hxt
    obtain ⟨γ, hγ, hlim⟩ := hφ _ ⟨hp, by rw [mem_preimage, hex]; exact hx⟩
    refine ⟨e '' γ, ?_, ?_⟩
    · have := (transfer_isArcAt h hp (h.arc_subset_source hp hγ)).1 hγ
      rwa [hex] at this
    · have := (transfer_tendsto h hp hγ f _).1 hlim
      simp only [comp_apply, hex] at this
      exact this

end Transfer

/-- `lem:locality`: if `W ∩ Ω = W ∩ Ω'` for a neighbourhood `W` of `p` and `f = f'` on `W ∩ Ω`,
then `f` has the limit `l` along some arc at `p` in `Ω` iff `f'` has it along some arc at `p` in
`Ω'`. -/
theorem curvConv_local {E : Type*} [TopologicalSpace E] [T2Space E] {Y : Type*} {Ω Ω' W : Set E}
    {p : E} (hW : W ∈ 𝓝 p) (hΩ : W ∩ Ω = W ∩ Ω') {f f' : E → Y} (hf : EqOn f f' (W ∩ Ω))
    (l : Filter Y) :
    (∃ γ, IsArcAt Ω p γ ∧ Tendsto f (𝓝[γ \ {p}] p) l) ↔
      ∃ γ, IsArcAt Ω' p γ ∧ Tendsto f' (𝓝[γ \ {p}] p) l := by
  have key : ∀ (Ω₁ Ω₂ : Set E) (f₁ f₂ : E → Y), W ∩ Ω₁ = W ∩ Ω₂ → EqOn f₁ f₂ (W ∩ Ω₁) →
      (∃ γ, IsArcAt Ω₁ p γ ∧ Tendsto f₁ (𝓝[γ \ {p}] p) l) →
      ∃ γ, IsArcAt Ω₂ p γ ∧ Tendsto f₂ (𝓝[γ \ {p}] p) l := by
    rintro Ω₁ Ω₂ f₁ f₂ hΩ₁ hf₁ ⟨γ, hγ, hlim⟩
    obtain ⟨γ', hγ', ⟨b, hb, hb'⟩, heq⟩ := hγ.exists_subarc_subset hW
    have hsub : γ' \ {p} ⊆ W ∩ Ω₁ := fun z hz => ⟨(hγ' hz.1).2, hb' hz⟩
    refine ⟨γ', ⟨b, hb, fun z hz => ((hΩ₁ ▸ hsub hz) : z ∈ W ∩ Ω₂).2⟩, ?_⟩
    rw [heq]
    refine hlim.congr' ?_
    rw [← heq]
    filter_upwards [self_mem_nhdsWithin] with z hz using hf₁ (hsub hz)
  refine ⟨key Ω Ω' f f' hΩ hf, key Ω' Ω f' f hΩ.symm fun z hz => (hf (hΩ ▸ hz)).symm⟩

/-! ### Charts (`def:charts`, `lem:charts`) -/

section Charts

open Complex

open scoped Real

theorem norm_sq_eq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-! #### The Cayley map -/

/-- The Cayley map `κ(z) = (z - i)/(z + i)` (`def:charts` (a)). -/
noncomputable def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse of the Cayley map, `w ↦ i(1 + w)/(1 - w)`. -/
noncomputable def cayleyInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem add_I_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at this
  linarith

theorem norm_sub_I_sq (z : ℂ) : ‖z - I‖ ^ 2 = ‖z + I‖ ^ 2 - 4 * z.im := by
  rw [norm_sq_eq_re_im, norm_sq_eq_re_im]
  simp only [sub_re, I_re, sub_im, I_im, add_re, add_im]
  ring

theorem norm_cayley_lt_one_iff {z : ℂ} (hz : 0 ≤ z.im) : ‖cayley z‖ < 1 ↔ 0 < z.im := by
  have hpos : 0 < ‖z + I‖ := norm_pos_iff.2 (add_I_ne_zero hz)
  rw [cayley, norm_div, div_lt_one hpos, ← sq_lt_sq₀ (norm_nonneg _) hpos.le, norm_sub_I_sq]
  constructor <;> intro h <;> linarith

theorem norm_cayley_le_one {z : ℂ} (hz : 0 ≤ z.im) : ‖cayley z‖ ≤ 1 := by
  have hpos : 0 < ‖z + I‖ := norm_pos_iff.2 (add_I_ne_zero hz)
  rw [cayley, norm_div, div_le_one hpos, ← sq_le_sq₀ (norm_nonneg _) hpos.le, norm_sub_I_sq]
  linarith

theorem norm_cayley_eq_one_iff {z : ℂ} (hz : 0 ≤ z.im) : ‖cayley z‖ = 1 ↔ z.im = 0 := by
  constructor
  · intro h
    by_contra h'
    have := (norm_cayley_lt_one_iff hz).2 (lt_of_le_of_ne hz (Ne.symm h'))
    linarith
  · intro h
    have hpos : 0 < ‖z + I‖ := norm_pos_iff.2 (add_I_ne_zero hz)
    rw [cayley, norm_div, div_eq_one_iff_eq hpos.ne']
    have := norm_sub_I_sq z
    rw [h, mul_zero, sub_zero] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

theorem cayley_ne_one {z : ℂ} (hz : 0 ≤ z.im) : cayley z ≠ 1 := by
  rw [cayley, Ne, div_eq_one_iff_eq (add_I_ne_zero hz)]
  intro h
  have := congrArg Complex.im h
  simp only [sub_im, I_im, add_im] at this
  linarith

theorem cayleyInv_cayley {z : ℂ} (hz : 0 ≤ z.im) : cayleyInv (cayley z) = z := by
  have hne := add_I_ne_zero hz
  have h1 : 1 - cayley z = 2 * I / (z + I) := by
    rw [cayley, eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring
  have h2 : 1 + cayley z = 2 * z / (z + I) := by
    rw [cayley, eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]; ring
  rw [cayleyInv, h1, h2, mul_div_assoc', div_div_div_cancel_right₀ hne, mul_comm (2 : ℂ) z,
    mul_comm I, mul_assoc, mul_div_assoc, div_self (mul_ne_zero two_ne_zero I_ne_zero), mul_one]

theorem cayley_cayleyInv {w : ℂ} (hw : w ≠ 1) : cayley (cayleyInv w) = w := by
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  have h1 : cayleyInv w - I = 2 * I * w / (1 - w) := by
    rw [cayleyInv, eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring
  have h2 : cayleyInv w + I = 2 * I / (1 - w) := by
    rw [cayleyInv, eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]; ring
  rw [cayley, h1, h2, div_div_div_cancel_right₀ hne]
  exact mul_div_cancel_left₀ w (mul_ne_zero two_ne_zero I_ne_zero)

theorem cayleyInv_im (w : ℂ) :
    (cayleyInv w).im = (1 - (w.re ^ 2 + w.im ^ 2)) / ((1 - w.re) ^ 2 + w.im ^ 2) := by
  simp only [cayleyInv, div_im, normSq_apply, mul_re, mul_im, I_re, I_im, add_re, add_im,
    sub_re, sub_im, one_re, one_im]
  rw [div_sub_div_same]
  congr 1 <;> ring

theorem cayleyInv_im_nonneg {w : ℂ} (hw : ‖w‖ ≤ 1) : 0 ≤ (cayleyInv w).im := by
  rw [cayleyInv_im]
  have : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    rw [← norm_sq_eq_re_im]; nlinarith [norm_nonneg w]
  apply div_nonneg <;> nlinarith

theorem cayleyInv_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayleyInv w).im := by
  rw [cayleyInv_im]
  have : w.re ^ 2 + w.im ^ 2 < 1 := by
    rw [← norm_sq_eq_re_im]; nlinarith [norm_nonneg w]
  have hre : w.re < 1 := by nlinarith [sq_nonneg w.im, sq_nonneg (w.re - 1)]
  apply div_pos <;> nlinarith

/-- `lem:charts` (a): the Cayley map as a homeomorphism of `ℍ ∪ ℝ` onto `(𝔻 ∪ C) \ {1}`. -/
noncomputable def cayleyPH : PartialHomeomorph ℂ ℂ where
  toFun := cayley
  invFun := cayleyInv
  source := {z | 0 ≤ z.im}
  target := closedBall 0 1 \ {1}
  map_source' _ hz := ⟨mem_closedBall_zero_iff.2 (norm_cayley_le_one hz), cayley_ne_one hz⟩
  map_target' _ hw := cayleyInv_im_nonneg (mem_closedBall_zero_iff.1 hw.1)
  left_inv' _ hz := cayleyInv_cayley hz
  right_inv' _ hw := cayley_cayleyInv hw.2
  continuousOn_toFun := by
    change ContinuousOn (fun z => (z - I) / (z + I)) _
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => add_I_ne_zero hz
  continuousOn_invFun := by
    change ContinuousOn (fun w => I * (1 + w) / (1 - w)) _
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => sub_ne_zero.2 (Ne.symm hw.2)

@[simp] theorem cayleyPH_apply (z : ℂ) : cayleyPH z = cayley z := rfl

@[simp] theorem cayleyPH_symm_apply (w : ℂ) : cayleyPH.symm w = cayleyInv w := rfl

theorem cayleyPH_source : cayleyPH.source = {z | 0 ≤ z.im} := rfl

theorem cayleyPH_target : cayleyPH.target = closedBall 0 1 \ {1} := rfl

/-- `lem:charts` (a): `κ` maps `ℍ` onto `𝔻` and `ℝ` onto `C \ {1}`. -/
theorem cayley_isChart : IsChart cayleyPH upper realAxis disc (circle \ {1}) where
  source_eq := by
    ext z
    simp only [cayleyPH_source, mem_ofPred_eq, mem_union]
    constructor
    · intro h; rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.le
      · exact h.ge
  target_eq := by
    ext w
    simp only [cayleyPH_target, Set.mem_sdiff, mem_closedBall_zero_iff, mem_singleton_iff, mem_union,
      mem_ball_zero_iff, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨h.le, fun h' => by rw [h', norm_one] at h; exact lt_irrefl _ h⟩
      · exact ⟨h1.le, h2⟩
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_ball_zero_iff.2 ((norm_cayley_lt_one_iff (le_of_lt hz)).2 hz)
    · intro hw
      have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
      refine ⟨cayleyInv w, cayleyInv_im_pos hw', cayley_cayleyInv fun h => ?_⟩
      rw [h, norm_one] at hw'
      exact lt_irrefl _ hw'
  disjoint := disjoint_left.2 fun z h1 h2 => by
    simp only [mem_ofPred_eq] at h1 h2; linarith
  disjoint' := disjoint_left.2 fun z h1 h2 => by
    have h1' : ‖z‖ < 1 := mem_ball_zero_iff.1 h1
    have h2' : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 h2.1
    linarith

/-- `lem:charts` (a): `|κ(z) - 1| → 0` as `|z| → ∞`. -/
theorem tendsto_cayley_cobounded : Tendsto cayley (Bornology.cobounded ℂ) (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hn := tendsto_norm_cobounded_atTop (E := ℂ)
  have hlim : Tendsto (fun z : ℂ => 2 / (‖z‖ - 1)) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ (-1) hn)
  refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_ hlim
  filter_upwards [hn.eventually_gt_atTop 1] with z hz
  have hne : z + I ≠ 0 := by
    intro h
    have : ‖z‖ = 1 := by rw [eq_neg_of_add_eq_zero_left h, norm_neg, norm_I]
    linarith
  have heq : cayley z - 1 = -(2 * I) / (z + I) := by
    rw [cayley, div_sub_one hne]; ring_nf
  have hle : ‖z‖ - 1 ≤ ‖z + I‖ := by
    have := norm_sub_norm_le z (-I)
    rw [sub_neg_eq_add, norm_neg, norm_I] at this
    exact this
  rw [heq, norm_div, norm_neg, norm_mul, norm_I, mul_one, RCLike.norm_two]
  exact div_le_div_of_nonneg_left zero_le_two (by linarith) hle

/-- `lem:charts` (a): `|κ⁻¹(w)| → ∞` as `w → 1`. -/
theorem tendsto_norm_cayleyInv : Tendsto (fun w => ‖cayleyInv w‖) (𝓝[≠] 1) atTop := by
  have h1 : Tendsto (fun w : ℂ => ‖I * (1 + w)‖) (𝓝[≠] 1) (𝓝 2) := by
    have : Tendsto (fun w : ℂ => ‖I * (1 + w)‖) (𝓝 1) (𝓝 ‖I * (1 + 1)‖) :=
      (continuous_const.mul (continuous_const.add continuous_id)).norm.tendsto 1
    rw [norm_mul, norm_I, one_mul, show (1 : ℂ) + 1 = 2 by norm_num, RCLike.norm_two] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun w : ℂ => ‖1 - w‖) (𝓝[≠] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun w : ℂ => ‖1 - w‖) (𝓝 1) (𝓝 ‖(1 : ℂ) - 1‖) :=
        (continuous_const.sub continuous_id).norm.tendsto 1
      rw [sub_self, norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hw))
  have h3 := h1.pos_mul_atTop two_pos (tendsto_inv_nhdsGT_zero.comp h2)
  refine h3.congr fun w => ?_
  simp only [comp_apply, cayleyInv, div_eq_mul_inv, norm_mul, norm_inv]

/-! #### The square `Q° ∪ X` and the chart `Ψ_ℍ` -/

/-- `Q° = (-1, 1) × (0, 1)`. -/
def openSquare : Set ℂ := {z | z.re ∈ Ioo (-1) 1 ∧ z.im ∈ Ioo 0 1}

/-- `X = (-1, 1) × {0}`. -/
def baseX : Set ℂ := {z | z.re ∈ Ioo (-1) 1 ∧ z.im = 0}

/-- `Q° ∪ X`. -/
def squareSource : Set ℂ := {z | z.re ∈ Ioo (-1) 1 ∧ z.im ∈ Ico 0 1}

theorem squareSource_eq : squareSource = openSquare ∪ baseX := by
  ext z
  simp only [squareSource, openSquare, baseX, mem_ofPred_eq, mem_union, mem_Ico, mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases h2.lt_or_eq with h | h
    · exact Or.inl ⟨h1, h, h3⟩
    · exact Or.inr ⟨h1, h.symm⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2.le, h3⟩
    · exact ⟨h1, h2.ge, by rw [h2]; exact one_pos⟩

theorem disjoint_openSquare_baseX : Disjoint openSquare baseX :=
  disjoint_left.2 fun z h1 h2 => by
    simp only [openSquare, baseX, mem_ofPred_eq, mem_Ioo] at h1 h2
    linarith [h1.2.1, h2.2]

theorem pi_mul_div_two_mem {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    π * x / 2 ∈ Ioo (-(π / 2)) (π / 2) := by
  have := Real.pi_pos
  constructor <;> nlinarith [hx.1, hx.2]

theorem two_div_pi_mul_arctan_mem (u : ℝ) : 2 / π * Real.arctan u ∈ Ioo (-1 : ℝ) 1 := by
  have hp := Real.pi_pos
  have h1 := Real.neg_pi_div_two_lt_arctan u
  have h2 := Real.arctan_lt_pi_div_two u
  constructor
  · rw [div_mul_eq_mul_div, lt_div_iff₀ hp]; linarith
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hp]; linarith

theorem tan_pi_mul_two_div_pi_mul_arctan (u : ℝ) :
    Real.tan (π * (2 / π * Real.arctan u) / 2) = u := by
  have hp := Real.pi_pos.ne'
  rw [show π * (2 / π * Real.arctan u) / 2 = Real.arctan u by field_simp, Real.tan_arctan]

theorem two_div_pi_mul_arctan_tan {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    2 / π * Real.arctan (Real.tan (π * x / 2)) = x := by
  have hp := Real.pi_pos.ne'
  have h := pi_mul_div_two_mem hx
  rw [Real.arctan_tan h.1 h.2]
  field_simp

/-- `Ψ_ℍ⟨x, y⟩ = tan(πx/2) + i y/(1 - y)` (`def:charts` (b)). -/
noncomputable def chartH (z : ℂ) : ℂ :=
  (Real.tan (π * z.re / 2) : ℂ) + ((z.im / (1 - z.im) : ℝ) : ℂ) * I

/-- The inverse of `Ψ_ℍ`. -/
noncomputable def chartHInv (w : ℂ) : ℂ :=
  ((2 / π * Real.arctan w.re : ℝ) : ℂ) + ((w.im / (1 + w.im) : ℝ) : ℂ) * I

@[simp] theorem chartH_re (z : ℂ) : (chartH z).re = Real.tan (π * z.re / 2) := by
  simp only [chartH, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring

@[simp] theorem chartH_im (z : ℂ) : (chartH z).im = z.im / (1 - z.im) := by
  simp only [chartH, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; ring

@[simp] theorem chartHInv_re (w : ℂ) : (chartHInv w).re = 2 / π * Real.arctan w.re := by
  simp only [chartHInv, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring

@[simp] theorem chartHInv_im (w : ℂ) : (chartHInv w).im = w.im / (1 + w.im) := by
  simp only [chartHInv, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; ring

theorem continuousOn_tan_pi_mul_re :
    ContinuousOn (fun z : ℂ => Real.tan (π * z.re / 2)) {z | z.re ∈ Ioo (-1) 1} :=
  Real.continuousOn_tan_Ioo.comp (by fun_prop) fun z hz => pi_mul_div_two_mem hz

/-- `lem:charts` (b): `Ψ_ℍ` as a homeomorphism of `Q° ∪ X` onto `ℍ ∪ ℝ`. -/
noncomputable def chartHPH : PartialHomeomorph ℂ ℂ where
  toFun := chartH
  invFun := chartHInv
  source := squareSource
  target := {w | 0 ≤ w.im}
  map_source' z hz := by
    simp only [mem_ofPred_eq, chartH_im]
    exact div_nonneg hz.2.1 (sub_pos.2 hz.2.2).le
  map_target' w hw := by
    refine ⟨by rw [chartHInv_re]; exact two_div_pi_mul_arctan_mem _, ?_, ?_⟩
    · rw [chartHInv_im]; exact div_nonneg hw (by simp only [mem_ofPred_eq] at hw; linarith)
    · have hw' : (0 : ℝ) ≤ w.im := hw
      rw [chartHInv_im, div_lt_one (by linarith)]; linarith
  left_inv' z hz := by
    have h1 : 1 - z.im ≠ 0 := (sub_pos.2 hz.2.2).ne'
    apply Complex.ext
    · simp only [chartHInv_re, chartH_re]; exact two_div_pi_mul_arctan_tan hz.1
    · simp only [chartHInv_im, chartH_im]; field_simp; ring
  right_inv' w hw := by
    have hw' : (0 : ℝ) ≤ w.im := hw
    have h1 : 1 + w.im ≠ 0 := by linarith
    apply Complex.ext
    · simp only [chartH_re, chartHInv_re]; exact tan_pi_mul_two_div_pi_mul_arctan _
    · simp only [chartH_im, chartHInv_im]; field_simp; ring
  continuousOn_toFun := by
    have h1 := continuousOn_tan_pi_mul_re.mono (fun z (hz : z ∈ squareSource) => hz.1)
    have h2 : ContinuousOn (fun z : ℂ => z.im / (1 - z.im)) squareSource :=
      ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => (sub_pos.2 hz.2.2).ne'
    exact (continuous_ofReal.comp_continuousOn h1).add
      ((continuous_ofReal.comp_continuousOn h2).mul continuousOn_const)
  continuousOn_invFun := by
    have h2 : ContinuousOn (fun w : ℂ => w.im / (1 + w.im)) {w | 0 ≤ w.im} :=
      ContinuousOn.div (by fun_prop) (by fun_prop) fun w (hw : 0 ≤ w.im) => by linarith
    exact (continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_arctan.comp continuous_re))).continuousOn.add
      ((continuous_ofReal.comp_continuousOn h2).mul continuousOn_const)

@[simp] theorem chartHPH_apply (z : ℂ) : chartHPH z = chartH z := rfl

@[simp] theorem chartHPH_symm_apply (w : ℂ) : chartHPH.symm w = chartHInv w := rfl

theorem chartHPH_source : chartHPH.source = squareSource := rfl

theorem chartHPH_target : chartHPH.target = {w | 0 ≤ w.im} := rfl

/-- `lem:charts` (b): `Ψ_ℍ` maps `Q°` onto `ℍ` and `X` onto `ℝ`. -/
theorem chartH_isChart : IsChart chartHPH openSquare baseX upper realAxis where
  source_eq := squareSource_eq
  target_eq := by
    ext w
    simp only [chartHPH_target, mem_ofPred_eq, mem_union]
    constructor
    · intro h; rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.le
      · exact h.ge
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < (chartH z).im
      rw [chartH_im]; exact div_pos hz.2.1 (sub_pos.2 hz.2.2)
    · intro hw
      have hw' : (0 : ℝ) < w.im := hw
      refine ⟨chartHInv w, ⟨by rw [chartHInv_re]; exact two_div_pi_mul_arctan_mem _, ?_, ?_⟩,
        chartHPH.right_inv hw'.le⟩
      · rw [chartHInv_im]; exact div_pos hw' (by linarith)
      · rw [chartHInv_im, div_lt_one (by linarith)]; linarith
  disjoint := disjoint_openSquare_baseX
  disjoint' := disjoint_left.2 fun z h1 h2 => by
    simp only [mem_ofPred_eq] at h1 h2; linarith

/-- `lem:charts` (b): on `X`, `Ψ_ℍ` is the increasing map `x ↦ tan(πx/2)`. -/
theorem chartH_ofReal (x : ℝ) : chartH x = (Real.tan (π * x / 2) : ℂ) := by
  simp [chartH]

theorem strictMonoOn_tan_pi_mul_div_two :
    StrictMonoOn (fun x : ℝ => Real.tan (π * x / 2)) (Ioo (-1) 1) := fun x hx y hy hxy =>
  Real.strictMonoOn_tan (pi_mul_div_two_mem hx) (pi_mul_div_two_mem hy)
    (by have := Real.pi_pos; nlinarith)

/-! #### The chart `Ψ_𝔻` and the sets `G°`, `G''` -/

theorem norm_one_sub_inv_sq {w : ℂ} (hw : w ≠ 0) :
    ‖1 - w⁻¹‖ ^ 2 = 1 + (1 - 2 * w.re) / ‖w‖ ^ 2 := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have : 1 - w⁻¹ = (w - 1) / w := by field_simp
  rw [this, norm_div, div_pow, norm_sq_eq_re_im (w - 1)]
  have h2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := norm_sq_eq_re_im w
  simp only [sub_re, one_re, sub_im, one_im, sub_zero]
  field_simp
  rw [h2]; ring

theorem norm_one_sub_inv_lt_one_iff {w : ℂ} (hw : w ≠ 0) : ‖1 - w⁻¹‖ < 1 ↔ 1 / 2 < w.re := by
  have hn : 0 < ‖w‖ ^ 2 := by have := norm_pos_iff.2 hw; positivity
  rw [← sq_lt_one_iff₀ (norm_nonneg _), norm_one_sub_inv_sq hw]
  constructor
  · intro h
    by_contra hc
    have : 0 ≤ (1 - 2 * w.re) / ‖w‖ ^ 2 := div_nonneg (by linarith) hn.le
    linarith
  · intro h
    have : (1 - 2 * w.re) / ‖w‖ ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) hn
    linarith

theorem norm_one_sub_inv_eq_one_iff {w : ℂ} (hw : w ≠ 0) : ‖1 - w⁻¹‖ = 1 ↔ w.re = 1 / 2 := by
  have hn : 0 < ‖w‖ ^ 2 := by have := norm_pos_iff.2 hw; positivity
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, norm_one_sub_inv_sq hw]
  constructor
  · intro h
    have : (1 - 2 * w.re) / ‖w‖ ^ 2 = 0 := by linarith
    rcases div_eq_zero_iff.1 this with h' | h'
    · linarith
    · exact absurd h' hn.ne'
  · intro h
    rw [h]; simp

theorem norm_one_sub_inv_le_one_iff {w : ℂ} (hw : w ≠ 0) : ‖1 - w⁻¹‖ ≤ 1 ↔ 1 / 2 ≤ w.re := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, norm_one_sub_inv_lt_one_iff hw,
    norm_one_sub_inv_eq_one_iff hw, eq_comm (a := (1 : ℝ) / 2)]

/-- `G° = {z ∈ 𝔻 : Re (1 - z)⁻¹ < 1}`. -/
def gOpen : Set ℂ := {z | z ∈ disc ∧ ((1 - z)⁻¹).re < 1}

/-- `G'' = {z ∈ 𝔻 : Re (1 - z)⁻¹ ≤ 3/4}`. -/
def gClosed : Set ℂ := {z | z ∈ disc ∧ ((1 - z)⁻¹).re ≤ 3 / 4}

/-- The point `w = ½(1 + y) + i tan(πx/2)` of the chart `Ψ_𝔻`. -/
noncomputable def chartDw (z : ℂ) : ℂ :=
  (((1 + z.im) / 2 : ℝ) : ℂ) + (Real.tan (π * z.re / 2) : ℂ) * I

/-- `Ψ_𝔻⟨x, y⟩ = 1 - 1/w`, `w = ½(1 + y) + i tan(πx/2)` (`def:charts` (c)). -/
noncomputable def chartD (z : ℂ) : ℂ := 1 - (chartDw z)⁻¹

/-- The inverse of `Ψ_𝔻`. -/
noncomputable def chartDInv (z : ℂ) : ℂ :=
  ((2 / π * Real.arctan ((1 - z)⁻¹).im : ℝ) : ℂ) + ((2 * ((1 - z)⁻¹).re - 1 : ℝ) : ℂ) * I

@[simp] theorem chartDw_re (z : ℂ) : (chartDw z).re = (1 + z.im) / 2 := by
  simp only [chartDw, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring

@[simp] theorem chartDw_im (z : ℂ) : (chartDw z).im = Real.tan (π * z.re / 2) := by
  simp only [chartDw, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; ring

@[simp] theorem chartDInv_re (z : ℂ) : (chartDInv z).re = 2 / π * Real.arctan ((1 - z)⁻¹).im := by
  simp only [chartDInv, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring

@[simp] theorem chartDInv_im (z : ℂ) : (chartDInv z).im = 2 * ((1 - z)⁻¹).re - 1 := by
  simp only [chartDInv, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; ring

theorem chartDw_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : chartDw z ≠ 0 := fun h => by
  have := congrArg Complex.re h
  rw [chartDw_re, zero_re] at this
  linarith

theorem one_sub_chartD (z : ℂ) : (1 - chartD z)⁻¹ = chartDw z := by
  rw [chartD, sub_sub_cancel, inv_inv]

theorem chartD_ne_one {z : ℂ} (hz : 0 ≤ z.im) : chartD z ≠ 1 := by
  rw [chartD, Ne, sub_eq_self, inv_eq_zero]
  exact chartDw_ne_zero hz

theorem eq_one_sub_inv {z : ℂ} : z = 1 - ((1 - z)⁻¹)⁻¹ := by
  rw [inv_inv, sub_sub_cancel]

theorem one_sub_inv_ne_zero {z : ℂ} (hz : z ≠ 1) : (1 - z)⁻¹ ≠ 0 :=
  inv_ne_zero (sub_ne_zero.2 (Ne.symm hz))

/-- For `z ≠ 1`: `|z| ≤ 1 ↔ Re (1 - z)⁻¹ ≥ 1/2`, and similarly for `<`, `=`. -/
theorem norm_le_one_iff_re {z : ℂ} (hz : z ≠ 1) : ‖z‖ ≤ 1 ↔ 1 / 2 ≤ ((1 - z)⁻¹).re := by
  conv_lhs => rw [eq_one_sub_inv (z := z)]
  exact norm_one_sub_inv_le_one_iff (one_sub_inv_ne_zero hz)

theorem norm_lt_one_iff_re {z : ℂ} (hz : z ≠ 1) : ‖z‖ < 1 ↔ 1 / 2 < ((1 - z)⁻¹).re := by
  conv_lhs => rw [eq_one_sub_inv (z := z)]
  exact norm_one_sub_inv_lt_one_iff (one_sub_inv_ne_zero hz)

theorem norm_eq_one_iff_re {z : ℂ} (hz : z ≠ 1) : ‖z‖ = 1 ↔ ((1 - z)⁻¹).re = 1 / 2 := by
  conv_lhs => rw [eq_one_sub_inv (z := z)]
  exact norm_one_sub_inv_eq_one_iff (one_sub_inv_ne_zero hz)

theorem ne_one_of_mem_disc {z : ℂ} (hz : z ∈ disc) : z ≠ 1 := fun h => by
  rw [h, mem_ball_zero_iff, norm_one] at hz; exact lt_irrefl _ hz

theorem mem_target_D {z : ℂ} (hz : z ∈ gOpen ∪ (circle \ {1})) :
    z ≠ 1 ∧ 1 / 2 ≤ ((1 - z)⁻¹).re ∧ ((1 - z)⁻¹).re < 1 := by
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hne := ne_one_of_mem_disc h1
    exact ⟨hne, ((norm_lt_one_iff_re hne).1 (mem_ball_zero_iff.1 h1)).le, h2⟩
  · have hne : z ≠ 1 := h2
    have := (norm_eq_one_iff_re hne).1 (mem_sphere_zero_iff_norm.1 h1)
    exact ⟨hne, this.ge, by rw [this]; norm_num⟩

/-- `lem:charts` (c): `Ψ_𝔻` as a homeomorphism of `Q° ∪ X` onto `G° ∪ (C \ {1})`. -/
noncomputable def chartDPH : PartialHomeomorph ℂ ℂ where
  toFun := chartD
  invFun := chartDInv
  source := squareSource
  target := gOpen ∪ (circle \ {1})
  map_source' z hz := by
    have h0 : 0 ≤ z.im := hz.2.1
    have hne := chartD_ne_one h0
    have hre : ((1 - chartD z)⁻¹).re = (1 + z.im) / 2 := by rw [one_sub_chartD z, chartDw_re]
    rcases hz.2.1.lt_or_eq with hpos | hzero
    · refine Or.inl ⟨mem_ball_zero_iff.2 ((norm_lt_one_iff_re hne).2 (by rw [hre]; linarith)), ?_⟩
      rw [hre]; linarith [hz.2.2]
    · refine Or.inr ⟨mem_sphere_zero_iff_norm.2 ((norm_eq_one_iff_re hne).2 (by
        rw [hre, ← hzero]; norm_num)), hne⟩
  map_target' z hz := by
    obtain ⟨hne, h1, h2⟩ := mem_target_D hz
    refine ⟨by rw [chartDInv_re]; exact two_div_pi_mul_arctan_mem _, ?_, ?_⟩
    · rw [chartDInv_im]; linarith
    · rw [chartDInv_im]; linarith
  left_inv' z hz := by
    have h0 : 0 ≤ z.im := hz.2.1
    apply Complex.ext
    · rw [chartDInv_re, one_sub_chartD z, chartDw_im]; exact two_div_pi_mul_arctan_tan hz.1
    · rw [chartDInv_im, one_sub_chartD z, chartDw_re]; ring
  right_inv' z hz := by
    obtain ⟨hne, h1, h2⟩ := mem_target_D hz
    have hw : chartDw (chartDInv z) = (1 - z)⁻¹ := by
      apply Complex.ext
      · rw [chartDw_re, chartDInv_im]; ring
      · rw [chartDw_im, chartDInv_re]; exact tan_pi_mul_two_div_pi_mul_arctan _
    show chartD (chartDInv z) = z
    rw [chartD, hw, inv_inv, sub_sub_cancel]
  continuousOn_toFun := by
    have h1 := continuousOn_tan_pi_mul_re.mono (fun z (hz : z ∈ squareSource) => hz.1)
    have hw : ContinuousOn chartDw squareSource :=
      (continuous_ofReal.comp (by fun_prop : Continuous fun z : ℂ => (1 + z.im) / 2)).continuousOn.add
        ((continuous_ofReal.comp_continuousOn h1).mul continuousOn_const)
    exact continuousOn_const.sub (hw.inv₀ fun z hz => chartDw_ne_zero hz.2.1)
  continuousOn_invFun := by
    have hinv : ContinuousOn (fun z : ℂ => (1 - z)⁻¹) (gOpen ∪ (circle \ {1})) :=
      (continuous_const.sub continuous_id).continuousOn.inv₀ fun z hz =>
        sub_ne_zero.2 (Ne.symm (mem_target_D hz).1)
    exact (continuous_ofReal.comp_continuousOn ((continuous_const.mul
      Real.continuous_arctan).comp_continuousOn (continuous_im.comp_continuousOn hinv))).add
      ((continuous_ofReal.comp_continuousOn ((continuous_const.mul
        continuous_re).comp_continuousOn hinv |>.sub continuousOn_const)).mul continuousOn_const)

@[simp] theorem chartDPH_apply (z : ℂ) : chartDPH z = chartD z := rfl

@[simp] theorem chartDPH_symm_apply (w : ℂ) : chartDPH.symm w = chartDInv w := rfl

theorem chartDPH_source : chartDPH.source = squareSource := rfl

theorem chartDPH_target : chartDPH.target = gOpen ∪ (circle \ {1}) := rfl

/-- `lem:charts` (c): `Ψ_𝔻` maps `Q°` onto `G°` and `X` onto `C \ {1}`. -/
theorem chartD_isChart : IsChart chartDPH openSquare baseX gOpen (circle \ {1}) where
  source_eq := squareSource_eq
  target_eq := rfl
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzs : z ∈ squareSource := squareSource_eq ▸ Or.inl hz
      rcases chartDPH.map_source hzs with h | ⟨h, -⟩
      · exact h
      · exfalso
        have h0 : 0 ≤ z.im := hz.2.1.le
        have hne := chartD_ne_one h0
        have := (norm_eq_one_iff_re hne).1 (mem_sphere_zero_iff_norm.1 h)
        rw [one_sub_chartD z, chartDw_re] at this
        linarith [hz.2.1]
    · intro hw
      have hwt : w ∈ chartDPH.target := Or.inl hw
      refine ⟨chartDInv w, ?_, chartDPH.right_inv hwt⟩
      have hs := chartDPH.map_target hwt
      have hne := ne_one_of_mem_disc hw.1
      refine ⟨hs.1, ?_, hs.2.2⟩
      show 0 < (chartDInv w).im
      rw [chartDInv_im]
      have := (norm_lt_one_iff_re hne).1 (mem_ball_zero_iff.1 hw.1)
      linarith
  disjoint := disjoint_openSquare_baseX
  disjoint' := disjoint_left.2 fun z h1 h2 => by
    have h1' : ‖z‖ < 1 := mem_ball_zero_iff.1 h1.1
    have h2' : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 h2.1
    linarith

theorem gClosed_subset_gOpen : gClosed ⊆ gOpen := fun z hz => ⟨hz.1, by linarith [hz.2]⟩

/-- `lem:charts` (c): `G''` is closed in `𝔻`. -/
theorem isClosed_gClosed : IsClosed ((Subtype.val : disc → ℂ) ⁻¹' gClosed) := by
  have hc : Continuous fun z : disc => ((1 - (z : ℂ))⁻¹).re :=
    continuous_re.comp ((continuous_const.sub continuous_subtype_val).inv₀ fun z =>
      sub_ne_zero.2 (Ne.symm (ne_one_of_mem_disc z.2)))
  have : (Subtype.val : disc → ℂ) ⁻¹' gClosed = {z : disc | ((1 - (z : ℂ))⁻¹).re ≤ 3 / 4} := by
    ext z
    simp only [gClosed, mem_preimage, mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  rw [this]
  exact isClosed_le hc continuous_const

/-- `lem:charts` (c): `G''` contains a neighbourhood in `𝔻` of each point of `C \ {1}`. -/
theorem exists_ball_inter_disc_subset_gClosed {x : ℂ} (hx : x ∈ circle) (hx1 : x ≠ 1) :
    ∃ r > 0, ball x r ∩ disc ⊆ gClosed := by
  have hc : ContinuousAt (fun z : ℂ => ((1 - z)⁻¹).re) x :=
    continuous_re.continuousAt.comp ((continuous_const.sub continuous_id).continuousAt.inv₀
      (sub_ne_zero.2 (Ne.symm hx1)))
  have hval : ((1 - x)⁻¹).re = 1 / 2 := (norm_eq_one_iff_re hx1).1 (mem_sphere_zero_iff_norm.1 hx)
  have hev : ∀ᶠ z in 𝓝 x, ((1 - z)⁻¹).re < 3 / 4 :=
    hc.eventually (gt_mem_nhds (show ((1 - x)⁻¹).re < 3 / 4 by rw [hval]; norm_num))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hev
  exact ⟨r, hr, fun z hz => ⟨hz.2, (hball hz.1).le⟩⟩

/-- `lem:charts` (c): `G''` is disjoint from the radius `[0, 1)`. -/
theorem ofReal_not_mem_gClosed {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) : (t : ℂ) ∉ gClosed := by
  rintro ⟨-, h⟩
  have h1 : (1 - (t : ℂ))⁻¹ = ((1 - t)⁻¹ : ℝ) := by push_cast; ring
  rw [h1, ofReal_re] at h
  have : 1 ≤ (1 - t)⁻¹ := (one_le_inv₀ (sub_pos.2 ht)).2 (by linarith)
  linarith

end Charts

/-! #### The strip map `𝓔_h` -/

section StripExp

open Complex

open scoped Real

/-- `𝓔_h(z) = e^{πz/h}` (`def:charts` (d)). -/
noncomputable def stripExp (h : ℝ) (z : ℂ) : ℂ := Complex.exp (((π / h : ℝ) : ℂ) * z)

/-- The open strip `0 < Im z < h`. -/
def openStrip (h : ℝ) : Set ℂ := {z | 0 < z.im ∧ z.im < h}

/-- The two boundary lines `Im z = 0` and `Im z = h` of the strip. -/
def stripLines (h : ℝ) : Set ℂ := {z | z.im = 0 ∨ z.im = h}

theorem stripExp_im (h : ℝ) (z : ℂ) :
    (stripExp h z).im = Real.exp (π / h * z.re) * Real.sin (π / h * z.im) := by
  rw [stripExp, Complex.exp_im, re_ofReal_mul, im_ofReal_mul]

theorem stripExp_ne_zero (h : ℝ) (z : ℂ) : stripExp h z ≠ 0 := Complex.exp_ne_zero _

/-- `lem:charts` (d): `𝓔_h` as a homeomorphism of `0 ≤ Im z ≤ h` onto `(ℍ ∪ ℝ) \ {0}`. -/
noncomputable def stripExpPH (h : ℝ) (hh : 0 < h) : PartialHomeomorph ℂ ℂ where
  toFun := stripExp h
  invFun w := ((h / π : ℝ) : ℂ) * Complex.log w
  source := {z | 0 ≤ z.im ∧ z.im ≤ h}
  target := {w | 0 ≤ w.im} \ {0}
  map_source' z hz := by
    refine ⟨?_, stripExp_ne_zero h z⟩
    show 0 ≤ (stripExp h z).im
    rw [stripExp_im]
    have hp := Real.pi_pos
    refine mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg (div_nonneg hp.le hh.le) hz.1) ?_)
    rw [div_mul_eq_mul_div, div_le_iff₀ hh]; nlinarith [hz.2]
  map_target' w hw := by
    have hp := Real.pi_pos
    have harg0 : 0 ≤ arg w := Complex.arg_nonneg_iff.2 hw.1
    have hargπ : arg w ≤ π := Complex.arg_le_pi w
    simp only [mem_ofPred_eq, im_ofReal_mul, Complex.log_im]
    refine ⟨mul_nonneg (div_nonneg hh.le hp.le) harg0, ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]; nlinarith
  left_inv' z hz := by
    have hp := Real.pi_pos
    have him : (((π / h : ℝ) : ℂ) * z).im = π / h * z.im := im_ofReal_mul _ _
    have hle : π / h * z.im ≤ π := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hh]; nlinarith [hz.2]
    show ((h / π : ℝ) : ℂ) * Complex.log (stripExp h z) = z
    rw [stripExp, Complex.log_exp (by rw [him]; nlinarith [hz.1, div_pos hp hh])
      (by rw [him]; exact hle), ← mul_assoc, ← ofReal_mul,
      show h / π * (π / h) = 1 by field_simp, ofReal_one, one_mul]
  right_inv' w hw := by
    have hp := Real.pi_pos
    show stripExp h (((h / π : ℝ) : ℂ) * Complex.log w) = w
    rw [stripExp, ← mul_assoc, ← ofReal_mul, show π / h * (h / π) = 1 by field_simp, ofReal_one,
      one_mul, Complex.exp_log hw.2]
  continuousOn_toFun := (by unfold stripExp; fun_prop : Continuous (stripExp h)).continuousOn
  continuousOn_invFun := by
    refine continuousOn_const.mul fun w hw => ?_
    by_cases hs : w ∈ slitPlane
    · exact (continuousAt_clog hs).continuousWithinAt
    · have hw0 : w ≠ 0 := hw.2
      rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hs
      have hre : w.re < 0 := lt_of_le_of_ne hs.1 fun h0 => hw0 (Complex.ext h0 hs.2)
      have hlog : (Complex.log : ℂ → ℂ) = fun z => (Real.log ‖z‖ : ℂ) + (arg z : ℂ) * I :=
        funext fun z => rfl
      rw [hlog]
      refine ContinuousWithinAt.add ?_ ?_
      · exact (continuous_ofReal.continuousAt.comp ((Real.continuousAt_log
          (norm_ne_zero_iff.2 hw0)).comp continuous_norm.continuousAt)).continuousWithinAt
      · exact (continuous_ofReal.continuousAt.comp_continuousWithinAt
          ((continuousWithinAt_arg_of_re_neg_of_im_zero hre hs.2).mono
            fun z hz => hz.1)).mul continuousWithinAt_const

@[simp] theorem stripExpPH_apply {h : ℝ} (hh : 0 < h) (z : ℂ) :
    stripExpPH h hh z = stripExp h z := rfl

theorem stripExpPH_source {h : ℝ} (hh : 0 < h) :
    (stripExpPH h hh).source = {z | 0 ≤ z.im ∧ z.im ≤ h} := rfl

theorem stripExpPH_target {h : ℝ} (hh : 0 < h) :
    (stripExpPH h hh).target = {w | 0 ≤ w.im} \ {0} := rfl

/-- `lem:charts` (d): `𝓔_h` maps the open strip onto `ℍ` and its boundary lines onto
`ℝ \ {0}`. -/
theorem stripExp_isChart {h : ℝ} (hh : 0 < h) :
    IsChart (stripExpPH h hh) (openStrip h) (stripLines h) upper (realAxis \ {0}) where
  source_eq := by
    ext z
    simp only [stripExpPH_source, openStrip, stripLines, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1.lt_or_eq with h1 | h1
      · rcases h2.lt_or_eq with h2 | h2
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl h1.symm)
    · rintro (⟨h1, h2⟩ | h1 | h1)
      · exact ⟨h1.le, h2.le⟩
      · exact ⟨h1.ge, by rw [h1]; exact hh.le⟩
      · exact ⟨by rw [h1]; exact hh.le, h1.le⟩
  target_eq := by
    ext w
    simp only [stripExpPH_target, Set.mem_sdiff, mem_ofPred_eq, mem_singleton_iff, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1.lt_or_eq with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1.symm, h2⟩
    · rintro (h1 | ⟨h1, h2⟩)
      · exact ⟨h1.le, fun h' => by rw [h', zero_im] at h1; exact lt_irrefl _ h1⟩
      · exact ⟨h1.ge, h2⟩
  image_eq := by
    have hp := Real.pi_pos
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < (stripExp h z).im
      rw [stripExp_im]
      refine mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi
        (mul_pos (div_pos hp hh) hz.1) ?_)
      rw [div_mul_eq_mul_div, div_lt_iff₀ hh]; nlinarith [hz.2]
    · intro hw
      have hw' : 0 < w.im := hw
      have hw0 : w ≠ 0 := fun h' => by rw [h', zero_im] at hw'; exact lt_irrefl _ hw'
      have hwt : w ∈ (stripExpPH h hh).target := ⟨hw'.le, hw0⟩
      refine ⟨(stripExpPH h hh).symm w, ?_, (stripExpPH h hh).right_inv hwt⟩
      have harg0 : 0 < arg w := lt_of_le_of_ne (Complex.arg_nonneg_iff.2 hw'.le) fun h' =>
        by have := (Complex.arg_eq_zero_iff.1 h'.symm).2; linarith
      have hargπ : arg w < π := lt_of_le_of_ne (Complex.arg_le_pi w) fun h' =>
        by have := (Complex.arg_eq_pi_iff.1 h').2; linarith
      show 0 < (((h / π : ℝ) : ℂ) * Complex.log w).im ∧ (((h / π : ℝ) : ℂ) * Complex.log w).im < h
      rw [im_ofReal_mul, Complex.log_im]
      refine ⟨mul_pos (div_pos hh hp) harg0, ?_⟩
      rw [div_mul_eq_mul_div, div_lt_iff₀ hp]; nlinarith
  disjoint := disjoint_left.2 fun z h1 h2 => by
    rcases h2 with h2 | h2
    · linarith [h1.1]
    · linarith [h1.2]
  disjoint' := disjoint_left.2 fun z h1 h2 => by
    have : (0 : ℝ) < z.im := h1
    have h2' : z.im = 0 := h2.1
    linarith

/-- `lem:charts` (d): on `Im z = 0`, `𝓔_h` is the increasing map `x ↦ e^{πx/h}` onto
`(0, ∞)`. -/
theorem stripExp_ofReal (h x : ℝ) : stripExp h x = (Real.exp (π / h * x) : ℂ) := by
  rw [stripExp, ← ofReal_mul, ← Complex.ofReal_exp]

/-- `lem:charts` (d): on `Im z = h`, `𝓔_h` is the decreasing map `x ↦ -e^{πx/h}` onto
`(-∞, 0)`. -/
theorem stripExp_add_I {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    stripExp h (x + h * I) = -(Real.exp (π / h * x) : ℂ) := by
  have : ((π / h : ℝ) : ℂ) * (x + h * I) = ((π / h * x : ℝ) : ℂ) + π * I := by
    push_cast
    rw [mul_add, ← mul_assoc, div_mul_cancel₀ (π : ℂ) (ofReal_ne_zero.2 hh)]
  rw [stripExp, this, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]; ring

end StripExp

/-! ### Geometry near a boundary point (`lem:disc-geometry`) and arcs of the circle -/

section DiscGeometry

open Complex MeasureTheory

open scoped Real

/-- The point `e^{it}` of the unit circle. -/
noncomputable def expI (t : ℝ) : ℂ := Complex.exp (t * I)

theorem norm_expI (t : ℝ) : ‖expI t‖ = 1 := Complex.norm_exp_ofReal_mul_I t

theorem expI_mem_circle (t : ℝ) : expI t ∈ circle := mem_sphere_zero_iff_norm.2 (norm_expI t)

theorem expI_add (s t : ℝ) : expI (s + t) = expI s * expI t := by
  rw [expI, expI, expI, ← Complex.exp_add]; push_cast; ring_nf

theorem expI_add_int_mul (t : ℝ) (k : ℤ) : expI (t + k * (2 * π)) = expI t := by
  have : expI (k * (2 * π)) = 1 := by
    rw [expI, show ((k * (2 * π) : ℝ) : ℂ) * I = k * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  rw [expI_add, this, mul_one]

theorem expI_arg {x : ℂ} (hx : ‖x‖ = 1) : expI (arg x) = x := by
  have := Complex.norm_mul_exp_arg_mul_I x
  rwa [hx, ofReal_one, one_mul] at this

/-- The closed arc of `C` from `e^{iθ}` counterclockwise to `e^{i(θ + ℓ)}`. -/
def circleArc (θ ℓ : ℝ) : Set ℂ := expI '' Icc θ (θ + ℓ)

/-- The open arc of `C` from `e^{iθ}` to `e^{i(θ + ℓ)}` (the relative interior of `circleArc θ ℓ`
when `0 < ℓ < 2π`). -/
def circleArcOpen (θ ℓ : ℝ) : Set ℂ := expI '' Ioo θ (θ + ℓ)

theorem circleArc_subset_circle (θ ℓ : ℝ) : circleArc θ ℓ ⊆ circle := by
  rintro _ ⟨t, -, rfl⟩; exact expI_mem_circle t

theorem left_mem_circleArc {θ ℓ : ℝ} (hℓ : 0 ≤ ℓ) : expI θ ∈ circleArc θ ℓ :=
  ⟨θ, ⟨le_rfl, by linarith⟩, rfl⟩

theorem right_mem_circleArc {θ ℓ : ℝ} (hℓ : 0 ≤ ℓ) : expI (θ + ℓ) ∈ circleArc θ ℓ :=
  ⟨θ + ℓ, ⟨by linarith, le_rfl⟩, rfl⟩

/-- Chord length: `|e^{it} - e^{is}| = 2 |sin ((t - s)/2)|`. -/
theorem norm_expI_sub_expI (s t : ℝ) : ‖expI t - expI s‖ = 2 * |Real.sin ((t - s) / 2)| := by
  have h : expI t - expI s = expI s * (Complex.exp (I * ((t - s : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, mul_comm I, ← expI, ← expI_add, add_sub_cancel]
  rw [h, norm_mul, norm_expI, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul,
    Real.norm_two, Real.norm_eq_abs]

/-- `lem:disc-geometry` (c): any arc of `C` between `w₁, w₂` has length at least `|w₁ - w₂|`. -/
theorem norm_expI_sub_le (s t : ℝ) : ‖expI t - expI s‖ ≤ |t - s| := by
  rw [norm_expI_sub_expI]
  have := Real.abs_sin_le_abs (x := (t - s) / 2)
  rw [abs_div, abs_two] at this
  linarith

theorem abs_sin_half_le {x b : ℝ} (hx : |x| ≤ b) (hb : b ≤ π) :
    |Real.sin (x / 2)| ≤ Real.sin (b / 2) := by
  have key : ∀ y, 0 ≤ y → y ≤ b → 0 ≤ Real.sin (y / 2) ∧ Real.sin (y / 2) ≤ Real.sin (b / 2) :=
    fun y hy hyb => ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith),
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
        (by linarith)⟩
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    obtain ⟨h1, h2⟩ := key x h hx
    rwa [abs_of_nonneg h1]
  · rw [abs_of_nonpos h] at hx
    obtain ⟨h1, h2⟩ := key (-x) (by linarith) hx
    rw [show -x / 2 = -(x / 2) by ring, Real.sin_neg] at h1 h2
    rw [abs_of_nonpos (by linarith)]
    exact h2

/-- `lem:disc-geometry` (c): if `0 ≤ ℓ ≤ π` and the endpoints of the arc `circleArc θ ℓ` are at
distance `< δ`, the arc lies in the `δ`-balls about both endpoints. -/
theorem shortArc_subset_ball {θ ℓ δ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓπ : ℓ ≤ π)
    (hδ : ‖expI (θ + ℓ) - expI θ‖ < δ) :
    circleArc θ ℓ ⊆ ball (expI θ) δ ∩ ball (expI (θ + ℓ)) δ := by
  have hs : 0 ≤ Real.sin (ℓ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rw [norm_expI_sub_expI, add_sub_cancel_left, abs_of_nonneg hs] at hδ
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, norm_expI_sub_expI]
    have := abs_sin_half_le (x := t - θ) (b := ℓ) (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]) hℓπ
    linarith
  · rw [mem_ball, dist_eq_norm, norm_expI_sub_expI]
    have := abs_sin_half_le (x := t - (θ + ℓ)) (b := ℓ)
      (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]) hℓπ
    linarith

/-- `lem:disc-geometry` (c): any two points of `C` are the endpoints of an arc `circleArc θ ℓ`
with `0 ≤ ℓ ≤ π` (the shorter arc between them). -/
theorem exists_shortArc {x x' : ℂ} (hx : x ∈ circle) (hx' : x' ∈ circle) :
    ∃ θ ℓ : ℝ, 0 ≤ ℓ ∧ ℓ ≤ π ∧
      ((expI θ = x ∧ expI (θ + ℓ) = x') ∨ (expI θ = x' ∧ expI (θ + ℓ) = x)) := by
  have h1 := expI_arg (mem_sphere_zero_iff_norm.1 hx)
  have h2 := expI_arg (mem_sphere_zero_iff_norm.1 hx')
  set d := toIocMod Real.two_pi_pos (-π) (arg x' - arg x) with hd
  have hdI := toIocMod_mem_Ioc Real.two_pi_pos (-π) (arg x' - arg x)
  rw [← hd] at hdI
  have hk := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-π) (arg x' - arg x)
  rw [← hd, zsmul_eq_mul] at hk
  have he : expI (arg x + d) = x' := by
    rw [← h2, ← expI_add_int_mul (arg x + d) (toIocDiv Real.two_pi_pos (-π) (arg x' - arg x))]
    congr 1; linarith
  rcases le_total 0 d with h | h
  · exact ⟨arg x, d, h, by linarith [hdI.2], Or.inl ⟨h1, he⟩⟩
  · refine ⟨arg x + d, -d, by linarith, by linarith [hdI.1], Or.inr ⟨he, ?_⟩⟩
    rw [add_neg_cancel_right, h1]

/-- `lem:disc-geometry` (d): finitely many arcs `circleArc (θ i) (ℓ i)` (`0 ≤ ℓ i ≤ 2π`) with
pairwise disjoint interiors have total length at most `2π`. The length of `circleArc θ ℓ` is `ℓ`,
the Lebesgue measure of its set of angles. -/
theorem sum_le_two_pi_of_pairwiseDisjoint {ι : Type*} (s : Finset ι) (θ ℓ : ι → ℝ)
    (hℓ : ∀ i ∈ s, 0 ≤ ℓ i ∧ ℓ i ≤ 2 * π)
    (hd : (s : Set ι).PairwiseDisjoint fun i => circleArcOpen (θ i) (ℓ i)) :
    ∑ i ∈ s, ℓ i ≤ 2 * π := by
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  let mk : ℝ → AddCircle (2 * π) := QuotientAddGroup.mk
  set U : ι → Set (AddCircle (2 * π)) := fun i => mk '' Ioo (θ i) (θ i + ℓ i) with hU
  have hUo : ∀ i, IsOpen (U i) := fun i => QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hmk : ∀ a b : ℝ, mk a = mk b → expI a = expI b := by
    intro a b hab
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hab)
    rw [zsmul_eq_mul] at hk
    rw [show b = a + k * (2 * π) by linarith, expI_add_int_mul]
  have hUd : (s : Set ι).PairwiseDisjoint U := by
    intro i hi j hj hij
    refine disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact disjoint_left.1 (hd hi hj hij) ⟨a, ha, rfl⟩ ⟨b, hb, hmk b a hab⟩
  have hmeas : ∀ i ∈ s, ENNReal.ofReal (ℓ i) ≤ volume (U i) := by
    intro i hi
    have hmp := AddCircle.measurePreserving_mk (2 * π) (θ i)
    rw [← hmp.measure_preimage (hUo i).measurableSet.nullMeasurableSet,
      Measure.restrict_apply' measurableSet_Ioc]
    calc ENNReal.ofReal (ℓ i) = volume (Ioo (θ i) (θ i + ℓ i)) := by
          rw [Real.volume_Ioo, add_sub_cancel_left]
      _ ≤ volume (mk ⁻¹' U i ∩ Ioc (θ i) (θ i + 2 * π)) :=
          measure_mono fun t ht => ⟨⟨t, ht, rfl⟩, ht.1, by linarith [ht.2, (hℓ i hi).2]⟩
  have : ∑ i ∈ s, ENNReal.ofReal (ℓ i) ≤ ENNReal.ofReal (2 * π) :=
    calc _ ≤ ∑ i ∈ s, volume (U i) := Finset.sum_le_sum hmeas
      _ = volume (⋃ i ∈ s, U i) :=
          (measure_biUnion_finset hUd fun i _ => (hUo i).measurableSet).symm
      _ ≤ volume (univ : Set (AddCircle (2 * π))) := measure_mono (subset_univ _)
      _ = _ := AddCircle.measure_univ _
  rw [← ENNReal.ofReal_sum_of_nonneg fun i hi => (hℓ i hi).1] at this
  exact (ENNReal.ofReal_le_ofReal_iff Real.two_pi_pos.le).1 this

/-- `lem:disc-geometry` (d), counting form: if moreover the endpoints of each arc are at chord
distance `≥ ε`, the number `m` of arcs satisfies `m ε ≤ 2π`. -/
theorem card_mul_le_two_pi {ι : Type*} (s : Finset ι) (θ ℓ : ι → ℝ)
    (hℓ : ∀ i ∈ s, 0 ≤ ℓ i ∧ ℓ i ≤ 2 * π)
    (hd : (s : Set ι).PairwiseDisjoint fun i => circleArcOpen (θ i) (ℓ i)) {ε : ℝ}
    (hε : ∀ i ∈ s, ε ≤ ‖expI (θ i + ℓ i) - expI (θ i)‖) : (s.card : ℝ) * ε ≤ 2 * π := by
  have hle : ∀ i ∈ s, ε ≤ ℓ i := fun i hi => by
    have := norm_expI_sub_le (θ i) (θ i + ℓ i)
    rw [add_sub_cancel_left, abs_of_nonneg (hℓ i hi).1] at this
    linarith [hε i hi]
  calc (s.card : ℝ) * ε = ∑ i ∈ s, ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, ℓ i := Finset.sum_le_sum hle
    _ ≤ 2 * π := sum_le_two_pi_of_pairwiseDisjoint s θ ℓ hℓ hd

/-- `lem:disc-geometry` (a): `𝔻 ∩ S(δ, x)` is convex. -/
theorem convex_disc_inter_ball (x : ℂ) (δ : ℝ) : Convex ℝ (disc ∩ ball x δ) :=
  (convex_ball 0 1).inter (convex_ball x δ)

theorem norm_sq_segment_sub {x y : ℂ} (hx : ‖x‖ = 1) (t : ℝ) :
    ‖((1 - t : ℝ) : ℂ) * y - ((1 + t : ℝ) : ℂ) * x‖ ^ 2 =
      ‖y - x‖ ^ 2 + 2 * t * (1 - ‖y‖ ^ 2) + t ^ 2 * ‖y + x‖ ^ 2 := by
  have hx2 : x.re ^ 2 + x.im ^ 2 = 1 := by rw [← norm_sq_eq_re_im, hx, one_pow]
  simp only [norm_sq_eq_re_im, sub_re, sub_im, add_re, add_im, re_ofReal_mul, im_ofReal_mul]
  linear_combination (2 * t) * hx2

/-- `lem:disc-geometry` (b): `𝔻 \ closedBall x δ` is connected and has `-x` in its closure. -/
theorem isConnected_disc_diff_closedBall {x : ℂ} (hx : x ∈ circle) {δ : ℝ} (h0 : 0 < δ)
    (h2 : δ < 2) :
    IsConnected (disc \ closedBall x δ) ∧ -x ∈ closure (disc \ closedBall x δ) := by
  have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
  set S := disc \ closedBall x δ with hS
  set C := disc ∩ ball (-x) (2 - δ) with hC
  have hCS : C ⊆ S := by
    rintro z ⟨hz, hz'⟩
    refine ⟨hz, fun hzb => ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hzb
    rw [mem_ball, dist_eq_norm, sub_neg_eq_add] at hz'
    have h2x : ‖(2 : ℂ) * x‖ ≤ ‖z + x‖ + ‖z - x‖ := by
      calc ‖(2 : ℂ) * x‖ = ‖(z + x) - (z - x)‖ := by ring_nf
        _ ≤ ‖z + x‖ + ‖z - x‖ := norm_sub_le _ _
    rw [norm_mul, hx1, mul_one, RCLike.norm_two] at h2x
    linarith
  -- the half-open segment from `y ∈ S` towards `-x` stays in `S`
  have hseg : ∀ y ∈ S, ∀ t ∈ Ico (0 : ℝ) 1, ((1 - t : ℝ) : ℂ) * y - (t : ℂ) * x ∈ S := by
    rintro y ⟨hy, hyb⟩ t ht
    have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.1 hy
    refine ⟨mem_ball_zero_iff.2 ?_, fun hb => ?_⟩
    · calc ‖((1 - t : ℝ) : ℂ) * y - (t : ℂ) * x‖ ≤ ‖((1 - t : ℝ) : ℂ) * y‖ + ‖(t : ℂ) * x‖ :=
            norm_sub_le _ _
        _ = (1 - t) * ‖y‖ + t := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, hx1, mul_one,
              Real.norm_of_nonneg (by linarith [ht.2]), Real.norm_of_nonneg ht.1]
        _ < 1 := by nlinarith [ht.1, ht.2]
    · rw [mem_closedBall, dist_eq_norm] at hb hyb
      have hyx : δ < ‖y - x‖ := lt_of_not_ge hyb
      have heq : ((1 - t : ℝ) : ℂ) * y - (t : ℂ) * x - x =
          ((1 - t : ℝ) : ℂ) * y - ((1 + t : ℝ) : ℂ) * x := by push_cast; ring
      rw [heq] at hb
      have hsq := norm_sq_segment_sub (y := y) hx1 t
      have : ‖y - x‖ ^ 2 ≤ ‖((1 - t : ℝ) : ℂ) * y - ((1 + t : ℝ) : ℂ) * x‖ ^ 2 := by
        rw [hsq]
        have : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
        nlinarith [ht.1, sq_nonneg t, sq_nonneg ‖y + x‖]
      nlinarith [norm_nonneg (y - x), norm_nonneg (((1 - t : ℝ) : ℂ) * y - ((1 + t : ℝ) : ℂ) * x)]
  -- a point of `C`
  set x₀ : ℂ := -((δ / 2 : ℝ) : ℂ) * x with hx₀
  have hx₀C : x₀ ∈ C := by
    refine ⟨mem_ball_zero_iff.2 ?_, ?_⟩
    · rw [hx₀, norm_mul, norm_neg, Complex.norm_real, hx1, mul_one,
        Real.norm_of_nonneg (by linarith)]
      linarith
    · rw [mem_ball, dist_eq_norm, sub_neg_eq_add,
        show x₀ + x = ((1 - δ / 2 : ℝ) : ℂ) * x by rw [hx₀]; push_cast; ring, norm_mul,
        Complex.norm_real, hx1, mul_one, Real.norm_of_nonneg (by linarith)]
      linarith
  have hconn : IsPreconnected S := by
    refine isPreconnected_of_forall x₀ fun y hy => ?_
    set A := (fun t : ℝ => ((1 - t : ℝ) : ℂ) * y - (t : ℂ) * x) '' Ico 0 1 with hA
    have hAS : A ⊆ S := by rintro _ ⟨t, ht, rfl⟩; exact hseg y hy t ht
    have hAc : IsPreconnected A := isPreconnected_Ico.image _ (by fun_prop)
    set s₀ : ℝ := 1 - (2 - δ) / 4 with hs₀
    have hs₀I : s₀ ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hpC : ((1 - s₀ : ℝ) : ℂ) * y - (s₀ : ℂ) * x ∈ C := by
      refine ⟨(hseg y hy s₀ hs₀I).1, ?_⟩
      rw [mem_ball, dist_eq_norm, sub_neg_eq_add,
        show ((1 - s₀ : ℝ) : ℂ) * y - (s₀ : ℂ) * x + x = ((1 - s₀ : ℝ) : ℂ) * (y + x) by
          push_cast; ring, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have hyx : ‖y + x‖ < 2 := by
        have := norm_add_le y x
        have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.1 hy.1
        linarith
      have : 1 - s₀ = (2 - δ) / 4 := by rw [hs₀]; ring
      rw [this]
      nlinarith
    refine ⟨A ∪ C, union_subset hAS hCS, Or.inr hx₀C, Or.inl ⟨0, ⟨le_rfl, one_pos⟩, by simp⟩,
      hAc.union _ ⟨s₀, hs₀I, rfl⟩ hpC ((convex_disc_inter_ball _ _).isPreconnected)⟩
  refine ⟨⟨⟨x₀, hCS hx₀C⟩, hconn⟩, ?_⟩
  refine closure_mono hCS (Metric.mem_closure_iff.2 fun ε hε => ?_)
  set r := min (ε / 2) ((2 - δ) / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by linarith)
  have hr1 : r ≤ ε / 2 := min_le_left _ _
  have hr2 : r ≤ (2 - δ) / 2 := min_le_right _ _
  refine ⟨-((1 - r : ℝ) : ℂ) * x, ⟨mem_ball_zero_iff.2 ?_, ?_⟩, ?_⟩
  · rw [norm_mul, norm_neg, Complex.norm_real, hx1, mul_one, Real.norm_of_nonneg (by linarith)]
    linarith
  · rw [mem_ball, dist_eq_norm, sub_neg_eq_add,
      show -((1 - r : ℝ) : ℂ) * x + x = (r : ℂ) * x by push_cast; ring, norm_mul,
      Complex.norm_real, hx1, mul_one, Real.norm_of_nonneg hr0.le]
    linarith
  · rw [dist_eq_norm, show -x - -((1 - r : ℝ) : ℂ) * x = -((r : ℂ) * x) by push_cast; ring,
      norm_neg, norm_mul, Complex.norm_real, hx1, mul_one, Real.norm_of_nonneg hr0.le]
    linarith

end DiscGeometry

/-! ### Crosscuts (`fact:crosscut`) -/

section Crosscut

open scoped Real

/-- `fact:crosscut` (Jordan curve theorem; Newman, *Elements*, Theorem 11.8, the θ-curve
theorem). Let `σ` be a crosscut of `𝔻` from `a = e^{iθ}` to `b = e^{i(θ + ℓ)}`, `0 < ℓ < 2π`, and
let `A₁ = circleArc θ ℓ`, `A₂ = circleArc (θ + ℓ) (2π - ℓ)` be the two closed arcs of `C` with
endpoints `a, b`. Then `𝔻 \ σ` has exactly two components `U₁, U₂`, and the frontier of `Uᵢ` is
`σ ∪ Aᵢ`. Imported fact. -/
theorem crosscut_theorem {σ : Set ℂ} {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ < 2 * π)
    (hσ : IsArc σ (expI θ) (expI (θ + ℓ))) (hσD : σ \ {expI θ, expI (θ + ℓ)} ⊆ disc) :
    ∃ z₁ ∈ disc \ σ, ∃ z₂ ∈ disc \ σ,
      Disjoint (connectedComponentIn (disc \ σ) z₁) (connectedComponentIn (disc \ σ) z₂) ∧
      (∀ z ∈ disc \ σ, connectedComponentIn (disc \ σ) z = connectedComponentIn (disc \ σ) z₁ ∨
        connectedComponentIn (disc \ σ) z = connectedComponentIn (disc \ σ) z₂) ∧
      frontier (connectedComponentIn (disc \ σ) z₁) = σ ∪ circleArc θ ℓ ∧
      frontier (connectedComponentIn (disc \ σ) z₂) = σ ∪ circleArc (θ + ℓ) (2 * π - ℓ) :=
  JordanCrosscut.crosscut_theorem' hℓ hℓ' hσ hσD

/-- The consequences of `fact:crosscut` for the closures of the two components:
`closure U ∩ C = A` and `σ ⊆ closure U`, when `frontier U = σ ∪ A` for a component `U` of
`𝔻 \ σ`. -/
theorem closure_inter_circle_of_frontier {σ U : Set ℂ} {θ ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hσD : σ \ {expI θ, expI (θ + ℓ)} ⊆ disc) (hU : U ⊆ disc)
    (hfr : frontier U = σ ∪ circleArc θ ℓ) :
    closure U ∩ circle = circleArc θ ℓ ∧ σ ⊆ closure U := by
  have hcl : closure U = interior U ∪ frontier U := by
    rw [frontier, union_sdiff_cancel interior_subset_closure]
  have hdc : Disjoint disc circle := disjoint_left.2 fun z h1 h2 => by
    have h1' : ‖z‖ < 1 := mem_ball_zero_iff.1 h1
    have h2' : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 h2
    linarith
  refine ⟨?_, fun z hz => hcl ▸ Or.inr (hfr ▸ Or.inl hz)⟩
  ext z
  constructor
  · rintro ⟨hz, hzC⟩
    rw [hcl] at hz
    rcases hz with hz | hz
    · exact absurd hzC (disjoint_left.1 hdc (hU (interior_subset hz)))
    · rw [hfr] at hz
      rcases hz with hz | hz
      · by_cases hab : z = expI θ ∨ z = expI (θ + ℓ)
        · rcases hab with rfl | rfl
          · exact left_mem_circleArc hℓ
          · exact right_mem_circleArc hℓ
        · push Not at hab
          exact absurd hzC (disjoint_left.1 hdc (hσD ⟨hz, by simp [hab.1, hab.2]⟩))
      · exact hz
  · intro hz
    exact ⟨hcl ▸ Or.inr (hfr ▸ Or.inr hz), circleArc_subset_circle θ ℓ hz⟩

/-- The endpoints of a crosscut of `𝔻` can be written `e^{iθ}`, `e^{i(θ + ℓ)}` with
`0 < ℓ < 2π`. -/
theorem IsCrosscut.exists_angles {σ : Set ℂ} (h : IsCrosscut disc circle σ) :
    ∃ θ ℓ : ℝ, 0 < ℓ ∧ ℓ < 2 * π ∧ IsArc σ (expI θ) (expI (θ + ℓ)) ∧
      σ \ {expI θ, expI (θ + ℓ)} ⊆ disc := by
  obtain ⟨a, b, hab, ha, hb, harc, hσ⟩ := h
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
  refine ⟨Complex.arg a, d, hd0, hdI.2, by rw [h1, he]; exact harc, by rw [h1, he]; exact hσ⟩

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

end Crosscut

end TJK
