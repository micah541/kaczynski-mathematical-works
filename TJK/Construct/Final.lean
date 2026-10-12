import Mathlib
import TJK.Defs
import TJK.Plane.Basic
import TJK.Baire.Basic
import TJK.Baire.Approx
import TJK.Baire.Sphere
import TJK.Construct.G
import TJK.Construct.H
import TJK.Construct.D

/-!
# Realization theorems (blueprint `thm:construct-E`, `thm:construct-F`, `thm:construct-H`)

* `exists_f_disc` (Trans. AMS 141, (E)): for an `F_σδ` set `A ⊆ C` and a bounded `φ : A → ℂ` of
  honorary Baire class `≤ 2`, a bounded continuous `f` on `𝔻` with `CC(f) = A` and boundary
  function `φ`. The function of `thm:construct-D` is carried to `G°` by `Ψ_𝔻`, extended from
  `G'' ∪ [0, 1)` by Tietze, after a rotation putting a point of `A` at `1`.
* `exists_f_sphere'` (Trans. AMS 141, (F); McMillan's problem): the same with values in the
  sphere, via the fold map.
* `exists_f_upperHalfPlane`, `exists_f_upperHalfPlane_sphere`, `exists_boundaryFn_euclidean'`
  (dissertation Theorem 6) and `exists_boundaryFn_sphere` (dissertation Theorem 7).
-/

namespace TJK

open _root_.Set Filter Topology Metric
open scoped Real

/-- `fact:tietze-ext`: a bounded continuous complex function on a closed subset of a normal space
extends to a continuous function on the whole space with the same bound. -/
theorem tietze_bounded_complex {X : Type*} [TopologicalSpace X] [NormalSpace X] {s : Set X}
    (hs : IsClosed s) {f : X → ℂ} (hf : ContinuousOn f s) {B : ℝ} (hB : 0 < B)
    (hfB : ∀ x ∈ s, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, Continuous g ∧ (∀ x, ‖g x‖ ≤ B) ∧ EqOn g f s := by
  have := Metric.instTietzeExtensionClosedBall.{u_1} ℂ (0 : ℂ) hB
  obtain ⟨g, hg, hgf⟩ := ContinuousMap.exists_forall_mem_restrict_eq hs
    ⟨s.domRestrict f, hf.domRestrict⟩ (t := closedBall (0 : ℂ) B)
    (fun x => mem_closedBall_zero_iff.2 (hfB x x.2))
  refine ⟨g, g.continuous, fun x => mem_closedBall_zero_iff.1 (hg x), fun x hx => ?_⟩
  exact DFunLike.congr_fun hgf ⟨x, hx⟩

/-- `lem:transfer`, in the form used for limits: `f ∘ Ψ` has the limit `l` along an arc at `p`
iff `f` has it along an arc at `Ψ p`. -/
theorem transfer_exists_tendsto {E : Type*} [TopologicalSpace E] [T2Space E] {E' : Type*}
    [TopologicalSpace E'] [T2Space E'] {e : PartialHomeomorph E E'} {Ω B : Set E}
    {Ω' B' : Set E'} (h : IsChart e Ω B Ω' B') {p : E} (hp : p ∈ e.source) {Y : Type*}
    (f : E' → Y) (l : Filter Y) :
    (∃ γ, IsArcAt Ω p γ ∧ Tendsto (f ∘ e) (𝓝[γ \ {p}] p) l) ↔
      ∃ γ', IsArcAt Ω' (e p) γ' ∧ Tendsto f (𝓝[γ' \ {e p}] (e p)) l := by
  constructor
  · rintro ⟨γ, hγ, hl⟩
    exact ⟨e '' γ, (transfer_isArcAt h hp (h.arc_subset_source hp hγ)).1 hγ,
      (transfer_tendsto h hp hγ f l).1 hl⟩
  · rintro ⟨γ', hγ', hl⟩
    have hγ't : γ' ⊆ e.target := h.symm.arc_subset_source (e.map_source hp) hγ'
    have hγ : e.symm '' γ' ⊆ e.source := fun _ ⟨z, hz, hze⟩ => hze ▸ e.map_target (hγ't hz)
    have himg : e '' (e.symm '' γ') = γ' :=
      e.toPartialEquiv.image_symm_image_of_subset_target hγ't
    have harc : IsArcAt Ω p (e.symm '' γ') := by
      rw [transfer_isArcAt h hp hγ, himg]; exact hγ'
    exact ⟨_, harc, by rw [transfer_tendsto h hp harc, himg]; exact hl⟩

theorem mem_curvConvSet_iff {E : Type*} [TopologicalSpace E] {Y : Type*} [TopologicalSpace Y]
    {Ω B : Set E} {f : E → Y} {x : E} :
    x ∈ curvConvSet Ω B f ↔ x ∈ B ∧ ∃ q, ∃ γ, IsArcAt Ω x γ ∧ Tendsto f (𝓝[γ \ {x}] x) (𝓝 q) :=
  ⟨fun ⟨hx, γ, hγ, q, hq⟩ => ⟨hx, q, γ, hγ, hq⟩, fun ⟨hx, q, γ, hγ, hq⟩ => ⟨hx, γ, hγ, q, hq⟩⟩

theorem IsBoundaryFunction.mono {E : Type*} [TopologicalSpace E] {Y : Type*}
    [TopologicalSpace Y] {Ω S S' : Set E} {f φ φ' : E → Y} (h : IsBoundaryFunction Ω f S φ)
    (hS : S' ⊆ S) (hφ : EqOn φ' φ S') : IsBoundaryFunction Ω f S' φ' := fun x hx => by
  rw [hφ hx]; exact h x (hS hx)

/-! ### Cluster sets under finite-to-one maps (`lem:cluster`) -/

/-- If `f` is continuous and bounded on `Ω` and `Θ` is continuous with finite fibres, then a limit
of `Θ ∘ f` along an arc forces a limit of `f` along it: the cluster set of `f` is connected and
mapped into a single fibre of `Θ`, hence a single point. -/
theorem exists_tendsto_of_tendsto_comp {Ω : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f Ω) {R : ℝ}
    (hR : ∀ z ∈ Ω, ‖f z‖ ≤ R) {Y : Type*} [TopologicalSpace Y] [T2Space Y] {Θ : ℂ → Y}
    (hΘ : Continuous Θ) (hfin : ∀ q, (Θ ⁻¹' {q}).Finite) {x : ℂ} {γ : Set ℂ}
    (hγ : IsArcAt Ω x γ) {q : Y} (hq : Tendsto (Θ ∘ f) (𝓝[γ \ {x}] x) (𝓝 q)) :
    ∃ w, Tendsto f (𝓝[γ \ {x}] x) (𝓝 w) := by
  classical
  set K := closedBall (0 : ℂ) (max R 0) with hK
  have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  let f₂ : ℂ → K := fun z => ⟨if z ∈ Ω then f z else 0, by
    by_cases hz : z ∈ Ω
    · rw [if_pos hz, mem_closedBall_zero_iff]; exact (hR z hz).trans (le_max_left _ _)
    · rw [if_neg hz, mem_closedBall_zero_iff, norm_zero]; exact le_max_right _ _⟩
  have hf₂v : ∀ z ∈ Ω, (f₂ z : ℂ) = f z := fun z hz => by simp [f₂, hz]
  have hf₂ : ContinuousOn f₂ Ω :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff).2 (hf.congr fun z hz => hf₂v z hz)
  have hΘ' : Continuous (Θ ∘ Subtype.val : K → Y) := hΘ.comp continuous_subtype_val
  have hγΩ : ∀ᶠ z in 𝓝[γ \ {x}] x, z ∈ Ω := by
    obtain ⟨b, -, hsub⟩ := hγ
    exact eventually_nhdsWithin_of_forall fun z hz => hsub hz
  have hq' : Tendsto ((Θ ∘ Subtype.val) ∘ f₂) (𝓝[γ \ {x}] x) (𝓝 q) :=
    hq.congr' (hγΩ.mono fun z hz => by simp [hf₂v z hz])
  have hsub : clusterSet ((Θ ∘ Subtype.val) ∘ f₂) γ x ⊆ {q} := fun y hy =>
    eq_of_nhds_neBot (ClusterPt.mono hy hq')
  rw [clusterSet_comp hΘ' f₂] at hsub
  have hfinC : (clusterSet f₂ γ x).Finite := by
    refine ((hfin q).preimage Subtype.val_injective.injOn).subset fun y hy => ?_
    exact hsub ⟨y, hy, rfl⟩
  have hconn := isConnected_clusterSet hγ hf₂
  have hss : (clusterSet f₂ γ x).Subsingleton := by
    by_contra hns
    exact hconn.2.infinite_of_nontrivial (not_subsingleton_iff.1 hns) hfinC
  obtain ⟨w, hw⟩ := hconn.1
  have hlim := (tendsto_iff_clusterSet_eq_singleton hγ f₂ w).2 (hss.eq_singleton_of_mem hw)
  exact ⟨w, ((continuous_subtype_val.tendsto w).comp hlim).congr'
    (hγΩ.mono fun z hz => hf₂v z hz)⟩

/-- `CC(Θ ∘ f) = CC(f)` for `f` continuous and bounded on `Ω` and `Θ` continuous with finite
fibres. -/
theorem curvConvSet_comp_eq {Ω B : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f Ω) {R : ℝ}
    (hR : ∀ z ∈ Ω, ‖f z‖ ≤ R) {Y : Type*} [TopologicalSpace Y] [T2Space Y] {Θ : ℂ → Y}
    (hΘ : Continuous Θ) (hfin : ∀ q, (Θ ⁻¹' {q}).Finite) :
    curvConvSet Ω B (Θ ∘ f) = curvConvSet Ω B f := by
  ext x
  constructor
  · rintro ⟨hx, γ, hγ, q, hq⟩
    exact ⟨hx, γ, hγ, exists_tendsto_of_tendsto_comp hf hR hΘ hfin hγ hq⟩
  · rintro ⟨hx, γ, hγ, w, hw⟩
    exact ⟨hx, γ, hγ, Θ w, (hΘ.tendsto w).comp hw⟩

end TJK

namespace TJK.Construct

open _root_.Set Filter Topology Metric
open scoped Real

/-! ### The disc: rotations and the empty case -/

section DiscAux

open Complex

theorem image_mul_eq_of_norm {a : ℂ} (ha : ‖a‖ = 1) {s : Set ℂ}
    (hs : ∀ z w : ℂ, ‖z‖ = ‖w‖ → z ∈ s → w ∈ s) : (fun z => a * z) '' s = s := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hs z _ (by rw [norm_mul, ha, one_mul]) hz
  · intro hw
    refine ⟨a⁻¹ * w, hs w _ (by rw [norm_mul, norm_inv, ha, inv_one, one_mul]) hw, ?_⟩
    field_simp

/-- The rotation `z ↦ a z` (`‖a‖ = 1`) as a chart of `𝔻 ∪ C` onto itself. -/
noncomputable def rotPH (a : ℂ) (ha : ‖a‖ = 1) : PartialHomeomorph ℂ ℂ :=
  (Homeomorph.mulLeft₀ a (by rintro rfl; simp at ha)).toPartialHomeomorphOfImageEq
    (closedBall 0 1) (closedBall 0 1)
    (image_mul_eq_of_norm ha fun z w h hz => by
      rw [mem_closedBall_zero_iff] at hz ⊢; rwa [← h])

theorem rotPH_apply (a : ℂ) (ha : ‖a‖ = 1) (z : ℂ) : rotPH a ha z = a * z := rfl

theorem rot_isChart (a : ℂ) (ha : ‖a‖ = 1) : IsChart (rotPH a ha) disc circle disc circle where
  source_eq := ball_union_sphere.symm
  target_eq := ball_union_sphere.symm
  image_eq := image_mul_eq_of_norm ha fun z w h hz => by
    rw [mem_ball_zero_iff] at hz ⊢; rwa [← h]
  disjoint := disjoint_left.2 fun z h1 h2 => by
    rw [mem_ball_zero_iff] at h1; rw [mem_sphere_zero_iff_norm] at h2; linarith
  disjoint' := disjoint_left.2 fun z h1 h2 => by
    rw [mem_ball_zero_iff] at h1; rw [mem_sphere_zero_iff_norm] at h2; linarith

/-- The function `sin (1 / (1 - |z|))` of the empty case of `thm:construct-E`. -/
noncomputable def sinRad (z : ℂ) : ℂ := ((Real.sin (1 / (1 - ‖z‖)) : ℝ) : ℂ)

theorem continuousOn_sinRad : ContinuousOn sinRad disc := by
  have : ContinuousOn (fun z : ℂ => 1 / (1 - ‖z‖)) disc :=
    continuousOn_const.div (by fun_prop) fun z hz => by
      rw [mem_ball_zero_iff] at hz; linarith
  exact continuous_ofReal.comp_continuousOn (Real.continuous_sin.comp_continuousOn this)

theorem norm_sinRad_le (z : ℂ) : ‖sinRad z‖ ≤ 1 := by
  rw [sinRad, norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _

/-- `sin (1 / (1 - |z|))` has no limit along any arc at a point of `C`. -/
theorem curvConvSet_sinRad : curvConvSet disc circle sinRad = ∅ := by
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro x ⟨hx, γ, hγ, q, hq⟩
  have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
  obtain ⟨U, hUo, hxU, hUS⟩ := mem_nhdsWithin.1 (Metric.tendsto_nhds.1 hq (1 / 2) (by norm_num))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo x hxU
  obtain ⟨C, hCγ, hC, hCb, hxC⟩ := hγ.exists_tail hr
  have hCd : ∀ z ∈ C, ‖z‖ < 1 := fun z hz => by
    obtain ⟨b, -, hsub⟩ := hγ
    exact mem_ball_zero_iff.1 (hsub (hCγ hz))
  have hCS : ∀ z ∈ C, dist (sinRad z) q < 1 / 2 := fun z hz =>
    hUS ⟨hball (hCb hz), hCγ hz⟩
  have hT : IsPreconnected ((fun z : ℂ => 1 / (1 - ‖z‖)) '' C) :=
    hC.image _ (continuousOn_const.div (by fun_prop) fun z hz => by linarith [hCd z hz])
  obtain ⟨z₀, hz₀⟩ : C.Nonempty := closure_nonempty_iff.1 ⟨_, hxC⟩
  have hunb : ∀ M : ℝ, ∃ z ∈ C, M < 1 / (1 - ‖z‖) := fun M => by
    obtain ⟨z, hz, hdz⟩ := Metric.mem_closure_iff.1 hxC (1 / (|M| + 1)) (by positivity)
    refine ⟨z, hz, ?_⟩
    have h1 : 0 < 1 - ‖z‖ := by linarith [hCd z hz]
    have h2 : 1 - ‖z‖ < 1 / (|M| + 1) := by
      have := norm_sub_norm_le x z
      rw [← dist_eq_norm, hx1] at this
      linarith
    calc M < |M| + 1 := by linarith [le_abs_self M]
      _ = 1 / (1 / (|M| + 1)) := by rw [one_div_one_div]
      _ < 1 / (1 - ‖z‖) := one_div_lt_one_div_of_lt h1 h2
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - ‖z₀‖) / (2 * π))
  have hn' : 1 / (1 - ‖z₀‖) ≤ π / 2 + 2 * π * n := by
    have := (div_lt_iff₀ (by positivity : 0 < 2 * π)).1 hn
    linarith
  obtain ⟨z₁, hz₁, hz₁v⟩ := hunb (π / 2 + 2 * π * n + π)
  have hI := hT.Icc_subset ⟨z₀, hz₀, rfl⟩ ⟨z₁, hz₁, rfl⟩
  obtain ⟨w₁, hw₁, hw₁v⟩ := hI ⟨hn', by linarith⟩
  obtain ⟨w₂, hw₂, hw₂v⟩ := hI ⟨by linarith, hz₁v.le⟩
  have hs1 : sinRad w₁ = 1 := by
    simp only at hw₁v
    rw [sinRad, hw₁v, show π / 2 + 2 * π * n = π / 2 + n * (2 * π) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two, ofReal_one]
  have hs2 : sinRad w₂ = -1 := by
    simp only at hw₂v
    rw [sinRad, hw₂v, show π / 2 + 2 * π * n + π = (π / 2 + π) + n * (2 * π) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_two, ofReal_neg, ofReal_one]
  have h1 := hCS w₁ hw₁
  have h2 := hCS w₂ hw₂
  rw [hs1] at h1
  rw [hs2] at h2
  have : dist (1 : ℂ) (-1) < 1 := by
    calc dist (1 : ℂ) (-1) ≤ dist (1 : ℂ) q + dist q (-1) := dist_triangle _ _ _
      _ < 1 / 2 + 1 / 2 := by rw [dist_comm q]; exact add_lt_add h1 h2
      _ = 1 := by norm_num
  rw [dist_eq_norm, sub_neg_eq_add, one_add_one_eq_two] at this
  norm_num at this

end DiscAux

/-! ### `thm:construct-E` -/

section DiscMain

open Complex

theorem Qo_eq : {z : ℂ | |z.re| < 1 ∧ 0 < z.im ∧ z.im < 1} = openSquare := by
  ext z
  simp only [openSquare, mem_ofPred_eq, mem_Ioo, abs_lt]

theorem baseX_eq : ((↑) : ℝ → ℂ) '' Ioo (-1) 1 = baseX := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨by simpa using hx, by simp⟩
  · rintro ⟨h1, h2⟩; exact ⟨z.re, h1, Complex.ext (by simp) (by simp [h2])⟩

theorem ofReal_mem_squareSource {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : (u : ℂ) ∈ squareSource :=
  ⟨by simpa using hu, by simp⟩

theorem openSquare_subset_Qc :
    openSquare ⊆ {z : ℂ | |z.re| ≤ 1 ∧ 0 < z.im ∧ z.im ≤ 1} := fun _ hz =>
  ⟨(abs_lt.2 hz.1).le, hz.2.1, hz.2.2.le⟩

/-- `thm:construct-E` when `1 ∈ A`. -/
theorem exists_f_disc_of_one_mem {A : Set ℂ} (hA : A ⊆ circle) (hAF : IsFσδ A)
    (h1A : (1 : ℂ) ∈ A) {φ : ℂ → ℂ} (hφb : ∃ B, ∀ x ∈ A, ‖φ x‖ ≤ B)
    (hφ : IsHonoraryBaireTwo (A.restrict φ)) :
    ∃ f : ℂ → ℂ, ContinuousOn f disc ∧ Bornology.IsBounded (f '' disc) ∧
      curvConvSet disc circle f = A ∧ IsBoundaryFunction disc f A φ := by
  classical
  -- the data on `X`
  set A' : Set ℝ := {u | u ∈ Ioo (-1) 1 ∧ chartD u ∈ A} with hA'def
  let T : Ioo (-1 : ℝ) 1 → ℂ := fun u => chartD u
  have hT : Continuous T := chartDPH.continuousOn.comp_continuous
    (continuous_ofReal.comp continuous_subtype_val) fun u => ofReal_mem_squareSource u.2
  have hA'F : IsFσδ A' := by
    have h1 : IsFσδ (T ⁻¹' A) := hAF.preimage hT
    have h2 : IsFσδ (Ioo (-1 : ℝ) 1) := (IsOpen.isFσ isOpen_Ioo).isFσδ
    convert h2.of_subtype h1 using 1
    ext u
    constructor
    · rintro ⟨hu, huA⟩; exact ⟨⟨u, hu⟩, huA, rfl⟩
    · rintro ⟨⟨u, hu⟩, huA, rfl⟩; exact ⟨hu, huA⟩
  let φ' : ℝ → ℂ := fun u => φ (chartD u)
  have hφ' : IsHonoraryBaireTwo (A'.restrict φ') := by
    let j : A' → A := fun u => ⟨chartD u, u.2.2⟩
    have hj : Continuous j :=
      (hT.comp (continuous_subtype_val.subtype_mk fun u : A' => u.2.1)).subtype_mk _
    have hjinj : Function.Injective j := fun u v huv => by
      have h := chartDPH.injOn (ofReal_mem_squareSource u.2.1) (ofReal_mem_squareSource v.2.1)
        (congrArg Subtype.val huv)
      exact Subtype.ext (ofReal_injective h)
    exact hφ.comp_continuous_injective hj hjinj
  obtain ⟨B, hB⟩ := hφb
  obtain ⟨f₁, hf₁c, hf₁b, hf₁CC, hf₁BF⟩ :=
    Construct.exists_f_Q hA'F (fun u hu => hu.1) ⟨B, fun u hu => hB _ hu.2⟩ hφ'
  rw [Qo_eq, baseX_eq] at hf₁CC
  rw [Qo_eq] at hf₁BF
  obtain ⟨C₁, hC₁⟩ := hf₁b.exists_norm_le
  have hmaps : MapsTo chartDInv gOpen openSquare := chartD_isChart.symm.mapsTo
  have hf₀c : ContinuousOn (fun z => f₁ (chartDInv z)) gOpen :=
    hf₁c.comp (chartDPH.continuousOn_symm.mono chartD_isChart.symm.subset_source)
      (hmaps.mono_right openSquare_subset_Qc)
  -- the closed set `G'' ∪ [0, 1)` of `𝔻` and the function on it
  set R : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re} with hRdef
  have hRg : ∀ z ∈ disc, z ∈ R → z ∉ gClosed := fun z hzd hzR => by
    have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzR.1])
    have hre : z.re < 1 :=
      calc z.re ≤ |z.re| := le_abs_self _
        _ ≤ ‖z‖ := abs_re_le_norm z
        _ < 1 := mem_ball_zero_iff.1 hzd
    rw [hz]; exact ofReal_not_mem_gClosed hzR.2 hre
  let F : ℂ → ℂ := fun z => if z ∈ gClosed then f₁ (chartDInv z) else φ 1
  set S : Set disc := Subtype.val ⁻¹' gClosed ∪ Subtype.val ⁻¹' R with hSdef
  have hRc : IsClosed (Subtype.val ⁻¹' R : Set disc) :=
    ((isClosed_eq continuous_im continuous_const).inter
      (isClosed_le continuous_const continuous_re)).preimage continuous_subtype_val
  have hSc : IsClosed S := isClosed_gClosed.union hRc
  have hFc : ContinuousOn (F ∘ Subtype.val) S := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_gClosed hRc
    · refine (hf₀c.comp continuous_subtype_val.continuousOn
        fun z hz => gClosed_subset_gOpen hz).congr fun z hz => ?_
      have hz' : (z : ℂ) ∈ gClosed := hz
      simp only [Function.comp, F, if_pos hz']
    · refine (continuousOn_const (c := φ 1)).congr fun z hz => ?_
      simp only [Function.comp, F, if_neg (hRg z z.2 hz)]
  set C₂ := max C₁ ‖φ 1‖ + 1 with hC₂
  have hC₂pos : 0 < C₂ := by
    have h0 := le_max_right C₁ ‖φ 1‖
    have h1 := norm_nonneg (φ 1)
    linarith
  have hFb : ∀ z ∈ S, ‖(F ∘ Subtype.val) z‖ ≤ C₂ := by
    intro z hz
    by_cases hg : (z : ℂ) ∈ gClosed
    · simp only [Function.comp, F, if_pos hg]
      exact (hC₁ _ ⟨_, openSquare_subset_Qc (hmaps (gClosed_subset_gOpen hg)), rfl⟩).trans
        (by linarith [le_max_left C₁ ‖φ 1‖])
    · simp only [Function.comp, F, if_neg hg]; linarith [le_max_right C₁ ‖φ 1‖]
  obtain ⟨g, hgc, hgb, hgF⟩ := tietze_bounded_complex hSc hFc hC₂pos hFb
  let f : ℂ → ℂ := fun z => if h : z ∈ disc then g ⟨z, h⟩ else 0
  have hfg : ∀ z (hz : z ∈ disc), f z = g ⟨z, hz⟩ := fun z hz => dif_pos hz
  have hfc : ContinuousOn f disc := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hgc using 1
    funext z
    exact hfg z z.2
  have hfG : ∀ z ∈ disc, z ∈ gClosed → f z = f₁ (chartDInv z) := fun z hzd hz => by
    rw [hfg z hzd, @hgF ⟨z, hzd⟩ (Or.inl hz)]
    simp only [Function.comp, F, if_pos hz]
  have hfR : ∀ z ∈ disc, z ∈ R → f z = φ 1 := fun z hzd hz => by
    rw [hfg z hzd, @hgF ⟨z, hzd⟩ (Or.inr hz)]
    simp only [Function.comp, F, if_neg (hRg z hzd hz)]
  -- locality and transfer at the points of `C \ {1}`
  have hloc : ∀ x ∈ circle, x ≠ 1 → ∀ l : Filter ℂ,
      (∃ γ, IsArcAt disc x γ ∧ Tendsto f (𝓝[γ \ {x}] x) l) ↔
        ∃ γ, IsArcAt openSquare (chartDInv x) γ ∧
          Tendsto f₁ (𝓝[γ \ {chartDInv x}] (chartDInv x)) l := by
    intro x hx hx1 l
    obtain ⟨r, hr, hsub⟩ := exists_ball_inter_disc_subset_gClosed hx hx1
    have hW : ball x r ∩ disc = ball x r ∩ gOpen := by
      ext z
      exact ⟨fun hz => ⟨hz.1, gClosed_subset_gOpen (hsub hz)⟩, fun hz => ⟨hz.1, hz.2.1⟩⟩
    rw [curvConv_local (ball_mem_nhds x hr) hW (f' := f₁ ∘ chartDPH.symm)
      (fun z hz => hfG z hz.2 (hsub hz)) l]
    exact transfer_exists_tendsto chartD_isChart.symm (p := x) (Or.inr ⟨hx, hx1⟩) f₁ l
  have hinv : ∀ x ∈ circle, x ≠ 1 → ((chartDInv x).re : ℂ) = chartDInv x ∧
      (chartDInv x).re ∈ Ioo (-1 : ℝ) 1 ∧ chartD (chartDInv x).re = x := by
    intro x hx hx1
    have ht : x ∈ chartDPH.target := Or.inr ⟨hx, hx1⟩
    have hB : chartDInv x ∈ baseX := (chartD_isChart.symm.mem_boundary_iff ht).2 ⟨hx, hx1⟩
    have hre : ((chartDInv x).re : ℂ) = chartDInv x :=
      Complex.ext (ofReal_re _) (by rw [ofReal_im]; exact hB.2.symm)
    refine ⟨hre, hB.1, ?_⟩
    rw [hre]
    exact chartDPH.right_inv ht
  have hbd : ∀ x ∈ circle, x ≠ 1 → (x ∈ A ↔ chartDInv x ∈ ((↑) : ℝ → ℂ) '' A') := by
    intro x hx hx1
    obtain ⟨he, hI, hx'⟩ := hinv x hx hx1
    constructor
    · intro hxA; exact ⟨_, ⟨hI, by rw [hx']; exact hxA⟩, he⟩
    · rintro ⟨u, ⟨-, huA⟩, hu⟩
      have : u = (chartDInv x).re := by rw [← hu, ofReal_re]
      rw [this, hx'] at huA
      exact huA
  have hbX : ∀ x ∈ circle, x ≠ 1 → chartDInv x ∈ baseX := fun x hx hx1 => by
    obtain ⟨he, hI, -⟩ := hinv x hx hx1
    rw [← baseX_eq]; exact ⟨_, hI, he⟩
  -- the radius `[0, 1)`
  have hrad : ∃ γ, IsArcAt disc 1 γ ∧ Tendsto f (𝓝[γ \ {1}] 1) (𝓝 (φ 1)) := by
    let P : Path (1 : ℂ) 0 :=
      ⟨⟨fun t => ((1 - (t : ℝ) : ℝ) : ℂ), by fun_prop⟩, by simp, by simp⟩
    have hP : ∀ t : unitInterval, P t = ((1 - (t : ℝ) : ℝ) : ℂ) := fun t => rfl
    have hPinj : Function.Injective P := fun s t hst => by
      rw [hP, hP] at hst
      have := ofReal_injective hst
      exact Subtype.ext (by linarith)
    have hsub : range P \ {1} ⊆ disc ∩ R := by
      rintro _ ⟨⟨t, rfl⟩, ht⟩
      have ht0 : (0 : ℝ) < t := by
        refine lt_of_le_of_ne t.2.1 fun h0 => ht ?_
        have : t = 0 := Subtype.ext h0.symm
        rw [this, mem_singleton_iff, P.source]
      have ht1 := t.2.2
      rw [hP]
      refine ⟨?_, by simp, by simp; linarith⟩
      rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    refine ⟨range P, ⟨0, ⟨P, hPinj, rfl⟩, fun z hz => (hsub hz).1⟩,
      tendsto_const_nhds.congr' ?_⟩
    exact eventually_nhdsWithin_of_forall fun z hz => (hfR z (hsub hz).1 (hsub hz).2).symm
  refine ⟨f, hfc, ?_, ?_, ?_⟩
  · refine (isBounded_closedBall (x := (0 : ℂ)) (r := C₂)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_closedBall_zero_iff, hfg z hz]
    exact hgb _
  · ext x
    rw [mem_curvConvSet_iff]
    by_cases hx1 : x = 1
    · subst hx1
      obtain ⟨γ, hγ, hl⟩ := hrad
      exact ⟨fun _ => h1A, fun _ => ⟨hA h1A, _, γ, hγ, hl⟩⟩
    constructor
    · rintro ⟨hx, q, hq⟩
      rw [hloc x hx hx1] at hq
      have hmem : chartDInv x ∈ curvConvSet openSquare baseX f₁ := by
        rw [mem_curvConvSet_iff]; exact ⟨hbX x hx hx1, q, hq⟩
      rw [hf₁CC] at hmem
      exact (hbd x hx hx1).2 hmem
    · intro hxA
      have hx := hA hxA
      have hmem : chartDInv x ∈ curvConvSet openSquare baseX f₁ := by
        rw [hf₁CC]; exact (hbd x hx hx1).1 hxA
      rw [mem_curvConvSet_iff] at hmem
      obtain ⟨-, q, hq⟩ := hmem
      exact ⟨hx, q, (hloc x hx hx1 _).2 hq⟩
  · intro x hxA
    by_cases hx1 : x = 1
    · subst hx1; exact hrad
    have hx := hA hxA
    obtain ⟨-, -, hx'⟩ := hinv x hx hx1
    obtain ⟨γ, hγ, hl⟩ := hf₁BF _ ((hbd x hx hx1).1 hxA)
    simp only [hx'] at hl
    exact (hloc x hx hx1 _).2 ⟨γ, hγ, hl⟩

end DiscMain

/-- `thm:construct-E` (Trans. AMS 141, (E)): for an `F_σδ` set `A ⊆ C` and a bounded
`φ : A → ℂ` of honorary Baire class `≤ 2` there is a bounded continuous `f` on `𝔻` with
`CC(f) = A` having `φ` as a boundary function. -/
theorem exists_f_disc (A : Set ℂ) (hA : A ⊆ circle) (hAF : IsFσδ A) (φ : ℂ → ℂ)
    (hφb : ∃ B, ∀ x ∈ A, ‖φ x‖ ≤ B) (hφ : IsHonoraryBaireTwo (A.restrict φ)) :
    ∃ f : ℂ → ℂ, ContinuousOn f disc ∧ Bornology.IsBounded (f '' disc) ∧
      curvConvSet disc circle f = A ∧ IsBoundaryFunction disc f A φ := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, haA⟩
  · refine ⟨sinRad, continuousOn_sinRad, ?_, curvConvSet_sinRad, fun x hx => hx.elim⟩
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨z, -, rfl⟩
    exact mem_closedBall_zero_iff.2 (norm_sinRad_le z)
  have ha : ‖a‖ = 1 := mem_sphere_zero_iff_norm.1 (hA haA)
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
  have hnorm : ∀ z : ℂ, ‖a * z‖ = ‖z‖ := fun z => by rw [norm_mul, ha, one_mul]
  set A₁ : Set ℂ := (fun z => a * z) ⁻¹' A with hA₁def
  have hA₁ : A₁ ⊆ circle := fun z hz => by
    have := hA hz
    rw [mem_sphere_zero_iff_norm] at this ⊢
    rwa [hnorm] at this
  have hA₁F : IsFσδ A₁ := hAF.preimage (continuous_mul_left a)
  have h1 : (1 : ℂ) ∈ A₁ := by show a * 1 ∈ A; rwa [mul_one]
  have hφ₁ : IsHonoraryBaireTwo (A₁.restrict fun z => φ (a * z)) := by
    let j : A₁ → A := fun z => ⟨a * z, z.2⟩
    have hj : Continuous j := ((continuous_mul_left a).comp continuous_subtype_val).subtype_mk _
    have hjinj : Function.Injective j := fun u v huv =>
      Subtype.ext (mul_left_cancel₀ ha0 (congrArg Subtype.val huv))
    exact hφ.comp_continuous_injective hj hjinj
  obtain ⟨B, hB⟩ := hφb
  obtain ⟨f₁, hf₁c, hf₁b, hf₁CC, hf₁BF⟩ :=
    exists_f_disc_of_one_mem hA₁ hA₁F h1 ⟨B, fun z hz => hB _ hz⟩ hφ₁
  have hch := rot_isChart a⁻¹ hb
  have hmaps : MapsTo (fun z => a⁻¹ * z) disc disc := hch.mapsTo
  refine ⟨f₁ ∘ rotPH a⁻¹ hb, hf₁c.comp (continuous_mul_left _).continuousOn hmaps, ?_, ?_, ?_⟩
  · exact hf₁b.subset (by rintro _ ⟨z, hz, rfl⟩; exact ⟨_, hmaps hz, rfl⟩)
  · rw [transfer_curvConvSet hch, hf₁CC]
    ext z
    simp only [mem_inter_iff, mem_preimage, rotPH_apply, hA₁def, mul_inv_cancel_left₀ ha0]
    exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
  · refine ((transfer_isBoundaryFunction hch f₁ hA₁ _).1 hf₁BF).mono ?_ ?_
    · intro z hz
      refine ⟨?_, ?_⟩
      · show z ∈ closedBall 0 1
        exact sphere_subset_closedBall (hA hz)
      · show a * (a⁻¹ * z) ∈ A
        rwa [mul_inv_cancel_left₀ ha0]
    · intro z _
      simp only [Function.comp, rotPH_apply, mul_inv_cancel_left₀ ha0]

/-! ### The sphere (`thm:construct-F`) -/

section Sphere

open Complex

/-- `ℂ → ℝ²`. -/
def toR2 (w : ℂ) : Fin 2 → ℝ := fun i => if i = 0 then w.re else w.im

/-- `ℝ² → ℂ`. -/
noncomputable def toC (v : Fin 2 → ℝ) : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * I

theorem continuous_toR2 : Continuous toR2 := continuous_pi fun i => by
  by_cases hi : i = 0
  · simp only [toR2, hi, if_true]; fun_prop
  · simp only [toR2, hi, if_false]; fun_prop

theorem continuous_toC : Continuous toC := by unfold toC; fun_prop

theorem toR2_toC (v : Fin 2 → ℝ) : toR2 (toC v) = v := by
  funext i
  fin_cases i <;> simp [toR2, toC]

theorem toR2_injective : Function.Injective toR2 := fun z w h => by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [toR2] at h0 h1
  exact Complex.ext (by simpa using h0) (by simpa using h1)

theorem norm_toC_le (v : Fin 2 → ℝ) : ‖toC v‖ ≤ 2 * ‖v‖ :=
  calc ‖toC v‖ ≤ ‖(v 0 : ℂ)‖ + ‖(v 1 : ℂ) * I‖ := norm_add_le _ _
    _ = ‖v 0‖ + ‖v 1‖ := by simp
    _ ≤ ‖v‖ + ‖v‖ := add_le_add (norm_le_pi_norm v 0) (norm_le_pi_norm v 1)
    _ = 2 * ‖v‖ := by ring

/-- `Θ = Φ ∘ σ⁻¹ : ℂ = ℝ² → 𝕊²`, at most three-to-one. -/
noncomputable def sphereMap (w : ℂ) : Sphere2 := Fold.fold (Fold.chartInv (toR2 w))

theorem continuous_sphereMap : Continuous sphereMap :=
  Fold.continuous_fold_chartInv.comp continuous_toR2

theorem chartInv_injective : Function.Injective Fold.chartInv := by
  intro v w h
  have hinj := (stereographic' 2 Fold.p₁).symm.injOn
  have := hinj (by simp) (by simp) h
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.injective this

theorem finite_sphereMap_fibre (q : Sphere2) : (sphereMap ⁻¹' {q}).Finite := by
  have h3 := Set.finite_of_encard_le_coe (Fold.fibre_card_le_three q)
  have h4 : (Fold.chartInv ⁻¹' (Fold.fold ⁻¹' {q})).Finite :=
    h3.preimage chartInv_injective.injOn
  exact h4.preimage (f := toR2) toR2_injective.injOn

/-- The fold factorisation of a sphere-valued map of honorary Baire class `≤ 2`:
`φ = Θ ∘ χ` with `χ` bounded and of honorary Baire class `≤ 2`. -/
theorem exists_sphere_lift {X : Type*} [MetricSpace X] {φ : X → Sphere2}
    (hφ : IsHonoraryBaireTwo φ) :
    ∃ χ : X → ℂ, IsHonoraryBaireTwo χ ∧ (∃ B, ∀ x, ‖χ x‖ ≤ B) ∧
      ∀ x, sphereMap (χ x) = φ x := by
  classical
  obtain ⟨N, hN, hF⟩ := ((isHonoraryBaireTwo_tfae_sphere φ).out 0 1).1 hφ
  obtain ⟨ψ, hψ, hψφ, -, hψc⟩ := Fold.exists_factor hF
  have hs : ∀ x, ∃ p ∈ Fold.ZU ∪ Fold.ZV, Fold.fold p = φ x := fun x =>
    Fold.fold_surjOn (mem_univ (φ x))
  let ψ₀ : X → Sphere2 := fun x => if h : x ∈ Nᶜ then ψ ⟨x, h⟩ else (hs x).choose
  have hψ₀ : ∀ x, ψ₀ x ∈ Fold.ZU ∪ Fold.ZV ∧ Fold.fold (ψ₀ x) = φ x := fun x => by
    by_cases h : x ∈ Nᶜ
    · simp only [ψ₀, dif_pos h]; exact ⟨hψ _, hψφ _⟩
    · simp only [ψ₀, dif_neg h]; exact (hs x).choose_spec
  have hχ : IsHonoraryBaireTwo (Fold.chart ∘ ψ₀) := by
    have key := (isHonoraryBaireTwo_tfae_pi (Fold.chart ∘ ψ₀)).out 0 1
    refine key.2 ⟨N, hN, ?_⟩
    have : Nᶜ.restrict (Fold.chart ∘ ψ₀) = Fold.chart ∘ ψ := funext fun x => by
      show Fold.chart (ψ₀ x) = Fold.chart (ψ x)
      simp only [ψ₀, dif_pos x.2]
    rw [this]; exact hψc
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 Fold.bounded_chart
  refine ⟨toC ∘ Fold.chart ∘ ψ₀, hχ.continuous_comp continuous_toC,
    ⟨2 * C, fun x => (norm_toC_le _).trans ?_⟩, fun x => ?_⟩
  · have := hC _ ⟨ψ₀ x, (hψ₀ x).1, rfl⟩
    simp only [Function.comp]
    linarith
  · simp only [sphereMap, Function.comp, toR2_toC,
      Fold.chartInv_chart (Fold.ne_p₁_of_mem (hψ₀ x).1), (hψ₀ x).2]

/-- `thm:construct-F` (Trans. AMS 141, (F)): McMillan's problem. For an `F_σδ` set `A ⊆ C`
and `φ : A → 𝕊²` of honorary Baire class `≤ 2` there is a continuous `f : 𝔻 → 𝕊²` with
`CC(f) = A` having `φ` as a boundary function. -/
theorem exists_f_sphere' (A : Set ℂ) (hA : A ⊆ circle) (hAF : IsFσδ A)
    (φ : ℂ → Sphere2) (hφ : IsHonoraryBaireTwo (A.restrict φ)) :
    ∃ f : ℂ → Sphere2, ContinuousOn f disc ∧ curvConvSet disc circle f = A ∧
      IsBoundaryFunction disc f A φ := by
  classical
  obtain ⟨χ, hχ, ⟨B, hB⟩, hχφ⟩ := exists_sphere_lift hφ
  let χ₀ : ℂ → ℂ := fun z => if h : z ∈ A then χ ⟨z, h⟩ else 0
  have hres : A.restrict χ₀ = χ := funext fun z => by
    show (if h : (z : ℂ) ∈ A then χ ⟨z, h⟩ else 0) = χ z
    rw [dif_pos z.2]
  have hv : ∀ x ∈ A, sphereMap (χ₀ x) = φ x := fun x hx => by
    simp only [χ₀, dif_pos hx]; exact hχφ ⟨x, hx⟩
  obtain ⟨f₁, hf₁c, hf₁b, hf₁CC, hf₁BF⟩ := exists_f_disc A hA hAF χ₀
    ⟨B, fun x hx => by simp only [χ₀, dif_pos hx]; exact hB _⟩ (by rw [hres]; exact hχ)
  obtain ⟨R, hR⟩ := hf₁b.exists_norm_le
  refine ⟨sphereMap ∘ f₁, continuous_sphereMap.comp_continuousOn hf₁c, ?_, fun x hx => ?_⟩
  · rw [curvConvSet_comp_eq hf₁c (fun z hz => hR _ ⟨z, hz, rfl⟩) continuous_sphereMap
      finite_sphereMap_fibre, hf₁CC]
  · obtain ⟨γ, hγ, hl⟩ := hf₁BF x hx
    refine ⟨γ, hγ, ?_⟩
    have := (continuous_sphereMap.tendsto _).comp hl
    rwa [hv x hx] at this

end Sphere

/-! ### The half-plane (`thm:construct-H`) -/

section HalfPlane

open Complex Real

/-- `Ψ_ℍ` on `X`: `u ↦ tan (πu/2)`. -/
noncomputable def tanX (u : ℝ) : ℝ := Real.tan (π * u / 2)

/-- The set `Ψ_ℍ⁻¹(A) ⊆ (-1, 1)`. -/
def preX (A : Set ℝ) : Set ℝ := {u | u ∈ Ioo (-1) 1 ∧ tanX u ∈ A}

theorem isFσδ_preX {A : Set ℝ} (hA : IsFσδ A) : IsFσδ (preX A) := by
  let T : Ioo (-1 : ℝ) 1 → ℝ := fun u => tanX u
  have hT : Continuous T :=
    Real.continuousOn_tan_Ioo.comp_continuous (by fun_prop) fun u => pi_mul_div_two_mem u.2
  have h1 : IsFσδ (T ⁻¹' A) := hA.preimage hT
  have h2 : IsFσδ (Ioo (-1 : ℝ) 1) := (IsOpen.isFσ isOpen_Ioo).isFσδ
  convert h2.of_subtype h1 using 1
  ext u
  constructor
  · rintro ⟨hu, huA⟩; exact ⟨⟨u, hu⟩, huA, rfl⟩
  · rintro ⟨⟨u, hu⟩, huA, rfl⟩; exact ⟨hu, huA⟩

theorem isHonoraryBaireTwo_comp_tanX {Y : Type*} [TopologicalSpace Y] {A : Set ℝ} {φ : ℝ → Y}
    (hφ : IsHonoraryBaireTwo (A.restrict φ)) :
    IsHonoraryBaireTwo ((preX A).restrict (φ ∘ tanX)) := by
  let j : preX A → A := fun u => ⟨tanX u, u.2.2⟩
  have hj : Continuous j := (Real.continuousOn_tan_Ioo.comp_continuous
    (by fun_prop : Continuous fun u : preX A => π * (u : ℝ) / 2)
    fun u => pi_mul_div_two_mem u.2.1).subtype_mk _
  have hjinj : Function.Injective j := fun u v huv =>
    Subtype.ext (strictMonoOn_tan_pi_mul_div_two.injOn u.2.1 v.2.1 (congrArg Subtype.val huv))
  exact hφ.comp_continuous_injective hj hjinj

theorem chartHInv_ofReal (x : ℝ) : chartHInv x = ((2 / π * Real.arctan x : ℝ) : ℂ) :=
  Complex.ext (by rw [chartHInv_re, ofReal_re, ofReal_re])
    (by rw [chartHInv_im, ofReal_im, ofReal_im, zero_div])

theorem tanX_arctan (x : ℝ) : tanX (2 / π * Real.arctan x) = x :=
  tan_pi_mul_two_div_pi_mul_arctan x

theorem chartHInv_mem_preX {A : Set ℝ} {x : ℝ} :
    chartHInv x ∈ ((↑) : ℝ → ℂ) '' preX A ↔ x ∈ A := by
  rw [chartHInv_ofReal]
  constructor
  · rintro ⟨u, hu, hux⟩
    rw [← tanX_arctan x, ← ofReal_injective hux]
    exact hu.2
  · intro hx
    exact ⟨_, ⟨two_div_pi_mul_arctan_mem x, by rwa [tanX_arctan]⟩, rfl⟩

theorem image_preX_subset_baseX (A : Set ℝ) : ((↑) : ℝ → ℂ) '' preX A ⊆ baseX := by
  rintro _ ⟨u, hu, rfl⟩
  rw [← baseX_eq]
  exact ⟨u, hu.1, rfl⟩

theorem openSquare_subset_upperHP : openSquare ⊆ upper := fun _ hz => hz.2.1

theorem continuousOn_comp_chartHInv {Y : Type*} [TopologicalSpace Y] {f₁ : ℂ → Y}
    {s : Set ℂ} (hs : openSquare ⊆ s) (hf₁ : ContinuousOn f₁ s) :
    ContinuousOn (f₁ ∘ chartHPH.symm) upper :=
  hf₁.comp (chartHPH.continuousOn_symm.mono chartH_isChart.symm.subset_source)
    (chartH_isChart.symm.mapsTo.mono_right hs)

/-- Transfer of boundary functions from `Q°` to `ℍ` (`lem:transfer` for `Ψ_ℍ`). -/
theorem isBoundaryFunction_transfer_H {Y : Type*} [TopologicalSpace Y] {A : Set ℝ}
    {f₁ : ℂ → Y} {φ : ℝ → Y}
    (h : IsBoundaryFunction openSquare f₁ (((↑) : ℝ → ℂ) '' preX A) fun z => φ (tanX z.re)) :
    IsBoundaryFunction upper (f₁ ∘ chartHPH.symm) (((↑) : ℝ → ℂ) '' A) fun z => φ z.re := by
  refine ((transfer_isBoundaryFunction chartH_isChart.symm f₁ (image_preX_subset_baseX A)
    _).1 h).mono ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ (x : ℂ).im
      simp
    · show chartHInv x ∈ ((↑) : ℝ → ℂ) '' preX A
      exact chartHInv_mem_preX.2 hx
  · rintro _ ⟨x, -, rfl⟩
    show φ (x : ℂ).re = φ (tanX (chartHInv x).re)
    rw [chartHInv_ofReal, ofReal_re, ofReal_re, tanX_arctan]

/-- Transfer of the set of curvilinear convergence from `Q°` to `ℍ`. -/
theorem curvConvSet_transfer_H {Y : Type*} [TopologicalSpace Y] {A : Set ℝ} {f₁ : ℂ → Y}
    (h : curvConvSet openSquare baseX f₁ = ((↑) : ℝ → ℂ) '' preX A) :
    curvConvSet upper realAxis (f₁ ∘ chartHPH.symm) = ((↑) : ℝ → ℂ) '' A := by
  rw [transfer_curvConvSet chartH_isChart.symm, h]
  ext z
  constructor
  · rintro ⟨hz, hzA⟩
    obtain ⟨x, rfl⟩ : ∃ x : ℝ, (x : ℂ) = z :=
      ⟨z.re, Complex.ext (by simp) (by simp only [ofReal_im]; exact hz.symm)⟩
    exact ⟨x, chartHInv_mem_preX.1 hzA, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ofReal_im x, chartHInv_mem_preX.2 hx⟩

/-- `thm:construct-H` (a): a bounded continuous `f` on `ℍ` with `CC(f) = A` and boundary
function `φ`, for `A ⊆ ℝ` of class `F_σδ` and bounded `φ` of honorary Baire class `≤ 2`. -/
theorem exists_f_upperHalfPlane (A : Set ℝ) (hA : IsFσδ A) (φ : ℝ → ℂ)
    (hφb : ∃ B, ∀ x ∈ A, ‖φ x‖ ≤ B) (hφ : IsHonoraryBaireTwo (A.restrict φ)) :
    ∃ f : ℂ → ℂ, ContinuousOn f upper ∧ Bornology.IsBounded (f '' upper) ∧
      curvConvSet upper realAxis f = ((↑) : ℝ → ℂ) '' A ∧
      IsBoundaryFunction upper f (((↑) : ℝ → ℂ) '' A) (fun z => φ z.re) := by
  obtain ⟨B, hB⟩ := hφb
  obtain ⟨f₁, hf₁c, hf₁b, hf₁CC, hf₁BF⟩ := Construct.exists_f_Q (isFσδ_preX hA)
    (fun u hu => hu.1) (φ := φ ∘ tanX) ⟨B, fun u hu => hB _ hu.2⟩ (isHonoraryBaireTwo_comp_tanX hφ)
  rw [Qo_eq, baseX_eq] at hf₁CC
  rw [Qo_eq] at hf₁BF
  refine ⟨f₁ ∘ chartHPH.symm, continuousOn_comp_chartHInv openSquare_subset_Qc hf₁c, ?_,
    curvConvSet_transfer_H hf₁CC, isBoundaryFunction_transfer_H hf₁BF⟩
  refine hf₁b.subset ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨_, openSquare_subset_Qc (chartH_isChart.symm.mapsTo hz), rfl⟩

/-- `thm:construct-H` (a), sphere version. -/
theorem exists_f_upperHalfPlane_sphere (A : Set ℝ) (hA : IsFσδ A) (φ : ℝ → Sphere2)
    (hφ : IsHonoraryBaireTwo (A.restrict φ)) :
    ∃ f : ℂ → Sphere2, ContinuousOn f upper ∧
      curvConvSet upper realAxis f = ((↑) : ℝ → ℂ) '' A ∧
      IsBoundaryFunction upper f (((↑) : ℝ → ℂ) '' A) (fun z => φ z.re) := by
  classical
  obtain ⟨χ, hχ, ⟨B, hB⟩, hχφ⟩ := exists_sphere_lift hφ
  let χ₀ : ℝ → ℂ := fun x => if h : x ∈ A then χ ⟨x, h⟩ else 0
  have hres : A.restrict χ₀ = χ := funext fun x => by
    show (if h : (x : ℝ) ∈ A then χ ⟨x, h⟩ else 0) = χ x
    rw [dif_pos x.2]
  obtain ⟨f₁, hf₁c, hf₁b, hf₁CC, hf₁BF⟩ := exists_f_upperHalfPlane A hA χ₀
    ⟨B, fun x hx => by simp only [χ₀, dif_pos hx]; exact hB _⟩ (by rw [hres]; exact hχ)
  obtain ⟨R, hR⟩ := hf₁b.exists_norm_le
  refine ⟨sphereMap ∘ f₁, continuous_sphereMap.comp_continuousOn hf₁c, ?_, ?_⟩
  · rw [curvConvSet_comp_eq hf₁c (fun z hz => hR _ ⟨z, hz, rfl⟩) continuous_sphereMap
      finite_sphereMap_fibre, hf₁CC]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ, hl⟩ := hf₁BF _ ⟨x, hx, rfl⟩
    refine ⟨γ, hγ, ?_⟩
    have := (continuous_sphereMap.tendsto _).comp hl
    convert this using 2
    simp only [ofReal_re, χ₀, dif_pos hx]
    exact (hχφ ⟨x, hx⟩).symm

/-- A short segment of slope `|c| < √2 - 1` at `x ∈ (-1, 1)` is an arc at `x` in `Q°`, and a
limit along `y ↦ seg x c y` as `y → 0⁺` is a limit along the arc (any target space; compare
`exists_segArc`). -/
theorem exists_segArc' {Y : Type*} [TopologicalSpace Y] {x c : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hc : |c| < √2 - 1) :
    ∃ γ : Set ℂ, IsArcAt openSquare (x : ℂ) γ ∧
      ∀ (F : ℂ → Y) (L : Y), Tendsto (fun y => F (Construct.seg x c y)) (𝓝[>] 0) (𝓝 L) →
        Tendsto F (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 L) := by
  have hx' : |x| < 1 := abs_lt.2 hx
  have hc1 : |c| < 1 := by
    have : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  set y₁ : ℝ := min (1 / 2) ((1 - |x|) / 2) with hy₁
  have hy₁pos : 0 < y₁ := lt_min (by norm_num) (by linarith)
  let P : Path (x : ℂ) (Construct.seg x c y₁) :=
    ⟨⟨fun t => Construct.seg x c (y₁ * (t : ℝ)), by unfold Construct.seg; fun_prop⟩,
      by simp [Construct.seg], by simp⟩
  have hPim : ∀ t : unitInterval, (P t).im = y₁ * t := fun t => by simp [P]
  have hPseg : ∀ t : unitInterval, P t = Construct.seg x c (P t).im := fun t => by
    rw [hPim]; rfl
  have hPinj : Function.Injective P := fun s t hst => by
    have := congrArg Complex.im hst
    rw [hPim, hPim] at this
    exact Subtype.ext (mul_left_cancel₀ hy₁pos.ne' this)
  have hmem : ∀ z ∈ range P \ {(x : ℂ)},
      0 < z.im ∧ z.im ≤ y₁ ∧ Construct.seg x c z.im = z := by
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    have ht0 : (0 : ℝ) < t := by
      refine lt_of_le_of_ne t.2.1 fun h0 => ht ?_
      have : t = 0 := Subtype.ext h0.symm
      rw [this, mem_singleton_iff, P.source]
    rw [hPim]
    exact ⟨mul_pos hy₁pos ht0, mul_le_of_le_one_right hy₁pos.le t.2.2, by rw [← hPim, ← hPseg]⟩
  refine ⟨range P, ⟨_, ⟨P, hPinj, rfl⟩, fun z hz => ?_⟩, fun F L hF => ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hmem z hz
    have h3 := min_le_left (1 / 2 : ℝ) ((1 - |x|) / 2)
    have h4 := min_le_right (1 / 2 : ℝ) ((1 - |x|) / 2)
    rw [← Qo_eq]
    refine ⟨?_, h0, by linarith⟩
    rw [← h2, Construct.seg_re]
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

/-- `thm:construct-H` (b) for `ℝ^m = Fin m → ℝ`. -/
theorem exists_boundaryFn_pi {m : ℕ} (E : Set ℝ) (φ : ℝ → Fin m → ℝ)
    (hφ : IsHonoraryBaireTwo (E.restrict φ)) :
    ∃ f : ℂ → Fin m → ℝ, ContinuousOn f upper ∧
      IsBoundaryFunction upper f (((↑) : ℝ → ℂ) '' E) (fun z => φ z.re) := by
  obtain ⟨h, hhc, hhl⟩ := Construct.exists_h (E := preX E) (fun u hu => hu.1) (isHonoraryBaireTwo_comp_tanX hφ)
  have hBF : IsBoundaryFunction openSquare h (((↑) : ℝ → ℂ) '' preX E)
      (fun z => φ (tanX z.re)) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨c, hc, hlim⟩ := hhl p hp
    obtain ⟨γ, hγ, hγl⟩ := exists_segArc' (Y := Fin m → ℝ) hp.1 hc
    exact ⟨γ, hγ, hγl h _ hlim⟩
  exact ⟨h ∘ chartHPH.symm, continuousOn_comp_chartHInv openSquare_subset_upperHP hhc,
    isBoundaryFunction_transfer_H hBF⟩

/-- `thm:construct-H` (b), dissertation Theorem 6: every `φ : E → ℝ^m` of honorary Baire class
`≤ 2` (`E ⊆ ℝ` arbitrary) is a boundary function of a continuous `f : ℍ → ℝ^m`. -/
theorem exists_boundaryFn_euclidean' {m : ℕ} (E : Set ℝ)
    (φ : ℝ → EuclideanSpace ℝ (Fin m)) (hφ : IsHonoraryBaireTwo (E.restrict φ)) :
    ∃ f : ℂ → EuclideanSpace ℝ (Fin m), ContinuousOn f upper ∧
      IsBoundaryFunction upper f (((↑) : ℝ → ℂ) '' E) (fun z => φ z.re) := by
  let e := EuclideanSpace.equiv (Fin m) ℝ
  obtain ⟨f, hfc, hf⟩ :=
    exists_boundaryFn_pi E (e ∘ φ) (by exact hφ.continuous_comp e.continuous)
  refine ⟨e.symm ∘ f, e.symm.continuous.comp_continuousOn hfc, fun x hx => ?_⟩
  obtain ⟨γ, hγ, hl⟩ := hf x hx
  refine ⟨γ, hγ, ?_⟩
  have := (e.symm.continuous.tendsto _).comp hl
  simpa using this

/-- `thm:construct-H` (c), dissertation Theorem 7: the same with values in the sphere. -/
theorem exists_boundaryFn_sphere (E : Set ℝ) (φ : ℝ → Sphere2)
    (hφ : IsHonoraryBaireTwo (E.restrict φ)) :
    ∃ f : ℂ → Sphere2, ContinuousOn f upper ∧
      IsBoundaryFunction upper f (((↑) : ℝ → ℂ) '' E) (fun z => φ z.re) := by
  classical
  obtain ⟨χ, hχ, -, hχφ⟩ := exists_sphere_lift hφ
  let χ₀ : ℝ → Fin 2 → ℝ := fun x => if h : x ∈ E then toR2 (χ ⟨x, h⟩) else 0
  have hres : E.restrict χ₀ = toR2 ∘ χ := funext fun x => by
    show (if h : (x : ℝ) ∈ E then toR2 (χ ⟨x, h⟩) else 0) = toR2 (χ x)
    rw [dif_pos x.2]
  obtain ⟨f₁, hf₁c, hf₁⟩ :=
    exists_boundaryFn_pi E χ₀ (by rw [hres]; exact hχ.continuous_comp continuous_toR2)
  refine ⟨(Fold.fold ∘ Fold.chartInv) ∘ f₁,
    Fold.continuous_fold_chartInv.comp_continuousOn hf₁c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨γ, hγ, hl⟩ := hf₁ _ ⟨x, hx, rfl⟩
  refine ⟨γ, hγ, ?_⟩
  have := (Fold.continuous_fold_chartInv.tendsto _).comp hl
  convert this using 2
  simp only [ofReal_re, χ₀, dif_pos hx, Function.comp]
  exact (hχφ ⟨x, hx⟩).symm

end HalfPlane

end TJK.Construct
