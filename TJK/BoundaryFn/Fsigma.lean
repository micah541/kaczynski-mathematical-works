import Mathlib
import TJK.Defs
import TJK.Plane.Basic
import TJK.Plane.Crosscut
import TJK.Baire.Basic
import TJK.Baire.Approx
import TJK.Baire.Higher
import TJK.Baire.Sphere
import TJK.McMillan.Basic

/-!
# Boundary functions of continuous functions are of class `F_σ` off a countable set (blueprint §E)

* `lem:th-lemma15` (`isFσMeasurable_of_sandwich`);
* `thm:bf-fsigma` (`BoundaryFn.exists_countable_isFσMeasurable'`, dissertation Theorem 5), and its
  disc version `BoundaryFn.exists_countable_isFσMeasurable_disc`;
* `cor:bf-honorary`: boundary functions into `ℝ^m` or the sphere are of honorary Baire class two;
* `fact:bagemihl` (`bagemihl_ambiguous_countable`, imported, `sorry`);
* `prop:gdelta-remark` (`McMillan.isFσδ_limit_mem_of_isGδ`).
-/

namespace TJK

open _root_.Set Filter Topology Function TopologicalSpace

/-! ### `lem:th-lemma15` -/

/-- **Dissertation Lemma 15.** Let `Y` be a separable metric space, `E ⊆ X` and `φ : X → Y`. If for
every open `U ⊆ Y` there are an `F_σ` set `L` and a countable set `N` with
`E ∩ φ⁻¹(U) ⊆ L` and `E ∩ L ⊆ φ⁻¹(closure U) ∪ N`, then `φ` is of class `F_σ` on `E \ M` for a
countable `M ⊆ E`. -/
theorem isFσMeasurable_of_sandwich {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    [SeparableSpace Y] {E : Set X} {φ : X → Y}
    (h : ∀ U : Set Y, IsOpen U → ∃ L N : Set X, IsFσ L ∧ N.Countable ∧ E ∩ φ ⁻¹' U ⊆ L ∧
      E ∩ L ⊆ φ ⁻¹' closure U ∪ N) :
    ∃ M ⊆ E, M.Countable ∧ IsFσMeasurable ((E \ M).restrict φ) := by
  choose L N hL hN hUL hLU using h
  have hbasis := isBasis_countableBasis Y
  have := (countable_countableBasis Y).to_subtype
  set M := E ∩ ⋃ B : countableBasis Y, N B (hbasis.isOpen B.2) with hM
  refine ⟨M, inter_subset_left, (countable_iUnion fun B => hN _ _).mono inter_subset_right,
    fun W hW => ?_⟩
  have hcount : {B ∈ countableBasis Y | closure B ⊆ W}.Countable :=
    (countable_countableBasis Y).mono (sep_subset _ _)
  have := hcount.to_subtype
  have key : (E \ M).restrict φ ⁻¹' W = Subtype.val ⁻¹'
      ⋃ B : {B ∈ countableBasis Y | closure B ⊆ W}, L B (hbasis.isOpen B.2.1) := by
    ext ⟨p, hpE, hpM⟩
    simp only [mem_preimage, mem_iUnion]
    constructor
    · intro hp
      obtain ⟨B, hB, hpB, hBW⟩ := hbasis.exists_closure_subset (hW.mem_nhds hp)
      exact ⟨⟨B, hB, hBW⟩, hUL _ _ ⟨hpE, hpB⟩⟩
    · rintro ⟨⟨B, hB, hBW⟩, hpL⟩
      rcases hLU _ _ ⟨hpE, hpL⟩ with h | h
      · exact hBW h
      · exact absurd ⟨hpE, mem_iUnion.2 ⟨⟨B, hB⟩, h⟩⟩ hpM
  rw [key]
  exact (IsFσ.iUnion fun B => hL _ _).preimage continuous_subtype_val

namespace BoundaryFn

/-! ### `thm:bf-fsigma` -/

section Theorem5

variable {Y : Type*} [TopologicalSpace Y]

/-- The points `x ∈ ℝ` with an arc at `x` mapped by `f` into `U` (apart from `x`) and reaching the
height `c`. -/
def reachSet (f : ℂ → Y) (U : Set Y) (c : ℝ) : Set ℝ :=
  {x | ∃ γ, IsArcAt upper (x : ℂ) γ ∧ MapsTo f (γ \ {(x : ℂ)}) U ∧ ∃ z ∈ γ, c ≤ z.im}

/-- The points `x ∈ ℝ` with an arc at `x` mapped by `f` into `W` (apart from `x`). -/
def arcSet (f : ℂ → Y) (W : Set Y) : Set ℝ :=
  {x | ∃ γ, IsArcAt upper (x : ℂ) γ ∧ MapsTo f (γ \ {(x : ℂ)}) W}

theorem mem_arcSet {f : ℂ → Y} {x : ℝ} {γ : Set ℂ} (hγ : IsArcAt upper (x : ℂ) γ) {p : Y}
    (hlim : Tendsto f (𝓝[γ \ {(x : ℂ)}] x) (𝓝 p)) {W : Set Y} (hW : IsOpen W) (hp : p ∈ W) :
    x ∈ arcSet f W := by
  obtain ⟨γ', -, hγ', hmaps⟩ := hγ.tendsto_subarc hlim (hW.mem_nhds hp) univ_mem
  exact ⟨γ', hγ', hmaps⟩

theorem exists_mem_reachSet {f : ℂ → Y} {x : ℝ} {γ : Set ℂ} (hγ : IsArcAt upper (x : ℂ) γ)
    {p : Y} (hlim : Tendsto f (𝓝[γ \ {(x : ℂ)}] x) (𝓝 p)) {U : Set Y} (hU : IsOpen U)
    (hp : p ∈ U) : ∃ n : ℕ, x ∈ reachSet f U (1 / (n + 1)) := by
  obtain ⟨γ', -, hγ', hmaps⟩ := hγ.tendsto_subarc hlim (hU.mem_nhds hp) univ_mem
  obtain ⟨b, hb, hbH⟩ := id hγ'
  have hbu : b ∈ upper := hbH ⟨hb.right_mem, fun h => hb.ne (mem_singleton_iff.1 h).symm⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < b.im from hbu)
  exact ⟨n, γ', hγ', hmaps, b, hb.right_mem, hn.le⟩

/-- The key step of Theorem 5: the points of `closure E_c` with an arc at them mapped into `W` form
a countable set, if `U ∩ W = ∅` (here `E_c` is `reachSet f U c`). -/
theorem countable_arcSet_inter_closure {f : ℂ → Y} (hf : ContinuousOn f upper) {U W : Set Y}
    (hW : IsOpen W) (hUW : Disjoint U W) {c : ℝ} (hc : 0 < c) :
    (arcSet f W ∩ closure (reachSet f U c)).Countable := by
  set O : Set ℂ := {z | z.im < c} ∩ (upper ∩ f ⁻¹' W) with hO
  have hOo : IsOpen O := (isOpen_lt Complex.continuous_im continuous_const).inter
    (hf.isOpen_inter_preimage (isOpen_lt continuous_const Complex.continuous_im) hW)
  -- for `x ∈ K`, an arc at `x` with its other points in `O`
  have hlow : ∀ x ∈ arcSet f W, ∃ γ : Set ℂ, ∃ b : ℂ, IsArc γ (x : ℂ) b ∧ γ \ {(x : ℂ)} ⊆ O := by
    rintro x ⟨γ, hγ, hmaps⟩
    have hnhds : {z : ℂ | z.im < c} ∈ 𝓝 (x : ℂ) :=
      (isOpen_lt Complex.continuous_im continuous_const).mem_nhds (by simpa using hc)
    obtain ⟨γ', hγ'γ, ⟨b, hb, hbH⟩, -⟩ := hγ.exists_subarc_subset hnhds
    exact ⟨γ', b, hb, fun z hz => ⟨(hγ'γ hz.1).2, hbH hz, hmaps ⟨(hγ'γ hz.1).1, hz.2⟩⟩⟩
  choose! γ b hγ hγO using hlow
  have hbO : ∀ x ∈ arcSet f W, b x ∈ O := fun x hx =>
    hγO x hx ⟨(hγ x hx).right_mem, fun h => (hγ x hx).ne (mem_singleton_iff.1 h).symm⟩
  obtain ⟨hcount, -, hpath, -⟩ := countable_connectedComponents_of_isOpen hOo
  set S := reachSet f U c
  set T := {x | x ∈ arcSet f W ∩ closure S ∧ ((∀ r > 0, (Ioo (x - r) x ∩ S).Nonempty) ∧
      ∀ r > 0, (Ioo x (x + r) ∩ S).Nonempty)}
  -- `x ↦` (the component of `O` containing the arc at `x`) is injective on `T`
  have key : ∀ x ∈ T, ∀ y ∈ T, x < y →
      connectedComponentIn O (b x) = connectedComponentIn O (b y) → False := by
    intro x hx y hy hxy hcomp
    have hxK := hx.1.1
    have hyK := hy.1.1
    have hj : JoinedIn (connectedComponentIn O (b x)) (b x) (b y) := by
      refine (hpath _ (hbO x hxK)).joinedIn _ (mem_connectedComponentIn (hbO x hxK)) _ ?_
      rw [hcomp]; exact mem_connectedComponentIn (hbO y hyK)
    obtain ⟨q₁, -, hq₁⟩ := hγ x hxK
    obtain ⟨q₂, -, hq₂⟩ := hγ y hyK
    set g : Path (x : ℂ) (y : ℂ) := (q₁.trans hj.somePath).trans q₂.symm
    have hxy' : (x : ℂ) ≠ y := fun h => hxy.ne (Complex.ofReal_injective h)
    -- a crosscut `α` from `x` to `y` inside `O`
    obtain ⟨α, hαg, hα⟩ := exists_arc_in_path g hxy'
    have hαO : α \ {(x : ℂ), (y : ℂ)} ⊆ O := by
      rintro z ⟨hzα, hz⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
      have hzg := hαg hzα
      simp only [g, Path.trans_range, Path.symm_range, hq₁, hq₂, mem_union] at hzg
      rcases hzg with (h | h) | h
      · exact hγO x hxK ⟨h, hz.1⟩
      · obtain ⟨t, rfl⟩ := h
        exact connectedComponentIn_subset _ _ (hj.somePath_mem t)
      · exact hγO y hyK ⟨h, hz.2⟩
    have hαc : ∀ v ∈ α, v.im < c := by
      intro v hv
      by_cases hvx : v = x
      · rw [hvx]; simpa using hc
      by_cases hvy : v = y
      · rw [hvy]; simpa using hc
      exact (hαO ⟨hv, by simp [hvx, hvy]⟩).1
    obtain ⟨A, V, hAo, hVo, -, -, hAV, hcov, -, -, hclA, -, -, habove⟩ :=
      crosscutH_theorem hxy hα fun z hz => (hαO hz).2.1
    -- a point `w ∈ (x, y) ∩ E_c` and its arc `β`
    obtain ⟨w, hwI, hwS⟩ := hy.2.1 (y - x) (sub_pos.2 hxy)
    rw [sub_sub_cancel] at hwI
    obtain ⟨β, hβ, hβU, z₀, hz₀β, hz₀c⟩ := hwS
    obtain ⟨bβ, hβarc, hβH⟩ := id hβ
    have hsub : β \ {(w : ℂ)} ⊆ A ∪ V := by
      rw [← hcov]
      refine fun z hz => ⟨hβH hz, fun hzα => ?_⟩
      have hzH : z ∈ upper := hβH hz
      have hzO : z ∈ O := hαO ⟨hzα, by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        constructor <;> rintro rfl <;> simp at hzH⟩
      exact disjoint_left.1 hUW (hβU hz) hzO.2.2
    have hz₀ : z₀ ∈ β \ {(w : ℂ)} := ⟨hz₀β, fun h => by
      rw [mem_singleton_iff] at h; subst h; simp at hz₀c; linarith⟩
    have hz₀A : z₀ ∈ A := habove z₀ fun v hv => (hαc v hv).trans_le hz₀c
    have hβA : β \ {(w : ℂ)} ⊆ A :=
      hβarc.isPreconnected_diff_left.subset_left_of_subset_union hAo hVo hAV hsub ⟨z₀, hz₀, hz₀A⟩
    have hwA : (w : ℂ) ∈ closure A ∩ realAxis :=
      ⟨closure_mono hβA (McMillan.IsArcAt.mem_closure_diff hβ), by simp⟩
    rw [hclA] at hwA
    obtain ⟨t, ht, htw⟩ := hwA
    rw [Complex.ofReal_inj] at htw
    subst htw
    rcases ht with ht | ht
    · exact absurd hwI.1 (not_lt.2 ht)
    · exact absurd hwI.2 (not_lt.2 ht)
  have hT : T.Countable := by
    refine MapsTo.countable_of_injOn (f := fun x => connectedComponentIn O (b x))
      (t := {C | ∃ x ∈ O, connectedComponentIn O x = C})
      (fun x hx => ⟨b x, hbO x hx.1.1, rfl⟩) (fun x hx y hy hxy => ?_) hcount
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key x hx y hy h hxy
    · exact key y hy x hx h hxy.symm
  refine (hT.union (countable_not_twoSided S)).mono fun x hx => ?_
  by_cases h : x ∈ T
  · exact Or.inl h
  · exact Or.inr ⟨hx.2, fun h' => h ⟨hx, h'⟩⟩

end Theorem5

/-- **Dissertation Theorem 5** (`thm:bf-fsigma`). A boundary function `φ : E → Y` (`E ⊆ ℝ`, `Y`
separable metric) of a continuous `f : ℍ → Y` is of class `F_σ` off a countable set. -/
theorem exists_countable_isFσMeasurable' {Y : Type*} [MetricSpace Y]
    [SeparableSpace Y] (f : ℂ → Y) (hf : ContinuousOn f upper) (E : Set ℂ)
    (hE : E ⊆ realAxis) (φ : ℂ → Y) (hφ : IsBoundaryFunction upper f E φ) :
    ∃ M ⊆ E, M.Countable ∧ IsFσMeasurable ((E \ M).restrict φ) := by
  refine isFσMeasurable_of_sandwich fun U hU => ?_
  set W := (closure U)ᶜ
  have hW : IsOpen W := isClosed_closure.isOpen_compl
  have hUW : Disjoint U W := disjoint_compl_right.mono_left subset_closure
  set S : ℕ → Set ℝ := fun n => reachSet f U (1 / (n + 1))
  have hcl : IsClosedMap ((↑) : ℝ → ℂ) := Complex.isometry_ofReal.isClosedEmbedding.isClosedMap
  have hre : ∀ z ∈ E, ((z.re : ℝ) : ℂ) = z := fun z hz => Complex.ext (by simp) (by simpa using (hE hz).symm)
  refine ⟨⋃ n, (↑) '' closure (S n), ⋃ n, (↑) '' (arcSet f W ∩ closure (S n)),
    IsFσ.iUnion fun n => IsClosed.isFσ (hcl _ isClosed_closure),
    countable_iUnion fun n => (countable_arcSet_inter_closure hf hW hUW (by positivity)).image _,
    ?_, ?_⟩
  · rintro z ⟨hzE, hzU⟩
    obtain ⟨x, rfl⟩ : ∃ x : ℝ, (x : ℂ) = z := ⟨z.re, hre z hzE⟩
    obtain ⟨γ, hγ, hlim⟩ := hφ _ hzE
    obtain ⟨n, hn⟩ := exists_mem_reachSet hγ hlim hU hzU
    exact mem_iUnion.2 ⟨n, x, subset_closure hn, rfl⟩
  · rintro z ⟨hzE, hzL⟩
    obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.1 hzL
    by_cases hz : φ x ∈ closure U
    · exact Or.inl hz
    · obtain ⟨γ, hγ, hlim⟩ := hφ _ hzE
      exact Or.inr (mem_iUnion.2 ⟨n, x, ⟨mem_arcSet hγ hlim hW hz, hx⟩, rfl⟩)

/-- `thm:bf-fsigma` in the disc: transfer from `ℍ` by the Cayley map `κ`; the point `1` is one
more exception. -/
theorem exists_countable_isFσMeasurable_disc {Y : Type*} [MetricSpace Y] [SeparableSpace Y]
    (f : ℂ → Y) (hf : ContinuousOn f disc) (E : Set ℂ) (hE : E ⊆ circle) (φ : ℂ → Y)
    (hφ : IsBoundaryFunction disc f E φ) :
    ∃ M ⊆ E, M.Countable ∧ IsFσMeasurable ((E \ M).restrict φ) := by
  set e := cayleyPH
  have hch := cayley_isChart
  set E' := e.source ∩ e ⁻¹' (E \ {1})
  have hφ' : IsBoundaryFunction upper (f ∘ e) E' (φ ∘ e) :=
    (transfer_isBoundaryFunction hch f (fun z hz => ⟨hE hz.1, hz.2⟩) φ).1
      fun z hz => hφ z hz.1
  have hf' : ContinuousOn (f ∘ e) upper :=
    hf.comp (e.continuousOn.mono hch.subset_source) hch.mapsTo
  have hE' : E' ⊆ realAxis := fun z hz => (hch.mem_boundary_iff hz.1).1 ⟨hE hz.2.1, hz.2.2⟩
  obtain ⟨M', -, hM', hmeas⟩ := exists_countable_isFσMeasurable' _ hf' E' hE' _ hφ'
  set M := E ∩ (e '' M' ∪ {1})
  refine ⟨M, inter_subset_left,
    ((hM'.image _).union (countable_singleton _)).mono inter_subset_right, ?_⟩
  have hpt : ∀ p : ↥(E \ M), (p : ℂ) ∈ e.target := fun p =>
    hch.boundary_subset_target ⟨hE p.2.1, fun h => p.2.2 ⟨p.2.1, Or.inr h⟩⟩
  have hmem : ∀ p : ↥(E \ M), e.symm p ∈ E' \ M' := by
    intro p
    refine ⟨⟨e.map_target (hpt p), ?_⟩, fun h => p.2.2 ⟨p.2.1, Or.inl ⟨_, h, e.right_inv (hpt p)⟩⟩⟩
    rw [mem_preimage, e.right_inv (hpt p)]
    exact ⟨p.2.1, fun h => p.2.2 ⟨p.2.1, Or.inr h⟩⟩
  have hcont : Continuous fun p : ↥(E \ M) => (⟨e.symm p, hmem p⟩ : ↥(E' \ M')) :=
    (e.continuousOn_symm.comp_continuous continuous_subtype_val hpt).subtype_mk _
  convert hmeas.comp_continuous hcont using 1
  funext p
  change φ p = φ (e (e.symm p))
  rw [e.right_inv (hpt p)]

/-! ### `cor:bf-honorary` -/

/-- From `E \ M` to the complement of `M` in the subspace `E`. -/
theorem isFσMeasurable_restrict_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {E M : Set X} {φ : X → Y} (h : IsFσMeasurable ((E \ M).restrict φ)) :
    IsFσMeasurable ((Subtype.val ⁻¹' M : Set E)ᶜ.restrict (E.restrict φ)) :=
  h.comp_continuous
    (g := fun p : ↥((Subtype.val ⁻¹' M : Set E)ᶜ) => (⟨p.1.1, p.1.2, p.2⟩ : ↥(E \ M)))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

/-- `cor:bf-honorary`: boundary functions into `ℝ^m` of continuous maps in `ℍ` are of honorary
Baire class two. -/
theorem isHonoraryBaireTwo_upperHalfPlane {m : ℕ} (f : ℂ → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f upper) (E : Set ℂ) (hE : E ⊆ realAxis) (φ : ℂ → EuclideanSpace ℝ (Fin m))
    (hφ : IsBoundaryFunction upper f E φ) : IsHonoraryBaireTwo (E.restrict φ) := by
  obtain ⟨M, -, hM, h⟩ := exists_countable_isFσMeasurable' f hf E hE φ hφ
  refine ((isHonoraryBaireTwo_tfae_euclidean (E.restrict φ)).out 0 1).2 ?_
  exact ⟨_, hM.preimage Subtype.val_injective, isFσMeasurable_restrict_preimage h⟩

/-- `cor:bf-honorary`: boundary functions into the sphere of continuous maps in `ℍ` are of
honorary Baire class two. -/
theorem isHonoraryBaireTwo_upperHalfPlane_sphere (f : ℂ → Sphere2) (hf : ContinuousOn f upper)
    (E : Set ℂ) (hE : E ⊆ realAxis) (φ : ℂ → Sphere2) (hφ : IsBoundaryFunction upper f E φ) :
    IsHonoraryBaireTwo (E.restrict φ) := by
  obtain ⟨M, -, hM, h⟩ := exists_countable_isFσMeasurable' f hf E hE φ hφ
  refine ((isHonoraryBaireTwo_tfae_sphere (E.restrict φ)).out 0 1).2 ?_
  exact ⟨_, hM.preimage Subtype.val_injective, isFσMeasurable_restrict_preimage h⟩

/-- `cor:bf-honorary` (1965 paper, Theorem 2): real version on the circle. -/
theorem isHonoraryBaireTwo_disc_real' (f : ℂ → ℝ) (hf : ContinuousOn f disc)
    (E : Set ℂ) (hE : E ⊆ circle) (φ : ℂ → ℝ) (hφ : IsBoundaryFunction disc f E φ) :
    IsHonoraryBaireTwo (E.restrict φ) := by
  obtain ⟨M, -, hM, h⟩ := exists_countable_isFσMeasurable_disc f hf E hE φ hφ
  refine ((isHonoraryBaireTwo_tfae_of_extend (E.restrict φ) fun N hN h =>
    exists_extend_of_countable_compl_real (by rwa [compl_compl]) h).out 0 1).2 ?_
  exact ⟨_, hM.preimage Subtype.val_injective, isFσMeasurable_restrict_preimage h⟩

/-- `cor:bf-honorary` (1965 paper, Theorem 3): Riemann-sphere version on the circle. -/
theorem isHonoraryBaireTwo_disc_sphere' (f : ℂ → Sphere2) (hf : ContinuousOn f disc)
    (E : Set ℂ) (hE : E ⊆ circle) (φ : ℂ → Sphere2) (hφ : IsBoundaryFunction disc f E φ) :
    IsHonoraryBaireTwo (E.restrict φ) := by
  obtain ⟨M, -, hM, h⟩ := exists_countable_isFσMeasurable_disc f hf E hE φ hφ
  refine ((isHonoraryBaireTwo_tfae_sphere (E.restrict φ)).out 0 1).2 ?_
  exact ⟨_, hM.preimage Subtype.val_injective, isFσMeasurable_restrict_preimage h⟩

end BoundaryFn

/-! ### `fact:bagemihl` and `prop:gdelta-remark` -/

/-- `fact:bagemihl` (Bagemihl's ambiguous point theorem, 1955): for any `f : 𝔻 → S²`, the points
of `C` with two arcs along which `f` has different limits form a countable set.
Imported fact; not in Mathlib. -/
theorem bagemihl_ambiguous_countable (f : ℂ → Sphere2) :
    {x | x ∈ circle ∧ ∃ γ₁ γ₂ : Set ℂ, ∃ p₁ p₂ : Sphere2, IsArcAt disc x γ₁ ∧
      IsArcAt disc x γ₂ ∧ Tendsto f (𝓝[γ₁ \ {x}] x) (𝓝 p₁) ∧
      Tendsto f (𝓝[γ₂ \ {x}] x) (𝓝 p₂) ∧ p₁ ≠ p₂}.Countable := by
  sorry

/-- `prop:gdelta-remark` (Michigan Math. J. 1966, remark after Corollary 4): McMillan's
`cor:mm-corollaries` (1) holds for `G_δ` sets `E ⊆ S²`. -/
theorem McMillan.isFσδ_limit_mem_of_isGδ (f : ℂ → Sphere2) (hf : ContinuousOn f disc)
    {E : Set Sphere2} (hE : IsGδ E) :
    IsFσδ {x | x ∈ circle ∧ ∃ γ, IsArcAt disc x γ ∧ ∃ p ∈ E,
      Tendsto f (𝓝[γ \ {x}] x) (𝓝 p)} := by
  set A := curvConvSet disc circle f
  have hA : IsFσδ A := McMillan.isFσδ_curvConvSet' f hf
  have : Nonempty Sphere2 := ⟨f 0⟩
  have hex : ∀ x ∈ A, ∃ q : Sphere2, ∃ γ, IsArcAt disc x γ ∧
      Tendsto f (𝓝[γ \ {x}] x) (𝓝 q) := by
    rintro x ⟨-, γ, hγ, q, hq⟩
    exact ⟨q, γ, hγ, hq⟩
  choose! φ γ hγ hlim using hex
  obtain ⟨M, -, hM, hmeas⟩ := BoundaryFn.exists_countable_isFσMeasurable_disc f hf A
    (fun x hx => hx.1) φ fun x hx => ⟨γ x, hγ x hx, hlim x hx⟩
  set Z := {x | x ∈ circle ∧ ∃ γ₁ γ₂ : Set ℂ, ∃ p₁ p₂ : Sphere2, IsArcAt disc x γ₁ ∧
      IsArcAt disc x γ₂ ∧ Tendsto f (𝓝[γ₁ \ {x}] x) (𝓝 p₁) ∧
      Tendsto f (𝓝[γ₂ \ {x}] x) (𝓝 p₂) ∧ p₁ ≠ p₂}
  have hZ : Z.Countable := bagemihl_ambiguous_countable f
  set S := {x | x ∈ circle ∧ ∃ γ, IsArcAt disc x γ ∧ ∃ p ∈ E, Tendsto f (𝓝[γ \ {x}] x) (𝓝 p)}
  set P := Subtype.val '' ((A \ M).restrict φ ⁻¹' E)
  have hAM : IsFσδ (A \ M) := hA.inter (IsGδ.isFσδ hM.isGδ_compl)
  have hP : IsFσδ P := by
    refine IsFσδ.of_subtype hAM ?_
    obtain ⟨O, hO, rfl⟩ := isGδ_iff_eq_iInter_nat.1 hE
    exact ⟨fun j => (A \ M).restrict φ ⁻¹' O j, fun j => hmeas _ (hO j), by rw [preimage_iInter]⟩
  have hS : S = (P ∩ Zᶜ) ∪ (S ∩ (M ∪ Z)) := by
    ext x
    constructor
    · intro hx
      by_cases hxMZ : x ∈ M ∪ Z
      · exact Or.inr ⟨hx, hxMZ⟩
      left
      rw [mem_union, not_or] at hxMZ
      obtain ⟨hxC, β, hβ, p, hpE, hp⟩ := hx
      have hxA : x ∈ A := ⟨hxC, β, hβ, p, hp⟩
      have hpφ : p = φ x := by
        by_contra hne
        exact hxMZ.2 ⟨hxC, β, γ x, p, φ x, hβ, hγ x hxA, hp, hlim x hxA, hne⟩
      subst hpφ
      exact ⟨⟨⟨x, hxA, hxMZ.1⟩, hpE, rfl⟩, hxMZ.2⟩
    · rintro (⟨⟨⟨x, hxA, hxM⟩, hxE, rfl⟩, -⟩ | ⟨hx, -⟩)
      · exact ⟨hxA.1, γ x, hγ x hxA, φ x, hxE, hlim x hxA⟩
      · exact hx
  rw [hS]
  exact (hP.inter (IsGδ.isFσδ hZ.isGδ_compl)).union
    (IsFσ.isFσδ (Set.Countable.isFσ ((hM.union hZ).mono inter_subset_right)))

end TJK
