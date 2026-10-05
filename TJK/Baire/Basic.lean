/-
Copyright: the TJK formalization project.

Section B of the blueprint (`paper/sections/B-baire.tex`), first part: closure properties of the
classes `F_σ`, `G_δ`, `F_σδ`, the reduction property of `F_σ` sets, Sierpiński's ambiguous
interpolation, and the first facts on functions of class `F_σ`.

The metric hypotheses of the paper are replaced by `PerfectlyNormalSpace` (every closed set is
`G_δ`, and the space is normal), which every (pseudo)metrizable space is.
-/
import Mathlib
import TJK.Defs

open Set Filter Topology Function

namespace TJK

/-! ## Closure properties (blueprint `lem:borel-basic`) -/

section BorelBasic

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

/-- The complement of a set is `G_δ` iff the set is `F_σ`. -/
theorem isGδ_compl_iff {s : Set X} : IsGδ sᶜ ↔ IsFσ s := by
  rw [isGδ_iff_eq_iInter_nat]
  constructor
  · rintro ⟨f, hf, h⟩
    refine ⟨fun n => (f n)ᶜ, fun n => (hf n).isClosed_compl, ?_⟩
    rw [← compl_iInter, ← h, compl_compl]
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun n => (F n)ᶜ, fun n => (hF n).isOpen_compl, compl_iUnion _⟩

/-- The complement of a set is `F_σ` iff the set is `G_δ`. -/
theorem isFσ_compl_iff {s : Set X} : IsFσ sᶜ ↔ IsGδ s := by
  rw [← isGδ_compl_iff, compl_compl]

theorem IsFσ.isGδ_compl {s : Set X} (hs : IsFσ s) : IsGδ sᶜ := isGδ_compl_iff.2 hs

theorem IsGδ.isFσ_compl {s : Set X} (hs : IsGδ s) : IsFσ sᶜ := isFσ_compl_iff.2 hs

theorem IsClosed.isFσ {s : Set X} (hs : IsClosed s) : IsFσ s :=
  ⟨fun _ => s, fun _ => hs, (iUnion_const s).symm⟩

theorem isFσ_empty : IsFσ (∅ : Set X) := IsClosed.isFσ isClosed_empty

theorem isFσ_univ : IsFσ (univ : Set X) := IsClosed.isFσ isClosed_univ

/-- `F_σ` sets are closed under countable unions. -/
theorem IsFσ.iUnion {ι : Sort*} [Countable ι] {s : ι → Set X} (hs : ∀ i, IsFσ (s i)) :
    IsFσ (⋃ i, s i) := by
  rw [← isGδ_compl_iff, compl_iUnion]
  exact IsGδ.iInter fun i => (hs i).isGδ_compl

theorem IsFσ.union {s t : Set X} (hs : IsFσ s) (ht : IsFσ t) : IsFσ (s ∪ t) := by
  rw [← isGδ_compl_iff, compl_union]
  exact hs.isGδ_compl.inter ht.isGδ_compl

/-- `F_σ` sets are closed under finite intersections. -/
theorem IsFσ.inter {s t : Set X} (hs : IsFσ s) (ht : IsFσ t) : IsFσ (s ∩ t) := by
  rw [← isGδ_compl_iff, compl_inter]
  exact hs.isGδ_compl.union ht.isGδ_compl

theorem IsFσ.preimage {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsFσ s) :
    IsFσ (f ⁻¹' s) := by
  rw [← isGδ_compl_iff, ← preimage_compl]
  exact hs.isGδ_compl.preimage hf

/-- In a perfectly normal (e.g. metrizable) space, open sets are `F_σ`. -/
theorem IsOpen.isFσ [PerfectlyNormalSpace X] {s : Set X} (hs : IsOpen s) : IsFσ s :=
  isGδ_compl_iff.1 hs.isClosed_compl.isGδ

/-- In a `T₁` space, countable sets are `F_σ`. -/
theorem Set.Countable.isFσ [T1Space X] {s : Set X} (hs : s.Countable) : IsFσ s :=
  isGδ_compl_iff.1 hs.isGδ_compl

theorem IsFσ.isFσδ {s : Set X} (hs : IsFσ s) : IsFσδ s :=
  ⟨fun _ => s, fun _ => hs, (iInter_const s).symm⟩

theorem isFσδ_univ : IsFσδ (univ : Set X) := isFσ_univ.isFσδ

/-- `F_σδ` sets are closed under countable intersections. -/
theorem IsFσδ.iInter {ι : Sort*} [Countable ι] {s : ι → Set X} (hs : ∀ i, IsFσδ (s i)) :
    IsFσδ (⋂ i, s i) := by
  choose A hA hsA using hs
  cases isEmpty_or_nonempty (PLift ι × ℕ) with
  | inl h =>
    have : IsEmpty ι := ⟨fun i => h.false (PLift.up i, 0)⟩
    exact ⟨fun _ => univ, fun _ => isFσ_univ, by simp⟩
  | inr _ =>
    obtain ⟨g, hg⟩ := exists_surjective_nat (PLift ι × ℕ)
    refine ⟨fun k => A (g k).1.down (g k).2, fun k => hA _ _, ?_⟩
    ext x
    simp only [hsA, mem_iInter]
    constructor
    · intro h k
      exact h _ _
    · intro h i n
      obtain ⟨k, hk⟩ := hg (PLift.up i, n)
      simpa [hk] using h k

theorem IsFσδ.inter {s t : Set X} (hs : IsFσδ s) (ht : IsFσδ t) : IsFσδ (s ∩ t) := by
  rw [inter_eq_iInter]
  exact IsFσδ.iInter (Bool.forall_bool.2 ⟨ht, hs⟩)

/-- `F_σδ` sets are closed under finite unions. -/
theorem IsFσδ.union {s t : Set X} (hs : IsFσδ s) (ht : IsFσδ t) : IsFσδ (s ∪ t) := by
  obtain ⟨P, hP, rfl⟩ := hs
  obtain ⟨R, hR, rfl⟩ := ht
  rw [iInter_union_iInter]
  exact IsFσδ.iInter fun n => IsFσδ.iInter fun m => ((hP n).union (hR m)).isFσδ

theorem IsFσδ.preimage {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsFσδ s) :
    IsFσδ (f ⁻¹' s) := by
  obtain ⟨A, hA, rfl⟩ := hs
  exact ⟨fun n => f ⁻¹' A n, fun n => (hA n).preimage hf, preimage_iInter⟩

/-- In a perfectly normal (e.g. metrizable) space, `G_δ` sets are `F_σδ`. -/
theorem IsGδ.isFσδ [PerfectlyNormalSpace X] {s : Set X} (hs : IsGδ s) : IsFσδ s := by
  obtain ⟨U, hU, rfl⟩ := isGδ_iff_eq_iInter_nat.1 hs
  exact ⟨U, fun n => IsOpen.isFσ (hU n), rfl⟩

theorem IsAmbiguous.preimage {f : X → Y} (hf : Continuous f) {s : Set Y} (hs : IsAmbiguous s) :
    IsAmbiguous (f ⁻¹' s) :=
  ⟨hs.1.preimage hf, hs.2.preimage hf⟩

/-- Homeomorphisms preserve the class `F_σ` (and, by the preimage lemmas, all the other
classes). -/
theorem Homeomorph.isFσ_image (h : X ≃ₜ Y) {s : Set X} (hs : IsFσ s) : IsFσ (h '' s) := by
  rw [h.image_eq_preimage_symm]
  exact hs.preimage h.symm.continuous

theorem Homeomorph.isFσδ_image (h : X ≃ₜ Y) {s : Set X} (hs : IsFσδ s) : IsFσδ (h '' s) := by
  rw [h.image_eq_preimage_symm]
  exact hs.preimage h.symm.continuous

/-! ### Subspaces -/

variable {L : Set X}

/-- `F_σ` sets of a subspace are the traces of `F_σ` sets of the ambient space. -/
theorem isFσ_subtype_iff {E : Set L} : IsFσ E ↔ ∃ P : Set X, IsFσ P ∧ E = Subtype.val ⁻¹' P := by
  constructor
  · rintro ⟨C, hC, rfl⟩
    choose D hD hDC using fun n => isClosed_induced_iff.1 (hC n)
    exact ⟨⋃ n, D n, IsFσ.iUnion fun n => IsClosed.isFσ (hD n), by simp [preimage_iUnion, hDC]⟩
  · rintro ⟨P, hP, rfl⟩
    exact hP.preimage continuous_subtype_val

/-- `G_δ` sets of a subspace are the traces of `G_δ` sets of the ambient space. -/
theorem isGδ_subtype_iff {E : Set L} : IsGδ E ↔ ∃ P : Set X, IsGδ P ∧ E = Subtype.val ⁻¹' P := by
  constructor
  · intro hE
    obtain ⟨U, hU, rfl⟩ := isGδ_iff_eq_iInter_nat.1 hE
    choose V hV hVU using fun n => isOpen_induced_iff.1 (hU n)
    exact ⟨⋂ n, V n, IsGδ.iInter_of_isOpen hV, by simp [preimage_iInter, hVU]⟩
  · rintro ⟨P, hP, rfl⟩
    exact hP.preimage continuous_subtype_val

/-- `F_σδ` sets of a subspace are the traces of `F_σδ` sets of the ambient space. -/
theorem isFσδ_subtype_iff {E : Set L} :
    IsFσδ E ↔ ∃ P : Set X, IsFσδ P ∧ E = Subtype.val ⁻¹' P := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    choose P hP hAP using fun n => isFσ_subtype_iff.1 (hA n)
    exact ⟨⋂ n, P n, ⟨P, hP, rfl⟩, by simp [preimage_iInter, hAP]⟩
  · rintro ⟨P, hP, rfl⟩
    exact hP.preimage continuous_subtype_val

/-- An `F_σδ` subset of an `F_σδ` subspace is `F_σδ` in the ambient space. -/
theorem IsFσδ.of_subtype (hL : IsFσδ L) {E : Set L} (hE : IsFσδ E) :
    IsFσδ (Subtype.val '' E) := by
  obtain ⟨P, hP, rfl⟩ := isFσδ_subtype_iff.1 hE
  rw [Subtype.image_preimage_coe]
  exact hL.inter hP

/-- A `G_δ` subset of a `G_δ` subspace is `G_δ` in the ambient space. -/
theorem IsGδ.of_subtype (hL : IsGδ L) {E : Set L} (hE : IsGδ E) :
    IsGδ (Subtype.val '' E) := by
  obtain ⟨P, hP, rfl⟩ := isGδ_subtype_iff.1 hE
  rw [Subtype.image_preimage_coe]
  exact hL.inter hP

/-- An `F_σ` subset of an `F_σ` subspace is `F_σ` in the ambient space. -/
theorem IsFσ.of_subtype (hL : IsFσ L) {E : Set L} (hE : IsFσ E) :
    IsFσ (Subtype.val '' E) := by
  obtain ⟨P, hP, rfl⟩ := isFσ_subtype_iff.1 hE
  rw [Subtype.image_preimage_coe]
  exact hL.inter hP

end BorelBasic

/-! ## Reduction (blueprint `lem:reduction`, `cor:reduction-finite`, `thm:sierpinski`) -/

section Reduction

variable {X : Type*} [TopologicalSpace X]

/-- If countably many pairwise disjoint `F_σ` sets cover the space, each of them is ambiguous. -/
theorem isAmbiguous_of_iUnion_eq_univ {ι : Type*} [Countable ι] {R : ι → Set X}
    (hR : ∀ i, IsFσ (R i)) (hdisj : Pairwise (Disjoint on R)) (hcov : ⋃ i, R i = univ) (i : ι) :
    IsAmbiguous (R i) := by
  refine ⟨hR i, ?_⟩
  have : (R i)ᶜ = ⋃ (j : ι) (_ : j ≠ i), R j := by
    ext x
    simp only [mem_compl_iff, mem_iUnion, exists_prop]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ i, R i)
      exact ⟨j, fun h => hx (h ▸ hj), hj⟩
    · rintro ⟨j, hji, hj⟩ hi
      exact Set.disjoint_left.1 (hdisj hji) hj hi
  rw [← isFσ_compl_iff, this]
  exact IsFσ.iUnion fun j => IsFσ.iUnion fun _ => hR j

/-- Reduction for countable families: countably many `F_σ` sets `P i` can be shrunk to pairwise
disjoint `F_σ` sets `R i ⊆ P i` with the same union. If the `P i` cover the space, the `R i` are
ambiguous. -/
theorem reduction_countable [PerfectlyNormalSpace X] {ι : Type*} [Countable ι] {P : ι → Set X}
    (hP : ∀ i, IsFσ (P i)) :
    ∃ R : ι → Set X, (∀ i, IsFσ (R i)) ∧ (∀ i, R i ⊆ P i) ∧ Pairwise (Disjoint on R) ∧
      ⋃ i, R i = ⋃ i, P i ∧ (⋃ i, P i = univ → ∀ i, IsAmbiguous (R i)) := by
  classical
  choose F hF hPF using hP
  obtain ⟨key, hkey⟩ := exists_injective_nat (ι × ℕ)
  -- the closed set `F i n`, minus all the closed sets that come earlier in the enumeration `key`
  let G : ι × ℕ → Set X := fun q => F q.1 q.2 \ ⋃ (r : ι × ℕ) (_ : key r < key q), F r.1 r.2
  have hG : ∀ q, IsFσ (G q) := by
    intro q
    have hfin : {r : ι × ℕ | key r < key q}.Finite :=
      (Set.finite_Iio (key q)).preimage hkey.injOn
    have hcl : IsClosed (⋃ (r : ι × ℕ) (_ : key r < key q), F r.1 r.2) := by
      have := hfin.isClosed_biUnion (f := fun r : ι × ℕ => F r.1 r.2) (fun r _ => hF _ _)
      simpa using this
    show IsFσ (_ \ _)
    rw [sdiff_eq]
    exact (IsClosed.isFσ (hF q.1 q.2)).inter (IsOpen.isFσ hcl.isOpen_compl)
  have hsub : ∀ i, (⋃ n, G (i, n)) ⊆ P i := by
    intro i x hx
    obtain ⟨n, hn, -⟩ := mem_iUnion.1 hx
    rw [hPF i]
    exact mem_iUnion.2 ⟨n, hn⟩
  have hdisj : Pairwise (Disjoint on fun i => ⋃ n, G (i, n)) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hx
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hx'
    have hne : key (i, n) ≠ key (j, m) := fun h => hij (congrArg Prod.fst (hkey h))
    rcases lt_or_gt_of_ne hne with h | h
    · exact hm' (mem_iUnion₂.2 ⟨(i, n), h, hn⟩)
    · exact hn' (mem_iUnion₂.2 ⟨(j, m), h, hm⟩)
  have hcov : ⋃ i, ⋃ n, G (i, n) = ⋃ i, P i := by
    apply Subset.antisymm (iUnion_mono hsub)
    intro x hx
    have hex : ∃ k, ∃ q : ι × ℕ, key q = k ∧ x ∈ F q.1 q.2 := by
      obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      rw [hPF i] at hi
      obtain ⟨n, hn⟩ := mem_iUnion.1 hi
      exact ⟨_, (i, n), rfl, hn⟩
    obtain ⟨q, hq, hxq⟩ := Nat.find_spec hex
    refine mem_iUnion.2 ⟨q.1, mem_iUnion.2 ⟨q.2, hxq, ?_⟩⟩
    simp only [mem_iUnion, not_exists]
    intro r hr hxr
    exact Nat.find_min hex (hq ▸ hr) ⟨r, rfl, hxr⟩
  refine ⟨fun i => ⋃ n, G (i, n), fun i => IsFσ.iUnion fun n => hG (i, n), hsub, hdisj, hcov, ?_⟩
  intro huniv
  exact isAmbiguous_of_iUnion_eq_univ (fun i => IsFσ.iUnion fun n => hG (i, n)) hdisj
    (hcov.trans huniv)

/-- **Reduction** (Kaczynski, Diss. Lemma 1). Two `F_σ` sets `E`, `F` can be shrunk to disjoint
`F_σ` sets `A ⊆ E`, `B ⊆ F` with `A ∪ B = E ∪ F`. -/
theorem reduction [PerfectlyNormalSpace X] {E F : Set X} (hE : IsFσ E) (hF : IsFσ F) :
    ∃ A B : Set X, IsFσ A ∧ IsFσ B ∧ A ⊆ E ∧ B ⊆ F ∧ Disjoint A B ∧ A ∪ B = E ∪ F := by
  obtain ⟨R, hR, hRP, hdisj, hcov, -⟩ :=
    reduction_countable (P := fun b : Bool => bif b then E else F) (fun b => by cases b <;> simpa)
  refine ⟨R true, R false, hR true, hR false, hRP true, hRP false, hdisj (by decide), ?_⟩
  rw [union_eq_iUnion (s₁ := E), ← hcov]
  ext x
  simp [Bool.exists_bool, or_comm]

/-- **Finite reduction.** Finitely many `F_σ` sets can be shrunk to pairwise disjoint `F_σ` sets
with the same union; if they cover the space, the shrunken sets are ambiguous. -/
theorem reduction_finite [PerfectlyNormalSpace X] {ι : Type*} [Finite ι] {P : ι → Set X}
    (hP : ∀ i, IsFσ (P i)) :
    ∃ R : ι → Set X, (∀ i, IsFσ (R i)) ∧ (∀ i, R i ⊆ P i) ∧ Pairwise (Disjoint on R) ∧
      ⋃ i, R i = ⋃ i, P i ∧ (⋃ i, P i = univ → ∀ i, IsAmbiguous (R i)) :=
  reduction_countable hP

/-- **Sierpiński.** Between a `G_δ` set and an `F_σ` superset there is an ambiguous set. -/
theorem sierpinski_ambiguous [PerfectlyNormalSpace X] {E F : Set X} (hE : IsGδ E) (hF : IsFσ F)
    (hEF : E ⊆ F) : ∃ K : Set X, IsAmbiguous K ∧ E ⊆ K ∧ K ⊆ F := by
  obtain ⟨A, B, hA, hB, hAE, hBF, hAB, hcov⟩ := reduction (IsGδ.isFσ_compl hE) hF
  have huniv : A ∪ B = univ := by
    rw [hcov, eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ E
    · exact Or.inr (hEF hx)
    · exact Or.inl hx
  have hBc : Bᶜ = A := by
    ext x
    constructor
    · intro hx
      have : x ∈ A ∪ B := huniv ▸ mem_univ x
      exact this.resolve_right hx
    · intro hx hx'
      exact Set.disjoint_left.1 hAB hx hx'
  refine ⟨B, ⟨hB, isFσ_compl_iff.1 (hBc ▸ hA)⟩, ?_, hBF⟩
  intro x hx
  have : x ∈ A ∪ B := huniv ▸ mem_univ x
  exact this.resolve_left fun h => hAE h hx

end Reduction

/-! ## Functions of class `F_σ` (blueprint `lem:baire1-fsigma`, `lem:finite-valued`,
`lem:finite-valued-ops`) -/

section Functions

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

/-- Every Baire-one function into a perfectly normal (e.g. metrizable) space is of class `F_σ`. -/
theorem IsBaireOne.isFσMeasurable [PerfectlyNormalSpace Y] {f : X → Y} (hf : IsBaireOne f) :
    IsFσMeasurable f := by
  obtain ⟨F, hFc, hlim⟩ := hf
  intro U hU
  obtain ⟨C, hC, hUC⟩ := IsOpen.isFσ hU
  choose W hWo hCW hWU using fun n =>
    normal_exists_closure_subset (hC n) hU (hUC ▸ subset_iUnion C n)
  have key : f ⁻¹' U = ⋃ p : ℕ × ℕ, ⋂ (m : ℕ) (_ : p.2 ≤ m), F m ⁻¹' closure (W p.1) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_iInter]
    constructor
    · intro hx
      rw [hUC] at hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 hx
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((hlim x).eventually ((hWo k).mem_nhds (hCW k hk)))
      exact ⟨(k, N), fun m hm => subset_closure (hN m hm)⟩
    · rintro ⟨⟨k, N⟩, h⟩
      exact hWU k (isClosed_closure.mem_of_tendsto (hlim x) (eventually_atTop.2 ⟨N, h⟩))
  rw [key]
  exact IsFσ.iUnion fun p => IsClosed.isFσ
    (isClosed_biInter fun m _ => isClosed_closure.preimage (hFc m))

/-- **Banach's Hilfssatz 3.** The level sets of a finitely valued function of class `F_σ` (into a
`T₁` space) are ambiguous. -/
theorem finiteValued_ambiguous [T1Space Y] {f : X → Y} (hf : IsFσMeasurable f)
    (hfin : (range f).Finite) (a : Y) : IsAmbiguous (f ⁻¹' {a}) := by
  constructor
  · have h1 : f ⁻¹' {a} = f ⁻¹' (range f \ {a})ᶜ := by
      ext x
      simp
    rw [h1]
    exact hf _ (hfin.subset sdiff_subset).isClosed.isOpen_compl
  · rw [← isFσ_compl_iff, ← preimage_compl]
    exact hf _ isOpen_compl_singleton

variable {Y' : Type*} [TopologicalSpace Y'] {Z : Type*} [TopologicalSpace Z]

/-- Any combination `x ↦ φ (f x) (g x)` of two finitely valued functions of class `F_σ` (into `T₁`
spaces) is of class `F_σ`. -/
theorem IsFσMeasurable.comp₂_of_finite [T1Space Y] [T1Space Y'] {f : X → Y} {g : X → Y'}
    (hf : IsFσMeasurable f) (hg : IsFσMeasurable g) (hfin : (range f).Finite)
    (hgfin : (range g).Finite) (φ : Y → Y' → Z) : IsFσMeasurable fun x => φ (f x) (g x) := by
  intro U _
  have key : (fun x => φ (f x) (g x)) ⁻¹' U =
      ⋃ (a : range f) (b : range g) (_ : φ a b ∈ U), f ⁻¹' {(a : Y)} ∩ g ⁻¹' {(b : Y')} := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      exact ⟨⟨f x, x, rfl⟩, ⟨g x, x, rfl⟩, hx, rfl, rfl⟩
    · rintro ⟨a, b, h, ha, hb⟩
      rw [ha, hb]
      exact h
  rw [key]
  have := hfin.to_subtype
  have := hgfin.to_subtype
  exact IsFσ.iUnion fun a => IsFσ.iUnion fun b => IsFσ.iUnion fun _ =>
    (finiteValued_ambiguous hf hfin a).1.inter (finiteValued_ambiguous hg hgfin b).1

omit [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z] in
theorem finite_range_comp₂ {f : X → Y} {g : X → Y'} (hfin : (range f).Finite)
    (hgfin : (range g).Finite) (φ : Y → Y' → Z) : (range fun x => φ (f x) (g x)).Finite := by
  refine ((hfin.prod hgfin).image fun p => φ p.1 p.2).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(f x, g x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩

/-- The sum of two finitely valued functions of class `F_σ` is finitely valued of class `F_σ`. -/
theorem IsFσMeasurable.add_of_finite [Add Y] [T1Space Y] {f g : X → Y} (hf : IsFσMeasurable f)
    (hg : IsFσMeasurable g) (hfin : (range f).Finite) (hgfin : (range g).Finite) :
    IsFσMeasurable (f + g) ∧ (range (f + g)).Finite :=
  ⟨hf.comp₂_of_finite hg hfin hgfin (· + ·), finite_range_comp₂ hfin hgfin (· + ·)⟩

/-- The difference of two finitely valued functions of class `F_σ` is finitely valued of class
`F_σ`. -/
theorem IsFσMeasurable.sub_of_finite [Sub Y] [T1Space Y] {f g : X → Y} (hf : IsFσMeasurable f)
    (hg : IsFσMeasurable g) (hfin : (range f).Finite) (hgfin : (range g).Finite) :
    IsFσMeasurable (f - g) ∧ (range (f - g)).Finite :=
  ⟨hf.comp₂_of_finite hg hfin hgfin (· - ·), finite_range_comp₂ hfin hgfin (· - ·)⟩

end Functions

end TJK
