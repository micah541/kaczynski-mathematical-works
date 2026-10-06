/-
Copyright: the TJK formalization project.

Section B of the blueprint (`paper/sections/B-baire.tex`), subsection "Higher Borel and Baire
classes": the additive and multiplicative classes `P^ξ`, `Q^ξ`, the elementary properties of Baire
classes of all orders, Banach's theorem (imported), countable equivalence of sets, and the lemmas on
intervals and monotone functions of the dissertation (Lemmas 18–22).

As in `TJK.Baire.Basic`, the metric hypotheses of the paper are replaced by `PerfectlyNormalSpace`
where this suffices.
-/
import Mathlib
import TJK.Defs
import TJK.Baire.Basic

open _root_.Set Filter Topology Function TopologicalSpace

namespace TJK

/-! ## The classes `P^ξ` and `Q^ξ` (blueprint `def:additive-classes`) -/

section Classes

variable {X : Type*} [TopologicalSpace X]

/-- `AddMulClass true ξ s` means `s ∈ P^ξ` and `AddMulClass false ξ s` means `s ∈ Q^ξ`: `P^1` are the
open sets, `Q^1` the closed sets, and for `ξ > 1`, `P^ξ` (resp. `Q^ξ`) consists of the countable
unions (resp. intersections) of members of `Q^η` (resp. `P^η`), `η < ξ`. Nothing is in a class of
index `0`. -/
inductive AddMulClass : Bool → Ordinal.{0} → Set X → Prop
  | isOpen {s : Set X} : IsOpen s → AddMulClass true 1 s
  | isClosed {s : Set X} : IsClosed s → AddMulClass false 1 s
  | iUnion {ξ : Ordinal.{0}} {ι : Type} [Countable ι] (η : ι → Ordinal.{0}) (s : ι → Set X) :
      1 < ξ → (∀ i, η i < ξ) → (∀ i, AddMulClass false (η i) (s i)) →
      AddMulClass true ξ (⋃ i, s i)
  | iInter {ξ : Ordinal.{0}} {ι : Type} [Countable ι] (η : ι → Ordinal.{0}) (s : ι → Set X) :
      1 < ξ → (∀ i, η i < ξ) → (∀ i, AddMulClass true (η i) (s i)) →
      AddMulClass false ξ (⋂ i, s i)

/-- The additive class `P^ξ`. -/
def AddClass (ξ : Ordinal.{0}) (s : Set X) : Prop := AddMulClass true ξ s

/-- The multiplicative class `Q^ξ`. -/
def MulClass (ξ : Ordinal.{0}) (s : Set X) : Prop := AddMulClass false ξ s

/-- A function is of class `P^ξ` if preimages of open sets are in `P^ξ`. -/
def IsAddClassMeasurable {Y : Type*} [TopologicalSpace Y] (ξ : Ordinal.{0}) (f : X → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → AddClass ξ (f ⁻¹' U)

end Classes

/-! ## Elementary properties (blueprint `lem:additive-basic`) -/

namespace AddMulClass

variable {X : Type*} [TopologicalSpace X] {b : Bool} {ξ η : Ordinal.{0}} {s t : Set X}

theorem one_le (h : AddMulClass b ξ s) : 1 ≤ ξ := by
  cases h with
  | isOpen _ => exact le_rfl
  | isClosed _ => exact le_rfl
  | iUnion _ _ h1 _ _ => exact h1.le
  | iInter _ _ h1 _ _ => exact h1.le

theorem compl (h : AddMulClass b ξ s) : AddMulClass (!b) ξ sᶜ := by
  induction h with
  | isOpen hs => exact isClosed hs.isClosed_compl
  | isClosed hs => exact isOpen hs.isOpen_compl
  | iUnion η s h1 hη _ ih => rw [compl_iUnion]; exact iInter η _ h1 hη ih
  | iInter η s h1 hη _ ih => rw [compl_iInter]; exact iUnion η _ h1 hη ih

theorem compl_iff : AddMulClass (!b) ξ sᶜ ↔ AddMulClass b ξ s :=
  ⟨fun h => by simpa using h.compl, compl⟩

theorem true_one_iff : AddMulClass true 1 s ↔ IsOpen s := by
  constructor
  · intro h
    cases h with
    | isOpen hs => exact hs
    | iUnion _ _ h1 _ _ => exact absurd h1 (lt_irrefl _)
  · exact isOpen

theorem false_one_iff : AddMulClass false 1 s ↔ IsClosed s := by
  rw [← compl_iff, Bool.not_false, true_one_iff, isOpen_compl_iff]

/-- Members of `P^ξ`, `ξ > 1`, are countable unions of members of lower multiplicative classes. -/
theorem exists_iUnion (h : AddMulClass true ξ s) (hξ : 1 < ξ) :
    ∃ (κ : Type) (_ : Countable κ) (η : κ → Ordinal.{0}) (t : κ → Set X),
      (∀ j, η j < ξ) ∧ (∀ j, AddMulClass false (η j) (t j)) ∧ s = ⋃ j, t j := by
  cases h with
  | isOpen _ => exact absurd hξ (lt_irrefl _)
  | @iUnion _ κ _ η t _ hη ht => exact ⟨κ, inferInstance, η, t, hη, ht, rfl⟩

theorem iUnion_of_countable_type {ι : Type} [Countable ι] {s : ι → Set X}
    (hs : ∀ i, AddMulClass true ξ (s i)) (hξ : 1 ≤ ξ) : AddMulClass true ξ (⋃ i, s i) := by
  rcases hξ.eq_or_lt with rfl | hξ
  · exact isOpen (isOpen_iUnion fun i => true_one_iff.1 (hs i))
  · choose κ hκ η t hη ht hst using fun i => (hs i).exists_iUnion hξ
    have : ⋃ i, s i = ⋃ p : (Σ i, κ i), t p.1 p.2 := by
      rw [iUnion_sigma]
      exact iUnion_congr hst
    rw [this]
    exact iUnion (fun p => η p.1 p.2) _ hξ (fun p => hη _ _) fun p => ht _ _

/-- `P^ξ` is closed under countable unions. -/
theorem iUnion' {ι : Sort*} [Countable ι] {s : ι → Set X}
    (hs : ∀ i, AddMulClass true ξ (s i)) (hξ : 1 ≤ ξ) : AddMulClass true ξ (⋃ i, s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    rw [iUnion_of_empty, ← iUnion_of_empty (ι := Empty) (fun _ => (∅ : Set X))]
    exact iUnion_of_countable_type (fun e => e.elim) hξ
  | inr _ =>
    obtain ⟨g, hg⟩ := exists_surjective_nat ι
    rw [← hg.iUnion_comp]
    exact iUnion_of_countable_type (fun n => hs (g n)) hξ

/-- `Q^ξ` is closed under countable intersections. -/
theorem iInter' {ι : Sort*} [Countable ι] {s : ι → Set X}
    (hs : ∀ i, AddMulClass false ξ (s i)) (hξ : 1 ≤ ξ) : AddMulClass false ξ (⋂ i, s i) := by
  rw [← compl_iff, Bool.not_false, compl_iInter]
  exact iUnion' (fun i => (hs i).compl) hξ

/-- If `η < ξ`, then `P^η ∪ Q^η ⊆ Q^ξ` (resp. `P^ξ`) for the "opposite" class. -/
theorem of_lt_not (h : AddMulClass b η s) (hlt : η < ξ) : AddMulClass (!b) ξ s := by
  have h1 : 1 < ξ := h.one_le.trans_lt hlt
  cases b
  · rw [← iUnion_const (ι := Unit) s]
    exact iUnion (fun _ => η) (fun _ => s) h1 (fun _ => hlt) fun _ => h
  · rw [← iInter_const (ι := Unit) s]
    exact iInter (fun _ => η) (fun _ => s) h1 (fun _ => hlt) fun _ => h

theorem univ (b : Bool) (hξ : 1 ≤ ξ) : AddMulClass b ξ (univ : Set X) := by
  rcases hξ.eq_or_lt with rfl | hlt
  · cases b
    · exact isClosed isClosed_univ
    · exact isOpen isOpen_univ
  · cases b
    · exact of_lt_not (isOpen isOpen_univ) hlt
    · exact of_lt_not (isClosed isClosed_univ) hlt

theorem empty (b : Bool) (hξ : 1 ≤ ξ) : AddMulClass b ξ (∅ : Set X) := by
  rw [← compl_iff, compl_empty]
  exact univ _ hξ

theorem true_of_lt [PerfectlyNormalSpace X] (h : AddMulClass true η s) (hlt : η < ξ) :
    AddMulClass true ξ s := by
  cases h with
  | isOpen hs =>
    obtain ⟨F, hF, rfl⟩ := IsOpen.isFσ hs
    exact iUnion (fun _ => 1) F hlt (fun _ => hlt) fun n => isClosed (hF n)
  | iUnion η' s' h1 hη' hs' =>
    exact iUnion η' s' (h1.trans hlt) (fun i => (hη' i).trans hlt) hs'

/-- **(c)** If `η < ξ`, then `P^η ∪ Q^η ⊆ P^ξ ∩ Q^ξ`. -/
theorem of_lt [PerfectlyNormalSpace X] (h : AddMulClass b η s) (hlt : η < ξ) (b' : Bool) :
    AddMulClass b' ξ s := by
  by_cases hb : b' = b
  · subst hb
    cases b'
    · rw [← compl_iff, Bool.not_false] at h ⊢
      exact true_of_lt h hlt
    · exact true_of_lt h hlt
  · have : b' = !b := by cases b <;> cases b' <;> simp_all
    subst this
    exact h.of_lt_not hlt

theorem mono [PerfectlyNormalSpace X] (h : AddMulClass b η s) (hle : η ≤ ξ) :
    AddMulClass b ξ s := by
  rcases hle.eq_or_lt with rfl | hlt
  · exact h
  · exact h.of_lt hlt b

/-- `Q^ξ` is closed under finite intersections. -/
theorem false_inter (hs : AddMulClass false ξ s) (ht : AddMulClass false ξ t) :
    AddMulClass false ξ (s ∩ t) := by
  rw [inter_eq_iInter]
  exact iInter' (Bool.forall_bool.2 ⟨ht, hs⟩) hs.one_le

/-- `P^ξ` is closed under finite unions. -/
theorem true_union (hs : AddMulClass true ξ s) (ht : AddMulClass true ξ t) :
    AddMulClass true ξ (s ∪ t) := by
  rw [union_eq_iUnion]
  exact iUnion' (Bool.forall_bool.2 ⟨ht, hs⟩) hs.one_le

/-- `P^ξ` is closed under finite intersections. -/
theorem true_inter [PerfectlyNormalSpace X] (hs : AddMulClass true ξ s)
    (ht : AddMulClass true ξ t) : AddMulClass true ξ (s ∩ t) := by
  rcases hs.one_le.eq_or_lt with rfl | hξ
  · exact isOpen ((true_one_iff.1 hs).inter (true_one_iff.1 ht))
  obtain ⟨κ, _, η, A, hη, hA, rfl⟩ := hs.exists_iUnion hξ
  obtain ⟨κ', _, η', B, hη', hB, rfl⟩ := ht.exists_iUnion hξ
  have : (⋃ i, A i) ∩ (⋃ j, B j) = ⋃ p : κ × κ', A p.1 ∩ B p.2 := by
    ext x
    simp only [mem_inter_iff, mem_iUnion, Prod.exists]
    exact ⟨fun ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ => ⟨i, j, hi, hj⟩, fun ⟨i, j, hi, hj⟩ => ⟨⟨i, hi⟩, ⟨j, hj⟩⟩⟩
  rw [this]
  exact iUnion (fun p => max (η p.1) (η' p.2)) _ hξ (fun p => max_lt (hη _) (hη' _))
    fun p => false_inter ((hA _).mono (le_max_left _ _)) ((hB _).mono (le_max_right _ _))

/-- `Q^ξ` is closed under finite unions. -/
theorem false_union [PerfectlyNormalSpace X] (hs : AddMulClass false ξ s)
    (ht : AddMulClass false ξ t) : AddMulClass false ξ (s ∪ t) := by
  rw [← compl_iff, Bool.not_false, compl_union]
  exact true_inter hs.compl ht.compl

/-- **(d)** `P^2` is the class of `F_σ` sets. -/
theorem true_two_iff : AddMulClass true 2 s ↔ IsFσ s := by
  constructor
  · intro h
    obtain ⟨κ, _, η, t, hη, ht, rfl⟩ := h.exists_iUnion one_lt_two
    have hcl : ∀ j, IsClosed (t j) := by
      intro j
      have h1 : η j ≤ 1 := by
        have := hη j
        rw [← one_add_one_eq_two] at this
        exact Order.lt_add_one_iff.1 this
      have : η j = 1 := le_antisymm h1 (ht j).one_le
      rw [← false_one_iff, ← this]
      exact ht j
    exact IsFσ.iUnion fun j => IsClosed.isFσ (hcl j)
  · rintro ⟨F, hF, rfl⟩
    exact iUnion (fun _ => 1) F one_lt_two (fun _ => one_lt_two) fun n => isClosed (hF n)

/-- **(d)** `Q^2` is the class of `G_δ` sets. -/
theorem false_two_iff : AddMulClass false 2 s ↔ IsGδ s := by
  rw [← compl_iff, Bool.not_false, true_two_iff, isFσ_compl_iff]

/-- **(e)** Continuous preimages preserve each class. -/
theorem preimage {Y : Type*} [TopologicalSpace Y] {f : Y → X} (hf : Continuous f)
    (h : AddMulClass b ξ s) : AddMulClass b ξ (f ⁻¹' s) := by
  induction h with
  | isOpen hs => exact isOpen (hs.preimage hf)
  | isClosed hs => exact isClosed (hs.preimage hf)
  | iUnion η s h1 hη _ ih => rw [preimage_iUnion]; exact iUnion η _ h1 hη ih
  | iInter η s h1 hη _ ih => rw [preimage_iInter]; exact iInter η _ h1 hη ih

/-- **(f)** The classes of a subspace are the traces of the classes of the ambient space. -/
theorem subtype_iff {L : Set X} {E : Set L} :
    AddMulClass b ξ E ↔ ∃ D : Set X, AddMulClass b ξ D ∧ E = Subtype.val ⁻¹' D := by
  constructor
  · intro h
    induction h with
    | isOpen hs =>
      obtain ⟨D, hD, rfl⟩ := isOpen_induced_iff.1 hs
      exact ⟨D, isOpen hD, rfl⟩
    | isClosed hs =>
      obtain ⟨D, hD, rfl⟩ := isClosed_induced_iff.1 hs
      exact ⟨D, isClosed hD, rfl⟩
    | iUnion η s h1 hη _ ih =>
      choose D hD hsD using ih
      exact ⟨⋃ i, D i, iUnion η D h1 hη hD, by rw [preimage_iUnion]; exact iUnion_congr hsD⟩
    | iInter η s h1 hη _ ih =>
      choose D hD hsD using ih
      exact ⟨⋂ i, D i, iInter η D h1 hη hD, by rw [preimage_iInter]; exact iInter_congr hsD⟩
  · rintro ⟨D, hD, rfl⟩
    exact hD.preimage continuous_subtype_val

/-- **(g)** Every member of every class is a Borel set. -/
theorem measurableSet [MeasurableSpace X] [OpensMeasurableSpace X] (h : AddMulClass b ξ s) :
    MeasurableSet s := by
  induction h with
  | isOpen hs => exact hs.measurableSet
  | isClosed hs => exact hs.measurableSet
  | iUnion η s h1 hη _ ih => exact MeasurableSet.iUnion ih
  | iInter η s h1 hη _ ih => exact MeasurableSet.iInter ih

end AddMulClass

section AddClassLemmas

variable {X : Type*} [TopologicalSpace X] {ξ η : Ordinal.{0}} {s t : Set X}

/-- **(a)** `E ∈ Q^ξ` iff its complement is in `P^ξ`. -/
theorem mulClass_iff_compl : MulClass ξ s ↔ AddClass ξ sᶜ :=
  (AddMulClass.compl_iff (b := false)).symm

theorem addClass_iff_compl : AddClass ξ s ↔ MulClass ξ sᶜ :=
  (AddMulClass.compl_iff (b := true)).symm

theorem AddClass.one_le (h : AddClass ξ s) : 1 ≤ ξ := AddMulClass.one_le h

theorem MulClass.one_le (h : MulClass ξ s) : 1 ≤ ξ := AddMulClass.one_le h

theorem addClass_one_iff : AddClass 1 s ↔ IsOpen s := AddMulClass.true_one_iff

theorem mulClass_one_iff : MulClass 1 s ↔ IsClosed s := AddMulClass.false_one_iff

/-- **(d)** `P^2 = F_σ`. -/
theorem addClass_two_iff : AddClass 2 s ↔ IsFσ s := AddMulClass.true_two_iff

/-- **(d)** `Q^2 = G_δ`. -/
theorem mulClass_two_iff : MulClass 2 s ↔ IsGδ s := AddMulClass.false_two_iff

/-- **(c)** -/
theorem AddClass.addClass_of_lt [PerfectlyNormalSpace X] (h : AddClass η s) (hlt : η < ξ) :
    AddClass ξ s := AddMulClass.of_lt h hlt true

theorem AddClass.mulClass_of_lt (h : AddClass η s) (hlt : η < ξ) : MulClass ξ s :=
  AddMulClass.of_lt_not h hlt

theorem MulClass.addClass_of_lt (h : MulClass η s) (hlt : η < ξ) : AddClass ξ s :=
  AddMulClass.of_lt_not h hlt

theorem MulClass.mulClass_of_lt [PerfectlyNormalSpace X] (h : MulClass η s) (hlt : η < ξ) :
    MulClass ξ s := AddMulClass.of_lt h hlt false

theorem AddClass.mono [PerfectlyNormalSpace X] (h : AddClass η s) (hle : η ≤ ξ) : AddClass ξ s :=
  AddMulClass.mono h hle

theorem MulClass.mono [PerfectlyNormalSpace X] (h : MulClass η s) (hle : η ≤ ξ) : MulClass ξ s :=
  AddMulClass.mono h hle

/-- **(b)** `P^ξ` is closed under countable unions (`ξ ≥ 1` is needed for empty unions). -/
theorem AddClass.iUnion {ι : Sort*} [Countable ι] {s : ι → Set X} (hs : ∀ i, AddClass ξ (s i))
    (hξ : 1 ≤ ξ) : AddClass ξ (⋃ i, s i) := AddMulClass.iUnion' hs hξ

/-- **(b)** `Q^ξ` is closed under countable intersections. -/
theorem MulClass.iInter {ι : Sort*} [Countable ι] {s : ι → Set X} (hs : ∀ i, MulClass ξ (s i))
    (hξ : 1 ≤ ξ) : MulClass ξ (⋂ i, s i) := AddMulClass.iInter' hs hξ

theorem AddClass.union (hs : AddClass ξ s) (ht : AddClass ξ t) : AddClass ξ (s ∪ t) :=
  AddMulClass.true_union hs ht

theorem MulClass.inter (hs : MulClass ξ s) (ht : MulClass ξ t) : MulClass ξ (s ∩ t) :=
  AddMulClass.false_inter hs ht

theorem AddClass.inter [PerfectlyNormalSpace X] (hs : AddClass ξ s) (ht : AddClass ξ t) :
    AddClass ξ (s ∩ t) := AddMulClass.true_inter hs ht

theorem MulClass.union [PerfectlyNormalSpace X] (hs : MulClass ξ s) (ht : MulClass ξ t) :
    MulClass ξ (s ∪ t) := AddMulClass.false_union hs ht

theorem addClass_empty (hξ : 1 ≤ ξ) : AddClass ξ (∅ : Set X) := AddMulClass.empty true hξ

theorem addClass_univ (hξ : 1 ≤ ξ) : AddClass ξ (univ : Set X) := AddMulClass.univ true hξ

theorem mulClass_empty (hξ : 1 ≤ ξ) : MulClass ξ (∅ : Set X) := AddMulClass.empty false hξ

theorem mulClass_univ (hξ : 1 ≤ ξ) : MulClass ξ (univ : Set X) := AddMulClass.univ false hξ

/-- **(e)** -/
theorem AddClass.preimage {Y : Type*} [TopologicalSpace Y] {f : Y → X} (hf : Continuous f)
    (h : AddClass ξ s) : AddClass ξ (f ⁻¹' s) := AddMulClass.preimage hf h

theorem MulClass.preimage {Y : Type*} [TopologicalSpace Y] {f : Y → X} (hf : Continuous f)
    (h : MulClass ξ s) : MulClass ξ (f ⁻¹' s) := AddMulClass.preimage hf h

/-- **(f)** `P^ξ(L) = {D ∩ L : D ∈ P^ξ(M)}`. -/
theorem AddClass.subtype_iff {L : Set X} {E : Set L} :
    AddClass ξ E ↔ ∃ D : Set X, AddClass ξ D ∧ E = Subtype.val ⁻¹' D :=
  AddMulClass.subtype_iff

theorem MulClass.subtype_iff {L : Set X} {E : Set L} :
    MulClass ξ E ↔ ∃ D : Set X, MulClass ξ D ∧ E = Subtype.val ⁻¹' D :=
  AddMulClass.subtype_iff

/-- **(g)** -/
theorem AddClass.measurableSet [MeasurableSpace X] [OpensMeasurableSpace X] (h : AddClass ξ s) :
    MeasurableSet s := AddMulClass.measurableSet h

theorem MulClass.measurableSet [MeasurableSpace X] [OpensMeasurableSpace X] (h : MulClass ξ s) :
    MeasurableSet s := AddMulClass.measurableSet h

/-- A function of class `P^ξ` is Borel measurable. -/
theorem IsAddClassMeasurable.measurable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y}
    (hf : IsAddClassMeasurable ξ f) : Measurable f :=
  measurable_of_isOpen fun U hU => (hf U hU).measurableSet

end AddClassLemmas

/-! ## Baire classes of all orders (blueprint `lem:baire-precomp`, `lem:baire-imp-class`) -/

section BaireClasses

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

/-- Precomposition with a continuous map keeps the Baire class. -/
theorem BaireClass.comp_continuous {Z : Type*} [TopologicalSpace Z] {ξ : Ordinal.{0}} {f : X → Y}
    (hf : BaireClass ξ f) {g : Z → X} (hg : Continuous g) : BaireClass ξ (f ∘ g) := by
  induction hf with
  | zero hc => exact .zero (hc.comp hg)
  | @lim ξ f η F hξ hη _ hlim ih => exact .lim η (fun n => F n ∘ g) hξ hη ih fun z => hlim (g z)

/-- Restrictions to subspaces keep the Baire class. -/
theorem BaireClass.restrict {ξ : Ordinal.{0}} {f : X → Y} (hf : BaireClass ξ f) (s : Set X) :
    BaireClass ξ (s.restrict f) :=
  hf.comp_continuous continuous_subtype_val

/-- The Baire classes increase with the index. -/
theorem BaireClass.mono {ξ ξ' : Ordinal.{0}} {f : X → Y} (hf : BaireClass ξ f) (h : ξ ≤ ξ') :
    BaireClass ξ' f := by
  rcases h.eq_or_lt with rfl | hlt
  · exact hf
  · exact .lim (fun _ => ξ) (fun _ => f) (zero_le.trans_lt hlt) (fun _ => hlt) (fun _ => hf)
      fun _ => tendsto_const_nhds

/-- A function of Baire class `ξ` is of class `P^{ξ+1}`. -/
theorem BaireClass.addClass_preimage [PerfectlyNormalSpace X] [PerfectlyNormalSpace Y]
    {ξ : Ordinal.{0}} {f : X → Y} (hf : BaireClass ξ f) : IsAddClassMeasurable (ξ + 1) f := by
  induction hf with
  | zero hc =>
    intro U hU
    rw [zero_add]
    exact addClass_one_iff.2 (hU.preimage hc)
  | @lim ξ f η F hξ hη _ hlim ih =>
    intro U hU
    obtain ⟨C, hC, hUC⟩ := IsOpen.isFσ hU
    choose W hWo hCW hWU using fun n =>
      normal_exists_closure_subset (hC n) hU (hUC ▸ subset_iUnion C n)
    have key : f ⁻¹' U = ⋃ p : ℕ × ℕ, ⋂ m, ⋂ (_ : p.2 ≤ m), F m ⁻¹' closure (W p.1) := by
      ext x
      simp only [mem_preimage, mem_iUnion, mem_iInter]
      constructor
      · intro hx
        rw [hUC] at hx
        obtain ⟨k, hk⟩ := mem_iUnion.1 hx
        obtain ⟨N, hN⟩ :=
          eventually_atTop.1 ((hlim x).eventually ((hWo k).mem_nhds (hCW k hk)))
        exact ⟨(k, N), fun m hm => subset_closure (hN m hm)⟩
      · rintro ⟨⟨k, N⟩, h⟩
        exact hWU k (isClosed_closure.mem_of_tendsto (hlim x) (eventually_atTop.2 ⟨N, h⟩))
    have h1 : 1 ≤ ξ := Order.one_le_iff_pos.2 hξ
    have hQ : ∀ k m, MulClass ξ (F m ⁻¹' closure (W k)) := by
      intro k m
      have := ih m _ (isClosed_closure (s := W k)).isOpen_compl
      rw [preimage_compl, ← mulClass_iff_compl] at this
      exact this.mono (Order.add_one_le_of_lt (hη m))
    rw [key]
    exact AddMulClass.iUnion (fun _ => ξ) _ (h1.trans_lt (lt_add_one ξ)) (fun _ => lt_add_one ξ)
      fun p => MulClass.iInter (fun m => MulClass.iInter (fun _ => hQ p.1 m) h1) h1

/-- Functions of any Baire class are Borel measurable. -/
theorem BaireClass.measurable [PerfectlyNormalSpace X] [PerfectlyNormalSpace Y] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] {ξ : Ordinal.{0}} {f : X → Y}
    (hf : BaireClass ξ f) : Measurable f :=
  hf.addClass_preimage.measurable

end BaireClasses

/-! ## Imported facts (blueprint `fact:banach`, `fact:borel-baire`) -/

/-- **Banach (1931).** For `ξ ≥ 2`, a function of class `P^{ξ+1}` from a metric space to a
separable, arcwise connected metric space is of Baire class `ξ`. Imported. -/
theorem banach_baireClass_of_addClass {M Y : Type*} [MetricSpace M] [MetricSpace Y]
    [SeparableSpace Y] [PathConnectedSpace Y] {ξ : Ordinal.{0}} (hξ : 2 ≤ ξ) {f : M → Y}
    (hf : IsAddClassMeasurable (ξ + 1) f) : BaireClass ξ f := by
  sorry

/-- **Lebesgue–Hausdorff–Banach.** Every Borel measurable function from a metric space to a
separable, arcwise connected metric space is of Baire class `ξ` for some countable ordinal `ξ`.
Imported. -/
theorem borel_measurable_exists_baireClass {M Y : Type*} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M] [MetricSpace Y] [SeparableSpace Y] [PathConnectedSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : M → Y} (hf : Measurable f) :
    ∃ ξ : Ordinal.{0}, ξ < Ordinal.omega 1 ∧ BaireClass ξ f := by
  sorry

/-! ## Countable equivalence (blueprint `lem:equiv`) -/

section CountablyEquiv

variable {α : Type*}

/-- `A ≈ B`: the sets `A \ B` and `B \ A` are countable. -/
def CountablyEquiv (A B : Set α) : Prop :=
  (A \ B).Countable ∧ (B \ A).Countable

namespace CountablyEquiv

variable {A B C E : Set α}

theorem refl (A : Set α) : CountablyEquiv A A := by
  simp [CountablyEquiv]

theorem symm (h : CountablyEquiv A B) : CountablyEquiv B A := And.symm h

theorem trans (h : CountablyEquiv A B) (h' : CountablyEquiv B C) : CountablyEquiv A C := by
  have key : ∀ {A B C : Set α}, A \ C ⊆ A \ B ∪ B \ C := by
    intro A B C x hx
    by_cases hB : x ∈ B
    · exact Or.inr ⟨hB, hx.2⟩
    · exact Or.inl ⟨hx.1, hB⟩
  exact ⟨(h.1.union h'.1).mono key, (h'.2.union h.2).mono key⟩

theorem equivalence : Equivalence (@CountablyEquiv α) :=
  ⟨refl, symm, trans⟩

theorem diff (h : CountablyEquiv A E) (S : Set α) : CountablyEquiv (S \ A) (S \ E) := by
  refine ⟨h.2.mono ?_, h.1.mono ?_⟩ <;>
  · intro x hx
    exact ⟨of_not_not fun h' => hx.2 ⟨hx.1.1, h'⟩, hx.1.2⟩

theorem iInter {ι : Sort*} [Countable ι] {A E : ι → Set α}
    (h : ∀ i, CountablyEquiv (A i) (E i)) : CountablyEquiv (⋂ i, A i) (⋂ i, E i) := by
  refine ⟨(countable_iUnion fun i => (h i).1).mono ?_,
    (countable_iUnion fun i => (h i).2).mono ?_⟩ <;>
  · intro x hx
    obtain ⟨i, hi⟩ := not_forall.1 fun h' => hx.2 (mem_iInter.2 h')
    exact mem_iUnion.2 ⟨i, mem_iInter.1 hx.1 i, hi⟩

theorem iUnion {ι : Sort*} [Countable ι] {A E : ι → Set α}
    (h : ∀ i, CountablyEquiv (A i) (E i)) : CountablyEquiv (⋃ i, A i) (⋃ i, E i) := by
  refine ⟨(countable_iUnion fun i => (h i).1).mono ?_,
    (countable_iUnion fun i => (h i).2).mono ?_⟩ <;>
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx.1
    exact mem_iUnion.2 ⟨i, hi, fun h' => hx.2 (mem_iUnion.2 ⟨i, h'⟩)⟩

theorem inter {A' E' : Set α} (h : CountablyEquiv A E) (h' : CountablyEquiv A' E') :
    CountablyEquiv (A ∩ A') (E ∩ E') := by
  rw [inter_eq_iInter, inter_eq_iInter (s₁ := E)]
  exact iInter (Bool.forall_bool.2 ⟨h', h⟩)

theorem union {A' E' : Set α} (h : CountablyEquiv A E) (h' : CountablyEquiv A' E') :
    CountablyEquiv (A ∪ A') (E ∪ E') := by
  rw [union_eq_iUnion, union_eq_iUnion (s₁ := E)]
  exact iUnion (Bool.forall_bool.2 ⟨h', h⟩)

end CountablyEquiv

end CountablyEquiv

/-! ## Intervals and one-sided limit points (blueprint `lem:intervals-open`, `lem:two-sided`) -/

section Intervals

/-- The points of `s ⊆ ℝ` with a gap of `s` immediately to their right form a countable set. -/
theorem countable_isolated_right (s : Set ℝ) :
    {x | x ∈ s ∧ ∃ y, x < y ∧ Disjoint (Ioo x y) s}.Countable := by
  refine (countable_setOfPred_isolated_right_within (s := s)).mono ?_
  rintro x ⟨hx, y, hxy, hd⟩
  refine ⟨hx, empty_mem_iff_bot.1 (mem_nhdsWithin.2 ⟨Iio y, isOpen_Iio, hxy, ?_⟩)⟩
  rintro z ⟨hzy, hzs, hxz⟩
  exact Set.disjoint_left.1 hd ⟨hxz, hzy⟩ hzs

/-- The points of `s ⊆ ℝ` with a gap of `s` immediately to their left form a countable set. -/
theorem countable_isolated_left (s : Set ℝ) :
    {x | x ∈ s ∧ ∃ y, y < x ∧ Disjoint (Ioo y x) s}.Countable := by
  refine (countable_setOfPred_isolated_left_within (s := s)).mono ?_
  rintro x ⟨hx, y, hxy, hd⟩
  refine ⟨hx, empty_mem_iff_bot.1 (mem_nhdsWithin.2 ⟨Ioi y, isOpen_Ioi, hxy, ?_⟩)⟩
  rintro z ⟨hzy, hzs, hxz⟩
  exact Set.disjoint_left.1 hd ⟨hzy, hxz⟩ hzs

/-- **Dissertation Lemma 19 / MMJ Lemma 1** (real version). If `𝓘` is a family of nondegenerate
intervals of `ℝ`, then `⋃ 𝓘 \ ⋃_{I ∈ 𝓘} interior I` is countable. -/
theorem countable_biUnion_diff_interior_real {𝓘 : Set (Set ℝ)}
    (h𝓘 : ∀ I ∈ 𝓘, I.OrdConnected ∧ I.Nontrivial) :
    ((⋃ I ∈ 𝓘, I) \ ⋃ I ∈ 𝓘, interior I).Countable := by
  set U := ⋃ I ∈ 𝓘, interior I
  refine ((countable_isolated_right Uᶜ).union (countable_isolated_left Uᶜ)).mono ?_
  rintro x ⟨hx, hxU⟩
  obtain ⟨I, hI, hxI⟩ := mem_iUnion₂.1 hx
  obtain ⟨y, hyI, hyx⟩ := (h𝓘 I hI).2.exists_ne x
  have hsub : ∀ {a b}, a ∈ I → b ∈ I → Disjoint (Ioo a b) Uᶜ := by
    intro a b ha hb
    rw [Set.disjoint_compl_right_iff_subset, ← interior_Icc]
    exact (interior_mono ((h𝓘 I hI).1.out ha hb)).trans (subset_biUnion_of_mem hI)
  rcases hyx.lt_or_gt with h | h
  · exact Or.inr ⟨hxU, y, h, hsub hyI hxI⟩
  · exact Or.inl ⟨hxU, y, h, hsub hxI hyI⟩

/-- In particular every union of nondegenerate intervals is `≈` an open set. -/
theorem exists_isOpen_countablyEquiv_real {𝓘 : Set (Set ℝ)}
    (h𝓘 : ∀ I ∈ 𝓘, I.OrdConnected ∧ I.Nontrivial) :
    ∃ O : Set ℝ, IsOpen O ∧ CountablyEquiv (⋃ I ∈ 𝓘, I) O := by
  refine ⟨⋃ I ∈ 𝓘, interior I, isOpen_biUnion fun _ _ => isOpen_interior,
    countable_biUnion_diff_interior_real h𝓘, ?_⟩
  rw [sdiff_eq_empty.2 (biUnion_mono subset_rfl fun _ _ => interior_subset)]
  exact countable_empty

/-- The image version of `countable_biUnion_diff_interior_real`: for parameter intervals
`[a, b]`, `a < b`, and any map `f` on `ℝ`, the points of `⋃ f '' [a, b]` not in `⋃ f '' (a, b)` form
a countable set. -/
theorem countable_biUnion_image_diff {α : Type*} (f : ℝ → α) {S : Set (ℝ × ℝ)}
    (hS : ∀ p ∈ S, p.1 < p.2) :
    ((⋃ p ∈ S, f '' Icc p.1 p.2) \ ⋃ p ∈ S, f '' Ioo p.1 p.2).Countable := by
  have h := countable_biUnion_diff_interior_real (𝓘 := (fun p : ℝ × ℝ => Icc p.1 p.2) '' S)
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨ordConnected_Icc, ⟨p.1, left_mem_Icc.2 (hS p hp).le, p.2, right_mem_Icc.2 (hS p hp).le,
        (hS p hp).ne⟩⟩)
  simp only [biUnion_image, interior_Icc] at h
  refine (h.image f).mono ?_
  rintro z ⟨hz, hzU⟩
  obtain ⟨p, hp, t, ht, rfl⟩ := mem_iUnion₂.1 hz
  refine ⟨t, ⟨mem_iUnion₂.2 ⟨p, hp, ht⟩, fun htU => hzU ?_⟩, rfl⟩
  obtain ⟨q, hq, htq⟩ := mem_iUnion₂.1 htU
  exact mem_iUnion₂.2 ⟨q, hq, t, htq, rfl⟩

/-- **Dissertation Lemma 19 / MMJ Lemma 1** (circle version). For a family of nondegenerate closed
arcs `{e^{it} : a ≤ t ≤ b}`, `a < b`, of the unit circle, the points of their union that lie in no
open arc `{e^{it} : a < t < b}` form a countable set. -/
theorem countable_biUnion_diff_interior_circle {S : Set (ℝ × ℝ)} (hS : ∀ p ∈ S, p.1 < p.2) :
    ((⋃ p ∈ S, (fun t : ℝ => Complex.exp (t * Complex.I)) '' Icc p.1 p.2) \
      ⋃ p ∈ S, (fun t : ℝ => Complex.exp (t * Complex.I)) '' Ioo p.1 p.2).Countable :=
  countable_biUnion_image_diff _ hS

/-- **Two-sided limit points.** For `F ⊆ ℝ`, the points of `closure F` that are not two-sided limit
points of `F` form a countable set. -/
theorem countable_not_twoSided (F : Set ℝ) :
    {x | x ∈ closure F ∧ ¬ ((∀ r > 0, (Ioo (x - r) x ∩ F).Nonempty) ∧
      ∀ r > 0, (Ioo x (x + r) ∩ F).Nonempty)}.Countable := by
  refine ((countable_isolated_right (closure F)).union
    (countable_isolated_left (closure F))).mono ?_
  rintro x ⟨hx, hnot⟩
  rcases not_and_or.1 hnot with h | h <;> obtain ⟨r, hr, hrF⟩ := not_forall₂.1 h <;>
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hrF
  · exact Or.inr ⟨hx, x - r, by linarith, hrF.closure_right isOpen_Ioo⟩
  · exact Or.inl ⟨hx, x + r, by linarith, hrF.closure_right isOpen_Ioo⟩

end Intervals

/-! ## Monotone functions (blueprint `lem:monotone-extend`, `lem:monotone-compose`) -/

section Monotone

/-- **Dissertation Lemma 20.** A function weakly increasing on `E ⊆ ℝ` with `|x - h x| ≤ 1` on `E`
extends to a weakly increasing function on `ℝ`. -/
theorem MonotoneOn.exists_monotone_extension_of_dist_le {E : Set ℝ} {h : ℝ → ℝ}
    (hmono : MonotoneOn h E) (hdist : ∀ x ∈ E, |x - h x| ≤ 1) :
    ∃ h₁ : ℝ → ℝ, Monotone h₁ ∧ EqOn h₁ h E := by
  let A : ℝ → Set ℝ := fun x => insert (x - 1) (h '' (E ∩ Iic x))
  have hbdd : ∀ x, BddAbove (A x) := by
    intro x
    refine ⟨x + 1, ?_⟩
    rintro _ (rfl | ⟨t, ⟨htE, htx⟩, rfl⟩)
    · linarith
    · have := (abs_sub_le_iff.1 (hdist t htE)).2
      simp only [mem_Iic] at htx
      linarith
  refine ⟨fun x => sSup (A x), ?_, ?_⟩
  · intro x y hxy
    refine csSup_le (insert_nonempty _ _) ?_
    rintro _ (rfl | ⟨t, ⟨htE, htx⟩, rfl⟩)
    · exact le_trans (by linarith) (le_csSup (hbdd y) (mem_insert _ _))
    · exact le_csSup (hbdd y) (mem_insert_of_mem _ ⟨t, ⟨htE, le_trans htx hxy⟩, rfl⟩)
  · intro x hx
    refine IsGreatest.csSup_eq ⟨mem_insert_of_mem _ ⟨x, ⟨hx, mem_Iic.2 le_rfl⟩, rfl⟩, ?_⟩
    rintro _ (rfl | ⟨t, ⟨htE, htx⟩, rfl⟩)
    · have := (abs_sub_le_iff.1 (hdist x hx)).1
      linarith
    · exact hmono htE hx htx

/-- **Dissertation Lemma 21.** If `f : ℝ → Y` is of Baire class `ξ` and `h : ℝ → ℝ` is weakly
increasing, then `f ∘ h` is of Baire class `ξ` off a countable set. -/
theorem BaireClass.comp_monotone {Y : Type*} [TopologicalSpace Y] {ξ : Ordinal.{0}} {f : ℝ → Y}
    (hf : BaireClass ξ f) {h : ℝ → ℝ} (hh : Monotone h) :
    ∃ N : Set ℝ, N.Countable ∧ BaireClass ξ ((Nᶜ).restrict (f ∘ h)) := by
  refine ⟨{x | ¬ContinuousAt h x}, hh.countable_not_continuousAt, ?_⟩
  have hc : Continuous ((({x | ¬ContinuousAt h x})ᶜ).restrict h) :=
    continuousOn_iff_continuous_domRestrict.1
      (continuousOn_of_forall_continuousAt fun x hx => not_not.1 hx)
  exact hf.comp_continuous hc

end Monotone

/-! ## A criterion for Baire class `ξ` (blueprint `lem:baire-criterion`) -/

/-- **Dissertation Lemma 22.** Let `Y` be a separable arcwise connected metric space and `ξ ≥ 2`.
If for every open `U ⊆ Y` some `T ∈ P^{ξ+1}(E)` satisfies `φ⁻¹(U) ⊆ T ⊆ φ⁻¹(closure U)`, then `φ`
is of Baire class `ξ`. -/
theorem baireClass_of_sandwich {E Y : Type*} [MetricSpace E] [MetricSpace Y] [SeparableSpace Y]
    [PathConnectedSpace Y] {ξ : Ordinal.{0}} (hξ : 2 ≤ ξ) {φ : E → Y}
    (h : ∀ U : Set Y, IsOpen U → ∃ T : Set E, AddClass (ξ + 1) T ∧ φ ⁻¹' U ⊆ T ∧
      T ⊆ φ ⁻¹' closure U) : BaireClass ξ φ := by
  refine banach_baireClass_of_addClass hξ fun W hW => ?_
  choose T hT hUT hTU using h
  have hbasis := isBasis_countableBasis Y
  have hcount : {B ∈ countableBasis Y | closure B ⊆ W}.Countable :=
    (countable_countableBasis Y).mono (sep_subset _ _)
  have := hcount.to_subtype
  have key : φ ⁻¹' W = ⋃ B : {B ∈ countableBasis Y | closure B ⊆ W},
      T B (hbasis.isOpen B.2.1) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨B, hB, hxB, hBW⟩ := hbasis.exists_closure_subset (hW.mem_nhds hx)
      exact mem_iUnion.2 ⟨⟨B, hB, hBW⟩, hUT _ _ hxB⟩
    · exact iUnion_subset fun B => (hTU _ _).trans (preimage_mono B.2.2)
  rw [key]
  have h1 : (1 : Ordinal.{0}) ≤ ξ + 1 := le_add_self
  exact AddClass.iUnion (fun B => hT _ _) h1

end TJK
