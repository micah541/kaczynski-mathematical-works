import Mathlib

/-!
# An analytic, non-Borel subset of `ℝ` (`fact:analytic-nonborel`)

Classical proof by diagonalization (Lusin–Souslin). Write `𝒞 = ℕ → Bool` (Cantor space) and
`𝒩 = ℕ → ℕ` (Baire space).

* For a second-countable space `Y` with a fixed countable basis `(B n)`, a code `x : 𝒞` codes the
  open set `⋃_{x n = true} B n`; the set `univOpen Y ⊆ 𝒞 × Y` of pairs `(x, y)` with `y` in the
  coded open set is open, and every open subset of `Y` is a section of it.
* With `Y = 𝒞 × 𝒩`, the complement `F` of `univOpen Y` is a closed set universal for closed subsets
  of `𝒞 × 𝒩`. Since every analytic subset of `𝒞` is the projection of a closed subset of `𝒞 × 𝒩`
  (the graph of a continuous map `𝒩 → 𝒞`), the projection of `F` is universal for analytic subsets
  of `𝒞`.
* The diagonal `D = {x | ∃ w, (x, (x, w)) ∈ F}` is analytic, and its complement is not, so `D` is
  not Borel.
* Transfer to `ℝ` along a continuous injection `𝒞 → ℝ`.
-/

open _root_.Set MeasureTheory TopologicalSpace

namespace TJK.Cube

section AnalyticNonBorel

/-- Instance search does not find this one by itself. -/
local instance polishSpace_cantor' : PolishSpace (ℕ → Bool) :=
  instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace

local instance polishSpace_cantor_baire' : PolishSpace ((ℕ → Bool) × (ℕ → ℕ)) :=
  instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace

variable (Y : Type*) [TopologicalSpace Y] [SecondCountableTopology Y]

/-- A fixed countable basis of a second-countable space. -/
noncomputable def seqBasis' : ℕ → Set Y :=
  (exists_seq_basis Y).choose

theorem isTopologicalBasis_seqBasis' : IsTopologicalBasis (range (seqBasis' Y)) :=
  (exists_seq_basis Y).choose_spec

/-- The universal open set: `x : ℕ → Bool` codes the open set `⋃_{x n = true} seqBasis' Y n`. -/
def univOpen' : Set ((ℕ → Bool) × Y) :=
  {p | ∃ n, p.1 n = true ∧ p.2 ∈ seqBasis' Y n}

theorem isOpen_univOpen' : IsOpen (univOpen' Y) := by
  have h : univOpen' Y = ⋃ n, {x : ℕ → Bool | x n = true} ×ˢ seqBasis' Y n := by
    ext p
    simp [univOpen']
  rw [h]
  refine isOpen_iUnion fun n => IsOpen.prod ?_
    ((isTopologicalBasis_seqBasis' Y).isOpen (mem_range_self n))
  have : IsOpen ((fun x : ℕ → Bool => x n) ⁻¹' {true}) :=
    (continuous_apply n).isOpen_preimage _ (isOpen_discrete _)
  exact this

variable {Y} in
theorem univOpen'_universal {V : Set Y} (hV : IsOpen V) :
    ∃ x : ℕ → Bool, ∀ y, (x, y) ∈ univOpen' Y ↔ y ∈ V := by
  classical
  refine ⟨fun n => decide (seqBasis' Y n ⊆ V), fun y => ?_⟩
  simp only [univOpen', mem_ofPred_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨n, hn, hy⟩
    exact hn hy
  · intro hy
    obtain ⟨t, ⟨n, rfl⟩, hyt, htV⟩ := (isTopologicalBasis_seqBasis' Y).isOpen_iff.1 hV y hy
    exact ⟨n, htV, hyt⟩

/-- Every analytic subset of Cantor space is a section of the projection of the closed set
`(univOpen' (𝒞 × 𝒩))ᶜ`. -/
theorem analytic_universal' {A : Set (ℕ → Bool)} (hA : AnalyticSet A) :
    ∃ x : ℕ → Bool, ∀ z, z ∈ A ↔ ∃ w : ℕ → ℕ, (x, (z, w)) ∉ univOpen' ((ℕ → Bool) × (ℕ → ℕ)) := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · obtain ⟨x, hx⟩ := univOpen'_universal (Y := (ℕ → Bool) × (ℕ → ℕ)) isOpen_univ
    exact ⟨x, fun z => by simp [hx]⟩
  · have hV : IsOpen {p : (ℕ → Bool) × (ℕ → ℕ) | f p.2 ≠ p.1} :=
      isOpen_ne_fun (hf.comp continuous_snd) continuous_fst
    obtain ⟨x, hx⟩ := univOpen'_universal hV
    exact ⟨x, fun z => by simp [hx]⟩

/-- The diagonal set. -/
def diagSet' : Set (ℕ → Bool) :=
  {x | ∃ w : ℕ → ℕ, (x, (x, w)) ∉ univOpen' ((ℕ → Bool) × (ℕ → ℕ))}

theorem analyticSet_diagSet' : AnalyticSet diagSet' := by
  have hS : IsClosed {p : (ℕ → Bool) × (ℕ → ℕ) |
      (p.1, p) ∉ univOpen' ((ℕ → Bool) × (ℕ → ℕ))} :=
    ((isOpen_univOpen' _).preimage (continuous_fst.prodMk continuous_id)).isClosed_compl
  have h : diagSet' = Prod.fst '' {p : (ℕ → Bool) × (ℕ → ℕ) |
      (p.1, p) ∉ univOpen' ((ℕ → Bool) × (ℕ → ℕ))} := by
    ext x
    simp [diagSet']
  rw [h]
  exact hS.analyticSet.image_of_continuous continuous_fst

theorem not_analyticSet_compl_diagSet' : ¬ AnalyticSet diagSet'ᶜ := by
  intro h
  obtain ⟨x, hx⟩ := analytic_universal' h
  have h2 : x ∉ diagSet' ↔ x ∈ diagSet' := hx x
  exact not_iff_self h2

theorem not_measurableSet_diagSet' : ¬ MeasurableSet diagSet' :=
  fun h => not_analyticSet_compl_diagSet' h.compl.analyticSet

theorem exists_analytic_not_borel' :
    ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A := by
  obtain ⟨g, -, hg, hinj⟩ :=
    (PerfectSpace.univ_perfect (α := ℝ)).exists_nat_bool_injection univ_nonempty
  refine ⟨g '' diagSet', analyticSet_diagSet'.image_of_continuous hg, fun h => ?_⟩
  apply not_measurableSet_diagSet'
  have := hg.measurable h
  rwa [hinj.preimage_image] at this

end AnalyticNonBorel

end TJK.Cube
