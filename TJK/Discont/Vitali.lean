/-
Vitali's non-measurable set (blueprint `fact:vitali`, proved here) and the corollary
`cor:nonmeasurable` of dissertation Theorem 10.
-/
import Mathlib
import TJK.Defs
import TJK.Discont.Segments

open MeasureTheory Filter Topology

namespace TJK.Discont

/-- The additive subgroup `ℚ ⊆ ℝ`. -/
private noncomputable def ratSubgroup : AddSubgroup ℝ := (Rat.castHom ℝ).toAddMonoidHom.range

private lemma mem_ratSubgroup {x : ℝ} : x ∈ ratSubgroup ↔ ∃ q : ℚ, (q : ℝ) = x := by
  simp [ratSubgroup]

private lemma exists_rep (c : ℝ ⧸ ratSubgroup) :
    ∃ x ∈ _root_.Set.Icc (0 : ℝ) 1, (x : ℝ ⧸ ratSubgroup) = c := by
  induction c using QuotientAddGroup.induction_on with
  | H y =>
    refine ⟨Int.fract y, ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩, ?_⟩
    refine QuotientAddGroup.eq.2 (mem_ratSubgroup.2 ⟨((⌊y⌋ : ℤ) : ℚ), ?_⟩)
    rw [Int.fract]; push_cast; ring

theorem exists_ae_zero_boundaryFn' {Y : Type*} [MetricSpace Y] (y₀ : Y) (φ : ℝ → Y) :
    ∃ f : ℂ → Y, (∀ᵐ z ∂volume, f z = y₀) ∧
      IsBoundaryFunction upper f realAxis (fun z => φ z.re) := by
  classical
  obtain ⟨γ, hγ, hdisj, hnull⟩ := exists_disjoint_null_arcs'
  have huniq : ∀ (w : ℂ) (x : ℝ) (h : ∃ x' : ℝ, w ∈ γ x'), w ∈ γ x → h.choose = x := by
    intro w x h hw
    by_contra hne
    exact (Set.disjoint_left.mp (hdisj hne) h.choose_spec) hw
  refine ⟨fun z => if h : ∃ x : ℝ, z ∈ γ x then φ h.choose else y₀, ?_, ?_⟩
  · refine MeasureTheory.ae_iff.2 (measure_mono_null (fun z hz => ?_) hnull)
    by_contra hz'
    simp only [Set.mem_iUnion, not_exists] at hz'
    simp [hz'] at hz
  · intro z hz
    have hzx : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hz)
    refine ⟨γ z.re, hzx ▸ hγ z.re, ?_⟩
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
    have h : ∃ x : ℝ, w ∈ γ x := ⟨z.re, hw.1⟩
    simp only [dif_pos h, huniq w z.re h hw.1]

/-- Blueprint `fact:vitali`: a Vitali set is not Lebesgue (null-)measurable. -/
theorem exists_not_nullMeasurableSet :
    ∃ s : Set ℝ, ¬ NullMeasurableSet s volume := by
  classical
  let rep : ℝ ⧸ ratSubgroup → ℝ := fun c => (exists_rep c).choose
  have hrep01 : ∀ c, rep c ∈ _root_.Set.Icc (0 : ℝ) 1 := fun c => (exists_rep c).choose_spec.1
  have hrepmk : ∀ c, ((rep c : ℝ) : ℝ ⧸ ratSubgroup) = c :=
    fun c => (exists_rep c).choose_spec.2
  let V : Set ℝ := _root_.Set.range rep
  refine ⟨V, fun hV => ?_⟩
  let ι := {q : ℚ // q ∈ _root_.Set.Icc (-1 : ℚ) 1}
  let T : ι → Set ℝ := fun q => (fun x => x + (-(q.1 : ℝ))) ⁻¹' V
  have hT : ∀ q, volume (T q) = volume V := fun q => measure_preimage_add_right _ _ _
  have hTm : ∀ q, NullMeasurableSet (T q) volume := fun q =>
    hV.preimage (measurePreserving_add_right volume _).quasiMeasurePreserving
  have hdisj : Pairwise (AEDisjoint volume on T) := by
    intro q q' hne
    refine Disjoint.aedisjoint (_root_.Set.disjoint_left.2 fun x hx hx' => hne ?_)
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hx'
    have hcc : c = c' := by
      rw [← hrepmk c, ← hrepmk c', hc, hc']
      refine QuotientAddGroup.eq.2 (mem_ratSubgroup.2 ⟨q.1 - q'.1, ?_⟩)
      push_cast; ring
    subst hcc
    have h : (q.1 : ℝ) = q'.1 := by linarith
    exact Subtype.ext (by exact_mod_cast h)
  have hU := measure_iUnion₀ hdisj hTm
  simp only [hT] at hU
  have hsub : _root_.Set.Icc (0 : ℝ) 1 ⊆ ⋃ q, T q := by
    intro x hx
    obtain ⟨q, hq⟩ := mem_ratSubgroup.1
      (QuotientAddGroup.eq.1 (hrepmk (x : ℝ ⧸ ratSubgroup)))
    have h1 := hrep01 (x : ℝ ⧸ ratSubgroup)
    have hq1 : (q : ℝ) ∈ _root_.Set.Icc (-1 : ℝ) 1 := by
      rw [hq]; constructor <;> linarith [hx.1, hx.2, h1.1, h1.2]
    refine _root_.Set.mem_iUnion.2 ⟨⟨q, ?_, ?_⟩, ?_⟩
    · exact_mod_cast hq1.1
    · exact_mod_cast hq1.2
    · refine ⟨(x : ℝ ⧸ ratSubgroup), ?_⟩
      show rep _ = x + -(q : ℝ)
      linarith
  have hsup : (⋃ q, T q) ⊆ _root_.Set.Icc (-1 : ℝ) 2 := by
    intro x hx
    obtain ⟨q, c, hc⟩ := _root_.Set.mem_iUnion.1 hx
    have h1 := hrep01 c
    have hq0 : (-1 : ℝ) ≤ q.1 := by exact_mod_cast q.2.1
    have hq1 : (q.1 : ℝ) ≤ 1 := by exact_mod_cast q.2.2
    simp only at hc
    constructor <;> linarith [h1.1, h1.2]
  have : Infinite ι := (_root_.Set.Icc_infinite (by norm_num : (-1 : ℚ) < 1)).to_subtype
  by_cases h0 : volume V = 0
  · have := measure_mono (μ := volume) hsub
    rw [hU, h0, tsum_zero, Real.volume_Icc] at this
    norm_num at this
  · have := measure_mono (μ := volume) hsup
    rw [hU, ENNReal.tsum_const_eq_top_of_ne_zero h0, Real.volume_Icc] at this
    exact absurd this (by simp)

/-- Blueprint `cor:nonmeasurable` (dissertation Theorem 10, Corollary 2). -/
theorem exists_measurable_nonmeasurable_boundaryFn' :
    ∃ f : ℂ → ℝ, NullMeasurable f volume ∧ ∃ φ : ℂ → ℝ,
      IsBoundaryFunction upper f realAxis φ ∧ ¬ NullMeasurable (fun x : ℝ => φ x) volume := by
  obtain ⟨s, hs⟩ := exists_not_nullMeasurableSet
  obtain ⟨f, hf0, hf⟩ := exists_ae_zero_boundaryFn' (0 : ℝ) (s.indicator 1)
  refine ⟨f, (measurable_const (a := (0 : ℝ))).nullMeasurable.congr
    (hf0.mono fun z hz => hz.symm), _, hf, fun h => hs ?_⟩
  have h' : NullMeasurable (s.indicator (1 : ℝ → ℝ)) volume := by
    simpa only [Complex.ofReal_re] using h
  have := h' (measurableSet_singleton (1 : ℝ))
  have he : s.indicator (1 : ℝ → ℝ) ⁻¹' {1} = s := by
    ext x; by_cases hx : x ∈ s <;> simp [hx]
  rwa [he] at this

end TJK.Discont
