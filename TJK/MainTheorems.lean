/-
The headline theorems of each of Kaczynski's works, as trusted (pinned) statements.
Proofs are filled in other files; here they may be `sorry`.
Blueprint: `paper/main.tex`; each theorem names its blueprint label.
-/
import TJK.Defs
import TJK.Discont.Segments
import TJK.Discont.Vitali
import TJK.BoundaryFn.Homeo
import TJK.Construct.Realize

open Set Filter Topology MeasureTheory

namespace TJK

/-! ## Sets of curvilinear convergence (Michigan Math. J. 1966; dissertation Theorem 3) -/

/-- McMillan's theorem (blueprint `thm:mcmillan`). -/
theorem McMillan.isFσδ_curvConvSet {K : Type*} [MetricSpace K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (f : ℂ → K) (hf : ContinuousOn f disc) :
    IsFσδ (curvConvSet disc circle f) := by
  sorry

/-- Kaczynski's generalization to cluster sets (blueprint `thm:mm-thm2`). -/
theorem McMillan.isFσδ_clusterSet_subset {K : Type*} [MetricSpace K] [CompactSpace K]
    (ℰ : Set (TopologicalSpace.NonemptyCompacts K)) (hℰ : IsClosed ℰ) (f : ℂ → K)
    (hf : ContinuousOn f disc) :
    IsFσδ {x | x ∈ circle ∧ ∃ γ, IsArcAt disc x γ ∧ ∃ E ∈ ℰ, clusterSet f γ x ⊆ (E : Set K)} := by
  sorry

/-! ## Boundary functions of continuous functions -/

/-- Dissertation Theorem 5 (blueprint `thm:bf-fsigma`). -/
theorem BoundaryFn.exists_countable_isFσMeasurable {Y : Type*} [MetricSpace Y]
    [TopologicalSpace.SeparableSpace Y] (f : ℂ → Y) (hf : ContinuousOn f upper) (E : Set ℂ)
    (hE : E ⊆ realAxis) (φ : ℂ → Y) (hφ : IsBoundaryFunction upper f E φ) :
    ∃ M ⊆ E, M.Countable ∧ IsFσMeasurable ((E \ M).restrict φ) := by
  sorry

/-- Boundary functions on the circle are of honorary Baire class 2: real version
(1965 paper, Theorem 2; blueprint `cor:bf-honorary`). -/
theorem BoundaryFn.isHonoraryBaireTwo_disc_real (f : ℂ → ℝ) (hf : ContinuousOn f disc)
    (E : Set ℂ) (hE : E ⊆ circle) (φ : ℂ → ℝ) (hφ : IsBoundaryFunction disc f E φ) :
    IsHonoraryBaireTwo (E.restrict φ) := by
  sorry

/-- Boundary functions on the circle are of honorary Baire class 2: Riemann-sphere version
(1965 paper, Theorem 3; blueprint `cor:bf-honorary`). -/
theorem BoundaryFn.isHonoraryBaireTwo_disc_sphere (f : ℂ → Sphere2) (hf : ContinuousOn f disc)
    (E : Set ℂ) (hE : E ⊆ circle) (φ : ℂ → Sphere2) (hφ : IsBoundaryFunction disc f E φ) :
    IsHonoraryBaireTwo (E.restrict φ) := by
  sorry

/-- 1965 paper, Theorem 1 (blueprint `thm:homeo`): a boundary function of a homeomorphism of the
disk onto itself is continuous off a countable set. -/
theorem Homeo.exists_countable_continuousOn (e : disc ≃ₜ disc) (f : ℂ → ℂ)
    (hfe : ∀ z : disc, f z = e z) (E : Set ℂ) (hE : E ⊆ circle) (φ : ℂ → ℂ)
    (hφ : IsBoundaryFunction disc f E φ) :
    ∃ N ⊆ E, N.Countable ∧ ContinuousOn φ (E \ N) :=
  Homeo.exists_countable_continuousOn' e f hfe E hE φ hφ

/-! ## Realization (Trans. AMS 141, 1969; dissertation Theorems 4, 6, 7) -/

/-- Dissertation Theorem 4 (blueprint `thm:cc-realize`): every `F_σδ` subset of `ℝ` is the set of
curvilinear convergence of a bounded continuous function in the upper half-plane. -/
theorem Construct.exists_curvConvSet_eq_upperHalfPlane (A : Set ℝ) (hA : IsFσδ A) :
    ∃ f : ℂ → ℂ, ContinuousOn f upper ∧ Bornology.IsBounded (f '' upper) ∧
      curvConvSet upper realAxis f = ((↑) : ℝ → ℂ) '' A :=
  Construct.exists_curvConvSet_eq_upperHalfPlane' A hA

/-- McMillan's problem, answered (Trans. AMS 141, (F); blueprint `thm:construct-F`). -/
theorem Construct.exists_f_sphere (A : Set ℂ) (hA : A ⊆ circle) (hAF : IsFσδ A)
    (φ : ℂ → Sphere2) (hφ : IsHonoraryBaireTwo (A.restrict φ)) :
    ∃ f : ℂ → Sphere2, ContinuousOn f disc ∧ curvConvSet disc circle f = A ∧
      IsBoundaryFunction disc f A φ := by
  sorry

/-- Dissertation Theorem 6 (blueprint `thm:construct-H` (b)). -/
theorem Construct.exists_boundaryFn_euclidean {m : ℕ} (E : Set ℝ)
    (φ : ℝ → EuclideanSpace ℝ (Fin m)) (hφ : IsHonoraryBaireTwo (E.restrict φ)) :
    ∃ f : ℂ → EuclideanSpace ℝ (Fin m), ContinuousOn f upper ∧
      IsBoundaryFunction upper f (((↑) : ℝ → ℂ) '' E) (fun z => φ z.re) := by
  sorry

/-! ## Discontinuous functions (dissertation Chapter II; 1965 paper, Theorems 4–6) -/

/-- Dissertation Theorem 8 (blueprint `thm:baire-plus-one`). -/
theorem Discont.baireClass_succ_of_boundaryFn {Y : Type} [MetricSpace Y]
    [TopologicalSpace.SeparableSpace Y] [PathConnectedSpace Y] (ξ : Ordinal.{0}) (hξ : 1 ≤ ξ)
    (f : ℂ → Y) (hf : BaireClass ξ (upper.restrict f)) (E : Set ℂ) (hE : E ⊆ realAxis)
    (φ : ℂ → Y) (hφ : IsBoundaryFunction upper f E φ) :
    BaireClass (ξ + 1) (E.restrict φ) := by
  sorry

/-- Dissertation Theorem 10 (blueprint `thm:th-thm10`). -/
theorem Discont.exists_disjoint_null_arcs :
    ∃ γ : ℝ → Set ℂ, (∀ x : ℝ, IsArcAt upper (x : ℂ) (γ x)) ∧
      Pairwise (fun x y => Disjoint (γ x) (γ y)) ∧ volume (⋃ x, γ x) = 0 :=
  Discont.exists_disjoint_null_arcs'

/-- 1965 paper, Theorem 6 (blueprint `cor:ae-zero`). -/
theorem Discont.exists_ae_zero_boundaryFn {Y : Type*} [MetricSpace Y] (y₀ : Y) (φ : ℝ → Y) :
    ∃ f : ℂ → Y, (∀ᵐ z ∂volume, f z = y₀) ∧
      IsBoundaryFunction upper f realAxis (fun z => φ z.re) :=
  Discont.exists_ae_zero_boundaryFn' y₀ φ

/-- Dissertation Theorem 10, Corollary 2 (blueprint `cor:nonmeasurable`). -/
theorem Discont.exists_measurable_nonmeasurable_boundaryFn :
    ∃ f : ℂ → ℝ, NullMeasurable f volume ∧ ∃ φ : ℂ → ℝ,
      IsBoundaryFunction upper f realAxis φ ∧ ¬ NullMeasurable (fun x : ℝ => φ x) volume :=
  Discont.exists_measurable_nonmeasurable_boundaryFn'

/-! ## Bounded harmonic functions (Trans. AMS 137, 1969) -/

/-- Answer to Bagemihl–Piranian's Problem 5 (blueprint `thm:ha-example`). -/
theorem Harmonic.exists_bounded_harmonic_boundaryFn_not_baireOne :
    ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f disc ∧ Bornology.IsBounded (f '' disc) ∧
      ∃ φ : ℂ → ℝ, IsBoundaryFunction disc f circle φ ∧ ¬ IsBaireOne (circle.restrict φ) := by
  sorry

/-- Blueprint `thm:ha-theorem`: for a harmonic function with bounded `p`-th integral means
(`p > 1`), the points with an asymptotic value but no general limit form a set of the first
category on the circle. -/
theorem Harmonic.isMeagre_asymptotic_diff_generalLimit (u : ℂ → ℝ)
    (hu : InnerProductSpace.HarmonicOnNhd u disc) (p : ℝ) (hp : 1 < p)
    (hmean : ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
      ∫ θ in (0 : ℝ)..(2 * Real.pi), |u (r * Complex.exp (θ * Complex.I))| ^ p ≤ B) :
    IsMeagre ((Subtype.val : circle → ℂ) ⁻¹'
      (curvConvSet disc circle u \ {ζ | ∃ L, Tendsto u (𝓝[disc] ζ) (𝓝 L)})) := by
  sorry

/-! ## The cube (Proc. AMS 23, 1969) -/

/-- The open cube `(-1,1) × (0,1) × (-1,1)` of the paper. -/
def Cube.openCube : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v 0 ∈ Ioo (-1 : ℝ) 1 ∧ v 1 ∈ Ioo (0 : ℝ) 1 ∧ v 2 ∈ Ioo (-1 : ℝ) 1}

/-- Blueprint `thm:cube`: a bounded continuous complex function in a cube whose set of
curvilinear convergence is not a Borel set. -/
theorem Cube.exists_not_measurableSet_curvConvSet :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℂ, ContinuousOn f Cube.openCube ∧
      Bornology.IsBounded (f '' Cube.openCube) ∧
      ¬ MeasurableSet (curvConvSet Cube.openCube (frontier Cube.openCube) f) := by
  sorry

end TJK
