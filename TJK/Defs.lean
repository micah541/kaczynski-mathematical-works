/-
Copyright: the TJK formalization project.

Trusted definitions for the formalization of the mathematical works of T. J. Kaczynski.
Every declaration in this file is pinned (see `blueprint/pinned.json`); the blueprint is
`paper/main.tex`.
-/
import Mathlib

open Set Filter Topology

namespace TJK

universe u v

/-! ## Classes of sets (blueprint `def:borel-classes`) -/

section Sets
variable {X : Type u} [TopologicalSpace X]

/-- A set is `F_σ` if it is a countable union of closed sets. -/
def IsFσ (s : Set X) : Prop :=
  ∃ F : ℕ → Set X, (∀ n, IsClosed (F n)) ∧ s = ⋃ n, F n

/-- A set is `F_σδ` if it is a countable intersection of `F_σ` sets. -/
def IsFσδ (s : Set X) : Prop :=
  ∃ A : ℕ → Set X, (∀ n, IsFσ (A n)) ∧ s = ⋂ n, A n

/-- A set is ambiguous if it is both `F_σ` and `G_δ`. -/
def IsAmbiguous (s : Set X) : Prop :=
  IsFσ s ∧ IsGδ s

end Sets

/-! ## Classes of functions (blueprint `def:fn-classes`) -/

section Functions
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- `f` is of class `F_σ`: preimages of open sets are `F_σ`. -/
def IsFσMeasurable (f : X → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → IsFσ (f ⁻¹' U)

/-- `f` is of Baire class `≤ 1`: a pointwise limit of continuous functions. -/
def IsBaireOne (f : X → Y) : Prop :=
  ∃ F : ℕ → X → Y, (∀ n, Continuous (F n)) ∧ ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))

/-- `f` is of honorary Baire class `≤ 2`: it agrees with a Baire-one function off a countable
set. -/
def IsHonoraryBaireTwo (f : X → Y) : Prop :=
  ∃ N : Set X, N.Countable ∧ ∃ g : X → Y, IsBaireOne g ∧ ∀ x ∉ N, f x = g x

/-- Baire classes of all orders: class `0` is the continuous functions; for `ξ > 0`, class `ξ`
consists of pointwise limits of sequences of functions of classes `η n < ξ`. -/
inductive BaireClass : Ordinal.{0} → (X → Y) → Prop
  | zero {f : X → Y} : Continuous f → BaireClass 0 f
  | lim {ξ : Ordinal.{0}} {f : X → Y} (η : ℕ → Ordinal.{0}) (F : ℕ → X → Y) :
      0 < ξ → (∀ n, η n < ξ) → (∀ n, BaireClass (η n) (F n)) →
      (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) → BaireClass ξ f

end Functions

/-! ## Arcs and curvilinear limits (blueprint `def:arcs`, `def:ccset`) -/

section Arcs
variable {E : Type u} [TopologicalSpace E] {Y : Type v} [TopologicalSpace Y]

/-- `γ` is a simple arc from `a` to `b`: the image of an injective path from `a` to `b`. -/
def IsArc (γ : Set E) (a b : E) : Prop :=
  ∃ p : Path a b, Function.Injective p ∧ range p = γ

/-- `γ` is an arc at `x` in `Ω`: a simple arc with one endpoint `x` and all other points in `Ω`. -/
def IsArcAt (Ω : Set E) (x : E) (γ : Set E) : Prop :=
  ∃ b, IsArc γ x b ∧ γ \ {x} ⊆ Ω

/-- `γ` is a crosscut of `Ω` with ends in `B`: a simple arc with two distinct endpoints in `B` and
all other points in `Ω`. -/
def IsCrosscut (Ω B : Set E) (γ : Set E) : Prop :=
  ∃ a b, a ≠ b ∧ a ∈ B ∧ b ∈ B ∧ IsArc γ a b ∧ γ \ {a, b} ⊆ Ω

/-- The set of curvilinear convergence of `f` in `Ω`, relative to the boundary set `B`: the points
`x ∈ B` with an arc at `x` along which `f` has a limit. -/
def curvConvSet (Ω B : Set E) (f : E → Y) : Set E :=
  {x | x ∈ B ∧ ∃ γ, IsArcAt Ω x γ ∧ ∃ q, Tendsto f (𝓝[γ \ {x}] x) (𝓝 q)}

/-- `φ` is a boundary function for `f` on `S`: at each `x ∈ S`, `f → φ x` along some arc at `x`. -/
def IsBoundaryFunction (Ω : Set E) (f : E → Y) (S : Set E) (φ : E → Y) : Prop :=
  ∀ x ∈ S, ∃ γ, IsArcAt Ω x γ ∧ Tendsto f (𝓝[γ \ {x}] x) (𝓝 (φ x))

/-- The cluster set of `f` along `γ` at `x`. -/
def clusterSet (f : E → Y) (γ : Set E) (x : E) : Set Y :=
  {q | MapClusterPt q (𝓝[γ \ {x}] x) f}

end Arcs

/-! ## The model domains -/

/-- The open unit disk `𝔻 ⊆ ℂ`. -/
abbrev disc : Set ℂ := Metric.ball 0 1

/-- The unit circle `C ⊆ ℂ`. -/
abbrev circle : Set ℂ := Metric.sphere 0 1

/-- The open upper half-plane `ℍ ⊆ ℂ`. -/
abbrev upper : Set ℂ := {z | 0 < z.im}

/-- The real axis, the boundary of `ℍ`. -/
abbrev realAxis : Set ℂ := {z | z.im = 0}

/-- The Riemann sphere, as the unit sphere of `ℝ³`. -/
abbrev Sphere2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

end TJK
