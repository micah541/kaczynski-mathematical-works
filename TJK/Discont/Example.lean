import Mathlib
import TJK.Defs
import TJK.Discont.Segments

/-!
# Disjointness cannot be omitted in Theorem 9 (blueprint `prop:th-example`)

There are null sets `M₀, M₁ ⊆ ℝ` such that every point of the open strip `0 < y < 1` lies on a
segment from `M₀ × {0}` to `M₁ × {1}`. We take `M₀ = M₁` = the Liouville numbers, a dense `G_δ`
null set (Mathlib); the segment through `(x₀, y₀)` with lower end `a` has upper end `g a`, `g` an
affine bijection, and `M ∩ g⁻¹(M)` is dense by Baire's theorem.
-/

open MeasureTheory Set

namespace TJK.Discont

/-- `prop:th-example`. -/
theorem segments_not_disjoint_example :
    ∃ M₀ M₁ : Set ℝ, volume M₀ = 0 ∧ volume M₁ = 0 ∧
      ∀ z : ℝ × ℝ, z.2 ∈ Ioo (0 : ℝ) 1 → ∃ p ∈ M₀ ×ˢ M₁, z ∈ segment01 p := by
  set M : Set ℝ := {x | Liouville x}
  refine ⟨M, M, volume_setOfPred_liouville, volume_setOfPred_liouville, ?_⟩
  rintro ⟨x₀, y₀⟩ ⟨hy0, hy1⟩
  simp only at hy0 hy1
  have hc : -(1 - y₀) / y₀ ≠ 0 := div_ne_zero (by linarith) hy0.ne'
  set e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ _ hc).trans (Homeomorph.addRight (x₀ / y₀)) with he
  have hD : Dense (M ∩ e ⁻¹' M) :=
    Dense.inter_of_Gδ IsGδ.setOfPred_liouville (IsGδ.setOfPred_liouville.preimage e.continuous)
      dense_liouville (dense_liouville.preimage e.isOpenMap)
  obtain ⟨a, haM, haeM⟩ := hD.nonempty
  refine ⟨(a, e a), ⟨haM, haeM⟩, ⟨⟨hy0.le, hy1.le⟩, ?_⟩⟩
  simp only [segLine, he, Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀,
    Homeomorph.coe_addRight]
  field_simp
  ring

end TJK.Discont
