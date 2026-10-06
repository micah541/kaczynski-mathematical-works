import Mathlib
import TJK.Defs
import TJK.Baire.Basic
import TJK.Construct.Regions
import TJK.Construct.Special

/-!
# The function `g` (blueprint §F, `thm:construct-A`)

For an `F_σδ` set `A ⊆ (-1, 1)` we construct `g : ℂ → ℝ`, continuous on the upper half-plane with
values in `[0, 1]` there, such that `g → 0` at every `x ∈ A` through the Stolz angle
`s(x, 1, 3π/8)`, and such that `g → 0` along an arc at a real point `x` only if `x ∈ A`.

The open sets `U n` of the blueprint are `uSet (𝓕 n) (α n) (β n) (θ n) (ε n) (δ n)`, the union of
the `piece`s `s(x, ε n x, θ n)`, `x ∈ E(𝓕 n)`, and `B(F, δ n F, α n, β n)`, `F ∈ 𝓕 n ²`.

Instead of conditions (i)–(iii) of the blueprint, the construction directly asks that the closure
in `ℍ` of each piece of `U (n+1)` lies in `U n` (`exists_stolz_subset_uSet`,
`exists_region_subset_uSet`).

General facts about arcs proved here (to be moved to a `TJK/Plane` file):
`TJK.IsArcAt.exists_tail`.
-/

namespace TJK.Construct

open _root_.Set Metric Real Filter Topology

/-! ### General facts -/

/-- Building a sequence step by step. -/
theorem exists_seq_of_step {X : Type*} (P : ℕ → X → Prop) (R : ℕ → X → X → Prop)
    (h0 : ∃ x, P 0 x) (hs : ∀ n x, P n x → ∃ y, P (n + 1) y ∧ R n x y) :
    ∃ s : ℕ → X, (∀ n, P n (s n)) ∧ ∀ n, R n (s n) (s (n + 1)) := by
  obtain ⟨x₀, hx₀⟩ := h0
  choose f hf using hs
  let s' : ∀ n, {x // P n x} := fun n =>
    Nat.rec (motive := fun n => {x // P n x}) ⟨x₀, hx₀⟩
      (fun n y => ⟨f n y.1 y.2, (hf n y.1 y.2).1⟩) n
  exact ⟨fun n => (s' n).1, fun n => (s' n).2, fun n => (hf n (s' n).1 (s' n).2).2⟩

/-- A preconnected set covered by pairwise disjoint open sets lies in one of them. -/
theorem IsPreconnected.exists_subset_of_pairwise_disjoint {ι X : Type*} [TopologicalSpace X]
    {P : ι → Set X} (hP : ∀ i, IsOpen (P i)) (hd : Pairwise (Function.onFun Disjoint P)) {C : Set X}
    (hC : IsPreconnected C) (hne : C.Nonempty) (hCU : C ⊆ ⋃ i, P i) : ∃ i, C ⊆ P i := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hCU hc)
  refine ⟨i, hC.subset_left_of_subset_union (v := ⋃ (j) (_ : j ≠ i), P j) (hP i)
    (isOpen_iUnion fun j => isOpen_iUnion fun _ => hP j) ?_ ?_ ⟨c, hc, hi⟩⟩
  · rw [disjoint_iUnion_right]
    intro j
    rw [disjoint_iUnion_right]
    intro hj
    exact hd (Ne.symm hj)
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hCU hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion₂.2 ⟨j, hji, hj⟩)

end TJK.Construct

namespace TJK

open _root_.Set Metric Filter Topology

/-- A tail of an arc at `x`: a preconnected subset of `γ \ {x}` inside `ball x r` having `x` in its
closure. -/
theorem IsArcAt.exists_tail {E : Type*} [MetricSpace E] {Ω : Set E} {x : E} {γ : Set E}
    (h : IsArcAt Ω x γ) {r : ℝ} (hr : 0 < r) :
    ∃ C ⊆ γ \ {x}, IsPreconnected C ∧ C ⊆ ball x r ∧ x ∈ closure C := by
  obtain ⟨b, ⟨p, hinj, rfl⟩, -⟩ := h
  obtain ⟨s, hs, hball⟩ := Metric.continuousAt_iff.1 p.continuous_extend.continuousAt r hr
  set t₀ := min (s / 2) 1 with ht₀
  have ht₀pos : 0 < t₀ := lt_min (by linarith) one_pos
  refine ⟨p.extend '' Ioc 0 t₀, ?_, isPreconnected_Ioc.image _ p.continuous_extend.continuousOn,
    ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.trans (min_le_right _ _)⟩
    rw [p.extend_apply htI]
    refine ⟨mem_range_self _, fun h0 => ?_⟩
    have : (⟨t, htI⟩ : unitInterval) = 0 := hinj (h0.trans p.source.symm)
    have := congrArg Subtype.val this
    simp only [Set.Icc.coe_zero] at this
    linarith [ht.1]
  · rintro _ ⟨t, ht, rfl⟩
    have := @hball t (by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      linarith [ht.2, min_le_left (s / 2) 1])
    rwa [p.extend_zero] at this
  · have h0 : (0 : ℝ) ∈ closure (Ioc 0 t₀) := by
      rw [closure_Ioc ht₀pos.ne]
      exact ⟨le_rfl, ht₀pos.le⟩
    have := mem_closure_image p.continuous_extend.continuousAt h0
    rwa [p.extend_zero] at this

end TJK

namespace TJK.Construct

open _root_.Set Metric Real Filter Topology

/-! ### The series `g = Σ 2^{-(n+1)} g_n` -/

theorem summable_half_pow_succ : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) :=
  (summable_nat_add_iff 1).2 summable_geometric_two

theorem tsum_half_pow_succ : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_two]
  norm_num

/-- If `U n` are open and `cl U (n+1) ∩ ℍ ⊆ U n`, there is `g`, continuous on `ℍ` with values
in `[0, 1]`, with `g ≥ 2^{-(n+1)}` on `ℍ \ U n` and `g ≤ 2^{-(n+1)}` on `ℍ ∩ U (n+1)`. -/
theorem exists_series_of_closure_subset {U : ℕ → Set ℂ} (hUo : ∀ n, IsOpen (U n))
    (hcl : ∀ n, closure (U (n + 1)) ∩ upper ⊆ U n) :
    ∃ g : ℂ → ℝ, ContinuousOn g upper ∧ MapsTo g upper (Icc 0 1) ∧
      (∀ n, ∀ z ∈ upper, z ∉ U n → (1 / 2 : ℝ) ^ (n + 1) ≤ g z) ∧
      (∀ n, ∀ z ∈ upper, z ∈ U (n + 1) → g z ≤ (1 / 2 : ℝ) ^ (n + 1)) := by
  have hanti : ∀ m n, m ≤ n → U n ∩ upper ⊆ U m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact inter_subset_left
    | succ n _ ih =>
      exact fun z hz => ih ⟨hcl n ⟨subset_closure hz.1, hz.2⟩, hz.2⟩
  have hU : ∀ n, ∃ f : C(upper, ℝ), EqOn f 0 (Subtype.val ⁻¹' closure (U (n + 1))) ∧
      EqOn f 1 (Subtype.val ⁻¹' (U n)ᶜ) ∧ ∀ w, f w ∈ Icc (0 : ℝ) 1 := by
    intro n
    refine exists_continuous_zero_one_of_isClosed
      (isClosed_closure.preimage continuous_subtype_val)
      ((hUo n).isClosed_compl.preimage continuous_subtype_val) ?_
    rw [disjoint_left]
    intro w hw1 hw2
    exact hw2 (hcl n ⟨hw1, w.2⟩)
  choose f hf0 hf1 hfI using hU
  set w : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 1) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => by positivity
  have hle : ∀ n z, w n * f n z ≤ w n := fun n z =>
    mul_le_of_le_one_right (hw0 n) (hfI n z).2
  have hnn : ∀ n z, 0 ≤ w n * f n z := fun n z => mul_nonneg (hw0 n) (hfI n z).1
  have hsum : ∀ z, Summable fun n => w n * f n z := fun z =>
    Summable.of_nonneg_of_le (hnn · z) (hle · z) summable_half_pow_succ
  set G : upper → ℝ := fun z => ∑' n, w n * f n z with hG
  have hGc : Continuous G := by
    refine continuous_tsum (fun n => continuous_const.mul (f n).continuous)
      summable_half_pow_succ fun n z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn n z)]
    exact hle n z
  classical
  refine ⟨fun z => if h : z ∈ upper then G ⟨z, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hGc using 1
    funext z
    simp [domRestrict, z.2]
  · intro z hz
    simp only [dif_pos hz]
    refine ⟨tsum_nonneg (hnn · _), ?_⟩
    rw [← tsum_half_pow_succ]
    exact (hsum _).tsum_le_tsum (hle · _) summable_half_pow_succ
  · intro n z hz hzU
    simp only [dif_pos hz]
    have h1 : f n ⟨z, hz⟩ = 1 := hf1 n hzU
    calc (1 / 2 : ℝ) ^ (n + 1) = w n * f n ⟨z, hz⟩ := by rw [h1, mul_one]
      _ ≤ G ⟨z, hz⟩ := (hsum _).le_tsum n fun j _ => hnn j _
  · intro n z hz hzU
    simp only [dif_pos hz]
    have h0 : ∀ m < n + 1, f m ⟨z, hz⟩ = 0 := fun m hm =>
      hf0 m (subset_closure (hanti (m + 1) (n + 1) (by omega) ⟨hzU, hz⟩))
    show ∑' i, w i * f i ⟨z, hz⟩ ≤ _
    rw [← (hsum _).sum_add_tsum_nat_add (n + 1),
      Finset.sum_eq_zero fun m hm => by rw [h0 m (Finset.mem_range.1 hm), mul_zero], zero_add]
    calc ∑' i, w (i + (n + 1)) * f (i + (n + 1)) ⟨z, hz⟩
        ≤ ∑' i, (1 / 2 : ℝ) ^ (n + 1) * w i := by
          refine ((summable_nat_add_iff (n + 1)).2 (hsum _)).tsum_le_tsum (fun i => ?_)
            (summable_half_pow_succ.mul_left _)
          refine (hle _ _).trans (le_of_eq ?_)
          simp only [hw]
          rw [← pow_add]
          ring_nf
      _ = (1 / 2 : ℝ) ^ (n + 1) := by
          rw [tsum_mul_left, hw, tsum_half_pow_succ, mul_one]

end TJK.Construct

namespace TJK.Construct

open _root_.Set Metric Real Filter Topology

/-! ### The open sets `U` -/

open Classical in
/-- The pieces of `U`: `s(x, ε x, θ)` for `x ∈ E(𝓕)` and `B(F, δ F, α, β)` for `F ∈ 𝓕²`. -/
noncomputable def piece (𝓕 : Set (Set ℝ)) (α β θ : ℝ) (ε : ℝ → ℝ) (δ : Set ℝ → ℝ) :
    ℝ ⊕ Set ℝ → Set ℂ
  | .inl x => if x ∈ endpoints 𝓕 then stolz x (ε x) θ else ∅
  | .inr F => if F ∈ twoPoint 𝓕 then region F (δ F) α β else ∅

/-- The open set `U = ⋃ pieces`. -/
def uSet (𝓕 : Set (Set ℝ)) (α β θ : ℝ) (ε : ℝ → ℝ) (δ : Set ℝ → ℝ) : Set ℂ :=
  ⋃ i, piece 𝓕 α β θ ε δ i

section Pieces

variable {𝓕 : Set (Set ℝ)} {α β θ : ℝ} {ε : ℝ → ℝ} {δ : Set ℝ → ℝ}

theorem stolz_subset_uSet {x : ℝ} (hx : x ∈ endpoints 𝓕) :
    stolz x (ε x) θ ⊆ uSet 𝓕 α β θ ε δ := by
  intro z hz
  refine mem_iUnion.2 ⟨.inl x, ?_⟩
  simp only [piece, if_pos hx]
  exact hz

theorem region_subset_uSet {F : Set ℝ} (hF : F ∈ twoPoint 𝓕) :
    region F (δ F) α β ⊆ uSet 𝓕 α β θ ε δ := by
  intro z hz
  refine mem_iUnion.2 ⟨.inr F, ?_⟩
  simp only [piece, if_pos hF]
  exact hz

theorem piece_subset_upper (i : ℝ ⊕ Set ℝ) : piece 𝓕 α β θ ε δ i ⊆ upper := by
  rcases i with x | F <;> simp only [piece] <;> split_ifs
  exacts [stolz_subset_upper _ _ _, empty_subset _, region_subset_upper _ _ _ _, empty_subset _]

theorem uSet_subset_upper : uSet 𝓕 α β θ ε δ ⊆ upper :=
  iUnion_subset piece_subset_upper


theorem isOpen_piece (h𝓕 : IsSpecialFamily 𝓕) (hβ0 : 0 < β) (hβα : β < α) (hαθ : α < θ)
    (hθ1 : θ < π / 2) (i : ℝ ⊕ Set ℝ) : IsOpen (piece 𝓕 α β θ ε δ i) := by
  rcases i with x | F <;> simp only [piece] <;> split_ifs with h
  · exact isOpen_stolz _ _ _
  · exact isOpen_empty
  · exact isOpen_region (h𝓕.isCompact F h.1) h.2.nonempty (hβ0.trans hβα)
      (hαθ.trans hθ1) hβ0 (hβα.trans (hαθ.trans hθ1))
  · exact isOpen_empty

theorem pairwise_disjoint_piece (hp : IsSpecialPair 𝓕 α β θ ε δ) :
    Pairwise (Function.onFun Disjoint (piece 𝓕 α β θ ε δ)) := by
  rintro (x | F) (y | G) hne <;> simp only [Function.onFun, piece] <;> split_ifs with h1 h2 <;>
    try simp only [disjoint_empty, empty_disjoint]
  · exact hp.disjoint_stolz h1 h2 fun h => hne (h ▸ rfl)
  · exact hp.disjoint_stolz_region x h1 G h2
  · exact (hp.disjoint_stolz_region y h2 F h1).symm
  · exact hp.disjoint_region h1 h2 fun h => hne (h ▸ rfl)

theorem isOpen_uSet (h𝓕 : IsSpecialFamily 𝓕) (hβ0 : 0 < β) (hβα : β < α) (hαθ : α < θ)
    (hθ1 : θ < π / 2) : IsOpen (uSet 𝓕 α β θ ε δ) :=
  isOpen_iUnion (isOpen_piece h𝓕 hβ0 hβα hαθ hθ1)

/-- (R2) for the pieces. -/
theorem closure_piece_inter_axis (h𝓕 : IsSpecialFamily 𝓕) (hβ0 : 0 < β) (hβα : β < α) (hαθ : α < θ)
    (hθ1 : θ < π / 2)
    (hp : IsSpecialPair 𝓕 α β θ ε δ) (i : ℝ ⊕ Set ℝ) {z : ℂ}
    (hz : z ∈ closure (piece 𝓕 α β θ ε δ i))
    (h0 : z.im = 0) : z.re ∈ ⋃₀ 𝓕 ∧ z = (z.re : ℂ) := by
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h0])
  refine ⟨?_, hz'⟩
  rcases i with x | F <;> simp only [piece] at hz <;> split_ifs at hz with h
  · have := closure_stolz_inter_axis (a := x) (hp.eps_pos x h) (hβ0.trans (hβα.trans hαθ)) hθ1
    have hzx : z = (x : ℂ) := by
      have hmem : z ∈ closure (stolz x (ε x) θ) ∩ {z : ℂ | z.im = 0} := ⟨hz, h0⟩
      rw [this] at hmem
      exact hmem
    obtain ⟨F, hF, -, -, hxF⟩ := h𝓕.exists_mem_of_mem_endpoints h
    rw [hzx, Complex.ofReal_re]
    exact ⟨F, hF, hxF⟩
  · simp at hz
  · obtain ⟨y, hy, rfl⟩ := closure_region_inter_axis (h𝓕.isCompact F h.1) h.2.nonempty
      (hβ0.trans hβα) (hαθ.trans hθ1) hβ0 (hβα.trans (hαθ.trans hθ1)) ⟨hz, h0⟩
    rw [Complex.ofReal_re]
    exact ⟨F, h.1, hy⟩
  · simp at hz

/-- The closure of `U` in `ℍ` is the union of the closures of the pieces (local finiteness). -/
theorem exists_mem_closure_piece (hp : IsSpecialPair 𝓕 α β θ ε δ) {z : ℂ}
    (hz : z ∈ closure (uSet 𝓕 α β θ ε δ)) (hz0 : 0 < z.im) :
    ∃ i, z ∈ closure (piece 𝓕 α β θ ε δ i) := by
  set V : Set ℂ := {w | z.im / 2 < w.im}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_im
  set S : Set (ℝ ⊕ Set ℝ) := Sum.inl '' {x | x ∈ endpoints 𝓕 ∧ z.im / 2 ≤ ε x} ∪
    Sum.inr '' {F | F ∈ twoPoint 𝓕 ∧ z.im / 2 ≤ δ F}
  have hS : S.Finite :=
    ((hp.finite_eps _ (by linarith)).image _).union ((hp.finite_delta _ (by linarith)).image _)
  have hsub : V ∩ uSet 𝓕 α β θ ε δ ⊆ ⋃ i ∈ S, piece 𝓕 α β θ ε δ i := by
    rintro w ⟨hwV, hw⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    refine mem_iUnion₂.2 ⟨i, ?_, hi⟩
    have hwV : z.im / 2 < w.im := hwV
    rcases i with x | F <;> simp only [piece] at hi <;> split_ifs at hi with h
    · exact Or.inl ⟨x, ⟨h, (hwV.trans hi.2.1).le⟩, rfl⟩
    · exact hi.elim
    · exact Or.inr ⟨F, ⟨h, (hwV.trans hi.1.2.1).le⟩, rfl⟩
    · exact hi.elim
  have := closure_mono hsub (hV.inter_closure ⟨show z.im / 2 < z.im by linarith, hz⟩)
  rw [hS.closure_biUnion] at this
  obtain ⟨i, -, hi⟩ := mem_iUnion₂.1 this
  exact ⟨i, hi⟩

end Pieces

end TJK.Construct

namespace TJK.Construct

open _root_.Set Metric Real Filter Topology

/-! ### One step of the construction -/

section Step

variable {𝓕 : Set (Set ℝ)} {α β θ : ℝ} {ε : ℝ → ℝ} {δ : Set ℝ → ℝ}

/-- Points of members of `𝓕` have small Stolz angles (of a larger angle `θ'`) whose closure in `ℍ`
lies in `U`: by (R3) at endpoints of hulls and by (R10) at interior points. -/
theorem exists_stolz_subset_uSet (h𝓕 : IsSpecialFamily 𝓕) (hp : IsSpecialPair 𝓕 α β θ ε δ)
    (hβ0 : 0 < β) (hβα : β < α) (hαθ : α < θ) {θ' : ℝ} (hθθ' : θ < θ') (hθ'1 : θ' < π / 2)
    {x : ℝ} {F : Set ℝ} (hF : F ∈ 𝓕) (hx : x ∈ F) :
    ∃ ζ > 0, closure (stolz x ζ θ') ∩ upper ⊆ uSet 𝓕 α β θ ε δ := by
  have hFc := h𝓕.isCompact F hF
  have hne : F.Nonempty := ⟨x, hx⟩
  have h1 := csInf_le hFc.bddBelow hx
  have h2 := le_csSup hFc.bddAbove hx
  by_cases he : x = sInf F ∨ x = sSup F
  · have hxe : x ∈ endpoints 𝓕 := ⟨F, hF, hne, he⟩
    have := hp.eps_pos x hxe
    exact ⟨ε x / 2, by linarith, (closure_stolz_subset (by linarith)
      (hβ0.trans (hβα.trans hαθ)) hθθ' hθ'1).trans (stolz_subset_uSet hxe)⟩
  · push Not at he
    have hlt1 : sInf F < x := lt_of_le_of_ne h1 (Ne.symm he.1)
    have hlt2 : x < sSup F := lt_of_le_of_ne h2 he.2
    have hFt : F ∈ twoPoint 𝓕 :=
      ⟨hF, sInf F, hFc.sInf_mem hne, sSup F, hFc.sSup_mem hne, (hlt1.trans hlt2).ne⟩
    have hα0 : 0 < α := hβ0.trans hβα
    have hα1 : α < π / 2 := hαθ.trans (hθθ'.trans hθ'1)
    have hc : 0 < cot θ' + cot α :=
      add_pos (cot_pos_of_lt_pi_div_two (hα0.trans (hαθ.trans hθθ')) hθ'1)
        (cot_pos_of_lt_pi_div_two hα0 hα1)
    have hδ := hp.delta_pos F hFt
    have hd1 : 0 < (x - sInf F) / (cot θ' + cot α) := div_pos (by linarith) hc
    have hd2 : 0 < (sSup F - x) / (cot θ' + cot α) := div_pos (by linarith) hc
    refine ⟨min (δ F / 2) (min ((x - sInf F) / (cot θ' + cot α) / 2)
      ((sSup F - x) / (cot θ' + cot α) / 2)), lt_min (by linarith) (lt_min (by linarith)
      (by linarith)), (closure_stolz_subset_region hFc hne hx hα0 hα1 hβ0
      (hβα.trans (hαθ.trans hθθ')) hθ'1 ?_ ?_ ?_).trans (region_subset_uSet hFt)⟩
    · exact (min_le_left _ _).trans_lt (by linarith)
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
    · exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)

/-- A member `K ⊆ F ∈ 𝓕` with two points has a thin region (of angles `α' < α`, `β' > β`) whose
closure in `ℍ` lies in `U`, by (R7). -/
theorem exists_region_subset_uSet (h𝓕 : IsSpecialFamily 𝓕) (hp : IsSpecialPair 𝓕 α β θ ε δ)
    (hβ0 : 0 < β) {α' β' : ℝ} (hββ' : β < β') (hβ'α' : β' < α') (hα'α : α' < α)
    (hα1 : α < π / 2) {K F : Set ℝ} (hK : K.Nontrivial) (hKc : IsCompact K) (hF : F ∈ 𝓕)
    (hKF : K ⊆ F) : ∃ η > 0, closure (region K η α' β') ∩ upper ⊆ uSet 𝓕 α β θ ε δ := by
  have hFt : F ∈ twoPoint 𝓕 := ⟨hF, hK.mono hKF⟩
  have hδ := hp.delta_pos F hFt
  exact ⟨δ F / 2, by linarith, (closure_region_subset (h𝓕.isCompact F hF) hKc hK.nonempty hKF
    (by linarith) hβ0 hββ' hβ'α' hα'α hα1).trans (region_subset_uSet hFt)⟩

/-- The inductive step: a special pair for `𝓕'` (refining `𝓕`, with angles `α' β' θ'`) whose set
`U'` satisfies `cl U' ∩ ℍ ⊆ U`. -/
theorem exists_next_pair (h𝓕 : IsSpecialFamily 𝓕) {𝓕' : Set (Set ℝ)} (h𝓕' : IsSpecialFamily 𝓕')
    (href : ∀ K ∈ 𝓕', ∃ F ∈ 𝓕, K ⊆ F) (hp : IsSpecialPair 𝓕 α β θ ε δ) {α' β' θ' : ℝ}
    (hβ0 : 0 < β) (hββ' : β < β') (hβ'α' : β' < α') (hα'α : α' < α) (hαθ : α < θ)
    (hθθ' : θ < θ') (hθ'1 : θ' < π / 2) :
    ∃ ε' δ', IsSpecialPair 𝓕' α' β' θ' ε' δ' ∧
      closure (uSet 𝓕' α' β' θ' ε' δ') ∩ upper ⊆ uSet 𝓕 α β θ ε δ := by
  have hβα : β < α := hββ'.trans (hβ'α'.trans hα'α)
  obtain ⟨e₀, d₀, hp₀⟩ := exists_specialPair h𝓕' (hβ0.trans hββ') hβ'α'
    (hα'α.trans (hαθ.trans hθθ')) hθ'1
  have hζ : ∀ x, ∃ ζ > 0, x ∈ endpoints 𝓕' →
      closure (stolz x ζ θ') ∩ upper ⊆ uSet 𝓕 α β θ ε δ := by
    intro x
    by_cases hx : x ∈ endpoints 𝓕'
    · obtain ⟨K, hK, -, -, hxK⟩ := h𝓕'.exists_mem_of_mem_endpoints hx
      obtain ⟨F, hF, hKF⟩ := href K hK
      obtain ⟨ζ, hζ, h⟩ := exists_stolz_subset_uSet h𝓕 hp hβ0 hβα hαθ hθθ' hθ'1 hF (hKF hxK)
      exact ⟨ζ, hζ, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  have hη : ∀ K, ∃ η > 0, K ∈ twoPoint 𝓕' →
      closure (region K η α' β') ∩ upper ⊆ uSet 𝓕 α β θ ε δ := by
    intro K
    by_cases hK : K ∈ twoPoint 𝓕'
    · obtain ⟨F, hF, hKF⟩ := href K hK.1
      obtain ⟨η, hη, h⟩ := exists_region_subset_uSet h𝓕 hp hβ0 hββ' hβ'α' hα'α
        (hαθ.trans (hθθ'.trans hθ'1)) hK.2 (h𝓕'.isCompact K hK.1) hF hKF
      exact ⟨η, hη, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hK⟩
  choose ζ hζ0 hζ using hζ
  choose η hη0 hη using hη
  have hp' : IsSpecialPair 𝓕' α' β' θ' (fun x => min (e₀ x) (ζ x)) (fun K => min (d₀ K) (η K)) :=
    hp₀.mono (fun x hx => ⟨lt_min (hp₀.eps_pos x hx) (hζ0 x), min_le_left _ _⟩)
      (fun K hK => ⟨lt_min (hp₀.delta_pos K hK) (hη0 K), min_le_left _ _⟩)
  refine ⟨_, _, hp', ?_⟩
  rintro z ⟨hz, hzu⟩
  obtain ⟨i, hi⟩ := exists_mem_closure_piece hp' hz hzu
  rcases i with x | K <;> simp only [piece] at hi <;> split_ifs at hi with h
  · exact hζ x h ⟨closure_mono (stolz_mono (min_le_right _ _)) hi, hzu⟩
  · simp at hi
  · exact hη K h ⟨closure_mono (region_mono (min_le_right _ _)) hi, hzu⟩
  · simp at hi

end Step

/-! ### The angles -/

/-- `angT n = π / (24 (n + 2))`, decreasing to `0`. -/
noncomputable def angT (n : ℕ) : ℝ := π / (24 * ((n : ℝ) + 2))

/-- `β_n = π/4 - 2 angT n ↑ π/4`. -/
noncomputable def angB (n : ℕ) : ℝ := π / 4 - 2 * angT n

/-- `α_n = π/4 + 2 angT n ↓ π/4`. -/
noncomputable def angA (n : ℕ) : ℝ := π / 4 + 2 * angT n

/-- `θ_n = 3π/8 - angT n ↑ 3π/8`. -/
noncomputable def angTh (n : ℕ) : ℝ := 3 * π / 8 - angT n

theorem angT_pos (n : ℕ) : 0 < angT n := by
  unfold angT; have := pi_pos; positivity

theorem angT_le (n : ℕ) : angT n ≤ π / 48 := by
  unfold angT
  apply div_le_div_of_nonneg_left pi_pos.le (by norm_num)
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith

theorem angT_succ_lt (n : ℕ) : angT (n + 1) < angT n := by
  unfold angT
  apply div_lt_div_of_pos_left pi_pos (by positivity)
  push_cast
  linarith

theorem angles (n : ℕ) : 0 < angB n ∧ angB n < angA n ∧ angA n < angTh n ∧
    angTh n < 3 * π / 8 ∧ angB n < angB (n + 1) ∧ angA (n + 1) < angA n ∧
    angTh n < angTh (n + 1) := by
  have h1 := angT_pos n
  have h2 := angT_le n
  have h3 := angT_succ_lt n
  have := pi_pos
  unfold angB angA angTh
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-! ### `thm:construct-A` -/

/-- `thm:construct-A`: for an `F_σδ` set `A ⊆ (-1, 1)` there is `g`, continuous on `ℍ` with values
in `[0, 1]`, such that (a) `g → 0` at each `x ∈ A` through `s(x, 1, 3π/8)`, and (b) if `g → 0`
along an arc at a real point `x` in `ℍ`, then `x ∈ A`. -/
theorem exists_g {A : Set ℝ} (hA : IsFσδ A) (hAX : A ⊆ Ioo (-1) 1) :
    ∃ g : ℂ → ℝ, ContinuousOn g upper ∧ MapsTo g upper (Icc 0 1) ∧
      (∀ x ∈ A, Tendsto g (𝓝[stolz x 1 (3 * π / 8)] (x : ℂ)) (𝓝 0)) ∧
      ∀ (x : ℝ) (γ : Set ℂ), IsArcAt upper (x : ℂ) γ →
        Tendsto g (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) → x ∈ A := by
  obtain ⟨𝓕, h𝓕, hA, href⟩ := exists_specialFamily_seq hA hAX
  have h38 : 3 * π / 8 < π / 2 := by linarith [pi_pos]
  obtain ⟨s, hsP, hsR⟩ := exists_seq_of_step
    (fun n (p : (ℝ → ℝ) × (Set ℝ → ℝ)) =>
      IsSpecialPair (𝓕 n) (angA n) (angB n) (angTh n) p.1 p.2)
    (fun n p q => closure (uSet (𝓕 (n + 1)) (angA (n + 1)) (angB (n + 1)) (angTh (n + 1)) q.1 q.2)
      ∩ upper ⊆ uSet (𝓕 n) (angA n) (angB n) (angTh n) p.1 p.2)
    (by
      obtain ⟨h0, h1, h2, h3, -⟩ := angles 0
      obtain ⟨e, d, h⟩ := exists_specialPair (h𝓕 0) h0 h1 h2 (h3.trans h38)
      exact ⟨(e, d), h⟩)
    (fun n p hp => by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := angles n
      obtain ⟨h0', h1', h2', h3', -⟩ := angles (n + 1)
      obtain ⟨e, d, he, hd⟩ := exists_next_pair (h𝓕 n) (h𝓕 (n + 1)) (href n) hp h0 h4 h1' h5 h2
        h6 (h3'.trans h38)
      exact ⟨(e, d), he, hd⟩)
  set U : ℕ → Set ℂ := fun n => uSet (𝓕 n) (angA n) (angB n) (angTh n) (s n).1 (s n).2 with hU
  have hUo : ∀ n, IsOpen (U n) := fun n => by
    obtain ⟨h0, h1, h2, h3, -⟩ := angles n
    exact isOpen_uSet (h𝓕 n) h0 h1 h2 (h3.trans h38)
  obtain ⟨g, hgc, hgI, hlow, hup⟩ := exists_series_of_closure_subset hUo hsR
  have hpow : ∀ n, (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ n := fun n => by
    rw [pow_succ]
    have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
    linarith
  refine ⟨g, hgc, hgI, ?_, ?_⟩
  · -- (a)
    intro x hx
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one he (by norm_num : (1 / 2 : ℝ) < 1)
    have hxn : x ∈ ⋃₀ 𝓕 (n + 1) := by
      rw [hA] at hx
      exact mem_iInter.1 hx (n + 1)
    obtain ⟨F, hF, hxF⟩ := hxn
    obtain ⟨h0, h1, h2, h3, -⟩ := angles (n + 1)
    obtain ⟨ζ, hζ, hsub⟩ := exists_stolz_subset_uSet (h𝓕 (n + 1)) (hsP (n + 1)) h0 h1 h2 h3 h38
      hF hxF
    refine ⟨ζ, hζ, fun z hz hzd => ?_⟩
    have hzim : z.im < ζ := by
      have := Complex.abs_im_le_norm (z - x)
      rw [← dist_eq_norm, Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      exact (le_abs_self _).trans_lt (this.trans_lt hzd)
    have hzU : z ∈ U (n + 1) := hsub ⟨subset_closure ⟨hz.1, hzim, hz.2.2⟩, hz.1⟩
    have h1 := hup n z hz.1 hzU
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hgI hz.1).1]
    exact h1.trans_lt ((hpow n).trans_lt hn)
  · -- (b)
    intro x γ hγ hlim
    rw [hA, mem_iInter]
    intro n
    rw [Metric.tendsto_nhdsWithin_nhds] at hlim
    obtain ⟨r, hr, hr'⟩ := hlim _ (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1))
    obtain ⟨C, hCγ, hC, hCb, hxC⟩ := hγ.exists_tail hr
    obtain ⟨b, -, hγΩ⟩ := hγ
    have hCU : C ⊆ U n := fun z hz => by
      have hzγ := hCγ hz
      by_contra hzn
      have h1 := hlow n z (hγΩ hzγ) hzn
      have h2 := hr' hzγ (hCb hz)
      rw [Real.dist_eq, sub_zero] at h2
      linarith [le_abs_self (g z)]
    have hne : C.Nonempty := closure_nonempty_iff.1 ⟨_, hxC⟩
    obtain ⟨h0, h1, h2, h3, -⟩ := angles n
    obtain ⟨i, hi⟩ := IsPreconnected.exists_subset_of_pairwise_disjoint
      (isOpen_piece (h𝓕 n) h0 h1 h2 (h3.trans h38)) (pairwise_disjoint_piece (hsP n)) hC hne hCU
    have := (closure_piece_inter_axis (h𝓕 n) h0 h1 h2 (h3.trans h38) (hsP n) i
      (closure_mono hi hxC) (Complex.ofReal_im x)).1
    rwa [Complex.ofReal_re] at this

end TJK.Construct
