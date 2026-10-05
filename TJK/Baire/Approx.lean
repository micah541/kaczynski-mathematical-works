/-
Copyright: the TJK formalization project.

Section B of the blueprint (`paper/sections/B-baire.tex`), second part: approximation of functions
of class `F_σ` by continuous functions (Kaczynski, Diss. Lemmas 2–6), uniform limits, and the
extension of Baire-one functions from `G_δ` and from co-countable subsets.

As in `TJK.Baire.Basic`, the ambient space `M` is only assumed `PerfectlyNormalSpace` (every
metrizable space is); a subset `L ⊆ M` is the subtype `↥L`, which is again perfectly normal.
Vector-valued functions take values in `Fin m → ℝ` (the sup-norm model of `ℝ^m`, which has the
Euclidean topology).
-/
import Mathlib
import TJK.Defs
import TJK.Baire.Basic

open Set Filter Topology Function

namespace TJK

/-! ## Auxiliary facts -/

section Aux

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
  {Z : Type*} [TopologicalSpace Z]

theorem IsFσMeasurable.comp_continuous {f : X → Y} (hf : IsFσMeasurable f) {g : Z → X}
    (hg : Continuous g) : IsFσMeasurable (f ∘ g) :=
  fun U hU => (hf U hU).preimage hg

theorem Continuous.comp_isFσMeasurable {g : Y → Z} (hg : Continuous g) {f : X → Y}
    (hf : IsFσMeasurable f) : IsFσMeasurable (g ∘ f) :=
  fun _ hU => hf _ (hU.preimage hg)

theorem isFσMeasurable_const (c : Y) : IsFσMeasurable fun _ : X => c := by
  intro U _
  by_cases h : c ∈ U
  · simp [h, isFσ_univ]
  · simp [h, isFσ_empty]

/-- A function constant on the pieces of a countable partition into `F_σ` sets is of class
`F_σ`. -/
theorem exists_piecewise_of_partition {ι : Type*} [Countable ι] {R : ι → Set X}
    (hR : ∀ i, IsFσ (R i)) (hdisj : Pairwise (Disjoint on R)) (hcov : ⋃ i, R i = univ)
    (v : ι → Y) :
    ∃ g : X → Y, (∀ i, ∀ x ∈ R i, g x = v i) ∧ IsFσMeasurable g ∧ range g ⊆ range v := by
  have hx : ∀ x, ∃ i, x ∈ R i := fun x => mem_iUnion.1 (hcov ▸ mem_univ x)
  choose c hc using hx
  have huniq : ∀ i x, x ∈ R i → c x = i := fun i x hx => by
    by_contra h
    exact Set.disjoint_left.1 (hdisj h) (hc x) hx
  refine ⟨fun x => v (c x), fun i x hx => by simp only [huniq i x hx], ?_, ?_⟩
  · intro U _
    have : (fun x => v (c x)) ⁻¹' U = ⋃ (i : ι) (_ : v i ∈ U), R i := by
      ext x
      simp only [mem_preimage, mem_iUnion, exists_prop]
      constructor
      · intro h
        exact ⟨c x, h, hc x⟩
      · rintro ⟨i, hi, hx⟩
        rwa [huniq i x hx]
    rw [this]
    exact IsFσ.iUnion fun i => IsFσ.iUnion fun _ => hR i
  · rintro _ ⟨x, rfl⟩
    exact ⟨c x, rfl⟩

/-- A sequence of functions into `ℝ^ι` whose coordinates are Baire-one is Baire-one. -/
theorem isBaireOne_pi {ι : Type*} {F : X → ι → ℝ} (hF : ∀ i, IsBaireOne fun x => F x i) :
    IsBaireOne F := by
  choose G hGc hGt using hF
  exact ⟨fun n x i => G i n x, fun n => continuous_pi fun i => hGc i n,
    fun x => tendsto_pi_nhds.2 fun i => hGt i x⟩

/-- Clamping a convergent sequence into an interval `[-b, b]` containing the limit preserves
convergence. -/
theorem tendsto_clamp {b a : ℝ} (ha : |a| ≤ b) {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => max (-b) (min b (u n))) atTop (𝓝 a) := by
  have := (tendsto_const_nhds (x := -b)).max ((tendsto_const_nhds (x := b)).min hu)
  rwa [min_eq_right (abs_le.1 ha).2, max_eq_right (abs_le.1 ha).1] at this

theorem abs_clamp_le {b : ℝ} (hb : 0 ≤ b) (y : ℝ) : |max (-b) (min b y)| ≤ b :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

end Aux

/-! ## Approximation by continuous functions (blueprint `lem:approx-char`, `lem:approx-finite`,
`lem:uniform-approx`, `lem:approx-real`, `thm:baire1-char`) -/

section Approx

variable {M : Type*} [TopologicalSpace M] [PerfectlyNormalSpace M]

/-- **Diss. Lemma 2.** The characteristic function of an ambiguous subset `E` of `L ⊆ M` is, on
`L`, the pointwise limit of continuous functions `M → [0, 1]`. -/
theorem approx_indicator {L : Set M} {E : Set L} (hE : IsAmbiguous E) :
    ∃ F : ℕ → M → ℝ, (∀ n, Continuous (F n)) ∧ (∀ n y, F n y ∈ Icc (0 : ℝ) 1) ∧
      ∀ x : L, Tendsto (fun n => F n x) atTop (𝓝 (E.indicator 1 x)) := by
  obtain ⟨E₁, hE₁, hEE₁⟩ := isFσ_subtype_iff.1 hE.1
  obtain ⟨F₁, hF₁, hEF₁⟩ := isFσ_subtype_iff.1 (isFσ_compl_iff.2 hE.2)
  obtain ⟨A, B, hA, hB, hAE, hBF, hAB, hcov⟩ := reduction hE₁ hF₁
  obtain ⟨An, hAn, rfl⟩ := hA
  obtain ⟨Bn, hBn, rfl⟩ := hB
  -- increasing closed exhaustions
  let A' : ℕ → Set M := fun n => ⋃ k ∈ Finset.range (n + 1), An k
  let B' : ℕ → Set M := fun n => ⋃ k ∈ Finset.range (n + 1), Bn k
  have hA' : ∀ n, IsClosed (A' n) := fun n => isClosed_biUnion_finset fun k _ => hAn k
  have hB' : ∀ n, IsClosed (B' n) := fun n => isClosed_biUnion_finset fun k _ => hBn k
  have hA'mem : ∀ k n, k ≤ n → An k ⊆ A' n := fun k n hkn =>
    subset_biUnion_of_mem (u := An) (Finset.mem_range.2 (Nat.lt_succ_of_le hkn))
  have hB'mem : ∀ k n, k ≤ n → Bn k ⊆ B' n := fun k n hkn =>
    subset_biUnion_of_mem (u := Bn) (Finset.mem_range.2 (Nat.lt_succ_of_le hkn))
  have hdisj : ∀ n, Disjoint (B' n) (A' n) := by
    intro n
    refine Set.disjoint_left.2 fun y hyB hyA =>
      Set.disjoint_left.1 hAB (show y ∈ ⋃ n, An n from ?_) (show y ∈ ⋃ n, Bn n from ?_)
    · obtain ⟨k, -, hk⟩ := mem_iUnion₂.1 hyA
      exact mem_iUnion.2 ⟨k, hk⟩
    · obtain ⟨k, -, hk⟩ := mem_iUnion₂.1 hyB
      exact mem_iUnion.2 ⟨k, hk⟩
  choose G hG0 hG1 hG01 using fun n => exists_continuous_zero_one_of_isClosed (hB' n) (hA' n)
    (hdisj n)
  refine ⟨fun n => G n, fun n => (G n).continuous, hG01, fun x => ?_⟩
  by_cases hx : x ∈ E
  · have hxE₁ : (x : M) ∈ E₁ := by rw [hEE₁] at hx; exact hx
    have hxA : (x : M) ∈ ⋃ n, An n := by
      have : (x : M) ∈ (⋃ n, An n) ∪ ⋃ n, Bn n := hcov ▸ Or.inl hxE₁
      refine this.resolve_right fun hxB => ?_
      have : x ∈ Eᶜ := by rw [hEF₁]; exact hBF hxB
      exact this hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hxA
    rw [indicator_of_mem hx]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k, fun n hn => ?_⟩)
    exact (hG1 n (hA'mem k n hn hk)).symm
  · have hxF₁ : (x : M) ∈ F₁ := by
      have : x ∈ Eᶜ := hx
      rw [hEF₁] at this; exact this
    have hxB : (x : M) ∈ ⋃ n, Bn n := by
      have : (x : M) ∈ (⋃ n, An n) ∪ ⋃ n, Bn n := hcov ▸ Or.inr hxF₁
      refine this.resolve_left fun hxA => hx ?_
      rw [hEE₁]; exact hAE hxA
    obtain ⟨k, hk⟩ := mem_iUnion.1 hxB
    rw [indicator_of_notMem hx]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k, fun n hn => ?_⟩)
    exact (hG0 n (hB'mem k n hn hk)).symm

/-- **Diss. Lemma 3.** A finitely valued real function of class `F_σ` on `L ⊆ M` is, on `L`, the
pointwise limit of continuous functions on `M`. -/
theorem approx_finiteValued {L : Set M} {f : L → ℝ} (hf : IsFσMeasurable f)
    (hfin : (range f).Finite) :
    ∃ F : ℕ → M → ℝ, (∀ n, Continuous (F n)) ∧
      ∀ x : L, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  classical
  choose G hGc _ hGt using fun a : ℝ => approx_indicator (L := L) (finiteValued_ambiguous hf hfin a)
  refine ⟨fun n y => ∑ a ∈ hfin.toFinset, a * G a n y,
    fun n => continuous_finsetSum _ fun a _ => continuous_const.mul (hGc a n), fun x => ?_⟩
  have : f x = ∑ a ∈ hfin.toFinset, a * (f ⁻¹' {a}).indicator 1 x := by
    rw [Finset.sum_eq_single (f x)]
    · simp
    · intro b _ hb
      rw [indicator_of_notMem (by simpa [eq_comm] using hb), mul_zero]
    · intro h
      exact absurd (by simp) h
  rw [this]
  exact tendsto_finsetSum _ fun a _ => (hGt a x).const_mul a

/-- **Diss. Lemma 4** (Banach's Hilfssatz 4). A bounded real function of class `F_σ` is
uniformly approximated, within any `ε > 0`, by finitely valued functions of class `F_σ`. -/
theorem uniform_approx_finiteValued {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]
    {f : X → ℝ} (hf : IsFσMeasurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, IsFσMeasurable g ∧ (range g).Finite ∧ (∀ x, |g x - f x| < ε) ∧
      ∀ x, |g x| ≤ C + ε := by
  set N : ℕ := ⌈C / ε⌉₊
  let ι := ↥(Finset.Icc (-(N : ℤ)) N)
  let P : ι → Set X := fun j => f ⁻¹' Ioo (((j : ℤ) - 1 : ℝ) * ε) (((j : ℤ) + 1 : ℝ) * ε)
  have hP : ∀ j, IsFσ (P j) := fun j => hf _ isOpen_Ioo
  obtain ⟨R, hR, hRP, hdisj, hcovR, -⟩ := reduction_finite hP
  have hcovP : ⋃ j, P j = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    set j : ℤ := ⌊f x / ε⌋
    have h1 : (j : ℝ) ≤ f x / ε := Int.floor_le _
    have h2 : f x / ε < j + 1 := Int.lt_floor_add_one _
    have hfC := abs_le.1 (hC x)
    have h3 : f x / ε ≤ C / ε := div_le_div_of_nonneg_right hfC.2 hε.le
    have h4 : -C / ε ≤ f x / ε := div_le_div_of_nonneg_right hfC.1 hε.le
    have h5 : C / ε ≤ N := Nat.le_ceil _
    have hjN : j ≤ N := by
      have : (j : ℝ) ≤ N := by linarith
      exact_mod_cast this
    have hjN' : -(N : ℤ) - 1 < j := by
      have : -(N : ℝ) - 1 < j := by
        have : -C / ε = -(C / ε) := neg_div _ _
        linarith
      exact_mod_cast this
    refine ⟨⟨j, Finset.mem_Icc.2 ⟨by omega, hjN⟩⟩, ?_⟩
    have e1 : (j : ℝ) * ε ≤ f x := (le_div_iff₀ hε).1 h1
    have e2 : f x < ((j : ℝ) + 1) * ε := (div_lt_iff₀ hε).1 h2
    simp only [P, mem_preimage, mem_Ioo]
    constructor <;> nlinarith
  have hcov : ⋃ j, R j = univ := hcovR.trans hcovP
  obtain ⟨g, hgv, hgF, hgr⟩ :=
    exists_piecewise_of_partition hR hdisj hcov fun j : ι => ((j : ℤ) : ℝ) * ε
  have hclose : ∀ x, |g x - f x| < ε := by
    intro x
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov ▸ mem_univ x : x ∈ ⋃ j, R j)
    have hx := hRP j hj
    simp only [P, mem_preimage, mem_Ioo] at hx
    rw [hgv j x hj, abs_lt]
    constructor <;> nlinarith
  refine ⟨g, hgF, (finite_range _).subset hgr, hclose, fun x => ?_⟩
  have := abs_sub_abs_le_abs_sub (g x) (f x)
  linarith [hclose x, hC x]

/-- A bounded real function of class `F_σ` is the sum of a series of finitely valued functions of
class `F_σ` with summable bounds (the telescoping series of the approximations of
`uniform_approx_finiteValued` with errors `2⁻ⁿ`). -/
theorem exists_hasSum_finiteValued {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]
    {f : X → ℝ} (hf : IsFσMeasurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∃ h : ℕ → X → ℝ, ∃ b : ℕ → ℝ, (∀ n, IsFσMeasurable (h n)) ∧ (∀ n, (range (h n)).Finite) ∧
      (∀ n, 0 ≤ b n) ∧ Summable b ∧ (∀ n x, |h n x| ≤ b n) ∧
      ∀ x, HasSum (fun n => h n x) (f x) := by
  choose g hgF hgfin hgε hgC using fun n : ℕ =>
    uniform_approx_finiteValued hf hC (ε := (1 / 2) ^ n) (by positivity)
  let h : ℕ → X → ℝ := fun n => if n = 0 then g 0 else g n - g (n - 1)
  have h0 : h 0 = g 0 := by simp [h]
  have hsucc : ∀ k, h (k + 1) = g (k + 1) - g k := fun k => by simp [h]
  have hpart : ∀ n x, ∑ i ∈ Finset.range (n + 1), h i x = g n x := by
    intro n x
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Finset.sum_range_succ, ih, hsucc]; simp
  let b : ℕ → ℝ := fun n => (|C| + 4) * (1 / 2) ^ n
  have hbd : ∀ n x, |h n x| ≤ b n := by
    intro n x
    rcases n with _ | k
    · rw [h0]
      have := hgC 0 x
      have : C ≤ |C| := le_abs_self C
      simp only [b, pow_zero, mul_one] at *
      linarith
    · rw [hsucc]
      have e1 := hgε (k + 1) x
      have e2 := hgε k x
      have : |g (k + 1) x - g k x| ≤ |g (k + 1) x - f x| + |g k x - f x| := by
        have := abs_sub_le (g (k + 1) x) (f x) (g k x)
        rwa [abs_sub_comm (f x)] at this
      have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
      have : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
      simp only [b, Pi.sub_apply] at *
      have := abs_nonneg C
      nlinarith
  have hb0 : ∀ n, 0 ≤ b n := fun n => by positivity
  have hbs : Summable b := (summable_geometric_two).mul_left _
  refine ⟨h, b, ?_, ?_, hb0, hbs, hbd, fun x => ?_⟩
  · intro n
    rcases n with _ | k
    · rw [h0]; exact hgF 0
    · rw [hsucc]; exact (IsFσMeasurable.sub_of_finite (hgF _) (hgF _) (hgfin _) (hgfin _)).1
  · intro n
    rcases n with _ | k
    · rw [h0]; exact hgfin 0
    · rw [hsucc]; exact (IsFσMeasurable.sub_of_finite (hgF _) (hgF _) (hgfin _) (hgfin _)).2
  · rw [hasSum_iff_tendsto_nat_of_summable_norm
      (hbs.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => (hbd n x))]
    rw [← tendsto_add_atTop_iff_nat 1]
    simp only [hpart]
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => (Real.dist_eq _ _ ▸ hgε n x).le) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Real functions of class `F_σ` which are bounded are, on `L`, pointwise limits of continuous
functions on `M`. -/
theorem approx_real_of_bounded {L : Set M} {f : L → ℝ} (hf : IsFσMeasurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    ∃ F : ℕ → M → ℝ, (∀ n, Continuous (F n)) ∧
      ∀ x : L, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  obtain ⟨h, b, hh, hfin, hb0, hbs, hbd, hsum⟩ := exists_hasSum_finiteValued hf hC
  choose K hKc hKt using fun n => approx_finiteValued (L := L) (hh n) (hfin n)
  let k : ℕ → ℕ → M → ℝ := fun n j y => max (-b n) (min (b n) (K n j y))
  have hk : ∀ n j y, ‖k n j y‖ ≤ b n := fun n j y => abs_clamp_le (hb0 n) _
  refine ⟨fun j y => ∑' n, k n j y, fun j => continuous_tsum (fun n => ?_) hbs fun n y => hk n j y,
    fun x => ?_⟩
  · exact continuous_const.max (continuous_const.min (hKc n j))
  · rw [← (hsum x).tsum_eq]
    exact tendsto_tsum_of_dominated_convergence hbs (fun n => tendsto_clamp (hbd n x) (hKt n x))
      (Eventually.of_forall fun j n => hk n j x)

open Real in
/-- **Diss. Lemma 5.** A real function of class `F_σ` on `L ⊆ M` is, on `L`, the pointwise limit
of continuous functions on `M`. -/
theorem approx_real {L : Set M} {f : L → ℝ} (hf : IsFσMeasurable f) :
    ∃ F : ℕ → M → ℝ, (∀ n, Continuous (F n)) ∧
      ∀ x : L, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  obtain ⟨G, hGc, hGt⟩ := approx_real_of_bounded (C := π / 2)
    (Continuous.comp_isFσMeasurable continuous_arctan hf)
    (fun x => (abs_lt.2 ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩).le)
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ0 : ∀ j, 0 < δ j := fun j => by positivity
  have hδ1 : ∀ j, δ j ≤ 1 := fun j => by
    simp only [δ]
    rw [div_le_one (by positivity)]
    simp
  have hπ := pi_gt_three
  let H : ℕ → M → ℝ := fun j y => max (-(π / 2) + δ j) (min (π / 2 - δ j) (G j y))
  have hHc : ∀ j, Continuous (H j) := fun j =>
    continuous_const.max (continuous_const.min (hGc j))
  have hHI : ∀ j y, H j y ∈ Ioo (-(π / 2)) (π / 2) := by
    intro j y
    have := hδ0 j
    have := hδ1 j
    constructor
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · exact max_lt (by linarith) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  refine ⟨fun j y => tan (H j y),
    fun j => continuousOn_tan_Ioo.comp_continuous (hHc j) (hHI j), fun x => ?_⟩
  have ha1 : -(π / 2) < arctan (f x) := neg_pi_div_two_lt_arctan _
  have ha2 : arctan (f x) < π / 2 := arctan_lt_pi_div_two _
  have hδt : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hHt : Tendsto (fun j => H j x) atTop (𝓝 (arctan (f x))) := by
    have := ((tendsto_const_nhds (x := -(π / 2))).add hδt).max
      (((tendsto_const_nhds (x := π / 2)).sub hδt).min (hGt x))
    simp only [Function.comp_apply, add_zero, sub_zero] at this
    rwa [min_eq_right ha2.le, max_eq_right ha1.le] at this
  have htan : ContinuousAt tan (arctan (f x)) :=
    continuousOn_tan_Ioo.continuousAt (Ioo_mem_nhds ha1 ha2)
  have := htan.tendsto.comp hHt
  rwa [tan_arctan] at this

/-- On the whole space, real functions of class `F_σ` are Baire-one. -/
theorem IsFσMeasurable.isBaireOne_real {f : M → ℝ} (hf : IsFσMeasurable f) : IsBaireOne f := by
  obtain ⟨F, hFc, hFt⟩ := approx_real (L := univ) (hf.comp_continuous continuous_subtype_val)
  exact ⟨F, hFc, fun y => hFt ⟨y, mem_univ y⟩⟩

/-- **Diss. Lemma 6.** For `f : L → ℝ^m` with `L ⊆ M`, the following are equivalent: `f` is
Baire-one; `f` is of class `F_σ`; `f` is, on `L`, the pointwise limit of continuous maps
`M → ℝ^m`. -/
theorem baireOne_tfae {L : Set M} {m : ℕ} (f : L → (Fin m → ℝ)) :
    List.TFAE [IsBaireOne f, IsFσMeasurable f,
      ∃ F : ℕ → M → (Fin m → ℝ), (∀ n, Continuous (F n)) ∧
        ∀ x : L, Tendsto (fun n => F n x) atTop (𝓝 (f x))] := by
  tfae_have 1 → 2 := IsBaireOne.isFσMeasurable
  tfae_have 2 → 3 := fun hf => by
    choose F hFc hFt using fun i : Fin m =>
      approx_real (L := L) (Continuous.comp_isFσMeasurable (continuous_apply i) hf)
    exact ⟨fun n y i => F i n y, fun n => continuous_pi fun i => hFc i n,
      fun x => tendsto_pi_nhds.2 fun i => hFt i x⟩
  tfae_have 3 → 1 := fun ⟨F, hFc, hFt⟩ =>
    ⟨fun n x => F n x, fun n => (hFc n).comp continuous_subtype_val, hFt⟩
  tfae_finish

/-! ## Uniform limits (blueprint `lem:uniform-limit-fsigma`) -/

/-- A uniform limit of functions of class `F_σ` (into a pseudometric space) is of class `F_σ`. -/
theorem IsFσMeasurable.of_tendstoUniformly {X : Type*} [TopologicalSpace X] {Y : Type*}
    [PseudoMetricSpace Y] {S : ℕ → X → Y} {F : X → Y} (hS : ∀ n, IsFσMeasurable (S n))
    (hF : TendstoUniformly S F atTop) : IsFσMeasurable F := by
  intro U hU
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  have hn : ∀ k, ∃ n, ∀ x, dist (F x) (S n x) < ε k := fun k =>
    ((Metric.tendstoUniformly_iff.1 hF _ (hε k)).exists)
  choose n hn using hn
  let V : ℕ → Set Y := fun k =>
    ⋃ (z : Y) (_ : Metric.ball z (3 * ε k) ⊆ U), Metric.ball z (ε k)
  have hV : ∀ k, IsOpen (V k) := fun k =>
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball
  have key : F ⁻¹' U = ⋃ k, S (n k) ⁻¹' V k := by
    ext x
    simp only [mem_preimage, mem_iUnion, V, exists_prop, Metric.mem_ball]
    constructor
    · intro hx
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU _ hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hr (by norm_num : (0 : ℝ) < 3))
      refine ⟨k, F x, ?_, by rw [dist_comm]; exact hn k x⟩
      refine (Metric.ball_subset_ball ?_).trans hrU
      have : ε k < r / 3 := hk
      linarith
    · rintro ⟨k, z, hzU, hz⟩
      apply hzU
      rw [Metric.mem_ball]
      have := dist_triangle (F x) (S (n k) x) z
      have := hn k x
      have := hε k
      linarith
  rw [key]
  exact IsFσ.iUnion fun k => hS (n k) _ (hV k)

/-! ## Extension of Baire-one functions (blueprint `thm:extension`) -/

/-- A finitely valued real function of class `F_σ` on a `G_δ` subset `L` extends to a finitely
valued function of class `F_σ` on `M`, with the same bound. -/
theorem exists_extend_finiteValued {L : Set M} (hL : IsGδ L) {h : L → ℝ}
    (hh : IsFσMeasurable h) (hfin : (range h).Finite) {b : ℝ} (hb : 0 ≤ b)
    (hbd : ∀ x, |h x| ≤ b) :
    ∃ H : M → ℝ, IsFσMeasurable H ∧ (range H).Finite ∧ (∀ y, |H y| ≤ b) ∧
      ∀ x : L, H x = h x := by
  choose P hP hPE using fun a : range h =>
    isFσ_subtype_iff.1 (finiteValued_ambiguous hh hfin (a : ℝ)).1
  have := hfin.to_subtype
  let Q : Option (range h) → Set M := fun o => o.elim Lᶜ P
  have hQ : ∀ o, IsFσ (Q o) := by
    rintro (_ | a)
    · exact IsGδ.isFσ_compl hL
    · exact hP a
  obtain ⟨R, hR, hRQ, hdisj, hcovR, -⟩ := reduction_finite hQ
  have hcovQ : ⋃ o, Q o = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    by_cases hy : y ∈ L
    · refine ⟨some ⟨h ⟨y, hy⟩, ⟨y, hy⟩, rfl⟩, ?_⟩
      show y ∈ P _
      have h2 : (⟨y, hy⟩ : L) ∈ h ⁻¹' {((⟨h ⟨y, hy⟩, ⟨y, hy⟩, rfl⟩ : range h) : ℝ)} := rfl
      rw [hPE] at h2
      exact h2
    · exact ⟨none, hy⟩
  have hcov : ⋃ o, R o = univ := hcovR.trans hcovQ
  let v : Option (range h) → ℝ := fun o => o.elim 0 Subtype.val
  have hv : ∀ o, |v o| ≤ b := by
    rintro (_ | ⟨_, x, rfl⟩)
    · simpa [v] using hb
    · exact hbd x
  obtain ⟨H, hHv, hHF, hHr⟩ := exists_piecewise_of_partition hR hdisj hcov v
  refine ⟨H, hHF, (finite_range v).subset hHr, fun y => ?_, fun x => ?_⟩
  · obtain ⟨o, ho⟩ := hHr ⟨y, rfl⟩
    rw [← ho]
    exact hv o
  · obtain ⟨o, ho⟩ := mem_iUnion.1 (hcov ▸ mem_univ (x : M) : (x : M) ∈ ⋃ o, R o)
    rw [hHv o _ ho]
    rcases o with _ | a
    · exact absurd x.2 (hRQ none ho)
    · have hxP : (x : M) ∈ P a := hRQ (some a) ho
      have : x ∈ h ⁻¹' {(a : ℝ)} := by rw [hPE]; exact hxP
      exact (this : h x = a).symm

/-- Partial sums of finitely valued functions of class `F_σ` are finitely valued of class
`F_σ`. -/
theorem isFσMeasurable_finiteValued_sum {X : Type*} [TopologicalSpace X] {H : ℕ → X → ℝ}
    (hH : ∀ n, IsFσMeasurable (H n)) (hfin : ∀ n, (range (H n)).Finite) (N : ℕ) :
    IsFσMeasurable (fun y => ∑ n ∈ Finset.range N, H n y) ∧
      (range fun y => ∑ n ∈ Finset.range N, H n y).Finite := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact ⟨isFσMeasurable_const 0, (finite_singleton 0).subset (range_const_subset)⟩
  | succ N ih =>
    have e : (fun y => ∑ n ∈ Finset.range (N + 1), H n y) =
        (fun y => ∑ n ∈ Finset.range N, H n y) + H N := by
      funext y
      simp [Finset.sum_range_succ]
    rw [e]
    exact IsFσMeasurable.add_of_finite ih.1 (hH N) ih.2 (hfin N)

/-- Bounded real functions of class `F_σ` on a `G_δ` subset extend to bounded Baire-one
functions on `M`. -/
theorem exists_extend_of_isGδ_real {L : Set M} (hL : IsGδ L) {f : L → ℝ}
    (hf : IsFσMeasurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∃ F : M → ℝ, IsBaireOne F ∧ (∃ C', ∀ y, |F y| ≤ C') ∧ ∀ x : L, F x = f x := by
  obtain ⟨h, b, hh, hfin, hb0, hbs, hbd, hsum⟩ := exists_hasSum_finiteValued hf hC
  choose H hHF hHfin hHb hHe using fun n =>
    exists_extend_finiteValued hL (hh n) (hfin n) (hb0 n) (hbd n)
  have hHb' : ∀ n y, ‖H n y‖ ≤ b n := hHb
  refine ⟨fun y => ∑' n, H n y, IsFσMeasurable.isBaireOne_real ?_,
    ⟨∑' n, b n, fun y => tsum_of_norm_bounded hbs.hasSum fun n => hHb' n y⟩, fun x => ?_⟩
  · exact IsFσMeasurable.of_tendstoUniformly
      (fun N => (isFσMeasurable_finiteValued_sum hHF hHfin N).1) (tendstoUniformly_tsum_nat hbs hHb')
  · simp only [hHe]
    exact (hsum x).tsum_eq

/-- **Extension from `G_δ` sets.** A bounded Baire-one map `L → ℝ^m` on a `G_δ` subset `L ⊆ M`
extends to a bounded Baire-one map `M → ℝ^m`. -/
theorem IsBaireOne.extend_of_isGδ {L : Set M} (hL : IsGδ L) {m : ℕ} {f : L → (Fin m → ℝ)}
    (hf : IsBaireOne f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ F : M → (Fin m → ℝ), IsBaireOne F ∧ (∃ C, ∀ y, ‖F y‖ ≤ C) ∧ ∀ x : L, F x = f x := by
  obtain ⟨C, hC⟩ := hbdd
  have hfF := hf.isFσMeasurable
  choose F hFB hFC hFe using fun i : Fin m =>
    exists_extend_of_isGδ_real hL (Continuous.comp_isFσMeasurable (continuous_apply i) hfF)
      (C := C) fun x => (norm_le_pi_norm (f x) i).trans (hC x)
  choose C' hC' using hFC
  refine ⟨fun y i => F i y, isBaireOne_pi hFB, ⟨∑ i, |C' i|, fun y => ?_⟩,
    fun x => funext fun i => hFe i x⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact (hC' i y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |C' j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))

open Real in
/-- Real Baire-one (equivalently, class `F_σ`) functions on a co-countable subset of a `T₁`
perfectly normal space extend to Baire-one functions on the whole space. -/
theorem exists_extend_of_countable_compl_real [T1Space M] {L : Set M} (hL : Lᶜ.Countable)
    {f : L → ℝ} (hf : IsFσMeasurable f) : ∃ F : M → ℝ, IsBaireOne F ∧ ∀ x : L, F x = f x := by
  have hLG : IsGδ L := isFσ_compl_iff.1 (Set.Countable.isFσ hL)
  obtain ⟨G, hGB, -, hGe⟩ := exists_extend_of_isGδ_real hLG
    (Continuous.comp_isFσMeasurable continuous_arctan hf) (C := π / 2)
    (fun x => (abs_lt.2 ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩).le)
  have hGF := hGB.isFσMeasurable
  let I : Set ℝ := Ioo (-(π / 2)) (π / 2)
  have hGL : ∀ x : L, G x ∈ I := fun x => by
    rw [hGe x]
    exact ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩
  have hZ : (G ⁻¹' Iᶜ).Countable := hL.mono fun y hy hyL => hy (hGL ⟨y, hyL⟩)
  classical
  let F : M → ℝ := fun y => if G y ∈ I then tan (G y) else 0
  refine ⟨F, IsFσMeasurable.isBaireOne_real fun U hU => ?_, fun x => ?_⟩
  · have e : F ⁻¹' U = G ⁻¹' (I ∩ tan ⁻¹' U) ∪ {y | G y ∉ I ∧ (0 : ℝ) ∈ U} := by
      ext y
      simp only [F, mem_preimage, mem_union, mem_inter_iff]
      split_ifs with hy <;> simp [hy]
    rw [e]
    refine (hGF _ (continuousOn_tan_Ioo.isOpen_inter_preimage isOpen_Ioo hU)).union ?_
    exact Set.Countable.isFσ (hZ.mono fun y hy => hy.1)
  · simp only [F, if_pos (hGL x), hGe x, Function.comp_apply, tan_arctan]

/-- **Extension from co-countable sets.** A Baire-one map `L → ℝ^m` on a subset `L` of a `T₁`
perfectly normal (e.g. metrizable) space `M` with countable complement extends to a Baire-one map
`M → ℝ^m`. -/
theorem IsBaireOne.extend_of_countable_compl [T1Space M] {L : Set M} (hL : Lᶜ.Countable)
    {m : ℕ} {f : L → (Fin m → ℝ)} (hf : IsBaireOne f) :
    ∃ F : M → (Fin m → ℝ), IsBaireOne F ∧ ∀ x : L, F x = f x := by
  have hfF := hf.isFσMeasurable
  choose F hFB hFe using fun i : Fin m =>
    exists_extend_of_countable_compl_real hL
      (Continuous.comp_isFσMeasurable (continuous_apply i) hfF)
  exact ⟨fun y i => F i y, isBaireOne_pi hFB, fun x => funext fun i => hFe i x⟩

end Approx

end TJK
