/-
Copyright: the TJK formalization project.

Section B of the blueprint (`paper/sections/B-baire.tex`): proofs of the two imported facts
`fact:banach` and `fact:borel-baire` of `TJK.Baire.Higher`.

Route (a variant of Banach 1931 / Kuratowski, Topology I, §31):

* `exists_tendsto_finiteValued_lower` (the heart, needs only `Y` separable): for `ξ ≥ 2`, a map of
  class `P^{ξ+1}` is the pointwise limit of finitely-valued maps `g m` all of whose preimages lie in
  `P^{β m + 1}` (hence are ambiguous of class `β m + 1`) with `1 ≤ β m < ξ`. Construction: write
  each `f⁻¹(B(y_k, 1/(n+1)))` as `⋃_j C n k j` with `C n k j ∈ Q^ξ`, approximate each `C n k j`
  from above by a decreasing sequence of sets of lower additive classes
  (`MulClass.exists_antitone_approx`), and let `g m x` be the centre chosen by a finite
  "consistent chain" priority rule at stage `m`.
* `baireClass_one_of_finite` (needs only path-connectedness): a finitely-valued map with `F_σ`
  preimages is `p ∘ h` with `h` real-valued finitely-valued `F_σ`-measurable (hence Baire-one by
  `TJK.Baire.Approx`) and `p : ℝ → Y` a path through the finitely many values.
* `baireClass_of_finite_addClass` by well-founded induction on `ξ ≥ 1`, then Banach.
* Borel measurable sets have countable class (`MeasurableSet.exists_addClass_mulClass`); a
  countable basis and `Ordinal.iSup_lt_omega_one` give the class of a Borel map; then Banach.

In particular local path-connectedness of `Y` is not needed, and `ξ ≥ 2` suffices.
-/
import Mathlib
import TJK.Defs
import TJK.Baire.Basic
import TJK.Baire.Approx
import TJK.Baire.Higher

open _root_.Set Filter Topology Function TopologicalSpace

namespace TJK

section Aux

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

/-- Postcomposition with a continuous map keeps the Baire class. -/
theorem Continuous.comp_baireClass {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hg : Continuous g) {ξ : Ordinal.{0}} {f : X → Y} (hf : BaireClass ξ f) :
    BaireClass ξ (g ∘ f) := by
  induction hf with
  | zero hc => exact .zero (hg.comp hc)
  | @lim ξ f η F hξ hη _ hlim ih =>
    exact .lim η (fun n => g ∘ F n) hξ hη ih fun x => (hg.tendsto _).comp (hlim x)

/-- `P^ξ` is closed under finite intersections indexed by a finset. -/
theorem AddClass.biInter_finset [PerfectlyNormalSpace X] {ι : Type*} {ξ : Ordinal.{0}}
    (t : Finset ι) {s : ι → Set X} (hs : ∀ i ∈ t, AddClass ξ (s i)) (hξ : 1 ≤ ξ) :
    AddClass ξ (⋂ i ∈ t, s i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using addClass_univ hξ
  | insert a t _ ih =>
    rw [Finset.set_biInter_insert]
    exact (hs a (Finset.mem_insert_self _ _)).inter
      (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

/-- `P^ξ` is closed under finite intersections. -/
theorem AddClass.iInter_finite [PerfectlyNormalSpace X] {ι : Type*} [Fintype ι] {ξ : Ordinal.{0}}
    {s : ι → Set X} (hs : ∀ i, AddClass ξ (s i)) (hξ : 1 ≤ ξ) : AddClass ξ (⋂ i, s i) := by
  have := AddClass.biInter_finset (Finset.univ : Finset ι) (fun i _ => hs i) hξ
  simpa using this

/-- A continuous map `ℝ → Y` through finitely many prescribed points of a path-connected space. -/
theorem exists_continuous_through [PathConnectedSpace Y] (y : ℕ → Y) (N : ℕ) :
    ∃ p : ℝ → Y, Continuous p ∧ ∀ i ≤ N, p i = y i := by
  induction N with
  | zero => exact ⟨fun _ => y 0, continuous_const, fun i hi => by rw [Nat.le_zero.1 hi]⟩
  | succ N ih =>
    obtain ⟨p, hp, hpy⟩ := ih
    let γ : Path (y N) (y (N + 1)) := (PathConnectedSpace.joined _ _).somePath
    refine ⟨fun t => if t ≤ (N : ℝ) then p t else γ.extend (t - N), ?_, ?_⟩
    · refine Continuous.if_le hp (γ.continuous_extend.comp (continuous_id.sub continuous_const))
        continuous_id continuous_const fun t ht => ?_
      simp [ht, hpy N le_rfl]
    · intro i hi
      rcases Nat.lt_or_eq_of_le hi with h | rfl
      · have h' : i ≤ N := Nat.lt_succ_iff.1 h
        have : (i : ℝ) ≤ N := by exact_mod_cast h'
        simp [this, hpy i h']
      · have : ¬ ((N + 1 : ℕ) : ℝ) ≤ N := by push_cast; linarith
        simp only [this, if_false]
        push_cast
        simp

end Aux

/-! ## Finitely-valued maps with `F_σ` pieces are Baire-one -/

section BaireOne

variable {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]
  {Y : Type*} [TopologicalSpace Y] [PathConnectedSpace Y]

/-- A finitely-valued map into a path-connected space all of whose preimages are `F_σ` is of Baire
class one. -/
theorem baireClass_one_of_finite {g : X → Y} (hfin : (range g).Finite)
    (hg : ∀ s : Set Y, AddClass 2 (g ⁻¹' s)) : BaireClass 1 g := by
  classical
  have := hfin.to_subtype
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (range g)
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  let y : ℕ → Y := fun i => if h : i < N then (e.symm ⟨i, h⟩).1 else y₀
  let idx : X → ℕ := fun x => e ⟨g x, mem_range_self x⟩
  have hy : ∀ x, y (idx x) = g x := by
    intro x
    simp [y, idx]
  obtain ⟨p, hp, hpy⟩ := exists_continuous_through y N
  let h : X → ℝ := fun x => (idx x : ℝ)
  have hgh : g = p ∘ h := by
    funext x
    simp only [comp_apply, h]
    rw [hpy _ (e ⟨g x, mem_range_self x⟩).2.le, hy]
  have hh : IsFσMeasurable h := by
    intro U _
    have : h ⁻¹' U = g ⁻¹' {z | ∃ hz : z ∈ range g, ((e ⟨z, hz⟩ : ℕ) : ℝ) ∈ U} := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq, h, idx]
      exact ⟨fun hx => ⟨mem_range_self x, hx⟩, fun ⟨_, hx⟩ => hx⟩
    rw [this]
    exact addClass_two_iff.1 (hg _)
  obtain ⟨F, hFc, hFt⟩ := hh.isBaireOne_real
  rw [hgh]
  exact .lim (fun _ => 0) (fun n => p ∘ F n) one_pos (fun _ => zero_lt_one)
    (fun n => .zero (hp.comp (hFc n))) fun x => (hp.tendsto _).comp (hFt x)

end BaireOne

/-! ## Approximation of multiplicative classes from above -/

section Approx

variable {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]

/-- For `ξ > 1`, a member of `Q^ξ` is the intersection of a decreasing sequence of sets of additive
classes `γ m` with `1 ≤ γ m < ξ`. -/
theorem MulClass.exists_antitone_approx {ξ : Ordinal.{0}} {s : Set X} (h : MulClass ξ s)
    (hξ : 1 < ξ) :
    ∃ (γ : ℕ → Ordinal.{0}) (E : ℕ → Set X), (∀ m, 1 ≤ γ m ∧ γ m < ξ) ∧
      (∀ m, AddClass (γ m) (E m)) ∧ Antitone E ∧ ⋂ m, E m = s := by
  have h' : AddMulClass false ξ s := h
  cases h' with
  | isClosed _ => exact absurd hξ (lt_irrefl _)
  | @iInter _ ι _ η t _ hη ht =>
    cases isEmpty_or_nonempty ι with
    | inl _ =>
      refine ⟨fun _ => 1, fun _ => univ, fun _ => ⟨le_rfl, hξ⟩, fun _ => addClass_univ le_rfl,
        fun _ _ _ => le_rfl, ?_⟩
      simp
    | inr _ =>
      obtain ⟨e, he⟩ := exists_surjective_nat ι
      let β : ℕ → Ordinal.{0} := fun n => max 1 (η (e n))
      have hβ1 : ∀ m, 1 ≤ (Finset.range (m + 1)).sup β := fun m =>
        (le_max_left _ _).trans (Finset.le_sup (f := β) (Finset.mem_range.2 (Nat.succ_pos m)))
      refine ⟨fun m => (Finset.range (m + 1)).sup β, fun m => ⋂ i ∈ Finset.range (m + 1), t (e i),
        fun m => ⟨hβ1 m, ?_⟩, fun m => ?_, ?_, ?_⟩
      · refine (Finset.sup_lt_iff (by rw [Ordinal.bot_eq_zero]; exact zero_lt_one.trans hξ)).2
          fun i _ => max_lt hξ (hη _)
      · refine AddClass.biInter_finset _ (fun i hi => ?_) (hβ1 m)
        exact AddClass.mono (ht (e i)) ((le_max_right _ _).trans (Finset.le_sup (f := β) hi))
      · intro a b hab
        refine subset_iInter₂ fun i hi => iInter₂_subset i (Finset.mem_range.2 ?_)
        have := Finset.mem_range.1 hi
        omega
      · apply Subset.antisymm
        · refine subset_iInter fun i => ?_
          obtain ⟨n, rfl⟩ := he i
          exact (iInter_subset _ n).trans (iInter₂_subset n (Finset.mem_range.2 n.lt_succ_self))
        · exact subset_iInter fun m => subset_iInter₂ fun i _ => iInter_subset _ _

end Approx

/-! ## Finitely-valued maps determined by finitely many sets -/

section Pieces

variable {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X] {Y : Type*}

open Classical in
/-- A map that factors through the membership pattern of `x` in finitely many sets of class `P^δ`
has finite range, and all its preimages are of class `P^{δ+1}`. -/
theorem addClass_preimage_comp_pattern {δ : Ordinal.{0}} (hδ : 1 ≤ δ) {N : ℕ}
    {E : Fin N → Set X} (hE : ∀ i, AddClass δ (E i)) (Φ : (Fin N → Bool) → Y) :
    (range fun x => Φ fun i => decide (x ∈ E i)).Finite ∧
      ∀ s : Set Y, AddClass (δ + 1) ((fun x => Φ fun i => decide (x ∈ E i)) ⁻¹' s) := by
  classical
  refine ⟨(finite_range Φ).subset (range_comp_subset_range _ Φ), fun s => ?_⟩
  have h1 : (1 : Ordinal.{0}) ≤ δ + 1 := hδ.trans (Order.le_succ δ)
  have hpiece : ∀ w : Fin N → Bool, AddClass (δ + 1) (⋂ i, {x | decide (x ∈ E i) = w i}) := by
    intro w
    refine AddClass.iInter_finite (fun i => ?_) h1
    cases hw : w i
    · have : {x | decide (x ∈ E i) = false} = (E i)ᶜ := by ext x; simp
      rw [this]
      exact MulClass.addClass_of_lt (addClass_iff_compl.1 (hE i)) (lt_add_one δ)
    · have : {x | decide (x ∈ E i) = true} = E i := by ext x; simp
      rw [this]
      exact (hE i).addClass_of_lt (lt_add_one δ)
  have : (fun x => Φ fun i => decide (x ∈ E i)) ⁻¹' s =
      ⋃ w : {w : Fin N → Bool // Φ w ∈ s}, ⋂ i, {x | decide (x ∈ E i) = w.1 i} := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_iInter, mem_ofPred_eq]
    exact ⟨fun hx => ⟨⟨_, hx⟩, fun i => rfl⟩, fun ⟨w, hw⟩ => by
      have : (fun i => decide (x ∈ E i)) = w.1 := funext hw
      rw [this]; exact w.2⟩
  rw [this]
  exact AddClass.iUnion (fun w => hpiece w.1) h1

end Pieces

/-! ## The heart: pointwise approximation by finitely-valued maps of lower class -/

section Select

variable {Y : Type*} [MetricSpace Y]

/-- At stage `m`, for the pattern `P`, the least index `t ≤ m` of level `n` with `P t`. -/
def selectAt (lvl : ℕ → ℕ) (m : ℕ) (P : ℕ → Bool) (n : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? fun t => decide (lvl t = n) && P t

theorem selectAt_congr (lvl : ℕ → ℕ) (m : ℕ) {P Q : ℕ → Bool} (h : ∀ t ≤ m, P t = Q t) :
    selectAt lvl m P = selectAt lvl m Q := by
  funext n
  refine List.find?_congr fun t ht => ?_
  rw [h t (Nat.lt_succ_iff.1 (List.mem_range.1 ht))]

theorem selectAt_eq_some_iff {lvl : ℕ → ℕ} {m : ℕ} {P : ℕ → Bool} {n t : ℕ} :
    selectAt lvl m P n = some t ↔
      (lvl t = n ∧ P t = true) ∧ t ≤ m ∧ ∀ t' < t, ¬ (lvl t' = n ∧ P t' = true) := by
  rw [selectAt, List.find?_range_eq_some, List.mem_range, Nat.lt_succ_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_and, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_and]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun j _ => ?_
  cases P j <;> simp

/-- The selections at levels `≤ n` form a consistent chain ending at level `n`. -/
def ChainGood (ctr : ℕ → Y) (s : ℕ → Option ℕ) (n : ℕ) : Prop :=
  ∀ n' ≤ n, ∃ t t', s n' = some t ∧ s n = some t' ∧
    dist (ctr t) (ctr t') < 1 / ((n' : ℝ) + 1) + 1 / ((n : ℝ) + 1)

open Classical in
/-- The value at stage `m`: the centre selected at the largest level `≤ m` ending a consistent
chain (`y₀` if there is none). -/
noncomputable def chainValue (ctr : ℕ → Y) (y₀ : Y) (m : ℕ) (s : ℕ → Option ℕ) : Y :=
  ((s (Nat.findGreatest (ChainGood ctr s) m)).map ctr).getD y₀

open Classical in
/-- Convergence of the chain selection. -/
theorem tendsto_chainValue {X : Type*} {f : X → Y} {lvl : ℕ → ℕ} {ctr : ℕ → Y} (y₀ : Y)
    {C : ℕ → Set X} {E : ℕ → ℕ → Set X} (hE : ∀ t, Antitone (E t))
    (hEC : ∀ t, ⋂ m, E t m = C t)
    (hC : ∀ t x, x ∈ C t → dist (f x) (ctr t) < 1 / ((lvl t : ℝ) + 1))
    (hcov : ∀ x n, ∃ t, lvl t = n ∧ x ∈ C t) (x : X) :
    Tendsto (fun m => chainValue ctr y₀ m (selectAt lvl m fun t => decide (x ∈ E t m))) atTop
      (𝓝 (f x)) := by
  set P : ℕ → ℕ → Bool := fun m t => decide (x ∈ E t m) with hP
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 / ((N : ℝ) + 1) < ε := by
    obtain ⟨N, hN⟩ := exists_nat_gt (3 / ε)
    refine ⟨N, (div_lt_iff₀ (by positivity)).2 ?_⟩
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  have hex : ∀ n, ∃ t, lvl t = n ∧ x ∈ C t := hcov x
  set ts : ℕ → ℕ := fun n => Nat.find (hex n) with hts_def
  have hts : ∀ n, lvl (ts n) = n ∧ x ∈ C (ts n) := fun n => Nat.find_spec (hex n)
  have hmin : ∀ n, ∀ t < ts n, lvl t = n → x ∉ C t := fun n t ht hl hx =>
    Nat.find_min (hex n) ht ⟨hl, hx⟩
  have hout : ∀ t, ∀ᶠ m in atTop, x ∉ C t → x ∉ E t m := by
    intro t
    by_cases hxt : x ∈ C t
    · exact Eventually.of_forall fun _ h => absurd hxt h
    · rw [← hEC t, mem_iInter, not_forall] at hxt
      obtain ⟨m0, hm0⟩ := hxt
      exact eventually_atTop.2 ⟨m0, fun m hm _ hxm => hm0 (hE t hm hxm)⟩
  set T := (Finset.range (N + 1)).sup ts with hT
  have hev := (eventually_all_finset (Finset.range (T + 1))).2 fun t _ => hout t
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine ⟨max M (T + N), fun m hm => ?_⟩
  have hMm : M ≤ m := (le_max_left _ _).trans hm
  have hTm : T ≤ m := (Nat.le_add_right _ _).trans ((le_max_right _ _).trans hm)
  have hNm : N ≤ m := (Nat.le_add_left _ _).trans ((le_max_right _ _).trans hm)
  have htsT : ∀ n ≤ N, ts n ≤ T := fun n hn =>
    Finset.le_sup (f := ts) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
  -- at stage `m`, the selection at each level `n ≤ N` is the true one
  have hsel : ∀ n ≤ N, selectAt lvl m (P m) n = some (ts n) := by
    intro n hn
    rw [selectAt_eq_some_iff]
    refine ⟨⟨(hts n).1, ?_⟩, (htsT n hn).trans hTm, fun t' ht' ⟨hl, hPt⟩ => ?_⟩
    · simp only [hP, decide_eq_true_eq]
      have := (hts n).2
      rw [← hEC] at this
      exact mem_iInter.1 this m
    · simp only [hP, decide_eq_true_eq] at hPt
      exact hM m hMm t' (Finset.mem_range.2 (Nat.lt_succ_of_le
        ((ht'.le.trans (htsT n hn)))))
        (hmin n t' ht' hl) hPt
  have hdist : ∀ n, dist (ctr (ts n)) (f x) < 1 / ((n : ℝ) + 1) := fun n => by
    rw [dist_comm]; simpa [(hts n).1] using hC _ x (hts n).2
  have hgood : ChainGood ctr (selectAt lvl m (P m)) N := by
    intro n' hn'
    refine ⟨ts n', ts N, hsel n' hn', hsel N le_rfl, ?_⟩
    calc dist (ctr (ts n')) (ctr (ts N))
        ≤ dist (ctr (ts n')) (f x) + dist (ctr (ts N)) (f x) := dist_triangle_right _ _ _
      _ < _ := add_lt_add (hdist n') (hdist N)
  classical
  set L := Nat.findGreatest (ChainGood ctr (selectAt lvl m (P m))) m with hL
  have hNL : N ≤ L := Nat.le_findGreatest hNm hgood
  have hgL : ChainGood ctr (selectAt lvl m (P m)) L := Nat.findGreatest_spec hNm hgood
  obtain ⟨t, t', ht, ht', hd⟩ := hgL N hNL
  rw [hsel N le_rfl, Option.some_inj] at ht
  subst ht
  have hval : chainValue ctr y₀ m (selectAt lvl m (P m)) = ctr t' := by
    rw [chainValue]
    convert congrArg (fun o => (Option.map ctr o).getD y₀) ht'
    rfl
  rw [hval]
  have hLN : 1 / ((L : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hNL 1)
  calc dist (ctr t') (f x) ≤ dist (ctr (ts N)) (ctr t') + dist (ctr (ts N)) (f x) :=
        dist_triangle_left _ _ _
    _ < (1 / ((N : ℝ) + 1) + 1 / ((L : ℝ) + 1)) + 1 / ((N : ℝ) + 1) := add_lt_add hd (hdist N)
    _ ≤ 3 / ((N : ℝ) + 1) := by
        have : 3 / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by
          ring
        linarith
    _ < ε := hN

end Select

section Main

variable {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]
  {Y : Type*} [MetricSpace Y] [SeparableSpace Y] [Nonempty Y]

/-- A member of `P^{ξ+1}`, `ξ ≥ 1`, is a countable union of members of `Q^ξ`, indexed by `ℕ`. -/
theorem AddClass.exists_nat_mulClass {ξ : Ordinal.{0}} {s : Set X} (h : AddClass (ξ + 1) s)
    (hξ : 1 ≤ ξ) : ∃ C : ℕ → Set X, (∀ j, MulClass ξ (C j)) ∧ s = ⋃ j, C j := by
  obtain ⟨κ, _, η, t, hη, ht, rfl⟩ :=
    AddMulClass.exists_iUnion h (hξ.trans_lt (lt_add_one ξ))
  cases isEmpty_or_nonempty κ with
  | inl _ => exact ⟨fun _ => ∅, fun _ => mulClass_empty hξ, by simp⟩
  | inr _ =>
    obtain ⟨e, he⟩ := exists_surjective_nat κ
    refine ⟨fun j => t (e j), fun j => MulClass.mono (ht (e j))
      (Order.lt_add_one_iff.1 (hη (e j))), ?_⟩
    exact (he.iUnion_comp t).symm

/-- Step 1: a dense sequence `y` and sets `C n k j ∈ Q^ξ` with
`f⁻¹(B(y k, 1/(n+1))) = ⋃_j C n k j`. -/
theorem exists_mulClass_cover {ξ : Ordinal.{0}} (hξ : 1 ≤ ξ) {f : X → Y}
    (hf : IsAddClassMeasurable (ξ + 1) f) :
    ∃ (y : ℕ → Y) (C : ℕ → ℕ → ℕ → Set X), (∀ n k j, MulClass ξ (C n k j)) ∧
      (∀ n k j x, x ∈ C n k j → dist (f x) (y k) < 1 / ((n : ℝ) + 1)) ∧
      ∀ x n, ∃ k j, x ∈ C n k j := by
  obtain ⟨y, hy⟩ := TopologicalSpace.exists_dense_seq Y
  choose C hC hCU using fun (n k : ℕ) =>
    AddClass.exists_nat_mulClass (hf (Metric.ball (y k) (1 / ((n : ℝ) + 1))) Metric.isOpen_ball) hξ
  refine ⟨y, C, hC, fun n k j x hx => ?_, fun x n => ?_⟩
  · have : x ∈ f ⁻¹' Metric.ball (y k) (1 / ((n : ℝ) + 1)) := by
      rw [hCU n k]; exact mem_iUnion.2 ⟨j, hx⟩
    exact this
  · obtain ⟨k, hk⟩ := hy.exists_dist_lt (f x) (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    have : x ∈ f ⁻¹' Metric.ball (y k) (1 / ((n : ℝ) + 1)) := hk
    rw [hCU n k] at this
    obtain ⟨j, hj⟩ := mem_iUnion.1 this
    exact ⟨k, j, hj⟩

/-- For `ξ ≥ 2`, a map of class `P^{ξ+1}` into a separable metric space is the pointwise limit of
finitely-valued maps `g m` whose preimages are of class `P^{β m + 1}`, `1 ≤ β m < ξ`. -/
theorem exists_tendsto_finiteValued_lower {ξ : Ordinal.{0}} (hξ : 2 ≤ ξ) {f : X → Y}
    (hf : IsAddClassMeasurable (ξ + 1) f) :
    ∃ (β : ℕ → Ordinal.{0}) (g : ℕ → X → Y), (∀ m, 1 ≤ β m ∧ β m < ξ) ∧
      (∀ m, (range (g m)).Finite) ∧ (∀ m (s : Set Y), AddClass (β m + 1) (g m ⁻¹' s)) ∧
      ∀ x, Tendsto (fun m => g m x) atTop (𝓝 (f x)) := by
  classical
  have h1ξ : 1 < ξ := one_lt_two.trans_le hξ
  obtain ⟨y, C, hCm, hCd, hcov⟩ := exists_mulClass_cover h1ξ.le hf
  let C' : ℕ → Set X := fun t =>
    C (Nat.unpair t).1 (Nat.unpair (Nat.unpair t).2).1 (Nat.unpair (Nat.unpair t).2).2
  choose γ E hγ hEc hEa hEi using fun t =>
    MulClass.exists_antitone_approx (hCm _ _ _ : MulClass ξ (C' t)) h1ξ
  let lvl : ℕ → ℕ := fun t => (Nat.unpair t).1
  let ctr : ℕ → Y := fun t => y (Nat.unpair (Nat.unpair t).2).1
  let δ : ℕ → Ordinal.{0} := fun m => (Finset.range (m + 1)).sup fun t => γ t m
  have hδ1 : ∀ m, 1 ≤ δ m := fun m =>
    (hγ 0 m).1.trans (Finset.le_sup (f := fun t => γ t m) (Finset.mem_range.2 m.succ_pos))
  have hδξ : ∀ m, δ m < ξ := fun m =>
    (Finset.sup_lt_iff (by rw [Ordinal.bot_eq_zero]; exact zero_lt_one.trans h1ξ)).2
      fun t _ => (hγ t m).2
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  let G : ℕ → X → Y := fun m x =>
    chainValue ctr y₀ m (selectAt lvl m fun t => decide (x ∈ E t m))
  let Φ : ∀ m, (Fin (m + 1) → Bool) → Y := fun m P =>
    chainValue ctr y₀ m (selectAt lvl m fun t => if h : t < m + 1 then P ⟨t, h⟩ else false)
  have hfac : ∀ m, G m = fun x => Φ m fun i => decide (x ∈ E i m) := by
    intro m
    funext x
    simp only [G, Φ]
    congr 1
    exact selectAt_congr lvl m fun t ht => by simp [Nat.lt_succ_of_le ht]
  have hpat := fun m => addClass_preimage_comp_pattern (hδ1 m) (E := fun i : Fin (m + 1) => E i m)
    (fun i => (hEc i m).mono (Finset.le_sup (f := fun t => γ t m) (Finset.mem_range.2 i.2)))
    (Φ m)
  refine ⟨δ, G, fun m => ⟨hδ1 m, hδξ m⟩, fun m => ?_, fun m s => ?_, fun x => ?_⟩
  · rw [hfac m]; convert (hpat m).1
  · rw [hfac m]; convert (hpat m).2 s
  · refine tendsto_chainValue y₀ (C := C') hEa hEi (fun t x hx => hCd _ _ _ x hx)
      (fun x n => ?_) x
    obtain ⟨k, j, hkj⟩ := hcov x n
    exact ⟨Nat.pair n (Nat.pair k j), by simp, by simpa [C'] using hkj⟩

end Main

/-! ## Banach's theorem -/

section Banach

variable {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]
  {Y : Type*} [MetricSpace Y] [SeparableSpace Y] [PathConnectedSpace Y]

/-- A finitely-valued map all of whose preimages are of class `P^{ξ+1}`, `ξ ≥ 1`, into a separable
path-connected metric space is of Baire class `ξ`. -/
theorem baireClass_of_finite_addClass {ξ : Ordinal.{0}} (hξ : 1 ≤ ξ) {g : X → Y}
    (hfin : (range g).Finite) (hg : ∀ s : Set Y, AddClass (ξ + 1) (g ⁻¹' s)) :
    BaireClass ξ g := by
  induction ξ using WellFoundedLT.induction generalizing g with
  | _ ξ ih =>
  rcases hξ.eq_or_lt with rfl | hlt
  · exact baireClass_one_of_finite hfin (by simpa [one_add_one_eq_two] using hg)
  · have h2 : (2 : Ordinal.{0}) ≤ ξ := by
      rw [← one_add_one_eq_two]; exact Order.add_one_le_of_lt hlt
    obtain ⟨β, G, hβ, hGfin, hG, hGt⟩ :=
      exists_tendsto_finiteValued_lower h2 (f := g) fun U _ => hg U
    exact .lim β G (zero_lt_one.trans_le hξ) (fun m => (hβ m).2)
      (fun m => ih _ (hβ m).2 (hβ m).1 (hGfin m) (hG m)) hGt

end Banach

/-- **Banach (1931).** Same statement as `TJK.banach_baireClass_of_addClass`. -/
theorem banach_baireClass_of_addClass {M Y : Type*} [MetricSpace M] [MetricSpace Y]
    [SeparableSpace Y] [PathConnectedSpace Y] {ξ : Ordinal.{0}} (hξ : 2 ≤ ξ) {f : M → Y}
    (hf : IsAddClassMeasurable (ξ + 1) f) : BaireClass ξ f := by
  obtain ⟨β, G, hβ, hGfin, hG, hGt⟩ := exists_tendsto_finiteValued_lower hξ hf
  have h0 : (0 : Ordinal.{0}) < ξ := lt_of_lt_of_le (by norm_num) hξ
  exact .lim β G h0 (fun m => (hβ m).2)
    (fun m => baireClass_of_finite_addClass (hβ m).1 (hGfin m) (hG m)) hGt

/-! ## Borel measurable maps -/

section Borel

theorem two_lt_omega_one : (2 : Ordinal.{0}) < Ordinal.omega 1 :=
  (Ordinal.natCast_lt_omega0 2).trans Ordinal.omega0_lt_omega_one

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Every Borel set of a metric space belongs to `P^ξ ∩ Q^ξ` for some `ξ < ω₁`. -/
theorem MeasurableSet.exists_addClass_mulClass {s : Set M} (hs : MeasurableSet s) :
    ∃ ξ : Ordinal.{0}, ξ < Ordinal.omega 1 ∧ AddClass ξ s ∧ MulClass ξ s := by
  have hlim := Cardinal.isSuccLimit_omega.{0} 1
  have h2 : (2 : Ordinal.{0}) < Ordinal.omega 1 := two_lt_omega_one
  have hs' : @MeasurableSet M (MeasurableSpace.generateFrom {s : Set M | IsOpen s}) s := by
    have := BorelSpace.measurable_eq (α := M)
    rw [this] at hs
    exact hs
  refine MeasurableSpace.generateFrom_induction {s : Set M | IsOpen s}
    (fun s _ => ∃ ξ : Ordinal.{0}, ξ < Ordinal.omega 1 ∧ AddClass ξ s ∧ MulClass ξ s)
    ?_ ?_ ?_ ?_ s hs'
  · intro t ht _
    exact ⟨2, h2, (addClass_one_iff.2 ht).mono one_le_two, mulClass_two_iff.2 ht.isGδ⟩
  · exact ⟨2, h2, addClass_empty one_le_two, mulClass_empty one_le_two⟩
  · rintro t _ ⟨ξ, hξ, ha, hm⟩
    exact ⟨ξ, hξ, addClass_iff_compl.2 (by rwa [compl_compl]),
      mulClass_iff_compl.2 (by rwa [compl_compl])⟩
  · intro u _ ih
    choose ξ hξ ha hm using ih
    set ζ := max 1 (⨆ n, ξ n) with hζ
    have hζω : ζ < Ordinal.omega 1 :=
      max_lt (one_lt_two.trans h2) (Ordinal.iSup_lt_omega_one hξ)
    have hle : ∀ n, ξ n ≤ ζ := fun n =>
      (le_ciSup Ordinal.bddAbove_of_small n).trans (le_max_right _ _)
    have hU : AddClass (ζ + 1) (⋃ n, u n) :=
      AddMulClass.iUnion ξ u ((le_max_left _ _).trans_lt (lt_add_one ζ))
        (fun n => (hle n).trans_lt (lt_add_one ζ)) hm
    exact ⟨ζ + 1 + 1, hlim.add_one_lt (hlim.add_one_lt hζω),
      hU.mono (Order.le_succ _), hU.mulClass_of_lt (lt_add_one _)⟩

end Borel

/-- **Lebesgue–Hausdorff–Banach.** Same statement as `TJK.borel_measurable_exists_baireClass`. -/
theorem borel_measurable_exists_baireClass {M Y : Type*} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M] [MetricSpace Y] [SeparableSpace Y] [PathConnectedSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : M → Y} (hf : Measurable f) :
    ∃ ξ : Ordinal.{0}, ξ < Ordinal.omega 1 ∧ BaireClass ξ f := by
  have hlim := Cardinal.isSuccLimit_omega.{0} 1
  have h2 : (2 : Ordinal.{0}) < Ordinal.omega 1 := two_lt_omega_one
  have hb := isBasis_countableBasis Y
  have := (countable_countableBasis Y).to_subtype
  choose ξ hξ ha _ using fun B : countableBasis Y =>
    MeasurableSet.exists_addClass_mulClass (hf (hb.isOpen B.2).measurableSet)
  set ζ := max 2 (⨆ B, ξ B) with hζ
  have hle : ∀ B, ξ B ≤ ζ := fun B =>
    (le_ciSup Ordinal.bddAbove_of_small B).trans (le_max_right _ _)
  refine ⟨ζ, max_lt h2 (Ordinal.iSup_lt_omega_one hξ),
    banach_baireClass_of_addClass (le_max_left _ _) fun U hU => ?_⟩
  rw [hb.open_eq_sUnion' hU, preimage_sUnion, biUnion_eq_iUnion]
  have : Countable {t | t ∈ countableBasis Y ∧ t ⊆ U} :=
    ((countable_countableBasis Y).mono fun t ht => ht.1).to_subtype
  refine AddClass.iUnion (fun t => ?_) (one_le_two.trans ((le_max_left _ _).trans (Order.le_succ _)))
  exact (ha ⟨t.1, t.2.1⟩).mono ((hle _).trans (Order.le_succ _))

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
