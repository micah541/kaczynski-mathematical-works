import Mathlib
import TJK.Defs
import TJK.Construct.Special

/-!
# The dissertation's special families (blueprint appendix `app:variants`)

Formalizes `def:th-special`, `lem:th-special-implies`, `lem:th-lemma9`, `lem:th-lemma10` and
`lem:th-lemma11` of `paper/sections/Z-appendix.tex`. These results are not used elsewhere.

* `InGap F F'`: `F'` lies in a complementary interval of `F`, i.e. the closed interval between any
  two points of `F'` misses `F`. (For a closed `F` and nonempty `F'` this says that `F'` lies in one
  component of `ℝ \ F`; the empty set lies in a gap of every bounded `F`.)
* `IsThesisSpecial 𝓕`: `𝓕` has an enumeration `F 0, F 1, …` by bounded closed sets such that for
  `n < m`, `F m` lies in a complementary interval of `F n` or `F m` and `F n` split.
-/

namespace TJK.Variant

open _root_.Set TJK.Construct

/-- `F'` lies in a complementary interval of `F`. -/
def InGap (F F' : Set ℝ) : Prop :=
  ∀ x ∈ F', ∀ y ∈ F', Icc x y ⊆ Fᶜ

theorem InGap.disjoint {F F' : Set ℝ} (h : InGap F F') : Disjoint F F' :=
  disjoint_left.2 fun x hxF hxF' => h x hxF' x hxF' (left_mem_Icc.2 le_rfl) hxF

theorem InGap.mono {F₁ F₂ G₁ G₂ : Set ℝ} (h : InGap F₁ G₁) (hF : F₂ ⊆ F₁) (hG : G₂ ⊆ G₁) :
    InGap F₂ G₂ :=
  fun x hx y hy _ hz hzF => h x (hG hx) y (hG hy) hz (hF hzF)

theorem InGap.empty_left (F' : Set ℝ) : InGap ∅ F' := fun _ _ _ _ _ _ h => h

theorem InGap.empty_right (F : Set ℝ) : InGap F ∅ := fun _ hx => absurd hx (notMem_empty _)

/-- `def:th-special`: a *thesis-special family*. -/
def IsThesisSpecial (𝓕 : Set (Set ℝ)) : Prop :=
  ∃ F : ℕ → Set ℝ, range F = 𝓕 ∧ (∀ n, IsClosed (F n) ∧ Bornology.IsBounded (F n)) ∧
    ∀ n m, n < m → InGap (F n) (F m) ∨ Split (F m) (F n)

/-- `lem:th-special-implies`: any two distinct members of a thesis-special family are disjoint or
split. -/
theorem IsThesisSpecial.pairwise {𝓕 : Set (Set ℝ)} (h : IsThesisSpecial 𝓕) :
    𝓕.Pairwise fun F G => Disjoint F G ∨ Split F G := by
  obtain ⟨F, rfl, -, hrel⟩ := h
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ hne
  have hnm : n ≠ m := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hnm with h | h
  · rcases hrel n m h with h1 | h1
    · exact Or.inl (InGap.disjoint h1)
    · exact Or.inr h1.symm
  · rcases hrel m n h with h1 | h1
    · exact Or.inl (InGap.disjoint h1).symm
    · exact Or.inr h1

/-- `lem:th-special-implies`: a thesis-special family of subsets of `X` is a special family. -/
theorem IsThesisSpecial.isSpecialFamily {𝓕 : Set (Set ℝ)} (h : IsThesisSpecial 𝓕)
    (hX : ∀ F ∈ 𝓕, F ⊆ Ioo (-1) 1) : IsSpecialFamily 𝓕 := by
  have hp := h.pairwise
  obtain ⟨F, rfl, hF, -⟩ := h
  refine ⟨countable_range F, ?_, hX, hp⟩
  rintro _ ⟨n, rfl⟩
  exact Metric.isCompact_of_isClosed_isBounded (hF n).1 (hF n).2

/-- `lem:th-lemma9`: every `F_σ` subset of `ℝ` is the union of a sequence of bounded closed sets,
any two of which (with distinct indices) are disjoint or split. -/
theorem exists_seq_split_or_disjoint {E : Set ℝ} (hE : IsFσ E) :
    ∃ C : ℕ → Set ℝ, (∀ n, IsClosed (C n) ∧ Bornology.IsBounded (C n)) ∧
      (Pairwise fun n m => Disjoint (C n) (C m) ∨ Split (C n) (C m)) ∧ ⋃ n, C n = E := by
  classical
  obtain ⟨𝓕, hc, hK, hp, hU⟩ := exists_countable_family_of_isFσ hE
  have : Countable ↥(𝓕 \ {∅}) := (hc.mono sdiff_subset).to_subtype
  obtain ⟨f, hf⟩ := exists_injective_nat ↥(𝓕 \ {∅})
  let C : ℕ → Set ℝ := fun n => if h : ∃ F : ↥(𝓕 \ {∅}), f F = n then (h.choose : Set ℝ) else ∅
  have hC1 : ∀ F : ↥(𝓕 \ {∅}), C (f F) = F := by
    intro F
    have h : ∃ F' : ↥(𝓕 \ {∅}), f F' = f F := ⟨F, rfl⟩
    simp only [C, dif_pos h]
    exact congrArg Subtype.val (hf h.choose_spec)
  have hC2 : ∀ n, C n = ∅ ∨ ∃ F : ↥(𝓕 \ {∅}), f F = n ∧ C n = F := by
    intro n
    by_cases h : ∃ F : ↥(𝓕 \ {∅}), f F = n
    · obtain ⟨F, rfl⟩ := h
      exact Or.inr ⟨F, rfl, hC1 F⟩
    · exact Or.inl (by simp only [C, dif_neg h])
  have hCmem : ∀ n, C n = ∅ ∨ C n ∈ 𝓕 := by
    intro n
    rcases hC2 n with h | ⟨F, -, h⟩
    · exact Or.inl h
    · exact Or.inr (h ▸ F.2.1)
  refine ⟨C, fun n => ?_, ?_, ?_⟩
  · rcases hCmem n with h | h
    · rw [h]; exact ⟨isClosed_empty, Bornology.isBounded_empty⟩
    · exact ⟨(hK _ h).isClosed, (hK _ h).isBounded⟩
  · intro n m hnm
    rcases hC2 n with h | ⟨F, rfl, hF⟩
    · rw [h]; exact Or.inl (empty_disjoint _)
    rcases hC2 m with h | ⟨G, rfl, hG⟩
    · rw [h]; exact Or.inl (disjoint_empty _)
    rw [hF, hG]
    have : (F : Set ℝ) ≠ G := fun h => hnm (by rw [Subtype.ext h])
    exact hp F.2.1 G.2.1 this
  · rw [← hU]
    ext x
    simp only [mem_iUnion, mem_sUnion]
    constructor
    · rintro ⟨n, hn⟩
      rcases hCmem n with h | h
      · simp [h] at hn
      · exact ⟨_, h, hn⟩
    · rintro ⟨F, hF, hx⟩
      have hF' : F ∈ 𝓕 \ {∅} := ⟨hF, fun h => by simp_all⟩
      exact ⟨f ⟨F, hF'⟩, by rw [hC1 ⟨F, hF'⟩]; exact hx⟩

/-- Block decoding. -/
theorem exists_flatten (n : ℕ → ℕ) :
    ∃ τ : ℕ → ℕ × ℕ, (∀ k l, k < l → (τ k).1 < (τ l).1 ∨
      ((τ k).1 = (τ l).1 ∧ (τ k).2 < (τ l).2)) ∧ ∀ s i, i ≤ n s → ∃ k, τ k = (s, i) := by
  obtain ⟨P, hP0, hP⟩ : ∃ P : ℕ → ℕ, P 0 = 0 ∧ ∀ s, P (s + 1) = P s + n s + 1 :=
    ⟨fun s => ∑ t ∈ Finset.range s, (n t + 1), by simp,
      fun s => by simp only [Finset.sum_range_succ]; omega⟩
  have hPmono : StrictMono P := strictMono_nat_of_lt_succ fun s => by rw [hP]; omega
  have hex : ∀ k, ∃ s, k < P (s + 1) := fun k => ⟨k, by have : k + 1 ≤ P (k + 1) := hPmono.id_le _; omega⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, ∀ k, k < P (σ k + 1) ∧ ∀ m < σ k, P (m + 1) ≤ k :=
    ⟨fun k => Nat.find (hex k), fun k => ⟨Nat.find_spec (hex k),
      fun m hm => not_lt.1 (Nat.find_min (hex k) hm)⟩⟩
  have hσ2 : ∀ k, k < P (σ k + 1) := fun k => (hσ k).1
  have hσ1 : ∀ k, P (σ k) ≤ k := by
    intro k
    by_cases h : σ k = 0
    · rw [h, hP0]; omega
    · have := (hσ k).2 (σ k - 1) (by omega)
      have h2 : σ k - 1 + 1 = σ k := by omega
      rw [h2] at this
      exact this
  have hσu : ∀ k s, P s ≤ k → k < P (s + 1) → σ k = s := by
    intro k s h1 h2
    rcases lt_trichotomy (σ k) s with h | h | h
    · have := hPmono.monotone (show σ k + 1 ≤ s from h)
      have := hσ2 k
      omega
    · exact h
    · have := hPmono.monotone (show s + 1 ≤ σ k from h)
      have := hσ1 k
      omega
  refine ⟨fun k => (σ k, k - P (σ k)), ?_, ?_⟩
  · intro k l hkl
    have hle : σ k ≤ σ l := by
      by_contra hlt
      push Not at hlt
      have := hPmono.monotone (show σ l + 1 ≤ σ k from hlt)
      have := hσ1 k
      have := hσ2 l
      omega
    rcases hle.lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      show k - P (σ k) < l - P (σ l)
      rw [← h]
      have := hσ1 k
      omega
  · intro s i hi
    refine ⟨P s + i, ?_⟩
    have : σ (P s + i) = s := hσu _ _ (by omega) (by rw [hP]; omega)
    simp only [this]
    congr 1
    omega

theorem exists_enum_finite {α : Type*} (S : Set α) (hS : S.Finite) (d : α) :
    ∃ (n : ℕ) (g : ℕ → α), (∀ i < n, g i ∈ S) ∧ (∀ i, n ≤ i → g i = d) ∧
      (∀ a ∈ S, ∃ i < n, g i = a) ∧ (∀ i < n, ∀ j < n, g i = g j → i = j) := by
  classical
  let T := hS.toFinset
  let e := T.equivFin
  refine ⟨T.card, fun i => if h : i < T.card then ((e.symm ⟨i, h⟩ : T) : α) else d,
    fun i hi => ?_, fun i hi => ?_, fun a ha => ?_, fun i hi j hj hij => ?_⟩
  · simp only [dif_pos hi]
    exact hS.mem_toFinset.1 (e.symm ⟨i, hi⟩).2
  · simp only [dif_neg (not_lt.2 hi)]
  · have haT : a ∈ T := hS.mem_toFinset.2 ha
    refine ⟨(e ⟨a, haT⟩).1, (e ⟨a, haT⟩).2, ?_⟩
    simp only [dif_pos (e ⟨a, haT⟩).2]
    simp
  · simp only [dif_pos hi, dif_pos hj] at hij
    have := e.symm.injective (Subtype.ext hij)
    simpa using this


/-- The class of `x` with respect to `K`: the points `y` with `[x, y] ∩ K = ∅`. -/
def cls (K : Set ℝ) (x : ℝ) : Set ℝ := {y | Disjoint (uIcc x y) K}

theorem cls_eq_of_disjoint {K : Set ℝ} {x x' : ℝ} (h : Disjoint (uIcc x x') K) :
    cls K x = cls K x' := by
  ext y
  show Disjoint (uIcc x y) K ↔ Disjoint (uIcc x' y) K
  constructor
  · intro hy
    have : uIcc x' y ⊆ uIcc x' x ∪ uIcc x y := uIcc_subset_uIcc_union_uIcc
    exact (Disjoint.union_left (by rwa [uIcc_comm]) hy).mono_left this
  · intro hy
    have : uIcc x y ⊆ uIcc x x' ∪ uIcc x' y := uIcc_subset_uIcc_union_uIcc
    exact (h.union_left hy).mono_left this

theorem cls_union (K L : Set ℝ) (x : ℝ) : cls (K ∪ L) x = cls K x ∩ cls L x := by
  ext y
  show Disjoint (uIcc x y) (K ∪ L) ↔ Disjoint (uIcc x y) K ∧ Disjoint (uIcc x y) L
  exact disjoint_union_right

theorem cls_empty (x : ℝ) : cls ∅ x = univ := by
  ext y
  simp [cls]

theorem cls_eq_empty_of_mem {K : Set ℝ} {x : ℝ} (hx : x ∈ K) : cls K x = ∅ := by
  ext y
  refine ⟨fun h => ?_, fun h => h.elim⟩
  exact disjoint_left.1 (show Disjoint (uIcc x y) K from h) left_mem_uIcc hx

theorem mem_cls_self {K : Set ℝ} {x : ℝ} (hx : x ∉ K) : x ∈ cls K x := by
  simpa [cls] using hx

theorem notMem_of_mem_cls {K : Set ℝ} {x y : ℝ} (hy : y ∈ cls K x) : y ∉ K :=
  fun h => disjoint_left.1 hy right_mem_uIcc h

theorem mem_cls_of_mem_uIcc {K : Set ℝ} {x y y' z : ℝ} (hy : y ∈ cls K x) (hy' : y' ∈ cls K x)
    (hz : z ∈ uIcc y y') : z ∈ cls K x := by
  have h1 : cls K x = cls K y := cls_eq_of_disjoint hy
  rw [h1] at hy' ⊢
  show Disjoint (uIcc y z) K
  exact Disjoint.mono_left (uIcc_subset_uIcc_left hz) (show Disjoint (uIcc y y') K from hy')

theorem cls_subset_Iio {K : Set ℝ} {x z : ℝ} (hz : z ∈ K) (hxz : x < z) : cls K x ⊆ Iio z := by
  intro y hy
  by_contra h
  exact disjoint_left.1 hy (mem_uIcc.2 (Or.inl ⟨hxz.le, not_lt.1 h⟩)) hz

theorem cls_subset_Ioi {K : Set ℝ} {x z : ℝ} (hz : z ∈ K) (hzx : z < x) : cls K x ⊆ Ioi z := by
  intro y hy
  by_contra h
  exact disjoint_left.1 hy (mem_uIcc.2 (Or.inr ⟨not_lt.1 h, hzx.le⟩)) hz

theorem disjoint_uIcc_of_split {A B : Set ℝ} {x x' : ℝ} (hs : Split A B) (hx : x ∈ B)
    (hx' : x' ∈ B) (hxA : x ∉ A) (hxA' : x' ∉ A) : Disjoint (uIcc x x') A := by
  rw [disjoint_left]
  intro z hz hzA
  obtain ⟨p, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hs
  · have := h1 z hzA
    have := h2 x hx
    have := h2 x' hx'
    rcases mem_uIcc.1 hz with ⟨a, b⟩ | ⟨a, b⟩
    · exact hxA (by rwa [show x = z by linarith])
    · exact hxA' (by rwa [show x' = z by linarith])
  · have := h2 z hzA
    have := h1 x hx
    have := h1 x' hx'
    rcases mem_uIcc.1 hz with ⟨a, b⟩ | ⟨a, b⟩
    · exact hxA' (by rwa [show x' = z by linarith])
    · exact hxA (by rwa [show x = z by linarith])


section Stage

variable {E : ℕ → Set ℝ}

theorem finite_cls_single (hE : ∀ n, IsClosed (E n) ∧ Bornology.IsBounded (E n))
    (hrel : ∀ n m, n ≠ m → Disjoint (E n) (E m) ∨ Split (E n) (E m)) {j s : ℕ} (hjs : j ≠ s) :
    (cls (E j) '' E s).Finite := by
  rcases hrel j s hjs with hd | hsp
  · have hKc : IsCompact (E j) := Metric.isCompact_of_isClosed_isBounded (hE j).1 (hE j).2
    have hLc : IsCompact (E s) := Metric.isCompact_of_isClosed_isBounded (hE s).1 (hE s).2
    obtain ⟨r, hr, hsep⟩ := exists_pos_le_abs_sub hKc hLc hd
    obtain ⟨t, hts, ht, hcov⟩ := hLc.finite_cover_balls hr
    refine (ht.image (cls (E j))).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcov hx)
    refine ⟨c, hc, (cls_eq_of_disjoint ?_).symm⟩
    rw [disjoint_left]
    intro z hz hzK
    have h1 := hsep z hzK x hx
    have h2 := hsep z hzK c (hts hc)
    have h3 := abs_lt.1 (show |x - c| < r by rw [← Real.dist_eq]; exact Metric.mem_ball.1 hxc)
    rcases mem_uIcc.1 hz with ⟨a, b⟩ | ⟨a, b⟩ <;>
    rcases le_abs'.1 h1 with h4 | h4 <;> rcases le_abs'.1 h2 with h5 | h5 <;>
    linarith [h3.1, h3.2]
  · by_cases hex : ∃ x₀ ∈ E s, x₀ ∉ E j
    · obtain ⟨x₀, hx₀, hx₀j⟩ := hex
      refine ((finite_singleton (cls (E j) x₀)).insert ∅).subset ?_
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxj : x ∈ E j
      · exact Or.inl (cls_eq_empty_of_mem hxj)
      · exact Or.inr (cls_eq_of_disjoint (disjoint_uIcc_of_split hsp hx hx₀ hxj hx₀j))
    · refine (finite_singleton (∅ : Set ℝ)).subset ?_
      rintro _ ⟨x, hx, rfl⟩
      exact cls_eq_empty_of_mem (by by_contra h; exact hex ⟨x, hx, h⟩)

theorem finite_cls_biUnion (hE : ∀ n, IsClosed (E n) ∧ Bornology.IsBounded (E n))
    (hrel : ∀ n m, n ≠ m → Disjoint (E n) (E m) ∨ Split (E n) (E m)) (s : ℕ) (J : Finset ℕ)
    (hJ : s ∉ J) : ((fun x => cls (⋃ j ∈ J, E j) x) '' E s).Finite := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    refine (finite_singleton (univ : Set ℝ)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    simp [cls_empty]
  | insert j J hj ih =>
    have hsj : j ≠ s := fun h => hJ (h ▸ Finset.mem_insert_self _ _)
    have hsJ : s ∉ J := fun h => hJ (Finset.mem_insert_of_mem h)
    refine ((finite_cls_single hE hrel hsj).image2 (· ∩ ·) (ih hsJ)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨cls (E j) x, ⟨x, hx, rfl⟩, cls (⋃ j ∈ J, E j) x, ⟨x, hx, rfl⟩, ?_⟩
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, cls_union]

/-- The sets of the earlier stages: `A s = E 0 ∪ ⋯ ∪ E (s - 1)`. -/
def stageA (E : ℕ → Set ℝ) (s : ℕ) : Set ℝ := ⋃ j ∈ Finset.range s, E j

/-- The new sets at stage `s`: the closure of `E s ∩ ` (the component of `ℝ \ A s` containing `x`). -/
def stageN (E : ℕ → Set ℝ) (s : ℕ) (x : ℝ) : Set ℝ := closure (E s ∩ cls (stageA E s) x)

theorem finite_stageN (hE : ∀ n, IsClosed (E n) ∧ Bornology.IsBounded (E n))
    (hrel : ∀ n m, n ≠ m → Disjoint (E n) (E m) ∨ Split (E n) (E m)) (s : ℕ) :
    (stageN E s '' E s).Finite := by
  have := (finite_cls_biUnion hE hrel s (Finset.range s) (by simp)).image
    (fun C => closure (E s ∩ C))
  rwa [image_image] at this

theorem stageN_subset (hE : ∀ n, IsClosed (E n)) (s : ℕ) (x : ℝ) : stageN E s x ⊆ E s :=
  closure_minimal inter_subset_left (hE s)

theorem stageN_eq_empty {s : ℕ} {x : ℝ} (hx : x ∈ stageA E s) : stageN E s x = ∅ := by
  simp [stageN, cls_eq_empty_of_mem hx]

theorem mem_stageN_self {s : ℕ} {x : ℝ} (hxE : x ∈ E s) (hx : x ∉ stageA E s) :
    x ∈ stageN E s x :=
  subset_closure ⟨hxE, mem_cls_self hx⟩

theorem stageA_mono_mem {s s' : ℕ} (h : s' < s) : E s' ⊆ stageA E s :=
  fun _ hx => mem_iUnion₂.2 ⟨s', Finset.mem_range.2 h, hx⟩

theorem notMem_stageA_of_ne_empty {s : ℕ} {x : ℝ} (h : stageN E s x ≠ ∅) : x ∉ stageA E s :=
  fun hx => h (stageN_eq_empty hx)



theorem inGap_closure {S K T : Set ℝ} (hS : IsClosed S) (hTK : T ⊆ K) (hd : Disjoint T S) (x : ℝ) :
    InGap T (closure (S ∩ cls K x)) := by
  intro u hu v hv z hz hzT
  have huS : u ∈ S := closure_minimal inter_subset_left hS hu
  have hvS : v ∈ S := closure_minimal inter_subset_left hS hv
  rcases hz.1.eq_or_lt with rfl | h1
  · exact disjoint_left.1 hd hzT huS
  rcases hz.2.eq_or_lt with rfl | h2
  · exact disjoint_left.1 hd hzT hvS
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hu (Iio z) isOpen_Iio h1
  obtain ⟨y', hy1', hy2'⟩ := mem_closure_iff.1 hv (Ioi z) isOpen_Ioi h2
  have hzc : z ∈ cls K x :=
    mem_cls_of_mem_uIcc hy2.2 hy2'.2 (mem_uIcc.2 (Or.inl ⟨le_of_lt hy1, le_of_lt hy1'⟩))
  exact notMem_of_mem_cls hzc (hTK hzT)

theorem split_closure {S S' K : Set ℝ} {x x' z : ℝ} (hz : z ∈ K) (hxz : x < z) (hzx' : z < x') :
    Split (closure (S ∩ cls K x)) (closure (S' ∩ cls K x')) := by
  refine ⟨z, Or.inl ⟨fun y hy => ?_, fun y hy => ?_⟩⟩
  · refine closure_minimal (t := Iic z) ?_ isClosed_Iic hy
    exact fun w hw => mem_Iic.2 (le_of_lt (cls_subset_Iio hz hxz hw.2))
  · refine closure_minimal (t := Ici z) ?_ isClosed_Ici hy
    exact fun w hw => mem_Ici.2 (le_of_lt (cls_subset_Ioi hz hzx' hw.2))

theorem split_stageN {s : ℕ} {x x' : ℝ} (hx : x ∉ stageA E s) (hx' : x' ∉ stageA E s)
    (hne : stageN E s x ≠ stageN E s x') : Split (stageN E s x) (stageN E s x') := by
  have hd : ¬ Disjoint (uIcc x x') (stageA E s) := fun h => hne (by
    unfold stageN
    rw [cls_eq_of_disjoint h])
  rw [not_disjoint_iff] at hd
  obtain ⟨z, hz, hzA⟩ := hd
  have hzx : z ≠ x := fun h => hx (h ▸ hzA)
  have hzx' : z ≠ x' := fun h => hx' (h ▸ hzA)
  rcases mem_uIcc.1 hz with ⟨a, b⟩ | ⟨a, b⟩
  · exact split_closure hzA (lt_of_le_of_ne a (Ne.symm hzx)) (lt_of_le_of_ne b hzx')
  · exact (split_closure (S := E s) (S' := E s) hzA (lt_of_le_of_ne a (Ne.symm hzx'))
      (lt_of_le_of_ne b hzx)).symm

end Stage


/-- `lem:th-lemma10`: every `F_σ` subset of `ℝ` is the union of a thesis-special family. -/
theorem exists_thesisSpecial_of_isFσ {E : Set ℝ} (hE : IsFσ E) :
    ∃ 𝓕 : Set (Set ℝ), IsThesisSpecial 𝓕 ∧ ⋃₀ 𝓕 = E := by
  obtain ⟨C, hC, hrel, hU⟩ := exists_seq_split_or_disjoint hE
  have hrel' : ∀ n m, n ≠ m → Disjoint (C n) (C m) ∨ Split (C n) (C m) := fun n m h => hrel h
  have hCc : ∀ n, IsClosed (C n) := fun n => (hC n).1
  choose n g hg1 hg2 hg3 hg4 using fun s =>
    exists_enum_finite (stageN C s '' C s) (finite_stageN hC hrel' s) ∅
  obtain ⟨τ, hτ1, hτ2⟩ := exists_flatten n
  have hgshape : ∀ s i, g s i = ∅ ∨ ∃ x ∈ C s, g s i = stageN C s x := by
    intro s i
    by_cases h : i < n s
    · obtain ⟨x, hx, hxe⟩ := hg1 s i h
      exact Or.inr ⟨x, hx, hxe.symm⟩
    · exact Or.inl (hg2 s i (not_lt.1 h))
  refine ⟨range fun k => g (τ k).1 (τ k).2, ⟨fun k => g (τ k).1 (τ k).2, rfl, fun k => ?_, ?_⟩, ?_⟩
  · show IsClosed (g (τ k).1 (τ k).2) ∧ Bornology.IsBounded (g (τ k).1 (τ k).2)
    rcases hgshape (τ k).1 (τ k).2 with h | ⟨x, hx, h⟩
    · rw [h]; exact ⟨isClosed_empty, Bornology.isBounded_empty⟩
    · rw [h]; exact ⟨isClosed_closure, (hC _).2.subset (stageN_subset hCc _ _)⟩
  · intro k l hkl
    have hlt := hτ1 k l hkl
    rcases h1 : τ k with ⟨s, i⟩
    rcases h2 : τ l with ⟨s', i'⟩
    simp only [h1, h2] at hlt ⊢
    by_cases h0 : g s i = ∅
    · rw [h0]; exact Or.inl (InGap.empty_left _)
    by_cases h0' : g s' i' = ∅
    · rw [h0']; exact Or.inl (InGap.empty_right _)
    obtain ⟨x, hx, hi⟩ := (hgshape s i).resolve_left h0
    obtain ⟨x', hx', hi'⟩ := (hgshape s' i').resolve_left h0'
    rw [hi] at h0
    rw [hi']  at h0'
    rcases hlt with hss | ⟨rfl, hii⟩
    · rw [hi, hi']
      rcases hrel' s s' hss.ne with hd | hsp
      · exact Or.inl (inGap_closure (hCc s')
          ((stageN_subset hCc s x).trans (stageA_mono_mem hss))
          (hd.mono_left (stageN_subset hCc s x)) x')
      · exact Or.inr (hsp.symm.mono (stageN_subset hCc s' x') (stageN_subset hCc s x))
    · refine Or.inr ?_
      have hin : i < n s := by
        by_contra h
        exact h0 (by rw [← hi]; exact hg2 s i (not_lt.1 h))
      have hin' : i' < n s := by
        by_contra h
        exact h0' (by rw [← hi']; exact hg2 s i' (not_lt.1 h))
      have hne : g s i ≠ g s i' := fun h => hii.ne (hg4 s i hin i' hin' h)
      rw [hi, hi'] at hne ⊢
      exact (split_stageN (notMem_stageA_of_ne_empty h0) (notMem_stageA_of_ne_empty h0') hne).symm
  · rw [← hU]
    ext y
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, hy⟩
      change y ∈ g (τ k).1 (τ k).2 at hy
      rcases hgshape (τ k).1 (τ k).2 with h | ⟨x, hx, h⟩
      · rw [h] at hy; exact hy.elim
      · rw [h] at hy; exact mem_iUnion.2 ⟨(τ k).1, stageN_subset hCc _ _ hy⟩
    · intro hy
      classical
      have hex : ∃ s, y ∈ C s := mem_iUnion.1 hy
      have hys : y ∈ C (Nat.find hex) := Nat.find_spec hex
      have hyA : y ∉ stageA C (Nat.find hex) := by
        intro h
        obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 h
        exact Nat.find_min hex (Finset.mem_range.1 hj) hyj
      obtain ⟨i, hi, hgi⟩ := hg3 (Nat.find hex) (stageN C (Nat.find hex) y) ⟨y, hys, rfl⟩
      obtain ⟨k, hk⟩ := hτ2 (Nat.find hex) i hi.le
      refine ⟨_, ⟨k, rfl⟩, ?_⟩
      show y ∈ g (τ k).1 (τ k).2
      rw [hk]
      dsimp only
      rw [hgi]
      exact mem_stageN_self hys hyA

/-- `lem:th-lemma11`: the meet of two thesis-special families is thesis-special. -/
theorem IsThesisSpecial.inf {𝓕 𝓖 : Set (Set ℝ)} (h𝓕 : IsThesisSpecial 𝓕)
    (h𝓖 : IsThesisSpecial 𝓖) : IsThesisSpecial (image2 (· ∩ ·) 𝓕 𝓖) := by
  obtain ⟨F, rfl, hF, hFr⟩ := h𝓕
  obtain ⟨G, rfl, hG, hGr⟩ := h𝓖
  refine ⟨fun k => F (Nat.unpair k).1 ∩ G (Nat.unpair k).2, ?_, fun k => ⟨?_, ?_⟩, ?_⟩
  · ext H
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact ⟨Nat.pair a b, by simp⟩
  · exact (hF _).1.inter (hG _).1
  · exact (hF _).2.subset inter_subset_left
  · intro k l hkl
    have key : (Nat.unpair k).1 < (Nat.unpair l).1 ∨ (Nat.unpair k).2 < (Nat.unpair l).2 := by
      by_contra hcon
      simp only [not_or, not_lt] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have : Nat.pair (Nat.unpair l).1 (Nat.unpair l).2 ≤ Nat.pair (Nat.unpair k).1 (Nat.unpair k).2 := by
        rcases h1.lt_or_eq with h1 | h1 <;> rcases h2.lt_or_eq with h2 | h2
        · exact ((Nat.pair_lt_pair_left _ h1).trans (Nat.pair_lt_pair_right _ h2)).le
        · rw [h2]; exact (Nat.pair_lt_pair_left _ h1).le
        · rw [h1]; exact (Nat.pair_lt_pair_right _ h2).le
        · rw [h1, h2]
      rw [Nat.pair_unpair, Nat.pair_unpair] at this
      omega
    rcases key with h | h
    · rcases hFr _ _ h with h1 | h1
      · exact Or.inl (h1.mono inter_subset_left inter_subset_left)
      · exact Or.inr (h1.mono inter_subset_left inter_subset_left)
    · rcases hGr _ _ h with h1 | h1
      · exact Or.inl (h1.mono inter_subset_right inter_subset_right)
      · exact Or.inr (h1.mono inter_subset_right inter_subset_right)

/-- `lem:th-lemma11`: the union of the meet is the intersection of the unions. -/
theorem sUnion_inf (𝓕 𝓖 : Set (Set ℝ)) :
    ⋃₀ image2 (· ∩ ·) 𝓕 𝓖 = ⋃₀ 𝓕 ∩ ⋃₀ 𝓖 :=
  TJK.Construct.sUnion_image2_inter 𝓕 𝓖

end TJK.Variant
