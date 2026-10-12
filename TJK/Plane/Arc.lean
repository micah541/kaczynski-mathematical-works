import Mathlib
import TJK.Defs

/-!
# Paths contain arcs (`fact:tietze-arc`)

`exists_arc_in_path'`: in a Hausdorff space, the image of a path `g` from `a` to `b ≠ a` contains a
simple arc from `a` to `b`.

Proof.
1. (Brouwer reduction.) Call a closed set `S ⊆ [0,1]` containing `0, 1` *admissible* if
   `g x = g y` for every gap `(x, y)` of `S` (`x < y` in `S`, `(x, y) ∩ S = ∅`). The intersection of
   a chain of admissible sets is admissible (compactness), so by Zorn there is a minimal admissible
   `m`. Minimality gives: if `x < y` in `m` and `g x = g y`, then `(x, y)` is a gap of `m`.
2. With `r t = sup (m ∩ (-∞, t])`, the map `f = g ∘ r : [0,1] → X` is continuous, has image in
   `g([0,1])`, `f 0 = a`, `f 1 = b`, and its fibres are intervals.
3. A continuous `f : [0,1] → X` with interval fibres admits a continuous monotone `h : [0,1] → ℝ`
   with exactly the same fibres: a weighted sum of the running maxima of countably many Urysohn
   functions on the compact Hausdorff space `f([0,1])`.
4. Then `f` factors through the closed quotient map `h`, giving an injective path.
-/

namespace TJK

open _root_.Set Filter Topology Function unitInterval

namespace ArcAux

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-! ### Step 4: from a monotone separating function to an injective path -/

omit [T2Space X] in
theorem exists_injective_path_of_monotone (f : I → X) (hf : Continuous f) (h : I → ℝ)
    (hh : Continuous h) (hmono : Monotone h) (hfh : ∀ x y, h x = h y ↔ f x = f y)
    (h01 : f 0 ≠ f 1) :
    ∃ q : Path (f 0) (f 1), Injective q ∧ range q ⊆ range f := by
  have hlt : h 0 < h 1 :=
    lt_of_le_of_ne (hmono (zero_le_one)) fun e => h01 ((hfh 0 1).1 e)
  set c := h 1 - h 0 with hc
  have hcpos : 0 < c := sub_pos.2 hlt
  have hmem : ∀ t, (h t - h 0) / c ∈ Icc (0 : ℝ) 1 := by
    intro t
    have h0t := hmono (show (0 : I) ≤ t from unitInterval.nonneg')
    have ht1 := hmono (show t ≤ (1 : I) from unitInterval.le_one')
    constructor
    · exact div_nonneg (sub_nonneg.2 h0t) hcpos.le
    · rw [div_le_one hcpos]; linarith
  let k : I → I := fun t => ⟨(h t - h 0) / c, hmem t⟩
  have hk : Continuous k :=
    Continuous.subtype_mk ((hh.sub continuous_const).div_const c) _
  have hks : Surjective k := by
    intro τ
    have hτ : (τ : ℝ) * c + h 0 ∈ Icc (h 0) (h 1) := by
      have h1 := τ.2.1
      have h2 := τ.2.2
      constructor <;> nlinarith
    obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hh hτ
    refine ⟨t, Subtype.ext ?_⟩
    simp only [k, ht]
    field_simp
    ring
  have hkq : IsQuotientMap k := hk.isClosedMap.isQuotientMap hk hks
  have hkeq : ∀ s t, k s = k t ↔ f s = f t := by
    intro s t
    rw [← hfh, Subtype.ext_iff]
    simp only [k]
    rw [div_left_inj' hcpos.ne', sub_left_inj]
  let sec := surjInv hks
  let q : I → X := fun τ => f (sec τ)
  have hqk : q ∘ k = f := funext fun t => (hkeq _ _).1 (surjInv_eq hks (k t))
  have hq : Continuous q := hkq.continuous_iff.2 (hqk ▸ hf)
  have hk0 : k 0 = 0 := Subtype.ext (by simp [k])
  have hk1 : k 1 = 1 := Subtype.ext (by simp only [k]; exact div_self hcpos.ne')
  have hq0 : q 0 = f 0 := by
    calc q 0 = q (k 0) := by rw [hk0]
      _ = f 0 := congrFun hqk 0
  have hq1 : q 1 = f 1 := by
    calc q 1 = q (k 1) := by rw [hk1]
      _ = f 1 := congrFun hqk 1
  refine ⟨⟨⟨q, hq⟩, hq0, hq1⟩, ?_, ?_⟩
  · intro τ τ' e
    have := (hkeq _ _).2 e
    rwa [surjInv_eq hks, surjInv_eq hks] at this
  · rintro _ ⟨τ, rfl⟩
    exact ⟨sec τ, rfl⟩

/-! ### Step 3: a monotone function with the same fibres -/

theorem exists_sep (f : I → X) (hf : Continuous f)
    (hconv : ∀ x w y : I, x ≤ w → w ≤ y → f x = f y → f w = f x) (p p' : ℝ) :
    ∃ φ : I → ℝ, Continuous φ ∧ Monotone φ ∧ (∀ t, φ t ∈ Icc (0 : ℝ) 1) ∧
      (∀ x y, f x = f y → φ x = φ y) ∧
      (Disjoint (f '' {s | (s : ℝ) ≤ p}) (f '' {s | p' ≤ (s : ℝ)}) →
        (∀ t : I, (t : ℝ) ≤ p → φ t = 0) ∧ (∀ t : I, p' ≤ (t : ℝ) → φ t = 1)) := by
  by_cases hd : Disjoint (f '' {s | (s : ℝ) ≤ p}) (f '' {s | p' ≤ (s : ℝ)})
  swap
  · exact ⟨fun _ => 0, continuous_const, monotone_const, fun _ => ⟨le_rfl, zero_le_one⟩,
      fun _ _ _ => rfl, fun h => absurd h hd⟩
  have : CompactSpace (range f) := isCompact_iff_compactSpace.mp (isCompact_range hf)
  let F : I → range f := rangeFactorization f
  have hF : Continuous F := hf.subtype_mk _
  have hK : IsClosed (F '' {s | (s : ℝ) ≤ p}) :=
    ((isClosed_le continuous_subtype_val continuous_const).isCompact.image hF).isClosed
  have hL : IsClosed (F '' {s | p' ≤ (s : ℝ)}) :=
    ((isClosed_le continuous_const continuous_subtype_val).isCompact.image hF).isClosed
  have hKL : Disjoint (F '' {s | (s : ℝ) ≤ p}) (F '' {s | p' ≤ (s : ℝ)}) := by
    rw [_root_.Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', he⟩
    exact _root_.Set.disjoint_left.1 hd ⟨s, hs, rfl⟩ ⟨s', hs', congrArg Subtype.val he⟩
  obtain ⟨u, hu0, hu1, hu⟩ := exists_continuous_zero_one_of_isClosed hK hL hKL
  let w : I → ℝ := fun s => u (F s)
  have hw : Continuous w := u.continuous.comp hF
  have hwf : ∀ s s', f s = f s' → w s = w s' := fun s s' e => by
    simp only [w]; congr 1; exact Subtype.ext e
  have hw01 : ∀ s, w s ∈ Icc (0 : ℝ) 1 := fun s => hu _
  let φ : I → ℝ := fun t => sSup ((fun s => w (min s t)) '' univ)
  have hbdd : ∀ t, BddAbove ((fun s => w (min s t)) '' univ) := fun t =>
    ⟨1, by rintro _ ⟨s, -, rfl⟩; exact (hw01 _).2⟩
  have hle : ∀ t s, w (min s t) ≤ φ t := fun t s => le_csSup (hbdd t) ⟨s, trivial, rfl⟩
  have hge : ∀ t c, (∀ s, w (min s t) ≤ c) → φ t ≤ c := fun t c hc =>
    csSup_le (image_nonempty.2 univ_nonempty) (by rintro _ ⟨s, -, rfl⟩; exact hc s)
  have hwt : ∀ t, w t ≤ φ t := fun t => by simpa using hle t t
  have hmono : Monotone φ := fun t t' htt' => hge t _ fun s => by
    have := hle t' (min s t)
    rwa [min_assoc, min_eq_left htt'] at this
  refine ⟨φ, ?_, hmono, ?_, ?_, ?_⟩
  · have := isCompact_univ.continuous_sSup (f := fun t s => w (min s t))
      (hw.comp (continuous_min.comp continuous_swap))
    exact this
  · intro t
    exact ⟨(hw01 t).1.trans (hwt t), hge t 1 fun s => (hw01 _).2⟩
  · have key : ∀ x y, x ≤ y → f x = f y → φ y ≤ φ x := by
      intro x y hxy e
      refine hge y _ fun s => ?_
      rcases le_total s x with hsx | hxs
      · rw [min_eq_left (hsx.trans hxy)]
        have := hle x s
        rwa [min_eq_left hsx] at this
      · have : f (min s y) = f x := hconv x (min s y) y (le_min hxs hxy) (min_le_right _ _) e
        rw [hwf _ _ this]
        exact hwt x
    intro x y e
    rcases le_total x y with h | h
    · exact le_antisymm (hmono h) (key x y h e)
    · exact le_antisymm (key y x h e.symm) (hmono h)
  · intro _
    refine ⟨fun t ht => le_antisymm (hge t 0 fun s => ?_) ((hw01 t).1.trans (hwt t)),
      fun t ht => le_antisymm (hge t 1 fun s => (hw01 _).2) ?_⟩
    · have hst : ((min s t : I) : ℝ) ≤ p := le_trans (min_le_right s t) ht
      have : w (min s t) = 0 := by simpa using hu0 ⟨min s t, hst, rfl⟩
      exact this.le
    · have : w t = 1 := by simpa using hu1 ⟨t, ht, rfl⟩
      rw [← this]
      exact hwt t

theorem exists_separating_monotone (f : I → X) (hf : Continuous f)
    (hconv : ∀ x w y : I, x ≤ w → w ≤ y → f x = f y → f w = f x) :
    ∃ h : I → ℝ, Continuous h ∧ Monotone h ∧ ∀ x y, h x = h y ↔ f x = f y := by
  choose Φ hΦc hΦm hΦ01 hΦf hΦs using
    fun pq : ℚ × ℚ => exists_sep f hf hconv (pq.1 : ℝ) (pq.2 : ℝ)
  obtain ⟨e, he⟩ := exists_surjective_nat (ℚ × ℚ)
  let h : I → ℝ := fun t => ∑' n : ℕ, (1 / 2 : ℝ) ^ n * Φ (e n) t
  have hterm : ∀ n t, 0 ≤ (1 / 2 : ℝ) ^ n * Φ (e n) t ∧ (1 / 2 : ℝ) ^ n * Φ (e n) t ≤ (1 / 2) ^ n :=
    fun n t => ⟨mul_nonneg (by positivity) (hΦ01 _ t).1,
      mul_le_of_le_one_right (by positivity) (hΦ01 _ t).2⟩
  have hsum : ∀ t, Summable fun n => (1 / 2 : ℝ) ^ n * Φ (e n) t := fun t =>
    summable_geometric_two.of_nonneg_of_le (fun n => (hterm n t).1) (fun n => (hterm n t).2)
  have main : ∀ x y : I, x < y → f x ≠ f y → h x < h y := by
    intro x y hxy hne
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
    obtain ⟨ε₁, hε₁, hU'⟩ := Metric.isOpen_iff.1 (hU.preimage hf) x hxU
    obtain ⟨ε₂, hε₂, hV'⟩ := Metric.isOpen_iff.1 (hV.preimage hf) y hyV
    have hxy' : (x : ℝ) < y := hxy
    set η := min (min ε₁ ε₂) (((y : ℝ) - x) / 2) with hη
    have hηpos : 0 < η := lt_min (lt_min hε₁ hε₂) (by linarith)
    have hη1 : η ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hη2 : η ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
    have hη3 : η ≤ ((y : ℝ) - x) / 2 := min_le_right _ _
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show (x : ℝ) < x + η by linarith)
    obtain ⟨p', hp'1, hp'2⟩ := exists_rat_btwn (show (y : ℝ) - η < y by linarith)
    have hx0 := x.2.1
    have hy1 := y.2.2
    let P : I := ⟨p, by linarith, by linarith⟩
    let P' : I := ⟨p', by linarith, by linarith⟩
    have hPU : f P ∈ U := hU' (by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
      constructor <;> simp only [P] <;> linarith)
    have hP'V : f P' ∈ V := hV' (by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
      constructor <;> simp only [P'] <;> linarith)
    have hdisj : Disjoint (f '' {s | (s : ℝ) ≤ (p : ℝ)}) (f '' {s | ((p' : ℚ) : ℝ) ≤ (s : ℝ)}) := by
      rw [_root_.Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', he⟩
      have h1 : f P = f s := hconv s P s' hs (show (P : ℝ) ≤ s' by
        simp only [P] at *; simp only [mem_ofPred_eq] at hs'; linarith) he.symm
      have h2 : f P' = f s := hconv s P' s' (show (s : ℝ) ≤ P' by
        simp only [P'] at *; simp only [mem_ofPred_eq] at hs; linarith) hs' he.symm
      exact _root_.Set.disjoint_left.1 hUV hPU (by rw [h1, ← h2]; exact hP'V)
    obtain ⟨n, hen⟩ := he (p, p')
    have hx : Φ (e n) x = 0 := by
      rw [hen]; exact (hΦs (p, p') hdisj).1 x (by simp only; linarith)
    have hy : Φ (e n) y = 1 := by
      rw [hen]; exact (hΦs (p, p') hdisj).2 y (by simp only; linarith)
    refine Summable.tsum_lt_tsum (i := n) (fun m => ?_) ?_ (hsum x) (hsum y)
    · exact mul_le_mul_of_nonneg_left (hΦm _ hxy.le) (by positivity)
    · rw [hx, hy, mul_zero, mul_one]
      positivity
  refine ⟨h, ?_, ?_, ?_⟩
  · refine continuous_tsum (fun n => continuous_const.mul (hΦc _)) summable_geometric_two
      fun n t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hterm n t).1]
    exact (hterm n t).2
  · intro x y hxy
    exact Summable.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (hΦm _ hxy) (by positivity)) (hsum x) (hsum y)
  · intro x y
    constructor
    · intro hxy
      by_contra hne
      rcases lt_trichotomy x y with hl | rfl | hl
      · exact (main x y hl hne).ne hxy
      · exact hne rfl
      · exact (main y x hl (Ne.symm hne)).ne hxy.symm
    · intro hxy
      exact tsum_congr fun n => by rw [hΦf _ x y hxy]

/-! ### Step 1: Brouwer reduction -/

/-- `S` is an admissible set of cut parameters for `g`: a closed subset of `[0,1]` containing `0`
and `1` such that `g` takes equal values at the ends of every gap of `S`. -/
def Admissible (g : ℝ → X) (S : Set ℝ) : Prop :=
  IsClosed S ∧ S ⊆ Icc 0 1 ∧ (0 : ℝ) ∈ S ∧ (1 : ℝ) ∈ S ∧
    ∀ x ∈ S, ∀ y ∈ S, x < y → (∀ z ∈ S, z ≤ x ∨ y ≤ z) → g x = g y

omit [TopologicalSpace X] [T2Space X] in
theorem admissible_Icc (g : ℝ → X) : Admissible g (Icc 0 1) := by
  refine ⟨isClosed_Icc, subset_rfl, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, ?_⟩
  intro x hx y hy hxy hgap
  rcases hgap ((x + y) / 2) ⟨by linarith [hx.1], by linarith [hy.2]⟩ with h | h <;>
    linarith

theorem admissible_sInter (g : ℝ → X) (hg : Continuous g) (c : Set (Set ℝ))
    (hc : c ⊆ {S | Admissible g S}) (hch : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    Admissible g (⋂₀ c) := by
  obtain ⟨S₀, hS₀⟩ := hne
  refine ⟨isClosed_sInter fun S hS => (hc hS).1, (sInter_subset_of_mem hS₀).trans (hc hS₀).2.1,
    mem_sInter.2 fun S hS => (hc hS).2.2.1, mem_sInter.2 fun S hS => (hc hS).2.2.2.1, ?_⟩
  intro x hx y hy hxy hgap
  by_contra hne
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
  obtain ⟨ε₁, hε₁, hU'⟩ := Metric.isOpen_iff.1 (hU.preimage hg) x hxU
  obtain ⟨ε₂, hε₂, hV'⟩ := Metric.isOpen_iff.1 (hV.preimage hg) y hyV
  set ε := min (min ε₁ ε₂) ((y - x) / 2) with hε
  have hεpos : 0 < ε := lt_min (lt_min hε₁ hε₂) (by linarith)
  have hε1 : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ (y - x) / 2 := min_le_right _ _
  -- some member of the chain misses `[x + ε/2, y - ε/2]`
  have : Nonempty c := ⟨⟨S₀, hS₀⟩⟩
  obtain ⟨⟨S, hSc⟩, hSK⟩ :=
    (isCompact_Icc (a := x + ε / 2) (b := y - ε / 2)).elim_directed_family_closed
    (fun i : c => (i : Set ℝ)) (fun i => (hc i.2).1)
    (by
      ext z
      simp only [mem_inter_iff, mem_iInter, mem_empty_iff_false, iff_false, not_and]
      intro hz hzc
      have : z ∈ ⋂₀ c := mem_sInter.2 fun S hS => hzc ⟨S, hS⟩
      rcases hgap z this with h | h <;> linarith [hz.1, hz.2])
    (by
      intro i j
      rcases hch.total i.2 j.2 with h | h
      · exact ⟨i, le_rfl, h⟩
      · exact ⟨j, h, le_rfl⟩)
  have hS := hc hSc
  have hxS : x ∈ S := mem_sInter.1 hx S hSc
  have hyS : y ∈ S := mem_sInter.1 hy S hSc
  set m := (x + y) / 2 with hmdef
  set α := sSup (S ∩ Icc x m)
  set β := sInf (S ∩ Icc m y)
  have hbα : BddAbove (S ∩ Icc x m) := bddAbove_Icc.mono inter_subset_right
  have hbβ : BddBelow (S ∩ Icc m y) := bddBelow_Icc.mono inter_subset_right
  have hα : α ∈ S ∩ Icc x m := (hS.1.inter isClosed_Icc).csSup_mem
    ⟨x, hxS, le_rfl, by linarith⟩ hbα
  have hβ : β ∈ S ∩ Icc m y := (hS.1.inter isClosed_Icc).csInf_mem
    ⟨y, hyS, by linarith, le_rfl⟩ hbβ
  have hgα : g α = g β := by
    rcases eq_or_lt_of_le (hα.2.2.trans hβ.2.1) with h | h
    · rw [h]
    · refine hS.2.2.2.2 α hα.1 β hβ.1 h fun z hz => ?_
      rcases le_total z m with hzm | hzm
      · left
        rcases lt_or_ge z x with hzx | hzx
        · exact hzx.le.trans hα.2.1
        · exact le_csSup hbα ⟨hz, hzx, hzm⟩
      · right
        rcases le_or_gt z y with hzy | hzy
        · exact csInf_le hbβ ⟨hz, hzm, hzy⟩
        · exact hβ.2.2.trans hzy.le
  have hαlt : α < x + ε / 2 := by
    by_contra h
    push Not at h
    have : α ∈ Icc (x + ε / 2) (y - ε / 2) ∩ S := ⟨⟨h, by linarith [hα.2.2]⟩, hα.1⟩
    rw [hSK] at this
    exact this
  have hβgt : y - ε / 2 < β := by
    by_contra h
    push Not at h
    have : β ∈ Icc (x + ε / 2) (y - ε / 2) ∩ S := ⟨⟨by linarith [hβ.2.1], h⟩, hβ.1⟩
    rw [hSK] at this
    exact this
  have hαU : g α ∈ U := hU' (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hα.2.1])
  have hβV : g β ∈ V := hV' (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hβ.2.2])
  exact _root_.Set.disjoint_left.1 hUV hαU (hgα ▸ hβV)

theorem exists_minimal_admissible (g : ℝ → X) (hg : Continuous g) :
    ∃ m, Admissible g m ∧ ∀ S, Admissible g S → S ⊆ m → m ⊆ S := by
  obtain ⟨m, hm⟩ := zorn_superset {S | Admissible g S} fun c hc hch => by
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨Icc 0 1, admissible_Icc g, fun s hs => absurd hs (notMem_empty s)⟩
    · exact ⟨⋂₀ c, admissible_sInter g hg c hc hch hne, fun s hs => sInter_subset_of_mem hs⟩
  exact ⟨m, hm.1, fun S hS hSm => hm.2 hS hSm⟩

omit [TopologicalSpace X] [T2Space X] in
/-- In a minimal admissible set, two parameters with equal values bound a gap. -/
theorem gap_of_minimal {g : ℝ → X} {m : Set ℝ} (hm : Admissible g m)
    (hmin : ∀ S, Admissible g S → S ⊆ m → m ⊆ S) {x y : ℝ} (hx : x ∈ m) (hy : y ∈ m)
    (hxy : x < y) (he : g x = g y) : ∀ z ∈ m, z ≤ x ∨ y ≤ z := by
  have hx01 := hm.2.1 hx
  have hy01 := hm.2.1 hy
  have hS' : Admissible g (m \ Ioo x y) := by
    refine ⟨hm.1.sdiff isOpen_Ioo, sdiff_subset.trans hm.2.1,
      ⟨hm.2.2.1, fun h => by linarith [h.1, hx01.1]⟩,
      ⟨hm.2.2.2.1, fun h => by linarith [h.2, hy01.2]⟩, ?_⟩
    intro u hu v hv huv hgap
    by_cases hall : ∀ z ∈ m, z ≤ u ∨ v ≤ z
    · exact hm.2.2.2.2 u hu.1 v hv.1 huv hall
    push Not at hall
    obtain ⟨z, hz, hzu, hzv⟩ := hall
    have hzI : z ∈ Ioo x y := by
      by_contra h
      rcases hgap z ⟨hz, h⟩ with h' | h' <;> linarith
    have hxS : x ∈ m \ Ioo x y := ⟨hx, fun h => lt_irrefl _ h.1⟩
    have hyS : y ∈ m \ Ioo x y := ⟨hy, fun h => lt_irrefl _ h.2⟩
    have hu' : u ∉ Ioo x y := hu.2
    have hv' : v ∉ Ioo x y := hv.2
    simp only [mem_Ioo, not_and, not_lt] at hu' hv'
    have h1 := hgap x hxS
    have h2 := hgap y hyS
    have hux : u = x := by
      rcases h1 with h1 | h1
      · rcases le_or_gt u x with h | h
        · exact le_antisymm h h1
        · linarith [hu' h, hzI.2]
      · linarith [hzI.1]
    have hvy : v = y := by
      rcases h2 with h2 | h2
      · linarith [hzI.2]
      · rcases le_or_gt y v with h | h
        · exact le_antisymm h2 h
        · linarith [hv' (by linarith [hzI.1]), hzI.1]
    rw [hux, hvy]
    exact he
  have hsub := hmin _ hS' sdiff_subset
  intro z hz
  by_contra h
  push Not at h
  exact (hsub hz).2 ⟨h.1, h.2⟩

/-! ### Step 2: collapsing the gaps -/

/-- The last point of `m` before `t`. -/
noncomputable def lastBefore (m : Set ℝ) (t : ℝ) : ℝ := sSup (m ∩ Iic t)

/-- The first point of `m` after `t`. -/
noncomputable def firstAfter (m : Set ℝ) (t : ℝ) : ℝ := sInf (m ∩ Ici t)

section Collapse

variable {m : Set ℝ} (hmc : IsClosed m) (h0 : (0 : ℝ) ∈ m) (h1 : (1 : ℝ) ∈ m)
include hmc

include h0 in
theorem lastBefore_mem {t : ℝ} (ht : 0 ≤ t) : lastBefore m t ∈ m ∩ Iic t :=
  (hmc.inter isClosed_Iic).csSup_mem ⟨0, h0, ht⟩ ⟨t, fun _ hz => hz.2⟩

omit hmc in
theorem le_lastBefore {t z : ℝ} (hz : z ∈ m) (hzt : z ≤ t) : z ≤ lastBefore m t :=
  le_csSup ⟨t, fun _ hz => hz.2⟩ ⟨hz, hzt⟩

include h1 in
theorem firstAfter_mem {t : ℝ} (ht : t ≤ 1) : firstAfter m t ∈ m ∩ Ici t :=
  (hmc.inter isClosed_Ici).csInf_mem ⟨1, h1, ht⟩ ⟨t, fun _ hz => hz.2⟩

omit hmc in
theorem firstAfter_le {t z : ℝ} (hz : z ∈ m) (htz : t ≤ z) : firstAfter m t ≤ z :=
  csInf_le ⟨t, fun _ hz => hz.2⟩ ⟨hz, htz⟩

include h0 in
theorem continuousWithinAt_lastBefore {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (lastBefore m) (Ici t) t := by
  by_cases htm : t ∈ m
  · have hrt : lastBefore m t = t :=
      le_antisymm (lastBefore_mem hmc h0 ht).2 (le_lastBefore htm le_rfl)
    rw [ContinuousWithinAt, hrt]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ?_ ?_
    · exact eventually_nhdsWithin_of_forall fun s (hs : t ≤ s) =>
        le_lastBefore htm hs
    · exact eventually_nhdsWithin_of_forall fun s (hs : t ≤ s) =>
        (lastBefore_mem hmc h0 (ht.trans hs)).2
  · obtain ⟨l, u, ⟨hlt, htu⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (hmc.isOpen_compl.mem_nhds htm)
    refine tendsto_const_nhds.congr' (Filter.mem_of_superset (Ico_mem_nhdsGE htu) ?_)
    intro s hs
    show lastBefore m t = lastBefore m s
    unfold lastBefore
    congr 1
    ext z
    simp only [mem_inter_iff, mem_Iic]
    constructor
    · rintro ⟨hz, hzt⟩
      exact ⟨hz, hzt.trans hs.1⟩
    · rintro ⟨hz, hzs⟩
      refine ⟨hz, ?_⟩
      by_contra hzt
      push Not at hzt
      exact hsub ⟨by linarith, by linarith [hs.2]⟩ hz

include h1 in
theorem continuousWithinAt_firstAfter {t : ℝ} (ht : t ≤ 1) :
    ContinuousWithinAt (firstAfter m) (Iic t) t := by
  by_cases htm : t ∈ m
  · have hrt : firstAfter m t = t :=
      le_antisymm (firstAfter_le htm le_rfl) (firstAfter_mem hmc h1 ht).2
    rw [ContinuousWithinAt, hrt]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) tendsto_const_nhds ?_ ?_
    · exact eventually_nhdsWithin_of_forall fun s (hs : s ≤ t) =>
        (firstAfter_mem hmc h1 (hs.trans ht)).2
    · exact eventually_nhdsWithin_of_forall fun s (hs : s ≤ t) =>
        firstAfter_le htm hs
  · obtain ⟨l, u, ⟨hlt, htu⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (hmc.isOpen_compl.mem_nhds htm)
    refine tendsto_const_nhds.congr' (Filter.mem_of_superset (Ioc_mem_nhdsLE hlt) ?_)
    intro s hs
    show firstAfter m t = firstAfter m s
    unfold firstAfter
    congr 1
    ext z
    simp only [mem_inter_iff, mem_Ici]
    constructor
    · rintro ⟨hz, hzt⟩
      exact ⟨hz, hs.2.trans hzt⟩
    · rintro ⟨hz, hzs⟩
      refine ⟨hz, ?_⟩
      by_contra hzt
      push Not at hzt
      exact hsub ⟨by linarith [hs.1], by linarith⟩ hz

end Collapse

omit [T2Space X] in
/-- The collapsed path `t ↦ g (lastBefore m t)` on `[0,1]`. -/
theorem collapse_properties {g : ℝ → X} (hg : Continuous g) {m : Set ℝ} (hm : Admissible g m)
    (hmin : ∀ S, Admissible g S → S ⊆ m → m ⊆ S) :
    Continuous (fun t : I => g (lastBefore m t)) ∧
      (∀ x w y : I, x ≤ w → w ≤ y → g (lastBefore m x) = g (lastBefore m y) →
        g (lastBefore m w) = g (lastBefore m x)) ∧
      g (lastBefore m 0) = g 0 ∧ g (lastBefore m 1) = g 1 := by
  obtain ⟨hmc, hm01, h0, h1, hgap⟩ := hm
  have hmem : ∀ t : I, lastBefore m t ∈ m ∩ Iic (t : ℝ) := fun t =>
    lastBefore_mem hmc h0 t.2.1
  have key : ∀ t ∈ Icc (0 : ℝ) 1, g (lastBefore m t) = g (firstAfter m t) := by
    intro t ht
    have hr := lastBefore_mem hmc h0 ht.1
    have hr' := firstAfter_mem hmc h1 ht.2
    rcases eq_or_lt_of_le ((mem_Iic.1 hr.2).trans (mem_Ici.1 hr'.2)) with h | h
    · rw [h]
    · refine hgap _ hr.1 _ hr'.1 h fun z hz => ?_
      rcases le_total z t with hzt | hzt
      · exact Or.inl (le_lastBefore hz hzt)
      · exact Or.inr (firstAfter_le hz hzt)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hcont : ContinuousOn (fun t => g (lastBefore m t)) (Icc 0 1) := by
      intro t ht
      rw [continuousWithinAt_iff_continuous_left_right]
      constructor
      · have := (hg.continuousAt (x := firstAfter m t)).comp_continuousWithinAt
          (continuousWithinAt_firstAfter hmc h1 ht.2)
        exact (this.mono inter_subset_right).congr (fun s hs => key s hs.1) (key t ht)
      · exact ((hg.continuousAt).comp_continuousWithinAt
          (continuousWithinAt_lastBefore hmc h0 ht.1)).mono inter_subset_right
    exact hcont.domRestrict
  · intro x w y hxw hwy he
    have hrx := hmem x
    have hry := hmem y
    have hrw := hmem w
    have hxw' : lastBefore m x ≤ lastBefore m w := le_lastBefore hrx.1 (hrx.2.trans hxw)
    have hwy' : lastBefore m w ≤ lastBefore m y := le_lastBefore hrw.1 (hrw.2.trans hwy)
    rcases eq_or_lt_of_le (hxw'.trans hwy') with h | h
    · rw [le_antisymm hxw' (h ▸ hwy')]
    · rcases gap_of_minimal ⟨hmc, hm01, h0, h1, hgap⟩ hmin hrx.1 hry.1 h he _ hrw.1 with
        h' | h'
      · rw [le_antisymm h' hxw']
      · rw [le_antisymm hwy' h', he]
  · congr 1
    exact le_antisymm (lastBefore_mem hmc h0 le_rfl).2 (le_lastBefore h0 le_rfl)
  · congr 1
    exact le_antisymm (lastBefore_mem hmc h0 zero_le_one).2 (le_lastBefore h1 le_rfl)

end ArcAux

open ArcAux in
/-- `fact:tietze-arc`: in a Hausdorff space, the image of a path from `a` to `b ≠ a` contains a
simple arc from `a` to `b`. -/
theorem exists_arc_in_path' {E : Type*} [TopologicalSpace E] [T2Space E] {a b : E}
    (g : Path a b) (hab : a ≠ b) : ∃ γ ⊆ range g, IsArc γ a b := by
  obtain ⟨m, hm, hmin⟩ := exists_minimal_admissible g.extend g.continuous_extend
  obtain ⟨hf, hconv, hf0, hf1⟩ := collapse_properties g.continuous_extend hm hmin
  set f : I → E := fun t => g.extend (lastBefore m t) with hfdef
  rw [Path.extend_zero] at hf0
  rw [Path.extend_one] at hf1
  replace hf0 : f 0 = a := by
    show g.extend (lastBefore m ((0 : I) : ℝ)) = a
    rw [Set.Icc.coe_zero]; exact hf0
  replace hf1 : f 1 = b := by
    show g.extend (lastBefore m ((1 : I) : ℝ)) = b
    rw [Set.Icc.coe_one]; exact hf1
  have hfg : range f ⊆ range g := by
    rw [← Path.extend_range]
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨h, hh, hmono, hfh⟩ := exists_separating_monotone f hf hconv
  obtain ⟨q, hq, hqr⟩ := exists_injective_path_of_monotone f hf h hh hmono hfh
    (by rw [hf0, hf1]; exact hab)
  exact ⟨range q, hqr.trans hfg, q.cast hf0.symm hf1.symm, hq, rfl⟩

end TJK
