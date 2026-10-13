import Mathlib
import TJK.Defs
import TJK.Baire.Basic
import TJK.Construct.Regions

/-!
# Special families and special functions (blueprint §F)

Formalizes `def:special-family`, `lem:special-from-fsigma`, `lem:special-sequence`,
`def:special-pair`, `lem:special-pair-exists` and `lem:special-pair-shrink` of
`paper/sections/F-construct.tex`.

Subsets of `X = (-1, 1)` are subsets of `ℝ` contained in `Ioo (-1) 1`. Being `F_σ` (`F_σδ`) in
`X` is expressed as being `F_σ` (`F_σδ`) in `ℝ`; for subsets of `X` the two notions agree because
`X` is open, hence `F_σ`, in `ℝ` (see `TJK.isFσ_subtype_iff`, `TJK.IsFσ.of_subtype`).

* `IsSpecialFamily 𝓕`: `𝓕` is a countable family of compact subsets of `X`, any two distinct
  members of which are disjoint or split. (The paper also asks `𝓕 ≠ ∅`; nothing uses this.)
* `endpoints 𝓕` is `E(𝓕)`, `twoPoint 𝓕` is `𝓕²`.
* `IsSpecialPair 𝓕 α β θ ε δ`: `(ε, δ)` is a pair of special `α, β, θ` functions for `𝓕`.

For `lem:special-from-fsigma` the open sets `X \ A_n` are covered by the maximal dyadic intervals
they contain (`dyadicSel`), instead of by bi-infinite chains of intervals in each component.
-/

namespace TJK.Construct

open _root_.Set Metric Real

/-! ### Special families (`def:special-family`) -/

/-- A *special family*: a countable family of compact subsets of `X = (-1, 1)`, any two distinct
members of which are disjoint or split. -/
structure IsSpecialFamily (𝓕 : Set (Set ℝ)) : Prop where
  countable : 𝓕.Countable
  isCompact : ∀ F ∈ 𝓕, IsCompact F
  subset : ∀ F ∈ 𝓕, F ⊆ Ioo (-1) 1
  pairwise : 𝓕.Pairwise fun F G => Disjoint F G ∨ Split F G

/-- `E(𝓕)`: the endpoints of the intervals `J(F)`, `F ∈ 𝓕`, `F ≠ ∅`. -/
def endpoints (𝓕 : Set (Set ℝ)) : Set ℝ :=
  {x | ∃ F ∈ 𝓕, F.Nonempty ∧ (x = sInf F ∨ x = sSup F)}

/-- `𝓕²`: the members of `𝓕` with at least two points. -/
def twoPoint (𝓕 : Set (Set ℝ)) : Set (Set ℝ) :=
  {F | F ∈ 𝓕 ∧ F.Nontrivial}

theorem Split.symm {E₁ E₂ : Set ℝ} (h : Split E₁ E₂) : Split E₂ E₁ := by
  obtain ⟨p, h | h⟩ := h
  exacts [⟨p, Or.inr h⟩, ⟨p, Or.inl h⟩]

theorem Split.mono {E₁ E₂ F₁ F₂ : Set ℝ} (h : Split E₁ E₂) (h₁ : F₁ ⊆ E₁) (h₂ : F₂ ⊆ E₂) :
    Split F₁ F₂ := by
  obtain ⟨p, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := h
  · exact ⟨p, Or.inl ⟨fun x hx => ha x (h₁ hx), fun x hx => hb x (h₂ hx)⟩⟩
  · exact ⟨p, Or.inr ⟨fun x hx => ha x (h₂ hx), fun x hx => hb x (h₁ hx)⟩⟩

/-- Endpoints of `J(F)` belong to `F`. -/
theorem IsSpecialFamily.exists_mem_of_mem_endpoints {𝓕 : Set (Set ℝ)} (h : IsSpecialFamily 𝓕)
    {e : ℝ} (he : e ∈ endpoints 𝓕) :
    ∃ F ∈ 𝓕, F.Nonempty ∧ (e = sInf F ∨ e = sSup F) ∧ e ∈ F := by
  obtain ⟨F, hF, hne, he'⟩ := he
  refine ⟨F, hF, hne, he', ?_⟩
  rcases he' with rfl | rfl
  exacts [(h.isCompact F hF).sInf_mem hne, (h.isCompact F hF).sSup_mem hne]

/-- A point of `E(𝓕)` inside `J(F)^*` does not belong to `F` (remark after
`def:special-family`). -/
theorem IsSpecialFamily.notMem_of_mem_Ioo {𝓕 : Set (Set ℝ)} (h : IsSpecialFamily 𝓕) {e : ℝ}
    (he : e ∈ endpoints 𝓕) {F : Set ℝ} (hF : F ∈ 𝓕) (heF : e ∈ Ioo (sInf F) (sSup F)) :
    e ∉ F := by
  obtain ⟨F', hF', -, he', heF'⟩ := h.exists_mem_of_mem_endpoints he
  have hFF : F' ≠ F := by
    rintro rfl
    rcases he' with rfl | rfl
    exacts [lt_irrefl _ heF.1, lt_irrefl _ heF.2]
  intro heF''
  have hFne : F.Nonempty := ⟨e, heF''⟩
  rcases h.pairwise hF' hF hFF with hd | ⟨p, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact disjoint_left.1 hd heF' heF''
  · have := h1 e heF'
    have := le_csInf hFne h2
    linarith [heF.1]
  · have := h2 e heF'
    have := csSup_le hFne h1
    linarith [heF.2]

/-! ### Dyadic intervals -/

/-- The dyadic interval `[k / 2^m, (k + 1) / 2^m]`. -/
def dyadic (m : ℕ) (k : ℤ) : Set ℝ :=
  Icc ((k : ℝ) / 2 ^ m) (((k : ℝ) + 1) / 2 ^ m)

theorem dyadic_subset_dyadic (j d : ℕ) (k : ℤ) : dyadic (j + d) k ⊆ dyadic j (k / 2 ^ d) := by
  have h2 : (0 : ℤ) < 2 ^ d := by positivity
  have h1 : (((k / 2 ^ d : ℤ) : ℝ)) * 2 ^ d ≤ k := by
    exact_mod_cast Int.ediv_mul_le k h2.ne'
  have h3 : (k : ℝ) + 1 ≤ ((((k / 2 ^ d : ℤ)) : ℝ) + 1) * 2 ^ d := by
    exact_mod_cast Int.add_one_le_iff.2 (Int.lt_ediv_add_one_mul_self k h2)
  have hj : (0 : ℝ) < 2 ^ j := by positivity
  have hd : (0 : ℝ) < 2 ^ d := by positivity
  have hp : (2 : ℝ) ^ (j + d) = 2 ^ j * 2 ^ d := pow_add _ _ _
  rintro x ⟨hx1, hx2⟩
  rw [hp] at hx1 hx2
  constructor
  · calc (((k / 2 ^ d : ℤ)) : ℝ) / 2 ^ j = ((k / 2 ^ d : ℤ) : ℝ) * 2 ^ d / (2 ^ j * 2 ^ d) := by
          field_simp
      _ ≤ k / (2 ^ j * 2 ^ d) := by gcongr
      _ ≤ x := hx1
  · calc x ≤ ((k : ℝ) + 1) / (2 ^ j * 2 ^ d) := hx2
      _ ≤ ((((k / 2 ^ d : ℤ)) : ℝ) + 1) * 2 ^ d / (2 ^ j * 2 ^ d) := by gcongr
      _ = ((((k / 2 ^ d : ℤ)) : ℝ) + 1) / 2 ^ j := by field_simp

/-- The maximal dyadic intervals contained in `U`: `dyadic m k ⊆ U` and no strictly larger dyadic
interval containing it lies in `U`. -/
def dyadicSel (U : Set ℝ) : Set (ℕ × ℤ) :=
  {p | dyadic p.1 p.2 ⊆ U ∧ ∀ j d : ℕ, j + d = p.1 → 0 < d → ¬dyadic j (p.2 / 2 ^ d) ⊆ U}

/-- The maximal dyadic intervals contained in an open set cover it. -/
theorem exists_mem_dyadicSel {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    ∃ p ∈ dyadicSel U, x ∈ dyadic p.1 p.2 := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hxk : x ∈ dyadic m ⌊x * 2 ^ m⌋ := by
    constructor
    · rw [div_le_iff₀ h2m]; exact Int.floor_le _
    · rw [le_div_iff₀ h2m]; exact (Int.lt_floor_add_one _).le
  have hkU : dyadic m ⌊x * 2 ^ m⌋ ⊆ U := by
    intro y hy
    apply hball
    rw [mem_ball, Real.dist_eq]
    have hm' : (1 / 2 : ℝ) ^ m = 1 / 2 ^ m := by rw [div_pow, one_pow]
    have : ((⌊x * 2 ^ m⌋ : ℝ) + 1) / 2 ^ m - (⌊x * 2 ^ m⌋ : ℝ) / 2 ^ m = 1 / 2 ^ m := by ring
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hx1, hx2⟩ := hxk
    rw [abs_lt]
    constructor <;> linarith
  have hP : ∃ j, ∃ d, j + d = m ∧ dyadic j (⌊x * 2 ^ m⌋ / 2 ^ d) ⊆ U :=
    ⟨m, 0, by simp, by simpa using hkU⟩
  obtain ⟨d₀, hd₀, hsub⟩ := Nat.find_spec hP
  refine ⟨(Nat.find hP, ⌊x * 2 ^ m⌋ / 2 ^ d₀), ⟨hsub, ?_⟩, ?_⟩
  · intro j d hjd hd hj
    simp only at hjd
    apply Nat.find_min hP (show j < Nat.find hP by omega)
    refine ⟨d₀ + d, by omega, ?_⟩
    rwa [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add] at hj
  · have := dyadic_subset_dyadic (Nat.find hP) d₀ ⌊x * 2 ^ m⌋
    rw [hd₀] at this
    exact this hxk

/-- Two distinct maximal dyadic intervals of `U` split. -/
theorem split_of_mem_dyadicSel {U : Set ℝ} {p p' : ℕ × ℤ} (hp : p ∈ dyadicSel U)
    (hp' : p' ∈ dyadicSel U) (hne : p ≠ p') : Split (dyadic p.1 p.2) (dyadic p'.1 p'.2) := by
  wlog hle : p.1 ≤ p'.1 generalizing p p'
  · exact (this hp' hp hne.symm (le_of_not_ge hle)).symm
  obtain ⟨j, k⟩ := p
  obtain ⟨m', k'⟩ := p'
  simp only at hle ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have h2 : (0 : ℤ) < 2 ^ d := by positivity
  have h1 : k' / 2 ^ d * 2 ^ d ≤ k' := Int.ediv_mul_le k' h2.ne'
  have h3 : k' + 1 ≤ (k' / 2 ^ d + 1) * 2 ^ d :=
    Int.add_one_le_iff.2 (Int.lt_ediv_add_one_mul_self k' h2)
  have hj : (0 : ℝ) < 2 ^ j := by positivity
  have hd : (0 : ℝ) < 2 ^ d := by positivity
  have hpw : (2 : ℝ) ^ (j + d) = 2 ^ j * 2 ^ d := pow_add _ _ _
  rcases lt_trichotomy (k' / 2 ^ d) k with hlt | heq | hgt
  · have hZ : k' + 1 ≤ k * 2 ^ d :=
      h3.trans (mul_le_mul_of_nonneg_right (Int.add_one_le_iff.2 hlt) h2.le)
    have hR : (k' : ℝ) + 1 ≤ k * 2 ^ d := by exact_mod_cast hZ
    refine ⟨k / 2 ^ j, Or.inr ⟨fun x hx => ?_, fun x hx => hx.1⟩⟩
    calc x ≤ ((k' : ℝ) + 1) / 2 ^ (j + d) := hx.2
      _ ≤ k * 2 ^ d / (2 ^ j * 2 ^ d) := by rw [hpw]; gcongr
      _ = k / 2 ^ j := by field_simp
  · rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp only [pow_zero, Int.ediv_one] at heq
      exact (hne (by simp [heq])).elim
    · exact absurd (by rw [heq]; exact hp.1) (hp'.2 j d rfl hd0)
  · have hZ : (k + 1) * 2 ^ d ≤ k' :=
      (mul_le_mul_of_nonneg_right (Int.add_one_le_iff.2 hgt) h2.le).trans h1
    have hR : ((k : ℝ) + 1) * 2 ^ d ≤ k' := by exact_mod_cast hZ
    refine ⟨(k + 1) / 2 ^ j, Or.inl ⟨fun x hx => hx.2, fun x hx => ?_⟩⟩
    calc ((k : ℝ) + 1) / 2 ^ j = (k + 1) * 2 ^ d / (2 ^ j * 2 ^ d) := by field_simp
      _ ≤ k' / (2 ^ j * 2 ^ d) := by gcongr
      _ = k' / 2 ^ (j + d) := by rw [hpw]
      _ ≤ x := hx.1

/-! ### `lem:special-from-fsigma` -/

/-- Every `F_σ` subset of `ℝ` is the union of a countable family of compact sets, any two distinct
members of which are disjoint or split. -/
theorem exists_countable_family_of_isFσ {E : Set ℝ} (hE : IsFσ E) :
    ∃ 𝓕 : Set (Set ℝ), 𝓕.Countable ∧ (∀ F ∈ 𝓕, IsCompact F) ∧
      (𝓕.Pairwise fun F G => Disjoint F G ∨ Split F G) ∧ ⋃₀ 𝓕 = E := by
  obtain ⟨C, hC, rfl⟩ := hE
  set A : ℕ → Set ℝ := fun n => ⋃ i ∈ Finset.range n, C i with hA
  have hAc : ∀ n, IsClosed (A n) := fun n => isClosed_biUnion_finset fun i _ => hC i
  have hAE : ∀ n, A n ⊆ ⋃ i, C i := fun n => iUnion₂_subset fun i _ => subset_iUnion C i
  have hAmono : Monotone A := fun m n hmn =>
    biUnion_subset_biUnion_left (by simpa using Finset.range_subset_range.2 hmn)
  refine ⟨{F | ∃ n, ∃ p ∈ dyadicSel (A n)ᶜ, F = dyadic p.1 p.2 ∩ A (n + 1)}, ?_, ?_, ?_, ?_⟩
  · refine (countable_range fun t : ℕ × ℕ × ℤ => dyadic t.2.1 t.2.2 ∩ A (t.1 + 1)).mono ?_
    rintro F ⟨n, p, -, rfl⟩
    exact ⟨(n, p.1, p.2), rfl⟩
  · rintro F ⟨n, p, -, rfl⟩
    exact isCompact_Icc.inter_right (hAc _)
  · rintro F ⟨n, p, hp, rfl⟩ G ⟨n', p', hp', rfl⟩ hne
    rcases lt_trichotomy n n' with h | rfl | h
    · exact Or.inl (disjoint_left.2 fun x hx hx' => hp'.1 hx'.1 (hAmono h hx.2))
    · have hpp : p ≠ p' := by rintro rfl; exact hne rfl
      exact Or.inr ((split_of_mem_dyadicSel hp hp' hpp).mono inter_subset_left inter_subset_left)
    · exact Or.inl (disjoint_left.2 fun x hx hx' => hp.1 hx.1 (hAmono h hx'.2))
  · apply Subset.antisymm
    · rintro x ⟨F, ⟨n, p, -, rfl⟩, hx⟩
      exact hAE _ hx.2
    · intro x hx
      classical
      have hex : ∃ n, x ∈ A n := by
        obtain ⟨i, hi⟩ := mem_iUnion.1 hx
        exact ⟨i + 1, mem_iUnion₂.2 ⟨i, by simp, hi⟩⟩
      have hn₀ : Nat.find hex ≠ 0 := by
        intro h
        have := Nat.find_spec hex
        rw [h] at this
        simp [hA] at this
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
      have hxn : x ∉ A n := Nat.find_min hex (by omega)
      obtain ⟨p, hp, hxp⟩ := exists_mem_dyadicSel (hAc n).isOpen_compl hxn
      have hx1 : x ∈ A (n + 1) := by
        have := Nat.find_spec hex
        rwa [hn] at this
      exact ⟨_, ⟨n, p, hp, rfl⟩, hxp, hx1⟩

/-- Every `F_σ` subset of `X = (-1, 1)` is the union of a special family. -/
theorem exists_specialFamily_of_isFσ {E : Set ℝ} (hE : IsFσ E) (hEX : E ⊆ Ioo (-1) 1) :
    ∃ 𝓕 : Set (Set ℝ), IsSpecialFamily 𝓕 ∧ ⋃₀ 𝓕 = E := by
  obtain ⟨𝓕, hc, hK, hp, hU⟩ := exists_countable_family_of_isFσ hE
  exact ⟨𝓕, ⟨hc, hK, fun F hF => (subset_sUnion_of_mem hF).trans (hU ▸ hEX), hp⟩, hU⟩

/-! ### `lem:special-sequence` -/

theorem IsSpecialFamily.image2_inter {𝓖 𝓢 : Set (Set ℝ)} (h𝓖 : IsSpecialFamily 𝓖)
    (h𝓢 : IsSpecialFamily 𝓢) : IsSpecialFamily (image2 (· ∩ ·) 𝓖 𝓢) where
  countable := h𝓖.countable.image2 h𝓢.countable _
  isCompact := by
    rintro _ ⟨G, hG, S, hS, rfl⟩
    exact (h𝓖.isCompact G hG).inter_right (h𝓢.isCompact S hS).isClosed
  subset := by
    rintro _ ⟨G, hG, S, hS, rfl⟩
    exact inter_subset_left.trans (h𝓖.subset G hG)
  pairwise := by
    rintro _ ⟨G, hG, S, hS, rfl⟩ _ ⟨G', hG', S', hS', rfl⟩ hne
    by_cases hGG : G = G'
    · subst hGG
      have hSS : S ≠ S' := by rintro rfl; exact hne rfl
      rcases h𝓢.pairwise hS hS' hSS with h | h
      · exact Or.inl (h.mono inter_subset_right inter_subset_right)
      · exact Or.inr (h.mono inter_subset_right inter_subset_right)
    · rcases h𝓖.pairwise hG hG' hGG with h | h
      · exact Or.inl (h.mono inter_subset_left inter_subset_left)
      · exact Or.inr (h.mono inter_subset_left inter_subset_left)

theorem sUnion_image2_inter (𝓖 𝓢 : Set (Set ℝ)) :
    ⋃₀ image2 (· ∩ ·) 𝓖 𝓢 = ⋃₀ 𝓖 ∩ ⋃₀ 𝓢 := by
  ext x
  constructor
  · rintro ⟨_, ⟨G, hG, S, hS, rfl⟩, hxG, hxS⟩
    exact ⟨⟨G, hG, hxG⟩, ⟨S, hS, hxS⟩⟩
  · rintro ⟨⟨G, hG, hxG⟩, ⟨S, hS, hxS⟩⟩
    exact ⟨G ∩ S, mem_image2_of_mem hG hS, hxG, hxS⟩

/-- An `F_σδ` subset `A` of `X` is `⋂ₙ ⋃ 𝓕ₙ` for special families `𝓕ₙ` such that every member of
`𝓕ₙ₊₁` lies in a member of `𝓕ₙ`. -/
theorem exists_specialFamily_seq {A : Set ℝ} (hA : IsFσδ A) (hAX : A ⊆ Ioo (-1) 1) :
    ∃ 𝓕 : ℕ → Set (Set ℝ), (∀ n, IsSpecialFamily (𝓕 n)) ∧ A = ⋂ n, ⋃₀ 𝓕 n ∧
      ∀ n, ∀ K ∈ 𝓕 (n + 1), ∃ F ∈ 𝓕 n, K ⊆ F := by
  obtain ⟨B, hB, rfl⟩ := hA
  have hB' : ∀ n, IsFσ (B n ∩ Ioo (-1) 1) := fun n => (hB n).inter (IsOpen.isFσ isOpen_Ioo)
  choose S hS hSU using fun n => exists_specialFamily_of_isFσ (hB' n) inter_subset_right
  let 𝓕 : ℕ → Set (Set ℝ) := fun n =>
    Nat.rec (motive := fun _ => Set (Set ℝ)) (S 0) (fun n 𝓖 => image2 (· ∩ ·) 𝓖 (S (n + 1))) n
  have h0 : 𝓕 0 = S 0 := rfl
  have hsucc : ∀ n, 𝓕 (n + 1) = image2 (· ∩ ·) (𝓕 n) (S (n + 1)) := fun n => rfl
  have hspec : ∀ n, IsSpecialFamily (𝓕 n) := by
    intro n
    induction n with
    | zero => exact h0 ▸ hS 0
    | succ n ih => rw [hsucc]; exact ih.image2_inter (hS _)
  have hU : ∀ n, ⋃₀ 𝓕 n ⊆ B n := by
    intro n
    cases n with
    | zero => rw [h0, hSU]; exact inter_subset_left
    | succ n =>
      rw [hsucc, sUnion_image2_inter, hSU]
      exact inter_subset_right.trans inter_subset_left
  refine ⟨𝓕, hspec, Subset.antisymm ?_ ?_, ?_⟩
  · intro x hx
    rw [mem_iInter] at hx ⊢
    have hxX := hAX (mem_iInter.2 hx)
    intro n
    induction n with
    | zero => rw [h0, hSU]; exact ⟨hx 0, hxX⟩
    | succ n ih => rw [hsucc, sUnion_image2_inter, hSU]; exact ⟨ih, hx _, hxX⟩
  · exact iInter_mono hU
  · intro n K hK
    rw [hsucc] at hK
    obtain ⟨G, hG, S', -, rfl⟩ := hK
    exact ⟨G, hG, inter_subset_left⟩

/-! ### Special functions (`def:special-pair`, `lem:special-pair-shrink`) -/

/-- `(ε, δ)` is a pair of special `α, β, θ` functions for `𝓕` (`ε` matters on `E(𝓕)`, `δ` on
`𝓕²`). The standing assumption `0 < β < α < θ < π/2` is a hypothesis of the lemmas. -/
structure IsSpecialPair (𝓕 : Set (Set ℝ)) (α β θ : ℝ) (ε : ℝ → ℝ) (δ : Set ℝ → ℝ) : Prop where
  eps_pos : ∀ x ∈ endpoints 𝓕, 0 < ε x
  delta_pos : ∀ F ∈ twoPoint 𝓕, 0 < δ F
  /-- (i) -/
  finite_delta : ∀ η > 0, {F | F ∈ twoPoint 𝓕 ∧ η ≤ δ F}.Finite
  /-- (ii) -/
  finite_eps : ∀ η > 0, {x | x ∈ endpoints 𝓕 ∧ η ≤ ε x}.Finite
  /-- (iii) -/
  disjoint_stolz : (endpoints 𝓕).Pairwise fun x y => Disjoint (stolz x (ε x) θ) (stolz y (ε y) θ)
  /-- (iv) -/
  disjoint_region : (twoPoint 𝓕).Pairwise fun F G =>
    Disjoint (region F (δ F) α β) (region G (δ G) α β)
  /-- (v) -/
  disjoint_stolz_region : ∀ x ∈ endpoints 𝓕, ∀ F ∈ twoPoint 𝓕,
    Disjoint (stolz x (ε x) θ) (region F (δ F) α β)

theorem stolz_mono {a ε ε' θ : ℝ} (h : ε ≤ ε') : stolz a ε θ ⊆ stolz a ε' θ :=
  fun _ ⟨h0, h1, h2⟩ => ⟨h0, h1.trans_le h, h2⟩

theorem region_mono {K : Set ℝ} {ε ε' α β : ℝ} (h : ε ≤ ε') :
    region K ε α β ⊆ region K ε' α β :=
  fun _ ⟨⟨h0, h1, h2, h3⟩, h4⟩ => ⟨⟨h0, h1.trans_le h, h2, h3⟩, h4⟩

/-- `lem:special-pair-shrink`. -/
theorem IsSpecialPair.mono {𝓕 : Set (Set ℝ)} {α β θ : ℝ} {ε ε₁ : ℝ → ℝ} {δ δ₁ : Set ℝ → ℝ}
    (h : IsSpecialPair 𝓕 α β θ ε δ) (hε₁ : ∀ x ∈ endpoints 𝓕, 0 < ε₁ x ∧ ε₁ x ≤ ε x)
    (hδ₁ : ∀ F ∈ twoPoint 𝓕, 0 < δ₁ F ∧ δ₁ F ≤ δ F) : IsSpecialPair 𝓕 α β θ ε₁ δ₁ where
  eps_pos x hx := (hε₁ x hx).1
  delta_pos F hF := (hδ₁ F hF).1
  finite_delta η hη :=
    (h.finite_delta η hη).subset fun F ⟨hF, hle⟩ => ⟨hF, hle.trans (hδ₁ F hF).2⟩
  finite_eps η hη :=
    (h.finite_eps η hη).subset fun x ⟨hx, hle⟩ => ⟨hx, hle.trans (hε₁ x hx).2⟩
  disjoint_stolz x hx y hy hxy :=
    (h.disjoint_stolz hx hy hxy).mono (stolz_mono (hε₁ x hx).2) (stolz_mono (hε₁ y hy).2)
  disjoint_region F hF G hG hFG :=
    (h.disjoint_region hF hG hFG).mono (region_mono (hδ₁ F hF).2) (region_mono (hδ₁ G hG).2)
  disjoint_stolz_region x hx F hF :=
    (h.disjoint_stolz_region x hx F hF).mono (stolz_mono (hε₁ x hx).2) (region_mono (hδ₁ F hF).2)

/-! ### Existence of special pairs (`lem:special-pair-exists`) -/

/-- `t` if `t > 0`, else `1`. -/
noncomputable def posOr (t : ℝ) : ℝ := if 0 < t then t else 1

theorem posOr_pos (t : ℝ) : 0 < posOr t := by
  unfold posOr
  split_ifs with h
  exacts [h, one_pos]

theorem posOr_of_pos {t : ℝ} (h : 0 < t) : posOr t = t := if_pos h

theorem exists_pos_le_abs_sub {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (h : Disjoint K L) : ∃ r > 0, ∀ x ∈ K, ∀ y ∈ L, r ≤ |x - y| := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, by simp⟩
  rcases L.eq_empty_or_nonempty with rfl | hLne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_infDist_pt L).continuousOn
  refine ⟨infDist x₀ L, ?_, fun x hx y hy => ?_⟩
  · exact (infDist_pos_iff_notMem_closure hLne).1
      (by rw [hL.isClosed.closure_eq]; exact disjoint_left.1 h hx₀)
  · rw [← Real.dist_eq]
    exact (isMinOn_iff.1 hmin x hx).trans (infDist_le_dist_of_mem hy)

open Classical in
/-- A positive lower bound for `|x - y|`, `x ∈ K`, `y ∈ L`, when `K`, `L` are disjoint compact
sets (and `1` if there is none). -/
noncomputable def sepDist (K L : Set ℝ) : ℝ :=
  if h : ∃ r > 0, ∀ x ∈ K, ∀ y ∈ L, r ≤ |x - y| then h.choose else 1

theorem sepDist_pos (K L : Set ℝ) : 0 < sepDist K L := by
  unfold sepDist
  split_ifs with h
  exacts [h.choose_spec.1, one_pos]

theorem sepDist_le {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L) (h : Disjoint K L)
    {x y : ℝ} (hx : x ∈ K) (hy : y ∈ L) : sepDist K L ≤ |x - y| := by
  have he := exists_pos_le_abs_sub hK hL h
  unfold sepDist
  rw [dif_pos he]
  exact he.choose_spec.2 x hx y hy

/-- The least `n` with `P (f n)` (`0` if there is none). -/
noncomputable def firstIdx (f : ℕ → Set ℝ) (P : Set ℝ → Prop) : ℕ :=
  sInf {n | P (f n)}

theorem firstIdx_spec {f : ℕ → Set ℝ} {P : Set ℝ → Prop} (h : ∃ n, P (f n)) :
    P (f (firstIdx f P)) :=
  Nat.sInf_mem h

theorem firstIdx_le {f : ℕ → Set ℝ} {P : Set ℝ → Prop} {n : ℕ} (h : P (f n)) :
    firstIdx f P ≤ n :=
  Nat.sInf_le h

/-- `k(F)`: the least index of `F` in the enumeration `f`. -/
noncomputable def memberIdx (f : ℕ → Set ℝ) (F : Set ℝ) : ℕ :=
  firstIdx f (· = F)

/-- `k(e)`: the least index `k` such that `e` is an endpoint of `J(f k)`. -/
noncomputable def endpointIdx (f : ℕ → Set ℝ) (e : ℝ) : ℕ :=
  firstIdx f fun F => F.Nonempty ∧ (e = sInf F ∨ e = sSup F)

/-- The constraint on `δ(F)` coming from the member `f j` (`c = cot θ + cot β`). -/
noncomputable def deltaTerm (f : ℕ → Set ℝ) (β c : ℝ) (F : Set ℝ) (j : ℕ) : ℝ :=
  min (1 / ((j : ℝ) + 1)) (min (posOr (sepDist (f j) F / (2 * cot β)))
    (min (posOr (infDist (sInf (f j)) F / c)) (posOr (infDist (sSup (f j)) F / c))))

/-- The constraint on `ε(e)` coming from the member `f j` (`c = cot θ + cot β`). -/
noncomputable def epsTerm (f : ℕ → Set ℝ) (θ c : ℝ) (e : ℝ) (j : ℕ) : ℝ :=
  min (1 / ((j : ℝ) + 1)) (min (posOr (|e - sInf (f j)| / (2 * cot θ)))
    (min (posOr (|e - sSup (f j)| / (2 * cot θ))) (posOr (infDist e (f j) / c))))

/-- `δ(F) = min_{j ≤ k(F)} deltaTerm F j`. -/
noncomputable def specialDelta (f : ℕ → Set ℝ) (β c : ℝ) (F : Set ℝ) : ℝ :=
  (Finset.range (memberIdx f F + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
    (deltaTerm f β c F)

/-- `ε(e) = min_{j ≤ k(e)} epsTerm e j`. -/
noncomputable def specialEps (f : ℕ → Set ℝ) (θ c : ℝ) (e : ℝ) : ℝ :=
  (Finset.range (endpointIdx f e + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
    (epsTerm f θ c e)

theorem specialDelta_pos (f : ℕ → Set ℝ) (β c : ℝ) (F : Set ℝ) : 0 < specialDelta f β c F :=
  (Finset.lt_inf'_iff _).2 fun j _ => lt_min (by positivity)
    (lt_min (posOr_pos _) (lt_min (posOr_pos _) (posOr_pos _)))

theorem specialEps_pos (f : ℕ → Set ℝ) (θ c : ℝ) (e : ℝ) : 0 < specialEps f θ c e :=
  (Finset.lt_inf'_iff _).2 fun j _ => lt_min (by positivity)
    (lt_min (posOr_pos _) (lt_min (posOr_pos _) (posOr_pos _)))

theorem specialDelta_le {f : ℕ → Set ℝ} {β c : ℝ} {F : Set ℝ} {j : ℕ} (hj : j ≤ memberIdx f F) :
    specialDelta f β c F ≤ deltaTerm f β c F j :=
  Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem specialEps_le {f : ℕ → Set ℝ} {θ c e : ℝ} {j : ℕ} (hj : j ≤ endpointIdx f e) :
    specialEps f θ c e ≤ epsTerm f θ c e j :=
  Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem le_floor_one_div {η : ℝ} (hη : 0 < η) {k : ℕ} (h : η ≤ 1 / ((k : ℝ) + 1)) :
    k ≤ ⌊1 / η⌋₊ := by
  apply Nat.le_floor
  rw [le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ hη]
  nlinarith

/-- `lem:special-pair-exists`: every special family has a pair of special `α, β, θ` functions. -/
theorem exists_specialPair {𝓕 : Set (Set ℝ)} (h𝓕 : IsSpecialFamily 𝓕) {α β θ : ℝ}
    (hβ0 : 0 < β) (hβα : β < α) (hαθ : α < θ) (hθ1 : θ < π / 2) :
    ∃ ε δ, IsSpecialPair 𝓕 α β θ ε δ := by
  rcases 𝓕.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 1, fun _ => 1, by constructor <;> simp [endpoints, twoPoint]⟩
  obtain ⟨f, rfl⟩ := h𝓕.countable.exists_eq_range hne
  have hα0 : 0 < α := hβ0.trans hβα
  have hα1 : α < π / 2 := hαθ.trans hθ1
  have hβ1 : β < π / 2 := hβα.trans hα1
  have hθ0 : 0 < θ := hα0.trans hαθ
  have hcθ := cot_pos_of_lt_pi_div_two hθ0 hθ1
  have hcβ := cot_pos_of_lt_pi_div_two hβ0 hβ1
  have hc0 : 0 < cot θ + cot β := add_pos hcθ hcβ
  have hfk : ∀ F ∈ range f, f (memberIdx f F) = F := fun F ⟨n, hn⟩ =>
    firstIdx_spec (P := (· = F)) ⟨n, hn⟩
  have hfe : ∀ e ∈ endpoints (range f), e = sInf (f (endpointIdx f e)) ∨
      e = sSup (f (endpointIdx f e)) := by
    rintro e ⟨F, ⟨n, rfl⟩, hne, he⟩
    exact (firstIdx_spec (P := fun F => F.Nonempty ∧ (e = sInf F ∨ e = sSup F)) ⟨n, hne, he⟩).2
  refine ⟨specialEps f θ (cot θ + cot β), specialDelta f β (cot θ + cot β),
    fun e _ => specialEps_pos .., fun F _ => specialDelta_pos .., ?_, ?_, ?_, ?_, ?_⟩
  · -- (i)
    intro η hη
    refine ((finite_Iic ⌊1 / η⌋₊).image f).subset ?_
    rintro F ⟨hF, hle⟩
    exact ⟨memberIdx f F, le_floor_one_div hη
      (hle.trans ((specialDelta_le le_rfl).trans (min_le_left _ _))), hfk F hF.1⟩
  · -- (ii)
    intro η hη
    refine ((finite_Iic ⌊1 / η⌋₊).biUnion fun j _ =>
      (finite_singleton (sSup (f j))).insert (sInf (f j))).subset ?_
    rintro e ⟨he, hle⟩
    refine mem_biUnion (x := endpointIdx f e) (le_floor_one_div hη
      (hle.trans ((specialEps_le le_rfl).trans (min_le_left _ _)))) ?_
    rcases hfe e he with h | h
    · exact Or.inl h
    · exact Or.inr h
  · -- (iii)
    have key : ∀ e ∈ endpoints (range f), ∀ e' ∈ endpoints (range f), e ≠ e' →
        endpointIdx f e' ≤ endpointIdx f e →
        Disjoint (stolz e' (specialEps f θ (cot θ + cot β) e') θ)
          (stolz e (specialEps f θ (cot θ + cot β) e) θ) := by
      intro e he e' he' hne hk
      apply stolz_disjoint hθ0 hθ1
      have h1 : 0 < |e - e'| / (2 * cot θ) :=
        div_pos (abs_pos.2 (sub_ne_zero.2 hne)) (mul_pos two_pos hcθ)
      have h2 : specialEps f θ (cot θ + cot β) e ≤ posOr (|e - e'| / (2 * cot θ)) := by
        refine (specialEps_le hk).trans ?_
        rcases hfe e' he' with h | h
        · refine (min_le_right _ _).trans ((min_le_left _ _).trans_eq ?_)
          rw [← h]
        · refine (min_le_right _ _).trans ((min_le_right _ _).trans
            ((min_le_left _ _).trans_eq ?_))
          rw [← h]
      rwa [posOr_of_pos h1, abs_sub_comm] at h2
    intro x hx y hy hxy
    rcases le_total (endpointIdx f x) (endpointIdx f y) with h | h
    · exact key y hy x hx hxy.symm h
    · exact (key x hx y hy hxy h).symm
  · -- (iv)
    have key : ∀ F ∈ twoPoint (range f), ∀ G ∈ twoPoint (range f), Disjoint G F →
        memberIdx f G < memberIdx f F →
        Disjoint (region G (specialDelta f β (cot θ + cot β) G) α β)
          (region F (specialDelta f β (cot θ + cot β) F) α β) := by
      intro F hF G hG hd hk
      have hGc := h𝓕.isCompact G hG.1
      have hFc := h𝓕.isCompact F hF.1
      refine region_disjoint_of_disjoint hGc hG.2.nonempty hFc hF.2.nonempty hα0 hα1 hβ0 hβ1
        fun x₁ hx₁ x₂ hx₂ => ?_
      calc specialDelta f β (cot θ + cot β) F
          ≤ deltaTerm f β (cot θ + cot β) F (memberIdx f G) := specialDelta_le hk.le
        _ ≤ posOr (sepDist (f (memberIdx f G)) F / (2 * cot β)) :=
          (min_le_right _ _).trans (min_le_left _ _)
        _ = sepDist G F / (2 * cot β) := by
          rw [hfk G hG.1, posOr_of_pos (div_pos (sepDist_pos _ _) (mul_pos two_pos hcβ))]
        _ ≤ |x₁ - x₂| / (2 * cot β) :=
          div_le_div_of_nonneg_right (sepDist_le hGc hFc hd hx₁ hx₂) (mul_pos two_pos hcβ).le
    intro F hF G hG hFG
    rcases h𝓕.pairwise hF.1 hG.1 hFG with hd | hs
    · have hk : memberIdx f F ≠ memberIdx f G := fun h =>
        hFG (by rw [← hfk F hF.1, ← hfk G hG.1, h])
      rcases lt_or_gt_of_ne hk with h | h
      · exact key G hG F hF hd h
      · exact (key F hF G hG hd.symm h).symm
    · exact region_disjoint_of_split hF.2.nonempty hG.2.nonempty hα0 hα1 hs
  · -- (v)
    intro e he F hF
    have hFc := h𝓕.isCompact F hF.1
    have hFne := hF.2.nonempty
    by_cases hin : e ∈ Ioo (sInf F) (sSup F)
    swap
    · exact (region_stolz_disjoint_of_not_mem_interior hα0 hαθ hθ1 hin).symm
    have heF := h𝓕.notMem_of_mem_Ioo he hF.1 hin
    have hd : 0 < infDist e F / (cot θ + cot β) :=
      div_pos ((infDist_pos_iff_notMem_closure hFne).1 (by rwa [hFc.isClosed.closure_eq])) hc0
    rcases le_or_gt (memberIdx f F) (endpointIdx f e) with hk | hk
    · apply stolz_region_disjoint_small_stolz hFc hFne hα0 hα1 hβ0 hβ1 hθ0 hθ1
      calc specialEps f θ (cot θ + cot β) e
          ≤ epsTerm f θ (cot θ + cot β) e (memberIdx f F) := specialEps_le hk
        _ ≤ posOr (infDist e (f (memberIdx f F)) / (cot θ + cot β)) :=
          (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
        _ = infDist e F / (cot θ + cot β) := by rw [hfk F hF.1, posOr_of_pos hd]
    · apply stolz_region_disjoint_small_region hFc hFne hα0 hα1 hβ0 hβ1 hθ0 hθ1
      refine (specialDelta_le hk.le).trans ?_
      rcases hfe e he with h | h
      · refine (min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_left _ _).trans_eq ?_))
        rw [← h, posOr_of_pos hd]
      · refine (min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans_eq ?_))
        rw [← h, posOr_of_pos hd]

end TJK.Construct
