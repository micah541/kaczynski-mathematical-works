import Mathlib

/-!
# Kaczynski's proof of Wedderburn's theorem (blueprint §J)

Formalizes `paper/sections/J-wedderburn.tex` (Kaczynski, Amer. Math. Monthly 71 (1964)):

* `exists_sq_add_sq_eq_neg_one` (`lem:wb-squares`);
* `exists_quaternion_of_not_isCyclic` (`lem:wb-pgroup`), the special case of the classification of
  `p`-groups with a unique subgroup of order `p` that the note uses;
* `isCyclic_sylow` (`lem:wb-sylow`);
* `mul_comm` (`thm:wedderburn`): every finite division ring is commutative.

Mathlib proves Wedderburn's theorem as the instance `littleWedderburn` (Witt's proof). The proof here
does not use it; `mul_comm` is stated for a `DivisionRing` so that no `Field` structure is available.
-/

namespace TJK.Wedderburn

-- Make sure that instance search never produces Mathlib's `Field` structure on a finite division
-- ring (which is Wedderburn's theorem).
attribute [-instance] littleWedderburn

/-- `lem:wb-squares`. -/
theorem exists_sq_add_sq_eq_neg_one (q : ℕ) [Fact q.Prime] :
    ∃ t r : ZMod q, t ≠ 0 ∧ t ^ 2 + r ^ 2 = -1 := by
  obtain ⟨a, b, h⟩ := ZMod.sq_add_sq q (-1)
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst ha hb
      simp at h
    · exact ⟨b, a, hb, by rw [add_comm]; exact h⟩
  · exact ⟨a, b, ha, h⟩


/-! ### Number theory for `lem:wb-pgroup` -/

/-- If `Σ = p ^ k * u` with `p ∤ u` and `p ^ k ∣ σ`, then `σ + j Σ ≡ 0 (mod p ^ n)` is solvable. -/
theorem exists_dvd_add_mul (p n k u σ : ℕ) [hp : Fact p.Prime] (hu : ¬ p ∣ u)
    (hσ : p ^ k ∣ σ) : ∃ j : ℕ, p ^ n ∣ σ + j * (p ^ k * u) := by
  obtain ⟨s, rfl⟩ := hσ
  have hcop : Nat.Coprime u (p ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hu))
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  refine ⟨(-(s : ZMod (p ^ n)) * (u : ZMod (p ^ n))⁻¹).val, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  have h1 := ZMod.coe_mul_inv_eq_one u hcop
  linear_combination (-((p : ZMod (p ^ n)) ^ k * s)) * h1

/-- If `ρ ≢ 1 (mod p)` then `1 + ρ + ⋯ + ρ ^ (p - 1) ≡ 1 (mod p)` (Fermat). -/
theorem not_dvd_geom_sum (p ρ : ℕ) [hp : Fact p.Prime] (h : ¬ ρ ≡ 1 [MOD p]) :
    ¬ p ∣ ∑ i ∈ Finset.range p, ρ ^ i := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  have hρ : (ρ : ZMod p) - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h'; apply h
    rw [← ZMod.natCast_eq_natCast_iff]; simpa using h'
  have := geom_sum_mul (ρ : ZMod p) p
  rw [ZMod.pow_card] at this
  intro h0
  rw [h0, zero_mul] at this
  exact hρ this.symm

/-- For `p` odd and `ρ ≡ 1 (mod p)`, `1 + ρ + ⋯ + ρ ^ (p - 1) ≡ p (mod p ^ 2)`. -/
theorem geom_sum_eq_mul (p ρ : ℕ) [hp : Fact p.Prime] (hodd : Odd p) (h : ρ ≡ 1 [MOD p]) :
    ∃ u, ∑ i ∈ Finset.range p, ρ ^ i = p * u ∧ ¬ p ∣ u := by
  have hp2 := hp.out.two_le
  have key : ((∑ i ∈ Finset.range p, ρ ^ i : ℕ) : ZMod (p ^ 2)) = p := by
    obtain ⟨c, hc⟩ : ∃ c, ρ = 1 + p * c := by
      refine ⟨ρ / p, ?_⟩
      have h1 : ρ % p = 1 := by
        have := h; unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_of_lt (by omega)
      have := Nat.div_add_mod ρ p
      omega
    have hP : (p : ZMod (p ^ 2)) ^ 2 = 0 := by exact_mod_cast ZMod.natCast_self (p ^ 2)
    have hpow : ∀ i : ℕ, ((1 : ZMod (p ^ 2)) + p * c) ^ i = 1 + i * p * c := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ ((1 : ZMod (p ^ 2)) + p * c) i, ih]; push_cast
        linear_combination (i * c ^ 2) * hP
    obtain ⟨m, hm⟩ := hodd
    have h2 : ∑ i ∈ Finset.range p, i = p * m := by
      have := Finset.sum_range_id_mul_two p
      have h3 : p - 1 = 2 * m := by omega
      rw [h3] at this
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
      rw [this]; ring
    have hsum : ∑ i ∈ Finset.range p, (i : ZMod (p ^ 2)) = p * m := by
      have := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) h2
      push_cast at this
      exact this
    push_cast
    rw [hc]
    push_cast
    simp_rw [hpow]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.sum_mul,
      ← Finset.sum_mul, hsum]
    simp only [nsmul_eq_mul, mul_one]
    linear_combination (m * c) * hP
  have hmod : ∑ i ∈ Finset.range p, ρ ^ i ≡ p [MOD p ^ 2] := by
    rw [← ZMod.natCast_eq_natCast_iff]; exact key
  have hdvd : p ∣ ∑ i ∈ Finset.range p, ρ ^ i := by
    have := hmod.of_dvd (dvd_pow_self p two_ne_zero)
    exact (Nat.modEq_zero_iff_dvd).mp (this.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, hu, ?_⟩
  rintro ⟨v, rfl⟩
  have : ((∑ i ∈ Finset.range p, ρ ^ i : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [hu, ← mul_assoc, ← sq, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  rw [key, ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd hp.out.pos this
  nlinarith

/-- The case analysis on `ρ` in the proof of `lem:wb-pgroup`: with `Σ = 1 + ρ + ⋯ + ρ ^ (p - 1)`,
either `σ + j Σ ≡ 0 (mod p ^ n)` for some `j`, or `p = 2`, `ρ ≡ -1` and `σ ≡ 2 ^ (n - 1)`
(mod `2 ^ n`). -/
theorem nt_main (p n ρ σ : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) (hσ : p ∣ σ)
    (hρσ : ρ * σ ≡ σ [MOD p ^ n]) :
    (∃ j : ℕ, p ^ n ∣ σ + j * ∑ i ∈ Finset.range p, ρ ^ i) ∨
      (p = 2 ∧ 2 ^ n ∣ ρ + 1 ∧ 2 ≤ n ∧ σ ≡ 2 ^ (n - 1) [MOD 2 ^ n]) := by
  rcases hp.out.eq_two_or_odd' with rfl | hodd
  · have hS : ∑ i ∈ Finset.range 2, ρ ^ i = ρ + 1 := by
      simp [Finset.sum_range_succ, add_comm]
    rw [hS]
    have h4 : ρ % 4 = 0 ∨ ρ % 4 = 1 ∨ ρ % 4 = 2 ∨ ρ % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · left
      simpa using exists_dvd_add_mul 2 n 0 (ρ + 1) σ (by omega) (by simp)
    · left
      obtain ⟨j, hj⟩ := exists_dvd_add_mul 2 n 1 ((ρ + 1) / 2) σ (by omega) (by simpa using hσ)
      refine ⟨j, ?_⟩
      convert hj using 3
      omega
    · left
      simpa using exists_dvd_add_mul 2 n 0 (ρ + 1) σ (by omega) (by simp)
    · have hσ' : 2 ^ (n - 1) ∣ σ := by
        have h1 : 2 ^ n ∣ σ * (ρ - 1) := by
          have := (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_left σ (by omega))).mp hρσ.symm
          rwa [← Nat.sub_one_mul, mul_comm] at this
        have hw : ρ - 1 = 2 * ((ρ - 1) / 2) := by omega
        have hwodd : ¬ 2 ∣ (ρ - 1) / 2 := by omega
        rw [hw, show 2 ^ n = 2 * 2 ^ (n - 1) by rw [← pow_succ']; congr 1; omega,
          mul_left_comm] at h1
        have h2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
        exact (Nat.Coprime.pow_left _
          ((Nat.prime_two.coprime_iff_not_dvd).mpr hwodd)).dvd_of_dvd_mul_right h2
      obtain ⟨k, u, hu, hku⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd (show ρ + 1 ≠ 0 by omega) 2 (by norm_num)
      by_cases hk : k ≤ n - 1
      · left
        rw [hku]
        exact exists_dvd_add_mul 2 n k u σ hu ((pow_dvd_pow 2 hk).trans hσ')
      · by_cases h2n : 2 ^ n ∣ σ
        · left
          exact ⟨0, by simpa using h2n⟩
        · right
          refine ⟨rfl, ?_, ?_, ?_⟩
          · rw [hku]
            exact (pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _)
          · by_contra hn2
            apply h2n
            have : n = 1 := by omega
            subst this
            simpa using hσ
          · obtain ⟨s, hs⟩ := hσ'
            have hs_odd : s % 2 = 1 := by
              by_contra hs2
              apply h2n
              obtain ⟨l, hl⟩ : 2 ∣ s := by omega
              rw [hs, hl, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
              exact dvd_mul_right _ _
            have : s = 2 * (s / 2) + 1 := by omega
            rw [hs, this, mul_add, mul_one, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
            unfold Nat.ModEq
            simp
  · left
    by_cases h1 : ρ ≡ 1 [MOD p]
    · obtain ⟨u, hu, hnu⟩ := geom_sum_eq_mul p ρ hodd h1
      rw [hu]
      simpa using exists_dvd_add_mul p n 1 u σ hnu (by simpa using hσ)
    · simpa using exists_dvd_add_mul p n 0 _ σ (not_dvd_geom_sum p ρ h1) (by simp)


/-! ### `p`-groups with a unique subgroup of order `p` -/

open Subgroup in
/-- The inductive step of `lem:wb-pgroup`: `G` of order `p ^ (n + 1)` with a cyclic normal subgroup
`⟨x⟩` of index `p`. -/
theorem quaternion_core {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (huniq : ∀ H K : Subgroup G, Nat.card H = p → Nat.card K = p → H = K)
    (hnc : ¬ IsCyclic G) (x : G) (n : ℕ) (hn : 1 ≤ n) (hx : orderOf x = p ^ n)
    (hcard : Nat.card G = p ^ (n + 1)) (hnorm : (zpowers x).Normal) :
    p = 2 ∧ ∃ a b : G, orderOf a = 4 ∧ orderOf b = 4 ∧ b * a * b⁻¹ = a⁻¹ := by
  have hp1 := hp.out.one_lt
  -- no element outside `⟨x⟩` has order `p`
  have hout : ∀ g : G, g ∉ zpowers x → g ^ p ≠ 1 := by
    intro g hg hgp
    have hg1 : g ≠ 1 := fun h => hg (h ▸ one_mem _)
    have hog : orderOf g = p := orderOf_eq_prime hgp hg1
    have hx'p : (x ^ (p ^ (n - 1))) ^ p = 1 := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, ← hx, pow_orderOf_eq_one]
    have hx'1 : x ^ (p ^ (n - 1)) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by positivity)
        (by rw [hx]; exact Nat.pow_lt_pow_right hp1 (by omega))
    have hox' : orderOf (x ^ (p ^ (n - 1))) = p := orderOf_eq_prime hx'p hx'1
    have := huniq (zpowers g) (zpowers (x ^ (p ^ (n - 1))))
      (by rw [Nat.card_zpowers, hog]) (by rw [Nat.card_zpowers, hox'])
    apply hg
    have hgm : g ∈ zpowers (x ^ (p ^ (n - 1))) := this ▸ mem_zpowers g
    exact (zpowers_le.mpr (npow_mem_zpowers x _)) hgm
  -- an element `y` outside `⟨x⟩`
  have hlt : Nat.card (zpowers x) < Nat.card G := by
    rw [Nat.card_zpowers, hx, hcard]; exact Nat.pow_lt_pow_right hp1 (by omega)
  obtain ⟨y, hy⟩ : ∃ y, y ∉ zpowers x := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : zpowers x = ⊤ := eq_top_iff.mpr fun g _ => h g
    rw [this, card_top] at hlt
    exact lt_irrefl _ hlt
  have hindex : (zpowers x).index = p := by
    have := (zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx, hcard, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ, x ^ σ = y ^ p := by
    have := (zpowers x).pow_index_mem y
    rw [hindex, ← mem_powers_iff_mem_zpowers] at this
    exact this
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℕ, x ^ ρ = y⁻¹ * x * y := by
    have := hnorm.conj_mem x (mem_zpowers x) y⁻¹
    rw [inv_inv, ← mem_powers_iff_mem_zpowers] at this
    exact this
  have hxy : x * y = y * x ^ ρ := by rw [hρdef]; group
  have hF1 : ∀ k : ℕ, x ^ k * y = y * x ^ (ρ * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_assoc, hxy, ← mul_assoc, ih, mul_assoc, ← pow_add, mul_add, mul_one]
  have hF2 : ∀ j k : ℕ, (y * x ^ j) ^ k = y ^ k * x ^ (j * ∑ i ∈ Finset.range k, ρ ^ i) := by
    intro j k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, geom_sum_succ, mul_assoc, ← mul_assoc (x ^ _), hF1, mul_assoc,
        ← pow_add, ← mul_assoc, ← pow_succ]
      congr 2
      ring
  -- `p ∣ σ`, otherwise `y` generates `G`
  have hσ : p ∣ σ := by
    by_contra hpσ
    apply hnc
    have hcop : Nat.Coprime (orderOf x) σ := by
      rw [hx]; exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpσ)
    have hoyp : orderOf (y ^ p) = p ^ n := by rw [← hσdef, hcop.orderOf_pow, hx]
    apply isCyclic_of_orderOf_eq_card y
    rw [hcard]
    apply orderOf_eq_prime_pow
    · intro h
      have : (y ^ p) ^ (p ^ (n - 1)) = 1 := by
        rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hn]; exact h
      exact pow_ne_one_of_lt_orderOf (by positivity)
        (by rw [hoyp]; exact Nat.pow_lt_pow_right hp1 (by omega)) this
    · rw [← hcard]; exact pow_card_eq_one'
  -- `ρ σ ≡ σ`, as `y ^ p` commutes with `y`
  have hρσ : ρ * σ ≡ σ [MOD p ^ n] := by
    rw [← hx, ← pow_eq_pow_iff_modEq]
    apply mul_left_cancel (a := y)
    rw [← hF1, hσdef, ← pow_succ, pow_succ']
  rcases nt_main p n ρ σ hn hσ hρσ with ⟨j, hj⟩ | ⟨rfl, hρ1, hn2, hσ2⟩
  · exfalso
    apply hout (y * x ^ j)
    · intro hm
      apply hy
      have : y = y * x ^ j * (x ^ j)⁻¹ := by group
      rw [this]
      exact mul_mem hm (inv_mem (npow_mem_zpowers x j))
    · rw [hF2, ← hσdef, ← pow_add]
      rw [← hx] at hj
      exact orderOf_dvd_iff_pow_eq_one.mp hj
  · refine ⟨rfl, ?_⟩
    have hxρ : x ^ ρ = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ]
      exact orderOf_dvd_iff_pow_eq_one.mp (hx ▸ hρ1)
    have hyx : y * x * y⁻¹ = x⁻¹ := by
      have h1 : x * y = y * x⁻¹ := by rw [hxy, hxρ]
      have h2 : y * x = x⁻¹ * y := by
        calc y * x = x⁻¹ * (x * y) * x := by group
          _ = x⁻¹ * y := by rw [h1]; group
      rw [h2]; group
    have hy2 : y ^ 2 = x ^ (2 ^ (n - 1)) := by
      rw [← hσdef, pow_eq_pow_iff_modEq, hx]; exact hσ2
    have hne : x ^ (2 ^ (n - 1)) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by positivity) (by rw [hx]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    have ha2 : (x ^ (2 ^ (n - 2))) ^ 2 = x ^ (2 ^ (n - 1)) := by
      rw [← pow_mul, ← pow_succ]; congr 2; omega
    have hx1 : (x ^ (2 ^ (n - 1))) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, ← hx, pow_orderOf_eq_one]
    refine ⟨x ^ (2 ^ (n - 2)), y, ?_, ?_, ?_⟩
    · rw [show 4 = 2 ^ (1 + 1) by norm_num]
      apply orderOf_eq_prime_pow
      · rw [pow_one, ha2]; exact hne
      · rw [pow_succ, pow_one, pow_mul, ha2, hx1]
    · rw [show 4 = 2 ^ (1 + 1) by norm_num]
      apply orderOf_eq_prime_pow
      · rw [pow_one, hy2]; exact hne
      · rw [pow_succ, pow_one, pow_mul, hy2, hx1]
    · rw [← conj_pow, hyx, inv_pow]

/-- `lem:wb-pgroup`: a finite `p`-group with exactly one subgroup of order `p` that is not cyclic
has `p = 2` and contains `a, b` of order `4` with `b a b⁻¹ = a⁻¹`. -/
theorem exists_quaternion_of_not_isCyclic {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hG : IsPGroup p G)
    (huniq : ∀ H K : Subgroup G, Nat.card H = p → Nat.card K = p → H = K)
    (hnc : ¬ IsCyclic G) :
    p = 2 ∧ ∃ a b : G, orderOf a = 4 ∧ orderOf b = 4 ∧ b * a * b⁻¹ = a⁻¹ := by
  have hp := (Fact.out : p.Prime)
  induction hN : Nat.card G using Nat.strong_induction_on generalizing G with
  | _ N ih =>
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hG
  obtain _ | _ | n := m
  · exfalso
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hm
    have : Subsingleton G := hm.1
    exact hnc inferInstance
  · exfalso
    rw [pow_one] at hm
    exact hnc (isCyclic_of_prime_card hm)
  · -- a subgroup `M` of index `p`, which is normal
    obtain ⟨M, hM⟩ := Sylow.exists_subgroup_card_pow_prime p
      (show p ^ (n + 1) ∣ Nat.card G by rw [hm]; exact pow_dvd_pow p (by omega))
    have hindex : M.index = p := by
      have := M.card_mul_index
      rw [hM, hm, pow_succ p (n + 1)] at this
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) this
    have hMn : M.Normal :=
      Subgroup.normal_of_index_eq_minFac_card (by rw [hindex, hm, hp.pow_minFac (by omega)])
    by_cases hMc : IsCyclic M
    · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
      have hog : orderOf (g : G) = p ^ (n + 1) := by
        rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hM]
      have hMx : M = Subgroup.zpowers (g : G) := by
        symm
        apply Subgroup.eq_of_le_of_card_ge
        · exact Subgroup.zpowers_le.mpr g.2
        · rw [Nat.card_zpowers, hog, hM]
      rw [hMx] at hMn
      exact quaternion_core huniq hnc (g : G) (n + 1) (by omega) hog hm hMn
    · have hMuniq : ∀ H K : Subgroup M, Nat.card H = p → Nat.card K = p → H = K := by
        intro H K hH hK
        apply Subgroup.map_injective M.subtype_injective
        apply huniq
        · rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hH
        · rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hK
      have hlt : Nat.card M < N := by
        rw [hM, ← hN, hm]; exact Nat.pow_lt_pow_right hp.one_lt (by omega)
      obtain ⟨h2, a, b, ha, hb, hab⟩ :=
        ih (Nat.card M) hlt (hG.to_subgroup M) hMuniq hMc rfl
      refine ⟨h2, a, b, by rw [Subgroup.orderOf_coe, ha], by rw [Subgroup.orderOf_coe, hb], ?_⟩
      have := congrArg Subtype.val hab
      simpa using this

/-! ### Division rings -/

/-- An abelian normal subgroup of the unit group of a division ring is central
(the `1 + x` argument of `thm:wedderburn`). -/
theorem le_center_of_normal {D : Type*} [DivisionRing D] (A : Subgroup Dˣ) [hA : A.Normal]
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A ≤ Subgroup.center Dˣ := by
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro x
  apply Units.ext
  simp only [Units.val_mul]
  by_cases hx : (1 : D) + x = 0
  · rw [eq_neg_of_add_eq_zero_right hx]
    simp
  · set u : Dˣ := Units.mk0 _ hx with hu
    have hz : u * y * u⁻¹ ∈ A := hA.conj_mem y hy u
    have hw : x * y * x⁻¹ ∈ A := hA.conj_mem y hy x
    have hcz : (y : D) * ((u * y * u⁻¹ : Dˣ) : D) = ((u * y * u⁻¹ : Dˣ) : D) * y := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm _ hy _ hz]
    have hcw : (y : D) * ((x * y * x⁻¹ : Dˣ) : D) = ((x * y * x⁻¹ : Dˣ) : D) * y := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm _ hy _ hw]
    set z : D := ((u * y * u⁻¹ : Dˣ) : D) with hzdef
    set w : D := ((x * y * x⁻¹ : Dˣ) : D) with hwdef
    have hzu : z * (1 + x) = (1 + x) * y := by
      have h0 : u * y * u⁻¹ * u = u * y := by group
      have h1 := congrArg Units.val h0
      rw [Units.val_mul, Units.val_mul] at h1
      rwa [hu, Units.val_mk0] at h1
    have hwx : w * x = x * y := by
      have h0 : x * y * x⁻¹ * x = x * y := by group
      have h1 := congrArg Units.val h0
      rwa [Units.val_mul, Units.val_mul] at h1
    have key : (y : D) - z = (z - w) * x := by
      have h1 : z + z * x = y + x * y := by
        have := hzu
        simp only [mul_add, add_mul, mul_one, one_mul] at this
        exact this
      rw [sub_mul, hwx, sub_eq_sub_iff_add_eq_add, ← h1, add_comm]
    by_cases hzw : z = w
    · rw [hzw, sub_self, zero_mul, sub_eq_zero] at key
      rw [← hwx, ← key]
    · have hx' : (x : D) = (z - w)⁻¹ * (y - z) := by
        rw [key, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hzw), one_mul]
      have hc : Commute (y : D) x := by
        rw [hx']
        exact ((Commute.sub_right hcz hcw).inv_right₀).mul_right
          ((Commute.refl _).sub_right hcz)
      exact hc.eq.symm

open scoped IsMulCommutative in
/-- If `g, h` are commuting units of a division ring, `g` of prime order `p` and `h ^ p = 1`, then `h`
is a power of `g` (count the roots of `X ^ p - 1` in the commutative domain generated by `g, h`). -/
theorem exists_pow_eq_of_commute {D : Type*} [DivisionRing D] {p : ℕ} [hp : Fact p.Prime]
    {g h : Dˣ} (hgh : Commute g h) (hg : orderOf g = p) (hh : h ^ p = 1) :
    ∃ i : ℕ, g ^ i = h := by
  have hc : (g : D) * h = h * g := by rw [← Units.val_mul, hgh.eq, Units.val_mul]
  have hcomm : ∀ a ∈ ({(g : D), (h : D)} : Set D), ∀ b ∈ ({(g : D), (h : D)} : Set D),
      a * b = b * a := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro a (rfl | rfl) b (rfl | rfl) <;> first | rfl | exact hc | exact hc.symm
  have := Subring.isMulCommutative_closure hcomm
  let R := Subring.closure ({(g : D), (h : D)} : Set D)
  have : IsDomain R := inferInstance
  let ζ : R := ⟨g, Subring.subset_closure (by simp)⟩
  let ξ : R := ⟨h, Subring.subset_closure (by simp)⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hζ : IsPrimitiveRoot ζ p := by
    rw [IsPrimitiveRoot.iff_orderOf, ← hg, ← orderOf_units,
      ← orderOf_submonoid (H := R.toSubmonoid)]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ξ)
    (by apply Subtype.ext; simp [ξ, ← Units.val_pow_eq_pow_val, hh])
  refine ⟨i, Units.ext ?_⟩
  have := congrArg Subtype.val hi
  simpa [ζ, ξ] using this

/-- `lem:wb-sylow`: the Sylow subgroups of the unit group of a finite division ring are cyclic. -/
theorem isCyclic_sylow (D : Type*) [DivisionRing D] [Finite D] {p : ℕ} [Fact p.Prime]
    (S : Sylow p Dˣ) : IsCyclic S := by
  by_contra hnc
  have hP : IsPGroup p S := S.isPGroup'
  have huniq : ∀ H K : Subgroup S, Nat.card H = p → Nat.card K = p → H = K := by
    have : Nontrivial S := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hnc inferInstance
    have hZ := hP.center_nontrivial
    obtain ⟨k, hk0, hk⟩ :=
      ((hP.to_subgroup (Subgroup.center S)).nontrivial_iff_card).mp hZ
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) p
      (show p ∣ Nat.card (Subgroup.center S) by rw [hk]; exact dvd_pow_self p hk0.ne')
    have key : ∀ H : Subgroup S, Nat.card H = p → H = Subgroup.zpowers (z : S) := by
      intro H hH
      apply Subgroup.eq_of_le_of_card_ge
      · intro h hh
        have hhp : h ^ p = 1 := by
          have := pow_card_eq_one' (x := (⟨h, hh⟩ : H))
          rw [hH] at this
          exact congrArg Subtype.val this
        have hcomm : Commute ((z : S) : Dˣ) (h : Dˣ) := by
          have := Subgroup.mem_center_iff.mp z.2 h
          exact (congrArg Subtype.val this).symm
        have hoz : orderOf ((z : S) : Dˣ) = p := by
          rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
        obtain ⟨i, hi⟩ := exists_pow_eq_of_commute hcomm hoz
          (by rw [← Subgroup.coe_pow, hhp, Subgroup.coe_one])
        have : (z : S) ^ i = h := Subtype.ext (by simpa using hi)
        rw [← this]
        exact Subgroup.npow_mem_zpowers _ _
      · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, hH]
    intro H K hH hK
    rw [key H hH, key K hK]
  obtain ⟨rfl, a, b, ha, hb, hab⟩ := exists_quaternion_of_not_isCyclic hP huniq hnc
  -- pass to `D`
  set α : D := ((a : Dˣ) : D) with hαdef
  set β : D := ((b : Dˣ) : D) with hβdef
  have sq_ne_one : ∀ c : S, orderOf c = 4 → ((c : Dˣ) : D) ^ 2 ≠ 1 := by
    intro c hc h
    apply pow_ne_one_of_lt_orderOf (n := 2) (by norm_num) (by rw [hc]; norm_num) (x := c)
    apply Subtype.ext; apply Units.ext
    simpa using h
  have sq_neg_one : ∀ c : S, orderOf c = 4 → ((c : Dˣ) : D) ^ 2 = -1 := by
    intro c hc
    have h4 : ((c : Dˣ) : D) ^ 4 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one]; rfl
    have : (((c : Dˣ) : D) ^ 2 - 1) * (((c : Dˣ) : D) ^ 2 + 1) = 0 := by
      have e : (((c : Dˣ) : D) ^ 2 - 1) * (((c : Dˣ) : D) ^ 2 + 1) = ((c : Dˣ) : D) ^ 4 - 1 := by
        noncomm_ring
      rw [e, h4, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) (sq_ne_one c hc)
    · exact eq_neg_of_add_eq_zero_left h
  have hα2 : α ^ 2 = -1 := sq_neg_one a ha
  have hβ2 : β ^ 2 = -1 := sq_neg_one b hb
  have hba : β * α = -(α * β) := by
    have h1 : (b : Dˣ) * a = (a : Dˣ)⁻¹ * b := by
      have := congrArg Subtype.val hab
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this]; group
    have h2 : ((a : Dˣ)⁻¹ : Dˣ) = (a : Dˣ) ^ 3 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', ← Subgroup.coe_pow]
      exact congrArg Subtype.val (show a ^ 4 = 1 from ha ▸ pow_orderOf_eq_one a)
    have h3 := congrArg Units.val h1
    rw [Units.val_mul, Units.val_mul, h2, Units.val_pow_eq_pow_val] at h3
    rw [h3, ← hαdef, pow_succ α 2, hα2]
    noncomm_ring
  have hne1 : (1 : D) ≠ -1 := by
    intro h
    exact sq_ne_one a ha (by rw [← hαdef, hα2]; exact h.symm)
  -- the characteristic
  set q := ringChar D
  have hq : q.Prime := CharP.char_is_prime D q
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨t, r, ht, htr⟩ := exists_sq_add_sq_eq_neg_one q
  set m := t.val
  set n := r.val
  have hm : ¬ q ∣ m := by
    rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]; exact ht
  have hsum : q ∣ m ^ 2 + n ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, htr]; ring
  have hmD : (m : D) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff D q]
  have hsumD : ((m ^ 2 + n ^ 2 + 1 : ℕ) : D) = 0 := (CharP.cast_eq_zero_iff D q _).mpr hsum
  have iden : (m • (1:D) + n • α + β) * ((n ^ 2 + 1) • (1 : D) + (n * m) • α + m • β) =
      (n * (m ^ 2 + n ^ 2 + 1)) • α + (m ^ 2 + n ^ 2 + 1) • β
      + (n^2 * m) • (α ^ 2 + 1) + m • (β ^ 2 + 1) + (n * m) • (α * β + β * α) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, pow_two,
      smul_add]
    module
  have hzero : (m • (1:D) + n • α + β) * ((n ^ 2 + 1) • (1 : D) + (n * m) • α + m • β) = 0 := by
    rw [iden, hα2, hβ2, hba, neg_add_cancel, add_neg_cancel, smul_zero, smul_zero, smul_zero,
      nsmul_eq_mul, nsmul_eq_mul, hsumD, Nat.cast_mul, hsumD]
    simp
  have hcomm : α * β = β * α := by
    rcases mul_eq_zero.mp hzero with h | h
    · have hb' : β = -(m • (1:D) + n • α) := eq_neg_of_add_eq_zero_right (by rw [← h])
      rw [hb']
      exact ((((Commute.one_right α).smul_right m).add_right
        ((Commute.refl α).smul_right n)).neg_right).eq
    · have hb' : m • β = -((n ^ 2 + 1) • (1 : D) + (n * m) • α) :=
        eq_neg_of_add_eq_zero_right (by rw [← h])
      have hc : α * (m • β) = (m • β) * α := by
        rw [hb']
        exact ((((Commute.one_right α).smul_right _).add_right
          ((Commute.refl α).smul_right _)).neg_right).eq
      rw [mul_smul_comm, smul_mul_assoc, nsmul_eq_mul, nsmul_eq_mul] at hc
      exact mul_left_cancel₀ hmD hc
  have h2 : (2 : D) * (α * β) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hcomm]
    rw [hba, add_neg_cancel]
  rcases mul_eq_zero.mp h2 with h | h
  · exact hne1 (by rw [eq_neg_iff_add_eq_zero, one_add_one_eq_two, h])
  · exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _) h

/-- `thm:wedderburn` (Wedderburn 1905, by Kaczynski's proof): every finite division ring is
commutative. -/
theorem mul_comm (D : Type*) [DivisionRing D] [Finite D] (a b : D) : a * b = b * a := by
  have : IsZGroup Dˣ := ⟨fun p hp P => by have := Fact.mk hp; exact isCyclic_sylow D P⟩
  have hcyc := IsZGroup.isCyclic_commutator Dˣ
  have hle : commutator Dˣ ≤ Subgroup.center Dˣ := by
    apply le_center_of_normal
    intro x hx y hy
    have := (IsCyclic.commGroup (α := commutator Dˣ)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have : Group.IsNilpotent Dˣ := by
    refine ⟨2, eq_top_iff.mpr fun x _ => ?_⟩
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    exact hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hcD : IsCyclic Dˣ := inferInstance
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have := (IsCyclic.commGroup (α := Dˣ)).mul_comm (Units.mk0 a ha) (Units.mk0 b hb)
  exact congrArg Units.val this

end TJK.Wedderburn
