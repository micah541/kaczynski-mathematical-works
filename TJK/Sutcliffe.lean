/-
Sutcliffe's problem: Kaczynski, *Note on a problem of Alan Sutcliffe*, Math. Mag. 41 (1968).
Blueprint: `paper/sections/A-sutcliffe.tex`.
-/
import Mathlib

namespace TJK.Sutcliffe

/-- `IsSolution n k L`: the digits `L = [a₀, a₁, …, a_h]` (least significant first) form an
`(h+1)`-digit solution for the base `n` with multiplier `k`, i.e.
`n ≥ 2`, `k > 1`, `a_h > 0`, `a₀ > 0`, all `aᵢ ≤ n - 1`, and
`k · (a_h … a₁ a₀)ₙ = (a₀ a₁ … a_h)ₙ`. (Blueprint `def:sut-solution`.) -/
def IsSolution (n k : ℕ) (L : List ℕ) : Prop :=
  2 ≤ n ∧ 1 < k ∧ L ≠ [] ∧ 0 < L.headI ∧ 0 < L.getLastI ∧ (∀ a ∈ L, a ≤ n - 1) ∧
    k * Nat.ofDigits n L = Nat.ofDigits n L.reverse

/-- There is a `d`-digit solution for `n`. -/
def HasSolution (n d : ℕ) : Prop :=
  ∃ k L, L.length = d ∧ IsSolution n k L

/-- 2-digit solutions in coordinates: `k (a n + c) = c n + a`. -/
theorem hasSolution_two_iff (n : ℕ) :
    HasSolution n 2 ↔ 2 ≤ n ∧ ∃ a c k, 1 < k ∧ 1 ≤ a ∧ a + 1 ≤ n ∧ 1 ≤ c ∧ c + 1 ≤ n ∧
      k * (a * n + c) = c * n + a := by
  constructor
  · rintro ⟨k, L, hL, hn, hk, -, h0, hl, hd, heq⟩
    obtain ⟨c, a, rfl⟩ := List.length_eq_two.mp hL
    simp only [List.headI_cons, List.getLastI_eq_getLast?_getD, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.getD_some] at h0 hl
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hd
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      Nat.ofDigits_cons, Nat.ofDigits_nil] at heq
    refine ⟨hn, a, c, k, hk, hl, by omega, h0, by omega, ?_⟩
    linarith
  · rintro ⟨hn, a, c, k, hk, ha, ha', hc, hc', heq⟩
    refine ⟨k, [c, a], rfl, hn, hk, by simp, ?_, ?_, ?_, ?_⟩
    · simp; omega
    · simp [List.getLastI_eq_getLast?_getD]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      omega
    · simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        Nat.ofDigits_cons, Nat.ofDigits_nil]
      linarith

/-- 3-digit solutions in coordinates: `k (a n² + b n + c) = c n² + b n + a`. -/
theorem hasSolution_three_iff (n : ℕ) :
    HasSolution n 3 ↔ 2 ≤ n ∧ ∃ a b c k, 1 < k ∧ 1 ≤ a ∧ a + 1 ≤ n ∧ b + 1 ≤ n ∧ 1 ≤ c ∧
      c + 1 ≤ n ∧ k * (a * n ^ 2 + b * n + c) = c * n ^ 2 + b * n + a := by
  constructor
  · rintro ⟨k, L, hL, hn, hk, -, h0, hl, hd, heq⟩
    obtain ⟨c, b, a, rfl⟩ := List.length_eq_three.mp hL
    simp only [List.headI_cons, List.getLastI_eq_getLast?_getD, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.getD_some] at h0 hl
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hd
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      Nat.ofDigits_cons, Nat.ofDigits_nil] at heq
    refine ⟨hn, a, b, c, k, hk, hl, by omega, by omega, h0, by omega, ?_⟩
    nlinarith [heq]
  · rintro ⟨hn, a, b, c, k, hk, ha, ha', hb', hc, hc', heq⟩
    refine ⟨k, [c, b, a], rfl, hn, hk, by simp, ?_, ?_, ?_, ?_⟩
    · simp; omega
    · simp [List.getLastI_eq_getLast?_getD]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      omega
    · simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        Nat.ofDigits_cons, Nat.ofDigits_nil]
      nlinarith [heq]

/-- Blueprint `lem:sut-basic`, 2-digit case. -/
theorem two_digit_basic {n a c k : ℕ} (hn : 2 ≤ n) (hk : 1 < k) (ha : 1 ≤ a) (ha' : a + 1 ≤ n)
    (hc : 1 ≤ c) (hc' : c + 1 ≤ n) (h : k * (a * n + c) = c * n + a) : k < n ∧ a < c := by
  constructor
  · by_contra hkn
    push Not at hkn
    have h0 : n ≤ a * n + c := by nlinarith
    have h1 : n * n ≤ k * (a * n + c) :=
      (Nat.mul_le_mul_right n hkn).trans (Nat.mul_le_mul_left k h0)
    have h2 : (c + 1) * n ≤ n * n := Nat.mul_le_mul_right n hc'
    nlinarith
  · by_contra hac
    push Not at hac
    have h1 : c * n ≤ a * n := Nat.mul_le_mul_right n hac
    have h2 : 2 * (a * n + c) ≤ k * (a * n + c) := Nat.mul_le_mul_right _ hk
    have h3 : a ≤ a * n := Nat.le_mul_of_pos_right a (by omega)
    nlinarith

/-- Blueprint `lem:sut-basic`, 3-digit case. -/
theorem three_digit_basic {n a b c k : ℕ} (hn : 2 ≤ n) (hk : 1 < k) (ha : 1 ≤ a)
    (ha' : a + 1 ≤ n) (hb' : b + 1 ≤ n) (hc : 1 ≤ c) (hc' : c + 1 ≤ n)
    (h : k * (a * n ^ 2 + b * n + c) = c * n ^ 2 + b * n + a) : k < n ∧ a < c := by
  constructor
  · by_contra hkn
    push Not at hkn
    have h0 : n ^ 2 ≤ a * n ^ 2 + b * n + c := by nlinarith
    have h1 : n * n ^ 2 ≤ k * (a * n ^ 2 + b * n + c) :=
      (Nat.mul_le_mul_right _ hkn).trans (Nat.mul_le_mul_left k h0)
    have h2 : (c + 1) * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hc'
    have h3 : (b + 1) * n ≤ n * n := Nat.mul_le_mul_right n hb'
    nlinarith
  · by_contra hac
    push Not at hac
    have h1 : c * n ^ 2 ≤ a * n ^ 2 := Nat.mul_le_mul_right _ hac
    have h2 : 2 * (a * n ^ 2 + b * n + c) ≤ k * (a * n ^ 2 + b * n + c) :=
      Nat.mul_le_mul_right _ hk
    have h3 : a ≤ a * n ^ 2 := Nat.le_mul_of_pos_right a (by positivity)
    nlinarith

/-- Blueprint `prop:sut-two-composite` (Sutcliffe, Theorem 2, first half). -/
theorem not_prime_of_two_digit {n : ℕ} (h : HasSolution n 2) : ¬ (n + 1).Prime := by
  obtain ⟨hn, a, c, k, hk, ha, ha', hc, hc', heq⟩ := (hasSolution_two_iff n).1 h
  obtain ⟨hkn, hac⟩ := two_digit_basic hn hk ha ha' hc hc' heq
  intro hp
  have hz : (k : ℤ) * (a * n + c) = c * n + a := by exact_mod_cast heq
  have hdvd : ((n : ℤ) + 1) ∣ ((k : ℤ) + 1) * (c - a) :=
    ⟨c - k * a, by linear_combination hz⟩
  have hp' : Prime ((n : ℤ) + 1) := by exact_mod_cast Nat.prime_iff_prime_int.mp hp
  rcases hp'.dvd_or_dvd hdvd with h1 | h1
  · have := Int.le_of_dvd (by positivity) h1
    omega
  · have := Int.le_of_dvd (by omega) h1
    omega

/-- Blueprint `prop:sut-explicit`, 2-digit part. -/
theorem explicit_two_digit {n d e : ℕ} (hd : 3 ≤ d) (he : 2 ≤ e) (hn : n + 1 = d * e) :
    HasSolution n 2 := by
  have hen : 3 * e ≤ n + 1 := by rw [hn]; exact Nat.mul_le_mul_right e hd
  rw [hasSolution_two_iff]
  refine ⟨by omega, e - 1, n - e, d - 1, by omega, by omega, by omega, by omega, by omega, ?_⟩
  have hz : (n : ℤ) = d * e - 1 := by
    have : ((n + 1 : ℕ) : ℤ) = ((d * e : ℕ) : ℤ) := by rw [hn]
    push_cast at this; linarith
  zify [show 1 ≤ e by omega, show e ≤ n by omega, show 1 ≤ d by omega]
  rw [hz]; ring

/-- Blueprint `prop:sut-explicit`, 3-digit part. -/
theorem explicit_three_digit {n d e : ℕ} (hd : 3 ≤ d) (he : 2 ≤ e) (hn : n + 1 = d * e) :
    HasSolution n 3 := by
  have hen : 3 * e ≤ n + 1 := by rw [hn]; exact Nat.mul_le_mul_right e hd
  rw [hasSolution_three_iff]
  refine ⟨by omega, e - 1, n - 1, n - e, d - 1, by omega, by omega, by omega, by omega, by omega,
    by omega, ?_⟩
  have hz : (n : ℤ) = d * e - 1 := by
    have : ((n + 1 : ℕ) : ℤ) = ((d * e : ℕ) : ℤ) := by rw [hn]
    push_cast at this; linarith
  zify [show 1 ≤ e by omega, show e ≤ n by omega, show 1 ≤ d by omega, show 1 ≤ n by omega]
  rw [hz]; ring

/-- Blueprint `lem:sut-factor`. -/
theorem exists_factor {n : ℕ} (hn : 4 ≤ n) (hp : ¬ (n + 1).Prime) :
    ∃ d e, 3 ≤ d ∧ 2 ≤ e ∧ n + 1 = d * e := by
  have hm1 : n + 1 ≠ 1 := by omega
  have hmin := Nat.minFac_prime hm1
  have hle : (n + 1).minFac ^ 2 ≤ n + 1 := Nat.minFac_sq_le_self (by omega) hp
  have hdm : (n + 1) / (n + 1).minFac * (n + 1).minFac = n + 1 :=
    Nat.div_mul_cancel (Nat.minFac_dvd _)
  generalize (n + 1).minFac = e at hmin hle hdm
  generalize (n + 1) / e = d at hdm
  have he2 := hmin.two_le
  refine ⟨d, e, ?_, he2, hdm.symm⟩
  by_contra hd
  push Not at hd
  have hed : e ≤ d := by nlinarith
  nlinarith

/-- Sutcliffe, Theorem 2 (blueprint `thm:sut-sutcliffe2`). -/
theorem two_digit_iff {n : ℕ} (hn : 4 ≤ n) : HasSolution n 2 ↔ ¬ (n + 1).Prime := by
  refine ⟨not_prime_of_two_digit, fun hp => ?_⟩
  obtain ⟨d, e, hd, he, hde⟩ := exists_factor hn hp
  exact explicit_two_digit hd he hde

/-- Sutcliffe, Theorem 3 (blueprint `thm:sut-sutcliffe3`). -/
theorem three_digit_of_two_digit {n : ℕ} (h : HasSolution n 2) : HasSolution n 3 := by
  obtain ⟨hn, a, c, k, hk, ha, ha', hc, hc', heq⟩ := (hasSolution_two_iff n).1 h
  obtain ⟨hkn, hac⟩ := two_digit_basic hn hk ha ha' hc hc' heq
  have hn4 : 4 ≤ n := by
    by_contra h4
    have hn3 : n = 3 := by omega
    subst hn3
    have hk2 : k = 2 := by omega
    subst hk2
    omega
  obtain ⟨d, e, hd, he, hde⟩ := exists_factor hn4 (not_prime_of_two_digit h)
  exact explicit_three_digit hd he hde

/-- Kaczynski, Lemma 1 (blueprint `lem:sut-lemma1`). -/
theorem kaczynski_lemma1 {a c n : ℕ} (hn : 2 ≤ n) (hac : a < c) (hc : c ≤ n - 1)
    (hsum : n + 1 ≤ a + c) : ¬ (n * (a - 1) + c ∣ n * (c - 1) + a) := by
  rintro ⟨k, hk⟩
  have ha : 2 ≤ a := by omega
  have hE : ((n : ℤ) * (a - 1) + c) * k = n * (c - 1) + a := by
    have := congrArg (fun t : ℕ => (t : ℤ)) hk
    push_cast [show 1 ≤ a by omega, show 1 ≤ c by omega] at this
    linarith
  -- k ≥ 2
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · simp at hk; omega
      · have h01 : ((n : ℤ) - 1) * (c - a) = 0 := by push_cast at hE; linear_combination -1 * hE
        rcases mul_eq_zero.mp h01 with h | h <;> omega
    · exact h
  have hq : ((k : ℤ) - 1) * (a + c - n) = ((n : ℤ) - 1) * (c - k * a) := by
    linear_combination hE
  have hpos : 0 < ((k : ℤ) - 1) * (a + c - n) := by
    apply mul_pos <;> omega
  have hq1 : 1 ≤ (c : ℤ) - k * a := by
    by_contra hneg
    push Not at hneg
    have : ((n : ℤ) - 1) * (c - k * a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    linarith
  have h1 : (n : ℤ) - 1 ≤ ((k : ℤ) - 1) * (a + c - n) := by nlinarith
  have h2 : ((k : ℤ) - 1) * (a + c - n) ≤ ((k : ℤ) - 1) * (a - 1) := by
    apply mul_le_mul_of_nonneg_left _ (by omega); omega
  nlinarith

/-- Kaczynski, Lemma 2 (blueprint `lem:sut-lemma2`). -/
theorem kaczynski_lemma2 {n : ℕ} (hn : n = 2 ∨ n = 3) : ¬ HasSolution n 3 := by
  intro h
  obtain ⟨hn2, a, b, c, k, hk, ha, ha', hb', hc, hc', heq⟩ := (hasSolution_three_iff n).1 h
  obtain ⟨hkn, hac⟩ := three_digit_basic hn2 hk ha ha' hb' hc hc' heq
  rcases hn with rfl | rfl
  · omega
  · have hk2 : k = 2 := by omega
    subst hk2
    omega

/-- **Kaczynski's theorem** (Sutcliffe's conjecture; blueprint `thm:sut-main`): if there is a
3-digit solution for `n ≥ 2`, there is a 2-digit solution. -/
theorem two_digit_of_three_digit {n : ℕ} (hn : 2 ≤ n) (h : HasSolution n 3) :
    HasSolution n 2 := by
  by_cases hn3 : n ≤ 3
  · exact absurd h (kaczynski_lemma2 (by omega))
  push Not at hn3
  by_cases hp : (n + 1).Prime
  swap
  · exact (two_digit_iff (by omega)).2 hp
  obtain ⟨-, a, b, c, k, hk, ha, ha', hb', hc, hc', heq⟩ := (hasSolution_three_iff n).1 h
  obtain ⟨hkn, hac⟩ := three_digit_basic hn hk ha ha' hb' hc hc' heq
  have hz : (k : ℤ) * (a * n ^ 2 + b * n + c) = c * n ^ 2 + b * n + a := by exact_mod_cast heq
  have hdvd : ((n : ℤ) + 1) ∣ ((k : ℤ) - 1) * (a - b + c) :=
    ⟨c * (n - 1) + b - k * (a * (n - 1) + b), by linear_combination hz⟩
  have hp' : Prime ((n : ℤ) + 1) := by exact_mod_cast Nat.prime_iff_prime_int.mp hp
  rcases hp'.dvd_or_dvd hdvd with h1 | h1
  · have := Int.le_of_dvd (by omega) h1
    omega
  obtain ⟨m, hm⟩ := h1
  have hm0 : 0 ≤ m := by
    by_contra hneg
    push Not at hneg
    have : ((n : ℤ) + 1) * m ≤ -((n : ℤ) + 1) := by nlinarith
    omega
  have hm1 : m ≤ 1 := by
    by_contra hbig
    push Not at hbig
    have : 2 * ((n : ℤ) + 1) ≤ ((n : ℤ) + 1) * m := by nlinarith
    omega
  have hnp : (0 : ℤ) < n + 1 := by positivity
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · -- b = a + c: a 2-digit solution with the same a, c, k
    rw [hasSolution_two_iff]
    refine ⟨hn, a, c, k, hk, ha, ha', hc, hc', ?_⟩
    have hb : (b : ℤ) = a + c := by linarith
    have : ((n : ℤ) + 1) * (k * (a * n + c) - (c * n + a)) = 0 := by
      rw [hb] at hz; linear_combination hz
    have h0 : (k : ℤ) * (a * n + c) - (c * n + a) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · omega
      · exact h
    exact_mod_cast (by linarith : (k : ℤ) * (a * n + c) = c * n + a)
  · -- b = a + c - (n + 1): impossible by Lemma 1
    exfalso
    have hb : (b : ℤ) = a + c - (n + 1) := by linarith
    have : ((n : ℤ) + 1) * (k * (n * (a - 1) + c) - (n * (c - 1) + a)) = 0 := by
      rw [hb] at hz; linear_combination hz
    have h0 : (k : ℤ) * (n * (a - 1) + c) - (n * (c - 1) + a) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · omega
      · exact h
    apply kaczynski_lemma1 (a := a) (c := c) (n := n) hn hac (by omega) (by omega)
    refine ⟨k, ?_⟩
    zify [show 1 ≤ a by omega, show 1 ≤ c by omega]
    linarith

/-- Kaczynski's corollary (blueprint `cor:sut-main`): for `n > 3` there is a 3-digit solution iff
`n + 1` is not prime. -/
theorem three_digit_iff {n : ℕ} (hn : 3 < n) : HasSolution n 3 ↔ ¬ (n + 1).Prime := by
  constructor
  · intro h
    exact (two_digit_iff (by omega)).1 (two_digit_of_three_digit (by omega) h)
  · intro hp
    exact three_digit_of_two_digit ((two_digit_iff (by omega)).2 hp)

end TJK.Sutcliffe
