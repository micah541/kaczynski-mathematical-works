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
  sorry

/-- 3-digit solutions in coordinates: `k (a n² + b n + c) = c n² + b n + a`. -/
theorem hasSolution_three_iff (n : ℕ) :
    HasSolution n 3 ↔ 2 ≤ n ∧ ∃ a b c k, 1 < k ∧ 1 ≤ a ∧ a + 1 ≤ n ∧ b + 1 ≤ n ∧ 1 ≤ c ∧
      c + 1 ≤ n ∧ k * (a * n ^ 2 + b * n + c) = c * n ^ 2 + b * n + a := by
  sorry

/-- Blueprint `lem:sut-basic`, 2-digit case. -/
theorem two_digit_basic {n a c k : ℕ} (hn : 2 ≤ n) (hk : 1 < k) (ha : 1 ≤ a) (ha' : a + 1 ≤ n)
    (hc : 1 ≤ c) (hc' : c + 1 ≤ n) (h : k * (a * n + c) = c * n + a) : k < n ∧ a < c := by
  sorry

/-- Blueprint `lem:sut-basic`, 3-digit case. -/
theorem three_digit_basic {n a b c k : ℕ} (hn : 2 ≤ n) (hk : 1 < k) (ha : 1 ≤ a)
    (ha' : a + 1 ≤ n) (hb' : b + 1 ≤ n) (hc : 1 ≤ c) (hc' : c + 1 ≤ n)
    (h : k * (a * n ^ 2 + b * n + c) = c * n ^ 2 + b * n + a) : k < n ∧ a < c := by
  sorry

/-- Blueprint `prop:sut-two-composite` (Sutcliffe, Theorem 2, first half). -/
theorem not_prime_of_two_digit {n : ℕ} (h : HasSolution n 2) : ¬ (n + 1).Prime := by
  sorry

/-- Blueprint `prop:sut-explicit`, 2-digit part. -/
theorem explicit_two_digit {n d e : ℕ} (hd : 3 ≤ d) (he : 2 ≤ e) (hn : n + 1 = d * e) :
    HasSolution n 2 := by
  sorry

/-- Blueprint `prop:sut-explicit`, 3-digit part. -/
theorem explicit_three_digit {n d e : ℕ} (hd : 3 ≤ d) (he : 2 ≤ e) (hn : n + 1 = d * e) :
    HasSolution n 3 := by
  sorry

/-- Blueprint `lem:sut-factor`. -/
theorem exists_factor {n : ℕ} (hn : 4 ≤ n) (hp : ¬ (n + 1).Prime) :
    ∃ d e, 3 ≤ d ∧ 2 ≤ e ∧ n + 1 = d * e := by
  sorry

/-- Sutcliffe, Theorem 2 (blueprint `thm:sut-sutcliffe2`). -/
theorem two_digit_iff {n : ℕ} (hn : 4 ≤ n) : HasSolution n 2 ↔ ¬ (n + 1).Prime := by
  sorry

/-- Sutcliffe, Theorem 3 (blueprint `thm:sut-sutcliffe3`). -/
theorem three_digit_of_two_digit {n : ℕ} (h : HasSolution n 2) : HasSolution n 3 := by
  sorry

/-- Kaczynski, Lemma 1 (blueprint `lem:sut-lemma1`). -/
theorem kaczynski_lemma1 {a c n : ℕ} (hn : 2 ≤ n) (hac : a < c) (hc : c ≤ n - 1)
    (hsum : n + 1 ≤ a + c) : ¬ (n * (a - 1) + c ∣ n * (c - 1) + a) := by
  sorry

/-- Kaczynski, Lemma 2 (blueprint `lem:sut-lemma2`). -/
theorem kaczynski_lemma2 {n : ℕ} (hn : n = 2 ∨ n = 3) : ¬ HasSolution n 3 := by
  sorry

/-- **Kaczynski's theorem** (Sutcliffe's conjecture; blueprint `thm:sut-main`): if there is a
3-digit solution for `n ≥ 2`, there is a 2-digit solution. -/
theorem two_digit_of_three_digit {n : ℕ} (hn : 2 ≤ n) (h : HasSolution n 3) :
    HasSolution n 2 := by
  sorry

/-- Kaczynski's corollary (blueprint `cor:sut-main`): for `n > 3` there is a 3-digit solution iff
`n + 1` is not prime. -/
theorem three_digit_iff {n : ℕ} (hn : 3 < n) : HasSolution n 3 ↔ ¬ (n + 1).Prime := by
  sorry

end TJK.Sutcliffe
