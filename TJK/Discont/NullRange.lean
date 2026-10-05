import Mathlib
import TJK.Defs

/-!
# A strictly increasing function with null range (blueprint `lem:th-lemma25`)

We use the function `g t = ∑ᵢ ⌊2ⁱ t⌋ / 3ⁱ`. It is strictly increasing (every term is monotone and
`⌊2ⁱ t⌋ < ⌊2ⁱ t'⌋` once `2ⁱ (t' - t) ≥ 1`), satisfies `3t - 3/2 ≤ g t ≤ 3t`, and on each dyadic
interval `[k/2ᴺ, (k+1)/2ᴺ)` it varies by at most `3/3ᴺ`; hence `g` maps `[m, m+1)` into a union of
`2ᴺ` intervals of length `3/3ᴺ`, so its range is null. Then `h x = (ε/3) g (x/ε)`.
-/

open MeasureTheory Set Filter Topology Pointwise

namespace TJK.Discont

/-- The `n`-th term of the series defining `cantorLike`. -/
noncomputable def cantorTerm (t : ℝ) (i : ℕ) : ℝ := (⌊(2 : ℝ) ^ i * t⌋ : ℝ) / 3 ^ i

/-- `cantorLike t = ∑ᵢ ⌊2ⁱ t⌋ / 3ⁱ`; for `t ∈ [0,1)` this is `3/2` times the point of the Cantor set
whose ternary digits are twice the binary digits of `t`. -/
noncomputable def cantorLike (t : ℝ) : ℝ := ∑' i, cantorTerm t i

lemma abs_floor_le (x : ℝ) : |(⌊x⌋ : ℝ)| ≤ |x| + 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  rw [abs_le]
  constructor <;> cases abs_cases x <;> linarith

lemma summable_cantorTerm (t : ℝ) : Summable (cantorTerm t) := by
  refine Summable.of_norm_bounded (g := fun i : ℕ => (|t| + 1) * (2 / 3 : ℝ) ^ i)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _) (fun i => ?_)
  rw [Real.norm_eq_abs, cantorTerm, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ i),
    div_le_iff₀ (by positivity), div_pow, mul_assoc, div_mul_cancel₀ _ (by positivity)]
  have h := abs_floor_le ((2 : ℝ) ^ i * t)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ i)] at h
  have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  nlinarith

lemma cantorTerm_mono (i : ℕ) : Monotone (fun t => cantorTerm t i) := by
  intro t t' h
  simp only [cantorTerm]
  gcongr

lemma cantorLike_strictMono : StrictMono cantorLike := by
  intro t t' htt
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (1 / (t' - t)) (by norm_num : (1 : ℝ) < 2)
  have hpos : 0 < t' - t := sub_pos.2 htt
  have hi' : 1 ≤ 2 ^ i * t' - 2 ^ i * t := by
    rw [div_lt_iff₀ hpos] at hi; nlinarith
  refine Summable.tsum_lt_tsum (i := i) (fun j => cantorTerm_mono j htt.le) ?_
    (summable_cantorTerm t) (summable_cantorTerm t')
  simp only [cantorTerm]
  gcongr
  have : ⌊(2 : ℝ) ^ i * t⌋ + 1 ≤ ⌊(2 : ℝ) ^ i * t'⌋ := by
    rw [← Int.floor_add_one]; exact Int.floor_mono (by linarith)
  exact_mod_cast this

lemma hasSum_geom_mul (t : ℝ) : HasSum (fun i : ℕ => (2 : ℝ) ^ i * t / 3 ^ i) (3 * t) := by
  have := (hasSum_geometric_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_right t
  have hf : (fun i : ℕ => (2 : ℝ) ^ i * t / 3 ^ i) = fun i => (2 / 3 : ℝ) ^ i * t := by
    ext i; rw [div_pow]; ring
  rw [hf, show 3 * t = (1 - 2 / 3 : ℝ)⁻¹ * t by norm_num]
  exact this

lemma cantorLike_le (t : ℝ) : cantorLike t ≤ 3 * t :=
  hasSum_le (fun i => by
      simp only [cantorTerm]
      gcongr
      exact Int.floor_le _)
    (summable_cantorTerm t).hasSum (hasSum_geom_mul t)

lemma le_cantorLike (t : ℝ) : 3 * t - 3 / 2 ≤ cantorLike t := by
  have h3 : HasSum (fun i : ℕ => (1 / 3 : ℝ) ^ i) (3 / 2) := by
    convert hasSum_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  refine hasSum_le (fun i => ?_) ((hasSum_geom_mul t).sub h3) (summable_cantorTerm t).hasSum
  simp only [cantorTerm, one_div, inv_pow]
  rw [← one_div, div_sub_div_same]
  gcongr
  linarith [Int.lt_floor_add_one ((2 : ℝ) ^ i * t)]

/-- On the dyadic interval `[⌊2ᴺ t⌋/2ᴺ, ⌊2ᴺ t⌋/2ᴺ + 1/2ᴺ)` the function varies by at most `3/3ᴺ`. -/
lemma cantorLike_le_dyadic (t : ℝ) (N : ℕ) :
    cantorLike t ≤ cantorLike ((⌊(2 : ℝ) ^ N * t⌋ : ℝ) / 2 ^ N) + 3 / 3 ^ N := by
  set k := ⌊(2 : ℝ) ^ N * t⌋ with hk
  set a : ℝ := (k : ℝ) / 2 ^ N with ha
  -- the first `N` terms agree
  have hA : ∀ i < N, cantorTerm t i = cantorTerm a i := by
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi.le
    simp only [cantorTerm]
    congr 2
    have e1 : (2 : ℝ) ^ i * t = (2 : ℝ) ^ (i + j) * t / ((2 ^ j : ℕ) : ℝ) := by
      push_cast; rw [pow_add]; field_simp
    have e2 : (2 : ℝ) ^ i * a = (k : ℝ) / ((2 ^ j : ℕ) : ℝ) := by
      rw [ha]; push_cast; rw [pow_add]; field_simp
    rw [e1, e2, Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_intCast]
  -- the tail terms differ by at most `2ʲ / 3^(j+N)`
  have hB : ∀ j : ℕ, cantorTerm t (j + N) ≤ cantorTerm a (j + N) + (2 / 3 : ℝ) ^ j * (1 / 3 ^ N) := by
    intro j
    have e : (2 : ℝ) ^ (j + N) * a = ((k * 2 ^ j : ℤ) : ℝ) := by
      rw [ha]; push_cast; rw [pow_add]; field_simp
    simp only [cantorTerm]
    have e' : (2 / 3 : ℝ) ^ j * (1 / 3 ^ N) = 2 ^ j / 3 ^ (j + N) := by
      rw [pow_add, div_pow]; field_simp
    rw [e, Int.floor_intCast, e', ← add_div]
    gcongr
    push_cast
    have h1 := Int.floor_le ((2 : ℝ) ^ (j + N) * t)
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ N * t)
    rw [← hk] at h2
    have h3 : (2 : ℝ) ^ (j + N) * t = 2 ^ j * (2 ^ N * t) := by rw [pow_add]; ring
    have h4 := mul_lt_mul_of_pos_left h2 (by positivity : (0 : ℝ) < 2 ^ j)
    linarith
  have st := summable_cantorTerm t
  have sa := summable_cantorTerm a
  rw [cantorLike, cantorLike, ← st.sum_add_tsum_nat_add N, ← sa.sum_add_tsum_nat_add N,
    Finset.sum_congr rfl (fun i hi => hA i (Finset.mem_range.1 hi)), add_assoc]
  gcongr
  have hg : HasSum (fun j : ℕ => (2 / 3 : ℝ) ^ j * (1 / 3 ^ N)) (3 / 3 ^ N) := by
    have := (hasSum_geometric_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_right
      (1 / 3 ^ N)
    rwa [show (1 - 2 / 3 : ℝ)⁻¹ * (1 / 3 ^ N) = 3 / 3 ^ N by norm_num; ring] at this
  exact hasSum_le hB ((summable_nat_add_iff N).2 st).hasSum
    (((summable_nat_add_iff N).2 sa).hasSum.add hg)

lemma volume_cantorLike_image_Ico (m : ℤ) : volume (cantorLike '' Ico (m : ℝ) (m + 1)) = 0 := by
  have bound : ∀ N : ℕ, volume (cantorLike '' Ico (m : ℝ) (m + 1)) ≤
      ENNReal.ofReal (3 * (2 / 3 : ℝ) ^ N) := by
    intro N
    have sub : cantorLike '' Ico (m : ℝ) (m + 1) ⊆
        ⋃ k ∈ Finset.Ico (m * 2 ^ N) ((m + 1) * 2 ^ N),
          Icc (cantorLike ((k : ℝ) / 2 ^ N)) (cantorLike ((k : ℝ) / 2 ^ N) + 3 / 3 ^ N) := by
      rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
      simp only [mem_iUnion, Finset.mem_Ico, mem_Icc, exists_prop]
      refine ⟨⌊(2 : ℝ) ^ N * t⌋, ⟨?_, ?_⟩, ?_, cantorLike_le_dyadic t N⟩
      · rw [Int.le_floor]; push_cast
        have : (0 : ℝ) < 2 ^ N := by positivity
        nlinarith
      · rw [Int.floor_lt]; push_cast
        have : (0 : ℝ) < 2 ^ N := by positivity
        nlinarith
      · apply cantorLike_strictMono.monotone
        rw [div_le_iff₀ (by positivity), mul_comm]
        exact Int.floor_le _
    refine (measure_mono sub).trans ((measure_biUnion_finset_le _ _).trans (le_of_eq ?_))
    simp only [Real.volume_Icc, add_sub_cancel_left, Finset.sum_const, Int.card_Ico, nsmul_eq_mul]
    have : ((m + 1) * 2 ^ N - m * 2 ^ N : ℤ).toNat = 2 ^ N := by
      have : ((m + 1) * 2 ^ N - m * 2 ^ N : ℤ) = ((2 ^ N : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [this, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), div_pow]
    congr 1
    push_cast
    field_simp
  have tend : Tendsto (fun N : ℕ => ENNReal.ofReal (3 * (2 / 3 : ℝ) ^ N)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num)
      (by norm_num)).const_mul 3
  exact le_antisymm (ge_of_tendsto' tend bound) bot_le

lemma volume_range_cantorLike : volume (range cantorLike) = 0 := by
  refine measure_mono_null ?_ (measure_iUnion_null fun m : ℤ => volume_cantorLike_image_Ico m)
  rintro _ ⟨t, rfl⟩
  exact mem_iUnion.2 ⟨⌊t⌋, t, ⟨Int.floor_le t, Int.lt_floor_add_one t⟩, rfl⟩

/-- Blueprint `lem:th-lemma25` (Kaczynski, dissertation, Lemma 25): for every `ε > 0` there is a
strictly increasing `h : ℝ → ℝ` whose range has measure zero and with `|x - h x| ≤ ε`. -/
theorem exists_strictMono_null_range {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, StrictMono h ∧ MeasureTheory.volume (Set.range h) = 0 ∧ ∀ x, |x - h x| ≤ ε := by
  refine ⟨fun x => ε / 3 * cantorLike (x / ε), ?_, ?_, ?_⟩
  · intro x y hxy
    have := cantorLike_strictMono (div_lt_div_of_pos_right hxy hε)
    simp only
    gcongr
  · refine measure_mono_null (?_ : _ ⊆ (ε / 3) • range cantorLike) ?_
    · rintro _ ⟨x, rfl⟩
      exact Set.smul_mem_smul_set ⟨x / ε, rfl⟩
    · rw [Measure.addHaar_smul, volume_range_cantorLike, mul_zero]
  · intro x
    have h1 := cantorLike_le (x / ε)
    have h2 := le_cantorLike (x / ε)
    have e : x = ε / 3 * (3 * (x / ε)) := by field_simp
    have hε3 : 0 < ε / 3 := by positivity
    have u1 := mul_le_mul_of_nonneg_left h1 hε3.le
    have u2 := mul_le_mul_of_nonneg_left h2 hε3.le
    rw [abs_le]
    constructor <;> nlinarith

end TJK.Discont
