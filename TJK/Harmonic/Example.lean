import Mathlib
import TJK.Defs
import TJK.Plane.Basic
import TJK.Baire.Sphere
import TJK.Harmonic.Poisson

/-!
# A bounded harmonic function with a boundary function not of Baire class one (blueprint §H)

Source: Kaczynski, Trans. AMS 137 (1969). We formalize

* `fact:poisson` (Poisson integrals; imported facts, stated with Mathlib's `poissonKernel`);
* `fact:jordan-access` (Jordan curve theorem with accessibility; imported fact);
* `lem:general-limit-endpoints` (`asymptotic_at_endpoint`);
* `lem:ha-sequences` (`exists_intervals`);
* `lem:ha-estimates` (`omega_jordan`, `omega_closure_disjoint`, `diam_omega_tendsto`, `fn_le_eps`,
  `fn_le_eps_sqrt`, `fn_tendsto_zero`);
* `lem:ha-lemma` (`accessible_avoiding_domains`; no longer used by the example, which uses the
  explicit `lem:ha-access` instead);
* ingredients of `thm:ha-example` (`f_harmonic`, `f_tendsto_one`, `f_tendsto_zero_of_arc`,
  `not_isBaireOne`).

`lem:ha-access` and `thm:ha-example` itself are in `TJK.Harmonic.Access`.

The Poisson integral of `φ : ℂ → ℝ` is `poisson φ z = ⨍_{|ζ| = 1} P(z, ζ) φ(ζ)`, with Mathlib's
`poissonKernel 0 z ζ = (|ζ|² - |z|²)/|ζ - z|²`.
-/

namespace TJK.Harmonic

open _root_.Set Filter Topology Metric Function MeasureTheory Complex
open scoped Real

/-! ### Poisson integrals (`fact:poisson`) -/

/-- The Poisson integral `P[φ]` of a function on the unit circle. -/
noncomputable def poisson (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage (fun ζ => poissonKernel 0 z ζ * φ ζ) 0 1

/-- `fact:poisson` (ii): if `φ` is integrable on the circle, `S` has full measure on the circle,
`ζ₀ ∈ S` and `φ|_S` is continuous at `ζ₀`, then `P[φ]` has the general limit `φ ζ₀` at `ζ₀`.
Imported fact (Hoffman, pp. 32–38). -/
theorem poisson_tendsto_of_continuousAt (φ : ℂ → ℝ) (hφ : CircleIntegrable φ 0 1) (S : Set ℂ)
    (hS : ∀ᵐ θ, circleMap 0 1 θ ∈ S) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ S ∩ circle)
    (hc : ContinuousWithinAt φ (S ∩ circle) ζ₀) :
    Tendsto (poisson φ) (𝓝[disc] ζ₀) (𝓝 (φ ζ₀)) :=
  poisson_tendsto_of_continuousAt' φ hφ S hS hζ₀ hc

/-- `fact:poisson` (iii): a harmonic function in the disc with bounded `p`-th integral means,
`p > 1`, has radial limits almost everywhere on the circle, and it is the Poisson integral of its
(integrable) radial limit function. Imported fact (Hoffman, pp. 32–38). -/
theorem hp_radial_limit_poisson (u : ℂ → ℝ) (hu : InnerProductSpace.HarmonicOnNhd u disc)
    (p : ℝ) (hp : 1 < p)
    (hmean : ∃ B : ℝ, ∀ r ∈ Ico (0 : ℝ) 1,
      ∫ θ in (0 : ℝ)..(2 * π), |u (r * Complex.exp (θ * Complex.I))| ^ p ≤ B) :
    ∃ ψ : ℂ → ℝ, CircleIntegrable ψ 0 1 ∧
      (∀ᵐ θ, Tendsto (fun r : ℝ => u (r * circleMap 0 1 θ)) (𝓝[<] 1)
        (𝓝 (ψ (circleMap 0 1 θ)))) ∧
      ∀ z ∈ disc, u z = poisson ψ z :=
  hp_radial_limit_poisson' u hu p hp hmean

/-! ### The Jordan curve theorem (`fact:jordan-access`) -/

/-- `fact:jordan-access`: the complement of a Jordan curve `Γ = e([-π, π])` (`e` continuous,
`e (-π) = e π`, injective on `[-π, π)`) is the disjoint union of two connected open sets, a bounded
one `B` and an unbounded one `U`, each with frontier `Γ`, and every point of `Γ` is accessible from
`B` by a simple arc. Imported fact (Jordan curve theorem; Newman, *Elements*, p. 164). -/
theorem jordan_accessible (e : ℝ → ℂ) (he : Continuous e) (hper : e (-π) = e π)
    (hinj : InjOn e (Ico (-π) π)) :
    ∃ B U : Set ℂ, IsOpen B ∧ IsOpen U ∧ IsConnected B ∧ IsConnected U ∧ Disjoint B U ∧
      B ∪ U = (e '' Icc (-π) π)ᶜ ∧ Bornology.IsBounded B ∧ ¬ Bornology.IsBounded U ∧
      frontier B = e '' Icc (-π) π ∧ frontier U = e '' Icc (-π) π ∧
      ∀ p ∈ e '' Icc (-π) π, ∃ γ, IsArcAt B p γ := by
  sorry

/-! ### Angles -/

theorem expI_eq_expI_iff {a b : ℝ} : expI a = expI b ↔ ∃ k : ℤ, a = b + k * (2 * π) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨k, ?_⟩
    have := congrArg Complex.im hk
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · rintro ⟨k, rfl⟩
    exact expI_add_int_mul b k

theorem eq_of_expI_eq {a b : ℝ} (h : expI a = expI b) (hab : |a - b| < 2 * π) : a = b := by
  obtain ⟨k, hk⟩ := expI_eq_expI_iff.1 h
  have hk' : |(k : ℝ)| * (2 * π) < 2 * π := by
    rw [show a - b = k * (2 * π) by linarith, abs_mul, abs_of_pos Real.two_pi_pos] at hab
    exact hab
  have : |(k : ℝ)| < 1 := by nlinarith [Real.two_pi_pos]
  have : k = 0 := by
    rw [← Int.cast_abs] at this
    have : |k| < 1 := by exact_mod_cast this
    have := abs_lt.1 this
    omega
  subst this
  simpa using hk

/-- `expI` is injective on `(-π, π]`. -/
theorem expI_injOn : InjOn expI (Ioc (-π) π) := fun a ha b hb h =>
  eq_of_expI_eq h (by rw [abs_lt]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2])

theorem expI_neg_pi : expI (-π) = expI π := by
  rw [show -π = π + ((-1 : ℤ) : ℝ) * (2 * π) by push_cast; ring, expI_add_int_mul]

theorem continuous_expI : Continuous expI := by unfold expI; fun_prop

theorem expI_arg' (z : ℂ) : z = (‖z‖ : ℂ) * expI (arg z) :=
  (Complex.norm_mul_exp_arg_mul_I z).symm

/-! ### The intervals (`lem:ha-sequences`) -/

/-- Left end `c - π ε² / 2` of the angle interval with centre `c` and parameter `ε`. -/
noncomputable def lo (c ε : ℝ) : ℝ := c - π * ε ^ 2 / 2

/-- Right end `c + π ε² / 2` of the angle interval with centre `c` and parameter `ε`. -/
noncomputable def hi (c ε : ℝ) : ℝ := c + π * ε ^ 2 / 2

/-- Conditions I and II for the `k`-th interval, given as (centre, `ε`). -/
def Single (k : ℕ) (x : ℝ × ℝ) : Prop :=
  0 < x.2 ∧ x.2 ≤ (1 / 2) ^ (k + 2) ∧ -π < lo x.1 x.2 ∧ hi x.1 x.2 < π

/-- Condition IV between an earlier interval `x` and a later one `y`: the arcs of the circle
`e^{i[lo, hi]}` are at distance at least `4 ε_y^{1/4}`. -/
def Sep (x y : ℝ × ℝ) : Prop :=
  ∀ s ∈ Icc (lo x.1 x.2) (hi x.1 x.2), ∀ t ∈ Icc (lo y.1 y.2) (hi y.1 y.2),
    4 * √(√y.2) ≤ ‖expI s - expI t‖

/-- The first `q` intervals satisfy I, II, IV and cover `p 0, …, p (q-1)`. -/
def Good (p : ℕ → ℝ) (q : ℕ) (g : ℕ → ℝ × ℝ) : Prop :=
  (∀ k < q, Single k (g k)) ∧ (∀ h k, h < k → k < q → Sep (g h) (g k)) ∧
    ∀ h < q, ∃ k < q, p h ∈ Icc (lo (g k).1 (g k).2) (hi (g k).1 (g k).2)

theorem lo_le_hi {c ε : ℝ} : lo c ε ≤ hi c ε := by
  unfold lo hi; nlinarith [Real.pi_pos, sq_nonneg ε]

theorem mem_lo_hi {c ε : ℝ} : c ∈ Icc (lo c ε) (hi c ε) := by
  unfold lo hi; constructor <;> nlinarith [Real.pi_pos, sq_nonneg ε]

theorem good_step (p : ℕ → ℝ) (hp : ∀ n, p n ∈ Ioo (-π) π) (q : ℕ) (g : ℕ → ℝ × ℝ)
    (hg : Good p q g) : ∃ x, Good p (q + 1) (update g q x) := by
  obtain ⟨hS, hSep, hcov⟩ := hg
  -- a centre `c ∈ (-π, π)` outside the earlier intervals, equal to `p q` if `p q` is uncovered
  obtain ⟨c, hc, hcout, hcp⟩ : ∃ c ∈ Ioo (-π) π,
      (∀ k < q, c ∉ Icc (lo (g k).1 (g k).2) (hi (g k).1 (g k).2)) ∧
      ((∃ k < q, p q ∈ Icc (lo (g k).1 (g k).2) (hi (g k).1 (g k).2)) ∨ c = p q) := by
    by_cases hcv : ∃ k < q, p q ∈ Icc (lo (g k).1 (g k).2) (hi (g k).1 (g k).2)
    · obtain ⟨k₀, hk₀, -⟩ := id hcv
      obtain ⟨m, hm, hmax⟩ := (Finset.range q).exists_max_image (fun k => hi (g k).1 (g k).2)
        ⟨k₀, Finset.mem_range.2 hk₀⟩
      have hm' := hS m (Finset.mem_range.1 hm)
      refine ⟨(hi (g m).1 (g m).2 + π) / 2, ⟨?_, ?_⟩, fun k hk hmem => ?_, Or.inl hcv⟩
      · have := hm'.2.2.1; have := lo_le_hi (c := (g m).1) (ε := (g m).2); linarith [Real.pi_pos]
      · linarith [hm'.2.2.2]
      · have := hmax k (Finset.mem_range.2 hk)
        linarith [hmem.2, hm'.2.2.2]
    · push Not at hcv
      exact ⟨p q, hp q, fun k hk h => hcv k hk h, Or.inr rfl⟩
  -- distances from `e^{ic}` to the earlier arcs
  have hd : ∀ k < q,
      0 < infDist (expI c) (expI '' Icc (lo (g k).1 (g k).2) (hi (g k).1 (g k).2)) := by
    intro k hk
    have hK : IsCompact (expI '' Icc (lo (g k).1 (g k).2) (hi (g k).1 (g k).2)) :=
      isCompact_Icc.image continuous_expI
    rw [← infDist_pos_iff_notMem_closure ((nonempty_Icc.2 lo_le_hi).image _),
      hK.isClosed.closure_eq]
    rintro ⟨s, hs, hse⟩
    have hk' := hS k hk
    have : s = c := expI_injOn ⟨by linarith [hs.1, hk'.2.2.1], by linarith [hs.2, hk'.2.2.2]⟩
      ⟨hc.1, hc.2.le⟩ hse
    exact hcout k hk (this ▸ hs)
  have hcont : Continuous fun ε : ℝ => π * ε ^ 2 / 2 + 4 * √(√ε) := by fun_prop
  have h0 : Tendsto (fun ε : ℝ => π * ε ^ 2 / 2 + 4 * √(√ε)) (𝓝[>] 0) (𝓝 0) := by
    have := hcont.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      Real.sqrt_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlo : Tendsto (fun ε : ℝ => lo c ε) (𝓝[>] 0) (𝓝 c) := by
    have : Continuous fun ε : ℝ => lo c ε := by unfold lo; fun_prop
    have := this.tendsto 0
    simp only [lo, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun ε : ℝ => hi c ε) (𝓝[>] 0) (𝓝 c) := by
    have : Continuous fun ε : ℝ => hi c ε := by unfold hi; fun_prop
    have := this.tendsto 0
    simp only [hi, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ (1 / 2) ^ (q + 2) ∧ -π < lo c ε ∧ hi c ε < π ∧
      ∀ k ∈ Finset.range q, π * ε ^ 2 / 2 + 4 * √(√ε) <
        infDist (expI c) (expI '' Icc (lo (g k).1 (g k).2) (hi (g k).1 (g k).2)) := by
    have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ (1 / 2) ^ (q + 2) :=
      (hid.eventually (gt_mem_nhds (by positivity))).mono fun _ h => h.le
    have e3 := hlo.eventually (lt_mem_nhds hc.1)
    have e4 := hhi.eventually (gt_mem_nhds hc.2)
    have e5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k ∈ Finset.range q, π * ε ^ 2 / 2 + 4 * √(√ε) <
        infDist (expI c) (expI '' Icc (lo (g k).1 (g k).2) (hi (g k).1 (g k).2)) := by
      rw [eventually_all_finset]
      intro k hk
      exact h0.eventually (gt_mem_nhds (hd k (Finset.mem_range.1 hk)))
    filter_upwards [e1, e2, e3, e4, e5] with ε h1 h2 h3 h4 h5 using ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε0, hεle, hεlo, hεhi, hεd⟩ := hev.exists
  refine ⟨(c, ε), ?_, ?_, ?_⟩
  · intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [update_of_ne hk.ne]; exact hS k hk
    · rw [update_self]; exact ⟨hε0, hεle, hεlo, hεhi⟩
  · intro h k hhk hk
    rw [update_of_ne (hhk.trans_le (Nat.lt_succ_iff.1 hk)).ne]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [update_of_ne hk.ne]; exact hSep h k hhk hk
    · rw [update_self]
      intro s hs t ht
      have h1 := infDist_le_dist_of_mem (x := expI c) (mem_image_of_mem expI hs)
      have h2 := hεd h (Finset.mem_range.2 hhk)
      have h3 : ‖expI c - expI t‖ ≤ π * ε ^ 2 / 2 := by
        refine (norm_expI_sub_le t c).trans ?_
        rw [abs_le]; unfold lo hi at ht; constructor <;> linarith [ht.1, ht.2]
      rw [dist_eq_norm] at h1
      have h4 : ‖expI c - expI s‖ ≤ ‖expI s - expI t‖ + ‖expI c - expI t‖ := by
        rw [norm_sub_rev (expI c) (expI s)]
        calc ‖expI s - expI c‖ = ‖(expI s - expI t) - (expI c - expI t)‖ := by ring_nf
          _ ≤ _ := norm_sub_le _ _
      simp only
      linarith
  · intro h hh
    rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | rfl
    · obtain ⟨k, hk, hmem⟩ := hcov h hh
      exact ⟨k, hk.trans (Nat.lt_succ_self q), by rwa [update_of_ne hk.ne]⟩
    · rcases hcp with ⟨k, hk, hmem⟩ | hcp
      · exact ⟨k, hk.trans (Nat.lt_succ_self _), by rwa [update_of_ne hk.ne]⟩
      · exact ⟨h, Nat.lt_succ_self h, by rw [update_self, ← hcp]; exact mem_lo_hi⟩

open Classical in
/-- The recursive construction of the intervals. -/
noncomputable def build (p : ℕ → ℝ) (hp : ∀ n, p n ∈ Ioo (-π) π) : ℕ → ℕ → ℝ × ℝ
  | 0 => fun _ => (0, 0)
  | q + 1 => if h : Good p q (build p hp q) then
      update (build p hp q) q (Classical.choose (good_step p hp q _ h)) else build p hp q

theorem build_good (p : ℕ → ℝ) (hp : ∀ n, p n ∈ Ioo (-π) π) (q : ℕ) :
    Good p q (build p hp q) := by
  induction q with
  | zero => exact ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ k _ hk => absurd hk
      (Nat.not_lt_zero _), fun h hh => absurd hh (Nat.not_lt_zero _)⟩
  | succ q ih =>
    rw [build, dif_pos ih]
    exact Classical.choose_spec (good_step p hp q _ ih)

theorem build_stable (p : ℕ → ℝ) (hp : ∀ n, p n ∈ Ioo (-π) π) {k q : ℕ} (hk : k < q) :
    build p hp q k = build p hp (k + 1) k := by
  induction q with
  | zero => exact absurd hk (Nat.not_lt_zero _)
  | succ q ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [← ih hk, build, dif_pos (build_good p hp q), update_of_ne hk.ne]
    · rfl

/-- The data of `lem:ha-sequences`: centres `c k` and parameters `ε k` of the angle intervals
`[α k, β k] = [c k - π ε_k² / 2, c k + π ε_k² / 2]` with conditions I, II and IV (IV in the
chordal form: the arcs `e^{i[α h, β h]}`, `e^{i[α k, β k]}`, `h < k`, are at distance at least
`4 ε_k^{1/4}`). -/
structure Intervals where
  c : ℕ → ℝ
  ε : ℕ → ℝ
  ε_pos : ∀ k, 0 < ε k
  ε_le : ∀ k, ε k ≤ (1 / 2) ^ (k + 2)
  lo_gt : ∀ k, -π < lo (c k) (ε k)
  hi_lt : ∀ k, hi (c k) (ε k) < π
  sep : ∀ h k, h < k → Sep (c h, ε h) (c k, ε k)

/-- `lem:ha-sequences`: for any sequence `p` in `(-π, π)` there are intervals satisfying I, II,
IV whose union contains every `p h` (V). -/
theorem exists_intervals (p : ℕ → ℝ) (hp : ∀ n, p n ∈ Ioo (-π) π) :
    ∃ d : Intervals, ∀ h, ∃ k, p h ∈ Icc (lo (d.c k) (d.ε k)) (hi (d.c k) (d.ε k)) := by
  let g : ℕ → ℝ × ℝ := fun k => build p hp (k + 1) k
  have hS : ∀ k, Single k (g k) := fun k => (build_good p hp (k + 1)).1 k (Nat.lt_succ_self k)
  refine ⟨⟨fun k => (g k).1, fun k => (g k).2, fun k => (hS k).1, fun k => (hS k).2.1,
    fun k => (hS k).2.2.1, fun k => (hS k).2.2.2, fun h k hhk => ?_⟩, fun h => ?_⟩
  · have := (build_good p hp (k + 1)).2.1 h k hhk (Nat.lt_succ_self k)
    rwa [build_stable p hp (hhk.trans (Nat.lt_succ_self k))] at this
  · obtain ⟨k, hk, hmem⟩ := (build_good p hp (h + 1)).2.2 h (Nat.lt_succ_self h)
    refine ⟨k, ?_⟩
    rwa [build_stable p hp hk] at hmem

/-! ### Families of Jordan domains along the circle (hypotheses of `lem:ha-lemma`) -/

/-- The hypotheses of `lem:ha-lemma`, in parametrized form. `I n = e^{i[a n, b n]}` are disjoint
closed arcs (`-π < a n < b n < π`); `Ω n ⊆ 𝔻` is connected; the part of its frontier off the open
arc `I n*` is the simple arc `Γ n = g n ([a n, b n])` from `e^{i a n}` to `e^{i b n}` through `𝔻`,
so that `Ω̄ n ⊆ Ω n ∪ Γ n ∪ I n` (this is how we use that `Ω n` is a Jordan domain with
`Ω̄ n ∩ C = I n`); the closures are pairwise disjoint; and `Γ n` is uniformly close to `I n`
(which is what `diam Ω n → 0` is used for). -/
structure DomainFamily (a b : ℕ → ℝ) (Ω : ℕ → Set ℂ) (g : ℕ → ℝ → ℂ) : Prop where
  a_gt : ∀ n, -π < a n
  lt : ∀ n, a n < b n
  b_lt : ∀ n, b n < π
  disj : Pairwise fun n m => Disjoint (Icc (a n) (b n)) (Icc (a m) (b m))
  cont : ∀ n, Continuous (g n)
  inj : ∀ n, InjOn (g n) (Icc (a n) (b n))
  left : ∀ n, g n (a n) = expI (a n)
  right : ∀ n, g n (b n) = expI (b n)
  mem_disc : ∀ n, ∀ t ∈ Ioo (a n) (b n), g n t ∈ disc
  conn : ∀ n, IsPreconnected (Ω n)
  sub_disc : ∀ n, Ω n ⊆ disc
  disj_curve : ∀ n, Disjoint (Ω n) (g n '' Icc (a n) (b n))
  curve_sub : ∀ n, g n '' Icc (a n) (b n) ⊆ closure (Ω n)
  closure_disj : Pairwise fun n m => Disjoint (closure (Ω n)) (closure (Ω m))
  closure_sub : ∀ n, closure (Ω n) ⊆ Ω n ∪ g n '' Icc (a n) (b n) ∪ expI '' Icc (a n) (b n)
  touch : ∀ n, ∃ t ∈ Ioo (a n) (b n), expI t ∈ closure (Ω n)
  small : ∀ δ > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (a n) (b n), ‖g n t - expI t‖ ≤ δ

/-! ### The domains `Ω n` (`lem:ha-estimates`, geometric part) -/

attribute [fun_prop] continuous_expI

/-- `vq r = (1 - r)^{1/4}`. -/
noncomputable def vq (r : ℝ) : ℝ := √(√(1 - r))

@[fun_prop] theorem continuous_vq : Continuous vq := by unfold vq; fun_prop

theorem vq_nonneg (r : ℝ) : 0 ≤ vq r := Real.sqrt_nonneg _

theorem vq_one : vq 1 = 0 := by simp [vq]

theorem vq_le {r ε : ℝ} (h : 1 - ε ≤ r) : vq r ≤ √(√ε) :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by linarith))

theorem vq_lt_one {r : ℝ} (h : 0 < r) : vq r < 1 := by
  unfold vq
  rcases le_or_gt (1 - r) 0 with h' | h'
  · rw [Real.sqrt_eq_zero'.2 h', Real.sqrt_zero]; norm_num
  · rw [Real.sqrt_lt' one_pos, one_pow, Real.sqrt_lt' one_pos, one_pow]; linarith

theorem vq_sq {r : ℝ} : vq r ^ 2 = √(1 - r) := Real.sq_sqrt (Real.sqrt_nonneg _)

/-- The parameter of the first coordinate along the three edges `s = 0`, `r = 1 - ε`, `s = 1` of
the rectangle, as a function of `u ∈ [0, 3]`. -/
noncomputable def σe (u : ℝ) : ℝ := max 0 (min 1 (u - 1))

/-- The depth fraction `(1 - r)/ε` along the three edges, as a function of `u ∈ [0, 3]`. -/
noncomputable def we (u : ℝ) : ℝ := min 1 (min u (3 - u))

@[fun_prop] theorem continuous_σe : Continuous σe := by unfold σe; fun_prop
@[fun_prop] theorem continuous_we : Continuous we := by unfold we; fun_prop

theorem σe_we_1 {u : ℝ} (h : u ∈ Icc (0 : ℝ) 1) : σe u = 0 ∧ we u = u := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · unfold σe; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  · unfold we; rw [min_eq_left (by linarith : u ≤ 3 - u), min_eq_right h1]

theorem σe_we_2 {u : ℝ} (h : u ∈ Icc (1 : ℝ) 2) : σe u = u - 1 ∧ we u = 1 := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · unfold σe; rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  · unfold we; rw [min_eq_left (le_min (by linarith) (by linarith))]

theorem σe_we_3 {u : ℝ} (h : u ∈ Icc (2 : ℝ) 3) : σe u = 1 ∧ we u = 3 - u := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · unfold σe; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  · unfold we; rw [min_eq_right (by linarith : 3 - u ≤ u), min_eq_right (by linarith : 3 - u ≤ 1)]

theorem σe_mem (u : ℝ) : σe u ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem we_mem {u : ℝ} (h : u ∈ Icc (0 : ℝ) 3) : we u ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_min h.1 (by linarith [h.2])), min_le_left _ _⟩

theorem we_pos {u : ℝ} (h : u ∈ Ioo (0 : ℝ) 3) : 0 < we u :=
  lt_min one_pos (lt_min h.1 (by linarith [h.2]))

theorem edge_cases {u : ℝ} (h : u ∈ Icc (0 : ℝ) 3) :
    (σe u = 0 ∧ we u = u ∧ u ≤ 1) ∨ (σe u = u - 1 ∧ we u = 1 ∧ 1 ≤ u ∧ u ≤ 2) ∨
      (σe u = 1 ∧ we u = 3 - u ∧ 2 ≤ u) := by
  rcases le_total u 1 with h1 | h1
  · exact Or.inl ⟨(σe_we_1 ⟨h.1, h1⟩).1, (σe_we_1 ⟨h.1, h1⟩).2, h1⟩
  rcases le_total u 2 with h2 | h2
  · exact Or.inr (Or.inl ⟨(σe_we_2 ⟨h1, h2⟩).1, (σe_we_2 ⟨h1, h2⟩).2, h1, h2⟩)
  · exact Or.inr (Or.inr ⟨(σe_we_3 ⟨h2, h.2⟩).1, (σe_we_3 ⟨h2, h.2⟩).2, h2⟩)

theorem edge_injOn : InjOn (fun u => (σe u, we u)) (Icc (0 : ℝ) 3) := by
  intro u hu u' hu' huu
  simp only [Prod.mk.injEq] at huu
  obtain ⟨h1, h2⟩ := huu
  rcases edge_cases hu with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩ <;>
  rcases edge_cases hu' with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  · rw [a1, b1] at h1; rw [a2, b2] at h2; linarith

theorem edge_boundary {u : ℝ} (h : u ∈ Icc (0 : ℝ) 3) : σe u = 0 ∨ σe u = 1 ∨ we u = 1 := by
  rcases edge_cases h with ⟨a1, -⟩ | ⟨-, a2, -⟩ | ⟨a1, -⟩
  · exact Or.inl a1
  · exact Or.inr (Or.inr a2)
  · exact Or.inr (Or.inl a1)

theorem edge_surj {s w : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1)
    (h : s = 0 ∨ s = 1 ∨ w = 1) : ∃ u ∈ Icc (0 : ℝ) 3, σe u = s ∧ we u = w := by
  rcases h with rfl | rfl | rfl
  · exact ⟨w, ⟨hw.1, by linarith [hw.2]⟩, σe_we_1 hw⟩
  · refine ⟨3 - w, ⟨by linarith [hw.2], by linarith [hw.1]⟩, ?_⟩
    have := σe_we_3 (u := 3 - w) ⟨by linarith [hw.2], by linarith [hw.1]⟩
    rw [this.1, this.2]; simp
  · refine ⟨s + 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    have := σe_we_2 (u := s + 1) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [this.1, this.2]; simp

namespace Intervals

variable (d : Intervals)

/-- `α n`, the left end of the `n`-th angle interval. -/
noncomputable def α (n : ℕ) : ℝ := lo (d.c n) (d.ε n)

/-- `β n`, the right end of the `n`-th angle interval. -/
noncomputable def β (n : ℕ) : ℝ := hi (d.c n) (d.ε n)

theorem β_sub_α (n : ℕ) : d.β n - d.α n = π * d.ε n ^ 2 := by unfold β α lo hi; ring

theorem α_lt_β (n : ℕ) : d.α n < d.β n := by
  have := d.ε_pos n; rw [← sub_pos, β_sub_α]; positivity

theorem ε_le_quarter (n : ℕ) : d.ε n ≤ 1 / 4 :=
  (d.ε_le n).trans ((pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (by omega : 2 ≤ n + 2)).trans (by norm_num))

theorem β_sub_α_le (n : ℕ) : d.β n - d.α n ≤ π / 16 := by
  rw [β_sub_α]
  have := d.ε_le_quarter n; have := d.ε_pos n
  have : d.ε n ^ 2 ≤ 1 / 16 := by nlinarith
  nlinarith [Real.pi_pos]

theorem α_gt (n : ℕ) : -π < d.α n := d.lo_gt n

theorem β_lt (n : ℕ) : d.β n < π := d.hi_lt n

theorem c_eq (n : ℕ) : d.c n = d.α n + (d.β n - d.α n) / 2 := by unfold β α lo hi; ring

/-- The angle `θ_n(s, r) = α - v + s (β - α + 2 v)`, `v = (1 - r)^{1/4}`. -/
noncomputable def θ (n : ℕ) (s r : ℝ) : ℝ := d.α n - vq r + s * (d.β n - d.α n + 2 * vq r)

/-- `H_n(s, r) = r e^{i θ_n(s, r)}`, a homeomorphism of the closed rectangle onto `Ω̄_n`. -/
noncomputable def H (n : ℕ) (x : ℝ × ℝ) : ℂ := (x.2 : ℂ) * expI (d.θ n x.1 x.2)

/-- The open rectangle `(0, 1) × (1 - ε_n, 1)`. -/
def rect (n : ℕ) : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo (1 - d.ε n) 1

/-- The closed rectangle `[0, 1] × [1 - ε_n, 1]`. -/
def crect (n : ℕ) : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc (1 - d.ε n) 1

/-- `Ω_n = {r e^{iθ} : 1 - ε_n < r < 1, Δ(θ, [α_n, β_n]) < (1 - r)^{1/4}}`, the image of the open
rectangle under `H_n`. -/
def Ω (n : ℕ) : Set ℂ := d.H n '' d.rect n

/-- The closed arc `I_n = e^{i[α_n, β_n]}`. -/
def I (n : ℕ) : Set ℂ := expI '' Icc (d.α n) (d.β n)

/-- The arc `Γ_n` (the frontier of `Ω_n` off `I_n*`), parametrized by `[α_n, β_n]`. -/
noncomputable def g (n : ℕ) (t : ℝ) : ℂ :=
  d.H n (σe (3 * (t - d.α n) / (d.β n - d.α n)),
    1 - d.ε n * we (3 * (t - d.α n) / (d.β n - d.α n)))

theorem continuous_θ (n : ℕ) : Continuous fun x : ℝ × ℝ => d.θ n x.1 x.2 := by
  unfold θ; fun_prop

theorem continuous_H (n : ℕ) : Continuous (d.H n) := by
  unfold H
  have := d.continuous_θ n
  fun_prop

theorem norm_H (n : ℕ) {x : ℝ × ℝ} (hx : 0 ≤ x.2) : ‖d.H n x‖ = x.2 := by
  rw [H, norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_of_nonneg hx]

theorem one_sub_ε_pos (n : ℕ) : 3 / 4 ≤ 1 - d.ε n := by linarith [d.ε_le_quarter n]

theorem θ_mem (n : ℕ) {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    d.θ n s r ∈ Icc (d.α n - vq r) (d.β n + vq r) := by
  have := vq_nonneg r; have := d.α_lt_β n
  unfold θ
  constructor <;> nlinarith [hs.1, hs.2]

theorem H_injOn (n : ℕ) : InjOn (d.H n) (d.crect n) := by
  intro x hx y hy hxy
  have h34 := d.one_sub_ε_pos n
  have hx2 : 0 < x.2 := by linarith [hx.2.1]
  have hy2 : 0 < y.2 := by linarith [hy.2.1]
  have hr : x.2 = y.2 := by
    have := congrArg norm hxy
    rwa [d.norm_H n hx2.le, d.norm_H n hy2.le] at this
  have he : expI (d.θ n x.1 x.2) = expI (d.θ n y.1 y.2) := by
    unfold H at hxy
    refine mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hy2.ne') ?_
    rw [← hxy]; congr 1; exact_mod_cast hr.symm
  have hw : 0 < d.β n - d.α n + 2 * vq y.2 := by linarith [d.α_lt_β n, vq_nonneg y.2]
  have hw' : d.β n - d.α n + 2 * vq y.2 < 2 * π := by
    linarith [d.β_sub_α_le n, vq_lt_one hy2, Real.pi_gt_three]
  have hdiff : d.θ n x.1 x.2 - d.θ n y.1 y.2 = (x.1 - y.1) * (d.β n - d.α n + 2 * vq y.2) := by
    unfold θ; rw [hr]; ring
  have h1 : |x.1 - y.1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hx.1.1, hx.1.2, hy.1.1, hy.1.2]
  have := eq_of_expI_eq he (by
    rw [hdiff, abs_mul, abs_of_pos hw]
    calc |x.1 - y.1| * (d.β n - d.α n + 2 * vq y.2) ≤ 1 * (d.β n - d.α n + 2 * vq y.2) :=
          mul_le_mul_of_nonneg_right h1 hw.le
      _ < 2 * π := by linarith)
  have h0 : (x.1 - y.1) * (d.β n - d.α n + 2 * vq y.2) = 0 := by rw [← hdiff]; linarith
  have : x.1 = y.1 := by
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · linarith
  exact Prod.ext this hr

/-- Polar description of `Ω_n`. -/
theorem mem_Ω (n : ℕ) {r t : ℝ} (hr : r ∈ Ioo (1 - d.ε n) 1)
    (ht : t ∈ Ioo (d.α n - vq r) (d.β n + vq r)) : (r : ℂ) * expI t ∈ d.Ω n := by
  have hw : 0 < d.β n - d.α n + 2 * vq r := by linarith [d.α_lt_β n, vq_nonneg r]
  refine ⟨((t - (d.α n - vq r)) / (d.β n - d.α n + 2 * vq r), r),
    ⟨⟨div_pos (by linarith [ht.1]) hw, (div_lt_one hw).2 (by linarith [ht.2])⟩, hr⟩, ?_⟩
  simp only [H, θ]
  rw [div_mul_cancel₀ _ hw.ne']
  ring_nf

theorem closure_rect (n : ℕ) : closure (d.rect n) = d.crect n := by
  have := d.ε_pos n
  rw [rect, crect, closure_prod_eq, closure_Ioo zero_ne_one, closure_Ioo (by linarith)]

theorem closure_Ω (n : ℕ) : closure (d.Ω n) = d.H n '' d.crect n := by
  apply Subset.antisymm
  · refine closure_minimal (image_mono ?_)
      ((isCompact_Icc.prod isCompact_Icc).image (d.continuous_H n)).isClosed
    rw [← d.closure_rect n]; exact subset_closure
  · rw [← d.closure_rect n]; exact image_closure_subset_closure_image (d.continuous_H n)

theorem uu_mem (n : ℕ) {t : ℝ} (ht : t ∈ Icc (d.α n) (d.β n)) :
    3 * (t - d.α n) / (d.β n - d.α n) ∈ Icc (0 : ℝ) 3 := by
  have h := sub_pos.2 (d.α_lt_β n)
  constructor
  · exact div_nonneg (by linarith [ht.1]) h.le
  · rw [div_le_iff₀ h]; linarith [ht.2]

theorem edge_mem_crect (n : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 3) :
    (σe u, 1 - d.ε n * we u) ∈ d.crect n := by
  have := d.ε_pos n; have hw := we_mem hu
  exact ⟨σe_mem u, by nlinarith [hw.2], by nlinarith [hw.1]⟩

theorem g_injOn (n : ℕ) : InjOn (d.g n) (Icc (d.α n) (d.β n)) := by
  intro t ht t' ht' h
  have h' := d.H_injOn n (d.edge_mem_crect n (d.uu_mem n ht))
    (d.edge_mem_crect n (d.uu_mem n ht')) h
  simp only [Prod.mk.injEq] at h'
  have hw : we (3 * (t - d.α n) / (d.β n - d.α n)) = we (3 * (t' - d.α n) / (d.β n - d.α n)) := by
    have := d.ε_pos n
    have h2 := h'.2
    field_simp at h2
    nlinarith [h2]
  have := edge_injOn (d.uu_mem n ht) (d.uu_mem n ht') (Prod.ext h'.1 hw)
  have hb := sub_pos.2 (d.α_lt_β n)
  field_simp at this
  linarith

theorem g_left (n : ℕ) : d.g n (d.α n) = expI (d.α n) := by
  simp [g, H, θ, σe, we, vq]

theorem g_right (n : ℕ) : d.g n (d.β n) = expI (d.β n) := by
  have hb := sub_pos.2 (d.α_lt_β n)
  have : 3 * (d.β n - d.α n) / (d.β n - d.α n) = 3 := by field_simp
  simp only [g, this, H, θ]
  have h1 : σe 3 = 1 := by norm_num [σe]
  have h2 : we 3 = 0 := by norm_num [we]
  rw [h1, h2]
  simp [vq]

theorem g_mem_disc (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (d.α n) (d.β n)) : d.g n t ∈ disc := by
  have hb := sub_pos.2 (d.α_lt_β n)
  have hu : 3 * (t - d.α n) / (d.β n - d.α n) ∈ Ioo (0 : ℝ) 3 := by
    constructor
    · exact div_pos (by linarith [ht.1]) hb
    · rw [div_lt_iff₀ hb]; linarith [ht.2]
  have hw := we_pos hu
  have hw1 := (we_mem (Ioo_subset_Icc_self hu)).2
  have := d.ε_pos n; have := d.ε_le_quarter n
  rw [mem_ball_zero_iff, g, d.norm_H n (by simp only; nlinarith)]
  simp only
  nlinarith

theorem crect_sub (n : ℕ) {x : ℝ × ℝ} (hx : x ∈ d.crect n) (hx' : x ∉ d.rect n) :
    x.2 = 1 ∨ ∃ t ∈ Icc (d.α n) (d.β n), d.g n t = d.H n x := by
  obtain ⟨⟨hs0, hs1⟩, hr0, hr1⟩ := hx
  have hε := d.ε_pos n
  by_cases hr : x.2 = 1
  · exact Or.inl hr
  refine Or.inr ?_
  have hcase : x.1 = 0 ∨ x.1 = 1 ∨ (1 - x.2) / d.ε n = 1 := by
    by_contra hc
    push Not at hc
    apply hx'
    refine ⟨⟨lt_of_le_of_ne hs0 (Ne.symm hc.1), lt_of_le_of_ne hs1 hc.2.1⟩,
      ⟨?_, lt_of_le_of_ne hr1 hr⟩⟩
    have : x.2 ≠ 1 - d.ε n := fun h => hc.2.2 (by rw [h]; field_simp; ring)
    exact lt_of_le_of_ne hr0 (Ne.symm this)
  obtain ⟨u, hu, hσ, hw⟩ := edge_surj (s := x.1) (w := (1 - x.2) / d.ε n) ⟨hs0, hs1⟩
    ⟨div_nonneg (by linarith) hε.le, (div_le_one hε).2 (by linarith)⟩ hcase
  have hb := sub_pos.2 (d.α_lt_β n)
  refine ⟨d.α n + u * (d.β n - d.α n) / 3, ⟨?_, ?_⟩, ?_⟩
  · have := mul_nonneg hu.1 hb.le; linarith
  · have := mul_le_mul_of_nonneg_right hu.2 hb.le; linarith
  · have : 3 * (d.α n + u * (d.β n - d.α n) / 3 - d.α n) / (d.β n - d.α n) = u := by
      field_simp; ring
    rw [g, this, hσ, hw]
    congr 1
    ext <;> simp only; field_simp; ring

theorem H_one (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : d.H n (s, 1) ∈ d.I n := by
  have hb := sub_pos.2 (d.α_lt_β n)
  refine ⟨d.α n + s * (d.β n - d.α n), ⟨?_, ?_⟩, ?_⟩
  · nlinarith [hs.1]
  · nlinarith [hs.2]
  · simp [H, θ, vq_one]

theorem I_sub_closure (n : ℕ) : d.I n ⊆ closure (d.Ω n) := by
  rw [d.closure_Ω]
  rintro _ ⟨t, ht, rfl⟩
  have hb := sub_pos.2 (d.α_lt_β n)
  have := d.one_sub_ε_pos n; have := d.ε_pos n
  refine ⟨((t - d.α n) / (d.β n - d.α n), 1), ⟨⟨div_nonneg (by linarith [ht.1]) hb.le,
    (div_le_one hb).2 (by linarith [ht.2])⟩, by linarith, le_rfl⟩, ?_⟩
  simp only [H, θ, vq_one, Complex.ofReal_one, one_mul]
  congr 1
  field_simp
  ring

theorem exists_near (n : ℕ) {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ t ∈ Icc (d.α n) (d.β n), |d.θ n s r - t| ≤ vq r := by
  have hθ := d.θ_mem n (r := r) hs
  have := d.α_lt_β n
  by_cases h1 : d.θ n s r < d.α n
  · exact ⟨d.α n, ⟨le_rfl, this.le⟩, by rw [abs_le]; constructor <;> linarith [hθ.1]⟩
  by_cases h2 : d.β n < d.θ n s r
  · exact ⟨d.β n, ⟨this.le, le_rfl⟩, by rw [abs_le]; constructor <;> linarith [hθ.2]⟩
  push Not at h1 h2
  exact ⟨_, ⟨h1, h2⟩, by simp [vq_nonneg]⟩

/-- `lem:ha-estimates`: the closures `Ω̄_h`, `Ω̄_k` (`h ≠ k`) are disjoint (by IV). -/
theorem omega_closure_disjoint :
    Pairwise fun n m => Disjoint (closure (d.Ω n)) (closure (d.Ω m)) := by
  have key : ∀ h k, h < k → Disjoint (closure (d.Ω h)) (closure (d.Ω k)) := by
    intro h k hhk
    rw [d.closure_Ω, d.closure_Ω, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hx2 : 0 < x.2 := by linarith [hx.2.1, d.one_sub_ε_pos h]
    have hy2 : 0 < y.2 := by linarith [hy.2.1, d.one_sub_ε_pos k]
    have hr : y.2 = x.2 := by
      have := congrArg norm hxy
      rwa [d.norm_H k hy2.le, d.norm_H h hx2.le] at this
    have he : expI (d.θ k y.1 y.2) = expI (d.θ h x.1 x.2) := by
      unfold H at hxy
      refine mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hx2.ne') ?_
      rw [← hxy]; congr 1; exact_mod_cast hr.symm
    obtain ⟨s, hs, hsθ⟩ := d.exists_near h (r := x.2) hx.1
    obtain ⟨t, ht, htθ⟩ := d.exists_near k (r := y.2) hy.1
    have hv : vq x.2 ≤ √(√(d.ε k)) := vq_le (by linarith [hy.2.1])
    have hv' : vq y.2 ≤ √(√(d.ε k)) := vq_le hy.2.1
    have hsep := d.sep h k hhk s hs t ht
    have h1 := norm_expI_sub_le s (d.θ h x.1 x.2)
    have h2 := norm_expI_sub_le (d.θ k y.1 y.2) t
    have h3 : ‖expI s - expI t‖ ≤ ‖expI (d.θ h x.1 x.2) - expI s‖ +
        ‖expI t - expI (d.θ k y.1 y.2)‖ := by
      rw [he, norm_sub_rev (expI (d.θ h x.1 x.2)) (expI s),
        norm_sub_rev (expI t) (expI (d.θ h x.1 x.2))]
      calc ‖expI s - expI t‖ = ‖(expI s - expI (d.θ h x.1 x.2)) +
            (expI (d.θ h x.1 x.2) - expI t)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [abs_sub_comm] at h2
    have hpos : 0 < √(√(d.ε k)) := Real.sqrt_pos.2 (Real.sqrt_pos.2 (d.ε_pos k))
    simp only at hsep
    linarith
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact key n m h
  · exact (key m n h).symm

/-- `lem:ha-estimates`: `Ω̄_n` lies within `ε_n + π ε_n² + ε_n^{1/4}` of every point of `I_n`;
in particular `diam Ω_n → 0`. -/
theorem norm_sub_le_of_mem_closure (n : ℕ) {z : ℂ} (hz : z ∈ closure (d.Ω n)) {t : ℝ}
    (ht : t ∈ Icc (d.α n) (d.β n)) :
    ‖z - expI t‖ ≤ d.ε n + π * d.ε n ^ 2 + √(√(d.ε n)) := by
  rw [d.closure_Ω] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hθ := d.θ_mem n (r := x.2) hx.1
  have hv : vq x.2 ≤ √(√(d.ε n)) := vq_le hx.2.1
  have h1 : ‖(x.2 : ℂ) * expI (d.θ n x.1 x.2) - expI (d.θ n x.1 x.2)‖ = 1 - x.2 := by
    rw [show (x.2 : ℂ) * expI (d.θ n x.1 x.2) - expI (d.θ n x.1 x.2) =
      ((x.2 - 1 : ℝ) : ℂ) * expI (d.θ n x.1 x.2) by push_cast; ring, norm_mul, norm_expI,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.2.2])]
    ring
  have h2 := norm_expI_sub_le t (d.θ n x.1 x.2)
  have h3 : |d.θ n x.1 x.2 - t| ≤ π * d.ε n ^ 2 + √(√(d.ε n)) := by
    rw [abs_le, ← d.β_sub_α]; constructor <;> linarith [hθ.1, hθ.2, ht.1, ht.2]
  calc ‖d.H n x - expI t‖ ≤ ‖(x.2 : ℂ) * expI (d.θ n x.1 x.2) - expI (d.θ n x.1 x.2)‖ +
        ‖expI (d.θ n x.1 x.2) - expI t‖ := by
        unfold H
        calc _ = ‖((x.2 : ℂ) * expI (d.θ n x.1 x.2) - expI (d.θ n x.1 x.2)) +
            (expI (d.θ n x.1 x.2) - expI t)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by rw [h1]; linarith [hx.2.1]

theorem tendsto_ε : Tendsto d.ε atTop (𝓝 0) := by
  refine squeeze_zero (fun n => (d.ε_pos n).le) d.ε_le ?_
  have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  exact this.comp (tendsto_add_atTop_nat 2)

/-- `lem:ha-estimates`: `diam Ω_n → 0`, in the uniform form used by `lem:ha-lemma`. -/
theorem diam_omega_tendsto (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ z ∈ closure (d.Ω n), ∀ t ∈ Icc (d.α n) (d.β n), ‖z - expI t‖ ≤ δ := by
  have hc : Continuous fun x : ℝ => x + π * x ^ 2 + √(√x) := by fun_prop
  have := (hc.tendsto 0).comp d.tendsto_ε
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    Real.sqrt_zero] at this
  filter_upwards [this.eventually (gt_mem_nhds hδ)] with n hn z hz t ht
  exact (d.norm_sub_le_of_mem_closure n hz ht).trans hn.le

/-- `lem:ha-estimates`: the `Ω_n` form a family of Jordan domains as in `lem:ha-lemma`. -/
theorem omega_jordan : DomainFamily d.α d.β d.Ω d.g where
  a_gt := d.α_gt
  lt := d.α_lt_β
  b_lt := d.β_lt
  disj := by
    intro n m hnm
    rw [disjoint_left]
    intro t htn htm
    exact disjoint_left.1 (d.omega_closure_disjoint hnm) (d.I_sub_closure n ⟨t, htn, rfl⟩)
      (d.I_sub_closure m ⟨t, htm, rfl⟩)
  cont n := by unfold g; have := d.continuous_H n; fun_prop
  inj := d.g_injOn
  left := d.g_left
  right := d.g_right
  mem_disc n _ ht := d.g_mem_disc n ht
  conn n := ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected.image _
    (d.continuous_H n).continuousOn
  sub_disc n := by
    rintro _ ⟨x, hx, rfl⟩
    have := d.one_sub_ε_pos n
    rw [mem_ball_zero_iff, d.norm_H n (by linarith [hx.2.1])]
    exact hx.2.2
  disj_curve n := by
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨t, ht, hxt⟩
    have hu := d.uu_mem n ht
    have := d.H_injOn n (d.edge_mem_crect n hu)
      ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2.1.le, hx.2.2.le⟩ hxt
    have hε := d.ε_pos n
    rw [Prod.ext_iff] at this
    rcases edge_boundary hu with h | h | h
    · rw [h] at this; linarith [hx.1.1, this.1]
    · rw [h] at this; linarith [hx.1.2, this.1]
    · rw [h] at this; simp only at this; linarith [hx.2.1, this.2]
  curve_sub n := by
    rintro _ ⟨t, ht, rfl⟩
    rw [d.closure_Ω]
    exact ⟨_, d.edge_mem_crect n (d.uu_mem n ht), rfl⟩
  closure_disj := d.omega_closure_disjoint
  closure_sub n := by
    rw [d.closure_Ω]
    rintro _ ⟨x, hx, rfl⟩
    by_cases hr : x ∈ d.rect n
    · exact Or.inl (Or.inl ⟨x, hr, rfl⟩)
    rcases d.crect_sub n hx hr with h | ⟨t, ht, h⟩
    · refine Or.inr ?_
      have : x = (x.1, 1) := Prod.ext rfl h
      rw [this]; exact d.H_one n hx.1
    · exact Or.inl (Or.inr ⟨t, ht, h⟩)
  touch n := by
    refine ⟨d.c n, ?_, ?_⟩
    · have := d.α_lt_β n; rw [c_eq]; constructor <;> linarith
    · rw [d.closure_Ω]
      have := d.one_sub_ε_pos n; have := d.ε_pos n
      refine ⟨(1 / 2, 1), ⟨⟨by norm_num, by norm_num⟩, by linarith, le_rfl⟩, ?_⟩
      simp only [H, θ, vq_one, Complex.ofReal_one, one_mul]
      rw [c_eq]; ring_nf
  small δ hδ := by
    filter_upwards [d.diam_omega_tendsto δ hδ] with n hn t ht
    exact hn _ (by rw [d.closure_Ω]; exact ⟨_, d.edge_mem_crect n (d.uu_mem n ht), rfl⟩) t ht

end Intervals

/-! ### Poisson integrals: elementary facts -/

/-- The Poisson kernel `P(z, e^{iθ})` as a function of the angle. -/
noncomputable def K (z : ℂ) (θ : ℝ) : ℝ := poissonKernel 0 z (expI θ)

theorem K_eq (z : ℂ) (θ : ℝ) : K z θ = (1 - ‖z‖ ^ 2) / ‖expI θ - z‖ ^ 2 := by
  simp [K, poissonKernel, norm_expI]

theorem expI_sub_ne_zero {z : ℂ} (hz : z ∈ disc) (θ : ℝ) : expI θ - z ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [mem_ball_zero_iff, ← h, norm_expI] at hz
  exact lt_irrefl _ hz

theorem one_sub_norm_le (z : ℂ) (θ : ℝ) : 1 - ‖z‖ ≤ ‖expI θ - z‖ := by
  have := norm_sub_norm_le (expI θ) z
  rwa [norm_expI] at this

theorem K_nonneg {z : ℂ} (hz : z ∈ disc) (θ : ℝ) : 0 ≤ K z θ := by
  rw [K_eq]
  have := mem_ball_zero_iff.1 hz
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

theorem K_le {z : ℂ} (hz : z ∈ disc) (θ : ℝ) : K z θ ≤ 2 / (1 - ‖z‖) := by
  have hr := mem_ball_zero_iff.1 hz
  have h0 := norm_nonneg z
  have hD := one_sub_norm_le z θ
  have hpos : 0 < 1 - ‖z‖ := by linarith
  have hD2 : (1 - ‖z‖) ^ 2 ≤ ‖expI θ - z‖ ^ 2 := pow_le_pow_left₀ hpos.le hD 2
  rw [K_eq, div_le_div_iff₀ (by nlinarith) hpos]
  nlinarith

theorem continuous_K {z : ℂ} (hz : z ∈ disc) : Continuous (K z) := by
  have : K z = fun θ => (1 - ‖z‖ ^ 2) / ‖expI θ - z‖ ^ 2 := funext (K_eq z)
  rw [this]
  exact continuous_const.div (by fun_prop) fun θ =>
    pow_ne_zero 2 (norm_ne_zero_iff.2 (expI_sub_ne_zero hz θ))

theorem poisson_eq (φ : ℂ → ℝ) (z : ℂ) :
    poisson φ z = (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), K z θ * φ (expI θ) := by
  rw [poisson, Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    smul_eq_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  simp [circleMap, K, expI]

theorem poisson_eq' (φ : ℂ → ℝ) (z : ℂ) :
    poisson φ z = (2 * π)⁻¹ * ∫ θ in (-π)..π, K z θ * φ (expI θ) := by
  rw [poisson, Real.circleAverage_def, smul_eq_mul]
  congr 1
  have hp : Periodic (fun θ => poissonKernel 0 z (circleMap 0 1 θ) * φ (circleMap 0 1 θ))
      (2 * π) := fun θ => by simp only [periodic_circleMap 0 1 θ]
  have := hp.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at this
  rw [this]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp [circleMap, K, expI]

theorem integrableOn_K_mul {z : ℂ} (hz : z ∈ disc) {φ : ℂ → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ ∈ circle, |φ ζ| ≤ M) {s : Set ℝ} (hs : volume s < ⊤) :
    IntegrableOn (fun θ => K z θ * φ (expI θ)) s := by
  refine IntegrableOn.of_bound hs
    ((continuous_K hz).measurable.mul (hφ.comp continuous_expI.measurable)).aestronglyMeasurable
    (2 / (1 - ‖z‖) * M) (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K_nonneg hz θ)]
  exact mul_le_mul (K_le hz θ) (hM _ (expI_mem_circle θ)) (abs_nonneg _)
    (by have := mem_ball_zero_iff.1 hz; have : 0 < 1 - ‖z‖ := by linarith
        positivity)

theorem integrableOn_K {z : ℂ} (hz : z ∈ disc) {s : Set ℝ} (hs : volume s < ⊤) :
    IntegrableOn (K z) s := by
  have := integrableOn_K_mul hz (φ := fun _ => 1) measurable_const (M := 1)
    (fun _ _ => by simp) hs
  simpa using this

theorem poisson_nonneg {z : ℂ} (hz : z ∈ disc) {φ : ℂ → ℝ} (hφ : ∀ ζ, 0 ≤ φ ζ) :
    0 ≤ poisson φ z := by
  rw [poisson_eq]
  exact mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Ioc fun θ _ => mul_nonneg (K_nonneg hz θ) (hφ _))

theorem poisson_indicator_eq (z : ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    poisson (S.indicator 1) z =
      (2 * π)⁻¹ * ∫ θ in expI ⁻¹' S, K z θ ∂(volume.restrict (Ioc 0 (2 * π))) := by
  rw [poisson_eq, ← integral_indicator (measurableSet_preimage continuous_expI.measurable hS)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  by_cases h : expI θ ∈ S
  · simp [indicator, h]
  · simp [indicator, h]

/-- Countable additivity of `S ↦ P[χ_S](z)`. -/
theorem poisson_indicator_hasSum {z : ℂ} (hz : z ∈ disc) {A : ℕ → Set ℂ}
    (hm : ∀ n, MeasurableSet (A n)) (hd : Pairwise (Disjoint on A)) :
    HasSum (fun n => poisson ((A n).indicator 1) z) (poisson ((⋃ n, A n).indicator 1) z) := by
  simp_rw [poisson_indicator_eq z (hm _), poisson_indicator_eq z (MeasurableSet.iUnion hm),
    preimage_iUnion]
  refine HasSum.mul_left _ (hasSum_integral_iUnion
    (fun n => measurableSet_preimage continuous_expI.measurable (hm n))
    (fun n m hnm => (hd hnm).preimage _) ?_)
  have : Integrable (K z) (volume.restrict (Ioc 0 (2 * π))) :=
    integrableOn_K hz (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
  exact this.integrableOn

/-- Upper bound for the Poisson integral of the indicator of an arc. -/
theorem poisson_indicator_le {z : ℂ} (hz : z ∈ disc) {a b M : ℝ} (ha : -π < a) (hab : a ≤ b)
    (hb : b < π) (hM : ∀ t ∈ Icc a b, K z t ≤ M) :
    poisson ((expI '' Icc a b).indicator 1) z ≤ M * (b - a) / (2 * π) := by
  rw [poisson_eq', intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hsub : Icc a b ⊆ Ioc (-π) π := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h1 : ∫ θ in Ioc (-π) π, K z θ * (expI '' Icc a b).indicator 1 (expI θ) =
      ∫ θ in Ioc (-π) π, (Icc a b).indicator (K z) θ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    by_cases h : θ ∈ Icc a b
    · simp [indicator, h, mem_image_of_mem expI h]
    · have : expI θ ∉ expI '' Icc a b := by
        rintro ⟨t, ht, hte⟩
        exact h (expI_injOn (hsub ht) hθ hte ▸ ht)
      simp [indicator, h, this]
  rw [h1, setIntegral_indicator measurableSet_Icc, inter_eq_right.2 hsub]
  have h2 : ∫ θ in Icc a b, K z θ ≤ ∫ _ in Icc a b, M :=
    setIntegral_mono_on (integrableOn_K hz (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top))
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top.ne))
      measurableSet_Icc hM
  rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul] at h2
  rw [mul_comm, ← div_eq_mul_inv]
  gcongr
  linarith

theorem circleIntegrable_of_bounded {φ : ℂ → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ ∈ circle, |φ ζ| ≤ M) : CircleIntegrable φ 0 1 := by
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    (hφ.comp (continuous_circleMap 0 1).measurable).aestronglyMeasurable M
    (ae_of_all _ fun θ => by
      rw [Real.norm_eq_abs]; exact hM _ (circleMap_mem_sphere 0 zero_le_one θ))

/-- `fact:poisson` (i): the Poisson integral of a bounded measurable function is a bounded harmonic
function in the disc, bounded by the bound of `φ`. Proved: `P[φ] = Re (2 C[φ] - C[φ](0))`, where
`C[φ](w) = (2πi)⁻¹ ∮ (ζ - w)⁻¹ φ(ζ) dζ` is a Cauchy integral, hence analytic in the disc. -/
theorem poisson_bounded_harmonic (φ : ℂ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ ζ ∈ circle, |φ ζ| ≤ M) :
    InnerProductSpace.HarmonicOnNhd (poisson φ) disc ∧ ∀ z ∈ disc, |poisson φ z| ≤ M := by
  have hint : CircleIntegrable φ 0 1 := circleIntegrable_of_bounded hφ hM
  have hintC : CircleIntegrable (fun ζ => (φ ζ : ℂ)) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hint ⊢
    exact Complex.ofRealCLM.integrable_comp hint
  constructor
  · -- the Cauchy integral and the constant term
    set C : ℂ → ℂ := fun w => (2 * π * I)⁻¹ • ∮ z in C(0, (1 : NNReal)), (z - w)⁻¹ • (φ z : ℂ)
      with hC
    set c₀ : ℂ := (2 * π * I)⁻¹ • ∮ z in C(0, 1), z⁻¹ • (φ z : ℂ) with hc₀
    have hpow := hasFPowerSeriesOn_cauchy_integral (R := 1) hintC one_pos
    have hG : ∀ w ∈ disc, poisson φ w = (2 * C w - c₀).re := by
      intro w hw
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
      have h1 : poisson φ w = (Real.circleAverage
          (fun ζ => herglotzRieszKernel 0 w ζ • (φ ζ : ℂ)) 0 1).re := by
        rw [re_circleAverage_herglotzRieszKernel_smul hint hw, poisson]
        congr 1
        funext ζ
        simp [poissonKernel_eq_re_herglotzRieszKernel]
      rw [h1, Real.circleAverage_eq_circleIntegral one_ne_zero]
      have hne : ∀ z ∈ sphere (0 : ℂ) 1, z - w ≠ 0 := fun z hz h => by
        rw [sub_eq_zero] at h
        rw [h, mem_sphere_zero_iff_norm] at hz
        linarith
      have hne0 : ∀ z ∈ sphere (0 : ℂ) 1, z ≠ 0 := fun z hz h => by
        rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz
        exact zero_ne_one hz
      have hA : CircleIntegrable (fun z => (z - w)⁻¹ • (φ z : ℂ)) 0 1 :=
        hintC.continuousOn_smul (g := fun z => (z - w)⁻¹)
          (ContinuousOn.inv₀ (by fun_prop) fun z hz => hne z (by simpa using hz))
      have hB : CircleIntegrable (fun z => z⁻¹ • (φ z : ℂ)) 0 1 :=
        hintC.continuousOn_smul (g := fun z => z⁻¹)
          (ContinuousOn.inv₀ (by fun_prop) fun z hz => hne0 z (by simpa using hz))
      rw [circleIntegral.integral_congr zero_le_one
        (g := fun z => (2 : ℂ) • ((z - w)⁻¹ • (φ z : ℂ)) - z⁻¹ • (φ z : ℂ))]
      · have hA2 : CircleIntegrable (fun z => (2 : ℂ) • ((z - w)⁻¹ • (φ z : ℂ))) 0 1 :=
          hA.const_smul
        rw [circleIntegral.integral_sub hA2 hB,
          circleIntegral.integral_smul]
        simp only [hC, hc₀, NNReal.coe_one, smul_eq_mul]
        rw [show ∀ X Y : ℂ, (2 * π * I)⁻¹ * (2 * X - Y) =
          2 * ((2 * π * I)⁻¹ * X) - (2 * π * I)⁻¹ * Y from fun X Y => by ring]
      · intro z hz
        have h1 := hne z hz
        have h2 := hne0 z hz
        simp only [herglotzRieszKernel, sub_zero, smul_eq_mul]
        field_simp
        ring
    intro x hx
    have han : AnalyticAt ℂ (fun w => 2 * C w - c₀) x := by
      have hCx : AnalyticAt ℂ C x := hpow.analyticAt_of_mem (by
        rw [Metric.mem_eball, edist_dist, dist_zero_right]
        simpa using ENNReal.ofReal_lt_ofReal_iff'.2 ⟨mem_ball_zero_iff.1 hx, one_pos⟩)
      exact (analyticAt_const.mul hCx).sub analyticAt_const
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 han.harmonicAt_re
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw using hG w hw
  · intro z hz
    have hK : ∀ ζ ∈ sphere (0 : ℂ) |1|, 0 ≤ poissonKernel 0 z ζ := by
      intro ζ hζ
      rw [abs_one, mem_sphere_zero_iff_norm] at hζ
      have := mem_ball_zero_iff.1 hz
      simp only [poissonKernel, sub_zero, hζ]
      exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)
    have hcont : ContinuousOn (poissonKernel 0 z) (sphere (0 : ℂ) |1|) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hz)
    have hI1 : CircleIntegrable (fun ζ => poissonKernel 0 z ζ * φ ζ) 0 1 :=
      hint.continuousOn_smul hcont
    have hI2 : ∀ a : ℝ, CircleIntegrable (poissonKernel 0 z • fun _ => a) 0 1 := fun a =>
      (circleIntegrable_const a 0 1).continuousOn_smul hcont
    have hP : ∀ a : ℝ, Real.circleAverage (poissonKernel 0 z • fun _ => a) 0 1 = a := fun a =>
      (InnerProductSpace.harmonicOnNhd_const a).circleAverage_poissonKernel_smul hz
    rw [abs_le]
    constructor
    · have := Real.circleAverage_mono (hI2 (-M)) hI1 fun ζ hζ => by
        have h1 := hM ζ (by simpa using hζ)
        simp only [smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 h1).1]) (hK ζ hζ)
      rw [hP] at this
      exact this
    · have := Real.circleAverage_mono hI1 (hI2 M) fun ζ hζ => by
        have h1 := hM ζ (by simpa using hζ)
        simp only [smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 h1).2]) (hK ζ hζ)
      rw [hP] at this
      exact this

theorem norm_expI_sub_sq (t θ r : ℝ) :
    ‖expI t - (r : ℂ) * expI θ‖ ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos (θ - t) := by
  rw [TJK.norm_sq_eq_re_im]
  simp [expI, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_sub]
  linear_combination (Real.sin_sq_add_cos_sq t) + r ^ 2 * (Real.sin_sq_add_cos_sq θ)

/-! ### The functions `f_n = P[χ_{I_n}]` (`lem:ha-estimates`, analytic part) -/

namespace Intervals

variable (d : Intervals)

/-- `f_n = P[χ_n]`, the Poisson integral of the indicator of `I_n`. -/
noncomputable def fn (n : ℕ) : ℂ → ℝ := poisson ((d.I n).indicator 1)

theorem K_le_of_not_mem (n : ℕ) {z : ℂ} (hz : z ∈ disc) (hzΩ : z ∉ d.Ω n)
    (hr : 1 - d.ε n < ‖z‖) {t : ℝ} (ht : t ∈ Icc (d.α n) (d.β n)) :
    K z t ≤ 16 / 3 * √(1 - ‖z‖) := by
  set r := ‖z‖ with hrdef
  have hr1 : r < 1 := mem_ball_zero_iff.1 hz
  have h34 := d.one_sub_ε_pos n
  set θ' := toIocMod Real.two_pi_pos (t - π) (arg z) with hθ'
  have hθ'mem := toIocMod_mem_Ioc Real.two_pi_pos (t - π) (arg z)
  rw [← hθ'] at hθ'mem
  have hk := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (t - π) (arg z)
  rw [← hθ', zsmul_eq_mul] at hk
  have hz' : z = (r : ℂ) * expI θ' := by
    conv_lhs => rw [expI_arg' z]
    rw [← hk, expI_add_int_mul]
  have hv : vq r ≤ |θ' - t| := by
    by_contra h
    push Not at h
    apply hzΩ
    rw [hz']
    obtain ⟨h1, h2⟩ := abs_lt.1 h
    exact d.mem_Ω n ⟨hr, hr1⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have habs : |θ' - t| ≤ π := by
    rw [abs_le]; constructor <;> linarith [hθ'mem.1, hθ'mem.2]
  have hcos : Real.cos (θ' - t) ≤ Real.cos (vq r) := by
    rw [← Real.cos_abs]; exact Real.cos_le_cos_of_nonneg_of_le_pi (vq_nonneg r) habs hv
  have hv0 := vq_nonneg r
  have hv1 : vq r ≤ 1 := (vq_lt_one (by linarith)).le
  have hcb := Real.cos_bound (x := vq r) (by rw [abs_of_nonneg hv0]; exact hv1)
  rw [abs_of_nonneg hv0] at hcb
  have hv4 : vq r ^ 4 ≤ vq r ^ 2 := by
    have h : vq r ^ 2 ≤ 1 := by nlinarith
    calc vq r ^ 4 = vq r ^ 2 * vq r ^ 2 := by ring
      _ ≤ vq r ^ 2 * 1 := mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := mul_one _
  have hcos2 : Real.cos (vq r) ≤ 1 - vq r ^ 2 / 4 := by nlinarith [(abs_le.1 hcb).2]
  have hv2 := vq_sq (r := r)
  have hq : 0 < √(1 - r) := Real.sqrt_pos.2 (by linarith)
  have hq2 : √(1 - r) ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
  have hD : ‖expI t - z‖ ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos (θ' - t) := by
    rw [hz']; exact norm_expI_sub_sq t θ' r
  have hDlow : r * √(1 - r) / 2 ≤ ‖expI t - z‖ ^ 2 := by
    rw [hD, ← hv2]; nlinarith [sq_nonneg (1 - r)]
  have hr0 : 0 < r := by linarith
  have hDpos : 0 < ‖expI t - z‖ ^ 2 := lt_of_lt_of_le (div_pos (mul_pos hr0 hq) two_pos) hDlow
  rw [K_eq, div_le_iff₀ hDpos]
  have := mul_le_mul_of_nonneg_left hDlow (by positivity : (0 : ℝ) ≤ 16 / 3 * √(1 - r))
  nlinarith

/-- `lem:ha-estimates` (2): `f_n(z) ≤ ε_n √(1 - |z|)` for `z ∉ Ω_n`, `|z| > 1 - ε_n`. -/
theorem fn_le_eps_sqrt (n : ℕ) {z : ℂ} (hz : z ∈ disc) (hzΩ : z ∉ d.Ω n)
    (hr : 1 - d.ε n < ‖z‖) : d.fn n z ≤ d.ε n * √(1 - ‖z‖) := by
  have h := poisson_indicator_le hz (d.α_gt n) (d.α_lt_β n).le (d.β_lt n)
    (fun t ht => d.K_le_of_not_mem n hz hzΩ hr ht)
  refine h.trans ?_
  rw [d.β_sub_α]
  have hq := Real.sqrt_nonneg (1 - ‖z‖)
  have := d.ε_le_quarter n; have := d.ε_pos n
  have hpi := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  have : 16 / 3 * √(1 - ‖z‖) * (π * d.ε n ^ 2) =
      (8 / 3 * d.ε n) * (d.ε n * √(1 - ‖z‖)) * (2 * π) := by
    ring
  rw [this]
  have : 0 ≤ d.ε n * √(1 - ‖z‖) * (2 * π) := by positivity
  nlinarith

/-- `lem:ha-estimates` (1): `0 ≤ f_n ≤ ε_n` on `𝔻 \ Ω_n`. -/
theorem fn_le_eps (n : ℕ) {z : ℂ} (hz : z ∈ disc) (hzΩ : z ∉ d.Ω n) :
    0 ≤ d.fn n z ∧ d.fn n z ≤ d.ε n := by
  refine ⟨poisson_nonneg hz fun ζ => by unfold indicator; split_ifs <;> simp, ?_⟩
  have hr1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hε := d.ε_pos n
  rcases le_or_gt ‖z‖ (1 - d.ε n) with hr | hr
  · have h := poisson_indicator_le hz (d.α_gt n) (d.α_lt_β n).le (d.β_lt n)
      (fun t _ => K_le hz t)
    refine h.trans ?_
    rw [d.β_sub_α]
    have hpi := Real.pi_pos
    have h1 : 0 < 1 - ‖z‖ := by linarith
    rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ h1]
    nlinarith [mul_nonneg (mul_nonneg hε.le hpi.le) (by linarith : (0 : ℝ) ≤ 1 - ‖z‖ - d.ε n)]
  · refine (d.fn_le_eps_sqrt n hz hzΩ hr).trans ?_
    have : √(1 - ‖z‖) ≤ 1 := Real.sqrt_le_one.2 (by linarith [norm_nonneg z])
    nlinarith

/-- `lem:ha-estimates` (3): `f_n → 0` at every point of the circle, along `𝔻 \ Ω_n`. -/
theorem fn_tendsto_zero (n : ℕ) {x : ℂ} (hx : x ∈ circle) :
    Tendsto (d.fn n) (𝓝[disc \ d.Ω n] x) (𝓝 0) := by
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝[disc \ d.Ω n] x) (𝓝 1) := by
    have := (continuous_norm.tendsto x).mono_left (nhdsWithin_le_nhds (s := disc \ d.Ω n))
    rwa [mem_sphere_zero_iff_norm.1 hx] at this
  have hup : Tendsto (fun z : ℂ => d.ε n * √(1 - ‖z‖)) (𝓝[disc \ d.Ω n] x) (𝓝 0) := by
    have hc : Continuous fun s : ℝ => d.ε n * √(1 - s) := by fun_prop
    have := (hc.tendsto 1).comp hnorm
    simpa [Function.comp_def] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (d.fn_le_eps n hz.1 hz.2).1
  · filter_upwards [self_mem_nhdsWithin, hnorm.eventually (lt_mem_nhds (by linarith [d.ε_pos n] :
      1 - d.ε n < 1))] with z hz hr
    exact d.fn_le_eps_sqrt n hz.1 hz.2 hr

end Intervals

/-! ### General limits along an arc (`lem:general-limit-endpoints`) -/

/-- `lem:general-limit-endpoints`: if `u` has the general limit `c` at every point
`e^{i(t₀ + sℓ)}`, `0 < s ≤ 1` (`0 < |ℓ| < 2π`), then `u` has the asymptotic value `c` at
`e^{it₀}`. The arc is `s ↦ (1 - m(s)/2) e^{i(t₀ + sℓ)}`, where `m(s) = min(h(s), s, 1)` and
`h(s)` is the distance from `e^{i(t₀ + sℓ)}` to the set of `z ∈ 𝔻` with
`|z - e^{it₀}| ≤ |u z - c|`. -/
theorem asymptotic_at_endpoint (u : ℂ → ℝ) (c t₀ ℓ : ℝ) (hℓ : ℓ ≠ 0) (hℓ' : |ℓ| < 2 * π)
    (hu : ∀ s ∈ Ioc (0 : ℝ) 1, Tendsto u (𝓝[disc] (expI (t₀ + s * ℓ))) (𝓝 c)) :
    ∃ γ, IsArcAt disc (expI t₀) γ ∧ Tendsto u (𝓝[γ \ {expI t₀}] (expI t₀)) (𝓝 c) := by
  set ζ₀ := expI t₀ with hζ₀
  set w : ℝ → ℂ := fun s => expI (t₀ + s * ℓ) with hw
  set F : Set ℂ := {z | z ∈ disc ∧ ‖z - ζ₀‖ ≤ |u z - c|} ∪ {0} with hF
  set h : ℝ → ℝ := fun s => infDist (w s) F with hh
  set m : ℝ → ℝ := fun s => min (min (h s) s) 1 with hm
  set Z : ℝ → ℂ := fun s => ((1 - m s / 2 : ℝ) : ℂ) * w s with hZ
  have hw_cont : Continuous w := by rw [hw]; fun_prop
  have hh_cont : Continuous h := (continuous_infDist_pt F).comp hw_cont
  have hm_cont : Continuous m := (hh_cont.min continuous_id).min continuous_const
  have hZ_cont : Continuous Z := by rw [hZ]; fun_prop
  have hw_ne : ∀ s ∈ Ioc (0 : ℝ) 1, w s ≠ ζ₀ := by
    intro s hs he
    have := eq_of_expI_eq he (by
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hs.1]
      calc s * |ℓ| ≤ 1 * |ℓ| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
        _ < 2 * π := by linarith)
    have : s * ℓ = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact hs.1.ne' h0
    · exact hℓ h0
  have hpos : ∀ s ∈ Ioc (0 : ℝ) 1, 0 < h s := by
    intro s hs
    rw [hh]
    simp only
    rw [← infDist_pos_iff_notMem_closure (s := F) (x := w s) ⟨0, Or.inr rfl⟩]
    set d := ‖w s - ζ₀‖ with hd
    have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 (hw_ne s hs))
    have h1 : ∀ᶠ z in 𝓝[disc] (w s), dist (u z) c < d / 2 :=
      Metric.tendsto_nhds.1 (hu s hs) (d / 2) (by positivity)
    rw [eventually_nhdsWithin_iff] at h1
    have h2 : ∀ᶠ z in 𝓝 (w s), d / 2 < ‖z - ζ₀‖ :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt.eventually
        (lt_mem_nhds (show d / 2 < d by linarith))
    have h3 : ∀ᶠ z in 𝓝 (w s), z ≠ 0 := isOpen_ne.mem_nhds (by
      intro h0; have := norm_expI (t₀ + s * ℓ)
      rw [show expI (t₀ + s * ℓ) = w s from rfl, h0, norm_zero] at this
      exact zero_ne_one this)
    rw [mem_closure_iff_frequently, not_frequently]
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    rintro (⟨hzd, hle⟩ | hz0)
    · have := hz1 hzd
      rw [Real.dist_eq] at this
      linarith
    · exact hz3 hz0
  have hh0 : ∀ s, 0 ≤ h s := fun s => infDist_nonneg
  have hm0 : m 0 = 0 := by
    simp only [hm, min_eq_right (hh0 0)]; norm_num
  have hm_pos : ∀ s ∈ Ioc (0 : ℝ) 1, 0 < m s := fun s hs =>
    lt_min (lt_min (hpos s hs) hs.1) one_pos
  have hm_le : ∀ s, m s ≤ 1 := fun s => min_le_right _ _
  have hm_h : ∀ s, m s ≤ h s := fun s => (min_le_left _ _).trans (min_le_left _ _)
  have hm_s : ∀ s, m s ≤ s := fun s => (min_le_left _ _).trans (min_le_right _ _)
  have hm_nonneg : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ m s := fun s hs =>
    le_min (le_min (hh0 s) hs.1) zero_le_one
  have hnormZ : ∀ s, ‖Z s‖ = 1 - m s / 2 := by
    intro s
    rw [hZ]; simp only
    rw [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_of_nonneg]
    linarith [hm_le s]
  have hZ0 : Z 0 = ζ₀ := by
    show ((1 - m 0 / 2 : ℝ) : ℂ) * expI (t₀ + 0 * ℓ) = expI t₀
    rw [hm0]; simp
  let q : Path ζ₀ (Z 1) :=
    { toFun := fun t => Z t
      continuous_toFun := hZ_cont.comp continuous_subtype_val
      source' := hZ0
      target' := rfl }
  have hq : ∀ t : unitInterval, q t = Z t := fun _ => rfl
  have hq_inj : Injective q := by
    intro a b hab
    rw [hq, hq] at hab
    have hn := congrArg norm hab
    rw [hnormZ, hnormZ] at hn
    have hmab : m a = m b := by linarith
    have hne : ((1 - m b / 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (by linarith [hm_le b])
    have hwab : w a = w b := by
      rw [hZ] at hab; simp only at hab
      rw [hmab] at hab
      exact mul_left_cancel₀ hne hab
    have ha := a.2; have hb := b.2
    have := eq_of_expI_eq hwab (by
      rw [show t₀ + a * ℓ - (t₀ + b * ℓ) = (a - b) * ℓ by ring, abs_mul]
      have : |(a : ℝ) - b| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
      calc |(a : ℝ) - b| * |ℓ| ≤ 1 * |ℓ| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ < 2 * π := by linarith)
    have : ((a : ℝ) - b) * ℓ = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact Subtype.ext (by linarith)
    · exact absurd h0 hℓ
  refine ⟨range q, ⟨Z 1, ⟨q, hq_inj, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨⟨s, rfl⟩, hne⟩
    rw [hq, mem_ball_zero_iff, hnormZ]
    have hs0 : (s : ℝ) ≠ 0 := by
      intro h0
      apply hne
      rw [mem_singleton_iff, hq, h0, hZ0]
    have := hm_pos s ⟨lt_of_le_of_ne s.2.1 (Ne.symm hs0), s.2.2⟩
    linarith
  · rw [IsArc.nhdsWithin_eq hq_inj, tendsto_map'_iff]
    have hZt : Tendsto Z (𝓝[>] 0) (𝓝 ζ₀) := by
      have := (hZ_cont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [hZ0] at this
    have hdist : Tendsto (fun s => ‖Z s - ζ₀‖) (𝓝[>] 0) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hZt
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hdist
    filter_upwards [Ioc_mem_nhdsGT one_pos] with s hs
    have hext : q.extend s = Z s := by
      rw [Path.extend_apply q (Ioc_subset_Icc_self hs)]; rfl
    simp only [comp_apply, hext]
    have hms := hm_pos s hs
    have hZd : Z s ∈ disc := by rw [mem_ball_zero_iff, hnormZ]; linarith
    have hZF : Z s ∉ F := by
      intro hF'
      have h1 := infDist_le_dist_of_mem (x := w s) hF'
      have h2 : dist (w s) (Z s) = m s / 2 := by
        rw [dist_eq_norm, hZ]; simp only
        rw [show w s - ((1 - m s / 2 : ℝ) : ℂ) * w s = ((m s / 2 : ℝ) : ℂ) * w s by
          push_cast; ring, norm_mul, hw]
        simp only
        rw [norm_expI, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have := hm_h s
      rw [hh] at this; simp only at this
      linarith
    simp only [hF, mem_union, mem_ofPred_eq, not_or, not_and, not_le] at hZF
    rw [Real.norm_eq_abs]
    exact (hZF.1 hZd).le

/-- `lem:general-limit-endpoints` for an open arc `e^{i(t₀, t₁)}`: both endpoints. -/
theorem asymptotic_at_endpoints (u : ℂ → ℝ) (c t₀ t₁ : ℝ) (ht : t₀ < t₁) (ht' : t₁ - t₀ < 2 * π)
    (hu : ∀ t ∈ Ioo t₀ t₁, Tendsto u (𝓝[disc] (expI t)) (𝓝 c)) :
    (∃ γ, IsArcAt disc (expI t₀) γ ∧ Tendsto u (𝓝[γ \ {expI t₀}] (expI t₀)) (𝓝 c)) ∧
      ∃ γ, IsArcAt disc (expI t₁) γ ∧ Tendsto u (𝓝[γ \ {expI t₁}] (expI t₁)) (𝓝 c) := by
  constructor
  · refine asymptotic_at_endpoint u c t₀ ((t₁ - t₀) / 2) (by linarith) ?_ fun s hs => hu _ ?_
    · rw [abs_of_pos (by linarith)]; linarith
    · constructor <;> nlinarith [hs.1, hs.2]
  · refine asymptotic_at_endpoint u c t₁ (-((t₁ - t₀) / 2)) (by linarith) ?_ fun s hs => hu _ ?_
    · rw [abs_neg, abs_of_pos (by linarith)]; linarith
    · constructor <;> nlinarith [hs.1, hs.2]

/-! ### Accessibility (`lem:ha-lemma`) -/

namespace DomainFamily

variable {a b : ℕ → ℝ} {Ω : ℕ → Set ℂ} {g : ℕ → ℝ → ℂ}

open Classical in
/-- The Jordan curve `Γ`: `g n` on `[a n, b n]`, `e^{it}` elsewhere. -/
noncomputable def curve (a b : ℕ → ℝ) (g : ℕ → ℝ → ℂ) (t : ℝ) : ℂ :=
  if h : ∃ n, t ∈ Icc (a n) (b n) then g h.choose t else expI t

/-- The approximations `φ_p` of `Γ` using only `g 0, …, g (p-1)`. -/
noncomputable def curveP (a b : ℕ → ℝ) (g : ℕ → ℝ → ℂ) (p : ℕ) (t : ℝ) : ℂ :=
  expI t + ∑ n ∈ Finset.range p, (Icc (a n) (b n)).indicator (fun t => g n t - expI t) t

variable (hD : DomainFamily a b Ω g)
include hD

theorem unique {n m : ℕ} {t : ℝ} (hn : t ∈ Icc (a n) (b n)) (hm : t ∈ Icc (a m) (b m)) :
    n = m := by
  by_contra h
  exact disjoint_left.1 (hD.disj h) hn hm

theorem curve_eq {n : ℕ} {t : ℝ} (ht : t ∈ Icc (a n) (b n)) : curve a b g t = g n t := by
  have h : ∃ n, t ∈ Icc (a n) (b n) := ⟨n, ht⟩
  rw [curve, dif_pos h, hD.unique h.choose_spec ht]

omit hD in
theorem curve_eq' {t : ℝ} (ht : ∀ n, t ∉ Icc (a n) (b n)) : curve a b g t = expI t := by
  rw [curve, dif_neg (by push Not; exact ht)]

theorem g_norm {n : ℕ} {t : ℝ} (ht : t ∈ Icc (a n) (b n)) :
    (t = a n ∧ g n t = expI t) ∨ (t = b n ∧ g n t = expI t) ∨ g n t ∈ disc := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · exact Or.inl ⟨h.symm, by rw [← h, hD.left]⟩
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · exact Or.inr (Or.inl ⟨h', by rw [h', hD.right]⟩)
  exact Or.inr (Or.inr (hD.mem_disc n t ⟨h, h'⟩))

theorem g_eq_of_circle {n : ℕ} {t : ℝ} (ht : t ∈ Icc (a n) (b n)) (h1 : ‖g n t‖ = 1) :
    g n t = expI t := by
  rcases hD.g_norm ht with h | h | h
  · exact h.2
  · exact h.2
  · rw [mem_ball_zero_iff, h1] at h; exact absurd h (lt_irrefl _)

theorem g_norm_le {n : ℕ} {t : ℝ} (ht : t ∈ Icc (a n) (b n)) : ‖g n t‖ ≤ 1 := by
  rcases hD.g_norm ht with h | h | h
  · rw [h.2, norm_expI]
  · rw [h.2, norm_expI]
  · exact (mem_ball_zero_iff.1 h).le

theorem Icc_sub (n : ℕ) : Icc (a n) (b n) ⊆ Ioo (-π) π := fun _ ht =>
  ⟨by linarith [hD.a_gt n, ht.1], by linarith [hD.b_lt n, ht.2]⟩

theorem curveP_eq (p : ℕ) (t : ℝ) :
    (∀ n < p, t ∈ Icc (a n) (b n) → curveP a b g p t = g n t) ∧
      ((∀ n < p, t ∉ Icc (a n) (b n)) → curveP a b g p t = expI t) := by
  constructor
  · intro n hn ht
    rw [curveP, Finset.sum_eq_single n]
    · simp [indicator, ht]
    · intro m _ hmn
      have : t ∉ Icc (a m) (b m) := fun h => hmn (hD.unique h ht)
      simp [indicator, this]
    · intro h; exact absurd (Finset.mem_range.2 hn) h
  · intro h
    rw [curveP, Finset.sum_eq_zero, add_zero]
    intro m hm
    simp [indicator, h m (Finset.mem_range.1 hm)]

theorem continuous_curveP (p : ℕ) : Continuous (curveP a b g p) := by
  unfold curveP
  refine continuous_expI.add (continuous_finsetSum _ fun n _ => ?_)
  refine continuous_indicator ?_ ((hD.cont n).sub continuous_expI).continuousOn
  intro t ht
  rw [frontier_Icc (hD.lt n).le] at ht
  simp only [mem_insert_iff, mem_singleton_iff] at ht
  rcases ht with h | h
  · rw [h, hD.left, sub_self]
  · rw [h, hD.right, sub_self]

theorem continuous_curve : Continuous (curve a b g) := by
  refine TendstoUniformly.continuous (F := curveP a b g) (p := atTop) ?_
    (Frequently.of_forall hD.continuous_curveP)
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hD.small (δ / 2) (by positivity))
  filter_upwards [eventually_ge_atTop N] with p hp t
  by_cases ht : ∃ n, t ∈ Icc (a n) (b n)
  · obtain ⟨n, hn⟩ := ht
    rw [hD.curve_eq hn]
    by_cases hnp : n < p
    · rw [(hD.curveP_eq p t).1 n hnp hn, dist_self]; exact hδ
    · rw [(hD.curveP_eq p t).2 fun m hm hmt => by
        have := hD.unique hmt hn; omega, dist_eq_norm]
      have := hN n (by omega) t hn
      linarith
  · push Not at ht
    rw [curve_eq' ht, (hD.curveP_eq p t).2 fun m _ => ht m, dist_self]
    exact hδ

theorem curve_cases (t : ℝ) :
    (∃ n, t ∈ Icc (a n) (b n) ∧ curve a b g t = g n t) ∨
      ((∀ n, t ∉ Icc (a n) (b n)) ∧ curve a b g t = expI t) := by
  by_cases h : ∃ n, t ∈ Icc (a n) (b n)
  · obtain ⟨n, hn⟩ := h; exact Or.inl ⟨n, hn, hD.curve_eq hn⟩
  · push Not at h; exact Or.inr ⟨h, curve_eq' h⟩

theorem curve_pi : curve a b g π = expI π :=
  curve_eq' fun n h => by linarith [h.2, hD.b_lt n]

theorem curve_neg_pi : curve a b g (-π) = expI (-π) :=
  curve_eq' fun n h => by linarith [h.1, hD.a_gt n]

theorem curve_injOn : InjOn (curve a b g) (Ico (-π) π) := by
  intro s hs t ht hst
  have hst2 : |s - t| < 2 * π := by
    rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hts2 : |t - s| < 2 * π := by rwa [abs_sub_comm]
  rcases hD.curve_cases s with ⟨n, hn, hs'⟩ | ⟨hn, hs'⟩ <;>
  rcases hD.curve_cases t with ⟨m, hm, ht'⟩ | ⟨hm, ht'⟩
  · rw [hs', ht'] at hst
    by_cases hnm : n = m
    · subst hnm; exact hD.inj n hn hm hst
    · have h1 : g n s ∈ closure (Ω n) := hD.curve_sub n ⟨s, hn, rfl⟩
      have h2 : g m t ∈ closure (Ω m) := hD.curve_sub m ⟨t, hm, rfl⟩
      rw [hst] at h1
      exact absurd h2 (disjoint_left.1 (hD.closure_disj hnm) h1)
  · rw [hs', ht'] at hst
    have h1 : ‖g n s‖ = 1 := by rw [hst, norm_expI]
    rw [hD.g_eq_of_circle hn h1] at hst
    have := eq_of_expI_eq hst hst2
    exact absurd (this ▸ hn) (hm n)
  · rw [hs', ht'] at hst
    have h1 : ‖g m t‖ = 1 := by rw [← hst, norm_expI]
    rw [hD.g_eq_of_circle hm h1] at hst
    have := eq_of_expI_eq hst.symm hts2
    exact absurd (this ▸ hm) (hn m)
  · rw [hs', ht'] at hst; exact eq_of_expI_eq hst hst2

theorem norm_curve_le (t : ℝ) : ‖curve a b g t‖ ≤ 1 := by
  rcases hD.curve_cases t with ⟨n, hn, h⟩ | ⟨_, h⟩
  · rw [h]; exact hD.g_norm_le hn
  · rw [h, norm_expI]

theorem expI_notMem_curve {n : ℕ} {t : ℝ} (ht : t ∈ Ioo (a n) (b n)) :
    expI t ∉ curve a b g '' Icc (-π) π := by
  rintro ⟨s, hs, hse⟩
  have htI := hD.Icc_sub n (Ioo_subset_Icc_self ht)
  have hst2 : |s - t| < 2 * π := by
    rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, htI.1, htI.2]
  rcases hD.curve_cases s with ⟨m, hm, hs'⟩ | ⟨hm, hs'⟩
  · rw [hs'] at hse
    have h1 : ‖g m s‖ = 1 := by rw [hse, norm_expI]
    have hg := hD.g_eq_of_circle hm h1
    rw [hg] at hse
    have hst := eq_of_expI_eq hse hst2
    subst hst
    have hmn : m = n := hD.unique hm (Ioo_subset_Icc_self ht)
    subst hmn
    rcases hD.g_norm hm with h | h | h
    · exact absurd h.1 ht.1.ne'
    · exact absurd h.1 ht.2.ne
    · rw [mem_ball_zero_iff, h1] at h; exact lt_irrefl _ h
  · rw [hs'] at hse
    have hst := eq_of_expI_eq hse hst2
    subst hst
    exact hm n (Ioo_subset_Icc_self ht)

theorem mem_curve {ζ : ℂ} (hζ : ζ ∈ circle) (hζI : ∀ n, ζ ∉ expI '' Ioo (a n) (b n)) :
    ζ ∈ curve a b g '' Icc (-π) π := by
  have harg := Complex.arg_mem_Ioc ζ
  have hζe : expI (arg ζ) = ζ := expI_arg (mem_sphere_zero_iff_norm.1 hζ)
  refine ⟨arg ζ, ⟨harg.1.le, harg.2⟩, ?_⟩
  rcases hD.curve_cases (arg ζ) with ⟨n, hn, h⟩ | ⟨_, h⟩
  · rw [h]
    rcases eq_or_lt_of_le hn.1 with h1 | h1
    · rw [← h1, hD.left, h1, hζe]
    rcases eq_or_lt_of_le hn.2 with h2 | h2
    · rw [h2, hD.right, ← h2, hζe]
    exact absurd ⟨arg ζ, ⟨h1, h2⟩, hζe⟩ (hζI n)
  · rw [h, hζe]

theorem disjoint_curve (n : ℕ) : Disjoint (Ω n) (curve a b g '' Icc (-π) π) := by
  rw [disjoint_left]
  rintro z hz ⟨s, -, rfl⟩
  rcases hD.curve_cases s with ⟨m, hm, h⟩ | ⟨_, h⟩
  · rw [h] at hz
    by_cases hnm : n = m
    · subst hnm; exact disjoint_left.1 (hD.disj_curve n) hz ⟨s, hm, rfl⟩
    · exact disjoint_left.1 (hD.closure_disj hnm) (subset_closure hz) (hD.curve_sub m ⟨s, hm, rfl⟩)
  · rw [h] at hz
    have := hD.sub_disc n hz
    rw [mem_ball_zero_iff, norm_expI] at this
    exact lt_irrefl _ this

/-- `lem:ha-lemma`: every point of `C \ ⋃ I_n*` is accessible by a simple arc in
`𝔻 \ ⋃ Ω̄_n`. -/
theorem accessible_avoiding_domains {ζ : ℂ} (hζ : ζ ∈ circle)
    (hζI : ∀ n, ζ ∉ expI '' Ioo (a n) (b n)) :
    ∃ γ, IsArcAt (disc \ ⋃ n, closure (Ω n)) ζ γ := by
  obtain ⟨B, U, hBo, hUo, -, -, hBU, hunion, hBb, -, -, -, hacc⟩ :=
    jordan_accessible (curve a b g) hD.continuous_curve
      (by rw [hD.curve_neg_pi, hD.curve_pi, expI_neg_pi]) hD.curve_injOn
  set Γ := curve a b g '' Icc (-π) π with hΓ
  have hΓc : IsCompact Γ := isCompact_Icc.image hD.continuous_curve
  -- points outside the closed disc lie in `U`
  have hU1 : ∀ z : ℂ, 1 < ‖z‖ → z ∈ U := by
    intro z hz
    set S := (fun t : ℝ => (t : ℂ) * z) '' Ici 1 with hS
    have hSc : IsPreconnected S :=
      isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * z).continuousOn
    have hSΓ : S ⊆ B ∪ U := by
      rintro _ ⟨t, ht, rfl⟩
      rw [hunion]
      rintro ⟨s, -, hse⟩
      have := hD.norm_curve_le s
      have ht1 : (1 : ℝ) ≤ t := ht
      rw [hse, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at this
      nlinarith
    rcases hSc.subset_or_subset hBo hUo hBU hSΓ with h | h
    · exfalso
      obtain ⟨R, hR⟩ := hBb.subset_closedBall 0
      have hm : (((|R| + 1 : ℝ)) : ℂ) * z ∈ B := h ⟨|R| + 1, by
        show (1 : ℝ) ≤ |R| + 1; linarith [abs_nonneg R], rfl⟩
      have := hR hm
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)] at this
      nlinarith [le_abs_self R, abs_nonneg R]
    · exact h ⟨1, show (1 : ℝ) ≤ 1 from le_rfl, by simp⟩
  -- points of the open arcs `I_n*` lie in `U`
  have hU3 : ∀ n, ∀ t ∈ Ioo (a n) (b n), expI t ∈ U := by
    intro n t ht
    have hnot := hD.expI_notMem_curve ht
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hΓc.isClosed.isOpen_compl (expI t) hnot
    have hballBU : ball (expI t) ρ ⊆ U ∪ B := by
      rw [union_comm, hunion]; exact hball
    have hz' : ((1 + ρ / 2 : ℝ) : ℂ) * expI t ∈ ball (expI t) ρ ∩ U := by
      constructor
      · rw [mem_ball, dist_eq_norm, show ((1 + ρ / 2 : ℝ) : ℂ) * expI t - expI t =
          ((ρ / 2 : ℝ) : ℂ) * expI t by push_cast; ring, norm_mul, norm_expI, mul_one,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      · apply hU1
        rw [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
    exact IsPreconnected.subset_left_of_subset_union hUo hBo hBU.symm hballBU ⟨_, hz'⟩
      (convex_ball _ _).isPreconnected (mem_ball_self hρ)
  -- the domains `Ω_n` lie in `U`
  have hU4 : ∀ n, Ω n ⊆ U := by
    intro n
    obtain ⟨t, ht, hcl⟩ := hD.touch n
    have hne : (Ω n ∩ U).Nonempty := by
      have := _root_.mem_closure_iff.1 hcl U hUo (hU3 n t ht)
      rwa [inter_comm] at this
    refine IsPreconnected.subset_left_of_subset_union hUo hBo hBU.symm ?_ hne (hD.conn n)
    intro z hz
    have hzΓ : z ∉ Γ := disjoint_left.1 (hD.disjoint_curve n) hz
    have : z ∈ B ∪ U := by rw [hunion]; exact hzΓ
    rcases this with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- hence `B ⊆ 𝔻 \ ⋃ Ω̄_n`
  have hB : B ⊆ disc \ ⋃ n, closure (Ω n) := by
    intro z hz
    have hzU : z ∉ U := disjoint_left.1 hBU hz
    have hzΓ : z ∉ Γ := by
      have : z ∈ B ∪ U := Or.inl hz
      rw [hunion] at this; exact this
    have hzd : z ∈ disc := by
      rw [mem_ball_zero_iff]
      rcases lt_trichotomy ‖z‖ 1 with h | h | h
      · exact h
      · exfalso
        have hzc : z ∈ circle := mem_sphere_zero_iff_norm.2 h
        by_cases hI : ∃ n, z ∈ expI '' Ioo (a n) (b n)
        · obtain ⟨n, t, ht, rfl⟩ := hI; exact hzU (hU3 n t ht)
        · push Not at hI; exact hzΓ (hD.mem_curve hzc hI)
      · exact absurd (hU1 z h) hzU
    refine ⟨hzd, ?_⟩
    simp only [mem_iUnion, not_exists]
    intro n hcl
    rcases hD.closure_sub n hcl with (h | h) | h
    · exact hzU (hU4 n h)
    · obtain ⟨t, ht, rfl⟩ := h
      have htI := hD.Icc_sub n ht
      exact hzΓ ⟨t, ⟨htI.1.le, htI.2.le⟩, hD.curve_eq ht⟩
    · obtain ⟨t, -, rfl⟩ := h
      rw [mem_ball_zero_iff, norm_expI] at hzd
      exact lt_irrefl _ hzd
  obtain ⟨γ, b', harc, hγ⟩ := hacc ζ (hD.mem_curve hζ hζI)
  exact ⟨γ, b', harc, hγ.trans hB⟩

end DomainFamily

/-! ### Ingredients of the example (`thm:ha-example`) -/

theorem arg_expI {t : ℝ} (ht : t ∈ Ioc (-π) π) : arg (expI t) = t := by
  rw [expI, Complex.arg_exp_mul_I, toIocMod_eq_self]
  rwa [show -π + 2 * π = π by ring]

namespace Intervals

variable (d : Intervals)

theorem measurableSet_I (n : ℕ) : MeasurableSet (d.I n) :=
  (isCompact_Icc.image continuous_expI).isClosed.measurableSet

theorem I_disjoint : Pairwise (Disjoint on d.I) := by
  intro n m hnm
  rw [Function.onFun, disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
  have := expI_injOn (Ioo_subset_Ioc_self (d.omega_jordan.Icc_sub m ht))
    (Ioo_subset_Ioc_self (d.omega_jordan.Icc_sub n hs)) hts
  exact disjoint_left.1 (d.omega_jordan.disj hnm) hs (this ▸ ht)

/-- The example `f = P[χ]`, `χ` the indicator of `⋃ I_n`. -/
noncomputable def f : ℂ → ℝ := poisson ((⋃ n, d.I n).indicator 1)

theorem f_hasSum {z : ℂ} (hz : z ∈ disc) : HasSum (fun n => d.fn n z) (d.f z) :=
  poisson_indicator_hasSum hz d.measurableSet_I d.I_disjoint

theorem measurable_χ : Measurable ((⋃ n, d.I n).indicator (1 : ℂ → ℝ)) :=
  measurable_const.indicator (MeasurableSet.iUnion d.measurableSet_I)

theorem abs_χ_le (ζ : ℂ) : |(⋃ n, d.I n).indicator (1 : ℂ → ℝ) ζ| ≤ 1 := by
  unfold indicator; split_ifs <;> simp

theorem f_harmonic : InnerProductSpace.HarmonicOnNhd d.f disc ∧ ∀ z ∈ disc, |d.f z| ≤ 1 :=
  poisson_bounded_harmonic _ d.measurable_χ 1 fun ζ _ => d.abs_χ_le ζ

/-- `f` has the general limit `1` at the points of the open arcs `I_n*` (`fact:poisson` (ii)). -/
theorem f_tendsto_one {n : ℕ} {t : ℝ} (ht : t ∈ Ioo (d.α n) (d.β n)) :
    Tendsto d.f (𝓝[disc] (expI t)) (𝓝 1) := by
  have htI : t ∈ Ioc (-π) π := ⟨by linarith [d.α_gt n, ht.1], by linarith [d.β_lt n, ht.2]⟩
  have hev : ∀ᶠ z in 𝓝[circle] (expI t), z ∈ d.I n := by
    have hslit : expI t ∈ slitPlane := by
      rw [mem_slitPlane_iff_arg, arg_expI htI]
      refine ⟨by linarith [d.β_lt n, ht.2], fun h => ?_⟩
      have := norm_expI t
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hc := (Complex.continuousAt_arg hslit).tendsto
    rw [arg_expI htI] at hc
    have := hc.eventually (Ioo_mem_nhds ht.1 ht.2)
    filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with z hz hzc
    show z ∈ expI '' Icc (d.α n) (d.β n)
    exact ⟨arg z, Ioo_subset_Icc_self hz, expI_arg (mem_sphere_zero_iff_norm.1 hzc)⟩
  have h1 : (⋃ n, d.I n).indicator (1 : ℂ → ℝ) (expI t) = 1 :=
    indicator_of_mem (mem_iUnion.2 ⟨n, show expI t ∈ expI '' Icc (d.α n) (d.β n) from
      ⟨t, Ioo_subset_Icc_self ht, rfl⟩⟩) _
  have hc : ContinuousWithinAt ((⋃ n, d.I n).indicator (1 : ℂ → ℝ)) (circle ∩ circle)
      (expI t) := by
    rw [inter_self, ContinuousWithinAt, h1]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with z hz
    exact (indicator_of_mem (mem_iUnion.2 ⟨n, hz⟩) (1 : ℂ → ℝ)).symm
  have := poisson_tendsto_of_continuousAt _ (circleIntegrable_of_bounded d.measurable_χ
    fun ζ _ => d.abs_χ_le ζ) circle (ae_of_all _ fun θ => by simp [circleMap])
    ⟨expI_mem_circle t, expI_mem_circle t⟩ hc
  rwa [h1] at this

/-- Along an arc at a point of `C` avoiding all `Ω_n`, `f → 0` (by (1), (3) and I). -/
theorem f_tendsto_zero_of_arc {ζ : ℂ} {γ : Set ℂ} (hγ : IsArcAt (disc \ ⋃ n, closure (d.Ω n)) ζ γ)
    (hζ : ζ ∈ circle) : Tendsto d.f (𝓝[γ \ {ζ}] ζ) (𝓝 0) := by
  obtain ⟨_, _, hsub⟩ := hγ
  have hL : ∀ n, 𝓝[γ \ {ζ}] ζ ≤ 𝓝[disc \ d.Ω n] ζ := fun n =>
    nhdsWithin_mono _ (hsub.trans fun z hz =>
      ⟨hz.1, fun h => hz.2 (mem_iUnion.2 ⟨n, subset_closure h⟩)⟩)
  have hfn : ∀ n, Tendsto (d.fn n) (𝓝[γ \ {ζ}] ζ) (𝓝 0) := fun n =>
    (d.fn_tendsto_zero n hζ).mono_left (hL n)
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (half_pos hη) (by norm_num : (1 / 2 : ℝ) < 1)
  have hsum : Tendsto (fun z => ∑ n ∈ Finset.range m, d.fn n z) (𝓝[γ \ {ζ}] ζ) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range m) fun n _ => hfn n
    simpa using this
  filter_upwards [hsum.eventually (gt_mem_nhds (half_pos hη)), self_mem_nhdsWithin]
    with z hz1 hz2
  have hz := hsub hz2
  have hzΩ : ∀ n, z ∉ d.Ω n := fun n h => hz.2 (mem_iUnion.2 ⟨n, subset_closure h⟩)
  have hS := d.f_hasSum hz.1
  have hb : ∀ n, 0 ≤ d.fn n z ∧ d.fn n z ≤ d.ε n := fun n => d.fn_le_eps n hz.1 (hzΩ n)
  rw [← hS.tsum_eq, ← hS.summable.sum_add_tsum_nat_add m]
  have htail : ∑' i, d.fn (i + m) z ≤ (1 / 2) ^ m := by
    have hg : HasSum (fun i : ℕ => (1 / 2 : ℝ) ^ (m + 2) * (1 / 2) ^ i) ((1 / 2) ^ (m + 2) * 2) :=
      hasSum_geometric_two.mul_left _
    have hf : HasSum (fun i => d.fn (i + m) z) (∑' i, d.fn (i + m) z) :=
      ((summable_nat_add_iff m).2 hS.summable).hasSum
    refine (hasSum_le (fun i => ?_) hf hg).trans ?_
    · refine (hb (i + m)).2.trans ((d.ε_le (i + m)).trans (le_of_eq ?_))
      ring
    · rw [pow_add]; norm_num
      have : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
      nlinarith
  have htail0 : 0 ≤ ∑' i, d.fn (i + m) z := tsum_nonneg fun i => (hb _).1
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range m, d.fn i z :=
    Finset.sum_nonneg fun i _ => (hb i).1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
  linarith

/-- If the intervals are dense, `φ = 0` at the points `e^{iα_n}` and `φ = 1` at the points
`e^{iβ_n}`, then `φ|_C` is not of Baire class one. -/
theorem not_isBaireOne
    (hden : ∀ x y, -π ≤ x → x < y → y ≤ π → ∃ k, ∃ s ∈ Icc (d.α k) (d.β k), x < s ∧ s < y)
    (φ : ℂ → ℝ) (hA : ∀ n, φ (expI (d.α n)) = 0) (hB : ∀ n, φ (expI (d.β n)) = 1) :
    ¬ IsBaireOne (circle.restrict φ) := by
  intro hf
  have hD := d.omega_jordan
  set A := range fun n => expI (d.α n) with hAdef
  set B := range fun n => expI (d.β n) with hBdef
  have hBA : A ⊆ closure B := by
    rintro _ ⟨n, rfl⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hδ : 0 < min ε (d.α n + π) := lt_min hε (by linarith [d.α_gt n])
    obtain ⟨k, s, hs, hs1, hs2⟩ := hden (d.α n - min ε (d.α n + π)) (d.α n)
      (by linarith [min_le_right ε (d.α n + π)]) (by linarith)
      (by linarith [d.α_lt_β n, d.β_lt n])
    have hβk : d.β k < d.α n := by
      by_contra hcon
      push Not at hcon
      have : k = n := hD.unique ⟨hs.1.trans hs2.le, hcon⟩ ⟨le_rfl, (d.α_lt_β n).le⟩
      subst this
      linarith [hs.1]
    refine ⟨expI (d.β k), ⟨k, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    refine (norm_expI_sub_le (d.β k) (d.α n)).trans_lt ?_
    rw [abs_of_pos (by linarith)]
    linarith [hs.2, min_le_left ε (d.α n + π)]
  have hAB : B ⊆ closure A := by
    rintro _ ⟨n, rfl⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hδ : 0 < min ε (π - d.β n) := lt_min hε (by linarith [d.β_lt n])
    obtain ⟨k, s, hs, hs1, hs2⟩ := hden (d.β n) (d.β n + min ε (π - d.β n))
      (by linarith [d.α_lt_β n, d.α_gt n]) (by linarith)
      (by linarith [min_le_right ε (π - d.β n)])
    have hαk : d.β n < d.α k := by
      by_contra hcon
      push Not at hcon
      have : k = n := hD.unique ⟨hcon, hs1.le.trans hs.2⟩ ⟨(d.α_lt_β n).le, le_rfl⟩
      subst this
      linarith [hs.2]
    refine ⟨expI (d.α k), ⟨k, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    refine (norm_expI_sub_le (d.α k) (d.β n)).trans_lt ?_
    rw [abs_of_neg (by linarith)]
    linarith [hs.1, min_le_left ε (π - d.β n)]
  set P := closure (A ∪ B) with hP
  have hcirc : A ∪ B ⊆ circle :=
    union_subset (range_subset_iff.2 fun n => expI_mem_circle _)
      (range_subset_iff.2 fun n => expI_mem_circle _)
  have hPcirc : P ⊆ circle := closure_minimal hcirc isClosed_sphere
  have hPc : IsCompact P := (isCompact_sphere (0 : ℂ) 1).of_isClosed_subset isClosed_closure hPcirc
  have : CompactSpace P := isCompact_iff_compactSpace.1 hPc
  have : Nonempty P := ⟨⟨expI (d.α 0), subset_closure (Or.inl ⟨0, rfl⟩)⟩⟩
  have hPA : P ⊆ closure A := closure_minimal
    (union_subset subset_closure hAB) isClosed_closure
  have hPB : P ⊆ closure B := closure_minimal
    (union_subset hBA subset_closure) isClosed_closure
  let ι : P → circle := fun x => ⟨x.1, hPcirc x.2⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  obtain ⟨x, hx⟩ := (hf.comp_continuous hι).exists_continuousAt
  rw [Metric.continuousAt_iff] at hx
  obtain ⟨δ, hδ, hδx⟩ := hx (1 / 2) (by norm_num)
  obtain ⟨a, ha, hda⟩ := Metric.mem_closure_iff.1 (hPA x.2) δ hδ
  obtain ⟨b, hb, hdb⟩ := Metric.mem_closure_iff.1 (hPB x.2) δ hδ
  have h1 := hδx (x := ⟨a, subset_closure (Or.inl ha)⟩)
    (by rw [Subtype.dist_eq, dist_comm]; exact hda)
  have h2 := hδx (x := ⟨b, subset_closure (Or.inr hb)⟩)
    (by rw [Subtype.dist_eq, dist_comm]; exact hdb)
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  change dist (φ (expI (d.α n))) (φ x.1) < 1 / 2 at h1
  change dist (φ (expI (d.β m))) (φ x.1) < 1 / 2 at h2
  rw [hA, Real.dist_eq] at h1
  rw [hB, Real.dist_eq] at h2
  linarith [abs_lt.1 h1, abs_lt.1 h2]

end Intervals

end TJK.Harmonic
