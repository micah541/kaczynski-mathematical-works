import Mathlib
import TJK.Defs
import TJK.Plane.Arc

/-!
# The crosscut theorem (`fact:crosscut`), towards a proof

Goal: `crosscut_theorem'`, with exactly the statement of `TJK.crosscut_theorem` in
`TJK/Plane/Basic.lean`. This file must not import `TJK.Plane.Basic` (Basic will import it), so it
uses local copies `expI'`, `circleArc'` of `TJK.expI`, `TJK.circleArc` with *identical* bodies;
the two statements are therefore definitionally equal and Basic can close
`crosscut_theorem` by `exact JordanCrosscut.crosscut_theorem' hℓ hℓ' hσ hσD`.

## Route: Eilenberg's criterion via continuous logarithms

Everything is phrased with `HasLogOn g K` ("`g` has a continuous logarithm on `K`"); no winding
numbers, no homology, no Brouwer. The only deep Mathlib input is homotopy lifting for the covering
map `exp : ℂ → ℂ \ {0}` (`IsCoveringMap.liftHomotopy`, `Complex.isCoveringMap_exp`) and continuous
logarithms on simply connected open sets (`Complex.exists_continuousOn_eqOn_exp_comp`).

Analytic core (§1):
* `HasLogOn.of_homotopy`: logarithms persist along homotopies through nonvanishing maps;
* `not_hasLogOn_sub_sphere`: `w ↦ w - c` has no logarithm on a circle around `c`;
* `admitsLogs_of_isArc`: every nonvanishing continuous function on an arc has a logarithm;
* `HasLogOn.union_of_inter_eq_singleton`: gluing;
* `mem_connectedComponentIn_of_hasLogOn` (Eilenberg): if `(w - z)/(w - z')` has a logarithm on a
  compact `K`, then `z, z'` lie in the same component of `Kᶜ` (Tietze + global logarithm on `ℂ`).

Topological consequences (§2): an arc does not separate the plane; `𝔻` minus two disjoint arcs,
each ending on `C`, is connected.

The crosscut (§3), with `a = e^{iθ}`, `b = e^{i(θ+ℓ)}`, `Aᵢ` the closed and `Aᵢ°` the open arcs:
* (Q) all points of `𝔻` near `A₁°` lie in one component `W₁` of `𝔻 \ σ`; similarly `W₂` for `A₂°`;
* (P1) every component of `𝔻 \ σ` has a point of `C \ {a, b}` in its closure (otherwise it would
  be clopen in `ℂ \ σ`, which is connected) — so every component is `W₁` or `W₂`;
* (P3) `W₁ ≠ W₂`: otherwise a point `z ∈ W₁` and a point `z'` outside `𝔻̄` would be joined in
  `ℂ \ (σ ∪ A₁)` and in `ℂ \ (σ ∪ A₂)`, so `(w - z)/(w - z')` would have logarithms on both, which
  glue along the connected `σ` to a logarithm on `C`: impossible as `|z| < 1 < |z'|`;
* (P4) `σ ⊆ closure Wᵢ`: if `p ∈ σ°` were not in `closure W₁`, removing a small open subarc
  around `p` from `σ` leaves two arcs `β₁ ∋ a`, `β₂ ∋ b`; `W₁` would be clopen in the connected set
  `𝔻 \ (β₁ ∪ β₂)`, hence contain `W₂`;
* the frontier description then follows (`frontier_component_eq`).
-/

namespace TJK

namespace JordanCrosscut

open _root_.Set Filter Topology Metric Function Complex

open scoped Real

/-- Local copy of `TJK.expI` (identical body). -/
noncomputable def expI' (t : ℝ) : ℂ := Complex.exp (t * I)

/-- Local copy of `TJK.circleArc` (identical body). -/
def circleArc' (θ ℓ : ℝ) : Set ℂ := expI' '' Icc θ (θ + ℓ)

/-- Local copy of `TJK.circleArcOpen` (identical body). -/
def circleArcOpen' (θ ℓ : ℝ) : Set ℂ := expI' '' Ioo θ (θ + ℓ)

/-! ## §0. Small facts on arcs and on the circle -/

section Basics

theorem arc_left_mem {γ : Set ℂ} {a b : ℂ} (h : IsArc γ a b) : a ∈ γ := by
  obtain ⟨p, -, rfl⟩ := h; exact ⟨0, p.source⟩

theorem arc_right_mem {γ : Set ℂ} {a b : ℂ} (h : IsArc γ a b) : b ∈ γ := by
  obtain ⟨p, -, rfl⟩ := h; exact ⟨1, p.target⟩

theorem arc_isCompact {γ : Set ℂ} {a b : ℂ} (h : IsArc γ a b) : IsCompact γ := by
  obtain ⟨p, -, rfl⟩ := h; exact isCompact_range p.continuous

theorem expI'_mem_circle (t : ℝ) : expI' t ∈ circle := by
  rw [mem_sphere_zero_iff_norm, expI', Complex.norm_exp_ofReal_mul_I]

theorem circleArc'_subset_circle (θ ℓ : ℝ) : circleArc' θ ℓ ⊆ circle := by
  rintro _ ⟨t, -, rfl⟩; exact expI'_mem_circle t

theorem circleArcOpen'_subset (θ ℓ : ℝ) : circleArcOpen' θ ℓ ⊆ circleArc' θ ℓ :=
  image_mono Ioo_subset_Icc_self

theorem expI'_add_two_pi (t : ℝ) : expI' (t + 2 * π) = expI' t := by
  rw [expI', expI', show ((t + 2 * π : ℝ) : ℂ) * I = t * I + 2 * π * I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem expI'_eq_expI' {s t : ℝ} (h : expI' s = expI' t) : ∃ n : ℤ, s = t + n * (2 * π) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simpa using this

theorem expI'_add_int_mul (t : ℝ) (k : ℤ) : expI' (t + k * (2 * π)) = expI' t := by
  rw [expI', expI', show ((t + k * (2 * π) : ℝ) : ℂ) * I = t * I + k * (2 * π * I) by
    push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem exists_expI'_Ico (θ : ℝ) {w : ℂ} (hw : w ∈ circle) :
    ∃ t ∈ Ico θ (θ + 2 * π), expI' t = w := by
  have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 hw
  have harg : expI' (arg w) = w := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rwa [hw1, ofReal_one, one_mul] at this
  have hk := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos θ (arg w)
  rw [zsmul_eq_mul] at hk
  refine ⟨toIcoMod Real.two_pi_pos θ (arg w), toIcoMod_mem_Ico _ _ _, ?_⟩
  calc expI' (toIcoMod Real.two_pi_pos θ (arg w))
      = expI' (toIcoMod Real.two_pi_pos θ (arg w) +
          (toIcoDiv Real.two_pi_pos θ (arg w) : ℝ) * (2 * π)) := (expI'_add_int_mul _ _).symm
    _ = expI' (arg w) := by rw [hk]
    _ = w := harg

/-- The endpoints of an open arc of length `≤ 2π` are not on it. -/
theorem endpoints_not_mem_circleArcOpen' {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ ≤ 2 * π) :
    expI' θ ∉ circleArcOpen' θ ℓ ∧ expI' (θ + ℓ) ∉ circleArcOpen' θ ℓ := by
  have key : ∀ u, (u = θ ∨ u = θ + ℓ) → expI' u ∉ circleArcOpen' θ ℓ := by
    rintro u hu ⟨t, ht, htu⟩
    obtain ⟨n, hn⟩ := expI'_eq_expI' htu
    have hπ := Real.pi_pos
    rcases hu with rfl | rfl
    · have h1 : (0 : ℝ) < n * (2 * π) := by linarith [ht.1]
      have h2 : (n : ℝ) * (2 * π) < 2 * π := by linarith [ht.2]
      have h1' : (0 : ℝ) < n := by nlinarith
      have h2' : (n : ℝ) < 1 := by nlinarith
      have : (0 : ℤ) < n := by exact_mod_cast h1'
      have : n < (1 : ℤ) := by exact_mod_cast h2'
      omega
    · have h1 : (-2 * π : ℝ) < n * (2 * π) := by linarith [ht.1]
      have h2 : (n : ℝ) * (2 * π) < 0 := by linarith [ht.2]
      have h1' : (-1 : ℝ) < n := by nlinarith
      have h2' : (n : ℝ) < 0 := by nlinarith
      have : (-1 : ℤ) < n := by exact_mod_cast h1'
      have : n < (0 : ℤ) := by exact_mod_cast h2'
      omega
  exact ⟨key θ (Or.inl rfl), key (θ + ℓ) (Or.inr rfl)⟩

/-- `C \ {a, b} ⊆ A₁° ∪ A₂°`. -/
theorem circle_diff_subset {θ ℓ : ℝ} (_hℓ : 0 < ℓ) (_hℓ' : ℓ < 2 * π) :
    circle \ {expI' θ, expI' (θ + ℓ)} ⊆
      circleArcOpen' θ ℓ ∪ circleArcOpen' (θ + ℓ) (2 * π - ℓ) := by
  rintro w ⟨hw, hwab⟩
  obtain ⟨t, ht, rfl⟩ := exists_expI'_Ico θ hw
  rcases ht.1.eq_or_lt with h | h
  · exact absurd (by rw [← h]; exact Or.inl rfl) hwab
  rcases lt_trichotomy t (θ + ℓ) with h' | h' | h'
  · exact Or.inl ⟨t, ⟨h, h'⟩, rfl⟩
  · exact absurd (by rw [h']; exact Or.inr rfl) hwab
  · exact Or.inr ⟨t, ⟨h', by linarith [ht.2]⟩, rfl⟩

/-- A closed arc is in the closure of the open one. -/
theorem circleArc'_subset_closure {θ ℓ : ℝ} (hℓ : 0 < ℓ) :
    circleArc' θ ℓ ⊆ closure (circleArcOpen' θ ℓ) := by
  have hc : Continuous expI' := by unfold expI'; fun_prop
  rw [circleArc', circleArcOpen', ← closure_Ioo (by linarith : θ ≠ θ + ℓ)]
  exact image_closure_subset_closure_image hc

/-- A point of `C` is a limit of points of `𝔻` in any ball around it. -/
theorem mem_closure_ball_inter_disc {p : ℂ} (hp : p ∈ circle) {r : ℝ} (hr : 0 < r) :
    p ∈ closure (ball p r ∩ disc) := by
  have hp1 : ‖p‖ = 1 := mem_sphere_zero_iff_norm.1 hp
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min ε (min r 1) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε := by
    have := min_le_left ε (min r 1); linarith
  have hδr : δ < r := by
    have := min_le_left r 1; have := min_le_right ε (min r 1); linarith
  have hδ1 : δ < 1 := by
    have := min_le_right r 1; have := min_le_right ε (min r 1); linarith
  have hdist : dist p ((1 - δ : ℝ) • p) = δ := by
    rw [dist_eq_norm, show p - (1 - δ : ℝ) • p = (δ : ℝ) • p by
      rw [sub_smul, one_smul]; abel, norm_smul, hp1, mul_one, Real.norm_of_nonneg hδ0.le]
  refine ⟨(1 - δ : ℝ) • p, ⟨?_, ?_⟩, by rw [hdist]; exact hδε⟩
  · rw [mem_ball, dist_comm, hdist]; exact hδr
  · rw [mem_ball_zero_iff, norm_smul, hp1, mul_one, Real.norm_of_nonneg (by linarith)]
    linarith

end Basics

/-! ## §1. Continuous logarithms -/

section Log

/-- `g` has a continuous logarithm on `K`. -/
def HasLogOn (g : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∃ f : ℂ → ℂ, ContinuousOn f K ∧ ∀ w ∈ K, exp (f w) = g w

/-- Every continuous nonvanishing function on `K` has a continuous logarithm on `K`. -/
def AdmitsLogs (K : Set ℂ) : Prop :=
  ∀ g : ℂ → ℂ, ContinuousOn g K → (∀ w ∈ K, g w ≠ 0) → HasLogOn g K

theorem HasLogOn.mono {g : ℂ → ℂ} {K L : Set ℂ} (h : HasLogOn g K) (hLK : L ⊆ K) :
    HasLogOn g L := by
  obtain ⟨f, hf, hfg⟩ := h
  exact ⟨f, hf.mono hLK, fun w hw => hfg w (hLK hw)⟩

theorem HasLogOn.congr {g g' : ℂ → ℂ} {K : Set ℂ} (h : HasLogOn g K) (hgg' : EqOn g g' K) :
    HasLogOn g' K := by
  obtain ⟨f, hf, hfg⟩ := h
  exact ⟨f, hf, fun w hw => (hfg w hw).trans (hgg' hw)⟩

theorem HasLogOn.mul {g h : ℂ → ℂ} {K : Set ℂ} (hg : HasLogOn g K) (hh : HasLogOn h K) :
    HasLogOn (fun w => g w * h w) K := by
  obtain ⟨f, hf, hfg⟩ := hg
  obtain ⟨k, hk, hkh⟩ := hh
  exact ⟨fun w => f w + k w, hf.add hk, fun w hw => by rw [exp_add, hfg w hw, hkh w hw]⟩

theorem HasLogOn.inv {g : ℂ → ℂ} {K : Set ℂ} (hg : HasLogOn g K) :
    HasLogOn (fun w => (g w)⁻¹) K := by
  obtain ⟨f, hf, hfg⟩ := hg
  exact ⟨fun w => -f w, hf.neg, fun w hw => by rw [exp_neg, hfg w hw]⟩

theorem hasLogOn_const {c : ℂ} (hc : c ≠ 0) (K : Set ℂ) : HasLogOn (fun _ => c) K :=
  ⟨fun _ => log c, continuousOn_const, fun _ _ => exp_log hc⟩

theorem hasLogOn_of_mem_slitPlane {g : ℂ → ℂ} {K : Set ℂ} (hg : ContinuousOn g K)
    (hK : ∀ w ∈ K, g w ∈ slitPlane) : HasLogOn g K :=
  ⟨fun w => log (g w), hg.clog hK, fun w hw => exp_log (slitPlane_ne_zero (hK w hw))⟩

/-- Homotopy lifting through `exp`: a logarithm of `H 0` on `K` deforms to one of `H 1` along a
homotopy through nonvanishing maps. Proof: `IsCoveringMap.liftHomotopy` for
`Complex.isCoveringMap_exp`, with `A = K` (subtype), then extend the lift at time `1` by `0` off
`K` (`continuousOn_iff_continuous_restrict`). Estimate: ~0.5 session. -/
theorem HasLogOn.of_homotopy {K : Set ℂ} {H : ℝ → ℂ → ℂ}
    (hH : ContinuousOn (fun x : ℝ × ℂ => H x.1 x.2) (Icc 0 1 ×ˢ K))
    (hH0 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ w ∈ K, H s w ≠ 0) (h0 : HasLogOn (H 0) K) :
    HasLogOn (H 1) K := by
  sorry

/-- `w ↦ w - c` has no continuous logarithm on a circle centred at `c`. Proof: with
`g(t) = f(c + r e^{it}) - log r - it`, `exp ∘ g = 1`, so `g` is constant on `[0, 2π]` (connected,
values in `2πiℤ`), but `g(2π) = g(0) - 2πi`. Estimate: ~0.5 session. -/
theorem not_hasLogOn_sub_sphere (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ¬ HasLogOn (fun w => w - c) (sphere c r) := by
  sorry

/-- Every continuous nonvanishing function on an arc has a continuous logarithm. Proof: the
parametrization `p : [0,1] → σ` is a homeomorphism; contract along `H s w = g (p (s · p⁻¹ w))`
(`HasLogOn.of_homotopy` from a constant), or lift `g ∘ p` directly with
`IsCoveringMap.exists_path_lifts`. Estimate: ~0.5 session. -/
theorem admitsLogs_of_isArc {σ : Set ℂ} {a b : ℂ} (hσ : IsArc σ a b) : AdmitsLogs σ := by
  sorry

/-- Same for the image of a compact interval under a map continuous and injective on it (the
subarcs of an arc used in (P4)). Estimate: shares the proof of `admitsLogs_of_isArc`. -/
theorem admitsLogs_image_Icc {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContinuousOn γ (Icc s t))
    (hinj : InjOn γ (Icc s t)) : AdmitsLogs (γ '' Icc s t) := by
  sorry

/-- Gluing logarithms across a single common point. -/
theorem HasLogOn.union_of_inter_eq_singleton {g : ℂ → ℂ} {K L : Set ℂ} {p : ℂ}
    (hK : IsClosed K) (hL : IsClosed L) (hKL : K ∩ L = {p}) (h₁ : HasLogOn g K)
    (h₂ : HasLogOn g L) : HasLogOn g (K ∪ L) := by
  classical
  obtain ⟨f₁, hf₁, hfg₁⟩ := h₁
  obtain ⟨f₂, hf₂, hfg₂⟩ := h₂
  have hpK : p ∈ K := (hKL.symm ▸ mem_singleton p : p ∈ K ∩ L).1
  have hpL : p ∈ L := (hKL.symm ▸ mem_singleton p : p ∈ K ∩ L).2
  set c := f₁ p - f₂ p
  have hc : exp c = 1 := by
    have h0 : g p ≠ 0 := by rw [← hfg₁ p hpK]; exact exp_ne_zero _
    rw [exp_sub, hfg₁ p hpK, hfg₂ p hpL, div_self h0]
  set F : ℂ → ℂ := fun w => if w ∈ K then f₁ w else f₂ w + c
  have hFK : EqOn F f₁ K := fun w hw => by simp [F, hw]
  have hFL : EqOn F (fun w => f₂ w + c) L := by
    intro w hw
    by_cases hwK : w ∈ K
    · have : w = p := by
        have : w ∈ K ∩ L := ⟨hwK, hw⟩
        rwa [hKL, mem_singleton_iff] at this
      subst this; simp [F, hwK, c]
    · simp [F, hwK]
  refine ⟨F, ?_, ?_⟩
  · exact ContinuousOn.union_of_isClosed (hf₁.congr hFK)
      ((hf₂.add continuousOn_const).congr hFL) hK hL
  · rintro w (hw | hw)
    · rw [hFK hw, hfg₁ w hw]
    · rw [hFL hw, exp_add, hc, mul_one, hfg₂ w hw]

/-- Two logarithms of the same function on a preconnected set differ by a constant (values in
`2πiℤ`, `IsPreconnected.constant_of_mapsTo`). Estimate: ~0.3 session. -/
theorem HasLogOn.sub_eq_const {g f₁ f₂ : ℂ → ℂ} {S : Set ℂ} (hS : IsPreconnected S)
    (hf₁ : ContinuousOn f₁ S) (hf₂ : ContinuousOn f₂ S)
    (h₁ : ∀ w ∈ S, exp (f₁ w) = g w) (h₂ : ∀ w ∈ S, exp (f₂ w) = g w) {x y : ℂ}
    (hx : x ∈ S) (hy : y ∈ S) : f₁ x - f₂ x = f₁ y - f₂ y := by
  sorry

/-- A path in `Kᶜ` from `z'` to `z` gives a logarithm of `(w - z)/(w - z')` on `K`
(`HasLogOn.of_homotopy` with `H s w = (w - γ s)/(w - z')`, starting from the constant `1`).
Estimate: ~0.3 session. -/
theorem hasLogOn_div_of_joinedIn {K : Set ℂ} {z z' : ℂ} (h : JoinedIn Kᶜ z' z) :
    HasLogOn (fun w => (w - z) / (w - z')) K := by
  sorry

/-- **Eilenberg's criterion** (the hard direction). If `(w - z)/(w - z')` has a continuous
logarithm on the compact set `K`, then `z` and `z'` lie in the same component of `Kᶜ`.

Proof. Let `U` be the component of `z`; suppose `z' ∉ U`. WLOG `U` is bounded (at most one
component of `Kᶜ` is unbounded, since `ℂ \ closedBall 0 R` is connected; otherwise swap `z, z'` and
use `-f`). Extend `f` to `F : ℂ → ℂ` by Tietze (`ContinuousMap.exists_restrict_eq`). Put
`φ = exp F · (w - z')` on `closure U` and `φ = w - z` off `U`; they agree on
`frontier U ⊆ K`, so `φ` is continuous, and nonvanishing on `ℂ`. Then `φ = exp h` globally
(`Complex.exists_continuousOn_eqOn_exp_comp` on `univ`), so `w - z` has a logarithm on a large
circle around `z`, contradicting `not_hasLogOn_sub_sphere`. Estimate: ~1.5–2 sessions. -/
theorem mem_connectedComponentIn_of_hasLogOn {K : Set ℂ} (hK : IsCompact K) {z z' : ℂ}
    (hz : z ∉ K) (hz' : z' ∉ K) (h : HasLogOn (fun w => (w - z) / (w - z')) K) :
    z' ∈ connectedComponentIn Kᶜ z := by
  sorry

/-- If `|z| < 1 < |z'|`, `(w - z)/(w - z')` has no logarithm on `C`. Proof: `w - z'` has one
(`-z'(1 - w/z')`, principal branch), hence so would `w - z`, and then `w` (homotopy
`w - (1 - s) z`), contradicting `not_hasLogOn_sub_sphere 0`. Estimate: ~0.3 session. -/
theorem not_hasLogOn_circle_div {z z' : ℂ} (hz : z ∈ disc) (hz' : 1 < ‖z'‖) :
    ¬ HasLogOn (fun w => (w - z) / (w - z')) circle := by
  sorry

end Log

/-! ## §2. Non-separation -/

section NonSeparation

/-- A set `S ⊆ Kᶜ`, clopen in `Kᶜ`, on which every `(w - z)/(w - z')` has a logarithm on `K`,
is preconnected (from Eilenberg's criterion). -/
theorem isPreconnected_of_hasLogOn {K S : Set ℂ} (hK : IsCompact K) (hSK : S ⊆ Kᶜ)
    (hSo : IsOpen S) (hScl : closure S ∩ Kᶜ ⊆ S)
    (h : ∀ z ∈ S, ∀ z' ∈ S, HasLogOn (fun w => (w - z) / (w - z')) K) : IsPreconnected S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact isPreconnected_empty
  refine isPreconnected_of_forall x fun y hy => ⟨connectedComponentIn Kᶜ x, ?_,
    mem_connectedComponentIn (hSK hx),
    mem_connectedComponentIn_of_hasLogOn hK (hSK hx) (hSK hy) (h x hx y hy),
    isPreconnected_connectedComponentIn⟩
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hSo
    ⟨x, mem_connectedComponentIn (hSK hx), hx⟩ ?_
  exact fun w ⟨hw, hwc⟩ => hScl ⟨hw, connectedComponentIn_subset _ _ hwc⟩

/-- An arc does not separate the plane. -/
theorem isPreconnected_compl_arc {σ : Set ℂ} {a b : ℂ} (hσ : IsArc σ a b) :
    IsPreconnected σᶜ := by
  have hK := arc_isCompact hσ
  refine isPreconnected_of_hasLogOn hK subset_rfl hK.isClosed.isOpen_compl
    (fun w hw => hw.2) fun z hz z' hz' => ?_
  refine admitsLogs_of_isArc hσ _ ?_ fun w hw => ?_
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => ?_
    exact sub_ne_zero.2 fun h => hz' (h ▸ hw)
  · exact div_ne_zero (sub_ne_zero.2 fun h => hz (h ▸ hw))
      (sub_ne_zero.2 fun h => hz' (h ▸ hw))

/-- `𝔻` minus two disjoint compact sets admitting logarithms, each meeting `C` in one point and
otherwise inside `𝔻`, is preconnected. (Used for (P4) with the two pieces of `σ` left after
removing a small open subarc.) -/
theorem isPreconnected_disc_diff {β₁ β₂ : Set ℂ} {a b : ℂ} (hc₁ : IsCompact β₁)
    (hc₂ : IsCompact β₂) (hl₁ : AdmitsLogs β₁) (hl₂ : AdmitsLogs β₂) (ha : a ∈ β₁)
    (hb : b ∈ β₂) (haC : a ∈ circle) (hbC : b ∈ circle) (h₁D : β₁ \ {a} ⊆ disc)
    (h₂D : β₂ \ {b} ⊆ disc) (h₁₂ : Disjoint β₁ β₂) : IsPreconnected (disc \ (β₁ ∪ β₂)) := by
  have hdC : ∀ w, w ∈ disc → w ∉ circle := fun w h1 h2 => by
    have h1' : ‖w‖ < 1 := mem_ball_zero_iff.1 h1
    have h2' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 h2
    linarith
  have hiC₁ : circle ∩ β₁ = {a} := by
    ext w; constructor
    · rintro ⟨hwC, hw⟩
      by_contra hwa
      exact hdC w (h₁D ⟨hw, hwa⟩) hwC
    · rintro rfl; exact ⟨haC, ha⟩
  have hiC₂ : (circle ∪ β₁) ∩ β₂ = {b} := by
    ext w; constructor
    · rintro ⟨hw | hw, hw₂⟩
      · by_contra hwb
        exact hdC w (h₂D ⟨hw₂, hwb⟩) hw
      · exact absurd hw₂ (disjoint_left.1 h₁₂ hw)
    · rintro rfl; exact ⟨Or.inl hbC, hb⟩
  set K := (circle ∪ β₁) ∪ β₂ with hKdef
  have hK : IsCompact K := ((isCompact_sphere 0 1).union hc₁).union hc₂
  have hS : disc \ (β₁ ∪ β₂) = disc ∩ Kᶜ := by
    ext w
    simp only [K, Set.mem_sdiff, mem_inter_iff, mem_compl_iff, mem_union]
    constructor
    · rintro ⟨hw, hw'⟩
      refine ⟨hw, ?_⟩
      rintro ((h | h) | h)
      · exact hdC w hw h
      · exact hw' (Or.inl h)
      · exact hw' (Or.inr h)
    · rintro ⟨hw, hw'⟩
      exact ⟨hw, fun h => hw' (h.elim (fun h => Or.inl (Or.inr h)) Or.inr)⟩
  rw [hS]
  refine isPreconnected_of_hasLogOn hK inter_subset_right
    (isOpen_ball.inter hK.isClosed.isOpen_compl) ?_ fun z hz z' hz' => ?_
  · rintro w ⟨hw, hwK⟩
    refine ⟨?_, hwK⟩
    have : w ∈ closedBall (0 : ℂ) 1 := by
      rw [← closure_ball (0 : ℂ) one_ne_zero]; exact closure_mono inter_subset_left hw
    rcases (mem_closedBall_zero_iff.1 this).lt_or_eq with h | h
    · exact mem_ball_zero_iff.2 h
    · exact absurd (Or.inl (Or.inl (mem_sphere_zero_iff_norm.2 h))) hwK
  · have hg : ∀ L : Set ℂ, L ⊆ K → ContinuousOn (fun w => (w - z) / (w - z')) L ∧
        ∀ w ∈ L, (w - z) / (w - z') ≠ 0 := fun L hL => by
      refine ⟨ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => ?_, fun w hw => ?_⟩
      · exact sub_ne_zero.2 fun h => hz'.2 (h ▸ hL hw)
      · exact div_ne_zero (sub_ne_zero.2 fun h => hz.2 (h ▸ hL hw))
          (sub_ne_zero.2 fun h => hz'.2 (h ▸ hL hw))
    have hC : HasLogOn (fun w => (w - z) / (w - z')) circle := by
      refine hasLogOn_div_of_joinedIn ?_
      refine ((convex_ball (0 : ℂ) 1).isPathConnected ⟨z, hz.1⟩).joinedIn z' hz'.1 z hz.1
        |>.mono fun w hw => hdC w hw
    have h1 := hl₁ _ (hg β₁ (by intro w hw; exact Or.inl (Or.inr hw))).1
      (hg β₁ (by intro w hw; exact Or.inl (Or.inr hw))).2
    have h2 := hl₂ _ (hg β₂ (by intro w hw; exact Or.inr hw)).1
      (hg β₂ (by intro w hw; exact Or.inr hw)).2
    exact (hC.union_of_inter_eq_singleton isClosed_sphere hc₁.isClosed hiC₁ h1)
      |>.union_of_inter_eq_singleton (isClosed_sphere.union hc₁.isClosed) hc₂.isClosed hiC₂ h2

end NonSeparation

/-! ## §3. The crosscut -/

section Crosscut

theorem disc_diff_isOpen {σ : Set ℂ} (hσ : IsClosed σ) : IsOpen (disc \ σ) :=
  isOpen_ball.sdiff hσ

/-- A point of `𝔻 \ σ` in the closure of a component of `𝔻 \ σ` lies in it. -/
theorem mem_component_of_mem_closure {σ : Set ℂ} (hσ : IsClosed σ) {z y : ℂ}
    (hy : y ∈ closure (connectedComponentIn (disc \ σ) z)) (hyD : y ∈ disc \ σ) :
    y ∈ connectedComponentIn (disc \ σ) z := by
  obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.1 hy _ ((disc_diff_isOpen hσ).connectedComponentIn)
    (mem_connectedComponentIn hyD)
  rw [connectedComponentIn_eq hx2, ← connectedComponentIn_eq hx1]
  exact mem_connectedComponentIn hyD

/-- If `ball p r ∩ 𝔻 ⊆ W₀` (a component) and `p ∈ closure W`, `W` another component, then
`W = W₀`. -/
theorem component_eq_of_mem_closure {σ : Set ℂ} {z z₀ p : ℂ} {r : ℝ}
    (hp : p ∈ closure (connectedComponentIn (disc \ σ) z)) (hr : 0 < r)
    (hsub : ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₀) :
    connectedComponentIn (disc \ σ) z = connectedComponentIn (disc \ σ) z₀ := by
  obtain ⟨y, hy, hyz⟩ := mem_closure_iff.1 hp _ isOpen_ball (mem_ball_self hr)
  have hyD : y ∈ disc := (connectedComponentIn_subset _ _ hyz).1
  rw [connectedComponentIn_eq hyz, ← connectedComponentIn_eq (hsub ⟨hy, hyD⟩)]

/-- If `z₂ ∉ W(z₁)`, the components of `z₁` and `z₂` are disjoint. -/
theorem component_disjoint {F : Set ℂ} {z₁ z₂ : ℂ} (hz₂ : z₂ ∈ F)
    (hne : z₂ ∉ connectedComponentIn F z₁) :
    Disjoint (connectedComponentIn F z₁) (connectedComponentIn F z₂) := by
  refine disjoint_left.2 fun y hy1 hy2 => hne ?_
  rw [connectedComponentIn_eq hy1, ← connectedComponentIn_eq hy2]
  exact mem_connectedComponentIn hz₂

/-- (Q) All points of `𝔻` near the open arc `A°` (disjoint from the closed set `σ`) lie in one
component of `𝔻 \ σ`. Proof: for `p, q ∈ A°`, the compact sub-arc between them has distance
`ρ > 0` from `σ`; join `z ∈ ball p r ∩ 𝔻` to `z' ∈ ball q r ∩ 𝔻` by segments to `(1 - ε)p`,
`(1 - ε)q` and the arc `t ↦ (1 - ε) e^{it}` (`ε < ρ`). Estimate: ~1 session. -/
theorem exists_component_near_arc {σ : Set ℂ} (hσc : IsClosed σ) {θ ℓ : ℝ} (hℓ : 0 < ℓ)
    (hdisj : Disjoint σ (circleArcOpen' θ ℓ)) :
    ∃ z₀ ∈ disc \ σ, ∀ p ∈ circleArcOpen' θ ℓ, ∃ r > 0,
      ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₀ := by
  sorry

/-- `σ` misses both open arcs. -/
theorem disjoint_arcOpen {σ : Set ℂ} {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ < 2 * π)
    (hσD : σ \ {expI' θ, expI' (θ + ℓ)} ⊆ disc) :
    Disjoint σ (circleArcOpen' θ ℓ) ∧ Disjoint σ (circleArcOpen' (θ + ℓ) (2 * π - ℓ)) := by
  have h₁ := endpoints_not_mem_circleArcOpen' (θ := θ) hℓ hℓ'.le
  have h₂ := endpoints_not_mem_circleArcOpen' (θ := θ + ℓ) (by linarith : 0 < 2 * π - ℓ)
    (by linarith)
  rw [show θ + ℓ + (2 * π - ℓ) = θ + 2 * π by ring, expI'_add_two_pi] at h₂
  have key : ∀ A : Set ℂ, A ⊆ circle → expI' θ ∉ A → expI' (θ + ℓ) ∉ A → Disjoint σ A := by
    intro A hAC ha hb
    refine disjoint_left.2 fun w hw hwA => ?_
    by_cases hab : w = expI' θ ∨ w = expI' (θ + ℓ)
    · rcases hab with rfl | rfl
      · exact ha hwA
      · exact hb hwA
    · push Not at hab
      have h1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (hσD ⟨hw, by simp [hab.1, hab.2]⟩)
      have h2 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 (hAC hwA)
      linarith
  exact ⟨key _ ((circleArcOpen'_subset θ ℓ).trans (circleArc'_subset_circle θ ℓ)) h₁.1 h₁.2,
    key _ ((circleArcOpen'_subset _ _).trans (circleArc'_subset_circle _ _)) h₂.2 h₂.1⟩

/-- (P1) The closure of every component of `𝔻 \ σ` meets `C \ {a, b}`: otherwise the component
would be clopen in `ℂ \ σ`, which is connected (`isPreconnected_compl_arc`). -/
theorem closure_component_meets_circle {σ : Set ℂ} {a b : ℂ} (hσ : IsArc σ a b)
    (haC : a ∈ circle) (hbC : b ∈ circle) (hσD : σ \ {a, b} ⊆ disc) {z : ℂ} (hz : z ∈ disc \ σ) :
    ∃ p ∈ closure (connectedComponentIn (disc \ σ) z), p ∈ circle ∧ p ∉ ({a, b} : Set ℂ) := by
  have hσc : IsClosed σ := (arc_isCompact hσ).isClosed
  set V := connectedComponentIn (disc \ σ) z
  have hVD : V ⊆ disc \ σ := connectedComponentIn_subset _ _
  by_contra hcon
  push Not at hcon
  have hsub : σᶜ ⊆ V := by
    refine (isPreconnected_compl_arc hσ).subset_of_closure_inter_subset
      (disc_diff_isOpen hσc).connectedComponentIn ⟨z, hz.2, mem_connectedComponentIn hz⟩ ?_
    rintro y ⟨hy, hyσ⟩
    have hyB : y ∈ closedBall (0 : ℂ) 1 := by
      rw [← closure_ball (0 : ℂ) one_ne_zero]
      exact closure_mono (fun w hw => (hVD hw).1) hy
    rcases (mem_closedBall_zero_iff.1 hyB).lt_or_eq with h | h
    · exact mem_component_of_mem_closure hσc hy ⟨mem_ball_zero_iff.2 h, hyσ⟩
    · have := hcon y hy (mem_sphere_zero_iff_norm.2 h)
      rcases this with rfl | rfl
      · exact absurd (arc_left_mem hσ) hyσ
      · exact absurd (arc_right_mem hσ) hyσ
  have h2 : (2 : ℂ) ∉ σ := by
    intro h2σ
    by_cases h : (2 : ℂ) = a ∨ (2 : ℂ) = b
    · rcases h with h | h
      · have := mem_sphere_zero_iff_norm.1 (h ▸ haC); norm_num at this
      · have := mem_sphere_zero_iff_norm.1 (h ▸ hbC); norm_num at this
    · push Not at h
      have := mem_ball_zero_iff.1 (hσD ⟨h2σ, by simp [h.1, h.2]⟩)
      norm_num at this
  have := (hVD (hsub h2)).1
  rw [mem_ball_zero_iff] at this
  norm_num at this

/-- (P3) The two sides differ. Proof: suppose `z₂ ∈ W(z₁)`. Pick `p ∈ A₁°`, and points
`z ∈ ball p r ∩ 𝔻` and `z_out = (1 + ε) p`; they are joined in `ℂ \ (σ ∪ A₂)` (through `p`), so
`(w - z)/(w - z_out)` has a logarithm on `σ ∪ A₂` (`hasLogOn_div_of_joinedIn`). Symmetrically,
`z` is joined to `z₂` in `𝔻 \ σ` and `z₂` to `z_out` in `ℂ \ (σ ∪ A₁)` (via `A₂°` and
`ℂ \ 𝔻̄`), so it has one on `σ ∪ A₁`. The two logarithms differ by a constant on the connected `σ`
(`HasLogOn.sub_eq_const`), so they glue on `A₁ ∪ A₂ = C`, contradicting `not_hasLogOn_circle_div`.
Estimate: ~1–1.5 sessions. -/
theorem not_mem_component_of_sides {σ : Set ℂ} {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ < 2 * π)
    (hσ : IsArc σ (expI' θ) (expI' (θ + ℓ))) (hσD : σ \ {expI' θ, expI' (θ + ℓ)} ⊆ disc)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ disc \ σ) (hz₂ : z₂ ∈ disc \ σ)
    (h₁ : ∀ p ∈ circleArcOpen' θ ℓ, ∃ r > 0,
      ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₁)
    (h₂ : ∀ p ∈ circleArcOpen' (θ + ℓ) (2 * π - ℓ), ∃ r > 0,
      ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₂) :
    z₂ ∉ connectedComponentIn (disc \ σ) z₁ := by
  sorry

/-- (P4) If `𝔻 \ σ` has a point `y` outside the component `W` of `z`, every interior point of `σ`
is in `closure W`. Proof: if `p = γ(t₀) ∉ closure W`, pick `δ` with `γ([t₀ - δ, t₀ + δ])` in a ball
missing `closure W`; with `β₁ = γ([0, t₀ - δ])`, `β₂ = γ([t₀ + δ, 1])` (`admitsLogs_image_Icc`),
`W` is clopen in `𝔻 \ (β₁ ∪ β₂)`, which is preconnected (`isPreconnected_disc_diff`); so
`W ⊇ 𝔻 \ σ ∋ y`. Estimate: ~1 session. -/
theorem diff_subset_closure_component {σ : Set ℂ} {a b : ℂ} (hσ : IsArc σ a b)
    (haC : a ∈ circle) (hbC : b ∈ circle) (hσD : σ \ {a, b} ⊆ disc) {z y : ℂ}
    (hz : z ∈ disc \ σ) (hy : y ∈ disc \ σ) (hyz : y ∉ connectedComponentIn (disc \ σ) z) :
    σ \ {a, b} ⊆ closure (connectedComponentIn (disc \ σ) z) := by
  sorry

/-- The frontier of a side. -/
theorem frontier_component_eq {σ A Ao Bo : Set ℂ} (hσc : IsClosed σ) {z₀ z₂ : ℂ}
    (h₀ : ∀ p ∈ Ao, ∃ r > 0, ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₀)
    (h₂ : ∀ p ∈ Bo, ∃ r > 0, ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₂)
    (hdisj : Disjoint (connectedComponentIn (disc \ σ) z₀) (connectedComponentIn (disc \ σ) z₂))
    (hcirc : circle ⊆ A ∪ Bo) (hAC : A ⊆ circle) (hAoC : Ao ⊆ circle) (hAcl : A ⊆ closure Ao)
    (hσcl : σ ⊆ closure (connectedComponentIn (disc \ σ) z₀)) :
    frontier (connectedComponentIn (disc \ σ) z₀) = σ ∪ A := by
  set V := connectedComponentIn (disc \ σ) z₀
  have hVD : V ⊆ disc \ σ := connectedComponentIn_subset _ _
  have hdC : ∀ w, w ∈ disc → w ∉ circle := fun w h1 h2 => by
    have h1' : ‖w‖ < 1 := mem_ball_zero_iff.1 h1
    have h2' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 h2
    linarith
  rw [(disc_diff_isOpen hσc).connectedComponentIn.frontier_eq]
  ext x
  constructor
  · rintro ⟨hxcl, hxV⟩
    by_cases hxσ : x ∈ σ
    · exact Or.inl hxσ
    have hxB : x ∈ closedBall (0 : ℂ) 1 := by
      rw [← closure_ball (0 : ℂ) one_ne_zero]
      exact closure_mono (fun w hw => (hVD hw).1) hxcl
    rcases (mem_closedBall_zero_iff.1 hxB).lt_or_eq with h | h
    · exact absurd (mem_component_of_mem_closure hσc hxcl ⟨mem_ball_zero_iff.2 h, hxσ⟩) hxV
    rcases hcirc (mem_sphere_zero_iff_norm.2 h) with hxA | hxB'
    · exact Or.inr hxA
    obtain ⟨r, hr, hsub⟩ := h₂ x hxB'
    obtain ⟨y, hy, hyV⟩ := mem_closure_iff.1 hxcl _ isOpen_ball (mem_ball_self hr)
    exact absurd (hsub ⟨hy, (hVD hyV).1⟩) (disjoint_left.1 hdisj hyV)
  · have hAocl : Ao ⊆ closure V := fun p hp => by
      obtain ⟨r, hr, hsub⟩ := h₀ p hp
      exact closure_mono hsub (mem_closure_ball_inter_disc (hAoC hp) hr)
    rintro (hx | hx)
    · exact ⟨hσcl hx, fun h => (hVD h).2 hx⟩
    · refine ⟨closure_minimal hAocl isClosed_closure (hAcl hx), fun h => ?_⟩
      exact hdC x (hVD h).1 (hAC hx)

/-- **`fact:crosscut`** (θ-curve theorem for crosscuts of `𝔻`), with exactly the statement of
`TJK.crosscut_theorem`. -/
theorem crosscut_theorem' {σ : Set ℂ} {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ < 2 * π)
    (hσ : IsArc σ (expI' θ) (expI' (θ + ℓ))) (hσD : σ \ {expI' θ, expI' (θ + ℓ)} ⊆ disc) :
    ∃ z₁ ∈ disc \ σ, ∃ z₂ ∈ disc \ σ,
      Disjoint (connectedComponentIn (disc \ σ) z₁) (connectedComponentIn (disc \ σ) z₂) ∧
      (∀ z ∈ disc \ σ, connectedComponentIn (disc \ σ) z = connectedComponentIn (disc \ σ) z₁ ∨
        connectedComponentIn (disc \ σ) z = connectedComponentIn (disc \ σ) z₂) ∧
      frontier (connectedComponentIn (disc \ σ) z₁) = σ ∪ circleArc' θ ℓ ∧
      frontier (connectedComponentIn (disc \ σ) z₂) = σ ∪ circleArc' (θ + ℓ) (2 * π - ℓ) := by
  have hσc : IsClosed σ := (arc_isCompact hσ).isClosed
  have hℓ₂ : 0 < 2 * π - ℓ := by linarith
  have haC := expI'_mem_circle θ
  have hbC := expI'_mem_circle (θ + ℓ)
  have hend : θ + ℓ + (2 * π - ℓ) = θ + 2 * π := by ring
  obtain ⟨hd₁, hd₂⟩ := disjoint_arcOpen hℓ hℓ' hσD
  obtain ⟨z₁, hz₁, h₁⟩ := exists_component_near_arc hσc hℓ hd₁
  obtain ⟨z₂, hz₂, h₂⟩ := exists_component_near_arc hσc hℓ₂ hd₂
  have hne := not_mem_component_of_sides hℓ hℓ' hσ hσD hz₁ hz₂ h₁ h₂
  have hdisj := component_disjoint hz₂ hne
  have hne' : z₁ ∉ connectedComponentIn (disc \ σ) z₂ := fun h =>
    disjoint_left.1 hdisj (mem_connectedComponentIn hz₁) h
  have hcirc := circle_diff_subset (θ := θ) hℓ hℓ'
  -- the closed arcs are in the closures of the sides
  have hAcl : ∀ {θ' ℓ' : ℝ} {z₀ : ℂ}, 0 < ℓ' →
      (∀ p ∈ circleArcOpen' θ' ℓ', ∃ r > 0,
        ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₀) →
      circleArc' θ' ℓ' ⊆ closure (connectedComponentIn (disc \ σ) z₀) := by
    intro θ' ℓ' z₀ hl h p hp
    refine closure_minimal (fun q hq => ?_) isClosed_closure (circleArc'_subset_closure hl hp)
    obtain ⟨r, hr, hsub⟩ := h q hq
    exact closure_mono hsub (mem_closure_ball_inter_disc
      ((circleArcOpen'_subset _ _).trans (circleArc'_subset_circle _ _) hq) hr)
  have hab₁ : ({expI' θ, expI' (θ + ℓ)} : Set ℂ) ⊆ circleArc' θ ℓ := by
    rintro _ (rfl | rfl)
    · exact ⟨θ, ⟨le_rfl, by linarith⟩, rfl⟩
    · exact ⟨θ + ℓ, ⟨by linarith, le_rfl⟩, rfl⟩
  have hab₂ : ({expI' θ, expI' (θ + ℓ)} : Set ℂ) ⊆ circleArc' (θ + ℓ) (2 * π - ℓ) := by
    rintro _ (rfl | rfl)
    · exact ⟨θ + 2 * π, ⟨by linarith, by linarith⟩, expI'_add_two_pi θ⟩
    · exact ⟨θ + ℓ, ⟨le_rfl, by linarith⟩, rfl⟩
  have hσcl : ∀ {z₀ y : ℂ} (A : Set ℂ), z₀ ∈ disc \ σ → y ∈ disc \ σ →
      y ∉ connectedComponentIn (disc \ σ) z₀ → ({expI' θ, expI' (θ + ℓ)} : Set ℂ) ⊆ A →
      A ⊆ closure (connectedComponentIn (disc \ σ) z₀) →
      σ ⊆ closure (connectedComponentIn (disc \ σ) z₀) := by
    intro z₀ y A hz₀ hy hyz habA hA w hw
    by_cases hwab : w ∈ ({expI' θ, expI' (θ + ℓ)} : Set ℂ)
    · exact hA (habA hwab)
    · exact diff_subset_closure_component hσ haC hbC hσD hz₀ hy hyz ⟨hw, hwab⟩
  refine ⟨z₁, hz₁, z₂, hz₂, hdisj, fun z hz => ?_, ?_, ?_⟩
  · obtain ⟨p, hpcl, hpC, hpab⟩ := closure_component_meets_circle hσ haC hbC hσD hz
    rcases hcirc ⟨hpC, hpab⟩ with hp | hp
    · obtain ⟨r, hr, hsub⟩ := h₁ p hp
      exact Or.inl (component_eq_of_mem_closure hpcl hr hsub)
    · obtain ⟨r, hr, hsub⟩ := h₂ p hp
      exact Or.inr (component_eq_of_mem_closure hpcl hr hsub)
  · refine frontier_component_eq hσc h₁ h₂ hdisj ?_ (circleArc'_subset_circle _ _)
      ((circleArcOpen'_subset _ _).trans (circleArc'_subset_circle _ _))
      (circleArc'_subset_closure hℓ)
      (hσcl _ hz₁ hz₂ hne hab₁ (hAcl hℓ h₁))
    intro w hw
    by_cases hwab : w ∈ ({expI' θ, expI' (θ + ℓ)} : Set ℂ)
    · exact Or.inl (hab₁ hwab)
    · rcases hcirc ⟨hw, hwab⟩ with h | h
      · exact Or.inl (circleArcOpen'_subset _ _ h)
      · exact Or.inr h
  · refine frontier_component_eq hσc h₂ h₁ hdisj.symm ?_ (circleArc'_subset_circle _ _)
      ((circleArcOpen'_subset _ _).trans (circleArc'_subset_circle _ _))
      (circleArc'_subset_closure hℓ₂)
      (hσcl _ hz₂ hz₁ hne' hab₂ (hAcl hℓ₂ h₂))
    intro w hw
    by_cases hwab : w ∈ ({expI' θ, expI' (θ + ℓ)} : Set ℂ)
    · exact Or.inl (hab₂ hwab)
    · rcases hcirc ⟨hw, hwab⟩ with h | h
      · exact Or.inr h
      · exact Or.inl (circleArcOpen'_subset _ _ h)

end Crosscut

end JordanCrosscut

end TJK
