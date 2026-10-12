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
`K` (`continuousOn_iff_continuous_domRestrict`). -/
theorem HasLogOn.of_homotopy {K : Set ℂ} {H : ℝ → ℂ → ℂ}
    (hH : ContinuousOn (fun x : ℝ × ℂ => H x.1 x.2) (Icc 0 1 ×ˢ K))
    (hH0 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ w ∈ K, H s w ≠ 0) (h0 : HasLogOn (H 0) K) :
    HasLogOn (H 1) K := by
  classical
  obtain ⟨f, hf, hfg⟩ := h0
  have hc : Continuous fun x : unitInterval × K => ((x.1 : ℝ), (x.2 : ℂ)) := by fun_prop
  let Hc : C(unitInterval × K, {z : ℂ // z ≠ 0}) :=
    ⟨fun x => ⟨H x.1 x.2, hH0 x.1 x.1.2 x.2 x.2.2⟩,
      (hH.comp_continuous hc fun x => ⟨x.1.2, x.2.2⟩).subtype_mk _⟩
  let f0 : C(K, ℂ) := ⟨K.domRestrict f, (continuousOn_iff_continuous_domRestrict).1 hf⟩
  have H_0 : ∀ a, Hc (0, a) = (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) (f0 a) := by
    intro a; ext; exact (hfg a a.2).symm
  set L := isCoveringMap_exp.liftHomotopy Hc f0 H_0
  have hL := isCoveringMap_exp.liftHomotopy_lifts Hc f0 H_0
  refine ⟨fun w => if h : w ∈ K then L (1, ⟨w, h⟩) else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : K.domRestrict (fun w => if h : w ∈ K then L (1, ⟨w, h⟩) else 0) =
        fun a => L (1, a) := by
      ext a; simp only [Set.domRestrict_apply, dif_pos a.2]
    rw [this]; fun_prop
  · intro w hw
    have := congrArg Subtype.val (congrFun hL (1, ⟨w, hw⟩))
    simp only [dif_pos hw]
    exact this

/-- A continuous function with `exp ∘ h = 1` on a preconnected set is constant there (its values
lie in the discrete group `2πiℤ`). -/
theorem eq_of_exp_eq_one {α : Type*} [TopologicalSpace α] {S : Set α} (hS : IsPreconnected S)
    {h : α → ℂ} (hc : ContinuousOn h S) (h1 : ∀ x ∈ S, exp (h x) = 1) {x y : α} (hx : x ∈ S)
    (hy : y ∈ S) : h x = h y := by
  refine hS.constant_of_mapsTo (T := (AddSubgroup.zmultiples (2 * π * I) : Set ℂ))
    (isDiscrete_iff_discreteTopology.2 (NormedSpace.discreteTopology_zmultiples _)) hc
    (fun x hx => ?_) hx hy
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 (h1 x hx)
  exact ⟨n, by simp only [hn, zsmul_eq_mul]⟩

/-- `w ↦ w - c` has no continuous logarithm on a circle centred at `c`. Proof: with
`g(t) = f(c + r e^{it}) - log r - it`, `exp ∘ g = 1`, so `g` is constant on `[0, 2π]` (connected,
values in `2πiℤ`), but `g(2π) = g(0) - 2πi`. -/
theorem not_hasLogOn_sub_sphere (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ¬ HasLogOn (fun w => w - c) (sphere c r) := by
  rintro ⟨f, hf, hfg⟩
  set γ : ℝ → ℂ := fun t => c + r * exp (t * I)
  have hγ : Continuous γ := by fun_prop
  have hγS : ∀ t, γ t ∈ sphere c r := fun t => by
    rw [mem_sphere_iff_norm, show γ t - c = r * exp (t * I) by simp [γ], norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have key := eq_of_exp_eq_one isPreconnected_univ
    (h := fun t : ℝ => f (γ t) - (t * I + log r))
    ((hf.comp_continuous hγ hγS).sub (by fun_prop)).continuousOn
    (fun t _ => by
      rw [exp_sub, hfg _ (hγS t), exp_add, exp_log hr0]
      simp only [γ, add_sub_cancel_left]
      field_simp)
    (mem_univ 0) (mem_univ (2 * π))
  have hγ2 : γ (2 * π) = γ 0 := by
    simp only [γ]; congr 2
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, exp_two_pi_mul_I]; simp
  simp only [hγ2] at key
  have : ((2 * π : ℝ) : ℂ) * I = 0 := by
    push_cast at key ⊢
    linear_combination key
  simp [Real.pi_ne_zero, I_ne_zero] at this

/-- Same for the image of a compact interval under a map continuous and injective on it (the
subarcs of an arc used in (P4)). Proof: `γ` is a homeomorphism of `[s, t]` onto its image
(compact to Hausdorff); contract along `H u w = g (γ (s + u (γ⁻¹ w - s)))` and apply
`HasLogOn.of_homotopy` from the constant `g (γ s)`. -/
theorem admitsLogs_image_Icc {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContinuousOn γ (Icc s t))
    (hinj : InjOn γ (Icc s t)) : AdmitsLogs (γ '' Icc s t) := by
  classical
  intro g hg hg0
  set K := γ '' Icc s t
  rcases (Icc s t).eq_empty_or_nonempty with he | ⟨s₀, hs₀⟩
  · rw [show K = ∅ by simp [K, he]]
    exact ⟨fun _ => 0, continuousOn_empty _, fun w hw => hw.elim⟩
  have hst : s ≤ t := hs₀.1.trans hs₀.2
  -- the inverse of `γ` on `K` is continuous (compact to Hausdorff)
  have : CompactSpace (Icc s t) := isCompact_iff_compactSpace.1 isCompact_Icc
  let e : Icc s t → K := fun x => ⟨γ x, mem_image_of_mem _ x.2⟩
  have he_cont : Continuous e :=
    ((continuousOn_iff_continuous_domRestrict.1 hγ)).subtype_mk _
  have he_bij : Bijective e := by
    refine ⟨fun x y hxy => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy)), ?_⟩
    rintro ⟨w, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  set E := Equiv.ofBijective e he_bij
  have hE : Continuous E.symm := he_cont.continuous_symm_of_equiv_compact_to_t2 (f := E)
  set ψ : ℂ → ℝ := fun w => if h : w ∈ K then (E.symm ⟨w, h⟩ : ℝ) else s
  have hψK : ∀ w ∈ K, ψ w ∈ Icc s t := fun w hw => by
    simp only [ψ, dif_pos hw]; exact (E.symm ⟨w, hw⟩).2
  have hγψ : ∀ w ∈ K, γ (ψ w) = w := fun w hw => by
    simp only [ψ, dif_pos hw]
    exact congrArg Subtype.val (E.apply_symm_apply ⟨w, hw⟩)
  have hψ : ContinuousOn ψ K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : K.domRestrict ψ = fun w => (E.symm w : ℝ) := by
      ext w; simp only [Set.domRestrict_apply, ψ, dif_pos w.2]
    rw [this]; fun_prop
  -- contract `K` onto `γ s` along `γ`
  set H : ℝ → ℂ → ℂ := fun u w => g (γ (s + u * (ψ w - s)))
  have hmem : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ K, s + x.1 * (ψ x.2 - s) ∈ Icc s t := by
    rintro ⟨u, w⟩ ⟨hu, hw⟩
    have h1 := hψK w hw
    have h2 : 0 ≤ u * (ψ w - s) := mul_nonneg hu.1 (by linarith [h1.1])
    have h3 : u * (ψ w - s) ≤ 1 * (ψ w - s) :=
      mul_le_mul_of_nonneg_right hu.2 (by linarith [h1.1])
    constructor <;> simp only at h2 h3 ⊢ <;> linarith [h1.2]
  have hH : ContinuousOn (fun x : ℝ × ℂ => H x.1 x.2) (Icc 0 1 ×ˢ K) := by
    have hlin : ContinuousOn (fun x : ℝ × ℂ => s + x.1 * (ψ x.2 - s)) (Icc 0 1 ×ˢ K) :=
      continuousOn_const.add (continuousOn_fst.mul
        ((hψ.comp continuousOn_snd fun x hx => hx.2).sub continuousOn_const))
    exact hg.comp (hγ.comp hlin hmem) fun x hx => mem_image_of_mem _ (hmem x hx)
  have hH0 : ∀ u ∈ Icc (0 : ℝ) 1, ∀ w ∈ K, H u w ≠ 0 := fun u hu w hw =>
    hg0 _ (mem_image_of_mem _ (hmem (u, w) ⟨hu, hw⟩))
  have hstart : HasLogOn (H 0) K := by
    refine (hasLogOn_const (c := g (γ s)) (hg0 _ (mem_image_of_mem _ ⟨le_rfl, hst⟩)) K).congr ?_
    intro w _; simp [H]
  refine (HasLogOn.of_homotopy hH hH0 hstart).congr fun w hw => ?_
  simp only [H, one_mul, add_sub_cancel, hγψ w hw]

/-- Every continuous nonvanishing function on an arc has a continuous logarithm. Proof: the
parametrization `p.extend` is continuous and injective on `[0, 1]`; apply
`admitsLogs_image_Icc`. -/
theorem admitsLogs_of_isArc {σ : Set ℂ} {a b : ℂ} (hσ : IsArc σ a b) : AdmitsLogs σ := by
  obtain ⟨p, hinj, rfl⟩ := hσ
  rw [← p.image_extend_of_subset subset_rfl]
  refine admitsLogs_image_Icc p.continuous_extend.continuousOn fun x hx y hy hxy => ?_
  rw [Path.extend_apply _ hx, Path.extend_apply _ hy] at hxy
  exact congrArg Subtype.val (hinj hxy)

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
`2πiℤ`, `eq_of_exp_eq_one`). -/
theorem HasLogOn.sub_eq_const {g f₁ f₂ : ℂ → ℂ} {S : Set ℂ} (hS : IsPreconnected S)
    (hf₁ : ContinuousOn f₁ S) (hf₂ : ContinuousOn f₂ S)
    (h₁ : ∀ w ∈ S, exp (f₁ w) = g w) (h₂ : ∀ w ∈ S, exp (f₂ w) = g w) {x y : ℂ}
    (hx : x ∈ S) (hy : y ∈ S) : f₁ x - f₂ x = f₁ y - f₂ y := by
  refine eq_of_exp_eq_one hS (h := fun w => f₁ w - f₂ w) (hf₁.sub hf₂) (fun w hw => ?_) hx hy
  have h0 : g w ≠ 0 := by rw [← h₁ w hw]; exact exp_ne_zero _
  rw [exp_sub, h₁ w hw, h₂ w hw, div_self h0]

/-- A path in `Kᶜ` from `z'` to `z` gives a logarithm of `(w - z)/(w - z')` on `K`
(`HasLogOn.of_homotopy` with `H s w = (w - γ s)/(w - z')`, starting from the constant `1`). -/
theorem hasLogOn_div_of_joinedIn {K : Set ℂ} {z z' : ℂ} (h : JoinedIn Kᶜ z' z) :
    HasLogOn (fun w => (w - z) / (w - z')) K := by
  set γ := h.somePath
  have hγK : ∀ u ∈ Icc (0 : ℝ) 1, γ.extend u ∉ K := fun u hu => by
    rw [Path.extend_apply _ hu]; exact h.somePath_mem _
  have hz'K : z' ∉ K := by simpa using hγK 0 ⟨le_rfl, zero_le_one⟩
  have hne : ∀ w ∈ K, w - z' ≠ 0 := fun w hw => sub_ne_zero.2 fun h => hz'K (h ▸ hw)
  set H : ℝ → ℂ → ℂ := fun u w => (w - γ.extend u) / (w - z')
  have hH : ContinuousOn (fun x : ℝ × ℂ => H x.1 x.2) (Icc 0 1 ×ˢ K) := by
    refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) fun x hx => hne x.2 hx.2
  have hH0 : ∀ u ∈ Icc (0 : ℝ) 1, ∀ w ∈ K, H u w ≠ 0 := fun u hu w hw =>
    div_ne_zero (sub_ne_zero.2 fun h => hγK u hu (h ▸ hw)) (hne w hw)
  have hstart : HasLogOn (H 0) K :=
    (hasLogOn_const one_ne_zero K).congr fun w hw => by
      simp only [H, Path.extend_zero, div_self (hne w hw)]
  exact (HasLogOn.of_homotopy hH hH0 hstart).congr fun w _ => by simp [H]

/-- Eilenberg's criterion when the component `U` of `z` in `Kᶜ` is bounded. If `z' ∉ U`, glue
`exp F · (w - z')` on `U` (`F` a Tietze extension of the logarithm) with `w - z` off `U`; they
agree on `frontier U ⊆ K`. The result is continuous and nonvanishing on `ℂ`, so (contracting `ℂ`
to `z`) it has a logarithm on a large circle around `z`, where it equals `w - z`. -/
theorem mem_connectedComponentIn_of_hasLogOn_aux {K : Set ℂ} (hK : IsCompact K) {z z' : ℂ}
    (hz : z ∉ K) (hz' : z' ∉ K) (h : HasLogOn (fun w => (w - z) / (w - z')) K) {R : ℝ}
    (hR : connectedComponentIn Kᶜ z ⊆ closedBall 0 R) :
    z' ∈ connectedComponentIn Kᶜ z := by
  classical
  by_contra hz'U
  set U := connectedComponentIn Kᶜ z with hUdef
  have hKo : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hUo : IsOpen U := hKo.connectedComponentIn
  obtain ⟨f, hf, hfg⟩ := h
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hK.isClosed
    (⟨K.domRestrict f, hf.domRestrict⟩ : C(K, ℂ))
  have hFK : ∀ w ∈ K, F w = f w := fun w hw => by
    have := congrArg (fun g : C(K, ℂ) => g ⟨w, hw⟩) hF
    exact this
  have hfr : frontier U ⊆ K := by
    intro a ha
    by_contra haK
    rw [hUo.frontier_eq] at ha
    obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.1 ha.1 _ hKo.connectedComponentIn
      (mem_connectedComponentIn (F := Kᶜ) haK)
    apply ha.2
    rw [hUdef, connectedComponentIn_eq hx2, ← connectedComponentIn_eq hx1]
    exact mem_connectedComponentIn haK
  set φ : ℂ → ℂ := fun w => if w ∈ U then exp (F w) * (w - z') else w - z
  have hφ : Continuous φ := by
    refine Continuous.if (fun a ha => ?_) (by fun_prop) (by fun_prop)
    have haK : a ∈ K := hfr ha
    rw [hFK a haK, hfg a haK, div_mul_cancel₀ _ (sub_ne_zero.2 fun e : a = z' => hz' (e ▸ haK))]
  have hφ0 : ∀ w, φ w ≠ 0 := by
    intro w
    by_cases hw : w ∈ U
    · simp only [φ, if_pos hw]
      exact mul_ne_zero (exp_ne_zero _) (sub_ne_zero.2 fun e => hz'U (e ▸ hw))
    · simp only [φ, if_neg hw]
      exact sub_ne_zero.2 fun e => hw (e ▸ mem_connectedComponentIn (F := Kᶜ) hz)
  set r : ℝ := |R| + ‖z‖ + 1
  have hr : 0 < r := by positivity
  have hsph : ∀ w ∈ sphere z r, w ∉ U := fun w hw hwU => by
    have h1 := mem_closedBall_zero_iff.1 (hR hwU)
    have h2 := mem_sphere_iff_norm.1 hw
    have h3 := norm_sub_le w z
    linarith [le_abs_self R]
  set H : ℝ → ℂ → ℂ := fun s w => φ (z + s * (w - z))
  have hlog := HasLogOn.of_homotopy (K := sphere z r) (H := H)
    (Continuous.continuousOn (by fun_prop)) (fun s _ w _ => hφ0 _)
    ((hasLogOn_const (hφ0 z) _).congr fun w _ => by simp [H])
  exact not_hasLogOn_sub_sphere z hr (hlog.congr fun w hw => by
    simp only [H, ofReal_one, one_mul, add_sub_cancel, φ, if_neg (hsph w hw)])

/-- **Eilenberg's criterion** (the hard direction). If `(w - z)/(w - z')` has a continuous
logarithm on the compact set `K`, then `z` and `z'` lie in the same component of `Kᶜ`.

Proof. Let `U` be the component of `z`; suppose `z' ∉ U`. WLOG `U` is bounded (at most one
component of `Kᶜ` is unbounded, since `ℂ \ closedBall 0 R` is connected; otherwise swap `z, z'` and
use `-f`). Extend `f` to `F : ℂ → ℂ` by Tietze (`ContinuousMap.exists_restrict_eq`). Put
`φ = exp F · (w - z')` on `closure U` and `φ = w - z` off `U`; they agree on
`frontier U ⊆ K`, so `φ` is continuous, and nonvanishing on `ℂ`. Then `φ = exp h` globally
(`Complex.exists_continuousOn_eqOn_exp_comp` on `univ`), so `w - z` has a logarithm on a large
circle around `z`, contradicting `not_hasLogOn_sub_sphere`. (In Lean: the bounded case is
`mem_connectedComponentIn_of_hasLogOn_aux`, which contracts `ℂ` to `z` instead of taking a global
logarithm; `exp '' {Re > log ρ}` is a preconnected subset of `Kᶜ` containing all `|w| > ρ`.) -/
theorem mem_connectedComponentIn_of_hasLogOn {K : Set ℂ} (hK : IsCompact K) {z z' : ℂ}
    (hz : z ∉ K) (hz' : z' ∉ K) (h : HasLogOn (fun w => (w - z) / (w - z')) K) :
    z' ∈ connectedComponentIn Kᶜ z := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set ρ : ℝ := |R| + 1
  have hρ : 0 < ρ := by positivity
  -- the outside of a large disc, as a preconnected subset of `Kᶜ`
  set S : Set ℂ := exp '' {x : ℂ | Real.log ρ < x.re}
  have hSc : IsPreconnected S :=
    (convex_halfSpace_re_gt _).isPreconnected.image _ continuous_exp.continuousOn
  have hSK : S ⊆ Kᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hxK
    have h1 := mem_closedBall_zero_iff.1 (hR hxK)
    rw [norm_exp] at h1
    have h2 : Real.exp (Real.log ρ) < Real.exp x.re := Real.exp_lt_exp.2 hx
    rw [Real.exp_log hρ] at h2
    linarith [le_abs_self R]
  have hbig : ∀ w : ℂ, ρ < ‖w‖ → w ∈ S := fun w hw => by
    have hw0 : w ≠ 0 := by rintro rfl; rw [norm_zero] at hw; linarith
    exact ⟨log w, by
      show Real.log ρ < (log w).re
      rw [log_re]; exact Real.log_lt_log hρ hw,
      exp_log hw0⟩
  -- each component of `Kᶜ` is bounded or contains `S`
  have hdich : ∀ y, y ∉ K → connectedComponentIn Kᶜ y ⊆ closedBall 0 ρ ∨
      ∀ w ∈ S, w ∈ connectedComponentIn Kᶜ y := by
    intro y _
    by_cases hsub : connectedComponentIn Kᶜ y ⊆ closedBall 0 ρ
    · exact Or.inl hsub
    · right
      obtain ⟨w, hw, hwρ⟩ := not_subset.1 hsub
      have hwS : w ∈ S := hbig w (by simpa using hwρ)
      intro v hv
      rw [connectedComponentIn_eq hw]
      exact hSc.subset_connectedComponentIn hwS hSK hv
  have hp : ((ρ + 1 : ℝ) : ℂ) ∈ S := hbig _ (by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith)
  rcases hdich z hz with h1 | h1
  · exact mem_connectedComponentIn_of_hasLogOn_aux hK hz hz' h h1
  rcases hdich z' hz' with h2 | h2
  · have := mem_connectedComponentIn_of_hasLogOn_aux hK hz' hz
      (h.inv.congr fun w _ => by simp only [inv_div]) h2
    rw [← connectedComponentIn_eq this]
    exact mem_connectedComponentIn hz'
  · rw [connectedComponentIn_eq (h1 _ hp), ← connectedComponentIn_eq (h2 _ hp)]
    exact mem_connectedComponentIn hz'

/-- If `|z| < 1 < |z'|`, `(w - z)/(w - z')` has no logarithm on `C`. Proof: `w - z'` has one
(`-z'(1 - w/z')`, principal branch), hence so would `w - z`, and then `w` (homotopy
`w - (1 - s) z`), contradicting `not_hasLogOn_sub_sphere 0`. -/
theorem not_hasLogOn_circle_div {z z' : ℂ} (hz : z ∈ disc) (hz' : 1 < ‖z'‖) :
    ¬ HasLogOn (fun w => (w - z) / (w - z')) circle := by
  intro hlog
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hz'0 : z' ≠ 0 := by rintro rfl; norm_num at hz'
  have hz'n : 0 < ‖z'‖ := by linarith
  have hne : ∀ w ∈ circle, w - z' ≠ 0 := fun w hw h => by
    rw [sub_eq_zero] at h
    have := mem_sphere_zero_iff_norm.1 hw
    rw [h] at this; linarith
  -- `w - z'` has a logarithm on `C`: `w - z' = -z' (1 - w/z')`, principal branch
  have hw' : HasLogOn (fun w => w - z') circle := by
    refine ((hasLogOn_const (neg_ne_zero.2 hz'0) circle).mul
      (hasLogOn_of_mem_slitPlane (g := fun w => 1 + -(w / z')) (by fun_prop)
        fun w hw => mem_slitPlane_of_norm_lt_one ?_)).congr fun w _ => ?_
    · rw [norm_neg, norm_div, mem_sphere_zero_iff_norm.1 hw, div_lt_one hz'n]; exact hz'
    · simp only; field_simp; ring
  have hsub : HasLogOn (fun w => w - z) circle :=
    (hlog.mul hw').congr fun w hw => by simp only; exact div_mul_cancel₀ _ (hne w hw)
  -- deform `w - z` to `w` through `w - (1 - u) z`
  set H : ℝ → ℂ → ℂ := fun u w => w - (1 - u) * z
  have hH : ContinuousOn (fun x : ℝ × ℂ => H x.1 x.2) (Icc 0 1 ×ˢ circle) :=
    Continuous.continuousOn (by fun_prop)
  have hH0 : ∀ u ∈ Icc (0 : ℝ) 1, ∀ w ∈ circle, H u w ≠ 0 := fun u hu w hw h => by
    rw [sub_eq_zero] at h
    have h1 := mem_sphere_zero_iff_norm.1 hw
    have h2 : ‖((1 - u : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hu.2])]; linarith [hu.1]
    have h3 : ‖((1 - u : ℝ) : ℂ) * z‖ < 1 := by
      rw [norm_mul]
      calc ‖((1 - u : ℝ) : ℂ)‖ * ‖z‖ ≤ 1 * ‖z‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hz1
    push_cast at h3
    rw [h] at h1; linarith
  have hend := HasLogOn.of_homotopy hH hH0 (hsub.congr fun w _ => by simp [H])
  exact not_hasLogOn_sub_sphere 0 one_pos (hend.congr fun w _ => by simp [H])

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
`(1 - ε)q` and the arc `t ↦ (1 - ε) e^{it}` (`ε < ρ`). (In Lean: chain the convex sets
`ball p₀ δ ∩ 𝔻`, the arc `(1 - ε/2) e^{i[t₀, t]}`, and `ball p ε ∩ 𝔻`.) -/
theorem exists_component_near_arc {σ : Set ℂ} (hσc : IsClosed σ) {θ ℓ : ℝ} (hℓ : 0 < ℓ)
    (hdisj : Disjoint σ (circleArcOpen' θ ℓ)) :
    ∃ z₀ ∈ disc \ σ, ∀ p ∈ circleArcOpen' θ ℓ, ∃ r > 0,
      ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₀ := by
  have hc : Continuous expI' := by unfold expI'; fun_prop
  -- `(1 - ε/2) q` lies in `ball q ε ∩ 𝔻` for `|q| = 1`
  have hscale : ∀ {q : ℂ}, ‖q‖ = 1 → ∀ {ε : ℝ}, 0 < ε → ε < 2 →
      ((1 - ε / 2 : ℝ) : ℂ) * q ∈ ball q ε ∩ disc := by
    intro q hq ε hε hε2
    constructor
    · rw [mem_ball, dist_eq_norm, show ((1 - ε / 2 : ℝ) : ℂ) * q - q = ((-(ε / 2) : ℝ) : ℂ) * q by
        push_cast; ring, norm_mul, Complex.norm_real, hq, mul_one, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by linarith)]
      linarith
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, hq, mul_one,
        Real.norm_of_nonneg (by linarith)]
      linarith
  have hnorm : ∀ s, ‖expI' s‖ = 1 := fun s => mem_sphere_zero_iff_norm.1 (expI'_mem_circle s)
  have hconv : ∀ q ε, IsPreconnected (ball q ε ∩ disc) := fun q ε =>
    ((convex_ball q ε).inter (convex_ball 0 1)).isPreconnected
  have ht₀ : θ + ℓ / 2 ∈ Ioo θ (θ + ℓ) := ⟨by linarith, by linarith⟩
  set t₀ := θ + ℓ / 2
  have hp₀σ : expI' t₀ ∉ σ := fun h => disjoint_left.1 hdisj h ⟨t₀, ht₀, rfl⟩
  obtain ⟨δ, hδ, hδσ⟩ := Metric.isOpen_iff.1 hσc.isOpen_compl _ hp₀σ
  set δ' := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  set z₀ := ((1 - δ' / 2 : ℝ) : ℂ) * expI' t₀
  have hz₀ := hscale (hnorm t₀) hδ' (by linarith)
  have hB0 : ball (expI' t₀) δ' ∩ disc ⊆ connectedComponentIn (disc \ σ) z₀ :=
    (hconv _ _).subset_connectedComponentIn hz₀
      fun w hw => ⟨hw.2, hδσ (ball_subset_ball (min_le_left _ _) hw.1)⟩
  refine ⟨z₀, ⟨hz₀.2, hδσ (ball_subset_ball (min_le_left _ _) hz₀.1)⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hIsub : uIcc t₀ t ⊆ Ioo θ (θ + ℓ) := ordConnected_Ioo.uIcc_subset ht₀ ht
  obtain ⟨ρ, hρ, hρσ⟩ := (isCompact_uIcc.image hc).exists_thickening_subset_open
    hσc.isOpen_compl (by
      rintro _ ⟨s, hs, rfl⟩ h
      exact disjoint_left.1 hdisj h ⟨s, hIsub hs, rfl⟩)
  set ε := min ρ δ'
  have hε : 0 < ε := lt_min hρ hδ'
  have hε2 : ε < 2 := by have := min_le_right ρ δ'; linarith
  have hball : ∀ s ∈ uIcc t₀ t, ball (expI' s) ε ⊆ σᶜ := fun s hs =>
    (ball_subset_ball (min_le_left _ _)).trans
      ((ball_subset_thickening (mem_image_of_mem _ hs) _).trans hρσ)
  have hq₀ : ((1 - ε / 2 : ℝ) : ℂ) * expI' t₀ ∈ connectedComponentIn (disc \ σ) z₀ := by
    have := hscale (hnorm t₀) hε hε2
    exact hB0 ⟨ball_subset_ball (min_le_right _ _) this.1, this.2⟩
  have hT : (fun s => ((1 - ε / 2 : ℝ) : ℂ) * expI' s) '' uIcc t₀ t ⊆
      connectedComponentIn (disc \ σ) z₀ := by
    rw [connectedComponentIn_eq hq₀]
    refine (isPreconnected_uIcc.image _ (continuous_const.mul hc).continuousOn)
      |>.subset_connectedComponentIn ⟨t₀, left_mem_uIcc, rfl⟩ ?_
    rintro _ ⟨s, hs, rfl⟩
    have := hscale (hnorm s) hε hε2
    exact ⟨this.2, hball s hs this.1⟩
  have hq := hT ⟨t, right_mem_uIcc, rfl⟩
  refine ⟨ε, hε, ?_⟩
  rw [connectedComponentIn_eq hq]
  exact (hconv _ _).subset_connectedComponentIn (hscale (hnorm t) hε hε2)
    fun w hw => ⟨hw.2, hball t right_mem_uIcc hw.1⟩

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

/-- The two closed arcs meet only at the endpoints. -/
theorem circleArc'_inter_subset {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ < 2 * π) :
    circleArc' θ ℓ ∩ circleArc' (θ + ℓ) (2 * π - ℓ) ⊆ {expI' θ, expI' (θ + ℓ)} := by
  rintro _ ⟨⟨t, ht, rfl⟩, ⟨s, hs, hst⟩⟩
  obtain ⟨n, hn⟩ := expI'_eq_expI' hst
  have hπ := Real.pi_pos
  have h1 : (0 : ℝ) ≤ n * (2 * π) := by linarith [ht.2, hs.1]
  have h2 : (n : ℝ) * (2 * π) ≤ 2 * π := by linarith [ht.1, hs.2]
  have h1' : (0 : ℝ) ≤ n := by nlinarith
  have h2' : (n : ℝ) ≤ 1 := by nlinarith
  have h1'' : (0 : ℤ) ≤ n := by exact_mod_cast h1'
  have h2'' : n ≤ (1 : ℤ) := by exact_mod_cast h2'
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · have : t = θ + ℓ := by
      simp only [Int.cast_zero, zero_mul, add_zero] at hn; linarith [ht.2, hs.1]
    rw [this]; exact Or.inr rfl
  · have : t = θ := by
      simp only [Int.cast_one, one_mul] at hn; linarith [ht.1, hs.2]
    rw [this]; exact Or.inl rfl

/-- Near a point `p ∈ C \ K`, `K ⊆ 𝔻̄` closed, every point is joined to `2` in `Kᶜ`. -/
theorem exists_joinedIn_two {K : Set ℂ} (hK : IsClosed K) (hKB : K ⊆ closedBall 0 1) {p : ℂ}
    (hpC : p ∈ circle) (hpK : p ∉ K) : ∃ ρ > 0, ∀ z ∈ ball p ρ, JoinedIn Kᶜ z 2 := by
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hK.isOpen_compl p hpK
  have hp1 : ‖p‖ = 1 := mem_sphere_zero_iff_norm.1 hpC
  set ρ' := min ρ 1
  have hρ' : 0 < ρ' := lt_min hρ one_pos
  set u : ℂ := ((1 + ρ' / 2 : ℝ) : ℂ) * p
  have hu1 : 1 < ‖u‖ := by
    rw [norm_mul, Complex.norm_real, hp1, mul_one, Real.norm_of_nonneg (by positivity)]
    linarith
  have huB : u ∈ ball p ρ := by
    rw [mem_ball, dist_eq_norm, show u - p = ((ρ' / 2 : ℝ) : ℂ) * p by
      simp only [u]; push_cast; ring, norm_mul, Complex.norm_real, hp1, mul_one,
      Real.norm_of_nonneg (by positivity)]
    have := min_le_left ρ 1; linarith
  set S : Set ℂ := exp '' {x : ℂ | 0 < x.re}
  have hSc : IsPathConnected S :=
    ((convex_halfSpace_re_gt 0).isPathConnected ⟨1, by simp⟩).image continuous_exp
  have hbig : ∀ w : ℂ, 1 < ‖w‖ → w ∈ S := fun w hw => by
    have hw0 : w ≠ 0 := by rintro rfl; rw [norm_zero] at hw; linarith
    exact ⟨log w, by show 0 < (log w).re; rw [log_re]; exact Real.log_pos hw, exp_log hw0⟩
  have hSK : S ⊆ Kᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hxK
    have h1 := mem_closedBall_zero_iff.1 (hKB hxK)
    rw [norm_exp] at h1
    have h2 := Real.exp_lt_exp.2 (show (0 : ℝ) < x.re from hx)
    rw [Real.exp_zero] at h2
    linarith
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  have h1 : JoinedIn Kᶜ z u :=
    (((convex_ball p ρ).isPathConnected ⟨p, mem_ball_self hρ⟩).joinedIn z hz u huB).mono hρK
  have h2 : JoinedIn Kᶜ u 2 :=
    (hSc.joinedIn u (hbig u hu1) 2 (hbig 2 (by norm_num))).mono hSK
  exact h1.trans h2

/-- Points of one component of an open set are joined inside it. -/
theorem joinedIn_of_mem_component {U : Set ℂ} (hU : IsOpen U) {x y : ℂ} (hx : x ∈ U)
    (hy : y ∈ connectedComponentIn U x) : JoinedIn (connectedComponentIn U x) x y :=
  (hU.connectedComponentIn.isConnected_iff_isPathConnected.1
    (isConnected_connectedComponentIn_iff.2 hx)).joinedIn x (mem_connectedComponentIn hx) y hy

/-- (P3) The two sides differ. Proof: suppose `z₂ ∈ W(z₁)`. Pick `p ∈ A₁°`, and points
`z ∈ ball p r ∩ 𝔻` and `z_out = (1 + ε) p`; they are joined in `ℂ \ (σ ∪ A₂)` (through `p`), so
`(w - z)/(w - z_out)` has a logarithm on `σ ∪ A₂` (`hasLogOn_div_of_joinedIn`). Symmetrically,
`z` is joined to `z₂` in `𝔻 \ σ` and `z₂` to `z_out` in `ℂ \ (σ ∪ A₁)` (via `A₂°` and
`ℂ \ 𝔻̄`), so it has one on `σ ∪ A₁`. The two logarithms differ by a constant on the connected `σ`
(`HasLogOn.sub_eq_const`), so they glue on `A₁ ∪ A₂ = C`, contradicting `not_hasLogOn_circle_div`.
(In Lean the outside point is `2`, reached through `ℂ \ 𝔻̄` by `exists_joinedIn_two`.) -/
theorem not_mem_component_of_sides {σ : Set ℂ} {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ < 2 * π)
    (hσ : IsArc σ (expI' θ) (expI' (θ + ℓ))) (hσD : σ \ {expI' θ, expI' (θ + ℓ)} ⊆ disc)
    {z₁ z₂ : ℂ} (_hz₁ : z₁ ∈ disc \ σ) (_hz₂ : z₂ ∈ disc \ σ)
    (h₁ : ∀ p ∈ circleArcOpen' θ ℓ, ∃ r > 0,
      ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₁)
    (h₂ : ∀ p ∈ circleArcOpen' (θ + ℓ) (2 * π - ℓ), ∃ r > 0,
      ball p r ∩ disc ⊆ connectedComponentIn (disc \ σ) z₂) :
    z₂ ∉ connectedComponentIn (disc \ σ) z₁ := by
  classical
  intro hz₂W
  have hσc : IsClosed σ := (arc_isCompact hσ).isClosed
  obtain ⟨hd₁, hd₂⟩ := disjoint_arcOpen hℓ hℓ' hσD
  have hc : Continuous expI' := by unfold expI'; fun_prop
  set A₁ := circleArc' θ ℓ with hA₁def
  set A₂ := circleArc' (θ + ℓ) (2 * π - ℓ) with hA₂def
  have hA₁c : IsClosed A₁ := (isCompact_Icc.image hc).isClosed
  have hA₂c : IsClosed A₂ := (isCompact_Icc.image hc).isClosed
  have hA₁C : A₁ ⊆ circle := circleArc'_subset_circle _ _
  have hA₂C : A₂ ⊆ circle := circleArc'_subset_circle _ _
  have hinter := circleArc'_inter_subset (θ := θ) hℓ hℓ'
  have hCB : circle ⊆ closedBall (0 : ℂ) 1 := sphere_subset_closedBall
  have hσB : σ ⊆ closedBall 0 1 := by
    intro w hw
    by_cases hwab : w ∈ ({expI' θ, expI' (θ + ℓ)} : Set ℂ)
    · simp only [mem_insert_iff, mem_singleton_iff] at hwab
      rcases hwab with h | h <;> rw [h] <;> exact hCB (expI'_mem_circle _)
    · exact ball_subset_closedBall (hσD ⟨hw, hwab⟩)
  have hdC : ∀ w, w ∈ disc → w ∉ circle := fun w h1 h2 => by
    have h1' : ‖w‖ < 1 := mem_ball_zero_iff.1 h1
    have h2' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 h2
    linarith
  have he₁ := endpoints_not_mem_circleArcOpen' (θ := θ) hℓ hℓ'.le
  have he₂ := endpoints_not_mem_circleArcOpen' (θ := θ + ℓ) (by linarith : 0 < 2 * π - ℓ)
    (by linarith)
  rw [show θ + ℓ + (2 * π - ℓ) = θ + 2 * π by ring, expI'_add_two_pi] at he₂
  have hp : expI' (θ + ℓ / 2) ∈ circleArcOpen' θ ℓ :=
    ⟨θ + ℓ / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hq : expI' (θ + ℓ + (2 * π - ℓ) / 2) ∈ circleArcOpen' (θ + ℓ) (2 * π - ℓ) :=
    ⟨θ + ℓ + (2 * π - ℓ) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  set p := expI' (θ + ℓ / 2)
  set q := expI' (θ + ℓ + (2 * π - ℓ) / 2)
  have hpK₂ : p ∉ σ ∪ A₂ := by
    rintro (h | h)
    · exact disjoint_left.1 hd₁ h hp
    · have h' := hinter ⟨circleArcOpen'_subset _ _ hp, h⟩
      simp only [mem_insert_iff, mem_singleton_iff] at h'
      rcases h' with h' | h'
      · exact he₁.1 (h' ▸ hp)
      · exact he₁.2 (h' ▸ hp)
  have hqK₁ : q ∉ σ ∪ A₁ := by
    rintro (h | h)
    · exact disjoint_left.1 hd₂ h hq
    · have h' := hinter ⟨h, circleArcOpen'_subset _ _ hq⟩
      simp only [mem_insert_iff, mem_singleton_iff] at h'
      rcases h' with h' | h'
      · exact he₂.2 (h' ▸ hq)
      · exact he₂.1 (h' ▸ hq)
  obtain ⟨r₁, hr₁, hsub₁⟩ := h₁ p hp
  obtain ⟨r₂, hr₂, hsub₂⟩ := h₂ q hq
  obtain ⟨ρ₁, hρ₁, hJ₁⟩ := exists_joinedIn_two (hσc.union hA₂c)
    (union_subset hσB (hA₂C.trans hCB)) (expI'_mem_circle _) hpK₂
  obtain ⟨ρ₂, hρ₂, hJ₂⟩ := exists_joinedIn_two (hσc.union hA₁c)
    (union_subset hσB (hA₁C.trans hCB)) (expI'_mem_circle _) hqK₁
  obtain ⟨z, hzB, hzD⟩ : (ball p (min r₁ ρ₁) ∩ disc).Nonempty :=
    closure_nonempty_iff.1 ⟨p, mem_closure_ball_inter_disc (expI'_mem_circle _) (lt_min hr₁ hρ₁)⟩
  obtain ⟨z', hz'B, hz'D⟩ : (ball q (min r₂ ρ₂) ∩ disc).Nonempty :=
    closure_nonempty_iff.1 ⟨q, mem_closure_ball_inter_disc (expI'_mem_circle _) (lt_min hr₂ hρ₂)⟩
  have hzW : z ∈ connectedComponentIn (disc \ σ) z₁ :=
    hsub₁ ⟨ball_subset_ball (min_le_left _ _) hzB, hzD⟩
  have hz'W : z' ∈ connectedComponentIn (disc \ σ) z₁ := by
    rw [connectedComponentIn_eq hz₂W]
    exact hsub₂ ⟨ball_subset_ball (min_le_left _ _) hz'B, hz'D⟩
  -- a logarithm on `σ ∪ A₂`
  have hL₂ : HasLogOn (fun w => (w - z) / (w - 2)) (σ ∪ A₂) :=
    hasLogOn_div_of_joinedIn (hJ₁ z (ball_subset_ball (min_le_right _ _) hzB)).symm
  -- a logarithm on `σ ∪ A₁`
  have hWK : ∀ x, connectedComponentIn (disc \ σ) x ⊆ (σ ∪ A₁)ᶜ := fun x w hw => by
    have := connectedComponentIn_subset _ _ hw
    rintro (h | h)
    · exact this.2 h
    · exact hdC w this.1 (hA₁C h)
  have hzz' : JoinedIn (σ ∪ A₁)ᶜ z z' := by
    have := joinedIn_of_mem_component (disc_diff_isOpen hσc)
      (connectedComponentIn_subset _ _ hzW) (y := z')
      (by rw [← connectedComponentIn_eq hzW]; exact hz'W)
    exact this.mono (hWK z)
  have hL₁ : HasLogOn (fun w => (w - z) / (w - 2)) (σ ∪ A₁) :=
    hasLogOn_div_of_joinedIn
      (hzz'.trans (hJ₂ z' (ball_subset_ball (min_le_right _ _) hz'B))).symm
  -- glue along `σ`
  obtain ⟨F₁, hF₁, hFg₁⟩ := hL₁
  obtain ⟨F₂, hF₂, hFg₂⟩ := hL₂
  have hσpc : IsPreconnected σ := by
    obtain ⟨γ, -, hγ⟩ := hσ
    rw [← hγ]; exact (isConnected_range γ.continuous).isPreconnected
  have ha : expI' θ ∈ σ := arc_left_mem hσ
  set c := F₂ (expI' θ) - F₁ (expI' θ) with hcdef
  have hcσ : ∀ w ∈ σ, F₂ w - F₁ w = c := fun w hw =>
    HasLogOn.sub_eq_const hσpc (hF₂.mono subset_union_left) (hF₁.mono subset_union_left)
      (fun w hw => hFg₂ w (Or.inl hw)) (fun w hw => hFg₁ w (Or.inl hw)) hw ha
  have hc1 : exp c = 1 := by
    have h0 : (expI' θ - z) / (expI' θ - 2) ≠ 0 := by
      exact fun h => exp_ne_zero (F₁ (expI' θ)) ((hFg₁ _ (Or.inl ha)).trans h)
    rw [hcdef, exp_sub, hFg₂ _ (Or.inl ha), hFg₁ _ (Or.inl ha)]
    exact div_self h0
  set H : ℂ → ℂ := fun w => if w ∈ A₂ then F₂ w else F₁ w + c
  have hH₂ : EqOn H F₂ A₂ := fun w hw => by simp only [H, if_pos hw]
  have hH₁ : EqOn H (fun w => F₁ w + c) A₁ := by
    intro w hw
    by_cases hw₂ : w ∈ A₂
    · have hwσ : w ∈ σ := by
        have h' := hinter ⟨hw, hw₂⟩
        simp only [mem_insert_iff, mem_singleton_iff] at h'
        rcases h' with h | h
        · rw [h]; exact arc_left_mem hσ
        · rw [h]; exact arc_right_mem hσ
      simp only [H, if_pos hw₂]
      have := hcσ w hwσ
      linear_combination this
    · simp only [H, if_neg hw₂]
  have hlog : HasLogOn (fun w => (w - z) / (w - 2)) (A₁ ∪ A₂) := by
    refine ⟨H, ContinuousOn.union_of_isClosed
      (((hF₁.mono subset_union_right).add continuousOn_const).congr hH₁)
      ((hF₂.mono subset_union_right).congr hH₂) hA₁c hA₂c, ?_⟩
    rintro w (hw | hw)
    · rw [hH₁ hw, exp_add, hc1, mul_one, hFg₁ w (Or.inr hw)]
    · rw [hH₂ hw, hFg₂ w (Or.inr hw)]
  have hcirc : circle ⊆ A₁ ∪ A₂ := by
    intro w hw
    by_cases hwab : w ∈ ({expI' θ, expI' (θ + ℓ)} : Set ℂ)
    · left
      simp only [mem_insert_iff, mem_singleton_iff] at hwab
      rcases hwab with h | h
      · rw [h]; exact ⟨θ, ⟨le_rfl, by linarith⟩, rfl⟩
      · rw [h]; exact ⟨θ + ℓ, ⟨by linarith, le_rfl⟩, rfl⟩
    · rcases circle_diff_subset hℓ hℓ' ⟨hw, hwab⟩ with h | h
      · exact Or.inl (circleArcOpen'_subset _ _ h)
      · exact Or.inr (circleArcOpen'_subset _ _ h)
  exact not_hasLogOn_circle_div hzD (by norm_num) (hlog.mono hcirc)

/-- (P4) If `𝔻 \ σ` has a point `y` outside the component `W` of `z`, every interior point of `σ`
is in `closure W`. Proof: if `p = γ(t₀) ∉ closure W`, pick `δ` with `γ([t₀ - δ, t₀ + δ])` in a ball
missing `closure W`; with `β₁ = γ([0, t₀ - δ])`, `β₂ = γ([t₀ + δ, 1])` (`admitsLogs_image_Icc`),
`W` is clopen in `𝔻 \ (β₁ ∪ β₂)`, which is preconnected (`isPreconnected_disc_diff`); so
`W ⊇ 𝔻 \ σ ∋ y`. -/
theorem diff_subset_closure_component {σ : Set ℂ} {a b : ℂ} (hσ : IsArc σ a b)
    (haC : a ∈ circle) (hbC : b ∈ circle) (hσD : σ \ {a, b} ⊆ disc) {z y : ℂ}
    (hz : z ∈ disc \ σ) (hy : y ∈ disc \ σ) (hyz : y ∉ connectedComponentIn (disc \ σ) z) :
    σ \ {a, b} ⊆ closure (connectedComponentIn (disc \ σ) z) := by
  classical
  have hσc : IsClosed σ := (arc_isCompact hσ).isClosed
  obtain ⟨p, hinj, rfl⟩ := hσ
  set W := connectedComponentIn (disc \ range p) z with hW
  have hWo : IsOpen W := (disc_diff_isOpen hσc).connectedComponentIn
  rintro w ⟨⟨u, rfl⟩, hwab⟩
  by_contra hwW
  have hu0 : (u : ℝ) ≠ 0 := fun h => hwab (Or.inl (by
    rw [show u = 0 from Subtype.ext h, p.source]))
  have hu1 : (u : ℝ) ≠ 1 := fun h => hwab (Or.inr (by
    rw [show u = 1 from Subtype.ext h, p.target]; rfl))
  set t₀ : ℝ := (u : ℝ) with ht₀def
  have ht₀ : 0 < t₀ ∧ t₀ < 1 := ⟨lt_of_le_of_ne u.2.1 (Ne.symm hu0), lt_of_le_of_ne u.2.2 hu1⟩
  have hO : IsOpen (p.extend ⁻¹' (closure W)ᶜ) :=
    isClosed_closure.isOpen_compl.preimage p.continuous_extend
  have ht₀O : t₀ ∈ p.extend ⁻¹' (closure W)ᶜ := by
    show p.extend u ∉ closure W
    rw [Path.extend_extends']; exact hwW
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 hO t₀ ht₀O
  set δ' := min δ (min t₀ (1 - t₀)) / 2 with hδ'def
  have hm : 0 < min δ (min t₀ (1 - t₀)) := lt_min hδ (lt_min ht₀.1 (by linarith))
  have hδ'0 : 0 < δ' := by positivity
  have hδ'δ : δ' < δ := by have := min_le_left δ (min t₀ (1 - t₀)); linarith
  have hδ't : δ' < t₀ := by
    have := min_le_right δ (min t₀ (1 - t₀)); have := min_le_left t₀ (1 - t₀); linarith
  have hδ't' : δ' < 1 - t₀ := by
    have := min_le_right δ (min t₀ (1 - t₀)); have := min_le_right t₀ (1 - t₀); linarith
  set β₁ := p.extend '' Icc 0 (t₀ - δ')
  set β₂ := p.extend '' Icc (t₀ + δ') 1
  have hinjE : InjOn p.extend (Icc 0 1) := fun x hx y hy hxy => by
    rw [Path.extend_apply _ hx, Path.extend_apply _ hy] at hxy
    exact congrArg Subtype.val (hinj hxy)
  have hsub₁ : Icc 0 (t₀ - δ') ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl (by linarith)
  have hsub₂ : Icc (t₀ + δ') 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (by linarith) le_rfl
  have hl₁ := admitsLogs_image_Icc p.continuous_extend.continuousOn (hinjE.mono hsub₁)
  have hl₂ := admitsLogs_image_Icc p.continuous_extend.continuousOn (hinjE.mono hsub₂)
  have hc₁ : IsCompact β₁ := isCompact_Icc.image p.continuous_extend
  have hc₂ : IsCompact β₂ := isCompact_Icc.image p.continuous_extend
  have ha : a ∈ β₁ := ⟨0, ⟨le_rfl, by linarith⟩, p.extend_zero⟩
  have hb : b ∈ β₂ := ⟨1, ⟨by linarith, le_rfl⟩, p.extend_one⟩
  have hβσ : ∀ s ∈ Icc (0 : ℝ) 1, p.extend s ∈ range p := fun s hs =>
    ⟨⟨s, hs⟩, (Path.extend_apply _ hs).symm⟩
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h₁D : β₁ \ {a} ⊆ disc := by
    rintro _ ⟨⟨s, hs, rfl⟩, hsa⟩
    refine hσD ⟨hβσ s (hsub₁ hs), ?_⟩
    rintro (h | h)
    · exact hsa h
    · have := hinjE (hsub₁ hs) h11 (h.trans p.extend_one.symm)
      linarith [hs.2]
  have h₂D : β₂ \ {b} ⊆ disc := by
    rintro _ ⟨⟨s, hs, rfl⟩, hsb⟩
    refine hσD ⟨hβσ s (hsub₂ hs), ?_⟩
    rintro (h | h)
    · have := hinjE (hsub₂ hs) h01 (h.trans p.extend_zero.symm)
      linarith [hs.1]
    · exact hsb h
  have h₁₂ : Disjoint β₁ β₂ := by
    rw [disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', hss'⟩
    have := hinjE (hsub₂ hs') (hsub₁ hs) hss'
    linarith [hs.2, hs'.1]
  have hβ : β₁ ∪ β₂ ⊆ range p := by
    rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact hβσ s (hsub₁ hs)
    · exact hβσ s (hsub₂ hs)
  have hpre := isPreconnected_disc_diff hc₁ hc₂ hl₁ hl₂ ha hb haC hbC h₁D h₂D h₁₂
  have hsubW := hpre.subset_of_closure_inter_subset hWo
    ⟨z, ⟨hz.1, fun h => hz.2 (hβ h)⟩, mem_connectedComponentIn hz⟩ ?_
  · exact hyz (hsubW ⟨hy.1, fun h => hy.2 (hβ h)⟩)
  rintro x ⟨hxcl, hxD, hxβ⟩
  by_cases hxσ : x ∈ range p
  · exfalso
    obtain ⟨v, rfl⟩ := hxσ
    have hxe : p.extend v = p v := Path.extend_extends' _ _
    rcases le_or_gt (v : ℝ) (t₀ - δ') with h | h
    · exact hxβ (Or.inl ⟨v, ⟨v.2.1, h⟩, hxe⟩)
    rcases le_or_gt (t₀ + δ') v with h' | h'
    · exact hxβ (Or.inr ⟨v, ⟨h', v.2.2⟩, hxe⟩)
    have hv : (v : ℝ) ∈ ball t₀ δ := by
      rw [Real.ball_eq_Ioo]; constructor <;> linarith
    exact hδO hv (hxe.symm ▸ hxcl)
  · exact mem_component_of_mem_closure hσc hxcl ⟨hxD, hxσ⟩

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
