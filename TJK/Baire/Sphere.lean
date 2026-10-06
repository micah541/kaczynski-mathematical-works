/-
Copyright: the TJK formalization project.

Section B of the blueprint (`paper/sections/B-baire.tex`), third part: points of continuity of
Baire-one functions (Baire–Kuratowski), functions of honorary Baire class two, and functions into
the Riemann sphere (the fold of Trans. AMS 141, (F)(I)).

As in `TJK.Baire.Basic`, metric hypotheses on the domain are replaced by `PerfectlyNormalSpace`
(plus `T1Space` where countable sets must be `F_σ`).
-/
import Mathlib
import TJK.Defs
import TJK.Baire.Basic
import TJK.Baire.Approx

open Set Filter Topology Function

namespace TJK

/-! ## Baire-one functions: elementary operations -/

section BaireOneOps

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
  {Z : Type*} [TopologicalSpace Z]

theorem IsBaireOne.comp_continuous {f : X → Y} (hf : IsBaireOne f) {g : Z → X}
    (hg : Continuous g) : IsBaireOne (f ∘ g) := by
  obtain ⟨F, hFc, hFt⟩ := hf
  exact ⟨fun n => F n ∘ g, fun n => (hFc n).comp hg, fun z => hFt (g z)⟩

theorem Continuous.comp_isBaireOne {g : Y → Z} (hg : Continuous g) {f : X → Y}
    (hf : IsBaireOne f) : IsBaireOne (g ∘ f) := by
  obtain ⟨F, hFc, hFt⟩ := hf
  exact ⟨fun n => g ∘ F n, fun n => hg.comp (hFc n),
    fun x => (hg.tendsto (f x)).comp (hFt x)⟩

/-- On the whole (perfectly normal) space, maps of class `F_σ` into `ℝ^m` are Baire-one. -/
theorem IsFσMeasurable.isBaireOne_pi [PerfectlyNormalSpace X] {m : ℕ} {f : X → Fin m → ℝ}
    (hf : IsFσMeasurable f) : IsBaireOne f :=
  TJK.isBaireOne_pi fun i =>
    TJK.IsFσMeasurable.isBaireOne_real (Continuous.comp_isFσMeasurable (continuous_apply i) hf)

end BaireOneOps

/-! ## Points of continuity (blueprint `thm:kuratowski`, `cor:baire-continuity-point`,
`lem:meager-subspace`) -/

section Continuity

variable {X : Type*} [TopologicalSpace X]

/-- A closed set minus its interior is nowhere dense. -/
theorem isNowhereDense_diff_interior {F : Set X} (hF : IsClosed F) :
    IsNowhereDense (F \ interior F) := by
  rw [(hF.sdiff isOpen_interior).isNowhereDense_iff, eq_empty_iff_forall_notMem]
  intro x hx
  have h1 : x ∈ interior F := interior_mono sdiff_subset hx
  exact (interior_subset hx).2 h1

/-- **Baire, Kuratowski.** The discontinuity set of a Baire-one function into a (pseudo)metric
space is meagre. -/
theorem IsBaireOne.meagre_discontinuity {Y : Type*} [PseudoMetricSpace Y] {f : X → Y}
    (hf : IsBaireOne f) : IsMeagre {x | ¬ ContinuousAt f x} := by
  obtain ⟨F, hFc, hFt⟩ := hf
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  let A : ℕ → ℕ → Set X := fun k N =>
    {x | ∀ n, N ≤ n → ∀ m, N ≤ m → dist (F n x) (F m x) ≤ ε k}
  have hA : ∀ k N, IsClosed (A k N) := fun k N => by
    simp only [A, ofPred_forall]
    exact isClosed_iInter fun n => isClosed_iInter fun _ => isClosed_iInter fun m =>
      isClosed_iInter fun _ => isClosed_le ((hFc n).dist (hFc m)) continuous_const
  have hcov : ∀ k x, ∃ N, x ∈ A k N := fun k x => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hFt x).cauchySeq _ (hε k)
    exact ⟨N, fun n hn m hm => (hN n hn m hm).le⟩
  refine IsMeagre.mono ?_ (isMeagre_iUnion fun k => isMeagre_iUnion fun N =>
    (isNowhereDense_diff_interior (hA k N)).isMeagre)
  intro x hx
  by_contra hmem
  have hmem' : ∀ k N, x ∈ A k N → x ∈ interior (A k N) := fun k N h => by
    by_contra h'
    exact hmem (mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨N, h, h'⟩⟩)
  apply hx
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hδ (by norm_num : (0 : ℝ) < 3))
  have hk' : ε k < δ / 3 := hk
  obtain ⟨N, hN⟩ := hcov k x
  have hint := hmem' k N hN
  -- on a neighbourhood of `x`, `f` is within `ε k` of `F N`
  have hnear : ∀ᶠ y in 𝓝 x, dist (f y) (F N y) ≤ ε k := by
    filter_upwards [mem_interior_iff_mem_nhds.1 hint] with y hy
    exact le_of_tendsto ((hFt y).dist tendsto_const_nhds)
      (eventually_atTop.2 ⟨N, fun n hn => hy n hn N le_rfl⟩)
  have hcont : ∀ᶠ y in 𝓝 x, dist (F N y) (F N x) < ε k :=
    Metric.tendsto_nhds.1 ((hFc N).continuousAt) _ (hε k)
  have hx0 : dist (F N x) (f x) ≤ ε k := by
    rw [dist_comm]
    exact hnear.self_of_nhds
  filter_upwards [hnear, hcont] with y h1 h2
  calc dist (f y) (f x) ≤ dist (f y) (F N y) + dist (F N y) (F N x) + dist (F N x) (f x) :=
        dist_triangle4 _ _ _ _
    _ < δ := by linarith

/-- A Baire-one function on a nonempty Baire space (e.g. a nonempty complete metric space) into a
(pseudo)metric space has a point of continuity. -/
theorem IsBaireOne.exists_continuousAt [BaireSpace X] [Nonempty X] {Y : Type*}
    [PseudoMetricSpace Y] {f : X → Y} (hf : IsBaireOne f) : ∃ x, ContinuousAt f x := by
  by_contra h
  push Not at h
  have hm := hf.meagre_discontinuity
  have : {x | ¬ ContinuousAt f x} = univ := eq_univ_of_forall h
  rw [this, IsMeagre, compl_univ] at hm
  have hd := dense_of_mem_residual hm
  obtain ⟨x⟩ := ‹Nonempty X›
  simpa using hd.nonempty

/-- A nowhere dense subset of a subspace `A` is nowhere dense in the ambient space. -/
theorem IsNowhereDense.image_val {A : Set X} {N : Set A} (hN : IsNowhereDense N) :
    IsNowhereDense (Subtype.val '' N) := by
  rw [IsNowhereDense, eq_empty_iff_forall_notMem]
  intro x hx
  have hO : IsOpen (interior (closure (Subtype.val '' N))) := isOpen_interior
  -- the open set `O` meets `N ⊆ A`
  obtain ⟨_, ⟨y, hyN, rfl⟩, hyO⟩ :
      ((Subtype.val '' N) ∩ interior (closure (Subtype.val '' N))).Nonempty := by
    have := mem_closure_iff.1 (interior_subset hx) _ hO hx
    obtain ⟨z, hzO, hzN⟩ := this
    exact ⟨z, hzN, hzO⟩
  have hsub : Subtype.val ⁻¹' interior (closure (Subtype.val '' N)) ⊆ interior (closure N) := by
    apply interior_maximal _ (hO.preimage continuous_subtype_val)
    intro z hz
    exact closure_subtype.2 (interior_subset hz)
  rw [IsNowhereDense] at hN
  exact (hN ▸ hsub hyO : y ∈ (∅ : Set A))

/-- A subset of `A ⊆ X` which is meagre in `A` is meagre in `X`. -/
theorem isMeagre_of_isMeagre_subtype {A : Set X} {N : Set A} (hN : IsMeagre N) :
    IsMeagre (Subtype.val '' N) := by
  obtain ⟨S, hS, hSc, hNS⟩ := isMeagre_iff_countable_union_isNowhereDense.1 hN
  refine isMeagre_iff_countable_union_isNowhereDense.2
    ⟨(fun t => Subtype.val '' t) '' S, ?_, hSc.image _, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (hS t ht).image_val
  · rw [sUnion_image]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hyt⟩ := mem_sUnion.1 (hNS hy)
    exact mem_iUnion₂.2 ⟨t, ht, y, hyt, rfl⟩

end Continuity

/-! ## Honorary Baire class two (blueprint `lem:honorary-invariance`, `thm:honorary-char`) -/

section Honorary

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
  {Z : Type*} [TopologicalSpace Z]

/-- Precomposition with a continuous injective map preserves honorary Baire class two. -/
theorem IsHonoraryBaireTwo.comp_continuous_injective {f : X → Y} (hf : IsHonoraryBaireTwo f)
    {h : Z → X} (hc : Continuous h) (hi : Injective h) : IsHonoraryBaireTwo (f ∘ h) := by
  obtain ⟨N, hN, g, hg, hfg⟩ := hf
  exact ⟨h ⁻¹' N, hN.preimage hi, g ∘ h, hg.comp_continuous hc, fun z hz => hfg (h z) hz⟩

/-- Restrictions of functions of honorary Baire class two are of honorary Baire class two. -/
theorem IsHonoraryBaireTwo.restrict {f : X → Y} (hf : IsHonoraryBaireTwo f) (s : Set X) :
    IsHonoraryBaireTwo (s.restrict f) :=
  hf.comp_continuous_injective continuous_subtype_val Subtype.val_injective

/-- Precomposition with a homeomorphism preserves honorary Baire class two. -/
theorem IsHonoraryBaireTwo.comp_homeomorph {f : X → Y} (hf : IsHonoraryBaireTwo f) (h : Z ≃ₜ X) :
    IsHonoraryBaireTwo (f ∘ h) :=
  hf.comp_continuous_injective h.continuous h.injective

/-- Postcomposition with a continuous map preserves honorary Baire class two. -/
theorem IsHonoraryBaireTwo.continuous_comp {f : X → Y} (hf : IsHonoraryBaireTwo f) {g : Y → Z}
    (hg : Continuous g) : IsHonoraryBaireTwo (g ∘ f) := by
  obtain ⟨N, hN, f', hf', hff'⟩ := hf
  exact ⟨N, hN, g ∘ f', Continuous.comp_isBaireOne hg hf', fun x hx => by simp [hff' x hx]⟩

/-- For a countable `N` (in a `T₁` space), `f` is of class `F_σ` on `X \ N` iff `f⁻¹(F) \ N` is
`G_δ` in `X` for every closed `F`. -/
theorem isFσMeasurable_restrict_compl_iff [T1Space X] {N : Set X} (hN : N.Countable)
    (f : X → Y) :
    IsFσMeasurable (Nᶜ.restrict f) ↔ ∀ F : Set Y, IsClosed F → IsGδ (f ⁻¹' F \ N) := by
  constructor
  · intro hf F hF
    have h1 : IsGδ (Nᶜ.restrict f ⁻¹' F) := by
      rw [← isFσ_compl_iff, ← preimage_compl]
      exact hf _ hF.isOpen_compl
    have h2 := IsGδ.of_subtype hN.isGδ_compl h1
    convert h2 using 1
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
  · intro hF U hU
    rw [← isGδ_compl_iff, ← preimage_compl]
    convert (hF _ hU.isClosed_compl).preimage continuous_subtype_val using 1
    ext x
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

theorem exists_countable_isFσMeasurable_iff [T1Space X] (f : X → Y) :
    (∃ N : Set X, N.Countable ∧ IsFσMeasurable (Nᶜ.restrict f)) ↔
      ∃ N : Set X, N.Countable ∧ ∀ F : Set Y, IsClosed F → IsGδ (f ⁻¹' F \ N) := by
  constructor
  · rintro ⟨N, hN, h⟩
    exact ⟨N, hN, (isFσMeasurable_restrict_compl_iff hN f).1 h⟩
  · rintro ⟨N, hN, h⟩
    exact ⟨N, hN, (isFσMeasurable_restrict_compl_iff hN f).2 h⟩

/-- **Characterisation of honorary Baire class two**, for any target `Y` in which maps of class
`F_σ` on co-countable sets extend to Baire-one maps. -/
theorem isHonoraryBaireTwo_tfae_of_extend [T1Space X] [PerfectlyNormalSpace Y] (f : X → Y)
    (hext : ∀ N : Set X, N.Countable → IsFσMeasurable (Nᶜ.restrict f) →
      ∃ g : X → Y, IsBaireOne g ∧ ∀ x : ↥Nᶜ, g x = f x) :
    List.TFAE [IsHonoraryBaireTwo f,
      ∃ N : Set X, N.Countable ∧ IsFσMeasurable (Nᶜ.restrict f),
      ∃ N : Set X, N.Countable ∧ ∀ F : Set Y, IsClosed F → IsGδ (f ⁻¹' F \ N)] := by
  tfae_have 1 → 2 := by
    rintro ⟨N, hN, g, hg, hfg⟩
    refine ⟨N, hN, ?_⟩
    have : Nᶜ.restrict f = Nᶜ.restrict g := funext fun x => hfg x x.2
    rw [this]
    exact (hg.comp_continuous continuous_subtype_val).isFσMeasurable
  tfae_have 2 → 1 := by
    rintro ⟨N, hN, h⟩
    obtain ⟨g, hg, hgf⟩ := hext N hN h
    exact ⟨N, hN, g, hg, fun x hx => (hgf ⟨x, hx⟩).symm⟩
  tfae_have 2 ↔ 3 := exists_countable_isFσMeasurable_iff f
  tfae_finish

/-- Maps into `ℝ^m` of class `F_σ` off a countable set extend to Baire-one maps. -/
theorem exists_isBaireOne_eq_of_countable [PerfectlyNormalSpace X] [T1Space X] {m : ℕ}
    {f : X → Fin m → ℝ} {N : Set X} (hN : N.Countable) (h : IsFσMeasurable (Nᶜ.restrict f)) :
    ∃ g : X → Fin m → ℝ, IsBaireOne g ∧ ∀ x : ↥Nᶜ, g x = f x := by
  have hB : IsBaireOne (Nᶜ.restrict f) := ((baireOne_tfae (L := Nᶜ) (Nᶜ.restrict f)).out 0 1).2 h
  exact IsBaireOne.extend_of_countable_compl (by rwa [compl_compl]) hB

/-- **Honorary Baire class two, `ℝ^m`-valued** (`Fin m → ℝ` model). -/
theorem isHonoraryBaireTwo_tfae_pi [PerfectlyNormalSpace X] [T1Space X] {m : ℕ}
    (f : X → Fin m → ℝ) :
    List.TFAE [IsHonoraryBaireTwo f,
      ∃ N : Set X, N.Countable ∧ IsFσMeasurable (Nᶜ.restrict f),
      ∃ N : Set X, N.Countable ∧ ∀ F : Set (Fin m → ℝ), IsClosed F → IsGδ (f ⁻¹' F \ N)] :=
  isHonoraryBaireTwo_tfae_of_extend f fun _ hN h => exists_isBaireOne_eq_of_countable hN h

/-- **Honorary Baire class two, `ℝ^m`-valued** (`EuclideanSpace` model). -/
theorem isHonoraryBaireTwo_tfae_euclidean [PerfectlyNormalSpace X] [T1Space X] {m : ℕ}
    (f : X → EuclideanSpace ℝ (Fin m)) :
    List.TFAE [IsHonoraryBaireTwo f,
      ∃ N : Set X, N.Countable ∧ IsFσMeasurable (Nᶜ.restrict f),
      ∃ N : Set X, N.Countable ∧
        ∀ F : Set (EuclideanSpace ℝ (Fin m)), IsClosed F → IsGδ (f ⁻¹' F \ N)] := by
  let e := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  refine isHonoraryBaireTwo_tfae_of_extend f fun N hN h => ?_
  have h' : IsFσMeasurable (Nᶜ.restrict (e ∘ f)) :=
    Continuous.comp_isFσMeasurable (f := Nᶜ.restrict f) e.continuous h
  obtain ⟨g, hg, hgf⟩ := exists_isBaireOne_eq_of_countable hN h'
  refine ⟨e.symm ∘ g, Continuous.comp_isBaireOne e.symm.continuous hg, fun x => ?_⟩
  simp [hgf x, e]

end Honorary

/-! ## Functions into the sphere: the fold (blueprint `def:fold`, `lem:fold`,
`lem:fold-factor`) -/

namespace Fold

open Real Metric

local notation "𝔼³" => EuclideanSpace ℝ (Fin 3)

noncomputable def s : ℝ := √2 / 2

theorem s_pos : 0 < s := by unfold s; positivity

theorem s_sq : s ^ 2 = 1 / 2 := by
  unfold s; rw [div_pow, sq_sqrt (by norm_num)]; norm_num

theorem s_lt_one : s < 1 := by nlinarith [s_sq, s_pos]

theorem mem_sphere_iff' (v : 𝔼³) :
    v ∈ sphere (0 : 𝔼³) 1 ↔ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]; simp
  rw [← h]
  constructor
  · intro h1; rw [h1]; norm_num
  · intro h1
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h1]; norm_num)

noncomputable def κ (z : ℝ) : ℝ := max 0 (2 * z ^ 2 - 1)

noncomputable def foldE (v : 𝔼³) : 𝔼³ :=
  !₂[v 0 * (1 + 2 * κ (v 2)), v 1 * (1 + 2 * κ (v 2)), v 2 * (2 * κ (v 2) - 1)]

theorem continuous_κ : Continuous κ := by unfold κ; fun_prop

theorem continuous_foldE : Continuous foldE := by
  unfold foldE
  have := continuous_κ
  fun_prop

theorem foldE_mem {v : 𝔼³} (hv : v ∈ sphere (0 : 𝔼³) 1) : foldE v ∈ sphere (0 : 𝔼³) 1 := by
  rw [mem_sphere_iff'] at hv ⊢
  simp only [foldE]
  simp
  rcases le_total 0 (2 * v 2 ^ 2 - 1) with h | h
  · rw [κ, max_eq_right h]
    linear_combination (4 * v 2 ^ 2 - 1) ^ 2 * hv
  · rw [κ, max_eq_left h]
    linear_combination hv

theorem cos_pi_div_four' : cos (π / 4) = s := cos_pi_div_four

theorem arccos_s : arccos s = π / 4 := by
  rw [← cos_pi_div_four']
  exact arccos_cos (by positivity) (by linarith [pi_pos])

/-- The inverse of `T(z) = 4z³ - 3z` on `[s, 1]`, defined on `(-s, 1]`. -/
theorem cubic_inv {y : ℝ} (hy1 : y ≤ 1) (hys : -s < y) :
    s < cos (arccos y / 3) ∧ 4 * cos (arccos y / 3) ^ 3 - 3 * cos (arccos y / 3) = y := by
  have hs := s_pos
  have hsl := s_lt_one
  have h1 : arccos y < 3 * π / 4 := by
    have := arccos_lt_arccos (by linarith) hys hy1
    rw [arccos_neg, arccos_s] at this
    linarith
  constructor
  · rw [← cos_pi_div_four']
    exact cos_lt_cos_of_nonneg_of_le_pi (by have := arccos_nonneg y; positivity)
      (by linarith [pi_pos]) (by linarith)
  · rw [← cos_three_mul, mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0),
      cos_arccos (by linarith) hy1]

/-- The cubic identity behind the fold. -/
theorem cubic_identity (w : ℝ) :
    (1 - w ^ 2) * (4 * w ^ 2 - 1) ^ 2 + (4 * w ^ 3 - 3 * w) ^ 2 = 1 := by ring

/-- The candidate inverse of the fold, with sign `e = ±1`. -/
noncomputable def secE (e : ℝ) (v : 𝔼³) : 𝔼³ :=
  !₂[v 0 / (4 * cos (arccos (e * v 2) / 3) ^ 2 - 1),
    v 1 / (4 * cos (arccos (e * v 2) / 3) ^ 2 - 1), e * cos (arccos (e * v 2) / 3)]

theorem coord_le_one {v : 𝔼³} (hv : v ∈ sphere (0 : 𝔼³) 1) (i : Fin 3) : |v i| ≤ 1 := by
  rw [mem_sphere_iff'] at hv
  apply (sq_le_one_iff_abs_le_one _).1
  have h0 := sq_nonneg (v 0)
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  fin_cases i
  · change v 0 ^ 2 ≤ 1; linarith
  · change v 1 ^ 2 ≤ 1; linarith
  · change v 2 ^ 2 ≤ 1; linarith

theorem secE_spec {e : ℝ} (he : e ^ 2 = 1) {v : 𝔼³} (hv : v ∈ sphere (0 : 𝔼³) 1)
    (h : -s < e * v 2) :
    secE e v ∈ sphere (0 : 𝔼³) 1 ∧ foldE (secE e v) = v ∧ s < e * secE e v 2 := by
  have hb := coord_le_one hv 2
  have he1 : |e| = 1 := by
    have := abs_nonneg e
    nlinarith [sq_abs e]
  have hy1 : e * v 2 ≤ 1 := by
    calc e * v 2 ≤ |e * v 2| := le_abs_self _
      _ = |v 2| := by rw [abs_mul, he1, one_mul]
      _ ≤ 1 := hb
  obtain ⟨hw, hT⟩ := cubic_inv hy1 h
  set w := cos (arccos (e * v 2) / 3) with hwdef
  have hs := s_pos
  have hw2 : 1 / 2 < w ^ 2 := by nlinarith [s_sq]
  have hc : 1 < 4 * w ^ 2 - 1 := by linarith
  have hc0 : 4 * w ^ 2 - 1 ≠ 0 := by linarith
  have hsph := (mem_sphere_iff' v).1 hv
  have hz : v 2 ^ 2 = (4 * w ^ 3 - 3 * w) ^ 2 := by
    rw [hT]; linear_combination (-(v 2) ^ 2) * he
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_sphere_iff']
    simp only [secE, ← hwdef]
    simp
    rw [div_pow, div_pow, mul_pow, he]
    field_simp
    linear_combination hsph - hz
  · have hκ : κ (e * w) = 2 * w ^ 2 - 1 := by
      rw [κ, max_eq_right (by nlinarith), mul_pow, he, one_mul]
    simp only [secE, ← hwdef, foldE]
    ext i
    fin_cases i
    · simp [hκ]; field_simp; ring
    · simp [hκ]; field_simp; ring
    · simp [hκ]
      linear_combination e * hT + (v 2) * he
  · simp only [secE, ← hwdef]
    simp
    rw [← mul_assoc, ← sq, he, one_mul]
    exact hw

/-- The height (third coordinate) of a point of the sphere. -/
def zc (p : Sphere2) : ℝ := (p : 𝔼³) 2

theorem continuous_zc : Continuous zc := by unfold zc; fun_prop

/-- **The fold** `Φ : 𝕊² → 𝕊²`. -/
noncomputable def fold (p : Sphere2) : Sphere2 := ⟨foldE p, foldE_mem p.2⟩

theorem continuous_fold : Continuous fold :=
  (continuous_foldE.comp continuous_subtype_val).subtype_mk _

def U : Set Sphere2 := {p | -s < zc p}
def V : Set Sphere2 := {p | zc p < s}
def ZU : Set Sphere2 := {p | s < zc p}
def ZV : Set Sphere2 := {p | zc p < -s}

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const continuous_zc
theorem isOpen_V : IsOpen V := isOpen_lt continuous_zc continuous_const

theorem U_union_V : U ∪ V = univ := by
  refine eq_univ_of_forall fun p => ?_
  have := s_pos
  by_cases h : zc p < s
  · exact Or.inr h
  · exact Or.inl (show -s < zc p by linarith [not_lt.1 h])

/-- The inverse branch of the fold with sign `e = ±1`, on `{-s < e z}`. -/
noncomputable def sec (e : ℝ) (he : e ^ 2 = 1) (p : Sphere2) : Sphere2 :=
  if h : -s < e * zc p then ⟨secE e p, (secE_spec he p.2 h).1⟩ else p

theorem fold_sec {e : ℝ} (he : e ^ 2 = 1) {p : Sphere2} (h : -s < e * zc p) :
    fold (sec e he p) = p := by
  simp only [sec, dif_pos h]
  exact Subtype.ext (secE_spec he p.2 h).2.1

theorem sec_mem {e : ℝ} (he : e ^ 2 = 1) {p : Sphere2} (h : -s < e * zc p) :
    s < e * zc (sec e he p) := by
  simp only [sec, dif_pos h]
  exact (secE_spec he p.2 h).2.2

theorem continuousOn_sec {e : ℝ} (he : e ^ 2 = 1) :
    ContinuousOn (sec e he) {p | -s < e * zc p} := by
  rw [continuousOn_iff_continuous_domRestrict]
  set W := {p : Sphere2 | -s < e * zc p}
  have hz : Continuous fun q : W => (q : 𝔼³) 2 := by fun_prop
  have hw : Continuous fun q : W => cos (arccos (e * (q : 𝔼³) 2) / 3) :=
    continuous_cos.comp ((continuous_arccos.comp (continuous_const.mul hz)).div_const 3)
  have hc : ∀ q : W, 4 * cos (arccos (e * (q : 𝔼³) 2) / 3) ^ 2 - 1 ≠ 0 := by
    intro q
    have hb := coord_le_one q.1.2 2
    have he1 : |e| = 1 := by
      have := abs_nonneg e
      nlinarith [sq_abs e]
    have hy1 : e * (q : 𝔼³) 2 ≤ 1 :=
      calc e * (q : 𝔼³) 2 ≤ |e * (q : 𝔼³) 2| := le_abs_self _
        _ = |(q : 𝔼³) 2| := by rw [abs_mul, he1, one_mul]
        _ ≤ 1 := hb
    obtain ⟨hw, -⟩ := cubic_inv hy1 q.2
    nlinarith [s_sq, s_pos]
  have hE : Continuous fun q : W => secE e q := by
    have h0 : Continuous fun q : W => (q : 𝔼³) 0 := by fun_prop
    have h1 : Continuous fun q : W => (q : 𝔼³) 1 := by fun_prop
    have hc' : Continuous fun q : W => 4 * cos (arccos (e * (q : 𝔼³) 2) / 3) ^ 2 - 1 := by
      fun_prop
    have ha := h0.div hc' hc
    have hb := h1.div hc' hc
    have hd := continuous_const.mul hw (f := fun _ : W => e)
    unfold secE
    fun_prop
  have : W.domRestrict (sec e he) = fun q => ⟨secE e q, (secE_spec he q.1.2 q.2).1⟩ := by
    funext q
    simp only [domRestrict_apply, sec]
    exact dif_pos q.2
  rw [this]
  exact hE.subtype_mk _

/-- The inverse of `fold` on `U`, with values in `Z_U`. -/
noncomputable def secU : Sphere2 → Sphere2 := sec 1 (by norm_num)

/-- The inverse of `fold` on `V`, with values in `Z_V`. -/
noncomputable def secV : Sphere2 → Sphere2 := sec (-1) (by norm_num)

theorem fold_secU {p : Sphere2} (hp : p ∈ U) : fold (secU p) = p :=
  fold_sec _ (by simpa [U] using hp)

theorem fold_secV {p : Sphere2} (hp : p ∈ V) : fold (secV p) = p :=
  fold_sec _ (by simpa [V] using hp)

theorem secU_mem_ZU {p : Sphere2} (hp : p ∈ U) : secU p ∈ ZU := by
  have := sec_mem (e := 1) (by norm_num) (p := p) (by simpa [U] using hp)
  rw [one_mul] at this
  exact this

theorem secV_mem_ZV {p : Sphere2} (hp : p ∈ V) : secV p ∈ ZV := by
  have := sec_mem (e := -1) (by norm_num) (p := p) (by simpa [V] using hp)
  simp only [ZV, mem_ofPred_eq]
  change s < -1 * zc (secV p) at this
  linarith

theorem continuousOn_secU : ContinuousOn secU U := by
  have := continuousOn_sec (e := 1) (by norm_num)
  simp only [one_mul] at this
  exact this

theorem continuousOn_secV : ContinuousOn secV V := by
  have := continuousOn_sec (e := -1) (by norm_num)
  have e : {p : Sphere2 | -s < -1 * zc p} = V := by
    ext p; simp only [V, mem_ofPred_eq]; constructor <;> intro h <;> linarith
  rw [e] at this
  exact this

theorem fold_surjOn : SurjOn fold (ZU ∪ ZV) univ := by
  intro q _
  by_cases hq : q ∈ U
  · exact ⟨secU q, Or.inl (secU_mem_ZU hq), fold_secU hq⟩
  · have hV : q ∈ V := (U_union_V ▸ mem_univ q : q ∈ U ∪ V).resolve_left hq
    exact ⟨secV q, Or.inr (secV_mem_ZV hV), fold_secV hV⟩

theorem fold_coord (p : Sphere2) (i : Fin 3) :
    ((fold p : Sphere2) : 𝔼³) i = ![(p : 𝔼³) 0 * (1 + 2 * κ (zc p)),
      (p : 𝔼³) 1 * (1 + 2 * κ (zc p)), zc p * (2 * κ (zc p) - 1)] i := by
  fin_cases i <;> rfl

theorem κ_nonneg (z : ℝ) : 0 ≤ κ z := le_max_left _ _

theorem fold_eq_of_zc_eq {p q : Sphere2} (h : fold p = fold q) (hz : zc p = zc q) : p = q := by
  have hc : (1 + 2 * κ (zc p)) ≠ 0 := by linarith [κ_nonneg (zc p)]
  have h0 := congrArg (fun r : Sphere2 => (r : 𝔼³) 0) h
  have h1 := congrArg (fun r : Sphere2 => (r : 𝔼³) 1) h
  simp only [fold_coord, ← hz] at h0 h1
  simp at h0 h1
  apply Subtype.ext
  ext i
  fin_cases i
  · exact h0.resolve_right hc
  · exact h1.resolve_right hc
  · exact hz

theorem zc_fold (p : Sphere2) : zc (fold p) = zc p * (2 * κ (zc p) - 1) := fold_coord p 2

theorem cubic_inj {a b : ℝ} (ha : 1 / 2 < a ^ 2) (hb : 1 / 2 < b ^ 2) (hab : 0 < a * b)
    (h : a * (2 * (2 * a ^ 2 - 1) - 1) = b * (2 * (2 * b ^ 2 - 1) - 1)) : a = b := by
  have : (a - b) * (4 * (a ^ 2 + a * b + b ^ 2) - 3) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · nlinarith

theorem injOn_fold_of {R : Set Sphere2}
    (hR : ∀ a ∈ R, ∀ b ∈ R, zc (fold a) = zc (fold b) → zc a = zc b) :
    ∀ a ∈ R, ∀ b ∈ R, fold a = fold b → a = b :=
  fun a ha b hb h => fold_eq_of_zc_eq h (hR a ha b hb (congrArg zc h))

theorem κ_of_le {z : ℝ} (h : s ≤ |z|) : κ z = 2 * z ^ 2 - 1 := by
  have := s_pos
  have : s ^ 2 ≤ z ^ 2 := by rw [← sq_abs z]; exact pow_le_pow_left₀ this.le h 2
  rw [κ, max_eq_right]
  nlinarith [s_sq]

theorem κ_of_ge {z : ℝ} (h : |z| ≤ s) : κ z = 0 := by
  have := s_pos
  have : z ^ 2 ≤ s ^ 2 := by rw [← sq_abs z]; exact pow_le_pow_left₀ (abs_nonneg z) h 2
  rw [κ, max_eq_left]
  nlinarith [s_sq]

/-- Each fibre of the fold has at most three points. -/
theorem fibre_card_le_three (q : Sphere2) : (fold ⁻¹' {q}).encard ≤ 3 := by
  have key : ∀ R : Set Sphere2, (∀ a ∈ R, ∀ b ∈ R, fold a = fold b → a = b) →
      (fold ⁻¹' {q} ∩ R).encard ≤ 1 := fun R hR =>
    encard_le_one_iff.2 fun a b ha hb => hR a ha.2 b hb.2 (ha.1.trans hb.1.symm)
  have hs := s_pos
  have hU : (fold ⁻¹' {q} ∩ ZU).encard ≤ 1 := by
    refine key _ (injOn_fold_of fun a ha b hb h => ?_)
    simp only [ZU, mem_ofPred_eq] at ha hb
    rw [zc_fold, zc_fold, κ_of_le (by rw [abs_of_pos (by linarith)]; linarith),
      κ_of_le (by rw [abs_of_pos (by linarith)]; linarith)] at h
    exact cubic_inj (by nlinarith [s_sq]) (by nlinarith [s_sq]) (by nlinarith) h
  have hV : (fold ⁻¹' {q} ∩ ZV).encard ≤ 1 := by
    refine key _ (injOn_fold_of fun a ha b hb h => ?_)
    simp only [ZV, mem_ofPred_eq] at ha hb
    rw [zc_fold, zc_fold, κ_of_le (by rw [abs_of_neg (by linarith)]; linarith),
      κ_of_le (by rw [abs_of_neg (by linarith)]; linarith)] at h
    exact cubic_inj (by nlinarith [s_sq]) (by nlinarith [s_sq]) (by nlinarith) h
  have hB : (fold ⁻¹' {q} ∩ {p | |zc p| ≤ s}).encard ≤ 1 := by
    refine key _ (injOn_fold_of fun a ha b hb h => ?_)
    simp only [mem_ofPred_eq] at ha hb
    rw [zc_fold, zc_fold, κ_of_ge ha, κ_of_ge hb] at h
    linarith
  have hcov : fold ⁻¹' {q} ⊆
      (fold ⁻¹' {q} ∩ ZU ∪ fold ⁻¹' {q} ∩ {p | |zc p| ≤ s}) ∪ fold ⁻¹' {q} ∩ ZV := by
    intro p hp
    simp only [ZU, ZV, mem_union, mem_inter_iff, mem_ofPred_eq]
    rcases lt_or_ge s (zc p) with h | h
    · exact Or.inl (Or.inl ⟨hp, h⟩)
    rcases lt_or_ge (zc p) (-s) with h' | h'
    · exact Or.inr ⟨hp, h'⟩
    · exact Or.inl (Or.inr ⟨hp, abs_le.2 ⟨h', h⟩⟩)
  calc (fold ⁻¹' {q}).encard ≤ _ := encard_le_encard hcov
    _ ≤ (fold ⁻¹' {q} ∩ ZU).encard + (fold ⁻¹' {q} ∩ {p | |zc p| ≤ s}).encard +
        (fold ⁻¹' {q} ∩ ZV).encard :=
      (encard_union_le _ _).trans (add_le_add_left (encard_union_le _ _) _)
    _ ≤ 1 + 1 + 1 := add_le_add (add_le_add hU hB) hV
    _ = 3 := by norm_num

instance fact_finrank_three : Fact (Module.finrank ℝ 𝔼³ = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

/-- The point `p₁ = ⟨1, 0, 0⟩`. -/
noncomputable def p₁ : Sphere2 := ⟨!₂[1, 0, 0], by rw [mem_sphere_iff']; simp⟩

theorem zc_p₁ : zc p₁ = 0 := rfl

/-- The chart `σ : 𝕊² \ {p₁} → ℝ²`: stereographic projection from `p₁`, with values in the
`Fin 2 → ℝ` model of `ℝ²`. -/
noncomputable def chart (p : Sphere2) : Fin 2 → ℝ :=
  EuclideanSpace.equiv (Fin 2) ℝ (stereographic' 2 p₁ p)

/-- The inverse of the chart, `ℝ² → 𝕊² \ {p₁}`. -/
noncomputable def chartInv (v : Fin 2 → ℝ) : Sphere2 :=
  (stereographic' 2 p₁).symm ((EuclideanSpace.equiv (Fin 2) ℝ).symm v)

theorem continuous_chartInv : Continuous chartInv := by
  have h := (stereographic' 2 p₁).continuousOn_symm
  rw [stereographic'_target, continuousOn_univ] at h
  exact h.comp (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous

theorem continuousOn_chart : ContinuousOn chart {p₁}ᶜ := by
  have h := (stereographic' 2 p₁).continuousOn
  rw [stereographic'_source] at h
  exact (EuclideanSpace.equiv (Fin 2) ℝ).continuous.comp_continuousOn h

theorem chartInv_chart {p : Sphere2} (hp : p ≠ p₁) : chartInv (chart p) = p := by
  simp only [chartInv, chart, ContinuousLinearEquiv.symm_apply_apply]
  exact (stereographic' 2 p₁).left_inv (by rw [stereographic'_source]; exact hp)

theorem ne_p₁_of_mem {p : Sphere2} (hp : p ∈ ZU ∪ ZV) : p ≠ p₁ := by
  rintro rfl
  have := s_pos
  rcases hp with h | h <;> simp only [ZU, ZV, mem_ofPred_eq, zc_p₁] at h <;> linarith

/-- The chart is bounded on `Z_U ∪ Z_V`. -/
theorem bounded_chart : Bornology.IsBounded (chart '' (ZU ∪ ZV)) := by
  let C : Set Sphere2 := {p | s ≤ |zc p|}
  have hC : IsCompact C :=
    (isClosed_le continuous_const continuous_zc.abs).isCompact
  have hC1 : C ⊆ {p₁}ᶜ := by
    intro p hp hp1
    rw [mem_singleton_iff] at hp1
    subst hp1
    simp only [C, mem_ofPred_eq, zc_p₁, abs_zero] at hp
    linarith [s_pos]
  have hsub : ZU ∪ ZV ⊆ C := by
    have := s_pos
    rintro p (h | h) <;> simp only [ZU, ZV, C, mem_ofPred_eq] at h ⊢
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  exact ((hC.image_of_continuousOn (continuousOn_chart.mono hC1)).isBounded).subset
    (image_mono hsub)

/-- **Fold factorisation.** A map of class `F_σ` into the sphere factors as `fold ∘ ψ`, with
`ψ` of class `F_σ` with values in `Z_U ∪ Z_V`, so that `chart ∘ ψ` is bounded and of class
`F_σ`. -/
theorem exists_factor {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]
    {f : X → Sphere2} (hf : IsFσMeasurable f) :
    ∃ ψ : X → Sphere2, (∀ x, ψ x ∈ ZU ∪ ZV) ∧ (∀ x, fold (ψ x) = f x) ∧ IsFσMeasurable ψ ∧
      IsFσMeasurable (chart ∘ ψ) := by
  classical
  have hE : IsGδ (f ⁻¹' V)ᶜ := (hf V isOpen_V).isGδ_compl
  have hEF : (f ⁻¹' V)ᶜ ⊆ f ⁻¹' U := fun x hx =>
    (U_union_V ▸ mem_univ (f x) : f x ∈ U ∪ V).resolve_right hx
  obtain ⟨K, hK, hEK, hKF⟩ := sierpinski_ambiguous hE (hf U isOpen_U) hEF
  have hKV : ∀ x, x ∉ K → f x ∈ V := fun x hx => by_contra fun h => hx (hEK h)
  let ψ : X → Sphere2 := fun x => if x ∈ K then secU (f x) else secV (f x)
  have hψmem : ∀ x, ψ x ∈ ZU ∪ ZV := fun x => by
    by_cases hx : x ∈ K
    · simp only [ψ, if_pos hx]; exact Or.inl (secU_mem_ZU (hKF hx))
    · simp only [ψ, if_neg hx]; exact Or.inr (secV_mem_ZV (hKV x hx))
  have hψF : IsFσMeasurable ψ := by
    intro W hW
    have e : ψ ⁻¹' W = (K ∩ f ⁻¹' (U ∩ secU ⁻¹' W)) ∪ (Kᶜ ∩ f ⁻¹' (V ∩ secV ⁻¹' W)) := by
      ext x
      by_cases hx : x ∈ K
      · simp [ψ, hx, hKF hx]
      · simp [ψ, hx, hKV x hx]
    rw [e]
    exact (hK.1.inter (hf _ (continuousOn_secU.isOpen_inter_preimage isOpen_U hW))).union
      ((IsGδ.isFσ_compl hK.2).inter (hf _ (continuousOn_secV.isOpen_inter_preimage isOpen_V hW)))
  refine ⟨ψ, hψmem, fun x => ?_, hψF, fun G hG => ?_⟩
  · by_cases hx : x ∈ K
    · simp only [ψ, if_pos hx]; exact fold_secU (hKF hx)
    · simp only [ψ, if_neg hx]; exact fold_secV (hKV x hx)
  · have : (chart ∘ ψ) ⁻¹' G = ψ ⁻¹' ({p₁}ᶜ ∩ chart ⁻¹' G) := by
      ext x
      simp [ne_p₁_of_mem (hψmem x)]
    rw [this]
    exact hψF _ (continuousOn_chart.isOpen_inter_preimage isOpen_compl_singleton hG)

theorem continuous_fold_chartInv : Continuous (fold ∘ chartInv) :=
  continuous_fold.comp continuous_chartInv

end Fold

/-! ## Baire-one maps into the sphere (blueprint `thm:sphere-baire1`, `thm:sphere-extension`) -/

section SphereBaire

variable {X : Type*} [TopologicalSpace X] [PerfectlyNormalSpace X]

/-- **Trans. AMS 141, Appendix (a).** A map into the sphere is Baire-one iff it is of class
`F_σ`. -/
theorem sphere_baireOne_iff (f : X → Sphere2) : IsBaireOne f ↔ IsFσMeasurable f := by
  refine ⟨IsBaireOne.isFσMeasurable, fun hf => ?_⟩
  obtain ⟨ψ, hψ, hfψ, -, hc⟩ := Fold.exists_factor hf
  obtain ⟨G, hGc, hGt⟩ := hc.isBaireOne_pi
  refine ⟨fun n => (Fold.fold ∘ Fold.chartInv) ∘ G n,
    fun n => Fold.continuous_fold_chartInv.comp (hGc n), fun x => ?_⟩
  have := (Fold.continuous_fold_chartInv.tendsto _).comp (hGt x)
  simp only [Function.comp_apply, Fold.chartInv_chart (Fold.ne_p₁_of_mem (hψ x)), hfψ] at this
  exact this

/-- **Trans. AMS 141, Appendix (c).** A Baire-one map from a `G_δ` subset `E` into the sphere
extends to a Baire-one map on the whole space. -/
theorem sphere_baireOne_extend {E : Set X} (hE : IsGδ E) {f : E → Sphere2} (hf : IsBaireOne f) :
    ∃ F : X → Sphere2, IsBaireOne F ∧ ∀ x : E, F x = f x := by
  obtain ⟨ψ, hψ, hfψ, -, hc⟩ := Fold.exists_factor hf.isFσMeasurable
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 Fold.bounded_chart
  obtain ⟨G, hG, -, hGe⟩ := IsBaireOne.extend_of_isGδ hE hc.isBaireOne_pi
    ⟨C, fun x => hC _ ⟨ψ x, hψ x, rfl⟩⟩
  refine ⟨(Fold.fold ∘ Fold.chartInv) ∘ G,
    Continuous.comp_isBaireOne Fold.continuous_fold_chartInv hG, fun x => ?_⟩
  simp [hGe x, Fold.chartInv_chart (Fold.ne_p₁_of_mem (hψ x)), hfψ]

/-- **Honorary Baire class two, sphere-valued** (Diss. Theorem 2, Trans. AMS 141 Appendix (b)). -/
theorem isHonoraryBaireTwo_tfae_sphere [T1Space X] (f : X → Sphere2) :
    List.TFAE [IsHonoraryBaireTwo f,
      ∃ N : Set X, N.Countable ∧ IsFσMeasurable (Nᶜ.restrict f),
      ∃ N : Set X, N.Countable ∧ ∀ F : Set Sphere2, IsClosed F → IsGδ (f ⁻¹' F \ N)] :=
  isHonoraryBaireTwo_tfae_of_extend f fun _ hN h =>
    sphere_baireOne_extend hN.isGδ_compl ((sphere_baireOne_iff _).2 h)

end SphereBaire

end TJK
