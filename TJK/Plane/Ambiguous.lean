import Mathlib
import TJK.Defs
import TJK.Plane.Basic

/-!
# Ambiguous points of continuous functions (blueprint `lem:two-domains`, `fact:bagemihl`)

* `accessible_two_domains` (`lem:two-domains`): at most three points of `C` are accessible from
  both of two disjoint connected open subsets of `𝔻`; the proof uses the crosscut theorem.
* `ambiguous_countable` (`fact:bagemihl`, continuous case of Bagemihl's ambiguous point theorem):
  for `f` continuous in `𝔻`, the points of `C` with two arcs along which `f` has different limits
  form a countable set.
-/

namespace TJK

open _root_.Set Filter Topology

/-- `x` is accessible from `W` by a path: `g 0 = x` and `g ((0, 1]) ⊆ W`. -/
def PathAccessible (W : Set ℂ) (x : ℂ) : Prop :=
  ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = x ∧ g '' Ioc 0 1 ⊆ W

/-! ### Auxiliary lemmas -/

open scoped Real

theorem not_mem_disc_of_mem_circle {z : ℂ} (hz : z ∈ circle) : z ∉ disc := fun h => by
  have h1 : ‖z‖ < 1 := mem_ball_zero_iff.1 h
  have h2 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
  linarith

/-- Two angles closer than `2π` with the same point `e^{it}` are equal. -/
theorem eq_of_expI_eq {s t : ℝ} (h : expI s = expI t) (h1 : |s - t| < 2 * π) : s = t := by
  rw [expI, expI, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  have him := congrArg Complex.im hk
  simp at him
  have hp := Real.two_pi_pos
  rw [abs_lt] at h1
  have a1 : (k : ℝ) < 1 := by nlinarith
  have a2 : (-1 : ℝ) < k := by nlinarith
  have b1 : k < 1 := by exact_mod_cast a1
  have b2 : -1 < k := by exact_mod_cast a2
  have hk0 : k = 0 := by omega
  rw [hk0] at him
  simpa using him

/-- A point of `C` other than `e^{iθ}` is `e^{ia}` with `θ < a < θ + 2π`. -/
theorem exists_angle_Ioo (θ : ℝ) {p : ℂ} (hp : p ∈ circle) (hpx : p ≠ expI θ) :
    ∃ a ∈ Ioo θ (θ + 2 * π), expI a = p := by
  have h1 := expI_arg (mem_sphere_zero_iff_norm.1 hp)
  have hI := toIcoMod_mem_Ico Real.two_pi_pos θ (Complex.arg p)
  have hk := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos θ (Complex.arg p)
  rw [zsmul_eq_mul] at hk
  set a := toIcoMod Real.two_pi_pos θ (Complex.arg p)
  have he : expI a = p := by
    rw [← h1, ← expI_add_int_mul a (toIcoDiv Real.two_pi_pos θ (Complex.arg p))]
    congr 1
  refine ⟨a, ⟨lt_of_le_of_ne hI.1 fun h => hpx ?_, hI.2⟩, he⟩
  rw [← he, h]

/-- A function continuous on `[0, 1]` gives a path from `g 0` to `g 1` with image `g([0, 1])`. -/
theorem exists_path_of_continuousOn (g : ℝ → ℂ) (hg : ContinuousOn g (Icc 0 1)) :
    ∃ p : Path (g 0) (g 1), range p = g '' Icc 0 1 := by
  refine ⟨⟨⟨fun t => g t, hg.comp_continuous continuous_subtype_val fun t => t.2⟩, rfl, rfl⟩, ?_⟩
  ext z
  simp only [Path.coe_mk_mk, mem_range, mem_image]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.2, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

theorem PathAccessible.mem_closure {W : Set ℂ} {x : ℂ} (h : PathAccessible W x) :
    x ∈ closure W := by
  obtain ⟨g, hg, rfl, hgW⟩ := h
  have h0 : (0 : ℝ) ∈ closure (Ioc 0 1) := by
    rw [closure_Ioc zero_ne_one]; exact left_mem_Icc.2 zero_le_one
  have hc : ContinuousWithinAt g (Ioc 0 1) 0 :=
    (hg 0 ⟨le_rfl, zero_le_one⟩).mono Ioc_subset_Icc_self
  exact closure_mono hgW (hc.mem_closure_image h0)

theorem PathAccessible.mem_of_mem_image {W : Set ℂ} {g : ℝ → ℂ} (hgW : g '' Ioc 0 1 ⊆ W) {z : ℂ}
    (hz : z ∈ g '' Icc 0 1) (hz0 : z ≠ g 0) : z ∈ W := by
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : t ≠ 0 := fun h => hz0 (by rw [h])
  exact hgW ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩, rfl⟩

/-- Two points accessible from a path-connected set `W` are joined by an arc whose other points
lie in `W`. -/
theorem exists_arc_of_accessible {W : Set ℂ} (hc : IsPathConnected W) {a b : ℂ} (hab : a ≠ b)
    (ha : PathAccessible W a) (hb : PathAccessible W b) :
    ∃ σ : Set ℂ, IsArc σ a b ∧ σ \ {a, b} ⊆ W := by
  obtain ⟨ga, hga, rfl, hgaW⟩ := ha
  obtain ⟨gb, hgb, rfl, hgbW⟩ := hb
  obtain ⟨pa, hpa⟩ := exists_path_of_continuousOn ga hga
  obtain ⟨pb, hpb⟩ := exists_path_of_continuousOn gb hgb
  have h1 : ga 1 ∈ W := hgaW ⟨1, ⟨zero_lt_one, le_rfl⟩, rfl⟩
  have h2 : gb 1 ∈ W := hgbW ⟨1, ⟨zero_lt_one, le_rfl⟩, rfl⟩
  have hj := hc.joinedIn _ h1 _ h2
  obtain ⟨σ, hσq, hσ⟩ := exists_arc_in_path ((pa.trans hj.somePath).trans pb.symm) hab
  refine ⟨σ, hσ, ?_⟩
  rintro z ⟨hzσ, hz⟩
  have hz' := hσq hzσ
  simp only [Path.trans_range, Path.symm_range, mem_union] at hz'
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
  rcases hz' with (hz' | ⟨t, rfl⟩) | hz'
  · rw [hpa] at hz'
    exact PathAccessible.mem_of_mem_image hgaW hz' hz.1
  · exact hj.somePath_mem t
  · rw [hpb] at hz'
    exact PathAccessible.mem_of_mem_image hgbW hz' hz.2

/-- The separation step of `lem:two-domains`: a crosscut `σ` from `e^{iθ}` to `e^{ia₂}` through
`W₁` separates `e^{ia₁}` from `e^{ia₃}` (`θ < a₁ < a₂ < a₃ < θ + 2π`), so the connected set `W₂`
cannot have both in its closure. -/
theorem not_closure_both_sides {W₁ W₂ : Set ℂ} (hc₂ : IsPreconnected W₂) (hW₁ : W₁ ⊆ disc)
    (hW₂ : W₂ ⊆ disc) (hd : Disjoint W₁ W₂) {θ a₁ a₂ a₃ : ℝ} (h1 : θ < a₁) (h12 : a₁ < a₂)
    (h23 : a₂ < a₃) (h3 : a₃ < θ + 2 * π) {σ : Set ℂ} (hσ : IsArc σ (expI θ) (expI a₂))
    (hσW : σ \ {expI θ, expI a₂} ⊆ W₁) (hy : expI a₁ ∈ closure W₂)
    (hw : expI a₃ ∈ closure W₂) : False := by
  set ℓ := a₂ - θ with hℓ
  have ha₂ : a₂ = θ + ℓ := by rw [hℓ]; ring
  rw [ha₂] at hσ hσW
  have hσD : σ \ {expI θ, expI (θ + ℓ)} ⊆ disc := hσW.trans hW₁
  obtain ⟨z₁, -, z₂, -, -, hall, hfr₁, hfr₂⟩ :=
    crosscut_theorem (ℓ := ℓ) (by linarith) (by linarith) hσ hσD
  obtain ⟨k, hk⟩ : W₂.Nonempty := closure_nonempty_iff.1 ⟨_, hy⟩
  have hK : W₂ ⊆ disc \ σ := by
    intro z hz
    refine ⟨hW₂ hz, fun hzσ => ?_⟩
    by_cases hze : z = expI θ ∨ z = expI (θ + ℓ)
    · rcases hze with rfl | rfl
      · exact not_mem_disc_of_mem_circle (expI_mem_circle θ) (hW₂ hz)
      · exact not_mem_disc_of_mem_circle (expI_mem_circle _) (hW₂ hz)
    · push Not at hze
      exact disjoint_left.1 hd (hσW ⟨hzσ, by simp [hze.1, hze.2]⟩) hz
  have hsub := hc₂.subset_connectedComponentIn hk hK
  have hUD : ∀ z, connectedComponentIn (disc \ σ) z ⊆ disc := fun z =>
    (connectedComponentIn_subset _ _).trans sdiff_subset
  rcases hall k (hK hk) with he | he
  · rw [he] at hsub
    have hcl := (closure_inter_circle_of_frontier (by linarith) hσD (hUD z₁) hfr₁).1
    have hwA : expI a₃ ∈ closure (connectedComponentIn (disc \ σ) z₁) ∩ circle :=
      ⟨closure_mono hsub hw, expI_mem_circle _⟩
    rw [hcl] at hwA
    obtain ⟨t, ht, hte⟩ := hwA
    have := eq_of_expI_eq hte (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])
    linarith [ht.2]
  · rw [he] at hsub
    have he2 : expI (θ + ℓ + (2 * π - ℓ)) = expI θ := by
      rw [show θ + ℓ + (2 * π - ℓ) = θ + ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
        expI_add_int_mul]
    have hcl := (closure_inter_circle_of_frontier (θ := θ + ℓ) (ℓ := 2 * π - ℓ) (by linarith)
      (by rw [he2, pair_comm]; exact hσD) (hUD z₂) hfr₂).1
    have hyA : expI a₁ ∈ closure (connectedComponentIn (disc \ σ) z₂) ∩ circle :=
      ⟨closure_mono hsub hy, expI_mem_circle _⟩
    rw [hcl] at hyA
    obtain ⟨t, ht, hte⟩ := hyA
    have := eq_of_expI_eq hte (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])
    linarith [ht.1]

/-- `lem:two-domains`. -/
theorem accessible_two_domains {W₁ W₂ : Set ℂ} (ho₁ : IsOpen W₁) (ho₂ : IsOpen W₂)
    (hc₁ : IsConnected W₁) (hc₂ : IsConnected W₂) (hW₁ : W₁ ⊆ disc) (hW₂ : W₂ ⊆ disc)
    (hd : Disjoint W₁ W₂) :
    {x | x ∈ circle ∧ PathAccessible W₁ x ∧ PathAccessible W₂ x}.encard ≤ 3 := by
  have hpc₁ : IsPathConnected W₁ := ho₁.isConnected_iff_isPathConnected.1 hc₁
  set S := {x | x ∈ circle ∧ PathAccessible W₁ x ∧ PathAccessible W₂ x} with hS
  have hpair : ∀ x ∈ S, (S \ {x}).encard ≤ 2 := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have h3 : (3 : ℕ∞) ≤ (S \ {x}).encard := by
      have := Order.add_one_le_of_lt hlt
      norm_num at this
      exact this
    obtain ⟨T, hTS, hT⟩ := exists_subset_encard_eq h3
    obtain ⟨y, z, w, hyz, hyw, hzw, rfl⟩ := encard_eq_three.1 hT
    obtain ⟨⟨hyC, hy1, hy2⟩, hyx⟩ := hTS (show y ∈ ({y, z, w} : Set ℂ) by simp)
    obtain ⟨⟨hzC, hz1, hz2⟩, hzx⟩ := hTS (show z ∈ ({y, z, w} : Set ℂ) by simp)
    obtain ⟨⟨hwC, hw1, hw2⟩, hwx⟩ := hTS (show w ∈ ({y, z, w} : Set ℂ) by simp)
    set θ := Complex.arg x
    have hxθ : expI θ = x := expI_arg (mem_sphere_zero_iff_norm.1 hx.1)
    obtain ⟨ay, hay, rfl⟩ := exists_angle_Ioo θ hyC (by rw [hxθ]; exact hyx)
    obtain ⟨az, haz, rfl⟩ := exists_angle_Ioo θ hzC (by rw [hxθ]; exact hzx)
    obtain ⟨aw, haw, rfl⟩ := exists_angle_Ioo θ hwC (by rw [hxθ]; exact hwx)
    have hx1 : PathAccessible W₁ (expI θ) := hxθ ▸ hx.2.1
    have key : ∀ a b c : ℝ, θ < a → a < b → b < c → c < θ + 2 * π →
        expI a ∈ closure W₂ → PathAccessible W₁ (expI b) → expI c ∈ closure W₂ → False :=
      fun a b c h1 h12 h23 h3 ha hb hc => by
        have hne : expI θ ≠ expI b := fun h => by
          have := eq_of_expI_eq h (by rw [abs_lt]; constructor <;> linarith)
          linarith
        obtain ⟨σ, hσ, hσW⟩ := exists_arc_of_accessible hpc₁ hne hx1 hb
        exact not_closure_both_sides hc₂.isPreconnected hW₁ hW₂ hd h1 h12 h23 h3 hσ hσW ha hc
    have hy2' := hy2.mem_closure
    have hz2' := hz2.mem_closure
    have hw2' := hw2.mem_closure
    have hyz' : ay ≠ az := fun h => hyz (by rw [h])
    have hyw' : ay ≠ aw := fun h => hyw (by rw [h])
    have hzw' : az ≠ aw := fun h => hzw (by rw [h])
    obtain ⟨hay1, hay2⟩ := hay
    obtain ⟨haz1, haz2⟩ := haz
    obtain ⟨haw1, haw2⟩ := haw
    rcases lt_or_gt_of_ne hyz' with h₁ | h₁ <;> rcases lt_or_gt_of_ne hyw' with h₂ | h₂ <;>
      rcases lt_or_gt_of_ne hzw' with h₃ | h₃ <;>
      first
      | exact key ay az aw (by linarith) (by linarith) (by linarith) (by linarith) hy2' hz1 hw2'
      | exact key ay aw az (by linarith) (by linarith) (by linarith) (by linarith) hy2' hw1 hz2'
      | exact key az ay aw (by linarith) (by linarith) (by linarith) (by linarith) hz2' hy1 hw2'
      | exact key az aw ay (by linarith) (by linarith) (by linarith) (by linarith) hz2' hw1 hy2'
      | exact key aw ay az (by linarith) (by linarith) (by linarith) (by linarith) hw2' hy1 hz2'
      | exact key aw az ay (by linarith) (by linarith) (by linarith) (by linarith) hw2' hz1 hy2'
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h, encard_empty]; norm_num
  · rw [← encard_sdiff_singleton_add_one hx]
    have := hpair x hx
    calc (S \ {x}).encard + 1 ≤ 2 + 1 := by gcongr
      _ = 3 := by norm_num

/-- The accessibility step of `fact:bagemihl`: if `f → p ∈ B` (`B` open) along an arc at `x`,
then `x` is accessible from a component of `𝔻 ∩ f⁻¹(B)`. -/
theorem exists_accessible_component {f : ℂ → Sphere2} {x : ℂ}
    {γ : Set ℂ} (hγ : IsArcAt disc x γ) {p : Sphere2} {B : Set Sphere2} (hB : IsOpen B)
    (hpB : p ∈ B) (ht : Tendsto f (𝓝[γ \ {x}] x) (𝓝 p)) :
    ∃ z ∈ disc ∩ f ⁻¹' B, PathAccessible (connectedComponentIn (disc ∩ f ⁻¹' B) z) x := by
  obtain ⟨b, ⟨q, hq, rfl⟩, hγD⟩ := hγ
  rw [IsArc.nhdsWithin_eq hq] at ht
  have hev : q.extend ⁻¹' (f ⁻¹' B) ∈ 𝓝[>] (0 : ℝ) := ht (hB.mem_nhds hpB)
  obtain ⟨ε, hε, hεB⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hε0 : (0 : ℝ) < ε := hε
  set δ := min (ε / 2) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set g : ℝ → ℂ := fun s => q.extend (δ * s) with hg
  have hgc : ContinuousOn g (Icc 0 1) :=
    (q.continuous_extend.comp (continuous_const.mul continuous_id)).continuousOn
  have hg0 : g 0 = x := by simp [hg]
  have hgU : g '' Ioc 0 1 ⊆ disc ∩ f ⁻¹' B := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : 0 < δ * s := mul_pos hδ0 hs.1
    have h2 : δ * s ≤ δ := by nlinarith [hs.2]
    refine ⟨hγD ⟨?_, fun h => ?_⟩, hεB ⟨h1, by linarith⟩⟩
    · rw [Path.range_eq_image_extend]
      exact ⟨δ * s, ⟨h1.le, by linarith⟩, rfl⟩
    · have := Path.injOn_extend_of_injective hq (show δ * s ∈ Icc (0 : ℝ) 1 from
        ⟨h1.le, by linarith⟩) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
        (by rw [Path.extend_zero]; exact h)
      linarith
  have h1mem : g 1 ∈ g '' Ioc 0 1 := ⟨1, ⟨zero_lt_one, le_rfl⟩, rfl⟩
  refine ⟨g 1, hgU h1mem, g, hgc, hg0, ?_⟩
  exact (isPreconnected_Ioc.image g (hgc.mono Ioc_subset_Icc_self)).subset_connectedComponentIn
    h1mem hgU

/-- `fact:bagemihl` (Bagemihl's ambiguous point theorem, 1955, for `f` continuous in `𝔻`). -/
theorem ambiguous_countable (f : ℂ → Sphere2) (hf : ContinuousOn f disc) :
    {x | x ∈ circle ∧ ∃ γ₁ γ₂ : Set ℂ, ∃ p₁ p₂ : Sphere2, IsArcAt disc x γ₁ ∧
      IsArcAt disc x γ₂ ∧ Tendsto f (𝓝[γ₁ \ {x}] x) (𝓝 p₁) ∧
      Tendsto f (𝓝[γ₂ \ {x}] x) (𝓝 p₂) ∧ p₁ ≠ p₂}.Countable := by
  obtain ⟨𝓑, h𝓑c, -, h𝓑⟩ := TopologicalSpace.exists_countable_basis Sphere2
  set 𝒲 : Set (Set ℂ) := ⋃ B ∈ 𝓑, {W | ∃ z ∈ disc ∩ f ⁻¹' B, connectedComponentIn (disc ∩ f ⁻¹' B) z = W}
    with h𝒲def
  have hU : ∀ B ∈ 𝓑, IsOpen (disc ∩ f ⁻¹' B) := fun B hB =>
    hf.isOpen_inter_preimage Metric.isOpen_ball (h𝓑.isOpen hB)
  have h𝒲c : 𝒲.Countable :=
    h𝓑c.biUnion fun B hB => (countable_connectedComponents_of_isOpen (hU B hB)).1
  have h𝒲 : ∀ W ∈ 𝒲, IsOpen W ∧ IsConnected W ∧ W ⊆ disc := by
    intro W hW
    obtain ⟨B, hB, z, hz, rfl⟩ := mem_iUnion₂.1 hW
    exact ⟨(hU B hB).connectedComponentIn, isConnected_connectedComponentIn_iff.2 hz,
      (connectedComponentIn_subset _ _).trans inter_subset_left⟩
  -- each point of the set is accessible from a component for each of two disjoint basic sets
  have hacc : ∀ x : ℂ, ∀ γ : Set ℂ, IsArcAt disc x γ → ∀ p : Sphere2,
      Tendsto f (𝓝[γ \ {x}] x) (𝓝 p) → ∀ B ∈ 𝓑, p ∈ B →
      ∃ W ∈ 𝒲, W ⊆ f ⁻¹' B ∧ PathAccessible W x := by
    intro x γ hγ p ht B hB hpB
    obtain ⟨z, hz, hW⟩ := exists_accessible_component hγ (h𝓑.isOpen hB) hpB ht
    exact ⟨_, mem_iUnion₂.2 ⟨B, hB, z, hz, rfl⟩,
      (connectedComponentIn_subset _ _).trans inter_subset_right, hW⟩
  set T : Set ℂ → Set ℂ → Set ℂ := fun W₁ W₂ =>
    {x | x ∈ circle ∧ PathAccessible W₁ x ∧ PathAccessible W₂ x ∧ Disjoint W₁ W₂} with hTdef
  have hT : ∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, (T W₁ W₂).Countable := by
    intro W₁ hW₁ W₂ hW₂
    by_cases hd : Disjoint W₁ W₂
    · obtain ⟨ho₁, hc₁, hD₁⟩ := h𝒲 W₁ hW₁
      obtain ⟨ho₂, hc₂, hD₂⟩ := h𝒲 W₂ hW₂
      refine (Set.finite_of_encard_le_coe (k := 3) ?_).countable
      refine le_trans (encard_le_encard ?_) (accessible_two_domains ho₁ ho₂ hc₁ hc₂ hD₁ hD₂ hd)
      exact fun x hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩
    · refine (countable_empty (α := ℂ)).mono fun x hx => absurd hx.2.2.2 hd
  refine (h𝒲c.biUnion fun W₁ hW₁ => h𝒲c.biUnion fun W₂ hW₂ => hT W₁ hW₁ W₂ hW₂).mono ?_
  rintro x ⟨hxC, γ₁, γ₂, p₁, p₂, ha₁, ha₂, ht₁, ht₂, hne⟩
  obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ := t2_separation hne
  obtain ⟨B₁, hB₁, hpB₁, hB₁u⟩ := h𝓑.exists_subset_of_mem_open hpu hu
  obtain ⟨B₂, hB₂, hpB₂, hB₂v⟩ := h𝓑.exists_subset_of_mem_open hpv hv
  obtain ⟨W₁, hW₁, hW₁B, hx₁⟩ := hacc x γ₁ ha₁ p₁ ht₁ B₁ hB₁ hpB₁
  obtain ⟨W₂, hW₂, hW₂B, hx₂⟩ := hacc x γ₂ ha₂ p₂ ht₂ B₂ hB₂ hpB₂
  have hd : Disjoint W₁ W₂ := by
    refine disjoint_left.2 fun z hz1 hz2 => disjoint_left.1 huv (hB₁u (hW₁B hz1)) (hB₂v (hW₂B hz2))
  exact mem_iUnion₂.2 ⟨W₁, hW₁, mem_iUnion₂.2 ⟨W₂, hW₂, hxC, hx₁, hx₂, hd⟩⟩

end TJK
