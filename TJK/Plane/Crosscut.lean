import Mathlib
import TJK.Defs
import TJK.Plane.Basic

/-!
# Crosscuts of the disk and of the half-plane, and arcs in a strip (blueprint §C)

* `crosscut_components`: `fact:crosscut` (imported as `crosscut_theorem`) restated with the two
  components as open connected sets;
* `lem:crosscut-H` (`crosscutH_theorem`), transferred by the Cayley map `κ`;
* `lem:strip` (`strip_order`), transferred by the strip map `𝓔_h`.

Auxiliary facts: the interior `γ \ {a, b}` of an arc is preconnected, nonempty and dense in `γ`;
`κ(x) = e^{i(π + 2 arctan x)}` on `ℝ`; `e^{is} = e^{it}` iff `s - t ∈ 2πℤ`.
-/

namespace TJK

open _root_.Set Filter Topology Metric Function Complex

open scoped Real

/-! ### The interior of an arc -/

section ArcInterior

variable {E : Type*} [TopologicalSpace E]

theorem Path.range_diff_pair_eq {a b : E} {q : Path a b} (hq : Injective q) :
    range q \ {a, b} = q.extend '' Ioo 0 1 := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, hz⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    refine ⟨t, ⟨lt_of_le_of_ne t.2.1 fun h => hz.1 ?_, lt_of_le_of_ne t.2.2 fun h => hz.2 ?_⟩,
      q.extend_extends' t⟩
    · have : t = 0 := Subtype.ext h.symm
      rw [this, q.source]
    · have : t = 1 := Subtype.ext h
      rw [this, q.target]
  · rintro ⟨t, ht, rfl⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    rw [q.extend_apply htI]
    refine ⟨mem_range_self _, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h
      have h' : q ⟨t, htI⟩ = q 0 := h.trans q.source.symm
      exact ht.1.ne' (congrArg Subtype.val (hq h'))
    · intro h
      have h' : q ⟨t, htI⟩ = q 1 := h.trans q.target.symm
      exact ht.2.ne (congrArg Subtype.val (hq h'))

theorem Path.range_diff_left_eq {a b : E} {q : Path a b} (hq : Injective q) :
    range q \ {a} = q.extend '' Ioc 0 1 := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, hz⟩
    refine ⟨t, ⟨lt_of_le_of_ne t.2.1 fun h => hz ?_, t.2.2⟩, q.extend_extends' t⟩
    have : t = 0 := Subtype.ext h.symm
    rw [this, q.source]; rfl
  · rintro ⟨t, ht, rfl⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    rw [q.extend_apply htI]
    refine ⟨mem_range_self _, fun h => ?_⟩
    have h' : q ⟨t, htI⟩ = q 0 := (mem_singleton_iff.1 h).trans q.source.symm
    exact ht.1.ne' (congrArg Subtype.val (hq h'))

/-- The interior `γ \ {a, b}` of an arc is preconnected. -/
theorem IsArc.isPreconnected_diff_pair {γ : Set E} {a b : E} (h : IsArc γ a b) :
    IsPreconnected (γ \ {a, b}) := by
  obtain ⟨q, hq, rfl⟩ := h
  rw [Path.range_diff_pair_eq hq]
  exact isPreconnected_Ioo.image _ q.continuous_extend.continuousOn

/-- An arc minus one endpoint is preconnected. -/
theorem IsArc.isPreconnected_diff_left {γ : Set E} {a b : E} (h : IsArc γ a b) :
    IsPreconnected (γ \ {a}) := by
  obtain ⟨q, hq, rfl⟩ := h
  rw [Path.range_diff_left_eq hq]
  exact isPreconnected_Ioc.image _ q.continuous_extend.continuousOn

/-- The interior of an arc is nonempty. -/
theorem IsArc.nonempty_diff_pair {γ : Set E} {a b : E} (h : IsArc γ a b) :
    (γ \ {a, b}).Nonempty := by
  obtain ⟨q, hq, rfl⟩ := h
  rw [Path.range_diff_pair_eq hq]
  exact ⟨_, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩

/-- An arc lies in the closure of its interior. -/
theorem IsArc.subset_closure_diff_pair {γ : Set E} {a b : E} (h : IsArc γ a b) :
    γ ⊆ closure (γ \ {a, b}) := by
  obtain ⟨q, hq, rfl⟩ := h
  rw [Path.range_diff_pair_eq hq, Path.range_eq_image_extend, ← closure_Ioo zero_ne_one]
  exact image_closure_subset_closure_image q.continuous_extend

end ArcInterior

/-! ### Angles -/

theorem expI_eq_expI_iff {s t : ℝ} : expI s = expI t ↔ ∃ k : ℤ, s = t + k * (2 * π) := by
  rw [expI, expI, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := congrArg Complex.im hk
    simp at this
    linarith
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

theorem int_eq_zero_of_mul_two_pi_mem {k : ℤ} (h1 : -(2 * π) < k * (2 * π))
    (h2 : k * (2 * π) < 2 * π) : k = 0 := by
  have hp := Real.two_pi_pos
  have a1 : (k : ℝ) < 1 := by nlinarith
  have a2 : (-1 : ℝ) < k := by nlinarith
  have b1 : k < 1 := by exact_mod_cast a1
  have b2 : -1 < k := by exact_mod_cast a2
  omega

/-- `t ↦ e^{it}` is injective on any half-open interval of length `2π`. -/
theorem expI_injOn_Ico (c : ℝ) : InjOn expI (Ico c (c + 2 * π)) := by
  intro s hs t ht hst
  obtain ⟨k, hk⟩ := expI_eq_expI_iff.1 hst
  have : k = 0 := int_eq_zero_of_mul_two_pi_mem (by linarith [hs.1, ht.2]) (by linarith [hs.2, ht.1])
  rw [hk, this]; simp

/-! ### The crosscut theorem with open components -/

/-- `fact:crosscut`, in the form used below: for a crosscut `σ` of `𝔻` from `e^{iθ}` to
`e^{i(θ+ℓ)}`, `𝔻 \ σ` is the union of two disjoint connected open sets `U, V` with
`closure U ∩ C = circleArc θ ℓ`, `closure V ∩ C = circleArc (θ + ℓ) (2π - ℓ)`, and
`σ ⊆ closure U ∩ closure V`. -/
theorem crosscut_components {σ : Set ℂ} {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ < 2 * π)
    (hσ : IsArc σ (expI θ) (expI (θ + ℓ))) (hσD : σ \ {expI θ, expI (θ + ℓ)} ⊆ disc) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      disc \ σ = U ∪ V ∧ closure U ∩ circle = circleArc θ ℓ ∧
      closure V ∩ circle = circleArc (θ + ℓ) (2 * π - ℓ) ∧ σ ⊆ closure U ∧ σ ⊆ closure V := by
  obtain ⟨z₁, hz₁, z₂, hz₂, hdisj, hcov, hfr₁, hfr₂⟩ := crosscut_theorem hℓ hℓ' hσ hσD
  have ho : IsOpen (disc \ σ) := isOpen_ball.sdiff hσ.isCompact.isClosed
  have hsub : ∀ z, connectedComponentIn (disc \ σ) z ⊆ disc := fun z =>
    (connectedComponentIn_subset _ _).trans sdiff_subset
  obtain ⟨h1, h1'⟩ := closure_inter_circle_of_frontier hℓ.le hσD (hsub z₁) hfr₁
  have hσD' : σ \ {expI (θ + ℓ), expI (θ + ℓ + (2 * π - ℓ))} ⊆ disc := by
    have : expI (θ + ℓ + (2 * π - ℓ)) = expI θ := by
      rw [show θ + ℓ + (2 * π - ℓ) = θ + ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
        expI_add_int_mul]
    rw [this, pair_comm]; exact hσD
  obtain ⟨h2, h2'⟩ := closure_inter_circle_of_frontier (by linarith) hσD' (hsub z₂) hfr₂
  refine ⟨_, _, ho.connectedComponentIn, ho.connectedComponentIn,
    isConnected_connectedComponentIn_iff.2 hz₁, isConnected_connectedComponentIn_iff.2 hz₂, hdisj,
    ?_, h1, h2, h1', h2'⟩
  ext z
  constructor
  · intro hz
    rcases hcov z hz with h | h
    · exact Or.inl (h ▸ mem_connectedComponentIn hz)
    · exact Or.inr (h ▸ mem_connectedComponentIn hz)
  · rintro (h | h) <;> exact connectedComponentIn_subset _ _ h

/-! ### The Cayley map on the real line -/

/-- The angle of `κ(x)`: `κ(x) = e^{i(π + 2 arctan x)}`. -/
noncomputable def cayleyAngle (x : ℝ) : ℝ := π + 2 * Real.arctan x

theorem cayley_ofReal (x : ℝ) : cayley x = expI (cayleyAngle x) := by
  rw [cayleyAngle]
  set t := Real.arctan x with ht
  have hc : 0 < Real.cos t := Real.cos_arctan_pos x
  have hx : x = Real.sin t / Real.cos t := by rw [← Real.tan_eq_sin_div_cos, ht, Real.tan_arctan]
  have hsc : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  have hne : (x : ℂ) + I ≠ 0 := add_I_ne_zero (by simp)
  rw [cayley, div_eq_iff hne, expI, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h1 : Real.cos (π + 2 * t) = -(Real.cos t ^ 2 - Real.sin t ^ 2) := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_two_mul, Real.sin_two_mul]; nlinarith
  have h2 : Real.sin (π + 2 * t) = -(2 * Real.sin t * Real.cos t) := by
    rw [Real.sin_add, Real.cos_pi, Real.sin_pi, Real.sin_two_mul]; ring
  rw [h1, h2]
  generalize Real.sin t = s at *
  generalize Real.cos t = c at *
  subst hx
  have hc0 : c ≠ 0 := hc.ne'
  apply Complex.ext <;>
    simp only [ofReal_re, ofReal_im, mul_re, mul_im, add_re, add_im, sub_re, sub_im, I_re, I_im]
  · field_simp; linear_combination (-s) * hsc
  · field_simp; linear_combination c * hsc

theorem cayleyAngle_mem (x : ℝ) : cayleyAngle x ∈ Ioo 0 (2 * π) := by
  have h1 := Real.neg_pi_div_two_lt_arctan x
  have h2 := Real.arctan_lt_pi_div_two x
  rw [cayleyAngle]
  constructor <;> linarith

theorem strictMono_cayleyAngle : StrictMono cayleyAngle := fun x y hxy => by
  have := Real.arctan_strictMono hxy
  rw [cayleyAngle, cayleyAngle]; linarith

/-- `κ` maps `[a, b]` onto the arc `circleArc (θ a) (θ b - θ a)`. -/
theorem cayley_mem_circleArc_iff {a b : ℝ} (x : ℝ) :
    cayley x ∈ circleArc (cayleyAngle a) (cayleyAngle b - cayleyAngle a) ↔ x ∈ Icc a b := by
  rw [cayley_ofReal, circleArc, add_sub_cancel]
  constructor
  · rintro ⟨t, ht, he⟩
    have hx := cayleyAngle_mem x
    have hta := cayleyAngle_mem a
    have htb := cayleyAngle_mem b
    have : t = cayleyAngle x := expI_injOn_Ico 0 ⟨by linarith [ht.1, hta.1], by linarith [ht.2, htb.2]⟩
      ⟨hx.1.le, by linarith [hx.2]⟩ he
    rw [this] at ht
    exact ⟨strictMono_cayleyAngle.le_iff_le.1 ht.1, strictMono_cayleyAngle.le_iff_le.1 ht.2⟩
  · intro hx
    exact ⟨cayleyAngle x, ⟨strictMono_cayleyAngle.monotone hx.1,
      strictMono_cayleyAngle.monotone hx.2⟩, rfl⟩

/-- `κ` maps `(-∞, a] ∪ [b, ∞)` onto the complementary arc. -/
theorem cayley_mem_circleArc_compl_iff {a b : ℝ} (x : ℝ) :
    cayley x ∈ circleArc (cayleyAngle a + (cayleyAngle b - cayleyAngle a))
      (2 * π - (cayleyAngle b - cayleyAngle a)) ↔ x ∈ Iic a ∪ Ici b := by
  have hx := cayleyAngle_mem x
  have hta := cayleyAngle_mem a
  have htb := cayleyAngle_mem b
  rw [cayley_ofReal, circleArc]
  constructor
  · rintro ⟨t, ht, he⟩
    obtain ⟨k, hk⟩ := expI_eq_expI_iff.1 he
    have hk1 : -(2 * π) < k * (2 * π) := by linarith [ht.1, hx.2.le, htb.1]
    have hk2 : k * (2 * π) < 4 * π := by linarith [ht.2, hx.1, hta.2]
    have hp := Real.two_pi_pos
    have a1 : (k : ℝ) < 2 := by nlinarith
    have a2 : (-1 : ℝ) < k := by nlinarith
    have b1 : k < 2 := by exact_mod_cast a1
    have b2 : -1 < k := by exact_mod_cast a2
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · right
      have : cayleyAngle b ≤ cayleyAngle x := by push_cast at hk; linarith [ht.1]
      exact strictMono_cayleyAngle.le_iff_le.1 this
    · left
      have : cayleyAngle x ≤ cayleyAngle a := by push_cast at hk; linarith [ht.2]
      exact strictMono_cayleyAngle.le_iff_le.1 this
  · rintro (h | h)
    · have h' : cayleyAngle x ≤ cayleyAngle a := strictMono_cayleyAngle.monotone h
      refine ⟨cayleyAngle x + ((1 : ℤ) : ℝ) * (2 * π), ⟨?_, ?_⟩, expI_add_int_mul _ _⟩ <;>
        push_cast <;> linarith [hx.1, hx.2, hta.1, hta.2, htb.1, htb.2]
    · have h' : cayleyAngle b ≤ cayleyAngle x := strictMono_cayleyAngle.monotone h
      exact ⟨cayleyAngle x, ⟨by linarith, by linarith [hx.2, hta.1]⟩, rfl⟩

/-- Closures correspond under a partial homeomorphism, at points of its source. -/
theorem PartialHomeomorph.mem_closure_symm_image_iff {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : PartialHomeomorph X Y) {s : Set Y} (hs : s ⊆ e.target) {x : X}
    (hx : x ∈ e.source) : x ∈ closure (e.symm '' s) ↔ e x ∈ closure s := by
  have hsrc : e.symm '' s ⊆ e.source := fun _ ⟨w, hw, hwz⟩ => hwz ▸ e.map_target (hs hw)
  constructor
  · intro h
    have := ((e.continuousOn x hx).mono hsrc).mem_closure_image h
    have h2 : e '' (e.symm '' s) = s := e.toPartialEquiv.image_symm_image_of_subset_target hs
    rwa [h2] at this
  · intro h
    have := ((e.continuousOn_symm (e x) (e.map_source hx)).mono hs).mem_closure_image h
    rwa [e.left_inv hx] at this

/-! ### `lem:crosscut-H` -/

/-- `lem:crosscut-H`: a crosscut `σ` of `ℍ` from `a` to `b`, `a < b`, splits `ℍ` into two disjoint
connected open sets: a bounded one `V` with `closure V ∩ ℝ = [a, b]` and an unbounded one `U` with
`closure U ∩ ℝ = ℝ \ (a, b)`; `σ ⊆ closure U ∩ closure V`, and `U` contains every point above
`σ`. -/
theorem crosscutH_theorem {σ : Set ℂ} {a b : ℝ} (hab : a < b) (hσ : IsArc σ a b)
    (hσH : σ \ {(a : ℂ), (b : ℂ)} ⊆ upper) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      upper \ σ = U ∪ V ∧ Bornology.IsBounded V ∧
      closure V ∩ realAxis = ((↑) : ℝ → ℂ) '' Icc a b ∧
      closure U ∩ realAxis = ((↑) : ℝ → ℂ) '' (Iic a ∪ Ici b) ∧
      σ ⊆ closure U ∧ σ ⊆ closure V ∧ ∀ z : ℂ, (∀ w ∈ σ, w.im < z.im) → z ∈ U := by
  set e := cayleyPH
  have hsrc : σ ⊆ e.source := by
    intro z hz
    show 0 ≤ z.im
    by_cases h : z = a ∨ z = b
    · rcases h with rfl | rfl <;> simp
    · push Not at h
      exact (hσH ⟨hz, by simp [h.1, h.2]⟩).le
  set θ := cayleyAngle a
  set ℓ := cayleyAngle b - cayleyAngle a
  have hℓ : 0 < ℓ := sub_pos.2 (strictMono_cayleyAngle hab)
  have hℓ' : ℓ < 2 * π := by linarith [(cayleyAngle_mem a).1, (cayleyAngle_mem b).2]
  have hθb : expI (θ + ℓ) = cayley b := by rw [add_sub_cancel, cayley_ofReal]
  have hθa : expI θ = cayley a := (cayley_ofReal a).symm
  have harc : IsArc (cayley '' σ) (expI θ) (expI (θ + ℓ)) := by
    rw [hθa, hθb]
    exact hσ.image (e.continuousOn.mono hsrc) (e.injOn.mono hsrc)
  have hD : cayley '' σ \ {expI θ, expI (θ + ℓ)} ⊆ disc := by
    rintro _ ⟨⟨z, hz, rfl⟩, hne⟩
    rw [hθa, hθb] at hne
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
    have hza : z ≠ a := fun h => hne.1 (by rw [h])
    have hzb : z ≠ b := fun h => hne.2 (by rw [h])
    exact cayley_isChart.mapsTo (hσH ⟨hz, by simp [hza, hzb]⟩)
  obtain ⟨U₀, V₀, hU₀, hV₀, hcU₀, hcV₀, hd, heq, hclU, hclV, hσU, hσV⟩ :=
    crosscut_components hℓ hℓ' harc hD
  have hU₀D : U₀ ⊆ disc := fun z hz => ((heq.symm ▸ Or.inl hz : z ∈ disc \ cayley '' σ)).1
  have hV₀D : V₀ ⊆ disc := fun z hz => ((heq.symm ▸ Or.inr hz : z ∈ disc \ cayley '' σ)).1
  have hDt : disc ⊆ e.target := cayley_isChart.subset_target
  have hupS : upper ⊆ e.source := cayley_isChart.subset_source
  -- the sets `upper ∩ κ⁻¹ W` for `W ⊆ 𝔻`
  have himg : ∀ W ⊆ disc, upper ∩ cayley ⁻¹' W = cayleyInv '' W := by
    intro W hW
    ext z
    constructor
    · rintro ⟨hz, hzW⟩
      exact ⟨cayley z, hzW, cayleyInv_cayley (le_of_lt hz)⟩
    · rintro ⟨w, hw, rfl⟩
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (hW hw)
      refine ⟨cayleyInv_im_pos hw1, ?_⟩
      rw [mem_preimage, cayley_cayleyInv (ne_one_of_mem_disc (hW hw))]
      exact hw
  have hopen : ∀ W, IsOpen W → IsOpen (upper ∩ cayley ⁻¹' W) := fun W hW =>
    (e.continuousOn.mono hupS).isOpen_inter_preimage (isOpen_lt continuous_const continuous_im) hW
  have hconn : ∀ W ⊆ disc, IsConnected W → IsConnected (upper ∩ cayley ⁻¹' W) := by
    intro W hW hc
    rw [himg W hW]
    exact hc.image _ (e.continuousOn_symm.mono (hW.trans hDt))
  have hclos : ∀ W ⊆ disc, ∀ z ∈ e.source, z ∈ closure (upper ∩ cayley ⁻¹' W) ↔
      cayley z ∈ closure W := by
    intro W hW z hz
    rw [himg W hW]
    exact PartialHomeomorph.mem_closure_symm_image_iff e (hW.trans hDt) hz
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ e.source := fun x => by show (0 : ℝ) ≤ (x : ℂ).im; simp
  have hcirc : ∀ x : ℝ, cayley x ∈ circle := fun x =>
    mem_sphere_zero_iff_norm.2 ((norm_cayley_eq_one_iff (hreal x)).2 (by simp))
  have hrealAxis : ∀ z ∈ realAxis, z = ((z.re : ℝ) : ℂ) := fun z hz => Complex.ext (by simp)
    (by simpa using hz)
  set V := upper ∩ cayley ⁻¹' U₀ with hVdef
  set U := upper ∩ cayley ⁻¹' V₀ with hUdef
  have hVU : Disjoint U V := disjoint_left.2 fun z hzU hzV =>
    disjoint_left.1 hd hzV.2 hzU.2
  have hcover : upper \ σ = U ∪ V := by
    ext z
    constructor
    · rintro ⟨hz, hzσ⟩
      have hz' : cayley z ∈ disc \ cayley '' σ := by
        refine ⟨cayley_isChart.mapsTo hz, ?_⟩
        rintro ⟨w, hw, hwz⟩
        exact hzσ (e.injOn (hsrc hw) (hupS hz) hwz ▸ hw)
      rw [heq] at hz'
      rcases hz' with h | h
      · exact Or.inr ⟨hz, h⟩
      · exact Or.inl ⟨hz, h⟩
    · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
      · have : cayley z ∈ disc \ cayley '' σ := heq.symm ▸ Or.inr h
        exact ⟨hz, fun hzσ => this.2 ⟨z, hzσ, rfl⟩⟩
      · have : cayley z ∈ disc \ cayley '' σ := heq.symm ▸ Or.inl h
        exact ⟨hz, fun hzσ => this.2 ⟨z, hzσ, rfl⟩⟩
  -- `V` is bounded: its closure avoids `1`
  have h1 : (1 : ℂ) ∉ closure U₀ := by
    intro h
    have : (1 : ℂ) ∈ closure U₀ ∩ circle := ⟨h, by simp⟩
    rw [hclU] at this
    obtain ⟨t, ht, he⟩ := this
    have h0 : expI 0 = 1 := by simp [expI]
    have := expI_injOn_Ico 0 ⟨by linarith [ht.1, (cayleyAngle_mem a).1],
      by linarith [ht.2, (cayleyAngle_mem b).2]⟩ ⟨le_rfl, by linarith [Real.pi_pos]⟩
      (he.trans h0.symm)
    linarith [ht.1, (cayleyAngle_mem a).1]
  have hVb : Bornology.IsBounded V := by
    obtain ⟨r, hr, hrU⟩ : ∃ r > 0, ∀ w ∈ U₀, r ≤ dist 1 w := by
      by_contra hcon
      push Not at hcon
      exact h1 (Metric.mem_closure_iff.2 fun ε hε => by
        obtain ⟨w, hw, hwε⟩ := hcon ε hε
        exact ⟨w, hw, hwε⟩)
    rw [hVdef, himg U₀ hU₀D, isBounded_iff_forall_norm_le]
    refine ⟨2 / r, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (hU₀D hw)
    have hd1 : r ≤ ‖1 - w‖ := by rw [← dist_eq_norm]; exact hrU w hw
    rw [cayleyInv, norm_div, norm_mul, norm_I, one_mul]
    rw [div_le_div_iff₀ (by linarith) hr]
    have : ‖1 + w‖ ≤ 2 := by
      calc ‖1 + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    nlinarith [norm_nonneg (1 + w)]
  refine ⟨U, V, hopen V₀ hV₀, hopen U₀ hU₀, hconn V₀ hV₀D hcV₀, hconn U₀ hU₀D hcU₀, hVU, hcover,
    hVb, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨hz, hzR⟩
      rw [hrealAxis z hzR] at hz ⊢
      rw [hclos U₀ hU₀D _ (hreal _)] at hz
      have : cayley (z.re : ℂ) ∈ closure U₀ ∩ circle := ⟨hz, hcirc _⟩
      rw [hclU, cayley_mem_circleArc_iff] at this
      exact mem_image_of_mem _ this
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, by simp⟩
      rw [hclos U₀ hU₀D _ (hreal _)]
      have : cayley x ∈ circleArc θ ℓ := (cayley_mem_circleArc_iff x).2 hx
      rw [← hclU] at this
      exact this.1
  · ext z
    constructor
    · rintro ⟨hz, hzR⟩
      rw [hrealAxis z hzR] at hz ⊢
      rw [hclos V₀ hV₀D _ (hreal _)] at hz
      have : cayley (z.re : ℂ) ∈ closure V₀ ∩ circle := ⟨hz, hcirc _⟩
      rw [hclV, cayley_mem_circleArc_compl_iff] at this
      exact mem_image_of_mem _ this
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, by simp⟩
      rw [hclos V₀ hV₀D _ (hreal _)]
      have : cayley x ∈ circleArc (θ + ℓ) (2 * π - ℓ) :=
        (cayley_mem_circleArc_compl_iff x).2 hx
      rw [← hclV] at this
      exact this.1
  · intro z hz
    rw [hclos V₀ hV₀D _ (hsrc hz)]
    exact hσV ⟨z, hz, rfl⟩
  · intro z hz
    rw [hclos U₀ hU₀D _ (hsrc hz)]
    exact hσU ⟨z, hz, rfl⟩
  · -- the half-plane above `σ` lies in `U`
    intro z hz
    set H := {w : ℂ | ∀ v ∈ σ, v.im < w.im} with hH
    have hHc : Convex ℝ H := by
      intro w₁ hw₁ w₂ hw₂ s t hs ht hst v hv
      have e1 := hw₁ v hv
      have e2 := hw₂ v hv
      show v.im < (s • w₁ + t • w₂).im
      rw [add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      have hv' : v.im = s * v.im + t * v.im := by rw [← add_mul, hst, one_mul]
      rcases hs.lt_or_eq with hs' | hs'
      · nlinarith [mul_pos hs' (sub_pos.2 e1), mul_nonneg ht (sub_nonneg.2 e2.le)]
      · subst hs'
        have : t = 1 := by linarith
        subst this; linarith
    have hHsub : H ⊆ U ∪ V := by
      rw [← hcover]
      intro w hw
      refine ⟨?_, fun hwσ => lt_irrefl _ (hw w hwσ)⟩
      have := hw a hσ.left_mem
      simpa using this
    rcases hHc.isPreconnected.subset_or_subset (hopen V₀ hV₀) (hopen U₀ hU₀) hVU hHsub with h | h
    · exact h hz
    · exfalso
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hVb
      set w := z + ((C + 1 + ‖z‖ : ℝ) : ℂ) * I
      have hwH : w ∈ H := by
        intro v hv
        have := hz v hv
        have h0 : 0 ≤ C + 1 + ‖z‖ := by
          have := hC _ (h (show z ∈ H from hz)); linarith [norm_nonneg z]
        simp only [w, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
          add_zero]
        linarith
      have h1 := hC w (h hwH)
      have h2 : w.im ≤ ‖w‖ := (le_abs_self _).trans (Complex.abs_im_le_norm w)
      have h3 : -‖z‖ ≤ z.im := (neg_abs_le _).trans' (neg_le_neg (Complex.abs_im_le_norm z))
      simp only [w, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
        add_zero] at h2
      linarith

/-! ### `lem:strip` -/

/-- `lem:strip`: in the strip `0 < Im z < h`, disjoint arcs from `x < x'` on the lower line to
`p`, `p'` on the upper line end in the same order: `Re p < Re p'`. -/
theorem strip_order {h : ℝ} (hh : 0 < h) {α α' : Set ℂ} {x x' : ℝ} {p p' : ℂ}
    (hp : p.im = h) (hp' : p'.im = h) (hα : IsArc α x p) (hα' : IsArc α' x' p')
    (hαS : α \ {(x : ℂ), p} ⊆ openStrip h) (hα'S : α' \ {(x' : ℂ), p'} ⊆ openStrip h)
    (hd : Disjoint α α') (hxx' : x < x') : p.re < p'.re := by
  set e := stripExpPH h hh
  have hch := stripExp_isChart hh
  have hEc : Continuous (stripExp h) := by unfold stripExp; fun_prop
  have hsrc : ∀ {β : Set ℂ} {y : ℝ} {q : ℂ}, q.im = h → β \ {(y : ℂ), q} ⊆ openStrip h →
      β ⊆ e.source := by
    intro β y q hq hβ z hz
    show 0 ≤ z.im ∧ z.im ≤ h
    by_cases hzy : z = y
    · subst hzy; simp [hh.le]
    by_cases hzq : z = q
    · subst hzq; rw [hq]; exact ⟨hh.le, le_rfl⟩
    have := hβ ⟨hz, by simp [hzy, hzq]⟩
    exact ⟨this.1.le, this.2.le⟩
  have hαs := hsrc hp hαS
  have hα's := hsrc hp' hα'S
  have hpe : ∀ q : ℂ, q.im = h → stripExp h q = ((-Real.exp (π / h * q.re) : ℝ) : ℂ) := by
    intro q hq
    have : q = (q.re : ℂ) + h * I := Complex.ext (by simp) (by simp [hq])
    rw [this, stripExp_add_I hh.ne']
    simp
  set u := Real.exp (π / h * x)
  set v := -Real.exp (π / h * p.re)
  have hvu : v < u := by
    have := Real.exp_pos (π / h * p.re); have := Real.exp_pos (π / h * x); linarith
  have harc : IsArc (stripExp h '' α) v u := by
    have := hα.image (e.continuousOn.mono hαs) (e.injOn.mono hαs)
    have h1 : e x = (u : ℂ) := stripExp_ofReal h x
    have h2 : e p = (v : ℂ) := hpe p hp
    rw [h1, h2] at this
    exact this.symm
  have hH : stripExp h '' α \ {(v : ℂ), (u : ℂ)} ⊆ upper := by
    rintro _ ⟨⟨z, hz, rfl⟩, hne⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
    have hzx : z ≠ x := fun h' => hne.2 (by rw [h']; exact stripExp_ofReal h x)
    have hzp : z ≠ p := fun h' => hne.1 (by rw [h']; exact hpe p hp)
    exact hch.mapsTo (hαS ⟨hz, by simp [hzx, hzp]⟩)
  obtain ⟨U, V, hUo, hVo, -, -, hUV, hcov, -, hclV, hclU, -, -, -⟩ := crosscutH_theorem hvu harc hH
  set T := stripExp h '' (α' \ {(x' : ℂ), p'})
  have hT : T ⊆ U ∪ V := by
    rw [← hcov]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hch.mapsTo (hα'S hz), ?_⟩
    rintro ⟨w, hw, hwz⟩
    have := e.injOn (hαs hw) (hα's hz.1) hwz
    exact disjoint_left.1 hd hw (this ▸ hz.1)
  have hTc : IsPreconnected T := hα'.isPreconnected_diff_pair.image _ hEc.continuousOn
  have hcl : stripExp h '' α' ⊆ closure T :=
    (image_mono hα'.subset_closure_diff_pair).trans (image_closure_subset_closure_image hEc)
  have hx'T : ((Real.exp (π / h * x') : ℝ) : ℂ) ∈ closure T := by
    rw [← stripExp_ofReal]; exact hcl ⟨_, hα'.left_mem, rfl⟩
  have hp'T : ((-Real.exp (π / h * p'.re) : ℝ) : ℂ) ∈ closure T := by
    rw [← hpe p' hp']; exact hcl ⟨_, hα'.right_mem, rfl⟩
  have hπh : 0 < π / h := div_pos Real.pi_pos hh
  rcases hTc.subset_or_subset hUo hVo hUV hT with hTU | hTV
  · have : ((-Real.exp (π / h * p'.re) : ℝ) : ℂ) ∈ closure U ∩ realAxis :=
      ⟨closure_mono hTU hp'T, ofReal_im _⟩
    rw [hclU] at this
    obtain ⟨s, hs, hse⟩ := this
    have hse' : s = -Real.exp (π / h * p'.re) := ofReal_injective hse
    subst hse'
    rcases hs with hs | hs
    · have hle : π / h * p.re ≤ π / h * p'.re := by
        have : Real.exp (π / h * p.re) ≤ Real.exp (π / h * p'.re) := by
          simp only [mem_Iic] at hs; linarith
        exact Real.exp_le_exp.1 this
      have hle' : p.re ≤ p'.re := le_of_mul_le_mul_left hle hπh
      refine lt_of_le_of_ne hle' fun heq => ?_
      have : p = p' := Complex.ext heq (by rw [hp, hp'])
      exact disjoint_left.1 hd hα.right_mem (this ▸ hα'.right_mem)
    · simp only [mem_Ici] at hs
      have := Real.exp_pos (π / h * p'.re)
      have := Real.exp_pos (π / h * x)
      linarith
  · have : ((Real.exp (π / h * x') : ℝ) : ℂ) ∈ closure V ∩ realAxis :=
      ⟨closure_mono hTV hx'T, ofReal_im _⟩
    rw [hclV] at this
    obtain ⟨s, hs, hse⟩ := this
    have hse' : s = Real.exp (π / h * x') := ofReal_injective hse
    subst hse'
    have : π / h * x' ≤ π / h * x := Real.exp_le_exp.1 hs.2
    have := le_of_mul_le_mul_left this hπh
    linarith

end TJK
