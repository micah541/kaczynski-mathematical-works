import Mathlib
import TJK.Defs

/-!
# Regions in the upper half-plane (blueprint §F, "Regions")

Formalizes `def:regions`, `lem:B-char`, the predicate `Split` of `def:special-family`, and
`lem:region-geometry` (R1)–(R10) of `paper/sections/F-construct.tex`.

Points `⟨x, y⟩` of the upper half-plane are complex numbers `z` with `x = z.re`, `y = z.im`
(as in `TJK.upper`). The real axis is `{z : ℂ | z.im = 0}`.

* `stolz a ε θ` is the Stolz angle `s(a, ε, θ)`;
* `trap a b ε θ` is `Trap(J, ε, θ)` and `tri a b θ` is `Tri(J, θ)` for the interval `J` with
  endpoints `a ≤ b`;
* `hull K` is `J(K) = [min K, max K]`; `gaps K` is the set of endpoint pairs `(a, b)` of the
  components `(a, b)` of `J(K) \ K` (see `connectedComponentIn_hull_diff` and `exists_gap`);
* `region K ε α β` is `B(K, ε, α, β) = Trap(J(K), ε, α) \ ⋃_{I} Tri(I, β)`.

Hypotheses that the paper states but the proofs do not need are omitted (this only strengthens
the statements). Distance hypotheses of the form `η ≤ d / c` are kept in that form; for (R6) the
distance `dist(K₁, K₂)` is expressed pointwise.
-/

namespace TJK.Construct

open Set Metric Real

/-! ### The cotangent on `(0, π/2)` -/

theorem cot_eq_inv_tan (x : ℝ) : cot x = (tan x)⁻¹ := by
  rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, inv_div]

theorem cot_pos_of_lt_pi_div_two {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) : 0 < cot θ := by
  rw [cot_eq_inv_tan]
  exact inv_pos.2 (tan_pos_of_pos_of_lt_pi_div_two h0 h1)

theorem cot_lt_cot_of_lt {θ θ' : ℝ} (h0 : 0 < θ) (hlt : θ < θ') (h1 : θ' < π / 2) :
    cot θ' < cot θ := by
  rw [cot_eq_inv_tan, cot_eq_inv_tan]
  exact inv_strictAnti₀ (tan_pos_of_pos_of_lt_pi_div_two h0 (hlt.trans h1))
    (tan_lt_tan_of_nonneg_of_lt_pi_div_two h0.le h1 hlt)

/-! ### Definitions (`def:regions`, `def:special-family`) -/

/-- The Stolz angle `s(a, ε, θ) = {⟨x, y⟩ : 0 < y < ε, |x - a| < y cot θ}`. -/
def stolz (a ε θ : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ z.im < ε ∧ |z.re - a| < z.im * cot θ}

/-- The trapezoid `Trap(J, ε, θ)` over the interval `J` with endpoints `a ≤ b`. -/
def trap (a b ε θ : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ z.im < ε ∧ a + z.im * cot θ < z.re ∧ z.re < b - z.im * cot θ}

/-- The closed triangle `Tri(J, θ)` over the interval `J` with endpoints `a ≤ b`. -/
def tri (a b θ : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ a + z.im * cot θ ≤ z.re ∧ z.re ≤ b - z.im * cot θ}

/-- `J(K) = [min K, max K]`. -/
def hull (K : Set ℝ) : Set ℝ :=
  Icc (sInf K) (sSup K)

/-- The components of `J(K) \ K`, recorded by their endpoints: the pairs `(a, b)` with
`a, b ∈ K`, `a < b` and `(a, b) ∩ K = ∅` (see `connectedComponentIn_hull_diff`, `exists_gap`). -/
def gaps (K : Set ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ K ∧ p.2 ∈ K ∧ p.1 < p.2 ∧ Disjoint (Ioo p.1 p.2) K}

/-- `B(K, ε, α, β) = Trap(J(K), ε, α) \ ⋃_{I ∈ 𝒥(K)} Tri(I, β)`. -/
def region (K : Set ℝ) (ε α β : ℝ) : Set ℂ :=
  trap (sInf K) (sSup K) ε α \ ⋃ p ∈ gaps K, tri p.1 p.2 β

/-- Two sets of reals *split* if some `p` lies (weakly) above one and below the other. -/
def Split (E₁ E₂ : Set ℝ) : Prop :=
  ∃ p : ℝ, ((∀ x ∈ E₁, x ≤ p) ∧ ∀ x ∈ E₂, p ≤ x) ∨ ((∀ x ∈ E₂, x ≤ p) ∧ ∀ x ∈ E₁, p ≤ x)

/-! ### The components of `J(K) \ K` -/

theorem Ioo_subset_hull_diff {K : Set ℝ} (hK : IsCompact K) {p : ℝ × ℝ} (hp : p ∈ gaps K) :
    Ioo p.1 p.2 ⊆ hull K \ K := by
  intro x hx
  refine ⟨⟨(csInf_le hK.bddBelow hp.1).trans hx.1.le, hx.2.le.trans (le_csSup hK.bddAbove hp.2.1)⟩,
    fun hxK => disjoint_left.1 hp.2.2.2 hx hxK⟩

/-- Each `Ioo a b` with `(a, b) ∈ gaps K` is a connected component of `J(K) \ K`. -/
theorem connectedComponentIn_hull_diff {K : Set ℝ} (hK : IsCompact K) {p : ℝ × ℝ}
    (hp : p ∈ gaps K) {x : ℝ} (hx : x ∈ Ioo p.1 p.2) :
    connectedComponentIn (hull K \ K) x = Ioo p.1 p.2 := by
  apply Subset.antisymm _ (isPreconnected_Ioo.subset_connectedComponentIn hx
    (Ioo_subset_hull_diff hK hp))
  have hC := isPreconnected_connectedComponentIn (F := hull K \ K) (x := x)
  have hxC : x ∈ connectedComponentIn (hull K \ K) x :=
    mem_connectedComponentIn (Ioo_subset_hull_diff hK hp hx)
  have hsub := connectedComponentIn_subset (hull K \ K) x
  intro y hy
  constructor
  · by_contra h
    push Not at h
    have : p.1 ∈ connectedComponentIn (hull K \ K) x :=
      hC.Icc_subset hy hxC ⟨h, hx.1.le⟩
    exact (hsub this).2 hp.1
  · by_contra h
    push Not at h
    have : p.2 ∈ connectedComponentIn (hull K \ K) x :=
      hC.Icc_subset hxC hy ⟨hx.2.le, h⟩
    exact (hsub this).2 hp.2.1

/-- Every point of `J(K) \ K` lies in one of the intervals of `gaps K`. -/
theorem exists_gap {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) {x : ℝ} (hx : x ∈ hull K)
    (hxK : x ∉ K) : ∃ p ∈ gaps K, x ∈ Ioo p.1 p.2 := by
  have hL : (K ∩ Iic x).Nonempty := ⟨sInf K, hK.sInf_mem hne, hx.1⟩
  have hR : (K ∩ Ici x).Nonempty := ⟨sSup K, hK.sSup_mem hne, hx.2⟩
  have hLc : IsCompact (K ∩ Iic x) := hK.inter_right isClosed_Iic
  have hRc : IsCompact (K ∩ Ici x) := hK.inter_right isClosed_Ici
  have ha := hLc.sSup_mem hL
  have hb := hRc.sInf_mem hR
  have hax : sSup (K ∩ Iic x) < x := lt_of_le_of_ne ha.2 fun h => hxK (h ▸ ha.1)
  have hxb : x < sInf (K ∩ Ici x) := lt_of_le_of_ne hb.2 fun h => hxK (h ▸ hb.1)
  refine ⟨(sSup (K ∩ Iic x), sInf (K ∩ Ici x)), ⟨ha.1, hb.1, hax.trans hxb, ?_⟩, hax, hxb⟩
  rw [disjoint_left]
  rintro k ⟨hk1, hk2⟩ hk
  rcases le_total k x with h | h
  · exact absurd (le_csSup hLc.bddAbove ⟨hk, h⟩) (not_le.2 hk1)
  · exact absurd (csInf_le hRc.bddBelow ⟨hk, h⟩) (not_le.2 hk2)

/-! ### Description of `B` (`lem:B-char`) -/

theorem mem_region_iff {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) {ε α β : ℝ}
    (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β) (hβ1 : β < π / 2) {z : ℂ} :
    z ∈ region K ε α β ↔ 0 < z.im ∧ z.im < ε ∧ sInf K + z.im * cot α < z.re ∧
      z.re < sSup K - z.im * cot α ∧ infDist z.re K < z.im * cot β := by
  have hcα := cot_pos_of_lt_pi_div_two hα0 hα1
  have hcβ := cot_pos_of_lt_pi_div_two hβ0 hβ1
  constructor
  · rintro ⟨⟨hy, hyε, h1, h2⟩, hno⟩
    refine ⟨hy, hyε, h1, h2, ?_⟩
    by_contra hge
    push Not at hge
    have hyc : 0 < z.im * cot β := mul_pos hy hcβ
    have hyα : 0 < z.im * cot α := mul_pos hy hcα
    have hxK : z.re ∉ K := fun h => by
      rw [infDist_zero_of_mem h] at hge
      linarith
    obtain ⟨p, hp, hxp⟩ := exists_gap hK hne ⟨by linarith, by linarith⟩ hxK
    apply hno
    refine mem_iUnion₂.2 ⟨p, hp, hy.le, ?_, ?_⟩
    · have := infDist_le_dist_of_mem (x := z.re) hp.1
      rw [Real.dist_eq, abs_of_pos (by linarith [hxp.1])] at this
      linarith
    · have := infDist_le_dist_of_mem (x := z.re) hp.2.1
      rw [Real.dist_eq, abs_of_neg (by linarith [hxp.2])] at this
      linarith
  · rintro ⟨hy, hyε, h1, h2, hd⟩
    refine ⟨⟨hy, hyε, h1, h2⟩, fun hmem => ?_⟩
    obtain ⟨p, hp, -, ha, hb⟩ := mem_iUnion₂.1 hmem
    have hyc : 0 < z.im * cot β := mul_pos hy hcβ
    have : z.im * cot β ≤ infDist z.re K := by
      rw [le_infDist hne]
      intro k hk
      rw [Real.dist_eq]
      have hk' : k ∉ Ioo p.1 p.2 := fun h => disjoint_left.1 hp.2.2.2 h hk
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hk'
      rcases hk' with hk' | hk'
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith)]
        linarith
    linarith

theorem region_eq {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) {ε α β : ℝ}
    (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β) (hβ1 : β < π / 2) :
    region K ε α β = {z : ℂ | 0 < z.im ∧ z.im < ε ∧ sInf K + z.im * cot α < z.re ∧
      z.re < sSup K - z.im * cot α ∧ infDist z.re K < z.im * cot β} :=
  Set.ext fun _ => mem_region_iff hK hne hα0 hα1 hβ0 hβ1

theorem region_subset_trap (K : Set ℝ) (ε α β : ℝ) :
    region K ε α β ⊆ trap (sInf K) (sSup K) ε α :=
  sdiff_subset

/-! ### Closures -/

theorem closure_stolz_subset_setOf (a ε θ : ℝ) :
    closure (stolz a ε θ) ⊆ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ ε ∧ |z.re - a| ≤ z.im * cot θ} := by
  refine closure_minimal (fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩) ?_
  exact (isClosed_le continuous_const Complex.continuous_im).inter
    ((isClosed_le Complex.continuous_im continuous_const).inter
      (isClosed_le (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
        (Complex.continuous_im.mul continuous_const)))

theorem closure_region_subset_setOf {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    {ε α β : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β) (hβ1 : β < π / 2) :
    closure (region K ε α β) ⊆ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ ε ∧ sInf K + z.im * cot α ≤ z.re ∧
      z.re ≤ sSup K - z.im * cot α ∧ infDist z.re K ≤ z.im * cot β} := by
  refine closure_minimal (fun z hz => ?_) ?_
  · obtain ⟨h0, h1, h2, h3, h4⟩ := (mem_region_iff hK hne hα0 hα1 hβ0 hβ1).1 hz
    exact ⟨h0.le, h1.le, h2.le, h3.le, h4.le⟩
  have hI : Continuous fun z : ℂ => z.im * cot α := Complex.continuous_im.mul continuous_const
  exact (isClosed_le continuous_const Complex.continuous_im).inter
    ((isClosed_le Complex.continuous_im continuous_const).inter
      ((isClosed_le (continuous_const.add hI) Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re (continuous_const.sub hI)).inter
          (isClosed_le ((continuous_infDist_pt K).comp Complex.continuous_re)
            (Complex.continuous_im.mul continuous_const)))))

/-! ### `lem:region-geometry` -/

/-- (R1) -/
theorem isOpen_stolz (a ε θ : ℝ) : IsOpen (stolz a ε θ) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter
      (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
        (Complex.continuous_im.mul continuous_const)))

/-- (R1) -/
theorem stolz_subset_upper (a ε θ : ℝ) : stolz a ε θ ⊆ upper :=
  fun _ hz => hz.1

/-- (R1) -/
theorem isOpen_region {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) {ε α β : ℝ}
    (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β) (hβ1 : β < π / 2) :
    IsOpen (region K ε α β) := by
  rw [region_eq hK hne hα0 hα1 hβ0 hβ1]
  have hI : Continuous fun z : ℂ => z.im * cot α := Complex.continuous_im.mul continuous_const
  exact (isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter
      ((isOpen_lt (continuous_const.add hI) Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re (continuous_const.sub hI)).inter
          (isOpen_lt ((continuous_infDist_pt K).comp Complex.continuous_re)
            (Complex.continuous_im.mul continuous_const)))))

/-- (R1) -/
theorem region_subset_upper (K : Set ℝ) (ε α β : ℝ) : region K ε α β ⊆ upper :=
  fun _ hz => hz.1.1

/-- (R2) -/
theorem closure_stolz_inter_axis {a ε θ : ℝ} (hε : 0 < ε) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    closure (stolz a ε θ) ∩ {z : ℂ | z.im = 0} = {(a : ℂ)} := by
  have hc := cot_pos_of_lt_pi_div_two hθ0 hθ1
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hz, h0⟩
    obtain ⟨-, -, h⟩ := closure_stolz_subset_setOf a ε θ hz
    rw [h0, zero_mul] at h
    have : z.re - a = 0 := abs_nonpos_iff.1 h
    apply Complex.ext
    · simp only [Complex.ofReal_re]; linarith
    · simp [h0]
  · rintro rfl
    refine ⟨Metric.mem_closure_iff.2 fun δ hδ => ?_, Complex.ofReal_im a⟩
    refine ⟨⟨a, min (δ / 2) (ε / 2)⟩, ⟨lt_min (by linarith) (by linarith),
      (min_le_right _ _).trans_lt (by linarith), ?_⟩, ?_⟩
    · simp only [sub_self, abs_zero]
      exact mul_pos (lt_min (by linarith) (by linarith)) hc
    · rw [Complex.dist_of_re_eq (by simp)]
      simp only [Complex.ofReal_im, Real.dist_eq, zero_sub, abs_neg]
      rw [abs_of_pos (lt_min (by linarith) (by linarith))]
      exact (min_le_left _ _).trans_lt (by linarith)

/-- (R2) -/
theorem closure_region_inter_axis {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    {ε α β : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β) (hβ1 : β < π / 2) :
    closure (region K ε α β) ∩ {z : ℂ | z.im = 0} ⊆ (fun x : ℝ => (x : ℂ)) '' K := by
  rintro z ⟨hz, h0⟩
  obtain ⟨-, -, -, -, h⟩ := closure_region_subset_setOf hK hne hα0 hα1 hβ0 hβ1 hz
  have h0 : z.im = 0 := h0
  rw [h0, zero_mul] at h
  have : infDist z.re K = 0 := le_antisymm h infDist_nonneg
  refine ⟨z.re, (hK.isClosed.mem_iff_infDist_zero hne).2 this, ?_⟩
  apply Complex.ext <;> simp [h0]

/-- (R3) -/
theorem closure_stolz_subset {a ε ε' θ θ' : ℝ} (hε : ε < ε') (hθ'0 : 0 < θ') (hθθ' : θ' < θ)
    (hθ1 : θ < π / 2) : closure (stolz a ε θ) ∩ upper ⊆ stolz a ε' θ' := by
  rintro z ⟨hz, hpos⟩
  have hpos : 0 < z.im := hpos
  obtain ⟨-, h1, h2⟩ := closure_stolz_subset_setOf a ε θ hz
  exact ⟨hpos, by linarith,
    h2.trans_lt (mul_lt_mul_of_pos_left (cot_lt_cot_of_lt hθ'0 hθθ' hθ1) hpos)⟩

/-- (R4) -/
theorem stolz_disjoint {a b ε η θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < π / 2)
    (hη : η ≤ |a - b| / (2 * cot θ)) : Disjoint (stolz a ε θ) (stolz b η θ) := by
  have hc := cot_pos_of_lt_pi_div_two hθ0 hθ1
  rw [le_div_iff₀ (by positivity)] at hη
  rw [disjoint_left]
  rintro z ⟨-, -, h2⟩ ⟨-, h1', h2'⟩
  have h3 : |a - b| ≤ |z.re - a| + |z.re - b| := by
    rw [abs_sub_comm z.re a]; exact abs_sub_le a z.re b
  have h4 : z.im * cot θ < η * cot θ := mul_lt_mul_of_pos_right h1' hc
  linarith

/-- (R5) -/
theorem region_disjoint_of_split {K₁ K₂ : Set ℝ} (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty)
    {ε₁ ε₂ α β : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (h : Split K₁ K₂) :
    Disjoint (region K₁ ε₁ α β) (region K₂ ε₂ α β) := by
  have hc := cot_pos_of_lt_pi_div_two hα0 hα1
  rw [disjoint_left]
  rintro z ⟨⟨hy, -, h1, h2⟩, -⟩ ⟨⟨-, -, h1', h2'⟩, -⟩
  have hyc : 0 < z.im * cot α := mul_pos hy hc
  obtain ⟨p, ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩⟩ := h
  · have := csSup_le hne₁ hp1
    have := le_csInf hne₂ hp2
    linarith
  · have := csSup_le hne₂ hp1
    have := le_csInf hne₁ hp2
    linarith

/-- (R6) The hypothesis `hη` says `η ≤ dist(K₁, K₂) / (2 cot β)`. -/
theorem region_disjoint_of_disjoint {K₁ K₂ : Set ℝ} (hK₁ : IsCompact K₁) (hne₁ : K₁.Nonempty)
    (hK₂ : IsCompact K₂) (hne₂ : K₂.Nonempty) {ε η α β : ℝ}
    (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β) (hβ1 : β < π / 2)
    (hη : ∀ x₁ ∈ K₁, ∀ x₂ ∈ K₂, η ≤ |x₁ - x₂| / (2 * cot β)) :
    Disjoint (region K₁ ε α β) (region K₂ η α β) := by
  have hc := cot_pos_of_lt_pi_div_two hβ0 hβ1
  rw [disjoint_left]
  intro z hz1 hz2
  obtain ⟨-, -, -, -, hd1⟩ := (mem_region_iff hK₁ hne₁ hα0 hα1 hβ0 hβ1).1 hz1
  obtain ⟨-, hyη, -, -, hd2⟩ := (mem_region_iff hK₂ hne₂ hα0 hα1 hβ0 hβ1).1 hz2
  obtain ⟨k₁, hk₁, hd1⟩ := (infDist_lt_iff hne₁).1 hd1
  obtain ⟨k₂, hk₂, hd2⟩ := (infDist_lt_iff hne₂).1 hd2
  have h := hη k₁ hk₁ k₂ hk₂
  rw [le_div_iff₀ (by positivity)] at h
  rw [Real.dist_eq] at hd1 hd2
  have h3 : |k₁ - k₂| ≤ |z.re - k₁| + |z.re - k₂| := by
    rw [abs_sub_comm z.re k₁]; exact abs_sub_le k₁ z.re k₂
  have h4 : z.im * cot β < η * cot β := mul_lt_mul_of_pos_right hyη hc
  linarith

/-- (R7) -/
theorem closure_region_subset {K K₁ : Set ℝ} (hK : IsCompact K) (hK₁ : IsCompact K₁)
    (hne₁ : K₁.Nonempty) (hsub : K₁ ⊆ K) {ε ε₁ α α₁ β β₁ : ℝ} (hε : ε₁ < ε)
    (hβ0 : 0 < β) (hββ₁ : β < β₁) (hβ₁α₁ : β₁ < α₁) (hα₁α : α₁ < α) (hα1 : α < π / 2) :
    closure (region K₁ ε₁ α₁ β₁) ∩ upper ⊆ region K ε α β := by
  have hne : K.Nonempty := hne₁.mono hsub
  have hα₁0 : 0 < α₁ := hβ0.trans (hββ₁.trans hβ₁α₁)
  have hα₁1 : α₁ < π / 2 := hα₁α.trans hα1
  have hβ₁1 : β₁ < π / 2 := hβ₁α₁.trans hα₁1
  rintro z ⟨hz, hpos⟩
  have hpos : 0 < z.im := hpos
  obtain ⟨-, h1, h2, h3, h4⟩ :=
    closure_region_subset_setOf hK₁ hne₁ hα₁0 hα₁1 (hβ0.trans hββ₁) hβ₁1 hz
  have hinf := csInf_le_csInf hK.bddBelow hne₁ hsub
  have hsup := csSup_le_csSup hK.bddAbove hne₁ hsub
  have hα := mul_lt_mul_of_pos_left (cot_lt_cot_of_lt hα₁0 hα₁α hα1) hpos
  have hβ := mul_lt_mul_of_pos_left (cot_lt_cot_of_lt hβ0 hββ₁ hβ₁1) hpos
  have hd := infDist_le_infDist_of_subset (x := z.re) hsub hne₁
  rw [mem_region_iff hK hne (hα₁0.trans hα₁α) hα1 hβ0 (hββ₁.trans hβ₁1)]
  exact ⟨hpos, by linarith, by linarith, by linarith, by linarith⟩

/-- (R8) -/
theorem region_stolz_disjoint_of_not_mem_interior {K : Set ℝ} {a ε ε₁ α β θ : ℝ}
    (hα0 : 0 < α) (hαθ : α < θ) (hθ1 : θ < π / 2) (ha : a ∉ Ioo (sInf K) (sSup K)) :
    Disjoint (region K ε α β) (stolz a ε₁ θ) := by
  rw [disjoint_left]
  rintro z ⟨⟨hy, -, h1, h2⟩, -⟩ ⟨-, -, h3⟩
  have := mul_lt_mul_of_pos_left (cot_lt_cot_of_lt hα0 hαθ hθ1) hy
  rw [abs_lt] at h3
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at ha
  rcases ha with ha | ha <;> linarith [h3.1, h3.2]

/-- (R9), first half. The hypothesis `a ∉ K` of the paper is implied when `η > 0`. -/
theorem stolz_region_disjoint_small_stolz {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    {a ε η α β θ : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β) (hβ1 : β < π / 2)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) (hη : η ≤ infDist a K / (cot θ + cot β)) :
    Disjoint (stolz a η θ) (region K ε α β) := by
  have hcθ := cot_pos_of_lt_pi_div_two hθ0 hθ1
  have hcβ := cot_pos_of_lt_pi_div_two hβ0 hβ1
  rw [le_div_iff₀ (by positivity)] at hη
  rw [disjoint_left]
  intro z ⟨hy, hyη, h1⟩ hz
  obtain ⟨-, -, -, -, h2⟩ := (mem_region_iff hK hne hα0 hα1 hβ0 hβ1).1 hz
  have h3 := infDist_le_infDist_add_dist (s := K) (x := a) (y := z.re)
  rw [Real.dist_eq, abs_sub_comm] at h3
  have h4 : z.im * (cot θ + cot β) < η * (cot θ + cot β) :=
    mul_lt_mul_of_pos_right hyη (by positivity)
  rw [mul_add, mul_add] at h4
  linarith

/-- (R9), second half. -/
theorem stolz_region_disjoint_small_region {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    {a ε η α β θ : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β) (hβ1 : β < π / 2)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) (hη : η ≤ infDist a K / (cot θ + cot β)) :
    Disjoint (stolz a ε θ) (region K η α β) := by
  have hcθ := cot_pos_of_lt_pi_div_two hθ0 hθ1
  have hcβ := cot_pos_of_lt_pi_div_two hβ0 hβ1
  rw [le_div_iff₀ (by positivity)] at hη
  rw [disjoint_left]
  intro z ⟨_, _, h1⟩ hz
  obtain ⟨-, hyη, -, -, h2⟩ := (mem_region_iff hK hne hα0 hα1 hβ0 hβ1).1 hz
  have h3 := infDist_le_infDist_add_dist (s := K) (x := a) (y := z.re)
  rw [Real.dist_eq, abs_sub_comm] at h3
  have h4 : z.im * (cot θ + cot β) < η * (cot θ + cot β) :=
    mul_lt_mul_of_pos_right hyη (by positivity)
  rw [mul_add, mul_add] at h4
  linarith

/-- (R10) The hypothesis `a ∈ J(K)^*` of the paper is implied by `h₁`, `h₂` when `η > 0`. -/
theorem closure_stolz_subset_region {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    {a ε η α β θ : ℝ} (ha : a ∈ K) (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 < β)
    (hβθ : β < θ) (hθ1 : θ < π / 2) (hηε : η < ε)
    (h₁ : η < (a - sInf K) / (cot θ + cot α)) (h₂ : η < (sSup K - a) / (cot θ + cot α)) :
    closure (stolz a η θ) ∩ upper ⊆ region K ε α β := by
  have hθ0 : 0 < θ := hβ0.trans hβθ
  have hcθ := cot_pos_of_lt_pi_div_two hθ0 hθ1
  have hcα := cot_pos_of_lt_pi_div_two hα0 hα1
  rw [lt_div_iff₀ (by positivity), mul_add] at h₁ h₂
  rintro z ⟨hz, hpos⟩
  have hpos : 0 < z.im := hpos
  obtain ⟨-, hyη, h⟩ := closure_stolz_subset_setOf a η θ hz
  have hθβ := mul_lt_mul_of_pos_left (cot_lt_cot_of_lt hβ0 hβθ hθ1) hpos
  have hθη := mul_le_mul_of_nonneg_right hyη hcθ.le
  have hαη := mul_le_mul_of_nonneg_right hyη hcα.le
  have hd := infDist_le_dist_of_mem (x := z.re) ha
  rw [Real.dist_eq] at hd
  have h' := abs_le.1 h
  rw [mem_region_iff hK hne hα0 hα1 hβ0 (hβθ.trans hθ1)]
  exact ⟨hpos, by linarith, by linarith, by linarith, by linarith⟩

end TJK.Construct
