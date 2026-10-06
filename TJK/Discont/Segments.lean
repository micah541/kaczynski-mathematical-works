import Mathlib
import TJK.Defs
import TJK.Discont.NullRange

/-!
# Unions of disjoint segments (blueprint `def:trapezoid`, `lem:th-lemma23`, `lem:th-lemma24`,
`thm:th-thm9`, `thm:th-thm10`)

Points of the plane are pairs `(x, y) : ℝ × ℝ`. A segment joining `X₀ = ℝ × {0}` to `X₁ = ℝ × {1}`
is described by its pair of abscissas `p = (p.1, p.2)`: it is `segment01 p`, the set of
`(segLine p y, y)` with `0 ≤ y ≤ 1`, where `segLine p y = (1 - y) p.1 + y p.2`.
-/

open MeasureTheory Set Filter Topology Pointwise

namespace TJK.Discont

/-- The abscissa at height `y` of the line through `(p.1, 0)` and `(p.2, 1)`. -/
def segLine (p : ℝ × ℝ) (y : ℝ) : ℝ := (1 - y) * p.1 + y * p.2

/-- The closed segment from `(p.1, 0)` to `(p.2, 1)`. -/
def segment01 (p : ℝ × ℝ) : Set (ℝ × ℝ) := {z | z.2 ∈ Icc (0 : ℝ) 1 ∧ z.1 = segLine p z.2}

/-- The closed trapezoid `T(a₀, b₀; a₁, b₁)` (blueprint `def:trapezoid`, finite parameters). -/
def closedTrapezoid (a₀ b₀ a₁ b₁ : ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Icc (0 : ℝ) 1 ∧ segLine (a₀, a₁) z.2 ≤ z.1 ∧ z.1 ≤ segLine (b₀, b₁) z.2}

lemma isClosed_closedTrapezoid (a₀ b₀ a₁ b₁ : ℝ) : IsClosed (closedTrapezoid a₀ b₀ a₁ b₁) := by
  have hc : ∀ q : ℝ × ℝ, Continuous fun z : ℝ × ℝ => segLine q z.2 := fun q => by
    unfold segLine; fun_prop
  convert ((isClosed_le (continuous_const : Continuous fun _ : ℝ × ℝ => (0 : ℝ)) continuous_snd).inter
    (isClosed_le continuous_snd (continuous_const : Continuous fun _ : ℝ × ℝ => (1 : ℝ)))).inter
    ((isClosed_le (hc (a₀, a₁)) continuous_fst).inter (isClosed_le continuous_fst (hc (b₀, b₁))))
    using 1
  ext z; simp [closedTrapezoid, and_assoc]

lemma volume_closedTrapezoid {a₀ b₀ a₁ b₁ : ℝ} (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) :
    volume (closedTrapezoid a₀ b₀ a₁ b₁) = ENNReal.ofReal (((b₀ - a₀) + (b₁ - a₁)) / 2) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (isClosed_closedTrapezoid _ _ _ _).measurableSet]
  have hsec : ∀ y : ℝ, volume ((fun x => (x, y)) ⁻¹' closedTrapezoid a₀ b₀ a₁ b₁) =
      (Icc (0 : ℝ) 1).indicator (fun y => ENNReal.ofReal ((1 - y) * (b₀ - a₀) + y * (b₁ - a₁))) y := by
    intro y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hy]
      have : (fun x => (x, y)) ⁻¹' closedTrapezoid a₀ b₀ a₁ b₁ = Icc (segLine (a₀, a₁) y) (segLine (b₀, b₁) y) := by
        ext x; simp [closedTrapezoid, hy.1, hy.2]
      rw [this, Real.volume_Icc]
      congr 1; simp only [segLine]; ring
    · rw [indicator_of_notMem hy]
      have : (fun x => (x, y)) ⁻¹' closedTrapezoid a₀ b₀ a₁ b₁ = ∅ := by
        ext x
        simp only [mem_Icc, not_and_or, not_le] at hy
        simp only [closedTrapezoid, mem_preimage, mem_Icc, mem_ofPred_eq, mem_empty_iff_false,
          iff_false, not_and]
        intro h1 h2; rcases hy with hy | hy <;> linarith
      rw [this, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp
    ring
  · exact (Continuous.integrableOn_Icc (by fun_prop))
  · refine (ae_restrict_mem measurableSet_Icc).mono fun y hy => ?_
    simp only [Pi.zero_apply]
    have := hy.1; have := hy.2
    nlinarith

/-! ### Order of disjoint segments -/

lemma segment01_inter_nonempty {p p' : ℝ × ℝ} (h₀ : p.1 ≤ p'.1) (h₁ : p'.2 ≤ p.2) :
    (segment01 p ∩ segment01 p').Nonempty := by
  rcases eq_or_lt_of_le (add_nonneg (sub_nonneg.2 h₀) (sub_nonneg.2 h₁)) with h | h
  · refine ⟨(p.1, 0), ⟨⟨le_rfl, zero_le_one⟩, by simp [segLine]⟩, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp [segLine]; linarith
  · set y := (p'.1 - p.1) / ((p'.1 - p.1) + (p.2 - p'.2)) with hy
    have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.2 h₀) h.le
    have hy1 : y ≤ 1 := (div_le_one h).2 (by linarith)
    refine ⟨(segLine p y, y), ⟨⟨hy0, hy1⟩, rfl⟩, ⟨hy0, hy1⟩, ?_⟩
    have e : y * ((p'.1 - p.1) + (p.2 - p'.2)) = p'.1 - p.1 := div_mul_cancel₀ _ h.ne'
    simp only [segLine]
    linear_combination e

lemma snd_le_of_fst_le {P : Set (ℝ × ℝ)} (hP : P.PairwiseDisjoint segment01) {p p' : ℝ × ℝ}
    (hp : p ∈ P) (hp' : p' ∈ P) (h : p.1 ≤ p'.1) : p.2 ≤ p'.2 := by
  by_contra h'
  rw [not_le] at h'
  have hne : p ≠ p' := by rintro rfl; exact lt_irrefl _ h'
  exact Set.not_disjoint_iff_nonempty_inter.2 (segment01_inter_nonempty h h'.le) (hP hp hp' hne)

lemma fst_le_of_snd_le {P : Set (ℝ × ℝ)} (hP : P.PairwiseDisjoint segment01) {p p' : ℝ × ℝ}
    (hp : p ∈ P) (hp' : p' ∈ P) (h : p.2 ≤ p'.2) : p.1 ≤ p'.1 := by
  by_contra h'
  rw [not_le] at h'
  have hne : p' ≠ p := by rintro rfl; exact lt_irrefl _ h'
  exact Set.not_disjoint_iff_nonempty_inter.2 (segment01_inter_nonempty h'.le h) (hP hp' hp hne)

lemma snd_lt_of_fst_lt {P : Set (ℝ × ℝ)} (hP : P.PairwiseDisjoint segment01) {p p' : ℝ × ℝ}
    (hp : p ∈ P) (hp' : p' ∈ P) (h : p.1 < p'.1) : p.2 < p'.2 :=
  lt_of_not_ge fun h' => h.not_ge (fst_le_of_snd_le hP hp' hp h')

lemma fst_lt_of_snd_lt {P : Set (ℝ × ℝ)} (hP : P.PairwiseDisjoint segment01) {p p' : ℝ × ℝ}
    (hp : p ∈ P) (hp' : p' ∈ P) (h : p.2 < p'.2) : p.1 < p'.1 :=
  lt_of_not_ge fun h' => h.not_ge (snd_le_of_fst_le hP hp' hp h')

/-! ### Components of open subsets of the line -/

lemma ordConnected_connectedComponentIn (G : Set ℝ) (x : ℝ) :
    (connectedComponentIn G x).OrdConnected :=
  isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn

lemma connectedComponentIn_eq_or_disjoint (G : Set ℝ) (x y : ℝ) :
    connectedComponentIn G x = connectedComponentIn G y ∨
      Disjoint (connectedComponentIn G x) (connectedComponentIn G y) := by
  by_cases h : Disjoint (connectedComponentIn G x) (connectedComponentIn G y)
  · exact Or.inr h
  · left
    obtain ⟨z, hx, hy⟩ := not_disjoint_iff.1 h
    rw [connectedComponentIn_eq hx, connectedComponentIn_eq hy]

lemma countable_components {G : Set ℝ} (hG : IsOpen G) :
    ((fun x => connectedComponentIn G x) '' G).Countable := by
  refine Set.PairwiseDisjoint.countable_of_isOpen (s := id) ?_ ?_ ?_
  · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hne
    exact (connectedComponentIn_eq_or_disjoint G x y).resolve_left hne
  · rintro _ ⟨x, -, rfl⟩; exact hG.connectedComponentIn
  · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, mem_connectedComponentIn hx⟩

lemma bddAbove_of_ordConnected {I : Set ℝ} (hI : I.OrdConnected) (h : volume I ≠ ⊤) :
    BddAbove I := by
  by_contra hb
  rcases I.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact hb bddAbove_empty
  refine h (top_unique ((Real.volume_Ici (a := x)).symm.le.trans (measure_mono fun z hz => ?_)))
  obtain ⟨w, hw, hzw⟩ := not_bddAbove_iff.1 hb z
  exact hI.out hx hw ⟨hz, hzw.le⟩

lemma bddBelow_of_ordConnected {I : Set ℝ} (hI : I.OrdConnected) (h : volume I ≠ ⊤) :
    BddBelow I := by
  by_contra hb
  rcases I.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact hb bddBelow_empty
  refine h (top_unique ((Real.volume_Iic (a := x)).symm.le.trans (measure_mono fun z hz => ?_)))
  obtain ⟨w, hw, hzw⟩ := not_bddBelow_iff.1 hb z
  exact hI.out hw hx ⟨hzw.le, hz⟩

lemma Ioo_csInf_csSup_subset {A K : Set ℝ} (hK : K.OrdConnected) (hA : A ⊆ K) :
    Ioo (sInf A) (sSup A) ⊆ K := by
  intro x hx
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [Real.sInf_empty, Real.sSup_empty] at hx
  obtain ⟨a, ha, hax⟩ := exists_lt_of_csInf_lt hne hx.1
  obtain ⟨b, hb, hxb⟩ := exists_lt_of_lt_csSup hne hx.2
  exact hK.out (hA ha) (hA hb) ⟨hax.le, hxb.le⟩

/-- Two families of points whose `v`-values lie in disjoint intervals `K`, `L`, and whose `u`- and
`v`-values are ordered alike, have disjoint open `u`-hulls. -/
lemma disjoint_Ioo_of_comonotone {ι : Type*} {u v : ι → ℝ} {s t : Set ι} {K L : Set ℝ}
    (hK : K.OrdConnected) (hL : L.OrdConnected) (hKL : Disjoint K L)
    (hs : ∀ i ∈ s, v i ∈ K) (ht : ∀ i ∈ t, v i ∈ L)
    (hmono : ∀ i ∈ s ∪ t, ∀ j ∈ s ∪ t, u i < u j → v i < v j) :
    Disjoint (Ioo (sInf (u '' s)) (sSup (u '' s))) (Ioo (sInf (u '' t)) (sSup (u '' t))) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have nes : (u '' s).Nonempty := by
    by_contra h; rw [not_nonempty_iff_eq_empty] at h
    simp [h, Real.sInf_empty, Real.sSup_empty] at hx
  have net : (u '' t).Nonempty := by
    by_contra h; rw [not_nonempty_iff_eq_empty] at h
    simp [h, Real.sInf_empty, Real.sSup_empty] at hx'
  obtain ⟨_, ⟨i₁, hi₁, rfl⟩, h1⟩ := exists_lt_of_csInf_lt nes hx.1
  obtain ⟨_, ⟨i₂, hi₂, rfl⟩, h2⟩ := exists_lt_of_lt_csSup nes hx.2
  obtain ⟨_, ⟨j₁, hj₁, rfl⟩, h3⟩ := exists_lt_of_csInf_lt net hx'.1
  obtain ⟨_, ⟨j₂, hj₂, rfl⟩, h4⟩ := exists_lt_of_lt_csSup net hx'.2
  have a := hmono i₁ (Or.inl hi₁) j₂ (Or.inr hj₂) (h1.trans h4)
  have b := hmono j₁ (Or.inr hj₁) i₂ (Or.inl hi₂) (h3.trans h2)
  rcases le_total (v j₁) (v i₁) with c | c
  · exact Set.disjoint_left.1 hKL (hs i₁ hi₁) (hL.out (ht j₁ hj₁) (ht j₂ hj₂) ⟨c, a.le⟩)
  · exact Set.disjoint_left.1 hKL (hK.out (hs i₁ hi₁) (hs i₂ hi₂) ⟨c, b.le⟩) (ht j₁ hj₁)

/-! ### The upper bound -/

lemma volume_closedTrapezoid_eq_add {a₀ b₀ a₁ b₁ : ℝ} (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) :
    volume (closedTrapezoid a₀ b₀ a₁ b₁) = (volume (Ioo a₀ b₀) + volume (Ioo a₁ b₁)) / 2 := by
  rw [volume_closedTrapezoid h₀ h₁, Real.volume_Ioo, Real.volume_Ioo,
    ← ENNReal.ofReal_add (sub_nonneg.2 h₀) (sub_nonneg.2 h₁),
    ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]

lemma segment01_subset_closedTrapezoid {p : ℝ × ℝ} {a₀ b₀ a₁ b₁ : ℝ} (h₀ : p.1 ∈ Icc a₀ b₀)
    (h₁ : p.2 ∈ Icc a₁ b₁) : segment01 p ⊆ closedTrapezoid a₀ b₀ a₁ b₁ := by
  rintro z ⟨hy, hz⟩
  refine ⟨hy, ?_, ?_⟩ <;> rw [hz] <;> simp only [segLine]
  · have := mul_le_mul_of_nonneg_left h₀.1 (sub_nonneg.2 hy.2)
    have := mul_le_mul_of_nonneg_left h₁.1 hy.1
    linarith
  · have := mul_le_mul_of_nonneg_left h₀.2 (sub_nonneg.2 hy.2)
    have := mul_le_mul_of_nonneg_left h₁.2 hy.1
    linarith

/-- The key covering estimate: if the endpoints of pairwise disjoint segments lie in open sets
`G₀`, `G₁`, the union of the segments has outer measure at most `(m(G₀) + m(G₁)) / 2`. -/
lemma volume_biUnion_segment01_le_of_isOpen {P : Set (ℝ × ℝ)} (hP : P.PairwiseDisjoint segment01)
    {G₀ G₁ : Set ℝ} (ho₀ : IsOpen G₀) (ho₁ : IsOpen G₁) (h₀ : ∀ p ∈ P, p.1 ∈ G₀)
    (h₁ : ∀ p ∈ P, p.2 ∈ G₁) :
    volume (⋃ p ∈ P, segment01 p) ≤ (volume G₀ + volume G₁) / 2 := by
  rcases eq_top_or_lt_top (volume G₀) with hG₀ | hG₀
  · simp [hG₀, ENNReal.top_div]
  rcases eq_top_or_lt_top (volume G₁) with hG₁ | hG₁
  · simp [hG₁, ENNReal.top_div]
  set c : ℝ × ℝ → Set ℝ × Set ℝ :=
    fun p => (connectedComponentIn G₀ p.1, connectedComponentIn G₁ p.2) with hc
  set Q := c '' P with hQdef
  have hQ : Q.Countable := ((countable_components ho₀).prod (countable_components ho₁)).mono
    (by rintro _ ⟨p, hp, rfl⟩; exact ⟨⟨p.1, h₀ p hp, rfl⟩, ⟨p.2, h₁ p hp, rfl⟩⟩)
  set Pq : Set ℝ × Set ℝ → Set (ℝ × ℝ) := fun q => {p ∈ P | c p = q} with hPq
  set α : Set ℝ × Set ℝ → ℝ := fun q => sInf (Prod.fst '' Pq q) with hα
  set β : Set ℝ × Set ℝ → ℝ := fun q => sSup (Prod.fst '' Pq q) with hβ
  set γ : Set ℝ × Set ℝ → ℝ := fun q => sInf (Prod.snd '' Pq q) with hγ
  set δ : Set ℝ × Set ℝ → ℝ := fun q => sSup (Prod.snd '' Pq q) with hδ
  -- basic facts about a class
  have mem₁ : ∀ q, ∀ p ∈ Pq q, p.1 ∈ q.1 := by
    rintro q p ⟨hp, rfl⟩; exact mem_connectedComponentIn (h₀ p hp)
  have mem₂ : ∀ q, ∀ p ∈ Pq q, p.2 ∈ q.2 := by
    rintro q p ⟨hp, rfl⟩; exact mem_connectedComponentIn (h₁ p hp)
  have oc₁ : ∀ q ∈ Q, q.1.OrdConnected := by
    rintro _ ⟨p, -, rfl⟩; exact ordConnected_connectedComponentIn _ _
  have oc₂ : ∀ q ∈ Q, q.2.OrdConnected := by
    rintro _ ⟨p, -, rfl⟩; exact ordConnected_connectedComponentIn _ _
  have fin₁ : ∀ q ∈ Q, volume q.1 ≠ ⊤ := by
    rintro _ ⟨p, -, rfl⟩
    exact ((measure_mono (connectedComponentIn_subset _ _)).trans_lt hG₀).ne
  have fin₂ : ∀ q ∈ Q, volume q.2 ≠ ⊤ := by
    rintro _ ⟨p, -, rfl⟩
    exact ((measure_mono (connectedComponentIn_subset _ _)).trans_lt hG₁).ne
  have sub₁ : ∀ q ∈ Q, q.1 ⊆ G₀ := by rintro _ ⟨p, -, rfl⟩; exact connectedComponentIn_subset _ _
  have sub₂ : ∀ q ∈ Q, q.2 ⊆ G₁ := by rintro _ ⟨p, -, rfl⟩; exact connectedComponentIn_subset _ _
  have ne : ∀ q ∈ Q, (Pq q).Nonempty := by rintro _ ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  have img₁ : ∀ q, Prod.fst '' Pq q ⊆ q.1 := by rintro q _ ⟨p, hp, rfl⟩; exact mem₁ q p hp
  have img₂ : ∀ q, Prod.snd '' Pq q ⊆ q.2 := by rintro q _ ⟨p, hp, rfl⟩; exact mem₂ q p hp
  have bA : ∀ q ∈ Q, BddAbove (Prod.fst '' Pq q) := fun q hq =>
    (bddAbove_of_ordConnected (oc₁ q hq) (fin₁ q hq)).mono (img₁ q)
  have bB : ∀ q ∈ Q, BddBelow (Prod.fst '' Pq q) := fun q hq =>
    (bddBelow_of_ordConnected (oc₁ q hq) (fin₁ q hq)).mono (img₁ q)
  have bA' : ∀ q ∈ Q, BddAbove (Prod.snd '' Pq q) := fun q hq =>
    (bddAbove_of_ordConnected (oc₂ q hq) (fin₂ q hq)).mono (img₂ q)
  have bB' : ∀ q ∈ Q, BddBelow (Prod.snd '' Pq q) := fun q hq =>
    (bddBelow_of_ordConnected (oc₂ q hq) (fin₂ q hq)).mono (img₂ q)
  have hmem : ∀ q ∈ Q, ∀ p ∈ Pq q, p.1 ∈ Icc (α q) (β q) ∧ p.2 ∈ Icc (γ q) (δ q) := by
    intro q hq p hp
    exact ⟨⟨csInf_le (bB q hq) ⟨p, hp, rfl⟩, le_csSup (bA q hq) ⟨p, hp, rfl⟩⟩,
      ⟨csInf_le (bB' q hq) ⟨p, hp, rfl⟩, le_csSup (bA' q hq) ⟨p, hp, rfl⟩⟩⟩
  have hαβ : ∀ q ∈ Q, α q ≤ β q ∧ γ q ≤ δ q := by
    intro q hq
    obtain ⟨p, hp⟩ := ne q hq
    have := hmem q hq p hp
    exact ⟨this.1.1.trans this.1.2, this.2.1.trans this.2.2⟩
  -- the covering by trapezoids
  have cover : (⋃ p ∈ P, segment01 p) ⊆
      ⋃ q ∈ Q, closedTrapezoid (α q) (β q) (γ q) (δ q) := by
    refine iUnion₂_subset fun p hp => ?_
    have hq : c p ∈ Q := ⟨p, hp, rfl⟩
    have := hmem (c p) hq p ⟨hp, rfl⟩
    exact (segment01_subset_closedTrapezoid this.1 this.2).trans
      (subset_biUnion_of_mem (u := fun q => closedTrapezoid (α q) (β q) (γ q) (δ q)) hq)
  -- disjointness of the bases
  have hmono₁ : ∀ i ∈ P, ∀ j ∈ P, i.1 < j.1 → i.2 < j.2 := fun i hi j hj =>
    snd_lt_of_fst_lt hP hi hj
  have hmono₂ : ∀ i ∈ P, ∀ j ∈ P, i.2 < j.2 → i.1 < j.1 := fun i hi j hj =>
    fst_lt_of_snd_lt hP hi hj
  have PqP : ∀ q, Pq q ⊆ P := fun q p hp => hp.1
  have comp₁ : ∀ q ∈ Q, ∀ q' ∈ Q, q.1 ≠ q'.1 → Disjoint q.1 q'.1 := by
    rintro _ ⟨p, -, rfl⟩ _ ⟨p', -, rfl⟩ h
    exact (connectedComponentIn_eq_or_disjoint G₀ p.1 p'.1).resolve_left h
  have comp₂ : ∀ q ∈ Q, ∀ q' ∈ Q, q.2 ≠ q'.2 → Disjoint q.2 q'.2 := by
    rintro _ ⟨p, -, rfl⟩ _ ⟨p', -, rfl⟩ h
    exact (connectedComponentIn_eq_or_disjoint G₁ p.2 p'.2).resolve_left h
  have disj₀ : Q.PairwiseDisjoint fun q => Ioo (α q) (β q) := by
    intro q hq q' hq' hne
    by_cases h1 : q.1 = q'.1
    · have h2 : q.2 ≠ q'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact disjoint_Ioo_of_comonotone (u := Prod.fst) (v := Prod.snd) (oc₂ q hq) (oc₂ q' hq')
        (comp₂ q hq q' hq' h2) (mem₂ q) (mem₂ q')
        (fun i hi j hj => hmono₁ i (hi.elim (PqP q ·) (PqP q' ·)) j (hj.elim (PqP q ·) (PqP q' ·)))
    · exact ((comp₁ q hq q' hq' h1).mono (Ioo_csInf_csSup_subset (oc₁ q hq) (img₁ q))
        (Ioo_csInf_csSup_subset (oc₁ q' hq') (img₁ q')))
  have disj₁ : Q.PairwiseDisjoint fun q => Ioo (γ q) (δ q) := by
    intro q hq q' hq' hne
    by_cases h1 : q.2 = q'.2
    · have h2 : q.1 ≠ q'.1 := fun h2 => hne (Prod.ext h2 h1)
      exact disjoint_Ioo_of_comonotone (u := Prod.snd) (v := Prod.fst) (oc₁ q hq) (oc₁ q' hq')
        (comp₁ q hq q' hq' h2) (mem₁ q) (mem₁ q')
        (fun i hi j hj => hmono₂ i (hi.elim (PqP q ·) (PqP q' ·)) j (hj.elim (PqP q ·) (PqP q' ·)))
    · exact ((comp₂ q hq q' hq' h1).mono (Ioo_csInf_csSup_subset (oc₂ q hq) (img₂ q))
        (Ioo_csInf_csSup_subset (oc₂ q' hq') (img₂ q')))
  have U₀ : (⋃ q ∈ Q, Ioo (α q) (β q)) ⊆ G₀ :=
    iUnion₂_subset fun q hq => (Ioo_csInf_csSup_subset (oc₁ q hq) (img₁ q)).trans (sub₁ q hq)
  have U₁ : (⋃ q ∈ Q, Ioo (γ q) (δ q)) ⊆ G₁ :=
    iUnion₂_subset fun q hq => (Ioo_csInf_csSup_subset (oc₂ q hq) (img₂ q)).trans (sub₂ q hq)
  calc volume (⋃ p ∈ P, segment01 p)
      ≤ volume (⋃ q ∈ Q, closedTrapezoid (α q) (β q) (γ q) (δ q)) := measure_mono cover
    _ ≤ ∑' q : Q, volume (closedTrapezoid (α q) (β q) (γ q) (δ q)) := measure_biUnion_le _ hQ _
    _ = ∑' q : Q, (volume (Ioo (α q) (β q)) + volume (Ioo (γ q) (δ q))) * 2⁻¹ := by
        refine tsum_congr fun q => ?_
        rw [volume_closedTrapezoid_eq_add (hαβ q q.2).1 (hαβ q q.2).2, div_eq_mul_inv]
    _ = (volume (⋃ q ∈ Q, Ioo (α q) (β q)) + volume (⋃ q ∈ Q, Ioo (γ q) (δ q))) / 2 := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_add, measure_biUnion hQ disj₀
          (fun _ _ => measurableSet_Ioo), measure_biUnion hQ disj₁ (fun _ _ => measurableSet_Ioo),
          div_eq_mul_inv]
    _ ≤ (volume G₀ + volume G₁) / 2 := by gcongr

lemma preimage_biUnion_segment01_zero (P : Set (ℝ × ℝ)) :
    (fun x : ℝ => (x, (0 : ℝ))) ⁻¹' (⋃ p ∈ P, segment01 p) = Prod.fst '' P := by
  ext x
  simp [segment01, segLine, eq_comm]

lemma preimage_biUnion_segment01_one (P : Set (ℝ × ℝ)) :
    (fun x : ℝ => (x, (1 : ℝ))) ⁻¹' (⋃ p ∈ P, segment01 p) = Prod.snd '' P := by
  ext x
  simp [segment01, segLine, eq_comm]

/-- Blueprint `thm:th-thm9`, upper bound (the half used for `thm:th-thm10`):
`m_e(S) ≤ ½ (m¹_e(S ∩ X₀) + m¹_e(S ∩ X₁))` for a union `S` of pairwise disjoint segments joining
`X₀ = ℝ × {0}` to `X₁ = ℝ × {1}`. -/
theorem outerMeasure_union_segments_le (P : Set (ℝ × ℝ)) (hP : P.PairwiseDisjoint segment01) :
    volume (⋃ p ∈ P, segment01 p) ≤
      (volume ((fun x : ℝ => (x, (0 : ℝ))) ⁻¹' (⋃ p ∈ P, segment01 p)) +
        volume ((fun x : ℝ => (x, (1 : ℝ))) ⁻¹' (⋃ p ∈ P, segment01 p))) / 2 := by
  rw [preimage_biUnion_segment01_zero, preimage_biUnion_segment01_one]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
  have h0 : volume (Prod.fst '' P) < volume (Prod.fst '' P) + ε := by
    refine ENNReal.lt_add_right ?_ (by simpa using hε.ne')
    intro h; simp [h, ENNReal.top_div] at hlt
  have h1 : volume (Prod.snd '' P) < volume (Prod.snd '' P) + ε := by
    refine ENNReal.lt_add_right ?_ (by simpa using hε.ne')
    intro h; simp [h, ENNReal.top_div] at hlt
  obtain ⟨G₀, hsub₀, ho₀, hG₀⟩ := (Prod.fst '' P).exists_isOpen_lt_of_lt _ h0
  obtain ⟨G₁, hsub₁, ho₁, hG₁⟩ := (Prod.snd '' P).exists_isOpen_lt_of_lt _ h1
  calc volume (⋃ p ∈ P, segment01 p)
      ≤ (volume G₀ + volume G₁) / 2 :=
        volume_biUnion_segment01_le_of_isOpen hP ho₀ ho₁ (fun p hp => hsub₀ ⟨p, hp, rfl⟩)
          (fun p hp => hsub₁ ⟨p, hp, rfl⟩)
    _ ≤ (volume (Prod.fst '' P) + ε + (volume (Prod.snd '' P) + ε)) / 2 := by
        gcongr
    _ = (volume (Prod.fst '' P) + volume (Prod.snd '' P)) / 2 + (ε / 2 + ε / 2) := by
        simp only [div_eq_mul_inv]; ring
    _ = _ := by rw [ENNReal.add_halves]

/-! ### The lower bound -/

lemma volume_add_volume_le_of_forall {A B : Set ℝ} {c : ENNReal}
    (h : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B,
      ENNReal.ofReal (a' - a) + ENNReal.ofReal (b' - b) ≤ c)
    (hA : A.Nonempty) (hB : B.Nonempty) : volume A + volume B ≤ c := by
  rcases eq_top_or_lt_top c with rfl | hc
  · exact le_top
  have hr : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B, (a' - a) + (b' - b) ≤ c.toReal := by
    intro a ha a' ha' b hb b' hb'
    have := ENNReal.toReal_mono hc.ne (h a ha a' ha' b hb b' hb')
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal',
      ENNReal.toReal_ofReal'] at this
    linarith [le_max_left (a' - a) 0, le_max_left (b' - b) 0]
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have bA : BddAbove A := ⟨c.toReal + a₀, fun a' ha' => by linarith [hr a₀ ha₀ a' ha' b₀ hb₀ b₀ hb₀]⟩
  have bA' : BddBelow A := ⟨a₀ - c.toReal, fun a ha => by linarith [hr a ha a₀ ha₀ b₀ hb₀ b₀ hb₀]⟩
  have bB : BddAbove B := ⟨c.toReal + b₀, fun b' hb' => by linarith [hr a₀ ha₀ a₀ ha₀ b₀ hb₀ b' hb']⟩
  have bB' : BddBelow B := ⟨b₀ - c.toReal, fun b hb => by linarith [hr a₀ ha₀ a₀ ha₀ b hb b₀ hb₀]⟩
  have key : sSup A - sInf A + (sSup B - sInf B) ≤ c.toReal := by
    have s1 : ∀ a ∈ A, ∀ b ∈ B, ∀ b' ∈ B, sSup A ≤ c.toReal + a + b - b' :=
      fun a ha b hb b' hb' => csSup_le ⟨a₀, ha₀⟩ fun a' ha' => by linarith [hr a ha a' ha' b hb b' hb']
    have s2 : ∀ a ∈ A, ∀ b ∈ B, sSup B ≤ c.toReal + a + b - sSup A :=
      fun a ha b hb => csSup_le ⟨b₀, hb₀⟩ fun b' hb' => by linarith [s1 a ha b hb b' hb']
    have s3 : ∀ b ∈ B, sSup A + sSup B - c.toReal - b ≤ sInf A :=
      fun b hb => le_csInf ⟨a₀, ha₀⟩ fun a ha => by linarith [s2 a ha b hb]
    have s4 : sSup A + sSup B - c.toReal - sInf A ≤ sInf B :=
      le_csInf ⟨b₀, hb₀⟩ fun b hb => by linarith [s3 b hb]
    linarith
  calc volume A + volume B
      ≤ volume (Icc (sInf A) (sSup A)) + volume (Icc (sInf B) (sSup B)) :=
        add_le_add (measure_mono fun a ha => ⟨csInf_le bA' ha, le_csSup bA ha⟩)
          (measure_mono fun b hb => ⟨csInf_le bB' hb, le_csSup bB hb⟩)
    _ = ENNReal.ofReal (sSup A - sInf A + (sSup B - sInf B)) := by
        rw [Real.volume_Icc, Real.volume_Icc,
          ENNReal.ofReal_add (sub_nonneg.2 ((csInf_le bA' ha₀).trans (le_csSup bA ha₀)))
            (sub_nonneg.2 ((csInf_le bB' hb₀).trans (le_csSup bB hb₀)))]
    _ ≤ ENNReal.ofReal c.toReal := ENNReal.ofReal_le_ofReal key
    _ = c := ENNReal.ofReal_toReal hc.ne

lemma inf_mem_of_total {Q : Set (ℝ × ℝ)} (hQ : ∀ q ∈ Q, ∀ q' ∈ Q, q ≤ q' ∨ q' ≤ q)
    {q q' : ℝ × ℝ} (hq : q ∈ Q) (hq' : q' ∈ Q) : q ⊓ q' ∈ Q := by
  rcases hQ q hq q' hq' with h | h
  · rwa [inf_of_le_left h]
  · rwa [inf_of_le_right h]

lemma sup_mem_of_total {Q : Set (ℝ × ℝ)} (hQ : ∀ q ∈ Q, ∀ q' ∈ Q, q ≤ q' ∨ q' ≤ q)
    {q q' : ℝ × ℝ} (hq : q ∈ Q) (hq' : q' ∈ Q) : q ⊔ q' ∈ Q := by
  rcases hQ q hq q' hq' with h | h
  · rwa [sup_of_le_right h]
  · rwa [sup_of_le_left h]

/-- If `Q` is totally ordered (componentwise), then
`m¹_e(Q₁) + m¹_e(Q₂) ≤ m¹_e({q₁ + q₂ : q ∈ Q})`. -/
lemma volume_fst_add_volume_snd_le {Q : Set (ℝ × ℝ)}
    (hQ : ∀ q ∈ Q, ∀ q' ∈ Q, q ≤ q' ∨ q' ≤ q) :
    volume (Prod.fst '' Q) + volume (Prod.snd '' Q) ≤ volume ((fun q => q.1 + q.2) '' Q) := by
  rw [Set.measure_eq_iInf_isOpen ((fun q : ℝ × ℝ => q.1 + q.2) '' Q)]
  refine le_iInf fun G => le_iInf fun hZG => le_iInf fun hG => ?_
  set σ : ℝ × ℝ → ℝ := fun q => q.1 + q.2 with hσ
  have hσG : ∀ q ∈ Q, σ q ∈ G := fun q hq => hZG ⟨q, hq, rfl⟩
  set c : ℝ × ℝ → Set ℝ := fun q => connectedComponentIn G (σ q) with hc
  set C := c '' Q with hCdef
  have hC : C.Countable := (countable_components hG).mono
    (by rintro _ ⟨q, hq, rfl⟩; exact ⟨σ q, hσG q hq, rfl⟩)
  set Qc : Set ℝ → Set (ℝ × ℝ) := fun I => {q ∈ Q | c q = I} with hQc
  have cover₁ : Prod.fst '' Q ⊆ ⋃ I ∈ C, Prod.fst '' Qc I := by
    rintro _ ⟨q, hq, rfl⟩; exact mem_biUnion ⟨q, hq, rfl⟩ ⟨q, ⟨hq, rfl⟩, rfl⟩
  have cover₂ : Prod.snd '' Q ⊆ ⋃ I ∈ C, Prod.snd '' Qc I := by
    rintro _ ⟨q, hq, rfl⟩; exact mem_biUnion ⟨q, hq, rfl⟩ ⟨q, ⟨hq, rfl⟩, rfl⟩
  have disjC : C.PairwiseDisjoint fun I => I := by
    rintro _ ⟨q, -, rfl⟩ _ ⟨q', -, rfl⟩ hne
    exact (connectedComponentIn_eq_or_disjoint G (σ q) (σ q')).resolve_left hne
  have key : ∀ I ∈ C, volume (Prod.fst '' Qc I) + volume (Prod.snd '' Qc I) ≤ volume I := by
    rintro _ ⟨q₀, hq₀, rfl⟩
    have hQc : ∀ q ∈ Qc (c q₀), ∀ q' ∈ Qc (c q₀), q ≤ q' ∨ q' ≤ q :=
      fun q hq q' hq' => hQ q hq.1 q' hq'.1
    have hmemI : ∀ q ∈ Qc (c q₀), σ q ∈ c q₀ := by
      rintro q ⟨hq, hcq⟩
      rw [← hcq]; exact mem_connectedComponentIn (hσG q hq)
    refine volume_add_volume_le_of_forall ?_ ⟨q₀.1, q₀, ⟨hq₀, rfl⟩, rfl⟩
      ⟨q₀.2, q₀, ⟨hq₀, rfl⟩, rfl⟩
    rintro _ ⟨q₁, h₁, rfl⟩ _ ⟨q₃, h₃, rfl⟩ _ ⟨q₂, h₂, rfl⟩ _ ⟨q₄, h₄, rfl⟩
    set lo := q₁ ⊓ q₂ with hlo
    set hi := (q₃ ⊔ q₄) ⊔ lo with hhi
    have hlo_mem : lo ∈ Qc (c q₀) := inf_mem_of_total hQc h₁ h₂
    have hhi_mem : hi ∈ Qc (c q₀) :=
      sup_mem_of_total hQc (sup_mem_of_total hQc h₃ h₄) hlo_mem
    have l1 : lo ≤ q₁ := inf_le_left
    have l2 : lo ≤ q₂ := inf_le_right
    have l3 : q₃ ≤ hi := le_sup_left.trans le_sup_left
    have l4 : q₄ ≤ hi := le_sup_right.trans le_sup_left
    have l5 : lo ≤ hi := le_sup_right
    calc ENNReal.ofReal (q₃.1 - q₁.1) + ENNReal.ofReal (q₄.2 - q₂.2)
        ≤ ENNReal.ofReal (hi.1 - lo.1) + ENNReal.ofReal (hi.2 - lo.2) := by
          gcongr
          all_goals first | exact l1.1 | exact l3.1 | exact l2.2 | exact l4.2
      _ = ENNReal.ofReal (σ hi - σ lo) := by
          rw [← ENNReal.ofReal_add (by linarith [l5.1]) (by linarith [l5.2])]
          congr 1; simp only [hσ]; ring
      _ = volume (Icc (σ lo) (σ hi)) := (Real.volume_Icc).symm
      _ ≤ volume (c q₀) := measure_mono
          ((ordConnected_connectedComponentIn _ _).out (hmemI lo hlo_mem) (hmemI hi hhi_mem))
  calc volume (Prod.fst '' Q) + volume (Prod.snd '' Q)
      ≤ ∑' I : C, volume (Prod.fst '' Qc I) + ∑' I : C, volume (Prod.snd '' Qc I) :=
        add_le_add ((measure_mono cover₁).trans (measure_biUnion_le _ hC _))
          ((measure_mono cover₂).trans (measure_biUnion_le _ hC _))
    _ = ∑' I : C, (volume (Prod.fst '' Qc I) + volume (Prod.snd '' Qc I)) := ENNReal.tsum_add.symm
    _ ≤ ∑' I : C, volume (I : Set ℝ) := ENNReal.tsum_le_tsum fun I => key I I.2
    _ = volume (⋃ I ∈ C, I) := (measure_biUnion hC disjC fun I hI => by
          obtain ⟨q, -, rfl⟩ := hI; exact hG.connectedComponentIn.measurableSet).symm
    _ ≤ volume G := measure_mono (iUnion₂_subset fun I hI => by
          obtain ⟨q, -, rfl⟩ := hI; exact connectedComponentIn_subset _ _)

lemma total_of_pairwiseDisjoint {P : Set (ℝ × ℝ)} (hP : P.PairwiseDisjoint segment01) :
    ∀ p ∈ P, ∀ p' ∈ P, p ≤ p' ∨ p' ≤ p := by
  intro p hp p' hp'
  rcases le_total p.1 p'.1 with h | h
  · exact Or.inl ⟨h, snd_le_of_fst_le hP hp hp' h⟩
  · exact Or.inr ⟨h, snd_le_of_fst_le hP hp' hp h⟩

lemma preimage_biUnion_segment01 (P : Set (ℝ × ℝ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x : ℝ => (x, t)) ⁻¹' (⋃ p ∈ P, segment01 p) = (fun p => segLine p t) '' P := by
  ext x
  simp [segment01, ht.1, ht.2, eq_comm]

/-- The horizontal section of `S` at height `t` has outer measure at least
`(1 - t) m¹_e(S ∩ X₀) + t m¹_e(S ∩ X₁)`. -/
lemma volume_section_ge {P : Set (ℝ × ℝ)} (hP : P.PairwiseDisjoint segment01) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (1 - t) * volume (Prod.fst '' P) + ENNReal.ofReal t * volume (Prod.snd '' P) ≤
      volume ((fun p => segLine p t) '' P) := by
  set f : ℝ × ℝ → ℝ × ℝ := fun p => ((1 - t) * p.1, t * p.2) with hf
  have hQ : ∀ q ∈ f '' P, ∀ q' ∈ f '' P, q ≤ q' ∨ q' ≤ q := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
    rcases total_of_pairwiseDisjoint hP p hp p' hp' with h | h
    · exact Or.inl ⟨mul_le_mul_of_nonneg_left h.1 (sub_nonneg.2 ht.2),
        mul_le_mul_of_nonneg_left h.2 ht.1⟩
    · exact Or.inr ⟨mul_le_mul_of_nonneg_left h.1 (sub_nonneg.2 ht.2),
        mul_le_mul_of_nonneg_left h.2 ht.1⟩
  have key := volume_fst_add_volume_snd_le hQ
  have e1 : Prod.fst '' (f '' P) = (1 - t) • (Prod.fst '' P) := by
    rw [image_image, ← image_smul, image_image]; rfl
  have e2 : Prod.snd '' (f '' P) = t • (Prod.snd '' P) := by
    rw [image_image, ← image_smul, image_image]; rfl
  have e3 : (fun q : ℝ × ℝ => q.1 + q.2) '' (f '' P) = (fun p => segLine p t) '' P := by
    rw [image_image]; rfl
  rw [e1, e2, e3, Measure.addHaar_smul_of_nonneg volume (sub_nonneg.2 ht.2),
    Measure.addHaar_smul_of_nonneg volume ht.1] at key
  simpa using key

lemma lintegral_Ioo_ofReal_id : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal t = 2⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  · simp
  · exact (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · exact (ae_restrict_mem measurableSet_Ioo).mono fun t ht => ht.1.le

lemma lintegral_Ioo_ofReal_one_sub : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - t) = 2⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  · rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp
    rw [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos two_pos]; simp
  · exact ((continuous_const.sub continuous_id).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · exact (ae_restrict_mem measurableSet_Ioo).mono fun t ht => sub_nonneg.2 ht.2.le

/-- Blueprint `thm:th-thm9`, lower bound. -/
theorem le_outerMeasure_union_segments (P : Set (ℝ × ℝ)) (hP : P.PairwiseDisjoint segment01) :
    (volume ((fun x : ℝ => (x, (0 : ℝ))) ⁻¹' (⋃ p ∈ P, segment01 p)) +
        volume ((fun x : ℝ => (x, (1 : ℝ))) ⁻¹' (⋃ p ∈ P, segment01 p))) / 2 ≤
      volume (⋃ p ∈ P, segment01 p) := by
  rw [preimage_biUnion_segment01_zero, preimage_biUnion_segment01_one]
  set S := ⋃ p ∈ P, segment01 p with hS
  set m₀ := volume (Prod.fst '' P)
  set m₁ := volume (Prod.snd '' P)
  rw [← measure_toMeasurable S, Measure.volume_eq_prod,
    Measure.prod_apply_symm (measurableSet_toMeasurable _ _)]
  calc (m₀ + m₁) / 2
      = ∫⁻ t in Ioo (0 : ℝ) 1, (ENNReal.ofReal (1 - t) * m₀ + ENNReal.ofReal t * m₁) := by
        rw [lintegral_add_right _ (by fun_prop), lintegral_mul_const _ (by fun_prop),
          lintegral_mul_const _ (by fun_prop), lintegral_Ioo_ofReal_one_sub,
          lintegral_Ioo_ofReal_id, div_eq_mul_inv]
        ring
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, volume ((fun x => (x, t)) ⁻¹' toMeasurable volume S) := by
        refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
        refine (volume_section_ge hP (Ioo_subset_Icc_self ht)).trans ?_
        rw [← preimage_biUnion_segment01 P (Ioo_subset_Icc_self ht)]
        exact measure_mono (preimage_mono (subset_toMeasurable _ _))
    _ ≤ ∫⁻ t, volume ((fun x => (x, t)) ⁻¹' toMeasurable volume S) :=
        setLIntegral_le_lintegral _ _

/-- Blueprint `thm:th-thm9` (Kaczynski, dissertation, Theorem 9): if `S` is the union of a set of
pairwise disjoint closed segments, each joining a point of `X₀ = ℝ × {0}` to a point of
`X₁ = ℝ × {1}`, then `m_e(S) = ½ (m¹_e(S ∩ X₀) + m¹_e(S ∩ X₁))`. -/
theorem outerMeasure_union_segments (P : Set (ℝ × ℝ)) (hP : P.PairwiseDisjoint segment01) :
    volume (⋃ p ∈ P, segment01 p) =
      (volume ((fun x : ℝ => (x, (0 : ℝ))) ⁻¹' (⋃ p ∈ P, segment01 p)) +
        volume ((fun x : ℝ => (x, (1 : ℝ))) ⁻¹' (⋃ p ∈ P, segment01 p))) / 2 :=
  le_antisymm (outerMeasure_union_segments_le P hP) (le_outerMeasure_union_segments P hP)

/-! ### Theorem 10: disjoint arcs with null union -/

/-- `ramp k y = max 0 (min 1 (2^(k+1) y - 1))` rises from `0` at `y = 2^-(k+1)` to `1` at
`y = 2^-k`. -/
def ramp (k : ℕ) (y : ℝ) : ℝ := max 0 (min 1 (2 ^ (k + 1) * y - 1))

lemma ramp_nonneg (k : ℕ) (y : ℝ) : 0 ≤ ramp k y := le_max_left _ _

lemma ramp_le_one (k : ℕ) (y : ℝ) : ramp k y ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma continuous_ramp (k : ℕ) : Continuous (ramp k) := by
  unfold ramp; fun_prop

lemma ramp_zero (k : ℕ) : ramp k 0 = 0 := by simp [ramp]

lemma two_pow_mul_half_pow (k : ℕ) : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by
  rw [← mul_pow]; norm_num

lemma ramp_eq_zero {n k : ℕ} (hnk : n < k) {y : ℝ} (hy : y ≤ (1 / 2) ^ k) : ramp n y = 0 := by
  have h1 : (2 : ℝ) ^ (n + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hnk
  have h2 : (2 : ℝ) ^ (n + 1) * y ≤ 1 := by
    calc (2 : ℝ) ^ (n + 1) * y ≤ 2 ^ (n + 1) * (1 / 2) ^ k :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ ≤ 2 ^ k * (1 / 2) ^ k := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := two_pow_mul_half_pow k
  simp only [ramp]
  exact max_eq_left (le_trans (min_le_right _ _) (by linarith))

lemma ramp_eq_one {n k : ℕ} (hkn : k < n) {y : ℝ} (hy : (1 / 2) ^ (k + 1) ≤ y) :
    ramp n y = 1 := by
  have h1 : (2 : ℝ) ^ (k + 2) ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ≤ 2 ^ (n + 1) * y := by
    calc (2 : ℝ) = 2 ^ (k + 2) * (1 / 2) ^ (k + 1) := by
          rw [pow_succ 2 (k + 1), mul_comm _ (2 : ℝ), mul_assoc, two_pow_mul_half_pow, mul_one]
      _ ≤ 2 ^ (n + 1) * y := mul_le_mul h1 hy (by positivity) (by positivity)
  simp only [ramp]
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma ramp_eq {k : ℕ} {y : ℝ} (hy : y ∈ Icc ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2) ^ k)) :
    ramp k y = 2 ^ (k + 1) * y - 1 := by
  have e1 := two_pow_mul_half_pow (k + 1)
  have e2 : (2 : ℝ) ^ (k + 1) * (1 / 2) ^ k = 2 := by
    rw [pow_succ, mul_comm _ (2 : ℝ), mul_assoc, two_pow_mul_half_pow, mul_one]
  have h1 := mul_le_mul_of_nonneg_left hy.1 (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1))
  have h2 := mul_le_mul_of_nonneg_left hy.2 (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1))
  simp only [ramp]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

lemma exists_dyadic_mem {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    ∃ k : ℕ, y ∈ Icc ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2) ^ k) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := 1 / y) (y := (2 : ℝ))
    (by rw [le_div_iff₀ hy0]; linarith) (by norm_num)
  refine ⟨n, ?_, ?_⟩
  · rw [one_div_pow]
    rw [div_lt_iff₀ hy0] at h2
    rw [div_le_iff₀ (by positivity)]; nlinarith
  · rw [one_div_pow]
    rw [le_div_iff₀ hy0] at h1
    rw [le_div_iff₀ (by positivity)]; linarith

/-- The abscissa at height `y` of the arc at `x`: piecewise linear, through `(H (k+1) x, 2^-(k+1))`
and `(H k x, 2^-k)`, and equal to `x` at `y = 0`. -/
noncomputable def arcAbscissa (H : ℕ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x + ∑' n, (H n x - H (n + 1) x) * ramp n y

lemma convex_comb_pos {r a b : ℝ} (r0 : 0 ≤ r) (r1 : r ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 < (1 - r) * a + r * b := by
  rcases le_total r (1 / 2) with h | h
  · nlinarith [mul_le_mul_of_nonneg_right h ha.le, mul_nonneg r0 hb.le]
  · nlinarith [mul_le_mul_of_nonneg_right h hb.le, mul_nonneg (sub_nonneg.2 r1) ha.le]

section Arc

variable {H : ℕ → ℝ → ℝ} (hH : ∀ n x, |x - H n x| ≤ (1 / 2) ^ n)
include hH

lemma abs_sub_H_le (n : ℕ) (x : ℝ) : |H n x - H (n + 1) x| ≤ 2 * (1 / 2) ^ n := by
  have h1 := hH n x
  have h2 := hH (n + 1) x
  rw [pow_succ] at h2
  have : |H n x - H (n + 1) x| ≤ |x - H n x| + |x - H (n + 1) x| := by
    rw [abs_sub_comm x (H n x)]
    exact abs_sub_le _ _ _
  have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  linarith

lemma norm_arcTerm_le (x : ℝ) (n : ℕ) (y : ℝ) :
    ‖(H n x - H (n + 1) x) * ramp n y‖ ≤ 2 * (1 / 2) ^ n := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ramp_nonneg n y)]
  calc |H n x - H (n + 1) x| * ramp n y ≤ |H n x - H (n + 1) x| * 1 :=
        mul_le_mul_of_nonneg_left (ramp_le_one n y) (abs_nonneg _)
    _ ≤ 2 * (1 / 2) ^ n := by rw [mul_one]; exact abs_sub_H_le hH n x

lemma summable_arcTerm (x y : ℝ) : Summable fun n => (H n x - H (n + 1) x) * ramp n y :=
  Summable.of_norm_bounded (summable_geometric_two.mul_left 2) (norm_arcTerm_le hH x · y)

lemma continuous_arcAbscissa (x : ℝ) : Continuous (arcAbscissa H x) :=
  continuous_const.add (continuous_tsum
    (fun n => continuous_const.mul (continuous_ramp n))
    (summable_geometric_two.mul_left 2) (fun n y => norm_arcTerm_le hH x n y))

omit hH in
lemma arcAbscissa_zero (x : ℝ) : arcAbscissa H x 0 = x := by
  simp [arcAbscissa, ramp_zero]

lemma tendsto_H (x : ℝ) : Tendsto (fun n => H n x) atTop (𝓝 x) := by
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
  rw [Real.norm_eq_abs, abs_sub_comm]; exact hH n x

lemma arcAbscissa_eq {k : ℕ} {x y : ℝ} (hy : y ∈ Icc ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2) ^ k)) :
    arcAbscissa H x y = (1 - ramp k y) * H (k + 1) x + ramp k y * H k x := by
  set f : ℕ → ℝ := fun n => (H n x - H (n + 1) x) * ramp n y with hf
  have hpart : ∀ N, k + 1 ≤ N →
      ∑ n ∈ Finset.range N, f n = (H k x - H (k + 1) x) * ramp k y + H (k + 1) x - H N x := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [Finset.sum_range_succ, Finset.sum_eq_zero fun n hn => ?_]
      · simp [hf]
      · simp only [hf, ramp_eq_zero (Finset.mem_range.1 hn) hy.2, mul_zero]
    | succ N hN ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [hf, ramp_eq_one (n := N) (k := k) (by omega) hy.1, mul_one]
      ring
  have ht : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop
      (𝓝 ((H k x - H (k + 1) x) * ramp k y + H (k + 1) x - x)) := by
    refine Tendsto.congr' (f₁ := fun N => (H k x - H (k + 1) x) * ramp k y + H (k + 1) x - H N x)
      ?_ (tendsto_const_nhds.sub (tendsto_H hH x))
    filter_upwards [eventually_ge_atTop (k + 1)] with N hN using (hpart N hN).symm
  have hs := (summable_arcTerm hH x y).hasSum.tendsto_sum_nat
  rw [arcAbscissa, ← hf, tendsto_nhds_unique hs ht]
  ring

lemma arcAbscissa_strictMono {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hm : ∀ n, StrictMono (H n)) :
    StrictMono fun x => arcAbscissa H x y := by
  intro x x' hxx
  rcases eq_or_lt_of_le hy.1 with rfl | hy0
  · simpa [arcAbscissa_zero] using hxx
  obtain ⟨k, hk⟩ := exists_dyadic_mem hy0 hy.2
  simp only [arcAbscissa_eq hH hk]
  have a1 := hm (k + 1) hxx
  have a2 := hm k hxx
  have := convex_comb_pos (ramp_nonneg k y) (ramp_le_one k y) (sub_pos.2 a1) (sub_pos.2 a2)
  linarith

end Arc

lemma segment01_disjoint {p p' : ℝ × ℝ} (h₁ : p.1 < p'.1) (h₂ : p.2 < p'.2) :
    Disjoint (segment01 p) (segment01 p') := by
  rw [Set.disjoint_left]
  rintro z ⟨hy, hz⟩ ⟨-, hz'⟩
  rw [hz] at hz'
  simp only [segLine] at hz'
  have := convex_comb_pos hy.1 hy.2 (sub_pos.2 h₁) (sub_pos.2 h₂)
  linarith

lemma volume_realAxis : volume {z : ℂ | z.im = 0} = 0 := by
  have : {z : ℂ | z.im = 0} = Complex.measurableEquivRealProd ⁻¹' (univ ×ˢ ({0} : Set ℝ)) := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [this, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Blueprint `thm:th-thm10` (Kaczynski, dissertation, Theorem 10): there are pairwise disjoint
arcs `γ x` at the points `x` of the real axis, lying in the upper half-plane except for `x`, whose
union has planar measure zero. Same statement as `TJK.Discont.exists_disjoint_null_arcs`. -/
theorem exists_disjoint_null_arcs' :
    ∃ γ : ℝ → Set ℂ, (∀ x : ℝ, IsArcAt upper (x : ℂ) (γ x)) ∧
      Pairwise (fun x y => Disjoint (γ x) (γ y)) ∧ volume (⋃ x, γ x) = 0 := by
  choose H hHm hHnull hH using fun n : ℕ =>
    exists_strictMono_null_range (ε := (1 / 2 : ℝ) ^ n) (by positivity)
  -- the arc at `x`, parametrized by the height
  let pt : ℝ → ℝ → ℂ := fun x y => (arcAbscissa H x y : ℂ) + (y : ℂ) * Complex.I
  have pt_re : ∀ x y, (pt x y).re = arcAbscissa H x y := fun x y => by simp [pt]
  have pt_im : ∀ x y, (pt x y).im = y := fun x y => by simp [pt]
  have pt_cont : ∀ x, Continuous (pt x) := fun x => by
    have := continuous_arcAbscissa hH x
    simp only [pt]; fun_prop
  let path : ∀ x : ℝ, Path (x : ℂ) (pt x 1) := fun x =>
    { toFun := fun y => pt x y
      continuous_toFun := (pt_cont x).comp continuous_subtype_val
      source' := by simp [pt, arcAbscissa_zero]
      target' := rfl }
  refine ⟨fun x => range (path x), fun x => ⟨pt x 1, ⟨path x, ?_, rfl⟩, ?_⟩, ?_, ?_⟩
  · intro y y' h
    have := congrArg Complex.im h
    simp only [path, Path.coe_mk_mk, pt_im] at this
    exact Subtype.ext this
  · rintro _ ⟨⟨⟨y, y0, y1⟩, rfl⟩, hne⟩
    simp only [mem_singleton_iff] at hne
    show 0 < (pt x y).im
    rw [pt_im]
    rcases eq_or_lt_of_le y0 with rfl | h
    · exact (hne (by simp [path, pt, arcAbscissa_zero])).elim
    · exact h
  · intro x x' hne
    rw [Set.disjoint_left]
    rintro _ ⟨⟨y, hy⟩, rfl⟩ ⟨⟨y', hy'⟩, he⟩
    simp only [path, Path.coe_mk_mk] at he
    have him := congrArg Complex.im he
    rw [pt_im, pt_im] at him
    subst him
    have hre := congrArg Complex.re he
    rw [pt_re, pt_re] at hre
    exact hne ((arcAbscissa_strictMono hH hy hHm).injective hre.symm)
  · -- the null cover
    let P : ℕ → Set (ℝ × ℝ) := fun k => range fun x => (H (k + 1) x, H k x)
    have hPd : ∀ k, (P k).PairwiseDisjoint segment01 := by
      rintro k _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ hne
      rcases lt_trichotomy x x' with h | rfl | h
      · exact segment01_disjoint (hHm _ h) (hHm _ h)
      · exact absurd rfl hne
      · exact (segment01_disjoint (hHm _ h) (hHm _ h)).symm
    have hPnull : ∀ k, volume (⋃ p ∈ P k, segment01 p) = 0 := by
      intro k
      refine le_antisymm ((outerMeasure_union_segments_le _ (hPd k)).trans (le_of_eq ?_)) bot_le
      rw [preimage_biUnion_segment01_zero, preimage_biUnion_segment01_one,
        measure_mono_null (?_ : Prod.fst '' P k ⊆ range (H (k + 1))) (hHnull (k + 1)),
        measure_mono_null (?_ : Prod.snd '' P k ⊆ range (H k)) (hHnull k)]
      · simp
      · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
      · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
    let B : ℕ → ℂ → ℂ := fun k w =>
      (w.re : ℂ) + (((1 + w.im) / 2 ^ (k + 1) : ℝ) : ℂ) * Complex.I
    let T : ℕ → Set ℂ := fun k => Complex.measurableEquivRealProd ⁻¹' (⋃ p ∈ P k, segment01 p)
    have hT : ∀ k, volume (B k '' T k) = 0 := fun k =>
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
        (by simp only [B]; fun_prop)
        ((Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv _).trans (hPnull k))
    refine measure_mono_null (?_ : _ ⊆ {z : ℂ | z.im = 0} ∪ ⋃ k, B k '' T k)
      (measure_union_null volume_realAxis (measure_iUnion_null hT))
    rintro _ ⟨_, ⟨x, rfl⟩, ⟨⟨y, ⟨y0, y1⟩⟩, rfl⟩⟩
    simp only [path, Path.coe_mk_mk]
    rcases eq_or_lt_of_le y0 with rfl | hy0
    · left; simp [pt]
    right
    obtain ⟨k, hk⟩ := exists_dyadic_mem hy0 y1
    set s := ramp k y with hs
    have hs' : s = 2 ^ (k + 1) * y - 1 := ramp_eq hk
    set p : ℝ × ℝ := (H (k + 1) x, H k x) with hp
    refine mem_iUnion.2 ⟨k, Complex.measurableEquivRealProd.symm (segLine p s, s), ?_, ?_⟩
    · show Complex.measurableEquivRealProd (Complex.measurableEquivRealProd.symm (segLine p s, s)) ∈
        ⋃ q ∈ P k, segment01 q
      rw [MeasurableEquiv.apply_symm_apply]
      exact mem_biUnion (x := p) ⟨x, rfl⟩ ⟨⟨ramp_nonneg k y, ramp_le_one k y⟩, rfl⟩
    · apply Complex.ext
      · simp only [B, pt, Complex.measurableEquivRealProd_symm_apply, Complex.add_re,
          Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
          mul_zero, mul_one, sub_self, add_zero]
        rw [arcAbscissa_eq hH hk]
        simp [segLine, hp, hs]
      · simp only [B, pt, Complex.measurableEquivRealProd_symm_apply, Complex.add_im,
          Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
          mul_zero, mul_one, zero_add, add_zero]
        rw [hs']
        field_simp
        ring

/-! ### The trapezoids `T(s, s')` and Lemma 23 -/

/-- `T(s, s')` for segments `s = segment01 p`, `s' = segment01 p'`: the points of the strip whose
abscissa lies between those of the two segments. For disjoint segments with `p ≤ p'` it is
`closedTrapezoid p.1 p'.1 p.2 p'.2`, and `segTrap p p = segment01 p`. -/
def segTrap (p p' : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Icc (0 : ℝ) 1 ∧ z.1 ∈ uIcc (segLine p z.2) (segLine p' z.2)}

lemma segTrap_self (p : ℝ × ℝ) : segTrap p p = segment01 p := by
  ext z; simp [segTrap, segment01]

lemma segTrap_comm (p p' : ℝ × ℝ) : segTrap p p' = segTrap p' p := by
  ext z; simp [segTrap, uIcc_comm]

lemma segTrap_eq_closedTrapezoid {p p' : ℝ × ℝ} (h : p ≤ p') :
    segTrap p p' = closedTrapezoid p.1 p'.1 p.2 p'.2 := by
  ext z
  simp only [segTrap, closedTrapezoid, mem_ofPred_eq]
  refine and_congr_right fun hy => ?_
  have : segLine p z.2 ≤ segLine p' z.2 := by
    simp only [segLine]
    have := mul_le_mul_of_nonneg_left h.1 (sub_nonneg.2 hy.2)
    have := mul_le_mul_of_nonneg_left h.2 hy.1
    linarith
  rw [uIcc_of_le this, mem_Icc]

lemma strict_of_disjoint {p p' : ℝ × ℝ} (h : Disjoint (segment01 p) (segment01 p')) :
    (p.1 < p'.1 ∧ p.2 < p'.2) ∨ (p'.1 < p.1 ∧ p'.2 < p.2) := by
  rcases lt_or_ge p.1 p'.1 with h1 | h1
  · rcases lt_or_ge p.2 p'.2 with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd h (Set.not_disjoint_iff_nonempty_inter.2 (segment01_inter_nonempty h1.le h2))
  · rcases lt_or_ge p'.2 p.2 with h2 | h2
    · rcases eq_or_lt_of_le h1 with e | h1'
      · exact absurd h (Set.not_disjoint_iff_nonempty_inter.2
          (segment01_inter_nonempty (p := p) (p' := p') e.ge h2.le))
      · exact Or.inr ⟨h1', h2⟩
    · exact absurd h.symm (Set.not_disjoint_iff_nonempty_inter.2 (segment01_inter_nonempty h1 h2))

lemma segLine_lt_iff {p p' : ℝ × ℝ} (h : p = p' ∨ Disjoint (segment01 p) (segment01 p'))
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    segLine p y < segLine p' y ↔ p.1 < p'.1 ∧ p.2 < p'.2 := by
  have key : ∀ {q q' : ℝ × ℝ}, q.1 < q'.1 → q.2 < q'.2 → segLine q y < segLine q' y := by
    intro q q' h1 h2
    have := convex_comb_pos hy.1 hy.2 (sub_pos.2 h1) (sub_pos.2 h2)
    simp only [segLine]; linarith
  refine ⟨fun hlt => ?_, fun h' => key h'.1 h'.2⟩
  rcases h with rfl | h
  · exact absurd hlt (lt_irrefl _)
  · rcases strict_of_disjoint h with h' | h'
    · exact h'
    · exact absurd (key h'.1 h'.2) (not_lt.2 hlt.le)

lemma segLine_le_iff_of {p p' : ℝ × ℝ} (h : p = p' ∨ Disjoint (segment01 p) (segment01 p'))
    {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) :
    segLine p y ≤ segLine p' y ↔ segLine p y' ≤ segLine p' y' := by
  have h' : p' = p ∨ Disjoint (segment01 p') (segment01 p) := h.imp Eq.symm fun hd => hd.symm
  rw [← not_lt, ← not_lt, segLine_lt_iff h' hy, segLine_lt_iff h' hy']

lemma uIcc_inter_nonempty_iff (a b c d : ℝ) :
    (uIcc a b ∩ uIcc c d).Nonempty ↔
      (a ≤ c ∨ a ≤ d ∨ b ≤ c ∨ b ≤ d) ∧ (c ≤ a ∨ c ≤ b ∨ d ≤ a ∨ d ≤ b) := by
  rw [uIcc, uIcc, Icc_inter_Icc, nonempty_Icc]
  simp only [sup_le_iff, le_inf_iff, inf_le_iff, le_sup_iff, le_refl, true_or, or_true, and_true,
    true_and]
  tauto

lemma uIcc_subset_union_of_inter {a b c d : ℝ} (h : (uIcc a b ∩ uIcc c d).Nonempty) :
    uIcc a c ⊆ uIcc a b ∪ uIcc c d := by
  obtain ⟨w, hw₁, hw₂⟩ := h
  refine (uIcc_subset_uIcc_union_uIcc (b := w)).trans (union_subset_union ?_ ?_)
  · exact uIcc_subset_uIcc left_mem_uIcc hw₁
  · exact uIcc_subset_uIcc hw₂ left_mem_uIcc

/-- Blueprint `lem:th-lemma23` (Kaczynski, dissertation, Lemma 23). -/
theorem segTrap_subset_union {p₁ p₂ p₃ p₄ : ℝ × ℝ}
    (h : ({p₁, p₂, p₃, p₄} : Set (ℝ × ℝ)).PairwiseDisjoint segment01)
    (hne : (segTrap p₁ p₂ ∩ segTrap p₃ p₄).Nonempty) :
    segTrap p₁ p₃ ⊆ segTrap p₁ p₂ ∪ segTrap p₃ p₄ := by
  have hp : ∀ {q q'}, q ∈ ({p₁, p₂, p₃, p₄} : Set (ℝ × ℝ)) →
      q' ∈ ({p₁, p₂, p₃, p₄} : Set (ℝ × ℝ)) → q = q' ∨ Disjoint (segment01 q) (segment01 q') := by
    intro q q' hq hq'
    by_cases e : q = q'
    · exact Or.inl e
    · exact Or.inr (h hq hq' e)
  have m1 : p₁ ∈ ({p₁, p₂, p₃, p₄} : Set (ℝ × ℝ)) := by simp
  have m2 : p₂ ∈ ({p₁, p₂, p₃, p₄} : Set (ℝ × ℝ)) := by simp
  have m3 : p₃ ∈ ({p₁, p₂, p₃, p₄} : Set (ℝ × ℝ)) := by simp
  have m4 : p₄ ∈ ({p₁, p₂, p₃, p₄} : Set (ℝ × ℝ)) := by simp
  obtain ⟨⟨x₀, y₀⟩, ⟨hy₀, hx₁⟩, ⟨-, hx₂⟩⟩ := hne
  have hmeet₀ : (uIcc (segLine p₁ y₀) (segLine p₂ y₀) ∩ uIcc (segLine p₃ y₀) (segLine p₄ y₀)).Nonempty :=
    ⟨x₀, hx₁, hx₂⟩
  rintro ⟨x, y⟩ ⟨hy, hx⟩
  have hmeet : (uIcc (segLine p₁ y) (segLine p₂ y) ∩ uIcc (segLine p₃ y) (segLine p₄ y)).Nonempty := by
    rw [uIcc_inter_nonempty_iff] at hmeet₀ ⊢
    rwa [segLine_le_iff_of (hp m1 m3) hy hy₀, segLine_le_iff_of (hp m1 m4) hy hy₀,
      segLine_le_iff_of (hp m2 m3) hy hy₀, segLine_le_iff_of (hp m2 m4) hy hy₀,
      segLine_le_iff_of (hp m3 m1) hy hy₀, segLine_le_iff_of (hp m3 m2) hy hy₀,
      segLine_le_iff_of (hp m4 m1) hy hy₀, segLine_le_iff_of (hp m4 m2) hy hy₀]
  rcases uIcc_subset_union_of_inter hmeet hx with h' | h'
  · exact Or.inl ⟨hy, h'⟩
  · exact Or.inr ⟨hy, h'⟩

/-! ### Trapezoids with possibly infinite parameters and Lemma 24 -/

/-- `(1 - y) a + y b` for `a b : EReal` (with `0 · (±∞) = 0`). -/
noncomputable def eLine (a b : EReal) (y : ℝ) : EReal := ((1 - y : ℝ) : EReal) * a + (y : EReal) * b

/-- The closed trapezoid `T(a₀, b₀; a₁, b₁)` with parameters in `[-∞, +∞]`
(blueprint `def:trapezoid`). -/
def closedTrapezoidE (a₀ b₀ a₁ b₁ : EReal) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Icc (0 : ℝ) 1 ∧ eLine a₀ a₁ z.2 ≤ z.1 ∧ (z.1 : EReal) ≤ eLine b₀ b₁ z.2}

/-- The interior `T°` of `T(a₀, b₀; a₁, b₁)` relative to the strip `0 ≤ y ≤ 1`. -/
def openTrapezoidE (a₀ b₀ a₁ b₁ : EReal) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Icc (0 : ℝ) 1 ∧ eLine a₀ a₁ z.2 < z.1 ∧ (z.1 : EReal) < eLine b₀ b₁ z.2}

/-- `S` is a trapezoid (blueprint `def:trapezoid`): `S = ∅`, or `T° ⊆ S ⊆ T` for a closed trapezoid
`T = T(a₀, b₀; a₁, b₁)` with `a₀ ≤ b₀`, `a₁ ≤ b₁`, `aᵢ < +∞`, `bᵢ > -∞`. -/
def IsTrapezoid (S : Set (ℝ × ℝ)) : Prop :=
  S = ∅ ∨ ∃ a₀ b₀ a₁ b₁ : EReal, a₀ ≤ b₀ ∧ a₁ ≤ b₁ ∧ a₀ ≠ ⊤ ∧ a₁ ≠ ⊤ ∧ b₀ ≠ ⊥ ∧ b₁ ≠ ⊥ ∧
    openTrapezoidE a₀ b₀ a₁ b₁ ⊆ S ∧ S ⊆ closedTrapezoidE a₀ b₀ a₁ b₁

lemma eLine_coe (r₀ r₁ y : ℝ) : eLine r₀ r₁ y = (segLine (r₀, r₁) y : EReal) := by
  simp only [eLine, segLine]; norm_cast

lemma closedTrapezoidE_coe (a₀ b₀ a₁ b₁ : ℝ) :
    closedTrapezoidE a₀ b₀ a₁ b₁ = closedTrapezoid a₀ b₀ a₁ b₁ := by
  ext z; simp [closedTrapezoidE, closedTrapezoid, eLine_coe]

lemma eLine_le_coe {a₀ a₁ : EReal} {r₀ r₁ y : ℝ} (h₀ : a₀ ≤ r₀) (h₁ : a₁ ≤ r₁)
    (hy : y ∈ Icc (0 : ℝ) 1) : eLine a₀ a₁ y ≤ (segLine (r₀, r₁) y : EReal) := by
  rw [← eLine_coe]
  exact add_le_add (mul_le_mul_of_nonneg_left h₀ (by exact_mod_cast sub_nonneg.2 hy.2))
    (mul_le_mul_of_nonneg_left h₁ (by exact_mod_cast hy.1))

lemma coe_le_eLine {b₀ b₁ : EReal} {r₀ r₁ y : ℝ} (h₀ : (r₀ : EReal) ≤ b₀) (h₁ : (r₁ : EReal) ≤ b₁)
    (hy : y ∈ Icc (0 : ℝ) 1) : (segLine (r₀, r₁) y : EReal) ≤ eLine b₀ b₁ y := by
  rw [← eLine_coe]
  exact add_le_add (mul_le_mul_of_nonneg_left h₀ (by exact_mod_cast sub_nonneg.2 hy.2))
    (mul_le_mul_of_nonneg_left h₁ (by exact_mod_cast hy.1))

lemma exists_lt_of_eLine_lt {P : Set (ℝ × ℝ)} (hP : P.Nonempty) {x y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1)
    (h : eLine (⨅ p ∈ P, (p.1 : EReal)) (⨅ p ∈ P, (p.2 : EReal)) y < x) :
    ∃ q₁ ∈ P, ∃ q₂ ∈ P, (1 - y) * q₁.1 + y * q₂.2 < x := by
  set A₀ := ⨅ p ∈ P, (p.1 : EReal) with hA₀
  set A₁ := ⨅ p ∈ P, (p.2 : EReal) with hA₁
  obtain ⟨p, hp⟩ := hP
  have ex₀ : ∀ r : ℝ, A₀ < r → ∃ q ∈ P, q.1 < r := fun r hr => by
    obtain ⟨q, hr⟩ := iInf_lt_iff.1 hr
    obtain ⟨hq, hr⟩ := iInf_lt_iff.1 hr
    exact ⟨q, hq, EReal.coe_lt_coe_iff.1 hr⟩
  have ex₁ : ∀ r : ℝ, A₁ < r → ∃ q ∈ P, q.2 < r := fun r hr => by
    obtain ⟨q, hr⟩ := iInf_lt_iff.1 hr
    obtain ⟨hq, hr⟩ := iInf_lt_iff.1 hr
    exact ⟨q, hq, EReal.coe_lt_coe_iff.1 hr⟩
  have le₀ : A₀ ≤ p.1 := biInf_le (fun q => (q.1 : EReal)) hp
  have le₁ : A₁ ≤ p.2 := biInf_le (fun q => (q.2 : EReal)) hp
  rcases eq_or_ne A₀ ⊥ with h₀ | h₀
  · rcases eq_or_lt_of_le hy.2 with rfl | hy1
    · -- `y = 1`
      have : A₁ < x := by simpa [eLine] using h
      obtain ⟨q, hq, hlt⟩ := ex₁ x this
      exact ⟨q, hq, q, hq, by simpa using hlt⟩
    · have hc : 0 < 1 - y := sub_pos.2 hy1
      obtain ⟨q, hq, hlt⟩ := ex₀ ((x - y * p.2) / (1 - y)) (by rw [h₀]; exact EReal.bot_lt_coe _)
      refine ⟨q, hq, p, hp, ?_⟩
      rw [lt_div_iff₀ hc] at hlt
      linarith
  rcases eq_or_ne A₁ ⊥ with h₁ | h₁
  · rcases eq_or_lt_of_le hy.1 with rfl | hy0
    · -- `y = 0`
      have : A₀ < x := by simpa [eLine] using h
      obtain ⟨q, hq, hlt⟩ := ex₀ x this
      exact ⟨q, hq, q, hq, by simpa using hlt⟩
    · obtain ⟨q, hq, hlt⟩ := ex₁ ((x - (1 - y) * p.1) / y) (by rw [h₁]; exact EReal.bot_lt_coe _)
      refine ⟨p, hp, q, hq, ?_⟩
      rw [lt_div_iff₀ hy0] at hlt
      linarith
  -- both parameters are finite
  have t₀ : A₀ ≠ ⊤ := (le₀.trans_lt (EReal.coe_lt_top _)).ne
  have t₁ : A₁ ≠ ⊤ := (le₁.trans_lt (EReal.coe_lt_top _)).ne
  set a := A₀.toReal
  set b := A₁.toReal
  have ea : A₀ = a := (EReal.coe_toReal t₀ h₀).symm
  have eb : A₁ = b := (EReal.coe_toReal t₁ h₁).symm
  rw [ea, eb, eLine_coe, EReal.coe_lt_coe_iff] at h
  simp only [segLine] at h
  set δ := (x - ((1 - y) * a + y * b)) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨q₁, hq₁, l₁⟩ := ex₀ (a + δ) (by rw [ea]; exact_mod_cast (by linarith : a < a + δ))
  obtain ⟨q₂, hq₂, l₂⟩ := ex₁ (b + δ) (by rw [eb]; exact_mod_cast (by linarith : b < b + δ))
  refine ⟨q₁, hq₁, q₂, hq₂, ?_⟩
  have m₁ := mul_le_mul_of_nonneg_left l₁.le (sub_nonneg.2 hy.2)
  have m₂ := mul_le_mul_of_nonneg_left l₂.le hy.1
  nlinarith

lemma exists_gt_of_lt_eLine {P : Set (ℝ × ℝ)} (hP : P.Nonempty) {x y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1)
    (h : (x : EReal) < eLine (⨆ p ∈ P, (p.1 : EReal)) (⨆ p ∈ P, (p.2 : EReal)) y) :
    ∃ q₁ ∈ P, ∃ q₂ ∈ P, x < (1 - y) * q₁.1 + y * q₂.2 := by
  set B₀ := ⨆ p ∈ P, (p.1 : EReal) with hB₀
  set B₁ := ⨆ p ∈ P, (p.2 : EReal) with hB₁
  obtain ⟨p, hp⟩ := hP
  have ex₀ : ∀ r : ℝ, (r : EReal) < B₀ → ∃ q ∈ P, r < q.1 := fun r hr => by
    obtain ⟨q, hr⟩ := lt_iSup_iff.1 hr
    obtain ⟨hq, hr⟩ := lt_iSup_iff.1 hr
    exact ⟨q, hq, EReal.coe_lt_coe_iff.1 hr⟩
  have ex₁ : ∀ r : ℝ, (r : EReal) < B₁ → ∃ q ∈ P, r < q.2 := fun r hr => by
    obtain ⟨q, hr⟩ := lt_iSup_iff.1 hr
    obtain ⟨hq, hr⟩ := lt_iSup_iff.1 hr
    exact ⟨q, hq, EReal.coe_lt_coe_iff.1 hr⟩
  have le₀ : (p.1 : EReal) ≤ B₀ := le_biSup (fun q => (q.1 : EReal)) hp
  have le₁ : (p.2 : EReal) ≤ B₁ := le_biSup (fun q => (q.2 : EReal)) hp
  rcases eq_or_ne B₀ ⊤ with h₀ | h₀
  · rcases eq_or_lt_of_le hy.2 with rfl | hy1
    · have : (x : EReal) < B₁ := by simpa [eLine] using h
      obtain ⟨q, hq, hlt⟩ := ex₁ x this
      exact ⟨q, hq, q, hq, by simpa using hlt⟩
    · have hc : 0 < 1 - y := sub_pos.2 hy1
      obtain ⟨q, hq, hlt⟩ := ex₀ ((x - y * p.2) / (1 - y)) (by rw [h₀]; exact EReal.coe_lt_top _)
      refine ⟨q, hq, p, hp, ?_⟩
      rw [div_lt_iff₀ hc] at hlt
      linarith
  rcases eq_or_ne B₁ ⊤ with h₁ | h₁
  · rcases eq_or_lt_of_le hy.1 with rfl | hy0
    · have : (x : EReal) < B₀ := by simpa [eLine] using h
      obtain ⟨q, hq, hlt⟩ := ex₀ x this
      exact ⟨q, hq, q, hq, by simpa using hlt⟩
    · obtain ⟨q, hq, hlt⟩ := ex₁ ((x - (1 - y) * p.1) / y) (by rw [h₁]; exact EReal.coe_lt_top _)
      refine ⟨p, hp, q, hq, ?_⟩
      rw [div_lt_iff₀ hy0] at hlt
      linarith
  have t₀ : B₀ ≠ ⊥ := ((EReal.bot_lt_coe _).trans_le le₀).ne'
  have t₁ : B₁ ≠ ⊥ := ((EReal.bot_lt_coe _).trans_le le₁).ne'
  set a := B₀.toReal
  set b := B₁.toReal
  have ea : B₀ = a := (EReal.coe_toReal h₀ t₀).symm
  have eb : B₁ = b := (EReal.coe_toReal h₁ t₁).symm
  rw [ea, eb, eLine_coe, EReal.coe_lt_coe_iff] at h
  simp only [segLine] at h
  set δ := (((1 - y) * a + y * b) - x) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨q₁, hq₁, l₁⟩ := ex₀ (a - δ) (by rw [ea]; exact_mod_cast (by linarith : a - δ < a))
  obtain ⟨q₂, hq₂, l₂⟩ := ex₁ (b - δ) (by rw [eb]; exact_mod_cast (by linarith : b - δ < b))
  refine ⟨q₁, hq₁, q₂, hq₂, ?_⟩
  have m₁ := mul_le_mul_of_nonneg_left l₁.le (sub_nonneg.2 hy.2)
  have m₂ := mul_le_mul_of_nonneg_left l₂.le hy.1
  nlinarith

lemma segLine_mono {q q' : ℝ × ℝ} (h : q ≤ q') {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    segLine q y ≤ segLine q' y := by
  simp only [segLine]
  have := mul_le_mul_of_nonneg_left h.1 (sub_nonneg.2 hy.2)
  have := mul_le_mul_of_nonneg_left h.2 hy.1
  linarith

/-- Blueprint `lem:th-lemma24` (Kaczynski, dissertation, Lemma 24): for a set of pairwise disjoint
segments, `⋃_{s, s' ∈ Σ} T(s, s')` is a trapezoid. -/
theorem isTrapezoid_biUnion {P : Set (ℝ × ℝ)} (hP : P.PairwiseDisjoint segment01) :
    IsTrapezoid (⋃ p ∈ P, ⋃ p' ∈ P, segTrap p p') := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · left; simp
  right
  have htot := total_of_pairwiseDisjoint hP
  obtain ⟨p, hp⟩ := hne
  refine ⟨⨅ p ∈ P, (p.1 : EReal), ⨆ p ∈ P, (p.1 : EReal), ⨅ p ∈ P, (p.2 : EReal),
    ⨆ p ∈ P, (p.2 : EReal), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (biInf_le (fun q => (q.1 : EReal)) hp).trans (le_biSup (fun q => (q.1 : EReal)) hp)
  · exact (biInf_le (fun q => (q.2 : EReal)) hp).trans (le_biSup (fun q => (q.2 : EReal)) hp)
  · exact ((biInf_le (fun q => (q.1 : EReal)) hp).trans_lt (EReal.coe_lt_top _)).ne
  · exact ((biInf_le (fun q => (q.2 : EReal)) hp).trans_lt (EReal.coe_lt_top _)).ne
  · exact ((EReal.bot_lt_coe _).trans_le (le_biSup (fun q => (q.1 : EReal)) hp)).ne'
  · exact ((EReal.bot_lt_coe _).trans_le (le_biSup (fun q => (q.2 : EReal)) hp)).ne'
  · rintro ⟨x, y⟩ ⟨hy, hlo, hhi⟩
    obtain ⟨q₁, hq₁, q₂, hq₂, hlt⟩ := exists_lt_of_eLine_lt ⟨p, hp⟩ hy hlo
    obtain ⟨q₃, hq₃, q₄, hq₄, hgt⟩ := exists_gt_of_lt_eLine ⟨p, hp⟩ hy hhi
    have hlo' : segLine (q₁ ⊓ q₂) y < x := by
      have h1 := mul_le_mul_of_nonneg_left (inf_le_left : q₁ ⊓ q₂ ≤ q₁).1 (sub_nonneg.2 hy.2)
      have h2 := mul_le_mul_of_nonneg_left (inf_le_right : q₁ ⊓ q₂ ≤ q₂).2 hy.1
      simp only [segLine]; linarith
    have hhi' : x < segLine (q₃ ⊔ q₄) y := by
      have h1 := mul_le_mul_of_nonneg_left (le_sup_left : q₃ ≤ q₃ ⊔ q₄).1 (sub_nonneg.2 hy.2)
      have h2 := mul_le_mul_of_nonneg_left (le_sup_right : q₄ ≤ q₃ ⊔ q₄).2 hy.1
      simp only [segLine]; linarith
    exact mem_iUnion₂.2 ⟨_, inf_mem_of_total htot hq₁ hq₂, mem_iUnion₂.2
      ⟨_, sup_mem_of_total htot hq₃ hq₄, hy, mem_uIcc.2 (Or.inl ⟨hlo'.le, hhi'.le⟩)⟩⟩
  · simp only [iUnion_subset_iff]
    rintro q hq q' hq' ⟨x, y⟩ ⟨hy, hx⟩
    have lo : ∀ r ∈ P, eLine (⨅ p ∈ P, (p.1 : EReal)) (⨅ p ∈ P, (p.2 : EReal)) y ≤
        (segLine r y : EReal) := fun r hr =>
      eLine_le_coe (biInf_le (fun q => (q.1 : EReal)) hr) (biInf_le (fun q => (q.2 : EReal)) hr) hy
    have hi : ∀ r ∈ P, (segLine r y : EReal) ≤
        eLine (⨆ p ∈ P, (p.1 : EReal)) (⨆ p ∈ P, (p.2 : EReal)) y := fun r hr =>
      coe_le_eLine (le_biSup (fun q => (q.1 : EReal)) hr) (le_biSup (fun q => (q.2 : EReal)) hr) hy
    refine ⟨hy, ?_, ?_⟩
    · rcases mem_uIcc.1 hx with h | h
      · exact (lo q hq).trans (EReal.coe_le_coe_iff.2 h.1)
      · exact (lo q' hq').trans (EReal.coe_le_coe_iff.2 h.1)
    · rcases mem_uIcc.1 hx with h | h
      · exact (EReal.coe_le_coe_iff.2 h.2).trans (hi q' hq')
      · exact (EReal.coe_le_coe_iff.2 h.2).trans (hi q hq)

end TJK.Discont
