/-
Copyright: the TJK formalization project.

Section G of the blueprint (`paper/sections/G-discont.tex`), subsection "Baire functions":
`def:meets-in`, `lem:figure5`, `thm:baire-plus-one` (dissertation Theorem 8, 1965 paper Theorem 4)
and `cor:borel`.
-/
import Mathlib
import TJK.Defs
import TJK.Plane.Basic
import TJK.Plane.Crosscut
import TJK.Baire.Basic
import TJK.Baire.Higher
import TJK.Baire.Banach

open _root_.Set Filter Topology Metric Complex

namespace TJK.Discont

theorem pathRange_isPathConnected {a b : ℂ} (q : Path a b) : IsPathConnected (range q) := by
  rw [Path.range_eq_image_extend]
  exact ((convex_Icc (0 : ℝ) 1).isPathConnected (nonempty_Icc.2 zero_le_one)).image'
    q.continuous_extend.continuousOn

/-! ### Meeting below a given height (`def:meets-in`) -/

/-- `γx` (an arc at `x`) meets `γy` (an arc at `y`) below height `c`: there are subarcs at `x` and
`y` of them, contained in `{Im z ≤ c}`, which intersect. -/
def MeetsIn (c : ℝ) (γx γy : Set ℂ) (x y : ℂ) : Prop :=
  ∃ α ⊆ γx, ∃ β ⊆ γy, IsArcAt upper x α ∧ IsArcAt upper y β ∧ α ⊆ {z | z.im ≤ c} ∧
    β ⊆ {z | z.im ≤ c} ∧ (α ∩ β).Nonempty

theorem MeetsIn.symm {c : ℝ} {γx γy : Set ℂ} {x y : ℂ} (h : MeetsIn c γx γy x y) :
    MeetsIn c γy γx y x := by
  obtain ⟨α, hα, β, hβ, ha, hb, hac, hbc, hne⟩ := h
  exact ⟨β, hβ, α, hα, hb, ha, hbc, hac, by rwa [inter_comm]⟩

theorem MeetsIn.mono {c c' : ℝ} (hcc' : c ≤ c') {γx γy : Set ℂ} {x y : ℂ}
    (h : MeetsIn c γx γy x y) : MeetsIn c' γx γy x y := by
  obtain ⟨α, hα, β, hβ, ha, hb, hac, hbc, hne⟩ := h
  exact ⟨α, hα, β, hβ, ha, hb, fun z hz => (hac hz).trans hcc',
    fun z hz => (hbc hz).trans hcc', hne⟩

theorem MeetsIn.nonempty_inter {c : ℝ} {γx γy : Set ℂ} {x y : ℂ} (h : MeetsIn c γx γy x y) :
    (γx ∩ γy).Nonempty := by
  obtain ⟨α, hα, β, hβ, -, -, -, -, z, hz⟩ := h
  exact ⟨z, hα hz.1, hβ hz.2⟩

/-! ### The Figure-5 lemma (`lem:figure5`) -/

/-- **Figure 5.** Let `x < t < y`, let `α`, `β` be arcs at `x`, `y` in `{Im z ≤ c}` which
intersect, and let `τ` be an arc from `t` to a point `p` with `Im p = c`, otherwise in `ℍ`.
Then `τ` meets `α ∪ β`. -/
theorem figure5 {c x t y : ℝ} (hxt : x < t) (hty : t < y) {α β τ : Set ℂ} {p : ℂ}
    (hα : IsArcAt upper x α) (hβ : IsArcAt upper y β) (hαc : α ⊆ {z | z.im ≤ c})
    (hβc : β ⊆ {z | z.im ≤ c}) (hαβ : (α ∩ β).Nonempty) (hτ : IsArc τ t p)
    (hτH : τ \ {(t : ℂ)} ⊆ upper) (hp : p.im = c) :
    (τ ∩ (α ∪ β)).Nonempty := by
  have hxy : x < y := hxt.trans hty
  -- a simple arc `σ ⊆ α ∪ β` from `x` to `y`
  obtain ⟨a, ⟨qa, -, hqa⟩, hαH⟩ := hα
  obtain ⟨b, ⟨qb, -, hqb⟩, hβH⟩ := hβ
  obtain ⟨w, hwα, hwβ⟩ := hαβ
  have hJα : JoinedIn α (x : ℂ) w := by
    have : IsPathConnected α := hqa ▸ pathRange_isPathConnected qa
    exact this.joinedIn _ (hqa ▸ ⟨0, qa.source⟩) _ hwα
  have hJβ : JoinedIn β w (y : ℂ) := by
    have : IsPathConnected β := hqb ▸ pathRange_isPathConnected qb
    exact this.joinedIn _ hwβ _ (hqb ▸ ⟨0, qb.source⟩)
  have hJ : JoinedIn (α ∪ β) (x : ℂ) y :=
    (hJα.mono subset_union_left).trans (hJβ.mono subset_union_right)
  have hxy' : (x : ℂ) ≠ y := fun h => hxy.ne (Complex.ofReal_injective h)
  obtain ⟨σ, hσg, hσ⟩ := exists_arc_in_path hJ.somePath hxy'
  have hσαβ : σ ⊆ α ∪ β := by
    rintro z hz
    obtain ⟨s, rfl⟩ := hσg hz
    exact hJ.somePath_mem s
  have hσH : σ \ {(x : ℂ), (y : ℂ)} ⊆ upper := by
    rintro z ⟨hz, hzxy⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzxy
    rcases hσαβ hz with h | h
    · exact hαH ⟨h, hzxy.1⟩
    · exact hβH ⟨h, hzxy.2⟩
  have hσc : ∀ z ∈ σ, z.im ≤ c := fun z hz => by
    rcases hσαβ hz with h | h
    · exact hαc h
    · exact hβc h
  obtain ⟨U, V, hUo, hVo, -, -, hUV, hHσ, -, -, hclU, -, -, habove⟩ :=
    crosscutH_theorem hxy hσ hσH
  by_contra hne
  have hτσ : Disjoint τ σ := by
    rw [Set.disjoint_iff]
    rintro z ⟨hzτ, hzσ⟩
    exact hne ⟨z, hzτ, hσαβ hzσ⟩
  have hsub : τ \ {(t : ℂ)} ⊆ U ∪ V := by
    rw [← hHσ]
    exact fun z hz => ⟨hτH hz, Set.disjoint_left.1 hτσ hz.1⟩
  have htcl : (t : ℂ) ∈ closure (τ \ {(t : ℂ)}) :=
    mem_closure_iff_nhdsWithin_neBot.2 (IsArcAt.nhdsWithin_neBot ⟨p, hτ, hτH⟩)
  rcases (hτ.isPreconnected_diff_left).subset_or_subset hUo hVo hUV hsub with h | h
  · have : (t : ℂ) ∈ closure U ∩ realAxis := ⟨closure_mono h htcl, by simp⟩
    rw [hclU] at this
    obtain ⟨s, hs, hst⟩ := this
    have := Complex.ofReal_injective hst
    subst this
    rcases hs with hs | hs
    · exact absurd hs (not_le.2 hxt)
    · exact absurd (mem_Ici.1 hs) (not_le.2 hty)
  · have hpV : p ∈ V := h ⟨hτ.right_mem, fun hpt => hτ.ne (mem_singleton_iff.1 hpt).symm⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVo p hpV
    have hz : p + (ε / 2 : ℝ) * I ∈ V := hball (by
      rw [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith)
    have hzU : p + (ε / 2 : ℝ) * I ∈ U := habove _ fun w hw => by
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, hp]
      linarith [hσc w hw]
    exact Set.disjoint_left.1 hUV hzU hz

/-! ### The sets `L`, `M`, `K_n` of the proof of `thm:baire-plus-one` -/

/-- The heights `1 / (n + 1)`. -/
noncomputable def lev (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem lev_pos (n : ℕ) : 0 < lev n := by unfold lev; positivity

theorem lev_antitone : Antitone lev := fun m n hmn => by
  unfold lev
  gcongr

theorem tendsto_lev : Tendsto lev atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- `L`: the points `x ∈ P` such that, at every height, `γ x` meets some `γ y`, `y ∈ P \ {x}`. -/
def Lset (P : Set ℝ) (γ : ℝ → Set ℂ) : Set ℝ :=
  {x | x ∈ P ∧ ∀ n : ℕ, ∃ y ∈ P, y ≠ x ∧ MeetsIn (lev n) (γ x) (γ y) x y}

/-- `K_n`: the points `x ∈ P` such that `γ x` reaches height `lev n` and, if `x ∉ L`, `γ x` meets
no `γ y`, `y ∈ P \ {x}`, below height `lev n`. -/
def Kset (P : Set ℝ) (γ : ℝ → Set ℂ) (n : ℕ) : Set ℝ :=
  {x | x ∈ P ∧ (∃ z ∈ γ x, z.im = lev n) ∧
    (x ∉ Lset P γ → ∀ y ∈ P, y ≠ x → ¬ MeetsIn (lev n) (γ x) (γ y) x y)}

/-- An arc at a real point reaches every small height. -/
theorem _root_.TJK.IsArcAt.eventually_reaches {x : ℝ} {γ : Set ℂ} (h : IsArcAt upper x γ) :
    ∀ᶠ n in atTop, ∃ z ∈ γ, z.im = lev n := by
  obtain ⟨b, hb, hbH⟩ := h
  have hbpos : 0 < b.im := hbH ⟨hb.right_mem, fun h' => hb.ne (mem_singleton_iff.1 h').symm⟩
  have hI : Icc 0 b.im ⊆ Complex.im '' γ :=
    (hb.isConnected.image _ Complex.continuous_im.continuousOn).isPreconnected.Icc_subset
      ⟨x, hb.left_mem, by simp⟩ ⟨b, hb.right_mem, rfl⟩
  filter_upwards [(tendsto_order.1 tendsto_lev).2 _ hbpos] with n hn
  obtain ⟨z, hz, hzn⟩ := hI ⟨(lev_pos n).le, hn.le⟩
  exact ⟨z, hz, hzn⟩

section Sets

variable {P : Set ℝ} {γ : ℝ → Set ℂ}

theorem eventually_mem_Kset (hγ : ∀ x ∈ P, IsArcAt upper x (γ x)) {x : ℝ}
    (hx : x ∈ P \ Lset P γ) : ∀ᶠ n in atTop, x ∈ Kset P γ n := by
  have : ¬ ∀ n : ℕ, ∃ y ∈ P, y ≠ x ∧ MeetsIn (lev n) (γ x) (γ y) x y := fun h => hx.2 ⟨hx.1, h⟩
  push Not at this
  obtain ⟨n₁, hn₁⟩ := this
  filter_upwards [(hγ x hx.1).eventually_reaches, eventually_ge_atTop n₁] with n hn hn'
  exact ⟨hx.1, hn, fun _ y hy hyx hm => hn₁ y hy hyx (hm.mono (lev_antitone hn'))⟩

theorem exists_mem_Kset (hγ : ∀ x ∈ P, IsArcAt upper x (γ x)) {x : ℝ} (hx : x ∈ P) :
    ∃ n, x ∈ Kset P γ n := by
  by_cases hL : x ∈ Lset P γ
  · obtain ⟨n, hn⟩ := (hγ x hx).eventually_reaches.exists
    exact ⟨n, hx, hn, fun h => absurd hL h⟩
  · exact (eventually_mem_Kset hγ ⟨hx, hL⟩).exists

/-- The first-hit subarc at height `lev n` of `γ t`, `t ∈ K_n`. -/
theorem exists_firstHit (hγ : ∀ x ∈ P, IsArcAt upper x (γ x)) {n : ℕ} {t : ℝ}
    (ht : t ∈ Kset P γ n) :
    ∃ τ ⊆ γ t, ∃ p : ℂ, p.im = lev n ∧ IsArc τ t p ∧ IsArcAt upper t τ ∧
      τ ⊆ {z | z.im ≤ lev n} ∧ τ \ {(t : ℂ), p} ⊆ openStrip (lev n) := by
  obtain ⟨τ, hτ, p, hp, harc, hat, hτc, hτS⟩ :=
    (hγ t ht.1).exists_subarc_strip (by simp) (lev_pos n) ht.2.1
  exact ⟨τ, hτ, p, hp, harc, hat, fun z hz => (hτc hz).2, hτS⟩

/-- **Step 1, main claim.** If `x ∈ L ∩ A`, `γ x` meets `γ y` below height `lev n`, then every `t`
between `x` and `y` that lies in `K_n` is in `L ∩ A`. -/
theorem mem_Lset_inter_of_meetsIn {A B : Set ℝ} (hP : P = A ∪ B)
    (hγ : ∀ x ∈ P, IsArcAt upper x (γ x)) (hdisj : ∀ x ∈ A, ∀ y ∈ B, Disjoint (γ x) (γ y))
    {n : ℕ} {x y t : ℝ} (hx : x ∈ Lset P γ ∩ A) (hy : y ∈ P) (hyx : y ≠ x)
    (hm : MeetsIn (lev n) (γ x) (γ y) x y) (ht : t ∈ uIcc x y) (htK : t ∈ Kset P γ n) :
    t ∈ Lset P γ ∩ A := by
  have hxP : x ∈ P := hx.1.1
  have htP : t ∈ P := htK.1
  have sideA : ∀ {u v : ℝ}, u ∈ A → v ∈ P → (γ u ∩ γ v).Nonempty → v ∈ A := by
    intro u v hu hv hne
    rw [hP] at hv
    rcases hv with hv | hv
    · exact hv
    · obtain ⟨z, hz⟩ := hne
      exact absurd hz.2 (Set.disjoint_left.1 (hdisj u hu v hv) hz.1)
  have hyA : y ∈ A := sideA hx.2 hy hm.nonempty_inter
  by_cases htx : t = x
  · exact htx ▸ hx
  -- `γ t` meets `γ x` or `γ y` below height `lev n`
  have key : ∃ w, (w = x ∨ w = y) ∧ w ≠ t ∧ MeetsIn (lev n) (γ t) (γ w) t w := by
    by_cases hty : t = y
    · subst hty
      exact ⟨x, Or.inl rfl, Ne.symm htx, hm.symm⟩
    obtain ⟨α, hα, β, hβ, hαa, hβa, hαc, hβc, hαβ⟩ := hm
    obtain ⟨τ, hτ, p, hp, harc, hat, hτc, -⟩ := exists_firstHit hγ htK
    have hτH : τ \ {(t : ℂ)} ⊆ upper := by obtain ⟨_, _, h⟩ := hat; exact h
    have hmeet : (τ ∩ (α ∪ β)).Nonempty := by
      rcases lt_or_gt_of_ne hyx with hlt | hlt
      · rw [uIcc_of_ge hlt.le] at ht
        rw [union_comm]
        exact figure5 (lt_of_le_of_ne ht.1 (Ne.symm hty)) (lt_of_le_of_ne ht.2 htx) hβa hαa hβc
          hαc (by rwa [inter_comm]) harc hτH hp
      · rw [uIcc_of_le hlt.le] at ht
        exact figure5 (lt_of_le_of_ne ht.1 (Ne.symm htx)) (lt_of_le_of_ne ht.2 hty) hαa hβa hαc
          hβc hαβ harc hτH hp
    obtain ⟨z, hzτ, hzα | hzβ⟩ := hmeet
    · exact ⟨x, Or.inl rfl, Ne.symm htx, τ, hτ, α, hα, hat, hαa, hτc, hαc, z, hzτ, hzα⟩
    · exact ⟨y, Or.inr rfl, Ne.symm hty, τ, hτ, β, hβ, hat, hβa, hτc, hβc, z, hzτ, hzβ⟩
  obtain ⟨w, hw, hwt, hmw⟩ := key
  have hwA : w ∈ A := by rcases hw with rfl | rfl; exacts [hx.2, hyA]
  have hwP : w ∈ P := by rcases hw with rfl | rfl; exacts [hxP, hy]
  refine ⟨?_, sideA hwA htP hmw.symm.nonempty_inter⟩
  by_contra htL
  exact htK.2.2 htL w hwP hwt hmw

/-- **Step 1.** `L ∩ A ≈ G ∩ P` for a `G_δ` set `G`. -/
theorem exists_isGδ_countablyEquiv {A B : Set ℝ} (hP : P = A ∪ B)
    (hγ : ∀ x ∈ P, IsArcAt upper x (γ x)) (hdisj : ∀ x ∈ A, ∀ y ∈ B, Disjoint (γ x) (γ y)) :
    ∃ G : Set ℝ, IsGδ G ∧ CountablyEquiv (Lset P γ ∩ A) (G ∩ P) := by
  set S : ℕ → Set (ℝ × ℝ) := fun n =>
    {q | q.1 ∈ Lset P γ ∩ A ∧ q.2 ∈ P ∧ q.2 ≠ q.1 ∧ MeetsIn (lev n) (γ q.1) (γ q.2) q.1 q.2}
  set W : ℕ → Set ℝ := fun n => ⋃ q ∈ S n, uIcc q.1 q.2
  have hO : ∀ n, ∃ O : Set ℝ, IsOpen O ∧ CountablyEquiv (W n) O := by
    intro n
    have := exists_isOpen_countablyEquiv_real (𝓘 := (fun q : ℝ × ℝ => uIcc q.1 q.2) '' S n) (by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨ordConnected_uIcc, q.1, left_mem_uIcc, q.2, right_mem_uIcc, hq.2.2.1.symm⟩)
    simpa only [biUnion_image] using this
  choose O hOo hOW using hO
  have hL : Lset P γ ∩ A = ⋂ n, (W n ∩ P) := by
    apply Subset.antisymm
    · intro x hx
      refine mem_iInter.2 fun n => ⟨?_, hx.1.1⟩
      obtain ⟨y, hy, hyx, hm⟩ := hx.1.2 n
      exact mem_iUnion₂.2 ⟨(x, y), ⟨hx, hy, hyx, hm⟩, left_mem_uIcc⟩
    · intro t ht
      have htP : t ∈ P := (mem_iInter.1 ht 0).2
      obtain ⟨m, hm⟩ := exists_mem_Kset hγ htP
      obtain ⟨q, hq, htq⟩ := mem_iUnion₂.1 (mem_iInter.1 ht m).1
      exact mem_Lset_inter_of_meetsIn hP hγ hdisj hq.1 hq.2.1 hq.2.2.1 hq.2.2.2 htq hm
  refine ⟨⋂ n, O n, IsGδ.iInter_of_isOpen hOo, ?_⟩
  rw [hL, iInter_inter]
  exact CountablyEquiv.iInter fun n => (hOW n).inter (CountablyEquiv.refl P)

/-- Points of an arc `γ` at a real point `x` with imaginary parts tending to `0` tend to `x`. -/
theorem tendsto_of_im_tendsto {x : ℝ} {γ : Set ℂ} (h : IsArcAt upper x γ) {u : ℕ → ℂ}
    (hu : ∀ᶠ n in atTop, u n ∈ γ \ {(x : ℂ)}) (him : Tendsto (fun n => (u n).im) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) := by
  obtain ⟨b, hb, hbH⟩ := h
  refine tendsto_nhdsWithin_iff.2 ⟨?_, hu⟩
  refine hb.isCompact.tendsto_nhds_of_unique_mapClusterPt (hu.mono fun n hn => hn.1) ?_
  intro a ha hcl
  by_contra hax
  have hapos : 0 < a.im := hbH ⟨ha, hax⟩
  have hfr : ∃ᶠ n in atTop, a.im / 2 < (u n).im :=
    hcl.frequently ((Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (show a.im ∈ Ioi (a.im / 2) by simp only [mem_Ioi]; linarith))
  obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually ((tendsto_order.1 him).2 _ (half_pos hapos))).exists
  exact lt_asymm hn1 hn2

/-- **Step 2.** For the points of `M = P \ L` there are weakly increasing `h_n : ℝ → ℝ` such that
`h_n(x) + i lev n → x` along `γ x`. -/
theorem exists_monotone_tendsto
    (hγ : ∀ x ∈ P, IsArcAt upper x (γ x) ∧ γ x ⊆ closedBall (x : ℂ) 1) :
    ∃ h : ℕ → ℝ → ℝ, (∀ n, Monotone (h n)) ∧ ∀ x ∈ P \ Lset P γ,
      Tendsto (fun n => ((h n x : ℂ) + (lev n : ℂ) * I)) atTop (𝓝[γ x \ {(x : ℂ)}] (x : ℂ)) := by
  have hγ' : ∀ x ∈ P, IsArcAt upper x (γ x) := fun x hx => (hγ x hx).1
  have hp : ∀ (n : ℕ) (x : ℝ), ∃ τ : Set ℂ, ∃ p : ℂ, x ∈ Kset P γ n → τ ⊆ γ x ∧ p.im = lev n ∧
      IsArc τ x p ∧ IsArcAt upper x τ ∧ τ ⊆ {z | z.im ≤ lev n} ∧
      τ \ {(x : ℂ), p} ⊆ openStrip (lev n) := by
    intro n x
    by_cases hx : x ∈ Kset P γ n
    · obtain ⟨τ, hτ, p, h1, h2, h3, h4, h5⟩ := exists_firstHit hγ' hx
      exact ⟨τ, p, fun _ => ⟨hτ, h1, h2, h3, h4, h5⟩⟩
    · exact ⟨∅, 0, fun h => absurd h hx⟩
  choose τ p hτp using hp
  have hmono : ∀ n, MonotoneOn (fun x => (p n x).re) ((P \ Lset P γ) ∩ Kset P γ n) := by
    intro n x hx x' hx' hxx'
    rcases hxx'.eq_or_lt with rfl | hlt
    · exact le_rfl
    obtain ⟨hτ, hpn, harc, hat, hτc, hτS⟩ := hτp n x hx.2
    obtain ⟨hτ', hpn', harc', hat', hτc', hτS'⟩ := hτp n x' hx'.2
    refine (strip_order (lev_pos n) hpn hpn' harc harc' hτS hτS' ?_ hlt).le
    rw [Set.disjoint_iff]
    rintro z hz
    exact hx.2.2.2 hx.1.2 x' hx'.1.1 hlt.ne'
      ⟨τ n x, hτ, τ n x', hτ', hat, hat', hτc, hτc', z, hz⟩
  have hdist : ∀ n, ∀ x ∈ (P \ Lset P γ) ∩ Kset P γ n, |x - (p n x).re| ≤ 1 := by
    intro n x hx
    obtain ⟨hτ, -, harc, -⟩ := hτp n x hx.2
    have h1 := mem_closedBall.1 ((hγ x hx.1.1).2 (hτ harc.right_mem))
    rw [Complex.dist_eq] at h1
    calc |x - (p n x).re| = |((x : ℂ) - p n x).re| := by simp
      _ ≤ ‖(x : ℂ) - p n x‖ := Complex.abs_re_le_norm _
      _ = ‖p n x - x‖ := norm_sub_rev _ _
      _ ≤ 1 := h1
  choose h hh hheq using fun n =>
    TJK.MonotoneOn.exists_monotone_extension_of_dist_le (hmono n) (hdist n)
  refine ⟨h, hh, fun x hx => ?_⟩
  have hev : ∀ᶠ n in atTop, (h n x : ℂ) + (lev n : ℂ) * I = p n x ∧ p n x ∈ γ x \ {(x : ℂ)} := by
    filter_upwards [eventually_mem_Kset hγ' hx] with n hn
    obtain ⟨hτ, hpn, harc, -⟩ := hτp n x hn
    refine ⟨?_, hτ harc.right_mem, fun h0 => ?_⟩
    · rw [hheq n ⟨hx, hn⟩]
      apply Complex.ext <;> simp [hpn]
    · have := congrArg Complex.im (mem_singleton_iff.1 h0)
      simp only [hpn, ofReal_im] at this
      exact (lev_pos n).ne' this
  refine tendsto_of_im_tendsto (hγ' x hx.1) (hev.mono fun n hn => ?_) ?_
  · rw [hn.1]; exact hn.2
  · refine tendsto_lev.congr fun n => ?_
    simp
end Sets

/-! ### `thm:baire-plus-one` -/

theorem two_lt_add_one_add_one {ξ : Ordinal.{0}} (hξ : 1 ≤ ξ) : (2 : Ordinal.{0}) < ξ + 1 + 1 := by
  rw [← one_add_one_eq_two]
  exact Order.lt_add_one_iff.2 (add_le_add_left hξ 1)

/-- Countable subsets of `ℝ` are in every class `P^ξ`, `ξ ≥ 2`. -/
theorem addClass_of_countable {ξ : Ordinal.{0}} (hξ : 2 ≤ ξ) {s : Set ℝ} (hs : s.Countable) :
    AddClass ξ s :=
  (addClass_two_iff.2 (TJK.Set.Countable.isFσ hs)).mono hξ

/-- **The core of `thm:baire-plus-one`, on the real line.** Let `A`, `B ⊆ ℝ` be disjoint, `ψ` map
`A` into the open set `U` and `B` outside `U`, and let `γ x` (`x ∈ A ∪ B`) be arcs at `x` in
`closedBall x 1` along which `f → ψ x`, with `γ x ∩ γ y = ∅` for `x ∈ A`, `y ∈ B`. If `f` is of
Baire class `ξ ≥ 1` in `ℍ`, then `A ⊆ T`, `T ∩ B = ∅` for some `T ∈ P^{ξ+2}(ℝ)`. -/
theorem exists_addClass_separating {Y : Type*} [MetricSpace Y] {ξ : Ordinal.{0}} (hξ : 1 ≤ ξ)
    {f : ℂ → Y} (hf : BaireClass ξ (upper.restrict f)) {U : Set Y} (hU : IsOpen U)
    {A B : Set ℝ} (hAB : Disjoint A B) {ψ : ℝ → Y} (hA : ∀ x ∈ A, ψ x ∈ U)
    (hB : ∀ x ∈ B, ψ x ∉ U) {γ : ℝ → Set ℂ}
    (hγ : ∀ x ∈ A ∪ B, IsArcAt upper x (γ x) ∧ γ x ⊆ closedBall (x : ℂ) 1 ∧
      Tendsto f (𝓝[γ x \ {(x : ℂ)}] (x : ℂ)) (𝓝 (ψ x)))
    (hdisj : ∀ x ∈ A, ∀ y ∈ B, Disjoint (γ x) (γ y)) :
    ∃ T : Set ℝ, AddClass (ξ + 1 + 1) T ∧ A ⊆ T ∧ Disjoint T B := by
  set P := A ∪ B with hP
  have hγ' : ∀ x ∈ P, IsArcAt upper x (γ x) := fun x hx => (hγ x hx).1
  have h2 := two_lt_add_one_add_one hξ
  -- Step 1
  obtain ⟨Ga, hGa, hLa⟩ := exists_isGδ_countablyEquiv hP hγ' hdisj
  obtain ⟨Gb, hGb, hLb⟩ := exists_isGδ_countablyEquiv (A := B) (B := A) (union_comm A B) hγ'
    fun x hx y hy => (hdisj y hy x hx).symm
  -- Step 2
  obtain ⟨h, hh, hlim⟩ := exists_monotone_tendsto fun x hx => ⟨(hγ x hx).1, (hγ x hx).2.1⟩
  have hF : ∀ n, BaireClass ξ (fun s : ℝ => f ((s : ℂ) + (lev n : ℂ) * I)) := fun n =>
    hf.comp_continuous (g := fun s : ℝ => (⟨(s : ℂ) + (lev n : ℂ) * I, by
      simp [lev_pos n]⟩ : upper)) (by fun_prop)
  choose N hN hNB using fun n => (hF n).comp_monotone (hh n)
  set M := P \ Lset P γ with hM
  set S := M \ ⋃ n, N n with hS
  have hgS : ∀ n, BaireClass ξ (S.restrict ((fun s : ℝ => f ((s : ℂ) + (lev n : ℂ) * I)) ∘ h n)) :=
    fun n => (hNB n).comp_continuous (g := Set.inclusion fun x hx hxN =>
      hx.2 (mem_iUnion.2 ⟨n, hxN⟩)) (continuous_inclusion _)
  have hψS : BaireClass (ξ + 1) (S.restrict ψ) :=
    .lim (fun _ => ξ) _ (zero_le.trans_lt (Order.lt_add_one_iff.2 le_rfl))
      (fun _ => Order.lt_add_one_iff.2 le_rfl) hgS
      fun x => (hγ x x.2.1.1).2.2.comp (hlim x x.2.1)
  obtain ⟨D, hD, hDeq⟩ := AddClass.subtype_iff.1 (hψS.addClass_preimage U hU)
  have hAD : ∀ x ∈ S, x ∈ A ↔ x ∈ D := by
    intro x hx
    have : ψ x ∈ U ↔ x ∈ D := Iff.of_eq (congrArg (fun s : Set S => (⟨x, hx⟩ : S) ∈ s) hDeq)
    rw [← this]
    refine ⟨hA x, fun hxU => ?_⟩
    rcases hx.1.1 with hxA | hxB
    · exact hxA
    · exact absurd hxU (hB x hxB)
  -- Step 3: bookkeeping
  have hNc : (⋃ n, N n).Countable := countable_iUnion hN
  set T₀ := Ga ∪ (D ∩ (Ga ∪ Gb)ᶜ) with hT₀
  have hT₀c : AddClass (ξ + 1 + 1) T₀ := by
    refine (MulClass.addClass_of_lt (mulClass_two_iff.2 hGa) h2).union (hD.inter ?_)
    exact (mulClass_iff_compl.1 (mulClass_two_iff.2 (hGa.union hGb))).mono h2.le
  have hLsub : Lset P γ ⊆ P := fun x hx => hx.1
  have hL : CountablyEquiv (Lset P γ) ((Ga ∪ Gb) ∩ P) := by
    have := hLa.union hLb
    rwa [← inter_union_distrib_left, inter_eq_left.2 hLsub,
      ← union_inter_distrib_right] at this
  have hMD : CountablyEquiv (M ∩ A) ((P \ ((Ga ∪ Gb) ∩ P)) ∩ D) := by
    refine CountablyEquiv.trans ?_ ((hL.diff P).inter (CountablyEquiv.refl D))
    refine ⟨hNc.mono ?_, hNc.mono ?_⟩
    · rintro x ⟨⟨hxM, hxA⟩, hxD⟩
      by_contra hxN
      exact hxD ⟨hxM, (hAD x ⟨hxM, hxN⟩).1 hxA⟩
    · rintro x ⟨⟨hxM, hxD⟩, hxA⟩
      by_contra hxN
      exact hxA ⟨hxM, (hAD x ⟨hxM, hxN⟩).2 hxD⟩
  have hAeq : (Lset P γ ∩ A) ∪ (M ∩ A) = A := by
    ext x
    constructor
    · rintro (hx | hx)
      exacts [hx.2, hx.2]
    · intro hx
      by_cases hxL : x ∈ Lset P γ
      · exact Or.inl ⟨hxL, hx⟩
      · exact Or.inr ⟨⟨Or.inl hx, hxL⟩, hx⟩
  have hTeq : (Ga ∩ P) ∪ ((P \ ((Ga ∪ Gb) ∩ P)) ∩ D) = T₀ ∩ P := by
    ext x
    simp only [hT₀, mem_union, mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
    tauto
  have hE : CountablyEquiv A (T₀ ∩ P) := by
    have := hLa.union hMD
    rwa [hAeq, hTeq] at this
  -- correct by countable sets
  set C₁ := A \ (T₀ ∩ P)
  set C₂ := (T₀ ∩ P) \ A
  refine ⟨(T₀ ∩ C₂ᶜ) ∪ C₁, ?_, ?_, ?_⟩
  · refine (hT₀c.inter ?_).union (addClass_of_countable h2.le hE.1)
    exact MulClass.addClass_of_lt
      (addClass_iff_compl.1 (addClass_of_countable le_rfl hE.2)) h2
  · intro x hx
    by_cases hxT : x ∈ T₀
    · exact Or.inl ⟨hxT, fun h => h.2 hx⟩
    · exact Or.inr ⟨hx, fun h => hxT h.1⟩
  · rw [Set.disjoint_left]
    rintro x (⟨hxT, hxC⟩ | ⟨hxA, -⟩) hxB
    · exact hxC ⟨⟨hxT, Or.inr hxB⟩, Set.disjoint_right.1 hAB hxB⟩
    · exact Set.disjoint_left.1 hAB hxA hxB

/-- **Dissertation Theorem 8 / 1965 paper Theorem 4** (`thm:baire-plus-one`). A boundary function
of a function of Baire class `ξ ≥ 1` in `ℍ` with values in a separable arcwise connected metric
space is of Baire class `ξ + 1`. -/
theorem baireClass_succ_of_boundaryFn' {Y : Type} [MetricSpace Y]
    [TopologicalSpace.SeparableSpace Y] [PathConnectedSpace Y] (ξ : Ordinal.{0}) (hξ : 1 ≤ ξ)
    (f : ℂ → Y) (hf : BaireClass ξ (upper.restrict f)) (E : Set ℂ) (hE : E ⊆ realAxis)
    (φ : ℂ → Y) (hφ : IsBoundaryFunction upper f E φ) :
    BaireClass (ξ + 1) (E.restrict φ) := by
  have h2 : (2 : Ordinal.{0}) ≤ ξ + 1 := by
    rw [← one_add_one_eq_two]
    exact add_le_add_left hξ 1
  refine baireClass_of_sandwich h2 fun U hU => ?_
  set V := (closure U)ᶜ with hV
  set A := {x : ℝ | (x : ℂ) ∈ E ∧ φ x ∈ U} with hA
  set B := {x : ℝ | (x : ℂ) ∈ E ∧ φ x ∈ V} with hB
  have hAB : Disjoint A B := Set.disjoint_left.2 fun x hxA hxB => hxB.2 (subset_closure hxA.2)
  have hsel : ∀ x : ℝ, ∃ γ : Set ℂ, (x ∈ A ∪ B → IsArcAt upper x γ ∧ γ ⊆ closedBall (x : ℂ) 1 ∧
      Tendsto f (𝓝[γ \ {(x : ℂ)}] (x : ℂ)) (𝓝 (φ x))) ∧
      (x ∈ A → MapsTo f (γ \ {(x : ℂ)}) U) ∧ (x ∈ B → MapsTo f (γ \ {(x : ℂ)}) V) := by
    intro x
    by_cases hx : x ∈ A ∪ B
    · have hxE : (x : ℂ) ∈ E := by rcases hx with h | h; exacts [h.1, h.1]
      obtain ⟨γ, hγ, hlim⟩ := hφ x hxE
      have key : ∀ W : Set Y, IsOpen W → φ x ∈ W → ∃ γ' : Set ℂ, (IsArcAt upper x γ' ∧
          γ' ⊆ closedBall (x : ℂ) 1 ∧ Tendsto f (𝓝[γ' \ {(x : ℂ)}] (x : ℂ)) (𝓝 (φ x))) ∧
          MapsTo f (γ' \ {(x : ℂ)}) W := by
        intro W hW hxW
        obtain ⟨γ', hγ's, hat, hmaps⟩ :=
          hγ.tendsto_subarc hlim (hW.mem_nhds hxW) (closedBall_mem_nhds _ one_pos)
        exact ⟨γ', ⟨hat, hγ's.trans inter_subset_right, hlim.mono_left (nhdsWithin_mono _
          (sdiff_subset_sdiff_left (hγ's.trans inter_subset_left)))⟩, hmaps⟩
      rcases hx with hxA | hxB
      · obtain ⟨γ', h1, h2⟩ := key U hU hxA.2
        exact ⟨γ', fun _ => h1, fun _ => h2,
          fun hxB => absurd hxB (Set.disjoint_left.1 hAB hxA)⟩
      · obtain ⟨γ', h1, h2⟩ := key V isClosed_closure.isOpen_compl hxB.2
        exact ⟨γ', fun _ => h1, fun hxA => absurd hxB (Set.disjoint_left.1 hAB hxA),
          fun _ => h2⟩
    · exact ⟨∅, fun h => absurd h hx, fun h => absurd (Or.inl h) hx,
        fun h => absurd (Or.inr h) hx⟩
  choose γ hγ hγA hγB using hsel
  have hdisj : ∀ x ∈ A, ∀ y ∈ B, Disjoint (γ x) (γ y) := by
    intro x hx y hy
    rw [Set.disjoint_iff]
    rintro z ⟨hzx, hzy⟩
    have hxy : (x : ℂ) ≠ y := fun h =>
      Set.disjoint_left.1 hAB hx (Complex.ofReal_injective h ▸ hy)
    have hupy : γ y \ {(y : ℂ)} ⊆ upper := by
      obtain ⟨_, _, h⟩ := (hγ y (Or.inr hy)).1; exact h
    have hupx : γ x \ {(x : ℂ)} ⊆ upper := by
      obtain ⟨_, _, h⟩ := (hγ x (Or.inl hx)).1; exact h
    by_cases hz : z = x
    · subst hz
      have := hupy ⟨hzy, fun h => hxy (mem_singleton_iff.1 h)⟩
      simp at this
    · have hzu : z ∈ upper := hupx ⟨hzx, hz⟩
      have hzy' : z ≠ y := fun h => by subst h; simp at hzu
      exact hγB y hy ⟨hzy, hzy'⟩ (subset_closure (hγA x hx ⟨hzx, hz⟩))
  obtain ⟨T, hT, hAT, hTB⟩ := exists_addClass_separating hξ hf hU hAB (ψ := fun x => φ x)
    (fun x hx => hx.2) (fun x hx hxU => hx.2 (subset_closure hxU)) hγ hdisj
  have hre : ∀ z : E, ((z : ℂ).re : ℂ) = z := fun z =>
    Complex.ext (by simp) (by simp [show (z : ℂ).im = 0 from hE z.2])
  refine ⟨Subtype.val ⁻¹' (Complex.re ⁻¹' T),
    AddClass.subtype_iff.2 ⟨_, hT.preimage Complex.continuous_re, rfl⟩, ?_, ?_⟩
  · intro z hz
    refine hAT (show (z : ℂ).re ∈ A from ?_)
    rw [hA, mem_ofPred_eq, hre z]
    exact ⟨z.2, hz⟩
  · intro z hz
    by_contra hzU
    refine Set.disjoint_left.1 hTB hz (show (z : ℂ).re ∈ B from ?_)
    rw [hB, mem_ofPred_eq, hre z]
    exact ⟨z.2, hzU⟩

/-! ### `cor:borel` -/

/-- **Dissertation Theorem 8, Corollary** (`cor:borel`). A boundary function of a Borel measurable
function in `ℍ` with values in a separable arcwise connected metric space is Borel measurable. -/
theorem measurable_of_boundaryFn {Y : Type} [MetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    [PathConnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y] (f : ℂ → Y)
    (hf : Measurable (upper.restrict f)) (E : Set ℂ) (hE : E ⊆ realAxis) (φ : ℂ → Y)
    (hφ : IsBoundaryFunction upper f E φ) : Measurable (E.restrict φ) := by
  obtain ⟨ξ, -, hξ⟩ := borel_measurable_exists_baireClass hf
  exact (baireClass_succ_of_boundaryFn' (max ξ 1) (le_max_right _ _) f
    (hξ.mono (le_max_left _ _)) E hE φ hφ).measurable

/-- **1965 paper, Theorem 4** (`cor:borel`): a real boundary function of a real function of Baire
class `ξ ≥ 1` in `ℍ` is of Baire class `ξ + 1`. (Theorem 5 is `measurable_of_boundaryFn` with
`Y = ℝ`.) -/
theorem baireClass_succ_of_boundaryFn_real (ξ : Ordinal.{0}) (hξ : 1 ≤ ξ) (f : ℂ → ℝ)
    (hf : BaireClass ξ (upper.restrict f)) (E : Set ℂ) (hE : E ⊆ realAxis) (φ : ℂ → ℝ)
    (hφ : IsBoundaryFunction upper f E φ) : BaireClass (ξ + 1) (E.restrict φ) :=
  baireClass_succ_of_boundaryFn' ξ hξ f hf E hE φ hφ

/-- `cor:borel` for real functions (1965 paper, Theorem 5). -/
example (f : ℂ → ℝ) (hf : Measurable (upper.restrict f)) (E : Set ℂ) (hE : E ⊆ realAxis)
    (φ : ℂ → ℝ) (hφ : IsBoundaryFunction upper f E φ) : Measurable (E.restrict φ) :=
  measurable_of_boundaryFn f hf E hE φ hφ

end TJK.Discont
