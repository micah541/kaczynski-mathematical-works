import Mathlib
import TJK.Defs
import TJK.Baire.Basic
import TJK.Baire.Higher
import TJK.Plane.Basic
import TJK.Plane.Crosscut

/-!
# Sets of curvilinear convergence (blueprint §D)

* `def:acc`: crosscut sets `Gamma`, the open arcs `crossArcOpen` (`L(γ)*`), `I0`, `acc`;
* `lem:mm-lemma2` (`countable_acc_diff_I0`), `lem:mm-lemma3` (`inter_nonempty`);
* `thm:mcmillan` (`isFσδ_curvConvSet'`), `thm:mm-thm2` (`isFσδ_clusterSet_subset'`),
  `cor:mm-corollaries`, `thm:mcmillan-H`;
* the half-plane lemmas `lem:th-lemma7`, `lem:th-lemma8`;
* `fact:hyperspace` (`compactSpace_nonemptyCompacts`, from Mathlib).

Both theorems are reduced to one skeleton (`isFσδ_of_skeleton`): for countably many open sets
`O n i ⊆ 𝔻 \ {0}` with components `comp (O n i) j`, every set `X` squeezed between
`Y = ⋂ₙ ⋃ᵢⱼ (I₀ ∩ closure acc)` and `⋂ₙ ⋃ᵢⱼ acc` is `F_σδ`. The inclusion `Y ⊆ X` uses an infinite
concatenation of paths (`exists_path_of_seq`) shrinking to a boundary point.
-/

namespace TJK

open _root_.Set Filter Topology Metric Function Complex TopologicalSpace

open scoped Real

/-- `fact:hyperspace`: the nonempty compact (= closed) subsets of a compact metric space form a
compact space in the Hausdorff metric. -/
theorem compactSpace_nonemptyCompacts (K : Type*) [MetricSpace K] [CompactSpace K] :
    CompactSpace (NonemptyCompacts K) := inferInstance

namespace McMillan

/-! ### Definitions (`def:acc`) -/

/-- `Γ(Ω)`: the crosscuts `γ` of `𝔻` with `γ ∩ 𝔻 ⊆ Ω`. -/
def Gamma (Ω : Set ℂ) : Set (Set ℂ) := {σ | IsCrosscut disc circle σ ∧ σ ∩ disc ⊆ Ω}

/-- `L(γ)*`: the open arc of `C` cut off by `γ` away from `0`, i.e. `C` minus the closure of the
component of `𝔻 \ γ` containing `0`. -/
def crossArcOpen (σ : Set ℂ) : Set ℂ := circle \ closure (connectedComponentIn (disc \ σ) 0)

/-- `I₀(Ω) = ⋃_{γ ∈ Γ(Ω)} L(γ)*`. -/
def I0 (Ω : Set ℂ) : Set ℂ := ⋃ σ ∈ Gamma Ω, crossArcOpen σ

/-- The points of `C` accessible by an arc in `Ω`. -/
def acc (Ω : Set ℂ) : Set ℂ := {x | x ∈ circle ∧ ∃ γ, IsArcAt Ω x γ}

theorem not_mem_disc_of_mem_circle {z : ℂ} (hz : z ∈ circle) : z ∉ disc := fun h => by
  have h1 : ‖z‖ < 1 := mem_ball_zero_iff.1 h
  have h2 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
  linarith

theorem zero_mem_disc : (0 : ℂ) ∈ disc := mem_ball_self one_pos

theorem zero_not_mem_circle : (0 : ℂ) ∉ circle := fun h => by
  have := mem_sphere_zero_iff_norm.1 h; simp at this

theorem IsArcAt.mem_closure_diff {E : Type*} [TopologicalSpace E] [T2Space E] {Ω : Set E}
    {x : E} {γ : Set E} (h : IsArcAt Ω x γ) : x ∈ closure (γ \ {x}) :=
  mem_closure_iff_nhdsWithin_neBot.2 h.nhdsWithin_neBot

theorem acc_subset_closure (Ω : Set ℂ) : acc Ω ⊆ closure Ω := by
  rintro x ⟨-, γ, hγ⟩
  obtain ⟨b, -, hΩ⟩ := id hγ
  exact closure_mono hΩ (IsArcAt.mem_closure_diff hγ)

theorem closure_acc_subset (Ω : Set ℂ) : closure (acc Ω) ⊆ closure Ω :=
  closure_minimal (acc_subset_closure Ω) isClosed_closure

theorem I0_eq (Ω : Set ℂ) :
    I0 Ω = circle ∩ ⋃ σ ∈ Gamma Ω, (closure (connectedComponentIn (disc \ σ) 0))ᶜ := by
  ext x
  simp only [I0, crossArcOpen, mem_iUnion₂, mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
  constructor
  · rintro ⟨σ, hσ, hx, hx'⟩; exact ⟨hx, σ, hσ, hx'⟩
  · rintro ⟨hx, σ, hσ, hx'⟩; exact ⟨σ, hσ, hx, hx'⟩

theorem I0_subset_circle (Ω : Set ℂ) : I0 Ω ⊆ circle := by
  rw [I0_eq]; exact inter_subset_left

theorem isFσ_I0_inter (Ω s : Set ℂ) : IsFσ (I0 Ω ∩ closure s) := by
  rw [I0_eq]
  refine ((IsClosed.isFσ isClosed_sphere).inter (IsOpen.isFσ ?_)).inter
    (IsClosed.isFσ isClosed_closure)
  exact isOpen_biUnion fun σ _ => isClosed_closure.isOpen_compl

/-! ### Crosscuts of the disk -/

/-- The data used in `lem:mm-lemma3`: `D \ σ = U ∪ V` with `U, V` open and disjoint, `U`
preconnected, and `σ ∩ D` nonempty, preconnected and contained in `closure U`. -/
structure Split (D σ U V : Set ℂ) : Prop where
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isPreconnected_U : IsPreconnected U
  disjoint : Disjoint U V
  diff_eq : D \ σ = U ∪ V
  nonempty : (σ ∩ D).Nonempty
  isPreconnected_inter : IsPreconnected (σ ∩ D)
  subset_closure : σ ∩ D ⊆ closure U

theorem connectedComponentIn_eq_of_split {F U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hc : IsPreconnected U) (hd : Disjoint U V) (hF : F = U ∪ V) {z : ℂ} (hz : z ∈ U) :
    connectedComponentIn F z = U := by
  have hzF : z ∈ F := by rw [hF]; exact Or.inl hz
  apply Subset.antisymm
  · have hsub : connectedComponentIn F z ⊆ U ∪ V := by
      rw [← hF]; exact connectedComponentIn_subset F z
    rcases isPreconnected_connectedComponentIn.subset_or_subset hU hV hd hsub with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn hzF)) (disjoint_left.1 hd hz)
  · exact hc.subset_connectedComponentIn hz (by rw [hF]; exact subset_union_left)

theorem inter_disc_eq {σ : Set ℂ} {a b : ℂ} (ha : a ∈ circle) (hb : b ∈ circle)
    (hσ : σ \ {a, b} ⊆ disc) : σ ∩ disc = σ \ {a, b} := by
  ext z
  constructor
  · rintro ⟨hz, hzD⟩
    refine ⟨hz, ?_⟩
    rintro (rfl | rfl)
    · exact not_mem_disc_of_mem_circle ha hzD
    · exact not_mem_disc_of_mem_circle hb hzD
  · intro hz; exact ⟨hz.1, hσ hz⟩

/-- A crosscut `σ ∌ 0` of `𝔻` splits `𝔻`; the component `U` containing `0` has
`L(σ)* = C \ closure U`. -/
theorem exists_split {σ : Set ℂ} (h : IsCrosscut disc circle σ) (h0 : (0 : ℂ) ∉ σ) :
    ∃ U V, Split disc σ U V ∧ (0 : ℂ) ∈ U ∧ crossArcOpen σ = circle \ closure U := by
  obtain ⟨θ, ℓ, hℓ, hℓ', harc, hD⟩ := h.exists_angles
  obtain ⟨U₀, V₀, hU₀, hV₀, hcU₀, hcV₀, hd, heq, -, -, hσU, hσV⟩ :=
    crosscut_components hℓ hℓ' harc hD
  have hinter := inter_disc_eq (expI_mem_circle θ) (expI_mem_circle (θ + ℓ)) hD
  have hne : (σ ∩ disc).Nonempty := hinter ▸ harc.nonempty_diff_pair
  have hpc : IsPreconnected (σ ∩ disc) := hinter ▸ harc.isPreconnected_diff_pair
  have h0D : (0 : ℂ) ∈ disc \ σ := ⟨zero_mem_disc, h0⟩
  rw [heq] at h0D
  rcases h0D with h0U | h0V
  · refine ⟨U₀, V₀, ⟨hU₀, hV₀, hcU₀.isPreconnected, hd, heq, hne, hpc, fun z hz => hσU hz.1⟩,
      h0U, ?_⟩
    rw [crossArcOpen, connectedComponentIn_eq_of_split hU₀ hV₀ hcU₀.isPreconnected hd heq h0U]
  · have heq' : disc \ σ = V₀ ∪ U₀ := by rw [heq, union_comm]
    refine ⟨V₀, U₀, ⟨hV₀, hU₀, hcV₀.isPreconnected, hd.symm, heq', hne, hpc,
      fun z hz => hσV hz.1⟩, h0V, ?_⟩
    rw [crossArcOpen,
      connectedComponentIn_eq_of_split hV₀ hU₀ hcV₀.isPreconnected hd.symm heq' h0V]

theorem expI_ne_of_lt {r r' : ℝ} (h1 : r' < r) (h2 : r < r' + 2 * π) : expI r ≠ expI r' := by
  intro h
  obtain ⟨k, hk⟩ := expI_eq_expI_iff.1 h
  have := int_eq_zero_of_mul_two_pi_mem (k := k) (by linarith [Real.pi_pos]) (by linarith)
  subst this
  simp at hk
  linarith

/-- For a crosscut from `e^{iθ}` to `e^{i(θ+ℓ)}` not through `0`, `L(σ)*` contains an open arc
`e^{i(s,t)}` whose closure contains `e^{iθ}`. -/
theorem exists_Ioo_subset_crossArcOpen {σ : Set ℂ} {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ < 2 * π)
    (hσ : IsArc σ (expI θ) (expI (θ + ℓ))) (hσD : σ \ {expI θ, expI (θ + ℓ)} ⊆ disc)
    (h0 : (0 : ℂ) ∉ σ) :
    ∃ s t : ℝ, s < t ∧ expI θ ∈ expI '' Icc s t ∧ expI '' Ioo s t ⊆ crossArcOpen σ := by
  obtain ⟨U₀, V₀, hU₀, hV₀, hcU₀, hcV₀, hd, heq, hclU, hclV, -, -⟩ :=
    crosscut_components hℓ hℓ' hσ hσD
  have h0D : (0 : ℂ) ∈ disc \ σ := ⟨zero_mem_disc, h0⟩
  rw [heq] at h0D
  rcases h0D with h0U | h0V
  · rw [crossArcOpen, connectedComponentIn_eq_of_split hU₀ hV₀ hcU₀.isPreconnected hd heq h0U]
    refine ⟨θ + ℓ, θ + 2 * π, by linarith, ⟨θ + 2 * π, ⟨by linarith, le_rfl⟩, ?_⟩, ?_⟩
    · rw [show θ + 2 * π = θ + ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring, expI_add_int_mul]
    · rintro _ ⟨r, hr, rfl⟩
      refine ⟨expI_mem_circle r, fun hcl => ?_⟩
      have : expI r ∈ closure U₀ ∩ circle := ⟨hcl, expI_mem_circle r⟩
      rw [hclU] at this
      obtain ⟨r', hr', he⟩ := this
      exact expI_ne_of_lt (by linarith [hr.1, hr'.2]) (by linarith [hr.2, hr'.1]) he.symm
  · have heq' : disc \ σ = V₀ ∪ U₀ := by rw [heq, union_comm]
    rw [crossArcOpen,
      connectedComponentIn_eq_of_split hV₀ hU₀ hcV₀.isPreconnected hd.symm heq' h0V]
    refine ⟨θ, θ + ℓ, by linarith, ⟨θ, ⟨le_rfl, by linarith⟩, rfl⟩, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨expI_mem_circle r, fun hcl => ?_⟩
    have : expI r ∈ closure V₀ ∩ circle := ⟨hcl, expI_mem_circle r⟩
    rw [hclV] at this
    obtain ⟨r', hr', he⟩ := this
    exact expI_ne_of_lt (by linarith [hr.2, hr'.1]) (by linarith [hr.1, hr'.2]) he

/-- Joining two arcs at `a ≠ a'` in a path-connected `Ω` (with `a, a' ∉ Ω`) through `Ω`, and
extracting a simple arc (`fact:tietze-arc`): a crosscut-like arc from `a` to `a'` through `Ω`. -/
theorem exists_arc_join {Ω : Set ℂ} (hΩ : IsPathConnected Ω) {a a' : ℂ} (hne : a ≠ a')
    {γ γ' : Set ℂ} (hγ : IsArcAt Ω a γ) (hγ' : IsArcAt Ω a' γ') :
    ∃ σ, IsArc σ a a' ∧ σ \ {a, a'} ⊆ Ω := by
  obtain ⟨c, harc, hqΩ⟩ := hγ
  obtain ⟨c', harc', hq'Ω⟩ := hγ'
  obtain ⟨q, -, hq⟩ := id harc
  obtain ⟨q', -, hq'⟩ := id harc'
  have hc : c ∈ Ω := hqΩ ⟨harc.right_mem, fun h => harc.ne (mem_singleton_iff.1 h).symm⟩
  have hc' : c' ∈ Ω := hq'Ω ⟨harc'.right_mem, fun h => harc'.ne (mem_singleton_iff.1 h).symm⟩
  set hJ := hΩ.joinedIn c hc c' hc'
  set P : Path a a' := (q.trans hJ.somePath).trans q'.symm
  obtain ⟨σ, hσP, hσ⟩ := exists_arc_in_path P hne
  refine ⟨σ, hσ, ?_⟩
  rintro z ⟨hz, hza⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hza
  have := hσP hz
  rw [Path.trans_range, Path.trans_range, Path.symm_range, hq, hq'] at this
  rcases this with (h | ⟨t, rfl⟩) | h
  · exact hqΩ ⟨h, hza.1⟩
  · exact hJ.somePath_mem t
  · exact hq'Ω ⟨h, hza.2⟩

/-! ### McMillan's Lemmas 2 and 3 -/

/-- `lem:mm-lemma2`: `acc(Ω) \ I₀(Ω)` is countable. -/
theorem countable_acc_diff_I0 {Ω : Set ℂ} (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (hD : Ω ⊆ disc \ {0}) : (acc Ω \ I0 Ω).Countable := by
  by_cases hs : (acc Ω).Subsingleton
  · exact hs.countable.mono sdiff_subset
  rw [Set.not_subsingleton_iff] at hs
  obtain ⟨a₀, ha₀, a₁, ha₁, hne⟩ := hs
  have hΩne : Ω.Nonempty := by
    obtain ⟨-, γ, b, harc, hΩ⟩ := ha₀
    exact ⟨b, hΩ ⟨harc.right_mem, fun h => harc.ne (mem_singleton_iff.1 h).symm⟩⟩
  have hpc : IsPathConnected Ω := (ho.isConnected_iff_isPathConnected).1 ⟨hΩne, hc⟩
  set S : Set (ℝ × ℝ) := {st | st.1 < st.2 ∧ expI '' Ioo st.1 st.2 ⊆ I0 Ω}
  refine (countable_biUnion_diff_interior_circle (S := S) fun p hp => hp.1).mono ?_
  rintro x ⟨hx, hxI⟩
  obtain ⟨a', ha', hxa'⟩ : ∃ a' ∈ acc Ω, x ≠ a' := by
    by_cases h : x = a₀
    · exact ⟨a₁, ha₁, h ▸ hne⟩
    · exact ⟨a₀, ha₀, h⟩
  obtain ⟨hxC, γ, hγ⟩ := hx
  obtain ⟨ha'C, γ', hγ'⟩ := ha'
  obtain ⟨σ, hσ, hσΩ⟩ := exists_arc_join hpc hxa' hγ hγ'
  obtain ⟨θ, ℓ, hℓ, hℓ', hθ, hθℓ⟩ := exists_angles_of_ne hxC ha'C hxa'
  have hσD : σ \ {expI θ, expI (θ + ℓ)} ⊆ disc := by
    rw [hθ, hθℓ]; exact fun z hz => (hD (hσΩ hz)).1
  have h0 : (0 : ℂ) ∉ σ := fun h0 => by
    have h0x : (0 : ℂ) ≠ x := fun h => zero_not_mem_circle (h ▸ hxC)
    have h0a : (0 : ℂ) ≠ a' := fun h => zero_not_mem_circle (h ▸ ha'C)
    exact (hD (hσΩ ⟨h0, by simp [h0x, h0a]⟩)).2 rfl
  have hσΓ : σ ∈ Gamma Ω := by
    refine ⟨⟨x, a', hxa', hxC, ha'C, hσ, fun z hz => (hD (hσΩ hz)).1⟩, ?_⟩
    rintro z ⟨hz, hzD⟩
    refine hσΩ ⟨hz, ?_⟩
    rintro (rfl | rfl)
    · exact not_mem_disc_of_mem_circle hxC hzD
    · exact not_mem_disc_of_mem_circle ha'C hzD
  obtain ⟨s, t, hst, hxs, hsub⟩ :=
    exists_Ioo_subset_crossArcOpen hℓ hℓ' (by rw [hθ, hθℓ]; exact hσ) hσD h0
  rw [hθ] at hxs
  have hsub' : expI '' Ioo s t ⊆ I0 Ω :=
    hsub.trans (subset_biUnion_of_mem (u := crossArcOpen) hσΓ)
  refine ⟨mem_iUnion₂.2 ⟨(s, t), ⟨hst, hsub'⟩, hxs⟩, fun h => hxI ?_⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 h
  exact hp.2 hxp

/-- The topological core of `lem:mm-lemma3` (and of `lem:th-lemma8`). -/
theorem inter_nonempty_of_split {D σ₁ σ₂ Ω₁ Ω₂ U₁ V₁ U₂ V₂ : Set ℂ} {a : ℂ}
    (h₁ : Split D σ₁ U₁ V₁) (h₂ : Split D σ₂ U₂ V₂) (hσ₁ : σ₁ ∩ D ⊆ Ω₁) (hσ₂ : σ₂ ∩ D ⊆ Ω₂)
    (hΩ₁ : Ω₁ ⊆ D) (hΩ₂ : Ω₂ ⊆ D) (hc₁ : IsPreconnected Ω₁) (hc₂ : IsPreconnected Ω₂)
    (hUU : (U₁ ∩ U₂).Nonempty) (ha₁ : a ∉ closure U₁) (ha₂ : a ∉ closure U₂)
    (ha₁' : a ∈ closure Ω₁) (ha₂' : a ∈ closure Ω₂) : (Ω₁ ∩ Ω₂).Nonempty := by
  by_contra hne
  have hdisj : ∀ z, z ∈ Ω₁ → z ∉ Ω₂ := fun z h1 h2 => hne ⟨z, h1, h2⟩
  have key : ∀ {σ σ' Ω Ω' U V U' V' : Set ℂ}, Split D σ U V → Split D σ' U' V' →
      σ ∩ D ⊆ Ω → σ' ∩ D ⊆ Ω' → Ω' ⊆ D → IsPreconnected Ω' → (∀ z, z ∈ Ω → z ∉ Ω') →
      a ∉ closure U → a ∈ closure Ω' → σ' ∩ D ⊆ U → False := by
    intro σ σ' Ω Ω' U V U' V' hs hs' hσ hσ' hΩ' hc' hd ha ha' hsub
    have hsub' : Ω' ⊆ U ∪ V := by
      rw [← hs.diff_eq]
      intro z hz
      exact ⟨hΩ' hz, fun hzσ => hd z (hσ ⟨hzσ, hΩ' hz⟩) hz⟩
    rcases hc'.subset_or_subset hs.isOpen_U hs.isOpen_V hs.disjoint hsub' with h | h
    · exact ha (closure_mono h ha')
    · obtain ⟨w, hw⟩ := hs'.nonempty
      exact disjoint_left.1 hs.disjoint (hsub hw) (h (hσ' hw))
  have hτ₁ : σ₁ ∩ D ⊆ U₂ ∪ V₂ := by
    rw [← h₂.diff_eq]
    intro z hz
    exact ⟨hz.2, fun hzσ => hdisj z (hσ₁ hz) (hσ₂ ⟨hzσ, hz.2⟩)⟩
  have hτ₂ : σ₂ ∩ D ⊆ U₁ ∪ V₁ := by
    rw [← h₁.diff_eq]
    intro z hz
    exact ⟨hz.2, fun hzσ => hdisj z (hσ₁ ⟨hzσ, hz.2⟩) (hσ₂ hz)⟩
  rcases h₁.isPreconnected_inter.subset_or_subset h₂.isOpen_U h₂.isOpen_V h₂.disjoint hτ₁ with
    k₁ | k₁
  · exact key h₂ h₁ hσ₂ hσ₁ hΩ₁ hc₁ (fun z h2 h1 => hdisj z h1 h2) ha₂ ha₁' k₁
  rcases h₂.isPreconnected_inter.subset_or_subset h₁.isOpen_U h₁.isOpen_V h₁.disjoint hτ₂ with
    k₂ | k₂
  · exact key h₁ h₂ hσ₁ hσ₂ hΩ₂ hc₂ hdisj ha₁ ha₂' k₂
  obtain ⟨w, hw⟩ := h₁.nonempty
  obtain ⟨u, huV₂, huU₁⟩ :=
    mem_closure_iff.1 (h₁.subset_closure hw) V₂ h₂.isOpen_V (k₁ hw)
  have hU₁D : U₁ ⊆ D := fun z hz => by
    have : z ∈ D \ σ₁ := by rw [h₁.diff_eq]; exact Or.inl hz
    exact this.1
  by_cases hm : (U₁ ∩ σ₂).Nonempty
  · obtain ⟨z, hz1, hz2⟩ := hm
    exact disjoint_left.1 h₁.disjoint hz1 (k₂ ⟨hz2, hU₁D hz1⟩)
  · have hsub : U₁ ⊆ U₂ ∪ V₂ := by
      rw [← h₂.diff_eq]
      intro z hz
      exact ⟨hU₁D hz, fun h => hm ⟨z, hz, h⟩⟩
    rcases h₁.isPreconnected_U.subset_or_subset h₂.isOpen_U h₂.isOpen_V h₂.disjoint hsub with
      k | k
    · exact disjoint_left.1 h₂.disjoint (k huU₁) huV₂
    · obtain ⟨z, hz1, hz2⟩ := hUU
      exact disjoint_left.1 h₂.disjoint hz2 (k hz1)

theorem zero_not_mem_of_mem_Gamma {σ Ω : Set ℂ} (hσ : σ ∈ Gamma Ω) (hD : Ω ⊆ disc \ {0}) :
    (0 : ℂ) ∉ σ := fun h0 => (hD (hσ.2 ⟨h0, zero_mem_disc⟩)).2 rfl

/-- `lem:mm-lemma3`: if `I₀(Ωᵢ) ∩ closure acc(Ωᵢ)`, `i = 1, 2`, have a common point, then
`Ω₁ ∩ Ω₂ ≠ ∅`. -/
theorem inter_nonempty {Ω₁ Ω₂ : Set ℂ} (hc₁ : IsPreconnected Ω₁) (hc₂ : IsPreconnected Ω₂)
    (hD₁ : Ω₁ ⊆ disc \ {0}) (hD₂ : Ω₂ ⊆ disc \ {0}) {a : ℂ}
    (ha₁ : a ∈ I0 Ω₁ ∩ closure (acc Ω₁)) (ha₂ : a ∈ I0 Ω₂ ∩ closure (acc Ω₂)) :
    (Ω₁ ∩ Ω₂).Nonempty := by
  obtain ⟨σ₁, hσ₁, ha₁σ⟩ := mem_iUnion₂.1 ha₁.1
  obtain ⟨σ₂, hσ₂, ha₂σ⟩ := mem_iUnion₂.1 ha₂.1
  obtain ⟨U₁, V₁, hs₁, h0U₁, he₁⟩ := exists_split hσ₁.1 (zero_not_mem_of_mem_Gamma hσ₁ hD₁)
  obtain ⟨U₂, V₂, hs₂, h0U₂, he₂⟩ := exists_split hσ₂.1 (zero_not_mem_of_mem_Gamma hσ₂ hD₂)
  rw [he₁] at ha₁σ
  rw [he₂] at ha₂σ
  exact inter_nonempty_of_split hs₁ hs₂ hσ₁.2 hσ₂.2 (fun z hz => (hD₁ hz).1)
    (fun z hz => (hD₂ hz).1) hc₁ hc₂ ⟨0, h0U₁, h0U₂⟩ ha₁σ.2 ha₂σ.2
    (closure_acc_subset _ ha₁.2) (closure_acc_subset _ ha₂.2)

/-! ### Infinite concatenation of paths -/

theorem Path.extend_mem_range {X : Type*} [TopologicalSpace X] {a b : X} (q : Path a b) (t : ℝ) :
    q.extend t ∈ range q :=
  ⟨projIcc 0 1 zero_le_one t, rfl⟩

/-- Paths `γₙ` from `zₙ` to `zₙ₊₁` that shrink to `y` concatenate to a path `g` from `z₀` to `y`
with `g(t) ∈ ⋃ γₙ` for `t < 1`, and `g(t) ∈ ⋃_{n ≥ N} γₙ` for `t` near `1`. -/
theorem exists_path_of_seq {X : Type*} [MetricSpace X] {y : X} {z : ℕ → X}
    (γ : ∀ n, Path (z n) (z (n + 1))) (hγ : ∀ ε > 0, ∀ᶠ n in atTop, range (γ n) ⊆ ball y ε) :
    ∃ g : Path (z 0) y, (∀ t : unitInterval, t ≠ 1 → ∃ n, g t ∈ range (γ n)) ∧
      ∀ N, ∀ᶠ t in 𝓝[<] (1 : ℝ), ∃ n ≥ N, g.extend t ∈ range (γ n) := by
  set h : ℝ → X := fun u => (γ ⌊u⌋₊).extend (u - ⌊u⌋₊) with hh
  have hfloor : ∀ u m, ⌊u⌋₊ = m → h u = (γ m).extend (u - m) := by
    rintro u m rfl; rfl
  have hmem : ∀ u, h u ∈ range (γ ⌊u⌋₊) := fun u => Path.extend_mem_range _ _
  have hpiece : ∀ (n : ℕ) (u : ℝ), (n : ℝ) ≤ u → u ≤ n + 1 → h u = (γ n).extend (u - n) := by
    intro n u h1 h2
    rcases h2.lt_or_eq with h2 | h2
    · exact hfloor u n ((Nat.floor_eq_iff (by linarith [n.cast_nonneg (α := ℝ)])).2 ⟨h1, h2⟩)
    · have hf : ⌊u⌋₊ = n + 1 := by rw [h2, ← Nat.cast_add_one, Nat.floor_natCast]
      rw [hfloor u (n + 1) hf, h2]
      push_cast
      rw [sub_self, Path.extend_zero, show (n : ℝ) + 1 - n = 1 by ring, Path.extend_one]
  have hlf : LocallyFinite (fun n : ℕ => Icc (n : ℝ) (n + 1)) := by
    intro u
    refine ⟨Ioo (u - 1) (u + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    refine (Set.finite_lt_nat (⌈u⌉₊ + 1)).subset ?_
    rintro n ⟨w, hw1, hw2⟩
    simp only [mem_ofPred_eq]
    have h1 : (n : ℝ) < u + 1 := by linarith [hw1.1, hw2.2]
    have h2 : (n : ℝ) < ⌈u⌉₊ + 1 := by linarith [Nat.le_ceil u]
    exact_mod_cast h2
  have hUnion : ⋃ n : ℕ, Icc (n : ℝ) (n + 1) = Ici 0 := by
    ext u
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨n, h1, -⟩; exact (n.cast_nonneg).trans h1
    · intro hu
      exact ⟨⌊u⌋₊, Nat.floor_le hu, (Nat.lt_floor_add_one u).le⟩
  have hcontOn : ContinuousOn h (Ici 0) := by
    have := hlf.continuousOn_iUnion (fun n => isClosed_Icc) fun n =>
      ((γ n).continuous_extend.comp (continuous_id.sub continuous_const)).continuousOn.congr
        fun u hu => hpiece n u hu.1 hu.2
    rwa [hUnion] at this
  have hcont : Continuous h := by
    refine continuous_iff_continuousAt.2 fun u => ?_
    rcases lt_or_ge u 1 with hu | hu
    · have : h =ᶠ[𝓝 u] (γ 0).extend := by
        filter_upwards [Iio_mem_nhds hu] with v hv
        rw [hfloor v 0 (Nat.floor_eq_zero.2 hv)]
        simp
      exact (γ 0).continuous_extend.continuousAt.congr this.symm
    · exact hcontOn.continuousAt (Ici_mem_nhds (by linarith))
  have htend : Tendsto h atTop (𝓝 y) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hγ ε hε)
    filter_upwards [eventually_ge_atTop (N : ℝ)] with u hu
    exact hN _ (Nat.le_floor hu) (hmem u)
  set φ : ℝ → ℝ := fun t => (1 - t)⁻¹ - 1 with hφdef
  have hφ : Tendsto φ (𝓝[<] 1) atTop := by
    have h2 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact sub_pos.2 (mem_Iio.1 ht)
    have := tendsto_atTop_add_const_right _ (-1) (tendsto_inv_nhdsGT_zero.comp h2)
    simpa [hφdef, sub_eq_add_neg] using this
  set G : ℝ → X := fun t => if t < 1 then h (φ t) else y with hGdef
  have hGlt : ∀ t, t < 1 → G t = h (φ t) := fun t ht => if_pos ht
  have hGge : ∀ t, 1 ≤ t → G t = y := fun t ht => if_neg (not_lt.2 ht)
  have hφc : ∀ t, t < 1 → ContinuousAt φ t := fun t ht =>
    ((continuous_const.sub continuous_id).continuousAt.inv₀ (by simp; linarith)).sub
      continuousAt_const
  have hGc : Continuous G := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    rcases lt_trichotomy t 1 with ht | rfl | ht
    · have : G =ᶠ[𝓝 t] h ∘ φ := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact hGlt s hs
      exact (hcont.continuousAt.comp (hφc t ht)).congr this.symm
    · rw [continuousAt_iff_continuous_left_right]
      constructor
      · rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hGge 1 le_rfl]
        refine (htend.comp hφ).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (hGlt s hs).symm
      · exact continuousWithinAt_const.congr (fun s hs => hGge s hs) (hGge 1 le_rfl)
    · have : G =ᶠ[𝓝 t] fun _ => y := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact hGge s hs.le
      exact continuousAt_const.congr this.symm
  have hG0 : G 0 = z 0 := by
    rw [hGlt 0 one_pos]
    simp [hφdef, hh]
  let g : Path (z 0) y := ⟨⟨fun t => G t, hGc.comp continuous_subtype_val⟩, hG0, hGge 1 le_rfl⟩
  have hgext : ∀ t ∈ Icc (0 : ℝ) 1, g.extend t = G t := fun t ht => by
    rw [g.extend_apply ht]; rfl
  refine ⟨g, fun t ht => ?_, fun N => ?_⟩
  · have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h' => ht (Subtype.ext h')
    show ∃ n, G t ∈ range (γ n)
    rw [hGlt _ ht1]
    exact ⟨_, hmem _⟩
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num),
      hφ.eventually (eventually_ge_atTop (N : ℝ))] with t ht hN
    rw [hgext t ⟨ht.1.le, ht.2.le⟩, hGlt t ht.2]
    exact ⟨_, Nat.le_floor hN, hmem _⟩

/-- A chain `Wₙ` as in the proof of `thm:mcmillan` yields an arc at `y` that is eventually in
`⋃_{n ≥ N} Wₙ` for every `N`. -/
theorem exists_arcAt_of_chain {W : ℕ → Set ℂ} (hWo : ∀ n, IsOpen (W n))
    (hWc : ∀ n, IsPreconnected (W n)) (hWD : ∀ n, W n ⊆ disc \ {0}) {y : ℂ}
    (hy : ∀ n, y ∈ I0 (W n) ∩ closure (acc (W n)))
    (hsmall : ∀ ε > 0, ∀ᶠ n in atTop, W n ⊆ ball y ε) :
    ∃ γ, IsArcAt disc y γ ∧ ∀ N, ∀ᶠ w in 𝓝[γ \ {y}] y, ∃ n ≥ N, w ∈ W n := by
  have hne : ∀ n, (W n ∩ W (n + 1)).Nonempty := fun n =>
    inter_nonempty (hWc n) (hWc (n + 1)) (hWD n) (hWD (n + 1)) (hy n) (hy (n + 1))
  choose z hz using hne
  have hj : ∀ n, JoinedIn (W (n + 1)) (z n) (z (n + 1)) := fun n =>
    ((hWo (n + 1)).isConnected_iff_isPathConnected.1 ⟨⟨z n, (hz n).2⟩, hWc (n + 1)⟩).joinedIn
      _ (hz n).2 _ (hz (n + 1)).1
  set γ := fun n => (hj n).somePath
  have hγW : ∀ n, range (γ n) ⊆ W (n + 1) := by
    rintro n _ ⟨t, rfl⟩; exact (hj n).somePath_mem t
  obtain ⟨g, hg1, hg2⟩ := exists_path_of_seq (y := y) γ fun ε hε => by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (hsmall ε hε)] with n hn
    exact (hγW n).trans hn
  have hyD : y ∉ disc := not_mem_disc_of_mem_circle (I0_subset_circle _ (hy 0).1)
  obtain ⟨β, -, hβ, hle⟩ := exists_arcAt_of_path (Ω := disc) g (fun t ht => by
    obtain ⟨n, hn⟩ := hg1 t ht
    exact (hWD _ (hγW n hn)).1) hyD
  refine ⟨β, hβ, fun N => hle (mem_map.2 ?_)⟩
  filter_upwards [hg2 N] with t ⟨n, hn, ht⟩
  exact ⟨n + 1, by omega, hγW n ht⟩

/-! ### The common skeleton of `thm:mcmillan` and `thm:mm-thm2` -/

/-- The components of an open set `O`, listed (with repetitions, or empty) by a dense sequence. -/
def comp (O : Set ℂ) (j : ℕ) : Set ℂ := connectedComponentIn O (denseSeq ℂ j)

theorem exists_comp {O S : Set ℂ} (hO : IsOpen O) (hS : IsPreconnected S) (hSO : S ⊆ O)
    (hne : S.Nonempty) : ∃ j, S ⊆ comp O j := by
  obtain ⟨s, hs⟩ := hne
  obtain ⟨j, hj⟩ := (denseRange_denseSeq ℂ).exists_mem_open hO.connectedComponentIn
    ⟨s, mem_connectedComponentIn (hSO hs)⟩
  refine ⟨j, ?_⟩
  rw [comp, ← connectedComponentIn_eq hj]
  exact hS.subset_connectedComponentIn hs hSO

theorem exists_mem_acc_comp {O : Set ℂ} (hO : IsOpen O) {x : ℂ} (hx : x ∈ circle) {γ : Set ℂ}
    (hγ : IsArcAt disc x γ) (hS : γ \ {x} ⊆ O) : ∃ j, x ∈ acc (comp O j) := by
  obtain ⟨b, harc, -⟩ := hγ
  obtain ⟨j, hj⟩ := exists_comp hO harc.isPreconnected_diff_left hS
    ⟨b, harc.right_mem, fun h => harc.ne (mem_singleton_iff.1 h).symm⟩
  exact ⟨j, hx, γ, b, harc, hj⟩

/-- The skeleton: for open `O n i ⊆ 𝔻 \ {0}`, a set `X` between
`Y = ⋂ₙ ⋃ᵢⱼ (I₀ ∩ closure acc)(comp (O n i) j)` and `⋂ₙ ⋃ᵢⱼ acc(comp (O n i) j)` is `F_σδ`:
`Y` is `F_σδ` and `X \ Y` is countable by `lem:mm-lemma2`. -/
theorem isFσδ_of_skeleton {ι : Type*} [Countable ι] (O : ℕ → ι → Set ℂ)
    (hO : ∀ n i, IsOpen (O n i)) (hOD : ∀ n i, O n i ⊆ disc \ {0}) {X : Set ℂ}
    (hYX : ∀ y, (∀ n, ∃ i j, y ∈ I0 (comp (O n i) j) ∩ closure (acc (comp (O n i) j))) → y ∈ X)
    (hXA : ∀ x ∈ X, ∀ n, ∃ i j, x ∈ acc (comp (O n i) j)) : IsFσδ X := by
  set Y := ⋂ n, ⋃ i, ⋃ j, (I0 (comp (O n i) j) ∩ closure (acc (comp (O n i) j)))
  have hY : IsFσδ Y :=
    ⟨_, fun n => IsFσ.iUnion fun i => IsFσ.iUnion fun j => isFσ_I0_inter _ _, rfl⟩
  have hYX' : Y ⊆ X := fun y hy => hYX y fun n => by
    obtain ⟨i, j, h⟩ := mem_iUnion₂.1 (mem_iInter.1 hy n)
    exact ⟨i, j, h⟩
  have hcount : (X \ Y).Countable := by
    refine (countable_iUnion fun n => countable_iUnion fun i => countable_iUnion fun j =>
      countable_acc_diff_I0 (Ω := comp (O n i) j) ?_ ?_ ?_).mono ?_
    · exact (hO n i).connectedComponentIn
    · exact isPreconnected_connectedComponentIn
    · exact (connectedComponentIn_subset _ _).trans (hOD n i)
    rintro x ⟨hx, hxY⟩
    obtain ⟨n, hn⟩ : ∃ n, x ∉ ⋃ i, ⋃ j, (I0 (comp (O n i) j) ∩ closure (acc (comp (O n i) j))) := by
      by_contra h
      push Not at h
      exact hxY (mem_iInter.2 h)
    obtain ⟨i, j, hij⟩ := hXA x hx n
    refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, hij, fun hI => hn ?_⟩⟩⟩
    exact mem_iUnion₂.2 ⟨i, j, hI, subset_closure hij⟩
  have : X = Y ∪ (X \ Y) := (union_sdiff_cancel hYX').symm
  rw [this]
  exact hY.union (IsFσ.isFσδ (TJK.Set.Countable.isFσ hcount))

/-- The sets `Q(n, m)`: small open pieces of `𝔻 \ {0}` centred at a dense sequence. -/
def Q (n m : ℕ) : Set ℂ := ball (denseSeq ℂ m) (1 / (n + 1)) ∩ (disc \ {0})

theorem isOpen_Q (n m : ℕ) : IsOpen (Q n m) :=
  isOpen_ball.inter (isOpen_ball.sdiff isClosed_singleton)

theorem Q_subset_disc (n m : ℕ) : Q n m ⊆ disc := fun _ hz => hz.2.1

/-- Every point of `C` has a neighbourhood `W` with `W ∩ 𝔻 ⊆ Q(n, m)` for some `m`. -/
theorem exists_Q_nhds {x : ℂ} (hx : x ∈ circle) (n : ℕ) :
    ∃ m, ∃ W ∈ 𝓝 x, W ∩ disc ⊆ Q n m := by
  have hpos : (0 : ℝ) < 1 / (2 * (n + 1)) := by positivity
  obtain ⟨m, hm⟩ := (denseRange_denseSeq ℂ).exists_dist_lt x hpos
  refine ⟨m, ball x (min (1 / (2 * (n + 1))) (1 / 2)), ball_mem_nhds _ (by positivity), ?_⟩
  rintro w ⟨hw, hwD⟩
  have hw1 := lt_of_lt_of_le (mem_ball.1 hw) (min_le_left _ _)
  have hw2 := lt_of_lt_of_le (mem_ball.1 hw) (min_le_right _ _)
  refine ⟨?_, hwD, ?_⟩
  · rw [mem_ball]
    calc dist w (denseSeq ℂ m) ≤ dist w x + dist x (denseSeq ℂ m) := dist_triangle _ _ _
      _ < 1 / (2 * (n + 1)) + 1 / (2 * (n + 1)) := add_lt_add hw1 hm
      _ = 1 / (n + 1) := by field_simp; ring
  · rintro rfl
    have : dist (0 : ℂ) x = 1 := by
      rw [dist_comm, dist_zero_right]; exact mem_sphere_zero_iff_norm.1 hx
    linarith

theorem eventually_two_div_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 2 / ((n : ℝ) + 1) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hN
  nlinarith

/-- Sets `Wₙ ⊆ Q(n, mₙ)` whose closures contain `y` shrink to `y`. -/
theorem eventually_subset_ball {W : ℕ → Set ℂ} {m : ℕ → ℕ} (hW : ∀ n, W n ⊆ Q n (m n)) {y : ℂ}
    (hy : ∀ n, y ∈ closure (W n)) : ∀ ε > 0, ∀ᶠ n in atTop, W n ⊆ ball y ε := by
  intro ε hε
  filter_upwards [eventually_two_div_lt hε] with n hn w hw
  have hyc : y ∈ closedBall (denseSeq ℂ (m n)) (1 / (n + 1)) :=
    closure_ball_subset_closedBall (closure_mono (fun z hz => (hW n hz).1) (hy n))
  have hwc := (hW n hw).1
  rw [mem_ball] at hwc ⊢
  rw [mem_closedBall] at hyc
  calc dist w y ≤ dist w (denseSeq ℂ (m n)) + dist y (denseSeq ℂ (m n)) := dist_triangle_right _ _ _
    _ < 1 / (n + 1) + 1 / (n + 1) := by linarith
    _ = 2 / (n + 1) := by ring
    _ < ε := hn

/-! ### McMillan's theorem (`thm:mcmillan`) -/

/-- **McMillan's theorem** (`thm:mcmillan`): for a continuous map of `𝔻` into a complete separable
metric space, the set of curvilinear convergence is `F_σδ`. -/
theorem isFσδ_curvConvSet' {K : Type*} [MetricSpace K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (f : ℂ → K) (hf : ContinuousOn f disc) :
    IsFσδ (curvConvSet disc circle f) := by
  have : Nonempty K := ⟨f 0⟩
  set p := denseSeq K
  set O : ℕ → ℕ × ℕ → Set ℂ := fun n i => Q n i.1 ∩ f ⁻¹' ball (p i.2) ((1 / 2) ^ n) with hOdef
  have hO : ∀ n i, IsOpen (O n i) := fun n i =>
    (hf.mono (Q_subset_disc n i.1)).isOpen_inter_preimage (isOpen_Q n i.1) isOpen_ball
  have hOD : ∀ n i, O n i ⊆ disc \ {0} := fun n i z hz => hz.1.2
  refine isFσδ_of_skeleton O hO hOD ?_ ?_
  · intro y hy
    choose i j hij using hy
    set W := fun n => comp (O n (i n)) (j n) with hWdef
    have hWO : ∀ n, W n ⊆ O n (i n) := fun n => connectedComponentIn_subset _ _
    have hWo : ∀ n, IsOpen (W n) := fun n => (hO n (i n)).connectedComponentIn
    have hWc : ∀ n, IsPreconnected (W n) := fun n => isPreconnected_connectedComponentIn
    have hWD : ∀ n, W n ⊆ disc \ {0} := fun n => (hWO n).trans (hOD n (i n))
    obtain ⟨γ, hγ, hev⟩ := exists_arcAt_of_chain hWo hWc hWD hij
      (eventually_subset_ball (m := fun n => (i n).1) (fun n => (hWO n).trans inter_subset_left)
        fun n => closure_acc_subset _ (hij n).2)
    -- the centres `p (i n).2` form a Cauchy sequence
    have hdist : ∀ n, dist (p (i n).2) (p (i (n + 1)).2) ≤ 4 / 2 / 2 ^ n := by
      intro n
      obtain ⟨w, hw1, hw2⟩ := inter_nonempty (hWc n) (hWc (n + 1)) (hWD n) (hWD (n + 1)) (hij n)
        (hij (n + 1))
      have e1 := mem_ball.1 (hWO n hw1).2
      have e2 := mem_ball.1 (hWO (n + 1) hw2).2
      have e3 : ((1 : ℝ) / 2) ^ (n + 1) ≤ (1 / 2) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
      have e4 : (4 : ℝ) / 2 / 2 ^ n = 2 * (1 / 2) ^ n := by rw [one_div_pow]; ring
      rw [e4]
      calc dist (p (i n).2) (p (i (n + 1)).2) ≤ dist (f w) (p (i n).2) + dist (f w) (p (i (n + 1)).2) :=
            dist_triangle_left _ _ _
        _ ≤ 2 * (1 / 2) ^ n := by linarith
    obtain ⟨P, hP⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hdist)
    refine ⟨I0_subset_circle _ (hij 0).1, γ, hγ, P, ?_⟩
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).eventually (gt_mem_nhds (half_pos hε))).and
        (hP.eventually (ball_mem_nhds P (half_pos hε))))
    filter_upwards [hev N] with w ⟨n, hn, hw⟩
    have e1 := mem_ball.1 (hWO n hw).2
    have e2 := (hN n hn).1
    have e3 := mem_ball.1 (hN n hn).2
    calc dist (f w) P ≤ dist (f w) (p (i n).2) + dist (p (i n).2) P := dist_triangle _ _ _
      _ < ε := by linarith
  · rintro x ⟨hxC, γ₀, hγ₀, q, hq⟩ n
    obtain ⟨k, hk⟩ := (denseRange_denseSeq K).exists_dist_lt q
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    obtain ⟨m, Wn, hWn, hWQ⟩ := exists_Q_nhds hxC n
    obtain ⟨γ', hγ'sub, hγ', hmaps⟩ :=
      hγ₀.tendsto_subarc hq (isOpen_ball.mem_nhds (mem_ball.2 hk)) hWn
    have hS : γ' \ {x} ⊆ O n (m, k) := by
      intro z hz
      obtain ⟨b, -, hΩ⟩ := hγ'
      exact ⟨hWQ ⟨(hγ'sub hz.1).2, hΩ hz⟩, hmaps hz⟩
    obtain ⟨j, hj⟩ := exists_mem_acc_comp (hO n (m, k)) hxC hγ' hS
    exact ⟨(m, k), j, hj⟩

/-! ### Cluster sets (`thm:mm-thm2`) -/

/-- If every cluster point of `f` along `F` lies in the open set `O` of a compact space, then
`f` is eventually in `O`. -/
theorem mem_map_of_forall_mapClusterPt {α Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    {F : Filter α} {f : α → Y} {O : Set Y} (hO : IsOpen O)
    (h : ∀ q, MapClusterPt q F f → q ∈ O) : O ∈ map f F := by
  by_contra hn
  have hne : (map f F ⊓ 𝓟 Oᶜ).NeBot := by
    rw [inf_principal_neBot_iff]
    intro U hU
    by_contra hU'
    exact hn (mem_of_superset hU fun z hz => by
      by_contra hzO
      exact hU' ⟨z, hz, hzO⟩)
  have := hne
  obtain ⟨q, hq, hcl⟩ := hO.isClosed_compl.isCompact.exists_clusterPt
    (f := map f F ⊓ 𝓟 Oᶜ) inf_le_right
  exact hq (h q (hcl.mono inf_le_left))

/-- **Theorem 2 of the Michigan paper** (`thm:mm-thm2`): for a closed family `ℰ` of nonempty
closed subsets of a compact metric space `K` and a continuous `f : 𝔻 → K`, the set of points of
`C` with an arc along which the cluster set is contained in a member of `ℰ` is `F_σδ`. -/
theorem isFσδ_clusterSet_subset' {K : Type*} [MetricSpace K] [CompactSpace K]
    (ℰ : Set (NonemptyCompacts K)) (hℰ : IsClosed ℰ) (f : ℂ → K)
    (hf : ContinuousOn f disc) :
    IsFσδ {x | x ∈ circle ∧ ∃ γ, IsArcAt disc x γ ∧ ∃ E ∈ ℰ, clusterSet f γ x ⊆ (E : Set K)} := by
  rcases ℰ.eq_empty_or_nonempty with rfl | hne
  · convert IsFσ.isFσδ (isFσ_empty (X := ℂ))
    ext x
    simp
  have : Nonempty ℰ := hne.to_subtype
  have hℰc : IsCompact ℰ := hℰ.isCompact
  set P : ℕ → NonemptyCompacts K := fun k => (denseSeq ℰ k : NonemptyCompacts K) with hPdef
  have hPℰ : ∀ k, P k ∈ ℰ := fun k => (denseSeq ℰ k).2
  have hPdense : ∀ E ∈ ℰ, ∀ ε > 0, ∃ k, dist E (P k) < ε := fun E hE ε hε => by
    obtain ⟨k, hk⟩ := (denseRange_denseSeq ℰ).exists_dist_lt ⟨E, hE⟩ hε
    exact ⟨k, hk⟩
  have hfin : ∀ A B : NonemptyCompacts K, hausdorffEDist (A : Set K) B ≠ ⊤ := fun A B =>
    edist_ne_top A B
  have hinf : ∀ (a : K) (A B : NonemptyCompacts K),
      infDist a (B : Set K) ≤ infDist a (A : Set K) + dist A B := fun a A B =>
    infDist_le_infDist_add_hausdorffDist (hfin A B)
  set O : ℕ → ℕ × ℕ → Set ℂ := fun n i =>
    Q n i.1 ∩ f ⁻¹' {a | infDist a (P i.2 : Set K) < 1 / (n + 1)} with hOdef
  have hO : ∀ n i, IsOpen (O n i) := fun n i =>
    (hf.mono (Q_subset_disc n i.1)).isOpen_inter_preimage (isOpen_Q n i.1)
      (isOpen_lt (continuous_infDist_pt _) continuous_const)
  have hOD : ∀ n i, O n i ⊆ disc \ {0} := fun n i z hz => hz.1.2
  refine isFσδ_of_skeleton O hO hOD ?_ ?_
  · intro y hy
    choose i j hij using hy
    set W := fun n => comp (O n (i n)) (j n) with hWdef
    have hWO : ∀ n, W n ⊆ O n (i n) := fun n => connectedComponentIn_subset _ _
    have hWo : ∀ n, IsOpen (W n) := fun n => (hO n (i n)).connectedComponentIn
    have hWc : ∀ n, IsPreconnected (W n) := fun n => isPreconnected_connectedComponentIn
    have hWD : ∀ n, W n ⊆ disc \ {0} := fun n => (hWO n).trans (hOD n (i n))
    have hsmall := eventually_subset_ball (m := fun n => (i n).1)
      (fun n => (hWO n).trans inter_subset_left) fun n => closure_acc_subset _ (hij n).2
    obtain ⟨E, hE, φ, hφ, hlim⟩ := hℰc.tendsto_subseq (x := fun n => P (i n).2)
      fun n => hPℰ _
    obtain ⟨γ, hγ, hev⟩ := exists_arcAt_of_chain (W := fun n => W (φ n)) (fun n => hWo _)
      (fun n => hWc _) (fun n => hWD _) (fun n => hij (φ n))
      fun ε hε => hφ.tendsto_atTop.eventually (hsmall ε hε)
    refine ⟨I0_subset_circle _ (hij 0).1, γ, hγ, E, hE, fun q hq => ?_⟩
    have hEc : IsClosed (E : Set K) := E.isCompact.isClosed
    rw [hEc.mem_iff_infDist_zero E.nonempty]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) infDist_nonneg
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (((hφ.tendsto_atTop.eventually (eventually_two_div_lt (half_pos hε)))).and
        (hlim.eventually (ball_mem_nhds E (half_pos hε))))
    have hmem : {a | infDist a (E : Set K) ≤ ε} ∈ map f (𝓝[γ \ {y}] y) := by
      refine mem_map.2 ?_
      filter_upwards [hev N] with w ⟨n, hn, hw⟩
      have e1 : infDist (f w) (P (i (φ n)).2 : Set K) < 1 / ((φ n : ℝ) + 1) := (hWO _ hw).2
      have e2 := (hN n hn).1
      have e3 := mem_ball.1 (hN n hn).2
      have e4 := hinf (f w) (P (i (φ n)).2) E
      have e5 : 1 / ((φ n : ℝ) + 1) ≤ 2 / ((φ n : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      show infDist (f w) (E : Set K) ≤ ε
      simp only [Function.comp] at e3
      linarith
    have := ClusterPt.mem_closure_of_mem hq _ hmem
    rw [(isClosed_le (continuous_infDist_pt _) continuous_const).closure_eq] at this
    simpa using this
  · rintro x ⟨hxC, γ₀, hγ₀, E, hE, hsub⟩ n
    obtain ⟨k, hk⟩ := hPdense E hE (1 / (n + 1)) (by positivity)
    have hEV : ∀ a ∈ (E : Set K), a ∈ {a | infDist a (P k : Set K) < 1 / (n + 1)} := by
      intro a ha
      have := hinf a E (P k)
      rw [infDist_zero_of_mem ha] at this
      show infDist a (P k : Set K) < 1 / (n + 1)
      linarith
    have hVmem := mem_map_of_forall_mapClusterPt (F := 𝓝[γ₀ \ {x}] x) (f := f)
      (isOpen_lt (continuous_infDist_pt _) continuous_const) fun q hq => hEV q (hsub hq)
    obtain ⟨m, Wn, hWn, hWQ⟩ := exists_Q_nhds hxC n
    obtain ⟨γ', hγ'sub, hγ', hmaps⟩ := hγ₀.tendsto_subarc tendsto_map hVmem hWn
    have hS : γ' \ {x} ⊆ O n (m, k) := by
      intro z hz
      obtain ⟨b, -, hΩ⟩ := hγ'
      exact ⟨hWQ ⟨(hγ'sub hz.1).2, hΩ hz⟩, hmaps hz⟩
    obtain ⟨j, hj⟩ := exists_mem_acc_comp (hO n (m, k)) hxC hγ' hS
    exact ⟨(m, k), j, hj⟩

/-! ### Corollaries (`cor:mm-corollaries`) -/

section Corollaries

variable {K : Type*} [MetricSpace K] [CompactSpace K]

/-- `cor:mm-corollaries` (1) (McMillan): the points with an arc along which `f` tends to a point
of a closed set `E` form an `F_σδ` set. -/
theorem cor1 (f : ℂ → K) (hf : ContinuousOn f disc) {E : Set K} (hE : IsClosed E) :
    IsFσδ {x | x ∈ circle ∧ ∃ γ, IsArcAt disc x γ ∧ ∃ p ∈ E, Tendsto f (𝓝[γ \ {x}] x) (𝓝 p)} := by
  set ℰ : Set (NonemptyCompacts K) := (fun p => ({p} : NonemptyCompacts K)) '' E
  have hℰ : IsClosed ℰ :=
    (hE.isCompact.image NonemptyCompacts.isometry_singleton.continuous).isClosed
  convert isFσδ_clusterSet_subset' ℰ hℰ f hf using 1
  ext x
  constructor
  · rintro ⟨hx, γ, hγ, p, hp, hlim⟩
    refine ⟨hx, γ, hγ, {p}, ⟨p, hp, rfl⟩, ?_⟩
    rw [(tendsto_iff_clusterSet_eq_singleton hγ f p).1 hlim, NonemptyCompacts.coe_singleton]
  · rintro ⟨hx, γ, hγ, _, ⟨p, hp, rfl⟩, hsub⟩
    refine ⟨hx, γ, hγ, p, hp, (tendsto_iff_clusterSet_eq_singleton hγ f p).2 ?_⟩
    rw [NonemptyCompacts.coe_singleton] at hsub
    exact (Set.Nonempty.subset_singleton_iff (clusterSet_nonempty hγ f)).1 hsub

/-- `cor:mm-corollaries` (2): the points with an arc along which the cluster set has diameter
`≤ d` form an `F_σδ` set. -/
theorem cor2 (f : ℂ → K) (hf : ContinuousOn f disc) {d : ℝ} (hd : 0 ≤ d) :
    IsFσδ {x | x ∈ circle ∧ ∃ γ, IsArcAt disc x γ ∧ diam (clusterSet f γ x) ≤ d} := by
  set ℰ : Set (NonemptyCompacts K) := {F | diam (F : Set K) ≤ d}
  have hℰ : IsClosed ℰ := by
    refine isClosed_of_closure_subset fun F hF => ?_
    refine diam_le_of_forall_dist_le hd fun x hx y hy => ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨F', hF', hFF'⟩ := Metric.mem_closure_iff.1 hF (ε / 2) (half_pos hε)
    obtain ⟨x', hx', hxx'⟩ := exists_dist_lt_of_hausdorffDist_lt hx hFF' (edist_ne_top F F')
    obtain ⟨y', hy', hyy'⟩ := exists_dist_lt_of_hausdorffDist_lt hy hFF' (edist_ne_top F F')
    have h1 := dist_le_diam_of_mem F'.isCompact.isBounded hx' hy'
    have h2 : diam (F' : Set K) ≤ d := hF'
    calc dist x y ≤ dist x x' + dist x' y' + dist y' y := dist_triangle4 _ _ _ _
      _ ≤ d + ε := by rw [dist_comm y' y]; linarith
  convert isFσδ_clusterSet_subset' ℰ hℰ f hf using 1
  ext x
  constructor
  · rintro ⟨hx, γ, hγ, hdiam⟩
    exact ⟨hx, γ, hγ, ⟨⟨_, isCompact_clusterSet f⟩, clusterSet_nonempty hγ f⟩, hdiam, le_rfl⟩
  · rintro ⟨hx, γ, hγ, E, hE, hsub⟩
    exact ⟨hx, γ, hγ, (diam_mono hsub E.isCompact.isBounded).trans hE⟩

/-- `cor:mm-corollaries` (3): the points with an arc along which the cluster set lies in a closed
set `E` form an `F_σδ` set. -/
theorem cor3 (f : ℂ → K) (hf : ContinuousOn f disc) {E : Set K} (hE : IsClosed E) :
    IsFσδ {x | x ∈ circle ∧ ∃ γ, IsArcAt disc x γ ∧ clusterSet f γ x ⊆ E} := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · convert IsFσ.isFσδ (isFσ_empty (X := ℂ))
    ext x
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨-, γ, hγ, h⟩
    exact (clusterSet_nonempty hγ f).ne_empty (subset_empty_iff.1 h)
  · set E' : NonemptyCompacts K := ⟨⟨E, hE.isCompact⟩, hne⟩
    convert isFσδ_clusterSet_subset' {E'} isClosed_singleton f hf using 1
    ext x
    constructor
    · rintro ⟨hx, γ, hγ, h⟩
      exact ⟨hx, γ, hγ, E', rfl, h⟩
    · rintro ⟨hx, γ, hγ, _, rfl, h⟩
      exact ⟨hx, γ, hγ, h⟩

end Corollaries

/-- The great circle of `S²` with unit normal `u`. -/
def greatCircle (u : Sphere2) : Set Sphere2 :=
  {v | inner ℝ (v : EuclideanSpace ℝ (Fin 3)) (u : EuclideanSpace ℝ (Fin 3)) = 0}

theorem isClosed_subset_greatCircle :
    IsClosed {F : NonemptyCompacts Sphere2 | ∃ u, (F : Set Sphere2) ⊆ greatCircle u} := by
  refine isClosed_of_closure_subset fun F hF => ?_
  obtain ⟨Fs, hFs, hlim⟩ := mem_closure_iff_seq_limit.1 hF
  choose u hu using hFs
  obtain ⟨u₀, -, φ, hφ, hlimu⟩ := isCompact_univ.tendsto_subseq (x := u) fun _ => mem_univ _
  refine ⟨u₀, fun v hv => ?_⟩
  have hd : Tendsto (fun n => dist F (Fs (φ n))) atTop (𝓝 0) := by
    have := (tendsto_iff_dist_tendsto_zero.1 (hlim.comp hφ.tendsto_atTop))
    simpa [dist_comm] using this
  have hex : ∀ n : ℕ, ∃ w ∈ (Fs (φ n) : Set Sphere2),
      dist v w < dist F (Fs (φ n)) + 1 / ((n : ℝ) + 1) := fun n =>
    exists_dist_lt_of_hausdorffDist_lt hv (lt_add_of_pos_right _ (by positivity))
      (edist_ne_top F (Fs (φ n)))
  choose w hw hwd using hex
  have hwlim : Tendsto w atTop (𝓝 v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun n : ℕ => dist F (Fs (φ n)) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using hd.add tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h0
    rw [dist_comm]; exact (hwd n).le
  have hc : Continuous fun p : Sphere2 × Sphere2 =>
      inner ℝ (p.1 : EuclideanSpace ℝ (Fin 3)) (p.2 : EuclideanSpace ℝ (Fin 3)) :=
    (continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)
  have hlim2 := (hc.tendsto (v, u₀)).comp (hwlim.prodMk_nhds hlimu)
  have hzero : ∀ n, inner ℝ ((w n : Sphere2) : EuclideanSpace ℝ (Fin 3))
      ((u (φ n) : Sphere2) : EuclideanSpace ℝ (Fin 3)) = 0 := fun n => hu (φ n) (hw n)
  exact tendsto_nhds_unique hlim2 (by simp [Function.comp_def, hzero])

/-- `cor:mm-corollaries` (4): the points with an arc along which the cluster set lies in a great
circle form an `F_σδ` set. Since the cluster set is closed and connected (`lem:cluster`), this
says that it is an arc of a great circle in the broad sense (a point, a closed arc, or the whole
circle). -/
theorem cor4 (f : ℂ → Sphere2) (hf : ContinuousOn f disc) :
    IsFσδ {x | x ∈ circle ∧ ∃ γ, IsArcAt disc x γ ∧ ∃ u, clusterSet f γ x ⊆ greatCircle u} := by
  convert isFσδ_clusterSet_subset' _ isClosed_subset_greatCircle f hf using 1
  ext x
  constructor
  · rintro ⟨hx, γ, hγ, u, hu⟩
    exact ⟨hx, γ, hγ, ⟨⟨_, isCompact_clusterSet f⟩, clusterSet_nonempty hγ f⟩, ⟨u, hu⟩, le_rfl⟩
  · rintro ⟨hx, γ, hγ, E, ⟨u, hu⟩, hsub⟩
    exact ⟨hx, γ, hγ, u, hsub.trans hu⟩

/-! ### McMillan's theorem in the half-plane (`thm:mcmillan-H`) -/

theorem curvConvSet_congr {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y] {Ω B : Set E}
    {f g : E → Y} (h : EqOn f g Ω) : curvConvSet Ω B f = curvConvSet Ω B g := by
  ext x
  refine and_congr_right fun _ => exists_congr fun γ => and_congr_right fun hγ =>
    exists_congr fun q => tendsto_congr' ?_
  obtain ⟨b, -, hΩ⟩ := hγ
  filter_upwards [self_mem_nhdsWithin] with z hz using h (hΩ hz)

/-- `thm:mcmillan-H` (dissertation Theorem 3): McMillan's theorem in the upper half-plane. -/
theorem isFσδ_curvConvSet_upperHalfPlane {K : Type*} [MetricSpace K] [CompleteSpace K]
    [SeparableSpace K] (f : ℂ → K) (hf : ContinuousOn f upper) :
    IsFσδ (curvConvSet upper realAxis f) := by
  set g : ℂ → K := f ∘ cayleyInv
  have hg : ContinuousOn g disc :=
    hf.comp (cayleyPH.continuousOn_symm.mono cayley_isChart.subset_target)
      fun w hw => cayleyInv_im_pos (mem_ball_zero_iff.1 hw)
  have hA := isFσδ_curvConvSet' g hg
  have h1 : curvConvSet upper realAxis f = curvConvSet upper realAxis (g ∘ cayleyPH) :=
    curvConvSet_congr fun z hz => by
      simp only [g, comp_apply, cayleyPH_apply, cayleyInv_cayley (le_of_lt hz)]
  rw [h1, transfer_curvConvSet cayley_isChart g]
  have h2 : realAxis ∩ cayleyPH ⁻¹' curvConvSet disc (circle \ {1}) g =
      Subtype.val '' ((fun z : realAxis => cayley z) ⁻¹' curvConvSet disc circle g) := by
    ext z
    constructor
    · rintro ⟨hz, hz1, hzc⟩
      exact ⟨⟨z, hz⟩, ⟨hz1.1, hzc⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, ⟨hz1, hzc⟩, rfl⟩
      exact ⟨hz, ⟨hz1, cayley_ne_one hz.ge⟩, hzc⟩
  rw [h2]
  refine IsFσδ.of_subtype (IsFσ.isFσδ (IsClosed.isFσ (isClosed_eq continuous_im
    continuous_const))) (hA.preimage ?_)
  exact (cayleyPH.continuousOn).comp_continuous continuous_subtype_val fun z =>
    show (0 : ℝ) ≤ (z : ℂ).im from z.2.ge

/-! ### The half-plane lemmas of the dissertation (`lem:th-lemma7`, `lem:th-lemma8`) -/

/-- `I(Ω)` for `Ω ⊆ ℍ`: the union of the open intervals `(c, d)` over the crosscuts of `ℍ` from
`c` to `d` (`c < d`) running through `Ω`. -/
def IH (Ω : Set ℂ) : Set ℂ :=
  {z | ∃ σ : Set ℂ, ∃ c d : ℝ, c < d ∧ IsArc σ c d ∧ σ \ {(c : ℂ), (d : ℂ)} ⊆ Ω ∧
    z ∈ ((↑) : ℝ → ℂ) '' Ioo c d}

/-- The points of `ℝ` accessible by an arc in `Ω`. -/
def accH (Ω : Set ℂ) : Set ℂ := {x | x ∈ realAxis ∧ ∃ γ, IsArcAt Ω x γ}

/-- The initial half of an arc whose interior lies in `Ω` is an arc at its first endpoint. -/
theorem IsArc.exists_arcAt {σ : Set ℂ} {a b : ℂ} (h : IsArc σ a b) {Ω : Set ℂ}
    (hΩ : σ \ {a, b} ⊆ Ω) : ∃ γ, IsArcAt Ω a γ := by
  obtain ⟨q, hq, rfl⟩ := id h
  refine ⟨_, _, IsArc.initial hq (δ := 1 / 2) (by norm_num) (by norm_num), ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, hne⟩
  apply hΩ
  rw [Path.range_diff_pair_eq hq]
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, by linarith [ht.2]⟩, rfl⟩
  rintro rfl
  exact hne (by rw [Path.extend_zero]; rfl)

/-- `lem:th-lemma7`: for a domain `Ω ⊆ ℍ`, `I(Ω)` is the open interval between the infimum and the
supremum of `acc(Ω)`. -/
theorem halfPlane_I_eq {Ω : Set ℂ} (ho : IsOpen Ω) (hc : IsPreconnected Ω) (x : ℝ) :
    (x : ℂ) ∈ IH Ω ↔
      (∃ c : ℝ, (c : ℂ) ∈ accH Ω ∧ c < x) ∧ ∃ d : ℝ, (d : ℂ) ∈ accH Ω ∧ x < d := by
  constructor
  · rintro ⟨σ, c, d, hcd, hσ, hσΩ, y, hy, hyx⟩
    have hyx' : y = x := ofReal_injective hyx
    subst hyx'
    refine ⟨⟨c, ⟨by simp, IsArc.exists_arcAt hσ hσΩ⟩, hy.1⟩, ⟨d, ⟨by simp, ?_⟩, hy.2⟩⟩
    exact IsArc.exists_arcAt hσ.symm (by rw [pair_comm]; exact hσΩ)
  · rintro ⟨⟨c, ⟨-, γ, hγ⟩, hcx⟩, ⟨d, ⟨-, γ', hγ'⟩, hxd⟩⟩
    have hΩne : Ω.Nonempty := by
      obtain ⟨b, harc, hΩ⟩ := hγ
      exact ⟨b, hΩ ⟨harc.right_mem, fun h => harc.ne (mem_singleton_iff.1 h).symm⟩⟩
    have hpc : IsPathConnected Ω := (ho.isConnected_iff_isPathConnected).1 ⟨hΩne, hc⟩
    have hne : (c : ℂ) ≠ d := fun h => (hcx.trans hxd).ne (ofReal_injective h)
    obtain ⟨σ, hσ, hσΩ⟩ := exists_arc_join hpc hne hγ hγ'
    exact ⟨σ, c, d, hcx.trans hxd, hσ, hσΩ, x, ⟨hcx, hxd⟩, rfl⟩

theorem accH_subset_closure (Ω : Set ℂ) : accH Ω ⊆ closure Ω := by
  rintro x ⟨-, γ, hγ⟩
  obtain ⟨b, -, hΩ⟩ := id hγ
  exact closure_mono hΩ (IsArcAt.mem_closure_diff hγ)

/-- `lem:th-lemma8`: for domains `Ω₁, Ω₂ ⊆ ℍ`, if `I(Ωᵢ) ∩ closure acc(Ωᵢ)` have a common point
then `Ω₁ ∩ Ω₂ ≠ ∅`. -/
theorem halfPlane_inter_nonempty {Ω₁ Ω₂ : Set ℂ} (hc₁ : IsPreconnected Ω₁)
    (hc₂ : IsPreconnected Ω₂) (hH₁ : Ω₁ ⊆ upper) (hH₂ : Ω₂ ⊆ upper) {a : ℂ}
    (ha₁ : a ∈ IH Ω₁ ∩ closure (accH Ω₁)) (ha₂ : a ∈ IH Ω₂ ∩ closure (accH Ω₂)) :
    (Ω₁ ∩ Ω₂).Nonempty := by
  have key : ∀ {Ω : Set ℂ}, Ω ⊆ upper → a ∈ IH Ω → ∃ σ U V : Set ℂ, Split upper σ U V ∧
      σ ∩ upper ⊆ Ω ∧ a ∉ closure U ∧ BddAbove (Complex.im '' σ) ∧
      ∀ z : ℂ, (∀ w ∈ σ, w.im < z.im) → z ∈ U := by
    intro Ω hH ha
    obtain ⟨σ, c, d, hcd, hσ, hσΩ, x, hx, rfl⟩ := ha
    obtain ⟨U, V, hU, hV, hcU, -, hd, heq, -, -, hclU, hσU, -, habove⟩ :=
      crosscutH_theorem hcd hσ (hσΩ.trans hH)
    have hinter : σ ∩ upper = σ \ {(c : ℂ), (d : ℂ)} := by
      ext z
      constructor
      · rintro ⟨hz, hzH⟩
        refine ⟨hz, ?_⟩
        rintro (rfl | rfl) <;> simp at hzH
      · intro hz; exact ⟨hz.1, hH (hσΩ hz)⟩
    refine ⟨σ, U, V, ⟨hU, hV, hcU.isPreconnected, hd, heq, hinter ▸ hσ.nonempty_diff_pair,
      hinter ▸ hσ.isPreconnected_diff_pair, fun z hz => hσU hz.1⟩, hinter ▸ hσΩ, ?_,
      hσ.isCompact.bddAbove_image continuous_im.continuousOn, habove⟩
    intro hcl
    have : (x : ℂ) ∈ closure U ∩ realAxis := ⟨hcl, ofReal_im x⟩
    rw [hclU] at this
    obtain ⟨y, hy, hyx⟩ := this
    rw [ofReal_injective hyx] at hy
    rcases hy with hy | hy
    · exact absurd hx.1 (not_lt.2 hy)
    · exact absurd hx.2 (not_lt.2 hy)
  obtain ⟨σ₁, U₁, V₁, hs₁, hσ₁, ha₁U, ⟨M₁, hM₁⟩, hab₁⟩ := key hH₁ ha₁.1
  obtain ⟨σ₂, U₂, V₂, hs₂, hσ₂, ha₂U, ⟨M₂, hM₂⟩, hab₂⟩ := key hH₂ ha₂.1
  set z : ℂ := ((max M₁ M₂ + 1 : ℝ) : ℂ) * I
  have hzim : z.im = max M₁ M₂ + 1 := by simp [z]
  have hzU : (U₁ ∩ U₂).Nonempty := by
    refine ⟨z, hab₁ z fun w hw => ?_, hab₂ z fun w hw => ?_⟩
    · have := hM₁ ⟨w, hw, rfl⟩; rw [hzim]; linarith [le_max_left M₁ M₂]
    · have := hM₂ ⟨w, hw, rfl⟩; rw [hzim]; linarith [le_max_right M₁ M₂]
  exact inter_nonempty_of_split hs₁ hs₂ hσ₁ hσ₂ hH₁ hH₂ hc₁ hc₂ hzU ha₁U ha₂U
    (closure_minimal (accH_subset_closure Ω₁) isClosed_closure ha₁.2)
    (closure_minimal (accH_subset_closure Ω₂) isClosed_closure ha₂.2)

end McMillan

end TJK
