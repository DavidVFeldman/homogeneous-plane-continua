import HPC.Hagopian.H84Delta

/-!
# Batch 186, §4.2–§4.3: Lemmas 14 and 15 of Hagopian 1984

* `delta_regular_rep`: a member of `Δ(𝒫)` is an interior layer of the map given by regularity.
* `delta_translate_eq`: if `h` moves points less than the distance `η` from `⋃Δ(𝒫)` to
  `M ∖ ⋃𝒫′`, and `h[Z]` meets `Z'` (both in `Δ(𝒫)`), then `h[Z] = Z'` (Lemma 3, with its three
  hypotheses checked through `η`).
* `hagopian84_lemma14_aux`: Lemma 14 (Hausdorff continuity of `Δ(𝒫)`).
* `hagopian84_lemma15_aux`: Lemma 15, with the smaller `ε` of commission 186 §4.3.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Lemma1415

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- The end layers of a continuum running straight through a chain miss `⋃𝒫′`. -/
theorem endlayers_not_mid {G : Set M} {d : G → unitInterval} {P : Fin 5 → Set M}
    (hP : IsChain5 P) (hrs : RunsStraight d P) {v : M} (hv : v ∈ layer d 0 ∪ layer d 1) :
    v ∉ midUnion P := by
  intro hm
  rcases hv with hv | hv
  · obtain ⟨h0, h1⟩ := hrs.2.1 hv
    rcases hm with (h | h) | h
    · exact h1 h
    · exact disjoint_left.1 (chain5_disjoint hP 0 2 (by decide)) h0 h
    · exact disjoint_left.1 (chain5_disjoint hP 0 3 (by decide)) h0 h
  · obtain ⟨h4, h3⟩ := hrs.2.2.1 hv
    rcases hm with (h | h) | h
    · exact disjoint_left.1 (chain5_disjoint hP 1 4 (by decide)) h h4
    · exact disjoint_left.1 (chain5_disjoint hP 2 4 (by decide)) h h4
    · exact h3 h

omit [CompactSpace M] [ConnectedSpace M] in
/-- A member of `Δ(𝒫)` is an interior layer of the map given by regularity. -/
theorem delta_regular_rep {P : Fin 5 → Set M} (hr : IsRegular5 P) {Z : Set M}
    (hZ : Z ∈ Delta5 P) :
    ∃ x ∈ midUnion P, ∃ d : closure (connectedComponentIn (midUnion P) x) → unitInterval,
      IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) d ∧ RunsStraight d P ∧
        ∃ s, 0 < s ∧ s < 1 ∧ Z = layer d s := by
  obtain ⟨⟨x, hx, d₀, hd₀, t, rfl⟩, hZd⟩ := hZ
  obtain ⟨d, hd, hrs⟩ := hr x hx
  obtain ⟨s, hs⟩ := exists_layer_eq_of_minimal hd₀ hd t
  obtain ⟨z, hz⟩ := layer_nonempty' hd.2.1 s
  have hzZ : z ∈ layer d₀ t := hs ▸ hz
  refine ⟨x, hx, d, hd, hrs, s, ?_, ?_, hs⟩
  · refine lt_of_le_of_ne unitInterval.nonneg' fun h => ?_
    rw [← h] at hz
    exact disjoint_left.1 hZd hzZ (subset_closure (Or.inl (hrs.2.1 hz).1))
  · refine lt_of_le_of_ne unitInterval.le_one' fun h => ?_
    rw [h] at hz
    exact disjoint_left.1 hZd hzZ (subset_closure (Or.inr (hrs.2.2.1 hz).1))

/-- **Translates inside `Δ(𝒫)`** (the use of Lemma 3 in Lemmas 14 and 15, with its hypotheses
checked): `η` bounds the distance from `⋃Δ(𝒫)` to `M ∖ ⋃𝒫′`; `h` moves points less than `η`;
`h[Z]` meets `Z'`. Then `h[Z] = Z'`. -/
theorem delta_translate_eq (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hr : IsRegular5 P) {η : ℝ}
    (hηd : ∀ z ∈ ⋃₀ Delta5 P, ∀ y : M, y ∉ midUnion P → η ≤ dist z y)
    {Z Z' : Set M} (hZ : Z ∈ Delta5 P) (hZ' : Z' ∈ Delta5 P) (h : M ≃ₜ M)
    (hh : ∀ v, dist v (h v) < η) (hmeet : (Z' ∩ h '' Z).Nonempty) : h '' Z = Z' := by
  obtain ⟨x, hx, d, hd, hrs, s, hs0, hs1, rfl⟩ := delta_regular_rep hr hZ
  obtain ⟨x', hx', d', hd', hrs', u, -, -, rfl⟩ := delta_regular_rep hr hZ'
  refine hagopian76_lemma3 hX hi hd hd' hs0 hs1 h hmeet ?_ ?_
  · rw [disjoint_left]
    rintro w hw ⟨v, hv, rfl⟩
    have := hηd (h v) ⟨_, hZ', hw⟩ v (endlayers_not_mid hP hrs hv)
    rw [dist_comm] at this
    exact absurd (hh v) (not_lt.2 this)
  · rw [disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hwe
    have := hηd w ⟨_, hZ, hw⟩ (h w) (endlayers_not_mid hP hrs' hwe)
    exact absurd (hh w) (not_lt.2 this)

/-- **Lemma 14** (p. 341): the decomposition `Δ(𝒫)` is continuous (Hausdorff form). -/
theorem hagopian84_lemma14_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hf : IsFree5 P) (hr : IsRegular5 P) :
    ∀ Z ∈ Delta5 P, ∀ z ∈ Z, ∀ ε > 0, ∃ δ > 0, ∀ Z' ∈ Delta5 P, ∀ z' ∈ Z', dist z z' < δ →
      Z ⊆ thickening ε Z' ∧ Z' ⊆ thickening ε Z := by
  obtain ⟨η, hη, hηd⟩ := delta5_dist_pos_aux hP.isOpen hf hr
  intro Z hZ z hz ε hε
  have hε' : 0 < min ε η := lt_min hε hη
  have hzW : z ∈ Wset84 z (min ε η) := ⟨Homeomorph.refl M, fun v => by simpa using hε', rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hagopian84_lemma1 hX z (min ε η)) z hzW
  refine ⟨δ, hδ, fun Z' hZ' z' hz' hzz' => ?_⟩
  obtain ⟨h, hh, hhz⟩ := hball (by rw [mem_ball, dist_comm]; exact hzz')
  have hhε : ∀ v, dist v (h v) < ε := fun v => (hh v).trans_le (min_le_left _ _)
  have key : h '' Z = Z' := delta_translate_eq hX hi hP hr hηd hZ hZ' h
    (fun v => (hh v).trans_le (min_le_right _ _)) ⟨z', hz', z, hz, hhz⟩
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [mem_thickening_iff]
    exact ⟨h w, key ▸ mem_image_of_mem h hw, hhε w⟩
  · rw [← key] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [mem_thickening_iff]
    exact ⟨v, hv, by rw [dist_comm]; exact hhε v⟩

omit [ConnectedSpace M] in
/-- A positive `ρ` such that points within `ρ` of `Cl P i` miss `Cl P j` (`j` far from `i`). -/
theorem exists_far_links {P : Fin 5 → Set M} (hn : IsNormal5 P) (i : Fin 5) (S : Set (Fin 5))
    (hS : ∀ j ∈ S, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) :
    ∃ ρ > 0, ∀ p q : M, p ∈ closure (P i) → dist p q < ρ → ∀ j ∈ S, q ∉ closure (P j) := by
  have hO : IsOpen (⋃ j ∈ S, closure (P j))ᶜ :=
    (isClosed_biUnion_finset (s := S.toFinite.toFinset) (fun j _ => isClosed_closure) |>.isOpen_compl
      |> fun h => by simpa using h)
  have hsub : closure (P i) ⊆ (⋃ j ∈ S, closure (P j))ᶜ := by
    intro p hp hpS
    obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.1 hpS
    rcases hS j hj with h | h
    · exact disjoint_left.1 (hn i j h) hp hpj
    · exact disjoint_left.1 (hn j i h) hpj hp
  obtain ⟨ρ, hρ, hth⟩ := isClosed_closure.isCompact.exists_thickening_subset_open hO hsub
  refine ⟨ρ, hρ, fun p q hp hpq j hj hq => ?_⟩
  have : q ∈ thickening ρ (closure (P i)) :=
    mem_thickening_iff.2 ⟨p, hp, by rw [dist_comm]; exact hpq⟩
  exact hth this (mem_iUnion₂.2 ⟨j, hj, hq⟩)

/-- **Lemma 15** (p. 341), with `ε` smaller than Hagopian's (commission 186 §4.3): less than the
distance `η` from `⋃Δ(𝒫)` to `M ∖ ⋃𝒫′`, and less than the distances from `Cl P 0` to
`Cl P 2 ∪ Cl P 3 ∪ Cl P 4` and from `Cl P 4` to `Cl P 0 ∪ Cl P 1 ∪ Cl P 2`. -/
theorem hagopian84_lemma15_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P)
    (hr : IsRegular5 P) :
    ∃ ε > 0, ∀ Z ∈ Delta5 P, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε) → h '' Z ∈ Omega5 P := by
  obtain ⟨η, hη, hηd⟩ := delta5_dist_pos_aux hP.isOpen hf hr
  obtain ⟨ρ₀, hρ₀, hfar₀⟩ := exists_far_links hn 0 {2, 3, 4} (by decide)
  obtain ⟨ρ₄, hρ₄, hfar₄⟩ := exists_far_links hn 4 {0, 1, 2} (by decide)
  refine ⟨min η (min ρ₀ ρ₄), lt_min hη (lt_min hρ₀ hρ₄), fun Z hZ h hh => ?_⟩
  have hhη : ∀ v, dist v (h v) < η := fun v => (hh v).trans_le (min_le_left _ _)
  have hh₀ : ∀ v, dist v (h v) < ρ₀ :=
    fun v => (hh v).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hh₄ : ∀ v, dist v (h v) < ρ₄ :=
    fun v => (hh v).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hZΔ := hZ
  obtain ⟨x, hx, d, hd, hrs, s, hs0, hs1, rfl⟩ := delta_regular_rep hr hZ
  -- `h[Z] ⊆ ⋃𝒫′`
  have hmid : ∀ w ∈ layer d s, h w ∈ midUnion P := by
    intro w hw
    by_contra hc
    exact absurd (hhη w) (not_lt.2 (hηd w ⟨_, hZΔ, hw⟩ (h w) hc))
  obtain ⟨z, hz⟩ := layer_nonempty' hd.2.1 s
  set x' := h z with hx'
  have hx'm : x' ∈ midUnion P := hmid z hz
  obtain ⟨d', hd', hrs'⟩ := hr x' hx'm
  have hhZK : h '' layer d s ⊆ (closure (connectedComponentIn (midUnion P) x')) := by
    refine subset_closure.trans' ?_
    exact ((layer_isPreconnected' hd.2.1 s).image _ h.continuous.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem h hz) (by rintro _ ⟨w, hw, rfl⟩; exact hmid w hw)
  -- the image map of `h[(closure (connectedComponentIn (midUnion P) x))]`
  obtain ⟨b, hb, hlay⟩ := exists_image_map h hd
  have hlb : ∀ r, layer b r = h '' layer d r := fun r => by simpa [layerSet, layer] using hlay {r}
  have hxs : x' ∈ layer b s := by rw [hlb]; exact mem_image_of_mem h hz
  -- `h[(closure (connectedComponentIn (midUnion P) x))] ∩ (closure (connectedComponentIn (midUnion P) x'))` meets two layers of `h[(closure (connectedComponentIn (midUnion P) x))]`
  have h2 : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((h '' (closure (connectedComponentIn (midUnion P) x)) ∩ (closure (connectedComponentIn (midUnion P) x'))) ∩ layer b t₁).Nonempty ∧
      ((h '' (closure (connectedComponentIn (midUnion P) x)) ∩ (closure (connectedComponentIn (midUnion P) x'))) ∩ layer b t₂).Nonempty := by
    by_contra hno
    push_neg at hno
    have hsub : (closure (connectedComponentIn (midUnion P) x')) ∩ h '' (closure (connectedComponentIn (midUnion P) x)) ⊆ layer b s := by
      rintro p ⟨hpG', hpG⟩
      have hpl : p ∈ layer b (b ⟨p, hpG⟩) := mem_layer_self84 b ⟨p, hpG⟩
      by_contra hps
      have hne : b ⟨p, hpG⟩ ≠ s := fun he => hps (he ▸ hpl)
      have := hno (b ⟨p, hpG⟩) s hne ⟨p, ⟨hpG, hpG'⟩, hpl⟩
      exact (not_nonempty_iff_eq_empty.2 this) ⟨x', ⟨layer_subset_set b s hxs, hhZK (hlb s ▸ hxs)⟩, hxs⟩
    obtain ⟨v, hv⟩ := layer_nonempty' hd'.2.1 0
    have hG'c : Fold.Q78.IsContinuum (closure (connectedComponentIn (midUnion P) x')) := hd'.1.choose_spec.choose_spec.1
    refine no_arm_at_interior_layer hX hi hb hs0 hs1 hG'c hsub
      ⟨x', hhZK (hlb s ▸ hxs), layer_subset_set b s hxs⟩ fun hY => ?_
    have hvY := hY (layer_subset_set d' 0 hv)
    rw [hlb] at hvY
    obtain ⟨w, hw, hwv⟩ := hvY
    exact endlayers_not_mid hP hrs' (Or.inl hv) (hwv ▸ hmid w hw)
  rcases layers_agree hX hi hb hd' h2 with ⟨v, hv⟩ | ⟨-, hag, -⟩
  · -- degenerate case: `h[G]` inside one layer of `G′`
    exfalso
    obtain ⟨p₀, hp₀⟩ := layer_nonempty' hd.2.1 0
    obtain ⟨p₁, hp₁⟩ := layer_nonempty' hd.2.1 1
    have hq₀ : h p₀ ∈ layer d' v := hv (mem_image_of_mem h (layer_subset_set d 0 hp₀))
    have hq₁ : h p₁ ∈ layer d' v := hv (mem_image_of_mem h (layer_subset_set d 1 hp₁))
    have hP₀ : p₀ ∈ closure (P 0) := subset_closure (hrs.2.1 hp₀).1
    have hP₄ : p₁ ∈ closure (P 4) := subset_closure (hrs.2.2.1 hp₁).1
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hrs'.1 (layer_subset_set d' v hq₀))
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hrs'.1 (layer_subset_set d' v hq₁))
    have hi01 : (i : ℕ) ≤ 1 := by
      by_contra hc
      exact hfar₀ p₀ (h p₀) hP₀ (hh₀ p₀) i (show i = 2 ∨ i = 3 ∨ i = 4 by revert hc; fin_cases i <;> decide) (subset_closure hi)
    have hj34 : 3 ≤ (j : ℕ) := by
      by_contra hc
      exact hfar₄ p₁ (h p₁) hP₄ (hh₄ p₁) j (show j = 0 ∨ j = 1 ∨ j = 2 by revert hc; fin_cases j <;> decide) (subset_closure hj)
    have hsi := layer_subset_link hd'.2.1 hP.isOpen hrs' ⟨_, hq₀, hi⟩
    have hsj := layer_subset_link hd'.2.1 hP.isOpen hrs' ⟨_, hq₁, hj⟩
    exact disjoint_left.1 (chain5_disjoint hP i j (by omega)) (hsi hq₀) (hsj hq₀)
  · obtain ⟨u, hu⟩ := hag s ⟨x', hhZK (hlb s ▸ hxs), hxs⟩
    exact ⟨x', hx'm, d', hd', u, by rw [← hlb, hu]⟩

end Lemma1415

end HPC.Hagopian
