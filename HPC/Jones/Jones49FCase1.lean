import HPC.Jones.Jones49FLocal

/-!
# Batch 154: Jones 1949 Theorem 1, Case 1 (item B)

* `frontier_cc_of_jordan` — step 2: a simple closed curve `J' ⊆ M` with `M − J'` connected is the
  boundary of a complementary domain of `M`.
* `exists_frontier_through` — steps 1–2: every point of `M` is on the boundary of an element of `G`.
* `countable_complDomains` — step 3: `G` is countable.
* `jones49_case1_core` — steps 4–5: Baire, and a point on an open arc of `M`.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore.Gen

/-- **Case 1, step 2 (the gap of §3.1 of the commission).** If `J' ⊆ M` is a simple closed curve and
`M ⊆ A ∪ J'` for a connected set `A` missing `J'`, then `J'` is the boundary of a complementary
domain of `M`: `A` lies on one side of `J'` (`jordan_side`); the other side `T` misses `M`, is
connected, and has frontier `J' ⊆ M`, so it is a component of `Mᶜ`. -/
theorem frontier_cc_of_jordan {M J' A : Set Pt} (hJ' : TSCC J') (hJM : J' ⊆ M)
    (hA : IsPreconnected A) (hAJ : Disjoint A J') (hMA : M ⊆ A ∪ J') :
    ∃ x' ∉ M, frontier (connectedComponentIn Mᶜ x') = J' := by
  obtain ⟨S, T, hSo, hSc, hTo, hTc, hST, hU, hfS, hfT, hAS⟩ := jordan_side hJ' hA hAJ
  have hJne : J'.Nonempty := by
    obtain ⟨a, b, C₁, C₂, h₁, -, -, rfl⟩ := hJ'; exact ⟨a, Or.inl h₁.left_mem⟩
  obtain ⟨j, hj⟩ := hJne
  obtain ⟨x', hx'⟩ := nonempty_of_frontier (hfT ▸ hj : j ∈ frontier T)
  have hTJ := disjoint_frontier_of_isOpen hTo hfT
  have hTM : ∀ z ∈ T, z ∉ M := fun z hz hzM => by
    rcases hMA hzM with h | h
    · exact disjoint_left.mp hST (hAS h) hz
    · exact disjoint_left.mp hTJ hz h
  refine ⟨x', hTM x' hx', ?_⟩
  have : connectedComponentIn Mᶜ x' = T :=
    subset_antisymm (cc_sub_of_frontier (hfT ▸ hJM) hx')
      (hTc.subset_connectedComponentIn hx' hTM)
  rw [this, hfT]

/-- **Case 1, steps 1–2.** If `J`, the boundary of a complementary domain of the homogeneous `M`, is
a simple closed curve with `M − J` connected, every point `p` of `M` lies on the boundary of a
complementary domain: a homeomorphism `h` of `M` carrying a point of `J` to `p` gives the simple
closed curve `J' = h(J) ∋ p` with `M − J' = h(M − J)` connected, and `frontier_cc_of_jordan`
applies. -/
theorem exists_frontier_through {M : Set Pt} (hX : IsHomogeneous M) {J : Set Pt} (hJ : TSCC J)
    (hJM : J ⊆ M) (h1 : IsConnected ((Subtype.val ⁻¹' J)ᶜ : Set M)) (p : M) :
    ∃ x' ∉ M, (p : Pt) ∈ frontier (connectedComponentIn Mᶜ x') := by
  obtain ⟨e⟩ := tscc_homeomorph_circle hJ
  have hJne : J.Nonempty := by
    obtain ⟨a, b, C₁, C₂, h₁, -, -, rfl⟩ := hJ; exact ⟨a, Or.inl h₁.left_mem⟩
  obtain ⟨q₀, hq₀⟩ := hJne
  obtain ⟨h, hh⟩ := hX ⟨q₀, hJM hq₀⟩ p
  set g : J → Pt := fun z => (h (Set.inclusion hJM z) : Pt) with hgdef
  have hg : IsEmbedding g :=
    IsEmbedding.subtypeVal.comp (h.isEmbedding.comp (IsEmbedding.inclusion hJM))
  have hTJ : TSCC (univ : Set J) := by
    have := tscc_image_embedding e.symm.isEmbedding tscc_circle
    rwa [image_univ, e.symm.range_coe] at this
  have hJ' : TSCC (range g) := by
    have := tscc_image_embedding hg hTJ; rwa [image_univ] at this
  set S : Set M := (Subtype.val ⁻¹' J)ᶜ
  set A : Set Pt := Subtype.val '' (h '' S)
  have hA : IsPreconnected A :=
    (h1.isPreconnected.image _ h.continuous.continuousOn).image _
      continuous_subtype_val.continuousOn
  have hAJ : Disjoint A (range g) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩ ⟨j, hj⟩
    have e2 := h.injective (Subtype.ext hj : h (Set.inclusion hJM j) = h s)
    apply hs
    show (s : Pt) ∈ J
    rw [← e2]; exact j.2
  have hMA : M ⊆ A ∪ range g := by
    intro z hz
    set m := h.symm ⟨z, hz⟩
    by_cases hm : (m : Pt) ∈ J
    · right
      refine ⟨⟨m, hm⟩, ?_⟩
      show (h (Set.inclusion hJM ⟨m, hm⟩) : Pt) = z
      have : Set.inclusion hJM ⟨(m : Pt), hm⟩ = m := Subtype.ext rfl
      rw [this, Homeomorph.apply_symm_apply]
    · left
      exact ⟨h m, ⟨m, hm, rfl⟩, by rw [Homeomorph.apply_symm_apply]⟩
  have hgM : range g ⊆ M := by rintro _ ⟨j, rfl⟩; exact (h _).2
  obtain ⟨x', hx', hfx'⟩ := frontier_cc_of_jordan hJ' hgM hA hAJ hMA
  refine ⟨x', hx', hfx' ▸ ⟨⟨q₀, hq₀⟩, ?_⟩⟩
  show (h (Set.inclusion hJM ⟨q₀, hq₀⟩) : Pt) = p
  rw [← hh]

/-- **Case 1, step 3: `G` is countable** (its elements are disjoint nonempty open subsets of the
plane). -/
theorem countable_complDomains {M : Set Pt} (hM : IsClosed M) :
    {U : Set Pt | ∃ x ∉ M, connectedComponentIn Mᶜ x = U}.Countable := by
  refine Set.PairwiseDisjoint.countable_of_isOpen (s := id) ?_ ?_ ?_
  · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hne
    refine disjoint_left.mpr fun z hzx hzy => hne ?_
    simp only [id] at hzx hzy ⊢
    rw [connectedComponentIn_eq hzx, connectedComponentIn_eq hzy]
  · rintro _ ⟨x, -, rfl⟩
    exact hM.isOpen_compl.connectedComponentIn
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_connectedComponentIn hx⟩

/-- **Case 1 of Jones 1949** (`M − J` connected, no point of order 2: a contradiction). By
`exists_frontier_through`, `M` is the union of the boundaries of the elements of `G`, countably many
closed sets (`countable_complDomains`); by Baire one of them, a simple closed curve
(`whyburn39_corollary1`), contains a nonempty open set of `M`; a point of it is a local separating
point (`isLocalSepPoint_of_open_sub_tscc`), so some point has order 2
(`jones49_some_order_two`). -/
theorem jones49_case1_core {M : Set Pt} [CompactSpace M] [ConnectedSpace M] [Nontrivial M]
    (hX : IsHomogeneous M) (hS : ∀ z : M, SemiLocConnAt z)
    (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) (hno : ∀ q : M, ¬ HasOrder q 2) {x : Pt}
    (hx : x ∉ M)
    (h1 : IsConnected ((Subtype.val ⁻¹' frontier (connectedComponentIn Mᶜ x))ᶜ : Set M)) :
    False := by
  have hMk : IsCompact M := isCompact_iff_compactSpace.mpr ‹_›
  have hMc : IsConnected M := isConnected_iff_connectedSpace.mpr ‹_›
  have hcirc : ∀ x' ∉ M, TSCC (frontier (connectedComponentIn Mᶜ x')) := fun x' hx' =>
    tscc_of_homeomorph_circle (whyburn39_corollary1 hMk hMc hS hcyc hx')
  set 𝒢 := {U : Set Pt | ∃ x ∉ M, connectedComponentIn Mᶜ x = U}
  haveI : Countable 𝒢 := (countable_complDomains hMk.isClosed).to_subtype
  set f : 𝒢 → Set M := fun U => Subtype.val ⁻¹' frontier (U : Set Pt)
  have hfc : ∀ U, IsClosed (f U) := fun U => isClosed_frontier.preimage continuous_subtype_val
  have hfU : ⋃ U, f U = univ := by
    refine eq_univ_of_forall fun p => ?_
    obtain ⟨x', hx', hp⟩ := exists_frontier_through hX (hcirc x hx)
      (HPC.Moore.Gen.frontier_connectedComponentIn_subset hMk.isClosed x) h1 p
    exact mem_iUnion.mpr ⟨⟨_, x', hx', rfl⟩, hp⟩
  obtain ⟨⟨U, x', hx', rfl⟩, p, hp⟩ := nonempty_interior_of_iUnion_of_closed hfc hfU
  haveI := uncountable_of_nontrivial (M := M)
  obtain ⟨q, hq⟩ := jones49_some_order_two hX (isLocalSepPoint_of_open_sub_tscc (hcirc x' hx')
    (HPC.Moore.Gen.frontier_connectedComponentIn_subset hMk.isClosed x') isOpen_interior hp
    fun z hz => by have := interior_subset hz; exact this)
  exact hno q hq

end HPC.Jones
