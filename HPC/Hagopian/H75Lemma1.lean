import HPC.Hagopian.H75Composants
import HPC.Hagopian.H75Sep
import HPC.Jones.Jones55T2A
import HPC.Plane.Atriodic51Defs
import HPC.Hagopian.H75Triod

/-!
# Batch 155, item D (second paragraph): a homogeneous indecomposable plane continuum is hereditarily
unicoherent

Hagopian 1975, Lemma 1, second paragraph. Suppose the proper subcontinuum `F = H ∪ L` of `M` is not
unicoherent. Then:

1. `F` separates the plane (`separatesPlane_of_not_isPreconnected_inter`, Moore 22).
2. Each composant `κ` contains a homeomorphic copy `F_κ` of `F` (homogeneity), and copies in different
   composants are disjoint.
3. **The "separable" step.** If every `F_κ` had a complementary domain `U_κ` missing `M`, the `U_κ`
   would be pairwise disjoint (`disjoint_components_missing`: if `U_κ` met `U_κ'`, each would lie in
   the other, as each misses the other's `F`; then `frontier U_κ ⊆ F_κ ∩ F_κ' = ∅`, and the plane is
   connected). Uncountably many disjoint nonempty open sets contradict separability
   (`countable_of_pairwiseDisjoint_open`). So some `F_κ` has all its complementary domains meeting
   `M`, and, separating the plane, it has two, `U` and `V`.
4. **The density step.** `κ` is meagre (Moore 136–137), so `U ∩ M` has a point `p ∉ κ` (Baire). The
   composant of `p` is dense (Moore 135), so it has a point `q ∈ V`; a proper subcontinuum `L ∋ p, q`
   meets `F_κ` (it joins two complementary domains of `F_κ`), so `L ∪ F_κ` is a proper subcontinuum
   (Moore 138's argument) and `p ∈ κ`.

Hagopian's text gives neither the disjointness of the domains (step 3) nor steps 4's Baire and
Moore 138 arguments.
-/

namespace HPC.Hagopian

open Set Topology HPC.Plane HPC.Jones HPC.Moore

/-- **Disjoint complementary domains.** Let `F₁`, `F₂` be disjoint subsets of `M` (`F₁` closed and
nonempty, `F₂` closed), and let `U₁`, `U₂` be components of `F₁ᶜ`, `F₂ᶜ` that miss `M`. Then
`U₁ ∩ U₂ = ∅`. -/
theorem disjoint_components_missing {M F₁ F₂ : Set Pt} (hF₁ : IsClosed F₁) (hF₂ : IsClosed F₂)
    (hF₁ne : F₁.Nonempty) (hF₁M : F₁ ⊆ M) (hF₂M : F₂ ⊆ M) (hd : Disjoint F₁ F₂) {p₁ p₂ : Pt}
    (hU₁ : Disjoint (connectedComponentIn F₁ᶜ p₁) M) (hU₂ : Disjoint (connectedComponentIn F₂ᶜ p₂) M) :
    Disjoint (connectedComponentIn F₁ᶜ p₁) (connectedComponentIn F₂ᶜ p₂) := by
  rw [Set.disjoint_iff]
  rintro z ⟨hz₁, hz₂⟩
  set U₁ := connectedComponentIn F₁ᶜ p₁
  set U₂ := connectedComponentIn F₂ᶜ p₂
  have h1 : U₁ ⊆ U₂ := by
    have : U₁ ⊆ connectedComponentIn F₂ᶜ z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hz₁
        (fun w hw hwF => hU₁.le_bot ⟨hw, hF₂M hwF⟩)
    rwa [← connectedComponentIn_eq hz₂] at this
  have h2 : U₂ ⊆ U₁ := by
    have : U₂ ⊆ connectedComponentIn F₁ᶜ z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hz₂
        (fun w hw hwF => hU₂.le_bot ⟨hw, hF₁M hwF⟩)
    rwa [← connectedComponentIn_eq hz₁] at this
  have heq : U₁ = U₂ := Subset.antisymm h1 h2
  have hfr : frontier U₁ = ∅ := by
    refine eq_empty_of_forall_notMem fun w hw => ?_
    have hw1 : w ∈ F₁ := by
      have := Moore.frontier_connectedComponentIn_subset hF₁.isOpen_compl p₁ hw
      simpa only [compl_compl] using this
    have hw2 : w ∈ F₂ := by
      have := Moore.frontier_connectedComponentIn_subset hF₂.isOpen_compl p₂ (heq ▸ hw)
      simpa only [compl_compl] using this
    exact hd.le_bot ⟨hw1, hw2⟩
  rcases isClopen_iff.1 (isClopen_iff_frontier_eq_empty.2 hfr) with h | h
  · exact (h ▸ hz₁ : z ∈ (∅ : Set Pt))
  · obtain ⟨w, hw⟩ := hF₁ne
    have : w ∈ U₁ := h ▸ mem_univ w
    exact connectedComponentIn_subset _ _ this hw

/-- Two distinct components of an open set are disjoint. -/
theorem disjoint_connectedComponentIn_of_notMem {F : Set Pt} {p q : Pt}
    (hq : q ∉ connectedComponentIn F p) :
    Disjoint (connectedComponentIn F p) (connectedComponentIn F q) := by
  rw [Set.disjoint_iff]
  rintro z ⟨h1, h2⟩
  have hqF : q ∈ F := connectedComponentIn_nonempty_iff.1 ⟨z, h2⟩
  have e1 := connectedComponentIn_eq h1
  have e2 := connectedComponentIn_eq h2
  apply hq
  rw [e1, ← e2]
  exact mem_connectedComponentIn hqF

section HU

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- The image of a proper subcontinuum under a homeomorphism is a proper subcontinuum. -/
theorem isContinuum_homeo_image (h : M ≃ₜ M) {K : Set M} (hK : Fold.Q78.IsContinuum K) :
    Fold.Q78.IsContinuum (h '' K) :=
  ⟨hK.1.image h.continuous, hK.2.image _ h.continuous.continuousOn⟩

omit [CompactSpace M] [ConnectedSpace M] in
theorem homeo_image_ne_univ (h : M ≃ₜ M) {K : Set M} (hK : K ≠ univ) : h '' K ≠ univ := by
  intro heq
  apply hK
  have h2 : h.symm '' (h '' K) = K := h.symm_image_image K
  rw [heq, image_univ_of_surjective h.symm.surjective] at h2
  exact h2.symm

omit [CompactSpace M] [ConnectedSpace M] in
/-- A proper subcontinuum lies in the composant of each of its points. -/
theorem subset_composant {K : Set M} (hK : Fold.Q78.IsContinuum K) (hKu : K ≠ univ) {y : M}
    (hy : y ∈ K) : K ⊆ Jones.composant y := fun _ hz => ⟨K, hK, hKu, hy, hz⟩

/-- In a Baire space, a meagre set contains no nonempty open set. -/
theorem exists_notMem_of_isMeagre {X : Type*} [TopologicalSpace X] [BaireSpace X] {O S : Set X}
    (hO : IsOpen O) (hOne : O.Nonempty) (hS : IsMeagre S) : ∃ p ∈ O, p ∉ S := by
  by_contra hcon
  push_neg at hcon
  have hd := dense_of_mem_residual (hS.mono hcon)
  obtain ⟨z, hzO, hzc⟩ := hd.inter_open_nonempty O hO hOne
  exact hzc hzO

/-- **Lemma 1, second paragraph.** A homogeneous indecomposable plane continuum is hereditarily
unicoherent. -/
theorem hereditarilyUnicoherent_of_homogeneous_indecomposable (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) : IsHereditarilyUnicoherent (univ : Set M) := by
  classical
  intro K _ hK hKnt H L hH hL hHL
  by_contra hcon
  -- `H ∩ L` is nonempty, so it is not preconnected
  have hHLne : (H ∩ L).Nonempty := by
    obtain ⟨z, hz⟩ := hK.2.nonempty
    have hHsub : H ⊆ K := hHL ▸ subset_union_left
    have hLsub : L ⊆ K := hHL ▸ subset_union_right
    obtain ⟨h0, hh0⟩ := hH.2.nonempty
    obtain ⟨l0, hl0⟩ := hL.2.nonempty
    obtain ⟨w, -, hw⟩ := isPreconnected_closed_iff.1 hK.2.isPreconnected H L hH.1.isClosed
      hL.1.isClosed hHL.symm.subset ⟨h0, hHsub hh0, hh0⟩ ⟨l0, hLsub hl0, hl0⟩
    exact ⟨w, hw⟩
  have hncon : ¬ IsPreconnected (H ∩ L) := fun h => hcon ⟨hHLne, h⟩
  -- `K` is proper
  have hKu : K ≠ univ := by
    intro hKu
    have hHu : H ≠ univ := by
      intro h; rw [h, univ_inter] at hncon; exact hncon hL.2.isPreconnected
    have hLu : L ≠ univ := by
      intro h; rw [h, inter_univ] at hncon; exact hncon hH.2.isPreconnected
    exact hi ⟨H, L, hH, hL, hHu, hLu, hHL.trans hKu⟩
  obtain ⟨x₀, hx₀⟩ := hK.2.nonempty
  -- the copies `F y = h_y '' K`
  choose hom hhom using fun y : M => hX x₀ y
  set F : M → Set M := fun y => hom y '' K with hFdef
  set F' : M → Set Pt := fun y => Subtype.val '' F y with hF'def
  have hFc : ∀ y, Fold.Q78.IsContinuum (F y) := fun y => isContinuum_homeo_image _ hK
  have hFu : ∀ y, F y ≠ univ := fun y => homeo_image_ne_univ _ hKu
  have hyF : ∀ y, y ∈ F y := fun y => ⟨x₀, hx₀, hhom y⟩
  have hF'c : ∀ y, IsCompact (F' y) := fun y => (hFc y).1.image continuous_subtype_val
  have hF'M : ∀ y, F' y ⊆ M := fun y => by rintro _ ⟨z, -, rfl⟩; exact z.2
  have hF'ne : ∀ y, (F' y).Nonempty := fun y => ⟨_, y, hyF y, rfl⟩
  -- each copy separates the plane
  have hsep : ∀ y, ¬ IsConnected (F' y)ᶜ := by
    intro y
    set g : M → Pt := fun m => (hom y m : Pt) with hg
    have hgi : IsInducing g := IsInducing.subtypeVal.comp (hom y).isInducing
    have hgF : F' y = g '' H ∪ g '' L := by
      simp only [hF'def, hFdef, hg, ← hHL, image_union, image_image]
    rw [hgF]
    refine separatesPlane_of_not_isPreconnected_inter (hH.1.image hgi.continuous)
      (hL.1.image hgi.continuous) (hgi.isPreconnected_image.2 hH.2.isPreconnected)
      (hgi.isPreconnected_image.2 hL.2.isPreconnected) ?_
    rw [← image_inter hgi.injective, hgi.isPreconnected_image]
    exact hncon
  -- copies in different composants are disjoint
  have hFdisj : ∀ y y', Jones.composant y ≠ Jones.composant y' → Disjoint (F' y) (F' y') := by
    intro y y' hne
    rw [Set.disjoint_iff]
    rintro _ ⟨⟨z, hz, rfl⟩, ⟨z', hz', hzz'⟩⟩
    have hzz : z' = z := Subtype.ext hzz'
    subst hzz
    rcases composant_eq_or_disjoint' hi y y' with h | h
    · exact hne h
    · exact h.le_bot ⟨subset_composant (hFc y) (hFu y) (hyF y) hz,
        subset_composant (hFc y') (hFu y') (hyF y') hz'⟩
  -- Step 3: some copy has every complementary domain meeting `M`
  have hNontriv : Nontrivial M := by
    obtain ⟨a, ha, b, hb, hab⟩ := hKnt
    exact ⟨⟨a, b, hab⟩⟩
  have hgood : ∃ y, ∀ p ∉ F' y, ¬ Disjoint (connectedComponentIn (F' y)ᶜ p) M := by
    by_contra hbad
    push_neg at hbad
    set ι := range (Jones.composant : M → Set M)
    have hrep : ∀ c : ι, ∃ y, Jones.composant y = c.1 := fun c => c.2
    choose yc hyc using hrep
    choose pc hpc hUc using fun c : ι => hbad (yc c)
    set U : ι → Set Pt := fun c => connectedComponentIn (F' (yc c))ᶜ (pc c)
    have hcount : Countable ι := by
      refine countable_of_pairwiseDisjoint_open (U := U)
        (fun c => (hF'c (yc c)).isClosed.isOpen_compl.connectedComponentIn)
        (fun c => ⟨pc c, mem_connectedComponentIn (hpc c)⟩) ?_
      intro c c' hcc'
      have hne : Jones.composant (yc c) ≠ Jones.composant (yc c') := by
        rw [hyc, hyc]; exact fun h => hcc' (Subtype.ext h)
      exact disjoint_components_missing (hF'c _).isClosed (hF'c _).isClosed (hF'ne _) (hF'M _)
        (hF'M _) (hFdisj _ _ hne) (hUc c) (hUc c')
    exact uncountable_composants' hi (Set.countable_coe_iff.1 hcount)
  obtain ⟨y, hy⟩ := hgood
  -- two complementary domains `U`, `V`
  have hcne : ((F' y)ᶜ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    have : IsCompact (univ : Set Pt) := h ▸ hF'c y
    exact noncompact_univ Pt this
  obtain ⟨p, hp⟩ := hcne
  obtain ⟨q, hq, hqU⟩ : ∃ q ∈ (F' y)ᶜ, q ∉ connectedComponentIn (F' y)ᶜ p := by
    by_contra h
    push_neg at h
    have heq : connectedComponentIn (F' y)ᶜ p = (F' y)ᶜ :=
      Subset.antisymm (connectedComponentIn_subset _ _) h
    exact hsep y ⟨⟨p, hp⟩, heq ▸ isPreconnected_connectedComponentIn⟩
  set U := connectedComponentIn (F' y)ᶜ p
  set V := connectedComponentIn (F' y)ᶜ q
  have hUV : Disjoint U V := disjoint_connectedComponentIn_of_notMem hqU
  have hUo : IsOpen U := (hF'c y).isClosed.isOpen_compl.connectedComponentIn
  have hVo : IsOpen V := (hF'c y).isClosed.isOpen_compl.connectedComponentIn
  -- Step 4: a point of `U ∩ M` outside the composant of `y`
  have hUM : (Subtype.val ⁻¹' U : Set M).Nonempty := by
    obtain ⟨z, hzU, hzM⟩ := not_disjoint_iff.1 (hy p hp)
    exact ⟨⟨z, hzM⟩, hzU⟩
  have hVM : (Subtype.val ⁻¹' V : Set M).Nonempty := by
    obtain ⟨z, hzV, hzM⟩ := not_disjoint_iff.1 (hy q hq)
    exact ⟨⟨z, hzM⟩, hzV⟩
  obtain ⟨p', hp'U, hp'κ⟩ := exists_notMem_of_isMeagre (hUo.preimage continuous_subtype_val) hUM
    (composant_isMeagre' hi y)
  obtain ⟨q', hq'V, hq'κ⟩ := (composant_dense' p').inter_open_nonempty _
    (hVo.preimage continuous_subtype_val) hVM
  obtain ⟨L', hL', hL'u, hp'L', hq'L'⟩ := hq'κ
  -- `L'` meets `F y`
  have hmeet : (L' ∩ F y).Nonempty := by
    by_contra hno
    rw [not_nonempty_iff_eq_empty] at hno
    have hsub : Subtype.val '' L' ⊆ (F' y)ᶜ := by
      rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
      rw [Subtype.ext hwz] at hw
      exact (hno ▸ (⟨hz, hw⟩ : z ∈ L' ∩ F y) : z ∈ (∅ : Set M))
    have hpre : IsPreconnected (Subtype.val '' L') :=
      hL'.2.isPreconnected.image _ continuous_subtype_val.continuousOn
    have h1 : Subtype.val '' L' ⊆ connectedComponentIn (F' y)ᶜ (p' : Pt) :=
      hpre.subset_connectedComponentIn ⟨p', hp'L', rfl⟩ hsub
    rw [← connectedComponentIn_eq hp'U] at h1
    exact hUV.le_bot ⟨h1 ⟨q', hq'L', rfl⟩, hq'V⟩
  -- so `p'` is in the composant of `y`
  apply hp'κ
  obtain ⟨w, hwL, hwF⟩ := hmeet
  refine ⟨L' ∪ F y, isContinuum_union hL' (hFc y) ⟨w, hwL, hwF⟩,
    union_ne_univ_of_indec hi hL' (hFc y) hL'u (hFu y), Or.inr (hyF y), Or.inl hp'L'⟩

/-- **Lemma 1, first paragraph**, from Moore's triod theorem: a homogeneous indecomposable plane
continuum is atriodic. A triod `T ⊆ M` is proper (`not_isTriod_univ_of_indecomposable`); its images
under homeomorphisms taking a point of `T` to a point `y` are triods in the composant of `y`; one per
composant gives uncountably many disjoint triods (`uncountable_composants'`), against `hmoore`. -/
theorem atriodic_of_homogeneous_indecomposable (hmoore : MooreTriodStatement)
    (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) : IsAtriodic (univ : Set M) := by
  classical
  intro T _ hT
  have hTu : T ≠ univ := fun h => not_isTriod_univ_of_indecomposable hi (h ▸ hT)
  have hTc : Fold.Q78.IsContinuum T := hT.1
  obtain ⟨x₀, hx₀⟩ := hTc.2.nonempty
  haveI : Nontrivial M := by
    obtain ⟨a, -, b, -, hab⟩ := IsTriod.nontrivial hT
    exact ⟨⟨a, b, hab⟩⟩
  choose hom hhom using fun y : M => hX x₀ y
  set ι := range (Jones.composant : M → Set M)
  have hrep : ∀ c : ι, ∃ y, Jones.composant y = c.1 := fun c => c.2
  choose yc hyc using hrep
  set Tc : ι → Set Pt := fun c => Subtype.val '' (hom (yc c) '' T)
  have hTc' : ∀ c, IsTriodSet (Tc c) := by
    intro c
    have := isTriodSet_image (g := fun m : M => ((hom (yc c) m : M) : Pt))
      (IsInducing.subtypeVal.comp (hom (yc c)).isInducing)
      (Subtype.val_injective.comp (hom (yc c)).injective) hT
    simpa only [Tc, image_image] using this
  have hsub : ∀ c, hom (yc c) '' T ⊆ Jones.composant (yc c) :=
    fun c => subset_composant (isContinuum_homeo_image _ hTc) (homeo_image_ne_univ _ hTu)
      ⟨x₀, hx₀, hhom _⟩
  have hdisj : Pairwise (Function.onFun Disjoint Tc) := by
    intro c c' hcc'
    have hne : Jones.composant (yc c) ≠ Jones.composant (yc c') := by
      rw [hyc, hyc]; exact fun h => hcc' (Subtype.ext h)
    rcases composant_eq_or_disjoint' hi (yc c) (yc c') with h | h
    · exact absurd h hne
    · simp only [Function.onFun, Tc]
      rw [Set.disjoint_iff]
      rintro _ ⟨⟨z, hz, rfl⟩, ⟨z', hz', hzz'⟩⟩
      rw [Subtype.ext hzz'] at hz'
      exact h.le_bot ⟨hsub c hz, hsub c' hz'⟩
  have hcount : Countable ι := hmoore ι Tc hTc' hdisj
  exact uncountable_composants' hi (Set.countable_coe_iff.1 hcount)

end HU

end HPC.Hagopian
