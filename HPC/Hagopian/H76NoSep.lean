import HPC.Hagopian.Hagopian76A
import HPC.Hagopian.H76SepInv

/-!
# Batch 157, item E: no proper subcontinuum of `M` separates the plane

Hagopian 1976, p. 344: "Since `M` is indecomposable and homogeneous, no proper subcontinuum of `M`
separates `R²` [5, Lemma 1 (second paragraph of proof)]." The 1975 paragraph (in the repository:
`hereditarilyUnicoherent_of_homogeneous_indecomposable`, `H75Lemma1.lean`) runs as follows for a
separating proper subcontinuum `K`:

* each composant of `M` contains a copy `h[K]` of `K`; **each copy contains a separating continuum**
  (`separating_in_copy`, from `exists_separating_subcontinuum_of_homeomorph`, `H76SepInv.lean`: this
  replaces the unstated topological invariance of plane separation);
* separating continua in different composants are disjoint, so their complementary domains missing
  `M` are disjoint; by separability some separating continuum `S` has all its complementary domains
  meeting `M`, two of them `U`, `V`;
* a point `p ∈ U ∩ M` outside the composant of `S` (Baire: composants are meagre) and a point
  `q ∈ V` of the (dense) composant of `p` give a proper subcontinuum from `p` to `q` meeting `S`,
  so `p` is in the composant of `S`.

The argument below is that of `H75Lemma1.lean`, with the separating continua `S_y` in place of the
non-unicoherent copies.
-/

namespace HPC.Hagopian

open Set Topology HPC.Plane HPC.Jones HPC.Moore

section NoSep

variable {M : Set Pt}

/-- **A homeomorphic copy of a separating continuum contains a separating continuum.** -/
theorem separating_in_copy (h : M ≃ₜ M) {K : Set M} (hK : Fold.Q78.IsContinuum K)
    (hs : SeparatesPlane (toPt K)) :
    ∃ C ⊆ toPt (h '' K), Fold.Q78.IsContinuum C ∧ SeparatesPlane C := by
  classical
  set φ : Pt → Pt := fun z => if hz : z ∈ M then (h ⟨z, hz⟩ : Pt) else z with hφ
  have hφM : ∀ m : M, φ m = (h m : Pt) := fun m => by simp [hφ, m.2]
  have hφc : ContinuousOn φ M := by
    rw [continuousOn_iff_continuous_restrict]
    have : M.restrict φ = fun m : M => (h m : Pt) := funext hφM
    rw [this]; exact continuous_subtype_val.comp h.continuous
  have hKc : IsCompact (toPt K) := hK.1.image continuous_subtype_val
  have hKM : toPt K ⊆ M := by rintro _ ⟨m, -, rfl⟩; exact m.2
  have himg : φ '' toPt K = toPt (h '' K) := by
    ext z; constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩; exact ⟨h m, ⟨m, hm, rfl⟩, (hφM m).symm⟩
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩; exact ⟨m, ⟨m, hm, rfl⟩, hφM m⟩
  have hinj : InjOn φ (toPt K) := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ hab
    rw [hφM, hφM] at hab
    exact congrArg Subtype.val (h.injective (Subtype.ext hab))
  have hK' : Fold.Q78.IsContinuum (toPt (h '' K)) :=
    isContinuum_val_image (isContinuum_homeo_image h hK)
  -- the homeomorphism `toPt K ≃ₜ toPt (h '' K)`
  haveI : CompactSpace (toPt K) := isCompact_iff_compactSpace.1 hKc
  have hcont : Continuous (fun x : toPt K => (⟨φ x, himg ▸ mem_image_of_mem φ x.2⟩ :
      toPt (h '' K))) :=
    ((hφc.mono hKM).restrict).subtype_mk _
  set e : toPt K ≃ toPt (h '' K) :=
    { toFun := fun x => ⟨φ x, himg ▸ mem_image_of_mem φ x.2⟩
      invFun := fun y => ⟨Function.invFunOn φ (toPt K) y,
        Function.invFunOn_mem (himg.symm ▸ y.2 : (y : Pt) ∈ φ '' toPt K)⟩
      left_inv := fun x => Subtype.ext (hinj
        (Function.invFunOn_mem ⟨x, x.2, rfl⟩) x.2
        (Function.invFunOn_eq ⟨x, x.2, rfl⟩))
      right_inv := fun y => Subtype.ext
        (Function.invFunOn_eq (himg.symm ▸ y.2 : (y : Pt) ∈ φ '' toPt K)) }
  exact exists_separating_subcontinuum_of_homeomorph hKc hs hK'
    (Continuous.homeoOfEquivCompactToT2 (f := e) hcont)

variable [CompactSpace M] [ConnectedSpace M]

/-- **No proper subcontinuum of `M` separates the plane** (Hagopian 1976, p. 344, citing [5, Lemma 1
(second paragraph of proof)]). -/
theorem no_proper_subcontinuum_separates_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {K : Set M} (hK : Fold.Q78.IsContinuum K) (hKu : K ≠ univ) :
    ¬ SeparatesPlane (toPt K) := by
  classical
  intro hsK
  obtain ⟨x₀, hx₀⟩ := hK.2.nonempty
  have hNontriv : Nontrivial M := by
    obtain ⟨z, hz⟩ : ∃ z, z ∉ K := by
      by_contra h; push_neg at h; exact hKu (eq_univ_of_forall h)
    exact ⟨⟨x₀, z, fun e => hz (e ▸ hx₀)⟩⟩
  choose hom hhom using fun y : M => hX x₀ y
  set F : M → Set M := fun y => hom y '' K with hFdef
  have hFc : ∀ y, Fold.Q78.IsContinuum (F y) := fun y => isContinuum_homeo_image _ hK
  have hFu : ∀ y, F y ≠ univ := fun y => homeo_image_ne_univ _ hKu
  have hyF : ∀ y, y ∈ F y := fun y => ⟨x₀, hx₀, hhom y⟩
  -- a separating continuum `F' y` inside each copy
  choose F' hF'sub hF'cont hsep using fun y => separating_in_copy (hom y) hK hsK
  have hF'c : ∀ y, IsCompact (F' y) := fun y => (hF'cont y).1
  have hF'M : ∀ y, F' y ⊆ M := fun y => (hF'sub y).trans (by rintro _ ⟨z, -, rfl⟩; exact z.2)
  have hF'ne : ∀ y, (F' y).Nonempty := fun y => (hF'cont y).2.nonempty
  have hF'F : ∀ y, ∀ z : M, (z : Pt) ∈ F' y → z ∈ F y := fun y z hz => by
    obtain ⟨w, hw, hwz⟩ := hF'sub y hz
    rwa [← Subtype.ext hwz]
  -- copies in different composants are disjoint
  have hFdisj : ∀ y y', Jones.composant y ≠ Jones.composant y' → Disjoint (F' y) (F' y') := by
    intro y y' hne
    rw [Set.disjoint_iff]
    rintro w ⟨hw, hw'⟩
    have hz := hF'F y ⟨w, hF'M y hw⟩ hw
    have hz' := hF'F y' ⟨w, hF'M y hw⟩ hw'
    rcases composant_eq_or_disjoint' hi y y' with h | h
    · exact hne h
    · exact h.le_bot ⟨subset_composant (hFc y) (hFu y) (hyF y) hz,
        subset_composant (hFc y') (hFu y') (hyF y') hz'⟩
  -- some separating continuum has every complementary domain meeting `M`
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
      rintro _ ⟨z, hz, rfl⟩ hzF
      exact (hno ▸ (⟨hz, hF'F y z hzF⟩ : z ∈ L' ∩ F y) : z ∈ (∅ : Set M))
    have hpre : IsPreconnected (Subtype.val '' L') :=
      hL'.2.isPreconnected.image _ continuous_subtype_val.continuousOn
    have h1 : Subtype.val '' L' ⊆ connectedComponentIn (F' y)ᶜ (p' : Pt) :=
      hpre.subset_connectedComponentIn ⟨p', hp'L', rfl⟩ hsub
    rw [← connectedComponentIn_eq hp'U] at h1
    exact hUV.le_bot ⟨h1 ⟨q', hq'L', rfl⟩, hq'V⟩
  apply hp'κ
  obtain ⟨w, hwL, hwF⟩ := hmeet
  exact ⟨L' ∪ F y, isContinuum_union hL' (hFc y) ⟨w, hwL, hwF⟩,
    union_ne_univ_of_indec hi hL' (hFc y) hL'u (hFu y), Or.inr (hyF y), Or.inl hp'L'⟩

end NoSep

end HPC.Hagopian
