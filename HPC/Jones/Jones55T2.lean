import HPC.Jones.Jones55T2D

/-!
# Batch 148 skeleton: Jones 1955 Theorem 2, modulo Jones 1949 Theorem 1

Save as `HPC/Jones/Jones55T2.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones55T2` at the end of `HPC.lean`. (Batch 148: every work item is discharged.) Shapes may be
adjusted, each change recorded at the statement and in the report.

Sources: F. B. Jones, *On a certain type of homogeneous plane continuum*, Proc. AMS 6 (1955),
735–740, Theorem 2 and the closing remarks, pp. 739–740 (`doc/sources/jones1955.pdf`); F. B. Jones,
*Note on homogeneous plane continua*, Bull. AMS 55 (1949), 113–114 (`doc/sources/jones1949.pdf`).
Transcribed from page images at 200 dpi.

**Theorem 2** (p. 739). "Suppose that `M` is a homogeneous, decomposable, bounded, plane continuum.
Let `G` denote the collection of all subsets `g` of `M` such that for some point `x` of `M`, `g` is
`L_x`. Then `G` is a continuous collection of mutually exclusive continua filling up `M` such that
(1) with respect to its elements (as points), `G` is a simple closed curve, and (2) each element of
`G` is a homogeneous, bounded, plane continuum which does not separate the plane."

**Modelling.** `M : Set Pt` with `CompactSpace M`, `ConnectedSpace M` (bounded plane continuum),
so batch 136's `Lset`, `lSetoid`, `jones55_*` apply to the subtype. Elements are pushed to the plane
by `Subtype.val`. A simple closed curve is a space homeomorphic to `Circle`.

**Scope.** Everything except Jones 1949 Theorem 1, which enters as the hypothesis `Jones49Thm1`
(batches 149– prove it). The final theorem, `jones55_theorem2`, discharges nothing it cannot.

**Layout (batch 148).** The skeleton is split: items A–C in `HPC/Jones/Jones55T2A.lean`
(`Jones49Thm1`, `not_jones49_theorem1_point`, `jordan_curve_theorem`,
`separatesPlane_of_homeomorph`, `countable_of_pairwiseDisjoint_open`), items D–E in
`HPC/Jones/Jones55T2D.lean` (`uncountable_quotient`, `jones55_compl_connected`,
`jones55_elt_not_separates`, `gPrimeRel`, `gPrimeRel_equivalence`, `gPrime`, `mooreDecomp_gPrime`,
`jones55_plane`, `jones55_embedding`, `isAposyndetic_iff_T`), items F–G here. All statements are
verbatim.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore

/-! ## Invariance under homeomorphisms -/

/-- Homogeneity is a topological invariant. -/
theorem IsHomogeneous.of_homeomorph {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) (h : IsHomogeneous Y) : IsHomogeneous Z := by
  intro z₁ z₂
  obtain ⟨T, hT⟩ := h (e.symm z₁) (e.symm z₂)
  exact ⟨(e.symm.trans T).trans e, by simp [hT]⟩

/-- Topological aposyndesis is a topological invariant. -/
theorem IsAposyndeticT.of_homeomorph {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) (h : IsAposyndeticT Y) : IsAposyndeticT Z := by
  intro z₁ z₂ hne
  obtain ⟨H, U, ⟨hHc, hHconn⟩, hU, hxU, hUH, hyH⟩ :=
    h (e.symm z₁) (e.symm z₂) (fun he => hne (e.symm.injective he))
  refine ⟨e '' H, e '' U, ⟨hHc.image e.continuous, hHconn.image _ e.continuous.continuousOn⟩,
    e.isOpenMap U hU, ⟨_, hxU, by simp⟩, image_mono hUH, ?_⟩
  rintro ⟨w, hw, hwe⟩
  apply hyH
  rw [← e.symm_apply_apply w, hwe] at hw
  simpa using hw

/-- Decomposability is invariant under homeomorphisms of metric spaces. -/
theorem IsDecomposableSpace.of_homeomorph {Y Z : Type*} [MetricSpace Y] [MetricSpace Z]
    (e : Y ≃ₜ Z) (h : IsDecomposableSpace Y) : IsDecomposableSpace Z := by
  obtain ⟨H, K, hH, hK, hHu, hKu, hHK⟩ := h
  have hne : ∀ {S : Set Y}, S ≠ univ → e '' S ≠ univ := fun {S} hS he =>
    hS (by rw [← e.preimage_image S, he, preimage_univ])
  refine ⟨e '' H, e '' K, ⟨hH.1.image e.continuous, hH.2.image _ e.continuous.continuousOn⟩,
    ⟨hK.1.image e.continuous, hK.2.image _ e.continuous.continuousOn⟩, hne hHu, hne hKu, ?_⟩
  rw [← image_union, hHK, image_univ, e.range_coe]

section T2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Each element of `G` is homogeneous; in the aposyndetic case (elements are points) trivially. -/
theorem isHomogeneous_Lset (hX : IsHomogeneous M) (x : M) : IsHomogeneous (Lset x) := by
  by_cases hap : IsAposyndetic M
  · haveI : Subsingleton (Lset x) := by
      rw [Lset_eq_singleton_of_isAposyndetic hap]; infer_instance
    exact isHomogeneous_of_subsingleton
  · exact (jones55_elements hX hap x x).2.2

/-- (1) of Theorem 2: `M/G` is a simple closed curve, given Jones 1949 Theorem 1. -/
theorem jones55_circle (h49 : Jones49Thm1) (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (Quotient (lSetoid M) ≃ₜ Circle) := by
  obtain ⟨hcpt, hconn, -, hnt, hhom, hapo⟩ := jones55_a hX hd
  obtain ⟨K, hK, hKc, ⟨e⟩⟩ := jones55_embedding hX hd
  have hKn : K.Nontrivial := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Quotient (lSetoid M))
    exact ⟨e a, (e a).2, e b, (e b).2, fun h => hab (e.injective (Subtype.ext h))⟩
  obtain ⟨e'⟩ := h49 K hK hKc hKn (hhom.of_homeomorph e)
    (isAposyndetic_iff_T.2 (hapo.of_homeomorph e))
  exact ⟨e.trans e'⟩

/-! ## Theorem 2 -/

/-- **Jones 1955, Theorem 2**, assuming Jones 1949 Theorem 1. `G` is a continuous decomposition of
`M`; (1) `M/G` is a simple closed curve; (2) each element is a homogeneous plane continuum not
separating the plane. (Boundedness of the elements is that of `M`.) -/
theorem jones55_theorem2 (h49 : Jones49Thm1) (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    IsContinuousDecomp (lSetoid M) ∧ Nonempty (Quotient (lSetoid M) ≃ₜ Circle) ∧
      ∀ x : M, IsConnected (Lset x) ∧ IsHomogeneous (Lset x) ∧
        ¬ SeparatesPlane (Subtype.val '' Lset x) :=
  ⟨jones55_continuous hX, jones55_circle h49 hX hd, fun x =>
    ⟨(isContinuum_Lset x).2, isHomogeneous_Lset hX x, jones55_elt_not_separates hX hd x⟩⟩

/-! ## The closing remarks (pp. 739–740): unnumbered claims -/

/-- p. 740: "every decomposable, homogeneous, bounded continuum in the plane must have exactly two
complementary domains (this follows from Theorem 2)".

*Proof:* in the plane of elements of `G′` (`jones55_plane`), the image of `M` is a simple closed
curve (Theorem 2 (1)); the Jordan curve theorem (`jordan_curve_theorem`) gives two domains of
elements, and their point sets are open, connected (`isConnected_ptsOf`, the elements of `G′` being
continua), disjoint, with union `S − M`. -/
theorem jones55_two_domains (h49 : Jones49Thm1) (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    ∃ U V : Set Pt, IsOpen U ∧ IsConnected U ∧ IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = Mᶜ := by
  have hG := mooreDecomp_gPrime hX hd
  obtain ⟨h, ⟨e⟩⟩ := jones55_embedding_data hX hd
  obtain ⟨c⟩ := jones55_circle h49 hX hd
  obtain ⟨I, E, hIo, hIc, hEo, hEc, hIE, hIEu, -, -, -, -⟩ := jordan_curve_theorem ⟨e.symm.trans c⟩
  refine ⟨Quotient.mk (gPrime M) ⁻¹' (h ⁻¹' I), Quotient.mk (gPrime M) ⁻¹' (h ⁻¹' E),
    (hIo.preimage h.continuous).preimage continuous_quotient_mk',
    isConnected_ptsOf hG ((h.isConnected_preimage).2 hIc),
    (hEo.preimage h.continuous).preimage continuous_quotient_mk',
    isConnected_ptsOf hG ((h.isConnected_preimage).2 hEc), (hIE.preimage _).preimage _, ?_⟩
  rw [← preimage_union, ← preimage_union, hIEu, preimage_compl, preimage_compl,
    h.preimage_image, preimage_image_mk_gPrime]

/-- p. 739, Remarks: "Because each element of `G` in Theorem 2 is homogeneous and does not separate
the plane, each such element is indecomposable."

*What it rests on (recorded):* the route of the commission, not Jones 1951 ([5] of Jones 1955, not
in the repository). A decomposable element `g` would be a homogeneous, decomposable plane continuum,
so by `jones55_two_domains` (which uses Theorem 2 (1), hence `h49`) its complement would be the
union of two disjoint nonempty open sets, against Theorem 2 (2). -/
theorem jones55_elements_indecomposable (h49 : Jones49Thm1) (hX : IsHomogeneous M)
    (hd : IsDecomposableSpace M) (x : M) : ¬ IsDecomposableSpace (Lset x) := by
  intro hdx
  set N : Set Pt := Subtype.val '' Lset x
  haveI : CompactSpace N := isCompact_iff_compactSpace.1 (isCompact_val_Lset x)
  haveI : ConnectedSpace N := isConnected_iff_connectedSpace.1
    ((isContinuum_Lset x).2.image _ continuous_subtype_val.continuousOn)
  obtain ⟨U, V, hUo, hUc, hVo, hVc, hUV, hUVe⟩ := jones55_two_domains h49
    ((isHomogeneous_Lset hX x).of_homeomorph (homeoVal _)) (hdx.of_homeomorph (homeoVal _))
  apply jones55_elt_not_separates hX hd x
  intro hc
  exact false_of_split hc.isPreconnected hUo hVo hUc.nonempty hVc.nonempty hUV hUVe

/-- p. 740: "every homogeneous, bounded continuum in the plane having more than two complementary
domains is indecomposable and of Type 3" (Type 3, p. 735: "Those which separate the plane but are
indecomposable"). Stated: three pairwise distinct complementary components force indecomposability
(separation is then automatic). -/
theorem jones55_three_domains (h49 : Jones49Thm1) (hX : IsHomogeneous M)
    {a b c : Pt} (ha : a ∉ M) (hb : b ∉ M) (hc : c ∉ M)
    (hab : connectedComponentIn Mᶜ a ≠ connectedComponentIn Mᶜ b)
    (hac : connectedComponentIn Mᶜ a ≠ connectedComponentIn Mᶜ c)
    (hbc : connectedComponentIn Mᶜ b ≠ connectedComponentIn Mᶜ c) :
    ¬ IsDecomposableSpace M := by
  intro hd
  obtain ⟨U, V, hUo, hUc, hVo, hVc, hUV, hUVe⟩ := jones55_two_domains h49 hX hd
  have key : ∀ p ∉ M, connectedComponentIn Mᶜ p = U ∨ connectedComponentIn Mᶜ p = V := by
    intro p hp
    have hpUV : p ∈ U ∪ V := hUVe ▸ hp
    have hcs : connectedComponentIn Mᶜ p ⊆ U ∪ V :=
      hUVe ▸ connectedComponentIn_subset _ _
    have hpc := mem_connectedComponentIn (F := Mᶜ) hp
    rcases hpUV with hpU | hpV
    · left
      refine (isPreconnected_connectedComponentIn.subset_left_of_subset_union hUo hVo hUV hcs
        ⟨p, hpc, hpU⟩).antisymm ?_
      exact hUc.isPreconnected.subset_connectedComponentIn hpU (hUVe ▸ subset_union_left)
    · right
      refine (isPreconnected_connectedComponentIn.subset_right_of_subset_union hUo hVo hUV hcs
        ⟨p, hpc, hpV⟩).antisymm ?_
      exact hVc.isPreconnected.subset_connectedComponentIn hpV (hUVe ▸ subset_union_right)
  rcases key a ha with h1 | h1 <;> rcases key b hb with h2 | h2 <;>
    rcases key c hc with h3 | h3 <;> simp_all

end T2

end HPC.Jones
