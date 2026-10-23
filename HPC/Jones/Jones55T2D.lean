import HPC.Jones.Jones55T2A

/-!
# Batch 148, items D–E: part (2) of Jones 1955 Theorem 2; the decomposition `G′` of the plane

Part of the batch-148 skeleton (`doc/batches/skeletons/Jones55T2-batch148.lean`), split under
`HPC/Jones/`; the statements are verbatim. Collected in `HPC/Jones/Jones55T2.lean`.

* **D.** `uncountable_quotient`, `jones55_compl_connected` (from (e) and (5) of Jones's proof of
  Theorem 1: `M − L_x = U_x` and two points of `U_x` lie in a continuum missing `x`, which misses
  `L_x` by (c); so `M − g` is continuum-wise connected), `jones55_elt_not_separates` (Jones's
  argument, with the disjointness of the domains `W_g` supplied: `W_g = W_h` would be an open set
  whose closure adds only points of `g ∩ h = ∅`).
* **E.** `gPrimeRel_equivalence`, `mooreDecomp_gPrime` (Moore's u.s.c. from `usc_of_isClosedMap`,
  batch 145, and the closedness of the quotient map `S → G′`), `jones55_plane` (Moore 1925
  Theorem 22), `jones55_embedding`, `isAposyndetic_iff_T`.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore

/-! ## General facts -/

/-- A connected, nondegenerate, metrizable space is uncountable (the distance to a point takes
all values in an interval). -/
theorem uncountable_of_connected_metrizable {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [ConnectedSpace Y] [Nontrivial Y] : Uncountable Y := by
  letI := TopologicalSpace.metrizableSpaceMetric Y
  obtain ⟨a, b, hab⟩ := exists_pair_ne Y
  set f : Y → ℝ := fun y => dist y a
  have hc : IsConnected (range f) := isConnected_range (continuous_id.dist continuous_const)
  have hsub : Icc 0 (dist b a) ⊆ range f :=
    hc.isPreconnected.Icc_subset ⟨a, dist_self a⟩ ⟨b, rfl⟩
  have hpos : 0 < dist b a := dist_pos.2 (Ne.symm hab)
  by_contra hcount
  rw [not_uncountable_iff] at hcount
  have : (Icc (0 : ℝ) (dist b a)).Countable := (countable_range f).mono hsub
  have h2 := this.le_aleph0
  rw [Cardinal.mk_Icc_real hpos] at h2
  exact absurd h2 (not_le.2 Cardinal.aleph0_lt_continuum)

/-- If `s` is not preconnected and `T ⊆ s` is preconnected and nonempty, some component of `s` is
disjoint from `T`. -/
theorem exists_component_disjoint {X : Type*} [TopologicalSpace X] {s T : Set X}
    (hs : ¬ IsPreconnected s) (hT : IsPreconnected T) (hTs : T ⊆ s) (hTn : T.Nonempty) :
    ∃ a ∈ s, Disjoint (connectedComponentIn s a) T := by
  obtain ⟨t, ht⟩ := hTn
  have hT0 : T ⊆ connectedComponentIn s t := hT.subset_connectedComponentIn ht hTs
  by_contra hcon
  push_neg at hcon
  apply hs
  have : s = connectedComponentIn s t := by
    refine (Subset.antisymm ?_ (connectedComponentIn_subset s t))
    intro a ha
    obtain ⟨z, hz1, hz2⟩ := not_disjoint_iff.1 (hcon a ha)
    rw [connectedComponentIn_eq (hT0 hz2), ← connectedComponentIn_eq hz1]
    exact mem_connectedComponentIn ha
  rw [this]
  exact isPreconnected_connectedComponentIn

/-- The closure of a component `W` of the complement of a set `g` adds only points of `g`. -/
theorem closure_component_compl_subset {X : Type*} [TopologicalSpace X] {g : Set X} {a : X} :
    closure (connectedComponentIn gᶜ a) ⊆ connectedComponentIn gᶜ a ∪ g := by
  intro z hz
  by_cases hzg : z ∈ g
  · exact Or.inr hzg
  left
  rcases (connectedComponentIn gᶜ a).eq_empty_or_nonempty with he | ⟨w, hw⟩
  · rw [he, closure_empty] at hz; exact hz.elim
  have hpc : IsPreconnected (closure (connectedComponentIn gᶜ a) ∩ gᶜ) :=
    isPreconnected_connectedComponentIn.subset_closure
      (subset_inter subset_closure (connectedComponentIn_subset _ _)) inter_subset_left
  have hsub := hpc.subset_connectedComponentIn (x := w) ⟨subset_closure hw,
    connectedComponentIn_subset _ _ hw⟩ inter_subset_right
  rw [← connectedComponentIn_eq hw] at hsub
  exact hsub ⟨hz, hzg⟩

section T2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- The collection `G` is uncountable when `M` is homogeneous and decomposable (a nondegenerate
compact metric continuum of elements, `jones55_a`). -/
theorem uncountable_quotient (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Uncountable (Quotient (lSetoid M)) := by
  obtain ⟨-, hc, hm, hn, -, -⟩ := jones55_a hX hd
  exact uncountable_of_connected_metrizable

/-- "It is clear that for each `g` of `G`, `M − g` is connected."

*What (5) is:* claim (5) of the proof of Theorem 1 (p. 736), "`p` does not cut any two points of
`U_p` from each other" (`jones55_claim5`), in its continuum form `exists_continuum_of_mem_aposSet`:
two points of `U_p` lie in a continuum missing `p`. Such a continuum misses `L_p` by (c), and
`M − L_p = U_p` by (e) (`jones55_prop_e`); so `M − g` is continuum-wise connected, which is the
"strongly connected" of Jones's parenthesis. -/
theorem jones55_compl_connected (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) (x : M) :
    IsConnected (Lset x)ᶜ := by
  haveI := nontrivial_of_isDecomposableSpace hd
  rw [jones55_prop_e]
  refine ⟨aposSet_nonempty hX hd x, isPreconnected_of_forall_pair ?_⟩
  intro a ha b hb
  obtain ⟨K, hK, haK, hbK, hxK⟩ := exists_continuum_of_mem_aposSet hX ha hb
  refine ⟨K, ?_, haK, hbK, hK.2.isPreconnected⟩
  intro z hz
  by_contra hzU
  rw [← jones55_prop_e] at hzU
  have hzU : z ∈ Lset x := by simpa using hzU
  have haL : a ∉ Lset x := by rw [← mem_compl_iff, jones55_prop_e]; exact ha
  exact hxK (jones55_c hX hK ⟨z, hz, hzU⟩ ⟨a, haK, haL⟩ (mem_Lset_self x))

/-- Jones's parenthesis: "`M − g` is strongly or continuum-wise connected". Any two points of
`M − L_x` lie in a continuum in `M − L_x` (by (5) and (c)). -/
theorem jones55_compl_continuumwise (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) (x : M)
    {a b : M} (ha : a ∉ Lset x) (hb : b ∉ Lset x) :
    ∃ K : Set M, Fold.Q78.IsContinuum K ∧ a ∈ K ∧ b ∈ K ∧ K ⊆ (Lset x)ᶜ := by
  haveI := nontrivial_of_isDecomposableSpace hd
  have ha' : a ∈ aposSet x := by rw [← jones55_prop_e]; exact ha
  have hb' : b ∈ aposSet x := by rw [← jones55_prop_e]; exact hb
  obtain ⟨K, hK, haK, hbK, hxK⟩ := exists_continuum_of_mem_aposSet hX ha' hb'
  refine ⟨K, hK, haK, hbK, fun z hz hzL => ?_⟩
  exact hxK (jones55_c hX hK ⟨z, hz, hzL⟩ ⟨a, haK, ha⟩ (mem_Lset_self x))

/-- If `M` is aposyndetic, each `L_x` is `{x}`. -/
theorem Lset_eq_singleton_of_isAposyndetic {X : Type*} [MetricSpace X] (ha : IsAposyndetic X)
    (x : X) : Lset x = {x} := by
  ext y
  rw [mem_Lset_iff, mem_singleton_iff]
  constructor
  · intro h; by_contra hyx; exact h (ha y x hyx)
  · rintro rfl; exact not_aposAt_self y

omit [ConnectedSpace M] in
/-- The point set of an element: compact. -/
theorem isCompact_val_Lset (x : M) : IsCompact (Subtype.val '' Lset x) :=
  (isClosed_Lset x).isCompact.image continuous_subtype_val

/-- A set of `M` is homeomorphic to its point set in the plane. -/
noncomputable def homeoVal (s : Set M) : s ≃ₜ (Subtype.val '' s : Set Pt) :=
  (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (by rw [range_comp, Subtype.range_coe]))

/-- **Theorem 2 (2), non-separation**: no element of `G` separates the plane.

*Proof (Jones's, completed):* in the aposyndetic case the elements are points. Otherwise the elements
are homeomorphic (`jones55_elements`), so if one separates, all do (`separatesPlane_of_homeomorph`).
`M − g` is connected (`jones55_compl_connected`), so some complementary domain `W_g` of `g` misses
`M − g`, hence misses `M`. For `g ≠ h`, `W_g` is a connected subset of `S − h`, so if `W_g` meets
`W_h` then `W_g ⊆ W_h` and symmetrically; then `W_g = W_h` has closure in `W_g ∪ (g ∩ h) = W_g`, so it
is open and closed in the plane, which is absurd. The `W_g` are uncountably many disjoint domains
(`uncountable_quotient`), against `countable_of_pairwiseDisjoint_open`. -/
theorem jones55_elt_not_separates (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) (x : M) :
    ¬ SeparatesPlane (Subtype.val '' Lset x) := by
  intro hsep
  by_cases hap : IsAposyndetic M
  · rw [Lset_eq_singleton_of_isAposyndetic hap, image_singleton] at hsep
    exact hsep (isConnected_compl_singleton_pt _)
  set g : M → Set Pt := fun y => Subtype.val '' Lset y with hgdef
  -- every element separates
  have hall : ∀ y : M, SeparatesPlane (g y) := by
    intro y
    obtain ⟨-, ⟨T⟩, -⟩ := jones55_elements hX hap x y
    exact separatesPlane_of_homeomorph (isCompact_val_Lset x) (isCompact_val_Lset y)
      ⟨((homeoVal _).symm.trans T).trans (homeoVal _)⟩ hsep
  -- the point set of `M`
  have hMconn : ∀ y : M, IsConnected (Subtype.val '' (Lset y)ᶜ) := fun y =>
    (jones55_compl_connected hX hd y).image _ continuous_subtype_val.continuousOn
  -- a complementary domain of `g y` missing `M`
  have hW : ∀ y : M, ∃ W : Set Pt, IsOpen W ∧ W.Nonempty ∧ Disjoint W M ∧
      ∃ a ∉ g y, W = connectedComponentIn (g y)ᶜ a := by
    intro y
    have hcpt := isCompact_val_Lset y
    have hnc : ¬ IsPreconnected (g y)ᶜ := by
      intro hpc
      apply hall y
      refine ⟨?_, hpc⟩
      obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall (0 : Pt)
      refine ⟨((R + 1 : ℝ), (0 : ℝ)), fun hm => ?_⟩
      have := hR hm
      rw [mem_closedBall, dist_zero_right, Prod.norm_def] at this
      have h1 : ‖(R + 1 : ℝ)‖ ≤ R := le_trans (le_max_left _ _) this
      rw [Real.norm_eq_abs] at h1
      linarith [le_abs_self (R + 1)]
    have hTs : Subtype.val '' (Lset y)ᶜ ⊆ (g y)ᶜ := by
      rintro _ ⟨m, hm, rfl⟩ ⟨m', hm', he⟩
      exact hm (Subtype.ext he ▸ hm')
    obtain ⟨a, ha, hdisj⟩ := exists_component_disjoint hnc (hMconn y).isPreconnected hTs
      (hMconn y).nonempty
    refine ⟨connectedComponentIn (g y)ᶜ a, hcpt.isClosed.isOpen_compl.connectedComponentIn,
      ⟨a, mem_connectedComponentIn ha⟩, ?_, a, ha, rfl⟩
    rw [disjoint_left]
    intro p hpW hpM
    by_cases hpL : (⟨p, hpM⟩ : M) ∈ Lset y
    · exact connectedComponentIn_subset _ _ hpW ⟨⟨p, hpM⟩, hpL, rfl⟩
    · exact disjoint_left.1 hdisj hpW ⟨⟨p, hpM⟩, hpL, rfl⟩
  choose W hWo hWn hWM a ha hWa using hW
  -- disjointness for distinct elements
  have hdisjW : ∀ y y' : M, Disjoint (Lset y) (Lset y') → Disjoint (W y) (W y') := by
    intro y y' hyy'
    have hgg : Disjoint (g y) (g y') := by
      rw [disjoint_left]
      rintro _ ⟨m, hm, rfl⟩ ⟨m', hm', he⟩
      exact disjoint_left.1 hyy' hm (Subtype.ext he ▸ hm')
    have hsub : ∀ {y y' : M}, Disjoint (g y) (g y') → (W y ∩ W y').Nonempty → W y ⊆ W y' := by
      intro y y' _ ⟨p, hp, hp'⟩
      have hWc : IsPreconnected (W y) := by rw [hWa y]; exact isPreconnected_connectedComponentIn
      have hWsub : W y ⊆ (g y')ᶜ := by
        intro z hz hzg
        obtain ⟨m, -, rfl⟩ := hzg
        exact disjoint_left.1 (hWM y) hz m.2
      have := hWc.subset_connectedComponentIn hp hWsub
      rw [hWa y'] at hp' ⊢
      rwa [← connectedComponentIn_eq hp'] at this
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne
    have hne' := nonempty_iff_ne_empty.2 hne
    have h1 := hsub hgg hne'
    have h2 := hsub hgg.symm (by rwa [inter_comm])
    have heq : W y = W y' := h1.antisymm h2
    have hcl : IsClosed (W y) := by
      refine closure_subset_iff_isClosed.1 fun z hz => ?_
      have c1 : z ∈ W y ∪ g y := by
        rw [hWa y] at hz ⊢; exact closure_component_compl_subset hz
      have c2 : z ∈ W y' ∪ g y' := by
        rw [heq] at hz; rw [hWa y'] at hz ⊢; exact closure_component_compl_subset hz
      rw [← heq] at c2
      rcases c1 with c1 | c1
      · exact c1
      rcases c2 with c2 | c2
      · exact c2
      exact (disjoint_left.1 hgg c1 c2).elim
    rcases isClopen_iff.1 ⟨hcl, hWo y⟩ with he | he
    · obtain ⟨p, hp⟩ := hWn y; rw [he] at hp; exact hp
    · exact disjoint_left.1 (hWM y) (he ▸ mem_univ (y : Pt)) y.2
  -- uncountably many disjoint domains
  have hunc := uncountable_quotient hX hd
  have hcount : Countable (Quotient (lSetoid M)) := by
    refine countable_of_pairwiseDisjoint_open (U := fun q => W q.out) (fun q => hWo _)
      (fun q => hWn _) ?_
    intro q q' hqq'
    apply hdisjW
    rw [disjoint_left]
    intro z hz hz'
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    apply Quotient.sound
    show Lset q.out = Lset q'.out
    rw [← (jones55_b hX).1 hz, ← (jones55_b hX).1 hz']
  exact not_countable hcount

/-! ## The decomposition `G′` of the plane -/

/-- The relation of `G′`: `G` together with the singletons of `S − M`. -/
def gPrimeRel (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (x y : Pt) : Prop :=
  x = y ∨ ∃ (hx : x ∈ M) (hy : y ∈ M), (lSetoid M) ⟨x, hx⟩ ⟨y, hy⟩

theorem gPrimeRel_equivalence (M : Set Pt) [CompactSpace M] [ConnectedSpace M] :
    Equivalence (gPrimeRel M) := by
  refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
  · rintro x y (rfl | ⟨hx, hy, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hy, hx, (lSetoid M).iseqv.symm h⟩
  · rintro x y z (rfl | ⟨hx, hy, h⟩) (rfl | ⟨hy', hz, h'⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hy', hz, h'⟩
    · exact Or.inr ⟨hx, hy, h⟩
    · exact Or.inr ⟨hx, hz, (lSetoid M).iseqv.trans h h'⟩

/-- `G′` as a setoid on the plane. -/
def gPrime (M : Set Pt) [CompactSpace M] [ConnectedSpace M] : Setoid Pt :=
  ⟨gPrimeRel M, gPrimeRel_equivalence M⟩

theorem gPrime_iff {x y : Pt} : gPrime M x y ↔ gPrimeRel M x y := Iff.rfl

/-- The elements of `G′` in `M` are the point sets of the `L_x`. -/
theorem elt_gPrime_of_mem (hX : IsHomogeneous M) {x : Pt} (hx : x ∈ M) :
    elt (gPrime M) x = Subtype.val '' Lset ⟨x, hx⟩ := by
  ext y
  show gPrimeRel M y x ↔ _
  constructor
  · rintro (rfl | ⟨hy, hx', h⟩)
    · exact ⟨⟨y, hx⟩, mem_Lset_self _, rfl⟩
    · exact ⟨⟨y, hy⟩, (jones55_b hX).2 h, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact Or.inr ⟨m.2, hx, (jones55_b hX).1 hm⟩

/-- The elements of `G′` off `M` are points. -/
theorem elt_gPrime_of_not_mem {x : Pt} (hx : x ∉ M) : elt (gPrime M) x = {x} := by
  ext y
  show gPrimeRel M y x ↔ _
  constructor
  · rintro (rfl | ⟨-, hx', -⟩)
    · rfl
    · exact (hx hx').elim
  · rintro rfl; exact Or.inl rfl

/-- The saturation of a closed plane set under `G′` is closed: the quotient map `S → G′` is
closed. -/
theorem isClosedMap_mk_gPrime (hX : IsHomogeneous M) : IsClosedMap (Quotient.mk (gPrime M)) := by
  intro F hF
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  change IsClosed (Quotient.mk (gPrime M) ⁻¹' _)
  have he : Quotient.mk (gPrime M) ⁻¹' (Quotient.mk (gPrime M) '' F) =
      F ∪ Subtype.val '' (Quotient.mk (lSetoid M) ⁻¹'
        (Quotient.mk (lSetoid M) '' (Subtype.val ⁻¹' F))) := by
    ext y
    simp only [mem_preimage, mem_image, mem_union]
    constructor
    · rintro ⟨x, hxF, hxy⟩
      rcases (Quotient.exact hxy : gPrimeRel M x y) with rfl | ⟨hx, hy, h⟩
      · exact Or.inl hxF
      · exact Or.inr ⟨⟨y, hy⟩, ⟨⟨x, hx⟩, hxF, Quotient.sound h⟩, rfl⟩
    · rintro (hyF | ⟨m, ⟨m', hm'F, hmm'⟩, rfl⟩)
      · exact ⟨y, hyF, rfl⟩
      · refine ⟨m', hm'F, Quotient.sound (Or.inr ⟨m'.2, m.2, Quotient.exact hmm'⟩)⟩
  rw [he]
  refine hF.union (IsCompact.isClosed (IsClosed.isCompact ?_ |>.image continuous_subtype_val))
  exact (isClosedMap_mk (jones55_usc hX) _ (hF.preimage continuous_subtype_val)).preimage
    continuous_quotient_mk'

/-- "Let `G′` denote the upper semi-continuous collection consisting of `G` together with each
degenerate subset of `S − M`": `G′` satisfies Moore's hypothesis (compact, connected,
non-separating elements; Moore's u.s.c.).

*The unargued upper semicontinuity:* the quotient map `S → G′` is closed (`isClosedMap_mk_gPrime`:
the saturation of a closed `F` is `F` together with the saturation of `F ∩ M` under `G`, closed by
the upper semicontinuity of `G`), and batch 145's `usc_of_isClosedMap` turns this into Moore's
distance form. -/
theorem mooreDecomp_gPrime (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    MooreDecomp (gPrime M) := by
  have hc : ∀ x, IsCompact (elt (gPrime M) x) := by
    intro x
    by_cases hx : x ∈ M
    · rw [elt_gPrime_of_mem hX hx]; exact isCompact_val_Lset _
    · rw [elt_gPrime_of_not_mem hx]; exact isCompact_singleton
  refine ⟨hc, fun x => ?_, fun x => ?_, usc_of_isClosedMap hc (isClosedMap_mk_gPrime hX)⟩
  · by_cases hx : x ∈ M
    · rw [elt_gPrime_of_mem hX hx]
      exact (isContinuum_Lset _).2.image _ continuous_subtype_val.continuousOn
    · rw [elt_gPrime_of_not_mem hx]; exact isConnected_singleton
  · by_cases hx : x ∈ M
    · rw [elt_gPrime_of_mem hX hx]; exact jones55_elt_not_separates hX hd _
    · rw [elt_gPrime_of_not_mem hx, SeparatesPlane, not_not]
      exact isConnected_compl_singleton_pt x

/-- "With respect to its elements (as points), `G′` is a plane [13]" — Moore 1925 Theorem 22. -/
theorem jones55_plane (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (Quotient (gPrime M) ≃ₜ ℝ × ℝ) :=
  m25_theorem22 (mooreDecomp_gPrime hX hd)

/-- The map `M/G → G′` induced by the inclusion. -/
def gIncl (M : Set Pt) [CompactSpace M] [ConnectedSpace M] :
    Quotient (lSetoid M) → Quotient (gPrime M) :=
  Quotient.lift (fun m : M => Quotient.mk (gPrime M) (m : Pt))
    (fun a b h => Quotient.sound (Or.inr ⟨a.2, b.2, h⟩))

theorem continuous_gIncl : Continuous (gIncl M) :=
  continuous_quotient_mk'.comp continuous_subtype_val |>.quotient_lift _

theorem injective_gIncl : Function.Injective (gIncl M) := by
  intro q q' h
  induction q using Quotient.inductionOn with | h a => ?_
  induction q' using Quotient.inductionOn with | h b => ?_
  rcases (Quotient.exact h : gPrimeRel M a b) with he | ⟨ha, hb, h'⟩
  · rw [Subtype.ext he]
  · exact Quotient.sound h'

theorem range_gIncl : range (gIncl M) = Quotient.mk (gPrime M) '' M := by
  ext q
  constructor
  · rintro ⟨q', rfl⟩
    induction q' using Quotient.inductionOn with | h a => ?_
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩

/-- `M` is saturated in `G′`. -/
theorem preimage_image_mk_gPrime : Quotient.mk (gPrime M) ⁻¹' (Quotient.mk (gPrime M) '' M) = M := by
  ext y
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rcases (Quotient.exact hxy : gPrimeRel M x y) with rfl | ⟨-, hy, -⟩
    · exact hx
    · exact hy
  · intro hy; exact ⟨y, hy, rfl⟩

/-- `jones55_embedding` with the data: the plane `G′ ≅ S`, and `M/G` homeomorphic to the image of
`M` in it. -/
theorem jones55_embedding_data (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    ∃ h : Quotient (gPrime M) ≃ₜ ℝ × ℝ,
      Nonempty (Quotient (lSetoid M) ≃ₜ (h '' (Quotient.mk (gPrime M) '' M) : Set Pt)) := by
  obtain ⟨h⟩ := jones55_plane hX hd
  haveI : T2Space (Quotient (gPrime M)) := h.isEmbedding.t2Space
  have hf : IsClosedEmbedding (h ∘ gIncl M) :=
    (h.continuous.comp continuous_gIncl).isClosedEmbedding (h.injective.comp injective_gIncl)
  refine ⟨h, ⟨hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr ?_)⟩⟩
  rw [range_comp, range_gIncl]

/-- "… and `G` is a compact subcontinuum of `G′`": `M/G` is homeomorphic to a compact connected
plane set. -/
theorem jones55_embedding (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    ∃ K : Set Pt, IsCompact K ∧ IsConnected K ∧ Nonempty (Quotient (lSetoid M) ≃ₜ K) := by
  obtain ⟨h, ⟨e⟩⟩ := jones55_embedding_data hX hd
  have hMc : IsCompact M := isCompact_iff_compactSpace.2 inferInstance
  have hMconn : IsConnected M := isConnected_iff_connectedSpace.2 inferInstance
  exact ⟨_, (hMc.image continuous_quotient_mk').image h.continuous,
    (hMconn.image _ continuous_quotient_mk'.continuousOn).image _ h.continuous.continuousOn, ⟨e⟩⟩

/-- Topological and metric aposyndesis agree (to move `jones55_a`'s `IsAposyndeticT` to the plane
copy of `M/G`, where Jones 1949 is stated with `IsAposyndetic`). -/
theorem isAposyndetic_iff_T {Y : Type*} [MetricSpace Y] : IsAposyndetic Y ↔ IsAposyndeticT Y :=
  Iff.rfl

end T2

end HPC.Jones
