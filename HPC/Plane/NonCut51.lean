import HPC.Plane.Atriodic51B
import HPC.Plane.NonCut51Gen

/-!
# Batch 94: Moore's non-cut-point theorem; the two end elements of Bing's decomposition

Skeleton of `COMMISSION-batch94.md` (saved as `HPC/Plane/NonCut51.lean`, imported at the end of
the root `HPC.lean`).

§1 is general topology (Nadler, *Continuum Theory*, 6.3, 6.4, 6.6, 6.7), stated for compact
connected `T₁` spaces — no metric. **Shape change:** §1 (the definitions `IsSeparation`,
`IsCutPoint` and the five statements) is moved verbatim to `HPC/Plane/NonCut51Gen.lean`, which
imports Mathlib only, so that the general theorem is reusable without Bing's material; there the
skeleton's `IsOpen (Y := Y) (...)` (which does not elaborate: `Y` is not an argument name of
`IsOpen`) is written `IsOpen ((↑) ⁻¹' P : Set Y)`, and the unused `[Nontrivial X]` is dropped from
6.6 (`exists_nonCutPoint_of_cut`) and 6.7 (`not_subset_of_nonCutPoints`).

§2 applies it to Bing's decomposition `G = {bingElt p}` of a space satisfying `BingS`: an element
is an *end element* (`IsEndElt`, batch 93: it separates no two other elements) if and only if it
is a non-cut element, and there are two of them. Route (a) of the commission: the decomposition
space `Quotient (Setoid.ker bingElt)`.

§3 is reconnaissance: hereditary transfer of `BingS` to a subcontinuum, and the elements of a
subcontinuum. **Shape change:** the subtype `S'` carries no `CompactSpace` instance by itself, so
the two statements of §3 install it from `hS'` (`isCompact_iff_compactSpace`) with a `haveI` in
the statement; the unused hypothesis `hnd` is dropped from `bingElt_subtype_subset`.
-/

namespace HPC.Plane

open Set Topology

/-! ## §2. End elements of Bing's decomposition -/

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- An element is a *cut element* when its complement is disconnected. -/
def IsCutElt (r : S) : Prop := ¬ IsConnected ((bingElt r)ᶜ)

theorem bingElt_ne_univ (hS : BingS S) (r : S) : bingElt r ≠ univ := by
  intro h
  haveI := hS.nontrivial
  have := bingElt_interior_eq_empty hS r
  rw [h, interior_univ] at this
  exact univ_nonempty.ne_empty this

theorem mem_bingElt_iff (hS : BingS S) {r x : S} : x ∈ bingElt r ↔ bingElt x = bingElt r :=
  ⟨fun h => (bingElt_partition hS r x h).symm, fun h => h ▸ mem_bingElt x⟩

theorem disjoint_bingElt_of_notMem (hS : BingS S) {q r : S} (h : q ∉ bingElt r) :
    Disjoint (bingElt q) (bingElt r) :=
  bingElt_disjoint hS fun e => h (e ▸ mem_bingElt q)

omit [CompactSpace S] in
/-- `IsEndElt r` depends only on the element `bingElt r`. -/
theorem IsEndElt.of_eq {r r' : S} (h : IsEndElt r) (e : bingElt r' = bingElt r) : IsEndElt r' := by
  unfold IsEndElt at *
  rw [e]; exact h

/-- **End element ⇔ non-cut element.** (⇒: a separation of `S ∖ g_r` contains a whole element on
each side, since elements are connected and disjoint from `g_r`; those two elements are then
separated by `g_r` in the sense of `Separates`. ⇐: `Separates` exhibits the separation.) -/
theorem isEndElt_iff_not_isCutElt (hS : BingS S) (r : S) : IsEndElt r ↔ ¬ IsCutElt r := by
  have hcl : ∀ q : S, IsClosed (bingElt q) := fun q => (bingElt_isContinuum hS q).1.isClosed
  constructor
  · intro hend hcut
    obtain ⟨a, ha⟩ := (ne_univ_iff_exists_notMem _).mp (bingElt_ne_univ hS r)
    obtain ⟨P, Q, hPQ, -⟩ := exists_separation_of_not_isConnected (Y := (bingElt r)ᶜ) ha hcut
    have hPo : IsOpen P := hPQ.symm.isOpen_right (hcl r).isOpen_compl
    have hQo : IsOpen Q := hPQ.isOpen_right (hcl r).isOpen_compl
    obtain ⟨q, hq⟩ := hPQ.1
    obtain ⟨q', hq'⟩ := hPQ.2.1
    have hqr : q ∉ bingElt r := hPQ.subset_left hq
    have hq'r : q' ∉ bingElt r := hPQ.subset_right hq'
    have side : ∀ {x : S}, x ∉ bingElt r → bingElt x ⊆ P ∨ bingElt x ⊆ Q := fun hx =>
      hPQ.subset_or_subset (bingElt_isContinuum hS _).2.isPreconnected
        (subset_compl_iff_disjoint_right.mpr (disjoint_bingElt_of_notMem hS hx))
    have hgq : bingElt q ⊆ P := (side hqr).resolve_right fun h =>
      Set.disjoint_left.mp hPQ.2.2.1 hq (h (mem_bingElt q))
    have hgq' : bingElt q' ⊆ Q := (side hq'r).resolve_left fun h =>
      Set.disjoint_left.mp hPQ.2.2.1 (h (mem_bingElt q')) hq'
    refine hend q q' (fun e => hqr (e ▸ mem_bingElt q)) (fun e => hq'r (e ▸ mem_bingElt q'))
      (fun e => Set.disjoint_left.mp hPQ.2.2.1 (hgq (e ▸ mem_bingElt q')) hq')
      ⟨(disjoint_bingElt_of_notMem hS hqr).symm, (disjoint_bingElt_of_notMem hS hq'r).symm,
        P, Q, hPo, hQo, hPQ.2.2.1, ?_, hgq, hgq'⟩
    exact fun x hx => hPQ.2.2.2.1 ▸ hx.2
  · intro hnc q q' _ _ _ hsep
    obtain ⟨d1, d2, U, V, hU, hV, hUV, hcov, hqU, hq'V⟩ := hsep
    refine hnc fun hc => ?_
    have hq : q ∈ (bingElt r)ᶜ := fun h => Set.disjoint_left.mp d1 h (mem_bingElt q)
    have hq' : q' ∈ (bingElt r)ᶜ := fun h => Set.disjoint_left.mp d2 h (mem_bingElt q')
    rcases hc.isPreconnected.subset_or_subset hU hV hUV (fun x hx => hcov ⟨mem_univ x, hx⟩) with h | h
    · exact Set.disjoint_left.mp hUV (h hq') (hq'V (mem_bingElt q'))
    · exact Set.disjoint_left.mp hUV (hqU (mem_bingElt q)) (h hq)

/-! ### The decomposition space (route (a)) -/

/-- The quotient map onto the decomposition space. -/
local notation "πG" => Quotient.mk (Setoid.ker (bingElt (S := S)))

omit [CompactSpace S] in
theorem mk_eq_mk_iff {x y : S} : πG x = πG y ↔ bingElt x = bingElt y := by
  rw [Quotient.eq]; exact Setoid.ker_def

/-- The fibre of the quotient map over the class of `r` is the element `bingElt r`. -/
theorem preimage_mk_singleton (hS : BingS S) (r : S) : πG ⁻¹' {πG r} = bingElt r := by
  ext x
  rw [mem_preimage, mem_singleton_iff, mk_eq_mk_iff, mem_bingElt_iff hS]

/-- **The decomposition space** `S / G`, with the quotient topology, is compact, connected, `T₁`
and nondegenerate. (`T₁`: a class is closed in the quotient iff its preimage, the element, is
closed in `S`. Nondegenerate: by Theorem 8 (b), no element is all of `S`.) -/
theorem decompositionSpace_props (hS : BingS S) :
    CompactSpace (Quotient (Setoid.ker (bingElt (S := S)))) ∧
    ConnectedSpace (Quotient (Setoid.ker (bingElt (S := S)))) ∧
    T1Space (Quotient (Setoid.ker (bingElt (S := S)))) ∧
    Nontrivial (Quotient (Setoid.ker (bingElt (S := S)))) := by
  haveI := hS.connected
  refine ⟨inferInstance, inferInstance, ⟨fun y => ?_⟩, ?_⟩
  · induction y using Quotient.inductionOn with
    | h r =>
      rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
      change IsClosed (πG ⁻¹' {πG r})
      rw [preimage_mk_singleton hS]
      exact (bingElt_isContinuum hS r).1.isClosed
  · haveI := hS.nontrivial
    obtain ⟨r⟩ := (inferInstance : Nonempty S)
    obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem _).mp (bingElt_ne_univ hS r)
    exact ⟨⟨πG x, πG r, fun e => hx ((mem_bingElt_iff hS).mpr (mk_eq_mk_iff.mp e))⟩⟩

/-- A cut element of `S` is a cut point of the decomposition space, and conversely. -/
theorem isCutElt_iff_isCutPoint_quot (hS : BingS S) (r : S) :
    IsCutElt r ↔ IsCutPoint (Quotient.mk (Setoid.ker (bingElt (S := S))) r) := by
  unfold IsCutElt IsCutPoint
  refine not_congr ⟨fun hc => ?_, fun hc => ?_⟩
  · have hpre : πG ⁻¹' {πG r}ᶜ = (bingElt r)ᶜ := by
      rw [preimage_compl, preimage_mk_singleton hS]
    rw [← image_preimage_eq ({πG r}ᶜ) Quotient.mk_surjective, hpre]
    exact hc.image _ continuous_quotient_mk'.continuousOn
  · have hpre : πG ⁻¹' {πG r}ᶜ = (bingElt r)ᶜ := by
      rw [preimage_compl, preimage_mk_singleton hS]
    obtain ⟨y, hy⟩ := hc.nonempty
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
    have hx : x ∈ (bingElt r)ᶜ := hpre ▸ hy
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [isPreconnected_iff_subset_of_disjoint]
    intro u v hu hv hsub hdisj
    -- the two traces are saturated
    have sat : ∀ {u v : Set S}, IsOpen u → IsOpen v → (bingElt r)ᶜ ⊆ u ∪ v → (bingElt r)ᶜ ∩ (u ∩ v) = ∅ →
        πG ⁻¹' (πG '' (u ∩ (bingElt r)ᶜ)) = u ∩ (bingElt r)ᶜ := by
      intro u v hu hv hsub hdisj
      refine Subset.antisymm ?_ (subset_preimage_image _ _)
      rintro y ⟨z, ⟨hzu, hzr⟩, hzy⟩
      have hyz : bingElt y = bingElt z := (mk_eq_mk_iff.mp hzy).symm
      have hgz : bingElt z ⊆ (bingElt r)ᶜ :=
        subset_compl_iff_disjoint_right.mpr (disjoint_bingElt_of_notMem hS hzr)
      have hyg : y ∈ bingElt z := hyz ▸ mem_bingElt y
      rcases isPreconnected_iff_subset_of_disjoint.mp
          (bingElt_isContinuum hS z).2.isPreconnected u v hu hv (hgz.trans hsub) (by
            rw [← subset_empty_iff, ← hdisj]; exact inter_subset_inter_left _ hgz) with h | h
      · exact ⟨h hyg, hgz hyg⟩
      · exfalso
        have : z ∈ (bingElt r)ᶜ ∩ (u ∩ v) := ⟨hzr, hzu, h (mem_bingElt z)⟩
        rw [hdisj] at this; exact this
    have satu := sat hu hv hsub hdisj
    have satv := sat hv hu (by rw [union_comm]; exact hsub) (by rw [inter_comm v u]; exact hdisj)
    have ou : IsOpen (πG '' (u ∩ (bingElt r)ᶜ)) := by
      rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
      change IsOpen (πG ⁻¹' (πG '' (u ∩ (bingElt r)ᶜ)))
      rw [satu]; exact hu.inter (bingElt_isContinuum hS r).1.isClosed.isOpen_compl
    have ov : IsOpen (πG '' (v ∩ (bingElt r)ᶜ)) := by
      rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
      change IsOpen (πG ⁻¹' (πG '' (v ∩ (bingElt r)ᶜ)))
      rw [satv]; exact hv.inter (bingElt_isContinuum hS r).1.isClosed.isOpen_compl
    have hcov : {πG r}ᶜ ⊆ πG '' (u ∩ (bingElt r)ᶜ) ∪ πG '' (v ∩ (bingElt r)ᶜ) := by
      intro w hw
      obtain ⟨z, rfl⟩ := Quotient.mk_surjective w
      have hz : z ∈ (bingElt r)ᶜ := hpre ▸ hw
      rcases hsub hz with h | h
      · exact Or.inl ⟨z, ⟨h, hz⟩, rfl⟩
      · exact Or.inr ⟨z, ⟨h, hz⟩, rfl⟩
    have hemp : {πG r}ᶜ ∩ (πG '' (u ∩ (bingElt r)ᶜ) ∩ πG '' (v ∩ (bingElt r)ᶜ)) = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro - ⟨z, hz, rfl⟩ hzv
      have hzv' : z ∈ v ∩ (bingElt r)ᶜ := by rw [← satv]; exact hzv
      have : z ∈ (bingElt r)ᶜ ∩ (u ∩ v) := ⟨hz.2, hz.1, hzv'.1⟩
      rw [hdisj] at this; exact this
    rcases isPreconnected_iff_subset_of_disjoint.mp hc.isPreconnected _ _ ou ov hcov hemp with h | h
    · left
      intro z hz
      have : z ∈ πG ⁻¹' (πG '' (u ∩ (bingElt r)ᶜ)) := h (hpre.symm ▸ hz : z ∈ πG ⁻¹' {πG r}ᶜ)
      rw [satu] at this; exact this.1
    · right
      intro z hz
      have : z ∈ πG ⁻¹' (πG '' (v ∩ (bingElt r)ᶜ)) := h (hpre.symm ▸ hz : z ∈ πG ⁻¹' {πG r}ᶜ)
      rw [satv] at this; exact this.1

/-- **Two end elements** (Bing, Theorem 11: "`g_1` and `g_2` are the end elements of `G`"; the
existence is Moore's theorem applied to the decomposition space). -/
theorem exists_two_endElts (hS : BingS S) :
    ∃ a b : S, bingElt a ≠ bingElt b ∧ IsEndElt a ∧ IsEndElt b := by
  obtain ⟨h1, h2, h3, h4⟩ := decompositionSpace_props hS
  obtain ⟨a', b', hne, ha, hb⟩ :=
    exists_two_nonCutPoints (X := Quotient (Setoid.ker (bingElt (S := S))))
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a'
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b'
  exact ⟨a, b, fun e => hne (mk_eq_mk_iff.mpr e),
    (isEndElt_iff_not_isCutElt hS a).mpr fun h => ha ((isCutElt_iff_isCutPoint_quot hS a).mp h),
    (isEndElt_iff_not_isCutElt hS b).mpr fun h => hb ((isCutElt_iff_isCutPoint_quot hS b).mp h)⟩

/-- **Nadler 6.7 for elements**: no proper subcontinuum of `S` meets every end element — the form
in which Theorem 8 (c) is used in Theorem 11. Proved directly from `exists_two_endElts` and
Theorem 8 (c) (`bingElt_irreducible`): a proper subcontinuum meeting two distinct end elements
would be `S`. -/
theorem not_subset_of_endElts (hS : BingS S) {Z : Set S} (hZ : Fold.Q78.IsContinuum Z)
    (hne : Z ≠ univ) : ∃ r : S, IsEndElt r ∧ Disjoint (bingElt r) Z := by
  by_contra hall
  push_neg at hall
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hS
  obtain ⟨x, hxa, hxZ⟩ := not_disjoint_iff.mp (hall a ha)
  obtain ⟨y, hyb, hyZ⟩ := not_disjoint_iff.mp (hall b hb)
  have ex := (mem_bingElt_iff hS).mp hxa
  have ey := (mem_bingElt_iff hS).mp hyb
  exact hne (bingElt_irreducible hS x y (ha.of_eq ex) (hb.of_eq ey)
    (by rw [ex, ey]; exact hab) Z hZ hxZ hyZ)

/-! ## §3. Reconnaissance: `BingS` on a subcontinuum; the elements of a subcontinuum -/

section Subtype

variable {S' : Set S}

omit [CompactSpace S] in
theorem isContinuum_image_val {K : Set S'} (hK : Fold.Q78.IsContinuum K) :
    Fold.Q78.IsContinuum (((↑) : S' → S) '' K) :=
  ⟨hK.1.image continuous_subtype_val, hK.2.image _ continuous_subtype_val.continuousOn⟩

omit [CompactSpace S] in
theorem isContinuum_of_image_val {K : Set S'} (hK : Fold.Q78.IsContinuum (((↑) : S' → S) '' K)) :
    Fold.Q78.IsContinuum K :=
  ⟨IsInducing.subtypeVal.isCompact_iff.mpr hK.1,
    ⟨image_nonempty.mp hK.2.nonempty, IsInducing.subtypeVal.isPreconnected_image.mp hK.2.2⟩⟩

omit [CompactSpace S] in
theorem isContinuum_preimage_val {K : Set S} (hK : Fold.Q78.IsContinuum (K ∩ S')) :
    Fold.Q78.IsContinuum (((↑) : S' → S) ⁻¹' K) :=
  isContinuum_of_image_val (by rw [Subtype.image_preimage_coe, inter_comm]; exact hK)

omit [CompactSpace S] in
theorem disjoint_closure_image_val {A B : Set S'} (h : Disjoint (closure A) B) :
    Disjoint (closure (((↑) : S' → S) '' A)) (((↑) : S' → S) '' B) := by
  rw [Set.disjoint_left]
  rintro _ hx ⟨b, hb, rfl⟩
  have : b ∈ closure A := by
    rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image]; exact hx
  exact Set.disjoint_left.mp h this hb

omit [CompactSpace S] in
theorem isTriod_image_val {T : Set S'} (hT : IsTriod T) : IsTriod (((↑) : S' → S) '' T) := by
  obtain ⟨hTc, N, hN, hNT, A, B, C, hA, hB, hC, heq, d1, d2, d3, d4, d5, d6⟩ := hT
  refine ⟨isContinuum_image_val hTc, _, isContinuum_image_val hN, image_mono hNT, _, _, _,
    hA.image _, hB.image _, hC.image _, ?_, disjoint_closure_image_val d1,
    (disjoint_closure_image_val d2.symm).symm, disjoint_closure_image_val d3,
    (disjoint_closure_image_val d4.symm).symm, disjoint_closure_image_val d5,
    (disjoint_closure_image_val d6.symm).symm⟩
  rw [← image_diff Subtype.val_injective, heq, image_union, image_union]

end Subtype

/-- **Hereditary transfer.** A nondegenerate subcontinuum `S'` of `S`, as a subtype, satisfies
Bing's standing hypothesis. (Shape change: the instance `CompactSpace S'` is installed from `hS'`
inside the statement.) -/
theorem bingS_subcontinuum (hS : BingS S) {S' : Set S} (hS' : Fold.Q78.IsContinuum S')
    (hnd : S'.Nontrivial) :
    haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
    BingS S' := by
  haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
  refine ⟨isConnected_iff_connectedSpace.mp hS'.2, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnd
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, fun e => hxy (congrArg Subtype.val e)⟩⟩
  · intro T _ hT
    exact hS.atriodic _ (subset_univ _) (isTriod_image_val hT)
  · intro K _ hK hKnt H K' hH hK' hunion
    have := hS.hu _ (subset_univ _) (isContinuum_image_val hK)
      (hKnt.image Subtype.val_injective) _ _ (isContinuum_image_val hH)
      (isContinuum_image_val hK') (by rw [← image_union, hunion])
    rw [← image_inter Subtype.val_injective] at this
    exact ⟨image_nonempty.mp this.nonempty,
      IsInducing.subtypeVal.isPreconnected_image.mp this.2⟩
  · intro K _ hK hKnt
    obtain ⟨A, B, hA, hB, hAK, hBK, hAB⟩ := hS.hd _ (subset_univ _) (isContinuum_image_val hK)
      (hKnt.image Subtype.val_injective)
    have hAS : A ⊆ S' := fun a ha => by
      obtain ⟨k, -, rfl⟩ : a ∈ ((↑) : S' → S) '' K := hAB ▸ Or.inl ha
      exact k.2
    have hBS : B ⊆ S' := fun a ha => by
      obtain ⟨k, -, rfl⟩ : a ∈ ((↑) : S' → S) '' K := hAB ▸ Or.inr ha
      exact k.2
    have iA : ((↑) : S' → S) '' (((↑) : S' → S) ⁻¹' A) = A := by
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hAS]
    have iB : ((↑) : S' → S) '' (((↑) : S' → S) ⁻¹' B) = B := by
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hBS]
    refine ⟨_, _, isContinuum_of_image_val (iA.symm ▸ hA), isContinuum_of_image_val (iB.symm ▸ hB),
      fun e => hAK (by rw [← iA, e]), fun e => hBK (by rw [← iB, e]), ?_⟩
    rw [← preimage_union, hAB, preimage_image_eq _ Subtype.val_injective]

/-- **Elements of a subcontinuum lie in elements of `S`** (report 93, §3, route 1: "a continuum
containing `x` doubly interiorly in `S`, intersected with `S'`, does the same in `S'`, by
unicoherence"). **Proved.** (Shape changes: the instance `CompactSpace S'` is installed from `hS'`
inside the statement; the hypothesis `hnd : S'.Nontrivial` is not used and is dropped.) -/
theorem bingElt_subtype_subset (hS : BingS S) {S' : Set S} (hS' : Fold.Q78.IsContinuum S')
    (x : S') :
    haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
    ((↑) : S' → S) '' bingElt x ⊆ bingElt (x : S) := by
  haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
  rintro _ ⟨y, hy, rfl⟩
  refine mem_sInter.mpr fun H ⟨hH, H', hH', hH'H, hxH'⟩ => ?_
  have c1 : Fold.Q78.IsContinuum (((↑) : S' → S) ⁻¹' H) := isContinuum_preimage_val
    (hS.inter_two hH hS' ⟨x, interior_subset (hH'H (interior_subset hxH')), x.2⟩)
  have c2 : Fold.Q78.IsContinuum (((↑) : S' → S) ⁻¹' H') := isContinuum_preimage_val
    (hS.inter_two hH' hS' ⟨x, interior_subset hxH', x.2⟩)
  have hN : ContainsNested (((↑) : S' → S) ⁻¹' H) x :=
    ⟨_, c2, (preimage_mono hH'H).trans
      (preimage_interior_subset_interior_preimage continuous_subtype_val),
      preimage_interior_subset_interior_preimage continuous_subtype_val hxH'⟩
  exact bingElt_subset c1 hN hy

end HPC.Plane
