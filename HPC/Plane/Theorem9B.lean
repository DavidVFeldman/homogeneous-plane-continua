import HPC.Plane.Theorem9BGen

/-!
# Batch 95: Theorem 9 (Bing 1951), the two open steps

Skeleton of `COMMISSION-batch95.md`, saved as `HPC/Plane/Theorem9B.lean` and imported at the end of
the root `HPC.lean`. The targets are batch 93's `endElt_mem_bingH` (Q1) and
`bingH_irreducible_singleton` (Q3).

**Status (batch 95).** Everything here is proved: QA, QB, QC (= Q1), Q3′ (the descent), Q3 and
Theorem 9 (`theorem9_1951`), unconditionally. The general facts used are in
`HPC/Plane/Theorem9BGen.lean`.

**Shape changes.**
* `endElt_contains_endElt_sub` (QB): the hypotheses `hnd : S'.Nontrivial` and
  `hne : bingElt r ≠ S'` are not used and are dropped. The statement holds for every subcontinuum
  `S'` containing `g`, indeed for every subcontinuum meeting `g`
  (`endElt_inter_contains_endElt`, in `Theorem9BGen.lean`).
* (Batch 96.) The batch-93 `sorry` declarations `endElt_mem_bingH`,
  `bingH_irreducible_singleton` and `theorem9_1951` were deleted from
  `HPC/Plane/Atriodic51B.lean`, and the batch-95 primed names here were renamed to those names
  (the primed names remain as `alias`es). `theorem9_1951` below is the unconditional Theorem 9.

Notation: `S'` a subcontinuum of `S`, as a subtype with `CompactSpace S'` installed from `hS'`
(batch 94's shape); `bingElt` on `S'` is the element computed in `S'`.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Q1, route 1: an end element of `S` contains an end element of every subcontinuum containing it -/

/-- **QA. Elements of `S'` inside an element of `S` form an order-interval.** If two elements of
`S'` lie in `g = bingElt r` (`r ∈ S`), every element of `S'` separating them (in `S'`) lies in
`g`. -/
theorem elt_between_subset (hS : BingS S) {S' : Set S} (hS' : Fold.Q78.IsContinuum S')
    (hnd : S'.Nontrivial) {r : S} {e e' e'' : S'}
    (he : ((↑) : S' → S) '' (haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
      bingElt e) ⊆ bingElt r)
    (he' : ((↑) : S' → S) '' (haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
      bingElt e') ⊆ bingElt r)
    (hsep : haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
      Separates (bingElt e'') (bingElt e) (bingElt e')) :
    ((↑) : S' → S) '' (haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
      bingElt e'') ⊆ bingElt r := by
  haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
  have hS'B := bingS_subcontinuum hS hS' hnd
  by_contra hno
  have off : ∀ z ∈ bingElt e'', (z : S) ∉ bingElt r := by
    intro z hz hzr
    apply hno
    have := bingElt_subtype_subset hS hS' z
    rwa [(mem_bingElt_iff hS'B).mp hz, (mem_bingElt_iff hS).mp hzr] at this
  have heg : (e : S) ∈ bingElt r := he ⟨e, mem_bingElt e, rfl⟩
  have he'g : (e' : S) ∈ bingElt r := he' ⟨e', mem_bingElt e', rfl⟩
  have hT : Fold.Q78.IsContinuum ((↑) ⁻¹' bingElt r : Set S') := isContinuum_preimage_val
    (hS.inter_two (bingElt_isContinuum hS r) hS' ⟨e, heg, e.2⟩)
  exact not_separates_of_preconnected hT.2.2
    (Set.disjoint_left.mpr fun z hzT hz => off z hz hzT) ⟨e, heg, mem_bingElt e⟩
    ⟨e', he'g, mem_bingElt e'⟩ hsep

/-- **QB. An end element of `S` contains an end element of every subcontinuum that contains it.**
(Shape change: the unused hypotheses `hnd : S'.Nontrivial` and `hne : bingElt r ≠ S'` are
dropped. The general form, for every subcontinuum *meeting* `g`, is
`endElt_inter_contains_endElt`.) -/
theorem endElt_contains_endElt_sub (hS : BingS S) {r : S} (hr : IsEndElt r) {S' : Set S}
    (hS' : Fold.Q78.IsContinuum S') (hsub : bingElt r ⊆ S') :
    haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
    ∃ e : S', IsEndElt e ∧ ((↑) : S' → S) '' bingElt e ⊆ bingElt r :=
  endElt_inter_contains_endElt hS hr hS' (hsub (mem_bingElt r)) (mem_bingElt r)

/-- **QC. Q1 of Theorem 9**: an end element of `S` is a member of Bing's `H`
(batch 93's `endElt_mem_bingH`). From QB and Theorem 8 (c) for `S'`: with `e ⊆ g` an end element
of `S'` and `e'` the other end element of `S'`, any `p ∈ e'` makes `S'` irreducible from `g` to
`p`. -/
theorem endElt_mem_bingH (hS : BingS S) {r : S} (hr : IsEndElt r) : BingH (bingElt r) := by
  refine ⟨bingElt_isContinuum hS r, bingElt_ne_univ hS r, fun S' hS' hsub hne => ?_⟩
  haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
  have hnd : S'.Nontrivial := by
    obtain ⟨s, hsS, hsg⟩ : ∃ s ∈ S', s ∉ bingElt r := by
      by_contra h
      push_neg at h
      exact hne (Subset.antisymm hsub h)
    exact ⟨r, hsub (mem_bingElt r), s, hsS, fun e => hsg (e ▸ mem_bingElt r)⟩
  have hS'B := bingS_subcontinuum hS hS' hnd
  obtain ⟨e, he, heg⟩ := endElt_contains_endElt_sub hS hr hS' hsub
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hS'B
  obtain ⟨e', he', hee'⟩ : ∃ e' : S', IsEndElt e' ∧ bingElt e ≠ bingElt e' := by
    by_cases h : bingElt e = bingElt a
    · exact ⟨b, hb, h ▸ hab⟩
    · exact ⟨a, ha, h⟩
  refine ⟨e', hS', hsub, e'.2, fun K hK hKS hgK hpK => ?_⟩
  have hK' : Fold.Q78.IsContinuum ((↑) ⁻¹' K : Set S') :=
    isContinuum_preimage_val (by rwa [inter_eq_left.mpr hKS])
  have := bingElt_irreducible hS'B e e' he he' hee' _ hK' (hgK (heg ⟨e, mem_bingElt e, rfl⟩)) hpK
  exact Subset.antisymm hKS fun x hx =>
    (show (⟨x, hx⟩ : S') ∈ ((↑) ⁻¹' K : Set S') from this ▸ trivial)

/-! ## Q3: descent -/

section Descent

/-- If an end element `F` of `W ⊇ h` contains the element `e` of `h`, then `W` is irreducible from
`e` to any point of another end element of `W`. -/
theorem irred_of_subset_endElt (hS : BingS S) {W h : Set S} (hW : Fold.Q78.IsContinuum W)
    (hh : Fold.Q78.IsContinuum h) (hWnt : W.Nontrivial) :
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1
    haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1
    ∀ {F x' : W}, IsEndElt F → IsEndElt x' → bingElt F ≠ bingElt x' → ∀ e : h,
      ((↑) : h → S) '' bingElt e ⊆ ((↑) : W → S) '' bingElt F →
      IrredFromSet W (((↑) : h → S) '' bingElt e) x' := by
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1
  haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1
  intro F x' hF hx' hFx e heF
  have hSW := bingS_subcontinuum hS hW hWnt
  have hEW : ((↑) : h → S) '' bingElt e ⊆ W := fun z hz => by
    obtain ⟨w, -, rfl⟩ := heF hz; exact w.2
  rw [irredFromSet_iff hW hEW x'.2]
  intro K hK hAK hxK
  obtain ⟨w, hwF, hw⟩ := heF ⟨e, mem_bingElt e, rfl⟩
  have hwE : (w : S) ∈ ((↑) : h → S) '' bingElt e := by rw [hw]; exact ⟨e, mem_bingElt e, rfl⟩
  have hwK : w ∈ K := hAK hwE
  have ew := (mem_bingElt_iff hSW).mp hwF
  exact bingElt_irreducible hSW w x' (hF.of_eq ew) hx' (by rw [ew]; exact hFx) K hK hwK hxK

/-- **Step G1.** If `W ⊋ h` is irreducible from `h` to some point, then `W` is irreducible from some
end element of `h` to some point. -/
theorem exists_endElt_good (hS : BingS S) {W h : Set S} (hW : Fold.Q78.IsContinuum W)
    (hh : Fold.Q78.IsContinuum h) (hsub : h ⊆ W) (hne : h ≠ W) {x : S}
    (hx : IrredFromSet W h x) :
    haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1
    ∃ e : h, IsEndElt e ∧ ∃ p, IrredFromSet W (((↑) : h → S) '' bingElt e) p := by
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1
  haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1
  obtain ⟨s, hsW, hsh⟩ : ∃ s ∈ W, s ∉ h := by
    by_contra hc; push_neg at hc; exact hne (Subset.antisymm hsub hc)
  obtain ⟨y, hy⟩ := hh.2.nonempty
  have hWnt : W.Nontrivial := ⟨y, hsub hy, s, hsW, fun e => hsh (e ▸ hy)⟩
  have hSW := bingS_subcontinuum hS hW hWnt
  have hA : Fold.Q78.IsContinuum ((↑) ⁻¹' h : Set W) :=
    isContinuum_preimage_val (by rw [inter_eq_left.mpr hsub]; exact hh)
  have hAne : ((↑) ⁻¹' h : Set W) ≠ univ := fun e =>
    hsh (show (⟨s, hsW⟩ : W) ∈ ((↑) ⁻¹' h : Set W) from e ▸ trivial)
  set x' : W := ⟨x, hx.2.2.1⟩
  have hirr := (irredFromSet_iff hW hsub hx.2.2.1).mp hx
  have hx'E := irred_isEndElt hSW hA hAne hirr
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hSW
  obtain ⟨F, hF, hFx⟩ : ∃ F : W, IsEndElt F ∧ bingElt F ≠ bingElt x' := by
    by_cases h' : bingElt a = bingElt x'
    · exact ⟨b, hb, fun e => hab (h'.trans e.symm)⟩
    · exact ⟨a, ha, h'⟩
  obtain ⟨w, hwA, hwF⟩ := irred_meets_endElt hSW hA hAne hirr hF hFx
  obtain ⟨e, he, heF⟩ := endElt_nested hS hW hh hsub hWnt hF hwA ⟨w, hwF, rfl⟩
  exact ⟨e, he, x, irred_of_subset_endElt hS hW hh hWnt hF hx'E hFx e heF⟩

/-- **Step G2 (monotonicity).** For `h ∈ H` and `h ⊊ W₁ ⊆ W₂`: if `W₁` is irreducible from the
element `e` of `h` to some point, so is `W₂`. -/
theorem good_mono (hS : BingS S) {h : Set S} (hH : BingH h) {W₁ W₂ : Set S}
    (hW₁ : Fold.Q78.IsContinuum W₁) (hW₂ : Fold.Q78.IsContinuum W₂) (h1 : h ⊆ W₁) (hne1 : h ≠ W₁)
    (h12 : W₁ ⊆ W₂) :
    haveI : CompactSpace h := isCompact_iff_compactSpace.mp hH.1.1
    ∀ e : h, (∃ p, IrredFromSet W₁ (((↑) : h → S) '' bingElt e) p) →
      ∃ p, IrredFromSet W₂ (((↑) : h → S) '' bingElt e) p := by
  haveI : CompactSpace h := isCompact_iff_compactSpace.mp hH.1.1
  haveI : CompactSpace W₂ := isCompact_iff_compactSpace.mp hW₂.1
  intro e hgood
  have hh := hH.1
  have hsub2 : h ⊆ W₂ := h1.trans h12
  have hne2 : h ≠ W₂ := fun eq => hne1 (Subset.antisymm h1 (eq ▸ h12))
  obtain ⟨x₂, hx₂⟩ := hH.2.2 W₂ hW₂ hsub2 hne2
  obtain ⟨s, hsW, hsh⟩ : ∃ s ∈ W₂, s ∉ h := by
    by_contra hc; push_neg at hc; exact hne2 (Subset.antisymm hsub2 hc)
  have hWnt : W₂.Nontrivial := ⟨e, hsub2 e.2, s, hsW, fun eq => hsh (eq ▸ e.2)⟩
  have hSW := bingS_subcontinuum hS hW₂ hWnt
  haveI := hSW.connected
  set A : Set W₂ := (↑) ⁻¹' h with hA_def
  have hA : Fold.Q78.IsContinuum A :=
    isContinuum_preimage_val (by rw [inter_eq_left.mpr hsub2]; exact hh)
  have hAne : A ≠ univ := fun eq =>
    hsh (show (⟨s, hsW⟩ : W₂) ∈ A from eq ▸ trivial)
  set x' : W₂ := ⟨x₂, hx₂.2.2.1⟩
  have hirr := (irredFromSet_iff hW₂ hsub2 hx₂.2.2.1).mp hx₂
  have hx'E := irred_isEndElt hSW hA hAne hirr
  have hdis := irred_disjoint hSW hA hAne hirr
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hSW
  obtain ⟨F, hF, hFx⟩ : ∃ F : W₂, IsEndElt F ∧ bingElt F ≠ bingElt x' := by
    by_cases h' : bingElt a = bingElt x'
    · exact ⟨b, hb, fun e => hab (h'.trans e.symm)⟩
    · exact ⟨a, ha, h'⟩
  obtain ⟨w₀, hw₀A, hw₀F⟩ := irred_meets_endElt hSW hA hAne hirr hF hFx
  set m : W₂ := Set.inclusion hsub2 e
  have hem := bingElt_nested_subset hS hh hsub2 e
  by_cases hin : ((↑) : h → S) '' bingElt e ⊆ ((↑) : W₂ → S) '' bingElt F
  · exact ⟨x₂, irred_of_subset_endElt hS hW₂ hh hWnt hF hx'E hFx e hin⟩
  exfalso
  have hmF : bingElt m ≠ bingElt F := fun eq => hin (eq ▸ hem)
  have hmA : m ∈ A := e.2
  have hmx : bingElt m ≠ bingElt x' := fun eq =>
    Set.disjoint_left.mp hdis hmA (eq ▸ mem_bingElt m)
  rcases bingElt_separates_triple hSW m F x' hmF hFx hmx with hsep | hsep | hsep
  rotate_left
  · exact hF m x' hmF hFx.symm hmx hsep
  · exact hx'E m F hmx hFx hmF hsep
  obtain ⟨d1, d2, U, V, hU, hV, hUV, hcov, hFU, hxV⟩ := hsep
  set C := bingElt m with hC_def
  have hcov' : Cᶜ ⊆ V ∪ U := fun z hz => by
    rw [union_comm]; exact hcov ⟨mem_univ z, hz⟩
  have hx'C : x' ∉ C := fun h' => Set.disjoint_left.mp d2 h' (mem_bingElt x')
  have hw₀C : w₀ ∉ C := fun h' => Set.disjoint_left.mp d1 h' hw₀F
  have hK := isContinuum_side (bingElt_isContinuum hSW m).1.isClosed (bingElt_isContinuum hSW m).2
    hV hU hUV.symm hcov' ⟨x', hx'C, hxV (mem_bingElt x')⟩ ⟨w₀, hw₀C, hFU hw₀F⟩
  set K := (Cᶜ ∩ V) ∪ C with hK_def
  have hKA := isContinuum_union hK hA ⟨m, Or.inr (mem_bingElt m), hmA⟩
  have hunion := hirr _ hKA subset_union_right (Or.inl (Or.inl ⟨hx'C, hxV (mem_bingElt x')⟩))
  have hUh : ∀ z : W₂, z ∈ U → z ∉ C → z ∈ A := by
    intro z hzU hzC
    have : z ∈ K ∪ A := hunion ▸ mem_univ z
    rcases this with (h' | h') | h'
    · exact absurd h'.2 (Set.disjoint_left.mp hUV hzU)
    · exact absurd h' hzC
    · exact h'
  have hw₀K : w₀ ∉ K := by
    rintro (h' | h')
    · exact Set.disjoint_left.mp hUV (hFU hw₀F) h'.2
    · exact hw₀C h'
  obtain ⟨p₁, hp₁⟩ := hgood
  have hp₁W₂ : p₁ ∈ W₂ := h12 hp₁.2.2.1
  set p' : W₂ := ⟨p₁, hp₁W₂⟩
  have hEh : ((↑) : h → S) '' bingElt e ⊆ h := Subtype.coe_image_subset _ _
  by_cases hpK : p' ∈ K
  · have hL := hS.inter_two hW₁ (isContinuum_image_val hK)
      ⟨e, h1 e.2, ⟨m, Or.inr (mem_bingElt m), rfl⟩⟩
    have hEL : ((↑) : h → S) '' bingElt e ⊆ W₁ ∩ ((↑) : W₂ → S) '' K := fun z hz => by
      refine ⟨h1 (hEh hz), ?_⟩
      obtain ⟨k, hk, hkz⟩ := hem hz
      exact ⟨k, Or.inr hk, hkz⟩
    have := hp₁.2.2.2 _ hL inter_subset_left hEL ⟨hp₁.2.2.1, p', hpK, rfl⟩
    have hw₀L : (w₀ : S) ∈ W₁ ∩ ((↑) : W₂ → S) '' K := by rw [this]; exact h1 hw₀A
    obtain ⟨k, hk, hkw⟩ := hw₀L.2
    exact hw₀K (Subtype.ext hkw ▸ hk)
  · have hpC : p' ∉ C := fun h' => hpK (Or.inr h')
    have hpU : p' ∈ U := by
      rcases hcov' hpC with h' | h'
      · exact absurd (Or.inl ⟨hpC, h'⟩) hpK
      · exact h'
    have hph : p₁ ∈ h := hUh p' hpU hpC
    exact hne1 (hp₁.2.2.2 h hh h1 hEh hph)

/-- Two continua properly containing a member of `H` meet in a continuum properly containing it. -/
theorem bingH_inter_super {h : Set S} (hS : BingS S) (hH : BingH h) {W₁ W₂ : Set S}
    (hW₁ : Fold.Q78.IsContinuum W₁) (hW₂ : Fold.Q78.IsContinuum W₂) (h1 : h ⊆ W₁) (hne1 : h ≠ W₁)
    (h2 : h ⊆ W₂) (hne2 : h ≠ W₂) :
    Fold.Q78.IsContinuum (W₁ ∩ W₂) ∧ h ⊆ W₁ ∩ W₂ ∧ h ≠ W₁ ∩ W₂ := by
  obtain ⟨y, hy⟩ := hH.1.2.nonempty
  refine ⟨hS.inter_two hW₁ hW₂ ⟨y, h1 hy, h2 hy⟩, subset_inter h1 h2, fun eq => ?_⟩
  have hU := isContinuum_union hW₁ hW₂ ⟨y, h1 hy, h2 hy⟩
  have hhU : h ≠ W₁ ∪ W₂ := fun e => hne1 (Subset.antisymm h1 (e ▸ subset_union_left))
  obtain ⟨z, hz⟩ := hH.2.2 _ hU (h1.trans subset_union_left) hhU
  rcases hz.2.2.1 with hz1 | hz2
  · have := hz.2.2.2 W₁ hW₁ subset_union_left h1 hz1
    have hsub : W₂ ⊆ W₁ := fun x hx => by rw [this]; exact Or.inr hx
    exact hne2 (by rw [eq, inter_eq_right.mpr hsub])
  · have := hz.2.2.2 W₂ hW₂ subset_union_right h2 hz2
    have hsub : W₁ ⊆ W₂ := fun x hx => by rw [this]; exact Or.inl hx
    exact hne1 (by rw [eq, inter_eq_left.mpr hsub])

end Descent

/-- **Q3′ (descent).** If `h` is a nondegenerate member of `H`, then an end element of `h`
(computed in `h` as a space) is a member of `H`. With Brouwer reduction (batch 93) this gives Q3:
a minimal member is a point. -/
theorem endElt_of_bingH_mem_bingH (hS : BingS S) {h : Set S} (hh : BingH h) (hnd : h.Nontrivial) :
    haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1.1
    ∃ e : h, IsEndElt e ∧ BingH (((↑) : h → S) '' bingElt e) := by
  haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1.1
  have hSh := bingS_subcontinuum hS hh.1 hnd
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hSh
  have hchoose : ∃ e : h, IsEndElt e ∧ ∀ W : Set S, Fold.Q78.IsContinuum W → h ⊆ W → h ≠ W →
      ∃ p, IrredFromSet W (((↑) : h → S) '' bingElt e) p := by
    by_contra hno
    push_neg at hno
    obtain ⟨W₁, hW₁, h1, hn1, hg1⟩ := hno a ha
    obtain ⟨W₂, hW₂, h2, hn2, hg2⟩ := hno b hb
    obtain ⟨hW₃, h3, hn3⟩ := bingH_inter_super hS hh hW₁ hW₂ h1 hn1 h2 hn2
    obtain ⟨x, hx⟩ := hh.2.2 _ hW₃ h3 hn3
    obtain ⟨c, hc, hgc⟩ := exists_endElt_good hS hW₃ hh.1 h3 hn3 hx
    obtain ⟨p₁, hp₁⟩ := good_mono hS hh hW₃ hW₁ h3 hn3 inter_subset_left c hgc
    obtain ⟨p₂, hp₂⟩ := good_mono hS hh hW₃ hW₂ h3 hn3 inter_subset_right c hgc
    rcases at_most_two_endElts hSh ha hb hc hab with e | e
    · rw [e] at hp₁; exact hg1 p₁ hp₁
    · rw [e] at hp₂; exact hg2 p₂ hp₂
  obtain ⟨e, he, hgood⟩ := hchoose
  refine ⟨e, he, isContinuum_image_val (bingElt_isContinuum hSh e), fun eq => hh.2.1
    (eq_univ_of_univ_subset (eq ▸ Subtype.coe_image_subset _ _)), ?_⟩
  intro S'' hS'' hES'' hne
  have heh : (e : S) ∈ h := e.2
  have heE : (e : S) ∈ ((↑) : h → S) '' bingElt e := ⟨e, mem_bingElt e, rfl⟩
  by_cases hS''h : S'' ⊆ h
  · -- inside `h`: Q1 for the space `h`
    have hS''' : Fold.Q78.IsContinuum ((↑) ⁻¹' S'' : Set h) :=
      isContinuum_preimage_val (by rwa [inter_eq_left.mpr hS''h])
    have himg : ((↑) : h → S) '' ((↑) ⁻¹' S'' : Set h) = S'' := by
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hS''h]
    obtain ⟨p, hp⟩ := (endElt_mem_bingH hSh he).2.2 _ hS'''
      (fun z hz => hES'' ⟨z, hz, rfl⟩)
      (fun eq => hne (by rw [eq, himg]))
    refine ⟨p, hS'', hES'', hp.2.2.1, fun K hK hKS hEK hpK => ?_⟩
    have hK' : Fold.Q78.IsContinuum ((↑) ⁻¹' K : Set h) :=
      isContinuum_preimage_val (by rwa [inter_eq_left.mpr (hKS.trans hS''h)])
    have := hp.2.2.2 _ hK' (preimage_mono hKS) (fun z hz => hEK ⟨z, hz, rfl⟩) hpK
    refine Subset.antisymm hKS fun x hx => ?_
    have : (⟨x, hS''h hx⟩ : h) ∈ ((↑) ⁻¹' K : Set h) := this ▸ hx
    exact this
  by_cases hhS'' : h ⊆ S''
  · exact hgood S'' hS'' hhS'' fun eq => hS''h eq.ge
  · exfalso
    have hW := isContinuum_union hS'' hh.1 ⟨e, hES'' heE, heh⟩
    have hhW : h ≠ S'' ∪ h := fun eq => hS''h (eq ▸ subset_union_left)
    obtain ⟨p, hp⟩ := hgood _ hW subset_union_right hhW
    have hEh : ((↑) : h → S) '' bingElt e ⊆ h := Subtype.coe_image_subset _ _
    rcases hp.2.2.1 with hpS | hph
    · exact hhS'' ((hp.2.2.2 S'' hS'' subset_union_left hES'' hpS).symm ▸ subset_union_right)
    · exact hhW (hp.2.2.2 h hh.1 subset_union_right hEh hph)

/-- **Q3 from Q3′** (batch 93's `bingH_irreducible_singleton`). -/
theorem bingH_irreducible_singleton (hS : BingS S) {h : Set S} (hh : BingH h)
    (hmin : ∀ h' : Set S, BingH h' → h' ⊆ h → h' = h) : ∃ p : S, h = {p} := by
  by_cases hnd : h.Nontrivial
  · exfalso
    haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1.1
    have hSh := bingS_subcontinuum hS hh.1 hnd
    obtain ⟨e, -, heH⟩ := endElt_of_bingH_mem_bingH hS hh hnd
    have := hmin _ heH (Subtype.coe_image_subset _ _)
    apply bingElt_ne_univ hSh e
    refine eq_univ_of_forall fun z => ?_
    have hz : (z : S) ∈ ((↑) : h → S) '' bingElt e := by rw [this]; exact z.2
    obtain ⟨z', hz', hzz⟩ := hz
    exact Subtype.ext hzz ▸ hz'
  · obtain ⟨p, hp⟩ := hh.1.2.nonempty
    exact ⟨p, (Set.not_nontrivial_iff.mp hnd).eq_singleton_of_mem hp⟩

/-- **Theorem 9** (Bing 1951, p. 659), unconditional: each end element of `G` contains a point
satisfying condition A for `S`. -/
theorem theorem9_1951 (hS : BingS S) {r : S} (hr : IsEndElt r) :
    ∃ p ∈ bingElt r, CondA (univ : Set S) p :=
  theorem9_1951_of_steps hS (fun _ hr => endElt_mem_bingH hS hr)
    (fun _ hh hmin => bingH_irreducible_singleton hS hh hmin) hr

/-- Batch-95 name of `endElt_mem_bingH`, kept as an alias (batch 96 renamed it). -/
alias endElt_mem_bingH' := endElt_mem_bingH
/-- Batch-95 name of `bingH_irreducible_singleton`, kept as an alias (batch 96). -/
alias bingH_irreducible_singleton' := bingH_irreducible_singleton
/-- Batch-95 name of `theorem9_1951`, kept as an alias (batch 96). -/
alias theorem9_1951' := theorem9_1951

end HPC.Plane
