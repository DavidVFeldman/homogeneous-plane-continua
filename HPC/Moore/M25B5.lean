import HPC.Moore.M25BDefs

/-!
# Batch 146, item C: Moore 1925, Theorems 5–8 (p. 420)

Each theorem is an instance, in the space of elements (metrizable by `quotient_metrizable_plane`),
of the general results of `CutArc.lean`:

* Theorem 5: `IsCutArc.isConnected_diff_ends` (a cut-point arc is an embedded `[0, 1]`).
* Theorem 6: a closed connected nondegenerate subset of an embedded arc is the image of an interval
  (`eq_image_Icc_of_subset_range`), hence a cut-point arc (`isCutArc_image_Icc`).
* Theorem 7 (with `x` for the printed `p`): the sub-arcs of `pq` having `x` as an interior element
  are the images of intervals `[s, t] ∋ u` with `s < u < t` (`ends_of_image_Icc`), and these form a
  neighbourhood base of `x` in `pq`.
* Theorem 8: Nadler 6.7 (`exists_nonCut_diff`). Moore's own proof (pp. 420–421) is followed in
  substance: Nadler's non-cut point theorem (batch 94) is what replaces his appeal to Theorem 5 for
  "`K₂ + p` would be a simple continuous arc".

`not_separatesPlane_ptsOf` is `isConnected_ptsOf` (batch 145): the point set of a connected set of
elements is connected.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

section M25B

variable (hG : MooreDecomp r)
include hG

/-- Sets of elements and their point sets: if `H` does not separate `G`, then `H̄` does not separate
`S` (used in Theorems 11 and 13: "neither `a` nor `b` separates `G` and therefore neither `ā` nor `b̄`
separates `S`"). -/
theorem not_separatesPlane_ptsOf {H : Set (Quotient r)} (hH : IsConnected Hᶜ) :
    ¬ SeparatesPlane (ptsOf r H) := by
  unfold SeparatesPlane
  rw [not_not, ← ptsOf_compl]
  exact isConnected_ptsOf hG hH

/-- **Theorem 5** (p. 420). No simple continuous arc of elements is disconnected by the omission of
either of its extremities. (No proof in the text; "for an indication of material sufficient for a
proof … see page 139 of F. A. and page 342 of" Moore 1920.) -/
theorem m25_theorem5 {A B : Quotient r} {H : Set (Quotient r)} (h : IsArcElt A B H) :
    IsConnected (H \ {A}) ∧ IsConnected (H \ {B}) := by
  haveI := quotient_metrizable_plane hG
  exact h.isCutArc.isConnected_diff_ends

/-- **Theorem 6** (p. 420). Every closed and connected subset of a simple continuous arc which
contains more than one element is itself a simple continuous arc. (No proof in the text.) -/
theorem m25_theorem6 {A B : Quotient r} {K L : Set (Quotient r)} (hK : IsArcElt A B K)
    (hLK : L ⊆ K) (hL : IsClosed L) (hLc : IsConnected L) (hLn : L.Nontrivial) :
    ∃ a b, IsArcElt a b L := by
  haveI := quotient_metrizable_plane hG
  obtain ⟨f, hf, hrange, -, -⟩ := hK.isCutArc.exists_embedding
  obtain ⟨s, t, hst, rfl⟩ := eq_image_Icc_of_subset_range hf (hrange ▸ hLK) hL
    hLc.isPreconnected hLn
  exact ⟨_, _, (isCutArc_image_Icc hf hst).isArcElt hL
    (hK.2.2.2.1.subset (ptsOf_mono hLK))⟩

/-- **Theorem 7** (p. 420), **with `x` for the printed `p`** in "then `p` is a limit element of the
set `H`". If `pq` is an arc from `p` to `q`, `x ∈ pq` distinct from `p`, `q`, and `H ⊆ pq`, then `x`
is a limit element of `H` iff every arc contained in `pq`, containing `x` but not having `x` as an
extremity, contains an element of `H` other than `x`. (No proof in the text.) -/
theorem m25_theorem7 {p q x : Quotient r} {K H : Set (Quotient r)} (hK : IsArcElt p q K)
    (hx : x ∈ K) (hxp : x ≠ p) (hxq : x ≠ q) (hHK : H ⊆ K) :
    AccPt x (Filter.principal H) ↔
      ∀ a b L, IsArcElt a b L → L ⊆ K → x ∈ L → x ≠ a → x ≠ b → ∃ h ∈ H ∩ L, h ≠ x := by
  haveI := quotient_metrizable_plane hG
  obtain ⟨f, hf, hrange, hf0, hf1⟩ := hK.isCutArc.exists_embedding
  obtain ⟨u, rfl⟩ : x ∈ range f := hrange ▸ hx
  rw [accPt_iff_nhds]
  constructor
  · intro hacc a b L hL hLK hxL hxa hxb
    obtain ⟨s, t, hst, hLeq⟩ := eq_image_Icc_of_subset_range hf (hrange ▸ hLK) hL.2.1
      hL.2.2.1.isPreconnected ⟨a, hL.2.2.2.2.1, b, hL.2.2.2.2.2.1, hL.1⟩
    have hends := ends_of_image_Icc hf hst (hLeq ▸ hL.isCutArc)
    obtain ⟨v, hv, hvu⟩ : f u ∈ f '' Icc s t := hLeq ▸ hxL
    rw [hf.injective hvu] at hv
    have hus : u ≠ s := by
      rintro rfl; rcases hends with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hxa h1.symm
      · exact hxb h2.symm
    have hut : u ≠ t := by
      rintro rfl; rcases hends with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hxb h2.symm
      · exact hxa h1.symm
    obtain ⟨W, hWo, hWeq⟩ := hf.isInducing.isOpen_iff.1 (isOpen_Ioo (a := s) (b := t))
    have huW : f u ∈ W := by
      have : u ∈ f ⁻¹' W := by
        rw [hWeq]; exact ⟨lt_of_le_of_ne hv.1 (Ne.symm hus), lt_of_le_of_ne hv.2 hut⟩
      exact this
    obtain ⟨y, ⟨hyW, hyH⟩, hyx⟩ := hacc W (hWo.mem_nhds huW)
    obtain ⟨w, rfl⟩ : y ∈ range f := hrange ▸ hHK hyH
    have hw : w ∈ Ioo s t := by rw [← hWeq]; exact hyW
    exact ⟨f w, ⟨hyH, hLeq ▸ ⟨w, Ioo_subset_Icc_self hw, rfl⟩⟩, hyx⟩
  · intro hyp U hU
    have hu0 : u ≠ 0 := by rintro rfl; exact hxp hf0
    have hu1 : u ≠ 1 := by rintro rfl; exact hxq hf1
    have hpos : (0 : unitInterval) < u := lt_of_le_of_ne (unitInterval.nonneg' (t := u))
      (Ne.symm hu0)
    have hlt : u < (1 : unitInterval) := lt_of_le_of_ne unitInterval.le_one' hu1
    have hU' : f ⁻¹' U ∈ 𝓝 u := hf.continuous.continuousAt.preimage_mem_nhds hU
    obtain ⟨l, r', ⟨hlu, hur⟩, hsub⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0, hpos⟩ ⟨1, hlt⟩).1 hU'
    obtain ⟨s, hls, hsu⟩ := exists_between hlu
    obtain ⟨t, hut, htr⟩ := exists_between hur
    have hst : s < t := hsu.trans hut
    have hLK : f '' Icc s t ⊆ K := hrange ▸ image_subset_range _ _
    have hLcl : IsClosed (f '' Icc s t) := (isCompact_Icc.image hf.continuous).isClosed
    have hLarc := (isCutArc_image_Icc hf hst).isArcElt hLcl (hK.2.2.2.1.subset (ptsOf_mono hLK))
    obtain ⟨h, ⟨hhH, hhL⟩, hhx⟩ := hyp _ _ _ hLarc hLK ⟨u, ⟨hsu.le, hut.le⟩, rfl⟩
      (fun e => hsu.ne' (hf.injective e)) (fun e => hut.ne (hf.injective e))
    obtain ⟨w, hw, rfl⟩ := hhL
    exact ⟨f w, ⟨hsub ⟨hls.trans_le hw.1, hw.2.trans_lt htr⟩, hhH⟩, hhx⟩

/-- **Theorem 8** (pp. 420–421). If `K` is a closed, connected and bounded set of elements and `H` a
connected proper subset of `K`, then `K − H` contains an element whose omission does not disconnect
`K`. -/
theorem m25_theorem8 {K H : Set (Quotient r)} (hK : IsClosed K) (hKc : IsConnected K)
    (hKb : Bornology.IsBounded (ptsOf r K)) (hHK : H ⊆ K) (hHc : IsConnected H) (hne : H ≠ K) :
    ∃ x ∈ K \ H, IsConnected (K \ {x}) := by
  haveI := t1Space_quot hG
  exact exists_nonCut_diff (isCompact_of_isClosed_bounded hK hKb) hKc hHK hHc hne

end M25B

end HPC.Moore
