import HPC.Moore.M25CInt

/-!
# Batch 147, item B: Moore 1925, Theorems 13 and 14 (pp. 422–423)

* `quot_janiszewski`: Janiszewski's theorem for sets of elements (closed, with bounded point sets),
  transported from `janiszewski_compact` through `ptsOf` (components correspond:
  `ptsOf_connectedComponentIn`).
* **Theorem 13**: Moore's proof. If `x`, `y` are elements of `R − k`, the boundary `B` of `R` does not
  separate them (`R` is connected and misses `B`), nor does `k` (`G − k` is connected: Theorem 9, or
  `isConnected_compl_singleton_quot`), and `k ∩ B` is empty or one element. By Janiszewski, `k + B`
  does not separate them; the component of `x` misses `B`, so lies in `R`, and misses `k`. That
  `R − k` is not empty (for `IsConnected`) is not in Moore's text: a region is infinite, and an
  arc has no interior (`not_subset_arc_of_cut`).
* **Theorem 14**: Moore's proof. Two elements `p ≠ q` of `R` (F.A. Theorem 4: a region is
  infinite); an arc `pxq` in `R` (F.A. Theorem 15); an element `x` of it other than `p`, `q`; an arc
  `pyq` in the domain `R − x` (Theorem 13). Moore's \"It is easy to see that the sum of the arcs `pxq`
  and `pyq` contains as a subset a simple closed curve\" is `exists_tscc_of_arcs`: the last element of
  `pyq` on `pxq` before `x` and the first one after `x` bound a sub-arc of `pxq` through `x` meeting
  `pyq` only in its ends, which with the sub-arc of `pyq` between them is a closed curve.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Gen

variable {r : Setoid Pt}

/-! ### Sub-arcs of two arcs (general topology) -/

section General

variable {T : Type*} [TopologicalSpace T] [T2Space T]

/-- **The sub-arc argument of Theorem 14.** If `x` is a point of the arc `X` (from `p` to `q`) not on
the arc `Y`, and `Y` contains `p` and `q`, then `X ∪ Y` contains a closed curve through `x`. -/
theorem exists_tscc_of_arcs {p q p' q' x : T} {X Y : Set T} (hX : TArc p q X) (hY : TArc p' q' Y)
    (hp : p ∈ Y) (hq : q ∈ Y) (hxX : x ∈ X) (hxY : x ∉ Y) :
    ∃ J ⊆ X ∪ Y, TSCC J ∧ x ∈ J ∧ ∃ A B : T, ∃ Xs Ys : Set T, Xs ⊆ X ∧ Ys ⊆ Y ∧
      TArc A B Xs ∧ TArc A B Ys ∧ Xs ∩ Ys = {A, B} ∧ J = Xs ∪ Ys ∧ x ∈ Xs := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hX
  obtain ⟨m, rfl⟩ := hxX
  have hZc : IsClosed (f ⁻¹' Y) := hY.isClosed.preimage hf.continuous
  have hbdd : BddAbove (f ⁻¹' Y ∩ Iic m) := ⟨1, fun _ _ => unitInterval.le_one'⟩
  have hbdd' : BddBelow (f ⁻¹' Y ∩ Ici m) := ⟨0, fun _ _ => unitInterval.nonneg'⟩
  have hne : (f ⁻¹' Y ∩ Iic m).Nonempty := ⟨0, hp, unitInterval.nonneg'⟩
  have hne' : (f ⁻¹' Y ∩ Ici m).Nonempty := ⟨1, hq, unitInterval.le_one'⟩
  set s := sSup (f ⁻¹' Y ∩ Iic m)
  set t := sInf (f ⁻¹' Y ∩ Ici m)
  have hs : s ∈ f ⁻¹' Y ∩ Iic m := (hZc.inter isClosed_Iic).csSup_mem hne hbdd
  have ht : t ∈ f ⁻¹' Y ∩ Ici m := (hZc.inter isClosed_Ici).csInf_mem hne' hbdd'
  have hsm : s < m := lt_of_le_of_ne hs.2 fun e => hxY (e ▸ hs.1)
  have hmt : m < t := lt_of_le_of_ne ht.2 fun e => hxY (e ▸ ht.1)
  have hst : s < t := hsm.trans hmt
  have hfst : f s ≠ f t := fun e => hst.ne (hf.injective e)
  obtain ⟨Ys, hYsY, hYs⟩ := hY.exists_sub hs.1 ht.1 hfst
  have hXs : TArc (f s) (f t) (f '' Icc s t) := TArc.image_Icc hf hst
  have hint : f '' Icc s t ∩ Ys = {f s, f t} := by
    apply subset_antisymm
    · rintro _ ⟨⟨u, ⟨hsu, hut⟩, rfl⟩, hu⟩
      have huY : u ∈ f ⁻¹' Y := hYsY hu
      rcases le_total u m with h | h
      · have : u ≤ s := le_csSup hbdd ⟨huY, h⟩
        exact Or.inl (by rw [le_antisymm this hsu])
      · have : t ≤ u := csInf_le hbdd' ⟨huY, h⟩
        exact Or.inr (by rw [le_antisymm hut this]; rfl)
    · rintro _ (rfl | rfl)
      · exact ⟨⟨s, ⟨le_rfl, hst.le⟩, rfl⟩, hYs.left_mem⟩
      · exact ⟨⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, hYs.right_mem⟩
  have hxXs : f m ∈ f '' Icc s t := ⟨m, ⟨hsm.le, hmt.le⟩, rfl⟩
  refine ⟨f '' Icc s t ∪ Ys, union_subset_union (image_subset_range _ _) hYsY,
    ⟨f s, f t, _, _, hXs, hYs, hint, rfl⟩, Or.inl hxXs, f s, f t, _, Ys,
    image_subset_range _ _, hYsY, hXs, hYs, hint, rfl, hxXs⟩

/-- An open set meeting an arc only inside it, at a point other than the ends, is not contained in
the arc: an arc has no interior point other than possibly its ends, in this weak form. -/
theorem not_subset_arc_of_cut {A B x : T} {k U : Set T} (hk : TArc A B k) (hUo : IsOpen U)
    (hxU : x ∈ U) (hxk : x ∈ k) (hxA : x ≠ A) (hxB : x ≠ B) (hUk : U ⊆ k)
    (hU : IsPreconnected (U \ {x})) : False := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hk
  obtain ⟨t, rfl⟩ := hxk
  have ht0 : 0 < t := lt_of_le_of_ne unitInterval.nonneg' fun e => hxA (by rw [← e])
  have ht1 : t < 1 := lt_of_le_of_ne unitInterval.le_one' fun e => hxB (by rw [e])
  have hF₁ : IsClosed (f '' Icc 0 t) := (isCompact_Icc.image hf.continuous).isClosed
  have hF₂ : IsClosed (f '' Icc t 1) := (isCompact_Icc.image hf.continuous).isClosed
  have hcov : U \ {f t} ⊆ f '' Icc 0 t ∪ f '' Icc t 1 := by
    rintro z ⟨hz, -⟩
    obtain ⟨u, rfl⟩ := hUk hz
    rcases le_total u t with h | h
    · exact Or.inl ⟨u, ⟨unitInterval.nonneg', h⟩, rfl⟩
    · exact Or.inr ⟨u, ⟨h, unitInterval.le_one'⟩, rfl⟩
  -- points of `U` on each side of `f t`
  have hside : ∀ c d : unitInterval, t ∈ closure (Ioo c d) → ∃ u ∈ Ioo c d, f u ∈ U := by
    intro c d hcl
    have h1 : f t ∈ closure (f '' Ioo c d) := image_closure_subset_closure_image hf.continuous
      ⟨t, hcl, rfl⟩
    obtain ⟨_, hzU, ⟨u, hu, rfl⟩⟩ := mem_closure_iff.1 h1 U hUo hxU
    exact ⟨u, hu, hzU⟩
  obtain ⟨u₁, hu₁, hu₁U⟩ := hside 0 t (by rw [closure_Ioo ht0.ne]; exact ⟨ht0.le, le_rfl⟩)
  obtain ⟨u₂, hu₂, hu₂U⟩ := hside t 1 (by rw [closure_Ioo ht1.ne]; exact ⟨le_rfl, ht1.le⟩)
  obtain ⟨z, ⟨hzU, hzt⟩, hz1, hz2⟩ := isPreconnected_closed_iff.1 hU _ _ hF₁ hF₂ hcov
    ⟨f u₁, ⟨hu₁U, fun e => hu₁.2.ne (hf.injective e)⟩, ⟨u₁, ⟨unitInterval.nonneg', hu₁.2.le⟩, rfl⟩⟩
    ⟨f u₂, ⟨hu₂U, fun e => hu₂.1.ne' (hf.injective e)⟩, ⟨u₂, ⟨hu₂.1.le, unitInterval.le_one'⟩, rfl⟩⟩
  obtain ⟨v, ⟨-, hvt⟩, rfl⟩ := hz1
  obtain ⟨w, ⟨htw, -⟩, hw⟩ := hz2
  have := hf.injective hw; subst this
  exact hzt (by rw [le_antisymm hvt htw]; rfl)

end General

section M25C13

variable (hG : MooreDecomp r)
include hG

/-- **Janiszewski's theorem for sets of elements.** -/
theorem quot_janiszewski {A B : Set (Quotient r)} (hA : IsClosed A)
    (hAb : Bornology.IsBounded (ptsOf r A)) (hB : IsClosed B)
    (hBb : Bornology.IsBounded (ptsOf r B)) (hAB : IsConnected (A ∩ B) ∨ A ∩ B = ∅)
    {x y : Quotient r} (hxA : x ∉ A) (hxB : x ∉ B) (hyA : y ∉ A) (hyB : y ∉ B)
    (hyA' : y ∈ connectedComponentIn Aᶜ x) (hyB' : y ∈ connectedComponentIn Bᶜ x) :
    y ∈ connectedComponentIn (A ∪ B)ᶜ x := by
  obtain ⟨X, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨Y, rfl⟩ := Quotient.mk_surjective y
  have hcomp : ∀ W : Set (Quotient r), Quotient.mk r Y ∈ connectedComponentIn Wᶜ (Quotient.mk r X) ↔
      Y ∈ connectedComponentIn (ptsOf r W)ᶜ X := fun W => by
    rw [← ptsOf_compl, ← ptsOf_connectedComponentIn hG]; rfl
  have hAc : IsCompact (ptsOf r A) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_iff_ptsOf.1 hA) hAb
  have hBc : IsCompact (ptsOf r B) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_iff_ptsOf.1 hB) hBb
  have hAB' : IsConnected (ptsOf r A ∩ ptsOf r B) ∨ ptsOf r A ∩ ptsOf r B = ∅ := by
    rcases hAB with h | h
    · exact Or.inl (isConnected_ptsOf hG h)
    · right; change ptsOf r (A ∩ B) = ∅; rw [h]; rfl
  have key := janiszewski_compact hAc hBc hAB' (x := X) (y := Y)
    (fun h => h.2.2 ((hcomp A).1 hyA')) (fun h => h.2.2 ((hcomp B).1 hyB'))
  rw [hcomp (A ∪ B)]
  by_contra hc
  exact key ⟨fun h => h.elim hxA hxB, fun h => h.elim hyA hyB, hc⟩

/-- A Moore region minus a closed bounded set `k` with connected complement, meeting the boundary
in a connected set or not at all, is preconnected (Moore's proof of Theorem 13). -/
theorem isPreconnected_region_diff {R k : Set (Quotient r)} (hR : mooreRegion R)
    (hkc : IsClosed k) (hkb : Bornology.IsBounded (ptsOf r k)) (hkcompl : IsConnected kᶜ)
    (hkB : IsConnected (k ∩ frontier R) ∨ k ∩ frontier R = ∅) : IsPreconnected (R \ k) := by
  obtain ⟨hRo, hRc, hRb, -⟩ := hR
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  have hxB : x ∉ frontier R := fun h => (Gen.notMem_of_mem_frontier hRo h) hx.1
  have hyB : y ∉ frontier R := fun h => (Gen.notMem_of_mem_frontier hRo h) hy.1
  have hRsub : R ⊆ connectedComponentIn (frontier R)ᶜ x :=
    hRc.isPreconnected.subset_connectedComponentIn hx.1
      (fun z hz hzB => (Gen.notMem_of_mem_frontier hRo hzB) hz)
  have hksub : kᶜ ⊆ connectedComponentIn kᶜ x :=
    hkcompl.isPreconnected.subset_connectedComponentIn hx.2 subset_rfl
  have hy' := quot_janiszewski hG hkc hkb isClosed_frontier (isBounded_ptsOf_frontier hG hRb) hkB
    hx.2 hxB hy.2 hyB (hksub hy.2) (hRsub hy.1)
  refine ⟨connectedComponentIn (k ∪ frontier R)ᶜ x, ?_, mem_connectedComponentIn
    (show x ∈ (k ∪ frontier R)ᶜ from fun h => h.elim hx.2 hxB), hy',
    isPreconnected_connectedComponentIn⟩
  have hsub := connectedComponentIn_subset (k ∪ frontier R)ᶜ x
  have hCR : connectedComponentIn (k ∪ frontier R)ᶜ x ⊆ R := by
    refine Gen.conn_sub_of_frontier isPreconnected_connectedComponentIn ?_
      ⟨x, mem_connectedComponentIn (show x ∈ (k ∪ frontier R)ᶜ from fun h => h.elim hx.2 hxB),
        hx.1⟩
    exact disjoint_left.2 fun z hz hzB => hsub hz (Or.inr hzB)
  exact fun z hz => ⟨hCR hz, fun hzk => hsub hz (Or.inl hzk)⟩

/-- **Theorem 13** (p. 422). If `R` is a region and `k` is either a single element or an arc every
element of which, except possibly one end element, belongs to `R`, then `R − k` is a domain. -/
theorem m25_theorem13 {R k : Set (Quotient r)} (hR : mooreRegion R)
    (hk : (∃ e, k = {e}) ∨ ∃ a b, IsArcElt a b k ∧ (k \ {a} ⊆ R ∨ k \ {b} ⊆ R)) :
    IsOpen (R \ k) ∧ IsConnected (R \ k) := by
  haveI := t1Space_quot hG
  have hRo := hR.1
  have hkB : ∀ e, k \ {e} ⊆ R → IsConnected (k ∩ frontier R) ∨ k ∩ frontier R = ∅ := by
    intro e he
    have hsub : k ∩ frontier R ⊆ {e} := by
      rintro z ⟨hzk, hzB⟩
      by_contra hze
      exact Gen.notMem_of_mem_frontier hRo hzB (he ⟨hzk, hze⟩)
    rcases (subset_singleton_iff_eq.1 hsub) with h | h
    · exact Or.inr h
    · rw [h]; exact Or.inl isConnected_singleton
  -- the single-element case
  have hsingle : ∀ e : Quotient r, IsOpen (R \ {e}) ∧ IsConnected (R \ {e}) := by
    intro e
    refine ⟨hRo.sdiff isClosed_singleton, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := (m25_region_infinite hG hR hR.2.1.nonempty).diff (finite_singleton e)
        |>.nonempty
      exact ⟨z, hz⟩
    · refine isPreconnected_region_diff hG hR isClosed_singleton
        (isCompact_ptsOf_singleton hG e).isBounded (isConnected_compl_singleton_quot hG e) ?_
      by_cases he : e ∈ frontier R
      · left; rw [inter_eq_left.2 (singleton_subset_iff.2 he)]; exact isConnected_singleton
      · right; rw [singleton_inter_eq_empty.2 he]
  rcases hk with ⟨e, rfl⟩ | ⟨a, b, hab, hkR⟩
  · exact hsingle e
  have hkc : IsClosed k := hab.2.1
  refine ⟨hRo.sdiff hkc, ?_, ?_⟩
  · -- `R − k ≠ ∅`: an open set inside an arc would have no cut points
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hemp
    obtain ⟨x, hx⟩ := ((m25_region_infinite hG hR hR.2.1.nonempty).diff
      (toFinite {a, b})).nonempty
    simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or] at hx
    haveI := t2Space_quot hG
    exact not_subset_arc_of_cut ((isArcElt_iff_tarc hG).1 hab) hRo hx.1 (hemp hx.1) hx.2.1
      hx.2.2 hemp (hsingle x).2.isPreconnected
  · refine isPreconnected_region_diff hG hR hkc hab.2.2.2.1 (m25_theorem9 hG hab) ?_
    rcases hkR with h | h
    · exact hkB a h
    · exact hkB b h

/-- **Theorem 14** (p. 423). Every region contains a simple closed curve of elements. -/
theorem m25_theorem14 {R : Set (Quotient r)} (hR : mooreRegion R) :
    ∃ J, IsSCCElt J ∧ J ⊆ R := by
  haveI := t2Space_quot hG
  -- two elements `p ≠ q` of `R`
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    (m25_region_infinite hG hR hR.2.1.nonempty).nontrivial
  -- the arc `pxq` in `R`, and an element `x` of it other than `p`, `q`
  obtain ⟨X, hXR, hX⟩ := arcConn_quot hG R hR.1 hR.2.1.isPreconnected p hp q hq hpq
  obtain ⟨x, hxX, hxpq⟩ := hX.nonempty_diff
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxpq
  -- the arc `pyq` in the domain `R − x`
  obtain ⟨hRxo, hRxc⟩ := m25_theorem13 hG hR (k := {x}) (Or.inl ⟨x, rfl⟩)
  obtain ⟨Y, hYR, hY⟩ := arcConn_quot hG _ hRxo hRxc.isPreconnected p ⟨hp, hxpq.1 ∘ Eq.symm⟩
    q ⟨hq, hxpq.2 ∘ Eq.symm⟩ hpq
  -- \"the sum of the arcs `pxq` and `pyq` contains as a subset a simple closed curve\"
  obtain ⟨J, hJXY, hJ, -⟩ := exists_tscc_of_arcs hX hY hY.left_mem hY.right_mem hxX
    (fun h => (hYR h).2 rfl)
  exact ⟨J, (isSCCElt_iff_tscc hG).2 hJ, hJXY.trans (union_subset hXR fun z hz => (hYR hz).1)⟩

end M25C13

end HPC.Moore
