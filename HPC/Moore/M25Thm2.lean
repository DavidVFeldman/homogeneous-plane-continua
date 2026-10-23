import HPC.Moore.M25Thm

/-!
# Batch 145, item D: Moore 1925, Theorem 2

Moore's proof (pp. 418–419), in the quotient topology, with Janiszewski's theorem applied to the
point sets. Let `D` be the component of `Mᶜ` containing `x`, `E` the component of `(∂D)ᶜ`
containing `y` (unbounded), `K = ∂E`, `p ∈ K`.

* `K` is closed; `K` is connected by Brouwer twice (`quot_brouwer`: `∂D` is connected, then
  `∂E`). This is what supplies Moore's "B is a closed and connected set".
* `D ∩ E = ∅` (else `E ⊆ D` and `E` would be bounded).
* `K − p ≠ ∅`: otherwise `E` would be all of `{p}ᶜ` (connected, since `p̄` does not separate the
  plane), which contains `D`.
* If `K − p = H ∪ N` (mutually separated), neither `(H + p)‾` nor `(N + p)‾` separates `x̄` from
  `ȳ` (Moore's argument with `D_x` and `q ∈ N`), they are compact and meet in the continuum `p̄`,
  so by `janiszewski_compact` their union `K̄` does not separate `x̄` from `ȳ`; but it does.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

section hG

variable (hG : MooreDecomp r)
include hG

/-- Plane separation by a closed set of elements gives separation in the quotient. -/
theorem not_mem_component_of_separates {F : Set (Quotient r)} {X Y : Pt}
    (h : SeparatesPts (ptsOf r F) X Y) :
    Quotient.mk r Y ∉ connectedComponentIn Fᶜ (Quotient.mk r X) := by
  intro hY
  have : Y ∈ ptsOf r (connectedComponentIn Fᶜ (Quotient.mk r X)) := hY
  rw [ptsOf_connectedComponentIn hG, ptsOf_compl] at this
  exact h.2.2 this

/-- **Theorem 2** (p. 418). If `D` is a bounded complementary domain of a bounded continuum of
elements `M`, `K` the outer boundary of `D`, and `p ∈ K`, then `K` is a continuum of elements and
`K − p` is connected.

*Reading* (skeleton): complementary domain = component of the complement; the outer boundary of
`D` is the frontier of an unbounded component `E` of `(∂D)ᶜ` (unique by `m25_unbounded_unique`). -/
theorem m25_theorem2 {M : Set (Quotient r)} (hM : IsClosed M) (hMc : IsConnected M)
    (hMb : Bornology.IsBounded (ptsOf r M)) {x : Quotient r} (hx : x ∉ M)
    (hDb : Bornology.IsBounded (ptsOf r (connectedComponentIn Mᶜ x)))
    {y : Quotient r} (hy : y ∉ frontier (connectedComponentIn Mᶜ x))
    (hE : ¬ Bornology.IsBounded
      (ptsOf r (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y)))
    {p : Quotient r}
    (hp : p ∈ frontier (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y)) :
    IsClosed (frontier (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y)) ∧
      IsConnected (frontier (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y)) ∧
      IsConnected
        (frontier (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y) \ {p}) := by
  haveI := locallyConnectedSpace_quot hG
  haveI := t1Space_quot hG
  set D := connectedComponentIn Mᶜ x with hDdef
  set E := connectedComponentIn (frontier D)ᶜ y with hEdef
  set K := frontier E with hKdef
  have hDo : IsOpen D := hM.isOpen_compl.connectedComponentIn
  have hxD : x ∈ D := mem_connectedComponentIn hx
  have hDc : IsConnected D := isConnected_connectedComponentIn_iff.2 hx
  have hEo : IsOpen E := isClosed_frontier.isOpen_compl.connectedComponentIn
  have hyE : y ∈ E := mem_connectedComponentIn hy
  have hEc : IsConnected E := isConnected_connectedComponentIn_iff.2 hy
  have hfrD : frontier D ⊆ M := fun z hz => by
    simpa using frontier_connectedComponentIn_subset hM.isOpen_compl x hz
  have hKD : K ⊆ frontier D := fun z hz => by
    simpa using frontier_connectedComponentIn_subset isClosed_frontier.isOpen_compl y hz
  have hDK : Disjoint D K := by
    rw [disjoint_left]; intro z hzD hzK
    have := hKD hzK; rw [hDo.frontier_eq] at this; exact this.2 hzD
  have hEK : Disjoint E K := by
    rw [disjoint_left]; intro z hzE hzK
    rw [hKdef, hEo.frontier_eq] at hzK; exact hzK.2 hzE
  have hEfD : E ⊆ (frontier D)ᶜ := connectedComponentIn_subset _ _
  -- `D` and `E` are disjoint
  have hDE : Disjoint D E := by
    rw [disjoint_left]
    intro z hzD hzE
    have hED : E ⊆ D := subset_of_preconnected_of_disjoint_frontier hEc.isPreconnected hDo
      ⟨z, hzE, hzD⟩ (disjoint_left.2 fun w hw hwf => hEfD hw hwf)
    exact hE (hDb.subset (ptsOf_mono hED))
  have hxK : x ∉ K := fun h => disjoint_left.1 hDK hxD h
  have hpK : p ∈ K := hp
  have hpD : p ∉ D := fun h => disjoint_left.1 hDK h hpK
  have hKc : IsConnected K := quot_brouwer hG isClosed_frontier (quot_brouwer hG hM hMc hx) hy
  have hKb : Bornology.IsBounded (ptsOf r K) := hMb.subset (ptsOf_mono (hKD.trans hfrD))
  refine ⟨isClosed_frontier, hKc, ?_, ?_⟩
  · -- `K − p` is nonempty
    by_contra hne
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hne
    obtain ⟨X0, rfl⟩ := Quotient.mk_surjective p
    have hpc : IsConnected ({Quotient.mk r X0}ᶜ : Set (Quotient r)) := by
      have h1 : IsConnected (ptsOf r {Quotient.mk r X0})ᶜ := by
        rw [ptsOf_singleton]; exact not_not.1 (hG.nonsep X0)
      have := h1.image (Quotient.mk r) (continuous_mk (r := r)).continuousOn
      rwa [← ptsOf_compl, image_ptsOf] at this
    have hsub : ({Quotient.mk r X0}ᶜ : Set (Quotient r)) ⊆ E := by
      refine subset_of_preconnected_of_disjoint_frontier hpc.isPreconnected hEo
        ⟨y, ?_, hyE⟩ ?_
      · rintro rfl; exact disjoint_left.1 hEK hyE hpK
      · rw [disjoint_left]; intro z hz hzK; exact hz (hne hzK)
    exact disjoint_left.1 hDE hxD (hsub fun h => hpD (h ▸ hxD))
  · -- `K − p` is preconnected
    by_contra hnc
    rw [isPreconnected_iff_subset_of_disjoint] at hnc
    push_neg at hnc
    obtain ⟨u, v, hu, hv, hSuv, hSuv', hSu, hSv⟩ := hnc
    set S := K \ {p} with hS
    set H := S ∩ u
    set N := S ∩ v
    have hHN : H ∪ N = S := by
      rw [← inter_union_distrib_left]; exact inter_eq_left.2 hSuv
    have hdisj : Disjoint H N := by
      rw [disjoint_left]; rintro z ⟨hzS, hzu⟩ ⟨-, hzv⟩
      exact (eq_empty_iff_forall_notMem.1 hSuv') z ⟨hzS, hzu, hzv⟩
    have hHne : N.Nonempty := by
      obtain ⟨z, hzS, hzu⟩ := not_subset.1 hSu
      exact ⟨z, hzS, (hSuv hzS).resolve_left hzu⟩
    have hNne : H.Nonempty := by
      obtain ⟨z, hzS, hzv⟩ := not_subset.1 hSv
      exact ⟨z, hzS, (hSuv hzS).resolve_right hzv⟩
    -- `H ∪ {p}` and `N ∪ {p}` are closed
    have hclosed : ∀ (A B : Set (Quotient r)) (w : Set (Quotient r)), IsOpen w → A ∪ B = S →
        B ⊆ w → Disjoint A w → IsClosed (A ∪ {p}) := by
      intro A B w hw hAB hBw hAw
      rw [← closure_subset_iff_isClosed, closure_union, closure_singleton]
      refine union_subset (fun z hz => ?_) subset_union_right
      have hzK : z ∈ K := isClosed_frontier.closure_subset_iff.2
        (fun a ha => (hAB ▸ (subset_union_left : A ⊆ A ∪ B) ha : a ∈ S).1) hz
      by_cases hzp : z = p
      · exact Or.inr hzp
      have hzS : z ∈ S := ⟨hzK, hzp⟩
      rw [← hAB] at hzS
      rcases hzS with h | h
      · exact Or.inl h
      · exact absurd (hBw h) (disjoint_left.1 (hAw.closure_left hw) hz)
    have hHcl : IsClosed (H ∪ {p}) := hclosed H N v hv hHN inter_subset_right
      (by rw [disjoint_left]; rintro z ⟨hzS, hzu⟩ hzv
          exact (eq_empty_iff_forall_notMem.1 hSuv') z ⟨hzS, hzu, hzv⟩)
    have hNcl : IsClosed (N ∪ {p}) := hclosed N H u hu (by rw [union_comm]; exact hHN)
      inter_subset_right
      (by rw [disjoint_left]; rintro z ⟨hzS, hzv⟩ hzu
          exact (eq_empty_iff_forall_notMem.1 hSuv') z ⟨hzS, hzu, hzv⟩)
    obtain ⟨X, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨Y, rfl⟩ := Quotient.mk_surjective y
    -- Moore's argument: `A ∪ {p}` does not separate when the other part `B` is nonempty
    have side : ∀ A B : Set (Quotient r), A ∪ B = S → Disjoint A B → B.Nonempty →
        IsClosed (A ∪ {p}) → ¬ SeparatesPts (ptsOf r (A ∪ {p})) X Y := by
      intro A B hAB hABd hBne hAcl hsep
      set F := A ∪ {p}
      have hFK : F ⊆ K := union_subset
        (fun a ha => (hAB ▸ (subset_union_left : A ⊆ A ∪ B) ha : a ∈ S).1)
        (singleton_subset_iff.2 hpK)
      have hyDx := not_mem_component_of_separates hG hsep
      set Dx := connectedComponentIn Fᶜ (Quotient.mk r X)
      have hxF : Quotient.mk r X ∉ F := fun h => hxK (hFK h)
      have hDxo : IsOpen Dx := hAcl.isOpen_compl.connectedComponentIn
      have hDDx : D ⊆ Dx := hDc.isPreconnected.subset_connectedComponentIn hxD
        (fun z hzD hzF => disjoint_left.1 hDK hzD (hFK hzF))
      have hfrDx : frontier Dx ⊆ F := fun z hz => by
        simpa using frontier_connectedComponentIn_subset hAcl.isOpen_compl _ hz
      obtain ⟨q, hqB⟩ := hBne
      have hqS : q ∈ S := hAB ▸ (subset_union_right : B ⊆ A ∪ B) hqB
      have hqF : q ∉ F := by
        rintro (h | h)
        · exact disjoint_left.1 hABd h hqB
        · exact hqS.2 h
      have hqDx : q ∈ Dx := by
        have hqcl : q ∈ closure Dx := closure_mono hDDx (frontier_subset_closure (hKD hqS.1))
        by_contra hq
        exact hqF (hfrDx ⟨hqcl, by rw [hDxo.interior_eq]; exact hq⟩)
      have hEDx : E ⊆ Dx := by
        refine subset_of_preconnected_of_disjoint_frontier hEc.isPreconnected hDxo ?_ ?_
        · obtain ⟨w, hwDx, hwE⟩ := mem_closure_iff.1 (frontier_subset_closure hqS.1) Dx hDxo hqDx
          exact ⟨w, hwE, hwDx⟩
        · rw [disjoint_left]; intro z hzE hz
          exact disjoint_left.1 hEK hzE (hFK (hfrDx hz))
      exact hyDx (hEDx hyE)
    have hP1 : IsCompact (ptsOf r (N ∪ {p})) :=
      Metric.isCompact_of_isClosed_isBounded (isClosed_iff_ptsOf.1 hNcl)
        (hKb.subset (ptsOf_mono (union_subset (inter_subset_left.trans diff_subset)
          (singleton_subset_iff.2 hpK))))
    have hP2 : IsCompact (ptsOf r (H ∪ {p})) :=
      Metric.isCompact_of_isClosed_isBounded (isClosed_iff_ptsOf.1 hHcl)
        (hKb.subset (ptsOf_mono (union_subset (inter_subset_left.trans diff_subset)
          (singleton_subset_iff.2 hpK))))
    have hinter : ptsOf r (N ∪ {p}) ∩ ptsOf r (H ∪ {p}) = ptsOf r {p} := by
      simp only [ptsOf]
      rw [← preimage_inter, ← inter_union_distrib_right, hdisj.symm.inter_eq, empty_union]
    have hunion : ptsOf r (N ∪ {p}) ∪ ptsOf r (H ∪ {p}) = ptsOf r K := by
      simp only [ptsOf]
      rw [← preimage_union]
      congr 1
      ext z
      constructor
      · rintro ((h | h) | (h | h))
        · exact h.1.1
        · rw [h]; exact hpK
        · exact h.1.1
        · rw [h]; exact hpK
      · intro hz
        by_cases hzp : z = p
        · exact Or.inl (Or.inr hzp)
        have hzS : z ∈ S := ⟨hz, hzp⟩
        rw [← hHN] at hzS
        rcases hzS with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inl h)
    have hjan := janiszewski_compact hP1 hP2
      (Or.inl (hinter ▸ isConnected_ptsOf_singleton hG p))
      (side N H (by rw [union_comm]; exact hHN) hdisj.symm hNne hNcl)
      (side H N hHN hdisj hHne hHcl)
    rw [hunion] at hjan
    refine hjan ⟨hxK, fun h => disjoint_left.1 hEK hyE h, fun hY => ?_⟩
    have hY' : Quotient.mk r Y ∈ connectedComponentIn Kᶜ (Quotient.mk r X) := by
      have : Y ∈ ptsOf r (connectedComponentIn Kᶜ (Quotient.mk r X)) := by
        rw [ptsOf_connectedComponentIn hG, ptsOf_compl]; exact hY
      exact this
    have hCE : connectedComponentIn Kᶜ (Quotient.mk r X) ⊆ E :=
      subset_of_preconnected_of_disjoint_frontier isPreconnected_connectedComponentIn hEo
        ⟨_, hY', hyE⟩ (disjoint_left.2 fun z hz hzK => connectedComponentIn_subset _ _ hz hzK)
    exact disjoint_left.1 hDE hxD (hCE (mem_connectedComponentIn hxK))

end hG

end HPC.Moore
