import HPC.Hagopian.H76Follows

/-!
# Batch 170, item B (first step): components of `π⁻¹[D] − Z` reach the frontier

Commission 170 §1.B, first step: if `Z` is a proper subcontinuum of `M`, no proper subcontinuum of
`M` separates the plane (`no_proper_subcontinuum_separates`), so no component `U` of `O − Z`
(`O` a bounded open set, Hagopian's `π⁻¹[D]`) has `Fr U ⊆ Z`: the closure of every such component
meets `Fr O`. The three cases of §1.B (bottom, `I₂`, pockets at the side edges) are not done here.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- A component of `O − Z` (`O` open and bounded, `Z` compact with connected complement) has closure
meeting `Fr O`. -/
theorem component_frontier_meets {O Z : Set Pt} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hZ : IsCompact Z) (hns : IsConnected Zᶜ) {x : Pt} (hx : x ∈ O \ Z) :
    (closure (connectedComponentIn (O \ Z) x) ∩ frontier O).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  set U := connectedComponentIn (O \ Z) x with hU
  have hOZ : IsOpen (O \ Z) := hO.sdiff hZ.isClosed
  have hUo : IsOpen U := hOZ.connectedComponentIn
  have hUsub : U ⊆ O \ Z := connectedComponentIn_subset _ _
  have hcl : closure U ∩ Zᶜ ⊆ U := by
    rintro y ⟨hyU, hyZ⟩
    have hyO : y ∈ O := by
      have hy' : y ∈ closure O := closure_mono (hUsub.trans diff_subset) hyU
      by_contra hyO
      have : y ∈ frontier O := ⟨hy', by rwa [hO.interior_eq]⟩
      have : y ∈ closure U ∩ frontier O := ⟨hyU, this⟩
      rw [hne] at this
      exact this
    have hyV : y ∈ connectedComponentIn (O \ Z) y := mem_connectedComponentIn ⟨hyO, hyZ⟩
    obtain ⟨w, hwV, hwU⟩ := mem_closure_iff.1 hyU _ hOZ.connectedComponentIn hyV
    rw [hU, connectedComponentIn_eq hwU, ← connectedComponentIn_eq hwV]
    exact hyV
  have hsub : Zᶜ ⊆ U := hns.isPreconnected.subset_of_closure_inter_subset hUo
    ⟨x, hx.2, mem_connectedComponentIn hx⟩ hcl
  have hb : Bornology.IsBounded (univ : Set Pt) := by
    rw [← union_compl_self Z]
    exact hZ.isBounded.union (hOb.subset (hsub.trans (hUsub.trans diff_subset)))
  exact NormedSpace.unbounded_univ ℝ Pt hb

section Cover

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **B, first step.** For a proper subcontinuum `K` of `M` and a bounded open `O ⊆ R²`, the closure
of every component of `O − K` meets `Fr O`. -/
theorem component_frontier_meets_of_subcontinuum (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {K : Set M} (hK : Fold.Q78.IsContinuum K) (hKM : K ≠ univ)
    {O : Set Pt} (hO : IsOpen O) (hOb : Bornology.IsBounded O) {x : Pt} (hx : x ∈ O \ toPt K) :
    (closure (connectedComponentIn (O \ toPt K) x) ∩ frontier O).Nonempty := by
  have hns := no_proper_subcontinuum_separates hX hi hK hKM
  unfold SeparatesPlane at hns
  rw [not_not] at hns
  exact component_frontier_meets hO hOb (hK.1.image continuous_subtype_val) hns hx

/-- **B, first step, in the set-up of T17.** For a continuous `π` and a proper subcontinuum `K` of
`M`, the closure of every component of `π⁻¹[D] − K` (`π⁻¹[D]` bounded) meets `π⁻¹[Fr D]`; with
`hagopian76_D`'s frontier, `π⁻¹[I₂ ∪ bottom edge ∪ side edges]`. -/
theorem component_reaches_frontier_D (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {K : Set M} (hK : Fold.Q78.IsContinuum K) (hKM : K ≠ univ) {π : Pt → Pt} (hπc : Continuous π)
    {D : Set Pt} (hD : IsOpen D) (hDb : Bornology.IsBounded (π ⁻¹' D)) {x : Pt}
    (hx : x ∈ π ⁻¹' D \ toPt K) :
    (closure (connectedComponentIn (π ⁻¹' D \ toPt K) x) ∩ π ⁻¹' frontier D).Nonempty := by
  obtain ⟨y, hy, hyf⟩ :=
    component_frontier_meets_of_subcontinuum hX hi hK hKM (hD.preimage hπc) hDb hx
  exact ⟨y, hy, hπc.frontier_preimage_subset D hyf⟩

end Cover

end HPC.Hagopian
