import HPC.Hagopian.H75Kur
import HPC.Jones.Basic
import HPC.Plane.Composant91

/-!
# Batch 155, item B: composants (Moore 1962, Theorems 135–139, pp. 58–59)

In a compact connected metric space `X`:

* `composant_dense'` (Moore 135): every composant of a nondegenerate `X` is dense — boundary bumping,
  `HPC.Plane.exists_proper_subcontinuum_meeting` (batch 91);
* `union_ne_univ_of_indec`: two proper subcontinua of an indecomposable `X` with a common point have
  a proper union (this is Moore 138's argument);
* `composant_eq_or_disjoint'` (Moore 138);
* `composant_isMeagre'` (Moore 136–137): the composant of `x` is covered by the components of `x` in
  `X ∖ b`, `b` running over a countable basis; each is a proper subcontinuum, which has empty interior
  (`HPC.T13.false_of_interior`, batch 81);
* `uncountable_composants'` (Moore 139): Baire.
-/

namespace HPC.Hagopian

open Set Topology HPC.Jones

section Composants

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Moore 135.** -/
theorem composant_dense' [Nontrivial X] (x : X) : Dense (Jones.composant x) := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨z, hz⟩
  have hnd : (univ : Set X).Nontrivial := nontrivial_univ
  obtain ⟨K, -, hKne, hK, hxK, y, hyK, hyO⟩ :=
    HPC.Plane.exists_proper_subcontinuum_meeting (Jones.isContinuum_univ) hnd (mem_univ x) hO
      ⟨z, hz, mem_univ z⟩
  exact ⟨y, hyO, K, hK, hKne, hxK, hyK⟩

omit [CompactSpace X] [ConnectedSpace X] in
/-- In an indecomposable continuum the union of two proper subcontinua with a common point is a
proper subcontinuum. -/
theorem union_ne_univ_of_indec (hi : ¬ IsDecomposableSpace X) {H K : Set X}
    (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K) (hHu : H ≠ univ) (hKu : K ≠ univ) :
    H ∪ K ≠ univ := fun h => hi ⟨H, K, hH, hK, hHu, hKu, h⟩

omit [CompactSpace X] [ConnectedSpace X] in
theorem composant_symm {x y : X} (h : y ∈ Jones.composant x) : x ∈ Jones.composant y := by
  obtain ⟨K, hK, hKu, hxK, hyK⟩ := h
  exact ⟨K, hK, hKu, hyK, hxK⟩

omit [CompactSpace X] [ConnectedSpace X] in
theorem composant_trans (hi : ¬ IsDecomposableSpace X) {x y z : X} (h₁ : y ∈ Jones.composant x)
    (h₂ : z ∈ Jones.composant y) : z ∈ Jones.composant x := by
  obtain ⟨K, hK, hKu, hxK, hyK⟩ := h₁
  obtain ⟨L, hL, hLu, hyL, hzL⟩ := h₂
  exact ⟨K ∪ L, isContinuum_union hK hL ⟨y, hyK, hyL⟩, union_ne_univ_of_indec hi hK hL hKu hLu,
    Or.inl hxK, Or.inr hzL⟩

omit [CompactSpace X] [ConnectedSpace X] in
theorem composant_eq_of_mem (hi : ¬ IsDecomposableSpace X) {x y : X}
    (h : y ∈ Jones.composant x) : Jones.composant y = Jones.composant x := by
  ext z
  exact ⟨fun hz => composant_trans hi h hz, fun hz => composant_trans hi (composant_symm h) hz⟩

omit [CompactSpace X] [ConnectedSpace X] in
/-- **Moore 138.** -/
theorem composant_eq_or_disjoint' (hi : ¬ IsDecomposableSpace X) (x y : X) :
    Jones.composant x = Jones.composant y ∨ Disjoint (Jones.composant x) (Jones.composant y) := by
  by_cases h : (Jones.composant x ∩ Jones.composant y).Nonempty
  · obtain ⟨w, hwx, hwy⟩ := h
    exact Or.inl ((composant_eq_of_mem hi hwx).symm.trans (composant_eq_of_mem hi hwy))
  · exact Or.inr (disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h))

omit [CompactSpace X] [ConnectedSpace X] in
theorem mem_composant_self [Nontrivial X] (x : X) : x ∈ Jones.composant x := by
  refine ⟨{x}, ⟨isCompact_singleton, isConnected_singleton⟩, ?_, rfl, rfl⟩
  intro h
  obtain ⟨y, hy⟩ := exists_ne x
  have : y ∈ ({x} : Set X) := h ▸ mem_univ y
  exact hy this

/-- A proper subcontinuum of an indecomposable continuum has empty interior. -/
theorem interior_eq_empty_of_proper (hi : ¬ IsDecomposableSpace X) {K : Set X}
    (hK : Fold.Q78.IsContinuum K) (hKu : K ≠ univ) : interior K = ∅ := by
  have hind : Fold.Q78.IsIndecomposable (univ : Set X) := by
    by_contra h
    exact hi (isDecomposableSpace_iff_not_isIndecomposable.2 h)
  by_contra hne
  obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hne
  exact HPC.T13.false_of_interior (M := univ) hind hK (subset_univ K) hKu isOpen_interior
    ⟨z, hz, mem_univ z⟩ (fun y hy => interior_subset hy.1)

/-- **Moore 136–137.** -/
theorem composant_isMeagre' (hi : ¬ IsDecomposableSpace X) (x : X) :
    IsMeagre (Jones.composant x) := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis X
  set B' := {b ∈ B | b.Nonempty}
  have hB'c : B'.Countable := hBc.mono (fun b hb => hb.1)
  haveI : Countable B' := hB'c.to_subtype
  set C : B' → Set X := fun b => connectedComponentIn (b.1ᶜ) x with hCdef
  have hCsub : ∀ b, C b ⊆ b.1ᶜ := fun b => connectedComponentIn_subset _ _
  have hCclosed : ∀ b, IsClosed (C b) := by
    intro b
    have hF : IsClosed (b.1ᶜ) := (hB.isOpen b.2.1).isClosed_compl
    by_cases hxb : x ∈ b.1ᶜ
    · have : closure (C b) ⊆ C b :=
        (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
          (subset_closure (mem_connectedComponentIn hxb))
          (closure_minimal (connectedComponentIn_subset _ _) hF)
      exact closure_subset_iff_isClosed.mp this
    · simp only [hCdef, connectedComponentIn_eq_empty hxb, isClosed_empty]
  have hnd : ∀ b, IsNowhereDense (C b) := by
    intro b
    rw [(hCclosed b).isNowhereDense_iff]
    by_cases hxb : x ∈ b.1ᶜ
    · refine interior_eq_empty_of_proper hi ⟨(hCclosed b).isCompact,
        ⟨x, mem_connectedComponentIn hxb⟩, isPreconnected_connectedComponentIn⟩ ?_
      intro h
      obtain ⟨w, hw⟩ := b.2.2
      exact hCsub b (h ▸ mem_univ w) hw
    · simp only [hCdef, connectedComponentIn_eq_empty hxb, interior_empty]
  have hcover : Jones.composant x ⊆ ⋃ b, C b := by
    rintro y ⟨K, hK, hKu, hxK, hyK⟩
    obtain ⟨w, hw⟩ : ∃ w, w ∉ K := by
      by_contra h; push_neg at h; exact hKu (eq_univ_of_forall h)
    obtain ⟨b, hbB, hwb, hbK⟩ := hB.exists_subset_of_mem_open hw hK.1.isClosed.isOpen_compl
    refine mem_iUnion.2 ⟨⟨b, hbB, w, hwb⟩, ?_⟩
    exact hK.2.isPreconnected.subset_connectedComponentIn hxK
      (fun z hz hzb => hbK hzb hz) hyK
  exact (isMeagre_iUnion fun b => (hnd b).isMeagre).mono hcover

/-- **Moore 139.** -/
theorem uncountable_composants' [Nontrivial X] (hi : ¬ IsDecomposableSpace X) :
    ¬ (range (Jones.composant : X → Set X)).Countable := by
  intro hc
  haveI : Countable (range (Jones.composant : X → Set X)) := hc.to_subtype
  have hcov : (univ : Set X) ⊆ ⋃ c : range (Jones.composant : X → Set X), c.1 := by
    intro y _
    exact mem_iUnion.2 ⟨⟨_, y, rfl⟩, mem_composant_self y⟩
  have hm : IsMeagre (univ : Set X) := by
    refine (isMeagre_iUnion fun c => ?_).mono hcov
    obtain ⟨_, y, rfl⟩ := c
    exact composant_isMeagre' hi y
  have hd := dense_of_mem_residual hm
  rw [compl_univ] at hd
  obtain ⟨y⟩ := (inferInstance : Nonempty X)
  have := hd.closure_eq
  rw [closure_empty] at this
  exact (this ▸ mem_univ y : y ∈ (∅ : Set X))

end Composants

end HPC.Hagopian
