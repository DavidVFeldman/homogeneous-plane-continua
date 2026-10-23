import HPC.Plane.Fugate66B

/-!
# Batch 102, part 0: definitions (Nadler 11.23, 11.24, 11.29) and general topology

The four definitions of the batch-102 skeleton (`HPC/Plane/Sorgenfrey.lean`), unchanged, moved
here so that the proofs can be split over several files, together with the general-topology
facts used in Nadler's §§4–5:

* `exists_separated_of_not_isPreconnected` — a disconnected set is the union of two separated
  nonempty sets (Nadler 6.2);
* `isContinuum_union_piece` — Nadler 6.3: a continuum plus one piece of a separation of its
  complement in a bigger continuum is a continuum;
* `exists_continuum_bump_closed`, `exists_continuum_bump_open` — boundary bumping (Nadler 5.4,
  5.7), in the form "a subcontinuum through `p` reaching the boundary";
* the elementary facts about an essential sum `X = Y ⊕ Z`, and a constructor for weak triods.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S]

/-! ## The definitions of the skeleton -/

/-- **Nadler 11.23**, three summands: `X = X₁ ⊕ X₂ ⊕ X₃` — continua whose union is `X`, none
contained in the union of the other two. -/
def IsEssentialSum₃ (X X₁ X₂ X₃ : Set S) : Prop :=
  Fold.Q78.IsContinuum X ∧ Fold.Q78.IsContinuum X₁ ∧ Fold.Q78.IsContinuum X₂ ∧
    Fold.Q78.IsContinuum X₃ ∧ X = X₁ ∪ X₂ ∪ X₃ ∧
    ¬ X₁ ⊆ X₂ ∪ X₃ ∧ ¬ X₂ ⊆ X₁ ∪ X₃ ∧ ¬ X₃ ⊆ X₁ ∪ X₂

/-- Two summands: `X = Y ⊕ Z`, i.e. a decomposition into proper subcontinua. -/
def IsEssentialSum₂ (X Y Z : Set S) : Prop :=
  Fold.Q78.IsContinuum X ∧ Fold.Q78.IsContinuum Y ∧ Fold.Q78.IsContinuum Z ∧ X = Y ∪ Z ∧
    Y ≠ X ∧ Z ≠ X

/-- **Nadler 11.24.** A *weak triod*: an essential sum of three continua with a common point. -/
def IsWeakTriod (X : Set S) : Prop :=
  ∃ X₁ X₂ X₃ : Set S, IsEssentialSum₃ X X₁ X₂ X₃ ∧ (X₁ ∩ X₂ ∩ X₃).Nonempty

/-- **11.29.** `C = irr(A, B)`: `C` meets `A` and `B`, and no proper subcontinuum of `C` does. -/
def IrrFromTo (C A B : Set S) : Prop :=
  Fold.Q78.IsContinuum C ∧ (C ∩ A).Nonempty ∧ (C ∩ B).Nonempty ∧
    ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ C → (K ∩ A).Nonempty → (K ∩ B).Nonempty → K = C

/-! ## General topology -/

/-- **Nadler 6.2.** A set which is not preconnected is the union of two separated nonempty sets. -/
theorem exists_separated_of_not_isPreconnected {s : Set S} (h : ¬ IsPreconnected s) :
    ∃ A B : Set S, A.Nonempty ∧ B.Nonempty ∧ s = A ∪ B ∧ Disjoint (closure A) B ∧
      Disjoint A (closure B) := by
  simp only [IsPreconnected, not_forall, not_nonempty_iff_eq_empty] at h
  obtain ⟨u, v, hu, hv, hsuv, hsu, hsv, huv⟩ := h
  have key : ∀ x, x ∈ s → x ∈ u → x ∈ v → False := fun x hx hxu hxv => by
    have : x ∈ s ∩ (u ∩ v) := ⟨hx, hxu, hxv⟩
    rw [huv] at this; exact this
  refine ⟨s ∩ u, s ∩ v, hsu, hsv, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      rcases hsuv hx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | h) <;> exact h.1
  · rw [Set.disjoint_left]
    rintro x hx ⟨hxs, hxv⟩
    obtain ⟨y, hyv, hys, hyu⟩ := mem_closure_iff.mp hx v hv hxv
    exact key y hys hyu hyv
  · rw [Set.disjoint_left]
    rintro x ⟨hxs, hxu⟩ hx
    obtain ⟨y, hyu, hys, hyv⟩ := mem_closure_iff.mp hx u hu hxu
    exact key y hys hyu hyv

section Compact

variable [CompactSpace S]

/-- **Nadler 6.3.** If `N ⊆ X` are continua and `X ∖ N = A ∪ R` with `A`, `R` separated and `A`
nonempty, then `N ∪ A` is a continuum. -/
theorem isContinuum_union_piece {X N A R : Set S} (hX : Fold.Q78.IsContinuum X)
    (hN : Fold.Q78.IsContinuum N) (hNX : N ⊆ X) (hcov : X \ N = A ∪ R)
    (hAR : Disjoint (closure A) R) (hRA : Disjoint A (closure R)) :
    Fold.Q78.IsContinuum (N ∪ A) := by
  have hAX : A ⊆ X := fun x hx => (hcov.symm ▸ (Or.inl hx : x ∈ A ∪ R) : x ∈ X \ N).1
  have hcl : IsClosed (N ∪ A) := by
    rw [← closure_subset_iff_isClosed, closure_union]
    refine union_subset (hN.1.isClosed.closure_subset.trans subset_union_left) fun x hx => ?_
    have hxX : x ∈ X := closure_minimal hAX hX.1.isClosed hx
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · have : x ∈ A ∪ R := hcov ▸ ⟨hxX, hxN⟩
      rcases this with h | h
      · exact Or.inr h
      · exact absurd h (Set.disjoint_left.mp hAR hx)
  refine ⟨hcl.isCompact, hN.2.nonempty.mono subset_union_left, ?_⟩
  exact isPreconnected_union_piece hX.2.isPreconnected hX.1.isClosed hN.2.isPreconnected
    hN.1.isClosed hN.2.nonempty hNX hcov hAR hRA

/-- **Boundary bumping, closed form** (Nadler 5.4). If `F` is a proper closed subset of a continuum
`M` and `p ∈ F`, a subcontinuum of `F` through `p` meets the closure of `M ∖ F`. (The proof is that
of `exists_subcontinuum_meeting_closedBall`, for a general `F`.) -/
theorem exists_continuum_bump_closed {M F : Set S} (hM : Fold.Q78.IsContinuum M)
    (hFcl : IsClosed F) (hFM : F ⊆ M) (hFne : F ≠ M) {p : S} (hpF : p ∈ F) :
    ∃ K : Set S, Fold.Q78.IsContinuum K ∧ K ⊆ F ∧ p ∈ K ∧ (K ∩ closure (M \ F)).Nonempty := by
  classical
  have hFc : IsCompact F := hFcl.isCompact
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc
  set p' : F := ⟨p, hpF⟩
  set C := connectedComponent p' with hC_def
  set K : Set S := Subtype.val '' C with hK_def
  have hKc : IsCompact K := (isClosed_connectedComponent.isCompact).image continuous_subtype_val
  have hKconn : IsConnected K :=
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have hKF : K ⊆ F := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have hpK : p ∈ K := ⟨p', mem_connectedComponent, rfl⟩
  refine ⟨K, ⟨hKc, hKconn⟩, hKF, hpK, ?_⟩
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  set H : Set F := Subtype.val ⁻¹' closure (M \ F) with hH_def
  have hHc : IsCompact H := (isClosed_closure.preimage continuous_subtype_val).isCompact
  have hCH : H ∩ ⋂ s : { s : Set F // IsClopen s ∧ p' ∈ s }, (s : Set F) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzH hzC
    have : (z : S) ∈ K ∩ closure (M \ F) := ⟨⟨z, hzC, rfl⟩, hzH⟩
    rw [hcon] at this
    exact this
  obtain ⟨u, hu⟩ := hHc.elim_finite_subfamily_closed
    (fun s : { s : Set F // IsClopen s ∧ p' ∈ s } => (s : Set F)) (fun s => s.2.1.isClosed) hCH
  set W' : Set F := ⋂ i ∈ u, (i : Set F) with hW'_def
  have hW'clopen : IsClopen W' := isClopen_biInter_finset fun i _ => i.2.1
  have hpW' : p' ∈ W' := mem_iInter₂.mpr fun i _ => i.2.2
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW'clopen.isOpen
  set W : Set S := Subtype.val '' W' with hW_def
  have hWcl : IsClosed W := (hW'clopen.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hWF : W ⊆ F := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have hWO : W = F ∩ O := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      refine ⟨z'.2, ?_⟩
      have : z' ∈ Subtype.val ⁻¹' O := by rw [hOW]; exact hz'
      exact this
    · rintro ⟨hzF, hzO⟩
      refine ⟨⟨z, hzF⟩, ?_, rfl⟩
      rw [← hOW]; exact hzO
  obtain ⟨w, hwW, hwcl⟩ := T13.clopen_meets_closure_diff hM.2.isPreconnected hFM hFne
    hWF hWcl hO hWO ⟨p, p', hpW', rfl⟩
  obtain ⟨w', hw', rfl⟩ := hwW
  have : w' ∈ H ∩ W' := ⟨hwcl, hw'⟩
  rw [hu] at this
  exact this

/-- **Boundary bumping, open form** (Nadler 5.7). If `L` is a continuum, `O` is open, `p ∈ L ∩ O`
and `L ⊄ O`, then a subcontinuum of `L` through `p`, contained in the closure of `L ∩ O`, leaves
`O`. -/
theorem exists_continuum_bump_open {L O : Set S} (hL : Fold.Q78.IsContinuum L) (hO : IsOpen O)
    {p : S} (hpL : p ∈ L) (hpO : p ∈ O) (hLO : ¬ L ⊆ O) :
    ∃ K : Set S, Fold.Q78.IsContinuum K ∧ K ⊆ L ∧ K ⊆ closure (L ∩ O) ∧ p ∈ K ∧
      (K \ O).Nonempty := by
  have hFL : closure (L ∩ O) ⊆ L := closure_minimal inter_subset_left hL.1.isClosed
  by_cases hF : closure (L ∩ O) = L
  · refine ⟨L, hL, Subset.rfl, hF.symm.subset, hpL, ?_⟩
    obtain ⟨x, hxL, hxO⟩ := not_subset.mp hLO
    exact ⟨x, hxL, hxO⟩
  obtain ⟨K, hK, hKF, hpK, x, hxK, hx⟩ :=
    exists_continuum_bump_closed hL isClosed_closure hFL hF (subset_closure ⟨hpL, hpO⟩)
  refine ⟨K, hK, hKF.trans hFL, hKF, hpK, x, hxK, ?_⟩
  have hsub : L \ closure (L ∩ O) ⊆ L \ O := fun y hy =>
    ⟨hy.1, fun hyO => hy.2 (subset_closure ⟨hy.1, hyO⟩)⟩
  have hcl : IsClosed (L \ O) := hL.1.isClosed.sdiff hO
  exact (closure_minimal hsub hcl hx).2

/-- The closure of a preconnected subset of a compact set `K` is a subcontinuum of `K` (when the
subset is nonempty). -/
theorem isContinuum_closure_of_subset {K Z : Set S} (hK : IsClosed K) (hZK : Z ⊆ K)
    (hZ : IsPreconnected Z) (hne : Z.Nonempty) :
    Fold.Q78.IsContinuum (closure Z) ∧ closure Z ⊆ K :=
  ⟨⟨isClosed_closure.isCompact, hne.closure, hZ.closure⟩, closure_minimal hZK hK⟩

end Compact

/-- **Constructor for weak triods.** -/
theorem isWeakTriod_of {X X₁ X₂ X₃ : Set S} (h₁ : Fold.Q78.IsContinuum X₁)
    (h₂ : Fold.Q78.IsContinuum X₂) (h₃ : Fold.Q78.IsContinuum X₃) (hcov : X = X₁ ∪ X₂ ∪ X₃)
    (e₁ : ∃ x ∈ X₁, x ∉ X₂ ∧ x ∉ X₃) (e₂ : ∃ x ∈ X₂, x ∉ X₁ ∧ x ∉ X₃)
    (e₃ : ∃ x ∈ X₃, x ∉ X₁ ∧ x ∉ X₂) (hc : ∃ x, x ∈ X₁ ∧ x ∈ X₂ ∧ x ∈ X₃) : IsWeakTriod X := by
  obtain ⟨c, hc1, hc2, hc3⟩ := hc
  have hX : Fold.Q78.IsContinuum X := by
    rw [hcov]
    exact isContinuum_union (isContinuum_union h₁ h₂ ⟨c, hc1, hc2⟩) h₃ ⟨c, Or.inl hc1, hc3⟩
  obtain ⟨a, ha, ha2, ha3⟩ := e₁
  obtain ⟨b, hb, hb1, hb3⟩ := e₂
  obtain ⟨d, hd, hd1, hd2⟩ := e₃
  refine ⟨X₁, X₂, X₃, ⟨hX, h₁, h₂, h₃, hcov, ?_, ?_, ?_⟩, c, ⟨hc1, hc2⟩, hc3⟩
  · intro hs; rcases hs ha with h | h <;> contradiction
  · intro hs; rcases hs hb with h | h <;> contradiction
  · intro hs; rcases hs hd with h | h <;> contradiction

/-! ## Essential sums of two continua -/

namespace IsEssentialSum₂

variable {X Y Z : Set S}

theorem left_subset (h : IsEssentialSum₂ X Y Z) : Y ⊆ X := h.2.2.2.1 ▸ subset_union_left

theorem right_subset (h : IsEssentialSum₂ X Y Z) : Z ⊆ X := h.2.2.2.1 ▸ subset_union_right

theorem symm (h : IsEssentialSum₂ X Y Z) : IsEssentialSum₂ X Z Y :=
  ⟨h.1, h.2.2.1, h.2.1, by rw [union_comm]; exact h.2.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

/-- `U = X ∖ Z` is nonempty. -/
theorem diff_nonempty (h : IsEssentialSum₂ X Y Z) : (X \ Z).Nonempty := by
  by_contra hc
  rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hc
  exact h.2.2.2.2.2 (Subset.antisymm h.right_subset hc)

/-- `X ∖ Z ⊆ Y`. -/
theorem diff_subset_left (h : IsEssentialSum₂ X Y Z) : X \ Z ⊆ Y := fun x hx => by
  have := h.2.2.2.1 ▸ hx.1
  rcases this with h' | h'
  · exact h'
  · exact absurd h' hx.2

/-- `Z ∖ Y` is nonempty. -/
theorem right_diff_nonempty (h : IsEssentialSum₂ X Y Z) : (Z \ Y).Nonempty := by
  obtain ⟨x, hx⟩ := h.symm.diff_nonempty
  exact ⟨x, h.symm.diff_subset_left hx, hx.2⟩

/-- `Ū ⊆ Y`. -/
theorem closure_diff_subset_left (h : IsEssentialSum₂ X Y Z) : closure (X \ Z) ⊆ Y :=
  closure_minimal h.diff_subset_left h.2.1.1.isClosed

/-- `Ū ⊆ X`. -/
theorem closure_diff_subset (h : IsEssentialSum₂ X Y Z) : closure (X \ Z) ⊆ X :=
  h.closure_diff_subset_left.trans h.left_subset

/-- `Ū` misses `Z ∖ Y`. -/
theorem closure_diff_disjoint (h : IsEssentialSum₂ X Y Z) {x : S} (hx : x ∈ closure (X \ Z)) :
    x ∉ Z \ Y := fun hx' => hx'.2 (h.closure_diff_subset_left hx)

/-- `X = Ū ∪ Z`. -/
theorem eq_closure_union (h : IsEssentialSum₂ X Y Z) : X = closure (X \ Z) ∪ Z := by
  refine Subset.antisymm (fun x hx => ?_) (union_subset h.closure_diff_subset h.right_subset)
  by_cases hxZ : x ∈ Z
  · exact Or.inr hxZ
  · exact Or.inl (subset_closure ⟨hx, hxZ⟩)

/-- `Ū ∩ Z ≠ ∅` (connectedness of `X`). -/
theorem closure_inter_nonempty (h : IsEssentialSum₂ X Y Z) : (closure (X \ Z) ∩ Z).Nonempty := by
  have hX := h.1.2.isPreconnected
  obtain ⟨u, hu⟩ := h.diff_nonempty
  obtain ⟨z, hz⟩ := h.2.2.1.2.nonempty
  obtain ⟨x, hxX, hx1, hx2⟩ := isPreconnected_closed_iff.mp hX _ _ isClosed_closure
    h.2.2.1.1.isClosed h.eq_closure_union.subset ⟨u, hu.1, subset_closure hu⟩
    ⟨z, h.right_subset hz, hz⟩
  exact ⟨x, hx1, hx2⟩

/-- `Ū ⊆ U ∪ (Ū ∩ Z)`. -/
theorem closure_diff_subset_union (h : IsEssentialSum₂ X Y Z) :
    closure (X \ Z) ⊆ (X \ Z) ∪ (closure (X \ Z) ∩ Z) := fun x hx => by
  by_cases hxZ : x ∈ Z
  · exact Or.inr ⟨hx, hxZ⟩
  · exact Or.inl ⟨h.closure_diff_subset hx, hxZ⟩

/-- `Ū ≠ X`. -/
theorem closure_diff_ne (h : IsEssentialSum₂ X Y Z) : closure (X \ Z) ≠ X := by
  intro he
  obtain ⟨x, hxZ, hxY⟩ := h.right_diff_nonempty
  have hx : x ∈ closure (X \ Z) := by rw [he]; exact h.right_subset hxZ
  exact h.closure_diff_disjoint hx ⟨hxZ, hxY⟩

end IsEssentialSum₂

/-- A point outside the closed set `Z` lying in the closure of `A` lies in the closure of
`A ∖ Z`. -/
theorem mem_closure_diff_of_mem_closure {Z A : Set S} (hZ : IsClosed Z) {x : S}
    (hx : x ∈ closure A) (hxZ : x ∉ Z) : x ∈ closure (A \ Z) := by
  have := hZ.isOpen_compl.inter_closure ⟨hxZ, hx⟩
  rwa [inter_comm, ← diff_eq] at this

end HPC.Plane
