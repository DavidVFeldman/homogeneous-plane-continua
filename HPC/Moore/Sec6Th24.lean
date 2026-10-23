import HPC.Moore.Sec6A

/-!
# Moore, F.A. (1916), §6: Theorem 24, in the topological setting (batch 138)

The setting of Theorems 24 and 25: `J = ACB + ADB` is a closed curve with interior `R`, and `AXB`
is an arc whose open part lies in `R`; `R₁`, `R₂` are the interiors of `AXBCA`, `AXBDA`.
Moore's proof of Theorem 24 uses Theorem 21, Theorem 1 and Axiom 2; so does this one.
-/

namespace HPC.Moore

open Set Topology

namespace Gen

variable {T : Type*} [TopologicalSpace T] {reg : Set (Set T)}

/-- The arc `AXB` with open part in the interior `R` of `J` meets `J` only in `A`, `B`. -/
theorem arc_eq_of_mem_J {J R : Set T} (hRo : IsOpen R) (hRJ : frontier R = J) {A B : T}
    {Xa : Set T} (hXR : Xa \ {A, B} ⊆ R) {x : T} (hx : x ∈ Xa) (hxJ : x ∈ J) : x = A ∨ x = B := by
  by_contra h
  push_neg at h
  exact notMem_of_mem_frontier hRo (hRJ ▸ hxJ) (hXR ⟨hx, by simp [h.1, h.2]⟩)

/-- The arc `AXB` lies in `R'`. -/
theorem arc_subset_closure {J R : Set T} (hRJ : frontier R = J) {A B : T} (hA : A ∈ J)
    (hB : B ∈ J) {Xa : Set T} (hXR : Xa \ {A, B} ⊆ R) : Xa ⊆ closure R := by
  intro x hx
  by_cases hxAB : x ∈ ({A, B} : Set T)
  · rcases hxAB with rfl | rfl
    · exact frontier_subset_closure (hRJ ▸ hA)
    · exact frontier_subset_closure (hRJ ▸ hB)
  · exact subset_closure (hXR ⟨hx, hxAB⟩)

/-- **Theorem 24 (1)**: `R₁ ⊆ R` (Theorem 21). -/
theorem th24_sub (h21 : Th21Prop reg) {J R : Set T} (hR : TInt reg J R) {A B : T} (hA : A ∈ J)
    (hB : B ∈ J) {C₁ Xa R₁ : Set T} (hC₁J : C₁ ⊆ J) (hXR : Xa \ {A, B} ⊆ R)
    (hR₁ : TInt reg (Xa ∪ C₁) R₁) : R₁ ⊆ R := by
  refine h21 R hR.2.1 R₁ hR₁.2.1 ?_
  rw [hR₁.2.2]
  exact union_subset (arc_subset_closure hR.2.2 hA hB hXR)
    (hC₁J.trans (hR.2.2 ▸ frontier_subset_closure))

/-- **Theorem 24 (2)**: the open arc `ADB` is without `R₁` (Theorem 1). -/
theorem th24_ext (hopen : ∀ R ∈ reg, IsOpen R) {J R : Set T} (hR : TInt reg J R) {A B : T}
    {C₁ C₂ Xa R₁ : Set T} (hC₂J : C₂ ⊆ J) (hC12 : C₁ ∩ C₂ = {A, B}) (hXR : Xa \ {A, B} ⊆ R)
    (hR₁ : TInt reg (Xa ∪ C₁) R₁) (hR₁R : R₁ ⊆ R) : C₂ \ {A, B} ⊆ (closure R₁)ᶜ := by
  have hRo := hopen R hR.2.1
  intro x ⟨hxC₂, hxAB⟩ hxcl
  rw [closure_eq_union_frontier (hopen R₁ hR₁.2.1), hR₁.2.2] at hxcl
  have hxJ : x ∈ J := hC₂J hxC₂
  rcases hxcl with hx | hx | hx
  · exact notMem_of_mem_frontier hRo (hR.2.2 ▸ hxJ) (hR₁R hx)
  · rcases arc_eq_of_mem_J hRo hR.2.2 hXR hx hxJ with rfl | rfl <;> simp at hxAB
  · exact hxAB (hC12 ▸ ⟨hx, hxC₂⟩)

/-- **Theorem 24 (3)**: `R₁ ∩ R₂ = ∅` (Axiom 2). -/
theorem th24_disj (hopen : ∀ R ∈ reg, IsOpen R) (hpc : ∀ R ∈ reg, IsPreconnected R)
    {J R : Set T} (hR : TInt reg J R) {A B : T} {C₁ C₂ Xa R₁ R₂ : Set T} (hC₁J : C₁ ⊆ J)
    (hR₁ : TInt reg (Xa ∪ C₁) R₁) (hR₂ : TInt reg (Xa ∪ C₂) R₂)
    (hR₂R : R₂ ⊆ R) (hC₂ext : C₂ \ {A, B} ⊆ (closure R₁)ᶜ) (hC₂ne : (C₂ \ {A, B}).Nonempty) :
    Disjoint R₁ R₂ := by
  have hRo := hopen R hR.2.1
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro hne
  have hfr : Disjoint R₂ (frontier R₁) := by
    rw [hR₁.2.2, disjoint_union_right]
    refine ⟨?_, ?_⟩
    · refine disjoint_left.mpr fun x hxR₂ hxX => ?_
      have : x ∈ frontier R₂ := hR₂.2.2 ▸ Or.inl hxX
      exact notMem_of_mem_frontier (hopen R₂ hR₂.2.1) this hxR₂
    · refine disjoint_left.mpr fun x hxR₂ hxC => ?_
      exact notMem_of_mem_frontier hRo (hR.2.2 ▸ hC₁J hxC) (hR₂R hxR₂)
  have hsub : R₂ ⊆ R₁ := conn_sub_of_frontier (hpc R₂ hR₂.2.1) hfr (by
    rw [inter_comm]; exact hne)
  obtain ⟨D, hD⟩ := hC₂ne
  have hDcl : D ∈ closure R₂ := frontier_subset_closure (hR₂.2.2 ▸ Or.inr hD.1)
  exact hC₂ext hD (closure_mono hsub hDcl)

end Gen

end HPC.Moore
