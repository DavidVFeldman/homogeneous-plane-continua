import HPC.Moore.M41

/-!
# Theorem 43: pockets on the inner side (batch 140, item B)

The dual of Theorem 41's `pocket`, for a connected open set `W` adjacent to a point `O` of `J` and
lying within `J` (`pocket_int`) or without `J` (`pocket_ext`): for a chord `Z` from `p` to `q`
lying (except for its ends) on the same side as `W`, and the arc `C` of `J` from `p` to `q` not
containing `O`, no point of the open arc `C` is a limit point of `W`. No unboundedness is needed:
`W` lies in the pocket whose arc of `J` contains `O`.

`adjacent_piece`: if `O` is on `J` and within the closed curve `J'`, there is a connected open set
within `J'`, on a prescribed side of `J`, having `O` as a limit point (Theorem 28). On the exterior
side this needs `I ⊄ I'`.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

section Pocket

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

omit h2 h7 in
/-- The two interiors cut off by a chord `Z` from `p` to `q` (open arc off `J`), with the arc `C` of
`J` and the other arc `C'`. -/
theorem chord_pockets {J I : Set S} (hI : σ.IsInteriorOf J I) {p q : S} {Z C : Set S}
    (hZ : @TArc S σ.topology p q Z) (hZJ : ∀ x ∈ Z \ {p, q}, x ∉ J)
    (hC : @TArc S σ.topology p q C) (hCJ : C ⊆ J) :
    letI := σ.topology
    ∃ C' R₁ R₂, TArc p q C' ∧ C ∩ C' = {p, q} ∧ C ∪ C' = J ∧
      TInt σ.region (Z ∪ C) R₁ ∧ TInt σ.region (Z ∪ C') R₂ := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨C', hC', hCC', hCC'u⟩ := exists_other_arc h1 h3 h4 h51 hI.1 hC hCJ
  have hC'J : C' ⊆ J := hCC'u ▸ subset_union_right
  have hT₁ : TSCC (Z ∪ C) := tscc_of_open_disjoint hC hZ hCJ hZJ
  have hT₂ : TSCC (Z ∪ C') := tscc_of_open_disjoint hC' hZ hC'J hZJ
  obtain ⟨R₁, hR₁r, hR₁f⟩ := ax8Prop h1 h3 h4 h51 h8 _ hT₁
  obtain ⟨R₂, hR₂r, hR₂f⟩ := ax8Prop h1 h3 h4 h51 h8 _ hT₂
  exact ⟨C', R₁, R₂, hC', hCC', hCC'u, ⟨hT₁, hR₁r, hR₁f⟩, ⟨hT₂, hR₂r, hR₂f⟩⟩

/-- **The pocket of a chord within `J`.** *Axioms used: 1–5, 7, 8.* -/
theorem pocket_int {J I W : Set S} (hI : σ.IsInteriorOf J I) {p q : S} {Z C : Set S}
    (hZ : @TArc S σ.topology p q Z) (hZI : Z \ {p, q} ⊆ I)
    (hC : @TArc S σ.topology p q C) (hCJ : C ⊆ J) {O : S} (hO : O ∈ J) (hOC : O ∉ C)
    (hW : @IsPreconnected S σ.topology W) (hWI : W ⊆ I) (hWZ : Disjoint W Z)
    (hOW : O ∈ @closure S σ.topology W) :
    Disjoint (C \ {p, q}) (@closure S σ.topology W) := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, -, -, hfr, -, -, -, -, -, hdisIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI
  have hZJ : ∀ x ∈ Z \ {p, q}, x ∉ J := fun x hx hxJ => disjoint_left.mp hdisIJ (hZI hx) hxJ
  obtain ⟨C', R₁, R₂, hC', hCC', hCC'u, hR₁, hR₂⟩ := chord_pockets h1 h3 h4 h5 h8 hI hZ hZJ hC hCJ
  have hR : TInt σ.region J I := (isInteriorOf_iff h1 h3 h4 h51).mp hI
  have hp : p ∈ J := hCJ hC.left_mem
  have hq : q ∈ J := hCJ hC.right_mem
  have hC'J : C' ⊆ J := hCC'u ▸ subset_union_right
  have h21 := th21Prop h1 h3 h4 h5 h7
  have hR₁I : R₁ ⊆ I := th24_sub h21 hR hp hq hCJ hZI hR₁
  have hR₂I : R₂ ⊆ I := th24_sub h21 hR hp hq hC'J hZI hR₂
  have hdec := th25 hopen_region (hpc_region h1 h2) h21 (arcConn h1 h3 h4 h51 h2)
    (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3) hR hC hC' hCC' hCC'u hZ hZI hR₁ hR₂
  have hR₁o : IsOpen R₁ := hopen_region R₁ hR₁.2.1
  have hR₂o : IsOpen R₂ := hopen_region R₂ hR₂.2.1
  have hOZ : O ∉ Z := fun h => hZJ O ⟨h, by
    rintro (e | e)
    · exact hOC (e ▸ hC.left_mem)
    · exact hOC ((mem_singleton_iff.mp e) ▸ hC.right_mem)⟩ hO
  -- `W` lies in `R₁ ∪ R₂`, hence in one of them, and not in `R₁`
  have hWsub : W ⊆ R₁ ∪ R₂ := fun x hx => by
    have : x ∈ I := hWI hx
    rw [hdec] at this
    rcases this with (h | h) | h
    · exact absurd h.1 (disjoint_left.mp hWZ hx)
    · exact Or.inl h
    · exact Or.inr h
  have hR₁₂ : Disjoint R₁ R₂ := th24_disj hopen_region (hpc_region h1 h2) hR hCJ hR₁ hR₂ hR₂I
    (th24_ext hopen_region hR hC'J hCC' hZI hR₁ hR₁I) hC'.nonempty_diff
  have hdisJ : ∀ y ∈ J, y ∉ R₁ ∧ y ∉ R₂ := fun y hy =>
    ⟨fun h => disjoint_left.mp hdisIJ (hR₁I h) hy, fun h => disjoint_left.mp hdisIJ (hR₂I h) hy⟩
  rcases hW.subset_or_subset hR₁o hR₂o hR₁₂ hWsub with h | h
  · exfalso
    have hOc : O ∈ closure R₁ := closure_mono h hOW
    rw [closure_eq_union_frontier hR₁o, hR₁.2.2] at hOc
    rcases hOc with h' | h' | h'
    · exact (hdisJ O hO).1 h'
    · exact hOZ h'
    · exact hOC h'
  · rw [disjoint_left]
    intro y hy hyc
    have hyc' : y ∈ closure R₂ := closure_mono h hyc
    rw [closure_eq_union_frontier hR₂o, hR₂.2.2] at hyc'
    rcases hyc' with h' | h' | h'
    · exact (hdisJ y (hCJ hy.1)).2 h'
    · exact hZJ y ⟨h', hy.2⟩ (hCJ hy.1)
    · have : y ∈ C ∩ C' := ⟨hy.1, h'⟩
      rw [hCC'] at this
      exact hy.2 this

/-- **The pocket of a chord without `J`** (no unboundedness needed). *Axioms used: 1–5, 7, 8.* -/
theorem pocket_ext {J I W : Set S} (hI : σ.IsInteriorOf J I) {p q : S} {Z C : Set S}
    (hZ : @TArc S σ.topology p q Z) (hZE : Z \ {p, q} ⊆ (@closure S σ.topology I)ᶜ)
    (hC : @TArc S σ.topology p q C) (hCJ : C ⊆ J) {O : S} (hO : O ∈ J) (hOC : O ∉ C)
    (hW : @IsPreconnected S σ.topology W) (hWE : W ⊆ (@closure S σ.topology I)ᶜ)
    (hWZ : Disjoint W Z) (hOW : O ∈ @closure S σ.topology W) :
    Disjoint (C \ {p, q}) (@closure S σ.topology W) := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, -, -, hfr, -, -, -, -, hcl, hdisIJ, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI
  have hJcl : J ⊆ closure I := hfr ▸ frontier_subset_closure
  have hZJ : ∀ x ∈ Z \ {p, q}, x ∉ J := fun x hx hxJ => hZE hx (hJcl hxJ)
  obtain ⟨C', R₁, R₂, hC', hCC', hCC'u, hR₁, hR₂⟩ :=
    chord_pockets h1 h3 h4 h5 h8 hI hZ hZJ hC hCJ
  have hR : TInt σ.region J I := (isInteriorOf_iff h1 h3 h4 h51).mp hI
  have hC'J : C' ⊆ J := hCC'u ▸ subset_union_right
  have hR₁o : IsOpen R₁ := hopen_region R₁ hR₁.2.1
  have hR₂o : IsOpen R₂ := hopen_region R₂ hR₂.2.1
  have hOC' : O ∈ C' \ {p, q} := by
    refine ⟨?_, ?_⟩
    · rw [← hCC'u] at hO; exact hO.resolve_left hOC
    · rintro (h | h)
      · exact hOC (h ▸ hC.left_mem)
      · exact hOC ((mem_singleton_iff.mp h) ▸ hC.right_mem)
  have hOZ : O ∉ Z := fun h => hZJ O ⟨h, hOC'.2⟩ hO
  have hWJ : Disjoint W J := disjoint_left.mpr fun x hx hxJ => hWE hx (hJcl hxJ)
  have hWI : Disjoint W I := disjoint_left.mpr fun x hx hxI => hWE hx (subset_closure hxI)
  have hWfr₁ : Disjoint W (frontier R₁) := by
    rw [hR₁.2.2]; exact disjoint_union_right.mpr ⟨hWZ, hWJ.mono_right hCJ⟩
  have hWfr₂ : Disjoint W (frontier R₂) := by
    rw [hR₂.2.2]; exact disjoint_union_right.mpr ⟨hWZ, hWJ.mono_right hC'J⟩
  obtain ⟨c₀, hc₀⟩ := hC.nonempty_diff
  have hcpt : ∀ R ∈ σ.region, IsCompact (closure R) := fun R hR => isCompact_closure_region h1 h4 hR
  rcases th27_dich hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7)
      (arcConn h1 h3 h4 h51 h2) (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3) hcpt
      (not_isCompact_univ h1 h5) hR hC hC' hCC' hCC'u hc₀ hOC' hZ hZE hR₁ hR₂ with h | h
  · have hWR₂ : Disjoint W R₂ := by
      rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
      intro hne
      have hWsub : W ⊆ R₂ := conn_sub_of_frontier hW hWfr₂ hne
      have hWR₁ : W ⊆ R₁ := fun x hx => by
        have : x ∈ R₂ := hWsub hx
        rw [h] at this
        rcases this with (h' | h') | h'
        · exact absurd (hCJ h'.1) (disjoint_left.mp hWJ hx)
        · exact absurd h' (disjoint_left.mp hWI hx)
        · exact h'
      have hOc : O ∈ closure R₁ := closure_mono hWR₁ hOW
      rw [closure_eq_union_frontier hR₁o, hR₁.2.2] at hOc
      rcases hOc with h' | h' | h'
      · have hOR₂ : O ∈ R₂ := by rw [h]; exact Or.inr h'
        exact notMem_of_mem_frontier hR₂o (hR₂.2.2 ▸ Or.inr hOC'.1) hOR₂
      · exact hOZ h'
      · exact hOC h'
    rw [disjoint_left]
    intro y hy hyc
    have hyR₂ : y ∈ R₂ := by rw [h]; exact Or.inl (Or.inl hy)
    obtain ⟨w, hwR, hwW⟩ := mem_closure_iff_nhds.mp hyc R₂ (hR₂o.mem_nhds hyR₂)
    exact disjoint_left.mp hWR₂ hwW hwR
  · have hOR₁ : O ∈ R₁ := by rw [h]; exact Or.inl (Or.inl hOC')
    obtain ⟨w, hwR, hwW⟩ := mem_closure_iff_nhds.mp hOW R₁ (hR₁o.mem_nhds hOR₁)
    have hWsub : W ⊆ R₁ := conn_sub_of_frontier hW hWfr₁ ⟨w, hwW, hwR⟩
    have hWR₂ : W ⊆ R₂ := fun x hx => by
      have : x ∈ R₁ := hWsub hx
      rw [h] at this
      rcases this with (h' | h') | h'
      · exact absurd (hC'J h'.1) (disjoint_left.mp hWJ hx)
      · exact absurd h' (disjoint_left.mp hWI hx)
      · exact h'
    rw [disjoint_left]
    intro y hy hyc
    have hyc' : y ∈ closure R₂ := closure_mono hWR₂ hyc
    rw [closure_eq_union_frontier hR₂o, hR₂.2.2] at hyc'
    rcases hyc' with h' | h' | h'
    · have hyR₁ : y ∈ R₁ := by rw [h]; exact Or.inr h'
      exact notMem_of_mem_frontier hR₁o (hR₁.2.2 ▸ Or.inr hy.1) hyR₁
    · exact hZJ y ⟨h', hy.2⟩ (hCJ hy.1)
    · have : y ∈ C ∩ C' := ⟨hy.1, h'⟩
      rw [hCC'] at this
      exact hy.2 this

end Pocket

end HPC.Moore
