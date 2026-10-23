import HPC.Moore.Sec7Chord

/-!
# Moore, F.A. (1916), §7: Theorem 37 (batch 139)

**Theorem 37.** `J`, `C` closed curves; `O` on `J` but not on `C`; `A₁ ≠ A₂` common to `C` and
`J`; `A₁XA₂` an arc of `C` whose open part is within `J`. Then there are `O₁`, `O₂ ≠ O` on the
intervals `A₁O`, `A₂O` of the arc `A₁OA₂` of `J`, joined by an arc of `C` whose open part is within
`J`, and innermost among such: if `B₁` on `O₁O` and `B₂` on `O₂O` are so joined, then `B₁ = O₁`,
`B₂ = O₂`.

Proof: `exists_maximal_chord` (`Sec7Chord.lean`) applied to the arcs of `C` from `A₁O` to `A₂O`
whose open parts lie in the interior of `J`. Moore's sets `M₁`, `M₂`, his monotonicity step
(\"in view of Theorem 29, it is clear that …\") and his limit-point argument (points `L₁`, `L₂`) are
replaced by the finiteness of the set of ends of such arcs (commission check 4: both steps are
covered by the finiteness argument in `exists_maximal_chord`).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- **Theorem 37.** *Axioms used: 1, 3, 4, 5₁.* **Shape change:** the axioms are made explicit
(the skeleton's section assumes Axioms 1–8; only 1, 3, 4 and 5₁ are used, 5₁ in place of 5). The
statement is otherwise the skeleton's. -/
theorem fa_theorem37 (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) {J C I : Set S} (hJ : σ.IsInteriorOf J I) (hC : σ.IsSCC C)
    {O A₁ A₂ : S} (hO : O ∈ J) (hOC : O ∉ C) (hA₁ : A₁ ∈ C ∩ J) (hA₂ : A₂ ∈ C ∩ J)
    (hA : A₁ ≠ A₂) {X : Set S} (hX : σ.IsArc A₁ A₂ X) (hXC : X ⊆ C)
    (hXI : openArc A₁ A₂ X ⊆ I) {T T₁ T₂ : Set S} (hT : σ.IsArc A₁ A₂ T) (hTJ : T ⊆ J)
    (hOT : O ∈ T) (hT₁ : σ.IsArc A₁ O T₁ ∧ T₁ ⊆ T) (hT₂ : σ.IsArc A₂ O T₂ ∧ T₂ ⊆ T) :
    ∃ O₁ O₂ : S, O₁ ≠ O ∧ O₂ ≠ O ∧ O₁ ∈ T₁ ∧ O₂ ∈ T₂ ∧
      (∃ Y, σ.IsArc O₁ O₂ Y ∧ Y ⊆ C ∧ openArc O₁ O₂ Y ⊆ I) ∧
      ∀ B₁ B₂ : S, ∀ U₁ U₂ : Set S, σ.IsArc O₁ O U₁ → U₁ ⊆ T₁ → σ.IsArc O₂ O U₂ → U₂ ⊆ T₂ →
        B₁ ∈ U₁ → B₂ ∈ U₂ →
        (∃ Z, σ.IsArc B₁ B₂ Z ∧ Z ⊆ C ∧ openArc B₁ B₂ Z ⊆ I) → B₁ = O₁ ∧ B₂ = O₂ := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨-, hIr, hIJ⟩ := hJ
  rw [bdry_eq_frontier h1] at hIJ
  have hIJd : ∀ x ∈ I, x ∉ J := fun x hx hxJ =>
    notMem_of_mem_frontier (isOpen_region hIr) (hIJ ▸ hxJ) hx
  obtain ⟨-, g, hg, hgr, hg0, hg1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hT
  subst hg0 hg1
  obtain ⟨o, rfl⟩ : O ∈ range g := hgr ▸ hOT
  have hgJ : range g ⊆ J := hgr ▸ hTJ
  have hT₁eq : T₁ = g '' Icc 0 o := by
    rw [← uIcc_of_le nonneg']
    exact eq_image_uIcc_of_isArc_subset h1 h4 hg (hgr ▸ hT₁.2) hT₁.1
  have hT₂eq : T₂ = g '' Icc o 1 := by
    rw [← uIcc_of_ge le_one']
    exact eq_image_uIcc_of_isArc_subset h1 h4 hg (hgr ▸ hT₂.2) hT₂.1
  set Good : unitInterval → unitInterval → Set S → Prop := fun s t Z =>
    s ≤ o ∧ o ≤ t ∧ Z ⊆ C ∧ TArc (g s) (g t) Z ∧ Z \ {g s, g t} ⊆ I with hGood
  have hGood' : ∀ s t Z, Good s t Z → s ≤ o ∧ o ≤ t ∧ Z ⊆ C ∧ TArc (g s) (g t) Z ∧
      ∀ x ∈ Z \ {g s, g t}, x ∉ J := fun s t Z ⟨h1', h2', h3', h4', h5'⟩ =>
    ⟨h1', h2', h3', h4', fun x hx => hIJd x (h5' hx)⟩
  have hXg : Good 0 1 X := ⟨nonneg', le_one', hXC, (isArc_iff_tarc h1 h3 h4 h51).mp hX, hXI⟩
  obtain ⟨p, q, Y, ⟨hpo, hoq, hYC, hYa, hYI⟩, hmax⟩ :=
    exists_maximal_chord h1 h3 h4 h51 hC hg hgJ hOC Good hGood' hXg
  have hpC : g p ∈ C := hYC hYa.left_mem
  have hqC : g q ∈ C := hYC hYa.right_mem
  refine ⟨g p, g q, fun e => hOC (e ▸ hpC), fun e => hOC (e ▸ hqC),
    hT₁eq ▸ mem_image_of_mem _ ⟨nonneg', hpo⟩, hT₂eq ▸ mem_image_of_mem _ ⟨hoq, le_one'⟩,
    ⟨Y, (isArc_iff_tarc h1 h3 h4 h51).mpr hYa, hYC, hYI⟩, ?_⟩
  intro B₁ B₂ U₁ U₂ hU₁ hU₁T hU₂ hU₂T hB₁ hB₂ ⟨Z, hZ, hZC, hZI⟩
  have hU₁eq : U₁ = g '' Icc p o := by
    rw [← uIcc_of_le hpo]
    exact eq_image_uIcc_of_isArc_subset h1 h4 hg
      (hU₁T.trans (hT₁eq ▸ image_subset_range _ _)) hU₁
  have hU₂eq : U₂ = g '' Icc o q := by
    rw [← uIcc_of_ge hoq]
    exact eq_image_uIcc_of_isArc_subset h1 h4 hg
      (hU₂T.trans (hT₂eq ▸ image_subset_range _ _)) hU₂
  rw [hU₁eq] at hB₁
  rw [hU₂eq] at hB₂
  obtain ⟨s, ⟨hps, hso⟩, rfl⟩ := hB₁
  obtain ⟨t, ⟨hot, htq⟩, rfl⟩ := hB₂
  obtain ⟨rfl, rfl⟩ := hmax s t Z ⟨hso, hot, hZC, (isArc_iff_tarc h1 h3 h4 h51).mp hZ, hZI⟩ hps htq
  exact ⟨rfl, rfl⟩

end HPC.Moore
