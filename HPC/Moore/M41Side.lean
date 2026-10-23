import HPC.Moore.M41Geom

/-!
# Theorem 41, Case II: chords and the unbounded component (batch 140, item A)

* `chord_side`: if a point of the open arc of a chord `Z` of `J₁` (lying in an open set `U`) is a
  limit point of a connected open set `V ⊆ U − J₁` that is closed in `U − J₁`, every point of `Z`
  is (batch 138's `side_propagate`, applied in `U − W` with `W` the other arc of `J₁`).
* `pocket`: for a chord `Z` from `p` to `q` without `J₂`, an arc `C` of `J₂` from `p` to `q`, and a
  point `O` of `J₂` not on `C` that is a limit point of a connected set `V` with noncompact closure
  missing `Z` and `J₂`, no point of the open arc `C` is a limit point of `V` (Theorem 27 and
  `Gen.disjoint_of_unbounded`).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

section Side

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **The side of a chord.** *Axioms used: 1–8.* -/
theorem chord_side {J₁ U V : Set S} (hJ₁ : σ.IsSCC J₁) (hU : @IsOpen S σ.topology U)
    {p q : S} {Z : Set S} (hZ : @TArc S σ.topology p q Z) (hZJ : Z ⊆ J₁)
    (hZU : Z \ {p, q} ⊆ U) (hVo : @IsOpen S σ.topology V)
    (hVc : @IsPreconnected S σ.topology V) (hVU : V ⊆ U \ J₁)
    (hVcl : @closure S σ.topology V ∩ (U \ J₁) ⊆ V)
    (hmeet : ((Z \ {p, q}) ∩ @closure S σ.topology V).Nonempty) :
    Z ⊆ @closure S σ.topology V := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨z₀, hz₀, hz₀V⟩ := hmeet
  obtain ⟨x₀, hx₀⟩ : V.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hz₀V
    exact hz₀V
  obtain ⟨W, hW, hZW, hZWu⟩ := exists_other_arc h1 h3 h4 h51 hJ₁ hZ hZJ
  set O := U \ W with hOdef
  have hOo : IsOpen O := hU.sdiff hW.isClosed
  obtain ⟨hpq, f, hf, rfl, rfl, rfl⟩ := hZ
  have hfO : ∀ u ∈ Ioo (0 : unitInterval) 1, f u ∈ O := by
    intro u hu
    have hmem : f u ∈ range f \ {f 0, f 1} := by
      rw [TArc.diff_eq hf]; exact mem_image_of_mem _ hu
    refine ⟨hZU hmem, fun hW' => hmem.2 ?_⟩
    have : f u ∈ range f ∩ W := ⟨mem_range_self _, hW'⟩
    rwa [hZW] at this
  have hOK : O \ range f = U \ J₁ := by
    rw [← hZWu]
    ext x
    simp only [hOdef, mem_diff, mem_union, not_or]
    tauto
  have hcc : connectedComponentIn (O \ range f) x₀ = V := by
    rw [hOK]
    apply subset_antisymm
    · have hsub : connectedComponentIn (U \ J₁) x₀ ⊆ V ∪ (closure V)ᶜ := fun y hy => by
        by_cases hyc : y ∈ closure V
        · exact Or.inl (hVcl ⟨hyc, connectedComponentIn_subset _ _ hy⟩)
        · exact Or.inr hyc
      exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hVo
        isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left subset_closure) hsub
        ⟨x₀, mem_connectedComponentIn (hVU hx₀), hx₀⟩
    · exact hVc.subset_connectedComponentIn hx₀ hVU
  have hz₀' : z₀ ∈ f '' Ioo 0 1 := by rw [← TArc.diff_eq hf]; exact hz₀
  obtain ⟨u₀, hu₀, rfl⟩ := hz₀'
  have key := side_propagate h1 h2 h3 h4 h5 h6 h7 h8 hf hOo (x₀ := x₀) isPreconnected_Ioo
    subset_rfl hfO hu₀ (by rw [hcc]; exact hz₀V)
  rw [hcc] at key
  have hsub : range f \ {f 0, f 1} ⊆ closure V := by
    rw [TArc.diff_eq hf]
    rintro _ ⟨u, hu, rfl⟩
    exact key u hu
  exact (TArc.subset_closure_diff ⟨hpq, f, hf, rfl, rfl, rfl⟩).trans
    (isClosed_closure.closure_subset_iff.mpr hsub)

omit h6 in
/-- **The pocket of a chord.** *Axioms used: 1–5, 7, 8.* -/
theorem pocket {J₂ I₂ V : Set S} (hI₂ : σ.IsInteriorOf J₂ I₂) {p q : S} {Z C : Set S}
    (hZ : @TArc S σ.topology p q Z) (hZE : Z \ {p, q} ⊆ (@closure S σ.topology I₂)ᶜ)
    (hC : @TArc S σ.topology p q C) (hCJ : C ⊆ J₂) {O : S} (hO : O ∈ J₂) (hOC : O ∉ C)
    (hV : @IsPreconnected S σ.topology V)
    (hVnc : ¬ @IsCompact S σ.topology (@closure S σ.topology V))
    (hVZ : Disjoint V Z) (hVJ : Disjoint V J₂) (hOV : O ∈ @closure S σ.topology V) :
    Disjoint (C \ {p, q}) (@closure S σ.topology V) := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, hfr₂, -, -, -, -, -, -, -, -, -, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI₂
  obtain ⟨C', hC', hCC', hCC'u⟩ := exists_other_arc h1 h3 h4 h51 hI₂.1 hC hCJ
  have hC'J : C' ⊆ J₂ := hCC'u ▸ subset_union_right
  have hOC' : O ∈ C' \ {p, q} := by
    refine ⟨?_, ?_⟩
    · rw [← hCC'u] at hO; exact hO.resolve_left hOC
    · rintro (h | h)
      · exact hOC (h ▸ hC.left_mem)
      · exact hOC ((mem_singleton_iff.mp h) ▸ hC.right_mem)
  have hZJ : ∀ x ∈ Z \ {p, q}, x ∉ J₂ := fun x hx hxJ =>
    hZE hx (frontier_subset_closure (hfr₂.symm ▸ hxJ))
  have hT₁ : TSCC (Z ∪ C) := tscc_of_open_disjoint hC hZ hCJ hZJ
  have hT₂ : TSCC (Z ∪ C') := tscc_of_open_disjoint hC' hZ hC'J hZJ
  obtain ⟨R₁, hR₁r, hR₁f⟩ := ax8Prop h1 h3 h4 h51 h8 _ hT₁
  obtain ⟨R₂, hR₂r, hR₂f⟩ := ax8Prop h1 h3 h4 h51 h8 _ hT₂
  have hR₁ : TInt σ.region (Z ∪ C) R₁ := ⟨hT₁, hR₁r, hR₁f⟩
  have hR₂ : TInt σ.region (Z ∪ C') R₂ := ⟨hT₂, hR₂r, hR₂f⟩
  have hR : TInt σ.region J₂ I₂ := (isInteriorOf_iff h1 h3 h4 h51).mp hI₂
  obtain ⟨c₀, hc₀⟩ := hC.nonempty_diff
  have hcpt : ∀ R ∈ σ.region, IsCompact (closure R) := fun R hR => isCompact_closure_region h1 h4 hR
  have hV₁ : Disjoint V R₁ := disjoint_of_unbounded hcpt hR₁ hV hVnc
    (disjoint_union_right.mpr ⟨hVZ, hVJ.mono_right hCJ⟩)
  have hV₂ : Disjoint V R₂ := disjoint_of_unbounded hcpt hR₂ hV hVnc
    (disjoint_union_right.mpr ⟨hVZ, hVJ.mono_right hC'J⟩)
  rcases th27_dich hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7)
      (arcConn h1 h3 h4 h51 h2) (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3) hcpt
      (not_isCompact_univ h1 h5) hR hC hC' hCC' hCC'u hc₀ hOC' hZ hZE hR₁ hR₂ with h | h
  · rw [disjoint_left]
    intro y hy hyV
    have hyR₂ : y ∈ R₂ := by rw [h]; exact Or.inl (Or.inl hy)
    obtain ⟨w, hwR, hwV⟩ := mem_closure_iff_nhds.mp hyV R₂
      ((hopen_region R₂ hR₂r).mem_nhds hyR₂)
    exact disjoint_left.mp hV₂ hwV hwR
  · exfalso
    have hOR₁ : O ∈ R₁ := by rw [h]; exact Or.inl (Or.inl hOC')
    obtain ⟨w, hwR, hwV⟩ := mem_closure_iff_nhds.mp hOV R₁
      ((hopen_region R₁ hR₁r).mem_nhds hOR₁)
    exact disjoint_left.mp hV₁ hwV hwR

end Side

end HPC.Moore
