import HPC.Moore.Sec6Th26

/-!
# Moore, F.A. (1916), §6: Theorem 27, in the topological setting (batch 138)

**Theorem 27.** If `A`, `B` separate `C`, `D` on `J` and the open arc `AXB` is without `J`, then
(1) `D` is without `AXBCA` or `C` is without `AXBDA`; (2) if `D` is without `AXBCA`, then `C` is
within `AXBDA`, and the interior of `AXBDA` is the open arc `ACB` + the interior of `J` + the
interior of `AXBCA`.

Moore's proof (p. 145): (1) if `D` is not without `AXBCA`, the open arc `ADB` is within it, and
Theorem 24 puts `C` without `AXBDA`. (2) The interiors of `ACBDA` and `AXBCA` are disjoint
(Axiom 2); if `C` were also without `AXBDA` the three interiors would be mutually exclusive,
against Theorem 26; and Theorem 25 gives the decomposition. Moore's \"Then `ADB` is within
`AXBCA`\" and the disjointness of the interiors of `AXBDA` and the other two (needed for Theorem
26) are supplied.
-/

namespace HPC.Moore

open Set Topology

namespace Gen

variable {T : Type*} [TopologicalSpace T] [T2Space T] {reg : Set (Set T)}

/-- **Theorem 27**, topologically. -/
theorem th27 [LocallyConnectedSpace T] (hopen : ∀ R ∈ reg, IsOpen R)
    (hpc : ∀ R ∈ reg, IsPreconnected R) (h21 : Th21Prop reg) (harc : ArcConn T)
    (h8 : Ax8Prop reg) (hext : ∀ R ∈ reg, IsPreconnected (closure R)ᶜ)
    (hcpt : ∀ R ∈ reg, IsCompact (closure R)) (hnc : ¬ IsCompact (univ : Set T))
    {J R : Set T} (hR : TInt reg J R) {A B C D : T} {C₁ C₂ : Set T} (hC₁ : TArc A B C₁)
    (hC₂ : TArc A B C₂) (hC12 : C₁ ∩ C₂ = {A, B}) (hCJ : C₁ ∪ C₂ = J)
    (hC : C ∈ C₁ \ {A, B}) (hD : D ∈ C₂ \ {A, B})
    {Xa : Set T} (hX : TArc A B Xa) (hXR : Xa \ {A, B} ⊆ (closure R)ᶜ) {R₁ R₂ : Set T}
    (hR₁ : TInt reg (Xa ∪ C₁) R₁) (hR₂ : TInt reg (Xa ∪ C₂) R₂) :
    (D ∈ (closure R₁)ᶜ ∨ C ∈ (closure R₂)ᶜ) ∧
      (D ∈ (closure R₁)ᶜ → C ∈ R₂ ∧ R₂ = C₁ \ {A, B} ∪ R ∪ R₁) := by
  have hRo := hopen R hR.2.1
  have hR₁o := hopen R₁ hR₁.2.1
  have hR₂o := hopen R₂ hR₂.2.1
  have hC₁J : C₁ ⊆ J := hCJ ▸ subset_union_left
  have hC₂J : C₂ ⊆ J := hCJ ▸ subset_union_right
  have hJcl : J ⊆ closure R := hR.2.2 ▸ frontier_subset_closure
  have hXJ : ∀ x ∈ Xa, x ∈ J → x = A ∨ x = B := by
    intro x hx hxJ
    by_contra h
    push_neg at h
    exact hXR ⟨hx, by simp [h.1, h.2]⟩ (hJcl hxJ)
  have hXC : ∀ Ci : Set T, Ci ⊆ J → A ∈ Ci → B ∈ Ci → Xa ∩ Ci = {A, B} := by
    intro Ci hCi hA hB
    apply subset_antisymm
    · rintro x ⟨hx, hxC⟩
      rcases hXJ x hx (hCi hxC) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro x (rfl | rfl)
      exacts [⟨hX.left_mem, hA⟩, ⟨hX.right_mem, hB⟩]
  have hXC₁ := hXC C₁ hC₁J hC₁.left_mem hC₁.right_mem
  have hXC₂ := hXC C₂ hC₂J hC₂.left_mem hC₂.right_mem
  have hfr₁ := hR₁.2.2
  have hfr₂ := hR₂.2.2
  -- `ADB` (open) misses the boundary of `R₁`; `ACB` (open) misses that of `R₂`
  have hC₂fr : Disjoint (C₂ \ {A, B}) (frontier R₁) := by
    rw [hfr₁]
    refine disjoint_left.mpr fun x hx hx' => hx.2 ?_
    rcases hx' with h | h
    · rw [← hXC₂]; exact ⟨h, hx.1⟩
    · rw [← hC12]; exact ⟨h, hx.1⟩
  have hC₁fr : Disjoint (C₁ \ {A, B}) (frontier R₂) := by
    rw [hfr₂]
    refine disjoint_left.mpr fun x hx hx' => hx.2 ?_
    rcases hx' with h | h
    · rw [← hXC₁]; exact ⟨h, hx.1⟩
    · rw [← hC12]; exact ⟨hx.1, h⟩
  have hDfr : D ∉ frontier R₁ := disjoint_left.mp hC₂fr hD
  have hCfr : C ∉ frontier R₂ := disjoint_left.mp hC₁fr hC
  refine ⟨?_, fun hDext => ?_⟩
  · -- (1)
    by_cases hDext : D ∈ (closure R₁)ᶜ
    · exact Or.inl hDext
    right
    have hDR₁ : D ∈ R₁ := by
      by_contra h
      exact hDext fun hcl => by
        rw [closure_eq_union_frontier hR₁o] at hcl
        rcases hcl with h' | h'
        exacts [h h', hDfr h']
    have hC₂R₁ : C₂ \ {A, B} ⊆ R₁ :=
      conn_sub_of_frontier hC₂.isPreconnected_diff hC₂fr ⟨D, hD, hDR₁⟩
    -- Theorem 24 for the curve `AXBCA` and the arc `ADB` within it
    have hJ' : TInt reg (Xa ∪ C₁) R₁ := hR₁
    have hR₂' : TInt reg (C₂ ∪ Xa) R₂ := by rw [union_comm]; exact hR₂
    have hsub : R₂ ⊆ R₁ := th24_sub h21 hJ' (Or.inl hX.left_mem) (Or.inl hX.right_mem)
      subset_union_left hC₂R₁ hR₂'
    exact th24_ext hopen hJ' subset_union_right hXC₁ hC₂R₁ hR₂' hsub hC
  · -- (2)
    have hC₂ext : C₂ \ {A, B} ⊆ (closure R₁)ᶜ :=
      conn_sub_ext_of_frontier hC₂.isPreconnected_diff hC₂fr ⟨D, hD, hDext⟩
    obtain ⟨P, hP⟩ := hX.nonempty_diff
    have hPfr₁ : P ∈ frontier R₁ := hfr₁ ▸ Or.inl hP.1
    have hPfr₂ : P ∈ frontier R₂ := hfr₂ ▸ Or.inl hP.1
    have hAfr₁ : A ∈ frontier R₁ := hfr₁ ▸ Or.inl hX.left_mem
    have hBfr₁ : B ∈ frontier R₁ := hfr₁ ▸ Or.inl hX.right_mem
    have hAfr₂ : A ∈ frontier R₂ := hfr₂ ▸ Or.inl hX.left_mem
    have hBfr₂ : B ∈ frontier R₂ := hfr₂ ▸ Or.inl hX.right_mem
    -- the interiors of `ACBDA` and `AXBCA` are disjoint
    have hRR₁ : Disjoint R R₁ := by
      rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
      rintro ⟨y, hyR, hyR₁⟩
      have hfr : Disjoint R₁ (frontier R) := by
        rw [hR.2.2, ← hCJ]
        refine disjoint_left.mpr fun x hx hx' => ?_
        have hxfr : x ∉ frontier R₁ := fun h => notMem_of_mem_frontier hR₁o h hx
        rcases hx' with h | h
        · exact hxfr (hfr₁ ▸ Or.inr h)
        · by_cases hAB : x ∈ ({A, B} : Set T)
          · rcases hAB with rfl | rfl
            exacts [hxfr hAfr₁, hxfr hBfr₁]
          · exact hC₂ext ⟨h, hAB⟩ (subset_closure hx)
      have hsub := conn_sub_of_frontier (hpc R₁ hR₁.2.1) hfr ⟨y, hyR₁, hyR⟩
      exact hXR hP (closure_mono hsub (frontier_subset_closure hPfr₁))
    -- `C` is within `AXBDA`
    have hCR₂ : C ∈ R₂ := by
      by_contra hCR₂
      have hCext : C ∈ (closure R₂)ᶜ := fun hcl => by
        rw [closure_eq_union_frontier hR₂o] at hcl
        rcases hcl with h' | h'
        exacts [hCR₂ h', hCfr h']
      have hC₁ext : C₁ \ {A, B} ⊆ (closure R₂)ᶜ :=
        conn_sub_ext_of_frontier hC₁.isPreconnected_diff hC₁fr ⟨C, hC, hCext⟩
      have hRR₂ : Disjoint R R₂ := by
        rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
        rintro ⟨y, hyR, hyR₂⟩
        have hfr : Disjoint R₂ (frontier R) := by
          rw [hR.2.2, ← hCJ]
          refine disjoint_left.mpr fun x hx hx' => ?_
          have hxfr : x ∉ frontier R₂ := fun h => notMem_of_mem_frontier hR₂o h hx
          rcases hx' with h | h
          · by_cases hAB : x ∈ ({A, B} : Set T)
            · rcases hAB with rfl | rfl
              exacts [hxfr hAfr₂, hxfr hBfr₂]
            · exact hC₁ext ⟨h, hAB⟩ (subset_closure hx)
          · exact hxfr (hfr₂ ▸ Or.inr h)
        have hsub := conn_sub_of_frontier (hpc R₂ hR₂.2.1) hfr ⟨y, hyR₂, hyR⟩
        exact hXR hP (closure_mono hsub (frontier_subset_closure hPfr₂))
      have hR₁R₂ : Disjoint R₁ R₂ := by
        rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
        rintro ⟨y, hyR₁, hyR₂⟩
        have hfr : Disjoint R₂ (frontier R₁) := by
          rw [hfr₁]
          refine disjoint_left.mpr fun x hx hx' => ?_
          have hxfr : x ∉ frontier R₂ := fun h => notMem_of_mem_frontier hR₂o h hx
          rcases hx' with h | h
          · exact hxfr (hfr₂ ▸ Or.inl h)
          · by_cases hAB : x ∈ ({A, B} : Set T)
            · rcases hAB with rfl | rfl
              exacts [hxfr hAfr₂, hxfr hBfr₂]
            · exact hC₁ext ⟨h, hAB⟩ (subset_closure hx)
        have hsub := conn_sub_of_frontier (hpc R₂ hR₂.2.1) hfr ⟨y, hyR₂, hyR₁⟩
        exact hDext (closure_mono hsub (frontier_subset_closure (hfr₂ ▸ Or.inr hD.1)))
      have h26 := th26 hopen hpc h21 harc h8 hext hcpt hnc hC₁ hX hC₂
        (by rw [inter_comm]; exact hXC₁) hC12 hXC₂ (by rw [hCJ]; exact hR)
        (by rw [union_comm]; exact hR₁) hR₂
      rcases h26 with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩
      · exact disjoint_left.mp hRR₁ hy.1 hy.2
      · exact disjoint_left.mp hRR₂ hy.1 hy.2
      · exact disjoint_left.mp hR₁R₂ hy.1 hy.2
    refine ⟨hCR₂, ?_⟩
    -- Theorem 25 for the curve `AXBDA` and the arc `ACB` within it
    have hC₁R₂ : C₁ \ {A, B} ⊆ R₂ :=
      conn_sub_of_frontier hC₁.isPreconnected_diff hC₁fr ⟨C, hC, hCR₂⟩
    exact th25 hopen hpc h21 harc h8 hext hR₂ hC₂ hX (by rw [inter_comm]; exact hXC₂)
      (union_comm _ _) hC₁ hC₁R₂ (by rw [hCJ]; exact hR) (by rw [union_comm]; exact hR₁)

end Gen

end HPC.Moore
