import HPC.Moore.M25C15

/-!
# Batch 147, item D: Moore 1925, Theorem 19 (p. 424)

**Theorem 19.** If `R` is a region and `p ∈ R`, there is a simple closed curve of elements lying in
`R` whose interior contains `p` and is a subset of `R`. Moore: \"With the use of Theorems 11, 12, 13,
17 and 18 this theorem may be proved by a method closely analogous to that employed to prove Theorem
36 in F.A.\"

The proof below is batch 139's proof of F.A. Theorem 36 (`fa_theorem36`, `Sec7B.lean`, with its
correction: the arc `BC` is cut at its first element off `R`), carried out in the space of elements
with Moore's regions as the neighbourhood basis. The letters are Moore's (F.A. pp. 151–152):

1. a closed curve `J` in a small region `Q` about an element `X₀ ≠ O` (Theorem 14), with
   interior `I ⊆ Q` (Theorem 12), so that `O` is in the exterior;
2. an arc `OA` meeting `J` only in `A` (F.A. Theorem 15, first point);
3. a boundary element `C` of `R` and an arc `BC` from `J` with `BC − C ⊆ R`, missing `OA` and
   meeting `J + I` only in `B` (Theorem 13 for `R − OA`; first points);
4. the arcs `AF₁B`, `AH₁B` of `J` (Theorem 10) and an arc `FZH` from `AF₁B` to `AH₁B`, missing
   `OA + AF₁B + BC` and lying, except for `F` and `H`, in the exterior of `J` (Theorem 13 for
   `R − (OA + AF₁B + BC)`, an arc with one end on the boundary of `R`; first points);
5. `B` is in the exterior of `ZHAFZ` (its interior lies in `R`, by Theorem 12, and the arc `BC`
   reaches `C ∉ R` without meeting it), so by Theorem 18 `A` is in the interior of `ZHBFZ`, and so is
   `O`, since `OA` does not meet that curve; and the interior lies in `R` (Theorem 12).

**Which of Moore's citations are used:** Theorem 11 (interiors and exteriors, throughout), Theorem 12
(steps 1, 5), Theorem 13 (steps 3, 4) and Theorem 18 (step 5). Theorem 17 is not used (nor is F.A.
Theorem 26 in batch 139's proof of F.A. Theorem 36). Theorems 10 and 14, which Moore does not cite,
are used as well (the arcs of `J`; the curve in `Q`, F.A. Theorem 35 in F.A.).
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Gen

variable {r : Setoid Pt}

namespace Gen

section General

variable {T : Type*} [TopologicalSpace T] [T2Space T]

/-- An arc inside an arc with the same ends is that arc. -/
theorem TArc.eq_of_subset {A B : T} {C D : Set T} (hC : TArc A B C) (hD : TArc A B D)
    (h : C ⊆ D) : C = D := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := hD
  by_contra hne
  exact (isCutArc_range hf).irreducible C h hne hC.left_mem hC.right_mem
    ⟨⟨_, hC.left_mem⟩, hC.isPreconnected⟩

/-- Two arcs `AB` meeting only in `A`, `B`: every arc from `A` to `B` inside their union is one
of them. -/
theorem TArc.eq_of_subset_union {A B : T} {D₁ D₂ C : Set T} (hD₁ : TArc A B D₁)
    (hD₂ : TArc A B D₂) (hint : D₁ ∩ D₂ = {A, B}) (hCJ : C ⊆ D₁ ∪ D₂) (hC : TArc A B C) :
    C = D₁ ∨ C = D₂ := by
  have hpc := hC.isPreconnected_diff
  have hAB : ∀ z, z ∈ D₁ → z ∈ D₂ → z = A ∨ z = B := fun z h1' h2' => by
    have : z ∈ D₁ ∩ D₂ := ⟨h1', h2'⟩
    rw [hint] at this; simpa using this
  have hcov : C \ {A, B} ⊆ D₂ᶜ ∪ D₁ᶜ := by
    rintro z ⟨hzC, hzAB⟩
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact hzAB (by simpa using hAB z h.2 h.1)
  have hdisj : C \ {A, B} ∩ (D₂ᶜ ∩ D₁ᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_diff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzC h2' h1'
    rcases hCJ hzC.1 with h | h
    · exact h1' h
    · exact h2' h
  rcases isPreconnected_iff_subset_of_disjoint.mp hpc _ _ hD₂.isClosed.isOpen_compl
      hD₁.isClosed.isOpen_compl hcov hdisj with h | h
  · left
    refine hC.eq_of_subset hD₁ fun z hz => ?_
    by_cases hzAB : z = A ∨ z = B
    · rcases hzAB with rfl | rfl
      · exact hD₁.left_mem
      · exact hD₁.right_mem
    · have : z ∉ D₂ := h ⟨hz, by simpa using hzAB⟩
      exact (hCJ hz).resolve_right this
  · right
    refine hC.eq_of_subset hD₂ fun z hz => ?_
    by_cases hzAB : z = A ∨ z = B
    · rcases hzAB with rfl | rfl
      · exact hD₂.left_mem
      · exact hD₂.right_mem
    · have : z ∉ D₁ := h ⟨hz, by simpa using hzAB⟩
      exact (hCJ hz).resolve_left this

end General

end Gen

section M25C19

variable (hG : MooreDecomp r)
include hG

/-- The interior of a closed curve lying in a Moore region lies in the region (Theorem 12). -/
theorem sccInterior_subset_of_subset {R J : Set (Quotient r)} (hR : mooreRegion R)
    (hJ : IsSCCElt J) (hJR : J ⊆ R) : sccInterior J ⊆ R := by
  obtain ⟨hIo, hIc, hIb, hfI, -⟩ := sccInterior_spec hG hJ
  exact m25_theorem12 hG ⟨hR.1, hR.2.1⟩ ⟨hIo, hIc⟩ hR.2.2.1 hIb hR.2.2.2 (by rw [hfI]; exact hJR)

theorem closure_sccInterior_subset {R J : Set (Quotient r)} (hR : mooreRegion R)
    (hJ : IsSCCElt J) (hJR : J ⊆ R) : closure (sccInterior J) ⊆ R := by
  rw [closure_sccInterior hG hJ]
  exact union_subset (sccInterior_subset_of_subset hG hR hJ hJR) hJR

/-- **Theorem 19** (p. 424). If `R` is a region and `p ∈ R`, there is a simple closed curve of
elements lying in `R` whose interior contains `p` and is a subset of `R`. (\"With the use of Theorems
11, 12, 13, 17 and 18 … closely analogous to that employed to prove Theorem 36 in F.A.\") -/
theorem m25_theorem19 {R : Set (Quotient r)} (hR : mooreRegion R) {p : Quotient r} (hp : p ∈ R) :
    ∃ J, IsSCCElt J ∧ J ⊆ R ∧ p ∈ sccInterior J ∧ sccInterior J ⊆ R := by
  haveI := t2Space_quot hG
  haveI := regularSpace_quot hG
  haveI := locallyConnectedSpace_quot hG
  have harc := arcConn_quot hG
  have hRo : IsOpen R := hR.1
  set O := p with hOp
  have hO : O ∈ R := hp
  -- Step 1: a closed curve `J` in `R` with `O` in its exterior
  obtain ⟨X₀, hX₀⟩ := ((m25_region_infinite hG hR ⟨O, hO⟩).diff (finite_singleton O)).nonempty
  obtain ⟨V, hV, -, hVsub⟩ := exists_mem_nhds_isClosed_subset
    ((hRo.sdiff isClosed_singleton).mem_nhds hX₀)
  obtain ⟨Q, hQ, -, hQV⟩ := exists_region_subset hG hV
  obtain ⟨J, hJ, hJQ⟩ := m25_theorem14 hG hQ
  set I := sccInterior J with hIdef
  obtain ⟨hIo, hIc, hIb, hfrI, hEo', hEc', hEb', hfrE', hdisIE, huIE⟩ := sccInterior_spec hG hJ
  have hcl : closure I = I ∪ J := closure_sccInterior hG hJ
  have hEeq : (closure I)ᶜ = sccExterior J := compl_closure_sccInterior hG hJ
  have hfrE : frontier (closure I)ᶜ = J := by rw [hEeq]; exact hfrE'
  have hclI : closure I ⊆ R \ {O} :=
    (closure_sccInterior_subset hG hQ hJ hJQ).trans (hQV.trans hVsub)
  have hJc : IsClosed J := hJ.1
  have hJR : J ⊆ R := fun x hx => (hclI (hcl ▸ Or.inr hx)).1
  have hOJ : O ∉ J := fun h => (hclI (hcl ▸ Or.inr h)).2 rfl
  have hJE : ∀ x ∈ J, x ∉ (closure I)ᶜ := fun x hx h => h (hcl ▸ Or.inr hx)
  -- Step 2: the arc `OA` meeting `J` only in `A`
  obtain ⟨A₁, hA₁⟩ : J.Nonempty := hJ.2.1.nonempty
  have hA₁O : A₁ ≠ O := fun h => hOJ (h ▸ hA₁)
  obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hR.2.1.isPreconnected O hO A₁ (hJR hA₁) hA₁O.symm
  obtain ⟨A, hAJ, Γ, hΓΓ₀, hΓ, hΓJ⟩ := hΓ₀.first_point hJc ⟨A₁, hΓ₀.right_mem, hA₁⟩ hOJ
  have hΓR : Γ ⊆ R := hΓΓ₀.trans hΓ₀R
  have hΓJ' : ∀ x ∈ Γ, x ∈ J → x = A := fun x hx hxJ => by
    have : x ∈ Γ ∩ J := ⟨hx, hxJ⟩
    rwa [hΓJ] at this
  -- Step 3: the boundary element `C` and the arc `BC`
  obtain ⟨C₀, hC₀⟩ : (frontier R).Nonempty :=
    nonempty_frontier_iff.2 ⟨⟨O, hO⟩, ne_univ_of_isBounded hR.2.2.1⟩
  have hC₀R : C₀ ∉ R := notMem_of_mem_frontier hRo hC₀
  have hK₀c : IsClosed (Γ ∪ closure I) := hΓ.isClosed.union isClosed_closure
  have hK₀R : Γ ∪ closure I ⊆ R := union_subset hΓR (hclI.trans diff_subset)
  obtain ⟨Rb, hRb, hC₀Rb, hRbK⟩ :=
    exists_region_subset hG (hK₀c.isOpen_compl.mem_nhds (fun h => hC₀R (hK₀R h)))
  have hRbK' : ∀ x ∈ Rb, x ∉ Γ ∧ x ∉ closure I := fun x hx => by
    have := hRbK hx; simp only [mem_compl_iff, mem_union, not_or] at this; exact this
  obtain ⟨D, hDRb, hDR⟩ := mem_closure_iff_nhds.mp hC₀.1 Rb (hRb.1.mem_nhds hC₀Rb)
  have hDJ : D ∉ J := fun h => (hRbK' D hDRb).2 (hcl ▸ Or.inr h)
  obtain ⟨B₁, hB₁J, hB₁A⟩ : ∃ B₁ ∈ J, B₁ ≠ A := hJ.2.2.1.exists_ne A
  have hRΓ : IsPreconnected (R \ Γ) := (m25_theorem13 hG hR (Or.inr ⟨O, A,
    (isArcElt_iff_tarc hG).2 hΓ, Or.inl (diff_subset.trans hΓR)⟩)).2.isPreconnected
  have hB₁Γ : B₁ ∉ Γ := fun h => hB₁A (hΓJ' B₁ h hB₁J)
  obtain ⟨Δ, hΔ, hΔa⟩ := harc (R \ Γ) (hRo.sdiff hΓ.isClosed) hRΓ B₁ ⟨hJR hB₁J, hB₁Γ⟩ D
    ⟨hDR, (hRbK' D hDRb).1⟩ (fun h => hDJ (h ▸ hB₁J))
  obtain ⟨B, hBJ, Δ', hΔ'Δ, hΔ', hΔ'J⟩ := hΔa.symm.first_point hJc ⟨B₁, hΔa.left_mem, hB₁J⟩ hDJ
  have hΔ'E : Δ' \ {B} ⊆ (closure I)ᶜ := by
    refine conn_sub_of_frontier hΔ'.isPreconnected_diff_right ?_ ⟨D, ⟨hΔ'.left_mem, ?_⟩, ?_⟩
    · rw [hfrE, disjoint_left]
      rintro x ⟨hx, hxB⟩ hxJ
      have : x ∈ Δ' ∩ J := ⟨hx, hxJ⟩
      rw [hΔ'J] at this; exact hxB this
    · rintro rfl; exact hDJ hBJ
    · intro h; exact (hRbK' D hDRb).2 h
  have hBA : B ≠ A := fun h => (hΔ (hΔ'Δ hΔ'.right_mem)).2 (h ▸ hΓ.right_mem)
  obtain ⟨Λ, hΛRb, hΛ⟩ := harc Rb hRb.1 hRb.2.1.isPreconnected D hDRb C₀ hC₀Rb
    (fun h => hC₀R (h ▸ hDR))
  have hΔ'R : Δ' ⊆ R := fun x hx => (hΔ (hΔ'Δ hx)).1
  obtain ⟨E₀, hE₀Δ', Λ', hΛ'Λ, hΛ', hΛ'Δ'⟩ := hΛ.symm.first_point hΔ'.isClosed
    ⟨D, hΛ.left_mem, hΔ'.left_mem⟩ (fun h => hC₀R (hΔ'R h))
  have hE₀B : E₀ ≠ B := fun h =>
    (hRbK' E₀ (hΛRb (hΛ'Λ hΛ'.right_mem))).2 (hcl ▸ Or.inr (h ▸ hBJ))
  obtain ⟨BE, hBEΔ', hBE⟩ := hΔ'.exists_sub hΔ'.right_mem hE₀Δ' hE₀B.symm
  have hβ₀ : TArc B C₀ (BE ∪ Λ') := by
    refine hBE.union hΛ'.symm (subset_antisymm ?_ ?_)
    · rintro x ⟨hx1, hx2⟩
      have : x ∈ Λ' ∩ Δ' := ⟨hx2, hBEΔ' hx1⟩
      rwa [hΛ'Δ'] at this
    · rintro x rfl; exact ⟨hBE.right_mem, hΛ'.right_mem⟩
  obtain ⟨C, hCRc, β, hββ₀, hβ, hβRc⟩ := hβ₀.first_point hRo.isClosed_compl
    ⟨C₀, hβ₀.right_mem, hC₀R⟩ (fun h => h (hJR hBJ))
  have hβR : β \ {C} ⊆ R := by
    rintro x ⟨hx, hxC⟩
    by_contra hxR
    have : x ∈ β ∩ Rᶜ := ⟨hx, hxR⟩
    rw [hβRc] at this; exact hxC this
  have hβK : ∀ x ∈ β, x ∈ Γ ∪ closure I → x = B := by
    intro x hx hxK
    rcases hββ₀ hx with h | h
    · have hxΔ' := hBEΔ' h
      rcases hxK with h' | h'
      · exact absurd h' (hΔ (hΔ'Δ hxΔ')).2
      · by_contra hxB
        exact hΔ'E ⟨hxΔ', hxB⟩ h'
    · have := hRbK' x (hΛRb (hΛ'Λ h))
      rcases hxK with h' | h'
      · exact absurd h' this.1
      · exact absurd h' this.2
  have hβJ : ∀ x ∈ β, x ∈ J → x = B := fun x hx hxJ => hβK x hx (Or.inr (hcl ▸ Or.inr hxJ))
  have hβΓ : Disjoint β Γ := by
    rw [disjoint_left]; intro x hx hxΓ
    have := hβK x hx (Or.inl hxΓ); subst this
    exact hBA (hΓJ' _ hxΓ hBJ)
  -- Step 4: the two arcs `AF₁B`, `AH₁B` of `J`, and the arc `FZH`
  obtain ⟨J₁, J₂, hJ₁e, hJ₂e, hJu, hJ12⟩ := m25_theorem10 hG hJ hAJ hBJ hBA.symm
  have hJ₁ := (isArcElt_iff_tarc hG).1 hJ₁e
  have hJ₂ := (isArcElt_iff_tarc hG).1 hJ₂e
  have hJ₁J : J₁ ⊆ J := hJu ▸ subset_union_left
  have hJ₂J : J₂ ⊆ J := hJu ▸ subset_union_right
  have hJ12' : ∀ x ∈ J₁, x ∈ J₂ → x = A ∨ x = B := fun x h1' h2' => by
    have : x ∈ J₁ ∩ J₂ := ⟨h1', h2'⟩
    rw [hJ12] at this; simpa using this
  obtain ⟨F₁, hF₁J₁, hF₁AB⟩ := hJ₁.nonempty_diff
  obtain ⟨H₁, hH₁J₂, hH₁AB⟩ := hJ₂.nonempty_diff
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hF₁AB hH₁AB
  have hZ₁c : IsClosed (Γ ∪ J₂ ∪ β ∪ Rᶜ) :=
    ((hΓ.isClosed.union hJ₂.isClosed).union hβ.isClosed).union hRo.isClosed_compl
  have hF₁Z : F₁ ∉ Γ ∪ J₂ ∪ β ∪ Rᶜ := by
    simp only [mem_union, mem_compl_iff, not_or, not_not]
    refine ⟨⟨⟨fun h => hF₁AB.1 (hΓJ' F₁ h (hJ₁J hF₁J₁)), fun h => ?_⟩,
      fun h => hF₁AB.2 (hβJ F₁ h (hJ₁J hF₁J₁))⟩, hJR (hJ₁J hF₁J₁)⟩
    rcases hJ12' F₁ hF₁J₁ h with h' | h'
    · exact hF₁AB.1 h'
    · exact hF₁AB.2 h'
  obtain ⟨R₁, hR₁, hF₁R₁, hR₁Z⟩ := exists_region_subset hG (hZ₁c.isOpen_compl.mem_nhds hF₁Z)
  have hR₁' : ∀ x ∈ R₁, x ∉ Γ ∧ x ∉ J₂ ∧ x ∉ β ∧ x ∈ R := fun x hx => by
    have := hR₁Z hx
    simp only [mem_compl_iff, mem_union, not_or, not_not] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  have hF₁cl : F₁ ∈ closure (closure I)ᶜ :=
    frontier_subset_closure (show F₁ ∈ frontier (closure I)ᶜ by rw [hfrE]; exact hJ₁J hF₁J₁)
  obtain ⟨L, hLR₁, hLE⟩ := mem_closure_iff_nhds.mp hF₁cl R₁ (hR₁.1.mem_nhds hF₁R₁)
  have hLJ : L ∉ J := fun h => hJE L h hLE
  obtain ⟨Λ₁, hΛ₁R₁, hΛ₁⟩ := harc R₁ hR₁.1 hR₁.2.1.isPreconnected L hLR₁ F₁
    hF₁R₁ (fun h => hLJ (h ▸ hJ₁J hF₁J₁))
  obtain ⟨F, hFJ, Φ₁, hΦ₁Λ₁, hΦ₁, hΦ₁J⟩ := hΛ₁.first_point hJc
    ⟨F₁, hΛ₁.right_mem, hJ₁J hF₁J₁⟩ hLJ
  have hΦ₁R₁ : Φ₁ ⊆ R₁ := hΦ₁Λ₁.trans hΛ₁R₁
  have hFJ₂ : F ∉ J₂ := (hR₁' F (hΦ₁R₁ hΦ₁.right_mem)).2.1
  have hFA : F ≠ A := fun h => hFJ₂ (h ▸ hJ₂.left_mem)
  have hFB : F ≠ B := fun h => hFJ₂ (h ▸ hJ₂.right_mem)
  have hconnE : ∀ {P Y : Quotient r} {Φ : Set (Quotient r)}, TArc P Y Φ → Φ ∩ J = {Y} →
      P ∈ (closure I)ᶜ → Φ \ {Y} ⊆ (closure I)ᶜ := by
    intro P Y Φ hΦ hΦJ hP
    refine conn_sub_of_frontier hΦ.isPreconnected_diff_right ?_ ⟨P, ⟨hΦ.left_mem, ?_⟩, hP⟩
    · rw [hfrE, disjoint_left]
      rintro x ⟨hx, hxY⟩ hxJ
      have : x ∈ Φ ∩ J := ⟨hx, hxJ⟩
      rw [hΦJ] at this; exact hxY this
    · rintro rfl
      have : P ∈ Φ ∩ J := by rw [hΦJ]; rfl
      exact hJE P this.2 hP
  have hΦ₁E := hconnE hΦ₁ hΦ₁J hLE
  -- the arc `κ = OA + AF₁B + BC`; Theorem 13 for `R − κ`
  have hκ : TArc O C (Γ ∪ J₁ ∪ β) := by
    refine (hΓ.union hJ₁ (subset_antisymm ?_ ?_)).union hβ (subset_antisymm ?_ ?_)
    · rintro x ⟨hx1, hx2⟩; exact hΓJ' x hx1 (hJ₁J hx2)
    · rintro x rfl; exact ⟨hΓ.right_mem, hJ₁.left_mem⟩
    · rintro x ⟨hx1 | hx1, hx2⟩
      · exact absurd hx1 (disjoint_left.mp hβΓ hx2)
      · exact hβJ x hx2 (hJ₁J hx1)
    · rintro x rfl; exact ⟨Or.inr hJ₁.right_mem, hβ.left_mem⟩
  have hκR : (Γ ∪ J₁ ∪ β) \ {C} ⊆ R := by
    rintro x ⟨(hx | hx) | hx, hxC⟩
    · exact hΓR hx
    · exact hJR (hJ₁J hx)
    · exact hβR ⟨hx, hxC⟩
  obtain ⟨hWo, hWc⟩ := m25_theorem13 hG hR (Or.inr ⟨O, C, (isArcElt_iff_tarc hG).2 hκ,
    Or.inr hκR⟩)
  have hLW : L ∈ R \ (Γ ∪ J₁ ∪ β) := by
    obtain ⟨hLΓ, -, hLβ, hLR⟩ := hR₁' L hLR₁
    refine ⟨hLR, ?_⟩
    rintro ((h | h) | h)
    · exact hLΓ h
    · exact hLJ (hJ₁J h)
    · exact hLβ h
  have hH₁W : H₁ ∈ R \ (Γ ∪ J₁ ∪ β) := by
    refine ⟨hJR (hJ₂J hH₁J₂), ?_⟩
    rintro ((h | h) | h)
    · exact hH₁AB.1 (hΓJ' H₁ h (hJ₂J hH₁J₂))
    · rcases hJ12' H₁ h hH₁J₂ with h' | h'
      · exact hH₁AB.1 h'
      · exact hH₁AB.2 h'
    · exact hH₁AB.2 (hβJ H₁ h (hJ₂J hH₁J₂))
  obtain ⟨Λ₂, hΛ₂W, hΛ₂⟩ := harc _ hWo hWc.isPreconnected L hLW H₁ hH₁W
    (fun h => hLJ (h ▸ hJ₂J hH₁J₂))
  obtain ⟨H, hHJ, Φ₂, hΦ₂Λ₂, hΦ₂, hΦ₂J⟩ := hΛ₂.first_point hJc
    ⟨H₁, hΛ₂.right_mem, hJ₂J hH₁J₂⟩ hLJ
  have hΦ₂W : Φ₂ ⊆ R \ (Γ ∪ J₁ ∪ β) := hΦ₂Λ₂.trans hΛ₂W
  have hHJ₁ : H ∉ J₁ := fun h => (hΦ₂W hΦ₂.right_mem).2 (Or.inl (Or.inr h))
  have hHA : H ≠ A := fun h => hHJ₁ (h ▸ hJ₁.left_mem)
  have hHB : H ≠ B := fun h => hHJ₁ (h ▸ hJ₁.right_mem)
  have hΦ₂E := hconnE hΦ₂ hΦ₂J hLE
  have hFJ₁ : F ∈ J₁ := by
    rcases (hJu ▸ hFJ : F ∈ J₁ ∪ J₂) with h | h
    · exact h
    · exact absurd h hFJ₂
  have hFH : F ≠ H := fun h => hHJ₁ (h ▸ hFJ₁)
  obtain ⟨Ψ, hΨ, hΨa⟩ := hΦ₁.symm.join hΦ₂.symm ⟨L, hΦ₁.left_mem, hΦ₂.left_mem⟩ hFH
  have hΨJ : ∀ x ∈ Ψ \ {F, H}, x ∉ J := by
    rintro x ⟨hx, hxFH⟩ hxJ
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxFH
    rcases hΨ hx with h | h
    · have : x ∈ Φ₁ ∩ J := ⟨h, hxJ⟩
      rw [hΦ₁J] at this; exact hxFH.1 this
    · have : x ∈ Φ₂ ∩ J := ⟨h, hxJ⟩
      rw [hΦ₂J] at this; exact hxFH.2 this
  have hΨE : Ψ \ {F, H} ⊆ (closure I)ᶜ := by
    rintro x ⟨hx, hxFH⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxFH
    rcases hΨ hx with h | h
    · exact hΦ₁E ⟨h, hxFH.1⟩
    · exact hΦ₂E ⟨h, hxFH.2⟩
  have hΨR : Ψ ⊆ R := fun x hx => by
    rcases hΨ hx with h | h
    · exact (hR₁' x (hΦ₁R₁ h)).2.2.2
    · exact (hΦ₂W h).1
  have hΨΓ : Disjoint Ψ Γ := by
    rw [disjoint_left]; intro x hx hxΓ
    rcases hΨ hx with h | h
    · exact (hR₁' x (hΦ₁R₁ h)).1 hxΓ
    · exact (hΦ₂W h).2 (Or.inl (Or.inl hxΓ))
  have hΨβ : Disjoint Ψ β := by
    rw [disjoint_left]; intro x hx hxβ
    rcases hΨ hx with h | h
    · exact (hR₁' x (hΦ₁R₁ h)).2.2.1 hxβ
    · exact (hΦ₂W h).2 (Or.inr hxβ)
  -- Step 5: the curves `ZHAFZ`, `ZHBFZ` and Theorem 18
  have key : ∀ Da Db : Set (Quotient r), TArc F H Da → TArc F H Db → Da ∩ Db = {F, H} →
      Da ∪ Db = J → A ∈ Da \ {F, H} → B ∈ Db \ {F, H} →
      ∃ J', IsSCCElt J' ∧ J' ⊆ R ∧ O ∈ sccInterior J' ∧ sccInterior J' ⊆ R := by
    intro Da Db hDa hDb hDab hDu hADa hBDb
    have hDaJ : Da ⊆ J := hDu ▸ subset_union_left
    have hDbJ : Db ⊆ J := hDu ▸ subset_union_right
    have hDae := (isArcElt_iff_tarc hG).2 hDa
    have hDbe := (isArcElt_iff_tarc hG).2 hDb
    have hΨe := (isArcElt_iff_tarc hG).2 hΨa
    have hΨJ' : ∀ z ∈ Ψ \ {F, H}, z ∉ Da ∪ Db := fun z hz h => hΨJ z hz (hDu ▸ h)
    obtain ⟨-, -, -, hZa, hZb⟩ := setting_int hG hDae hDbe hΨe hDab hΨJ'
    have hBDa : B ∉ Da := fun h => by
      have : B ∈ Da ∩ Db := ⟨h, hBDb.1⟩
      rw [hDab] at this; exact hBDb.2 this
    have hADb : A ∉ Db := fun h => by
      have : A ∈ Da ∩ Db := ⟨hADa.1, h⟩
      rw [hDab] at this; exact hADa.2 this
    -- `B` is in the exterior of `ZHAFZ`
    have hZaR : Da ∪ Ψ ⊆ R := union_subset (hDaJ.trans hJR) hΨR
    have hBRa : B ∈ sccExterior (Da ∪ Ψ) := by
      rw [← compl_closure_sccInterior hG hZa]
      have hclRa := closure_sccInterior_subset hG hR hZa hZaR
      intro hBcl
      have hBRa : B ∈ sccInterior (Da ∪ Ψ) := by
        rw [closure_sccInterior hG hZa] at hBcl
        rcases hBcl with h | h | h
        · exact h
        · exact absurd h hBDa
        · exact absurd hβ.left_mem (disjoint_left.mp hΨβ h)
      have hβRa : β ⊆ sccInterior (Da ∪ Ψ) := by
        refine conn_sub_of_frontier hβ.isPreconnected ?_ ⟨B, hβ.left_mem, hBRa⟩
        rw [(sccInterior_spec hG hZa).2.2.2.1, disjoint_left]
        rintro x hx (h | h)
        · have := hβJ x hx (hDaJ h); subst this; exact hBDa h
        · exact disjoint_left.mp hΨβ h hx
      exact hCRc (hclRa (subset_closure (hβRa hβ.right_mem)))
    -- by Theorem 18, `A` is in the interior of `ZHBFZ`
    have hΨext : Ψ \ {F, H} ⊆ sccExterior (Da ∪ Db) := by
      rw [hDu, ← hEeq]; exact hΨE
    have hDbside := diff_subset_int_or_ext hG hZa hDbe fun y hy hyZ =>
      hyZ.elim (fun h => hy.2 (hDab ▸ ⟨h, hy.1⟩))
        (fun h => hy.2 (by
          have : y ∈ Db ∩ Ψ := ⟨hy.1, h⟩
          by_contra hne
          exact hΨJ y ⟨h, hne⟩ (hDbJ hy.1)))
    have hDbE : Db \ {F, H} ⊆ sccExterior (Da ∪ Ψ) := hDbside.resolve_left fun hsub =>
      disjoint_left.1 (sccInterior_spec hG hZa).2.2.2.2.2.2.2.2.1 (hsub hBDb) hBRa
    have h18 := (m25_theorem18 hG hDae hDbe hΨe hDab hΨext).2 hDbE
    have hARc : A ∈ sccInterior (Db ∪ Ψ) := h18.1 hADa
    have hΓRc : Γ ⊆ sccInterior (Db ∪ Ψ) := by
      refine conn_sub_of_frontier hΓ.isPreconnected ?_ ⟨A, hΓ.right_mem, hARc⟩
      rw [(sccInterior_spec hG hZb).2.2.2.1, disjoint_left]
      rintro x hx (h | h)
      · have := hΓJ' x hx (hDbJ h); subst this; exact hADb h
      · exact disjoint_left.mp hΨΓ h hx
    have hZbR : Db ∪ Ψ ⊆ R := union_subset (hDbJ.trans hJR) hΨR
    exact ⟨Db ∪ Ψ, hZb, hZbR, hΓRc hΓ.left_mem, sccInterior_subset_of_subset hG hR hZb hZbR⟩
  -- `A` and `B` lie on different arcs of `J` from `F` to `H`
  obtain ⟨D₁, D₂, hD₁e, hD₂e, hDu, hD12⟩ := m25_theorem10 hG hJ hFJ hHJ hFH
  have hD₁ := (isArcElt_iff_tarc hG).1 hD₁e
  have hD₂ := (isArcElt_iff_tarc hG).1 hD₂e
  have hHJ₂ : H ∈ J₂ := (show H ∈ J₁ ∪ J₂ by rw [hJu]; exact hHJ).resolve_left hHJ₁
  have hsame : ∀ Dc : Set (Quotient r), TArc F H Dc → Dc ⊆ J → A ∈ Dc → B ∈ Dc → False := by
    intro Dc hDc hDcJ hADc hBDc
    obtain ⟨D', hD'Dc, hD', hFD', hHD'⟩ :=
      hDc.sub_avoid hADc hBDc hFA.symm hHA.symm hFB.symm hHB.symm hBA.symm
    rcases TArc.eq_of_subset_union hJ₁ hJ₂ hJ12 (hD'Dc.trans (hDcJ.trans hJu.symm.subset)) hD' with h | h
    · exact hFD' (h ▸ hFJ₁)
    · exact hHD' (h ▸ hHJ₂)
  have hAFH : A ∉ ({F, H} : Set (Quotient r)) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => hFA h.symm, fun h => hHA h.symm⟩
  have hBFH : B ∉ ({F, H} : Set (Quotient r)) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => hFB h.symm, fun h => hHB h.symm⟩
  have hD₁J : D₁ ⊆ J := hDu ▸ subset_union_left
  have hD₂J : D₂ ⊆ J := hDu ▸ subset_union_right
  have hAD : A ∈ D₁ ∪ D₂ := by rw [hDu]; exact hAJ
  have hBD : B ∈ D₁ ∪ D₂ := by rw [hDu]; exact hBJ
  rcases hAD with hA1 | hA2
  · have hB2 : B ∈ D₂ := hBD.resolve_left fun h => hsame D₁ hD₁ hD₁J hA1 h
    exact key D₁ D₂ hD₁ hD₂ hD12 hDu ⟨hA1, hAFH⟩ ⟨hB2, hBFH⟩
  · have hB1 : B ∈ D₁ := hBD.resolve_right fun h => hsame D₂ hD₂ hD₂J hA2 h
    exact key D₂ D₁ hD₂ hD₁ (by rw [inter_comm, hD12]) (by rw [union_comm, hDu])
      ⟨hA2, hAFH⟩ ⟨hB1, hBFH⟩

end M25C19

end HPC.Moore
