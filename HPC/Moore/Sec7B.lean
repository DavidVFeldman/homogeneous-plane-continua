import HPC.Moore.Sec7A

/-!
# Moore, F.A. (1916), §7: Theorem 36 (batch 139)

**Theorem 36.** If `O` is a point of a region `R`, there is a simple closed curve which lies in `R`
and encloses `O`. Moore's proof (pp. 151–152) is followed step by step; the letters are his.

One step needs a correction. Moore takes an arc `DC` in a region `R̄` about the boundary point
`C` and claims that `BE + EC` is \"an arc `BC` every point of which, except `C`, is in `R`\". But
`R̄` need not lie in `R`, so `EC` may leave `R` before reaching `C`. The arc is cut at its first
point outside `R`, which is again a boundary point of `R`, and that point is used as `C`.

`fa_theorem36_interior_subset` (commission check 2) adds that the interior lies in `R`
(Theorem 21).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

namespace Gen

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Between two interior points of an arc there is a sub-arc avoiding both ends. -/
theorem TArc.sub_avoid {P Q a b : X} {D : Set X} (h : TArc P Q D) (ha : a ∈ D) (hb : b ∈ D)
    (haP : a ≠ P) (haQ : a ≠ Q) (hbP : b ≠ P) (hbQ : b ≠ Q) (hab : a ≠ b) :
    ∃ D' ⊆ D, TArc a b D' ∧ P ∉ D' ∧ Q ∉ D' := by
  obtain ⟨-, f, hf, rfl, rfl, rfl⟩ := h
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have hst : s ≠ t := fun e => hab (e ▸ rfl)
  refine ⟨_, image_subset_range _ _, TArc.image_uIcc hf hst, ?_, ?_⟩
  · rintro ⟨u, hu, hu0⟩
    have := hf.injective hu0; subst this
    rcases le_total s t with h | h
    · rw [uIcc_of_le h] at hu
      exact haP (by rw [le_antisymm hu.1 nonneg'])
    · rw [uIcc_of_ge h] at hu
      exact hbP (by rw [le_antisymm hu.1 nonneg'])
  · rintro ⟨u, hu, hu1⟩
    have := hf.injective hu1; subst this
    rcases le_total s t with h | h
    · rw [uIcc_of_le h] at hu
      exact hbQ (by rw [le_antisymm le_one' hu.2])
    · rw [uIcc_of_ge h] at hu
      exact haQ (by rw [le_antisymm le_one' hu.2])

end Gen

section Th36

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Theorem 36.** If `O` is a point in a region `R`, there exists a simple closed curve which lies
in `R` and encloses `O`. *Axioms used: 1–8.*
Moore's proof: a closed curve `J` in a region about a point `X ≠ O`, inside `R` and missing `O`
(Theorem 35), so that `O` is without `J` (Theorem 21); the arc `AO` meeting `J` only in `A`; a
boundary point `C` of `R` (Theorem 19) and an arc `BC` meeting `OA + J + I` only in `B`, with
`BC − C ⊆ R` (**corrected**: see the module docstring); points `F₁`, `H₁` of the two arcs
`AF₁B`, `AH₁B` of `J`; the arc `FZH` without `J` (Theorems 20, 33); then `B` is without `ZHAFZ`
(its interior lies in `R`, by Theorem 21, and `BC` cannot cross it), so by Theorem 27 `A` is within
`ZHBFZ`, and so is `O`, since `OA` does not meet `ZHBFZ`.
**Shape change:** the axioms are made explicit. -/
theorem fa_theorem36 {R : Set S} (hR : R ∈ σ.region) {O : S} (hO : O ∈ R) :
    ∃ J ⊆ R, ∃ I, σ.IsInteriorOf J I ∧ O ∈ I := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  have harc := arcConn h1 h3 h4 h51 h2
  have hRo : IsOpen R := isOpen_region hR
  -- Step 1: a closed curve `J` in `R` with `O` without it
  obtain ⟨X₀, hX₀R, hX₀O⟩ := exists_ne_of_region h1 h3 h51 hR hO
  obtain ⟨Q, hQ, hX₀Q, hQcl⟩ := exists_region_closure_subset h1 (hRo.sdiff isClosed_singleton)
    (show X₀ ∈ R \ {O} from ⟨hX₀R, hX₀O⟩)
  obtain ⟨J, hJQ, hJ⟩ := fa_theorem35 h1 h2 h3 h4 h5 h6 h7 h8 hQ ⟨X₀, hX₀Q⟩
  obtain ⟨I, hIr, hIJ⟩ := h8 J hJ
  have hI : σ.IsInteriorOf J I := ⟨hJ, hIr, hIJ⟩
  obtain ⟨hIo, hIc, hIne, hfrI, hEo, hEc, hEne, hfrE, hcl, hdis, hEJ, hcomp, hJcpt, hJt⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI
  have hJc : IsClosed J := hJcpt.isClosed
  have hIQ : I ⊆ Q := fa_theorem21 h1 h3 h4 h5 h7 hQ hIr
    (by rw [hIJ, cl_eq_closure h1]; exact hJQ.trans subset_closure)
  have hclI : closure I ⊆ R \ {O} := by
    rw [hcl]
    exact union_subset (hIQ.trans (subset_closure.trans hQcl))
      (hJQ.trans (subset_closure.trans hQcl))
  have hJR : J ⊆ R := fun x hx => (hclI (hcl ▸ Or.inr hx)).1
  have hOJ : O ∉ J := fun h => (hclI (hcl ▸ Or.inr h)).2 rfl
  have hJE : ∀ x ∈ J, x ∉ (closure I)ᶜ := fun x hx h => disjoint_left.mp hEJ h hx
  -- Step 2: the arc `OA` meeting `J` only in `A`
  obtain ⟨A₁, hA₁⟩ : J.Nonempty := by
    obtain ⟨P, Q', C₁, C₂, hC₁, -, -, rfl⟩ := hJt
    exact ⟨P, Or.inl hC₁.left_mem⟩
  have hA₁O : A₁ ≠ O := fun h => hOJ (h ▸ hA₁)
  obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo (hpc_region h1 h2 R hR) O hO A₁ (hJR hA₁) hA₁O.symm
  obtain ⟨A, hAJ, Γ, hΓΓ₀, hΓ, hΓJ⟩ := hΓ₀.first_point hJc ⟨A₁, hΓ₀.right_mem, hA₁⟩ hOJ
  have hΓR : Γ ⊆ R := hΓΓ₀.trans hΓ₀R
  have hΓJ' : ∀ x ∈ Γ, x ∈ J → x = A := fun x hx hxJ => by
    have : x ∈ Γ ∩ J := ⟨hx, hxJ⟩
    rwa [hΓJ] at this
  -- Step 3: the boundary point `C` and the arc `BC`
  obtain ⟨C₀, hC₀⟩ := fa_theorem19 h1 h4 h5 h3 hR ⟨O, hO⟩
  rw [bdry_eq_frontier h1] at hC₀
  have hC₀R : C₀ ∉ R := notMem_of_mem_frontier hRo hC₀
  have hK₀c : IsClosed (Γ ∪ closure I) := hΓ.isClosed.union isClosed_closure
  have hK₀R : Γ ∪ closure I ⊆ R := union_subset hΓR (hclI.trans diff_subset)
  obtain ⟨Rb, hRb, hC₀Rb, hRbK⟩ := (mem_nhds_iff_region h1).mp
    (hK₀c.isOpen_compl.mem_nhds (fun h => hC₀R (hK₀R h)))
  have hRbK' : ∀ x ∈ Rb, x ∉ Γ ∧ x ∉ closure I := fun x hx => by
    have := hRbK hx; simp only [mem_compl_iff, mem_union, not_or] at this; exact this
  obtain ⟨D, hDRb, hDR⟩ := mem_closure_iff_nhds.mp hC₀.1 Rb ((isOpen_region hRb).mem_nhds hC₀Rb)
  have hDJ : D ∉ J := fun h => (hRbK' D hDRb).2 (hcl ▸ Or.inr h)
  obtain ⟨B₁, hB₁J, hB₁A⟩ : ∃ B₁ ∈ J, B₁ ≠ A := by
    obtain ⟨P, Q', C₁, C₂, hC₁, -, -, rfl⟩ := hJt
    by_cases hP : P = A
    · exact ⟨Q', Or.inl hC₁.right_mem, fun h => hC₁.ne (hP.trans h.symm)⟩
    · exact ⟨P, Or.inl hC₁.left_mem, hP⟩
  have hRΓ : IsPreconnected (R \ Γ) := (isConn_iff h1).mp
    (fa_theorem34_region h1 h2 h3 h4 h5 h6 h7 h8 hR ((isArc_iff_tarc h1 h3 h4 h51).mpr hΓ) hΓR)
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
  obtain ⟨Λ, hΛRb, hΛ⟩ := harc Rb (isOpen_region hRb) (hpc_region h1 h2 Rb hRb) D hDRb C₀ hC₀Rb
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
  have hCfr : C ∈ frontier R :=
    mem_frontier_of_mem_closure hRo (closure_mono hβR hβ.mem_closure_diff_right) hCRc
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
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ12, hJu⟩ :=
    exists_two_arcs_of_isSCC h1 h3 h4 h51 hJ hAJ hBJ hBA.symm
  rw [isArc_iff_tarc h1 h3 h4 h51] at hJ₁ hJ₂
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
  obtain ⟨R₁, hR₁, hF₁R₁, hR₁Z⟩ := (mem_nhds_iff_region h1).mp (hZ₁c.isOpen_compl.mem_nhds hF₁Z)
  have hR₁' : ∀ x ∈ R₁, x ∉ Γ ∧ x ∉ J₂ ∧ x ∉ β ∧ x ∈ R := fun x hx => by
    have := hR₁Z hx
    simp only [mem_compl_iff, mem_union, not_or, not_not] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  have hF₁cl : F₁ ∈ closure (closure I)ᶜ :=
    frontier_subset_closure (show F₁ ∈ frontier (closure I)ᶜ by rw [hfrE]; exact hJ₁J hF₁J₁)
  obtain ⟨L, hLR₁, hLE⟩ := mem_closure_iff_nhds.mp hF₁cl R₁ ((isOpen_region hR₁).mem_nhds hF₁R₁)
  have hLJ : L ∉ J := fun h => hJE L h hLE
  obtain ⟨Λ₁, hΛ₁R₁, hΛ₁⟩ := harc R₁ (isOpen_region hR₁) (hpc_region h1 h2 R₁ hR₁) L hLR₁ F₁
    hF₁R₁ (fun h => hLJ (h ▸ hJ₁J hF₁J₁))
  obtain ⟨F, hFJ, Φ₁, hΦ₁Λ₁, hΦ₁, hΦ₁J⟩ := hΛ₁.first_point hJc
    ⟨F₁, hΛ₁.right_mem, hJ₁J hF₁J₁⟩ hLJ
  have hΦ₁R₁ : Φ₁ ⊆ R₁ := hΦ₁Λ₁.trans hΛ₁R₁
  have hFJ₂ : F ∉ J₂ := (hR₁' F (hΦ₁R₁ hΦ₁.right_mem)).2.1
  have hFA : F ≠ A := fun h => hFJ₂ (h ▸ hJ₂.left_mem)
  have hFB : F ≠ B := fun h => hFJ₂ (h ▸ hJ₂.right_mem)
  have hconnE : ∀ {P Y : S} {Φ : Set S}, TArc P Y Φ → Φ ∩ J = {Y} → P ∈ (closure I)ᶜ →
      Φ \ {Y} ⊆ (closure I)ᶜ := by
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
  -- the arc `κ = OA + AF₁B + BC` and Theorem 33
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
  have h33 := fa_theorem33 h1 h2 h3 h4 h5 h6 h7 h8 hR (A := C) (B := O)
    (by rw [bdry_eq_frontier h1]; exact hCfr) hO ((isArc_iff_tarc h1 h3 h4 h51).mpr hκ.symm) hκR
  have hWeq : R \ ((Γ ∪ J₁ ∪ β) \ {C}) = R \ (Γ ∪ J₁ ∪ β) := by
    ext x
    simp only [mem_diff, mem_singleton_iff, not_and, not_not]
    constructor
    · rintro ⟨hxR, h⟩
      refine ⟨hxR, fun hx => ?_⟩
      have := h hx; subst this; exact hCRc hxR
    · rintro ⟨hxR, h⟩; exact ⟨hxR, fun hx => absurd hx h⟩
  rw [hWeq, isConn_iff h1] at h33
  have hWo : IsOpen (R \ (Γ ∪ J₁ ∪ β)) := hRo.sdiff hκ.isClosed
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
  obtain ⟨Λ₂, hΛ₂W, hΛ₂⟩ := harc _ hWo h33 L hLW H₁ hH₁W (fun h => hLJ (h ▸ hJ₂J hH₁J₂))
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
  have hHJ₂ : H ∈ J₂ := (show H ∈ J₁ ∪ J₂ by rw [hJu]; exact hHJ).resolve_left hHJ₁
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
  -- Step 5: the curves `ZHAFZ`, `ZHBFZ` and Theorem 27
  have hTI : TInt σ.region J I := (isInteriorOf_iff h1 h3 h4 h51).mp hI
  have key : ∀ Da Db : Set S, TArc F H Da → TArc F H Db → Da ∩ Db = {F, H} → Da ∪ Db = J →
      A ∈ Da \ {F, H} → B ∈ Db \ {F, H} → ∃ J' ⊆ R, ∃ I', σ.IsInteriorOf J' I' ∧ O ∈ I' := by
    intro Da Db hDa hDb hDab hDu hADa hBDb
    have hDaJ : Da ⊆ J := hDu ▸ subset_union_left
    have hDbJ : Db ⊆ J := hDu ▸ subset_union_right
    have hZa := tscc_of_open_disjoint hDa hΨa hDaJ hΨJ
    have hZb := tscc_of_open_disjoint hDb hΨa hDbJ hΨJ
    obtain ⟨Ra, hRa, hRaZ⟩ := ax8Prop h1 h3 h4 h51 h8 _ hZa
    obtain ⟨Rc, hRc, hRcZ⟩ := ax8Prop h1 h3 h4 h51 h8 _ hZb
    have h27 := th27 hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7) harc
      (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3) (fun R hR => isCompact_closure_region h1 h4 hR)
      (not_isCompact_univ h1 h5) hTI hDa hDb hDab hDu hADa hBDb hΨa hΨE
      ⟨hZa, hRa, hRaZ⟩ ⟨hZb, hRc, hRcZ⟩
    have hBDa : B ∉ Da := fun h => by
      have : B ∈ Da ∩ Db := ⟨h, hBDb.1⟩
      rw [hDab] at this; exact hBDb.2 this
    have hADb : A ∉ Db := fun h => by
      have : A ∈ Da ∩ Db := ⟨hADa.1, h⟩
      rw [hDab] at this; exact hADa.2 this
    have hBRa : B ∈ (closure Ra)ᶜ := by
      have hZaR : Ψ ∪ Da ⊆ R := union_subset hΨR (hDaJ.trans hJR)
      have hRaR : Ra ⊆ R := th21Prop h1 h3 h4 h5 h7 R hR Ra hRa
        (by rw [hRaZ]; exact hZaR.trans subset_closure)
      have hclRa : closure Ra ⊆ R := by
        rw [closure_eq_union_frontier (isOpen_region hRa), hRaZ]; exact union_subset hRaR hZaR
      intro hBcl
      have hBRa : B ∈ Ra := by
        rw [closure_eq_union_frontier (isOpen_region hRa), hRaZ] at hBcl
        rcases hBcl with h | h | h
        · exact h
        · exact absurd hβ.left_mem (disjoint_left.mp hΨβ h)
        · exact absurd h hBDa
      have hβRa : β ⊆ Ra := by
        refine conn_sub_of_frontier hβ.isPreconnected ?_ ⟨B, hβ.left_mem, hBRa⟩
        rw [hRaZ, disjoint_left]
        rintro x hx (h | h)
        · exact disjoint_left.mp hΨβ h hx
        · have := hβJ x hx (hDaJ h); subst this; exact hBDa h
      exact hCRc (hclRa (subset_closure (hβRa hβ.right_mem)))
    have hARc : A ∈ Rc := (h27.2 hBRa).1
    have hΓRc : Γ ⊆ Rc := by
      refine conn_sub_of_frontier hΓ.isPreconnected ?_ ⟨A, hΓ.right_mem, hARc⟩
      rw [hRcZ, disjoint_left]
      rintro x hx (h | h)
      · exact disjoint_left.mp hΨΓ h hx
      · have := hΓJ' x hx (hDbJ h); subst this; exact hADb h
    refine ⟨Ψ ∪ Db, union_subset hΨR (hDbJ.trans hJR), Rc, ?_, hΓRc hΓ.left_mem⟩
    exact (isInteriorOf_iff h1 h3 h4 h51).mpr ⟨hZb, hRc, hRcZ⟩
  -- `A` and `B` lie on different arcs of `J` from `F` to `H`
  obtain ⟨D₁, D₂, hD₁, hD₂, hD12, hDu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hJ hFJ hHJ hFH
  rw [isArc_iff_tarc h1 h3 h4 h51] at hD₁ hD₂
  have hsame : ∀ Dc : Set S, TArc F H Dc → Dc ⊆ J → A ∈ Dc → B ∈ Dc → False := by
    intro Dc hDc hDcJ hADc hBDc
    obtain ⟨D', hD'Dc, hD', hFD', hHD'⟩ :=
      hDc.sub_avoid hADc hBDc hFA.symm hHA.symm hFB.symm hHB.symm hBA.symm
    rcases arc_eq_of_subset_union h1 h3 h4 h51 ((isArc_iff_tarc h1 h3 h4 h51).mpr hJ₁)
      ((isArc_iff_tarc h1 h3 h4 h51).mpr hJ₂) hJ12 (hJu ▸ hD'Dc.trans hDcJ)
      ((isArc_iff_tarc h1 h3 h4 h51).mpr hD') with h | h
    · exact hFD' (h ▸ hFJ₁)
    · exact hHD' (h ▸ hHJ₂)
  have hAFH : A ∉ ({F, H} : Set S) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => hFA h.symm, fun h => hHA h.symm⟩
  have hBFH : B ∉ ({F, H} : Set S) := by
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

/-- **Theorem 36, with the interior inside `R`** (unnumbered; commission check 2). Moore 1925,
Theorem 19, uses a closed curve "whose interior contains `p` and is a subset of `R`"; this is not
part of the printed Theorem 36 but follows from it by Theorem 21 (the boundary `J` of the interior
lies in `R ⊆ R'`). *Axioms used: 1–8.* -/
theorem fa_theorem36_interior_subset {R : Set S} (hR : R ∈ σ.region) {O : S} (hO : O ∈ R) :
    ∃ J ⊆ R, ∃ I, σ.IsInteriorOf J I ∧ O ∈ I ∧ I ⊆ R := by
  obtain ⟨J, hJR, I, hI, hOI⟩ := fa_theorem36 h1 h2 h3 h4 h5 h6 h7 h8 hR hO
  refine ⟨J, hJR, I, hI, hOI, fa_theorem21 h1 h3 h4 h5 h7 hR hI.2.1 ?_⟩
  rw [hI.2.2]
  exact fun x hx => (Or.inl (hJR hx) : x ∈ R ∪ σ.bdry R)

end Th36

end HPC.Moore
