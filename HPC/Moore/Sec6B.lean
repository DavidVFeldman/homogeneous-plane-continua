import HPC.Moore.Sec6Th27

/-!
# Moore, F.A. (1916), §6: Theorems 24–27 (batch 138, item B)

Moore's statements, derived from the topological versions `Gen.th24_sub`, `Gen.th24_ext`,
`Gen.th24_disj`, `Gen.th25`, `Gen.th26`, `Gen.th27` (files `Sec6Th24.lean` … `Sec6Th27.lean`)
through the bridge of `Sec6A.lean`.

**Shape change (all four):** each statement carries the axioms its proof uses, instead of the
skeleton's Axioms 1–8; Axiom 6 is used by none of them.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-! ### The hypotheses of the topological setting, from Moore's axioms -/

theorem hopen_region : ∀ R ∈ σ.region, @IsOpen S σ.topology R := fun _ hR => isOpen_region hR

theorem hpc_region (h1 : σ.Axiom1) (h2 : σ.Axiom2) :
    ∀ R ∈ σ.region, @IsPreconnected S σ.topology R := fun R hR => (isConn_iff h1).mp (h2 R hR)

theorem hext_region (h1 : σ.Axiom1) (h3 : σ.Axiom3) :
    ∀ R ∈ σ.region, @IsPreconnected S σ.topology (@closure S σ.topology R)ᶜ := fun R hR => by
  have := (isConn_iff h1).mp (h3 R hR); rwa [ext_eq_compl_closure h1] at this

theorem separatesOn_iff (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) {J : Set S} {A B C D : S} {C₁ C₂ : Set S} :
    σ.SeparatesOn J A B C D C₁ C₂ ↔ @TArc S σ.topology A B C₁ ∧ @TArc S σ.topology A B C₂ ∧
      C₁ ∩ C₂ = {A, B} ∧ C₁ ∪ C₂ = J ∧ C ∈ C₁ \ {A, B} ∧ D ∈ C₂ \ {A, B} := by
  rw [Space.SeparatesOn, isArc_iff_tarc h1 h3 h4 h51, isArc_iff_tarc h1 h3 h4 h51]; rfl

/-! ### Theorem 24 -/

/-- **Theorem 24.** If `A`, `B` separate `C`, `D` on `J` (arcs `ACB`, `ADB`), `R` is the interior of
`J`, and `AXB` is an arc whose open part lies in `R`, then (1) `R₁`, the interior of `AXBCA`, lies
in `R`; (2) the open arc `ADB` is without `R₁`; (3) `R₁ ∩ R₂ = ∅`, where `R₂` is the interior of
`AXBDA`. *Axioms used: 1, 2, 3, 4, 5, 7.* Moore's proof: (1) Theorem 21; (2) Theorem 1; (3) Axiom 2
(`R₂` would lie in `R₁`, but `D` is a boundary point of `R₂` without `R₁`).
**Shape change:** the axioms are made explicit; the hypothesis that `AXB` is an arc is dropped
(the proof uses only that `AXBCA`, `AXBDA` have interiors and that the open arc lies in `R`). -/
theorem fa_theorem24 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) {J R : Set S} (hR : σ.IsInteriorOf J R) {A B C D : S}
    {C₁ C₂ : Set S} (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X : Set S}
    (hXR : openArc A B X ⊆ R) {R₁ R₂ : Set S} (hR₁ : σ.IsInteriorOf (X ∪ C₁) R₁)
    (hR₂ : σ.IsInteriorOf (X ∪ C₂) R₂) :
    R₁ ⊆ R ∧ openArc A B C₂ ⊆ σ.ext R₁ ∧ Disjoint R₁ R₂ := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  rw [isInteriorOf_iff h1 h3 h4 h51] at hR hR₁ hR₂
  obtain ⟨hC₁, hC₂, hC12, hCJ, -, -⟩ := (separatesOn_iff h1 h3 h4 h51).mp hsep
  have h21 := th21Prop h1 h3 h4 h5 h7
  have hC₁J : C₁ ⊆ J := hCJ ▸ subset_union_left
  have hC₂J : C₂ ⊆ J := hCJ ▸ subset_union_right
  have hA : A ∈ J := hC₁J hC₁.left_mem
  have hB : B ∈ J := hC₁J hC₁.right_mem
  have hR₁R := th24_sub h21 hR hA hB hC₁J hXR hR₁
  have hR₂R := th24_sub h21 hR hA hB hC₂J hXR hR₂
  have hext := th24_ext hopen_region hR hC₂J hC12 hXR hR₁ hR₁R
  refine ⟨hR₁R, by rw [ext_eq_compl_closure h1]; exact hext, ?_⟩
  exact th24_disj hopen_region (hpc_region h1 h2) hR hC₁J hR₁ hR₂ hR₂R hext hC₂.nonempty_diff

/-! ### Theorem 25 -/

/-- **Theorem 25.** Under the hypothesis of Theorem 24, `R = AXB (open) + R₁ + R₂`.
*Axioms used: 1, 2, 3, 4, 5, 7, 8.* Moore's proof, with the steps he calls clear or easy supplied
(see `Gen.th25`). **Shape change:** the axioms are made explicit; the points `C`, `D` of the
separation are not used (any points of the open arcs would do). -/
theorem fa_theorem25 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {J R : Set S} (hR : σ.IsInteriorOf J R)
    {A B C D : S} {C₁ C₂ : Set S} (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X : Set S}
    (hX : σ.IsArc A B X) (hXR : openArc A B X ⊆ R) {R₁ R₂ : Set S}
    (hR₁ : σ.IsInteriorOf (X ∪ C₁) R₁) (hR₂ : σ.IsInteriorOf (X ∪ C₂) R₂) :
    R = openArc A B X ∪ R₁ ∪ R₂ := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  rw [isInteriorOf_iff h1 h3 h4 h51] at hR hR₁ hR₂
  rw [isArc_iff_tarc h1 h3 h4 h51] at hX
  obtain ⟨hC₁, hC₂, hC12, hCJ, -, -⟩ := (separatesOn_iff h1 h3 h4 h51).mp hsep
  exact th25 hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7) (arcConn h1 h3 h4 h51 h2)
    (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3) hR hC₁ hC₂ hC12 hCJ hX hXR hR₁ hR₂

/-! ### Theorem 26 -/

/-- **Theorem 26.** If `ACB`, `ADB`, `AFB` are three arcs, no two with a common point other than
`A` and `B`, then the interiors of `ACBFA`, `ACBDA`, `ADBFA` are not mutually exclusive (some two
of them meet). *Axioms used: 1, 2, 3, 4, 5, 7, 8.* Moore's proof, simplified (see `Gen.th26`):
his Case I is reduced to Case II, and the auxiliary curves `J̄₁`, `J̄₂` and Theorem 25 are not
needed. **Shape change:** the axioms are made explicit. -/
theorem fa_theorem26 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {A B : S} {K₁ K₂ K₃ : Set S}
    (hK₁ : σ.IsArc A B K₁) (hK₂ : σ.IsArc A B K₂) (hK₃ : σ.IsArc A B K₃)
    (h12 : K₁ ∩ K₂ = {A, B}) (h13 : K₁ ∩ K₃ = {A, B}) (h23 : K₂ ∩ K₃ = {A, B})
    {R R₁ R₂ : Set S} (hR : σ.IsInteriorOf (K₁ ∪ K₃) R) (hR₁ : σ.IsInteriorOf (K₁ ∪ K₂) R₁)
    (hR₂ : σ.IsInteriorOf (K₂ ∪ K₃) R₂) :
    (R ∩ R₁).Nonempty ∨ (R ∩ R₂).Nonempty ∨ (R₁ ∩ R₂).Nonempty := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  rw [isInteriorOf_iff h1 h3 h4 h51] at hR hR₁ hR₂
  rw [isArc_iff_tarc h1 h3 h4 h51] at hK₁ hK₂ hK₃
  exact th26 hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7) (arcConn h1 h3 h4 h51 h2)
    (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3) (fun R hR => isCompact_closure_region h1 h4 hR)
    (not_isCompact_univ h1 h5) hK₁ hK₂ hK₃ h12 h13 h23 hR hR₁ hR₂

/-! ### Theorem 27 -/

/-- **Theorem 27.** If `A`, `B` separate `C`, `D` on `J` and the open arc `AXB` is without `J`,
then (1) `D` is without `AXBCA` or `C` is without `AXBDA`; (2) if `D` is without `AXBCA`, then `C`
is within `AXBDA`, and the interior of `AXBDA` is the open arc `ACB` + the interior of `ACBDA`
(`= J`) + the interior of `AXBCA`. *Axioms used: 1, 2, 3, 4, 5, 7, 8.* Moore's proof (Theorems 24,
25, 26 and Axiom 2). **Shape change:** the axioms are made explicit. -/
theorem fa_theorem27 (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {J R : Set S} (hR : σ.IsInteriorOf J R)
    {A B C D : S} {C₁ C₂ : Set S} (hsep : σ.SeparatesOn J A B C D C₁ C₂) {X : Set S}
    (hX : σ.IsArc A B X) (hXR : openArc A B X ⊆ σ.ext R) {R₁ R₂ : Set S}
    (hR₁ : σ.IsInteriorOf (X ∪ C₁) R₁) (hR₂ : σ.IsInteriorOf (X ∪ C₂) R₂) :
    (D ∈ σ.ext R₁ ∨ C ∈ σ.ext R₂) ∧
      (D ∈ σ.ext R₁ → C ∈ R₂ ∧ R₂ = openArc A B C₁ ∪ R ∪ R₁) := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  rw [isInteriorOf_iff h1 h3 h4 h51] at hR hR₁ hR₂
  rw [isArc_iff_tarc h1 h3 h4 h51] at hX
  rw [ext_eq_compl_closure h1] at hXR
  rw [ext_eq_compl_closure h1, ext_eq_compl_closure h1]
  obtain ⟨hC₁, hC₂, hC12, hCJ, hC, hD⟩ := (separatesOn_iff h1 h3 h4 h51).mp hsep
  exact th27 hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7) (arcConn h1 h3 h4 h51 h2)
    (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3) (fun R hR => isCompact_closure_region h1 h4 hR)
    (not_isCompact_univ h1 h5) hR hC₁ hC₂ hC12 hCJ hC hD hX hXR hR₁ hR₂

end HPC.Moore
