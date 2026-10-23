import HPC.Hagopian.H76Lemma5End

/-!
# Batch 169, §1.1: `R(E)` is meagre in `M`

Every extension of `E` (away from either end set) is a proper subcontinuum of `M` through a fixed
point `e ∈ E`: it is a continuum, and it is proper because it has a proper extension (Lemma 4,
applied to `k` or to the reversed map `σ ∘ k`). So `R(E)` lies in the composant of `e`, which is
meagre (Moore 136–137, `composant_isMeagre`). Consequently every nonempty open subset of `M`
contains points off `R(E)` (Baire).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- An extension of `E` away from an end set of `E` is a proper subcontinuum of `M`. -/
theorem extension_proper (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {X₀ : Set M}
    (hX₀ : X₀ = layer k 0 ∨ X₀ = layer k 1) {F : Set M} (hF : IsExtensionAway E X₀ F) :
    Fold.Q78.IsContinuum F ∧ F ≠ univ := by
  obtain ⟨d, ⟨⟨a, b, hab⟩, -, -⟩, -⟩ := hF.2
  refine ⟨⟨hab.1.1, hab.1.2⟩, fun hFu => ?_⟩
  have key : ∃ H, IsExtensionAway E X₀ H ∧ F ⊂ H := by
    rcases hX₀ with rfl | rfl
    · exact (hagopian76_lemma4 hX hi hE).2 F hF
    · have h1 : layer k 1 = layer (unitInterval.symm ∘ k) 0 := by
        rw [layer_symm_comp, unitInterval.symm_zero]
      rw [h1] at hF ⊢
      exact (hagopian76_lemma4 hX hi hE.symm_comp).2 F hF
  obtain ⟨H, -, hFH⟩ := key
  exact hFH.2 (hFu ▸ subset_univ H)

/-- `R(E)` lies in the composant of every point of `E`. -/
theorem Rset_subset_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {e : M} (he : e ∈ E) :
    Rset k ⊆ Jones.composant e := by
  rintro z (⟨F, hF, hzF⟩ | ⟨F, hF, hzF⟩)
  · obtain ⟨hFc, hFu⟩ := extension_proper hX hi hE (Or.inl rfl) hF
    exact ⟨F, hFc, hFu, hF.1 he, hzF⟩
  · obtain ⟨hFc, hFu⟩ := extension_proper hX hi hE (Or.inr rfl) hF
    exact ⟨F, hFc, hFu, hF.1 he, hzF⟩

/-- **`R(E)` is meagre in `M`** (commission 169 §1.1). -/
theorem isMeagre_Rset_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) : IsMeagre (Rset k) := by
  obtain ⟨y₀, hy₀⟩ := hE.2.1.2.1 0
  obtain ⟨y₁, hy₁⟩ := hE.2.1.2.1 1
  have hne : (y₀ : M) ≠ (y₁ : M) := by
    intro h
    have : y₀ = y₁ := Subtype.ext h
    rw [this, hy₁] at hy₀
    exact one_ne_zero hy₀
  haveI : Nontrivial M := ⟨⟨_, _, hne⟩⟩
  exact (composant_isMeagre hi (y₀ : M)).mono (Rset_subset_composant hX hi hE y₀.2)

/-- **Points off `R(E)` in every nonempty open set** (commission 169 §1.1): `M` is a Baire space. -/
theorem exists_notMem_Rset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {O : Set M} (hO : IsOpen O)
    (hOne : O.Nonempty) : ∃ p ∈ O, p ∉ Rset k :=
  exists_notMem_of_isMeagre hO hOne (isMeagre_Rset_aux hX hi hE)

end HPC.Hagopian
