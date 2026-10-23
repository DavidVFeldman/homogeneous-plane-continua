import HPC.Jones.Jones49F
import HPC.Jones.Jones55T2A
import HPC.Plane.Atriodic51Defs

/-!
# Batch 155, item J: a unicoherent homogeneous plane continuum is indecomposable

Hagopian 1975, proof of Theorem 1, paragraph 13: "Since `Y` is a unicoherent homogeneous plane
continuum, it is indecomposable [Jones 1955, Theorem 2]." Jones's Theorem 2 states that a
decomposable homogeneous plane continuum has a continuous monotone decomposition onto a simple
closed curve; the step to "not unicoherent" is the following. If `f : N → S¹` is the quotient map,
the preimages `H`, `K` of the two half-circles are continua (the decomposition is upper
semicontinuous with connected elements) with `H ∪ K = N`, and `H ∩ K` is the union of the two
disjoint nonempty closed sets `f⁻¹(1)` and `f⁻¹(-1)`.
-/

namespace HPC.Hagopian

open Set Topology HPC.Plane HPC.Jones

theorem indecomposable_of_unicoherent_homogeneous_aux {N : Set Pt} [CompactSpace N]
    [ConnectedSpace N] (hX : IsHomogeneous N) (hu : IsUnicoherent (univ : Set N)) :
    ¬ IsDecomposableSpace N := by
  intro hd
  obtain ⟨hcd, ⟨e⟩, hL⟩ := jones55_theorem2' hX hd
  obtain ⟨A, B, C₁, C₂, h₁, h₂, h12, hJ⟩ := HPC.Jones.tscc_circle
  set q := Quotient.mk (lSetoid N)
  have hconn : ∀ x, IsConnected (cls (lSetoid N) x) := fun x => by
    rw [cls_lSetoid hX x]; exact (hL x).1
  have harc₁ : IsCompact C₁ ∧ IsConnected C₁ := by
    obtain ⟨-, f, hf, rfl, -, -⟩ := h₁
    exact ⟨isCompact_range hf.continuous, isConnected_range hf.continuous⟩
  have harc₂ : IsCompact C₂ ∧ IsConnected C₂ := by
    obtain ⟨-, f, hf, rfl, -, -⟩ := h₂
    exact ⟨isCompact_range hf.continuous, isConnected_range hf.continuous⟩
  have hpre : ∀ {C : Set Circle}, IsCompact C ∧ IsConnected C →
      Fold.Q78.IsContinuum (q ⁻¹' (e ⁻¹' C)) := by
    intro C hC
    obtain ⟨hc, hcn⟩ := hC
    refine isContinuum_preimage hcd.1 hconn ⟨?_, ?_⟩
    · rw [← e.image_symm]; exact hc.image e.symm.continuous
    · rw [← e.image_symm]; exact hcn.image _ e.symm.continuous.continuousOn
  have hunion : q ⁻¹' (e ⁻¹' C₁) ∪ q ⁻¹' (e ⁻¹' C₂) = univ := by
    rw [← preimage_union, ← preimage_union, ← hJ]; rfl
  have hI := hu _ _ (hpre harc₁) (hpre harc₂) hunion
  rw [← preimage_inter, ← preimage_inter, h12] at hI
  have hsurj : Function.Surjective (fun x : N => e (q x)) :=
    e.surjective.comp Quotient.mk_surjective
  have hcont : Continuous (fun x : N => e (q x)) := e.continuous.comp continuous_quotient_mk'
  obtain ⟨xa, hxa⟩ := hsurj A
  obtain ⟨xb, hxb⟩ := hsurj B
  have hAB : A ≠ B := h₁.1
  have hI' := hI.2
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hI'
  have key := hI' ((fun x : N => e (q x)) ⁻¹' {A}) ((fun x : N => e (q x)) ⁻¹' {B})
    (isClosed_singleton.preimage hcont) (isClosed_singleton.preimage hcont)
    (by
      intro x hx
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr h)
    (by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_and]
      intro _ ha hb
      exact hAB (ha.symm.trans hb))
  rcases key with h | h
  · have : e (q xb) = A := h (show e (q xb) ∈ ({A, B} : Set Circle) from hxb ▸ Or.inr rfl)
    exact hAB (this.symm.trans hxb)
  · have : e (q xa) = B := h (show e (q xa) ∈ ({A, B} : Set Circle) from hxa ▸ Or.inl rfl)
    exact hAB (hxa.symm.trans this)

end HPC.Hagopian
