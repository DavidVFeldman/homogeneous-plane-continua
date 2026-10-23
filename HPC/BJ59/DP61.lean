import HPC.BJ59.BJ59B

/-!
# Batch 200, §6: Domokos–Prajs Theorem 6.1, both directions

* `IsAtomicCircPAMap.comp_homeomorph`: the transport lemma (fibres, openness, atomicity);
* `exists_atomic_of_plane_isCircleOfPA`: the argument of `nonvac_atomic` for a given plane circle
  of pseudo-arcs;
* `dp22_theorem61_iff` (statement verbatim from the skeleton).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-- **Transport of atomic maps** along a homeomorphism. -/
theorem IsAtomicCircPAMap.comp_homeomorph {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] {g : Y → Circle} (hg : IsAtomicCircPAMap g) (e : X ≃ₜ Y) :
    IsAtomicCircPAMap (g ∘ e) := by
  have hpre : ∀ z, (g ∘ e) ⁻¹' {z} = e.symm '' (g ⁻¹' {z}) := fun z => by
    rw [e.image_symm]; rfl
  refine ⟨hg.cont.comp e.continuous, hg.isOpenMap.comp e.isOpenMap,
    hg.surj.comp e.surjective, fun z => ?_, fun z L hL hLz => ?_⟩
  · rw [hpre]
    exact isPseudoArc_of_homeomorph (hg.fib z) (e.symm.image _)
  · have hL' : Fold.Q78.IsContinuum (e '' L) := ⟨hL.1.image e.continuous, hL.2.image _
      e.continuous.continuousOn⟩
    obtain ⟨x, hxL, hxz⟩ := hLz
    rcases hg.atomic z (e '' L) hL' ⟨e x, mem_image_of_mem _ hxL, hxz⟩ with h | h
    · left
      intro y hy
      exact h (mem_image_of_mem _ hy)
    · right
      intro y hy
      obtain ⟨y', hy', hyy⟩ := h (show e y ∈ g ⁻¹' {z} from hy)
      rw [e.injective hyy] at hy'
      exact hy'

/-- A plane circle of pseudo-arcs carries an atomic map onto the circle (the argument of
`nonvac_atomic`, for a given plane circle of pseudo-arcs). -/
theorem exists_atomic_of_plane_isCircleOfPA (h10 : BJThm10) {C : Set Pt} (hC : IsCircleOfPA C) :
    ∃ f : C → Circle, IsAtomicCircPAMap f := by
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hC
  haveI := hf.compactSpace
  haveI : ConnectedSpace C :=
    { isPreconnected_univ := hf.circ.1.2.isPreconnected
      toNonempty := ⟨hf.circ.1.2.nonempty.some⟩ }
  rcases circle_or_atomic_of_decomposable (isHomogeneous_of_isCircleOfPA h10 hC)
    (isDecomposableSpace_of_isCircPAMap hf) with hψ | h
  · exfalso
    obtain ⟨ψ⟩ := hψ
    set F : Set C := f ⁻¹' {1}
    have hK : IsPseudoArc (ψ '' F) := isPseudoArc_of_homeomorph (hf.fib 1) (ψ.image F)
    refine not_isPseudoArc_of_ne_univ_circle (fun hu => ?_) hK
    obtain ⟨x, hx⟩ := hf.surj (Circle.exp Real.pi)
    obtain ⟨y, hy, hyx⟩ : ψ x ∈ ψ '' F := hu ▸ mem_univ _
    have : y = x := ψ.injective hyx
    subst this
    have h1 : f y = 1 := hy
    rw [hx] at h1
    exact circle_exp_pi_ne_one h1
  · exact h

/-- **Domokos–Prajs, Theorem 6.1, both directions**, given Bing–Jones Theorem 10 and a plane circle
of pseudo-arcs. -/
theorem dp22_theorem61_iff (h10 : BJThm10) (hEx : BJPlaneExample) {X : Type} [MetricSpace X]
    [CompactSpace X] : IsCircleOfPA X ↔ ∃ f : X → Circle, IsAtomicCircPAMap f := by
  obtain ⟨C, hC⟩ := hEx
  constructor
  · intro hX
    obtain ⟨e⟩ := homeomorph_of_isCircleOfPA h10 hX hC
    obtain ⟨g, hg⟩ := exists_atomic_of_plane_isCircleOfPA h10 hC
    exact ⟨g ∘ e, hg.comp_homeomorph e⟩
  · rintro ⟨f, hf⟩
    exact isCircleOfPA_of_atomic h10 hf hC

end HPC.BJ59
