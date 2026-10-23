import HPC.Hagopian.H76Setup

/-!
# Batch 158, item F (first part): the arc `π[E]` with its parametrization

`exists_quotient_plane_aux` (batch 157) constructs `γ t = π(k⁻¹(t))` and only returns the
homeomorphism `π[E] ≃ₜ [0, 1]`. Here the same construction returns `γ` itself: an embedding of
`[0, 1]` (continuous and injective on a compact space) with `π x = γ t` for `x ∈ k⁻¹(t)` and
`range γ = π[E]` (report 157 §5).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Quot

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **`exists_quotient_plane` with the parametrization** `γ t = π(k⁻¹(t))`. -/
theorem exists_quotient_plane'_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (π : Pt → Pt) (γ : unitInterval → Pt), IsQuotientMap π ∧
      (∀ p q, π p = π q ↔ layerSetoid k p q) ∧ IsEmbedding γ ∧
      (∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) ∧ range γ = π '' toPt E := by
  have hm := layerSetoid_mooreDecomp_aux hX hi hE
  obtain ⟨φ⟩ := HPC.Moore.m25_theorem22 hm
  set π : Pt → Pt := fun p => φ (Quotient.mk (layerSetoid k) p) with hπ
  have hπq : IsQuotientMap π := φ.isQuotientMap.comp isQuotientMap_quotient_mk'
  have hπeq : ∀ p q, π p = π q ↔ layerSetoid k p q := fun p q => by
    simp only [hπ, φ.injective.eq_iff]
    exact Quotient.eq
  haveI : CompactSpace E := isCompact_iff_compactSpace.1 hE.isCompact
  have hk : Continuous k := hE.2.1.1
  have hks : Function.Surjective k := hE.2.1.2.1
  choose σ hσ using hks
  set γ : unitInterval → Pt := fun t => π ((σ t : M) : Pt) with hγ
  have hrel : ∀ e : E, layerSetoid k ((σ (k e) : M) : Pt) ((e : M) : Pt) := fun e => by
    change layerKey k _ = layerKey k _
    rw [layerKey_of_mem, layerKey_of_mem, hσ]
  have hγk : γ ∘ k = fun e : E => π ((e : M) : Pt) := funext fun e => (hπeq _ _).2 (hrel e)
  have hkq : IsQuotientMap k := (hk.isClosedMap).isQuotientMap hk (hE.2.1.2.1)
  have hγc : Continuous γ := by
    rw [hkq.continuous_iff, hγk]
    exact hπq.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hγi : Function.Injective γ := fun t t' h => by
    have := (hπeq _ _).1 h
    change layerKey k _ = layerKey k _ at this
    rw [layerKey_of_mem, layerKey_of_mem, hσ, hσ] at this
    exact Sum.inl_injective this
  have hrange : range γ = π '' toPt E := by
    ext z; constructor
    · rintro ⟨t, rfl⟩; exact ⟨_, ⟨(σ t : M), (σ t).2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨k ⟨m, hm⟩, ?_⟩
      have := congrFun hγk ⟨m, hm⟩
      simpa using this
  refine ⟨π, γ, hπq, hπeq, (hγc.isClosedEmbedding hγi).isEmbedding, ?_, hrange⟩
  rintro t _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
  have he' : k e = t := he
  have := congrFun hγk e
  simp only [Function.comp_apply] at this
  rw [← this, he']

end Quot

end HPC.Hagopian
