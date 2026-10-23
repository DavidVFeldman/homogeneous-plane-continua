import HPC.Plane.EndPoints51
import HPC.PseudoArc.Recon86Chain

/-!
# Bing, *Concerning hereditarily indecomposable continua* (Pacific J. Math. 1 (1951), 43–51),
# Theorem 1 and its consequences

Skeleton for batch 88 (save as `HPC/Plane/PseudoArc51.lean`; add `import HPC.Plane.PseudoArc51` to
the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Auxiliary statements may
be reshaped with the change recorded; `theorem1_HIC`, `theorem1_HIC'` and `isPseudoArc_iff_endPoints`
keep their conclusions.

`IsSnakeLike` (= Bing's "can be chained"), `IsEpsChain`, `IsEndPoint`, `OppositeEndPoints`,
`IsHereditarilyIndecomposable` are from `Snake51.lean` / `EndPoints51.lean`; `composant` from
`PseudoArc/Statements79.lean`; `Description` from `PseudoArc/Description.lean`.
-/

namespace HPC.Plane

open Set

variable {X : Type*} [MetricSpace X]

/-- **A pseudo-arc**: a nondegenerate chainable hereditarily indecomposable (compact) continuum
(Bing 1951, p. 45: "all of these continua are topologically equivalent and are pseudo-arcs"). -/
def IsPseudoArc (M : Set X) : Prop :=
  IsSnakeLike M ∧ IsHereditarilyIndecomposable M ∧ M.Nontrivial

/-- **The body of Bing's proof of Theorem 1**: a nondegenerate chainable hereditarily
indecomposable continuum with two points in different composants admits a description from the
one to the other whose continuum is `M`. (COMMISSION-batch88.md §2–3.) -/
theorem exists_description_of_chainable_HI {M : Set X} (hM : IsPseudoArc M) {p q : X}
    (hp : p ∈ M) (hq : q ∈ M) (hpq : q ∉ composant M p) :
    ∃ Δ : Description X p q, Δ.M = M := by
  sorry

/-- **Bing 1948, Theorem 12, without a compact ambient space**: two descriptions in arbitrary
metric spaces have homeomorphic continua with the end points corresponding (restrict to the
compact continua themselves, as `Transfer.lean` does for Theorem 13). -/
theorem theorem12_of {X₁ X₂ : Type*} [MetricSpace X₁] [MetricSpace X₂] {P₁ Q₁ : X₁} {P₂ Q₂ : X₂}
    (Δ₁ : Description X₁ P₁ Q₁) (Δ₂ : Description X₂ P₂ Q₂) (h₁ : P₁ ≠ Q₁) (h₂ : P₂ ≠ Q₂)
    (hc₁ : IsCompact Δ₁.M) (hc₂ : IsCompact Δ₂.M) :
    ∃ T : Δ₁.M ≃ₜ Δ₂.M,
      T ⟨P₁, Δ₁.P_mem_M⟩ = ⟨P₂, Δ₂.P_mem_M⟩ ∧ T ⟨Q₁, Δ₁.Q_mem_M⟩ = ⟨Q₂, Δ₂.Q_mem_M⟩ := by
  sorry

/-- **Bing 1951 (Pacific J. Math.), Theorem 1, the "in fact" clause.** -/
theorem theorem1_HIC {X' : Type*} [MetricSpace X'] {M : Set X} {M' : Set X'}
    (hM : IsPseudoArc M) (hM' : IsPseudoArc M') {p q : X} {p' q' : X'}
    (hp : p ∈ M) (hq : q ∈ M) (hpq : q ∉ composant M p)
    (hp' : p' ∈ M') (hq' : q' ∈ M') (hpq' : q' ∉ composant M' p') :
    ∃ T : M ≃ₜ M', T ⟨p, hp⟩ = ⟨p', hp'⟩ ∧ T ⟨q, hq⟩ = ⟨q', hq'⟩ := by
  sorry

/-- **Theorem 1**: any two pseudo-arcs are homeomorphic. (Also *Snake-like continua*, Theorem 1.) -/
theorem theorem1_HIC' {X' : Type*} [MetricSpace X'] {M : Set X} {M' : Set X'}
    (hM : IsPseudoArc M) (hM' : IsPseudoArc M') : Nonempty (M ≃ₜ M') := by
  sorry

/-- A pseudo-arc is homogeneous (Bing, p. 45). -/
theorem homogeneous_of_isPseudoArc {M : Set X} (hM : IsPseudoArc M) (p q : X) (hp : p ∈ M)
    (hq : q ∈ M) : ∃ T : M ≃ₜ M, T ⟨p, hp⟩ = ⟨q, hq⟩ := by
  sorry

/-- A nondegenerate subcontinuum of a pseudo-arc is a pseudo-arc, hence homeomorphic to it
(Bing, p. 45; Moise's property). -/
theorem isPseudoArc_of_subcontinuum {M K : Set X} (hM : IsPseudoArc M) (hK : K ⊆ M)
    (hKc : Fold.Q78.IsContinuum K) (hKnd : K.Nontrivial) : IsPseudoArc K := by
  sorry

/-- The continuum of a description with `P ≠ Q` is a pseudo-arc; in particular the plane continuum
of `Plane.pseudoArc_exists`, and by `theorem1_HIC'` every pseudo-arc is homeomorphic to it. -/
theorem isPseudoArc_of_description {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q)
    (hc : IsCompact Δ.M) : IsPseudoArc Δ.M := by
  sorry

/-- Points of different composants of a pseudo-arc are opposite end points of it (Bing 1951,
*Snake-like continua*, proof of Theorem 16, necessity, citing this paper's Theorem 1). -/
theorem oppositeEndPoints_of_composants {M : Set X} (hM : IsPseudoArc M) {p q : X} (hp : p ∈ M)
    (hq : q ∈ M) (hpq : q ∉ composant M p) : OppositeEndPoints M p q := by
  sorry

/-- **Bing 1951 (*Snake-like continua*), Theorem 16, complete**: a nondegenerate snake-like
continuum is a pseudo-arc iff each of its points is an end point. Sufficiency is batch 85's
`exists_not_endPoint_of_not_HI`. -/
theorem isPseudoArc_iff_endPoints {M : Set X} (hM : IsSnakeLike M) (hnd : M.Nontrivial) :
    IsPseudoArc M ↔ ∀ p ∈ M, IsEndPoint M p := by
  sorry

end HPC.Plane
