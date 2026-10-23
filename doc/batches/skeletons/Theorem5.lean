import HPC.PseudoArc.Statements79
import HPC.PseudoArc.Uniqueness

/-!
# Bing 1948, Theorems 5 and 6, and Theorem 12 unconditional

Skeleton for batch 80 (save as `HPC/PseudoArc/Theorem5.lean`; add `import HPC.PseudoArc.Theorem5`
to the root `HPC.lean`). Statements only; every proof is `sorry` and is a work item.

The statements `Theorem5Statement`, `Theorem6Statement`, `Theorem6PosStatement` are those of
`Statements79.lean`. Bing's induction (COMMISSION-batch80.md §3) applies "the theorem" to
configurations its own statement does not cover, so the proof is expected to go through a
generalised statement `Theorem5'` of the prover's design (§4 of the commission), from which the
three theorems below follow. That statement is to be added to this file with its docstring saying
exactly how it specialises to `Theorem5Statement`.
-/

namespace HPC.Description

variable {X : Type*} [MetricSpace X] {P Q : X}

/-- **Bing 1948, Theorem 5.** -/
theorem theorem5 [CompactSpace X] (Δ : Description X P Q) : Theorem5Statement Δ := by
  sorry

/-- **Bing 1948, Theorem 6**, with the deep level Bing's proof produces, for every tail of the
description. This is the hypothesis of Theorem 12. -/
theorem theorem6Pos_shift [CompactSpace X] (Δ : Description X P Q) (i : ℕ) :
    Theorem6PosStatement (Δ.shift i) := by
  sorry

/-- Pattern following holds for every description. -/
theorem patternFollowing [CompactSpace X] (Δ : Description X P Q) : Δ.PatternFollowing :=
  patternFollowing_of_theorem6Pos Δ (theorem6Pos_shift Δ)

end HPC.Description

namespace HPC

variable {X₁ X₂ : Type*} [MetricSpace X₁] [MetricSpace X₂]

/-- **Bing 1948, Theorem 12**, unconditional: two descriptions give homeomorphic continua, with
the end points corresponding. -/
theorem theorem12 [CompactSpace X₁] [CompactSpace X₂] {P₁ Q₁ : X₁} {P₂ Q₂ : X₂}
    (Δ₁ : Description X₁ P₁ Q₁) (Δ₂ : Description X₂ P₂ Q₂) (hPQ₁ : P₁ ≠ Q₁) (hPQ₂ : P₂ ≠ Q₂) :
    ∃ T : Δ₁.M ≃ₜ Δ₂.M,
      T ⟨P₁, Δ₁.P_mem_M⟩ = ⟨P₂, Δ₂.P_mem_M⟩ ∧ T ⟨Q₁, Δ₁.Q_mem_M⟩ = ⟨Q₂, Δ₂.Q_mem_M⟩ :=
  Description.exists_homeomorph Δ₁ Δ₂ hPQ₁ hPQ₂ Δ₁.patternFollowing Δ₂.patternFollowing

end HPC
