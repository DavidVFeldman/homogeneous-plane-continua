import HPC.PseudoArc.Theorem13
import HPC.Fold.Theorem7

/-!
# Bing 1948, Theorems 14 and 15; irreducible subcontinua

Skeleton for batch 83 (save as `HPC/PseudoArc/Theorem14.lean`; add `import HPC.PseudoArc.Theorem14`
to the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be
adjusted with the change recorded, except that `theorem14` and `theorem15` keep their conclusions.

Conventions as in `Theorem13.lean`: `Δ : Description X P Q` with `P ≠ Q` in a compact `X`;
`composant Δ.M p` is the union of the proper subcontinua of `Δ.M` containing `p`
(`Statements79.lean`); `Fold.Q78.IsContinuum K` is `IsCompact K ∧ IsConnected K`.

The hypotheses Bing leaves implicit and the skeleton states are listed in COMMISSION-batch83.md
§3.2 and §3.5: `W_i ≠ M` in Theorem 15; `P_i ≠ R_i` in Theorem 14; `Q_i ∈ M`.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-- `W` is a continuum containing `A` and `B`, and no proper subcontinuum of `W` contains both:
Bing's "subcontinuum irreducible from `A` to `B`". -/
def IsIrreducibleBetween (W : Set X) (A B : X) : Prop :=
  Fold.Q78.IsContinuum W ∧ A ∈ W ∧ B ∈ W ∧
    ∀ K : Set X, Fold.Q78.IsContinuum K → K ⊆ W → A ∈ K → B ∈ K → K = W

/-- **Irreducible subcontinua exist.** A continuum containing `A` and `B` contains a subcontinuum
irreducible between them. (Zorn on the subcontinua containing `A` and `B`, ordered by reverse
inclusion; a nested intersection of continua is a continuum.) -/
theorem exists_irreducible [CompactSpace X] {K : Set X} (hK : Fold.Q78.IsContinuum K) {A B : X}
    (hA : A ∈ K) (hB : B ∈ K) : ∃ W, W ⊆ K ∧ IsIrreducibleBetween W A B := by
  sorry

namespace Description

variable {P Q : X}

/-- **The irreducible subcontinuum is unique** (Bing p. 742, last paragraph): in the described
continuum, two subcontinua both irreducible between the distinct points `A`, `B` coincide. Bing's
witness is the limit superior of the spans of the subchains `D_k(A, B)`; proof in
COMMISSION-batch83.md §3.1. -/
theorem irreducible_unique [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) {A B : X}
    (hA : A ∈ Δ.M) (hB : B ∈ Δ.M) (hAB : A ≠ B) {W₁ W₂ : Set X} (h₁ : W₁ ⊆ Δ.M) (h₂ : W₂ ⊆ Δ.M)
    (hi₁ : IsIrreducibleBetween W₁ A B) (hi₂ : IsIrreducibleBetween W₂ A B) : W₁ = W₂ := by
  sorry

/-- **Bing 1948, Theorem 14** (statement), with the implicit hypotheses `P_i ≠ R_i` and `Q_i ∈ M`
made explicit. -/
def Theorem14Statement (Δ : Description X P Q) : Prop :=
  ∀ (P₁ Q₁ R₁ P₂ Q₂ R₂ : X) (hP₁ : P₁ ∈ Δ.M) (hQ₁ : Q₁ ∈ Δ.M) (hR₁ : R₁ ∈ Δ.M)
    (hP₂ : P₂ ∈ Δ.M) (hQ₂ : Q₂ ∈ Δ.M) (hR₂ : R₂ ∈ Δ.M),
    R₁ ∈ composant Δ.M P₁ → R₂ ∈ composant Δ.M P₂ →
    Q₁ ∉ composant Δ.M P₁ → Q₂ ∉ composant Δ.M P₂ →
    P₁ ≠ R₁ → P₂ ≠ R₂ →
    ∃ T : Δ.M ≃ₜ Δ.M, T ⟨P₁, hP₁⟩ = ⟨P₂, hP₂⟩ ∧ T ⟨Q₁, hQ₁⟩ = ⟨Q₂, hQ₂⟩ ∧ T ⟨R₁, hR₁⟩ = ⟨R₂, hR₂⟩

/-- **Theorem 15 from Theorem 14** (Bing p. 741–742), with the implicit hypothesis `W_i ≠ M`.
`Q_i` "in a composant not containing `W_i`" is stated as `Q_i ∉ composant Δ.M P_i`
(COMMISSION-batch83.md §3.2). The image of `W₁` under `T`, read in `X`, is `W₂`. -/
theorem theorem15_of_theorem14 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    (h14 : Theorem14Statement Δ)
    {W₁ W₂ : Set X} (hW₁ : Fold.Q78.IsContinuum W₁) (hW₂ : Fold.Q78.IsContinuum W₂)
    (hW₁M : W₁ ⊆ Δ.M) (hW₂M : W₂ ⊆ Δ.M) (hW₁ne : W₁ ≠ Δ.M) (hW₂ne : W₂ ≠ Δ.M)
    (hnd₁ : W₁.Nontrivial) (hnd₂ : W₂.Nontrivial)
    {P₁ P₂ Q₁ Q₂ : X} (hP₁ : P₁ ∈ W₁) (hP₂ : P₂ ∈ W₂) (hQ₁ : Q₁ ∈ Δ.M) (hQ₂ : Q₂ ∈ Δ.M)
    (hQ₁c : Q₁ ∉ composant Δ.M P₁) (hQ₂c : Q₂ ∉ composant Δ.M P₂) :
    ∃ T : Δ.M ≃ₜ Δ.M, T ⟨P₁, hW₁M hP₁⟩ = ⟨P₂, hW₂M hP₂⟩ ∧ T ⟨Q₁, hQ₁⟩ = ⟨Q₂, hQ₂⟩ ∧
      (fun w : Δ.M => (T w : X)) '' {w | (w : X) ∈ W₁} = W₂ := by
  sorry

/-- **The covering description** (Bing's `X_{i,1}, X_{i,2}, …` in the proof of Theorem 14, "a
consequence of Theorem 9"): a description of `M` from `P'` to `Q'` each of whose levels has its
subchain from `P'` (link `0`) to `R` covering the subcontinuum `W` irreducible between `P'` and
`R`. Bing does not say how it follows; COMMISSION-batch83.md §3.3 records what is known. -/
theorem exists_description_covering [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    ∃ Δ' : Description X P' Q', Δ'.M = Δ.M ∧
      ∀ i, ∃ b : Fin (Δ'.n i), ∃ h0b : (⟨0, (Δ'.isFrom i).1⟩ : Fin (Δ'.n i)) ≤ b,
        ((Δ'.D i).sub ⟨0, (Δ'.isFrom i).1⟩ b h0b).IsFrom P' R ∧
        W ⊆ (Δ'.D i).span ⟨0, (Δ'.isFrom i).1⟩ b := by
  sorry

/-- **Bing 1948, Theorem 14.** Proof: COMMISSION-batch83.md §2 and §3.4 (the alternating
construction of Theorem 12 with `R`-positions carried, Theorem 5 three times per step, Theorem 11
with tracking at the end). -/
theorem theorem14 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) :
    Theorem14Statement Δ := by
  sorry

/-- **Bing 1948, Theorem 15.** -/
theorem theorem15 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    {W₁ W₂ : Set X} (hW₁ : Fold.Q78.IsContinuum W₁) (hW₂ : Fold.Q78.IsContinuum W₂)
    (hW₁M : W₁ ⊆ Δ.M) (hW₂M : W₂ ⊆ Δ.M) (hW₁ne : W₁ ≠ Δ.M) (hW₂ne : W₂ ≠ Δ.M)
    (hnd₁ : W₁.Nontrivial) (hnd₂ : W₂.Nontrivial)
    {P₁ P₂ Q₁ Q₂ : X} (hP₁ : P₁ ∈ W₁) (hP₂ : P₂ ∈ W₂) (hQ₁ : Q₁ ∈ Δ.M) (hQ₂ : Q₂ ∈ Δ.M)
    (hQ₁c : Q₁ ∉ composant Δ.M P₁) (hQ₂c : Q₂ ∉ composant Δ.M P₂) :
    ∃ T : Δ.M ≃ₜ Δ.M, T ⟨P₁, hW₁M hP₁⟩ = ⟨P₂, hW₂M hP₂⟩ ∧ T ⟨Q₁, hQ₁⟩ = ⟨Q₂, hQ₂⟩ ∧
      (fun w : Δ.M => (T w : X)) '' {w | (w : X) ∈ W₁} = W₂ :=
  theorem15_of_theorem14 Δ hPQ (theorem14 Δ hPQ) hW₁ hW₂ hW₁M hW₂M hW₁ne hW₂ne hnd₁ hnd₂
    hP₁ hP₂ hQ₁ hQ₂ hQ₁c hQ₂c

end Description

end HPC
