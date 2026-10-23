import HPC.PseudoArc.Theorem14
import HPC.Plane.PseudoArc51

/-!
# Batch 114: the covering step of Bing 1948, Theorem 14, by Lehner's Lemma 3

Skeleton (save as `HPC/PseudoArc/Lehner.lean`; add `import HPC.PseudoArc.Lehner` at the end of
the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted
with the change recorded. Existing files edited only as the commission says (the open
`covering_step` and `exists_description_covering` move here from `Theorem14.lean`).

Source: G. R. Lehner, *Extending homeomorphisms on the pseudo-arc*, Trans. Amer. Math. Soc. 98
(1961) 369–394 (a dissertation under Bing). Its Lemma 3 (p. 375), in the case `n = 2`, is the
one-level covering claim `CoveringStep` to which Bing's Theorem 14 was reduced in batch 83; its
proof (p. 376) uses crookedness of one level in the previous one directly, not Bing's Theorem 9.
The transcription is in COMMISSION-batch114.md §1. Lehner's `W_m` are the levels `Δ.D m`; his
Theorem 2 is Moise's (subcontinua of a pseudo-arc are pseudo-arcs); his Theorem 3 is Bing's
Theorem 13 (`exists_description_from'`, here through `exists_description_of_steps` so that the
levels are consolidations of levels of `Δ`).
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- A nondegenerate subcontinuum of a pseudo-arc is a pseudo-arc (Moise; here from the
hereditary properties: `isSnakeLike_of_subcontinuum`, hereditary indecomposability is hereditary
by definition). -/
theorem isPseudoArc_of_subcontinuum {M W : Set X} (hM : Plane.IsPseudoArc M) (hW : W ⊆ M)
    (hWc : Fold.Q78.IsContinuum W) (hnt : W.Nontrivial) : Plane.IsPseudoArc W := by
  sorry

/-- The end points of an irreducible continuum lie in different composants of it. -/
theorem not_mem_composant_of_irreducible {W : Set X} {A B : X} (h : IsIrreducibleBetween W A B)
    (hAB : A ≠ B) : B ∉ composant W A := by
  sorry

/-- **An `ε`-chain of a sub-pseudo-arc from one end to the other**: for `W ⊆ M` irreducible
between `P'` and `R`, a chain from `P'` to `R` covering `W`, every link meeting `W`, of mesh
`< ε`. (From a description of `W` from `P'` to `R`, `exists_description_of_chainable_HI`, at a
deep level, dropping the links that miss `W` and renumbering — or stating that the levels of a
description have all links meeting its continuum, if that is already available.) -/
theorem exists_epsChain_of_irreducible [CompactSpace X] {M W : Set X} (hM : Plane.IsPseudoArc M)
    (hW : W ⊆ M) {P' R : X} (hirr : IsIrreducibleBetween W P' R) (hne : P' ≠ R) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (m : ℕ) (E : Chain X m), 2 ≤ m ∧ E.IsFrom P' R ∧ W ⊆ E.union ∧
      (∀ i, (E.link i ∩ W).Nonempty) ∧ ∀ i, diam (E.link i) < ε := by
  sorry

/-- A consolidation of a consolidation is a consolidation. -/
theorem Chain.IsConsolidationOf.trans {l m n : ℕ} {F : Chain X l} {G : Chain X m}
    {D : Chain X n} (h₁ : F.IsConsolidationOf G) (h₂ : G.IsConsolidationOf D) :
    F.IsConsolidationOf D := by
  sorry

/-- **A description of `M` from `P'` to `Q'` whose levels are consolidations of levels of `Δ`**
(Bing's Theorem 13 through `exists_description_of_steps` with the property carried). -/
theorem exists_description_consolidating [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) {P' Q' : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hQc : Q' ∉ composant Δ.M P') :
    ∃ Δ' : Description X P' Q', Δ'.M = Δ.M ∧ ∀ i, ∃ k, (Δ'.D i).IsConsolidationOf (Δ.D k) := by
  sorry

/-- **Lehner's Lemma 3, `n = 2`** (Trans. AMS 98 (1961), p. 375–376), in the form of the covering
step: for a description `Δ` of `M`, points `P'`, `Q'` of `M` in different composants, `R ≠ P'` in
the composant of `P'`, and `W` irreducible between `P'` and `R`, every level `L` admits a deeper
consolidation `F` of a level of `Δ`, a chain from `P'` to `Q'` with closures of links inside links
of `D_L` and mesh `≤ 1/(L+1)`, whose initial subchain from `P'` to `R` covers `W`. -/
theorem lehner_lemma3_two [CompactSpace X] {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q)
    {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    Description.CoveringStep Δ P' Q' R W := by
  sorry

/-- **The covering step** (formerly the open `Description.covering_step` of `Theorem14.lean`). -/
theorem Description.covering_step [CompactSpace X] {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q)
    {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    Description.CoveringStep Δ P' Q' R W :=
  lehner_lemma3_two Δ hPQ hP' hQ' hR hRc hQc hPR hW hWirr

/-- **The covering description** (formerly conditional): a description of `M` from `P'` to `Q'`
each of whose levels covers `W` by its initial subchain from `P'` to `R`. -/
theorem Description.exists_description_covering [CompactSpace X] {P Q : X} (Δ : Description X P Q)
    (hPQ : P ≠ Q) {P' Q' R : X} (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M)
    (hRc : R ∈ composant Δ.M P') (hQc : Q' ∉ composant Δ.M P') (hPR : P' ≠ R)
    {W : Set X} (hW : W ⊆ Δ.M) (hWirr : IsIrreducibleBetween W P' R) :
    ∃ Δ' : Description X P' Q', Δ'.M = Δ.M ∧
      ∀ i, ∃ b : Fin (Δ'.n i), ∃ h0b : (⟨0, (Δ'.isFrom i).1⟩ : Fin (Δ'.n i)) ≤ b,
        ((Δ'.D i).sub ⟨0, (Δ'.isFrom i).1⟩ b h0b).IsFrom P' R ∧
        W ⊆ (Δ'.D i).span ⟨0, (Δ'.isFrom i).1⟩ b :=
  Description.exists_description_covering_of_step Δ
    (Description.covering_step Δ hPQ hP' hQ' hR hRc hQc hPR hW hWirr)

end HPC
