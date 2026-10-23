import HPC.Plane.Thm5

/-!
# Batch 108: Bing 1948 (Amer. J. Math.), *Some characterizations of arcs and simple closed curves*,
# §2: Theorem 5 and Corollary 2; Duke 1951 Theorem 12 in Bing's generality

Skeleton (save as `HPC/Plane/Arcs48.lean`; add `import HPC.Plane.Arcs48` to the root `HPC.lean`).
Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the change
recorded. No existing file is to be edited, except the audit.

Source: R. H. Bing, *Some characterizations of arcs and simple closed curves*, Amer. J. Math. 70
(1948) 497–506 — "the arcs paper", [4] of the Duke paper. Transcriptions in
COMMISSION-batch108.md §1. Everything is for a compact metric space `S` and continua `M ⊆ S`.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Bing's "cuts"** (p. 497): `R` *cuts `A` from `B` in `M`* if `M` contains a continuum
meeting both `A` and `B`, `R` is disjoint from `A` and from `B`, and `R` meets every continuum in
`M` meeting both `A` and `B`. -/
def Cuts (M R A B : Set S) : Prop :=
  (∃ K : Set S, Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ (K ∩ A).Nonempty ∧ (K ∩ B).Nonempty) ∧
    Disjoint R A ∧ Disjoint R B ∧
    ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ M → (K ∩ A).Nonempty → (K ∩ B).Nonempty →
      (K ∩ R).Nonempty

/-- A continuum *irreducible about* `R`: contains `R`, and no proper subcontinuum does. -/
def IrreducibleAbout (N R : Set S) : Prop :=
  Fold.Q78.IsContinuum N ∧ R ⊆ N ∧ ∀ K : Set S, Fold.Q78.IsContinuum K → K ⊆ N → R ⊆ K → K = N

/-- Existence of a subcontinuum irreducible about a nonempty closed `R ⊆ M` (Zorn / Brouwer
reduction). -/
theorem exists_irreducibleAbout {M R : Set S} (hM : Fold.Q78.IsContinuum M) (hR : IsClosed R)
    (hRM : R ⊆ M) (hne : R.Nonempty) : ∃ N ⊆ M, IrreducibleAbout N R := by
  sorry

/-- **Arcs paper, Theorem 5.** For each proper closed subset `R` of the compact continuum `M`
(nonempty, so that the continua in question exist) there is `p ∈ M ∖ R` such that the union of all
continua lying in `M ∖ {p}` and meeting `R` is dense in `M`. -/
theorem arcs_theorem5 {M R : Set S} (hM : Fold.Q78.IsContinuum M) (hR : IsClosed R) (hRM : R ⊆ M)
    (hne : R.Nonempty) (hRne : R ≠ M) :
    ∃ p ∈ M \ R, Dense[instTopologicalSpaceSubtype]
      ((↑) ⁻¹' (⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧ K ⊆ M \ {p} ∧ (K ∩ R).Nonempty}, K) :
        Set M) := by
  sorry

/-- The point case used by Duke Theorem 12: `R = {r}`, in the form "`M ⊆ closure (⋃ …)`". -/
theorem arcs_theorem5_point {M : Set S} (hM : Fold.Q78.IsContinuum M) (hnd : M.Nontrivial)
    {r : S} (hr : r ∈ M) :
    ∃ p ∈ M, p ≠ r ∧ M ⊆ closure (⋃ K ∈ {K : Set S | Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ p ∉ K ∧ r ∈ K}, K) := by
  sorry

/-- **Arcs paper, Corollary 2.** Each nondegenerate compact continuum contains two points neither
of which cuts between two open subsets of the continuum. -/
theorem arcs_corollary2 {M : Set S} (hM : Fold.Q78.IsContinuum M) (hnd : M.Nontrivial) :
    ∃ p q : S, p ∈ M ∧ q ∈ M ∧ p ≠ q ∧
      (∀ D E : Set S, IsOpen D → IsOpen E → (D ∩ M).Nonempty → (E ∩ M).Nonempty →
        ¬ Cuts M {p} (D ∩ M) (E ∩ M)) ∧
      (∀ D E : Set S, IsOpen D → IsOpen E → (D ∩ M).Nonempty → (E ∩ M).Nonempty →
        ¬ Cuts M {q} (D ∩ M) (E ∩ M)) := by
  sorry

/-- **Duke 1951, Theorem 12, B ⇒ A, in Bing's generality** (any compact continuum `M`), by his
own proof: for a nondegenerate subcontinuum `M' ∋ p`, Theorem 5 gives `q ≠ p` with the continua
in `M' ∖ {q}` through `p` dense in `M'`; under condition B these are nested, so their union is
connected with closure `M'`; a proper subcontinuum `H ∋ p, q` would be incomparable with some
member `K ⊄ H` of the family. -/
theorem condA_of_condB_general {M : Set S} (hM : Fold.Q78.IsContinuum M) {p : S}
    (hp : CondB M p) : CondA M p := by
  sorry

theorem theorem12_1951_general {M : Set S} (hM : Fold.Q78.IsContinuum M) (p : S) :
    CondA M p ↔ CondB M p := by
  sorry

end HPC.Plane
