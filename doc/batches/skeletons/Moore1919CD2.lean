import HPC.Moore.M19CD

/-!
# Batch 142 skeleton: Moore 1919, Theorem C corrected; Theorem D

Save as `HPC/Moore/M19CD2.lean` (splitting under `HPC/Moore/` is expected); add
`import HPC.Moore.M19CD2` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Batch 141 refuted Theorem C as printed (`not_m19_theoremC_printed`): a curve touching a side from
within admits no ruling. The corrected forms below exclude exactly that configuration: a point of
`g ∩ ABCDA` that is a common end of two pieces of `g` lying within `ABCDA`.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

/-- A *cross-cut* of the quadrilateral: an arc whose open part lies within `ABCDA` and whose ends lie
on `ABCDA`, distinct from `A, B, C, D`. -/
def Space.IsCrossCut (σ : Space S) (J I : Set S) (A B C D : S) (P Q : S) (K : Set S) : Prop :=
  σ.IsArc P Q K ∧ openArc P Q K ⊆ I ∧ P ∈ J ∧ Q ∈ J ∧ P ∉ ({A, B, C, D} : Set S) ∧
    Q ∉ ({A, B, C, D} : Set S)

section M19CD2

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Theorem C, cross-cut form** (the core of the correction). A finite system of pairwise disjoint
cross-cuts (so with pairwise distinct ends) can be absorbed into a double ruling: there is a double
ruling whose subdivisions meet none of the cross-cuts. -/
theorem m19_theoremC_crosscuts (q : σ.Quad J I A B C D sAB sBC sCD sDA) {k : ℕ}
    (P Q : Fin k → S) (K : Fin k → Set S) (hK : ∀ i, σ.IsCrossCut J I A B C D (P i) (Q i) (K i))
    (hdisj : ∀ i i', i ≠ i' → Disjoint (K i) (K i')) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∀ i, Disjoint U (K i) := by
  sorry

/-- **Theorem C, closed-curve-within form** (used in Theorem G, Fig. 3: "`Jₙ₊₁` can be divided by a
double ruling … into nine subdivisions of which the central one is `AₙBₙCₙDₙAₙ (Jₙ)`"). A closed
curve lying within `ABCDA` can be absorbed into a double ruling. State the nine-cell form Theorem G
needs if convenient. -/
theorem m19_theoremC_within (q : σ.Quad J I A B C D sAB sBC sCD sDA) {g Ig : Set S}
    (hg : σ.IsInteriorOf g Ig) (hgI : g ⊆ I) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, U ⊆ Ig ∨ U ⊆ σ.ext Ig := by
  sorry

/-- **Theorem C, corrected.** As printed, with the touching configuration excluded: no point of
`g ∩ J` is a common end of two arcs of `g` whose open parts lie within `ABCDA`. -/
theorem m19_theoremC_corrected (q : σ.Quad J I A B C D sAB sBC sCD sDA) {g Ig : Set S}
    (hg : σ.IsInteriorOf g Ig) (hfin : (g ∩ J).Finite) (hA : A ∉ g) (hB : B ∉ g) (hC : C ∉ g)
    (hD : D ∉ g)
    (hnotouch : ∀ P ∈ g ∩ J, ∀ Q₁ Q₂ : S, ∀ K₁ K₂ : Set S, σ.IsArc P Q₁ K₁ → σ.IsArc P Q₂ K₂ →
      K₁ ⊆ g → K₂ ⊆ g → K₁ \ {P} ⊆ I → K₂ \ {P} ⊆ I → K₁ ∩ K₂ = {P} → False) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, U ⊆ Ig ∨ U ⊆ σ.ext Ig := by
  sorry

/-- **Theorem D** (p. 173), as in the batch-141 skeleton (open there). -/
theorem m19_theoremD (q : σ.Quad J I A B C D sAB sBC sCD sDA) (G : Set (Set S × Set S))
    (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2) (hcov : ∀ P ∈ J ∪ I, ∃ p ∈ G, P ∈ p.2) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∃ p ∈ G, U ⊆ p.2 := by
  sorry

end M19CD2

end HPC.Moore
