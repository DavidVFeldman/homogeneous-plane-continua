import HPC.Moore.M19CD2

/-!
# Batch 143 skeleton: Moore 1919, Theorems E and F (pp. 176–177)

Save as `HPC/Moore/M19EF.lean` (splitting under `HPC/Moore/` is expected); add
`import HPC.Moore.M19EF` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Transcribed from the page images at 200 dpi.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

section M19EF

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Theorem E** (p. 176). If `ABCDA` is a closed curve, there exist two sets of arcs `α₁` and `α₂`
such that:
(1) each arc of `α₁` lies wholly within `ABCDA`, except that its endpoints are on `AB` and `CD`;
(2) each arc of `α₂` lies wholly within `ABCDA`, except that its endpoints are on `BC` and `DA`;
(3) each point on `ABCDA`, with the exception of `A, B, C, D`, is an endpoint either of just one arc
of `α₁` or of just one arc of `α₂`;
(4) through each point within `ABCDA` there is just one arc of `α₁` and just one arc of `α₂`;
(5) each arc of `α₁` has just one point in common with each arc of `α₂`.
Arcs are recorded with their endpoints: `α₁ : Set (S × S × Set S)`. Read (3) as "of just one arc of
`α₁` or of just one arc of `α₂`, and not both"; record your reading. -/
theorem m19_theoremE (q : σ.Quad J I A B C D sAB sBC sCD sDA) :
    ∃ α₁ α₂ : Set (S × S × Set S),
      (∀ a ∈ α₁, σ.IsArc a.1 a.2.1 a.2.2 ∧ a.1 ∈ sAB ∧ a.2.1 ∈ sCD ∧
        openArc a.1 a.2.1 a.2.2 ⊆ I) ∧
      (∀ a ∈ α₂, σ.IsArc a.1 a.2.1 a.2.2 ∧ a.1 ∈ sBC ∧ a.2.1 ∈ sDA ∧
        openArc a.1 a.2.1 a.2.2 ⊆ I) ∧
      (∀ P ∈ J \ {A, B, C, D},
        ((∃! a, a ∈ α₁ ∧ (P = a.1 ∨ P = a.2.1)) ∧ ¬ ∃ a ∈ α₂, P = a.1 ∨ P = a.2.1) ∨
        ((∃! a, a ∈ α₂ ∧ (P = a.1 ∨ P = a.2.1)) ∧ ¬ ∃ a ∈ α₁, P = a.1 ∨ P = a.2.1)) ∧
      (∀ P ∈ I, (∃! a, a ∈ α₁ ∧ P ∈ a.2.2) ∧ (∃! a, a ∈ α₂ ∧ P ∈ a.2.2)) ∧
      (∀ a ∈ α₁, ∀ b ∈ α₂, ∃! P, P ∈ a.2.2 ∩ b.2.2) := by
  sorry

/-- **Schoenflies form** (stretch; not in Moore, but what Theorem E amounts to, and what batch 144
may want). `ABCDA` together with its interior is homeomorphic to the closed unit square, with the
sides going to the sides and `A, B, C, D` to the corners `(0,0), (0,1), (1,1), (1,0)`. -/
theorem m19_schoenflies (q : σ.Quad J I A B C D sAB sBC sCD sDA) :
    ∃ f : unitInterval × unitInterval → S, @IsEmbedding _ _ _ σ.topology f ∧ range f = J ∪ I ∧
      f (0, 0) = A ∧ f (0, 1) = B ∧ f (1, 1) = C ∧ f (1, 0) = D ∧
      f '' {p | p.1 = 0} = sAB ∧ f '' {p | p.2 = 1} = sBC ∧ f '' {p | p.1 = 1} = sCD ∧
      f '' {p | p.2 = 0} = sDA := by
  sorry

/-- **Theorem F** (p. 176). There is a countably infinite sequence of closed curves `J₁, J₂, …` such
that every point lies within one of them and, for every `n`, `Jₙ₊₁` encloses `Jₙ`. ("Encloses"
is read as: `Jₙ` and its interior lie within `Jₙ₊₁`.) -/
theorem m19_theoremF :
    ∃ Jn In : ℕ → Set S, (∀ n, σ.IsInteriorOf (Jn n) (In n)) ∧ (∀ P, ∃ n, P ∈ In n) ∧
      ∀ n, Jn n ∪ In n ⊆ In (n + 1) := by
  sorry

end M19EF

end HPC.Moore
