import HPC.Moore.M19EF

/-!
# Batch 144 skeleton: Moore 1919, the end of the paper. A Σ-space is a number plane.

Save as `HPC/Moore/M19G.lean` (splitting under `HPC/Moore/` is expected); add `import HPC.Moore.M19G`
at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be adjusted, each change recorded
at the statement and in the report.

Route: the Schoenflies route recommended in REPORT-batch143 (accepted). Moore's Theorem G and his
final paragraph are derived as corollaries of the main theorem `m19_plane`.
-/

namespace HPC.Moore

open Set Topology Filter

variable {S : Type*} {σ : Space S}

section M19G

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Schoenflies with prescribed boundary.** Given parametrizations of the four sides (`φAB` from `A`
to `B`, `φBC` from `B` to `C`, `φDC` from `D` to `C`, `φAD` from `A` to `D`), the embedding of the
square can be chosen to restrict to them: `f (0, y) = φAB y`, `f (x, 1) = φBC x`, `f (1, y) = φDC y`,
`f (x, 0) = φAD x`. -/
theorem m19_schoenflies_boundary (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (φAB φBC φDC φAD : unitInterval → S)
    (hAB : @IsEmbedding _ _ _ σ.topology φAB ∧ range φAB = sAB ∧ φAB 0 = A ∧ φAB 1 = B)
    (hBC : @IsEmbedding _ _ _ σ.topology φBC ∧ range φBC = sBC ∧ φBC 0 = B ∧ φBC 1 = C)
    (hDC : @IsEmbedding _ _ _ σ.topology φDC ∧ range φDC = sCD ∧ φDC 0 = D ∧ φDC 1 = C)
    (hAD : @IsEmbedding _ _ _ σ.topology φAD ∧ range φAD = sDA ∧ φAD 0 = A ∧ φAD 1 = D) :
    ∃ f : unitInterval × unitInterval → S, @IsEmbedding _ _ _ σ.topology f ∧ range f = J ∪ I ∧
      (∀ y, f (0, y) = φAB y) ∧ (∀ x, f (x, 1) = φBC x) ∧ (∀ y, f (1, y) = φDC y) ∧
      (∀ x, f (x, 0) = φAD x) := by
  sorry

/-- **The annulus lemma** (the use of Fig. 3, p. 177). If the closed curve `J₂` encloses the closed
curve `J₁` (`J₁ ∪ I₁ ⊆ I₂`), the closed annulus `J₂ ∪ I₂ − I₁` is homeomorphic to a square annulus,
compatibly with a given homeomorphism of `J₁` onto the inner square. *The shape is left to you.*
Record whether Moore's nine-cell ruling (*"Jₙ₊₁ can be divided by a double ruling … into nine
subdivisions of which the central one is AₙBₙCₙDₙAₙ (Jₙ)"*, unargued) is proved along the way. -/
theorem m19_annulus : True := by
  sorry

/-- **Main theorem** (Moore 1919: "every space `S` that satisfies Σ₁ or Σ₂ is a number plane"). A
space satisfying Axioms 1–8 of F.A. is homeomorphic, in the region topology, to `ℝ²`. -/
theorem m19_plane : Nonempty (@Homeomorph S (ℝ × ℝ) σ.topology _) := by
  sorry

/-- **Theorem G** (p. 177), as a corollary. There are two sets `G₁`, `G₂` of open curves such that
(1) through each point there is just one curve of `G₁` and just one curve of `G₂`; (2) each curve of
`G₁` has just one point in common with each curve of `G₂`. An *open curve* is taken here as the image
of a closed embedding of `ℝ`. Also prove that such an image is an open curve in F.A.'s sense (p. 159:
"a closed, connected set of points `M` such that if `P` is a point of `M` then `M − P` is the sum of
two mutually exclusive connected point-sets, neither of which contains a limit point of the other
one"). -/
theorem m19_theoremG :
    ∃ G₁ G₂ : Set (Set S),
      (∀ k ∈ G₁ ∪ G₂, ∃ e : ℝ → S, @IsClosedEmbedding _ _ _ σ.topology e ∧ range e = k) ∧
      (∀ P, (∃! k, k ∈ G₁ ∧ P ∈ k) ∧ (∃! k, k ∈ G₂ ∧ P ∈ k)) ∧
      (∀ k ∈ G₁, ∀ l ∈ G₂, ∃! P, P ∈ k ∩ l) := by
  sorry

/-- **The final paragraph** (p. 178), in Moore's form. There is a one-to-one correspondence
`P ↦ (x_P, y_P)` between `S` and the number plane such that `P` is a sequential limit point of
`P₁, P₂, …` if and only if `lim x_{Pₙ} = x_P` and `lim y_{Pₙ} = y_P`. -/
theorem m19_final :
    ∃ e : S ≃ ℝ × ℝ, ∀ (P : S) (u : ℕ → S),
      σ.IsSeqLimit P u ↔ Tendsto (fun n => e (u n)) atTop (𝓝 (e P)) := by
  sorry

end M19G

end HPC.Moore
