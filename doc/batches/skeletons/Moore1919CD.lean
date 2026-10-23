import HPC.Moore.M19AB

/-!
# Batch 141 skeleton: Moore 1919, double rulings; Theorems C and D (pp. 172–176)

Save as `HPC/Moore/M19CD.lean` (splitting under `HPC/Moore/` is expected); add
`import HPC.Moore.M19CD` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted (this skeleton makes several modelling choices, listed in the commission), each change
recorded at the statement and in the report.

Transcribed from page images at 200 dpi (`doc/sources/moore1919.pdf`, pp. 172–176).

**The double ruling (footnote *, p. 172), as printed.**
On the closed curve `ABCDA` there are points `X₁ … Xₙ, Y₁ … Yₙ, X′ₙ … X′₁, Y′ₙ … Y′₁` in the order
`A X₁ X₂ ⋯ Xₙ B Y₁ Y₂ ⋯ Yₙ C X′ₙ X′ₙ₋₁ ⋯ X′₁ D Y′ₙ Y′ₙ₋₁ ⋯ Y′₁ A`.
There are arcs `X₁X′₁, …, XₙX′ₙ, Y₁Y′₁, …, YₙY′ₙ` which, except for their endpoints, lie entirely
within `ABCDA`. Finally, for every `i, j` (`1 ≤ i ≤ n`, `1 ≤ j ≤ n`), `XᵢX′ᵢ` has just one point in
common with `YⱼY′ⱼ` and no point in common with `XⱼX′ⱼ` (unless `i = j`).
Then these two sets of arcs are said to constitute a double ruling of the interior of `ABCDA`.
"The arcs `XᵢX′ᵢ` are said to be parallel to `BC` and to `AD` and the arcs `YᵢY′ᵢ` are said to be
parallel to `AB` and to `CD`." Footnote †: the sides of `ABCDA` are the segments `AB`, `BC`, `CD`,
`DA`, and "the interval `AB` of `J`" is the one not containing `C`.

**Modelling choices.**
* The two rulings may have different numbers of arcs (`n`, `m`); the printed definition uses `n` for
  both.
* The `Y`-arcs are required to be mutually disjoint; the printed definition omits this.
* The *subdivisions* are the components of `I − ⋃ arcs`.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

/-- A *quadrilateral* `ABCDA`: a closed curve `J` with interior `I`, divided by `A, B, C, D` into the
four sides `AB, BC, CD, DA` (arcs), consecutive sides meeting only in their common vertex and
opposite sides disjoint. -/
structure Space.Quad (σ : Space S) (J I : Set S) (A B C D : S) (sAB sBC sCD sDA : Set S) :
    Prop where
  interior : σ.IsInteriorOf J I
  ab : σ.IsArc A B sAB
  bc : σ.IsArc B C sBC
  cd : σ.IsArc C D sCD
  da : σ.IsArc D A sDA
  union : sAB ∪ sBC ∪ sCD ∪ sDA = J
  ab_bc : sAB ∩ sBC = {B}
  bc_cd : sBC ∩ sCD = {C}
  cd_da : sCD ∩ sDA = {D}
  da_ab : sDA ∩ sAB = {A}
  ab_cd : Disjoint sAB sCD
  bc_da : Disjoint sBC sDA

/-- A *double ruling* of the quadrilateral, with `n` arcs `XᵢX′ᵢ` (from `AB` to `CD`, "parallel to
`BC` and `AD`") and `m` arcs `YⱼY′ⱼ` (from `BC` to `DA`, "parallel to `AB` and `CD`"). -/
structure Space.DoubleRuling (σ : Space S) {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
    (_q : σ.Quad J I A B C D sAB sBC sCD sDA) (n m : ℕ) where
  X : Fin n → S
  X' : Fin n → S
  Y : Fin m → S
  Y' : Fin m → S
  arcX : Fin n → Set S
  arcY : Fin m → Set S
  orderAB : σ.InOrder sAB A B ([A] ++ List.ofFn X ++ [B])
  orderBC : σ.InOrder sBC B C ([B] ++ List.ofFn Y ++ [C])
  orderDC : σ.InOrder sCD D C ([D] ++ List.ofFn X' ++ [C])
  orderAD : σ.InOrder sDA A D ([A] ++ List.ofFn Y' ++ [D])
  isArcX : ∀ i, σ.IsArc (X i) (X' i) (arcX i)
  isArcY : ∀ j, σ.IsArc (Y j) (Y' j) (arcY j)
  withinX : ∀ i, openArc (X i) (X' i) (arcX i) ⊆ I
  withinY : ∀ j, openArc (Y j) (Y' j) (arcY j) ⊆ I
  crossXY : ∀ i j, ∃! P, P ∈ arcX i ∩ arcY j
  disjX : ∀ i i', i ≠ i' → Disjoint (arcX i) (arcX i')
  /-- Not in the printed definition (see the commission). -/
  disjY : ∀ j j', j ≠ j' → Disjoint (arcY j) (arcY j')

/-- The union of the arcs of a double ruling. -/
def Space.DoubleRuling.carrier {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
    {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ} (R : σ.DoubleRuling q n m) : Set S :=
  (⋃ i, R.arcX i) ∪ ⋃ j, R.arcY j

/-- The *subdivisions* of the double ruling: the components of `I − ⋃ arcs` (in the region
topology). -/
def Space.DoubleRuling.cells {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}
    {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ} (R : σ.DoubleRuling q n m) :
    Set (Set S) :=
  letI := σ.topology
  {U | ∃ x ∈ I \ R.carrier, U = connectedComponentIn (I \ R.carrier) x}

section M19CD

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Subdivision lemma** (used throughout 1919, never stated): every subdivision of a double
ruling is the interior of a closed curve lying in `J ∪ ⋃ arcs`; there are exactly `(n+1)(m+1)` of
them. (State the four-arc boundary of the cell `(i, j)` if that is the convenient form for later
batches.) -/
theorem doubleRuling_cell {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) {U : Set S} (hU : U ∈ R.cells) :
    ∃ J' : Set S, σ.IsInteriorOf J' U ∧ J' ⊆ J ∪ R.carrier := by
  sorry

theorem doubleRuling_cells_ncard {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) : R.cells.ncard = (n + 1) * (m + 1) := by
  sorry

/-- **Theorem C** (p. 172). If the closed curve `g` has only finitely many points in common with
`ABCDA` and contains none of `A, B, C, D`, the interior of `ABCDA` can be divided by a double ruling
into subdivisions each wholly within or wholly without `g`. Moore gives only an *"Indication of
proof"* (one example, Fig. 1). -/
theorem m19_theoremC (q : σ.Quad J I A B C D sAB sBC sCD sDA) {g Ig : Set S}
    (hg : σ.IsInteriorOf g Ig) (hfin : (g ∩ J).Finite) (hA : A ∉ g) (hB : B ∉ g) (hC : C ∉ g)
    (hD : D ∉ g) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, U ⊆ Ig ∨ U ⊆ σ.ext Ig := by
  sorry

/-- **Theorem D** (p. 173). If `G` is a set of closed curves and each point on or within `ABCDA` is
within some curve of `G`, the interior of `ABCDA` can be divided by a double ruling into subdivisions
each within some curve of `G`. (`G` is given as a set of (curve, interior) pairs.) -/
theorem m19_theoremD (q : σ.Quad J I A B C D sAB sBC sCD sDA) (G : Set (Set S × Set S))
    (hG : ∀ p ∈ G, σ.IsInteriorOf p.1 p.2) (hcov : ∀ P ∈ J ∪ I, ∃ p ∈ G, P ∈ p.2) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∃ p ∈ G, U ⊆ p.2 := by
  sorry

/-- **Refinement** (the step "The arcs of these rulings may be extended in such a way that there
will result a new double ruling … such that each arc of `τ₁` is also an arc of `τ₂`", p. 175, used
again in Theorem E). If each cell of a double ruling is itself given a double ruling, there is a
double ruling of the whole that refines the first and whose cells refine the cells of the cell
rulings. *The shape is left to you*; state what Theorem D's induction and Theorem E need. -/
theorem doubleRuling_refine : True := by
  sorry

end M19CD

end HPC.Moore
