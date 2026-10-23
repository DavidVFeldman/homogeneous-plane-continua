import HPC.Moore.M19AB

/-!
# Moore 1919: quadrilaterals and double rulings (batch 141, item A)

Verbatim from the batch-141 skeleton (`doc/batches/skeletons/Moore1919CD.lean`), transcribed from
the page images of `doc/sources/moore1919.pdf`, p. 172 (footnotes * and †).

**The double ruling (footnote *, p. 172), as printed.**
On the closed curve `ABCDA` there are points `X₁ … Xₙ, Y₁ … Yₙ, X′ₙ … X′₁, Y′ₙ … Y′₁` in the order
`A X₁ X₂ ⋯ Xₙ B Y₁ Y₂ ⋯ Yₙ C X′ₙ X′ₙ₋₁ ⋯ X′₁ D Y′ₙ Y′ₙ₋₁ ⋯ Y′₁ A`.
There are arcs `X₁X′₁, …, XₙX′ₙ, Y₁Y′₁, …, YₙY′ₙ` which, except for their endpoints, lie entirely
within `ABCDA`. Finally, for every `i, j` (`1 ≤ i ≤ n`, `1 ≤ j ≤ n`), `XᵢX′ᵢ` has just one point in
common with `YⱼY′ⱼ` and no point in common with `XⱼX′ⱼ` (unless `i = j`).

**Modelling choices** (commission, item A; see the report for whether they are needed).
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

end HPC.Moore
