Commission read: `doc/batches/COMMISSION-batch141.md` (batch 141 — Part D, Moore V: Moore 1919, double rulings; Theorems C and D).

# Report, batch 141

`lake build HPC` succeeds with `import HPC.Moore.M19CD` added at the end of `HPC.lean`. The skeleton
is kept verbatim at `doc/batches/skeletons/Moore1919CD.lean`; the source is
`doc/sources/moore1919.pdf`, pp. 172–176. `HPC/Moore/M19CD.lean` is an umbrella module importing the
files below; its docstring has a table mapping each skeleton item to its file and outcome, and keeps
the statement of Theorem D (open) as a comment. The main build carries no `sorry`, and `sorryAx`
occurs in no line of `axioms.txt`.

**Outcome in one line.** Items A, B and E are *proved*; Theorem C (item C) as printed is *refuted*;
Theorem D (item D) is *open*, with the obstruction stated in `OPEN.md`; the region form of Theorem D
(check 5) is *proved relative to* the curve form.

| file | content |
|---|---|
| `HPC/Moore/M19CDDefs.lean` | `Space.Quad`, `Space.DoubleRuling`, `carrier`, `cells` (verbatim from the skeleton) |
| `HPC/Moore/M19CDTile.lean` | tilings (`Space.Tiling`): finite families of mutually exclusive interiors of closed curves; adding a cross-cut adds one tile (`Space.Tiling.add_arc`, `add_arc_finite`); the tiles are the components (`Space.Tiling.components`) |
| `HPC/Moore/M19CDCells.lean` | the subdivision lemma: `Space.DoubleRuling.tiling`, `doubleRuling_cell`, `doubleRuling_cells_ncard` |
| `HPC/Moore/M19CRefute.lean` | Theorem C as printed is false: `no_ruling_of_two_branches`, `tangent_configuration`, `not_m19_theoremC_printed` |
| `HPC/Moore/M19CDSplit.lean` | a cross-cut from `AB` to `CD` cuts `ABCDA` into two quadrilaterals (`Space.Quad.splitX`); rotation `Space.Quad.rot` |
| `HPC/Moore/M19CDRuling.lean` | rulings given by *sets* of arcs (`Space.ArcRuling`, `Space.cellsOf`); cuts (`Space.Quad.Cut`, `exists_cut`); restriction of a ruling to a half (`restrict_half`) |
| `HPC/Moore/M19CDCut.lean` | the two halves of a cut ruling (`Cut.inter_cl`, `Cut.restrictA`, `Cut.restrictB`, `Cut.X_eq`, `Cut.carrier_iffA/B`) |
| `HPC/Moore/M19CDGlue.lean` | gluing rulings of the two halves along the cut (`Cut.glue`) |
| `HPC/Moore/M19CDExt.lean` | adding an arc `Y` through a given point of `BC` (`Space.ArcRuling.extendY`, `extendY_finite`) |
| `HPC/Moore/M19CDRefine.lean` | refinement of a ruling by sets of arcs (`Space.ArcRuling.refine`) |
| `HPC/Moore/M19CDOrder.lean` | rulings by sets of arcs are exactly the double rulings, up to indexing (`Space.ArcRuling.sortX`, `Space.DoubleRuling.toArcRuling`, `Space.ArcRuling.toDoubleRuling`) |
| `HPC/Moore/M19CDMain.lean` | `doubleRuling_refine` (item E) and `doubleRuling_pad` (item A) |
| `HPC/Moore/M19CDRegion.lean` | `m19_theoremD_regions_of_curves` (check 5) |

## Items (commission §2), in order

Every statement carries only the axioms its proof uses; the skeleton's section assumed Axioms 1–8.
**That change of shape applies to every item and is not repeated below.** All names are in
`HPC.Moore`.

**A. Definitions — verbatim.** `Space.Quad`, `Space.DoubleRuling` (with `n`, `m` and `disjY`),
`carrier`, `cells`, exactly as in the skeleton.

* **Is choice (1), different numbers `n`, `m`, needed? No — it is a convenience.** `doubleRuling_pad`
  (*proved*, Axioms 1–8): every double ruling with `n` arcs `X` and `m` arcs `Y` extends, by adding
  arcs, to a double ruling with `max n m` arcs in each ruling, each arc of the given ruling being an
  arc of the new one and each subdivision of the new one lying in a subdivision of the given one. So
  padding to equal numbers is always possible, and every result stated with `n`, `m` gives one in the
  printed form. (The proof adds arcs `Y` through new points of `BC` with `Space.ArcRuling.extendY`,
  and arcs `X` by rotating.)
* **Fig. 1 (p. 173).** Counted on the page image: the arcs parallel to `AB` (Moore's list:
  `K₁D₁C₁B₁L₁, K₂D₂C₂B₂L₂, A₄B₄L₃, A₃B₃L₄, E₃D₃L₅, E₄D₄L₆, E₇A₇, K₃B₆A₆, K₄B₅A₅`) are **9**; those
  parallel to `BC` (`H₁B₃C₃D₃M₆, H₂B₄C₄D₄M₅, E₂D₂M₄, E₁D₁M₃, A₁B₁M₂, A₂B₂M₁, H₃B₆E₆, H₄B₅E₅`) are
  **8**. Moore's own example therefore does *not* have equally many arcs in the two rulings, against
  the letter of his definition; this supports choice (1). The figure is consistent with the text's
  lists.
* **Choice (2), the `Y`-arcs mutually disjoint.** Kept. In Fig. 1 the `Y`-arcs are disjoint, and every
  use requires it.

**B. The subdivision lemma — *proved*** (`doubleRuling_cell`, `doubleRuling_cells_ncard`; Axioms 1,
2, 3, 4, 5, 7, 8 — Axiom 6 is not used). Statements as in the skeleton. Both come from one statement,
`Space.DoubleRuling.tiling`: `I − (J + ⋃ arcs)` is the union of exactly `(n+1)(m+1)` mutually
exclusive interiors of closed curves lying on `J + ⋃ arcs`, and these are its components
(`Space.Tiling.components`), i.e. the cells. Proof: start with the single tile `I`; an arc `XᵢX′ᵢ`
meets `J` and the earlier arcs only in its ends and adds one tile; an arc `YⱼY′ⱼ` meets `J`, the
arcs `X` and the earlier arcs `Y` in its two ends and its `n` crossing points, and so is a chain of
`n + 1` cross-cuts of the current tiles, adding `n + 1` tiles (`Space.Tiling.add_arc`,
`add_arc_finite`: a cross-cut of a tile, ending on its boundary, splits it into two interiors of
closed curves, by Theorems 24–27 of F.A. via the Jordan package). Total
`1 + n + m(n+1) = (n+1)(m+1)`. The four-arc boundary of the cell `(i, j)` is not named; the tiling
form is the one used by the refinement (item E).

**C. Theorem C — *refuted as printed*** (`not_m19_theoremC_printed`; Axioms 1–8). In every space
satisfying Axioms 1–8 there are a quadrilateral `ABCDA` and a closed curve `g` meeting it in a single
point `p` of the segment `AB` (none of `A, B, C, D`), `g` lying otherwise within `ABCDA`
(`tangent_configuration`: in the plane, a circle inside a square touching one side), and no double
ruling of `ABCDA` has every subdivision within or without `g`. The reason
(`no_ruling_of_two_branches`): every point of `g` within `ABCDA` would lie on an arc of the ruling;
near `p` the only arc of the ruling is the arc `XᵢX′ᵢ` with `Xᵢ = p`, if any (the arcs `Y` end on
`BC` and `DA`, the other arcs `X` stay away from `p`); and `g` leaves `p` along two arcs meeting only
at their ends, which would both have to begin along that one arc from its end `p`, and so would
overlap. The hypothesis "finitely many points in common" does not exclude touching. **No corrected
Theorem C is proved.** The suggested routes were examined (ledger, check 3): Moore's set `K` of arcs
of `g` does not exist in the counterexample (the part of `g` within `ABCDA` is a single open arc whose
two ends are the same point `p`), and the case `g ∩ J = ∅` (where Theorem C is true, and is needed
in Theorem G of batch 142) is not covered by the indication either.

**D. Theorem D — *open*.** The skeleton's statement is kept, commented out, in
`HPC/Moore/M19CD.lean`; the obstruction is recorded in `OPEN.md`. Of the parts of Moore's proof,
the arc of footnote * of p. 174 (`m19_D_arc`, batch 140), Theorem B (batch 140) and the extension /
refinement steps (item E) are available; what is missing:

1. Moore applies Theorem C to `ĀB̄C̄D̄` and `g₁`, where `J̄` is only known (by Theorem B) to meet `g₁`
   in finitely many points. `g₁` may touch `J̄` without crossing it, and then Theorem C fails
   (item C). A corrected Theorem C would be needed (for instance, for curves crossing `ABCDA` at each
   common point, together with the case of a curve within `ABCDA`), and the choice of `J̄` would have
   to secure its hypothesis.
2. In the induction over `g₂, …, gₘ` Moore applies the same reasoning to the subdivisions of `τ₁`
   lying without `g₁` (*"each such subdivision can itself be divided by a double ruling … into
   subdivisions each of which is either wholly within some curve of the set `G` or wholly without
   `g₂`"*). The boundaries of these subdivisions are arcs of `τ₁`, about which nothing restricts the
   intersection with `g₂`; so this is not an application of Theorem C even as printed, but a form of
   Theorem D itself (for the cover `G` together with the exterior of `g₂`).
3. The construction of `J′` and of the arcs of the annulus (*"It easily follows that there exist
   (Fig. 2) …"*) is not formalized.

**E. Refinement — *proved*** (`doubleRuling_refine`, Axioms 1–8; shape chosen). Let `Good` be a
property of sets inherited by subsets. If every subdivision of a double ruling `R` of `ABCDA`, taken as
the interior of a quadrilateral in any way, has a double ruling all of whose subdivisions are `Good`,
then `ABCDA` has a double ruling `R′` such that each arc of `R` is an arc of `R′`, and each
subdivision of `R′` is `Good` and lies in a subdivision of `R`. This is what both uses need: in
Theorem D (p. 175), `Good U` = "*`U` is wholly without `g₁, …, gₖ` or wholly within some curve of
`G`*"; in Theorem E (p. 176), `Good U` = "*`U` lies within some region of `Gₙ₊₁`*". Proof:
`Space.ArcRuling.refine`, by induction on the number of arcs. Cut along an arc `x` of `𝒳` (if `𝒳`
is empty, along an arc of `𝒴`, after rotating; `Space.Quad.splitX`, `Space.Quad.exists_cut`),
restrict the ruling to the two halves (`restrict_half`, `Cut.restrictA/B`), refine each half by
induction, make the arcs `Y` of the two halves end at the same points of `x` by the extension lemma
(`Space.ArcRuling.extendY_finite`), and glue (`Cut.glue`); then sort the arcs
(`Space.ArcRuling.toDoubleRuling`). The extension lemma (`extendY`: through each point of the open
side `BC` on no arc `Y` passes an arc `y` with `(𝒳, 𝒴 + y)` a ruling) is itself proved by the same
cut-and-glue induction, with Theorem 35 (`exists_arc_through`) for the empty ruling.

**Check 5 (region form of Theorem D) — *proved relative to the curve form***
(`m19_theoremD_regions_of_curves`, Axioms 1–8). If the conclusion of Theorem D holds (for the given
`ABCDA`) for every set of closed curves whose interiors cover `ABCDA` and its interior, then it holds
for every set of regions covering them: each point of a region is within a closed curve whose
interior lies in the region (Theorem 36 with Theorem 21, `fa_theorem36_interior_subset`). So the
curve form suffices for Moore's use in Theorem E; no separate region form is needed.

## Ledger entries (`LEDGER.md` §6, new subsection "Moore 1919, double rulings; Theorems C and D (batch 141)")

1. **The double ruling definition** (footnote *, p. 172): equal numbers of arcs, and no disjointness
   of the `Y`-arcs. Equal numbers: not needed (`doubleRuling_pad`), and Moore's own Fig. 1 has 9 and 8
   arcs. `Y`-arcs disjoint: added; implied by every use and by the figure.
2. **The subdivisions** are never defined, and the subdivision lemma is never stated: defined as the
   components of `I − ⋃ arcs`; lemma proved.
3. **Theorem C:** *"This indication of how a ruling may be constructed in the case of this typical
   example is given instead of a tedious formal proof covering all possible cases."* The statement is
   false (tangency); the set `K` of the indication need not exist. No proof is supplied.
4. **Theorem D, unargued steps:** Heine–Borel step — correct (Theorem 12; compactness of `J + I`).
   Condition (2) on `EᵢE′ᵢ` — read as "within every curve of `Ḡ` whose interior contains `Eᵢ`" (the
   regions of `Ḡ` are the interiors of its curves). The construction of `J′` (*"It easily follows
   …"*), the continuation of the arcs of `τ̄` across the annulus, and *"It can be shown in a similar
   way …"* — not supplied; the last is a form of Theorem D itself (item D, point 2). The application
   of Theorem C fails in the tangent case (item D, point 1).
5. **Theorem D's conclusion and its use in Theorem E:** the curve form suffices
   (`m19_theoremD_regions_of_curves`).

## Axioms (Lean)

`#print axioms` for every new theorem (135 of them, including the new
`m19_theoremD_regions_of_curves`): `doc/batches/audits/axioms-batch141.lean` →
`doc/batches/audits/axioms-batch141.txt`. Every one depends only on `propext`, `Classical.choice`,
`Quot.sound` (two helper lemmas on `propext`, `Quot.sound` only; `Space.Quad.Cut.single` on none).
`axioms.txt` regenerated (`lake build HPC`, `lake env lean Axioms.lean > axioms.txt`; 943 lines);
`sorryAx` occurs in no line. Before this batch: `doc/batches/audits/axioms-before-batch141.txt`.

Moore's axioms used by each main theorem (as hypotheses of the statements):

| theorem | Moore's axioms | Lean axioms |
|---|---|---|
| `Space.DoubleRuling.tiling`, `doubleRuling_cell`, `doubleRuling_cells_ncard` | 1, 2, 3, 4, 5, 7, 8 | `propext`, `Classical.choice`, `Quot.sound` |
| `no_ruling_of_two_branches` | 1, 2, 3, 4, 5, 7 | same |
| `tangent_configuration`, `not_m19_theoremC_printed` | 1–8 | same |
| `Space.Quad.splitX`, `Space.Quad.exists_cut` | 1, 2, 3, 4, 5, 7, 8 | same |
| `Space.Quad.Cut.glue` | 1, 2, 3, 4, 5₁, 7 | same |
| `Space.ArcRuling.extendY`, `extendY_finite`, `Space.ArcRuling.refine` | 1–8 | same |
| `Space.ArcRuling.toDoubleRuling` | 1, 2, 3, 4, 5, 7, 8 | same |
| `doubleRuling_pad`, `doubleRuling_refine` | 1–8 | same |
| `m19_theoremD_regions_of_curves` | 1–8 | same |

## Other edits

* `HPC.lean`: `import HPC.Moore.M19CD` at the end.
* `HPC/Moore/FA7.lean`: the batch-139 docstring table marks Theorems 41–43 closed (authorized edit).
* `Axioms.lean`: new group "Moore 1919 C–D (batch 141)"; `axioms.txt` regenerated.
* `README.md`: Part D line for batch 141; batch count 141.
* `LEDGER.md` §6: the subsection above.
* `OPEN.md`: new section for Theorem D (open), with the obstruction.

## Reading plan for batch 142: Theorems E, F, G and the final paragraph (pp. 176–178)

**Prerequisite.** Theorem D is open; Theorem E uses it at every stage. Batch 142 should either close
Theorem D first or take it as a hypothesis (`m19_theoremD_regions_of_curves` already reduces the region
form used in E to the curve form). A proof of D needs a corrected Theorem C. A possible route:
(i) Theorem C for a finite set of pairwise disjoint cross-cuts of `ABCDA` with distinct ends off
`A, B, C, D` (`Good U` := `U` misses the cross-cuts), by induction with the cut-and-glue machinery of
this batch: a cross-cut between opposite sides is cut along; one between adjacent sides (or with both
ends on one side) is first completed, along a piece of itself, to an arc `Y` (or `X`), after which
its remaining pieces join opposite sides of a half — Moore's three chord types; (ii) the case of a
closed curve within `ABCDA` (the nine-cell ruling of Theorem G, Fig. 3); (iii) Theorem D for
two-element open covers, by separating two disjoint closed subsets of `J + I` by such a system of
cross-cuts and curves, and then for any finite cover by induction on its size, with a shrinking of
the cover to keep the closures of the subdivisions covered.

**Theorem E** (p. 176). Two families `α₁` (arcs from `AB` to `CD`) and `α₂` (from `BC` to `DA`) with:
each point of `ABCDA` other than `A, B, C, D` an end of just one arc; through each point within just
one arc of each family; each arc of `α₁` meets each arc of `α₂` in just one point. Proof: fundamental
regions `Gₙ` of subscript `> n` about each point of `J + I`; Theorem D gives `β₁` (subdivisions in
regions of `G₁`); refinement (`doubleRuling_refine`, item E, with `Good` = "within a region of
`Gₙ₊₁`") gives `β₂ ⊇ β₁`, …; `α₂`′s first part is the set of all arcs of all `βₙ` from `BC` to
`DA`; for a point `P` on no such arc, *"it can be proved that there exists through `P`, and with
endpoints on `ABCDA`, just one arc that does not intersect any arc of the set"* — the main unargued
step: the limit arc through `P` (nested strips between consecutive arcs, whose widths go to 0 because
the subdivisions lie in fundamental regions of growing subscript, Axiom 1). Places to check: that the
limit is an arc (and not merely a continuum), uniqueness, and condition (3) at points of `ABCDA` that
are limits of ends.

**Theorem F** (pp. 176–177). A sequence of closed curves `J₁, J₂, …` with `Jₙ₊₁` enclosing `Jₙ` and
every point within one of them. Proof: Theorem 36, Theorem 12, Theorem 42 (now unconditional), and
Theorem 15 for the arc `A′₁A′₂`. Expected to be routine with batches 139–140.

**Theorem G** (pp. 177–178). Two families of open curves `G₁`, `G₂` with just one curve of each
through each point, each curve of `G₁` meeting each curve of `G₂` in just one point. Proof: Fig. 3,
*"`Jₙ₊₁` can be divided by a double ruling, with two arcs parallel to `Bₙ₊₁Cₙ₊₁` … into nine
subdivisions of which the central one is `AₙBₙCₙDₙAₙ (Jₙ)`"* — Theorem C for a curve within
`ABCDA`, unargued; then the open curves `kₘ`, `tₙ` (footnote: F.A. p. 159), the curves `Jₘₙ`,
Theorem E in each, and the concatenation of arcs `gₘₙ` into open curves `l_P`. **The final
paragraph**: the correspondence `P ↦ (x_P, y_P)` with the number plane, *"continuous in the sense
that … `P` is a sequential limit point of `P₁, P₂, …` if, and only if, `lim x_{Pₙ} = x_P` and
`lim y_{Pₙ} = y_P`"*; check that the correspondence is one-to-one and onto, and that "continuous" in
this sense is a homeomorphism (sequential, in a metrizable space).
