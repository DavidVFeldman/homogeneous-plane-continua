Commission read: `doc/batches/COMMISSION-batch143.md` (batch 143 — Part D, Moore VII: Moore 1919, Theorems E and F).

# Report, batch 143

`lake build HPC` succeeds with `import HPC.Moore.M19EF` added at the end of `HPC.lean`. The skeleton
is kept verbatim at `doc/batches/skeletons/Moore1919EF.lean`, and the commission at
`doc/batches/COMMISSION-batch143.md` (both moved from the root). The source is
`doc/sources/moore1919.pdf`, pp. 176–178. `HPC/Moore/M19EF.lean` is the skeleton with its three
`sorry`s replaced by proofs; the three statements are unchanged (no shape changes). The main build
carries no `sorry`. `axioms.txt` (regenerated, 971 lines) has `sorryAx` in no line.

**Outcome in one line.** Item A (Theorem E), item B (the Schoenflies form) and item C (Theorem F) are
*proved*; nothing is left open, and `OPEN.md` is unchanged.

| file | content |
|---|---|
| `HPC/Moore/GridSquare.lean` | pure topology (`HPC.Sq`): families of lines (`Family`: positions in `[0,1]`, two closed sides per line), pre-grids and grids; the position `pos` of a point; **a compact set carrying a grid of vanishing mesh is a closed square, positions going to coordinates** (`Grid.exists_square`) |
| `HPC/Moore/GridMesh.lean` | pure topology: the boxes cut out by consecutive lines of finite subfamilies are disjoint, nonempty and cover the complement of the lines; **counting: if that complement has as many components as there are boxes, each box lies in one component** (`PreGrid.box_sub_component`) |
| `HPC/Moore/M19ESeq.lean` | **the nested double rulings `β₁, β₂, …`** for any sequence of covers by regions (`nested_rulings`) and Moore's instance with fundamental regions (`nested_rulings_fund`) |
| `HPC/Moore/M19ELines.lean` | the two closed sides of a cross-cut from `AB` to `CD`, and its position (the parameter of its end on `AB`) (`Space.Quad.IsLineRec`, `exists_lineRec`, `lr_mono`) |
| `HPC/Moore/M19EFamily.lean` | **the family of lines** of a set of pairwise disjoint cross-cuts, with `DA` and `BC` (`lineFam`) |
| `HPC/Moore/M19EGrid.lean` | a cross-cut meets each of its sides once; **the pre-grid of the two families** (`lfLine_cross`, `preGrid`); positions are injective (`lfT_injective`) |
| `HPC/Moore/M19EMesh.lean` | **the boxes of the sides and the arcs of a ruling lie in subdivisions of the ruling** (`preGrid_box_sub_cell`), by the counting lemma and `doubleRuling_cells_ncard` |
| `HPC/Moore/M19ESchoenflies.lean` | **the Schoenflies form** (`m19_schoenflies_proof`) |
| `HPC/Moore/M19EThm.lean` | Theorem E from a square (`theoremE_of_square`); **Theorem E** (`m19_theoremE_proof`) |
| `HPC/Moore/M19F.lean` | the space is connected (`preconnectedSpace`); **every compact set lies within a closed curve** (`exists_curve_about_compact`); **Theorem F** (`m19_theoremF_proof`) |
| `HPC/Moore/M19EF.lean` | the skeleton: `m19_theoremE`, `m19_schoenflies`, `m19_theoremF` |

## Items

**A. Theorem E** (`m19_theoremE`). *Proved* (Axioms 1–8), in the skeleton's shape, with (3) read
exclusively. Moore's steps 1–3 are formalized as stated (`nested_rulings`; see ledger checks 3 and 4).
Step 4 is replaced: Theorem E is derived from the Schoenflies form (item B). With `f` the embedding of
the square, `α₁` is the set of images of the segments `p.2 = t`, from `f (0, t) ∈ AB` to
`f (1, t) ∈ CD`, and `α₂` the set of images of the segments `p.1 = s`, from `f (s, 1) ∈ BC` to
`f (s, 0) ∈ DA`, for `0 < s, t < 1`. Conditions (1)–(5) are then statements about the square
(`theoremE_of_square`, which uses Axioms 1, 3, 4, 5 only to translate arcs).

So the commission's three questions are settled through the square. The limit arcs are arcs: they are
images of segments under an embedding. They are unique in the sense of (4). (3) and (5) hold, including
at points of `ABCDA` that are limits of ends.

**B. Schoenflies form** (`m19_schoenflies`). *Proved* (Axioms 1–8). The proof is the one the commission
sketched, with the dyadic grid replaced by positions:

1. The `k`-th ruling has its subdivisions in regions inside balls of radius `1/(k+1)`, for a metric
   of the (metrizable) space (`nested_rulings`).
2. All arcs of all rulings, with the sides, form two families of lines in `J + I`. Each line has a
   position, the parameter of its end on `AB` (resp. `BC`), and two closed sides (`lineFam`). They
   form a pre-grid: each line of one family meets each line of the other in one point (`preGrid`).
3. The mesh tends to `0`. For the `k`-th ruling, the boxes cut out by the sides and its arcs number
   `(n+1)(m+1)`; they are nonempty, disjoint and cover `I − ⋃ arcs`, which has `(n+1)(m+1)`
   components. So each box lies in one subdivision (`preGrid_box_sub_cell`).
4. A point `z` is sent to the pair of infima of the positions of the lines having `z` on their lower
   side. On a compact set with a grid of vanishing mesh this map is continuous, injective and onto
   the square (`HPC.Sq.Grid.exists_square`). Its inverse is the embedding.

E was easier to derive from the Schoenflies form than to prove directly, so B was proved first and E
from it. Batch 144 can use either. The form proved has the sides going to the sides but no control of
the boundary parametrization (see the reading plan).

**C. Theorem F** (`m19_theoremF`). *Proved* (Axioms 1–8), in the skeleton's shape `Jₙ ∪ Iₙ ⊆ Iₙ₊₁`.
`Jₙ₊₁` is a closed curve about the compact set `Jₙ + Iₙ + R′ₙ₊₁`, where `Rₙ` are Axiom 1's fundamental
regions, by `exists_curve_about_compact`. That lemma makes the interiors connected before applying
Theorem 42 (ledger check 5). The reading of "encloses" as "lies within" is Moore's: his proof speaks
of a curve that "encloses the interiors of all the curves of the set Gₙ".

## Ledger entries (LEDGER.md §6, "Moore 1919, Theorems E and F; the Schoenflies form (batch 143)")

1. **E (3)**: read exclusively, proved so. No point of a side is an endpoint of arcs of both
   families, not even near the corners. The corners are endpoints of no arc.
2. **E, step 4** (*"it can be proved that there exists through P, and with endpoints on ABCDA, just one
   arc that does not intersect any arc of the set {ᾱ₂}"*): unargued by Moore; replaced by the
   Schoenflies form. The limit arcs are images of segments. Moore's uniqueness among all arcs through
   `P` is not formalized as stated, and is not needed.
3. **E, "This process may be continued"**: supplied by `nested_rulings`, whose step is
   `doubleRuling_refine` (batch 141) with `m19_theoremD_regions` (batch 142).
4. **E, first sentence**: Axiom 1 (1); Theorem D is applied to a set of regions (region form). Moore's
   instance is `nested_rulings_fund`. The Schoenflies proof uses regions in small metric balls instead.
5. **F**: Theorem 12 is needed for the closure `R′ₙ` (compact), and so read it is what is needed.
   Theorem 42 needs the union of the interiors to be connected. Moore omits this, and the gap is
   filled with arcs (Theorem 15) in `exists_curve_about_compact`. "Encloses" = "lies within" is
   confirmed.

## Axioms

From `doc/batches/audits/axioms-batch143.txt`, which lists all 131 theorems of the eleven new files:
every theorem uses `[propext, Classical.choice, Quot.sound]` or a subset of it. In particular:

| theorem | axioms |
|---|---|
| `HPC.Moore.m19_theoremE` | `propext, Classical.choice, Quot.sound` |
| `HPC.Moore.m19_schoenflies` | `propext, Classical.choice, Quot.sound` |
| `HPC.Moore.m19_theoremF` | `propext, Classical.choice, Quot.sound` |
| `HPC.Moore.nested_rulings`, `nested_rulings_fund` | `propext, Classical.choice, Quot.sound` |
| `HPC.Sq.Grid.exists_square`, `HPC.Sq.PreGrid.box_sub_component` | `propext, Classical.choice, Quot.sound` |
| `HPC.Moore.preGrid_box_sub_cell`, `theoremE_of_square`, `exists_curve_about_compact` | `propext, Classical.choice, Quot.sound` |

Of Moore's axioms, all three theorems use Axioms 1–8, as the skeleton's `include` provides. Group
*Moore 1919 E–F (batch 143)* of `Axioms.lean` lists the 16 main names. The previous `axioms.txt` is
kept as `doc/batches/audits/axioms-before-batch143.txt`.

## Reading plan for batch 144: Theorem G, Fig. 3, the open curves, the final paragraph (pp. 177–178)

**What Moore does.**
1. *Theorem G* (*"There exist two sets G₁ and G₂ of open curves such that (1) through each point there
   is just one curve of G₁ and just one curve of G₂, (2) each curve of G₁ has just one point in common
   with each curve of G₂"*), from the curves `Jₙ` of Theorem F.
2. *Fig. 3, the nine-cell ruling*: on `Jₙ₊₁` there are points `Aₙ₊₁, …, Dₙ₊₁` such that `Jₙ₊₁` *"can be
   divided by a double ruling, with two arcs parallel to Bₙ₊₁Cₙ₊₁ and Aₙ₊₁Dₙ₊₁ and the other two
   parallel to Aₙ₊₁Bₙ₊₁ and Cₙ₊₁Dₙ₊₁, into nine subdivisions of which the central one is AₙBₙCₙDₙAₙ
   (Jₙ)"*. This is unargued: it needs four disjoint arcs from `Aₙ, Bₙ, Cₙ, Dₙ` to `Jₙ₊₁` in the annulus,
   extended through `Jₙ`'s sides. It is a candidate ledger entry.
3. *The open curves `kₘ`, `tₙ`* (`-∞ < m, n < ∞`), formed from these ruling arcs across all the
   annuli, with properties (1)–(3) of p. 177 (`kₘ` meets `tₙ` once; `tₙ` separates `tₙ₋₁` from `tₙ₊₁`;
   every point off them lies between consecutive ones). They cut the plane into cells `Jₘₙ`.
4. *`l_P`, `r_P`*: Theorem E in each cell `Jₘₙ`, and the arcs `gₘₙ` chained across cells (*"This process
   may be continued"*, p. 178) into open curves `l_P` through the points `P` of `t₀`, and `r_P` through
   the points of `k₀`.
5. *The final paragraph*: a one-to-one continuous correspondence of `t₀` (and of `k₀`) with the real
   numbers, and the map `P ↦ (x_P, y_P)`, continuous in both directions in the sequential sense.

**Does the Schoenflies form shorten this? Yes, and I recommend it.** Route:
1. **Schoenflies with prescribed boundary.** Strengthen `m19_schoenflies` so that the embedding
   restricts on each side to a given parametrization of that side. Two sides come almost for free:
   the construction already takes parametrizations of `AB` and `BC`, and the positions are dense.
   This still has to be proved, starting from `HPC.Sq.Grid.mem_L_of_pos_eq`. The other two sides
   follow by composing with explicit homeomorphisms of the square fixing two opposite sides
   pointwise, such as `(x, y) ↦ ((1 − y)·g(x) + y·x, y)`.
2. **Fig. 3** as above, but only as four quadrilaterals filling the annulus `Jₙ₊₁ − Iₙ` (the nine-cell
   ruling minus its centre). The splitting lemmas of batches 141–142 (`split_interior`,
   `Space.Quad.Cut`) cut along cross-cuts of an annulus in the same way.
3. **The annulus is a square annulus.** Glue the eight (or four) prescribed-boundary square maps along
   their common sides, choosing compatible parametrizations of the common arcs. Then
   `Jₙ₊₁ ∪ Iₙ₊₁ − Iₙ ≅ [−(n+1), n+1]² − (−n, n)²`, compatible on `Jₙ` with the previous stage.
4. **`S ≅ ℝ²`** by pasting these maps over the locally finite closed cover by annuli
   (`Jₙ ∪ Iₙ ⊆ Iₙ₊₁` and `⋃ Iₙ = S`, Theorem F). This **is** the final paragraph, in topological form.
   Moore's sequential continuity is equivalent, since the space is metrizable.
5. **Theorem G** is then a corollary: the images of horizontal and vertical lines. So are the
   properties of `kₘ`, `tₙ`, `l_P`, `r_P`, if they are wanted as stated.

Moore's route instead needs: open curves as a notion (Foundations, p. 159), the chaining of
infinitely many arcs into an open curve and its homeomorphism with `ℝ`, the "between" relations
(2)–(3) for open curves, and a separate continuity argument. Each is a substantial new piece of
infrastructure with no reuse elsewhere. The Schoenflies route reuses the grid machinery of this batch
and the cutting lemmas of batches 141–142. **Recommendation:** Schoenflies route, with Theorem G and
Moore's open curves derived as corollaries. The nine-cell ruling of Fig. 3 and the "This process may
be continued" of p. 178 should still be checked and recorded in the ledger as printed.
