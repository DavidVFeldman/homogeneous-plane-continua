Commission read: `doc/batches/COMMISSION-batch142.md` (batch 142 — Part D, Moore VI: Moore 1919, Theorem C corrected; Theorem D).

# Report, batch 142

`lake build HPC` succeeds with `import HPC.Moore.M19CD2` added at the end of `HPC.lean`. The skeleton
is kept verbatim at `doc/batches/skeletons/Moore1919CD2.lean` and the commission at
`doc/batches/COMMISSION-batch142.md` (both moved from the root). The source is
`doc/sources/moore1919.pdf`, pp. 172–176. `HPC/Moore/M19CD2.lean` holds the skeleton's definition and
the three forms of Theorem C; Theorem D is split off into `HPC/Moore/M19DThm.lean`; the docstring of
`M19CD2.lean` maps each skeleton item to its file. The main build carries no `sorry`, and `sorryAx`
occurs in no line of `axioms.txt`.

**Outcome in one line.** Items A.1, A.2, A.3 (the three corrected forms of Theorem C) and item B
(Theorem D) are *proved*; nothing is left open. The region form of Theorem D used in Theorem E is now
unconditional (`m19_theoremD_regions`).

| file | content |
|---|---|
| `HPC/Moore/M19DGlue.lean` | rotation and reflection of rulings (`Space.Rulable.of_rot`, `to_rot`, `of_refl`); gluing good rulings of the two halves of a cut (`Space.Quad.Cut.rulable`) |
| `HPC/Moore/M19DDefs.lean` | chords (`Space.IsChord`) and crossings (`Space.Crosses`); `Space.Rulable.mono`, `Space.Quad.rulable_of_good` |
| `HPC/Moore/M19DPocket.lean` | the two pockets into which a chord divides `I` (`Space.Pocket`, `exists_pocket`) and their nesting |
| `HPC/Moore/M19DOuter.lean` | the outer tile of a family of chords with exclusive pockets; an arc through it (`outer_tile`, `outer_arc`) |
| `HPC/Moore/M19DWeight.lean` | the weight of a chord (opposite sides 1, adjacent sides 2, one side 3); chords of the halves of a cut (`Cut.chord_half`); gluing rulings missing chords (`Cut.glue_chords`) |
| `HPC/Moore/M19DCorner.lean` | gaps between pocket bases (`exists_gap`); pockets at corners |
| `HPC/Moore/M19DChords.lean` | **a ruling missing finitely many disjoint chords** (`chords_rulable`), by induction on the total weight (`opp_step`, `absorb_step`, `chordsBelow`) |
| `HPC/Moore/M19DInside.lean` | access to an open side (`Space.Quad.side_access`); **a ruling missing a closed curve within `ABCDA`** (`inside_rulable`) |
| `HPC/Moore/M19DExtract.lean` | an arc ending at `p` contains no fork at `p` (`Gen.TArc.no_fork`); a crossing excludes touching (`Space.Crosses.no_fork`); pieces of an arc (`Gen.pieces`); **the chords of a closed curve touching `ABCDA` from within nowhere** (`extract_chords`) |
| `HPC/Moore/M19DLens.lean` | a lens crosses `J` at its ends (`crosses_of_lens`); **lenses about each point of `J`** (`lens_data`) |
| `HPC/Moore/M19DNice.lean` | lens families with distinct ends (`lens_family`); a connected compact set between `F` and `V` (`exists_conn_compact`); merging curves (`merge_nice`); **a curve about a compact set crossing `J` at each common point** (`exists_nice_curve`) |
| `HPC/Moore/M19DThm.lean` | the corrected Theorem C in ruling form (`curve_rulable`); Theorem D for a finite cover (`rulable_of_cover`); **`m19_theoremD`** |
| `HPC/Moore/M19CD2.lean` | `Space.IsCrossCut`; `m19_theoremC_crosscuts`, `m19_theoremC_within`, `m19_theoremC_corrected`; `m19_theoremD_regions` |

## Items (commission §2), in order

**A.1 `m19_theoremC_crosscuts`** — *proved* (Axioms 1–8). Statement verbatim. From `chords_rulable`:
a finite set of mutually exclusive chords of `ABCDA` (arcs with ends on `ABCDA` other than
`A, B, C, D` and open part within) admits a ruling none of whose subdivisions meets a chord. The
proof is the route (i) of batch 141 with Moore's three chord types. Induction on the total weight
(a chord joining opposite sides weighs 1, adjacent sides 2, one side 3). A chord joining opposite
sides is an arc of a cut: cut along it, distribute the other chords to the two halves
(`Cut.halves`), rule each half, glue (`Cut.glue_chords`). Otherwise take a chord `t` whose pocket is
maximal, with an end `a` on `AB` after rotating, a point `d` of the open side `CD` on no base of a
maximal pocket (`exists_gap`), and an arc `u` from a point `c` of `t` to `d` through the outer tile
(`outer_arc`). Cut along `x = ac + u`. The rest `cb` of `t` is a chord of one half, of smaller weight
(`absorb_step`).

**A.2 `m19_theoremC_within`** — *proved* (Axioms 1–8). Statement verbatim; the nine-cell form of
Theorem G is **not** stated (see the reading plan below). From `inside_rulable`: an arc `x` from a
point `P` of the open side `AB` to a point `H` of the open side `CD` is assembled from
* an arc `Pa` meeting `h` only in `a` (access to `AB`, then the first point on `h`);
* an arc `ab` of `h`;
* an arc `bH` meeting `h` only in `b` and missing `Pa`. It is drawn in `I − Pa`, which is connected
  by Theorem 33 in the form `hair_isPreconnected`, and `b ≠ a` because `a ∈ Pa`.

The other arc of `h` from `a` to `b` is then a chord of one half of the cut along `x`
(`Cut.chord_half`). That half is ruled by A.1 and the other half meets `h` nowhere. The
subdivisions miss `h`, so each lies within or without `h` (`side_of_disjoint`).

**A.3 `m19_theoremC_corrected`** — *proved* (Axioms 1–8). Statement verbatim: the touch
hypothesis is the skeleton's `hnotouch` (no point of `g ∩ J` is a common end of two arcs of `g`
meeting only there and lying, except for that point, within `ABCDA`). No cleaner equivalent was
needed. `hfin` is still used: it makes the part of `g` within `ABCDA` lie on finitely many chords.
From `curve_rulable`:
* if `g ∩ J = ∅`, `g` lies within `ABCDA` (A.2) or without it (no arc needed);
* otherwise `extract_chords` cuts the two arcs of `g` between two common points at the common points
  (`Gen.pieces`). The pieces within `ABCDA` are chords. Two of them meeting would meet at a common
  end, where `g` would touch `ABCDA` from within, contrary to `hnotouch`.

Then A.1 applies. Touching from without needs no hypothesis (ledger check 1).

**B. `m19_theoremD`** — *proved* (Axioms 1–8). Statement verbatim (in `M19DThm.lean` rather than
`M19CD2.lean`, a split). **The proof replaces Moore's.** The printed sentences replaced are the
whole of the proof after the first one, in particular:
* *"There exists a set of points `E₁, E₂, ⋯ Eₙ₋₁` and arcs `E₁E′₁, ⋯` such that …"* (p. 173) and the
  arc of footnote * (p. 174);
* *"It easily follows that there exist (Fig. 2) (1) on `ABCDA`, `4n` points … (2) within `ABCDA` a
  closed curve `J′` … (3) arcs …"* (p. 174);
* *"By Theorem B there exists a set, `α`, of arcs …"* and *"There exist, on the segments `ĒₙF̄₁, …`
  points `B̄, C̄, D̄`, and `Ā` that are not on `g₁`. The arcs of `α` form a closed curve `ĀB̄C̄D̄Ā` which
  will, at times, be called `J̄`."* (pp. 174–175);
* *"By Theorem C the interior of `ĀB̄C̄D̄Ā` may be divided by a double ruling `τ̄` …"* (p. 175);
* *"If any of them are wholly without `g₁`, then each such subdivision can itself be divided by a
  double ruling … It can be shown in a similar way that there exists a double ruling `τ₃` … This
  process may be continued."* (p. 175).

The first sentence (*"There exists a finite set `Ḡ` of closed curves `g₁, g₂, ⋯ gₘ` …"*) is kept
(Heine–Borel). Route:

1. *Finite cover.* `J + I` is compact, so finitely many curves of `G` cover it.
   `rulable_of_cover` proves, by induction on the number of curves, that every quadrilateral whose
   closure is covered by the interiors of the curves of a finite family has a ruling each of whose
   subdivisions lies within a curve of `G`. Converting rulings by sets of arcs into double rulings is
   batch 141's `Space.ArcRuling.toDoubleRuling`.
2. *Step.* Let `g₁` be one curve, with interior `V`. The part `F` of `J + I` not within the other
   curves is compact and lies in `V`. `exists_nice_curve` gives a closed curve `h` such that
   * its interior `W` contains `F` and `h + W ⊆ V`;
   * `h ∩ J` is finite, misses `A, B, C, D`, and `h` crosses `J` at each common point.
3. *Ruling missing `h`.* A crossing excludes touching from within (`Space.Crosses.no_fork`), so the
   corrected Theorem C (`curve_rulable`) gives a ruling whose subdivisions miss `h`. Each
   subdivision is then within `W ⊆ V` (good) or without `W`. In the second case it is a
   quadrilateral whose closure misses `W ⊇ F`, so it is covered by the other curves, and the
   induction hypothesis rules it. The rulings are combined by `Space.ArcRuling.refine` (batch 141).
4. *The curve `h`* (`exists_nice_curve`).
   * `F` is enlarged to a connected compact `K ⊆ V` (`exists_conn_compact`).
   * Each point `O` of `K ∩ J` has *lenses* (`lens_data`). Theorem 28 with `M = I` gives a pocket of
     `I` at `O`, and with `M = ext I` (in a smaller region) a pocket without `I`; an arc `φ` of `J`
     through `O` lies on both. For any two points `u = φ x`, `v = φ y` there is
     * an arc `t` from `u` to `v` in the inner pocket;
     * an arc `t′` from `u` to `v` in the outer pocket.

     By Theorem 27 the interior of `k = t + t′` contains the open arc `φ(x, y)`, and `k` crosses `J`
     at `u` and `v` (`crosses_of_lens`).
   * Finitely many lenses, with all ends distinct and off `A, B, C, D`, cover `K ∩ J` (compactness,
     then `lens_family`, choosing ends off a finite set).
   * Finitely many curves missing `J` (Theorem 36) cover the rest of `K`.
   * Theorem 42 merges all of them into one curve `h ⊆ ⋃ curves` whose interior contains theirs
     (`merge_nice`). Near a common point of `h` and `J`, `h` lies on one lens only, so `h` crosses
     `J` there.

**Added.** `m19_theoremD_regions` (region form, Axioms 1–8), from `m19_theoremD` and batch 141's
`m19_theoremD_regions_of_curves`.

**Shape changes.**
* `m19_theoremD` lives in `M19DThm.lean` (split), with the same statement.
* No statement of the skeleton was changed.

## Ledger entries (`LEDGER.md` §6, new subsection "Moore 1919, Theorem C corrected; Theorem D (batch 142)")

1. **Theorem C.**
   * Proved with "no touching from within", in the skeleton's form (`m19_theoremC_corrected`).
   * Touching from without is harmless: it is not excluded by the hypothesis.
   * `hfin` is used by the proof; it is not shown to be removable.
2. **The choice of `J̄`.**
   * Moore secures only that `J̄ ∩ g₁` is finite, which does not exclude touching from within, so his
     proof fails at the application of Theorem C.
   * Whether `J̄` could be re-chosen so that `g₁` crosses it is not decided.
   * The proof does not use `J̄`: it builds instead a curve `h` that crosses `ABCDA` at each common
     point (lenses and Theorem 42).
3. **The induction.**
   * The obstruction (subdivision boundaries meeting `g₂` infinitely often) is avoided.
   * The induction is on the number of curves.
   * Each subdivision without `h` gets its own curve about its own uncovered part.
4. **`J′`.** Not needed; neither are the arcs `EᵢE′ᵢ`, the arc of footnote * (`m19_D_arc`) or
   Theorem B.

## Axioms (Lean)

`#print axioms` for every theorem of the batch-142 files (100 theorems):
`doc/batches/audits/axioms-batch142.lean` → `doc/batches/audits/axioms-batch142.txt`. Every one
depends only on `propext`, `Classical.choice`, `Quot.sound`. `axioms.txt` was regenerated (`lake build
HPC`, `lake env lean Axioms.lean > axioms.txt`; 955 lines) and `sorryAx` occurs in no line.

Moore's axioms used by each main theorem (as hypotheses of the statements):

| theorem | Moore's axioms | Lean axioms |
|---|---|---|
| `chords_rulable` | 1–8 | `propext`, `Classical.choice`, `Quot.sound` |
| `inside_rulable` | 1–8 | same |
| `extract_chords` | 1, 2, 3, 4, 5, 7 | same |
| `curve_rulable` | 1–8 | same |
| `crosses_of_lens`, `Space.Crosses.no_fork` | 1 | same |
| `lens_data`, `merge_nice`, `exists_nice_curve` | 1–8 | same |
| `exists_conn_compact` | 1, 2, 3, 4, 5 | same |
| `rulable_of_cover`, `m19_theoremD`, `m19_theoremD_regions` | 1–8 | same |
| `m19_theoremC_crosscuts`, `m19_theoremC_within`, `m19_theoremC_corrected` | 1–8 | same |

## Other edits

* `HPC.lean`: `import HPC.Moore.M19CD2` at the end.
* `HPC/Moore/M19CD.lean`: the commented-out Theorem D is removed and the docstring table points to
  batch 142 (authorized edit).
* `Axioms.lean`: new group "Moore 1919 C corrected, D (batch 142)"; `axioms.txt` regenerated.
* `README.md`: Part D line for batch 142; batch count 142.
* `LEDGER.md` §6: the subsection above.
* `OPEN.md`: the Theorem D entry is closed (section "Closed in batch 142", and a row in *Closed
  items*).
* Uploads moved: `COMMISSION-batch142.md` → `doc/batches/`, `Moore1919CD2.lean` →
  `doc/batches/skeletons/`.

## Reading plan for batch 143: Theorems E, F, G and the final paragraph (pp. 176–178), updated

**Theorem E** (p. 176) now has its prerequisite. Theorem D in the region form Moore uses
(*"By Theorem D the interior of `ABCDA` can be divided by a double ruling `β₁` into subdivisions each
of which is within some region of the set `G₁`"*) is `m19_theoremD_regions`, unconditional. The
successive refinements `β₂ ⊇ β₁, …` are `doubleRuling_refine` (with `Good` = "within a region of
`Gₙ₊₁`"). Better: since the proof of D goes through `Space.Rulable` and `Space.ArcRuling.refine`,
`rulable_of_cover` can be applied directly to each subdivision with the cover `Gₙ₊₁`. The main
unargued step is unchanged: *"it can be proved that there exists through `P`, and with endpoints on
`ABCDA`, just one arc that does not intersect any arc of the set"*, the limit arc through a point on no
arc of any `βₙ`. Places to check:
* the limit of the nested strips is an arc, not merely a continuum;
* uniqueness;
* condition (3) at points of `ABCDA` that are limits of ends.

The tools of this batch that may help:
* `Gen.TArc.no_fork` and the pieces of an arc (`Gen.pieces`) for the order along the limit arc;
* the lens construction for arcs crossing `J`.

**Theorem F** (pp. 176–177). Unchanged: Theorem 36, Theorem 12, Theorem 42 (as used in
`merge_nice`) and Theorem 15. Expected to be routine.

**Theorem G** (pp. 177–178). The nine-cell ruling (*"`Jₙ₊₁` can be divided by a double ruling, with
two arcs parallel to `Bₙ₊₁Cₙ₊₁` … into nine subdivisions of which the central one is
`AₙBₙCₙDₙAₙ (Jₙ)`"*) is **not** given by `m19_theoremC_within`, which only makes each subdivision lie
within or without `Jₙ`. The nine-cell form needs:
* four arcs of `Jₙ₊₁ − (Jₙ + Iₙ)` joining the corners `Aₙ, Bₙ, Cₙ, Dₙ` to the four sides of `Jₙ₊₁`;
* the four sides of `Jₙ` extended by them to two `X`-arcs and two `Y`-arcs of `Jₙ₊₁`.

Suggested route:
* access arcs from the corners (as in `Space.Quad.side_access`), drawn successively in the annulus
  minus the earlier arcs (connected by `hair_isPreconnected`);
* the subdivision lemma (`doubleRuling_cell`) for the count of nine.

Then the open curves `kₘ`, `tₙ`, the curves `Jₘₙ`, Theorem E in each, and the concatenation into the
curves `l_P`. **The final paragraph**: check that the correspondence `P ↦ (x_P, y_P)` is one-to-one
and onto, and that "continuous" in Moore's sequential sense is a homeomorphism.
