Commission read: `doc/batches/COMMISSION-batch140.md` (batch 140 — Part D, Moore IV: F.A. Theorems 41–43 completed; Moore 1919, Theorems A and B).

# Report, batch 140

`lake build HPC` succeeds with `import HPC.Moore.M19AB` added at the end of `HPC.lean`. The skeleton
is kept verbatim at `doc/batches/skeletons/Moore1919AB.lean`; the source is
`doc/sources/moore1919.pdf` (pp. 170–174), with `doc/sources/moore1916.pdf` (F.A., pp. 155–156).
`HPC/Moore/M19AB.lean` is an umbrella module importing the files below; its docstring has a table
mapping each skeleton item to its file. **Everything commissioned is proved; nothing is refuted;
nothing is left open.** The main build carries no `sorry`, and `sorryAx` occurs in no line of
`axioms.txt`.

| file | content |
|---|---|
| `HPC/Moore/M19Defs.lean` | `Space.IsSegmentOf`, `Space.ShareSegment` (verbatim from the skeleton) |
| `HPC/Moore/M19A.lean` | the crossing lemma `Gen.crossing`; Theorem A |
| `HPC/Moore/M19Bstep.lean` | `Gen.TArc.tail_in_open`; the step of Theorem B (`m19_B_step`) |
| `HPC/Moore/M19B.lean` | "properly joined" (`Gen.PJ`), `loc_arc`, `seg_nhds`; Theorem B |
| `HPC/Moore/M19D.lean` | Theorem 33 for any connected open set (`hair_isPreconnected`); the arc of footnote * of p. 174 (`m19_D_arc`) |
| `HPC/Moore/M41Replace.lean` | replacement of a null family of arcs (`Gen.arc_replace`, `Gen.finite_long_intervals`) |
| `HPC/Moore/M41Geom.lean` | unbounded components, chords of a closed curve, `chords_null` (from Theorem A) |
| `HPC/Moore/M41Side.lean` | `chord_side`, `pocket` (Theorem 27 for each pocket) |
| `HPC/Moore/M41Half.lean` | `half_replace`: the replacement along half of `J₂` |
| `HPC/Moore/M41.lean` | Theorem 41 Case II, Theorem 41 in full, Theorem 42 |
| `HPC/Moore/M43Pocket.lean`, `M43Dual.lean`, `M43Comp.lean` | pockets inside a curve, `adjacent_piece`, `dual_component` |
| `HPC/Moore/M43.lean` | `dual_step` (intersection analogue of Theorem 41), `iterate_inner`, Theorem 43 corrected |

## Items (commission §2), in order

Every statement carries only the axioms its proof uses. The skeleton's section assumes Axioms 1–8;
**that change of shape applies to every item and is not repeated below.** All names are in
`HPC.Moore`.

**A. F.A. Theorem 41, Case II — *proved*** (`fa_theorem41_caseII`; hence `fa_theorem41` in full, by
cases with batch 139's `fa_theorem41_caseI` and `fa_theorem41_of_subset`). Statement as in the
skeleton. The commission's route is followed, with the curve located first: `V`, a component of
`S − (I₁' + I₂')` with non-compact closure; `J₂` split at two points `O`, `O'` of `J₂` without `J₁`
that are limit points of `V`; on each half, the arcs `k_P` of `J₂` cut off by chords `t_P` of `J₁`
lying in `V'` replaced by those chords. The chords form a null family by Theorem A of 1919
(`chords_null`), their parameter intervals are disjoint by Theorem 27 (`pocket`), and the replacement
map is continuous and injective (`Gen.arc_replace`), so `J` is a closed curve; it is the boundary of
`V`, and so its interior contains `I₁ + I₂` (`curve_of_frontier_subset`). Theorem 38 is not used.
See ledger check 4.

**A′. F.A. Theorem 42 — *proved*** (`fa_theorem42`), statement as in the skeleton, from batch 139's
`fa_theorem42_of_41` and `fa_theorem41`.

**B. F.A. Theorem 43, corrected (`G` nonempty) — *proved*** (`fa_theorem43`). Statement as in the
skeleton (which already carries `hGne`). Moore gives no proof. Supplied: `dual_step`, the
intersection analogue of Theorem 41 (if `O` is a point of the closed curve `J` within the closed curve
`J'`, and `U` is the interior of `J`, or its exterior provided `I ⊄ I'`, there is a closed curve
through `O` on `J + J'` whose interior lies in `U ∩ I'`), proved by the pocket-replacement method of
item A (`chord_pockets`, `adjacent_piece`, `dual_component`); then `iterate_inner` iterates it over
the finite set `G`. `J₂` comes from iterating from `J` itself; `J₁` from iterating from the curve
given by `dual_step` on the exterior side of `J` for one curve of `G` (the hypothesis `¬ I ⊆ I_p`
is used there; `G ≠ ∅` provides that curve).

Since Theorem 43 is proved, the fallback statements were not needed for it, but both are proved
anyway, each **without** Theorem 43 (shorter proofs, and in the form 1919 uses):
* `m19_B_step` — the arc of Theorem B (p. 172), statement as in the skeleton.
* `m19_D_arc` — the arc of footnote * of p. 174 (Theorem D), **shape chosen**: `J` (interior `I`),
  `g` (interior `I_g`) closed curves; `K` an interval `A₁B₁` of `J` whose segment lies within `g`;
  `E₁` on that segment; `β = E₁E′₁` an arc within `g` lying, except for `E₁`, within `J`. Conclusion:
  an arc `γ` from `A₁` to `E′₁` with `γ − A₁` within `g` and within `J`, and `γ ∩ β = {E′₁}`. The
  "curve `ABTNA` of p. 149" of Moore's footnote is replaced by `hair_isPreconnected` (Kline's proof of
  Theorem 33, valid for any connected open set).

**C. Moore 1919, Theorem A — *proved*** (`m19_theoremA`; Axioms 1, 3, 4, 5₁). Moore's printed proof:
limit points `A ∈ M`, `B ∈ N` of a subsequence; four points in the order `ECADFB`; of three late
arcs two share the interval `CE` or `DF`. The last step is `Gen.crossing` (every connected subset of
`L` meeting small neighbourhoods of `A` and `B` contains one of two fixed nondegenerate arcs).
**Shape change:** the skeleton's `Function.Injective f` is dropped (the statement is stronger; a
repeated nondegenerate arc shares a segment with itself, and the proof uses three distinct indices).
The reading of "no two arcs of `G` have a segment in common" by `ShareSegment` is checked (ledger,
check 3).

**D. Moore 1919, Theorem B — *proved*** (`m19_theoremB`), statement as in the skeleton, following
Moore's proof with his unargued steps supplied (ledger check 2). One change of argument: the finiteness
of `A₁, A₂, …` is obtained from compactness (finitely many classes of properly joined points, each
open), not from Theorem A; Theorem A does apply, as Moore says (ledger check 3). Footnote ‡ (the
example `y = x sin(1/x)`, p. 170) is set in the ordinary plane: **recorded, not formalized**.

## Ledger entries (`LEDGER.md` §6, new subsection "Moore 1916, F.A., Theorems 41–43, and Moore 1919, Theorems A and B (batch 140)")

1. Footnote †, p. 170, *"… and have `A` and `B` as endpoints"*: misprint for `X`, `Y`; confirmed.
2. Theorem B's five unargued steps (*"it is clear that there exists a point `A₁` …"*, *"By an
   argument similar to the above proof of the non-existence of `X` …"*, *"It is clear that `O` is
   either `Aₘ` or `Bₘ`"*, *"It is easy to see, with the aid of Theorems 43 and 40 …"*, *"In view of
   these considerations it is clear that the point-set `τ` contains …"*): each supplied (`seg_nhds`
   and closedness; `Gen.PJ` with `loc_arc`; the termination of the construction gives `O = Bₘ`;
   `m19_B_step`; `Gen.TArc.join`).
3. Theorem B's use of Theorem A: applies, with `M = J` and `N` the interval `A₁O` of `AB` (closed,
   disjoint because `AB` meets `J` only in `A`, `B`). The Lean proof uses compactness instead.
   `ShareSegment` reading: checked.
4. Theorem 41 Case II, *"It may be proved that `J` is a closed curve satisfying the requirements of
   Theorem 41"*: supplied by the boundary of an unbounded component `V` and the replacement of a null
   family of arcs (Theorem A for nullity, Theorem 27 for disjointness).

No new refutation. Further entries: Theorems 42, 43 proved; `m19_D_arc` proved; footnote ‡
recorded; degenerate cases.

## Axioms (Lean)

`#print axioms` for all 49 new theorems: `doc/batches/audits/axioms-batch140.lean` →
`doc/batches/audits/axioms-batch140.txt`. Every one depends only on `propext`, `Classical.choice`,
`Quot.sound`. `axioms.txt` regenerated (`lake build HPC`,
`lake env lean Axioms.lean > axioms.txt`); `sorryAx` occurs in no line. Before this batch:
`doc/batches/audits/axioms-before-batch140.txt`.

Moore's axioms used by each theorem (as hypotheses of the statements):

| theorem | Moore's axioms | Lean axioms |
|---|---|---|
| `m19_theoremA` | 1, 3, 4, 5₁ | `propext`, `Classical.choice`, `Quot.sound` |
| `chords_null` | 1, 3, 4, 5₁ | same |
| `fa_theorem41_caseII`, `fa_theorem41`, `fa_theorem42` | 1–8 | same |
| `dual_step`, `iterate_inner`, `fa_theorem43` | 1–8 | same |
| `m19_B_step`, `m19_theoremB` | 1–8 | same |
| `hair_isPreconnected`, `m19_D_arc` | 1–8 | same |

## Other edits

* `HPC.lean`: `import HPC.Moore.M19AB` at the end.
* `HPC/Moore/FA7.lean`: the commented-out open statements of Theorems 41–43 at its end deleted (now
  proved); nothing else changed. Its docstring table (the batch-139 record, which
  still says "open" for Theorems 41–43) is left as it is, since the commission allows only the
  deletion; the current status is the table of `HPC/Moore/M19AB.lean`.
* `Axioms.lean`: new group "Moore F.A. 41–43, 1919 A–B (batch 140)" after "Moore F.A. §7 (batch 139)";
  the batch-139 comment "Case II open (OPEN.md)" updated to point to it. `axioms.txt` regenerated.
* `README.md`: Part D line for batch 140; batch count 140.
* `LEDGER.md` §6: the subsection above.
* `OPEN.md`: the batch-139 section (Theorems 41, 42, 43) removed; the three items added to the table
  of closed items. Nothing new is open.

## Reading plan for batch 141: Theorems C and D (pp. 172–176)

**The double ruling (footnote *, p. 172).** On the closed curve `ABCDA` points
`X₁ … Xₙ` on `AB`, `Y₁ … Yₙ` on `BC`, `X′ₙ … X′₁` on `CD`, `Y′ₙ … Y′₁` on `DA` (in the order
`AX₁…XₙBY₁…YₙCX′ₙ…X′₁DY′ₙ…Y′₁A`), and arcs `XᵢX′ᵢ`, `YⱼY′ⱼ` lying, except for their ends, within
`ABCDA`, with `XᵢX′ᵢ ∩ YⱼY′ⱼ` a single point and `XᵢX′ᵢ ∩ XⱼX′ⱼ = ∅` (`i ≠ j`; the text is damaged
in the scan, presumably also `YᵢY′ᵢ ∩ YⱼY′ⱼ = ∅`, to be checked against the page image). "Parallel"
is a name only. Footnote † of p. 172: the *sides* are the segments `AB, BC, CD, DA`; "the interval
`AB`" is the one not containing `C`. Needed for formalization: the definition as a structure
(two finite families of arcs indexed by `Fin n`, `Fin n'` — the printed footnote uses `n` for both;
check whether the two rulings must have the same number of arcs), and the *subdivisions*: the
`(n+1)(n'+1)` regions cut out — each the interior of a closed curve made of four arcs. That the
subdivisions are interiors of closed curves (Theorem 41/42-type arguments, `fa_theorem34`) is the
first lemma batch 141 needs; Moore never states it.

**Theorem C (p. 172).** If the closed curve `g` meets `ABCDA` in finitely many points, none of `A,
B, C, D`, the interior of `ABCDA` can be divided by a double ruling into subdivisions each wholly
within or wholly without `g`. Only an *"Indication of proof"*: a finite set `K` of arcs of `g`
(chords of `ABCDA`) covers `g ∩ I`; each chord is of type (1) both ends on one side, (2) ends on
adjacent sides, or (3) ends on opposite sides; one example (Fig. 1, four chords of type 1, two of type
2, one of type 3) *"is given instead of a tedious formal proof covering all possible cases"*.
Batch 141 must write the proof. Suggested route: induction on the number of chords, each new chord
cut by the existing ruling into finitely many pieces (Theorem B of this batch keeps intersections
finite); or, avoiding cases, first rule so that every chord meets each ruling arc finitely often and
then refine. The finiteness of `K` follows from `g ∩ ABCDA` finite (each chord has ends there, and
two chords with the same ends are the two arcs of `g`).

**Theorem D (pp. 173–176).** If every point on or within `ABCDA` is within some curve of a set `G`,
the interior can be divided by a double ruling into subdivisions each within some curve of `G`. The
proof: a finite subcover `g₁ … gₘ`; segments `AᵢBᵢ` of `AB` covering it, each within a curve
`ḡᵢ`; points `Eᵢ` and arcs `EᵢE′ᵢ` into `J`; the arcs `A₁E′₁, E′₁E′₂, …` (**footnote * of p. 174:
`m19_D_arc`, proved here**); then (Fig. 2) an inner curve `J′` with `4n` points and arcs between
`J′` and `J` splitting the annulus into pieces each within a curve of `G`; **Theorem B** (proved here)
for arcs `a` meeting `g₁` finitely; **Theorem C** for the curve `Ā B̄ C̄ D̄` and `g₁`; extension of the
rulings across the annulus; then *"This process may be continued"* over `g₂, …, gₘ` (an induction to
be written, each step refining the ruling inside the subdivisions without `g₁ … gₖ`). Points to check
in batch 141: the order `A₁A₂B₁A₃B₂ …` of the covering segments (a chain cover of the interval `AB`;
Lebesgue-number argument); the five conditions on `EᵢE′ᵢ` (condition (2) speaks of *regions* of `G`:
compare with the hypothesis, which speaks of curves); the existence of `J′` (*"It easily follows"*,
Fig. 2 — the main unargued step); and the refinement step (extension of a ruling of a subdivision to a
ruling of the whole, *"The arcs of these rulings may be extended"*).
