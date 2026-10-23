Commission read: `doc/batches/COMMISSION-batch139.md` (batch 139 — Part D, Moore III: F.A. §7, Theorems 35–43).

# Report, batch 139

`lake build HPC` succeeds with `import HPC.Moore.FA7` added at the end of `HPC.lean`. The skeleton is
kept verbatim at `doc/batches/skeletons/MooreFA7.lean` (byte-identical to the upload; the commission
is at `doc/batches/COMMISSION-batch139.md`). The source is `doc/sources/moore1916.pdf`, pp. 150–157.
`HPC/Moore/FA7.lean` is an umbrella module importing the files below. Its docstring has a table
mapping each skeleton item to its file. The three open statements are recorded at its end as comments
(not in the build, not `sorry`). The main build carries no `sorry`.

| file | content |
|---|---|
| `HPC/Moore/Sec7A.lean` | `jordan` (structure of `J`, its interior `I`, its exterior `S − I'`), `component_eq`, `access`; Theorems 35 (+ refutation), 39, 40; footnote p. 152 |
| `HPC/Moore/Sec7B.lean` | Theorem 36, `fa_theorem36_interior_subset` |
| `HPC/Moore/Sec7Chord.lean` | chords of a closed curve: `param_chords_finite`, `exists_maximal_chord` |
| `HPC/Moore/Sec7Th37.lean` | Theorem 37 |
| `HPC/Moore/Sec7Th38.lean` | Theorem 38 (shape chosen), `param_chords_accumulate`, `two_arcs_eq` |
| `HPC/Moore/Sec7Th41.lean` | Theorem 41: Case I and the first sub-case of Case II |
| `HPC/Moore/Sec7Th42.lean` | `isSCC_eq_of_subset`, Theorem 43 as printed refuted, Theorem 42 from Theorem 41 |

## Items (skeleton §2), in order

Every statement carries only the axioms its proof uses. The skeleton's section assumes Axioms 1–8;
**that change of shape applies to every item and is not repeated below.** All names are in
`HPC.Moore`.

1. **Theorem 35** — *proved* with `hne : R.Nonempty` (`fa_theorem35`; as in the skeleton).
   *Printed form refuted* (`not_fa_theorem35_printed`): in batch 137's `withEmpty` space, which
   satisfies Axioms 1–8, the region `∅` contains no closed curve. **Moore's proof replaced:** an arc
   in `R` (Theorem 16) and, about one of its interior points, the closed curve of batch 138's
   `th31_pocket` (the construction of Theorem 31), which lies in `R`.
2. **Theorem 36** — *proved* by Moore's proof (`fa_theorem36`), with one step corrected: *"Then `BE`
   (on `BD`) + `EC` (on `DC`) is an arc `BC` every point of which, except `C`, is in `R`"* is not
   right as printed, because the region `R̄` about `C` need not lie in `R`. The arc is cut at its
   first point outside `R` (a boundary point of `R`), and that point plays the part of `C`.
3. **`fa_theorem36_interior_subset`** — *proved*: Theorem 36 with the interior inside `R`
   (Theorem 21). This is not part of the printed statement.
4. **Footnote, p. 152** — *proved* (`fa_arcs_of_scc_meet`).
5. **Theorem 37** — *proved*, in the skeleton's shape (`fa_theorem37`). Moore's two steps (check 4)
   are replaced by a finiteness argument (`param_chords_finite`, `exists_maximal_chord`).
6. **Theorem 38** — *proved* (`fa_theorem38`). **Shape chosen** (the skeleton had `True`), modelled on
   Theorem 37:
   * **"`A₁XA₂OA₁`"**: the closed curve `X ∪ T`, where `T` is the arc of `J` from `A₁` to `A₂`
     through `O`. There is exactly one such arc, since `O ≠ A₁, A₂`. Its interior `W` lies in the
     exterior of `J` (`hWE`).
   * **Added hypothesis `hXE`**: the open arc `A₁XA₂` is without `J`. Theorem 41's use assumes it
     (*"an interval `A_pXB_p` of `J₁` lying entirely without `J₂` except for its endpoints"*), and
     conclusion (2) states it for `O₁YO₂`.
   * **(1)**: `O₁`, `O₂` lie on the arc `T'` of `J` from `A₁` to `A₂` not through `O`. The interval
     `O₁OO₂` is the arc `V` of `J` from `O₁` to `O₂` through `O`, with `T ⊆ V`. *"`O` is between
     `O₁` and `A₂`"* is stated as: every arc of `V` from `O₁` to `A₂` contains `O`, and likewise for
     `O₂`, `A₁`.
   * **(2)**: an arc `Y ⊆ C` from `O₁` to `O₂`, with open part without `J`; the interior of `Y ∪ V`
     is without `J`.
   * **(3)**, as printed: `B₁`, `B₂` lie on the arc `V'` of `J` from `O₁` to `O₂` *not* containing
     `O`. So `O₁YO₂` is the *outermost* such arc of `C`, which is the reading Theorem 41 uses. The
     conclusion is **`{B₁, B₂} = {O₁, O₂}`**, because the statement does not say which of `B₁`, `B₂`
     is nearer `O₁`.
7. **Theorem 39** — *proved* (`fa_theorem39`). **Moore's argument replaced** (check 5). The point
   lies in the interior or in the exterior of `J`. `access`, which is batch 138's `accessible`
   applied to an arc of `J` ending at `O`, joins it to `O` inside that set.
8. **Theorem 40** — *proved* (`fa_theorem40`). No proof is printed. Supplied: by `access`, a point of
   the interior (of the exterior) is joined to `A` and to `B`, and the union of the two arcs
   contains an arc from `A` to `B` (`exists_arc_through`).
9. **Theorem 41** — **open in Case II.** The following parts are *proved*:
   * Case I (`J₁ ∩ J₂` has at most one point): `fa_theorem41_caseI_nested` (`I₁ ⊆ I₂` or
     `I₂ ⊆ I₁`) and `fa_theorem41_caseI`;
   * the first sub-case of Case II, *"If every point of `J₁` is within or on `J₂` then `J` is `J₂`"*:
     `fa_theorem41_of_subset`.

   The remaining case is `J₁ ∩ J₂` with at least two points, each curve having a point without the
   other. Moore ends it with *"It may be proved that `J` is a closed curve satisfying the
   requirements of Theorem 41"*. **Obstruction** (`OPEN.md`): Moore's `J` can consist of infinitely
   many arcs `t_P`. Proving that it is a closed curve needs a limit construction: replace a null
   family of intervals `k_P` of `J₂` by the arcs `t_P`, show the result is continuous and injective,
   and give a side argument for every pocket. None of this is in F.A., and it was not carried out.
   The statement is commented out at the end of `FA7.lean`.
10. **Theorem 42** — *proved from Theorem 41* (`fa_theorem42_of_41`, with Theorem 41 as the
    hypothesis `Th41 σ`). The unconditional form is **open** because it needs Theorem 41; it is
    commented out at the end of `FA7.lean`. The commission's question, *"check that connectedness of
    the union gives an ordering in which each new interior meets the previous union"*, is answered
    yes. If the curves already absorbed formed a proper subfamily `H` and no remaining interior met
    their union, the union of all interiors would split into two disjoint nonempty open sets.
11. **Theorem 43** — *printed form refuted* (`not_fa_theorem43_printed`, check 7). The corrected form,
    with **`G` nonempty** (`hGne`), is **open**. **Obstruction** (`OPEN.md`): no proof is printed.
    `J₂`, and similarly `J₁`, needs the statement dual to Theorem 41 for intersections of interiors.
    That statement is of the same kind as Theorem 41 Case II and is not in F.A. The corrected
    statement is commented out at the end of `FA7.lean`.

**Optional follow-up on Theorem 32 (`C ∉ AB` instead of `Disjoint R K`): not done.** The form with
`C ∉ AB` needs more than `accessible`. It must show that the component of `H − AB` containing `C`
has a point of `AB` beyond `A₁` as a limit point. When parts of `AB` enter `R`, that is a statement
that an arc ending on the boundary of a Jordan domain does not separate it from `D`. It also needs
the printed hypothesis that `A₁X₁B₁` meets `AB` only in `A₁`, `B₁`, which batch 138 dropped as
unused. Batch 139 uses only `accessible`, never `fa_theorem32` itself: Theorems 39 and 40 go through
`access`. So the form with `Disjoint R K` is the only one used so far.

## Ledger entries (`LEDGER.md` §6, new subsection "Moore 1916, F.A., §7, Theorems 35–43 (batch 139)")

* **Refuted as printed:** Theorem 35 for `R = ∅` (`not_fa_theorem35_printed`; it does not follow from
  Axioms 1–8). Theorem 43 for `G = ∅` (`not_fa_theorem43_printed`; false in every space satisfying
  Axioms 1–8).
* **Check 1**: Theorem 35 is refuted for `∅`, and Moore's proof is replaced.
* **Check 2**: Theorem 36 is proved, with the step *"… is an arc `BC` every point of which, except
  `C`, is in `R`"* corrected. The interior lies in `R`, which is not printed
  (`fa_theorem36_interior_subset`).
* **Check 3**: the footnote is proved.
* **Check 4**: the Theorem-29 monotonicity step and the limit points `L₁`, `L₂` are both replaced by
  the finiteness of chords.
* **Check 5**: all seven sentences of the proof of Theorem 39 are covered by `access` (quoted in the
  ledger).
* **Check 6**: Case I of Theorem 41 is supplied, as is the sub-case *"If every point of `J₁` is within
  or on `J₂`…"*. Case II, *"It may be proved that `J` is a closed curve …"*, is open.
* **Check 7**: Theorem 43 is refuted for `G = ∅`. The corrected form is open.
* **Check 8**: degenerate cases are listed per theorem. The ones that matter:
  * Theorem 38's added `hXE` and its set-valued (3);
  * Theorem 40's `A ≠ B`;
  * Theorem 42's `G` nonempty;
  * Theorem 43's `G = ∅`.

## Axioms (Lean)

* **Lean axioms.** All 28 new theorems use only `propext`, `Classical.choice`, `Quot.sound`
  (`doc/batches/audits/axioms-batch139.txt`, from `axioms-batch139.lean`).
* **`axioms.txt`.** Regenerated: 901 lines (882 before; the old file is kept as
  `doc/batches/audits/axioms-before-batch139.txt`), with `sorryAx` in none. The new group in
  `Axioms.lean` is "Moore F.A. §7 (batch 139)".

**Moore's axioms used, per theorem:**

| theorem | Moore's axioms |
|---|---|
| `jordan`, `component_eq` | 1, 2, 3, 4, 5₁, 7 |
| `access`, `exists_arc_through` | 1–8 |
| Theorem 35 (`fa_theorem35`) | 1–8 |
| `not_fa_theorem35_printed` | 1–8 (hypotheses on `σ`; the conclusion is about `withEmpty`) |
| Theorem 36, `fa_theorem36_interior_subset` | 1–8 |
| footnote (`fa_arcs_of_scc_meet`) | 1, 3, 4, 5₁ |
| `exists_maximal_chord` | 1, 3, 4, 5₁ |
| Theorem 37 | 1, 3, 4, 5₁ |
| Theorem 38 | 1, 2, 3, 4, 5, 7, 8 |
| Theorem 39, Theorem 40 | 1–8 |
| `two_meets_of_in_out` | 1, 2, 3, 4, 5₁, 7 |
| Theorem 41 Case I (`fa_theorem41_caseI_nested`, `fa_theorem41_caseI`) | 1, 2, 3, 4, 5, 7 |
| Theorem 41, first sub-case of Case II (`fa_theorem41_of_subset`) | 1, 3, 4, 5, 7 |
| `isSCC_eq_of_subset` | 1, 3, 4, 5₁ |
| Theorem 42 from 41 (`fa_theorem42_of_41`) | 1, 2, 3, 4, 5₁, 7 + Theorem 41 |
| `not_fa_theorem43_printed` | 1–8 |

Axiom 6 enters only through batch 138's `accessible` and `th31_pocket`, and so through Theorems 35,
36, 39 and 40.

## Other edits

* `HPC.lean`: `import HPC.Moore.FA7` added at the end.
* `Axioms.lean`, `axioms.txt`: the new group, as above.
* `README.md`: a Part D line for Moore III, `HPC/Moore` now §§2–7, and the batch count set to 139.
* `LEDGER.md` §6: the new subsection.
* `OPEN.md`: a section for the three open statements (Theorem 41 Case II, Theorem 42, corrected
  Theorem 43), with their obstructions.

## What batch 140 (Moore 1919) needs from F.A.

**Caveat.** Moore 1919 (*Concerning a set of postulates for plane analysis situs*) is **not** in
`doc/sources/`. The citation list below is therefore the commission's list, matched against F.A.;
the 1919 text itself was not read. Please upload it with the batch-140 commission.

| 1919 cites | F.A. content there | status in the repository |
|---|---|---|
| p. 132 | definitions (limit point, boundary, `M'`, exterior, connected, Heine–Borel) and Axioms 1–7 | batch 137 (`HPC/Moore/Defs.lean`, `Basic.lean`, …) |
| p. 133 | Axiom 8, the footnote "5₁" (at least three points), Theorems 1–5 | batch 137 (Theorem 4 as printed refuted; `axiom5₁_of_axiom5`) |
| p. 139 | Theorem 16; Lennes's arc facts (two sub-arcs, intervals, betweenness, first and last points); definition of a simple closed curve | batch 137 (`fa_theorem16`, `isArc_iff`, `fa_sec5_*`, `fa_scc_two_arcs`) |
| p. 149 | the special proof of Theorems 33/34 (boundary a closed curve: *"The arc `ADE` divides `R` into two regions …"*, Theorems 25, 32) | Theorems 33, 34 proved in batch 138 by Kline's general proof; the special proof is not formalized. Theorem 25 is proved. |
| pp. 152–153 | Theorem 37, its footnote, and Theorem 38 | proved (this batch) |
| p. 159 | Theorem 48 (the Lennes/Schoenflies-type characterization of the closed curve), the definition of open curve, and the start of Theorem 49 | **not formalized** |
| Theorem 12 | a closed bounded set has the Heine–Borel property | batch 137 (`fa_theorem12`) |
| Theorem 15 | arcs in domains (by nested simple chains) | batch 137 (`fa_theorem15`) |
| Theorem 36 | closed curve in `R` about `O` | proved (this batch), with the interior in `R` (`fa_theorem36_interior_subset`) |
| Theorem 37 | | proved (this batch) |
| Theorem 40 | arcs inside and outside a closed curve | proved (this batch) |
| Theorem 42 | the union of interiors | **conditional** on Theorem 41 (`fa_theorem42_of_41`); Theorem 41 Case II open |
| Theorem 43 | | printed form refuted; corrected form (`G ≠ ∅`) **open** |

**Beyond Theorem 43.** The commission lists p. 159 among the citations. On that page F.A. defines
open curves and states Theorem 48 and the beginning of Theorem 49. So batch 140 probably needs:
* at least the definition of open curve;
* very likely Theorems 49–51:
  * Theorem 49: a segment of an open curve plus its ends is an arc;
  * Theorem 50: every ray contains a set with no limit point;
  * Theorem 51: an open curve separates `S` into two connected sets.

This is likely because a "number plane" proof builds coordinate lines, which are open curves.

What their F.A. proofs use:
* Theorem 49: Theorem 5 and a closed curve about a point. It is "bounded" via a closed curve
  `J` enclosing `X`.
* Theorem 50: Heine–Borel.
* Theorem 51: Theorems 16, 34 and 40, all of which are proved.

None of them uses Theorems 41–43. Whether Theorem 48 is needed cannot be settled without the 1919
text. The commission says it is not needed for 139.

**Blocking for batch 140.** If Moore 1919 uses Theorems 42 or 43, it inherits the open Case II of
Theorem 41 (and, for 43, the dual statement for intersections). These are the items to settle first,
either by finishing the limit construction or by checking whether 1919 only uses configurations with
finitely many pockets (for instance curves built from finitely many arcs of a grid). In that case
the finiteness lemmas of this batch (`param_chords_finite`) may give Theorem 41 for such curves
directly.
