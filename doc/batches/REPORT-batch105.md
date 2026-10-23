Commission read: `COMMISSION-batch105.md` — batch 105, housekeeping after Theorem 11.

# Report, batch 105

Nothing was proved, refuted, weakened or re-proved. Three open declarations that Theorem 11 had made
obsolete were deleted. The audit was extended by six batch-104 theorems, and the documentation was
brought up to date. `lake build HPC` succeeds (8285 jobs). It reports exactly five
`declaration uses sorry` warnings: `theorem3_end`, `covering_step`, `theorem14`,
`exists_tame_chain_near` and `fugate_cor1`. The audit agrees before and after on all 223
declarations present in both (§3).

## 1. Edits (commission §1)

1. **`HPC/Plane/Layers51.lean`.** The three `-- OPEN` declarations `isContPt_congr`,
   `subcontinuum_of_isContPt` and `theorem11_1951_of_T10'` were deleted, each leaving a one-line
   pointer comment. Fort's theorem (`isMeagre_not_isContPt`), `exists_contPt_not_endElt`, the
   definition `IsContPt` and the Cantor-organ refutations are untouched. In the module docstring,
   the **Open** bullet was replaced by one sentence saying that the three statements were removed
   in batch 105, once Theorem 11 was proved without them. The file now has no `sorry`.
   No other file referred to the three names in Lean code.
2. **`HPC/Plane/Theorem11.lean`.** The sentence "Superseded by `theorem11_1951` /
   `theorem11_1951_iff` (`Theorem11B.lean`), which need neither hypothesis." was added to the
   docstrings of `theorem11_1951_of_T10` and `theorem11_1951_iff_of_T10`. Statements and proofs are
   unchanged.
3. **`Axioms.lean`.** These were added to the Duke group, right after the two `_of_T10` lines:
   `theorem11_1951`, `theorem11_1951_iff`, `exists_terminal_point_of_isTerminalSub`,
   `isTerminalSub_of_union_terminal`, `claim1_contains_inter` and `epsCoverable_of_halves`, each
   commented with its place in Fugate 1969. The three deleted names were removed from *Open
   targets*. `axioms.txt` was regenerated with `lake env lean Axioms.lean > axioms.txt`.
4. **`OPEN.md`.** Entries 5–7 were removed. The other four stay as written, and the Fugate 1966
   entry is unchanged apart from its number, which went from 8 to 5 so that the list stays
   consecutive.
5. **`README.md`.** Fugate 1969 (Lemma 3, Lemma 4, Theorem 2 Case II) was added to the sources,
   and the line "Bing's Duke Theorem 11 is proved by Fugate's Case II argument" to the summary.
   The batch count in the layout table now reads 105. The `doc/sources/` row now also names
   Fugate 1969.
   **`LEDGER.md`.**
   * A new §4 "Fugate 1969" gives the eleven items of REPORT-batch104.md's ledger, each with the
     Lean name where there is one.
   * §4 also gives the final form of the Bing Duke Theorem 11 entry:
     * the three unargued sentences: the "uncountable `G'`" sentence; "`p'` satisfies condition A
       for `M` equal to either `H` or `K`"; and the separation of `S − N`;
     * the separation is supplied by Fugate's Claims 1–2, and the point by Lemma 4's terminal
       point `μ` of both halves;
     * the "uncountable `G'`" sentence does no work: one non-end element is enough, and it need
       not be degenerate;
     * Theorem 10 is not needed, because Fugate 1966's Lemma 1 takes its place.
   * A row in the Duke table points to this entry. The introduction now mentions §4.
6. **Filing.**
   * `COMMISSION-batch104.md` and `REPORT-batch104.md` were already in `doc/batches/`.
   * `Axioms104.lean` and `axioms-batch104.txt` moved to `doc/batches/audits/`, where their
     predecessors are.
   * This commission moved to `doc/batches/COMMISSION-batch105.md`.
   * The pre-edit audit was kept as `doc/batches/audits/axioms-before-batch105.txt`.
   * Not asked for, but filed the same way:
     * the uploaded notes `theorems-3-4-scheduling(11).md` (through §121) replace the older copy
       `doc/theorems-3-4-scheduling.md` (through §118);
     * the Fugate 1969 PDF is now `doc/sources/fugate-1969-a-characterization-of-chainable-continua.pdf`.
       PDFs are git-ignored, so this file travels with the tree but not with the git history.

One stale reference was left in place, because the commission asks for no further Lean edits: the
module docstring of `HPC/Plane/Theorem11B.lean` (line 8) still calls `theorem11_1951` the
sorry-free form of "`theorem11_1951_of_T10'` in `Layers51.lean`", and that declaration is now
deleted.

## 2. Final counts

* `axioms.txt`: **229 lines** (226 before, minus 3, plus 6).
* `sorryAx` occurs in exactly **9 lines**:
  * the five open targets: `HPC.Fold.theorem3_end`, `HPC.Description.covering_step`,
    `HPC.Description.theorem14`, `HPC.Plane.exists_tame_chain_near`, `HPC.Plane.fugate_cor1`;
  * the four consequences: `HPC.Description.theorem15`,
    `HPC.Description.exists_description_covering`, `HPC.Plane.dense_pseudoArcs`,
    `HPC.Plane.theorem2_HIC`.
* `sorry` warnings in `lake build HPC`: 5 (before: 8).
* `OPEN.md`: 5 entries (before: 8).

## 3. Before/after comparison

Before: `doc/batches/audits/axioms-before-batch105.txt` (226 lines). After: `axioms.txt` (229
lines). Comparison by declaration name:

* **Present in both: 223 declarations, all 223 lines identical.**
* Removed (3), each `[propext, sorryAx, Classical.choice, Quot.sound]` before:
  `HPC.Plane.isContPt_congr`, `HPC.Plane.subcontinuum_of_isContPt`,
  `HPC.Plane.theorem11_1951_of_T10'`.
* Added (6), each `[propext, Classical.choice, Quot.sound]`:
  `HPC.Plane.theorem11_1951`, `HPC.Plane.theorem11_1951_iff`,
  `HPC.Plane.exists_terminal_point_of_isTerminalSub`, `HPC.Plane.isTerminalSub_of_union_terminal`,
  `HPC.Plane.claim1_contains_inter`, `HPC.Plane.epsCoverable_of_halves`.

These are exactly the lines the commission lists.
