# Commission: batch 105 — housekeeping after Theorem 11

**Go!** Runs on top of the batch-104 delivery. One file accompanies this commission:
`COMMISSION-batch105.md` (this text, also pasted into the prompt). No skeleton. Nothing is to be
proved, weakened or re-proved; the test is that `axioms.txt` agrees before and after on every
declaration present in both, and that the new lines are the ones listed here.

The report names the commission read in its first line.

## 0. On batch 104

Audited: Theorem 11 proved, no refutations; the Fugate 1969 ledger recorded (the `R ⊄ K` gap in
Lemma 3 closed by Sorgenfrey). This batch brings the pruned tree up to date.

## 1. Edits

1. **`HPC/Plane/Layers51.lean`.** Delete the three `-- OPEN` declarations
   `isContPt_congr`, `subcontinuum_of_isContPt`, `theorem11_1951_of_T10'` (the first two were
   steps of a route that batch 97 closed; the third is superseded by `theorem11_1951`). Leave a
   one-line pointer each; keep Fort's theorem (`isMeagre_not_isContPt`) and
   `exists_contPt_not_endElt`, which are proved and stand on their own. Update the module
   docstring in one sentence.
2. **`HPC/Plane/Theorem11.lean`.** `theorem11_1951_of_T10` and `theorem11_1951_iff_of_T10` stay
   (batch 103's decision); add to their docstrings one sentence: "Superseded by
   `theorem11_1951` / `theorem11_1951_iff` (`Theorem11B.lean`), which need neither hypothesis."
3. **`Axioms.lean`.** Add, in the Duke group, `theorem11_1951`, `theorem11_1951_iff`,
   `exists_terminal_point_of_isTerminalSub`, `isTerminalSub_of_union_terminal`,
   `claim1_contains_inter`, `epsCoverable_of_halves`; remove the three deleted names from the
   *Open targets* group. Regenerate `axioms.txt`. Expected: 229 lines; `sorryAx` in exactly 9
   lines (`theorem3_end`, `covering_step`, `theorem14`, `exists_tame_chain_near`, `fugate_cor1`,
   and the four consequences).
4. **`OPEN.md`.** Remove the three entries; the remaining five stay as written.
5. **`README.md`.** Add Fugate 1969 (Lemma 3, Lemma 4, Theorem 2 Case II) to the list of sources
   and one line to the summary: Bing's Duke Theorem 11 is proved by Fugate's Case II argument.
   `LEDGER.md`: add a §4 "Fugate 1969" with the eleven items of REPORT-batch104.md's ledger, and
   under Bing Duke Theorem 11 the final form of the entry (the three unargued sentences; which
   two are supplied by Fugate's Claims 1–2 and Lemma 4; that the "uncountable `G'`" sentence does
   no work; that Theorem 10 is not needed).
6. `doc/batches/`: file `COMMISSION-batch104.md`, `REPORT-batch104.md`, `Axioms104.lean`,
   `axioms-batch104.txt` where the pruning pass put their predecessors.

## 2. Deliverables

The edited tree; `axioms.txt`; the report with the before/after comparison and the final counts.
