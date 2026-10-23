Commission read: COMMISSION-batch123.md (batch 123 — closing `theorem3_end`; Bing's Theorem 4 in his two-link form; the only-clauses; the ledger for Theorem 3).

# Report, batch 123

**Outcome.**

| item | verdict |
|---|---|
| 1. close `theorem3_end`; `theorem3_bing` | **proved** (`sorry` removed; `sorryAx` now in exactly one line of `axioms.txt`, `fugate_cor1`) |
| 2. `theorem4_two`, `theorem4_of_two` | **proved**, with one change of shape: `theorem4_two` needs `r < s ∨ k ≠ 3`; without it the statement is **refuted** (`theorem4_two_degenerate_false`) |
| 3. the only-clauses | **open, with the obstruction stated** (no counterexample in the model census); `Theorem4Literal` as recorded in the skeleton is **refuted** in the degenerate case `m = 3`, `r = s` (`not_theorem4Literal`), for a reason unrelated to the only-clauses |
| 4. ledger, OPEN, README | done |

Everything builds with `lake build HPC`. The new theorems use only `propext`, `Classical.choice`
and `Quot.sound` (`doc/batches/audits/axioms-batch123.{lean,txt}`); no `native_decide`, no new
`sorry`. The two `sorry`s of the skeleton are replaced by proofs.

## 1. `theorem3_end` closed; `theorem3_bing`

* New file `HPC/Fold/Theorem3Bing.lean`, importing `Recon122General` and `T9Ends` (the chain
  library), not `Theorem4`. It receives, verbatim and under their old names, `chainRho`,
  `chainSig`, `chainT`, `bHyp_of_crooked`, `chain_of_bconcl`, `Theorem3Block` and
  `theorem3Block_holds` (all `HPC.Fold.Recon122.*`), so nothing downstream changes. Two lemmas of
  `Recon121` that the transfer uses (`link_subset_of_between`, `meets_of_forced`) sit above
  `Theorem4` in the import graph; they are copied as `private` lemmas.
* `HPC.Fold.theorem3_bing`: Theorem 3 as printed without the only-clause, as a theorem about
  chains with explicit arguments (the unfolding of `Theorem3Block`); `theorem3Block_holds` is now
  `fun … => theorem3_bing …`.
* `HPC.Fold.theorem3_end_of_bing`: the statement of `theorem3_end` from `theorem3_bing` (the proof
  of `theorem3EndStmt_of_block`, specialised).
* `HPC/Fold/Theorem4.lean` imports `Theorem3Bing`; `theorem3_end` keeps its statement verbatim, its
  proof is `theorem3_end_of_bing hk hcr i`, the `-- OPEN` marker is removed and the docstring gains
  the line "Proved in batch 123 from `Theorem3Bing` (`theorem3_end_of_bing`)" (plus the remark that
  `hn` is not used, as for `theorem4`; the linter reports `hn` unused, the statement being
  verbatim).
* `HPC/Fold/Recon122.lean`: the moved declarations are deleted there (same names, now from
  `Theorem3Bing`); `theorem3EndStmt_holds` and `theorem3_end'` are now aliases of
  `HPC.Fold.theorem3_end`. `theorem3Strong_holds`, `theorem3Block_of_strong`,
  `theorem3EndStmt_of_block`, `theorem3EndStmt_of_strong` are unchanged.
* `Axioms.lean`: `theorem3_end` moved from "Open targets" to the Bing 1948 group (with
  `theorem3_bing`, `theorem3_end_of_bing`). `axioms.txt` regenerated: `sorryAx` occurs in exactly
  one line, `HPC.Plane.fugate_cor1`. Previous version: `doc/batches/audits/axioms-before-batch123.txt`.

## 2. Theorem 4, two-link form

Files: `HPC/Fold/Theorem4TwoModel.lean` (the model), `HPC/Fold/Theorem4Two.lean` (the skeleton,
saved there; `import HPC.Fold.Theorem4Two` added at the end of `HPC.lean`).

**Change of shape (recorded in the file).** `theorem4_two` has the extra hypothesis
`hdeg : r < s ∨ k ≠ 3`. It is necessary: `theorem4_two_degenerate_false` gives three intervals of
`ℝ` crooked (vacuously, `k = 3`) in three intervals, the middle fine link meeting the first and the
last coarse link; with `r = s` = that link, `(β r).val = 0 = q − 1` forces `q = 1`, and the union of
`E` lies in no two adjacent links of `D`. For `k ≤ 2` and for `k ≥ 4` the hypothesis is automatic
(for `k ≥ 4` no link meets both end links). `theorem4_of_two` keeps the commissioned statement minus
the unused `hn`, and is derived from `theorem4_two` (in the degenerate case directly: one block,
three links of `D` are all of `D`).

**The proof.** In the model (`TwoConcl n ρ σ r s`: `β r = 0`, `β s` maximal, Lipschitz, fibres in
two adjacent levels), transferred by `chain_of_twoConcl` (surjectivity of the block map by the
discrete intermediate value theorem between `r` and `s`).

* `seg3`: Theorem 3 (`bing_main`) on a segment `p … q` of the fine chain with any basepoint, in
  absolute indices, with Bing's end clause at both ends of the segment (from `BHyp.sub` and
  `BConcl.sub_abs` of batch 122 with the full coarse range).
* `two_core` (`K ≥ 5`, `r ≤ h < k ≤ s`, `d_h` meets `e₁`, `d_k` meets `e_m`): `H = seg3` on
  `D(1, h)` with `d_r` first, `G = seg3` on `D(k, n)` with `d_s` first;
  `F t = H t` if `t ≤ h` and `H t < a := H h`; `F t = a + (K − 3) + (b − G t)` if `t ≥ k` and
  `G t < b := G k`; otherwise `a + genG t` (the bottom-anchored level groups of batch 122:
  "in `e₁ + e₂`", "in `e₃` not `e₂`", …, "in `e_{m−1} + e_m`"). Then `F r = 0`,
  `F s = a + K − 3 + b` is the maximum, and every fibre is in two adjacent levels.
* `two_small` (`K ≤ 4`), Bing's "easily established": every link lies in `e₁ + e₂` (`ρ ≤ 1`) or in
  `e_{m−1} + e_m` (`σ ≥ K − 2`). If `d_r` is low and `d_s` high (or conversely), two blocks: the low
  links other than `d_s`, and the rest. If both are high (`ρ ≥ 2`), three blocks split at the link
  meeting `e₁` (which is low and lies strictly between `r` and `s`): high links before it, low
  links, high links after it; symmetrically if both are low.
* `two_model`: `h ≠ k` for `K ≥ 4`; the case `k < h` by mirroring the coarse chain (`BHyp.flip`).

**What Bing's half page needed beyond the text** (ledger notes for Theorem 4):

1. *The degenerate case.* `r = s` with `m = 3` makes the statement false (above); Bing's
   "Since the case of our theorem where m ≤ 4 is easily established" hides it. Outside it the case
   `m ≤ 4` is indeed easy (`two_small`), but it needs its own grouping (Bing's level groups fail at
   `m = 4`: a link in `e₂ ∩ e₃` may lie in the block `g_v` of `d_k` and also belongs to the group
   "in `e₁ + e₂`").
2. *The level groups read bottom-anchored* (`genG`: "in `e₁ + e₂`" first, "in `e_{m−1} + e_m`"
   last, the rest by least level). With this reading they are consecutive and every value between
   the two seams is attained — not because each group is nonempty (they need not be: nonemptiness
   is not needed), but because `F` moves by at most one and runs from `F r = 0` to the maximum
   `F s`, so the block map is surjective by the discrete intermediate value theorem.
3. *The two seams.* The commission's expectation holds and is what the proof uses: a link of
   `H(1, u − 1)` adjacent to `D′` has `H = u − 1` and its neighbour `H = u`, i.e. the neighbour is in
   `h_u ⊆ e₁ + e₂` (from the end clause of Theorem 3 at `d_h`; the alternative
   `h_u ⊆ e_{m−1} + e_m` is impossible because `d_h` meets `e₁` and `m ≥ 5`), so it is in the bottom
   group; likewise at `g_{v−1}`, whose neighbours in `D′` lie in `g_v ⊆ e_{m−1} + e_m`, hence (as
   `m ≥ 5`) not in `e₂` and in the top group. A link of `H(1, u − 1)` is never adjacent to a link of
   `G(v − 1, 1)` (`h < k`).
4. *The case `h > k`* by reversal of the coarse chain (Bing: "for convenience, suppose that
   `h < k`").
5. *`r = s` or `h = k`.* For `m ≥ 4` both are impossible: a link meeting `e₁` lies in `e₁ ∪ e₂`
   (`σ ≤ 1`), a link meeting `e_m` in `e_{m−1} ∪ e_m` (`ρ ≥ m − 2 ≥ 2`). For `m = 3`, `h = k` is
   allowed when `r < s` (`two_small` does not use `h ≠ k`), and `r = s` is the counterexample. If
   `u = 1` (`d_r` in the block of `d_h`) or `v = 1`, the corresponding part of `F` is empty; this needs
   no separate treatment.
6. *Bing's "Let D(h, k) be a subchain of D(r, s)"*: any `h, k` in `[r, s]` with `d_h` meeting `e₁`
   and `d_k` meeting `e_m` work; no minimality is needed.

## 3. The only-clauses — open, with the obstruction

**Verdict: (c) open.** No counterexample, no proof.

*What is proved.*

* `onlyIn_of_not_covered`: the clause holds at `i` unless `E.link i` is covered by its two
  neighbours (with `link_subset_neighbours` of batch 121).
* `onlyIn_of_neighbour`: the clause holds at `i` as soon as one neighbour of `i` is in the block of
  `i`. (A link outside its block can only be covered by its neighbours in that block; with one
  neighbour in its own block, a point common to `E.link i` and that neighbour would lie in the other
  neighbour, two links apart.)
* So the only-clause of Theorem 3 at a covered interior basepoint `i` is equivalent to: *some
  consolidation as in `theorem3_bing` has `i` and a neighbour of `i` in its first block.*
* `Theorem4Literal` (the skeleton's `Prop`) is refuted, but only through the degenerate case of
  item 2 (`not_theorem4Literal`); `Theorem4LiteralND` (with `r < s ∨ k ≠ 3`) is recorded as the
  open `Prop` for Theorem 4 as printed.

*The obstruction.* What is needed is a **pair form of Theorem 3** (`Theorem3Pair`): two adjacent
links lying in a common link of `D`, both in the first block. It would give the only-clause for a
covered link sharing a coarse link with a neighbour; a covered link sharing a coarse link with
neither neighbour (levels `a, a + 1, a + 2` in a row) needs an argument of its own. Bing's
induction does not give the pair form directly, and the obvious reduction — merge the pair into one
fine link and apply Theorem 3 — fails: the merged sequence need not be crooked (scratch census:
6 848 of 448 028 pair instances at `n = 6`, `K = 5` lose crookedness, e.g. `ρσ = (0,0), (0,0), (1,1),
(1,2), (1,1), (2,2)` merging links 2, 3). Also, the moves "drop `i` into its neighbours' block"
(which does not change any union, because `E.link i` is covered) only help when the first block is
`{i}` alone.

*The census* (`doc/census/recon-batch123-only.py`, logs `recon-batch123-*.log`; Python, not
Lean-checked). Model of batch 122 with the meeting table as data; a covered interior link `i` is
modelled by `T(i) ⊆ T(i−1) ∪ T(i+1)` and by the containment that the covering forces in chains
(every coarse link containing both neighbours contains link `i`).

| mode | (n, K) | instances | failures |
|---|---|---|---|
| only-clause at covered `i` | (5,4), (6,4), (7,4) | 29 777; 220 468; 1 530 295 | 0 |
| | (6,5), (7,5), (7,6) | 330 720; 2 319 522; 3 108 749 | 0 |
| pair form | (6,4), (6,5), (7,5), (7,6) | 298 449; 448 028; 3 017 612; 4 045 322 | 0 |
| only-clause **without** the containment constraint | (5,4), (6,4) | 34 411; 255 952 | 24; 132 |

The last line shows that the containment constraint matters: without it the model has
"counterexamples" (first: `ρσ = (0,0), (1,1), (2,2), (1,1), (2,2)`, `i = 3`), but they need link 3
outside `e₂` although both its neighbours lie in `e₂`, which a covered link cannot do. With the
constraint, nothing fails. Pair instances whose two links share no coarse link do fail
(e.g. `(1,1), (2,2)`), which is why `Theorem3Pair` asks for a common coarse link.

OPEN.md gets item 2 (the only-clauses, an open statement recorded as `Prop`s, no `sorry`).

## 4. Ledger, OPEN, README

* `LEDGER.md` §1: the batch-121 row "Theorem 3, Bing's proof, special case" is replaced by the row
  asked for (statement proved, `theorem3_bing`; the proof as written fails, certificate
  `seam_every_H_fails`; the three repairs `cbotG`, `special_five`, `special_middle`). The row on the
  respective reading is unchanged. New row: "Theorem 4 as printed, degenerate case `m = 3`, `r = s`"
  (`not_theorem4Literal`, `theorem4_two_degenerate_false`). There is no row "Theorem 3 as printed
  (the only-clause)": item 3 did not refute it.
* `OPEN.md`: item 1 (`theorem3_end`) closed and moved to the Closed-items table (with
  `theorem3_bing`, batch 123); `fugate_cor1` renumbered 1; item 2 the only-clauses.
* `README.md`: the Bing 1948 entry as asked (Theorem 3 `theorem3_bing`, only-clause open; Theorem 4
  `theorem4_two` and `theorem4`, plus the degenerate case); batch count 123; the sentence about
  `theorem3_end`'s `sorry` removed. The line on `OPEN.md` now says "the only `sorry` of the main
  build, and open statements recorded as `Prop`s".

## 5. Deliverables and housekeeping

* `axioms.txt` regenerated (468 lines): `sorryAx` in **one** line (`HPC.Plane.fugate_cor1`). Per-batch audit
  `doc/batches/audits/axioms-batch123.{lean,txt}` (23 declarations, all standard axioms).
  `Axioms.lean`: Bing 1948 group gains `theorem3_bing`, `theorem3_end`, `theorem3_end_of_bing`,
  `theorem4_two`, `theorem4_of_two`, `not_theorem4Literal`; Refutations gains
  `theorem4_two_degenerate_false`, `not_theorem4Literal`; new group "Batch 123"; `theorem3_end`
  removed from "Open targets".
* Uploaded notes moved to `doc/theorems-3-4-scheduling.md` (replacing the previous version); the
  commission filed as `doc/batches/COMMISSION-batch123.md`; the uploaded skeleton kept as
  `doc/batches/skeletons/Theorem4Two.lean`; no stray copies at the root.
* `doc/census/README.md` is not in the list of files to edit and was not edited; the new census
  files are `doc/census/recon-batch123-only.py` and `recon-batch123-{only,pair,nocontain}.log`.
* Not attempted: `fugate_cor1`, `treeLike_nonseparating`, `PlaneFacts`.
