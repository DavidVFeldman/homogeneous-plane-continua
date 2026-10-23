Commission read: COMMISSION-batch121.md (batch 121 — reconnaissance on `theorem3_end` and on Bing's Theorem 3 as printed).

# Report, batch 121

**Outcome.**

* **One reading is refuted.** Bing's Theorem 3, with the end clause read *respectively* (`Theorem3Literal`, the reading of Q1(a)), is false at `k = 3`: `HPC.Fold.Recon121.not_theorem3Literal`.
* **Bing's own wording is open.** His wording is "… meets `e₁` or `e_m` … is a subset of `e₁ + e₂` or `e_{m−1} + e_m`" (`Theorem3LiteralOr`). It is not refuted, because it differs from the respective reading only at `k = 3`, where it follows from the main clause. Theorem 3 as printed is therefore **open**.
* **`theorem3_end` is open.** No counterexample was found, including in the census under the reading that covers general chains (Q2).
* **Bing's proof is incomplete as written.** The special case, executed literally, fails. A Lean certificate is `seam_every_H_fails` together with `seamD_special`, `seamD_hk` and `seamIH_H0` (Q4).

**Audit.** Every theorem of the batch depends only on `[propext, Classical.choice, Quot.sound]` (50 theorems, `doc/batches/audits/axioms-batch121.txt`). No `native_decide` was used: the finite checks are `decide` or `decide +kernel`. `axioms.txt` was regenerated (436 declarations, up from 413). `sorryAx` still occurs in exactly two declarations, `theorem3_end` and `fugate_cor1`. The previous version is kept as `doc/batches/audits/axioms-before-batch121.txt`.

**Files.**

* **New Lean file.** `HPC/Fold/Recon121.lean`, imported on the last line of `HPC.lean`. Open statements are `def … : Prop`, and there is no new `sorry`.
* **Edited files.**
  * `Axioms.lean`: new group "Reconnaissance, batch 121", 23 entries.
  * `axioms.txt`: regenerated.
  * `LEDGER.md` §1: two rows in "Bing 1948 and its skeletons", because a refutation was found.
* **`OPEN.md`: not edited.** The status of item 1 (`theorem3_end`, open) did not change.
* **`doc/census/README.md`: not edited.** The new census files are listed below, so they can be added to it if wanted.
* **New census files.**
  * Programs: `doc/census/census-batch121.c` (uses `census-batch87-common.h`, unchanged) and `doc/census/seam-batch121.py`.
  * Logs: `doc/census/census-batch121-{k3,k4a,k4b,k5a,k5b,bing56,bing7,bing7-big}.log` and `doc/census/seam-batch121.log`.
* **Housekeeping.** The uploaded notes file was moved to `doc/theorems-3-4-scheduling.md`, as usual, and the commission was filed as `doc/batches/COMMISSION-batch121.md`.

## Q1 — Bing's statement in Lean

**(a) The definitions.** All of them are in the block reading of `HPC.Fold.Theorem4`. Bing's `D` is our fine `E`, Bing's `E` is our coarse `D`, and "a subset of the sum of `w` adjacent links" is `⊆ D.unionRange j w`.

| `def` | content |
|---|---|
| `Theorem3Literal` | The respective reading asked for in Q1(a). Its clauses: `β i = 0`; the only-clause `∀ v ≠ β i, ¬ E.link i ⊆ (E.ofBlocks β).link v`; every block in `D.unionRange j 2`; an end link meeting `D.link 0` has its block in `D.unionRange 0 2`, and one meeting `D.link (k−1)` has its block in `D.unionRange (k−2) 2`. |
| `Theorem3LiteralOr` | The same, with Bing's own "or … or" end clause: an end link meeting `D.link 0` **or** `D.link (k−1)` has its block in `D.unionRange 0 2` **or** in `D.unionRange (k−2) 2`. |
| `Theorem3EndTwo` | The three-link main clause (`theorem3`) with the two-link respective end clause (Q1(b)). |
| `Theorem3EndStmt` | The statement of `theorem3_end`, verbatim. |
| `Theorem3Stmt` | The statement of `theorem3`, verbatim. |

**The respective reading is false (`not_theorem3Literal : ¬ Theorem3Literal.{0}`).**

* **The example.** `k3Chain` consists of five open rectangles in `ℝ × ℝ`, crooked in three vertical strips. Crookedness is vacuous for `k = 3`.
  * The end links `0` and `4` lie in the middle strip and reach into both outer strips.
  * Links `1` and `3` lie in the outer strips `0` and `2` respectively.
* **Why no block map works.** The respective clause puts the block of each end link inside `D_0 ∪ D_1` and inside `D_1 ∪ D_2`, hence inside `D_1`. So that block contains neither link `1` nor link `3`. Links `1` and `3` cannot share a two-link block either. From basepoint `2` no block map satisfies all four separations.
* **Bing's wording survives.** `endClause_or_iff` shows that for `k ≥ 4` the two end clauses are equivalent: `D.unionRange 0 2` and `D.unionRange (k−2) 2` are then disjoint, and a link cannot meet `D_0` and `D_{k−1}` at once. For `k = 3` Bing's clause follows from the main clause, since every two-link block lies in `D_0 ∪ D_1` or in `D_1 ∪ D_2`. So the respective reading is refuted *only* where the two readings differ, and Bing's statement as printed is not refuted.
* **The meeting is unforced.** `k3_unforced_meeting` shows that the end link `0` meets the last strip although neither it nor its neighbour lies in that strip. This is exactly the gap of Q2.

**The only-clause.** It is **not automatic** for chains in general, but it is automatic for the realized chains of the faithful model.

* `link_subset_neighbours`: if a link is covered by a block it does not belong to, it is covered by its neighbours in that block.
* `only_clause_not_automatic`: the chain `(0, 1), (0, 2), (3/2, 3)` in `ℝ` with `β = id`. The first link lies inside the second block. Chains allow a link inside a neighbour, since links are not required to be connected or to stick out.
* `linkChain_only` (via `only_of_linkRect`): in every realized chain the point of link `t` at height `t + 3/4` lies in no other link, so the clause holds for every block map. The census therefore needs no separate check for it.

**(c) The implications** (all proved):

```
theorem3EndTwo_of_literal     : Theorem3Literal   → Theorem3EndTwo
theorem3EndStmt_of_endTwo     : Theorem3EndTwo    → Theorem3EndStmt
theorem3Stmt_of_endStmt       : Theorem3EndStmt   → Theorem3Stmt
theorem3Stmt_holds            : Theorem3Stmt                     (= theorem3)
theorem3LiteralOr_of_literal  : Theorem3Literal   → Theorem3LiteralOr
theorem3EndStmt_of_literalOr  : Theorem3LiteralOr → Theorem3EndStmt
```

* **The chain asked for.** `Theorem3Literal → Theorem3EndTwo → theorem3_end`-statement `→ theorem3`-statement.
* **Bing's statement as printed also implies `theorem3_end`.** The proof of `theorem3EndStmt_of_literalOr` goes through `endClause_or_iff` for `k ≥ 4`. For `k = 3`, `D.unionRange 0 3` is all of `D`.
* **The first link of the chain is false.** `Theorem3Literal` is refuted, so `Theorem3LiteralOr` is the right hypothesis to keep.

## Q2 — Does the model census bear on general chains?

**Yes, after one correction. The batch-86/87 census under-covered; the corrected census over-covers, and its verdict transfers to all chains by a Lean theorem.**

**(b) The general-chain class projects exactly onto the faithful model** (`exists_chain_iff_isCrookedIvF`). A pair `(ρ, σ)` with values in `[0, M)` is the `(minIdx, maxIdx)` pair of some chain crooked in some `M`-link chain, in some metric space, iff `IsCrookedIvF ρ σ` holds.

* One direction is `isCrookedIvF_minIdx_maxIdx`; the other is `realization`, whose rectangles have only forced meetings.
* So unforced meetings impose **no** constraint on `(ρ, σ)` beyond `IsCrookedIvF`. Their only effect is to add instances of the hypothesis of the end clause. The general-chain class is not smaller than the model, so the forced-table census **under-covers**.
* `k3_unforced_meeting` shows such an instance in a crooked chain.

**(a) The reduction.** Read the end-clause hypothesis through the *possible* meeting table: an end link `t` may meet `D_0` iff `σ t ≤ 1`, and may meet `D_{k−1}` iff `ρ t ≥ k − 2`.

* **It contains every real meeting** (`maxIdx_le_one_of_meets_first`, `le_minIdx_of_meets_last`): a link inside `D_{σ t}` meets `D_0` only if `D_{σ t}` does.
* **It contains every forced meeting** (`meets_of_forced`).
* The model statement with this table is `ModelEndP ρ σ K w i`.
* **`chain_of_modelEndP`.** If the `(minIdx, maxIdx)` pair of a chain satisfies `ModelEndP` at width `w`, the chain has a block consolidation with basepoint `i` first, blocks in `w` adjacent links, and the width-`w` end clause read with the *true* meetings.
* **`theorem3_end_of_model`.** `(∀ faithful (ρ, σ), K ≥ 3, ∀ i, ModelEndP ρ σ K 3 i) → Theorem3EndStmt`. This is the theorem asked for.

So the census class `T3ENDP` decides, on a finite corpus, exactly the hypothesis of `theorem3_end_of_model`. A failure of `T3ENDP` would *not* by itself refute `theorem3_end`, because the meetings it assumes may not be realizable together with crookedness. That is why the census also has the `M` classes (forced meetings plus every admissible set of extra meetings, see Q3).

## Q3 — The two-link forms, census

**Program.** `doc/census/census-batch121.c`, with the enumerator and Bing chains of batch 87 (`census-batch87-common.h`). The search is an exact DFS over block maps with the basepoint at time `0`. On hitting its node limit it is retried once with the other arm swept first; if that also hits the limit, the instance is "undecided".

**Classes.** Each class is decided at every basepoint.

| class | block width | end clause | meetings | meaning |
|---|---|---|---|---|
| `T3END` | 3 | width 3 | forced | batch 87's class, re-run as a cross-check |
| `T3ENDP` | 3 | width 3 | possible | Q2: the hypothesis of `theorem3_end_of_model` |
| `S2` | 2 | none | — | Q3(a): Bing's main clause |
| `LIT` | 2 | width 2 | forced | Q3(b): `Theorem3Literal` on realized chains (the only-clause is automatic there) |
| `LITP` | 2 | width 2 | possible | sufficient for `Theorem3Literal` minus the only-clause, on all chains |
| `T3E2` / `T3E2P` | 3 | width 2 | forced / possible | `Theorem3EndTwo` |
| `LITM` | 2 | width 2 | forced + `S`, for every admissible `S` | see below |
| `T3ENDM` | 3 | width 3 | forced + `S`, for every admissible `S` | see below |

**Admissible sets `S`.** An admissible `S` is a set of extra end-link meetings with the extreme levels, each possible and unforced, such that the sequence stays crooked under the 1948 clause with the enlarged meeting table. These are the meeting hypotheses a general chain with the given `(minIdx, maxIdx)` can present, up to realizability of `S`. "fails with `K ≥ 4`" counts instances whose subchain spans at least four levels; at `K = 3` the two-link end clauses are the respective reading refuted in Q1.

### Results

**Enumerated corpus.** All crooked sequences in the faithful model of length `n` over `K` levels, at every basepoint.

| range | sequences | instances (`M` classes) | `T3END` | `T3ENDP` | `S2` | `LIT` | `LITP` | `T3E2` | `T3E2P` | `LITM` | `T3ENDM` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `K = 3`, `n = 3 … 12` | 6 218 016 | 72 363 432 (143 301 848) | 0 | 0 | 0 | 0 | **1 744** (all `K = 3`) | 0 | 0 | **1 744** (all `K = 3`) | 0 |
| `K = 4`, `n = 6 … 10` | 95 808 | 936 960 (1 015 040) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `K = 4`, `n = 11` | 379 584 | 4 175 424 (4 698 144) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `K = 4`, `n = 12` | 1 754 176 | 21 050 112 (24 425 856) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `K = 4`, `n = 13` | 7 811 008 | 101 543 104 (121 253 600) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `K = 5`, `n = 13` | 512 | 6 656 (6 656) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `K = 5`, `n = 14` | 10 752 | 150 528 (150 528) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `K = 5`, `n = 15` | 129 536 | 1 943 040 (1 958 400) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `K = 5`, `n = 16` (six shards) | 1 174 016 | 18 784 256 (19 161 088) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

* **Undecided.** None in the enumerated corpus.
* **`K = 3` failures.** The `K = 3` failures of `LITP`/`LITM` (2, 4, 14, 32, 82, 188, 438, 984 at `n = 5 … 12`) are all of the kind refuted in Lean. A sequence of the shape `1, 0, …, 0, 1, 2, 1` has an end link in the middle level that may meet both outer levels, so the respective clause confines its block to the middle level. Under Bing's "or" reading these instances are covered by `S2`, which has no failure.
* **Cross-check.** `T3END` reproduces batch 87's counts and its verdict (no failure).

**Bing's chains** `P(0, 4)` to `P(0, 6)` (`KK = 5, 6, 7`). All subchains are included, at every basepoint, with node limit `2 · 10⁶`. Batch 87 used only subchains with an end link on an extreme level and interior basepoints, so the instance counts differ.

| `KK` | sequences | instances (`M`) | `T3END` | `T3ENDP` | `S2` | `LIT` | `LITP` | `T3E2` | `T3E2P` | `LITM` | `T3ENDM` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 5 | 66 | 418 (670) | 0 | 0 | 0 | 0 | 3 (0 with `K ≥ 4`) | 0 | 0 | 3 (0 with `K ≥ 4`) | 0 |
| 6 | 406 | 4 872 (7 534) | 0 | 0 | 0 | 0 | 12 (**2** with `K ≥ 4`) | 0 | 0 | 10 (0 with `K ≥ 4`) | 0 |
| 7 | 2 415 | 61 985 (87 102) | 0 | 0 | 0 (1 588 undec.) | 0 (1 588 undec.) | 213 (**186** with `K ≥ 4`; 1 426 undec.) | 0 (29 undec.) | **2** with `K ≥ 4` (33 undec.) | 27 (0 with `K ≥ 4`; 2 070 undec.) | 0 |

**Re-run of the undecided cases.** A re-run of `S2`, `LIT` and `LITM` on Bing `KK = 7` with a node limit ten times larger (`2 · 10⁷`) was stopped after about an hour, before it finished; its partial log is `census-batch121-bing7-big.log`.

* It found no failure with `K ≥ 4`. Its only failures are the `K = 3` respective-reading kind.
* The instances it reached that are hard stayed undecided: `n = 50 … 53`, `K = 6`, basepoints 25 and 26, in each of the three classes (24 lines).
* So the Bing `KK = 7` undecided counts in the table stand.

**The `K ≥ 4` failures of `LITP` and `T3E2P` are not counterexamples.**

* Each of them assumes an extra meeting that is not admissible: adding it to the meeting table makes the sequence non-crooked.
  * The class `LITM`, which presents every admissible set of extra meetings, has no failure with `K ≥ 4`.
  * Example (`KK = 6`, `n = 18`, `K = 5`, basepoint 16): `ρ = σ = 0,1,2,1,2,3,2,1,2,3,2,3,4,3,2,3,2,1`. `LITP` assumes that the last link (level 1) may meet level 0. In a crooked chain it cannot, and `LITM` decides the instance positively.
* No failure was found in a class whose failure would refute a statement:
  * `T3END`, `T3ENDP` and `T3ENDM` for `theorem3_end`;
  * `S2` and `LIT` for the main clause and for `Theorem3Literal` on realized chains, at `K ≥ 4`;
  * `T3E2` for `Theorem3EndTwo`.

  So nothing was certified in Lean through `realization`.

**The Q2 caveat.**

* **`T3ENDP` is the sufficient side** of `theorem3_end_of_model`, and on the corpus above it has no failure. Its zero counts therefore say, by a Lean theorem, that `theorem3_end` holds for **every** chain (in any metric space) whose `(minIdx, maxIdx)` pair, over `k = K` coarse links, is in the enumerated corpus.
  * This does not hold for the Bing rows or the undecided cases.
  * The census verdict itself is not Lean-checked.
* **The two-link classes are weaker evidence for general chains.** `S2` and `LIT` cover realized chains. `LITP` (sufficient for all chains) fails at non-admissible meetings. `LITM` (exact up to realizability of `S`) has no failure at `K ≥ 4`. So no general chain in the corpus is known to violate Bing's statement, but the corpus result for it is not a theorem about all chains.

## Q4 — Bing's proof, the seam

**Verdict: the special case, executed literally, fails, and the failure does not depend on the choice of `H`. The proof is incomplete as written. Bing's statement is not refuted.**

**The special case does occur.** For a whole realized chain with `n ≥ 3` it cannot: a link inside `e₁` forces its neighbour to meet `e₁`. It does occur for subchains, and so for general chains.

* **The chain.** `seamD` is the subchain `1 … 11` of the realized chain of the thirteen-term faithful sequence
  `seamRho = 0,1,1,1,2,2,2,1,2,2,2,3,4`, `seamSig = 0,1,2,1,2,3,2,1,2,3,2,3,4`
  over five strips (`r = 5`).
* `seamD_special`: its end links meet `e₁` and `e₅`, and no interior link meets either.
* `seamD_hk`: crookedness gives the pair `(h, k) = (4, 6)` (0-indexed: `d_h ⊆ e₄`, `d_k ⊆ e₂`), and it is the only one.
* `seamD_minIdx_maxIdx`: the levels of the links are `ρ = 1,1,1,2,2,2,1,2,2,2,3` and `σ = 1,2,1,2,3,2,1,2,3,2,3`.

**The induction hypothesis can be met.** `seamC = D(1, h)` (five links) is crooked in `seamE' = E(1, r − 1)` (four strips; `seamC_crooked`). `SeamIH` is the conclusion of Theorem 3 for it. `seamIH_H0` gives an `H` satisfying `SeamIH`, namely `H = 0, 0, 0, 1, 1` at basepoints `i = 0, 1, 2`; `seamIH_H1` gives `H = 0, 1, 0, 1, 1` at `i = 0`. So the construction is reached.

**The construction, in Bing's words.**

* `h_u` is the first link of `H` containing `d_h`.
* `F = H(1, u − 1) ⌢ (level groups of D′, top to bottom) ⌢ D(k + 1, n)`.
* The groups are "in `e₁ + e₂`", "in `e₃` but not in `e₂`", …, that is, by least level `ρ`. This is `bingSpecialF` (reading A).
* `F` is a chain with `d_i` first iff its time function is 1-Lipschitz along `D` with value `0` at `i`.

**`seam_every_H_fails`.** For **every** basepoint `i ≤ h` and **every** `H` with `H i = 0`, `F` fails: two consecutive fine links get times at least 2 apart, so their links of `F` meet without being adjacent, or `d_i` is not in the first link. Nothing else about `H` is used, so the statement covers every `H` given by the induction hypothesis.

* **Why it fails.** Every link of `D′` has `ρ ≤ 2`. The top group, "in `e₄` but not in `e₃`", is empty, so the time `u` is skipped.
* If `u = 0`, then `d_i` lands in a later group.
* Otherwise the last link of `H(1, u − 1)` before `d_h` is followed by a link of time at least `u + 1`. This is the seam at `h_{u−1}` that the commission predicted, in its sharpest form: `h_{u−1}` meets only an empty group.

**Other readings of the grouping.**

* **`Cbot`.** In `bingSpecialFCbot`, the bottom group `e₁ + e₂` takes links that are in both end groups, and the top group absorbs the rest of `e_{r−2} + e_{r−1}`. `seam_Cbot_fails` shows that this reading fails for the `H` of `seamIH_H1`: `d_1` gets time `0` and its neighbour `d_2` gets time `2`.
* **The census over all readings** (`seam-batch121.py`, `K = 5`; the special case has no instance at `K = 6` up to `n = 14`):

| reading | `n` | instances `(seq, h, k, i)` | some IH-`H` fails | every IH-`H` fails |
|---|---|---|---|---|
| A (by `ρ`, Bing's text) | 11 / 12 / 13 | 320 / 6 528 / 76 288 | 288 / 5 920 / 69 632 | 192 / 3 808 / 43 296 |
| B (by `σ`, top-anchored) | 11 / 12 | 320 / 6 528 | 160 / 3 264 | 160 / 3 264 |
| Ctop | 11 / 12 | 320 / 6 528 | 160 / 3 264 | 160 / 3 264 |
| Cbot | 11 / 12 | 320 / 6 528 | 176 / 3 760 | **0 / 0** |

**Can the construction be read so that it works?** On this corpus only one reading comes close.

* Under `Cbot`, for every instance *some* `H` satisfying the induction hypothesis makes `F` a chain. Under the other readings at least half the instances fail for every `H`.
* So the reading that might work is: group `D′` by `Cbot`, **and choose `H`**.
* The choice is not given by the induction hypothesis. What it must control is which block of `H` the link `d_h` falls in, and what the links of `h_{u−1}` meet. That is the block of an end link of `D(1, h)` relative to its time: exactly the end-time control that is open for `theorem3_end`.
* This reading is not proved here, and the evidence for it is only the `K = 5` census of the table.

**The commission's second seam (`d_{k+1}`) is not a defect.** `d_{k+1}` is a link of `F` by itself, and fine links meet only their neighbours. So the link `{d_{k+1}}` of `F` meets only the group of `d_k` and the link `{d_{k+2}}`. Since `d_k ⊆ e₂`, that group is the bottom group, which is adjacent to it in `F`.

**The general case.**

* **The wording.** "Any link of F containing an end link of D(h, k)" should read "of H", as the commission says. With that correction the step is sound as far as the regrouping goes.
* **No seam at `h_{u−1}`.**
  * `h_u` is the first link of `H` meeting `e₁ + e_r`; say it meets `e₁`. Then `h_u ⊆ e₁ + e₂`, so all of `h_u` lies in the bottom group.
  * The end links of `D(h, k)` meet `e₁` or `e_r`, so none lies in `H(1, u − 1)`. Hence the links of `H(1, u − 1)` are interior to `D(h, k)`, and their fine neighbours lie in `H(1, u)`.
  * So `h_{u−1}` meets only `h_{u−2}` and the bottom group.
* **The grouping by `ρ` is 1-Lipschitz along `D′`.** A link inside `e_a ∩ … ∩ e_b` lies in `e_a`, so neighbours have `|Δρ| ≤ 1`.
* **What remains open.** The gap in the general case is the existence of `H`, which calls the special case when `D(h, k)` meets both `e₁` and `e_r`. That is exactly where the special case fails.
* This analysis of the general case is informal. It was not formalized.

## Q5 — Assessment

* **Bing's Theorem 3 as printed** (`Theorem3LiteralOr`): **(iii) open.**
  * No counterexample was found. `S2` and `LIT` have no failure, and `LITM` has none at `K ≥ 4`.
  * The *respective* reading of its end clause (`Theorem3Literal`) is **(ii) refuted** at `k = 3` (`not_theorem3Literal`). It is the same statement for `k ≥ 4`, where it is open.
  * The only-clause is automatic in realized chains but not in general (`only_clause_not_automatic`).
* **`theorem3_end`: (iii) open.**
  * No counterexample was found in the possible-meeting census `T3ENDP`. By `theorem3_end_of_model`, its zero counts cover every chain whose `(minIdx, maxIdx)` pair, over `k = K` coarse links, is in the enumerated corpus.
  * None was found in `T3END` or `T3ENDM` either.
* **Bing's proof: incomplete as written.**
  * The special case, executed literally, fails for every `H` (`seam_every_H_fails`, on a chain satisfying the special-case hypotheses: `seamD_special`, `seamD_hk`). The construction is reached (`seamIH_H0`), and the alternative grouping `Cbot` fails for an admissible `H` (`seam_Cbot_fails`).
  * The general case is sound modulo the special case.

**What a proof would need.** Both statements need control of where the block of an end link sits in the time order ("end-time control"); the main clause alone gives none. For Bing's argument, the induction hypothesis must be strengthened so that the consolidation `H` of `D(1, h)` can be chosen with the link `h_{u−1}` before the block of `d_h` meeting only links of `D′` that the regrouping places in a single group next to it. Equivalently, the time of the block of the end link `d_h` must be fixed relative to the levels of the links it meets. The `Cbot` census row shows such an `H` exists on the `K = 5` corpus. Whether this strengthened hypothesis is itself provable by Bing's induction (it must be reproduced for `F`) was not checked. For `theorem3_end` the needed statement is the three-link form of the same control, for the end links of the whole chain. No reduction of it to a weaker statement was found; the obstruction recorded in OPEN.md item 1 is unchanged.

**Recommendation.** Keep `theorem3_end` as the audited open target (`sorry`). Nothing in the build depends on it. It is implied by Bing's statement (`theorem3EndStmt_of_literalOr`) and, through the model, by `T3ENDP` (`theorem3_end_of_model`). Record `Theorem3LiteralOr` (Bing's wording) as the `Prop` for Theorem 3 as printed, not `Theorem3Literal`, which is false at `k = 3`. David decides.

## Ledger text (entered in LEDGER.md §1, "Bing 1948 and its skeletons")

| statement (source) | refutation (Lean) | explanation |
|---|---|---|
| Theorem 3 as printed (Bing 1948), end clause read *respectively* (`Theorem3Literal`, batch 121) | `HPC.Fold.Recon121.not_theorem3Literal` (`Fold/Recon121.lean`) | Three coarse links (strips), five rectangles, basepoint 2: the end links lie in the middle strip and reach into both outer strips, so the respective clause puts their blocks in `D_1`, and no two-link block map separates them from links 1 and 3. Bing's own wording (`Theorem3LiteralOr`) is **not** refuted: for `k = 3` it follows from the main clause, for `k ≥ 4` the readings coincide (`endClause_or_iff`). The statement as printed is open. |
| Theorem 3, Bing's proof, special case (Bing 1948, p. 732) | — (statement not refuted; defect in the proof, certificate `HPC.Fold.Recon121.seam_every_H_fails`, with `seamD_special`, `seamD_hk`, `seamIH_H0`, `seam_Cbot_fails`) | Eleven links of a realized chain over five strips satisfy the special-case hypotheses with `(h, k) = (4, 6)` forced; an `H` satisfying the induction hypothesis exists, but for every basepoint `i ≤ h` and every `H` the literal `F = H(1, u−1) ⌢ (level groups of D′) ⌢ D(k+1, n)` is not a chain with `d_i` first (the top group of `D′` is empty, so a time is skipped); the alternative grouping fails too. |

## Deliverables

1. `HPC/Fold/Recon121.lean` (builds; no `sorry`, no `native_decide`). It contains:
   * the definitions of Q1;
   * the implications of Q1(c);
   * the Q2 theorems `exists_chain_iff_isCrookedIvF`, `chain_of_modelEndP` and `theorem3_end_of_model`;
   * the refutation `not_theorem3Literal`;
   * the Q4 certificate.
2. Audit `doc/batches/audits/axioms-batch121.{lean,txt}` (50 theorems), and `axioms.txt` regenerated (`sorryAx` in two declarations).
3. This report. `LEDGER.md` §1 has the two rows above. `OPEN.md` is unchanged, because item 1's status did not change.
