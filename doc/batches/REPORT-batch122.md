Commission read: COMMISSION-batch122.md (batch 122 — reconnaissance: can Bing's induction for Theorem 3 be closed by a stronger hypothesis?).

# Report, batch 122

**Outcome.**

* **Bing's induction closes in the faithful model, and no strengthening of the hypothesis is needed.** Three repairs suffice. (1) The level groups of the special case are read as `Cbot`. (2) At `r = 5` the special case uses an explicit grouping. (3) The branch "`d_i` between `d_h` and `d_k`", which Bing covers by "a similar argument", applies the induction hypothesis to `D(h, k)` inside `E(2, r − 1)`. The theorem is `HPC.Fold.Recon122.bing_main : ∀ K, BingMain K`, Bing's Theorem 3 in the model (block reading, blocks in two adjacent links, the "or" end clause read with the meeting table). It has standard axioms.
* **The statement of `theorem3_end` is proved.** `HPC.Fold.Recon122.theorem3_end'` is the statement of `HPC.Fold.theorem3_end` (`HPC/Fold/Theorem4.lean`), word for word, with standard axioms. The `sorry` in `Theorem4.lean` was **not** touched, since that file is outside the scope of this batch. Replacing that `sorry` by `Recon122.theorem3_end'` would close OPEN.md item 1. That decision belongs to the commission owner.
* **Bing's Theorem 3 as printed is proved apart from the only-clause** (`theorem3Block_holds`). This holds for every chain crooked (1948 sense) in a chain, in every metric space. The only-clause ("`d_i` is contained in only the first link of `F`") is still open for general chains. On realized chains it is automatic (`linkChain_only`, batch 121).
* **Q1:** a property `P` that separates is found: `SeamP`, candidate (s). Every `H` with `P` works under `Cbot`, and on the corpus some `H` has `P` at every instance. In Lean: `cbot_works_of_seamP` and `seamP_of_endClause`. Candidates (a)–(d) are all **refuted** as sufficient conditions.
* **Q2:** `P` **does not need to reproduce**. At `r ≥ 6` it follows from the end clause of the induction hypothesis, and at `r = 5` the special case does not use `H` at all.
* **Q3:** proved: `Theorem3Strong` (with `P = True`), `Theorem3Strong → Theorem3EndStmt`, and `Theorem3Strong → Theorem3Block`. `Theorem3Strong → Theorem3LiteralOr` is **open** because of the only-clause.
* **Q4:** not pursued, because Q3 superseded it.

**Audit.** The four new files have 44 theorems, and every one depends only on `[propext, Classical.choice, Quot.sound]` or a subset of it (`doc/batches/audits/axioms-batch122.{lean,txt}`). There is no `native_decide`. `axioms.txt` was regenerated: 452 lines, up from 436, with 16 new entries in the group "Reconnaissance, batch 122". `sorryAx` still occurs in exactly two declarations, `HPC.Fold.theorem3_end` and `HPC.Plane.fugate_cor1`. The previous version is kept as `doc/batches/audits/axioms-before-batch122.txt`.

**Files.**

* **New Lean files**, all without `sorry`. Open statements are `def … : Prop`.
  * `HPC/Fold/Recon122.lean`, imported on the last line of `HPC.lean`.
  * Its three dependencies, which together hold Bing's induction in the model:
    * `HPC/Fold/Recon122Model.lean`: the model `BHyp`/`BConcl`, the transformations, the base case and the level cases.
    * `HPC/Fold/Recon122Special.lean`: the special case.
    * `HPC/Fold/Recon122General.lean`: the general case and `bing_main`.
* **Edited files.**
  * `HPC.lean`: one import.
  * `Axioms.lean`: new group "Reconnaissance, batch 122", 16 entries.
  * `axioms.txt`: regenerated.
  * Housekeeping, §3 below: `README.md`, `OPEN.md`, `doc/census/README.md`.
* **`LEDGER.md`: not edited.** No refutation of a statement was found.
* **New census files.**
  * Programs: `doc/census/recon-batch122-q1.py` (Q1: candidates for `P`, using `seam-batch121.py`) and `doc/census/recon-batch122-bing.py` (the repaired recursive algorithm, run on the corpus).
  * Logs: `doc/census/recon-batch122-*.log`.

---

## Q1 — What distinguishes the `H` that work? **Answered: `P_s` (candidate s); (a)–(d) refuted**

**Corpus.** These are the special-case instances `(seq, h, k, i)` with the basepoint in `D(1, h)`. Every `H` allowed by the induction hypothesis was enumerated: basepoint first, blocks in two adjacent links of `E(1, r − 1)`, and the "or" end clause for `d₁` and `d_h`. This is the `SeamIH` reading of batch 121. For each `H`, the census formed `F` under `Cbot` (`bingSpecialFCbot`) and under Bing's reading A (`bingSpecialF`), and checked whether `F` is a chain with `d_i` first and with Bing's clauses. Program: `recon-batch122-q1.py`.

**Candidates.** Coordinates are 0-indexed and `u = H(h)`.

* (a) `u = max H`.
* (b) every link of `h_{u−1}` has `σ ≥ r − 4`, which is Bing's `σ ≥ r − 3` in 0-indexed form.
* (c) both (a) and (b).
* (d) the end-time form: for each end link `e ∈ {d₁, d_h}` meeting an extreme level `L` of `E(1, r − 1)`, `H(e)` is the largest time of a link meeting `L`.
* (s) **strict end clause at `d_h`**: every link of the block `h_u` of `d_h` has `ρ ≥ r − 3`, i.e. lies in none of `e₁ … e_{r−3}`.
* (w) the exact working condition, for reference.

**Table 1 — K = 5** (`recon-batch122-q1-k5.log`).

* The four numbers in a cell are: #H with P / #H with P failing under `Cbot` ("unsound") / #instances with no H with P ("unsat").
* "IH-H" is the number of `H` satisfying the induction hypothesis.
* "work C" and "work A" count the IH-H that work under `Cbot` and under reading A.

| `n` | instances | IH-H | work C | work A | (a) | (b) | (d) | **(s)** |
|---|---|---|---|---|---|---|---|---|
| 11 | 320 | 3 296 | 2 640 | 792 | 1 280 / 176 / 128 | 3 296 / 656 / 0 | 2 592 / 512 / 0 | **2 336 / 0 / 0** |
| 12 | 6 528 | 102 960 | 82 656 | 24 888 | 38 400 / 5 024 / 2 624 | 102 960 / 20 304 / 0 | 76 864 / 15 168 / 0 | **73 440 / 0 / 0** |
| 13 | 76 288 | 1 921 280 | 1 545 792 | 465 368 | 686 400 / 84 960 / 30 848 | 1 921 280 / 375 488 / 0 | 1 358 160 / 270 048 / 0 | **1 378 992 / 0 / 0** |

* (c) has the same counts as (a) at every `n`.
* (w) holds for exactly the `H` that work under `Cbot`, by construction.
* At every instance some `H` works under `Cbot`. No instance has all `H` failing.
* A counterexample to (a), (b) and (d) at once: `ρ = [1,1,1,2,2,2,1,2,2,2,3]`, `σ = [1,2,1,2,3,2,1,2,3,2,3]`, `h = 4`, `k = 6`, `i = 0`, `H = [0,1,0,1,1]`. Here (a), (b) and (d) hold, and `F` fails under `Cbot`.
* (a) is unsatisfiable at, for example, the same sequence with `i = 3`.

**Table 2 — per-instance counts "H satisfying IH / with P_s / working (Cbot)", K = 5, n = 11.** There are 320 instances. They fall into 19 count profiles, each shared by 16 instances (one by 32). The full listing, `H` by `H`, with C/A flags and the candidates that hold, is `recon-batch122-q1-k5-list11.log`.

| IH-H / with `P_s` / working | instances |
|---|---|
| 10 / 10 / 10 | 32 |
| 22 / 12 / 12 | 16 |
| 19 / 14 / 19 | 16 |
| 15 / 14 / 15 | 16 |
| 15 / 12 / 12 | 16 |
| 15 / 10 / 12 | 16 |
| 13 / 10 / 13 | 16 |
| 13 / 5 / 9 | 16 |
| 11 / 7 / 7 | 16 |
| 10 / 3 / 3 | 16 |
| 9 / 5 / 7 | 16 |
| 8 / 7 / 7 | 16 |
| 7 / 5 / 6 | 16 |
| 7 / 4 / 4 | 16 |
| 6 / 3 / 3 | 16 |
| 5 / 5 / 5 | 16 |
| 4 / 4 / 4 | 16 |
| 4 / 3 / 4 | 16 |
| 3 / 3 / 3 | 16 |

In every row, 1 ≤ with `P_s` ≤ working ≤ IH-H.

**K = 6.** The enumeration finds **no** special-case instances for `n = 8 … 16` (`recon-batch122-q1-k6.log`, `n = 8 … 13`; `recon-batch122-q1-k6b.log`, `n = 14 … 16`). The first `K = 6` special-case instances found are inside Bing's chain `P(0, 5)`, where `n = 28` (`recon-batch122-q1-bing6.log`):

| corpus | instances | IH-H | work C | work A | (a) | (b) | (d) | (s) |
|---|---|---|---|---|---|---|---|---|
| Bing `P(0,5)`, `K = 5` subchains, `n = 11` | 10 | 64 | 64 | 34 | 24 / 0 / 4 | 64 / 0 / 0 | 50 / 0 / 0 | 64 / 0 / 0 |
| Bing `P(0,5)`, `K = 6`, `n = 28` | 12 | 5 362 | 5 362 | 2 893 | 2 045 / 0 / 5 | 5 018 / 0 / 0 | 3 994 / 0 / 0 | 5 362 / 0 / 0 |

At `K = 6`, **every** IH-H works under `Cbot`. The proof below explains why.

**The property, in Lean.** The census reading of (s) is "every link of `h_u` has `ρ ≥ r − 3`". `SeamP K ρ σ H h` says instead that every link of `h_u` has `ρ ≥ 2` and `σ ≥ K − 3`, i.e. it lies in the top `Cbot` group. At `K = 5` the two conditions coincide, and for `K ≥ 6` `SeamP` is the weaker of the two.

* `bingSpecialFCbot_eq_cutF`: the batch-121 `F` is the closed construction `cutF`, cut at the block of `d_h`.
* **`cbot_works_of_seamP`**, for every `r ≥ 5`. Suppose `H` is a consolidation of `D(1, h)` with `d_i` at time 0, the block of `d₁` lies in `e₁ + e₂` (the end clause at `d₁`), and `SeamP` holds. Then `bingSpecialFCbot` satisfies Bing's conclusion: `F(i) = 0`, it is a consolidation with blocks in two adjacent links, and it satisfies the end clause.
* **`seamP_of_endClause`**, for `r ≥ 6`. If `d_h` reaches `e_{r−1}` and `H` satisfies the end clause of the induction hypothesis at `d_h`, then `SeamP` holds. So for `r ≥ 6` **every** IH-H works, as the `n = 28` census shows. Only at `r = 5` can the induction hypothesis put a link of `e₂ + e₃` into the block of `d_h`, and only then do some `H` fail. This explains the failures of batch 121, which were all at `K = 5`.

The reading `Cbot` is necessary: under Bing's reading A, `F` fails for 2 469 of the 5 362 IH-H even at `K = 6`.

## Q2 — Does `P` reproduce? **Not needed (answered by the proof)**

The induction in Lean carries **no** property of the consolidation beyond Bing's conclusion. In `Theorem3Strong`, `P = True`. Point by point:

* **(a) Base cases and the level cases.** These are `bconcl_base` (`m ≤ 4`), `bconcl_low` (`d_i ⊆ e₁ + e₂`, groups by the least level) and `bconcl_high`, the mirror image. They are proved outright and need nothing of `P`.
* **(b) Special case.**
  * At `r ≥ 6`, `P_s` comes for free from the end clause (`seamP_of_endClause`). That covers `special_branch1` (`d_i ∈ D(1, h)`), its mirror image (`d_i ∈ D(k, n)`), and `special_middle` (`d_i` strictly between `d_h` and `d_k`). In the last branch, `H` is taken on `D(h, k)` inside `E(2, r − 1)` and cut at the earlier of the blocks of `d_h` and `d_k`.
  * At `r = 5`, `special_five` gives an explicit grouping that needs no `H`: the links up to `d_k` in `e₁ + e₂`, the other links up to `d_k`, then the links after `d_k` one by one.
  * So the question "is there an `H` with `P` such that `F` has `P`" does not arise.
* **(c) General case.** This is `general_case`, via `genF_concl`: Bing's regrouping, cut at the first block of `H` containing a link that meets `e₁` or `e_r`, with the remaining links grouped by level from the bottom. It needs only Bing's conclusion for `H`, which comes from the induction hypothesis or from the special case.

Whether `F` itself satisfies a version of `P_s` relative to `E` was not censused further, because the proof does not use it.

**Census of the repaired algorithm** (`recon-batch122-bing.py`, Python, not machine-checked). It runs Bing's recursion with the repairs above and checks every resulting `F`. **No failure** was found on any of the following corpora:

| corpus | instances | failures | log |
|---|---|---|---|
| special case, `K = 5`, `n = 11, 12, 13` (every basepoint) | 704 / 11 520 / 109 824 | 0 | `special-5-11-12`, `special-5-13-13` |
| all faithful sequences with the possible-meeting tables, `K = 3`, `n = 3 … 10` | 8 174 672 | 0 | `enum-3-3-10` |
| same, `K = 4`, `n = 4 … 11` | 5 713 184 | 0 | `enum-4-4-11` |
| Bing's chains `P(0, KK−1)`, every subchain and frame, `KK = 5, 6, 7` | 1 545 / 20 014 / 269 282 | 0 | `bing-{5,6,7}-frames` |
| Bing's chains, `KK = 7`; `KK = 8` (length 170) | 62 125; 833 170 | 0 | `bing-7`, `bing-8` |

The `KK = 8` run took every branch of the recursion: 223 808 instances in each special branch, 111 484 in the middle branch, and 559 100 general instances with a special subchain. The `K = 5` enumeration run (`enum-5-11-13`) was stopped by hand during `n = 12`.

## Q3 — The strengthened statement. **Proved (`Theorem3Strong`, `→ Theorem3EndStmt`, `→ Theorem3Block`); `→ Theorem3LiteralOr` open**

In `HPC/Fold/Recon122.lean`:

* `Theorem3Strong : Prop := ∀ K, BingMain K`. This is Bing's statement in the block reading in the model, for every number of coarse links, with the meeting table as data and `P = True`.
* **`theorem3Strong_holds`** (`= bing_main`). Bing's induction on `K` (`special_case` and `general_case`), with the repairs of Q2.
* `bHyp_of_crooked`: every chain crooked (1948 sense) in a chain satisfies the hypotheses of the model, with its `(minIdx, maxIdx)` and its true meeting table.
* `chain_of_bconcl`: a solution in the model gives a block consolidation of the chain.
* `Theorem3Block : Prop`: `Theorem3LiteralOr` without its only-clause.
* `theorem3Block_of_literalOr`: `Theorem3LiteralOr → Theorem3Block`.
* **`theorem3Block_of_strong`**: `Theorem3Strong → Theorem3Block`.
* **`theorem3EndStmt_of_strong`**: `Theorem3Strong → Theorem3EndStmt`, through `theorem3EndStmt_of_block`.
* **`theorem3Block_holds`**, **`theorem3EndStmt_holds`**, **`theorem3_end'`**: the unconditional consequences.

**Open: `Theorem3Strong → Theorem3LiteralOr`.** The only-clause asks that `E.link i` not be contained in any block of `F` other than its own.

* By `link_subset_neighbours` (batch 121), it can fail only if `E.link i` is covered by its neighbours `E.link (i ± 1)`, and those neighbours lie in another block.
* `only_clause_not_automatic` shows that chains allow such links.
* If `i` is an end link, the defect can be repaired by moving the covering neighbour into the first block. For an interior `i`, the neighbours may be split across both adjacent blocks, and no repair was found.
* On realized chains the clause is automatic (`linkChain_only`). So, as the commission says, nothing is lost for Bing's statement on realized chains.

## Q4 — The three-link end clause. **Not pursued (superseded)**

Q4 asked for a route to `theorem3_end` through Z77's greedy choice. The statement of `theorem3_end` is now proved by another route (`theorem3_end'`, from the two-link theorem), so no three-link analogue of `P` was formulated or censused. Z77 was not modified. Whether Z77's construction (`Fit`, `greedy_fit`) can be made to satisfy end-time control by a change of the greedy choice is still **open**, as a question about Z77. It is no longer needed for `theorem3_end`.

## Q5 — Assessment

| question | status |
|---|---|
| A reproducing `P` exists (on the corpus) | **Not needed.** `P_s` separates the working `H` and holds at every instance of the corpus (Q1). The induction needs no `P` to reproduce (Q2). |
| Bing's induction closes with it (in Lean) | **Proved**: `bing_main` / `theorem3Strong_holds`, with standard axioms |
| `theorem3_end` by Q4 | **Not pursued.** The statement of `theorem3_end` is **proved** by Q3 (`theorem3_end'`). |
| Theorem 3 as printed (`Theorem3LiteralOr`) | **Open**, only through the only-clause for general chains. Everything else is proved (`theorem3Block_holds`). |

Two pieces would complete the picture. The first is mechanical: replace the `sorry` of `HPC.Fold.theorem3_end` by `HPC.Fold.Recon122.theorem3_end'`. This would leave `sorryAx` in one declaration, `fugate_cor1`; it is outside this batch's scope and is for the commission owner to decide. The second concerns the only-clause for general chains. It needs either a repair of `F` at an interior basepoint covered by its two neighbours lying in different blocks, or a counterexample built on `only_clause_not_automatic`.

## Housekeeping (§3), confirmed

1. **`README.md`.** "Theorems 1–15 (Theorem 3 without its end-link clause)" was replaced by the commission's wording. A sentence was added saying that batch 122 proved the statement of `theorem3_end` (`Recon122.theorem3_end'`) and Theorem 3 without the only-clause (`Recon122.theorem3Block_holds`), and that `theorem3_end` itself still carries its `sorry`. Without that sentence the prescribed wording "end clause open" would be out of date. The batch count was changed from 120 to 122.
2. **`OPEN.md` item 1.** A "Batch 121" paragraph cites `theorem3_end_of_model`, the census class `T3ENDP` and its corpus, `Theorem3LiteralOr`, `theorem3EndStmt_of_literalOr`, and the proof defect with its certificate `seam_every_H_fails`. A "Batch 122" paragraph records `theorem3_end'`. The item stays in the list, because the `sorry` is still there.
3. **`doc/census/README.md`.** The batch-121 programs and logs (`census-batch121.c`, `census-batch121-*.log`, `seam-batch121.{py,log}`) and this batch's files are listed.
4. **Notes file.** The uploaded `theorems-3-4-scheduling(28).md` was moved to `doc/theorems-3-4-scheduling.md`; the new file only extends the old one. No stray copy remains at the root. The commission was filed as `doc/batches/COMMISSION-batch122.md`.
