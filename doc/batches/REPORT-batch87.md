Commission read: `COMMISSION-batch87.md` (batch 87 — Bing 1948, the two open items, continued: three-link blocks, and end-time control of folds). Run on top of batch 86; batch 85 has not been run.

# Report — batch 87

**Summary.**
* Neither target is proved or refuted. `Description.covering_step` (`HPC/PseudoArc/Theorem14.lean`) and `Fold.theorem3_end` (`HPC/Fold/Theorem4.lean`) are unchanged and still `sorry`. Nothing outside the new files was changed, except that `HPC.lean` now imports them.
* New Lean files, all imported from `HPC.lean` and all free of `sorry`:
  * `HPC/PseudoArc/Recon87.lean` (item 1)
  * `HPC/PseudoArc/Recon87Model.lean` (items 1–2, the model side)
  * `HPC/Fold/Recon87End.lean` (item 3)
* `#print axioms` for every new theorem is in `axioms-batch87.txt` (generated from `Axioms87.lean`). Each uses only `propext`, `Classical.choice` and `Quot.sound`, or a subset of them.
* Census sources: `census-batch87-model.c` together with `census-batch87-common.h`. Logs: `census-batch87-k4.log`, `census-batch87-k5.log`, `census-batch87-bing.log`. Each log begins with the exact statements it decides.
* Results by item:
  * **Item 1: proved.** This is `coveringStep_of_folds₃`.
  * **Item 2: refuted as stated**, with a kernel-checked refutation. Under the extra separation S2, which holds at deep levels, the search found no failure.
  * **Item 3: refuted**, with two kernel-checked refutations. The second one already assumes the obvious necessary condition.
  * **Item 4: open.** The search found no failure, and every Bing case of `theorem3_end` at `K = 7` is now decided.

## 1. Refutations

All three are proved in Lean. In each, crookedness in the faithful model (`IsCrookedIvF`) is checked by the kernel, and the non-existence of a fold is a short proof by `omega`.

1. **`Fold.model_covering_fold₃_refuted`** (`Recon87Model.lean`). The three-link time-ordering fold of item 2 can fail.
   * **Data.** Seven links with coarse intervals `[0,0], [0,0], [1,1], [1,2], [1,1], [2,2], [3,3]`. `P'` is in link `1`, `R` in link `6`, `Q'` in link `0`, and `W` meets links `1 … 6`.
   * **Hypotheses that hold.**
     * The pattern is crooked.
     * It has the window property.
     * The links of `P'` and `R` are three coarse levels apart (S1, `3 ≤ levelGap … 1 6`).
   * **Hypothesis that fails.** S2: the link of `Q'` is adjacent to the link of `P'`.
   * **Why no fold exists.**
     * `β 1 = 0` and `β 0` is the maximal time, so the maximal time is at most `1`.
     * Link `6` (level `3`) cannot share a block with link `1` (level `0`). So `β 6 = 1`.
     * Link `6` also cannot share a block with link `0` (level `0`). So `β 0 ≠ 1`.
     * Then `β 0 = 0`. But `β 0` is the maximal time and `β 6 = 1 > 0`, a contradiction.
2. **`Fold.model_end_time_refuted`** (`Recon87End.lean`). The end-time lemma of item 3 can fail.
   * **Data.** Coarse levels `0, 1, 2, 1, 2, 3, 3` (`ρ = σ`), `p = 5`, `c = 6`.
   * **Hypotheses that hold.**
     * The pattern is crooked.
     * It has the window property with respect to the arm `[0, p]`.
     * The links of `R` and `P'` are three levels apart.
   * **Why no fold exists.** Both ends are at the maximal time, so they lie in one block (`ModelEndTime.ends_close`, proved in general). Their levels `0` and `3` do not fit in one three-link window.
3. **`Fold.model_end_time_refuted'`** (`Recon87End.lean`). The end-time lemma still fails when the ends *do* fit in one window (condition C).
   * **Data.** Fifteen links spanning five coarse links, `p = 13`, `c = 14`:
     * lower ends `ρ = 0,0,1,1,1,2,2,2,1,2,2,2,3,4,3`;
     * upper ends `σ = 1,0,1,2,1,2,3,2,1,2,3,2,3,4,3`.
   * **Hypotheses that hold.** Crookedness (checked with `isCrookedIvF_of_check2` and `decide +kernel`), the window property, the separation of `R` and `P'`, and C.
   * **Why no fold exists.**
     * The arm `[p, c]` is one step long, so the maximal time is at most `1`.
     * Link `1` (level `0`) fits in neither block: block `0` holds level `4`, and block `1` holds level `3`.

No counterexample to `covering_step` or to `theorem3_end` was found.

## 2. Item 1 — three-link blocks: **proved**

* **`Description.IsCoveringFold₃`** (`Recon87.lean`) is `IsCoveringFold` with the block clause changed to `∀ u, ∃ j, ∀ t, β t = u → (D k).link t ⊆ (D m).unionRange j 3`. The other clauses are unchanged: `P'` in block `0`, `Q'` in the last block, `R` in block `b`, and every `W`-link in a block `≤ b`.
* **`IsCoveringFold.toFold₃`**: a one-link fold is a three-link fold.
* **`Description.coveringStep_of_folds₃`**, proved. Suppose that for every `m₀` there are `m, k ≥ m₀` and a three-link fold of `D_k` over `D_m`. Then `CoveringStep Δ P' Q' R W` holds.
  * **The closures clause.** A Lebesgue number `δ` of the cover of `closure (D_{L+1}).union` by the links of `D_L` is used, as in `exists_step`.
  * **Choice of `m`.** Take `m` with `ε_m < min δ (1/(L+1)) / 3`.
  * **Why that suffices.** A block lies in `closedBall x₀ (3 ε_m)` by `dist_le_of_mem_unionRange`. That ball is inside a Lebesgue ball, and its diameter is at most `1/(L+1)`.
* **`Fold.ModelCoveringFold₃`** (`Recon87Model.lean`) is the model reading: `∃ j, ∀ t, β t = u → j ≤ σ t ∧ ρ t ≤ j + 2`.
  * **`Fold.model_covering_fold₃_recon86`**: the batch-86 witness has the fold `β = (0,1,2,3,3,4)`, with `b = 3` and every block in the window `[0, 2]`. Commission §0.1 is confirmed in Lean.

## 3. Item 2 — census for `ModelCoveringFold₃`: **refuted as stated; no failure under S2**

**Statement decided (class `FOLD3`).**
* **Data.** A faithful sequence `(ρ, σ)` of length `n` spanning exactly `K` coarse links, and indices `a ≠ c` (links of `P'`, `R`) and `q` (link of `Q'`).
* **The interval `I`.** `I` is the largest index interval that contains `a` and `c`, does not contain `q`, and whose members all have the window property with respect to `[min a c, max a c]` (`ModelWindow`).
* **Claim.** There is a three-link block map with `β a = 0`, with `β q` the maximal time, and with `β t ≤ β c` for every `t ∈ I`.

**Why the largest `I` is enough.** The fold condition is antitone in `I`, and the window property is checked member by member. So the largest admissible `I` is the hardest case: a fold for it is a fold for every smaller admissible `I`. The singletons `A = {a}`, `T = {c}`, `Qs = {q}` are used. Every `(a, c, q)` is tried.

**Hypothesis classes.**
* none;
* **S1:** `levelGap a c ≥ 3`;
* **S2:** `levelGap t q ≥ 3` for every `t ∈ I` (`ModelFar`);
* S1 + S2.

S1 and S2 both hold at deep levels:
* two points in links at most two apart are within `3 ε_m`;
* `P' ≠ R`;
* `Q'` is at positive distance from `W`.

| range | sequences | none | S1 | S2 | S1+S2 |
|---|---|---|---|---|---|
| `K = 4`, `n = 6` | 32 | 2 560 / 0 | 0 | 0 | 0 |
| `K = 4`, `n = 7` | 352 | 49 280 / 80 | 96 / 16 | 32 / 0 | 0 |
| `K = 4`, `n = 8` | 2 528 | 566 272 / 1 504 | 1 856 / 256 | 448 / 0 | 0 |
| `K = 4`, `n = 9` | 14 880 | 4 999 680 / 16 656 | 21 024 / 2 512 | 3 904 / 0 | 0 |
| `K = 4`, `n = 10` | 78 016 | 37 447 680 / 140 832 | 182 208 / 19 360 | 27 072 / 0 | 0 |
| `K = 4`, `n = 11` | 379 584 | — | — | 163 840 / 0 | 0 |
| `K = 4`, `n = 12` | 1 754 176 | — | — | 906 560 / 0 | 0 |
| `K = 4`, `n = 13` | 7 811 008 | — | — | 4 711 104 / 0 | 0 |
| `K = 5`, `n = 13` | 512 | — | — | 512 / 0 | 0 |
| `K = 5`, `n = 14` | 10 752 | — | — | 19 456 / 0 | 0 |
| `K = 5`, `n = 15` | 129 536 | — | — | 352 768 / 0 | 0 |
| `K = 5`, `n = 16` | 1 174 016 | — | — | 4 399 616 / 0 | 0 |
| Bing `K = 5`, all subchains | 66 | 12 012 / 68 | 140 / 6 | 4 / 0 | 0 |
| Bing `K = 6`, all subchains | 406 | — | — | 504 / 0 | 0 |
| Bing `K = 7`, all subchains | 2 415 | — | — | 67 316 / 0, 530 undecided | 12 / 0 |
| Bing `K = 8`, whole chain (170 links) | 1 | — | — | 11 616 / 0, 2 874 undecided | 240 / 0, 32 undecided |

How to read the table:
* Entries are `instances / failures`.
* "—" means the class was not run at that range. Classes none and S1 need `n³` searches per sequence, so they were run only up to `n = 10` and on Bing `K = 5`.
* Undecided cases (the node limit was reached in both search orders) are listed where there are any.
* **Search limits.** The limit is `2·10⁷` nodes per order for the exhaustive ranges, and `2·10⁶` for Bing `K ≥ 6`. A rerun of Bing `K = 7` at `5·10⁷` nodes did not finish in under three hours and was stopped, so its results are not reported.

**Reading.**
* The three-link statement is false under crookedness, the window property and S1: §1.1 is the smallest such witness, found at `n = 7`.
* Every failure found violates S2.
* Under S2 no failure was found.
* **Caveat.** At `K = 4, 5`, S2 forces every link of `I` into one three-link window, so those instances test only the part of the chain outside `I`. Non-degenerate S2 instances first occur in the Bing chains at `K ≥ 6`, and S1 + S2 instances first occur at `K = 7`.
* The statement with S2 is recorded as a commented conjecture at the end of `Recon87Model.lean`. It is not proved.

## 4. Item 3 — the end-time control lemma: **refuted; obstruction stated**

**Statement** (`Fold.ModelEndTime ρ σ p` on `Fin (c+1)`). There is a three-link block map of `[0, c]` with `β p = 0` and `β 0 = β c = q − 1`, i.e. both arm ends at the maximal time. `P'`'s link set is taken to be `{p}`. This is weaker than asking for both links of `P'`, so each refutation also refutes the two-link version.

**Proved obstruction** (`ModelEndTime.ends_close`). Both ends are in the last block, so the coarse intervals of links `0` and `c` meet a common window `[j, j+2]` (condition C). Nothing in the setting of `covering_step` puts the last `W`-link `c` near `R`'s link. §1.2 refutes the lemma under crookedness, the window property and the separation S of `R` and `P'`.

**Second obstruction.** Under C there is still the *length of the arm `[p, c]`*.
* The block map is 1-Lipschitz, so the maximal time is at most `c − p`. It is also at least the number of times the arm `[0, p]` needs.
* §1.3 refutes the lemma under crookedness, the window property, S and C together.

**Which extra hypothesis excludes the failures.** The condition that does is **X**: each arm `[0, p]` and `[p, c]` contains a link at coarse level `0` and a link at level `K − 1`. This is Theorem 4's hypothesis, on each arm.
* Under C + X no failure was found, with or without the window property.
* Neither C nor X is known to follow from the irreducibility of `W`, or from anything else among the hypotheses of `covering_step`.
* **C.** It asks the last `W`-link to lie near `R`.
* **X.** Nothing forces the arm beyond `P'` to sweep the coarse range. When `P'` lies near the last `W`-link, that arm is short.
* So I did not assemble `covering_step` from item 3.

**Census (class `END`, `c = n − 1`, every basepoint `0 < p < c`).** The hypothesis classes are:
* none;
* W (`ModelWindow ρ σ 0 p univ`);
* W + S (S: `levelGap 0 p ≥ 3`);
* X;
* W + S + X;
* C;
* W + S + C;
* C + X;
* W + S + C + X.

| range | none | W | W+S | X | W+S+X | C | W+S+C | C+X | W+S+C+X |
|---|---|---|---|---|---|---|---|---|---|
| `K=4`, `n=6` | 128/32 | 48/0 | 0 | 0 | 0 | 96/0 | 0 | 0 | 0 |
| `K=4`, `n=7` | 1 760/360 | 640/16 | 24/8 | 0 | 0 | 1 400/0 | 16/0 | 0 | 0 |
| `K=4`, `n=8` | 15 168/2 624 | 5 520/224 | 304/96 | 0 | 0 | 12 576/32 | 208/0 | 0 | 0 |
| `K=4`, `n=9` | 104 160/15 536 | 38 328/1 856 | 2 400/720 | 0 | 0 | 89 040/416 | 1 680/0 | 0 | 0 |
| `K=4`, `n=10` | 624 128/81 568 | 233 024/12 064 | 15 152/4 336 | 0 | 0 | 545 856/3 296 | 10 816/0 | 0 | 0 |
| `K=4`, `n=11` | 3 416 256/396 664 | 1 295 728/68 192 | 83 992/23 016 | 256/0 | 64/0 | 3 040 200/20 608 | 60 976/0 | 256/0 | 64/0 |
| `K=4`, `n=12` | 17 541 760/1 831 712 | 6 761 680/352 720 | 428 224/112 752 | 5 120/0 | 1 216/0 | 15 822 400/112 352 | 315 472/0 | 5 120/0 | 1 216/0 |
| `K=4`, `n=13` | 85 921 088/8 155 456 | 33 662 184/1 717 904 | 2 061 696/523 152 | 59 904/0 | 13 440/0 | 78 327 392/561 760 | 1 538 544/0 | 59 904/0 | 13 440/0 |
| `K=5`, `n=13` | 5 632/4 224 | 1 792/896 | 256/256 | 0 | 0 | 1 408/0 | 0 | 0† | 0† |
| `K=5`, `n=14` | 129 024/94 208 | 39 936/19 584 | 6 400/6 144 | 0 | 0 | 35 328/512 | 256/0 | 0† | 0† |
| `K=5`, `n=15` | 1 683 968/1 191 424 | 509 440/243 456 | 89 600/82 176 | 0 | 0 | 512 512/19 968 | 7 936/**512** | 0† | 0† |
| `K=5`, `n=16` | 16 436 224/11 251 712 | 4 877 824/2 266 624 | 922 624/810 496 | 0 | 0 | 5 540 864/356 352 | 124 416/**12 288** | 0† | 0† |
| Bing `K=5` | 286/55 | 123/10 | 8/3 | 49/0 | 0 | 231/0 | 5/0 | 49/0 | 0 |
| Bing `K=6` | 4 060/298 (472 u) | 1 823/67 (178 u) | 176/18 (61 u) | 486/6 (48 u) | 43/1 (8 u) | 3 314/24 | 97/0 | 432/0 | 34/0 |

How to read the table:
* Entries are `instances/failures`; "u" marks cases left undecided at the `2·10⁶` node limit.
* † X has no instances at `K = 5`, `n ≤ 16`, so C + X is empty there. The C + X classes were added to the program after the `K = 5` runs; the X column shows the emptiness directly.
* Bing `K = 8` (whole chain only): 168 instances with no hypothesis, 2 failures, 166 undecided. None of the other classes has an instance there.
* **Where the failures sit.** The Bing `K = 6` failures under X and under W + S + X all violate C; the first is at the 16-link subchain with levels `0,1,2,1,2,3,2,1,2,1,0,1,2,1,2,3`. The failures under W + S + C at `K = 5` (512 at `n = 15`, 12 288 at `n = 16`) all lack X, since X has no instances there. §1.3 is one of them.

**Status: refuted.** The lemma fails for two reasons, and neither is excluded by any hypothesis derivable in the setting of `covering_step`:
* the ends are not in a common window (C);
* the arm `[p, c]` is too short (X).

The strengthened statement "crookedness + C + X ⇒ `ModelEndTime`" had no failure in the search. It is recorded as a comment in `Recon87End.lean` and is not proved.

## 5. Item 4 — `theorem3_end`: **open; no failure found**

**Statement decided (class `T3END`).** This is the decision procedure of batch 86, re-implemented in `census-batch87-model.c`.
* For every basepoint `i` there must be a three-link block map with `β i = 0` and the end-link clause.
* **The clause.** If link `0` (resp. `n − 1`) meets coarse level `0`, every member of its block has `ρ ≤ 2`. If it meets level `K − 1`, every member has `σ ≥ K − 3`. Meetings are by the forced-meeting table.
* **What changed from batch 86.**
  * When a search hits its node limit, it is retried once with the other arm swept first.
  * The enumerator prunes crookedness on prefixes.
  * Its counts at `K = 4, n = 6 … 10` equal batch 86's (32, 352, 2 528, 14 880, 78 016).

| range | sequences / subchains | instances | failures | undecided |
|---|---|---|---|---|
| `K = 4`, `n = 6 … 10` | 95 808 | 936 960 | 0 | 0 |
| `K = 4`, `n = 11, 12, 13` | 379 584 / 1 754 176 / 7 811 008 | 4 175 424 / 21 050 112 / 101 543 104 | 0 | 0 |
| `K = 5`, `n = 13, 14, 15` | 512 / 10 752 / 129 536 | 6 656 / 150 528 / 1 943 040 | 0 | 0 |
| `K = 5`, `n = 16` | 1 174 016 | 18 784 256 | 0 | 0 |
| Bing `K = 5`, `6`, `7` (as in batch 86: subchains with an end link on an extreme level, interior basepoints) | — | 11 / 674 / 28 006 | 0 | 0 |

* Five coarse links first appear at `n = 13` (512 sequences), the least length allowed by `minimality`. They were searched exhaustively through `n = 16`.
* The 1 493 Bing `K = 7` cases that batch 86 left undecided are all decided now, and none fails.
* `theorem3` itself (without the clause) was re-checked on every case where the clause search failed. There were no such cases.

**Status: open.**
* No refutation was found, so there is nothing to record in Lean.
* The general clause is still the end-time question: control of the block of an end link.
* Item 3 did not produce a usable end-time lemma. Its refutations concern *two* ends sharing the maximal time, which `theorem3_end` does not ask for.

## 6. What the evidence says

* **Three-link blocks remove the batch-86 obstruction.**
  * `coveringStep_of_folds₃` makes the three-link fold sufficient for `covering_step`.
  * In the model the three-link fold fails only in the search's failures. All of them put `Q'`'s link next to the `W`-links, which S2 excludes at deep levels.
  * The census has no failure under S2. At four and five coarse links, though, S2 makes the `W`-part trivial.
* **The end-time lemma, as commissioned, is false.**
  * Placing both arm ends at the maximal time puts them in one block. That needs the last `W`-link to be near `R` (C), and an arm beyond `P'` long enough to carry the times (X).
  * Neither follows from irreducibility.
  * So the route "end-time lemma ⇒ `covering_step`" does not go through in this form.
* **What remains.**
  * The remaining candidate is the item-2 statement under S2 (`Recon87Model.lean`, conjecture). It is the covering fold itself, with `Q'`'s link far from `W`.
  * Its non-degenerate instances begin at six coarse links. Only the Bing chains reach them, and some Bing `K = 7` and `K = 8` cases remain undecided at the node limits used.

## 6a. Lean-checked part of the census

The small end of the census was redone in Lean (`HPC/Fold/Census87.lean`, `HPC/Fold/Census87Checks.lean`).
* `gen K n` lists coarse-interval sequences. `mem_gen` / `ofFn_mem_gen` prove that every crooked sequence with `0 ≤ ρ` and `σ < K` is listed, so the enumeration is complete.
* A search proposes a time function. Only its output is used, and only after a decidable certificate (`CertT3`, `CertF3`) accepts it. `CertT3.toModel` / `CertF3.toModel` then build the block map through `IsSchedule.exists_blockMap`.
* `modelT3End_of_check` and `fold3_of_check` turn a successful finite check over `gen K n` into the model statements for every crooked sequence.
* The checks for `K = 4`, `1 ≤ n ≤ 7` are decided by `native_decide`. This gives:
  * `modelT3End_census_K4`: `ModelT3End ρ σ 4 i` for every crooked sequence of at most seven links over four coarse links, at every basepoint `i`.
  * `fold3_census_K4`: the three-link covering fold under the window property and S2, for the same sequences.
* The larger C runs (`K = 4`, `n` up to 13; `K = 5`; Bing chains) are **not** checked in Lean. They remain C-only evidence. A test run of `K = 4, n = 8` together with `K = 5, n = 7` passed but took about 20 minutes, so it was not included in the build.

## 7. Deliverables

1. Lean: `IsCoveringFold₃`, `IsCoveringFold.toFold₃`, `coveringStep_of_folds₃` (`Recon87.lean`); `ModelCoveringFold₃`, `levelGap`, `ModelFar`, `block₃_val_ne`, `model_covering_fold₃_recon86`, `model_covering_fold₃_refuted` (`Recon87Model.lean`); `ModelEndTime`, `ModelEndTime.ends_close`, `model_end_time_refuted`, `model_end_time_refuted'` (`Recon87End.lean`). `covering_step` and `theorem3_end` were not reached.
2. `axioms-batch87.txt`.
3. Lean census: `Census87.lean`, `Census87Checks.lean` (`modelT3End_census_K4`, `fold3_census_K4`; uses `native_decide`).
4. C census: `census-batch87-model.c`, `census-batch87-common.h`; logs `census-batch87-k4.log`, `census-batch87-k5.log`, `census-batch87-bing.log`.
