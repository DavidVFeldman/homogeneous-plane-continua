# Report: batch 56 — the far witness, the ceiling residues, and the seam under the induction

## 0. The refutation, first

**Bing's seam under the induction's own hypothesis: the prediction fails, and something else
breaks.** Question 3 asks for the construction of p. 733 run with `H` a width-two consolidation of
the inner chain **with respect to `E(2, m − 1)`** — the chain the induction is on — with the end
links of `D(h, k)` that meet `e₁` or `e_m` attached at the regroup, and predicts *a seam of width
three when the block containing the inner end link reaches one link past the extreme*.

`seam-batch56.py` (log `seam-batch56.log`) carries that out. **No seam of width three occurs**, in
either model:

| pass | basepoints | `h_u` inside the end links | `F` a chain | `d_i` first only | blocks of `F` of width ≥ 3 | seam widths |
|---|---|---|---|---|---|---|
| thin: `bing 0 4`, `0 5`, `0 6` | 84 | **0** | **59** | **25** | 0 | [2] |
| general: nine single shavings of `bing 0 6`, `bing 0 7` | 820 | **0** | **357** | **463** | 0 | [2] |

The reason the seam stays at two is that the regroup splits `h_u`'s links among the level groups,
so the group that receives them is the group of `e₁ ∪ e₂`, of width two, whatever `h_u` spans. What
the induction's own hypothesis does break is elsewhere, and it breaks harder than a wide seam
would:

* `h_u` is **never** inside `e₁ ∪ e₂` (0 of 84 in the thin model, 0 of 820 in the general one),
  where batch 55 — with `H` consolidated with respect to `E` itself — had it inside at all 84;
* `F` stops being a chain at **25 of 84** thin basepoints and at **463 of 820** general ones;
* `d_i` stops being in the first link of `F` only at **59 of 84** and at **357 of 820**.

The last of these has a clean cause, visible in the table: with the induction's `H`, the block
containing the inner end link is very often the block containing `d_i` itself (`u = 1`), so the
head `H(1, u − 1)` of `F` is **empty** and `F` is nothing but the level groups. A least
consolidation with a non-empty head (`u ≥ 2`) exists at only 25 of the 84 thin basepoints — none at
`bing 0 4` or `bing 0 5` — and where it exists, `F` is then a chain at none of them. So the choice
the construction needs is not available at most basepoints once `H` is the object Bing's induction
supplies.

Batch 55's table was therefore a statement about a stronger `H` than the induction has, as the
commission says, and correcting the object does not produce the predicted width-three seam: it
produces an empty head and a broken chain. The repair recorded for completeness — keep `h_u` as a
block of `F` — restores a chain at 54 of the 84 thin basepoints and 570 of the 820 general ones,
with seams of width 1 (thin) and 1 or 2 (general).

**No §1 target is refuted**, and question 2's targeted construction provably does not exist: see
§2.2.

---

## 1. The targets

Three of them are now theorems, and with them the branch `L + 4` of span nine is complete.

| target | file | status |
|---|---|---|
| `cross_valley_profile` | `HPC/Fold/Mixed.lean` | **proved** (was a `sorry` since batch 48) |
| `cross_ceil_sentence` | `HPC/Fold/CrossCeil.lean` | **proved** (was a `sorry` since batch 52) |
| `unserved_three_walks` | `HPC/Fold/Mixed.lean` | **proved** (was a `sorry` since batch 49) |
| `s3_span_nine_mid4` | `HPC/Fold/Mixed.lean` | **complete and `sorry`-free** as a consequence |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | open (the branch `L + 5`) |
| `s3_span_nine`, `s3_general`, `theorem3` | `HPC/Fold/General.lean`, `HPC/Fold/Open.lean` | open |

The whole of what closed the three is one observation, and it is the answer to question 1.

### The observation

Both crossings were reduced, in batches 50 and 53, to configurations local to the basepoint —
`ValleyResidual` (the sequence stands at `L + 2` two or three steps to one side) and the two
ceiling residues — because the clause was read through the one-arm predicates `CrookUp`,
`CrookDown`, which see `ρ` alone, and the only timing available for what they return was the
Lipschitz bound and the climb bounds of batch 42.

Read the crookedness clause of the faithful model directly, between the descent and the ascent and
at the two arms' **own levels**, and the two links it returns carry *intervals* at named levels.
Bing's Theorem 7 then applies to them through `minGap` (`HPC/Fold/Minimal.lean`), which counts
links between two intervals meeting levels `d` apart: `z 3 − 1 = 5` steps for three levels,
`z 4 − 1 = 12` for four, `z 5 − 1 = 29` for five. The new lemma is `ivSep`
(`HPC/Fold/ValleyFar.lean`), the timing law in separation form, with `ivSep3`, `ivSep4`, `ivSep5`
for the three cases used.

**The valley crossing** (`cross_valley_low_fwd_far`, `cross_valley_low_bwd_far`,
`HPC/Fold/ValleyFar.lean`). Let `X` be the arm failing `Leg3Valley`, at a descent `t` with
`ρ t ≤ L + 1`, and `Y` the other arm, at an ascent `s` with `L + 7 ≤ ρ s`. The clause at
`{s, t}` with `h = ρ s`, `k = ρ t` returns a link whose interval contains a level at `L + 6` or
above and one whose interval contains a level at `L + 2` or below.

* The high link is five levels from the descent, so `29` steps from it: in particular it is past
  the window in which the failure of `Leg3Valley` says nothing, so the failure applies to it and
  puts it within **two** steps of the basepoint.
* The low link is four levels from the high one, so **twelve** steps from it, hence at least ten
  steps past the basepoint.

Ten is more than the four the V-criterion asks, so the witness is always there:
`cross_valley_vee_pair` proves the conclusion of the work item outright, and `ValleyResidual` is
not an obstruction at all.

**The ceiling crossing** (`HPC/Fold/CeilFar.lean`). The same two bounds, one level higher.

* `CeilHighResidual` asks the sequence to stand at `L + 7` or above exactly four steps from a
  basepoint at `L + 4`; three levels need five steps. So it never holds:
  `no_ceilHighResidual` — the census's count of 0 is a theorem.
* `CeilPeakResidual` does occur (the census finds 292 824 instances), but it is no longer an
  obstruction: read at the ascent's own level the clause returns a peak whose interval reaches
  `L + 7`, and such a link is **five** steps from the basepoint, where the Lipschitz bound allowed
  three. `ceil_cross_peak_fwd_far` and `ceil_cross_peak_bwd_far` therefore have no residual
  disjunct, and neither do `ceil_cross_high_fwd_far`, `ceil_cross_high_bwd_far`, where the peak
  reaches `L + 8` and so is **twelve** steps out.

`ceilCrossGap_far` assembles the two clauses and `cross_ceil_sentence_far` is the work item.

**The three walks** (`HPC/Fold/Unserved.lean`). With both crossings available the case analysis of
`unserved_three_walks_or_cross` closes: an arm failing `Valley4` fails `Leg3Valley`, so the valley
crossing would serve the pair with the V-walk, contrary to the hypothesis; if an arm fails
`Leg3Ceil` the ceiling crossing gives both arms the sentence of `w₅`; otherwise both arms satisfy
`Valley4` and `Leg3Ceil`, which is the exact criterion of `w₃`.

### What moved, and what did not

`HPC/Fold/CrossValley.lean`, `HPC/Fold/CeilCross.lean`, `HPC/Fold/CeilNarrow.lean` and
`HPC/Fold/ValleyNarrow.lean` are untouched: the dichotomies and the residues they name stand as
they were, and the new files sit beside them. Three import lines changed so that the new material
can be quoted where the targets stand — `HPC/Fold/CeilArm.lean` now imports the files it actually
uses instead of `HPC/Fold/CrossCeil.lean` (it used nothing from it), `HPC/Fold/CrossCeil.lean`
imports `HPC/Fold/CeilFar.lean`, and `HPC/Fold/Mixed.lean` imports `HPC/Fold/ValleyFar.lean` and
`HPC/Fold/Unserved.lean`. No statement was weakened; the three targets are quoted verbatim and
proved.

---

## 2. The questions

### 2.1 Question 1 — is the far witness a consequence of the timing law?

**Yes.** That is §1 above: applied between `X`'s descent to `L + 1` and `Y`'s ascent to `L + 7`,
the clause returns a time at `L + 6` and a later time at `L + 2`, and the timing laws place the
returned `L + 2` at index **twelve** or later on `Y` — three times the four the criterion asks. The
two subcases the commission names are exactly the two bounds that close them:

* *the returned `L + 6` on `X`'s first two steps*: the returned high link is `z 5 − 1 = 29` steps
  from the descent, so the failure of `Leg3Valley` does apply to it, and all it yields is that the
  link is within two steps of the basepoint — which is all the argument needs;
* *`X`'s descent late*: the same bound; no hypothesis about where the descent is, is used.

Neither the Lipschitz hypothesis nor the value at the basepoint is needed in the two far lemmas.

The census confirms the bound and shows it is **sharp**: over 1 235 506 basepoints of the branch
`L + 4`, at every one of the 246 308 with a valley failure the witness at arm index twelve or later
exists (0 failures), and the least witness index seen anywhere in the corpus is exactly **12**.
Likewise `Valley5` with its index bound raised from 4 to 5 and `TopW5` with its raised from 4 to 12
fail nowhere.

### 2.2 Question 2 — is the witness a property of the model or of the corpus?

**Of the model, and the targeted construction the question asks for cannot exist.** A general pair
in `ValleyResidual` whose arm `Y` has no time at `L + 2` or below at index four or later before its
ascent would refute `cross_valley_profile`; `cross_valley_profile` is now a theorem, so no such
pair exists in the faithful model — the timing law excludes it, which is question 1 answered from
the other side. The census agrees: 312 366 pairs of `ValleyResidual`, 0 failures.

### 2.3 Question 3 — the seam under the induction's hypothesis

See §0. The prediction is refuted; the construction breaks in a different place.

### 2.4 Question 4 — four turns at `L + 5`

**Each walk of the table has a criterion, and three of them cover the whole residue of the
corpus.** The census measures the branch `L + 5` over the same corpus: 1 464 514 basepoints, of
which the three reflected three-turn walks serve all but **917**. Every one of the 917 is served by
a walk of the window of the wide four-leg engine `foldsOnto_leg4W` (`HPC/Fold/Leg4Wide.lean`) —
`by none 0` — and the greedy cover of the 917 needs **three** walks:

| walk | engine parameters | covers (greedily) | serves in all |
|---|---|---|---|
| `L+4 → L+7 → L+1 → L+8 → L+1` | `leg4Walk L (L+9) (L+7) (L+1) (L+5)` | 701 | 701 |
| `L+4 → L+7 → L+2 → L+8 → L+1` | `leg4Walk L (L+9) (L+7) (L+2) (L+5)` | 116 | 611 |
| `L+6 → L+3 → L+7 → L+1 → L+8` | reflection of `leg4Walk L (L+9) (L+6) (L+2) (L+4)` | 100 | 528 |

All three lie inside the engine's window, so each has a criterion of the shape of
`foldsOnto_walk5738`, and the three are proved in the new file `HPC/Fold/CoverL5.lean`:
`foldsOnto_walk47181`, `foldsOnto_walk47281`, `foldsOnto_walk63718` — the last through
`foldsOnto_leg4W_refl`, with the three announcements read on the arm as ascents to `L + 8`, ascents
to `L + 9` and descents to `L + 1`.

Sixteen walks of the family serve some basepoint of the residue; the full list, with counts, is in
`census-batch56.log`. What this does **not** settle is the branch: covering the residue of a corpus
is not covering the branch, and the rule choosing between the three walks at a given pair is not
proved. The cover is a measurement; the three criteria are theorems.

---

## 3. The census

`census-batch56.c`, log `census-batch56.log`. Same generators and same audit protocol as batch 55
(the generators, `IsCrookedIvF`, the `FoldsOnto` dynamic program of `HPC/Fold/Decide.lean` and the
walk predicates are carried over unchanged); 4 566 faithful pairs, 6 421 438 links, 47 458 non-thin.

| corpus | pairs | branch-`L+4` basepoints |
|---|---|---|
| thin chains | 2 | 364 |
| single shavings | 576 | 105 004 |
| single fills | 576 | 104 832 |
| random mixtures (rate 1/3) | 80 | 16 610 |
| heavy mixtures (rate 1/2, and the total mixture) | 82 | 18 863 |
| faithful perturbation walks | 9 | 1 652 |
| chains outside Bing's family and concatenations | 3 241 | 988 181 |

Totals, over 1 235 506 basepoints of the branch `L + 4`:

* valley failures 246 308; pairs not folding onto the V-walk: **0**;
* the witness at arm index 12 or later: fails **0** times; least index seen **12**;
* ceiling failures 57 245, of them missing the Λ-walk 589; the gap (`TopW5` on the failing arm,
  `Valley5` on the other) fails **0** times; `Valley5` at index 5 fails **0**; `TopW5` at index 12
  fails **0**;
* residues: `ValleyResidual` 312 366, `CeilPeakResidual` 292 824, `CeilHighResidual` **0**;
* unserved pairs 366 897, served by none of `w₃`, `w₄`, `w₅`: **0**.

Branch `L + 5`: 1 464 514 basepoints, 1 463 597 served by a reflected walk, residue 917, of which
917 are served by the four-leg family and **0** by none.

---

## 4. Deliverables and audit

1. **Proved, `sorry`-free.** New files `HPC/Fold/ValleyFar.lean` (the timing law in separation form
   and the valley crossing), `HPC/Fold/CeilFar.lean` (the two ceiling halves with no residue),
   `HPC/Fold/Unserved.lean` (the three walks) and `HPC/Fold/CoverL5.lean` (the three four-leg
   walks); the three targets in `HPC/Fold/Mixed.lean` and `HPC/Fold/CrossCeil.lean` are now quoted
   proofs. `lake build HPC` is clean; every new file is in `HPC.lean`; no `sorry`, no
   `native_decide`, no new `axiom`, no `@[implemented_by]`.

   ```
   'HPC.Fold.cross_valley_vee_pair'      depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.cross_valley_profile'       depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.cross_ceil_sentence'        depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.cross_ceil_sentence_far'    depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.unserved_three_walks'       depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.unserved_three_walks_far'   depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.no_ceilHighResidual'        depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.s3_span_nine_mid4'          depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.ivSep'                      depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.foldsOnto_walk47181'        depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.foldsOnto_walk47281'        depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.foldsOnto_walk63718'        depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The remaining `sorry`s of the fold route are `s3_span_nine_mid5` (`HPC/Fold/Mixed.lean`),
   `s3_span_nine` and `s3_general` (`HPC/Fold/General.lean`) and `theorem3` (`HPC/Fold/Open.lean`),
   as before; the three closed this batch are no longer among them.

2. **The census** over the general model, under the audit protocol of batch 55: `census-batch56.c`,
   log `census-batch56.log`. Every predicate is evaluated by its own definition; the three
   strengthened criteria (the witness at index 12, `Valley5` at index 5, `TopW5` at index 12) are
   the definitions with the index bound raised to the value the timing law gives, and are reported
   as such.

3. **The §2.3 tables** above, produced by `seam-batch56.py` (log `seam-batch56.log`). The general
   pass is run on the first six single shavings of `bing 0 6` and the first three of `bing 0 7`;
   the search for consolidations is quadratic in the length of the chain, and the bound is
   recorded here.

4. **This report**, in the commission's order.
