# Report: batch 74 — after span nine

The commission read is `COMMISSION-batch74.md` (copy `COMMISSION.md`), on top of the batch-73
delivery. `lake build` is clean on the whole project; the repository's `sorry`s are still exactly
`s3_general` (`HPC/Fold/General.lean:162`) and `theorem3` (`HPC/Fold/Open.lean:47`) — this batch
adds none and closes neither.

## 0. The counterexample, first

**No basepoint of any span searched is served by no walk at all.** At spans nine, ten, eleven and
twelve, every distinct basepoint of the corpus is served, on both arms, by some walk of at most
five legs. So the counterexample the commission asks to be reported first — a basepoint at span ten
served by no walk of any family searched — does not exist in this corpus; at span ten every
basepoint is served by a walk of at most **four** legs.

**What is refuted is a recorded census statement, one span higher.** `HPC/Fold/Span.lean` records,
from REPORT-batch26.md, that "the least itinerary at a basepoint always had `⌊span/2⌋ − 1` turning
targets or fewer, exhaustively for spans four to twelve". At span eleven this is false.
`census-batch74.c` finds **19 distinct basepoints of span eleven whose least itinerary has five
turning targets**, where `⌊11/2⌋ − 1 = 4`. The sentence is kept where it stands and a correction is
recorded beside it; the rest of the sentence is not contradicted (the bound holds at spans nine, ten
and twelve in the same census, with maxima 3, 4 and 5, and no basepoint at which `S3` fails was
found).

*The witness, and its definition audit.* The first such basepoint is written out in full in
`witness-batch74-span11.txt`: a faithful pair of **5815 links** (a window of `bing 0 12`, shaved and
filled, so `σ ≠ ρ`), band exactly `[0, 11]`, basepoint `946` at level `5`, whole arms of 4869 and
947 links. `check74.py` (log `check74.log`) re-checks it from scratch, importing nothing from the
census and writing every predicate out again from its Lean definition — `IsCrookedIvF` of
`HPC/Fold/Faithful.lean` (`le`, `width`, `adj`, and the crookedness clause with interval triggers),
`armG`/`armT`, and `FoldsOnto` decided by a *second* procedure (propagation of the reachable set of
walk times as a set of integers, against the census's 128-bit mask). It confirms, independently:

* the pair is faithful and its band is `[0, 11]`;
* of the 8219 walks of at most four legs based within one of the basepoint's level, **not one**
  folds both arms;
* the five-leg walk `4 → 7 → 2 → 8 → 1 → 10` folds both arms.

That walk is the span-nine four-leg walk of the engine (`leg4Walk` at `K = 7, M = 2, P = 5`, i.e.
`4 → 7 → 2 → 8 → 1`) with **one more leg** appended, a final ascent to `H − 1`.

*The same thing at span twelve, on Bing's own chain, thin.* At span twelve the census finds 962
five-leg basepoints, and the first one it writes out (`witness-batch74-span12.txt`) needs no window
and no shaving: it is `bing 0 12` itself, all 13 861 links, `σ = ρ`, at basepoint `2027`, again at
level `L+5`, with whole arms of 11 834 and 2028 links. `check74.py` (log `check74-span12.log`)
confirms it independently: the chain is faithful, none of the 12 014 walks of at most four legs based
within one of level 5 folds both arms, and the five-leg walk `4 → 7 → 2 → 9 → 1 → 11` does. So the
failure of the four-leg family is not an artefact of the corpus's shavings, fillings or windows.

## 1. Targets

`s3_general` is not proved, and `theorem3` is therefore still open. The batch is the reconnaissance
and packaging the commission describes; what it delivers towards the target is §2.1 (the milestone
statements, proved) and §2.3 (the census that says where the four-leg engine stops).

## 2.1 Packaging what is proved

New file `HPC/Fold/Target74.lean`, `sorry`-free, on `[propext, Classical.choice, Quot.sound]`
(`axioms-batch74.txt`); it is imported by the root `HPC.lean`. Nothing else in the repository is
touched except the correction note in the docstring of `HPC/Fold/Span.lean` recorded in §0.

* `S3SpanLeNine` / **`s3_span_le_nine`** — `S3` with the band restricted to `H ≤ L + 9`. As the
  commission says, `S3`'s two attainment hypotheses (`∃ t, ρ t = L`, `∃ t, ρ t = H`) are not needed:
  they are *not carried*, so what is proved is stronger than "`S3` restricted".

* **`theorem3_ten_links`** — Bing 1948 Theorem 3, block reading, three-link form, **unconditional**,
  for a chain `D` of at most ten links: if `E` is crooked in `D` (1948 sense) and `D` has `k ≤ 10`
  links, then `E` has a block consolidation in which the chosen link `i` opens the first block and
  every block lies in three consecutive links of `D`.

**The bound is ten, and the reduction loses nothing.** `theorem3_of_S3` runs the fold on
`ρ t = (minIdx t : ℤ)`, the least index of `D` whose link contains `E.link t`; `minIdx t : Fin k`,
so `0 ≤ ρ ≤ k − 1` and the band of the pair has `H − L ≤ k − 1`. With `k ≤ 10` that is exactly
`H ≤ L + 9`, the hypothesis of `s3_span_nine`; and the degenerate case `H ≤ L + 2` never reaches the
fold (`exists_blocks_first_of_range_le_two`). So ten links is the true bound of the span-nine
theorem read back through the reduction: no level is lost, and eleven links would need span ten.

Both statements, and `s3_span_nine` itself, print `[propext, Classical.choice, Quot.sound]`; no
`native_decide`, no new axioms, no `sorry`.

## 2.2 What the downstream uses need

**Answer: arbitrary.** Asked as a question about the repository's own reductions, the facts are
these.

1. The repository contains **no** reduction of Theorem 4 to Theorem 3. The only Theorem-4 statement
   in it is `Chain.exists_blocks_first_last` (`HPC/Chains/Consolidation.lean:574`), the easy case,
   and it does not call Theorem 3 at all: it is proved from `monoBlocks_spec`, and, as its docstring
   says, crookedness is not used. Nothing else in the repository refers to it. So the reduction of
   the hard case is read here from the statements, not from Lean.

2. Theorem 3's own statement quantifies over `D : Chain X k` with no bound on `k`
   (`theorem3_of_S3`, `HPC/Fold/Span.lean`), and its conclusion names links of *that same* `D`:
   every block lies in `D.unionRange j 3`. The conclusion is therefore at the resolution of the
   chain that is passed.

3. Theorem 1, as formalised (`isCrookedIn'_of_isConsolidationOf`, `HPC/Chains/Basic.lean:276`),
   preserves crookedness when the **target** chain is coarsened: if `F` is crooked in `E` and `D` is
   a consolidation of `E`, then `F` is crooked in `D`. So one may indeed replace `D` by a
   consolidation `D'` of bounded length and keep the hypothesis of Theorem 3 — but the conclusion
   one gets back is about `D'`. A block inside three consecutive links of `D'` is inside a union of
   three *blocks* of `D`, which is weaker than "three consecutive links of `D`" by exactly the
   coarsening factor, and Theorem 4's conclusion (two adjacent links of `D`, with prescribed first
   and last blocks) is *finer* than Theorem 3's conclusion at `D`. Coarsening therefore cannot
   supply it: it moves in the wrong direction.

4. The one route by which a bounded chain could enter is windowing rather than coarsening:
   `IsCrookedIn'.restrict` (`HPC/Chains/Consolidation.lean:313`) gives crookedness in a subchain
   `D.sub a b`, which can be taken of ten links. But its hypothesis is `E.Refines (D.sub a b)` —
   the *whole* of `E` must lie in the window — so it applies only when the pair already has span at
   most nine. Using it in general would need `E` cut to the part lying over the window and the block
   maps of the windows glued; the repository has no such gluing (`foldsFrom_split`,
   `HPC/Fold/Span.lean`, glues two halves of one **arm**, at a split index, not two windows of `D`),
   and Theorem 4's prescribed first and last blocks are global conditions across all windows.

5. Finally, the quantity the fold actually consumes is the **span**, not the length: `theorem3_of_S3`
   uses only `H − L ≤ k − 1`. The chains of any defining sequence of a pseudo-arc have mesh tending
   to zero, so their link counts — and, in the repository's own corpus, their spans: `bing 0 N` has
   span `N` — are unbounded.

So the chain `D` that Theorem 4's hard case passes to Theorem 3 is arbitrary, and `theorem3_ten_links`
does not suffice for it. This settles the commission's question in the direction it names:
`s3_general` is needed for the classification, and not only for Bing's statement.

## 2.3 Reconnaissance at spans ten, eleven, twelve

`census-batch74.c`; logs `census-batch74-span9.log`, `-span10.log`, `-span11.log`, `-span12.log`.
Span nine is swept too, with the same code and the same protocol, so that every number at ten,
eleven and twelve is read against the span whose answer is known.

**What a walk is.** A *walk with k legs* based at a basepoint of level `p` is a start
`c0 ∈ {p−1, p, p+1} ∩ [L, H]` followed by `k` turning targets in `[L+1, H−1]`, the directions
alternating, each leg a run of unit steps — the itinerary of census-batch26.py, and exactly the
shape `FoldsOnto` consumes. The engine's four-leg family (`leg4Walk L H K M P`, i.e.
`P−1 → K → M → H−1 → L+1`) is the sub-family of the `k = 4` walks whose last two targets are pinned,
so "a walk of the four-leg family serves both arms" is reported as "the least number of legs is at
most four", and the pinned sub-family is measured separately alongside.

**The corpus** is the batch-70 corpus builder with the band widened from `[0,9]` to `[0,S]`: the
Bing chains `bpath 0 S` and `bpath S 0`; windows of span exactly `S`, at grid and at random offsets,
of `bing 0 N` for `N = S+1 … S+4`; the `vpath` chains outside Bing's family, in four parameter
settings and both orientations; random concatenations of Bing blocks and windows of them; and for
every base sequence the thin pair, single shavings of peaks, single fillings of valleys, random
mixtures at rates 1/3 and 1/2, and the total mixture. Each pair is tested for `IsCrookedIvF` in its
own right. **This is a census over pairs and over whole arms, not over truncated arms: no
arm-length bound applies** — a basepoint is scored on its two whole arms, from the basepoint to each
end of the pair — and the arm lengths seen are reported below. The only length cap is on the *pair*:
3000 links at spans nine and ten, 6000 at eleven, 14000 at twelve; a window longer than the cap is
truncated, and then kept only if its band is still exactly `[0, S]`, so a truncated window is a
shorter faithful pair, scored on its own whole arms. Basepoints are de-duplicated by their pair of
whole arms and each distinct configuration is scored once.

**Definition audit.** `IsCrookedIvF`, `armG`, `armT` and `FoldsOnto` are each evaluated by their own
definition; `FoldsOnto` is decided twice, by a 128-bit mask propagation and by an array propagation,
and the two are compared on 3000 samples at spans nine, ten and eleven with **0 disagreements**
(0 samples at span twelve, where every arm of the sample is longer than the audit's length window;
the span-twelve witness is instead audited in full, by a third implementation, in `check74.py`). No
criterion of the four-leg engine and no landmark sentence is used anywhere in the census.

### The census

| span | distinct basepoints | least 1 | 2 | 3 | 4 | 5 legs | none of ≤ 5 | arms |
|---|---|---|---|---|---|---|---|---|
| 9  | 924 827   | 126 599 | 670 253 | 127 931 | 44      | 0   | 0 | 1 – 3000 |
| 10 | 788 692   | 59 912  | 469 495 | 256 468 | 2 817   | 0   | 0 | 1 – 3000 |
| 11 | 1 028 908 | 40 100  | 447 596 | 519 364 | 21 829  | 19  | 0 | 1 – 6000 |
| 12 | 1 590 808 | 30 905  | 472 563 | 960 311 | 126 067 | 962 | 0 | 1 – 14000 |

**Is there a walk of the four-leg family at every basepoint?**

* **Span ten: yes.** All 788 692 distinct basepoints are served by a walk of at most four legs; the
  maximum is exactly four, attained at 2817 basepoints — 2712 of them at level `L+5` and 105 at
  level `L+6`.
* **Span eleven: no.** 19 basepoints need five legs (15 at level `L+5`, 4 at level `L+7`); the other
  1 028 889 are served by at most four, 21 829 of them needing exactly four (10 950 at `L+5`,
  10 726 at `L+6`, 153 at `L+7`).
* **Span twelve: no.** 962 need five legs (450 at `L+5`, 49 at `L+6`, 460 at `L+7`, 3 at `L+8`);
  126 067 need exactly four; the rest fewer.
* At no span does any basepoint need more than five legs within the search bound (`k ≤ 5`; the
  five-leg families searched are 75 828 walks at span ten, 145 332 at eleven, 261 316 at twelve).

The pinned sub-family of the engine — `leg4Walk` and its reflection, 120 walks at span ten, 184 at
eleven, 266 at twelve — already fails more often than the four-leg family as a whole: it serves
783 375 of 788 692 at span ten, 1 025 632 of 1 028 908 at eleven, 1 587 675 of 1 590 808 at twelve.
The gap between the two is what a new *choice rule* would have to cover even where four legs are
still enough.

**Is the structure of span nine visible at span ten?** Measured as a greedy cover, level by level:
the fewest walks of at most four legs that, between them, serve every sampled basepoint of that
level (250 distinct basepoints per level, sampled by reservoir over all the level's distinct
basepoints; a greedy cover, so each count is an upper bound on the least number of walks).

| span | levels with a basepoint | levels needing more than one walk ("branches") | walks in the cover |
|---|---|---|---|
| 9  | 10 | 4 — levels 3, 4, 5, 6 | 23 |
| 10 | 11 | 5 — levels 3, 4, 5, 6, 7 | 29 |
| 11 | 12 | 6 — levels 3, 4, 5, 6, 7, 8 | 42 |
| 12 | 13 | 7 — levels 3 … 9 | 61 |

So the shape of span nine is visible at span ten, one level wider and one walk deeper:

* the extreme levels (`L`, `L+1`, `L+2` and `H−2`, `H−1`, `H`) are each served by a single walk at
  every span, as at span nine;
* the middle levels carry the branches, and their number grows by one per span: 4 at nine, 5 at ten,
  6 at eleven, 7 at twelve — that is, `span − 5`;
* at span nine the deepest branch is `L+5`, needing 5 walks in the cover and 4 legs at its hardest
  basepoints; at span ten it is again `L+5`, needing 6 walks, with `L+6` now also carrying four-leg
  basepoints. The trichotomy-plus-two shape of the span-nine branch (three walks, and a fifth and
  sixth for the crossings) is reproduced at span ten as a cover of six walks at `L+5` and five at
  `L+6`;
* the two walks the cover picks first at level `L+5` have, at both spans, the engine's four-leg
  shape `P−1 → K → M → H−1 → L+1` with `K = 7`, once directly and once reflected, with only the
  ceiling target following the band: `6 → 2 → 7 → 1 → 8` and `4 → 7 → 3 → 8 → 1` at span nine,
  `4 → 7 → 2 → 9 → 1` and `6 → 2 → 7 → 1 → 9` at span ten.

The answer to the question batch 41 asked one span down is therefore: at span ten the span-by-span
route still converges, with the same engine and one more walk per branch; at span eleven it does
not, because the family the engine is built on — four legs — is no longer sufficient, and the walk
that is needed is a five-leg extension of the span-nine walk.

## 2.4 The parametric core

`parametric-batch74.py`, log `parametric-batch74.log`. A statement about the repository.

**A correction of the arithmetic first.** The commission's §0 records "471 declarations in the
dependency graph, 304 pinning a level offset, 161 parametric". The inventory's second list is headed
*Span-generic (167)* and contains 167 bullets; 304 + 167 = 471. The parametric count is 167, not
161. (Of the 471 names, 470 are found by a source scan; the one that is not is `κ`, a notation
declared by `notation`, not by a `def`.)

**Which of the span-generic declarations are the engine.** Grouped by what they do:

| family | count | what is in it |
|---|---|---|
| the timing law | 19 | `z`, `z_pos`, `z_pos_aux`, `z_mono`, `z_mono_aux`, `minGap`, `ivGap`, `ivGap4`, `ivGap5`, `ivSep`, `ivSep3`, `ivSep4`, `ivSep5`, `ArmSep`, `armG_armSep`, `armT_armSep`, `isLip_gap`, `isLip_index_gap`, `isLip_index_gap'` |
| the exact fold criteria | 14 | `foldsOnto_vee_iff_profile`, `profile_of_foldsOnto_lam`, `ascReach_iff_of_isLip`, `foldsOnto_landmark1`, `foldsOnto_landmark2`, `foldsOnto_walk7_of_val7`, `foldsOnto_leg4W_refl`, `foldsOnto_neg`, `AscReach`, `CritLamProfile`, `CritVeeProfile`, `beta_dist`, `beta_hits`, `beta_le_val` |
| the crookedness pairing | 16 | `CrookUp`, `CrookDown`, `CrookUp.levels`, `crookUp_armG`, `crookUp_armT`, `crookDown_armG`, `crookDown_armT`, `crookUp_climb3/4/5`, `crookDown_fall3/4`, `IsCrookedIvF`, `IsCrookedIvF.isLip`, `IsCrookedIvF.near`, `isCrookedIvF_restrict` |
| the arms and the walks | 27 | `armG`, `armT`, `armRefl`, `FoldsOnto`, `IsLip`, `lamCenter`, `veeCenter`, `leg3Walk`, `bumpWalk`, … |
| the announcements and the dichotomy | 17 | `LowAt`, `HighAt`, `NonAscAt`, `not_lowAt_highAt`, `dichotomy_at`, `highRunG_of_not_deepFirst2`, `highRunT_of_not_deepFirst2`, `nineBeforeDeep_of_highRunG/T`, … |
| the rest (local scaffolding) | 74 | the `gseq`/`gstep`/`prog`/`pseq` walk-arithmetic families, `runMin`, `nascPhase`, `ascVal`, `aVal`, `bVal`, the `…Min_of_…` profile lemmas, `exists_eq_between_isLip` and its variants, `leg4TriCrossL5_holds` |

So the engine the commission names is real and is about a third of the span-generic list (49
declarations in the timing law, the fold criteria and the pairing; 93 with the arms, the walks and
the dichotomy). The other 74 are span-generic by the inventory's criterion but are the arithmetic of
particular walk shapes, not machinery a wider span could reuse unchanged.

**One correction to the commission's naming.** There is no `foldsOnto_leg4_iff_leg4Land` in the
dependency graph: the exact criterion for the four-leg walk is `foldsOnto_leg4_of_leg4Land`
(`HPC/Fold/Leg4Land.lean`), and it is in the **level-pinned** list, together with `Leg4Land` itself,
because its statement writes offsets from the floor and the ceiling (`H−1`, `H−2`, `L+1`, `K−1`, …)
even though it is parametric in the walk's turning levels `K`, `M`, `P`. Likewise
`critLamProfile_iff_of_isLip` is level-pinned while `foldsOnto_vee_iff_profile` is not. The engine
is therefore parametric in the *walk* and pinned in the *band* — which is exactly the shape a
general proof would have to break.

**Which of the 304 level-pinned ones are instances.** Measured on the sources: a level-pinned
declaration counts as an instance when its proof body mentions **no other level-pinned theorem** —
its only project-level theorem references are span-generic ones, so the argument is already
parametric and only its statement is pinned.

* **68 of the 304** are of this kind. Eight of them have proofs of at most six lines and are
  instances in the narrowest sense (`aVal`, `HighLate`, `HighRunG`, `HighRunT`,
  `leg3Walk_branch_val`, `leg3Walk_deep_val`, `notW8_base3`, `Zig`).
* The other 60 are longer but equally self-contained: the six `crooked_peak_valley_*` /
  `crooked_valley_peak_*` readings of the pairing at fixed levels (29–34 lines each), the four
  `ceil_cross_*_far` and two `cross_valley_low_*_far` distance lemmas, the six `progLand_*` and six
  `prog4_*` walk-arithmetic lemmas, the `val3_gstep*` family, `leg4Land_w8_of_run`,
  `leg4Land_wb_of_land_of_deepFirst`, `lowLate_arm*_of_not_highLate_arm*`, `foldsOnto_walk7*_of_leaf`
  and `foldsOnto_offLam_self`. Each would be proved at once, at every span, by a parametric
  restatement of *its own* statement: nothing in its proof knows the band.
* The remaining 236 do consume other level-pinned theorems, so a parametric restatement of them is
  only as parametric as its dependencies.
* A second, cheaper economy: **16 pairs (32 declarations)** of the level-pinned list differ only by
  the arm they are read on (`…_armG` / `…_armT`, or `…G` / `…T`), and a reflection lemma —
  `armRefl`, `armRefl_isLip`, `foldsOnto_leg4W_refl`, all span-generic — proves each pair at once.

The combined statement: of the 471 declarations the span-nine proof rests on, 167 are already
span-generic, 68 more have span-generic proofs behind pinned statements, and 32 of the remainder are
mirror duplicates. The genuinely span-nine content is the walks (fixed tuples of levels), the
criteria that select them, and the 236 pinned lemmas whose proofs consume other pinned lemmas.

## 3. Deliverables

* `HPC/Fold/Target74.lean` — §2.1, `sorry`-free; `axioms-batch74.txt` is the `#print axioms` of
  `s3_span_le_nine`, `theorem3_ten_links` and `s3_span_nine`, all
  `[propext, Classical.choice, Quot.sound]`. `HPC.lean` imports it.
* `census-batch74.c` with logs `census-batch74-span9.log` … `census-batch74-span12.log` — §2.3,
  under the audit protocol, over whole arms.
* `witness-batch74-span11.txt`, `witness-batch74-span12.txt`, `check74.py`, `check74.log`,
  `check74-span12.log` — the span-eleven and span-twelve witnesses and their independent re-checks.
* `parametric-batch74.py`, `parametric-batch74.log` — §2.4.
* The correction note in the docstring of `HPC/Fold/Span.lean`; nothing else in the existing sources
  is changed.

## 4. Not delivered

No proof at span ten or above, and no proof of `s3_general`; `theorem3` in general is still
`sorry`. Theorem 4's reduction is read, in §2.2, not proved. The census is evidence, not a theorem:
it reports what holds at every basepoint of a finite corpus, and the five-leg finding at span eleven
is a statement about that corpus, checked twice.
