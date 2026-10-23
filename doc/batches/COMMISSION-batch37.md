# Commission: batch 37 — Bing 1948 Theorem 3, handed over without a route

**Go!** Runs on top of the batch-36 delivery. One new file, `HPC/Fold/Open.lean`; root `HPC.lean`
updated. Nothing else touched.

## 0. What this batch is, and why

Thirteen formulations of the folding statement have been refuted. Of the last four commissions,
every one contained an error this run had to find: a quantifier that collapsed the statement into
its own goal (batch 27), a trim that provably could not be appended to (batch 34), a structure
whose clauses contradicted each other (batch 35), and a census that measured a looser condition
than the statement it was offered as evidence for (batch 36). In each case the run's effort went
to correcting the commission rather than to the mathematics.

The bottleneck is the formulating, not the proving, and the formulating has been mine. So this
commission proposes no statement of its own beyond Bing's, no route, no family, no induction, and
no sketch. **The scaffolding of batches 6–36 may be used, replaced or ignored.**

Two permissions that earlier commissions did not grant, and that matter:

* **Restate the target.** `S3`, `S3ZigFree`, `S3ZigFreeInterior` and the rest are one author's
  reductions. If a different formulation of Theorem 3's content is better, state it and work on
  that. The only thing that must not change is `theorem3` itself, which is Bing's.
* **Work at whatever level suits.** The sequence model of batches 5 onward is a convenience, not
  a commitment. A proof at the level of chains and consolidations — Bing's own level — is
  welcome, and so is abandoning the block reading's three-link form for the two-link form Bing
  actually stated, if that turns out easier.

## 1. The goal

`HPC/Fold/Open.lean` states `theorem3` with a single `sorry`. The routes already proved, any of
which suffices, are listed in its docstring; `exists_blocks_first_of_folds` (batch 6) is the most
useful of them, since it accepts an arbitrary walk and asks only that both arms of the basepoint
fold onto it.

A counterexample to `theorem3` would be the most valuable outcome of all and should be reported
first. There is no evidence for one: every corpus in this project has served every basepoint.

## 2. The record of what is refuted

Fifty-nine `not_`/`no_` theorems are in the repository. The ones that constrain any future
attempt, with what they forbid:

**About the model.** `not_isCrookedSeq_neg` (batch 13) — reflection does not preserve the down
form, so a lemma may be reflected only when no crookedness hypothesis lies anywhere beneath it.
`no_three_banded_cut_in_general` (batch 27) — a faithful crooked sequence may visit `L, H, L, H`
in order, so three pieces of strictly smaller span need not exist.

**About families of walks.** The reversal law (census, exhaustive to span 12): the least number of
turning targets grows as `⌊span/2⌋ − 1`, so **no family with a bounded number of turns can
work**. `cover_card_ge_span` (batch 32) — any cover of a chain's basepoints needs at least
`⌊(H−L)/3⌋ + 1` walks, for arbitrary walks. `notConstantOnBand` (batch 32) — the choice of walk
cannot depend on the band alone. `not_s3Zig` with `zig_base_lower`/`zig_base_upper` (batch 28) —
a walk of strictly increasing amplitude cannot start in an extreme band.

**About separating the two arms.** `no_common_walk_pairA_pairB` (batch 33) — two contiguous
stretches of one faithful crooked sequence, starting at a common level, each foldable alone, with
**no walk whatever** folding both. So no argument may treat the arms as independent sequences
sharing a level. `not_oneTurn_of_opposite` (batch 31) — the one-turn case, settled both ways.

**About extension.** `no_outer_member_of_span_one_trim` and `no_outer_member_of_boundary_trim`
(batches 34–35) — an inner band must be strictly inside at **both** ends to be appendable, which
the cut's own stretches are not. `no_fold_of_early_low` (batch 34) — an arm reaching `L` at index
`d` forces `d` to be at least the inner walk's length. `not_extendStepMin` (batch 36) — even
restricted to shortest inner walks, extension fails; and the census shows even the weakest
extension form failing at spans 11 and 12. **Extending an inner walk by two outer legs is not the
construction.**

**About black boxes.** Batch 27 §4 — a hypothesis of the form "an arbitrary walk for a middle
piece extends" is at least as strong as the goal, because the middle piece can be made three links
long. Batch 35 — `cutWalk'_iff_s3ZigFreeInterior`: a route that only supplies data is equivalent
to the goal, not a reduction of it.

**About Bing's own proof.** `bing-theorems-3-4-notes.md` §4: his induction has three subcases; he
writes the first and dispatches the rest with "by a similar line of argument". The second and
third need a tail-absorption step that appears nowhere in the paper. An implementation of his
construction, with that step done by backtracking search allowing new blocks only at the end,
fails at basepoint 6 of the thirteen-link `bing 0 4` — but his written subcase dissolves blocks
past the seam and regroups by level, a stronger move that implementation did not generalise. So
the step is missing from the text; whether his intended argument works is not known.

## 3. What is settled

The faithful interval model is exactly the class of `(minIdx, maxIdx)` pairs of 1948-crooked
chains (`isCrookedIvF_minIdx_maxIdx` and `realization`, batch 22), so a counterexample stated
over it is a counterexample about chains. Bing's Theorem 7 holds with minimality (`minimality`,
`bingPath_length`), giving `timing_slack'` and `index_gap_of_level_gap'`. `bingPath` generates
crooked chains of any span on demand — the only objects in the project that reach the inductive
case, since a crooked chain of span `d` needs `z d` links and no random search finds them.
`s3ZigFree_near_extreme` settles every basepoint within two of an extreme at any span.

## 4. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. A census of whatever was explored.
3. Report: any counterexample first; what was attempted; what was abandoned and why. **A run that
   proves nothing but reports which of the remaining routes it closed is a good outcome** — the
   most useful results of the last ten batches have been refutations.

## 5. Not in this batch

Bing 1948 Theorems 4, 5, 6, 13; the reduction in Bing 1951 and its definitional seam; the
linear-time far-index check that would make `¬ F2PrimeOff` unconditional.
