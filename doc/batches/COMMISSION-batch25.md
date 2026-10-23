# Commission: batch 25 — `OffDichotomy`

**Go!** Runs on top of the batch-24 delivery. One new file, `HPC/Fold/Dichotomy.lean`; root
`HPC.lean` updated. Nothing else touched.

## Protocol

`arm_first_exit` is an ordinary item with the proof in §3.1. `offDichotomy` is the search
item, as batches 18–24: search permitted, time unbounded, sketch in §3.2. Census, axiom audit,
no silent weakening. **A counterexample to `OffDichotomy` is a success; report it first**, with
`σ` and the faithful check. A run that proves neither is legitimate; keep sound partials.

## 1. The statement

Batch 24's `OffDichotomy`, unchanged. `BottomOnTime f c L` says: `f` never exceeds `c + 1`, or
there is an index `j ≥ c − L − 1` with `f k ≤ c + 1` for all `k ≤ j` and `f j ≤ min (L + 2) c`
(the second clause of the definition, `f k ≤ min (L+2) c + (j − k)`, is then automatic from
`IsLip`, so the content is: *reach the bottom band at an index no earlier than the ladder token
can, without first rising above the base window*). `TopOnTime` is the mirror. The batch-24
census scores the dichotomy with no failure on every corpus of induction depth the project
has: `bing 0 n` to `n = 7`, 7 559 subchains of `bing 0 7` (665 322 basepoints), the faithful
exhaustive corpus to length 9, both batch-23 witnesses.

## 2. What is known

* Batch 24: `f2PrimeOff_of_offDichotomy`; the monotone case (`f2PrimeOff_monotone`); the
  ladder folds `foldsOnto_offLam_self`/`foldsOnto_offVee_self` — an arm satisfying
  `BottomOnTime` folds onto the Λ-ladder, and `TopOnTime` onto the V-ladder.
* Batch 12: `not_hStarArm_and_lStarArm` — the single-arm exit lemma at center `p`. §3.1
  restates it off center, without crookedness.
* Batch 7/13: `sync`, `sync_up`; batch 23: `IsCrookedIvF.isCrookedSeqUp σ`, so both forms are
  available on one faithful sequence. Batch 11: the Phase Lemma.
* The batch-24 report's two negative findings: the plain ladder `offVee c (L+1) L H` from a
  single `c` fails at 34 basepoints of `bing 0 6`/`bing 0 7` — the choice of `c` is essential —
  and level-only criteria fail in both directions; the index condition `j ≥ c − L − 1` is
  needed.

## 3. Proofs and sketch

### 3.1 `arm_first_exit`

Case split on whether `∃ j, c + 1 < f j` and whether `∃ j, f j < c − 1`. If neither, the first
disjunct (or second) holds. If only the first, take `j` least with `c + 1 < f j`; every `k < j`
has `f k ≤ c + 1`, and `f k ≥ c − 1` because there is no down-exit at all: the third disjunct.
If only the second, symmetric: fourth. If both, take `j₁` least with `c + 1 < f j₁` and `j₂`
least with `f j₂ < c − 1`; they differ; if `j₁ < j₂` then all `k ≤ j₁` satisfy `c − 1 ≤ f k` by
minimality of `j₂`, giving the third disjunct; else the fourth. No crookedness; `IsLip` is not
needed either and may be dropped.

### 3.2 `offDichotomy` — sketch

Write `p = ρ i` and `G`, `T` for the arms. For each `c ∈ {p−1, p, p+1}` and each arm,
`arm_first_exit` gives: bounded above (then `BottomOnTime` holds vacuously… *no*: bounded above
by `c + 1` is the first clause of `BottomOnTime` and gives it outright), bounded below (gives
`TopOnTime`), first exit up, or first exit down.

*Reduce to first exits.* If some `c` makes both arms bounded on the same side, done. Otherwise
consider the arm exits. **The claim to establish is that some `c` makes both arms' first exits
agree in direction, and that the arm exiting, say, upward first reaches the top band on
schedule.** The three values of `c` shift the window by one; an arm whose first exit is upward
at `c` may have its first exit downward at `c + 1` only if it drops to `c − 1 = (c+1) − 2`
before rising to `c + 3`; so moving `c` by one changes an arm's exit direction only for arms
that leave both sides of the base window within one level of each other. Crookedness enters
here through the Synchronization Lemma: an arm that exits upward at `c + 2` and downward at
`c − 2` with the window intact between them carries a link at exactly `c − 1` then one at
exactly `c + 1` (both forms available on a faithful sequence), and that structure determines
which shift of `c` reverses the exit.

*On schedule.* Given both arms exit upward first at `c`, `TopOnTime` needs each to reach
`max (H − 2) c` at an index `≥ H − 1 − c` without first dropping below `c − 1`. The first-exit
clause gives "without first dropping"; the arrival needs crookedness: the arm rises from `c`
to at least `c + 2`; pair it with the index attaining `L` (which exists) — if that index is on
the same arm beyond the exit, crookedness on the pair (exit, `L`-index), gap `≥ 3`, gives a
near-target link at `≤ L + 1` preceded by a near-source link at `≥ c + 1`… the direction of the
pair matters and the arm may instead attain `H` first. The batch-24 census can be queried for
which of these configurations occur at the 34 basepoints where the single-`c` ladder fails.

*Bing's induction, as the fallback.* If the direct argument does not close, `OffDichotomy` is
what his induction on the span produces: the special case's witnesses `h′, k′` put the
basepoint in one of three segments, and the induction hypothesis on the segment yields the
dichotomy there; the outer pieces are on schedule by construction, since `h′` and `k′` are
exactly one below the top and one above the bottom.

## 4. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report: any counterexample; whether `offDichotomy` was proved, and by which route; for a
   partial result, which of the cases in §3.2 closed.

## 5. If `offDichotomy` falls

`f2PrimeOff` and `theorem3` follow by the two lines in the skeleton, and Bing 1948 Theorem 3 in
the block reading is unconditional.
