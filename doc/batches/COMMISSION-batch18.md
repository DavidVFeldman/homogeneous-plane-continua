# Commission: batch 18 — the three conjectures, search permitted

**Go!** Runs on top of the batch-17 delivery. One new file, `HPC/Fold/Closure.lean`; root
`HPC.lean` updated. Nothing else touched.

## This batch is different

Every earlier batch supplied a complete English proof for each statement and forbade open
search. This one does not. The three theorems below are conjectures: each has been checked on
7 042 754 basepoints under the down form (batch 16's census) and on further runs to length 60,
none has a proof, and the three that occupied this position before them were false. What is
supplied is a sketch of the mechanism and the verified lemmas the proof should assemble from.
**Search is permitted and time is unbounded.**

What does not change: census against the skeleton; `#print axioms` on every theorem; no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`; no statement weakened, no hypothesis
added, without saying so in the report. And this, above everything: **a counterexample to any
of the three is a success.** Report it before anything else. If a conjecture is refuted, replace
its `theorem` by `theorem not_<name> : ¬ <Name>` with the witness, and delete the corollaries
that depend on it; say so.

## Protocol otherwise

As batches 1–17. All of `HPC/Fold/` is available. The lemmas most likely to matter are named
in §3.

## 1. What the three statements say

Fix a down-crooked Lipschitz `ρ`, a basepoint `i`, `p := ρ i`, the extremes `H`, `L` with
`L + 3 ≤ H`, and `hStar`, `lStar` as in batch 9. Arms `G`, `T` read outward from `i`.

**`ExitReach`.** For each arm: either it never drops below `p − 1`, or its phase-adjusted level
reaches `hStar` before its first drop. Both arms satisfy this (the Λ family), or both satisfy
the reflection at `lStar` (the V family).

**`HighExitValleyOpen`.** In the case where the cap in `hStar` does not bind — equivalently
(batch 17, `demands_lt_of_open`) both arms' demands and `p` are strictly below `H − 1` — an arm
that exceeds `hStar + 1` after its peak index has visited `L + 1` or below in between.

**`LowExitPeak`.** The reflection of the *unrestricted* `HighExitValley` (batch 16 §4). Note
that `HighExitValley ↔ HighExitValleyOpen` is proved (batch 17) but the reflection of that
equivalence is **not** available, because reflecting through a crookedness hypothesis is
unsound (batch 13, `not_isCrookedSeq_neg`). So `LowExitPeak` must be attacked directly; see §3.

## 2. What is already known, and verified

* `not_hStarArm_and_lStarArm` (batch 12): no arm has demand `≥ p + 2` upward and `≤ p − 2`
  downward. Whichever witness comes first violates the other's prefix condition.
* `exists_nonAsc_of_climb`, `phase_eq_one_of_climb` (batch 11): an arm standing `≥ p + 3` above
  its start has phase `1`, because crookedness forbids a monotone climb of three.
* `sync` (batch 7): between an upward exit at `p + 2` and a downward exit at `p − 2` with the
  window intact, a link at exactly `p − 1` followed by one `≥ p`.
* `segLam_of_okLam_no_drop` (batch 16): an arm that never drops satisfies `SegLam` at `hStar`.
* `exists_drop_before_exceed`, `pre_drop_eq`, `demands_lt_of_open` (batch 17).
* `not_agreement` (batch 15): the two arms' demands can differ by two in both directions at
  once; the cap in `hStar` is what makes that harmless. Any proof of `ExitReach` must use the
  cap, since the uncapped statement is false.

## 3. Sketches

### `HighExitValleyOpen`

By `demands_lt_of_open`, `hStarArm G < H − 1`, `hStarArm T < H − 1`, `p < H − 1`, and
`hStar = max (hStarArm G) (hStarArm T) (p) (L + 1) ≤ H − 2`. Let `A` be an arm, `s` its peak
index, `u ≥ s` with `A u > hStar + 1`. By `exists_drop_before_exceed`, `A` has a first drop `d`
with `d < u`, and by `pre_drop_eq`, `A (d − 1) = p − 1`.

In the corpus, four shapes occur, as `(hStar − p, H − 1 − hStar, L − (p − 2))`:

* `(0, 1, 0)`, the overwhelming majority: `hStar = p`, so `s = 0`, and `L = p − 2`, so the
  visit is `A (d − 1) = p − 1 = L + 1` with `0 = s ≤ d − 1 < u`. Pure bookkeeping.
* `(0, 1, −1)`: `L = p − 3`, so `L + 1 = p − 2 = A d`; the visit is the drop itself, `s = 0 ≤ d`.
* `(0, 2, 0)`: `H = p + 3`; still `hStar = p`, `s = 0`, visit at `d − 1`.
* `(1, 1, 0)`: `hStar = p + 1`. Here `s` may exceed `d − 1` — if `A`'s own demand is `p` and the
  other arm's is `p + 1`, `A` reaches `p + 1` phase-adjusted only via `A = p` with phase `1`,
  which needs a non-ascending step before a return to `p`. If instead `A` goes `p, p − 1, p − 2`
  directly, then `A + φ` never reaches `p + 1` before the drop, `s` is at or after `d`, and one
  must check whether the clause is then vacuous (no `u ≥ s` exceeds `hStar + 1`) or whether the
  hypothesis on `s` in `HighExitValleyOpen` fails. The corpus says the conjecture holds; the
  reason in this shape is what needs finding.

The general argument should show these four shapes exhaust the non-vacuous case or handle it
uniformly. The likely tool: crookedness applied to the pair `(d, u)` — levels `p − 2` and
`> hStar + 1 ≥ p + 1`, gap `≥ 3` — which gives a link in `[A u − 2, A u − 1]` followed by one in
`[p − 2, p − 1]` between them; and, when `L` is attained on `A`, to the pair (position of `L`,
`u`), which gives a link `≥ A u − 2 ≥ hStar` followed by one `≤ L + 1`. The second link is the
visit if it lies at or after `s`, and the first link, being `≥ hStar`, is at or after `s`
provided it is on `A`.

### `LowExitPeak`

Do not reflect. Rerun the argument above on the descending case of `IsCrookedSeq`, whose
windows are `[f t, f t + 1]` for the near-target witness and `[f s − 2, f s − 1]` for the
near-source one. The asymmetry against the ascending case — the near-source window sits two
below the source rather than at it — is real and is why reflection fails; the proof must carry
the shifted bounds through.

### `ExitReach`

Suppose the Λ family fails: some arm `A` drops to `p − 2` at `d` with `hReach A p < hStar`.
Show both arms satisfy the V condition at `lStar`.

For `A` itself: it drops before reaching `hStar`. If it never rises to `p + 2`, `OkVee` holds by
the no-rise disjunct. If it rises, at `r`: is `r < d` or `d < r`? If `r < d`, then
`hStarArm A ≥ p + 2`, so `hStar ≥ p + 2`, and `A` failed to reach `hStar` before `d` although
it reached `p + 2` — so `hStar ≥ p + 3` (the phase gives one unit) and the *other* arm's demand
is at least `p + 3` uncapped. If `d < r`, then `lStarArm A ≤ p − 2` and `lStar ≤ lStarArm A`,
and `A` reaches `lStarArm A` before `r` by definition — `lReach A ≤ lStarArm A ≤ ... ` needs
`lReach A ≤ lStar`, which is where the cap on the V side enters, symmetric to the Λ-side cap.

For the other arm `B`: this is the case that broke every earlier formulation. The two facts
that must combine are `not_hStarArm_and_lStarArm` for `B` and the cap. If `B` never rises,
done. If `B` rises at `r_B` before dropping, then `hStarArm B ≥ p + 2` and `lStarArm B ≥ p − 1`,
so `lStar = min (lStarArm G) (lStarArm T) (p) (H − 1)` floored at `min (L + 1) p` is at least
`min (p − 1, lStarArm A, ...)` — and `B` reaches `lStar` before `r_B` iff `lStar ≥ lReach B`
which holds if `lStar ≥ p − 1` or `B` dips to `p − 1` before rising. The refuting sequence for
`Agreement` is the test case: there `hStar` was capped, the Λ family worked, and this branch
was never needed. A proof must explain why the failure of Λ *forces* the V-side inequalities
for `B`; the candidate mechanism is `sync` applied to `A`'s drop and `B`'s rise, with the
window intact between them because `A` reached neither `hStar` nor `p + 2` before `d` and `B`
reached neither `p − 2` nor `lStar` before `r_B`.

Expect the case analysis to be wide. The corpus can be consulted for any sub-case: every
down-crooked sequence of length `≤ 12` on six levels is enumerable in seconds.

## 4. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample found; which of the three were proved; for each
   proof, the actual mechanism, since the sketches above are guesses; for any not proved, how
   far the search got and what obstructed it. **A run that ends with none of the three proved
   and none refuted is a legitimate outcome and should be reported as such**, with the partial
   results kept if they are sound.

## 5. If all three fall

`f2Prime` and `theorem3` follow by the two lines in the skeleton, and Bing 1948 Theorem 3 in the
block reading is unconditional in the repository.
