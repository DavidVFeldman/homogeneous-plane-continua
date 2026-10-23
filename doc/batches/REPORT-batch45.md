# Report: batch 45 — a counterexample, the branch re-split, and span nine on a thin sequence

Runs on top of the batch-44 delivery. Everything earlier is untouched except `HPC/Fold/Mixed.lean`,
which is the commissioned file; four new files carry the new material —
`HPC/Fold/Bing9.lean` and `HPC/Fold/Bing9Witness.lean` (the counterexample),
`HPC/Fold/MixedThin.lean` and `HPC/Fold/ThinSpan9.lean` (the thin branch) — and root `HPC.lean`
imports them. `lake build HPC` succeeds. The only `sorry`s in the project are `theorem3`
(`HPC/Fold/Open.lean`), the two targets of `HPC/Fold/General.lean`, and, in `Mixed.lean`,
`s3_span_nine_mid5` and the two work items `unserved_ceiling`, `unserved_valley` — all of them in
the **general** faithful model. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`
for everything proved; no `native_decide`.

## 0. The counterexample, first

**`unserved_high8` is false.** The batch-44 work item — *a pair of the branch that folds onto
neither canonical walk has, on each arm, a time at `L + 1` or below before every ascent to
`L + 8`* — fails on an actual pair, and its negation is now proved in Lean
(`not_unservedHigh8`, `HPC/Fold/Bing9Witness.lean`).

The witness is **`bing 0 9` at its basepoint `278`**. That chain has 986 links, span exactly nine
and both ends attained, so it satisfies every hypothesis the work item makes about the sequence;
a faithful crooked sequence of span nine cannot be shorter, since `z 9 = 986`. At the basepoint,
which stands at `L + 4`:

| | |
|---|---|
| both arms `HighAt (L + 1) (L + 8)` | yes — the basepoint is in the open branch |
| Λ-walk based at `L + 3` | folds the forward arm, **not** the backward one |
| V-walk based at `L + 5` | folds the backward arm, **not** the forward one |
| forward arm | stands at `L + 8` at its step `130`, with no earlier time at `L + 1` or below |

The backward arm drops to `L + 1` at its step `39` having never stood above `L + 6`
(`not_foldsOnto_lam_b9T`); the forward arm rises to `L + 7` at its step `31`, having been at
`L + 2` only at its step `2`, which the V-walk reaches too early (`not_foldsOnto_vee_b9G`); and
before its step `130` the forward arm stays in `[L + 2, L + 7]` (`not_highAt_b9G`). Thirty-three
of the 182 branch basepoints of `bing 0 9` refute the item in the same way, and over the wider
corpus 11 033 of the 20 493 pairs folding onto neither canonical walk do
(`census-batch45.c`, `census-batch45b.c`).

**Why batch 44's census did not see it.** That census checked, over the arms of the unserved
pairs, the *three-clause ceiling announcement* the engine consumes — and reported it holding
38 368 times out of 38 368, which is true. The Lean work item asked instead for
`HighAt f L (L + 8)`, which is strictly stronger; the gap between the two is exactly this
counterexample. The census and the Lean statement were not checking the same thing.

**`bing 0 9` is now in Lean.** `HPC/Fold/Bing9.lean` carries the 986 links as one natural number
in base sixteen and proves `bing9_faithful : IsCrookedIvF bing9 bing9` by the far-index method of
`HPC/Fold/DichotomyFaithful.lean`, with two changes of bookkeeping: the adjacency check is read
along the chain rather than over all pairs, and the crookedness check is cut into five blocks of
indices, each its own kernel evaluation. The file builds in under a minute.

## 1. §1 — the targets

### 1.1 The branch is re-split, and `s3_span_nine_mid4` now rests on the right two items

What `foldsOnto_leg3_deep` asks at the ceiling is the announcement now named `CeilAnn`: before an
ascent to `L + 8` the arm has been at `L` or below; or at `L + 7` or above and after that at
`L + 2` or below; or at `L + 1` or below, then at `L + 6` or above, then at `L + 2` or below.
`valleyBranch_ceiling` derives it from `HighAt f L (L + 8)` — that direction survives — and
`foldsOnto_leg3deep_branch` and `s3_span_nine_mid4_of_valley` now ask `CeilAnn` directly (the
latter no longer needs crookedness at all). The refuted item is replaced by `unserved_ceiling`,
which the census finds holding on every unserved pair, and `s3_span_nine_mid4` is unchanged in
statement and now rests on `unserved_ceiling` and `unserved_valley`.

New in `Mixed.lean`, and proved:

* `foldsOnto_lam_of_ceil_fail`, `ceiling_or_lam` — an arm that fails `CeilAnn` folds onto the
  Λ-walk by itself, so the failure is never the fault of the arm exhibiting it. This replaces
  `high8_or_lam` and keeps the halving of the work item that batch 44 set up.
* `no_low_gap`, `no_low_gap'`, `no_high_gap`, `no_high_gap'` — the crookedness clause read on a
  *window*: between a time at `A` or below and a later time at `A + 3` or above some time stands
  at `A + 1` or below, and its three reflections. Unlike `no_split_low_before_high` these
  constrain only the times strictly between the two, which is what an argument about the part of
  an arm before its first descent needs.
* `cross_floor_excluded`, `cross_floor_excluded'` — the same, across the basepoint: an arm cannot
  reach the floor `L` before the basepoint, staying at `L + 2` or above afterwards, while the
  other arm climbs three levels staying at `L + 2` or above.
* `cross_ceiling_thin`, `cross_valley_thin` — **the configuration each work item reduces to is
  impossible on a thin sequence `σ = ρ`.** In the thin form the crookedness clause is sharper than
  `CrookUp`: the intermediate link *meets* the level `k − 1`, hence stands there. Applied across
  the basepoint between the descent at `L + 1` and the ascent at `L + 8` (respectively `L + 7`) it
  produces a time at `L + 7` (respectively `L + 6`) where the two windows allow at most `L + 6`
  (respectively `L + 5`), or an `L + 7`-then-`L + 2` pattern that the failure of the ceiling
  announcement forbids, or a four-level drop in three steps. Each is one application of the clause.

### 1.2 The two work items, proved for thin sequences

`HPC/Fold/MixedThin.lean` writes the bookkeeping between the work items' own hypotheses and those
two configurations, and so proves both items on a thin sequence:

* `unserved_ceiling_thin`, `unserved_valley_thin` — the two work items, with `σ = ρ`.
* On the way: `ceil_fail_data`, `lam_fail_data`, `vee_fail_data`, `valleyAnn_fail_data` read each
  failure as an event plus a window before it; `base_window_above` says the sequence stays at
  `L + 2` or above three steps either side of the basepoint (falling or climbing three levels
  needs four steps); `cross_ceiling_thin'`, `cross_valley_thin'` are the two configurations with
  the arms exchanged — separate statements, because the crookedness clause is not symmetric in
  time: between a high time and a later low time it returns the *low* link first.
* `s3_span_nine_mid4_thin` — **the branch `L + 4`, complete, for a thin sequence.**

Two hypotheses of the commissioned statements turned out to be unnecessary and are not asked for:
neither `HighAt` branch hypothesis, and neither end of the band. The ceiling item uses only
`hnotLam` and the valley item only `hnotVee`. What the proof uses is that the basepoint stands at
`L + 4` in a band of width nine.

### 1.3 `s3_span_nine_mid5` and `s3_span_nine`, for thin sequences

`HPC/Fold/ThinSpan9.lean`. Because `s3_span_nine_mid4_thin` needs neither branch hypothesis, the
obstruction recorded under §2.1 below disappears and the branch `L + 5` *is* the reflection of the
branch `L + 4`:

* `isCrookedIvF_reflect` — **the thin model is symmetric under reflection of the levels**: if `ρ`
  is thin faithful crooked so is `a − ρ`. Reflection exchanges the two branches of the crookedness
  clause, and on a thin sequence each branch pins its two links exactly, so the exchange is an
  equality. (The general model is not symmetric in its own terms: reflecting the pair `(ρ, σ)`
  gives `(−σ, −ρ)`, so the reflected sequence's *lower* endpoints are the originals' upper ones.)
* `s3_span_nine_mid5_thin` — reflect in `a = 2L + 9`, which fixes the band `[L, L + 9]` and
  carries `L + 5` to `L + 4`.
* `s3_span_nine_thin` — **span nine, complete, for a thin sequence**: every basepoint of a thin
  faithful crooked sequence of span at most nine has both its arms folding onto one walk. This is
  the commissioned `s3_span_nine` with `σ = ρ` added.

### 1.4 What is not proved

`unserved_ceiling`, `unserved_valley`, `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`,
`theorem3` — all in the general model — are untouched and still `sorry`. Spans ten and above were
out of scope, so even the thin route stops at span nine and gives nothing towards `s3_general`.

In the general model the one application of the clause that settles the thin case yields a link
with `ρ = L + 6` and `σ = L + 7`, and nothing in the repository excludes it: that single level is
the whole of what is left at the branch `L + 4`.

## 2. §2 — the questions

**2.1 Is `s3_span_nine_mid5` the reflection of `s3_span_nine_mid4`?** *As the two are stated*, no;
*as the branch `L + 4` is now proved*, yes. Both halves matter.

Not as stated: under `x ↦ 2L + 9 − x` the branch hypothesis `LowAt f (L + 1) (L + 8)` of the
branch at `L + 5` becomes

```
∀ d, L + 8 ≤ f d → (∃ j < d, f j ≤ L + 1) ∨ (∃ j < j' < d, L + 7 ≤ f j ∧ f j' ≤ L + 3),
```

whose first clause implies `HighAt f (L + 1) (L + 8)` but whose second does not: an arm may
announce its ascent to `L + 8` by a high-then-middling pair and never stand at `L + 2` before it.
So the reflection of the branch at `L + 5` is a *weaker* hypothesis than the branch at `L + 4`,
and `s3_span_nine_mid5` does not follow from `s3_span_nine_mid4` by reflection.

But the obstruction is in the *statements*, not in the mathematics: a proof of the branch at
`L + 4` that does not use `hG`, `hT` reflects, because the reflected statement then makes no
demand the original does not. That is what `s3_span_nine_mid4_thin` is, and
`s3_span_nine_mid5_thin` is its reflection, three lines long. The branch hypotheses were never
load-bearing; they were what the dichotomy happened to have left over.

**2.2 What do the two work items say about the pair, in the language of `mix_events_far`?** They do
not follow from timing alone, and `mix_events_far` is not the tool they need — it is used nowhere
in the proofs above. What settles them, in the thin form, is:

* one application of the crookedness clause across the basepoint, between the descending arm's
  **first** descent to `L + 1` and the other arm's failure event, in the sharp form the thin model
  gives it;
* the two windows the failures supply: before its first descent the Λ-failing arm stays in
  `[L + 2, L + 6]` and the V-failing arm's window is `[L + 2, L + 5]` — the upper bounds are the
  failures themselves, the lower bound is minimality of the first descent;
* two facts of size, both from crookedness: that three levels need four steps
  (`base_window_above`, which fills the window in the four steps around the basepoint where the
  criterion's index clause says nothing), and that the four levels between `L + 2` and `L + 6`
  need four steps.

Timing enters only through the index clauses of the two profile criteria, where `armG_gap`,
`armT_gap` (via `armG_three_levels`, `armT_three_levels`) make the Λ-criterion's "at step five or
later" free. So: one application of the crookedness clause, plus the crookedness bound on speed;
and in the general model that single application is one level short, which is exactly the gap that
remains.

The census also says why no weaker argument can work: in every one of the 10 318 ceiling failures
it met, the arm's window before the failure has least level exactly `L + 2` and greatest level
exactly `L + 7`, with every `L + 2` before every `L + 7`. So the window always contains a time at
`L + 2`, and an argument that only used the clause at levels `L + 2` and `L + 8` would stop one
level short as well.

**2.3 Does the thin form `σ = ρ` lose pairs?** Still not settled — but the question is now the
whole of what separates span nine from being proved, and there is a new reason to distrust the
evidence for the general case.

Both censuses range over thin sequences. Everything they check about the two work items is now a
theorem (`unserved_ceiling_thin`, `unserved_valley_thin`), so *they could not have found a
counterexample*, and their agreement is no evidence at all about the general model. Any census
bearing on the open items would have to generate faithful pairs with `σ ≠ ρ` somewhere, which no
program in this repository does. Concretely, what would refute the general items is a faithful
crooked pair, of span nine, with a link whose `ρ = L + 6` and `σ = L + 7` sitting where the thin
argument puts its `L + 7`.

## 3. The censuses

Both range over **thin** faithful crooked sequences (`sigma = rho`), each verified pair by pair
against `IsCrookedIvF` by the routine of `census-batch43.c`, run first on paths whose status is
known. Neither ranges over a one-arm class. Folding is decided exactly, by the dynamic program
over the definition `FoldsOnto`.

* `census-batch45.c` (log `census-batch45.log`) — the corpus of batch 44: `bing 0 9` entire, its
  windows of span nine, `bing a b` with `|a − b| ≥ 9`, and crooked concatenations. Over 71 000
  branch pairs, 20 493 folding onto neither canonical walk:

  | | |
  |---|---|
  | `unserved_high8` fails | **11 033** |
  | `unserved_valley` fails | 0 |
  | the ceiling announcement `CeilAnn` fails | 0 |
  | arms failing `CeilAnn`, whose pair's other arm fails to fold Λ | 0 (of 10 318) |
  | arms failing the valley announcement, whose other arm fails to fold V | 0 (of 35 138) |

* `census-batch45b.c` (log `census-batch45b.log`) — `bing 0 9` alone, with each fold decided
  **twice**, by the dynamic program and by the exact profile criteria of `HPC/Fold/Profile.lean`
  read with the index clauses of `HPC/Fold/Timing.lean`; the two agree at all 182 branch
  basepoints. Of the 55 unserved pairs there, 33 refute `unserved_high8`, none refutes the
  ceiling or the valley announcement. This is the program that exhibits the pair formalized in
  `HPC/Fold/Bing9Witness.lean`.

The two zero rows of the first table are, after this batch, instances of the two theorems of
`HPC/Fold/MixedThin.lean`; see §2.3.

## 4. Deliverables

1. Proved, `sorry`-free, standard axioms `[propext, Classical.choice, Quot.sound]`:
   * `HPC/Fold/Bing9.lean` entire, in particular `bing9_faithful`;
   * `HPC/Fold/Bing9Witness.lean` entire, in particular `not_unservedHigh8`;
   * in `HPC/Fold/Mixed.lean`: `CeilAnn`, `valleyBranch_ceiling`, `foldsOnto_leg3deep_branch`,
     `s3_span_nine_mid4_of_valley`, `foldsOnto_lam_of_ceil_fail`, `ceiling_or_lam`, `no_low_gap`,
     `no_low_gap'`, `no_high_gap`, `no_high_gap'`, `cross_floor_excluded`, `cross_floor_excluded'`,
     `cross_ceiling_thin`, `cross_valley_thin`, together with everything batch 44 proved there;
   * `HPC/Fold/MixedThin.lean` entire, in particular `unserved_ceiling_thin`,
     `unserved_valley_thin`, `s3_span_nine_mid4_thin`;
   * `HPC/Fold/ThinSpan9.lean` entire, in particular `isCrookedIvF_reflect`,
     `s3_span_nine_mid5_thin`, `s3_span_nine_thin`.
2. Censuses: `census-batch45.c`, `census-batch45b.c`, with logs; both over thin sequences, as
   §3 states.
3. What is open, all of it in the general model: `unserved_ceiling`, `unserved_valley`,
   `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`.
