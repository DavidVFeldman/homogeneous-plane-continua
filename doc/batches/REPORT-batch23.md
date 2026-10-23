# Report: batch 23 — the three conjectures over the faithful model

**All three conjectures are false**, and so is the conclusion `F2PrimeF` they were to deliver.
Each refutation is at a member of `IsCrookedIvF`, so by batch 22's `realization` each is the
`(minIdx, maxIdx)` pair of an explicit chain of open rectangles crooked in a chain of strips:
these refute statements about Bing's objects, not merely about sequences.

Everything below is `sorry`-free, builds with `lake build`, and uses no `axiom`,
`native_decide` or `implemented_by`.

---

## 1. The counterexamples

### 1.1 `ExitReachF` — `HPC/Fold/ExitReachFWitness.lean`

A forty-two term member of the model, with a genuinely wide pair of links (`σ ≠ ρ`):

    ρ = 4 3 2 3 2 1 2 2 2 1 2 1 0 1 2 1 2 3 2 1 2 2 2 3 4 3 2 3 2 1 2 3 2 3 4 3 2 3 4 3 4 5
    σ = ρ  except  σ 7 = 3  and  σ 21 = 3

Basepoint `exfPt = 2`, so `p = 2`; `H = 5`, `L = 0`, both attained.

* The backward arm is `2, 3, 4`. It never leaves the window below, so its peak demand is `4`,
  and the bump height is `hStar = 4`, the cap `max (H − 1) p`.
* The forward arm drops to `0` at its eleventh index and, before that, never exceeds `3` in
  the phase-adjusted sense, so `OkLam` fails on it.
* Dually the forward arm attains `L = 0`, so the valley depth is the floor `lStar = 1`, while
  the reflected backward arm leaves its window at its third index with reflected reach only
  `−2`; so `OkVee` fails on the backward arm.

Both disjuncts fail at this basepoint: `not_exitReachF`. At the same witness and basepoint
neither the Λ branch nor the V branch folds, which gives `not_f2PrimeF` directly — `F2PrimeF`
does not merely lose this route, it is false.

### 1.2 `HighExitValleyF` and `LowExitPeakF` — `HPC/Fold/ValleyFWitness.lean`

One seventy-one term **thin** member (`σ = ρ`, so the `σ` column is the `ρ` column) refutes
both:

    0 1 2 1 2 3 2 1 2 3 2 3 4 3 2 3 2 1 2 3 2 3 4 3 2 3 4 3 4 5 4 3 4 3 2 3 4 3 2 3 2 1
    2 3 2 3 4 3 2 3 4 3 4 5 4 3 4 3 2 3 4 3 4 5 4 3 4 5 4 5 6

with `H = 6`, `L = 0`, both attained.

* **`HighExitValleyF`** fails at basepoint `hlPtH = 46`, where `p = 4` and `hStar = 4`. On the
  forward arm no index reaches `hStar` in the phase-adjusted sense before index `0`, so the
  peak-index hypothesis holds vacuously at `s = 0`; the arm's last index carries level
  `6 > hStar + 1`, and the arm never descends to `L + 1 = 1` at all. Refuting index `u = 24`
  on that arm: `not_highExitValleyF`.
* **`LowExitPeakF`** fails at basepoint `hlPtL = 24`, where `p = 2` and `lStar = 2`. On the
  backward arm, reflected, `s = 0` passes for the same reason, the arm's last index carries
  `0 < lStar − 1`, and the arm never rises to `H − 1 = 5` in between. Refuting index `u = 24`:
  `not_lowExitPeakF`.

Both failures are at `s = 0`. That is not an artefact of a weak hypothesis: the conjectures
quantify over *all* admissible peak indices, and a vacuously-admissible `s = 0` is the
cheapest of them.

### 1.3 The membership check actually used

The commission asks that a counterexample be checked with `IsCrookedIvFCheck`. Batch 22's
`IsCrookedIvFCheck` quantifies the forced-meeting indices over all of `Fin n`; at these
lengths it is not evaluable (a kernel `decide` on the forty-two term witness reached 58–70 GB
of resident memory and had not finished after forty-five minutes).

This batch therefore proves a cheaper sufficient criterion, `IsCrookedIvFCheck2`, together
with `isCrookedIvF_of_check2 : IsCrookedIvFCheck2 ρ σ → IsCrookedIvF ρ σ` (in
`HPC/Fold/ClosureF.lean`). Two changes make it evaluable:

* the meeting index is taken at three **clamped offsets** (`clampIdx`, `exists_clampIdx`)
  rather than searched over all indices;
* the two intermediate links are produced by an explicit search, `findMeet` / `meetPair` with
  their specifications, instead of by an existential.

Cost on the same machine: the thirty-term witness went from about eight minutes to 43 s, and
the forty-two term witness — previously not completable — to about 1 min 40 s. The criterion
is *sufficient*, proved in Lean, so a witness that passes it is a genuine member of the model
and hence, by `realization`, a genuine chain. The three membership facts are
`exfSeq_isCrookedIvF`, `hlSeq_isCrookedIvF`, `hevSeq_isCrookedIvF`.

### 1.4 A separating counterexample to the sketch's mechanism

`HPC/Fold/ClosureFWitness.lean` refutes the batch-19 sub-claim
`AttainsMinBeforeExceedF` — *an arm which exceeds `hStar + 1` has already attained `L`* — at a
thirty-term thin member,

    0 1 2 1 2 3 2 1 2 3 2 3 4 3 2 3 2 1 2 3 2 3 4 3 2 3 4 3 4 5

at basepoint `5` (`p = 3`, `H = 5`, `L = 0`, `hStar = 3`): the forward arm reaches
`5 = hStar + 2` at its last index and never visits level `0`, which sits entirely on the
backward side. At that chain `HighExitValleyF` itself still **holds** (the arm visits
`1 = L + 1`, and `s = 0` is the only admissible peak index), so this witness separates the
mechanism from the conjecture. Batch 19's refutation of the same sub-claim used a sequence now
known to be no chain; this one is a chain.

---

## 2. Which of the three were proved, and by what mechanism

None — all three are false. What was proved is the surrounding structure.

**The two ordinary items (§1 of the commission), both delivered.**

* `f2PrimeF_of_exitReachF` — batch 20's `f2PrimeIv_of_exitReachIv` transfers verbatim with
  `IsCrookedIvF` for `IsCrookedIv`; as the batch-20 report predicted, crookedness is only
  passed through. (It is now a conditional with a false hypothesis, but it is correct and is
  what shows the three conjectures were the right target.)
* `IsCrookedIvF.isCrookedSeqUp` — instantiating the faithful clause at `h := σ s`, `k := σ t`
  and reading `ρ r ≤ k ∓ 1 ≤ σ r ≤ ρ r + 1` gives exactly the batch-13 up-form windows. So a
  single faithful pair carries the down form on `ρ` (`isCrookedSeq`) and the up form on `σ`.

**The combined Synchronization Lemma**, also delivered: `IsCrookedIvF.sync_comb` and its
mirror `IsCrookedIvF.sync_comb'`. With the window `p − 1 ≤ ρ`, `σ ≤ p + 1` intact across an
upward and a downward exit they produce a link at exactly `ρ j = p − 1` followed by one at
exactly `σ k = p + 1`, and the reverse.

**Partial structure for `HighExitValleyF`**, kept because it is sound and reusable:

* `isCrookedSeq_armG`, `isCrookedSeq_armT` — each arm inherits the down form;
* `valleyBefore_of_attains_min` — the arm-level form of the batch-19 mechanism;
* `le_hStar_of_range`, and the reduction `highExitValleyF_of_attainsMin`, which shows that
  `HighExitValleyF` needs nothing beyond `AttainsMinBeforeExceedF`.

The reduction is what turned the search: it says a counterexample to the sub-claim is the
first thing to look for, and the crooked-pattern chains that produce sub-claim failures in
bulk are exactly the ones that produce conjecture failures.

The three conjecture statements and the two corollaries (`f2PrimeF`, `theorem3`) are kept in
`HPC/Fold/ClosureF.lean` as commented-out blocks, with the refutations named beside them.
Nothing was silently weakened. §5 of the commission does not apply: Bing 1948 Theorem 3 in the
block reading is **not** made unconditional by this route. The conditional
`theorem3_of_F2PrimeF` from the previous batch is untouched and still stands; only its
hypothesis is now known to be false.

---

## 3. Was the combined Synchronization Lemma usable? Was the `σ`-side reflection?

**The Synchronization Lemma: proved, and not needed.** `sync_comb` / `sync_comb'` are exactly
the sharpening §17 of the notes wanted, and they are legitimate over the faithful model
(the up form on `σ` is what licenses them). But the branch of the `ExitReachF` sketch they
were to serve — the arm that does not fail the Λ side — does not exist in general: the
forty-two term witness fails the Λ side on the forward arm and the V side on the backward arm
simultaneously. The lemma is delivered on its own merits.

**The `σ`-side reflection: not usable.** The commission's observation is correct that the
reflection of the down form is the up form, and that over the faithful model the up form is
available on `σ`, so a reflected argument can in principle run on `σ` rather than on `−ρ`.
The obstruction is which witness each form pins. Batch 13 established that the down form pins
the *near-target* link and the up form the *near-source* link; and with `σ − ρ ∈ {0, 1}`, both
the down form on `ρ` and the up form on `σ` end up pinning the **lower** of the two ends. On
the low side the target to be reached is `ρ j ≥ H − 1`, an upper witness, and what the two
forms jointly supply is one unit short of it. So the reflection transports the shape of the
argument but loses exactly the unit that the high-side argument gains from the floor/cap
asymmetry. The low-side conjecture is in any case false, so no repair was attempted.

---

## 4. Census, and how far the search got

Scripts, all in the project root:

* `census-batch23.py` — the model and the conclusion checkers (`is_faithful`, `check_point`,
  `hStar`, `lStar`, `hReach`, `okLam`, `okVee`, `valley_all_s`, `enumerate_faithful`).
  CLI: `exhaustive LEN LEVELS`, `random LEN LEVELS TRIALS [SEED]`.
* `search-batch23.py` — a fast incremental `Builder`, Bing's pattern `crook`, the `σ` search
  `sigma_dfs`, `random_crooked_chain`, and `shrink`.
  CLI: `random TRIALS LEN LEVELS [SEED]`, `crooked TRIALS MAXLEN LEVELS [SEED]`.
* `anneal-batch23.py` — a soft-margin hill climb.
  CLI: `TARGET ROUNDS STEPS LEVELS [SEED] [START]`, `TARGET ∈ {exit,high,low}`,
  `START ∈ {flat,crooked}`. Its margins were checked to agree exactly with `check_point` on
  3000 random sequences.

**Exhaustive, over the faithful model with attained extremes, five levels.**

| length | faithful pairs | basepoints |
| --- | --- | --- |
| 4 | 78 | 312 |
| 5 | 278 | 1 390 |
| 6 | 1 006 | 6 036 |
| 7 | 3 686 | 25 802 |
| 8 | 13 614 | 108 912 |

No failure of any of the three, and none of the sub-claim `AttainsMinBeforeExceedF`
(142 452 basepoints). This reproduces the commission's own counts and batch 22's.

**Random walks in the model.** 200 chains of length 40 on eight levels; 100 of length 80 on
fourteen levels; 10 of length 300 on sixty levels; 300 of length 100 on twenty levels. No
failure — and the diagnosis is that plain random walks in the model essentially never reach
the failing region: over 300 chains of length 100 on twenty levels the realised range never
exceeded 5.

**Chains built from Bing's crooked pattern.** This is what found everything. Concatenating
`crook` and then searching for an admissible `σ`: 208 faithful chains of length ≤ 120 on seven
levels, 4 585 basepoints inspected → **22** `ExitReachF` failures, **12** `LowExitPeakF`,
**12** `HighExitValleyF`. The seventy-one term witness alone carries failures at basepoints
10, 14, 23 (`ExitReachF`), 24 (`LowExitPeakF`), 35, 46 (`HighExitValleyF`), 47, 56 and 60.
Sub-claim census over the same generator: 283 chains, 7 704 basepoints, **361** failures of
`AttainsMinBeforeExceedF`.

**Hill climbing.** From a flat start the climb never got past margin 0 — the model constraints
leave no gradient. Seeded from a crooked chain it found the first `ExitReachF` failure within
two rounds (seed 11, six levels, a ninety-term chain, later shrunk to the forty-two term
witness by removing links while re-checking membership).

The moral of the census is the commission's own warning, sharpened: the failing region of the
faithful model is reached by iterating Bing's pattern and by essentially nothing else. The
zero-failure counts of batches 16–22, and of the exhaustive census here, are all below the
length at which a doubled-back crooked pattern first fits.

---

## 5. Axiom audit

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every delivered result:

`not_exitReachF`, `not_f2PrimeF`, `not_highExitValleyF`, `not_lowExitPeakF`,
`not_attainsMinBeforeExceedF`, `f2PrimeF_of_exitReachF`, `IsCrookedIvF.isCrookedSeqUp`,
`IsCrookedIvF.sync_comb`, `IsCrookedIvF.sync_comb'`, `highExitValleyF_of_attainsMin`,
`valleyBefore_of_attains_min`, `isCrookedIvF_of_check2`.

No `sorry`, no `axiom`, no `native_decide`, no `@[implemented_by]` in any file of this batch;
the membership checks are kernel `decide`. `lake build` succeeds, and none of this batch's
files produces a linter warning. Four `unused variable` warnings remain, in
`HPC/Fold/Itinerary.lean` (`lamCenter`, parameter `L`) and `HPC/Fold/Bump.lean` (`bumpCenter`,
`SegLamC`, `SegLam`, parameter `H`). They predate this batch and each would require dropping a
parameter from a definition used throughout the development; the commission asks that nothing
outside `ClosureF.lean` and `HPC.lean` be touched, so they are left as they are and flagged
here instead.
