# Report — batch 20: the interval model

Two files: `HPC/Fold/Interval.lean`, the commissioned one, and `HPC/Fold/IntervalWitness.lean`,
which is not commissioned and carries the batch's main finding. Root `HPC.lean` imports both.
Nothing else in the project was touched. The whole project builds; neither new file contains
`sorry`, `admit`, `axiom`, `native_decide` or `implemented_by`, and every declaration in them
has axiom profile within `propext`, `Classical.choice`, `Quot.sound`. The census script is
`census-batch20.py`; the commission text is kept as `COMMISSION-batch20.md`.

## 1. Everything commissioned went through

`Interval.lean` is delivered complete: `IsCrookedIv`, `isCrookedIv_minIdx_maxIdx`,
`IsCrookedIv.isCrookedSeq`, `badSeq_not_realizable`, `fpSeq_not_realizable`, the four `…Iv`
statements, `f2PrimeIv_of_exitReachIv` and `theorem3_of_F2PrimeIv`, all proved.

**Which route the non-realizability proofs took.** The decision-tree route, not `decide`, and
the trees are shorter than the commission's. Each witness needs exactly **two** instances of the
crookedness clause; `census-batch20.py greedy` verifies exhaustively, over all `2⁹` respectively
`2¹⁴` patterns of `σ`, that those two instances kill every pattern.

* `badSeq = 1,2,3,2,3,4,3,4,5`. If `σ 2 = 4`, the instance `(s,t,h,k) = (0,2,1,4)` asks for two
  links strictly between indices `0` and `2`, and there is one. If `σ 2 = 3`, the instance
  `(0,8,1,5)` asks for a link whose interval contains `4` — hence at an index carrying level `3`
  or `4`, so index `2` or later — followed by a *later* one whose interval contains `2` — hence
  at an index carrying level `1` or `2`, so index `3` or earlier. Only `r = 2, r' = 3` fits, and
  `σ 2 = 3` rules it out. (The commission's tree starts with `(0,8,1,5)` at `s = 0` and then
  `s = 3`, `s = 1`; the case split on `σ 2` is shorter.)
* `fpSeq = 5,4,3,3,2,3,2,1,2,3,2,1,1,0`. The instance `(0,7,5,1)` forces `r ∈ {4,6}` and then
  `r' = 5` with `σ 5 = 4`; the instance `(5,7,4,1)` then asks for two links strictly between
  indices `5` and `7`. No case split on `σ 0` or `σ 3` is needed, so the commission's five-level
  tree collapses to two steps.

In Lean each step is: read off from the width clause that the interval at an index is
`{ρ t, ρ t + 1}`; obtain `r, r'` from the crookedness clause; bound their positions by two
`decide`-checked facts about the level sequence (which indices carry which levels); finish with
`omega`. No brute force over patterns appears in the proofs.

**Whether the batch-16 assembly copied over cleanly.** Yes, verbatim. No lemma in the chain
consumes crookedness directly — `f2PrimeTight_of_exitReachTight` only passes it to its three
hypotheses — so `IsCrookedIv ρ σ` is passed in its place and `IsCrookedIv.isCrookedSeq` is never
needed inside the assembly. `theorem3_of_F2PrimeIv` is batch 9's proof with
`isCrookedSeq_minIdx` replaced by `isCrookedIv_minIdx_maxIdx` and `σ := maxIdx`.

**What was supplied.** (i) In `isCrookedIv_minIdx_maxIdx`, the step the commission flags: with
width at most one there is no coarse index strictly between `minIdx t` and `maxIdx t`, so the
value `h` given by the crookedness clause *is* one of the two, and the link lies in it by
`minIdx_subset` or `maxIdx_subset`. This is packaged as `crookedIv_step`, one application of
`IsCrookedIn'` read on containing indices, which also handles the reversal of the roles of `r`
and `r'` in the descending case. (ii) The two decision trees above.

## 2. The finding: the batch-16 route fails over the interval model too

The commission's premise — "over the faithful model, the batch-16 route is unbroken" — is false,
and this is the substance of the batch. `HPC/Fold/IntervalWitness.lean` proves

* `not_exitReachIv : ¬ ExitReachIv`,
* `not_f2PrimeIv : ¬ F2PrimeIv`,
* `not_lowExitPeakIv : ¬ LowExitPeakIv`,

each at a **genuine interval chain**: the witnesses come with an explicit `σ` and a machine-
checked proof that `IsCrookedIv ρ σ` holds, so they are not refutations by non-chains in the way
the batch-15 and batch-19 witnesses were. What the interval model buys is exactly the negative
direction — a sequence carried by no `σ` is the minimal-index sequence of no chain — so these
witnesses are not yet known to be minimal-index sequences of actual chains either; but they can
no longer be excluded by the argument of §3 of the commission, which is what killed the earlier
ones.

The two witnesses:

    ExitReachIv, F2PrimeIv   ρ = 9,8,7,8,7,6,7,6,6,5,6,6,7,8,7,6,6,5,6,5,5,4     basepoint 15
                             σ = 9,8,7,8,7,6,8,6,7,5,7,6,7,8,7,6,7,5,7,5,6,4

    LowExitPeakIv            ρ = 5,6,6,7,8,7,6,6,5,6,5,5,4,5,6,5,6,5,5,4,5,4,4,3 basepoint 2
                             σ = 5,7,6,7,8,7,6,7,5,7,5,6,4,5,6,5,7,5,6,4,6,4,5,3

For the first, `p = 6`, `H = 9`, `L = 4`; the backward arm's peak demand is `9`, so the bump
height is the cap `hStar = 8`, while the forward arm's phase-adjusted reach is only `7`; dually
`lStarArm G = 4` gives `lStar = 5` while the reflected backward arm reaches only `−6`. Both arms
of both disjuncts therefore fail, for `OkLam`/`OkVee` and for `SegLam`/`SegVee` alike. For the
second, `p = 6`, `H = 8`, `L = 3`, `lStar = 5`; index `4` is admissible on the forward arm and
the arm dips to `3` at index `21` without reaching `H − 1 = 7` in between.

`HighExitValleyIv` is *not* refuted: no census run has produced a failure of it.

Two tools were needed and are in the same file. `IsCrookedIvCheck` is the finite form of
`IsCrookedIv` — the integers `h`, `k` are replaced by two Booleans selecting the ends of the two
intervals — and `isCrookedIv_of_check` derives the model from it; this is what makes membership
in the model `decide`-able on concrete data. (Instance synthesis for the resulting proposition
needs `synthInstance.maxSize` raised.)

`theorem3_of_F2PrimeIv` stands, as `theorem3_of_F2PrimeTight` and `theorem3_of_F2PrimeFree` do,
but its hypothesis is now known to be false, so it does not deliver Theorem 3.

## 3. Census

`census-batch20.py` enumerates *interval chains* — pairs `(ρ, σ)` with `ρ` 1-Lipschitz,
`ρ t ≤ σ t ≤ ρ t + 1`, and the interval crookedness clause satisfied for every pair of indices —
and scores the four `…Iv` statements at the tight reading `H = max ρ`, `L = min ρ`, by the very
checkers used in the batch-18/19 censuses (imported from `census-batch19.py`).

    python3 census-batch20.py iv 10 6
      6 levels, length ≤ 10: 22 779 004 crooked interval chains (61 990 distinct ρ),
      221 711 036 basepoints, 20 647 632 instances with L + 3 ≤ H
      ExitReachIv / HighExitValleyIv / LowExitPeakIv / F2PrimeIv: no failure

    python3 census-batch20.py random 400 30 9 1
      400 random crooked interval chains of length 30 on 9 levels, 7 650 instances: no failure

    python3 census-batch20.py random 20000 60 12 7
      20 000 random crooked interval chains of length 60 on 12 levels, 1 072 800 instances:
      ExitReachIv, LowExitPeakIv and F2PrimeIv all FAIL; HighExitValleyIv does not

    python3 census-batch20.py random 40000 80 14 11
      40 000 random crooked interval chains of length 80 on 14 levels, 3 032 720 instances:
      ExitReachIv, LowExitPeakIv and F2PrimeIv fail again; HighExitValleyIv still does not

So the commission's negative census is reproduced and extended — nothing fails below length 11
on six levels — and the statements nevertheless fail once the chains are long enough and the
levels many enough. The failures were shrunk (end cuts, interior deletions and `σ`
simplification, each step rechecking that the result is still a crooked interval chain that
still fails) to the two witnesses above, of lengths 22 and 24, and those are what the Lean file
carries; the Lean proofs, not the script, are the evidence.

`python3 census-batch20.py witness` rechecks the two non-realizability results independently:
of the `2⁹` and `2¹⁴` interval patterns over `badSeq` and `fpSeq`, none is crooked.

## 4. Status of the route

| statement | sequence model (`IsCrookedSeq`) | interval model (`IsCrookedIv`) |
|---|---|---|
| `ExitReach` | false (batch 19, tight form) | **false** (this batch) |
| `HighExitValley` | false (batch 19, tight form) | open — no failure found |
| `LowExitPeak` | false (batch 19, tight form) | **false** (this batch) |
| `F2Prime` | false (batch 19, tight and free forms) | **false** (this batch) |
| assembly and Theorem 3 from `F2Prime` | proved, hypothesis false | proved, hypothesis false |

The refutations of batch 15 and batch 19 were by non-chains, as the commission says; but
replacing the model does not save the route. What is now known to be false is the *conclusion*
`F2PrimeIv` itself, over the model the commission calls faithful, so no repair of the three
hypotheses can restore this path to Theorem 3. Any next attempt has to weaken what is asked of
the fold — the free form `F2PrimeFree` of batch 19 is already refuted in the sequence model, and
its interval-model analogue is the natural next question — or abandon the one-bump reading.
