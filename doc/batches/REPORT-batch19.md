# Report — batch 19: the tight conjectures, and the end of the one-bump route

One new file, `HPC/Fold/ClosureTight.lean`; root `HPC.lean` as supplied by the batch; the
commission text kept as `COMMISSION-batch19.md`. Nothing else in the project was touched. The
census script is `census-batch19.py`, added for reproducibility.

`lake build` succeeds. The new file contains no `sorry`/`admit`/`axiom`/`native_decide`/
`implemented_by` outside the commented-out block of commissioned statements, and elaborates
with no linter warnings. Every declaration in it has axiom profile within
`[propext, Classical.choice, Quot.sound]`.

## 0. Counterexamples, first

**All three tight conjectures are false. So is `F2PrimeTight`. So, and this is the substantive
point, is the free form `F2PrimeFree`, in which the bump height, the valley depth and the
bounds `H`, `L` are all existentially quantified.**

| statement | witness `ρ` | `i` | `H` | `L` | Lean |
|---|---|---|---|---|---|
| `ExitReachTight` | `5,4,3,3,2,3,2,1,2,3,2,1,1,0` | 5 | 5 | 0 | `not_exitReachTight` |
| `F2PrimeTight` | as above | 5 | 5 | 0 | `not_f2PrimeTight` |
| `F2PrimeFree` | as above | 5 | — | — | `not_f2PrimeFree` |
| `LowExitPeakTight` | `3,4,4,5,6,5,4,4,3,4,3,2,3,4,3,2,2,1` | 2 | 6 | 1 | `not_lowExitPeakTight` |
| `HighExitValleyOpenTight` | `6,5,4,4,3,4,3,2,3,4,3,2,2,1,2,2,3,4,3,2,2,1,2,1,0` | 9 | 6 | 0 | `not_highExitValleyOpenTight` |
| `HighExitValleyTight` | as above | 9 | 6 | 0 | `not_highExitValleyTight` |

Every witness is 1-Lipschitz and down-crooked (`IsCrookedSeq`, by `decide` on the definition),
and in every one of them **`H` is the maximum and `L` the minimum of the sequence**, so both
attainment hypotheses added in batch 18 hold. In the third witness the cap does not bind, so
the openness hypothesis is met as well. `python3 census-batch19.py witness` rechecks all three
independently of Lean.

Adding attainment in batch 18 was therefore necessary but not sufficient; and, unlike batch 18,
these failures are not artifacts of how the statements quantify their bounds.

### Why batch 16's and batch 18's censuses did not see them

They are all longer than any exhaustive corpus reached. The exhaustive census here —
429 562 crooked sequences of length at most 12 on six levels, 4 890 850 basepoints,
1 512 136 instances with `L + 3 ≤ H`, all read at tight extremes — still shows **no failure of
any of the six statements**. The witnesses have lengths 14, 18 and 25. They were found by
randomised depth-first dives to length 60 on twelve levels (`census-batch19.py random`), where
every seed tried produces failures of `ExitReachTight`, `LowExitPeakTight`, `F2PrimeTight` and
`F2PrimeFree`, and most produce failures of `HighExitValleyOpenTight`; they were then shrunk by
deletion and single-level perturbation, each shrink rechecked for crookedness.

## 1. The first witness in detail: there is no one-bump fold at all

`ρ = 5,4,3,3,2,3,2,1,2,3,2,1,1,0`, basepoint `i = 5`, so `p = 3`, `H = 5`, `L = 0`; arms

    G = 3,2,1,2,3,2,1,1,0        T = 3,2,3,3,4,5

Demands: `hStarArm G = 3`, `hStarArm T = 5`, `lStarArm G = 0`, `lStarArm T = 2`; hence
`hStar = min 5 (max 4 3) = 4` and `lStar = max 0 (min 1 3) = 1`.

*`ExitReachTight`.* The forward arm drops to `p − 2 = 1`, so the Λ side needs
`hReach G 3 ≥ 4`; but only the first two indices of `G` have all their predecessors at or above
`p − 1 = 2`, and there `G + phase = 3, 3`, so `hReach G 3 = 3`. The backward arm rises to
`p + 2 = 5`, so the V side needs `hReach (−T) (−3) ≥ −lStar = −1`; but
`−T + phase = −3, −2, −2, −2, −3, −4`, so `hReach (−T) (−3) = −2`. Both sides fail.

*`F2PrimeTight`.* The same two arms, one step further on: `G` has a peak index only at `4`, and
index `2` — where `G` is below `p − 1` — precedes it, so `SegLam G` fails at the height `4`;
`−T` never reaches `−lStar` in the phase-adjusted sense, so `SegVee T` fails at the depth `1`.

*`F2PrimeFree`.* The interesting part. The four lemmas `fpSeq_segLam_G_le`,
`fpSeq_segLam_T_ge`, `fpSeq_segVee_T_ge` and `fpSeq_not_segVee_G` pin down, for each side, the
heights and depths each arm admits, *for arbitrary admissible `H`, `L`*:

* `SegLam G` forces `hb ≤ 3`: index `2` is below `p − 1`, so no peak index can follow it, and
  the peak index must therefore be one of `0, 1, 2`, where the phase-adjusted level is at
  most `3`.
* `SegLam T` forces `hb ≥ 4`: at a lower height the peak index is `0`, the arm must leave the
  window by index `5` (where it is at `5 > hb + 1`), so the excursion has to be closed at a
  level `≤ L + 1 ≤ 1` — and `T` never descends below `2`.
* `SegVee T` forces `lb ≥ 2`: the negated arm's phase-adjusted levels are all at most `−2`, so
  a peak index needs `−lb ≤ −2`, and there is no peak-free alternative because the arm leaves
  the window below at its last index.
* `SegVee G` fails for every `lb ≥ 2`: if the negated arm has a peak index at all then the
  excursion it opens has to be closed at `−H + 1 ≤ −4`, and the negated arm never goes below
  `−3`; and if it has none, index `2` already violates the strictness clause.

So the two arms are separated on both sides at every admissible parameter, and there is no
one-bump fold at this basepoint. Since `SegLam` does not mention `H` and `SegVee` does not
mention `L`, and both are monotone in the remaining bound, slack bounds cannot help either —
the Lean statement quantifies over all admissible `H` and `L`, so this is proved, not assumed.

## 2. The other two witnesses

*`LowExitPeakTight`*, at `ρ = 3,4,4,5,6,5,4,4,3,4,3,2,3,4,3,2,2,1`, basepoint `2`, `p = 4`,
`H = 6`, `L = 1`. Arms `G = 4,5,6,5,4,4,3,4,3,2,3,4,3,2,2,1` and `T = 4,4,3`, with
`lStarArm G = 4`, `lStarArm T = 3`, so `lStar = 3`. On the forward arm the index `4` is
admissible — the first four phase-adjusted negated levels are `−4, −4, −5, −4`, all below
`−lStar = −3` — and at `u = 15` the negated arm is at `−1 > −lStar + 1`. The clause then
demands an index in `[4, 15)` at which the arm is at `H − 1 = 5` or above; from index `4` on it
never exceeds `4`.

*`HighExitValleyOpenTight`*, at
`ρ = 6,5,4,4,3,4,3,2,3,4,3,2,2,1,2,2,3,4,3,2,2,1,2,1,0`, basepoint `9`, `p = 4`, `H = 6`,
`L = 0`. Both arms have demand `4`, so `hStar = 4`, one below the cap `max (H − 1) p = 5`: the
basepoint is open, and batch 17's shrinking does not make the clause vacuous. Index `0` is
admissible on the backward arm `T = 4,3,2,3,4,3,4,4,5,6` — vacuously — and `T` reaches
`6 > hStar + 1` at `u = 9`, having never visited `L + 1 = 1`; it never goes below `2`.

`HighExitValleyTight` falls with it through `highExitValleyTight_iff_open`.

## 3. The sub-claim of the commission

The commission asks specifically whether *in the open non-vacuous case `L` is attained on the
exceeding arm before its exceeding index*. **It is refuted, by the third witness.** There the
exceeding arm is `T = 4,3,2,3,4,3,4,4,5,6`; `L = 0` is not attained on it at all (it is
attained at index 24 of `ρ`, which lies on the other arm), while the exceeding configuration
`s = 0`, `u = 9` is genuine. The proposed mechanism — crookedness on the pair `(ℓ, u)` with `ℓ`
an index where `L` is attained — therefore has no starting point on this arm, and the branch
the commission singled out as "the one to work out", `L` attained only on the other arm, is
exactly the branch that fails.

For the record, on the exhaustive corpus (length ≤ 12, six levels) the sub-claim holds at all
516 exceeding configurations in the open case; it is a genuine small-corpus regularity, like
the shape classification the commission retracts in its §2.

## 4. What is proved

Besides the six refutations:

* `hReach_le_of_pre` — `hReach` is bounded by any bound on the phase-adjusted levels of those
  indices whose predecessors all stay at or above `p − 1`. This refines batch 18's
  `hReach_le_of_all`, whose hypothesis is the unconditional bound; the first witness needs the
  conditional form, its arm climbing back up after leaving the window.
* `not_segLam_of_window_or_peak` — `SegLam` fails if the arm leaves the window somewhere and
  every peak index is preceded by a window violation. This generalizes batch 18's
  `not_segLam_of_no_peak` (the case of no peak index at all).
* `F2PrimeFree`, the free folding condition, and `theorem3_of_F2PrimeFree`: Bing 1948,
  Theorem 3 in the block reading still follows from it, by the two block-consolidation lemmas
  used with the supplied data rather than with `hStar` and `lStar`. The implication is proved;
  its hypothesis is false.

## 5. Where this leaves Theorem 3

`F2PrimeFree` is the weakest condition of its family: it asks only that the hypotheses of
`exists_blocks_first_of_segLam` or of `exists_blocks_first_of_segVee` be satisfiable at the
given basepoint, with every parameter free. Its refutation says that at the basepoint `5` of
the fourteen-term witness *no* one-bump itinerary receives both arms, so no repair that keeps
`SegLam`/`SegVee` as the fold target and insists on a common target for the two arms can work.

Nothing above refutes Bing's Theorem 3 itself, nor the batch-8 and batch-6 machinery: what is
refuted is the sufficiency route through a single bump at an arbitrary basepoint. Three
directions survive and are not explored here:

1. *Move the basepoint.* Theorem 3 fixes `i` only through the requirement that `d_i` lie in the
   first block; the consolidation may be built from a different anchor, and the witness may
   well admit a fold at another basepoint.
2. *Two bumps.* The two arms disagree by exactly one level on both sides in the witness; an
   itinerary with a bump and a dip — `Λ` on one arm, `V` on the other — is not in the present
   family and is not excluded by anything proved here.
3. *Weaken the block condition.* `unionRange j 3` is the three-link target; the arms are
   separated by one level, which is what a four-link target would absorb.
