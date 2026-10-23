# Report — batch 18: the three conjectures

One new file, `HPC/Fold/Closure.lean`; root `HPC.lean` as supplied by the batch; the commission
text kept as `COMMISSION-batch18.md`. Nothing else in the project was touched. The census
script is `census-batch18.py`, added for reproducibility.

`lake build` succeeds. The new file contains no `sorry`/`admit`/`axiom`/`native_decide`/
`implemented_by` and elaborates with no linter warnings. Axiom profiles: `exitSeq_pt`,
`valleySeq_pt`, `peakSeq_pt` use `[propext, Quot.sound]`, the `decidableNonAscAt` instance uses
none, and every other declaration uses `[propext, Classical.choice, Quot.sound]`.

## 0. Counterexamples, first

**All three conjectures are false as stated. So is `F2Prime`.**

| statement | witness `ρ` | `i` | `H` | `L` | Lean |
|---|---|---|---|---|---|
| `ExitReach` | `0,1,2,1,2,2,3,4` | 2 | 4 | −1 | `not_exitReach` |
| `F2Prime` | `0,1,2,1,2,2,3,4` | 2 | 4 | −1 | `not_f2Prime` |
| `HighExitValleyOpen` | `2,1,0,1,2,1,2,2,3,4` | 0 | 4 | −2 | `not_highExitValleyOpen` |
| `HighExitValley` | as above | 0 | 4 | −2 | `not_highExitValley` |
| `LowExitPeak` | `0,1,2,1,2,2,3,4,3,2` | 9 | 6 | 0 | `not_lowExitPeak` |

Every witness is 1-Lipschitz and down-crooked (`IsCrookedSeq`, by `decide` on the definition),
and satisfies `∀ t, L ≤ ρ t`, `∀ t, ρ t ≤ H`, `L + 3 ≤ H`; in the `HighExitValleyOpen` witness
the cap genuinely does not bind, so that hypothesis is met too.

**None of this contradicts any earlier census, and none of it is about crookedness.** The
failures come from a place nobody had looked: the extremes `H` and `L` are universally
quantified in all four statements, subject only to `L ≤ ρ ≤ H` and `L + 3 ≤ H`, whereas every
census — batch 16's 7 042 754 basepoints included, and the new one below — was taken with `H`
and `L` set to the sequence's own maximum and minimum. A *strict* bound is admissible in the
statements, and the two sides of the dichotomy do not degrade symmetrically when it is
loosened:

* `hStar = min (max (max dG dT) (max p (L+1))) (max (H−1) p)` is **capped** at `max (H−1) p`.
  Raising `H` above `max ρ` raises the cap, so it raises the height the Λ side must reach —
  up to the uncapped maximum of the two demands, which batch 15's `not_agreement` already shows
  an arm can miss.
* `lStar = max (min (min lG lT) (min p (H−1))) (min (L+1) p)` is **floored** at `min (L+1) p`.
  Lowering `L` below `min ρ` lowers the floor, so it lowers the depth the V side may stop at.

With tight extremes, whichever side is in trouble is rescued by its cap or its floor — which is
precisely the mechanism §2 of the commission describes and the corpus confirms. With slack
extremes both protections are removed at once, and a single sequence can fail both sides.

### The `ExitReach` and `F2Prime` witness in detail

`ρ = 0,1,2,1,2,2,3,4`, basepoint `i = 2`, so `p = 2`; arms `G = 2,1,2,2,3,4` and `T = 2,1,0`.
Demands: `hStarArm G = 4`, `hStarArm T = 2`, `lStarArm G = 1`, `lStarArm T = 0`. Take `H = 4`
(the true maximum — no slack at all) and `L = −1` (one below the true minimum).

* `hStar = min (max 4 2) (max 3 2) = 3`. The backward arm drops to `p − 2 = 0`, so the Λ side
  needs `hReach T 2 ≥ 3`; but `T + phase = 2, 2, 1`, so `hReach T 2 = 2`. **`OkLam T` fails.**
* `lStar = max (min 0 2) (min 0 2) = 0` — the floor `min (L+1) p` has dropped from `1` to `0`.
  The forward arm rises to `p + 2`, so the V side needs `hReach (−G) (−2) ≥ −lStar = 0`; but
  `−G + phase = −2, −1, −1, −1, −2, −3`, so `hReach (−G) (−2) = −1`. **`OkVee G` fails.**

With `L = 0` the floor puts `lStar = 1`, `OkVee G` holds, `OkVee T` holds vacuously (the
backward arm never rises), and `ExitReach` is satisfied at this basepoint by its V branch.
So the witness is sharp: one unit of slack in `L`, and no slack in `H`, is exactly enough.

`F2Prime` fails at the same instance for the same reason, one level lower down: no index of `T`
has `T j + phase T j ≥ hStar = 3`, so any `SegLam` for `T` must take `s = m`, and then clause
(1) fails because `T 2 = 0 < p − 1`; symmetrically no index of `−G` reaches `−lStar = 0`, so
any `SegVee` for `G` must take `s = m`, and clause (1) fails because `−G 5 = −4 < −p − 1`. This
is the reusable lemma `not_segLam_of_no_peak`.

### The two valley witnesses

`HighExitValleyOpen` at `ρ = 2,1,0,1,2,1,2,2,3,4`, `i = 0`, `H = 4`, `L = −2`: both demands are
`2` (the forward arm drops to `0` at index 2), so `hStar = 2` and the cap `max (H−1) p = 3`
does not bind — the basepoint is open, as the hypothesis requires. `s = 0` is admissible, the
arm reaches `4 > hStar + 1 = 3` at its last index, and the clause therefore demands a visit to
`L + 1 = −1`; the sequence never goes below `0`. Two units of slack in `L` are needed here,
because at `L = −1` the visit to `0` exists.

`LowExitPeak` at `ρ = 0,1,2,1,2,2,3,4,3,2`, `i = 9`, `H = 6`, `L = 0` (`L` tight, `H` two above
the maximum): both valley demands are `2`, so `lStar = 2`; the backward arm — the sequence read
from the right — ends at `0 < lStar − 1`, `s = 0` is admissible, and the clause demands a visit
to `H − 1 = 5` before it; the sequence never exceeds `4`.

## 1. What survives, and what replaces the three

Everything downstream of `F2Prime` survives, because `theorem3_of_F2Prime` never used the
general form: it constructs `L` and `H` as `ρ tL` and `ρ tH`, the attained minimum and maximum
of the sequence it builds. The file therefore states the **tight** forms — `F2PrimeTight`,
`ExitReachTight`, `HighExitValleyTight`, `HighExitValleyOpenTight`, `LowExitPeakTight`, each
with `∃ t, ρ t = L` and `∃ t, ρ t = H` added and nothing else changed — and proves the three
structural facts that carry the old chain over to them:

* `highExitValleyTight_iff_open` — batch 17's shrinking, verbatim, in tight form;
* `f2PrimeTight_of_exitReachTight` — batch 16's assembly, verbatim, in tight form;
* `theorem3_of_F2PrimeTight` — **Bing 1948 Theorem 3**, block reading, three-link form, from
  `F2PrimeTight` alone.

So the statement of the objective is unchanged and the route to it is intact; what has to be
re-conjectured is the tight form of the three. Both attainment hypotheses are needed: `F2Prime`
still fails with `L` tight and `H` slack (`ρ = 0,1,2,1,2,2,3,4`, `i = 5`, `H = 5`, `L = 0`) and
with `H` tight and `L` slack (the witness above), so neither can be dropped alone.

The commissioned `exitReach`, `highExitValleyOpen`, `lowExitPeak` and their corollaries
`highExitValley`, `f2Prime`, `theorem3` are deleted as the commission directs — kept verbatim,
commented out, at the end of the file, with a pointer to `theorem3_of_F2PrimeTight`.

## 2. Census

`census-batch18.py`. Exhaustive enumeration of 1-Lipschitz sequences on six levels, filtered
for the down form `IsCrookedSeq`, over every basepoint, in two readings.

**Tight** (`H = max ρ`, `L = min ρ`; instances counted are those with `L + 3 ≤ H`):

| levels | lengths | crooked sequences | instances | failures |
|---|---|---|---|---|
| 6 | 1 – 13 | 315 225 | 1 710 562 | none, for any of the five statements |
| 7 | 1 – 13 | 1 443 481 | 6 684 572 | none, for any of the five statements |

The seven-level run uses the depth-first mode of the script, which prunes a prefix as soon as
it carries a crookedness violation — a violation inside a prefix can never be repaired by
extending it.

**Slack** (`max ρ ≤ H ≤ max ρ + 2`, `min ρ − 2 ≤ L ≤ min ρ`, `L + 3 ≤ H`):

| lengths | instances | `ExitReach` | `HighExitValley(Open)` | `LowExitPeak` | `F2Prime` |
|---|---|---|---|---|---|
| 1 – 11 | 3 699 948 | fails | fails | fails | fails |

The five witnesses tabulated in §0 are the smallest failures in this enumeration, ordered by
length first and then by total slack `(H − max ρ) + (min ρ − L)`. This is an exploratory
computation in a separate script, not a Lean-checked claim; the Lean-checked claims are the
five `not_` theorems, which depend on no census.

## 3. On the sketches of §3 of the commission

The mechanisms suggested there were not used, and the reason is worth recording: each sketch
argues within a fixed basepoint and reasons from `L` and `H` as if they were the attained
extremes. For `HighExitValleyOpen`, §3 identifies the four shapes
`(hStar − p, H − 1 − hStar, L − (p − 2))` seen in the corpus and observes that in the dominant
shape `(0,1,0)` the visit is the pre-drop index, where `A = p − 1 = L + 1`. That step is exactly
what fails when `L` is a strict lower bound: `A (d−1) = p − 1` is still true, but it is no
longer `≤ L + 1`. The refuting sequence is in shape terms `(0, 1, −2)`, which the corpus cannot
produce because `L` there is attained. The same remark applies to the `ExitReach` sketch, where
"the cap on the V side" is the floor `min (L+1) p`, and to `LowExitPeak`, where the reflected
cap is `min p (H−1)`.

In tight form the sketches are untouched by any of this and remain the natural line of attack.

## 4. Status of the tight conjectures

Not proved and not refuted. Beyond the census above, the work done on them in this batch was
the analysis that produced the refutations: the observation that the cap and the floor are what
make the two sides of the dichotomy complementary, and that they are complementary only when
the extremes are attained. That is a constraint on any proof of the tight forms — it says the
proof must use attainment, and not merely `L ≤ ρ ≤ H`, at exactly the two points where the
slack witnesses break: the identification of `A (d−1) = p − 1` with a visit to `L + 1`
(Λ side) and the floor `min (L+1) p` in `lStar` (V side). The three tight statements are
recorded so that the next batch has them in the form the corpus actually supports.

### A sharpened target for the next batch

One piece of new evidence, from the tight corpus at lengths at most 12 on six levels. Count the
*bite* instances — an arm and an admissible index `s` at which the clause is not vacuous,
i.e. some `u ≥ s` really does exceed `hStar + 1` (respectively fall below `lStar - 1`):

| side | bite instances | shapes observed |
|---|---|---|
| Λ, shape `(hStar − p, H − 1 − hStar, L − (p − 2))` | 226 | `(0, 1, 0)` only |
| V, shape `(p − lStar, lStar − (L + 1), (p + 2) − H)` | 226 | `(0, 1, 0)` only |

So in every non-vacuous tight instance in this corpus, `hStar = p`, `L = p − 2` and `H = p + 2`
on the Λ side, and the mirror image on the V side: the whole configuration lives in the
five-level window `[p − 2, p + 2]`. If that can be proved — *tight and open and non-vacuous
implies `L = p − 2`* — both valley conjectures become bookkeeping, because then the visit
demanded is a visit to `L + 1 = p − 1`, which `pre_drop_eq` (batch 17) already supplies at the
index before the first drop, and `hStar = p` forces `s = 0`, so the visit lies in range. That
implication is exactly the step the slack witnesses destroy, and it is where attainment of the
extremes has to enter.
