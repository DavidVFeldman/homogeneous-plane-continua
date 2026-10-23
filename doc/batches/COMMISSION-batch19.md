# Commission: batch 19 — the tight conjectures, search permitted

**Go!** Runs on top of the batch-18 delivery. One new file, `HPC/Fold/ClosureTight.lean`; root
`HPC.lean` updated. Nothing else touched.

## Protocol

As batch 18: search permitted, time unbounded, the English is a sketch. Census, axiom audit, no
silent weakening. **A counterexample to any of the three is a success; report it first.** If a
conjecture is refuted, replace its theorem by the negation with the witness and drop the
corollaries. A run that proves none and refutes none is a legitimate outcome; keep sound
partials and say how far the search got.

Available: everything in `HPC/Fold/`, including batch 18's `not_segLam_of_no_peak`,
`hReach_le_of_all`, and the tight definitions with `highExitValleyTight_iff_open` and
`f2PrimeTight_of_exitReachTight`.

## 1. The statements

The batch-18 tight forms: `ExitReachTight`, `HighExitValleyOpenTight`, `LowExitPeakTight`,
each with `(∃ t, ρ t = L) → (∃ t, ρ t = H)` added to the loose form. Evidence: 7 042 754
basepoints under the down form with attained extremes (batch 16's census), no failure; random
down-crooked sequences to length 60 on twelve levels, no failure.

## 2. A retraction of the batch-18 sharpened target

Batch 18 §4 proposed: *tight and open and non-vacuous implies `L = p − 2`*, on the ground that in
its corpus (length ≤ 12, six levels) every instance where a valley clause has bite has the shape
`(hStar − p, H − 1 − hStar, L − (p − 2)) = (0, 1, 0)`. **That is a small-corpus artifact.** With
attained extremes, at greater length, three further shapes occur. Explicit down-crooked
witnesses, all with `H = max ρ` and `L = min ρ`, and in each the Λ-valley clause has bite and
holds:

**Shape `(0, 1, −1)`.** `ρ = 2,1,1,2,1,1,2,3,2,3,4,3,2,3,4,4,3,4,4,5,6,5,4,4`, basepoint 10, so
`p = 4`, `H = 6`, `L = 1`, `hStar = 4`. Forward arm `4,3,2,3,4,4,3,4,4,5,6`: peak index 0, first
drop at 2 to level 2, first exceed of `hStar + 1 = 5` at index 10. The visit is the drop
itself: `L + 1 = 2 = A 2`. So when `L = p − 3` the drop index is the visit.

**Shape `(0, 2, 0)`.** `ρ = 5,4,3,3,4,3,3,3,2,3,2,2,1,2,2,3,2,1,2,2,1,0,1,2`, basepoint 23, so
`p = 2`, `H = 5`, `L = 0`, `hStar = 2`. Backward arm `2,1,0,1,2,2,1,2,3,…,4`: peak index 0,
first drop at 2, first exceed at 19. Visit at index 1, level `1 = L + 1 = p − 1`: the pre-drop
level, as in the trivial shape. `H = p + 3` changes nothing.

**Shape `(1, 1, 0)` — the real case.** `ρ = 4,4,3,4,5,4,5,4,4,3,4,3,2,2,3,2,1,2,3,2,2,2,2,3,3,2,
1,2,1,0,0,1,1,2,2,3,3,3,3,2`, basepoint 33, so `p = 2`, `H = 5`, `L = 0`, `hStar = 3`. Backward
arm `2,1,1,0,0,1,2,1,2,3,3,2,2,2,2,3,2,1,2,3,2,2,3,4,3,4,4,5`: first drop at index 3, **peak
index `s = 6`, after the drop** (the arm reaches `hStar = 3` only phase-adjusted, at `A = 2` with
phase 1), first exceed at 27. The pre-drop level at index 2 is `1 = L + 1` but lies *before*
`s`, so it does not serve. The visit is a **second dip** to `L + 1` at index 7, after the peak.

So `L = p − 2` is not forced, the peak index need not precede the first drop, and the visit
need not be the pre-drop level. The valley clause holds in all three, and in the third by the
mechanism of §3.

## 3. Sketches

### `HighExitValleyOpenTight`

Let the arm `A` exceed `hStar + 1` at `u ≥ s`. By batch-17's `demands_lt_of_open` and
`exists_drop_before_exceed`, `A` has a first drop `d < u`.

*The mechanism, from the `(1, 1, 0)` witness.* There, `L` is attained on `A` at index 3 and
`A u = 5`. Crookedness on the pair `(3, 27)` — levels `0` and `5`, gap `5` — gives `r < r'`
strictly between with `A r ∈ [3, 4]` and `A r' ∈ [0, 1]`. Since `A r ≥ 3 = hStar`, the
phase-adjusted level at `r` is at least `hStar`, so `r ≥ s`. Then `r' ∈ (r, u) ⊆ [s, u)` with
`A r' ≤ L + 1`: the visit. In general: **if `L` is attained on `A` at an index `ℓ < u`, then the
pair `(ℓ, u)` has gap `A u − L ≥ hStar + 2 − L ≥ 3`, and crookedness supplies `r` with
`A r ≥ A u − 2 ≥ hStar` — hence `r ≥ s` — followed by `r'` with `A r' ≤ L + 1`, and `r' ∈ [s, u)`.**
This is where attainment of `L` enters: with a slack `L` the near-source window
`[L, L + 1]` need not contain any value the arm takes.

So the sketch reduces to: *in the open non-vacuous case, `L` is attained on the exceeding arm
before its exceeding index.* In every instance examined it is. Why it must be: if `L` is
attained only on the other arm `B`, at index `ℓ_B`, apply crookedness to the pair `(ℓ_B, u)`
across the basepoint; the near-target witness `r` has level `≥ hStar`, and if it lies on `A` the
argument above closes. If it lies on `B`, then `B` reaches level `≥ hStar ≥ ` its own demand
… — this branch is the one to work out, using that in the open case both demands are strictly
below `H − 1` (`demands_lt_of_open`) while `B` attains `L`. The trivial shape is the case
`L = p − 2`, where the pre-drop level is `L + 1` and `s = 0`.

### `LowExitPeakTight`

The reflection of `HighExitValleyTight`, which by batch 13 cannot be obtained by reflecting a
proof that uses crookedness. Rerun the argument above on the descending case of
`IsCrookedSeq`, whose windows are `[f t, f t + 1]` and `[f s − 2, f s − 1]`. Note the near-source
window is now two below the source; the mechanism's "`A r' ≤ L + 1`" becomes "`A r' ≥ H − 1`"
on this side with the bounds shifted, and the shift is what the proof must carry.

### `ExitReachTight`

Unchanged from batch 18 §3, with `L` and `H` now attained. The branch that has broken every
earlier formulation is the arm that does *not* fail the Λ side; the candidate mechanism is
`sync` (batch 7) across the failing arm's drop and the other arm's rise, with the window intact
between them. The floor `min (L + 1) p` in `lStar` and the cap `max (H − 1) p` in `hStar` are
what make the two sides complementary, and — as batch 18 showed — only when the extremes are
attained. A proof must use attainment at exactly those two points.

## 4. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample; which of the three were proved, with the actual
   mechanism; for any not proved, how far the search got, and in particular whether the
   sub-claim "`L` is attained on the exceeding arm before its exceeding index" was established,
   refuted, or left open.

## 5. If all three fall

`f2PrimeTight` and `theorem3` follow by the lines in the skeleton, and Bing 1948 Theorem 3 in
the block reading is unconditional.
