# Report: batch 29 — `S3ZigFree`

Delivered: `HPC/Fold/ZigFree.lean` (new), `HPC.lean` (import added), `census-batch29.c` with
its output `census-batch29.log`, and this report. Nothing else was touched. The whole project
builds; the new file has no `sorry`, `admit`, `axiom`, `native_decide` or `@[implemented_by]`
outside the commented-out conjecture block at the end, no linter warnings, and every theorem in
it has axiom profile inside `propext`, `Classical.choice`, `Quot.sound`.

---

## 1. No counterexample to `S3ZigFree`

**None was found, and the census is exact.** `census-batch29.c` decides `FoldsOnto` exactly, by
bitmask reachability over walk times, and enumerates itineraries by iterative deepening on the
number of turning targets, so the first walk that serves a basepoint has the least turn count.
One `O(n)` sweep per walk resolves every basepoint of the chain at once.

* every basepoint of `bing 0 4` … `bing 0 12` (13 861 links at span twelve): **0 unserved**;
* 4 000 random subchains of `bing 0 12` of span ≥ 9: **0 failures**, 0 basepoints;
* 8 025 grid subchains (stride 97) of `bing 0 12` of span ≥ 9: **0 failures**;
* a second run with a different seed reproduced both subchain figures.

The contrast with batch 28 is exactly at the extremes: in the same run, `IsZig` leaves **2**
basepoints unserved at *every* span — the two chain endpoints, at extreme levels — while
`IsZigFree` leaves none. That is the `zig_base_lower` / `zig_base_upper` obstruction and its
repair, seen side by side.

Section 2 of the census is a direct check of this batch's theorem: at every span from four to
twelve, every basepoint of `bing 0 N` whose level is within two of an extreme (226 of them at
span twelve) is served by the corresponding ladder, `[L+1, H−1, L+1]` below and
`[H−1, L+1, H−1]` above. That is a check of the statement `s3ZigFree_near_extreme`, which is
proved in Lean.

---

## 2. The reconciliation asked for in §0

**Both tables are right, and neither counts the base level. They minimise over different sets
of itineraries.** The convention is the same in both: an itinerary is a base centre `ts[0]`
followed by `k` turning targets, and the number reported is the maximum over basepoints of the
least `k` that works. What differs is the set searched: batch 26 searched **all free zigzags**
(alternating directions, nothing else), batch 28 searched **inside the family**, where `k ≥ 2`
is forced by `3 ≤ ts.length` and the amplitudes and the ending are constrained too.

Recomputed here, exhaustively, in all three regimes at spans four to twelve
(census §1):

| span | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|
| free zigzags (batch 26's quantity) | 1 | 1 | 2 | 2 | 3 | 3 | 4 | 4 | 5 |
| inside `IsZig` (batch 28's quantity) | 2 | 2 | 2 | 3 | 3 | 3 | 4 | 4 | 5 |
| inside `IsZigFree` | 2 | 2 | 2 | 2 | 3 | 3 | 4 | 4 | 5 |

The first row reproduces batch 26's table exactly, and it is `⌊span/2⌋ − 1` at every span from
four to twelve. The commission's independent recomputation is reproduced too, including the
span-8 distribution: least `k` equal to `1` at 90 basepoints, `2` at 311, `3` at 8. The second
row reproduces batch 28's table exactly.

So **the sentence to strike is batch 28's "this is `⌊span/2⌋ − 1` at every span"**, not its
numbers. The correct statements are:

* over free zigzags the maximum least turn count is `⌊span/2⌋ − 1`, spans four to twelve —
  this is the reversal law, and it is batch 26's row;
* inside `IsZigFree` it is `max(2, ⌊span/2⌋ − 1)`: the family cannot use fewer than two
  turning targets, so the law is invisible below span eight and identical to it from span
  eight on;
* inside `IsZig` it is the same except at span seven, where it is `3` rather than `2`: the
  strict increase from the first amplitude costs one extra turn there.

The law itself — the argument that no family with a bounded number of turns can work — rests
on the first row, which is now confirmed twice.

---

## 3. `s3ZigFree`: not proved, and what is closed

`s3ZigFree` is **not proved and not refuted**. It is kept, commented out, at the end of
`HPC/Fold/ZigFree.lean`, together with `s3` and `theorem3`, which would follow from it through
the already proved `s3_of_s3ZigFree` and `theorem3_of_S3`.

What is closed, unconditionally:

**Every basepoint within two of an extreme, at any span** (`s3ZigFree_near_extreme`). This is
the range in which `IsZig` has no walk at all, so it is the part of the statement the exemption
was introduced for, and it is now a theorem. The proof is the *tracking fold*: the walk of
`[L+1, H−1, L+1]` climbs the whole band one level per step, and the token is put at

```
β j = min (min (f j − (L+1)).toNat (H − L − 2).toNat) j,
```

the arm's own level, clamped to the band, and held back so that it never runs ahead of the
index. The clamp handles the two ends of the band, and the hold-back is what covers a start at
`L + 2` rather than `L + 1`: where it bites, the arm has ascended at full speed from `L + 2`,
so the token is exactly one level behind, which the slack allows. The mirror walk
`[H−1, L+1, H−1]` does the upper case. No crookedness is used.

**Hence every span up to five** (`s3ZigFree_span_five`), since at span five and below every
level is within two of an extreme, and **the reduction of the rest to the interior**
(`s3ZigFree_of_interior`): `S3ZigFree` follows from its restriction to basepoints with
`L + 3 ≤ ρ i ≤ H − 3`. Only spans six and above carry any content.

**The family is closed at the open end** (`isZigFree_cons`): a zig sequence may be prefixed by
a sweep of arbitrary amplitude and the result is a member of the free family, provided only
that the new step alternates with the old first one. Since `zigWalk` starts at the head of the
sequence, this is the step that moves a walk's start to where a basepoint needs it, and it is
exactly what the exemption of the first amplitude buys. `isZigFree_base_free` — the §2 item —
is the extreme case of the same phenomenon.

**The near-extreme range is sharp, as long as the crookedness is unused**
(`no_zigWalk_fold_veeSeq`, `not_near_extreme_three`). Three levels in the argument above must
fail, and not only for this family: the straight descent `6, 5, 4, 3, 2, 1, 0`, based at its
middle (level `3 = L + 3 = H − 3`), is 1-Lipschitz and confined to `[0, 6]`, and **no walk of
unit steps serves it at all**. Its forward arm is at `L` three indices on and its backward arm
is at `H` three indices back; a token that starts at time `0` is at time `u` at a position at
most `u`, so it would have to be within one of `L` and within one of `H` at two times at most
three apart, while the walk moves one level per step and needs `H − L − 2 = 4` steps between
those two levels. The sequence is of course not crooked — that is the point: the interior cases
left by `s3ZigFree_of_interior` cannot be settled without using the crookedness, so the
induction has to be carried by the cut, as §3 of the commission says.

**Why no induction is claimed.** The two constraints from the record both bind. The reversal
law (§2 above, first row) says the itinerary must acquire turns in proportion to the span, so a
step that adds one turn must reduce the span by about two; and no black-box extension
hypothesis is admissible (batch 27 §4), so the extension must be constructed with the middle
piece's itinerary. The pieces available are `crookedIvF_cut_first` (the cut at its first
crossings, with the two pieces banded) and `foldsFrom_split` (gluing two folds at a split
index), both from batch 26. What is missing is the construction that takes a member of the
family for the middle piece, on the band `[L+2, H−2]`, and produces a member for the whole on
`[L, H]` whose walk the outer pieces can track at the right times: the ladder argument of this
batch gives the outer pieces for free only when the basepoint is near an extreme, which is
precisely the case already closed. Attempting it at a basepoint three levels in reproduces the
timing obstruction of `no_zigWalk_fold_veeSeq`, which the crookedness — and only the
crookedness — removes.

---

## 4. What is in the Lean file

`HPC/Fold/ZigFree.lean`, in order:

* `isZigFree_base_free` — the §2 item: `[L+1, H−1, L+1]` is `IsZigFree` when `L + 3 ≤ H`.
* `isZigFree_cons` — closure at the open end.
* `ladderUp`, `ladderDown`, with `isZigFree_ladderUp`, `isZigFree_ladderDown`.
* `stepRun_getD_up`, `stepRun_getD_down` — the values of a step run.
* `zigLevels_ladderUp`, `zigLevels_ladderDown`, `zigWalk_ladderUp_length`,
  `zigWalk_ladderDown_length`, `zigWalk_ladderUp_val`, `zigWalk_ladderDown_val` — the walk of a
  ladder, and its level at each time of the first leg.
* `foldsOnto_ladderUp`, `foldsOnto_ladderDown` — the tracking fold.
* `s3ZigFree_near_extreme`, `s3ZigFree_of_interior`, `s3ZigFree_span_five`.
* `zigWalk_dist_le`, `veeSeq`, `veeSeq_isLip`, `veeBase`, `veeG`, `veeT`,
  `no_zigWalk_fold_veeSeq`, `not_near_extreme_three` — the sharpness section.
* the conjecture block, commented out: `s3ZigFree`, `s3`, `theorem3`.

---

## 5. Not attempted

As §5 of the commission directs: the linear-time far-index check that would make
`¬ F2PrimeOff` unconditional; Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9
gap.
