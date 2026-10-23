# Commission: batch 30 — Bing's Theorem 7, and the timing bound

**Go!** Runs on top of the batch-29 delivery. One new file, `HPC/Fold/Minimal.lean`; root
`HPC.lean` updated. Nothing else touched.

## 0. On batch 29

Audited clean: thirty-seven earlier files identical, no forbidden tokens. Three things in it
are worth more than the conjecture it was aimed at.

**The reconciliation settles it.** Both tables were right and neither counted the base; they
minimise over different sets. Free zigzags give `⌊span/2⌋ − 1` — that is the reversal law, and
the row the no-bounded-family argument rests on — while inside `IsZigFree` it is
`max(2, ⌊span/2⌋ − 1)` and inside `IsZig` the same but for span seven. The sentence to strike
was batch 28's, not its numbers. That is the right way to resolve a disagreement between two
censuses, and this project has needed it before.

**`s3ZigFree_near_extreme` is a real theorem**, at any span, with no crookedness: the tracking
fold, with the token placed at the arm's own level, clamped into the band and held back so it
never runs ahead of the index. With `s3ZigFree_span_five` and `s3ZigFree_of_interior`, only
spans six and above at interior basepoints carry any content.

**The sharpness result is the most useful thing delivered in several batches.**
`no_zigWalk_fold_veeSeq`: the straight descent `6,5,4,3,2,1,0`, based at its middle, admits *no*
walk of unit steps at all — not merely no member of the family. A token starting at time zero is
at time `u` at a position at most `u`, so it cannot be within one of `L` and within one of `H`
at two times three apart when the walk needs `H − L − 2 = 4` steps between those levels. The
sequence is not crooked, and that is the point: it says precisely where crookedness must enter,
and that no argument avoiding it can close the interior.

## 1. What this batch is

The missing ingredient is a lower bound on how far apart in *index* two levels must be. It is
Bing's Theorem 7, whose construction and length the repository already has (`bingPath`,
`bingPath_length`, `z`, batch 24) and whose minimality it does not.

**Minimality**: a faithful crooked sequence of span `d` has at least `z d` terms.

Checked here: the shortest faithful crooked thin sequence of span three has six terms and of
span four thirteen — exhaustively over all thin sequences to length thirteen on seven levels —
against `z 3 = 6` and `z 4 = 13`. And on `bing 0 n` for `n = 4 … 8` and 4 000 of their
subchains, every pair of indices at level distance `d ≥ 3` is at least `z d − 1` apart, with no
exception.

This is a named theorem of Bing's that the project would add to the verified list, and it is
what the interior case needs. It is also independent of the folding programme: it is worth
having whatever happens to `S3ZigFree`.

## 2. Ordinary items

**z_ge_of_le, z_gt_linear.** From the recurrence, by induction; `z_pos` (batch 24) is available.
`z_gt_linear` needs only `z 3 = 6 ≥ 6` and that each step at least doubles.

**isCrookedIvF_restrict.** A contiguous stretch is faithful and crooked. `bounds`, `width` and
`adj` restrict directly. For `crooked`, a forced-meeting witness `u` for an index inside the
stretch is within one of it, so either it is inside the stretch — and the clause transfers — or
it is the neighbour just outside, in which case the meeting it supplies is a meeting the
*ambient* sequence has, and the ambient clause gives witnesses `r, r'` strictly between `s` and
`t`, both of which lie inside the stretch because `s` and `t` do. *(supply: the index
arithmetic. This lemma is wanted independently — several earlier batches assumed restriction
silently in their censuses, and it has never been proved.)*

**index_gap_of_level_gap.** Apply `Minimality` to the stretch from `s` to `t` via
`isCrookedIvF_restrict`, with `L` and `H` the minimum and maximum of `ρ` on that stretch, which
are attained there. The span of the stretch is at least `|ρ t − ρ s|`, so `z_ge_of_le` gives the
bound with the stretch's length `t − s + 1`.

**timing_slack.** From `index_gap_of_level_gap` at the pair `(s, t)` and `z_gt_linear`.

## 3. `Minimality` — the search item

Search permitted. **A counterexample is a success; report it first.**

The shape of the proof is Bing's own recursion read backwards. `z (d+3) = 2·z(d+2) + z(d+1) − 2`
counts `P(a,b) = P(a,b∓1) · P(b∓1,a±1) · P(a±1,b)` with shared junctions: pieces of span
`d+2`, `d+1`, `d+2`, overlapping in one term each. For the lower bound one needs, in a faithful
crooked sequence of span `d`, three consecutive stretches of spans at least `d−1`, `d−2`, `d−1`,
and then induction.

The cut that gives them should be `crookedIvF_cut_first` (batch 26): between an index at the
bottom and a later one at the top, the sequence comes within one of the top and then within one
of the bottom. **Note the direction.** Batch 27 §2 shows that three pieces of *strictly smaller*
span need not exist — `cutSeq` is the witness — but that is an upper bound on the pieces, and
here the requirement is a lower bound on them, which the same cut may well supply. Do not
assume the batch-27 obstruction applies; it is about the opposite inequality.

If the induction resists, a weaker bound that still serves §2 would be worth delivering and
reporting as such: anything growing faster than `2d` closes `timing_slack`, and the exact
value `z d` is needed only for Theorem 7 itself.

## 4. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample to `Minimality`; whether it was proved, and with
   what bound if not the exact one; whether `isCrookedIvF_restrict` went through as stated.

## 5. Not in this batch

`s3ZigFree`; the linear-time far-index check that would make `¬ F2PrimeOff` unconditional;
Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
