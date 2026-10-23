# Report: batch 31 — the interior case of `S3ZigFree`

One new file, `HPC/Fold/Interior.lean`; the root `HPC.lean` updated; `README.md` notes the
batch; the commission text is kept as `COMMISSION-batch31.md`. Nothing else was touched. The
whole project builds. The new file has no `sorry`, `admit`, `axiom`, `native_decide` or
`@[implemented_by]` outside the commented block at its end, no linter warnings, and every
theorem in it has axiom profile inside `propext`, `Classical.choice`, `Quot.sound`. The census
program is `census-batch31.c`, its output `census-batch31.log`.

## 1. No counterexample

No counterexample to `S3ZigFreeInterior` was found, and none is claimed. The sweep re-decides
`S3ZigFree` exactly, by bitmask reachability, at every basepoint of `bing 0 n` for `n = 4 … 12`
and on random subchains of `bing 0 12`; every basepoint is served (`census-batch31.log`,
sections 3 and 4).

**But one commissioned statement is false, and is refuted.** See §2.

## 2. The ordinary items

`armG_index_gap` and `armT_index_gap` put `index_gap_of_level_gap'` (batch 30) into arm
coordinates: for either arm of any basepoint of a faithful crooked sequence,

    z (|arm j − ρ i|).toNat ≤ j + 1,

with no hypothesis beyond the model. This is the supply the commission asked for — the
arm-index versus sequence-index arithmetic — and it is the general form; everything else in §2
is a corollary.

**`arm_timing` as commissioned is false.** The commissioned statement asks, with no hypothesis
on `ρ i`, that an arm reaching an extreme at arm-index `j` have `(H − L − 2) ≤ j` unless
`ρ i = L` or `ρ i = H`. What the timing bound controls is the distance from `ρ i` to the extreme
the arm reaches, not whether `ρ i` is itself extreme: a basepoint one level below the top
reaches the top in one index at every span. `cutSeq` (batch 26: thirty-seven links of
`bing 0 8`, faithful, `L = 3`, `H = 7`) has level `6` at index `11` and level `7` at index `12`,
so its forward arm from index `11` reaches `H` at arm-index `1`, while `H − L − 2 = 2` and
`ρ i = 6` is neither extreme. That is `not_armTimingClaim`, proved against the commissioned
statement written out as `ArmTimingClaim`.

The corrected `arm_timing` is the same statement with the interior hypotheses
`L + 3 ≤ ρ i ≤ H − 3` of `both_arms_timing` added — the setting the item is used in — and with
the bound that does fall out, `z 3 − 1 = 5`:

    arm_timing : … → L + 3 ≤ ρ i → ρ i ≤ H − 3 → (armG ρ i j = L ∨ armG ρ i j = H) → 5 ≤ j.val

`arm_timing_back` is the same on the backward arm, and `both_arms_timing` is exactly as
commissioned (its `2` follows from the `5`). The hypotheses `hLb`, `hHb`, `hLH` of
`both_arms_timing` are not used and are kept only because the statement asks for them.

## 3. `s3ZigFreeInterior` — not proved, and what was learned

The greedy route of COMMISSION §3 was attempted. It goes through for one arm at a time; what it
cannot do, in the form suggested, is serve with one turn two arms that make opposite demands on
the token — one needing it above the base early, the other below — and that is now a theorem
rather than an impression.

**The walks an interior basepoint can use.** `FoldsOnto` pins the walk's time `0` to within one
of the basepoint's level, so the walk must start at the basepoint's own level `b`, and the free
family's exemption of the first amplitude is what allows it. The two shortest such walks are

    veeAt L H b = [b, L+1, H−1]        lamAt L H b = [b, H−1, L+1],

both in `IsZigFree` for every `b` strictly inside the band (`isZigFree_veeAt`,
`isZigFree_lamAt`). Their walks are computed (`zigWalk_veeAt_val_down`, `zigWalk_veeAt_val_up`
and the two mirrors), and the tracking fold of batch 29 generalises to them:

* `foldsOnto_veeAt`: an arm confined to `[L, H]` that starts at `b` and stays at or below
  `b + 1` until it first reaches `L + 1` folds onto the vee. The token follows the arm's level
  down the first leg and, from the arm's first visit to `L + 1` onwards, along the sweep,
  clamped to the band. `foldsOnto_lamAt` is the mirror.
* Hence `s3ZigFreeInterior_descentFirst` and `s3ZigFreeInterior_ascentFirst`: the interior case
  at every basepoint both of whose arms descend first, resp. ascend first.

**Why that is not all of it.** While the token is on the first leg of the vee the walk offers no
level above `b`, and the token is at the foot of that leg only when the arm is within one of
`L + 1`. So an arm that rises two above `b` must have come within one of `L + 1` first
(`foldsOnto_veeAt_descent_first`, by the discrete intermediate value theorem
`exists_lt_eq_of_lip`), and mirror-wise for the lam (`foldsOnto_lamAt_ascent_first`). Therefore
a basepoint whose forward arm rises two above the base before coming within one of `L + 1`, and
whose backward arm falls two below the base before coming within one of `H − 1`, is served by
**no** one-turn walk at all (`not_oneTurn_of_opposite`) — this is the formal version of the
commission's warning that "a shape chosen for one arm is a shape imposed on the other".

The census (`census-batch31.log`, sections 1–2) measures how much that costs. Over the interior
basepoints of `bing 0 n`, counting the three admissible bases `ρ i` and `ρ i ± 1` and deciding
service exactly by reachability:

| span | interior basepoints | served by a one-turn walk | served by none | of those, explained by `not_oneTurn_of_opposite` |
|---|---|---|---|---|
| 6 | 25 | 25 | 0 | 0 |
| 7 | 104 | 104 | 0 | 0 |
| 8 | 319 | 311 | 8 | 6 |
| 9 | 868 | 720 | 148 | 126 |
| 10 | 2 229 | 1 380 | 849 | 789 |
| 11 | 5 556 | 2 396 | 3 160 | 3 058 |
| 12 | 13 635 | 3 880 | 9 755 | 9 607 |

and on 143 random subchains of `bing 0 12` of span at least six: 186 911 interior basepoints,
161 203 served by a one-turn walk, 25 708 not, of which 21 820 satisfy the hypothesis of
`not_oneTurn_of_opposite`. So the obstruction accounts for the great majority of the
unserved basepoints, and the number of unserved ones grows with the span.

The same file re-tabulates the least number of turning targets over interior basepoints: 2, 2,
3, 3, 4, 4, 5 at spans 6 … 12, i.e. `⌊span/2⌋ − 1`, first attained at basepoints 5, 5, 57, 57,
343, 343, 2027 — the reversal law of batches 28–29, unchanged. **No fixed family of walks can
settle the interior: the number of legs grows with the span.** A greedy construction must
therefore produce a walk whose leg count grows, and the reversal law is the check on it.

**What is delivered towards the general construction.** The induction step:

* `zigWalk_cons_length` and `zigWalk_cons_val_tail` — the walk of `b :: ts` is the leg from `b`
  to the head of `ts` followed, after exactly `|t₁ − b|` times, by the walk of `ts`;
* `foldsOnto_prefixLeg` — if the arm's tail from index `e` folds onto the walk of `ts`, and the
  arm's first `e` indices carry the token from the start of the new leg to its far end, then the
  whole arm folds onto the walk of `b :: ts`.

With `isZigFree_cons` (batch 29) on the family side, this is the whole of one step of a
multi-leg construction. What is missing — and it is the same thing the ten refuted families
missed — is the rule that reads the two arms of a faithful crooked sequence and chooses the
turning targets, with the amplitudes increasing after the first and the two arms' demands
reconciled. The cut route of batch 29 §3 was not attempted in this batch.

## 4. Deliverables

1. Census: `census-batch31.c`, output `census-batch31.log`. Sections: the coverage of the
   one-turn walks and of the fold hypothesis at interior basepoints of `bing 0 6 … 12`; the
   least-turn table with the reversal law; random subchains of `bing 0 12`. No basepoint of any
   chain or subchain censused fails `S3ZigFree`.
2. Everything stated in `HPC/Fold/Interior.lean` is proved, `sorry`-free, with the axiom profile
   above. `s3ZigFreeInterior`, `s3ZigFree`, `s3` and `theorem3` are kept, commented out, at the
   end of the file, as batch 29 kept `s3ZigFree`.
3. Report: this file. A counterexample to the commissioned `arm_timing` (§2); no counterexample
   to `s3ZigFreeInterior`; the greedy route attempted, its one-turn case proved and its limit
   proved (§3).

## 5. Not in this batch

`s3ZigFreeInterior` itself, and with it `S3ZigFree`, `S3` and Bing 1948 Theorem 3 in the block
reading; the cut route; the linear-time far-index check for `¬ F2PrimeOff`; Bing 1948 Theorems
4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
