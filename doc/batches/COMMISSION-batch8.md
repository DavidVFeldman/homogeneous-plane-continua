# Commission: batch 8 — the one-bump itinerary (Lemma F1′)

**Go!** Runs on top of the batch-7 delivery. One new file, `HPC/Fold/Bump.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

The two-itinerary dichotomy of batch 6 is false (a counterexample is on record). Its
replacement uses a family with an adjustable bump, `Λ(h) = p ↑ h ↓ L+1 ↑ H−1`. This batch
proves a *sufficient* condition for an arm to fold onto `Λ(h)`, by exhibiting the assignment;
derives the reflected family; and draws the consequence for chains. It does **not** claim a
characterization, and it does not prove that a common `h` always exists (F2′, open).

The condition was checked for soundness against a brute-force reachability computation on
2 927 498 basepoints — every crooked sequence of length ≤ 12 on six levels, plus random
crooked sequences up to length 40 — with no case where it claimed a fold that does not exist.

## Protocol

As batches 1–7. Batch-6 results expected: `IsLip`, `FoldsOnto`, `NonAscAt`, `κ`, `lamCenter`,
`armG`, `armT`, `exists_schedule_of_folds`, `exists_blocks_first_of_folds`. Batch-4/5:
`Chain.Refines.minIdx`, `minIdx_lip`, `Chain.exists_blocks_of_walk`.

## 1. The itinerary

`a := h − p`, `b := h − L − 1`. Centers: `p + u` for `u ≤ a`; `h − (u − a)` for
`a < u ≤ a + b` (so the center at `a + b` is `L + 1`); `L + 1 + (u − a − b)` thereafter, up to
`H − 1`.

**The three level-regions are nested.** Leg 1's assignment covers levels in `[p−1, h+1]`, leg
2's covers `[L, h+1]`, leg 3's covers `[L, H]`. Each contains the previous, so a fold passes
through the legs once and never returns. This is what makes the condition a clean segmentation
rather than a reachability computation.

## 2. Proofs of the itinerary lemmas

**bumpCenter_zero.** `0 ≤ a`, so the first branch applies.

**bumpCenter_lip.** Within leg 1 consecutive centers differ by `+1`; within leg 2 by `−1`;
within leg 3 by `+1`. At `u = a` the centers are `h` and `h − 1`; at `u = a + b` they are
`L + 1` and `L + 2`. *(supply: the branch arithmetic, four cases.)*

**bumpCenter_eq_lamCenter.** For `h = κ p H` the first two legs are exactly `lamCenter`'s two
legs; compare the branch conditions. This records that `Λ(κ)` extends the old `Λ*`, so batch-6
results about `Λ*` remain usable.

## 3. The phase and the segmented condition

`phase f j = 1` iff some `t ≤ j` is a non-ascending step. `phase_zero`: a non-ascending step
has positive index. `phase_add_isLip`: at a step where `φ` goes `0 → 1` the witness must be
the step itself, so `f` does not ascend there and `f + φ` changes by at most one; where `φ` is
constant, `f + φ` changes as `f` does; `φ` never decreases.

(These three are the batch-6 auxiliaries `hbound1`-style facts stated in their own right. If
batch 6's proof of `foldsOnto_lam_iff` already contains them in usable form, lift them rather
than reproving; record which.)

**SegLam f p H L h** asks for `s ≤ t ≤ m` with:
1. `∀ j < s`, `p − 1 ≤ f j ≤ h + 1`;
2. if `s < m`, `h ≤ f s + φ s`;
3. `∀ j < s`, `f j + φ j < h` (so `s` is the least index reaching the peak in the adjusted
   sense);
4. `∀ j` with `s ≤ j < t`, `L ≤ f j ≤ h + 1`;
5. `t = m`, or the level immediately before `t` is at most `L + 1`.

## 4. Lemma F1′ — the construction

Write `φ := phase f`, `g := f + φ`. Define

    β j := min a (max 0 (g j))          shifted: min a (max 0 (g j − p))      for j < s
    β j := a + max 0 (h − 1 − f j)                                            for s ≤ j < t
    β j := a + b + max 0 (f j − (L + 2))                                      for t ≤ j

**Windows.**
*Leg 1.* If `0 < β j < a` the center is `f j + φ j`, within one of `f j` since `φ j ≤ 1`. If
`β j = 0` then `g j ≤ p`, so `f j ≤ p`, and `f j ≥ p − 1` by (1): center `p`. If `β j = a`
(the clamp) then `g j ≥ h`, so `f j ≥ h − 1`, and `f j ≤ h + 1` by (1): center `h`.
*Leg 2.* If `f j ≥ h − 1` then `β j = a`, center `h`, and `f j ≤ h + 1` by (4). Otherwise
`β j = a + (h − 1 − f j)`, center `h − (h − 1 − f j) = f j + 1`. The time is at most `a + b`
because `f j ≥ L` by (4).
*Leg 3.* If `f j ≥ L + 2` the center is `L + 1 + (f j − L − 2) = f j − 1`. Otherwise
`β j = a + b`, center `L + 1`, and `f j ≥ L` by hypothesis. The time is within the walk since
`f j ≤ H`.

**Lipschitz within a leg.** Leg 1: `g` is Lipschitz (`phase_add_isLip`) and `min`/`max` with
constants preserve that. Legs 2 and 3: `f` is Lipschitz and the formulas are `±f` up to
constants with one clamp.

**The first seam.** Let `j = s − 1` (if `s = 0` there is nothing to check). By (3),
`g j < h`, so `β j = min a (max 0 (g j − p)) ≤ a − 1` — unless the clamp binds, which it
cannot since `g j − p < a`. By (2), `g s ≥ h`, so `f s ≥ h − 1` and `β s = a` on the leg-2
formula. By Lipschitz of `g`, `g j ≥ g s − 1 ≥ h − 1`, so `β j ≥ a − 1`. Hence
`β j ∈ {a − 1}` ∪ … and `|β s − β j| ≤ 1`.

**The second seam.** Let `j = t − 1` (if `t = m` there is no seam). By (5), `f j ≤ L + 1`, so
`β j = a + (h − 1 − f j) ≥ a + (h − 1 − L − 1) = a + b − 1`; also `β j ≤ a + b` since
`f j ≥ L`. By Lipschitz, `f t ≤ L + 2`, so `β t = a + b`. Hence `|β t − β j| ≤ 1`.

*(This is the point at which the natural-looking condition "`f t ≤ L + 2`" fails: with
`f (t−1) = L + 3` the two formulas differ by three. The condition is stated on the index
before the seam, and at `L + 1`, for exactly this reason.)*

**Start.** `β 0 = 0`: if `s > 0` then `g 0 = p + 0`, so `max 0 (g 0 − p) = 0`. If `s = 0` then
(2) gives `h ≤ f 0 + φ 0 = p`, so `a = 0` and the leg-2 formula gives
`β 0 = 0 + max 0 (h − 1 − p) = 0`. If also `t = 0`, the leg-3 formula gives
`a + b + max 0 (p − L − 2)`, which is `0` only if `b = 0` and `p ≤ L + 2`; in that case
`h = L + 1` and `h = p`, consistent. *(supply: this last sub-case, or strengthen `SegLam` to
require `0 < t` when `a + b > 0`, recording the change.)*

**Bound.** `β j < bumpLen` in each leg from the computations above.

## 5. The reflected family

`segVee_foldsOnto`: `g := −f` is Lipschitz with `g 0 = −p`, values in `[−H, −L]`, and
`|f j − (−c)| = |g j − c|`; the definitions of `veeBumpLen`, `veeBumpCenter`, `SegVee` are the
reflections, so this is `segLam_foldsOnto` applied to `g`. *(supply: the unfolding.)*

## 6. Consequence for chains

`exists_blocks_first_of_segLam`: apply `segLam_foldsOnto` to each arm to get two folds onto the
same walk, then batch-6 `exists_blocks_first_of_folds` with `len := bumpLen p H L hb` and
`c := bumpCenter p H L hb`.

## 7. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: what was supplied at each step; whether the phase auxiliaries were lifted from
   batch 6 or reproved; the outcome on the `s = t = 0` sub-case of §4; any statement that did
   not go through, with the point of failure.

## 8. Not in this batch

F2′ — that a common bump height exists for both arms. Bing 1948 Theorems 3–6, the reduction,
the D8/D9 gap.
