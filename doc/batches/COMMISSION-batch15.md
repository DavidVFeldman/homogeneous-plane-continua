# Commission: batch 15 — refuting `MixedGap`, `MixedGapUp` and `Agreement`

**Go!** Runs on top of the batch-14 delivery. One new file, `HPC/Fold/Refutations.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

Three propositions carried in the repository as open conjectures are false. Their docstrings
cite large corpora, and those corpora were filtered with a crookedness model strictly stronger
than either weak form — witnesses at exactly the adjacent levels rather than within a unit. No
sequence satisfying only a weak form was ever tested. This batch records the refutation
formally, so the conjectures cannot be worked on again by mistake.

Nothing proved elsewhere is affected. All three are `def ... : Prop` and none was ever
discharged as a hypothesis of a theorem.

## Protocol

As batches 1–14. Expected: `IsLip`, `IsCrookedSeq`, `IsCrookedSeqUp`, `hStarArm`, `lStarArm`,
`armG`, `armT`, `MixedGap`, `MixedGapUp`, `Agreement`.

## 1. The sequence

`badSeq = ![1, 2, 3, 2, 3, 4, 3, 4, 5] : Fin 9 → ℤ`, basepoint `badPt = 4`, so `p = 3`.

Arms: `armG badSeq badPt = 3, 4, 3, 4, 5` (length 5) and
`armT badSeq badPt = 3, 2, 3, 2, 1` (length 5).

## 2. Verification, with all witnesses

**badSeq_isLip.** The eight consecutive differences are `+1, +1, −1, +1, +1, −1, +1, +1`.
`decide` after `Fin` case analysis, or eight `norm_num` goals.

**badSeq_isCrookedSeq.** Exactly five pairs `s < t` have `3 ≤ |f t − f s|`; for each, witnesses
`(r, r')` in the down-form windows — `f r ∈ [f t − 2, f t − 1]`, `f r' ∈ [f s, f s + 1]` in the
ascending case:

| `s` (level) | `t` (level) | `r` | `r'` |
|---|---|---|---|
| 0 (1) | 5 (4) | 1 | 3 |
| 0 (1) | 7 (4) | 1 | 3 |
| 0 (1) | 8 (5) | 2 | 3 |
| 1 (2) | 8 (5) | 2 | 3 |
| 3 (2) | 8 (5) | 4 | 6 |

Every pair is ascending, so the descending branch of `IsCrookedSeq` is discharged by
`absurd`/`omega`.

**badSeq_isCrookedSeqUp.** The same five pairs, up-form windows — `f r ∈ [f t − 1, f t]`,
`f r' ∈ [f s + 1, f s + 2]`:

| `s` (level) | `t` (level) | `r` | `r'` |
|---|---|---|---|
| 0 (1) | 5 (4) | 2 | 3 |
| 0 (1) | 7 (4) | 2 | 3 |
| 0 (1) | 8 (5) | 5 | 6 |
| 1 (2) | 8 (5) | 5 | 6 |
| 3 (2) | 8 (5) | 5 | 6 |

*(supply: the enumeration of pairs. `Fin 9 × Fin 9` is 81 cases; `decide` may or may not be
tractable on `ℤ`-valued goals — if not, do the case analysis with `Fin.cases` and discharge the
`|f t − f s| < 3` majority by `omega`, then supply the five witnesses explicitly. Report which
route was taken.)*

## 3. The four demands

**badSeq_hStarArm_G = 5.** `armG` never reaches `p − 2 = 1`, so every index satisfies the side
condition and `hStarArm` is the maximum, `5`, attained at index `4`.

**badSeq_hStarArm_T = 3.** `armT = 3, 2, 3, 2, 1` reaches `1 = p − 2` at index `4`, so the side
condition holds exactly for indices `0..3`, on which the maximum is `3`.

**badSeq_lStarArm_G = 3.** `lStarArm A p = − hStarArm (−A) (−p)` by definition. `−armG` is
`−3, −4, −3, −4, −5` with base `−3`; it reaches `−5 = −p − 2` at index `4`, so the side
condition holds on `0..3` and the maximum there is `−3`. Hence `lStarArm = 3`.

**badSeq_lStarArm_T = 1.** `−armT` never reaches `−5`, so `hStarArm (−armT) (−3) = −1` and
`lStarArm = 1`.

*(supply: `hStarArm` is an `sSup` over a set of integers; use `hStarArm_mem` and
`le_hStarArm` from batch 9 together with `csSup_eq_of_...`, or whichever characterization the
delivered encoding offers. The point in each case is that the defining set is explicitly
`{3}`, `{3, 2}`, `{3, 4, 5}` or the like, computed from five values.)*

## 4. The refutations

**not_mixedGap.** Apply the universally quantified `MixedGap` to `9`, `badSeq`, `badPt`,
`badSeq_isLip`, `badSeq_isCrookedSeq`. Its conclusion is the negation of a conjunction; supply
the conjunction from the four demand values: `3 + 2 ≤ 5` and `1 + 2 ≤ 3`.

**not_mixedGapUp.** The same with `badSeq_isCrookedSeqUp`.

**not_agreement.** Apply `Agreement` and refute both disjuncts: `|5 − 3| = 2` and
`|3 − 1| = 2`, neither `≤ 1`. Note the arms in `Agreement` appear as `G` minus `T`; the
absolute values make the orientation immaterial.

## 5. Docstring corrections

The docstrings of `MixedGap`, `MixedGapUp` and `Agreement` — in `Exits.lean`, `Symmetry.lean`
and `Phase.lean` — state corpus sizes as evidence. Those files are otherwise untouched by this
batch and **should stay untouched**: do not edit them. Instead, the module docstring of
`Refutations.lean` records that the evidence was gathered under the wrong model, and the three
`not_` theorems are the authority. Report if you think a different arrangement is better, but
do not change earlier files without saying so.

## 6. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: which route was taken for the crookedness enumeration; how `hStarArm` was computed
   from the explicit sequence; what was supplied; any statement that did not go through. **If
   any of the three propositions turns out not to be refuted by this sequence — in particular
   if `badSeq` fails one of the two crookedness conditions — report that first.**

## 7. Not in this batch

The replacement for `Agreement`; re-running the evidence base under the down form;
`SmallDemandCase`; `HighExitValley`; the assembly into `F2Prime`; Bing 1948 Theorems 4, 5, 6;
the reduction in Bing 1951; the D8/D9 gap.
