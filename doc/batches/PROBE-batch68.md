# The engine probe to forty times — batch 68 §2.4

**Result, stated either way: the probe reached forty and the sentence did not survive it.** The
corrected landmark sentence `LandWalkP` **with the clause of batch 66 §2.3 added** — every time of
the arm whose level is served only by walk positions before the `r`-th turn comes before the `r`-th
landmark — is still **not sufficient** for folding, at arms of forty times, for walks whose shortest
leg is at least three and for walks whose shortest leg is four. So the batch-64 rule is met at last
and its verdict is negative: **no sufficiency statement for the landmark sentence is written in this
batch**, and the added clause of batch 66 §2.3 is not the repair.

## The program

`probe68.c` is `probe65b.c` with two changes: the arm bound is raised from thirty to forty, and the
sentence tested carries the added clause. It is a census over **walks and arms**, not over the
general model, and its arm-length bound is **forty times**, against walks of up to twenty-one times
— twice the walk's length, which is what the batch-64 rule asks for.

It enumerates walks by their turning levels — at most four turns, levels in `[0, 6]`, shortest leg
at least three — and for each runs randomised depth-first descents over 1-Lipschitz arms to forty
times with a fixed node budget per walk, pruning on the two prefix-monotone conditions (a level of
the arm that no time of the walk serves, and a trigger the sentence leaves unmet, are both
permanent). `walkList`, `walkLen`, `walkStop`, `walkLevel`, the sentence with the added clause and
`FoldsOnto` are evaluated by their own definitions; the landmark chain is decided by the backwards
greedy, which takes each landmark as late as possible and is therefore optimal for the added clause
as well as for the gaps.

## The runs

| log | budget per walk | state | counterexamples |
| --- | --- | --- | --- |
| `probe68c.log` | 200 000 nodes | **complete sweep**: 742 walks, 146 443 515 arms tested, deepest prefix reached **40** | **12** |
| `probe68b.log` | 2 000 000 nodes | partial — still walking when the batch closed (through `s = 1`) | 11 so far |
| `probe68.log` | 20 000 000 nodes | partial — still on the first walks when the batch closed | 2 so far |

It is a sample and not an exhaustive sweep of arms, and is reported as such: an exhaustive sweep to
forty times is `3^40` arms per walk.

## What it found

Twelve counterexamples in the complete run, at arms of exactly forty times, one of them at a walk
whose shortest leg is **four**:

```
s = 0, ts = [5,1,6,0]   legs 5,4,5,6   walk 0 1 2 3 4 5 4 3 2 1 2 3 4 5 6 5 4 3 2 1 0
  arm (40) -1 0 -1 0 0 -1 0 0 1 2 2 2 3 2 3 2 3 2 1 2 1 2 2 2 3 4 4 3 2 1 0 -1 0 1 2 3 4 5 6 7
```

and eleven at shortest leg three, at `ts = [4,1,6,0]`, `[4,1,5,1]` from `s = 0`; `[5,2,5,0]`,
`[5,2,6,0]`, `[5,2,6,1]`, `[5,2,6,2]` from `s = 1`; `[6,3,6,1]` from `s = 2`; and `[1,4,0,4]`,
`[2,5,0,5]`, `[2,5,0,6]`, `[2,5,1,6]` from `s = 6`. The deeper partial runs add, among others,

```
s = 0, ts = [4,1,5]     legs 4,3,4     walk 0 1 2 3 4 3 2 1 2 3 4 5
  arm (40) -1 0 1 2 1 0 -1 0 -1 0 1 0 1 2 2 3 3 4 3 2 3 4 3 4 3 2 1 0 -1 0 1 2 3 2 2 3 3 4 5 6

s = 0, ts = [5,2,6]     legs 5,3,4     walk 0 1 2 3 4 5 4 3 2 3 4 5 6
  arm (40) -1 0 0 1 1 0 -1 -1 0 -1 0 1 2 3 3 3 4 3 2 1 0 0 1 0 -1 0 1 0 1 2 3 3 4 3 4 5 6 6 6 7

s = 0, ts = [5,1,6,0]   legs 5,4,5,6   walk 0 1 2 3 4 5 4 3 2 1 2 3 4 5 6 5 4 3 2 1 0
  arm (40) -1 0 -1 -1 -1 0 1 0 -1 -1 0 -1 0 1 1 2 1 2 3 4 3 4 3 3 4 4 3 3 2 1 0 -1 0 1 2 3 4 5 6 7
```

**Four of these were re-checked independently.** `check68.py` (log `check68.log`) is written from
the definitions of `HPC/Fold/LandList.lean` and `HPC/Fold/Itinerary.lean` and shares no code with
`probe68.c`; it rebuilds the walk and reports, for each case, that the arm is 1-Lipschitz, starts
within one of the walk's first level, has every level served by some time of the walk, satisfies the
sentence **with the added clause**, and does **not** fold onto the walk. Two of the four have
shortest leg four, so lengthening the legs is not the repair here either — the same lesson batch 65
drew at arms of thirty.

## What this means for the branch

Nothing in `HPC/Fold/Ceil68.lean`, or in any earlier batch, depends on the sufficiency of the
landmark sentence: every fold in the development is produced by `foldsOnto_leg4_iff_leg4Land` for
the four-leg family, whose criterion is exact and proved, and the sentence of `LandWalk` is used
only in its *necessary* direction (`foldsOnto_landmark1`, `foldsOnto_landmark2`,
`foldsOnto_landmark3`). The probe therefore closes a question rather than opening one:
`LandWalkPSuffices` and its variants are refuted, `LandWalkP3Suffices` and `LandWalkPLegSuffices 4`
were refuted in batch 65, and the clause of batch 66 §2.3 does not restore sufficiency at forty.
