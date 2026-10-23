# Report: batch 61 — the crossing at `L + 5`

Written in the order the commission prescribes: counterexamples first, then §1 (targets), then §2
questions 1–3, then §3 deliverables.

## 0. Counterexamples and refutations

**None this batch.** Nothing in the batch-60 delivery was refuted, and no statement of this
batch's commission was found false. Two measurements correct the picture rather than contradict
it, and both are reported below as facts of the census, not as refutations:

* the list of five is **not** the list — the residue of the five walks is not empty on the corpus,
  and a sixth walk is needed (question 2);
* the walk the crossings ask for is *not* outside the window of the wide engine: it is the engine's
  own parameter set `(P, K, M) = (L+5, L+7, L+1)`, the walk `L+4 → L+7 → L+1 → L+8 → L+1`, whose
  *engine* criterion batch 58 refuted but whose *exact* criterion serves every crossing.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`; the residue is now the crossings of a list of **six** walks (`s3_span_nine_mid5_of_leg4SixCrossL5`), which the census measures **empty over the whole corpus** |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged |
| `s3_general` | `HPC/Fold/General.lean` | unchanged |
| `theorem3` | — | unchanged, waits on `s3_general` |

What moved. Batch 60 left the branch resting on the crossings of three walks (449 basepoints of
the corpus's 1 408 842 at this batch's seed, 371 of 1 745 960 at the last one) and, with two walks
added, of five (23 here, 38 there). This batch adds the walk the crossings themselves pick out,

```
w71 : direct (P, K, M) = (L+5, L+7, L+1)     L+4 → L+7 → L+1 → L+8 → L+1
```

and delivers two further reductions in `HPC/Fold/CrossW71.lean`:

* `s3_span_nine_mid5_of_leg4QuadCrossL5` — the three walks of `leg4Land_tri` with `w71`; residue 84
  on the corpus;
* `s3_span_nine_mid5_of_leg4SixCrossL5` — those four with `w72 = L+4 → L+7 → L+2 → L+8 → L+1` and
  `w81 = L+5 → L+8 → L+1 → L+8 → L+1`; **residue 0 at every generator of the corpus.**

Alongside them, three theorems about the crossing itself (§2.1) and the general statement of the
landmark sentence (§2.3).

## 2. The questions

### 2.1 The crossing

**Measured first.** `census-batch61.c` (log `census-batch61.log`) stores every five-walk crossing
of the corpus whole — both arms, and the faithful pair it was found in, duplicates merged — and
then reads it. The 23 distinct crossings have exactly the shape the commission describes: one arm
is served by `{w8, w72, w81}` (or by `{w8, w81}`) and the other by `{wb}` or by `{w3, wb, w72}`;
none is served by no walk of the four-leg family. And **one walk serves both arms of every one of
them**: the exact criterion of `w71` holds on both arms at all 23 (as does that of the parameter
set `(6,7,1)`, the same walk based one level higher). Against the list of six the corpus has no
crossing at all.

**The crossing is tight for the timing law.** The census prints, for each crossing, the first time
each arm reaches `L + 8` and the first time each descends to `L + 2`. At every crossing the two
indices that matter — the `w8` side's climb to `L + 8` and the other side's descent to `L + 2` —
sum to **exactly seventy**: `14 + 56`, `13 + 57`, `11 + 59`, `9 + 61`, `5 + 65`, … That is the
extremal case of the timing law of `HPC/Fold/Mixed.lean`: the two events are six levels apart
across the basepoint, a faithful crooked sequence needs `z 6 = 71` links to span six levels, and
so `dT + dG ≥ 70`. This batch proves that bound for the configuration:

* `cross_high8_low2_far` (and its mirror) — a time at `L + 8` or above on one arm and a time at
  `L + 2` or below on the other are seventy steps apart in total;
* `cross_no_low2_before` (and its mirror) — once one arm has climbed to `L + 8` at its step `dG`,
  the other stands at `L + 3` or above for its first `70 - dG` steps.

So the crossing is not a free configuration: it sits on the boundary of what crookedness allows,
and the census finds it nowhere else.

**What each side of the crossing already owes `w71`.** Inside the band the landmark sentence of
`w71` is two clauses — before every descent to `L + 2` a time at `L + 6` or above (index at least
three, gap at least `L + 6 - f d`), and before every ascent to `L + 9` a time at `L + 6` or above
followed six steps later by one at `L + 2` or below, itself `f d - L - 2` steps before the ascent.
`HPC/Fold/CrossW71.lean` proves:

* `leg4Land_w71_floor_of_w8` — an arm served by `w8` has the floor clause outright (`w8` asks for
  the same landmark one level higher, one index later and one step earlier), so the `w8` side owes
  `w71` only its ceiling clause (`leg4Land_w71_of_w8_of_ceil`);
* `land_w71_floor_low1_of_wb`, `land_w71_floor_low1_of_w3` — an arm served by `wb` or `w3` has the
  floor clause at its descents to `L + 1`, because the ceiling clause of those walks read on the
  unreflected arm is exactly that landmark; so the other side owes `w71` only its descents to
  *exactly* `L + 2` and its ascents to `L + 9` (`leg4Land_w71_of_wb_of_rest`).

Neither implication is unconditional, and the arm probe says so: `probe61.c` (log `probe61.log`)
enumerates every 1-Lipschitz arm of the band based at `L + 5` with the branch hypothesis to length
sixteen — 14 742 992 arms — and finds the service sets

```
{wb} 1 034   {w8} 1 590 250   {w3} 15 110   {wb,w3} 2 093 991   {w8,w3} 395 912
{w8,w71} 2 113 101   {wb,w3,w71} 635 212   all four 7 898 382     and {} 0
```

so `w71` never holds alone, never with `w3` alone and never with `wb` alone; 1 590 250 arms are
served by `w8` and not by `w71`, every one of them failing its ceiling clause. What the census says
is that at a *crossing* — where the two arms sit at one basepoint of a faithful pair, seventy steps
apart — the missing clauses hold. That pairing is what `Leg4QuadCrossL5` and `Leg4SixCrossL5` still
ask for, and it is where the argument stops. It does not stop at an index (batch 53's kind) or at
the level read from below (batch 57's kind): the arm-only half is exact, and the census finds no
disagreement between the sentence and the fold anywhere (0 in 400 000 sampled arm × parameter-set
pairs, both directions).

### 2.2 Is five the list?

**No, and the sixth walk is inside the window.** With a sixth walk the count *does* fall: it falls
to nothing. The census reads it three ways.

* Against the three walks of `leg4Land_tri` the corpus has **449** crossings; adding `w71` leaves
  **84**; adding `w72` and `w81` as well leaves **0** at every generator (thin chains, single
  shavings, single fills, random mixtures, heavy mixtures, faithful perturbation walks, chains
  outside Bing's family and concatenations).
* At the 23 crossings of the list of five, `w71` serves both arms at all 23, and so does `(6,7,1)`.
  No parameter set of the family serves none of them.
* Read by the fold itself rather than by a criterion, the crossings are served by far more: of the
  904 860 walks with a start in `[L, L + 9]` and up to six alternating turns, **6 004** serve both
  arms of all 23, the shortest being the *three*-leg walk `L+5 → L+7 → L+1 → L+8` (16 links),
  followed by `L+4 → L+7 → L+1 → L+8` (17). So the crossing is not short of walks; what it is
  short of is a *criterion*, and `w71` is the shortest walk of the engine's own window that has
  one.

The answer to the question as asked — whether the residue is served by a common walk outside the
window of the wide engine, or by five walks with a rule choosing among them — is neither: it is
served by a sixth walk *inside* the window, whose exact criterion batch 59 supplied and whose
engine criterion batch 58 had refuted. The refutation of `not_walk47181CritL5` was a refutation of
the engine's criterion for this walk, not of the walk.

### 2.3 The general engine, stated

`HPC/Fold/LandList.lean` states it and proves half of it.

A walk is given by its list of turning levels: `walkList s ts` starts at `s` and turns, in order,
at the levels of `ts`, one level per time; `walkLen s ts` is its length, `walkStop s ts k` the time
of its `k`-th turn and `walkLevel s ts k` the level there. `walkList_walkStop` says the walk is at
the `k`-th turning level at the `k`-th turn time and `walkList_step` that it moves by at most one
level per time.

The landmark sentence is then the conjunction over the walk's legs:

```
LandWalk f s ts :  ∀ r d,
  (the arm's level at d is served only by the walk's times walkStop s ts r and later) →
  ∃ j 0 ≤ ⋯ ≤ j r = d,  |f (j u) - walkLevel s ts u| ≤ 1  for every u < r,
                        with every gap j (u+1) - j u at least walkStop (u+1) - walkStop u.
```

* `landWalk_of_foldsOnto` — **the sentence is necessary for a walk of any shape**, immediately from
  `foldsOnto_landmarkN` of batch 60: the walk's own turn times are the increasing chain of
  positions the chain theorem asks for.
* `leg4Walk_eq_walkList`, `walkLen_leg4`, `walkStop_leg4_one/two/three` — the four-leg walk of the
  engine **is** `walkList (P-1) [K, M, H-1, L+1]`, with the turn times `A = K - P + 1`,
  `B = 2K - P + 1 - M`, `C = 2K - P + H - 2M` of `HPC/Fold/Leg4Land.lean`. So `Leg4Land` is this
  sentence read at four turning levels, clause by clause.

The sufficiency half — the invariant of `gseq4_invLand` with two bounds per interior leg, the
credit being the index gap between consecutive turn times — is still not proved, and is now the
only missing half of the general engine.

## 3. Deliverables

**New Lean files, both `sorry`-free, no `native_decide`, no new axiom.**

* `HPC/Fold/LandList.lean` — `walkList`, `walkLen`, `walkStop`, `walkLevel`, `walkList_zero`,
  `walkStop_mono`, `walkList_walkStop`, `walkList_step`, `LandWalk`, `landWalk_of_foldsOnto`,
  `walkLen_leg4`, `walkStop_leg4_one`, `walkStop_leg4_two`, `walkStop_leg4_three`,
  `leg4Walk_eq_walkList`.
* `HPC/Fold/CrossW71.lean` — `leg4Land_w71_floor_of_w8`, `leg4Land_w71_of_w8_of_ceil`,
  `land_w71_floor_low1_of_wb`, `land_w71_floor_low1_of_w3`, `leg4Land_w71_of_wb_of_rest`,
  `leg4Window_w71`, `Leg4QuadCrossL5`, `s3_span_nine_mid5_of_leg4QuadCrossL5`,
  `cross_high8_low2_far`, `cross_high8_low2_far'`, `cross_no_low2_before`,
  `cross_no_low2_before'`, `Leg4SixCrossL5`, `s3_span_nine_mid5_of_leg4SixCrossL5`.

`lake build HPC` is clean and both files are in `HPC.lean`.

```
'HPC.Fold.landWalk_of_foldsOnto' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Walk_eq_walkList' depends on axioms: [propext, Quot.sound]
'HPC.Fold.walkList_walkStop' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_leg4QuadCrossL5' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_leg4SixCrossL5' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_high8_low2_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_no_low2_before' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w71_of_w8_of_ceil' depends on axioms: [propext, Quot.sound]
'HPC.Fold.land_w71_floor_low1_of_wb' depends on axioms: [propext, Quot.sound]
'HPC.Fold.leg4Land_w71_of_wb_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Censuses over the general model, under the audit protocol.** `census-batch61.c` (log
`census-batch61.log`, run as `census-batch61 40 61 200 12`) is the batch-60 census with the
batch-61 blocks added: the crossings of the list of five stored whole and read walk by walk, the
crossings of the list of four and of the list of six, the shape of each crossing, the search over
904 860 walks of any shape for one serving them all, and the first crossings shrunk to minimal
faithful windows. Every predicate is evaluated by its own definition — `IsCrookedIvF`, `IsLip`,
`LowAt`, `Leg4Land` clause by clause with the index bounds the walk's positions dictate, and
`FoldsOnto` by the dynamic program of `HPC/Fold/Decide.lean`; the definition audit at the end of
the log lists them.

**Arm-only probe** (it says so): `probe61.c` (log `probe61.log`) enumerates arms, not pairs, and
carries no faithfulness hypothesis beyond the band, the Lipschitz condition, the basepoint `L + 5`
and the branch hypothesis.

The numbers quoted above are from those two programs and their logs.
