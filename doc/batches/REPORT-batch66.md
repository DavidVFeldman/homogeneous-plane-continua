# Report: batch 66 — the residue proved for the relaxed clause, and the pairing shown to be needed

Batch 66 arrived without a written commission, so the agenda is the residue list the batch-65
report leaves standing: `CrossMid2L5'` (the corrected residue of the branch `L + 5`), the `w8`
side's disjunction, and the four targets. Following the house order, counterexamples first.

## 0. Counterexamples

**One, and it is about the shape of the residue rather than about its truth.**

### 0.1 `CrossMid2L5'` is not an arm-only fact

`ArmCrossMid2L5` (`HPC/Fold/Mid2Cross66.lean`) is `CrossMid2L5'` read over two **independent**
arms: each 1-Lipschitz, inside the band `[L, L + 9]`, based at `L + 5`, with the branch hypothesis
`LowAt (L + 1) (L + 8)`; the three crossing clauses of `TriCrossL5`, written for the two arms; the
same conclusion. The one hypothesis dropped is the crookedness that pairs the two arms. The
statement is **false** (`not_armCrossMid2L5`), at two very short arms:

```
g = 5 6 7 8 9        the `w8` side: it never descends, so `w3` and `wb` fail on it
f = 5 4 3 4 3 2      the partner: it stands at `L + 2` at its index five
```

* `f` fails `w8` (`not_w8_cexT66`) — so the first crossing clause holds;
* `g` fails `w3` and `wb` (`not_w3_cexG66`, `not_wb_cexG66`), because it has no time at `L + 4`
  before its ascent — so the second and third crossing clauses hold;
* `f` fails `Mid2Floor` (`not_mid2Floor_cexT66`): at its index five the clause asks for a landmark
  at an index in `[3, 1]`.

Both arms satisfy the branch hypothesis vacuously (neither reaches `L + 1`), and the reading is
decided by the kernel. The pair cannot be the two arms of a crooked basepoint — `g` rises seven
levels monotonically, which crookedness forbids — and that is exactly the content: **a proof of the
residue must read the pairing between the two arms, not each arm on its own.** The batch-65 census
says the same numerically: 308 258 basepoints of the corpus have one arm failing `Mid2Floor` and
the other served by `w8`, and none of them is a crossing.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`; the branch's residue is proved, for the relaxed clause, on the basepoints of §2.3 and §2.4 |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged |
| `s3_general` | `HPC/Fold/General.lean` | unchanged |
| `theorem3` | `HPC/Fold/Open.lean` | unchanged, waits on `s3_general` |

## 2. What was proved

### 2.1 The crooked peak lies on the `w8` side — now a theorem

The batch-65 census reported that at a descent of the partner to exactly `L + 2` at which
`Mid2Floor` fails, the peak the pairing produces lies on the `w8` side and never on the partner's.
That is not an accident of the corpus. The failure of `Mid2Floor` at a descent `d` says the arm has
no time at `L + 6` or above at arm index three or more and four steps before `d`; the pairing
(`cross_peak_valley_armG'`, batch 63) asks for no time at `L + 7` or above at arm index four or more
and seven steps before `d` — a weaker demand on a smaller window (`mid2Fail_window`). So

* `crossMid2_peak_on_w8_side` — if the backward arm fails `Mid2Floor`, then at **every** ascent of
  the forward arm to `L + 9` the peak (`L + 7` or above, arm index five or more) and the valley
  (`L + 3` or below, twenty-nine steps later, seventy steps before the ascent) are times of the
  *forward* arm;
* `crossMid2_peak_on_w8_side_T` — the mirror.

### 2.2 The failure buys the other arm the fifth walk

The same hypothesis is what `leg4Land_w72_of_cross_of_floor_fail` (batch 63) wants, so:

* `leg4Land_w72_of_mid2fail_armT` — in a band that misses the floor, a backward arm failing
  `Mid2Floor` forces the forward arm, already served by `w8`, to satisfy
  `w72 = L+4 → L+7 → L+2 → L+8 → L+1` in full; `leg4Land_w72_of_mid2fail_armG` is the mirror;
* `s3_span_nine_mid5_cross_dich` — hence at such a basepoint **either** the partner satisfies
  `Mid2Floor` — which is what the residue asserts, and from which the batch-64 chain runs —
  **or** the `w8` side is served by `w72`.

This cannot by itself close the branch: the arm that fails `Mid2Floor` is served by none of `w8`,
`w71`, `w72` (`mid2Floor_of_leg4Land`, batch 65), so what the failure buys is a walk for the *other*
arm. `mid2Fail_w3_or_wb` places the failing arm where the census puts it: by the trichotomy it is
served by `w3` or by `wb`.

### 2.3 The residue, proved for the relaxed clause, where the branch hypothesis is met the first way

This is the batch's main result. Two definitions and one law set it up.

**The relaxed clause.** `Mid2Floor2` (`HPC/Fold/Mid2Ascent66.lean`) is `Mid2Floor` with the index
bound lowered from three to two: at a descent to exactly `L + 2`, a time at `L + 6` or above at arm
index **two** or more and four steps earlier. It is weaker than `Mid2Floor`
(`mid2Floor2_of_mid2Floor`), so failing it is a stronger hypothesis — and it is the form the pairing
can read, because the timing law keeps a link whose interval reaches `L + 7` two steps from the
basepoint (`z 2 = 3`) and not three. The one index of slack between the two clauses is exactly the
difference between them.

**The pairing at `L + 8`.** `crooked_peak_valley_high8` and `crooked_valley_peak_high8` read
crookedness between a link at `L + 2` or below and a link whose *interval* reaches `L + 8`, in both
orders: they produce a peak whose interval reaches `L + 7` and a valley at `ρ a + 1` or below,
spaced twenty-nine steps from the low link (`z 5 = 30`) and twelve from each other (`z 4 = 13`).
Reading them against a high time of the `w8` side rather than against an ascent to `L + 9` is what
makes the argument cover all of the ascent clause.

**The ascent clause, on both arms.**

* `land_ascent_of_mid2fail2` — if the backward arm fails `Mid2Floor2`, the forward arm has, before
  every one of its times at `L + 8` or above, a time at `L + 4` or below at arm index three or more
  and twelve steps earlier. The peak of the pair cannot be a time of the partner: the timing law
  puts it at arm index two or more and twenty-nine steps from the descent, so it would sit inside
  the window the failure empties. The valley, which comes after the peak, is therefore a time of the
  forward arm; where its own index is exactly two, the next index serves, one level higher and
  still inside the clause.
* `land_ascent_armT_of_mid2fail2` (`HPC/Fold/Mid2Fold66.lean`) — the **failing arm itself** has the
  same landmark. First `mid2fail2_high_late`: every time of a failing arm at `L + 8` or above lies
  past its failing descent — a time at `L + 8` is at arm index three or more, a time at arm index
  between two and `dT - 4` is at `L + 5` or below by the failure, and a time at `L + 8` within
  three steps of a time at `L + 2` is forbidden by the law that charges seventy steps for six
  levels. Then crookedness read from that high time forward produces the valley on the same arm,
  between the two.
* `land_ascent_armG_of_mid2fail2G` and `land_ascent_armT_of_mid2fail2G`
  (`HPC/Fold/Mid2FoldG66.lean`) — the same two statements with the arms exchanged. They are not
  corollaries: the two arms run in opposite directions along the chain, so the mirror uses the other
  one of the two pairing lemmas.

**`w3` in full, and the fold.** The landmark above is the floor clause of the reflected walks `w3`
and `wb`, which they share. `w3`'s deep clause is vacuous inside the band (it triggers at `L + 10`),
and its ceiling clause at a descent to `L + 1` is supplied by the **first disjunct** of the branch
hypothesis — a time at `L + 8` before the descent — with the landmark above placed before it and the
index gaps free by the timing law. Hence `leg4Land_w3_of_mid2fail2`,
`leg4Land_w3_armT_of_mid2fail2` and their two mirrors, and then

* `s3_span_nine_mid5_of_mid2fail2` and `s3_span_nine_mid5_of_mid2fail2G` — at a basepoint of the
  branch where one arm fails `Mid2Floor2` and both arms meet the branch hypothesis by its first
  disjunct, **both** arms are served by `w3` and the pair folds;
* `not_triCross_of_mid2fail2` — such a basepoint is not a crossing of the trichotomy;
* `mid2Floor2_of_cross_highFirst` and `crossMid2_relaxed_of_highFirst` — equivalently, at a crossing
  both of whose arms have a time at `L + 8` before every descent to `L + 1`, **both** arms satisfy
  `Mid2Floor2`.

The last is the residue `CrossMid2L5'` proved on those basepoints, with the clause relaxed by one
index. It is the first positive result about the residue: previous batches assumed it, and batch 65
refuted the version of it that dropped the crossing.

### 2.4 The second route: `wb`, where a descent comes first

`w3` needs the *first* disjunct of the branch hypothesis because its ceiling clause asks for a
landmark at `L + 7`. The other reflected walk `wb` asks only for `L + 6` there, which is exactly
what the *second* disjunct offers, so on `wb` the branch hypothesis needs no case distinction at
all. What `wb` asks for instead is its deep clause at the ascents to `L + 9` — a time at `L + 4` or
below, then one at `L + 6` or above, then one at `L + 2` or below — and a **descent to `L + 1`
before the ascent** supplies its last link, the branch hypothesis at that descent its middle one,
and the landmark of §2.3 its first. Hence, in `HPC/Fold/Mid2Wb66.lean`:

* `ArmSep`, `armG_armSep`, `armT_armSep` — the timing law packaged as a property of an arm: `k`
  levels cost `z k - 1` steps, in whichever order the two times come;
* `leg4Land_wb_of_land_of_deepFirst` — an arm of the band with the branch hypothesis, with the
  landmark of §2.3, and with a descent to `L + 1` before each of its own times at `L + 9`, is
  served by `wb`; an arm that never reaches `L + 9` satisfies the last hypothesis vacuously;
* `s3_span_nine_mid5_of_mid2fail2_deepFirst` and its mirror — the pair folds onto `wb` at such a
  basepoint;
* `crossMid2_relaxed_of_deepFirst` — at a crossing both of whose arms descend to `L + 1` before
  they rise to `L + 9`, both arms satisfy `Mid2Floor2`.

So the residue, for the relaxed clause, is proved at the crossings whose arms are **both** high
first (§2.3) and at those whose arms are **both** low first (here). What is left is the *mixed*
basepoint: one arm rising to `L + 9` before it descends to `L + 1` and the other not. The two
conditions are not exclusive and neither is universal, which is why the mixed case is a case and
not a gap in the argument.

### 2.5 What is left of the residue

Two gaps, both named:

1. **The second disjunct of the branch hypothesis.** `LowAt (L + 1) (L + 8)` offers, at a descent to
   `L + 1`, either an earlier time at `L + 8` — the case proved above — or a time at `L + 2`
   followed by one at `L + 6`. The second gives `w3`'s ceiling clause one level short (`L + 6` where
   `L + 7` is asked), and `wb`, whose ceiling clause does accept `L + 6`, then owes its deep clause
   at the ascents to `L + 9`, whose last landmark must be at `L + 2` or below. The pairing's valley
   is at `ρ a + 1`, and the failing descent is at exactly `L + 2`, so the valley is at `L + 3`: one
   level short again. This is the same `L + 2`/`L + 1` seam the batch-64 and batch-65 assemblies
   carry as their `low1` hypothesis. §2.4 removes this gap where the arm descends to `L + 1` before
   it rises to `L + 9`; the mixed basepoint is what remains.
2. **The index of slack.** What is proved is `Mid2Floor2`, not `Mid2Floor`: a landmark at arm index
   exactly two is allowed by the timing law (`z 2 = 3`, two levels cost two steps), and a step down
   from `L + 6` is `L + 5`, so the repair that works for the valley — read the next index, one level
   lower — does not work for the peak.

### 2.6 The `w8` side's disjunction

Not attempted this batch; the batch-65 measurement stands, and §2.2 is what replaces its motivation:
where the partner fails `Mid2Floor`, the `w8` side gets `w72` whole, so the disjunction is only
needed where the partner satisfies the clause.

## 3. Deliverables

**Five new Lean files, all `sorry`-free, no `native_decide`, no new axiom.**

* `HPC/Fold/Mid2Cross66.lean` — `mid2Fail_window`, `mid2Fail_witness`, `crossMid2_peak_on_w8_side`,
  `crossMid2_peak_on_w8_side_T`, `leg4Land_w72_of_mid2fail_armT`, `leg4Land_w72_of_mid2fail_armG`,
  `s3_span_nine_mid5_cross_dich`, `mid2Fail_w3_or_wb`; and the arm-only refutation
  `ArmCrossMid2L5`, `cexG66`, `cexT66` with their readings and `not_armCrossMid2L5`.
* `HPC/Fold/Mid2Ascent66.lean` — `Mid2Floor2`, `mid2Floor2_of_mid2Floor`, `mid2Fail2_witness`,
  `crooked_peak_valley_high8`, `land_ascent_of_mid2fail2`, `land_w3_floor_of_mid2fail2`,
  `leg4Land_w3_of_mid2fail2`, `mid2fail2_cross_w3`.
* `HPC/Fold/Mid2Fold66.lean` — `crooked_valley_peak_high8`, `mid2fail2_high_late`,
  `land_ascent_armT_of_mid2fail2`, `land_w3_floor_armT_of_mid2fail2`,
  `leg4Land_w3_armT_of_mid2fail2`, `s3_span_nine_mid5_of_mid2fail2`, `not_triCross_of_mid2fail2`,
  `mid2Floor2_of_cross_highFirst`.
* `HPC/Fold/Mid2Wb66.lean` — `ArmSep`, `armG_armSep`, `armT_armSep`,
  `leg4Land_wb_of_land_of_deepFirst`, `s3_span_nine_mid5_of_mid2fail2_deepFirst`,
  `s3_span_nine_mid5_of_mid2fail2G_deepFirst`, `crossMid2_relaxed_of_deepFirst`.
* `HPC/Fold/Mid2FoldG66.lean` — the mirror: `mid2fail2_high_late_G`,
  `land_ascent_armG_of_mid2fail2G`, `land_ascent_armT_of_mid2fail2G`,
  `leg4Land_w3_armG_of_mid2fail2G`, `leg4Land_w3_armT_of_mid2fail2G`,
  `s3_span_nine_mid5_of_mid2fail2G`, `crossMid2_relaxed_of_highFirst`.

All five are imported by `HPC.lean`; `lake build HPC` is clean. The only edit to an earlier file is
those five import lines. The
project's `sorry`s are exactly the four standing targets — `s3_span_nine_mid5` (`Mixed.lean`),
`s3_span_nine` and `s3_general` (`General.lean`) and `theorem3` (`Open.lean`) — and nothing this
batch adds uses any of them.

```
'HPC.Fold.crossMid2_peak_on_w8_side' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crossMid2_peak_on_w8_side_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_mid2fail_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_mid2fail_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_cross_dich' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2Fail_w3_or_wb' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_armCrossMid2L5' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_of_mid2fail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w3_of_mid2fail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2fail2_cross_w3' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crooked_valley_peak_high8' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2fail2_high_late' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armT_of_mid2fail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w3_armT_of_mid2fail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_mid2fail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_triCross_of_mid2fail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2Floor2_of_cross_highFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2fail2_high_late_G' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armG_of_mid2fail2G' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armT_of_mid2fail2G' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_mid2fail2G' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crossMid2_relaxed_of_highFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.armG_armSep' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.armT_armSep' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_wb_of_land_of_deepFirst' depends on axioms: [propext, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_mid2fail2_deepFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_mid2fail2G_deepFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crossMid2_relaxed_of_deepFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No census or probe was run in this batch: every statement here is proved from the definitions and
from the timing law, and the numbers quoted are those of the batch-65 logs, cited as such.

## 4. Not in this batch

The mixed basepoints and the index of slack (§2.5); the `w8` side's
disjunction; a replacement sufficiency statement for the landmark sentence (the probe bound of the
batch-64 rule — forty times — has still not been reached); spans ten and above; Bing 1948
Theorems 4, 5, 6, 13; the 1951 reduction.
