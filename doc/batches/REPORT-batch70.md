# Report — batch 70

The commission read is `COMMISSION-batch70.md` (identical copy `COMMISSION.md`), the batch-70
archive's text: *three statements about one crossing, on a wider corpus.*

New in the project: two Lean files, `HPC/Fold/Deep70.lean` and `HPC/Fold/Reading70.lean`, both
`sorry`-free and imported by `HPC.lean`; the widened census `census-batch70.c` with its log
`census-batch70.log`; the independent re-check `check70.py` with its log `check70.log` and the
witness it reads, `witness-batch70.txt`; the axiom profiles of all thirty new theorems in
`axioms-batch70.txt`. `lake build` is clean, and the project's standing `sorry`s are still exactly
the four targets — `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`.

## 0. The finding, first

**`BothNineL5` is inhabited. The third of the three statements the branch owed is false.**

On the widened corpus both arms of a crossing reach `L + 9` at

* **39 of the 229** high-run crossings,
* **67 of the 1351** crossings of the trichotomy,
* 146409 of the 2444297 basepoints of the branch `L + 5`,

where the batch-68/69 corpus — windows of one 986-link pair — had none of 461 and none of 87. So
the hypothesis `hnineT : ∀ j, armT ρ i j ≤ L + 8` that the batch-68 and batch-69 assemblies carry
is **not** innocuous, and `armT_no_nine_or_bothNine` really is a case split and not a formality.

**The definition audit.** The census stores the first such crossing in full —
`witness-batch70.txt`, a faithful pair of 2378 links with basepoint 2026 — and `check70.py`
re-checks it from scratch, with every predicate written out again independently of the census's C
(`check70.log`):

```
the witness: 2378 links, basepoint 2026, the w8 side is the forward arm
  levels run from 0 to 9
  IsCrookedIvF: True            (the clause searched literally over all pairs of times and levels)
  rho i = 5
  arm lengths: forward 352, backward 2027
  LowAt on the forward arm: True; on the backward arm: True
  the forward arm reaches 9: True (first at arm index 113)
  the backward arm reaches 9: True (first at arm index 225)
  w8: forward True, backward False
  wb: forward False, backward True
  w3: forward False, backward True
  a crossing of the trichotomy (no one of the three serves both arms): True
  w72 = (7,2,5) on the forward arm: True; on the backward arm: True
  walks of the four-leg family serving both arms: 6
```

`Leg4Land` is written out literally there, with no greedy reading, and `FoldsOnto` as the
reachability program of `HPC/Fold/Decide.lean`. The pair is a window of `bing 0 10` of span nine,
shifted to the band `[0, 9]`; it is a faithful pair in its own right, and the two arms are whole
arms of it.

**It is not a counterexample to `S3` at span nine, and so not to `theorem3`.** At all 39 both-nine
high-run crossings both arms satisfy the landmark sentence of `w72` and six walks of the four-leg
family serve both arms; at the witness above the shortest is `4 → 7 → 2 → 8 → 1`, which is `w72`
itself. What the finding refutes is a *hypothesis of the assembly*, not the statement being proved.

**And the batch made the hypothesis unnecessary.** The assembly of §2.5 below is symmetric: it
never asks which arm carries `w8`, and it never asks the partner to stop below `L + 9`. So the
configuration the corpus now exhibits is covered.

## 1. The targets

`s3_span_nine_mid5`, `s3_span_nine`, `s3_general` and `theorem3` are **not** proved in this batch.
What the batch does is to discharge two of the three statements batch 69 left standing, as
theorems, and to refute the third while removing the need for it: the branch at `L + 5` at a
high-run crossing now owes **one** statement, not three.

## 2. The questions

### 2.1 The corpus, widened

`census-batch70.c` (log `census-batch70.log`) is a new census, self-contained, whose corpus is
built from

* the Bing chains `bing 0 9` and `bing 9 0`;
* **windows of span exactly nine of `bing 0 N` for `N = 10, 11, 12, 13`**, at grid offsets (stride
  149) and at random offsets — the "`bing 0 N` for larger `N`; subchains at other offsets" and "the
  random and grid subchains of batch 29" the commission names, shifted so that the band is `[0, 9]`;
* the recursive chains `vpath a b back fwd` outside Bing's family, in both directions and at four
  splitting parameters;
* random concatenations of Bing blocks, and windows of span nine of them;
* and, **for every base sequence above**, the thin pair, up to sixty single shavings, up to sixty
  single fillings, random mixtures at rates 1/3 and 1/2, and the total mixture — the shaved and
  filled pairs where the general model differs from the thin one.

Every window is re-tested for `IsCrookedIvF` in its own right, so this is a census over whole pairs
and whole arms of those pairs: **no arm-length bound applies**, and the arms actually seen at the
high-run crossings run from 105 to 2211 times.

| the corpus | |
| --- | --- |
| base level sequences of band `[0,9]` | 64 |
| faithful pairs scanned | 7040 (6796 distinct) |
| links, of which not thin | 12 392 192, of which 205 420 |
| basepoints of the branch `L + 5` | 2 444 297 |
| crossings of the trichotomy | 1351 (all distinct by their pair of arms) |
| **high-run crossings** | **229** (all distinct) |
| **distinct configurations among them** | **52** |

(The configuration of a high-run crossing is the tuple the tables below measure: the level and
index of the low landmark, its distance from the ascent, the peak's index and level, the three
nearest low distances, whether the partner's arm reaches the floor and satisfies `Deep72`, whether
both arms reach `L + 9`. Batch 69's 87 crossings were **one** such tuple; the widened corpus has
52.)

**The three statements, re-measured.**

| | |
| --- | --- |
| 1. the distance: a time of the pair at `L + 2` or below within 67 steps across the basepoint | **holds at 229 of 229**; the nearest such time is 56 to 65 steps away, exactly the batch-69 range |
| 2. the partner's deep-floor clause `Deep72` | the partner's own arm reaches the floor at 202 of 229 and **`Deep72` holds at all 202**; at the other 27 the clause is vacuous (`deep72_of_off_floor`) |
| 3. `BothNineL5` empty | **false** — see §0: 39 of 229, 67 of 1351 |

Also measured, and uniform: `Ceil72` holds at every ascent of the running arm at 229 of 229; the
low landmark is at level `L + 3` at all 229; both arms satisfy `Mid2Floor` at all 229; where the
running arm reaches the floor (27 of 229) its `Deep72` holds and `NineBeforeDeep` holds. The
greedy reading of `Leg4Land` was checked against the literal one on 596 samples with no
disagreement.

### 2.2 The distance: which readings are available, and what bound each gives

**67 is the bound of the reading chosen, not the pairing's** — and the reading is fixed by how low
the low time is. `Ceil72` needs its peak at arm index three; the pairing read between a time `a` and
a link carrying `L + 9` puts that peak `z k − 1` steps after `a`, where `k` is the number of levels
from `ρ a` up to the peak's level `L + 8` and `z` is the timing law (`z 6 = 71`, `z 7 = 170`,
`z 8 = 409`). Hence, and this is now proved in `HPC/Fold/Reading70.lean`:

| the low time is at | the peak is at least | the bound on `i − a` | the reading |
| --- | --- | --- | --- |
| `L + 2` or below | `a + 70` | **67** | `crooked_peak_valley_high9_mid` |
| `L + 1` or below | `a + 169` | **166** | `crooked_peak_valley_high9` |
| `L` (the floor) | `a + 408` | **405** | `crooked_peak_valley_high9_low` (new) |

All three return a valley at `ρ a + 1 ≤ L + 3` or below and place it far more than the six steps
before the ascent that the clause asks. The three are packaged as `NearLowBandT` / `NearLowBandG`,
and `ceil72_of_nearLowBandT_armG` (with its mirror) proves that **any** of them gives the arm its
ceiling clause. Reading the same pairing against a *different* high time of the running arm changes
nothing: the bound comes only from where the low time is, which is why the theorems quantify over
every ascent.

**What the corpus says about the other two readings.** They have far more room and are **not
available**: at the 229 high-run crossings the nearest time at `L + 1` or below is 295 to 642 steps
from the basepoint (against 166) and the nearest at the floor is 872 to 2035 (against 405), while
the nearest at `L + 2` or below is 56 to 65 (against 67). So the two steps of slack are real, and
the `L + 2` reading is the only one that fires.

**What forces a low time near the basepoint at all.** Nothing that is proved. The partner's failure
of `w8` does put a time at `L + 2` or below on the partner's arm — that is
`w8_floor_fail_of_not_w8` (batch 68), and it is what the crossing gives — but the statement carries
**no index bound**: what the failure returns is a descent `d₀` at `L + 2` or below together with the
information that no time at `L + 7` or above sits in the long window before it, and an arm may
satisfy that with `d₀` arbitrarily far out. No bound is derivable from the crossing clauses as they
stand, and none is claimed here. The distance therefore remains the branch's one open statement, now
in its widest form (`NearLowBandT` / `NearLowBandG`).

### 2.3 The partner's deep-floor clause — closed

**Both deep-floor clauses at a high-run crossing are theorems** (`HPC/Fold/Deep70.lean`), and
neither needs the distance hypothesis. Write `HighRunG ρ i L` for *an ascent of the forward arm to
`L + 9` with nothing at `L + 2` or below before it* — the failure of `DeepFirst2`, written out
(`highRunG_of_not_deepFirst2`).

> **The running arm.** `deep72_of_nineBeforeDeep_armG` (mirror `…_armT`): an arm every one of whose
> descents to the floor follows one of its own ascents to `L + 9` has `w72`'s deep-floor clause.
> The pairing is read **inside the arm**, from the ascent down to the descent
> (`crooked_valley_peak_high9_mid`): it returns a valley at `L + 1` or below seventy steps after the
> ascent and, twenty-nine steps later, a peak at `L + 7` or above, itself seventy steps before the
> descent, where the clause asks for five, six and seven. The ascent itself is the first landmark,
> at arm index four or more by the Lipschitz law. A high run gives this hypothesis for free
> (`nineBeforeDeep_of_highRunG`): a descent to the floor before the ascent would be a time at
> `L + 2` or below before it.
>
> **The partner.** `deep72_partner_armT_of_highRun_armG` (mirror `…_armG_of_highRun_armT`): the
> partner of a high-running arm has `w72`'s deep-floor clause. This is the reading the commission
> asks about — the pairing read at the partner's floor descent **against the running arm's link
> carrying `L + 9`**, across the basepoint — and it does return the missing level. The pairing's
> peak carries `L + 8`, so it is at `L + 7` or above, which is exactly the level `wb`'s ceiling
> clause could not reach. What places the two landmarks on the *partner's* arm is the high run
> itself: the pairing's valley is at `L + 1` or below, and the running arm has nothing at `L + 2` or
> below between the basepoint and its ascent, so the valley — and the peak before it — must lie
> before the basepoint. The third landmark comes from `Mid2Floor` on the partner, read at the
> descent to `L + 2` that the Lipschitz law puts between the valley and the basepoint
> (`exists_eq_strict_isLip`), and the crossing supplies `Mid2Floor` (`crossMid2`).

So the answer to the first half of the question is **yes**: reading the pairing against a link
carrying `L + 9` rather than against a time at `L + 8` returns the level `wb` misses. The answer to
the second half — *is the partner's clause needed at all?* — is that it is still used, but it is no
longer a hypothesis: the assembly asks for it and the theorem above supplies it.

### 2.4 `BothNineL5` — inhabited

See §0 for the finding and its audit. To the rest of the question:

* **Which walk serves it.** At all 39 both-nine high-run crossings some walk of the four-leg family
  serves both arms, and at all 39 both arms satisfy the landmark sentence of `w72` itself; at the
  stored witness six walks of the family serve both arms, the first being `4 → 7 → 2 → 8 → 1`.
* **What the top-of-band pairing gives between the two `L + 9` times.** Nothing. Crookedness is
  triggered by two levels three or more apart; between two links both carrying `L + 9` it says
  nothing at all, and `crooked_peak_valley_high9` needs one low endpoint. The census confirms the
  configuration is common rather than marginal (146409 basepoints of the branch), so there is
  nothing to exclude.
* **Why it no longer matters.** The new assembly is symmetric and does not use the hypothesis. At
  all 39 the partner is deep first at `L + 2`, so its own ceiling clause is the batch-68 theorem
  `ceil72_of_deepFirst2_armT`; the census records that `Ceil72` holds on the partner at all 39.

### 2.5 Assembly

`leg4Land_w72_of_tri_of_mid2_of_ceil` is not about the `w8` side of anything: it reads `w72` off
any arm of the branch that has `Mid2Floor`, the deep-floor clause and the ceiling clause. Batch 70
draws the consequence:

> **`s3_span_nine_mid5_of_cross_ceil_deep`** — at a crossing of the trichotomy at the branch
> `L + 5`, if both arms have `Deep72` and `Ceil72`, both fold onto `w72`.
>
> **`s3_span_nine_mid5_of_cross_highRun_ceil_armG`** (mirror `…_armT`) — at a crossing whose
> forward arm runs high, both deep-floor clauses are discharged by §2.3, so the pair folds as soon
> as both arms have `Ceil72`. No `w8` hypothesis, no `BothNineL5` hypothesis, no partner clause.
>
> **`s3_span_nine_mid5_of_cross_highRun_nearLowT_armG`** (mirror; and
> `s3_span_nine_mid5_of_cross_highRun_band_armG` on the widest reading of §2.2) — with the distance
> hypothesis for the running arm, and for the partner one of: it stops below `L + 9` (its clause is
> then vacuous, `ceil72_of_no_nine`), or it is deep first at `L + 2` (batch 68), or the mirror
> distance holds.

So what the branch at `L + 5` owes at a high-run crossing is **one** statement, the distance, and on
the corpus the partner never needs its mirror: at the 190 crossings where the partner stops below
`L + 9` its clause is vacuous, and at the 39 where it does reach `L + 9` it is deep first at `L + 2`.
`s3_span_nine_mid5` itself is not closed, because the distance is not proved.

The inventory of batch 69 §2.6 is not due: it is asked for once `s3_span_nine` is a theorem, and it
is not.

## 3. Deliverables

1. **What is proved, `sorry`-free, with `#print axioms`.** `axioms-batch70.txt` lists all thirty
   new theorems; every profile is a subset of `[propext, Classical.choice, Quot.sound]`, and two are
   axiom-free. No `native_decide`, no `axiom`, no `implemented_by`.
   * `HPC/Fold/Deep70.lean`: `exists_eq_between_isLip`, `exists_eq_between_isLip'`,
     `exists_eq_strict_isLip`, `exists_eq_strict_isLip'`; the definitions `HighRunG`, `HighRunT`
     with `highRunG_of_not_deepFirst2`, `highRunT_of_not_deepFirst2`, `nineBeforeDeep_of_highRunG`,
     `nineBeforeDeep_of_highRunT`; `deep72_at_of_nine_armG`, `deep72_of_nineBeforeDeep_armG` and
     mirrors; `deep72_partner_armT_of_highRun_armG`, `deep72_partner_armG_of_highRun_armT`;
     `ceil72_of_no_nine`; `s3_span_nine_mid5_of_cross_ceil_deep`,
     `s3_span_nine_mid5_of_cross_highRun_ceil_armG` and mirror,
     `s3_span_nine_mid5_of_cross_highRun_nearLowT_armG` and mirror.
   * `HPC/Fold/Reading70.lean`: `crooked_peak_valley_high9_low`, `crooked_valley_peak_high9_low`,
     `ceil72_at_of_landmarks_armG`, `ceil72_at_of_landmarks_armT`; the definitions `NearLowBandT`,
     `NearLowBandG` with `nearLowBandT_of_nearLowT`, `nearLowBandG_of_nearLowG`,
     `ceil72_of_nearLowBandT_armG`, `ceil72_of_nearLowBandG_armT`,
     `s3_span_nine_mid5_of_cross_highRun_band_armG` and mirror.
2. **The widened census of §2.1, under the audit protocol, with the count of distinct
   configurations.** `census-batch70.c`, log `census-batch70.log`. Its definition audit is printed
   in the source header and in the log: `IsCrookedIvF`, `LowAt`, `Leg4Land` (greedy, with the
   literal reading sampled against it), `DeepFirst2`, `Ceil72`, `Deep72`, `Mid2Floor`,
   `NineBeforeDeep` and `FoldsOnto` are each evaluated by their own definition, and the crookedness
   clause is read exactly as `crooked_peak_valley_high9_mid` reads it. No criterion of the engine is
   used anywhere. The census is over whole pairs and whole arms, not over truncated arms, so no
   arm-length bound applies; the arms seen run from 105 to 2211 times. The finding of §0 is
   re-checked independently by `check70.py` (log `check70.log`) from the stored pair
   `witness-batch70.txt`.
3. **This report**, whose first line names the commission read, with the finding first, then the
   targets, then the five questions.

## 4. What the corpus is, and what it is not

The 229 high-run crossings come from 52 distinct configurations, drawn from windows of `bing 0 10`
through `bing 0 13` at many offsets as well as from `bing 0 9` itself and from chains outside Bing's
family; that is a real widening of the batch-69 corpus, which was one configuration. It is still a
corpus: the uniformity of the distance range (56 to 65 at all 229, the same range as at the 87) is
a measurement and not a theorem, and the fact that the range did not move when the corpus grew
thirty-fold is the strongest evidence the batch has for the one statement the branch still owes.
