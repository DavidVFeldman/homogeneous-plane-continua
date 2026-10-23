# Report: batch 67 — the residue of the branch `L + 5` proved

The commission in the archive is the batch-65 text, which batches 65 and 66 have answered, so the
agenda is again the residue list the last report leaves standing: §2.5 of `REPORT-batch66.md` — the
mixed basepoints and the index of slack — and §2.6, the `w8` side's disjunction. House order:
counterexamples first, then the targets, then the questions, then the deliverables.

**Headline.** Both gaps of §2.5 are closed, and with them the residue of the branch at `L + 5`:

> `crossMid2` — at a crossing of the trichotomy in the branch at `L + 5`, **both** arms satisfy
> `Mid2Floor`, the floor clause at the descents to exactly `L + 2` that `w71` and `w72` ask for.

`crossMid2L5'` is the batch-65 statement of the residue, which follows from it. Batch 63 assumed
the residue, batch 64 named it, batch 65 refuted the version that drops the crossing, batch 66
proved a relaxed form of it on two families of basepoints; it is now a theorem.

## 0. Counterexamples

**One, and it is what forces the shape of the proof of §2.2.**

### 0.1 `Mid2Floor2` does not imply `Mid2Floor` on an arm

`Mid2Floor2` is `Mid2Floor` with the landmark allowed at arm index **two** instead of three; batch
66 proves the residue in that relaxed form, and §2.1 below proves the relaxed form at every
crossing. `not_mid2Floor_of_mid2Floor2_arm` (`HPC/Fold/Mid2Slack67.lean`) refutes

> an arm of the band `[L, L + 9]`, based at `L + 5`, 1-Lipschitz and obeying the timing law in the
> form `ArmSep` — `k` levels cost `z k - 1` steps — that satisfies `Mid2Floor2` satisfies
> `Mid2Floor`

at the fifteen-time arm

```
cex67 :  5 6 6 5 5 5 5 5 5 4 4 4 3 3 2
index :  0 1 2 3 4 5 6 7 8 9 . . . . 14
```

Its only time at `L + 2` is its index fourteen; its only times at `L + 6` are its indices one and
two. So the relaxed clause is met, at index two (`mid2Floor2_cex67`), and the clause itself is not
(`not_mid2Floor_cex67`): from index three on the arm never reaches `L + 6` again. The descent obeys
the law with room to spare (`cex67_armSep`) — four levels fourteen steps apart where twelve are
asked, three levels six where five are asked, two levels two where two are asked. All three
readings are decided by the kernel.

So the missing index cannot be recovered on one arm. §2.2 recovers it from the pairing instead,
which is the same lesson `not_armCrossMid2L5` of batch 66 taught about the residue itself.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`; the branch's residue `CrossMid2L5'` is **proved** (`crossMid2L5'`), and the batch-64 two-walk assembly now runs with no residual clause |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged |
| `s3_general` | `HPC/Fold/General.lean` | unchanged |
| `theorem3` | `HPC/Fold/Open.lean` | unchanged, waits on `s3_general` |

What moved. Batch 66 proved the residue for the relaxed clause on the basepoints whose two arms are
both **high first** (a time at `L + 8` before every descent to `L + 1`) and on those whose two arms
are both **deep first** (a descent to `L + 1` before every ascent to `L + 9`), leaving the *mixed*
basepoint, the second disjunct of the branch hypothesis, and the index. All three are gone.
`s3_span_nine_mid5_of_cross_wb_two_walks_of_cross` is the batch-64 two-walk form with its
`Mid2Floor` hypothesis discharged: at a crossing whose partner is served by `wb`, the pair folds as
soon as the `w8` side satisfies `w71`, or satisfies `w72` while the partner has its deep-floor
clause. That last disjunction — §2.6 of batch 66, measured at 461 of 461 — is what the branch still
owes.

## 2. The questions

### 2.1 The mixed basepoint

**There is no third kind of arm.** `highFirst_or_deepFirst` (`HPC/Fold/Mid2Mixed67.lean`): every
arm of the band is high first or deep first. If the arm is not high first it has a descent `d` to
`L + 1` with no earlier time at `L + 8`; a time at `L + 9` before `d` would be that missing time,
so every time at `L + 9` is past `d`, and `d` itself witnesses deep first. The two families of
batch 66 are therefore exhaustive arm by arm, and the case they leave is precisely: one arm high
first only, the other deep first only.

**The pairing at the top of the band.** The seam that blocked the mixed case is the one §2.5.1 of
batch 66 names: `crooked_peak_valley_high8`, read against a link at `L + 2`, returns a peak whose
interval reaches `L + 7` and a valley at `L + 3` or below — each one level short of what the two
walks ask. `crooked_peak_valley_high9` is the same pairing read against a link at `L + 1` or below
and a link carrying the top level `L + 9` of the band. Because the high link carries `L + 9`
itself, the peak carries `L + 8`, so

* its own level is `L + 7` or above — a link is one level wide — and its interval reaches `L + 8`;
* the valley after it is at `L + 2` or below.

`L + 7` is exactly what `w3`'s ceiling clause asks for at a descent to `L + 1`; `L + 2` is exactly
what `wb`'s deep clause asks for at an ascent to `L + 9`. The timing law spaces the three: `169`
steps from the low link to the peak, `70` from the peak to the valley, `169` from the valley to the
high link. `crooked_valley_peak_high9` is the same pair read from the high link.

**The peak decides which walk.** `mixed_ceilT_or_deepG_of_land`, and its mirror
`mixed_ceilG_or_deepT_of_land`: read that pairing between one arm's descent to `L + 1` and the
other arm's time at `L + 9`. The peak lands on one of the two arms, and either way the landmark —
a time at `L + 4` or below, at arm index three or more, before every link whose interval reaches
`L + 8` — supplies the chain's first link on the arm the peak lies on. Then

* peak on the arm with the **descent**: that arm has `w3`'s ceiling clause at that descent;
* peak on the arm with the **ascent**: that arm has `wb`'s deep clause at that ascent, the valley
  after the peak being the clause's last link.

The landmark must be readable at a link whose *interval* reaches `L + 8` and not only at a time at
`L + 8`, because the peak's own level may be `L + 7`.

**One walk for both arms.** `w3_or_wb_of_land`: at a basepoint of the branch with the branch
hypothesis on both arms and that landmark on both arms, **either** `w3` serves both arms **or**
`wb` serves both. The proof is the dichotomy above plus one case split:

* both arms high first — both get `w3`, by `ceilChain_of_highFirst_armG` / `..._armT` and
  `leg4Land_w3_armG_of_ceilChain` / `..._armT`;
* both arms deep first — both get `wb`, by `leg4Land_wb_of_land_of_deepFirst` (batch 66);
* mixed, say the forward arm high first and the backward arm deep first — ask whether **every**
  descent of the backward arm carries `w3`'s ceiling clause. If it does, both arms get `w3`. If it
  does not, fix a descent that fails; then at every time of the forward arm at `L + 9` the peak of
  the pairing with that descent cannot lie on the backward arm — it would give the failing descent
  its clause — so it lies on the forward arm, and the forward arm has `wb`'s deep clause at every
  one of its ascents. Both arms then get `wb`
  (`leg4Land_wb_of_land_of_deepChain`, `wb_chain_of_land`).

Nothing in this asks how the branch hypothesis is met at a descent, so gap 1 of batch 66's §2.5
disappears with it: `wb` accepts either disjunct, and where `w3` is used its ceiling clause comes
from the pairing and not from the disjunct.

**The residue for the relaxed clause.** A failure of `Mid2Floor2` on either arm supplies that
landmark on both arms (the `σ`-forms of the batch-66 lemmas: `land_ascent_sig_of_mid2fail2`,
`land_ascent_armT_sig_of_mid2fail2` and their two mirrors), so `crossMid2_relaxed`
(`HPC/Fold/Mid2MixedG67.lean`) — at a crossing both arms satisfy `Mid2Floor2`.

### 2.2 The index of slack, recovered from the pairing

Everything downstream of the landmark is already generic — `w3_or_wb_of_land` asks only for the
landmark — so it is enough to prove the landmark from a failure of `Mid2Floor`, which is the weaker
hypothesis. A failure of `Mid2Floor` at a descent `d` to exactly `L + 2` leaves the window
`[3, d - 4]` empty of times at `L + 6` or above, one index narrower than the window a failure of
`Mid2Floor2` leaves. Two places feel the difference, and both are repaired
(`HPC/Fold/Mid2Index67.lean`):

* **the index a high link forces.** A link whose interval reaches `L + 8` is at arm index **five**
  or more, not two: three levels above the basepoint cost `z 3 - 1 = 5` steps. The batch-66 proofs
  read the *level* and used 1-Lipschitzness, which gives only two; reading the interval through the
  timing law gives five, and the narrower window still applies
  (`armG_index_of_sig8`, `armT_index_of_sig8`, `mid2fail_high_late_armT`,
  `mid2fail_high_late_armG`).
* **the peak of the pairing at index two.** At a descent of the partner the pairing's peak is at
  `L + 6` or above with its interval reaching `L + 7`, which the law puts at arm index two or more
  and no further; where it is exactly two the window does not reach it. But then the valley that
  follows it, at `L + 3` or below, would have to sit at arm index one or zero of the same arm, and
  the arm is at `L + 4` or above there, because it starts at `L + 5` and is 1-Lipschitz. So the
  valley is a time of the *other* arm, which is all the landmark lemma claims
  (`land_ascent_sig_of_mid2fail`, `land_ascent_armT_sig_of_mid2failG`).

This is why §0.1 is not an obstruction: the missing index is recovered from the two-arm pairing,
which §0.1 leaves untouched, and not from the arm.

Hence `land_ascent_sig_of_mid2fail`, `land_ascent_armT_sig_of_mid2fail`,
`land_ascent_armG_sig_of_mid2failG`, `land_ascent_armT_sig_of_mid2failG`, and through
`w3_or_wb_of_land`:

* `w3_or_wb_of_mid2floorFailT` and `..._FailG` — at a basepoint of the branch where either arm
  fails `Mid2Floor`, one reflected walk serves both arms;
* `s3_span_nine_mid5_of_mid2floorFailT` and `..._FailG` — so the pair folds there;
* **`crossMid2`** — at a crossing of the trichotomy both arms satisfy `Mid2Floor`;
* `crossMid2L5'` — the batch-65 statement of the residue, which `crossMid2` implies.

### 2.3 Assembly

`s3_span_nine_mid5_of_cross_wb_two_walks_of_cross` and its mirror are the batch-64 two-walk form
with the residual clause discharged: at a crossing of the trichotomy whose partner is served by
`wb`, the pair folds as soon as the `w8` side satisfies `w71`, or satisfies `w72` while the partner
has its deep-floor clause. Batch 64 measured that disjunction at 461 of 461 crossings of the corpus
and batch 66 did not attempt it; it is what the branch at `L + 5` now owes, together with the
partner's `wb` — which batch 64's census puts at 461 of 461 as well (`mid2Fail_w3_or_wb` places a
failing arm on `w3` or `wb`, and at a crossing `w3` cannot serve both).

### 2.4 The `w8` side's disjunction

Not attempted this batch; see §2.3 for why it is now the branch's only remaining item.

### 2.5 `LandWalkP3Suffices`

Not attempted. The batch-64 rule — no sufficiency statement until the arm probe has covered arms at
least twice the walk's length, which for the walks in question is forty times — has still not been
met, and no probe was run in this batch.

## 3. Deliverables

**Four new Lean files, all `sorry`-free, no `native_decide`, no new axiom.**

* `HPC/Fold/Mid2Mixed67.lean` — `HighFirst`, `DeepFirst`, `highFirst_or_deepFirst`;
  `crooked_peak_valley_high9`, `crooked_valley_peak_high9`; the `σ`-forms
  `land_ascent_sig_of_mid2fail2`, `mid2fail2_high_late_sig`, `land_ascent_armT_sig_of_mid2fail2`;
  the case split `mixed_ceilT_or_deepG_of_land`, `mixed_ceilG_or_deepT_of_land`; the walk lemmas
  `wb_chain_of_land`, `leg4Land_wb_of_land_of_deepChain`, `leg4Land_w3_armG_of_ceilChain`,
  `leg4Land_w3_armT_of_ceilChain`, `ceilChain_of_highFirst_armG`, `ceilChain_of_highFirst_armT`;
  and `w3_or_wb_of_land`, `s3_span_nine_mid5_of_land`, `w3_or_wb_of_mid2failT`,
  `s3_span_nine_mid5_of_mid2failT`, `not_triCross_of_mid2failT`, `crossMid2_relaxed_armT`.
* `HPC/Fold/Mid2MixedG67.lean` — the mirror's landmark lemmas `mid2fail2_high_late_G_sig`,
  `land_ascent_armG_sig_of_mid2fail2G`, `land_ascent_armT_sig_of_mid2fail2G`; and
  `w3_or_wb_of_mid2failG`, `s3_span_nine_mid5_of_mid2failG`, `not_triCross_of_mid2failG`,
  `crossMid2_relaxed_armG`, `crossMid2_relaxed`.
* `HPC/Fold/Mid2Slack67.lean` — `cex67` with its readings `cex67_isLip`, `cex67_lb`, `cex67_ub`,
  `cex67_base`, `cex67_span`, `cex67_armSep`, `mid2Floor2_cex67`, `not_mid2Floor_cex67`, and the
  refutation `not_mid2Floor_of_mid2Floor2_arm`.
* `HPC/Fold/Mid2Index67.lean` — `mid2Fail_witness3`, `armG_index_of_sig8`, `armT_index_of_sig8`,
  `mid2fail_high_late_armT`, `mid2fail_high_late_armG`, `land_ascent_sig_of_mid2fail`,
  `land_ascent_armT_sig_of_mid2fail`, `land_ascent_armG_sig_of_mid2failG`,
  `land_ascent_armT_sig_of_mid2failG`, `w3_or_wb_of_mid2floorFailT`, `w3_or_wb_of_mid2floorFailG`,
  `s3_span_nine_mid5_of_mid2floorFailT`, `s3_span_nine_mid5_of_mid2floorFailG`, `crossMid2`,
  `crossMid2L5'`, `s3_span_nine_mid5_of_cross_wb_two_walks_of_cross` and its mirror.

All four are imported by `HPC.lean`; `lake build HPC` is clean and free of linter warnings in the
new files. The only edit to an earlier file is those four import lines. The project's `sorry`s are
exactly the four standing targets — `s3_span_nine_mid5` (`Mixed.lean`), `s3_span_nine` and
`s3_general` (`General.lean`) and `theorem3` (`Open.lean`) — and nothing this batch adds uses any of
them.

```
'HPC.Fold.highFirst_or_deepFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crooked_peak_valley_high9' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crooked_valley_peak_high9' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_sig_of_mid2fail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2fail2_high_late_sig' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armT_sig_of_mid2fail2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mixed_ceilT_or_deepG_of_land' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mixed_ceilG_or_deepT_of_land' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.wb_chain_of_land' depends on axioms: [propext, Quot.sound]
'HPC.Fold.leg4Land_wb_of_land_of_deepChain' depends on axioms: [propext, Quot.sound]
'HPC.Fold.leg4Land_w3_armG_of_ceilChain' depends on axioms: [propext, Quot.sound]
'HPC.Fold.leg4Land_w3_armT_of_ceilChain' depends on axioms: [propext, Quot.sound]
'HPC.Fold.ceilChain_of_highFirst_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.ceilChain_of_highFirst_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.w3_or_wb_of_land' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_land' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.w3_or_wb_of_mid2failT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_mid2failT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_triCross_of_mid2failT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crossMid2_relaxed_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2fail2_high_late_G_sig' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armG_sig_of_mid2fail2G' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armT_sig_of_mid2fail2G' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.w3_or_wb_of_mid2failG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_mid2failG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_triCross_of_mid2failG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crossMid2_relaxed_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crossMid2_relaxed' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cex67_armSep' depends on axioms: [propext, Quot.sound]
'HPC.Fold.mid2Floor2_cex67' depends on axioms: [propext, Quot.sound]
'HPC.Fold.not_mid2Floor_cex67' depends on axioms: [propext, Quot.sound]
'HPC.Fold.not_mid2Floor_of_mid2Floor2_arm' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2Fail_witness3' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.armG_index_of_sig8' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.armT_index_of_sig8' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2fail_high_late_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2fail_high_late_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_sig_of_mid2fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armT_sig_of_mid2fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armG_sig_of_mid2failG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_ascent_armT_sig_of_mid2failG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.w3_or_wb_of_mid2floorFailT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.w3_or_wb_of_mid2floorFailG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_mid2floorFailT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_mid2floorFailG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crossMid2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.crossMid2L5'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_wb_two_walks_of_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_wb_two_walks_armG_of_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**No census or probe was run in this batch.** Every statement here is proved from the definitions,
from crookedness and from the timing law; the counterexample of §0.1 is decided by the kernel. The
numbers quoted from earlier batches are cited as theirs, and the corpus figures for the `w8` side's
disjunction (§2.3) are batch 64's, not new measurements.

## 4. Not in this batch

The `w8` side's disjunction, which is what the branch at `L + 5` now owes; `Leg4SixCrossL5` and
`s3_span_nine_mid5` itself; a replacement sufficiency statement for the landmark sentence, whose
probe bound of forty times has still not been reached; spans ten and above; Bing 1948 Theorems 4, 5,
6, 13; the 1951 reduction.
