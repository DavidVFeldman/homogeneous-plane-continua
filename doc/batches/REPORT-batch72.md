# Report — batch 72

The commission read is `COMMISSION-batch72.md` (identical copy `COMMISSION.md`), the batch-72
archive's text: *the valley at L + 3.*

New in the project: two Lean files, `HPC/Fold/Valley72.lean` and `HPC/Fold/Audit72.lean`, both
`sorry`-free and imported by `HPC.lean`; the census `census-batch72.c` with its log
`census-batch72.log` and its seeds `seeds-batch72.txt`; the construction attempt `break-batch72.c`
(log `break-batch72.log`); the minimiser `min-batch72.c` (log `min-batch72.log`); the stored
witnesses `witness-batch72-c0.txt`, `-c1.txt`, `-c2.txt` and `witness-batch72-min.txt`; the
independent re-check `check72.py` (log `check72.log`); the axiom profiles of all new theorems in
`axioms-batch72.txt`. `lake build` is clean and the project's `sorry`s are still exactly the four
standing targets (`s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`) — I added none.

## 0. The counterexample, first

**The valley is not a fact about a running arm of the branch.** `Valley3BeforeNine` — the landmark
pair batch 71 proved equivalent to `Ceil72` and had never seen fail — is **false** without the
crossing, and the refutation is a Lean theorem checked by the kernel:

> **`not_valley3BranchL5`** (`HPC/Fold/Audit72.lean`): there is a faithful pair of **78 links** — a
> thin window of Bing's own chain `bpath 0 9` — with a basepoint at `L + 5`, band `[L, L + 9]`,
> `LowAt (L + 1) (L + 8)` on both arms, whose **forward arm runs high** (it reaches `L + 9` at arm
> index 76 with nothing at `L + 2` or below before it) and which has **no** peak at `L + 6` or above
> at arm index three or more with a time at `L + 3` or below five steps later and six steps before
> that ascent. Equivalently (`not_ceil72_armG`), `Ceil72` fails on that arm.

Everything is put to the kernel in the manner of `HPC/Fold/Audit71.lean`: `Audit72.faithful` is
`IsCrookedIvF ρ σ` by the interval search of `HPC/Fold/DichotomyFaithful.lean` with `decide +kernel`,
and `lip`, `band_lo`, `band_hi`, `base_level`, `lowAt_armG`, `lowAt_armT`, `highRun_armG`,
`not_valley3_armG` and `not_ceil72_armG` are `decide +kernel` as well. No `native_decide`, no
`axiom`; every profile in `axioms-batch72.txt` is a subset of `[propext, Classical.choice,
Quot.sound]`, three of them without `Classical.choice`.

**The definition audit.** The finding is re-checked from scratch by `check72.py` (log
`check72.log`), with `IsCrookedIvF`, `LowAt`, `HighRunG`, `Valley3BeforeNine`, `Ceil72`, `Leg4Land`
and `FoldsOnto` written out again in Python, independently of the C of the census and of the Lean,
on the stored 986-link pair and on the 78-link window:

```
witness-batch72-min.txt: 78 links, basepoint 1, the running arm is the forward arm
  IsCrookedIvF: True;  the band: [3, 9] inside [L, L+9];  rho i = 5
  LowAt on both arms: True
  the running arm runs high: True (first ascent at arm index 76)
  Valley3BeforeNine on the running arm: False
  Ceil72 on the running arm: False; on the partner: True
  the trichotomy: forward -8b, backward 38b; shared: w8, wb  -- NOT a crossing
  walks of the four-leg family serving both arms: 15
```

**It is not a counterexample to `S3`.** At the witness fifteen walks of the four-leg family serve
both arms, and at **all 194 076** failures the census records a walk of the family serves both arms.
What is refuted is the placement of the statement: `Valley3BeforeNine` on a running arm is not a
theorem of the branch, and any proof of it must use the **crossing**.

**Why the crossing is what carries it, and this is now a theorem.** A running arm of the band is
always a `w8` arm (`leg4Land_w8_of_run`), so at a failing basepoint the crossing can only come from
the partner failing `w8` — and the census finds that at every one of the 187 132 failing
(basepoint, running arm) pairs the two arms *share* `w8`. The construction of §2.3 then failed to
take `w8` off the partner in 23 080 attempts.

## 1. The targets

`s3_span_nine_mid5`, `s3_span_nine`, `s3_general` and `theorem3` are **not** proved in this batch.
What the batch does is place the statement they were waiting on, close the missing half of batch 71
§2.5, and use it to discharge one of the two obligations the batch-70 assembly carries. No refuted
statement has been deleted: `Valley3BeforeNine` and every theorem about it are conditional
statements and remain true as stated; what is now known — recorded in `HPC/Fold/Audit72.lean` and in
the header of `HPC/Fold/Valley72.lean` — is that the branch hypothesis alone does not imply it.

## 2. The questions

### 2.1 Is it a crossing fact at all?

**Yes — and nothing weaker.** `census-batch72.c` re-runs the batch-70 corpus unchanged (64 base
level sequences, 7040 faithful pairs, 12 392 192 links, 3 151 162 basepoints of the band, 2 444 297
of the branch, 1351 crossings, **229 high-run crossings**, arms of 105 to 2211 times at those, so
the batch-70/71 counts are reproduced exactly) and reads `Valley3BeforeNine` by its own definition
on every arm that runs high, in five classes:

| class | running arms | holds | fails | first ascent | arm lengths |
| --- | --- | --- | --- | --- | --- |
| the band, `LowAt` asked of nothing | 478 735 | 284 659 | **194 076** | 12 … 396 | 13 … 2353 |
| the band, `LowAt` on the running arm | 478 735 | 284 659 | **194 076** | 12 … 396 | 13 … 2353 |
| the branch, `LowAt` on both arms | 478 735 | 284 659 | **194 076** | 12 … 396 | 13 … 2353 |
| a running arm at a crossing | 229 | **229** | 0 | 104 … 335 | 105 … 1917 |
| the running arm of a high-run crossing | 229 | **229** | 0 | 104 … 335 | 105 … 1917 |

So `LowAt` changes nothing at all — on this corpus every running arm of a band basepoint already has
`LowAt` on both arms — and the statement is **not** a fact about a running arm of a faithful pair,
with or without the branch hypothesis. It is a fact about a running arm **at a crossing**, where it
holds at all 229. This is a census over whole pairs and whole arms, so no arm-length bound applies;
and because the statement already fails without the crossing, the batch-64 rule (probe the arm-only
class) does not apply — there is nothing to probe for.

**How it fails.** Of the 194 076 failures, 165 724 have no time at `L + 3` or below early enough
(the arm's approach never descends that far before its ascent, or descends only within six steps of
it) and 28 352 have such a time but no peak at `L + 6` or above five steps before it. The first
ascent of a failing arm ranges over 12 … 178. The histogram of the first ascent of a running arm
begins at **12** — the timing law's `z 4 − 1`, and the shortest crooked rise from `L + 5` to `L + 9`
— and `Valley3BeforeNine` is *unsatisfiable* whenever that ascent is at 13 or less, since the clause
asks for a peak at arm index three or more, a valley five steps later and six more before the
ascent. 10 767 running arms of the corpus have their ascent at exactly 12.

**What the failures share.** At every one of the 187 132 failing (basepoint, running arm) pairs the
two arms share the walk `w8` (103 410 share `w8` alone, 83 722 share `w8` and `wb`); `w3` is never
shared. So no failure is a crossing, which is exactly the table's last two rows — and the reason is
a theorem: `leg4Land_w8_of_run`.

### 2.2 The reading that places the valley

The descending pairing of batch 71 §2.3 is now a theorem — `crooked_mid5_low2` and its mirror
`crooked_low2_mid5` (`HPC/Fold/Valley72.lean`): a link carrying `L + 5` and a link carrying `L + 2`
have a link carrying `L + 3` strictly between them. The census measures its availability at the 229
high-run crossings, trying **every** link carrying `L + 5` on the running arm's own side (arm index
1 … 400) against the nearest link carrying `L + 2` on the partner's side:

| | |
| --- | --- |
| a link carrying `L + 5` on the running arm's side | at all **229** |
| a link carrying `L + 2` on the partner's side | at all **229**, 56 to 65 steps past the basepoint |
| a reading of that shape exists | at all **229** |
| *some* reading puts its landmark on the running arm at an index the clause can use | at **31** |
| and there it is exactly the `Ceil72` valley | at all **31** |
| readings whose landmark lands past the point the clause can use | 2769 |

So the answer to *is the reading available* is **yes everywhere**, and the answer to *does it name
the valley* is **only at 31 of 229** — at the other 198 every reading of that shape puts its
landmark past the basepoint, on the partner's arm, where the clause cannot use it. Where it does
land on the running arm, the `L + 5` link that names it sits at arm index 36 to 181 and the landmark
2 to 138 steps further in (the counterexample of batch 71 is of this kind: `L + 5` at 36, landmark
at 34).

**The index question, answered in the negative.** Crookedness places its landmarks *somewhere*
strictly between the endpoints and the timing law bounds them only from the endpoints: between
`L + 5` and `L + 3` two levels cost two steps, between `L + 3` and `L + 4` one costs one, between
`L + 4` and `L + 2` two cost two. There is no upper bound at all on how far past the `L + 5` link
the landmark sits, and the census exhibits the failure: 2769 readings place it past the usable
point. `low_nine_sep` separates the `L + 2` endpoint from the ascent by 169, which bounds the low
endpoint away from the ascent but says nothing about where inside the interval the landmark lands.
What *is* free is the other landmark: `run_peak_armG` / `run_peak_armT` prove that the pairing
between the basepoint and the ascent always puts a link at `L + 7` or above at arm index five or
more and at least seven steps before the ascent, so a reading of `Ceil72` on a running arm has only
the valley left to place (`valley3BeforeNine_of_peak_low`).

### 2.3 Break the valley

`break-batch72.c` carries batch 71's machinery over, with one new edit, and runs two attacks.
`cut` is the inverse of batch 71's surviving `stretch`: delete the material between two links of
equal level — the one edit that can *remove* a level pattern without lifting a link out of the band.

**Attack A** takes the 64 stored high-run crossings of `census-batch71.c` and edits the running
arm's approach, aiming at its valley (cuts bracketing it, the raise of the valley link and its
neighbours, splices and stretches on either side of it):

| edit | tried | faithful | still a crossing | still a high run | breaks it |
| --- | --- | --- | --- | --- | --- |
| `cut` | 27 744 | **0** | 0 | 0 | 0 |
| `stretch` | 2 722 | 2 229 | 43 | 2 | 0 |
| `raise` | 119 | 0 | 0 | 0 | 0 |
| `splice` (a crooked descent of the sub-band) | 2 164 | 0 | 0 | 0 | 0 |

**Attack B** takes the 96 sampled basepoints at which the running arm *already* fails the valley and
edits the partner, aiming at its `w8` sentence — which, by §0, is the only thing standing between
such a basepoint and a crossing:

| edit | tried | faithful | still a crossing | still a high run | breaks it |
| --- | --- | --- | --- | --- | --- |
| `cut` | 15 273 | 320 | **0** | 0 | 0 |
| `stretch` | 3 629 | 2 269 | **0** | 0 | 0 |
| `raise` | 265 | 1 | **0** | 0 | 0 |
| `splice` | 3 913 | 148 | **0** | 0 | 0 |

55 829 edits, and **no crossing whose running arm fails `Valley3BeforeNine`**. Every edited pair is
re-tested for `IsCrookedIvF` and re-scanned from scratch for the band, the basepoint, `LowAt`, the
trichotomy, the high run and the valley; nothing is inherited from the seed.

**The obstruction, named.** Three obstructions, and they are different in kind.

* `cut` is killed by crookedness outright: **0 of 27 744** survive in attack A and 320 of 15 273 in
  attack B. Deleting a stretch of a crooked chain deletes the very landmarks crookedness demands
  between the links on either side of it — the mirror image of batch 71's finding that *adding* a
  retraced stretch is always safe.
* `raise` and the downward `splice` are killed exactly as batch 71's `raise` and `band` were:
  removing a low time, or splicing in a whole crooked descent of the sub-band, adds a level pattern
  the surrounding chain is not crooked against.
* `stretch` survives in bulk (2 229 of 2 722, 2 269 of 3 629) and is useless for this target, for
  the reason batch 71 recorded: it adds no new level pattern. It moves indices, so it can destroy
  the crossing or the high run — and it does, leaving only 43 crossings and 2 high runs in attack A
  — but it can neither delete the running arm's valley nor give the partner a low time before its
  first high.

Attack B's column of zeros is the sharpest statement of the obstruction: **no edit ever took `w8`
off the partner**. For that the partner would need a time at `L + 2` or below before its first time
at `L + 7` or above, and every edit that can introduce one destroys faithfulness.

### 2.4 `BothHighRunL5` at a crossing — closed

**The missing half is a theorem.** The commission asks whether a `w8` arm can run high while its
partner runs high. It cannot, and the reason is simpler than the two-`w3` reading batch 71 used:

> **`leg4Land_w8_of_run`** (`HPC/Fold/Valley72.lean`): an arm of the band based at `L + 5` that runs
> high **is** a `w8` arm. Inside the band the `w8` sentence has only its first clause — every time
> at `L + 2` or below is preceded by a time at `L + 7` or above, at arm index four or more and by at
> least `L + 7 −` its level steps — and the arm's own ascent serves as that time: the high run puts
> every low time *after* the ascent, the timing law (`z 7 = 170`) puts it 169 steps after, where the
> clause asks for at most seven, and `z 4 = 13` puts the ascent itself at arm index 12 or more.

Hence, with the arm forms `leg4Land_w8_armG_of_highRun` and `leg4Land_w8_armT_of_highRun`:

> **`not_bothHighRun_of_cross`**: at a crossing at most one arm runs high — both would be `w8` arms
> and `w8` would serve both. Equivalently `not_cross_of_bothHighRun`.

The census line of batch 71 — both arms run high at 16 235 basepoints of the branch and at **0** of
the 1351 crossings — is therefore a theorem, and it is reproduced by `census-batch72.c` exactly
(16 235 and 0, and 0 of the 229 high-run crossings). The shapes the census sees at the 16 235: at
least one arm is a `w8` arm at all of them, both arms are `w3` arms at none, both are `wb` arms at
4 588, exactly one at 7 522, and neither arm is `w3` or `wb` at 4 125.

**What closing it buys, as the commission said it would.** At a crossing whose forward arm runs
high, the backward arm does not, so it is deep first at `L + 2`, so the batch-68 route gives it its
ceiling clause:

> **`deepFirst2_partner_of_cross_highRunG`** and **`ceil72_partner_of_cross_highRunG`** (and the
> mirrors): the partner's `Ceil72` at a high-run crossing, in general.

So the batch-70 assembly's second hypothesis is discharged, and what a high-run crossing owes is one
clause on one arm:

> **`s3_span_nine_mid5_of_cross_highRun_ceilRun_armG`** (and its mirror): at a crossing whose forward
> arm runs high, `Ceil72` on **that arm alone** — equivalently `Valley3BeforeNine` — gives a walk
> onto which both arms fold.

**And the crossing does give the running arm something.** Since the running arm is a `w8` arm, the
crossing takes `w8` off the partner, and inside the band that failure *produces a time of the
partner at `L + 2` or below*:

> **`partnerLow_of_cross_highRunG`**: at a high-run crossing the partner has a time at `L + 2` or
> below strictly before the basepoint; and **`partnerLow_sep_of_cross_highRunG`**: its distance to
> the basepoint plus the arm index of the running arm's ascent is at least 169.

So what the branch owes is no longer the *existence* of the low time the batch-69 reading needs but
only its **distance**: `NearLowT` asks for one within 67, batch 71's counterexample has one at 185,
and the census sees 56 to 65 at all 229 of the corpus.

### 2.5 Assembly

Not due: §2.1–2.3 do not make `Valley3BeforeNine` a theorem — §2.1 refutes it outside the crossing
and §2.3 fails to break it inside. `s3_span_nine_mid5` is still `sorry`. What the branch at `L + 5`
owes is now one statement about one arm, with the partner's half discharged:

> **at a crossing of the trichotomy at `L + 5` whose forward arm runs high, that arm has a peak at
> `L + 6` or above at arm index three or more and, five steps later, a time at exactly `L + 3`, at
> least six steps before its first ascent to `L + 9`.**

The census sees it at all 229 crossings of the corpus, and batch 71 saw it at all 2229 crossings of
its construction; it is false at 194 076 basepoints that are not crossings, and 55 829 edits did not
produce a crossing at which it fails.

## 3. Deliverables

1. **What is proved, `sorry`-free, with `#print axioms`** (`axioms-batch72.txt`; every profile a
   subset of `[propext, Classical.choice, Quot.sound]`, three of them without `Classical.choice`; no
   `native_decide`, no `axiom`, no `implemented_by`).
   * `HPC/Fold/Valley72.lean`: `leg4Land_w8_of_run` with `leg4Land_w8_armG_of_highRun` and
     `leg4Land_w8_armT_of_highRun`; `not_bothHighRun_of_cross` and `not_cross_of_bothHighRun`;
     `deepFirst2_partner_of_cross_highRunG` / `…T` and `ceil72_partner_of_cross_highRunG` / `…T`;
     `s3_span_nine_mid5_of_cross_highRun_ceilRun_armG` / `…T`; `crooked_mid5_low2` and
     `crooked_low2_mid5`; `run_peak_armG` and `run_peak_armT`; `valley3BeforeNine_of_peak_low`;
     `partnerLow_of_cross_highRunG` and `partnerLow_sep_of_cross_highRunG`.
   * `HPC/Fold/Audit72.lean`: `Valley3BranchL5` and its refutation `not_valley3BranchL5`, with the
     witness `Audit72.rho78`, `Audit72.sig78` and the kernel-checked facts `faithful`, `lip`,
     `band_lo`, `band_hi`, `base_level`, `lowAt_armG`, `lowAt_armT`, `highRun_armG`,
     `not_valley3_armG`, `not_ceil72_armG`.
2. **The censuses of §2.1 and §2.2 and the construction of §2.3, under the audit protocol.**
   `census-batch72.c` (log `census-batch72.log`) evaluates `IsCrookedIvF`, `LowAt`, `Leg4Land`
   (greedy, with the literal reading sampled against it — 4000 samples, 0 disagreements),
   `HighRunG` / `HighRunT`, `Valley3BeforeNine`, `Ceil72` and `FoldsOnto` each by its own
   definition; it is a census over whole pairs and whole arms, so **no arm-length bound applies**
   (the arms seen at a high-run crossing run from 105 to 2211 times, and over all classes from 13 to
   2353). `break-batch72.c` (log `break-batch72.log`) re-tests every edited pair from scratch.
   `min-batch72.c` (log `min-batch72.log`) trims the counterexample to the 78-link window the kernel
   checks, and `check72.py` (log `check72.log`) re-checks every stored witness from literal
   definitions, independently of the C and of the Lean.
3. **This report**, whose first line names the commission read, with the counterexample first, then
   the targets, then the five questions.

## 4. What is now open

The branch at `L + 5` owes exactly one thing at a high-run crossing: `Ceil72`, equivalently
`Valley3BeforeNine`, on the **running** arm — and it is now known that the crossing is not
dispensable in that statement. The two things the crossing supplies, and that a proof must use, are
now theorems: the partner is not a `w8` arm, and therefore has a time at `L + 2` or below before the
basepoint (`partnerLow_of_cross_highRunG`), at least `169 − e` steps away. Whether that low time can
be put within 67 — or whether the valley can be placed from it by a reading with an index bound —
is the question batch 71's counterexample and batch 72's §2.2 leave standing.
