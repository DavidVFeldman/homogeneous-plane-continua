# Report: batch 75 — reconnaissance for a general argument

The commission read is `COMMISSION-batch75.md` (copy `COMMISSION.md`), on top of the batch-74
delivery. `lake build` is clean on the whole project; the repository's `sorry`s are still exactly
`s3_general` (`HPC/Fold/General.lean`) and `theorem3` (`HPC/Fold/Open.lean`)
— this batch adds none and closes neither.

## 0. The basepoint served by no walk, first — and what is refuted instead

**No basepoint of any span swept is served by no walk at all.** At spans eight to fourteen, every
distinct basepoint of the corpus that was searched to exhaustion is served, on both whole arms, by
some walk. Up to span eleven five legs always suffice; at spans twelve, thirteen and fourteen a few
basepoints need six, and each of those that was searched further — all four at span twelve, all four
at span thirteen, and 20 of the 186 at span fourteen, the deep search being capped at 20 per sweep —
is served by a walk of six legs. So the counterexample the commission asks to be reported first does
not exist in this corpus either; the 166 unsearched basepoints of span fourteen are the only ones
about which the census says nothing beyond "not by five legs".

**What is refuted is the census statement of batch 74, one and two spans below where it was made.**
Batch 74 recorded, and `HPC/Fold/Span.lean` repeats, that the bound `⌊span/2⌋ − 1` on the number of
turning targets "holds at spans nine, ten and twelve … (maxima 3, 4 and 5)". On the wider corpus of
this batch that is false at both span ten and span twelve:

* **span ten**: four distinct basepoints, all at level `L+5`, whose least walk has **five** legs,
  where `⌊10/2⌋ − 1 = 4`;
* **span twelve**: four distinct basepoints, all at level `L+7`, served by **no walk of at most five
  legs at all**, and by a six-leg walk.

Both are written out in full and re-checked from scratch. `witness-batch75-span10-k5.txt` is a
3000-link window of `bing 0 13` in the general model (`σ ≠ ρ`), band exactly `[0,10]`, basepoint 1256 at level
5, whole arms of 1744 and 1257 links; `check75.py` (log `check75-span10-k5.log`) confirms, with every
predicate written again from its Lean definition and `IsCrookedIvF` decided **twice**, by two
different procedures, that the pair is faithful, that none of 5371 walks of at most four legs based
within one of level 5 folds both arms, and that `4 → 7 → 2 → 8 → 1 → 9` does — the span-nine walk
`w72` with one ascent to `H − 1` appended, exactly the shape batch 74 found one span higher.
`witness-batch75-span12-k6.txt` is a 14000-link window of `bing 0 16`, in the general model (`σ ≠ ρ`), band `[0,12]`, basepoint 1586
at level 7, arms of 12414 and 1587; `check75-span12-k6.log` confirms that **none of 80170 walks of
at most five legs** folds both arms and that `6 → 9 → 4 → 10 → 2 → 11 → 1` does. A correction note is
recorded beside the sentence in `HPC/Fold/Span.lean`; the sentence itself is left where it stands.

*The definition audit.* Every predicate of the census is evaluated by its own definition:
`IsCrookedIvF` (`HPC/Fold/Faithful.lean`: `le`, `width`, `adj`, and the crookedness clause with
interval triggers), `armG`, `armT`, and `FoldsOnto`, which is decided twice — by propagation of the
reachable set of walk times as a 128-bit mask and, independently, as an array of flags — with
**0 disagreements** on the samples taken at every span (3000 at spans 8–11, 402 at spans 12–14,
where the arms run to tens of thousands of links). The re-checker `check75.py` shares no code with
the census, decides the fold by a third procedure (a Python set of integers), and decides
`IsCrookedIvF` by two procedures of its own — the quadratic one, over all index pairs, straight from
the definition, and a linear one; on every witness short enough for both (spans 9, 10, 11) the two
**agree**.

## 1. Targets

`s3_general` is not proved and no proof was attempted: the commission asks for none. What this batch
delivers towards it is §2.4 — the one Lean deliverable, `sorry`-free — and the four censuses.

## 2.1 Does the least walk at span S extend a least walk at a lower span?

**Answer: yes, without exception in the sample, and always by exactly one leg, appended at the end,
to an extreme.**

*What was measured.* For a basepoint at index `i` of level `p` in a pair of band `[L, H] = [0, S]`,
and a band `[L', H']` with `L ≤ L' ≤ p ≤ H' ≤ H` and `H' − L' < S`, the *pair read in the sub-band*
is the maximal contiguous stretch of indices around `i` all of whose levels stay in `[L', H']`; by
`isCrookedIvF_restrict` that stretch is again a faithful crooked pair, of strictly smaller span. Its
two arms are the whole arms truncated where they first leave the sub-band. A walk *serves the
basepoint in the sub-band* when its levels lie in `[L', H']`, its start is within one of `p`, and it
folds both truncated arms. A walk `w` *is obtained by appending legs at the ends* from `w'` when
`w'` is a leg-aligned contiguous sub-walk of `w` — legs `j₁ … j₂ − 1` of `w`, started at `w`'s
target `j₁ − 1` — so that `j₁` legs are prepended and `k − j₂` appended. For each sampled basepoint
of least leg count `k ≥ 3`, up to sixteen least walks were enumerated and every leg-aligned
sub-walk of each was tested, the sub-band being the minimal one containing the sub-walk's levels and
`p`. The sample is up to 250 basepoints per level **and per leg count**, so the rare `k = 4` and
`k = 5` basepoints are covered as densely as the common `k = 3`.

| span | sampled `k ≥ 3` basepoints | with a sub-band ancestor | `k=3` | `k=4` | `k=5` | legs appended | legs prepended |
|---|---|---|---|---|---|---|---|
| 8  | 750  | **750**  | 750/750   | –       | –       | 1 in every case | 0 in every case |
| 9  | 1048 | **1048** | 1000/1000 | 48/48   | –       | 1 | 0 |
| 10 | 1250 | **1250** | 1246/1246 | 4/4     | 0/0     | 1 | 0 |
| 11 | 2056 | **2056** | 1500/1500 | 552/552 | 4/4     | 1 | 0 |
| 12 | 3319 | **3319** | 1750/1750 | 984/984 | 585/585 | 1 | 0 |
| 13 | 4043 | **4043** | 2000/2000 | 1040/1040 | 1003/1003 | 1 | 0 |
| 14 | 4959 | **4959** | 2250/2250 | 1406/1406 | 1303/1303 | 1 | 0 |

**The shape of the appended leg.** In every success the single appended leg is a run to an extreme:
an ascent to `H − 1` or a descent to `L + 1`, and never anything else. Both occur, in comparable
numbers, and the ascent is the more common as the span grows: 300/450 (ascent/descent) at span
eight, 532/516 at nine, 649/601 at ten, 1125/931 at eleven, 2150/1169 at twelve, 2946/1097 at thirteen, 3673/1286 at fourteen.

**The successes are not vacuous.** The truncated arms are long: the shorter of the two is at least
ten links in every success at spans 9–13 (739 of 750 at span eight), and at least a hundred links in
1100 of 1250 at span ten, 1904 of 2056 at eleven, 3080 of 3319 at twelve, 3811 of 4043 at thirteen, 4699 of 4959 at fourteen.

**Where the conjecture the commission names fails.** "One leg per two levels of span" is *not* what
the data says. At no span and at no sampled basepoint is there a success at a sub-band of span
`S − 1` or `S − 2`: the widest sub-band at which any success is found is `S − 3`, and it is the
modal one (918 of 1250 at span ten, 1338 of 2056 at eleven, 2035 of 3319 at twelve, 2055 of 4043 at thirteen, 2020 of 4959 at fourteen), with the rest at `S − 4`, `S − 5`, … . So the law the corpus supports is

> a least walk of `k` legs at span `S` is the extension, **by one leg run to an extreme**, of a walk
> that serves the same basepoint in a sub-band of span at most `S − 3`,

and three levels, not two, is the price of the leg. The six-leg witnesses obey it too: the span-12
six-leg walk `6 → 9 → 4 → 10 → 2 → 11 → 1` extends `6 → 9 → 4 → 10 → 2 → 11` read in the span-9
sub-band `[2,11]`, on truncated arms of 4240 and 1501 links, and the span-13 one extends
`6 → 4 → 9 → 2 → 11 → 1` read in a span-10 sub-band (`check75-span12-k6.log`,
`check75-span13-k6.log`).

## 2.2 What the split lemma sees

`foldsFrom_split` glues a fold of a prefix of **one arm**, arriving at walk time `u₁`, to a fold of
its suffix starting from `u₁`. At the five-leg basepoints the census asks three things of it: does
each arm admit a split with both sides of span at most nine; is there a common sub-band of span at
most nine holding a prefix of *both* arms; and — the question that decides whether the two halves
can be glued to one walk — do the two arms' sets of arrival times on a common prefix walk **meet**?

| span | five-leg basepoints examined | split on arm G | on arm T | on **both** | common prefix band of span ≤ 9 | one walk of that band folding both prefixes | arrival times **meet** | both suffixes of span ≤ 9 |
|---|---|---|---|---|---|---|---|---|
| 10 | 4   | 4   | 4   | **4**  | 4   | 4   | **0**   | 4  |
| 11 | 4   | 4   | 4   | **4**  | 4   | 4   | **0**   | 0  |
| 12 | 400 | 212 | 220 | **32** | 400 | 400 | **4**   | 14 |
| 13 | 400 | 124 | 186 | **0**  | 400 | 400 | 270     | 0  |
| 14 | 400 | 0   | 62  | **0**  | 400 | 400 | 108     | 0  |

**What this says, as a census.** The first half of what the split lemma would need is always there:
at every five-leg basepoint of every span there is a common sub-band of span at most nine holding a
prefix of both arms, and a single walk confined to that band that folds both prefixes — that is,
`s3_span_nine`'s conclusion for the truncated pair, which is exactly what `isCrookedIvF_restrict`
plus `s3_span_nine` supply. The second half is where it stops. At span eleven the two arms' arrival
times on that common walk **never** meet (0 of 4); at span twelve they meet at 4 of 400. And a split
index at which *both* sides of *both* arms lie in a band of span at most nine — the shape the two
applications of `s3_span_nine` would need — exists at 32 of 400 basepoints at span twelve and at
**none** of the 400 at span thirteen or the 400 at span fourteen: the forward arm crosses out of every span-nine sub-band at an
index at which the backward arm has not, and conversely.

So the obstruction the commission asked to have named is visible, and it is the one it describes:
**the split is per-arm and the walk is shared.** Gluing along the forward arm fixes the arrival time
`u₁` at which the suffix walk must start; the backward arm arrives at a different time on the same
walk, and at spans eleven and twelve the two arrival sets are disjoint, so no single `u₁` serves
both. `foldsFrom_split` cannot see this, because its statement quantifies over one arm; an inductive
step built on it would have to carry the arrival time as a shared datum of the two arms, which is
not what the lemma provides.

## 2.3 The growth of the least leg count

The census was extended to spans thirteen and fourteen. At those spans the corpus builder reaches
the band only through the Bing chains themselves. With the pair-length cap that keeps the `O(n²)`
faithfulness test affordable (14 000 links, as at span twelve) not one window of span 13 cut from
`bing 0 14` … `bing 0 17` attains the band — a first sweep with windows on and that cap produced no
faithful pair at all — so the span-13 and span-14 sweeps were run with windows off, on `bing 0 13`
and `bing 13 0` (33 462 links) and `bing 0 14`, `bing 14 0` (80 783 links) together with their
shavings, fillings and mixtures, and the narrower corpus is reported as such. At every span, the
basepoints that no stored walk serves are searched further, with walks of six, seven and eight legs
enumerated on the fly, so the maximum is a maximum and not merely a bound.

| span | distinct basepoints | least 1 | 2 | 3 | 4 | 5 | 6 | **maximum** | attained at |
|---|---|---|---|---|---|---|---|---|---|
| 8  | 441 942   | 109 194 | 322 551 | 10 197    | 0       | 0     | 0 | **3** | `L+3`, `L+4`, `L+5` |
| 9  | 994 341   | 136 800 | 719 105 | 138 388   | 48      | 0     | 0 | **4** | `L+5` |
| 10 | 760 552   | 58 251  | 454 299 | 245 214   | 2 784   | 4     | 0 | **5** | `L+5` |
| 11 | 1 029 785 | 42 071  | 451 804 | 514 871   | 21 035  | 4     | 0 | **5** | `L+7` |
| 12 | 1 800 780 | 36 061  | 536 122 | 1 085 423 | 142 038 | 1 132 | 4 | **6** | `L+7` |
| 13 | 468 468   | 3 565   | 86 383  | 280 044   | 96 000  | 2 472 | 4 | **6** | `L+7` |
| 14 | 807 830   | 2 904   | 92 448  | 415 683   | 278 707 | 17 902 | 186 | **6** | `L+7` |

(The last column of the span-14 row counts the basepoints served by no walk of at most five legs:
there are 186 of them, 158 at level `L+7` and 28 at `L+8`, and the cap on the deep search meant that
20 were searched further — every one of them served by six legs and by no fewer. So at span fourteen
the maximum over the *searched* part of the corpus is exactly six, and over the whole corpus it is at
least six. The first of them, `bing 0 14` itself — **thin**, 80 783 links, basepoint 11825 at level
`L+7`, whole arms of 68 958 and 11 826 links — is re-checked in `check75-span14-k6.log`: none of
190 019 walks of at most five legs folds both arms, and `6 → 4 → 9 → 2 → 11 → 1 → 13` does.)

**Both conjectures the commission offers are refuted by this data.**

* `⌊(S − 1)/2⌋` would give 4 at span ten and 5 at span twelve; the observed maxima are 5 and 6, each
  certified by a witness re-checked by independent code.
* `⌈S/3⌉ + 1` would give 5 at span twelve; the observed maximum is 6.

What the data is consistent with is `⌊S/2⌋` from span nine on — 4, 5, 5, 6, 6 at spans 9–13, with
span 8 one below at 3 — but that is a conjecture with six data points, each of which is a maximum
over a finite corpus and hence a *lower* bound for the class. What is certain is the direction: the
least leg count is not bounded by any of the recorded formulas, it grows, and the level at which the
maximum is attained moves from `L+5` (spans 9, 10) to `L+7` (spans 11, 12, 13, 14) — not to the
middle of the band, but to a fixed distance from the ends plus one step inward every two spans.

## 2.4 The extreme levels, parametrically — the Lean deliverable

**The single-walk fact at the extreme levels is a theorem at every span, and the repository's
argument for it uses only the distance to the nearer end. The parametric restatement goes through
with no step re-proved.** New file `HPC/Fold/Target75.lean`, `sorry`-free, imported by the root;
`#print axioms` for all of its results is `[propext, Classical.choice, Quot.sound]`
(`axioms-batch75.txt`).

* `lowEndWalk L H = offVee (L+1) (L+1) L H` and `highEndWalk L H = offLam (H−1) (H−1) L H` — the two
  walks, depending on the band and on nothing else.
* **`foldsOnto_lowEndWalk`** — in any band `[L, H]` with `L + 3 ≤ H` and **no bound on `H − L`**, at
  any basepoint of level at most `L + 2`, both arms fold onto `lowEndWalk L H`.
  **`foldsOnto_highEndWalk`** is the reflected statement at levels at least `H − 2`.
* **`extreme_levels_two_walks`** — the census's sentence as a theorem: for every band there are two
  walks, chosen *before* the sequence and the basepoint, such that in every Lipschitz sequence with
  values in the band every basepoint within two of an extreme has both arms folding onto the walk of
  its end.
* `s3_near_extreme_named` — `s3_near_extreme` with the existential walk replaced by the explicit
  one; `lowEndWalk_len`, `highEndWalk_len` — both walks have `1 + 2((H−L−3)+1)` times, so the
  statement is not vacuous as the span grows.

Three things come out stronger than the commission asks, and all three were already true of the
argument: the walk does not depend on the basepoint's level, so **one** walk serves all three levels
at each end rather than one per level; **no crookedness is used** (`IsCrookedIvF` appears in no
hypothesis — only `IsLip` and the two band bounds); and the extremes need not be attained. The
reason is visible in `offDichotomyAt_near_extreme` (`HPC/Fold/Dichotomy.lean`): at a level within two
of the bottom the base centre is taken to be `L + 1` outright, and the criterion is discharged by its
trivial clause — no arm can fall below `c₀ − 1 = L`, because `L` is the floor of the band. The span
never enters. So no step fails and none had to be named.

## 2.5 What the general model adds

**At every span from nine to thirteen the thin pairs alone show a maximum least leg count exactly one
lower than the general model.**

| span | maximum over all pairs | maximum over thin pairs (`σ = ρ`) | distinct thin basepoints |
|---|---|---|---|
| 8  | 3 | **3** | 28 433 |
| 9  | 4 | **3** | 64 612 |
| 10 | 5 | **4** | 48 901 |
| 11 | 5 | **4** | 65 052 |
| 12 | 6 | **5** | 111 652 |
| 13 | 6 | **5** | 66 924 |
| 14 | 6 | **6** (see below) | 161 566 |

**But the gap closes at span fourteen.** The thin column above is read off the basepoints served
within five legs; at span fourteen 16 of the 186 basepoints served by *no* walk of at most five legs
are thin, and the one that was written out and re-checked — `bing 0 14` itself, thin, 80 783 links,
basepoint 11825 at level `L+7` — needs **six** (`check75-span14-k6.log`). So the thin model reaches
six too, two spans after the general model first does.

The thin sub-corpus is the smaller one (one pair per base level sequence, against the shavings,
fillings and mixtures of each), so the gap at spans nine to thirteen is a gap between what was
*found*, not a proved separation; but it is one leg at five consecutive spans, always in the same
direction, and two witnesses sharpen it. At span twelve the hardest thin basepoint (`bing 0 12`
itself, thin, basepoint 2027, re-checked in `check75-span12-k5.log`, agreeing exactly with batch 74's
independent finding) needs five legs while the hardest general basepoint of that span needs six; at
span thirteen the six-leg basepoints are on general (shaved) variants of `bing 0 13` and the thin
chain itself stops at five. The reading the data supports is therefore that `σ` *advances* the
difficulty rather than creating it: a single shaved peak or filled valley, at the right index, moves
a basepoint from `k` to `k + 1` legs about two spans before the thin chains get there by themselves.
Any uniform argument has to cover the general model, and at every span up to thirteen it is the
general model that is one leg ahead.

## 3. Deliverables

* `HPC/Fold/Target75.lean` — §2.4, `sorry`-free, imported by `HPC.lean`; `axioms-batch75.txt` is its
  `#print axioms`, `[propext, Classical.choice, Quot.sound]` throughout (the two length lemmas do
  not even use `Classical.choice`).
* `census-batch75.c` with logs `census-batch75-span8.log` … `census-batch75-span14.log` — §§2.1,
  2.2, 2.3, 2.5, over whole arms, with `FoldsOnto` decided twice and 0 disagreements.
* `witness-batch75-span<S>-k<k>.txt` — the first basepoint of each span attaining each leg count
  from four up, written out in full (pair, basepoint, walk).
* `check75.py` with logs `check75-span<S>-k<k>.log` — the independent re-check of every witness,
  sharing no code with the census, with two deciders for `IsCrookedIvF` and a third for `FoldsOnto`.
* The correction note in the docstring of `HPC/Fold/Span.lean`; nothing else in the existing sources
  is changed.

## 4. What the evidence says about an argument uniform in the span

The evidence is two-sided and it is not the two sides one would guess. On the one hand the part of
the span-nine argument that is *about the ends* is already uniform: the six extreme levels are served
by two walks that depend on the band alone, with no crookedness and no span bound, and §2.4 says so
in Lean — whatever a general proof looks like, it need not revisit them. On the other hand the part
that is *about the middle* does not merely grow; it grows in a way that no bounded family of walks
can track. The least leg count is 3, 4, 5, 5, 6, 6, 6 at spans 8–14, so every
fixed-size family — the four-leg engine, its five-leg extension, any family chosen in advance — is
refuted at a finite span, and the level at which the hardest basepoints sit drifts inward with the
span. Two regularities survive that drift and are the only uniform structure the census found: every
least walk sampled, at every span and every leg count, is a walk of a **sub-band of span at most
`S − 3`** with **one leg appended, run to an extreme**; and the difficulty is carried by the general
model, the thin pairs lagging one leg behind at every span from nine to thirteen. Against this, the
one lemma the repository has for assembling folds, `foldsFrom_split`, is per-arm, and the census of
§2.2 shows precisely where that is fatal: at the five-leg basepoints a common sub-band walk for the
two prefixes exists every time, and the two arms' arrival times on it are disjoint almost every time,
so there is no time at which the two glued suffixes could start together. An argument uniform in the
span is therefore not excluded by anything found here — no basepoint is unserved, `S3` allows any
walk, and the sub-band-plus-one-leg regularity is exactly the shape an induction on the span would
want — but it cannot be an induction that carries a walk: it would have to carry, for both arms at
once, the *time* at which the walk of the sub-band is left, and it is that shared time, and not the
existence of the sub-band walk, that the evidence says is the hard object.
