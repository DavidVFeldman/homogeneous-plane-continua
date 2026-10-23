# Report on `COMMISSION-batch76.md` (copy `COMMISSION.md`) — batch 76: the extension law, and what gluing actually needs

The commission read is `COMMISSION-batch76.md`, on top of the batch-75 delivery. `lake build` is clean on the whole project; the repository's `sorry`s are still exactly
`s3_general` (`HPC/Fold/General.lean`) and `theorem3` (`HPC/Fold/Open.lean`) — this batch adds none
and closes neither, as commissioned.

## 0. Unserved basepoints, and failures of the extension law, first

**No basepoint is unserved, and the extension law fails nowhere it was tested.** The census of this
batch (`census-batch76.c`) rebuilds the batch-75 corpus exactly — same builder, same seeds, same caps;
the first basepoint of each span attaining each leg count is byte-for-byte the batch-75 witness file —
so its §2.3-of-batch-75 table (least leg counts) is batch 75's, and no basepoint at any span is
served by no walk. At every sampled basepoint of least leg count `k ≥ 3` it decides
`ExtendsSubBand ρ i L H k` **exactly**, and the predicate holds at every one:

| span `S` | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|
| sampled basepoints, `k ≥ 3` | 750 | 1048 | 1584 | 2056 | 3319 | 4043 | 4959 |
| of which `k = 3 / 4 / 5` | 750/0/0 | 1000/48/0 | 1250/330/4 | 1500/552/4 | 1750/984/585 | 2000/1040/1003 | 2250/1406/1303 |
| `ExtendsSubBand` holds | 750 | 1048 | 1584 | 2056 | 3319 | 4043 | 4959 |
| fails | **0** | **0** | **0** | **0** | **0** | **0** | **0** |

*Definition audit.* The census decides the predicate as `HPC/Fold/Target76.lean` states it, through
a reduction whose every step is a fact about the definitions (header of `census-batch76.c`): a target
list can be normalised (repeats dropped, monotone runs merged, padded back to length `k − 1` by
repeating its last level) without changing the walk; a fold of an arm restricts to a fold of each
prefix, and an arm truncated at a narrower band is a prefix of the arm truncated at a wider one, so
for a given `w'` the minimal band containing `w'`'s levels and `ρ i` is the only one that needs
testing. The decision is therefore: enumerate every alternating walk `w` of at most `k` legs (targets
in `[L, H]`, based within one of `ρ i`) ending at `L + 1` or `H − 1` and folding both whole arms, split
off its last leg (or shorten it) to get `w'`, and accept when `w'` has at most `k − 1` legs, its minimal
band has span at most `S − 3`, and it folds both truncated arms. `FoldsOnto` is decided by a 128-bit
mask propagation and, on every suffix test of every canonical witness and a sample of the other calls
(about 200 000 calls per span), by an array propagation as well: 0 disagreements at every span. The
separate audit sample of batch 75 (stored walks, whole arms) is repeated: 0 disagreements.

*The one corpus statement corrected.* The commission's figure of 17 425 sampled basepoints is taken
from the batch-75 summary, which lists 1250 at span ten; the batch-75 log
(`census-batch75-span10.log`, §2.1) says 1584 — 1250 is its `k = 3` count. The corrected total over
spans 8–14 is 17 759. The regularity itself is unaffected: batch 75 found it at all 1584.

*Leg count six.* Basepoints whose least leg count is six (four at span twelve, four at span thirteen,
and at span fourteen those found by the capped deep search) lie outside the census's sample, which is
drawn from basepoints scored by the exhaustive five-leg search. At the stored six-leg witnesses the
predicate was put to the independent search `ext76.py` (§2.3 below).

## 1. Targets

`s3_general` is not proved and no proof was attempted: the commission asks for none. This batch
states the extension law as a decidable Lean predicate, checks it at the stored witnesses by the
kernel, records the conjecture as a comment, and measures what an induction through it would carry.

## 2.1 Is "arrival times meet" what a two-arm gluing needs?

**No. It is a hypothesis of no statement in the repository, and it is strictly stronger than what
gluing needs.** `FoldsOnto f len c` asks for one itinerary `β` for the one arm `f`; `S3` (the statement
`s3_general` would prove) and the fold statements built on it ask for `FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i)
len c`, two independent existentials sharing only `(len, c)`. `foldsFrom_split` (`Span.lean`) is
stated for one arm, with that arm's own split index `s` and arrival time `u₁`. Its only uses in the
repository are `s3_at_window` (`Cut.lean`), which applies it once to each arm with each arm's own
split index, and — as a statement shape — `Tracking` (`Cut.lean`), whose two middle-piece folds end at
two separately quantified times `uG` and `uT`, with no hypothesis relating them. (In `s3_at_window`
both arrival times happen to be `0`, because the window lies within one of `c 0`; that is a property
of the window, not a requirement of the gluing.)

To make this exact, `HPC/Fold/Target76.lean` now states it:
**`foldsOnto_arms_of_split`** — given, for the forward arm, a prefix fold ending at time `uG` at index
`sG` and a suffix fold from `uG`, and, for the backward arm, the same with `sT`, `uT`, both whole arms
fold onto the walk. Nothing relates `uG` to `uT` or `sG` to `sT`. `#print axioms`:
`[propext, Classical.choice, Quot.sound]`.

So the column "arrival times meet" of batch 75 §2.2 measured a condition no gluing uses, and the
sentence of batch 75 §2.2 and §4 — "no single `u₁` serves both" — names an obstruction that is not
one: each arm has its own `u₁`. What a gluing through the extension law does need, per arm, is
measured in §2.2.

## 2.2 The suffixes

At every sampled basepoint satisfying the extension law, for every witness `(w', w)` (every `w'` of at
most `k − 1` legs with its minimal band of span at most `S − 3`, every appended level), and for each
arm separately: truncate the arm at its first exit from the sub-band, fold the truncated arm onto
`w'`, and take the *set* `A` of arrival times at the truncation index (the last index inside the
band) over **all** folds `β` of the truncated arm; then ask whether the suffix of the arm from that
index satisfies `FoldsFrom suffix len c u₁` on `w` for some `u₁ ∈ A` (and separately for the latest
and the earliest element of `A`). The *canonical* witness is the one with the widest sub-band, then
the longest truncated arms, preferring `w` with all targets in `[L + 1, H − 1]`.

| span `S` | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|
| basepoints | 750 | 1048 | 1584 | 2056 | 3319 | 4043 | 4959 |
| canonical witness: both suffixes fold from the **latest** arrival time | 720 | 1048 | 1540 | 1940 | 3082 | 3868 | 4739 |
| … from the **earliest** | 484 | 653 | 1002 | 1329 | 2105 | 2596 | 3114 |
| … from **some** arrival time of its own arm | 720 | 1048 | 1540 | 1940 | 3082 | 3868 | 4739 |
| **some** witness at which both suffixes fold from some own arrival time | 750 | 1048 | 1576 | 1987 | 3119 | 3902 | 4751 |
| **no** witness and no arrival time serves | **0** | **0** | **8** | **69** | **200** | **141** | **208** |
| witnesses tried / of which both suffixes fold | 4337 / 4255 | 7118 / 6464 | 11839 / 10526 | 16086 / 14200 | 34971 / 31477 | 51949 / 47085 | 70374 / 63643 |

Per arm, at the canonical witness (not truncated / latest serves / earliest serves / some serves):

| span | arm G | arm T |
|---|---|---|
| 8 | 0 / 743 / 650 / 743 | 16 / 727 / 570 / 727 |
| 9 | 0 / 1048 / 926 / 1048 | 0 / 1048 / 768 / 1048 |
| 10 | 0 / 1568 / 1349 / 1568 | 0 / 1556 / 1224 / 1556 |
| 11 | 3 / 2032 / 1796 / 2032 | 0 / 1964 / 1589 / 1964 |
| 12 | 0 / 3192 / 2808 / 3192 | 0 / 3209 / 2586 / 3209 |
| 13 | 0 / 3938 / 3671 / 3938 | 0 / 3973 / 2946 / 3973 |
| 14 | 0 / 4852 / 4482 / 4852 | 0 / 4846 / 3589 / 4846 |

**What this says.** (i) Whenever some arrival time of the truncated fold serves the suffix, the
*latest* one does — at every span, on both arms, the "latest" and "some" columns are equal; a different
`β` of the truncated arm never repairs what the latest-arriving `β` cannot, so where the canonical
witness fails, no other fold of the truncated arm onto the same `w'` repairs it. (ii) Where the canonical
witness fails, another witness `(w', w)` repairs it at most basepoints (36 of the 44 canonical failures at
span ten, 47 of 116 at span eleven). (iii) Where none does, the basepoint is written out
(`witness-batch76-q2-span<S>-<j>.txt`, the first six at each span from ten up, with `w'`, its band
and `e`).

**The unrepaired basepoints, re-checked.** `ext76.py q2all` (sharing no code with the census;
`FoldsOnto` decided by propagation of Python sets of walk times; `walkList` written from its Lean
definition) re-checks eleven of them — the six of span ten, two of span eleven, one each of twelve,
thirteen and fourteen — over the **literal** definition: every sub-band `[L', H']`, minimal or not, every start,
every target list, every appended level, and every arrival time. Its own least-leg search agrees with
the census's `k` at all eleven; the number of `ExtendsSubBand` witnesses is 2 to 12; at **none** of them
do both suffixes fold (`check76-q2.log`). `ext76.py q2` then shows what happens instead, and it is the
same at all eleven: the whole arm does fold onto `w`, but its fold **leaves `w'` before the arm leaves
the sub-band** — folding the truncated arm onto the whole walk `w` rather than onto `w'`, its arrival
set gains times on the appended leg, and it is exactly from those that the suffix folds. For
`witness-batch76-q2-span10-1.txt` (the thin `bing` chain of span ten, 2379 links, basepoint 465, level 5,
`w' = 5 → 2 → 9`, band `[2, 9]`, `e = 1`): arm T is truncated at 226 of 466 links; its arrival times
on `w'` are `{2, 3, 4}` and the suffix folds from none; folded onto `w` instead, the prefix arrives at
`{2, 3, 4, 16, 17, 18}` — times `16–18` are on the appended descent to `1` — and the suffix folds from
`{16, 17, 18}`. At the span-eleven to fourteen examples (`w' = 4 → 7 → 1`, band `[1, 7]`) it is arm G,
arriving at `{2, 3, 4}` on `w'` and at `{14, 15, 16}` on `w`.

So the datum an induction through the extension law would carry is *not* always available at the
first exit from the sub-band: at 0.5–6 % of the sampled basepoints from span ten up, every way of
cutting at the first exit fails, because the arm's fold onto the whole walk uses the appended leg while
the arm is still inside the sub-band. The split index an induction would need is then later than the
first exit, and the prefix fold must be onto `w`, not onto `w'`.

## 2.3 The extension law in Lean

`HPC/Fold/Target76.lean`, `sorry`-free, imported by the root:

* `bandPrefixLen`, `truncArm` — an arm truncated at its first exit from a band, with the three facts
  that make it mean that (`bandPrefixLen_le`, `mem_band_of_lt_bandPrefixLen`,
  `not_mem_band_bandPrefixLen`) and `truncArm_apply`.
* **`ExtendsSubBand ρ i L H k`** — there are `L ≤ L' ≤ ρ i ≤ H' ≤ H` with `H' − L' ≤ H − L − 3`, a start
  `s` and `k − 1` targets in `[L', H']` (so every level of `w'` is in `[L', H']`: `walkList_mem_Icc`),
  `w' = walkList s ts` folding both arms truncated at `[L', H']`, and `e ∈ {L + 1, H − 1}` different
  from the last level of `w'`, such that `w = walkList s (ts ++ [e])` folds both whole arms.
* `extendsSubBandB` and **`extendsSubBandB_iff`** — the finite search over every sub-band, start,
  target list and appended level, proved equal to the definition; hence the `Decidable` instance.
* `extendsSubBand_of_witness` — the form in which the kernel checks are made.
* `foldsOnto_arms_of_split` — §2.1.

**Kernel checks** (`decide +kernel`, every clause, the folds through `foldsB`, which `foldsB_iff`
proves equal to `FoldsOnto`):

| witness | links | basepoint | band | least legs | where | checked |
|---|---|---|---|---|---|---|
| `witness-batch72-min.txt` | 78 | 1 | `[3, 9]` | 1 | `Audit76.P78` | witness; the whole search |
| `witness-batch71-min.txt` | 290 | 104 | `[2, 9]` | 3 | `Audit76.P290` | witness; the whole search; **fails at `k = 2`** by the whole search |
| `witness-batch75-span9-k4.txt` | 2378 | 343 | `[0, 9]` | 4 | `Audit76.P2378` | witness |
| `witness-batch75-span10-k4.txt` | 2379 | 343 | `[0, 10]` | 4 | `Audit76.P2379` | witness |
| `witness-batch75-span10-k5.txt` | 3000 | 1256 | `[0, 10]` | 5 | `Audit76.P3000` | witness |
| `witness-batch74-span11.txt` | 5815 | 946 | `[0, 11]` | 5 | `Audit76Long.P5815B946` | witness |
| `witness-batch75-span11-k4.txt` | 5742 | 343 | `[0, 11]` | 4 | `Audit76Long.P5742aB343` | witness |
| `witness-batch75-span11-k5.txt` | 5742 | 5099 | `[0, 11]` | 5 | `Audit76Long.P5742bB5099` | witness |
| `witness-batch74-span12.txt` = `witness-batch75-span12-k5.txt` | 13861 | 2027 | `[0, 12]` | 5 | `Audit76Long.P13861B2027` | witness |
| `witness-batch75-span12-k4.txt` | 13861 | 343 | `[0, 12]` | 4 | `Audit76Long.P13861B343` | witness |
| `witness-batch75-span12-k6.txt` | 14000 | 1586 | `[0, 12]` | **6** | `Audit76Long.P14000B1586` | witness |
| `witness-batch75-span13-k4/k5/k6.txt`, `witness-batch75-span14-k4/k5/k6.txt` | 33462, 80783 | — | `[0, 13]`, `[0, 14]` | 4–6 | — | **not kernel-checked**: the kernel's evaluation of the folds on arms of 30 000–80 000 links exhausted the 64 GB of memory available (the 14 000-link check already peaked near 44 GB); `ext76.py` only |

The first five are in `HPC/Fold/Audit76.lean` (part of the default build). The longer ones are in the
library `Audit76Long` (`Audit76Long/*.lean`, generated by `gen-audit76.py` from `ext76.py`'s
witnesses; nothing generated is trusted, every clause is re-checked by the kernel): their arms outrun
the kernel's default thread stack, so the library is built with `--tstack=4000000` (set in
`lakefile.toml`) and is not a default target — `lake build Audit76Long`. For the pairs of `Audit71`
and `Audit72` the sequence is also proved equal to theirs, so their kernel-proved faithfulness is
carried over (`P78.faithful`, `P290.faithful`); for the others faithfulness is the census's and
`check75.py`'s. The least leg count is not a Lean statement; `ExtendsSubBand` does not mention it, and
at the 290-link pair the kernel's evaluation of the whole search to *false* at `k = 2` shows the
statement is not vacuous one leg below the least count. `#print axioms` for every theorem:
`[propext, Classical.choice, Quot.sound]` (`axioms-batch76.txt`).

**The independent search at every stored witness.** `ext76.py least` (no code shared with the census;
the least leg count by its own search over walks with targets in `[L + 1, H − 1]`; the extension law
by a literal search over every sub-band) finds a witness of `ExtendsSubBand` at the least leg count at
every stored witness (`check76-least.log`): all eighteen (seventeen distinct basepoints: `witness-batch74-span12.txt` and `witness-batch75-span12-k5.txt` are the same basepoint), including the three six-leg witnesses of spans 12, 13 and 14; its least leg count agrees with the file's at every one (for the 80 783-link six-leg witness the count is taken from `check75.py` rather than re-searched, `extk` mode). Where its witness differs from the one in the Lean module (the search order was changed between the two runs, widest bands first), both are witnesses — the definition asks for one.

**The conjecture**, recorded as a comment in `HPC/Fold/Target76.lean`, not proved:

```
∀ S ≥ 8, every basepoint of a faithful pair of span S with least leg count k ≥ 3
satisfies ExtendsSubBand ρ i L H k.
```

with the census cited — `ExtendsSubBand` holds at all 17 759 sampled basepoints of spans 8–14 and fails at none (table of §0) — and with the caveat that `LeastLegs` is the census's
notion (a walk with `k` turning targets in `[L + 1, H − 1]`, directions alternating, based within one
of `ρ i`, folds both whole arms, and none with fewer does) and is not defined in Lean.

## 2.4 Which extreme?

The census's table, at the canonical witness (counts: appended down to `L + 1` / up to `H − 1`):

| span | down / up | basepoints admitting both directions | (a) first exit from the sub-band, down-appended: D / U | up-appended: D / U | (b) `ρ i` below / at / above the sub-band's middle, down | up | (c) last level of `w'`: down-appended at the band's top | up-appended at its bottom |
|---|---|---|---|---|---|---|---|---|
| 8 | 450 / 300 | 200 | 200 / 250 | 246 / 54 | 200 / 0 / 250 | 250 / 0 / 50 | 450 of 450 | 300 of 300 |
| 9 | 516 / 532 | 256 | 162 / 354 | 360 / 172 | 0 / 266 / 250 | 250 / 250 / 32 | 516 of 516 | 532 of 532 |
| 10 | 748 / 836 | 288 | 289 / 459 | 492 / 344 | 266 / 56 / 426 | 390 / 82 / 364 | 748 of 748 | 836 of 836 |
| 11 | 931 / 1125 | 216 | 435 / 496 | 716 / 409 | 249 / 219 / 463 | 432 / 202 / 491 | 931 of 931 | 1125 of 1125 |
| 12 | 1169 / 2150 | 213 | 451 / 718 | 1209 / 941 | 157 / 38 / 974 | 792 / 133 / 1225 | 1169 of 1169 | 2150 of 2150 |
| 13 | 1097 / 2946 | 109 | 416 / 681 | 1928 / 1018 | 0 / 247 / 850 | 917 / 455 / 1574 | 1097 of 1097 | 2946 of 2946 |
| 14 | 1286 / 3673 | 48 | 533 / 753 | 2477 / 1196 | 70 / 16 / 1200 | 1132 / 240 / 2301 | 1286 of 1286 | 3673 of 3673 |

* **(a) The side on which the arms first leave the sub-band does not decide it**: both sides occur in
  both directions at every span.
* **(b) The basepoint's level against the sub-band's middle does not decide it** either.
* **(c) The last target of `w'` decides it, at every span, without exception**: the appended leg runs
  down exactly when `w'` ends at the top of its sub-band, and up exactly when it ends at the bottom;
  `w'`'s last leg is always an ascent before a down-append and a descent before an up-append; and `w'`
  comes within one of exactly one extreme — of `H` before a down-append, of `L` before an up-append.
  So the appended leg always reverses `w'`'s last leg (no canonical witness continues it) and crosses
  the whole band, from within one of one extreme to within one of the other. Part of this is forced by
  the definition — once `w'` ends at `H − 1`, the clause `e ≠ last` leaves only `e = L + 1` — and what
  the census adds is that `w'` *always* ends within one of an extreme.
* A fourth reading, not asked for, agrees with the direction almost always: take the **widest** band
  containing `w'`'s levels and `ρ i` at which `w'` still folds both truncated arms (the band of the
  *arms*, not of the walk). At every canonical witness of spans 10, 12, 13 and 14 it contains the extreme
  `w'` reaches (`b = H` before a down-append, `a = L` before an up-append) and the arms first leave it
  on the side of the appended leg. The exceptions — 117, 7 and 3 at spans 8, 9 and 11 — are all
  down-appends whose widest band touches `L` instead of `H`, and there the arms leave it upward. For
  the canonical `w'` this band has span `S − 1` at 100 % (span 8) down to 41 % (span 14) of the
  basepoints; for *some* least witness a band of span exactly `S − 1` always serves (§2.5 (B)).

The choice of direction at a basepoint is not unique: 48 to 288 basepoints per span admit witnesses
in both directions, and the table is of the canonical witness.

## 2.5 Why `S − 3`?

Both readings, measured at every sampled basepoint of every span, 8–14:

**(A) The arms: is there a walk of a sub-band of span `S − 1` or `S − 2` folding the truncated arms
at all?** Yes, at **every** sampled basepoint of every span, for both `S − 1` and `S − 2`, within
`k + 1` legs; at span fourteen the least such walk has 1–5 legs in a band of span `S − 1` and 1–4 in a
band of span `S − 2`. So the second reading — "no walk of a sub-band of span `S − 1` or `S − 2` folds
the truncated arms" — is **refuted at every basepoint**.

**(B) The least walks: is the least walk `w` (k legs) a one-leg extension of a `w'` that folds the
arms truncated at a band of span exactly `S − 1` (resp. `S − 2`) containing its levels?** Yes, at
**every** sampled basepoint, for both. So the extension law holds with the truncation taken at a band
of span `S − 1` — the arms tolerate it. What is never `S − 1` is the span of the **minimal** band of
`w'`'s *levels*:

| span | widest minimal band of `w'`, over least extensions: `S − 3` / `S − 2` / `S − 1` | the same with every target of `w` in `[L + 1, H − 1]` (the batch-75 family) | over extensions of `k + 1` legs (not least): `S − 1` |
|---|---|---|---|
| 8 | 32 / 718 / 0 | 750 / 0 / 0 | 750 |
| 9 | 39 / 1009 / 0 | 1048 / 0 / 0 | 1048 |
| 10 | 174 / 1410 / 0 | 1584 / 0 / 0 | 1584 |
| 11 | 365 / 1691 / 0 | 2056 / 0 / 0 | 2056 |
| 12 | 577 / 2742 / 0 | 3319 / 0 / 0 | 3319 |
| 13 | 579 / 3464 / 0 | 4043 / 0 / 0 | 4043 |
| 14 | 709 / 4250 / 0 | 4959 / 0 / 0 | 4959 |

So `S − 3` is **a fact about least walks, and about the family they were drawn from, not about the
arms**: batch 75 searched `w` with targets in `[L + 1, H − 1]`, and there the minimal band of `w'` is
never wider than `S − 3` (span `S − 2` would need `w'` to reach both `L + 1` and `H − 1`, which no least
extension in the family does at any sampled basepoint); allowing a target at `L` or `H` gives `S − 2` at most basepoints;
`S − 1` appears as soon as one more leg than the least is allowed, at every basepoint. "Least" hides
it, as the first reading says — and the family hides `S − 2`.

## 2.6 The `⌊S/2⌋` conjecture

Recorded as a comment in the docstring of `HPC/Fold/Span.lean`, beside the two corrections, with
the six data points (maxima 4, 5, 5, 6, 6, 6 at spans 9–14 against `⌊S/2⌋` = 4, 5, 5, 6, 6, 7): as an
upper bound it holds at all six (and at span eight, 3 against 4), it is attained at spans nine to
thirteen and not at fourteen, and each point is a maximum over a finite corpus, hence a lower bound for
the true maximum at that span. This batch's span-fourteen census, on the same corpus, reproduces the maximum six (186 basepoints not served by five legs; the 20 searched further are served by six).

## 3. Deliverables

* `HPC/Fold/Target76.lean` — §2.3's definition, its decision procedure and `foldsOnto_arms_of_split`,
  `sorry`-free, imported by `HPC.lean`, with the conjecture as a comment.
* `HPC/Fold/Audit76.lean` (default build) and `Audit76Long/*.lean` (library `Audit76Long`, built with a
  larger thread stack: `lake build Audit76Long`) — the kernel checks; `axioms-batch76.txt`.
* `census-batch76.c` with logs `census-batch76-span8.log` … `census-batch76-span14.log` — §§2.2, 2.3
  (exact decision), 2.4, 2.5 over whole arms, two `FoldsOnto` deciders, 0 disagreements.
* `witness-batch76-q2-span<S>-<j>.txt` — the basepoints of §2.2 at which no witness serves, written
  out (pair, basepoint, `w'`, band, `e`).
* `ext76.py` with `check76-q2.log` and `check76-least.log` — the independent re-checks.
* The `⌊S/2⌋` comment in `HPC/Fold/Span.lean`, the two new imports in `HPC.lean` and the
  `Audit76Long` library entry in `lakefile.toml`; nothing else in the existing sources is changed.

## 4. What the evidence says

The extension law holds at every basepoint it was tested on — every sampled basepoint of least leg
count three to five at spans eight to fourteen, decided exactly, and every stored witness, eleven of
them by the kernel — and it holds in a stronger form than stated: the sub-band can be taken of span
`S − 1` for the arms, the `S − 3` being the span of the walk's own levels in the family batch 75
searched, not a constraint the arms impose. The appended leg's direction is fixed by where `w'` ends,
which is always within one of an extreme. The measurement batch 75 took to be the obstruction —
common arrival times of the two arms — is not a condition any gluing uses: the two arms are glued
independently, each at its own index and time, and the repository's statements already have that
shape. What the evidence does show is a different and narrower obstruction to the most direct
induction through the extension law: cutting each arm at its first exit from the sub-band and gluing
the suffix to the truncated fold succeeds at most basepoints, and whenever any arrival time works the
latest does; but at a small fraction from span ten up (8, 69, 200, 141, 208
basepoints at spans 10–14, 0.5–6 % of the sample) it fails for every witness, because the whole arm's fold enters the
appended leg while the arm is still inside the sub-band. At those basepoints an induction would have
to cut later than the first exit and fold the prefix onto the extended walk rather than the sub-band
walk.
