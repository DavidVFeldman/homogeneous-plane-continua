# Report: batch 43 — Bing's timing law on arms, and the mixed configuration

Runs on top of the batch-42 delivery. Everything earlier is untouched; `HPC/Fold/Timing.lean` is
the commissioned file, `HPC/Fold/MixedWitness.lean` is new, and root `HPC.lean` imports both.
`lake build HPC` succeeds; the only `sorry`s in the project are `theorem3` (`HPC/Fold/Open.lean`)
and the two long-standing targets of `HPC/Fold/General.lean`.

## 0. First: the answer to §2.1 is yes, and it corrects the batch-42 record

**The mixed configuration is inhabited, by actual pairs, inside Bing's own chain.**

`bing 0 9` is a faithful crooked sequence of 986 links with values `0 … 9`, so of span exactly
nine with both ends attained. It has 182 basepoints at level `L + 4` whose two arms are both
`HighAt (L+1) (L+8)` — that is, 182 basepoints of the branch that `s3_span_nine_except` leaves
open. Of those,

| | |
|---|---|
| both arms satisfy the Λ-criterion (the Λ-walk based at `L+3` serves the pair) | 30 |
| both arms satisfy the V-criterion (the V-walk based at `L+5` serves the pair) | 97 |
| **one arm each — neither walk serves the pair** | **55** |
| neither criterion on some arm | 0 |

The criteria used are the exact ones of `HPC/Fold/Profile.lean`, not announcements:
`foldsOnto_lam_iff_profile` and `foldsOnto_vee_iff_profile` make them iff, and the index clause on
the Λ side is now supplied by the timing law proved in this batch (§1), so the Λ-criterion reads
simply *before the arm ever drops to `L + 1` it stands at `L + 7`*.

This contradicts the statement in `REPORT-batch42.md` that the mixed class is empty over the
corpus of Bing windows. The cause is a limit in `census-batch42k.c`: it held each arm in a buffer
of 512 entries and skipped every basepoint with a longer arm (`if (mg > 512 || mt > 512)
continue;`). At length 986 that leaves ten of the 182 branch basepoints, and all ten happen to be
of the `lam, lam` kind. `census-batch43.c` holds 4200 and skips nothing; its crookedness test is
run on paths whose status is known before it is used (`bing 0 N` for `N ≤ 9` pass, a monotone run
and a single fold fail).

**The witness is in Lean, sorry-free** (`HPC/Fold/MixedWitness.lean`). The sequence used there is
not `bing 0 9` — whose faithfulness is not yet proved in the repository at that length — but the
409-link chain `ceSeq = bing 0 8`, whose faithfulness *is* proved (`ceSeq_faithful`,
`HPC/Fold/DichotomyFaithful.lean`), read in the band `[0, 9]`. Its basepoint `138` stands at level
`0 + 4`, both its arms are `HighAt (L+1) (L+8)`, and

* `not_foldsOnto_lam_armT_mix` — the backward arm (139 links) does not fold onto the Λ-walk
  `lamCenter 3 9 0`: it drops to `L + 1` at its step 39 and never stands at `L + 7` at all
  (`mixT_le_six`);
* `not_foldsOnto_vee_armG_mix` — the forward arm (271 links) does not fold onto the V-walk
  `veeCenter 5 9 0`: it rises to `L + 7` at its step 31, and from its step 4 to its step 31 it
  never drops to `L + 2` (`mixG_no_valley_before`);
* `mix_no_common_walk_of_the_two` collects this: an actual faithful crooked pair meeting every
  hypothesis of the open branch at which neither of the two walks folds both arms;
* `mix_served_by_four_leg` — and the third walk does serve it. The four-leg walk
  `L+3 → L+6 → L+1 → L+8`, sixteen centers, is exhibited with the two time-assignments written
  out (`betaGlist`, `betaTlist`, found by the census and checked in the kernel), and both arms
  fold onto it.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for all of them. (The band there
is `[0, 9]` while the chain has span eight, so that particular basepoint is in fact served, by
`s3_span_eight`. What the witness settles is the *method*: the branch hypotheses do not imply
either criterion, so no argument that offers only those two walks can close the branch. The
span-nine instances of §0, inside `bing 0 9`, are not served by anything the repository proves.)

## 1. §2.2, and the commissioned targets

**Does the Λ-walk serve every actual pair of the branch at `L + 4`? No.** Of the 182 branch
basepoints of `bing 0 9`, 30 are served by the Λ-walk; 55 have an arm on which it fails, and for
those the V-walk fails on the other arm. Equivalently, by `s3_span_nine_mid_low_of_lam`, it is not
true that each arm of such a basepoint stands at `L + 7` before it drops to `L + 1`: the backward
arm at basepoint 138 never stands at `L + 7`.

The three commissioned targets of `HPC/Fold/Timing.lean` are proved.

* `armG_gap`, `armT_gap` — **the timing law on an arm.** If an arm of a faithful crooked sequence
  stands at two levels exactly `d` apart at its steps `s < t`, then `z d ≤ t - s + 1`. The window
  between the two steps is itself a faithful crooked sequence (`isCrookedIvF_restrict`) and
  `minGap`, the engine of Bing's Theorem 7, counts its links. So three levels take at least five
  steps, four take twelve, five take twenty-nine — against four, seven and twelve from the one-arm
  clause `CrookUp`.
* `z_mono` — Bing's recurrence is monotone. `minGap` needs the two levels exactly `d` apart; with
  `z_mono` a gap of *at least* `d` gives the same bound. This is what the commission noted was
  missing.
* `armG_three_levels`, `armT_three_levels` — an arm three levels above its basepoint is at step
  five or later, since `z 3 = 6`.
* `s3_span_nine_mid_low_of_lam` — the Λ-criterion at the branch `L + 4` with no index clause: a
  basepoint is served as soon as each arm stands at `L + 7` before it ever drops to `L + 1`. The
  clause `5 ≤ j` of `s3_span_nine_mid_low_of_lamProfile` follows from the level `L + 7` alone.

## 2. §2.3 — what does serve the mixed pairs

The census asked the same corpus what walks serve the pairs it met. Two facts, both from
`census-batch43.log`:

* **One walk serves every mixed pair met.** Of 20 000 branch pairs tested against the four-leg
  walk `L+3, L+6, L+1, L+8` (read through the reflection `x ↦ 2L + 9 - x` at the branch `L + 5`),
  6 738 are not served — but of the 5 280 *mixed* ones among them, **none** fails. All 55 mixed
  basepoints of `bing 0 9` are served by it, with three turns, and no fewer.
* **Intersecting the walks of up to three turns over 3 000 mixed pairs leaves exactly two:**
  `L+3, L+6, L+1, L+8` and `L+3, L+7, L+1, L+8`. Over the branch pairs of all kinds the
  intersection is empty after a few hundred pairs, as it must be — the `lam, lam` pairs and the
  `vee, vee` pairs need their own walks.

So the shape of what is missing is now explicit. Span nine at the branch `L + 4` needs three
walks, not two, and the third is a four-leg walk `L+3 → L+6 → L+1 → L+8` —
`mix_served_by_four_leg` exhibits it working at the witness, in Lean. The repository already
has a four-leg engine (`HPC/Fold/Leg4.lean`, batch 40, six progress clauses and a three-time
clause); what it does not yet have is an exact criterion for this walk in the style of
`HPC/Fold/Profile.lean`, which is what the batch-42 route would need.

## 3. The census

`census-batch43.c`, log `census-batch43.log`. Everything it counts ranges over **actual faithful
crooked sequences**: each is verified link by link and pair by pair against `IsCrookedIvF` in its
thin form (`sigma = rho`, so the adjacency clause is 1-Lipschitz and the crookedness clause is
decidable as written). No one-arm clause and no announcement is used; arms are classified by the
two exact profile criteria. The corpus:

* **A** — windows of `bing 0 N`, `N = 9, 10` (window starts on a stride of about a two-hundredth
  of the length of the source path, every end used), and `bing 0 9` again as a single window with
  every one of its 986 basepoints;
* **B** — windows of `bing a b` for `0 ≤ a, b ≤ 12` with `|a - b| ≥ 9`, of length at most 4000;
* **C** — 40 random concatenations `bing t0 t1 ++ bing t1 t2 ++ …` with turning levels in
  `[0, 9]`, of which 20 are crooked and were used.

Totals over the three families: 9 128 windows of span exactly nine, 4 197 408 basepoints at each
of `L + 4` and `L + 5`, of which 6 292 719 lie in the open branch, and **1 625 599 of those are
mixed**. Of the 3 290 pairs put through the full set of walks of up to three turns, none was
unserved.

## 4. What is open

Unchanged: `theorem3` (`HPC/Fold/Open.lean`), and `s3_span_nine`, `s3_general`
(`HPC/Fold/General.lean`). What batch 43 changes is the shape of the span-nine gap: it is not a
configuration to be excluded — `HPC/Fold/CrossArm.lean` excluded the vacuous part of it, and the
rest is inhabited — but a third walk to be added, with its own exact criterion, and a rule that
picks between the three. `s3_span_nine_of_mid` already states span nine in the form the three
walks would discharge.
