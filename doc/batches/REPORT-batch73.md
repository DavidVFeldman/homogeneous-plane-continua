# Report, batch 73

The commission read is `COMMISSION-batch73.md` (copy `COMMISSION.md`).

## 0. No counterexample this time

The commission asks for any counterexample first. There is none: the reading proposed in §2.1 is
**correct as stated**, and it is now a theorem. Nothing in the repository was refuted in this
batch, nothing was weakened, and no statement was commented out as false. Two statements were
moved, and only because of Lean's import order; that is §1 below.

## 1. Targets

| target | status |
| --- | --- |
| `s3_span_nine_mid5` | **proved** — `HPC/Fold/Target73.lean` |
| `s3_span_nine'` | **proved** — `HPC/Fold/Target73.lean` |
| `s3_span_nine` | **proved** — `HPC/Fold/Target73.lean` |
| `s3_general` | open (`HPC/Fold/General.lean`) — spans ten and above are not in this batch |
| `theorem3` | open (`HPC/Fold/Open.lean`) — it is closed by `theorem3_of_S3` once `s3_general` is |

`lake build` is clean on the whole project. The only two `sorry`s left in the repository are
`s3_general` and `theorem3`; the two branch targets are gone.

**Where the three proved targets live, and why.** They cannot be proved where they were stated.
`HPC/Fold/Mixed.lean` (which carries `s3_span_nine_mid5` and `s3_span_nine'`) and
`HPC/Fold/General.lean` (which carries `s3_span_nine`) are *imported by* every file that closes the
branch at `L + 5` — the chain runs `Mixed → … → CoverL5Land → … → Mid2Index67 → Ceil68 → Ceil69 →
Deep70 → Reading70 → Distance71 → Valley72 → Descent73`. The three statements are therefore kept in
place, unchanged, commented out, each with a note naming `HPC/Fold/Target73.lean`, and restated
there verbatim and proved. No other declaration in either file is touched, and nothing else in the
repository refers to the three names.

The two attainment hypotheses of `s3_span_nine_mid5` (`∃ t, ρ t = L` and `∃ t, ρ t = L + 9`) turn
out not to be needed; they are part of the commissioned statement, so they are kept, with leading
underscores and a note in the docstring.

Axiom profiles (`axioms-batch73.txt`, produced by `#print axioms`) are
`[propext, Classical.choice, Quot.sound]` for every declaration of the two new files and for the
three targets. No `native_decide`, no new axiom, no `implemented_by`.

## 2.1 Does the `w8`-failing descent place the valley? Yes

The reading is right, in every clause, and it needs no distance hypothesis. It is
`ceil72_run_of_cross_highRunG` (`HPC/Fold/Descent73.lean`):

> at a basepoint `i` of the band `[L, L + 9]` with `ρ i = L + 5` which is a crossing of the
> trichotomy (`TriCrossL5`) and whose forward arm runs high (`HighRunG`), `Ceil72 (armG ρ i) L`.

and its mirror `ceil72_run_of_cross_highRunT`. The proof is the commission's, step for step:

1. the running arm is a `w8` arm (`leg4Land_w8_armG_of_highRun`, batch 72), so the first clause of
   `TriCrossL5` denies `w8` to the partner, and `w8_floor_fail_of_not_w8` returns a partner index
   `d₀` with `armT d₀ ≤ L + 2` and the sentence *for every partner index `j` with `4 ≤ j` and
   `j + (L + 7 − armT d₀) ≤ d₀`, `armT j < L + 7`*. `d₀ ≠ 0`, since the basepoint is at `L + 5`, so
   its chain index `a` satisfies `a < i` and `ρ a ≤ L + 2`;
2. `crooked_peak_valley_high9_mid` between `a` and the chain index `b = i + d` of any ascent
   `armG d ≥ L + 9` returns `r`, `r'` with `a + 70 ≤ r`, `r + 29 ≤ r'`, `r' + 70 ≤ b`,
   `L + 7 ≤ ρ r`, `L + 8 ≤ σ r`, `ρ r' ≤ ρ a + 1 ≤ L + 3`;
3. `r > i`. If `r < i` then `r` is a partner time at arm index `q = i − r`, and `L + 8 ≤ σ r` gives
   `q ≥ 5` by `armT_index_of_sig8`; the second condition of the `w8`-failure sentence reads
   `a + (L + 7 − ρ a) ≤ r`, which holds because `L ≤ ρ a` bounds `L + 7 − ρ a` by `7` and step 2
   gives `a + 70 ≤ r`; so `ρ r < L + 7`, against `L + 7 ≤ ρ r`. If `r = i` then `ρ r = L + 5`;
4. hence `r` and `r'` are running-arm times at indices `j = r − i` and `k = r' − i`, and
   `armG_index_of_sig8` (again from `L + 8 ≤ σ r`) gives `j ≥ 5 ≥ 3`. `Ceil72`'s three index
   conditions are `3 ≤ j` (`j ≥ 5`), `j + 5 ≤ k` (`k ≥ j + 29`) and
   `k + (armG d − (L + 3)) ≤ d`, where `k + 70 ≤ d` from `r' + 70 ≤ b` and the band bounds
   `armG d − (L + 3)` by `6`; the two level conditions are `L + 6 ≤ armG j` (`= ρ r ≥ L + 7`) and
   `armG k ≤ L + 3` (`= ρ r' ≤ ρ a + 1 ≤ L + 3`).

One small correction of detail to §2.1's last arithmetic line: `armG d − (L + 3)` is `6` only when
the ascent is exactly at `L + 9`; in general the band gives `armG d − (L + 3) ≤ 6`, which is what
the proof uses, and the conclusion is unchanged.

What separates this reading from batch 69's is exactly what the commission says: batch 69 paired
from the *nearest* low time, which may have a partner time at `L + 7` or above before it — that is
what `not_nearLowBandCrossL5` (batch 71) exploits — whereas the descent `w8`'s failure returns
carries, as part of the failure, the sentence that no such partner time precedes it. The peak of
the pairing therefore cannot be a partner time, and it lands on the running arm.

## 2.2 Assembly

With §2.1, the high-run crossings fold in both orientations
(`s3_span_nine_mid5_of_cross_highRunG`, `…_highRunT`, `HPC/Fold/Descent73.lean`), by the batch-72
assembly, whose partner clause is already free.

The exhaustiveness the commission asks to have confirmed is confirmed, with one correction of
attribution. At a crossing the split is on `DeepFirst2`:

* both arms `DeepFirst2` — `s3_span_nine_mid5_of_cross_deepFirst2` (batch 68) folds the pair onto
  `w71`;
* otherwise some arm fails `DeepFirst2`, and *failure of `DeepFirst2` inside the band is exactly a
  high run* (`highRunG_of_not_deepFirst2` / `highRunT_of_not_deepFirst2`, batch 70), so §2.1
  applies to that arm.

So the two cases are exhaustive by `highRunG_of_not_deepFirst2`, not by `not_bothHighRun_of_cross`.
`not_bothHighRun_of_cross` says something stronger and different — that at a crossing the two arms
cannot *both* run high — and it is what makes the partner's ceiling clause free inside
`ceil72_partner_of_cross_highRunG`; it is used, but it is not what closes the case split. This is
`s3_span_nine_mid5_of_cross`, and with it the residue `Leg4TriCrossL5` of `HPC/Fold/LandTri.lean`
is a theorem (`leg4TriCrossL5_holds`).

`s3_span_nine_mid5_of_leg4TriCrossL5` then adds the non-crossings — the basepoints where one walk
of the three of `leg4Land_tri` serves both arms, folded by
`s3_span_nine_mid5_of_leg4Land_direct` / `_refl` — and gives `s3_span_nine_mid5`. Span nine is
`s3_span_nine_of_mid` applied to `s3_span_nine_mid4` (batch 56) and the branch, which is
`s3_span_nine'`, and `s3_span_nine` is that statement under its other name.

## 2.3 The inventory

`inventory-batch73.md`, as commissioned: a statement only, with no claim about any other span. It
walks the kernel dependency graph of `s3_span_nine` in the compiled environment — 494 declarations
of the `HPC.Fold` namespace, of which 471 are written in the repository and 23 are compiler
generated — and splits the 471 by whether the statement (for a definition, the body) pins a level
by a literal offset `L ± k` or `H ± k`: 304 do, 161 do not. The criterion is syntactic, and the
file says so, with the two caveats that matter: a statement in the first list is not thereby known
to fail at another span, and a statement in the second list may still be *used* only at nine,
because the timing constants enter through `z` and `minGap`, which are generic in the number of
levels while every call site here fixes that number from the band.

## 2.4 The fallback census

Not run, and not needed: §2.1 holds as a theorem, so the census of batch 72 §2.2 restricted to the
`w8`-failing descent has nothing left to decide. The census corpus of batches 70–72 is unchanged
and is not re-run in this batch; no new census is claimed.

## Files

* `HPC/Fold/Descent73.lean` — the reading of §2.1: `ceil72_run_of_cross_highRunG` and its mirror,
  the two fold theorems at a high-run crossing, the crossing theorem `s3_span_nine_mid5_of_cross`,
  and `leg4TriCrossL5_holds`.
* `HPC/Fold/Target73.lean` — `s3_span_nine_mid5`, `s3_span_nine'`, `s3_span_nine`.
* `HPC/Fold/Mixed.lean`, `HPC/Fold/General.lean` — the three statements kept, commented out, with
  a pointer; nothing else changed.
* `HPC.lean` — two import lines.
* `axioms-batch73.txt`, `inventory-batch73.md`, `COMMISSION-batch73.md`, this report.
