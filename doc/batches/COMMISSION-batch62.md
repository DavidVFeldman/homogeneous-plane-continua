# Commission: batch 62 — the crossing on the boundary of the timing law

**Go!** Runs on top of the batch-61 delivery. No new file is prescribed.

## 0. On batch 61

Audited: every earlier Lean file identical; two new files; standard axioms, no `native_decide`;
no refutation. Two corrections of the picture, both census facts: five walks are not the list, six
are — adding `w71 = L+4 → L+7 → L+1 → L+8 → L+1` (residue 84) and then `w72`, `w81` (residue **0
at every generator**); and the walk the crossings pick out is inside the engine's window — it is
the walk whose *engine* criterion batch 58 refuted and whose *exact* criterion (batch 59) serves
both arms of every crossing. The branch rests on `Leg4SixCrossL5`
(`s3_span_nine_mid5_of_leg4SixCrossL5`), which the corpus says is empty.

Three facts fixed by the batch:

* **The crossing is extremal for the timing law.** At every crossing the `w8` side's first climb to
  `L + 8` and the other side's first descent to `L + 2` sum to exactly seventy steps, and
  `cross_high8_low2_far` proves the bound: six levels across the basepoint, `z 6 = 71`.
  `cross_no_low2_before` is its consequence for the partner arm's opening.
* **Each side already owes `w71` one clause.** The `w8` side has `w71`'s floor clause and owes its
  ceiling clause (`leg4Land_w71_of_w8_of_ceil`); the `wb`/`w3` side has the floor clause at its
  descents to `L + 1` and owes it at descents to exactly `L + 2`, plus the ceiling clause
  (`leg4Land_w71_of_wb_of_rest`). Neither is unconditional on arms alone (`probe61`: 1 590 250 arms
  served by `w8` and not `w71`); at a crossing both hold.
* **The landmark sentence is stated for any walk** (`LandList.lean`: `walkList`, `LandWalk`) and its
  necessity is a theorem for any walk (`landWalk_of_foldsOnto`); `leg4Walk` is an instance. The
  sufficiency half is the only missing half of the general engine.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`), through `Leg4SixCrossL5` or `Leg4QuadCrossL5`.
2. `s3_span_nine` (`General.lean`).
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The two owed clauses, from the pairing.** At a crossing the `w8` side `X` climbs to `L + 8` at
   step `dG` and the other side `Y` descends to `L + 2` at step `dT` with `dG + dT ≥ 70` and, in the
   corpus, `= 70`. What `X` owes is `w71`'s ceiling clause (before an ascent to `L + 9`: `L + 6`,
   then six steps later `L + 2`); what `Y` owes is the floor clause at its descents to exactly
   `L + 2` and the ceiling clause. Whether the clause read between `X`'s climb and `Y`'s descent at
   their own levels, with `ivSep` at six levels and the two `cross_*` theorems, supplies them — or
   whether a second pairing (Y's `L + 9`, if any, against X's opening) is needed — is the branch.
   If the argument stops, say whether at an index or at a level.
2. **Why exactly seventy.** The equality `dG + dT = 70` at every crossing of the corpus is the
   extremal case of `z 6 = 71`. Whether that is forced — a crossing of the three walks exists only
   at the extremal configuration, and the extremal configuration is a *single* shape of Bing's
   chain up to shaving and filling — is asked. If so, the crossing is not a case but a witness, and
   the proof of question 1 has one configuration to handle.
3. **Sufficiency for `LandWalk`.** The invariant of `gseq4_invLand` with two bounds per interior
   leg and the credit equal to the gap of consecutive turn times, stated over `walkList s ts`. The
   statement in Lean is a deliverable even if the proof is not; the proof is the general engine.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the audit protocol; censuses over arms alone say so.
3. Report: any counterexample first; then §1; then §2 1–3.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
