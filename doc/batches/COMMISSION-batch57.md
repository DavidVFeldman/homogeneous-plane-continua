# Commission: batch 57 — the branch `L + 5` by the same law, and the law at every span

**Go!** Runs on top of the batch-56 delivery. No new file is prescribed.

## 0. On batch 56

Audited: every earlier Lean file identical except the three whose imports changed and the two
where targets became proofs; four new files; standard axioms, no `native_decide`; no target
refuted. **The branch `L + 4` of span nine is complete**: `cross_valley_profile`,
`cross_ceil_sentence` and `unserved_three_walks` are theorems, `s3_span_nine_mid4` is
`sorry`-free, and `no_ceilHighResidual` turns a census zero into a theorem. The remaining
`sorry`s of the route are `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`.

What closed it is one lemma, `ivSep`: the crookedness clause of the faithful model read at the two
arms' own levels returns *links*, and Bing's Theorem 7 (`minGap`) counts the links between two
intervals meeting levels `d` apart — 5, 12, 29 steps for `d = 3, 4, 5`. Applied across the
basepoint that places the returned witnesses ten and twelve steps out where the criteria asked
for four. The "one level" that every batch since 45 reported as the general model's residue was
never a level: it was a *distance*, and the one-arm clauses `CrookUp`/`CrookDown` could not see it
because they read `ρ` alone and carried no count. The residues `ValleyResidual`,
`CeilPeakResidual` are not obstructions; `CeilHighResidual` is empty.

Two things fixed by this:

* **Theorem 7 is a lemma for Theorem 3 across the basepoint**, not only along one arm (batch 43).
  Every crossing statement in the route is now of one shape: clause at the arms' own levels,
  `ivSep` on what it returns.
* **Bing's seam, under the induction's hypothesis, breaks — but not where predicted.** No
  width-three seam; instead the head `H(1, u − 1)` is empty at most basepoints (`u = 1`) and `F`
  is not a chain (25 of 84 thin, 463 of 820 general). One thing about that test is recorded so it
  can be repeated correctly: the search took *any* width-two consolidation of the inner chain with
  respect to `E(2, m − 1)` and did not impose Bing's end clause on it — "any link of `H` containing
  an end link of the inner chain which meets its extreme link lies in that link and its
  neighbour". The clause is part of the statement being induced on.

At `L + 5`: the three reflected walks serve all but 917 of 1 464 514 basepoints, three four-leg
walks of the wide engine serve every one of the 917, and each has a proved criterion
(`CoverL5.lean`).

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`), through `s3_span_nine_mid5_of_sentence` or otherwise.
2. `s3_span_nine` (`General.lean`), which `s3_span_nine'` derives from the two branches.
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **Does the branch `L + 5` yield to the interval clause and `ivSep`?** The obstruction batch 52
   found to reflection was that `CrookUp` and `CrookDown` are not mirror images. The interval
   clause of `IsCrookedIvF` is symmetric under `(ρ, σ) ↦ (a − σ, a − ρ)`, and `ivSep` is stated on
   intervals. Whether the crossings at `L + 5` — for the three reflected walks and the three
   four-leg walks — close by the same two bounds, and whether the branch hypotheses `LowAt`
   deliver the announcements the six criteria ask for, is the branch.
2. **Is the `L + 4` proof a template?** Its shape: the leaf of `s3_span_seven_of_cases`; a split
   by `dichotomy_at`; for each branch a finite list of walks with exact landmark criteria; arm-only
   dichotomies (`_or_lam`, `_or_vee`) putting a failing arm onto a canonical walk; crossings closed
   by the clause at the arms' own levels and `ivSep`. Whether that shape is a proof of `S3` at
   every span — with the list of walks growing as the reversal law requires and the landmark
   engine (`foldsOnto_leg4W` and its predecessors) supplying criteria — is asked as the general
   question it has been since batch 42, now with the crossing mechanism known. If it is, say what
   the induction is on; if it is not, say which step does not generalise.
3. **Bing's seam with the end clause imposed.** Repeat `seam-batch56.py` with `H` restricted to
   width-two consolidations of the inner chain, with respect to `E(2, m − 1)`, **satisfying Bing's
   end clause** at both extremes of the inner chain, and report the same table (head empty or
   not; `F` a chain; `d_i` first only; seam width). Whether such an `H` exists at every basepoint
   is itself part of the answer.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the audit protocol; censuses over arms alone say so.
3. The §2.3 table, with the program that produced it.
4. Report: any counterexample first; then §1; then §2 1–3.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check.
