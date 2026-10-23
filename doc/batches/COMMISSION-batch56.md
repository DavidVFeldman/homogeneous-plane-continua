# Commission: batch 56 — the far witness, and the seam under the induction's own hypothesis

**Go!** Runs on top of the batch-55 delivery. No new file is prescribed.

## 0. On batch 55

Audited: every earlier Lean file identical; two new files, no new `sorry`; standard axioms, no
`native_decide`. The σ-route is refuted with a kernel-checked instance (`Audit55.lean`): 501
basepoints where the `τ`-pair folds onto one of the five and the `(9 − ρ)`-pair onto none. Batch
54's "loses a walk, never a basepoint" was a fact about that corpus, as the report says. The wide
four-leg engine (`Leg4Wide.lean`) covers both test walks; the raise of the floor announcements from
`M − 1, M − 2` to `P − 3, P − 4` is forced (engine sweep: old reading fails at all 18 parameter
sets with `M < P − 2`, new reading at none).

**The witness.** At every valley-residual pair the V-criterion's witness exists, is at `L + 2`
exactly, and is far: index 8 or 12, and 29 or 31 steps before the ascent — never the residual
time at index two or three. No single application of the clause forces it at four fifths of the
pairs, and no anchoring scheme within 24 steps covers more than 4 364 of 95 209. So the residue is
a real obstruction to the one-application method. Two numbers in that table are not accidents:
`z 5 − 1 = 29` is the least distance from a time at `L + 2` to a time at `L + 7`, and the witness
sits at that distance from the ascent.

**Bing's seam.** The prediction fails on `bing 0 4`, `bing 0 5`, `bing 0 6`: with `H` of width two
the construction goes through at all 84 basepoints, seam width two, `F` a chain, `d_i` first only.
Recorded as such. One thing about the test is fixed here so it is not mistaken for more than it
is: `H` was any width-two consolidation of `D(h, k)` **with respect to `E`**, found by search. Bing's
induction is on the number of links of `E`, so the consolidation his hypothesis supplies is of a
chain in a *shorter* coarse chain, and a block of it containing an end link of the inner chain
lies in two adjacent links of the shorter chain, not of `E`. The test shows the regroup step is
sound when `H` is width two in `E`; it does not test what the induction hypothesis yields.

## 1. Targets

Unchanged: `cross_ceil_sentence`, `cross_valley_profile`, `unserved_three_walks`,
`s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`. A counterexample is a success and is
reported first, after a definition audit.

## 2. Questions, asked as questions

1. **Is the far witness a consequence of the timing law?** Apply the clause between the failing
   arm `X`'s descent to `L + 1` and the other arm `Y`'s ascent to `L + 7`; it returns a time at
   `L + 6` and a later time at `L + 2` between them in chain order. Whether the timing laws
   (`minGap` across the basepoint: five levels need 29 steps, four need 12) place the returned
   `L + 2` at index four or later on `Y` — and in which subcases they do not (the returned `L + 6`
   on `X`'s first two steps; `X`'s descent late) — is asked. If the subcases are finite and each
   closes, the residue closes; if one does not, it is the residue's true shape.
2. **Is the witness a property of the model or of the corpus?** Every pair of every generator has
   it. A targeted construction — a general pair in `ValleyResidual` whose arm `Y` has no time at
   `L + 2` or below at index four or later before its ascent — would refute `cross_valley_profile`
   and, unless another walk serves it, `unserved_three_walks`. Whether such a pair exists, or the
   timing law excludes it (question 1), is the same question from the other side.
3. **The seam under the induction's hypothesis.** Run `seam-batch55.py` again with `H` a width-two
   consolidation of the inner chain **with respect to `E(2, m − 1)`** — the chain the induction is
   on — with the end links of `D(h, k)` that meet `e₁` or `e_m` attached at the regroup, and report
   the same table: is `F` a chain, is `d_i` first only, and the seam width. Then the same in the
   general model (links straddling two links of `E`), on shavings of `bing 0 6` and `bing 0 7`.
   The prediction to refute is the one of batch 55, now aimed at the right object: a seam of width
   three when the block containing the inner end link reaches one link past the extreme.
4. **Four turns at `L + 5`.** With `foldsOnto_leg4W` and its reflection, whether the walks of the
   batch-53 table now each have a criterion, and whether a finite list of them with criteria
   covers the branch, is asked — the sentence machinery of `ArmReflect.lean` is in place for it.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the tightened audit protocol; censuses over arms alone
   say so.
3. The §2.3 tables, with the program that produced them.
4. Report: any counterexample first; then §1; then §2 1–4.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
