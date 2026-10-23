# Commission: batch 54 — inside the residues, and four turns at `L + 5`

**Go!** Runs on top of the batch-53 delivery. No new file is prescribed: the targets are the
`sorry`s of `HPC/Fold/CrossCeil.lean`, `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` as they
stand.

## 0. On batch 53

Audited: every earlier Lean file identical except `CrossCeil.lean`; two new files, no new `sorry`;
standard axioms, no `native_decide`; no counterexample. The ceiling crossing is reduced to two
clauses (`CeilCrossGap`) and proved off two local residues, each an *index* shortfall within four
steps of the basepoint; the level shortfall at the ceiling is located exactly (`topW5_low3`). The
valley residue is realised in abundance — 267 877 basepoints, more than half of the cases the
item speaks of — and batch 52's "unrealised" was a count of an arm-level proxy, not of
`ValleyResidual` as `CrossValley.lean` defines it. That is the fourth census–Lean mismatch, and
this batch's audit caught it. The protocol is tightened accordingly:

> **Every predicate that appears in the statement of a Lean theorem the census is offered as
> evidence for — hypotheses, residues and conclusions alike — is evaluated by the census as the
> definition reads it, and is named in the audit list. A proxy is reported as a proxy.**

At the branch `L + 5`: 182 of 321 874 unserved pairs are served by none of the three reflected
walks, 42 of them by no walk of at most three turns at all, and no short witness exists (shortest
unserved prefix pair has arms of 113 and 874 steps). The σ-route serves every pair there on the
arms of `τ = 9 − σ` and loses one link coming back. Bing's seam (question 4) was not attempted;
the theorem is comfortable at `bing 0 4` basepoint 6 (`s3_span_eight`), so the question is about
the construction only.

## 1. Targets

1. `cross_ceil_sentence` — `CeilCrossGap` inside `CeilPeakResidual` and `CeilHighResidual`.
2. `cross_valley_profile` — inside `ValleyResidual`, which is where most of the model is.
3. `unserved_three_walks`, from 1 and 2.
4. `s3_span_nine_mid5`, through `s3_span_nine_mid5_of_sentence` with the list the branch needs.
5. `s3_span_nine`, `s3_general`; if `s3_general` is proved, close `theorem3` by `theorem3_of_S3`.

A counterexample to any of these is a success and is reported first, after a definition audit. A
refuted statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **What happens inside the residues?** Every residue so far is a configuration within four
   steps of the basepoint, and in every one the census says the pair is served — but the proof
   reaches the right level at the wrong index, or the right index one level short. Whether the
   pairs inside a residue are served by the *same* walk with a different base (`FoldsOnto` lets the
   walk start within one of `ρ i`), or by a different walk, or by the same walk through a fold the
   greedy engine does not find, is a census question first: for each residue, which walks serve
   its pairs. If one walk serves a whole residue, the residue is a branch of its own with the
   sentence machinery already in place.
2. **Engines for four turns.** The branch `L + 5` needs walks of four turns. The necessity half of
   the landmark sentence is a theorem for every walk; the sufficiency engines exist for three legs
   with peak, trough and start window as parameters. Whether the same four invariants (clock, `R`,
   slack clock, `S`) give the engine for a walk of any number of legs, with landmark positions as
   constants — the general sufficiency asked since batch 48 — is asked again, now with a concrete
   need: the ten walks of the batch-53 table.
3. **The σ-route's lost link.** A fold of the arms of `τ = 9 − σ` serves every pair of the branch
   `L + 5`; a fold of `σ` gives four-link blocks (`exists_blocks_first_of_folds_max`). Whether the
   fold of `τ` can be *modified* — not transported — into a fold of the arms of `ρ` with window one,
   using that `σ − ρ ∈ {0, 1}` and the adjacency clause of the model, is asked. If it can, the
   branch `L + 5` is the branch `L + 4` and the asymmetry is bookkeeping; if it provably cannot,
   that is the one level as a theorem.
4. **Bing's seam**, as in batch 53 §2.4, still open: implement the dissolve-and-regroup move at
   `bing 0 4` basepoint 6 and report whether it succeeds, and if not whether the failure is a seam
   block one link wider than the theorem allows.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model, generators named, fraction of non-thin links stated, with the
   definition audit under the tightened protocol; censuses over arms alone say so.
3. Report: any counterexample first; then §1 in order; then §2 1–4, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
