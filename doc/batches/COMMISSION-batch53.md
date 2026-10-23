# Commission: batch 53 — the ceiling crossing, the branch `L + 5`, and Bing's seam

**Go!** Runs on top of the batch-52 delivery. No new file is prescribed: the targets are the
`sorry`s of `HPC/Fold/CrossCeil.lean`, `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` as they
stand.

## 0. On batch 52

Audited: every earlier Lean file identical; five new files; standard axioms, no `native_decide`;
one new `sorry` (`cross_ceil_sentence`, a named work item). The refutation is the result of the
batch: the branch `L + 5` is not the reflection of the branch `L + 4`. The criteria reflect
(`ArmReflect.lean`, no model symmetry used); the crookedness clauses do not (`CrookUp` and
`CrookDown` are not mirror images — their windows differ by one level — and the model delivers only
the unreflected pair, `ArmReflectGap.lean`); and the list of walks does not (`not_threeWalks5Arms`:
771 of 74 884 unserved basepoints at `L + 5` are served by none of the three reflected walks, and
166 by none of five). The definition audit ran on the reflected predicates and on the transport
theorem itself (3 126 010 checks). The valley residue is unrealised as a pair over 1 369 general
pairs; the ceiling crossing holds at all 521 configurations where it is tested.

One fact from the batch to keep in view: the asymmetry between the two branches is the asymmetry
between `ρ` and `σ`. The reflection of the general model sends `(ρ, σ)` to `(a − σ, a − ρ)`, so the
branch `L + 5` of `ρ` is the branch `L + 4` of the *upper* sequence, read upside down. That is
the same one level as everywhere else in the general model.

## 1. Targets

1. `cross_ceil_sentence` (`CrossCeil.lean`). With it and the valley side, `unserved_three_walks`.
2. `cross_valley_profile`.
3. `s3_span_nine_mid5`, through `s3_span_nine_mid5_of_sentence` with whatever sentence the
   branch turns out to need.
4. `s3_span_nine`, `s3_general`; if `s3_general` is proved, close `theorem3` by `theorem3_of_S3`.

A counterexample to any of these is a success and is reported first, after a definition audit. A
refuted statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The list at `L + 5`.** What serves the 166? Whether the list of walks at `L + 5` is finite
   and stable as the corpus grows, and what its members are, is asked. Since the branch `L + 5` of
   `ρ` is the branch `L + 4` of `a − σ`, whether the three walks of `L + 4`, read on the arms of
   `σ`, serve every pair there — and what a fold of the arms of `σ` is worth for the arms of `ρ`
   beyond `exists_blocks_first_of_folds_max` — is asked alongside.
2. **`cross_ceil_sentence`.** Whether crookedness across the basepoint gives it, as the valley
   crossing was given off its residue; and if the proof stops one level short, exactly where.
3. **The valley residue.** Unrealised over 1 369 pairs. Whether it is excluded in the general
   model, or a generator exists that reaches it (a mixture at a higher rate, a chain other than
   Bing's), is asked; a realisation would settle whether `cross_valley_profile` needs the
   configuration excluded or merely survives it.
4. **Bing's seam.** A question about the paper, not about a target. Bing's proof of Theorem 3
   (p. 733) cuts the inductive consolidation `H` of the inner chain at the first block `h_u`
   meeting `e₁ ∪ e_m`, asserts `h_u ⊂ e₁ ∪ e₂`, and regroups the rest of `D` by level from there.
   The inductive hypothesis places `h_u` in two adjacent links of the inner chain `E(2, m − 1)`,
   so in `e₂ ∪ e₃`; the assertion needs `h_u ⊂ e₂`. Batch 24 implemented his construction without
   the regroup-by-level move and it failed at basepoint 6 of `bing 0 4`. Whether the move as
   written — dissolve every block from `h_u` on and regroup by level — succeeds or fails there,
   and if it fails whether the failure is exactly a seam block one link wider than the theorem
   allows, is asked. If the second, it is a proposition about the paper with a certificate:
   Bing's Theorem 3 holds with three links, and his written induction loses one link at each seam.

No opinion is offered on the answers; question 4 states a prediction so that it can be refuted.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model, generators named, fraction of non-thin links stated, with the
   definition audit; censuses over arms alone say so.
3. Report: any counterexample first; then §1 in order; then §2 1–4, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
