# Commission: batch 55 — the witness inside the residue, and Bing's seam as a deliverable

**Go!** Runs on top of the batch-54 delivery. No new file is prescribed for the targets; one new
file is prescribed for §3.

## 0. On batch 54

Audited: every earlier Lean file identical; two new files, no new `sorry`; standard axioms, no
`native_decide`; no counterexample over 5 008 + 8 287 general pairs including two generator
families outside Bing's (random concatenations of Bing blocks; free depth-first walks). Both
residues sharpened by the first use of the *interval* clause in a crossing proof (a level met
within one step of the anchor, witnesses strictly between) — and the sharpening removes nothing
from the corpus: every residual `L + 2` is a weak local minimum with both neighbours at `L + 2`
or above. So the interval clause is exhausted at the residues.

Two facts fixed by the batch:

* **The residues are not new branches.** One walk serves each residue whole: the V-walk at every
  valley-residual pair with a failing arm (118 663), the V-walk and `w₅` at every ceiling-peak
  residual pair (34). The conclusion holds where the proof stops.
* **The σ-route loses a walk, never a basepoint.** At 1 241 basepoints the walk that serves the
  arms of `τ = 9 − σ` fails on `9 − ρ`, but at every one another of the five serves `9 − ρ`. A
  modification that keeps the walk provably does not exist (general-model counterexamples with
  `σ − ρ = 1` at the breaking link).

## 1. Targets

Unchanged: `cross_ceil_sentence`, `cross_valley_profile`, `unserved_three_walks`,
`s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`. A counterexample is a success and is
reported first, after a definition audit.

## 2. Questions, asked as questions

1. **Where is the witness?** At every valley-residual pair the V-criterion holds on the arm `Y`:
   there is a time at `L + 2` or below at index four or later before `Y`'s ascent to `L + 7`. The
   proof finds only the residual time at index two or three. The census can locate the witness the
   criterion actually uses at each of the 118 663 pairs: its index, its level, its position
   relative to the residual time `u` and the ascent `e`, and whether it is produced by an
   application of the clause the proof has not made — with which anchors, which levels, and on
   which arm the anchors lie. If one anchoring produces it at every residual pair, that anchoring is
   the missing step; if none does, the witness is not a clause consequence and the residue is a
   real obstruction to this method. The same for the 34 ceiling-peak pairs and `TopW5`.
2. **Is the σ-route a theorem with the walk allowed to change?** Over the corpus, whenever the
   `τ`-arms fold onto one of the five walks, the `(9 − ρ)`-arms fold onto one of the five. Whether
   that is provable — a fold of the upper sequence yields a fold of the lower one onto *some* walk
   of a fixed finite list — is asked. If it is, the branch `L + 5` follows from the branch `L + 4`
   after all, by a different mechanism than reflection.
3. **Engines for four turns**, as in batch 54 §2.2, with the two test walks `5 → 7 → 3 → 8 → 1` and
   `4 → 3 → 7 → 1 → 8` and the two obstructions named there (base at `L + 5`; valley three below the
   base; the mirror shape). Unattempted for two batches; asked again.

No opinion is offered on the answers.

## 3. Bing's seam — now a deliverable, in a file of its own

Twice asked, twice not attempted, and the report says why: the move is not in the repository and
has to be written from the paper. So this batch prescribes the file: `HPC/Fold/BingSeam.lean` (or
a census program, if a program is the honest first pass), carrying the construction of p. 733 as
the exposition reads it:

> Let `D` be crooked in `E = [e₁, …, e_m]`, `d_i` a link of `D`, `m > 4`, `d_i ⊄ e₁ ∪ e₂`,
> `d_i ⊄ e_{m−1} ∪ e_m`. Take `D(h, k)` maximal containing `d_i` with no interior link meeting
> `e₁` or `e_m`. By induction, `H = [h₁, …, h_s]` is a consolidation of `D(h, k)` with `d_i` in
> `h₁` only and every `h_j` in two adjacent links. Let `h_u` be the first link of `H` meeting
> `e₁ ∪ e_m`; say it meets `e₁`, so (Bing) `h_u ⊂ e₁ ∪ e₂`. Then `F` is `H(1, u − 1)` followed by
> the remaining links of `D` grouped as: those in `e₁ ∪ e₂`; those in `e₃` not in `e₂`; …; those
> in `e_{m−1} ∪ e_m`.

Deliverable: run this at `bing 0 4`, basepoint 6 (and at every basepoint of `bing 0 4`, `bing 0 5`,
`bing 0 6` in the thin model), with the inductive consolidation supplied by any correct source
(the repository's own folds will do), and report for each basepoint: whether the output is a chain,
whether `d_i` is in the first link only, the width in links of every block, and in particular the
width of the seam block. The prediction to refute: at some basepoints the seam block has width
three because `h_u` reaches into `e₃`, and no other block exceeds two. Whether the prediction holds
or fails, the table is the deliverable.

## 4. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the tightened audit protocol; censuses over arms alone
   say so.
3. The §3 table, with the program or file that produced it.
4. Report: any counterexample first; then §1; then §2 1–3; then §3.

## 5. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
