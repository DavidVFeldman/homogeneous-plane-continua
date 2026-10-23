# Commission: batch 140 — Part D, Moore IV: F.A. Theorems 41–43 completed; Moore 1919, Theorems A and B

**Go!** This batch builds on the batch-139 delivery. Three files come with it, as separate uploads:

* `COMMISSION-batch140.md`: this text (also pasted into the prompt).
* `Moore1919AB.lean`: the skeleton. Save it as `HPC/Moore/M19AB.lean`. Splitting it into several
  files is expected. Add `import HPC.Moore.M19AB` at the end of `HPC.lean`.
* `moore1919.pdf`: R. L. Moore, *Concerning a set of postulates for plane analysis situs*, Trans.
  AMS 20 (1919), 169–178. Save it as `doc/sources/moore1919.pdf`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore F.A. 41–43, 1919 A–B (batch 140)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`: remove the batch-139 entries that this batch closes, and add only what remains open.
  * You may also delete the commented-out open statements at the end of `HPC/Moore/FA7.lean`, once
    they are proved here.

## 0. On batch 139

Audited and accepted. The open items are recorded correctly.

* **Skeleton and statements.** The skeleton copy is byte-identical. Every statement is the
  skeleton's, with axioms made explicit. Theorem 38's shape, which I left to you, is accepted.
* **Axioms.** `axioms.txt` has 901 lines, with `sorryAx` in none.
* **New results:**
  * the corrected step of Theorem 36 (the arc `BC` cut at its first point outside `R`);
  * the finite-chord proof of Theorem 37;
  * Theorems 39 and 40 from one accessibility lemma;
  * Theorem 43 refuted at `G = ∅`.

**Theorems 41–43 are on the critical path.** Moore 1919 cites:
* Theorem 42 in the proof of its Theorem F, which constructs the closed curves exhausting the plane;
* Theorem 43 in the proof of Theorem B ("It is easy to see, with the aid of Theorems 43 and 40") and
  in footnote * of p. 174 (Theorem D: "Make use of Theorems 43 and 40 and the existence of the curve
  ABTNA described on page 149 of Foundations").

So they must be settled before the 1919 batches go further.

## 1. Where this sits

| batch | content |
|---|---|
| 137–139 | F.A. §§2–7 to Theorem 40 (done) |
| **140 (this one)** | F.A. 41–43; 1919 Theorems A, B |
| 141 | 1919 Theorems C, D (double rulings) |
| 142 | 1919 Theorems E, F, G and the final correspondence with the number plane |
| 143 | Moore 1925 §I and Theorem 22 |
| 144 | Jones 1955 Theorem 2, with Jones 1949 |

**The 1919 paper is the sketchiest source so far.** I read it from the page images.
* *Theorem C* has only an "Indication of proof", one example (Fig. 1), "given instead of a tedious
  formal proof covering all possible cases".
* *Theorems D and E* proceed by "This process may be continued".
* *Theorem G* ends "It is clear that through every point there is just one curve of the set α and
  just one curve of the set β …".
* *The final paragraph* asserts continuity of the coordinate map with "It is clear".

Batches 141–142 will have to write those proofs. This batch prepares the ground.

## 2. Items

**A. F.A. Theorem 41, Case II** (open in batch 139).

The obstruction you recorded is that Moore's `J` can be made of infinitely many arcs `t_P`. A
suggested route:
* The arcs `t_P` lie on `J₁`, have disjoint interiors, and are pairwise non-overlapping sub-arcs of
  a single arc or closed curve.
* So for each `ε > 0` only finitely many have diameter `≥ ε`. This follows from uniform continuity
  of a parametrization of `J₁`, or from Theorem A of 1919, which says exactly this kind of thing.
* The same holds for the replaced intervals `k_P` of `J₂`.
* *Replacement of a null family of arcs.* Let `f : circle → J₂` be a parametrization. Replace `f`,
  on each parameter interval of a `k_P`, by a parametrization of `t_P` with the same endpoints. The
  result is continuous, because the diameters tend to 0, and injective. So `J` is a simple closed
  curve.
* Then show `I₁ ∪ I₂ ⊆ I` as Moore intends.

Any correct route is fine. Then prove `fa_theorem42` (from your `fa_theorem42_of_41`).

**B. F.A. Theorem 43, corrected (`G` nonempty).** Moore gives no proof. If a proof is within reach,
give it. Otherwise prove only what 1919 draws from Theorem 43:
* `m19_B_step`, the arc in the proof of Theorem B;
* the arc in footnote * of p. 174, used in Theorem D: "Within `ḡ₁` (and within `J` except for the
  point `A₁`) there is an arc `A₁E′₁` that has in common with `E₁E′₁` only the point `E′₁`". State it
  in the form Theorem D needs.

Leave the general Theorem 43 open in that case.

**C. Moore 1919, Theorem A** (p. 170). The proof is printed.
* It uses "Cf. the proof of Theorem 37 on pages 152 and 153 of *Foundations*".
* "No two arcs of `G` have a segment in common" is rendered by `ShareSegment`. Check the reading.

**D. Moore 1919, Theorem B** (pp. 170–172). Follow the proof. Footnote ‡ gives an example (the curve
`y = x sin(1/x)`) showing that the restriction on `A`, `B` cannot be dropped. It is set in the
ordinary plane and is not to be formalized. Record it.

## 3. Places to check (candidate ledger entries)

1. **Footnote †, p. 170:** "there are just two arcs that lie wholly on `J` and have `A` and `B` as
   endpoints". The points are called `X` and `Y` in the same sentence, so this is a misprint.
2. **Theorem B, unargued steps:**
   * "it is clear that there exists a point `A₁` which is the first point that the segment `AB` has
     in common with `L`";
   * "By an argument similar to the above proof of the non-existence of `X` it can be shown that
     `B₁` cannot be a limit point of a set of points of `M` no one of which can be properly joined to
     `A₁`";
   * "It is clear that `O` is either `Aₘ` or `Bₘ`";
   * "It is easy to see, with the aid of Theorems 43 and 40 …";
   * "In view of these considerations it is clear that the point-set `τ` contains, as a subset, an
     arc from `A` to `B` …".

   Supply each one.
3. **Theorem B's finiteness argument** uses Theorem A on arcs "such that each of them has one
   endpoint on `J` and the other on the interval `A₁O`". Check that Theorem A applies, with `M` and
   `N` closed and disjoint.
4. **Theorem 41 Case II:** the final sentence, "It may be proved that `J` is a closed curve
   satisfying the requirements of Theorem 41". Record how it was supplied.

## 4. Deliverables

1. Items A–D.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch140.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, giving the outcome of each check and quoting the
   printed sentence.
3. The report. Its first line names the commission. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * what Theorems C and D (pp. 172–176) need, as a short reading plan for batch 141: the double
     ruling definition (footnote *, p. 172), Theorem C's "indication of proof", and Theorem D's
     proof.
4. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   goes at the root.
