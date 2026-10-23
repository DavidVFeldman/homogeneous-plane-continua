# Commission: batch 142 — Part D, Moore VI: Moore 1919, Theorem C corrected; Theorem D

**Go!** This batch builds on the batch-141 delivery. Two files come with it, as separate uploads:

* `COMMISSION-batch142.md`: this text, also pasted into the prompt.
* `Moore1919CD2.lean`: the skeleton. Save it as `HPC/Moore/M19CD2.lean` (splitting it is expected)
  and add `import HPC.Moore.M19CD2` at the end of `HPC.lean`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore 1919 C corrected, D (batch 142)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`: close the Theorem D entry if you prove it;
  * `HPC/Moore/M19CD.lean`: remove the commented-out Theorem D once it is proved here.

## 0. On batch 141

Audited and accepted.

* **Proved:**
  * the subdivision lemma, giving `(n+1)(m+1)` cells, each the interior of a closed curve;
  * refinement and padding (`doubleRuling_refine` with any subset-closed `Good`; `doubleRuling_pad`);
  * the cut-and-glue and extension machinery;
  * the region form of D from the curve form.
* **Fig. 1 count:** 9 arcs and 8 arcs. This settles that unequal families are needed, and padding
  shows they cost nothing.
* **Theorem C refuted as printed** (`not_m19_theoremC_printed`). The refutation holds in every model
  of Axioms 1–8: a curve touching a side from within. This is a defect of the printed theorem, not
  only of its "indication of proof". It also breaks Moore's proof of Theorem D, which applies C to a
  curve `J̄` that `g₁` may touch.
* **Theorem D open,** with the three obstructions you recorded.

## 1. Where this sits

| batch | content |
|---|---|
| 141 | double rulings; subdivision, refinement; C refuted (done) |
| **142 (this one)** | corrected Theorem C (three forms); Theorem D |
| 143 | 1919 Theorems E, F, G and the final correspondence |
| 144 | Moore 1925 §I and Theorem 22 |
| 145 | Jones 1955 Theorem 2, with Jones 1949 |

**Theorem D is the crux of the 1919 paper.** It says that grids exist subordinate to any cover. Its
consequence, Theorem E, is in effect the Schoenflies theorem for Moore's space. Close it first.

## 2. Items

**A. Corrected Theorem C, in three forms** (skeleton).
1. `m19_theoremC_crosscuts`: a finite system of pairwise disjoint cross-cuts, with ends off `A, B,
   C, D`, can be absorbed into a double ruling. Your route (i) applies: induction with cut-and-glue,
   using Moore's three chord types. A cross-cut joining opposite sides is cut along; one joining
   adjacent sides, or with both ends on one side, is first completed along a piece of itself to a
   ruling arc.
2. `m19_theoremC_within`: a closed curve lying within `ABCDA` can be absorbed. This is your route
   (ii), the nine-cell configuration of Theorem G's Fig. 3. Batch 143 needs the nine-cell form, so
   state it if it is convenient.
3. `m19_theoremC_corrected`: the printed statement with the touching configuration excluded. Derive
   it from (1), since the pieces of `g` within `ABCDA` are then disjoint cross-cuts. The touch
   hypothesis in the skeleton is one rendering; replace it with a cleaner equivalent if you find
   one, and record it. Also record whether `hfin` is still needed.

**B. Theorem D.** Any correct proof will do. Moore's own proof needs the corrected C and a choice of
`J̄` that `g₁` crosses. That choice is unargued and may fail, as in your obstruction 1. Your route
(iii) is:
* first two-element covers, by separating two disjoint closed subsets of `J + I` with a system of
  cross-cuts and closed curves;
* then any finite cover, by induction on its size, shrinking the cover so that the closures of the
  subdivisions stay covered.

It is acceptable. So is any other elementary route. Quote the printed sentences of Moore's proof
that your argument replaces.

## 3. Places to check (candidate ledger entries)

1. **Theorem C:** the corrected hypothesis is "no touching from within". Record the precise form
   proved, and whether touching *from without* (a point of `g ∩ J` that is the end of no arc of `g`
   within `ABCDA`) is harmless. It should be.
2. **Theorem D, the choice of `J̄`:** "There exist, on the segments `ĒₙF̄₁, F̄ₙL̄₁, L̄ₙM̄₁, and M̄ₙĒ₁`
   respectively, points `B̄, C̄, D̄`, and `Ā` that are not on `g₁`. The arcs of `α` form a closed curve
   `ĀB̄C̄D̄Ā` …". Record whether Moore's `J̄` can be chosen so that `g₁` crosses it at every common
   point. If it can, Moore's proof is repaired; if not, his proof fails at this step and your route
   replaces it.
3. **Theorem D, the induction** ("It can be shown in a similar way … This process may be
   continued"): record the obstruction you found (cell boundaries meeting `g₂` infinitely often)
   and how the proof avoids it.
4. **Theorem D, "It easily follows that there exist (Fig. 2) …":** record whether your proof needs
   `J′` at all.

## 4. Deliverables

1. Items A and B.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch142.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * an update of the batch-141 reading plan for Theorems E, F and G, in the light of the D you
     proved.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the
   root.
