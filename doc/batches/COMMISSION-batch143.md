# Commission: batch 143 — Part D, Moore VII: Moore 1919, Theorems E and F

**Go!** This batch runs on top of the batch-142 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch143.md`: this text, also pasted into the prompt.
* `Moore1919EF.lean`: the skeleton.
  * Save it as `HPC/Moore/M19EF.lean`. Splitting it into several files is expected.
  * Add `import HPC.Moore.M19EF` at the end of `HPC.lean`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore 1919 E–F (batch 143)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 142

Audited and accepted.
* **Skeleton and statements.** The skeleton copy is byte-identical, and every statement matches it
  verbatim.
* **Axioms.** `axioms.txt` has 955 lines, with `sorryAx` in none.
* **Theorem C.** The three corrected forms are proved.
* **Theorem D.** It is proved by a new argument: a finite subcover, induction on its size, and at
  each step a curve about the uncovered part that crosses `ABCDA` at every common point. This
  replaces Moore's `J̄` and `J′`. The region form is now unconditional.

The ledger will record:
* Moore's proof of D as defective, with the statement true;
* the choice of `J̄` left undecided, which is acceptable, since the proof does not need it.

## 1. Where this sits

| batch | content |
|---|---|
| 142 | Theorem C corrected; Theorem D (done) |
| **143 (this one)** | 1919 Theorems E and F (and, as a stretch, Schoenflies for Moore's space) |
| 144 | 1919 Theorem G, the nine-cell ruling of Fig. 3, and the final correspondence with the number plane; the end of the 1919 paper |
| 145 | Moore 1925 §I and Theorem 22 |
| 146 | Jones 1955 Theorem 2, with Jones 1949 |

## 2. Items

**A. Theorem E** (p. 176). Moore's proof, following your updated reading plan:
1. Fundamental regions `Gₙ` of subscript greater than `n` about each point of `J + I`. These come
   from Axiom 1's fixed sequence, batch 137's `IsFund`.
2. Theorem D in region form, giving `β₁`.
3. Refinement (`doubleRuling_refine` or `rulable_of_cover`), giving `β₂ ⊇ β₁`, and so on.
4. `ᾱ₂` is the set of all arcs from `BC` to `DA` occurring in some `βₙ`. For a point `P` on no arc
   of `ᾱ₂`, Moore says: *"it can be proved that there exists through `P`, and with endpoints on
   `ABCDA`, just one arc that does not intersect any arc of the set `ᾱ₂`"*.
5. `α₂ = ᾱ₂ ∪ α₂*`, and symmetrically for `α₁`.

Step 4 is the main unargued step. The limit of the nested strips between consecutive arcs has to be
shown to be an arc. The cells shrink, because they lie in fundamental regions of growing subscript
(Axiom 1 (2)).

Three things to establish:
* that the limit is an arc and not merely a continuum;
* that it is unique;
* conditions (3) and (5) for the limit arcs. At points of `ABCDA` that are limits of ends, (3) needs
  a separate argument.

**B. Schoenflies form** (`m19_schoenflies`; stretch). The closed region `ABCDA + interior` is
homeomorphic to the closed square, with sides to sides. It is not in Moore. It is what the nested
rulings of Theorem E give directly: send the dyadic grid of the square to the rulings `βₙ`, and the
mesh tends to 0. Prove it if it comes cheaply from your proof of E, or if E itself is easier to
derive from it. Batch 144 can then use whichever is cleaner for Theorem G and the final paragraph.

**C. Theorem F** (pp. 176–177). Moore's proof uses:
* Theorem 36;
* Theorem 12, giving a finite set `Gₙ` of curves covering the fundamental region `Rₙ`;
* Theorem 42, giving a curve `J′ₙ` enclosing them;
* Theorem 15, giving the arc `A′₁A′₂`;
* "There exists a finite set of curves enclosing `J′₁ + J′₂ + A′₁A′₂`. It follows that there exists
  a closed curve `J₂` enclosing `J′₁`, `R₁`, and `R₂`".

The shape fixes "`Jₙ₊₁` encloses `Jₙ`" as `Jₙ ∪ Iₙ ⊆ Iₙ₊₁`. Check that this is Moore's meaning
("encloses" a set means it lies within the curve).

## 3. Places to check (candidate ledger entries)

1. **Theorem E (3):** "an endpoint either of just one arc of `α₁` or of just one arc of `α₂`". Record
   the reading: exclusive or inclusive. Record also whether a point of a side can be an endpoint of
   an arc of both families. It should not be, since the families have their ends on different pairs
   of sides, except near the corners.
2. **Theorem E, step 4:** quoted above, the main unargued step.
3. **Theorem E, "This process may be continued"** (the sequence `β₁, β₂, …`): record which of your
   lemmas supplies it.
4. **Theorem E proof, its first sentence:** "there exists, about each point `P` of `ABCDA` plus its
   interior, a fundamental region of subscript greater than `n`". This is Axiom 1 (1). Note that
   Theorem D is then applied to a set of regions.
5. **Theorem F:** "It follows, with the aid of Theorem 12, that there exists, for each `n`, a finite
   set `Gₙ` of closed curves such that every point of the fundamental region `Rₙ` is within some
   curve of the set `Gₙ` and every curve of the set `Gₙ` encloses a point of `Rₙ`". This applies
   Theorem 12 to `Rₙ′`. Check that this is what is needed. Also check "There exists a finite set of
   curves enclosing `J′₁ + J′₂ + A′₁A′₂`. It follows that there exists a closed curve `J₂` …":
   Theorem 42 needs the union of the interiors to be connected.

## 4. Deliverables

1. Items A–C.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch143.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 144: Theorem G (pp. 177–178), the nine-cell ruling of Fig. 3, the
     construction of the open curves `kₘ`, `tₙ`, `l_P`, `r_P`, and the final paragraph.

   For the reading plan, say whether the Schoenflies form (if proved) lets the end of the paper be
   done more simply. For example: build a homeomorphism of each closed annulus `Jₙ₊₁ − Iₙ` with a
   square annulus, compatible on the common boundaries. Weigh that against Moore's route through
   open curves and the real line. Say which you recommend.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the
   root.
