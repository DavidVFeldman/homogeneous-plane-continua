# Commission: batch 141 — Part D, Moore V: Moore 1919, double rulings; Theorems C and D

**Go!** Runs on top of the batch-140 delivery. Two files come with it, as separate uploads:

* `COMMISSION-batch141.md`: this text, also pasted into the prompt.
* `Moore1919CD.lean`: the skeleton. Save it as `HPC/Moore/M19CD.lean` and add
  `import HPC.Moore.M19CD` at the end of `HPC.lean`. Splitting it into several files is expected.

The source is `doc/sources/moore1919.pdf`, pp. 172–176.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore 1919 C–D (batch 141)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open;
  * the batch-139 docstring table of `HPC/Moore/FA7.lean`, to mark Theorems 41–43 closed. I authorize
    this edit.

## 0. On batch 140

Audited and accepted. The skeleton copy is byte-identical, every statement is faithful, and
`axioms.txt` has 923 lines with `sorryAx` in none. The following are accepted:

* Theorem 41, Case II, by replacement with chords, with Theorem A giving smallness;
* Theorem 42;
* Theorem 43 (`G` nonempty), via the dual step;
* `m19_B_step` and `m19_D_arc`;
* Theorem A, stated without injectivity, which is a stronger statement;
* Theorem B.

With this, F.A. is complete up to Theorem 43, and nothing is open.

Your reading plan for batch 141 is the basis of this commission.

## 1. Where this sits

| batch | content |
|---|---|
| 140 | F.A. 41–43; 1919 A, B (done) |
| **141 (this one)** | double rulings; the subdivision lemma; 1919 Theorems C and D |
| 142 | 1919 Theorems E, F, G and the final correspondence with the number plane |
| 143 | Moore 1925 §I and Theorem 22 |
| 144 | Jones 1955 Theorem 2, with Jones 1949 |

## 2. Items

**A. Definitions** (skeleton header). These follow the 200-dpi page image of footnote * on p. 172.

* `Quad` is the closed curve `ABCDA` with its four sides.
* `DoubleRuling` departs from the printed text in two ways:
  1. The two rulings may have different numbers of arcs (`n`, `m`). As printed, both are `n`.
  2. The `Y`-arcs are required to be mutually disjoint. As printed, the definition gives only "no
     point in common with `XⱼX′ⱼ` (unless `i = j`)" for the `X`-arcs. It is silent about two
     `Y`-arcs, though the figures and every use assume they are disjoint.
* `cells`, Moore's *subdivisions*, are the components of `I − ⋃ arcs`.

Report whether choice (1) is needed. Check whether Fig. 1 of p. 173 has equally many arcs in the two
rulings (count them), and whether padding to equal numbers is always possible.

**B. The subdivision lemma** (`doubleRuling_cell`, `doubleRuling_cells_ncard`). Moore never states
it, but every later step uses it. The cells are the `(n+1)(m+1)` interiors of the closed curves bounded
by consecutive ruling arcs and sides. Prove it in the form most useful for later work, for instance
with the four-arc boundary of the cell `(i, j)` named. Theorems 24–27 of F.A. are the tools.

**C. Theorem C** (p. 172). Moore gives only an *"Indication of proof"*. It consists of:
* a finite set `K` of chords of `g` that covers `g ∩ I`;
* the three chord types: both ends on one side, ends on adjacent sides, ends on opposite sides;
* one example (Fig. 1), *"given instead of a tedious formal proof covering all possible cases"*.

You must write the proof. Two suggested routes:
* induction on the number of chords;
* first rule so that every chord meets each ruling arc in finitely many points (Theorem B), then
  refine.

The finiteness of `K` should follow from the finiteness of `g ∩ J`.

**D. Theorem D** (pp. 173–176). Follow Moore's proof. Your reading plan lists its parts:
* the finite subcover `g₁ … gₘ`;
* the chain cover `A₁B₁, …, AₙBₙ` of the interval `AB`;
* the points `Eᵢ` and the arcs `EᵢE′ᵢ`;
* the arcs `A₁E′₁, E′₁E′₂, …` from `m19_D_arc`;
* the inner curve `J′` with `4n` points and the arcs of the annulus (Fig. 2);
* Theorem B for the arcs of `α`;
* Theorem C for `ĀB̄C̄D̄` and `g₁`;
* extension across the annulus;
* the induction over `g₂, …, gₘ`.

**E. Refinement** (`doubleRuling_refine`; the shape is left to you). Moore uses it twice without
proof:
* p. 175: "The arcs of these rulings may be extended in such a way that there will result a new
  double ruling `τ₂` of `ABCDA` such that each arc of `τ₁` is also an arc of `τ₂`".
* Theorem E (p. 176): "the arcs of this ruling being so chosen that they can be extended".

State and prove what Theorem D's induction and Theorem E (batch 142) need.

## 3. Places to check (candidate ledger entries)

1. **The double ruling definition** (footnote *, p. 172): equal numbers of arcs, and no disjointness
   of the `Y`-arcs, as in A above.
2. **The subdivisions** are never defined, and the subdivision lemma is never stated (B above).
3. **Theorem C:** "This indication of how a ruling may be constructed in the case of this typical
   example is given instead of a tedious formal proof covering all possible cases." Record the proof
   you supply.
4. **Theorem D, unargued steps.**
   * "There exists a finite set `Ḡ` of closed curves `g₁, g₂, ⋯ gₘ` such that … every point on or
     within `J` is within one of them": Theorem 12 (Heine–Borel).
   * "There exists a set of points `E₁, ⋯ Eₙ₋₁` and arcs `E₁E′₁, ⋯` such that …". Its condition (2)
     reads "`EᵢE′ᵢ` lies within every *region* of the set `Ḡ` that contains `Eᵢ`", although `Ḡ` is a
     set of curves. Record the reading.
   * "It easily follows that there exist (Fig. 2) (1) on `ABCDA`, `4n` points … (2) within `ABCDA`, a
     closed curve `J′` … (3) arcs …". This is the main unargued step.
   * "By the addition of certain arcs … it is possible to continue the arcs of `τ̄` …".
   * "It can be shown in a similar way that there exists a double ruling `τ₃` … This process may be
     continued."
5. **Theorem D's conclusion and its use.** In Theorem E (p. 176) Moore applies Theorem D to a set of
   *regions* (fundamental regions `Gₙ`), not of closed curves. Check whether the curve form suffices
   there: each region contains, by Theorem 36, a curve about each of its points. If it does not, state
   and prove the region form here.

## 4. Deliverables

1. Items A–E.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch141.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, giving the outcome of each check and quoting the
   printed sentence.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 142: Theorem E (p. 176), Theorem F (pp. 176–177), Theorem G and the
     final paragraph (pp. 177–178).
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the
   root.
