# Commission: batch 153 — Part F, Jones 1949 V: Whyburn 1939, Corollary 1

**Go!** This batch runs on top of the batch-152 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch153.md`: this text, also pasted into the prompt.
* `Jones49E.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones49E.lean`. You may split it.
  * Add `import HPC.Jones.Jones49E` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Whyburn 1939 Corollary 1 (batch 153)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 152

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** `whyburn39_local_noncut` and `whyburn39_theorem14` are verbatim.
  `whyburn39_moore_curve` and `whyburn39_curve_from_order_two` take the shapes you chose, which is
  what was asked.
* **Audit.** `axioms.txt` has 1183 lines, with `sorryAx` in none.

**Whyburn 1939 Theorem 14 is verified**, for bounded and unbounded domains, without inversion.
* Your route replaces Whyburn's curves `C` and `K` and his limit continuum `H` with three things: a
  Janiszewski joining lemma, the "no finite order at an accumulation point" lemma, and the
  uncountability of the bad points over the middle third of the annulus, set against `whyburn_3_2`.
* This route is accepted. It is shorter, and it avoids the step whose truth is undecided (`K` with
  `K·M = c + d`).

The ledger counts the inversion gap as the fourteenth defective proof. Whyburn's curve `K` is
recorded as "unargued, not decided, not needed".

## 1. Where this sits

| batch | content |
|---|---|
| **153 (this one)** | Whyburn 1939 Corollary 1 |
| 154 | Jones 1949 Cases 1 and 2; `jones49_theorem1 : Jones49Thm1`; Jones 1955 Theorem 2 and its closing remarks unconditional |

## 2. Items

Follow your batch 152 §8 plan.

**A. `tarc_of_isSimplePolyArc`.**

**B. `exists_tarc_of_locallyConnected`** (the arc theorem for Peano continua).
* It is classical, and the exposition will use it more than once, so prove it in general.
* Use `exists_tarc_of_seq` on chains of small connected open sets, or any shorter route you find.
* Record which route you took.

**C. `accessible_of_cyclic`.** Use `local_join_of_noncut`, polygonal arcs, item A and
`exists_tarc_of_seq`, as in your plan.

**D. `frontier_cyclic`.** Use item C, `jordan_curve_theorem` and `tscc_homeomorph_circle`. Write
out the two-sided construction:
1. two accessing arcs at the cut point `z` of `B`, one from each side;
2. an arc in `R` joining their far ends, trimmed with `TArc.first_point`;
3. a Jordan curve through `z` meeting `M` only at `z`;
4. the parts of `M − z` inside and outside it.

**E. `theta_of_cyclic_peano`** (choose its shape), or the plane route (every point of `B` has order
2, then `menger_order_two`). Your §8 leaves this choice open. Make it after trying both briefly, and
record why.
* For the θ route you need a simple closed curve in a cyclic Peano continuum. Two arcs between two
  points, made disjoint except at their ends, need the absence of cut points and the arc theorem.
* You also need a third arc from a point off the curve, attached at two distinct points. This uses
  the absence of cut points again, together with `TArc.first_point`.

**F. `whyburn39_corollary1`.** If `B` is not a simple closed curve, it contains a θ-curve. The
θ-curve's three complementary domains (`HPC/Moore/Sec6Th26.lean` transported, or
`jordan_curve_theorem` twice) then place `R` in one of them. The open arc that is not on that
domain's boundary has a neighbourhood missing `R`, which contradicts `B = ∂R`. Conclude with
`tscc_homeomorph_circle`.

## 3. Places to check (candidate ledger entries)

1. **Corollary 1 is stated without proof.** Record what the proof uses, and compare it with
   footnote 16's equivalence ("semi-local-connectedness is equivalent to Wilder's property local
   0-avoidability" for cyclic continua). Is that equivalence used? Is it proved anywhere in Whyburn
   1939 ("it follows by the argument given under (6.2)")?
2. **Wilder 1938, Theorem 8a and its first corollary** (p. 196, `doc/sources/wilder1938.pdf`).
   Record whether its statement agrees with Corollary 1. Wilder's proof uses homology and is not to
   be formalized.
3. **Degenerate cases.** If `M` is a single point, "cyclic" fails, because `{z}ᶜ = ∅` is not
   connected. If `M` is a simple closed curve or a closed disk, the conclusion holds. Check that the
   statement needs no nondegeneracy hypothesis beyond cyclicity.

## 4. Deliverables

1. Items A–F.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch153.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 154: Jones 1949 Theorem 1, Cases 1 and 2 (`doc/sources/jones1949.pdf`),
     using the ledger's A.18 list of unargued steps and your batch 148 §(v) plan.

   For the reading plan, say how each step goes with what is now available:
   * Case 1: Baire, and the passage to the boundary of an element of `G` via
     `jordan_curve_theorem`.
   * Case 2:
     * the arc `T`;
     * `C ∩ J ≠ ∅`;
     * "`M − (A + B)` is *not* connected";
     * the local separating point;
     * `jones49_some_order_two`.
   * The final assembly: `jones49_theorem1 : Jones49Thm1`, and the discharge of `h49` in
     `jones55_theorem2` and the closing remarks.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
