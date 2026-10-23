# Commission: batch 151 — Part F, Jones 1949 III: crossing continua; Moore 1922 Theorem 4; complementary domains

**Go!** This batch runs on top of the batch-150 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch151.md`: this text, also pasted into the prompt.
* `Jones49C.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones49C.lean`. You may split it.
  * Add `import HPC.Jones.Jones49C` at the end of `HPC.lean`.
  * It restates `moore22_theorem4`, left open in batch 150, verbatim. When it is proved, delete the
    commented copy at the end of `HPC/Jones/Moore22T4.lean` and update `OPEN.md`. Also correct the
    stale sentence in `HPC/Jones/Jones49A.lean`'s module docstring, the one saying that (9.2) and
    `jones49_some_order_two` are open.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `HPC/Jones/Moore22T4.lean` and `HPC/Jones/Jones49A.lean`, only as above;
  * `Axioms.lean` and `axioms.txt` (new group "Crossing continua; Moore 1922 Theorem 4;
    complementary domains (batch 151)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`.

## 0. On batch 150

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** All 13 statements are verbatim. The open one, `moore22_theorem4`, is kept as a
  comment.
* **Audit.** `axioms.txt` has 1155 lines, with `sorryAx` in none.

The results:
* **Whyburn (3.2), (8.4), (8.41), (9.2) and `jones49_some_order_two`** are proved by a single
  theorem for open sets, through separation chains. This closes both items left open in batch 149.
  The route is shorter than Whyburn's, and it avoids (8.2), (8.3) and the non-separated cuttings.
* **Moore 1922 Theorems 1–3** are proved.
* **The PNAS 4 step is reconstructed**, so that paper is not needed.

**Classification.**
* Your new finding on Theorem 4's necessity (`Y_m`, `Y_n` lie in `R`, not `M`) is recorded as a
  *candidate* defective proof. It will be counted once Theorem 4 is verified.
* The same applies to the inversion gap in Whyburn 1939 §14 that your reading plan found. I checked
  it on p. 747. It will be counted once Theorem 14 is verified.

**Your batch 151 proposal is split into three batches,** to keep each one finishable:

| batch | content |
|---|---|
| **151 (this one)** | the sector theorem; Moore's sufficiency in local form; Moore 1922 Theorem 4 in both directions; complementary domains (boundary a continuum, Moore-simply-connected); (6.22) in the §14 form |
| 152 | Whyburn 1939 §14: the F.A. curve `C` in `ℝ²`; the Jordan curve `K` from order 2; Theorem 14 by the local form, with no inversion |
| 153 | Whyburn 1939 Corollary 1: accessibility of boundary points; a θ-curve in a cyclic Peano continuum that is not a circle; boundaries of complementary domains of a cyclic s.l.c. plane continuum are simple closed curves |
| 154 | Jones 1949 Cases 1 and 2; `jones49_theorem1 : Jones49Thm1`; Jones 1955 Theorem 2 and its closing remarks unconditional |

## 1. Items

**A. `sector_theorem`.** Choose its shape. Two disjoint continua crossing a closed annulus cut it
into two pieces, and a connected subset of the open annulus that joins points of different pieces
meets one of them. Prove it together with the cyclic order on the middle circle of infinitely many
disjoint crossing continua. Tools:
* `janiszewski_compact`;
* `plane_unicoherent`;
* `jordan_curve_theorem`;
* the θ-curve theorems of F.A. §6 for arcs, which may need transporting to `ℝ²`.

Record which you use.

**B. `moore22_sufficiency_local`.** Moore's p. 236 argument, with Whyburn's local condition in
place of global property S, and with `exists_crossing_continua` and item A.

**C. `moore22_theorem4`,** both directions.
* Sufficiency is item B, together with batch 150's `isConnected_frontier_of_mooreSimplyConnected`.
* Necessity is Moore's p. 236–237 argument, with your repair of its last step and item A.

**D. Complementary domains.**
* `isConnected_frontier_complDomain`, for bounded and unbounded domains.
* `mooreSimplyConnected_complDomain`, your §5 (b) argument.

**E. `whyburn39_6_22_sec14`,** from `whyburn_6_2` (batch 136) and semi-local connectedness, as in
your §5 (c).

## 2. Places to check (candidate ledger entries)

1. **Moore 1922 p. 236:** "There exists an infinite sequence `B₁, B₂, B₃, …` of distinct points of
   the set `A₁, A₂, A₃, …`, lying in the order `B₁B₂B₃ … BₙBₙ₊₁ …` on the curve `K*`". A monotone
   subsequence on a circle exists, by Ramsey or Bolzano–Weierstrass on angles. Record what the
   proof needs from it, and whether it needs the cyclic order of the *continua* or only that of
   the points.
2. **p. 236:** "a circle with center at `Bₙ` and radius less than `(r − r̄)/4` which neither contains
   nor encloses any point of `kₙ₋₁` or of `kₙ₊₁`". This needs `Bₙ ∉ kₙ₋₁ ∪ kₙ₊₁`; record it.
3. **p. 236:** "Then `R` is not the sum of a finite collection of connected point-sets all of diameter
   less than `ε`". The step from "no connected subset of diameter `< ε` contains two of the `C`s"
   to this is pigeonhole; record it.
4. **The necessity repair** of batch 150. State it in the ledger in the form in which it is proved.
5. **Whyburn 1939 p. 747, the inversion sentence:** confirmed from the page image. Record the
   counterexample (a closed disk) in `LEDGER.md` §6 under this batch, as the text a reader would
   need.

## 3. Deliverables

1. Items A–E.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch151.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 152: Whyburn 1939 §14.

   For the reading plan:
   * Decide whether the F.A. curve `C` is better transported (does `ℝ²` with Jordan-curve regions
     satisfy Axioms 1–8 in the repository?) or built directly.
   * Describe the construction of `K` from order 2.
   * Give the formal shape of Theorem 14: every complementary domain, bounded or not.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
