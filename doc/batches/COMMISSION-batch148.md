# Commission: batch 148 — Part F, Jones 1955 Theorem 2 (modulo Jones 1949 Theorem 1)

**Go!** This batch runs on top of the batch-147 delivery. Three files come with it, as separate
uploads:

* `COMMISSION-batch148.md`: this text, also pasted into the prompt.
* `Jones55T2.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones55T2.lean`. You may split it.
  * Add `import HPC.Jones.Jones55T2` at the end of `HPC.lean`.
* `whyburn-analytic-topology.pdf`: G. T. Whyburn, *Analytic Topology*, AMS Colloquium Publications
  28 (1942). Save it to `doc/sources/`. It is needed only for the batch 149 reading plan
  (Theorem 9.1, p. 61, cited by Jones 1949). Whyburn 1939, *Semi-locally-connected sets*, is already
  in `doc/sources/whyburn1939.pdf`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Jones 1955 Theorem 2 (batch 148)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 147

Audited and accepted.
* The skeleton and commission copies are byte-identical, and all 22 statements are verbatim.
* `axioms.txt` has 1091 lines, with `sorryAx` in none. The audit file records
  `m25_theorem22: [propext, Quot.sound, Classical.choice]`.

**This completes Moore's decomposition theorem: `m25_theorem22 : Nonempty (Quotient r ≃ₜ ℝ × ℝ)`**
for every upper semicontinuous decomposition of the plane into compact, connected, non-separating
continua. It is proved from F.A., Moore 1919 and Moore 1925 §I, with no general Jordan curve theorem
assumed.

Points accepted:
* **Theorem 19.** The change of route is accepted, since it follows Moore's own citation; the
  ledger records which theorems it uses.
* **Axioms 6 and 7.** The direct proof is accepted. The ledger now counts Theorem 21's step through
  Moore 1919 as a defective proof: that step rests on F.A.'s unproved Σ₁/Σ₂ equivalence, and 1919
  proves nothing for Σ₂.
* **Your reading plan for Jones 1955 Theorem 2 is adopted.** This batch carries out items 1–4 and
  part (2). Jones 1949 Theorem 1, which is the substantive remainder, enters as a hypothesis
  (`Jones49Thm1`) and is proved in batches 149–.

## 1. Where this sits

| batch | content |
|---|---|
| 147 | Moore 1925 Theorems 13–22 (done) |
| **148 (this one)** | the plane Jordan curve theorem as a corollary; Borsuk invariance; Jones 1955 Theorem 2 and its closing remarks, assuming Jones 1949 Theorem 1 |
| 149– | Jones 1949 Theorem 1 (Menger's order-2 theorem, simple domains, Whyburn 9.1), discharging the hypothesis |

## 2. Items

**A. Jones 1949 Theorem 1 as a statement.**
* `Jones49Thm1`, with nondegeneracy.
* `not_jones49_theorem1_point`: the printed form fails for a one-point set. Check Jones's footnote 3,
  which says "For other definitions the reader is referred to Moore's book or Whyburn's book".
  Read Whyburn's definition of continuum in *Analytic Topology*, Ch. I. If his continua are
  nondegenerate, record the printed form as harmless instead, and say so.

**B. `jordan_curve_theorem`.** Apply `m25_theorem11` to `ptSetoid` (batch 146), with batch 147's
`isSCCElt_iff_tscc`.
* This makes the general Jordan curve theorem in `ℝ²` a corollary of Moore 1925 and Mullikin, with
  no circularity.
* Record the axioms it uses, and the import chain (it rests on `m25_theorem11`, not on
  `m19_plane`).

**C. Borsuk invariance and countability.**
* `separatesPlane_of_homeomorph`: from `borsuk_exists_log` and `no_log_pow_of_bounded_component`
  (batch 146), as in your plan.
* `countable_of_pairwiseDisjoint_open`: second countability.

**D. Part (2) and `M − g` connected.**
* `uncountable_quotient`.
* `jones55_compl_connected`. Jones calls this clear, and adds "(in fact, by (5), `M − g` is strongly
  or continuum-wise connected)". Use batch 136's `jones55_prop_e` and `jones55_claim5`, and record
  what (5) is.
* `jones55_elt_not_separates`: Jones's argument. If one element separates, all do (item C); a
  complementary domain `W_g` of each `g` missing `M − g` gives uncountably many disjoint domains.
  * Disjointness of distinct `W_g`, `W_h` needs an argument: Jones gives none. Supply it.
  * Handle the aposyndetic case, where the elements are points.

**E. `G′`.**
* `gPrimeRel_equivalence`.
* `mooreDecomp_gPrime`: Moore's metric u.s.c. from the closed relation and compact elements; check
  whether batch 145's `usc_of_isClosedMap` already gives it.
* `jones55_plane`, which is `m25_theorem22`.
* `jones55_embedding`.
* `isAposyndetic_iff_T`.

**F. `jones55_theorem2`,** assuming `h49 : Jones49Thm1`:
* continuity from `jones55_continuous`;
* (1) from `jones55_embedding`, `jones55_a` and `h49`;
* (2) from `jones55_elements` and item D.

**G. The closing remarks** (unnumbered claims; `h49` assumed):
* `jones55_two_domains`. `M/G` is a circle in the plane of elements of `G′`. Batch 147's
  `isSCCElt_iff_tscc` makes it an `IsSCCElt`, and `m25_theorem11` gives two domains of elements.
  Their point sets are the two complementary domains of `M`.
* `jones55_elements_indecomposable`: a decomposable element would have two complementary domains,
  against (2). Alternatively use Jones 1951 (`[5]`: a homogeneous continuum lying in but not
  separating the plane is indecomposable), if the repository has it. Record which.
* `jones55_three_domains`.

## 3. Places to check (candidate ledger entries)

All are transcribed from page images at 200 dpi.

1. **Theorem 2's proof** (p. 739): "Since each two elements of `g` are homeomorphic". The `g` should
   be `G`, a misprint. Confirm it.
2. "It is clear that for each `g` of `G`, `M − g` is connected (in fact, by (5), `M − g` is strongly
   or continuum-wise connected)". Record what (5) is, and whether "strongly connected" follows.
3. "if one element of `G` were to separate `S`, then each of them would separate `S`" (Borsuk:
   unstated) and "there would exist uncountably many mutually exclusive domains (at least one for
   each `g`) in the plane. This being impossible". Record what is supplied: the choice of domains,
   their disjointness, and the uncountability of `G`.
4. "Let `G′` denote the upper semi-continuous collection consisting of `G` together with each
   degenerate subset of `S − M`". The upper semicontinuity of `G′` is unargued.
5. "With respect to its elements (as points), `G′` is a plane [13] and `G` is a compact
   subcontinuum of `G′`."
   * Record that [13] cites Moore 1932 Theorems 19 (p. 340) and 2 (p. 369), *and* Moore 1925
     Theorem 22, and that the formalization uses the latter.
   * Record that "compact subcontinuum" is unargued.
6. "Furthermore, `G` is homogeneous and aposyndetic. Hence by [5], `G` is a simple closed curve."
   * [5] for [3] is already in the ledger.
   * Record that "homogeneous and aposyndetic" is Theorem 1 (a) (`jones55_a`), and that Jones 1949
     needs `G` *in the plane*, which is item E.
7. **Remarks** (p. 739): "Because each element of `G` in Theorem 2 is homogeneous and does not
   separate the plane, each such element is indecomposable." This is an unnumbered claim; record
   what it rests on.
8. **p. 740:** "every decomposable, homogeneous, bounded continuum in the plane must have exactly two
   complementary domains (this follows from Theorem 2)" and "every homogeneous, bounded continuum in
   the plane having more than two complementary domains is indecomposable and of Type 3". These are
   unnumbered claims; record them.
9. **The aposyndetic case.** When `M` is aposyndetic, `L_x = {x}`, `G` is the collection of points,
   and Theorem 2 (1) is Jones 1949 for `M` itself. Jones does not mention the case. Record it.

## 4. Deliverables

1. Items A–G.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch148.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batches 149–: Jones 1949 Theorem 1 (`doc/sources/jones1949.pdf`).

   For the reading plan, take each cited ingredient in turn:
   * Menger, *Kurventheorie* p. 267 (a homogeneous continuum with a point of order 2 is a simple
     closed curve). I do not have it; say whether `circle_char` or a direct argument replaces it, and
     what "order" requires: Menger–Urysohn order, defined by neighbourhoods with boundaries of `n`
     points.
   * Jones 1941 Theorem 4 (`semiLocConn_of_isAposyndetic`, batch 136).
   * Wilder 1938 and Whyburn 1939 ("each element of `G` is a simple domain"). I do not have Wilder;
     Whyburn 1939 is in `doc/sources/`. Locate the theorem used there.
   * Whyburn, *Analytic Topology*, Theorem 9.1, p. 61 (all but countably many local separating points
     are of order 2).
   * The two cases of Jones's proof, with the gaps in A.18 of my ledger: Case 1's passage from "some
     such simple closed curve" to "the boundary of an element of `G`"; Case 2's arc `T`, the element
     `U`, `C ∩ J ≠ ∅`, and "`M − (A + B)` is *not* connected".

   Estimate the size and propose a split into batches.
4. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   goes at the root.
