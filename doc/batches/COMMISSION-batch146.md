# Commission: batch 146 — Part E, Moore 1925 II: arcs and closed curves of elements, Theorems 5–12; Mullikin

**Go!** This batch runs on top of the batch-145 delivery. Six files come with it, as separate
uploads:

* `COMMISSION-batch146.md`: this text, also pasted into the prompt.
* `Moore1925II.lean`: the skeleton.
  * Save it as `HPC/Moore/M25B.lean`. You may split it.
  * Add `import HPC.Moore.M25B` at the end of `HPC.lean`.
* Three sources. Save them to `doc/sources/`:
  * `mullikin1922.pdf`: A. M. Mullikin, *Certain theorems relating to plane connected point sets*,
    Trans. AMS 24 (1922), 144–162;
  * `moore1920.pdf`: R. L. Moore, *Concerning simple continuous curves*, Trans. AMS 21 (1920),
    333–347;
  * `moore1924-pcs.pdf`: R. L. Moore, *Concerning the prime parts of certain continua which separate
    the plane*, PNAS 10 (1924), 170–175 ("P.C.S.").

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore 1925 §I, Theorems 5–12 (batch 146)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 145

Audited and accepted.
* **Skeleton and statements.** The skeleton copy is byte-identical, and the commission copy too.
  Every statement is verbatim except `m25_unbounded_unique`, where the closedness hypothesis is
  dropped. That makes the theorem stronger, and it is accepted.
* **Axioms.** `axioms.txt` has 1028 lines, with `sorryAx` in none.
* **Plane facts.** Brouwer's boundary theorem and Janiszewski for compact sets are proved by
  logarithms, with no Jordan curve theorem. Unicoherence of the plane is proved without
  compactness. These are what the exposition needs.
* **Moore's claims.** Theorems 1–4 are proved, and so is the unnumbered p. 420 claim (Axioms 1, 2,
  4, 5 and F.A. Theorem 4). So is `spaceOfElts_topology`.

**One correction to the report** (ledger entry 9). The Math. Z. paper, p. 313, claims "Axioms 1, 2,
4 and **5₁** and Theorem 4 of F. A." The subscript is clear on the 400-dpi image and is lost in
`pdftotext`. Axiom 5₁ (three points) holds in a compact space of prime parts. So the remark that
Axiom 5 "cannot hold there" concerns a claim the paper does not make. Please correct ledger entry 9
of batch 145 in `LEDGER.md` §6, and leave the rest of it as it stands. The 1925 paper does print 5,
without subscript (p. 420, 400-dpi), and `m25_axiom5` proves it.

## 1. Where this sits

| batch | content |
|---|---|
| 145 | 1925 Theorems 1–4, Axioms 1, 2, 4, 5 (done) |
| **146 (this one)** | three refutations of printed definitions; Mullikin's Theorem 5 (refuted as printed, proved corrected); Theorems 5–12 |
| 147 | Theorems 13–21 (restricted regions; Axioms 3, 6′, 7′, 6, 7, 8 for `S(G)`) and Theorem 22: `Quotient r ≃ₜ ℝ²` via `m19_plane` |
| 148– | Jones 1955 Theorem 2, with Jones 1949 |

Your recommendation is adopted. Prove the cut-point characterizations once, for compact metric
continua:
* a cut-point arc is irreducible, hence an embedded `[0, 1]`;
* a continuum with more than one point, disconnected by the omission of any two points, is a circle,
  i.e. the union of two arcs meeting in their ends (Moore 1920 Theorem 4).

Use Mathlib, batch 94's `exists_two_nonCutPoints` and `ArcChar`. Then instantiate them in the
quotient through `quotient_metrizable_plane`. Theorems 5–8 and 10 become short instances. The
plane-specific work is Theorem 9 (via `m25_theorem2` and P.C.S. Lemma 8), Mullikin's theorem (via
the logarithms of `M25Plane.lean`), and Theorem 11.

## 2. Items

**A. Refutations of the printed definitions.** Each uses the decomposition of the plane into points.
Its `MooreDecomp` is immediate, apart from the nonseparation of a point.
1. `not_m25_theorem2_printed`: your example from batch 145 (closed disc; open disc minus a radius;
   plane minus the radius).
2. `not_m25_theorem10_printed` and `not_m25_theorem11_printed`. The printed simple closed curve (p.
   417: "A bounded subset `H` of the set `G` is said to be a simple closed curve … provided it is
   disconnected by the omission of any two of its elements") requires neither closedness nor
   connectedness. Two disjoint segments qualify.
   * Moore 1920's Definition 4 (p. 340), which 1925 cites, reads: "A simple closed curve is a
     closed, connected, and bounded point-set which is disconnected by the omission of any two of its
     points".
   * The skeleton's corrected `IsSCCElt` adds, in addition, that the set be nontrivial. A single
     element satisfies 1920's Definition 4 vacuously, and then Theorem 11 fails. Record whether 1920
     Theorem 4 is false for a one-point set as printed.

**B. Mullikin.**
1. `not_mullikin_theorem5_printed`. "Mutually exclusive connected sets" need not be separated. The
   candidate is `M₁ = M₂` a segment, `K₁` a half-open half of it, and `K₂` the closed other half.
2. `mullikin_theorem5` (with `K₁`, `K₂` closed): the complement of `M₁ ∪ M₂` is exactly two
   domains.
   * **Separation:** the Phragmén–Brouwer / Janiszewski direction, by gluing logarithms across the
     two components of `M₁ ∩ M₂`.
   * **"Just two":** Eilenberg's bound: when neither of two compacta separates the plane, the
     complement of their union has at most as many components as their (nonempty) intersection.
   * Mullikin's own proof (pp. 154–162) uses polygons and Theorem 3. Follow whichever is shorter;
     record which.
   * Record also her Theorem 4 at `M₁ ∩ M₂ = ∅` ("a necessary and sufficient condition … is that
     `M̄` … be not connected"), against her convention for "connected" (her pp. 144–145).

**C. Theorems 5–8** (p. 420), from the cut-point characterization of arcs.
* Theorem 7 is stated with `x` for the printed `p`. `not_m25_theorem7_printed` is optional.
* Theorem 8 has a full proof in the text (pp. 420–421). Follow Moore or batch 94, and record which.

**D. Theorem 9** (p. 421). Moore gives no proof, only "an argument largely similar to that used in
the proof of Lemma 8" of P.C.S. (pp. 173–174, with Theorems 2 and 6). Your reading plan sketches it:
a bounded complementary domain of `pq` would have an outer boundary `K ⊆ pq` with `K − r` connected
for each `r ∈ K` (Theorem 2), while sub-arcs are cut by their interior elements (Theorem 6).

Two further points:
* the case where the complementary domain of `pq` is unbounded but `G − pq` is still disconnected
  must be excluded too; record how;
* record what Lemma 8 of P.C.S. actually argues.

**E. Theorem 10** (p. 421): from the circle characterization.

**F. Theorem 11** (pp. 421–422): Moore's proof, with `not_separatesPlane_ptsOf` and
`mullikin_theorem5`. Check 4 of §3 is a gap in it.

**G. Theorem 12** (p. 422): Moore's proof is complete.

## 3. Places to check (candidate ledger entries)

All are transcribed from page images at 200 dpi.

1. **Theorem 8's proof** (p. 421):
   * "It is easy to see that `K₁ + p` and `K₂ + p` are both closed and connected";
   * "if `q` denotes some element of `K₂`, `K₂ + p` would be a simple continuous arc having `p` and
     `q` as its extremities". This needs `K₂ + p` bounded and `p ≠ q`, and every element other than
     `p`, `q` to disconnect `K₂ + p`, which is the negated supposition.

   Record both.
2. **Theorem 11's proof:**
   * "By Theorem 9 neither `a` nor `b` separates `G` and therefore neither `ā` nor `b̄` separates
     `S`" (`not_separatesPlane_ptsOf`; monotone closed maps pull back connectedness);
   * "It is easy to see that one of these domains (call it `D₁`) is bounded and the other one (`D₂`)
     is unbounded";
   * "Clearly `I` and `E` are domains of elements of `G` and `I + E = G − J`".

   Record each.
3. **Theorem 11's proof:** "In a similar way it may be proved that `J` is also the boundary of
   `E`". Record it.
4. **Theorem 11's proof, the main gap:** "If `B` is not identical with `J` then it is a proper subset
   of `J`. It easily follows, with the help of Theorems 10 and 6, that `B` is a simple continuous arc
   of elements of `G`. But `B` separates `G` and, by Theorem 9, no arc separates `G`."
   * Theorem 6 applies to closed *connected* subsets, and `B` is not shown to be connected.
   * A repair: `B` misses some `x ∈ J`, hence a sub-arc of `J` about `x`. So `B ⊆ A` for an arc `A`
     of `J` (Theorem 10). Then `G − A = I ∪ (E ∪ (J − A))`, and these two sets are separated, since
     `cl I ∩ (J − A) ⊆ B ∩ (J − A) = ∅`. That contradicts Theorem 9 for `A`.

   Confirm or replace.
5. **Theorem 12's proof:** "Since `D₂` is bounded it has at least one boundary element" (true for
   nonempty `D₂`). Record the reading of "domain" as nonempty.
6. **P.C.S. footnote** (1925 p. 421: "In this paper in the statement of Lemma 5 replace the last `M`
   by `K`"). This is Moore's own erratum; record it if Lemma 5 is used.
7. **Moore 1920 Theorem 4** is stated "In a space satisfying Axioms 1′ and 4 of F.A.". Record
   whether your general proof uses only compact metrizability, and whether the 1925 instance needs
   anything else.

## 4. Deliverables

1. Items A–G.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch146.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted, and the batch 145 entry 9 corrected.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 147: Theorems 13–22, pp. 422–425.

   For Theorems 15–19 (proved only by analogy with F.A. Theorems 24–27 and 36), say which of batches
   138–139's proofs transfer. Those proofs assumed Axioms 1–8 for an abstract space, and here only
   the `S(G)` facts proved so far are available. Say also how Axioms 3, 6′, 7′, 6, 7 and 8 will be
   verified for the *restricted* regions of p. 424, and how Theorem 22 is to be obtained from
   `m19_plane` and `spaceOfElts_topology`. The restricted regions give the same topology (Theorem
   20).
4. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   goes at the root.
