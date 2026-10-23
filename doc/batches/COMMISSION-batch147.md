# Commission: batch 147 — Part E, Moore 1925 III: Theorems 13–22. The space of elements is a plane

**Go!** This batch runs on top of the batch-146 delivery. Three files come with it, as separate
uploads:

* `COMMISSION-batch147.md`: this text, also pasted into the prompt.
* `Moore1925III.lean`: the skeleton.
  * Save it as `HPC/Moore/M25C.lean`. You may split it.
  * Add `import HPC.Moore.M25C` at the end of `HPC.lean`.
* `jones1949.pdf`: F. B. Jones, *Note on homogeneous plane continua*, Bull. AMS 55 (1949), 113–114,
  for the batch 148 reading plan. Save it to `doc/sources/`.

The sources for this batch are already in `doc/sources/`: Moore 1925 pp. 422–425, F.A. p. 163, and
Moore 1919.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore 1925 §I, Theorems 13–22 (batch 147)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 146

Audited and accepted.
* **Skeleton and statements.** The skeleton and commission copies are byte-identical. Every statement
  is verbatim. The one exception is `not_m25_theorem7_printed`: its placeholder is replaced by the
  negation of the printed theorem, which is what was asked.
* **Axioms.** `axioms.txt` has 1057 lines, with `sorryAx` in none.
* **Results.** Everything is proved:
  * the three refutations of printed definitions;
  * Mullikin's Theorem 5, refuted as printed and proved in corrected form (by Borsuk's logarithm
    theorem: Stone–Weierstrass and Sard);
  * Moore 1920 Theorem 4, refuted for a one-point set;
  * the cut-point characterizations of the arc and the circle;
  * Theorems 5–12, with the gap in Theorem 11's proof repaired.
* **Ledger.** It now counts nineteen false printed statements and ten defective proofs.
* **A correction to my commission.** Moore 1920's Definition 4 is on p. 342, not p. 340. This is
  recorded as my slip.

Your reading plan for Theorems 13–22 is adopted, including:
* transferring F.A. Theorems 24–27 through their `Gen` forms, with `reg` the restricted regions;
* proving Theorem 19 directly in the plane.

## 1. Where this sits

| batch | content |
|---|---|
| 146 | Theorems 5–12; Mullikin (done) |
| **147 (this one)** | Theorems 13–22: restricted regions; Axioms 1–8 for `S(G)`; **`Quotient r ≃ₜ ℝ²`** |
| 148– | Jones 1955 Theorem 2, with Jones 1949 |

## 2. Items

**A. Infrastructure.**
* `sccInterior`, `sccExterior` (defined like `polyInterior`) and `sccInterior_spec`, which is
  Theorem 11 restated through them.
* `isSCCElt_union`.
* `mooreRegion_of_restricted`.
* `TSCC J ↔ IsSCCElt J`, and F.A.'s `σ.IsSCC` and `σ.IsArc` for `spaceRestricted r` against
  `IsSCCElt`, `IsArcElt`. Through `spaceRestricted_topology` and `isArc_iff_topological` these are
  what Axiom 8 needs. Choose the shapes.

**B. Theorems 13, 14.** Moore's proofs. Theorem 14 rests on "It is easy to see that the sum of the
arcs `pxq` and `pyq` contains as a subset a simple closed curve". Supply it.

**C. Theorems 15–18,** through `Gen.th24` – `Gen.th27` with `reg` the restricted regions, as in your
plan. In particular, record:
* whether Moore's remark that F.A. Theorem 21 "may be easily proved with the help of Theorem 11"
  (p. 423) is right as it stands, or needs Theorem 12 as well (your plan uses 12);
* the reading of `x`, `y` in Theorem 18 (§3, check 4).

**D. Theorem 19.** Prove it directly, as you proposed:
1. a small polygon about `p̄` inside `R̄`;
2. Theorem 3's construction;
3. a simple closed curve of elements extracted from the boundary, with Theorem 14's sub-arc argument.

Record which of Theorems 11, 12, 13, 17 and 18, which Moore cites, the proof actually uses.

**E. Theorem 20 and `spaceRestricted_topology`.**

**F. Theorem 21.**
* Axioms 1, 2, 4, 5 come from `m25_axioms1245` via Theorems 19 and 20.
* Axiom 3 comes from Theorem 11.
* Axiom 8 comes from Theorem 11 and item A.
* Axioms 6′ and 7′ (`m25_axioms6'7'`), "a consequence of Theorems 11 and 13".
* **Axioms 6 and 7** are to be proved *directly* for the restricted regions, with Theorems 15–19 and
  Theorem 7 (cross-cuts of `J` near `P`, inside `R` and inside the exterior respectively).
  * Moore instead writes: "With the aid of results established in my paper *Concerning a set of
    postulates for plane analysis situs* and the fact that every region in the restricted sense is
    the interior of a simple closed curve it easily follows that Axiom 6 and 7 also hold true".
  * Batch 144 established that `m19_plane` is formalized for Σ₁ only.
  * Moore 1919's introduction (p. 169) asserts the plane theorem "for every space `S` that satisfies
    Σ₁ or Σ₂". F.A. p. 163 asserts, without proof, that Σ₁ and Σ₂ are "equivalent with respect to
    point and limit point".
  * So Moore's step to 6 and 7 seems to rest on that unproved equivalence, possibly through a
    Σ₂-version of the 1919 theorem. Read 1919 and record whether anything there is proved for Σ₂
    beyond the assertion. Check 6 of §3 below is this question.

**G. Theorem 22.** Apply `m19_plane` to `spaceRestricted r` (Theorem 21), then transport along
`spaceRestricted_topology` to get `m25_theorem22`. Then prove Moore's limit-preserving form,
`m25_theorem22_moore`, with `isLimitElt_iff`.

**Scope.** If the batch runs short, deliver through Theorem 21 except Axioms 6 and 7. Leave those
two axioms and Theorem 22 open, with their obstruction in `OPEN.md`, rather than weakening any
statement.

## 3. Places to check (candidate ledger entries)

All are transcribed from page images at 200 dpi.

1. **Theorem 13's proof** (p. 422): "if `x` and `y` are any two elements of `R`, `x̄` and `ȳ` are not
   separated from each other by `B̄`", "Hence the set of all those elements of `R` which do not
   belong to `k` is connected. It easily follows that it is a domain." Record them. Record also
   whether the statement's "every element of which (except possibly just one of its end elements)
   belongs to `R`" applies to the single-element case, and whether that matters.
2. **Theorem 14's proof** (p. 423):
   * "Let `p` and `q` denote two distinct elements of the region `R`". This needs `R` to have two
     elements (F.A. Theorem 4 for nonempty `R`).
   * The arc is first called `pq`, then `pxq`, with `x` never introduced.
   * "It is easy to see that the sum of the arcs `pxq` and `pyq` contains as a subset a simple closed
     curve".

   Record each.
3. **Theorems 15–19**: no proofs in the text, only pointers to F.A. Theorems 24–27 and 36. Record what
   each pointer amounts to.
4. **Theorem 18's statement** (pp. 423–424): "(1) either `y` is without `J₁` … or `x` is in the
   exterior of `J₂`, (2) if `y` is without `J₁` then `x` is in the interior of `J₂` …". Here `x` and
   `y` name the arcs `pxq`, `pyq` and are used as elements without being introduced. The skeleton
   reads them as all elements of the arcs other than `p` and `q`. Record whether the condition
   depends on the choice, which it should not, and how F.A. Theorem 27 phrases it.
5. **Theorem 20's proof:** "Since `R` is also a region in the original sense". This is unargued
   (`mooreRegion_of_restricted`).
6. **Theorem 21's proof:**
   * "With the help of Theorems 19 and 20 it is easy to see that these axioms continue to hold"
     (Axioms 1, 2, 4, 5);
   * "That Axiom 3 holds … can easily be seen with the help of Theorem 11";
   * "The truth of Axioms 6′ and 7′ … is a consequence of Theorems 11 and 13";
   * "it easily follows that Axiom 6 and 7 also hold true".

   All four are unargued. Take the last together with item F.
7. **Theorem 22** (p. 425): "follows from Theorems 20 and 21 and the results of" Moore 1919. Record
   that this needs 1919 for Σ₁ only, if item F proves Axioms 6 and 7 directly.
8. **F.A. p. 163:** "though Σ₁ and Σ₂ are not absolutely equivalent, they are equivalent with
   respect to point and limit point" ("It is easy however to show"). This is stated without proof.
   Record it as an F.A. entry; the 1925 route need not use it.

## 4. Deliverables

1. Items A–G.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch147.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 148: Jones 1955 Theorem 2 (`doc/sources/jones1955.pdf`, pp. 738–740),
     with the 1955 ledger's open items (Borsuk-type separation invariance; uncountably many
     complementary domains; `G′` upper semicontinuous; the embedding of `M/G` in `S/G′`).

   For each, say which of batches 136–147 supplies it, and what Jones 1949 (`jones1949.pdf`) must
   contribute.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
