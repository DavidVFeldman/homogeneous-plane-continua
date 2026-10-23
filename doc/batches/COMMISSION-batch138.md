# Commission: batch 138 — Part D, Moore II: F.A. §6, Theorems 20–34

**Go!** This batch builds on the batch-137 delivery. Two files come with it, as separate uploads:

* `COMMISSION-batch138.md`: this text, also pasted into the prompt.
* `MooreFA6.lean`: the skeleton. Its `sorry`s are the work items.
  * Save it as `HPC/Moore/FA6.lean`.
  * Add `import HPC.Moore.FA6` at the end of `HPC.lean`.
  * Splitting it into several files under `HPC/Moore/` is expected.

`moore1916.pdf` is already in `doc/sources/`. The theorems are on pp. 140–150.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore F.A. §6 (batch 138)");
  * `README.md` (the Part D line and the batch count);
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open;
  * the batch-137 ledger subsection, for the one correction in §0 below.

## 0. On batch 137

Audited and accepted.
* The skeleton copy is byte-identical. Definitions and statements match the skeleton, apart from
  the recorded hypotheses: axioms made explicit, `R.Nonempty`, and 5₁ for 5.
* `axioms.txt` has 850 lines, with `sorryAx` in none.
* The four refutations are accepted:
  * Theorem 14 without `Mₙ ≠ ∅`;
  * Theorems 4 and 19 at the empty region, via `withEmpty`;
  * the limit-point criterion at an endpoint.
* The Theorem 15 gap you found and filled ("`P_B` precedes `P`") goes into the ledger and the
  exposition. So do the two "it is clear" steps you supplied.

**One correction to your ledger text.** Check 9 says: "the printed Theorem 5 (3) ('`Rₙ` is a subset
of `R`', no closure) does not supply this". The page image (p. 133, checked at 400 dpi) reads "(3)
if `R` is a region about `P` then there exists `n` such that **`R′ₙ`** is a subset of `R`". The
prime is printed. pdftotext drops primes and overbars, which is the hazard behind the
transcription rule. Please correct the sentence. The skeleton's form of Theorem 5 is the printed
form.

## 1. Where this sits

| batch | content |
|---|---|
| 137 | F.A. §§2–5 (done) |
| **138 (this one)** | F.A. §6, Theorems 20–34: interiors of closed curves, theta-curves, arcs into and out of regions, `R − AB` connected |
| 139 | F.A. §7, only what Moore 1919 and 1925 use |
| later | Moore 1919; Moore 1925 §I and Theorem 22; Jones 1955 Theorem 2 with Jones 1949 |

Moore 1925 cites F.A. Theorems 21, 24, 25, 26, 27 and 36 by number. Moore 1919 cites Theorems 12, 15,
36, 37, 40, 42 and 43. So §6 is needed in full.

## 2. Items

**A. Conventions** (skeleton header and §1).
* `openArc`: Moore's underlined arc, i.e. the arc minus its endpoints.
* `IsInteriorOf`. **"The interior of `J`" is never defined in F.A.** It is used from the proof of
  Theorem 23 on. Prove `existsUnique_interior`: existence by Axiom 8, uniqueness by Theorem 21.
  Record it as an unnumbered gap.
* `SeparatesOn` (p. 140).
* `InOrder`: points of an arc in a given order, via the parametrization of batch 137. If batch
  137's own order or interval API is cleaner, use it instead and record the change.

**B. Theorems 20–34** (skeleton §2). These are Moore's arguments with arcs, closed curves and
regions. Follow his proofs where they are printed: 21, 23–29, 31–34. Supply proofs for the
others:
* 20: "easily proved with the help of Axiom 7";
* 22: "easily proved with the help of Theorem 19, Axioms 2 and 3 and Theorem 20";
* 30: no proof printed.

For each theorem, record the axioms actually used. Batch 137's bridge and arc lemmas are
available. Where Moore's argument is a planar picture (Figs. 1–5), the Lean proof must make every
"it can easily be shown" explicit.

## 3. Places to check (candidate ledger entries)

1. **Interior of a closed curve:** undefined (A above).
2. **Theorem 23** ("No region is a subset of an arc") fails for the empty region. `hne` is added.
   Refute the printed form with `withEmpty`.
3. **Theorem 31:** the order `C E B G D` needs `B` to be distinct from `C` and `D`, which is not
   stated. Check whether `B` an endpoint can be allowed with a modified conclusion. Otherwise
   record it as a tacit hypothesis.
4. **Theorem 32:** "If, in a domain `H`, `AB` is an arc … and `C` is a point in `R`, the interior of
   … then there exists, in `H`, an arc `CB`". Nothing puts `A₁X₁B₁` or `R` (hence `C`) in `H`.
   Determine the intended hypothesis. The skeleton assumes `X₁ ⊆ H` and `R ⊆ H`. Try to weaken
   this to what the proof needs, and refute the literal form if it fails.
5. **Theorem 33:** printed "`R − AB − A)` is connected", with an unbalanced parenthesis; read as
   `R − (AB − A)`. There are two proofs. One (pp. 148–150) covers the case where the boundary of
   `R` is a closed curve; the other (p. 150, "a modification of a proof due to Mr. J. R. Kline")
   covers any region. Formalize the general one, and record whether the special one is needed.
6. **Theorem 34:** printed "If `J` is a Jordan *arc* and `AB` is an arc lying wholly in `R`, the
   interior of `J`". This must be a misprint for closed curve. Prove both the closed-curve form and
   the any-region form (`fa_theorem34_region`). The second proof covers both.
7. **Unargued steps** to supply:
   * Theorem 23: "There exist on `AB` two points `A₁` and `B₁` such that…"; "it must be a subset of
     `A₁OB₁`".
   * Theorem 25: "It is clear that no one of the three sets … contains a limit point of either of
     the other two"; "It can easily be shown that the point-set `FG + GĀ` contains as a subset an
     arc `FH` …"; "It easily follows that `EL − L` is a subset of `Y`".
   * Theorem 26: "It may be easily proved with the assistance of Theorems 17 and 13 that `E`
     contains at least one point which does not belong to …"; "It is clear that `Y` is composed of
     all points that are common to `E`, `E₁`, and `E₂`"; "It can easily be shown that there exist
     points `G₁, G₂, H₁, H₂` …" (footnote: "Cf. proof of Theorem 25").
   * Theorem 32: "It follows (cf. proof of Theorem 31) that `DO` may be covered by a finite set …
     and possibly one additional arc"; "It easily follows that there exists an infinite set of arcs
     …"; "It is easily seen that `B` is a limit point of `CX₁ + CX₂ + ⋯` and that `τ` is connected
     and contains no proper connected subset that contains `B` and `C`".
   * Theorem 33: "The case where one or both of the points `P₁` and `P₂` is on `DE` can be easily
     treated".
   * Theorem 34: "It easily follows that `R − AB` is connected".

   Each supplied step goes into the ledger with the printed sentence quoted.
8. **Degenerate cases.** Watch for empty regions and for arcs at their endpoints, as in batch 137.
   Every "there exists a point `O` of …" is a candidate.

## 4. Deliverables

1. Items A and B.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch138.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for F.A. §6, with the outcome of each check in §3, quoting the
   printed sentence each time. Also make the correction in §0.
3. The report. Its first line names the commission. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * what batch 139 needs from this one: F.A. §7, Theorems 35–43. Read pp. 150–157 for this.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the
   root.
