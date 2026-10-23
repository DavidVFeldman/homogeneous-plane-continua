# Commission: batch 136 — Part D: decomposition spaces; Whyburn (6.2), (6.21); Jones 1951 Theorem 1; Jones 1955 Theorem 1

**Go!** This batch runs on top of the batch-135 delivery. Four files come with this commission as
separate uploads (no archive):

* `COMMISSION-batch136.md`: this text, also pasted into the prompt.
* `Jones55.lean`: the skeleton. Its `sorry`s are the work items.
  * Save it as `HPC/Jones/Jones55.lean`.
  * Add `import HPC.Jones.Jones55` at the end of `HPC.lean`.
  * Splitting it into several files under `HPC/Jones/` is expected.
* `whyburn1939.pdf`: G. T. Whyburn, *Semi-locally connected sets*, Amer. J. Math. 61 (1939),
  733–749. Save it as `doc/sources/whyburn1939.pdf`.
* `jones1941.pdf`: F. B. Jones, *Aposyndetic continua and certain boundary problems*, Amer. J.
  Math. 63 (1941), 545–553. Save it as `doc/sources/jones1941.pdf`.

`jones1951.pdf` and `jones1955.pdf` are already in `doc/sources/`.

**Rules.**
* You may adjust shapes; record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Jones 1955, decompositions (batch 136)");
  * `README.md` (Part D line, batch count);
  * `LEDGER.md` §6;
  * `OPEN.md`: remove `jones51_theorem1` if you prove it, and add only what is left open.
* Exception: you may move `AposAt` and the other batch-135 definitions from `[MetricSpace X]` to
  `[TopologicalSpace X]` if that is cleaner than `AposAtT` in §1 of the skeleton. Their bodies
  need no metric. If you do, record it, and keep every batch-135 statement compiling unchanged.

## 0. On batch 135

Audited and accepted. Details:

* **Statements.** Every definition is verbatim from the skeleton, and every theorem statement is
  the skeleton's or has hypotheses dropped, as recorded.
* **Audit.** `axioms.txt` has 750 lines, and `sorryAx` appears in none of them.
* **The Lemma.** Your proof of it, by the minimum of a lower semicontinuous function, will go into
  the exposition in place of Jones's transfinite sequence.

**The defects ledger.** It now records two Jones 1948 statements as false at the empty set
(Theorems 6 and 10). It also lists the following as stated without proof: Theorems 0, 2, 3 and 5.

## 1. Where this sits

Jones 1955, Theorem 1 says that any decomposable, homogeneous, compact metric continuum has the
sets `L_x` as the elements of a continuous decomposition. The decomposition space is a homogeneous
aposyndetic continuum, and (c) holds. Theorem 2, in the plane, comes next, after the Moore
decision (notes §168). This batch also closes Jones 1951 Theorem 1, which needs the same two tools.

## 2. Items

**A. Decomposition spaces (skeleton §2), in general form.**

Shapes:
* A decomposition is a `Setoid X` on a compact metric `X`.
* `IsUSCDecomp` is stated with open sets.
* `LSCAt` is "continuity at an element". You may restate it with the Hausdorff metric if that is
  easier. If you do, prove the equivalence.

Items:
* `isClosedMap_mk`, T2, second countability, metrizability.
* `isContinuum_preimage` (monotone decompositions).
* `exists_homeomorph_quotient`.
* `residual_lscAt`. This is the unstated theorem of Jones 1955 (Kuratowski; Fort 1951). One route
  runs through the decomposition space:
  1. For each pair of basic open sets `B ⊆ cl B ⊆ V`, the set of elements meeting `cl B` is
     closed in the quotient.
  2. Discontinuity at an element puts it in the boundary of one such set, for some pair.
  3. That boundary is closed and nowhere dense.
  4. Baire finishes, since the quotient is compact metrizable.

  Any correct route is fine.

**B. Jones 1941 Theorem 4; Whyburn 1939 (6.1), (6.2), (6.21)** (skeleton §3).
* Whyburn's standing hypothesis (p. 737) is metric, connected and semi-locally-connected; here the
  space is also compact.
* (6.2) is the substantive item. Its proof uses the components `Rᵢ` of `M − V_{δᵢ}(x)` and the
  finiteness given by semi-local connectivity.
* `whyburn_6_21` is stated in the form Jones 1951 needs: "cuts" (`CutsPts`) implies "separates".
  Check against the page image that this is what Jones 1951 applies, and record what it is.

**C. Jones 1951, Theorem 1** (skeleton §4; obstruction in `OPEN.md`, batch 135). It needs:
* the quotient `M′` by the decomposition of Jones's proof (item A);
* that `M′` is aposyndetic, so that `M′` is semi-locally-connected (B);
* Whyburn (6.21) in `M′`;
* `arcs_corollary2`, transferred by homogeneity;
* the Lemma.

Transcribe the proof from the page images. Check two things:
* that every use of "hereditarily unicoherent" is on `M`, not on `M′`;
* whether `M′` is shown to be unicoherent or merely used.

**D. Jones 1955, Theorem 1** (skeleton §5). Formalize Jones's proof. Make the numbered claims
(1)–(12) named lemmas, in Jones's numbering:

| claim | content | source / tool |
|---|---|---|
| (1) | `M` is totally nonaposyndetic | when `L_x` is nondegenerate |
| (2) | every point is a cut point | footnote 3: "cut point" = weak cut point; the p. 409 Corollary `totallyNonApos_exists_weakCutPoint` and homogeneity |
| (3) | no point cuts two open sets from each other | `arcs_corollary2` and homogeneity; note Bing's `Cuts` convention (`A ⊄ R`) |
| (4)–(8) | as stated | (8) is the Lemma, `jones51_lemma` |
| (9)–(12) | about `H` and `N_o` | — |

Then come:
* the characterization of `N_o` (with footnote 4);
* the case argument "`N_o + U_o ≠ M`" with `d(q)`, `E_n`, `M₀` and Theorem 6 of 1948;
* `N_o = M − U_o`, so `N_o = L_o` is a continuum (`theorem3`);
* properties (a)–(f) on p. 739;
* upper semicontinuity, then continuity.

The conclusions are `jones55_b`, `jones55_c`, `jones55_usc`, `jones55_continuous`, `jones55_a`
and `jones55_elements`.

You may replace Jones's argument where it fails, or where a different argument is shorter. Record
it when you do, and say which printed sentence the replacement covers.

## 3. Places to check (candidate ledger entries, from my reading of the page images)

1. **The continuity step** ("`G` must be continuous at some one of its elements"): this is item A,
   `residual_lscAt`. Confirm that homogeneity then gives continuity everywhere: a homeomorphism
   permuting the elements preserves continuity at an element.
2. **Conclusion (a) is not argued.** Nothing in the proof says why the decomposition space is
   homogeneous or aposyndetic.
   * *Homogeneous.* `T(L_x) = L_{Tx}`, and `exists_homeomorph_quotient`.
   * *Aposyndetic (my sketch).* Given `g ≠ g′`, take `x ∈ g`, `y ∈ g′`, and a continuum `K`
     containing a neighbourhood `V` of `y`, with `x ∉ K`.
     * By (c), `K` is a union of elements and misses `g`.
     * Its image in the quotient is a continuum missing `g`.
     * Lower semicontinuity at `g′` (`g′` meets `V`) makes that image a neighbourhood of `g′`.

     Check the sketch, or replace it.
3. **"The set `N_o` is closed"** (p. 737): no argument is given. Supply one.
4. **(10) and (11)** use "an uncountable well-ordered monotone decreasing sequence of distinct
   closed subsets of a compact metric space. This being impossible". Prove (11) without
   transfinite recursion if possible, as you did for the Lemma.
5. **`d(q)` is "the *largest* number such that …"** (p. 738). Is the supremum attained? That needs
   a limit argument on the continua `K_o`: a limit continuum irreducible from a limit point `o` to
   `cl V₂`, missing `q`, with `M` not aposyndetic at `q` with respect to it. Also, "`E_n` is
   closed" is unargued. If attainment fails, report whether a "≥ sup − ε" version is enough.
6. **"Since `M₀` is a subset of `M₁`"** (p. 738, Case I). This is my main suspicion.
   * Each `K_o(q)` is irreducible from `o` to `cl V₂`. So `K_o(q) − cl V₂ ⊆ M − V₂ = M₁`.
   * But `K_o(q)` may meet `cl V₂ − M₁ ⊆ V₂`. For instance, if `o ∈ cl V₂` then `K_o(q) = {o}`.
   * Then `M₀ ⊆ M₁` is not justified as written.

   Decide one of:
   * it is true for a reason I miss (record it);
   * the case argument survives with `M₀ ⊆ M₁ ∪ cl V₂`;
   * it needs repair. If so, supply the repair.

   Case II ("`M₂ + M₀` … contains no point of `R_r(p)·R_s(p)`") also deserves a check.
7. **"`M · R_r(p) · R_s(p)`"**: an intersection of two balls about `p`. Check that "every point of
   `K_o(q)` is outside `R_r(p)`" uses `s = 1/n′ − r` as I read it:
   * `q` is within `s` of `p`;
   * `d(K_o(q), q) ≥ 1/n′`;
   * so `d(K_o(q), p) ≥ r`.
8. **"(4) `U_p` is nondegenerate"**: decomposability gives a pair with aposyndesis (Theorem 9);
   homogeneity spreads it; no isolated points.
9. **The first paragraph.** "If for some point `x`, `L_x` is degenerate, then all elements of `G`
   are degenerate and `M` is aposyndetic". Homogeneity gives this. Check that "nondegenerate
   continuous collection" in the conclusion is then the decomposition into points.
10. **Unnumbered remark.** "A compact continuum lying in a regular, semi-metric space or in a Moore
    space is itself a metric space" (p. 736). Not to be formalized; record that it is not used.

## 4. Deliverables

1. Items A–D.
   * Write `#print axioms` for every new theorem to `doc/batches/audits/axioms-batch136.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with its obstruction in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for Jones 1955 Theorem 1, Whyburn 1939 and Jones 1951 Theorem 1.
   It records the outcome of each check in §3, with the printed sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * a list of the Jones 1955 Theorem 1 sentences you replaced, if any;
   * what Theorem 2 will need beyond Moore's theorem. Read p. 739 (Theorem 2 and its proof) and the
     notes I give in §168 of my file, quoted here:
     * the separation step uses Borsuk's theorem (plane separation is a topological invariant of a
       plane compactum);
     * the upper semicontinuity of `G′` is asserted.
4. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   goes at the root.
