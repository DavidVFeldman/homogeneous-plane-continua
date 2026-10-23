Commission read: `doc/batches/COMMISSION-batch147.md` (batch 147, Part E, Moore 1925 III: Theorems 13–22. The space of elements is a plane).

# Report, batch 147

All items A–G are **proved**. Nothing is left open, so `OPEN.md` is unchanged. `lake build HPC`
succeeds with `import HPC.Moore.M25C` at the end of `HPC.lean`. No new file contains `sorry`, and
every new theorem uses only `propext`, `Classical.choice` and `Quot.sound`
(`doc/batches/audits/axioms-batch147.txt`, 73 theorems). `axioms.txt` is regenerated (1091 lines,
`sorryAx` in none; the previous version is kept as `doc/batches/audits/axioms-before-batch147.txt`).
`Axioms.lean` has the new group *Moore 1925 §I, Theorems 13–22 (batch 147)*.

**The space of elements is homeomorphic to the plane** (`m25_theorem22 : Nonempty (Quotient r ≃ₜ ℝ × ℝ)`),
and Moore's limit-preserving form holds (`m25_theorem22_moore`).

**Files.** The skeleton is kept verbatim at `doc/batches/skeletons/Moore1925III.lean` and split as
follows:

| file | content |
|---|---|
| `HPC/Moore/M25CDefs.lean` | the skeleton's definitions, verbatim (`sccInterior`, `sccExterior`, `restrictedRegion`, `spaceRestricted`, `Axiom6'`, `Axiom7'`) |
| `HPC/Moore/TSCCCut.lean` | `Gen.tscc_cut`: two arcs with only their ends in common are cut by any two points (general Hausdorff topology) |
| `HPC/Moore/M25CInt.lean` | item A |
| `HPC/Moore/M25C13.lean` | item B: Theorems 13, 14; `quot_janiszewski`; `exists_tscc_of_arcs` |
| `HPC/Moore/M25C15.lean` | item C: Theorems 15–18 |
| `HPC/Moore/M25C19.lean` | item D: Theorem 19 |
| `HPC/Moore/M25C20.lean` | item E and part of F: Theorem 20, `spaceRestricted_topology`, Axioms 1–5, 8, 6′, 7′ |
| `HPC/Moore/M25C6.lean` | item F: Axioms 6, 7, proved directly |
| `HPC/Moore/M25C.lean` | items F, G: Theorems 21, 22 (umbrella) |

**Statements.** Every skeleton statement is verbatim; no shape was changed. A script compared all 22
skeleton declarations, after whitespace normalization, with the delivered ones.

## The items

**A. Infrastructure.** **Proved.**
* `sccInterior_spec`: Theorem 11 restated through `sccInterior` and `sccExterior`. The two domains
  of Theorem 11 are the components of `Jᶜ` with bounded and with unbounded point set
  (`sccInterior_eq_of_split`).
* `isSCCElt_union`: proved through `Gen.tscc_cut`.
* `mooreRegion_of_restricted`: proved from Theorem 11.
* `isArcElt_iff_tarc` and `isSCCElt_iff_tscc`: Moore's arcs and closed curves of elements are the
  topological ones.
  * One direction: `IsCutArc.exists_embedding` and Theorem 10.
  * The other: `isCutArc_range` and `Gen.tscc_cut`.
* F.A.'s notions for `spaceRestricted r` (`M25C20.lean`): `isArc_restricted_iff` (`σ.IsArc ↔
  IsArcElt`) and `isSCC_restricted_iff` (`σ.IsSCC ↔ IsSCCElt`). Both go through
  `isArc_iff_tarc`/`isSCC_iff_tscc` and `spaceRestricted_topology`.
* The hypotheses of `Gen.th24_*` … `Gen.th27` for the restricted regions:
  * `arcConn_quot` (F.A. Theorem 15);
  * `th21Prop_restricted`;
  * `ax8Prop_restricted`;
  * `isOpen_restricted`, `isPreconnected_restricted`, `ext_restricted`,
    `isCompact_closure_restricted`, `not_isCompact_univ_quot`.

**B. Theorems 13, 14.** **Proved** (`m25_theorem13`, `m25_theorem14`), by Moore's proofs.
* Theorem 13 uses `quot_janiszewski`, which is `janiszewski_compact` transported through `ptsOf`,
  for `k` and the boundary `B` of `R`.
  * `G − k` is connected by Theorem 9 for an arc, and by `isConnected_compl_singleton_quot` for a
    single element.
  * Moore does not argue that `R − k` is nonempty. It follows from `not_subset_arc_of_cut`.
* Theorem 14: Moore's sentence "It is easy to see that the sum of the arcs `pxq` and `pyq` contains
  as a subset a simple closed curve" is supplied by `exists_tscc_of_arcs`. The proof takes first and
  last meeting points along a parametrization, and works in any Hausdorff space.

**C. Theorems 15–18.** **Proved** (`m25_theorem15` … `m25_theorem18`), through `Gen.th24_sub`,
`Gen.th24_ext`, `Gen.th24_disj`, `Gen.th25`, `Gen.th26` and `Gen.th27`, with `reg` the restricted
regions.
* **F.A. Theorem 21 "with the help of Theorem 11"**: right as it stands. `th21Prop_restricted` uses
  Theorem 11 only, not Theorem 12, which the batch-146 plan had proposed.
* **`x`, `y` in Theorem 18**: the condition does not depend on the choice (`diff_subset_int_or_ext`).
  F.A. 27 is phrased with points `C`, `D`. See ledger entry 4.

**D. Theorem 19.** **Proved** (`m25_theorem19`). **Change of route:** the commission asked for the
polygon route (a small polygon about `p̄`, Theorem 3's construction, a closed curve extracted from
the boundary). The proof follows instead the route Moore cites: batch 139's proof of F.A.
Theorem 36, with its correction, carried out in the space of elements. The reason is that Theorems
13, 14 and 18 were already available, and batch 139's proof transferred step by step. The statement
is unchanged. The steps:
1. a closed curve `J` in a small region `Q` about an element `X₀ ≠ O`, by Theorem 14;
2. the arc `OA`;
3. the boundary element `C` and the arc `BC`, by Theorem 13 for `R − OA`;
4. the arcs `AF₁B`, `AH₁B` of `J`, by Theorem 10, and the arc `FZH`, by Theorem 13 for
   `R − (OA + AF₁B + BC)`;
5. Theorem 18 puts `A`, and hence `O`, inside `ZHBFZ`, and Theorem 12 puts that interior in `R`.

**Of Moore's citations (11, 12, 13, 17, 18) the proof uses 11, 12, 13 and 18, not 17.** It also uses
Theorems 10 and 14, which Moore does not cite.

**E. Theorem 20 and `spaceRestricted_topology`.** **Proved.**
* Theorem 19 makes the restricted regions a topological basis of the quotient
  (`isTopologicalBasis_restricted`). Hence `spaceRestricted_topology`, and `m25_theorem20` by
  Moore's two-direction argument with Theorem 4 (`isLimitElt_iff`).
* Also proved: `cl_eq_closure_restricted` and `bdry_restricted`.

**F. Theorem 21.** **Proved** (`m25_theorem21`).
* Axioms 1, 2, 4, 5 (`m25r_axiom1` … `m25r_axiom5`):
  * Axiom 1: a nested sequence of restricted regions about each element, from Theorem 19 and a
    compatible metric;
  * Axioms 2 and 4: Theorem 11 and bounded closures;
  * Axiom 5: batch 145's `m25_axiom5` via Theorem 20.
* Axiom 3 (`m25r_axiom3`): Theorem 11. The complement of the closure of the interior is the
  exterior, which is connected.
* Axiom 8 (`m25r_axiom8`): Theorem 11 with `isSCC_restricted_iff`.
* Axioms 6′ and 7′ (`m25_axioms6'7'`):
  * Axiom 6′ is Theorem 13 for an arc with one end possibly on the boundary.
  * Axiom 7′ is Theorem 11: the boundary of the exterior is `J`.
* **Axioms 6 and 7** (`m25r_axiom6`, `m25r_axiom7`) are **proved directly**, as asked.
  * **Cross-cuts** (`exists_crosscut`): for `P ∈ J` and a Moore region `V₀` about `P`, the
    construction gives elements `a`, `b` of `J` with arcs `X ∋ P` (inside `V₀`) and `Y` of `J`
    between them. It also gives an arc `c` from `a` to `b` in `V₀`, lying (ends excepted) in the
    interior, respectively the exterior, of `J`. Ingredients:
    * Theorem 10;
    * sub-arcs of `J` about `P` (the role of Theorem 7);
    * accessible points (`exists_access`);
    * Janiszewski for `J` and `frontier V₀ + C₂`, whose common part `C₂` is connected.
  * **Axiom 6:** `K` is the interior of `X + c`. Theorem 15 puts `K` in `R`, and Theorem 12 puts it
    in `V₀`. `K̄` is a restricted region about `P` in `V₀ − Y`, by Theorem 19.
  * **Axiom 7:** `L` is the interior of `X + c` for an exterior cross-cut. Theorem 18 gives two
    cases, and the case `Y − a − b ⊆ L` is excluded by choosing `V₀` to miss an element of `J`.
  * Moore's step through Moore 1919 is not used. In particular the Σ₂ case is not used, for which
    1919 proves nothing (ledger entry 6).

**G. Theorem 22.** **Proved.**
* `m25_theorem22` applies `m19_plane` (batch 144, Σ₁) to `spaceRestricted r` with Theorem 21. It
  then rewrites along `spaceRestricted_topology`.
* `m25_theorem22_moore`: the homeomorphism's underlying equivalence preserves limit points in
  Moore's sense. The proof uses `isLimitElt_iff` and `accPt_iff_homeomorph`.

## Ledger entries (`LEDGER.md` §6, new subsection "batch 147")

1. **Theorem 13's proof.**
   * "`x` and `y` any two elements of `R`" must be read as elements of `R − k`.
   * "By Theorem 9" covers arcs only. The single-element case is supplied.
   * Moore does not argue that `R − k` is nonempty. This is supplied.
   * "It easily follows that it is a domain" is confirmed.
   * The clause "every element of which (except possibly just one of its end elements) belongs to
     `R`" applies to the arc only. This does not matter.
2. **Theorem 14's proof.**
   * Two elements of `R` are supplied by F.A. Theorem 4.
   * The arc changes name from `pq` to `pxq`, and the removed element is `r`. This is notation only.
   * The sub-arc sentence is supplied by `exists_tscc_of_arcs`.
3. **Theorems 15–18.** The pointers amount to the F.A. proofs read in the space of elements, with the
   F.A. axioms replaced by Theorem 11 (and Theorem 10, F.A. 15, bounded closures). The F.A. 21
   remark is right as it stands.
4. **Theorem 18, `x`, `y`.** The condition does not depend on the choice. F.A. 27 uses named points
   `C`, `D`.
5. **Theorem 20.** "Since `R` is also a region in the original sense" is supplied by
   `mooreRegion_of_restricted`.
6. **Theorem 21.** The four "easy" claims:
   * Axioms 1, 2, 4, 5: confirmed.
   * Axiom 3: confirmed.
   * Axioms 6′, 7′: confirmed. The `+ A` in Axiom 6′ is idle.
   * Axioms 6, 7: proved directly instead of through Moore 1919.

   Moore 1919 proves nothing for Σ₂ beyond the assertion of its introduction ("In my proof that Σ₁
   is categorical I will make use of the following theorems"). Moore's step rests on F.A. p. 163.
7. **Theorem 22** needs Moore 1919 for Σ₁ only.
8. **F.A. p. 163** (and p. 131): the equivalence of Σ₁ and Σ₂ "with respect to point and limit point"
   is stated without proof. It is recorded as an F.A. entry and is not used.

Further outcomes: Theorem 19's route and the citations it uses; arcs and closed curves of elements
are the topological ones.

## Axioms per theorem

Every theorem below depends exactly on `[propext, Classical.choice, Quot.sound]`. The full list of
all 73 new theorems, every one with these three axioms only, is in
`doc/batches/audits/axioms-batch147.txt`.
* Item A: `sccInterior_spec`, `isSCCElt_union`, `mooreRegion_of_restricted`, `isArcElt_iff_tarc`,
  `isSCCElt_iff_tscc`, `th21Prop_restricted`, `ax8Prop_restricted`, `Gen.tscc_cut`.
* Theorems 13–19: `quot_janiszewski`, `exists_tscc_of_arcs`, `m25_theorem13`, `m25_theorem14`,
  `m25_theorem15`, `m25_theorem16`, `m25_theorem17`, `m25_theorem18`, `m25_theorem19`.
* Theorem 20: `m25_theorem20`, `spaceRestricted_topology`.
* The axioms for the restricted regions: `m25r_axiom1` … `m25r_axiom8`, `m25_axioms6'7'`,
  `isArc_restricted_iff`, `isSCC_restricted_iff`, `exists_crosscut`.
* Theorems 21, 22: `m25_theorem21`, `m25_theorem22`, `m25_theorem22_moore`.

## Reading plan for batch 148: Jones 1955 Theorem 2 (pp. 738–740), with Jones 1949

**The statement** (p. 739). Let `M` be a homogeneous, decomposable, bounded plane continuum, and `G`
the collection of the sets `L_x`. Then `G` is a continuous collection of mutually exclusive continua
filling up `M` such that:
1. "with respect to its elements (as points), `G` is a simple closed curve";
2. "each element of `G` is a homogeneous, bounded, plane continuum which does not separate the
   plane".

**What batch 136 already gives for the abstract `M`:**
* `jones55_usc` and `jones55_continuous`: continuity of `G`.
* `jones55_a`: `M/G` is compact, connected, metrizable, nontrivial, homogeneous and aposyndetic.
* `jones55_elements`: the elements are nondegenerate, pairwise homeomorphic and homogeneous.

The new work places `M` in the plane. For each open item of the 1955 ledger (batch 136 report, "What
Theorem 2 needs beyond Moore's theorem"):

1. **Borsuk-type invariance of plane separation** ("if one element of `G` were to separate `S`, then
   each of them would separate `S`").
   * **Batch 146 supplies both halves of Borsuk's criterion** for plane compacta:
     * `borsuk_exists_log`: complement connected ⇒ every nonvanishing map has a logarithm;
     * `no_log_pow_of_bounded_component`: a bounded complementary component ⇒ `z − x` has no
       logarithm.
   * To write:
     * a disconnected complement of a compact set has a bounded component (two unbounded components
       coincide; this is the point-set form of `m25_unbounded_unique`);
     * transport of logarithms along a homeomorphism `g ≃ₜ g′` (compose with the inverse).
   * The homeomorphisms are `jones55_elements` (batch 136).
   * Jones 1949 contributes nothing here.
2. **Uncountably many complementary domains** ("there would exist uncountably many mutually exclusive
   domains … This being impossible").
   * Elementary; the argument is sketched in the batch 136 report, step 3. Choose for each `g` a
     complementary domain `W_g` missing the connected set `M − g`. Distinct `W_g` are disjoint,
     since boundaries lie in disjoint elements. The plane is second countable.
   * `G` is uncountable because it is a nontrivial connected metrizable compact space (`jones55_a`).
     A short lemma (connected, nontrivial, T₁, regular ⇒ uncountable) may be needed.
   * `M − g` connected is `jones55_claim5` / `jones55_prop_e` (batch 136).
   * Jones 1949: nothing.
3. **`G′` upper semicontinuous** (`G` together with the singletons of `S − M`).
   * Batch 136 supplies the closedness of the `L`-relation on `M` (`isClosed_lSetoid`,
     `isUSCDecomp_of_isClosed`, `jones55_usc`).
   * With `M` closed in the plane, the relation of `G′` is closed in `S × S`.
   * The repository's Moore decomposition (`MooreDecomp`, batch 145) asks for:
     * compact connected elements: the `L_x` are continua (batch 136);
     * non-separating elements: items 1–2;
     * Moore's metric u.s.c.: still to be written. Closed relation plus compact elements gives the
       metric form by a sequence argument, unless batch 145 already has it.
   * Then **batch 147's `m25_theorem22` gives `Quotient G′ ≃ₜ ℝ²`**: "with respect to its elements
     (as points), `G′` is a plane [13]".
   * Jones 1949: nothing.
4. **The embedding of `M/G` in `S/G′`** ("`G` is a compact subcontinuum of `G′`").
   * `M` is closed and saturated, so the induced map `M/G → S/G′` is a continuous injection from a
     compact space into a Hausdorff space, hence a closed embedding.
   * Batch 145 supplies the quotient machinery (`isClosedMap_mk_plane`, `continuous_mk`); batch 147
     supplies the plane.
   * Composed with `m25_theorem22`, `M/G` becomes a compact plane continuum, homogeneous and
     aposyndetic (`jones55_a`, transported).
   * Jones 1949: nothing.
5. **Jones 1949 must contribute its Theorem 1**: "If a compact, plane continuum `M` is both
   homogeneous and aposyndetic, then `M` is a simple closed curve". This is what "Hence by [5]"
   cites; [5] is a slip for [3], as recorded in batch 135. Its proof (p. 113–114) uses:
   * Menger (*Kurventheorie* p. 267): a point of order 2 makes `M` a simple closed curve (with
     homogeneity);
   * that no point separates `M`: from homogeneity and a non-separating point, which batch 108's
     `arcs_corollary2` supplies;
   * Jones 1941 Theorem 4: aposyndetic ⇒ semi-locally connected (batch 136,
     `semiLocConn_of_isAposyndetic`);
   * Wilder/Whyburn: the complementary domains of a semi-locally connected plane continuum are
     simple domains, with boundaries simple closed curves;
   * Case 1 by Baire (the countably many boundary curves, each nowhere dense in `M`);
   * Case 2 by Whyburn, *Analytic Topology* Theorem 9.1 (all but countably many local separating
     points are of order 2).

   None of Menger's order-2 theorem, the simple-domain theorem or Whyburn 9.1 is in the repository.
   **This is the substantive work of batch 148 and beyond.** The final step can use batch 146's
   `circle_char` (a compact connected Hausdorff set disconnected by any two of its points is a
   simple closed curve) in place of Menger, if the order-2 conclusion is reached in that form.
6. **Part (2)** ("does not separate the plane") is items 1–2. Homogeneity of the elements is
   `jones55_elements`.
