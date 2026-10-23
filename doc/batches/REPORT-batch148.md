Commission read: `doc/batches/COMMISSION-batch148.md` (batch 148, Part F, Jones 1955 Theorem 2 (modulo Jones 1949 Theorem 1)).

# Report, batch 148

All items A–G are **proved**, and nothing is left open, so `OPEN.md` is unchanged. `lake build HPC`
succeeds with `import HPC.Jones.Jones55T2` at the end of `HPC.lean`. No new file contains `sorry`,
and every new theorem uses only `propext`, `Classical.choice` and `Quot.sound`
(`doc/batches/audits/axioms-batch148.txt`, produced by `axioms-batch148.lean`). `axioms.txt` is
regenerated (`sorryAx` in no line); the previous version is kept as
`doc/batches/audits/axioms-before-batch148.txt`. `Axioms.lean` has the new group *Jones 1955
Theorem 2 (batch 148)*.

* **The Jordan curve theorem in `ℝ²` is a corollary of Moore 1925 Theorem 11** (`jordan_curve_theorem`),
  resting on `m25_theorem11`, not on `m19_plane`.
* **Jones 1955 Theorem 2 is proved assuming Jones 1949 Theorem 1** (`jones55_theorem2 (h49 :
  Jones49Thm1) …`). Of its conclusions only (1), that `M/G` is a simple closed curve, uses `h49`:
  continuity (`jones55_continuous`, batch 136) and (2) (`jones55_elt_not_separates`,
  `isHomogeneous_Lset`) do not.
* The closing remarks (two complementary domains, indecomposable elements, three domains force
  indecomposability) are proved, also assuming `h49`.

**Uploads.** The commission is at `doc/batches/COMMISSION-batch148.md`. The skeleton is kept verbatim
at `doc/batches/skeletons/Jones55T2-batch148.lean`. Whyburn's *Analytic Topology* is at
`doc/sources/whyburn1942.pdf`. Nothing is left at the root.

**Files.**

| file | content |
|---|---|
| `HPC/Jones/Jones55T2A.lean` | items A–C: `Jones49Thm1`, `not_jones49_theorem1_point`; `tscc_circle`, `jordan_curve_theorem`; `separatesPlane_of_homeomorph`, `countable_of_pairwiseDisjoint_open` |
| `HPC/Jones/Jones55T2D.lean` | items D, E: `uncountable_quotient`, `jones55_compl_connected`, `jones55_compl_continuumwise`, `jones55_elt_not_separates`; `gPrimeRel`, `gPrimeRel_equivalence`, `gPrime`, `isClosedMap_mk_gPrime`, `mooreDecomp_gPrime`, `jones55_plane`, `jones55_embedding_data`, `jones55_embedding`, `isAposyndetic_iff_T` |
| `HPC/Jones/Jones55T2.lean` | items F, G (umbrella): `jones55_circle`, `jones55_theorem2`, `jones55_two_domains`, `jones55_elements_indecomposable`, `jones55_three_domains` |

**Statements.** A script compared all 19 skeleton declarations with the delivered ones, after
normalizing whitespace: every statement is verbatim. **One shape change**: the skeleton's
`countable_of_pairwiseDisjoint_open` does not elaborate as written, because the notation
`Disjoint on U` needs `open Function`. `open Function in` is added before it, and the statement is
otherwise unchanged; the change is recorded at the statement. Docstrings are extended with the
recorded checks.

## Items

**A. Jones 1949 Theorem 1 as a statement: proved.** `Jones49Thm1` carries `K.Nontrivial`.
`not_jones49_theorem1_point`: the printed form fails for `{0}`, which is compact, connected,
homogeneous and vacuously aposyndetic but not homeomorphic to `Circle`. **Convention:** Whyburn,
*Analytic Topology*, Ch. I §10, p. 15: "A compact connected set will be called a continuum". By §8,
p. 13, a single point is connected. One-point continua are therefore continua in Whyburn's
convention, and the printed form is false rather than harmless. Moore 1932 is not in the repository.

**B. `jordan_curve_theorem`: proved.** The proof uses three ingredients:
* `Circle` is a topological simple closed curve: two half-circles `t ↦ exp(±π t)` from `1` to
  `−1` (`tscc_circle`, from `Circle.exp_eq_exp`).
* Topological arcs and closed curves are carried along embeddings (`tarc_image_embedding`,
  `tscc_image_embedding`), so `ptHomeo '' J` is a `TSCC`, and hence an `IsSCCElt` of the
  decomposition into points (`isSCCElt_iff_tscc mooreDecomp_ptSetoid`, batch 147).
* `m25_theorem11` gives two domains of elements, which are pulled back along `ptHomeo`.

*Import chain:* `m25_theorem11` (`HPC/Moore/M25B11.lean`; Mullikin's Theorem 5 by logarithms, and
Moore 1925 Theorems 9 and 10), `isSCCElt_iff_tscc` (`HPC/Moore/M25CInt.lean`) and
`mooreDecomp_ptSetoid` (`HPC/Moore/M25BPts.lean`). Neither `m19_plane` nor `m25_theorem22` is used.
*Axioms:* `[propext, Classical.choice, Quot.sound]`.

**C. Borsuk invariance and countability: proved.**
* `separatesPlane_of_homeomorph`: if `A` separates, some `x ∉ A` has a bounded component
  (`exists_bounded_component_of_separates`). Then `z ↦ z − x` has no continuous logarithm on `A`
  (`no_log_pow_of_bounded_component`, with `a = 1`, `u = 1`). If `B` did not separate, the
  transported function `z ↦ φ⁻¹ z − x` would have one on `B` (`borsuk_exists_log`), and composing
  with `φ` would give one on `A`.
* `countable_of_pairwiseDisjoint_open`: `Set.PairwiseDisjoint.countable_of_isOpen` (the plane is
  separable).

**D. Part (2) and `M − g` connected: proved.**
* `uncountable_quotient`: `M/G` is connected, metrizable and nondegenerate (`jones55_a`). Such a
  space is uncountable, because the distance to a point takes every value in an interval
  (`uncountable_of_connected_metrizable`).
* `jones55_compl_connected` and `jones55_compl_continuumwise`: Jones's "(5)" is claim (5) on
  p. 736. Any two points of `M − L_x = U_x` lie in a continuum missing `x`
  (`exists_continuum_of_mem_aposSet`), and by (c) that continuum misses `L_x`. So `M − g` is
  continuum-wise connected ("strongly connected" follows).
* `jones55_elt_not_separates`, by Jones's argument. In the aposyndetic case the elements are points
  (`Lset_eq_singleton_of_isAposyndetic`). Otherwise:
  * the elements are homeomorphic (`jones55_elements`), so if one separates, all do (item C);
  * `M − g` is connected and lies in one component of `S − g`, so another component `W_g` misses
    `M` (`exists_component_disjoint`).
  * **Disjointness, which Jones does not argue, is supplied:** if `W_g` meets `W_h` (`g ≠ h`), then
    each lies in the other, being a connected subset of the complement of the other's element.
    The closure of `W_g = W_h` adds only points of `g` and of `h`
    (`closure_component_compl_subset`), and `g ∩ h = ∅`, so the set is open and closed in `S`,
    which is absurd.
  * Indexing by `M/G` gives uncountably many disjoint nonempty open sets, against item C.

**E. `G′`: proved.**
* `gPrimeRel_equivalence` is direct.
* `mooreDecomp_gPrime`:
  * The elements are `Subtype.val '' L_x` on `M` and singletons off `M` (`elt_gPrime_of_mem`,
    `elt_gPrime_of_not_mem`). They are compact, connected, and non-separating by item D.
  * **Moore's u.s.c.:** batch 145's `usc_of_isClosedMap` does give it, once the quotient map
    `S → G′` is shown to be closed (`isClosedMap_mk_gPrime`). The saturation of a closed `F` is
    `F ∪ val '' (saturation of val⁻¹' F under G)`, closed by `isClosedMap_mk (jones55_usc hX)` and
    the compactness of `M`.
* `jones55_plane` is `m25_theorem22 (mooreDecomp_gPrime hX hd)`.
* `jones55_embedding` (via `jones55_embedding_data`): the map `M/G → G′` induced by the inclusion
  (`gIncl`) is continuous and injective. Composed with `G′ ≃ₜ ℝ²` it is a closed embedding of the
  compact space `M/G`. Its image `h '' (π '' M)` is compact and connected.
* `isAposyndetic_iff_T` is `Iff.rfl` (`aposAtT_iff`).

**F. `jones55_theorem2`: proved, assuming `h49`.**
* Continuity: `jones55_continuous`.
* (1) `jones55_circle`: `jones55_embedding` gives `K ⊆ ℝ²` with `M/G ≃ₜ K`. `K` is nondegenerate,
  homogeneous and aposyndetic, transported from `jones55_a` along the homeomorphism
  (`IsHomogeneous.of_homeomorph`, `IsAposyndeticT.of_homeomorph`, `isAposyndetic_iff_T`). Then
  `h49 K` applies.
* (2): `isContinuum_Lset`; `isHomogeneous_Lset` (`jones55_elements` outside the aposyndetic case,
  points inside it); and item D.

**G. The closing remarks: proved, assuming `h49`.**
* `jones55_two_domains`: the image of `M` in the plane of elements, `h '' (π '' M)`, is homeomorphic
  to `Circle` by (1). `jordan_curve_theorem` gives `I` and `E`. Their point sets
  `π⁻¹' (h⁻¹' I)` and `π⁻¹' (h⁻¹' E)` are open, connected (`isConnected_ptsOf`, batch 145) and
  disjoint, with union `(π⁻¹' (π '' M))ᶜ = Mᶜ` (`preimage_image_mk_gPrime`).
* `jones55_elements_indecomposable`: **by the commission's first route**. Jones 1951 ([5]) is not
  in the repository. A decomposable element `g` is a homogeneous, decomposable plane continuum
  (`IsDecomposableSpace.of_homeomorph`, `homeoVal`), so by `jones55_two_domains` applied to `g`
  itself its complement is the union of two disjoint nonempty open sets. Then `g` separates the
  plane, against (2).
* `jones55_three_domains`: if `M` were decomposable, `jones55_two_domains` gives `U` and `V`, and
  every complementary component is `U` or `V`. Hence two of `a`, `b`, `c` would have the same
  component. Decomposability is not assumed in the statement, and it is not needed.

## Ledger entries (`LEDGER.md` §6, new subsection "batch 148")

1. "Since each two elements of `g` are homeomorphic": **confirmed misprint** for `G`.
2. "(in fact, by (5), `M − g` is strongly or continuum-wise connected)": (5) is claim (5), p. 736,
   "`p` does not cut any two points of `U_p` from each other". **"Strongly connected" follows**
   (`jones55_compl_continuumwise`).
3. "if one element of `G` were to separate `S`, then each of them would separate `S` … uncountably
   many mutually exclusive domains": **supplied** are Borsuk invariance, the choice of the domains,
   **their disjointness (no argument in Jones)**, the uncountability of `G`, and the countability of
   disjoint domains.
4. "the upper semi-continuous collection `G′`": **u.s.c. unargued; supplied** (closed quotient map,
   then `usc_of_isClosedMap`).
5. "`G′` is a plane [13] and `G` is a compact subcontinuum of `G′`": [13] cites Moore 1932,
   Theorem 19 (p. 340) and Theorem 2 (p. 369), *and* Moore 1925 Theorem 22. **The formalization
   uses the latter.** "Compact subcontinuum" is **unargued; supplied** (`jones55_embedding`).
6. "`G` is homogeneous and aposyndetic. Hence by [5]": this is Theorem 1 (a) (`jones55_a`). Jones
   1949 is applied to the plane copy of `M/G` (item E).
7. Remarks, "each such element is indecomposable": **unnumbered claim; rests on** Theorem 2 (1)
   (hence on `h49`) through `jones55_two_domains`, together with (2).
8. p. 740, the two claims: **unnumbered; both proved assuming `h49`** (`jones55_two_domains`,
   `jones55_three_domains`).
9. **The aposyndetic case**: `L_x = {x}`, `G` is the collection of points, and (1) is Jones 1949 for
   `M`. **Not mentioned by Jones; recorded**, and handled separately in the proofs.

Further entries:
* The Jordan curve theorem comes from Moore 1925 Theorem 11, with no circularity.
* **Jones 1949's reference [8] ("Theorem 9.1, p. 61") is Whyburn's (9.2)**, the "Local separating
  point-order theorem". Whyburn's (9.1) is the lemma that opens its proof; both are on p. 61.
* The shape change of `countable_of_pairwiseDisjoint_open`.

## Axioms

Every theorem of the three new files uses `[propext, Classical.choice, Quot.sound]` or a subset; the
complete list (one line per theorem) is `doc/batches/audits/axioms-batch148.txt`. The theorems of the
skeleton:

| theorem | axioms |
|---|---|
| `not_jones49_theorem1_point` | `[propext, Quot.sound, Classical.choice]` |
| `jordan_curve_theorem` | `[propext, Quot.sound, Classical.choice]` |
| `separatesPlane_of_homeomorph` | `[propext, Quot.sound, Classical.choice]` |
| `countable_of_pairwiseDisjoint_open` | `[propext, Quot.sound, Classical.choice]` |
| `uncountable_quotient` | `[propext, Quot.sound, Classical.choice]` |
| `jones55_compl_connected` | `[propext, Quot.sound, Classical.choice]` |
| `jones55_elt_not_separates` | `[propext, Quot.sound, Classical.choice]` |
| `gPrimeRel_equivalence` | `[propext, Quot.sound, Classical.choice]` |
| `mooreDecomp_gPrime` | `[propext, Quot.sound, Classical.choice]` |
| `jones55_plane` | `[propext, Quot.sound, Classical.choice]` |
| `jones55_embedding` | `[propext, Quot.sound, Classical.choice]` |
| `isAposyndetic_iff_T` | `[propext, Quot.sound, Classical.choice]` |
| `jones55_theorem2` | `[propext, Quot.sound, Classical.choice]` |
| `jones55_two_domains` | `[propext, Quot.sound, Classical.choice]` |
| `jones55_elements_indecomposable` | `[propext, Quot.sound, Classical.choice]` |
| `jones55_three_domains` | `[propext, Quot.sound, Classical.choice]` |

`Jones49Thm1`, `gPrimeRel` and `gPrime` are definitions. In total the three files declare 47
theorems (15 + 23 + 9, counting one generated equation lemma), all with standard axioms only. `axioms.txt` has 1113 lines; the only change
is 22 added lines (the new group), and `sorryAx` occurs in no line.

## Reading plan for batches 149–: Jones 1949 Theorem 1

Source: `doc/sources/jones1949.pdf`, pp. 113–114. The proof is about 25 lines. The ingredients, in
the order Jones uses them:

**(i) Menger, *Kurventheorie*, p. 267 ([4]):** "If a point of `M` is of order 2 in `M`, then `M` is a
simple closed curve" (for homogeneous `M`). This is not available. **A direct argument replaces it**,
ending in `circle_char` (Moore 1920 Theorem 4, `HPC/Moore/CutArc.lean`):
* *Order.* Menger–Urysohn order: `p` has order `≤ n` in `M` if `p` has arbitrarily small open
  neighbourhoods `U` (rel. `M`) whose frontier has at most `n` points. Whyburn's definition
  (*Analytic Topology*, Ch. III §2, p. 48: "order less than or equal to `n` in `M` relative to `G`",
  with `G` the collection of points) agrees. A point of order 2 has order `≤ 2` and not `≤ 1`. Order
  is a topological invariant, so by homogeneity every point has order 2.
* *No cut points.* Moore's non-cut-point theorem (already in the repository), with homogeneity.
* *Every two points separate `M`.* This is the substantive step. Small neighbourhoods with
  two-point frontiers show that each point lies in a small open set `U` with `M − Fr U` disconnected.
  From this one needs: `M` is locally connected (a continuum of finite order at each point is
  regular, hence locally connected); and for `x ≠ y`, `M − {x, y}` is not connected (in a locally
  connected continuum without cut points in which every point has order 2, every two points
  separate). Then `circle_char` gives two cut-point arcs from `x` to `y` with only `x`, `y` in common.
* *A homeomorphism with `Circle`.* `TSCC J → Nonempty (J ≃ₜ Circle)`, by gluing two arcs along their
  ends. This is new: the repository has `TSCC` but no map to `Circle`. Item B of this batch gives the
  converse.

Estimate: one batch (about 600 lines).

**(ii) Jones 1941 Theorem 4 ([5]): aposyndetic ⇒ semi-locally-connected.** Already proved as
`semiLocConn_of_isAposyndetic` (batch 136). "No point of `M` separates `M`" is the non-cut-point
theorem with homogeneity.

**(iii) Wilder 1938 ([6]) and Whyburn 1939 ([7]): "each element of `G` is a simple domain".** In
Whyburn 1939 (`doc/sources/whyburn1939.pdf`) this is **§14, Theorem** (p. 747: "If `M` is a compact
semi-locally-connected plane continuum, the boundary of each complementary domain of `M` is locally
connected") and its **Corollary 1** (p. 749: "If `M` is a compact plane semi-locally-connected cyclic
continuum, the boundary of every complementary domain of `M` is a simple closed curve"). Footnote 16
identifies Corollary 1 with the first corollary of Wilder's Theorem 8a (p. 196), via the equivalence
of s.l.c. with Wilder's local 0-avoidability for cyclic continua. Here "cyclic" means without cut
points, which is item (ii).

Whyburn's proof of the Theorem shows that a complementary domain `R` has Moore's property S and then
quotes Moore (Fund. Math. 3, 1922): the boundary of a domain with property S is locally connected.
The corollary then needs: a locally connected boundary of a complementary domain of a cyclic plane
continuum is a simple closed curve. In the plane, one route is to show that the boundary has no cut
points and is separated by every pair of points, and then apply `circle_char`. Needed: property S,
Moore 1922, and the cyclic step.

Estimate: one to two batches (about 1000 lines).

**(iv) Whyburn, *Analytic Topology*, "Theorem 9.1, p. 61" ([8]):** the statement used is **(9.2)**,
"All save a countable number of the local separating points of any locally compact separable metric
space `L` are points of order 2 of `L`". Its proof uses (9.1) (a separating point of an open `R` is
one of every open `U` with `p ∈ U ⊆ R`) and (8.41) (Ch. III §8: all but countably many separating
points of a locally compact separable metric space are of order 2 relative to … ). (8.41) rests on
Ch. III §§2 and 8: non-separated cuttings, (2.2) and (2.22), (8.4). Jones uses it for `M` itself,
which is compact metric, and only needs "uncountably many local separating points ⇒ one of order 2".

Estimate: one batch (about 600 lines), possibly less by proving only that consequence for compact
metric continua.

**(v) The two cases of Jones's proof** (`M` has no point of order 2; `D` is an element of `G` with
boundary `J`, a simple closed curve).

*Case 1, `M − J` connected.*
* "each point of `M` belongs to some such simple closed curve lying in `M`": the images of `J` under
  homeomorphisms of `M`.
* **Gap (A.18):** "Consequently each point of `M` belongs to the boundary of an element of `G`".
  This passes from "some such simple closed curve" `J′` (with `M − J′` connected) to "the boundary
  of an element of `G`". The **Jordan curve theorem of this batch supplies it**: `M − J′` is
  connected, so it lies in one complementary domain of `J′`. The other domain `D′` misses `M`, and
  its closure adds only points of `J′ ⊆ M`, so `D′` is open and closed in `S − M`. Hence `D′` is a
  component of `S − M`, an element of `G` with boundary `J′`.
* "But `G` is countable": item C.
* Baire: `M = ⋃ J_i`, so some `J_i` has interior in `M`. "Since no point of `M` is of order 2 in `M`,
  each point of `J_i` is a limit point of `M − J_i`": a point of `J_i` with a neighbourhood in `M`
  lying in `J_i` has an arc neighbourhood, hence order 2. This is elementary.

*Case 2, `M − J = H + K` separated.*
* **The arc `T`:** "There exists an arc `T` lying in the complement of `D` which is irreducible from
  `H` to `K`". `H` and `K` lie in the other complementary domain `E` of `J`, which is open and
  connected, hence arcwise connected. Take an arc in `E` from `H` to `K` and its sub-arc irreducible
  from `H` to `K` (`TArc.first_point`). Its interior misses `H`, `K` and `J`, hence `M`.
* **The element `U`:** "Except for its end points, `T` lies in an element `U` of `G`": the interior
  of `T` is connected and lies in `S − M`.
* **`C ∩ J ≠ ∅` (A.18):** the boundary `C` of `U` is a simple closed curve by (iii), lies in `M`, and
  contains both ends of `T` (one in `H`, one in `K`). `C` is connected and `M − J = H + K` is
  separated, so `C` meets `J`. Hence the component `AxB` of `C − C·J` containing `x` is an open arc
  with ends `A`, `B` on `J`.
* **"`M − (A + B)` is *not* connected" (A.18):** Jones gives no argument. `AxB − {A, B}` lies in `H`,
  say. `J ∪ AxB` is a θ-curve: `J` and the cross-cut `AxB`, which lies outside `D`. Batch 138's
  `tscc_theta` and the Jordan curve theorem give the three complementary domains of the θ-curve.
  `M − {A, B}` should split along the two arcs of `J` from `A` to `B`, using that `M` misses `D`
  and the domain bounded by `AxB` and an arc of `J` that meets `U`. This step needs the most care;
  it is the main new plane-topology work of the case.
* "`M − B` is connected" is (ii). Then `A` is a separating point of the open set `M − B`, hence a
  local separating point (Whyburn's definition, p. 61). By homogeneity every point is one, and `M` is
  uncountable, so by (iv) some point has order 2, against the case hypothesis.
* **The conclusion:** in both cases some point has order 2, so by (i) `M` is a simple closed curve.
  This discharges `h49` and makes `jones55_theorem2` and the closing remarks unconditional.

**Size and split.** About 3000–3500 lines in four batches:

| batch | content |
|---|---|
| 149 | (i): order, `TSCC ⇒ ≃ₜ Circle`, a homogeneous continuum with a point of order 2 is a simple closed curve (Menger replaced) |
| 150 | (iii): Moore 1922 (property S), Whyburn 1939 §14 Theorem and Corollary 1 (simple domains) |
| 151 | (iv): Whyburn Ch. III §§8–9, local separating points of order 2 (possibly only the consequence for compact metric continua) |
| 152 | (v): Jones 1949 Cases 1 and 2 (Baire; the arc `T`, `C ∩ J ≠ ∅`, the θ-curve step), `jones49_theorem1 : Jones49Thm1`, and the unconditional Theorem 2 |

Batches 149 and 151 are independent and can be done in either order. Batch 152 needs all three.
