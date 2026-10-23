*This is the batch-by-batch record that was kept in `README.md` until batch 203, moved here unchanged in batch 204 (except for this line and for long quotations, which batch 204 moved to `doc/sources/transcriptions/`).*

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# HPC — machine-checked Bing 1948, Bing 1951 and Fugate 1966

A Lean 4 / Mathlib formalization of

* R. H. Bing, *A homogeneous indecomposable plane continuum* (Duke Math. J., 1948): Theorems 1–15;
  Theorem 3 as printed, every clause including the only-clause (`theorem3_literal`, through the
  pair form `theorem3_pair`; batch 124); Theorem 4 in the two-link form (`theorem4_two`, outside the
  degenerate case `m = 3`, `r = s`) and the three-link form (`theorem4`); Theorem 4 as printed is
  proved, every clause, for `m ≥ 4` coarse links (`theorem4_literal_ge4`,
  `theorem4LiteralGe4_holds`; batch 125) and false for `m = 3` (degenerate case, and the
  only-clauses with `r < s`, `LEDGER.md` §1); Bing's proof of Theorem 3 is incomplete as
  written and was repaired (`LEDGER.md` §1, REPORT-batch121 to REPORT-batch124);
* R. H. Bing, *Some characterizations of arcs and simple closed curves* (Amer. J. Math., 1948):
  Theorem 5 and Corollary 2;
* R. H. Bing, *Snake-like continua* (Duke Math. J., 1951): Theorems 1–16 as printed, Theorem 6
  with its converse (batch 133), Theorem 2 in Euclidean space of dimension `≥ 2` and in Hilbert
  space. Theorems 6 and 7 are proved outright
  (`HPC.Plane.theorem6_1951`, `HPC.Plane.theorem7_1951`, `HPC/Plane/Enc2.lean`): the facts of
  plane topology they use — the Jordan curve theorem for simple closed polygons, the enclosing
  polygon around a non-separating continuum, and Janiszewski's theorem for polygonal sets, bundled
  as `HPC.Plane.PlaneFacts` — are all proved in the repository (batches 125–131;
  `planeFacts_holds`). Theorem 6 is a corollary of Theorem 7 in the repository. Theorem 7 as
  printed, for tree-like continua, is `theorem7_1951_treeLike`, and Theorem 6 with its converse,
  "tree-like ⇔ no subcontinuum separates the plane", is `isTreeLike_iff_nonseparating`
  (`HPC/Plane/TreeLikeNS.lean`, batch 133; the definition of tree-like was repaired in that batch,
  `LEDGER.md`);
* R. H. Bing, *Concerning hereditarily indecomposable continua* (Pacific J. Math., 1951),
  including Theorem 2 in Euclidean space of dimension `≥ 2` and in Hilbert space;
* G. R. Lehner, *Extending homeomorphisms on the pseudo-arc* (Trans. AMS 98, 1961): Lemma 3 for
  `n = 2`;
* J. B. Fugate, *Decomposable chainable continua* (Trans. AMS, 1966): every numbered statement
  proved, including Corollary 1, which Fugate states without proof (`HPC.Plane.fugate_cor1`,
  batch 132, via the property (∗) of Ingram 1968);
* W. T. Ingram, *Decomposable circle-like continua* (Fund. Math., 1968): Lemma 1 (in the form used),
  Lemma 2 (terminality for a hereditarily unicoherent piece; irreducibility in general), with the
  appeals to Sorgenfrey replaced, and the property (∗) used for Fugate's Corollary 1;
* J. B. Fugate, *A characterization of chainable continua* (Canad. J. Math., 1969): Lemma 3,
  Lemma 4 and Theorem 2, Case II;
* the supporting theorems of S. B. Nadler, *Continuum Theory* (1992) that these use (Moore's
  non-cut-point theorem, Sorgenfrey's theorem 11.22–11.35);
* Part C of the classification project (batch 134): J. van Mill, *A note on the Effros theorem*
  (Amer. Math. Monthly, 2004), §§2–3 — the open mapping principle for a Polish group acting
  transitively on a metric Baire space (`HPC.Effros.effros_open_mapping`), the homeomorphism group
  of a compact metric space as a Polish topological group, and Ungar's corollary for homogeneous
  compacta (`HPC.Effros.effros_homogeneous`, `effros_homogeneous_set`; `HPC/Effros/`);
* Part D, foundations (batch 135): F. B. Jones, *Concerning non-aposyndetic continua* (Amer. J.
  Math., 1948), Theorems 0–19 and the three Corollaries, with Theorems 6 and 10 as printed refuted
  and corrected; and the Lemma of F. B. Jones, *Certain homogeneous unicoherent indecomposable
  continua* (Proc. AMS, 1951) (`HPC.Jones.jones51_lemma`; `HPC/Jones/`); decompositions (batch
  136): upper semicontinuous decompositions of a compact metric space and their decomposition spaces,
  with the residuality of the elements of continuity (`HPC/Jones/Decomp.lean`); Jones 1941 Theorem
  4 and Whyburn 1939 (6.1), (6.2), (6.21) (`HPC/Jones/Whyburn.lean`); Jones 1951 Theorem 1
  (`HPC.Jones.jones51_theorem1`); and F. B. Jones, *On a certain type of homogeneous plane
  continuum* (Proc. AMS, 1955), Theorem 1 with claims (1)–(12) and properties (a)–(f): the sets
  `L_x` of a decomposable homogeneous continuum form a continuous decomposition whose space is a homogeneous aposyndetic continuum
  (`HPC.Jones.jones55_continuous`, `jones55_a`; `HPC/Jones/Jones55*.lean`);
* Part D, Moore I (batch 137): R. L. Moore, *On the foundations of plane analysis situs* (Trans.
  AMS, 1916), §§2–5: the definitions and Axioms 1–8, Theorems 1–19 (Theorem 15 by Moore's nested
  simple chains), with Theorem 14 as printed refuted and the printed Theorems 4 and 19 shown not to
  follow from the axioms (`∅` may be a region); the bridge to topology (the regions form a basis,
  Moore's notions are the topological ones, the space is metrizable); the arc characterization
  (`HPC.Moore.isIrreducibleConnected_iff_arc`), Moore arcs as embedded `[0, 1]`'s
  (`HPC.Moore.isArc_iff`) and the arc facts of pp. 139–140 (`HPC/Moore/`);
* Part D, Moore II (batch 138): Moore 1916, §6, Theorems 20–34, all proved: the interior of a
  closed curve exists and is unique (`HPC.Moore.existsUnique_interior`, unnumbered in F.A.),
  theta-curves (Theorems 24–27, 29, 30), arcs into and out of regions (Theorems 28, 31, 32) and
  `R − AB` connected (Theorems 33, 34, by Kline's proof, for any region); the printed Theorem 23
  shown not to follow from the axioms (`∅` may be a region), a hypothesis added to Theorem 32
  (`HPC/Moore/FA6.lean`, `HPC/Moore/Sec6*.lean`);
* Part D, Moore III (batch 139): Moore 1916, §7, Theorems 35–43: Theorems 35–40 proved (closed
  curves in regions and about points, the interior of Theorem 36 inside the region, the footnote of
  p. 152, Theorems 37 and 38 by a finiteness argument for chords, accessibility of a closed curve
  from both sides: Theorems 39, 40); Theorem 41 proved in Case I and the first sub-case of Case II,
  Theorem 42 proved from Theorem 41 (`HPC.Moore.fa_theorem42_of_41`); the printed Theorem 35 shown
  not to follow from the axioms (`∅` as a region) and the printed Theorem 43 refuted (`G = ∅`);
  Theorem 41 Case II, Theorem 42 and the corrected Theorem 43 left open (`HPC/Moore/FA7.lean`,
  `HPC/Moore/Sec7*.lean`), all closed in batch 140;
* Part D, Moore IV (batch 140): Moore 1916, Theorems 41 (Case II, by replacing a null family of arcs
  of `J₂` by chords of `J₁`), 42 and 43 (corrected: `G` nonempty, through the intersection analogue
  of Theorem 41) proved; Moore 1919, Theorems A and B proved, with the step of Theorem B and the arc
  of footnote * of p. 174 (used in Theorem D) proved without Theorem 43 (`HPC/Moore/M19AB.lean`,
  `HPC/Moore/M19*.lean`, `HPC/Moore/M41*.lean`, `HPC/Moore/M43*.lean`);
* Part D, Moore V (batch 141): Moore 1919, double rulings: the subdivision lemma (the
  `(n+1)(m+1)` subdivisions are interiors of closed curves on the ruling) proved; the refinement step
  of Theorems D and E (`doubleRuling_refine`) and padding to equal numbers of arcs proved; Theorem C
  as printed refuted (a closed curve touching one side from within); Theorem D left open (`OPEN.md`),
  with its region form proved from its curve form (`HPC/Moore/M19CD.lean`, `HPC/Moore/M19CD*.lean`,
  `HPC/Moore/M19CRefute.lean`), closed in batch 142;
* Part D, Moore VI (batch 142): Moore 1919, Theorem C corrected in three forms (finitely many
  disjoint cross-cuts; a closed curve within `ABCDA`; the printed statement for curves touching
  `ABCDA` from within nowhere) and Theorem D, in its curve and region forms, proved by a route
  replacing Moore's (`HPC/Moore/M19CD2.lean`, `HPC/Moore/M19D*.lean`);
* Part D, Moore VII (batch 143): Moore 1919, Theorem F proved (Theorems 36, 15, 42, with the
  interiors made to have connected union before Theorem 42); the nested double rulings `β₁, β₂, …`
  of Theorem E proved; the Schoenflies form (`ABCDA` plus its interior is a closed square, sides to
  sides) proved from the rulings through a general criterion (a compact set carrying two families
  of lines of vanishing mesh is a square, `HPC.Sq.Grid.exists_square`); Theorem E, with (3) read
  exclusively, derived from it (`HPC/Moore/M19EF.lean`, `HPC/Moore/M19E*.lean`,
  `HPC/Moore/M19F.lean`, `HPC/Moore/GridSquare.lean`, `HPC/Moore/GridMesh.lean`);
* Part D, Moore VIII (batch 144): Moore 1919, the end of the paper. **A space satisfying Axioms 1–8
  of F.A. is homeomorphic to the number plane** (`m19_plane`), by the Schoenflies route: the
  Schoenflies form with all four sides prescribed; the closed annulus between nested closed curves is
  a collar of the inner curve (cut into two quadrilaterals by two cross-cuts, in place of Moore's
  unargued nine-cell ruling of Fig. 3); the annulus maps pasted over Theorem F's exhaustion. Theorem
  G, the open-curve property in F.A.'s sense and Moore's final paragraph (the sequential form) are
  proved as corollaries (`HPC/Moore/M19G.lean`, `HPC/Moore/M19G*.lean`);
* Part E, Moore 1925 I (batch 145): upper semicontinuous decompositions of the plane into
  non-separating continua. The space of elements is the quotient (closed map, metrizable; Moore's
  limit elements, domains and boundary are the quotient notions); Theorems 1–4 proved; Brouwer's
  boundary theorem and Janiszewski's theorem for compact sets proved by logarithms, without the
  Jordan curve theorem; **Axioms 1, 2, 4, 5 and F.A. Theorem 4 hold for the space of elements**
  (`m25_axioms1245`), the region topology is the quotient topology, and representative F.A.
  theorems (3, 6, 13, 14, 15) are instantiated (`HPC/Moore/M25A.lean`, `HPC/Moore/M25*.lean`);
* Part E, Moore 1925 II (batch 146): arcs and simple closed curves of elements. The cut-point
  characterizations (a cut-point arc is an embedded `[0, 1]`; Moore 1920 Theorem 4, the circle) are
  proved for compact spaces (`HPC/Moore/CutArc.lean`); **Theorems 5–12 proved** (Theorem 7 with `x`
  for the printed `p`; Theorems 10, 11 for the corrected simple closed curve; Theorem 11 with the gap
  in Moore's boundary step repaired); Borsuk's logarithm theorem for the plane and **Mullikin's
  Theorem 5 (with `K₁`, `K₂` closed)** proved by logarithms; the printed Theorems 2, 7, 10, 11,
  Mullikin's printed Theorem 5 and Moore 1920 Theorem 4 for a one-point set refuted
  (`HPC/Moore/M25B.lean`, `HPC/Moore/M25B*.lean`, `HPC/Moore/Borsuk.lean`, `HPC/Moore/Mullikin*.lean`);
* Part E, Moore 1925 III (batch 147): **Theorems 13–22 proved**. Moore's arcs and simple closed
  curves of elements are the topological ones; Theorems 15–18 through batch 138's topological forms
  of F.A. 24–27; Theorem 19 by the route of F.A. 36; with the restricted regions (interiors of
  simple closed curves of elements) **Axioms 1–8 of F.A. hold** (Theorem 21; Axioms 6 and 7 proved
  directly, without Moore's appeal to Moore 1919 for Σ₂), and **the space of elements is
  homeomorphic to the plane** (`m25_theorem22`, with Moore's limit-preserving form
  `m25_theorem22_moore`) (`HPC/Moore/M25C.lean`, `HPC/Moore/M25C*.lean`, `HPC/Moore/TSCCCut.lean`);
* Part F, Jones 1955 Theorem 2 (batch 148): **the Jordan curve theorem in `ℝ²`** as a corollary of
  Moore 1925 Theorem 11 (`HPC.Jones.jordan_curve_theorem`); Borsuk invariance of plane separation
  for compacta; the decomposition `G′` of the plane satisfies Moore's hypothesis and is a plane;
  **Jones 1955 Theorem 2 and its closing remarks proved assuming Jones 1949 Theorem 1** (the
  hypothesis `Jones49Thm1`; Theorem 2 (2) and the continuity of `G` without it); Jones 1949 Theorem 1
  as printed refuted for a one-point continuum (`HPC/Jones/Jones55T2.lean`,
  `HPC/Jones/Jones55T2A.lean`, `HPC/Jones/Jones55T2D.lean`);
* Part F, Jones 1949 I (batch 149): the order of a point and its invariance; **a topological simple
  closed curve is homeomorphic to `Circle`** (`HPC.Jones.tscc_homeomorph_circle`); **Menger's
  theorem: a nondegenerate compact metric continuum all of whose points have order 2 is a circle**
  (`HPC.Jones.menger_order_two`), and its homogeneous form used by Jones 1949
  (`HPC.Jones.jones49_order_two`); Whyburn's (9.1) (`HPC.Jones.whyburn_9_1`); Whyburn's (9.2) and
  `jones49_some_order_two` left open (`OPEN.md`), the latter reduced to the former
  (`HPC/Jones/Jones49A.lean`, `HPC/Jones/Jones49Order.lean`, `HPC/Jones/Jones49Circle.lean`,
  `HPC/Jones/Jones49Menger.lean`, `HPC/Jones/Jones49Why.lean`);
* Part F, Jones 1949 II (batch 150): **all but countably many separating points of an open set of a
  locally compact separable metric space are of order 2** (`HPC.Jones.countable_sepPoint_not_hasOrder_two`),
  hence Whyburn's (3.2) for continua, (8.4), (8.41), **(9.2)** and **`jones49_some_order_two`**
  (`HPC/Jones/Jones49Chain.lean`, `HPC/Jones/Jones49Sep.lean`, `HPC/Jones/Jones49B.lean`); Moore 1922,
  *Concerning connectedness im kleinen and a related property*, Theorems 1–3 (`HPC/Jones/Moore22.lean`);
  Theorem 4 left open (`OPEN.md`), with the boundary shown to be a continuum and the cited PNAS step
  reconstructed (`HPC/Jones/Moore22T4.lean`);
* Part F, Jones 1949 III (batch 151): **the sector theorem** — two disjoint continua crossing a
  square annulus cut it into two pieces — and **the cyclic order** of infinitely many disjoint
  crossing continua (`HPC.Jones.sector_theorem`, `HPC.Jones.sector_cyclic_order`); **Moore's
  sufficiency in Whyburn's local form** (`HPC.Jones.moore22_sufficiency_local`) and **Moore 1922,
  Theorem 4**, both directions (`HPC.Jones.moore22_theorem4`); the boundary of every complementary
  domain of a plane continuum is a continuum, and a bounded one is simply connected in Moore's sense
  (`HPC.Jones.isConnected_frontier_complDomain`, `HPC.Jones.mooreSimplyConnected_complDomain`);
  Whyburn 1939 (6.22) in the §14 form (`HPC.Jones.whyburn39_6_22_sec14`)
  (`HPC/Jones/Jones49CStrip.lean`, `HPC/Jones/Jones49COrder.lean`, `HPC/Jones/Jones49CAnn.lean`,
  `HPC/Jones/Jones49CMoore.lean`, `HPC/Jones/Jones49C.lean`);
* Part F, Jones 1949 IV (batch 152): **Whyburn 1939, Theorem 14** — the boundary of every
  complementary domain of a compact semi-locally-connected plane continuum is locally connected
  (`HPC.Jones.whyburn39_theorem14`), with Whyburn's step 3 at non-cut points
  (`HPC.Jones.whyburn39_local_noncut`), the joining lemma replacing Moore's curve
  (`HPC.Jones.whyburn39_moore_curve`, by Janiszewski's theorem) and the no-finite-order lemma
  replacing the curve `K` (`HPC.Jones.whyburn39_curve_from_order_two`); no inversion
  (`HPC/Jones/Jones49DSep.lean`, `HPC/Jones/Jones49DCross.lean`, `HPC/Jones/Jones49D.lean`);
* Part F, Jones 1949 V (batch 153): **Whyburn 1939, Corollary 1** — the boundary of every
  complementary domain of a compact semi-locally-connected cyclic plane continuum is a simple closed
  curve (`HPC.Jones.whyburn39_corollary1`), with simple polygonal arcs as arcs
  (`HPC.Jones.tarc_of_isSimplePolyArc`), **the arc theorem for Peano continua**
  (`HPC.Jones.exists_tarc_of_locallyConnected`, and for connected open subsets
  `HPC.Jones.exists_tarc_in_open`), accessibility of boundary points (`HPC.Jones.accessible_of_cyclic`),
  cyclicity of the boundary (`HPC.Jones.frontier_cyclic`, by Janiszewski's theorem), θ-curves in cyclic
  Peano continua (`HPC.Jones.theta_of_cyclic_peano`) and the θ-curve lemma
  (`HPC.Jones.theta_not_subset_closure`) (`HPC/Jones/Jones49EArc.lean`, `HPC/Jones/Jones49ETheta.lean`,
  `HPC/Jones/Jones49EAcc.lean`, `HPC/Jones/Jones49EPlane.lean`, `HPC/Jones/Jones49E.lean`);
* Part F, Jones 1949 VI (batch 154): **Jones 1949, Theorem 1** — a nondegenerate homogeneous
  aposyndetic compact plane continuum is a simple closed curve (`HPC.Jones.jones49_theorem1 :
  Jones49Thm1`), through Case 1 (`HPC.Jones.jones49_case1`: Baire) and Case 2
  (`HPC.Jones.jones49_case2`: a local separating point), with the separation of `M − (A + B)` proved
  by a θ-curve argument (`HPC.Jones.theta_separation`, from `HPC.Jones.theta_no_common_side`:
  Jordan curve theorem and Janiszewski's theorem); **Jones 1949, Theorem 2** (nondegenerate form,
  `HPC.Jones.jones49_theorem2`; the printed form refuted for a point,
  `HPC.Jones.not_jones49_theorem2_point`); **Jones 1955 Theorem 2 and its closing remarks without
  hypothesis** (`HPC.Jones.jones55_theorem2'`, `HPC.Jones.jones55_two_domains'`,
  `HPC.Jones.jones55_elements_indecomposable'`, `HPC.Jones.jones55_three_domains'`)
  (`HPC/Jones/Jones49FTheta.lean`, `HPC/Jones/Jones49FLocal.lean`, `HPC/Jones/Jones49FCase1.lean`,
  `HPC/Jones/Jones49FCase2.lean`, `HPC/Jones/Jones49F.lean`);
* Part E, Hagopian 1975 I (batch 155): **Moore's triod theorem** — the plane contains no
  uncountable family of mutually disjoint triods (`HPC.Hagopian.moore_triod_theorem`, by Moore's two
  cases with an interlacing lemma proved from Janiszewski's theorem); Moore 1962 Theorems 135–139 on
  composants; **Hagopian 1975, Lemmas 1–4** (`HPC.Hagopian.hagopian75_lemma1`: a homogeneous
  indecomposable plane continuum is atriodic and hereditarily unicoherent;
  `HPC.Hagopian.hagopian75_lemma2`, through Kuratowski §48; `HPC.Hagopian.hagopian75_lemma3` and
  `HPC.Hagopian.hagopian75_lemma3_unique` in the type A′ form; `HPC.Hagopian.hagopian75_lemma4`);
  Theorem 1, paragraphs 1–3 and 5–13 (`HPC.Hagopian.hagopian75_exists_typeA'`,
  `HPC.Hagopian.hagopian75_layer_invariant`, `HPC.Hagopian.hagopian75_layer_homogeneous`,
  `HPC.Hagopian.indecomposable_of_unicoherent_homogeneous`) and Theorem 1 with paragraph 4 as a
  hypothesis (`HPC.Hagopian.hagopian75_theorem1_of_layer`); two skeleton statements refuted
  (`HPC.Hagopian.not_admissible_end_sets`, `HPC.Hagopian.not_arc_of_degenerate_layers`)
  (`HPC/Hagopian/`).
* Part E, Hagopian 1976 I (batch 156): **Hagopian 1976, §2**, Lemmas 2, 3 and 8
  (`HPC.Hagopian.hagopian76_lemma2`, `HPC.Hagopian.hagopian76_lemma3` as printed,
  `HPC.Hagopian.hagopian76_lemma8`), the end sets (`HPC.Hagopian.hagopian76_end_sets`), Lemma 4's
  linear order (`HPC.Hagopian.hagopian76_lemma4_chain`), its first paragraph in corrected form
  (`HPC.Hagopian.hagopian76_lemma4_layers'`) and its sequence form given "no maximal element"
  (`HPC.Hagopian.hagopian76_lemma4_seq_of_noMax`). Theorem 1 is stated as `Hagopian76Thm1`, and
  from it are derived 1976 Theorem 2 (`HPC.Hagopian.hagopian76_theorem2`), Hagopian 1975 Theorem 1,
  Corollary and Theorem 2 (`HPC.Hagopian.hagopian75_theorem1`, `HPC.Hagopian.hagopian75_corollary`,
  `HPC.Hagopian.hagopian75_theorem2`) and Bing 1960 for plane continua
  (`HPC.Hagopian.bing60_plane`). Lemma 4 as printed and its sequence form are proved
  (`HPC.Hagopian.hagopian76_lemma4`, `HPC.Hagopian.hagopian76_lemma4_seq`), with the step Hagopian
  leaves unargued ("no maximal element") supplied (`HPC.Hagopian.exists_proper_extension`,
  `HPC.Hagopian.ext_of_branch`). Lemma 4's first paragraph as printed and Lemmas 5–7 are open,
  commented out, and listed in `OPEN.md` (`HPC/Hagopian/`).
* Part E, Hagopian 1976 II (batch 157): **no proper subcontinuum of a homogeneous indecomposable
  plane continuum separates the plane** (`HPC.Hagopian.no_proper_subcontinuum_separates`; the
  invariance step is supplied by `HPC.Hagopian.exists_separating_subcontinuum_of_homeomorph`, from
  logarithms and Bing's Theorem 6, without Borsuk's theorem); the set-up of Theorem 1: the relation
  `S` satisfies Moore 1925's hypotheses (`HPC.Hagopian.layerSetoid_mooreDecomp`), the quotient map
  onto the plane and the arc `π[E]` (`HPC.Hagopian.exists_quotient_plane`), an accessible point in an
  interior layer (`HPC.Hagopian.exists_accessible_typeA'`); Lemma 5 at the layers other than the end
  sets and its reduction to the end sets (`HPC.Hagopian.hagopian76_lemma5_interior`,
  `HPC.Hagopian.hagopian76_lemma5_usc`, `HPC.Hagopian.hagopian76_lemma5_of_ends`); the first
  paragraph of Lemma 4 shown equivalent to the exclusion of the swallowed-layer configuration
  (`HPC.Hagopian.hagopian76_lemma4_layers_of_no_swallowed`,
  `HPC.Hagopian.hagopian76_no_swallowed_of_lemma4_layers`). D1, Lemma 5 at the end sets, the
  two-sided extension, Lemmas 6–7 and the unnumbered claims are open, commented out, and listed in
  `OPEN.md` (`HPC/Hagopian/Hagopian76B.lean`).
* Part E, Hagopian 1976 III (batch 158): **the first paragraph of Lemma 4 (D1) in the strong form**
  — an extension `F` of `E` away from `k⁻¹(0)` has `E` as an initial segment `d⁻¹[[0, s]]`, and every
  layer of `E` is a layer of `F` (`HPC.Hagopian.hagopian76_far_layer`,
  `HPC.Hagopian.hagopian76_initial_segment`, `HPC.Hagopian.hagopian76_lemma4_layers`,
  `HPC.Hagopian.hagopian76_no_swallowed_layer`), by lower semicontinuity of the larger continuum;
  **Lemma 5** (`HPC.Hagopian.hagopian76_lemma5`: the decomposition of `E` is continuous);
  **Moore 1962, Theorem 28** (`HPC.Hagopian.moore62_theorem28`, via an exterior arc and Janiszewski's
  theorem); the arc `π[E]` with its parametrization (`HPC.Hagopian.exists_quotient_plane'`) and the
  definitions of Lemma 9 (`AbutSameSide`, `DecompAccessible`). The two-sided extension (not needed),
  Lemmas 6, 7, 9 and the unnumbered claims are open, commented out, and listed in `OPEN.md`
  (`HPC/Hagopian/Hagopian76C.lean`).
* Part E, Hagopian 1976 IV (batch 159): **the Schoenflies theorem in the plane** with one side
  prescribed (`HPC.Hagopian.plane_schoenflies`: Moore 1919's theorem for the restricted regions of the
  plane, transported along `ptHomeo`), the **cross-cut theorem** in the plane
  (`HPC.Hagopian.plane_split`), **every arc lies on a simple closed curve**
  (`HPC.Hagopian.TArc.exists_closing_arc`), **every arc has a two-sided collar**
  (`HPC.Hagopian.exists_collar`, glued from a Schoenflies half-collar and one obtained by inversion),
  and **Lemma 8 with prescribed caps** (`HPC.Hagopian.hagopian76_lemma8_caps`); the collar form of
  "decomposably accessible" (`DecompAccessibleC`). Lemmas 6, 7, 9 and the unnumbered claims are open,
  commented out, and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76D.lean`).
* Part E, Hagopian 1976 V (batch 160): **Lemma 6** (`HPC.Hagopian.hagopian76_lemma6`: `Cl R(E)` is
  indecomposable; with `hagopian76_lemma6_X` and `hagopian76_closure_extUnion`), via an *absorption*
  lemma (a continuum missing `X` that meets an extension away from `X` lies in `R(X, E)`), which makes
  Hagopian's steps 6–7 unnecessary, and step 8 from the 1975 ¶2 argument without homeomorphisms; the
  two unnumbered claims (`HPC.Hagopian.hagopian76_Rset_composant`: `R(E)` is a composant of
  `Cl R(E)`; `HPC.Hagopian.hagopian76_essential_typeA'`: essential continua are of type A′);
  **Schoenflies with two adjacent sides prescribed** (`HPC.Hagopian.plane_schoenflies₂`); upper
  semicontinuity in metric form (`HPC.Hagopian.layer_nbhd_small`). Lemmas 7 and 9 are open, commented
  out, and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76E.lean`).
* Part E, Hagopian 1976 VI (batch 161), the set-up of Theorem 1: **`ε₁`**
  (`HPC.Hagopian.hagopian76_eps1`, with the families used recorded in `IsEps1`; the chain of
  `ε₁`-neighbourhoods of the elevenths follows every `h[E]`, `hagopian76_eps1_chain`, which needs a
  family not among Hagopian's four); **the chain `{Gᵢ}`, its refinement `L`, and Property 1**
  (`HPC.Hagopian.hagopian76_chain11`, `HPC.Hagopian.hagopian76_property1`); the first sentence of T9
  (`HPC.Hagopian.hagopian76_T9`, for any `D` with the property it uses); the step "By Lemmas 2 and 3"
  of Property 3 (`HPC.Hagopian.hagopian76_property3_shift`); the triod of Lemma 7
  (`HPC.Hagopian.hagopian76_lemma7_triod`) and **Lemma 7 reduced** to the existence of the continuum
  `F` for two points in one composant of `Cl R(E)` (`HPC.Hagopian.hagopian76_lemma7_of_F`). T11,
  Property 3, Lemmas 7 and 9 are open, commented out, and listed in `OPEN.md`
  (`HPC/Hagopian/Hagopian76F.lean`).
* Part E, Hagopian 1976 VII (batch 162): **half-ray density** (`HPC.Hagopian.halfray_dense`: for
  a continuum `G` essential to `R(E)` and an interior layer `d⁻¹(u)` of `G`, the extensions of each
  half of `G` away from `d⁻¹(u)` are dense in `Cl R(E)`; they meet only in `d⁻¹(u)`,
  `HPC.Hagopian.halfray_inter`), from `Cl R(G) = Cl R(E)` for essential `G`
  (`HPC.Hagopian.closure_Rset_essential`) and the fact that every minimal admissible map of a piece
  `d⁻¹[[a, b]]` has end layers `d⁻¹(a)`, `d⁻¹(b)` (`HPC.Hagopian.piece_end_layers`); **Lemma 7**
  (`HPC.Hagopian.hagopian76_lemma7`), with Hagopian's continuum `F` taken on the half-ray that
  misses `t`; **Property 2** (`HPC.Hagopian.hagopian76_property2`), from Lemma 7. Lemma 9, T6–T8,
  T9 in full, T11 and Property 3 are open, commented out, and listed in
  `OPEN.md` (`HPC/Hagopian/Hagopian76G.lean`).
* Part E, Hagopian 1976 VIII (batch 163), the collar geometry: an **adapted collar**
  (`HPC.Hagopian.exists_collar_adapted`: a collar of the arc `γ` whose vertical below `γ y` runs
  along a given arc ending at `γ y`); **no point of `π[M]` just below `π[E]`**
  (`HPC.Hagopian.no_M_below`: Lemma 9's argument run for any point, with collar rectangles, boundary
  bumping and freeness in place of Moore's Theorem 28); **Lemma 9**
  (`HPC.Hagopian.hagopian76_lemma9`, without the hypothesis "not decomposably accessible");
  **T3** at interior points and **T6** (`HPC.Hagopian.hagopian76_T3`, `HPC.Hagopian.hagopian76_T6`).
  T7 and the steps waiting on it (T8, T9 in full, T11, Property 3) are open and listed in `OPEN.md`
  (`HPC/Hagopian/Hagopian76H.lean`).
* Part E, Hagopian 1976 IX (batch 164):
  * **the reparametrization** (`HPC.Hagopian.hagopian76_reparam`): an increasing homeomorphism `θ`
    of `[0, 1]` turns `k` into `θ ∘ k`, with the same layers, `π` and collar up to `θ`;
  * **T6 at Hagopian's abscissae** `[3/22, 19/22]` (`HPC.Hagopian.hagopian76_T6_placed`,
    `HPC.Hagopian.hagopian76_I1`);
  * in T7, **points of `π[M]` above `π[E]`** (`HPC.Hagopian.M_meets_above`) and **an accessible
    point of `M − E` above `π[E]`** (`HPC.Hagopian.exists_accessible_above`,
    `HPC.Hagopian.hagopian76_T7_accessible`);
  * the **positivity in `ε₂`** (`HPC.Hagopian.hagopian76_eps2_pos`).

  T7's arc `I₂`, and T8, T9 in full, T11 and Property 3, are open and listed in `OPEN.md`
  (`HPC/Hagopian/Hagopian76I.lean`).
* Part E, Hagopian 1976 X (batch 165):
  * **no hair on `E`** (`HPC.Hagopian.hagopian76_no_hair`: a continuum meeting `E` and missing both
    end sets lies in `E`) and **preimages of continua under `π`**
    (`HPC.Hagopian.preimage_pi_isContinuum`);
  * the **crossing lemma** (`HPC.Hagopian.rect_crossing`, by Janiszewski) and **T7**
    (`HPC.Hagopian.hagopian76_T7`: the arc `I₂` in every thin collar rectangle);
  * **link control** (`HPC.Hagopian.exists_isEps1_endCtl`, `HPC.Hagopian.hagopian76_link_control`),
    **T8** as property (D) (`HPC.Hagopian.hagopian76_T8`), **T9 in full**
    (`HPC.Hagopian.hagopian76_T9_full`) and **T11** with `K` replaced by `π⁻¹[D ∩ ⟨p₃, q₃⟩]`
    (`HPC.Hagopian.hagopian76_T11`).

  Property 3, T12–T17 and the assembly of Theorem 1 are open and listed in `OPEN.md`
  (`HPC/Hagopian/Hagopian76J.lean`).
* Part E, Hagopian 1976 XI (batch 166):
  * **`D` as a Jordan domain** (`HPC.Hagopian.rect_domain`, `HPC.Hagopian.hagopian76_D`). `D` is the
    bounded complementary domain of `I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩`. It is open and connected,
    has that curve as frontier, and meets `π[M]`.
  * **`K₀`**, the low part of `K` (`HPC.Hagopian.hagopian76_K0`). It is a component of
    `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets `π⁻¹(p₃)` and `π⁻¹[I₂]`. It is a **cross-cut** of `D`
    (`HPC.Hagopian.hagopian76_K0_crosscut`).
  * **two composants different from a given one in every open set** of an indecomposable continuum
    (`HPC.Hagopian.exists_two_composants_in_open`).

  "The chain `L − {L₁, L₁₁}` follows `Cl B`", Property 3, T12–T17 and the assembly of Theorem 1 are
  open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76K.lean`).
* Part E, Hagopian 1976 XII (batch 167):
  * **crossing translates** (Lemma T, `HPC.Hagopian.crossing_translate`). Let `h` be a small
    homeomorphism with `h(x)` above the axis and off `E`. Then the component of `M ∩ π⁻¹[D]` through
    `h(x)` contains `h[k⁻¹[[a + ζ/2, b − ζ/2]]]`, and its closure meets both side edges of `D`.
  * **Hagopian's `x`** in `k⁻¹(p₃) ∩ Cl(M ∩ K₀)` (Lemma T′, `HPC.Hagopian.K0_dense_low`).
  * **T12, parts (1)–(2)** (`HPC.Hagopian.hagopian76_T12_parts12`, `HPC.Hagopian.crossing_essential`).
    Crossing components over the thin strip are carried into a translate of `E` and are essential
    to `R(E)` there.

  T12 (3), Property 3, T13, T15–T17 and the assembly of Theorem 1 are open and listed in `OPEN.md`
  (`HPC/Hagopian/Hagopian76L.lean`).
* Part E, Hagopian 1976 XIII (batch 168):
  * **crossing pieces of `R(E)`** (Lemma R, `HPC.Hagopian.crossing_piece_of_R`). Near every point of
    `E` over the middle range, small translates of `E` give crossing continua of `R(k⁻¹(0), E)` that
    miss `E` and lie in one extension of `E`.
  * **crossing continua cut `D` along `K₀`** (`HPC.Hagopian.crossing_separates`,
    `HPC.Hagopian.crossing_pair_separates`), by the Jordan curve theorem in collar coordinates.
  * **T12, part (3), in a shape** (`HPC.Hagopian.hagopian76_T12`): a crossing continuum of
    `R(k⁻¹(0), E)` separates `p = h₀(x)` from `q = h₁(x)` on `K₀` in `π⁻¹[D]`.

  The report lists what T13–T17 actually use of `p` and `q`: only `p, q ∉ R(E)`. Choosing such
  `p` and `q`, Property 3, T13, T15–T17 and the assembly of Theorem 1 are open and listed in
  `OPEN.md` (`HPC/Hagopian/Hagopian76M.lean`).

* Part E, Hagopian 1976 XIV (batch 169):
  * **`R(E)` is meagre in `M`** (`HPC.Hagopian.isMeagre_Rset`): it lies in the composant of a point
    of `E`.
  * **below and above a crossing continuum** (`HPC.Hagopian.belowSet`, `HPC.Hagopian.aboveSet`):
    open sets, disjoint for a crossing continuum (`HPC.Hagopian.crossing_sides`).
  * **generic `p`, `q`** (`HPC.Hagopian.exists_generic_pq`): `p = h(x)` below and `q = h₁(x)` above a
    crossing continuum inside an extension `H`, both off `R(E)`. `H` and `R(E)` separate them in
    `π⁻¹[D]`, and their components in `M ∩ π⁻¹[D]` cross.
  * **the dichotomy for translates of `R(E)`**, proved if `Cl R(E) = M`
    (`HPC.Hagopian.Rset_homeo_dichotomy_of_closure`). It is also stated as a hypothesis
    (`HPC.Hagopian.RsetDichotomy`), under which T12 holds in the weakest form T13–T17 need
    (`HPC.Hagopian.hagopian76_T12_of_dichotomy`).
  * **T13**: the intersection of a chain of separating extensions still separates
    (`HPC.Hagopian.iInter_chain_extension`). If it is again an extension
    (`HPC.Hagopian.ExtChainInter`), the irreducible separating extension exists
    (`HPC.Hagopian.hagopian76_T13`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76N.lean`): the dichotomy
  itself, `Cl R(E) = M`, `ExtChainInter`, the covering half of above/below, Property 3, T15–T17 and
  the assembly of Theorem 1.

* Part E, Hagopian 1976 XV (batch 170):
  * **the intersection of a chain of extensions is an extension** (`HPC.Hagopian.extChainInter`,
    `HPC.Hagopian.extChainInter_in`), so **T13 holds unconditionally**
    (`HPC.Hagopian.hagopian76_T13_uncond`).
  * **"follows" for crossing components** (`HPC.Hagopian.follows_crossing`): the closure of a
    crossing component over the thin strip contains a small translate of the middle of `E`.
  * **components of `π⁻¹[D] − K` reach the frontier** for proper subcontinua `K` of `M`
    (`HPC.Hagopian.crossing_sides_cover_frontier`), the first step of the covering half.
  * **the least crossing parameter exists** in the form with margins
    (`HPC.Hagopian.crossing_set_closed`, `HPC.Hagopian.hagopian76_first_crossing_param`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76O.lean`): the cases of the
  covering half, Property 3, T15–T17, the dichotomy and the assembly of Theorem 1.

* Part E, Hagopian 1976 XVI (batch 171):
  * **T12 without the dichotomy** (`HPC.Hagopian.hagopian76_T12_uncond`): a homeomorphism moving a
    point of `E` off its composant carries `R(E)` off `R(E)` (`HPC.Hagopian.translate_Rset_disjoint`).
  * **Lemma 3 against two translated layers** (`HPC.Hagopian.layer_meets_translate_end`), and
    Property 3 reduced to an end case (`HPC.Hagopian.hagopian76_property3_reduced`).
  * **the bottom case of the covering half** (`HPC.Hagopian.crossing_bottom_below`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76P.lean`): the end case of
  Property 3, the `I₂` case and side edges of the covering half, the ends of crossing components,
  T15–T17 and the assembly of Theorem 1.

* Part E, Hagopian 1976 XVII (batch 172):
  * **the swallowing lemma** (`HPC.Hagopian.continuum_subset_layer_of_open`): a subcontinuum of a
    type A′ continuum with a nonempty relatively open part in one layer lies in that layer.
  * **Property 3 reduced to one configuration** (`HPC.Hagopian.hagopian76_property3_translate`): a
    layer containing a crossing contains a whole translate of the extension. Property 3 follows from
    the named `Prop` `Property3End` (`HPC.Hagopian.hagopian76_property3_of_end`). `Property3End`
    follows from `Cl R(E) = M` and from the dichotomy (`HPC.Hagopian.property3End_of_closure_Rset`,
    `HPC.Hagopian.property3End_of_dichotomy`).
  * **the inner collar of an arc of a Jordan curve** (`HPC.Hagopian.jordan_inner_collar`), and **the
    bottom and `I₂` cases of the covering half** (`HPC.Hagopian.crossing_sides_cover_schoenflies`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76Q.lean`):
  * `Property3End`;
  * the side edges and pockets of the covering half;
  * the ends of crossing components;
  * T15–T17 and the assembly of Theorem 1.

* Part E, Hagopian 1976 XVIII (batch 173):
  * **Property 3, unconditionally** (`HPC.Hagopian.hagopian76_property3`,
    `HPC.Hagopian.hagopian76_property3_domain`), by descent: a layer containing a translate of `E`
    contains a crossing (D1, `HPC.Hagopian.crossing_from_layer_translate`), a crossing in an interior
    layer gives one in a lower layer (D2, `HPC.Hagopian.crossing_descends`), and the crossing
    parameters form a closed set (`HPC.Hagopian.isClosed_layerCrossing`).
  * **a length bound for crossings** (`HPC.Hagopian.crossing_length_pos`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76R.lean`):
  * Property 3 for the end element `d⁻¹(1)`;
  * the pockets of the covering half;
  * the ends of crossing components;
  * "`I` is finite", Property 4, T15–T17 and the assembly of Theorem 1.

* Part E, Hagopian 1976 XIX (batch 174):
  * **Property 3 for every element of the decomposition**, the end element `d⁻¹(1)` included
    (`HPC.Hagopian.hagopian76_property3_end_element`,
    `HPC.Hagopian.hagopian76_property3_components`), through a proper extension;
  * **Hagopian's collection `I` is finite** (`HPC.Hagopian.hagopian76_I_finite`); distinct members
    have disjoint interiors (`HPC.Hagopian.crossingIntervals_disjoint`);
  * **`x₁ = 0`, `x₂ = e`** (`HPC.Hagopian.hagopian76_J_xs`) and **`[x₁, x₂]` does not have
    Property 4** (`HPC.Hagopian.hagopian76_property4_base`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76S.lean`):
  * `x₂ₙ = 1`;
  * Property 4 for `[x₂ₙ₋₁, x₂ₙ]` and the induction (Cases 1 and 2: pockets; `N` and `ε₂`);
  * the assembly of Theorem 1.

* Part E, Hagopian 1976 XX (batch 175):
  * **components through the middle cross**: every component of `F ∩ π⁻¹[D]` through a point over
    the abscissae `[3/8, 5/8]` is crossing or meets the far end set
    (`HPC.Hagopian.component_over_middle_crossing`); hence **no deep pockets**
    (`HPC.Hagopian.cover_pocket_middle`); P2 (`HPC.Hagopian.translate_through_point_in_F`);
  * **`x₂ₙ = 1` from one cutting step** (`HPC.Hagopian.hagopian76_x2n_eq_one_of_cut`, assuming the
    named `Prop` `TailCutKeepsSep`), with the tail lemma `HPC.Hagopian.hagopian76_tail_middle`.

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76T.lean`):
  * `TailCutKeepsSep`;
  * Property 4 for `[x₂ₙ₋₁, x₂ₙ]` and the induction (pockets over `L₆`; `N` and `ε₂`);
  * the assembly of Theorem 1.

* Part E, Hagopian 1976 XXI (batch 176):
  * **positions by `ε₃`** (`HPC.Hagopian.eps3_positions_middle`): for `ε₃` small, with Property 2
    kept, points within `ε₃` of a point over the abscissa `1/2` lie over `(3/8, 5/8)`;
  * **Janiszewski's theorem inside a domain** (`HPC.Hagopian.sepIn_union_cases`);
  * **`x₂ₙ = 1` and Property 4 for the top block from one separation statement**
    (`HPC.Hagopian.hagopian76_x2n_eq_one`, `HPC.Hagopian.hagopian76_property4_top`, assuming the
    named `Prop` `SepByCrossing`), on the T12 package `T12Data`;
  * **the closing contradiction, conditional** (`HPC.Hagopian.hagopian76_T15_T17_cond`: `T12Data`,
    `SepByCrossing` and the induction step `Property4Step` give `False`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76U.lean`):
  * `SepByCrossing`;
  * the existence of `T12Data`;
  * `Property4Step` (Cases 1 and 2);
  * the assembly of Theorem 1.

* Part E, Hagopian 1976 XXII (batch 177):
  * **the strand lemma** (`HPC.Hagopian.strand_lemma`, `HPC.Hagopian.strand_crossing`,
    `HPC.Hagopian.strand_closure_subset`, `HPC.Hagopian.strand_fine_positions`). A resolution `n` near
    `E` is fixed before `D`. Then every point of `M` over the inner middle `[3/22 + 3/n, 19/22 − 3/n]`
    of a thin enough domain lies on a crossing component (a strand). Its closure lies in a
    `θ/4`-translate `h[E]` and contains `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`;
  * **whole strands in type A′ continua** (`HPC.Hagopian.typeA'_inner_strands`);
  * **the T12 package exists** (`HPC.Hagopian.exists_T12Data`), with T12 (2) for the `h` of T12 (3);
  * **`π⁻¹[Fr D]` is compact and connected** (`HPC.Hagopian.pi_preimage_frontier_D`);
  * **the closing contradiction, conditional**:
    * `HPC.Hagopian.hagopian76_T15_T17_cond2`: the package and `Y` are discharged; `SepByCrossing`,
      the blocks and `Property4Step` give `False`;
    * `HPC.Hagopian.hagopian76_T15_T17_cond_fix` corrects the batch-176 form, whose hypotheses are
      inconsistent.

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76V.lean`):
  * the order of strands (S4);
  * the blocks of `St J`;
  * `SepByCrossing`;
  * `Property4Step`;
  * the assembly of Theorem 1.

* Part E, Hagopian 1976 XXIII (batch 178):
  * **the order of crossing pieces without Schoenflies** (`HPC.Hagopian.crossing_piece_sides`,
    `HPC.Hagopian.crossing_piece_below_iff`, `HPC.Hagopian.crossing_piece_below_trans`), in an
    abstract vertical frame, with crossing pieces of `π⁻¹[D]` as instances
    (`HPC.Hagopian.isPiece_of_isCrossingPiece`, `HPC.Hagopian.crossing_piece_meets_sigma`);
  * **separation along the vertical** (`HPC.Hagopian.strand_separation`, its converse, and
    `HPC.Hagopian.sepByCrossing_of_inner_crossing`);
  * **two plane continua with disconnected intersection separate the plane**
    (`HPC.Hagopian.separatesPlane_union_of_inter_disconnected`);
  * **the end layer of `F` is not over `D`** (`HPC.Hagopian.T12Data.end_layer_not_subset`);
  * **the strands through `h[R(E)] ∪ h₁[R(E)]` miss `F`** (`HPC.Hagopian.strand_misses_F_of_composant`);
  * **`SepByCrossing`, conditional** (`HPC.Hagopian.sep_by_crossing`, from the named `Prop`
    `InnerComponentsCross`);
  * **the blocks of `St J`** (`HPC.Hagopian.exists_blocks`, assuming the members of `I` nondegenerate).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76W.lean`):
  * `InnerComponentsCross` (3b) and its block form (3c);
  * crossing pieces through `p`, `f(p)` (4.B);
  * nondegeneracy of the members of `I`;
  * `Thm1Setup` and Theorem 1 from the step (§7);
  * `Property4Step` (§8) and the assembly of Theorem 1.

* Part E, Hagopian 1976 XXIV (batch 179):
  * **the strands of `p`, `f(p)` are crossing pieces missing `F`** (`HPC.Hagopian.p_on_crossing_piece`);
  * **the members of `I` are nondegenerate and the crossing components are finitely many**
    (`HPC.Hagopian.crossingIntervals_nondegenerate`, `HPC.Hagopian.crossing_components_finite`);
  * **the heights of Property 3, of "`I` is finite" and of `x₂ₙ = 1` are chosen before `F`**
    (`HPC.Hagopian.hagopian76_property3_components_unif`, `HPC.Hagopian.hagopian76_I_finite_unif`,
    `HPC.Hagopian.hagopian76_x2n_eq_one_unif`, and the other `…_unif` theorems);
  * **`SepByCrossing`, `x₂ₙ = 1` and Property 4 for the top block from `InnerComponentsCross` alone**
    (`HPC.Hagopian.sep_by_crossing_uncond`, `HPC.Hagopian.hagopian76_x2n_eq_one_final`,
    `HPC.Hagopian.hagopian76_property4_top_final`), and the blocks (`HPC.Hagopian.exists_blocks_uncond`);
  * **Hagopian's set-up assembled from T1–T13** (`HPC.Hagopian.Thm1Setup`,
    `HPC.Hagopian.exists_thm1Setup`);
  * **Theorem 1 from `InnerComponentsCross` and `Property4Step`** for every set-up
    (`HPC.Hagopian.hagopian76_theorem1_of_step`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76X.lean`):
  * `InnerComponentsCross` (2e, with 2a, 2b, 2d) and its block form (3c);
  * `Property4Step` (§6);
  * the unconditional Theorem 1.

* Part E, Hagopian 1976 XXV (batch 180):
  * **with batch 179's `K = {p}`, Property 4 fails below the top block**
    (`HPC.Hagopian.property4_lower_false_of_K_eq`), so the set-up is repaired:
    `HPC.Hagopian.Thm1Setup` now carries `K = {p} ∪ K₀` (the points of `M` over the low vertical),
    `ε₂` as printed, `ε₃ ≤ θ/2` with the position clause, `n ≥ 40` and the composant data
    (`HPC.Hagopian.hagopian76_T15_T17_cond4`, `HPC.Hagopian.exists_thm1Setup`);
  * **every crossing piece inside `M` meets `K`** (`HPC.Hagopian.Thm1Setup.K_meets_crossing`);
  * **the end layer of `F` meets the tip layer** (`HPC.Hagopian.tip_meets_end_layer` and its mirror);
  * **the tip triods 2a, 2b and the degenerate chunk 2c** (`HPC.Hagopian.tip_triod`,
    `HPC.Hagopian.tip_triod_mirror`, `HPC.Hagopian.tip_triod_on_tip_layer`,
    `HPC.Hagopian.degenerate_chunk_iii`);
  * **Theorem 1 from `InnerComponentsCross` on `(3/22 + 8/n, 19/22 − 8/n)` and `Property4Step`**
    for every repaired set-up (`HPC.Hagopian.hagopian76_theorem1_of_step`, restated).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76Y.lean`):
  * 2d and 2e (`InnerComponentsCross`), 3c, E0, E1;
  * `Property4Step` (§4: E2.1–E2.6, Case 2);
  * the unconditional Theorem 1.

* Part E, Hagopian 1976 XXVI (batch 181):
  * **two bounds on `ε₃` added to the set-up** (`HPC.Hagopian.Thm1Setup` fields `hε₃O`, `hε₃S`;
    `HPC.Hagopian.exists_thm1Setup` restated), so that **`f(y) ∈ π⁻¹[D]` for `y ∈ K`**
    (`HPC.Hagopian.f_mem_O_of_mem_K`);
  * **the cap lemma**: the region above a crossing piece has closure missing the open bottom edge, and
    a point of the middle set within `ε₃` of a point above a crossing piece is within `ε₃` of its
    closure (`HPC.Hagopian.above_closure_misses_bottom`, `HPC.Hagopian.cross_strand_near`; mirror
    under a hypothesis, `HPC.Hagopian.cross_strand_near_mirror`);
  * **3c, E0, E1** with `InnerComponentsCross` as a hypothesis (`HPC.Hagopian.block_components_cross`,
    `HPC.Hagopian.property4_strand`, `HPC.Hagopian.property4_step_unless_setup`);
  * **the ending of Case 1 and claim (c) of Case 2** (`HPC.Hagopian.case1_ending`,
    `HPC.Hagopian.case2_ending`);
  * **the mirror tip triod with the hypothesis relaxed to `2/n < σ < 1`**
    (`HPC.Hagopian.tip_triod_mirror_rel`, `HPC.Hagopian.chunk_edge_case_mirror`);
  * **Theorem 1 from `InnerComponentsCross` and three named `Prop`s** (`BlockLayersMeetSides`,
    `Case1Claims`, `Case2Claims`) (`HPC.Hagopian.hagopian76_property4_step_cond`,
    `HPC.Hagopian.hagopian76_theorem1_of_cases`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76Z.lean`):
  * saturation §1.1–§1.4 (except §1.4 step 3), 2d and 2e (`InnerComponentsCross`);
  * the named `Prop`s `BlockLayersMeetSides`, `Case1Claims`, `Case2Claims`;
  * the unconditional Theorem 1.

* Part E, Hagopian 1976 XXVII (batch 182):
  * **the case split of p. 348 fails at `i = 2`**: for every set-up with blocks, `d⁻¹(x₂) = k⁻¹(1)`
    meets neither side segment, so the batch-181 named `Prop` `BlockLayersMeetSides` is false
    (`HPC.Hagopian.blockLayersMeetSides_false`; `hagopian76_theorem1_of_cases` is a vacuous reduction);
  * **the mirror cap with no extra hypothesis** (`HPC.Hagopian.cross_strand_near_above`), and the
    cap, E1 and the endings of Cases 1 and 2 **in both orientations** (`HPC.Hagopian.cross_strand_near_o`,
    `HPC.Hagopian.property4_step_unless_o`, `HPC.Hagopian.case1_ending_oriented`,
    `HPC.Hagopian.case2_ending_oriented`);
  * **the last step** (`i = 2`) read with the bottom edge in place of the `J`-strand
    (`HPC.Hagopian.last_step_ending`, `HPC.Hagopian.not_property4_x3x4`);
  * **the closure of `F − E` meets `E` only in `k⁻¹(1)`** (`HPC.Hagopian.closure_G_diff_E`); the halves
    `K∓` are continua (`HPC.Hagopian.Thm1Setup.kminus_isContinuum`, `kplus_isContinuum`); boundary
    bumping in a half, reaching a side segment (`HPC.Hagopian.Thm1Setup.half_bump`,
    `HPC.Hagopian.Thm1Setup.half_bump_side`);
  * **`L ∩ F = ∅`** for an extension through a good point, and the components through `h[R(E)]`,
    `h₁[R(E)]` miss `F` (`HPC.Hagopian.Thm1Setup.extension_misses_G`,
    `HPC.Hagopian.Thm1Setup.comp_disjoint_G`);
  * **tight block sequences**: the assembly with the step asked only for block sequences without padded
    blocks (`HPC.Hagopian.exists_thm1Setup_tight`, `HPC.Hagopian.hagopian76_theorem1_of_step_tight`);
  * **Theorem 1 from `InnerComponentsCross` and five named `Prop`s** with no antecedent `¬ Property4 J`
    (`StepFrame`, `LastStepClaims`, `BlockLayersMeetSides3`, `Case1Claims'`, `Case2Claims'`)
    (`HPC.Hagopian.hagopian76_property4_step_cond2`, `HPC.Hagopian.hagopian76_theorem1_of_cases2`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76AA.lean`):
  * saturation (§3.1 steps 4–5; the points `zⱼ`; `τ₁ = 1`), 2d and 2e (`InnerComponentsCross`);
  * the case split for `i ≥ 3`; E2.1 steps 1–3, 5; E2.4; Case 2 (e); the five named `Prop`s;
  * the unconditional Theorem 1.

* Part E, Hagopian 1976 XXVIII (batch 183):
  * **Bing 1960 pp. 224–228 read against Hagopian pp. 348–349**: the dictionary and which of Bing's
    reasons carry over to continua (`doc/notes/hagopian76-cases.md`, E5; `LEDGER.md` §6);
  * **E2.4 by Bing's arc `ab`**: the pair of points within `ε₃` in both of Bing's configurations
    (`HPC.Hagopian.e24_pair_between`, `HPC.Hagopian.e24_pair_below`); the part of a minimal admissible
    continuum between two layers, with the layers kept (`HPC.Hagopian.minimalAdmissible_restrict_of_lsc`,
    `HPC.Hagopian.minimalAdmissible_restrict`); the violation of Property 2
    (`HPC.Hagopian.property2_violation`); E2.4 from the named `Prop` `E24Claims`
    (`HPC.Hagopian.e24_between_false`, `HPC.Hagopian.e24_below_far`, `HPC.Hagopian.E24Data.far`);
  * **Theorem 1 with E2.4 and Case 2 (d) reduced to `E24Data`**
    (`HPC.Hagopian.hagopian76_theorem1_of_cases3`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76AB.lean`):
  * "between" (Case 1); Case 2 (a), (b), (e); the two other orientations (the proposal fails as
    stated); E2.1 steps 1–3, 5; saturation and 2e; the split by the gap continuum;
  * the named `Prop`s `StepFrame`, `LastStepClaims`, `BlockLayersMeetSides3`, `Case1ClaimsE24`,
    `Case2ClaimsE24`, `E24Claims`;
  * the unconditional Theorem 1.

* Part E, Hagopian 1984 I (batch 184; Hagopian 1976 Theorem 1 by F. B. Jones's plan,
  `doc/notes/hagopian84.md`):
  * **the assembly**: Theorem 1 of 1976 from Jones's decomposition and the arc step, both named
    `Prop`s (`HPC.Hagopian.hagopian76_theorem1_of_jones`, from `Hagopian84Decomp` and
    `NoArcIndecHomPlane`);
  * **the plane quotient**: a monotone image of a homogeneous indecomposable plane continuum with
    proper fibres is homeomorphic to a compact plane set, by Moore 1925
    (`HPC.Hagopian.exists_plane_quotient_of_monotone`); monotone images of indecomposable continua are
    indecomposable (`HPC.Hagopian.indecomposable_of_monotone_image`);
  * **Hagopian 1975 Theorem 1 with paragraph 4 supplied** by the arc step
    (`HPC.Hagopian.hagopian75_theorem1_of_noArc`);
  * **Hagopian 1984 Lemmas 1, 6, 11 (with `N = M`)** (`HPC.Hagopian.hagopian84_lemma1`,
    `HPC.Hagopian.hagopian84_lemma6`, `HPC.Hagopian.hagopian84_lemma11`), and the definitions of the
    paper's §3 (essential subcontinuum, 5-linked chains, free, normal, runs straight, regular, `Ω`, `Δ`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian84A.lean`):
  * Lemmas 7, 8, 10, 12–16; the arc in `M/𝔇`; Theorem 1 with `N = M` (`Hagopian84Decomp`);
  * the arc step `NoArcIndecHomPlane` (Bing 1960; reconnaissance only).

* Part E, Hagopian 1976 XXX (batch 185; the 1984 Lemma 7, saturation, the case split):
  * **the two-sided extension**: a type λ continuum is an essential subcontinuum of one missing both
    of its end sets (`HPC.Hagopian.hagopian84_two_sided`), by gluing two type λ continua along a common
    end set (`HPC.Hagopian.glue_minimalAdmissible`);
  * **Lemma 7 of Hagopian 1984** (`HPC.Hagopian.hagopian84_lemma7`, `HPC.Hagopian.hagopian84Lemma7_holds`),
    by a route other than the printed one; **rigidity** (`HPC.Hagopian.layers_agree`) and **runs**
    (`HPC.Hagopian.translate_run`, `HPC.Hagopian.translate_run_right`);
  * **saturation (2e)** for Hagopian's `F`, unconditionally (`HPC.Hagopian.innerComponentsCross_hagopian`,
    through `HPC.Hagopian.half_in_O_false` and `HPC.Hagopian.noncrossing_half_in_O_steps45`);
  * **the case split for `i ≥ 3`** (`HPC.Hagopian.blockLayersMeetSides3`), and `d⁻¹(x₃)` meets a side
    segment (`HPC.Hagopian.layer_x3_meets_side`);
  * **Theorem 1 from four named `Prop`s** `StepFrame`, `LastStepClaims`, `Case1ClaimsE24`,
    `Case2ClaimsE24` (`HPC.Hagopian.hagopian76_theorem1_of_cases4`); `Wset84 = Wset`
    (`HPC.Hagopian.wset84_eq_wset`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian76AC.lean`):
  * runs of `F` along a translate (§3.3); "between" with runs (§6);
  * the four named `Prop`s; the 1984 Lemmas 8, 10, 12–16 and `Hagopian84Decomp`, `NoArcIndecHomPlane`;
  * the unconditional Theorem 1.

* Part E, Hagopian 1984 III (batch 186; the quotient package, Lemmas 12–16):
  * **the quotient package**: `Hagopian84Decomp` from Jones decompositions
    (`HPC.Hagopian.hagopian84Decomp_of_package`, `HPC.Hagopian.IsJonesDecomp84`), with homogeneity
    of the quotient by an orbit argument (`HPC.Hagopian.exists_comp_small_homeo`) and the arc by a
    quotient-map lift;
  * **folds** (`HPC.Hagopian.exists_fold`), **Lemma 12** (`HPC.Hagopian.hagopian84_lemma12`);
  * **the decomposition `Δ(𝒫)` and positivity** (`HPC.Hagopian.delta5_partition`,
    `HPC.Hagopian.delta5_dist_pos`), **Lemma 14** (`HPC.Hagopian.hagopian84_lemma14`), **Lemma 15**
    with a smaller `ε` (`HPC.Hagopian.hagopian84_lemma15`), and an interval of layers in `Δ(𝒫)`
    (`HPC.Hagopian.exists_interval_in_delta`).

  The following are open and listed in `OPEN.md` (`HPC/Hagopian/Hagopian84B.lean`):
  * Lemma 13 (with the chain of its proof), Lemma 16 and its weaker form;
  * the construction of pp. 343–344 and the assembly `hagopian84_decomp`; `NoArcIndecHomPlane`
    (reconnaissance of Jones 1975 in `doc/notes/jones75.md`).

* Part E, Hagopian 1984 IV (batch 187; Lemma 13, Lemma 16′, the bridge `J(Z)`, `𝒫(Z)`, the cover):
  * **Lemma 13** (`HPC.Hagopian.hagopian84_lemma13`), with the chain of its proof
    (`HPC.Hagopian.chainLinks84_chain`, `HPC.Hagopian.chainLinks84_runsStraight`,
    `HPC.Hagopian.chainLinks84_regular`): Hagopian's (3) through Lemma 3 and fifteen gap bounds, (4)
    through Effros, (5) through the fold and atriodicity, and regularity in a general form
    (`HPC.Hagopian.strand_of_runsStraight84`);
  * **Lemma 16′** (`HPC.Hagopian.strand_layer_of_extension`): for a free normal regular chain, every
    layer of a type λ continuum whose end layer misses `⋃𝒫′`, through a point of `⋃𝒫′`, is a layer
    of a strand; with the dichotomy, the impossibility of the degenerate case
    (`HPC.Hagopian.not_strand_subset_extension_layer`) and the identification
    (`HPC.Hagopian.strand_layer_mem_delta`);
  * **Lemma 16 as printed** (`HPC.Hagopian.hagopian84_lemma16`, normality added), from Lemma 16′;
  * **the bridge** (`HPC.Hagopian.exists_bridge84`) and the position of `Ω(𝒫) ∖ Δ(𝒫)`
    (`HPC.Hagopian.omega_not_delta_side`);
  * **the chain `𝒫(Z)`** with `Z ∈ Δ(𝒫(Z))` (`HPC.Hagopian.exists_chainZ84`,
    `HPC.Hagopian.mem_delta_of_bridge_chain`) and **the finite cover**
    (`HPC.Hagopian.hagopian84_cover`, `HPC.Hagopian.exists_finite_cover84`), by compactness of
    `Cl ⋃Δ(𝒫) ∖ ⋃Δ(𝒫)` instead of the printed closedness of `⋃𝔅`.

  The following were open after batch 187 and are closed in batch 188: the relation `𝔇`, claims
  (5)–(6), the fields of `IsJonesDecomp84` and `hagopian84_decomp`.

* Part E, Hagopian 1984 V (batch 188; `𝔇`, claims (5)–(6), `hagopian84_decomp`):
  * **the transfer lemma** (`HPC.Hagopian.omega_layer_of_mem_mid`,
    `HPC.Hagopian.omega_mem_delta_of_mem_mid`): a member of `Ω(𝒫)` through a point of `⋃𝒬′`, for a
    free normal regular chain `𝒬` whose union misses `Cl P₃`, is a layer of the strand of `𝒬` through
    that point (Lemma 16′ for `𝒬`); it replaces Hagopian's "by (2), (3), and Lemma 7";
  * **the decomposition `𝔇`** (`HPC.Hagopian.CoverData84`, `HPC.Hagopian.exists_coverData84`,
    `HPC.Hagopian.CoverData84.members_disjoint`, `HPC.Hagopian.CoverData84.setoid`);
  * **claims (5) and (6)** (`HPC.Hagopian.CoverData84.omega_subset_members`,
    `HPC.Hagopian.CoverData84.omega_mem_members`, `HPC.Hagopian.CoverData84.invariant`);
  * **the package** (`HPC.Hagopian.CoverData84.isJonesDecomp`) and **Theorem 1 of 1984 with
    `N = M`, in the form used** (`HPC.Hagopian.hagopian84_decomp : Hagopian84Decomp`);
  * **Theorem 1 of 1976 from the arc step alone** (`HPC.Hagopian.hagopian76_theorem1_jones`);
  * the printed `⋃𝔅 = M` (`HPC.Hagopian.sUnion_cover84_eq_univ`).

  Open after batch 188: `NoArcIndecHomPlane` (Jones 1975), the last open input of
  `Hagopian76Thm1` on the 1984 route; closed in batch 190.

* Part E, Jones 1975 I (batch 189; arcs and lines, no small reversal, recurrence, (L)), for a compact
  metric space with `HPC.Hagopian.JonesSetting` (homogeneous, hereditarily unicoherent, atriodic,
  with an arc; `HPC.Hagopian.jonesSetting_of_plane` for a homogeneous indecomposable plane continuum):
  * **Jones (c)** (`HPC.Hagopian.JonesSetting.union_arc`, `HPC.Hagopian.JonesSetting.nested`) and
    arcs through a point (`HPC.Hagopian.JonesSetting.exists_arc_through`);
  * **every arc component is a line** (`HPC.Hagopian.JonesSetting.exists_line`), arcs of a line
    (`HPC.Hagopian.JonesSetting.line_arc`) and homeomorphisms on lines
    (`HPC.Hagopian.JonesSetting.homeo_on_line`);
  * **no small reversal and orientation** (`HPC.Hagopian.JonesSetting.no_reversal_arc`,
    `HPC.Hagopian.JonesSetting.exists_no_reversal`, `HPC.Hagopian.JonesSetting.orientation`), which
    replace Jones's (f), whose proof is defective (ledger J75.1);
  * **recurrence** (`HPC.Hagopian.JonesSetting.omegaLim_saturated`,
    `HPC.Hagopian.JonesSetting.line_recurrent`, `HPC.Hagopian.JonesSetting.jones75_d`);
  * **(L), no backtracking** (`HPC.Hagopian.JonesSetting.no_backtrack`,
    `HPC.Hagopian.no_backtrack_in_collar`).

  The planar core, open after batch 189, is closed in batch 190.

* Part E, Jones 1975 II (batch 190; the planar core, by the route of commission 190):
  * **passes** of a collar box and their properties (P1)–(P4) (`HPC.Hagopian.IsPass`,
    `HPC.Hagopian.IsPass.disjoint`, `HPC.Hagopian.IsPass.finite`,
    `HPC.Hagopian.IsPass.above_or_below`);
  * **the shadow lemma and the flow box**, in the middle band (`HPC.Hagopian.shadow_pass`,
    `HPC.Hagopian.flow_box`), and late thin passes (`HPC.Hagopian.exists_late_thin_pass`);
  * **the region of a thin pass** (`HPC.Hagopian.region_pass`, `HPC.Hagopian.region_cross`,
    `HPC.Hagopian.region_lemmaA`) and **the trapping lemma** (`HPC.Hagopian.trap_pass`);
  * **the arc step** (`HPC.Hagopian.jones75_noArc : NoArcIndecHomPlane`): no indecomposable
    homogeneous plane continuum contains an arc;
  * **Theorem 1 of Hagopian 1976, unconditionally** (`HPC.Hagopian.hagopian76_theorem1 :
    Hagopian76Thm1`): every indecomposable homogeneous plane continuum is hereditarily
    indecomposable;
  * unconditionally: **Bing 1960 for plane continua** (`HPC.Hagopian.bing60_plane_uncond`), Hagopian
    1976 Theorem 2 (`HPC.Hagopian.hagopian76_theorem2_uncond`), Hagopian 1975 Corollary and
    Theorem 2 (`HPC.Hagopian.hagopian75_corollary_uncond`, `HPC.Hagopian.hagopian75_theorem2_uncond`)
    and `HPC.Hagopian.hagopian75_theorem1_of_noArc_uncond`.

  Nothing on the route to `Hagopian76Thm1` is open.

* Theorem C I (batch 191; span, Cook 1967, Oversteegen–Tymchatyn 1982 Theorem 3.6 and Corollary 3.5,
  `HPC/Span/`):
  * **span** in topological form (`HPC.Span.SurjSpanPos`, `HPC.Span.SurjSemiSpanPos`,
    `HPC.Span.SpanZero`, `HPC.Span.SemiSpanZero`, `HPC.Span.HOSpanZero`) and O–T's definitions read
    literally (`HPC.Span.otSemiSpanPos_iff`, `HPC.Span.otSpanPos_iff`), the Hoehn–Oversteegen forms
    (`HPC.Span.semiSpanZero_iff_hoSpanZero`, `HPC.Span.hoSpanZero_iff_maps`);
  * **Cook 1967, Theorem 4**: maps onto hereditarily indecomposable continua are confluent
    (`HPC.Span.cook67_theorem4`);
  * **Brouwer reduction** (`HPC.Span.isContinuum_sInter_chain`, `HPC.Span.brouwer_reduction`) and
    **Davis's Theorem 1.1 for hereditarily indecomposable continua**
    (`HPC.Span.exists_surjSpanPos_of_surjSemiSpanPos`, `HPC.Span.semiSpanZero_of_spanZero`);
  * **O–T Theorem 3.6 (indecomposable case) from Corollary 3.5** (`HPC.Span.ot82_theorem36_of_cor35`,
    `HPC.Span.theoremC_of_cor35`);
  * **O–T Corollary 3.5 from Theorem 3.2 in strip form** (`HPC.Span.ot82_cor35_of_thm32 : OTThm32 →
    OTCor35`), with the re-embedding lemmas (`HPC.Span.exists_homeomorph_unique_leftmost`,
    `HPC.Span.exists_homeomorph_push`, `HPC.Span.isConnected_rightHalf_diff`) and uncountably many
    disjoint crossing continua (`HPC.Span.exists_uncountable_crossing`);
  * **Theorem C from Theorem 3.2** (`HPC.Span.theoremC_of_thm32 : OTThm32 → TheoremC`).

  Open after batch 191 (both closed in batch 192): `OTThm32` (O–T Theorem 3.2 in strip form; the only open input of
  `TheoremC`) and `crossing_traces_separated` (commission 191 §7, commented out); see `OPEN.md`.

* Theorem C II (batch 192; the strip theorem, `HPC/Span/OT82*.lean`):
  * **Theorem C of Hoehn–Oversteegen, unconditionally** (`HPC.Span.theoremC : TheoremC`): "every
    homogeneous indecomposable plane continuum has span zero" (`HOSpanZero`, the Hoehn–Oversteegen
    form);
  * **O–T Theorem 3.2 in strip form** (`HPC.Span.ot82_theorem32 : OTThm32`);
  * the **strip lemma** (O–T Theorem 2.7 in the form used, `HPC.Span.strip_lemma`), with the parity
    tools (`HPC.Span.parity_eq_zero_of_not_mem_convex`, `HPC.Span.parity_eq_of_perturb`,
    `HPC.Span.parity_flip_vertical_edge`), a common zero on a rectangle
    (`HPC.Span.common_zero_rect`) and the continuity of the strip sign function
    (`HPC.Span.stripSign_continuousOn`);
  * the **order of disjoint crossing continua** (`HPC.Span.crossing_traces_separated`).

  Nothing on the route to `TheoremC` is open.

* H–O Theorem 1, I (batch 193; Hoehn–Oversteegen 2016 Theorems 1, 4, 8 and Krasinkiewicz–Minc 1977
  Lemma 2, `HPC/HO16/*.lean`):
  * **Every indecomposable non-degenerate homogeneous plane continuum is a pseudo-arc, from
    `HOThm20`** (`HPC.HO16.isPseudoArc_of_indec_homogeneous`,
    `HPC.HO16.homeomorph_pseudoArc_of_indec_homogeneous`), where `HOThm20` is the forward direction
    of H–O Theorem 20 for PL graphs, a named `Prop` and the only open input;
  * **H–O Theorem 1, "if" direction, for plane continua, from `HOThm20`**
    (`HPC.HO16.ho16_theorem1_plane`): a hereditarily indecomposable plane continuum with span zero
    is snake-like;
  * **H–O Theorem 4** in path form (`HPC.HO16.ho16_theorem4`); **K–M Lemma 2** for hereditarily
    indecomposable compacta (`HPC.HO16.km77_lemma2`); the **core of H–O Theorem 8, (1) ⇒ (2)**
    (`HPC.HO16.ho16_theorem8_core`);
  * plane approximations: a hereditarily indecomposable plane continuum has empty interior
    (`HPC.HO16.interior_eq_empty_of_hi`), grid graphs (`HPC.HO16.exists_plGraph_approx`), paths
    (`HPC.HO16.exists_path_approx`).

  Open: `HOThm20` (to be proved in later batches; see `OPEN.md`).

* H–O Theorem 1, II (batch 194; Hoehn–Oversteegen 2016 §4, `HPC/HO16/FoldDefs.lean` …
  `HO16B.lean`):
  * simple folds realized as sets in `E × ℝ` (`HPC.HO16.IsSimpleFoldOf`), and **they exist** for
    every triple satisfying (F1)–(F3) (`HPC.HO16.exists_simpleFold`);
  * a **library for PL graphs**: common subdivisions and refinement
    (`HPC.HO16.IsPLGraph.exists_refinement`), unions, closures of differences, finite relative
    frontiers, components (`HPC/HO16/Subdiv.lean`, `PLLib.lean`);
  * **H–O Lemma 6** (`HPC.HO16.ho16_lemma6`), **H–O Theorem 8, (1) ⇒ (2), for simple folds**
    (`HPC.HO16.ho16_theorem8`), **H–O Proposition 7** (`HPC.HO16.ho16_prop7`);
  * certificates: Theorem 1 as restated on p. 211 and Theorem 1′ as printed on p. 212 fail for a
    one-point continuum (`HPC.HO16.ho16_theorem1_printed_false`,
    `HPC.HO16.ho16_theorem1prime_printed_false`).

  Open: `HOThm20`, unchanged (see `OPEN.md`).

* H–O Theorem 1, III (batch 195; Hoehn–Oversteegen 2016 §§4–6, `HPC/HO16/StairDefs.lean` …
  `HO16C.lean`):
  * library additions: components of `G \ (K ∪ P)`, **ordinary points** (order 2, independent of
    the decomposition: `HPC.HO16.isOrdinaryPt_iff_order`), intersections with PL graphs and with
    preimages under `Prod.fst` (`HPC/HO16/PLLib2.lean`);
  * **Definition 9** (consistent complement, sides `σ_B(A)`), the observations of p. 190 (the
    characterization of `σ_B(A)`), **Propositions 10 and 11** (`HPC.HO16.ho16_prop10`,
    `HPC.HO16.ho16_prop11`; the second part of Proposition 10 by a route avoiding a gap in H–O's
    proof, `LEDGER.md` HO.15);
  * **Definitions 12, 13, 16** (straight sets, end sets, stairwell and broken stairwell structures),
    the observations on components, **Claim 14.1** and `π(S) = G` for odd height on connected `G`,
    the height-1 homeomorphism, **Proposition 17** (`HPC.HO16.ho16_prop17`), the remarks of p. 201,
    **Lemma 18** (`HPC.HO16.ho16_lemma18`) and the fold of Proposition 19 with (19.1)–(19.3)
    (`HPC.HO16.ho16_prop19_fold`);
  * a certificate that the remarks of pp. 193–194 fail without "G connected"
    (`HPC.HO16.ho16_p193_remark_false`), and a stairwell structure of height 3 over `[0, 3]`
    (`HPC.HO16.stairwell_example`).

  Open: `HOThm20`, unchanged (see `OPEN.md`).

* H–O Theorem 1, IV (batch 196; Hoehn–Oversteegen 2016 pp. 202–210, `HPC/HO16/P19Defs.lean` …
  `HO16D.lean`, `NonVac196.lean`):
  * **ordinary points of a simple fold** (`HPC.HO16.IsSimpleFoldOf.isOrdinaryPt_iff`);
  * **Proposition 19** in the full fold (`HPC.HO16.ho16_prop19_full`) and for a connected fold
    (`HPC.HO16.ho16_prop19`), with the proof of p. 208 repaired;
  * a certificate that a sentence of the proof on p. 208 is false (`HPC.HO16.ho16_p208_false`);
  * **Theorem 20 from Theorem 15** (`HPC.HO16.ho16_theorem20_of_thm15 : HOThm15 → HOThm20`), the
    induction `HPC.HO16.ho16_lift_stairwell`, and the classification step with `HOThm15` as its only
    open input (`HPC.HO16.homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`).

  Open: `HOThm15` (H–O Theorem 15, a named `Prop`; see `OPEN.md`); `HOThm20` follows from it.

* H–O Theorem 1, V (batch 197; Hoehn–Oversteegen 2016 pp. 194–198, `HPC/HO16/LadderDefs.lean` …
  `HO16E.lean`, `NonVac197.lean`):
  * **ladders** (`HPC.HO16.IsLadder`, `ladderSheet`, `ladderHeight`): an explicit form of H–O's
    sheets with side wedges and zig-zags; **every ladder carries a stairwell structure of odd
    height** (`HPC.HO16.ho16_stairwell_of_ladder`), with an example of height 3
    (`HPC.HO16.ladder_example_stairwell`);
  * **a ladder inside every open neighbourhood of a separator** (`HPC.HO16.exists_ladder`, replacing
    H–O's Claim 15.1), hence **H–O Theorem 15** (`HPC.HO16.ho16_theorem15 : HOThm15`) and
    **Theorem 20** (`HPC.HO16.ho16_theorem20 : HOThm20`);
  * **every indecomposable non-degenerate homogeneous plane continuum is a pseudo-arc**, with no
    named hypothesis (`HPC.HO16.ho16_indec_homogeneous_pseudoArc`), and the two-way form with Bing's
    converse (`HPC.HO16.ho16_indec_homogeneous_iff`); its hypotheses are met by the plane
    pseudo-arc (`HPC.HO16.exists_indec_homogeneous_plane`).

  Open: nothing new. `HOThm15` and `HOThm20` are closed. What remains of the classification is the
  decomposable case (the circle of pseudo-arcs) and the final three-case statement (see `OPEN.md`).

* Part G, I (batch 198; Bing–Jones 1959, `HPC/BJ59/Defs.lean` … `BJ59A.lean`, `NonVac198.lean`):
  * definitions: arcs of continua, continuous arcs of pseudo-arcs, **circles of pseudo-arcs**
    (`HPC.BJ59.IsCircleOfPA`), chain maps; the named inputs `BJThm10` (Bing–Jones Theorem 10),
    `HOCircleLike`, `BJPlaneExample`;
  * **Jones's elements are pseudo-arcs** (`HPC.BJ59.isPseudoArc_Lset`, unconditional);
  * from `BJThm10`: any two circles of pseudo-arcs are homeomorphic and each is homogeneous
    (`homeomorph_of_isCircleOfPA`, `isHomogeneous_of_isCircleOfPA`);
  * **the classification of homogeneous plane continua**, from the named inputs
    (`HPC.BJ59.ho16_classification`, `HPC.BJ59.ho16_classification_plane`);
  * Bing–Jones Theorems 2, 3, 4, 6 (`bj_theorem2` … `bj_theorem6`); Theorem 5 refuted as printed
    (`bj_theorem5_printed_false`) and proved in repaired form (`bj_theorem5`).

  Open: the named inputs `BJThm10`, `HOCircleLike`, `BJPlaneExample` (see `OPEN.md`).
* Part G, II (batch 199; Domokos–Prajs 2022 Theorem 6.1 and Bing–Jones 1959 Theorem 7,
  `HPC/BJ59/Atomic.lean` … `Thm7Ends2.lean`, `BJ59B.lean`, `NonVac199.lean`):
  * definitions: atomic maps (`HPC.BJ59.IsAtomicMap`), open atomic maps onto the circle with
    pseudo-arc fibres (`IsAtomicCircPAMap`), chains in Bing–Jones's sense (`IsBJChain`);
  * **an atomic map onto an arc with snake-like hereditarily indecomposable fibres has a snake-like
    domain** (`isSnakeLike_of_atomic'`, unconditional);
  * from `BJThm10`: **Domokos–Prajs Theorem 6.1** in the "if" direction (`dp22_theorem61`): a
    compact metric space with an open atomic map onto the circle with pseudo-arc fibres is
    homeomorphic to every circle of pseudo-arcs, is homogeneous, and is a circle of pseudo-arcs
    when one exists (`isCircleOfPA_of_atomic`, `homeomorph_of_atomic`, `isHomogeneous_of_atomic`);
  * the decomposable case without circle-likeness (`circle_or_atomic_of_decomposable`,
    unconditional) and **the classification from `BJThm10` alone**
    (`ho16_classification_atomic`); `HOCircleLike` is now a theorem (`hoCircleLike`, from `BJThm10`
    and `BJPlaneExample`), giving `ho16_classification₂`, `ho16_classification_plane₂`;
  * **Bing–Jones Theorem 7** (`bj_theorem7`, every `n`; `bj_theorem7_ends`, `n ≥ 3`); its second
    sentence refuted as printed for one link (`bj_theorem7_ends_printed_false`);
  * optional items: the general, non-degenerate certificate against Bing–Jones Theorem 5 as printed
    (`bj_theorem5_printed_false_general`, `HPC/BJ59/Thm5Cert.lean`), and Bing–Jones chains are
    Fugate's taut chains (`isBJChain_iff_isTaut`, `HPC/BJ59/Taut.lean`).

  Open: `isAtriodic_of_atomic` (commented out); the named inputs `BJThm10`, `BJPlaneExample` (see
  `OPEN.md`). Bing–Jones Theorem 9, left open in batch 199, is proved in batch 200 (below).
* Part G, III (batch 200; Bing–Jones 1959 §§4–6, `HPC/BJ59/Zigzag.lean` … `Thm9.lean`, `DP61.lean`,
  `NonVac200.lean`, `NonVac200b.lean`, collected by `HPC/BJ59/BJ59C.lean`):
  * **the homeomorphism of Bing–Jones pp. 188–189** for any two sequences of chains with
    Conditions B and B′ (`HPC.BJ59.zigzag_homeomorph`), and Condition A's consequence
    (`zigzag_fibre`);
  * private points (`exists_privatePoint_interior`, `exists_privatePoint_shrink`); Step 1(b) of
    Theorem 10 (`bj_step1b`);
  * **Bing–Jones Theorem 8** (`bj_theorem8`, continuous arcs, `n ≥ 3`) and its corollary
    (`bj_theorem8_cor`);
  * **Bing–Jones Theorem 9** (`bj_theorem9`, with `bj9_base` for the two simplifications);
  * Domokos–Prajs Theorem 6.1 in both directions, from `BJThm10` and `BJPlaneExample`
    (`dp22_theorem61_iff`), with the transport lemma `IsAtomicCircPAMap.comp_homeomorph`;
  * the certificate that Theorem 7's printed reduction fails for three links
    (`bj_theorem7_proof_n3`).

  Open: the named inputs `BJThm10`, `BJPlaneExample` (see `OPEN.md`). Nothing of the batch-200
  skeleton is left open.
* Part G, IV (batch 201; Bing–Jones 1959 §6, Theorem 10, `HPC/BJ59/Thm10Defs.lean` …
  `Thm10Step.lean`, `NonVac201.lean`, `NonVac201b.lean`, collected by `HPC/BJ59/BJ59D.lean`):
  * the conditions of the construction (`HasPrivatePoints`, `IsFibreChainMap`, `EndCompat`,
    `IsFibreFine`) and the tools: points of a link only (`exists_point_only_of_minimal`),
    Theorem 6 in the form used (`adjacent_of_properCover`), fibre-fineness
    (`isFibreFine_of_isEpsChain`), the chain map of Step 2(b) (`exists_pattern`), the corollary to
    Theorem 8 on a sub-arc (`bj_theorem8_cor_sub`), the repaired Theorem 5 on a window
    (`bj_theorem5_window`, with `exists_window_set`);
  * the step of Steps 2–5 (`BJStep`, `bj_step`) and the induction (`bjThm10_of_step`);
  * **Bing–Jones Theorem 10**: the named input `BJThm10` is now a theorem (`HPC.BJ59.bjThm10`);
  * **the classification of homogeneous plane continua with Domokos–Prajs's third class, with no
    named hypothesis** (`ho16_classification_atomic'`); each circle of pseudo-arcs is homogeneous
    and any two are homeomorphic (`isHomogeneous_of_isCircleOfPA'`,
    `homeomorph_of_isCircleOfPA'`); the classification with Bing–Jones's third class and its
    plane form from `BJPlaneExample` alone (`ho16_classification₃`, `ho16_classification_plane₃`).

  Open: the named input `BJPlaneExample` (see `OPEN.md`). Nothing of the batch-201 skeleton is left
  open.
* Part G, V (batch 202; Bing–Jones 1959 §7, a plane circle of pseudo-arcs, by a construction that
  is not Bing–Jones's; `HPC/BJ59/CircDescr.lean` … `CircPlane.lean`, `Sweep.lean`,
  `SweepPattern.lean`, `Sweep3.lean`, `NonVac202.lean`, `NonVac202b.lean`, `NonVac202c.lean`, collected by
  `HPC/BJ59/BJ59E.lean`):
  * circular descriptions (`CircDescr`) and the recognition theorem: a circular description
    describes a circle of pseudo-arcs (`CircDescr.isCircleOfPA`);
  * the sweep lemma (`sweep_lemma`, at most two events, as used; `sweep_lemma3`, at most three
    events, the commission's bound, sharp by `nonvac_sweep_four_events`) and the sweep patterns
    (`exists_sweepPattern`);
  * the standard circular chains (`stdCircLink`, `stdCircLink_meet_iff`) and the circular planar
    step (`circ_step`);
  * the assembly: a circular description in the plane (`exists_circDescr_plane`), hence
    **a plane circle of pseudo-arcs**: the named input `BJPlaneExample` is now a theorem
    (`HPC.BJ59.bjPlaneExample`);
  * **the classification of homogeneous plane continua with Bing–Jones's third class, and its
    plane form, with no named hypothesis** (`ho16_classification₄`, `ho16_classification_plane₄`),
    Domokos–Prajs Theorem 6.1 in both directions (`dp22_theorem61'`, `dp22_theorem61_iff'`) and
    `hoCircleLike'`;
  * non-vacuity, including non-degenerate witnesses for `BJThm10`, `BJStep`,
    `bj_theorem8_cor_sub`, `bj_theorem5_window` from a half of the plane example, and a sweep walk
    with four events that is not crooked (`nonvac_sweep_four_events`).

  Open: `isAtriodic_of_atomic` (batch 199, optional). No named input of Part G remains (see
  `OPEN.md`).

Toolchain: as pinned in `lean-toolchain` (Lean `v4.28.0`) and `lake-manifest.json` (Mathlib).

What is proved, what is refuted and what is open is stated by `axioms.txt` and nothing else: this
README makes no claim beyond it.

Bing's Duke Theorem 11 is proved by Fugate's Case II argument (`HPC.Plane.theorem11_1951`,
`HPC/Plane/Theorem11B.lean`). Bing's Theorem 14 is proved by his own alternating construction, with
the covering descriptions supplied by Lehner's Lemma 3 (`HPC.Description.theorem14`,
`HPC/PseudoArc/Thm14.lean`).

## Dependency census (batch 203)

What the classification uses (`doc/depcensus/`, report `doc/batches/REPORT-batch203.md`). The
joint closure of `ho16_classification_plane₄` and `ho16_classification₄` uses 4689 of the 11697
counted declarations of the three `lean_lib`s (40.1 %), in 446 of 863 modules, covering 92845 of
255835 source lines (36.3 %); 417 modules have no used declaration. Its 12480 library constants,
replayed through the kernel into an environment built from Mathlib, `Init` and Batteries alone
(`scripts/Replay.lean`), are all accepted, and the two statements of `HPC/BJ59/BJ59E.lean`
elaborate there to exactly the replayed types. Regenerate with `lake env lean
scripts/DepCensus.lean` (see `doc/depcensus/README.md`); `scripts/closure.py` recomputes the counts
independently.

## Building

```
lake build HPC          # the main line and the open targets (default target)
lake build HPCCensus    # optional: the native_decide census theorems
lake build HPCArchive   # optional: exploratory files kept compiling
lake env lean Axioms.lean > axioms.txt   # regenerate the audit
```

## Layout

| path | content |
|---|---|
| `HPC.lean` | root of the main build: the verified main line and the open targets |
| `HPC/Chains`, `HPC/Covers`, `HPC/Fold`, `HPC/PseudoArc`, `HPC/Plane`, `HPC/Effros`, `HPC/Jones`, `HPC/Moore`, `HPC/Hagopian` | the main line (`HPC/Hagopian`: Part E, Hagopian 1975, Moore's triod theorem and Hagopian 1976 §2; `HPC/Effros`: Part C, the Effros theorem; `HPC/Jones`: Part D, Jones 1948, Jones 1951 (the Lemma and Theorem 1), Jones 1941 Theorem 4, Whyburn 1939 (6.1), (6.2), (6.21), upper semicontinuous decompositions, Jones 1955 Theorems 1 and 2, Jones 1949 Theorems 1 and 2, the Jordan curve theorem, order of points, Menger's theorem on curves of order 2, Whyburn (9.1); `HPC/Moore`: Part D, Moore 1916 §§2–7 and Moore 1919, ending with `m19_plane`; Part E, Moore 1925 §I) |
| `HPC/Span` | Theorem C I (batch 191): span, Cook 1967 Theorem 4, Davis 1.1 for hereditarily indecomposable continua, Oversteegen–Tymchatyn 1982 Theorem 3.6 and Corollary 3.5 from Theorem 3.2; Theorem C II (batch 192): the strip lemma, Theorem 3.2 in strip form, `theoremC` |
| `HPC/HO16` | H–O Theorem 1, I (batch 193): PL graphs, fans, `HOThm20`; K–M Lemma 2; the core of H–O Theorem 8; H–O Theorem 4 in path form; grid graphs and paths in the plane; the pseudo-arc from `HOThm20`; H–O Theorem 1, II (batch 194): PL-graph library, simple folds, Lemma 6, Theorem 8 for folds, Proposition 7; H–O Theorem 1, III (batch 195): sides, Propositions 10, 11, straight sets, stairwell structures, Claim 14.1, Proposition 17, Lemma 18, the fold of Proposition 19; H–O Theorem 1, IV (batch 196): ordinary points of folds, Proposition 19, Theorem 20 from `HOThm15`; H–O Theorem 1, V (batch 197): ladders, Theorem 15, Theorem 20, the indecomposable case of the classification |
| `HPC/BJ59` | Part G, I (batch 198): Bing–Jones 1959 §§2–4 (arcs of continua, circles of pseudo-arcs, Theorems 2–6), the halves and gluing of circles of pseudo-arcs, the decomposable case and the classification from the named inputs `BJThm10`, `HOCircleLike`, `BJPlaneExample`; Part G, II (batch 199): atomic maps, Domokos–Prajs Theorem 6.1 (from `BJThm10`), the classification from `BJThm10` alone, `HOCircleLike` from `BJThm10` and `BJPlaneExample`, Bing–Jones Theorem 7, the general certificate against Theorem 5 as printed, `IsBJChain ↔ IsTaut`; Part G, III (batch 200): the homeomorphism of pp. 188–189, private points, Step 1(b), Bing–Jones Theorems 8 and 9 and the corollary to Theorem 8, Domokos–Prajs Theorem 6.1 in both directions (from `BJThm10`, `BJPlaneExample`), the certificate for Theorem 7's proof with three links; Part G, IV (batch 201): Bing–Jones Theorem 10 (`bjThm10`) and the classification with Domokos–Prajs's third class with no named hypothesis; Part G, V (batch 202): circular descriptions, the sweep patterns, the circular planar step, a plane circle of pseudo-arcs (`bjPlaneExample`) and the classification with Bing–Jones's third class with no named hypothesis |
| `HPC/Census/`, `HPCCensus.lean` | the `native_decide` census theorems (not imported by `HPC.lean`) |
| `HPC/Archive/`, `HPCArchive.lean` | exploratory files no main-line theorem depends on (not imported by `HPC.lean`) |
| `Axioms.lean`, `axioms.txt` | the single axiom audit, grouped by paper |
| `OPEN.md` | the open items (the only `sorry` of the main build, and open statements recorded as `Prop`s) |
| `LEDGER.md` | the refutations: false statements of the sources and of the commissions, with the Lean theorem refuting each |
| `doc/batches/` | the commissions, reports and notes of the 166 batches; `skeletons/` (uploaded skeletons), `audits/` (per-batch audits) |
| `doc/census/` | census, check, probe and witness programs and logs, with a README saying which report cites which file |
| `doc/exposition/` | `pseudoarc-bing-exposition.pdf`, `Theorem3-formalized-proof.{tex,pdf}` |
| `doc/sources/` | the Nadler excerpts used for batch 102; Fugate 1969 (batch 104); Bing 1948, Amer. J. Math., the arcs paper (batch 108); Ingram 1968 (batch 132); van Mill 2004 (batch 134); Jones 1948, 1951, 1955 (batch 135); Jones 1941, Whyburn 1939 (batch 136); Moore 1916 (batch 137); Moore 1919; Moore 1925, Trans. AMS, and Moore 1925, Math. Z., the prime parts (batch 145); Mullikin 1922, Moore 1920, Moore 1924 (P.C.S.) (batch 146); Jones 1949 (batch 147); Whyburn 1942, *Analytic Topology* (`whyburn1942.pdf`, batch 148); Menger, *Kurventheorie* (`menger-kurventheorie.pdf`), Wilder 1938 (`wilder1938.pdf`) (batch 149); Moore 1922, Fund. Math. 3, the scan and the commissioner's transcription (`moore1922.pdf`, `moore1922-transcription.pdf`, batch 150); Hagopian 1984, Pacific J. Math. 113 (`hagopian1984.pdf`, batch 184); Jones 1975, Houston J. Math. 1 (`jones1975.pdf`, batch 186); Oversteegen–Tymchatyn 1982, Houston J. Math. 8, and Cook 1967, Fund. Math. 60 (`oversteegen-tymchatyn1982.pdf`, `cook1967.pdf`, batch 191); Hoehn–Oversteegen 2016, Acta Math. 216, and Krasinkiewicz–Minc 1977, Bull. Acad. Polon. Sci. 25 (`hoehn-oversteegen2016.pdf`, `krasinkiewicz-minc1977.pdf`, batch 193; not in git); Lelek 1979, Topology Proc. 4 (`lelek1979.pdf`, batch 194; not in git); Bing–Jones 1959, Trans. AMS 90 (`bing-jones1959.pdf`, batch 198; not in git); Domokos–Prajs 2022, arXiv:2203.15906 (`domokos-prajs2022.pdf`, batch 199; not in git); the eight sources missing from the batch-199 delivery's `doc/sources/` (`bing-jones1959.pdf`, `cook1967.pdf`, `domokos-prajs2022.pdf`, `hagopian1984.pdf`, `hoehn-oversteegen2016.pdf`, `jones1975.pdf`, `lelek1979.pdf`, `oversteegen-tymchatyn1982.pdf`) restored in batch 200 (PDFs are not in git) |
| `doc/theorems-3-4-scheduling.md` | the project notes (latest copy) |

## Axiom policy

* Everything imported by `HPC.lean` uses only the standard axioms `propext`, `Classical.choice`,
  `Quot.sound`, except the declarations listed in `OPEN.md` and the theorems that depend on them,
  which also show `sorryAx`. `axioms.txt` records this declaration by declaration.
* `native_decide` (axioms `Lean.ofReduceBool`, `Lean.trustCompiler`) occurs only under
  `HPC/Census`, and nothing in `HPC.lean` depends on it.
* The programs under `doc/census` are not part of the build; a finite fact counts as verified only
  where a Lean theorem states it.

## Naming conventions

* `foo'` — a corrected or alternative form of `foo`; where a statement was superseded (batch 103),
  the proved version carries the unprimed name and the primed name is kept as an `alias`.
* `foo_of` / `foo_of_bar` — a conditional theorem: `foo` with a named hypothesis (often an open
  lemma, or the statement of another theorem) as an explicit assumption.
* `foo_false`, `foo_refuted`, `not_foo`, `not_foo_literal` — a refutation of the statement `foo`
  (see `LEDGER.md`).

See `OPEN.md`, `LEDGER.md` and `doc/exposition` for details; `doc/batches/README.md` is the previous
README.
