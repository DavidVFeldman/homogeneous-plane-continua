# Defects ledger

**Sources.** Bing 1948; Bing 1951 (Duke and Pacific); Fugate 1966 and 1969; Lehner 1961;
Ingram 1968; van Mill 2004 (the Effros theorem, Part C of the classification); Jones 1948 and
1951 (Part D foundations); Jones 1955 Theorem 1; Whyburn 1939 §6; Hagopian 1975, 1976 and 1984
and Jones 1975 (Part E); and the textbooks used alongside them. Verified: Hoehn–Oversteegen
2016 Theorem 1 (Part F, batches 193–197), with Krasinkiewicz–Minc 1977 and Lelek 1979 (A.26);
Oversteegen–Tymchatyn 1982 and Cook 1967 (Theorem C, A.29). Bing–Jones 1959 (Part G, A.25):
Theorems 1–10, the corollary to Theorem 8 and the passage to circles verified (batches 198–201);
the claim of §7 (a plane circle of pseudo-arcs) verified by a construction of my own, not
Bing–Jones's (batch 202). Domokos–Prajs 2022 Theorem 6.1 (A.27) verified in both directions
(batches 199–202). **The classification of homogeneous plane continua, in Bing–Jones's form and in
its plane form, is verified with no named hypothesis (batch 202).** A dependency census of the two
final theorems (batch 203) lists what they use, declaration by declaration, and replays their
closure through the kernel from Mathlib alone (Part D, "Census"). Read, not yet formalized: the
rest of the later literature on the steps of Parts F–G (A.27).

**Status.** As of batch 203 (2026-10-22). Repository `HPC`, Lean 4.28.0 with Mathlib. The build has
no `sorry`: `axioms.txt` has 4030 lines, and `sorryAx` appears in none of them. Since batch 178 the
project download has often not carried the committed work; each batch's work arrives as a published
tarball of its changed files, which I overlay on the previous tree. The batch-187 and
batch-188 downloads were stale; the batch-189 and batch-190 downloads were current (their
`axioms.txt` files equal the overlays, 2479 and 2550 lines); the batch-191 download was stale again
(2550 lines; the overlay has 2595); the batch-192, batch-193 and batch-194 downloads were current
(2658, 2712 and 2824 lines). The first download sent for batch 195 (`aristotle_72`) is identical
to the batch-194 download (same run, same `axioms.txt`, no batch-195 files); the second
(`aristotle_74`) is current (2942 lines, equal to the overlay). The batch-196 to batch-202
downloads (`aristotle_75` to `aristotle_81`) are current (3176, 3385, 3507, 3624, 3710, 3776 and
4030 lines). The batch-203 download (`aristotle_82`) is current (4030 lines, unchanged; no file
under `HPC/` changed) and lacks the same 72 Lean files, which its tarball carries unchanged.
The batch-197 to batch-199 downloads lack eight sources under `doc/sources/` and the batch-199
copies of the commission and skeleton; batch 200 restores them. The downloads of batches 199 and
200 also carry stale copies of eight files under `HPC/Hagopian/` (one of them with a `sorry` for
`hagopian76_theorem1`, which `Jones75B.lean` proves) and lack 64 Lean files of the project (54
under `HPC/Hagopian/`, five each under `HPC/Jones/` and `HPC/Span/`); `axioms.txt` lists their
declarations, with no `sorryAx`, so the build used the current files. The batch-201 download has
the same gaps, but its tarball carries current copies of every file under `HPC/Hagopian/`,
`HPC/Jones/` and `HPC/Span/` (identical to the tree's). The batch-202 download no longer carries
the eight stale copies and lacks 72 Lean files (62 under `HPC/Hagopian/`, five each under
`HPC/Jones/` and `HPC/Span/`); its tarball again carries current copies of all of them (258 files,
identical to the tree's), and every Lean file the download does carry equals the tree's. After my
working container was replaced during the batch-183 audit, I rebuilt the tree from the batch-177
download with tarballs 178–183 overlaid; the line counts after each overlay match the earlier
audits.

**Route (David's decision, 2026-10-17).** From batch 187 the batches stay on the 1984 route; the
alternation of batches 184–186 ends.

**Batch 202: the plane example; the classification is complete (A.25).** 254 new theorems (231
on the three standard axioms, 22 on `propext` and `Quot.sound`, 1 on `propext`); all 25
declarations of the skeleton proved with the skeleton's statements; nothing commented out. The
example is my construction, not Bing–Jones's (commission 202 §1; A.25, sixth reading). Verified:
* **the recognition theorem** (`CircDescr.isCircleOfPA`): nested circular chains refining along
  lifted patterns, whose links carry arcs of the base circle satisfying nesting, survival and
  crookedness of runs, describe a circle of pseudo-arcs;
* **the sweep lemma** (`sweep_lemma`, two events; `sweep_lemma3`, three events, sharp: a sweep walk
  with four events that is not crooked, `nonvac_sweep_four_events`) and the sweep patterns
  (`exists_sweepPattern`);
* **the circular planar step** (`circ_step`): an equivariant shear on the universal cover,
  descended through `circExp`;
* **a plane circle of pseudo-arcs** (`exists_circDescr_plane`, `bjPlaneExample : BJPlaneExample`);
* with no named hypothesis: **the classification of homogeneous plane continua with Bing–Jones's
  third class** (`ho16_classification₄`) **and its plane form** (`ho16_classification_plane₄`:
  there are plane continua `C₁`, `C₂`, `C₃` — a simple closed curve, a pseudo-arc, a circle of
  pseudo-arcs — each homogeneous, pairwise non-homeomorphic, and a nondegenerate plane continuum
  is homogeneous iff it is homeomorphic to one of them); Domokos–Prajs 6.1 in both directions
  (`dp22_theorem61'`, `dp22_theorem61_iff'`); `hoCircleLike'`;
* the non-degenerate witnesses missing in batch 201 (`exists_snakeArcPA`: a half of the plane
  example is a continuous snake-like arc of pseudo-arcs; `nonvac_bjThm10`, `nonvac_bjStep`, …).

Nothing counted (A.25). No named input of the classification remains. Optional items left:
Domokos–Prajs's atriodicity (`isAtriodic_of_atomic`), the certificate of commission 202 §4.4, and
a certificate for BJ.43.

**Check of the final statements (2026-10-21).** An independent agent, reading sources only,
traced every notion in `ho16_classification₄` and `ho16_classification_plane₄` to Mathlib and
found the standard ones; it found no `axiom`, no `sorry` outside comments and no kernel-weakening
option in `HPC/`, and every named hypothesis on the path discharged by a theorem. To clean up:
stale skeleton copies with `sorry` at the repository root (not built). Scheduling notes §245.

**Batch 201: Bing–Jones Theorem 10 (A.25).** 66 new theorems (63 on the three standard axioms, 2
on `propext` and `Quot.sound`, 1 on `propext`); every declaration of the skeleton is proved, 20 of
21 with the skeleton's statement and `exists_pattern` in a stronger form (the skeleton's form is
`exists_pattern_skeleton`). Verified with no named hypothesis:
* **Bing–Jones Theorem 10** in the fibre-preserving form `BJThm10` (`bjThm10`): one step of the
  induction (`bj_step`, the statement `BJStep`), applied alternately from one-link chains
  (`bjThm10_of_step`), through the homeomorphism of pp. 188–189 (`zigzag_homeomorph`);
* **the classification of homogeneous plane continua with Domokos–Prajs's third class**
  (`ho16_classification_atomic'`): a non-degenerate plane continuum is homogeneous iff it is a
  simple closed curve, a pseudo-arc, or has an open atomic map onto the circle with pseudo-arc
  fibres;
* every circle of pseudo-arcs is homogeneous, and any two are homeomorphic
  (`isHomogeneous_of_isCircleOfPA'`, `homeomorph_of_isCircleOfPA'`); Domokos–Prajs 6.1, "if",
  as the term `dp22_theorem61 bjThm10` (no declaration of batch 201 states it; commission 202
  asks for one);
* the tools: Theorem 6 in the form Step 2(c) uses, the pattern of a map of a fibre (Step 2(b)),
  the corollary to Theorem 8 on sub-arcs (one link or at least three), Theorem 5 on windows, small
  transition sets.

Verified with `BJPlaneExample` as the only named hypothesis: the classification with Bing–Jones's
third class (`ho16_classification₃`) and its plane form (`ho16_classification_plane₃`). Theorem 9
is not used in Theorem 10. Nothing counted (A.25). The named input left: `BJPlaneExample`.

**Batch 200: Bing–Jones's homeomorphism of pp. 188–189, Theorems 8 and 9 (A.25).** 86 new
theorems (82 on the three standard axioms, 1 on `propext` and `Quot.sound`, 1 on `propext`, 2 on
none); every declaration of the skeleton is proved with the skeleton's statement, and nothing is
left open. Verified with no named hypothesis:
* the homeomorphism of pp. 188–189 as a lemma about any two sequences of chains with Conditions B
  and B′ (`zigzag_homeomorph`), with its fibre form for Condition A (`zigzag_fibre`);
* private points: every interior link of a chain in Bing–Jones's sense properly covering a
  connected set has one (`exists_privatePoint_interior`), and any such chain covering a
  non-degenerate continuum can be shrunk so that every link has one
  (`exists_privatePoint_shrink`);
* Step 1(b) of Theorem 10 (`bj_step1b`);
* Theorem 8 for continuous snake-like arcs of pseudo-arcs and chains of three or more links
  (`bj_theorem8`), and its corollary with the arc as the whole space (`bj_theorem8_cor`);
* Theorem 9 as printed, for chains in Bing–Jones's sense (`bj_theorem9`, through `bj9_base`);
* the certificate that Theorem 7's printed reduction fails for three links
  (`bj_theorem7_proof_n3`).

Verified with `BJThm10` and `BJPlaneExample`: Domokos–Prajs Theorem 6.1 in both directions
(`dp22_theorem61_iff`). Theorem 8's non-vacuity is not given (a continuous snake-like arc of
pseudo-arcs is known here only under `BJPlaneExample`). Counted: Theorem 7's proof (BJ.19), the
eighteenth defective proof. The named inputs left: `BJThm10`, `BJPlaneExample`.

**Batch 199: the circle-likeness step; Bing–Jones Theorem 7 (A.25, A.27).** 114 new theorems
(96 on the three standard axioms, 16 on `propext` and `Quot.sound`, 2 on none) and the three
batch-198 `@[simp]` lemmas, now audited (all three standard axioms); every declaration of the
skeleton is as commissioned, except the two items left open. Verified with no named hypothesis:
* an atomic map onto `[0, 1]` whose fibres are snake-like and hereditarily indecomposable has a
  snake-like domain (`isSnakeLike_of_atomic'`, Bing's 1951 argument; no shape theory);
* a decomposable homogeneous plane continuum is a simple closed curve or has an open atomic map
  onto the circle with pseudo-arc fibres (`circle_or_atomic_of_decomposable`);
* Bing–Jones Theorem 7, first sentence, for every `n` (`bj_theorem7`), and second sentence for
  `n ≥ 3` (`bj_theorem7_ends`); a certificate that the second sentence as printed is false for a
  chain of one link (`bj_theorem7_ends_printed_false`);
* the general certificate against Theorem 5 as printed, from every instance with three or more
  links (`bj_theorem5_printed_false_general`).

Verified with Bing–Jones Theorem 10 (`BJThm10`) as the only named hypothesis: Domokos–Prajs
Theorem 6.1, "if" (`dp22_theorem61`); homogeneity and uniqueness of spaces with such maps; **the
classification with Domokos–Prajs's third class** (`ho16_classification_atomic`): a non-degenerate
plane continuum is homogeneous iff it is a simple closed curve, a pseudo-arc, or has an open
atomic map onto the circle with pseudo-arc fibres. With `BJThm10` and `BJPlaneExample`:
`HOCircleLike` (`hoCircleLike`), and the classification with Bing–Jones's third class and its plane
form (`ho16_classification₂`, `ho16_classification_plane₂`). Left open: Theorem 9 (the stretch
item) and Domokos–Prajs's atriodicity (optional). Counted: Theorem 7's second sentence, the
twenty-fourth false printed statement (Part D). The named inputs left: `BJThm10`, `BJPlaneExample`.

**Batch 198: Part G from the top, and Bing–Jones Theorems 1–6 (A.25).** 122 theorems declared in
sixteen files; the audit lists 119 of them and the reused `isUnicoherent_of_isSnakeLike`, all on
the three standard axioms; three `@[simp]` lemmas are missing from the audit (asked for in
commission 199). Every declaration of the skeleton is as commissioned. Verified with
three named hypotheses (`BJThm10`, Bing–Jones Theorem 10 in fibre-preserving form;
`HOCircleLike`, a decomposable homogeneous plane continuum is circle-like; `BJPlaneExample`, a
circle of pseudo-arcs lies in the plane):
* from `BJThm10`: any two circles of pseudo-arcs are homeomorphic, and each is homogeneous (the
  passage of pp. 173 and 189, by gluing the two halves);
* from `BJThm10` and `HOCircleLike`: **the classification** (`ho16_classification`): a
  non-degenerate plane continuum is homogeneous iff it is a circle, a pseudo-arc or a circle of
  pseudo-arcs;
* from all three: the plane form (`ho16_classification_plane`), with three plane examples, no two
  homeomorphic.

Verified with no named hypothesis: each non-degenerate Jones element of a decomposable
homogeneous plane continuum is a pseudo-arc (`isPseudoArc_Lset`), and the quotient map onto the
circle is open; the circle is homogeneous; Bing–Jones Theorems 2, 3, 4 and 6; Theorem 5 in a
repaired form (`f` open, and no fibre meets a link only inside `Ū`); a certificate that Theorem 5
as printed is false (a degenerate case; the non-degenerate construction is in prose). Bing–Jones
Theorem 1 is Nadler 12.2, already in the library. Theorem 5 is now counted as a false printed
statement (twenty-three; Part D). Still open in Part G: the three named hypotheses.

**Batch 197: Theorem 15; Part F is complete (A.26).** 209 theorems: 201 on the three standard
axioms, eight list lemmas on a subset of them; none with a named hypothesis. Verified: a ladder
(explicit sheets over a decomposition, zig-zags on one line, at most one wedge per edge) carries a
stairwell structure of odd height (`ho16_stairwell_of_ladder`); inside any open set containing a
separator there is a ladder (`exists_ladder`, replacing Claim 15.1); hence H–O Theorem 15
(`ho16_theorem15 : HOThm15`) and Theorem 20 (`ho16_theorem20 : HOThm20`). **Hoehn–Oversteegen's
main theorem for indecomposable continua is verified with no named hypothesis**
(`ho16_indec_homogeneous_pseudoArc`): every indecomposable non-degenerate homogeneous plane
continuum is a pseudo-arc. With Bing's homogeneity of the pseudo-arc (batch 88), the two-way form
(`ho16_indec_homogeneous_iff`): a non-degenerate plane continuum is homogeneous and indecomposable
iff it is a pseudo-arc. Its hypotheses are met (`exists_indec_homogeneous_plane`). What remains of
the classification: the circle-of-pseudo-arcs step and its converse (Part G, A.25, A.27).

**Batch 196: Proposition 19, and Theorem 20 from Theorem 15 (A.26).** 232 theorems, all on the
three standard axioms. Verified with no named hypothesis: ordinary points of a fold
(`IsSimpleFoldOf.isOrdinaryPt_iff`); Proposition 19, first in the full fold with H–O's sets of
p. 203 (`ho16_prop19_full`), then for a connected fold (`ho16_prop19`); a certificate that a
sentence of H–O's proof (p. 208) is false (`ho16_p208_false`). Verified with H–O Theorem 15 as the
only hypothesis (the named `Prop` `HOThm15`, stated for connected PL graphs): Theorem 20, forward
direction (`ho16_theorem20_of_thm15 : HOThm15 → HOThm20`, by an induction over the ambient normed
space, `ho16_lift_stairwell`), and every indecomposable non-degenerate homogeneous plane continuum
is a pseudo-arc (`homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`). **Theorem 15 is the only
open input of Part F.** The proof of Proposition 19 is counted as defective (p. 208; the
seventeenth), the proposition being true.

**Batch 195: sides, straight sets, stairwells (A.26).** 116 theorems; 115 on the three standard
axioms and one (a list lemma) on `propext` alone; none with a named hypothesis. Verified:
* components of `G \ (K ∪ P)`, ordinary points (order 2 in any decomposition), intersections and
  preimages of PL graphs;
* Definition 9 with the observations after it (the characterization of `σ_B(A)`), Propositions
  10 and 11;
* Definitions 12, 13 and 16 (`IsStraight`, `IsStairwellStr`, `IsBrokenStairwellStr`), checked
  clause by clause against the page images; the observations on components (relative to the
  component); Claim 14.1; the height-1 homeomorphism; Proposition 17 (with `k ≥ 3`); the remarks of
  p. 201; Lemma 18; and the first step of Proposition 19 with (19.1)–(19.3);
* a certificate that the remarks of pp. 193–194 fail without "G connected"; examples of a stairwell
  structure of height 3 and of a broken one.

Ten statements were proved with fewer hypotheses than the skeleton asked. `HOThm20` is still the
only hypothesis of `homeomorph_pseudoArc_of_indec_homogeneous`; still to do for it: Proposition 19
after its first step, Theorem 15, Theorem 20.

**Batch 194: the fold machinery of Hoehn–Oversteegen §§4–5 (A.26).** 112 theorems, all on the
standard axioms, none with a named hypothesis. Verified:
* a library for piecewise linear graphs: a common subdivision of finitely many segments; refinement
  of a graph so that given subgraphs are unions of edges and given points are vertices; unions,
  closures of differences, finite relative frontiers, components (finitely many, piecewise linear);
* simple folds exist over every fold triple (pp. 185–186), built from piecewise linear heights in
  `E × ℝ` instead of H–O's quotient (`exists_simpleFold`);
* Lemma 6, which H–O leave to the reader (`ho16_lemma6`);
* Theorem 8, (1) ⇒ (2), for simple folds (`ho16_theorem8`);
* Proposition 7 (`ho16_prop7`), with its three unargued steps supplied;
* certificates: Theorem 1 as restated on p. 211 and Theorem 1′ as printed on p. 212 fail for a
  one-point continuum. Theorem 1′ is now counted as a false printed statement (twenty-two; Part D).

`HOThm20` is still the only hypothesis of `homeomorph_pseudoArc_of_indec_homogeneous`. Still to do
for it: Definitions 9, 12, 13, 16; Propositions 10, 11, 17, 19; Lemma 18; Theorems 15 and 20.
Commission 195 asks for all of these except Proposition 19 and Theorems 15 and 20.

**Batch 193: Hoehn–Oversteegen Theorem 1 for plane continua, reduced to one named claim (A.26).**
54 theorems, all on the standard axioms. Verified, with the named `Prop` `HOThm20` (the forward
direction of H–O Theorem 20, for piecewise linear graphs) as the only hypothesis:
`homeomorph_pseudoArc_of_indec_homogeneous`, every indecomposable non-degenerate homogeneous plane
continuum is homeomorphic to a pseudo-arc; and H–O Theorem 1 ("if") for plane continua
(`ho16_theorem1_plane`). Verified with no named hypothesis on the way: Krasinkiewicz–Minc Lemma 2
for hereditarily indecomposable compacta (`km77_lemma2`); the core of H–O Theorem 8, (1) ⇒ (2)
(`ho16_theorem8_core`); H–O Theorem 4 in a path form (`ho16_theorem4`); a hereditarily
indecomposable plane set has empty interior; grid graphs and radial projections approximating a
plane compactum with empty interior. Tree-likeness (H–O's citations [31] and [46]) is not used.

**Batch 192: Theorem C is verified (A.29).** 63 theorems, all on the standard axioms.
`theoremC : TheoremC` has no hypotheses: every homogeneous indecomposable plane continuum has span
zero, in Hoehn–Oversteegen's sense. With it the strip form of O–T Theorem 3.2
(`ot82_theorem32 : OTThm32`), Corollary 3.5 and Theorem 3.6 (indecomposable case) are
unconditional, and the order of disjoint crossing continua (`crossing_traces_separated`) is
proved. The route replaces O–T's §2 at three places: the continua in zero sets by a common zero
found with a logarithm (`common_zero_rect`), Remark 2.5 and Lemma 2.4 by chains in the span
witness, and the Jordan-curve arguments by the crossing parity of polygons.

So Theorems A (Jones 1955), B (Hagopian 1976) and C (Oversteegen–Tymchatyn 1982) of
Hoehn–Oversteegen are all verified with no named hypotheses. What remains of the classification:
Hoehn–Oversteegen's Theorem 1 (Part F) and the circle-of-pseudo-arcs step (Part G). Commission
193 begins Part F (A.26, second reading).

**Batch 191: Theorem C reduced to one named claim (A.29).** 45 theorems, all on the standard axioms.
`theoremC_of_thm32 : OTThm32 → TheoremC` is verified, where `TheoremC` is Hoehn–Oversteegen's
Theorem C ("Every homogeneous indecomposable plane continuum has span zero", in their sense of span)
and `OTThm32` is a strip form of O–T Theorem 3.2 (the images lie in disjoint continua crossing the
strip). Verified on the way:
* Cook 1967 Theorem 4 (maps onto hereditarily indecomposable continua are confluent), by a proof
  that needs neither of the printed proof's unstated steps;
* Davis's zero span ⇒ zero semi-span, for hereditarily indecomposable continua (Brouwer reduction
  and Cook);
* O–T Theorem 3.6 (indecomposable case) from Corollary 3.5, without tree-likeness;
* Corollary 3.5 from `OTThm32`, with the re-embedding that O–T's "without loss of generality"
  needs, and the uncountable family of crossing continua.
The order of disjoint crossing continua along a side (`crossing_traces_separated`) is open; it is
an input of the proof of `OTThm32`.

**Batch 190: Part E is complete.** 71 theorems, all on the standard axioms. The arc step is
verified (`jones75_noArc : NoArcIndecHomPlane`) by the repaired planar route of commission 190
(A.28). Hence **Theorem 1 of Hagopian 1976 is verified with no named hypothesis**
(`hagopian76_theorem1 : Hagopian76Thm1`): every indecomposable homogeneous plane continuum is
hereditarily indecomposable. Verified with it, each with only the hypotheses of its statement:
* Bing 1960 for plane continua (`bing60_plane_uncond`): a homogeneous plane continuum that contains
  an arc is a simple closed curve;
* Hagopian 1976 Theorem 2 (`hagopian76_theorem2_uncond`): a homogeneous plane continuum that does
  not separate the plane is hereditarily indecomposable;
* Hagopian 1975's Corollary, Theorem 2 and the irreducible form of Theorem 1
  (`hagopian75_corollary_uncond`, `hagopian75_theorem2_uncond`,
  `hagopian75_theorem1_of_noArc_uncond`).

With Jones 1955 Theorem 2 (`jones55_theorem2'`, batch 154) this gives Theorems A and B of
Hoehn–Oversteegen. The combination (a homogeneous plane continuum is hereditarily indecomposable,
or has a continuous decomposition into homogeneous hereditarily indecomposable non-separating
continua with a simple closed curve as quotient) is not stated as one theorem in the repository.
What remains of the classification: Theorem C (Oversteegen–Tymchatyn 1982, A.29), Theorem 1 of
Hoehn–Oversteegen (Part F, A.26), and the circle-of-pseudo-arcs step (Part G, A.25–A.27).
Commission 191 starts Theorem C, top down: Theorem 3.6 and Corollary 3.5 from a strip form of
Theorem 3.2 (A.29).

**Batch 189: the arc step started (Jones 1975, A.28).** 65 theorems, all on the standard axioms.
They are stated for a compact metric space that is homogeneous, hereditarily unicoherent and
atriodic and contains an arc (`JonesSetting`); the dyadic solenoid satisfies these hypotheses, so
the theorems are not vacuous. The results:
* Jones's (c);
* arc components are lines (injective continuous images of `ℝ`), and homeomorphisms act on them
  monotonically;
* no small homeomorphism fixing a point reverses the line through it; small homeomorphisms carrying
  a line into itself preserve its orientation (these replace Jones's (f), whose proof is
  defective);
* every line lies in its forward and backward limit sets (Jones's (d), both directions);
* no backtracking near an arc in collar coordinates.

Aristotle's reconnaissance gives a hand proof of `NoArcIndecHomPlane` by a Poincaré–Bendixson
argument in a collar box. An independent check found an error in it near the edges of the box. A
repaired version, checked by me, is commission 190 (A.28).

**Batch 188: `Hagopian84Decomp` is verified** (`hagopian84_decomp`). This is Hagopian 1984
Theorem 1 with `N = M`, in the form the assembly uses. Hence Theorem 1 of Hagopian 1976 is
verified conditionally on one named claim, the arc step `NoArcIndecHomPlane` (Bing 1960 for
indecomposable continua; planned source Jones 1975): `hagopian76_theorem1_jones`. Batch 188 adds 22
theorems, all on the standard axioms:
* the transfer lemma (my route, commission 188 §2): through a point of `⋃𝒫(Zᵢ)′`, a member of
  `Ω(𝒫)` is a layer of a strand of `𝒫(Zᵢ)`. It is Lemma 16′ applied to a piece of a strand of `𝒫`.
  It replaces the printed appeals to Lemma 7 (A.24, H84.30 and H84.32);
* the decomposition `𝔇` and its disjointness, claims (5) (where (6) uses it) and (6), and the
  fields of the package (u.s.c., connected proper classes, invariance, the arc);
* the printed `⋃𝔅 = M`, as a corollary of the finite cover (H84.29).

Batch 187 (the 1984 route) added 86 theorems, all on the standard axioms:
* Lemma 13 as printed, with regularity. Its unargued steps are all true; the orientation argument
  for regularity is not in the text (A.24).
* Lemma 16′, my replacement for the one use of Lemma 16 (A.24, "Lemma 16"). Lemma 16 as printed
  follows from it, with normality added.
* The bridge `J(Z)` (without the printed positions of its end sets), the chain `𝒫(Z)` with
  `Z ∈ Δ(𝒫(Z))`, and a finite cover of `M` by `⋃Δ(𝒫)` and finitely many `⋃Δ(𝒫(Zᵢ))`.

After batch 187, what remained of `Hagopian84Decomp` was the decomposition `𝔇`, its disjointness,
claims (5)–(6) and the fields of the package; batch 188 proved them.

Batch 186 (the 1984 route) added 45 theorems, all on the standard axioms:
* the quotient package: `Hagopian84Decomp` from a Jones decomposition (`IsJonesDecomp84`), with
  homogeneity by an orbit argument;
* 1984 Lemma 12, Lemmas 14 and 15 (Lemma 15 with a smaller `ε`; "By Lemma 3" does not suffice as
  printed), the note on p. 341, the positivity of `½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`, and an interval of layers
  for the arc in `M/𝔇`;
* the combinatorics of the fold in Lemma 13 (5).

Lemmas 13 and 16 were then open; batch 187 proved them.

Batch 185 added 62 theorems, all on the standard axioms:
* the two-sided extension (open since batch 158) and 1984 Lemma 7 (A.24), by a route other than
  the printed one;
* saturation (2e) for Hagopian's `F`, with no hypotheses: the end-layer case, open since batch 178,
  is closed by Lemma 7 (A.23);
* the case split for `i ≥ 3` ("The proof now breaks down into two cases"), by the route of
  commission 185, without Lemma 7; the same argument puts `d⁻¹(x₃)` on a side segment;
* rigidity and translate runs;
* the reduction `hagopian76_theorem1_of_cases4`.

Batch 184 started the second route to Hagopian 1976 Theorem 1, Jones's plan as carried out in
Hagopian 1984 (A.24). It added 17 theorems: Theorem 1 of 1976 from two named claims
(`hagopian76_theorem1_of_jones`: Jones's decomposition, and "no indecomposable homogeneous plane
continuum contains an arc"); the plane quotient (Moore 1925); Hagopian 1975 Theorem 1 with its
paragraph 4 supplied (A.22); 1984 Lemmas 1, 6 and 11.

Hagopian 1976 Lemmas 1–9 are verified. Theorem 1 is verified by the 1984 route (batch 190). The
1976 route was not completed: by a verified theorem (`hagopian76_theorem1_of_cases4`) it is
reduced to four named claims, which stay open:
* the frame of E0–E1 (`StepFrame`);
* the claims of the last step (`LastStepClaims`);
* the claims of Cases 1–2, with E2.4 replaced by three sub-claims (`Case1ClaimsE24`,
  `Case2ClaimsE24`; `E24Claims`: essential, a far layer, far from `π⁻¹(p₄)`).

Saturation and the case split, which batch 183's reduction still assumed, are proved. Report 185 §7
gives the two non-vacuity checks for each claim. Cases 1–2 of Hagopian follow Bing 1960
pp. 225–227 (A.23). Of Bing's reasons, the arc `ab` carries over to continua. Two do not: that the
strands end on the side lines, and the parity of crossings of a simple closed curve. The first is
the "between" step, still open after batch 185. The batch-176 conditional theorem was vacuous; its corrected form is verified.

**A second proof of Theorem 1 exists (found in my batch-183 audit).** Hagopian, *Atriodic
homogeneous continua*, Pacific J. Math. 113 (1984), 333–347, Corollary 3, re-proves Theorem 1 by
F. B. Jones's 1969 plan. It does not use the case analysis of pp. 348–349 (A.23, "Other proofs";
A.24). Batches 184–186 alternated between the two routes; from batch 187 they stay on the 1984
route.

**A lemma for both routes (batches 184–185).** 1984 Lemma 7 says that when two type λ continua `E`,
`F` overlap without either containing the other, every layer of `E` that meets `F` is a layer of
`F`. Hagopian 1976 has nothing of this kind at end layers; its Lemma 3 covers interior layers only.
In my batch-184 audit I read Lemma 7 as closing the end-layer case of saturation (A.23, "The end
layer of `F`", open since batch 178); batch 185 confirmed this. My second reading, that Lemma 7
makes `F` run along translates of `E` across the side segments, is not yet confirmed: the runs are
proved, but `F` leaving `D` along a translate (report 185 §3.3) is open.

**The circle-of-pseudo-arcs step (2026-10-17, a search of David's collection).**
Hoehn–Oversteegen's Theorem 2 needs "decomposable with pseudo-arc elements ⇒ the circle of
pseudo-arcs", and cites nothing for it (A.26). Prajs 2000 shows that planarity and dimension 1 do
not give it (A.27). A route that uses homogeneity has two steps.
* Jones's elements are terminal. This is Jones 1955 Theorem 1 (c), already verified
  (`jones55_c`).
* Continuous curves of terminal pseudo-arcs over the same quotient are homeomorphic (Lewis 1985,
  not yet obtained).

In the same search I found that Oversteegen–Tymchatyn's proof of Theorem C uses Rogers 1981, which
I had listed as background only (A.27).

**Scope.** This document reorganizes the repository's `LEDGER.md` and the project notes by source.
It separates two kinds of item:

* **Part A**: defects in the published texts.
* **Part B**: refuted *readings and reformulations*. These are statements this project put forward
  while trying to formalize a source. They are not claims of the source.

"Verified" means compiled with a clean axiom audit (`propext`, `Classical.choice`, `Quot.sound`
only). Lean names are in the namespaces `HPC.Fold`, `HPC.Plane` and `HPC`. File paths are
relative to `HPC/`; the Effros material is in `HPC.Effros`.

## Status vocabulary

Each entry carries exactly one of the following labels.

| label | meaning |
|---|---|
| **False as printed** | The printed statement is refuted by a verified counterexample. |
| **Proof defective; statement true** | The printed proof fails at an identified step. The statement is proved by a repaired argument. |
| **Unstated step** | The proof uses a fact that the paper neither states nor proves. The fact is true and is proved in the repository. |
| **Unargued sentences** | Sentences of the proof are asserted without argument. Each is supplied (or shown unnecessary) in the repository. |
| **Stated without proof** | No proof is given. Its status in the repository is recorded. |
| **Not established** | An assertion of a proof sketch that the repository neither proves in the generality stated nor refutes. |
| **Harmless mismatch** | Wording that disagrees with itself or with a cited source, without consequence for the results. |

Two distinctions are kept throughout:

* "a special case of the *theorem* fails" (the statement is false) versus "a special case of the
  *proof* fails" (the statement may still be true);
* defects of the source versus defects of a transcription of the source.

---

## Part A. Defects in the published texts

### A.1 R. H. Bing, *A homogeneous indecomposable plane continuum*, Duke Math. J. 15 (1948), 729–742

Every numbered statement is settled, and Theorems 1–15 are proved, with the exceptions recorded
below; Theorem 9 is verified with its mesh clause weakened (A.1.5).

**A.1.1 Theorem 3 (p. 732): proof defective; statement true.**
* *Statement.* Proved as printed, in every clause:
  * `theorem3_literal` (`Fold/Theorem3Pair.lean`), through the pair form `theorem3_pair`;
  * the end clause in Bing's "or" wording, `Recon121.theorem3LiteralOr_holds`;
  * the two-link form, `theorem3_bing`.
* *Defect.* The proof fails in its special case (p. 732).
  * Certificate: `Recon121.seam_every_H_fails`, with `seamD_special`, `seamD_hk`, `seamIH_H0` and
    `seam_Cbot_fails`.
  * Eleven links of a realized chain over five coarse links satisfy the special-case hypotheses,
    with `(h, k) = (4, 6)` forced.
  * A chain `H` satisfying the induction hypothesis exists.
  * Yet for every basepoint `i ≤ h` and every such `H`, the chain Bing writes down,
    `F = H(1, u−1) ⌢ (level groups of D′) ⌢ D(k+1, n)`, is not a chain with `d_i` first.
* *Repair.* Batch 122, `Recon122.bing_main`. Three changes, none of them in the text:
  1. the level groups are read bottom-anchored (`cbotG`);
  2. an explicit grouping is made when there are five coarse links (`special_five`);
  3. the branch `d_i ∈ D(h, k)` is handled by the induction hypothesis applied to `D(h, k)` inside
     `E(2, r−1)` (`special_middle`).
* *History.* Theorem 3 took about 70 batches (17–124). The many refuted intermediate statements
  belong to Part B.2, not here.

**A.1.2 Theorem 4 (p. 733): false as printed for m = 3; true for m ≥ 4.** Here m is the number of
links of the coarse chain. There are two independent failures at `m = 3`.
* *Degenerate case `r = s`.*
  * Certificate: `not_theorem4Literal`, `theorem4_two_degenerate_false`
    (`Fold/Theorem4Two.lean`).
  * Three intervals in ℝ are crooked in three intervals, and the middle fine link meets the first
    and the last coarse link.
  * So `D(r, s) = d_r` satisfies the hypothesis.
  * Requiring `d_r` to lie in both the first and the last link of `F` forces `F` to have a single
    link, all of `D`, which lies in no two adjacent links of `E`.
* *Only-clauses, `r < s`.*
  * Certificate: `not_theorem4LiteralND` (`Fold/Theorem4Only.lean`).
  * The example lives in ℕ with the discrete topology. Coarse links: `{0,1,5}`, `{1,2,4,5}`,
    `{2,3,4}`. Fine links: `{5}`, `{4,5}`, `{2,3,4}`, `{1,2}`, `{0,1}`. Take `r = 0`, `s = 1`.
* *What holds.*
  * The two-link form is proved under `r < s ∨ m ≠ 3` (`theorem4_two`).
  * The statement as printed, every clause, is proved for `m ≥ 4` (`theorem4_literal_ge4`,
    `theorem4LiteralGe4_holds`).
* *Classification.* This is a special case of the *theorem* that fails.

**A.1.3 Theorem 8: false as printed.**
* Certificate: `not_theorem8_literal` (`Fold/Theorem8Counter.lean`).
* Two six-link chains are crooked in a four-link chain and follow `bingPattern 4`, but the unions
  of their corresponding links form no chain.
* Corrected form: `theorem8`.

**A.1.4 Theorem 14: unargued sentences; not-established assertions.**
* *"That there exist such sequences follows as a consequence of Theorem 9."* This is not a proof.
  * The covering descriptions are supplied by Lehner's Lemma 3 for `n = 2` (Lehner 1961,
    pp. 375–376), verified as `lehner_lemma3_two` (`PseudoArc/Lehner.lean`, batch 114).
* *Not established.* Two assertions of the sketch are not established for an *arbitrary* covering
  description:
  1. there is a point `A` with `X_{1,j}(P₁, A) ⊆ Y_{1,1}(P₁, R₁)` and
     `cl x(1,j)_A ⊆ y(1,1)_{P₁}`;
  2. `Y_{2,2}(P₂, R₂) ⊆ Y_{2,1}(P₂, R₂)`.

  Both hold for the description Lehner's construction produces (`CoversUpToA`,
  `Description.exists_description_coveringA`, `PseudoArc/Thm14.lean`, batch 115).
* *Steps the sketch leaves out* (all supplied, batch 115):
  1. Theorem 5 is needed with a decreasing pattern on the stretch `R → A`
     (`Description.theorem5_gen`).
  2. The three applications of Theorem 5 must land at one level.
  3. The fine links at each junction must land in the correct end link of each piece (a clause of
     Theorem 5's *construction*, not of its statement).
  4. The glued chain must be a chain (`Chain.threePiece`).
  5. The glued chain must run from `P` to `Q`.
  6. `W` must lie in the first part.
  7. The junction indices need bounds, given a small enough mesh.
  8. The base rung needs a pattern carrying the `R`-indices across.
  9. Every new `R`-index must be positive.

**A.1.5 Theorem 9: no defect found; verified with the mesh clause weakened.**
* Lehner (1961, p. 370) re-proves it "at the request of Professor Bing" because the original "has
  presented some readers with difficulty".
* `theorem9` (`Fold/Theorem7.lean`, batch 82) has every link of `F` in three consecutive links of
  `E` (`D.unionRange j 3`; its docstring: "three-link form for the mesh clause as in
  `theorem4`"), where Bing (p. 737) has "each link of F is a subset of the sum of two adjacent
  links of E". The printed two-link form is not formalized. Until 2026-10-22 this entry said
  "proved as Bing states it"; the referee of the severity document found the difference.
* The Lean statement names the chains the other way round: Bing's `D` (crooked in `E`, and
  consolidated into `F`) is `E` in `theorem9`, and Bing's `E` is `D`.

### A.2 R. H. Bing, *Snake-like continua*, Duke Math. J. 18 (1951), 653–663

Theorems 1–16 are verified as printed, with Theorem 6 now an equivalence (A.2.3), except as noted
below.

**A.2.1 Theorem 8 (p. 658): verified as printed; unargued steps.** Until 2026-10-22 this entry
read "false as printed". That was my error.
* *The definition.* Bing (p. 658, page image): "For each point `p` let `g_p` denote the
  intersection of all continua which contain interiorly a continuum that contains `p`
  interiorly." My batch-92 commission dropped the inner continuum.
* *What the certificate refutes.* `Counter92.theorem8_1951_false`
  (`Plane/Atriodic51CounterBing.lean`) refutes the one-layer variant: in `S₀` (two sine curves
  over a bar), `q ∈ g p` while `g p ≠ g q`. It does not touch Bing's definition (B.1).
* *Verified.* `theorem8_1951'` (`Plane/Atriodic51B.lean`, batch 93) proves every clause with
  Bing's `g_p` (`bingElt`), with (a) in the form Bing's proof gives it (of any three elements, one
  separates the other two). On `S₀` the elements are the bar and the points of the curves.
* *Unargued steps; supplied (batch 93).* "`K₂` contains `K₄` interiorly" (proved in the stronger
  form `cl C₄ ⊆ C₂`). "Similarly, we find that each point in `g_q` is in `g_p`": `p ∈ g_q` must
  be proved first, without the paragraph's own conclusion, so the order of the two inclusions is
  forced.

**A.2.2 Theorem 11, sufficiency (p. 660): unargued sentences; statement true.** The theorem is
proved: `theorem11_1951`, `theorem11_1951_iff`. Three sentences of the proof are not argued:
1. "There is an uncountable collection `G′` … a sequence … converging to `g′` such that infinitely
   many elements … separate `g′` from `g₁` and infinitely many separate `g′` from `g₂`."
   * This sentence *does no work*. The proof needs only one element that is not an end element
     (`exists_not_endElt`), and that element need not be degenerate.
   * The Cantor organ has no degenerate element (`exists_degenerate_interior_elt_refuted`).
2. "`p′` satisfies condition A for `M` equal to either `H` or `K`."
   * Supplied by Fugate 1969, Lemma 4: a terminal point `μ` of both halves (`exists_mu`).
   * Bing's own `p′` need not lie in `Cl(B − A)`, so his choice does not supply it in general.
3. "`S − N` is the sum of two mutually separated sets `H′` and `K′` …"
   * Read with the implicit "`h₁, …, h_m` covers `H′`".
   * Supplied by Fugate 1969, Claim 2 (`claim1_contains_inter`, `claim2`).
   * The stronger reading, with `K′ ⊇ K − g′ − N`, is refuted (`not_separation_of_accumulates'`).

Theorem 10 is not needed for Theorem 11. Fugate's 1966 Lemma 1 (`fugate_lemma1`) provides the
chains.

**A.2.3 Theorem 7: unstated step; statement true.**
* *The step.* Theorem 7 is stated for a *tree-like* plane continuum, and is introduced by "In the
  proof of Theorem 6 we establish the following result". But the proof of Theorem 6 assumes that
  `M` contains no continuum separating the plane. The implication "tree-like ⇒ no subcontinuum
  separates the plane" is neither stated nor proved in the paper. It is classical.
* *Proved:* `treeLike_nonseparating` (`Plane/TreeLikeNS.lean`, batch 133). The proof uses neither
  Borsuk's separation theorem nor Brouwer's:
  * a continuous logarithm of `z − p` on a fine tree cover, built leaf by leaf;
  * its impossibility on a polygon around `p`, by the east-ray crossing parity.
* *Consequences:*
  * Theorem 7 as printed: `theorem7_1951_treeLike`.
  * Theorem 6 with its converse: `isTreeLike_iff_nonseparating`.

**A.2.4 Theorems 6 and 7: the plane topology they use.** This is not a defect. The proofs use the
following, which the paper takes as known:
* the Jordan curve theorem for polygons;
* Janiszewski's theorem;
* the existence of a polygon enclosing a non-separating continuum inside a given open set.

All three are proved in the repository, in the polygonal forms the proofs need:
* `jct_polygon` (batches 125–126);
* `janiszewski_polygonal` (batches 127–129);
* `enclose_holds` (batches 130–131), giving `planeFacts_holds`.

The compact form of Janiszewski's theorem is not needed. In the repository, Theorem 6 is a
corollary of Theorem 7, the reverse of Bing's order: the circular-chain argument needs links that
are polygon interiors.

### A.3 R. H. Bing, *Concerning hereditarily indecomposable continua*, Pacific J. Math. 1 (1951), 43–51

* Theorems 1–4: verified. No defect found.
* §5: not formalized; not planned.

### A.4 J. B. Fugate, *Decomposable chainable continua*, Trans. AMS 123 (1966), 460–468

Every numbered statement is verified.

**A.4.1 Corollary 1 (p. 467): stated without proof; true.**
* *Statement.* A finite chain of chainable continua, consecutive ones meeting, has a chainable
  union iff the union is atriodic and unicoherent.
* *Proved:* `fugate_cor1` (`Plane/Ingram68.lean`, batch 132).
* *The missing step.* The one-line induction through Theorem 1 that Fugate presumably intends
  needs every partial union `A₀ ∪ ⋯ ∪ A_p` to be unicoherent. That is condition (U), and it is
  exactly what is missing (`fugateU_iff_cor1Sufficiency`, batch 124). (U) holds
  (`fugateU_holds`), but the proof is not elementary. It goes through a property (∗): every proper
  subcontinuum of an atriodic union of two chainable continua with disconnected intersection is
  unicoherent. (∗) is proved by the direct route through Ingram 1968, Lemmas 1–2.
* *Literature (2026-10-08).* No proof, correction, counterexample or discussion of Corollary 1
  for more than two pieces was found in any of the following:
  * MR0196720 (reviewer L. K. Barrett) and Zbl 0139.40701;
  * Fugate 1969; Bennett–Fugate 1977;
  * Nadler 1992; Macías 2005; the Houston Problem Book (1995);
  * the citing papers Gordh 1973, Ingram 1968 and Alhassan 2020;
  * a web search.

**A.4.2 Introduction (p. 460) versus Theorem 1 (p. 466): harmless mismatch.**
* The introduction says "a-triodic and hereditarily unicoherent". Theorem 1 says "a-triodic and
  unicoherent".
* For two pieces the two are equivalent (`isHereditarilyUnicoherent_union`).
* Barrett's MR review follows the introduction. The zbMATH review, Ingram 1968 and Alhassan 2020
  follow the theorem.

**A.4.3 The citation of Miller [6, Theorem 1.5, p. 180]: citation over-general; harmless in
context.**
* *As Fugate cites it.* If `A ∪ B` contains a non-unicoherent subcontinuum `D`, then `D ⊆ A` or
  `D ⊆ B`.
* *Refuted:* `miller_1_5_false` (`Plane/Fugate66BMiller.lean`). The closed disk is the union of
  two half-disks, and its boundary circle lies in neither.
* *What Fugate needs:* hereditary unicoherence of `A ∪ B` for chainable `A`, `B` with connected
  intersection. It is proved directly: `isHereditarilyUnicoherent_union`, `hu_union_of_snakeLike`.
* Corrected form: `miller_1_5_of_hu`.
* Miller's own statement (Trans. AMS 69, 1950) has not been checked against the citation.

**A.4.4 The citation of Sorgenfrey [8, p. 440] (Theorem 1, Claim 1): citation over-general;
harmless in context.**
* *As cited.* Three intersecting continua, none contained in the union of the other two, have a
  union that is a triod.
* This fails in general: a circle is the union of three arcs (REPORT-batch100).
* Inside a hereditarily unicoherent continuum it holds (`isTriod_union_of_three`), and that is the
  situation of Claim 1.

### A.5 J. B. Fugate, *A characterization of chainable continua*, Canad. J. Math. 21 (1969), 383–393

No statement is refuted. Lemma 3, Lemma 4 and Theorem 2, Case II are verified (batch 104). The
formal proof needed the following beyond the text:
1. **Lemma 3, "points `p ∈ R` and `q ∈ K`": a real gap.**
   * Lemma 2 only gives `K ∪ R` irreducible between some `q ∈ K` and some `p`. Getting
     `p ∈ R ∖ K` needs `R ⊄ K`, which Fugate does not argue.
   * Proved from Sorgenfrey's theorem (`isTerminalSub_of_union_terminal`).
2. **Lemma 3, "Clearly `A ⊆ R`".** Replace `R` by `R ∪ A`.
3. **Lemma 3, the "similar" case `R ⊆ S ∪ K`.** The mirror argument. Fugate's remark about `q` is
   not needed.
4. **Lemma 3, "`L ∩ (S ∪ K)` is a continuum".** Needs hereditary unicoherence, which Fugate does
   not state (`isContinuum_inter_of_hu`).
5. **Lemma 4, inductiveness.** Replaced by a two-line monotonicity argument
   (`isTerminalSub_iInter`).
6. **Claim 1, the choice of `s`.** Needs `exists_nbhd_not_separated` and Theorem 8(a). Upper
   semicontinuity is not used.
7. **Claim 1, "`W(s)` is a continuum".** Needs unicoherence of the space
   (`claim1_contains_inter`).
8. **"`K` is terminal in `Cl(B − A)`".** The triod needs `A ⊄ R ∪ L`.
9. **Claim 2.** Needs connectedness of `N` and of `M`, and hereditary unicoherence of `M`
   (`claim2`).
10. **The displayed chain is in general only a weak chain.** Links may be empty, and consecutive
    links need not meet. It is trimmed (`exists_chain_of_weak`), and the mesh is checked
    (`epsCoverable_of_halves`).

### A.6 G. R. Lehner, *Extending homeomorphisms on the pseudo-arc*, Trans. AMS 98 (1961), 369–394

* Lemma 3 (`n = 2`): verified (`lehner_lemma3_two`). No defect found.
* It supplies the sequences Bing's Theorem 14 asserts (A.1.4).

### A.7 W. T. Ingram, *Decomposable circle-like continua*, Fund. Math. 63 (1968), 193–198 (support for A.4.1)

* *Lemmas 1–3: no defect found.*
  * Every appeal to Sorgenfrey (1944, Theorem 1.8) was checked: the three continua have a common
    point, and none lies in the union of the other two.
  * The two steps of Lemma 3 flagged in the commission are correct.
* *Verified:*
  * Lemmas 1 and 2. The formal proof replaces the appeals to Sorgenfrey by a "core" triod lemma,
    `isTriod_of_core`.
  * Lemma 2's terminality clause carries an added hypothesis, that `A` is hereditarily
    unicoherent. This is a limitation of the replacement, not of Ingram.
* *Not formalized and not needed:* Lemma 3, Theorems 1 and 2(2), and Sorgenfrey 1.8 in general.

### A.8 Textbooks used in the formalization

* **Nadler, *Continuum Theory* (1992), 11.25–11.35** (Sorgenfrey's theorem, batch 102).
  * 11.28 *as transcribed* is false: take `H = Ū`, so that `U − H = ∅`
    (`isConnected_diff_of_superset_false`). Nadler's own proof assumes `U − H ≠ ∅`, so this is a
    transcription slip, not Nadler's.
  * The remaining notes are omitted nondegeneracy and closedness hypotheses, and simplifications
    (REPORT-batch102, thirteen items). None is a false statement of Nadler's.
* **Nadler 12.51** (proper subcontinua of circle-like continua are chainable): verified. No
  defect.

### A.9 J. van Mill, *A note on the Effros theorem*, Amer. Math. Monthly 111 (2004), 801–806

Verified (batch 134, `HPC/Effros/`): Lemma 2.1, Proposition 2.2, Lemmas 3.1–3.4, Proposition 3.5,
Corollary 3.6. Also verified are the open mapping principle for a Polish group
(`effros_open_mapping`) and Ungar's corollary (`effros_homogeneous`, `effros_homogeneous_set`).
No false statement was found.

* **Proposition 2.2: tacit hypothesis.** `X ≠ ∅` is assumed without being stated. In the empty
  space, `∅` is analytic and fat (`isFat_empty_of_isEmpty`). This is trivial.
* **Proposition 3.5: implicit step.** Proposition 2.2 is applied "in `E`". This needs "nowhere
  meager in `X`" to give "nowhere meager in `E`" for subsets of the open set `E`. That is true but
  not said. The formalization avoids it with a relative form of 2.2
  (`inter_nonempty_of_nowhereMeagre`).

### A.10 F. B. Jones, *Concerning non-aposyndetic continua*, Amer. J. Math. 70 (1948), 403–413, and *Certain homogeneous unicoherent indecomposable continua*, Proc. AMS 2 (1951), 855–859

Verified (batch 135, `HPC/Jones/`):
* Jones 1948, Theorems 0–19 and the three Corollaries;
* Jones 1951: `aposSet`, `isOpen_aposSet` and the Lemma.

Jones 1951 Theorem 1 is verified (batch 136, `jones51_theorem1`) by a different argument. It
uses hereditary unicoherence of `M` only, with no decomposition space and no Whyburn.

* **Jones 1951, Theorem 1: unargued sentences** (p. 859, page image). The following are asserted
  without proof:
  * "Furthermore `M′` is homogeneous and aposyndetic";
  * "`M′` contains a nonseparating point";
  * "But `M′` is hereditarily unicoherent". This is true, since a monotone image of a hereditarily
    unicoherent continuum is hereditarily unicoherent, but it is not argued.

  The formal proof needs none of them.
* **Jones 1951: harmless mismatch.** "hereditorily" (p. 858) is a misprint.

* **Jones 1948, Theorem 10: false as printed.** p. 407 (page image): "In order that a compact
  continuum M be indecomposable it is necessary and sufficient that M contain an open subset D of
  M such that if x is a point of D and y is a point of M − x, then M is not aposyndetic at x with
  respect to y." (Until 2026-10-22 this entry gave a paraphrase in quotation marks.)
  * `D = ∅` satisfies the condition vacuously in every continuum, so the statement says every
    continuum is indecomposable. An arc refutes it (`theorem10_printed_iff`,
    `not_theorem10_printed_unitInterval`).
  * With `D` nonempty it is proved (`theorem10`).
* **Jones 1948, Theorem 6: false as printed** (same defect). With `D = M₀ = ∅` the hypotheses hold
  vacuously, and the conclusion asks for a point of `D` (`not_theorem6_printed`). Proved with `D`
  nonempty.
* **Jones 1948, Theorems 11, 12, 13 and 19: tacit hypothesis.** `D` (resp. `U`) must be
  nonempty, for the same reason. These are not listed as false, because the intended reading is
  plain.
* **Jones 1948, Theorems 2 and 3: stated without proof.** Theorem 3 is used by Jones 1955. Both
  are proved:
  * openness of the aposyndesis relation in `X × X`;
  * boundary bumping (`aposAt_of_frontier`).
* **Jones 1948, Theorems 0 and 5: stated without proof** ("with the help of the Heine–Borel
  theorem"; "similar to Theorem 4"). Both are proved.
* **Jones 1948, Theorems 14, 15, 18 and 19: sketches.** All go through as indicated.
* **Jones 1948, Theorem 13: unargued sentence.** Jones's choice of `V₂` must also satisfy
  `cl V₂ ⊆ W₁`, which his next sentence uses. Supplied.
* **Jones 1948, Theorem 16: harmless mismatch.** "`P`" is printed for the weak cut point "`p`".
* **Jones 1951, Lemma.** The two steps checked ("evidently `x_ω ≠ xₙ`" and the limit stages)
  are correct. The formal proof replaces the transfinite sequence by a lower semicontinuous
  function on a compact space. `x ≠ y` is not needed.

### A.11 F. B. Jones, *On a certain type of homogeneous plane continuum*, Proc. AMS 6 (1955), 735–740

**Theorem 1: verified** (batch 136, `HPC/Jones/Jones55*.lean`). Verified: the conclusions (a), (b),
(c), u.s.c., continuity, and that the elements are homogeneous and mutually homeomorphic.
* The formal proof keeps Jones's claims (1)–(10), the two characterizations of `N_o`, properties
  (a)–(f) of p. 739, and his last sentence.
* It replaces (11), (12), the case argument of pp. 737–738 and the u.s.c. argument. The
  replacement is a spreading lemma from the Effros theorem: in a homogeneous compact metric space,
  a continuum with interior that contains `o` and misses `x` gives aposyndesis at `o` with respect
  to `x`.
* Decomposability is needed only for nondegeneracy of the decomposition space.

* **Theorem 1, case argument (pp. 737–738): proof defective; statement true.**
  * "Since `M₀` is a subset of `M₁`" (Case I) fails as written. When `o(q) ∈ V₂`, the
    irreducible continuum `K_o(q)` can be `{o}`, which is not in `M₁`. (When `o ∉ V₂`, boundary
    bumping does keep it in `M₁`.) The text does not keep `o(q)` out of `V₂`.
  * "Since `q` does not cut `o` from `U_q`" draws on `q ∉ N_o`, which is stated with `U_o`. It
    therefore needs `U_q = U_o`, i.e. (b), which is not yet available at that point.
  * The argument is not repaired in place. The conclusion it serves (`N_o = M − U_o`) is proved by
    the replacement.
* **Theorem 1, continuity step: unstated step.** "Since `G` must be continuous at some one of its
  elements": an u.s.c. decomposition of a compact metric space is continuous at a residual set of
  elements (`residual_lscAt`, proved).
* **Theorem 1, conclusion (a): unargued.** Homogeneity and aposyndesis of the decomposition space
  are not argued. Both are proved; aposyndesis by (c) and lower semicontinuity.
* **Theorem 1, "`N_o` is closed": unargued.** Moot, since `N_o = L_o` is closed.
* **Theorem 1, (10)/(11): transfinite device.** The uncountable well-ordered sequence is replaced:
  (11) follows from (c).
* **Theorem 1, `d(q)`: not established.** Attainment of the supremum and "`E_n` is closed" are not
  decided. They are moot, because the argument is not used.
* **Theorem 2, last step: harmless mismatch (citation).** "Hence by [5]": the result used is [3]
  (Jones 1949), not [5] (Jones 1951).
* **Theorem 2: verified** (conditionally in batch 148; unconditionally in batch 154,
  `jones55_theorem2'`, after Jones 1949 Theorem 1).
* **Theorem 2, separation step: unstated step; supplied.** "Since each two elements of `G` are
  homeomorphic, … if one element of `G` were to separate `S`, then each of them would" uses Borsuk's
  theorem, that plane separation is a topological invariant of a plane compactum
  (`separatesPlane_of_homeomorph`). For the "uncountably many mutually exclusive domains" Jones
  argues neither the choice of the domains nor their disjointness; both are supplied
  (`jones55_elt_not_separates`).
* **Theorem 2: unargued; supplied.** The upper semicontinuity of `G′` (`mooreDecomp_gPrime`, via a
  closed quotient map) and "`G` is a compact subcontinuum of `G′`" (`jones55_embedding`). [13]
  cites both Moore 1932 and Moore 1925 Theorem 22; the formalization uses the latter.
* **Theorem 2: unmentioned case.** When `M` is aposyndetic, `L_x = {x}`, and (1) is Jones 1949 for
  `M` itself. Handled separately.
* **Theorem 2's proof: misprint (confirmed).** "Since each two elements of `g` are homeomorphic"
  should read `G`.
* **Theorem 2's proof: unargued; supplied.** "It is clear that for each `g` of `G`, `M − g` is
  connected (in fact, by (5), `M − g` is strongly or continuum-wise connected)". The "(5)" is claim
  (5), p. 736. Continuum-wise connectedness follows (`jones55_compl_continuumwise`).
* **Closing remarks, pp. 739–740: unnumbered claims; verified** (unconditionally, batch 154)
  (`jones55_elements_indecomposable`, `jones55_two_domains`, `jones55_three_domains`, batch 148).
  * "Because each element of `G` in Theorem 2 is homogeneous and does not separate the plane, each
    such element is indecomposable."
  * "every decomposable, homogeneous, bounded continuum in the plane must have exactly two
    complementary domains (this follows from Theorem 2)".
  * "every homogeneous, bounded continuum in the plane having more than two complementary domains is
    indecomposable and of Type 3".

### A.12 R. L. Moore, *On the foundations of plane analysis situs*, Trans. AMS 17 (1916), 131–164 ("F.A."), §§2–5

Verified (batch 137, `HPC/Moore/`):
* the definitions and Axioms 1–8;
* Theorems 1–19;
* the unnumbered facts of pp. 135 and 139–140;
* a bridge identifying Moore's notions with those of the topology generated by the regions, which
  is metrizable under Axioms 1, 3 and 5₁.

Moore's §5 rests on Lennes 1911 ("it is possible to prove Theorems 2–9 of §4 of Lennes' paper") and
supplies no proofs. Those facts are proved instead through the arc characterization (embedded
`[0, 1]`).

* **Theorem 14: false as printed.**
  * The proof opens "For each `n`, `Mₙ` contains at least one point", but this is not a
    hypothesis.
  * `Mₙ = ∅` refutes the statement (`not_fa_theorem14_printed`).
  * It is proved with `Mₙ` nonempty.
* **Theorems 4 and 19: false as printed (empty region).** Adjoining `∅` to the regions preserves
  Axioms 1–8 and every derived notion (`withEmpty`). The tacit hypothesis is "regions are
  nonempty", and Moore's proofs begin by choosing a point of `R`. Both are proved with `R`
  nonempty.
* **Limit points on an arc (p. 139, unnumbered): false as printed** at an endpoint, where the
  criterion holds vacuously (`not_fa_sec5_limitPt_printed`). Corrected and proved.
* **First and last points (p. 139): harmless rewording.** "Between `P₁` and `B`" must allow `B`.
* **Theorem 10: proof defective; statement true.** "`R₁R₂⋯R_kR` is a simple chain" need not hold.
  Repaired by taking a shortest sub-chain.
* **Theorem 15: proof defective; statement true.** In part III, "since `y` precedes every link of
  `Cₙ` that contains `P` it follows that `P_B` precedes `P`" fails at stage `n`, because `P_B` can
  lie in the next link, which may contain `P`. Repaired by choosing `n` large. The two "it is
  clear" steps of part III are also supplied.
* **Definition of connected (p. 132): tacit hypothesis.** The two parts must be nonempty;
  otherwise no nonempty set is connected.
* **Stated without proof:** Theorems 1, 3, 7, 11, 13, 16, 17 and 18, and "`M′` is closed". All are
  proved. Theorem 1 needs no axiom.
* **§6 opening (p. 140): not formalized.** "It is clear that Theorems 1–19 are consequences of
  Axioms 2–5 and Theorems 5 and 15." This is partly borne out.

### A.13 Moore, F.A. §6, Theorems 20–34 (pp. 140–150)

Verified (batch 138): Theorems 20–34, and Theorem 34 for any region.

* **"The interior of `J`": undefined term.** It is used from the proof of Theorem 23 on and never
  defined. It is supplied as the region bounded by `J`, which exists by Axiom 8 and is unique by
  Theorem 21 (`existsUnique_interior`).
* **Theorem 23: false as printed (empty region).** Proved for `R` nonempty.
* **Theorem 31: tacit hypothesis.** The order `C E B G D` needs `B ≠ C, D`.
* **Theorem 32: tacit hypothesis.**
  * Nothing in the statement keeps `C ∈ R` off the arc `AB`. If `C` is on `AB`, no arc `CB` can
    meet `AB` only in `B` (argued in prose, not formalized).
  * Proved under the stronger hypothesis `R ∩ AB = ∅`. Whether `C ∉ AB` suffices is under check
    (batch 139).
* **Theorem 28: proof defective, statement true.** The last step needed a correction.
* **Theorems 33–34: proof defective, statement true.**
  * Two proofs are printed. Kline's general proof (p. 150) was formalized, and the special
    closed-curve proof is not needed.
  * Kline's proof has a gap, now filled: the first point of `DC` on `CAB` may be `B`.
* **Theorem 34: harmless mismatch.** "Jordan *arc*" is printed for "closed curve".
* **Theorem 33: harmless mismatch.** An unbalanced parenthesis.
* **Stated without proof.** Theorems 20 ("easily … Axiom 7"), 22 ("easily …") and 30 have no
  proof printed. All three are proved. Every "it can easily be shown" step listed in the commission
  was supplied.

### A.14 Moore, F.A. §7, Theorems 35–43 (pp. 150–157)

Verified (batch 139):
* Theorems 35–40;
* Theorem 41 Case I and the first sub-case of Case II;
* Theorem 42 conditional on 41;
* the p. 152 footnote;
* the interior of Theorem 36's curve lies in `R`.

Completed in batch 140: Theorem 41 (Case II), Theorem 42, and corrected Theorem 43.

* **Theorem 35: false as printed (empty region).** Proved for `R` nonempty.
* **Theorem 43: false as printed.** It fails for `G = ∅` in every model
  (`not_fa_theorem43_printed`). It has no proof printed; the corrected form is open.
* **Theorem 36: proof defective, statement true.** The arc `BC` can leave `R`; it is cut at its
  first point outside `R`.
* **Theorem 36: tacit addition.** The interior lies in `R`. Moore 1925 Theorem 19 needs this; it
  follows from Theorem 21.
* **Stated without proof:** Theorems 38 ("analogous"), 40, 42 and 43.
* **Unargued:** Theorem 41's final step, "It may be proved that `J` is a closed curve satisfying the
  requirements". This hides a limit construction, because the curve can consist of infinitely many
  arcs.
  * Supplied in batch 140. The arcs are replaced by chords; Moore 1919 Theorem A keeps them small,
    and Theorem 27 keeps them from overlapping.
  * Theorem 43, which has no proof printed, is proved through a dual of Theorem 41 for intersections
    of interiors, which F.A. never states.
* **Theorem 37: unargued steps.** Replaced by a finite-chord argument.
* **Theorem 39: unargued steps.** About seven, all replaced by an accessibility lemma.

### A.15 R. L. Moore, *Concerning a set of postulates for plane analysis situs*, Trans. AMS 20 (1919), 169–178

The whole paper is verified (batches 140–144), and with it Moore's characterization of the plane:
`m19_plane`, a space satisfying F.A.'s Axioms 1–8 is homeomorphic in its region topology to `ℝ²`
(batch 144). Theorems E, G and the final paragraph are reached by a route different from Moore's
(Schoenflies by grids, square annuli, pasting over Theorem F's exhaustion).

* **Footnote †, p. 170: harmless misprint.** "Have `A` and `B` as endpoints" should read `X` and
  `Y`.
* **Theorem A: verified.** It is proved in a stronger form, without assuming the arcs distinct.
* **Theorem B: verified.** The five steps Moore calls "clear" or "easy" are supplied. Finiteness is
  obtained by compactness instead of from Theorem A; Theorem A also applies, as printed.
* **Theorem C: false as printed** (batch 141, `not_m19_theoremC_printed`, in every model of Axioms
  1–8).
  * A closed curve touching a side from within meets `ABCDA` in one point, but admits no ruling of
    the required kind.
  * The printed "Indication of proof … given instead of a tedious formal proof covering all possible
    cases" misses this case.
  * Batch 142 proves three corrected forms: absorbing finitely many disjoint cross-cuts; a curve
    within `ABCDA`; and the printed statement with touching from within excluded. Touching from
    without is harmless.
* **Double-ruling definition, footnote *, p. 172.**
  * It requires equal numbers of arcs in the two families, but Moore's own Fig. 1 has 9 and 8.
    Padding shows the requirement costs nothing (`doubleRuling_pad`).
  * It omits the disjointness of the `Y`-arcs; this is added.
  * The "subdivisions" are never defined, and the subdivision lemma is never stated. It is proved:
    `(n+1)(m+1)` cells, each the interior of a closed curve.
* **Theorem D: proof defective; statement true** (verified, batch 142).
  * Moore's proof applies Theorem C to a curve `J̄` that `g₁` may touch.
  * His induction over `g₂, …` needs D itself.
  * The Fig. 2 construction is unargued ("It easily follows").
  * Replaced by an induction over a finite subcover. At each step a curve is built about the
    uncovered part, crossing `ABCDA` at every common point, and the corrected C is applied.
  * Whether Moore's `J̄` could be re-chosen so that it is crossed rather than touched is not
    decided.
* **Theorems D and E: unargued.** They rely on "This process may be continued" and on extension of
  rulings, which is never proved.
  * Both are supplied (batches 141–143): refinement, then nested rulings.
  * Theorem E is verified (batch 143). Moore's unargued limit arcs ("it can be proved that there
    exists through `P` … just one arc") are replaced: E is derived from a Schoenflies theorem for
    Moore's space, proved from the grid of all ruling arcs (mesh → 0 by counting).
  * Theorem E (3) is read as exclusive.
* **Theorem F: verified** (batch 143). Theorem 42 needs the union of the interiors to be connected,
  which Moore does not provide; it is supplied with arcs.
* **Theorem E: candidate mismatch.** It applies Theorem D to regions, while D is stated for closed
  curves.
* **Fig. 3, the nine-cell ruling (p. 177): unargued; not proved as stated** (batch 144). "There
  exist on `Jₙ₊₁` four distinct points … such that `Jₙ₊₁` can be divided by a double ruling … into
  nine subdivisions of which the central one is `AₙBₙCₙDₙAₙ (Jₙ)`." Our route does not need it: the
  annulus between `Jₙ` and `Jₙ₊₁` is cut by two arcs into two quadrilaterals (`exists_cuts`,
  `annulus_decomp`), which receive prescribed-boundary square maps (`m19_schoenflies_boundary`).
* **The open curves `kₘ`, `tₙ` and "This process may be continued … two sequences of arcs
  `gₘ₀, gₘ₁, …`"; "The sum of all the arcs … is clearly a continuous open curve" (p. 178):
  unargued; not needed** by our route. Its open curves are images of lines under the homeomorphism,
  open curves in F.A.'s sense (p. 159) by `m19_openCurve`.
* **Theorem G: unargued; supplied** (`m19_theoremG`, batch 144). "It is clear that through every
  point there is just one curve of the set `α` and just one curve of the set `β` …" (p. 178).
* **The final paragraph: unargued; supplied** (`m19_final`, batch 144). "Between the points of `t₀`
  and the set of all real numbers there is a one-to-one continuous correspondence"; "It is clear
  that the correspondence thus established … is continuous". Neither the 1915 characterization of
  the line nor metrizability is used: Moore's sequential limit is convergence in the region topology
  from Axiom 1 alone (`isSeqLimit_iff_tendsto`).
* **"Σ₁ or Σ₂" (p. 169).** Only Σ₁ (Axioms 1–8) is formalized. F.A. p. 163 asserts without proof
  that Σ₁ and Σ₂ (Axioms 6′, 7′ for 6, 7) "are equivalent with respect to point and limit point of a
  point-set". The assertion is not needed: Moore 1925 Theorem 21 verifies Axioms 6 and 7
  themselves.
* **Introduction (p. 169): stated without proof.** "every space `S` that satisfies Σ₁ or Σ₂ is a
  number plane". The paper's proofs use Σ₁. For Σ₂ the claim rests on F.A. p. 163's unproved
  equivalence ("It is easy however to show that though Σ₁ and Σ₂ are not absolutely equivalent, they
  are equivalent with respect to point and limit point").

### A.16 R. L. Moore, *Concerning upper semi-continuous collections of continua*, Trans. AMS 27 (1925), 416–428, §I

The whole of §I is verified (batches 145–147), ending with Theorem 22: the space of elements of an
upper semicontinuous decomposition of the plane into non-separating continua is homeomorphic to the
plane (`m25_theorem22`). No Jordan curve theorem is used: Brouwer's boundary theorem, Janiszewski's
theorem for compact sets, Borsuk's logarithm theorem and Mullikin's Theorem 5 are proved by
logarithms (Eilenberg's method).

* **u.s.c. (p. 416): harmless.** Moore's distance form is equivalent, for compact elements, to the
  closed-map form (`isClosedMap_mk_plane`, `usc_of_isClosedMap`).
* **Definition of boundary (p. 417): misprint.** "The set of all elements `[x]` of `H` such that `x`
  either belongs to `H` and … or `x` does not belong to `H` but it is a limit element of `H`." As
  printed the second clause is empty. Read "of `G`", it is the frontier (`m25_boundary_iff`).
* **Definition of complementary domain (p. 417): defective.** "A domain of elements of `G` is said
  to be a complementary domain of a closed set `H` … provided the boundary of `D` is a subset of
  `H`." Neither disjointness from `H` nor maximality is required. So `G` is a complementary domain
  of every closed set, and "the unbounded complementary domain" is not unique.
  * **Theorem 2 is false under this definition** (`not_m25_theorem2_printed`, batch 146). Take the
    decomposition into points, `M` a closed disc, `D` the open disc minus a radius, and `E` the
    plane minus the radius. The outer boundary is then the radius, which is cut by each of its
    interior points.
  * Read as components of the complement, Theorem 2 holds (`m25_theorem2`), and the unbounded one is
    unique (`m25_unbounded_unique`, without closedness).
* **Definition of simple closed curve (p. 417): defective; Theorems 10 and 11 false as printed**
  (batch 146). "A bounded subset `H` of the set `G` is said to be a simple closed curve … provided
  it is disconnected by the omission of any two of its elements." Neither closedness nor
  connectedness is required, and neither is more than one element. Two disjoint segments
  (decomposition into points) qualify. For them Theorems 10 and 11 fail: they are not a union of two
  arcs, and their complement is connected (`not_m25_theorem10_printed`,
  `not_m25_theorem11_printed`). Moore 1920's Definition 4 (p. 342), which 1925 cites, has "closed,
  connected, and bounded"; but it admits a single point, for which 1920 Theorem 4 is false
  (`not_moore1920_theorem4_singleton`), and so is 1925 Theorem 11 (`not_m25_theorem11_singleton`).
  The corrected definition adds "closed, connected, nontrivial"; with it Theorems 10 and 11 are
  verified.
* **Theorem 1: two harmless slips.** In I, "a subsequence of distinct points" need not exist (a
  constant subsequence does the job). In II, "that element of `H₁` which contains `p`" should read
  `P`. Verified (`m25_theorem1`).
* **Theorem 2: unargued steps; supplied.** "`B` is a closed and connected set" is used without
  citing Brouwer; Brouwer's theorem is needed twice (for `∂D`, then for `∂E`). "Clearly `Dₓ`
  contains `D`", "`q` does not belong to the boundary of `Dₓ`", and `K − p ≠ ∅` are supplied. Only
  the closedness of `H + p`, `N + p` is used.
* **Theorem 3: statement incomplete; four unargued steps; supplied.** The
  statement does not say the region contains `p`, though the proof gives it and Theorem 4 needs it.
  "The point set `H̄` is a continuum", "the boundary of `R` consists of all those elements …", "It
  follows that the boundary of `R` is connected" and "clearly `R` is a domain" are supplied.
* **Theorem 4: stated without proof** ("may be easily established with the help of Theorem 3");
  supplied.
* **The p. 420 claim: stated without proof** ("by methods largely analogous to those used … in my
  paper *Concerning the prime parts of a continuum*"); supplied (`m25_axioms1245`). The Math. Z.
  paper's Theorem 13 is the model for Axiom 1 and its Theorem 12 for Axiom 4; it argues neither
  Axiom 5 nor F.A. Theorem 4. The Math. Z. paper claims Axioms 1, 2, 4 and **5₁** (p. 313, 400-dpi
  image), not 5; the 1925 paper claims 5, which holds there (`m25_axiom5`).
* **Theorem 7 (p. 420): false as printed, by a misprint.** "then `p` is a limit element of the set
  `H`" should read `x`. The printed form is refuted (`not_m25_theorem7_printed`); the corrected form
  is verified (`m25_theorem7`).
* **Theorems 5, 6, 10: stated without proof; supplied** (batch 146), as instances of general
  cut-point characterizations of the arc and the circle in compact metric continua (`CutArc.lean`,
  `circle_char`).
* **Theorem 8's proof (pp. 420–421): two unargued steps; supplied.** "It is easy to see that
  `K₁ + p` and `K₂ + p` are both closed and connected"; the conditions under which "`K₂ + p` would
  be a simple continuous arc" are supplied from the negated supposition.
* **Theorem 9: stated without proof** ("an argument largely similar to that used in the proof of
  Lemma 8" of P.C.S.); supplied. A bounded complementary domain would have an outer boundary that is
  a sub-arc not cut by its interior elements (Theorems 2, 6); two unbounded domains coincide. P.C.S.
  Lemma 8 passes tacitly from "separates" to "has a bounded complementary domain".
* **Theorem 11's proof (pp. 421–422): defective; statement true (corrected definition).** "If `B` is
  not identical with `J` then it is a proper subset of `J`. It easily follows, with the help of
  Theorems 10 and 6, that `B` is a simple continuous arc". Theorem 6 needs `B` connected, which is
  not shown. A repair: `B` lies in a sub-arc `A` of `J` missing an element of `J − B`, and `A` would
  separate `G`, against Theorem 9. The repair is verified (`frontier_eq_of_scc`, batch 146). Three
  further unargued steps ("therefore neither `ā` nor `b̄` separates `S`"; "It is easy to see that one
  of these domains … is bounded"; "Clearly `I` and `E` are domains … and `I + E = G − J`") are
  supplied.
* **Theorem 12: complete as printed**, with "domain" read as nonempty.
* **Theorem 13's proof (p. 422): unargued steps; supplied.** `R − k` is not shown to be nonempty;
  "By Theorem 9" covers arcs, not the single-element case; "`x` and `y` any two elements of `R`"
  must be read in `R − k`.
* **Theorem 14's proof (p. 423): notation slip and unargued step; supplied.** The arc `pq` becomes
  `pxq` with `x` never introduced. "It is easy to see that the sum of the arcs `pxq` and `pyq`
  contains as a subset a simple closed curve" is supplied (`exists_tscc_of_arcs`).
* **Theorems 15–19: stated without proof** (pointers to F.A. Theorems 24–27 and 36); supplied.
  Theorems 15–18 go through batch 138's general forms of F.A. 24–27. Theorem 19 follows batch 139's
  corrected F.A. 36. It uses Theorems 10–14 and 18, not 17. Moore's remark that F.A. Theorem 21 "may
  be easily proved with the help of Theorem 11" is right as it stands.
* **Theorem 18's statement: undefined symbols; harmless.** `x` and `y` are used as elements without
  being introduced. The condition does not depend on which elements of the arcs they are.
* **Theorem 20's proof: unargued step; supplied.** "Since `R` is also a region in the original
  sense".
* **Theorem 21's proof: defective for Axioms 6 and 7; statement true** (verified, batch 147). "With
  the aid of results established in my paper *Concerning a set of postulates for plane analysis
  situs* … it easily follows that Axiom 6 and 7 also hold true." Moore 1919 proves nothing for Σ₂
  beyond the assertion of its introduction. The step therefore rests on F.A. p. 163's unproved
  equivalence of Σ₁ and Σ₂. Axioms 6 and 7 are proved directly with cross-cuts and Theorems 10, 12,
  15, 18 and 19. The other three "easily" claims (Axioms 1, 2, 4, 5; Axiom 3; Axioms 6′, 7′) are
  confirmed. The "`+ A`" of Axiom 6′ is idle.
* **Theorem 22: verified** from Moore 1919 for Σ₁ only.

### A.17 A. M. Mullikin, *Certain theorems relating to plane connected point sets*, Trans. AMS 24 (1922), 144–162 (used by Moore 1925 Theorem 11)

* **Theorem 5 (p. 160): false as printed** (`not_mullikin_theorem5_printed`, batch 146). "… such
  that `M₁` and `M₂` have in common only `K₁` and `K₂`, where `K₁` and `K₂` are mutually exclusive
  connected sets, then `S − M₁ − M₂` is the sum of just two mutually exclusive, connected domains."
  Mutually exclusive connected sets need not be separated: take `M₁ = M₂` a segment, `K₁` a
  half-open half and `K₂` the closed other half. Their union is connected, and the complement of the
  segment is connected. The intended hypothesis is that `K₁`, `K₂` be closed (mutually separated).
  Moore's use (`K₁ = p̄`, `K₂ = q̄`) satisfies it. The corrected form is verified
  (`mullikin_theorem5`), by logarithms and Borsuk's theorem instead of her polygons.
* **Theorem 4 (p. 154): harmless.** "A necessary and sufficient condition that their sum … shall
  disconnect `S` is that `M̄`, the set of points common to `M₁` and `M₂`, be not connected." For
  disjoint `M₁`, `M₂` it is true under her convention (p. 144), where the empty set is connected
  (`mullikin_theorem4_disjoint`), and false under Mathlib's
  (`not_mullikin_theorem4_disjoint_mathlib`).

### A.18 F. B. Jones, *Note on homogeneous plane continua*, Bull. AMS 55 (1949), 113–114 

Theorems 1 and 2 are verified for nondegenerate continua (`jones49_theorem1`, `jones49_theorem2`,
batch 154). With them, Jones 1955 Theorem 2 and its closing remarks are verified unconditionally
(`jones55_theorem2'` etc.).

* **Theorem 1: false as printed at a degenerate case** (`not_jones49_theorem1_point`, batch 148).
  "If a compact, plane continuum `M` is both homogeneous and aposyndetic, then `M` is a simple
  closed curve" fails for a one-point continuum. Whyburn's convention (*Analytic Topology*, Ch. I
  §10, p. 15: "A compact connected set will be called a continuum"), which Jones's footnote 3 cites,
  admits one-point continua. The corrected form (`Jones49Thm1`) assumes nondegeneracy.
* **Reference [8]: harmless slip.** "Theorem 9.1, p. 61" is Whyburn's (9.2), the "Local separating
  point-order theorem". (9.1) is the lemma before it on the same page.
* **Reference [4]: harmless mismatch; supplied** (`jones49_order_two`, batch 149). Menger's theorem
  (p. 267) characterizes the circle by *all* points being of order 2. Jones applies it to *a* point
  of order 2, so homogeneity and the topological invariance of order are tacit.
* **Case 1: unargued step.** "If `M − J` is connected, then each point of `M` belongs to some such
  simple closed curve lying in `M`. Consequently each point of `M` belongs to the boundary of an
  element of `G`." The homeomorphisms of `M` do not extend to the plane. The second sentence needs
  the Jordan curve theorem: a closed curve `J′ ⊆ M` with `M − J′` connected bounds a complementary
  domain of `M`. The JCT is now available (`jordan_curve_theorem`, batch 148, from Moore 1925
  Theorem 11 with the decomposition into points).
  Supplied (`frontier_cc_of_jordan`).
* **Case 1: unargued step.** "Since no point of `M` is of order 2 in `M`, each point of `J_i` is a
  limit point of `M − J_i`". True. The formal proof replaces it: an interior point of `J_i` in `M`
  is a local separating point, and Whyburn (9.2) then gives a point of order 2.
* **Case 2: unargued steps.**
  * "There exists an arc `T` lying in the complement of `D̄` which is irreducible from `H` to `K`."
  * "Except for its end points, `T` lies in an element `U` of `G`."
  * That the boundary `C` of `U` meets `J`, so that "the component `AxB` of `C − C·J` … is an
    arc-segment whose end points lie on `J`".
  * "It follows that `M − (A + B)` is *not* connected".

  All four are supplied and true. The last needs a real argument: θ-curves, a "no common side" lemma
  and Janiszewski's theorem (`theta_separation`). It uses no hypothesis beyond those of the case;
  homogeneity and the absence of points of order 2 are not needed.
* **"all except countably many of the local separating points … must be of order 2" (p. 114):
  unstated hypothesis.** The step needs `M` uncountable. Nondegeneracy supplies it.
* **Theorem 2: false as printed at a degenerate case** (`not_jones49_theorem2_point`, batch 154). A
  point is homogeneous and has no weak cut point. "Being aposyndetic at one point, `M` must be
  aposyndetic at each of its points" is a tacit use of homogeneity.

  The citations [4] (Menger, *Kurventheorie* p. 267), [6, 7] (Wilder 1938; Whyburn 1939) and [8]
  (Whyburn, *Analytic Topology* Theorem 9.1) carry the rest.

### A.19 Sources cited by Jones 1949 (batch 149–)

* **Menger, *Kurventheorie* (1932), p. 267, theorem on curves of order 2: verified**
  (`menger_order_two`). The verification does not follow Menger's derivation. It uses Menger's own
  second argument on the same page (an arc meets a curve first at a branch point) twice. Menger's
  route through the *Kennzeichnung der gewöhnlichen Kurven* (p. 266) contains unargued steps:
  * the sharpening of the Lemma of p. 260 to `n`-Beine is only asserted ("folgende Verschärfung
    desselben bewiesen werden kann");
  * "Je zwei Bogen B′ … haben offenbar höchstens Endpunkte gemein";
  * a one-sentence finiteness claim.

  These are not used.
* **Whyburn, *Analytic Topology*, (9.1): defective proof; statement true** (`whyburn_9_1`, batch
  149). The proof applies [I, (10.2)], which requires `N·G` compact, to `U·(Q·R_a + p)`, which need
  not be compact. The case `N·G = N` is not treated, and "`Q·R_a + p` is a generalized continuum" is
  asserted. The repair runs boundary bumping in a compact neighbourhood. The openness of `R` is not
  needed.
* **Whyburn (3.2), (8.4), (8.41), (9.2): verified** (batch 150). The proof is a single separating
  point-order theorem for open sets, through a linearly ordered "separation chain". It does not go
  through (8.2), (8.3) or the non-separated cuttings.
* **Whyburn (9.2), proof: routine unargued step.** "and hence also of order 2 in L".
* **Whyburn (8.41), proof: unargued step.** "each separating point of `L` lies in some `L_i` and is
  a separating point of `L̄_i`". True by the boundary bumping of (9.1).
* **Whyburn (8.4), proof: unargued step, not covered by what is cited.** "since N is ordered as in
  (1.31), there exist points x and y of N … such that δ[Q₂(x)·Q₁(y)] < ε/4". It needs two-sided
  limits and a trivial residue. These come from inside the proof of (2.2), not from the statement of
  (3.2). Supplied (`exists_small_interval`).
* **Whyburn (3.1): stated without proof** ("Thus we have", from (2.2), (2.22)). Not used.
* **Whyburn (8.3), statement: harmless.** "no convergent sequence of components" must exclude the
  constant sequence; read "distinct components".
* **Jones 1949's use, `jones49_some_order_two`: verified** (batch 150).

### A.20 R. L. Moore, *Concerning connectedness im kleinen and a related property*, Fund. Math. 3 (1922), 232–237 (cited by Whyburn 1939 §14)

The paper is verified (Theorems 1–3, batch 150; Theorem 4, batch 151). The step Moore cites from
PNAS 4 (1918), pp. 365–366, is reconstructed with two boundary-bumping arguments, and the "sector
theorem" for continua crossing an annulus is proved by lifting to a strip (`sector_theorem`,
`sector_cyclic_order`). Sufficiency also holds in a local form that needs neither boundedness nor
simple connectivity (`moore22_sufficiency_local`).
* **Theorem 1's proof (p. 233): slip.** "lies wholly within `K*`" should read `K̄`. Harmless. The
  formal proof builds an explicit chain instead of a limiting set.
* **Theorem 2's proof (p. 234): notation.** `M_s` / `M_t`. The subscripts are damaged in the scan,
  so this is not settled.
* **Theorem 3's proof (pp. 234–235): slip.** "these connected point-sets are all of diameter less
  than `ε`". The diameter is only `≤ 2ε`. Harmless with `ε/3`.
* **Theorem 4's proof (pp. 236–237): misprints.**
  * "`t_m`" should read `t̄_m`.
  * "`1 ≤ m ≤ n`" should read `4ⁿ`.
  * "`ε = (b − c)/4`" is negative, since `c = 3b`; read `(c − b)/4`.
* **Theorem 4's proof, necessity, last step (p. 237): defective; statement true** (verified, batch
  151). The points `Y_m`, `Y_n` lie in `R`, not in `M`, so "there exists no connected subset of `M`
  of diameter less than `ε` that contains both `Y_m` and `Y_n`" proves nothing. Repaired within the
  proof: take points of `R̄_n` on the middle square and use `ε/2`.
* **Theorem 4's proof, sufficiency (p. 236): unargued steps; supplied.**
  * The points `B₁, B₂, …` "lying in the order `B₁B₂B₃ …` on the curve `K*`": the proof needs the
    cyclic order of the *continua* `kₙ`, which is supplied. Whether the order of the points alone
    suffices is not settled.
  * The circles about `Bₙ` need `Bₙ ∉ kₙ₋₁ ∪ kₙ₊₁`, which holds by disjointness.
  * "Then `R` is not the sum of a finite collection …" is pigeonhole.
* **Theorem 4's proof: unargued steps.**
  * "every `R_{m̄P_i}` has at least one limit point on the square `T_m̄`";
  * "the boundary of `R_n` contains a closed connected subset `R̄_n` …";
  * "It can easily be seen that no two of the sets `R̄₂, R̄₄, …` …", which is the sector theorem;
  * "every connected point-set … must clearly contain a point either of `k_{n−1}` or of `k_{n+1}`"
    (p. 236), also the sector theorem;
  * the disjointness of the `R_{m̄P}` for fixed `m̄` (they are components).
* **Typographical:** "fie" (p. 233), "curce" (p. 235), "a sumed" (p. 234, footnote).

### A.21 G. T. Whyburn, *Semi-locally-connected sets*, Amer. J. Math. 61 (1939), 733–749, §14

Theorem 14 is verified for bounded and unbounded domains alike, without inversion
(`whyburn39_theorem14`, batch 152). Corollary 1 is verified (`whyburn39_corollary1`, batch 153), by
the arc theorem for Peano continua, a θ-curve in a cyclic Peano continuum that is not a circle, and
the Jordan curve theorem.

* **The formal route differs from Whyburn's.** Moore's curve `C` is replaced by a joining lemma from
  Janiszewski's theorem. Whyburn's curve `K` and limit continuum `H` are replaced by two facts: a
  point where infinitely many disjoint connected sets accumulate has no finite order, and
  `whyburn_3_2`.

* **Theorem 14's proof (p. 747): defective; statement true** (counted, batch 152). "Clearly we may
  suppose `R` bounded, since an inversion of the plane can be used to throw `R` into a bounded
  region complementary to the image of `M`." The centre of inversion must lie in another
  complementary domain. For `M` with no bounded complementary domain, such as a closed disk, there
  is none. The formal proof avoids the inversion.
* **Theorem 14's proof (pp. 747–748): unargued steps and slips (harmless).**
  * "`N` can intersect only one of the arcs `xuy`, `xvy`" is an unargued θ-curve step; it is true.
  * "the arc `x₁xuyy₁` of `J` is contained in `C`" is unargued and true.
  * "`ou − o` lies in `I·V_ε(p)`" should read `ou − u`.
  * The limit continuum `H` lies in `M` and is nondegenerate; both are unargued.
  * "`< 3ε`" after "`< 4ε`": the argument gives `2ε`, and any constant works.
  * "every point of `H`" should read "every point of `H` within `V_ε(p)`".
  * "there exists points" should read "there exist".
  * The finite-cover step for the subarc `xy` is correct, but uniform continuity is unstated.
* **"Hence there exists a simple closed curve `K` in `V_ε(p)` such that `K·M = c + d` …" (p. 748):
  unargued, not decided.** This is the passage from order 2 in `M` to a plane Jordan curve meeting
  `M` in two points. It requires `c` and `d` to be accessible from `Mᶜ`. The formal proof does not
  need it.
* **"by a theorem of R. L. Moore" (p. 748, footnote 14): no theorem number.** The claim is "there
  exists a simple closed curve `C ⊂ J + C_ε` such that if `E` is the complementary region of `C`
  containing `0`, then `E ⊂ I·V_ε(p)`". In substance it is F.A. Theorem 43 (corrected), which is
  proved for spaces satisfying Axioms 1–8 but not yet in `ℝ²`.
* **(6.22), §14 form: verified** (`whyburn39_6_22_sec14`, batch 151).
* **Corollary 1 (p. 749): stated without proof; supplied.** Footnote 16 refers to Wilder 1938,
  Theorem 8a, first corollary. That corollary has the same conclusion under "local 0-avoidability".
* **Footnote 16: unargued remark, not decided, not used.** For cyclic continua,
  semi-local-connectedness is equivalent to Wilder's local 0-avoidability ("it follows by the
  argument given under (6.2)").
* **(6.22): stated without proof** ("results at once from the proof of (6.2) together with §3"), and
  used in a variant form.

### A.22 C. L. Hagopian, *Homogeneous plane continua*, Houston J. Math. 1 (1975), 35–41 (Part E; batch 155)

Verified (batch 155):
* Lemmas 1–4;
* Theorem 1, paragraphs 1–3 (`hagopian75_exists_typeA'`);
* paragraphs 5–13 (`hagopian75_layer_invariant`, `hagopian75_layer_homogeneous`,
  `indecomposable_of_unicoherent_homogeneous`);
* Theorem 1 with paragraph 4 as a hypothesis (`hagopian75_theorem1_of_layer`).

Paragraph 4 cites Bing 1960. It is set aside, because Hagopian 1976 does not use it. Its first
half ("`E` would contain an arc") is verified (`exists_arc_of_degenerate_layers`). Batch 184:
Theorem 1 is verified with paragraph 4 replaced by the named claim `NoArcIndecHomPlane` (no
indecomposable homogeneous plane continuum contains an arc; Bing 1960 in the indecomposable case)
(`hagopian75_theorem1_of_noArc`). The same claim is one of the two inputs of the 1984 route (A.24).

Cited sources verified on the way:
* Moore 1962 Theorems 135–139 (composants);
* Moore 1962 Theorem 22 p. 175 (Janiszewski: a non-unicoherent plane continuum separates);
* Moore 1962 Theorem 84 p. 222 (the triod theorem), by Moore's two cases (Theorems 73, 76, 78, 79);
* Kuratowski Vol. 2 §48 III, IV, VII (sufficiency in Lemma 2).

**No statement is false as printed, and no proof is defective.**

* **p. 35: "a *continuum* is a nondegenerate compact connected metric space".** Recorded.
  Nondegeneracy is needed only for Moore 135–139 and for Theorem 1's conclusion. Lemma 1 holds for
  a point.
* **Lemma 1 (p. 36): three steps unargued, all true.**
  * "each of its composants contains a triod" needs the triod to be proper; `M` itself is not a
    triod, since it is indecomposable.
  * "Since the plane is separable … there exists a proper subcontinuum of `M` having two
    complementary domains that intersect `M`" leaves out that the complementary domains missing
    `M` are pairwise disjoint.
  * "This contradicts the fact that each composant is dense" also needs Baire (composants are
    meagre) and Moore 138.
* **p. 36: definition of an admissible decomposition.** Hagopian's wording ("upper semi-continuous
  … quotient space is the unit interval") agrees with the map form in both directions
  (`admissible_quotient_homeomorph`).
* **Lemma 2 (pp. 36–37): citation imprecise.** "[10, Theorem 3, p. 216]" states that Kuratowski's
  family `D` has the order type of the interval, not that the continuum is of type A′. The gap is
  filled by a countable dense subfamily, Cantor's theorem, and the map `k(y) = inf {q : y ∈ D_q}`.
* **Lemma 3 (p. 37): printed for type A, citing Thomas 1966 (not in hand).** Only the type A′ form
  is proved and used (`hagopian75_lemma3`, `hagopian75_lemma3_unique`).
* **p. 37: misprint "transfromation".** Harmless. Effros is used in the repository's uniform form,
  not as the open map `T_x`.
* **Theorem 1, paragraph 2 (p. 38): two steps unargued; both true and supplied.**
  * "Note that `F`, `f[F]`, and `g[F]` are mutually disjoint." This holds by hereditary
    unicoherence once `f(x)`, `g(x)` lie in composants of `I` other than that of `x`.
  * "It follows that `B ∪ F ∪ f[F] ∪ g[F]` is a triod". The core is `B`.

  "the c-component of `E − Q`" means the component containing `c`. The boundary point `x` comes from
  boundary bumping.
* **Paragraph 9 (p. 39): "`hᵢ[Y] ⊂ hᵢk⁻¹[[r,t]] ⊂ E`" — the second inclusion is unargued; it is
  true** (a triod argument).
* **Paragraph 10: true.** The appeal to "the minimal admissible decomposition of `hᵢ[E]`" is
  replaced by invariance of relative interior. The decomposition is in any case intrinsic
  (`hagopian75_lemma3_unique`).
* **Paragraph 11: "Using the same argument" is paragraph 10 applied to `hᵢ⁻¹`.**
* **Paragraph 13: "[9, Theorem 2]".** Jones 1955 Theorem 2 implies, but does not state, that a
  unicoherent homogeneous plane continuum is indecomposable. Supplied as
  `indecomposable_of_unicoherent_homogeneous`.

### A.23 C. L. Hagopian, *Indecomposable homogeneous plane continua are hereditarily indecomposable*, Trans. AMS 224 (1976), 339–350 (Part E; batches 156–185)

**Status of the formalization.**
* Verified (batch 156):
  * Lemmas 2, 3, 4 (both halves, and the countable form) and 8;
  * the end-set property;
  * Theorem 2, 1975 Theorem 1, the 1975 Corollary, 1975 Theorem 2, and Bing 1960 for plane
    continua, each conditional on Theorem 1 (`Hagopian76Thm1`).
* Open in batch 156, verified since: the first paragraph of Lemma 4 (third sentence), and
  Lemmas 5–7. Lemmas 1–9 are verified.
* Theorem 1: **verified (batch 190) by the 1984 route** (A.24, A.28), not by the printed proof.
  The printed proof is defective: its case split fails at the last step of the induction (below,
  "The proof now breaks down into two cases"). On the 1976 route Theorem 1 is reduced by
  `hagopian76_theorem1_of_cases4` (batch 185) to named claims, which stay open (Status at the
  top). Entries below that say "open" refer to that route.
* So Theorem 2, the three 1975 statements and Bing 1960 for plane continua are verified without
  the hypothesis `Hagopian76Thm1` (batch 190).

**Other proofs.** Hagopian 1984, Corollary 3, re-proves Theorem 1 by F. B. Jones's 1969 plan,
without pp. 348–349. It is the second route of this project (A.24). Batches 184–186 alternated
between the two routes (David's decision, 2026-10-16); from batch 187 they stayed on the 1984
route. J. T. Rogers, Jr., Proc. AMS 102
(1988), re-proves the 1984 Corollary 1 by a decomposition theorem and reports no defect in the 1984
paper.

**Standing remark.** §2 and Theorem 1 argue by contradiction from a type A′ subcontinuum that, by
Theorem 1, does not exist. So no §2 statement can be refuted inside a homogeneous indecomposable
`M`. A step can only be proved, or shown not to follow from the hypotheses its proof uses.

* **Lemma 3 (p. 340): true as printed.** "This lemma follows from the argument presented in
  paragraphs 9 through 11 in the proof of Theorem 1 of [5]." The 1975 argument uses an `ε`. Lemma 3
  replaces it with `h[Y] ∩ (T ∪ V) = ∅`, and the argument adapts (`hagopian76_lemma3`).
* **Lemma 4 (pp. 340–341): true as printed; two steps unargued, supplied.**
  * The triod "`H ∩ d⁻¹[[s, 1]]` would separate `F ∪ H` into three nonempty disjoint open sets" is
    supplied with explicit arms.
  * The second step is "Since `F` is irreducible between `X` and `d⁻¹(1)`, it is a proper subset of
    an element of `𝓕` that is contained in `F ∪ h⁻¹[F]` (Lemma 1)". It needs:
    * a case analysis on how `h⁻¹[F]` meets `F`;
    * an irreducible continuum shown to be of type A′ by Kuratowski's criterion;
    * a three-continua argument for the configuration in which a layer of `h⁻¹[F]` contains a tail
      of `F`.

    About two hundred lines of Hagopian's step are missing (`exists_proper_extension`).
* **Lemma 4, first paragraph (p. 341): third sentence unargued; reason given insufficient.**
  "Since the decompositions of `E` and `F` are minimal, each element of the decomposition of `E`
  (except possibly `k⁻¹(1)`) is an element of the decomposition of `F`."
  * Minimality gives it only for layers in `d⁻¹(u)` with `u < s` (`hagopian76_lemma4_layers'`).
  * A plane model without homogeneity (the half-bar, `OPEN.md` D1) has a layer `k⁻¹(t)`, `t < 1`,
    swallowed by `d⁻¹(s)`.
  * The first two sentences ("`d[E] = [0, s]`"; "`d⁻¹(r)` is in `E`") are true.
  * The two forms are equivalent without homogeneity (batch 157).
  * **Verified (batch 158)**, in the strong form `E = d⁻¹[[0, s]]` with every layer of `E` a layer
    of `F` (`hagopian76_far_layer`, `hagopian76_initial_segment`).
    * Lemma 5 at interior layers (proved from Lemmas 2 and 3) is applied to `F` itself. With the
      continuity of `k`, it forces `d⁻¹(s) = k⁻¹(1)`.
    * The strong form is what p. 347 uses: "`d⁻¹[[0, e]] = E`".
* **Lemma 5 (p. 341): verified (batch 158); Hagopian's continuum `F` not needed.**
  * Interior layers: by Lemma 3 with `F := E`.
  * End sets: by one extension on each side, through D1.
  * "There exists a type A′ continuum `F` in `R(E)` that is the union of two extensions" is unargued
    and not decided. It is not used.
* **Lemma 6 (pp. 341–343): verified (batch 160); the proof is longer than it needs to be.**
  * Steps 1–3 are true; step 3 ("Note that `B − C` is contained in `K`") is unargued.
  * Step 4 is `hagopian76_lemma4_seq`.
  * Step 5's "Since `M` is atriodic, it follows that `f[L]` is a subset of `R(X, E)`" is unargued
    and true. In general form it is *absorption*: a continuum missing `X` and meeting an extension
    lies in `R(X, E)`. Absorption gives `C ⊆ R(X, E)`, hence `c ∈ R(X, E)` and the contradiction at
    once.
  * Hagopian's intermediate claim "The point `c` belongs to `Cl R(X, E) − R(X, E)`" is the
    conclusion of a proof by contradiction. Steps 6–7, which refute the case `c ∉ R(X, E)`, are
    therefore superfluous. They were not checked; they are not wrong as far as checked.
  * Step 8 is proved by the 1975 ¶2 argument without the homeomorphisms `f₁`, `f₂`.
* **p. 343, "Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`" and "every continuum
  essential to `R(E)` is of type A′ (Lemma 5)": unargued, true, verified (batch 160).** The second
  needs the containment of an essential continuum in one extension, which is also unargued; it is
  supplied through "`R(X, E)` is not closed".
* **Lemma 7 (pp. 343–344): verified (batch 162); two sentences unargued, both true.**
  * "By Lemma 2, an integer `i` and a homeomorphism `f` … exist such that a continuum `F` essential
    to `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects `A`" is true read literally. Take `F` in
    the translate `fhᵢ[R(E)]`, on the side of the layer `f[Uᵢ]` away from `t`. This uses the density
    of both half-rays from any layer (`halfray_dense`) and the fact that the two half-rays meet only
    in the layer (`halfray_inter`).
  * The intermediate reduction to arbitrary points of one composant (`Lemma7F`, batch 161) is too
    strong and is not needed.
  * "Note that `g[F] ∪ Hⱼ` is a triod in `M`" is true.
* **Theorem 1, T10, Property 2 (p. 346): verified** (`hagopian76_property2`, batch 162), for every
  `ε₂ > 0`.
* **Theorem 1, `ε₁` (pp. 345–346): "Note that if `h` is an `ε₁`-homeomorphism of `M` onto `M`, then
  the chain formed by taking `ε₁`-neighborhoods … follows `h[E]`": unargued.**
  * It does not follow from the four printed families. Nothing separates `k⁻¹[[0, 1/11]]` from
    `k⁻¹[[2/11, 3/11]]`.
  * It is true after shrinking `ε₁` (`hagopian76_eps1`, `hagopian76_eps1_chain`, batch 161). It is
    recorded as an unargued step with a repair, not as a defective proof.
* **Theorem 1, Property 1 (p. 346): unargued, true, verified** (`hagopian76_property1`, batch 161).
* **Lemma 9 (pp. 344–345): verified, in a stronger form (batch 163).**
  * The hypothesis "Assume `U` and `Y` are not decomposably accessible from a side of `E`" is not
    used.
  * The argument proves more: no point of `π[M]` lies in a strip just below `π[E]` away from the
    accessing arc (`no_M_below`).
  * "Since `M` is atriodic and `h(u)` is not in `E`, the sets `G₂ ∩ E` and `G₂ ∩ h[E]` are disjoint"
    is unargued and not used. Its consequence, `h[D] ∩ C = ∅`, is proved directly.
  * "this is impossible [13, Theorem 28, p. 156]": replaced by a collar rectangle, boundary bumping
    and freeness. Theorem 28 itself is verified (batch 158). The printed application, with disc
    links and interlaced points, is not supplied by the printed `L` and was not decided.
  * "`π[Gᵢ]` is an open disk": true for collar rectangles, and not needed.
* **T3 (p. 345) and T6 (p. 346, "It follows from the proof of Lemma 9 …"): true, verified (batch
  163)** at interior points (`hagopian76_T3`, `hagopian76_T6`).
* **p. 345: "Since `M` is homogeneous, we can assume without loss of generality … that
  `π[k⁻¹(i/22)] = (i, 0)` for each integer `i`": true, verified (batch 164).** It is a relabelling
  by a homeomorphism of `[0, 1]` (`hagopian76_reparam`). Homogeneity is not needed for it. With it,
  T6 holds at Hagopian's abscissae `[3/22, 19/22]` (`hagopian76_I1`).
* **p. 346, T7: "Let `y` be a point of `M ∩ L₆` that is accessible from `R² − M` such that `π(y)` is
  above `π[E]`": unargued, true, verified (batch 164)** (`exists_accessible_above`). The proof needs
  that `π[M]` approaches `π[E]` from above, which holds because a proper subcontinuum of `M` has no
  interior (`M_meets_above`).
* **p. 346, T7: "There exists an arc `A` in `(St L) − M` to one side of `h[E]` that meets `L₁` and
  `L₁₁` (Lemma 9 (proof)). By choosing `y` sufficiently close to `E` and `h` sufficiently close to
  the identity, we get that every point of `R²` between `⟨p₁, p₅⟩` and a subarc of `π[A]` … belongs
  to `π[St L]`": unargued; the statement it serves is true, verified (batch 165) by another route.**
  * The citation is right in substance: Lemma 9's argument applies to the type A′ continuum `h[E]`.
    Which side of `π[E]` the arc `π[A]` lies on is not argued, nor is the second sentence.
  * The arc `I₂` exists in every thin collar rectangle over `⟨p₁, p₅⟩` (`hagopian76_T7`), without
    `y`, `h` or Lemma 9. A continuum of `M` that meets `E` and misses both end sets lies in `E`
    (`hagopian76_no_hair`, from Lemma 6's absorption step). So no continuum of `π[M]` joins the axis
    to the top of the rectangle, and Janiszewski's theorem gives a crossing arc in the complement
    (`rect_crossing`).
* **pp. 345–346, `ε₁` and property (D) of T9 ("every point of `M ∩ Cl π⁻¹[D]` lies in one of
  `L₂, …, L₁₀`", used tacitly): unargued; true after shrinking `ε₁` (batch 165).** The printed
  families keep `G₁` off the vertical `⟨o₁, q₁⟩` but not off the region to its right. One more
  term, `EndCtl`, gives property (D) (`hagopian76_T8`). Whether (D) fails for the printed `ε₁` is
  not decided.
* **p. 346, T9: "Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is the
  image of a subcontinuum of `E` …": true, verified (batch 165)** (`hagopian76_T9_full`), with
  `Cl B ∩ E = ∅` from `hagopian76_no_hair`. "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`":
  unargued; superseded in a finer form (batch 177), see the next entry but one.
* **p. 346, T8: "Let `D` be the bounded complementary domain of `I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪
  ⟨p₅, s⟩` in `R²`": true, verified (batch 166)** (`rect_domain`, `hagopian76_D`).
* **p. 346, T9: "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`": unargued; open.**
  * My suggested route (both ends of `Cl B` on the side edges) fails at one step. An end of
    `Cl B` is part of a layer, and continuing `B` past it inside `π⁻¹[D]` is not argued.
  * Lower semicontinuity of the layers excludes Aristotle's `sin(1/x)` illustration. It does not
    give the connected continuation.
  * Batch 167 proves the sentence for the components Hagopian uses, those through `h(x)` with `h`
    small, by translates.
  * **Superseded (batch 177).** Fix the resolution before `D`: `n`, then `θ(n)`, then Effros's `δ′`,
    then the height `c(n)`. Then every component of `M ∩ π⁻¹[D]` through a point over the inner
    middle `[3/22 + 3/n, 19/22 − 3/n]` is a *strand*. Its closure lies in a `θ/4`-translate `h[E]`
    and contains `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`. Along it, positions are within `2/n` of the
    parameter (`strand_lemma`, `strand_fine_positions`). The chain `L` is not needed.
* **p. 347, T12: "Let `p` and `q` be points of `K ∩ (W − R(E))` that belong to distinct inaccessible
  composants [10] of the indecomposable continuum `Cl R(E)`": inaccessibility is never used
  afterwards (batch 166).** The citation of Mazurkiewicz 1929 is unnecessary. Two points of `W` in
  distinct composants off `R(E)` exist by Baire (`exists_two_composants_in_open`). That they can be
  taken on `K` is unargued; open.
* **p. 347, T12: "To see this let `x` be a point of `k⁻¹(p₃) ∩ Cl K`": true with `x` chosen as a
  limit of points of `M ∩ K₀`, verified (batch 167)** (`K0_dense_low`). For such `x`, the
  components through `p = h(x)`, `h` small, cross `D` and are followed by `L − {L₁, L₁₁}`
  (`crossing_translate`, `hagopian76_T12_parts12`). Hagopian's (2) is verified with T9's
  homeomorphism in place of his `h`. **Batch 177: his own `h` works**, once it is a
  `θ/4`-homeomorphism (`strand_essential`, `exists_T12Data`). This is Hagopian's "by Lemma 5".
* **p. 347, T12: "let `x` be a point of `k⁻¹(p₃) ∩ Cl K`": the choice must be restricted.** An
  arbitrary point of the layer need not have points of `M ∩ K` nearby, and `p ∈ K ∩ W` needs them.
  Repair: take `x` as a limit of points of `M ∩ K₀`.
* **p. 347, T12: "Let `p` and `q` be points of `K ∩ (W − R(E))` that belong to distinct
  inaccessible composants [10] of the indecomposable continuum `Cl R(E)`": of these conditions only
  `p`, `q ∉ R(E)` is used in T13–T17 (batch 168).** "Inaccessible", "distinct composants" and
  "`p`, `q ∈ Cl R(E)`" are never used.
* **pp. 347–349, a tacit dichotomy: "if `g[R(E)]` meets `R(E)`, then `g[R(E)] = R(E)`"; unargued,
  open.** T17 needs `h[R(E)] ∩ R(E) = ∅` and `h₁[R(E)] ∩ R(E) = ∅`. Hagopian obtains them from
  `p`, `q ∉ R(E)`, which needs the dichotomy. It holds if `Cl R(E) = M`, by the disjointness of
  composants; that equality is not decided.
* **p. 347, T12: "By Property 1, `R(E)` intersects an arc in `K` that is irreducible between `C`
  and the `q`-component …, and `R(E)` separates these components in `π⁻¹[D]`": true in substance,
  verified (batch 168).** Crossing pieces of `R(k⁻¹(0), E)` exist near `x`, each inside one
  extension (`crossing_piece_of_R`). Such a piece separates the components through points below and
  above it (`crossing_separates`, `hagopian76_T12`).
* **p. 347, T13: "Let `F` be a continuum that is irreducible with respect to the following
  properties … The existence of such a continuum `F` follows from Property 1 and the fact that
  `Cl R(E) = Cl R(k⁻¹(0), E)`": unargued; true, verified (batch 170)** (`hagopian76_T13_uncond`).
  The proof uses Zorn's lemma, Lemma 4's strong form and `piece_map`, not the reasons printed.
  `p`, `f(p)` off the separating extension come from `exists_generic_pq` (batch 169).
* **p. 349, T17: "Since no point of `N` is within `ε₂` of `Q`, the continuum `f[N]` does not
  intersect `P`": gap.** It also needs `f[N] ∩ F = ∅`, that is, `h₁[R(E)] ∩ R(E) = ∅`: the
  dichotomy above.
* **The tacit dichotomy: not needed (batch 171).** What T17 uses, `h[R(E)] ∩ R(E) = ∅`, follows
  from choosing `h(x)` off the composant of `x`, a meagre set that contains `R(E)`
  (`translate_Rset_disjoint`, `hagopian76_T12_uncond`). So Hagopian's tacit step is supplied by a
  different argument. The dichotomy itself is proved from `Cl R(E) = M` (batch 169); neither is
  decided in general.
* **p. 347, T12, `p`, `q ∈ K`: not needed for genericity (batch 169).** The induction uses two
  properties of `K` (batch 180): `p ∈ K`, and `K` meets every crossing component
  (`Thm1Setup.K_meets_crossing`). Points off `R(E)` are generic, because
  `R(E)` is meagre (`isMeagre_Rset`). `K` serves only as the reference for positions.
* **p. 347: "It follows from Property 3 that `I` is finite": unargued steps; true, verified (batch
  174)** (`hagopian76_I_finite`). The omitted step is that distinct members of `I` have disjoint
  interiors. That step does not use Property 3. The closure of a crossing component contains the
  whole layers of its interval, so two components with overlapping intervals coincide.
* **pp. 347–348: "Note that `x₁ = 0`, `x₂ = e`, and `x₂ₙ = 1`."**
  * `x₁ = 0` and `x₂ = e`: true, verified, with `e < x` for every member of `I` (`hagopian76_J_xs`).
  * `x₂ₙ = 1`: unargued, open. It depends on the irreducibility of `F` (T13), and is false for a
    general extension (`F = E` gives `I = ∅`). Batch 175 reduces it to `TailCutKeepsSep`: cutting
    off the part of `F` beyond its last crossing block keeps the separation of `p` from `f(p)`.
    Batch 176 reduces that to `SepByCrossing`. Batch 179 proves it from saturation alone
    (`hagopian76_x2n_eq_one_final`); saturation is the entry "The end layer of `F`" below.
* **p. 348: "Note that `[x₁, x₂]` does not have Property 4": true, verified (batch 174)**
  (`hagopian76_property4_base`), from the connectedness of `π⁻¹[D]`.
* **p. 348: "Note that `f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`": unargued; the position part verified
  (batch 176).** For `ε₃` small, a point of `M` within `ε₃` of a point over `1/2` and lying over
  `D` lies over abscissae in `(3/8, 5/8)` (`eps3_positions_middle`). Shrinking `ε₃` keeps
  Property 2. That `f(yᵢ₋₁)` lies in `π⁻¹[D]` at all is assumed there, not proved. It needs `ε₃`
  small with respect to `D` (chosen before `F`), and `f(yᵢ₋₁) ∉ E`, which holds by the choice of
  `h₁` off the composant. Verified (batch 181, `f_mem_O_of_mem_K`), with the bound `hε₃O`.
* **p. 348, Property 4 for the top block: unargued; verified from `SepByCrossing` (batch 176)**
  (`hagopian76_property4_top`). The step "only the top block separates" is Janiszewski's theorem
  inside `π⁻¹[D]` (`sepIn_union_cases`) together with the irreducibility of `F`. From saturation
  alone: batch 179 (`hagopian76_property4_top_final`).
* **p. 348, the block ends `x₁ < x₂ < ⋯ < x₂ₙ`: that every member of `I` is nondegenerate is not
  stated; true, verified (batch 179)** (`crossingIntervals_nondegenerate`). A member `[u, u]` would
  belong to a crossing component inside the layer `d⁻¹(u)`, which Property 3 as printed excludes.
* **Theorem 1, the order of the constants: not fixed by the text; fixed (batch 177).** The text
  introduces `ε₁`, `L`, `D`, `ε₂`, `ε₃` in that order, and the fine control the endgame needs is not
  among them. Fixing a resolution `n → θ(n) → δ′ → η → c(n)` before `D`, and taking `D` of height
  `≤ c(n)`, constrains nothing downstream: T7 gives `I₂` at every height, and `ε₁`, `L`, `ε₂`, `ε₃`
  are untouched (`StrandConst`, `strand_fine_translate`). Batch 179 checks the other heights the
  endgame uses (Property 3, the finiteness of `I`, the middle-crossing lemmas). None depends on `F`
  in substance, and each is chosen before `F` (the `…_unif` theorems). So `F` (T13) may come after
  `D`, as printed.
* **p. 348, T17: "Since `L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and `Cl Cᵢ`, the continuum `N` does not
  come within `ε₂` of `π⁻¹(p₄)`": unargued; open. The range obstruction is removed (batch 177).**
  `p₄` is over `15/22`, which lies in the inner middle for `n ≥ 15`, so strand positions control
  `N` there (`strand_fine_positions`). The chain `L`'s control stops at `[3/8, 5/8]`, which excludes
  `15/22`. Which strands `N` runs along is the Case 1 question below. The sentence that uses it
  (p. 349, "Since no point of `N` is within `ε₂` of `Q`") needs the distance from `Q`, an arc of
  the vertical over `p₄` above `π⁻¹(p₄)`. The points of `N` outside `π⁻¹[D]` are not addressed
  (batch 180, open).
  * Batch 183: the sentence is now the named `Prop` `Thm1Setup.FarFrom`, for the subcontinuum `H`
    of E2.4 (with `p₂` in Case 2). `L` follows the components only inside `π⁻¹[D]`. Outside `D`,
    `L` may enter a pocket of the complement near `p₄` from the far side; nothing proved excludes
    it.
  * Bing's sentence in the same place is also unargued (1960, p. 227): "Note that no point of the
    arc `pq` in `M` is within `ε₄` of this vertical part of `J` above `a₄`."
* **p. 348, Case 1: "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see that `yᵢ₋₁` is
  between `d⁻¹[I]` and `d⁻¹[J]`": unargued; open (batch 177).** The position argument closes a
  region with the gap continuum `d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]`. That this continuum together with the rest
  separates the plane is the unicoherence of the plane (the converse of Janiszewski's theorem). The
  text neither states nor cites it. Whether the bounded side matters, and whether the blocks `I`,
  `J` can interleave, are not decided.
  * Batch 183, with Bing's reason ("It follows from the Jordan curve theorem that `q` lies between
    …", 1960, p. 226). Let `A = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` and let `σ` be the part of the side segment
    between the points where `Cl S_J` and `Cl S_I` meet it. The two sides of `σ` lie in different
    components of the complement of `A ∪ σ`, by unicoherence (not formalized). `L` misses `F`, so it
    stays in one component until it meets `π⁻¹[D]` again.
  * What is missing is that this component meets `π⁻¹[D]` only through `σ`. Suppose that near an
    end of a strand `F` has no points outside `D`, so that the strand only touches the side segment
    there. Then the component passes around that end, and `L` may re-enter `π⁻¹[D]` on the far side
    of the strand (the batch-180 configuration).
  * Bing's arcs end exactly on the side line, at the points where the gap arc begins. Hagopian's
    strands, components of `F ∩ π⁻¹[D]`, need not. Open; not refuted.
* **The end layer of `F` over `D` (needed by "Note that `x₂ₙ = 1`" and by Property 4 for the top
  block; not in the text): open since batch 178; closed in batch 185 by 1984 Lemma 7.** Saturation
  is verified with no hypotheses (`innerComponentsCross_hagopian`). The tip layer `h[k⁻¹(τ)]` is a
  layer of `F` by Lemma 7 (`h[E] ⊄ F ⊄ h[E]` by S0), hence `d⁻¹(1)`, which would then lie over `D`,
  against `T12Data.end_layer_not_subset`. The chunk argument of batches 179–183 below is no longer
  used. So the 1976 text needs, at this step, a lemma that appears only in Hagopian's 1984 paper.
  History: Separation along the vertical (commission 178 §2) turns `SepByCrossing` into "every
  component of `F ∩ π⁻¹[D]` through a point over the inner middle crosses" (`InnerComponentsCross`).
  * A non-crossing such component has an inner tip at which `d⁻¹(1)` meets a translated layer.
  * `d⁻¹(1) ⊄ π⁻¹[D]` follows from the irreducibility of `F` (verified, batch 178:
    `T12Data.end_layer_not_subset`).
  * A triod excludes the tip unless `d⁻¹(1)` swallows a chunk of the translate through the point
    (batch 178, configuration 3.3).
  * Commission 179 proposes excluding that configuration by the void interior of `d⁻¹(1)`, the
    finiteness of the crossing components, and the triod at nearby points of lower layers.
  * Batch 179: the finiteness of the crossing components is verified
    (`crossing_components_finite`; it needs the nondegeneracy of `I`). Two points of the route
    need care.
    * The triod needs its core `Λ₁ ∪ h[k⁻¹(τ)]` connected. It is: step 3.1 of commission 178
      already shows that `d⁻¹(1)` meets the tip layer.
    * The strand claim at the nearby points needs the limit point over
      `(3/22 + 4/n, 19/22 − 4/n)`, not the inner middle. A margin: saturation is to be stated on a
      narrower interval, with `n` raised.
  * Batch 180, verified: `d⁻¹(1)` meets the tip layer (`tip_meets_end_layer`, and its mirror form);
    the tip triod on both sides (`tip_triod`, `tip_triod_mirror`); the triod on the tip layer when
    its third arm is nonempty (`tip_triod_on_tip_layer`); the degenerate chunk
    (`degenerate_chunk_iii`).
  * Batch 181, verified: the edge case when the chunk of `d⁻¹(1)` in the translate ends before the
    translate's far end (`chunk_edge_case_mirror`, through `tip_triod_mirror_rel`).
  * Still open:
    * the reduction of a non-crossing component to "one half lies in `π⁻¹[D]`" (sound on paper
      since batch 178);
    * the nearby points `zⱼ` of the nondegenerate chunk;
    * the edge case in which `F ∩ hⱼ[E]` lies in the tip layer;
    * the edge case in which the chunk reaches the far end of the translate (`τ₁ = 1`).
* **p. 348, Case 1: Hagopian's `Q` (batch 178).** One segment of the vertical over `p₄` between
  consecutive points of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` closes the band between the two blocks only if the
  band crosses that vertical once. In general the band crosses it in several strips, and the segment
  must be the one `Cᵢ` meets first from the left. "Between `d⁻¹[I]` and `d⁻¹[J]`" must be read
  between adjacent strands in the order of strands, since `I`- and `J`-strands may interleave. Gap
  in exposition; open.
* **p. 349, Case 2: unargued claims; open (batches 178, 180).** The printed paragraph is: "If
  `yᵢ₋₁` is above `d⁻¹[J]`, it is between `d⁻¹[I]` and `d⁻¹[J]`, and `f(yᵢ₋₁)` is above `d⁻¹[I]`.
  Since both `yᵢ` and `yᵢ₋₁` are within `ε₃` of `d⁻¹[I]`, it follows as in Case 1 that a
  subcontinuum of `L` violates Property 2. Hence `yᵢ₋₁` is below `d⁻¹[J]` and `f(yᵢ₋₁)` is above.
  Therefore `J` has Property 4."
  * (a) "If `yᵢ₋₁` is above `d⁻¹[J]`, it is between": no reason is given. Report 180 describes,
    informally, a configuration consistent with the minimality of `L`, `L ∩ F = ∅`, Property 2 and
    the order of strands in which the side of `Cᵢ₋₁` relative to an `I`-strand is not the one the
    text needs. `L` leaves `π⁻¹[D]` through a side segment and re-enters on the other side of that
    strand's end.
  * (b) "`f(yᵢ₋₁)` is above `d⁻¹[I]`": no reason is given. If `f(yᵢ₋₁)` is below `d⁻¹[J]`, then
    `J` has Property 4 at once. So (b) is needed only for the remaining case, where it amounts to
    the band argument of Case 1.
  * (c) "Hence … `f(yᵢ₋₁)` is above": no reason is given. When `yᵢ₋₁` is below `d⁻¹[J]`, the band
    argument leaves `f(yᵢ₋₁)` above `d⁻¹[I]` or below `d⁻¹[J]`, and the second is not excluded.
  * Batch 181 (in the claim labels of commission 181):
    * "both `yᵢ` and `yᵢ₋₁` are within `ε₃` of `d⁻¹[I]`" follows from (b) by the cap lemma
      (verified, `case2_ending`);
    * the band of Case 1 does not obviously exist in Case 2, where the gap continuum meets both
      side segments;
    * Aristotle finds nothing in Property 2, the Case 2 configuration, or the choice of `yᵢ₋₁`
      that excludes `f(yᵢ₋₁)` below `d⁻¹[J]` when `yᵢ₋₁` is below it. That claim is unsupported
      by the text;
    * the hypothesis "`π⁻¹[⟨p₅, s⟩]` meets … `d⁻¹(x₂ᵢ₋₃)`" is probably not a misprint for
      `x₂ᵢ₋₂`, which would contradict the case hypothesis.
  * Bing 1960, p. 227 (Case 2) has the sentence behind (c): "If `v` is below `x₂ᵢ₊₁x₂ᵢ₊₂`, `q` is
    below `x₂ᵢ₊₁x₂ᵢ₊₂` and `h(q)` is above."
    * On my reading it follows from Bing's simple closed curve `J` (p. 227, Case 1). `J` is a
      vertical interval in `K` together with an arc containing the gap arc.
    * The reading needs the gap arc to pass outside `K` on the side away from the base arc, as in
      Bing's Figure 3. Then the image of `pq` stays in the complementary domain of `J` containing
      `h(p)`, which lies above the `J`-arc.
    * Whether Hagopian's gap continuum can instead pass around an end of `π[E]` is open.
  * Batch 182: neither extending away from `Z` nor Property 2 for `f[N]` decides (c).
  * Batch 183 corrects my reading. In Bing, the side of `h(q)` follows from the parity of crossings
    of the simple closed curve `J`, whichever way the gap arc runs (over the top or underneath).
    Aristotle checked this by hand on polygons; it is not formalized. So the route of the gap arc is
    not a gap in Bing. The exception is that the gap arc might enter `K`, which Bing does not
    discuss.
  * For Hagopian's continuum `P` there is no parity argument. The Janiszewski form in the
    repository separates the two sides of `Q`, not the two sides of `S_I`. (a), (b), (c) are open.
  * (d) "it follows as in Case 1": reduced to E2.4 with `π⁻¹(p₂)` in place of `π⁻¹(p₄)`, after
    Bing's `a₂` (`Case2WitnessE24`).
* **p. 349, Case 1: "It is not above `d⁻¹[I]` because `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃` and
  `ρ(yᵢ₋₁, f(yᵢ₋₁)) < ε₃`": unargued; open (batch 180).** The segment from `yᵢ₋₁` to `f(yᵢ₋₁)`
  misses `d⁻¹[I]`. It may still leave `π⁻¹[D]`, through the bottom edge, which lies over `E`, and
  `yᵢ₋₁ ∈ K` may be arbitrarily close to `E`. Proposed repair (commission 181): the region above an
  `I`-strand has closure missing the bottom edge, so a short connected set from below the strand to
  above it meets the strand, `π⁻¹[I₂]` or a side segment. The last two are excluded by `ε₂` and by
  a new bound on `ε₃`, chosen before `F`. Verified (batch 181): `above_closure_misses_bottom`,
  `cross_strand_near`, with the bound `hε₃S`.
* **pp. 348–349, Cases 1–2: they follow Bing 1960 pp. 225–227 ("Following Bing [2, p. 225]",
  p. 348), and Bing gives several reasons that Hagopian omits (my batch-182 reading, page images at
  200 dpi).**
  * "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see that `yᵢ₋₁` is between" is Bing's
    "It follows from the Jordan curve theorem that `q` lies between `x₂ᵢ₋₁x₂ᵢ` and `x₂ᵢ₊₁x₂ᵢ₊₂`"
    (p. 226).
    * The arc leaves `K` at `u`, between `x₂ᵢ` and `x₂ᵢ₊₁` on the side line.
    * It cannot cross the gap arc, which lies in another arc component.
    * So it re-enters `K` between the same two points.
    * In Hagopian, the gap continuum `d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]` plays the part of the gap arc, and
      `L ∩ F = ∅` that of the different arc component.
  * E2.4 ("for otherwise, a subcontinuum of `L` would violate Property 2") is Bing's arc `ab`
    (p. 227).
    * If `q` is above `tu`, then `a = p`, and `b` is a point of `vw` between `p` and the `I`-arc.
    * If `q` is below `tu` and within `ε₄` of the `I`-arc, then `b = q`, and `a` is a point of `tu`
      between `q` and the `I`-arc.
    * Either way `ρ(a, b) < ε₄`, while `ab` is long and stays away from `a₄`.
    * So the ends of the offending subcontinuum are a point of `Cl Cᵢ` and a point of `Cl Cᵢ₋₁`
      lying close together across a strand. They are not `yᵢ` and `yᵢ₋₁`. Batch 182 tried the
      subcontinuum `N` between `yᵢ` and `yᵢ₋₁`, whose end sets need not be close.
  * "`f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`" is Bing's simple closed curve `J`
    (p. 227): a vertical interval above `a₄` together with an arc containing the gap arc.
  * Bing's arcs become continua in Hagopian. Each reason therefore needs a continuum form:
    Janiszewski and unicoherence in place of the Jordan curve theorem, and composants in place of
    arc components.
  * Batch 183 (Aristotle, from page images at 200 dpi): the dictionary and my transcriptions agree
    with the pages. Which reasons carry over:
    * the arc `ab`: yes. The two close points are verified (`e24_pair_between`, `e24_pair_below`);
    * "a subarc of an arc between two points": yes, through Lemma 5. The part of `L` between two
      layers, with the layers kept, needs lower semicontinuity in general
      (`minimalAdmissible_restrict_of_lsc`);
    * the Jordan curve theorem for "between": only in part (entry "By considering the position"
      above);
    * "the image … does not intersect `J`. Hence `h(q)` is …": no, since it rests on parity (Case 2
      entry);
    * "no point of the arc `pq` … within `ε₄` of this vertical part of `J`": unargued in both;
    * `a₂` in Case 2: adopted.
  * One slip of Bing's own (p. 227), harmless: he supposes "`ρ(q, x₂ᵢ₋₁x₂ᵢ) ≥ ε₄`" and then writes
    "It is not above `x₂ᵢ₋₁x₂ᵢ` because `ρ(q, x₂ᵢ₋₁x₂ᵢ) > ε₄` and `ρ(q, h(q)) < ε₄`". The weak
    inequality suffices.
* **p. 348, E2.4: "The point `yᵢ₋₁` is below `Cᵢ` and `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`; for otherwise, a
  subcontinuum of `L` would violate Property 2": reduced (batch 183).**
  * The subcontinuum is Bing's `ab`: the part `H` of `L` between a layer through a point of `Cl Cᵢ`
    and a layer through a point of `Cl Cᵢ₋₁`, the two points within `ε₃` across one strand.
  * Verified: the two points, `H` with its layers, and the contradiction with Property 2
    (`property2_violation`). They are conditional on three claims, each a printed sentence or
    implied by one (`E24Claims`):
    * `h⁻¹[H]` is essential to `R(E)`;
    * some layer of `H` is farther than `ε₂` from an end set;
    * `H` does not come within `ε₂` of `π⁻¹(p₄)` (T17; entry above).
  * Verified only for the `I`-strand `S_I` next to `Cᵢ`, not for all of `d⁻¹[I]` as printed. For an
    `I`-strand below `Cᵢ` the segment from `yᵢ₋₁` need not cross `Cl Cᵢ`. The printed form is not
    decided.
  * My check of the reduction: under Property 2, `E24Claims` at `yᵢ₋₁` for `Cl Cᵢ` amounts to
    `ρ(yᵢ₋₁, Cl Cᵢ) ≥ ε₃`, since `Cl Cᵢ ⊆ L`. That is stronger than the conclusion, as it should be
    in a proof by contradiction. The three sub-claims are where the work is.
* **p. 348: "Then `d⁻¹[J]` separates `yᵢ` from `f(yᵢ)` in `π⁻¹[D]` and `J` has Property 4 unless
  `yᵢ` is above `d⁻¹[J]`": true in strand terms, given saturation; verified (batch 181)**
  (`property4_strand`, `property4_step_unless_setup`, with 3c `block_components_cross`).
* **p. 348: "(Other cases are handled with similar arguments to that given in this case.)": gap in
  exposition (batch 181).** The four cases are: `f(yᵢ)` above or below `d⁻¹[I]`, and `d⁻¹[J]` below
  or above `d⁻¹[I]`. The frame is not symmetric top to bottom: the bottom edge lies over `E`, the
  top over `I₂`.
  * E0 and E1 are symmetric (verified).
  * Aristotle's mirror of the cap lemma (`cross_strand_near_mirror`) carries an extra hypothesis:
    the point must be `ε₃`-far from the bottom edge.
  * On my reading the extra hypothesis is not needed. The argument can always use the region above
    the strand, whichever point lies there. Verified (batch 182, `cross_strand_near_above`).
  * Batch 182 covers the printed configuration and its mirror, in which `d⁻¹[J]` lies on the side of
    `yᵢ`. The other two, with `d⁻¹[J]` on the side of `f(yᵢ)`, are not treated: E1 then leaves
    `f(yᵢ)` between the strands, and `f(yᵢ)` is not a point of `K`. Bing's text (1960, p. 226) has
    the same parenthesis. On my reading, Bing's `K` is a disc, so the roles of `p` and `h(p)` might
    be exchanged by carrying the induction for `h` or `h⁻¹`. Hagopian's `K` is an arc, and `f(yᵢ)`
    need not lie on it. Not checked.
  * Batch 183: my proposal (Property 4 for points over the middle, carried for `f` or `f⁻¹`) fails
    as stated.
    * E1 places `f(yᵢ)` over `(3/8, 5/8)` only, not over the middle interval
      `[1/2 − 2/n, 1/2 + 2/n]`, and the cap from `f(yᵢ)` uses the `ε₃` bounds stated on that
      interval.
    * That the closure of the component of `f(yᵢ)` is essential to `h₁[R(E)]` does not follow from
      the corresponding fact for `Cl Cᵢ` and `h[R(E)]`.
    * Aristotle suggests a possible repair, not carried out: state the `ε₃` bounds on the points
      over `[1/2 − 4/n, 1/2 + 4/n]`. The two orientations remain open.
* **p. 348, "The proof now breaks down into two cases": the case split presupposes that
  `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` each meet a side segment `π⁻¹[⟨p₁, r⟩]` or `π⁻¹[⟨p₅, s⟩]`.
  Unargued (batch 181). At the last step of the induction (`i = 2`, `J = [x₁, x₂] = [0, e]`) it is
  false.** There `d⁻¹(x₂) = d⁻¹(e) = k⁻¹(1)` (`ext_layers`). That layer lies over `γ(1)`, the far
  end of `π[E]`, and meets neither side segment. So neither printed case applies to the step that
  produces the final contradiction with "`[x₁, x₂]` does not have Property 4". In that step
  `d⁻¹[J] = E` misses `π⁻¹[D]` altogether, so there are no `J`-strands. Found in my batch-181 audit;
  the certificate is verified (batch 182, `blockLayersMeetSides_false`). The last step is read
  separately, with the bottom edge in place of the `J`-strand (`last_step_ending`). In Bing's model
  (1960, p. 226) the corresponding points `x₂ᵢ`, `x₂ᵢ₊₁` are end points of arcs irreducible between
  the two side lines, so they lie on the sides by construction. In Hagopian the block ends are
  values of `d`, and nothing printed places their layers on the sides.
  * **For `i ≥ 3` the presupposition is true: verified, batch 185 (`blockLayersMeetSides3`).** A
    block end is an end of a crossing interval; upper semicontinuity keeps its layer out of
    `π⁻¹[D]`; so the layer meets the frontier, which away from `E` and `I₂` is a side segment. The
    argument does not say which side. It also puts `d⁻¹(x₃)` on a side segment
    (`layer_x3_meets_side`).
  * **Classification (batch-190 audit): proof defective, statement true.** The printed proof of
    Theorem 1 fails at an identified step (the case split at `i = 2`), with a verified
    certificate, and the statement is verified by another route (batch 190). Counted in Part D.
    Precedents: Moore 1916 Theorem 28 (a last step corrected) and Jones 1975's Theorem (a
    statement proved by a different proof). An independent check of Part D raised it; until then
    this entry carried only "unargued".
* **p. 349, T17: "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`": unargued.**
  * It presupposes that every point off the crossing continuum is above or below it.
  * Components that reach the bottom edge or `I₂` are verified (batches 171–172, through
    Schoenflies).
  * Components meeting the frontier only in a side segment (pockets) are not addressed by the
    printed argument. Batch 175 shows that no such component of `F ∩ π⁻¹[D]` reaches the abscissae
    `[3/8, 5/8]`, unless it meets the far end set of `F` (`cover_pocket_middle`). Open as printed;
    not refuted.
* **p. 347, Property 3: unargued steps; true, verified (batch 173)** for every element `d⁻¹(v)`
  with `v < 1` (`hagopian76_property3`, `hagopian76_property3_domain`).
  * "Let `v` be the first point …": the least element is attained for a closed condition
    (`LayerCrossing`). For the printed open condition, attainment is unargued.
  * "By Lemma 1 and Property 1, `L` follows a type A′ continuum in `d⁻¹(v)`": supplied by the
    swallowing lemma. A layer containing a crossing contains a whole translate of `F`.
  * "`d⁻¹(u)` contains a component … whose closure meets …" after the shift: unargued. It is
    supplied by recreating the crossing from the ends of the shifted translate (D1). No margin is
    lost.
  * The end element `d⁻¹(1)`: verified (batch 174) through a proper extension, in which it is an
    interior layer.
* **p. 347, T11: "Note that `K` separates `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]` in `π⁻¹[D]`":
  unargued.**
  * True, verified (batch 165), for the whole section `π⁻¹[D ∩ ⟨p₃, q₃⟩]` (`hagopian76_T11`).
  * For the single component `K` it does not follow from the properties of `D` stated. If `I₂`
    crosses the vertical over `p₃` three times, `D` has a channel above the lowest crossing that
    joins a region left of `p₃` to the right side. A point of `M ∩ L₂` in that channel is then not
    separated from `L₁₀` by `K`. Not refuted, since no such `M` exists by Theorem 1. Not needed: T12
    uses `K` only near `π⁻¹(p₃)`, and the separation is supplied by the whole section.
* **p. 346: "Define `ε₂` to be the minimum of `ε₁` and `ρ(M, π⁻¹[I₁ ∪ I₂])`": positivity unargued,
  true, verified (batch 164)** for any closed set missing `π[M]` (`hagopian76_eps2_pos`).
* **p. 344, Lemma 9: "We assume without loss of generality that `π[E]` is lying on a horizontal line
  `B` … and `π[I − {y}]` is below `B` on a vertical line".**
  * This uses the plane Schoenflies theorem, which is unstated.
  * The first half is supplied (batch 159): `plane_schoenflies`, from Moore 1919 through the plane
    model of Moore's axioms; and `exists_collar`, a two-sided collar of any arc.
  * The second half needs Schoenflies with two sides prescribed (batch 160).
* **p. 344: "decomposably accessible from a side … abut on the same side of the arc `π[E]` in `R²`
  [2, p. 215]".**
  * Recorded in collar form (`DecompAccessibleC`).
  * Bing's form asks for a homeomorphism of the whole plane. The two agree given Schoenflies; the
    equivalence is not formalized.
* **p. 346: Lemma 8 "with the open sets `A` and `B` … in `G₁ − G₂` and `G₁₁ − G₁₀`": true**
  (`hagopian76_lemma8_caps`, batch 159).
* **p. 344: "Since `M` is indecomposable and homogeneous, no proper subcontinuum of `M` separates
  `R²` [5, Lemma 1 (second paragraph of proof)]": the citation does not cover it.**
  * The cited argument carries a *non-unicoherent* continuum to every composant. For a separating
    one, it needs the topological invariance of plane separation (Borsuk), which neither paper
    states.
  * Supplied without Borsuk: a plane continuum homeomorphic to a separating compactum contains a
    separating subcontinuum (`exists_separating_subcontinuum_of_homeomorph`: logarithms on
    tree-like continua, Bing 1951 Theorem 6). The statement is verified
    (`no_proper_subcontinuum_separates`).
* **p. 344: "Hence we can assume that the quotient space `R²/S` is `R²` [12]".** True by Moore 1925
  Theorem 22 (`layerSetoid_mooreDecomp`, `exists_quotient_plane`). `π` is a quotient map, not a
  homeomorphism.
* **p. 345: "we can assume without loss of generality that `k⁻¹[(0, 1)]` is accessible from
  `R² − M`".** Unargued. It is true in the form "some point" (`exists_accessible_typeA'`: a nearest
  point is accessible by a segment).
* **Lemma 4, countable form (p. 342): unargued, true.** "Since `M` is second countable, there exists
  a monotone strictly increasing sequence". Supplied by `exists_strictMono_seq_of_chain`.
* **Lemma 8 (p. 344): unargued steps, true, supplied.** The open sets `A`, `B` with `E` a component
  of `M − (A ∪ B)`; that `{Lᵢ}` is a chain, follows `E`, and is free.
* **Theorem 2 (p. 349): citation replaced.** "[4], [6]" (Gordh 1975, Jones 1951) is replaced by
  `jones55_two_domains'`.
* **p. 340: the end-set property** "[14, Theorem 8, p. 14]" is true for the decomposition and false
  for an arbitrary admissible map.

### A.24 C. L. Hagopian, *Atriodic homogeneous continua*, Pacific J. Math. 113 (1984), 333–347 (Part E, second route to A.23 Theorem 1; batch 184–)

Read from page images at 200 dpi (19 PDF pages; journal page = PDF page + 331), by me and by
Aristotle (`doc/notes/hagopian84.md`: dictionary, route; from batch 204 the transcription is in
`doc/sources/transcriptions/hagopian84.md`, which is not public). The repository's
`LEDGER.md`, section "Hagopian 1984 I", has the fourteen checks with the printed sentences quoted.

**The route** (Corollary 3, p. 346, Jones's plan). Let `M` be an indecomposable homogeneous plane
continuum with a decomposable subcontinuum. `M` is atriodic and hereditarily unicoherent (1975
Lemma 1). Theorem 1 with `N = M` gives a monotone continuous decomposition `𝔇` with `M/𝔇`
homogeneous and containing an arc. `M/𝔇` is planar (Moore 1925) and indecomposable, so the arc step
(Bing 1960) gives a contradiction.

**Status of the formalization.**
* Verified (batch 184):
  * the assembly `hagopian76_theorem1_of_jones`: Theorem 1 of 1976 from the named claims
    `Hagopian84Decomp` (Theorem 1 with `N = M`) and `NoArcIndecHomPlane` (the arc step);
  * the plane quotient `exists_plane_quotient_of_monotone`: Moore 1925 Theorem 22 applied to the
    decomposition of the plane into the fibres and the points off `M`. The fibres do not separate
    the plane by `no_proper_subcontinuum_separates`, which replaces Hagopian's appeal to
    tree-likeness;
  * monotone images of indecomposable continua are indecomposable;
  * Lemma 1 (`W(x, ε)` open, by Effros), Lemma 6 (proved without Thomas's Theorem 8), and Lemma 11
    with `N = M`.
* Verified (batch 185): Lemma 7 (`hagopian84_lemma7`) and the two-sided extension
  (`hagopian84_two_sided`), open since batch 158; rigidity (`layers_agree`) and runs
  (`translate_run`).
* Verified (batch 186): the quotient package (`hagopian84Decomp_of_package`); Lemma 12; Lemmas 14
  and 15; the note on p. 341 (`delta5_partition`); positivity (`delta5_dist_pos`); the interval of
  layers for the arc (`exists_interval_in_delta`); the fold combinatorics of Lemma 13 (5)
  (`exists_fold`, both the printed case and its mirror).
* Verified (batch 187):
  * Lemma 13 as printed (`hagopian84_lemma13`), with the chain part, conditions (3)–(6) of running
    straight, and regularity;
  * Lemma 16′ (`strand_layer_of_extension`) and Lemma 16 with normality added
    (`hagopian84_lemma16`);
  * `X(Z)` (`omega_not_delta_side`), `F(Z)` (`exists_ext_meeting_P2`) and the bridge `J(Z)`
    (`exists_bridge84`), without the positions of its end sets relative to `K(Z)`;
  * `𝒫(Z)` with `Z ∈ Δ(𝒫(Z))` (`exists_chainZ84`), and a finite cover of `M`
    (`hagopian84_cover`).
* Verified (batch 188): the transfer lemma; the decomposition `𝔇` and its disjointness; claims
  (5) and (6); the package (`CoverData84.isJonesDecomp`); **`hagopian84_decomp :
  Hagopian84Decomp`**; and `hagopian76_theorem1_jones (hA : NoArcIndecHomPlane) :
  Hagopian76Thm1`. Also the printed `⋃𝔅 = M` (`sUnion_cover84_eq_univ`).
* Verified (batch 190): the arc step `NoArcIndecHomPlane` (`jones75_noArc`, A.28), the last
  open input of Theorem 1 of 1976 on this route; so `hagopian76_theorem1 : Hagopian76Thm1`.
  Lemmas 8 and 10, claim (4), the solenoid conclusion and the last paragraph are not needed with
  `N = M`. Also not formalized (not needed): the printed (5) at members outside `⋃𝒫(Zᵢ)′`, and the
  lower semicontinuity of `𝔇`. Report 186 records Jones 1975 (for the arc step) in
  `doc/notes/jones75.md`.

**Lemma 7, batch 185 (H84.15 of the repository's ledger).** The printed proof's three atriodicity
steps (below) are avoided, not repaired: with `H ⊇ E` and `I ⊇ F` the two-sided extensions and
`K = H ∩ F`, either `K` lies in one layer of `H` or of `F`, and then the other continuum is a third
arm of a triod at an interior layer (`no_arm_at_interior_layer`), or `K` meets two layers of each,
and Lemma 6 twice gives the conclusion. "By Lemma 4, there is a continuum `H` of type λ in `M` such
that (1) `E` is an essential subcontinuum of `H` that misses both end sets of `H`" is a gap in
exposition: Lemma 4 extends `E` on one side only. The two-sided `H` needs `F₁ ∩ F₂ = E` and a glued
decomposition; neither is stated, and both are now verified.

**Checks** (batch 184; no statement refuted, no proof found to fail):
* **p. 335, "the decomposition" of a type λ continuum, cited to Kuratowski and Thomas.** The same
  citation as Hagopian 1975 Lemma 2 (A.22), with the same gap, filled there. The repository's type
  A′ is the decomposition form; its equivalence with Kuratowski's definition is not needed.
* **Lemma 2 (cited to Mackowiak–Tymchatyn 13.8) applied to unions** `F ∪ J`, `N ∪ F`, …: harmless in
  the plane, where every nondegenerate subcontinuum is unicoherent. For a general atriodic `M` the
  unions must be proper, and in Lemma 7 this is not argued.
* **Lemma 9: the citation covers only part.** 1975 ¶5–12 treats interior layers. Lemma 9 claims
  every element, end sets included; true via an extension, not stated.
* **Lemmas 7, 8, 12, 13: gaps in exposition.** Unargued atriodicity steps, among them:
  * Lemma 7: "there is a point `x` of `F` in `H∖k⁻¹(r)`" and "`k⁻¹(r) ⊂ F`";
  * Lemma 8: "the union of two arcs … atriodic … no simple closed curve", hence an arc;
  * Lemma 12: "`E∖(A ∪ B)` is a component of `M∖(A ∪ B)`";
  * Lemma 13: the hypotheses of Lemma 3 in (3)–(5), never checked. Batch 187 (H84.28): all the
    unargued steps of (3)–(6) are true, and Lemma 13 is verified as printed. The positions of
    `r` and `s` in (3) follow from the `½ρ` bounds without uniform continuity. The regularity
    sentence needs an orientation argument that the text does not give: two consecutive parameter
    sets would otherwise be disjoint and disconnect `[0, 1]`.
* **Lemmas 14–15: positivity of `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)` is unargued.** It needs
  `Cl ⋃Δ(𝒫) ⊂ ⋃𝒫′`, from freeness and normality. The convergence is in the Hausdorff sense.
* **Lemma 16.** "`s ∉ S` and `s ≠ 1`": a gap, true (`S` is open). "Since `𝒫` is free, there exist a
  3-linked subchain `𝔔` … and numbers `t`, `w` …": unargued; batch 186 found no argument.
  * My batch-186 audit (read by an independent check, which found it correct after one wording fix
    and one added identification; not yet formalized). Theorem 1 uses Lemma 16 once: "By Lemmas 7
    and 16, each
    element of the decomposition of `F(Z)` that intersects `⋃𝒫′` is an element of the decomposition
    of the closure of a component of `⋃𝒫′`."
  * With `layers_agree`, that sentence fails only if a layer of `F(Z)` contains the closure of a
    whole component.
  * I exclude that case without Hagopian's subchain `𝔔`, for any type λ `F` whose end layer
    `d⁻¹(0)` misses `⋃𝒫′`. Take the last parameter before the bad one whose layer misses `P₃`.
    Just past it every layer would contain a whole strand. The limit layer would then contain a
    member of `Δ(𝒫)` (Lemma 14) while missing `P₃`, which `layers_agree` forbids.
  * Commission 187 §3 asks for this in place of Lemma 16.
  * Hagopian's own proof needs only an interval of layers that meet three consecutive links and
    whose union misses one link. His (1), "no element of `𝒫∖𝔔` that intersects a link of `𝔔`", asks
    for more than that.
  * **Verified in batch 187** (`strand_layer_of_extension`, H84.23), by this route. Step 3 needs
    only one limit point in `d⁻¹(α) ∩ Cl P₃`, not Lemma 14. Lemma 16 as printed then follows in a
    few lines for normal chains (`hagopian84_lemma16`): a layer meeting three consecutive links
    meets `⋃𝒫′`, so it is a strand layer, and it would lie in two disjoint links. Hagopian's `𝔔`,
    his (1) and his interval are not needed. Lemma 16 without normality is not decided (every
    chain it is applied to is normal). Step (1) stays unargued; gap in exposition.
* **Theorem 1, pp. 342–344.** Several steps are unargued: `X(Z)`; the application of Lemma 11 to
  `Cl K(Z) ⊂ h[E]`, which for general `N` needs `h[N]` or Lemma 10; `J(Z)`; the cover; disjointness.
  "Thus `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`" holds by my reading, which Aristotle confirms: an
  indecomposable continuum has no proper subcontinuum with interior.
  * Batch 187: `X(Z)` (H84.25) and "Thus `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`" (H84.26) are
    unargued and true, and verified.
  * `J(Z)` (H84.27) is verified without the positions of its end sets: "one end set in
    `K(Z) ∩ (⋃Δ(𝒫))` and the other end set in `(⋃Δ(𝒫))∖K(Z)`". With the construction used, the
    second end layer may still be a layer of `Cl K(Z)`. Nothing later on this route uses the
    positions.
  * **The cover (H84.29).** "Since `𝒫` is free and since `𝒫(Z)` is free and (3) holds for each
    element `Z` of `Ω(𝒫)∖Δ(𝒫)`, it follows that `⋃𝔅` is a closed open subset of `M`." Freeness and
    (3) control the boundary of each `⋃𝒫(Z)` separately. Over uncountably many `Z` they do not by
    themselves place a limit of points of distinct `⋃Δ(𝒫(Zₙ))` in `⋃𝔅`. Batch 187 proves the
    finite subcover directly (`hagopian84_cover`). Then `⋃𝔅 = M` for the same choice of chains, so
    the printed statement is true; only the reason given is not an argument (my reading in my
    batch-187 audit). The corollary is verified in batch 188 (`sUnion_cover84_eq_univ`). Gap in
    exposition.
  * **Disjointness, first case (H84.30; my reading, commission 188 §3.4, read by an independent
    check, which narrowed it; verified in batch 188).** "If `A ∪ B` intersects `⋃Δ(𝒫)`, then, by
    (2), (3), and Lemma 7, `A = B`." Gap in exposition.
    * Lemma 7 needs `E∖F ≠ ∅ ≠ F∖E`. Take a strand `S_A` of `𝒫(Zᵢ)`, the member `Y ∈ Δ(𝒫)` through
      the common point, and the strand `S_Y` of `Y`.
    * (2) gives `S_Y ⊄ S_A`, since every strand of `𝒫` meets `P₃`. `S_A ⊄ S_Y` is not argued.
    * If `S_A ⊆ S_Y` without lying in one layer, rigidity (`layers_agree`) gives `A = Y` anyway.
      The case the text leaves open is `S_A ⊆ Y`, and (3) does not exclude it.
    * Hagopian's "first note" on p. 344 would exclude it ("each component of `⋃Δ𝒫(Zᵢ)` misses `P₃`
      and intersects `M∖⋃𝒫′`"), but that note is itself unargued (H84.35). It seems to need the
      end links of `𝒫(Zᵢ)` in different components of `⋃𝒫′`. Lemma 13 and (3) do not give that,
      and since the components of `⋃𝒫′` are not open, neither do the printed end-set positions of
      `J(Z)` (Aristotle, batch 188).
    * My route: Lemma 16′ for `𝒫(Zᵢ)`, applied to the piece of `S_Y` between `Y` and a layer inside
      `P₃` (commission 188 §2). It uses (2), not (3). Verified (`omega_mem_delta_of_mem_mid`,
      `CoverData84.eq_of_meet_delta`, `CoverData84.members_disjoint`).
  * **Disjointness, last case (H84.31).** Correct as printed, with the end sets read off the maps
    that run straight (`delta_regular_rep`). Verified.
  * **Claims (5)–(6) (H84.32, H84.33; commission 188 §4, read by an independent check).**
    * (5) holds as printed. For `i ≥ 1`, at a layer `W` of a strand `S` of `𝒫(Zᵢ)`: if `S ⊄ Y`,
      Hagopian's "(3) and Lemma 7" (or `layers_agree`) works. The case `S ⊆ Y` again needs an
      argument, and the transfer lemma supplies it. Verified for `i = 0` in full and for `i ≥ 1`
      at members inside `⋃𝒫(Zᵢ)′`, which is all (6) uses. The argument at members outside
      `⋃𝒫(Zᵢ)′` (found by the check, where I had none) is recorded in report 188 §4.2 and not
      formalized. Gap in exposition.
    * (6): Lemma 15 as printed gives no bound that keeps `h[Z]` inside `⋃𝒫′`. Its proof takes
      `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`, which does. My first reading, that Hagopian's `δ` lacks this bound,
      was wrong; the check found the error before the commission went out. Verified with the bound
      made explicit (`CoverData84.invariant`).
  * **"It follows from Lemma 14 that `𝔇` is continuous" (H84.34).** The u.s.c. half is verified
    (the `usc` field). The l.s.c. half follows from the other inclusion of Lemma 14 (Aristotle,
    not formalized, not needed).
* **p. 344: "`M/𝔇` … contains an arc" is used and not argued.** The interval of layers it needs is
  verified (batch 186, `exists_interval_in_delta`); the arc in the quotient then comes from the
  package (`hagopian84Decomp_of_package`). Verified end to end in batch 188 (the `arc` field of
  `CoverData84.isJonesDecomp`).
* **p. 343, `K(Z)`: "For each element `Z` of `Ω(𝒫)∖Δ(𝒫)`, let `K(Z)` be the component of `⋃𝒫′` that
  contains `Z`" (my batch-186 audit; confirmed in batch 187, H84.24).** An end layer of `Cl K` lies
  in `Ω(𝒫)∖Δ(𝒫)` and outside `⋃𝒫′`, so no component contains it. Read "the component whose closure
  has `Z` as a layer". Slip, harmless.
* **p. 346: "since the elements of `𝔇` are tree-like, if `M` is planar, then `M/𝔇` is planar
  [21]".** Moore 1925 needs elements that do not separate the plane, and that tree-like continua do
  not is not stated. Gap filled in the plane by `no_proper_subcontinuum_separates`.
* **Corollary 3** goes through Theorem 2, which assumes that `M` is not a solenoid. Theorem 1 with
  `N = M` needs no such assumption.
* **Slips, harmless.** "opens sets" (p. 333), "ε-circluar" (p. 334), "ε-homomorphisms" (p. 338),
  unbalanced brackets in Lemma 13 (5). "In 1968 F. B. Jones [16]" (p. 346), where the reference list
  and the 1976 abstract give 1969.
* **Lemma 13 (5) is printed without `h` (p. 340; my batch-185 audit, from the page image).** "(5) if
  `0 ≤ r < t ≤ 1` and `k⁻¹(r) ∪ k⁻¹(t) ⊂ Lᵢ`, then `k⁻¹[[r, t]] ⊂ Lᵢ`." The proof and the use in
  (6) ("`h[E]` runs straight through `𝔏`") are about the translate. The reduction in its proof
  ("By (1), (2), and (3), there exist numbers `r`, `s`, and `t` …") is unargued and omits the mirror
  case; commission 186 §3.1 proposes a combinatorial lemma for it.
* **Lemma 15 (p. 341), "By Lemma 3": gap in exposition (my reading in commission 186 §4.3;
  confirmed, batch 186, H84.20).** The layer of `Cl K′` through a point of `h[Z]` need not lie in
  `Δ(𝒫)`, and then a hypothesis of Lemma 3 is not available. Verified with a smaller `ε`, rigidity
  (`layers_agree`) and normality. Lemma 14's "By Lemma 3" is fine as printed (both layers lie in
  `Δ(𝒫)`).
* **Lemma 12 (batch 186, H84.19).** Verified. Its first unargued step ("Since `𝔏` is regular,
  `E∖(A ∪ B)` is an essential subcontinuum of `E`") is not needed: Moore's Theorem 44 applies by
  atriodicity directly.

**The arc step.** Aristotle's reconnaissance of Bing 1960 (notes §F): only Properties 4 and 5 (in
the indecomposable case) and the Effros-type input are in the repository. Sections 3–7 and 9–10 of
Bing's paper are a separate project. Jones 1975 (Houston J. Math. 1, 57–61) is now in
`doc/sources/jones1975.pdf`, with Aristotle's transcription and reconnaissance in
`doc/notes/jones75.md` (batch 186). It is the planned source for the arc step. Commission 186 gave
the pages as 57–62 (my slip; the sixth PDF page is blank).

### A.25 R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959), 171–192 (Part G; my first reading, 2026-10-17)

Read from page images at 200 dpi (23 PDF pages: a JSTOR cover, then journal pp. 171–192 on PDF
pages 2–23). Nothing is formalized yet. These are candidate entries, not checked by Aristotle.

* **The definition (p. 173).** "It is a circle-like continuum `M` such that there is a continuous
  decomposition of `M` into pseudo-arcs such that the decomposition space is a simple closed curve."
  Circle-likeness is part of the definition.
* **Uniqueness, pp. 173 and 189: "It follows from Theorem 10 that any two circles of pseudo-arcs are
  topologically equivalent and that each is homogeneous."** Unargued as stated.
  * Theorem 10 (pp. 181–189) is about continuous *snake-like* arcs of pseudo-arcs: a homeomorphism
    between the end elements extends, with `h(pₓ) = qₓ`.
  * The passage to circles is not written. Presumably one cuts the circle into two arcs, shows
    that their preimages are snake-like (from circle-likeness), and glues.
* **Planarity (§7, pp. 189–191) is a sketch:** "one may see with the help of [3] that each element
  of `G` is a pseudo-arc."
* **The gap for the classification (my reading).** Jones 1955 Theorem 2 (verified,
  `jones55_theorem2'`) gives a continuous decomposition over a circle into homogeneous
  indecomposable elements. With Theorems B and C and Hoehn–Oversteegen, each element is a
  pseudo-arc. Bing–Jones's uniqueness then needs `M` circle-like, or at least the preimages of arcs
  snake-like.
  * Nothing in the chain provides this.
  * A continuous arc of pseudo-arcs need not be snake-like: pseudo-arc × `[0, 1]` is one.
  * **Corrected 2026-10-17.** I first wrote here that planarity "must be what is used". Planarity
    is not enough, and neither is dimension 1: Prajs 2000 gives a plane curve with a continuous
    decomposition into pseudo-arcs over a simple closed curve that is triodic and whose elements
    are not terminal (A.27). What must be used is homogeneity, through the terminality of Jones's
    elements (A.27).
  * Hoehn–Oversteegen pass from Jones's Theorem A to "the circle of pseudo-arcs" without stating
    this step (A.26). The surveys take it for granted as well (A.27).
  * Lewis, *Homogeneous circle-like continua* (Proc. AMS 89 (1983)), Burgess (Bull. AMS 75
    (1969)) and Hagopian–Rogers (Houston J. Math. 3 (1977)) all assume circle-likeness, so they
    cannot close the step. A route that does not need circle-likeness is in A.27.

**Second reading: the whole paper, for Part G (2026-10-20).** David re-sent the paper (the same
file as the collection's copy, same checksum). Read from page images at 200 dpi; every item
marked (400) was checked on a 400-dpi crop. Not yet checked by Aristotle.

* **Structure.** §2 definitions (chains with nonadjacent links at positive distance; snake-like;
  an arc of continua is the fibres of a map onto `[0, 1]`, continuous when the map is open;
  circle-like is "A compact nonsnake-like continuum which for each positive number ε can be
  covered by an ε-circular chain"; chain maps). §3 Theorems 1–5 (snake-like arcs of continua).
  §4 Theorems 6–8 and a corollary (chain maps; Theorem 7 uses Bing 1948 Theorem 6). §5 Theorem 9
  (a chain map approximated by a homeomorphism of pseudo-arcs, "essentially like the proof of
  Theorem 12 of [3]"). §6 Theorem 10. §7 the plane example (a sketch).
* **Theorem 10 (pp. 181–182)**: "Suppose P, Q are continuous snake-like arcs of pseudo-arcs {p_x},
  {q_x} (0≦x≦1). Then each homeomorphism h that takes the sum of the ends of P onto the sum of the
  ends of Q may be extended to a homeomorphism taking P onto Q. In fact, if h(p₀)=q₀, the extended
  homeomorphism h may be chosen so that h(p_x)=q_x."
* **The step to circles: unargued (pp. 173, 189).** "It follows from Theorem 10 that any two
  circles of pseudo-arcs are topologically equivalent and that each is homogeneous." Repair (my
  reading): cut the circle at two points. The preimages of the two arcs are proper subcontinua of
  a circle-like continuum, hence snake-like (`isSnakeLike_of_subset_circleLike`, Nadler 12.51,
  verified in batch 132), and continuous arcs of pseudo-arcs (restrictions of an open monotone
  map). Apply Theorem 10 to each, with the same homeomorphisms of the two cut fibres, and glue.
  For homogeneity, rotate the base and take, over one cut point, a homeomorphism between pseudo-arcs
  carrying `x` to `y` (`theorem1_HIC`, `homogeneous_of_isPseudoArc`). The statement is true given
  Theorem 10. Not counted. Circle-likeness is used, which is why the step of A.25 above stays open.
* **Misprints**, each as "printed X, read Y". (Rewritten 2026-10-21: this list had used both
  orders of "X for Y"; commission 200.)
  * p. 173 (400): "any two continuous snake-like arcs of pseudo-arcs of homeomorphic": printed
    `of`, read `are`.
  * p. 175, Theorem 3 (400): "B to denote the sum of the elements of F(v, m)": printed `F(v, m)`,
    read `F(w, m)` (my reading). As printed, `B·e_r` can meet `f_{v+1}`, so `D` need not be a
    chain; with `F(w, m)` it is symmetric with `A` (`F(1, v)`).
  * p. 177, Theorem 7 (400): "Let p₁, p₂ be points of different components of P": printed
    `components`, read `composants` (`P` is connected; Bing 1948's descriptions run between points
    of different composants).
  * p. 178, Theorem 8 (400): "Let U_A, U_B be open sets with closures in d₁, d₂ respectively":
    printed `d₂`, read `d_n` (the proof needs `Ū_B·p_a ⊂ e(a)_m` with `H(y_m) = d_n`).
  * p. 180, Theorem 9 (400): "and the links of G with closures in e_{n−1}·e_n are combined to form
    e′_{4n−6}, e′_{4n−5}, e′_{4n−4}": printed `G` (the chain covering `P`, introduced in the next
    paragraph), read `F` (the chain covering `Q`).
  * p. 181 (400): "Let E₂ be any G_i of mesh less than 1/3 that refines E_i and H₂ be any chain map
    of E₂ onto E₁ such that e²_j⊂H₁(e²_j)": printed `E_i`, read `E₁`; printed `H₂`, read `H₁` (by
    (3), `H_i` maps the `(i+1)`-st chains onto the `i`-th).
  * p. 185 (400): printed "R_{(2i+1)/n}(f_y)", read `R_{(2i+1)/2n}(f_y)`; printed
    "P(0, 1/n−ε)⊂A′_i", read `P(0, i/n−ε)`.
  * p. 186 (400): "link of the subchain of E_k that irreducibly covers Q(i/n, (i+1)/n)": printed
    `E_k`, read `E₁`.
  * p. 189 (my reading): "so ρ(p, q)<4/2^i": the meshes give `8/2^i` (two intersecting sets, each
    at most two adjacent links of `D_{i−1}`, of mesh `< 1/2^{i−1}`). Harmless.
  * Found by the independent check of commission 198 (400-dpi crops; I confirmed the first three):
    p. 180, "d₂′ is the sum of the other links of G in e₁−e₂; d₄′, d₅′, d₆′ are formed by combining
    links of G in e₂−(e₁+e₃), ⋯, d′_{4n−4} is the sum of the other links of G in e_n−e_{n−1}":
    printed `e`, read `d`, throughout; p. 181, "d²_j⊂d¹_k=H₁(d²_j) if H₁(e²_j)=d¹_k": printed
    `d¹_k` (the last), read `e¹_k`; p. 182, "E₁, D₁, H₁, E₂, K₁, D₂, H₂, E₃, K₃, ⋯": printed `K₃`,
    read `K₂`; p. 187, "intesects".
* **Theorem 5 (pp. 175–176): false as printed.** "Then if U is an open set such that U·G≠0,
  U·(g₀+g₁)=0, and Ū lies in a link of E, then G−U may be expressed as the sum of two mutually
  separated sets A, B such that g₀⊂A, g₁⊂B, and for each x (0≦x≦1), either A·g_x intersects each
  link of E or B·g_x intersects each link of E." I first found only a degenerate failure (a fibre
  inside `U`, possible for chains of at most three links; with the library's definitions `[0, 1]`
  and `f = id` with one link is an example). The independent check of commission 198 found the
  general one: in any instance with `n ≥ 3` links, merge the last two links (`e_{n−1} ∪ e_n`, then
  `e_n`), so that `cl(e_n) ⊆ e_{n−1}`, and take `U` a small neighbourhood of `cl(g_c ∩ e_n)` inside
  `e_{n−1}`. Then `g_c − U` misses `e_n`, and the conclusion fails at `c` for every separation,
  though no fibre lies in `U`. I checked the construction (the merged collection is a chain in
  Bing–Jones's sense, covers `G` and properly covers every fibre). The printed proof passes from
  separations of `G − d_j` to separations of `G − U`. The application on p. 185 is existential ("By
  Theorem 5 there is an open set U_i …"), so Theorem 10 is not affected. Repair commissioned: `f`
  open, and no fibre meets a link only inside `Ū`. **Counted (batch 198):** a false printed
  statement, the twenty-third. The verified certificate is the degenerate one
  (`bj_theorem5_printed_false`); the non-degenerate construction is checked by hand, twice, and is
  not yet formalized (commissioned again, optional, in 199).
* **Theorem 3 (p. 175), the chain `D`.** Even with `F(w, m)` read for the printed `F(v, m)`, `D`
  is not a chain as written: `A·e_{j−1}` can meet `f_{v+1}` (through `f_v ∩ f_{v+1} ∩ e_{j−1}`),
  and they are not adjacent in `D`; likewise `B·e_{r+1}` and `f_{w−1}` (found by the independent
  check). The statement is true; the construction needs repair at both junctions.
* **Unargued steps.**
  * p. 174, Theorem 2: that `G(b, c)` meets the link `d_t` between `D′` and `D″` is not said; it
    holds if `D′`, `D″` are all the links meeting `G(0, b)`, `G(c, 1)` (connectedness of `G`).
  * p. 175, Theorem 3: "Then the elements of D are …": that `D` is an `ε`-chain from `g₀` to `g₁`
    is left to the reader.
  * p. 178, Theorem 8: "It follows from Theorem 4 that P is covered by open sets U₁, U₂, ⋯, U_t
    such that U_i·U_j=U_A+U_B if i≠j and if p_x·(U_i−(U_A+U_B))≠0, then x∈I_{a_i}": Theorem 4
    gives one separation at a time; the cover is not derived. "Then the chain E whose kth link
    e_k=e(a₁)_k·U₁+e(a₂)_k·U₂+ ⋯ +e(a_t)_k·U_t is the required chain": not verified. My reading:
    for `i ≠ j` the sets `e(a_i)_k·U_i` and `e(a_j)_l·U_j` can meet inside `U_A + U_B` for
    nonadjacent `k`, `l` (when `H` sends both `y_k` and `y_l` into `d₁`), so the links need
    shrinking. Settled in the fourth reading (below).
  * p. 180, Theorem 9: the last display ends "⊂ē_i", where the claim is "h(P·d_i)⊂e_i" (found by
    the independent check; confirmed).
  * p. 181, Theorem 9: "That h is a homeomorphism of P onto Q follows from an argument similar to
    that contained at the end of the proof of Theorem 10 of this paper or in Theorem 11 of [3]."
  * pp. 187–188, Theorem 10: Step 3, Conditions I and II "similar to" Step 2; "Steps 4, 5, ⋯.
    These steps are essentially repetitions of Step 3." The induction is carried by Conditions A,
    A′, B, B′, C, C′ (p. 188), which is enough to define `h` and check it (pp. 188–189).
* **§7, the plane example (pp. 189–191): a sketch.** "Now there exists a sequence D₁, D₂, D₃, ⋯
  of circular chains of simple domains in the plane such that" (1)–(9): asserted, not
  constructed. "With the addition of (9) one may see with the help of [3] that each element of G
  is a pseudo-arc. It follows from Theorem 10 that M is homogeneous." Covering by fine circular
  chains follows from (1)–(3). Not argued: that `M` is not snake-like, that the elements of `G`
  form a continuous decomposition of `M` over a circle, and that each element is a pseudo-arc.
* **Definitions.** Bing–Jones's chains have nonadjacent links at positive distance, and the
  proof of Theorem 10 uses "chains whose nonadjacent links do not have closures that intersect"
  (p. 189). The repository's `Chain` only makes nonadjacent links disjoint, and its
  `IsCircleLike` omits "nonsnake-like". Neither difference matters for compact continua, but
  each must be bridged.
* **What Part G takes from the paper.** Theorem 10 and the gluing give the converse for the
  third continuum (homogeneity) and the uniqueness of circles of pseudo-arcs; §7 gives a plane
  example. The forward step (a decomposable homogeneous plane continuum is circle-like, or its arc
  preimages are snake-like) is not in the paper. Lewis 1985 does not supply it; the route is
  Domokos–Prajs 2022 Theorem 6.1 with Fugate 1969 in place of shape theory (A.27). Theorem 5 is
  counted (above); the rest are misprints and gaps.
* **Batch 198 outcome.** Verified: Theorems 2, 3, 4 and 6; Theorem 5 repaired, with a degenerate
  certificate against the printed form; the passage to circles (uniqueness and homogeneity) and
  the classification, from the named `Prop`s `BJThm10`, `HOCircleLike` and `BJPlaneExample`
  (batch paragraph above). Aristotle's ledger BJ.1–BJ.16 agrees with the second reading item by
  item and adds two observations: Theorem 2 needs neither snake-likeness nor `0 < a`, `d < 1`;
  Theorem 3 produces a chain only in the library's sense (nonadjacent links disjoint, not at
  positive distance), so a bridge is needed before Theorem 10 can use it. Its repair of
  Theorem 3 merges `f_{v+1}` into the last `A`-link and `f_{w−1}` into the first `B`-link.
  **Counted:** Theorem 5 (false printed statements: twenty-three). **Not counted:** Theorem 3's
  chain (a defective construction with a one-line repair; Aristotle compares it with its HO.15
  and HO.23, local steps that fail as written and are repaired in place). Defective proofs stay
  at seventeen.

**Third reading: §§4–5, Theorems 7 and 9 (2026-10-20, for commission 199).** Page images at
200 dpi, statements and formulas at 400 dpi; checked again by the independent check of commission
199. Not yet checked by Aristotle.
* **p. 172 (400).** "Also, D *irreducibly covers* X of each link of D contains a point of X that is
  not covered by any other link of D": printed `of`, read `if`.
* **Theorem 7, second sentence (p. 177, 400): false as printed for chains of one or two links.**
  "*In fact, if A, B are closed sets in P·d₁, P·d_n respectively and H(x_r) = d₁, H(x_s) = d_n, the
  chain E may be selected so that A ⊂ e_r, B ⊂ e_s.*" With `n = 1`, `m = 3`, `H` constant,
  `A = B = {p}`, `r = 1`, `s = 3`: `p ∈ e₁ ∩ e₃`, and `e₁`, `e₃` are not adjacent. With `n = 2`
  the same, `p ∈ P·d₁·d₂`, `H = (d₁, d₁, d₂)`. For `n ≥ 3` it holds when "closed" means closed in
  the space (Bing–Jones's own use, p. 178, is of this kind). If it means closed in the subspace
  `P·d₁`, it fails for every `n`: `H = (d₁, d₂, d₁, d₂, d₃)`, `r = 1`, `A = P·d₁`. **Counted
  (batch 199):** a false printed statement, the twenty-fourth (degenerate case, under the reading
  the skeleton adopts; certificate `bj_theorem7_ends_printed_false`, `n = 1`).
* **Theorem 7, proof (p. 177).** Unargued: in the special case, `A ⊂ e₁` (immediate: `A` meets no
  link of `D` but `d₁`); the existence of the crooked sequence `D₁ = D, D₂, ⋯` (true for a
  pseudo-arc, by Bing 1951's crookedness eventually); the non-emptiness of `P·(d₁ − d₂)`.
  The reduction `D′ = U₀, U₁, U₂, d₃, ⋯, d_{n−2}, U_{n−1}, U_n, U_{n+1}` works for `n ≥ 4`; for
  `n = 3` its conditions cannot all hold (a link serving as `U₂` and `U_{n−1}` contains `P·d₂` and
  meets `U₄`), and `n ≤ 2` is not treated. The first sentence is true for every `n` (other
  constructions, commission 199 §6). Not counted until the formal proof shows what the printed
  one lacks.
* **Theorem 9, remark (p. 179, 400).** "The rather awkward condition … is necessary because it may
  be that D = d₁, d₂, ⋯, d_n and E = e₁, e₂, ⋯, e_n have the same number of links, H(d_i) = e_i,
  P ⊂ d̄₂ + d̄₃ + ⋯ + d̄_{n−1}, and Q ⊄ ē₂ + ē₃ + ⋯ + ē_{n−1}." True read existentially; the
  configuration as written does not force failure (an `h` exists when `d₂` is enlarged by an open
  set disjoint from `P`, which puts `P` in `d̄₂`). An instance with no `h`: `n = 3`,
  `d₁ = B(a, ρ)`, `d₃ = B(b, ρ)`, `d₂ = U − {a, b}`. Not a defect.
* **Batch 199 outcome.** Verified: Theorem 7, first sentence for every `n` (by following the
  pattern along a walk and folding, with no special case and no reduction), second sentence for
  `n ≥ 3` (a collar chain of `n + 4` links replaces `D′`); the certificate for `n = 1`; the general
  certificate against Theorem 5 (BJ.5) from every instance with `n ≥ 3` links. Aristotle's ledger
  BJ.17–BJ.20 agrees with the third reading and lists nine points (a)–(i) for Theorem 7's proof
  (BJ.19), among them "We suppose with no loss of generality that r<s", unargued. **Counted:**
  BJ.18 (above). **Not yet counted:** BJ.19, proposed by Aristotle as a defective proof (the
  printed `D′` cannot exist for `n = 3`; `n ≤ 2` not treated). The `n = 3` failure is argued by
  hand only; a certificate is commissioned (200). Theorem 9 is open (not attempted).

**Fourth reading: §§4–6, Theorems 8 and 9 and the end of Theorem 10 (2026-10-21, for commission
200).** Page images at 200 dpi, statements and formulas at 400 dpi; checked again by the
independent check of commission 200. Not yet checked by Aristotle. Links are numbered from
1, as printed.
* **Theorem 8, first step (p. 178, 400).** "Let U_A, U_B be open sets with closures in d₁, d₂
  respectively such that U_A, U_B intersect each element of {p_x}" (printed `d₂`, read `d_n`):
  asserted without argument. For a continuous collection such sets exist (`x ↦ sup` of the
  distance to `d₁ᶜ` over `p_x ∩ d₁` is positive and lower semicontinuous); for an upper
  semicontinuous one, as printed, I do not know.
* **Theorem 8, the cover (p. 178).** "It follows from Theorem 4": unargued (Theorem 4 gives one
  separation at a time). My repair: a minimal subcover by the intervals `I_{a_i}`, cuts in the
  overlaps, and Theorem 4 applied at each cut.
* **Theorem 8, the chain `E` (p. 178).** The printed `e_k` need not form a chain (argued, not
  certified): `e(a_i)_k` is controlled only over `I_{a_i}`, and over a fibre outside `I_{a_i}` it
  can meet `e(a_j)₁` inside `U_A`, for `k ≥ 3` with `H(y_k) ∈ {d₁, d₂}`. Repaired by restricting
  each piece to the fibres over `I_{a_i}`. A defective construction with a one-line repair; not
  counted (as Theorem 3's chain).
* **Theorem 8, the general case (p. 178).** "alter Y as was done in the proof of Theorem 7":
  unargued. My repair: unfolding along a walk and folding (Aristotle's route for Theorem 7).
* **Corollary to Theorem 8, proof (p. 178, 400).** "H be a chain map that takes links of Y numbered
  4i+1, 4i+2, 4i+3, 4i+4 into the image under H₁ of the ith link of D(r, s)": printed
  `4i+1, …, 4i+4`, read `4i−3, …, 4i` (links 1–4 of `Y` get no image as printed). The three
  consecutive links of the conclusion are not argued; my repair is a crossing argument. The
  proof's "properly covering", against "irreducibly covering" in the statement, is not a defect.
* **Theorem 9, the second simplification (pp. 179–180, 400).** "Suppose that ε is a positive number
  so small that each subset of Q of diameter less than 5ε lies in one link of E. Let F be an
  ε-chain properly covering Q. Then e′₁ is the sum of all links of F whose closures intersect
  e₁−e₂, …". The condition concerns subsets of `Q`, and the links of `F` are not subsets of `Q`.
  It secures neither that links of `F` in different middles are disjoint (`e_i − e_{i+1}` and
  `e_{i+1} − e_i` can come arbitrarily close) nor that every link of `F` falls under one of the
  rules. Repair: links of `F` with closures in links of `E`, and a smaller mesh (`Q` misses
  `cl(e_i − e_{i+1}) ∩ cl(e_{i+1} − e_i)`; compactness). A defective construction repaired in
  place; not counted. Found by the independent check.
* **Theorem 9, private points (p. 179, 400).** Bing–Jones ask for private points in the end links
  of `D″` only. That suffices: in a chain whose nonadjacent links are at positive distance and
  which properly covers a connected set, every interior link has one. For `E` they delete points
  ("If there are not already such points, points may be deleted from e₂ and e_{n−1} to make the
  condition satisfied"). Not defects.
* **Step 1(b) of Theorem 10 (p. 182, 400).** Unargued. My proof uses compactness and the lower
  semicontinuity of an open map. Its "irreducibly covers" (p. 172) agrees, for a connected set
  such as `Q(a, b)`, with "neither end link can be dropped".
* **pp. 188–189.** "Of course, d(p, i+1)⊂d(p, i)" (from Condition B). Slip (400): "H_iK_i(e_j^{i+1})
  = H_i(d_k^{i+1})": `H_i` applied to a link of `D_{i+1}`; meant `H_i(K_iH_{i+1}(d_k^{i+1}))`.
  "ρ(p, q)<4/2^i": above (misprints).
* **Commission 200** asks for the repairs, with the definition of `h` (pp. 188–189) as a lemma
  about any two sequences of chains with Conditions B and B′, which also gives Theorem 9's
  homeomorphism, and the certificate for Theorem 7's proof with `n = 3` (BJ.19).
* **Batch 200 outcome.** Verified: the homeomorphism of pp. 188–189 as a lemma
  (`zigzag_homeomorph`, `zigzag_fibre`); private points (`exists_privatePoint_interior`,
  `exists_privatePoint_shrink`); Step 1(b) (`bj_step1b`); Theorem 8 for continuous arcs and chains
  of three or more links, and its corollary for the arc as the whole space; Theorem 9 as printed,
  for chains in Bing–Jones's sense; the certificate `bj_theorem7_proof_n3`. Aristotle's ledger
  BJ.21–BJ.29 agrees with this reading item by item, and adds: the separation for `E′` follows
  from a Lebesgue number `λ` of `E` on `Q` (mesh `λ/5`: two links of `F` joined through at most
  two others lie in one link of `E`, which cannot be both `e_i` and `e_{i+1}`), with no convergent
  subsequences; and the route needs no composants (BJ.28 (e)). **Counted (batch 200):** BJ.19,
  Theorem 7's proof, the eighteenth defective proof. Not counted: Theorem 8's chain `E` and
  Theorem 9's `E′` (defective constructions repaired in place, as Theorem 3's chain). Aristotle
  checked the quotations of pp. 178–181 and 189 at 200 dpi only, and did not re-render pp. 182 and
  188; mine were checked at 400 dpi.

**Fifth reading: §6, the proof of Theorem 10 (2026-10-21, for commission 201).** Pages 176 and
181–188 at 400 dpi; checked again by the independent check of commission 201. Not yet
checked by Aristotle.
* **Structure.** Steps 2, 3, 4, ⋯ (pp. 183–188) are one construction made alternately on the two
  sides; Conditions A, A′, B, B′, C, C′ (p. 188) are what the induction carries. Bing–Jones extend
  `h` at each step to the cut fibres (Step 1(c), "We merely impose the condition that h takes
  p_{i/n} homeomorphically onto q_{i/n}"; Step 2(i), by Theorem 9) and build the maps near those
  fibres from `h`. With overlapping sub-arcs the construction passes directly from one sub-arc's
  map to the next and uses `h` only on `p₀`, `p₁`. On that route Theorem 9 is not used in
  Theorem 10. Not a defect.
* **Step 3 (3), p. 187 (400).** "The image under h⁻¹ of any subset of q₀+q_{1/k}+ ⋯ +q₁ of
  diameter less than 5ε lies in an element of E₁": printed `E₁`, read `D₁` (`h⁻¹` maps into `P`).
* **Step 2(b), p. 184 (400).** That a chain map `R_{i/n}` with `h(f_j·p_{i/n})⊂R_{i/n}(f_j)` and
  the three-consecutive property exists is argued only through the "precaution" (five
  consecutive links sent to `e_k` when `e_k` is the only link containing `h(f_j·p_{i/n})`).
  Unargued step; my proof: least admissible index, overridden by decided positions.
* **Step 2(c), pp. 184–185 (400).** "it follows from Theorem 6 that there are an f_y and an f_z
  … such that R_{(2i+1)/n}(f_y), R_{i/n}(f_y) are adjacent …". Theorem 6 (p. 176) concerns "two
  chain maps of D into E such that H_i (i=1, 2) takes a link of D into e_{m−1}"; Bing–Jones do
  not say which chain plays `E`. With `E₁` the hypothesis fails. With the subchain spanned by the
  two images (different subchains properly covering `q_{i/n}`) it holds, since such runs have ends
  at most one apart; when an image has one link the adjacency is immediate. Unargued step.
  (Corrected before commission 201 went out: I first wrote that Theorem 6 does not apply as
  printed.)
* **Step 2(c), p. 185 (400).** "By Theorem 5 there is an open set U_i in P(i/n, i/n+ε)·f_y such
  that Ū_i⊂f_y and P−U_i is the sum of two mutually exclusive closed sets A_i, B_i …". The
  printed Theorem 5 is false (above); the repaired form needs `U_i` to contain no set
  `f_k·p_x`, which Bing–Jones do not arrange. A small enough `U_i` exists (a uniform lower bound
  on the diameters of `f_k·p_x`, by boundary bumping). Unargued step, consequent on Theorem 5.
* **Step 2(i), p. 187.** "Theorem 9 assures us that h can be extended in this fashion": Theorem
  9's hypothesis (each link the image of a link with a private point) is not checked for `D₁`,
  `H₁` on `p_{i/k}`. Unargued; not needed on the route above.
* **Step 3, p. 188 (400).** "we pick ε so small that the Q_i, V_i, U_i we obtain will have the
  property that if f_j is an element of the subchain of F irreducibly covering q_{i/k}, then
  (V_i+Q_i+U_i)·f_j⊂H₁R_{i/k}(f_j)": unargued, and it needs the closures of the `f_j` on
  `q_{i/k}`, not only `q_{i/k}·f_j⊂H₁R_{i/k}(f_j)`.
* **Steps 4, 5, ⋯, p. 188.** "These steps are essentially repetitions of Step 3": the induction
  is left to the reader.
* **Step 3, p. 187 (400).** "It takes the subchain f_t, f_{i+1}, ⋯, f_u of F that irreducibly
  covers Q(i/k, (i+1)/k)": printed `f_{i+1}`, read `f_{t+1}` (found by the independent check).
  Condition "(1) f_j⊂H₁R_{(2i+1)/2k}(f_j)" asks for the whole link, while the corollary to
  Theorem 8, read with `Q(i/k, (i+1)/k)` as the space, controls only `f_j·Q(i/k, (i+1)/k)`; the
  construction needs only that part. Unargued as stated.
* **"the subchain … that irreducibly covers"** (throughout): a minimal covering run of a set is
  unique when it has two links or more; two different ones occur only when the set lies in two
  adjacent links, each covering it alone. Any one serves. Harmless.
* **Commission 201** asks for the step as one lemma (`BJStep`), Theorem 10 from it
  (`bjThm10_of_step`), and the tools: Theorem 6 in the needed form, the pattern of a map of a
  fibre (Step 2(b)), the corollary to Theorem 8 on sub-arcs, Theorem 5 on windows.
* **Batch 201 outcome.** Verified: Theorem 10 (`bjThm10`), through the step lemma (`bj_step`)
  and the induction from one-link chains; the tools of the fifth reading. Aristotle's ledger
  BJ.30–BJ.40 agrees with the fifth reading item by item and found no further defect in Steps
  2(d)–(h). **Not counted:** the use of the printed Theorem 5 in Step 2(c) (BJ.33) is existential
  ("there is an open set U_i"), and a small enough `U_i` exists, so the step's claim is true; the
  defect is Theorem 5's, already counted. The other items are unargued steps, slips or
  overstatements. Counts unchanged: 24 and 18.

**Sixth reading: §7, the plane example (2026-10-21, for commission 202).** Pages 189–191 at
400 dpi. §7 states its aim, "In this section we show that the plane contains a circle of
pseudo-arcs" (p. 189), and gives a sketch.
* **P. 190, not established**: "Now there exists a sequence D₁, D₂, D₃, ⋯ of circular chains of
  simple domains in the plane such that" (1)–(9). The chains are not constructed.
* **P. 191, unargued**: "Also, in this case M would be a continuous circle-like circle of
  continua." ("In this case" means with (9) omitted; the claim for the chains with (9) is
  implicit in the next two sentences.) That the elements of `G` are disjoint, fill `M` and form a
  continuous decomposition with a circle as quotient is not argued in either case.
* **P. 191, unargued**: "With the addition of (9) one may see with the help of [3] that each
  element of G is a pseudo-arc." (9) makes each new column `T_ij` crooked in a pair
  `T_hk + T_hl` of old columns. As far as I can see this does not control an element of `G`
  covered by two adjacent columns at some level: two crooked chains joined end to end are not
  crooked in general.
* **P. 190, unargued, not used**: "It is easy to see that G is an upper-semicontinuous collection
  of arcs, G is a circle (if its elements are thought of as points) and G* (the sum of the
  elements of G) is a circle-like continuum." (the collection of `V`'s).
* **Commission 202** obtains the example by a construction of my own (scheduling notes §244): a
  recognition theorem for nested circular chains with arcs of the base circle, sweep patterns,
  and a circular planar step. Nothing of §7 is used except its claim. Not counted.
* **Batch 202 outcome.** Verified: the recognition theorem, the sweep lemma and patterns, the
  circular planar step, and `bjPlaneExample`; with them the classification in both forms (Part
  G is complete). Aristotle's ledger BJ.41–BJ.47 agrees with the sixth reading and adds two slips:
  * BJ.46, the figure on p. 191 (checked at 400 dpi): the labels write the level second,
    `T_{r k+1}`, `T_{r+2 k+1}`, `T_{r+3 k+1}`, `T_jk`, against the text's `T_ij` (level first);
    and the end points are labelled `a₁`, `c₁` beside `b_i`. Printed `a₁`, `c₁`, read `a_i`,
    `c_i`. Harmless.
  * BJ.47, the letter `G` for the collection of arcs (p. 190) and for the set of subcontinua
    irreducible from `W₁` to `W₂` (p. 191). Harmless.
  * **BJ.43 not counted.** Aristotle would count it as a defective proof; it agrees that (9) does
    not visibly control an element of `G` covered by two adjacent columns, but gives no
    certificate. The status vocabulary asks for an identified failing step; without chains
    satisfying (1)–(9) whose `G` has an element that is not a pseudo-arc, the step is not shown
    to fail. Label: not established. Counts unchanged: 24 and 18.

### A.26 L. C. Hoehn and L. G. Oversteegen, *A complete classification of homogeneous plane continua*, Acta Math. 216 (2016), 177–216 (Part F and the final assembly; my first reading, 2026-10-17)

Read from page images at 200 dpi, introduction only (journal pp. 177–183).

* **p. 180, Theorem 2: an unstated step (my reading).** "It follows immediately from Theorems B and
  C above and Theorem 1 that every indecomposable non-degenerate homogeneous plane continuum is a
  pseudo-arc. Combining this with Theorem A above, we obtain the following classification": the
  circle, the pseudo-arc, and the circle of pseudo-arcs.
  * p. 183 defines the circle of pseudo-arcs as "a circle-like continuum which admits an open map to
    the circle whose point preimages are pseudo-arcs". It adds: "Bing and Jones proved that the
    circle of pseudo-arcs is homogeneous and that it is unique, in the sense that it is the only
    continuum (up to homeomorphism) with the above properties."
  * Theorem A (p. 179) gives the open map with homeomorphic fibres, but not circle-likeness. So the
    step "a decomposable homogeneous plane continuum whose fibres are pseudo-arcs is circle-like"
    is used and not stated or cited.
  * The paper itself observes that circle-likeness does not follow from the open map alone, but
    does not draw the consequence: the pseudo-arc × `S¹` "is homogeneous but not embeddable in the
    plane" (p. 183).
  * This is the step A.25 flags. The paper cites nothing for it. A route from the later literature
    (terminality of Jones's elements, then Lewis 1985) is in A.27.
  * **Updated 2026-10-20.** Lewis 1985 does not contain that step (it leaves uniqueness open), and
    the first proof I have found is Domokos–Prajs 2022, Theorem 6.1, whose authors "did not find in
    the literature a proper reference" (A.27). So when Hoehn–Oversteegen wrote, the step was
    asserted in surveys but unproved in print. Classification: a gap in the proof of Theorem 2
    (nothing printed is false; the statement holds by Domokos–Prajs, pending its formalization).
    Not counted.
* **References used by the classification.** [16] Jones 1955; [12] Hagopian 1976; [45]
  Oversteegen–Tymchatyn, *Plane strips and the span of continua. I*; [49] Rogers 1981, *Homogeneous,
  separating plane continua are decomposable*, Michigan Math. J. 28. The paper cites [49] as
  background only. But the proof of Theorem C in [45] uses it (A.27, "Theorem C").

**Second reading: §§3–7 and the sources they cite (2026-10-18; for commission 193).** Read from
page images at 200 dpi (journal pp. 184–211), with Lelek 1979 [31] (Topology Proc. 4, 631–633)
and Krasinkiewicz–Minc 1977 [24] (Bull. Acad. Polon. Sci. 25, 675–680).

* **p. 211, Theorem 1 restated without "non-degenerate" (misprint; my reading).** "A continuum X
  is homeomorphic to the pseudo-arc if and only if X is hereditarily indecomposable and has span
  zero." The statement on p. 180 begins "A non-degenerate continuum". As restated it is false for a
  one-point continuum. Theorem 1′ (p. 212, "surjective semispan zero" in place of "span zero")
  has the same defect.
* **[31] is a research announcement (my reading).** H–O p. 191: "Because X has span zero, it is
  tree-like [31]"; p. 211: "Since X has span zero, by [31] we have that X is tree-like." Lelek 1979,
  p. 631: "The purpose of the present paper is to announce some results … A complete version will
  be published elsewhere." Its Lemma 5 and Theorem 6 carry no proof; Corollary 10 ("If X is a
  continuum and σ(X) = 0, then X is tree-like") is obtained on p. 633 from its Corollary 9 with
  Lelek 1964, Krasinkiewicz 1976 and Case–Chamberlin 1960. On p. 212 H–O supply a published
  reference for a stronger statement: "It is proved in [46] that any continuum with surjective
  semispan zero is tree-like" ([46] = Oversteegen–Tymchatyn, Fund. Math. 122 (1984)). So the
  citation on pp. 191 and 211 is to an announcement, and p. 212 cites a proof. (My first draft
  of commission 193 said H–O give no other reference.)
  * Lelek 1979 itself (checked by the referee of commission 194 and by Aristotle in batch 194,
    against page images; I rechecked pp. 632–633): Propositions 1–4 are called "rather
    straightforward" and are not proved; Lemma 5 and Theorem 6 have no proof. Corollary 9 ("If X is
    compact and σ(X) = 0, then each mapping f: X → T is inessential") is listed among "corollaries
    to theorem 6" but drops Theorem 6's hypothesis "dimX ≤ 1". On p. 633 Corollary 10 is obtained in
    one paragraph: "It is known [4] that continua of span zero are one-dimensional if
    non-degenerate. By corollary 9, the mappings defined on them and having values in
    one-dimensional polyhedra [3] are all inessential, and then corollary 10⁽²⁾ can be obtained via
    a well-known characterization of tree-like continua [1]." The passage from `T` to all
    one-dimensional polyhedra is the bare citation of [3]. Not used on this route; Part D row.
  * Not needed on my route (commission 193): the proof of Theorem 1 uses the tree only as a graph,
    and Theorems 4, 15 and 20 are stated for graphs. For plane continua a grid graph serves:
    hereditary indecomposability gives empty interior, and radial projection in the squares of a
    fine grid maps the continuum into the union of their edges.
  * For continua outside the plane, Lelek 1964 [29] (span zero implies dimension at most one; with
    proof) would give graphs by nerves of covers of order two. Not on the route.
* **p. 184, Theorem 4: no defect (my reading, corrected).** I first read "there is a continuum
  Zₙ ⊂ Gₙ × Iₙ meeting Gₙ × {pₙ} and Gₙ × {qₙ} … such that d(x, y) ≥ ε for all (x, y) ∈ Zₙ" as
  unjustified, because the complement of `Mₙ` contains the end rows. It is right: apply [44,
  Theorem 5.2] to `{d ≥ ε}`; if no continuum there joins the rows, its splitting extends by the
  rows to a separation. The compactness of the hyperspace it uses is stated on p. 183.
* **p. 211, proof of Theorem 1: an unargued step (found by the independent check of commission
  193).** "It follows that d_H(X,T)<δ": from `d_sup(f, id_X) < δ` only `X ⊆ T_δ` and
  `f(X) ⊆ X_δ` follow, while Theorem 4 needs `T ⊆ X_δ` too. Repair: replace `T` by `f(X)`, a
  subcontinuum of a tree and so a tree. My route needs only `G ⊆ X_δ`, which the grid gives.
* **p. 185, Lemma 6: stated without proof.** "The proofs of these properties are left to the
  reader." Seven properties. **Verified in batch 194** for folds in the sense of `IsSimpleFoldOf`:
  items (1), (2), (4)–(7) (`ho16_lemma6`); (3) holds by definition. Nothing against H–O.
* **pp. 186–187: unargued.** "It is straightforward to see" (the fold determined by `G₁, G₂, G₃`);
  "It is straightforward to check from the definition of a simple fold that … F′ … is a simple
  fold" (Proposition 7). **Batch 194:**
  * The existence of the fold is verified in another form (PL heights in `E × ℝ`); the uniqueness
    clause ("then there is a homeomorphism θ: F′ → F") is not formalized and not used.
  * Proposition 7 is verified as stated. Three unargued steps are supplied: the component `K` of
    `G₂` meeting both closures ("By (F2) and (F3), and since G is connected", p. 186; `G₂` has
    finitely many components); the application of Claim 7.1 on p. 187, which needs `φ(C′) ⊆ G₂`
    (supplied through the component of `G₂` containing `φ(p)`); and "F′ … is a simple fold",
    through a lemma H–O do not state (a component of `G₂` that misses `∂G₁` has copies over `G₃`
    that are clopen in `F`). No clause of the definition fails. The referee's two test cases agree
    (checked by hand).
  * The two remarks of p. 186 are right: "In general, even if G is connected, a simple fold F on G
    need not be connected" (`G = [0, 2]`, `G₁ = G`, `G₂ = G₃ = [1, 2]`), and "if G is connected and
    ∂G1=∅, then G1=G, F is disconnected, and φ|F1 is a homeomorphism of F1 onto G". Checked in
    words.
* **pp. 187–189, Theorem 8, (1) ⇒ (2): a gap in exposition (my reading, refined by the
  independent check).** The fans must be pairwise disjoint (for "L′ is closed and open"); this is
  not said. With it, `U₁ ∩ U₃ = ∅` follows from the choice of the `Uᵢ`; `(X₂∪X₃)∩U₁ = U₁∖X₁` is
  open, so `∂L′` has its literal meaning. (I had listed both as further gaps.) The claim
  "f(cl(Uᵢ∖Kᵢ)) ⊂ ⋃ⱼ Oⱼⁱ" is true: a frontier point of `Kᵢ` maps to one of the `yⱼⁱ`.
* **p. 189, Theorem 8, (3) ⇒ (1): misprint (my reading).** "By [24] it suffices to show that
  X=X₁∪X₂∪X₃ where … X₁∩X₂⊂U, and X₂∩X₃⊂V"; the proof then shows "X₁∩X₂⊂V" and "X₂∩X₃⊂U", the
  form quoted on p. 187. `U` and `V` are interchanged in the first sentence. The printed condition
  holds in every compactum (`X₂ = X`, and `X₁`, `X₃` small closed neighbourhoods of `A`, `B`), so
  it cannot be the criterion. Not on the route.
* **pp. 189–191, Definition 9 and Propositions 10–11: unargued.** The observations after
  Definition 9 (the characterization of `σ_B(A)`); Proposition 10's first part "follows immediately
  from the observations"; Proposition 11: "Clearly G₁, G₂, and G₃ are all regular subsets of G".
* **pp. 194–198, Theorem 15: unargued steps.** Claim 15.1: "We leave it to the reader to show that
  there exists a set M′ having properties (1), (3), (5), and (6), and which separates" (the main
  construction; my route replaces it by a piecewise linear approximation of a sign function).
  Also: "for each point a∈Z′, the set M′∩{a}⋆ contains an odd number of points" (p. 196); "clearly
  S irreducibly separates G×{0} from G×{1}, because M′ does" (p. 197); "It is clear that S_i^[a,b]
  is straight"; "Properties (S3) and (S5) are immediate from the construction" (p. 198).
* **p. 209, Proposition 19: unargued.** "there is a component K of π(P₂)=φ(F₂) such that K meets
  both π(E(P₁))=∂φ(F₁) and π(γ_{i₀})=∂φ(F₃)".
* **p. 210, Theorem 20: an unneeded assumption.** "We further assume that the numbers εᵢ are chosen
  small enough so that h(X)⊂U": `h(X)` lies in `S ⊆ U` whatever the `εᵢ`. Harmless.
* **Misprints.** p. 209 "((φₙ)⋆∘…∘(φ₁)⋆)⁻¹(S)" (the maps compose as `(φ₁)⋆∘…∘(φₙ)⋆`, as on
  p. 210); p. 195 "C₁ and C₂ are arcs which both have x as an endpoint" for `(x, y)`; p. 198
  "Since aᵢ∈C" for `a_p`; p. 202 "E(S″)⊂(F₁∩F₂)⋆ since S″⊂(F₁∩F₂)⋆" for `F₁ ∪ F₂`; pp. 205 and
  206 `φ⁻¹` for `φ⋆⁻¹` (once each; also p. 207, fourth reading).
* **Proposition 14** ("Though we will not technically need the next proposition in the sequel",
  p. 193): not read closely.
* **Krasinkiewicz–Minc 1977, Lemma 2 (p. 676): no defect found.** For hereditarily indecomposable
  `X` its Lemma 1 is not needed: the two components that meet at a point of `A* ∩ B*` form a
  decomposable continuum.

* **Batch 193 outcome.** Verified: Theorem 4 in path form (any proper metric space; `X` need not
  be connected; only `G ⊆ X_δ` of the graph); the core of Theorem 8, (1) ⇒ (2), without folds (by a
  correction toward the fan vertex instead of Tietze extensions); K–M Lemma 2 for hereditarily
  indecomposable compacta; and, from `HOThm20`, Theorem 1 ("if") for plane continua and "every
  indecomposable non-degenerate homogeneous plane continuum is a pseudo-arc" (p. 180). Aristotle's
  ledger HO.1–HO.8 adopts the entries above, except one reading of p. 188 taken from the text layer. Still to classify: Theorem 1′ (p. 212) is false at a one-point continuum as printed; I
  propose counting it as false as printed, as Jones 1949 Theorems 1–2 and Moore 1920 Theorem 4 are,
  and Theorem 1 on p. 211 as a misprint (p. 180 is correct). Commission 194 asks for both
  certificates and Aristotle's view.
* **Batch 194 outcome.** Verified: the PL-graph library, the existence of simple folds, Lemma 6,
  Theorem 8 (1) ⇒ (2) for folds and Proposition 7 (bullets above), with no named hypothesis.
  Classification settled with Aristotle: **Theorem 1′ (p. 212) is a false printed statement** at a
  degenerate case (`ho16_theorem1prime_printed_false`), counted as Jones 1949 Theorems 1–2 and
  Moore 1920 Theorem 4 are; Theorem 1 as restated on p. 211 stays a misprint
  (`ho16_theorem1_printed_false` as supporting evidence). They are counted differently because
  Theorem 1 is stated correctly on p. 180, while Theorem 1′ is stated correctly nowhere, although
  p. 212 presents it as what "our proof of Theorem 1 in fact establishes". Aristotle withdrew its
  p. 188 reading. Aristotle's own ledger keeps no running count of false printed statements;
  this ledger's count is in Part D.
**Third reading: pp. 189–210, for commission 195 (2026-10-19).** Read from page images at 200 dpi,
with 400-dpi crops of the formulas with primes and subscripts (pp. 190, 192, 199–202).

* **p. 190, the observations after Definition 9: unargued (my reading: right).** "σ_B(A) is equal
  to the closure of the union of all components of G\B meeting A∩V" and "σ_B(A) can be
  characterized as the unique closed (regular) set D⊂G such that ∂D=B and D∩V=A∩V for some
  neighborhood V of B". Both use that `G \ A` and `G \ B` have finitely many components.
* **p. 190, Proposition 10, second part: an unargued step (my reading).** "Let C′ be a component of
  G\A′ meeting C∩V. … If C′≠C, then there must be a point x∈∂C′∩C. But since A′ has consistent
  complement relative to B, we must have x∈B". Consistency gives `∂C′ ⊆ B` only if `∂C′` meets
  `B`, which is not shown for a `C′` that merely meets `C ∩ V`, `V` being the neighbourhood of the
  hypothesis. Repair: shrink `V` to miss the closures of the finitely many components of `G \ A′`
  whose closures miss `B`. The statement is right. Also unstated there: `∂C ⊆ B` (from the
  consistency of `A`). The second part is used again on p. 208 (Proposition 19, (S4)). The
  independent check of commission 195 agrees.
* **pp. 190–191, Proposition 11: three short unargued steps.** "Clearly G₁, G₂, and G₃ are all
  regular subsets of G"; "If x∈A, then we must have x∈B₂"; "one can find a neighborhood of x which
  meets only A and components of G\A whose closures meet B₂".
* **p. 192:** "comple ment" in (S4) (a stray space). The observation after Definition 12 (π is open
  on `S \ 𝓔(S)`) is right.
* **pp. 193–194, "G connected" omitted (my reading).** p. 193: "it will follow from the next
  proposition (in fact from Claim 14.1) that if k is odd then π(S)=G"; p. 194: "consider a set
  S⊂G×(0,1) with a stairwell structure of height 1. In this case, π maps S homeomorphically onto
  G". With H–O's convention ("G will denote a (not necessarily connected) graph", p. 184) both are
  false: `G = [0, 1] ∪ [2, 3]`, `S = [0, 1] × {½}`. Both point to Proposition 14 ("If G is a
  connected graph"). Proposed: omitted hypotheses, not counted; certificate commissioned.
* **p. 200, Proposition 17: the hypothesis `k ≥ 3` is not printed** (for `k ≤ 2` the conclusion
  has height `≤ 0`); harmless, since Theorem 20 applies it to odd `k ≠ 1`. "It is now easy to
  verify": checked by me clause by clause. p. 210 (Theorem 20, Step 2): "if γ_{i₀}=∅, then in fact
  S has a stairwell structure of height k−2" says more than p. 201, which gives the structure to
  `S₁ ∪ … ∪ S_k ⊆ S` only (found by the independent check); harmless.
* **pp. 201–202, Lemma 18: right (my reading).** Unargued: that `π(S′)` has finitely many
  components (H–O check only non-degeneracy). Misprint: "clearly 𝓔(S″)⊂(F₁∩F₂)⋆ since
  S″⊂(F₁∩F₂)⋆" for `F₁ ∪ F₂` (400 dpi; already listed above); "S″ is a straight" (a word missing).
* **pp. 202–203, omitted citations (found by the independent check).** "So, by (S2′) and
  Proposition 11": Proposition 11 also needs (S4′); the identity `π(P₁) = σ_{π(𝓔(P₁))}(π(P₂))`
  also uses (S4′) and `𝓔(P₁) ≠ ∅`, where H–O cite (S3′). Harmless.
* **Genericity** is used in Proposition 19 only at p. 207 ("φ(z) is not a branch point of G, so
  there is a neighborhood of z in F which is homeomorphic to an open arc J") and p. 208 ("the set of
  branch points and endpoints of F is φ⁻¹(Z)"). The formal reading: a point is neither a branch
  point nor an endpoint iff it has a neighbourhood that is two segments meeting at it (p. 183
  defines both through cutpoints of connected neighbourhoods).
* **Batch 195 outcome.** Verified, with no named hypothesis: everything listed in this third
  reading except Proposition 19 after its first step. Aristotle's ledger (HO.13–HO.22) agrees with
  every reading above. Classification: Proposition 10's second part is a gap in the proof
  (statement true; not counted), as Aristotle proposes; Aristotle's formal proof avoids the step
  altogether, through the first part of the proposition (`C` is a component of `G \ B` missing
  `A`, hence missing `σ_B(A) = σ_B(A′) ⊇ A′`). The omitted "G connected" of pp. 193–194: not
  counted (certificate `ho16_p193_remark_false`).

**Fourth reading: pp. 202–210, for commission 196 (2026-10-19).** Read from page images at 200 dpi,
with 400-dpi crops of pp. 203, 205, 206 and 208.

* **p. 208, (S4′) for `P′₂`: a false sentence in the proof (my reading).** "If D⊂F₁∪F₂, then …
  φ(D) is contained in a component D̃ of G\π(S_{i₀}). Moreover, φ(D)⊂π(P₁∪P₂), so
  ∂D̃∩π(α_{i₀})=∅ by (S6′) for S. This means that either ∂D̃⊂π(β_{i₀}) or ∂D̃⊂π(γ_{i₀})."
  Example: `G = [0, 10]`, `k = 3`, `i₀ = 2`; `S₁ = [4, 10] × {0.1}`, `S₂` from `(4, 0.1)` to
  `(6, 0.5)`, `S₃ = G × {0.9}`; `α₂ = {(4, 0.1)}`, `γ₂ = {(6, 0.5)}`;
  `π(P₂) = [1, 2] ∪ [a, 6]`, `π(P₁) = [1, 2] ∪ [a, 10]` (`5 < a < 6`), `P₁` and `P₂` meeting
  over `1, 2, a`. Every clause of Definition 16 holds. In the fold of Proposition 19
  (`G₃ = [0, 6]`), the copies of `[1, 2]` in `F₁` and `F₂` form a circle component `D ⊆ F₁ ∪ F₂`
  missing `π(P′₂)`; `D̃ = [0, 4)` and `∂D̃ = {4} = π(α₂)`. The conclusion of the step holds
  (`∂D = ∅`; when `∂D ≠ ∅`, a point of `∂D` maps into `∂D̃ ∩ π(P₁ ∪ P₂)`, which misses `π(α_{i₀})`,
  and consistency does the rest). The sentence fails only for components of `F`, which the
  restriction of p. 209 discards. Proposed (the referee of commission 196 agrees): a defective
  proof (the seventeenth), statement true; pending Aristotle's certificate.
* **pp. 203–207: unargued steps.** "clearly each of φ⋆⁻¹(P₁)∩(F₁)⋆, … is straight" (regularity);
  the "straightforward observations" of pp. 205–206; (S3) on p. 207 ("It is then straightforward
  to see"); (S5′) on p. 208 ("the set of branch points and endpoints of F is φ⁻¹(Z)").
* **p. 205: a misprint.** "P′₁∩(∂F₃)⋆=φ⋆⁻¹(γ_{i₀}) by (19.2)" is false whenever `γ ≠ ∅`:
  `φ⋆⁻¹(γ)` also contains the points over the `F₁`-copies of `π(γ)`, in `F₁ \ F₂`. It should read
  `φ⋆⁻¹(γ_{i₀}) ∩ (∂F₃)⋆`; the next clause uses only `⊆` (found by the independent check).
  `φ⁻¹` for `φ⋆⁻¹` occurs three times (pp. 205, 206, 207). Slips on p. 207: `β_{i₀}`, `β′_{i₀}`
  for their projections, and `P′₂` for `π(P′₂)`.
* **p. 209.** The component `K` of `π(P₂)` meeting both frontier sets: unargued (H–O's reason,
  consistent complement, works). "clearly C meets ∂F₃ by Lemma 6 (6)": right (`φ(C) = G`, so `C`
  meets `F₁ \ F₂` and `F₃ \ ∂F₃`, and Lemma 6 (6) separates them); my first reading, that the
  citation was wrong, was itself wrong.
* **Batch 196 outcome.** Verified: Proposition 19 (full fold and connected fold), the ordinary
  points of a fold, the certificate `ho16_p208_false` (the example of commission 196 §4, checked in
  Lean clause by clause, every sheet at height ½), and Theorem 20 from Theorem 15. Aristotle's
  ledger HO.23–HO.28 agrees with the fourth reading, except that it records only two `φ⁻¹` slips
  and could not read the start of the p. 207 line "P′₂=φ⁻¹(π(S_{i₀}))∩(F₁∪F₂)"; I confirmed both
  p. 207 items on 400-dpi crops ("since S′_{i₀}∩(F₃)⋆=φ⁻¹(S_{i₀})∩(F₃)⋆" in the (S4) paragraph).
  **Counted:** p. 208 as a defective proof (the seventeenth). The formal proof of the connected
  version does not use H–O's `K`: any component from Proposition 7 serves. *Scope of the
  certificate* (checked 2026-10-22 by the referee of the severity document; `HPC/HO16/P208.lean`):
  it is a statement about `G` only, with `a = 11/2` and every sheet at height ½: a point
  `x = 3/2 ∈ π(P₂) \ π(S₂)` whose component `[0, 4)` in `G \ π(S₂)` has the frontier point
  `4 ∈ π(α₂)`. The fold and its circle component `D` are not constructed; that part of the reading
  above is a hand argument.
* **p. 210.** "after a sequence of at most (k₀−1)+(k₀−3)+...+1 simple folds": for odd `k₀` the
  printed sum mixes parities; each pass from height `k` to `k − 2` uses at most `k − 2` folds; an
  upper bound either way. Harmless.

**Fifth reading: pp. 194–198 (the proof of Theorem 15), for commission 197 (2026-10-20).** Read
from page images at 200 dpi, with 400-dpi crops of pp. 195 and 198; the independent check of
commission 197 read the same pages at 400 dpi. Beyond the items of the first reading (Claim 15.1,
the odd counts at `Z′`, "clearly S irreducibly separates", "It is clear that S_i^[a,b] is
straight", "(S3) and (S5) are immediate", and the misprints "x as an endpoint" (p. 195) and
"Since aᵢ∈C" (p. 198)):

* **p. 195, the passage to an irreducible subset: unargued.** "Replacing M′ by a subset … which
  irreducibly separates G×{0} from G×{1} in G⋆ accomplishes (2)": why the subset keeps (1) and (3)
  is not said.
* **p. 195, property (4): a wrong reason (found by the independent check; my reading agrees).**
  "Note that (x,y) cannot be an endpoint of M′, because x is not an endpoint of G by (5), and
  π(M′∩V) is open for some neighborhood V of (x,y) by (3)". Here `(x, y) ∈ T`, and (3) speaks only
  of points of `M′ \ T`; the openness at `(x, y)` comes from irreducible separation. The step is
  true.
* **pp. 195–196, the branch-point surgery: unargued.** "It follows that n is even"; "Obviously
  this can be done without compromising properties (1), (5), and (6), and without leaving U"; "It
  is easy to see that the resultant M′ still irreducibly separates G×{0} from G×{1} in G⋆".
* **p. 197, the zig-zags: an unstated condition (found by the independent check).** Nothing
  excludes `b ∈ J_j`; then `C¹_j` reaches `{b}⋆`, against "S_i^{[a,x]}∩{a}⋆=∅ if i>j" (p. 198).
  The `J_i` must lie in the open arc. Otherwise the construction is right (the `J_i` ordered from
  `π(W)` toward `b`; `C¹_i`, `C²_i`, `C³_i` into `S_i`, `S_{i−1}`, `S_{i−2}`), and "clearly S
  irreducibly separates … because M′ does" is unargued (`S ≠ M′`).
* **p. 198, (S4): an incomplete case split (found by the independent check).** "If C⊂[a,b] …";
  "Suppose, on the other hand, that x₁,x₂∈∂C do not belong to the same component of G\Z′": a
  component not inside one arc, with its frontier points on one arc (around a cycle of `G`), is in
  neither case; the same chain argument covers it. Also "It is now easy to see that each of x₁ and
  x₂ corresponds to the tip point …": unargued.
* **p. 198: typography.** "|M′∩{z}_*|<i" prints an asterisk for the star (400 dpi).
* **The route of commission 197 avoids all of this**: ladders (explicit sheets over a
  decomposition, zig-zags on one line, explicit end sets, the parity argument made exact by
  odd-length lists), and a ladder inside `U` built from a sign function on a grid, with no
  irreducible separators and no Claim 15.1. Proposed: nothing on pp. 194–198 counted (misprints,
  one wrong reason for a true step, gaps; every statement true).
* **Batch 197 outcome.** Verified on the ladder route, with no named hypothesis: Theorem 15,
  Theorem 20 and the main theorem for indecomposable continua. Aristotle's ledger HO.29–HO.35
  agrees with this reading item by item (its HO.34 adds a sketch in words of why Figure 8's set
  separates). Nothing counted; the counts stay at 22 false printed statements and 17 defective
  proofs. Aristotle's route differs from the commission's in three harmless ways: `u` is
  2-Lipschitz (so `δ` is explicit), each grid edge is cut into `N − 1` equal pieces with at most
  one flip each, and the event of a piece is read off its two end lists.

### A.27 The circle-of-pseudo-arcs step and Theorem C in the later literature (search of David's collection, 2026-10-17)

Found by text search of the PDFs. The quotations marked (img) were checked against page images at
200 dpi; the others are from the text layer only. Nothing here is formalized or checked by
Aristotle.

* **What the classification needs.** A decomposable homogeneous plane continuum `M` whose Jones
  elements are pseudo-arcs is homeomorphic to the Bing–Jones circle of pseudo-arcs (A.25, A.26).
* **Planarity and dimension 1 are not enough.** Prajs, *A continuous circle of pseudo-arcs filling
  up the annulus*, Trans. AMS 352 (2000), 1743–1757.
  * Theorem 8 (p. 1753, img): "There exist a plane s-arc of pseudo-arcs and a plane s-circle of
    pseudo-arcs." These are curves (p. 1752) with continuous decompositions into pseudo-arcs over
    an arc and over a simple closed curve.
  * p. 1753 (img), on Lewis's questions whether such curves over an arc are unique and whether
    their elements must be terminal: "The above examples show that the answer to both these
    question is no. The known arcs of pseudo-arcs (circles of pseudo-arcs) are chainable
    (circularly chainable), while the examples constructed here are triodic, and thus
    topologically different. Evidently, their elements of the decompositions are not terminal."
  * So the step must use homogeneity.
* **The surveys take the step for granted.**
  * Lewis, *Homogeneous continua and continuous decompositions*, Topology Proc. 8 (1983), 71–84,
    pp. 72–73: five classes, among them "3) circle of pseudo-arcs" and "5) circles of continua of
    type 4". No argument that a circle of pseudo-arcs in class 3 is circle-like.
  * Lewis, *The pseudo-arc of pseudo-arcs is unique*, Houston J. Math. 10 (1984), 227–234, p. 230:
    "(or a homogeneous separating plane continuum other than the simple closed curve and the
    circle of pseudo-arcs)".
  * Lewis, *The classification of homogeneous continua*, Soochow J. Math. 18 (1992), 85–121,
    p. 102: a positive answer to Jones's Question 13 "would show that the classification of
    homogeneous plane continua is complete with the four currently known examples". Yet p. 100
    lists as open (Question 10) whether two one-dimensional continua with continuous decompositions
    into pseudo-arcs over homeomorphic quotients must be homeomorphic.
* **A route through terminality (my reading, not checked).**
  1. *Jones's elements are terminal.* This is in Jones 1955 itself, Theorem 1 (c) (p. 736, img): "if
     g is an element of G and K is a subcontinuum of M which contains both a point of g and a point
     of M − g, then g is a subset of K." It is verified as `jones55_c` and, without decomposability,
     as `Lset_subset_of_meets` (both standard axioms; batch 184 `axioms.txt` lines 759 and 783). I
     found this after writing the corroborating citations below; step 1 needs nothing beyond the
     repository.
     * Rogers, *Cell-like decompositions of homogeneous continua*, Proc. AMS 87 (1983), 375–377
       (uploaded by David, 2026-10-17), proof of Theorem 5 (p. 377, img): "Jones [1] has shown
       that his decomposition of X consists of terminal continua." [1] is Jones 1955.
     * Krupski–Prajs, *Outlet points and homogeneous continua*, Trans. AMS 318 (1990), 123–141,
       Theorem 6.6 (p. 138, img): a homogeneous curve has a unique continuous decomposition whose
       elements are hereditarily indecomposable, tree-like, homogeneous and terminal, and whose
       quotient is a homogeneous curve with no proper nondegenerate terminal subcontinua.
     * Their introduction: "In the case where X is decomposable the decomposition coincides with
       the known Jones aposyndetic decomposition [24, Theorem 5, p. 377]". [24] is Rogers 1983.
       The proof of Theorem 6.6 cites "[24, Theorem 4, p. 377]". There is no slip: Theorem 4
       (a partition into terminal subcontinua respected by all homeomorphisms is a continuous
       decomposition) is what the proof uses, and Theorem 5 is the one about Jones's
       decomposition.
     * Rogers, *Classifying homogeneous continua*, Topology Appl. 44 (1992), p. 348: "Implicit in
       the proof of Jones' decomposition for a decomposable, homogeneous continuum X is the fact
       that {L_x : x ∈ X} = {Z : Z is a maximal, terminal proper subcontinuum of X}." Terminality
       itself is not implicit: Jones states it as Theorem 1 (c). Maximality is what is left to the
       reader.
  2. *Terminal elements give uniqueness.*
     * Lewis 1983 (Topology Proc.), p. 80 (img), of the uniqueness question: "This question has an
       affirmative answer if all of the decomposition elements in each of G₁ and G₂ are terminal
       continua."
     * Lewis, *Continuous collections of hereditarily indecomposable continua*, Topology Appl. 74
       (1996), 169–176, p. 173 (img): "For each continuum in one class there is a unique
       corresponding continuum in the other class, obtained either by shrinking out maximal
       terminal pseudo-arcs or by enlarging each point to a terminal pseudo-arc."
     * The proof is in Lewis, *Continuous curves of pseudo-arcs*, Houston J. Math. 11 (1985),
       no. 1, 91–99, as in Lewis 1996 [24] and Lewis–Zhou 2002 [18] (confirmed on the journal's
       table of contents for 11(1)). Lewis 1992 [82] gives pp. 225–236, which are the pages of
       Lewis, *Compact group actions on chainable continua*, 11(2) (harmless slip). I have not
       read the paper.
  3. *Apply it.* A homogeneous plane continuum has empty interior, so it is one-dimensional. By
     Jones, Theorems B and C, and Hoehn–Oversteegen Theorem 1, the Jones elements of `M` are
     pseudo-arcs over a circle, terminal by step 1. Step 2 then makes any two such `M`
     homeomorphic. Lewis's "terminal" is terminal in the whole continuum, which is what
     `jones55_c` gives.
     * This gives the exhaustive direction without Bing–Jones.
     * Naming the third continuum needs one example. Either Bing–Jones (homogeneous, planar:
       A.25), whose decomposition is the terminal one by Lewis–Zhou, Topology Appl. 126 (2002),
       p. 414, or Lewis 1985's construction.
* **Corrected 2026-10-20: Lewis 1985 does not prove uniqueness, and step 2 above fails as a
  route.** David obtained the paper (Houston J. Math. 11 (1985), 91–99; read from page images at
  200 dpi). Its results are existence and lifting: for every one-dimensional continuum `M` there is
  a continuous curve of pseudo-arcs `M̂` over `M` with terminal elements (the construction, pp.
  93–94), homeomorphisms of `M` lift to `M̂` (Theorem 4, p. 95), motion within elements is free
  (Theorem 5, p. 98). On uniqueness it says the opposite of what I had attributed to it:
  * p. 93: "It will follow from our construction that all decomposition elements are terminal
    continua. We still do not know in general whether M̂ is unique."
  * p. 98: "Our construction gives one method of obtaining continuous curves of pseudo-arcs. It does
    not indicate whether they can all be obtained by this type of construction or whether they are
    unique. As indicated in the introduction, for a few cases they are known to be unique."
  * p. 99, Question 2: "If M̂₁ and M̂₂ are two continuous curves of pseudo-arcs with homeomorphic
    decomposition spaces, are M̂₁ and M̂₂ homeomorphic?"
  So the assertions of Lewis 1983 (p. 80) and Lewis 1996 (p. 173) quoted under step 2 cite a paper
  that leaves the question open; I found no proof of them. **My error:** I put the proof in Lewis
  1985 on the strength of those citations, marked as unread, and planned Part G on it.
* **A proof of the step needed here: Domokos–Prajs 2022.** A. Domokos and J. R. Prajs, *The Planck
  boundary within the hyperspace of the circle of pseudo-arcs*, arXiv:2203.15906 (2022), Theorem
  6.1 (read through a web fetch of the arXiv PDF, not from page images): "A continuum X is a circle
  of pseudo-arcs if and only if X admits an open atomic map f : X → S onto a simple closed curve S
  such that all point-inverses, f⁻¹(y), are pseudo-arcs." Atomic means every point-inverse is
  terminal; "circle of pseudo-arcs" means homeomorphic to Bing–Jones's example. The authors: "We
  include the proof because we did not find in the literature a proper reference to this theorem."
  The proof: `X` is atriodic ("one can easily show"); the preimages of the two halves of the
  circle are "atriodic folders of chainable continua", chainable by Proposition 6 of Hagopian,
  Marsh and Prajs, *Folders of continua*, Topology Proc. 55 (2020), 13–33; then Bing–Jones
  Theorem 10 glues them onto Bing–Jones's example (the gluing of commission 198 §4). With
  terminality (`jones55_c`) this gives the step of A.25–A.26 for the classification.
* **Both papers read (David, 2026-10-20; page images at 200 dpi).**
  * Domokos–Prajs, arXiv:2203.15906v1, pp. 13–14: the quotations above are confirmed on the
    images. Definitions (p. 13): "A subcontinuum K ⊂ X is terminal in X, if for any continuum L ⊂ X
    with K ∩ L ≠ ∅ we have either K ⊂ L or L ⊂ K. A map f : X → Y between continua X and Y is
    called atomic if all point-inverses f⁻¹(y) for y ∈ Y are terminal subcontinua of X." (p. 14):
    "We call a continuum a circle of pseudo-arcs if it is homeomorphic to the original example Ψ of
    Bing and Jones [4]." The proof of Theorem 6.1 is the five sentences quoted above.
  * Unargued in it: "one can easily show that X is atriodic". My reading: true, by a saturation
    lemma for atomic maps (a subcontinuum `L` either lies in a fibre or equals `f⁻¹(f(L))`, by
    terminality). A triod with `K` saturated maps onto a triod in `S¹`; with `K` in a fibre `F`,
    either the triod lies in `F` (a pseudo-arc is atriodic) or all three continua are saturated and
    contain `F`, so `K = F` and their images are three arcs of `S¹` meeting pairwise only at
    `f(F)`, which is impossible. Also unargued: that Ψ's map is atomic ("It is known"; only the
    other direction is needed here).
  * Hagopian, Marsh and Prajs, *Folders of continua*, Topology Proc. 55 (2020), 13–33. Definition 1
    (p. 14): "We refer to a member X of M together with a monotone surjective map η: X → [0, 1] as
    a continuum folder. … If each fiber of X is either a point or belongs to G, we call X a G folder
    or a folder of continua from G." Proposition 6 (p. 16): "A folder of chainable continua is
    chainable if and only if it is atriodic." Its proof: unicoherence by Proposition 1 (the
    Vietoris–Begle theorem and Bruschlinsky's theorem, Čech cohomology), irreducibility by
    Sorgenfrey, dimension one by Proposition 5 (Lelek–Zaremba), trivial shape by Proposition 2
    (Sher), "Thus, we have that X is tree-like. So, X is hereditarily unicoherent", indecomposable
    subcontinua in fibres by Proposition 4, and Fugate 1969 Theorem 2 [14]. Nothing found wrong;
    "Thus … tree-like" and the acyclicity of chainable fibres are not argued (standard facts).
* **Route for Part G (my reading).** In our case (an open atomic map onto an arc, pseudo-arc
  fibres) the shape theory is not needed. The saturation lemma gives directly that `f⁻¹(arc)` is
  atriodic and hereditarily unicoherent, and that its indecomposable subcontinua lie in fibres
  (a saturated subcontinuum over a non-degenerate arc is decomposable), which have empty interior
  (`f` is open). So Fugate 1969 Theorem 2 applies, in its Case II ("Each indecomposable
  subcontinuum of M has void interior"). There the continuum `K` of the proof, an irreducible
  terminal subcontinuum of `A` inside the middle fibre, is a point: every subcontinuum of the
  fibre is terminal in `A` (subcontinua of a pseudo-arc through a common point are nested, and
  saturated ones contain the fibre). This is the terminal-point case that the repository's proof
  of Bing 1951 Theorem 11 already handles (A.5), with the map `f` in place of Bing's decomposition.
  Then Bing–Jones Theorem 10 and the gluing finish. Sources: nothing further needed.
* **The route as commissioned (199, 2026-10-20).** Sharper than the paragraph above: Fugate 1969 is
  not needed either. Bing's proof of 1951 Theorem 11, as the library has it
  (`exists_minimal_notCoverable`, `fugate_lemma1`, `epsCoverable_of_halves`), applies directly: a
  minimal non-`ε`-coverable subcontinuum lies in no fibre, so it is `f⁻¹[a, b]` with `a < b`; split
  it at the middle fibre, whose points satisfy condition B in each half. Openness of `f` is not
  used, and the fibres need only be snake-like and hereditarily indecomposable. Two consequences:
  * the classification with Domokos–Prajs's third class (an open atomic map onto the circle with
    pseudo-arc fibres) depends on Bing–Jones Theorem 10 alone;
  * the classification with Bing–Jones's third class (circle-like) also needs a circle of
    pseudo-arcs known to be circle-like (Bing–Jones §7), since atomicity gives circle-likeness
    here only through a homeomorphism with one.
* **An alternative route to circle-likeness, not pursued.** Ingram 1968 Theorem 2(2), sufficiency
  (two chainable continua with atriodic union and disconnected intersection have a circle-like
  union; A.7, not formalized), applied to the two halves, would give circle-likeness without
  Theorem 10 or §7. Its printed proof treats one case, leaves the others as similar, and rests on
  several reductions it does not prove (commission 132 §3.5, a transcription; not rechecked on the
  page images). Not needed: Theorem 10 and §7 are needed for the classification anyway.
* **Domokos–Prajs, Example 6.1 (p. 13, 200 dpi).** "Triggered by this result, Bing and Jones [4]
  constructed the *circle of pseudo-arcs*, denoted here by Ψ, which is a homogenous, decomposable
  and nowhere locally-connected continuum in the plane admitting a continuous decomposition into
  terminal pseudo-arcs. Therefore, we can assume having an open atomic map Π : Ψ → S¹ …". Bing–Jones
  do not prove that the elements are terminal. This is the support for "It is known" in the proof
  of the "only if" direction of Theorem 6.1 (p. 14). Unsupported as cited; not used by our route;
  not counted. ("homogenous": typography.)
* **Batch 199 outcome (Domokos–Prajs).** Verified: the "if" direction of Theorem 6.1, given
  Bing–Jones Theorem 10 (`dp22_theorem61`), with the halves made chainable by Bing's 1951 argument
  (`isSnakeLike_of_atomic'`). Aristotle's DP.2 observes that the "only if" direction also has a
  proof here, though not the one Domokos–Prajs cite: a plane circle of pseudo-arcs is homogeneous
  (Theorem 10), so Jones's decomposition gives an atomic map (`jones55_c`;
  `circle_or_atomic_of_decomposable`, `nonvac_atomic`), and any space homeomorphic to it inherits
  one. Verified for the plane example under `BJThm10` and `BJPlaneExample`; the transport to every
  circle of pseudo-arcs is commissioned (200). The atriodicity claim (DP.1) is not formalized.
* **Batch 200 outcome (Domokos–Prajs).** Verified: Theorem 6.1 in both directions, given
  `BJThm10` and `BJPlaneExample` (`dp22_theorem61_iff`), with the transport of open atomic maps
  along homeomorphisms (`IsAtomicCircPAMap.comp_homeomorph`).
* **Batch 201 outcome (Domokos–Prajs).** With `BJThm10` proved (`bjThm10`), the classification
  with Domokos–Prajs's third class (`ho16_classification_atomic'`) is verified with no named
  hypothesis, and so is the "if" direction of Theorem 6.1, as the term `dp22_theorem61 bjThm10`
  (no declaration states it yet). The "only if" direction still uses `BJPlaneExample`.
* **Batch 202 outcome (Domokos–Prajs).** Theorem 6.1 in both directions with no named hypothesis
  (`dp22_theorem61'`, `dp22_theorem61_iff'`).
* **Lewis, *Homogeneous circle-like continua*, Proc. AMS 89 (1983), 163–168** (uploaded by David,
  2026-10-17; text layer). It assumes circle-likeness throughout. On the plane case, p. 163: Bing
  and Jones "constructed a homogeneous circle-like plane continuum with a continuous
  decomposition into pseudo-arcs ... and showed that it is the only continuum with the above
  properties"; p. 165: "The case of the circle of pseudo-arcs has already been handled by Bing and
  Jones." Both keep circle-likeness among the hypotheses, so neither closes the step.
* **Theorem C uses Rogers 1981 (correction to my critical-path list).**
  * Hoehn–Oversteegen cite Theorem C to [45] alone. In Oversteegen–Tymchatyn, *Plane strips and
    the span of continua, (I)*, Houston J. Math. 8 (1982), 129–142, it is Theorem 3.6 (p. 140,
    img): "If X is a homogeneous plane continuum, then every proper subcontinuum of X has zero
    semi-span. Moreover if X is indecomposable, then the (semi-)span of X is zero."
  * The proof begins "Since X is atriodic tree-like". The source is p. 139 (img): "It is known
    (see Jones [13] and Rogers [20]) that a homogeneous plane continuum is either indecomposable
    and tree-like or it is a circle of such continua". [20] is Rogers 1981.
  * The proof also uses: Hagopian 1976 (Theorem B); Effros; Davis's equivalence of zero span and
    zero semispan (Theorem 1.1); Corollary 3.5 and Theorems 3.1–3.3 of the paper; and Cook [4].
  * Cook [4] is *Continua which admit only the identity mapping onto non-degenerate subcontinua*,
    Fund. Math. 60 (1967), 241–249 (uploaded by David, 2026-10-17; a scan without a text layer).
    The result used is Theorem 4 (p. 243, img): "If f is a mapping of the compact metric
    continuum X onto the hereditarily indecomposable continuum Y, then f is confluent." Its
    printed proof is six lines.
    * The proof takes a decreasing sequence of subcontinua `Cₙ`, each containing the component
      `C` properly, with intersection `C`.
    * It needs `C ≠ X`; when `C = X` the conclusion is immediate (unstated, harmless).
  * I had listed Rogers 1981 as background only (A.26; my reply of 2026-10-17). For Theorem C it
    is an input as the proof is written.
  * **Superseded (A.29):** the indecomposable case of Theorem 3.6 does not use tree-likeness, so
    neither Rogers 1981 nor a substitute is needed for Theorem C.
  * A substitute (my reading): with Theorem B, `X` is atriodic because hereditarily
    indecomposable. Tree-likeness then follows from Rogers, *Homogeneous hereditarily
    indecomposable continua are tree-like*, Houston J. Math. 8 (1982), 421–428, which is in the
    collection.
* **Constructions of a circle of pseudo-arcs (2026-10-21, for commission 202).** Read from page
  images at 200 dpi.
  * Lewis, *Continuous curves of pseudo-arcs*, Houston J. Math. 11 (1985), 91–99, p. 93: for a
    finite graph `M_i`, "one can form a continuum M̂_i with a continuous decomposition into
    pseudo-arcs, whose decomposition space is homeomorphic to M_i, by identifying the end
    pseudo-arcs of arcs of pseudo-arcs in the same manner that the endpoints of arcs are
    identified to form the vertices of M_i." For the circle this is an arc of pseudo-arcs with its
    two end pseudo-arcs identified. The arc of pseudo-arcs is taken from Bing–Jones; neither
    circle-likeness nor planarity of `M̂` is discussed. P. 91 takes Bing–Jones §7 at face value:
    they "constructed the circle of pseudo-arcs and showed that it is a homogeneous, circle-like
    continuum which separates the plane."
  * The same paper, p. 91, on its Theorem 1 (p. 92): "It is not stated as a theorem by Bing and
    Jones, but is a variant on their Theorem 10. It does however follow from their proof of that
    theorem and essentially satisfies the conditions existing after part (h) of step 2 of their
    proof." Its conditions I and II on a chain map are, in substance, Conditions C and A of
    commission 201 (`BJStep`): an independent extraction of the same step.
  * Boroński and Smith, *Continuous curves of nonmetric pseudo-arcs and semi-conjugacies to
    interval maps*, Topology Appl. 282 (2020), 107309 (uploaded by David, 2026-10-21), p. 6: "It
    follows from Lewis' construction that if M is G-like then his "M of metric pseudo-arcs" is
    G-like as well." Unargued there and not in Lewis.
  * Neither paper gives a plane circle of pseudo-arcs or a proof of circle-likeness for the glued
    arc; commission 202 is unchanged.

### A.28 F. B. Jones, *Use of a new technique in homogeneous continua*, Houston J. Math. 1 (1975), 57–61 (Part E, the arc step; my reading, 2026-10-18)

Read from page images at 250 dpi (six PDF pages, the sixth blank). Aristotle's transcription
(`doc/notes/jones75.md`, batch 186) agrees with the images except for two slips: the pages (57–62
for 57–61), and "`< ε`" for the printed "`d(h(p), p) ≤ ε`" in the Effros corollary. Role: the named
claim `NoArcIndecHomPlane`, the last open input of Theorem 1 of Hagopian 1976 on the 1984 route
(A.24). **Verified in batch 190** (`jones75_noArc`), by a proof that is not Jones's.

The findings below are my readings, checked by an independent agent before commission 189 went out
(it corrected one of them, on (d)), and confirmed by Aristotle in batch 189 (repository `LEDGER.md`,
"Jones 1975 I", J75.1–J75.5; the solenoid claims as a hand argument, not formalized). The
replacements of (c), (d) and (f) are verified (batch 189); the Theorem is verified (batch 190, by
the planar route below).

* **(f), p. 59: proof defective.**
  * The proof uses only the Effros corollary and (c), hence only (a) and (b). It ends: "This is
    impossible since the `3ε`-neighbourhood of `q₁p₁` contains no point of `p₂q₂` (and conversely)."
    That does not follow: the image of `a′b′` may run along the arc `q₁pq₂ ∪ g[a′b′c′]` past `q₁`
    and come back near `p₂q₂`.
  * The dyadic solenoid satisfies everything the proof uses (homogeneous, indecomposable,
    hereditarily unicoherent, atriodic in the sense of `IsTriod`, with (c)), and (f) fails there,
    also with `d(b, p) < ε`: a long arc of a dense line is `ε`-dense.
  * Two earlier steps are unargued too. "Takes `b` to `p`" and "`b′` is close enough to `b`" need
    `b` near `p`: the negation of (f) gives only a point of `ab` near `p` (read "close enough to
    `p`"). And "leaves the images `q₁` and `q₂` … in `D`" is unjustified for a homeomorphism that is
    not small.
  * For plane continua (f) is vacuously true once the Theorem is known; the proof does not
    establish it. The Theorem uses (f) twice: for `η`, and in its last sentence.
* **(d), p. 58, second sentence ("every point of `ab` is a limit point of `T − ab`").**
  * "Let `c` be the first point of `T` (if there is one) …": if such points exist, a first one does
    (the first point of `cl(T − ae) ∩ ae`). My first reading, that the argument shows only that no
    first point exists, was wrong; the check corrected it before the commission went out.
  * The gap is orientation: "`c′` has the properties possessed by `c`" holds only if the Effros
    homeomorphism preserves the direction of `T`. Adding `d(a, ce)` to the minimum repairs it.
  * The triod paragraph does not yield the contradiction as printed: nothing makes the images of
    `T` meet `T`.
  * Replacement (commission 189 §4): limit sets of lines are arc-saturated, and Jones's own
    `½d(a, T̄ − T)` device then shows every line lies in its forward and backward limit sets. The
    statement holds in both directions.
* **(c), p. 57: true; the argument from (a) and (b) is unstated.**
* **The Theorem, pp. 59–61: unargued steps.**
  * "let us assume that `T` is accessible from the complement of `M`";
  * "There exists a positive integer `η` … This follows from property (f)";
  * "This makes `h` take `[t₀, t_d]` onto (approximately) `[t_d, t₀]`. So there is a fixed point
    `t_f`". For small `ε` this is false: by (O) below, `h` preserves the orientation of `T`;
  * "Clearly `t_f` cannot lie in `D̄₁ ∪ D̄₂ ∪ D̄₃` without violating the selection of `η`";
  * "it is easy to see that `p ∉ D̄₂` and property (f) is violated".
* **Classification (batch 189, J75.1 and J75.4).** The proofs of (f) and of the Theorem are
  counted as defective proofs of true statements (the fourteenth and
fifteenth; Hagopian 1976 Theorem 1, counted in the batch-190 audit, is the sixteenth). (f) is true
for plane
  continua only vacuously, once the Theorem is known. In the Theorem, the step "This makes `h`
  take `[t₀, t_d]` onto (approximately) `[t_d, t₀]`" is unargued. Under the hypotheses of the
  setting it contradicts (O), so any argument for it would itself finish the proof. (d)'s second
  sentence and (c) are gaps in exposition (J75.2, J75.3).
* **Verified (batch 189).**
  * (c) (`union_arc`, `nested`);
  * lines (`exists_line`, `line_arc`, `homeo_on_line`);
  * (R0) (`no_reversal_arc`, without the hypothesis `A ∩ C = {p}`);
  * (R) (`exists_no_reversal`);
  * (O) (`orientation`);
  * recurrence and (d) in both directions (`omegaLim_saturated`, `line_recurrent`, `jones75_d`);
  * (L) (`no_backtrack`, `no_backtrack_in_collar`).

  All are in `HPC/Jones/Jones75*.lean`, on the standard axioms, and all except (L) are stated
  under `JonesSetting`.
* **The planar core (Aristotle's hand proof, report 189 §6.3; read by me; checked by an
  independent agent, which found an error I had missed).** It is a Poincaré–Bendixson argument in
  a collar box around an arc of a line.
  * By Effros and (O), points of the line near the base arc lie on left-to-right *passes* of the
    box (a flow box, at two scales).
  * The region between the base pass and a later thin pass is bounded by a Jordan curve made of a
    vertical segment and an arc of the line.
  * Once the line leaves that region on the right, it never enters it again on the left. This
    contradicts recurrence.
  * It needs no accessibility, no (e) and no (L); the planar inputs are the Jordan curve theorem
    and a cross-cut lemma.
  * The route of the independent check's sketch is kept; Aristotle corrected two of its steps.
  * **Error (found by the second independent check).** The shadow lemma and the flow box are
    stated for the whole box, but hold only in the middle band `X ∈ [¼ + κ, ¾ − κ]`. Near the
    vertical edges a point of the line can lie on a U-turn through one edge rather than on a pass,
    because backtracking up to `2κ` is allowed. Consequently "every point of `ℓ` in `R` lies on a
    pass" fails near the edges. The trapping lemma's `R ∩ J = σ°` is then unsupported, since edge
    U-turns of the line between the two passes can enter `R`, and so are its two-sides and
    frontier steps.
  * A second, minor slip: the neighbourhood `N_o` must be chosen after `P_{m₂}` (I had noticed
    this too).
  * **Repair (the independent check, asked to write it out; checked step by step by me).** The
    shadow lemma and the flow box are stated in the middle band only, with a monotone-shadow
    property (Mon): along a pass, `X` never falls back by `2κ`.
    * The trap is rebuilt in the column `3/8 ≤ X ≤ 5/8`. It uses two low vertical segments and two
      low boxes beside `σ`, all inside the region `R_m` that `rect_domain_aux` gives for the whole
      thin pass.
    * It needs neither `R ∩ J = σ°` nor the decomposition `R ∖ σ = R_L ⊔ R_R`, nor a general
      cross-cut lemma.
    * The last-time argument uses (Mon) to order the crossings of a pass.
    * The choice of the neighbourhood of `o` is moved after the second pass.

    This is commission 190 §2–§6.
  * **Verified (batch 190), in the repaired form.** Passes and (P1)–(P4); the shadow lemma, the
    flow box, scale 2 and late thin passes, in the middle band only; the region of a thin pass and
    Lemma A; the trap (`trap_jordan`, `trap_pass`); the contradiction (`jones75_contra`); the arc
    step `jones75_noArc`. Files `HPC/Jones/Jones75Pass.lean`, `Jones75Shadow.lean`,
    `Jones75Region.lean`, `Jones75Trap.lean`, `Jones75B.lean`. Shape changes (report 190 §0): the
    trap is stated on the low strip `F((3/8, 5/8) × (0, h))` with (H) in a minimality form, and
    `exists_late_thin_pass` gains `η ≤ 1`.
  * **The Theorem (J75.7, repository `LEDGER.md`).** "If M is a homogeneous plane continuum
    containing an arc, then M is a simple closed curve": verified (`bing60_plane_uncond`). The
    printed steps the route replaces are quoted there: accessibility and (e); the choice of `η`
    from (f); `[t_a, t_b]`; the domains `Dᵢ`; `[t_c, t_d]` and the fixed point; the final limit
    argument.
  * **J75.6.** Aristotle records the error in report 189 §6.3 in the repository ledger as well;
    it is not counted (not a published proof).

### A.29 L. G. Oversteegen and E. D. Tymchatyn, *Plane strips and the span of continua, (I)*, Houston J. Math. 8 (1982), 129–142, and H. Cook, *Continua which admit only the identity mapping onto non-degenerate subcontinua*, Fund. Math. 60 (1967), 241–249 (Theorem C; my reading, 2026-10-18)

Read from page images at 200 dpi (O–T: 14 PDF pages, journal pp. 129–142; Cook: p. 243). Role:
Theorem C of Hoehn–Oversteegen is the second sentence of O–T Theorem 3.6; Cook's Theorem 4 is cited
in its proof. Formalized top down in batch 191 (`HPC/Span/`): Theorem 3.6 and Corollary 3.5 are
verified from the named claim `OTThm32`; Cook's Theorem 4 is verified. Aristotle confirmed every
entry below (repository `LEDGER.md`, OT.1–OT.7) and found two more misprints. These entries were put
to Aristotle in commission 191 §9. An independent agent checked them against the images before the
commission went out and refined three of them (the `x_K` entry, the readings of `[0,5/8]`, and the
suppositions of Theorem 3.2).

* **Theorem 3.6 (p. 140), indecomposable case: "Since X is atriodic tree-like": not needed.** The
  reduction it introduces ("we may assume that f is onto and g is either irreducible with respect
  to mapping onto X or g is into") needs only Corollary 3.5 and a Brouwer reduction. So the
  source on p. 139 ("It is known (see Jones [13] and Rogers [20]) that a homogeneous plane
  continuum is either indecomposable and tree-like or ...") is off the path: Rogers 1981 and
  Jones 1969 are not needed for Theorem C. This replaces the remark of A.27 that Rogers 1981 is
  an input as the proof is written.
* **Theorem 3.6: two unargued steps, true.** "Hence there exists an index i and points
  x ∈ f(Cᵢ), y ∈ g(Cᵢ) such that d(x,y) < δ" (some `Kᵢ` is `δ`-dense); "since Z is a proper
  subcontinuum" (from the reduction to "g irreducible or into").
* **Theorem 3.6, decomposable case:** not needed for the classification (Theorem C is applied to
  Jones's elements, which are indecomposable). Not audited.
* **Corollary 3.5 (pp. 139–140).**
  * "Without loss of generality we may suppose x ∈ A ∩ g(C), π₁(A) = [0,1/2] and π₁(X) = [0,1]":
    unargued, and not a scaling: a copy of `A` through the leftmost point may reach as far right
    as `X`. My route: make the point the unique leftmost one (a quadratic shear), move `A` onto it
    by homogeneity, then push a point of `X ∖ A` far to the right by a homeomorphism supported in
    the half-plane minus `A` (connected, by Janiszewski and Hagopian's non-separation).
  * "For each K ∈ 𝒦 we may suppose K ∩ {ε} × R = {x_K}": unargued. Minimality does not give it
    in general (a continuum minimal for meeting both sides of a strip can meet a side in an arc:
    the sin(1/x) continuum with its bar on the side, which is not hereditarily indecomposable).
    Not needed: any `x_K` on the side serves for Effros. O–T may have wanted it for the
    single-point supposition in their proof of Theorem 3.2.
  * The uncountable family `𝒦` of disjoint crossing continua: unargued, true (one in each
    composant).
  * "It is easy to see that there is a continuum B ⊂ X such that [0,5/8] ⊂ π₁(h_K(B)) ⊂ [0,3/4)":
    the first inclusion is impossible as printed, since `h_K(B) ⊂ K ⊂ [ε, 3/4] × R`. Two readings:
    `[ε, 5/8] ⊂ π₁(h_K(B))` for each `K`, or `[0, 5/8] ⊂ π₁(B)`. Only the second gives what
    Theorem 3.2 needs, one `y ∈ B` for all `K`. Either way the existence of `B` is unargued.
    Argument: the continua `h_K⁻¹(K)` all contain `A`, so hereditary indecomposability makes them
    nested; `B` is their intersection, and the one `y` comes from the chain of compacta
    `h_K⁻¹(K) ∩ {x ≥ r − η}`.
  * "an indecomposable homogeneous plane" ("continuum" missing): misprint.
* **Theorem 3.2 (pp. 137–138): its proof is unargued for the images it allows.** It begins: "We may
  suppose that for each λ ∈ Λ h_λ(Y) meets {0} × R in a single point and h_λ(Y) intersects
  {1} × R in at most one point. Hence, ... we may suppose that for each λ ∈ Λ neither h_λ(X) nor
  h_λ(Y) separates the plane. Let δ ∈ Λ. We may suppose that π₁(h_δ(y)) > π₁(h_δ(z)) + 1/2 for
  each z ∈ X. We may also suppose that d(h_λ(z), h_γ(z)) < 1/8 for each z ∈ Y and λ, γ ∈ Λ. The
  proof now proceeds as in Theorem 3.1".
  * The single-point supposition is unargued, and can be avoided but not justified (disjoint
    crossing arcs can each meet a side in two points). The non-separation supposition is correct.
  * The two suppositions about `δ` are not available together: the cluster of maps within `1/8`
    need not contain `δ`, and one rescaling does not fix the other gaps. Repair: fix `n` with
    uncountably many indices having span `≥ 1/n` and gap `> 1/n`, then cluster within `1/(8n)`.
  * The proof of 3.1 picks three images one of which separates the other two in the strip
    (unargued). In Corollary 3.5 the images
  lie in disjoint continua crossing the strip, whose traces on the side are ordered; the named
  claim `OTThm32` of commission 191 adds that hypothesis. Whether the printed 3.2 holds in general
  is not decided.
* **Theorem 3.1 (p. 137):** the approximating arcs `Aᵢ` in the Hilbert cube can be replaced by
  piecewise-linear interpolation along `η`-chains of `Y` (my route).
* **§2 (pp. 131–136), for later batches.**
  * Lemma 2.1's proof is sketched ("The lemma now follows easily"; "it is easy to see"). The
    repository's crossing parity (`parity`, `HPC/Plane/Jct1.lean`) is the lemma in ray-crossing
    form.
  * Theorems 2.6–2.7 use Remark 2.5 (a locally connected `Y ⊃ X` near `X`); `Y` must lie in
    `U ∪ B₀ ∪ B₁`, which is not automatic when `X` meets `B₀` (unstated). A union of grid squares
    in the half-plane serves.
  * Theorem 2.7: "It is easy to see that the first part of Lemma 2.3 is valid even if
    (π₁ ∘ f)⁻¹(b) ≠ 1 ≠ (π₁ ∘ g)⁻¹(b)" can fail: `φ` is discontinuous where the path `h` meets
    a point of `B₁` at which `f` or `g` crosses the inside of `B₁`. Harmless where `h` stays off
    `B₁`, as in Corollary 3.5.
  * Theorem 2.7: "there exists a continuum H in C such that (0,p) ∈ H and H meets both I × {0}
    and I × {1}" does not follow from "the first part of Lemma 2.3", which gives continua from
    bottom to top only; the corner claim is true (unicoherence of the rectangle). "Clearly
    K ∩ H ≠ ∅" needs a crossing argument in the square.
  * Lemma 2.3 and Theorems 2.6–2.7: "the component of U₁ whose boundary meets each of f(I) and
    g(I) in a nondegenerate continuum" presumes uniqueness, and the boundary condition is not
    used (harmless).
* **Theorem 1.1 (Davis), p. 130:** used once, in Corollary 3.5, for a proper subcontinuum of a
  hereditarily indecomposable continuum. There Cook's Theorem 4 gives confluence and the Brouwer
  reduction O–T mention takes ten lines; Davis's paper and the Lelek and Grispolakis–Tymchatyn
  inputs are not needed.
* **Misprints, harmless:** "σ₀(x)" (p. 129); "f(X) ⊃ g(X)" for `f(C) ⊃ g(C)` and "homomorphism"
  (p. 140); "[7]" for Effros, which is [6] (pp. 139, 140). Found by Aristotle (batch 191) and
  checked against the images: "C = {(x,y) ∈ R² | d(B_x,h(y)) = 0}" and the same for `Y` (p. 136,
  proof of Theorem 2.7) for `I²`; "d(h_λ(Z),h_γ(z)) < 1/8" (p. 138, (5) of the proof of
  Theorem 3.3) for `h_λ(z)`.
* **Batch 192 (Aristotle's checks OT.8–OT.13, repository `LEDGER.md`).**
  * Theorem 2.7 (p. 136): "there exists a continuum H in C such that (0,p) ∈ H and H meets both
    I × {0} and I × {1}" and "Clearly, K ∩ H ≠ φ": both unargued, neither found false; replaced
    by `common_zero_rect`. Gaps in exposition.
  * Theorem 2.7, continuity of `φ` when `(π₁ ∘ f)⁻¹(b) ≠ {1}`: confirmed discontinuous where the
    path meets `B₁` at a point `f(t₀)`, `t₀ < 1`. Harmless in every use here.
  * Remark 2.5 and Lemma 2.4: not needed; the locally connected `Y` would have to stay in
    `U ∪ B₀ ∪ B₁`, which is not argued. Gap in exposition.
  * "the component of U₁ whose boundary meets ...": uniqueness presumed, condition unused.
  * Theorem 3.1, the separating triple: unargued; supplied for crossing images by
    `crossing_traces_separated`.
  * **Theorem 3.2: proof defective (the two suppositions about `δ` are not available together),
    statement not decided** (only the strip form `OTThm32` is proved). Not counted: the ledger
    counts a defective proof only once its statement is verified or refuted (as for Whyburn 1939
    Theorem 14 and Hagopian 1976 Theorem 1). Aristotle's argument; I agree.
* **Verified (batch 192).** `ot82_theorem32 : OTThm32`, `crossing_traces_separated`,
  `strip_lemma` (the form of Theorem 2.7 used), `theoremC : TheoremC`. Corollary 3.5 and
  Theorem 3.6 (indecomposable case) are now unconditional.
* **Verified (batch 191).** Theorem 3.6, indecomposable case, from Corollary 3.5
  (`ot82_theorem36_of_cor35`); Corollary 3.5 from `OTThm32` (`ot82_cor35_of_thm32`); Theorem C
  from `OTThm32` (`theoremC_of_thm32`). Davis's Theorem 1.1 for hereditarily indecomposable
  continua (`semiSpanZero_of_spanZero`). The ten-line reduction of §5.2 and the re-embedding of
  Corollary 3.5 are in `HPC/Span/Thm36.lean` and `HPC/Span/Reembed.lean`.
* **Cook, Theorem 4 (p. 243): two unstated steps, true.** The proof takes "a sequence of
  subcontinua of X such that ... C is a proper subcontinuum of Cₙ ... and C is the common part"
  without constructing it (boundary bumping; it does not exist when `C = X`, a case that needs
  no argument); and "The common part of f(C₁), f(C₂), ... is f(C)" (decreasing compacta) is
  unstated. **Verified (batch 191)**, `cook67_theorem4`, by a shorter proof that needs neither
  step: if `q ∈ Q ∖ f(C)`, a closed neighbourhood of `C` missing `f⁻¹(q)` contains, by boundary
  bumping, a continuum larger than `C` whose image misses `q`, hence lies in `Q`.

---

## Part B. Refuted readings and reformulations (not defects of the sources)

### B.1 Readings of printed statements

| reading | certificate | note |
|---|---|---|
| Bing 1948 Theorem 3, end clause read "respectively" (`Theorem3Literal`) | `Recon121.not_theorem3Literal` | False at `k = 3`. Bing's own "or" wording (`Theorem3LiteralOr`) is proved. For `k ≥ 4` the two readings coincide (`endClause_or_iff`). |
| "1951-crooked implies 1948-crooked" | `isCrookedIn_ne_isCrookedIn'` (`Chains/Counterexample.lean`) | The two papers' notions of crookedness differ. Four strips and six rectangles. |
| Bing 1951 Theorem 11, separation read with `K′ ⊇ K − g′ − N` | `not_separation_of_accumulates'` | See A.2.2, sentence 3. |
| Bing 1951 Theorem 8, `g_p` read with one layer (my batch-92 commission) | `Counter92.theorem8_1951_false` | Bing's two-layer `g_p` gives the theorem (`theorem8_1951'`; A.2.1). Counted as a false printed statement until 2026-10-22. |

### B.2 Intermediate conjectures of the Theorem-3 campaign (batches 17–60)

Each of the following was proposed as a route to Theorem 3 and is refuted by an explicit crooked
sequence. Theorem 3 itself is proved (A.1.1).
* `exitReach`, `highExitValleyOpen`, `lowExitPeak`, `highExitValley`, `f2Prime`, and their Tight
  and F forms.
* `exists_cutData` (`CutData` is empty) and `offDichotomy` (basepoint 57 of `bing 0 8`).
* `extendStepMin`, `s3Zig`, `arm_timing`, `unserved_high8`, `unserved_ceiling`,
  `unserved_valley`, `cross_ceil_profile`, `unserved_profile`, `unserved_leg3deep`.
* `f2PrimeOff` is refuted only *conditionally*, under an undischarged faithfulness hypothesis.

The full table is in `LEDGER.md` §1.

### B.3 Models of open questions (reconnaissance)

* The time-ordering fold (batch 86) and the three-link fold (batch 87) for Theorem 14's covering
  step: refuted in the model.
* The end-time lemma for `theorem3_end` (batch 87): refuted in the model.
* None of these is a defect of Bing. The routes actually used are Lehner's (A.1.4) and Bing's
  induction (A.1.1).

### B.4 Duke 1951 questions put by the commissions

* Q-deg: a degenerate interior element (`exists_degenerate_interior_elt_refuted`). The Cantor
  organ has no degenerate element.
* Q3: `bingElt_degenerate_of_isContPt` (`…_refuted`).
* The gluing question `isSnakeLike_union_of_terminal`. Two organs glued along a terminal layer
  form a triod (`…_refuted`, `two_organs_counterexample`).
* `isArc_of_separatesPairs`. The decomposition space of `S₀` is not Hausdorff.
* The converse of `bingElt_subtype_subset`.

---


## Part D. Summary

| source | false as printed | proof defective, statement true | unstated step / unargued | stated without proof | harmless |
|---|---|---|---|---|---|
| Bing 1948 | Thm 4 (m = 3, two ways); Thm 8 | Thm 3 (special case of proof) | Thm 14 (sequences; 2 not-established assertions; 9 omitted steps) | — | — |
| Bing 1951 Duke | — (Thm 8 was listed here until 2026-10-22: my misreading) | — | Thm 7 (tree-like ⇒ no separating subcontinuum); Thm 8 (`K₂` contains `K₄` interiorly; order of the two inclusions); Thm 11 (3 sentences) | — | — |
| Bing 1951 Pacific | — | — | — | — | — |
| Fugate 1966 | — | — | — | Cor 1 (true) | intro vs. Thm 1; Miller and Sorgenfrey citations over-general |
| Fugate 1969 | — | — | Lemma 3 (`R ⊄ K`), plus nine smaller items | — | — |
| Lehner 1961 | — | — | — | — | — |
| Ingram 1968 | — | — | — | — | — |
| van Mill 2004 | — | — | Prop 3.5 (subspace step); Prop 2.2 (tacit `X ≠ ∅`) | — | — |
| Jones 1948 | Thm 10; Thm 6 (both `D = ∅`) | — | Thm 13 (`cl V₂ ⊆ W₁`); Thms 11–13, 19 tacit `D ≠ ∅` | Thms 0, 2, 3, 5 (all proved) | Thm 16 (`P`/`p`) |
| Jones 1951 | — | — | Thm 1 (`M′` homogeneous, aposyndetic, hereditarily unicoherent, has a nonseparating point) | — | "hereditorily" |
| Moore 1916 (F.A.) §§2–5 | Thm 14 (`Mₙ ≠ ∅`); Thms 4, 19 (empty region); p. 139 limit criterion (endpoint) | Thms 10, 15 | connected (nonempty parts) | Thms 1, 3, 7, 11, 13, 16–18; §5 (Lennes) | p. 139 first/last point |
| Moore 1916 (F.A.) §6 | Thm 23 (empty region) | Thm 28 (last step); Thms 33–34 (Kline's gap) | interior of `J` undefined; Thm 31 (`B ≠ C, D`); Thm 32 (`C ∉ AB`) | Thms 20, 22, 30 | Thm 34 ("Jordan arc"); Thm 33 (parenthesis) |
| Moore 1916 (F.A.) §7 | Thm 35 (empty region); Thm 43 (`G = ∅`) | Thm 36 (arc `BC`) | Thm 36 (interior ⊆ `R`); Thms 37, 39 (unargued steps) | Thms 38, 40, 42, 43; Thm 41 last step (all supplied) | — |
| Moore 1919 | Thm C (touching curve) | Thm D | Thm B (five steps); ruling definition; subdivisions; Thm E limit arcs; Fig. 3 nine-cell ruling; Thm G; final paragraph | — | footnote † (`A`, `B` for `X`, `Y`) |
| Moore 1925 §I | Thm 2 (printed complementary domain); Thms 10, 11 (printed closed curve); Thm 7 (misprint) | Thm 11 (`B` an arc); Thm 21 (Axioms 6, 7 via unproved Σ₂ equivalence) | boundary definition; Thm 2 (Brouwer, three steps); Thm 3 (four steps; `p ∈ R` omitted); Thm 8 (two steps); Thm 11 (three steps); Thm 13 (three steps); Thm 14 (sub-curve); Thm 20 | Thms 4, 5, 6, 9, 10, 15–19; p. 420 claim (all supplied) | Thm 1 (two slips); Thm 12 (nonempty domain); Thm 14 (`pxq`); Thm 18 (`x`, `y`) |
| Mullikin 1922 | Thm 5 (separatedness) | — | — | — | Thm 4 (empty intersection, convention) |
| Jones 1949 | Thm 1, Thm 2 (one-point continuum) | — | Case 1 (two steps); Case 2 (four steps); `M` uncountable | — | [8] (9.1 for 9.2); [4] ("a point" for "all points") |
| Whyburn 1942 | — | (9.1) (`N·G` compact) | (9.2) (order in `L`); (8.41) (separating point of `L̄_i`); (8.4) (small interval, not from (3.2)) | (3.1) | (8.3) (constant sequence) |
| Moore 1922 | — | Thm 4 necessity, last step | Thm 4 (five steps; sufficiency, three steps) | — | Thms 1, 3, 4 (slips, misprints); typography |
| Hagopian 1975 | — | — | Lemma 1 (proper triod; disjoint domains; Baire and Moore 138); Thm 1 ¶2 (disjointness; the triod); ¶9 (second inclusion) | — | "transfromation"; Lemma 2 citation (Kuratowski Thm 3 for type A′); ¶13 citation (Jones 1955 Thm 2 implies) |
| Whyburn 1939 §14 | — | Thm 14 (inversion) | Thm 14 (curve `K`; θ step; `C`; `H`); (6.22); fn. 16 (equivalence with Wilder) | Cor 1 (supplied) | Thm 14 (`ou − o`; `3ε`; "there exists") |
| Menger 1932 | — | — | p. 266 (three steps; not used) | — | — |
| Moore 1920 | Thm 4 (one-point set) | — | — | — | — |
| Jones 1955 | — | Thm 1 (case argument: `M₀ ⊆ M₁`; `U_q` for `U_o`) | Thm 1 (residual continuity; (a); `N_o` closed; `d(q)` not established); Thm 2 (Borsuk; disjoint domains; `M − g` connected; `G′` u.s.c.; embedding; aposyndetic case) — Thm 2 verified | closing remarks (three unnumbered claims; verified) | Thm 2 ("[5]" for [3]; `g` for `G`) |
| Hagopian 1976 | — | Thm 1 (the case split fails at the last step `i = 2`; Thm 1 verified by the 1984 route) | Lemmas 4–9 and pp. 343–345 (unargued steps, supplied; Lemma 5's union of two extensions not decided, unused); Thm 1 (about twenty unargued steps, supplied; the end layer of `F` needs 1984 Lemma 7); seven steps of pp. 347–349 not established (1976 route not completed) | — | — |
| Hagopian 1984 | — | — | Lemmas 7–9, 12–16 and Thm 1 (about twenty unargued steps, supplied or avoided; Lemma 15's "By Lemma 3" insufficient as printed; Lemma 16 without normality not decided) | — | `K(Z)`; Lemma 2 for unions (in the plane); misprints |
| Jones 1975 | — | (f) (solenoid); the Theorem (rests on (f) and unargued planar steps) | (c) (argument from (a), (b) unstated); (d), second sentence (orientation) | — | — |
| Cook 1967 | — | — | Thm 4 (the sequence `Cₙ`; `⋂ f(Cₙ) = f(C)`) | — | — |
| Oversteegen–Tymchatyn 1982 | — | — (Thm 3.2: proof defective, statement not decided; not counted) | Thm 3.6 (tree-likeness cited, unused; two steps); Cor 3.5 (normalization; `x_K`; `𝒦`; `B`); Thm 3.1 (separating triple; single points); Thm 2.7 (`H ∋ (0,p)`; `K ∩ H`); Rem 2.5; Lem 2.1 (sketch) | — | `σ₀(x)`; `f(X) ⊃ g(X)`; "homomorphism"; "[7]" for [6]; `R²` for `I²`; `h_λ(Z)`; "[0,5/8] ⊂ π₁(h_K(B))" |
| Krasinkiewicz–Minc 1977 | — | — | — | — | — |
| Lelek 1979 (announcement; not used) | — | — | Cor 9 (`dim X ≤ 1` dropped); Cor 10 (one-paragraph sketch through [4], [3], [1]) | Props 1–4, Lemma 5, Thm 6 | — |
| Hoehn–Oversteegen 2016 (Thm 1 verified, batch 197) | Thm 1′ (one-point continuum; certificate, batch 194) | Prop 19 (p. 208, (S4′) step false; certificate `ho16_p208_false`) | Thm 8 (disjoint fans); Thm 1 proof (`d_H(X, T) < δ`); pp. 185–186 (fold well defined; existence verified in another form); Prop 7 (three steps, supplied); p. 190 observations (verified); Prop 10 (second part: "x∈B" needs `∂C′ ∩ B ≠ ∅`; `∂C ⊆ B` unstated); Prop 11 (three steps); Prop 17 (`k ≥ 3`; "easy to verify"); Lemma 18 (regularity); pp. 202–203 (citations); Thm 15 (Claim 15.1 left to the reader; the irreducible subset; branch-point surgery; (3) cited for a point of `T`; `b ∈ J_j` not excluded; the (S4) case split); Prop 19 and Thm 20 (pp. 203–210, unargued steps, supplied) | Lemma 6 (verified) | Thm 1 restated on p. 211 ("non-degenerate" dropped); Thm 8 (3) ⇒ (1) (`U`, `V` interchanged); p. 195 (`x` for `(x, y)`); p. 198 (`aᵢ`); p. 202 (`∩` for `∪`; "a straight"); pp. 205–207 (`φ⁻¹`, three times; p. 205 `P′₁∩(∂F₃)⋆=φ⋆⁻¹(γ)`); p. 209 (order of composition); pp. 193–194 ("G connected" omitted; certificate); p. 192 ("comple ment"); p. 198 (`{z}_*`); p. 210 (says more than p. 201) |
| Bing–Jones 1959 (Thms 1–10 verified, batches 198–201; §7's claim by another construction, batch 202) | Thm 5 (degenerate and general certificates verified); Thm 7, second sentence (`n ≤ 2`; certificate for `n = 1`) | Thm 7 (the printed `D′` cannot exist for `n = 3`, certificate verified; `n ≤ 2` not treated). Not counted: Thm 3 (the chain `D` fails at two junctions), Thm 8 (the printed `e_k` need not form a chain; argued), Thm 9 (`E′` need not be a chain for Bing–Jones's `ε`); one-line repairs, verified | pp. 173, 189 (passage to circles; supplied from Thm 10); Thm 7 (special case `A ⊂ e₁`; crooked sequence from `D`; `P·(d₁ − d₂) ≠ ∅`; `r < s`; supplied); Thm 2 (`G(b, c)` meets `d_t`; supplied); Thm 3 (`D` an ε-chain; supplied); Thm 8 (`U_A`, `U_B`, for continuous arcs; the cover `U₁, …, U_t`; the general case; supplied); corollary to Thm 8 (three consecutive links; supplied); Thm 9 ("⊂ē_i"; the homeomorphism by analogy; supplied); Thm 10 (Step 1(b); "Of course" on p. 188; Step 2(b), the map `R_{i/n}`; Step 2(c), Theorem 6 without naming `E`, and the transition set for the repaired Theorem 5; Step 2(i), Theorem 9's hypothesis; p. 188, closures; Steps 3, 4, 5, ⋯ by analogy; all supplied); §7 (a sketch: the chains `D_i` not constructed; disjointness, filling and continuity of `G` unargued; the pseudo-arc step from (9) not established; the claim verified by another construction) | — | p. 172 (`of` for `if`); p. 173 (`of` for `are`); Thm 3 (`F(v, m)` for `F(w, m)`); Thm 7 (`components`); Thm 8 (`d₂` for `d_n`); Thm 9 (`G` for `F`; `e` for `d`); p. 181 (`E_i`, `H₂`, `d¹_k`); p. 182 (`K₃`); p. 185 (two indices); p. 186 (`E_k`); p. 187 ("intesects"); p. 178, corollary (`4i+1, …, 4i+4` for `4i−3, …, 4i`); p. 187 (`E₁` for `D₁`; `f_{i+1}` for `f_{t+1}`; condition (1) for the whole link); p. 188 (`H_i(d_k^{i+1})`); p. 189 (`4/2^i`); p. 191 (figure: level written second; `a₁`, `c₁` for `a_i`, `c_i`); pp. 190–191 (`G` twice) |

Twenty-three printed statements are false (twenty-four until 2026-10-22):
* Bing 1948 Theorems 4 (m = 3) and 8;
* Jones 1948 Theorems 6 and 10;
* Moore 1916 Theorems 4, 14, 19, 23, 35 and 43, and the limit-point criterion of p. 139;
* Moore 1919 Theorem C (a genuine configuration, not a degenerate case);
* Moore 1920 Theorem 4 (one-point set);
* Moore 1925 Theorems 2, 10 and 11 (under the printed definitions of complementary domain and simple
  closed curve: genuine configurations) and Theorem 7 (a misprint, `p` for `x`);
* Mullikin 1922 Theorem 5 (unseparated `K₁`, `K₂`: a genuine configuration);
* Jones 1949 Theorems 1 and 2 (one-point continuum);
* Hoehn–Oversteegen 2016 Theorem 1′ (p. 212; one-point continuum);
* Bing–Jones 1959 Theorem 5 (pp. 175–176; verified at point fibres, and from every instance with
  three or more links by merging the last two: `bj_theorem5_printed_false_general`);
* Bing–Jones 1959 Theorem 7, second sentence (p. 177; chains of one or two links; verified for one).

The Jones (1948, 1949), Moore 1916, Moore 1920 and Hoehn–Oversteegen failures, and Bing–Jones
Theorem 7's, are at degenerate cases (empty sets, endpoints, one point, chains of one link).
Bing–Jones Theorem 5 fails in every instance with three or more links; I know of no unconditional
instance with non-degenerate fibres (the halves of a circle of pseudo-arcs would give one, under
`BJPlaneExample`). Every intended reading is proved. Eighteen published
proofs fail while their statements are true (until the batch-190 audit the count of sixteen had a
list of fifteen items):
* Bing 1948 Theorem 3;
* Jones 1955 Theorem 1 (the case argument of pp. 737–738);
* Moore 1916 Theorems 10, 15, 28, 33–34 (Kline's proof, counted once) and 36;
* Moore 1919 Theorem D;
* Moore 1925 Theorem 11 (`B` asserted to be an arc);
* Moore 1925 Theorem 21 (Axioms 6 and 7 through Moore 1919 for Σ₂, which rests on F.A.'s unproved
  equivalence of Σ₁ and Σ₂);
* Whyburn 1942 (9.1) (boundary bumping applied to a set not known to be compact);
* Moore 1922 Theorem 4, necessity (the final contradiction is drawn for points of `R`, not `M`);
* Whyburn 1939 Theorem 14 (reduction to a bounded domain by an inversion that need not exist);
* Jones 1975 (f) (the last inference ignores where the image arc runs; the dyadic solenoid satisfies
  everything the proof uses and violates the conclusion; true for plane continua only vacuously);
* Jones 1975, the Theorem (rests on (f), and on unargued planar steps; A.28);
* Hagopian 1976 Theorem 1 (the case split fails at the last step of the induction, with a verified
  certificate; the statement is verified by the 1984 route; A.23);
* Hoehn–Oversteegen 2016 Proposition 19 (p. 208: "∂D̃∩π(α_{i₀})=∅ by (S6′)" is false for a
  component of the fold, with a verified certificate; the proposition is verified with a case
  split; A.26);
* Bing–Jones 1959 Theorem 7 (p. 177: the reduction to a chain `D′` cannot be carried out for
  chains of three links, with a verified certificate, `bj_theorem7_proof_n3`, and chains of one or
  two links are not treated; the theorem is verified by another route; A.25).

**Severity (my judgment, 2026-10-22, in answer to David).** The counts treat every failure alike.
Sorted by what fails:
* *False statements, 23.*
  * Degenerate cases, 15. Empty sets: Jones 1948 Theorems 6 and 10; Moore 1916 Theorems 4, 14,
    19, 23, 35 and 43. An endpoint: Moore 1916, p. 139. One point: Moore 1920 Theorem 4; Jones
    1949 Theorems 1 and 2; Hoehn–Oversteegen Theorem 1′. Short chains: Bing 1948 Theorem 4 at
    `m = 3` (the case Bing calls "easily established"); Bing–Jones Theorem 7, second sentence.
  * Wording, 5. A definition or hypothesis says less than the author meant, and a configuration
    the author did not have in mind refutes it: Moore 1925 Theorems 2, 10 and 11 (the definitions
    of complementary domain and simple closed curve) and Theorem 7 (a misprint); Mullikin 1922
    Theorem 5 ("mutually exclusive" for "mutually separated").
  * Genuine, 3. Bing 1948 Theorem 8 (the unions of corresponding links need not form a chain;
    Theorem 9's proof uses it). Moore 1919 Theorem C (a curve touching a side from within; the
    proof of Theorem D applies C to such a curve). Bing–Jones Theorem 5 (fails in every instance
    with three or more links; its one use is existential, so Theorem 10 is unaffected).
* *Defective proofs, 18.*
  * Local, 10. A step fails and a short argument repairs it in place: Moore 1916 Theorems 10, 15,
    28, 33–34 and 36; Moore 1925 Theorem 11; Moore 1922 Theorem 4; Whyburn 1942 (9.1);
    Hoehn–Oversteegen Proposition 19 (the false sentence concerns components that p. 209
    discards); Bing–Jones Theorem 7 (the reduction works for `n ≥ 4`; the short chains need
    another construction).
  * The argument does not go through, 8. Bing 1948 Theorem 3 (the special case; the repair
    changes three things and took about seventy batches). Jones 1955 Theorem 1 (uses (b) before it
    is available). Moore 1919 Theorem D (applies the false Theorem C, and its induction presupposes
    D). Moore 1925 Theorem 21 (rests on an equivalence nobody proved). Whyburn 1939 Theorem 14
    (the inversion does not exist when `M` has no bounded complementary domain, which is the case
    of every non-separating `M`). Jones 1975 (f) and the Theorem (the dyadic solenoid satisfies
    everything the proof of (f) uses). Hagopian 1976 Theorem 1 (the case split fails at the last
    step, and seven steps of the route are not established; verified by the 1984 route).
* *Not counted.* The most serious gaps are in neither count. First among them is
  Hoehn–Oversteegen's own Theorem 2 (p. 180): the step from Jones's decomposition with pseudo-arc
  fibres to the circle of pseudo-arcs (circle-likeness) is used without proof or citation, was
  unproved in print when they wrote (Lewis 1985, p. 93: "We still do not know in general whether
  M̂ is unique"), and its first proof found is Domokos–Prajs's 2022 preprint, Theorem 6.1 (A.26,
  A.27). Then:
  Bing–Jones §7 (the plane circle of pseudo-arcs is a sketch whose pseudo-arc step is not
  established; my construction replaces it, batch 202); Hagopian 1976 pp. 347–349; and Bing 1948
  Theorem 14 (two assertions not established for an arbitrary description; Lehner's description
  supplies them).

**Census (batch 203).** The joint closure of `ho16_classification_plane₄` and
`ho16_classification₄` uses 4689 of the library's 11697 counted declarations, in 446 of 863
modules; its 12480 library constants are all accepted when replayed through the kernel into an
environment built from Mathlib, `Init` and Batteries alone, and the replayed types equal the
statements of `BJ59E.lean`. My own breadth-first search over `nodes.tsv` and the two edge files
agrees in every count (closure 17643 constants, 4689 used, per-module counts). Whether the formal
proof uses the verified form of each counted defect:
* *Used:* Hagopian 1976 Theorem 1 (by the 1984 route), Jones 1975's arc step (`jones75_noArc`),
  Jones 1955 Theorem 1, Moore 1919 Theorem D, Whyburn 1939 Theorem 14, Moore 1925 Theorems 2, 10,
  11 and 21, Whyburn (9.1), Hoehn–Oversteegen Proposition 19, Moore 1916 Theorems 4, 19, 28, 33, 35
  and 36, Mullikin Theorem 5, Jones 1949 Theorem 1, Moore 1920 Theorem 4 (`circle_char`),
  Bing–Jones Theorem 5 (repaired) and Theorem 7's second sentence (`bj_theorem7_ends'`).
* *Not used:* Bing 1948 Theorems 3, 4, 8 and 9 (all of `HPC/Fold` beyond definitions and the
  greedy zigzag), Bing–Jones Theorem 7's first sentence (`bj_theorem7`), Moore 1916 Theorems 10, 14,
  15, 23, 34 and 43, Moore 1919 Theorem C's corrected forms, Moore 1922 Theorem 4, Moore 1925
  Theorem 7, Jones 1948 Theorems 6 and 10, Jones 1949 Theorem 2.
* The formal route differs from the published one in places. It does not use Bing 1948
  Theorems 3–9 or 13–15 (`HPC/Fold` and `HPC/PseudoArc` are mostly unused), Bing 1951 (Duke)
  Theorems 8, 9, 11 or 12, or Hagopian 1976's own proof of Theorem 1.
