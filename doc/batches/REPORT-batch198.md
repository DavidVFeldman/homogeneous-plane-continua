Commission read: `doc/batches/COMMISSION-batch198.md` ("Commission: batch 198 — Part G, I: the circle of pseudo-arcs (Bing–Jones 1959), top down").

# Report, batch 198

## 0. Summary, omissions, shape changes

**Every theorem of the skeleton is proved, the stretch `bj_theorem5` included.** Bing–Jones's
Theorem 5 as printed is refuted (`bj_theorem5_printed_false`). The three named inputs `BJThm10`,
`HOCircleLike`, `BJPlaneExample` are stated and not attempted, as commissioned. All 120 new theorems
of the batch, and the reused `HPC.Plane.isUnicoherent_of_isSnakeLike`, depend on exactly
`[propext, Classical.choice, Quot.sound]` (`doc/batches/audits/axioms-batch198.txt`); `sorryAx`
occurs in none.

```
STATUS: isHomogeneous_circle proved
STATUS: isPseudoArc_Lset proved (unconditional)
STATUS: isHomogeneous_of_isCircleOfPA proved (from BJThm10)
STATUS: homeomorph_of_isCircleOfPA proved (from BJThm10)
STATUS: circle_or_circleOfPA_of_decomposable proved (from HOCircleLike)
STATUS: ho16_classification proved (from BJThm10, HOCircleLike)
STATUS: ho16_classification_plane proved (from BJThm10, HOCircleLike, BJPlaneExample)
STATUS: bj_theorem2 proved
STATUS: bj_theorem3 proved
STATUS: bj_theorem4 proved
STATUS: bj_theorem5 proved (repaired form, stretch)
STATUS: bj_theorem5_printed_false proved
STATUS: bj_theorem6 proved
STATUS: BJThm10 open (named Prop; not commissioned in this batch)
STATUS: HOCircleLike open (named Prop; not commissioned; no source in hand)
STATUS: BJPlaneExample open (named Prop; not commissioned)
```

**Files.** The skeleton (`doc/batches/skeletons/BJ59A.lean`, byte-identical to the uploaded
`BJ59A.lean`; the commission is copied to `doc/batches/COMMISSION-batch198.md`, the source to
`doc/sources/bing-jones1959.pdf`, both byte-identical to the uploads) is split under `HPC/BJ59/`:

* `Defs.lean`: the skeleton's §§2–3 (definitions and named inputs), verbatim;
* `Order.lean`: the combinatorial core of Theorem 2 (`order_core`);
* `ChainOps.lean`: restriction, merging the last link, concatenation of chains;
* `Arc.lean`: connectedness of `G(a, b)`, Theorem 2 (`theorem2_arc`), Theorem 4 from a chain;
* `Thm3Assembly.lean`, `Thm3.lean`: the repaired chain of Theorem 3 (`chain_assembly`,
  `theorem3_arc`);
* `Thm5.lean`: Theorem 5 repaired (`theorem5_repaired`);
* `Thm56.lean`: the sign lemma for chain maps (`sign_persist`) and the degenerate examples;
* `Transfer.lean`: snake-likeness and pseudo-arcs pass along homeomorphisms;
* `Halves.lean`, `Glue.lean`, `Homog.lean`: §4;
* `CircleFacts.lean`, `Decomp.lean`: §5's library facts;
* `BJ59A.lean`: the skeleton's theorems of §§4–6;
* `NonVac198.lean`: non-vacuity (§8).

`HPC.lean` ends with `import HPC.BJ59.BJ59A` and `import HPC.BJ59.NonVac198`. `lake build HPC`
succeeds. No file of `HPC/BJ59/` contains `sorry`, `admit` or `axiom`.

**Statements.** Every declaration of the skeleton is textually the skeleton's (the definitions and
named `Prop`s moved to `Defs.lean` so that the library files can use them). No shape was changed.
Hypotheses that the proofs do not use, kept because they are in the skeleton:
* `bj_theorem2`: `hS` (snake-likeness), `h0a` (`0 < a`) and `hd1` (`d < 1`) are not used; Theorem 2
  holds for every arc of continua with `a < b < c < d`.
* `bj_theorem5`: `hE` (`E` covers `X`) and `hUE` (`Ū` in a link) are not used.

**Omissions** (optional items): `¬ IsSnakeLike univ` for a circle of pseudo-arcs (§2), and the
general certificate for Theorem 5 as a lemma (§6; given in prose, `LEDGER.md` BJ.5).

## 1. §§2–3: definitions and the named inputs; tests on degenerate inputs

The definitions `IsArcOfContinua`, `IsContArcPA`, `IsCircleOfPA`, `IsChainMap` and the named `Prop`s
`BJThm10`, `HOCircleLike`, `BJPlaneExample` are the skeleton's.

* `BJThm10`. `IsContArcPA f` makes `f` surjective onto `[0, 1]`, so `X ≠ ∅`, and each fibre a
  pseudo-arc, which in the library is non-degenerate (`IsPseudoArc` includes `Nontrivial`). So the
  degenerate case `X = [0, 1]`, `f = id` does not meet the hypotheses (it would, and harmlessly, if
  points counted as pseudo-arcs: then `f` is a homeomorphism and `H = g⁻¹ ∘ f` works). I see no
  refutation as stated; the statement is the fibre-preserving form of Bing–Jones's last sentence,
  with arbitrary end homeomorphisms (any two pseudo-arcs are homeomorphic, so they exist).
* `HOCircleLike`. A point is not decomposable, and `ConnectedSpace` excludes `∅`, as expected. The
  library's `IsCircleLike` omits "nonsnake-like", so this is weaker than Bing–Jones's
  circle-likeness; it is what the classification needs. The circle meets the hypotheses
  (`nonvac_plane_circle`) and is circle-like. No refutation in sight.
* `BJPlaneExample`. An existence statement; nothing degenerate to test.

## 2. §5, unconditional items

* `isHomogeneous_circle`: left multiplication (`Homeomorph.mulLeft`).
* `isPseudoArc_Lset`: as sketched — `jones55_theorem2'` gives each `Lset x` connected and homogeneous,
  `jones55_elements_indecomposable'` indecomposable, `isClosed_Lset` compact; the image in `Pt` is a
  pseudo-arc by `isPseudoArc_of_indec_homogeneous ho16_theorem20`, transferred back along the
  embedding (`isPseudoArc_of_homeomorph`, `Transfer.lean`, which shows that snake-likeness and
  hereditary indecomposability are invariant under homeomorphisms between subsets of metric spaces,
  through the `ε`-map criterion and Tietze).

## 3. §4: homogeneity and uniqueness from Theorem 10

* **Halves** (`Halves.lean`): for `IsCircPAMap f` (a bundled form of the second half of
  `IsCircleOfPA`, `isCircleOfPA_iff`) and `s = ±1`, `halfSet f s = f⁻¹(A_s)` with
  `A_s = {exp(sπt) : t ∈ [0, 1]}`, and `halfMap f hs : halfSet f s → [0, 1]`. Proved:
  `isContArcPA_halfMap` (openness from the restriction of an open map to a full preimage; the fibres
  are those of `f`, transferred to the subtype) and `isSnakeLike_halfSet` (a proper subcontinuum of
  the circle-like `X`, Nadler 12.51 `isSnakeLike_of_subset_circleLike`; it misses the fibre over a
  point of the open complementary arc, `exists_not_mem_range_halfC`). End fibres: over `1` and
  `−1 = exp π`.
* **Gluing** (`Glue.lean`, `exists_homeomorph_glue`): `BJThm10` on the upper halves and on the lower
  halves with the same end maps; the two homeomorphisms agree on the two cut fibres and glue along
  the closed cover by the halves; a continuous bijection of compact Hausdorff spaces. Hence
  `homeomorph_of_isCircleOfPA`.
* **Homogeneity** (`Homog.lean`): **a simpler route than the commission's**: instead of cutting the
  target at `w`, `−w`, rotate the map. For `x`, `y` put `f₁ = f(x)⁻¹·f` and `f₂ = f(y)⁻¹·f`; both are
  circle-of-pseudo-arc maps (`IsCircPAMap.mul_left`) with `x` and `y` over `1`. Glue a homeomorphism
  of the fibres over `1` taking `x` to `y` (`theorem1_HIC'` composed with
  `homogeneous_of_isPseudoArc`) with any homeomorphism over `−1`. Hence
  `isHomogeneous_of_isCircleOfPA`.

## 4. §5, the rest

* `circle_or_circleOfPA_of_decomposable` (`Decomp.lean`, `circle_or_circPAMap_of_decomposable`).
  **Route change:** the dichotomy is taken from aposyndesis rather than from homogeneity of the
  `Lset`s. If `M` is aposyndetic, every `Lset x` is `{x}` (`Lset_eq_singleton_of_isAposyndetic`), the
  quotient map followed by the homeomorphism onto `Circle` given by `jones55_theorem2'` is a
  continuous bijection, hence a homeomorphism. Otherwise every `Lset x` is non-degenerate
  (`jones55_elements`), so a pseudo-arc (`isPseudoArc_Lset`). **Openness**: the quotient map of a
  continuous decomposition is open (`isOpenMap_quotient_mk_of_continuous`, proved here from the
  lower semicontinuity clause of the library's `IsContinuousDecomp`: the saturation of an open set is
  open). `HOCircleLike` supplies circle-likeness.
* `ho16_classification`: forward from `ho16_indec_homogeneous_iff` and the previous item; backward
  from `isHomogeneous_circle` with `IsHomogeneous.of_homeomorph`, `ho16_pseudoArc_indec_homogeneous`,
  and `isHomogeneous_of_isCircleOfPA`.
* `ho16_classification_plane`: `C₁` from `exists_plane_circle`, `C₂` from `isPseudoArc_plane`, `C₃`
  from `BJPlaneExample`. Distinctness:
  * `C₁ ≄ C₂`, `C₂ ≄ C₃`: the circle and a circle of pseudo-arcs are decomposable
    (`isDecomposableSpace_circle`, `isDecomposableSpace_of_isCircPAMap`: the two halves), the
    pseudo-arc is not;
  * `C₁ ≄ C₃`: **route change** — instead of "proper subcontinua of the circle are arcs", the image of
    the fibre over `1` would be a pseudo-arc that is a proper subset of the circle (it misses the image
    of a point over `exp π`), and no proper subset of the circle is a pseudo-arc
    (`not_isPseudoArc_of_ne_univ_circle`: cut the circle at a missing point and embed in `ℝ`, where a
    non-degenerate continuum is an interval, which is not hereditarily indecomposable).

## 5. §6: Bing–Jones §§3–4

* **Theorem 1**: `HPC.Plane.isUnicoherent_of_isSnakeLike`, added to the audit and the ledger.
* **Theorem 2** (`bj_theorem2`, from `theorem2_arc` and `order_core`): the missing step is supplied as
  the commission suggests (`LEDGER.md` BJ.3). The proof needs neither snake-likeness nor `0 < a`,
  `d < 1`.
* **Theorem 3** (`bj_theorem3`, from `theorem3_arc`): Bing–Jones's construction with the chain
  repaired at both junctions by merging `f_{v+1}` into the last `A`-link and `f_{w−1}` into the first
  `B`-link (`chain_assembly`; `LEDGER.md` BJ.4). The `F(v, m)` misprint is confirmed at 400 dpi.
* **Theorem 4** (`bj_theorem4`): Bing–Jones's proof — a Theorem-3 chain of mesh below
  `ρ(p, G − U)`, a link `d_i ∋ p` inside `U`, and the separation by the links before and after it
  (`theorem4_of_chain`, `theorem4_explicit`).
* **Theorem 6** (`bj_theorem6`): on indices; if `H₁ − H₂` never has absolute value `≤ 1`, its sign is
  constant along the chain (`sign_persist`); if `H₁ − H₂ ≥ 2` everywhere, then at the link `H₂` sends
  to index `m − 2` the map `H₁` would reach index `m`, and symmetrically; a contradiction.
* **Theorem 5**: refuted as printed (`bj_theorem5_printed_false`, the degenerate example) and proved in
  the repaired form (`bj_theorem5`, from `theorem5_repaired`, `Thm5.lean`) by the commission's route
  with topological limits superior (`HPC.T13.limSup`, batch 81) in place of Hausdorff limits:
  separations `A_k`, `B_k` from Theorem-3 chains `D_k` of mesh `→ 0`; on failure at `t_k` with links
  `α`, `β` fixed along a subsequence and `t_k → c`, the parts `P_k`, `Q_k` of the fibres are
  `δ_k`-chained with `p` added (`chainedAt_union_point`), so their limits superior are continua
  (`isPreconnected_limSup`) in `g_c` (continuity of `f`) covering `g_c` (openness of `f`,
  `fibre_subset_limSup_union`); one of them is `g_c` (indecomposability); `hEU` gives a point of
  `g_c ∩ e_α` off `Ū`, near which some `P_k` meets `e_α` off `U`: a contradiction. The general
  non-degenerate counterexample to the printed statement is recorded in prose (`LEDGER.md` BJ.5); the
  optional lemma producing it from an arbitrary instance was not written.

## 6. Non-vacuity (`NonVac198.lean`)

* `bj_theorem2`–`bj_theorem4`: `X = [0, 1]`, `f = id` (`nonvac_arc_id`), with the theorems applied
  (`nonvac_bj_theorem2` with `a, b, c, d = 1/5, 2/5, 3/5, 4/5`; `nonvac_bj_theorem3` with
  `ε = 1/10`; `nonvac_bj_theorem4` with `U = (1/4, 3/4)`).
* `bj_theorem6`: `n = m = 3`, the constant map onto the middle link and the identity
  (`nonvac_bj_theorem6`).
* `circle_or_circleOfPA_of_decomposable`, `ho16_classification`: a plane circle is compact,
  connected, non-degenerate, homogeneous and decomposable (`nonvac_plane_circle`).
* `BJThm10`: its hypotheses are met by the two halves of any circle of pseudo-arcs
  (`nonvac_bjThm10_halves`), hence under `BJPlaneExample`; no unconditional example.
* `isPseudoArc_Lset`: no witness. A witness needs a decomposable homogeneous plane continuum that is
  not aposyndetic; under `BJPlaneExample` and `BJThm10` the plane circle of pseudo-arcs `C₃` is
  homogeneous and decomposable, and it is not aposyndetic since its fibres are non-degenerate
  terminal subcontinua; identifying its Jones elements with its fibres needs that terminality
  (`jones55_c`) or a direct argument. Not formalized.
* `bj_theorem5` (repaired): point fibres cannot satisfy `hE` and `hEU` with `U ≠ ∅`
  (`bj_theorem5_hyps_fail_id`); the hypotheses of the core `theorem5_repaired` are met only
  degenerately (`nonvac_theorem5_repaired_degenerate`, the chain with no links). A real witness needs
  non-degenerate indecomposable fibres (the halves of a circle of pseudo-arcs with `U` small, so under
  `BJPlaneExample`). No simple unconditional example found.
* Named `Prop`s on degenerate inputs: §1 above.

## 7. Ledger

New section "Bing–Jones 1959 (batch 198)" in `LEDGER.md`, items BJ.1–BJ.16, each quoted from the
page images. The commission's second reading is confirmed in every item; I checked items 1, 3, 4, 6,
7, 8, 9, 10, 11, 12, 14 on 400-dpi crops and the others against 200-dpi pages and the text. One
addition: in BJ.16, Theorems 2, 4, 5, 6 hold a fortiori for Bing–Jones's chains, but Theorem 3
produces a chain only in the library's sense.

**Counting.** I would count BJ.5 (Theorem 5) as the twenty-third false printed statement: it is false
for non-degenerate indecomposable fibres (the merged-links construction), not only for points. BJ.4
(the chain of Theorem 3 is not a chain) is a defective construction with a one-line repair; I would
not count it, as HO.15 and HO.23. Nothing is counted until you decide: the counts stay at 22 and 17.

## 8. Axioms

`doc/batches/audits/axioms-batch198.txt`: 120 new theorems and `isUnicoherent_of_isSnakeLike`, all on
`[propext, Classical.choice, Quot.sound]`. `axioms.txt` is regenerated from `Axioms.lean` (new group
"Bing–Jones 1959, I (batch 198)") after a full `lake build HPC`: 3507 lines (3385 before; the first
3385 lines are unchanged and the last 122 are the batch-198 audit); `sorryAx` occurs in no line.

## 9. Dependency map of `ho16_classification_plane`

```
ho16_classification_plane  [BJThm10, HOCircleLike, BJPlaneExample]
├─ exists_plane_circle, isPseudoArc_plane, BJPlaneExample
├─ isHomogeneous_circle (mulLeft); homogeneous_of_isPseudoArc (Bing 1951)
├─ isHomogeneous_of_isCircleOfPA ── isHomogeneous_of_isCircPAMap  [BJThm10]
│    ├─ IsCircPAMap.mul_left; theorem1_HIC' (Bing 1951); homogeneous_of_isPseudoArc
│    └─ exists_homeomorph_glue ── exists_half_homeomorph  [BJThm10]
│         ├─ isContArcPA_halfMap (open maps restricted to full preimages)
│         └─ isSnakeLike_halfSet ── isSnakeLike_of_subset_circleLike (Nadler 12.51, batch 132),
│                                    isSnakeLike_univ_of_isSnakeLike (Transfer)
├─ homeomorph_of_isCircleOfPA ── homeomorph_of_isCircPAMap ── exists_homeomorph_glue, theorem1_HIC'
├─ distinctness: isDecomposableSpace_circle, isDecomposableSpace_of_isCircPAMap,
│    not_isDecomposableSpace_of_isIndecomposable_univ, not_isPseudoArc_of_ne_univ_circle,
│    isPseudoArc_of_homeomorph (Transfer)
└─ ho16_classification  [BJThm10, HOCircleLike]
     ├─ ho16_indec_homogeneous_iff (batch 197), ho16_pseudoArc_indec_homogeneous
     └─ circle_or_circleOfPA_of_decomposable ── circle_or_circPAMap_of_decomposable  [HOCircleLike]
          ├─ jones55_theorem2' (Jones 1955 Theorem 2), Lset_eq_singleton_of_isAposyndetic,
          │    jones55_elements
          ├─ isOpenMap_quotient_mk_of_continuous
          └─ isPseudoArc_Lset' ── ho16_theorem20 (batch 197), isPseudoArc_of_indec_homogeneous,
                                   jones55_elements_indecomposable', isPseudoArc_of_homeomorph
```

## 10. The three named inputs

* **`BJThm10`** needs Bing–Jones §§5–6: Theorems 7, 8, 9 (homeomorphisms of pseudo-arcs following
  chain maps, with end conditions), the construction of pp. 182–189 (four steps, the last ones by
  analogy, BJ.13), and Theorem 5 in the repaired form (now available). It also needs a bridge
  between the library's chains and chains whose nonadjacent links have disjoint closures (BJ.16):
  Theorem 3 should be strengthened to produce such chains. Bing–Jones's reference [3] is Bing 1948
  (*A homogeneous indecomposable plane continuum*, Duke), whose Theorems 1–15 the library
  formalizes; Bing–Jones cite its Theorems 6, 11 and 13 and its patterns. Which library statements
  match those citations is to be checked when Theorems 7–10 are commissioned.
* **`HOCircleLike`**: nothing in Bing–Jones. What the library has: Jones's decomposition with
  continuity, its elements terminal (`jones55_c`), indecomposable and pseudo-arcs
  (`isPseudoArc_Lset`), the quotient a circle, circle-likeness and Nadler 12.51 (batch 132), and
  `isOpenMap_quotient_mk_of_continuous`. Missing: the passage from "open map onto the circle with
  terminal pseudo-arc fibres" to circle-likeness (the expected source is Lewis 1985). Prajs 2000 shows
  terminality must be used.
* **`BJPlaneExample`** needs the full construction of §7: the circular chains `D_i` with (1)–(9),
  that `M = ⋂ D*_i` is not snake-like, that the irreducible subcontinua from `W₁` to `W₂` form a
  continuous decomposition over a circle, and that each is a pseudo-arc (by crookedness, Bing 1951);
  circle-likeness of `M` follows from (1)–(3).

## 11. Delivery

`doc/batches/batch198-files.tar.gz` (every file added or changed in this batch, the commission and
skeleton copies and the new source included) and `doc/batches/batch198-MANIFEST.txt`.
