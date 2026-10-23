Commission read: `doc/batches/COMMISSION-batch196.md` ("Commission: batch 196 — H–O Theorem 1, IV: Proposition 19; Theorem 20 from Theorem 15").

# Report, batch 196

## 0. Summary, omissions, shape changes

**Every item of commission §2–§5 is proved, including the stretch items of §5.** Nothing is
refuted apart from the certificate of §4, which refutes a sentence on p. 208 of H–O's proof, as the
commission asked. Nothing is commented out. After this batch the only open input of
`homeomorph_pseudoArc_of_indec_homogeneous_of_thm15` is `HOThm15` (H–O Theorem 15), as planned in
commission §1.

The skeleton `doc/batches/skeletons/HO16D.lean` (a copy of the uploaded `HO16D.lean`, byte-identical;
the commission is copied to `doc/batches/COMMISSION-batch196.md`) is split over files under
`HPC/HO16/`:

* `P19Defs.lean`: the skeleton's definitions `p19T`, `p19α`, `HOThm15`, and the new named `Prop`
  `HOProp19` (see shape changes);
* `OrdFold.lean`: §2, `IsSimpleFoldOf.isOrdinaryPt_iff`;
* `P19Lib.lean` (preimages under `φ⋆`, `foldPre` lemmas, consistent complements pulled back),
  `P19Ctx.lean` (the hypotheses bundled as a structure `P19` and the basic facts about the fold),
  `Prop19A.lean` (straightness and end sets), `Prop19B.lean` (level `i₀`), `Prop19C.lean`
  (images, (S3′), (S5′), (S6′)), `Prop19D.lean` ((S4′)), `Prop19.lean` (assembly):
  §3, `ho16_prop19_full`;
* `Prop19Conn.lean`: §3, `ho16_prop19`, and `hoProp19_holds : HOProp19`;
* `P208.lean`: §4, `ho16_p208_false`;
* `Thm20.lean`: §5 with `HOProp19` as a hypothesis (`ho16_lift_aux`,
  `ho16_lift_stairwell_of_prop19`, `ho16_theorem20_of_thm15_prop19`,
  `homeomorph_pseudoArc_of_indec_homogeneous_of_thm15_prop19`);
* `HO16D.lean`: the skeleton's §5 statements, `HOProp19` discharged by `hoProp19_holds`;
* `NonVac196.lean`: the non-vacuity examples of §6.

`HPC.lean` ends with `import HPC.HO16.HO16D` and `import HPC.HO16.NonVac196`; `lake build HPC`
succeeds. No new file contains `sorry`, `admit` or `axiom`.

**Statements.** Every definition and theorem of the skeleton (`p19T`, `p19α`,
`IsSimpleFoldOf.isOrdinaryPt_iff`, `ho16_prop19_full`, `ho16_prop19`, `ho16_p208_false`, `HOThm15`,
`ho16_lift_stairwell`, `ho16_theorem20_of_thm15`,
`homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`) is textually the skeleton's (checked by a
script comparing each declaration with the skeleton, whitespace normalized).

**Shape changes** (additions only; no skeleton statement is changed):
1. New definition `HOProp19` (`P19Defs.lean`): the statement of `ho16_prop19` quantified over
   `E : Type`, as a named `Prop`. The induction of Theorem 20 was written against it
   (`Thm20.lean`) while Proposition 19 was being proved; it is now proved (`hoProp19_holds`).
2. The conditional versions in `Thm20.lean` (suffix `_prop19`, with the hypothesis
   `h19 : HOProp19`); the skeleton's three §5 theorems in `HO16D.lean` apply them to
   `hoProp19_holds`.
3. The file split above.

Status lines:
* STATUS: §2 `IsSimpleFoldOf.isOrdinaryPt_iff` proved
* STATUS: §3 `ho16_prop19_full` proved
* STATUS: §3 `ho16_prop19` proved (and `hoProp19_holds : HOProp19`)
* STATUS: §4 `ho16_p208_false` proved
* STATUS: §5 `ho16_lift_stairwell` proved
* STATUS: §5 `ho16_theorem20_of_thm15` proved
* STATUS: §5 `homeomorph_pseudoArc_of_indec_homogeneous_of_thm15` proved

## 1. The items, in order

### §2. Ordinary points of a fold (`OrdFold.lean`)

`IsSimpleFoldOf.isOrdinaryPt_iff`: if every point of `∂G₂` is ordinary in `G`, then `z ∈ F` is
ordinary in `F` iff `π(z)` is ordinary in `G`. Off `F₁ ∩ F₂` and `F₂ ∩ F₃`, `z` has a
neighbourhood in `F` inside one sheet; being ordinary is local (`IsOrdinaryPt.of_local`,
`isOrdinaryPt_congr_local`) and is transported by `π` on a PL graph on which `π` is injective
(`isOrdinaryPt_image_fst_iff`, through batch 195's order count `isOrdinaryPt_iff_order`;
`isOrdinaryPt_one_sheet`). At a glueing point, `G₂` lies on one side of `π(z)` near it
(`one_side_of_relFrontier`), each of the two sheets is a single segment near `z`
(`exists_single_spoke`), and the two spokes meet only at `z`
(`IsSimpleFoldOf.isOrdinaryPt_of_mem_inter`). The latter is also the "J₁, J₂" of p. 207, used for
(S3′) at `∂F₃`.

### §3. Proposition 19 (`P19Lib.lean` … `Prop19Conn.lean`)

`ho16_prop19_full` follows H–O pp. 203–208 and commission §3 step by step:
* straightness and end sets, (19.4)–(19.9): Lemma 18 for `S′ᵢ` (`i ≠ i₀`), `P′₁`, `P′₂`
  (`P19.straight_T`, `P19.straight_P'₁`, `P19.straight_P'₂`); level `i₀` by hand, with
  `π(S′_{i₀}) = F₁ ∪ F₂ ∪ (F₃ ∩ φ⁻¹(π(S_{i₀})))` (`P19.image_T'₀`, `P19.isPLGraph_image_T'₀`,
  `P19.straight_T'₀`, `P19.endSet_T'₀`);
* (S1′), (S2′), finiteness (at most three preimages of a point, `foldPre_finite`): `Prop19.lean`;
* (S3′): `P19.S3'T`, `P19.S3'P`, `P19.S3'γ`;
* (S4′): `Prop19D.lean`; frontiers of components of `F \ π(S′ᵢ)` lie over frontiers of components
  of `G \ π(Sᵢ)` (`relFrontier_over`, `hasConsCompl_pullback`); level `i₀`: `P19.S4'_i₀`; level
  `i₀ + 1`: Proposition 10 (second part) and Lemma 6 (6) (`P19.split_i₀1`, `P19.S4'_i₀1_α`,
  `P19.S4'_i₀1_γ`); `P′₂`: the case split of commission §3 (`P19.split_P'₂`, `P19.S4'_P'₂_E`,
  `P19.S4'_P'₂_γ`), not H–O's sentence (§4);
* (S5′): `P19.gen'_stair`, `P19.gen'_broken`, by §2;
* (S6′): `P19.S6'`.
The broken structure (`i₀ < k`) is `P19.broken`, the stairwell (`i₀ = k`) `P19.stair`, and
`S′ ⊆ φ⋆⁻¹(S)` is `P19.sub_foldPre_S`.

`ho16_prop19` (`Prop19Conn.lean`): `exists_simpleFold` gives the fold; the first part of
Proposition 7 (`ho16_prop7`) gives a component `C` of `F` with `φ(C) = G`, and the pieces `Fᵢ ∩ C`
form a connected simple fold. `C` meets `F₂ ∩ F₃` (`P19.comp_meets_F₂₃`, H–O's "clearly C meets
∂F₃ by Lemma 6 (6)", through the sides of Lemma 6 (6)), so `S′_{i₀}`, `P′₁`, `P′₂` meet `C⋆`
(`P19.γ_lift`), and the other levels do because `φ(C) = G` (`P19.T'_meets`). The structure is
restricted with `ho16_obs16_comp` / `ho16_obs13_comp` and `foldPre_inter_comp`
(`foldPre F S ∩ C⋆ = foldPre C S`). H–O's component `K` is not needed.

### §4. The false sentence of p. 208 (`P208.lean`)

`ho16_p208_false` is proved with the data of commission §4 (`G = [0, 10]`, `a = 11/2`). Since the
statement is about `G` only, every sheet is placed at height `1/2` (the heights of the commission's
example are irrelevant to the projections); all of (S1′)–(S6′) are checked in Lean, with explicit
relative frontiers (`p208_rf_*`) and end sets (`endSet_p208*`). The point is `x = 3/2`, whose
component `[0, 4)` in `G \ [4, 6]` has frontier `{4} = π(α₂)`. I found no error in the example.

### §5. Theorem 20 from Theorem 15 (`Thm20.lean`, `HO16D.lean`)

`ho16_lift_aux` is the strong induction of commission §5 with the measure `(k + 1)²` (stairwell)
and `(k + 1)² + (k + 1 − i₀)` (broken), quantified over `E : Type`. Height 1: the section of
`ho16_height_one`. Height `k ≥ 3`: `ho16_prop17` (pit at level 1, height `k − 2`). Broken with
`γ = ∅` or `𝓔(P₁) = ∅`: `ho16_rem17_gamma`, `ho16_rem17_P1`. Otherwise: `HOProp19` (i.e.
Proposition 19), `ho16_theorem8` with `ε/2`, the induction hypothesis in `E × ℝ` with `ε/2`, and
`phiStar`. `ho16_theorem20_of_thm15_prop19` does the reduction to components (finitely many,
clopen; `M ∩ C⋆` separates `C × {0}` from `C × {1}` in `C⋆` with the same open sets; the maps on the
clopen sets `f⁻¹(C)` are glued, continuity by local agreement) and applies `HOThm15` and the
induction to each component. `HO16D.lean` discharges `HOProp19`.

## 2. Non-vacuity notes

All in `NonVac196.lean`, proved:
* `ho16_prop19`, `ho16_prop19_full` with `i₀ = k`: `prop19_example_stair` applies `ho16_prop19` to
  batch 195's `prop19_fold_example` (height 1, pit at level 1, over `[0, 3]`) and obtains a
  connected simple fold of `[0, 3]` with a stairwell structure of height 1 in `φ⋆⁻¹(S)`.
* With `i₀ < k`: `prop19_example_broken` applies `ho16_prop19` to the structure of §4 (height 3,
  pit at level 2; `ho16_p208_false` contains every hypothesis of Proposition 19: PL, connected,
  broken structure, `γ ≠ ∅`, `𝓔(P₁) ≠ ∅`) and obtains a connected fold of `[0, 10]` with a broken
  structure of height 3 with a pit at level 3. The same structure, through `ho16_prop19_full`, is
  an instance of the full-fold version.
* `ho16_lift_stairwell`: `lift_stairwell_example` applies it to batch 195's stairwell of height 3
  over `[0, 3]`, `X` a point (`isHereditarilyIndecomposable_univ_unit`) and `f` constant.
* `ho16_theorem20_of_thm15`, the named `Prop`s on degenerate inputs: empty `G` is excluded from
  `HOThm15` by `IsConnected G` (with `G = ∅` the statement would be false, as the commission's
  referee found); `hoThm15_segment_hyps` checks that a segment `G = [0, 1]` with `M = G × {½}` (and
  `U = univ`) meets every hypothesis of `HOThm15`. `HOProp19`'s hypotheses require `γ ≠ ∅` and
  `𝓔(P₁) ≠ ∅`, so for empty `G` it is vacuous; it is proved (`hoProp19_holds`) and its hypotheses
  are met by the two examples above. The proof of `ho16_theorem20_of_thm15` uses Propositions 17
  and 19, the remarks of p. 201, Theorem 8 for folds and the height-1 section; `HOThm15` is used
  only to produce the stairwell on each component, not as a shortcut.

## 3. Ledger entries

`LEDGER.md`, section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)", HO.23–HO.28:
* HO.23: straightness and end sets supplied; the misprints `φ⁻¹` for `φ⋆⁻¹` (pp. 205, 206) and
  "P′₁∩(∂F₃)⋆=φ⋆⁻¹(γ_{i₀})" (p. 205). Not counted.
* HO.24: (S3)/(S3′) on p. 207 supplied; the slips "β_{i₀}" for `π(β_{i₀})` and "β′_{i₀}" for
  `π(β′_{i₀})` confirmed; the slip "P′₂=φ⁻¹(π(S_{i₀}))∩(F₁∪F₂)" not confirmed (the start of the
  line is illegible in our scan; the visible part reads "…(π(S_{i₀}))∩(F₁∪F₂) agree"). Not counted.
* HO.25: the sentence of p. 208 is false (`ho16_p208_false`); the proposition is true and proved
  with the case split. **Counted as a defective proof, the seventeenth**, as proposed: I agree with
  the classification — a sentence printed false, with a missing case, in the proof of a true
  proposition (as Moore 1925 Theorem 11, Jones 1955 Theorem 1), unlike gaps where nothing printed is
  false (HO.15) and misprints where the argument is intact (HO.23). The annotation of commission
  §7.3 is recorded.
* HO.26: (S5′) supplied by `IsSimpleFoldOf.isOrdinaryPt_iff`. Not counted.
* HO.27: `K` not needed (Proposition 7 gives `C`); "C meets ∂F₃" supplied (`P19.comp_meets_F₂₃`).
  Not counted.
* HO.28: Theorem 20 proved relative to Theorem 15; the reduction to components supplied; the fold
  count: each pass from height `k` to `k − 2` uses at most `k − 2` folds, at most
  `((k₀ − 1)/2)²` in all, as the referee counts; the printed sum mixes parities and is an upper
  bound. Not counted.

The count of defective proofs rises from sixteen to seventeen.

Quotation checks (page images at 200 dpi; p. 207 also at 400 dpi): the §4 sentences (p. 208);
"S′_{i₀}∩(F₃)⋆=φ⁻¹(S_{i₀})∩(F₃)⋆" and "P′₁∩(∂F₃)⋆=φ⋆⁻¹(γ_{i₀}) by (19.2)" (p. 205);
"φ⋆⁻¹(α_{i₀})∩(F₃)⋆=φ⁻¹(α_{i₀})=α′_{i₀}" (p. 206); "neighborhood of β_{i₀}=α_{i₀+1} in G",
"neighborhood of β′_{i₀}=α′_{i₀+1}", "π(S′_{i₀})∩F₃=φ⁻¹(π(S_{i₀}))∩F₃" and the (S4′) text (p. 207)
are as quoted in the commission. On p. 208, H–O's argument at level `i₀ + 1` uses Proposition 10
contrapositively, as the formal proof does (`P19.split_i₀1`).

## 4. Axioms

`doc/batches/audits/axioms-batch196.txt` contains `#print axioms` for the 232 new theorems (the
batch-196 group "H–O Theorem 1, IV (batch 196)" of `Axioms.lean`). All 232 depend on exactly
`[propext, Classical.choice, Quot.sound]`; in particular `IsSimpleFoldOf.isOrdinaryPt_iff`,
`ho16_prop19_full`, `ho16_prop19`, `hoProp19_holds`, `ho16_p208_false`, `ho16_lift_stairwell`,
`ho16_theorem20_of_thm15` and `homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`. (In the audit
file the line of `homeomorph_pseudoArc_of_indec_homogeneous_of_thm15_prop19` is wrapped over three
lines by Lean's pretty-printer, so the file has 234 lines for 232 theorems.) `axioms.txt` is
regenerated after `lake build HPC`: 3176 lines (2942 + 234, none removed; its first 2942 lines are
byte-identical to batch 195's), and contains no `sorryAx`.

## 5. Dependency maps

`homeomorph_pseudoArc_of_indec_homogeneous` is unchanged from batch 193 (its only open input is the
named `Prop` `HOThm20`). The `_of_thm15` version:

```
homeomorph_pseudoArc_of_indec_homogeneous_of_thm15    (HO16D)   proved, from HOThm15
└── homeomorph_pseudoArc_of_indec_homogeneous_of_thm15_prop19 (Thm20) + hoProp19_holds
    ├── homeomorph_pseudoArc_of_indec_homogeneous      (HO16A)   proved, from HOThm20 (batch 193)
    └── ho16_theorem20_of_thm15_prop19 : HOThm20       (Thm20)   proved, from HOThm15, HOProp19
        ├── HOThm15                                    (P19Defs) ** OPEN: named Prop hypothesis **
        ├── reduction to components                    (Thm20)   proved
        └── ho16_lift_aux (induction)                  (Thm20)   proved
            ├── ho16_height_one                        (Stairwell, batch 195) proved
            ├── ho16_prop17                            (Stairwell, batch 195) proved
            ├── ho16_rem17_gamma, ho16_rem17_P1        (Stairwell, batch 195) proved
            ├── ho16_theorem8                          (Thm8Fold, batch 194)  proved
            └── HOProp19 = hoProp19_holds              (Prop19Conn) proved
                └── ho16_prop19
                    ├── ho16_prop19_fold, exists_simpleFold, ho16_prop7 (batches 194–195) proved
                    ├── ho16_obs13_comp, ho16_obs16_comp             (batch 195)  proved
                    └── ho16_prop19_full                (Prop19)  proved
                        ├── ho16_lemma18, ho16_lemma6, ho16_prop10, ho16_obs9_char (batches 194–195)
                        └── IsSimpleFoldOf.isOrdinaryPt_iff          (OrdFold)    proved
```

`HOThm15` is the only open input of the `_of_thm15` route.

## 6. Comments on the plan for Theorem 15 (pp. 194–198)

* **What the library has.** PL graphs with fans, components, relative frontiers, ordinary points
  and their finiteness (`IsPLGraph.finite_not_ordinary`), intersections with preimages under `π`
  (`IsPLGraph.inter_preimage_fst`), straight sets whose projections are PL (the sheets need not be
  PL), consistent complements and sides, generic lists.
* **What it lacks.** (i) A PL approximation in `G⋆ ⊆ E × ℝ`: piecewise linear functions on a
  triangulation of `G × [0, 1]` (the library has subdivisions of `G`, `Subdiv.lean`, but nothing two
  dimensional); (ii) general position: perturbing the vertex values of a PL function so that its
  zero set meets each 2-cell of `G × [0, 1]` in a segment avoiding the vertices, and so that the
  finitely many critical first coordinates `Z′` avoid the non-ordinary points of `G`; (iii) the
  structure of the zero set of a generic PL function on `G × [0, 1]` (a finite union of segments, a
  1-dimensional PL set, separating `{u < 0}` from `{u > 0}`); (iv) reading sheets: over each
  component of `G \ Z′` the zero set is a finite union of graphs of continuous functions, ordered by
  height; consecutive ones glue into sheets with end sets over `Z′`.
* **The route of the design notes** (sign function `u = d(·, R₀′) − d(·, R₁′)`, its PL
  approximation, zero set inside `U` in general position, sheets between consecutive points of
  `Z′`): I see no obstruction. Two points to settle first: the zero set must lie inside `U`, which
  needs `R₀′`, `R₁′` (the two sides of the separator outside `U`) to be at positive distance from
  each other and the approximation finer than half that distance (compactness of `G⋆ \ U` gives
  this); and the parity argument for odd height (H–O's count of sheets crossing a vertical fibre,
  which batch 195's `ho16_claim14_1` / `ho16_odd_image` handle at the level of stairwells) needs the
  zero set to cross each fibre `{y} × [0, 1]`, `y ∉ Z′`, an odd number of times, which follows from
  `u < 0` at height 0 and `u > 0` at height 1 and transversality.
* **What I would prove first.** The zero set of a PL function on a single triangle (a segment or a
  point under general position), then on a PL graph times `[0, 1]` triangulated as prisms over the
  edges of a subdivision of `G`; with it, the "graph-like" decomposition over `G \ Z′` and the
  generic choice of `Z′`. The stairwell axioms (S1)–(S5) would then be checked one by one, as for
  Proposition 19.

## 7. Files

The tarball `doc/batches/batch196-files.tar.gz` contains every file added or changed for batch 196
(the work spans two runs; the list compares every file with the batch-195 delivery)
(including this report, the audit, the notes, `doc/batches/COMMISSION-batch196.md` and
`doc/batches/skeletons/HO16D.lean`); the list is `doc/batches/batch196-MANIFEST.txt`.
