Commission read: `doc/batches/COMMISSION-batch197.md` ("Commission: batch 197 — H–O Theorem 1, V: Theorem 15 (ladders), and the end of Part F").

# Report, batch 197

## 0. Summary, omissions, shape changes

**Every item of commission §2–§6 is proved, the stretch of §5 included.** Nothing is refuted and
nothing is open. In particular `ho16_theorem15 : HOThm15` and `ho16_theorem20 : HOThm20` are proved,
and **`ho16_indec_homogeneous_pseudoArc` (every indecomposable non-degenerate homogeneous plane
continuum is a pseudo-arc, H–O p. 180) holds with no named hypothesis**, on the three standard
axioms:

```
'HPC.HO16.ho16_indec_homogeneous_pseudoArc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The skeleton `doc/batches/skeletons/HO16E.lean` (byte-identical to the uploaded `HO16E.lean`; the
commission is copied to `doc/batches/COMMISSION-batch197.md`, byte-identical) is split over files
under `HPC/HO16/`:

* `LadderDefs.lean`: the skeleton's definitions `IsLadder`, `zzL`, `zzR`, `zzLine`, `ladderY`,
  `ladderPiece`, `ladderSheet`, `ladderHeight`;
* `LadderParam.lean`: the parameter calculus of an edge (zig-zag intervals, their order, the pieces'
  parameter intervals, the candidate end points);
* `LadderPiece.lean`: pieces as segments, their projections, injectivity of `π`, compactness;
* `LadderStair.lean`, `LadderStair2.lean`: §3, (S1)–(S5), the explicit `α` (`ladderAlphaSet`),
  `ladder_isStairwellStr`;
* `LadderSubdiv.lean`: uniform subdivision of a decomposition (`subdiv`);
* `LadderSign.lean`: sign sequences, their sign changes and lists of heights (`chg`, `sgnList`,
  `wedgeEv`), the effect of one flip (`chg_flip`, `chgPair_cases`), heights of pieces
  (`heightOK_of_mem_piece`);
* `LadderSep.lean`: the sign function of a separator (`exists_sign_fn`);
* `LadderExists.lean`: the ladder near a separator (`exists_ladder_aux`);
* `HO16E.lean`: the skeleton's theorems;
* `NonVac197.lean`: further non-vacuity checks (§2 below).

`HPC.lean` ends with `import HPC.HO16.HO16E` and `import HPC.HO16.NonVac197`; `lake build HPC`
succeeds. No new file contains `sorry`, `admit` or `axiom`.

**Statements.** Every definition and theorem of the skeleton (`IsLadder`, `zzL`, `zzR`, `zzLine`,
`ladderPiece`, `ladderSheet`, `ladderHeight`, `ho16_stairwell_of_ladder`, `exists_ladder`,
`ho16_theorem15`, `ho16_theorem20`, `ho16_indec_homogeneous_pseudoArc`,
`ho16_pseudoArc_indec_homogeneous`, `ho16_indec_homogeneous_iff`, `exists_indec_homogeneous_plane`,
`ladder_example`) is textually the skeleton's (checked by a script comparing each declaration with
the skeleton, whitespace normalized; definitions with their bodies).

**Shape changes:** none to skeleton statements. Additions: `ladder_example_height`,
`ladder_example_stairwell` (§6, the height-3 structure of the example), `ladder_example_alpha2`,
`ladder_example_alpha3`, `exists_ladder_example`, `isLadder_empty`, `not_isLadder_even` (non-vacuity),
`isIndecomposable_univ_of_isIndecomposable` and `not_isDecomposableSpace_of_isIndecomposable_univ`
(the transfer of §5/§6), and the file split above.

**Route differences** (commission §5, "If you see a simpler route, take it and say so"):
1. *Lipschitz instead of uniform continuity.* `u = infDist · K₀ − infDist · K₁` is 2-Lipschitz, so
   the `δ` of step 2 is explicit; `exists_sign_fn` returns `δ` with: every point of `G⋆` within `δ`
   of a point with `u ≤ 0` and of a point with `u > 0` lies in `U ∩ G × (0, 1)`.
2. *Uniform subdivision.* Each edge of the fine decomposition is cut into `N − 1` equal pieces
   (rather than into `r` pieces, one per flipped level); the `k`-th point carries the signs of the
   second end at levels `≤ k` and of the first end above, so consecutive points differ at level
   `k + 1` at most (`lσE`). A piece where nothing flips has equal lists and no event.
3. *Events read off the lists.* The event of a piece is computed from the two end lists
   (`wedgeEv`: a wedge at the second end iff the second list is two longer, at place
   `firstDiff + 1`, tip at parameter `½`, at height the mean of the two new entries, which is
   `t_q`); a piece whose first list is two longer is oriented backwards (`lo`).
4. Connectedness of `G` is used only for `G ≠ ∅` (in `exists_sign_fn`); §3 does not use it.

Status lines:
* STATUS: §2–§3 `ho16_stairwell_of_ladder` proved
* STATUS: §5 `ho16_pseudoArc_indec_homogeneous` proved
* STATUS: §5 `exists_ladder` proved
* STATUS: §5 `ho16_theorem15` proved
* STATUS: §5 `ho16_theorem20` proved
* STATUS: §5 `ho16_indec_homogeneous_pseudoArc` proved
* STATUS: §5 `ho16_indec_homogeneous_iff` proved
* STATUS: §6 `ladder_example`, `exists_indec_homogeneous_plane` proved

## 1. The items, in order

### Proved

1. **`ho16_stairwell_of_ladder`** (§3). If `IsLadder G S y ev` and `S.Nonempty`, then
   `ladderHeight S y` is odd (`odd_ladderHeight`) and the union of the sheets `1 … k` has the
   stairwell structure `IsStairwellStr G _ k (ladderSheet S y ev) (ladderAlphaSet S y ev)`
   (`ladder_isStairwellStr`). The commission's reading is confirmed point by point:
   * the `α` (`ladderAlphaSet`, `LadderStair.lean`; per edge `eA`, `LadderParam.lean`): on a wedge
     edge the right ends `L_{i−1}(r_{i−1})`, the left ends `L_{i−2}(l_{i−2})`, and the tip for
     `i = m + 1`; `α₁ = ∅`, `α_{k+1} = ∅` (`e_A_one`, `e_A_top`);
   * (S1): `injOn_fst_ladderSheet` (pairwise disjoint parameter intervals `eI_disj`, and the common
     point `(v, yᵢ(v))` over a vertex, `ladderPiece_snd_of_fst`, `ladderPiece_snd_of_snd`),
     `isPLGraph_image_fst_ladderSheet`, `isStraight_ladderSheet`, non-emptiness from a vertex with
     `j(v) = k` (`ladderSheet_nonempty`);
   * (S2): `relFrontier_image_fst_ladderSheet`, `endSet_ladderSheet`;
   * (S3): `ladder_S3` (the two sheets leave each point of `β_i = α_{i+1}` along the same segment,
     `w_S3`, `e_S3`);
   * (S4): `ladder_S4`, through `relFrontier_comp_ladder` (a component either lies in a gap inside
     an edge, `gapA`, `gapB`, or contains only vertices with `j(v) < i`, and its frontier points are
     labelled by the parity of `i`, `vertex_label`);
   * (S5): `ladder_S5` (end points over interior points of edges, ordinary by
     `isOrdinaryPt_iff_order`, at pairwise different parameters, `e_A_disj`).
   Connectedness is not used; neither sortedness nor distinctness of the lists.
2. **`ho16_pseudoArc_indec_homogeneous`**: from `IsPseudoArc (univ : Set M)`, homogeneity by
   `homogeneous_of_isPseudoArc` transferred along `Homeomorph.Set.univ`, and indecomposability by
   `not_isDecomposableSpace_of_isIndecomposable_univ`.
3. **`exists_ladder`** (§5; replacing Claim 15.1): from `exists_ladder_aux`, on the route of
   commission §5 with the differences listed in §0. Steps: `exists_sign_fn` (step 1); a
   subdivision `S₁` of a decomposition of `G` into edges shorter than `δ` and `N = ⌈1/δ⌉ + 2` levels
   (step 2); lists `ly` as midpoints of sign changes, odd by `odd_length_chg` (step 3); the uniform
   subdivision with one flip per piece, events by `wedgeEv` (step 4); the ladder property
   `LData.isLadder`; every point of every sheet near two corners with both signs
   (`LData.sheet_corners`, from `heightOK_of_mem_piece`), hence in `U ∩ G × (0, 1)`.
4. **`ho16_theorem15 : HOThm15`**: `exists_ladder`, then `ho16_stairwell_of_ladder` (the union of the
   sheets lies in `U ∩ G × (0, 1)`).
5. **`ho16_theorem20 : HOThm20`**: `ho16_theorem20_of_thm15 ho16_theorem15`.
6. **`ho16_indec_homogeneous_pseudoArc`**: `homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`
   applied to `ho16_theorem15`. No named hypothesis.
7. **`ho16_indec_homogeneous_iff`**: forward `isPseudoArc_of_indec_homogeneous` with
   `ho16_theorem20`; backward `ho16_pseudoArc_indec_homogeneous`.
8. **`ladder_example`**, `ladder_example_height` (`= 3`), `ladder_example_stairwell` (a stairwell
   structure of height 3), and **`exists_indec_homogeneous_plane`** (§6).

### Refuted

None.

### Open

None.

## 2. Non-vacuity notes

* **`IsLadder`** on degenerate inputs: `isLadder_empty` (`G = ∅`, `S = ∅`: every `y`, `ev` is a
  ladder; that is why `ho16_stairwell_of_ladder` assumes `S.Nonempty`, which makes the height
  attained); `not_isLadder_even` (a list of even length, here `[]`, is rejected). The example
  `ladder_example` is a ladder with a wedge.
* **`ladder_example`** (§6) checked against the commissioner's hand computation:
  `ladder_example_alpha2 : π(α₂) = {4/3, 3/2}` and `ladder_example_alpha3 : π(α₃) = {7/6}` hold as
  computed (`l₁ = 1/6`, `r₁ = 1/3` over `[1, 2]`), and the structure has height 3.
* **`exists_ladder`**: its hypotheses are met (`exists_ladder_example`: `G = [0, 1]`,
  `M = G × {½}`, `U = ℝ × (¼, ¾)`; the hypotheses from batch 196's `hoThm15_segment_hyps`), and its
  conclusion then gives a non-empty ladder with all sheets inside `U ∩ G × (0, 1)`.
* **`ho16_indec_homogeneous_pseudoArc`** has no named hypothesis; its hypotheses are met
  (`exists_indec_homogeneous_plane`: the plane pseudo-arc `isPseudoArc_plane`, homogeneous by
  `homogeneous_of_isPseudoArc`, indecomposable as the subtype by
  `isIndecomposable_univ_of_isIndecomposable` and `not_isDecomposableSpace_of_isIndecomposable_univ`;
  non-degenerate). No transfer `IsPseudoArc M₀ → IsPseudoArc (univ : Set M₀)` was needed.
* `HOThm15` itself: batch 196's note stands (with `G = ∅` its conclusion would be false; it is
  stated for connected `G`); now proved.

## 3. Ledger entries

In `LEDGER.md`, section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)":

* **§0, two additions** (as asked; confirmed by the commissioner on 400-dpi crops of p. 207): HO.23
  (the second `φ⁻¹` in the (S4) paragraph, for `φ⋆⁻¹`) and HO.24 (the start of the line in (S3)
  reads "P′₂=φ⁻¹(π(S_{i₀}))∩(F₁∪F₂) agree", `P′₂` for `π(P′₂)`). Both recorded as misprints, not
  counted.
* **HO.29** (p. 195, Claim 15.1): unargued main construction; replaced by `exists_ladder`. The side
  wedge "x as an endpoint" for `(x, y)`: misprint. "(x,y) cannot be an endpoint of M′ … by (3)":
  a wrong citation for a true step (irreducibility gives it). Not counted.
* **HO.30** (pp. 195–196, branch points): unargued; not used. Not counted.
* **HO.31** (p. 196, odd counts): unargued; supplied by sign changes (`odd_length_chg`). Not counted.
* **HO.32** (p. 197): "two consecutive points", "exactly j−2 points": unargued, true; "S irreducibly
  separates … because M′ does": unargued and not needed (the end sets come from the construction).
  Not counted.
* **HO.33** (p. 198): straightness, (S3), (S5), the tips and turning points: unargued, supplied by
  `ho16_stairwell_of_ladder`. The unstated condition `b ∉ J_j` (the `J_i` in the open arc): agreed,
  a gap in the wording, not in the argument. "a_i" for `a_p`: misprint. The missing case of the (S4)
  case split (a component around a cycle of `G` with both frontier points on one arc): agreed, a
  gap, covered by the same chain argument. "{z}_*": typography. Not counted.
* **HO.34** (p. 198, Figure 8): in words; not formalized, not needed. Not counted.
* **HO.35** (pp. 194–195, the cited theorem on irreducible separators): not used; recorded. Not
  counted.

The quotations of §4 on pp. 195–198 were checked against page images rendered at 200 dpi (PDF
pp. 19–22); the subscripts and primes quoted there (including "C₂ are arcs which both have x as an
endpoint", "|M′∩{z}_*|<i", "Since a_i∈C for p=2, ..., n−1") read as the commission quotes them.
The p. 207 additions rest on the commissioner's 400-dpi check.

**Count.** Batch 197 adds no defective proof and no refutation (HO.29–HO.35 are unargued steps, a
construction left to the reader, a wrong citation for a true step, an unstated condition, a missing
case, and misprints; nothing printed false about the objects of a proof, unlike HO.25). The count
stays at seventeen. If the commissioner prefers to count the missing case of HO.33 or the wrong
citation of HO.29, the entries say exactly what was found.

## 4. Axioms

`doc/batches/audits/axioms-batch197.txt`: `#print axioms` for every new public theorem (209
lines, group "H–O Theorem 1, V (batch 197)" of `Axioms.lean`). `sorryAx` occurs in none. 201
show exactly `[propext, Classical.choice, Quot.sound]`; 8 (list lemmas of `LadderSign.lean`:
`mem_chg`, `chg_congr`, `chg_succ`, `length_chg_mod`, `range_split`, `chg_split`, `chg_flip`,
`chgPair_cases`) show a subset (`[propext, Quot.sound]` or `[propext]`). The theorems of the
skeleton:

| theorem | axioms |
|---|---|
| `ho16_stairwell_of_ladder` | `propext, Classical.choice, Quot.sound` |
| `exists_ladder` | `propext, Classical.choice, Quot.sound` |
| `ho16_theorem15` | `propext, Classical.choice, Quot.sound` |
| `ho16_theorem20` | `propext, Classical.choice, Quot.sound` |
| `ho16_indec_homogeneous_pseudoArc` | `propext, Classical.choice, Quot.sound` |
| `ho16_pseudoArc_indec_homogeneous` | `propext, Classical.choice, Quot.sound` |
| `ho16_indec_homogeneous_iff` | `propext, Classical.choice, Quot.sound` |
| `exists_indec_homogeneous_plane` | `propext, Classical.choice, Quot.sound` |
| `ladder_example` | `propext, Classical.choice, Quot.sound` |

`axioms.txt` is regenerated with `lake env lean Axioms.lean > axioms.txt` (see §7 for its line
count).

## 5. Dependency map of `ho16_indec_homogeneous_pseudoArc`

```
ho16_indec_homogeneous_pseudoArc                       (HO16E)     proved, no named hypothesis
└── homeomorph_pseudoArc_of_indec_homogeneous_of_thm15 (HO16D, batch 196) proved, from HOThm15
    ├── homeomorph_pseudoArc_of_indec_homogeneous      (HO16A, batch 193) proved, from HOThm20
    │   ├── pseudoArc_unique                           (HPC.Plane)  proved
    │   └── isPseudoArc_of_indec_homogeneous           (HO16A)      from HOThm20
    │       ├── hagopian76_theorem1                    (HPC.Hagopian) proved (batch 190)
    │       ├── theoremC                               (HPC.Span)   proved (batch 192)
    │       └── ho16_theorem1_plane                    (HO16A)      from HOThm20
    │           └── ho16_theorem4, grid/path approximation, isSnakeLike_univ_of_epsMap  proved
    ├── ho16_theorem20_of_thm15 : HOThm15 → HOThm20     (Thm20, batch 196) proved
    │   ├── reduction to components                    (Thm20)      proved
    │   └── ho16_lift_aux / ho16_lift_stairwell        (Thm20)      proved
    │       ├── ho16_height_one, ho16_prop17, ho16_rem17_*   (batch 195) proved
    │       ├── ho16_theorem8 (folds)                  (batch 194)  proved
    │       └── hoProp19_holds : HOProp19 (ho16_prop19) (batch 196) proved
    └── ho16_theorem15 : HOThm15                        (HO16E)     proved   ← this batch
        ├── exists_ladder = exists_ladder_aux           (LadderExists)
        │   ├── exists_sign_fn                          (LadderSep)
        │   ├── subdiv, pairwiseEndpoints_subdiv        (LadderSubdiv)
        │   ├── odd_length_chg, chg_flip, chgPair_cases,
        │   │   wedgeEv, heightOK_of_mem_piece          (LadderSign)
        │   └── LData.isLadder, LData.sheet_corners     (LadderExists)
        └── ho16_stairwell_of_ladder                    (HO16E)
            ├── odd_ladderHeight                        (LadderStair)
            └── ladder_isStairwellStr                   (LadderStair2)
                ├── (S1) injOn_fst_ladderSheet, isPLGraph_image_fst_ladderSheet,
                │        isStraight_ladderSheet         (LadderStair, LadderPiece)
                ├── (S2) relFrontier_image_fst_ladderSheet, endSet_ladderSheet
                ├── (S3) ladder_S3
                ├── (S4) ladder_S4, relFrontier_comp_ladder, vertex_label
                └── (S5) ladder_S5
```

Nothing on this map is open; every node is proved on the three standard axioms.

## 6. What remains of the classification

H–O (p. 180) state the classification: up to homeomorphism, the only non-degenerate homogeneous
plane continua are the circle, the pseudo-arc and the circle of pseudo-arcs. In the main build:

* **The circle**: Bing 1960 for plane continua (`bing60_plane_uncond`, batch 190): a homogeneous
  plane continuum containing an arc is a simple closed curve.
* **The indecomposable case, both directions** (this batch): a non-degenerate plane continuum is
  homogeneous and indecomposable iff it is a pseudo-arc (`ho16_indec_homogeneous_iff`).
* **The decomposable case, first half** (Theorem A; Jones 1955 Theorem 2, batch 154,
  `HPC.Jones.jones55_theorem2'`): a decomposable homogeneous plane continuum has a continuous
  decomposition into homogeneous, indecomposable, non-separating continua with quotient a simple
  closed curve. With this batch, each element is a homogeneous indecomposable plane continuum, so
  (if non-degenerate) a pseudo-arc.

Still to come (not commissioned here):
1. **Part G, the decomposable case**: a decomposable homogeneous plane continuum is homeomorphic to
   *the* circle of pseudo-arcs. On top of Jones 1955 and this batch, this needs a definition of the
   circle of pseudo-arcs and a uniqueness theorem for circle-like decompositions into pseudo-arcs
   (Bing–Jones 1959). `HPC/Covers/Matching.lean` (homeomorphisms from matched covers of summable
   mesh) is described there as the engine of Bing–Jones's uniqueness; the uniqueness theorem
   itself is not in the build.
2. **The converse**: the circle of pseudo-arcs is homogeneous (Bing–Jones 1959).
3. **The final statement with all three cases**: a non-degenerate homogeneous plane continuum is
   homeomorphic to the circle, the pseudo-arc or the circle of pseudo-arcs, and each of them is
   homogeneous. The first two cases and the trichotomy's case split are in place (Bing 1960,
   Jones 1955, Hagopian 1976 Theorem 1, Theorem C and now H–O Theorem 1); the third case is items 1
   and 2.

## 7. Files

See `doc/batches/batch197-MANIFEST.txt` (header, then `A`/`M` lines) and the tarball
`doc/batches/batch197-files.tar.gz`, which contains every listed file and the manifest.

* `axioms.txt`: regenerated, 3385 lines (`wc -l axioms.txt`; 3176 before this batch plus the 209 new lines, the first 3176 unchanged); `sorryAx` in no line.
* `doc/batches/audits/axioms-batch197.txt`: the 209 new lines.
* `LEDGER.md`: additions to HO.23 and HO.24; HO.29–HO.35 and the count.
* `OPEN.md`: batch-197 entry (nothing open; `HOThm15`, `HOThm20` closed).
* `README.md`: H–O Theorem 1, V; layout row.
* `doc/notes/ho16.md`: "Ladders and Theorem 15 (batch 197)"; "What remains" updated.
