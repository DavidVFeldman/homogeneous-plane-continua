Commission read: `doc/batches/COMMISSION-batch193.md` ("Commission: batch 193 — H–O Theorem 1, I: Theorems 4 and 8; plane graphs; `HOThm20`").

# Report, batch 193

## 0. Summary, omissions

**Every item of commission §2–§7 is proved.** The target
`homeomorph_pseudoArc_of_indec_homogeneous` is proved with `HOThm20` (H–O Theorem 20, forward
direction, for PL graphs; a named `Prop`) as its **only open input**. The skeleton is split over
seven files under `HPC/HO16/`:

* `HPC/HO16/Defs.lean` (§2: `IsPLGraph`, `IsFanAt`, `SeparatesIn`, `HOThm20`, three lemmas),
* `HPC/HO16/KM77.lean` (§3: `km77_lemma2`),
* `HPC/HO16/Thm8.lean` (§4: `ho16_theorem8_core`),
* `HPC/HO16/Thm4.lean` (§5: `ho16_theorem4`),
* `HPC/HO16/Grid.lean` (§6.2: `exists_plGraph_approx`, radial projections, grid edges),
* `HPC/HO16/Plane.lean` (§6.1 `interior_eq_empty_of_hi`, §6.3 `exists_path_approx`),
* `HPC/HO16/HO16A.lean` (§7: the three assembly theorems; header lists the split).

`HPC.lean` ends with `import HPC.HO16.HO16A`; `lake build HPC` succeeds (8744 jobs). No declaration
contains `sorry`, `admit` or `axiom`; the seven new files build without warnings. Every one of the
16 skeleton statements (4 definitions, 12 theorems) is **unchanged** (checked by a script comparing
each declaration's text with the skeleton). Nothing is refuted and nothing is commented out.

`axioms.txt` has **2712 lines** (2658 + 54 added, none removed). `sorryAx` occurs in none of them.
The 54 new theorems (group "H–O Theorem 1, I (batch 193)" of `Axioms.lean`; copy in
`doc/batches/audits/axioms-batch193.txt`) use only standard axioms (§4).

**Omissions.** None.

Status lines:
* STATUS: §2 `IsPLGraph.isCompact` proved
* STATUS: §2 `IsPLGraph.exists_fan` proved
* STATUS: §2 `separatesIn_of_closed` proved
* STATUS: §3 `km77_lemma2` proved
* STATUS: §4 `ho16_theorem8_core` proved
* STATUS: §5 `ho16_theorem4` proved
* STATUS: §6.1 `interior_eq_empty_of_hi` proved
* STATUS: §6.2 `exists_plGraph_approx` proved
* STATUS: §6.3 `exists_path_approx` proved
* STATUS: §7 `ho16_theorem1_plane` proved (from `HOThm20`)
* STATUS: §7 `isPseudoArc_of_indec_homogeneous` proved (from `HOThm20`)
* STATUS: §7 `homeomorph_pseudoArc_of_indec_homogeneous` proved (from `HOThm20`)

## 1. The items, in order

### §2. Definitions and lemmas (`Defs.lean`)
The four definitions are the skeleton's. `IsPLGraph.isCompact`: a finite union of segments.
`IsPLGraph.exists_fan`: at `y ∈ G`, the fan consists of the initial pieces, of length `c`, of the
segments from `y` toward the endpoints `w ≠ y` of the segments through `y`, with `c < r/2`, `c`
below the distance from `y` to every other vertex and below the distance from `y` to every segment
not containing `y` (helpers `mem_segment_iff_param`, `segment_subset_union_of_mem`,
`eq_of_mem_segment_halves`).
`separatesIn_of_closed`: disjoint closed `R₀ ⊇ P`, `R₁ ⊇ Q` covering `Y \ M` give the separation
(take `U = R₁ᶜ`, `V = R₀ᶜ`).

### §3. K–M Lemma 2 (`KM77.lean`)
K–M's proof (p. 676). `A*` (resp. `B*`) is the union of the components of `X \ V′` (resp.
`X \ U′`) meeting `A` (resp. `B`); compactness of `A*` is `isClosed_biUnion_connectedComponentIn`.
`A* ∩ B* = ∅`: otherwise continua `C₁ ⊆ A*` from `A` and `C₂ ⊆ B*` from `B` with `C₁ ∩ C₂ ≠ ∅`
give the decomposable continuum `C₁ ∪ C₂` (neither contains the other, as `C₁ ∩ B = ∅`,
`C₂ ∩ A = ∅`), contradicting hereditary indecomposability; K–M's Lemma 1 is not needed. The two
separations and the sets `F₀, F₁, F₂` are K–M's.

### §4. Core of H–O Theorem 8 (`Thm8.lean`)
Statement unchanged. **Route change** (as allowed by "shapes may be adjusted"; the statement is not
affected): steps 1–4 as in the commission (fans of radius `r ≤ ε` with `2r` below the least distance
between the finitely many points of `B₁ ∪ B₃`, so pairwise disjoint; `Kᵢ = f⁻¹(cl(Gᵢ \ G₂))`;
`U₁ = O₁ ∩ f⁻¹(N₁)` with `O₁, O₃` disjoint open neighbourhoods of `K₁, K₃`; K–M Lemma 2). Steps 5–7
(per-segment Tietze extensions and pasting) are replaced by:
* `u₁ : X → [0, 1]` Urysohn, `0` on `X₂ ∩ X₃`, `1` off `U₁`; `u₃` likewise for `X₁ ∩ X₂`, `U₃`;
* `c₁(x)` = the vertex of the fan containing `f(x)`, for `x ∈ W₁ = U₁ \ X₁` (locally constant
  there, since the fans are disjoint and closed: `continuousOn_center_comp`);
* `h = f + g₁ + g₃` with `g₁ = (1 − u₁)·(c₁ ∘ f − f)` on `W₁` and `0` off `W₁` (likewise `g₃`).
  `g₁` is continuous (`continuous_correction`): at a point off `W₁`, either it is off `U₁`, where
  `u₁ = 1` and `‖g₁‖ ≤ (1 − u₁)·r → 0`, or it lies in `X₁ ∩ U₁`, which has the open neighbourhood
  `U₁ \ (X₂ ∪ X₃)` missing `W₁` (a point of `X₁ ∩ U₁` is in no `X₂`, since `X₁ ∩ X₂ ⊆ U₃` misses
  `U₁`, and in no `X₃`).
Only the star-shapedness of a fan about its vertex is used (`IsFanAt.props`): `h(x)` lies on the
segment from `f(x)` to the vertex, so in the fan. The checks are those of step 8.

### §5. H–O Theorem 4, path form (`Thm4.lean`)
Statement unchanged. Step 1 (`thm4_continuum_of_not_separates`): if the set does not separate, the
cut-wire theorem (`exists_split_of_no_continuum`) applied to the compact set
`{(x, t) ∈ G × [0, 1] : d(x, γ t) ≥ ε}` gives a continuum in it meeting both end rows. Step 2
(`thm4_limit_contra`): for `δ = 1/(n+1)`, push these continua to `E × E` by `(x, t) ↦ (x, γ t)`; a
Hausdorff-convergent subsequence (`HPC/Plane/Most51.lean`) has limit a continuum `Z ⊆ X × X` with
`d ≥ ε` on `Z` and `π₂(Z) = X`, hence `π₁(Z) ⊆ π₂(Z)`, contradicting `HOSpanZero X`.

### §6. Plane approximations (`Plane.lean`, `Grid.lean`)
* `interior_eq_empty_of_hi`: a closed ball inside `M` is a continuum, the union of its two closed
  half-balls, which are proper subcontinua.
* `exists_plGraph_approx`: grid of mesh `η = δ/2`; for each grid square meeting `X`, an inner point
  `c ∉ X` (empty interior); radial projection `radProj` from `c` onto the square's frontier (via the
  gauge `rectGauge`). `G` = union of the edges of those squares (a PL graph: grid edges meet only at
  grid points, `gridEdge_inter_subset`). `f` is pasted over the finitely many squares
  (`continuousOn_biUnion_finset`); on shared frontiers `radProj` is the identity.
* `exists_path_approx`: a chain of points of `X` with consecutive distances `< δ`
  (`exists_chain_through`, through a `δ`-net), joined by a polygonal path (`plPath`).

### §7. The assembly (`HO16A.lean`)
As in the commission: Theorem 4 with `ε/6`, `δ = min(δ₀, ε/6)`, the grid graph and path, `HOThm20`
with `U = {(x, t) : t ∈ (0, 1), d(x, γ t) < ε/6}`; the `t`-coordinate of `h` is an `ε`-map, so
`isSnakeLike_univ_of_epsMap` applies. Then Hagopian (`hagopian76_theorem1`), Theorem C (`theoremC`)
and `pseudoArc_unique`.

## 2. Non-vacuity notes

* **`HOThm20` in `ho16_theorem1_plane`, `isPseudoArc_of_indec_homogeneous`,
  `homeomorph_pseudoArc_of_indec_homogeneous`.**
  1. *Not refuted by a short argument.* Its hypotheses are satisfiable (e.g. `X` a point, `G` a
     segment, `M = G × {1/2}`, which separates), and in that instance the conclusion holds (`h`
     constant in `M ⊆ U`). For general `X` it is H–O's Theorem 20, a published theorem; nothing in
     the set-up contradicts it. It quantifies over `X : Type` and `E : Type` (universe 0), which is
     all the assembly uses.
  2. *Not equivalent to the conclusion.* `HOThm20` is about maps from hereditarily indecomposable
     compacta into separators of `G × [0, 1]`; it says nothing about homogeneity, span or
     snake-likeness. The conclusions need, besides `HOThm20`, Theorem 4 (span zero), the grid and
     path approximations, Hagopian's theorem and Theorem C. The printed argument (p. 211) is direct,
     not by contradiction.
* **`ho16_theorem8_core`** has no named `Prop` hypothesis; its fan hypothesis `hfan` is satisfied
  by every PL graph `G₂` (`IsPLGraph.exists_fan`), so it is not vacuous.
* **`ho16_theorem4`** uses `HOSpanZero X` (a definition from batch 191, satisfied by every
  homogeneous indecomposable plane continuum by `theoremC`, and by a point).

## 3. Ledger entries

New section in `LEDGER.md`: "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)",
items HO.1–HO.8, the eight items of commission §9, each with the printed sentence quoted (checked
against the PDF text layer; Theorem 1′ on p. 212 and K–M p. 676 against the page images):
* HO.1 Theorem 1 restated on p. 211 without "non-degenerate": misprint.
* HO.2 [31] for tree-likeness (pp. 191, 211) and [46] (p. 212): recorded; not used on this route.
  [31] itself is not in `doc/sources/`, so its content (announcement, no proofs of Lemma 5 and
  Theorem 6) was not checked here.
* HO.3 Theorem 4, p. 184: the cut wire is to be applied to `{d ≥ ε}`; with that reading the step is
  right. Gap; not counted.
* HO.4 Theorem 8, pp. 187–189: disjointness of different fans not said (the "otherwise pairwise
  disjoint" of p. 187 concerns the arcs of one fan). **Further observation:** p. 188 defines
  "Ki =f −1 (Gi \G2 )" (not closed in general) and writes "f −1 (yj1 ) ⊂ f −1 (G1 \G2 ) = K1",
  false as written since `yⱼ¹ ∈ G₂`; the reading `Kᵢ = f⁻¹(cl(Gᵢ \ G₂))` repairs both. Gaps; not
  counted.
* HO.5 Theorem 8, (3) ⇒ (1), p. 189: `U` and `V` interchanged; misprint.
* HO.6 K–M Lemma 2, p. 676: correct; Lemma 1 not needed for hereditarily indecomposable `X`.
* HO.7 "It follows that dH (X, T )<δ" (p. 211): unargued; repaired by `T := f(X)`; avoided here.
* HO.8 Theorem 1′, p. 212: the defect of HO.1; misprint.

No defective proof is added; the count stays at sixteen.

## 4. Axioms

`axioms.txt` regenerated by `lake env lean Axioms.lean`: **2712 lines** (2658 before, 54 added,
none removed); `sorryAx` in no line. The 54 lines of the new group are in
`doc/batches/audits/axioms-batch193.txt`.
**All 54 use exactly the three standard axioms `propext`, `Classical.choice`, `Quot.sound`.**
`HOThm20` is a hypothesis (a `Prop` argument), not an axiom, so it does not appear in the lists.

Main theorems:
```
'HPC.HO16.km77_lemma2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.ho16_theorem8_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.ho16_theorem4' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.interior_eq_empty_of_hi' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.exists_path_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.exists_plGraph_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.ho16_theorem1_plane' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.isPseudoArc_of_indec_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.homeomorph_pseudoArc_of_indec_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Dependency map of `homeomorph_pseudoArc_of_indec_homogeneous`

```
homeomorph_pseudoArc_of_indec_homogeneous        (HO16A)      proved, from HOThm20
├── pseudoArc_unique                              (HPC.Plane)  proved (earlier batches)
└── isPseudoArc_of_indec_homogeneous              (HO16A)      proved, from HOThm20
    ├── hagopian76_theorem1                       (HPC.Hagopian) proved (earlier batches)
    ├── theoremC                                  (HPC.Span)   proved (batch 192)
    └── ho16_theorem1_plane                       (HO16A)      proved, from HOThm20
        ├── HOThm20                               (Defs)       ** OPEN: named Prop hypothesis **
        ├── ho16_theorem4                         (Thm4)       proved
        │   ├── thm4_continuum_of_not_separates   (cut wire, exists_split_of_no_continuum)
        │   └── thm4_limit_contra                 (Hausdorff limits, Most51)
        ├── interior_eq_empty_of_hi               (Plane)      proved
        ├── exists_plGraph_approx                 (Grid)       proved
        ├── exists_path_approx                    (Plane)      proved
        ├── IsPLGraph.isCompact                   (Defs)       proved
        └── isSnakeLike_univ_of_epsMap            (HPC.Plane)  proved (earlier batches)
```

`HOThm20` is the only open input. `km77_lemma2` and `ho16_theorem8_core` are not on this map; they
are the first pieces of `HOThm20` (commission §8).

## 6. What the classification now has

H–O (p. 180) combine Theorems A, B, C and Theorem 1 into Theorem 2: up to homeomorphism the only
non-degenerate homogeneous plane continua are the circle, the pseudo-arc and the circle of
pseudo-arcs. In the main
build:
* Theorems A, B and C are in the main build (batch 192 commission, §0); **Theorem C**
  (`theoremC`) and **Hagopian's theorem** (`hagopian76_theorem1`: homogeneous indecomposable plane
  continua are hereditarily indecomposable) are unconditional;
* **new in batch 193:** "every indecomposable non-degenerate homogeneous plane continuum is a
  pseudo-arc" (`isPseudoArc_of_indec_homogeneous`, `homeomorph_pseudoArc_of_indec_homogeneous`)
  **from `HOThm20`**, its only open input; and H–O Theorem 1, "if", for plane continua
  (`ho16_theorem1_plane`), from `HOThm20`.

Remaining for the indecomposable case: `HOThm20` (commission §8: folds as sets, Theorem 8 for
folds from `ho16_theorem8_core`, Lemma 6 – Proposition 19, Theorem 15, Theorem 20).

## 7. Comments on the route of §8

* `ho16_theorem8_core` is stated for normed `E` and uses only that fans are star-shaped about their
  vertex and pairwise disjoint (enforced inside the proof by the radius choice). For folds realized
  as sets in `E × ℝ`, `F` is again a PL graph, so `IsPLGraph.exists_fan` supplies the fans.
* The correction `h = f + (1 − u)·(c − f)` keeps `h` on the segment from `f(x)` to a fan vertex,
  which is convenient for the lift `g = (h, height on Fᵢ)`: on `X₂ ∩ X₃` the value is exactly the
  vertex.

## 8. Files

The tarball `doc/batches/batch193-files.tar.gz` contains every file added or changed in this run;
the list is `doc/batches/batch193-MANIFEST.txt`.
