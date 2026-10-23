Commission read: `doc/batches/COMMISSION-batch195.md` ("Commission: batch 195 — H–O Theorem 1, III: sides; straight sets, stairwells; Prop. 17, Lemma 18").

# Report, batch 195

## 0. Summary, omissions, shape changes

**Every item of commission §2–§9 is proved, including the stretch item of §8**
(`ho16_prop19_fold`). Nothing is refuted apart from the certificate of §5.4, which refutes the
remarks of pp. 193–194 read without "G connected", as the commission asked. Nothing is commented
out. `HOThm20` remains the only open input of `homeomorph_pseudoArc_of_indec_homogeneous`.

The skeleton `doc/batches/skeletons/HO16C.lean` is split over nine files under `HPC/HO16/`:

* `StairDefs.lean` (the definitions of §§3–6: `HasConsCompl`, `sideOf`, `IsOrdinaryPt`, `IsGeneric`,
  `IsStraight`, `endSet`, `IsStairwellStr`, `HasStairwell`, `IsBrokenStairwellStr`,
  `HasBrokenStairwell`, `phiStar`, `foldPre`; skeleton text);
* `PLLib2.lean` (§2: components of `G \ (K ∪ P)`, ordinary points, intersections);
* `SidesLib.lean` (§3: workhorse lemmas on components, frontiers and sides, ending with the
  characterization `IsPLGraph.sideOf_char_aux`);
* `Sides.lean` (§3: the observations after Definition 9, Propositions 10 and 11);
* `StairLib.lean` (§§4–6: tools for straight sets, components, generic lists, the parity count);
* `Stairwell.lean` (§§4–6, §8: `ho16_obs12`, the observations on components, Claim 14.1, odd image,
  height one, Proposition 17, the remarks of p. 201, the fold of Proposition 19);
* `Lemma18.lean` (§7: Lemma 18);
* `StairExample.lean` (§5.4 certificate, §9 examples);
* `HO16C.lean` (imports the above; header lists the split).

`HPC.lean` ends with `import HPC.HO16.HO16C`; `lake build HPC` succeeds. No new file contains
`sorry`, `admit` or `axiom`.

`axioms.txt` has **2942 lines** (2824 + 118 added for 116 theorems, one output wrapped over three lines; none removed). `sorryAx` occurs in none of them.
Of the 116 new theorems (group "H–O Theorem 1, III (batch 195)" of `Axioms.lean`; copy in
`doc/batches/audits/axioms-batch195.txt`), 115 use exactly `propext`, `Classical.choice`,
`Quot.sound`, and one (`forall₂_exists_of_mem`, a list lemma) uses only `propext` (§4).

**Shape changes** (each also recorded at the statement). All are removals of hypotheses that the
proofs do not use, so every changed statement implies the skeleton's:
1. `IsPLGraph.comp_diff_mem_nhdsWithin`, `IsPLGraph.relFrontier_comp_diff`: `K ⊆ G`, `P ⊆ G`
   dropped.
2. `isOrdinaryPt_iff_order`: `x ∈ G` dropped (both sides force it).
3. `ho16_obs9_nhds`, `ho16_obs9_unique`: `A.Nonempty` dropped.
4. `ho16_obs9_char`: `IsConnected G`, `A.Nonempty`, `B.Nonempty` dropped.
5. `ho16_prop11_frontier`: `IsConnected G`, `A.Nonempty`, `Disjoint B₁ B₂` dropped.
6. `ho16_prop11_remark`: `A ⊆ G` dropped.
7. `ho16_rem17_P1`: `IsPLGraph G` dropped.
8. `ho16_prop19_fold`: `γ.Nonempty` dropped (the first step of Proposition 19 does not need it).

All other definitions and statements (12 definitions, 22 theorems) are textually the skeleton's
(checked by a script comparing each declaration with the skeleton, whitespace normalized). Added
beyond the skeleton: one auxiliary definition `IsPLPlusFinite` (a PL graph plus a finite set,
`PLLib2.lean`), the helper theorems listed in `Axioms.lean`, and the examples
`stairwell_example'` (the explicit structure of §9, with `𝓔(S₁) ≠ ∅`, `α₃ ≠ ∅`),
`broken_stairwell_example`, `lemma18_example`, `prop19_fold_example`.

**Omissions.**
* Proposition 14 and Claim 14.2 (not asked for, commission §1).
* The p. 201 remark on (S6′) (optional): discussed in words in `LEDGER.md` HO.20, no example given.
* The equivalence of `IsOrdinaryPt` with H–O's cutpoint definitions (not asked, §2.2).

Status lines:
* STATUS: §2.1 `IsPLGraph.finite_components_diff`, `comp_diff_mem_nhdsWithin`, `closure_comp_diff`,
  `relFrontier_comp_diff` proved
* STATUS: §2.2 `isOrdinaryPt_iff_order`, `IsPLGraph.finite_not_ordinary` proved
* STATUS: §2.3 `IsPLGraph.inter_eq_union_finite`, `IsPLGraph.inter_preimage_fst`,
  `isPLGraph_union_finite` proved
* STATUS: §3 `ho16_obs9_emptyB`, `ho16_obs9_emptyA`, `ho16_obs9_nhds`, `ho16_obs9_char`,
  `ho16_obs9_unique` proved
* STATUS: §3 `ho16_prop10` proved
* STATUS: §3 `ho16_prop11`, `ho16_prop11_frontier`, `ho16_prop11_remark` proved
* STATUS: §4 `ho16_obs12` proved
* STATUS: §5.1 `ho16_obs13_comp` proved
* STATUS: §5.2 `ho16_height_one` proved
* STATUS: §5.3 `ho16_claim14_1`, `ho16_odd_image` proved
* STATUS: §5.4 `ho16_p193_remark_false` proved
* STATUS: §6.1 `ho16_obs16_comp` proved
* STATUS: §6.2 `ho16_prop17`, `ho16_prop17_exists` proved
* STATUS: §6.3 `ho16_rem17_gamma`, `ho16_rem17_P1` proved
* STATUS: §7 `ho16_lemma18` proved
* STATUS: §8 `ho16_prop19_fold` proved
* STATUS: §9 `stairwell_example`, `broken_stairwell_example`, `lemma18_example`,
  `prop19_fold_example` proved

## 1. The items, in order

### §2. Library additions (`PLLib2.lean`)

* **§2.1.** Route as suggested: refine so that `K` is a union of edges and `P` consists of vertices
  (`IsPLGraph.exists_pieces`, from batch 194's `exists_refinement`); a component of `G \ (K ∪ P)`
  is a union of "pieces" (open edges and vertices) under "share a vertex not in `K ∪ P`"
  (`connectedComponentIn_eq_biUnion_pieces`), hence finitely many components
  (`finite_components_of_pieces`), each relatively open in `G`, with PL closure and frontier inside
  `∂(K ∪ P)`.
* **§2.2.** `IsOrdinaryPt G x`: two segments `[a, x]`, `[x, b]` meeting only at `x` whose union is a
  neighbourhood of `x` in `G`. `isOrdinaryPt_iff_order`: for every decomposition `S`, ordinary iff
  `x` is interior to an edge or exactly two edges end at `x`. The proof follows the sketch: near
  `x`, `G` is the fan of the edges at `x`; two segments through `x` covering the fan force at most
  two spokes, and at least two because each segment lies along a spoke (`posPar_of_mem_segment`,
  `exists_common_of_posPar`, `exists_small_step`). `IsPLGraph.finite_not_ordinary`: non-ordinary
  points are vertices.
* **§2.3.** `IsPLGraph.inter_eq_union_finite` (refine `A ∪ B`); `IsPLGraph.inter_preimage_fst` (on
  an edge, `Prod.fst` is affine: `segment_inter_preimage_fst`); `isPLGraph_union_finite` (a PL graph
  plus finitely many non-isolated points: they lie in `K`).

### §3. Definition 9, observations, Propositions 10 and 11 (`SidesLib.lean`, `Sides.lean`)

* The observations: `ho16_obs9_emptyB`, `ho16_obs9_emptyA`, `ho16_obs9_nhds`, `ho16_obs9_char`,
  `ho16_obs9_unique`, along the commission's sketches. The core is
  `IsPLGraph.sideOf_char_aux`: for a PL subgraph `A ⊆ G`, `B ⊆ ∂A` with consistent complement,
  `σ_B(A)` is a PL graph, `A ⊆ σ_B(A) ⊆ G`, `∂σ_B(A) = B`, and `σ_B(A) ∩ V = A ∩ V` for a
  neighbourhood `V` of `B` missing the closures of the finitely many components `C` of `G \ A` with
  `∂C ∩ B = ∅`. Connectedness of `G` and nonemptiness of `A`, `B` are not needed for it (shape
  change 4). `sideOf_empty_of_connected`: `σ_∅(A) = G` for connected `G` and `A ≠ ∅`.
* **Proposition 10** (`ho16_prop10`): first part from the characterization and uniqueness (or
  `σ_∅ = G` when `B = ∅`). Second part: **H–O's step is incomplete, as the commission reads it**
  (`LEDGER.md` HO.15). The formal proof does not shrink `V`; it derives `∂C ⊆ B` from consistency
  of `A` and a point of `C̄ ∩ B` (unstated in H–O), so that `C` is a component of `G \ B`
  (`IsPLGraph.comp_eq_of_relFrontier_subset`) missing `A`, hence missing `σ_B(A) = σ_B(A′) ⊇ A′`
  (`IsPLGraph.disjoint_comp_sideOf`); then `C ⊆ G \ A′ ⊆ G \ B` and `C` is the component of
  `G \ A′` through each of its points. The statement is as printed, with `B = ∅` allowed.
* **Proposition 11** (`ho16_prop11`): (F1) by the characterization; (F2) and (F3) by H–O's
  argument, with the finiteness of the components of `G \ A`, `∂C ⊆ B₁ ∪ B₂` and `∂C ≠ ∅` (`G`
  connected) supplied (`LEDGER.md` HO.16). `ho16_prop11_frontier`, `ho16_prop11_remark` proved.

### §4. Definition 12 (`StairDefs.lean`, `StairLib.lean`, `Stairwell.lean`)

`IsGeneric`, `IsStraight`, `endSet` as in the skeleton. `IsStraight.image_endSet`:
`π(𝓔(S)) = ∂π(S)`. **`ho16_obs12`**: for `U` open in `E × ℝ`, `π(U ∩ (S \ 𝓔(S))) = W ∩ G` for an
open `W`; `π|S` is a homeomorphism onto `π(S)` (compactness), and `π(S) \ ∂π(S)` is open in `G`.

### §5. Definition 13 and the remarks on pp. 193–194

Definition 13 was checked clause by clause against the page image of p. 192 (200 dpi): (S1)–(S5)
match `IsStairwellStr` (with `βᵢ = α (i + 1)`; the list of (S5) is `List.range' 2 (k − 1)`, i.e.
indices `2, …, k`). No mismatch.

1. `ho16_obs13_comp`: relative to `C = connectedComponentIn G p`. Uses that `C` is clopen in `G`
   (`IsPLGraph.isClosed_comp`, `comp_relOpen`), so frontiers (`relFrontier_inter_comp`), end sets
   (`endSet_inter_comp`), components of complements (`comp_diff_inter_comp`), consistency
   (`HasConsCompl.inter_comp`) and ordinary points (`IsOrdinaryPt.comp`) pass to `C`; genericity by
   `IsGeneric.of_forall₂`.
2. `ho16_height_one`: for connected `G`, `π(S) = G`, `π` injective on `S`, and `invFunOn π S` is
   continuous on `G` and a section.
3. `ho16_claim14_1`: with `Mᵢ = σ_{π(αᵢ₊₁)}(π(Sᵢ))` (and `M₀ = G`), Proposition 10 with (S3) gives
   `σ_{π(αᵢ₊₁)}(π(Sᵢ)) = σ_{π(αᵢ₊₁)}(π(Sᵢ₊₁))`, Proposition 11 gives `π(Sᵢ) = Mᵢ₋₁ ∩ Mᵢ` and
   `Mᵢ₋₁ ∪ Mᵢ = G`, and `M_k = G` (`β_k = ∅`); a parity count (`parity_count`) finishes. So the
   definition passes the test of §5.3. `ho16_odd_image` follows.
4. `ho16_p193_remark_false`: `G = [0, 1] ∪ [2, 3]`, `S = [0, 1] × {½}`, height 1.

### §6. Definition 16, Proposition 17, remarks on p. 201

Definition 16 was checked clause by clause against the page images of pp. 199–200 (200 dpi):
(S1′)–(S6′) match `IsBrokenStairwellStr`; `1 ≤ i₀ ≤ k` is explicit; finiteness of `𝓔(P₁)` is not a
clause of the definition (it follows from straightness). No mismatch.

1. `ho16_obs16_comp`: as §5.1.
2. `ho16_prop17` (relabelling explicit, `3 ≤ k` added as the commission proposed) and
   `ho16_prop17_exists`. The checks are the commission's list; the list of (S5′) is a permutation of
   a sublist of the list of (S5) (`IsGeneric.perm`, `IsGeneric.sublist`).
3. `ho16_rem17_gamma`, `ho16_rem17_P1` (with `G` connected; `𝓔(P₁) = ∅` makes `π(P₁)` clopen and
   nonempty).

### §7. Lemma 18 (`Lemma18.lean`)

`ho16_lemma18` in the skeleton's form. The claim (`lemma18_claim` over `∂F₁ = F₁ ∩ F₂`,
`lemma18_claim'` over `∂F₃ = F₂ ∩ F₃`) as in the commission's step 1; the pointwise facts
(`lemma18_points`: non-isolation and the frontier of `F ∩ φ⁻¹(π(S))` and of
`(F₁ ∪ F₂) ∩ φ⁻¹(π(S))`) from Lemma 6 (7) off `(∂F₂)⋆` (`lift_mem_closure`) and the claim on
`(∂F₂)⋆`; regularity from §2.3. `π(foldPre F S ∩ T⋆) = F ∩ T ∩ φ⁻¹(π(S))` is
`image_foldPre_inter`; injectivity of `π` on `foldPre F S` is `injOn_foldPre`.

### §8. Stretch: the fold of Proposition 19 (`Stairwell.lean`)

`ho16_prop19_fold`, by the commission's route: `ho16_obs9_unique` for
`π(P₁) = σ_{π(𝓔(P₁))}(π(P₂))`, `ho16_prop10` (with the `W` of (S3′)) for
`σ_{π(γ)}(π(S_{i₀})) = σ_{π(γ)}(π(P₂))`, `ho16_prop11` with `A = π(P₂)`, `B₁ = π(𝓔(P₁))`,
`B₂ = π(γ)` (disjoint by `𝓔(P₁) ∩ γ = ∅` and injectivity of `π` on `P₂`; `B₁ ∪ B₂ = ∂π(P₂)` from
`𝓔(P₂) = 𝓔(P₁) ∪ γ`), and `ho16_prop11_frontier` for (19.1)–(19.3). `γ ≠ ∅` is not used.

### §9. Non-vacuity examples (`StairExample.lean`)

`stairwell_example` (the commission's choice: `S₁ = [0, 2] × {¼}`, `S₂` from `(2, ¼)` to `(1, ½)`,
`S₃` from `(1, ½)` to `(3, ¾)`, `α₂ = {(2, ¼)}`, `α₃ = {(1, ½)}`, inside `[0, 3] × (0, 1)`);
`broken_stairwell_example` (`ho16_prop17` applied to it: height 1, pit at level 1);
`lemma18_example` (the batch-194 fold on `[0, 3]` and `S = [0, 3] × {½}`); `prop19_fold_example`
(the same broken structure, with `𝓔(P₁) = {(2, ¼)} ≠ ∅` and `γ = {(1, ½)} ≠ ∅`, over the connected
PL graph `[0, 3]`).

## 2. Non-vacuity notes

For each theorem whose hypotheses include a named `Prop` or a structure:

* **`IsStairwellStr`** (`ho16_obs13_comp`, `ho16_claim14_1`, `ho16_height_one`, `ho16_prop17`; and
  `HasStairwell` in `ho16_odd_image`, `ho16_prop17_exists`).
  1. *Satisfiable:* `stairwell_example` (height 3, connected `G = [0, 3]`, all of (S1)–(S5) with
     nonempty `α₂`, `α₃`), so `ho16_claim14_1`, `ho16_odd_image`, `ho16_prop17` (`k = 3`) and
     `ho16_obs13_comp` (with `C = G`) have instances; `ho16_p193_remark_false` exhibits a height-1
     structure (on a disconnected graph); a height-1 structure on a connected graph is
     `⟨[0, 3] × {½}⟩` with all `αᵢ = ∅` (`lemma18_example`'s set: (S1), (S2) with `𝓔 = ∅`, (S4)
     relative to `∅` by `hasConsCompl_empty`; checked by hand, not formalized).
  2. *Not equivalent to the conclusions:* the conclusions (odd count, `π(S) = G`, the homeomorphism,
     the broken relabelling, the restricted structure) are not clauses of Definition 13; Claim 14.1
     needs Propositions 10–11, and the restriction to a component needs that components are clopen.
* **`IsBrokenStairwellStr`** (`ho16_obs16_comp`, `ho16_rem17_gamma`, `ho16_rem17_P1`,
  `ho16_prop19_fold`).
  1. *Satisfiable:* `broken_stairwell_example`; for `ho16_prop19_fold` every hypothesis, including
     `𝓔(P₁) ≠ ∅` and H–O's `γ ≠ ∅`, is met by `prop19_fold_example`. For `ho16_rem17_gamma` and
     `ho16_rem17_P1` the extra hypotheses (`γ = ∅`, `𝓔(P₁) = ∅`) are not met by this example; they
     are the hypotheses of H–O's remarks, which Theorem 20 uses in its two terminal cases. They are
     consistent with Definition 16: a structure with `P₁ = P₂ = S₁ = [0, 3] × {½}` (height 1, pit
     at level 1, all `αᵢ`, `γ` empty) satisfies all clauses (checked by hand, not formalized).
  2. *Not equivalent:* the fold (F1)–(F3) and the two identities of Proposition 19 are not clauses
     of Definition 16; they need Propositions 10, 11 and the characterization.
* **`IsStraight`** (`ho16_obs12`, `ho16_lemma18`, the `StairLib` tools): satisfied by any
  horizontal segment over an interval (`isStraight_prod_singleton`) and any non-vertical segment
  (`isStraight_segment`); the openness of `π` on `S \ 𝓔(S)` and the conclusions of Lemma 18 are not
  clauses.
* **`HasConsCompl`** (`ho16_obs9_*`, `ho16_prop10`, `ho16_prop11`, `ho16_prop11_frontier`,
  `ho16_prop11_remark`): satisfied whenever `∂A ⊆ B` (`hasConsCompl_of_relFrontier_subset`) and for
  `B = ∅` (`hasConsCompl_empty`); the instances used in `stairwell_example` include
  `[1, 2] ⊆ [0, 3]` relative to `{1}` and to `{2}`, which meet every hypothesis of `ho16_prop11`
  (connected `G`, `∂[1, 2] = {1} ⊔ {2}`). The conclusions (regularity of the sides, the fold) are
  not clauses.
* **`IsSimpleFoldOf`** (`ho16_lemma18`, `lemma18_claim`, `lemma18_points`): `lemma18_example`
  meets every hypothesis of `ho16_lemma18` (first alternative of the frontier hypothesis).
* **`IsPLGraph`**, **`PairwiseEndpoints`**, **`IsOrdinaryPt`**: library notions; `isOrdinaryPt_Icc03`
  shows interior points of `[0, 3]` are ordinary.
* The certificate `ho16_p193_remark_false` has no hypotheses.

## 3. Ledger entries

In `LEDGER.md`, section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)", items
HO.13–HO.22. Quotations were checked against page images at 200 dpi (H–O pp. 190, 191, 192, 199,
200).
* **HO.13** (p. 183): the `IsOrdinaryPt` reading, its equivalence with order 2; cutpoint
  definitions not formalized.
* **HO.14** (p. 190 observations): verified; hypotheses used recorded (the characterization needs
  neither `G` connected nor `A`, `B` nonempty).
* **HO.15** (Proposition 10): the commission's reading **confirmed** — "we must have x∈B" needs
  `∂C′ ∩ B ≠ ∅`, not argued for a `C′` merely meeting `C ∩ V`. The formal proof avoids the step
  through the first part (above). Also unstated: `∂C ⊆ B`. Proposed classification: gap, statement
  true, not counted as a defective proof (left to the commissioner).
* **HO.16** (Proposition 11): the three unargued steps supplied; remark verified.
* **HO.17** (p. 192 observation): verified; "comple ment" typographical; Definitions 12, 13, 16
  match the page images.
* **HO.18** (pp. 193–194, "G connected"): agreed — omitted hypotheses, harmless, not counted (as
  HO.1); certificate `ho16_p193_remark_false`.
* **HO.19** (observations on components): verified relative to `C`.
* **HO.20** (Proposition 17): verified; `k ≥ 3` added; remarks of p. 201 verified; the (S6′) remark
  discussed in words; the p. 210 overstatement harmless.
* **HO.21** (Lemma 18): verified; regularity and the off-`(∂F₂)⋆` equivalence supplied; misprints
  of p. 202 recorded.
* **HO.22** (stretch, pp. 202–203): verified; `γ ≠ ∅` not needed for this step; the omitted
  citations recorded.

The count of defective proofs stays at sixteen.

## 4. Axioms

`doc/batches/audits/axioms-batch195.txt` contains `#print axioms` for the 116 new theorems (the
batch-195 group of `Axioms.lean`). 115 of them depend on exactly
`[propext, Classical.choice, Quot.sound]`; `forall₂_exists_of_mem` depends on `[propext]` only. (In
the audit file the line of `IsPLGraph.connectedComponentIn_inter_mem_nhdsWithin` is wrapped over
three lines by Lean's pretty-printer, so the file has 118 lines for 116 theorems.) `axioms.txt` (2942 lines) contains no `sorryAx`.

## 5. Dependency map of `homeomorph_pseudoArc_of_indec_homogeneous`

Unchanged from batch 193:

```
homeomorph_pseudoArc_of_indec_homogeneous        (HO16A)      proved, from HOThm20
├── pseudoArc_unique                              (HPC.Plane)  proved (earlier batches)
└── isPseudoArc_of_indec_homogeneous              (HO16A)      proved, from HOThm20
    ├── hagopian76_theorem1                       (HPC.Hagopian) proved (earlier batches)
    ├── theoremC                                  (HPC.Span)   proved (batch 192)
    └── ho16_theorem1_plane                       (HO16A)      proved, from HOThm20
        ├── HOThm20                               (Defs)       ** OPEN: named Prop hypothesis **
        ├── ho16_theorem4                         (Thm4)       proved
        ├── interior_eq_empty_of_hi               (Plane)      proved
        ├── exists_plGraph_approx                 (Grid)       proved
        ├── exists_path_approx                    (Plane)      proved
        ├── IsPLGraph.isCompact                   (Defs)       proved
        └── isSnakeLike_univ_of_epsMap            (HPC.Plane)  proved (earlier batches)
```

`HOThm20` is the only open input. **Now in place for its proof** (H–O §§4–6):
* batch 194: simple folds (`IsSimpleFoldOf`, `exists_simpleFold`), Lemma 6, Theorem 8 for folds,
  Proposition 7, the PL-graph library;
* batch 195: components of `G \ (K ∪ P)`, ordinary points, intersections; Definition 9 with the
  characterization of sides; Propositions 10 and 11; Definitions 12, 13, 16; the restriction of
  (broken) stairwell structures to a component; the height-1 homeomorphism; Claim 14.1;
  Proposition 17 and the remarks of p. 201; Lemma 18; the fold of Proposition 19 with
  (19.1)–(19.3).

**Still missing:** Theorem 15; Proposition 19 after its first step (pp. 203–209); Theorem 20.

## 6. Comments on the plan for Proposition 19 and Theorem 15

* **Proposition 19 (pp. 203–209).** After the fold, the proof applies `ho16_prop7` to pass to a
  connected component `C` of `F` with `φ(C) = G`, and Lemma 18 to the sheets: `S′ᵢ = φ⋆⁻¹(Sᵢ)` for
  levels away from the pit, `φ⋆⁻¹(S_{i₀}) ∩ (F₁ ∪ F₂)⋆`-type pieces near it. Lemma 18 is stated for
  `foldPre F S` in `F⋆ ⊆ (E × ℝ) × ℝ`, which is what is needed; the restriction to `C⋆` is
  `ho16_obs16_comp` / `ho16_obs13_comp` with `G := F` (relative to `C`, as the commission wanted).
  Expected new library needs: (a) **end sets of intersections** `𝓔(S ∩ C⋆)` when `C` is a component
  of `F` (present: `IsPLGraph.endSet_inter_comp`); (b) **genericity in `F`** of preimages of generic
  sets: a point of `G` which is ordinary and not in `∂G₁ ∪ ∂G₃` has ordinary preimages in `F`
  (Lemma 6 (7) gives local homeomorphisms off `∂F₂`, and genericity of `π(𝓔(P₁))`, `π(γ)` keeps the
  frontier points ordinary — a lemma "`IsOrdinaryPt` is preserved by local homeomorphisms between
  PL graphs" is needed); (c) **consistent complement in `F`**: components of `F \ π(S′)` versus
  components of `G \ π(S)`; this is where Proposition 10's second part is used (p. 208), and the
  referee's warning about `G′ᵢ ⊊ Gᵢ` after Proposition 7 applies — the identities (19.1)–(19.2)
  should be restated for `G′ᵢ = φ(Fᵢ ∩ C)`; `ho16_prop7` already gives that the restricted triple is
  a simple fold, so `ho16_lemma6` applies to it.
* **Theorem 15 (pp. 194–198).** It produces straight sets as graphs of continuous (not PL) height
  functions over PL subgraphs; `IsStraight` requires only `π(S)` PL, so no change is needed. The
  construction needs: a separator `M` of `G × {0}` from `G × {1}` in `G⋆`, a PL approximation, and
  the decomposition of its "graph-like" part into sheets with generic end sets. The library lacks
  (i) a general-position lemma (perturb finite sets off the finitely many non-ordinary points,
  `IsPLGraph.finite_not_ordinary` gives the finiteness), (ii) "a subcontinuum of a PL graph is a PL
  graph" (noted in report 194), and (iii) sections of `π` over components (the height-1 argument of
  `ho16_height_one` generalizes).
* **Encoding.** I would keep the encoding of Definitions 13 and 16 (one `α`, `βᵢ = α (i + 1)`,
  lists for generic families). One change worth considering before Theorem 20: Theorem 20 iterates
  Proposition 19 with a varying ambient space (`E`, `E × ℝ`, …) and a varying height `k` with a
  moving pit `i₀`; an existential form packaging "`S` contains a set with a broken structure of
  height `k` with pit at level `i`, over a connected PL graph in some normed space, with a map to
  `G` that is a composition of fold projections" will be needed, and stating it as a structure now
  would fix the interface. No change to the batch-195 definitions is required for it.

## 7. Files

The tarball `doc/batches/batch195-files.tar.gz` contains every file added or changed in this run
(including this report, the audit and the notes); the list is `doc/batches/batch195-MANIFEST.txt`.
