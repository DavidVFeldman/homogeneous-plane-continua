# Ledger of refutations

Statements made by Bing, Fugate, Nadler, Miller or the commissions (skeletons) that are false as
stated, with the Lean theorem that refutes them. Every Lean name below is in the main build and in
the group *Refutations* of `Axioms.lean` / `axioms.txt` (standard axioms only), unless marked
otherwise. File paths are relative to `HPC/`.

In batch 103 the sorried or commented-out copies of these statements were deleted from the sources;
each deletion left a one-line pointer to this file. Section 2 lists the statements that were
deleted although they are not refuted (superseded, moot or too strong; batches 103 and 111); section 3 a proved theorem
with a refuted hypothesis that was kept; section 4 what the formalization of Fugate 1969 needed
beyond his text, and the final entry for Bing's Duke Theorem 11; section 5 (batch 116) what the
proof of Bing 1948, Theorem 14 needed beyond his sketch, and how it relates to Theorem 9 and to
Lehner 1961.

## 1. Refuted statements

### Bing 1948 and its skeletons

| statement (source) | refutation (Lean) | explanation |
|---|---|---|
| Theorem 8 as printed (Bing 1948) | `HPC.Fold.not_theorem8_literal` (`Fold/Theorem8Counter.lean`) | Two six-link chains crooked in a four-link chain, following `bingPattern 4`, whose unions of corresponding links form no chain; corrected form `HPC.Fold.theorem8`. |
| `theorem8` (skeleton form, batch 79) | `HPC.Fold.theorem8_skeleton_false` (`Fold/Theorem8Counter.lean`) | Orientation ignored: for a three-link `D`, `D.reverse` meets every hypothesis but does not follow `bingPattern 3`. |
| `theorem6Pos_shift` (skeleton, no `P ≠ Q`) | `HPC.Description.not_theorem6Pos_shift_unconditional` (`PseudoArc/Theorem5.lean`) | A description of the one-point space with `P = Q`: the pattern `0, 0` cannot be followed by a two-link chain from `P` to `P`. |
| `patternFollowing` (skeleton, no `P ≠ Q`) | `HPC.Description.not_patternFollowing_unconditional` (`PseudoArc/Theorem5.lean`) | Same one-point description. |
| `exists_rect_chain_following` (skeleton's planar step, batch 84) | `HPC.Plane.rectStepSkeleton_false` (`Plane/Counter.lean`) | Three rectangles with room; the middle fine link must reach both outer coarse links, so its diameter is at least 9 whatever `ε`. |
| `theorem12_of` (skeleton: compact described sets suffice) | `HPC.Plane.theorem12_of_false` (`Plane/PseudoArc51.lean`) | A description in a non-complete space can describe a two-point set, which is not homeomorphic to the plane pseudo-arc. |
| `isPseudoArc_of_description` (skeleton) | `HPC.Plane.isPseudoArc_of_description_false` (`Plane/PseudoArc51.lean`) | Same description: compact but not connected. |
| Theorem 3 as printed (Bing 1948), end clause read *respectively* (`Theorem3Literal`, batch 121) | `HPC.Fold.Recon121.not_theorem3Literal` (`Fold/Recon121.lean`) | Three coarse links (strips), five rectangles, basepoint 2: the end links lie in the middle strip and reach into both outer strips, so the respective clause puts their blocks in `D_1`, and no two-link block map separates them from links 1 and 3. Bing's own wording ("meets `e₁` or `e_m` … subset of `e₁ + e₂` or `e_{m−1} + e_m`", `Theorem3LiteralOr`) is **not** refuted: for `k = 3` it follows from the main clause, for `k ≥ 4` the readings coincide (`endClause_or_iff`). The statement as printed, every clause including the only-clause, is **proved** in batch 124: `HPC.Fold.theorem3_literal`, `HPC.Fold.Recon121.theorem3LiteralOr_holds` (`Fold/Theorem3Pair.lean`), through the pair form `HPC.Fold.theorem3_pair`. |
| Theorem 3, Bing's proof, special case (Bing 1948, p. 732) | — (statement **proved**: `HPC.Fold.theorem3_bing`, two-link form, end clause, "or" reading; the only-clause added in batch 124, `HPC.Fold.theorem3_literal`; the proof as written fails in its special case, certificate `HPC.Fold.Recon121.seam_every_H_fails`, with `seamD_special`, `seamD_hk`, `seamIH_H0`, `seam_Cbot_fails`) | Eleven links of a realized chain over five strips satisfy the special-case hypotheses with `(h, k) = (4, 6)` forced; an `H` satisfying the induction hypothesis exists, but for every basepoint `i ≤ h` and every `H` the literal `F = H(1, u−1) ⌢ (level groups of D′) ⌢ D(k+1, n)` is not a chain with `d_i` first. Repaired (batch 122, `HPC.Fold.Recon122.bing_main`) by three changes, none of which is in the text: (1) the level groups read bottom-anchored (`cbotG`); (2) an explicit grouping at five coarse links (`special_five`); (3) the branch `d_i ∈ D(h, k)` by the induction hypothesis on `D(h, k)` inside `E(2, r−1)` (`special_middle`). REPORT-batch121.md §4, REPORT-batch122.md. |
| Theorem 4 as printed (Bing 1948, p. 733), degenerate case `m = 3`, `r = s` (`Theorem4Literal`, skeleton of batch 123) | `HPC.Fold.not_theorem4Literal`, `HPC.Fold.theorem4_two_degenerate_false` (`Fold/Theorem4Two.lean`) | Three intervals in `ℝ` crooked in three intervals; the middle fine link meets the first and the last coarse link, so `D(r, s) = d_r` satisfies the hypothesis, and `d_r` in the first and in the last link of `F` forces `F` to have one link, all of `D`, which lies in no two adjacent links of `E`. The only-clauses play no role. Outside this case the two-link form is proved (`HPC.Fold.theorem4_two`, hypothesis `r < s ∨ m ≠ 3`); the only-clauses are refuted for `m = 3` (next row) and **proved** for `m ≥ 4` (batch 125, `HPC.Fold.theorem4_literal_ge4`). |
| Theorem 4 as printed (Bing 1948, p. 733), only-clauses, `m = 3`, `r < s` (`Theorem4LiteralND`, batch 123) | `HPC.Fold.not_theorem4LiteralND` (`Fold/Theorem4Only.lean`) | Batch 124. In `ℕ` (discrete, every set open): coarse links `{0,1,5}`, `{1,2,4,5}`, `{2,3,4}`; fine links `{5}`, `{4,5}`, `{2,3,4}`, `{1,2}`, `{0,1}`; `r = 0`, `s = 1`, `d₀ ⊆ d₁`. `D(r, s)` meets the first and the last coarse link, but `d₁` in the last link of `F` with `d₀` only in the first forces `F` to have a single link, all of `D`, which lies in no two adjacent links of `E`. The two-link form without the only-clauses holds (`theorem4_two`); with `m ≥ 4` the statement as printed, every clause, is **proved** in batch 125 (`HPC.Fold.theorem4_literal_ge4`, `HPC.Fold.theorem4LiteralGe4_holds`). So Theorem 4 as printed is false as a statement about `m = 3` and proved for `m ≥ 4`. |

### The Theorem-3 campaign (Bing 1948, Theorem 3; commissions of batches 17–60)

| statement (commission) | refutation (Lean) | explanation |
|---|---|---|
| `exitReach`, `highExitValleyOpen`, `lowExitPeak`, and the corollaries `highExitValley`, `f2Prime` | `not_exitReach`, `not_highExitValleyOpen`, `not_lowExitPeak`, `not_highExitValley`, `not_f2Prime` (`HPC.Fold.*`, `Fold/Closure.lean`) | Explicit crooked sequences; Theorem 3 by this route was replaced (Theorem 3 is now proved, `HPC.Fold.theorem3`). |
| `exitReachTight`, `highExitValleyOpenTight`, `lowExitPeakTight`, `highExitValleyTight`, `f2PrimeTight` | `not_exitReachTight`, `not_highExitValleyOpenTight`, `not_lowExitPeakTight`, `not_highExitValleyTight`, `not_f2PrimeTight`, and `not_f2PrimeFree` (`Fold/ClosureTight.lean`) | The tight forms fail too; `theorem3_of_F2PrimeFree` keeps the implication with a false hypothesis. |
| `exitReachF`, `f2PrimeF` | `HPC.Fold.not_exitReachF`, `HPC.Fold.not_f2PrimeF` (`Fold/ExitReachFWitness.lean`) | A forty-two-term member of the faithful model, basepoint 2. |
| `highExitValleyF`, `lowExitPeakF` | `HPC.Fold.not_highExitValleyF`, `HPC.Fold.not_lowExitPeakF` (`Fold/ValleyFWitness.lean`) | A seventy-one-term member of the faithful model. |
| `exists_cutData` (batch 26) | `HPC.Fold.not_cutData`, `HPC.Fold.not_exists_cutData_cutSeq` (`Fold/CutRoute.lean`) | `CutData` is empty for every sequence; the hypotheses are met by `cutSeq`. |
| `offDichotomy` (batch 24) | `HPC.Fold.not_offDichotomy` (`Fold/DichotomyFaithful.lean`) | Basepoint 57, level 3, of the 409-link chain `bing 0 8`. |
| `f2PrimeOff` (batches 23–24) | `HPC.Fold.not_f2PrimeOff_of_faithful` (`Fold/SpanWitness.lean`) | **Conditional**: refuted given the faithfulness hypothesis `IsCrookedIvF ceSeq10 ceSeq10`, which is not discharged in Lean. |
| `extendStepMin` (batch 35) | `HPC.Fold.not_extendStepMin` (`Fold/Minimal2.lean`) | Explicit witness on `[0, 6]`. |
| `s3Zig` (batch 28) | `HPC.Fold.not_s3Zig` (`Fold/Zigzag.lean`) | `cutSeq` at basepoint 0: thirty-seven links of `bing 0 8`, first link at the bottom level. |
| `arm_timing` (batch 31) | `HPC.Fold.not_armTimingClaim` (`Fold/Interior.lean`) | A basepoint one level below the top reaches the top in one index, whatever the span. |
| `unserved_high8` (batch 44) | `HPC.Fold.not_unservedHigh8` (`Fold/Bing9Witness.lean`) | `bing 0 9`, basepoint 278. |
| `unserved_ceiling`, `unserved_valley` (batch 45) | `HPC.Fold.not_unservedCeiling`, `HPC.Fold.not_unservedValley` (`Fold/Bing9ShaveWitness.lean`) | `bing 0 9` with one peak shaved, basepoints 336 and 138. |
| `cross_ceil_profile` (batch 48) | `HPC.Fold.not_crossCeilProfile` (`Fold/CrossWitness.lean`) | Basepoint 336 of `bing9sB`. |
| `unserved_profile`, `unserved_leg3deep` (batch 48) | `HPC.Fold.not_unservedProfile`, `HPC.Fold.not_unservedLeg3deep` (`Fold/CrossWitness.lean`) | Same basepoint; `Leg3Ceil` is necessary for the third walk. |

### Bing 1951 (Duke) and its commissions

| statement (source) | refutation (Lean) | explanation |
|---|---|---|
| `theorem8_1951` (the batch-92 commission's one-layer reading of Bing's Theorem 8; not Bing's statement) | `HPC.Plane.Counter92.theorem8_1951_false` (`Plane/Atriodic51CounterBing.lean`) | `theorem8_1951` takes `g p` to be "the intersection of all continua containing `p` interiorly" (the one-layer reading). Bing (p. 658) defines `g_p` as "the intersection of all continua which contain interiorly a continuum that contains p interiorly", and with that definition the theorem holds (`theorem8_1951'`, batch 93). For the one-layer reading, the planar continuum `S₀` (two sine curves over a bar) satisfies `BingS`, but `q ∈ g p` with `g p ≠ g q`, and the step "`H_1` contains `H_2` interiorly" of the proof fails. The refutation and the failure of the proof step are for the reading, not for Bing. |
| `isArc_of_separatesPairs` (batch 92) | `HPC.Plane.Counter92.isArc_of_separatesPairs_false` (`Plane/Atriodic51CounterArc.lean`) | The decomposition space of `S₀` is not Hausdorff (`Counter92.quotient_not_t2`). |
| `not_separation_of_accumulates` (batch 96 skeleton) | `HPC.Plane.not_separation_of_accumulates_false` (`Plane/Theorem11.lean`) | `N` may miss a point of `g` while containing the nearby points of `K ∖ g`; counterexample on `[0, 1]`. Corrected: `not_separation_of_accumulates'`. |
| `exists_degenerate_interior_elt` (Q-deg, batch 96; live `sorry` until batch 103) and `exists_degenerate_interior_elt'` (batch 97) | `HPC.Plane.exists_degenerate_interior_elt_refuted` (`Plane/Layers51.lean`) | The Cantor organ is a `BingS` space none of whose elements is degenerate. |
| `bingElt_degenerate_of_isContPt` (Q3, batch 97) | `HPC.Plane.bingElt_degenerate_of_isContPt_refuted` (`Plane/Layers51.lean`) | In the Cantor organ every element is a nondegenerate arc, and points over good parameters are continuity points. |
| reverse of `bingElt_subtype_subset` (batch 94, Q2) | `HPC.Plane.Counter92.bingElt_subtype_reverse_false` (`Plane/NonCut51Counter.lean`) | On `S₀` with `S' = [0, 2] × {0}`. |
| `lastLink_of_minimal` (skeleton, batch 99) | `HPC.Plane.lastLink_of_minimal_skeleton_false` (`Plane/LastLink99.lean`) | `D = (ℝ, ℝ)`, `K = {0}`, `p = 0`, `F = (ℝ)`: no point of `K` differs from `p`. |
| `isSnakeLike_union_of_terminal` (gluing question, batch 98) | `HPC.Plane.isSnakeLike_union_of_terminal_refuted`, `HPC.Plane.two_organs_counterexample` (`Plane/Organ98.lean`) | Two organs glued along a terminal layer form a triod; also `arcs_counterexample` (two arcs meeting in one point). |
| Theorem 11, sufficiency (Bing's proof, p. 660) | — (not refuted: proved, `HPC.Plane.theorem11_1951`, `Plane/Theorem11B.lean`) | Three sentences of the proof are unargued; final form of the entry in §4. |
| Bing 1951 (Duke), Theorem 7: stated for tree-like continua, proved by reference to the proof of Theorem 6, which assumes no subcontinuum separates the plane | — (not refuted: proved, batch 133) | The implication "tree-like ⇒ no subcontinuum separates the plane" is not stated or proved in the paper (classical). Proved: `HPC.Plane.treeLike_nonseparating` (`Plane/TreeLikeNS.lean`, batch 133); Theorem 7 as printed is `HPC.Plane.theorem7_1951_treeLike`, Theorem 6 with its converse `HPC.Plane.isTreeLike_iff_nonseparating`. |

### Bing 1948 / 1951: the two notions of crookedness

| statement | Lean | explanation |
|---|---|---|
| "1951-crooked implies 1948-crooked" (COMMISSION.md, T3) | `HPC.isCrookedIn_ne_isCrookedIn'` (`Chains/Counterexample.lean`) | Four vertical strips and six rectangles in `ℝ × ℝ`. |

### Fugate 1966, Miller 1950, Nadler

| statement (source) | refutation | explanation |
|---|---|---|
| `isFugateTriod_iff_isTriod` (batch-100 skeleton) | — (no Lean refutation; REPORT-batch100.md) | The θ-curve is a Fugate triod (common part `{x, y}` not connected) but not a triod. Proved instead: `isFugateTriod_of_isTriod`, `isTriod_of_isFugateTriod_of_hu`, `isSorgenfreyTriod_iff_isTriod`. |
| `isTriod_union_of_three` without hypothesis (batch-100 skeleton) | — (no Lean refutation; REPORT-batch100.md) | The circle as the union of three arcs. The corrected form (inside a hereditarily unicoherent continuum) is proved. |
| `miller_1_5` (Miller 1950, Theorem 1.5, as transcribed) | `HPC.Plane.miller_1_5_false` (`Plane/Fugate66BMiller.lean`) | The closed disk as the union of two half-disks; its boundary circle lies in neither half. Corrected: `miller_1_5_of_hu`. |
| Corollary 1 (Fugate 1966, p. 467), sufficiency, as stated | — (**not refuted**; proved, batch 132) | Stated without proof. True: proved (batch 132) via (∗), from Ingram 1968 (`HPC.Plane.fugate_cor1`, `Plane/Ingram68.lean`; (∗) is `ingramStar_holds`, by the direct route through Ingram's Lemmas 1–2 rather than his Theorem 2(2)). The induction through Theorem 1 that Fugate presumably intends needs (U), which holds (`fugateU_holds`) but is not elementary. History: open in batches 101–131 (`fugateU_iff_cor1Sufficiency`, batch 124; REPORT-batch124 §Q4). |
| Fugate 1966, introduction (p. 460) versus Theorem 1 (p. 466) | — (harmless) | The introduction says 'a-triodic and hereditarily unicoherent', the theorem 'a-triodic and unicoherent'. Equivalent for two pieces (Miller 1.5 / `isHereditarilyUnicoherent_union`); harmless. Barrett's MR review follows the introduction; the zbMATH review, Ingram 1968 and Alhassan 2020 follow the theorem. |
| Ingram 1968, Lemmas 1–3: appeals to Sorgenfrey 1944, Theorem 1.8 | — (no defect found; replaced) | Each appeal checked: the three continua do have a common point and none lies in the union of the other two. In the formalization the appeals in Lemmas 1 and 2 are replaced by the core lemma `isTriod_of_core` (`Plane/Ingram68Core.lean`); for Lemma 2's terminality the core `(H ∪ L₁) ∩ (H ∪ L₂)` is a continuum only when `A` is hereditarily unicoherent, so `ingram_lemma2` carries that extra hypothesis (true in the application, `A` snake-like). Lemma 3's two steps flagged in COMMISSION-batch132.md §3.4 ("since `M₂` is a subcontinuum of `A`": `M₂ ⊆ H ∩ A = L₁ ⊔ L₂` is connected and meets `L₁`; Case 2: `L₁ ∩ (H ∩ B) ⊆ L₁ ∩ K = ∅`) are correct. Lemma 3 itself is not formalized and not needed. Theorems 1 and 2 were not checked (direct route). |
| `isConnected_diff_of_superset` (Nadler 11.28, as transcribed) | `HPC.Plane.isConnected_diff_of_superset_false` (`Plane/SorgenfreyLemmas.lean`) | `H = Ū` gives `U ∖ H = ∅`. Corrected: `isConnected_diff_of_superset'`. |

### Models of the open items (reconnaissance)

| statement | refutation | explanation |
|---|---|---|
| the time-ordering fold for `covering_step` (batch 86) | `HPC.Fold.model_covering_fold_refuted` (`PseudoArc/Recon86Model.lean`) | Fails in the model under all the stated hypotheses. |
| the three-link fold (batch 87) | `HPC.Fold.model_covering_fold₃_refuted` (`PseudoArc/Recon87Model.lean`) | Fails in the model; the link of `Q'` is adjacent to that of `P'`. |
| the end-time lemma for `theorem3_end` (batch 87) | `HPC.Fold.model_end_time_refuted` (`Fold/Recon87End.lean`) | Fails in the model under crookedness, the window property and separation. |

### Commission slips: skeleton refutations (batches 107, 109)

These statements were claimed by the commissions' skeletons (the last, batch 133, by a repository
definition), not by the sources (Bing's
proofs do not need them); each is a slip in the skeleton, refuted at the boundary case and replaced
by a corrected form.

| statement (source) | refutation (Lean) | explanation |
|---|---|---|
| `squeeze_stdRect_subset` (batch-107 skeleton, Duke Theorem 5): `closure (squeeze b '' stdRect j) ⊆ stdRect j` | `HPC.Plane.not_squeeze_stdRect_subset` (`Plane/Thm5.lean`) | The squeezes fix the first coordinate, so the closure of the image contains the point `(2j, (1/2 + c)/3)` on the left side of the rectangle, which is not in the open rectangle `stdRect j`; false for every `b`, `j`. Corrected: `squeeze_image_stdRect_subset`. |
| `stripSet_eq` (batch-109 skeleton, density lemma) at `m = 0`: `stripSet m = (0, 2m+1) × (0, 1)` | `HPC.Plane.stripSet_zero_ne` (`Plane/Band.lean`) | `stripSet 0` is an empty union, the square `(0, 1) × (0, 1)` is not empty. Corrected: `stripSet_eq` with `0 < m`. |
| `stretchTri_subset_ball` (batch-109 skeleton) for `k > n`: the stretch triangle `k` lies in the closed ball of radius `δ/2` about `c k` | `HPC.Plane.stretchTri_subset_ball_false` (`Plane/Band.lean`) | With no steps (`n = 0`) and `c i = (10 i, 0)`, the stretch triangle `1` contains the midpoint of `c 0` and `c 1`, at distance `5δ` from `c 1`. Corrected: `stretchTri_subset_ball` with `k ≤ n`. |
| `stretchTri_subset_thickening` (batch-109 skeleton) at `n = 0`: each stretch triangle lies within `δ/2` of the polygonal path | `HPC.Plane.stretchTri_subset_thickening_false` (`Plane/Band.lean`) | A path with no steps has an empty polygonal path, while the stretch triangle `0` contains the point `c 0`. Corrected: `stretchTri_subset_thickening` with `0 < n`. |
| Repository definition `IsTreeLike` (batch 117, `Plane/Tree67.lean`): links of diameter `< ε`, boundedness omitted | `HPC.Plane.isTreeLikeOld_of_isContinuum` (`Plane/TreeLikeNS.lean`; old definition kept as `IsTreeLikeOld`) | Mathlib's `diam` of an unbounded set is `0`, so `{univ}` is a tree chain of every mesh and every continuum satisfied `IsTreeLike`; `theorem6_1951` (conclusion `IsTreeLike M`) was vacuous until batch 133, and the open question `treeLike_nonseparating` was false as stated (a circle). Commission slip. Repaired in batch 133: links must be bounded (`Bornology.IsBounded A ∧ diam A < ε`, as in `IsEpsChain`); `theorem6_1951` re-proved (its links are polygon interiors, bounded), `treeLike_nonseparating` proved. No other statement changed meaning. |

The supporting lemmas of the `S₀` counterexample (`HPC.Plane.Counter92.*`) are listed in the audit
as well.

## 2. Deleted statements that are not refuted (batches 103 and 111)

### Commented-out statements deleted in batch 103

| statement (file before) | status |
|---|---|
| `s3` (`Fold/Choice`, `Interior`, `ZigFree`, `Span`) and `theorem3` (`Fold/Closure`, `ClosureF`, `ClosureTight`, `Dichotomy`, `Interior`, `OffCenter`, `Span`, `ZigFree`) | **Proved**: `S3` is `HPC.Fold.Z77.s3_zig`, Theorem 3 is `HPC.Fold.theorem3` (`Fold/Open.lean`). |
| `s3ZigFree`, `s3ZigFreeInterior` (`Fold/Choice`, `Interior`, `ZigFree`) | Neither proved nor refuted; no longer needed (their purpose, `S3`, is proved directly). |
| `s3ZigFreeInterior_of_cutWalk`, `cutWalk'` (`Fold/CutRoute`) | Equivalent to `S3ZigFreeInterior` (`cutWalk'_iff_s3ZigFreeInterior`; `CutWalk` holds vacuously by `not_cutData`); open and moot as above. |
| `s3_span_nine` (`Fold/General`), `s3_span_nine_mid5`, `s3_span_nine'` (`Fold/Mixed`) | **Proved** with the same names and statements in `Archive/Target73.lean` (batch 73). |
| `extendStep` (`Fold/Step`) | The commissioned form is unproved; the corrected form was refuted by census only (REPORT-batch34.md), not in Lean. Moot. |
| `hStarArm_eq_of_peak_on_T'` (`Fold/Witnesses`) | The commissioned form misses a hypothesis; the corrected form `hStarArm_eq_of_peak_on_T` is proved. No Lean refutation. |
| `theorem10_1951_of_step` (`Plane/Recon91`) | Superseded: as hard as Theorem 10, which is now proved (`HPC.Plane.theorem10_1951`); replaced by `theorem10_1951_of_endPoint`. |

### Statements deleted in batch 111 (COMMISSION-batch111.md §1(a))

| statement (file before) | status |
|---|---|
| `exists_tame_chain_near` (`Plane/Most51.lean`, open `sorry` since batch 90) | Neither proved nor refuted; deleted as too strong. It was the batch-90 skeleton's own intermediate and asked for a tame chain near every continuum, i.e. a *homeomorphism of `E`* carrying the standard boxes onto the links, which is more than `exists_pseudoArc_in_tameChain` uses (batch 109: the threaded form `GeomLemma'` suffices, `geomLemma'_of_geomLemma`, `dense_pseudoArcs_of'`). The batch-90 obstruction (REPORT-batch90.md, item 7) was an obstruction to that excess. Replaced by the weak open statement `geomLemma'_of_two_le_rank` (`Plane/LatticeCycle.lean`), proved in the plane (`geomLemma'_of_finrank_two`). Its conclusion as a hypothesis, `GeomLemma E`, stays (with `dense_pseudoArcs_of`, `theorem2_HIC_of`, proved); partial results stay in `Archive/Most51Geom.lean`. |
| `dense_pseudoArcs` (`Plane/Most51.lean`, proved from `exists_tame_chain_near`) | Re-added with the same statement in `Plane/LatticeCycle.lean`, now proved from `geomLemma'_of_two_le_rank`. |
| `theorem2_HIC` (`Plane/Most51.lean`, proved from `exists_tame_chain_near`) | Re-added with the same statement in `Plane/LatticeCycle.lean`, now proved from `geomLemma'_of_two_le_rank`. |

## 3. Kept: a proved theorem with a refuted hypothesis

`HPC.Plane.theorem11_1951_of_T10` (`Plane/Theorem11.lean`) and `theorem11_1951_iff_of_T10` are
proved, but their hypothesis `hdeg` (every compact `BingS` space in the universe of `S` has a
degenerate interior element) is refuted in universe `0` by `HPC.Plane.theorem11_hdeg_refuted`
(`Plane/Layers51.lean`). The commission asked for `theorem11_1951_of_T10` to be deleted; it was kept
because `theorem11_1951_iff_of_T10` depends on it and because the refutation covers only universe
`0` (see `doc/batches/REPORT-batch103.md`).

## 4. Fugate 1969

J. B. Fugate, *A characterization of chainable continua* (Canad. J. Math. 21, 1969), Lemma 3,
Lemma 4 and Theorem 2, Case II, formalized in batch 104 (`Plane/Theorem11B.lean`). No statement of
Fugate's is refuted. The list records what the formal proof needed beyond his text (from
`doc/batches/REPORT-batch104.md`).

1. **Lemma 3, "Clearly `A ⊆ R`".** Replacing `R` with `R ∪ A` keeps (†), and `R ∪ A` still meets
   `A`.
2. **Lemma 3, "points `p ∈ R` and `q ∈ K`".** Lemma 2 only gives `K ∪ R` irreducible between a point
   `q` of `K` and some point `p`. Getting `p ∈ R ∖ K` requires `R ⊄ K`, which Fugate does not argue.
   It is proved from Sorgenfrey's theorem: an irreducible pair `r₁, r₂` of `R` avoids `A`, by (†);
   if `R ⊆ K`, the pair lies in `B`, so `R ∩ B = R` by hereditary unicoherence and irreducibility;
   that gives `A ⊆ R ⊆ B` and `K = B`, a contradiction. Without this, the case `R ⊆ K` is a real gap
   in the text (`isTerminalSub_of_union_terminal`).
3. **Lemma 3, the "similar" case `R ⊆ S ∪ K`.** The mirror image, with the same core lemma. Fugate's
   remark "`q ∈ B − (L ∩ (S ∪ K)) ⊆ S`" is not needed: properness only needs `q ∈ K ⊆ S ∪ K` and
   `q ∉ L`.
4. **Lemma 3, "`L ∩ (S ∪ K)` is a continuum".** Hereditary unicoherence, unstated by Fugate
   (`isContinuum_inter_of_hu`).
5. **Lemma 4, inductiveness.** A two-line argument by monotonicity replaces Fugate's
   (`isTerminalSub_iInter`; Lemma 4 in the hereditarily decomposable case is
   `exists_terminal_point_of_isTerminalSub`).
6. **Claim 1, the choice of `s`** ("there is `s ∈ V ∩ f⁻¹(0, f(t)) ∩ (B − A)`"). With Bing's
   elements in place of `f`, this needs `exists_nbhd_not_separated` together with Theorem 8 (a).
   Upper semicontinuity (`bingElt_usc`) is not used.
7. **Claim 1, `W(s)` is a continuum.** From unicoherence of the space, using the sides of `g_s` and
   `V_s ⊆ V` (`claim1_contains_inter`).
8. **"`K` is a terminal subcontinuum of `Cl(B − A)`".** The triod `R ∪ L ∪ A` needs `A ⊄ R ∪ L`,
   which holds because `U ≠ ∅` and `U ∩ cl V = ∅`; the hereditary unicoherence hypothesis of
   `isTriod_union_of_three` is `BingS`.
9. **Claim 2, "`N` must intersect `A ∩ Cl(B − A)`".** Uses the connectedness of `N` and `M = A ∪ C`;
   "`N ∩ Cl(B − A)` is a subcontinuum" uses hereditary unicoherence of `M` (`claim2`).
10. **The displayed chain.** Fugate's chain is in general only a weak chain: links may be empty, and
    `E_x ∩ S` need not meet `(F_y ∩ T) ∪ U`. It is trimmed (`exists_chain_of_weak`). The mesh is
    `ε`, because `(F_y ∩ T) ∪ U ⊆ F_y` (`epsCoverable_of_halves`).
11. **Bing's Theorem 11 along Fugate's lines.** Bing's `K` becomes `C = Cl(B − A)` and his `p'`
    becomes `μ`, a terminal point of both halves (`exists_mu`); Bing's separation of `S − N` is
    Claim 2 (with Moore's theorem 44); Bing's displayed chain is the trimmed weak chain of item 10.
    Theorem 10 is not used, nor the degenerate interior element refuted in batch 96
    (`theorem11_hdeg_refuted`); Lemma 4 (hereditarily decomposable case) and Lemma 1 (Fugate 1966,
    `fugate_lemma1`) replace them.

### Bing 1951 (Duke), Theorem 11 — final form of the entry

Theorem 11 is true and proved (`HPC.Plane.theorem11_1951`, `HPC.Plane.theorem11_1951_iff`;
necessity in batch 96, sufficiency in batch 104). Bing's proof of sufficiency (p. 660) has three
unargued sentences:

1. "there is an uncountable collection `G'` of `G` such that … there is a sequence of elements of
   `G` converging to `g'` such that infinitely many elements of this sequence separate `g'` from
   `g₁` and infinitely many separate `g'` from `g₂`";
2. "`p'` satisfies condition A for `M` equal to either `H` or `K`" (for the point `p'` chosen in
   `g'`);
3. "`S − N` is the sum of two mutually separated sets `H'` and `K'` such that `H'` contains `H − N`
   and `k₁, …, k_n` covers `K'`" — read with the implicit "`h₁, …, h_m` covers `H'`", needed for
   Bing's displayed chain in any case (batch 104 commission; the stronger reading with
   `K' ⊇ K − g' − N` is the one refuted by `not_separation_of_accumulates'`).

Sentences 2 and 3 are supplied by Fugate 1969: the separation (3) is Fugate's Claim 2, proved from
Claim 1 (`claim1_contains_inter`, `claim2`), and the point (2) is replaced by a terminal point `μ` of
both halves `A` and `Cl(B − A)`, given by Lemma 4 (`exists_terminal_point_of_isTerminalSub`,
`exists_mu`); Bing's `p'` need not even lie in `Cl(B − A)`, so his own choice does not supply it in
general. Sentence 1 (the "uncountable `G'`") does no work: the proof needs only one element that is
not an end element (`exists_not_endElt`), and it need not be degenerate (the Cantor organ has no
degenerate element, `exists_degenerate_interior_elt_refuted`). Theorem 10 is not needed: Fugate's
Lemma 1 (Fugate 1966, `fugate_lemma1`) gives the chains with `μ` in the last links.

## 5. Bing 1948, Theorems 9 and 14, and Lehner 1961

Batch 116 (COMMISSION-batch116.md §1.2); the proofs are those of batches 114 and 115
(REPORT-batch114.md, REPORT-batch115.md). Nothing in this section is a refutation, and §1 has no
new entry.

**The covering descriptions.** Theorem 14 says: "That there exist such sequences follows as a
consequence of Theorem 9." This is not a proof. The sequences (descriptions whose levels cover `W`
from `P'` to `R`) are supplied by Lehner's Lemma 3 for `n = 2` (G. R. Lehner, *Extending
homeomorphisms on the pseudo-arc*, Trans. AMS 98 (1961), pp. 375–376), proved in batch 114 as
`HPC.lehner_lemma3_two` (`PseudoArc/Lehner.lean`): one level is crooked in the previous one, and
Lehner's chain counting is carried out on that. The batch-86/87 reformulations through folds
(`Description.coveringStep_of_folds`, `Description.coveringStep_of_folds₃`, and the end-time lemma)
are not the route. Their refutations (`model_covering_fold_refuted`, `model_covering_fold₃_refuted`,
`model_end_time_refuted`, §1 *Models of the open items*) stand as refutations of those
reformulations and say nothing against Theorem 14.

**Two further assertions of the sketch.** Two of the sketch's assertions are **not established for
an arbitrary covering description**:
1. there is a point `A` with `X_{1,j}(P_1, A)` inside `Y_{1,1}(P_1, R_1)`, and the closure of
   `x(1,j)_A` lies inside `y(1,1)_{P_1}`;
2. the finer covering part lies inside the coarser one (`Y_{2,2}(P_2, R_2) ⊆ Y_{2,1}(P_2, R_2)`).

They are established for the description that Lehner's construction gives, which also keeps its
covering part within `1/(i+1)` of `W` and has a return point (`CoversUpToA`,
`Description.exists_description_coveringA`, `PseudoArc/Thm14.lean`, batch 115). No refutation of
either assertion for arbitrary covering descriptions was proved, so they are recorded here as "not
established", not as false.

**Steps of the three-piece assembly that the sketch leaves out** (REPORT-batch115.md, *Ledger*,
list 1–9, in brief):
1. on the stretch `R → A` Theorem 5 is needed with a decreasing pattern; it is obtained by
   reversing the coarse chain, since the proof of Theorem 5 does not need that chain to be a level
   or to run from `P` to `Q` (`Description.theorem5_gen`, `PseudoArc/T5Gen.lean`);
2. the three applications of Theorem 5 must land at one level; Theorem 5 holds at every deep
   enough level;
3. the fine links meeting a junction link land in the correct end link of each piece (a clause of
   Theorem 5's construction, not of its statement; added to `T5.assemble`);
4. the glued chain is a chain: cross-intersections only at the junction links, and the stretches
   `P → R` and `A → Q` are disjoint (`Chain.threePiece`, `PseudoArc/T14Glue.lean`);
5. the glued chain runs from `P` to `Q` with `P`, `R` only in the links `0` and `ρ'` of its first
   part (uses `R ∉ c_0`, `P ∉ c_ρ`, `Q ∉ c_0`);
6. `W` lies in that first part;
7. the junction links of the deep level satisfy `ρ_a ≥ 1`, `ρ_a + 2 ≤ α < n_a − 1`, with closures
   in the right coarse links, once the mesh is small compared with `dist P R`, `dist P Q` and the
   radii of balls about `P`, `R`, `Q`;
8. the base rung needs a pattern tracking the `R`-indices from a fine level of one description to
   a coarse level of the other (uses `P₁ ≠ R₁ ≠ Q₁`);
9. the new `R`-index of every rung is positive (mesh below `dist P R`).

**Theorem 9 and Lehner's Theorem 1.** Lehner's Theorem 1 is Bing's Theorem 9, re-proved "at the
request of Professor Bing" because the original "has presented some readers with difficulty"
(Lehner, p. 370). The repository's `HPC.Fold.theorem9` (`Fold/Theorem7.lean`, batch 82) is proved with
every block of `F` in three consecutive links of `D` (Bing's `E`), while Bing prints "each link of F
is a subset of the sum of two adjacent links of E" (p. 737); the printed two-link form is not
formalized. The statement has no end clause (Lehner's). Naming: the chains are named the other way
round from Bing, so that Bing's `D` (crooked in `E`, and consolidated into `F`) is `E` in the Lean
statement and Bing's `E` is `D`.

## 6. Classification sources (Part C onward)

### van Mill 2004, *A note on the Effros theorem* (batch 134)

Formalized in `HPC/Effros/` (REPORT-batch134.md). Lemma 2.1, Proposition 2.2, Lemmas 3.1–3.4,
Proposition 3.5 and Corollary 3.6 are proved as printed, with the reading of the uploaded scan
(`doc/sources/vanmill2004.pdf`), which shows the closure bars legibly. The Lean names of this
section are in the group *Effros theorem (batch 134)* of `Axioms.lean` / `axioms.txt` (standard
axioms only), not in the group *Refutations*.

| statement (source) | Lean | explanation |
|---|---|---|
| Proposition 2.2 ("two analytic fat subspaces meet") without `X ≠ ∅` | `HPC.Effros.isFat_empty_of_isEmpty` (`Effros/Fat.lean`) | In the empty space `∅` is analytic and fat, and `∅ ∩ ∅ = ∅`. Van Mill tacitly assumes `X` nonempty; the proved statement `inter_nonempty_of_isFat` carries `[Nonempty Y]`. A triviality, recorded for completeness. |
| Lemma 3.4 as transcribed in COMMISSION-batch134.md §3.2 ("the interior of `Uₙx` is dense in `Uₙx`", proof "not nowhere dense, i.e. has nonempty interior") | — (not a defect of the source) | The printed Lemma 3.4 has closure bars: "the interior of `cl(Uₙx)` is dense in `cl(Uₙx)`; `x` belongs to the interior of `cl(Uₙx)`", and the proof says "`cl(V ∩ Uₙx)` is not nowhere dense". The suspected gap is an artifact of the transcription. Both sentences are proved as printed: `HPC.Effros.vanMill_3_4_dense`, `HPC.Effros.vanMill_3_4`. Likewise Proposition 3.5 is printed as "the interior of `cl(Uₙ₊₁x)` is contained in `Uₙx`" (`HPC.Effros.vanMill_3_5`), the commission's 3.5′. |
| Proposition 2.2, invariant (3), as reconstructed in COMMISSION-batch134.md §3.1 | — (not a defect of the source) | The scan prints (3) as `cl Wₙ₊₁ ⊆ cl α(Uₙ) ⊆ cl β(Vₙ) ⊆ Wₙ`. The commission's weaker reconstruction (`β(Vₙ) ⊆ Wₙ`, `α(Uₙ) ⊆ cl β(Vₙ)`) also suffices and is the one formalized (`HPC.Effros.CoreGood`, `coreGood_step`, `exists_eq_of_core`); with it the supplement "`W ⊆ Wₙ`" of step 2 is needed, while under the printed (3) it is automatic (`W ⊆ cl α(Uₙ) ⊆ cl β(Vₙ) ⊆ Wₙ`). |
| Proposition 3.5: Proposition 2.2 "applied in `E`" | — (implicit step, not false) | Corollary 3.3 gives "nowhere meager in `X`", while 2.2 in the subspace `E` needs "nowhere meager in `E`". For subsets of an open `E` the two agree, but the text does not say so. The formalization avoids subspaces: Proposition 2.2 is proved in a relative form (`HPC.Effros.inter_nonempty_of_nowhereMeagre`: `S`, `T` analytic and nowhere meager in the ambient space, `S ≠ ∅`, `S ⊆ cl T`), applied to `Uₙ₊₁x ∩ E` and `Uₙ₊₁z ∩ E`. |

### Jones 1948, *Concerning non-aposyndetic continua*, and Jones 1951, the Lemma (batch 135)

Formalized in `HPC/Jones/` (REPORT-batch135.md). The continuum `M` is the whole space `X` (compact,
connected, metric). Lean names are in the group *Jones 1948, 1951 (batch 135)* of `Axioms.lean` /
`axioms.txt` (standard axioms only); the per-file audit is `doc/batches/audits/axioms-batch135.txt`.

**Refuted as printed.**

| statement (source) | Lean | explanation |
|---|---|---|
| Theorem 10 ("`M` is indecomposable iff `M` contains an open set `D` such that `M` is not aposyndetic at any point of `D` with respect to any other point") | `HPC.Jones.theorem10_printed_iff`, `HPC.Jones.not_theorem10_printed_unitInterval` (`Jones/Basic.lean`) | `D = ∅` satisfies the right-hand side in every continuum, so the printed statement says "every continuum is indecomposable"; false for an arc (`isDecomposableSpace_unitInterval`). Corrected with `D` nonempty: `HPC.Jones.theorem10`. |
| Theorem 6 without "`D` nonempty" | `HPC.Jones.not_theorem6_printed` (`Jones/Theorem6.lean`) | With `D = M₀ = ∅` the hypotheses hold vacuously and the conclusion asks for `x₀ ∈ D`. Proved with `D` nonempty: `HPC.Jones.theorem6` (as in the skeleton, with `D ∩ M₀ = ∅`, although Jones's footnote 6 allows `D` to meet `M₀`). |

**Implicit hypotheses.** Theorems 11, 12, 13 and 19 need `D` (resp. `U`) nonempty, for the same
reason as Theorem 10; the formal statements carry it (`hDne`, `hUne`). Theorem 16 needs a third
point ("let `y` denote a point of `M − (p + x)`"): a nondegenerate connected metric space has one
(`HPC.Jones.exists_ne_ne`).

**No proof printed.**

* Theorem 2 (none at all): the pairs `(x, y)` with `X` aposyndetic at `x` with respect to `y` form
  an open subset of `X × X` (`HPC.Jones.isOpen_setOf_aposAt`); Theorem 2 is a slice of its
  complement. Theorem 1 is the same fact, and holds without `x ≠ y` and `yᵢ ≠ xᵢ`.
* Theorem 3 (none; Jones 1955 relies on it): closedness as for Theorem 2; connectedness needs
  boundary bumping: if `X` is aposyndetic at every point of the frontier of an open `V` with respect
  to `y ∉ cl V`, then at every point of `V` (`HPC.Jones.aposAt_of_frontier`: finitely many
  continua `Hᵢ` from Heine–Borel, and each component of `cl V ∪ ⋃ Hᵢ` meets the frontier).
* Theorem 0 ("with the help of the Heine–Borel theorem"): one direction from finitely many
  continua covering the compact `X − U`; the other from the closedness of components of a closed
  set and an open set inside a finite union of them (`HPC.Jones.exists_open_subset_component`).
* Theorem 5 ("similar to Theorem 4"): Theorem 0 turns "not semi-locally-connected at `x`" into
  "some `o ≠ x` with `X` not aposyndetic at `o` with respect to `x`"; then the second projection of
  the closed sets `{(o, x) | ¬ aposyndetic, d(o, x) ≥ 1/(n+1)}` (compactness of `X`).

**Proof sketches only.** Theorem 15 ("with the help of Theorems 0 and 13"): Theorem 0, then
Theorem 13 in every open subset of `U`. Theorem 18 ("with the help of Theorems 4, 5, 12, and
15"): Theorems 4 and 5 make the complement an `F_σ` (so the set is a `G_δ`); by Theorems 12 and 15
each closed piece has empty interior; Baire gives density. Theorem 19 ("follows from Theorem
15"): by contradiction, Theorem 15 puts a weak cut point in `U`. Theorem 14 ("follows
immediately from Theorem 13"): it is immediate — Theorem 13 applied to each nonempty open set gives
a weak cut point (the middle point `y ∈ D`) in it. All four are proved as sketched.

**Other remarks.**

* Theorem 12, indecomposable case: the density of composants (Jones's (1)) is not needed; a point
  `z` outside the composant of `x` (`HPC.T13.exists_not_mem_proper_subcontinua`) and any third
  point `y` suffice.
* Theorem 13: Jones's choice `V₂ ⊆ R₂ · ∏ U₂ᵢ · (M − H₁)` is supplemented by `cl V₂ ⊆ W₁`, which his
  next sentence ("consequently `Q₂` contains `Q₁` and `W₁` contains `W₂`") uses. His finite
  families `H_{n1}, …, H_{nmₙ}` are replaced by a uniform radius (`exists_radius_uniform_apos`).
* Theorem 16: the text writes "the composant of `M` containing `P`" for the weak cut point `p`
  (`P` vs `p`, a misprint). The skeleton's `[Nontrivial X]` is replaced by the existence of the weak
  cut point `p`, which gives three distinct points.
* Theorem 17 does not use that `p` is a weak cut point (only that no other point is one).

**Jones 1951, Lemma.** "Evidently `x_ω ≠ xₙ`" is right: `U_{x_ω} ⊆ U_{x_{n+1}} ⊊ U_{xₙ}`, so
`x_ω = xₙ` is impossible; the same argument works at every limit stage of the transfinite
continuation. The formal proof (`HPC.Jones.jones51_lemma`) avoids transfinite recursion: with a
countable base `B₀, B₁, …`, `g(w) = ∑ₖ [cl Bₖ ⊆ U_w] 2⁻ᵏ` is lower semicontinuous (each term is the
indicator of an open set, by Theorem 1 and compactness of `cl Bₖ`) and strictly increasing along
proper inclusion of the `U_w` (`HPC.Jones.exists_lsc_strictMono_aposSet`); at a minimum point `w₀`
of `g`, a homeomorphism `T` with `T x = w₀` would give `U_{T y} ⊊ U_{w₀}`. The hypothesis `x ≠ y`
is not needed.

**Jones 1951, Theorem 1:** open in batch 135; proved in batch 136 (next subsection).

**Jones 1955 citations (for the record, not formalized).**

* Theorem 2, last step: "`G` is homogeneous and aposyndetic. Hence by [5], `G` is a simple closed
  curve." Reference [5] is Jones 1951 (indecomposability); the result used is Jones 1949, *A note
  on homogeneous plane continua* (homogeneous + aposyndetic plane continuum ⇒ simple closed curve),
  which is [3] in the introduction. A citation slip.
* Theorem 1, last step: "Since `G` must be continuous at some one of its elements, it follows from
  the homogeneity that `G` is continuous" uses, unstated, that an upper semicontinuous
  decomposition of a compact metric space is continuous at the elements of a residual set.

### Jones 1955 Theorem 1, Whyburn 1939, Jones 1941 Theorem 4 and Jones 1951 Theorem 1 (batch 136)

Formalized in `HPC/Jones/Decomp.lean`, `Whyburn.lean`, `Jones55Core.lean`, `Jones51Thm1.lean`,
`Jones55.lean` (REPORT-batch136.md). Lean names are in the group *Jones 1955, decompositions (batch
136)* of `Axioms.lean` / `axioms.txt` (standard axioms only); the per-file audit, covering all 82
new theorems, is `doc/batches/audits/axioms-batch136.txt`. No statement of these sources is refuted.
Quotations are from the page images of Proc. AMS 6 (1955), 735–740 and Proc. AMS 2 (1951), 855–859.

**The key replacement.** One consequence of the Effros theorem (batch 134) does most of Jones's
work: in a homogeneous compact metric space, if a continuum `K` with nonempty interior contains `o`
and misses `x`, then the space is aposyndetic at `o` with respect to `x`
(`HPC.Jones.aposAt_of_isContinuum_interior`, "spreading"). From it, non-aposyndesis is transitive
(`not_aposAt_trans`); with the Lemma of 1951, `y ∈ L_x ⇒ U_y = U_x`; and Theorem 1 (b), (c) follow
(`mem_Lset_iff_Lset_eq`, `Lset_subset_of_meets`) **without decomposability**. Jones's claims (11),
(12), his characterization of `N_o`, the case argument of p. 738 and his u.s.c. argument are
replaced (see the report for the list of sentences).

**Outcome of the checks of COMMISSION-batch136.md §3.**

1. *"Since `G` must be continuous at some one of its elements, it follows from the homogeneity that
   `G` is continuous."* **Confirmed.** Continuity at some element: `exists_lscAt`, from
   `residual_lscAt` (the unstated theorem: Baire in the decomposition space, applied to the
   frontiers of the closed sets `π(cl B)`, `B` in a countable base). A homeomorphism permuting the
   elements carries continuity at an element to continuity at its image (`lscAt_homeomorph`); the
   homeomorphisms of `M` permute the `L_x` (`Lset_homeomorph`, `lSetoid_homeomorph`). Assembled in
   `jones55_continuous`.
2. *"(a) with respect to its elements (as points) `G` is a homogeneous, aposyndetic, compact, metric
   continuum"* — **not argued in the text; supplied.** Homogeneity: `T(L_x) = L_{Tx}` and
   `exists_homeomorph_quotient`. Aposyndesis: the commissioner's sketch is correct as stated and is
   the proof of `jones55_a` (a continuum `K` with `y ∈ V ⊆ K`, `x ∉ K` misses `g ∋ x` by (c); its
   image is a continuum, by compactness and connectedness of images; by lower semicontinuity at
   `g′` the image contains a neighbourhood of `g′`). Compactness, metrizability: `isClosedMap_mk`,
   `t2Space_quotient`, `secondCountable_quotient`, `metrizableSpace_quotient`. Nondegeneracy of
   `G` uses decomposability (Theorem 8 of 1948 gives `L_x ≠ M`).
3. *"The set `N_o` is closed."* **Supplied, but moot.** For `o ∈ H` (so `U = U_o`), `N_o = L_o`
   (`Nset_eq_Lset`, from (b) and (c)), and `L_o` is closed (`isClosed_Lset`, Theorem 1 of 1948).
   No direct argument at Jones's stage (before (11)) is given or needed.
4. *"Thus one obtains an uncountable well-ordered monotone decreasing sequence of distinct closed
   subsets of a compact metric space. This being impossible, …"* **(11) is proved without
   transfinite recursion** (`jones55_claim11`): if `p ∈ H` cuts `o ∈ H` from `U`, then `p ∈ L_o`,
   and every continuum through `p` meeting `U = M − L_o` contains `L_o ∋ o` by (c). (10) is proved
   as printed (`jones55_claim10`, using the Lemma of 1951).
5. *"let `d(q)` be the largest number such that for some `o` and `K_o` …, `d(q) = d(K_o, q)`"*;
   *"First, observe that `E_n` is closed"*. **Not decided; moot for the theorem.** The case argument
   of p. 738 is not used: `N_o = M − U_o` is `Nset_eq_Lset`. Neither the attainment of the supremum
   nor the closedness of `E_n` is formalized, and no "≥ sup − ε" variant was needed.
6. *"Since `M₀` is a subset of `M₁`, `y` belongs to `M₁`."* **The suspicion is justified, with a
   sharper boundary.** If `o ∉ V₂`, a continuum `K` irreducible from `o` to `cl V₂` does not meet
   `V₂` (boundary bumping: for `v ∈ K ∩ V₂`, `v ≠ o`, take an open `W ∋ v` with `cl W ⊆ V₂`,
   `o ∉ cl W`; the component of `K − W` containing `o` meets `cl W ⊆ cl V₂` and is a proper
   subcontinuum), so `K ⊆ M − V₂ = M₁`. If `o ∈ V₂`, then `K_o = {o} ⊄ M₁`. So `M₀ ⊆ M₁` is justified
   only when every `o(q)` lies outside `V₂`, which the text does not secure. Not repaired in place:
   the whole case argument is replaced (item 5). Also, *"Since `q` does not cut `o` from `U_q` and
   `V₂·U_q ≠ 0`, `q` does not cut `o` from `V₂`"*: `V₂·U_q ≠ 0` is density of `U_q` ((12)), and the
   inference uses "cuts `o` from one point of `U_q` ⇒ from all of `U_q`" (`cutsFrom_of_cutsPts`,
   from (5)). The premise "`q` does not cut `o` from `U_q`" is drawn from "`q` does not belong to
   `N_o`", whose characterization is in terms of `U_o`; this needs `U_q = U_o` for `q ∈ L_o`, which is
   (b) itself and is not available at this point of the text (in the formalization it is
   `aposSet_eq_of_not_aposAt`, via spreading). Case II was not checked further, for the same reason
   as item 5.
7. *"if `s = 1/n′ − r`, then for each point `q` of `M·R_r(p)·R_s(p)` every point of `K_o(q)` is
   outside of `R_r(p)`"*. **The reading is right** (triangle inequality: `d(q, p) < s` and
   `d(K_o(q), q) ≥ 1/n′` give `d(k, p) > 1/n′ − s = r`). Not formalized (item 5).
8. *"Since `M` is decomposable and homogeneous, (4) for each point `p` of `M`, `U_p` is a
   nondegenerate, (rel.) open subset of `M`."* **Confirmed** (`jones55_claim4`): Theorem 8 of 1948
   gives a pair with aposyndesis, homogeneity moves it to every `p`, and a nonempty open subset of a
   nondegenerate continuum is nondegenerate (`isOpen_nontrivial_of_nonempty`).
9. *"If for some point `x` of `M`, `L_x` is degenerate, then all elements of `G` are degenerate and
   `M` is aposyndetic. In this case, Theorem 1 is obvious."* **Confirmed.** By homogeneity
   (`Lset_homeomorph`) all `L_y` are points; `G` is the decomposition into points, which is
   continuous, and its space is `M` itself, homogeneous and aposyndetic. "Nondegenerate" in the
   conclusion then refers to `G` as a space (more than one element), not to its elements. The
   formal statements need no case split: `jones55_b`, `jones55_c`, `jones55_usc`,
   `jones55_continuous`, `jones55_a` cover both cases; `jones55_elements` is stated for `M` not
   aposyndetic, as in the skeleton.
10. *"(A compact continuum lying in a regular, semi-metric space or in a Moore space is itself a
    metric space.)"* **Not used**; not formalized.

**Further remarks on Jones 1955.**

* Claims (1)–(10) are proved by Jones's arguments (`jones55_claim1` … `jones55_claim10`); (2) uses
  the p. 409 Corollary of 1948 (`totallyNonApos_exists_weakCutPoint`) with footnote 3's reading of
  "cut point"; (3) is Bing's Corollary 2 (`arcs_corollary2`) moved by homogeneity
  (`exists_continuum_meets_of_open`).
* (12) *"The set `U` is dense in `M`"*: proved from (c) and (3) (`jones55_claim12`,
  `interior_Lset_eq_empty`), not from (11) and Theorem 6 of 1948.
* Upper semicontinuity, *"For if this were not the case `G` would contain a convergence sequence of
  elements whose sequential limiting set would contain points `a` and `b` belonging to different
  elements of `G`"*: replaced by the closedness of the relation in `M × M` (`isClosed_lSetoid`) and
  `isUSCDecomp_of_isClosed`.
* Footnote 4 (*"either `N_x = N_y` or `N_x·N_y = 0`"*) is (b) with `N = L` (`jones55_b`,
  `Nset_eq_Lset`).

**Whyburn 1939 and Jones 1941.** Whyburn's standing hypothesis (p. 737): *"Throughout this part we
shall suppose that `M` is a metric, connected, and semi-locally-connected space."* Here `M` is also
compact. (6.1) and (6.2) are proved (`whyburn_6_1`, `whyburn_6_2`), not by Whyburn's components `Rᵢ`
of `M − V_{δᵢ}(x)` but by Jones 1948 Theorem 0 (semi-local connectedness ⇔ aposyndesis at the
point; batch 135): the set of points joined to `a` by a continuum missing `x` is open and closed in
the component. Whyburn's (6.21) as printed is *"Each component of `M − x` is strongly connected,
i.e., any two points of such a component `R` lie together in a closed and connected set contained
wholly in `R`."* Jones 1941 Theorem 4 is *"If an aposyndetic continuum `M` is locally peripherally
bicompact at a point `P` of `M`, then `M` is semi-locally connected at `P`"*; in the compact case it
is one direction of Theorem 0 (`semiLocConn_of_isAposyndetic`; the converse is
`isAposyndetic_of_semiLocConn`).

**Jones 1951 Theorem 1, page-image check (p. 859).**

* What Jones applies: *"In such a continuum the meaning of 'cut point' and 'separating point' are
  the same [9]"* ([9] = Whyburn 1939, *"Theorem 6.21"*), used as *"Since `M′` contains a
  nonseparating point, every point of `M′` is a nonseparating point … There exists in `M′ − X` a
  continuum `T₁` containing `A + B`"*: a nonseparating point cuts no two points. This is the
  contrapositive of `whyburn_6_21` (cuts ⇒ separates), i.e. Whyburn's (6.21) (= (6.2) applied in
  each component). Whyburn's printed number is "(6.21)", as Jones cites.
* "Hereditarily unicoherent" occurs three times in the proof (searched in the text layer, checked
  on the page images). Twice on `M` (p. 858: *"Since `M` is
  hereditorily unicoherent, this is a contradiction"*, *"Because `M` is hereditarily unicoherent,
  the same reasoning holds"*). Once on `M′` (p. 859: *"But `M′` is hereditarily unicoherent"*):
  **used, not shown.** (It is true — a monotone image of a hereditarily unicoherent continuum is
  hereditarily unicoherent; standard, not formalized here — but Jones gives no argument.)
* *"Furthermore `M′` is homogeneous and aposyndetic"* and *"`M′` contains a nonseparating point"*:
  asserted without argument.
* The formal proof (`jones51_theorem1`) avoids `M′` entirely (decomposition by the `L_x`, an
  irreducible continuum, claim (5)); hereditary unicoherence is used on `M` only. `[Nontrivial X]`
  is not needed.

### Moore 1916, *On the foundations of plane analysis situs* (F.A.), §§2–5 (batch 137)

Formalized in `HPC/Moore/` (REPORT-batch137.md). Lean names are in the group *Moore F.A. §§2–5
(batch 137)* of `Axioms.lean` / `axioms.txt` (standard axioms only); the per-file audit, covering
all 139 new theorems, is `doc/batches/audits/axioms-batch137.txt`. Quotations are from the page
images of Trans. AMS 17 (1916), 131–164 (`doc/sources/moore1916.pdf`). Moore's axioms are
hypotheses of the Lean statements; "axioms used" below means Moore's axioms.

**Refuted as printed.**

| statement (source) | Lean | explanation |
|---|---|---|
| Theorem 14 (p. 136), without "`Mₙ` nonempty" | `HPC.Moore.not_fa_theorem14_printed` (`Moore/Sec4.lean`) | With every `Mₙ = ∅` the hypotheses hold (bounded; `M′ₙ₊₁ = ∅ ⊆ Mₙ`) and there is no common point, in every space satisfying Axiom 1. Proved with `hne`: `fa_theorem14`. |
| Theorem 4 (p. 133, "Every region contains infinitely many points") and Theorem 19 (p. 140, "Every region has at least one boundary point"), for `R = ∅` | `HPC.Moore.not_fa_theorem4_printed`, `not_fa_theorem19_printed` (`Moore/Refute.lean`) | Adding `∅` to the regions changes no derived notion and preserves Axioms 1–8 (Axiom 3 at `∅` is the connectedness of `S`, which follows from Axioms 1, 3, 4, 5: `isConn_univ`). So the printed forms follow from Axioms 1–8 only if the axioms have no model. Moore's proofs begin "There exists in `R` at least one point `O`" and "Let `P` denote a point of `R`"; proved with `R` nonempty: `fa_theorem4`, `fa_theorem19`. |
| Limit points on an arc (p. 139): "`P` is a limit point of `M` if and only if every interval of `AB` that contains `P` (but does not have `P` as an endpoint) contains also a point of `M` distinct from `P`" | `HPC.Moore.not_fa_sec5_limitPt_printed` (`Moore/Arcs.lean`) | For `P = A` every sub-arc containing `A` has `A` as an endpoint (`eq_or_eq_of_mem_subarc`), so the right side holds vacuously, while `A` is not a limit point of `∅`. Corrected (intervals may end at `P` when `P` is `A` or `B`): `fa_sec5_limitPt_iff`. |

**Not refuted, reworded.** First and last points (p. 139): "if `X₁` is common to `AB` and `K` and
`X₁ ≠ P₁` then `X₁` is between `P₁` and `B`". Read literally ("between" excludes the endpoints) this
fails when `B ∈ K` and `AB ∩ K ≠ {B}`; proved with "on the interval `P₁B`" (`fa_sec5_first_point`,
`fa_sec5_last_point`). Theorem 10 (p. 134): "Let `R_k` be the first link of this chain that
intersects `R`. Then `R₁R₂R₃ ⋯ R_k R` is a simple chain from `A` to `B₁`" — not simple in general
(`A ∈ R`, or `B₁` in an earlier link); the formal proof runs Moore's argument with weak chains and
extracts a simple chain as a shortest sub-chain (`exists_simpleChain_sublist`).

**Outcome of the checks of COMMISSION-batch137.md §3.**

1. *"A set of points is said to be connected if, however it be divided into two mutually exclusive
   subsets, one of them contains a limit point of the other one"* (p. 132). **The nonempty-parts
   reading is needed.** With an empty part allowed, `M = M + ∅` and neither part contains a limit
   point of the other (no point is a limit point of `∅`, and `∅` contains no
   point), so no nonempty set would be connected and Axiom 2 would fail for every nonempty
   region. With nonempty parts, Moore's connected is exactly `IsPreconnected` for the region
   topology (`isConn_iff`, Axiom 1).
2. *"THEOREM 1. No point of a region is a boundary point of that region"* (no proof). **Confirmed:
   no axiom** (`fa_theorem1`): `R` itself is a region containing `P` with `R − R = ∅`.
3. **No proof printed — what each proof needs** (each statement carries exactly these axioms):
   Theorem 1: none. Theorem 3: Axiom 1 (induction on the finite set, Axiom 1 (2) separating two
   points). Theorem 7: Axiom 1 (Theorem 6). Theorem 11: Axioms 1, 4 (closure of a finite union).
   Theorem 13 (*"see F. Hausdorff, Grundzüge der Mengenlehre"*): Axioms 1, 4 (an infinite subset
   of the compact `(R₁ + ⋯ + Rₙ)′` has an accumulation point). Theorem 16: Axioms 1, 2, 3, 4, 5₁ (as
   Theorem 15). Theorem 17 (*"Theorem 17 is a consequence of Axiom 5 and Theorem 13"*): Axioms 1, 4,
   5 — exactly as Moore says (the set of Axiom 5 meets `R′` in a finite set). Theorem 18: Axioms 1,
   4, 5 (Theorems 13, 17). *"It is clear that if `M` is a set of points then `M′` is closed"*
   (p. 135): no axiom (`fa_cl_isClosed`).
4. *"Proof. For each `n`, `Mₙ` contains at least one point"* (Theorem 14, p. 136). **Refuted as
   printed** (table above): the nonemptiness is not a hypothesis and is needed.
5. *"It is clear that the sequence `R₁, R₂, R₃, …` thus defined, satisfies conditions (1), (2), and
   (3)"* (Theorem 5, p. 134). **Confirmed, with Theorem 4 needed for the construction.** Each step
   ("the first fundamental region that follows `Rₙ`, contains `P` and is a proper subset of `Rₙ`")
   exists because `Rₙ` has a second point (Theorem 4) and Axiom 1 (2) applies. Condition (1)
   ("`P` is the only point they have in common") follows from (3) and Theorem 3: for `X ≠ P` a
   region about `P` misses `X`, and some `Rₙ` lies in it (`fa_theorem5`; Axioms 1, 3, 5₁).
6. *"With the help of Zermelo's postulate it follows that there exists an infinite sequence of
   points"* (Theorem 9, p. 134; also Theorem 14). **Noted:** in Lean this is `Classical.choose`
   (`fa_theorem9`); Theorem 14 is proved by compactness instead.
7. Theorem 15, part III (p. 138). *"Furthermore it is clear that if `X₁` and `X₂` do not lie in the
   same link of `Cₙ` but `X₁` lies in a link of `Cₙ` that precedes one in which `X₂` lies, then if
   `m > n` every link of `Cₘ` that contains `X₁` precedes every link of `Cₘ` that contains `X₂`."*
   **Supplied.** At stage `n` the links containing a point have adjacent indices (simple chain:
   `IsSimpleChain.adjacent`), so "not in a common link" and one pair `i < j` give: every link of
   `X₁` precedes every link of `X₂`. This persists to stage `n + 1` because each link of `Cₙ₊₁` lies
   with its closure in a link of `Cₙ` (condition (1)) and the owners are monotone (condition (2)):
   if `j′ ≤ i′` at stage `n + 1` then `owner j′ ≤ owner i′` at stage `n` (`hpers` in
   `exists_irreducible`). *"It is clear that `S_A` contains `A` and `S_B` contains `B`"*:
   **supplied** — `A` lies in the first link of every chain and in no other; for `P ≠ A`, from some
   stage on `A` and `P` lie in no common link (smallness), so the first link precedes every link of
   `P`; likewise `B`, with the last link. **A further gap, filled:** *"Suppose that some link `y` of
   the chain `Cₙ` contains `P_A` and also a point `P_B` of the set `S_B`. Since `y` precedes every
   link of `Cₙ` that contains `P` it follows that `P_B` precedes `P`"* — `P_B` may also lie in the
   link after `y`, which may contain `P`, so at stage `n` it need not precede `P`. Fix: choose `n`
   so large that no two links of `Cₙ` that meet contain `P_A` and `P` respectively (links of `Cₙ`
   have diameter `< 2/(n+1)` for a compatible metric; Moore's `Kₙ, Kₙ₊₁, …` serve the same purpose);
   then every link of `P_A` is at least two places before every link of `P`, and every point of `C`
   in a link `y` of `P_A` lies only in `y` and its neighbours, all before the links of `P`
   (`hgap2`, `htoU` in `exists_irreducible`). Theorem 15 is proved by Moore's construction
   (`fa_theorem15`; Axioms 1, 2, 4, and 3, 5₁ through metrizability).
8. *"THEOREM 16. Every two points of a region `R` can be joined by an arc lying entirely in `R`
   while every two points without `R` can be joined by an arc lying entirely without `R`"* (no
   proof). **Confirmed.** "Without `R`" means in `S − R′` (p. 132); this set is open (`R′` is closed:
   `isOpen_ext`, Axiom 1) and connected (Axiom 3), hence a domain, and Theorem 15 applies
   (`fa_theorem16`). The first half uses Axiom 2 and Theorem 1 in the same way.
9. *"It is clear that Theorems 1–19 are consequences of Axioms 2–5 and Theorems 5 and 15"* (§6,
   p. 140). **Not formalized; partly borne out.** The formal proofs use Axiom 1 directly. In
   Theorems 2, 3, 6–9 it enters only as "every point lies in a region" and "two points are separated
   by a region" (Theorem 3), which Theorem 5 (1), (3) supply. Theorem 4, the bridge (regularity) and
   everything resting on them use Axiom 1 (2) with closures (`exists_region_cl_subset`); the printed
   Theorem 5 (3) (*"if `R` is a region about `P` then there exists `n` such that `R′ₙ` is a subset of
   `R`"*, p. 133, with the prime) supplies this, and the skeleton's form of Theorem 5 (with
   `Rₙ′ ⊆ R`) is the printed form. (Corrected in batch 138: the batch-137 text dropped the prime,
   following pdftotext.) Theorem 15 enters only Theorem 16 (and Theorems 17–19 do
   not use it), as in Moore.

**Other remarks.**

* Axiom 5₁ (*"there exist at least three points"*, footnote p. 133) does not mention the regions;
  the skeleton's `σ.Axiom5₁` does not typecheck, and the statements write `Space.Axiom5₁ (S := S)`.
  Theorems 15, 16 and the arc results assume 5₁ instead of Axiom 5 (weaker; `axiom5₁_of_axiom5`).
* Lennes's Theorems 2–9 (*"On the basis of Axioms 2–5 and Theorem 5 it is possible to prove
  Theorems 2–9 of § 4 of Lennes' paper"*, p. 139) are not supplied in F.A.; they are proved via the
  arc characterization (`isIrreducibleConnected_iff_arc`, `isArc_iff`).

### Moore 1916, F.A., §6, Theorems 20–34 (batch 138)

Formalized in `HPC/Moore/FA6.lean` and `HPC/Moore/Sec6*.lean` (REPORT-batch138.md). Lean names are
in the group *Moore F.A. §6 (batch 138)* of `Axioms.lean` / `axioms.txt` (standard axioms only);
the per-file audit of all 103 new theorems is `doc/batches/audits/axioms-batch138.txt`. Quotations are
from pp. 140–150 of `doc/sources/moore1916.pdf`; Moore's underlined arcs (arc minus endpoints) are
written "open arc" / `openArc`. All names are in namespace `HPC.Moore`. Every theorem of §6 is
proved; one printed statement is shown not to follow from the axioms, one gets an added hypothesis.

**Refuted as printed.**

| statement (source) | Lean | explanation |
|---|---|---|
| Theorem 23 (p. 140), *"No region is a subset of an arc"*, for `R = ∅` | `not_fa_theorem23_printed` (`Moore/Sec6A.lean`) | In batch 137's `withEmpty` space (Axioms 1–8 preserved) the region `∅` is a subset of every arc, and arcs exist. Moore's proof begins *"Then `R` must contain at least one point `O` belonging to `AB` but distinct from `A` and from `B`"*. Proved with `R` nonempty: `fa_theorem23`. |

**Hypothesis added (literal form not formally refuted).** Theorem 32 (p. 147), see check 4.

**Outcome of the checks of COMMISSION-batch138.md §3.**

1. **Interior of a closed curve.** *"But `O` is on the boundary of `R₁`, the interior of `J`"*
   (proof of Theorem 23, p. 141) is the first use; F.A. never defines "the interior of `J`".
   **Unnumbered gap, filled:** Axiom 8 gives a region whose boundary is `J`; two such regions are
   each inside the other by Theorem 21, so they are equal (`existsUnique_interior`; Axioms 1, 3, 4,
   5, 7, 8). All statements use `IsInteriorOf J R` ("`R` is a region with boundary `J`").
2. **Theorem 23** *"No region is a subset of an arc."* **Refuted for the empty region** (table
   above); `hne : R.Nonempty` added. Moore's proof is otherwise followed (`fa_theorem23`; Axioms 1,
   2, 3, 4, 5₁, 8).
3. **Theorem 31** *"If `CD` is an arc, `B` is a point of `CD`, and `BX` is an arc which has no point
   except `B` in common with `CD` … then there exists in the region `R` an arc `EFG` such that (1) the
   points `E` and `G` are on `CD` in the order `CEBGD`"* (p. 146). **Tacit hypothesis:** `B ≠ C, D`
   (the skeleton's `hB : B ∈ openArc C D K`). For `B = C` the order `C E B …` is impossible with
   `E ≠ C`, and Moore's proof (*"About `B` there exists a region `R̄` which contains neither `C` nor
   `D`"*) needs `B` distinct from both. A modified conclusion with `B` an endpoint (a one-sided
   pocket `E = B`) was not pursued, since no later theorem of F.A. §6 uses it: Theorem 32 applies
   Theorem 31 only at interior points of the arc. Recorded as a tacit hypothesis.
4. **Theorem 32** *"If, in a domain `H`, `AB` is an arc, `A₁`, `B₁`, and `D` are three points on
   `AB` in the order `AA₁DB₁B` and `A₁X₁B₁` is an arc which has no point in common with `AB` except
   `A₁` and `B₁`, and finally `C` is a point in `R`, the interior of the closed curve `A₁X₁B₁DA₁`,
   then there exists, in `H`, an arc `CB` which has no point except `B` in common with `AB`"*
   (p. 147). **Intended hypotheses determined; one added.** The proof needs: `AB ⊆ H`, `R ⊆ H`
   (not `A₁X₁B₁ ⊆ H`), `D` on the boundary of `R`, and **`R` has no point in common with `AB`**
   (`hRK`). Without the last the literal statement fails in the plane: nothing stops the interval
   `AA₁` from entering `R` (e.g. spiralling in from outside and meeting `A₁X₁B₁DA₁` only at `A₁`);
   a point `C` of `AA₁` in `R` lies on `AB`, so no arc from `C` meets `AB` only in `B`. This is
   not formally refuted (it would need a model of Axioms 1–8, which the repository does not
   have). In Moore's use (Theorem 34, and Kline's proof) `R` is a pocket of Theorem 31, which
   misses `AB`. Dropped as unused: `X₁ ⊆ H`, the arc hypotheses on `A₁X₁B₁` and on `A₁DB₁`, and
   `IsArc A B K` (implied by the order). `fa_theorem32`, Axioms 1–8.
5. **Theorem 33** *"then `R − AB − A)` is connected"* (p. 148, unbalanced parenthesis). **Read as
   `R − (AB − A)`**, confirmed by the end of Moore's proof (*"Hence `R − (AB − A)` is
   connected"*, p. 150) and by the hypothesis that the open arc lies in `R`. The general proof
   (*"Proof of Theorems 33 and 34 … for the case where `R` is any region"*, p. 150, *"a
   modification of a proof due to Mr. J. R. Kline"*) is formalized (`fa_theorem33`). **The special
   proof (pp. 148–150, boundary a closed curve) is not needed.**
6. **Theorem 34** *"If `J` is a Jordan arc and `AB` is an arc lying wholly in `R`, the interior of
   `J`, then `R − AB` is connected"* (p. 150). **Misprint confirmed**: "the interior of `J`" is used in F.A.
   only for closed curves (Axiom 8), and Moore's first proof treats *"the case where the boundary of
   `R` is a closed curve `J`"*. Proved for closed curves (`fa_theorem34`) and for any region
   (`fa_theorem34_region`), both by Kline's proof.
7. **Unargued steps — supplied.**
   * Theorem 23: *"There exist on `AB` two points `A₁` and `B₁` such that `A₁` is the last point
     that `AXB` has in common with the interval `AO` …"* — first/last points of batch 137
     (`Gen.TArc.first_point`), and the arc of `AXB` from `A₁` to `B₁` meets `AB` only in them;
     *"it must be a subset of `A₁OB₁`"* — a subset of `AB` missing `AA₁ + B₁B` lies in the
     interval `A₁OB₁` (order on the parametrized arc).
   * Theorem 25: *"It is clear that no one of the three sets `R₁`, `R₂`, and `Y` contains a limit
     point of either of the other two"* — `Y` is defined as `R − (AXB + R₁′ + R₂′)`, and the three
     sets are open and disjoint; *"It can easily be shown that the point-set `FG + GA` contains as
     a subset an arc `FH` …"* — supplied by `Gen.exists_cross`, aimed at interior points of `AXB`
     (Moore's `H` near `A` might land on `ACB`); *"It easily follows that `EL − L` is a subset of
     `Y`"* — `EL − L` is connected, in `R − AXB`, misses `R₁` by construction and meets `Y`.
     (`Gen.th25`.)
   * Theorem 26: *"It may be easily proved with the assistance of Theorems 17 and 13 that `E`
     contains at least one point which does not belong to `R₁`, `R₂`, or `ADB`"* — the closures of
     the regions are compact and the space is not; *"It is clear that `Y` is composed of all points
     that are common to `E`, `E₁`, and `E₂`"* — taken as the definition of `Y`, with each open arc
     shown to lie without the curve of the other two (`Gen.th26_aux`); *"It can easily be shown that
     there exist points `G₁, G₂, H₁, H₂` …"* — `Gen.exists_cross`. Case I is reduced to the others,
     so Theorem 25 and the curves `J̄₁`, `J̄₂` are not needed. (`Gen.th26`.)
   * Theorem 28: *"The point-set `A₂C + CP + PD + DB₂` contains as a subset an arc `AXB` satisfying
     conditions (1), (2), and (3)"* — **needs a correction**: `CA₂` runs in `R_A`, which straddles
     `J`, so the part of `CA₂` before `J` need not lie in `M`; `A` is taken as the first point of
     `CA₂` outside `M` (a boundary point of `M`, hence on `J`, hence on the open arc `A₁O`).
   * Theorem 32: *"It follows (cf. proof of Theorem 31) that `DO` may be covered by a finite set …
     and possibly one additional arc"* and *"It easily follows that there exists an infinite set of
     arcs …"* — replaced by `sides` (pockets of Theorem 31 near each point of the open arc) and
     `side_propagate` (connectedness of an interval instead of the Class I/II least upper bound),
     then dependent choice for the infinite chain; *"It is easily seen that `B` is a limit point of
     `CX₁ + CX₂ + ⋯` and that `τ` is connected and contains no proper connected subset that
     contains `B` and `C`"* — `Gen.tarc_of_seq` (compact, connected, irreducible, hence an arc by
     batch 137's `isIrreducibleConnected_iff_arc`).
   * Theorem 33: *"The case where one or both of the points `P₁` and `P₂` is on `DE` can be easily
     treated"* — **moot**: it belongs to the special proof, which is not used.
   * Theorem 34: *"It easily follows that `R − AB` is connected"* — **moot** for the same reason.
     **A gap in Kline's proof, filled:** *"Likewise there exists in `R` an arc `DC` having no point
     except `C` in common with the arc `CAB`"* — the first point of `DC` on `CAB` may be the end
     `B`, where Theorem 32 does not apply in the stated form; then `C … A B … D` is itself an arc
     and the two points are joined around it (`joinZ`).
8. **Degenerate cases.** Theorem 23: the empty region (refuted, check 2). Theorem 28: *"There
   exist on `J` two points `A₁` and `B₁` such that the arc `A₁OB₁` (on `J`) lies in `L̄`"* — `O`
   ends up in the open arc `AB` of `J`, not merely on it; the conclusion is stated in that
   stronger form, which Theorem 31 uses. Theorem 30: the skeleton's `B ∈ DBC` is not needed; the
   conclusion holds for either arc of `J` from `D` to `C`. Theorem 31: `B` an endpoint (check 3).
   Theorem 32: `C` on `AB` (check 4). Theorem 34: first point at the end `B` (check 7). Theorems
   20–22, 24–27, 29, 33: no degenerate case found (Theorems 24–27, 29, 30 have their regions
   nonempty by Axiom 8 / the separation hypothesis).

**No proof printed — what each proof needs.** Theorem 20 (*"can easily be proved with the help of
Axiom 7"*): Axiom 7 only, as Moore says. Theorem 22 (*"can be easily proved with the help of
Theorem 19, Axioms 2 and 3 and Theorem 20"*): Axioms 1, 3, 4, 5 via batch 137's `isConn_univ`, not
Moore's hint. Theorem 30: Axioms 1, 2, 3, 4, 5, 7, 8 (Theorems 24, 25 in Case I; 20, 24–27 in
Case II).

### Moore 1916, F.A., §7, Theorems 35–43 (batch 139)

Formalized in `HPC/Moore/FA7.lean` and `HPC/Moore/Sec7*.lean` (REPORT-batch139.md). Lean names are
in the group *Moore F.A. §7 (batch 139)* of `Axioms.lean` / `axioms.txt` (standard axioms only);
the per-file audit of all 28 new theorems is `doc/batches/audits/axioms-batch139.txt`. Quotations
are from pp. 150–157 of `doc/sources/moore1916.pdf`; Moore's underlined arcs are written "open arc" /
`openArc`. All names are in namespace `HPC.Moore`. Theorems 35–40 are proved; Theorem 41 is proved
in Case I and in the first sub-case of Case II, and its Case II is **open** (`OPEN.md`); Theorem 42
is proved from Theorem 41; Theorem 43 as printed is refuted and its corrected form is **open**.

**Refuted as printed.**

| statement (source) | Lean | explanation |
|---|---|---|
| Theorem 35 (p. 150), *"Every region contains at least one simple closed curve"*, for `R = ∅` | `not_fa_theorem35_printed` (`Moore/Sec7A.lean`) | In batch 137's `withEmpty` space (Axioms 1–8 preserved) the region `∅` contains no closed curve. Proved with `R` nonempty: `fa_theorem35`. |
| Theorem 43 (p. 156), for `G` empty | `not_fa_theorem43_printed` (`Moore/Sec7Th42.lean`) | The hypotheses hold vacuously. The conclusion gives a closed curve `J₁ ⊆ J`, so `J₁ = J` (`isSCC_eq_of_subset`) and `I₁ = I` (Theorem 21), while `I₁` must lie without `J`. Proved for every space satisfying Axioms 1–8: such a space has a closed curve (Theorem 35). Correction: `G` nonempty; the corrected form is open. |

**Outcome of the checks of COMMISSION-batch139.md §3.**

1. **Theorem 35** *"Every region contains at least one simple closed curve."* **Refuted for the
   empty region** (table above); `hne : R.Nonempty` added (`fa_theorem35`, Axioms 1–8). Moore's
   proof (Theorems 4, 16, 23, 34, 15) is replaced: an arc in `R` and, about one of its interior
   points, the closed curve of batch 138's `th31_pocket`.
2. **Theorem 36** *"there exists a simple closed curve which lies in `R` and encloses `O`"*
   (p. 151). Proved by Moore's proof (`fa_theorem36`, Axioms 1–8), with one step corrected:
   *"Then `BE` (on `BD`) + `EC` (on `DC`) is an arc `BC` every point of which, except `C`, is in
   `R`"* — the region `R̄` about `C` need not lie in `R`, so `EC` can leave `R` before `C`; the arc is
   cut at its first point outside `R` (again a boundary point of `R`), which is used as `C`. **Not
   part of the printed statement:** the interior lies in `R` (`fa_theorem36_interior_subset`, by
   Theorem 21: its boundary `J` lies in `R`). This is the form Moore 1925 Theorem 19 needs.
3. **Footnote, p. 152** *"Two arcs of a closed curve can have no point in common unless one of them
   contains an endpoint of the other one."* **Proved** (`fa_arcs_of_scc_meet`; Axioms 1, 3, 4, 5₁).
4. **Theorem 37 proof.** *"Hence, in view of Theorem 29, it is clear that if `W₁` is between `Z₁`
   and `O` on the arc `A₁O` then `W₂` must be between `Z₂` and `O` on the arc `A₂O`"* and *"If
   Theorem 37 is false there exists a point `L₁` on `A₁O` and a point `L₂` on `A₂O` such that `L₁` is
   a limit point of `M₁` …"* — **both replaced** by one finiteness argument
   (`param_chords_finite`, `exists_maximal_chord`): apart from `A₁XA₂`, the arcs of `C` from `A₁O` to
   `A₂O` with open part within `J` lie in the other arc `K` of `C` from `A₁` to `A₂`; in the
   parameter of `K` they have disjoint open intervals, each of length at least some `λ > 0`
   (compactness), so there are finitely many and an innermost one exists. Theorem 29 and the limit
   points `L₁`, `L₂` are not needed. `fa_theorem37`: Axioms 1, 3, 4, 5₁ only.
5. **Theorem 39 proof** — **replaced**, covering all seven sentences: *"It may be easily shown with
   the help of Theorems 5 and 36 that there exists a sequence of closed Jordan curves `J₁, J₂, …`"*,
   *"With the use of (1) it may be shown that `I` contains a point of `Jₙ`"*, *"It is clear that, for
   a given `n`, the arc `AₓBₓ` is completely determined by the point `X`"*, *"It may be easily proved
   that `J̄ₙ` is a closed Jordan curve"*, *"It easily follows (cf. proof of Theorem 25) that there
   exists an arc `T₁T₂` …"*, *"It may be easily proved that the point-set `O + P₁Pₙ₂ + ⋯` is an arc
   from `P₁` to `O`"*, and *"That a point without `J` can be so joined to any point of `J` may be
   proved in a similar manner"*. Replacement (`access`, `fa_theorem39`; Axioms 1–8): a point not on
   `J` lies in the interior `I` or the exterior `S − I'`; batch 138's `accessible` (the limit-arc
   lemma behind Theorem 32), applied to an arc of `J` ending at `O`, joins it to `O` inside that set.
   The exterior case is the same argument, not "similar".
6. **Theorem 41 proof.**
   * Case I: *"Then, since `I₁` and `I₂` have a point in common, it easily follows that either `I₁`
     is in `I₂` or `I₂` is in `I₁`"* — **supplied** (`fa_theorem41_caseI_nested`,
     `fa_theorem41_caseI`; Axioms 1, 2, 3, 4, 5, 7): if `J₂` misses `I₁`, then `I₁ ⊆ I₂` (`I₁` is
     connected); otherwise `J₂` has no point without `J₁` (the two arcs of `J₂` from a point within
     to a point without would meet `J₁` in two distinct points, `two_meets_of_in_out`), so
     `J₂ ⊆ I₁'` and `I₂ ⊆ I₁` by Theorem 21. Also supplied: *"If every point of `J₁` is within or on
     `J₂` then `J` is `J₂`"* (`fa_theorem41_of_subset`, Theorem 21).
   * Case II: *"It may be proved that `J` is a closed curve satisfying the requirements of Theorem
     41."* — **open** (`OPEN.md`). Moore's `J` (the arcs `t_P` together with the points of `J₂` on no
     `k_P`) may consist of infinitely many arcs `t_P`; proving that it is a closed curve, and that its
     interior contains `I₁ + I₂`, needs a limit construction which was not carried out. Moore's use
     of Theorem 38 in this proof (`A_p XB_p`, *"if `Z` and `W` are points on `A_pC` and `B_pC` …"*)
     fixes the reading of Theorem 38 (3) recorded in `fa_theorem38` (outermost arc).
7. **Theorem 43 with `G` empty** — **refuted** (table above). The corrected form (`G` nonempty) is
   **open** (`OPEN.md`): no proof is printed, and the evident route needs Theorem 42 (hence Theorem
   41) and, for `J₂`, the dual statement for intersections of interiors, which F.A. does not state.
8. **Degenerate cases.** Theorem 35: the empty region (check 1). Theorem 36: none (`O ∈ R` makes
   `R` nonempty); the corrected step of check 2 is an endpoint case (the first point outside `R`).
   Theorem 37: none (`O ∉ C` keeps `O₁`, `O₂ ≠ O`). Theorem 38: the skeleton leaves the shape open;
   the open arc `A₁XA₂` is assumed without `J` (`hXE`, implicit in Moore's use in Theorem 41), and
   (3) is concluded as `{B₁, B₂} = {O₁, O₂}` (the statement does not say which end is which).
   Theorem 40: `A ≠ B` (the skeleton's `hAB`) is needed: an arc has distinct ends. Theorem 41: Case I
   with `J₁ ∩ J₂ = ∅` is covered by `fa_theorem41_caseI`. Theorem 42: `G` nonempty (the skeleton's
   `hne`) is needed, since no closed curve lies in the empty union. Theorem 43: `G` empty (check 7).

**No proof printed — what each proof needs.** Theorem 38 (*"analogous"*): Axioms 1, 2, 3, 4, 5, 7, 8
(finiteness of the outer chords via `param_chords_accumulate` and Theorems 21, 27). Theorem 40:
Axioms 1–8 (`access`, i.e. batch 138's `accessible`). Theorem 42: from Theorem 41 by induction, the
order given by connectedness of the union (`fa_theorem42_of_41`; Axioms 1, 2, 3, 4, 5₁, 7 besides
Theorem 41). Theorem 43: open.

### Moore 1916, F.A., Theorems 41–43, and Moore 1919, Theorems A and B (batch 140)

Formalized in `HPC/Moore/M19AB.lean` (umbrella) and `HPC/Moore/M19*.lean`, `HPC/Moore/M41*.lean`,
`HPC/Moore/M43*.lean` (REPORT-batch140.md). Lean names are in the group *Moore F.A. 41–43, 1919 A–B
(batch 140)* of `Axioms.lean` / `axioms.txt` (standard axioms only); the per-file audit of all 49 new
theorems is `doc/batches/audits/axioms-batch140.txt`. Quotations of 1919 are from pp. 170–174 of
`doc/sources/moore1919.pdf`, of F.A. from p. 156 of `doc/sources/moore1916.pdf`. All names are in
namespace `HPC.Moore`. Everything commissioned is **proved**: Theorem 41 (Case II), Theorem 42,
Theorem 43 corrected (`G` nonempty), Theorems A and B, and the arc of footnote * of p. 174. Nothing
new is refuted; nothing is left open.

**Outcome of the checks of COMMISSION-batch140.md §3.**

1. **Footnote †, p. 170.** *"If `X` and `Y` are two points of a closed curve `J`, there are just two
   arcs that lie wholly on `J` and have `A` and `B` as endpoints."* **Misprint confirmed**: `A` and
   `B` stand for `X` and `Y` (the sentence introduces `X`, `Y` and uses no `A`, `B`; the `A`, `B` of
   Theorem B, to which the footnote is attached, are points of `J` but are not the general points of
   the definition). Read with `X`, `Y`: `Space.IsSegmentOf` (`Moore/M19Defs.lean`). The statement
   "just two arcs" itself is F.A. p. 140 (an arc of a closed curve and the closure of its complement),
   already formalized in batch 137.
2. **Theorem B, unargued steps** — each **supplied** (`m19_theoremB`, `Moore/M19B.lean`; Axioms 1–8).
   * *"it is clear that there exists a point `A₁` which is the first point that the segment `AB` has
     in common with `L`"*: by the restriction on `A` (and `B`), near `A` the curve `L` lies on `J`
     (`seg_nhds`: if `A ∉ L`, a neighbourhood misses `L`; if `A` is on a segment common to `J` and
     `L`, a neighbourhood meets `L` only in that segment). The open arc `AB` is within `J`, so in the
     parameter of `AB` the points of `L` form a closed set `Z` inside a closed sub-interval `[a', b']`,
     `0 < a'`, `b' < 1`; a nonempty closed set of parameters has a first element.
   * *"By an argument similar to the above proof of the non-existence of `X` it can be shown that `B₁`
     cannot be a limit point of a set of points of `M` no one of which can be properly joined to
     `A₁`"*: "properly joined" (footnote ‡) is `Gen.PJ L I`, an equivalence relation (`PJ.symm`,
     `PJ.trans`), and each class is open in `Z`, because a closed curve is locally arcwise connected
     (`loc_arc`: near each of its points, points of `L` are joined to it by small arcs of `L`, which
     lie within `J` when the point does). An open class is also closed in `Z`, so `B₁` (a limit point of
     the class of `A₁`) lies in it, and no point of another class is near `B₁`. This one argument
     replaces both Moore's proof of the non-existence of `X` and the "similar" argument.
   * *"It is clear that `O` is either `Aₘ` or `Bₘ`"*: `O` is the last point of `L` on `AB`. By the
     construction, `Bₘ` is the last point properly joined to `Aₘ` and no point of `M` follows `Bₘ`
     (otherwise `Aₘ₊₁` would exist); `Bₘ ∈ M`, so `O = Bₘ` (and `Bₘ = Aₘ` in the degenerate case,
     hence Moore's "either"). In the Lean proof the process is an induction on the number of classes
     of `Z` lying after the current point, and the last step is `empty_case` (no point of `Z` beyond
     the current point: the rest of `AB` is used as it stands).
   * *"It is easy to see, with the aid of Theorems 43 and 40, that there exists an arc `AₙZ̄ₙBₙ` that
     lies entirely within `J` and, except for its endpoints, is also entirely within `L`"*:
     `m19_B_step` (`Moore/M19Bstep.lean`; Axioms 1–8), **proved without Theorem 43**: with `K₂` the
     other arc of `L` from `Aₙ` to `Bₙ`, the set `O = I − K₂` is open, contains the open arc
     `AₙZₙBₙ`, and `O − AₙZₙBₙ` lies in `I − L`; the component of `O − AₙZₙBₙ` reached from the
     interior of `L` (Theorem 40, `Gen.exists_access`) has `Aₙ`, `Bₙ` as accessible boundary points
     (batch 138's `accessible`). Theorem 43 is proved as well (batch 140), but is not needed here.
   * *"In view of these considerations it is clear that the point-set `τ` contains, as a subset, an arc
     from `A` to `B` …"*: the pieces are joined one at a time from `B` backwards
     (`Gen.TArc.join`: the union of two arcs meeting at an end contains an arc between the other
     ends), keeping track of the finitely many points of `L` (`join_step`).
3. **Theorem B's finiteness argument.** *"then there are infinitely many arcs, all lying on `L`, such
   that no two of them have, in common, any point unless possibly a common endpoint, and such that
   each of them has one endpoint on `J` and the other on the interval `A₁O` of the arc `AB` … But by
   Theorem A a simple closed curve cannot contain an infinite set of arcs of this type."* **Theorem A
   applies**: take `M = J` and `N` the interval `A₁O` of `AB`. Both are closed (an arc and a closed
   curve are closed). They are disjoint: the arc `AB` meets `J` only in `A` and `B`, and the interval
   `A₁O` contains neither (`A₁` follows `A`, `O` precedes `B`, both being points of `L` on the
   *segment* `AB`). The arcs `BₙXₙ` lie on `L`, each contains a point of `M` (`Xₙ`) and of `N` (`Bₙ`),
   and two of them meet at most in an endpoint, so they have no segment in common. Moore's argument
   that the segments `BᵢXᵢ`, `Bᵢ₊ⱼXᵢ₊ⱼ` are disjoint is correct as printed. **In the Lean proof Theorem
   A is not used**: compactness of `Z` gives finitely many properly-joined classes (each open in
   `Z`), and each step `Aₙ ↦ Bₙ ↦ Aₙ₊₁` leaves a class behind for good, so there are at most as many
   steps as classes. Theorem A is proved separately (`m19_theoremA`) and is used in Theorem 41
   (check 4).
   **The reading of "no two arcs of `G` have a segment in common"** (commission item C):
   `Space.ShareSegment K K'` says that some arc `T` has its open part `openArc X Y T` in `K ∩ K'`. For
   arcs `K`, `K'` on `L` this is Moore's notion: `openArc X Y T ⊆ L` forces `T ⊆ L` (`L` is closed),
   so `T` is an interval of `L` and its open part a segment of `L` (footnote †) common to both arcs;
   conversely a common segment is the open part of its interval. **Checked.** The skeleton's
   injectivity of the family is dropped in `m19_theoremA` (a repeated nondegenerate arc shares a
   segment with itself, and the proof uses only three distinct indices), which makes the statement
   stronger.
4. **Theorem 41, Case II.** *"It may be proved that `J` is a closed curve satisfying the requirements
   of Theorem 41."* (F.A. p. 156) — **supplied** (`fa_theorem41_caseII`, `Moore/M41.lean`; Axioms
   1–8), by the route suggested in the commission, with the curve located first:
   * `V` is a component of `S − (I₁' + I₂')` whose closure is not compact
     (`Gen.exists_unbounded_component`); its boundary lies on `J₁ + J₂`, and `V` misses the interior of
     every closed curve that misses `V` (`Gen.disjoint_of_unbounded`).
   * A point `O` of `J₂` without `J₁` is a limit point of `V` (otherwise `V` would be the exterior of
     `J₁` and `J₂ ⊆ I₁'`, the sub-case already proved); the chord of `J₂` through `O` gives a second
     point `O'` (`chord_through`, `chord_side`).
   * `J₂` is split at `O`, `O'`. On each of the two arcs, every arc of `J₂` cut off by a chord of
     `J₁` (an arc of `J₁` with open part in `V`, ends on `J₂`) is replaced by that chord. These chords
     are Moore's `t_P`, the replaced arcs his `k_P`. There may be infinitely many: **Theorem A of
     1919** shows that only finitely many have diameter `≥ ε` (`chords_null`: arcs of `J₁` with pairwise disjoint open parts; if infinitely many reached distance
     `ε` from their first end, a subsequence would have a far point near `c` and a first end near `d`,
     `dist c d ≥ ε`, and Theorem A applied with `M`, `N` the closed balls of radius `ε/3` about `c`,
     `d` — closed and disjoint — gives a contradiction), and the parameter intervals of the `k_P` are pairwise disjoint
     (`pocket`, from Theorem 27: the pocket `t_P + k_P` bounds a region missing `V`). The
     replacement of a null family of arcs (`Gen.arc_replace`, `Gen.finite_long_intervals`) is
     continuous and injective, so each half becomes an arc from `O` to `O'` (`half_replace`); the two
     arcs meet only in `O`, `O'`, and their union `J` is a closed curve on `J₁ + J₂`.
   * `J` contains the boundary of `V` (each point of `J₁` without `J₂` on it lies on a chord in
     `V'`), so `V` is the exterior of `J`, and `I₁ + I₂`, missing `J` and `V`, lies in the interior of
     `J` (`curve_of_frontier_subset`, Theorems 21 and 28).
   Moore's use of Theorem 38 (the outermost pocket through each point) is not needed: the curve
   obtained is the same one, the boundary of `V`.

**Further outcomes.**

* **Theorem 42** (p. 156): **proved** unconditionally (`fa_theorem42`, `Moore/M41.lean`; Axioms 1–8),
  from batch 139's `fa_theorem42_of_41`.
* **Theorem 43, corrected** (p. 156, `G` nonempty; the printed form stays refuted for `G = ∅`,
  `not_fa_theorem43_printed`): **proved** (`fa_theorem43`, `Moore/M43.lean`; Axioms 1–8). Moore prints
  no proof. Supplied: the intersection analogue of Theorem 41 (`dual_step`: if `O` is a point of the closed curve `J` within the closed curve `J'`, and `U` is
  the interior of `J`, or its exterior provided `I ⊄ I'`, there is a closed curve through `O` on
  `J + J'` whose interior lies in `U ∩ I'`; proved by the same
  pocket-replacement method, `chord_pockets`, `adjacent_piece`, `dual_component`), iterated over `G`
  (`iterate_inner`), started from `J` for `J₂` and, for `J₁`, from a closed curve through `O` without
  `J` given by `dual_step` applied to the exterior side (this is where `¬ I ⊆ I_p` is used).
* **The arc of footnote * of p. 174** (Theorem D): *"Within `ḡ₁` (and within `J` except for the point
  `A₁`) there is an arc `A₁E′₁` that has in common with `E₁E′₁` only the point `E′₁`"*, with the
  footnote *"Make use of Theorems 43 and 40 and the existence of the curve `ABTNA` described on page
  149 of Foundations"*: **proved** in the form Theorem D needs (`m19_D_arc`, `Moore/M19D.lean`;
  Axioms 1–8), without Theorem 43: the curve `ABTNA` is the device of Kline's proof of Theorem 33, here
  `hair_isPreconnected` (a connected open set minus an arc having one end in it and the other end
  outside stays connected).
* **Footnote ‡ of p. 170** (the example `y = x sin(1/x)`, showing the restriction on `A`, `B` in
  Theorem B cannot be dropped): set in the ordinary plane; **recorded, not formalized**, as the
  commission directs.
* **Degenerate cases.** Theorem A: the family is `ℕ`-indexed without injectivity (check 3). Theorem B:
  `A ≠ B` is needed (an arc has distinct ends); the case where `AB` misses `L` is `empty_case`.
  Theorem 43: `G = ∅` (refuted in batch 139). `m19_D_arc`: `E₁` is on the *segment* `A₁B₁`.

### Moore 1919, double rulings; Theorems C and D (batch 141)

Formalized in `HPC/Moore/M19CD.lean` (umbrella) and `HPC/Moore/M19CD*.lean`,
`HPC/Moore/M19CRefute.lean` (REPORT-batch141.md). Lean names are in the group *Moore 1919 C–D (batch
141)* of `Axioms.lean` / `axioms.txt` (standard axioms only); the per-file audit of all new theorems
is `doc/batches/audits/axioms-batch141.txt`. Quotations are from pp. 172–176 of
`doc/sources/moore1919.pdf`. All names are in namespace `HPC.Moore`. Outcome: the subdivision lemma,
padding and the refinement step are **proved**; Theorem C as printed is **refuted**; Theorem D is
**open** (`OPEN.md`); the region form of Theorem D is proved from its curve form.

**Outcome of the checks of COMMISSION-batch141.md §3.**

1. **The double ruling definition** (footnote *, p. 172). *"… there are points in the order
   `AX₁X₂ ⋯ XₙBY₁Y₂ ⋯ YₙCX′ₙ ⋯ X′₁DY′ₙ ⋯ Y′₁A` and `X₁X′₁, …, XₙX′ₙ, Y₁Y′₁, …, YₙY′ₙ` are arcs which,
   except for their endpoints, lie entirely within `ABCDA`, and finally, for every `i, j`
   (`1 ≤ i ≤ n`, `1 ≤ j ≤ n`), `XᵢX′ᵢ` has just one point in common with `YⱼY′ⱼ` and no point in
   common with `XⱼX′ⱼ` (unless `i = j`) …"*
   * *Equal numbers of arcs*: **not needed**. `doubleRuling_pad` (Axioms 1–8): a double ruling with
     `n` and `m` arcs extends, by adding arcs, to one with `max n m` arcs in each ruling whose
     subdivisions lie in those of the given one. Moore's own Fig. 1 (p. 173) has **9** arcs parallel
     to `AB` (`K₁D₁C₁B₁L₁, K₂D₂C₂B₂L₂, A₄B₄L₃, A₃B₃L₄, E₃D₃L₅, E₄D₄L₆, E₇A₇, K₃B₆A₆, K₄B₅A₅`) and **8**
     parallel to `BC` (`H₁B₃C₃D₃M₆, H₂B₄C₄D₄M₅, E₂D₂M₄, E₁D₁M₃, A₁B₁M₂, A₂B₂M₁, H₃B₆E₆, H₄B₅E₅`),
     counted on the page image and agreeing with the lists in the text: the example does not satisfy
     the printed definition literally. The formal definition allows `n ≠ m`.
   * *Disjointness of the `Y`-arcs*: the printed text is silent; **added** (`disjY`). The `Y`-arcs of
     Fig. 1 are disjoint, and the subdivision lemma is false without it.
2. **The subdivisions** (*"subdivisions"*, p. 172, never defined) are defined as the components of
   `I − ⋃ arcs` (`Space.DoubleRuling.cells`). **The subdivision lemma** (never stated) is **proved**:
   there are exactly `(n+1)(m+1)` subdivisions, each the interior of a closed curve lying on
   `ABCDA` and the arcs (`doubleRuling_cell`, `doubleRuling_cells_ncard`, from
   `Space.DoubleRuling.tiling`; Axioms 1, 2, 3, 4, 5, 7, 8).
3. **Theorem C.** *"If the closed curve `g` has only a finite number of points in common with the
   closed curve `ABCDA` and does not contain `A`, `B`, `C`, or `D` then the interior of `ABCDA` can be
   divided by a double ruling … into subdivisions such that the interior of each one of them is either
   wholly within or wholly without `g`."* — **refuted** (`not_m19_theoremC_printed`; Axioms 1–8): `g`
   meeting `ABCDA` in a single point of the segment `AB` and lying otherwise within it
   (`tangent_configuration`) admits no such ruling (`no_ruling_of_two_branches`: both branches of `g`
   at the point of contact would have to run along the one arc of the ruling ending there).
   *"Indication of proof. There exists a finite set `K` of arcs of `g` each of which lies entirely
   within `ABCDA` except that its endpoints are on `ABCDA` and such that every point of `g` that is
   within `ABCDA` lies on an arc of `K`."* In the counterexample no such `K` exists (the part of `g`
   within `ABCDA` is one open arc whose two ends coincide), nor when `g` lies wholly within `ABCDA`.
   *"This indication of how a ruling may be constructed in the case of this typical example is given
   instead of a tedious formal proof covering all possible cases."* **No proof is supplied**; no
   corrected Theorem C is proved in this batch.
4. **Theorem D, unargued steps.**
   * *"There exists a finite set `Ḡ` of closed curves `g₁, g₂, ⋯ gₘ` such that every one of them is a
     curve of the set `G` and such that every point on or within `J` is within one of them"*: correct
     by Theorem 12 (Heine–Borel; `J + I` is compact).
   * *"(2) `EᵢE′ᵢ` lies within every region of the set `Ḡ` that contains `Eᵢ`"*: `Ḡ` is a set of
     curves. **Reading**: "within every curve of `Ḡ` within which `Eᵢ` lies" (the regions meant are
     the interiors of the curves). This is the form of `m19_D_arc` (batch 140).
   * *"It easily follows that there exist (Fig. 2) (1) on `ABCDA`, `4n` points … (2) within `ABCDA` a
     closed curve `J′` … (3) arcs …"*: **not supplied**.
   * *"By Theorem C the interior of `ĀB̄C̄D̄` may be divided by a double ruling `τ̄` …"*: Theorem C is
     false as printed (check 3), and `J̄` is only known to meet `g₁` in finitely many points, so the
     step fails when `g₁` touches `J̄` without crossing it. **Gap recorded.**
   * *"By the addition of certain arcs … it is possible to continue the arcs of `τ̄` … in such a way
     that there will result a double ruling `τ₁` of `ABCDA` …"*: of the kind of the refinement /
     extension lemmas proved here (`doubleRuling_refine`, `Space.ArcRuling.extendY`), but the
     annulus is not formalized.
   * *"If any of them are wholly without `g₁`, then each such subdivision can itself be divided by a
     double ruling … into subdivisions each of which is either wholly within some curve of the set
     `G` or wholly without `g₂`. The arcs of these rulings may be extended in such a way that there
     will result a new double ruling `τ₂` …"*: the extension is **proved** (`doubleRuling_refine`, with
     `Good U` = "wholly without `g₁, …, gₖ` or wholly within some curve of `G`"). The division of each
     subdivision is **not** an application of Theorem C: the boundary of a subdivision of `τ₁` may
     meet `g₂` in infinitely many points. It is a form of Theorem D itself. **Gap recorded.**
   * *"It can be shown in a similar way that there exists a double ruling `τ₃` … This process may be
     continued."*: the same gap.
5. **Theorem D's conclusion and its use in Theorem E** (*"By Theorem D the interior of `ABCDA` can be
   divided by a double ruling `β₁` into subdivisions each of which is within some region of the set
   `G₁`"*, p. 176). **The curve form suffices**: `m19_theoremD_regions_of_curves` (Axioms 1–8) derives
   the region form from the curve form, each point of a region being within a closed curve whose
   interior lies in the region (Theorem 36 with Theorem 21).

**Further outcomes.**

* **Refinement** (*"The arcs of these rulings may be extended in such a way that there will result a
  new double ruling `τ₂` of `ABCDA` such that each arc of `τ₁` is also an arc of `τ₂`"*, p. 175, and
  *"the arcs of this ruling being so chosen that they can be extended"*, p. 176): **proved**
  (`doubleRuling_refine`, `Space.ArcRuling.refine`; Axioms 1–8) for any property `Good` of
  subdivisions inherited by subsets.
* **Theorem G's nine-cell ruling** (p. 177, *"`Jₙ₊₁` can be divided by a double ruling … into nine
  subdivisions of which the central one is `AₙBₙCₙDₙAₙ`"*) is the case of Theorem C for a curve
  within `ABCDA`; it is not covered by Theorem C's indication of proof. Noted for batch 142.

### Moore 1919, Theorem C corrected; Theorem D (batch 142)

Formalized in `HPC/Moore/M19CD2.lean` (umbrella, with the three forms of Theorem C and the region
form of D) and `HPC/Moore/M19D*.lean` (REPORT-batch142.md). Lean names are in the group *Moore 1919
C corrected, D (batch 142)* of `Axioms.lean` / `axioms.txt` (standard axioms only); the audit of the
new theorems is `doc/batches/audits/axioms-batch142.txt`. Quotations are from pp. 172–176 of
`doc/sources/moore1919.pdf`. All names are in namespace `HPC.Moore`. Outcome: the three corrected
forms of Theorem C and Theorem D (curve and region forms) are **proved**, Theorem D by a route that
replaces Moore's.

**Outcome of the checks of COMMISSION-batch142.md §3.**

1. **Theorem C** (*"If the closed curve `g` has only a finite number of points in common with the
   closed curve `ABCDA` and does not contain `A`, `B`, `C`, or `D` then the interior of `ABCDA` can be
   divided by a double ruling … into subdivisions such that the interior of each one of them is either
   wholly within or wholly without `g`"*). **Proved with the hypothesis "no touching from within"**
   (`m19_theoremC_corrected`, Axioms 1–8), in the skeleton's form: no point `P` of `g ∩ ABCDA` is a
   common end of two arcs `K₁, K₂` of `g` with `K₁ ∩ K₂ = {P}` and `Kᵢ − P` within `ABCDA`. The
   hypotheses that `g ∩ ABCDA` is finite and that `A, B, C, D ∉ g` are kept; `hfin` is used by the
   proof (the part of `g` within `ABCDA` is cut into finitely many cross-cuts) and is not shown to be
   removable. **Touching from without is harmless**: the hypothesis says nothing about a point of
   `g ∩ ABCDA` at which `g` stays without `ABCDA`, and the theorem holds there. The two other forms
   are proved too: finitely many pairwise disjoint cross-cuts with ends off `A, B, C, D`
   (`m19_theoremC_crosscuts`), and a closed curve within `ABCDA` (`m19_theoremC_within`; the
   nine-cell form of Theorem G is not stated).
2. **Theorem D, the choice of `J̄`** (*"There exist, on the segments `ĒₙF̄₁, F̄ₙL̄₁, L̄ₙM̄₁`, and `M̄ₙĒ₁`
   respectively, points `B̄, C̄, D̄`, and `Ā` that are not on `g₁`. The arcs of `α` form a closed curve
   `ĀB̄C̄D̄Ā` which will, at times, be called `J̄`. This curve does not have more than a finite number
   of points in common with `g₁`."*, p. 175). Moore secures only finiteness of `J̄ ∩ g₁`, which does not
   exclude `g₁` touching `J̄` from within, the configuration in which Theorem C fails
   (`not_m19_theoremC_printed`). Whether `J̄` can be re-chosen so that `g₁` crosses it at every common
   point is **not decided** here; Moore's proof, as written, does not give it, so it **fails at this
   step**. **Replaced**: the proof does not use `J̄`. The roles are exchanged: `ABCDA` is kept and a
   closed curve `h` within `g₁`, whose interior contains the part `F` of `ABCDA + I` not within the
   other curves, is built so as to cross `ABCDA` at each of its finitely many common points
   (`exists_nice_curve`): lenses about the points of `F ∩ ABCDA` (an arc within `I` and an arc without
   `I` with common ends, Theorems 27 and 28; `lens_data`), with distinct ends (`lens_family`), and
   curves missing `ABCDA` about the other points of `F` (Theorem 36), merged by Theorem 42
   (`merge_nice`). A crossing excludes touching (`Space.Crosses.no_fork`), so the corrected Theorem C
   applies to `h` (`curve_rulable`).
3. **Theorem D, the induction** (*"If any of them are wholly without `g₁`, then each such subdivision
   can itself be divided by a double ruling … into subdivisions each of which is either wholly within
   some curve of the set `G` or wholly without `g₂`. … It can be shown in a similar way that there
   exists a double ruling `τ₃` … This process may be continued."*, p. 175). The obstruction recorded in
   batch 141 (the boundary of a subdivision of `τ₁` may meet `g₂` in infinitely many points, so that
   Theorem C does not apply) is **avoided**: the induction is on the number of curves of a finite
   subcover (`rulable_of_cover`). A subdivision of the ruling missing `h` lies within `h` (hence within
   `g₁`) or without `h`; in the second case it is a quadrilateral whose closure is covered by the
   remaining curves, and the induction hypothesis is applied to it, which builds a new curve about
   *its* uncovered part. No subdivision boundary is ever compared with a given curve `g₂`. The
   rulings of the subdivisions are combined by the refinement lemma of batch 141
   (`Space.ArcRuling.refine`).
4. **Theorem D, `J′`** (*"It easily follows that there exist (Fig. 2) (1) on `ABCDA`, `4n` points …
   (2) within `ABCDA` a closed curve `J′` …"*, p. 174). **Not needed**: the proof uses neither `J′`,
   nor the annulus between `J` and `J′`, nor the arcs `EᵢE′ᵢ` of p. 173 and the arc of footnote *
   (`m19_D_arc`, batch 140), nor Theorem B.

**Further outcomes.**

* **Theorem D, region form** (as used in Theorem E, p. 176): proved unconditionally
  (`m19_theoremD_regions`, from `m19_theoremD` and `m19_theoremD_regions_of_curves`).
* **Cross-cuts** (commission item A.1): proved by induction on a weight of the system (opposite
  sides 1, adjacent sides 2, one side 3): a cross-cut joining opposite sides is cut along; otherwise,
  for a cross-cut `t` whose pocket is maximal, with an end `a` on `AB` (after rotating), the ruling
  arc `ac + u` is cut along, `ac` a piece of `t` and `u` an arc through the outer tile from `c` to a
  point of `CD` on no base of a maximal pocket; the rest of `t` is a cross-cut of one half, of smaller
  weight (`chords_rulable`, `absorb_step`,
  `opp_step`, `M19DChords.lean`). This is Moore's three chord types, with the completion of a
  non-opposite cross-cut to a ruling arc made explicit.

### Moore 1919, Theorems E and F; the Schoenflies form (batch 143)

Formalized in `HPC/Moore/M19EF.lean` (umbrella, the skeleton's three statements verbatim),
`HPC/Moore/M19E*.lean`, `HPC/Moore/M19F.lean`, and the two files of pure topology
`HPC/Moore/GridSquare.lean`, `HPC/Moore/GridMesh.lean` (namespace `HPC.Sq`) (REPORT-batch143.md).
Lean names are in the group *Moore 1919 E–F (batch 143)* of `Axioms.lean` / `axioms.txt` (standard
axioms only); the audit of the new theorems is `doc/batches/audits/axioms-batch143.txt`. Quotations are
from pp. 176–177 of `doc/sources/moore1919.pdf`. All names are in namespace `HPC.Moore` unless stated.
Outcome: Theorem E (`m19_theoremE`), the Schoenflies form (`m19_schoenflies`) and Theorem F
(`m19_theoremF`) are **proved** (Axioms 1–8). Theorem E is proved by a route that differs from
Moore's at step 4: it is derived from the Schoenflies form.

**Outcome of the checks of COMMISSION-batch143.md §3.**

1. **Theorem E (3)** (*"each point on ABCDA, with the exception of A, B, C, and D, is an endpoint
   either of just one arc of α₁ or of just one arc of α₂"*). **Read exclusively** and proved in that
   form: every point of `ABCDA` other than `A, B, C, D` is an endpoint of just one arc of one family
   and of **no** arc of the other. So no point of a side is an endpoint of arcs of both families, not
   even near the corners. The corners themselves are endpoints of no arc. In the proof, `α₁` is the
   set of images of the segments `p.2 = t` (`0 < t < 1`) of the unit square, with ends on `AB`
   (`p.1 = 0`) and `CD` (`p.1 = 1`), and `α₂` the images of the segments `p.1 = s`, with ends on `BC`
   and `DA`. A non-corner point of `AB` or `CD` therefore has second coordinate in `(0, 1)` and first
   coordinate `0` or `1`, so it is not an end of a vertical segment (`theoremE_of_square`).
2. **Theorem E, step 4** (*"If P is a point within or on ABCD, distinct from A, B, C, and D, and not on
   any arc of the set {ᾱ₂} it can be proved that there exists through P, and with endpoints on ABCDA,
   just one arc that does not intersect any arc of the set {ᾱ₂}"*). Moore gives no argument. **The
   step is replaced**: the limit arcs are not built one at a time. All arcs of all the rulings `βₙ`,
   together with the sides, are taken as two families of "lines" in `J + I`. Each line has a position
   in `[0, 1]`, the parameter of its end on `AB` (resp. `BC`), and two closed sides
   (`lineFam`, `HPC/Moore/M19EFamily.lean`; the sides of a cross-cut are built in
   `HPC/Moore/M19ELines.lean`). A point `z` gets the coordinates `(pos_Y z, pos_X z)`, where `pos_X z`
   is the infimum of the positions of the lines having `z` on their lower side. This map is continuous
   and injective because the mesh tends to `0` (see below), and it is onto `[0, 1]²`
   (`HPC.Sq.Grid.exists_square`). Its inverse is the homeomorphism of the Schoenflies form, and the
   limit arcs are the images of segments at positions that are not positions of lines. The three
   things the commission asked for follow from the square: these sets **are arcs** (images of
   segments under an embedding), they are **unique** in the sense of (4), and **(3) and (5)** hold,
   including at points of `ABCDA` that are limits of ends. Moore's uniqueness claim *among all arcs*
   through `P` that miss the arcs of `ᾱ₂` is not formalized as stated. Theorem E does not need it.
   **The mesh tends to 0** (`preGrid_box_sub_cell`, `HPC/Moore/M19EMesh.lean`): the sides and the arcs
   of `βₙ` cut `J + I` into boxes, and each box lies in one subdivision of `βₙ`. This is a counting
   argument (`HPC.Sq.PreGrid.box_sub_component`): there are `(n+1)(m+1)` boxes, they are nonempty and
   disjoint, and they cover `I − ⋃ arcs`, which has exactly `(n+1)(m+1)` components (the subdivision
   lemma of batch 141, `doubleRuling_cells_ncard`). So each component lies in one box and each box in
   one component.
3. **Theorem E, "This process may be continued"** (*"Each of these subdivisions can be divided by a
   double ruling into subdivisions each of which is within some region of the set G₂ the arcs of this
   ruling being so chosen that they can be extended in such a way that there will result a double
   ruling β₂ of ABCDA such that each arc of β₁ is an arc of β₂ … This process may be continued."*).
   **Proved** as `nested_rulings` (`HPC/Moore/M19ESeq.lean`): for any sequence of covers by regions,
   there is a sequence of double rulings whose `k`-th has every subdivision inside a region of the
   `k`-th cover, contains every arc of the previous one, and refines it. The step is
   `doubleRuling_refine` (batch 141, the extension of the arcs across subdivisions) together with
   Theorem D in region form, `m19_theoremD_regions` (batch 142), applied on each subdivision.
4. **Theorem E, first sentence of the proof** (*"For each positive integer n there exists, about each
   point P of ABCDA plus its interior, a fundamental region of subscript greater than n."*). This is
   Axiom 1 (1). **Confirmed**: Theorem D is applied to a *set of regions* covering `J + I`, in its
   region form. Moore's instance is `nested_rulings_fund`: each subdivision of the `k`-th ruling lies
   in a fundamental region `K l` with `l > k`. The Schoenflies proof uses another cover by regions,
   namely the regions lying in a ball of radius `1/(k+1)` for a metric of the space (the space is
   metrizable, `metrizable`). This makes "the cells shrink" a statement about distances.
   Moore's cover would do as well with Axiom 1 (2).
5. **Theorem F** (*"It follows, with the aid of Theorem 12, that there exists, for each n, a finite set
   Gₙ of closed curves such that every point of the fundamental region Rₙ is within some curve of the
   set Gₙ and every curve of the set Gₙ encloses a point of Rₙ."* and *"There exists a finite set of
   curves enclosing J′₁ + J′₂ + A′₁A′₂. It follows that there exists a closed curve J₂ enclosing J₁, R₁,
   and R₂."*). The first sentence needs a finite cover of the **closure** `R′ₙ` of `Rₙ`, not of `Rₙ`.
   That is Theorem 12 (compactness) applied to `R′ₙ`, which is compact (`isCompact_closure_region`).
   With that reading **it is what is needed**. The second sentence uses Theorem 42, which needs **the
   union of the interiors to be connected**. Moore's sentence does not say so; the gap can be
   filled, and is. `exists_curve_about_compact` (`HPC/Moore/M19F.lean`) covers a compact set by finitely
   many interiors (Theorem 36). It ties them to a base point by arcs (Theorem 15), which gives a
   connected compact set. It then covers that set by finitely many interiors each meeting it, so their
   union is connected, and encloses them by Theorem 42. **"Encloses"** is Moore's "lies within": the
   proof's *"a closed curve Jₙ that encloses the interiors of all the curves of the set Gₙ"* encloses a
   set by having it within. The shape `Jₙ ∪ Iₙ ⊆ Iₙ₊₁` (the curve and its interior lie within `Jₙ₊₁`)
   is proved. `Jₙ₊₁` is a curve about the compact set `Jₙ + Iₙ + R′ₙ₊₁` (`m19_theoremF_proof`).

**Further outcomes.**

* **Schoenflies form** (commission item B): proved (`m19_schoenflies`, Axioms 1–8). `ABCDA` plus its
  interior is the image of an embedding of `[0, 1]²`, with sides to sides and `A, B, C, D` to
  `(0,0), (0,1), (1,1), (1,0)`. The construction takes parametrizations of `AB` and `BC` as input.
  It is not stated or proved here that the embedding restricts to them on these sides.
* **A compact set with a grid of vanishing mesh is a square** (`HPC.Sq.Grid.exists_square`, pure
  topology): stated for two families of closed "half-planes" in a compact metric space. It has
  nothing specific to Moore's axioms.

### Moore 1919, the plane: Theorem G and the final paragraph (batch 144)

Formalized in `HPC/Moore/M19G.lean` (umbrella, the skeleton's statements; one shape change, see
below) and `HPC/Moore/M19GSquare.lean`, `M19GPaste.lean` (pure topology, namespace `HPC.Sq`),
`M19GBoundary.lean`, `M19GCuts.lean`, `M19GSplit.lean`, `M19GCollar.lean`, `M19GPlane.lean`,
`M19GCor.lean` (REPORT-batch144.md). Lean names are in the group *Moore 1919, the plane (batch 144)*
of `Axioms.lean` / `axioms.txt` (standard axioms only); the audit of the new theorems is
`doc/batches/audits/axioms-batch144.txt`. Quotations are from pp. 169 and 177–178 of
`doc/sources/moore1919.pdf` and pp. 159, 163 of `doc/sources/moore1916.pdf`. All names are in
namespace `HPC.Moore` unless stated.
Outcome: **`m19_plane` is proved**: a space satisfying Axioms 1–8 of F.A. is homeomorphic, in its
region topology, to `ℝ × ℝ`. Theorem G (`m19_theoremG`), the open-curve property (`m19_openCurve`)
and the final paragraph (`m19_final`) are proved as corollaries. The route differs from Moore's
after Theorem F: the Schoenflies route of REPORT-batch143, accepted by the commission.

**Outcome of the checks of COMMISSION-batch144.md §3.**

1. **Fig. 3** (*"there exist on `Jₙ₊₁` four distinct points `Aₙ₊₁`, `Bₙ₊₁`, `Cₙ₊₁`, and `Dₙ₊₁` such
   that `Jₙ₊₁` can be divided by a double ruling … into nine subdivisions of which the central one is
   `AₙBₙCₙDₙAₙ (Jₙ)`"*). Unargued in Moore. **Not proved as stated; replaced.** The proof uses, in
   place of the nine-cell ruling, **two** cuts of the annulus: disjoint arcs `PP'`, `QQ'` from `Jₙ` to
   `Jₙ₊₁`, each meeting `Jₙ ∪ Iₙ` only in `P` (resp. `Q`) and `Jₙ₊₁` only in `P'` (resp. `Q'`)
   (`exists_cuts`, `HPC/Moore/M19GCuts.lean`: put `Jₙ₊₁ ∪ Iₙ₊₁` on a square; the cuts are the
   horizontal segments from the extreme points of `Jₙ ∪ Iₙ` on one line to the two vertical sides). They cut the closed
   annulus into **two quadrilaterals** `PP'Q'QP` and `QQ'P'PQ` with disjoint interiors whose union
   with their boundaries is `Jₙ₊₁ + Iₙ₊₁ − Iₙ` (`annulus_decomp`, `HPC/Moore/M19GSplit.lean`, by the
   splitting of an interior along an arc, `half_split`). The commission suggested four quadrilaterals;
   two suffice. Each quadrilateral receives a square map with prescribed boundary (item A), the two
   agreeing on the cuts, and the result is a collar of `Jₙ` (`exists_collar`).
2. **The open curves `kₘ`, `tₙ`** (*"It follows that there exists a set of open curves `[kₘ]` … and
   another set `[tₙ]` such that (1) … (2) … (3) …"*). Unargued in Moore. Moore's route needs them;
   **ours does not**: no curve `kₘ`, `tₙ` is constructed. Their analogues are the images under the
   homeomorphism of `m19_plane` of the lines `x = m`, `y = n`, if they are wanted.
3. **"This process may be continued. It follows that there exist two sequences of arcs `gₘ₀, gₘ₁,
   …`"** and **"The sum of all the arcs … is clearly a continuous open curve"** (p. 178). Both
   unargued in Moore. **Not needed** on our route: no infinite chain of arcs is formed. The
   corresponding open curves are images of closed embeddings of `ℝ` (lines of `ℝ²` under the
   homeomorphism), and that these are open curves in F.A.'s sense is `m19_openCurve`. (The infinite
   process of our route is the pasting of the annulus maps, `HPC.Sq.exhaust_homeomorph`.)
4. **"It is clear that through every point there is just one curve of the set `α` and just one curve
   of the set `β` and furthermore each curve of the set `α` has just one point in common with each
   curve of the set `β`"** (p. 178). Unargued in Moore. **Supplied** by `m19_theoremG`: `G₁` and `G₂`
   are the images of the horizontal and the vertical lines (`theoremG_of_homeomorph`).
5. **The final paragraph**: *"Between the points of `t₀` and the set of all real numbers there is a
   one-to-one continuous correspondence"* (using F.A. p. 159 and the 1915 characterization of the
   line) and *"It is clear that the correspondence thus established … is continuous"*. Both unargued
   in Moore. **Supplied** by `m19_final`: a bijection `e : S ≃ ℝ × ℝ` such that `P` is a sequential
   limit point of `P₁, P₂, …` (Moore's `IsSeqLimit`) if and only if `e Pₙ → e P`. The 1915
   characterization of the line is not used: the correspondence is the homeomorphism of `m19_plane`.
   The commission's note that metrizability (batch 137) makes sequential and topological continuity
   agree is not needed either: `isSeqLimit_iff_tendsto` shows directly, from Axiom 1, that Moore's
   sequential limits are the limits of the region topology, and `ℝ²` is first countable.
6. **"Σ₁ or Σ₂"** (p. 169: *"every space `S` that satisfies Σ₁ or Σ₂ is a number plane"*).
   **`m19_plane` is stated for Σ₁** (Axioms 1–8), as in the skeleton. F.A. p. 163: *"Let Σ₂ denote
   the set of Axioms 1–5, 6′, 7′, 8"*, with *"AXIOM 6′. If R is a region and AB is an arc such that
   AB − A is a subset of R then (R + A) − AB is connected"* and *"AXIOM 7′. Every boundary point of a
   region is a limit point of the exterior of that region"*; and *"though Σ₁ and Σ₂ are not absolutely
   equivalent, they are equivalent with respect to point and limit point of a point-set"*. The Σ₂ case
   of Moore's theorem is **not formalized**. For batch 145 it is not needed **provided** the
   decomposition space is shown to satisfy Axioms 6 and 7 themselves (with the regions defined there),
   which is what Moore 1925 Theorem 21 does after verifying 6′ and 7′; then `m19_plane` applies as it
   stands. Only if that verification were to fail or be skipped would the Σ₂ form (via F.A.'s
   equivalence "with respect to point and limit point", which F.A. does not prove) be needed.

**Further outcomes.**

* **Schoenflies with prescribed boundary** (item A, `m19_schoenflies_boundary`, Axioms 1–8): proved.
  Two sides from the grid construction (`HPC.Sq.Grid.exists_square_param`, from
  `Grid.mem_L_of_pos_eq`), the other two by a homeomorphism of the square fixing the sides `p.1 = 0`
  and `p.2 = 1` pointwise (`HPC.Sq.exists_square_reparam`).
* **The annulus lemma** (item B): **shape change**, the skeleton's `True` replaced by the collar form
  `m19_annulus` (an embedding of `J₁ × [0, 1]` onto `J₂ + I₂ − I₁`, the identity on `J₁ × 0`, onto
  `J₂` on `J₁ × 1`) and the square form `m19_annulus_square` (added): a square map of radius `r`
  onto `J₁ + I₁` extends to one of radius `r + 1` onto `J₂ + I₂`, mapping the square annulus onto the
  closed annulus. Proved (Axioms 1–8).
* **Open curves in F.A.'s sense** (`Space.IsOpenCurveFA`, p. 159: *"a closed, connected set of
  points M such that if P is a point of M then M − P is the sum of two mutually exclusive connected
  point-sets, neither of which contains a limit point of the other one"*). The two point-sets are
  taken nonempty. `m19_openCurve` (Axiom 1 only): the image of a closed embedding of `ℝ` is one.
* **A closed curve has only one interior** (`interior_unique`, Axioms 1–5, 7) and **every closed
  curve with its interior is a square with boundary the curve** (`exists_square_of_interior`).

### Moore 1925, *Concerning upper semi-continuous collections of continua*, §I, Theorems 1–4 (batch 145)

Formalized in `HPC/Moore/M25A.lean` (umbrella) and `HPC/Moore/M25Defs.lean` (the skeleton's
definitions, verbatim), `M25Plane.lean` (plane facts), `M25Quot.lean` (the quotient, Theorem 1),
`M25Thm.lean` (Theorems 3, 4), `M25Thm2.lean` (Theorem 2), `M25Ax.lean`, `M25FA.lean` (the claim of
p. 420) (REPORT-batch145.md). Lean names are in the group *Moore 1925 §I, Theorems 1–4 (batch 145)*
of `Axioms.lean` / `axioms.txt` (standard axioms only); the audit of the new theorems is
`doc/batches/audits/axioms-batch145.txt`. Quotations are from pp. 416–420 of
`doc/sources/moore1925.pdf` and pp. 307–313 of `doc/sources/moore1925-primeparts.pdf`. All names are
in namespace `HPC.Moore`.
Outcome: items A–G **proved**; nothing open. The space of elements of a decomposition satisfying
`MooreDecomp` is the quotient; Moore's limit element, domain and boundary are the quotient notions;
Theorems 1–4 hold; Axioms 1, 2, 4, 5 and F.A. Theorem 4 (nonempty regions) hold for Moore's regions
(`m25_axioms1245`). No Jordan curve theorem is used: Brouwer's boundary theorem and Janiszewski's
theorem are proved by logarithms (Eilenberg's method).

**Outcome of the checks of COMMISSION-batch145.md §3.**

1. **Theorem 1, I** (*"Since `p` is closed and bounded the sequence `X₁, X₂, ⋯` contains a
   subsequence of distinct points which has as its sequential limit point some point `X` in `p`"*,
   p. 418). **Recorded; harmless.** The `Xₙ` may take finitely many values, and then no subsequence
   of distinct points exists; a constant subsequence does the job. Our proof does not use sequences:
   Theorem 1 (closed part) is `isClosedMap_mk_plane`, from the compactness of the elements and
   Moore's u.s.c. (`m25_theorem1`).
2. **Theorem 1, II** (*"Let `p` denote that element of `H₁` which contains `p`"*). **Recorded; a
   typographical slip**: the second `p` is the point `P`. The connected part of `m25_theorem1` is
   the continuity of the quotient map.
3. **Definition of boundary** (*"the set of all elements `[x]` of `H` such that `x` either belongs to
   `H` and is a limit element of the set `G—H` or `x` does not belong to `H` but it is a limit element
   of `H`"*, p. 417). **Confirmed**: read as printed ("elements `[x]` of `H`"), the second clause is empty.
   Read "elements `[x]` of `G`", it is the quotient frontier: `m25_boundary_iff` (with
   `isLimitElt_iff`).
4. **Definition of complementary domain** (*"A domain of elements of `G` is said to be a
   complementary domain of a closed set `H` of elements of `G` provided the boundary of `D` is a
   subset of `H`"*). **Recorded.** As printed, `G` is a complementary domain of every closed `H` (empty
   boundary), and so is the interior of a closed disc of elements, of the disc; "*the* unbounded
   complementary domain" (pp. 417, 418) is then not unique. **Theorem 2 fails under the literal
   reading** (informal argument, not formalized): take the decomposition into points, `M` a closed
   disc and `D` the open disc minus a radius (a bounded domain with boundary the circle plus the
   radius, a subset of `M`). The plane minus the radius is an unbounded domain whose boundary (the
   radius) lies in the boundary of `D`, so under the literal reading it is an "unbounded
   complementary domain" of `∂D`; its boundary `K` is a segment, and `K − p` is disconnected for an
   interior point `p`. The skeleton reads "component of `Hᶜ`", presumably Moore's intent; so read,
   the unbounded complementary domain of a set of elements with bounded point set exists and is
   unique (`m25_unbounded_unique`, which needs neither closedness of `H` nor `MooreDecomp`: shape
   change), and Theorem 2 holds (`m25_theorem2`).
5. **Theorem 2's proof.** (a) *"Since each point of `B` belongs to some element of `K` and each
   element of `K` contains a point of `B` and `B` is a closed and connected set of points, therefore,
   by Theorem 1, `K` is a closed and connected set of elements"*. **Supplied by Brouwer twice**:
   `∂D` is connected by Brouwer applied to the continuum `M` (`quot_brouwer`, from
   `brouwer_boundary` in the plane), and then `K = ∂E` is connected by Brouwer applied to the
   continuum `∂D`. Closedness of `K` is that of a frontier. Our proof works with sets of elements
   throughout; the point set `B` is not needed. (b) *"Clearly `Dₓ` contains `D`"*: `D` is connected
   and misses `H + p ⊆ K ⊆ ∂D` (an open set misses its frontier), so it lies in the component `Dₓ`.
   (c) *"But `q` does not belong to the boundary of `Dₓ`"*: `∂Dₓ ⊆ H + p` (a component's frontier lies
   in the removed closed set), and `q ∈ N` is neither in `H` nor `p`. (d) Moore's *"`H + p` and
   `N + p` are both closed and connected"*: only **closedness** is used (each is `K − p` minus an open
   set, plus `p`); Janiszewski (`janiszewski_compact`) needs only that the intersection, the element
   `p̄`, be connected. (e) `K − p ≠ ∅` (Moore's connectedness admits the empty set; ours does not): if
   `K = {p}` then `E ⊇ G − p`, which contains `D`.
6. **Theorem 3's statement** (*"there exists a region of elements of `G` such that every element of
   this region is at an upper distance less than `e` from the element `p`"*) omits "containing `p`".
   **Recorded**; `m25_theorem3` has `p ∈ R` (skeleton). Moore's proof gives it (`p̄ ⊆ D`).
7. **Theorem 3's proof.** All four sentences are **supplied**:
   (a) *"The point set `H̄` is a continuum"*: `H = [J]` is closed (closed map) and connected (image of
   `J`); `H̄` is connected because the elements are connected and the map is closed
   (`isConnected_ptsOf`), and closed since `H` is.
   (b) *"It follows that the boundary of `R` is connected"*: `quot_brouwer` (Brouwer in the plane,
   through `ptsOf_connectedComponentIn` and `frontier_eq_image`).
   (c) *"But clearly `R` is a domain"*: components of open sets of elements are open
   (`isOpen_connectedComponentIn_quot`), so `R`, the component of `Hᶜ` containing `p`, is a connected
   open set, i.e. a Moore domain (`m25_domain_iff`). Moore's `R` (elements that are subsets of `D`)
   is ours: `R̄` is the component of `H̄ᶜ` containing `p̄` (`ptsOf_connectedComponentIn`), i.e. `D`.
   (d) *"the boundary of `R` consists of all those elements `[g]` of `G` such that `g` contains a point
   of `B`"*: `frontier_eq_image`.
   The last sentence (*"Every element which belongs to it is at an upper distance less than `e` from
   the element `p`"*) uses `D ⊆` interior of `J` (`R̄` lies in the component of `Jᶜ` containing `p̄`,
   the polygon's interior), and the interior of `J` lies in the `e`-tube. The enclosing curve is a
   polygon (`planeFacts_holds.enclose`), not PNAS 1925 Theorem 1.
8. **Theorem 4** (*"The truth of Theorem 4 may be easily established with the help of Theorem 3"*).
   **Recorded; supplied** (`m25_theorem4`). The proof uses: `isLimitElt_iff` (the tubes of the
   `e`-thickenings of `p̄` form a neighbourhood basis of `p`: Moore's u.s.c. and the closed map);
   Theorem 3 in tube form (`exists_region_in_tube`: a region about `p` inside every such tube); and
   the openness of regions.
9. **The p. 420 claim** (*"By methods largely analogous to those used in a similar connection in my
   paper Concerning the prime parts of a continuum it may be shown that … Axioms 1, 2, 4 and 5 and
   Theorem 4 of F. A. hold true and consequently Theorems 1–15 of that paper all hold true"*).
   **Recorded; proved** (`m25_axioms1245`, Theorem 4 for nonempty regions; `m25_FA_1_15`). What the
   Math. Z. paper supplies (pp. 310–313): regions `R_pe` defined by upper distance (Definition,
   p. 310), so Axiom 2 there is immediate from the definition; Theorem 10 (*"The prime part `p` is a
   limit element of the set of prime parts `K` if, and only if, every region which contains `p`
   contains at least one prime part which belongs to the set `K` and is distinct from `p`"*), the
   analogue of 1925 Theorem 4; Theorem 11 (closed sets of prime parts ⇔ closed point sets), the
   analogue of 1925 Theorem 1; Theorem 12 (*"Every closed set of prime parts has the Heine-Borel-
   Lebesgue property"*, by circles about the points and Theorem 7), the model for Axiom 4; and
   Theorem 13 (Axiom 1: *"for each positive integer `n`, `M` is covered by a finite set of regions
   `Hₙ₁, …, Hₙₘₙ`, all of radius less than `1/n`. Let `K₁, K₂, K₃, …` denote the infinite sequence of
   regions `H₁₁, …, H₁ₘ₁, H₂₁, …`"*). "Methods largely analogous" therefore amounts to: Theorem 13's
   construction for Axiom 1 (our `m25_axiom1` is exactly it: finite covers at level `k` by regions in
   balls of radius `1/(k+1)` of a compatible metric, laid end to end, with Theorem 3 in place of the
   radius of `R_pe`); Theorem 12's argument for Axiom 4 (ours: `R'` is a closed subset of the compact
   image of `closure R̄`). **Corrected in batch 146** (COMMISSION-batch146.md §0): the Math. Z.
   paper, p. 313, claims *"Axioms 1, 2, 4 and 5₁ and Theorem 4 of F. A."*, with the subscript (clear
   on the 400-dpi image, lost in `pdftotext`). Axiom 5₁ (three points) holds in a compact space of
   prime parts, so the earlier remark here, that Axiom 5 *"fails there"*, concerned a claim the
   paper does not make, and is withdrawn. The 1925 paper prints Axiom 5 without subscript (p. 420,
   400-dpi); in the 1925 setting the plane is unbounded and Axiom 5 holds (`m25_axiom5`: the elements
   of the points `(n, 0)`).
10. **The u.s.c. definition** (*"for each element `g` of the collection `G` and each positive number `e`
    there exists a positive number `d` such that if `x` is any element of `G` at a lower distance from
    `g` less than `d` then the upper distance of `x` from `g` is less than `e`"*, p. 416) against the
    open-set form. **Equivalent for compact elements**: `isClosedMap_mk_plane` (u.s.c. ⇒ closed map;
    uses the compactness of the elements: a closed set missing an element misses a thickening of it)
    and `usc_of_isClosedMap` (closed map ⇒ u.s.c.; uses compactness to fit a thickening inside the
    open preimage of a tube).

**Further outcomes.**

* **Brouwer's boundary theorem** (`brouwer_boundary`) and **Janiszewski's theorem for compact
  sets** (`janiszewski_compact`, intersection connected or empty): proved from the unicoherence of the
  plane (`plane_unicoherent`, closed sets not necessarily bounded) and Borsuk's logarithm criterion.
  Neither needs the Jordan curve theorem. Shape change: both are stated without the section
  hypothesis `hG` (plane facts).
* **The region topology of the space of elements is the quotient topology** (`spaceOfElts_topology`);
  Moore's `M'` is the quotient closure (`cl_eq_closure_quot`).
* **F.A. Theorem 15 for the space of elements** (`m25_fa_theorem15`): batch 137's construction with
  metrizability from the quotient, not from Axiom 3 (which for the space of elements is batch 147's).

### Moore 1925, §I, Theorems 5–12; Mullikin 1922, Theorems 4 and 5; Moore 1920, Theorem 4 (batch 146)

Formalized in `HPC/Moore/M25B.lean` (umbrella) and `HPC/Moore/CutArc.lean` (cut-point arcs, the
circle characterization), `M25BDefs.lean` (the skeleton's definitions, verbatim), `M25B5.lean`
(Theorems 5–8), `M25B9.lean` (Theorems 9, 10, 12), `Borsuk.lean` (Borsuk's logarithm theorem for the
plane), `Mullikin.lean` (Mullikin's Theorem 5, corrected), `Mullikin4.lean` (her Theorem 4 at
`M₁ ∩ M₂ = ∅`), `M25B11.lean` (Theorem 11), `M25BPts.lean` and `M25BRefute.lean` (the decomposition
into points; the refutations) (REPORT-batch146.md). Lean names are in the group *Moore 1925 §I,
Theorems 5–12 (batch 146)* of `Axioms.lean` / `axioms.txt` (standard axioms only); the audit of the
new theorems is `doc/batches/audits/axioms-batch146.txt`. Quotations are from pp. 417, 420–422 of
`doc/sources/moore1925.pdf`, pp. 144, 154, 160 of `doc/sources/mullikin1922.pdf`, p. 342 of
`doc/sources/moore1920.pdf` and pp. 171–173 of `doc/sources/moore1924-pcs.pdf`. All names are in
namespace `HPC.Moore`.
Outcome: items A–G **proved** (refutations A and B1 proved as negations); nothing open. Every
skeleton statement is verbatim except `not_m25_theorem7_printed`, whose placeholder `True` is
replaced by the negation of the printed Theorem 7.

**Outcome of the checks of COMMISSION-batch146.md §3.**

1. **Theorem 8's proof** (p. 421). (a) *"It is easy to see that `K₁ + p` and `K₂ + p` are both
   closed and connected"*. **Confirmed**: `K₂` is open in `K − p`, so `K₁ + p = K − K₂` is closed;
   likewise `K₂ + p`; connectedness of `Kᵢ + p` is the standard fact for a separation of `K − p`
   (batch 94's `exists_two_nonCutPoints` setting). (b) *"if `q` denotes some element of `K₂`, `K₂ +
   p` would be a simple continuous arc having `p` and `q` as its extremities"*. **Confirmed, with
   the conditions supplied**: `p ≠ q` since `q ∈ K₂ ∌ p`; `K₂ + p ⊆ K` is bounded; and the negated
   supposition (*no* element of `K₂` fails to disconnect `K₂ + p`) makes every element of `K₂`,
   hence every element other than `p` and `q`, disconnect `K₂ + p`. Theorem 5 then contradicts the
   supposition at `q` itself. Our proof (`m25_theorem8`) follows Moore in substance through
   Nadler 6.7 (`exists_nonCut_diff`, `CutArc.lean`): the non-cut point theorem replaces the appeal
   to Theorem 5.
2. **Theorem 11's proof.** (a) *"By Theorem 9 neither `a` nor `b` separates `G` and therefore neither
   `ā` nor `b̄` separates `S`"*. **Confirmed** (`not_separatesPlane_ptsOf`): the point set of the
   complement of `a` is the complement of `ā`, and the point set of a connected set of elements is
   connected (batch 145's `isConnected_ptsOf`: closed monotone map). (b) *"It is easy to see that
   one of these domains (call it `D₁`) is bounded and the other one (`D₂`) is unbounded"*.
   **Supplied**: two unbounded complementary domains coincide (`m25_unbounded_unique`), and if both
   were bounded the plane `D₁ ∪ D₂ ∪ J̄` would be bounded. (c) *"Clearly `I` and `E` are domains of
   elements of `G` and `I + E = G − J`"*. **Supplied** (`ptsOf_image_eq_of_split`): each element off
   `J̄` is connected, so lies in `D₁` or in `D₂`; hence `D₁`, `D₂` are saturated, `I`, `E` are open
   (quotient topology) and connected (images), and they cover `G − J` disjointly.
3. **Theorem 11's proof:** *"In a similar way it may be proved that `J` is also the boundary of `E`"*.
   **Confirmed**: the boundary step is proved once (`frontier_eq_of_scc`: for any nonempty open set
   of elements missing `J` with frontier in `J`, the frontier is `J`) and applied to `I` and to `E`.
4. **Theorem 11's proof, the main gap** (*"If `B` is not identical with `J` then it is a proper
   subset of `J`. It easily follows, with the help of Theorems 10 and 6, that `B` is a simple
   continuous arc of elements of `G`. But `B` separates `G` and, by Theorem 9, no arc separates
   `G`"*). **Confirmed as a gap**: Theorem 6 needs `B` connected, which is not shown. **The
   commission's repair is confirmed and used** (`frontier_eq_of_scc`): for `x ∈ J − B`, two arcs of
   `J` from `x` (Theorem 10) give elements `p₁`, `q₁` on either side of `x` such that the sub-arc `C`
   of `J` through `x` between them misses the closed set `B`; by Theorem 10 again and irreducibility,
   `C` is one of the two arcs of `J` from `p₁` to `q₁`, and the other, `A`, contains `B` and misses
   `x`. Then `G − A = I ∪ (E ∪ (J − A))`, and `I`, `(cl I)ᶜ` separate it (`cl I ⊆ I ∪ B`), against
   Theorem 9 for `A`.
5. **Theorem 12's proof:** *"Since `D₂` is bounded it has at least one boundary element"*.
   **Recorded**: true for nonempty `D₂` (a nonempty proper open subset of the connected space of
   elements has nonempty frontier). "Domain" is read as nonempty: the skeleton's `IsConnected D₂`
   includes nonemptiness (`m25_theorem12`, Moore's proof as printed otherwise).
6. **P.C.S. footnote** (*"In this paper in the statement of Lemma 5 replace the last "M" by "K""*,
   1925 p. 421). **Recorded; Lemma 5 is not used.** With the erratum, P.C.S. Lemma 5 reads "the set
   `K − H` contains a prime part of `M` whose omission does not disconnect `K`", the prime-part analogue
   of 1925 Theorem 8; Theorem 8 is proved directly (check 1).
7. **Moore 1920 Theorem 4** (*"In a space satisfying Axioms 1' and 4 of F.A., a set of points `M`
   satisfying the requirements of Definition 4 is the sum of two simple continuous arcs that have
   only their end points in common"*, p. 342). **Recorded.** Our general proof (`circle_char`) uses
   only a Hausdorff space and a compact connected `J` (no metrizability), with the conclusion in
   cut-point form (`IsCutArc`); metrizability enters only when cut-point arcs are turned into
   embedded `[0, 1]` (`IsCutArc.exists_embedding`). The 1925 instance (`m25_theorem10`) needs, in
   addition, that `J` be compact, which comes from `J` closed with bounded point set (closed map,
   compact elements), and the Hausdorff property of the quotient (`quotient_metrizable_plane`).
   Definition 4 (*"A simple closed curve is a closed, connected, and bounded point-set which is
   disconnected by the omission of any two of its points"*) is printed on p. 342 of our copy (the
   commission cites p. 340). **Theorem 4 as printed is false for a one-point set**, which satisfies
   Definition 4 vacuously (`not_moore1920_theorem4_singleton`); the corrected `IsSCCElt` adds
   `J.Nontrivial`, and without it 1925 Theorem 11 fails too (`not_m25_theorem11_singleton`).

**Further outcomes.**

* **Theorem 9 and P.C.S. Lemma 8.** Lemma 8 (*"If `M` is a bounded continuum then no simple
  continuous arc of prime parts of `M` separates the plane unless the plane is separated by some
  prime part of `M` which belongs to that arc"*) argues: let `D` be a bounded complementary domain of
  the point set `H` of the arc and `B` its outer boundary with respect to the prime parts; `B` is
  closed, connected and has more than one prime part (*"Since S is not separated by any prime part
  of M belonging to the set pq"*); by Lemma 6 it is an arc, so *"contains uncountably many prime
  parts of M such that the omission of any one of them disconnects B. But this is contrary to
  Lemma 3"* (Lemma 3 is the analogue of 1925 Theorem 2). Lemma 8 tacitly passes from "separates" to
  "has a bounded complementary domain". Our Theorem 9 (`m25_theorem9`) follows this argument with
  Theorems 2 and 6, and excludes the unbounded case as follows: the argument shows that *no*
  complementary domain of the arc is bounded, and two unbounded complementary domains coincide
  (`m25_unbounded_unique`), so `G − pq` is connected. One interior element of the arc suffices in
  place of "uncountably many".
* **Mullikin's Theorem 5.** As printed it is false (`not_mullikin_theorem5_printed`: `M₁ = M₂` a
  segment, `K₁` a half-open half, `K₂` the closed other half). With `K₁`, `K₂` closed it is proved
  (`mullikin_theorem5`) by logarithms rather than by Mullikin's polygons (pp. 154–162): at least two
  domains from Borsuk's theorem (`borsuk_exists_log`, proved by smooth approximation and Sard's
  theorem), at most two by Eilenberg's bound (`compl_union_two_components`).
* **Mullikin's Theorem 4 at `M₁ ∩ M₂ = ∅`** (*"a necessary and sufficient condition that their sum,
  `M`, shall disconnect `S` is that `M̄`, the set of points common to `M₁` and `M₂`, be not
  connected"*, p. 154), against her convention (*"A point set `M` is said to be connected if it
  cannot be expressed as the sum of two mutually exclusive point sets neither of which contains a
  limit point of the other"*, p. 144). The summands must be nonempty (else `M = M + ∅` and nothing
  is connected), so the empty set is connected in her sense, and Theorem 4 at `M₁ ∩ M₂ = ∅` says the
  union does not disconnect `S`: **true** (`mullikin_theorem4_disjoint`, Janiszewski with empty
  intersection). Under Mathlib's convention (the empty set is not connected) the same sentence would
  be **false** (`not_mullikin_theorem4_disjoint_mathlib`: two points).
* **Theorem 7 as printed** (*"then `p` is a limit element of the set `H`"*) is **false**
  (`not_m25_theorem7_printed`: `pq = [0, 1] × {0}`, `x = (1/2, 0)`, `H = (0, 1/4] × {0}`); with `x`
  for `p` it is proved (`m25_theorem7`).
* **The printed simple closed curve** (*"A bounded subset `H` of the set `G` is said to be a simple
  closed curve (of elements of `G`) provided it is disconnected by the omission of any two of its
  elements"*, p. 417): Theorems 10 and 11 fail for two disjoint segments
  (`not_m25_theorem10_printed`, `not_m25_theorem11_printed`). **The printed complementary domain**:
  Theorem 2 fails (`not_m25_theorem2_printed`, the slit disc of batch 145's entry 4, now formalized).

### Moore 1925, §I, Theorems 13–22; F.A. p. 163; Moore 1919, p. 169 (batch 147)

Formalized in `HPC/Moore/M25C.lean` (Theorems 21, 22) and `HPC/Moore/M25CDefs.lean` (the skeleton's
definitions, verbatim), `TSCCCut.lean` (two arcs with only their ends in common are cut by any two
points), `M25CInt.lean` (interiors; arcs and closed curves of elements), `M25C13.lean` (Theorems 13,
14), `M25C15.lean` (Theorems 15–18), `M25C19.lean` (Theorem 19), `M25C20.lean` (Theorem 20; Axioms
1–5, 8, 6′, 7′ for the restricted regions) and `M25C6.lean` (Axioms 6, 7) (REPORT-batch147.md).
Lean names are in the group *Moore 1925 §I, Theorems 13–22 (batch 147)* of `Axioms.lean` /
`axioms.txt` (standard axioms only); the audit of the new theorems is
`doc/batches/audits/axioms-batch147.txt`. Quotations are from pp. 422–425 of
`doc/sources/moore1925.pdf`, pp. 131, 163 of `doc/sources/moore1916.pdf` and pp. 169–170 of
`doc/sources/moore1919.pdf`. All names are in namespace `HPC.Moore`.
Outcome: items A–G **proved**; nothing open. Every skeleton statement is verbatim. **The space of
elements is homeomorphic to the plane** (`m25_theorem22`; Moore's limit-preserving form
`m25_theorem22_moore`).

**Outcome of the checks of COMMISSION-batch147.md §3.**

1. **Theorem 13's proof** (p. 422). (a) *"By Theorem 9, `k` does not separate `G`"*: Theorem 9 is
   about arcs; for `k` a single element the fact is batch 146's (`isConnected_compl_singleton_quot`).
   **Supplied.** (b) *"if `x` and `y` are any two elements of `R`, `x̄` and `ȳ` are not separated from
   each other by `B̄`"*: **confirmed**, with `x`, `y` to be read as elements of `R − k` (Janiszewski
   needs `x̄`, `ȳ` off `k̄` as well; `isPreconnected_region_diff`). (c) *"Hence the set of all those
   elements of `R` which do not belong to `k` is connected. It easily follows that it is a domain."*
   **Confirmed**: open because `k` is closed; *nonempty*, which Moore does not argue, because a
   region is infinite and an open set inside an arc would have no cut points
   (`not_subset_arc_of_cut`). (d) The clause *"every element of which (except possibly just one of
   its end elements) belongs to `R`"* grammatically applies to the arc only; the single element need
   not lie in `R` (the skeleton's disjunct `∃ e, k = {e}` has no such condition). **It does not
   matter**: if `e ∉ R` then `R − e = R`, and `e ∩ B̄` is empty or one element in either case.
2. **Theorem 14's proof** (p. 423). (a) *"Let `p` and `q` denote two distinct elements of the region
   `R`"*: **supplied** by `m25_region_infinite` (F.A. Theorem 4 for the space of elements, batch 145).
   (b) The arc is introduced as `pq` (*"a simple continuous arc `pq` of elements of `G` such that
   every element of `pq` belongs to `R`. Let `r` denote some element of `pq` distinct from `p` and
   from `q`"*) and then called `pxq` (*"the sum of the arcs `pxq` and `pyq`"*); `x` is never
   introduced (the element removed is `r`). **Recorded**: a change of notation, no gap. (c) *"It is
   easy to see that the sum of the arcs `pxq` and `pyq` contains as a subset a simple closed curve
   of elements of `G`"*. **Supplied** (`exists_tscc_of_arcs`, general Hausdorff topology): the last
   point of `pyq` on `pxq` before `r` and the first one after `r` bound a sub-arc of `pxq` through
   `r` meeting `pyq` only in its ends; with the sub-arc of `pyq` between them it is a closed curve
   (`Gen.tscc_cut` makes it a simple closed curve of elements).
3. **Theorems 15–18** (p. 423): no proofs, only pointers. *"Theorem 15 may be proved by an argument
   closely analogous to that used to prove Theorem 24 of F. A."*; *"Theorem 16 may be proved by an
   argument closely parallel to that employed in F. A. to prove Theorem 25"*; *"Theorem 17 may be
   proved with the help of Theorems 15 and 16 by a method similar to that used in F. A. to prove
   Theorem 26 with the aid of Theorems 24 and 25"*; *"Theorem 18 may be proved with the help of
   Theorems 16 and 17 by a method analogous to that used in F. A. to prove Theorem 27 with the aid of
   Theorems 25 and 26"*. **What each pointer amounts to**: batch 138's F.A. proofs in their
   topological form (`Gen.th24_sub`, `Gen.th24_ext`, `Gen.th24_disj`, `Gen.th25`, `Gen.th26`,
   `Gen.th27`), read in the space of elements with `reg` the restricted regions; the F.A. axioms
   they use are replaced by Theorem 11 (open, connected interiors and exteriors with boundary `J`;
   Axiom 8), F.A. Theorem 15 for the space of elements (arcs in domains), bounded point sets
   (compact closures) and Theorem 10 (arcs of a closed curve). The pointers are therefore right.
   Moore's remark *"In the proof there given reference is made to Theorem 21 of F. A. For the case
   where `K` and `R` are interiors of simple closed curves of elements of `G` this Theorem 21 may be
   easily proved with the help of Theorem 11 above"* is **right as it stands**:
   `th21Prop_restricted` uses Theorem 11 only (the exterior of `K` is connected, misses the
   boundary of `R`, and is unbounded, so it misses `R`), not Theorem 12.
4. **Theorem 18's statement** (pp. 423–424): *"(1) either `y` is without `J₁`, the simple closed
   curve formed by `pxq` and `pzq`, or `x` is in the exterior of `J₂`, the simple closed curve formed
   by `pyq` and `pzq`, (2) if `y` is without `J₁` then `x` is in the interior of `J₂` and the interior
   of `J₂` is the sum of the interior of `J`, the interior of `J₁` and the set of elements
   `pxq − (p + q)`"*. `x` and `y` name the arcs and are used as elements without introduction.
   **Recorded; the condition does not depend on the choice**: `pyq − p − q` is connected and misses
   `J₁`, so it lies wholly in the interior or wholly in the exterior of `J₁`
   (`diff_subset_int_or_ext`), and likewise `pxq − p − q` with `J₂`. The skeleton's reading (all
   elements of the arcs other than `p`, `q`) is therefore equivalent to "some element". F.A.
   Theorem 27 is phrased with named points `C`, `D` of the two arcs (`A` and `B` separating `C` and
   `D` on `J`), and its conclusions are about `C` and `D`; `m25_theorem18` applies `Gen.th27` to one
   pair `C`, `D` and spreads the conclusion by `diff_subset_int_or_ext`.
5. **Theorem 20's proof** (p. 424): *"Since `R` is also a region in the original sense"*. **Supplied**
   (`mooreRegion_of_restricted`): the interior of a closed curve of elements is open, connected,
   with bounded point set and boundary `J` connected (Theorem 11).
6. **Theorem 21's proof** (pp. 424–425). (a) *"With the help of Theorems 19 and 20 it is easy to see
   that these axioms continue to hold true if region is interpreted in the restricted sense"*
   (Axioms 1, 2, 4, 5): **confirmed**: Theorem 19 makes the restricted regions a basis of the
   quotient topology (`isTopologicalBasis_restricted`), hence `spaceRestricted_topology`; Axiom 1
   then needs a nested sequence of restricted regions about each element (from Theorem 19 and
   metrizability), Axioms 2, 4 are Theorem 11 and bounded closures, Axiom 5 is batch 145's via
   Theorem 20 (`m25r_axiom1` … `m25r_axiom5`). (b) *"That Axiom 3 holds true for this
   interpretation can easily be seen with the help of Theorem 11"*: **confirmed** (the complement
   of the closure of the interior is the exterior, connected). (c) *"The truth of Axioms 6′ and 7′ of
   the system Σ₂ (see page 163 of F. A.) is a consequence of Theorems 11 and 13"*: **confirmed**
   (`m25_axioms6'7'`): Axiom 6′ is Theorem 13 for an arc with one end possibly on the boundary;
   Axiom 7′ is Theorem 11 (the boundary of the exterior is `J`). In Axiom 6′ (*"`(R + A) − AB` is
   connected"*) the `+ A` is idle, since `A ∈ AB`. (d) *"Thus all the axioms of the system Σ₂ hold
   true for `G`. With the aid of results established in my paper* Concerning a set of postulates
   for plane analysis situs *and the fact that every region in the restricted sense is the interior
   of a simple closed curve it easily follows that Axiom 6 and 7 also hold true"*. **Proved
   directly instead** (`m25r_axiom6`, `m25r_axiom7`, `M25C6.lean`): cross-cuts of `J` near `P`
   through the interior, respectively the exterior (Theorem 10 and the sub-arcs of `J` about `P`,
   Janiszewski, Theorems 12, 15, 18, 19). **What Moore 1919 contains for Σ₂**: the introduction
   (p. 169) asserts *"every space `S` that satisfies Σ₁ or Σ₂ is a number plane"* and *"Σ₁ and Σ₂ are
   both categorical with respect to point and limit point"*; the proof begins (p. 170) *"In my proof
   that Σ₁ is categorical I will make use of the following theorems"*, and Theorems A–G and the
   final construction use Axioms 1–8 only. **Nothing is proved there for Σ₂ beyond the assertion.**
   Moore's step to 6 and 7 thus reads: Σ₂ holds; by 1919 (for Σ₂) `S(G)` is a number plane; in a
   plane whose regions are Jordan interiors, 6 and 7 hold. The middle step rests on F.A. p. 163's
   unproved equivalence of Σ₁ and Σ₂ (check 8). The direct proof avoids it.
7. **Theorem 22** (p. 425): *"The truth of Theorem 22 follows from Theorems 20 and 21 and the results
   of my paper* Concerning a set of postulates for plane analysis situs*"*. **Confirmed; Moore 1919
   is needed for Σ₁ only**: `m25_theorem22` applies `m19_plane` (batch 144, Axioms 1–8) to
   `spaceRestricted r` (Theorem 21, with 6 and 7 proved directly) and transports along
   `spaceRestricted_topology` (Theorem 20 / 19). `m25_theorem22_moore` is Moore's form: the
   correspondence preserves limit points in Moore's sense of limit elements (`isLimitElt_iff`).
8. **F.A. p. 163** (*"It is easy however to show that though Σ₁ and Σ₂ are not absolutely
   equivalent, they are equivalent with respect to point and limit point of a point-set as defined
   in § 2"*; the same claim on p. 131: *"Σ₂ is equivalent to Σ₁ as far as statements in terms of
   point and limit point are concerned"*). **Recorded as an F.A. entry: stated without proof.** The
   footnote on p. 163 only explains the terms (*"every statement in terms of point and limit point of
   a point-set … that follows from Σ₁ … follows also from Σ₂ … and conversely"*). The 1925 route
   formalized here does not use it.

**Further outcomes.**

* **Theorem 19** (*"With the use of Theorems 11, 12, 13, 17 and 18, Theorem 19 may be proved by an
  argument closely analogous to that employed to prove Theorem 36 in F. A."*, p. 424). Proved by
  that route (batch 139's proof of F.A. Theorem 36, with its correction), not by the polygon route
  of the commission. **Used**: Theorems 11, 12, 13, 18, and also 10 and 14, which Moore does not
  cite; **not used**: Theorem 17.
* **Arcs and closed curves of elements are the topological ones** (`isArcElt_iff_tarc`,
  `isSCCElt_iff_tscc`; with F.A.'s notions for `spaceRestricted r`: `isArc_restricted_iff`,
  `isSCC_restricted_iff`).

### Jones 1955, Theorem 2 and the closing remarks; Jones 1949 Theorem 1 as a statement (batch 148)

Formalized in `HPC/Jones/Jones55T2A.lean` (items A–C), `HPC/Jones/Jones55T2D.lean` (items D, E) and
`HPC/Jones/Jones55T2.lean` (items F, G) (REPORT-batch148.md). Lean names are in the group *Jones 1955
Theorem 2 (batch 148)* of `Axioms.lean` / `axioms.txt` (standard axioms only); the audit of the new
theorems is `doc/batches/audits/axioms-batch148.txt`. Quotations are from pp. 736, 739–740 of
`doc/sources/jones1955.pdf`, p. 113 of `doc/sources/jones1949.pdf` and pp. 13, 15, 61 of
`doc/sources/whyburn1942.pdf` (Whyburn, *Analytic Topology*). All names are in namespace
`HPC.Jones`. Outcome: items A–G **proved**; nothing open. Theorem 2 and the closing remarks are proved
**assuming Jones 1949 Theorem 1** (the hypothesis `h49 : Jones49Thm1`, to be discharged in batches
149–); Theorem 2 (2) and continuity do not use it. The general **Jordan curve theorem** in `ℝ²`
is a corollary of Moore 1925 Theorem 11 (`jordan_curve_theorem`).

**Jones 1949 Theorem 1 as printed** (*"If a compact, plane continuum `M` is both homogeneous and
aposyndetic, then `M` is a simple closed curve"*) is **refuted for a one-point set**
(`not_jones49_theorem1_point`). Jones's footnote 3 (*"For other definitions the reader is referred to
Moore's book or Whyburn's book"*): Whyburn, Ch. I §10, p. 15, *"A compact connected set will be called
a continuum"*, and by §8, p. 13 (*"A set of points `M` is said to be connected provided that however
it be expressed as the sum of two disjoint non-vacuous sets …"*) a point is connected. So one-point
continua are continua in Whyburn's convention, and the printed form is false, not harmless (Moore
1932 is not in the repository). `Jones49Thm1` carries `K.Nontrivial`.

**Outcome of the checks of COMMISSION-batch148.md §3.**

1. **"Since each two elements of `g` are homeomorphic"** (p. 739). **Confirmed misprint** for `G`:
   the sentence is about two elements of `G`, which are homeomorphic by Jones's Theorem 1 argument
   (`jones55_elements`, batch 136; outside the aposyndetic case).
2. **"It is clear that for each `g` of `G`, `M − g` is connected (in fact, by (5), `M − g` is strongly
   or continuum-wise connected)"** (p. 739). **(5)** is claim (5) of the proof of Theorem 1, p. 736:
   *"(5) `p` does not cut any two points of `U_p` from each other"* (`jones55_claim5`). With (c) and
   `M − L_p = U_p` (property (e), `jones55_prop_e`): two points of `M − g` lie in a continuum missing
   `p` (`exists_continuum_of_mem_aposSet`), which misses `L_p` by (c). **"Strongly connected"
   follows**: `jones55_compl_continuumwise` (continuum-wise), hence `jones55_compl_connected`.
3. **"if one element of `G` were to separate `S`, then each of them would separate `S` and there would
   exist uncountably many mutually exclusive domains (at least one for each `g`) in the plane. This
   being impossible"** (p. 739). **Supplied**: (a) Borsuk invariance, unstated
   (`separatesPlane_of_homeomorph`, by logarithms); (b) the choice of domains: since `M − g` is
   connected it lies in one complementary domain of `g`, and `g` separating gives another one, `W_g`,
   missing `M` (`exists_component_disjoint`); (c) **disjointness**, which Jones does not argue: for
   `g ≠ h`, `W_g` is a connected subset of `S − h`, so if `W_g` meets `W_h` then `W_g ⊆ W_h` and
   symmetrically; then `W_g = W_h`, its closure adds only points of `g` and of `h`
   (`closure_component_compl_subset`), hence none, and it is open and closed in `S`, absurd;
   (d) the uncountability of `G` (`uncountable_quotient`: a nondegenerate connected metrizable
   space); (e) "This being impossible": `countable_of_pairwiseDisjoint_open`. Proof:
   `jones55_elt_not_separates`.
4. **"Let `G′` denote the upper semi-continuous collection consisting of `G` together with each
   degenerate subset of `S − M`"** (p. 739). **The upper semicontinuity is unargued; supplied**: the
   quotient map `S → G′` is closed (`isClosedMap_mk_gPrime`; the saturation of a closed `F` is `F`
   together with the saturation of `F ∩ M` under `G`, closed by the upper semicontinuity of `G`), and
   batch 145's `usc_of_isClosedMap` gives Moore's distance form (`mooreDecomp_gPrime`, which also
   needs the elements compact, connected and non-separating: item 3).
5. **"With respect to its elements (as points), `G′` is a plane [13] and `G` is a compact
   subcontinuum of `G′`."** [13] cites *"R. L. Moore, Foundations of point-set theory, … 1932,
   Theorem 19, p. 340 and Theorem 2, p. 369; and Concerning upper semi-continuous collections of
   continua, Trans. Amer. Math. Soc. vol. 27 (1925) pp. 416–428, Theorem 22"*. **The formalization
   uses Moore 1925 Theorem 22** (`jones55_plane := m25_theorem22 (mooreDecomp_gPrime …)`). **"Compact
   subcontinuum" is unargued; supplied** (`jones55_embedding`, `jones55_embedding_data`): the map
   `M/G → G′` induced by the inclusion is continuous and injective, so a homeomorphism of the compact
   space `M/G` onto the image of `M`, a compact connected set of the plane `G′ ≅ ℝ²`.
6. **"Furthermore, `G` is homogeneous and aposyndetic. Hence by [5], `G` is a simple closed curve."**
   ([5] for [3]: already recorded, batch 136.) **"Homogeneous and aposyndetic" is Theorem 1 (a)**
   (`jones55_a`). Jones 1949 needs `G` **in the plane**: it is applied to the plane copy `K` of `M/G`
   from item 5, with homogeneity and aposyndesis carried along the homeomorphism
   (`IsHomogeneous.of_homeomorph`, `IsAposyndeticT.of_homeomorph`, `isAposyndetic_iff_T`) and
   nondegeneracy from `jones55_a` (`jones55_circle`).
7. **Remarks** (p. 739): *"Because each element of `G` in Theorem 2 is homogeneous and does not
   separate the plane, each such element is indecomposable."* **Unnumbered claim, stated without
   proof. What it rests on** (`jones55_elements_indecomposable`): Theorem 2 applied to the element
   itself. A decomposable element `g` is a homogeneous, decomposable, bounded plane continuum, so it
   has two complementary domains (`jones55_two_domains`, which uses Theorem 2 (1) and so `h49`), and
   separates the plane, against Theorem 2 (2). Jones 1951 ([5] of Jones 1955: a homogeneous continuum
   lying in but not separating the plane is indecomposable) is not in the repository and is not
   used.
8. **p. 740:** *"Since every decomposable, homogeneous, bounded continuum in the plane must have
   exactly two complementary domains (this follows from Theorem 2), every homogeneous, bounded
   continuum in the plane having more than two complementary domains is indecomposable and of Type
   3."* **Unnumbered claims; both proved, assuming `h49`**: `jones55_two_domains` (the image of `M` in
   the plane of elements of `G′` is a simple closed curve by Theorem 2 (1); the Jordan curve theorem
   gives two domains of elements; their point sets are open, connected — `isConnected_ptsOf`, the
   elements of `G′` being continua — disjoint, with union `S − M`), and `jones55_three_domains`
   (without the decomposability hypothesis: a decomposable `M` would have every complementary
   component equal to one of the two domains). "Type 3" (p. 735: *"Those which separate the plane but
   are indecomposable"*): separation is automatic with two or more complementary components.
9. **The aposyndetic case.** When `M` is aposyndetic, `L_x = {x}` (`Lset_eq_singleton_of_isAposyndetic`),
   `G` is the collection of points and Theorem 2 (1) is Jones 1949 for `M` itself. **Jones does not
   mention the case; recorded.** The proofs treat it separately where it matters: the elements are
   points in `jones55_elt_not_separates` (a point does not separate the plane) and in
   `isHomogeneous_Lset` (a point is homogeneous); `jones55_elements` (which needs `M` not
   aposyndetic) is used only in the other case.

**Further outcomes.**

* **Jordan curve theorem** (`jordan_curve_theorem`): `m25_theorem11` for the decomposition into
  points (`ptSetoid`, batch 146), with `isSCCElt_iff_tscc` (batch 147) and the two half-circles of
  `Circle` (`tscc_circle`). It rests on `m25_theorem11` (Mullikin's Theorem 5 by logarithms, Moore
  1925 Theorems 9, 10), not on `m19_plane`; no circularity.
* **Jones 1949, reference [8]** (*"G. T. Whyburn, Analytic topology, … Theorem 9.1, p. 61"*), cited for
  *"all except countably many of the local separating points of `M` must be of order 2 in `M`"*. On
  p. 61 of Whyburn, **(9.1)** is the lemma *"If `p` is a separating point of an open set `R` in `L` then
  it is also of every open set `U` such that `p ⊂ U ⊂ R`"*; the statement Jones uses is **(9.2)**,
  *"Local separating point-order theorem. All save a countable number of the local separating points
  of any locally compact separable metric space `L` are points of order 2 of `L`"* (same page; (9.1)
  is the first step of its proof). **Recorded: Jones's "Theorem 9.1" is (9.2)**, or (9.1)–(9.2)
  together.
* **The skeleton's `countable_of_pairwiseDisjoint_open`** does not elaborate as written (`Disjoint on
  U` needs `open Function`); `open Function in` is added before the statement, which is otherwise
  verbatim.

### Jones 1949 I: order, Menger's theorem, Whyburn (9.1)–(9.2) (batch 149)

The formalization is in five files (REPORT-batch149.md): `HPC/Jones/Jones49Order.lean` (item A),
`HPC/Jones/Jones49Circle.lean` (item B), `HPC/Jones/Jones49Menger.lean` (item C),
`HPC/Jones/Jones49Why.lean` (item D) and `HPC/Jones/Jones49A.lean` (the umbrella). All names are in
namespace `HPC.Jones`.
* **Axioms.** Lean names are in the group *Jones 1949: order, Menger, Whyburn 9.2 (batch 149)* of
  `Axioms.lean` / `axioms.txt`, with standard axioms only. The audit of the new theorems is
  `doc/batches/audits/axioms-batch149.txt`.
* **Sources.** Quotations are from p. 113 and the references of `doc/sources/jones1949.pdf`, from
  pp. 97, 260, 266–267 of `doc/sources/menger-kurventheorie.pdf` (Menger, *Kurventheorie*; PDF page
  = book page + 8), and from pp. 16, 48, 60–62 of `doc/sources/whyburn1942.pdf`.
* **Outcome.**
  * Items A–C are **proved**, including **Menger's theorem**: a nondegenerate compact metric
    continuum all of whose points are of order 2 is a circle (`menger_order_two`).
  * Item D: (9.1) is **proved** (`whyburn_9_1`, with the unused hypothesis `hR` dropped).
  * (9.2) and `jones49_some_order_two` are **open**; see `OPEN.md`. The latter is reduced to the
    former (`jones49_some_order_two_of_whyburn_9_2`).
* **Definitions.** `OrderLE`/`HasOrder` agree with Menger's *Ordnung* (Ch. III — not Ch. IV —
  p. 97: "wenn p in beliebig kleinen Umgebungen enthalten ist, deren Begrenzungen mit M höchstens n
  Punkte gemein haben") and with Whyburn's order (Ch. III §2, p. 48, relative to the collection of
  points) for a set that is the whole space.
  * Menger's neighbourhoods are ambient, with boundaries intersected with `M`. For `M` the whole
    space this is no difference.

**Outcome of the checks of COMMISSION-batch149.md §2.**

1. **Jones 1949, p. 113:**
   > If a point of M is of order 2 in M, then M is a simple closed curve [4].

   [4] is "Karl Menger, Kurventheorie, Teubner, 1932, p. 267". Menger's theorem needs *all* points
   of order 2. **Homogeneity (a hypothesis of Theorem 1) and the topological invariance of order are
   tacit. Harmless** (`jones49_order_two`, from `menger_order_two` and `hasOrder_homeomorph`).
2. **Menger, p. 267:**
   > Theorem über die Kurven zweiter Ordnung. Eine Kurve zweiter Ordnung ist ein Bogen oder ein
   > topologischer Kreis …

   It is derived in one sentence ("so ergibt sich aus dem Kennzeichnungstheorem folgendes") from
   three things:
   * the *Kennzeichnung der gewöhnlichen Kurven* (p. 266);
   * the remark that the only ordinary curves without branch points are arcs and circles (pp. 64 f.);
   * their characterization by end points.

   **What it rests on (pp. 262–266).** The Kennzeichnung rests on:
   * p. 64 (finitely many points of order other than 2 on an ordinary curve);
   * p. 127 (an irregular curve has infinitely many irregular points);
   * the `n`-Beinsatz (p. 214);
   * the Lemma of p. 260 (free sub-arcs).

   pp. 262–265 (*beständig reguläre Kurven*) are not used beyond that Lemma.

   **Unargued:**
   * the sharpening of the Lemma of p. 260 to `n`-Beine, asserted with "folgende Verschärfung
     desselben bewiesen werden kann";
   * "Je zwei Bogen … haben offenbar höchstens Endpunkte gemein";
   * the finiteness of the components of `B_i′`, which gets one sentence.

   **The formalization avoids this route.** It uses Menger's *second* argument on p. 267, the Lemma
   proved there:
   > Ist K ein im Kleinen zusammenhängendes Kontinuum, K′ eine reguläre Kurve ohne Punkte
   > wachsender Ordnung, welche eine echte Teilmenge von K ist, dann existiert mindestens ein Punkt
   > von K′, der eine größere Ordnung in K als in K′ besitzt.

   It is applied twice, to `V̄` and to `X − V` (`arc_eq_of_legs`, `not_orderLE_two_of_triod`). The
   inputs are local connectedness of all subcontinua (`locallyConnectedSpace_of_orderLE`,
   `orderLE_subtype`) and arcs in them (`exists_tarc_of_orderLE`). The step "regular, hence locally
   connected", which Menger cites from earlier chapters, is supplied by boundary bumping.
3. **Whyburn (9.1), proof (p. 61):**
   > since Q·R_a + p and Q·R_b + p are generalized continua, it follows by [I, (10.2)] that the
   > components V₁ and V₂ of U·(Q·R_a + p) and U·(Q·R_b + p), respectively, containing p are
   > nondegenerate.

   [I, (10.2)] (p. 16) reads:
   > If N is a generalized continuum and G is an open set such that N·G is nonvacuous and different
   > from N and N·G is compact, F(G) contains at least one limit point of each component of N·G.

   **A boundary-bumping step whose hypothesis "N·G compact" is not arranged.** `U·(Q·R_a + p)` need
   not be compact.
   * The case `N·G = N` is also not treated; it is trivial.
   * That `Q·R_a + p` is a generalized continuum is asserted. It is connected by the classical lemma
     on one side of a cut point, and locally compact as a closed subset of `R`.
   * **Supplied:** `isPreconnected_side`, and `exists_continuum_bump_compact`, which bumps inside a
     compact neighbourhood `K ⊆ U` of `p`.
   * The openness of `R` is not needed, so `hR` is dropped from `whyburn_9_1`.
4. **Whyburn (9.2), proof (pp. 61–62):**
   > For let R₁, R₂, … be a fundamental sequence of neighborhoods in L, let G be the set of all local
   > separating points of L and, for each i, let G_i be the set of all separating points of R_i. …
   > by (8.41) all save a countable number of points of G_i are points of order 2 of R_i and hence
   > also of order 2 in L …

   **Steps:**
   * `G = Σ G_i`, by (9.1) with `p ∈ R_i ⊆ T`;
   * (8.41) for each `R_i`;
   * order in an open subset passes to `L`. **Unargued but routine:** small neighbourhoods with
     closure in `R_i` have the same frontier in `R_i` and in `L`.

   **The weight is in (8.41) and (8.4)**, and through them in (8.2), (8.3) and the cut point-order
   theorem (3.2). Open (`OPEN.md`).
5. **Whyburn (8.41) (p. 61):**
   > Then each separating point of L lies in some L_i and is a separating point of L̄_i.

   **True under the skeleton's reading, unargued.** Separating `L̄_i` requires points of both sides
   in the component of `p` *in `L̄_i`*. This follows by the boundary-bumping argument of (9.1),
   run in the compact neighbourhood `L̄_i` of `p ∈ L_i`; the argument is that of
   `whyburn_9_1_side`, not formalized separately for (8.41).

**Further outcomes.**

* **Local separating points have order at least 2** under the skeleton's reading (not formalized).
  The exceptions in (9.2) are therefore points of order `> 2`.
* **`jones49_some_order_two` already asserts that `M` is a simple closed curve.** By homogeneity one
  point of order 2 gives all (`hasOrder_homeomorph`), and then `jones49_order_two` applies. Jones's
  appeal to (9.2) is thus the whole content of the end of Case 2.
* **Whyburn 1939 §14, footnote 6** (for batch 150): "there exists a point p′ of H·V(p) which is of
  order 2 in M" cites Whyburn, Trans. AMS 33 (1931). This is the cut point-order theorem again, the
  same ingredient as (9.2).

### Jones 1949 II: Whyburn's order theorems (3.2), (8.4), (8.41), (9.2); Moore 1922 (batch 150)

The formalization is in five files (REPORT-batch150.md): `HPC/Jones/Jones49Chain.lean` and
`HPC/Jones/Jones49Sep.lean` (the separating point-order theorem for open sets), `HPC/Jones/Jones49B.lean`
(the skeleton items of Whyburn, Ch. III), `HPC/Jones/Moore22.lean` (Moore 1922, the definitions and
Theorems 1–3) and `HPC/Jones/Moore22T4.lean` (the parts of Theorem 4 that are proved). All names are
in namespace `HPC.Jones`.
* **Axioms.** Lean names are in the group *Whyburn Ch. III; Moore 1922 (batch 150)* of `Axioms.lean`
  / `axioms.txt`, with standard axioms only. The audit of the new theorems is
  `doc/batches/audits/axioms-batch150.txt`.
* **Sources.** Moore is quoted from the scan `doc/sources/moore1922.pdf` (pp. 232–237, read at 170
  and 400 dpi), not from the transcription. Whyburn is quoted from pp. 45–50 and 59–61 of
  `doc/sources/whyburn1942.pdf` (PDF page = book page + 14).
* **Outcome.**
  * Whyburn (3.2) (for compact metric continua), (8.4), (8.41), (9.2) and `jones49_some_order_two`
    are **proved**, statements verbatim. (9.2) and `jones49_some_order_two` were open in batch 149.
  * Moore 1922 Theorems 1–3 are **proved**, statements verbatim.
  * Moore 1922 Theorem 4 is **open** (`OPEN.md`): the boundary is shown to be a continuum, and the
    step cited from PNAS 4 (1918) is reconstructed and proved (`exists_crossing_continua`); the
    plane-separation steps of pp. 236–237 are not formalized.
* **Route for Whyburn.** Not Whyburn's. All five items are corollaries of one theorem: *all but
  countably many separating points of an open set `R` of a locally compact separable metric space
  are of order 2* (`countable_sepPoint_not_hasOrder_two`). For two fixed basic open sets `U`, `W`,
  the separating points of `R` whose separation puts `U` and `W` on different sides, within one
  component, form a chain (`SepChain`) ordered as in Whyburn's (1.31). All but countably many points
  are limits from both sides (Whyburn's (2.1)). All but countably many of those have empty
  *residue*, i.e. no point of `Q − p` is unseparated from `p` by points of the chain on both sides.
  This is the step of (2.2) that discards the cuttings `H` with a dense point `p_h` not separated
  from `H`. Each remaining point has small intervals about it and, by a cut-wire argument in a
  compact ball, small open neighbourhoods with frontier `{x, y}`. Neither (8.2), nor the
  non-separated cuttings and potential order of §2, nor (8.3) is used. The definitions of
  *generalized continuum* (Ch. I) and of *potential order* (p. 45) are recorded
  (`IsGeneralizedContinuum`, `PotentialOrderLE`) but not used.

**Outcome of the checks of COMMISSION-batch150.md §2.**

1. **Moore, p. 233, Theorem 1's proof:**
   > Since M is uniformly connected im kleinen there exists a circle K* with center at P such that
   > if X and Y are two points of M lying within K* then X and Y lie together in a connected subset
   > of M that lies wholly within K̄. … For each n there exists a connected point-set tₙ which
   > contains Aₙ and Pₙ, is a subset of M and lies wholly within K*. … Then t is a closed,
   > connected subset of M′ which contains A and P and lies wholly within K.

   **Confirmed slip.** The scan prints "within `K*`" for `tₙ`. By the choice of `K*` the set lies
   within `K̄`, and only then does the limiting set `t` lie within `K` (`K̄` lies within `K`). As
   printed, `t` lies on or within `K*`, and `K*` is not chosen inside `K`. **Harmless:** read `K̄`.
   Also unargued but standard: that the limiting set of the `tₙ` is connected (lim sup of connected
   sets with nonempty lim inf in a compact region). The formalization avoids limiting sets: it
   joins `X` to `P` by an explicit chain of connected sets of summable diameters
   (`moore22_theorem1`).
2. **Moore, p. 234, Theorem 2's proof:**
   > therefore there exists a set M_s of the collection β that contains infinitely many distinct
   > points of the sequence α. The point-set M_t + P is a connected subset of M, of diameter less
   > than ε, which contains P and points of α.

   **Not settled by the scan.** At 400 dpi the two subscripts are printed differently: the first
   glyph is closer to `s` (or a damaged `2`), the second to `t` (or `1`). Whatever the letters, both
   denote the one set of `β` just chosen, and the mismatch, if real, is notational only. The
   **mathematical step is unargued but correct**: `M_t + P` is connected because `P` is a limit
   point of `M_t` (it is the sequential limit of points of `α` in `M_t`), and its diameter is that
   of `M_t`, since `P ∈ closure M_t`. The formalization uses the finitely many pieces whose closure
   contains `P` (`moore22_theorem2`).
3. **Moore, pp. 234–235, Theorem 3's proof:**
   > Let M_K denote the set of all points [X] such that X and P lie together in a connected subset
   > of M of diameter less than ε. … But these connected point-sets are all of diameter less than ε.
   > Theorem 3 is therefore established.

   **Confirmed slip.** `M_K` is a union of connected sets of diameter `< ε` through the centre `P`,
   so its diameter is only `≤ 2ε`. **Harmless:** run the proof with a smaller number. The
   formalization uses `ε/3` (`moore22_theorem3`).
4. **Moore, p. 236, Theorem 4's proof (sufficiency):**
   > For each positive integer m the point-set tₘ contains at least one point Aₘ on K*.

   **Confirmed:** the scan prints `tₘ` without the bar here, while `t̄₁, t̄₂, …` and "(2) `t̄ₘ`
   contains" carry it. Read `t̄ₘ`. **Harmless.**

   > For each positive integer m(1 ≤ m ≤ n) let Tₘ denote the square …

   (necessity; the sentence runs from p. 236 to p. 237). **Confirmed misprint** for `1 ≤ m ≤ 4ⁿ`:
   the squares are `K₁, K₂, …, K_{4ⁿ}`. **Harmless.**
5. **Moore, p. 237, Theorem 4's proof (necessity):**
   > Let ε = (b − c)/4.

   **Confirmed.** `b` and `c` are the sides of `K_m̄` and `T_m̄`, and `c = 3b`, so `(b − c)/4 < 0`.
   Read `(c − b)/4` (`= b/2`, the distance between `K_m̄` and `H_m̄`). **Harmless.**

   **Unargued steps (confirmed in the scan):**
   * > Since R is a connected domain every R_{m̄Pᵢ} has at least one limit point on the square T_m̄.

     True: otherwise `R_{m̄Pᵢ}` is open and closed in `R`, hence equal to `R`, which would then be
     of diameter `< ε`, against the failure of property S. The argument is not given.
   * > For each n the boundary of Rₙ contains a closed connected subset R̄ₙ such that (1) R̄ₙ
     > contains at least one point on K_m̄ and at least one point on H_m̄, (2) every point of R̄ₙ
     > lies either on K_m̄ or on H_m̄ or between them.

     A plane-separation step (`Rₙ` reaches from within `K_m̄` to without `H_m̄`; its boundary
     contains a continuum crossing the annulus). Unargued, and not formalized.
   * > It can easily be seen that no two of the sets R̄₂, R̄₄, R̄₆, … have a point in common and that
     > indeed if Z and W are points belonging to different sets of this infinite collection then Z
     > and W do not lie together in any connected subset of M which is contained in the point-set
     > I …

     A sector-separation step (the components `R₂, R₄, …` separate one another in the annulus).
     Unargued, and not formalized; see `OPEN.md`.

   **A further slip, not in the commission's list:**
   > No matter how small positive number δ may be there exist two even integers m and n such that
   > the distance from Yₘ to Yₙ is less than δ. It follows that there exists no connected subset of
   > M of diameter less than ε that contains both Yₘ and Yₙ. Therefore M is not connected im kleinen.

   The points `Yₙ` lie in `Rₙ ⊆ R` (they are the points `Xᵢ` of `R_{m̄Pᵢ}` on `H_m̄`), and `R` is a
   domain with boundary `M`, so **no `Yₙ` belongs to `M`**. The conclusion is vacuous as written.
   Moreover, a connected subset of `M` of diameter `< ε` through a point of `H_m̄` need not lie in
   `I`, so the "indeed" clause would not apply even to points of `M` on `H_m̄`. **Repair:** take
   `Zₙ ∈ R̄ₙ` on the square concentric with `K_m̄` midway between `K_m̄` and `H_m̄` (each `R̄ₙ` is a
   continuum crossing from `K_m̄` to `H_m̄`, so it meets it), and use `ε/2`: a connected set of
   diameter `< ε/2` through `Zₙ` stays in `I`. Two of the `Zₙ` are arbitrarily close, and then
   `M` fails to be connected im kleinen at a limit point of the `Zₙ`. That last step is also
   unargued: Moore's definition is pointwise. **A defective step, repairable within the proof.**
6. **Moore, p. 237** (the commission says p. 236; the sentence is on p. 237):
   > Since R does not have property S and each set R_{mP} is of diameter less than ε there must
   > exist at least one value m̄ of m and infinitely many distinct points P₁, P₂, P₃, … Pₙ …
   > belonging to R and lying on or within K_m̄ such that no two of the connected sets R_{m̄P₁},
   > R_{m̄P₂}, R_{m̄P₃}, … have a point in common.

   **Confirmed unargued step.** `R` is the union of the sets `R_{mP}`. If each `m` gave finitely
   many distinct ones, property S would hold for `ε`, so some `m̄` gives infinitely many distinct
   ones. Their disjointness needs that for fixed `m` two sets `R_{mP}` are equal or disjoint, which
   holds because they are components of `R` intersected with the interior of `Tₘ`. Not stated.
   **Harmless.**
7. **Typographical (all confirmed in the scan):**
   * "then X and P fie together in a connected subset of M" (p. 233) for "lie";
   * "should have a continuous curce as its boundary" (p. 235, Theorem 4) for "curve";
   * "the connected sets in question are a sumed to be closed" (p. 234, footnote 1) for "assumed".
8. **Whyburn (3.2) and (8.4): unargued steps.**
   * **(3.1)–(3.2), pp. 49–50.**
     > Clearly any collection of cut points (or of disjoint connected cuttings) of a connected set M
     > is non-separated. Thus we have (3.1) Theorem. …

     (3.1) is stated without proof as a consequence of (2.2) and (2.22). Unargued: that a set of
     cut points is a non-separated collection of cuttings ("Clearly"); that the subcollection `[Q]`
     of (2.2) misses only countably many of them; and, for the second sentence of (3.1), that
     (2.22) applies (points are compact). The passage from "order 2 relative to `Q`" in (3.1) to
     "order 2" in (3.2) (the Note on p. 50) needs that a frontier in the sum of at most two points
     of `Q` has at most two points. That is immediate. **Harmless; the formalization does not use
     §2.**
   * **(8.4), p. 60.**
     > Then since N is ordered as in (1.31), there exist points x and y of N in the order a, x, p,
     > y, b such that, in the notation of §1, δ[Q₂(x)·Q₁(y)] < ε/4

     **Unargued, and not a consequence of what is cited.** (3.2) gives that each point of `N` is of
     order 2 in `Q` relative to `N`. The ordering (1.31) does not give that the intervals
     `Q₂(x)·Q₁(y)` about `p` become small. That needs `p` to be a limit of `N` from both sides
     *and* the intersection of the intervals to be `p`, i.e. the construction inside the proof of
     (2.2) (the sets `Uᵢ` and (2.21)), not its statement. The formalization proves this step
     (`SepChain.exists_small_interval`) for points that are two-sided limits with empty residue,
     and shows that the other points are countable (`countable_not_good`, `countable_res`).
   * **(8.4), p. 60:**
     > then R is a neighborhood of p in K with δ(R) < ε/2, R·Q = Q₂(x)·Q₁(y) and F(R)·Q = x + y.

     Unargued but routine (`x`, `y` are limit points of `Q₁(x)`, `Q₂(y)`, so the radii exclude
     them).
   * **(8.3), p. 59 (statement) against its use on p. 61.** (8.3) asks that "there exists no
     convergent sequence of components of K whose limit contains points of both C·R and
     C·(K − R̄)". Read literally this is never satisfied, since the constant sequence `C, C, …`
     converges to `C`. (8.4) verifies it for "distinct components". **Harmless:** read "distinct
     components of `K` other than `C`".
   * The formalization replaces (8.3), (8.31), (8.32) and (2.21)–(2.22) by a cut-wire argument in
     a compact ball (`SepChain.exists_open_frontier_pair`).

**Further outcomes.**

* **Theorem 4's boundary is always a continuum.** For a bounded domain that is simply connected
  in Moore's sense, the complement is connected and the boundary is a continuum
  (`isConnected_frontier_of_mooreSimplyConnected`), with or without property S. Moore's "continuous
  curve" thus reduces to local connectedness. Moore's simple connectivity (p. 235, footnote 2:
  "A bounded domain R in the plane is said to be simply connected if R contains the whole of every
  bounded point-set whose boundary is a subset of R") is recorded verbatim as
  `MooreSimplyConnected`.
* **The PNAS step is short.** "The argument beginning with the second line from the bottom of page
  365 and ending in the twenty third line from the top of page 366" of PNAS 4 is reconstructed by
  two boundary-bumping arguments (`exists_crossing_continua`, about 130 lines). The continua lie
  between two concentric squares and meet both. PNAS 4 is not needed for it.

### Jones 1949 III: crossing continua; Moore 1922 Theorem 4; complementary domains (batch 151)

The formalization is in five new files (REPORT-batch151.md): `HPC/Jones/Jones49CStrip.lean`,
`HPC/Jones/Jones49COrder.lean`, `HPC/Jones/Jones49CAnn.lean` (the sector theorem, via lifts of the
square annulus to a strip), `HPC/Jones/Jones49CMoore.lean` (Moore's sufficiency in local form and the
necessity) and `HPC/Jones/Jones49C.lean` (the skeleton items). Names are in namespace `HPC.Jones`,
helpers in `HPC.Jones.Sector`.
* **Axioms.** Lean names are in the group *Crossing continua; Moore 1922 Theorem 4; complementary
  domains (batch 151)* of `Axioms.lean` / `axioms.txt`, with standard axioms only. The audit of the
  163 new theorems is `doc/batches/audits/axioms-batch151.txt`.
* **Sources.** Moore is quoted from the scan `doc/sources/moore1922.pdf` (p. 236 is PDF page 5).
  Whyburn 1939 is quoted from `doc/sources/whyburn1939.pdf` (p. 747 is PDF page 16).
* **Outcome.** The sector theorem and the cyclic order, Moore's sufficiency in local form, Moore 1922
  Theorem 4 (both directions, statement verbatim), the two theorems on complementary domains and
  Whyburn's (6.22) in the §14 form are **proved**. Theorem 4 is therefore verified, and the
  candidate entry of batch 150 on Moore's necessity is counted (check 4); Whyburn's inversion
  (check 5) is counted once Theorem 14 is verified.

**Checks.**

1. **Moore 1922, p. 236:**
   > There exists an infinite sequence B₁, B₂, B₃, … of distinct points of the set A₁, A₂, A₃, …,
   > lying in the order B₁B₂B₃ … BₙBₙ₊₁ … on the curve K*

   **True, but the proof needs more than the order of the points.** The later steps ("must clearly
   contain a point either of kₙ₋₁ or of kₙ₊₁") use that the continuum `kₙ` lies between `kₙ₋₁` and
   `kₙ₊₁`, i.e. the cyclic order of the *continua*. A continuum may meet `K*` in many points, so the
   order of one chosen point `Bₙ` on each does not by itself give the order of the continua; whether
   the point order alone suffices is not settled here. The formalization orders the continua
   directly: it lifts each to a strip and extracts a monotone subsequence for the order of lifts
   (`Sector.sector_cyclic`, `sector_cyclic_order`), and then uses the odd indices `n ≥ 1`.
   **Classification: unargued step, true; harmless.**
2. **p. 236:**
   > a circle with center at Bₙ and radius less than (r − r̄)/4 which neither contains nor encloses
   > any point of kₙ₋₁ or of kₙ₊₁

   This needs `Bₙ ∉ kₙ₋₁ ∪ kₙ₊₁`. It holds: `Bₙ ∈ kₙ`, and distinct continua of the sequence are
   disjoint. The formalization takes a ball of radius `δₙ ≤ (r₂ − r₁)/4` and `δₙ ≤ 1/(n + 1)`.
   **Harmless.**
3. **p. 236:**
   > Then R is not the sum of a finite collection of connected point-sets all of diameter less than ε

   The step from "no connected subset of `R` of diameter `< ε` contains points of two of the `C`s" is
   pigeonhole: of finitely many pieces, one contains points of infinitely many `C`s
   (`Sector.hloc_of_propertyS`). **Harmless.**
4. **Moore's necessity, last step (candidate of batch 150, now counted).** Moore's points `Yₘ`, `Yₙ`
   lie in `R`, not in `M`, so local connectedness of `M` at their limit does not apply to them. The
   repair as proved (`Sector.propertyS_of_locallyConnected`): in the annulus between the squares of
   radii `ε/8` and `3ε/16` about the limit boundary point, with `η = (b − a)/4`, walk along the middle
   square from the point `γₙ` to the first point of a neighbouring continuum (`Sector.sphere_walk`).
   This gives points `zₙ ∈ M` in the piece `Vₙ` of the annulus. A limit `q` of the `zₙ` is a point of
   `M`, and local connectedness of `M` at `q` (`Sector.cikAt_of_locallyConnectedSpace`) gives a small
   connected subset of `M` joining two of the `zₙ` in different pieces, which the sector theorem
   forbids. Simple connectivity is not used. **Classification: defective proof (gap in the last
   step); theorem true.**
5. **Whyburn 1939, p. 747 (candidate of batch 150; counted once Theorem 14 is verified):**
   > Clearly we may suppose R bounded, since an inversion of the plane can be used to throw R into a
   > bounded region complementary to the image of M.

   **False as stated.** Counterexample: `M` a closed disk. Its only complementary domain `R` is
   unbounded. An inversion maps `R` to a bounded region only if its centre lies outside `R`, and the
   image of `M` is compact only if the centre lies outside `M`; but `M ∪ R` is the whole plane. With
   the centre in `R` the image of `R` is unbounded; with the centre in `M` the image of `M` is not
   compact (not a continuum). So the reduction to bounded `R` is not available. The theorem is not
   affected: Moore's argument in local form (`moore22_sufficiency_local`) uses no boundedness, and the
   boundary of every complementary domain is a continuum (`isConnected_frontier_complDomain`).
   **Classification: defective proof (gap); theorem true.**

### Jones 1949 IV: Whyburn 1939 Theorem 14 (batch 152)

The formalization is in three new files (REPORT-batch152.md): `HPC/Jones/Jones49DSep.lean` (the
joining lemma by Janiszewski's theorem, and its use at a non-cut point), `HPC/Jones/Jones49DCross.lean`
(the bad point at every radius of a crossing annulus, and the no-finite-order lemma) and
`HPC/Jones/Jones49D.lean` (the skeleton items). Names are in namespace `HPC.Jones`, helpers in
`HPC.Jones.Sec14`.
* **Axioms.** Lean names are in the group *Whyburn 1939 Theorem 14 (batch 152)* of `Axioms.lean` /
  `axioms.txt`, with standard axioms only. The audit of the new theorems is
  `doc/batches/audits/axioms-batch152.txt`.
* **Source.** Whyburn 1939 is quoted from page images of `doc/sources/whyburn1939.pdf` (pp. 747–748
  are PDF pages 16–17).
* **Outcome.** Theorem 14 (`whyburn39_theorem14`, statement verbatim) is **proved**, with step 3
  (`whyburn39_local_noncut`, statement verbatim) and the two auxiliary items in shapes chosen here
  (`whyburn39_moore_curve`, `whyburn39_curve_from_order_two`). The route uses no arcs, no Jordan
  curve and no inversion (see the report, §§1–4). Since Theorem 14 is verified, the inversion
  (check 8) is now counted as a defective proof.

**Checks.**

1. **p. 747:**
   > Since almost all the points pᵢ lie in V_δ(p), we may suppose that all of them do. Let p₁p₂ be an
   > arc in R from p₁ to p₂.

   Arcs in a connected open plane set exist (in the repository: polygonal arcs,
   `HPC.Plane.exists_polyPath_of_isConnected` with `exists_simplePolyArc_of_polyPath`). The
   formalization does not use arcs at all: step 3 is proved by Janiszewski's theorem
   (`HPC.Jones.Sec14.join_in_domain`). **Harmless.**
2. **pp. 747–748:**
   > There must exist a subarc xy of p₁p₂ such that x + y ⊂ C_δ, xy − (x + y) lies without C_δ and x
   > and y cannot be joined by a continuum of R lying in V_{2ε}(p)

   The finite-cover argument is correct. Two imprecisions: the sum of the finitely many subarcs and
   pieces of `C_δ` is only connected (its closure is the continuum asked for), and the finiteness of
   the subarcs meeting `C_δ` in the required way rests on uniform continuity, which is not stated.
   Not used by the formalization. **Harmless.**
3. **p. 748:**
   > Now the continuum N can intersect only one of the arcs xuy, xvy of C_δ, since neither N nor xy
   > contains a point of V_δ(p) and N·xy = 0.

   A θ-curve separation step, unargued. It is true: `C_δ + xy` is a θ-curve with complementary
   domains `V_δ(p)`, `D₁` (bounded by `xy + xuy`) and `D₂` (bounded by `xy + xvy`). `N` misses
   `V_δ(p)` and `xy`, so `N ⊂ (D₁ + xuy − (x + y)) ∪ (D₂ + xvy − (x + y))`; the two pieces are
   disjoint and each is relatively open in `N` (a point of the open arc `xuy` has a neighbourhood in
   `V_δ(p) + D₁ + xuy`), so the connected `N` lies in one of them. Not used by the formalization. **Classification: unargued step, true; harmless.**
4. **p. 748:**
   > Let 0 be a point of I·V_ε(p) which can be joined to u by an arc ou such that ou − o lies in
   > I·V_ε(p).

   **Misprint:** `ou − o` contains `u ∈ J`, which is not in `I`; the intended condition is
   `ou − u ⊂ I·V_ε(p)`. Such an `0` exists because `u` is an interior point of an arc of `J` lying in
   the open set `V_ε(p)`, and `u` is on the frontier of `I`: a short segment from `u` into `I` does it.
   **Harmless (misprint).**
5. **p. 748:**
   > since ou − o ⊂ E, the arc x₁xuyy₁ of J is contained in C

   Unargued, but true: the component of `C − C_ε` containing `u` is an arc of `J − C_ε` (the points
   of `C` off `C_ε` lie on `J`), and it runs from `x₁` to `y₁`. Not used by the formalization, which
   replaces `C` by the component `W` of `V_ε(p) − N` containing `p` (`whyburn39_moore_curve`).
   **Classification: unargued step, true; harmless.**
6. **p. 748:**
   > The sequence of arcs pᵢqᵢ contains a subsequence … converging to a non-degenerate continuum
   > H ⊂ M

   and

   > every point of H within V_ε(p) is, like p, the limit of a sequence of points of R no pair of
   > which can be joined in R by a connected set of diameter < 3ε

   `H ⊂ M`: a point of `H` in `R` would have a disc in `R` meeting two of the arcs near their ends,
   joining two `pᵢ` by a connected subset of `R` of diameter `< 4ε`. `H` is nondegenerate: it contains
   `p` and a point of `C_ε`. The second sentence is unargued, and the constant is a slip: the argument
   as given yields only diameter `< 2ε`; any positive constant suffices for the proof. "Every point
   of `H`" should read "every point of `H` within `V_ε(p)`", as printed later. In step 3 the
   `R·V_{3ε}(p)` is likewise a slip for `V_{2ε}(p)`. The formalization replaces `H` by Moore's crossing
   continua and obtains one bad point at every radius of an interval
   (`HPC.Jones.Sec14.exists_bad_point_of_crossing`, with `ε = (r₂ − r₁)/6`).
   **Classification: unargued step with a slip in the constant, true; harmless.**
7. **p. 748:**
   > But there exists points p′ᵢ, p′ⱼ, p′ₖ from distinct arcs … which lie in D

   **Misprint:** "there exists" for "there exist". Given the curve `K` and the domain `D`, the step is
   correct: infinitely many of the arcs enter `D` and leave it, so each meets `K − (c + d)`, which has
   two components. The formalization does not build `K`: such a point has no finite order in `M`
   (`whyburn39_curve_from_order_two`). **Harmless (misprint).**
8. **The inversion (p. 747), candidate of batches 150–151, now counted:**
   > Clearly we may suppose R bounded, since an inversion of the plane can be used to throw R into a
   > bounded region complementary to the image of M.

   False as stated (counterexample in the batch-151 subsection, check 5). Theorem 14 is now verified
   without it (`whyburn39_theorem14`), so the entry is counted. **Classification: defective proof
   (gap); theorem true.** It is the fourteenth defective proof of the ledger.

### Jones 1949 V: Whyburn 1939 Corollary 1 (batch 153)

The formalization is in five new files (REPORT-batch153.md): `HPC/Jones/Jones49EArc.lean` (polygonal
arcs are arcs; the arc theorem for connected open subsets of Peano continua),
`HPC/Jones/Jones49ETheta.lean` (simple closed curves and θ-curves in cyclic Peano continua),
`HPC/Jones/Jones49EAcc.lean` (accessibility), `HPC/Jones/Jones49EPlane.lean` (the boundary is cyclic;
the θ-curve lemma) and `HPC/Jones/Jones49E.lean` (the skeleton items). Names are in namespace
`HPC.Jones`.
* **Axioms.** Lean names are in the group *Whyburn 1939 Corollary 1 (batch 153)* of `Axioms.lean` /
  `axioms.txt`, with standard axioms only. The audit of the new theorems is
  `doc/batches/audits/axioms-batch153.txt`.
* **Sources.** Whyburn 1939, p. 749 and footnote 16 (`doc/sources/whyburn1939.pdf`); Wilder 1938,
  Theorem 8a and its corollaries (`doc/sources/wilder1938.pdf`).
* **Outcome.** Corollary 1 (`whyburn39_corollary1`, statement verbatim) is **proved**, together with
  items A–D (statements verbatim) and item E (shape chosen here: `theta_of_cyclic_peano`).

**Checks.**

1. **Corollary 1 is stated without proof (p. 749):**
   > COROLLARY 1. If M is a compact plane semi-locally-connected cyclic continuum, the boundary of
   > every complementary domain of M is a simple closed curve.

   What the formal proof uses: (a) Theorem 14 (`whyburn39_theorem14`, batch 152), which is where
   semi-local-connectedness enters, through (6.22) and `local_join_of_noncut`; (b) Brouwer's boundary
   theorem (`isConnected_frontier_complDomain`); (c) every cut point of the boundary `B` is a cut point
   of `M` (`frontier_cyclic`). This needs only compactness of `M`, its cyclicity and Janiszewski's
   theorem, not semi-local-connectedness. (d) The arc theorem for Peano continua, giving a θ-curve in
   `B` if `B` is not a simple closed curve; (e) the θ-curve lemma (Jordan curve theorem three times
   and Janiszewski's theorem): a θ-curve cannot lie in the closure of a connected set that misses it.
   Accessibility (item C) is proved but not used. The corollary does follow from Theorem 14 by
   classical plane topology, as the word "Corollary" suggests, but the deduction takes items (b)–(e)
   and is not written anywhere in the paper. **Classification: stated without proof; true.**
   Footnote 16:
   > Since, as was pointed out to me by R. L. Wilder after this paper was submitted for publication,
   > it follows by the argument given under (6. 2) that in the case of a cyclic continuum,
   > "semi-local-connectedness" is equivalent to Wilder's property "local 0-avoidability" it results
   > that this corollary is equivalent to the first corollary following Theorem 8a on p. 196 of his
   > paper

   The equivalence is **not used**: the proof goes through Theorem 14 and needs no homology. It is not
   proved in Whyburn 1939 either. The footnote refers to "the argument given under (6. 2)", and (6.2),
   (6.21), (6.22) relate semi-local-connectedness to non-cut points, but no proof of the equivalence
   with local 0-avoidability (a homological condition, Wilder's Definition II) is printed. Not checked
   here, since nothing depends on it. **Classification: unargued remark, not used, not decided.**
2. **Wilder 1938, Theorem 8a and its first corollary:**
   > Corollary. In the plane, if M is a continuum all of whose points are locally 0-avoidable, then
   > the boundaries of the complementary domains of M are simple closed curves.

   Same conclusion as Corollary 1. The hypothesis differs: local 0-avoidability at every point, in
   place of "semi-locally-connected and cyclic". Whether local 0-avoidability alone implies cyclicity
   is not examined here. Footnote 16 asserts the equivalence only for cyclic continua, so the two
   statements agree provided that equivalence holds and Wilder's hypothesis gives cyclicity. That equivalence is neither used
   nor decided here (check 1). Wilder's proof is homological and is not formalized, as instructed.
   Compactness is part of Wilder's Theorem 8a ("Let M be a compact continuum") and of Whyburn's
   statement. **Agreement of conclusions recorded; the hypotheses are equivalent only under the
   footnote's claim.**
3. **Degenerate cases.** If `M` is a single point `z`, the hypothesis "cyclic" fails, since
   `{z}ᶜ = ∅` is not connected (`IsConnected` requires nonemptiness). The empty set is excluded by
   `IsConnected M`. The formal statement carries no hypothesis beyond the printed ones, so no
   nondegeneracy hypothesis is needed. Cyclicity is what keeps `B` nondegenerate: if `B ⊆ {z}` then
   `{z}ᶜ ⊆ R`, so `M ⊆ {z}` (`frontier_diff_nonempty`). For `M` a simple closed curve or a closed disc,
   the conclusion holds; this is an instance of the theorem, and no separate formal check was made.
   **Harmless: no hidden hypothesis.**

### Jones 1949 VI: Theorems 1 and 2; Jones 1955 Theorem 2 unconditional (batch 154)

The formalization is in five new files (REPORT-batch154.md): `HPC/Jones/Jones49FTheta.lean`
(θ-curve lemmas and the separation of `M − (A + B)`), `HPC/Jones/Jones49FLocal.lean` (local
separating points), `HPC/Jones/Jones49FCase1.lean`, `HPC/Jones/Jones49FCase2.lean` and
`HPC/Jones/Jones49F.lean` (the skeleton items). Names are in namespace `HPC.Jones`.
* **Axioms.** Lean names are in the group *Jones 1949 Theorems 1–2; Jones 1955 Theorem 2
  unconditional (batch 154)* of `Axioms.lean` / `axioms.txt`, with standard axioms only. The audit of
  the new theorems is `doc/batches/audits/axioms-batch154.txt`.
* **Source.** Jones 1949, pp. 113–114 (`doc/sources/jones1949.pdf`).
* **Outcome.** Theorem 1 (`jones49_theorem1 : Jones49Thm1`, nondegenerate form) and Theorem 2
  (`jones49_theorem2`, nondegenerate form) are **proved**; every skeleton statement is verbatim. The
  hypothesis `h49` of batch 148 is discharged (`jones55_theorem2'`, `jones55_two_domains'`,
  `jones55_elements_indecomposable'`, `jones55_three_domains'`).

**Checks.**

1. **Case 1, p. 113:**
   > If M − J is connected, then each point of M belongs to some such simple closed curve lying in M.
   > Consequently each point of M belongs to the boundary of an element of G.

   The first sentence is homogeneity: a homeomorphism `h` of `M` carrying a point of `J` to `p`
   gives `J' = h(J) ∋ p` with `M − J' = h(M − J)` connected. The second is unargued. It is supplied
   by the Jordan curve theorem (`frontier_cc_of_jordan`): `M − J'` lies on one side of `J'`; the other
   side misses `M`, is connected, and has frontier `J' ⊆ M`, so it is a component of `Mᶜ` with
   boundary `J'`. **Classification: unargued step; true; supplied (`exists_frontier_through`).**
2. **Case 1, p. 113:**
   > Since no point of M is of order 2 in M, each point of Jᵢ is a limit point of M − Jᵢ.

   Unargued. The sentence is true: a point of `Jᵢ` that is not a limit point of `M − Jᵢ` has a
   neighbourhood in `M` lying on the simple closed curve `Jᵢ`, and a point on an open arc of `M` has
   order 2. The formal proof does not prove this sentence as stated. It shows that such a point is a
   local separating point of `M` (it separates `W − q`, `isLocalSepPoint_of_open_sub_tscc`); then
   homogeneity and Whyburn (9.2) give some point of order 2 (`jones49_some_order_two`), against the case
   hypothesis. Baire is Mathlib's `nonempty_interior_of_iUnion_of_closed`, and `G` is countable
   (`countable_complDomains`). **Classification: unargued step; true; replaced by a different
   argument with the same conclusion.**
3. **Case 2, p. 114:**
   > There exists an arc T lying in the complement of D̄ which is irreducible from H to K. Except for
   > its end points, T lies in an element U of G.

   Supplied (`exists_domain_meeting`). The complement of `D̄` is the other side of `J`, a connected
   open set containing `M − J`. An arc in it from `H` to `K` (`exists_tarc_of_isOpen_plane`), trimmed
   at its last point on `H̄` and then at the next point on `K̄` (`TArc.first_point`), is irreducible
   from `H` to `K`. Its interior misses `M`, because `M` meets the complement of `D̄` only in
   `H + K`, so it lies in one component `U` of `Mᶜ`. **Classification: unargued; true.**

   > The component AxB of C − C·J which contains x is an arc-segment whose end points lie on J.

   This needs `C ∩ J ≠ ∅`: `C` is a simple closed curve in `M` (Whyburn 1939 Corollary 1) through
   `x ∈ H` and `y ∈ K`, and each of its two arcs from `x` to `y` meets `J`, since `H` and `K` are
   separated in `M − J`. The first points `A`, `B` of `J` on these two arcs give `C = AxB + L'` with
   `AxB · J = {A, B}` and `A ≠ B` (`exists_theta_arcs`). The ends are distinct because `y ∉ AxB`; this
   is where the two-sidedness of the case enters. **Classification: unargued; true.**

   > It follows that M − (A + B) is *not* connected

   **True; no argument is printed, and one is needed.** The proof is `theta_separation`. Let `J₁`,
   `J₂` be the arcs of `J` from `A` to `B`. Let `E₁` be the side of `J₁ + AxB` not containing `J₂°`,
   and `E₂` the side of `J₂ + AxB` not containing `J₁°`. Then:
   * Every point of `M` off the θ-curve `J + AxB` lies in `E₁ + E₂`, and `U` lies in `E₁` or `E₂`.
     Both facts come from `theta_no_common_side`: for a θ-curve `K₁ + K₂ + K₃`, no point is, for each
     `i`, on the side of `Kⱼ + Kₖ` containing `Kᵢ°`. That lemma is proved from the Jordan curve
     theorem and Janiszewski's theorem.
   * Say `U ⊆ E₁`. The difficulty noted in §2 C of the commission is that `AxB°` lies in the closure
     of both `E₁` and `E₂`. It is met as follows. `L' = C − AxB°` lies in `Ē₁` and meets `J₂` only in
     `A`, `B`, so `L' + AxB + J₂` is a θ-curve. A point of `M · E₁` not on `L'` is outside `U` and
     outside `E₂`, so by `theta_no_common_side` it is not on the side of `L' + J₂` containing `AxB°`.
     Hence `M · E₁` does not accumulate at `AxB°`.
   * `M − (A + B) = M·(E₁ + J₁°) + M·(E₂ + J₂° + AxB°)` is then a separation.

   Which hypotheses are used: `M ∩ D = ∅`, `J + AxB ⊆ M`, and `U` a complementary domain other than
   `D` whose boundary is the simple closed curve `AxB + L'`. That boundary is a simple closed curve by
   Whyburn's Corollary 1, which is where semi-local connectedness and cyclicity enter. Homogeneity and
   the absence of points of order 2 are not used. **Classification: unargued step; true; supplied.**

   > but M − B *is* connected. Hence A is a local separating point of M.

   `M − B` is connected because `M` is cyclic (`jones49_setting`). `A` then separates the open set
   `M − B`, whose component containing `A` is all of `M − B`, in Whyburn's sense
   (`isLocalSepPoint_of_separation`). **True.**

   *Degenerate subcase.* "`M − J` is not connected" includes `M = J`, where `M − J` is empty. There
   Jones's argument does not apply, but every point is a local separating point
   (`isLocalSepPoint_of_open_sub_tscc` with `W = M`). In Jones's proof this subcase is already covered
   by the first sentence (points of a simple closed curve have order 2). **Harmless.**
4. **Case 2, p. 114:**
   > Since M is homogeneous, every point of M is a local separating point of M. But all except
   > countably many of the local separating points of M must be of order 2 [8].

   This is `jones49_some_order_two` (batches 149–150, through Whyburn (9.2)). It needs `M`
   uncountable, which is not stated. A nondegenerate continuum is uncountable
   (`uncountable_of_connected_metrizable`), so nondegeneracy suffices. **Classification: tacit
   hypothesis, supplied by nondegeneracy; true.**
5. **Theorem 2's proof, p. 114:**
   > If M contains no weak cut point, it is aposyndetic at some point [9]. Being aposyndetic at one
   > point, M must be aposyndetic at each of its points. Hence Theorem 2 follows from Theorem 1.

   [9] is Jones 1948 Theorem 18 (`theorem18`). It gives a dense `G_δ` of points at which `M` is
   aposyndetic, which is nonempty since `M` is. The second sentence is homogeneity, which is tacit:
   aposyndesis at `x` with respect to `y` is invariant under homeomorphisms (`aposAt_homeomorph_iff`).
   **Classification: tacit use of homogeneity; true.**
6. **Degenerate cases.** A one-point continuum is homogeneous and aposyndetic, and has no weak cut
   point, since `CutsPts` needs two distinct points other than the cut point. It is not a simple
   closed curve. So Theorem 1 (`not_jones49_theorem1_point`, batch 148) and Theorem 2
   (`not_jones49_theorem2_point`) are false as printed for it, and both are stated and proved with
   `K.Nontrivial`. **Classification: missing nondegeneracy hypothesis, as for Theorem 1.**

No step of Jones's proof is false; the gaps are unargued steps, all true. No defective proof is added,
and the count stays at fourteen.

### Hagopian 1975 I: Lemmas 1–4, type A′, interior layers (batch 155)

The formalization is in nineteen new files under `HPC/Hagopian/` (REPORT-batch155.md): the skeleton
`Hagopian75.lean` and its supporting files `H75Defs`, `H75Basic`, `H75Sep` (Moore 22), `H75Lemma1`,
`H75Kur`, `H75KurScale`, `H75KurMap` (Kuratowski §48), `H75Transfer`, `H75Composants`, `H75Jones`,
`H75MooreA`, `H75MooreB`, `H75Triod` (Moore 84), `H75Thm1A`, `H75Thm1B`, `H75Thm1C` (Theorem 1),
`H75Counter`, `H75Sine` (the two refuted skeleton statements). Names are in namespace `HPC.Hagopian`.
* **Axioms.** Lean names are in the group *Hagopian 1975 (batch 155)* of `Axioms.lean` /
  `axioms.txt`, with standard axioms only. The audit of all 161 new theorems is
  `doc/batches/audits/axioms-batch155.txt`.
* **Sources.** Hagopian 1975, pp. 35–40 (`doc/sources/hagopian1975.pdf`); Kuratowski, *Topology* II,
  §48 (`doc/sources/kuratowski2-s48.pdf`); Moore 1962 (`doc/sources/moore1962-excerpts.pdf`); Jones
  1955 (`doc/sources/jones1955.pdf`).
* **Outcome.** Every item A–K is **proved**, including Moore's triod theorem (`moore_triod_theorem`)
  with no hypothesis. Shape changes: `uncountable_composants` (`¬ … .Countable`, as Mathlib has no
  `Set.Uncountable`), `composant_eq_or_disjoint` (compactness and connectedness omitted),
  `hagopian75_lemma2` (`hab` dropped), `hagopian75_layer_invariant` (`hr0`, `ht1` dropped). Two
  skeleton statements that are not Hagopian's sentences are **refuted** and kept commented out:
  `admissible_end_sets` (`not_admissible_end_sets`; corrected `admissible_end_sets'` with the type A′
  hypothesis) and `arc_of_degenerate_layers` (`not_arc_of_degenerate_layers`, the `sin (1/x)`
  continuum; what Hagopian uses is `exists_arc_of_degenerate_layers`).

**Checks.**

1. **p. 35:**
   > In this paper, a continuum is a nondegenerate compact connected metric space.

   The repository's `IsContinuum` admits a point. Nondegeneracy is needed, and assumed as
   `[Nontrivial X]`, in Moore 135, 136–137 and 139 (`composant_dense`, `composant_isMeagre`,
   `uncountable_composants`: a point has one composant, which is not meagre in itself). Theorem 1's
   conclusion "a homogeneous indecomposable continuum" is stated with `Y.Nontrivial`, which comes from
   paragraph 4 (`hnd`). Lemma 1, Lemma 2, Lemma 3, Lemma 4, the layer statements and paragraph 13
   need no nondegeneracy (for a point Lemma 1's conclusions hold vacuously; in Lemma 2, `a = b` makes
   both sides fail, so `hab` is dropped). Triods are nondegenerate by definition. **Classification:
   convention; recorded; no statement changes truth.**
2. **p. 36, Lemma 1:**
   > Suppose M contains a triod. Since M is homogeneous, it follows that each of its composants
   > contains a triod.

   A homeomorphism carries a triod to a triod and maps composants onto composants (it maps proper
   subcontinua to proper subcontinua). A triod `T` lies in some composant only if it is proper; it is,
   because an indecomposable continuum is not a triod (`not_isTriod_univ_of_indecomposable`: a triod
   is the union of two proper subcontinua). Then a homeomorphism carrying a point of `T` into a given
   composant `κ` carries `T` into `κ`. Copies in distinct composants are disjoint (Moore 138), giving
   uncountably many disjoint triods (Moore 139), against `moore_triod_theorem` (via the bridge
   `isTriodSet_image`). **Classification: unargued step (properness of the triod); true; supplied.**
3. **p. 36, Lemma 1:**
   > Since the plane is separable and M has uncountably many composants, there exists a proper
   > subcontinuum of M having two complementary domains that intersect M. This contradicts the fact
   > that each composant is dense in M [12, Theorem 135, p. 58].

   Both steps are unargued. *Separable step:* if every copy `F_κ` of `F` (one in each composant) had a
   complementary domain `U_κ` missing `M`, the `U_κ` would be pairwise disjoint (each misses the
   other's `F`, so if they met, each would lie in the other and `∂U_κ ⊆ F_κ ∩ F_κ' = ∅`;
   `disjoint_components_missing`), contradicting separability (`countable_of_pairwiseDisjoint_open`).
   So some `F_κ` has all its complementary domains meeting `M`, and it has two since `F` separates
   the plane (Moore 22, `separatesPlane_of_not_isPreconnected_inter`). *Density step:* `κ` is meagre
   (Moore 136–137), so by Baire a complementary domain `U` contains a point `p ∈ M ∖ κ`; the
   composant of `p` is dense (Moore 135), so it meets the other domain `V` at `q`; a proper
   subcontinuum through `p` and `q` meets `F_κ`, and its union with `F_κ` is proper (Moore 138's
   argument), so `p ∈ κ`. **Classification: unargued steps; true; supplied (disjointness of domains,
   Baire, Moore 138) in `H75Lemma1.lean`.**
4. **p. 36:**
   > Let D be a collection of compact subsets of a continuum M such that each point of M is contained
   > in one and only one element of D. … [type A:] admits an upper semi-continuous decomposition whose
   > elements are connected sets and whose quotient space is the unit interval [0,1].

   The map form (`IsAdmissibleMap`: continuous, onto `[0, 1]`, connected fibres) agrees: fibres of
   such a map are compact, connected, form an upper semicontinuous decomposition (closed map), and the
   quotient is homeomorphic to `[0, 1]` (`admissible_quotient_homeomorph`); conversely the quotient
   map of such a decomposition, composed with the homeomorphism onto `[0, 1]`, is admissible with the
   elements as fibres. Both directions are written out at `admissible_quotient_homeomorph`; the first
   is formalized. **Classification: definition; agrees.**
5. **pp. 36–37, Lemma 2:**
   > A necessary and sufficient condition that M be of type A′ is that every subcontinuum of M with
   > nonvoid interior be decomposable [10, Theorem 3, p. 216] [14, Theorem 10, p. 15].

   Kuratowski's Theorem 3 is about the order type of the family `D`, not type A′. The gap is filled
   (`H75Kur`, `H75KurScale`, `H75KurMap`): `D` is a chain (§48 III, `IsDElt.chain`) without jumps when
   every subcontinuum with interior is decomposable (VII Theorems 1–2, `IsDElt.exists_between`); a
   countable dense subfamily is order-isomorphic to `ℚ ∩ (0, 1)` (`exists_scale`), and
   `k(y) = inf {q : y ∈ D_q}` is admissible with layers of void interior (`scaleMap_spec`; §48 IV, VII
   Theorems 4–5). Necessity is direct (`not_isIndecomposable_of_typeA'`). **Classification: citation
   does not state the claim; lemma true; gap filled.**
6. **p. 37, Lemma 3:**
   > If M is a continuum of type A, then M has a unique minimal admissible decomposition (relative to
   > the partial ordering by refinement) [14, Theorem 3, p. 8 and Theorem 6, p. 10].

   Thomas is not in hand. Only the type A′ form is proved and used: the type A′ map refines every
   admissible map (`hagopian75_lemma3`), and two type A′ maps have the same layers
   (`hagopian75_lemma3_unique`). The printed type A form is not formalized. **Classification: proved in
   the form used.**
7. **p. 37:**
   > A topological transfromation group (G,M) is … E. G. Effros [5, Theorem 2.1] proved that each
   > orbit is a set of the type G_δ in M if and only if for each x ∈ M, the mapping Gx → g(x) of G/G_x
   > onto Gx is a homeomorphism.

   Misprint "transfromation" for "transformation". The repository's Effros theorem
   (`HPC.Effros.effros_homogeneous`) is the uniform consequence of the open-mapping form: for `ε > 0`
   there is `δ > 0` such that points within `δ` are exchanged by a homeomorphism moving no point by
   `ε`. Lemma 4 takes `W` the ball of radius `δ/2` instead of Hagopian's `T_x[U]`. **Classification:
   misprint; citation used in an equivalent form.**
8. **p. 38, Theorem 1:**
   > Since M is hereditarily unicoherent and I is indecomposable, I is contained in E ∩ B or E ∩ C.

   True: `I ∩ B` and `I ∩ C` are continua or empty (hereditary unicoherence applied to `I ∩ A`, `B`,
   `C`; `isContinuum_inter_of_HU`) with union `I`, so one of them is `I` by indecomposability.
   **Classification: true; terse.**
9. **p. 38:**
   > Let F be the c-component of E − Q.

   Read as the component of `E − Q` containing `c`. `c ∉ Q` since `Q ⊆ I ⊆ B` and `c ∉ B`. The proof
   uses any continuum `F ⊆ E ∖ O` through `c` meeting `cl Q` (boundary bumping,
   `exists_continuum_bump_closed`). **Classification: notation; true.**
10. **p. 38:**
    > Since F is a continuum that does not contain I and M is hereditarily unicoherent, F meets only
    > one composant of I. Let x be a boundary point of Q that belongs to F. By Lemma 4, there exist
    > homeomorphisms f and g … (1) x, f(x), and g(x) belong to distinct composants of I, (2)
    > {c, f(c), g(c)} is a subset of M − B, and (3) Q is not contained in f[F] ∪ g[F]. Note that F,
    > f[F], and g[F] are mutually disjoint. It follows that B ∪ F ∪ f[F] ∪ g[F] is a triod.

    * "`F` meets only one composant of `I`": true (`F ∩ I` is a proper subcontinuum of `I`, by
      hereditary unicoherence).
    * "a boundary point of `Q` that belongs to `F`": true by boundary bumping (`F` reaches `cl Q`).
    * `f`, `g`: exist (Effros with `ε = min(dist(c, B), dist(q, F))`, `q ∈ Q`; composants of `I` are
      meagre, so the `δ`-ball at `x` has points of `I` in two further composants). `f(x)`, `g(x)` are
      taken in composants of `I` other than that of `x`; (3) is obtained as `q ∉ f[F] ∪ g[F]`.
    * Mutual disjointness (unargued): if `F ∩ f[F] ≠ ∅`, `(F ∪ f[F]) ∩ I` is a continuum through `x`
      and `f(x)`, in distinct composants, so it is `I ∋ q`, against `q ∉ F ∪ f[F]`. Same for the other
      pairs.
    * The triod (unargued): core `B`; the pieces `F ∖ B`, `f[F] ∖ B`, `g[F] ∖ B` are nonempty
      (`c`, `f(c)`, `g(c)`), pairwise separated as each closure lies in its closed source and the
      sources are disjoint (`isTriod_of_core`).

    **Classification: all true; disjointness and the triod structure unargued; supplied
    (`H75Thm1A.lean`).**
11. **p. 38, paragraph 4:**
    > There exists a number s (0 < s < 1) such that k⁻¹(s) is not degenerate; for otherwise, E would
    > contain an arc [14, Theorem 21, p. 29] and M would be a simple closed curve [3]

    Set aside, as the commission directs: it is the hypothesis `hnd` of
    `hagopian75_theorem1_of_layer`. The first half is proved (`exists_arc_of_degenerate_layers`); the
    second needs Bing 1960 (a homogeneous bounded plane continuum containing an arc is a simple closed
    curve), which is not in the repository and which Hagopian 1976 does not use. The skeleton's
    `arc_of_degenerate_layers` (conclusion "`E` is an arc") is false (`not_arc_of_degenerate_layers`);
    Hagopian's sentence only claims that `E` *contains* an arc, which is true. **Classification: set
    aside (Bing 1960); first half true.**
12. **p. 39, paragraph 9:**
    > Since Y ∩ hᵢ[Y] ≠ ∅ and M is atriodic and hereditarily unicoherent, hᵢ[Y] ⊂ hᵢk⁻¹[[r,t]] ⊂ E.

    The second inclusion is unargued. It is true (`homeo_image_subset_of_meets`): otherwise
    `J = E ∩ hᵢk⁻¹[r, t]` is a continuum with `k(J) = [d′, e′] ⊆ (0, 1)`, and `k⁻¹[0, d′]`,
    `k⁻¹[e′, 1]` and `hᵢk⁻¹[r, t] ∪ k⁻¹[d′, e′]` form a triod with core `k⁻¹[d′, e′]`.
    **Classification: unargued step; true; supplied.**
13. **p. 39, paragraph 10:**
    > the closure of R ∪ T does not meet an element of H. Hence hᵢ[Y] contains a nonempty open subset
    > of hᵢ[E], which contradicts the fact that hᵢ[Y] is an element of {hᵢk⁻¹(u) : 0 ≤ u ≤ 1}, the
    > minimal admissible decomposition of hᵢ[E].

    The first sentence is true (`homeo_image_layer_subset`: the images of `k⁻¹[r, s)` and
    `k⁻¹(s, t]` are connected subsets of `E` missing `k⁻¹(d, e) ⊆ hᵢ[Y]`, so each lies on one side).
    The contradiction is obtained without the minimal decomposition: pulling the open set back by `hᵢ`
    gives `Y` nonvoid interior in `E`, against `hk0`. The printed route needs the decomposition to be
    intrinsic, which holds (`hagopian75_lemma3_unique`). **Classification: true; route simplified.**
14. **p. 39, paragraph 11:**
    > Using the same argument, one can show that if Y is not contained in hᵢ[Y], then Y has nonvoid
    > interior relative to E

    It is paragraph 10 applied to `hᵢ⁻¹`, which moves no point by `ε` and meets `Y` on `Y`
    (`hagopian75_layer_invariant_aux`). **Classification: true; same argument.**
15. **p. 39:**
    > Since Y is a unicoherent homogeneous plane continuum, it is indecomposable [9, Theorem 2].

    Jones 1955 Theorem 2 does not state this: it states that a homogeneous decomposable bounded plane
    continuum is a continuous collection of continua forming a simple closed curve. It implies it: the
    preimages of two half-circles are subcontinua whose intersection is not connected
    (`indecomposable_of_unicoherent_homogeneous`, from `jones55_theorem2'`). (Jones's Remarks state
    indecomposability only for the nonseparating elements of `G`.) **Classification: implied, not
    stated; supplied.**

No statement of Hagopian's is false as printed, and no step of the proofs read is false; the gaps
are unargued steps, all true, and one citation (Kuratowski Theorem 3) that does not state what it is
cited for. No defective proof is added; the count stays at fourteen. The two refuted statements are
skeleton forms of Thomas's results (Theorems 8 and 21 as cited), not Hagopian's sentences.

### Hagopian 1976 I: §2, Lemmas 2–8; the consequences of Theorem 1 (batch 156)

The formalization is in eight new files under `HPC/Hagopian/` (`doc/batches/REPORT-batch156.md`):
the skeleton `Hagopian76A.lean` and its supporting files `H76Defs` (the definitions and
`Hagopian76Thm1`, verbatim), `H76Lemma2`, `H76Lemma3`, `H76Lemma4` (chain; countable form),
`H76Lemma4Layers`, `H76Lemma8`, `H76Cons` (the consequences of Theorem 1). Names are in namespace
`HPC.Hagopian`.
* **Axioms.** Lean names are in the group *Hagopian 1976 §2 (batch 156)* of `Axioms.lean` /
  `axioms.txt`, with standard axioms only. The audit of all 33 new theorems is
  `doc/batches/audits/axioms-batch156.txt`.
* **Source.** Hagopian 1976, pp. 339–344 and 349 (`doc/sources/hagopian1976.pdf`); Moore 1962,
  Theorem 44 (`doc/sources/moore1962-excerpts.pdf`).
* **Outcome.** **Proved:** items A (definitions), B (`hagopian76_lemma2`, `hagopian76_end_sets`), C
  (`hagopian76_lemma3`, as printed), H (`hagopian76_lemma8`), I (all five consequences, from
  `h1 : Hagopian76Thm1`). From item D, `hagopian76_lemma4_chain` (linear order),
  `hagopian76_lemma4_layers'` (the corrected first paragraph) and `hagopian76_lemma4_seq_of_noMax`
  (the sequence, given no maximal element) are proved. In the continuation, Lemma 4 as printed and
  its sequence form are proved (`hagopian76_lemma4`, `hagopian76_lemma4_seq`, via
  `exists_proper_extension`, `HPC/Hagopian/H76NoMax.lean`). **Open**, commented out with the
  obstruction in `OPEN.md`: `hagopian76_lemma4_layers` as printed (D1), Lemma 5 (E), Lemma 6 and the two unnumbered claims (F), Lemma 7 (G).
  **Refuted:** nothing. Shape changes: `hagopian76_lemma3` (`hu0`, `hu1` dropped, unused);
  `hagopian76_lemma4_layers'` (new, the corrected form); `hagopian76_lemma4_chain`,
  `hagopian76_lemma4_seq_of_noMax` (new, the two proved halves).

**Checks.**

1. **p. 339:**
   > A continuum is a nondegenerate compact connected metric space. A continuum is of type A′
   > provided it is irreducible between a pair of its points and admits a monotone upper
   > semicontinuous decomposition, each of whose elements has void interior, whose quotient space is
   > an arc [14].

   1975 (p. 36) said "an upper semi-continuous decomposition whose elements are connected sets and
   whose quotient space is the unit interval". A monotone decomposition is one with connected
   elements, and an arc is homeomorphic to `[0, 1]`, so the two definitions agree. Both are the
   repository's `IsTypeA'`, and `IsMinimalAdmissible` is the map form (an admissible map with
   layers of void interior on an irreducible continuum). Nondegeneracy is as in 1975 (batch 155,
   check 1). **Classification: definition; agrees.**
2. **p. 340:**
   > No proper subcontinuum of E intersects both X and Z [14, Theorem 8, p. 14].

   This is true for the decomposition (`hagopian76_end_sets`, from `admissible_end_sets'`: it needs
   the layers to have void interior). It fails for an arbitrary admissible map
   (`not_admissible_end_sets`: on `[0, 2]`, `max 0 (x − 1)`). In §2 "the decomposition" is the
   minimal one, so the sentence is correct as used. **Classification: true in context; recorded.**
3. **p. 340, Lemma 3:**
   > Suppose h is a homeomorphism of M onto M such that U ∩ h[Y] ≠ ∅ and U ∩ h[X ∪ Z] = ∅ =
   > h[Y] ∩ (T ∪ V). Then h[Y] = U. PROOF. This lemma follows from the argument presented in
   > paragraphs 9 through 11 in the proof of Theorem 1 of [5].

   The 1975 argument uses an `ε` to keep `h k⁻¹[[r, t]]` off the end sets. Here
   `h[Y] ∩ (T ∪ V) = ∅` plays that role: by the 1975 ¶9 triod it puts `h[Y]` inside `F`. With
   `J = F ∩ h[E]` (a continuum, Lemma 1) and `[γ, δ] = k(h⁻¹[J])`, the end cases `γ = s` and `δ = s`
   put `h[X]` or `h[Z]` inside `h[Y]`. In the middle case, `h[Y] ⊄ U` gives `h[Y]` an open subset of
   `F`, and the ¶10 neighbourhood argument then gives `Y` interior in `E`. So `h[Y] ⊆ U`, and the
   same argument for `h⁻¹` (using `U ∩ h[X ∪ Z] = ∅`) gives `U ⊆ h[Y]`. The 1975 argument goes through
   with the changes stated (`H76Lemma3.lean`). **Classification: citation adapts; true as printed;
   supplied.**
4. **p. 341, Lemma 4:**
   > Since the decompositions of E and F are minimal, each element of the decomposition of E (except
   > possibly k⁻¹(1)) is an element of the decomposition of F.

   > If H is an element of F, then F ⊂ H or H ⊂ F; for otherwise, the continuum H ∩ d⁻¹[[s, 1]]
   > (Lemma 1) would separate F ∪ H into three nonempty disjoint open sets, which contradicts the
   > fact that M is atriodic.

   > Since F is irreducible between X and d⁻¹(1), it is a proper subset of an element of F that is
   > contained in F ∪ h⁻¹[F] (Lemma 1).

   *First sentence:* the reason given does not suffice. Minimality gives
   `d⁻¹[0, s) ⊆ E ⊆ d⁻¹[0, s]`, puts each layer of `E` inside a layer of `F`, and makes a layer of `E`
   inside `d⁻¹(u)`, `u < s`, equal to `d⁻¹(u)` (`hagopian76_lemma4_layers'`). A plane configuration
   with every hypothesis except homogeneity has a non-end layer of `E` strictly inside `d⁻¹(s)`, and
   another has `E ≠ d⁻¹[0, s]` (`OPEN.md`, D1). Inside a homogeneous indecomposable `M` the claim
   cannot be refuted, since by Theorem 1 no type A′ `E` exists. The main proof of Lemma 4 does not
   use this sentence. *Triod:* proved (`ext_chain`), with core `N = J ∩ d⁻¹[r, 1]`, `J = F ∩ H`, and
   arms in `d⁻¹[0, r]`, `d⁻¹[σ, 1]`, `e⁻¹[e(z), 1]`. *Third sentence:* unargued, and
   supplied in the continuation of batch 156 (`exists_proper_extension`, `H76NoMax.lean`). Either
   `F ⊆ h⁻¹[F]` (`ext_of_subset`), or a half of `h⁻¹[F]` meets `F` only in `d⁻¹(1)` and the proper
   extension lies in `F ∪ F″` (`ext_of_branch`), or a layer of `h⁻¹[F]` contains a tail of `F`, which
   is handled by a three-continua argument from atriodicity (`ext_of_side`). So Lemma 4 holds as
   printed (`hagopian76_lemma4`, `hagopian76_lemma4_seq`; `OPEN.md`, D2, closed).
   **Classification: first sentence, gap (reason insufficient), open; triod, true, supplied; third
   sentence, unargued, true, supplied.**
5. **p. 341, Lemma 5:**
   > There exists a type A′ continuum F in R(E) that is the union of two extensions of E such that
   > the end sets T and V of F miss E (Lemma 4). … In fact, each element of A that is not an end set
   > of E is an element of B. … By Lemma 2, an integer i and an ε/2-homeomorphism h of M onto M exist
   > such that (1) h(y) = yᵢ, (2) Yᵢ ∈ B, and (3) ρ(Yᵢ, T ∪ V) > ε/2.

   The existence of `F` uses Lemma 4's "no maximal element" (proved in the continuation). That the union is of type A′ is
   not argued. "Each element of `A` that is not an end set of `E` is an element of `B`" is the
   two-sided form of check 4's first sentence, and holds for layers lying strictly inside by the
   argument of `hagopian76_lemma4_layers'`. The choice (1)–(3) is by Lemma 2 and upper
   semicontinuity, and Lemma 3 (proved) then finishes the proof. **Classification: depends on open
   steps; open.**
6. **p. 342, Lemma 6:**
   > Since M is second countable, there exists a monotone strictly increasing sequence {Fᵢ} of
   > elements of F such that R(X, E) = ⋃ Fᵢ (Lemma 4).

   Proved from Lemma 4, `exists_strictMono_seq_of_chain`: for each basic open set met by a member,
   choose one such member; these countably many members are cofinal (otherwise every chosen member
   lies in a member `F`, and a larger member `G` has a point outside `F` with a basic neighbourhood
   missing `F`), and a strictly increasing sequence dominating them is chosen using "no maximal
   element". With "no maximal element" supplied in the continuation (check 4), `hagopian76_lemma4_seq`
   is proved; `hagopian76_lemma4_seq_of_noMax` (the hypothetical form) is kept. **Classification: true given Lemma 4; argument
   supplied.**
7. **pp. 342–343, Lemma 6, steps 1–8:**
   > Since E is irreducible and M is hereditarily unicoherent, and since X does not have interior
   > relative to E, it follows that B contains X.

   > The sets X and C are disjoint. … Note that B − C is contained in K. … The point c belongs to
   > Cl R(X, E) − R(X, E). … The sets N and h₁⁻¹[N] are disjoint. … Thus C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]
   > is a triod … We complete this proof by showing that Cl R(X, E) = Cl R(E).

   Steps 1–3 need only Lemma 1 and irreducibility, and were checked informally. Steps 4–8 use the
   sequence `{Fᵢ}` (check 6, so Lemma 4) and the continuity of the decompositions of the extensions
   (Lemma 5). Not formalized. **Classification: depends on Lemmas 4 and 5; open.**
8. **p. 343:**
   > Since M is atriodic, R(E) is a composant of Cl R(E). … Note that every continuum essential to
   > R(E) is of type A′ (Lemma 5).

   Both are unnumbered. The first needs Lemma 6 (indecomposability of `Cl R(E)`), and the second
   needs Lemma 5. **Classification: depends on Lemmas 5 and 6; open.**
9. **pp. 343–344, Lemma 7:**
   > By Lemma 2, an integer i and a homeomorphism f of M onto M exist such that a continuum F
   > essential to fhᵢ[R(E)] contains u, misses t, and intersects A. … Note that g[F] ∪ Hⱼ is a triod
   > in M.

   Both steps use "essential" continua and their type A′ structure (check 8). The reading "essential
   to `h[R(E)]`" = "`h⁻¹[H]` essential to `R(E)`" loses nothing, since `h` carries extensions of `E`
   to extensions of `h[E]` together with their decompositions. **Classification: depends on Lemma 5;
   open.**
10. **p. 344, Lemma 8:**
    > Since M is atriodic, there exist open sets A and B in G₁ and Gₙ, respectively, such that E is a
    > component of M − (A ∪ B). … The chain {Lᵢ: 1 ≤ i ≤ n} is an ordered refinement of G that
    > follows E and is free relative to M.

    Both are unargued and true. `A = G₁ − E` and `B = Gₙ − E` work (`component_of_caps`): a larger
    connected set would, by boundary bumping, contain a continuum meeting `E` and missing `X ∪ Z`,
    which lies in `E` by the 1975 ¶9 triod. Then Moore 1962 Theorem 44 gives `C` and `D`
    (`exists_closed_split_of_no_connected`). The final sentence holds: the overlaps of `G` meet
    `E ⊆ C`, so `L` is a chain; it follows `E` because every point of `E` in `Gⱼ` is in `Lⱼ`; and it is
    free because a point of `M ∩ Bd St L` lies in `D`, so it is not in `C`. For one or two links,
    `L = G` and `G` is free by definition. **Classification: unargued steps; true; supplied.**
11. **p. 349, Theorem 2:**
    > Since every homogeneous nonseparating plane continuum is indecomposable [4], [6], this theorem
    > follows immediately from Theorem 1.

    The repository route: a decomposable homogeneous plane continuum has two complementary domains
    (`jones55_two_domains'`, from Jones 1955 Theorem 2), so a nonseparating one is indecomposable.
    Gordh 1975 [4] and Jones 1951 [6] are not needed (`hagopian76_theorem2`). **Classification:
    citation replaced; true.**
12. **p. 339, abstract:**
    > It follows from these results that every homogeneous plane continuum that has a hereditarily
    > decomposable subcontinuum is a simple closed curve.

    This is Hagopian 1975 Theorem 2 (`hagopian75_theorem2`, from `h1 : Hagopian76Thm1`). If `M` is
    indecomposable, the 1975 Corollary excludes `H`. If `M` is decomposable, the elements of
    Jones's decomposition (`jones55_theorem2'`) are degenerate, so `M` is a circle. An element
    containing `H` would be a homogeneous indecomposable plane continuum with a decomposable
    subcontinuum, which Theorem 1 excludes. An element meeting `H` and a point outside it lies in `H`
    (`jones55_c`), so it is hereditarily decomposable and indecomposable, hence degenerate. The
    abstract derives the statement from the 1975 Corollary, whose proof rests on 1975 Theorem 1 as
    printed. In the repository, both routes go through `Hagopian76Thm1`. **Classification: true;
    proved conditionally on Theorem 1.**

No statement of Hagopian's is refuted. One stated reason is insufficient (check 4, first sentence),
and its truth in context is open. One step is unargued and open (check 5); a second unargued step (check 4, third sentence) is supplied
in the continuation of batch 156.
Everything downstream (Lemmas 5–7) is open. No defective proof is added while these are unsettled;
the count stays at fourteen.

### Hagopian 1976 II: §2 continued (D1, Lemmas 5–7); the set-up of Theorem 1 (batch 157)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76B.lean` and six new supporting files
under `HPC/Hagopian/` (`doc/batches/REPORT-batch157.md`): `H76BDefs` (the set-up definitions,
verbatim), `H76SepInv` (plane separation carried over by homeomorphisms, up to subcontinua),
`H76NoSep` (no proper subcontinuum separates), `H76D1` (D1 reduced to the swallowed configuration),
`H76Lemma5` (Lemma 5 away from the end sets), `H76Setup` (`S`, `π`, the arc `π[E]`, accessibility).
Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 §2 continued (batch 157)* of `Axioms.lean` / `axioms.txt`,
  standard axioms only; the audit of all 44 new theorems is `doc/batches/audits/axioms-batch157.txt`.
* **Source.** Hagopian 1976, pp. 341–349 (`doc/sources/hagopian1976.pdf`); Hagopian 1975, p. 36
  (`doc/sources/hagopian1975.pdf`); Moore 1925 Theorem 22 (batch 147); Bing 1951 Theorem 6
  (batch 132–133); Bing 1960, p. 215 (`doc/sources/bing1960.pdf`, reading plan only).
* **Outcome.** **Proved:** `no_proper_subcontinuum_separates`, `layerSetoid_mooreDecomp`,
  `exists_quotient_plane`, `exists_accessible_typeA'` (shape: `hi` dropped, unused),
  `hagopian76_lemma5_interior`; and, added, `hagopian76_lemma5_usc`, `hagopian76_lemma5_of_ends`,
  `hagopian76_lemma4_layers_of_no_swallowed`, `hagopian76_no_swallowed_of_lemma4_layers`. **Open**,
  commented out with the obstruction in `OPEN.md` (batch-157 section): D1
  (`hagopian76_lemma4_layers`, `hagopian76_no_swallowed_layer`), `hagopian76_lemma5`,
  `hagopian76_two_sided_extension`, Lemma 6 and the two unnumbered claims, Lemma 7. **Refuted:**
  nothing.

**Checks.**

1. **p. 341, Lemma 4:**
   > Since the decompositions of E and F are minimal, each element of the decomposition of E (except
   > possibly k⁻¹(1)) is an element of the decomposition of F.

   Re-rendered (commission §0; ledger C.2): the first two sentences of the paragraph are
   `hagopian76_lemma4_layers'`, and this sentence is equivalent, without homogeneity, to the
   exclusion of the swallowed configuration `d⁻¹(s) ∩ E = k⁻¹[[t₀, 1]]`, `t₀ < 1`
   (`hagopian76_lemma4_layers_of_no_swallowed`, `hagopian76_no_swallowed_of_lemma4_layers`; the
   step supplied is `k⁻¹(1) ⊆ d⁻¹(s)`). The half-bar model realizes the configuration without
   homogeneity. **Classification: reason insufficient; truth in context open (D1).**
2. **p. 341, Lemma 5:**
   > There exists a type A′ continuum F in R(E) that is the union of two extensions of E such that the
   > end sets T and V of F miss E (Lemma 4).

   Lemma 4 gives the two extensions. That their union is of type A′ with end sets missing `E` is
   unargued; the natural argument needs the tails of the two extensions to meet `E` only in `Z` and
   `X`, which is D1 at both ends. **Classification: unargued; open (depends on D1).**

   > Each element of A is contained in an element of B. In fact, each element of A that is not an end
   > set of E is an element of B.

   The first sentence is the `hin` clause of `lemma4_layers_aux` (applied on either side). The
   second is the two-sided D1. **Classification: first sentence true (proved form); second open
   (D1).**

   > By Lemma 2, an integer i and an ε/2-homeomorphism h of M onto M exist such that (1) h(y) = yᵢ,
   > (2) Yᵢ ∈ B, and (3) ρ(Yᵢ, T ∪ V) > ε/2. It follows from Lemma 3 that h[U] = Yᵢ.

   (1) and (3) are Lemma 2 and compactness. (2) is the second sentence above (D1). At layers other
   than the end sets the whole step is replaced by Lemma 3 with `F := E`
   (`hagopian76_lemma5_interior`, proved, in neighbourhood form): there `h[Y] ∩ (X ∪ Z) = ∅` holds
   for `h` near the identity, and Hagopian's `F` is not needed. At the end sets `h[U] ∩ X = ∅` fails,
   so `F` is needed, and with it (2). **Classification: true away from the end sets (proved by
   another route); at the end sets depends on D1; open.**
3. **p. 342:**
   > Note that if F is an element of the set F of extensions of E away from X, then the
   > decomposition of F is a continuous collection (Lemma 5) that has the decomposition of E as a
   > subcollection.

   *Continuity:* Lemma 5 for `F` (open at the end sets). *Subcollection:* D1 for `E ⊆ F`, with
   possibly `k⁻¹(1)` excepted. Used in step 6 of Lemma 6 (check 4). **Classification: depends on
   Lemma 5 and D1; open.**
4. **pp. 342–343, Lemma 6, steps 1–8** (checked, not formalized):
   1. > Since E is irreducible and M is hereditarily unicoherent, and since X does not have interior
      > relative to E, it follows that B contains X.

      `B ∩ E`, `C ∩ E` are continua (Lemma 1) covering `E`; the one meeting `Z`-side layers and `X`
      would be `E`; `X` having void interior excludes `X` split between them. Uses Lemma 1 and the
      end sets. **True; supplied detail.**
   2. > The sets X and C are disjoint. … Since B ∩ H and C ∩ H are continua, this violates the
      > irreducibility of H.

      Lemma 1 and irreducibility. **True.**
   3. > Note that B − C is contained in K.

      `K ∩ B ⊇ X` and `K ∩ C` are continua covering `K`; with Lemma 4 (linear order) every extension
      meeting `B − C` is comparable with `K`. Unargued; follows from Lemmas 1 and 4. **True as far as
      checked.**
   4. > Since M is second countable, there exists a monotone strictly increasing sequence {Fᵢ} of
      > elements of F such that R(X, E) = ⋃ Fᵢ (Lemma 4).

      `hagopian76_lemma4_seq` (batch 156). **True; proved.**
   5. > The point c belongs to Cl R(X, E) − R(X, E). … Since M is atriodic, it follows that f[L] is a
      > subset of R(X, E).

      Lemma 2, Lemma 1 (unicoherence, atriodicity), irreducibility of `Fᵢ`. **True as far as
      checked.**
   6. > The sets N and h₁⁻¹[N] are disjoint. For suppose on the contrary that N ∩ h₁⁻¹[N] ≠ ∅. Then
      > since no element Y of the decomposition of N has the property that h₁⁻¹[Y] contains N, the
      > point c belongs to R(E).

      `ε₁` is chosen so that no `ε₁`-neighbourhood of a layer of `K` contains `K`. To pass from layers
      of `K` to layers of `N ⊇ K` one needs the layers of `N` meeting `K` to be layers of `K`: the
      subcollection remark (check 3), D1. A layer of `N` swallowing layers of `K` is not controlled by
      `ε₁`. **Depends on D1; open.**
   7. > Thus C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P] is a triod, and this is a contradiction of Lemma 1.

      Given step 6. **True as far as checked.**
   8. > By Lemma 2, there exist homeomorphisms f₁ and f₂ of M onto M near the identity such that
      > Q ∪ f₁[Q] ∪ f₂[Q] ∪ Cl R(X, E) is a triod (see the second paragraph in the proof of Theorem 1
      > of [5]).

      The 1975 ¶2 argument (`hagopian75_no_indecomposable_interior` and its proof). **True as far as
      checked; not formalized.**
5. **p. 343:**
   > Since M is atriodic, R(E) is a composant of Cl R(E).

   Uses Lemma 6. **Depends on Lemma 6; open.**

   > Note that every continuum essential to R(E) is of type A′ (Lemma 5).

   Needs (i) that the continuum lies in a single extension (unargued) and (ii) that it contains the
   whole layers it meets at its two ends, which is lower semicontinuity of that extension's
   decomposition there (possibly at an end set: Lemma 5 open). **Unargued; depends on Lemma 5;
   open.**
6. **pp. 343–344, Lemma 7:**
   > By Lemma 2, an integer i and a homeomorphism f of M onto M exist such that a continuum F
   > essential to fhᵢ[R(E)] contains u, misses t, and intersects A.

   Uses Lemma 2 at `u ∈ Cl R(E)` and the structure of `R(E)` near `u` (Lemma 6: `u` is in the
   indecomposable `Cl R(E)`, approximated by essential continua). **Unargued detail; depends on
   Lemma 6; open.**

   > Note that g[F] ∪ Hⱼ is a triod in M.

   `g[F]` contains `u` and meets `A`; `Hⱼ` passes near `u` with ends near `t`; the triod uses the
   type A′ structure of `Hⱼ` (essential, check 5). **Unargued; depends on check 5; open.**
7. **p. 344:**
   > Since M is indecomposable and homogeneous, no proper subcontinuum of M separates R² [5, Lemma 1
   > (second paragraph of proof)]. Hence we can assume that the quotient space R²/S is R² [12].

   *First sentence:* the cited paragraph proves hereditary unicoherence; its argument applied to a
   separating `K` needs a separating continuum in each copy `h[K]`, i.e. the topological invariance
   of plane separation (Borsuk), which neither paper states. Supplied without Borsuk
   (`exists_separating_subcontinuum_of_homeomorph`: a logarithm argument and Bing 1951 Theorem 6),
   then the 1975 argument (`no_proper_subcontinuum_separates`). **Citation adapts; unstated
   invariance step supplied; true.**
   *Second sentence:* Moore 1925 Theorem 22 gives `R²/S ≅ R²` once `S` satisfies its hypotheses
   (`layerSetoid_mooreDecomp`: u.s.c. from `k`, not Lemma 5). "We can assume" hides that `π` is the
   quotient map followed by a homeomorphism `R²/S → R²`; `π` is a quotient map with fibres the
   classes of `S` (`exists_quotient_plane`), not a homeomorphism, so later uses of `π[M]`, `π[Gᵢ]`,
   `π⁻¹` refer to this composite; `π⁻¹` is the preimage. **Supplied; true.**
8. **p. 345:**
   > Since M is homogeneous, we can assume without loss of generality that k⁻¹[(0, 1)] is accessible
   > from R² − M.

   Read as "some point of `k⁻¹((0, 1))` is accessible": proved (`exists_accessible_typeA'`; a nearest
   point of `M` to a point off `M`, then a homeomorphism of `M` moving it into `k⁻¹(1/2)`; `E` is
   replaced by its image). The later sentence "each point of `π[E]` is an end point of an arc segment
   in `R² − π[M]` below `π[E]` (Lemma 9)" is a stronger statement, and Lemma 9 supplies only part of
   it: Lemma 9 gives, for each pair `U`, `Y` of non-end layers with `Y` accessible, arcs on a common
   side; "below" for every point needs the side to be the same for all `U` (Hagopian fixes it by the
   vertical segment `π[I]` below `π[E]` in Lemma 9's proof), and the end points of `π[E]` are not
   covered (they are not used: the points `pᵢ = (4i − 1, 0)` are interior). **First sentence:
   supplied, true (weak reading). Second: stronger; to be checked with Lemma 9 (batch 158).**
9. **p. 347 (new):**
   > Let e be the point of [0, 1] such that d⁻¹[[0, e]] = E.

   This is the strong form `layerSet d (Icc 0 e) = E` that the batch-156 skeleton used and the
   half-bar model separates from the printed Lemma 4 (`E′ ≠ d⁻¹[0, s]`). Here `F` is an extension
   away from `k⁻¹(0)`, so it needs `d⁻¹(e) ⊆ E`, more than D1 as re-rendered. **Stronger than D1;
   open.**

No statement of Hagopian's is refuted. Two unstated steps are supplied (checks 7 and 8, first
sentence), Lemma 5 is proved away from the end sets by a route that avoids D1 (check 2), and D1 is
reduced to one configuration (check 1). Everything that uses D1 or Lemma 5 at the end sets
(Lemma 5 in full, the two-sided extension, Lemmas 6–7, the unnumbered claims, and check 9) is
open. No defective proof is added; the count stays at fourteen.

### Hagopian 1976 III: D1 by lower semicontinuity; Lemma 5; Moore 1962 Theorem 28; Lemma 9 (batch 158)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76C.lean` and five new supporting files
under `HPC/Hagopian/` (`doc/batches/REPORT-batch158.md`): `H76Far` (D1 in the strong form, the
commission's route), `H76Lemma5End` (the initial-segment form; Lemma 5 at the end sets),
`H76Moore28` (Moore 1962 Theorem 28), `H76Quot` (the arc `π[E]` with its parametrization), `H76Sub`
(a subcontinuum meeting two layers is of type A′: `isTypeA'_of_subcontinuum`, toward item C). Names are
in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 III (batch 158)* of `Axioms.lean` / `axioms.txt`, standard
  axioms only; the audit of the new theorems is `doc/batches/audits/axioms-batch158.txt`.
* **Source.** Hagopian 1976, pp. 341–347 (`doc/sources/hagopian1976.pdf`); Moore 1962, Theorem 28,
  p. 156 (`doc/sources/moore1962-excerpts.pdf`; the excerpt breaks off inside the proof); Bing 1960,
  p. 215 (`doc/sources/bing1960.pdf`).
* **Outcome.** **Proved:** `hagopian76_far_layer`, `hagopian76_initial_segment`,
  `hagopian76_lemma4_layers` (re-rendered), `hagopian76_no_swallowed_layer`, `hagopian76_lemma5`,
  `moore62_theorem28`, `exists_quotient_plane'`; supporting, toward item C: `isTypeA'_of_subcontinuum`.
  **Open**, commented out with the obstruction in
  `OPEN.md` (batch-158 section): `hagopian76_two_sided_extension` (not needed), Lemma 6 and the two
  unnumbered claims, Lemma 7, Lemma 9. **Refuted:** nothing.

**Checks.**

1. **p. 341, Lemma 4, first paragraph:**
   > Since the decompositions of E and F are minimal, each element of the decomposition of E (except
   > possibly k⁻¹(1)) is an element of the decomposition of F.

   The reason given (minimality of the two decompositions) is insufficient: the half-bar model of
   batch 156 has both decompositions minimal and a layer of `F` swallowing layers of `E`. The
   statement is nevertheless true in the setting of the lemma, even in the strong form
   `d⁻¹[[0, s]] = E` with every layer of `E` (including `k⁻¹(1)`, which is `d⁻¹(s)`) a layer of `F`
   (`hagopian76_initial_segment`). The argument (commission 158 §1, checked step by step in the report,
   §0) uses Lemmas 2 and 3 through the lower semicontinuity of the decomposition of `F` at its interior
   layer `d⁻¹(s)` (`hagopian76_lemma5_interior` for `F`), and continuity of `k`. **Classification:
   unargued step (reason insufficient); true; supplied by an argument Hagopian does not give.**
2. **p. 341, Lemma 5:**
   > There exists a type A′ continuum F in R(E) that is the union of two extensions of E such that the
   > end sets T and V of F miss E (Lemma 4). Let B denote the decomposition of F. Each element of A is
   > contained in an element of B. In fact, each element of A that is not an end set of E is an
   > element of B.

   *Route actually used* (`hagopian76_lemma5`): at each end set, one extension on the other side
   (Lemma 4, `exists_proper_extension`, with the reversed map at `X`); item A makes the end set an
   interior layer of that extension and the layers of `E` its layers; lower semicontinuity passes from
   the extension to `E`. The continuum `F` is never formed. *The sentences:* the last one is true
   (item A applied on each side, each extension separately); that the union of the two extensions is of
   type A′ with end sets missing `E` remains unargued and is not needed
   (`hagopian76_two_sided_extension`, open). **Classification: Lemma 5 true, proved by a variant of
   Hagopian's route; the type A′ structure of `F` unargued, not needed.**
3. **pp. 342–343, Lemma 6, steps 1–8** (quoted in the batch-157 subsection, check 4). Step 6:
   > The sets N and h₁⁻¹[N] are disjoint. For suppose on the contrary that N ∩ h₁⁻¹[N] ≠ ∅. Then
   > since no element Y of the decomposition of N has the property that h₁⁻¹[Y] contains N, the
   > point c belongs to R(E).

   The p. 342 remark it rests on,
   > Note that if F is an element of the set F of extensions of E away from X, then the
   > decomposition of F is a continuous collection (Lemma 5) that has the decomposition of E as a
   > subcollection,

   is now proved: continuity is `hagopian76_lemma5`, and "subcollection" is item A applied to `K ⊆ N`
   (the layers of `N` meeting `K` are layers of `K`). So step 6 is no longer blocked. Steps 1–8 are
   **true as far as checked; not formalized** (report §1.C lists what each needs).
4. **pp. 343–344, Lemma 7:**
   > By Lemma 2, an integer i and a homeomorphism f of M onto M exist such that a continuum F
   > essential to fhᵢ[R(E)] contains u, misses t, and intersects A.

   > Note that g[F] ∪ Hⱼ is a triod in M.

   Unchanged from batch 157, check 6: unargued details using Lemma 6 (open) and the type A′ structure
   of essential continua (Lemma 5 is proved; the containment in one extension follows from step 5 of
   Lemma 6). **Unargued; depends on Lemma 6; open.**
5. **p. 344, Lemma 9:**
   > We assume without loss of generality that π[E] is lying on a horizontal line B in R² and π[I − {y}]
   > is below B on a vertical line.

   Needs a homeomorphism of the plane straightening the arc `π[E]` (and then the arc `π[I]`). Moore
   1919 and F.A. in the repository do not state it for the plane (Moore 1919's Schoenflies-type
   theorem `m19_schoenflies` is for his abstract spaces and simple closed curves). **Unargued
   (standard but not available); open.**

   > Let G = {G₁, G₂, G₃} be a chain in R² that follows E such that (1) for i = 1, 2, and 3, Hᵢ ⊂ Gᵢ,
   > each point of Gᵢ is within ε of Hᵢ, and π[Gᵢ] is an open disk, and (2) for i = 1 and 2,
   > π[Gᵢ] ∩ π[Gᵢ₊₁] is an open disk.

   Saturated open sets have open images under the quotient map `π`; that the images can be taken to
   be open disks with disk intersections is unargued (it needs the plane Schoenflies theorem). **Unargued;
   open.**

   > Note that I intersects Bd G₂ and misses Cl (G₁ ∪ G₃).

   From the choice of `ε`: points of `G₁ ∪ G₃` are within `ε` of `H₁ ∪ H₃`, and `ρ(I, H₁ ∪ H₃) ≥ 3ε`;
   `I` is connected, contains `y ∈ Y ⊆ H₂ ⊆ G₂` and `x` with `ρ(x, E) ≥ 3ε`, so `x ∉ G₂`. **True;
   supplied detail.**

   > Since M is atriodic and h(u) is not in E, the sets G₂ ∩ E and G₂ ∩ h[E] are disjoint.

   Uses atriodicity (Lemma 1) and the smallness of `h`; the triod is not written out by Hagopian and
   was not checked in detail here. **Unargued detail; not formalized.**

   > Since L is free relative to M and π[C ∪ I] ∩ πh[Cl G₃] = ∅, this is impossible [13, Theorem 28,
   > p. 156].

   Moore 1962 Theorem 28 is proved (`moore62_theorem28`; the excerpt of Moore's proof is incomplete,
   so another route is used: an exterior arc, the θ-curve sides, and Janiszewski's theorem). Its application
   here (to the simple domain bounded by a curve built from `π[E]`, `π[I]` and the boundary of
   `π[G₂]`) was not formalized. **Citation: the cited theorem is true (proved); its application open.**
6. **p. 347:**
   > Let e be the point of [0, 1] such that d⁻¹[[0, e]] = E.

   The strong form of item A (`hagopian76_initial_segment`). **True; supplied (batch-157 check 9
   closed).**

No statement of Hagopian's is refuted. D1 is closed in the strong form (check 1), Lemma 5 is proved
(check 2), the cited Theorem 28 of Moore is proved (check 5), and check 9 of batch 157 is closed
(check 6). Lemmas 6, 7 and 9 remain open. No defective proof is added; the count stays at fourteen.


### Hagopian 1976 IV: Lemma 6, Lemma 7; plane Schoenflies and collars; Lemma 9 (batch 159)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76D.lean` and four new supporting files
under `HPC/Hagopian/` (`doc/batches/REPORT-batch159.md`): `H76Schoen` (the plane Schoenflies
theorem with one side prescribed; the cross-cut theorem in the plane), `H76Invert` (half-collars on
the two sides of a simple closed curve, the unbounded one by an inversion), `H76Collar`
(accessibility at a non-cut point; every arc lies on a simple closed curve; the two-sided collar),
`H76Lemma8Caps` (Lemma 8 with prescribed caps). Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 IV (batch 159)* of `Axioms.lean` / `axioms.txt`, standard axioms
  only; the audit of the new theorems is `doc/batches/audits/axioms-batch159.txt`.
* **Source.** Hagopian 1976, pp. 342–346 (`doc/sources/hagopian1976.pdf`); Bing 1960, p. 215
  (`doc/sources/bing1960.pdf`); Moore 1919 (`m19_schoenflies_boundary_proof`, `split_interior_of`).
* **Outcome.** **Proved:** `plane_schoenflies`, `exists_collar`, `hagopian76_lemma8_caps` (shape
  chosen); supporting: `plane_split`, `TArc.exists_closing_arc`, `accessible_of_noncut`,
  `isHalfCollar_bounded`, `isHalfCollar_unbounded`. **Open**, commented out with the obstruction in
  `OPEN.md` (batch-159 section): Lemma 6 and the two unnumbered claims, Lemma 7, Lemma 9 (collar form).
  **Refuted:** nothing.

**Checks.**

1. **pp. 342–343, Lemma 6, steps 1–8.** Not formalized in this batch; the sentences, with the outcome
   of the informal check:
   1. > Assume without loss of generality that X intersects B. Since E is irreducible and M is
      > hereditarily unicoherent, and since X does not have interior relative to E, it follows that B
      > contains X.

      True (Lemma 1 and the boundary of `X` in `E`); as in batch 157, check 4. **True; not formalized.**
   2. > The sets X and C are disjoint. For suppose on the contrary that X intersects C. Then C contains
      > X. Let H be an element of F such that H ∩ (B − C) ≠ ∅ ≠ H ∩ (C − B). Since B ∩ H and C ∩ H are
      > continua, this violates the irreducibility of H.

      True, given that some extension meets both `B − C` and `C − B` (they are open in
      `Cl R(X, E)` and `R(X, E)` is dense). **True; not formalized.**
   3. > Let K be an element of F that meets C − B. Note that B − C is contained in K.

      Unargued; follows from the irreducibility of `K` and step 2 as in the previous sentence.
      **Unargued; true as far as checked.**
   4. > Since M is second countable, there exists a monotone strictly increasing sequence {Fᵢ} of
      > elements of F such that R(X, E) = ⋃ Fᵢ (Lemma 4).

      Needs that the extensions away from `X` are linearly ordered by inclusion; batch 158 gives that
      `E` is an initial segment of each, not the comparison of two extensions. **Unargued step;
      open.**
   5. > The point c belongs to Cl R(X, E) − R(X, E). … Since M is hereditarily unicoherent and f[L]
      > contains zᵢ and misses w, and since Fᵢ is irreducible, the sets L and f[L] are disjoint. Since
      > M is atriodic, it follows that f[L] is a subset of R(X, E).

      Step 5. The `δ`-homeomorphism is Lemma 2 (proved). The two conclusions are one-sentence triod
      arguments; the first needs `L ∩ f[L] ≠ ∅ ⇒ L ∪ f[L] ⊆ Fᵢ`-type containment, which again uses the
      linear order of extensions. **Unargued details; open.**
   6. > The sets N and h₁⁻¹[N] are disjoint.

      Its "subcollection" premise is item A of batch 158 (proved). **True as far as checked; not
      formalized.**
   7. > Thus C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P] is a triod, and this is a contradiction of Lemma 1.

      **Not checked in detail; not formalized.**
   8. > By Lemma 2, there exist homeomorphisms f₁ and f₂ of M onto M near the identity such that
      > Q ∪ f₁[Q] ∪ f₂[Q] ∪ Cl R(X, E) is a triod (see the second paragraph in the proof of Theorem 1
      > of [5]).

      **Citation of the 1975 ¶2 triod; not formalized.**
2. **p. 343, the unnumbered claims:**
   > Since M is atriodic, R(E) is a composant of Cl R(E). … Note that every continuum essential to
   > R(E) is of type A′ (Lemma 5).

   The second needs that an essential continuum lies in one extension (unargued; it follows from step
   5, report 158 §1.C), after which `isTypeA'_of_subcontinuum` with Lemma 5 applies. The first uses
   Lemma 6. **Unargued (containment); open.**
3. **pp. 343–344, Lemma 7:**
   > By Lemma 2, an integer i and a homeomorphism f of M onto M exist such that a continuum F
   > essential to fhᵢ[R(E)] contains u, misses t, and intersects A.

   > Note that g[F] ∪ Hⱼ is a triod in M.

   Unchanged from batch 158, check 4. **Unargued; depends on Lemma 6; open.**
4. **p. 344, decomposably accessible:**
   > Distinct elements U and Y of the decomposition of E that are not end sets are said to be
   > decomposably accessible from a side of E if there exist arc segments A and B in R² − π[M] such
   > that (1) π[U] ∈ Cl A, (2) π[Y] ∈ Cl B, and (3) Cl A and Cl B abut on the same side of the arc
   > π[E] in R² [2, p. 215].

   *Collar form* (`DecompAccessibleC`): for some collar `F` of the arc `γ = π[E]` and some side `σ`,
   the vertical segments `F({u} × σ(0, h₁])`, `F({y} × σ(0, h₂])` miss `π[M]`. *Comparison:* the collar
   form implies Bing's (the two vertical segments are arc segments with the required closures; a
   homeomorphism of the plane extending the collar coordinates, which Bing's definition asks for,
   exists by Schoenflies applied to the two sides of the θ-curve built in `exists_collar_aux` and the
   Schoenflies extension to the outside, not formalized); Bing's implies the collar form after
   re-choosing the collar so that `Cl A`, `Cl B` become vertical near their ends (Schoenflies applied to
   the quadrilaterals cut off by `A`, `B`; not formalized). Every arc has a collar (`exists_collar`,
   proved). **Definition recorded in collar form; the equivalence with Bing's form is not
   formalized.**
5. **pp. 344–345, Lemma 9:**
   > We assume without loss of generality that π[E] is lying on a horizontal line B in R² and π[I − {y}]
   > is below B on a vertical line.

   The first half is now available: the collar of `γ` (`exists_collar`) puts `π[E]` on the horizontal
   axis with an open neighbourhood. The second half needs Schoenflies with two sides prescribed (the
   collar does not prescribe a second arc). **Unargued (Schoenflies, unstated); first half supplied.**

   > Let G = {G₁, G₂, G₃} be a chain in R² that follows E such that (1) for i = 1, 2, and 3, Hᵢ ⊂ Gᵢ,
   > each point of Gᵢ is within ε of Hᵢ, and π[Gᵢ] is an open disk, and (2) for i = 1 and 2,
   > π[Gᵢ] ∩ π[Gᵢ₊₁] is an open disk.

   In collar coordinates the `π[Gᵢ]` can be taken as open rectangles about the three thirds of
   `[0, 1] × {0}` (their pairwise intersections rectangles); that their preimages are within `ε` of the
   `Hᵢ` needs upper semicontinuity of the decomposition in metric form. **Unargued; supplied in outline;
   not formalized.**

   > Note that I intersects Bd G₂ and misses Cl (G₁ ∪ G₃).

   As in batch 158, check 5. **True; supplied detail.**

   > Since L is free relative to M and π[C ∪ I] ∩ πh[Cl G₃] = ∅, this is impossible [13, Theorem 28,
   > p. 156].

   *Configuration (as far as reconstructed):* the simple domain is `π[L₂]` (or `π[G₂]`), its boundary
   curve `J`; the two disjoint continua are `π[C] ∪ π[I]` (meeting `J` where `π[E]` leaves `π[G₂]`
   towards `G₁` and where `π[I]` crosses `Bd π[G₂]`) and `πh[D]` (meeting `J` where it leaves towards
   `G₃` and at the bottom, through the vertical segment `A`); the freeness of `L` puts the points of
   `M ∩ Bd St L` in `Cl (L₁ ∪ L₃)`, which forces the four boundary points into the interlaced order
   that Theorem 28 forbids. Hagopian does not name the four points. Moreover `L₂ = C ∩ G₂` after
   Lemma 8, and `π[L₂]` need not be a disk, while Theorem 28 is stated for simple domains. **Citation:
   the theorem is true (proved, batch 158); its application unargued in detail; open.**
6. **p. 346, Lemma 8 with caps:**
   > Using the method described in the proof of Lemma 8, we define an ordered refinement … (Here the
   > open sets A and B in the proof of Lemma 8 are in G₁ − G₂ and G₁₁ − G₁₀ respectively.)

   The method works with caps inside any open `U ⊆ G₀`, `V ⊆ Gₙ` containing the end sets
   (`hagopian76_lemma8_caps`): the only properties of `A`, `B` used are that `E` is a component of
   `M − (A ∪ B)` (from the caps lemma, which needs `X ⊆ U`, `Z ⊆ V`) and that `A ∪ B ⊆ G₀ ∪ Gₙ`. For
   `A ⊆ G₁ − G₂` (1-indexed) the end set `X` must lie in `G₁ − Cl G₂`; in the setting of p. 346 this
   holds when the chain is chosen fine enough. **True; proved in the chosen shape.**

No statement of Hagopian's is refuted. The plane Schoenflies theorem and the collar (the unstated
plane topology behind "we assume without loss of generality …", pp. 345, 346) are proved; Lemmas 6,
7 and 9 remain open. No defective proof is added; the count stays at fourteen.

### Hagopian 1976 V: Lemma 6 in full, Lemma 7; two-sided Schoenflies; Lemma 9 (batch 160)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76E.lean` and seven new supporting files
under `HPC/Hagopian/` (`doc/batches/REPORT-batch160.md`): `H76USC` (upper semicontinuity in metric
form), `H76Schoen2` (Schoenflies with two adjacent sides prescribed), `H76Absorb` (absorption: a
continuum missing `X` that meets an extension away from `X` lies in `R(X, E)`), `H76Lemma6` (steps
1–5), `H76Step8` (step 8 and Lemma 6), `H76Composant` (`R(E)` is a composant), `H76Essential`
(essential continua are of type A′). Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 V (batch 160)* of `Axioms.lean` / `axioms.txt`, standard axioms
  only; the audit of the new theorems is `doc/batches/audits/axioms-batch160.txt`.
* **Source.** Hagopian 1976, pp. 342–345 (`doc/sources/hagopian1976.pdf`); Hagopian 1975, proof of
  Theorem 1, second paragraph (`hagopian75_no_indecomposable_interior`); Moore 1919
  (`m19_schoenflies_boundary_proof`).
* **Outcome.** **Proved:** `hagopian76_lemma6_X`, `hagopian76_closure_extUnion`, `hagopian76_lemma6`,
  `hagopian76_Rset_composant`, `hagopian76_essential_typeA'`, `layer_nbhd_small`,
  `plane_schoenflies₂`, all in the skeleton's shapes. **Open**, commented out with the obstruction in
  `OPEN.md` (batch-160 section): Lemma 7, Lemma 9. **Refuted:** nothing.

**Checks.**

1. **pp. 342–343, Lemma 6, steps 1–8.**
   1. > Assume without loss of generality that X intersects B. Since E is irreducible and M is
      > hereditarily unicoherent, and since X does not have interior relative to E, it follows that B
      > contains X.

      As printed the first sentence is a normalization that the second does not need: the formal
      step (`lemma6_step1`) shows that one of `B`, `C` contains `X`. `E ∩ B`, `E ∩ C` are continua
      (Lemma 1) with union `E`; if `E ∩ B ⊆ X` then `E ∩ C ⊇ E − X`, dense in `E`, so `E ⊆ C`;
      otherwise `E ∩ B` meets `X` and another layer and contains `X` (the interval lemma at `0`,
      `layer_zero_subset_of_meets`). **True; proved.**
   2. > The sets X and C are disjoint. For suppose on the contrary that X intersects C. Then C contains
      > X. Let H be an element of F such that H ∩ (B − C) ≠ ∅ ≠ H ∩ (C − B). Since B ∩ H and C ∩ H are
      > continua, this violates the irreducibility of H.

      `H` exists because `B − C`, `C − B` are open in `Cl R(X, E)` and `R(X, E)` is the increasing
      union of the `Fᵢ`; the one of `H ∩ B`, `H ∩ C` meeting the far end layer of `H` is `H`
      (`subset_of_meets_ends`). **True; proved (`lemma6_step2`).**
   3. > Let K be an element of F that meets C − B. Note that B − C is contained in K.

      Unargued. Proved in the stronger form `Cl R(X, E) − C ⊆ K` (`lemma6_step3`): for `w ∈ Fⱼ ⊋ K`
      outside `C`, `Fⱼ ∩ B` is an initial segment of `Fⱼ` not reaching the points of `K` in `C − B`.
      **Unargued; true; proved.**
   4. > Since M is second countable, there exists a monotone strictly increasing sequence {Fᵢ} of
      > elements of F such that R(X, E) = ⋃ Fᵢ (Lemma 4).

      `hagopian76_lemma4_seq` (batch 156). `K ⊆ Fᵢ` for large `i`, and the far ends `zᵢ` then lie
      in `C`. **True; proved (`lemma6_main`).**
   5. > The point c belongs to Cl R(X, E) − R(X, E). … Since M is hereditarily unicoherent and f[L]
      > contains zᵢ and misses w, and since Fᵢ is irreducible, the sets L and f[L] are disjoint. Since
      > M is atriodic, it follows that f[L] is a subset of R(X, E).

      Both sentences hold. The second is an instance of *absorption* (`subset_extUnion_of_meets`): a
      continuum that misses `X` and meets an extension away from `X` lies in `R(X, E)` (an
      irreducible continuum from `X` to a point of it inside the union contains the extension, by
      atriodicity applied to three continua through a common point, and is itself an extension).
      **Unargued; true; proved (`lemma6_main`).** Absorption applied to `C` itself (which misses `X`
      by step 2 and meets `K`) gives `C ⊆ R(X, E)`, so the limit point `c ∈ C` lies in `R(X, E)` and
      step 5 already yields the contradiction.
   6. > Then since no element Y of the decomposition of N has the property that h₁⁻¹[Y] contains N,
      > the point c belongs to R(E).

      **Not needed** (see step 5): steps 6–7 derive a contradiction from `c ∉ R(X, E)`, which is
      impossible once `C ⊆ R(X, E)`. Not checked further; not formalized.
   7. > Thus C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P] is a triod, and this is a contradiction of Lemma 1.

      **Not needed**, as step 6.
   8. > By Lemma 2, there exist homeomorphisms f₁ and f₂ of M onto M near the identity such that
      > Q ∪ f₁[Q] ∪ f₂[Q] ∪ Cl R(X, E) is a triod (see the second paragraph in the proof of Theorem 1
      > of [5]).

      Proved without homeomorphisms (`closure_extUnion_aux`): if an extension `Q` away from `Z` is not
      inside `I = Cl R(X, E)`, either `I ⊆ Q` (then `I` meets two layers of `Q` and is decomposable,
      `false_of_indec_subset_layers`) or an irreducible continuum from a point of `I` outside every
      proper subcontinuum through `X` to a point of `Q − I` contains `I` with interior, against
      `hagopian75_no_indecomposable_interior` (the cited paragraph). **Citation correct; proved by a
      different route.**
2. **p. 343, the unnumbered claims:**
   > Since M is atriodic, R(E) is a composant of Cl R(E).

   Unargued. Proved (`Rset_composant_aux`): a proper subcontinuum `P` of `Cl R(E)` through a point of
   an extension `F` gives the proper subcontinuum `A = P ∪ F ⊇ E`; extensions `K`, `Q` away from `X`,
   `Z` not inside `A` exist (step 8); of the three continua `A`, `K`, `Q` through a point of `X` one
   lies in the union of the others (atriodicity), and since `K ∩ Q ⊆ E` (`ext_inter_subset`) it is
   `A`. **Unargued; true; proved.**

   > Note that every continuum essential to R(E) is of type A′ (Lemma 5).

   Unargued. The containment of report 158 §1.C (a continuum `G ⊆ R(X, E)` lies in one extension) is
   `exists_ext_of_subset`; it uses that `R(X, E)` is not closed (from Lemma 6 and the composant
   argument), **not** the point `c` of step 5. An essential continuum inside one side is then of type
   A′ by `isTypeA'_of_subcontinuum` and Lemma 5; one meeting both sides contains `E`, its two halves
   lie in single extensions `K`, `Q` (`exists_ext_cover`), and it is irreducible between their
   farthest points, decomposable, and of type A′ (`essential_typeA'_two_sided`). **Unargued; true;
   proved.**
3. **pp. 343–344, Lemma 7:**
   > By Lemma 2, an integer i and a homeomorphism f of M onto M exist such that a continuum F
   > essential to fhᵢ[R(E)] contains u, misses t, and intersects A.

   > Note that g[F] ∪ Hⱼ is a triod in M.

   Lemma 6 and the type A′ structure of essential continua are now available. The first sentence still
   hides a construction: `u` and `t` are limit points in `Cl R(E)` and Lemma 2 only moves single
   points; that some translate of `R(E)` contains a continuum essential to it through `u`, missing
   `t`, meeting `A = {x ∈ M : ρ(x, p) < ε/4}` is not argued. The second
   sentence needs the arms of the triod (`g[F]` from `uⱼ` to `A`, and the two parts of `Hⱼ` from
   `uⱼ` to `Tⱼ` and `Vⱼ`), unargued. **Unargued; open.**
4. **pp. 344–345, Lemma 9:**
   > We assume without loss of generality that π[E] is lying on a horizontal line B in R² and π[I − {y}]
   > is below B on a vertical line.

   Both inputs named in batch 159 are now proved: Schoenflies with two adjacent sides prescribed
   (`plane_schoenflies₂`, directly from Moore's four-sided form, no reparametrization of the square) and
   upper semicontinuity in metric form (`layer_nbhd_small`). **Unargued; inputs supplied.**

   > Since L is free relative to M and π[C ∪ I] ∩ πh[Cl G₃] = ∅, this is impossible [13, Theorem 28,
   > p. 156].

   The chain of discs and the application of Theorem 28 are not formalized; the configuration is as
   reconstructed in batch 159, check 5. **Open.**

No statement of Hagopian's is refuted. Lemma 6 and the two unnumbered claims are proved; steps 6–7
of Lemma 6 are superfluous (absorption). No defective proof is added; the count stays at fourteen.

### Hagopian 1976 VI: Theorem 1 set-up (`ε₁`, the chain, Property 1, T9, Property 3, T11); Lemma 7; Lemma 9 (batch 161)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76F.lean` and six new supporting files
under `HPC/Hagopian/` (`doc/batches/REPORT-batch161.md`): `H76Eps1` (the elevenths, `IsEps1`),
`H76Lemma8Sep` (Lemma 8 with caps, exposing Moore's open sets `C`, `D`), `H76Prop1` (`Wₓ`, `Gₓ`, the
chain `{Gᵢ}`, `L`, Property 1), `H76T9` (T9, first sentence), `H76Lemma7` (the triod of Lemma 7 and
the reduction to the existence of `F`), `H76Prop3` (the step "By Lemmas 2 and 3" of Property 3).
Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 VI (batch 161)* of `Axioms.lean` / `axioms.txt`, standard axioms
  only; the audit of the new theorems is `doc/batches/audits/axioms-batch161.txt`.
* **Source.** Hagopian 1976, pp. 343–348 (`doc/sources/hagopian1976.pdf`).
* **Outcome.** **Proved:** `hagopian76_eps1`, `hagopian76_eps1_chain`, `exists_Gset`,
  `hagopian76_chain11`, `hagopian76_property1`. **Partly proved:** `hagopian76_T9` (first sentence,
  for any `D` with property (D)), `hagopian76_property3_shift` (one step of Property 3),
  `hagopian76_lemma7_triod` and `hagopian76_lemma7_of_F` (Lemma 7 reduced to `u`, `t` in one
  composant of `Cl R(E)`). **Open**, commented out with the obstruction in `OPEN.md` (batch-161
  section): T11, Property 3, Lemma 7, Lemma 9. **Refuted:** nothing.

**Checks.**

1. **pp. 345–346, `ε₁`:**
   > Define ε₁ to be one-third the minimum of the union of {ρ(Aᵢ, Bᵢ) : 1 ≤ i ≤ 5},
   > {ρ(E, π⁻¹(qᵢ)) : 1 ≤ i ≤ 5}, {ρ(k⁻¹(0) ∪ k⁻¹(1), k⁻¹[[1/11, 10/11]])}, and …

   Use by the later steps, as formalized: the third family (`IsEps1.ends`) is used by Property 1 (the
   caps `U = G₁ − Cl G₂`, `V = G₁₁ − Cl G₁₀` contain the end sets) and by T9 (`Cl B` misses
   `h[k⁻¹(0) ∪ k⁻¹(1)]`). The families `ρ(Aᵢ, Bᵢ)` and `ρ(E, π⁻¹(qᵢ))` concern the verticals of the
   collar picture and are meant for T11 and Property 3 (both open); no step proved here uses them.
   The chain of check 2 needs a family that is **not** in the list: non-adjacent elevenths at distance
   `≥ 4ε₁` (`IsEps1.sep`). **True with one added family; `ε₁` exists (`exists_isEps1`).**
2. **p. 346, the chain of `ε₁`-neighbourhoods:**
   > Note that if h is an ε₁-homeomorphism of M onto M, then the chain formed by taking
   > ε₁-neighborhoods in R² of the elements of {k⁻¹[[(i − 1)/11, i/11]] : 1 ≤ i ≤ 11} follows h[E].

   Unargued. The four printed families do not imply that these neighbourhoods form a chain:
   `ρ(Aᵢ, Bᵢ)` only measures distances from the five verticals, and nothing bounds
   `ρ(k⁻¹[[0, 1/11]], k⁻¹[[2/11, 3/11]])` from below. With the family `IsEps1.sep` the sentence is
   proved (`hagopian76_eps1_chain`, from `follows_of_elev`: a chain of eleven links follows a type A′
   continuum when its `i`-th eleventh lies in the `i`-th link). **Unargued; does not follow from the
   printed `ε₁`; true after shrinking `ε₁`; proved.** Not counted as a defective proof: the repair is a
   smaller `ε₁`, and no later step depends on the exact value.
3. **p. 346, Property 1:**
   > PROPERTY 1. For each point y of M ∩ ⋃{Lᵢ : 2 ≤ i ≤ 10}, there exists an ε₁-homeomorphism h of M
   > onto M such that y belongs to h[E] and L follows h[E]. (Here the open sets A and B in the proof
   > of Lemma 8 are in G₁ − G₂ and G₁₁ − G₁₀ respectively.)

   Unargued ("Using the method described in the proof of Lemma 8"). Proved (`property1_aux`): `y ∈ Gₓ`
   for some `x` of the `i`-th eleventh, so `h(x) = y` for an `ε₁`-homeomorphism `h`; `h[piece j] ⊆ Gⱼ`
   for every `j` (`Gₓ' ∋ h(x')`); `h[k⁻¹[[1/11, 10/11]]]` is connected, misses the caps (they lie in
   `G₁ − G₂`, `G₁₁ − G₁₀`, which is where the parenthesis is used), and meets Moore's set `C` at `y`;
   since `M − (A ∪ B) ⊆ C ∪ D` with `C ∩ D = ∅` it lies in `C`, so `h[piece j] ⊆ Lⱼ` for all `j`. Uses
   the Lemma-8 set `D`, which the batch-159 statement did not return (`lemma8_caps_sep`). **Unargued;
   true; proved.**
4. **p. 346, T9:**
   > Since M is atriodic, it follows from Property 1 and Lemma 5 that Cl B is the image of a
   > subcontinuum of E (essential to R(E)) under an ε₁-homeomorphism. Note that the chain
   > L − {L₁, L₁₁} follows Cl B.

   The containment is proved (`T9_aux`) for any open `O` such that every point of `M ∩ Cl O` lies in
   `L₂ ∪ … ∪ L₁₀`: `Cl B` misses `h[k⁻¹(0) ∪ k⁻¹(1)]` (third family of `ε₁`) and meets `h[E]`, so lies
   in `h[E]` by the 1975 ¶9 triod (`subset_of_meets_avoids`); Lemma 5 is not needed for this. That
   `h⁻¹[Cl B]` is *essential* needs it to meet two layers of `E`; proved when `Cl B` meets links `Lₐ`,
   `L_c` with `c ≥ a + 3`. That `Cl B` reaches such links, and the second sentence, depend on `D`
   (T8). **Unargued; first sentence true (for `D` with the stated property); remainder open.**
5. **p. 347, T11:**
   > Note that K separates L₂ ∩ M ∩ π⁻¹[D] from L₁₀ ∩ M ∩ π⁻¹[D] in π⁻¹[D].

   Unargued. That the cross-cut `K` separates `π⁻¹[D]` is the cross-cut theorem (`π` is a
   homeomorphism off `E`). That `L₂ ∩ π⁻¹[D]` and `L₁₀ ∩ π⁻¹[D]` lie on *opposite sides* is not
   implied by the printed `ε₁`: `ρ(A₃, B₃) ≥ 3ε₁` keeps `G₂` and `G₁₀` away from `A₃ ⊇ K`, but the
   sets `Gₓ` are not connected and the side of each point is not controlled. **Unargued; open.**
6. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)]. By Lemma 1 and Property 1, L follows a type A′
   > continuum in d⁻¹(v) that meets L₆ ∩ π⁻¹[D]. By Lemmas 2 and 3, a homeomorphism g of M onto M and
   > a point u of [0, v) exist such that gd⁻¹(v) = d⁻¹(u) and d⁻¹(u) contains a component of
   > F ∩ π⁻¹[D] whose closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)].

   (a) "first point": the set of such `v` is not shown to be closed; **unargued, open**. (b) "By
   Lemma 1 and Property 1": this is the first sentence of T9 applied to the closure of the component
   (check 4). (c) "By Lemmas 2 and 3, … `gd⁻¹(v) = d⁻¹(u)`": **true; proved** for every interior
   layer and every `δ > 0`, with `u ∈ (0, v)` (`layer_shift`; Lemma 5 supplies the nearby earlier
   layer, Lemma 2 the homeomorphism, Lemma 3 the equality). (d) "and `d⁻¹(u)` contains a component …
   whose closure meets [both verticals]": a crossing property of `D` under small homeomorphisms;
   **unargued, open**.
7. **pp. 343–344, Lemma 7:**
   > By Lemma 2, an integer i and a homeomorphism f of M onto M exist such that a continuum F essential
   > to fhᵢ[R(E)] contains u, misses t, and intersects A.

   > Note that g[F] ∪ Hⱼ is a triod in M.

   The second sentence is **true; proved** (`lemma7_triod`), with arms taken at the layer of `uⱼ`:
   `d⁻¹[[0, c]]`, `d⁻¹[[c, 1]]` (`c = d(uⱼ)`, `0 < c < 1` since `ρ(Tⱼ, Uⱼ) > ε` and `ρ(Tⱼ, Vⱼ) < ε`),
   and `g[F]`, against `three_continua`; the case where `g[F] ∩ Hⱼ` reaches an end layer needs no
   separate treatment. The commission's reading of §1 (choice of `ε′`, `j`, and that `g[F]` misses
   `tⱼ`, `vⱼ` and meets `B`) is confirmed and formalized (`lemma7_of_F`: Lemma 7 follows from the
   existence of `F` for limit points `p`, `u ≠ t` of `Cl R(E)`). Neither the essentiality of `F` nor
   its position in a translate of `R(E)` is used. The first sentence: `F` exists when `u`, `t` lie in
   different composants of `Cl R(E)` (`exists_F_of_not_mem_composant`, boundary bumping); **open**
   when they lie in one composant. Note that any continuum through `uⱼ` not inside `Hⱼ` contains `Tⱼ`
   or `Vⱼ` (the triod), so `F` cannot be found near the `Hⱼ`. **Unargued; second sentence proved;
   first sentence open in one case.**
8. **pp. 344–345, Lemma 9, the Theorem 28 configuration:**
   > Note that πh[D] contains πh(u), intersects π[G₃], and misses π[C ∪ I ∪ Cl G₁]. Since L is free
   > relative to M and π[C ∪ I] ∩ πh[Cl G₃] = ∅, this is impossible [13, Theorem 28, p. 156].

   Checked against the text, not formalized. The cyclic order `a₁, b₂, a₂, b₁` on `Bd π[G₂]` (report
   160 §1.E) is right (with `U = k⁻¹(1/3)`, `Y = k⁻¹(1/2)`: `b₂` at abscissa `1/3`, `a₂` at `1/2`).
   Two corrections: the continuum through `b₁`, `b₂` is `πh[D]` *with the segment of `A` from `πh(u)`
   down to the bottom side* (it misses `π[C ∪ I]`: below the axis, at a different abscissa from
   `π[I]`), and the exit point `b₁` is a point of `Cl π[L₃]` reached by `πh[D]` (freeness: `h[D]`
   leaves `St L` only through `Cl (L₁ ∪ L₃)`, and it misses `Cl G₁`), which lies on the right side of
   `π[G₂]` only when the links are collar rectangles. **Configuration confirmed with two corrections;
   open.**

No statement of Hagopian's is refuted. The chain sentence of p. 346 does not follow from the printed
`ε₁` and is repaired by one more family; this is not counted as a defective proof. The count stays at
fourteen.

### Hagopian 1976 VII: Lemma 7 by half-ray density; Lemma 9; T6–T9, T11, Property 3 (batch 162)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76G.lean` and two new supporting files
under `HPC/Hagopian/` (`doc/batches/REPORT-batch162.md`): `H76HalfRay` (end layers of pieces,
`Cl R(G) = Cl R(E)` for essential `G`, the two half-rays: separation and density) and `H76Lemma7Ray`
(the continuum `F`, and Lemma 7). Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 VII (batch 162)* of `Axioms.lean` / `axioms.txt`, standard axioms
  only; the audit of the new theorems is `doc/batches/audits/axioms-batch162.txt`.
* **Source.** Hagopian 1976, pp. 343–347 (`doc/sources/hagopian1976.pdf`).
* **Outcome.** **Proved:** `halfray_dense`, `halfray_inter`, `hagopian76_lemma7`, and (outside the
  batch's items) T10, Property 2 (`hagopian76_property2`, "By Lemma 7, there exists a positive number
  ε₃ less than ε₂ …": immediate from Lemma 7). **Open**,
  commented out with the obstruction in `OPEN.md` (batch-162 section): Lemma 9, T6, T7, T8, T9 in
  full, T11, Property 3. **Refuted:** nothing.

**Checks.**

1. **pp. 343–344, Lemma 7:**
   > By Lemma 2, an integer i and a homeomorphism f of M onto M exist such that a continuum F essential
   > to fhᵢ[R(E)] contains u, misses t, and intersects A.

   Unargued; **true; proved** (`lemma7_aux`, `hagopian76_lemma7`) by the commission's steps 1–5:
   (1) Lemma 2 gives `f` (here `g⁻¹`) with `f(uᵢ) = u` and small displacement, `i` large; (2)
   `hᵢ⁻¹(f⁻¹(t))` is off the layer `hᵢ⁻¹[Uᵢ]`, since `ρ(tᵢ, Uᵢ) > ε` while `ρ(t, tᵢ) < ε/2` and `f`
   moves points less than `ε/12`; (3) the extensions of the two halves `d⁻¹[[0, c]]`, `d⁻¹[[c, 1]]` of
   `hᵢ⁻¹[Hᵢ]` away from the layer `d⁻¹(c)` meet only in that layer (`halfray_inter_subset`: if a
   point off the layer were in both, the continuum `K₊ ∩ K₋` would contain points of `d⁻¹((c, 1])`
   lying in `K₋ ∩ G ⊆ d⁻¹[[0, c]]`), so one of the two half-rays misses that point; (4) each half-ray
   is dense in `Cl R(E)` (`halfray_dense_aux`), so one extension `K` on the good side comes within
   `ε/12` of `p`, and `F = f hᵢ[K]` meets `A`; (5) `lemma7_triod`. **Is `F` essential to `fhᵢ[R(E)]`?**
   `F` is the image under `fhᵢ` of an extension of a half of `hᵢ⁻¹[Hᵢ]` (an essential continuum); it
   is of type A′ and contains the image of that half. Whether it lies in `fhᵢ[R(E)]` and meets two
   layers of an extension of `fhᵢ[E]`, as the definition of "essential" asks, was not checked.
   **Not used:** the proof uses only `u ∈ F`, `t ∉ F`, `F ∩ A ≠ ∅`.
   `Lemma7F` (batch 161: `F` for arbitrary `u ≠ t` in one composant) is too strong and **not needed**;
   it is neither proved nor refuted (a refutation would need a model of the hypotheses, which the
   theorem being proved says does not exist).

   The proof of half-ray density writes out the commission's argument. "Both are composants of their
   closures and they share `E′`" is not by itself enough, and the formal argument goes through
   extensions instead: (a) every minimal admissible map of a piece `d⁻¹[[a, b]]` has end layers
   `d⁻¹(a)`, `d⁻¹(b)` (`piece_end_layers`), so `R(·)` depends only on the set (`Rset_eq_of_maps`);
   (b) if `Q ⊇ P` have the same layer over `0`, their extensions away from it coincide
   (`extUnion_eq_of_subset`, from the chain property `ext_chain`), so `Cl R(P) = Cl R(Q)` by Lemma 6,
   step 8; (c) hence `Cl R(P) = Cl R(G)` for every piece `P` of `G` (`closure_Rset_piece`), and two
   type A′ continua sharing a continuum that meets two layers of each have the same `Cl R(·)`
   (`closure_Rset_of_common`); (d) an essential `G` shares such a continuum with an extension of `E`
   (`closure_Rset_essential`): `G` itself if `G ⊆ R(X, E)` or `G ⊆ R(Z, E)` (as in
   `essential_typeA'_of_subset`), and in the two-sided case `G ∩ K` or `G ∩ Q`, one of which meets two
   layers of `G`.
2. **pp. 344–345, Lemma 9, the Theorem 28 configuration, formally:**
   > Note that πh[D] contains πh(u), intersects π[G₃], and misses π[C ∪ I ∪ Cl G₁]. Since L is free
   > relative to M and π[C ∪ I] ∩ πh[Cl G₃] = ∅, this is impossible [13, Theorem 28, p. 156].

   Not formalized. The configuration of report 161 §1.6 stands (interlacing `a₁, b₂, a₂, b₁`; the
   continuum through `b₁`, `b₂` includes the segment of `A`; the links must be collar rectangles).
   Missing: the chain of collar rectangles, its lift and a Lemma-8 refinement by rectangles, and the
   application of `moore62_theorem28`. **Open.**
3. **p. 346, T6:**
   > It follows from the proof of Lemma 9 that there exists a horizontal interval I₁ below ⟨p₁, p₅⟩ in
   > R² − π[M] such that the end points of I₁ are in ⟨o₁, p₁⟩ ∪ ⟨o₅, p₅⟩ and no point of π[M] lies
   > between I₁ and ⟨p₁, p₅⟩.

   Depends on the proof of Lemma 9 (check 2). **Open.**
4. **p. 346, T7:**
   > We find that there exists such an arc I₂ as follows. … By choosing y sufficiently close to E and h
   > sufficiently close to the identity, we get that every point of R² between ⟨p₁, p₅⟩ and a subarc of
   > π[A] irreducible between ⟨p₁, q₁⟩ and ⟨p₅, q₅⟩ belongs to π[St L].

   **Unargued.** It needs: that the accessible point `y ∈ M ∩ L₆` can be taken with `π(y)` above
   `π[E]` (a side of the collar); Property 1 at `y` (proved, `hagopian76_property1`); and that the
   Jordan domain bounded by `⟨p₁, p₅⟩`, the two verticals and the subarc of `π[A]` lies in `π[St L]`,
   which needs the links of `L` controlled in collar coordinates. **Open.**
5. **p. 346, T8, T9:**
   > Note that the chain L − {L₁, L₁₁} follows Cl B.

   Depends on `D` (T8, from T7). The first sentence of T9 is proved for any `D` with property (D)
   (batch 161, `hagopian76_T9`). **Open.**
6. **p. 347, T11:**
   > Note that K separates L₂ ∩ M ∩ π⁻¹[D] from L₁₀ ∩ M ∩ π⁻¹[D] in π⁻¹[D].

   Status as in batch 161, check 5: the sides of `K` are not controlled by the printed `ε₁`; with `D`
   in collar coordinates they would be decided by abscissae. **Unargued; open.**
7. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)].

   **Unargued.** The set of such `v` is closed only if a limit of crossing components contained in
   layers `d⁻¹(vₙ)` again yields a crossing component contained in the limit layer, which is a
   crossing property of `D`; no argument is given. "By Lemmas 2 and 3" stays proved (batch 161). **Open.**

No statement of Hagopian's is refuted, and no defective proof is added: the Lemma 7 sentence is
unargued but true by steps 1–5. The count stays at fourteen.

### Hagopian 1976 VIII: the collar geometry — an adapted collar, `no_M_below`, Lemma 9, T3, T6 (batch 163)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76H.lean` and eight new supporting files
under `HPC/Hagopian/` (`doc/batches/REPORT-batch163.md`): `H76Adapt`, `H76Rect`, `H76Glue`,
`H76AdaptHalf`, `H76AdaptMain` (the adapted collar) and `H76NoBelow`, `H76NoBelowCore`,
`H76NoBelowMain` (the general form of Lemma 9's argument). Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 VIII (batch 163)* of `Axioms.lean` / `axioms.txt`, standard axioms
  only; the audit of the new theorems is `doc/batches/audits/axioms-batch163.txt`.
* **Source.** Hagopian 1976, pp. 344–346 (`doc/sources/hagopian1976.pdf`).
* **Outcome.** **Proved:** `exists_collar_adapted` (item A), `no_M_below` (item B, both sides),
  **Lemma 9** (`hagopian76_lemma9`, item C), **T6** (`hagopian76_T6`, item D) and, added, T3 at the
  interior points (`hagopian76_T3`). **Open:** T7 (optional, not attempted), the reparametrization
  placing Hagopian's `⟨p₁, p₅⟩` away from the accessible layer, T3 at the two end points (`OPEN.md`,
  batch-163 section). **Refuted:** nothing.

**Checks.**

1. **p. 344** (the proof of Lemma 9, printed on p. 345):
   > Since M is atriodic and h(u) is not in E, the sets G₂ ∩ E and G₂ ∩ h[E] are disjoint.

   **Unargued; not used.** The argument needs only its consequence `h[D] ∩ C = ∅`, where
   `C = k⁻¹[[0, y]]` and `D = k⁻¹[[a′, 1]]`, `a′ < y` the parameter of `U`; this is proved instead
   (`no_M_below_core`, step `YC`) by the 1975 ¶9 lemma `subset_of_meets_avoids`. If a point
   `h(e) ∈ h[D]` were in `C`, then `k(e) < ζ₃` for a fixed `ζ₃ ∈ (y, 1)` (else `h(e)` is within `ε` of
   `k⁻¹[[ζ₃, 1]]`, whose `ε`-thickening misses `C`), and the continuum `P = h[k⁻¹[[a′, k(e)]]]` meets `E`
   (at `h(e)`), misses both end sets of `E` (it is within `ε` of `k⁻¹[[a′, ζ₃]]`, far from
   `k⁻¹(0) ∪ k⁻¹(1)`), hence `P ⊆ E`; but `P ∋ h(u) = z ∉ E`. This uses one more smallness condition
   on `ε` than Hagopian's list (`ρ(k⁻¹[[a′, ζ₃]], k⁻¹(0) ∪ k⁻¹(1))` and `ρ(k⁻¹[[ζ₃, 1]], C)`, the
   analogues of his `ρ(H₂, k⁻¹(0) ∪ k⁻¹(1))` and `ρ(C, H₃)`). Whether the printed sentence itself
   holds was not decided.
2. **p. 345:**
   > Since L is free relative to M and π[C ∪ I] ∩ πh[Cl G₃] = ∅, this is impossible [13, Theorem 28,
   > p. 156].

   **Replaced; the replacement is proved.** No Theorem 28 and no Jordan curve: the open collar
   rectangle `O = F((0, y) × (−c, 0))` (`IsCollar.isOpen_image`), boundary bumping
   (`exists_continuum_bump_compact`) for the component `Q` of `h[D] ∩ π⁻¹[Cl O]` through `z`, which
   exits `π⁻¹[Cl O]` because `h[D]` contains `h[k⁻¹(1)]`, far from `C`; the exit point `w` has `π(w)`
   on the bottom side at abscissa `≥ β₁` (top: `w` would be in `C`; right: the vertical misses
   `π[M]`; left and bottom-left: in `G₁`, which `h[D]` misses), so `w ∉ St L`; freeness puts a point
   of `Q ∩ Bd(St L)` in `Cl G₁ ∪ Cl G₃`, and `π⁻¹[Cl O]` misses `Cl G₃` by abscissa
   (`no_M_below_core`). The links are collar rectangles; the end links are collar rectangles together
   with a small disc about `γ 0` (resp. `γ 1`), so that they are open and contain the end layers
   (`chain3_follows`). **Hagopian's Theorem 28 route as printed:** not checked further. The cited
   theorem is true (`moore62_theorem28`, batch 158); its application needs the configuration of report
   161 §1.6 (interlaced boundary points of a disc link), which the printed refinement `L` (Lemma 8
   refines `G₂` to `C′ ∩ G₂`) does not supply. Not decided whether the printed route can be completed.

   Two further changes in the formal argument: the point `z ∈ M − E` below `π[E]` is reached by a
   sequence rather than by compactness over `a′` (if no strip works, points of `M` over strips of
   heights `→ 0` accumulate at a point `u` of some layer `k⁻¹(a′)`, `a ≤ a′ ≤ b`; Lemma 2 at `u` gives
   `h(u) = z`; `no_M_below_left`); and the mirror side is obtained by reversing the parameter
   (`k ↦ 1 − k`, `F(x, s) ↦ F(1 − x, s)`; `no_M_below_aux`).
3. **p. 344:**
   > Let G = {G₁, G₂, G₃} be a chain in R² that follows E such that (1) for i = 1, 2, and 3, Hᵢ ⊂ Gᵢ,
   > each point of Gᵢ is within ε of Hᵢ, and π[Gᵢ] is an open disk, and (2) for i = 1 and 2,
   > π[Gᵢ] ∩ π[Gᵢ₊₁] is an open disk.

   **True for collar rectangles; the disk property is not needed.** The formal chain is
   `Gᵢ = π⁻¹[Rᵢ]` with `Rᵢ` collar rectangles (end links with a disc added); `π[Gᵢ] = Rᵢ` and
   `Rᵢ ∩ Rᵢ₊₁` are images of open rectangles under the collar embedding, hence open disks. The proof
   uses only that the `Rᵢ` are open, the chain and "follows" conditions (`chain3_follows`), and the
   `ε`-closeness through `π` (`layer_close_of_pi_close`, from upper semicontinuity).
4. **p. 345, Lemma 9's hypothesis:**
   > Assume U and Y are not decomposably accessible from a side of E.

   **Not used: Lemma 9 holds in a stronger form.** `no_M_below` gives, for any accessible interior
   layer `k⁻¹(y)` and every `[a, b] ⊆ (0, 1)` avoiding `y`, a strip below `γ([a, b])` free of `π[M]`;
   the verticals below `γ u` and `γ y` then witness decomposable accessibility (both on side
   `σ = −1`) directly, with no argument by contradiction (`hagopian76_lemma9`).
5. **p. 345, T3, and p. 346, T6:**
   > … and that each point of π[E] is an end point of an arc segment in R² − π[M] below π[E]
   > (Lemma 9).

   > It follows from the proof of Lemma 9 that there exists a horizontal interval I₁ below ⟨p₁, p₅⟩ in
   > R² − π[M] such that the end points of I₁ are in ⟨o₁, p₁⟩ ∪ ⟨o₅, p₅⟩ and no point of π[M] lies
   > between I₁ and ⟨p₁, p₅⟩.

   **True; proved from `no_M_below`** in collar coordinates: T6 as `hagopian76_T6` (for every
   `[a, b] ⊆ (0, 1)` avoiding the accessible parameter `y`; `I₁` is the bottom side of the strip), T3
   at the interior points as `hagopian76_T3`. For Hagopian's `⟨p₁, p₅⟩` (abscissae `3/22 … 19/22`) the
   accessible layer must lie outside it; the reparametrization of `k` doing this is not formalized
   (open). T3 at the two end points of `π[E]` is not covered.

No statement of Hagopian's is refuted, and no defective proof is added: the sentence of check 1 is
unargued and not used, the Theorem 28 step (check 2) is replaced. The count stays at fourteen.

### Hagopian 1976 IX: the reparametrization; T7 (the accessible point above); `ε₂` (batch 164)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76I.lean` and three new supporting files
under `HPC/Hagopian/`: `H76Reparam` (the reparametrization), `H76Above` and `H76AboveAcc` (points of
`π[M]` above `π[E]`, an accessible one, and the positivity in `ε₂`). The report is
`doc/batches/REPORT-batch164.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 IX (batch 164)* of `Axioms.lean` / `axioms.txt`, standard axioms
  only. The audit of the 33 new theorems is `doc/batches/audits/axioms-batch164.txt`.
* **Source.** Hagopian 1976, pp. 345–347 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** the reparametrization (`hagopian76_reparam`) and T6 at Hagopian's abscissae
    (`hagopian76_T6_placed`, `hagopian76_I1`).
  * **Proved:** in T7, the points of `π[M]` above `π[E]` (`M_meets_above`) and the accessible point
    `y` above (`exists_accessible_above`, `hagopian76_T7_accessible`).
  * **Proved:** the positivity in `ε₂` (`hagopian76_eps2_pos`).
  * **Open:** the arc `A` and `I₂` of T7, then T8, T9 in full, T11 and Property 3 (`OPEN.md`,
    batch-164 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 345:**
   > Since M is homogeneous, we can assume … that π[k⁻¹(i/22)] = (i, 0) for each integer i

   **True; proved** in collar form. An increasing piecewise linear homeomorphism `θ` of `[0, 1]`
   with `θ y = z` gives the minimal admissible map `θ ∘ k`, with the same layers, the same relation
   `S` (so the same `π`), `γ ∘ θ⁻¹` and the transported collar `F ∘ (θ⁻¹ × id)`
   (`hagopian76_reparam`). With `z = 1/22`, `⟨p₁, p₅⟩` sits at `[3/22, 19/22]`, away from the
   accessible layer (`hagopian76_T6_placed`). Homogeneity is not needed for this step.
2. **p. 346, T7:**
   > Let y be a point of M ∩ L₆ that is accessible from R² − M such that π(y) is above π[E]. …
   > There exists an arc A in (St L) − M to one side of h[E] that meets L₁ and L₁₁ (Lemma 9 (proof)).
   > By choosing y sufficiently close to E and h sufficiently close to the identity, we get that
   > every point of R² between ⟨p₁, p₅⟩ and a subarc of π[A] irreducible between ⟨p₁, q₁⟩ and
   > ⟨p₅, q₅⟩ belongs to π[St L].

   * **The existence of `y`: unargued in print; true, proved.**
     * In every collar window `F((a, b) × (0, c))` above an interval avoiding the accessible
       parameter, `π[M]` has points (`M_meets_above`). Otherwise the proper subcontinuum
       `k⁻¹[[a, b]]` would have interior in the indecomposable `M`.
     * The window contains `π(x)` for an accessible `x ∈ M − E` (`exists_accessible_above`). `x` is
       the first point of `π[M]` on a segment, in collar coordinates, from a point of the complement
       (`π[M]` has no interior off `π[E]`), lifted by `π`, which is an open embedding off `E`.
   * **"(Lemma 9 (proof))": right in substance, incomplete; open.** It is T6 for the type A′
     continuum `h[E]` with its own `π′` and collar. That the strip lies on the side of `h[E]` facing
     `π[E]`, and close to `π[E]`, is not argued.
   * **"By choosing `y` sufficiently close …": unargued; open.** Proposed route: `π[St L]` contains
     a collar strip over `[3/22, 19/22]` (uniform height), and `π[A]` lies in it (report 164 §1.2).
3. **p. 346, T8:**
   > Let D be the bounded complementary domain of I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩ in R².

   **Not reached** (needs `I₂`). The Jordan curve theorem is available.
4. **p. 346, T9:**
   > Note that the chain L − {L₁, L₁₁} follows Cl B.

   **Not reached** (needs `D`). Status of batch 161 unchanged.
5. **p. 346:**
   > Define ε₂ to be the minimum of ε₁ and ρ(M, π⁻¹[I₁ ∪ I₂]).

   **Positive; proved** for any closed `I` missing `π[M]` (`hagopian76_eps2_pos`: `M` is compact,
   `π⁻¹[I]` is closed and disjoint from `M`). `I₁` misses `π[M]` (`hagopian76_I1`), and `I₂` does by
   its definition. So the positivity reduces to the existence of `I₂`.
6. **p. 347, T11:**
   > Note that K separates L₂ ∩ M ∩ π⁻¹[D] from L₁₀ ∩ M ∩ π⁻¹[D] in π⁻¹[D].

   **Not reached.** The obstruction of batch 161 (the sides of `K`) stands. In collar coordinates it
   reduces to link control: `π[L₂ ∩ π⁻¹[D]]` to the left of the abscissa `7/22`, `π[L₁₀ ∩ π⁻¹[D]]`
   to the right (report 164 §1.5, §5).
7. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[⟨p₁, r⟩] and π⁻¹[⟨p₅, s⟩]. … By Lemmas 2 and 3, … This contradicts the
   > definition of v.

   * **"By Lemmas 2 and 3": proved** (batch 161, `hagopian76_property3_shift`).
   * **"The first point" and the contradiction: unargued; not reached.** A limit argument in the
     hyperspace is proposed in report 164 §1.6.

No statement of Hagopian's is refuted, and no defective proof is added. The count stays at fourteen.

### Hagopian 1976 X: T7 by a crossing argument; link control; T8, T9 in full, T11 (batch 165)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76J.lean` and five new supporting files
under `HPC/Hagopian/`: `H76Crossing` (the crossing lemma), `H76NoHair` (no hair on `E`, preimages
under `π`), `H76T7` (T7), `H76Thin` (link control) and `H76T9Full` (property (D), T9, T11). The
report is `doc/batches/REPORT-batch165.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 X (batch 165)* of `Axioms.lean` / `axioms.txt`, standard axioms
  only. The audit of the 30 new theorems is `doc/batches/audits/axioms-batch165.txt`.
* **Source.** Hagopian 1976, pp. 345–347 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** `hagopian76_no_hair`, `preimage_pi_isContinuum`, `rect_crossing`, `hagopian76_T7`.
  * **Proved:** `exists_isEps1_endCtl`, `hagopian76_link_control`, `hagopian76_T8` (property (D)),
    `hagopian76_T9_full` (without "follows `Cl B`"), `hagopian76_T11` (with `K` replaced by
    `π⁻¹[D ∩ ⟨p₃, q₃⟩]`).
  * **Open:** `D` as a Jordan domain, T11 for the single component `K`, Property 3, T12–T17 and the
    assembly (`OPEN.md`, batch-165 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 346, T7:**
   > There exists an arc A in (St L) − M to one side of h[E] that meets L₁ and L₁₁ (Lemma 9 (proof)).
   > By choosing y sufficiently close to E and h sufficiently close to the identity, we get that
   > every point of R² between ⟨p₁, p₅⟩ and a subarc of π[A] irreducible between ⟨p₁, q₁⟩ and
   > ⟨p₅, q₅⟩ belongs to π[St L].

   * **The printed route leaves the side of `h[E]` unargued** (report 164, check 164.2): unchanged.
   * **The crossing route replaces it; proved.** A continuum of `M` meeting `E` and missing both end
     sets lies in `E` (`hagopian76_no_hair`, from absorption and `ext_inter_subset`). Pulled back by
     `π` (`preimage_pi_isContinuum`), a connected part of `{z : F(z) ∈ π[M]}` joining the bottom and
     the top of a collar rectangle over `[a, b] ⊆ (0, 1)` would lie over `π[E]`, i.e. on the bottom
     edge. So the rectangle is crossed by an arc missing `π[M]` (`rect_crossing`). A thin collar
     rectangle lies in `π[St L]` because `St L` is open, contains `E`, hence is `π`-saturated, so
     `π[St L]` is open (`isOpen_pi_image`). Result: `hagopian76_T7`, in every thin enough rectangle,
     with no accessible point and no `h[E]`. Nothing is proved too much: `M_meets_above` (points of
     `π[M]` in every window) is consistent, `I₂` passes between them.
2. **p. 346, T8:**
   > Define r and s to be the end points of I₂ belonging to ⟨p₁, q₁⟩ and ⟨p₅, q₅⟩ respectively. Let
   > D be the bounded complementary domain of I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩ in R².

   **True in substance; the property used is proved, `D` itself not built.** The end points `r`, `s`
   of `hagopian76_T7` lie on the two side edges, and `I₂` meets them only there, so the four pieces
   form a simple closed curve in the closed rectangle. Its use in T9 is property (D), proved for every
   set over the thin strip (`hagopian76_T8`). The Jordan domain itself is not formalized.
3. **p. 346, T9:**
   > Since M is atriodic, it follows from Property 1 and Lemma 5 that Cl B is the image of a
   > subcontinuum of E (essential to R(E)) under an ε₁-homeomorphism. … Note that the chain
   > L − {L₁, L₁₁} follows Cl B.

   * **The first sentence: true; proved** for every connected `B` over the open strip through
     `L₂ ∪ … ∪ L₁₀` (`hagopian76_T9_full`, from `hagopian76_T9` and property (D)). In addition
     `Cl B ∩ E = ∅` (`closure_disjoint_E_of_above`, from `hagopian76_no_hair`).
   * **"follows `Cl B`": unargued; open.** It needs `Cl B` to reach both verticals.
4. **pp. 345–346, `ε₁`:**
   > Define ε₁ to be one-third the minimum of the union of {ρ(Aᵢ, Bᵢ) : 1 ≤ i ≤ 5},
   > {ρ(E, π⁻¹(qᵢ)) : 1 ≤ i ≤ 5}, {ρ(k⁻¹(0) ∪ k⁻¹(1), k⁻¹[[1/11, 10/11]])}

   **A gap; filled by `EndCtl`.** The printed `ρ(A₁, B₁)` keeps `G₁` off the vertical `⟨o₁, q₁⟩`
   but not off the region to its right; the third family and the batch-161 family `IsEps1.sep`
   separate `k⁻¹[[0, 1/11]]` from `k⁻¹[[2/11, 1]]` but not from parameters in `[3/22, 4/22]`. So
   property (D) (no point of `L₁` over the strip) does not follow from the printed families by the
   argument given. Adding `EndCtl` (`4ε₁ ≤ ρ(k⁻¹[[0, 2/22]], k⁻¹[[3/22, 1]])` and the mirror term) to
   the minimum is harmless (`exists_isEps1_endCtl`), and gives property (D)
   (`hagopian76_link_control`). Whether property (D) can fail for the printed `ε₁` was not decided.
5. **p. 347, T11:**
   > Let K be the component of π⁻¹[D ∩ ⟨p₃, q₃⟩] whose closure meets both π⁻¹(p₃) and π⁻¹[I₂].
   > Note that K separates L₂ ∩ M ∩ π⁻¹[D] from L₁₀ ∩ M ∩ π⁻¹[D] in π⁻¹[D].

   * **For the whole of `π⁻¹[D ∩ ⟨p₃, q₃⟩]`: true; proved** (`hagopian76_T11`). Link control puts
     the `π`-images of points of `L₂` over the strip left of abscissa `6/22 + η < 11/22` and those of
     `L₁₀` right of `16/22 − η`, and the strip minus the vertical is the union of two disjoint open
     sets.
   * **For the single component `K`: unargued; open.** If `I₂` crosses the vertical over `p₃`
     several times, the part of `D` above the lowest crossing may be connected to both sides around
     `K` (an `I₂` that runs right high up, back left in the middle and right again low down encloses
     such a channel). No refutation: points of `M` in the channel need not lie in `L₂` or `L₁₀`.
6. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[⟨p₁, r⟩] and π⁻¹[⟨p₅, s⟩]. … This contradicts the definition of v.

   **Not reached.** Status of batch 164 unchanged; the limit continuum of report 164 §1.6 misses `E`
   by `hagopian76_no_hair` (new), the rest is open.
7. **pp. 347–349, T12–T17:** **not reached.**

No statement of Hagopian's is refuted, and no defective proof is added. The count stays at fourteen.

### Hagopian 1976 XI: `D` as a Jordan domain; `K₀`; "follows `Cl B`"; Property 3; T12–T17 (batch 166)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76K.lean` and four new supporting files
under `HPC/Hagopian/`:
* `H76Domain`: the domain under a crossing arc;
* `H76DCollar`: `π` is closed; `D` in the plane; `K₀`;
* `H76Crosscut`: `K₀` is a cross-cut;
* `H76TwoComposants`: two composants in an open set.

The report is `doc/batches/REPORT-batch166.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XI (batch 166)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the 18 new theorems is `doc/batches/audits/axioms-batch166.txt`.
* **Source.** Hagopian 1976, pp. 346–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** `rect_domain`, `hagopian76_D`, `hagopian76_K0`, `hagopian76_K0_crosscut`,
    `exists_two_composants_in_open`.
  * **Open:** "follows `Cl B`", Property 3, T12, T13, T15–T17 and the assembly (`OPEN.md`, batch-166
    section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 346, T8:**
   > Define r and s to be the end points of I₂ belonging to ⟨p₁, q₁⟩ and ⟨p₅, q₅⟩ respectively. Let
   > D be the bounded complementary domain of I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩ in R².

   **True; proved.**
   * In collar coordinates, the frame `{a} × [0, r₂] ∪ [a, b] × {0} ∪ {b} × [0, s₂]` is an arc that
     meets the pulled-back `I₂` only at its ends, so their union is a simple closed curve.
   * Its bounded domain lies in the open rectangle, because the complement of the closed rectangle
     is connected and unbounded (`rect_domain`).
   * `D = F[D′]` is open and connected, and its frontier is the printed curve. `π⁻¹[D]` is open, and
     `D` meets `π[M]` (`hagopian76_D`).
2. **p. 346, T9:**
   > Note that the chain L − {L₁, L₁₁} follows Cl B.

   **Unargued; open.** Commission 166 §1.C suggests a route (the two ends of `Cl B` lie on opposite
   side edges). It fails at its step 2:
   * The end of `Cl B = h[G]` at `u = min k[G]` is `h[G ∩ k⁻¹(u)]`, part of a layer.
   * Boundary bumping in `h[k⁻¹[0, u]]` from a point of it in `π⁻¹[D]` produces a continuum inside
     `B ⊆ h[G]`, hence inside that layer. There is no contradiction unless the point is a limit of
     `h[k⁻¹[0, u)]`, which is not argued.
   * In a `sin(1/x)` curve with its bar `T` and an arc leaving `T` from one point, the points of `T`
     other than that point are not limits of the arc side (report 166 §1.C).

   At step 4 the margin is one link short at `L₄`. Restricting to components through `K₀` (over
   abscissa `11/22`, links `L₅`–`L₇`) repairs it, and T12 and T17 use only such components.
3. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[⟨p₁, r⟩] and π⁻¹[⟨p₅, s⟩]. By Lemma 1 and Property 1, L follows a type A′
   > continuum in d⁻¹(v) that meets L₆ ∩ π⁻¹[D]. … This contradicts the definition of v.

   * **"first point": the infimum must be attained.** The next sentence works inside `d⁻¹(v)`.
     Attainment is a hyperspace limit and is unargued. The contradiction itself needs only a crossing
     at some `u < v`.
   * **"By Lemma 1 and Property 1, L follows …": unargued.** It needs item C for continua inside a
     layer of `F`.
   * **"This contradicts the definition of v": needs a margin.** Under the shift `g`, `g[Q]` stays off
     `π⁻¹[I₂]` (by `ε₂`), but it may meet `E` and its closure may fall short of the side edges.

   Open.
4. **p. 347, T12:**
   > Let p and q be points of K ∩ (W − R(E)) that belong to distinct inaccessible composants [10] of
   > the indecomposable continuum Cl R(E) (Lemma 6). … By Property 1, R(E) intersects an arc in K
   > that is irreducible between C and the q-component of M ∩ π⁻¹[D] and R(E) separates these
   > components in π⁻¹[D].

   * **"inaccessible" is not used afterwards.** Distinct composants off `R(E)` inside `W` exist by
     Baire, without [10] (`exists_two_composants_in_open`).
   * **The points on `K`: unargued; open.** Crossing components meet `K₀` (`hagopian76_K0_crosscut`),
     but that they exist near `x` (item C) and meet `K₀` near `x` is not argued. Hagopian's `x`, any
     point of `k⁻¹(p₃) ∩ Cl K`, should be taken in `Cl(K ∩ Cl R(E))`.
   * **"By Property 1, R(E) intersects an arc in K …": unargued; open.** It needs crossing
     components of `R(E)` between two given crossing components.
5. **p. 347, T13:**
   > The existence of such a continuum F follows from Property 1 and the fact that
   > Cl R(E) = Cl R(k⁻¹(0), E) (Lemma 6 (proof)).

   **Not reached.**
6. **pp. 347–349, T15–T17:**
   > It follows from Property 3 that I is finite. … Following Bing [2, p. 225], we now show that if
   > I = [x₂ᵢ₋₁, x₂ᵢ] has Property 4, then so does J = [x₂ᵢ₋₃, x₂ᵢ₋₂].

   **Not reached.**

No statement of Hagopian's is refuted, and no defective proof is added. The count stays at fourteen.

### Hagopian 1976 XII: crossing translates; the `p`-components; T12, Property 3, T13; T15–T17 (batch 167)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76L.lean` and four new supporting files
under `HPC/Hagopian/`:
* `H76Translate`: boundary bumping for components; uniform collar coordinates;
* `H76TranslateMain`: Lemma T;
* `H76K0Dense`: Lemma T′; the crossing `p`-components;
* `H76CrossEss`: crossing continua over the thin strip are essential; T12 (1)–(2).

The report is `doc/batches/REPORT-batch167.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XII (batch 167)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the 18 new theorems is `doc/batches/audits/axioms-batch167.txt`.
* **Source.** Hagopian 1976, pp. 346–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** `crossing_translate` (Lemma T), `K0_dense_low` (Lemma T′), `crossing_essential`,
    `hagopian76_T12_parts12` (T12 (1)–(2) in a shape I chose).
  * **Open:** T12 (3), Property 3, T13, T15–T17 and the assembly (`OPEN.md`, batch-167 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 346, T9:**
   > Note that the chain L − {L₁, L₁₁} follows Cl B.

   * **For the components T12 uses: the commission's substitute is proved.** These are the
     components through `p = h(x)` with `h` small. Such a component contains
     `h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]` and is crossing (`crossing_translate`,
     `hagopian76_T12_parts12`). So `L − {L₁, L₁₁}` follows it in Property 1's sense.
   * **For T17: partly.** In T17, `Cᵢ₋₁` is "the first component … met by extending `Cl Cᵢ` away from
     `X`", and `yᵢ₋₁` is "a point of `K ∩ Cᵢ₋₁`". The same holds when `Cᵢ₋₁` has a point low enough
     over the middle range (report §1.E); that it has one is not argued.
   * **In general: open.**
2. **p. 347, T12:**
   > To see this let x be a point of k⁻¹(p₃) ∩ Cl K. … Let p and q be points of K ∩ (W − R(E)) that
   > belong to distinct inaccessible composants [10] of the indecomposable continuum Cl R(E)
   > (Lemma 6). … By Property 1, R(E) intersects an arc in K that is irreducible between C and the
   > q-component of M ∩ π⁻¹[D] and R(E) separates these components in π⁻¹[D].

   * **The choice of `x`: true; proved.** Take `x` from Lemma T′ (`K0_dense_low`). Then
     `x ∈ k⁻¹(p₃) ∩ Cl(M ∩ K₀)`, and every neighbourhood of `x` meets `M ∩ K₀`.
   * **(2) "the closure of the p-component C … is essential to h[R(E)]": true for crossing
     components over the thin strip; proved with T9's homeomorphism `h′` in place of `h`**
     (`crossing_essential`).
   * **The choice of `p`, `q`: open.**
     * The commission proposes that one composant contains only countably many disjoint crossing
       components. This does not follow from general continuum theory: one proper subcontinuum can
       contain uncountably many disjoint crossing continua (the Cantor comb).
     * Whether `Cl R(E) = M` is not settled (check 6).
   * **"By Property 1, R(E) intersects an arc in K …": unargued; open.** Lemma T gives crossing
     translates `h[E]`, not crossing pieces of `R(E)`.
3. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[⟨p₁, r⟩] and π⁻¹[⟨p₅, s⟩]. … This contradicts the definition of v.

   **Unchanged from batch 166; open.** For T15–T17, the continuum form of "crossing" should suffice
   (report §1.C).
4. **p. 347, T13:**
   > The existence of such a continuum F follows from Property 1 and the fact that
   > Cl R(E) = Cl R(k⁻¹(0), E) (Lemma 6 (proof)).

   **Not reached.** It waits on T12 (3).
5. **pp. 347–349, T15–T17:**
   > It follows from Property 3 that I is finite. … Following Bing [2, p. 225], we now show that if
   > I = [x₂ᵢ₋₁, x₂ᵢ] has Property 4, then so does J = [x₂ᵢ₋₃, x₂ᵢ₋₂].

   **Not reached.**
6. **Whether `Cl R(E) = M`.** Hagopian treats `Cl R(E)` as a possibly proper subcontinuum (p. 343):
   > Since M is atriodic, R(E) is a composant of Cl R(E).

   **Not settled.** If `Cl R(E) ≠ M`, the points of `K₀` near `x` given by Lemma T′ lie in
   translates `h[E]`, which are not known to lie in `Cl R(E)` (report §1.B).

No statement of Hagopian's is refuted, and no defective proof is added. The count stays at fourteen.

### Hagopian 1976 XIII: crossing pieces of `R(E)`; what T13–T17 use; T12 (3); Property 3; T13 (batch 168)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76M.lean` and five new supporting files
under `HPC/Hagopian/`:
* `H76TranslateIn`: Lemma T relative to an ambient set containing the translate;
* `H76RPiece`: Lemma R (crossing pieces of `R(X, E)`, inside one extension);
* `H76PairSep`: an arc from the bottom to `I` is a cross-cut of `D′`; a crossing set separates `D′`
  along the vertical;
* `H76CrossSep`: the same in `π⁻¹[D]`;
* `H76T12`: T12 (3) in the shape of commission 168 §2.C.

The report is `doc/batches/REPORT-batch168.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XIII (batch 168)* of `Axioms.lean` / `axioms.txt`; standard
  axioms only. The audit of the 14 new theorems is `doc/batches/audits/axioms-batch168.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** `crossing_piece_of_R` (Lemma R), `crossing_separates`, `crossing_pair_separates`,
    `hagopian76_T12` (T12 (3) in a shape: a crossing continuum of `R(X, E)` inside one extension
    separates `p = h₀(x)` from `q = h₁(x)` on `K₀`).
  * **Open:** `p`, `q` off `R(E)`; the dichotomy for translates of `R(E)`; Property 3; T13;
    T15–T17; the assembly (`OPEN.md`, batch-168 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 347, T12, the choice of `p`, `q`:**
   > Let p and q be points of K ∩ (W − R(E)) that belong to distinct inaccessible composants [10] of
   > the indecomposable continuum Cl R(E) (Lemma 6).

   **Of these conditions only `p, q ∉ R(E)` is used** (report §1.A). It is used in T13, where `p`
   and `f(p)` must lie off `F`, and in T17, as `h[R(E)] ∩ R(E) = ∅` and `h₁[R(E)] ∩ R(E) = ∅`.
   Passing from `p, q ∉ R(E)` to these needs a dichotomy that is never stated: if `g[R(E)]` meets
   `R(E)`, then `g[R(E)] = R(E)`. "Distinct composants", "inaccessible" and `p, q ∈ Cl R(E)` are
   used nowhere on pp. 347–349. Choosing `p`, `q` off `R(E)` is open.
2. **p. 347, T12, the separation:**
   > By Property 1, R(E) intersects an arc in K that is irreducible between C and the q-component of
   > M ∩ π⁻¹[D] and R(E) separates these components in π⁻¹[D].

   **True in the following form; proved.**
   * `crossing_piece_of_R`: crossing pieces of `R(X, E)`, disjoint from `E`, lie arbitrarily low on
     `K₀`, each inside one extension of `E` away from `k⁻¹(0)`.
   * `crossing_separates`: a crossing continuum between two points of `K₀` separates them in
     `π⁻¹[D]`.
   * `hagopian76_T12` combines the two for `p = h₀(x)` and `q = h₁(x)`.
   * Commission 168 §1 (Lemma R), checked step by step: every step holds (report §1.B). Steps 1–4
     are done with `R(X, E)`; step 5 by Lemma T relative to an ambient set.
3. **p. 347, Property 3:** unchanged from batch 167; open.
4. **p. 347, T13:**
   > The existence of such a continuum F follows from Property 1 and the fact that
   > Cl R(E) = Cl R(k⁻¹(0), E) (Lemma 6 (proof)).

   **Gap (unargued), not refuted.**
   * Existence needs an extension away from `k⁻¹(0)` that separates `p` from `f(p)`. This in turn
     needs `p, f(p) ∉` that extension. Lemma R supplies the crossing piece inside one extension
     `H`; `p, q ∉ H` is not shown.
   * The irreducible element needs that the intersection of a chain of separating extensions is an
     extension. Hagopian does not argue this; it is plausible from Lemma 4.
5. **pp. 348–349, T17:**
   > Since no point of N is within ε₂ of Q, the continuum f[N] does not intersect P.

   **Gap (unargued), not refuted.** `P = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q`. The sentence gives `f[N] ∩ Q = ∅`.
   It also needs `f[N] ∩ F = ∅`, which follows from `f[N] ⊆ h₁[R(E)]` once `h₁[R(E)] ∩ R(E) = ∅`
   (check 1).
6. **pp. 347–349, T15–T17, the rest:**
   > It follows from Property 3 that I is finite. … Following Bing [2, p. 225], …

   * Not reached, apart from the planar fact used for "`f(yᵢ₋₁)` is either above `d⁻¹[I]` or below
     `d⁻¹[J]`". That fact, the three-part cut by two crossing continua, is proved
     (`crossing_pair_separates`).
   * The Property 4 base case needs that only the last block `d⁻¹[[x₂ₙ₋₁, x₂ₙ]]` separates; this is
     unargued.
   * T17's low point of `Cᵢ₋₁` is not given by Lemma R and Property 3. The missing statement is
     report §1.E.

No statement of Hagopian's is refuted. Checks 4 and 5 record unargued steps (gaps), not defective
proofs. The count stays at fourteen.

### Hagopian 1976 XIV: above and below; generic `p`, `q`; the dichotomy for `R(E)`; T13; Property 3 (batch 169)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76N.lean` and six new supporting files
under `HPC/Hagopian/`:
* `H76Meagre`: `R(E)` lies in a composant of `M`, so it is meagre;
* `H76Sides`: the sets below and above a crossing continuum;
* `H76T12Sides`: the batch-168 T12 construction, with the position data exposed;
* `H76Generic`: generic `p`, `q`;
* `H76Dichot`: the dichotomy (as a `Prop`, and from `Cl R(E) = M`);
* `H76ChainSep`: intersections of chains of separators; T13 under `ExtChainInter`.

The report is `doc/batches/REPORT-batch169.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XIV (batch 169)* of `Axioms.lean` / `axioms.txt`; standard
  axioms only. The audit of the 33 new theorems is `doc/batches/audits/axioms-batch169.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** `isMeagre_Rset`, `crossing_sides` (disjointness half), `exists_generic_pq`,
    `Rset_homeo_dichotomy_of_closure`, `hagopian76_T12_of_dichotomy` (under `RsetDichotomy`),
    `iInter_chain_extension` (separation and continuum halves), `hagopian76_T13` (under
    `ExtChainInter`).
  * **Open:** the dichotomy; `Cl R(E) = M`; `ExtChainInter`; the covering half of above/below;
    Property 3; T15–T17; the assembly (`OPEN.md`, batch-169 section).
  * **Refuted:** nothing formally. The covering half of commission §1.1, for arbitrary crossing
    continua, fails by an informal example (check 1). The example is not formalized.

**Checks.**

1. **p. 347, T12, whether `K` is needed:**
   > Let p and q be points of K ∩ (W − R(E)) …

   **`K` is not needed for `p`, `q`; proved** (`exists_generic_pq`). The points are taken in the open
   sets below and above a crossing continuum `Z` near the batch-168 points of `K₀`, off `R(E)` by
   meagreness. `K` stays in use as the reference for the positions, and as the place where T17
   picks `yᵢ₋₁` (`K ∩ Cᵢ₋₁ ≠ ∅` because `K₀` is a cross-cut, `hagopian76_K0_crosscut`). In
   pp. 348–349 every position statement ("`yᵢ` is between `d⁻¹[I]` and `d⁻¹[J]`", "`f(yᵢ)` is
   above `d⁻¹[I]`", "`yᵢ₋₁` is below `C`") is of the form "joined, by a connected set missing the
   separator, to a point of `K` on a given side". That is `belowSet`/`aboveSet`. The points `f(yᵢ)`
   are not on `K` in any case. So Hagopian already uses positions of points off `K`.
   * **Disjointness of below and above: proved** (`crossing_sides`).
   * **Covering:**
     > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

     This sentence needs every point off the separator to be on one side. For an arbitrary crossing
     continuum this fails: the inside of a bubble (a crossing arc with a small circle attached) is
     on neither side. This is an informal example, not formalized. For the separators of T17, which
     are subcontinua of `M`, the covering needs them not to separate the plane. **Open.**
2. **pp. 347–349, the tacit dichotomy:**
   > Let p and q be points of K ∩ (W − R(E)) … the continuum f[N] does not intersect P.

   **Proved from `Cl R(E) = M`** (`Rset_homeo_dichotomy_of_closure`): `R(E)` and `g[R(E)]` are then
   composants of `M`. In general it is **open**, so it is carried as the hypothesis `RsetDichotomy`.
   Under it, `h[R(E)] ∩ R(E) = ∅` follows from `h(x) ∉ R(E)` (`disjoint_image_Rset`).
3. **p. 347, T13, the existence sentence:**
   > Let F be a continuum that is irreducible with respect to the following properties: …
   > The existence of such a continuum F follows from Property 1 and the fact that
   > Cl R(E) = Cl R(k⁻¹(0), E) (Lemma 6 (proof)).

   * **The starting extension: proved.** `exists_generic_pq` gives an extension `H` away from
     `k⁻¹(0)` that separates `p` from `f(p)` (with `p`, `f(p) ∉ H`).
   * **The chain step, compactness half: proved** (`iInter_chain_extension`). The intersection
     still separates and is a continuum containing `E`.
   * **Whether the intersection is an extension: gap (unargued), open** (`ExtChainInter`). Under
     it, the irreducible `F` exists (`hagopian76_T13`, Zorn).
4. **p. 347, Property 3:**
   > No component of F ∩ π⁻¹[D] whose closure meets both π⁻¹[⟨p₁, r⟩] and π⁻¹[⟨p₅, s⟩] is contained
   > in an element of the decomposition of F. To see this assume the contrary. Let v be the first
   > point of [0, 1] such that d⁻¹(v) contains a component …

   Not attempted; unchanged from batch 168. **Open.**
5. **pp. 347–349, T15–T17:** not reached beyond checks 1–3. T17's component `Cᵢ₋₁`:
   > Let Cᵢ₋₁ be the first component of M ∩ π⁻¹[D] (whose closure intersects π⁻¹[⟨p₁, r⟩] and
   > π⁻¹[⟨p₅, s⟩]) that is met by extending Cl Cᵢ away from X in M.

   This component is fixed by `Cl Cᵢ`, so its points cannot be chosen generically. Lemma T covers it
   only if it has a point `h′(x′)` low over the middle range. **Open** (item F).
6. **`Cl R(E) = M`?** No argument either way. **Open.** By check 2 it would give the dichotomy.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XV: `ExtChainInter`; the covering half; "follows" for crossing components; Property 3 (batch 170)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76O.lean` and four new supporting files
under `HPC/Hagopian/`:
* `H76ChainInter`: intersections of extensions inside one extension; `ExtChainInter`;
* `H76Follows`: T9's homeomorphism with the link condition kept; "follows" for crossing components;
* `H76Cover`: components of `π⁻¹[D] − K` reach the frontier (`K` a proper subcontinuum of `M`);
* `H76CrossClosed`: upper limits of connected sets; `crossing_set_closed`.

The report is `doc/batches/REPORT-batch170.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XV (batch 170)* of `Axioms.lean` / `axioms.txt`; standard
  axioms only. The audit of the 19 new theorems is `doc/batches/audits/axioms-batch170.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** `extChainInter_in`, `extChainInter`, `hagopian76_T13_uncond` (T13 unconditional),
    `crossing_sides_cover_frontier` (first step of the covering half), `follows_crossing`,
    `crossing_set_closed` and `hagopian76_first_crossing_param` (the least `v`, with margins).
  * **Open:** the three cases of the covering half; the shift step and Property 3; T15–T17; the
    assembly; the dichotomy (`OPEN.md`, batch-170 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 347, T13, the existence sentence:**
   > Let F be a continuum that is irreducible with respect to the following properties: 1. F is an
   > extension of E in M away from k⁻¹(0). 2. F separates p from f(p) in π⁻¹[D]. The existence of
   > such a continuum F follows from Property 1 and the fact that Cl R(E) = Cl R(k⁻¹(0), E)
   > (Lemma 6 (proof)).

   **Proved** (`hagopian76_T13_uncond`). The chain step is `extChainInter`: inside one extension
   `H` (map `d`) every extension away from `k⁻¹(0)` is an initial segment `d⁻¹[[0, s]]` (Lemma 4,
   strong form), so the intersection of a chain is `d⁻¹[[0, inf s]]`, an extension by `piece_map`.
   The printed reasons (Property 1, Lemma 6) are not the ones used; the sentence is unargued as
   printed but true.
2. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)].

   **With margins, proved** (`crossing_set_closed`, `hagopian76_first_crossing_param`): the set of
   `v` whose layer contains a connected set inside a closed region and meeting two closed edge
   segments is closed (upper limits, `limsup_isPreconnected`). For the printed open conditions the
   existence of the first point is unargued.
   > By Lemma 1 and Property 1, L follows a type A′ continuum in d⁻¹(v) that meets L₆ ∩ π⁻¹[D].

   **Proved in a weaker form** (`follows_crossing`): the closure of a crossing component contains
   `h[k⁻¹((4/11, 7/11))]` for an `ε₁`-homeomorphism `h` with Property 1's link condition.
   > This contradicts the definition of v.

   **Unargued; open.** The shift `g` with `g[d⁻¹(v)] = d⁻¹(u)` is small but does not preserve a fixed
   margin, so `u` need not be in the set whose least element is `v` (report §1.D).
3. **p. 347:**
   > It follows from Property 3 that I is finite.

   Not reached. **Open.**
4. **p. 348, Property 4, the base case:**
   > Note that [x₁, x₂] does not have Property 4.

   Not reached. `d⁻¹[[x₁, x₂]] = E` misses `π⁻¹[D]`; the sentence reduces to `π⁻¹[D]` being
   connected (report §1.E). **Open.**
5. **pp. 348–349, the induction:**
   > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

   **First step proved** (`crossing_sides_cover_frontier`): since no proper subcontinuum of `M`
   separates the plane, every component of `π⁻¹[D] − d⁻¹[I]` reaches the frontier of `π⁻¹[D]`. The
   bottom, `I₂` and side-edge cases are open; pockets at the side edges are not excluded by
   non-separation, and `f(yᵢ₋₁) ∈ L₆` does not keep it out of them. **Open.**
   > Since L − {L₁, L₁₁} follows Cl Cᵢ₋₁ and Cl Cᵢ, the continuum N does not come within ε₂ of
   > π⁻¹(p₄).

   The weaker "follows" of check 2 does not give this; it needs the end pieces of the translate to
   lie outside `D` (report §1.C). **Open.**
6. **The tacit dichotomy:** unchanged; open, carried as `RsetDichotomy`. Theorem 1 is not verified,
   conditionally or otherwise.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XVI: Property 3 without margins; positions through the side edges; the ends of crossing components; the dichotomy (batch 171)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76P.lean` and three new supporting files
under `HPC/Hagopian/`:
* `H76Prop3L3`: Lemma 3 against two translated layers; the parameters met by a layer form an interval;
* `H76Bottom`: preimages under `π` of open connected sets off `π[E]`; the bottom case of the covering;
* `H76GenericComp`: translates moving a point of `E` off its composant miss `R(E)`; generic `p`, `q`
  off the composant.

The report is `doc/batches/REPORT-batch171.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XVI (batch 171)* of `Axioms.lean` / `axioms.txt`; standard
  axioms only. The audit of the 11 new theorems is `doc/batches/audits/axioms-batch171.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** `layer_meets_translate_end` (Lemma 3 against two translated layers),
    `hagopian76_property3_reduced` (Property 3 reduced to an end case), `crossing_bottom_below` (the
    bottom case of the covering), `translate_Rset_disjoint` and `hagopian76_T12_uncond` (T12,
    conditions 2–3, without the dichotomy).
  * **Open:** the end case of Property 3; the `I₂` case, the side edges and the pockets of the
    covering; the ends of crossing components; T15–T17; the assembly (`OPEN.md`, batch-171 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)]. By Lemma 1 and Property 1, L follows a type A′
   > continuum in d⁻¹(v) that meets L₆ ∩ π⁻¹[D]. By Lemmas 2 and 3, a homeomorphism g of M onto M
   > and a point u of [0, v) exist such that gd⁻¹(v) = d⁻¹(u) … This contradicts the definition of v.

   **Reduced; open.** Lemma 3 alone (`lemma3_half` for `h⁻¹`) shows that an interior layer of `F`
   meeting two distinct layers of a translate `h[E]` meets a translated end set
   (`layer_meets_translate_end`); with "follows" (`follows_crossing`), a layer of `F` containing a
   crossing reaches an end link of the chain through every link on one side
   (`hagopian76_property3_reduced`). No least `v` is used. The remaining configuration (the layer
   meets every `h[k⁻¹(t)]` with `t ≤ 6/11`, or every one with `t ≥ 5/11`) is not excluded; the
   triod route of the commission does not reach it either (it needs `h[E] ∩ F ⊆ d⁻¹(v)`).
2. **p. 347:**
   > It follows from Property 3 that I is finite.

   Not reached. **Open.**
3. **p. 348:**
   > Note that [x₁, x₂] does not have Property 4.

   Not reached; reduces to `π⁻¹[D]` connected (report 170 §1.E). **Open.**
4. **pp. 348–349:**
   > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

   The bottom case is **proved** (`crossing_bottom_below`): a component of `π⁻¹[D] − Z` reaching
   the bottom edge is below `Z`, for compact `Z` missing `π⁻¹` of the bottom edge. The `I₂` case and
   the side edges are **open**.
   > the continuum N does not come within ε₂ of π⁻¹(p₄)

   Needs the ends of crossing components (item C). **Open.**
   > Let Cᵢ₋₁ be the first component …

   Not reached. **Open.**
5. **The tacit dichotomy** (if a translate of `R(E)` meets `R(E)`, it equals `R(E)`): **not needed.**
   T12 in the form T13–T17 use (`h[R(E)] ∩ R(E) = ∅ = h₁[R(E)] ∩ R(E)`) holds without it
   (`hagopian76_T12_uncond`): `R(E)` lies in the composant of `x ∈ E`, and `h(x)` is chosen off that
   (meagre) composant, so `h[R(E)]` lies in another composant (`translate_Rset_disjoint`). The
   paper's unargued step is supplied by a different argument; the dichotomy itself remains unproved.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XVII: the end case of Property 3; the `I₂` case and the side edges by Schoenflies; the ends of crossing components; T15–T17 (batch 172)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76Q.lean` and two new supporting files
under `HPC/Hagopian/`:
* `H76Swallow`: the swallowing lemma and its consequences for translates;
* `H76InnerCollar`: the inner collar of an arc of a Jordan curve, `D′` as a Jordan domain, and the
  `I₂` case.

The report is `doc/batches/REPORT-batch172.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XVII (batch 172)* of `Axioms.lean` / `axioms.txt`; standard
  axioms only. The audit of the 18 new theorems is `doc/batches/audits/axioms-batch172.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * `continuum_subset_layer_of_open` (the swallowing lemma);
    * `translate_subset_layer` and `translate_extension_subset_layer`;
    * `hagopian76_property3_translate` (a layer containing a crossing contains `h[F]`);
    * `hagopian76_property3_of_end` (Property 3 from `Property3End`);
    * `closure_Rset_subset_of_translate`, `property3End_of_closure_Rset` and
      `property3End_of_dichotomy`;
    * `jordan_inner_collar`, `rect_frontier_domain` and `top_component_above_aux` (the `I₂` case);
    * `crossing_sides_cover_schoenflies` (the bottom and `I₂` cases together).
  * **Open:**
    * `Property3End`, hence Property 3;
    * the side edges and pockets of the covering;
    * the ends of crossing components;
    * T15–T17 and the assembly (`OPEN.md`, batch-172 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 347, Property 3:**
   > Let v be the first point of [0, 1] such that d⁻¹(v) contains a component of F ∩ π⁻¹[D] whose
   > closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)]. By Lemma 1 and Property 1, L follows a type A′
   > continuum in d⁻¹(v) that meets L₆ ∩ π⁻¹[D]. By Lemmas 2 and 3, a homeomorphism g of M onto M
   > and a point u of [0, v) exist such that gd⁻¹(v) = d⁻¹(u) … This contradicts the definition of v.

   **Reduced further; open.**
   * The batch-171 end case is closed. The middle translate in the closure of the crossing is a
     relatively open piece of `h[E]`, so by the swallowing lemma (lower semicontinuity, Lemma 5) the
     layer `d⁻¹(v)` contains all of `h[E]`, and then all of `h[F]`
     (`hagopian76_property3_translate`).
   * Property 3 follows from `Property3End` (no `ε₁`-homeomorphism carries `F` into an interior
     layer of `F`).
   * `Property3End` follows from `Cl R(E) = M` and from the dichotomy, since such a homeomorphism
     puts `Cl R(E)` in one layer of `h⁻¹[F]`.
   * The least `v` is not used. The configuration left is the one Hagopian's move `g` must exclude.
2. **p. 347:**
   > It follows from Property 3 that I is finite.

   Not reached. **Open.**
3. **p. 348:**
   > Note that [x₁, x₂] does not have Property 4.

   Not reached. **Open.**
4. **pp. 348–349:**
   > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

   * The bottom and `I₂` cases are **proved** (`crossing_sides_cover_schoenflies`). A component of
     `π⁻¹[D] − Z` whose closure reaches the bottom edge is below `Z`, and one whose closure reaches
     `π⁻¹[I₂]` is above `Z`. This holds for compact `Z` missing both; the `I₂` case uses the inner
     collar from Schoenflies.
   * Components whose closure meets the frontier only in a side segment (pockets) are **open**. The
     printed argument does not address them: it is a gap in exposition, not a refutation.

   > the continuum N does not come within ε₂ of π⁻¹(p₄)

   Item C. **Open.**
   > Let Cᵢ₋₁ be the first component …

   Not reached. **Open.**

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XVIII: Property 3 by descent; pockets; the ends of crossing components; T15–T17 (batch 173)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76R.lean` and one new supporting file,
`HPC/Hagopian/H76Descent.lean` (layer crossings, D1, D2, the least element, the length bound).

The report is `doc/batches/REPORT-batch173.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XVIII (batch 173)* of `Axioms.lean` / `axioms.txt`; standard
  axioms only. The audit of the 21 new theorems is `doc/batches/audits/axioms-batch173.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * `crossing_from_layer_translate` (D1) and `crossing_descends` (D2);
    * `isClosed_layerCrossing` (the crossing parameters form a closed set);
    * `hagopian76_property3_domain` and `hagopian76_property3` (**Property 3, unconditionally**,
      for layers `d⁻¹(v)`, `v < 1`);
    * `crossing_length_pos` (crossings below `v₀ < 1` need parameter length `≥ λ > 0`).
  * **Open:**
    * the pockets of the covering half (`CoverPocket`);
    * the ends of crossing components (`CrossingEnds`);
    * "`I` is finite", Property 4, T15–T17 and the assembly (`OPEN.md`, batch-173 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 347, Property 3:**
   > No component of F ∩ π⁻¹[D] whose closure meets both π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)] is contained
   > in an element of the decomposition of F. … Let v be the first point of [0, 1] such that d⁻¹(v)
   > contains a component of F ∩ π⁻¹[D] whose closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)]. By Lemma 1
   > and Property 1, L follows a type A′ continuum in d⁻¹(v) that meets L₆ ∩ π⁻¹[D]. By Lemmas 2 and
   > 3, a homeomorphism g of M onto M and a point u of [0, v) exist such that gd⁻¹(v) = d⁻¹(u) and
   > d⁻¹(u) contains a component of F ∩ π⁻¹[D] whose closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)].
   > This contradicts the definition of v.

   **Proved** (`hagopian76_property3`, `hagopian76_property3_domain`), for every element `d⁻¹(v)`
   with `v < 1`, and for every extension `F` of `E` away from `k⁻¹(0)` (not only the irreducible one).
   * "The first point `v`": attained for the closed condition `LayerCrossing` (a connected subset of
     `d⁻¹(v)` over `Cl D` meeting the closed side segments), `isClosed_layerCrossing`. No margin is
     needed: the axis is excluded afterwards (`layerCrossing_disjoint`), and `I₂` misses `π[M]`.
   * "By Lemma 1 and Property 1": supplied by the swallowing lemma (batch 172,
     `hagopian76_property3_translate`): the layer contains a whole translate `h[F]`.
   * "By Lemmas 2 and 3 … `d⁻¹(u)` contains a component …": the shift `g` keeps `gh(x)` over `D`
     for one middle point `x`, and the crossing in `d⁻¹(u)` is recreated from the ends of the
     translate `gh[E]` by boundary bumping (D1). Hagopian gives no argument for this step; the
     argument supplied here is D1.
   * The element `d⁻¹(1)` (included in "an element of the decomposition") is not covered: the
     swallowing lemma needs an interior layer. T15–T17 use Property 3 only through the collection
     `I`, whose finiteness is open (check 2).
2. **p. 347:**
   > It follows from Property 3 that I is finite.

   **Open.** What Property 3 gives (`crossing_length_pos`): below any `v₀ < 1`, every interval of
   `I` has length `≥ λ > 0`. Intervals of `I` are pairwise non-nested and belong to pairwise
   disjoint components. Neither fact bounds the number of intervals: overlapping intervals of
   length `≥ λ` can accumulate, and components of `F ∩ π⁻¹[D]` can accumulate since `F` is not
   locally connected. The inference is not evident from Property 3 alone. This is recorded as a gap
   in exposition, not a refutation.
3. **p. 348:**
   > Note that [x₁, x₂] does not have Property 4.

   Not reached. **Open.**
4. **pp. 348–349:**
   > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

   Pockets: **open** (as in batch 172). Coarse monotonicity (`IsEps1.sep_of_gap`) confines each point
   of `Cl Cᵢ₋₁` over abscissa `t` to a translate of a piece adjacent to that of `t`; it does not keep
   pockets away from the middle abscissae, since the pieces of `E` need not be small.
   > the continuum N does not come within ε₂ of π⁻¹(p₄)

   **Open.** D1 controls a single translate; `N` lies in the shortest extension `L` of `Cl Cᵢ`
   containing `Cᵢ₋₁`, which D1 does not control.
   > Let Cᵢ₋₁ be the first component …

   Not reached. **Open.**

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XIX: "`I` is finite"; the end element; `J` and the `xᵢ`; Property 4; the induction (batch 174)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76S.lean` and three new supporting files:
`HPC/Hagopian/H76EndElement.lean` (the end element through a proper extension; the length bound in
every layer), `HPC/Hagopian/H76IFinite.lean` (crossing components, irreducible intervals, `I`,
finiteness) and `HPC/Hagopian/H76JXs.lean` (`e`, `x₂ = e`, the base case of Property 4).

The report is `doc/batches/REPORT-batch174.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XIX (batch 174)* of `Axioms.lean` / `axioms.txt`; standard
  axioms only. The audit of the 27 new theorems is `doc/batches/audits/axioms-batch174.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * `hagopian76_property3_end_element`, `hagopian76_property3_components` (**Property 3 for every
      element of the decomposition**, the end element `d⁻¹(1)` included);
    * `hagopian76_I_finite` (**`I` is finite**), with `crossingIntervals_disjoint` (distinct members
      of `I` have disjoint interiors);
    * `hagopian76_J_xs` (`d⁻¹[[0, e]] = E` and `e < x` for every `[x, y] ∈ I`: `x₁ = 0`, `x₂ = e`);
    * `hagopian76_property4_base` (`[x₁, x₂]` does not have Property 4).
  * **Open:** `x₂ₙ = 1` (`LastIntervalReachesOne`); Property 4 for `[x₂ₙ₋₁, x₂ₙ]`; the induction
    (pockets; `N` and `ε₂`); the assembly (`OPEN.md`, batch-174 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 347:**
   > It follows from Property 3 that I is finite.

   **Proved** (`hagopian76_I_finite`), by commission 174 §1. The inference is correct but not
   immediate; the printed text omits these steps:
   * the closure of a crossing component `C` with interval `[x, y]` contains the whole layers
     `d⁻¹((x, y))` (`IsIrreducibleInterval.layerSet_Ioo_subset_closure`, from `layerSet_Ioo_subset`);
   * a component of `F ∩ π⁻¹[D]` contains every point of `F ∩ π⁻¹[D]` in its closure
     (`mem_component_of_mem_closure_in`), so two crossing components whose intervals have
     overlapping interiors coincide, and distinct members of `I` have disjoint interiors
     (`crossingIntervals_disjoint`; no Property 3 needed);
   * Property 3 in every layer, the end element included, gives a length bound `λ > 0` on all
     members (`crossing_length_pos_all`); then at most `1/λ + 1` members.

   Report 173 recorded this inference as not evident; that entry is superseded: the missing step
   was the disjointness of interiors (report 173 only had non-nesting).
2. **p. 347–348:**
   > Note that x₁ = 0, x₂ = e, and x₂ₙ = 1.

   * `x₁ = 0`, `x₂ = e`: **proved** (`hagopian76_J_xs`). Every `[x, y] ∈ I` has `e < x`: a crossing
     component misses `E` (no point of `E` lies over `D`, `crossSet_disjoint_E`), and its closure
     cannot meet `d⁻¹(e) = k⁻¹(1)`, which lies over `F(1, 0)`, outside `Cl D`. The strict inequality
     is true and is what keeps `[0, e]` a block by itself.
   * `x₂ₙ = 1`: **open**. It needs the irreducibility of `F` (T13): cutting off the tail beyond the
     last crossing block should keep the separation of `p` from `f(p)`. The tail can meet `π⁻¹[D]` in
     components that are not crossing components, and these can still separate `π⁻¹[D]`; no
     argument is printed. Recorded as a gap in exposition, not a refutation. The claim fails for an
     arbitrary extension (`F = E` gives `I = ∅`), so it depends on the choice of `F`.
3. **p. 348:**
   > Note that [x₁, x₂] does not have Property 4.

   **Proved** (`hagopian76_property4_base`): `d⁻¹[[x₁, x₂]] = E` misses `π⁻¹[D]`, which is connected
   (`isPreconnected_preimage_off`, `D` connected by `rect_frontier_domain`), so clause (2) fails for
   every point.
   > The interval [x₂ₙ₋₁, x₂ₙ] has the following property: 4. …

   **Open.** No argument is printed. Clause (2) needs that only the last block separates `yₙ` from
   `f(yₙ)`, which meets the obstruction of check 2 (`x₂ₙ = 1`).
   > we now show that if I = [x₂ᵢ₋₁, x₂ᵢ] has Property 4, then so does J = [x₂ᵢ₋₃, x₂ᵢ₋₂]

   **Open** (check 4).
4. **pp. 348–349, Cases 1 and 2:**
   > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

   Pockets: **open** (as in batches 172–173).
   > the continuum N does not come within ε₂ of π⁻¹(p₄)

   **Open.** The printed reason, "Since `L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and `Cl Cᵢ`", needs
   Property 3 and the first-component argument for `L`, an extension of `Cl Cᵢ`, not of `E`.
   > Let Cᵢ₋₁ be the first component …

   **Open.**
5. **Property 3 at the end element** (commission 174 §1.6):
   > No component of F ∩ π⁻¹[D] whose closure meets both π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)] is contained
   > in an element of the decomposition of F.

   **Proved for every element**, `d⁻¹(1)` included (`hagopian76_property3_components`,
   `hagopian76_property3_end_element`). A proper extension `F′ ⊋ F` away from `k⁻¹(0)` (Lemma 4)
   has `d⁻¹(1) = d′⁻¹(s′)` with `s′ < 1` (`ext_layers`), and Property 3 for `F′` applies. Hagopian's
   descent (least `v`) does not reach `v = 1` by itself; the proper extension supplies it.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XX: components through the middle; no deep pockets; `x₂ₙ = 1`; Property 4; the induction (batch 175)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76T.lean` and two new supporting files:
`HPC/Hagopian/H76Pocket.lean` (bumping inside an extension; P3; P2; no deep pockets; the tail) and
`HPC/Hagopian/H76X2n.lean` (`TailCutKeepsSep`; `x₂ₙ = 1` from it).

The report is `doc/batches/REPORT-batch175.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XX (batch 175)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the 13 new theorems is `doc/batches/audits/axioms-batch175.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * `component_over_middle_crossing`: every component of `F ∩ π⁻¹[D]` through a point over `D` at
      abscissa in `[3/8, 5/8]` is crossing or meets `d⁻¹(1)`;
    * `component_over_middle_crossing_of_end`: crossing, when `d⁻¹(1)` is not over `D`;
    * `cover_pocket_middle`: no deep pockets;
    * `translate_through_point_in_F`: P2;
    * `hagopian76_tail_middle`: the tail beyond the last crossing interval;
    * `hagopian76_x2n_eq_one_of_cut`: `x₂ₙ = 1` from the named `Prop` `TailCutKeepsSep`.
  * **Open:** `TailCutKeepsSep`; Property 4 for `[x₂ₙ₋₁, x₂ₙ]`; the induction (pockets over `L₆`;
    `N` and `ε₂`); the assembly (`OPEN.md`, batch-175 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 348:**
   > Note that x₁ = 0, x₂ = e, and x₂ₙ = 1.

   `x₂ₙ = 1`: **open, reduced.** For Hagopian's irreducible `F` (T13) it follows from
   `TailCutKeepsSep` (`hagopian76_x2n_eq_one_of_cut`): cutting `F` at a layer beyond every interval
   of `I` keeps the separation of `p` from `f(p)`.
   * The tail beyond the last crossing interval meets the middle only in components reaching the end
     set `d⁻¹(1)` (`hagopian76_tail_middle`).
   * That the tail is not needed for the separation is a plane-separation statement (Janiszewski,
     compact form) that is not formalized.

   Gap in exposition, not a refutation.
2. **p. 348:**
   > The interval [x₂ₙ₋₁, x₂ₙ] has the following property: 4. …

   **Open.** Clause (2) is the cutting step for the gaps between blocks as well as the tail; clause
   (1) needs the T12 set-up.
3. **pp. 348–349, Cases 1 and 2:**
   > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

   **Partly addressed.** No non-crossing component of `F ∩ π⁻¹[D]` missing `d⁻¹(1)` has a point over
   the abscissae `[3/8, 5/8]` (`cover_pocket_middle`).
   * The induction places `f(yᵢ₋₁)` in `L₆`, over `(5/11 − η, 8/11 + η)`, which is wider.
   * The set removed is a block plus an arc, not a whole extension.
   > the continuum N does not come within ε₂ of π⁻¹(p₄)

   **Open.** `N` lies in an extension of `Cl Cᵢ`, not of `E`, so P2 does not apply to it.
   > Let Cᵢ₋₁ be the first component …

   **Open.**
4. **Atriodicity in P1** (commission 175 §4.4): does not arise. P1 is not used. P3 is proved by the
   shortcut of commission 175 §1, P3's last bullet, which uses atriodicity only through no hair for
   `F` (`subset_of_meets_avoids`), as before.
5. **Commission 175 §1, P3's last bullet** ("every component of `F ∩ π⁻¹[D]` through a point over the
   middle is crossing"): **true with two corrections**, and proved in that form
   (`component_over_middle_crossing`).
   * Exception: the component may instead meet `d⁻¹(1)`. Informally, an extension can end over the
     middle.
   * The middle is `[3/8, 5/8]`; `[7/22, 15/22]` is too wide for coarse monotonicity at one eleventh.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXI: the cutting step; positions by `ε₃`; Property 4; the induction (batch 176)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76U.lean` and three new supporting files:
`HPC/Hagopian/H76Eps3.lean` (positions by `ε₃`; Property 2 at smaller `ε₃`), `HPC/Hagopian/H76Cut.lean`
(Janiszewski inside a domain; `SepByCrossing`; the cutting step; the separation above a gap) and
`HPC/Hagopian/H76Prop4.lean` (`T12Data`; `Property4`; the top block; the closing contradiction).

The report is `doc/batches/REPORT-batch176.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXI (batch 176)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the 21 new theorems is `doc/batches/audits/axioms-batch176.txt`.
* **Source.** Hagopian 1976, pp. 347–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * `eps3_positions_middle`, `eps3_image_middle`: for `ε₃` small (Property 2 kept), points within
      `ε₃` of a point over the abscissa `1/2` lie over `(3/8, 5/8)`;
    * `sepIn_union_cases`: Janiszewski's theorem inside a domain surrounded by a compact connected set;
    * `sep_by_crossing_cut`, `hagopian76_x2n_eq_one`: `SepByCrossing → TailCutKeepsSep → x₂ₙ = 1`;
    * `hagopian76_property4_top`: Property 4 for the block above a gap, from `SepByCrossing`, on a
      `T12Data`;
    * `hagopian76_T15_T17_cond`: `T12Data` + `SepByCrossing` + `Property4Step` → `False`.
  * **Open:** `SepByCrossing`; the existence of `T12Data`; `Property4Step`; the assembly
    (`OPEN.md`, batch-176 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 348:**
   > Note that f(yᵢ₋₁) belongs to L₆ ∩ π⁻¹[D].

   **A stronger position is available, and proved.** For `ε₃` small, `f(yᵢ₋₁)` lies over the
   abscissae `(3/8, 5/8)` (`eps3_positions_middle`, `eps3_image_middle`). The reasons are those of
   commission 176 §1.A: `yᵢ₋₁ ∈ K` lies over `11/22`, `π` is uniformly continuous on `M`, and the
   collar is an embedding of the compact rectangle. Shrinking `ε₃` keeps Property 2
   (`Property2At.mono`).
2. **p. 348:**
   > Note that x₁ = 0, x₂ = e, and x₂ₙ = 1.

   `x₂ₙ = 1`: **open, reduced** to `SepByCrossing` (`hagopian76_x2n_eq_one`): separation of `p`
   from `f(p)` by `F` is witnessed by the closures of the crossing components. Every crossing closure
   lies in the layers of its interval of `I` (`closure_crossing_subset_interval`), so it survives
   the cut. Gap in exposition, not a refutation.
3. **p. 348:**
   > The interval [x₂ₙ₋₁, x₂ₙ] has the following property: 4. …

   **Reduced:** proved from `SepByCrossing` on a `T12Data` (`hagopian76_property4_top`).
   * "Only the top block separates" is Janiszewski inside `π⁻¹[D]` (`sepIn_union_cases`) applied to
     the parts below and above a gap of `St J`.
   * Irreducibility (T13) then excludes the lower part, a proper extension of `E`.
   * The existence of the package (T12 (2) for the `h` of T12 (3)) is open.
4. **pp. 348–349, Cases 1 and 2:**
   > Let Cᵢ₋₁ be the first component of M ∩ π⁻¹[D] … that is met by extending Cl Cᵢ away from X in M.

   **Open.** Transporting Property 3 and `hagopian76_I_finite` by `h` needs the extensions of
   `Cl Cᵢ` as type A′ continua compatible with `D`, and the order of crossing components along them.
   > the continuum N does not come within ε₂ of π⁻¹(p₄)

   **Open.** P3 controls `L` over `[3/8, 5/8]`; `π⁻¹(p₄)` lies over `15/22`.
   > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

   **Partly addressed.** By check 1, `f(yᵢ₋₁)` is over the middle, where `cover_pocket_middle`
   controls the pockets; the separation by `P ∪ Q` is open.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXII: the strand lemma; `T12Data`; `π⁻¹[Fr D]`; the endgame (batch 177)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76V.lean` and three new supporting files:
* `HPC/Hagopian/H76Strand.lean`: `θ(n)`, the strand constants `StrandConst`, S2, S3;
* `HPC/Hagopian/H76StrandUse.lean`: the inner middle, S5, S6, strands are essential;
* `HPC/Hagopian/H76T12Exists.lean`: `π⁻¹[Fr D]`, `T12Data`, the conditional assembly.

The report is `doc/batches/REPORT-batch177.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXII (batch 177)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the 28 new theorems is `doc/batches/audits/axioms-batch177.txt`.
* **Source.** Hagopian 1976, pp. 346–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * S0–S3 and S6 of the strand lemma (`strand_fine_translate`, `strand_closure_subset`,
      `strand_crossing`, `strand_lemma`, `strand_fine_positions`);
    * S5, the whole-strand part (`typeA'_inner_strands`);
    * the existence of `T12Data` (`exists_T12Data`), with T12 (2) for the `h` of T12 (3)
      (`strand_essential`);
    * `π⁻¹[Fr D]` is compact and connected (`pi_preimage_frontier_D`);
    * the conditional assembly with the package and `Y` discharged (`hagopian76_T15_T17_cond2`).
  * **Corrected:** the batch-176 `hagopian76_T15_T17_cond` has inconsistent hypotheses
    (`T15_T17_cond_hyps_inconsistent`: `StrictMono x` on all of `ℕ` and `x(2n) = 1`). The corrected
    form `hagopian76_T15_T17_cond_fix` is proved.
  * **Open:** S4 (the order of strands); the hairs of S5; the blocks (C); `SepByCrossing` (D);
    `Property4Step` (E); the assembly (`OPEN.md`, batch-177 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 346, T9:**
   > Note that the chain L − {L₁, L₁₁} follows Cl B.

   **Superseded in the fine form, proved.** A crossing component through the inner middle
   `[3/22 + 3/n, 19/22 − 3/n]` has its closure in a `θ/4`-translate `h[E]`. The closure contains
   `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]` (`strand_lemma`), and positions along it are within `2/n`
   (`strand_fine_positions`). The chain `L` is not needed.
2. **p. 348:**
   > Note that x₁ = 0, x₂ = e, and x₂ₙ = 1.

   `x₂ₙ = 1`: **still reduced** to `SepByCrossing` (batch 176). That statement is open, and rests on
   the order of strands (S4).
3. **p. 348, Case 1:**
   > By considering the position of d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]], … yᵢ₋₁ is between d⁻¹[I] and d⁻¹[J].

   **Gap in exposition, open.** The cap `Λ` formed by the gap piece and the left side segment
   separates the plane by the converse of Janiszewski's theorem (unicoherence of the plane). That
   converse is not formalized. Which side of `Λ` is bounded is not checked formally.
4. **p. 348:**
   > the continuum N does not come within ε₂ of π⁻¹(p₄)

   **The range obstruction is removed.** `p₄ = 15/22` lies in the inner middle for `n ≥ 15`, where
   S6 gives positions within `2/n`. The sentence itself is open with `Property4Step`.
   > Since L − {L₁, L₁₁} follows …

   Replaced by the strand form of check 1.
5. **p. 349:**
   > Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J].

   **Open**, resting on S4. Case 2: open in the same way.
6. **The order of constants (commission 177 §2).** **Recorded.**
   * The fine resolution near `E` (`n`, `θ(n)`, Effros' `δ′`, `η`, the strip height `c(n)`) must be
     fixed before `D`. Hagopian's text does not fix an order.
   * With this order nothing downstream is constrained. `T12Data` is obtained for every `ε₃ > 0`,
     with no condition `ε₃ ≤ θ/2`, because T12's homeomorphisms are taken at `min(ε₃/2, θ/4)`.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXIII: the order of strands without Schoenflies; separation along the vertical; the end layer of `F`; unicoherence; the blocks (batch 178)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76W.lean` and seven new supporting files:
* `HPC/Hagopian/H76Unicoh.lean`: two continua with disconnected intersection separate the plane;
  separation in a domain;
* `HPC/Hagopian/H76Order.lean`: the abstract vertical frame `VFrame`, S4b–S4e, SSL;
* `HPC/Hagopian/H76OrderConcrete.lean`: the frame `lowFrame`, crossing pieces, S4a;
* `HPC/Hagopian/H76EndLayer.lean`: 3a;
* `HPC/Hagopian/H76SepCross.lean`: `SepByCrossing` from SSL;
* `HPC/Hagopian/H76Blocks.lean`: the blocks of `St J`;
* `HPC/Hagopian/H76Comp.lean`: the composant argument, `exists_T12Data_comp`.

The report is `doc/batches/REPORT-batch178.md`; the reconstruction of Cases 1–2 is
`doc/notes/hagopian76-cases.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXIII (batch 178)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the 71 new theorems is `doc/batches/audits/axioms-batch178.txt`.
* **Source.** Hagopian 1976, pp. 346–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * the order of crossing pieces, S4a–S4e, without Schoenflies (`crossing_piece_meets_sigma`,
      `crossing_piece_sides`, `crossing_piece_below_iff`, `crossing_piece_below_trans`,
      `crossing_piece_no_pocket`; `isPiece_of_isCrossingPiece`);
    * SSL, its converse and the general `SepByCrossing` (`strand_separation`,
      `strand_separation_converse`, `sepByCrossing_of_inner_crossing`);
    * unicoherence in separation form (`separatesPlane_union_of_inter_disconnected`) and the domain
      form (`sepIn_iff_separatesPts_union`);
    * 3a (`T12Data.end_layer_not_subset`);
    * 4.A (`strand_misses_F_of_composant`);
    * 4.C conditionally (`sep_by_crossing`, from `InnerComponentsCross`);
    * the blocks, with nondegenerate members (`exists_blocks`).
  * **Open:** 3b (`InnerComponentsCross`), 3c, 4.B, nondegeneracy of the members of `I`, §7, §8, the
    assembly (`OPEN.md`, batch-178 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 348:**
   > Note that x₁ = 0, x₂ = e, and x₂ₙ = 1.

   `x₂ₙ = 1`: **gap in exposition, reduced, open.** Through `sep_by_crossing` and the batch-176
   chain (`tailCutKeepsSep_of_sepByCrossing`, `x2n_eq_one_of_cut`) it now rests on two inputs:
   3b (`InnerComponentsCross`: the components of `F ∩ π⁻¹[D]` through the low vertical are crossing)
   and 4.B (`p`, `f(p)` lie on crossing pieces missing `F`; the "missing `F`" half is proved,
   `strand_misses_F_of_composant`). The text mentions neither.
2. **p. 348:**
   > The interval [x₂ₙ₋₁, x₂ₙ] has the following property

   **Same status as check 1** (`hagopian76_property4_top` with `sep_by_crossing`).
3. **p. 348:**
   > Then d⁻¹[J] separates yᵢ from f(yᵢ) and J has Property 4 unless yᵢ is above d⁻¹[J].

   **Correct in strand form, open.** If a `J`-strand lies between `Cᵢ` and the strand of `f(yᵢ)`,
   `d⁻¹[J]` separates (`strand_separation_converse`, proved); the remaining hypotheses (the strands
   involved are crossing pieces) are 3c and 4.B.
4. **p. 348, Case 1:**
   > By considering the position of d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]], … yᵢ₋₁ is between d⁻¹[I] and d⁻¹[J].

   **Gap in exposition, open.** The tool for the cap is now proved
   (`separatesPlane_union_of_inter_disconnected`). (α): one segment `Q` closes the band only if it is
   the first segment of the vertical over `15/22` met by `Cᵢ` from the left; (β): "between" must be
   read with respect to the strands of `d⁻¹[J] ∪ d⁻¹[I]` adjacent in the order of S4, since `I`- and
   `J`-strands can interleave; (γ): not checked formally. Details: `doc/notes/hagopian76-cases.md`.
5. **p. 349, Case 2:**
   > If yᵢ₋₁ is above d⁻¹[J], it is between d⁻¹[I] and d⁻¹[J] and f(yᵢ₋₁) is above d⁻¹[I].

   **Gap in exposition, open.** "`f(yᵢ₋₁)` is above `d⁻¹[I]`" needs that `Cᵢ₋₁` is above `d⁻¹[I]`,
   i.e. the minimality of `L` together with `L ∩ F = ∅` (the latter proved); reconstruction in the
   notes, §3 E2.6.
6. **The end layer of `F` (not in the text).**
   * **3a, proved** (`T12Data.end_layer_not_subset`): `d⁻¹(1) ⊄ π⁻¹[D]`, by irreducibility, the
     domain form of separation, Janiszewski, and `no_proper_subcontinuum_separates`.
   * **3b, open** (named `InnerComponentsCross`). The route's step 3.3 (the end layer swallowing a
     chunk `h[k⁻¹((τ, τ₁))]` of the translate through `y`, `τ₁ ≥ k(e)`) is not settled by the triod,
     by 3a, or by the void interior of `d⁻¹(1)`; see the report, §3b.
7. **Blocks (commission 178 §6), new finding.** The blocks of `St J` give `x` strictly increasing
   only if no member of `I` is degenerate (`[u, u]`, a crossing component inside one layer
   `d⁻¹(u)`). The text does not address this. `exists_blocks` assumes nondegeneracy.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXIV: the end layer of `F`; `SepByCrossing` without conditions; uniform heights; the assembly; the step (batch 179)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76X.lean` and seven new supporting files:
* `HPC/Hagopian/H76Nondeg.lean`: nondegeneracy of `I` and finiteness of the crossing components
  (abstract forms);
* `HPC/Hagopian/H76Uniform.lean`, `H76Uniform2.lean`, `H76Uniform3.lean`: the heights chosen before
  `G`;
* `HPC/Hagopian/H76PieceB.lean`: 4.B;
* `HPC/Hagopian/H76Final179.lean`: `SepByCrossing`, `x₂ₙ = 1`, the top block, the blocks, T15–T17
  from `InnerComponentsCross`;
* `HPC/Hagopian/H76Thm1Setup.lean`: `Thm1Setup`, T1–T13 assembled, Theorem 1 from saturation and the
  step.

The report is `doc/batches/REPORT-batch179.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXIV (batch 179)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the 32 new theorems is `doc/batches/audits/axioms-batch179.txt`.
* **Source.** Hagopian 1976, pp. 346–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * 4.B (`p_on_crossing_piece`);
    * nondegeneracy of `I` (`crossingIntervals_nondegenerate`) and finitely many crossing
      components (`crossing_components_finite`);
    * the uniform heights (`…_unif`);
    * `SepByCrossing`, `x₂ₙ = 1` and Property 4 for the top block from `InnerComponentsCross` alone
      (`sep_by_crossing_uncond`, `hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`);
    * the blocks from `x₂ₙ = 1` alone (`exists_blocks_uncond`);
    * T15–T17 from `InnerComponentsCross` and the step (`hagopian76_T15_T17_cond3`);
    * T1–T13 assembled (`exists_thm1Setup`), and Theorem 1 from `InnerComponentsCross` and
      `Property4Step` for every set-up (`hagopian76_theorem1_of_step`).
  * **Open:** 2e (`InnerComponentsCross`) with 2a, 2b, 2d; 3c; §6 (`Property4Step`); the
    unconditional Theorem 1 (`OPEN.md`, batch-179 section).
  * **Refuted:** nothing.

**Checks.**

1. **The end layer of `F` (not in the text).** Needed for "`x₂ₙ = 1`" and the top block.

   **Gap in exposition, open.**
   * 3a is proved (batch 178).
   * 2e (`InnerComponentsCross`) is the one remaining input of `hagopian76_x2n_eq_one_final` and
     `hagopian76_property4_top_final`.
   * The route of commission 179 §2 is not formalized. Two points need care (report §1.2):
     * in 2d.5, `c` must lie over `(3/22 + 4/n, 19/22 − 4/n)`;
     * in 2a and 2b, `Z = Λ₁ ∪ h[k⁻¹(τ)]` must be a continuum.
2. **p. 348:**
   > Note that x₁ = 0, x₂ = e, and x₂ₙ = 1.

   **Gap in exposition, reduced to check 1.** 4.B is proved (`p_on_crossing_piece`), so `x₂ₙ = 1`
   now rests only on `InnerComponentsCross` (`hagopian76_x2n_eq_one_final`).
3. **p. 347, Property 3:**
   > No component of F ∩ π⁻¹[D] whose closure meets both π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)] is contained in an element of the decomposition of F.

   **Correct, and sufficient for the nondegeneracy of `I`** (`crossingIntervals_nondegenerate`,
   through `crossingIntervals_nondegenerate_of`). Finding 7 of batch 178 is settled. Nondegeneracy
   also gives finitely many crossing components (`crossing_components_finite`).
4. **The order of the constants (T13 builds `F` from `D`).**

   **Correct.**
   * Every height in Property 3, "`I` is finite", `x₂ₙ = 1` and the middle-crossing lemmas comes
     from `follows_crossing`, `pi_thin_near_layer` or `hagopian76_link_control`. None of these
     mentions `F`.
   * So each height can be fixed before `F` (the `…_unif` theorems).
   * `exists_thm1Setup` chooses the domain height as the minimum of the strand height, these heights
     and the height of T7, before the package is built.
5. **pp. 348–349, Cases 1–2:**
   > Following Bing [2, p. 225], we now show that if I = [x₂ᵢ₋₁, x₂ᵢ] has Property 4, then so does J = [x₂ᵢ₋₃, x₂ᵢ₋₂].

   **Open.** E0 and E1 need 3c, and the rest is not started. By `hagopian76_theorem1_of_step`,
   `Property4Step` for every set-up and `InnerComponentsCross` are exactly what Theorem 1 still
   needs.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXV: the set-up repaired; saturation; 3c; the step (batch 180)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76Y.lean` and two new supporting files:
* `HPC/Hagopian/H76Cond4.lean`: T15–T17 with the composant data of the package exposed;
* `HPC/Hagopian/H76Tip.lean`: §2.1 (the end layer meets the tip layer), 2a, 2b, 2c.

`HPC/Hagopian/H76Thm1Setup.lean` is restated in place (the repaired `Thm1Setup`). The report is
`doc/batches/REPORT-batch180.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXV (batch 180)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the 19 new theorems is `doc/batches/audits/axioms-batch180.txt`.
* **Source.** Hagopian 1976, pp. 346–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:**
    * the certificate for batch 179's set-up (`property4_lower_false_of_K_eq`);
    * the repaired set-up (`Thm1Setup`, `hagopian76_T15_T17_cond4`, `exists_thm1Setup`) and Theorem 1
      from saturation on `(3/22 + 8/n, 19/22 − 8/n)` and the step (`hagopian76_theorem1_of_step`);
    * every crossing piece in `M` meets `K` (`Thm1Setup.K_meets_crossing`);
    * the end layer of `F` meets the tip layer (`tip_meets_end_layer`, `tip_meets_end_layer_mirror`);
    * 2a with its mirror form, 2b with a nonempty third arm, 2c (`tip_triod`, `tip_triod_mirror`,
      `tip_triod_on_tip_layer`, `degenerate_chunk_iii`).
  * **Open:** 2d, 2e (`InnerComponentsCross`), 3c, E0, E1, §4 (`Property4Step`), the unconditional
    Theorem 1 (`OPEN.md`, batch-180 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 347, `K`:**
   > Let K be the component of π⁻¹[D ∩ ⟨p₃, q₃⟩] …

   **Correct; the batch-179 set-up was a project error, not a defect of the text.** Batch 179 used
   `K = {p}`. With that `K`, Property 4 fails for every block below the top
   (`property4_lower_false_of_K_eq`: `d⁻¹[[0, x₂ᵢ₋₂]]` would be a proper extension of `E` separating
   `p` from `f(p)`, against irreducibility), so the induction step could only be met vacuously. The
   properties of `K` the induction uses: it contains `p` (the top block, `yₙ = p`); it meets every
   strand over the inner middle (E2.1, the choice of `yᵢ₋₁`). The repaired set-up takes
   `K = {p} ∪ K₀` with `K₀` the points of `M` over the open low vertical `F[{1/2} × (0, w₂)]`, and
   the second property is `Thm1Setup.K_meets_crossing`.
2. **p. 346, `ε₂`:**
   > Define ε₂ to be the minimum of ε₁ and ρ(M, π⁻¹[I₁ ∪ I₂]).

   **Correct as printed; recorded in the set-up** (`hε₂₁`, `hε₂I`, with `I₁` the side of the strip of
   `hagopian76_I1` at height `−cs/2`). Where Cases 1–2 use it: `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])` keeps the
   continua of E2.2 and E2.4 away from the top arc and from below the axis; `ε₂ ≤ ε₁` is used through
   Property 2 (Lemma 7 at `ε₁`). Neither use is formalized yet (§4 is open). An extra margin
   `5/n + ε₂ < 15/22 − 3/22` (E2.2) is recorded as well (`hε₂V`).
3. **The end layer of `F` (not in the text).** The two points of report 179 §1.2.

   **Gap in exposition, partly closed.** `d⁻¹(1)` meets the tip layer (`tip_meets_end_layer`), so
   `Z = Λ₁ ∪ h[k⁻¹(τ)]` is a continuum and the triods of 2a and 2b are triods (`tip_triod`,
   `tip_triod_on_tip_layer`). The margin of 2d.5 is handled by narrowing saturation to
   `(3/22 + 8/n, 19/22 − 8/n)` with `n = 40`; 2d itself is not formalized.
4. **pp. 348–349, Cases 1–2:**
   > Following Bing [2, p. 225], we now show that if I = [x₂ᵢ₋₁, x₂ᵢ] has Property 4, then so does J = [x₂ᵢ₋₃, x₂ᵢ₋₂].

   **Open.** E0, E1, the cap and Case 2 are not formalized. The set-up now carries the facts the
   steps use (report §1.2); the bound of E2.5.2 (the segment `[yᵢ₋₁, f(yᵢ₋₁)]` inside `π⁻¹[D]`) is
   not implied by the choice of constants and is recorded as a point to check.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXVI: saturation; 3c; Case 1 strand by strand; Case 2 sentence by sentence (batch 181)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76Z.lean` and five new supporting files:
* `HPC/Hagopian/H76Mid.lean`: the middle set `Mid` and the two bounds on `ε₃` (§3.1);
* `HPC/Hagopian/H76Block3c.lean`: 3c by the irreducible interval (§2.1);
* `HPC/Hagopian/H76Cap.lean`: E0/E1 and the cap in the abstract vertical frame (§2.2, §3.2);
* `HPC/Hagopian/H76CapLow.lean`: `f(y) ∈ π⁻¹[D]`, `above_closure_misses_bottom`, the cap lemma and its
  mirror (§3.1, §3.2);
* `HPC/Hagopian/H76TipRel.lean`: the mirror tip lemmas with the hypothesis relaxed (§1.4).

`HPC/Hagopian/H76Thm1Setup.lean` is restated in place (fields `hε₃O`, `hε₃S`). The report is
`doc/batches/REPORT-batch181.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXVI (batch 181)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the new theorems is `doc/batches/audits/axioms-batch181.txt`.
* **Source.** Hagopian 1976, pp. 348–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** the two bounds of §3.1 and `f(y) ∈ π⁻¹[D]` (`exists_eps_mid_O`, `exists_eps_mid_sides`,
    `f_mem_O_of_mem_K`); 3c (`block_components_cross`); E0, E1 (`property4_strand`,
    `property4_step_unless_setup`); the cap lemma (`above_closure_misses_bottom`,
    `cross_strand_near`) and its mirror under a hypothesis (`cross_strand_near_mirror`); the ending of
    Case 1 (`case1_ending`) and claim (c) of Case 2 (`case2_ending`); Case 1, Case 2, the step and
    Theorem 1 conditional on named `Prop`s (`case1`, `case2`, `hagopian76_property4_step_cond`,
    `hagopian76_theorem1_of_cases`); §1.4 step 3 (`chunk_edge_case_mirror`).
  * **Open:** §1.1–§1.3, §1.4 steps 1, 2, 4, 2d, 2e (`InnerComponentsCross`); the claims E2.1, §3.4,
    §3.5, §3.6 (`Case1Claims`), Case 2 (a), (b), (d), (e) (`Case2Claims`), and the case split
    (`BlockLayersMeetSides`) (`OPEN.md`, batch-181 section).
  * **Refuted:** nothing.

**Checks.**

1. **p. 348, the membership of `f(yᵢ₋₁)`:**
   > Note that f(yᵢ₋₁) belongs to L₆ ∩ π⁻¹[D].

   **Correct, with a bound the text does not state.** It follows from `ε₃` small relative to the
   middle set `Mid` (field `hε₃O`, chosen before `F`; `exists_eps_mid_O`) and from `f(y) ∉ E`
   (`f(y) ∈ h₁[R(E)]`, which misses `F ⊇ E` by the composant choice): `f_mem_O_of_mem_K`. It needs
   `h⁻¹(yᵢ₋₁) ∈ R(E)`, which clause (1) of Property 4 gives. The membership in `L₆` is not formalized
   (no step of the formalized ending uses it).
2. **p. 349, "It is not above `d⁻¹[I]` because …":**
   > It is not above d⁻¹[I] because ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃ and ρ(yᵢ₋₁, f(yᵢ₋₁)) < ε₃.

   **Correct, with a gap in exposition, closed.** The segment `[yᵢ₋₁, f(yᵢ₋₁)]` may leave `π⁻¹[D]`.
   It cannot leave through `I₂` (`hε₂I`), nor through the sides (field `hε₃S`), nor through the open
   bottom edge into the region above an `I`-strand (`above_closure_misses_bottom`). So it meets the
   closure of the strand: `cross_strand_near`. The mirror (the point above the strand, the other point
   below) needs in addition that the point be `ε₃`-far from `π⁻¹` of the bottom edge
   (`cross_strand_near_mirror`), which is not uniform on `Mid`.
3. **pp. 348–349, `N` and `π⁻¹(p₄)` versus `N` and `Q`:**
   > Since L − {L₁, L₁₁} follows Cl Cᵢ₋₁ and Cl Cᵢ, the continuum N does not come within ε₂ of π⁻¹(p₄).
   > Since no point of N is within ε₂ of Q, the continuum f[N] does not intersect P.

   **Gap in exposition, open.** The first sentence concerns `π⁻¹(p₄)`; the second uses the distance
   from `N` to `Q`. Neither is formalized. The ending as formalized takes the conclusion of the band
   (`f(yᵢ₋₁)` above `S_I` or below `S_J`) as the field `band` of `Case1Witness`.
4. **p. 348, "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` …":**
   > By considering the position of d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]], we see that yᵢ₋₁ is between d⁻¹[I] and d⁻¹[J].

   **Gap in exposition, open.** The Case 1 hypothesis, the minimality of `L` and `L ∩ F = ∅` do not
   exclude the configuration of report 180 §4.5 (`L` leaves `D` through a side segment and re-enters on
   the other side of a strand's end). The claim is the field `between` of `Case1Witness`.
5. **p. 348, "(Other cases are handled with similar arguments …)":**
   > (Other cases are handled with similar arguments to that given in this case.)

   **Gap in exposition: the cases are not mirror images.** The four configurations are `f(yᵢ)` above or
   below `S_I`, and `d⁻¹[J]` below or above `d⁻¹[I]`. Exchanging "above" and "below" exchanges the
   bottom edge (over `E`) with `I₂`. The cap lemma transfers only under the hypothesis of
   `cross_strand_near_mirror` (distance `≥ ε₃` from `π⁻¹` of the bottom edge). E0 and E1 are symmetric
   (`property4_strand` gives both orders; `VFrame.opposite_of_sepIn`).
6. **p. 349, Case 2:**
   > If yᵢ₋₁ is above d⁻¹[J], it is between d⁻¹[I] and d⁻¹[J], and f(yᵢ₋₁) is above d⁻¹[I]. … Hence
   > yᵢ₋₁ is below d⁻¹[J] and f(yᵢ₋₁) is above.

   **Gap in exposition, open; one claim unsupported.** Claim (c) follows from (b) by the cap lemma
   (proved). Claims (a), (b), (d) are unargued. In (e), nothing printed excludes `f(yᵢ₋₁)` below every
   `J`-strand when `yᵢ₋₁` is; then `J` does not separate at `yᵢ₋₁`. **`x₂ᵢ₋₃`:** reading it as `x₂ᵢ₋₂`
   would contradict the case hypothesis (unless a layer meets both side segments), so it is probably
   not that misprint; as printed it is an extra, unexplained assumption on `d⁻¹(x₂ᵢ₋₃)`, which the
   conditional `case2` does not use.
7. **The end layer of `F` (not in the text), the edge case of saturation.**

   **Gap in exposition, partly closed.** The mirror triod needs only `2/n < σ < 1`
   (`tip_triod_mirror_rel`), so §1.4 step 3 holds whenever `τ₁ < 1` (`chunk_edge_case_mirror`). The
   case `τ₁ = 1` (the end layer contains every point of `F` on the translate beyond the tip layer) is
   undecided; §1.1–§1.3 are not formalized.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXVII: the last step; honest claims; saturation; E2.1 and E2.4 (batch 182)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76AA.lean` and four new supporting files:
* `HPC/Hagopian/H76Last.lean`: the certificate that the case split fails at `i = 2` (§1.1), the
  mirror cap without extra hypothesis (§2.1), the closure of `F − E` (§3.2);
* `HPC/Hagopian/H76Orient.lean`: orientation (§2.2), the last step (§1.2), the restated claims
  (§2.3) and the step (§2.4);
* `HPC/Hagopian/H76Sat182.lean`: the weaker split at `i = 2` (§1.3), the halves `K∓` (§3.1 step 1),
  `L ∩ F = ∅` (§4.1 step 4);
* `HPC/Hagopian/H76Tight.lean`: the assembly over tight block sequences (report §2.4).

The report is `doc/batches/REPORT-batch182.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXVII (batch 182)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the new theorems is `doc/batches/audits/axioms-batch182.txt`.
* **Source.** Hagopian 1976, pp. 348–349 (`doc/sources/hagopian1976.pdf`).
* **Outcome.**
  * **Proved:** `blockLayersMeetSides_false`; `cross_strand_near_above`; the cap, E1 and both endings
    in both orientations; `last_step_ending`, `not_property4_x3x4`; `closure_G_diff_E`;
    `Thm1Setup.kminus_isContinuum`, `Thm1Setup.kplus_isContinuum`, `Thm1Setup.half_bump`,
    `Thm1Setup.half_bump_side`; `Thm1Setup.extension_misses_G`, `Thm1Setup.comp_disjoint_G`; `exists_thm1Setup_tight`; the step
    and Theorem 1 conditional on named `Prop`s without the antecedent `¬ Property4 J`
    (`hagopian76_property4_step_cond2`, `hagopian76_theorem1_of_cases2`).
  * **Open:** the case split for `i ≥ 3`; §3.1 steps 4–5; the points `zⱼ`; `τ₁ = 1`; 2e; E2.1
    steps 1–3, 5; E2.4; Case 2 (e) (`OPEN.md`, batch-182 section).
  * **Refuted:** the batch-181 *formalization* `BlockLayersMeetSides` (not a statement of Hagopian's).

**Checks.**

1. **p. 348, the case split:**
   > Let X and Z be the end sets of Cl Cᵢ. The proof now breaks down into two cases.
   > Case 1. Suppose d⁻¹(x₂ᵢ₋₁) and d⁻¹(x₂ᵢ₋₂) intersect the same element of {π⁻¹[⟨p₁, r⟩], π⁻¹[⟨p₅, s⟩]}.

   **Gap in exposition: fails at `i = 2`; unargued for `i ≥ 3`.** At `i = 2`, `d⁻¹(x₂) = d⁻¹(e) = k⁻¹(1)`
   lies over `γ(1) = F(1, 0)` and meets neither side segment (`blockLayersMeetSides_false`); also
   `d⁻¹[J] = E` misses `π⁻¹[D]`, so there are no `J`-strands. The step at `i = 2` must show that
   `[x₃, x₄]` does not have Property 4; read with the bottom edge in place of the `J`-strand, the ending
   of Case 1 goes through (`last_step_ending`), conditional on the Case 1 claims for that step
   (`LastStepClaims`). For `i ≥ 3` the split is the named `Prop` `BlockLayersMeetSides3`, open.
2. **p. 348, the parenthesis:**
   > For convenience we suppose d⁻¹[J] is below d⁻¹[I] and f(yᵢ) is above d⁻¹[I]. (Other cases are
   > handled with similar arguments to that given in this case.)

   **Correct where the cap is used; two configurations not covered.** The mirror cap needs no extra
   hypothesis (`cross_strand_near_above`: the segment meets the frontier of the region *above* the
   strand, which misses the open bottom edge); the cap, E1 and both endings hold in both orientations
   (`case1_ending_oriented`, `case2_ending_oriented`). This corrects batch-181 check 5. The two
   configurations with `d⁻¹[J]` on the side of `f(yᵢ)` leave, after E1, the case "`f(yᵢ)` between
   `d⁻¹[I]` and `d⁻¹[J]`", which is not a mirror image of the printed one (the point of `K` is `yᵢ`, not
   `f(yᵢ)`); not treated.
3. **p. 348, the existence of `Cᵢ₋₁`:**
   > Let Cᵢ₋₁ be the first component of M ∩ π⁻¹[D] (whose closure intersects π⁻¹[⟨p₁, r⟩] and
   > π⁻¹[⟨p₅, s⟩]) that is met by extending Cl Cᵢ away from X in M. The existence of Cᵢ₋₁ follows from
   > the indecomposability of Cl R(X, Cl Cᵢ) (Lemma 6 (proof)) and an argument similar to the one for
   > Property 3. Note that Cl Cᵢ₋₁ is essential to h[R(E)]. Let L be the shortest extension of Cl Cᵢ
   > away from X that contains Cᵢ₋₁.

   **Gap in exposition, open; one step closed.** `L ∩ F = ∅` (used later) holds for every extension
   through a point of `h[R(E)]`, and `yᵢ` is such a point (`Thm1Setup.extension_misses_G`). The existence
   of a crossing component of `M` met by an extension, the "first" one and the shortest `L` are not
   formalized: the Property 3 argument concerns crossing components of `F`.
4. **p. 348, E2.4:**
   > The point yᵢ₋₁ is below Cᵢ and ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃; for otherwise, a subcontinuum of L would
   > violate Property 2.

   **Gap in exposition, open.** Of the hypotheses of Property 2: "essential to `h[R(E)]`" holds for
   subcontinua of `L` containing `Cl Cᵢ`; "minimal admissible decomposition" needs the restriction of the
   decomposition of `L`; "end sets within `ε₃`" is not implied by the two distances to `d⁻¹[I]` (the
   points may be near `S_I` at different heights, and `L` misses `F`); "a layer farther than `ε₂` from
   the first end set" needs the passage of `L` around a strand. Not decided.
5. **p. 349, Case 2 (e):**
   > Hence yᵢ₋₁ is below d⁻¹[J] and f(yᵢ₋₁) is above. Therefore J has Property 4.

   **Unsupported, open.** Extending `Cl Cᵢ` away from `Z` instead of `X` does not change the position
   of the gap continuum, which in Case 2 meets both side segments, so it does not reduce to Case 1.
   Property 2 for `f[N]` (essential to `h₁[R(E)]`) gives a reach, not a side. Batch-181 check 6 stands.
6. **The end layer of `F` (not in the text):**

   **Partly closed.** The closure of `F − E` meets `E` only in `k⁻¹(1)` (`closure_G_diff_E`); the halves
   `K∓` are continua, boundary bumping applies in them, and the bumped point lies over a side segment
   (`kminus_isContinuum`, `half_bump`, `half_bump_side`). The case
   `τ₁ = 1` is still undecided.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXVIII: Bing's reasons for Cases 1–2; E2.4; the orientation; saturation (batch 183)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76AB.lean` and two new supporting files:
* `HPC/Hagopian/H76Restrict.lean`: the subcontinuum of a minimal admissible continuum between two
  layers, with the layers kept (§2 step 3);
* `HPC/Hagopian/H76E24.lean`: E2.4 by Bing's arc `ab` (§2 steps 1–2, the violation of Property 2).

The report is `doc/batches/REPORT-batch183.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXVIII (batch 183)* of `Axioms.lean` / `axioms.txt`; standard
  axioms only. The audit of the new theorems is `doc/batches/audits/axioms-batch183.txt`.
* **Sources.** Hagopian 1976, pp. 348–349 (`doc/sources/hagopian1976.pdf`); Bing 1960, pp. 224–228
  (`doc/sources/bing1960.pdf`, PDF pages 16–20, read from page images at 200 dpi).
* **Outcome.**
  * **Proved:** the pair `a`, `b` of E2.4 in both of Bing's configurations (`e24_pair_between`,
    `e24_pair_below`); the restriction with layers kept (`minimalAdmissible_restrict_of_lsc`,
    `minimalAdmissible_restrict`); the violation of Property 2 from the three remaining claims
    (`property2_violation`); E2.4 from the named `Prop` `E24Claims` (`e24_between_false`,
    `e24_below_far`, `E24Data.far`); Theorem 1 with the fields `far` and `claim_d` replaced by the
    data of E2.4 (`hagopian76_theorem1_of_cases3`).
  * **Open:** "between" (§3); Case 2 (a), (b), (e) (§4); the two other orientations (§5, the
    proposal fails as stated); E2.1 steps 1–3, 5; saturation; the split by `Γ` (`OPEN.md`, batch-183
    section).
  * **Refuted:** nothing.

**Checks.**

1. **pp. 348–349 against Bing 1960 pp. 225–227.**
   > Following Bing [2, p. 225], we now show that if I = [x₂ᵢ₋₁, x₂ᵢ] has Property 4, then so does
   > J = [x₂ᵢ₋₃, x₂ᵢ₋₂]. (Hagopian, p. 348)

   **Bing is the model, sentence by sentence; three of his reasons carry over, two do not.** The
   dictionary of commission 183 §1 agrees with the pages (`doc/notes/hagopian76-cases.md`, E5). Bing's
   `M′` has every proper subcontinuum an arc, and his strands are arcs ending on the side lines at the
   points `x₂ᵢ`, `x₂ᵢ₊₁` where the gap arc starts. Carry over: the arc `ab` (E2.4, check 2); the
   subarc between two points (with Lemma 5, check 2); the separation of the two sides of the side
   subsegment (check 4, in part). Do not carry over: the strand ends on the side lines (check 4); the
   parity argument for the simple closed curve `J` (check 5). A small inconsistency in Bing (p. 227): he
   supposes "ρ(q, x₂ᵢ₋₁x₂ᵢ) ≥ ε₄" and then writes "It is not above x₂ᵢ₋₁x₂ᵢ because
   ρ(q, x₂ᵢ₋₁x₂ᵢ) > ε₄ and ρ(q, h(q)) < ε₄"; the weak inequality suffices there.
2. **p. 348, E2.4: the subcontinuum is Bing's `ab`, not `N`.**
   > The point yᵢ₋₁ is below Cᵢ and ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃; for otherwise, a subcontinuum of L would
   > violate Property 2. (Hagopian, p. 348)

   > If q were above tu, we would take p = a and let b be a point of vw between p and x₂ᵢ₋₁x₂ᵢ. If q
   > were below tu and ρ(q, x₂ᵢ₋₁x₂ᵢ) < ε₄, we would take q to be b and a to be a point of tu between q
   > and x₂ᵢ₋₁x₂ᵢ. (Bing, p. 227)

   **Gap in exposition; steps 1–3 closed, steps 4–6 named.** The pair: `e24_pair_between` (`a = yᵢ`,
   `b ∈ Cl Cᵢ₋₁`), `e24_pair_below` (`b = yᵢ₋₁`, `a ∈ Cl Cᵢ`), each with `ρ(a, b) < ε₃`, from the cap
   lemma. `H` = the part of `L` between the layers through `a` and `b`, with the layers kept
   (`minimalAdmissible_restrict`; in a general metric space this needs the lower semicontinuity that
   Lemma 5 supplies in `M`). Its end sets contain `a` and `b`, so they are within `ε₃`. Given a far layer,
   essentiality and `FarFrom`, Property 2 is violated (`property2_violation`). The second case is stated
   for the `I`-strand `S_I` adjacent to `Cᵢ`; for an `I`-strand below `Cᵢ` the argument does not reach
   the printed `d⁻¹[I]`, and the printed form is not decided.
3. **p. 348, "`N` does not come within `ε₂` of `π⁻¹(p₄)`", and Bing's "no point of the arc `pq`
   …".**
   > Since L − {L₁, L₁₁} follows Cl Cᵢ₋₁ and Cl Cᵢ, the continuum N does not come within ε₂ of
   > π⁻¹(p₄). (Hagopian, p. 348)

   > Note that no point of the arc pq in M is within ε₄ of this vertical part of J above a₄. (Bing,
   > p. 227)

   **Unargued in both; open.** Stated for `H` as the named `Prop` `Thm1Setup.FarFrom` (part of
   `E24Claims`). The chain `L` follows `Cl Cᵢ₋₁` and `Cl Cᵢ` only inside `π⁻¹[D]`; outside `D`, `L` may
   enter a pocket of the complement near `p₄` from the far side, and nothing proved excludes it.
4. **p. 348, "between" (Case 1).**
   > By considering the position of d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]], we see that yᵢ₋₁ is between d⁻¹[I] and
   > d⁻¹[J]. (Hagopian, p. 348)

   > It follows from the Jordan curve theorem that q lies between x₂ᵢ₋₁x₂ᵢ and x₂ᵢ₊₁x₂ᵢ₊₂. (Bing,
   > p. 226)

   **Gap in exposition, open; Bing's reason carries over in part.** The two sides of the part `σ` of the
   side segment between the strands' ends lie in different components of the complement of
   `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ σ`. Open: that the outer component meets `π⁻¹[D]` only through `σ`. If near an
   end of a strand `F` has no points outside `D`, the outer component passes around that end, and the
   batch-180 configuration is not excluded. Bing's arcs end on the side line exactly where the gap arc
   starts; that is what is missing for continua.
5. **p. 349, Case 2 (a), (b), (e); `p₂` versus `p₄`.**
   > If yᵢ₋₁ is above d⁻¹[J], it is between d⁻¹[I] and d⁻¹[J], and f(yᵢ₋₁) is above d⁻¹[I]. … Hence
   > yᵢ₋₁ is below d⁻¹[J] and f(yᵢ₋₁) is above. (Hagopian, p. 349)

   > As a point moves from p to q, the image of the point under h does not intersect J. Hence, h(q) is
   > either above x₂ᵢ₋₁x₂ᵢ or below x₂ᵢ₊₁x₂ᵢ₊₂. (Bing, p. 227)

   > … it follows as in Case 1 that tuvw contains an arc ab such that ρ(a, b) < ε₄, diameter ab > ε₃,
   > ρ(ab, a₂) > ε₃. (Bing, p. 227)

   **Open; (d) reduced.** (a): as check 4. (b), (e): for Bing's simple closed curve `J`, the side of
   `h(q)` follows from crossing parity along the vertical through `a₃`, whatever route the gap arc
   takes, so the `E`-side route is not a gap in Bing (except that the gap arc might enter `K`, which
   Bing does not discuss). For the continuum `P` there is no parity argument, and the Janiszewski form
   separates the sides of `Q`, not of `S_I`. (d): reduced to `E24Data` with `π⁻¹(p₂)` (`r = 7/22`),
   following Bing's `a₂`; Hagopian's `π⁻¹(p₄)` in Case 2 is not used.
6. **p. 348, "(Other cases …)": Bing's disc against Hagopian's arc `K`.**
   > (Other cases are handled with similar arguments to that given in this case.) (Hagopian, p. 348)

   **Gap, open; the commission's proposal fails as stated.** `f(yᵢ)` need not lie in `Mid` (abscissae in
   `(3/8, 5/8)` only), and the cap from `f(yᵢ)` uses the `ε₃` fields stated on `Mid`; the essentiality
   of the component of `f(yᵢ)` to `h₁[R(E)]` does not follow from that of `Cl Cᵢ` to `h[R(E)]`. Bing's
   `K` is a disc and contains both `p` and its neighbours; Hagopian's `K` is an arc.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976 XXX: saturation by the 1984 Lemma 7; the case split for `i ≥ 3`; runs (batch 185)

The formalization is in the skeleton `HPC/Hagopian/Hagopian76AC.lean` and five supporting files:
`HPC/Hagopian/H84TwoSided.lean` (the two-sided extension), `HPC/Hagopian/H84Lemma7.lean` (Lemma 7 of
1984), `HPC/Hagopian/H84Rigid.lean` (rigidity, runs), `HPC/Hagopian/H76Sat185.lean` (saturation),
`HPC/Hagopian/H76Split185.lean` (the case split). The report is `doc/batches/REPORT-batch185.md`.
Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1976 XXX (batch 185)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the new theorems is `doc/batches/audits/axioms-batch185.txt`.
* **Sources.** Hagopian 1976, pp. 347–348 (`doc/sources/hagopian1976.pdf`); Hagopian 1984,
  pp. 336–337 (`doc/sources/hagopian1984.pdf`).
* **Outcome.**
  * **Proved:** saturation (2e) for Hagopian's `F` on `(3/22 + 8/n, 19/22 − 8/n)`, unconditionally
    (`innerComponentsCross_hagopian`), through the tip by Lemma 7 (`half_in_O_false`) and steps 4–5 of
    `noncrossing_half_in_O` (`noncrossing_half_in_O_steps45`); the case split for `i ≥ 3` with tight
    blocks (`blockLayersMeetSides3`); Theorem 1 from `StepFrame`, `LastStepClaims`, `Case1ClaimsE24`,
    `Case2ClaimsE24` alone (`hagopian76_theorem1_of_cases4`).
  * **Open:** §3.3 (runs of `F` along a translate) and §6 ("between" with runs); the four named
    `Prop`s of `hagopian76_theorem1_of_cases4` (`OPEN.md`, batch 185).
  * **Refuted:** nothing.

**Checks.**

1. **p. 347, the collection `I`, and the end layer of `F` (not in the text).**
   > Let `I` be the collection of all intervals `[x, y]` such that `d⁻¹[[x, y]]` is irreducible with
   > respect to containing a component of `F ∩ π⁻¹[D]` whose closure meets `π⁻¹[(p₁, r)]` and
   > `π⁻¹[(p₅, s)]`.

   **Gap in exposition (batches 178–184), closed.** The argument needs that every component of
   `F ∩ π⁻¹[D]` through the middle crosses `D` (saturation, 2e). Its last case — a half
   `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` inside `π⁻¹[D]`, whose tip layer meets the end layer `d⁻¹(1)` of `F`
   (`tip_meets_end_layer`) — was open since batch 178 (this ledger, batch 181 check 7: "`τ₁ = 1` …
   undecided"). It is closed by Lemma 7 of Hagopian 1984 (p. 336), applied to the translate `h[E]`
   and `F`: the tip layer `h[k⁻¹(τ)]` is a layer of `F`, hence equal to `d⁻¹(1)`, which would then lie
   over `D`, against `T12Data.end_layer_not_subset`. Lemma 7 is proved here by a route different from
   the printed one (Hagopian 1984 check H84.15 below). The text of 1976 replaced: none is printed; the
   repository's chunk argument (the points `zⱼ`, the chunk, the edge case `F ∩ hⱼ[E] ⊆ Tⱼ`, `τ₁ = 1`,
   batches 179–183) is no longer needed. The earlier tip results are kept.
2. **p. 348, "The proof now breaks down into two cases".**
   > The proof now breaks down into two cases. … Suppose `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` intersect the
   > same element of `{π⁻¹[⟨p₁, r⟩], π⁻¹[⟨p₅, s⟩]}`.

   **Presupposition true for `i ≥ 3`, false at `i = 2`.** That each of the two layers meets a closed
   side segment is unargued. For tight blocks and `3 ≤ i ≤ m` it holds (`blockLayersMeetSides3`; route
   of commission 185 §5: the block ends are ends of members of `I`; a crossing component whose
   interval starts at `x₂ᵢ₋₁` has `d⁻¹(x₂ᵢ₋₁) ⊄ π⁻¹[D]` by upper semicontinuity, so the layer meets
   `Fr π⁻¹[D]`, over a side segment since it misses `E` and `I₂`). Lemma 7 is not used. At `i = 2` it
   is false (`blockLayersMeetSides_false`, batch 182). Which side each layer meets is not determined
   by the argument. This also locates `d⁻¹(x₃)` (notes E3): it meets a closed side segment
   (`layer_x3_meets_side`, the left-end argument at `i = 2`).
3. **p. 348, "between"** (commission 185 §6).
   > By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see that `yᵢ₋₁` is between `d⁻¹[I]` and
   > `d⁻¹[J]`

   **Open; one input proved.** The runs of commission 185 §3.2 hold for any type λ continuum against
   `F` (`translate_run`, `translate_run_right`: an end of the common segment that is not an end of the
   translate is an end layer of `F`). §3.3 (that `F` leaves `D` along the strand's translate) is open:
   the common segment exists (`strand_lemma`, `layers_agree`), but the degenerate case of
   `layers_agree` and the end layer `d⁻¹(0)` are not excluded, and no form usable for "between" was
   found (report §3.3, §6).

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1976: Theorem 1 classified (batch 191)

**Hagopian 1976, Theorem 1: proof defective, statement true.** The printed proof fails at an
identified step, the case split at `i = 2` of p. 348 (`blockLayersMeetSides_false`, batch 182; see
check 2 of the batch-185 subsection above). The statement is verified by another route:
`hagopian76_theorem1 : Hagopian76Thm1` (batch 190, through `jones75_noArc`). The precedents are Moore
1916 Theorem 28 (a last step corrected) and Jones 1975's Theorem (a statement proved by a different
proof). **The sixteenth defective proof of the ledger** (count corrected in batch 191; see the
note at the end of the Jones 1975 I subsection).

### Hagopian 1984 I: Jones's plan; the plane quotient; Lemmas 1, 6, 11; the unargued steps (batch 184)

C. L. Hagopian, *Atriodic homogeneous continua*, Pacific J. Math. 113 (1984), 333–347
(`doc/sources/hagopian1984.pdf`, journal page = PDF page + 331, read from page images at 200 dpi).
The paper re-proves Theorem 1 of Hagopian 1976 by F. B. Jones's plan (p. 346). Transcription,
dictionary and route: `doc/notes/hagopian84.md`. The formalization is in
`HPC/Hagopian/Hagopian84A.lean` and `HPC/Hagopian/H84Quot.lean`; the report is
`doc/batches/REPORT-batch184.md`. Names are in namespace `HPC.Hagopian`.
* **Axioms.** Group *Hagopian 1984 I (batch 184)* of `Axioms.lean` / `axioms.txt`; standard axioms
  only. The audit of the new theorems is `doc/batches/audits/axioms-batch184.txt`.
* **Outcome.**
  * **Proved:** the assembly `hagopian76_theorem1_of_jones` (from the named `Prop`s
    `Hagopian84Decomp` and `NoArcIndecHomPlane`); the plane quotient
    `exists_plane_quotient_of_monotone`; `indecomposable_of_monotone_image`;
    `hagopian75_theorem1_of_noArc`; Lemma 1 (`hagopian84_lemma1`); Lemma 6 (`hagopian84_lemma6`);
    Lemma 11 with `N = M` (`hagopian84_lemma11`).
  * **Open:** Lemmas 7, 8, 10, 12–16, the arc in `M/𝔇`, Theorem 1 with `N = M`
    (`Hagopian84Decomp`), the arc step (`NoArcIndecHomPlane`). See `OPEN.md`, batch 184.

**Checks.**

1. **H84.1, p. 335, the citation for "the decomposition".**
   > If a continuum `M` is of type λ, then `M` admits a unique monotone upper semi-continuous
   > decomposition `𝔇` such that `M/𝔇` is an arc and each element of `𝔇` has a void interior
   > relative to `M` [19, Theorem 3, page 216] [26, Theorem 10, page 15].

   **Citation as in Hagopian 1975 Lemma 2; claim true.** The same pair of references is given in
   Hagopian 1975, Lemma 2 (this ledger, Hagopian 1975, check 5), where Kuratowski's Theorem 3 gives
   the order type of the family `D`, not the decomposition; the gap was filled there (`H75Kur`,
   `H75KurScale`, `H75KurMap`). Uniqueness: `hagopian75_lemma3_unique`. The route uses type λ only in
   the decomposition form (`IsMinimalAdmissible`), so the equivalence with Kuratowski's definition is
   not needed.
2. **H84.2, Lemma 2 applied to unions** (pp. 337, 338, 342, 343).
   > By Lemma 2, `F ∩ J` is a subcontinuum of `J`. (p. 337)

   > By Lemma 2, `F`, `f[F]`, and `g[F]` are disjoint. (p. 338)

   **Unargued for a general atriodic `M`; harmless here.** Lemma 2 (`M` hereditarily unicoherent) is
   applied to `F ∪ J`, `N ∪ F`, `K ∪ L`, `I ∪ d⁻¹[[t, v]]`. In the repository's setting (an
   indecomposable homogeneous plane continuum) every nondegenerate subcontinuum, `M` included, is
   unicoherent (`hagopian75_lemma1_hu`), so no properness is needed. For a general atriodic `M`
   ([20, Theorem 13.8] as cited) the unions must be proper or `M` unicoherent; in Lemma 7,
   `F ∪ J ⊂ I ∪ H` is not argued to be proper.
3. **H84.3, Lemmas 6 and 9: the citations.**
   > *Proof.* Lemma 6 follows from Lemma 5 and the irreducibility properties of `E` [26, Theorem 8,
   > page 14]. (p. 336)

   > *Proof.* Lemma 9 follows from paragraphs 5 through 12 in the proof of Theorem 1 of [10]. (p. 338)

   **Lemma 6: proved without [26]** (`hagopian84_lemma6`, from Lemma 5, `isTypeA'_of_subcontinuum`,
   `minimalAdmissible_restrict`, `hagopian75_lemma3_unique`). **Lemma 9: citation covers part.** The
   cited paragraphs of Hagopian 1975 (`hagopian75_layer_homogeneous`) treat the layers over interior
   points; Lemma 9 claims every element, end sets included. An end set of `E` is an interior layer of
   an extension of `E` (Lemma 4), so the claim holds; the step is not stated. Not formalized.
4. **H84.4, Lemma 7.**
   > Since `M` is atriodic, it follows from (1) that there is a point `x` of `F` in `H∖k⁻¹(r)`.

   > Suppose that (2) is false. Then `F ∩ J` does not contain `k⁻¹(r)`. Hence `F ∩ J` is a proper
   > subcontinuum of `J`. Since `x ∈ F ∩ J` and `F ∩ J` intersects `k⁻¹(r)`, this contradicts the fact
   > that `J` is irreducible between `x` and `k⁻¹(r)`.

   **Gaps in exposition; open.** (a) The point `x`: if `F ⊂ H` it exists because `F ⊄ k⁻¹(r)`; if not,
   `k⁻¹(r)` with the two sides in `H` and a piece of `F∖H` would form a triod; not argued. (b) The
   irreducibility of `J` "between `x` and `k⁻¹(r)`" is point-to-end-set irreducibility of a type λ
   continuum; true (`isTypeA'_of_subcontinuum` gives the needed form in `M`). (c) "(2) false" gives a
   point of `k⁻¹(r)` in `I∖F`, hence not in `F ∩ J`: one line missing, correct. The step "Since `M` is
   atriodic and `F ∩ k⁻¹(r) ≠ ∅`, it follows from (2) that `k⁻¹(r) ⊂ F`" is also unargued. The
   formalization is blocked by the two-sided extension (Lemma 4 used to make `E`, `F` miss both end
   sets of `H`, `I`), open since batch 158.
5. **H84.5, Lemma 8.**
   > The quotient space `(E ∪ F)/𝔇` is the union of two arcs. Since `M` is atriodic, `(E ∪ F)/𝔇` is
   > atriodic. … It follows from Lemma 2 that `(E ∪ F)/𝔇` does not contain a simple closed curve.
   > Thus `(E ∪ F)/𝔇` is an arc

   **Gaps in exposition; true; open.** The union of two arcs is `E/𝔇 ∪ F/𝔇`. "Atriodic" needs that the
   monotone preimage of a triod is a triod: true, since preimages of subcontinua under a closed monotone
   map are subcontinua (`isContinuum_preimage_of_monotone`, proved this batch); not stated. "Hence an
   arc" needs that an atriodic union of two arcs containing no simple closed curve is an arc; not
   argued.
6. **H84.6, Lemma 12.**
   > Since `𝔏` is regular, `E∖(A ∪ B)` is an essential subcontinuum of `E`. Since `M` is atriodic,
   > `E∖(A ∪ B)` is a component of `M∖(A ∪ B)`.

   > The chain `𝒫 = {Pᵢ: 1 ≤ i ≤ 5}` is a free normal regular ordered refinement of `𝔏`. Note that `E`
   > runs straight through `𝒫`.

   **Unargued; open.** Moore 1962 Theorem 44 [22] is available in the compact form
   (`exists_closed_split_of_no_connected`, used for the 1976 Lemma 8). The three quoted sentences are
   not argued; that `E∖(A ∪ B)` is a continuum uses (2), (3) and (5) of "runs straight".
7. **H84.7, Lemma 13.**
   > It follows from the definition of `δ` that `r ∈ [x₂, x₁₃]∖[x₃ᵢ₋₃, x₃ᵢ]`. … By Lemma 3,
   > `g[k⁻¹(s)] = h[k⁻¹(r)]`.

   > Since `M` is atriodic, it follows from (6) and Lemma 6 that `Cl K` is an essential subcontinuum
   > of `h[E]` that runs straight through `𝔏`.

   **Gaps in exposition; open.** The hypotheses of Lemma 3 (the layer `h[k⁻¹(r)]` misses the end sets
   of `g[E]`, and `g[k⁻¹(s)]` misses those of `h[E]`) follow from `r, s ∈ [x₂, x₁₃]` and the `½ρ`
   bound in `δ`; not said. In (4), the `μ`-homeomorphism `f` with `fh` a δ-homeomorphism and
   `f(p) ∈ Lᵢ` comes from Lemma 1 with the slack of `h` (as in `hagopian84_lemma1`); not said. (5) has
   a misprint (`g[k⁻¹(0, x₃ᵢ)]]`). The last paragraph needs that every component `K` of `⋃𝒫′` meets
   some `h[E]` with `h` a δ-homeomorphism: `⋃𝒫′ ⊂ ⋃𝔏′`, and `L₂ ∪ L₃ ∪ L₄` is a union of sets
   `W(·, δ)` of points of `E`; one line missing.
8. **H84.8, Lemmas 14 and 15.**
   > Let `ε` be any positive number less than `½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`. … By Lemma 3, if `zᵢ` belongs to the
   > open set `W(z, ε)` (Lemma 1), then there is an ε-homeomorphism `h` of `M` onto `M` such that
   > `h[Z] = Zᵢ`. Since `ε` is arbitrarily small, `{Zᵢ}` converges to `Z`.

   **Unargued; open.** `⋃Δ(𝒫)` is not closed, and `½ρ(⋃Δ(𝒫), M∖⋃𝒫′) > 0` needs
   `Cl ⋃Δ(𝒫) ⊂ ⋃𝒫′`, which uses freeness and normality; not argued. The hypotheses of Lemma 3 (`h[Z]`
   misses the end sets of `Cl Kᵢ`, which lie in `M∖⋃𝒫′`; `Zᵢ` misses the images of the end sets of
   `Cl K₀`) are not checked. Convergence is in the Hausdorff sense (`h[Z] = Zᵢ` with `h` an
   ε-homeomorphism gives Hausdorff distance `< ε`), which gives upper and lower semicontinuity at `Z`.
   Lemma 15 uses Lemma 3 in the same way.
9. **H84.9, Lemma 16.**
   > Since `𝔇` is continuous (Lemma 5), `s ∉ S` and `s ≠ 1`.

   > Since `𝒫` is free, there exist a 3-linked subchain `𝔔` of `𝒫` and numbers `t`, `w` greater than
   > `s` such that (1) …

   **First sentence: gap, true. Second: unargued; open.** `S` is open in `[0, 1]` (meeting three open
   links is an open condition by lower semicontinuity, `lsc_of_minimalAdmissible`), so `s = inf S ∉ S`;
   `s ≠ 1` as `S ≠ ∅`. The existence of `𝔔`, `t`, `w` from freeness is not argued. The final appeal to
   uniqueness is correct (`hagopian75_lemma3_unique`).
10. **H84.10, Theorem 1, pp. 342–344.**
    > Let `X(Z)` be the end set of `Cl K(Z)` that is separated from `Z` in `Cl K(Z)` by `P₃`. By
    > Lemma 11, `Cl ⋃𝔖(X(Z), Cl K(Z))` is an indecomposable subcontinuum of `N`. Thus
    > `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`.

    **Gaps in exposition; open.** (i) `X(Z)`: `Z ∉ Δ(𝒫)` meets `Cl(P₁ ∪ P₅)`, and by "runs straight"
    `Z` lies on one side of `P₃`; not argued. (ii) Lemma 11 is applied to `Cl K(Z) ⊂ h[E]`, not to `E`;
    for general `N` this needs `Cl K(Z) ⊂ N` (so `h[N]` in place of `N`, or Lemma 10 first); with
    `N = M` it is automatic. (iii) "Thus …": the commission's reading is right — otherwise
    `Cl ⋃𝔖 ∩ P₃` is a nonempty open subset of `Cl ⋃𝔖` inside its proper subcontinuum `Cl K(Z)`, which
    an indecomposable continuum does not have. (iv) "Hence there is an essential subcontinuum `J(Z)`"
    (Lemmas 7, 16): detail not given. (v) The cover ("it follows that `⋃𝔅` is a closed open subset of
    `M`") and disjointness ("by (2), (3), and Lemma 7, `A = B`"; "Thus, by Lemma 3, `A = B`"): as
    printed, with the hypotheses of Lemma 3 again not checked. The elements of `𝔇` are proper
    subcontinua (layers of type λ continua, with void interior).
11. **H84.11, p. 344, the arc in `M/𝔇`.**
    > Since `M/𝔇` is an atriodic homogeneous continuum that contains an arc, `M/𝔇` is a solenoid [20,
    > Theorem 14.4].

    **Unargued; open.** Proposed argument (report §5.7): for a component `K` of `⋃𝒫′`, the layers of
    `Cl K` inside `P₃` miss `Cl(P₁ ∪ P₅)` (normality), so they are elements of `Δ(𝒫) ⊂ 𝔇`; if they fill
    a nondegenerate interval of the decomposition of `Cl K`, their union maps onto an arc. That the
    interval is nondegenerate is the step still to be shown.
12. **H84.12, p. 346, planarity of `M/𝔇`.**
    > In Theorem 2 (above), since the elements of `𝔇` are tree-like, if `M` is planar, then `M/𝔇` is
    > planar [21].

    **Citation does not state the claim; claim true; gap filled.** Moore 1925 [21] needs elements that
    do not separate the plane; that a tree-like continuum does not separate the plane is not stated.
    The route uses instead that the elements are proper subcontinua of `M`, which do not separate the
    plane (`no_proper_subcontinuum_separates`), with Moore 1925 Theorem 22 (`m25_theorem22`):
    `exists_plane_quotient_of_monotone`, proved. Upper semicontinuity of the plane decomposition needs
    only compactness (`fibre_usc`), not the continuity of `𝔇`.
13. **H84.13, Corollary 3 through Theorem 2.**
    > Hence Theorem 2 provides the decomposition that Jones requested

    **Agrees; the route differs.** Theorem 2 assumes "`M` is not a solenoid"; for an indecomposable plane
    continuum this is not checked in the paragraph (a solenoid contains an arc, so it needs Bing's
    theorem again, or the non-planarity of solenoids other than the circle). The route uses Theorem 1 with `N = M`
    (`Hagopian84Decomp`), which needs no such hypothesis; if `𝔇` has only points, `M/𝔇 = M`.
14. **H84.14, small slips.**
    > opens sets (p. 333); ε-circluar (p. 334); ε-homomorphisms (p. 338)

    > In 1968 F. B. Jones [16] suggested … (p. 346)

    **Misprints.** "opens", "circluar", "homomorphisms" (for homeomorphisms); "subcontinuum `H` and
    `K`" (p. 335); Lemma 13 (5) `g[k⁻¹(0, x₃ᵢ)]]`. The year 1968 disagrees with "(1969)" in reference
    [16] (p. 347) and with the 1976 abstract ("At the Auburn Topology Conference in 1969").

No statement of Hagopian's is refuted. No proof of the 1984 paper is classified defective in this
batch (the unargued steps of checks 2, 4–11 are gaps in exposition, or open). The count of defective
proofs stays at fourteen.

### Hagopian 1984 II: Lemma 7; the two-sided extension; rigidity (batch 185)

Same paper and pages (pp. 336–337). The formalization is in `HPC/Hagopian/H84TwoSided.lean`,
`HPC/Hagopian/H84Lemma7.lean`, `HPC/Hagopian/H84Rigid.lean`, stated in
`HPC/Hagopian/Hagopian76AC.lean`; the report is `doc/batches/REPORT-batch185.md`.
* **Outcome.**
  * **Proved:** the two-sided extension (`hagopian84_two_sided`); Lemma 7 (`hagopian84_lemma7`, and
    the named `Prop` `Hagopian84Lemma7` by `hagopian84Lemma7_holds`); rigidity (`layers_agree`); runs
    (`translate_run`, `translate_run_right`); `Wset84 = Wset` (`wset84_eq_wset`).
  * **Open:** Lemmas 8, 10, 12–16, the arc in `M/𝔇`, Theorem 1 with `N = M`, the arc step (as batch
    184).

**Checks.**

15. **H84.15, Lemma 7 (p. 336–337), the route.**
    > By Lemma 4, there is a continuum `H` of type λ in `M` such that (1) `E` is an essential
    > subcontinuum of `H` that misses both end sets of `H`.

    > Since `M` is atriodic and `F ∩ k⁻¹(r) ≠ ∅`, it follows from (2) that `k⁻¹(r) ⊂ F`. Therefore,
    > since `M` is atriodic and `E∖F ≠ ∅`, there is a point `y` of `E∖k⁻¹(r)` in `I∖F`.

    **Lemma true; the printed proof has the gaps of H84.4; proved by another route.** (1) is "By
    Lemma 4" only in the sense that Lemma 4 gives extensions away from each end set; the two-sided
    `H` needs `F₁ ∩ F₂ = E` and a glued decomposition, not stated. Both are proved
    (`ext_inter_ext_subset`: the intersection is a continuum by hereditary unicoherence and the tails
    beyond the two end sets meet `E` in different end sets; `glue_minimalAdmissible`: the union of two
    type λ continua meeting exactly in a common end set is of type λ, irreducibility again by
    hereditary unicoherence). The proof of Lemma 7 then avoids the points `x`, `y` and the continua
    `J`, `K`, `L`: a case split on `K = H ∩ F` — inside one layer of `H` (then `F` is the third arm of
    a triod with core `k⁻¹(r)`, `no_arm_at_interior_layer`), meeting two layers of `H` and two of `F`
    (Lemma 6 twice, `layer_common_of_essential`), or meeting two layers of `H` inside one layer `Y` of
    `F` (then `H ∩ I ⊆ Y`, else two layers of `H` would both be the layer `Y` of `I`, and `H` is the
    third arm at `Y`). H84.4 (b) and (c) are not used; (a) and the two other atriodicity steps are
    replaced by `no_arm_at_interior_layer`.
16. **H84.16, rigidity (commission 185 §3.1) and its degenerate case.**

    **True; one degenerate case.** If `E ∩ G` meets two layers of `E`, then either `E` lies in one
    layer of `G` (then `E ⊆ G`), or the decompositions agree on `E ∩ G` (`layers_agree`). The case
    "`E` in one layer of `G`" with `E ⊄ G` or `G ⊄ E` is excluded by Lemma 7; with `G ⊆ E` by the
    surjectivity of `d`. Whether a type λ continuum can lie in a single layer of another is not
    decided; in §4 it does not arise (Lemma 7 is applied with `h[E] ⊄ F` and `F ⊄ h[E]`).

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen.

### Hagopian 1984 III: the quotient package; Lemmas 12–16 (batch 186)

Same paper, pp. 339–344. The formalization is in `HPC/Hagopian/Hagopian84B.lean` (statements),
`HPC/Hagopian/H84Fold.lean`, `HPC/Hagopian/H84Delta.lean`, `HPC/Hagopian/H84Lemma12.lean`,
`HPC/Hagopian/H84Lemma1415.lean`; the report is `doc/batches/REPORT-batch186.md`.
* **Outcome.**
  * **Proved:** the quotient package (`hagopian84Decomp_of_package`, with `exists_comp_small_homeo`);
    the fold combinatorics (`exists_fold`); Lemma 12 (`hagopian84_lemma12`); the note on p. 341
    (`delta5_partition`) and positivity (`delta5_dist_pos`); Lemma 14 (`hagopian84_lemma14`);
    Lemma 15 with a smaller `ε` (`hagopian84_lemma15`); the interval of layers for the arc
    (`exists_interval_in_delta`).
  * **Open:** Lemma 13 (with `chainLinks84_runsStraight`, `chainLinks84_regular`), Lemma 16 and its
    weaker form, the construction of pp. 343–344, Lemmas 8 and 10 (not needed with `N = M`), the arc
    step (`NoArcIndecHomPlane`).

**Checks.**

17. **H84.17, Lemma 13 (5) and the fold (p. 340).**
    > (5) if `0 ≤ r < t ≤ 1` and `k⁻¹(r) ∪ k⁻¹(t) ⊂ Lᵢ`, then `k⁻¹[[r, t]] ⊂ Lᵢ`.

    > By (1), (2), and (3), there exist numbers `r`, `s`, and `t` (`0 ≤ r < s < t ≤ 1`) and an
    > integer `i` (`1 ≤ i ≤ 4`) such that `h[k⁻¹(s)] ⊂ Lᵢ` and `h[k⁻¹(r) ∪ k⁻¹(t)] ⊂ Lᵢ₊₁∖Lᵢ`.

    **Slip (found by the commission) and an unargued reduction.** (5) is about `h[k⁻¹(r)]`,
    `h[k⁻¹(t)]`, `h[k⁻¹[[r, t]]]`, as its proof and its use in (6) show. The reduction omits the
    mirror case (`s ∈ Vᵢ₊₁`, `r, t ∈ Vᵢ∖Vᵢ₊₁`). The combinatorial part, with both cases, is proved
    (`exists_fold`, by a left-to-right sweep instead of the commission's monotonicity sketch); the
    geometric part (kinds D and U) is not formalized.
18. **H84.18, Lemma 13, the other unargued sentences (pp. 339–341).**
    > Note that `𝔏` is a normal chain in `M∖A`.

    > It follows from the definition of `δ` that `r ∈ [x₂, x₁₃]∖[x₃ᵢ₋₃, x₃ᵢ]`.

    > Since `M` is atriodic, it follows from (6) and Lemma 6 that `Cl K` is an essential
    > subcontinuum of `h[E]` that runs straight through `𝔏`.

    > Since `δ < ε`, `M` is atriodic, and `𝒫` is a regular ordered refinement of `𝔏`, there is an
    > ε-homeomorphism …

    **Unargued; not formalized this batch.** The readings of commission 186 §3.1 are recorded at
    `chainLinks84_runsStraight` and `chainLinks84_regular` (commented out). The last paragraph needs
    nothing further once Lemma 12 is proved with the added clause (each component of `⋃𝒫′` is a
    component of `⋃𝔏′`), which it is.
19. **H84.19, Lemma 12 (p. 339).**
    > Since `𝔏` is regular, `E∖(A ∪ B)` is an essential subcontinuum of `E`.

    > Since `M` is atriodic, `E∖(A ∪ B)` is a component of `M∖(A ∪ B)`.

    > The chain `𝒫` … is a free normal regular ordered refinement of `𝔏`.

    **Lemma true; proved; the first sentence is not needed.** Moore's Theorem 44 (compact form
    `exists_closed_split_of_no_connected`) is applied in `M∖(A ∪ B)` with
    `A = L 0∖Cl L 1`, `B = L 4∖Cl L 3`; its hypothesis (no connected set meets both `E∖(A ∪ B)` and
    `M∖⋃𝔏`) comes from atriodicity directly: the closure of such a connected set is a continuum
    meeting `E` and missing both end layers, so `subset_of_meets_avoids` puts it in `E`. Freeness is
    proved by the commission's route (a point of `Bd ⋃𝒫` in `Cl ⋃𝒫′` would lie in `K₁ ⊆ ⋃𝔏` and
    outside `L 0 ∪ L 4`, hence in `⋃𝒫′`).
20. **H84.20, Lemmas 14 and 15 (p. 341).**
    > Note that since `𝒫` is regular, `Δ(𝒫)` is a decomposition of `(⋃𝒫)∖Cl(P₁ ∪ P₅)`.

    > Let `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`.

    > By Lemma 3, …

    **Note and positivity: unargued, true, proved** (`delta5_partition`, `delta5_dist_pos`;
    positivity by freeness: `Cl ⋃Δ(𝒫) ⊆ ⋃𝒫′`). **Lemma 14: true, proved**; the three hypotheses of
    Lemma 3 are checked through the distance `η` of positivity. **Lemma 15: "By Lemma 3" does not
    suffice as printed** — the layer of `Cl K′` through a point of `h[Z]` need not lie in `Δ(𝒫)`,
    and Lemma 3's hypothesis on the end sets is then unavailable. Proved with a smaller `ε` (also
    less than half the distances between non-adjacent link closures), through `layers_agree` and
    `no_arm_at_interior_layer`. Whether Hagopian's `ε` works is not decided. Recorded as a gap in
    exposition: the lemma asks only for some `ε`.
21. **H84.21, Lemma 16 (pp. 341–342).**
    > Since `𝒫` is free, there exist a 3-linked subchain `𝔔` of `𝒫` and numbers `t`, `w` greater
    > than `s` such that (1) for each number `u` (`t < u < w`), `d⁻¹(u)` intersects each link of `𝔔`
    > and no element of `𝒫∖𝔔` that intersects a link of `𝔔` …

    **Unargued; open.** Freeness controls `Bd ⋃𝒫`; (1) asks that the layers of `F` just after `s`
    avoid the links adjacent to `𝔔`, a statement about how `F` leaves `⋃𝒫`. No argument was found,
    and the weaker form of commission 186 §5 meets the same step. The other steps (`s > 0`; `s ∉ S`
    by lower semicontinuity; uniqueness by `hagopian75_lemma3_unique`) are available.
22. **H84.22, p. 344: the arc and the points `vᵢ`.**
    > Since `M/𝔇` is an atriodic homogeneous continuum that contains an arc, …

    **Unargued; the arc proved from an interval of layers.** In the package, an interval of classes
    gives the arc by a quotient-map lift and a closed embedding; the interval itself is
    `exists_interval_in_delta`. The chain of points `vᵢ` is replaced by the orbit argument
    (`exists_comp_small_homeo`): harmless.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen (H84.20,
Lemma 15, is recorded as a gap in exposition, the lemma being proved for a smaller `ε`).

### Hagopian 1984 IV: Lemma 13; Lemma 16′; the bridge `J(Z)`; `𝒫(Z)`; the cover (batch 187)

Same paper, pp. 339–343. The formalization is in `HPC/Hagopian/Hagopian84C.lean` (statements),
`HPC/Hagopian/H84Chain13.lean`, `HPC/Hagopian/H84Runs13.lean`, `HPC/Hagopian/H84Regular13.lean`,
`HPC/Hagopian/H84Lemma13.lean`, `HPC/Hagopian/H84Strand.lean`, `HPC/Hagopian/H84Bridge.lean`,
`HPC/Hagopian/H84Cover.lean`; the report is `doc/batches/REPORT-batch187.md`.
* **Outcome.**
  * **Proved:** Lemma 13 (`hagopian84_lemma13`, with `chainLinks84_chain`,
    `chainLinks84_runsStraight`, `chainLinks84_regular`); Lemma 16′ (`strand_layer_of_extension`,
    the sentence of p. 343 that uses Lemma 16); Lemma 16 as printed with normality added
    (`hagopian84_lemma16`); §4.2 (`omega_not_delta_side`); the bridge (`exists_bridge84`); `𝒫(Z)`
    with `Z ∈ Δ(𝒫(Z))` (`exists_chainZ84`); the finite cover (`hagopian84_cover`).
  * **Open:** the printed closedness of `⋃𝔅` (not needed); the relation `𝔇`, claims (5)–(6),
    `hagopian84_decomp`; the arc step (`NoArcIndecHomPlane`).

**Checks.**

23. **H84.23, Lemma 16 (pp. 341–342) and its use (p. 343).**
    > Then no element of `𝔇` intersects three consecutive links of `𝒫`.

    > Since `𝒫` is free, there exist a 3-linked subchain `𝔔` of `𝒫` and numbers `t`, `w` greater
    > than `s` such that (1) for each number `u` (`t < u < w`), `d⁻¹(u)` intersects each link of `𝔔` …

    > By Lemmas 7 and 16, each element of the decomposition of `F(Z)` that intersects `⋃𝒫′` is an
    > element of the decomposition of the closure of a component of `⋃𝒫′`.

    **Step (1) still unargued; the lemma (with normality) and its use proved by another route.**
    The sentence of p. 343, the only use of Lemma 16, is proved directly for any type λ continuum
    whose end layer `d⁻¹(0)` misses `⋃𝒫′` (Lemma 16′, commission 187 §3: the dichotomy from
    `layers_agree` and `no_arm_at_interior_layer`, the degenerate case excluded by a limit layer).
    Lemma 16 then follows in a few lines, for a free *normal* regular chain (the chains of Lemma 13
    are normal); Hagopian's subchain `𝔔`, his step (1) and his contradiction are replaced. Whether
    Lemma 16 holds without normality is not decided. Gap in exposition (the conclusion used is
    proved).
24. **H84.24, p. 343: `K(Z)`.**
    > For each element `Z` of `Ω(𝒫)∖Δ(𝒫)`, let `K(Z)` be the component of `⋃𝒫′` that contains `Z`.

    **Slip, harmless.** An end layer of a strand is in `Ω(𝒫)∖Δ(𝒫)` and outside `⋃𝒫′`, so no
    component of `⋃𝒫′` contains it. Read (commission 187 §4.1): the component whose closure has `Z`
    as a layer, which is how `Ω(𝒫)` is defined.
25. **H84.25, p. 343: `X(Z)`.**
    > Let `X(Z)` be the end set of `Cl K(Z)` that is separated from `Z` in `Cl K(Z)` by `P₃`.

    **Unargued, true, proved** (`omega_not_delta_side`): a member of `Ω(𝒫)∖Δ(𝒫)` lies in `Cl P₁` or
    in `Cl P₅` and misses `Cl P₃`; `X(Z)` is the end layer on the other side.
26. **H84.26, p. 343: `F(Z)`.**
    > By Lemma 11, `Cl ⋃𝔖(X(Z), Cl K(Z))` is an indecomposable subcontinuum of `N`. Thus
    > `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`.

    **Unargued, true, proved** (`exists_ext_meeting_P2`): otherwise `Cl ⋃𝔖 ∩ P₃` would be a nonempty
    open subset of the indecomposable `Cl ⋃𝔖` inside its proper subcontinuum `Cl K(Z)` (extensions
    are strict, `hagopian76_lemma4`).
27. **H84.27, p. 343: `J(Z)`.**
    > Hence there is an essential subcontinuum `J(Z)` of `F(Z)` that contains `Z`, misses `Cl P₃`,
    > and has one end set in `K(Z) ∩ (⋃Δ(𝒫))` and the other end set in `(⋃Δ(𝒫))∖K(Z)`.

    **Unargued; proved without the positions relative to `K(Z)`** (`exists_bridge84`): `J(Z)` lies
    between the last parameter below `z₀` and the first parameter above `z₀` whose layers meet
    `Cl P₃`; its end layers are members of `Δ(𝒫)` by Lemma 16′. The commission's `translate_run`
    step is not needed. That the second end set lies outside `K(Z)` is not claimed: with the first
    parameter `≥ z₀` meeting `Cl P₃`, that layer may still be a layer of `Cl K(Z)`. Neither `𝒫(Z)`
    nor the cover uses the positions.
28. **H84.28, Lemma 13, steps (3)–(6) and regularity (pp. 339–340).** (Continues H84.17, H84.18.)
    > It follows from the definition of `δ` that `r ∈ [x₂, x₁₃]∖[x₃ᵢ₋₃, x₃ᵢ]`.

    > By Lemma 1, there exists a `μ`-homeomorphism `f` of `M` onto `M` such that `fh` is a
    > `δ`-homeomorphism and `f(p) ∈ Lᵢ`.

    > Since `M` is atriodic and `g[k⁻¹[[0, x₃ᵢ]]]` misses `Lᵢ₊₁∖Lᵢ`, it follows that
    > `g[k⁻¹[[0, x₃ᵢ]]] ⊂ h[k⁻¹[[r, t]]]`. This contradicts the definition of `δ`.

    > Since `M` is atriodic, it follows from (6) and Lemma 6 that `Cl K` is an essential
    > subcontinuum of `h[E]` that runs straight through `𝔏`.

    **Unargued steps; all true; Lemma 13 proved as printed** (batch-186 shape). (3): the positions
    of `r` and `s` follow from the gap bounds as comparisons with the `xⱼ` (commission 187 §2.1; no
    uniform continuity). (4): `f` needs the room `δ − max dist(v, h v)`, positive by compactness.
    (5): kind U (the mirror case of H84.17) is omitted in print and is the mirror argument. The
    regularity sentence needs an orientation argument not in the text: the end parameters of
    `Cl K` lie in `V₁ ∪ V₅`, and `a ∈ V₅` or `c ∈ V₁` would make two consecutive parameter sets
    disjoint, disconnecting `[0, 1]`. The `δ` here is also below fifteen gap radii instead of
    thirteen (harmless: `δ` is chosen).
29. **H84.29, p. 343: the cover.**
    > Since `𝒫` is free and since `𝒫(Z)` is free and (3) holds for each element `Z` of
    > `Ω(𝒫)∖Δ(𝒫)`, it follows that `⋃𝔅` is a closed open subset of `M`. Hence `𝔅` covers `M`.

    **Unargued; the conclusion used afterwards proved by another argument.** Freeness and (3)
    control `Bd ⋃𝒫(Z)` for each `Z` separately; for a limit of points of `⋃Δ(𝒫(Zₙ))` with pairwise
    distinct `Zₙ` (the family is uncountable) nothing in the text places it in `⋃𝔅`. What the proof
    uses next is a finite subcover, and that is proved directly (`hagopian84_cover`):
    `Cl ⋃Δ(𝒫)∖⋃Δ(𝒫)` is compact and covered by the sets `⋃Δ(𝒫(Z))`; the union of finitely many of
    them with `⋃Δ(𝒫)` is open and, by freeness and (3) for those finitely many, closed. Gap in
    exposition. *Reclassified in batch 188* (entry 29 of "Hagopian 1984 V" below): the statement is
    proved (`sUnion_cover84_eq_univ`); only the printed reason is unargued.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen (H84.23 and
H84.29 are gaps in exposition: the conclusions used are proved by other routes; Lemma 16 is proved
with normality added, which every chain it is applied to has).

### Hagopian 1984 V: `𝔇`; claims (5)–(6); `hagopian84_decomp` (batch 188)

Same paper, pp. 343–344. The formalization is in `HPC/Hagopian/Hagopian84D.lean`; the report is
`doc/batches/REPORT-batch188.md`.
* **Outcome.**
  * **Proved:** the transfer lemma (`omega_layer_of_mem_mid`, `omega_mem_delta_of_mem_mid`); the data
    (`CoverData84`, `exists_coverData84`); `𝔇` and its disjointness (`CoverData84.members_disjoint`);
    the relation (`CoverData84.setoid`, `CoverData84.cls_eq`); claim (5) for `i = 0` in full
    (`CoverData84.omega_subset_members`) and for `i ≥ 1` for the members inside `⋃𝒫(Zᵢ)′`
    (`CoverData84.omega_mem_members`); claim (6) (`CoverData84.invariant`); the package
    (`CoverData84.isJonesDecomp`); **Theorem 1 with `N = M` in the form used**
    (`hagopian84_decomp : Hagopian84Decomp`); **Theorem 1 of 1976 from the arc step alone**
    (`hagopian76_theorem1_jones`); the printed `⋃𝔅 = M` (`sUnion_cover84_eq_univ`).
  * **Open:** the arc step (`NoArcIndecHomPlane`, Jones 1975), now the last open input of
    `Hagopian76Thm1` on this route. Not formalized (not needed): the printed (5) for members of
    `Ω(𝒫(Zᵢ))` outside `⋃𝒫(Zᵢ)′`, and the lower semicontinuity of `𝔇`.

**Checks.**

29. **H84.29, p. 343: the cover** (reclassified, batch 188).
    > it follows that `⋃𝔅` is a closed open subset of `M`. Hence `𝔅` covers `M`.

    **Statement proved; the printed reason unargued.** For any choice of the chains `𝒫(Z)` as in
    `exists_finite_cover84`, `⋃𝔅 = M` (`sUnion_cover84_eq_univ`, a corollary of the finite cover), so
    `⋃𝔅` is closed. What is unargued in print is only the reason given (freeness and (3)). Gap in
    exposition.
30. **H84.30, p. 344: disjointness, first case.**
    > Let `A` and `B` be intersecting elements of `𝔇`. If `A ∪ B` intersects `⋃Δ(𝒫)`, then, by (2),
    > (3), and Lemma 7, `A = B`.

    **Unargued in one case; the statement proved by another route.** Lemma 7 needs `E∖F ≠ ∅ ≠ F∖E`
    for the strands. Let `S_A` be the strand of `𝒫(Zᵢ)` through `A`, `Y ∈ Δ(𝒫)` the member through
    the common point, `S_Y` its strand. Every strand of `𝒫` meets `P₃` and `S_A` misses `P₃` by (2), so
    `S_Y ⊄ S_A`. `S_A ⊄ S_Y` is not argued; if `S_A ⊆ S_Y` without lying in one layer, `layers_agree`
    gives `A = Y` without Lemma 7, so the only case the text leaves open is `S_A ⊆ Y`, which (3) does
    not exclude (it only puts the end links of `𝒫(Zᵢ)` inside `⋃Δ(𝒫)`). The transfer lemma
    (commission 188 §2: Lemma 16′ for `𝒫(Zᵢ)` applied to the piece of the strand of `Y` between `Y`
    and a layer inside `P₃`; it uses (2) and not (3)) covers every case, including `S_A ⊆ Y`
    (`omega_mem_delta_of_mem_mid`, `CoverData84.eq_of_meet_delta`). Gap in exposition.
31. **H84.31, p. 344: disjointness, last case.**
    > Since `A ∪ B` misses `⋃Δ(𝒫)`, it follows from (3) that `A ∪ B` misses both end sets of `Cl I` and
    > both end sets of `Cl J`. Thus, by Lemma 3, `A = B`.

    **Correct, with the maps chosen.** The end sets lie in `Cl(P(Zᵢ)₁ ∪ P(Zᵢ)₅) ⊆ ⋃Δ(𝒫)` for the maps
    running straight through `𝒫(Zᵢ)` (`delta_regular_rep`), which also give `A`, `B` as interior
    layers; then Lemma 3 with `h` the identity. (For an arbitrary decomposition of `Cl I` this is the
    same, by uniqueness of the decomposition, but the end sets are read off the map running
    straight.) Proved in `CoverData84.members_disjoint`.
32. **H84.32, p. 344: claim (5).**
    > Since `𝒫` is a free regular chain, it follows from (3) and Lemma 7 that (5) for each integer `i`
    > (`0 ≤ i ≤ n`), `Ω(𝒫(Zᵢ)) ⊂ 𝔇`.

    **Unargued in the case `S ⊆ Y`; proved where used.** As in H84.30, Lemma 7 does not apply when the
    strand `S` of `𝒫(Zᵢ)` lies inside the member `Y` of `Δ(𝒫)`; the transfer lemma covers it. Proved:
    `i = 0` in full (`CoverData84.omega_subset_members`; a member of `Ω(𝒫)∖Δ(𝒫)` lies in `Cl P₁` or
    `Cl P₅`, so it is covered by some `⋃Δ(𝒫(Zᵢ))`, and the transfer lemma) and `i ≥ 1` for members
    inside `⋃𝒫(Zᵢ)′` (`CoverData84.omega_mem_members`), which is all that (6) uses. For members outside
    `⋃𝒫(Zᵢ)′` an argument is recorded in the report (§4.2), not formalized. Gap in exposition.
33. **H84.33, p. 344: claim (6) and Lemma 15.**
    > By Lemma 15, for each integer `i` … there is a positive number `εᵢ` such that if `Z ∈ Δ(𝒫(Zᵢ))`
    > and `h` is an `εᵢ`-homeomorphism of `M` onto `M`, then `h[Z] ∈ Ω(𝒫(Zᵢ))`. … It follows from (5)
    > that (6) …

    **Correct, with a bound from the proof of Lemma 15.** The proof of Lemma 15 takes
    `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`, which keeps `h[Z]` inside `⋃𝒫′`; the statement of Lemma 15 drops that.
    `δ` is taken below the `η` of `delta5_dist_pos` for each of the finitely many chains as well
    (`delta_translate_small84`), so that the part of (5) proved applies (`CoverData84.invariant`).
34. **H84.34, p. 344: continuity.**
    > It follows from Lemma 14 that `𝔇` is continuous.

    **The u.s.c. half proved; the l.s.c. half follows by the same argument (not formalized, not
    needed).** For a member `D ∈ Δ(R)` through `z₀`, Lemma 14 at `z₀` and the openness of `⋃Δ(R)`
    (`isOpen_sUnion_delta5`) put every member through a point near `z₀` (a member of `Δ(R)`, by
    disjointness) in the `ε`-neighbourhood of `D` (field `usc` of `CoverData84.isJonesDecomp`). The
    other half of Lemma 14 (`D ⊆ thickening ε D′`), with the same balls around the points of `D`, gives
    the lower semicontinuity.
35. **H84.35, p. 344: the "first note".**
    > First note that for each integer `i` …, each component of `⋃Δ𝒫(Zᵢ)` misses `P₃` and intersects
    > `M∖⋃𝒫′`.

    **Not used on this route; the second half unargued.** "Misses `P₃`" is (2). "Intersects
    `M∖⋃𝒫′`" would close the case `S_A ⊆ Y` of H84.30 (the component through `A` lies in `S_A`, and
    `Y ⊆ ⋃𝒫′`), but no argument for it was found. It needs more than the end-set positions of `J(Z)`
    (H84.27): the end links of `𝒫(Zᵢ)` lie in `⋃Δ(𝒫) ⊆ ⋃𝒫′`, and a strand of `𝒫(Zᵢ)` leaves `⋃𝒫′` only
    if its two end layers lie in different components of `⋃𝒫′`. The strands of `𝒫(Zᵢ)` only come
    within `δ` of the end sets of `J(Z)`, and since `M` is not locally connected the components of
    `⋃𝒫′` are not open, so even the printed positions of the end sets of `J(Z)` do not place the end
    layers of the strands in different components. Lemma 13 and (3) do not give this.

No statement of Hagopian's is refuted. The count of defective proofs stays at fourteen (H84.29, H84.30
and H84.32 are gaps in exposition: the conclusions used are proved by other routes).

### Jones 1975 I: (c), (d), (f) and the Theorem; lines, no small reversal, recurrence (batch 189)

F. B. Jones, *Use of a new technique in homogeneous continua*, Houston J. Math. 1 (1975), 57–61
(`doc/notes/jones75.md`). The formalization is in `HPC/Jones/Jones75Arcs.lean`,
`Jones75Line.lean`, `Jones75Rev.lean`, `Jones75L.lean` and `Jones75A.lean`; the report is
`doc/batches/REPORT-batch189.md`.
* **Outcome.**
  * **Proved** (for a compact metric `Y` with `JonesSetting Y`: homogeneous, hereditarily
    unicoherent, atriodic, containing an arc; `jonesSetting_of_plane` for the plane): (c)
    (`JonesSetting.union_arc`, `JonesSetting.nested`); arcs through a point
    (`JonesSetting.exists_arc_through`); every arc component is a line (`JonesSetting.exists_line`);
    arcs of a line and homeomorphisms on lines (`JonesSetting.line_arc`,
    `JonesSetting.homeo_on_line`); no small reversal (`JonesSetting.no_reversal_arc`,
    `JonesSetting.exists_no_reversal`); orientation (`JonesSetting.orientation`); limit sets are
    arc-saturated and every line is recurrent (`JonesSetting.omegaLim_saturated`,
    `JonesSetting.line_recurrent`); the second sentence of (d) for every line in both directions
    (`JonesSetting.jones75_d`); (L), no backtracking (`JonesSetting.no_backtrack`,
    `no_backtrack_in_collar`).
  * **Open:** the planar core of the Theorem (`jones75_noArc : NoArcIndecHomPlane`); hand proof and
    skeleton in the report, §6. (Proved in batch 190, by the repaired route of commission 190; see
    the next subsection.)

**Checks.**

1. **J75.1, p. 59: the proof of (f).**
   > (f) If p is a point of M and D is an open set in E with p ∉ D̄, then there exists a positive
   > number ε such that no arc abc in M has the property that both a and c belong to D and the
   > ε-neighbourhood of the subarc ab contains both p and the subarc bc.

   > Since b′c′ is in the ε-neighbourhood of a′b′, the image of b′c′ must be in the
   > 3ε-neighbourhood of the image of a′b′. This is impossible since the 3ε-neighbourhood of q₁p₁
   > contains no point of p₂q₂ (and conversely).

   **Defective proof; the statement true for plane continua only vacuously (once the Theorem is
   known).** The last inference is a non sequitur: the images of `a′b′` and `b′c′` lie on the arc
   `q₁pq₂ ∪ g[a′b′c′]` (an arc by (c)), but `g[a′b′]` may continue beyond `q₁` and come back near
   `p₂q₂`; nothing confines it to `q₁pq₂`. The proof uses only the Effros corollary and (c) (through
   (a) and (b)). **The dyadic solenoid `Σ` refutes the argument** (hand argument, not formalized):
   `Σ` is homogeneous and indecomposable, hence unicoherent; its proper subcontinua are arcs, so it
   is hereditarily unicoherent; it is atriodic (an arc minus a subcontinuum has at most two
   components, and `Σ` minus a proper subcontinuum contains a dense composant, so is connected); its
   arc components are dense lines, so (c) holds. Yet (f) fails in `Σ`, even with `d(b, p) < ε`: take
   a line `λ` with `λ(0) = a ∈ D`, `S` with `λ[0, S]` `ε/2`-dense, `S₁ ≥ S` with `d(λ(S₁), p) < ε`
   and `S₂ > S₁` with `λ(S₂) ∈ D` (forward rays are dense, since `{n ≥ N}` is dense in the 2-adic
   integers); then `abc = λ[0, S₂]`, `b = λ(S₁)` has `N_ε(ab) = Σ ⊇ {p} ∪ bc`. Two earlier steps
   are unargued as well:
   > Then there exists an arc abc in M and a homeomorphism of M onto M which takes b to p but leaves
   > the images q₁ and q₂ of a and c respectively in D.

   The negation of (f) gives a point of `ab` within `ε` of `p`, not `b`; and leaving `q₁`, `q₂` in
   `D` is unjustified for a homeomorphism that is not small.
   > b′ is close enough to b so that there exists a homeomorphism of M to M that moves b′ to p but
   > moves no point more than ε

   needs `b′` close to `p`, not to `b`. **Replacement:** (R) and (O) (`exists_no_reversal`,
   `orientation`), proved under `JonesSetting` alone, give what the Theorem uses (f) for. **The
   fourteenth defective proof of the ledger** (batch 191 correction; batch 189 had "fifteenth").
2. **J75.2, p. 58: the second sentence of (d).**
   > Let c be the first point of T (if there is one) which is a limit point of T − ae for some
   > point e beyond c in T. Let 2ε < min{d(a,W), d(e,ac)}. … Then c′ has the properties possessed
   > by c and hence c was not the first point of T with these properties. Hence no such point c
   > exists.

   **Gap; statement true (proved, `JonesSetting.jones75_d`).** A first such point exists if any
   does (for a witness `e`, `cl(T − ae) ∩ ae` is closed and misses `a`). The transport step ignores
   orientation: if the Effros homeomorphism reverses `T`, then `a = g(y)` for some `y ∈ ce`, and
   `2ε < d(a, W)` does not exclude that; adding `d(a, ce)` to the minimum, or (O), repairs it.
   > Then T union with the image of T under two such homeomorphisms taking r to each of p and q
   > would contain a triod.

   As printed nothing makes those images meet `T`, so no triod is produced. Replaced by
   recurrence (`JonesSetting.line_recurrent`, Jones's own `½ d(a, T̄ − T)` device applied to the
   arc-saturated limit set). Gap in exposition; not counted.
3. **J75.3, p. 57: (c).**
   > (c) If two arcs A and B of M intersect then A ∪ B is an arc, and in particular where they have
   > a common end point and intersect somewhere else, then one of them is a subset of the other.

   **True; the argument, (a) plus (b), is unstated.** Proved: `JonesSetting.union_arc`,
   `JonesSetting.nested` (the intersection is a subcontinuum, hence a subarc of each; three arms at
   an end of it would form a triod). Not counted.
4. **J75.4, pp. 59–61: the Theorem.**
   > Furthermore let us assume that T is accessible from the complement of M

   unargued.
   > There exists a positive integer η such that no arc of T lying between y = 1/η and the x-axis,
   > has an interior point in only one of the lines x = n (n = 1,2,3,4) and has both end points
   > either on x = n+1 or on x = n−1. This follows from property (f).

   rests on J75.1; replaced by (L) (`JonesSetting.no_backtrack`, `no_backtrack_in_collar`).
   > This makes h take [t₀,t_d] onto (approximately) [t_d,t₀]. So there is a fixed point t_f on
   > [t₀,t_d].

   **Unargued.** The hypotheses of the Theorem are never satisfied (`jones75_noArc`, batch 190), so
   the step is not called false; but under the hypotheses of the setting it contradicts (O)
   (`JonesSetting.orientation`): a homeomorphism that moves no point more than `ε < ε₀` and carries
   a point of a line into that line is increasing on it, so it does not reverse `T`. Any argument
   for the step would therefore itself finish the proof. (Wording of commission 190 §9.1, adopted
   in batch 190; batch 189 had called the step false for `ε < ε₀`.)
   > Clearly t_f cannot lie in D̄₁ ∪ D̄₂ ∪ D̄₃

   unargued (and moot: there is no `t_f`).
   > it is easy to see that p ∉ D̄₂ and property (f) is violated.

   unargued, and rests on J75.1. **Defective proof (a false step); the Theorem true** (Bing 1960;
   Hagopian 1976 by a different route). The contradiction can instead come from a piece `[t_c, t_d]`
   of `T` from `x = 5` to `x = 0` in a thin strip, through (L), or from the Poincaré–Bendixson
   argument of the report, §6. **The fifteenth defective proof of the ledger** (batch 191 correction; batch 189 had
   "sixteenth").
5. **J75.5: `doc/notes/jones75.md` (batch 186).** The pages are 57–61 (the sixth PDF page is blank),
   not 57–62; the Effros corollary is printed with "`d(h(p), p) ≤ ε`", not "`< ε`". Corrected.

No statement of Jones's is refuted. The count of defective proofs rises from thirteen to fifteen
(J75.1 and J75.4).

**Count corrected (batch 191, commission 191 §0).** The earlier count had included Moore 1916
Theorems 33–34 twice, although they share one printed proof (Kline's), which is counted once. With
the correction, the figure "fourteen" in the subsections before this one reads thirteen; the count
before Hagopian 1976 Theorem 1 is fifteen, and with it (classified in batch 191, see the Hagopian
1976 subsection "Theorem 1 classified") sixteen.

### Jones 1975 II: the planar core; `NoArcIndecHomPlane`; Theorem 1 of 1976 (batch 190)

Same paper, pp. 59–61 (the Theorem). The formalization is in `HPC/Jones/Jones75Pass.lean`,
`Jones75Shadow.lean`, `Jones75Region.lean`, `Jones75Trap.lean` and `Jones75B.lean`; the report is
`doc/batches/REPORT-batch190.md`.
* **Outcome.**
  * **Proved:** passes and (P1)–(P4) (`IsPass.disjoint`, `IsPass.finite`, `exists_first_pass`,
    `isPass_base`, `IsPass.above_or_below`); the shadow lemma, the flow box, scale 2 and late thin
    passes, all in the middle band (`shadow_pass`, `flow_box`, `scale_two`,
    `exists_late_thin_pass`); N1–N4 (`thinPass_arc`, `tarc_lowest`, `two_sides`,
    `IsPass.lc_left_mem_closure`); (R1)–(R3) and Lemma A (`region_pass`, `region_thin_above`,
    `region_cross`, `region_lemmaA`); the trap (`trap_jordan`, `trap_pass`); the contradiction
    (`jones75_contra`); **the arc step `jones75_noArc : NoArcIndecHomPlane`**; **Theorem 1 of
    Hagopian 1976, unconditionally** (`hagopian76_theorem1`); Bing 1960 for plane continua and
    Hagopian 1976 Theorem 2, unconditionally (`bing60_plane_uncond`, `hagopian76_theorem2_uncond`),
    and the unconditional forms `hagopian75_corollary_uncond`, `hagopian75_theorem2_uncond`,
    `hagopian75_theorem1_of_noArc_uncond`.
  * **Open:** nothing in this section.

**Checks.**

6. **J75.6: report 189 §6.3 (the repository's own hand proof, not Jones's).** Its shadow lemma and
   flow box were stated for the whole box `F([¼, ¾] × [−η, η])`. They hold only in the middle band
   `X ∈ [¼ + κ, ¾ − κ]`: near an edge, backtracking up to `2κ` is allowed, so the sup/inf
   construction can produce a U-turn through one edge instead of a pass. Hence "every point of `ℓ`
   in `R` lies on a pass" fails near the edges, and "`R ∩ J = σ°`" (used for the two sides and
   the frontier point) is unsupported. Also `N_o` had to be chosen after `P_{m₂}`. Found by an
   independent check for commission 190 (§0), which rebuilt the trap in the column
   `3/8 ≤ X ≤ 5/8` with the property (Mon). **Formalized in batch 190 in the repaired form**
   (`shadow_pass` and `flow_box` are stated for `x ∈ [9/32, 23/32]` only; the trap `trap_pass`
   never uses `R_m ∩ J = σ°`). Not counted (not a published proof).
7. **J75.7, p. 59: the Theorem, statement.**
   > THEOREM. *If M is a homogeneous plane continuum containing an arc, then M is a simple closed
   > curve.*

   **Proved** (`bing60_plane_uncond`; its indecomposable case is `jones75_noArc`, its
   decomposable case Jones 1955). The proof is not Jones's: the route of commission 190 replaces
   the following printed steps (each already recorded under J75.4):
   > Furthermore let us assume that T is accessible from the complement of M

   (accessibility and property (e) are not used);
   > There exists a positive integer η such that … This follows from property (f).

   (replaced by the flow box with (Mon), `flow_box`);
   > Now let a and b be the smallest positive numbers with a < b such that [t_a,t_b] is irreducible
   > from x = 5 to x = 0 and lies between y = 1/η and the x-axis.

   (replaced by the first thin pass after `¾`, `exists_first_pass`);
   > For each i (i = 1,…,4) let zᵢ be the lowest point of [t_a,t_b] on x = i and let Dᵢ be the
   > simple domain bounded by …

   (replaced by the single region `R_m = F(D_m)` of a thin pass, `rect_domain_aux`, and the lowest
   points `w_m(c)`, `tarc_lowest`);
   > Now let c and d denote positive numbers with c < d so that [t_c,t_d] lies above the x-axis, is
   > irreducible from x = 5 to x = 0, and no point of [t_c,t_d] lies above y = δ. … So there is a
   > fixed point t_f on [t₀,t_d].

   (no fixed point; replaced by the trap, `trap_pass`, with the Jordan curve `σ ∪ ℓ[½, t_m]`);
   > By appropriately selecting a sequence of values ε₁, ε₂, … of ε converging to zero … property
   > (f) is violated.

   (no limit argument; replaced by recurrence near `o = ℓ(½)` after the first thin passes above and
   below the base arc, `jones75_contra`). Not counted: the defects are J75.1 and J75.4.

No statement of Jones's is refuted. The count of defective proofs stays at fifteen (corrected in
batch 191 from "sixteen"; see the note at the end of Jones 1975 I).


### Oversteegen–Tymchatyn 1982 and Cook 1967 (batch 191)

L. G. Oversteegen and E. D. Tymchatyn, *Plane strips and the span of continua (I)*, Houston J. Math.
8 (1982), 129–142 (`doc/sources/oversteegen-tymchatyn1982.pdf`); H. Cook, *Continua which admit only
the identity mapping onto non-degenerate subcontinua*, Fund. Math. 60 (1967), 241–249
(`doc/sources/cook1967.pdf`). Quotations are from the page images (transcriptions in
`doc/notes/ot82.md`). The formalization is in `HPC/Span/Defs.lean`, `Cook.lean`, `Thm36.lean`,
`Reembed.lean`, `Crossing.lean` and `OT82A.lean`; the report is `doc/batches/REPORT-batch191.md`.
* **Axioms.** Lean names are in the group *Theorem C I (batch 191)* of `Axioms.lean` / `axioms.txt`,
  with standard axioms only; audit `doc/batches/audits/axioms-batch191.txt`.
* **Outcome.**
  * **Proved:** Cook's Theorem 4 (`cook67_theorem4`); Davis's Theorem 1.1 for hereditarily
    indecomposable continua (`exists_surjSpanPos_of_surjSemiSpanPos`, `semiSpanZero_of_spanZero`);
    Theorem 3.6, second sentence, from Corollary 3.5 (`ot82_theorem36_of_cor35`); Corollary 3.5 from
    Theorem 3.2 in strip form (`ot82_cor35_of_thm32 : OTThm32 → OTCor35`); Theorem C from it
    (`theoremC_of_thm32`).
  * **Open in batch 191:** `OTThm32` (Theorem 3.2 in strip form) and the planar lemma
    `crossing_traces_separated` (commission 191 §7). **Both proved in batch 192**
    (`ot82_theorem32 : OTThm32`, `crossing_traces_separated`), and with them `theoremC : TheoremC`
    without hypotheses; see the batch-192 checks OT.8–OT.13 below.

**Checks** (commission 191 §9; numbering OT.1–OT.7).

1. **OT.1, p. 140: Theorem 3.6, "Since X is atriodic tree-like".**
   > Since X is atriodic tree-like, and the semi-span of all proper subcontinua is zero, we may
   > assume that f is onto and g is either irreducible with respect to mapping onto X or g is into.

   **Reading confirmed.** In the indecomposable case neither atriodicity nor tree-likeness is used:
   the reduction is a Brouwer reduction for "`g(W) = X`" plus a swap (`exists_reduced_witness`),
   and "`f` onto" comes from the zero semi-span of proper subcontinua. The whole proof
   (`not_surjSemiSpanPos_univ`) uses Corollary 3.5, Effros, Hagopian 1976 Theorem 1, Cook and the
   Brouwer reduction only. So Rogers 1981 and Jones 1969 are not needed. Gap in exposition; not
   counted.
2. **OT.2, p. 140: two unargued steps of Theorem 3.6.**
   > Hence there exists an index i and points x ∈ f(Cᵢ), y ∈ g(Cᵢ) such that d(x,y) < δ.

   **Unargued, true.** It needs some `Kᵢ` to be `δ`-dense, which follows from `cl(∪Kᵢ) = X` and
   compactness (the `Kᵢ` increase). The existence of the sequence `{Kᵢ}` itself is unargued
   (composants are dense). The formalization takes one `δ`-dense proper subcontinuum directly
   (`exists_dense_proper_subcontinuum`: the proper subcontinua through a point are directed by
   union and their union, the composant, is dense).
   > This contradicts Corollary 3.5, since Z is a proper subcontinuum.

   **Unargued, true; it rests on the reduction.** `h f(Cᵢ) ≠ X` because `Kᵢ ≠ X`;
   `g(Cᵢ) ≠ X` because either `g` is into, or `g` is irreducible and `Cᵢ ⊊ C` (as `f(Cᵢ) = Kᵢ ≠ X`).
   Proved inside `not_surjSemiSpanPos_univ`. Also: the constant `3ε` can be any `α ≤ min d(f, g)`
   with Effros applied for `α` itself (`d(hf(c), g(c)) > α − α = 0`). Gaps; not counted.
3. **OT.3, pp. 139–140: Corollary 3.5, items 1–5 of commission 191 §6.**
   1. > Without loss of generality we may suppose x ∈ A ∩ g(C), π₁(A) = [0,1/2] and π₁(X) = [0,1].

      **Unargued; confirmed that it is not a matter of scaling.** Arranged by re-embedding
      (`exists_homeomorph_unique_leftmost`, the finger move `exists_homeomorph_push` in the
      connected set `{x > 0} ∖ A`, `isConnected_rightHalf_diff`); the formal route needs only a
      point of `X` strictly to the right of `A`, not the numbers `1/2` and `1`.
   2. > For each K ∈ 𝒦 we may suppose K ∩ {ε} × R = {x_K}.

      **Unargued; not needed (confirmed).** The formalization takes any `x_K ∈ K` on `x = ε`.
      The sin(1/x) example of the commission (a continuum minimal for meeting both sides that meets
      a side in an arc) is accepted as a hand argument; not formalized.
   3. > Since X is indecomposable there exists an uncountable collection 𝒦 of pairwise disjoint
      > subcontinua of X ∩ [ε,3/4] × R each of which meets both {ε} × R and {3/4} × R.

      **Unargued, true; proved** (`exists_uncountable_crossing`, by the cut-wire lemma
      `exists_crossing_subcontinuum` in each composant).
   4. > It is easy to see that there is a continuum B ⊂ X such that [0,5/8] ⊂ π₁(h_K(B)) ⊂ [0,3/4)
      > and h_K(B) ⊂ K for each K ∈ 𝒦.

      **Impossible as printed (confirmed): `h_K(B) ⊂ K ⊂ [ε, 3/4] × R` excludes `0 ∈ π₁(h_K(B))`.**
      The second reading (`[0, 5/8] ⊂ π₁(B)`, one `y ∈ B` for all `K`) is the one Theorem 3.2 needs,
      and it is what is proved: `B = ⋂_K h_K⁻¹(K)` (nested, by hereditary indecomposability) with a
      point `y` far to the right in every `h_K(B)` (inside `cor35_core`). Unargued step; with the
      misprint, a gap in exposition, not counted.
   5. > It is known [8] that an indecomposable homogeneous plane is hereditarily indecomposable.

      **Misprint confirmed** ("continuum" missing); "[7]" for Effros (Effros is [6]). Harmless.

   Corollary 3.5 is not verified (it rests on `OTThm32`), so no classification of its proof is made.
4. **OT.4, pp. 137–138: Theorem 3.2, the suppositions of its proof.**
   > We may suppose that for each λ ∈ Λ h_λ(Y) meets {0} × R in a single point and h_λ(Y)
   > intersects {1} × R in at most one point. Hence, since h_λ(X) ∩ {0} × R ≠ φ and
   > h_λ(Y) ⊂ [0,1] × R, we may suppose that for each λ ∈ Λ neither h_λ(X) nor h_λ(Y) separates the
   > plane. Let δ ∈ Λ. We may suppose that π₁(h_δ(y)) > π₁(h_δ(z)) + 1/2 for each z ∈ X. We may
   > also suppose that d(h_λ(z),h_γ(z)) < 1/8 for each z ∈ Y and λ,γ ∈ Λ. The proof now proceeds as
   > in Theorem 3.1 except that we use Theorem 2.7 instead of Theorem 2.6.

   and from Theorem 3.1 (p. 137):
   > Let λ₁,λ₂,λ₃ ∈ Λ such that h_λ₂(X) separates h_λ₁(X) from h_λ₃(X) in [0,1] × R.

   **Readings confirmed (hand arguments, not formalized).** The separating triple and the
   single-point supposition are unargued. The two "we may suppose" steps about `δ` are not
   available together; the fix of the commission (one `n` for span witness `≥ 1/n` and gap
   `> 1/n` on uncountably many indices, then a cluster within `1/(8n)`) is adopted for batch 192.
   The non-separation supposition is correct as the commission argues. **`OTThm32` adds the
   crossing continua** (`h i` maps `Y` into `K i`, pairwise disjoint continua crossing
   `[0, 1] × ℝ`), drops "`X ⊊ Y`, `y ∈ Y ∖ X`" (forced by the gap) and allows any index type. It is
   weaker than the printed statement and is what Corollary 3.5 uses (`ot82_cor35_of_thm32`).
   Whether the printed Theorem 3.2 holds in general is not decided. Open; not counted.
5. **OT.5, p. 130: Theorem 1.1 (Davis).**
   > Since every map of any continuum C onto an atriodic tree-like continuum is weakly-confluent
   > (see [21]), the following theorem follows easily by a Brouwer reduction type argument.

   **Proved here only for hereditarily indecomposable continua, through Cook**
   (`exists_surjSpanPos_of_surjSemiSpanPos`, `semiSpanZero_of_spanZero`), which is the case used in
   Corollary 3.5 (a subcontinuum of a hereditarily indecomposable continuum). Davis's paper, Lelek's
   theorem and Grispolakis–Tymchatyn are not needed. The general Theorem 1.1 is not formalized.
6. **OT.6, Cook p. 243: Theorem 4.**
   > Let C₁, C₂, C₃, ... be a sequence of subcontinua of X such that (1) for each n, Cₙ₊₁ is a
   > subcontinuum of Cₙ; (2) for each n, C is a proper subcontinuum of Cₙ; and (3) C is the common
   > part of continua of that sequence. … The common part of f(C₁), f(C₂), ... is f(C) …

   **Confirmed: the existence of `Cₙ` (which fails when `C = X`) and `⋂ f(Cₙ) = f(C)` are
   unstated; the theorem is proved** (`cook67_theorem4`) by a proof that needs neither: if
   `q ∈ Q ∖ f(C)`, a closed neighbourhood `N` of `C` misses `f⁻¹(q)`; by boundary bumping the
   component of `x` in `N` is a continuum strictly larger than `C` (or `C = X`, and then
   `q ∈ f(X)`), so its image meets `Q` and is not inside `Q`, hence contains `Q` by hereditary
   indecomposability, and so contains `q`; contradiction. Gaps; not counted (both are standard
   and true).
7. **OT.7: misprints.** "σ₀(x)" for σ₀(X) (p. 129); "f(X) ⊃ g(X)" for f(C) ⊃ g(C) and
   "homomorphism" for homeomorphism (p. 140); "[7]" for Effros, who is [6] (pp. 139, 140).
   **Confirmed.** Also: in the proof of Theorem 2.7 (p. 136), "C = {(x,y) ∈ R² | …}" should read
   `I²` (as in the proof of Lemma 2.3); and "d(h_λ(Z),h_γ(z))" for d(h_λ(z),h_γ(z)) in (5) of the
   proof of Theorem 3.3 (p. 138). Harmless.

No statement of Oversteegen–Tymchatyn or Cook is refuted, and no defective proof is added. The count
of defective proofs stays at sixteen (fifteen before Hagopian 1976 Theorem 1, which is classified in
batch 191; see the Hagopian 1976 subsection "Theorem 1 classified").

**Batch 192: Theorem 3.2 in strip form, Theorem C** (commission 192 §8; checks OT.8–OT.13). The
formalization is in `HPC/Span/OT82Parity.lean` (parity tools), `OT82Zero.lean` (a common zero on a
rectangle), `OT82Strip.lean` (strips, the sign function, the strip lemma), `OT82Order.lean` (order
of disjoint crossing continua) and `OT82B.lean` (`ot82_theorem32 : OTThm32`,
`theoremC : TheoremC`); the report is `doc/batches/REPORT-batch192.md`. Lean names are in the group
*Theorem C II (batch 192)* of `Axioms.lean` / `axioms.txt`, standard axioms only; audit
`doc/batches/audits/axioms-batch192.txt`.

8. **OT.8, p. 136: Theorem 2.7, the continua `H` and `K`.**
   > It is easy to see that the first part of Lemma 2.3 is valid even if (π₁ ∘ f)⁻¹(b) ≠ 1 ≠
   > (π₁ ∘ g)⁻¹(b) so there exists a continuum H in C such that (0,p) ∈ H and H meets both I × {0}
   > and I × {1}.

   > Clearly, K ∩ H ≠ φ.

   **Both unargued; neither found false.** The first part of Lemma 2.3 gives a continuum in the zero
   set from bottom to top, not one through the prescribed point `(0, p)`; a continuum through
   `(0, p)` can be obtained from the sign conditions (`φ ≥ 0` on `{0} × I`, `φ ≤ 0` on `I × {p}`)
   by a further separation argument that O–T do not give. "Clearly, K ∩ H ≠ φ" needs a crossing
   argument in `I²` (two continua, one joining `(0, p)` to both horizontal sides, the other joining
   `(0, q)` to both horizontal sides, must meet), true by a planar hand argument (if `p < q`, `H` joins `(0, p)` to the
   top side and so separates the left-side point `(0, q)` from the bottom side in `I²`, while `K`
   joins them; symmetrically if `q < p`), not given. **Both
   steps are replaced** by `common_zero_rect` (commission §4): a common zero of the two sign
   functions on the rectangle `[0, 1] × [p, q]`, found by a continuous logarithm of `φ + iψ`; no
   continuum in a zero set is used. Gaps; not counted.
9. **OT.9, p. 136: Theorem 2.7, continuity of `φ` when `(π₁ ∘ f)⁻¹(b) ≠ {1}`.**
   > Then φ is continuous on I², φ({0} × I) ≥ 0, φ({1} × I) ≤ 0 …

   **Confirmed: `φ` can be discontinuous.** In Theorem 2.7 `B₁` need not be vertical and `f` may
   pass through a point `z = f(t₀) ∈ B₁` with `t₀ < 1`. If `h(y₀) = z`, then for `x ∈ [t₀, 1)` with
   `d(B_x, z) > 0`, `z ∈ f[0, x] ⊆ S_x`, so `z ∉ U_x` and `φ(x, y₀) = +d(B_x, z) > 0`, while points
   `h(y)` near `z` on the inner side of `f` give `φ(x, y) ≈ −d(B_x, z) < 0`. Harmless here: the
   strip lemma requires the continuum `W` to miss `B₁`, `f[0, 1]` and `g[0, 1]`, and the formal sign
   function `stripSign` is continuous on the relevant set (`stripSign_continuousOn`).
10. **OT.10, pp. 134–135: Remark 2.5 and Lemma 2.4.**
    > Lemma 2.4 is particularly useful if an arbitrary continuum X of positive (semi-)span is
    > embedded in a locally connected continuum Y. Moreover, we can choose Y to lie in an arbitrary
    > small neighbourhood of X (cf. the proof of Theorem 2.6).

    **Not needed.** For Theorems 2.6–2.7 the locally connected `Y` would have to stay inside
    `U ∪ B₀ ∪ B₁` (the maps `h, k` take values there), which is impossible in general near `B₀`
    (a small neighbourhood of `X` leaves the strip where `X` meets `{a} × R`) and is not argued.
    The strip lemma works directly with the span witness `Z`: a fine chain in `Z` and straight
    segments between consecutive points give the two paths (`exists_eps_chain`, inside
    `strip_lemma`). Gap in exposition; not counted.
11. **OT.11, Lemma 2.3 and Theorems 2.6–2.7: "the component of U₁ whose boundary meets each of f(I)
    and g(I) in a nondegenerate continuum".** The definite article presumes uniqueness, which is
    not argued; the boundary condition is not used in the proofs. Here the region is described by
    the predicate `StripInner a b 1` (on `x = 0`, or off `S₁` with parity `1`), i.e. `U₁` itself,
    with no choice of component. Gap in exposition; not counted.
12. **OT.12, p. 137: Theorem 3.1, the separating triple.**
    > Let λ₁,λ₂,λ₃ ∈ Λ such that h_λ₂(X) separates h_λ₁(X) from h_λ₃(X) in [0,1] × R.

    **Unargued.** For images lying in pairwise disjoint continua crossing `[0, 1] × R` it is
    supplied by `crossing_traces_separated` (the traces on `x = 0` are strictly ordered; proved by
    the crossing parity alone, no Jordan curve theorem) together with step 3 of the proof of
    `ot82_theorem32` (three indices with the middle trace between the other two,
    `exists_between_three`). The arcs `A_i` in the Hilbert cube are not needed: the outer strip
    boundaries are piecewise linear paths through the images of a fine chain of points of `Y`.
13. **OT.13: classification.**
    * **Theorem 3.2: proof defective; statement not decided.** The proof fails at an identified
      step: the two "we may suppose" steps about `δ` (OT.4) are not available together. The
      strip form `OTThm32` (images in pairwise disjoint crossing continua) is **proved**
      (`ot82_theorem32`), by the repaired counting (one `n`, then a cluster) and the strip lemma;
      the printed statement without the crossing continua is neither proved nor refuted. Following
      the ledger's convention (a defective proof is counted once the statement is verified or
      refuted; cf. the Whyburn 1939 entry and "No defective proof is added while these are
      unsettled" in Hagopian 1976 I), **it is not counted** while the printed statement is
      undecided.
    * **Theorem 2.7: unargued steps (OT.8), replaced;** the form used (the strip lemma
      `strip_lemma`) is proved. Gaps; not counted.
    * **Theorem 3.1:** the separating triple is unargued (OT.12); not used beyond the strip form.
      Not counted.
    * **Corollary 3.5** in the form `OTCor35` is now verified (`ot82_cor35_of_thm32
      ot82_theorem32`); its unargued steps (OT.3) are gaps, so its proof is not counted.

No statement of Oversteegen–Tymchatyn or Cook is refuted in batch 192, and no defective proof is
added. The count of defective proofs stays at sixteen.

### Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)

L. C. Hoehn and L. G. Oversteegen, *A complete classification of homogeneous plane continua*, Acta
Math. 216 (2016), 177–216 (`doc/sources/hoehn-oversteegen2016.pdf`); J. Krasinkiewicz and P. Minc,
*Mappings onto indecomposable continua*, Bull. Acad. Polon. Sci. Sér. Sci. Math. Astronom. Phys. 25
(1977), 675–680 (`doc/sources/krasinkiewicz-minc1977.pdf`). Page numbers are the journals'. Quotations
were checked against the PDFs (the text layer of H–O, and the page images of H–O p. 212 and of
the K–M scan). The formalization is in `HPC/HO16/Defs.lean`, `KM77.lean`, `Thm8.lean`, `Thm4.lean`,
`Grid.lean`, `Plane.lean` and `HO16A.lean`; notes `doc/notes/ho16.md`; report
`doc/batches/REPORT-batch193.md`. Batch 194 (H–O Theorem 1, II: PL graphs, simple folds, Lemma 6,
Theorem 8 for folds, Proposition 7) adds `HPC/HO16/FoldDefs.lean`, `Subdiv.lean`, `PLLib.lean`,
`Lemma6.lean`, `FoldExists.lean`, `Thm8Fold.lean`, `Prop7.lean`, `FoldExample.lean` and `HO16B.lean` (report
`doc/batches/REPORT-batch194.md`); its quotations (HO.2, HO.4, HO.8–HO.12) were checked against page
images at 200 dpi, and those with bars, primes or subscripts at 400 dpi, not against the text layer.
* **Axioms.** Lean names are in the group *H–O Theorem 1, I (batch 193)* of `Axioms.lean` /
  `axioms.txt`, with standard axioms only; audit `doc/batches/audits/axioms-batch193.txt`. Batch 194:
  group *H–O Theorem 1, II (batch 194)*, audit `doc/batches/audits/axioms-batch194.txt`.
* **Outcome.** Proved: K–M Lemma 2 for hereditarily indecomposable compacta (`km77_lemma2`); the
  core of H–O Theorem 8, (1) ⇒ (2) (`ho16_theorem8_core`); H–O Theorem 4 in path form
  (`ho16_theorem4`); plane approximations (`interior_eq_empty_of_hi`, `exists_plGraph_approx`,
  `exists_path_approx`); and, from the named `Prop` `HOThm20` (H–O Theorem 20, "only if", for PL
  graphs), H–O Theorem 1 ("if") for plane continua (`ho16_theorem1_plane`) and "every
  indecomposable non-degenerate homogeneous plane continuum is a pseudo-arc"
  (`isPseudoArc_of_indec_homogeneous`, `homeomorph_pseudoArc_of_indec_homogeneous`).
  Batch 194 proved: a library for PL graphs (refinement `IsPLGraph.exists_refinement`, unions,
  closures of differences, finite relative frontiers, components); simple folds exist
  (`exists_simpleFold`); Lemma 6 (`ho16_lemma6`); Theorem 8, (1) ⇒ (2), for simple folds
  (`ho16_theorem8`); Proposition 7 (`ho16_prop7`); and the certificates for HO.1 and HO.8
  (`ho16_theorem1_printed_false`, `ho16_theorem1prime_printed_false`). `HOThm20` remains the only
  open input.

HO.1. **Theorem 1, p. 211: the restatement drops "non-degenerate".** p. 180:
   > Theorem 1. A non-degenerate continuum X is homeomorphic to the pseudo-arc if and only if X is
   > hereditarily indecomposable and has span zero.

   p. 211:
   > Theorem 1. A continuum X is homeomorphic to the pseudo-arc if and only if X is hereditarily
   > indecomposable and has span zero.

   Without "non-degenerate" the restatement is false: a one-point continuum is hereditarily
   indecomposable and has span zero but is not a pseudo-arc. **A misprint**; the formal statements
   carry non-degeneracy (`IsPseudoArc` includes it; `isPseudoArc_of_indec_homogeneous` assumes
   `(univ : Set M).Nontrivial`).

   **Batch 194: certificate and classification.** `ho16_theorem1_printed_false` (`HO16B.lean`)
   refutes the p. 211 wording with `X` a one-point space: H–O p. 177, "by a continuum, we mean a
   compact connected metric space. A continuum is non-degenerate if it contains more than one
   point", so a point is a continuum; p. 178, "A continuum is hereditarily decomposable
   (hereditarily indecomposable) if every non-degenerate subcontinuum is decomposable
   (indecomposable, respectively)", so it is hereditarily indecomposable; it has span zero; and
   `IsPseudoArc` includes non-degeneracy. The classification **stays a misprint**: Theorem 1 is
   stated correctly on p. 180, and p. 211 restates it; the certificate is supporting evidence. It is
   counted differently from HO.8 (see there).

HO.2. **[31] for tree-likeness, pp. 191 and 211.** p. 191:
   > Because X has span zero, it is tree-like [31], so we can choose a tree T ⊂[0, 1]^N …

   p. 211:
   > Since X has span zero, by [31] we have that X is tree-like.

   [31] is listed as "— The span of mappings and spaces. Topology Proc., 4 (1979), 631–633"
   (Lelek). On p. 212:
   > It is proved in [46] that any continuum with surjective semispan zero is tree-like.

   with [46] = Oversteegen–Tymchatyn, *On span and weakly chainable continua*, Fund. Math. 122
   (1984), 159–174. The commission describes [31] as a research announcement whose Lemma 5 and
   Theorem 6 carry no proof; [31] is not in `doc/sources/`, so this description was **not checked
   here** in batch 193.

   **Batch 194: checked against `doc/sources/lelek1979.pdf`** (pp. 631–633, PDF pages 2–4; page
   images at 200 dpi). The heading reads "Research Announcement", and p. 631:
   > The purpose of the present paper(1) is to announce some results which relate to spans of
   > mappings and have a number of interesting consequences for spans of spaces. A complete
   > version will be published elsewhere.

   followed by "The proofs of the following four propositions are rather straightforward"
   (Propositions 1–4, no proofs; p. 632: "Note that proposition 4 follows from propositions 2 and
   3"). **5. Lemma** (an essential `f : S → T`, `0 ≤ ε ≤ 1/2`) and **6. Theorem** ("If f: X → T is
   an essential mapping, X is compact, dimX ≤ 1 and 0 ≤ ε ≤ 1/2, then there exists a continuum
   K ⊂ X × X such that p₁(K) = p₂(K) and ρ[f(x),f(x′)] = ε for (x,x′) ∈ K") carry **no proof**.
   "The following four statements are corollaries to theorem 6": 7 and 8 assume "X is compact" and
   "dimX ≤ 1"; but
   > 9. If X is compact and σ(X) = 0, then each mapping f: X → T is inessential.

   has **no dimension hypothesis** (the derivation from 7 and Proposition 4 needs `dim X ≤ 1`).
   p. 633 obtains Corollary 10 ("If X is a continuum and σ(X) = 0, then X is tree-like"):
   > It is known [4] that continua of span zero are one-dimensional if non-degenerate. By corollary
   > 9, the mappings defined on them and having values in one-dimensional polyhedra [3] are all
   > inessential, and then corollary 10(2) can be obtained via a well-known characterization of
   > tree-like continua [1].

   So dimension one is supplied only for non-degenerate continua (by [4], Lelek 1964), which is
   all Corollary 10 needs (a degenerate continuum is trivially tree-like); the step from maps into
   `T` to maps into all one-dimensional polyhedra is the citation of [3] (Krasinkiewicz, "On
   one-point union of two circles") without argument; and Corollary 9 for compacta of dimension
   `> 1`, if such have span zero, is not covered by the argument shown. (Footnote (2) on p. 633 is
   about a result of J. F. Davis, not about the proof.) The referee's reading is confirmed. Record:
   the citation on pp. 191 and 211 is to an announcement whose Lemma 5 and Theorem 6 are unproved
   there and whose Corollary 10 is obtained by a sketch through [4], [3] and [1]; p. 212 supplies a
   published reference ([46]). **Neither is used on this route**: Theorems 4 and 20 need only a
   graph, and plane continua get graphs from the grid (`exists_plGraph_approx`). Not counted.

HO.3. **Theorem 4's proof, p. 184.**
   > … the set Mn ={(x, y)∈Gn ×(In \{pn , qn }):d(x, y)<ε} does not separate Gn ×{pn } from
   > Gn ×{qn } for each n=1, 2, ... . This would mean (see e.g. [44, Theorem 5.2]) that for every
   > n=1, 2, ..., there is a continuum Zn ⊂Gn ×In meeting Gn ×{pn } and Gn ×{qn } … such that
   > d(x, y)⩾ε for all (x, y)∈Zn .

   The cut wire theorem is to be applied to the compact set `{(x, y) ∈ Gn × In : d(x, y) ≥ ε}`
   (not to the complement of `Mn`, which contains the points of the end rows with `d < ε`); if no
   continuum in it meets both end rows, the cut wire splits it, and the split together with `Mn`
   separates the end rows. With that reading the printed step is right (formalized as
   `thm4_continuum_of_not_separates`). The compactness of the hyperspace behind "accumulates on a
   continuum" is stated on p. 183. [44] (Nadler, *Continuum Theory*) was not checked for the
   numbering of its Theorem 5.2. Gap in exposition; not counted.

HO.4. **Theorem 8's proof, pp. 187–189: the fans.** p. 187:
   > Each of these points yji is the vertex point of a finite fan Yji ⊂G2 (meaning Yji is the union
   > of finitely many arcs, each having yji as one endpoint, and which are otherwise pairwise
   > disjoint) such that Yji is the closure of an open neighborhood Oji of yji in G2 , and the
   > diameter of Yji is less than ε.

   "Otherwise pairwise disjoint" concerns the arcs of one fan; that **different fans are pairwise
   disjoint** is not said, and is needed (for `U₁ ∩ U₃ = ∅`, for `W₁ = U₁ \ X₁` to be open so that
   `∂L′` has its literal meaning, and for "`f(cl(Uᵢ \ Kᵢ)) ⊂ ⋃ⱼ Oⱼⁱ`"). Here the fans are chosen of
   radius `r` with `2r` below the least distance between the finitely many vertices, which makes
   them pairwise disjoint. Gap in exposition; not counted. `Kᵢ = f⁻¹(cl(Gᵢ \ G₂))` is used in
   `ho16_theorem8_core`.

   **Batch 194: an observation of batch 193 withdrawn.** Batch 193 recorded here that p. 188
   defines `Kᵢ = f⁻¹(Gᵢ \ G₂)` without closure and writes `f⁻¹(yⱼ¹) ⊂ f⁻¹(G₁ \ G₂) = K₁ ⊂ X₁`.
   That was a misreading of the **text layer**, which drops overlines. The page image of p. 188
   (PDF page 12, rendered at 400 dpi and cropped to both lines) prints the closure bar over
   `Gᵢ \ G₂` in "Let Kᵢ = f⁻¹(cl(Gᵢ \ G₂))" and over `G₁ \ G₂` in
   "f⁻¹(yⱼ¹) ⊂ f⁻¹(cl(G₁ \ G₂)) = K₁ ⊂ X₁". Both formulas are right as printed; the observation is
   removed. (Route change: instead of a Tietze extension on each `cl L′`, the
   formal proof uses Urysohn functions `u₁, u₃` and the correction `h = f + (1 − u)·(c − f)`, `c`
   the vertex of the fan containing `f(x)`; only the star-shapedness of the fans is used.)

HO.5. **Theorem 8, (3) ⇒ (1), p. 189** (not on the route).
   > By [24] it suffices to show that X =X1 ∪X2 ∪X3 where X1 , X2 , and X3 are closed subsets of X
   > such that A⊂X1 , B ⊂X3 , X1 ∩X3 =∅, X1 ∩X2 ⊂U , and X2 ∩X3 ⊂V .

   The proof then shows
   > To see that X1 ∩X2 ⊂V , let x∈X1 ∩X2 . … Similarly, X2 ∩X3 ⊂U .

   which is the form of [24] quoted on p. 187 ("X1 ∩X2 ⊂V , X2 ∩X3 ⊂U"). `U` and `V` are
   interchanged in the first sentence. **A misprint**: the printed condition holds in every
   compactum (take `X₂ = X` and for `X₁`, `X₃` closed neighbourhoods of `A`, `B` inside `U`, `V`
   with disjoint closures), so it cannot be the criterion.

HO.6. **K–M Lemma 2, p. 676.**
   > 2. LEMMA. Let A and B be nonvoid disjoint and closed subsets of a continuum X such that each
   > subcontinuum of X irreducible between them is indecomposable. Then for each neighborhood U of
   > A and for each neighborhood V of B (in X) the triple (X, A, B) is crooked between U and V.

   The proof is correct. For hereditarily indecomposable `X`, Lemma 1 (used for "there is a
   decomposable subcontinuum of X irreducible between A and B, a contradiction") is not needed:
   the subcontinuum `C₁ ∪ C₂` is itself decomposable. The proof works in a compactum (H–O's remark
   on p. 187); formalized as `km77_lemma2`. Nothing to record against K–M.

HO.7. **Proof of Theorem 1, p. 211.**
   > Therefore, there exists a tree T ⊂[0, 1]^N and a map f : X →T such that dsup (f, idX )<δ. It
   > follows that dH (X, T )<δ.

   From `d_sup(f, id_X) < δ` only `X ⊆ T_δ` and `f(X) ⊆ X_δ` follow; points of `T` off `f(X)` may
   be far from `X`, and Theorem 4 needs both halves. Repair: replace `T` by `f(X)` (a subcontinuum
   of a tree, hence a tree). This route avoids it: only `G ⊆ thickening δ X` is needed of the graph
   (`ho16_theorem4`), and the grid gives it. **An unargued step**; not counted.

HO.8. **Theorem 1′, p. 212.**
   > Theorem 1′. A continuum X is homeomorphic to the pseudo-arc if and only if X is hereditarily
   > indecomposable and has surjective semispan zero.

   (checked on the page image; the text layer renders the prime as "10"). The defect of HO.1:
   false for a one-point continuum.

   **Batch 194: reclassified as a false printed statement at a degenerate case**, with the
   certificate `ho16_theorem1prime_printed_false` (`HO16B.lean`; `X` a one-point space, which is a
   continuum and hereditarily indecomposable by H–O pp. 177–178 as quoted under HO.1, has surjective
   semispan zero in the sense of p. 212, `SurjSemiSpanZero`, and is not a pseudo-arc). It is counted
   as the ledger counts Jones 1949 Theorem 1 and Moore 1920 Theorem 4 (refuted for a one-point
   continuum or set). **Why HO.1 and HO.8 are counted differently:** Theorem 1 is stated correctly
   on p. 180, so the p. 211 wording is a slip in a restatement; Theorem 1′ is stated correctly
   nowhere, although p. 212 presents it as what "our proof of Theorem 1 in fact establishes". (The
   ledger keeps no running number of false printed statements, only of defective proofs; the
   classification is recorded here.)

HO.9. **Lemma 6, p. 185** ("We record here some basic properties of simple folds. The proofs of
   these properties are left to the reader."). Stated without proof. Items (1), (2), (4), (5), (6),
   (7) are **verified** for folds in the sense of `IsSimpleFoldOf` (`ho16_lemma6`, `Lemma6.lean`);
   item (3) ("F₁, F₂, and F₃ are regular subsets of F") holds by definition (each `Fᵢ` a PL graph).
   (7) is formalized as: `φ` maps every neighbourhood of `p` in `Fᵢ` onto a neighbourhood of `φ(p)`
   in `G`. Nothing to record against H–O.

HO.10. **The construction, pp. 185–186.**
   > It is straightforward to see that this is a well defined simple fold, and if F′ is another
   > simple fold on G with projection φ′ such that φ′(F′ᵢ)=Gᵢ for i=1, 2, 3, then there is a
   > homeomorphism θ: F′ → F with θ(F′ᵢ)=Fᵢ for i=1, 2, 3 and φ′=φ∘θ.

   The **existence** is verified in the form of commission 194 §4, by graphs of PL height functions
   in `E × ℝ`, not by the quotient (`exists_simpleFold`, `FoldExists.lean`). The **uniqueness**
   clause: not formalized, not used (Theorem 8 is proved for every fold in the sense of
   `IsSimpleFoldOf`). Not counted.

HO.11. **Proposition 7, pp. 186–187.** Proved as stated (`ho16_prop7`, `Prop7.lean`). Three steps are
   unargued and are supplied:
   * "By (F2) and (F3), and since G is connected, there is a component K of G₂ which meets both
     cl(G₁ \ G₂) and cl(G₃ \ G₂)" (bars checked on the page image): `G₂` has finitely many
     components; if none met both closures, grouping them by the closure they meet splits `G` into
     two disjoint nonempty closed sets (`exists_comp_meets_both`).
   * The application of Claim 7.1 to "the closure of the component of C\φ⁻¹(∂G₃) containing p"
     needs `φ(C′) ⊆ G₂`, which is not argued. The formal proof takes the commission's route without
     boundary bumping: `K` the component of `G₂` containing `φ(p)`; if `K` missed `∂G₃`, the two
     copies of `K` over `G₁` would be clopen in `F`, so `φ(C) ⊆ K` would miss `∂G₃`; hence Claim 7.1
     applies to the `F₂`-copy of `K` (`image_comp_mem_nhds_glue`, `image_comp_eq`).
   * "It is straightforward to check from the definition of a simple fold that if C ⊂ F is a
     component with φ(C)=G, then F′ … is a simple fold on G": every clause of `IsSimpleFoldOf` is
     checked; the check rests on a lemma H–O do not state (commission 194 §7, Lemma (L): a component
     `K` of `G₂` missing `∂G₁` is a component of `G₃` whose copies over `G₃` are clopen in `F` and
     disjoint from `C`; so `K₂ ⊆ C` forces `K₁ ∪ K₃ ⊆ C`; and `K` cannot miss both frontiers). **No
     clause fails.** The referee's two regression tests (`G = [0, 4]`, `G₁ = [0, 3]`,
     `G₃ = [½, 1] ∪ [2, 4]`; `G = [0, 3]`, `G₁ = [0, 1] ∪ [2, 3]`, `G₃ = [½, 3]`) agree with the
     theorem (checked by hand, not formalized): the restrictions are `([0, 3], [2, 3], [2, 4])` and
     `([0, 1], [½, 1], [½, 3])`. Unargued steps; not counted.

HO.12. **Two remarks, p. 186.**
   > In general, even if G is connected, a simple fold F on G need not be connected.

   **Right.** Example: `G = [0, 2] ⊆ ℝ`, `G₁ = G`, `G₂ = G₃ = [1, 2]`; then `∂G₁ = ∅`, so
   `F₁ ∩ F₂ = ∅` and `F₁ ∩ F₃ = ∅`, and `F₁` and `F₂ ∪ F₃` are disjoint nonempty closed sets
   covering `F` (an instance of the next remark).
   > Note that if G is connected and ∂G1=∅, then G1=G, F is disconnected, and φ|F1 is a
   > homeomorphism of F1 onto G.

   **Right**: `∂G₁ = ∅` makes `G₁` clopen in `G` (`G \ G₁ = G₃ \ G₂` is then closed), hence
   `G₁ = G`; (F5) gives `F₁ ∩ (F₂ ∪ F₃) = ∅`, and `F₂ ≠ ∅` by (F1); and `φ|F₁` is a homeomorphism
   onto `G₁ = G` by (F4). Checked in words; not formalized.

No statement of Hoehn–Oversteegen or Krasinkiewicz–Minc is refuted in batch 193 beyond the
degenerate readings of HO.1 and HO.8 (misprints), and no defective proof is added. The count of
defective proofs stays at sixteen. Batch 194: HO.8 (Theorem 1′ as printed) is now a false printed
statement at a degenerate case, with certificate; HO.1 stays a misprint, with certificate; HO.4's
further observation is withdrawn; HO.9–HO.12 add no refutation and no defective proof. The count of
defective proofs stays at sixteen.

**Batch 195** (commission 195 §10; quotations checked against page images of H–O pp. 190, 191, 192,
199, 200 at 200 dpi).

HO.13. **p. 183, branch points and endpoints.** Reading: a point which is "neither a branch point
   nor an endpoint" is formalized as `IsOrdinaryPt G x` (a neighbourhood of `x` in `G` is the union
   of two segments `[a, x]`, `[x, b]` meeting only at `x`). It does not mention a decomposition;
   for every decomposition `S` of a PL graph it is equivalent to "`x` is interior to an edge, or
   exactly two edges end at `x`" (`isOrdinaryPt_iff_order`, `PLLib2.lean`), and a PL graph has
   finitely many non-ordinary points (`IsPLGraph.finite_not_ordinary`). The equivalence with H–O's
   cutpoint definitions is not formalized. Not counted.

HO.14. **p. 190, the observations after Definition 9.** Unargued; **verified** under the PL reading
   (`ho16_obs9_emptyB`, `ho16_obs9_emptyA`, `ho16_obs9_nhds`, `ho16_obs9_char`, `ho16_obs9_unique`,
   `Sides.lean`). Hypotheses used: `σ_∅(A)` as a union of components needs only `G` a PL graph
   (components are relatively open, finitely many); `σ_B(∅) = ∅` needs nothing. The
   characterization (existence, with `A ⊆ σ_B(A)`, `σ_B(A)` regular, `∂σ_B(A) = B`, agreement with
   `A` near `B`) needs `A` a PL subgraph, `B ⊆ ∂A` and consistent complement, but **neither `G`
   connected nor `A`, `B` nonempty**. The neighbourhood form and uniqueness need `G` connected and
   `B ≠ ∅` (each component of `G \ B` must have `B` in its closure), but not `A ≠ ∅`. Not counted.

HO.15. **Proposition 10, p. 190.** First part ("follows immediately from the observations after
   Definition 9"): proved from `ho16_obs9_char` and `ho16_obs9_unique` (and `σ_∅ = G` for connected
   `G` when `B = ∅`). Second part: the commission's reading is **confirmed**. H–O's step "since A′
   has consistent complement relative to B, we must have x∈B" needs `∂C′ ∩ B ≠ ∅`; consistency
   only gives the dichotomy `∂C′ ⊆ B` or `∂C′ ∩ B = ∅`, and nothing in the proof excludes the second
   alternative for a component `C′` of `G \ A′` that merely meets `C ∩ V` (the point `x ∈ ∂C′ ∩ C`
   need not lie in `V`, and `V` is the hypothesis's neighbourhood, which may be large). The
   statement is right. The formal proof (`ho16_prop10`) does not repair H–O's argument by shrinking
   `V`; it uses the first part instead: `C̄ ∩ B ≠ ∅` and consistency of `A` give `∂C ⊆ B` (the step
   H–O leave unstated), so `C` is a component of `G \ B` missing `A`, hence missing
   `σ_B(A) = σ_B(A′) ⊇ A′`; so `C ⊆ G \ A′`, and since every connected subset of `G \ A′ ⊆ G \ B`
   through a point of `C` lies in `C`, `C` is a component of `G \ A′`. **Classification
   (proposed): gap in a proof; statement true; not counted as a defective proof** — the repair is
   short (either the commission's shrinking of `V`, or the route above through the first part of the
   same proposition), as for the shrunk `ε₁` of the Hagopian 1976 entries (p. 346). If the commissioner prefers
   to count it, it would be the seventeenth.

HO.16. **Proposition 11, pp. 190–191.** Proved as stated (`ho16_prop11`). The three unargued steps
   are supplied: (F1) "Clearly G₁, G₂, and G₃ are all regular" is the characterization of p. 190
   (`IsPLGraph.sideOf_char_aux`); "If x∈A, then we must have x∈B₂" and "one can find a neighborhood
   of x which meets only A and components of G\A whose closures meet B₂" rest on the finiteness of
   the components of `G \ A` (`IsPLGraph.finite_components_diff`) and on `∂C ⊆ B₁ ∪ B₂`,
   `∂C ≠ ∅` for each component `C` (`G` connected). `ho16_prop11_frontier` (`∂G₁ = B₁`,
   `∂G₃ = B₂`) needs neither `G` connected, nor `A ≠ ∅`, nor `B₁ ∩ B₂ = ∅`. The remark after the
   proof is **verified** (`ho16_prop11_remark`; `A ⊆ G` is not needed). Not counted.

HO.17. **p. 192, the observation after Definition 12.** Unargued; **verified** (`ho16_obs12`: the
   image under `π` of a relatively open subset of `S \ 𝓔(S)` is relatively open in `G`). "comple
   ment" in (S4) of Definition 13 (p. 192; also visible in the page image): a stray space,
   typographical. Definitions 12, 13 and 16 were checked clause by clause against the page images of
   pp. 192 and 199–200: no mismatch with `IsGeneric`, `IsStraight`, `endSet`, `IsStairwellStr`,
   `IsBrokenStairwellStr` (finiteness of `𝓔(P₁)` is not a clause of Definition 16 and is not
   imposed; it follows from straightness). Not counted.

HO.18. **pp. 193–194, "G connected" missing.** The remark of p. 193 ("if k is odd then π(S)=G")
   and the height-1 remark of p. 194 ("π maps S homeomorphically onto G") are false for a
   disconnected `G` (`ho16_p193_remark_false`: `G = [0, 1] ∪ [2, 3]`, `S = [0, 1] × {½}`), and H–O's
   convention of p. 184 ("G will denote a (not necessarily connected) graph") does not supply
   connectedness. Both remarks point to Proposition 14, whose hypothesis is "G is a connected
   graph", and both are proved with it (`ho16_odd_image`, `ho16_height_one`). **View:** agreed with
   the commission — omitted hypotheses, harmless, not counted (as HO.1). The reader is sent to
   Proposition 14 explicitly ("it will follow from the next proposition"), and every later use
   (Theorem 20) is for connected `G`.

HO.19. **pp. 193 and 200, the observations on components.** Unargued; **verified relative to the
   component `C`** (`ho16_obs13_comp`, `ho16_obs16_comp`): a component of a PL graph is clopen, so
   frontiers, components of complements, consistent complements and ordinary points in `C` are those
   in `G`. Not counted.

HO.20. **Proposition 17, p. 200.** "It is now easy to verify": **verified** (`ho16_prop17`, with
   H–O's relabelling written out; `ho16_prop17_exists`). The hypothesis `3 ≤ k` is not printed and
   is added (for `k ≤ 2` the conclusion has height `≤ 0`, outside Definition 16); harmless, since
   Theorem 20 applies the proposition only for odd `k ≠ 1`. The remarks of p. 201 are **verified**
   (`ho16_rem17_gamma`; `ho16_rem17_P1`, with `G` connected, as printed). The p. 201 remark on (S6′)
   (the pit cannot in general be put at level `k − 2`; optional): the mirror relabelling
   `P₁ = S_k`, `P₂ = S_{k−1}`, `γ′_{k−2} = α_{k−1}`, `β′_{k−2} = ∅` satisfies (S1′)–(S5′) by the
   same checks, but (S6′) then asks `π(α_{k−2}) ∩ π(S_{k−1} ∪ S_k) = ∅`, which (S1)–(S5) do not give
   (for `k = 3` it holds trivially, `α₁ = ∅`; for `k ≥ 5` nothing prevents a point of `π(α_{k−2})`
   from lying under `S_{k−1}`). No explicit example is given; not formalized. p. 210 ("S has a stairwell structure of height k−2") says more
   than the remark of p. 201, which gives it to `S₁ ∪ … ∪ S_k ⊆ S`; harmless. Not counted.

HO.21. **Lemma 18, pp. 201–202.** Proved (`ho16_lemma18`, `Lemma18.lean`). Unargued and supplied:
   regularity of `π(S′)` and `π(S″)` (finitely many components): `F ∩ φ⁻¹(π(S))` is a PL graph plus
   finitely many points (`IsPLGraph.inter_preimage_fst`), and it has no isolated points
   (`lemma18_points`), so it is a PL graph (`isPLGraph_union_finite`); and "for x∉(∂F₂)⋆, x∈𝓔(S′)
   iff φ⋆(x)∈𝓔(S)" (`lemma18_points`, from Lemma 6 (7) on the open sheets). H–O's claim is
   `lemma18_claim` / `lemma18_claim'`; their "By hypothesis" also covers the case where `φ(π(x))` is
   interior to `π(S)`, which needs no hypothesis (harmless). Misprints on p. 202: "𝓔(S″)⊂(F₁∩F₂)⋆
   since S″⊂(F₁∩F₂)⋆" for `F₁ ∪ F₂` (twice), "S″ is a straight" (a word missing). Not counted.

HO.22. **pp. 202–203, the fold of Proposition 19.** **Verified** (`ho16_prop19_fold`): the two
   identities `π(P₁) = σ_{π(𝓔(P₁))}(π(P₂))` and `σ_{π(γ)}(π(S_{i₀})) = σ_{π(γ)}(π(P₂))`, the fold
   (F1)–(F3) by Proposition 11, and (19.1)–(19.3) as frontiers of `G₁`, `G₃`, `G₂`. The hypothesis
   `γ_{i₀} ≠ ∅` of Proposition 19 is not needed for this first step (with `γ = ∅` the identities
   still hold, `σ_∅ = G`). Omitted citations (harmless): Proposition 11 also needs (S4′); the first
   identity also uses (S4′) and `𝓔(P₁) ≠ ∅`, where H–O cite (S3′). Not counted.

Batch 195 adds one gap in a proof (HO.15, Proposition 10, second part; statement true; proposed not
counted) and no refutation of a statement read with its intended hypotheses (HO.18 records omitted
hypotheses, as HO.1). The count of defective proofs stays at sixteen.

HO.23. **pp. 203–206, straightness and end sets in Proposition 19.** Unargued and **supplied**:
   "clearly each of φ⋆⁻¹(P₁)∩(F₁)⋆, φ⋆⁻¹(P₂)∩(F₂)⋆, and φ⋆⁻¹(S_{i₀})∩(F₃)⋆ is straight"
   (`P19.straight_T'₀`, with `π(S′_{i₀}) = F₁ ∪ F₂ ∪ (F₃ ∩ φ⁻¹(π(S_{i₀})))` a PL graph,
   `P19.isPLGraph_image_T'₀`, `isPLGraph_sheet_inter_preimage`), and the "straightforward
   observations" of pp. 205–206 (`P19Ctx.lean`, `Prop19A.lean`: (19.4)–(19.9) through Lemma 18,
   `P19.straight_T`, `P19.straight_P'₁`, `P19.straight_P'₂`, `P19.endSet_T'₀`). Misprints (checked
   at 200 dpi, p. 207 also at 400 dpi): "S′_{i₀}∩(F₃)⋆=φ⁻¹(S_{i₀})∩(F₃)⋆" (p. 205, and
   "π(S′_{i₀})∩F₃=φ⁻¹(π(S_{i₀}))∩F₃" on p. 207, where `φ⁻¹` is right) and
   "φ⋆⁻¹(α_{i₀})∩(F₃)⋆=φ⁻¹(α_{i₀})=α′_{i₀}" (p. 206), `φ⁻¹` for `φ⋆⁻¹`; "P′₁∩(∂F₃)⋆=φ⋆⁻¹(γ_{i₀})
   by (19.2)" (p. 205), false as printed whenever `γ ≠ ∅` (`φ⋆⁻¹(γ)` also contains the points over
   the `F₁`-copies of `π(γ)`, outside `(∂F₃)⋆`), for `φ⋆⁻¹(γ_{i₀}) ∩ (∂F₃)⋆`; the next clause uses
   only `⊆`. Misprints, the argument intact. Not counted.
   *Addition (batch 197; confirmed by the commissioner on 400-dpi crops of p. 207):* in the (S4)
   paragraph, "`Also, we have C⊂F₃\φ⁻¹(π(S_{i₀})), since S′_{i₀}∩(F₃)⋆=φ⁻¹(S_{i₀})∩(F₃)⋆`": the
   second `φ⁻¹`, the one applied to `S_{i₀}`, is a third `φ⁻¹` for `φ⋆⁻¹`. A misprint of the same
   kind as those above; not counted.

HO.24. **p. 207, (S3) and (S3′) for `S′`.** "It is then straightforward to see from property (S3′)
   for S and from the definition of S′ᵢ that there exists a neighborhood V": unargued,
   **supplied** (`P19.S3'T`, `P19.S3'P`, `P19.S3'γ`): the neighbourhoods of (S3′) for `S` pulled
   back along `φ`, away from `F₁ ∪ F₂` at levels `i₀`, `i₀ + 1`, away from `F₃` for `P′₂`; at the
   points of `∂F₃` by the two spokes of `IsSimpleFoldOf.isOrdinaryPt_of_mem_inter`. Slips on
   p. 207: "neighborhood of β_{i₀}=α_{i₀+1} in G" and "neighborhood of β′_{i₀}=α′_{i₀+1}" for
   `π(β_{i₀})`, `π(β′_{i₀})` (confirmed); "P′₂=φ⁻¹(π(S_{i₀}))∩(F₁∪F₂)" for `π(P′₂)` (the start of
   the printed line was not legible in our scan; the visible part reads "…(π(S_{i₀}))∩(F₁∪F₂)
   agree"). Not counted.
   *Addition (batch 197; confirmed by the commissioner on 400-dpi crops of p. 207):* the start of
   the line in (S3) does read "`P′₂=φ⁻¹(π(S_{i₀}))∩(F₁∪F₂) agree`": `P′₂` is printed for `π(P′₂)`.
   The slip is confirmed as printed; not counted.

HO.25. **p. 208, (S4′) for `P′₂`.** "Moreover, φ(D)⊂π(P₁∪P₂), so ∂D̃∩π(α_{i₀})=∅ by (S6′) for S.
   This means that either ∂D̃⊂π(β_{i₀}) or ∂D̃⊂π(γ_{i₀}).": **false** in a legitimate configuration
   (certificate `ho16_p208_false`, `P208.lean`: commission 196 §4's structure of height 3 with a
   pit at level 2 on `G = [0, 10]`, `a = 11/2`, every sheet at height `1/2`; `x = 3/2 ∈ π(P₂) \
   π(S₂)`, whose component `[0, 4)` in `G \ π(S₂)` has frontier `{4} = π(α₂)`). The example was
   checked in Lean, (S1′)–(S6′) included; no error found. Every `x ∈ π(P₂) \ π(S_{i₀})` is `φ` of
   a point of `F₂` whose component in `F \ π(P′₂)` lies in `F₁ ∪ F₂`, so the sentence fails for
   every fold. The proposition and the paragraph's conclusion are true: **proved** with the case
   split of commission §3 (`P19.split_P'₂`; if `∂D = ∅` nothing to show, otherwise a point of
   `∂D` lies over `∂D̃ ∩ π(P₁ ∪ P₂)`, which misses `π(α_{i₀})` by (S6′), and consistency of
   `π(S_{i₀})` does the rest). The sentence fails only for components `D` of `F` (`∂D = ∅`), which
   the restriction of p. 209 discards. **Counted as a defective proof (the seventeenth)**, as
   proposed: a sentence printed false, with a missing case, inside the proof of a true
   proposition, as for Moore 1925 Theorem 11 and Jones 1955 Theorem 1, and unlike the gaps (HO.15,
   nothing printed false) and the misprints of HO.23 (a formula misprinted, the argument intact).

HO.26. **p. 208, (S5′).** "the set of branch points and endpoints of F is φ⁻¹(Z)" and "It is then
   trivial to see …": unargued, **supplied** by `IsSimpleFoldOf.isOrdinaryPt_iff` (`OrdFold.lean`;
   if every point of `∂G₂` is ordinary in `G`, then `z ∈ F` is ordinary in `F` iff `π(z)` is
   ordinary in `G`) and `P19.gen'_stair`, `P19.gen'_broken`. H–O's list puts `π(γ′_{i₀+1})` before
   `π(𝓔(P′₁))`, the reverse of Definition 16's order; harmless (pairwise disjointness). Not counted.

HO.27. **p. 209, the connected fold.** The existence of `K` (a component of `π(P₂)` meeting
   `π(𝓔(P₁))` and `π(γ_{i₀})`): unargued; **not needed** in the formal proof, which takes the
   component `C` given by the first part of Proposition 7 (`ho16_prop7`: some component of `F`
   whose image meets `∂G₁` and `∂G₃`, and then `φ(C) = G`). "clearly C meets ∂F₃ by Lemma 6 (6)":
   right, unargued, **supplied** (`P19.comp_meets_F₂₃`: a connected `C ⊆ F` with `φ(C) = G` meets
   `F₂ ∩ F₃`, by the sides of Lemma 6 (6)). Restriction to `C`: `ho16_prop19`. Not counted.

HO.28. **pp. 209–210, Theorem 20 (forward direction, from Theorem 15).** **Proved relative to
   Theorem 15** (`ho16_theorem20_of_thm15 : HOThm15 → HOThm20`; induction `ho16_lift_stairwell`).
   The reduction to connected `G` (unargued details) is supplied: each component `C` of `G` is
   clopen, `M ∩ C⋆` separates `C × {0}` from `C × {1}` in `C⋆` with the same open sets, and the
   maps on the clopen sets `f⁻¹(C)` are glued. The fold count "after a sequence of at most
   (k₀−1)+(k₀−3)+...+1 simple folds": each pass from height `k` to `k − 2` (Proposition 17, then
   Proposition 19 from pit level 1 to `k − 2`) uses at most `k − 2` folds, so at most
   `(k₀ − 2) + (k₀ − 4) + … + 1 = ((k₀ − 1)/2)²` folds in all; the printed sum mixes parities
   (for odd `k₀` its terms are even, ending in `2`, not `1`), and it is an upper bound either way.
   Harmless (only finiteness is used; the formal induction does not count folds). Earlier records
   stand: "εᵢ chosen small enough so that h(X)⊂U" is unneeded (`h(X) ⊆ S ⊆ U`), and "if γ_{i₀}=∅,
   then in fact S has a stairwell structure of height k−2" says more than the remark of p. 201
   (HO.20). Not counted.

Batch 196 adds one defective proof (HO.25, p. 208, the (S4′) argument for `P′₂` in Proposition 19;
the proposition is true and proved). The count of defective proofs rises from sixteen to
seventeen.

HO.29. **p. 195, Claim 15.1.** "We leave it to the reader to show that there exists a set M′ having
   properties (1), (3), (5), and (6), and which separates G×{0} from G×{1}." The main construction
   of the proof of Theorem 15, unargued; and in "Replacing M′ by a subset (which, by abuse of
   notation, we also denote by M′) which irreducibly separates G×{0} from G×{1} in G⋆ accomplishes
   (2)", that the subset keeps (1) and (3) is not argued. **Replaced** on this route by
   `exists_ladder` (`HO16E.lean`, from `exists_ladder_aux`, `LadderExists.lean`): inside any open
   `U` containing a separator there is a ladder (`IsLadder`, `LadderDefs.lean`), built from a
   Lipschitz sign function `u = infDist · K₀ − infDist · K₁` (`exists_sign_fn`, `LadderSep.lean`;
   the Lipschitz bound replaces the uniform continuity of the commission's route), a grid of edges
   shorter than `δ` and heights `q/N`, and a uniform subdivision of each grid edge with one sign
   flip per piece (`subdiv`, `LadderSubdiv.lean`; `chg_flip`, `LadderSign.lean`). No irreducible
   separator is needed. Also on p. 195 (checked at 200 dpi, with the commissioner's 400-dpi crop):
   in the definition of a side wedge, "C₂ are arcs which both have x as an endpoint but are
   otherwise disjoint", `x` for `(x, y)` (the arcs lie in `G⋆`): a misprint. In the paragraph on
   property (4), "Note that (x,y) cannot be an endpoint of M′, because x is not an endpoint of G by
   (5), and π(M′∩V) is open for some neighborhood V of (x,y) by (3)": here `(x, y) ∈ T`, and (3)
   speaks only of points of `M′ \ T`, so it does not give the openness at `(x, y)`; the step is true
   (an end point of `M′` could be removed with a small neighbourhood, against irreducibility), so
   this is a wrong citation for a true step. Not counted (an unargued construction, a misprint and
   a wrong citation; nothing printed false about the objects of the proof).

HO.30. **pp. 195–196, branch points of `M′`.** "Because M′ is an irreducible separator, the
   complementary regions of M′ in D alternate between R₀ and R₁. It follows that n is even.";
   "Obviously this can be done without compromising properties (1), (5), and (6), and without
   leaving U."; "It is easy to see that the resultant M′ still irreducibly separates G×{0} from
   G×{1} in G⋆." Unargued; **not used** on this route: the sheets of a ladder meet the vertical
   lines over vertices of `G` only at the list points `(v, yᵢ(v))`, and over an edge each sheet is a
   finite union of non-vertical segments (`isStraight_ladderSheet`). Not counted.

HO.31. **p. 196, odd counts.** "Observe that since Z′∩π(T)=∅ and since M′ irreducibly separates
   G×{0} from G×{1}, for each point a∈Z′, the set M′∩{a}⋆ contains an odd number of points."
   Unargued. On this route the odd counts come from sign changes: the list at a vertex `v` holds the
   midpoints of the `q` with `σ(v, q) ≠ σ(v, q + 1)`, and the sign sequence goes from `−` (at
   `q = 0`) to `+` (at `q = N`), so the number of changes is odd (`odd_length_chg`,
   `LadderSign.lean`; used in `LData.isLadder`). Not counted.

HO.32. **p. 197, the wedge edge.** "Clearly W∩{a}⋆ consists of two consecutive points"; "Observe
   that M′∩{b}⋆ contains exactly j−2 points": unargued, true in H–O's setting. On this route the
   corresponding facts are the definition of a ladder (`ev s = some (m, λ, h)` forces
   `j(s.2) = j(s.1) + 2`, places `m`, `m + 1` at `s.2`) and, for the ladder built in
   `exists_ladder_aux`, the case analysis of one flip (`chgPair_cases`, `wedgeEv_eq_some`,
   `wedgeEv_eq_none`). "Observe that S is in U, and clearly S irreducibly separates G×{0} from G×{1},
   because M′ does.": the second half is not argued (`S` is not `M′`: the zig-zags are added) and
   **not needed**: H–O use it on p. 198 for "there are no other points in the end sets of the S_i's
   because S irreducibly separates G×{0} from G×{1} in G⋆", which on this route follows from the
   construction (`relFrontier_image_fst_ladderSheet`, `endSet_ladderSheet`, `LadderStair2.lean`).
   That every sheet lies in `U ∩ G × (0, 1)` is `LData.sheet_corners` with
   `heightOK_of_mem_piece`. Not counted.

HO.33. **p. 198, the stairwell structure from the ladder.** "It is clear that S_i^{[a,b]} is
   straight"; "Properties (S3) and (S5) are immediate from the construction."; "It is now easy to
   see that each of x₁ and x₂ corresponds to the tip point of a side wedge or a turning point of a
   zig-zag joining S_{j₁−1} and S_{j₁}.": unargued; **supplied** in explicit form by
   `ho16_stairwell_of_ladder` (`ladder_isStairwellStr`; (S1) `injOn_fst_ladderSheet`,
   `isPLGraph_image_fst_ladderSheet`; (S2) `relFrontier_image_fst_ladderSheet`; (S3) `ladder_S3`;
   (S4) `ladder_S4` through `relFrontier_comp_ladder` and the parity argument `vertex_label`;
   (S5) `ladder_S5`), with `α_i` given explicitly (`ladderAlphaSet`), since the sheets overlap on
   the zig-zag lines and H–O's choice "β_i=α_{i+1}=S_i∩S_{i+1}" is not available. The construction
   of pp. 196–197 itself is right (our reading agrees with the commission's: the `J_i` ordered from
   `π(W)` toward `b`, `C¹_i`, `C²_i`, `C³_i` into `S_i`, `S_{i−1}`, `S_{i−2}`), with one unstated
   condition: nothing excludes `b ∈ J_j`; then `π(C¹_j) ⊇ J_j ∋ b`, so `C¹_j` reaches `{b}⋆`, where
   `S_j` should have no point ("S_i^{[a,x]}∩{a}⋆=∅ if i>j" read at `b`), and two end sets could
   meet over `b`, against (S5). The `J_i` must lie in the open arc; a choice H–O are free to make,
   so a gap in the wording, not in the argument. On a ladder the zig-zag intervals `[lᵢ, rᵢ]` lie in
   `(0, λ)` by definition (`zz_lr`, `zz_lam`). In the (S4) argument (checked at 200 dpi):
   "Since a_i∈C for p=2, ..., n−1", `a_i` for `a_p`, a misprint; and the case split ("If C⊂[a,b]
   …"; "Suppose, on the other hand, that x₁,x₂∈∂C do not belong to the same component of G\Z′")
   omits a component not inside one arc whose two frontier points lie on one arc (it runs around a
   cycle of `G`); the same chain argument through the vertices of `C` covers it, and on this route
   the frontier of every component is handled at once (`relFrontier_comp_ladder`: every frontier
   point lies at the first piece of sheet `i` on a wedge edge leaving a vertex of `C`, labelled by
   the parity of `i`). "|M′∩{z}_*|<i" prints an asterisk for the star (the commissioner's 400-dpi
   crop): typography only. Not counted: a gap (a missing case, nothing printed false) and
   misprints, as HO.15 and HO.23.

HO.34. **p. 198, Figure 8.** "We leave it to the reader to observe that this set S irreducibly
   separates G×{0} from G×{1}." In words (a sketch only), the reason is the parity count of p. 198: over each
   point of `G` off the finitely many end points the set meets the vertical segment an odd number
   of times, so the bottom and the top lie in different components of the complement; and each
   point of the set is needed, since cutting a small open arc out of a sheet joins a region below it
   to a region above it. Not
   formalized (not needed: a ladder need not separate, and Theorem 15 asks only for a stairwell
   structure inside `U`). Not counted.

HO.35. **pp. 194–195, the cited theorem.** "It is well known (see e.g. [26, Theorems 46.VII.3 and
   49.V.3]) that for any set S⊂G×(0,1) which separates G×{0} from G×{1}, there is a closed set
   S′⊆S which irreducibly separates G×{0} from G×{1}." **Not used** on this route (`exists_ladder`
   works from any separator, irreducible or not). Recorded; not checked against the cited source.
   Not counted.

**Theorem 15 (p. 194).** **Proved** (`ho16_theorem15 : HOThm15`, from `exists_ladder` and
`ho16_stairwell_of_ladder`), and with it Theorem 20 (`ho16_theorem20 : HOThm20`) and H–O's main
statement on p. 180 for indecomposable continua, with no named hypothesis
(`ho16_indec_homogeneous_pseudoArc`; with Bing's converse, `ho16_indec_homogeneous_iff`). The proof
of Theorem 15 on pp. 194–198 is replaced at Claim 15.1 (HO.29) and made explicit on pp. 196–198
(HO.30–HO.33).

Batch 197 adds no defective proof (HO.29–HO.35: unargued steps, a construction left to the reader,
one wrong citation for a true step, one unstated condition, one missing case of a case split, and
misprints; nothing printed false about the objects of a proof) and no refutation. The count of
defective proofs stays at seventeen.

### Bing–Jones 1959 (batch 198)

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
171–192 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`). Every quotation
below was checked against page images rendered at 200 dpi, and the items marked (400) against
400-dpi crops. The commission's second reading (commission 198 §7, items 1–16) is **confirmed** in
every item checked; nothing is corrected. Theorems 7–10 and §7 are not formalized yet: items BJ.6–BJ.15
are recorded as readings, to be revisited when those sections are done.

BJ.1. **p. 173 (400), a misprint.** "In Theorem 10 we show that any two continuous snake-like arcs
   of pseudo-arcs of homeomorphic—indeed there is a very strong type of homeomorphism between
   them.": `of` for `are`. Typography only. Not counted.

BJ.2. **pp. 173, 189, the passage to circles.** p. 173: "It follows from Theorem 10 that any two
   circles of pseudo-arcs are topologically equivalent and that each is homogeneous." Not argued.
   **Supplied** from Theorem 10 (as the named `Prop` `BJThm10`): the halves of a circle of
   pseudo-arcs are continuous snake-like arcs of pseudo-arcs (`isContArcPA_halfMap`,
   `isSnakeLike_halfSet`, `HPC/BJ59/Halves.lean`), and Theorem 10 on the two halves with the same
   end maps glues to a homeomorphism (`exists_homeomorph_glue`, `HPC/BJ59/Glue.lean`); hence
   `homeomorph_of_isCircleOfPA` and `isHomogeneous_of_isCircleOfPA` (`HPC/BJ59/BJ59A.lean`). Not
   counted (an unargued step).

BJ.3. **p. 174, Theorem 2, a missing step.** "If j<i<t, G(b, c) intersects d_i because G(b, c) is
   connected and intersects each of d_j and d_t." That `G(b, c)` meets `d_t` is not argued.
   **Supplied** (`order_core`, `HPC/BJ59/Order.lean`): `d_t` lies between the links of `D′` and of
   `D″`, so it meets neither `G(0, b)` nor `G(c, 1)`; since the chain covers `G = G(0, b) ∪ G(b, c)
   ∪ G(c, 1)`, `d_t` meets `G(b, c)`. Theorem 2 is proved (`bj_theorem2`). Not counted.

BJ.4. **p. 175, Theorem 3 (400), a misprint and a defective construction.** "Use A to denote the
   sum of the elements of F(1, v) and B to denote the sum of the elements of F(v, m). Then the
   elements of D are A·e_i, A·e_{i+1}, ⋯, A·e_j, f_{v+1}, f_{v+2}, ⋯, f_{w−1}, B·e_r, B·e_{r+1}, ⋯,
   B·e_s." `F(v, m)` is a misprint for `F(w, m)` (the preceding sentence: "E(r, s) covers each link of
   F(w, m)"). As written `D` is not a chain: `A·e_{j−1}` can meet `f_{v+1}` (through
   `f_v ∩ f_{v+1} ∩ e_{j−1}`, as `f_v ⊆ e_j`), and they are not adjacent in `D`; likewise
   `B·e_{r+1}` and `f_{w−1}`. **Repaired** (`chain_assembly`, `HPC/BJ59/Thm3Assembly.lean`): merge
   `f_{v+1}` into the last `A`-link and `f_{w−1}` into the first `B`-link,
   `A·e_i, …, A·e_{j−1}, A·e_j + f_{v+1}, f_{v+2}, …, f_{w−2}, B·e_r + f_{w−1}, B·e_{r+1}, …, B·e_s`
   (`f_{v+1}` meets `A` only inside `f_v ⊆ e_j`). That the result is an `ε`-chain from `g₀` to `g₁`
   is proved (`theorem3_arc`, `HPC/BJ59/Thm3.lean`; `bj_theorem3`). The statement of Theorem 3 is
   true. Proposed: a defective proof (the chain printed is not a chain), but with a one-line repair;
   **not counted** pending the commissioner's decision, as for HO.15 and HO.23 (nothing printed
   false about the objects of the theorem; the construction is wrong at two links).

BJ.5. **pp. 175–176, Theorem 5, false as printed.** "Suppose G is a snake-like arc of
   indecomposable continua {g_x|0≦x≦1} and E is a chain covering G such that E properly covers each
   g_x. Then if U is an open set such that U·G≠0, U·(g₀+g₁)=0, and Ū lies in a link of E, then G−U
   may be expressed as the sum of two mutually separated sets A, B such that g₀⊂A, g₁⊂B, and for
   each x (0≦x≦1), either A·g_x intersects each link of E or B·g_x intersects each link of E."
   **Refuted**:
   * *Degenerate certificate, in Lean* (`bj_theorem5_printed_false`): `X = [0, 1]`, `f = id` (a
     point is an indecomposable continuum in the library's sense), `E` one link, `U = (1/4, 3/4)`,
     `x = 1/2`: both `A·g_x` and `B·g_x` are empty.
   * *General construction* (commission §6; in prose, not formalized): from any instance with
     `n ≥ 3` links properly covering every fibre, merge the last two links (`e_{n−1} ∪ e_n` as the
     new `(n−1)`-st link, `e_n` kept); then `cl(e_n) ⊆ e_{n−1}` can be arranged, and for `0 < c < 1`
     a small neighbourhood `U` of `cl(g_c ∩ e_n)` with `Ū` in the new `(n−1)`-st link makes
     `g_c − U` miss `e_n`, so the conclusion fails at `x = c` for every separation. This is
     non-degenerate (no fibre lies in `U`). The library operation `chainMergeLast`
     (`HPC/BJ59/ChainOps.lean`) is the merge used here; the lemma producing the certificate from an
     arbitrary instance was not written (optional in the commission).
   * *The printed proof* passes from separations of `G − d_j` to separations of `G − U`.
   * **Repaired** (`bj_theorem5`, from `theorem5_repaired`, `HPC/BJ59/Thm5.lean`) with `f` open and
     `hEU`: no fibre meets a link only inside `Ū`. Proof: the commission's route, with topological
     limits superior in place of Hausdorff limits. The skeleton's `hE` (`E` covers `X`) and `hUE`
     (`Ū` in a link) turn out not to be used by the proof; they are kept, as in the skeleton.
     Bing–Jones's use on p. 185 is existential, so Theorem 10 is not affected.
   **Proposed for the count** as the twenty-third false printed statement: the general construction
   refutes it in non-degenerate cases (indecomposable non-degenerate fibres). The Lean certificate is
   the degenerate one; I would count it on the strength of the prose construction, and leave the
   count at twenty-two until the commissioner adopts it.

BJ.6. **p. 177, Theorem 7 (400), a misprint.** "Let p₁, p₂ be points of different components of P
   in d₁−d₂, d_n−d_{n−1}": `components` for `composants` (`P` is connected; compare p. 179, "p₁, p₂
   belong to different composants of P"). Confirmed. Reading; not counted.

BJ.7. **p. 178, Theorem 8 (400).** "Let U_A, U_B be open sets with closures in d₁, d₂
   respectively": `d_n` for `d₂` (confirmed on the crop; the case being treated is "H(y₁)=d₁,
   H(y_m)=d_n"). The two unargued steps of the commission's item 7 (the cover `U₁, …, U_t` "from
   Theorem 4", and the chain `e_k = e(a₁)_k·U₁ + ⋯ + e(a_t)_k·U_t`, whose links may meet for
   nonadjacent `k`, `l` inside `U_A + U_B`) are recorded; to be checked when Theorem 8 is
   formalized. Not counted.

BJ.8. **p. 180, Theorem 9 (400).** "and the links of G with closures in e_{n−1}·e_n are combined to
   form `e′_{4n−6}, e′_{4n−5}, e′_{4n−4}`": `F` for `G` (confirmed; the two preceding clauses say
   "links of F"). In the next paragraph, "`d₂′` is the sum of the other links of G in e₁−e₂;
   `d₄′, d₅′, d₆′` are formed by combining links of G in e₂−(e₁+e₃), ⋯, `d′_{4n−4}` is the sum of
   the other links of G in e_n−e_{n−1}": `d` for `e` throughout (confirmed). The final display ends
   "⊂ē_i" where the claim is "h(P·d_i)⊂e_i" (confirmed): the closure is not removed. Readings; not
   counted.

BJ.9. **p. 181 (400).** "Let E₂ be any G_i of mesh less than 1/3 that refines E_i and H₂ be any
   chain map of E₂ onto E₁ such that e²_j⊂H₁(e²_j)": `E₁` for `E_i`, `H₁` for `H₂` (confirmed; the
   next paragraph introduces "H₂ be any chain map" again, of `D₃` onto `D₂`). "d²_j⊂d¹_k=H₁(d²_j) if
   H₁(e²_j)=d¹_k": the last `d¹_k` should be `e¹_k` (confirmed as printed). "That h is a homeomorphism
   of P onto Q follows from an argument similar to …": unargued. Readings; not counted.

BJ.10. **p. 182 (400).** "E₁, D₁, H₁, E₂, K₁, D₂, H₂, E₃, K₃, ⋯": `K₂` for `K₃` (confirmed). Not
   counted.

BJ.11. **p. 185 (400).** "R_{(2i+1)/n}(f_y), R_{i/n}(f_y) are adjacent": `R_{(2i+1)/2n}` (confirmed
   as printed); "P(0, 1/n−ε)⊂A′_i": `P(0, i/n−ε)` (confirmed as printed). Not counted.

BJ.12. **p. 186 (400).** "link of the subchain of E_k that irreducibly covers Q(i/n, (i+1)/n)":
   `E₁` (confirmed as printed). Not counted.

BJ.13. **pp. 187–188, Theorem 10, steps by analogy.** Step 3 (Conditions I and II "similar to"
   Step 2) and "Steps 4, 5, ⋯. These steps are essentially repetitions of Step 3." Unargued by
   analogy. "intesects" (p. 187): typography. Recorded; not counted.

BJ.14. **p. 189 (400).** "But the closures of these two sets contain p and q respectively so
   ρ(p, q)<4/2^i": the meshes give `8/2^i` (commission's reading; harmless). Not counted.

BJ.15. **§7, pp. 189–191, a sketch.** "Now there exists a sequence D₁, D₂, D₃, ⋯ of circular
   chains of simple domains in the plane such that" (1)–(9): asserted, not constructed; "With the
   addition of (9) one may see with the help of [3] that each element of G is a pseudo-arc. It
   follows from Theorem 10 that M is homogeneous." Not argued: that `M` is not snake-like, that `G`
   is a continuous decomposition over a circle, that each element is a pseudo-arc. Recorded as the
   named `Prop` `BJPlaneExample`. Not counted.

BJ.16. **Definitions (p. 172–173).** (a) Chains: Bing–Jones require nonadjacent links to be "a
   positive distance apart" (p. 172), and Theorem 10's proof uses "chains whose nonadjacent links do
   not have closures that intersect" (p. 189); the library's `Chain` only makes nonadjacent links
   disjoint. Theorems 2 and 5 quantify over chains and Theorems 4 and 6 do not produce chains, so
   with the library's (weaker) chains they hold a fortiori for Bing–Jones's; Theorem 3 produces a
   chain in the library's sense only (a bridge to Bing–Jones's chains is not proved in this batch). (b) Circle-like: "A compact nonsnake-like continuum which for each positive number
   ε can be covered by an ε-circular chain is called circle-like." The library's `IsCircleLike` omits
   "nonsnake-like"; for a circle of pseudo-arcs it is automatic (commission §2), not formalized in
   this batch (optional). Not counted.

**Theorem 1 (p. 174)**, "Each snake-like continuum is unicoherent": in the library as
`HPC.Plane.isUnicoherent_of_isSnakeLike` (`HPC/Plane/Theorem11.lean`, Nadler 12.2), with the
recorded shape change that the ambient space is compact. Added to the batch-198 audit.

Batch 198 adds one candidate false printed statement (BJ.5, proposed for the count, not yet counted)
and one candidate defective proof (BJ.4, not counted). The counts stay at twenty-two false printed
statements and seventeen defective proofs, pending the commissioner's decision.

### Domokos–Prajs 2022 and Bing–Jones §§4–5 (batch 199)

Sources: A. Domokos and J. R. Prajs, *The Planck boundary within the hyperspace of the circle of
pseudo-arcs*, arXiv:2203.15906v1 (2022), §6, pp. 13–14 (`doc/sources/domokos-prajs2022.pdf`);
Bing–Jones 1959 as in batch 198. The quotations below were checked against page images rendered at
200 dpi (Domokos–Prajs pp. 13–14; Bing–Jones pp. 172, 176, 177, 179), and item BJ.17 against a
400-dpi crop. The commission's quotations agree with the page images in every item checked.

**Count after commission 199 §0:** BJ.5 is counted; twenty-three false printed statements and
seventeen defective proofs before this batch.

DP.1. **p. 14, atriodicity.** "Using the atriodicity of S¹ and of the pseudo-arc, and the
   atomicity of f one can easily show that X is atriodic." Unargued. **Not supplied** in this batch
   (`isAtriodic_of_atomic`, optional, is left open; `OPEN.md`). The commission's reading (§4: a
   triod in Domokos–Prajs's sense, "the union T of three continua A, B and C such that
   K = A ∩ B = B ∩ C = A ∩ C is a proper subcontinuum of each of A, B and C", p. 14; either `K` lies
   in no fibre and the three continua are saturated, or `K` lies in a fibre and all three contain
   it; in both cases three arcs of `S¹` pairwise meeting exactly in one arc or point) is recorded,
   not formalized. Not used by our route, which does not go through Hagopian–Marsh–Prajs. Not
   counted.

DP.2. **p. 14, the "only if" direction.** "It is known that the circle of pseudo-arcs from [4]
   admits an open, atomic map onto a circle with pseudo-arcs as fibers." The support offered is
   Example 6.1 (p. 13): Bing and Jones "constructed the *circle of pseudo-arcs*, denoted here by Ψ,
   which is a homogenous, decomposable and nowhere locally-connected continuum in the plane admitting
   a continuous decomposition into terminal pseudo-arcs" ("homogenous" as printed). Bing–Jones do
   not prove that the elements are terminal. Not used by our route. **Supplied in the plane** from
   Jones 1955: a decomposable homogeneous plane continuum that is not a simple closed curve has an
   open atomic map onto the circle with pseudo-arc fibres, atomic by `jones55_c`
   (`circle_or_atomic_of_decomposable`); under `BJThm10` and `BJPlaneExample` this applies to the
   plane circle of pseudo-arcs (`nonvac_atomic`). Not counted.

DP.3. **p. 14, the halves.** "Then f⁻¹(A) and f⁻¹(B) are atriodic folders of chainable continua in
   the sense of [7]. Therefore, they are chainable by Proposition 6 of [7]." True in this case;
   **replaced** by Bing's 1951 argument: an atomic map onto an arc with snake-like hereditarily
   indecomposable fibres has a snake-like domain (`isSnakeLike_of_atomic'`, `HPC/BJ59/Atomic.lean`),
   so the halves are snake-like (`isSnakeLike_halfSet_of_atomic`). No shape theory. Not a defect.

DP.4. **p. 14, the two definitions of a circle of pseudo-arcs.** Domokos–Prajs: "We call a
   continuum a circle of pseudo-arcs if it is homeomorphic to the original example Ψ of Bing and
   Jones [4]." Bing–Jones (and the library's `IsCircleOfPA`, `HPC/BJ59/Defs.lean`): a circle-like
   continuum with a continuous decomposition into pseudo-arcs whose quotient is a simple closed
   curve (as an open continuous map onto the circle with pseudo-arc fibres). Our theorems use the
   second: `dp22_theorem61` (given `BJThm10`) makes a compact space with an open atomic map onto the
   circle with pseudo-arc fibres homeomorphic to *every* `Y` with `IsCircleOfPA Y`, and
   `isCircleOfPA_of_atomic` makes it a circle of pseudo-arcs in Bing–Jones's sense when one exists.
   With `BJThm10` any two circles of pseudo-arcs in Bing–Jones's sense are homeomorphic
   (`homeomorph_of_isCircleOfPA`, batch 198), so the two definitions agree once one example exists
   (`BJPlaneExample`). Not counted.

BJ.17. **p. 172 (400), a misprint.** "Also, D *irreducibly covers* X of each link of D contains a
   point of X that is not covered by any other link of D.": `of` for `if` (confirmed on the
   400-dpi crop). Typography only. Not counted.

BJ.18. **pp. 176–177, Theorem 7, second sentence, false as printed for `n ≤ 2`.** "In fact, if A, B
   are closed sets in P·d₁, P·d_n respectively and H(x_r) = d₁, H(x_s) = d_n, the chain E may be
   selected so that A ⊂ e_r, B ⊂ e_s." **Refuted** in the degenerate case `n = 1`
   (`bj_theorem7_ends_printed_false`, a plane pseudo-arc `P`, `D` one link, `m = 3`, `H` constant,
   `A = B = {p}`, `r = 1`, `s = 3`: `p ∈ e₁ ∩ e₃`, not adjacent). `n = 2` fails in the same way
   (commission §6; in prose). Under the reading "closed in the subspace P·d₁" it fails for every
   `n ≥ 3` (commission §6: `H = (d₁, d₂, d₁, d₂, d₃)`, `r = 1`, `A = P·d₁`, `B = ∅`; in prose, not
   formalized). **Proved** for `n ≥ 3` under the skeleton's reading (`A`, `B` closed in the space)
   (`bj_theorem7_ends`), with the conclusion a chain in Bing–Jones's sense, the hypothesis on `D`
   only the library's (weaker) chain condition, and the surjectivity of `H` not needed (a chain map
   taking values `d₁` and `d_n` is onto). Proposed for the count as a degenerate false printed
   statement, under the reading the skeleton adopts; I agree with the commission that it should be
   counted, by the ledger's practice for degenerate failures.

BJ.19. **p. 177, Theorem 7, proof.** Recorded defects:
   (a) BJ.6, "points of different components of P" for composants (confirmed on the page image);
   (b) the special case's "A ⊆ e₁" is unargued (immediate: a point of `A` lies in `d₁` only);
   (c) the sequence `D₁ = D, D₂, …` crooked in one another is assumed without comment (supplied:
   `prependDesc`, `HPC/BJ59/Thm7Core.lean`, puts `D` in front of a late level of any description of
   `P`, crookedness from `PA51.eventually_crookedIn`);
   (d) the non-emptiness of `P·(d₁ − d₂)` and `P·(d_n − d_{n−1})` is assumed; our route avoids it:
   closed balls about points `p ∈ P·d₁`, `q ∈ P·d_n` in different composants (composants are dense)
   are removed from the neighbouring links (`exists_chain_isFrom`);
   (e) the chain `D′ = U₀, U₁, U₂, d₃, …, d_{n−2}, U_{n−1}, U_n, U_{n+1}` needs `n ≥ 4`; for `n = 3`
   its printed conditions cannot all hold (commission §6). **Repaired** for every `n ≥ 3` by a
   different chain of `n + 4` links (`exists_collar_chain`, `HPC/BJ59/Thm7Ends.lean`): `d₁` is
   replaced by three collars `{infDist · A < 2ρ}`, `{ρ < infDist · A < 3ρ}`, `d₁ ∩ {infDist · A > 2ρ}`
   and `d₂` by `d₂ ∩ {infDist · A > 3ρ}` (and symmetrically at `d_n`), so that `A` meets only the
   first link and `B` only the last; the walk `r, r, r, r − 1, …, 0, 1, …, m − 1, …, s, s, s` in `X`
   (Bing–Jones's `X′` with `y′`, `z′`) followed in it and folded back gives `E` (`bufIdx`, `bufPat`,
   `bj7_ends_compact`, `HPC/BJ59/Thm7Ends2.lean`);
   (f) "We suppose with no loss of generality that r<s": unargued (supplied by reversing the
   indices of `X`);
   (g) the case `n ≤ 2` of the first sentence is not treated (supplied: the first sentence is proved
   for every `n`, `bj_theorem7`, by following the pattern `H` along the walk
   `r, r − 1, …, 0, …, m − 1, …, s` and folding, with no special case and no reduction);
   (h) that the sums `e_i = e′_i + f_i + g_i` form a chain is not checked (supplied: `foldChain`,
   `HPC/BJ59/Thm7Fold.lean`; folding along a walk with steps of at most one and a section keeping
   adjacent indices adjacent gives a chain);
   (i) the conclusion is a chain whose nonadjacent links are at positive distance only after a
   shrinking step (`exists_bjChain_shrink`), not mentioned.
   Proposed for the count as a defective proof ((e): the printed construction fails for `n = 3`,
   and `n ≤ 2` is not treated); I would count it.

BJ.20. **p. 179, Theorem 9.** Not formalized in this batch (`bj_theorem9`, the stretch item, is
   left open; `OPEN.md`); BJ.8 and BJ.9 are not revisited. The "awkward condition" remark: "The
   rather awkward condition that each link of E is the image of a link of D that covers a point of
   P not covered by the closure of any other link of D is necessary because it may be that D = d₁,
   d₂, ⋯, d_n and E = e₁, e₂, ⋯, e_n have the same number of links, H(d_i) = e_i,
   P ⊂ d̄₂ + d̄₃ + ⋯ + d̄_{n−1}, and Q ⊄ ē₂ + ē₃ + ⋯ + ē_{n−1}." (wording confirmed; it differs from
   the statement's "contains a point of P not on the closure of any other link"). The commission's
   reading (true read existentially; the configuration alone does not prevent `h`, with the example
   `d₂ = c₂ ∪ ((c₁ ∪ c₃) − P)`, `h = id`) is recorded, not formalized. Not counted.

BJ.5, revisited (commission 199 §7, optional). **The general certificate is now formalized**
   (`bj_theorem5_printed_false_general`, `HPC/BJ59/Thm5Cert.lean`): from any compact space, continuous
   map to `[0, 1]` and chain of `n ≥ 3` links covering the space and meeting every fibre in every
   link, it produces a chain `E′` with `n` links satisfying the same conditions and an open `U` with
   `U ≠ ∅`, `U · (g₀ + g₁) = 0` and `Ū` in a link of `E′`, such that no fibre lies in `U` and
   `e′_n · g_{1/2} ⊆ U`; so for every expression `G − U = A + B` neither `A · g_{1/2}` nor
   `B · g_{1/2}` meets every link, and the printed conclusion fails. The remaining printed hypotheses
   (snake-like `G`, indecomposable fibres) concern `X` and `f` only and are untouched. Route: the
   commission's merge, done in place (`chainMergePenult`: `e_{n−1}` becomes `e_{n−1} ∪ e_n`, the
   other links are kept), and `U = N_δ(cl(g_{1/2} · e_n)) − cl(e₁)`. The commission's "`cl(e_n) ⊆
   e_{n−1}` can be arranged" is not needed: `cl(e_n) ⊆ e_{n−1} ∪ e_n` holds for every chain covering
   the space (`closure_last_subset`). Removing `cl(e₁)` is what makes "no fibre lies in `U`" hold
   for `n = 3`, where `e₁` meets the merged link. The hypotheses of the certificate are met with
   non-degenerate fibres by the unit square, the first projection and three horizontal strips
   (`nonvac_bj_theorem5_printed_false_general`). This settles the non-degenerate refutation that
   batch 198 gave in prose only.

`IsBJChain D ↔ IsTaut D` (commission 199 §7, optional) is proved in every metric space
(`isBJChain_iff_isTaut`, `HPC/BJ59/Taut.lean`); compactness is not needed because the links of a
chain are nonempty.

Batch 199 proposes one false printed statement (BJ.18, degenerate) and one defective proof (BJ.19)
for the count. The counts stay at twenty-three false printed statements and seventeen defective
proofs, pending the commissioner's decision.

### Bing–Jones §§4–6 (batch 200)

Source: Bing–Jones 1959 as in batch 198 (`doc/sources/bing-jones1959.pdf`, restored with the other
seven sources of commission 200 §0). The quotations of items 1–5 and 8 were checked against page
images of pp. 178, 179, 180 and 181 rendered at 200 dpi, and item 7's "4/2^i" against p. 189 at
200 dpi; the commission's quotations agree with the page images in every item checked. The quotations
of p. 182 (item 6) and p. 188 (item 7, Conditions A, B, B′ and the slip "H_i(d_k^{i+1})") are taken
from the commission and were not re-rendered in this batch; no 400-dpi crops were made.

**Convention.** From this section on, every slip is written "printed X, read Y". Earlier entries mix
the two orders (BJ.7–BJ.10 put the reading first, e.g. BJ.7 "`d_n` for `d₂`"; BJ.17 puts the printed
text first, "`of` for `if`"); they are not edited.

BJ.21. **p. 178, Theorem 8, first step.** "Let U_A, U_B be open sets with closures in d₁, d₂
   respectively such that U_A, U_B intersect each element of {p_x}." Printed `d₂`, read `d_n` (BJ.7).
   The sets are asserted without argument. **Supplied** for continuous arcs (`exists_deep_radius`,
   `exists_deep_sets`, `HPC/BJ59/Thm8Lib.lean`: an open set meeting every fibre of an open map onto
   `[0, 1]` contains a ball of fixed radius about a point of each fibre). For upper semicontinuous
   arcs, as printed, not decided. Not counted.

BJ.22. **p. 178, Theorem 8, the cover `U₁, …, U_t`.** "It follows from Theorem 4 that P is covered by
   open sets U₁, U₂, ⋯, U_t such that U_i·U_j = U_A+U_B if i≠j and if p_x·(U_i−(U_A+U_B))≠0, then
   x∈I_{a_i}." Unargued. **Supplied** (`bj_cut`, `HPC/BJ59/Thm8Lib.lean`, Theorem 4 for an open set
   over an interval with the two pieces located; the cover in `bj_theorem8_ends`,
   `HPC/BJ59/Thm8.lean`), with a uniform grid of `T` segments under a Lebesgue number of the cover
   `{I_a}` in place of a minimal subcover. Not counted.

BJ.23. **p. 178, Theorem 8, the chain `E`.** "Then the chain E whose kth link
   e_k = e(a₁)_k·U₁+e(a₂)_k·U₂+ ⋯ +e(a_t)_k·U_t is the required chain." The printed `e_k` need not
   form a chain (argued in commission 200 §4, not certified here). **Repaired** by restricting each
   piece to the fibres over its interval: `e_k = ⋃ᵢ e(a_i)_k ∩ U_i ∩ f⁻¹(I_{a_i})`
   (`bj_theorem8_ends`). A defective construction with a one-line repair; I would not count it
   (as BJ.4).

BJ.24. **p. 178, Theorem 8, the general case.** "Then alter Y as was done in the proof of Theorem 7 by
   adding elements onto the first of it and elements onto the last of it …". Unargued. **Supplied**
   by folding along the walk `r, r − 1, …, 0, …, m − 1, …, s` (`bj_theorem8_le`, with
   `isBJChain_foldChain`, `HPC/BJ59/Thm8Lib.lean`), and by reversing `D` when `s < r`
   (`bj_theorem8`). Not counted.

BJ.25. **p. 178, the corollary to Theorem 8.** The three consecutive links are not argued.
   **Supplied** (`bj_theorem8_cor`, `HPC/BJ59/Thm8Cor.lean`, by a discrete intermediate value argument,
   `walk_core`; for one-link `D(r, s)` by the uniform spread of the fibres, `exists_fibre_spread`). In
   the proof, printed "4i+1, 4i+2, 4i+3, 4i+4", read `4i−3, 4i−2, 4i−1, 4i` (numbering from 1, the
   printed blocks leave links 1–4 of `Y` without image and run past `4ℓ`). "properly covering" in
   the proof against "irreducibly covering" in the statement: not a defect (an irreducible cover is
   proper). Not counted.

BJ.26. **p. 182, Step 1(b).** "It follows from the continuity of the collection {p_x} and the
   bicompactness of an arc that there is a positive integer n such that …". Unargued. **Supplied**
   (`bj_step1b`, `HPC/BJ59/Step1b.lean`), by a neighbourhood form of the compactness argument (no
   sequences): about each point of `[0, 1]` a neighbourhood over which every point lies in a link
   meeting every fibre (`exists_nhd_step1b`), and a Lebesgue number. Bing–Jones's "irreducibly covers"
   agrees, for the connected sets `f⁻¹[a, b]`, with the skeleton's end-link reading. Not counted.

BJ.27. **pp. 188–189, the homeomorphism.** (a) "Of course, d(p, i+1)⊂d(p, i)": follows from
   Condition B (supplied, `starImage_succ_subset`, `HPC/BJ59/Zigzag.lean`). (b) The slip
   "H_iK_i(e_j^{i+1}) = H_i(d_k^{i+1})": printed `H_i(d_k^{i+1})`, read
   `H_i(K_iH_{i+1}(d_k^{i+1}))` (`d_k^{i+1}` is a link of `D_{i+1}`). (c) "ρ(p, q)<4/2^i" (p. 189,
   confirmed): the bound is `4ε_{i−1}`, i.e. `8/2^i` (BJ.14). The construction is otherwise as
   printed and is proved in the abstract form `zigzag_homeomorph` (with `zigzag_fibre` for Condition
   A); injectivity uses that the chains `E_i` are chains in Bing–Jones's sense, as Bing–Jones say.
   Not counted.

BJ.28. **pp. 179–181, Theorem 9.**
   (a) BJ.8 and BJ.9 confirmed on the page images: p. 180, printed "the links of G with closures in
   e_{n−1}·e_n", read "links of F"; printed "d₂′ is the sum of the other links of G in e₁−e₂", read
   `d₁ − d₂` (and likewise in the next two clauses, printed `e`, read `d`); the display ends
   "⊂ē_i" (closures). p. 181, printed "Let E₂ be any G_i of mesh less than 1/3 that refines E_i",
   read `E₁`; printed "H₂ be any chain map of E₂ onto E₁", read `H₁`.
   (b) **The choice of `F` on p. 179** ("Suppose that ε is a positive number so small that each subset
   of Q of diameter less than 5ε lies in one link of E. Let F be an ε-chain properly covering Q.") does
   not make `E′` a chain: links of `F` assigned to different middles can meet (commission 200 §5).
   **Repaired** in place by a finer mesh, argued through a Lebesgue number `λ` of `E` on `Q` (mesh
   `λ/5`) rather than by the commission's convergent subsequences (`bj9_Eside`,
   `HPC/BJ59/Thm9E.lean`). A defective construction repaired in place; I would not count it.
   (c) The first simplification needs private points only for the end links of `D″`, as Bing–Jones
   say: interior links have them automatically (`exists_privatePoint_interior`,
   `HPC/BJ59/Private.lean`). Our `bj9_base` takes them from the hypothesis for every link.
   (d) "If there are not already such points, points may be deleted from e₂ and e_{n−1} to make the
   condition satisfied" (p. 179): used, as `exists_privatePoint_shrink` (all links shrunk).
   (e) The printed first simplification also asks that `p₁`, `p₂` lie in different composants; the
   route used (alternating refinements, Theorem 7 of batch 199, and `zigzag_homeomorph` instead of
   Theorem 13 of Bing 1951) does not need composants. Not a defect.
   Theorem 9 is **proved** as printed (`bj_theorem9`, `HPC/BJ59/Thm9.lean`), with `D`, `E` chains in
   Bing–Jones's sense (p. 172). Not counted.

BJ.29. **Theorem 7's proof for `n = 3`** (BJ.19 (e)). The certificate is now **verified**
   (`bj_theorem7_proof_n3`, `HPC/BJ59/Private.lean`): for a connected `P` properly covered by a chain
   of three links, any `V ⊇ P·(d₂ − d₁)` and any open `U ⊆ d₃` with `U ⊇ P·(d₃ − d₂)` meeting `P`
   intersect, though the printed `D′` puts them at places two apart. Its hypotheses are met by a plane
   pseudo-arc (`nonvac_bj_theorem7_proof_n3`, `HPC/BJ59/NonVac200b.lean`). By commission 199 §0
   this makes BJ.19 countable as a defective proof.

Which items I would count: **BJ.19** (Theorem 7's proof), now that its certificate (BJ.29) is
verified, as a defective proof. Of the new items, none: BJ.23 and BJ.28 (b) are defective
constructions repaired in place (as BJ.4), the rest are unargued steps, slips or remarks. The counts
are left unchanged (twenty-four false printed statements, seventeen defective proofs), pending the
commissioner's decision.

### Bing–Jones §6, Theorem 10 (batch 201)

Source: Bing–Jones 1959 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
Every quotation below, and the quotations of commission 201 §§1–3 (Theorem 10, pp. 181–182;
Theorem 6, p. 176; Step 2(b), p. 184; Step 2(c), pp. 184–185; Conditions A, B, A′, B′, C, C′,
p. 188), was checked against crops of page images rendered at 400 dpi and viewed at full
resolution; the commission's quotations agree with the page images in every item. Convention:
"printed X, read Y".

BJ.30. **p. 187, Step 3 (3).** "The image under h⁻¹ of any subset of q₀+q_{1/k}+ ⋯ +q₁ of diameter
   less than 5ε lies in an element of E₁." Printed `E₁`, read `D₁` (`h⁻¹` maps into `P`, and `D₁` is
   the chain on `P`). Slip. Not counted.

BJ.31. **p. 184, Step 2(b).** The existence of the chain map `R_{i/n}` is argued only through the
   "precaution" ("A precaution to take to insure that each e_k is the image of three consecutive
   elements …"). Unargued step. **Supplied** (`exists_pattern`, `HPC/BJ59/Thm10Pattern.lean`), by
   the decided-position construction of commission 201 §3, with closures; shape change: the second
   clause is stated for every link (values in the run, and the closure condition for every link),
   which implies the skeleton's form (`exists_pattern_skeleton`). Not counted.

BJ.32. **pp. 184–185, Step 2(c), Theorem 6.** "… it follows from Theorem 6 that there are an f_y
   and an f_z of f_t, f_{t+1}, ⋯, f_u such that R_{(2i+1)/n}(f_y), R_{i/n}(f_y) are adjacent …".
   Theorem 6 (p. 176) needs both maps to take a link into `e_{m−1}`; Bing–Jones do not say which
   chain plays `E`. With `E₁` the hypothesis fails; with the subchain spanned by the two images it
   holds. Unargued step. **Supplied** directly (`adjacent_of_properCover`,
   `HPC/BJ59/Thm10Defs.lean`, via `exists_abs_le_one_of_steps`; no connectedness). The printed
   `R_{(2i+1)/n}` (confirmed at 400 dpi, p. 185) is BJ.11's misprint. Not counted.

BJ.33. **p. 185, Step 2(c), Theorem 5.** "By Theorem 5 there is an open set U_i in
   P(i/n, i/n+ε)·f_y such that Ū_i⊂f_y and P−U_i is the sum of two mutually exclusive closed sets
   A_i, B_i …". Theorem 5 as printed is false (BJ.5); the repaired form (batch 198) needs `U_i` to
   contain no set `f_k·p_s`, which Bing–Jones do not provide. **Supplied**: `exists_window_set`
   (the transition set, with a uniform lower bound for the spread of the links of the run over the
   fibres near the middle of the window) and `bj_theorem5_window` (the repaired Theorem 5 on the
   window `g⁻¹[a, b]`, transferred by `window_transfer`), `HPC/BJ59/Thm10Window.lean`. A gap
   caused by the false Theorem 5; I would not count it separately from BJ.5.

BJ.34. **p. 187, Step 2(i).** "Theorem 9 assures us that h can be extended in this fashion." The
   hypothesis of Theorem 9 (a link with a private point mapped onto each link) is not checked for
   `D₁`, `H₁` on `p_{i/k}`. Unargued step; **not needed** on this route (homeomorphisms on cut
   fibres are not used, BJ.37). Not counted.

BJ.35. **p. 188, Step 3, the analogue of Step 2c.** "In the analogue to Step 2c we pick ε so small
   that the Q_i, V_i, U_i we obtain will have the property that if f_j is an element of the subchain
   of F irreducibly covering q_{i/k}, then (V_i+Q_i+U_i)·f_j⊂H₁R_{i/k}(f_j)." Unargued; the reason
   given, `q_{i/k}·f_j ⊂ H₁R_{i/k}(f_j)`, gives the conclusion only with closures,
   `q_{i/k}·f̄_j ⊂ H₁R_{i/k}(f_j)`, and a compactness argument. **Supplied** with closures
   (`exists_tau_incl`, `HPC/BJ59/Thm10Pieces.lean`; the closure clause of `exists_pattern`). Not
   counted.

BJ.36. **p. 188, Steps 4, 5, ⋯** (BJ.13). "These steps are essentially repetitions of Step 3." The
   induction is left to the reader. **Supplied**: one step for both sides (`BJStep`, `bj_step`,
   `HPC/BJ59/Thm10Step.lean`, with the gluing `bj_glue`, `HPC/BJ59/Thm10Glue.lean`) and the
   alternation (`bjThm10_of_step`, `HPC/BJ59/Thm10Induct.lean`). Not counted.

BJ.37. **Route.** The homeomorphisms on cut fibres (Step 1(c), Step 2(i)) are not needed: the step
   passes from the map of one sub-arc to the map of the next through overlapping sub-arcs and a
   window, and uses `h` only on `p₀`, `p₁`. Theorem 9 is not used in Theorem 10. Not a defect.

BJ.38. **pp. 182–188, "the subchain … that irreducibly covers".** A minimal covering run of a set is
   unique when it has two links or more; two different ones occur only when the set lies in two
   adjacent links, each covering it alone. Any one serves (the library takes a minimal run,
   `exists_minimal_run`, `HPC/BJ59/Thm10Runs.lean`). Harmless.

BJ.39. **p. 187, Step 3.** "It takes the subchain f_t, f_{i+1}, ⋯, f_u of F that irreducibly covers
   Q(i/k, (i+1)/k) …" (confirmed at 400 dpi). Printed `f_{i+1}`, read `f_{t+1}`. Slip. Not
   counted.

BJ.40. **p. 187, Step 3, condition (1).** "(1) f_j⊂H₁R_{(2i+1)/2k}(f_j)" asks for the whole link
   `f_j`, while the corollary to Theorem 8, read with `Q(i/k, (i+1)/k)` as the space, controls only
   `f_j·Q(i/k, (i+1)/k)`. The construction needs only that part: (R1) of commission 201 §4,
   `bj_theorem8_cor_sub` (`HPC/BJ59/Thm10Sub.lean`), whose second clause is
   `F.link k ∩ g⁻¹[a, b] ⊆ E.link (H₁ (R k))`. An overstatement; not counted.

No other defect of Steps 2(d)–(h) was met beyond those above: the rest of the construction (regions,
the choice of `μ`, the definition of `K`, the verification of A′, B′, C′ and of `K` onto) goes
through as commission 201 §4 (f)–(g) describes, with the window dichotomy of the repaired
Theorem 5 in Step 2(h).

Which items I would count: none. BJ.33 is a consequence of the false Theorem 5 (BJ.5, already
counted); the others are unargued steps, slips or overstatements, all supplied. **Theorem 10 is
proved** in the fibre-preserving form `BJThm10` (`bjThm10`, `HPC/BJ59/BJ59D.lean`). The counts are
left unchanged (twenty-four false printed statements, eighteen defective proofs), pending the
commissioner's decision.

### Bing–Jones §7, the plane example (batch 202)

Commission 202 §7. Every quotation below (pp. 189–191) was checked against page images rendered
at 200 dpi, and condition (9) and the labels of the figure on p. 191 against crops rendered at
400 dpi and viewed at full resolution; the commission's quotations agree with the page images.
Convention: "printed X, read Y".

BJ.41. **P. 190, the chains D_i.** "Now there exists a sequence D₁, D₂, D₃, ⋯ of circular chains
   of simple domains in the plane such that" (1)–(9). The chains are not constructed. **Not
   established** from Bing–Jones's text. The example is obtained here by another construction,
   not Bing–Jones's (commission 202 §§3–6): a circular description in the plane (`planeDescr`,
   `HPC/BJ59/CircPlane.lean`; `exists_circDescr_plane`, `HPC/BJ59/BJ59E.lean`), recognized as a
   circle of pseudo-arcs by `CircDescr.isCircleOfPA` (`HPC/BJ59/CircMap.lean`). Not counted.

BJ.42. **P. 191, M without (9).** "Also, in this case M would be a continuous circle-like circle
   of continua." "In this case" is the case with (9) omitted; the same claim for the chains with
   (9) is implicit in the next two sentences ("With the addition of (9) … each element of G is a
   pseudo-arc. It follows from Theorem 10 that M is homogeneous."). That the elements of `G` are
   disjoint, fill `M`, and form a continuous decomposition with a circle as quotient is argued in
   neither case. Unargued step. In the construction of this batch the corresponding facts are
   proved for a circular description (the fibres of the map onto the circle are the intersections
   of the runs, `CircDescr.fib`, `HPC/BJ59/CircDescr.lean`; continuity and openness of the map,
   `HPC/BJ59/CircMap.lean`). Not counted.

BJ.43. **P. 191, the elements of G are pseudo-arcs.** "With the addition of (9) one may see with
   the help of [3] that each element of G is a pseudo-arc." Unargued. (9) reads (400 dpi): "if h<i
   and T_ij is a refinement of T_hk+T_hl, T_ij is crooked [3] with respect to T_hk+T_hl where
   l=(k+1) mod n(h)." The subscripts are as quoted. I agree with the commission: (9) controls one
   new column inside a pair of consecutive old columns, and an element of `G` covered at some level
   by two adjacent columns `T_ij + T_{i,j+1}` needs the run of the two new columns to be crooked in
   the old columns it refines. Crookedness of each new column gives, for a pair `h`, `k` of old
   links, the return `k − 1`, `h + 1` only when both lie in the old pair refined by that column;
   for `h` in the range of the first column only and `k` in the range of the second only, neither
   column provides it, and two crooked chains joined end to end are not crooked in general. No
   certificate (two explicit chains) is given in this batch. The construction of this batch
   replaces (9) by the crookedness of every run of the new chain over at most two window changes
   (the sweep lemma, `sweep_lemma`, `HPC/BJ59/Sweep.lean`; `sweepX_crook`,
   `HPC/BJ59/SweepPattern.lean`). An unargued step whose stated hypothesis does not visibly
   suffice. I would count it (see below).

BJ.44. **P. 190, the arc collection.** "It is easy to see that G is an upper-semicontinuous
   collection of arcs, G is a circle (if its elements are thought of as points) and G* (the sum of
   the elements of G) is a circle-like continuum." This is about the collection built from the arcs
   `V_i` (the analogue announced on p. 189: "But we first describe an analogous
   upper-semicontinuous collection G of arcs in the plane"), and is not used afterwards. Unargued;
   harmless. Not counted.

BJ.45. **Route.** The construction of this batch uses no part of §7 except its claim, that the
   plane contains a circle of pseudo-arcs (`bjPlaneExample : BJPlaneExample`,
   `HPC/BJ59/BJ59E.lean`). Not a defect.

BJ.46. **P. 191, the figure.** The labels of the figure are `T_jk` (the old column) and
   `T_{r k+1}`, `T_{r+2 k+1}`, `T_{r+3 k+1}` (new columns), with the level written second, while the
   text writes the level first (`T_ij`, column `j` of `D_i`, (7)–(9)). Printed `T_{r k+1}`, read
   `T_{k+1, r}` (and similarly for the others). The end points are labelled `a₁`, `c₁` next to
   `b_i`: printed `a₁`, `c₁`, read `a_i`, `c_i` (400 dpi). Slips. Not counted.

BJ.47. **Pp. 190–191, the letter G.** `G` denotes the upper-semicontinuous collection of arcs on
   p. 190 (BJ.44) and the set of subcontinua of `M` irreducible from `W₁` to `W₂` on p. 191. A reuse
   of notation; harmless. Not counted.

Which items I would count: BJ.43, as a defective proof (the one step of §7 that carries the
pseudo-arc property rests on a condition that, as far as can be seen, does not give it); BJ.41 and
BJ.42 are omissions of a construction that the paper does not claim to give in detail, and I would
not count them. I count nothing myself; the counts are left unchanged (twenty-four false printed
statements, eighteen defective proofs), pending the commissioner's decision.
