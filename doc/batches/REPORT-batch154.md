Commission read: `doc/batches/COMMISSION-batch154.md` (batch 154 — Part F, Jones 1949 VI: Theorems 1 and 2; Jones 1955 Theorem 2 unconditional).

# Report, batch 154

**Status: all items A–F proved; nothing open.** `jones49_theorem1 : Jones49Thm1` is proved, so the
hypothesis `h49` of batch 148 is discharged, and Jones 1955 Theorem 2 and its closing remarks hold
without it. `lake build HPC` succeeds with `import HPC.Jones.Jones49F` added at the end of
`HPC.lean`. The new files contain no `sorry`. Every new theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.

**Files.**

| file | content |
|---|---|
| `HPC/Jones/Jones49F.lean` | the skeleton items A–F, and `not_jones49_theorem2_point` |
| `HPC/Jones/Jones49FTheta.lean` | plane lemmas: `mem_cc_of_not_mem_domain`, `theta_no_common_side`, `theta_separation_core`, `theta_separation` (item C, step 5) |
| `HPC/Jones/Jones49FLocal.lean` | local separating points: `isLocalSepPoint_of_open_sub_tscc`, `isLocalSepPoint_of_separation`; `tscc_of_homeomorph_circle` |
| `HPC/Jones/Jones49FCase1.lean` | item B: `frontier_cc_of_jordan`, `exists_frontier_through`, `countable_complDomains`, `jones49_case1_core` |
| `HPC/Jones/Jones49FCase2.lean` | item C: `TArc.first_point_split`, `exists_domain_meeting`, `exists_theta_arcs`, `jones49_case2_core` |

**Statements.** All eleven skeleton statements are verbatim: a diff against
`doc/batches/skeletons/Jones49F.lean` shows only the module docstring, the import line, the proofs,
and `:= by sorry` becoming term proofs for item F. There are no shape changes. One theorem is added,
`not_jones49_theorem2_point` (item E's degenerate case).

**Housekeeping.**
* The uploads are moved off the root: the commission is now `doc/batches/COMMISSION-batch154.md`
  and the skeleton is `doc/batches/skeletons/Jones49F.lean`.
* `Axioms.lean` has the new group "Jones 1949 Theorems 1–2; Jones 1955 Theorem 2 unconditional
  (batch 154)".
* `axioms.txt` is regenerated, with `sorryAx` in no line. The previous version is kept in
  `doc/batches/audits/axioms-before-batch154.txt`.
* The per-theorem audit is `doc/batches/audits/axioms-batch154.txt`.
* `README.md` and `LEDGER.md` §6 are updated. `OPEN.md` is unchanged, since nothing is left open.

## 1. The items

**A. `jones49_setting`, `jones49_simple_domains` — proved, statements verbatim.**
* Cyclic: a nondegenerate continuum has a non-cut point (`exists_two_nonCutPoints`), and a
  homeomorphism of `M` carries it to any point `z`, so `{z}ᶜ` is the image of a connected set.
* Semi-locally connected: `semiLocConn_of_isAposyndetic` (Jones 1941 Theorem 4).
* `jones49_simple_domains` is `whyburn39_corollary1` with these two facts.

**B. `jones49_case1` — proved, statement verbatim**, following the commission's steps
(`jones49_case1_core`; homogeneity, cyclicity, semi-local connectedness and `hno` are used).
1. *Images of `J`.* `h : M ≃ₜ M` carries a point of `J` to `p`. Then `J' = h(J)` is a simple closed
   curve (`tscc_image_embedding`), and `M ⊆ h(M − J) ∪ J'` with `h(M − J)` connected and disjoint
   from `J'`.
2. *Boundary of an element of `G`* (`frontier_cc_of_jordan`). By `jordan_side`, `h(M − J)` lies on
   one side `S` of `J'`. The other side `T` misses `M`, is connected and has frontier `J' ⊆ M`, so
   `T` is the component of `Mᶜ` through any of its points (`cc_sub_of_frontier`). Its boundary is
   `J' ∋ p` (`exists_frontier_through`).
3. *`G` countable* (`countable_complDomains`): `Set.PairwiseDisjoint.countable_of_isOpen`.
4. *Baire.* `M` is the union of the closed sets `M ∩ ∂U`, `U ∈ G`. Since `M` is compact Hausdorff,
   `nonempty_interior_of_iUnion_of_closed` gives `U` such that `∂U` contains a nonempty open set `W`
   of `M`. `∂U` is a simple closed curve (`whyburn39_corollary1`).
5. *Order 2.* A point `p ∈ W` is a local separating point of `M`
   (`isLocalSepPoint_of_open_sub_tscc`): split `∂U` at `p` and another point `q` into arcs `L₁`,
   `L₂`. Then `p` separates the open set `W − q` into the parts off `L₂` and off `L₁`, and small
   sub-arcs of `L₁`, `L₂` at `p` (`TArc.shrink`) lie in its component through `p`. So some point has
   order 2 (`jones49_some_order_two`, with `M` uncountable), against `hno`. *Recorded:* this
   replaces Jones's "each point of `Jᵢ` is a limit point of `M − Jᵢ`"; see ledger check 2.

**C. `jones49_case2` — proved, statement verbatim** (`jones49_case2_core`). Only cyclicity and
semi-local connectedness are used, through `jones49_setting`; homogeneity is not used.
0. *`M = J`.* Every point is a local separating point (`isLocalSepPoint_of_open_sub_tscc` with
   `W = M`). This subcase is included in "`M − J` not connected", since `M − J` is then empty.
1. *The arc `T`.* `M − J ⊆ u ∪ v`, cut by open sets with `(M − J) ∩ u ∩ v = ∅`; `H`, `K` are the
   traces. The side `E` of `J` containing `M − J` is connected and open; it is the complement of
   `D̄` (`mem_cc_of_not_mem_domain`). `exists_tarc_of_isOpen_plane` gives an arc in `E` from `H` to
   `K`. Trimming it at its last point `x` on `H̄` and then at the next point `y` on `K̄`
   (`TArc.first_point`, twice) gives `T`, with interior missing `M` (`exists_domain_meeting`).
2. *The element `U`:* the component of `Mᶜ` containing `T − {x, y}`, with `x ∈ H`, `y ∈ K` on its
   boundary `C`. `C` is a simple closed curve (`whyburn39_corollary1`), and `U ≠ D` because
   `x ∉ J`.
3. *`C ∩ J ≠ ∅`:* each arc of `C` from `x` to `y` meets `J`, since otherwise it would be a
   connected subset of `M − J` meeting both `u` and `v`.
4. *The arc `AxB`* (`exists_theta_arcs`). `C` is split at `x`, `y` into `P₁`, `P₂`
   (`tscc_split`). The first points `A ∈ P₁`, `B ∈ P₂` of `J` from `x` (`TArc.first_point_split`)
   give arcs `L = AxB` and `L'` from `A` to `B`, with `L ∪ L' = C`, `L ∩ L' = {A, B}`,
   `L ∩ J = {A, B}` and `A ≠ B`.
5. *`M − (A + B)` not connected* (`theta_separation`; see the next paragraph).
6. *`M − B` connected:* cyclicity.
7. *`A` a local separating point* (`isLocalSepPoint_of_separation`): `A` separates the open set
   `M − B`, whose component through `A` is `M − B`, into the parts off `closure X₂` and off
   `closure X₁`.

**About step 5 (§2 C of the commission).** The commission's start is correct, and the difficulty it
points to is real: `AxB°` lies in the closure of both `E₁` and `E₂`. Here is the argument as
formalized.
* *The no-common-side lemma* (`theta_no_common_side`). For a θ-curve `K₁ + K₂ + K₃`, no point off
  it lies, for each `i`, in the component of `(Kⱼ + Kₖ)ᶜ` containing `Kᵢ°`.
  * Proof: take `w` on the other side of `K₁ + K₂`. That side misses `K₃` and has `K₁`, `K₂` in its
    closure, so `w` is on the `K₁°`-side of `K₂ + K₃` and on the `K₂°`-side of `K₁ + K₃`, as `m` is.
  * Janiszewski's theorem (`janiszewski_compact`, for `K₁ + K₃` and `K₂ + K₃`, whose common part
    `K₃` is connected) then puts `m` and `w` in one component of the complement of the θ-curve.
  * That component lies in one side of `K₁ + K₂`, which is a contradiction.
* *Sides.* Let `E₁` be the side of `J₁ + AxB` away from `J₂°`, and `E₂` the side of `J₂ + AxB`
  away from `J₁°`.
  * `E₁` and `E₂` are disjoint: `E₁` misses `J₂ + AxB` and has `J₁°` in its closure.
  * Every point of `M` off the θ-curve lies in `E₁ ∪ E₂`. It is not in `D`, so it is on the
    `AxB°`-side of `J` (`mem_cc_of_not_mem_domain`); now apply the lemma.
  * By the same argument `U ⊆ E₁ ∪ E₂`, and `U` lies in one of them since it is connected. Say
    `U ⊆ E₁`; the other case is symmetric (`theta_separation` calls `theta_separation_core` with
    `J₁`, `J₂` exchanged).
* *The key step.* `L' ⊆ C ⊆ Ū ⊆ Ē₁`, so `L'` meets `J₂` only in `A`, `B`, and `L' + AxB + J₂` is a
  θ-curve. Let `m ∈ M ∩ E₁` with `m ∉ L'`. Then:
  * `m ∉ U`, so `m` is on the `J₂°`-side of `C = L' + AxB`;
  * `m ∉ E₂`, so `m` is on the `L'°`-side of `J₂ + AxB`;
  * so by the lemma `m` is not in the component `S'` of `(L' + J₂)ᶜ` containing `AxB°`.

  `S'` is open, so `closure (M ∩ E₁) ⊆ S'ᶜ ∪ L'`, which misses `AxB°`.
* *The separation:* `X₁ = M · (E₁ + J₁°)` and `X₂ = M · (E₂ + J₂° + AxB°)`. Their union is
  `M − {A, B}`, both are nonempty (they contain `J₁°` and `J₂°`), and
  `closure X₁ ∩ X₂ = X₁ ∩ closure X₂ = ∅`.
* *Hypotheses used:* `M ∩ D = ∅`, `J + AxB ⊆ M`, and that `U` is a complementary domain other than
  `D` whose boundary is a simple closed curve containing `AxB`. Homogeneity and the absence of
  points of order 2 are not needed. Semi-local connectedness and cyclicity enter only through
  Whyburn's Corollary 1, which makes `C` a simple closed curve. The two-sidedness `H`, `K` enters
  only in step 4, to make `A ≠ B`. The step is therefore **true as Jones states it**.

**D. `jones49_theorem1` — proved, statement verbatim.**
* If some point has order 2, `jones49_order_two` applies.
* Otherwise there is `x ∉ M` (`noncompact_univ`). Let `J` be the boundary of the complementary
  domain of `x`.
  * If `M − J` is connected, Case 1 gives a contradiction.
  * Otherwise Case 2 gives a local separating point, and `jones49_some_order_two` gives a point of
    order 2 (`M` is uncountable by `uncountable_of_nontrivial`), which is again a contradiction.

**E. `jones49_theorem2` — proved, statement verbatim.**
* `theorem18` (Jones 1948) gives a dense, hence nonempty, set of points at which `M` is aposyndetic.
* For `x ≠ y`, take `h` with `h x₀ = x`. Aposyndesis at `x₀` with respect to `h⁻¹ y` transfers to
  `x` with respect to `y` (`aposAt_homeomorph_iff`), so `M` is aposyndetic and Theorem 1 applies.
* *Degenerate case:* `not_jones49_theorem2_point`. `{0}` is compact, connected and homogeneous, and
  has no weak cut point (`CutsPts` needs `x ≠ y`), but it is not a circle. So the printed Theorem 2
  fails for a one-point continuum, exactly as Theorem 1 does.

**F. The unconditional Jones 1955 results — proved, statements verbatim.** `jones55_theorem2'`,
`jones55_two_domains'`, `jones55_elements_indecomposable'` and `jones55_three_domains'` are
`jones55_theorem2`, `jones55_two_domains`, `jones55_elements_indecomposable` and
`jones55_three_domains` applied to `jones49_theorem1`.

## 2. Ledger entries (`LEDGER.md` §6, "Jones 1949 VI")

1. **Case 1, "Consequently each point of `M` belongs to the boundary of an element of `G`"**:
   unargued. It is supplied by the Jordan curve theorem (`frontier_cc_of_jordan`). True.
2. **Case 1, "Since no point of `M` is of order 2 in `M`, each point of `Jᵢ` is a limit point of
   `M − Jᵢ`"**: unargued, and true. In the formal proof it is replaced by a different argument with
   the same conclusion: a point of `Jᵢ` interior in `M` is a local separating point, so some point
   has order 2 by Whyburn (9.2).
3. **Case 2.** All four sentences are unargued and true, and each is supplied:
   * the arc `T` and the element `U`;
   * the arc `AxB`, which needs `C ∩ J ≠ ∅`, obtained from the separation of `H` and `K`;
   * **"`M − (A + B)` is not connected"**, which needs a real argument (θ-curves, Janiszewski) and
     no extra hypothesis;
   * the local separating point.

   The degenerate subcase `M = J` is harmless.
4. **"all except countably many of the local separating points … must be of order 2"** needs `M`
   uncountable. This is unstated, but nondegeneracy supplies it.
5. **Theorem 2, "Being aposyndetic at one point, `M` must be aposyndetic at each of its points"**:
   tacit use of homogeneity. True.
6. **Degenerate cases:** a one-point continuum refutes both printed Theorems 1 and 2. Both are
   proved for nondegenerate `M`.

No step is false. No defective proof is added; the count stays at fourteen.

## 3. Axioms per theorem

All 35 theorems of the new files depend on exactly `[propext, Classical.choice, Quot.sound]`. The
full list is in `doc/batches/audits/axioms-batch154.txt`. The deliverables:

| theorem | axioms |
|---|---|
| `jones49_setting` | propext, Classical.choice, Quot.sound |
| `jones49_simple_domains` | propext, Classical.choice, Quot.sound |
| `jones49_case1` | propext, Classical.choice, Quot.sound |
| `jones49_case2` | propext, Classical.choice, Quot.sound |
| `jones49_theorem1` | propext, Classical.choice, Quot.sound |
| `jones49_theorem2` | propext, Classical.choice, Quot.sound |
| `not_jones49_theorem2_point` | propext, Classical.choice, Quot.sound |
| `jones55_theorem2'` | propext, Classical.choice, Quot.sound |
| `jones55_two_domains'` | propext, Classical.choice, Quot.sound |
| `jones55_elements_indecomposable'` | propext, Classical.choice, Quot.sound |
| `jones55_three_domains'` | propext, Classical.choice, Quot.sound |

## 4. Closing inventory: Parts D–F (Jones 1955 Theorem 2 through all its dependencies)

**Method.** The constants used by the proofs of `jones55_theorem2'`, `jones55_two_domains'`,
`jones55_elements_indecomposable'`, `jones55_three_domains'` and `jones49_theorem2` were traversed
transitively. The result was intersected with the main list of `Axioms.lean`. That gives 461 audited
results, each with its group and file, listed in `doc/batches/audits/inventory-batch154.txt`. The
table below lists the source results among them, by source. Each status is the one recorded in
`LEDGER.md` and in the docstring at the statement:
* **verified**: the printed statement, possibly with Moore's axioms made explicit or an unused
  hypothesis dropped (both are generalizations);
* **verified with corrected hypotheses**;
* **replaced by a different argument**: the statement is verified, but the printed proof is not
  followed at the step named.

The remaining entries of the inventory are infrastructure, not source results: polygonal plane
topology (batches 118–133), chains, the arc and order machinery, and so on.

| source | results used (file: theorem) | status |
|---|---|---|
| Bing 1948 (arcs paper) | `Plane/Arcs48.lean`: `arcs_theorem5_point`, `arcs_corollary2` | verified |
| Nadler 6.6 | `Plane/NonCut51Gen.lean`: `exists_two_nonCutPoints` | verified |
| Jordan curve theorem and Janiszewski for polygons | `Plane/Jct1.lean`: `polygon_separates`; `Plane/Jct2.lean`: `jct_polygon`; `Plane/Cyc1.lean`, `Plane/Cyc2.lean`: `janiszewskiPoly_of_oddCycle`, `janiszewskiPoly_holds`; `Plane/JanPoly.lean`: `janiszewski_polygonal` | verified |
| van Mill 2004 (Effros) | `Effros/OpenMapping.lean`: `exists_vanMill_basis`, `vanMill_3_1`–`vanMill_3_5`, `effros_open_mapping`; `Effros/Effros.lean`: `effros_homogeneous` | verified (closure bars of Lemma 3 as printed, recorded at the statements) |
| Jones 1948 | `Jones/Basic.lean`: `theorem0`, `theorem3`, `theorem4`, `theorem5`, `theorem8`, `theorem9`; `Jones/Theorem6.lean`: `theorem6`; `Jones/CutPoints.lean`: `theorem11`, `theorem12`, `theorem15`, `theorem18`; `Jones/Theorem13.lean`: `theorem13` | verified; in Theorem 13 Jones's finite families are replaced by a uniform radius (`exists_radius_uniform_apos`) |
| Jones 1948, Theorem 10 | `Jones/Basic.lean`: `theorem10` | verified with corrected hypotheses (`D` nonempty; printed form refuted, `not_theorem10_printed_unitInterval`) |
| Jones 1951, the Lemma | `Jones/Jones51.lean`: `jones51_lemma` | verified; the transfinite construction is replaced by the minimum of a lower semicontinuous function (`exists_lsc_strictMono_aposSet`) |
| Jones 1941 Thm 4; Whyburn 1939 (6.2) | `Jones/Whyburn.lean`: `semiLocConn_of_isAposyndetic`, `isAposyndetic_of_semiLocConn`, `whyburn_6_2` | verified |
| Jones 1955, §1 and Theorem 1 | `Jones/Jones55.lean`: `jones55_a`, `jones55_b`, `jones55_c`, `jones55_usc`, `jones55_continuous`, `jones55_elements`; `Jones/Jones55Core.lean`: `jones55_prop_e` | verified; three steps replaced, as recorded in the batch-136 ledger: the upper semicontinuity argument (by closedness of the relation, `isClosed_lSetoid`, used by `jones55_usc`), claim (12) (from (c) and (3)), and one case argument (check 6 there) |
| Moore 1916 (F.A.) §§2–5 | `Moore/Basic.lean`: `fa_theorem2`, `fa_theorem3`, `fa_theorem6`; `Moore/Sec4.lean`: `fa_theorem12`, `fa_theorem13`, `fa_theorem17`; `Moore/Thm15.lean`: `exists_irreducible`, `fa_theorem16`; `Moore/Arcs.lean`: `fa_sec5_arc_split`, `fa_scc_two_arcs` | verified |
| Moore 1916 (F.A.), Theorems 4, 19 | `Moore/Basic.lean`: `fa_theorem4`; `Moore/Sec4.lean`: `fa_theorem19` | verified with corrected hypotheses (`R` nonempty) |
| Moore 1916 (F.A.) §6 | `Moore/Sec6A.lean`: `fa_theorem20`, `fa_theorem21`; `Moore/Sec6B.lean`: `fa_theorem24`, `fa_theorem25`, `fa_theorem27`; `Moore/Sec6Th28.lean`: `fa_theorem28`; `Moore/Sec6Lim.lean`: `tarc_of_seq`, `exists_tarc_of_seq`; `Moore/Sec6Th32.lean`: `accessible`; `Moore/Sec6Th33.lean`: `fa_theorem33`, `fa_theorem34_region` | verified |
| Moore 1916 (F.A.) §7, Theorems 35, 36, 41, 42 | `Moore/Sec7A.lean`: `jordan`, `fa_theorem35`; `Moore/Sec7B.lean`: `fa_theorem36`; `Moore/Sec7Th41.lean`, `Moore/M41.lean`: `fa_theorem41`, `fa_theorem41_caseI`, `fa_theorem41_caseII`; `Moore/Sec7Th42.lean`, `Moore/M41.lean`: `fa_theorem42`, `fa_theorem42_of_41` | Theorem 35: verified with corrected hypotheses (`R` nonempty), proof replaced; Theorem 36: verified, one step of the proof corrected; Theorems 41, 42: verified |
| Moore 1919, Theorems A, D, E, F, G | `Moore/M19A.lean`: `m19_theoremA`; `Moore/M19DThm.lean`, `Moore/M19CD2.lean`, `Moore/M19CDRegion.lean`: `m19_theoremD`, `m19_theoremD_regions`, `m19_theoremD_regions_of_curves`; `Moore/M19ESchoenflies.lean`: `m19_schoenflies_proof`; `Moore/M19F.lean`: `m19_theoremF_proof`; `Moore/M19GBoundary.lean`, `Moore/M19GPlane.lean`, `Moore/M19G.lean`: `m19_schoenflies_param`, `m19_schoenflies_boundary_proof`, `m19_plane_proof`, `m19_plane` | verified; three unargued or failing steps replaced: in Theorem D the curve `J̄` is not used (batch 142), in Theorem E step 4 the limit arcs are not built one at a time (batch 143), and in Theorem G the nine-cell ruling of Fig. 3 is replaced by two cuts of the annulus (batch 144) |
| Moore 1925 §I, Theorems 1–4 | `Moore/M25Plane.lean`: `plane_unicoherent`, `brouwer_boundary`, `janiszewski_compact`; `Moore/M25Quot.lean`: `quot_brouwer`; `Moore/M25Thm.lean`: `m25_theorem4`, `m25_unbounded_unique`; `Moore/M25Thm2.lean`: `m25_theorem2`; `Moore/M25Ax.lean`: `m25_axiom1`, `m25_axiom2`, `m25_axiom4`, `m25_axiom5`; `Moore/M25FA.lean`: `m25_fa_theorem15` | verified |
| Moore 1925 §I, Theorems 5–12; Mullikin 1922; Moore 1920 | `Moore/CutArc.lean`: `circle_char`; `Moore/Borsuk.lean`: `borsuk_exists_log`; `Moore/M25B5.lean`: `m25_theorem6`; `Moore/M25B9.lean`: `m25_theorem9`, `m25_theorem10`, `m25_theorem12`; `Moore/M25B11.lean`: `m25_theorem11`; `Moore/Mullikin.lean`: `mullikin_theorem5` | Mullikin Theorem 5: verified with corrected hypotheses (`K₁`, `K₂` closed); Theorems 10, 11: verified with Moore 1920's definition of a simple closed curve corrected (`IsSCCElt`); the others verified |
| Moore 1925 §I, Theorems 13–22 | `Moore/M25C13.lean`: `quot_janiszewski`, `m25_theorem13`, `m25_theorem14`; `Moore/M25C15.lean`: `m25_theorem15`, `m25_theorem18`; `Moore/M25C19.lean`: `m25_theorem19`; `Moore/M25C20.lean`: `m25_theorem20`; `Moore/M25C.lean`: `m25_theorem21`, `m25_theorem22` | verified (Theorem 21 by a recorded route to Axioms 6 and 7) |
| Jones 1955 Theorem 2 and remarks | `Jones/Jones55T2A.lean`: `jordan_curve_theorem`; `Jones/Jones55T2D.lean`: `jones55_compl_connected`, `jones55_elt_not_separates`, `jones55_plane`, `jones55_embedding`; `Jones/Jones55T2.lean`: `jones55_circle`, `jones55_theorem2`, `jones55_two_domains`, `jones55_elements_indecomposable`, `jones55_three_domains`; `Jones/Jones49F.lean`: the four primed forms | verified; `jones55_elements_indecomposable` by the commission's route, not Jones 1951 (not in the repository) |
| Menger, *Kurventheorie* | `Jones/Jones49Menger.lean`: `menger_order_two`, `jones49_order_two` | verified |
| Whyburn, *Analytic Topology* (3.2), (9.1), (9.2) | `Jones/Jones49Why.lean`: `whyburn_9_1`; `Jones/Jones49B.lean`: `whyburn_3_2`, `whyburn_9_2`, `jones49_some_order_two`; `Jones/Jones49A.lean`: `jones49_some_order_two_of_whyburn_9_2` | verified; (3.2) by a recorded route (separating points of `univ`) |
| Moore 1922; complementary domains | `Jones/Jones49CAnn.lean`: `Sector.sector_cyclic`; `Jones/Jones49C.lean`: `whyburn39_6_22_sec14` | verified |
| Whyburn 1939, Theorem 14 | `Jones/Jones49D.lean`: `whyburn39_local_noncut`, `whyburn39_curve_from_order_two`, `whyburn39_theorem14` | Theorem 14 verified, by a different argument at the inversion step (refuted as printed) and at the curve `K` (replaced by `whyburn39_curve_from_order_two`) |
| Whyburn 1939, Corollary 1 | `Jones/Jones49E.lean`: `frontier_cyclic`, `theta_of_cyclic_peano`, `whyburn39_corollary1`; `Jones/Jones49EPlane.lean`: `theta_not_subset_closure`; `Jones/Jones49ETheta.lean`: `exists_theta_of_cyclic` | verified; stated without proof in the source; `frontier_cyclic` by a different route (Janiszewski) |
| Jones 1949, Theorems 1 and 2 | `Jones/Jones49F.lean`: `jones49_setting`, `jones49_case1`, `jones49_case2`, `jones49_theorem1`, `jones49_theorem2` | verified with corrected hypotheses (nondegenerate; printed forms refuted for a point); Case 1's limit-point step replaced by a different argument |

**Non-standard axioms and hypotheses remaining: none.**
* Every result in the inventory depends on axioms within `[propext, Classical.choice, Quot.sound]`.
* `jones55_theorem2'`, `jones55_two_domains'`, `jones55_elements_indecomposable'` and
  `jones55_three_domains'` carry only the printed hypotheses (`M` a compact connected plane set,
  homogeneous, and decomposable where Jones says so). No `h49` remains.
* `Jones49Thm1` is now a theorem.
