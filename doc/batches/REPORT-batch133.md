Commission read: `doc/batches/COMMISSION-batch133.md` (batch 133 — tree-like continua do not contain separating continua; Bing 1951 (Duke), Theorem 7 as printed; the definition of tree-like repaired).

# Report, batch 133

`lake build HPC` succeeds. Nothing in `HPC/Plane/TreeLikeNS.lean` or in its two helper files
(`TreeLikeNSGraph.lean`, `TreeLikeNSLog.lean`) is `sorry`. The regenerated `axioms.txt` has
`sorryAx` in no line (692 lines, 17 of them new). The per-batch audit is
`doc/batches/audits/axioms-batch133.{lean,txt}`: all 37 entries (every theorem of the three new
files, plus the re-proved `theorem6_1951_rel` and `theorem6_1951`) show exactly
`[propext, Classical.choice, Quot.sound]`. The previous
`axioms.txt` is saved as `doc/batches/audits/axioms-before-batch133.txt`.

Nothing was refuted. None of the four refutation candidates fails (details under the items).

## 0. Batch 132

The `fugate_cor1` docstring now says that (∗) "rests on Ingram's Lemmas 1–2 and the direct route
(`Ingram68Core`, `Ingram68Star`)". That is the only edit to `Ingram68.lean`.

## 1. The definition (§1 of the commission)

* `Tree67.lean`: `IsTreeLike` now asks `Bornology.IsBounded A ∧ diam A < ε` of each link. The
  docstring records the old form and this batch's finding.
* `IsTreeLikeOld` (old definition, verbatim) and `isTreeLikeOld_of_isContinuum`: **proved**. The
  witness is `G = {univ}`. `isTreeChain_univ` shows `{univ}` is a tree chain: coherence and the
  triple clause hold vacuously, and a circular chain has more than two links, so it cannot be a
  subcollection of a singleton. `diam univ = 0` because `univ` is unbounded.
* **Theorem 6 re-checked.** `theorem6_1951_rel` (`Tree7Comp.lean`) needed a three-line change:
  the links come from `theorem7_1951_rel` and are polygon interiors, so they are bounded by
  `PlaneFacts.polyInterior_eq`. The statement is unchanged. `theorem6_1951` (`Enc2.lean`) is
  unchanged and builds as it is.

### Result of the `IsTreeLike` / `IsTreeChain` grep

* `IsTreeLike` is used in `Tree67.lean` (the definition), in the conclusions of
  `theorem6_1951_rel` (`Tree7Comp.lean`) and `theorem6_1951` (`Enc2.lean`), in the comment on
  `treeLike_nonseparating` (`Tree7.lean`), and in `TreeLikeNS.lean`. Nothing in `HPC/Archive`,
  `HPC/Census` or the census/archive roots uses it.
* `IsTreeChain` is unchanged. It appears in `Tree67.lean`, `Tree7.lean` (`treeChain_of_cover`),
  `Tree7Comp.lean` (`theorem7_1951_rel`, `theorem7_weak_rel`) and `Enc2.lean`
  (`theorem7_1951`, `theorem7_weak`). None of these changes meaning.
* So the only statement whose meaning changed is `theorem6_1951`'s conclusion (and that of its
  relative form). Before this batch it was vacuous; now it says something.

## 2. Items (`TreeLikeNS.lean`)

### 2.1 The definition — proved (§1 above).

### 2.2 A logarithm on a fine tree cover — all proved

* `toCpx`, `continuous_toCpx`: **proved**. *Shape change:* both are moved to
  `TreeLikeNSLog.lean`, with the same names in the same namespace, so the helper lemmas can use
  them.
* `exists_log_on_ball`: **proved as stated**, with the constant `4`. The branch is
  `log ((z − p) / (c − p)) + log (c − p)`. In the sup metric, `‖toCpx z − toCpx c‖ ≤ 2 dist z c`
  and `dist c p ≤ ‖toCpx c − toCpx p‖`. So `|(z − c)/(c − p)| < 2r / 4r = 1/2`, and the quotient
  has positive real part. **Refutation candidate:** the constant `4` holds; only a factor `2` is
  lost, not `√2`, because the bound goes through `|re| + |im|`.
* `exists_leaf`: **proved as stated**. **Refutation candidate:** the claim that `G.erase A` is
  coherent holds. The proof does not use trees as such:
  1. `exists_chainConn_card` grows a *chain-connected* subcollection `H` one link at a time,
     using coherence, until it has `G.card − 1` links.
  2. The one remaining link `C` meets some link of `H` (coherence of `G`), and at most one
     (`no_two_nbrs`).
  3. `G.erase C = H` is chain-connected, hence coherent (`isCoherent_of_chainConn`).
  4. The open, triple and circular clauses pass to subcollections.

  `no_two_nbrs` works as follows. Take a *shortest* chain `P 0, …, P k` of links of `H` whose two
  ends are distinct and both meet `C`. By minimality its inner links miss `C`, it has no chords,
  and consecutive links are distinct. So `C, P 0, …, P k` is a circular chain
  (`circularChain_of_minimal`). This includes `k = 1`, where the three links meet pairwise.
* `exists_log_on_treeChain`: **proved as stated**. The induction on `G.card` is
  `exists_log_inv`, which carries the ball invariant: on each nonempty link `A`, `L` agrees with a
  branch `ℓ_A` defined on a whole ball `ball c ε ⊇ A`.
  * Removing a leaf `A` with neighbour `B`, the branches `ℓ_A` and `ℓ_B` differ by a constant on
    the convex set `ball c_A ε ∩ ball c_B ε` (`sub_const_of_exp_eq`). The branch on `A` is
    shifted by that constant.
  * Continuity on `⋃ G` follows from the invariant at the end, because links are open. The
    triple-intersection clause is never used.

### 2.3 No logarithm on a polygon around `p` — proved (`no_log_on_polygon`)

* Per edge `[a, b]`, `log_diff_edge` gives `L b − L a = log ((p − b)/(p − a))` (principal
  branch). Along the edge, `(p − γ t)/(p − a)` runs along the segment from `1` to
  `(p − b)/(p − a)`. That segment avoids the closed negative half-line, because the segment
  `[a, b]` misses `p` (`slit_of_segment_ne_zero`). So `log` of it is continuous, and two
  continuous logarithms differ by a constant.
* Telescoping (`finRotate`) gives `Σ arg ((p − bᵢ)/(p − aᵢ)) = 0`.
* `edge_jump`: `arg ((p − b)/(p − a)) = arg (p − b) − arg (p − a) + 2π j`, with `j ∈ {−1, 0, 1}`
  and `(j : ZMod 2) = ceInd p a b`. The `arg (p − ·)` terms also telescope, so `Σ jᵢ = 0`.
  Hence `parity v p = Σ ceInd = 0`, against `parity v p = 1` (`polyInterior_eq_oddSet`).

**How vertices on the ray were handled** (refutation candidate: it holds). No case split on
vertices was needed. Write `A = p − a`, `B = p − b`.

1. `arg_div_jump`: `j ≠ 0` iff `|arg B − arg A| > π`. The value `±π` is impossible because
   `B/A` lies in the slit plane.
2. Using Mathlib's `0 ≤ arg w ↔ 0 ≤ im w` and `arg w < 0 ↔ im w < 0`, `|arg B − arg A| > π` holds
   iff one of the following holds:
   * `0 ≤ im A`, `im B < 0`, and the cross product `im B · re A − re B · im A` is positive;
   * the same with `A` and `B` exchanged and the cross product negative.

   The sign comes from `‖A‖‖B‖ sin (arg B − arg A)` = the cross product.
3. `crossesEast_iff_cross`: that condition is literally `CrossesEast p a b`.
   * `0 ≤ im A` is `a.2 ≤ p.2` and `im B < 0` is `p.2 < b.2`.
   * The cross-product sign is "the crossing point is east of `p`", after multiplying by
     `b.2 − a.2`.

So a vertex `a` exactly on the east ray (`im A = 0`, `re A < 0`, `arg A = π`) is treated by `arg`
the same way `CrossesEast` treats it: as lying *above* the ray. This is the half-open convention
`a.2 ≤ p.2` of batch 125. Horizontal edges at the height of `p` give `j = 0`, and they are never
crossed.

### 2.4 A polygon in an open set around a point — proved

* `exists_enclosing_polygon_pt`: **proved as stated**. It is the batch-130 proof with `x₀ := x`
  and uses only boundedness.
* `exists_polygon_around`: **proved as stated**.
  1. `R` is chosen with the component of `p` in `Wᶜ` inside `ball 0 R`.
  2. The cut-wire theorem `exists_split_of_no_continuum` is applied in the compact subspace
     `X = Wᶜ ∩ closedBall 0 R`, with `E₁ = {p}` and `E₂ = {x | dist x 0 = R}`. A continuum of `X`
     through `p` lies in that component, so it misses the sphere.
  3. This gives `X = F₁ ⊔ F₂`. `M := F₁` is compact, lies in `ball 0 R`, and is disjoint from the
     closed set `Z = F₂ ∪ {R ≤ dist · 0}`, which contains `Wᶜ ∖ M`.
  4. `IsCompact.exists_cthickening_subset_open` gives `δ` with `cthickening δ M ⊆ Zᶜ`.
  5. Grid of mesh `δ/2`: the frontier of the grid union lies in `cthickening δ M` and misses `M`,
     so it lies in `W`.
  6. `exists_enclosing_polygon_pt` at `p` and `frontier_gridUnion` finish the proof.

### 2.5 Assembly — proved

* `exists_bounded_component_of_separates`: **proved as stated**. **Refutation candidate:** it
  holds.
  * The complement of a closed sup-ball is preconnected: it is the union of four open half-planes
    chained at corners (`isPreconnected_compl_closedBall`).
  * If every component of `Kᶜ` were unbounded, each would meet that set, so all would equal the
    component of one point. Then `Kᶜ` would be connected.
* `isTreeChain_filter_meet`: **proved as stated**. If no link of `H` met a link of `G' ∖ H`,
  then `⋃ H` and `⋃ (G' ∖ H)` would split `K`.
* `treeLike_nonseparating`: **proved**. Take `ε = d/10`, where `d = infDist p K`, so every point
  of a link meeting `K` is at distance `> 9ε > 8ε` from `p`. The assembly is as in the header.
* `theorem7_1951_treeLike` (Theorem 7 as printed) and `isTreeLike_iff_nonseparating` (Theorem 6
  and its converse): **proved**, with the bodies as given.

## 3. Edits to existing files

1. `Tree67.lean`: `IsTreeLike` repaired, with a docstring note.
2. `Tree7.lean`: the comment on `treeLike_nonseparating` now points to `TreeLikeNS.lean`
   (batch 133).
3. `Tree7Comp.lean`: `theorem6_1951_rel`'s proof gains the boundedness of its links (statement
   unchanged). `Enc2.lean` is unchanged.
4. `Ingram68.lean`: the `fugate_cor1` docstring (§0).
5. `Axioms.lean`: new group "Tree-like continua do not separate; Duke Theorem 7 as printed;
   `IsTreeLike` repaired (batch 133)". `axioms.txt` is regenerated.
6. `OPEN.md`: `treeLike_nonseparating` is closed, recorded as false under the old definition and
   proved under the repaired one. The section *Not attempted* is replaced by that record.
7. `LEDGER.md`: two rows. Bing's Theorem 7 (*Bing 1951 (Duke)* table), and the `IsTreeLike`
   commission slip (*Commission slips* table). No further defect was found.
8. `README.md`: the Duke line now reads "Theorems 1–16 as printed, Theorem 6 with its converse",
   with pointers. Batch count is 133.

Additions: `HPC.lean` ends with `import HPC.Plane.TreeLikeNS`. There are two new helper files,
`HPC/Plane/TreeLikeNSGraph.lean` (nerve combinatorics) and `HPC/Plane/TreeLikeNSLog.lean`
(logarithms, the edge jump).

Shape changes, also recorded in the header of `TreeLikeNS.lean`:
* `toCpx` and `continuous_toCpx` are moved to `TreeLikeNSLog.lean`.
* Imports: `Enc1Cyc`, `Cyc2Circle` and `Ingram68` are replaced by `Ingram68Star` and the two
  helper files. `Enc2` is kept.

## 4. Housekeeping

The commission is filed as `doc/batches/COMMISSION-batch133.md` and the skeleton as
`doc/batches/skeletons/TreeLikeNS.lean`. Nothing is left at the root.

Not attempted, as commissioned: the optional Ingram items (Sorgenfrey 1.8, Lemma 3, Theorems 1
and 2(2)).
