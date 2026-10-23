Commission read: `COMMISSION-batch112.md` — batch 112, the band in dimension ≥ 3, and Hilbert space reduced to finite dimension.

# Report, batch 112

**Refutations:** none. No statement of the skeleton is false.

All five items are **proved**. None is open. The three new files contain no `sorry`. All 14
skeleton theorems depend only on `[propext, Classical.choice, Quot.sound]`
(`doc/batches/audits/axioms-batch112.txt`). The five open targets, the `d`-cube cycle and the
assembly were not attempted, as §3.3 specifies. `geomLemma'_of_two_le_rank` (OPEN.md item 4) is
still open.

## 0. Files

* `HPC/Plane/BandNAux.lean` (253 lines, new). Elementary lemmas, namespace `HPC.Plane.BandNAux`:
  * unit steps of `ℤ^d` (`unitN_cases`);
  * the integer dot product `dotZ`;
  * the sign vector `signZ`;
  * the arithmetic of `diagDir_not_mem_span` (`diag_not_mem_span`);
  * the coordinate map `vecL e x = Σ x i • e i` with its inner products, norms and injectivity;
  * the real inequality `sep_ineq` used in the `ℓ¹` case of the separation lemma.

  It imports only Mathlib.
* `HPC/Plane/BandNPath.lean` (575 lines, new): items 1–3. It holds the skeleton's definitions in
  the skeleton's order. Proof-internal lemmas are in the namespace `HPC.Plane.BandN`.
* `HPC/Plane/BandN.lean` (419 lines, new): the skeleton saved as commissioned, with items 4 and 5.
  It imports `BandNPath`. The module header lists every shape change. Items 1–3 were moved out so
  that no file passes 1000 lines; together the three files have 1247 lines.
* `HPC.lean`: `import HPC.Plane.BandN` added at the end.
* `Axioms.lean`:
  * 14 lines added to the Pacific group under `-- density lemma, batch 112`, directly after the
    batch-110 block.
  * `axioms.txt` regenerated: **296 lines**, up from 282. The diff is exactly the 14 new lines.
  * `sorryAx` is in **10** lines, unchanged.
  * The pre-edit `axioms.txt` is saved as `doc/batches/audits/axioms-before-batch112.txt`.
  * The per-batch audit is `doc/batches/audits/Axioms112.lean`, with output in
    `axioms-batch112.txt`.
* The commission and the skeleton are filed as `doc/batches/COMMISSION-batch112.md` and
  `doc/batches/skeletons/BandN.lean`.
* No other existing file was edited. `OPEN.md`, `LEDGER.md` and `README.md` are unchanged.
* The root file `theorems-3-4-scheduling(18).md` came with this upload but is not mentioned in the
  commission. It is the current `doc/theorems-3-4-scheduling.md` plus a new §131. It is left
  untouched, and the doc copy is not replaced.

`lake build HPC` succeeds (8296 jobs). The `sorry` warnings are exactly the five existing ones:
`Theorem4.lean:24` (`theorem3_end`), `Theorem14.lean:209`, `:235`, `Fugate66.lean:577` and
`LatticeCycle.lean:420`.

## 1. Items

### Item 1 — lattice paths in `ℤ^d`: proved

* `IsUnitStepN`, `LatticePathN`, `latticePtN`, `stepMidN`, `stretchTriN` and `polyPathN` are the
  skeleton's definitions, unchanged.
* **Coordinates.** I write `latticePtN e δ p = δ • vecL e (toRN p)` (`latticePtN_eq`). Inner
  products of lattice vectors are then integer dot products (`inner_vecL_toRN`), and unit steps
  have norm 1 (`norm_vecL_unit`).
* `stretchTriN_subset_ball` and `stretchTriN_subset_thickening`: the proofs of `Band.lean`,
  transcribed.
* `stretchTriN_separated` has the two cases of `stretchTri_separated`.
  * **Lattice-adjacent** (`c k' - c k` a unit step `v`). Stretch `k` lies in
    `⟪· - c k, v⟫ ≤ 0` and stretch `k'` in `⟪· - c k', -v⟫ ≤ 0`. This holds because distinct unit
    steps have nonpositive dot product (`dotZ_nonpos_of_ne`), and the self-avoiding path never
    steps from `c k` to `c k'`. The two stretches are therefore at distance at least
    `δ ≥ (√2/2) δ`.
  * **`ℓ¹`-distance `L ≥ 2`.** I take `w = Σ sign (c k' i - c k i) • e i`.
    * Every arm has `|⟪u, w⟫| ≤ 1`, so the gap in direction `w` is at least `(L - 1) δ`.
    * In `ℤ^d`, `‖w‖` is not `√2` but `√r`, where `r ≤ L` is the number of nonzero coordinates
      of `c k' - c k` (`dotZ_signZ_self_le`).
    * From `(L - 1) δ ≤ ‖q - p‖ · ‖w‖`, `‖w‖² ≤ L` and `L ≥ 2` it follows that
      `‖q - p‖ ≥ (√2/2) δ`, because `(L - 1)² ≥ L/2` for `L ≥ 2` (`sep_ineq`).

### Item 2 — the piecewise-linear path: proved

* `plPathN e δ P τ = Σ_{j < n} hat (τ - 1/2 - j) • stepMidN e δ P j`, the formula of
  `roundedPath`. `continuous_plPathN` is immediate.
* The stretch formula (`plPathN_stretch`) is `sum_hat_two` from `BandAux.lean`, and the node
  values (`plPathN_half`) are `Band.sum_hat_half`. Both are reused as they are.
* `plPathN_mem_stretchTriN`: on stretch `k` the path is a convex combination of the two
  midpoints.
* `plPathN_injOn`. Let `k ≤ k'` be the stretches of `τ, τ'` with `Γ τ = Γ τ'`.
  * `k' ≥ k + 2` contradicts the separation lemma (`stretch_close`).
  * `k' = k`: the chord `m_k - m_{k-1} = (δ/2)(u_{k-1} + u_k)` is nonzero because
    `c (k+1) ≠ c (k-1)`.
  * `k' = k + 1`: take the inner product with `u_k`. The two chords have dot product
    `1 + ⟪u_{k-1}, u_k⟫ ≥ 1` and `1 + ⟪u_{k+1}, u_k⟫ ≥ 1` with `u_k`, because consecutive steps
    are not opposite (`dotZ_nonneg_of_ne_neg`). So `(1 - s)(≥ 1) + s'(≥ 1) = 0`, which forces
    `s = 1` and `s' = 0`, the common midpoint. This is the "opposite half-spaces" argument of the
    skeleton.

### Item 3 — the transverse direction and the band: proved

* `norm_diagDir`: `‖Σ e i‖² = d`.
* `diagDir_not_mem_span` (`BandNAux.diag_not_mem_span`). Each unit step is `±` a basis vector,
  on axes `a, b, c`.
  * If some axis `i ∉ {a, b, c}`, then coordinate `i` gives `lam = 0`.
  * Otherwise `Fin d = {a, b, c}`. With `3 ≤ d` this forces `a, b, c` to be pairwise distinct
    (two axes cannot cover `Fin d`).
  * The three coordinates then give `α ε₁ = (α + β) ε₂ = β ε₃ = lam`, and in each of the 8 sign
    cases linear arithmetic gives `lam = 0`.

  This also covers the header's case `d ≥ 4`.
* `continuous_bandN` is immediate.
* `bandN_injOn`. First show `t = t'` (`BandN.bandN_aux`), then cancel and apply `plPathN_injOn`.
  For `bandN_aux`, write `Γ τ - Γ τ' = r • w` with `|r| = |t' - t| δ < δ/4`.
  * Nonadjacent stretches contradict separation, since `δ/4 < (√2/2) δ`.
  * For equal or adjacent stretches, both sides are `vecL` of explicit coordinate vectors
    (`plPathN_stretch'`, `midCN_sub_same`, `midCN_sub_next`). Injectivity of `vecL` gives the
    coordinate identities `α (u + u') + β (u' + u'') = r/√d`, and `diagDir_not_mem_span` gives
    `r = 0`.

### Item 4 — the chain: proved

`exists_threadedChain_of_latticePathN` is the proof of `exists_threadedChain_of_latticePath`,
transcribed with `plPathN`/`bandN`:
* `threadMapN`, `latticeLinkN` and `latticeChainN`, with the same constants `16 δ`, `δ`, `δ`,
  `22 ≤ n` and `m = (n - 4)/6`;
* `plPathN_far`, `plPathN_near`, `dist_latticePtN_le`, `dist_latticePtN_le'` and
  `latticeLinkN_disjoint`;
* threading by `continuous_bandN` and `bandN_injOn`.

The containment of the threaded rectangles in the links uses `‖w‖ = 1`, so
`‖bandN - plPathN‖ = |t| δ < δ/8`. This replaces `‖ν‖ ≤ 1` from the plane.

### Item 5 — Hilbert space: proved

* `exists_finiteDimensional_subspace_near`.
  * Take a finite `η`-net `t ⊆ g` (`IsCompact.finite_cover_balls`).
  * Take a linearly independent set `s` with `#s = 2` (`le_rank_iff_exists_linearIndependent`),
    which is finite.
  * Let `F = span (t ∪ s)`. It is finite-dimensional, and `finrank F ≥ finrank (span s) = 2`.
* `exists_threadedChain_pullback`.
  * `P = F.orthogonalProjection` and `link j = P ⁻¹' (D'.link j) ∩ thickening η F`.
  * Adjacency is the same as in `D'`, in both directions, because `P y = y` on `F`.
  * The threading map is the old one followed by the inclusion `F → E`.
  * Key fact: on `thickening η F`, `dist x (P x) < η` (`starProjection_minimal`). The diameter
    bound, `D.union ⊆ thickening η D'.union` and `D'.union ⊆ D.union` follow from it.
* `geomLemma'_of_subspaces` follows the commission's recipe.
  * `F` for `ε/4`; `g' = P '' g` is a continuum of `F`; `GeomLemma' F` at `ε/2`; pull back with
    `η = ε/8`.
  * Diameter: `< ε/2 + ε/4`. Union within `ε/8 + ε/2 + ε/4` of `g`. `g` within `ε/4 + ε/2` of the
    union.
  * The boundedness hypothesis comes from `D'.union ⊆ thickening (ε/2) g'`.

## 2. Shape changes

All are recorded in the module doc of `HPC/Plane/BandN.lean`. None strengthens a hypothesis.
1. `diagDir_not_mem_span`: the hypotheses `h1 : u' ≠ -u` and `h2 : u'' ≠ -u'` are dropped as
   unused (see item 3).
2. `exists_threadedChain_pullback` and `geomLemma'_of_subspaces`: `[CompleteSpace E]` is dropped
   as unused. The orthogonal projection onto a finite-dimensional subspace exists in any inner
   product space. The planned assembly with `[CompleteSpace E]` still applies.
3. `plPathN_mem_stretchTriN`: `hon` and `hδ` are dropped as unused, and `e`, `δ` are now
   explicit.
4. `plPathN` (a `sorry` definition in the skeleton) is the hat-function sum above.

## 3. What of `Band.lean` / `BandChain.lean` was reused and what was duplicated

* **Reused as they are:**
  * from `BandAux.lean`: `hat`, `continuous_hat`, `sum_hat_two`, `exists_stretch`;
  * from `Band.lean`: `Band.sum_hat_half`, `IsThreadedChain`, `stripSet_subset`, `GeomLemma'`;
  * from `BandChain.lean`: `chainLam`, `chainLam_mul`, `three_le_chainLam`, `chainLam_lt_four`,
    `threadMap_param`, `exists_link_param`.
* **Duplicated with `ℤ^d`/`vecL` in place of `ℤ × ℤ`/`planeL`:**
  * the definitions of item 1;
  * `stepMid_sub_left/right`, `stretchTri_inner_le`, `latticePt_mem_polyPath(')`,
    `stretchTri_subset_ball`, `stretchTri_subset_thickening`, `stretchTri_separated` (with the
    new `ℓ¹` estimate);
  * `roundedPath_mem_stretchTri`, `roundedPath_far`, `roundedPath_near`,
    `dist_latticePt_le(')`, `latticeLink(_disjoint)`, `latticeChain`,
    `isThreadedChain_latticeChain`, and the body of `exists_threadedChain_of_latticePath`.
* **Not used:** the plane's integer lemmas (`unit_cases`, `edge_of_sum`, `locF*`). They are
  replaced by `BandNAux`. The band's injectivity proof is new, since there is no normal field.

## 4. Not attempted

The five open targets; the `d`-cube cycle and the assembly (batch 113).
