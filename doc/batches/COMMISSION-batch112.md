# Commission: batch 112 — the band in dimension ≥ 3, and Hilbert space reduced to finite dimension

**Go!** Runs on top of the batch-111 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch112.md` — this text (also pasted into the prompt);
* `BandN.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/BandN.lean` and
  add `import HPC.Plane.BandN` at the end of the root `HPC.lean`. No existing file is to be
  edited, except `Axioms.lean`/`axioms.txt` (Pacific group, sub-comment "density lemma, batch
  112"). Shapes may be adjusted with the change recorded; split the file if it passes 1000
  lines.

The report names the commission read in its first line.

## 0. On batch 111

Audited: the housekeeping exactly as asked; 282 declarations; `sorryAx` in 10 — the commission's
"stays 9" was my arithmetic slip, the report's count is right (five targets, five consequences).
`lake build HPCArchive HPCCensus` confirmed.

## 1. The task

Towards OPEN.md item 4 (`geomLemma'_of_two_le_rank`), the two halves that do not need the
`d`-dimensional cycle; the skeleton header explains both. The point of (A): in dimension `≥ 3`
the band needs **no normal field** — the constant direction `w = (Σ e i)/√d` is transverse to
every pair of consecutive chords, because all its coordinates are nonzero. The point of (B): a
compact set of a Hilbert space is within `η` of a finite-dimensional subspace, and a threaded
chain of a subspace pulls back to `E` through the orthogonal projection.

## 2. Items

1. **Lattice paths in `ℤ^d`** (`IsUnitStepN`, `LatticePathN`, `latticePtN`, `stepMidN`,
   `stretchTriN`, `polyPathN`, `stretchTriN_subset_ball`, `stretchTriN_subset_thickening`,
   `stretchTriN_separated`). These are `Band.lean`'s definitions and proofs with `Fin d → ℤ` in
   place of `ℤ × ℤ` and an orthonormal family `e : Fin d → E` in place of the pair; coordinates
   `⟪latticePtN e δ p, e i⟫ = δ p i`. The separation lemma's two cases are those of
   `stretchTri_separated`, with `w = Σ (sign (c k' i - c k i)) • e i` in the `ℓ¹` case.

2. **The piecewise-linear path and its injectivity** (`plPathN`, `continuous_plPathN`,
   `plPathN_mem_stretchTriN`, `plPathN_injOn`). `plPathN` is `roundedPath`'s hat-function sum.
   Injectivity on `[1/2, n - 1/2]`: within a stretch, a segment between distinct midpoints
   (`m_{k-1} ≠ m_k` since `c (k+1) ≠ c (k-1)`); adjacent stretches lie in the closed half-spaces
   `⟪· - m_k, u_k⟫ ≤ 0` and `≥ 0` and meet the common line only at `m_k`; nonadjacent stretches
   are separated.

3. **The transverse direction and the band** (`diagDir`, `norm_diagDir`, `diagDir_not_mem_span`,
   `bandN`, `continuous_bandN`, `bandN_injOn`). `diagDir_not_mem_span` is the arithmetic of the
   header (three cases by the number of distinct axes among `u, u', u''`; `3 ≤ d` gives a vanishing
   coordinate in the one- and two-axis cases). `bandN_injOn` as in its docstring: from
   `Γ τ - Γ τ' = (t' - t) δ • w`, either `t = t'` (then `plPathN_injOn`), or the two stretches
   are nonadjacent (`stretchTriN_separated` against `‖(t' - t) δ • w‖ < δ/4`), or equal/adjacent
   (write the difference as `α • (u + u') + β • (u' + u'')` in `δ/2` units and apply
   `diagDir_not_mem_span` coordinatewise).

4. **The chain** (`exists_threadedChain_of_latticePathN`). `BandChain.lean` with `bandN`:
   `threadMap`, `latticeLink`, adjacency, disjointness of nonadjacent links by
   `stretchTriN_separated`, threading by `continuous_bandN`/`bandN_injOn`, the constants `16 δ`,
   `δ`, `δ`, `22 ≤ n`, `m = (n - 4)/6`. If the generic parts of `BandChain.lean` (`chainLam`,
   `exists_link_param`, `threadMap_param`) can be reused as they are, reuse them.

5. **Hilbert space** (`exists_finiteDimensional_subspace_near`, `exists_threadedChain_pullback`,
   `geomLemma'_of_subspaces`). Nets: `IsCompact.finite_cover_balls` or `Metric.finite_approx_of_totallyBounded`;
   `F := span (net) ⊔ (a two-dimensional subspace)`; `2 ≤ Module.rank ℝ E` gives two independent
   vectors. Projection: `orthogonalProjection F` (`F` complete as finite-dimensional);
   `dist x (P_F x) ≤ dist x y` for `y ∈ F`. In `geomLemma'_of_subspaces`: `g' := P_F '' g` is a
   compact continuum of `F` (image of `g` under the continuous `P_F`, taken in the subtype);
   `GeomLemma' F` at `ε/2`; pull back with `η := ε/8`; check the five clauses of `GeomLemma' E`
   (`3 ≤ m`, threaded, `diam < ε/2 + ε/4`, union within `ε/8 + ε/2 + ε/4` of `g`, `g` within
   `ε/4 + ε/2` of the union). The boundedness hypothesis of the diameter clause in
   `exists_threadedChain_pullback` is met because `D'.union ⊆ thickening (ε/2) g'`.

Report each item *proved / refuted / open with the obstruction stated*; refutations first.

## 3. Deliverables

1. Items 1–5; `#print axioms` in `axioms-batch112.txt`; `axioms.txt` regenerated (`sorryAx` in 10
   unless an item is left open).
2. Report: first line names the commission read; items in order; what of `Band.lean`/`BandChain.lean`
   was duplicated and what reused.
3. Not attempted: the five open targets; the `d`-cube cycle and the assembly (batch 113).

## 4. Next

Batch 113: the self-avoiding lattice cycle through the cubes of `ℤ^d` meeting `g` (the splice of
`LatticeCycleAux.lean`, a `d`-cube loop by induction on `d` — two copies of the `(d-1)`-loop on
the bottom and top layers joined by two columns, designated face pairs consistent across shared
faces); the cubes of a `d`-dimensional `E`; `geomLemma'_of_finrank (3 ≤ finrank)`; then
`geomLemma'_of_two_le_rank` from the plane case, this, and `geomLemma'_of_subspaces` — closing
OPEN.md item 4 and Bing's Theorem 2 (Pacific) and Theorem 2 (Duke) in the generality he states.
