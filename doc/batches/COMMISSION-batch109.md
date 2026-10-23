# Commission: batch 109 — threaded chains, and the band around a self-avoiding lattice path (density lemma, first half)

**Go!** Runs on top of the batch-108 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch109.md` — this text (also pasted into the prompt);
* `Band.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/Band.lean` and add
  `import HPC.Plane.Band` at the end of the root `HPC.lean`. No existing file is to be edited,
  except `Axioms.lean`/`axioms.txt` (add the new theorems to the Pacific group under a sub-comment
  "density lemma, batch 109"). Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 108

Audited: all four items proved, no refutation; 243 declarations, `sorryAx` in 9. The ledger of the
arcs paper's Theorem 5 is accepted as written; in particular the two suspected gaps that turned out
not to be gaps (`ΣN_i ≠ M`, and `E_i · F_i` without openness of `E_i`) are recorded as such.

## 1. What this batch is for

The open `exists_tame_chain_near` (OPEN.md item 4) asks for a chain whose links are the images of
the standard boxes under a *homeomorphism of `E`*. The batch-90 report records the obstruction:
bending the straight strip at the corners of a polygonal arc by a homeomorphism of the whole
plane. But the only consumer, `exists_pseudoArc_in_tameChain`, uses far less: its proof takes the
homeomorphism `Φ`, composes it with `planeMap`, and then uses only (i) continuity, (ii)
injectivity, both on the planar pseudo-arc `M ⊆ ⋃ stdRect j`, and (iii)
`f '' stdRect j ⊆ D.link j`. Nothing about openness of `f`, nothing about the links being images.

So the lemma is restated with that weaker notion (`IsThreadedChain`, §2 item 1), and the geometric
construction becomes a *band* around a self-avoiding lattice path with rounded corners: a map of
the strip into `E` that is continuous and injective on the strip, no homeomorphism of the plane
and no bending of the complement. This batch builds the band and the chain from a given path
(items 2–4). Batch 110 will supply the path (a self-avoiding lattice cycle inside the grid squares
meeting a plane continuum, through every one of them — an induction adding one square at a time)
and assemble the density lemma in the plane, Pacific Theorem 2 and Duke Theorem 2 for the plane.
Dimension `≥ 3` and Hilbert space are not addressed by this route; `exists_tame_chain_near` stays
as it is in this batch (nothing is deleted).

## 2. Items

1. **Threaded chains** (`stripSet`, `stripSet_eq`, `IsThreadedChain`,
   `isThreadedChain_of_isTameChain`, `exists_pseudoArc_in_threadedChain`, `GeomLemma'`,
   `geomLemma'_of_geomLemma`, `dense_pseudoArcs_of'`, `theorem2_HIC_of'`). The three proofs
   `exists_pseudoArc_in_threadedChain`, `dense_pseudoArcs_of'`, `theorem2_HIC_of'` are those of
   `exists_pseudoArc_in_tameChain`, `dense_pseudoArcs_of`, `theorem2_HIC_of` with `f` in place of
   `Φ ∘ planeMap` (continuity and injectivity on `M ⊆ stripSet m`). If `IsMonotoneMap` needs more
   than `ContinuousOn f M`, say what.

2. **Lattice paths and stretch triangles** (`IsUnitStep`, `LatticePath`, `latticePt`, `stepMid`,
   `stretchTri`, `polyPath`, `stretchTri_subset_ball`, `stretchTri_subset_thickening`,
   `stretchTri_separated`). The separation lemma is the geometric heart; its two cases are in the
   docstring. The `ℓ¹` case: for `p` in the `ℓ¹`-ball of radius `δ/2` about `c k` and `q` in the
   one about `c k'`, `‖p - q‖₁ ≥ ‖c k - c k'‖₁ - δ ≥ δ`, and `‖·‖₂ ≥ ‖·‖₁/√2` in the
   `(e₁, e₂)`-plane. The adjacent case: `c k' = c k + e` with `e` a unit lattice vector; the
   path-neighbours `c (k-1)`, `c (k+1)` are not `c k'` (injectivity on `Iic n` and `|k - k'| ≥ 2`),
   so they are `c k + e'` with `e' ≠ e`, hence `⟪e', e⟫ ≤ 0`; the stretch triangle `k` is the
   convex hull of points with `⟪· - c k, e⟫ ≤ 0`; symmetrically for `k'` with `≥ δ`. (Coordinates:
   `⟪latticePt p, e₁⟫ = δ p.1`, `⟪latticePt p, e₂⟫ = δ p.2` by orthonormality; the construction
   never leaves the `(e₁, e₂)`-plane.)

3. **The rounded path, the normal and the band** (`roundedPath`, `roundedNormal`, the four
   continuity/norm/containment lemmas, `band`, `band_injOn`, `band_continuousOn`). The
   definitions are work items: any parametrisation with the stated properties is acceptable,
   recorded. Suggested: on `[k - 1/2, k + 1/2]` with `s = τ - (k - 1/2) ∈ [0, 1]`, straight
   stretch `Γ τ = m_{k-1} + s • (m_k - m_{k-1})`; quarter circle with centre `z` (lattice
   `c k - u/2 + u'/2`, `u = c k - c (k-1)`, `u' = c (k+1) - c k`), `Γ τ = z + (δ/2) •
   (cos (sπ/2) • (-u') + sin (sπ/2) • u)` — check that this runs from `m_{k-1} = z - (δ/2) u'`
   to `m_k = z + (δ/2) u` (in `E`-units) and is tangent to both steps there. `ν` on the quarter
   circle is `∓ (cos (sπ/2) • (-u') + sin (sπ/2) • u)`, sign by the turn. The end stretches
   `k = 0`, `k = n` are the half-steps. Injectivity (`band_injOn`): the three cases of the
   docstring. The adjacent case needs, for the band over stretch `k`, `⟪p - m_k, u_k⟫ ≤ 0`
   (straight: `= (s - 1) δ`; quarter circle: `= -(r cos θ)` with `r ∈ (3δ/8, 5δ/8)`), and the
   converse inclusion for stretch `k + 1`; equality only at `τ = k + 1/2`, where both give
   `m_k + (t δ) • ν (k + 1/2)`. The nonadjacent case: a band point over stretch `k` is within
   `δ/8` of `Γ τ ∈ stretchTri k`; two such for stretches `≥ 2` apart are `≥ (√2/2 - 1/4) δ > 0`
   apart.

4. **The chain** (`threadMap`, `latticeLink`, `latticeChain`, `latticeChain_link`,
   `isThreadedChain_latticeChain`, `exists_threadedChain_of_latticePath`). `λ = n/(2m+1)`; with
   `6m + 3 ≤ n < 6m + 9`, `λ ∈ [3, 3 + 6/(2m+1))`. Links are open (thickenings). Adjacency: links
   `j`, `j+1` share `Γ (λ (2j + 5/2))`; links `j`, `j'` with `j' ≥ j + 2` have `τ`-ranges
   `[2λj, λ(2j+3)]` and `[2λj', …]` with `2λj' - λ(2j+3) ≥ λ ≥ 3`, so a stretch of the first and a
   stretch of the second have indices `≥ 2` apart, and `stretchTri_separated` with the two `δ/8`
   thickenings gives disjointness (`(√2/2) δ > δ/4`). Threading: `threadMap '' stdRect j ⊆
   latticeLink j` since `x ∈ (2j, 2j+3)` gives `λ x` in the range and `|t| < 1/8`; `ContinuousOn`
   and `InjOn` on `stripSet m` from `band_continuousOn`, `band_injOn` and `stripSet_eq`
   (`λ x ∈ (0, n)`). Diameter: `Γ` over a `τ`-interval of length `3λ < 12` meets at most 13
   consecutive stretch triangles, each within `δ/2` of its lattice point, consecutive lattice
   points `δ` apart: `≤ 13δ`, plus `δ/4`. Union within `δ`: `δ/8 + δ/2`
   (`stretchTri_subset_thickening`). Every `c i` within `δ` of the union: `Γ i ∈ stretchTri i`
   is within `δ/2` of `c i`, and `Γ i` lies in some link (`i ≤ n = λ (2m+1)`; the link ranges
   cover `[0, λ(2m+1)]`). Choose `m := (n - 3) / 6` (natural division); `21 ≤ n` gives `m ≥ 3`.

Report each item *proved / refuted / open with the obstruction stated*; refutations first. Constants
(`1/8`, `16 δ`, `21`) may be changed if the proof wants others; record the change.

## 3. Deliverables

1. Items 1–4; `#print axioms` in `axioms-batch109.txt`; `axioms.txt` regenerated (`sorryAx` still
   in 9 unless an item is left open, in which case the new `sorry` is listed in the report and in
   `OPEN.md` is *not* edited — the item simply stays in the report as open).
2. Report: first line names the commission read; items in order; the parametrisation chosen for
   `roundedPath`/`roundedNormal`; any constant changed.
3. Not attempted: the five open targets; the combinatorial lemma and the assembly (batch 110);
   dimension `≥ 3`.

## 4. Next

Batch 110: the self-avoiding lattice cycle inside the grid squares meeting a plane continuum,
through every square (induction over a connected enumeration of the squares, splicing a detour
into each new square along the shared side); the assembly `GeomLemma' E` for
`finrank ℝ E = 2`; `dense_pseudoArcs_plane`, `theorem2_HIC_plane`; Duke Theorem 2 for the plane
(snake-like continua a dense `G_δ`).
