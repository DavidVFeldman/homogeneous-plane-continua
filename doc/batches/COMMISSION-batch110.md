# Commission: batch 110 — the lattice cycle through the squares meeting a plane continuum; the density lemma, Pacific Theorem 2 and Duke Theorem 2 in the plane

**Go!** Runs on top of the batch-109 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch110.md` — this text (also pasted into the prompt);
* `LatticeCycle.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/LatticeCycle.lean` and add `import HPC.Plane.LatticeCycle` at the end of the root
  `HPC.lean`. No existing file is to be edited, except `Axioms.lean`/`axioms.txt` (Pacific group,
  sub-comment "density lemma, batch 110"; Duke group, "Theorem 2, in the plane (batch 110)").
  Shapes may be adjusted with the change recorded. If the file grows past 1000 lines, split it
  as in batch 109 and say so.

The report names the commission read in its first line.

## 0. On batch 109

Audited: every item proved; three refutations of my skeleton at degenerate parameters (`m = 0`,
`k > n`, `n = 0`), all accepted. The chamfered corners (piecewise-linear interpolation of the
midpoints and of the normals, injectivity by the unit-square argument over the 12 direction pairs)
are a better route than my quarter circles; the parametrisation and the constants (`λ = (n-1)/(2m+1)`,
`6m + 4 ≤ n < 8m + 5`, `n ≥ 22`) are recorded. 264 declarations, `sorryAx` in 9.

## 1. The task

Supply the path and assemble. The header of `LatticeCycle.lean` describes the cycle construction
and its invariant in full; §2 lists the items. After this batch the density lemma in the plane is
closed: `theorem2_HIC_plane` (Pacific Theorem 2 for a two-dimensional real inner product space)
and `theorem2_1951_plane` (Duke Theorem 2, p. 654: "In a Euclidean space or Hilbert space 'most'
compact continua are snake-like", in the plane) are to be proved with no open dependency. Bing
states both theorems for Euclidean `n`-space and Hilbert space; only the plane is addressed here,
and the report says so. `exists_tame_chain_near`, `dense_pseudoArcs`, `theorem2_HIC` (the
general-`E` statements through the open lemma) are unchanged in this batch; what to do with them
is decided afterwards.

## 2. Items

1. **The connected enumeration** (`exists_connected_enumeration`). Induction on the size of the
   enumerated prefix: if the squares enumerated so far are not all of `T`, the set of enumerated
   squares is closed under adjacency only if it is `T` (`PolyConnected`), so some unenumerated
   square is adjacent to an enumerated one. (A `List` of indices, built by well-founded recursion
   on `T.card - length`, or any other formulation; the statement's shape is a suggestion.)

2. **The cycle** (`exists_latticeCycle`). Induction along the enumeration with the invariant of
   the file header, (a)–(c). Suggested representation: the cycle as a `List (ℤ × ℤ)` with
   `List.Nodup`, `List.Chain'` for the unit steps, and the closing step; the splice as
   `List.rotate` to bring the `σ`-row to the front, then replacement of its five interior
   elements by the 21-point detour (`1 + 19 + 1`: the point of `σ` at offset `1`; the 24-point
   loop of `ℓ` minus the five interior points of its `σ`-row, traversed from the one `σ`-corner
   of `ℓ` to the other; the point of `σ` at offset `7`), a net gain of `16`; state the length
   formula (`L = 24 + 16 (N - 1)` if this count is right). Prove
   `Nodup` of the new list from (b): new points are depth-1 points of `ℓ` or the two points of
   `σ` at offsets `1`, `7`; old points are depth-1 points of other squares, or on sides shared
   within the old set, which meet `σ` only at corners. Prove (a)–(c) for the new set. The base case
   is the loop of `s₁`, the 24 boundary points of `[1,7]²` in fine coordinates.
   *If the invariant needs strengthening, say how.* One place to watch: (a) must say the row is
   consecutive *in some direction*, and the splice must handle both.

3. `exists_latticePath_of_polyomino`: drop the closing step; `n = L - 1 ≥ 23 ≥ 22`.

4. **The squares of the plane** (`exists_orthonormal_pair_span` — from an orthonormal basis of a
   two-dimensional space; `squaresMeeting_finite`; `exists_sq_mem` — `s = (⌊⟪x,e₁⟫/δ⌋, ⌊⟪x,e₂⟫/δ⌋)`;
   `diam_sqSet_le`; `latticePt_mem_sqSet`; `squaresMeeting_connected` — docstring).

5. **Assembly** (`geomLemma'_of_finrank_two`, `dense_pseudoArcs_plane`, `theorem2_HIC_plane`,
   `isGδ_snakeLike`, `dense_snakeLike_plane`, `theorem2_1951_plane`). Constants in the docstring
   of `geomLemma'_of_finrank_two`; `g` nonempty and bounded as a compact continuum; the finite
   set of squares is nonempty since `g` is; the lattice path at fine mesh `δ/8` is placed by
   `latticePt e₁ e₂ (δ/8)`; `exists_threadedChain_of_latticePath` with `δ/8` in place of its `δ`.
   `isGδ_snakeLike`: `{K | IsSnakeLike K} = ⋂ i, {K | ∃ chain …}ᶜᶜ` via `Most.isSnakeLike_iff` and
   `isClosed_notCoverable`.

Report each item *proved / refuted / open with the obstruction stated*; refutations first. Item 2
is the long one; if it is not finished, leave it `sorry` with the invariant as far as proved and
the obstruction stated, and prove items 3–5 from it (the new `sorryAx` lines are then listed in
the report; `OPEN.md` is not edited).

## 3. Deliverables

1. Items 1–5; `#print axioms` in `axioms-batch110.txt`; `axioms.txt` regenerated (`sorryAx` in 9
   if everything is proved).
2. Report: first line names the commission read; items in order; the exact length formula of the
   cycle; any change to the invariant.
3. Not attempted: the five open targets; dimension `≥ 3` and Hilbert space.

## 4. Next

Housekeeping of the open lemma (delete `exists_tame_chain_near` and its two consequences as a
too-strong intermediate of batch 90, or keep them as the open item for dimension `≥ 3`), then Duke
Theorems 6–7 on a polygonal-Jordan-curve-theorem interface.
