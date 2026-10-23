Commission read: `COMMISSION-batch110.md` — batch 110, the lattice cycle through the squares meeting a plane continuum; the density lemma, Pacific Theorem 2 and Duke Theorem 2 in the plane.

# Report, batch 110

**Refutations:** none. No statement of the skeleton is false.

Every item is **proved**. The two new files contain no `sorry`. The density lemma in the plane is
closed: `theorem2_HIC_plane` (Pacific Theorem 2) and `theorem2_1951_plane` (Duke Theorem 2, p. 654)
hold for every two-dimensional real inner product space and depend only on
`[propext, Classical.choice, Quot.sound]`. Only the plane is treated. Bing states both theorems for
Euclidean `n`-space and Hilbert space; dimension `≥ 3` and Hilbert space were not attempted, as the
commission specifies. `exists_tame_chain_near`, `dense_pseudoArcs` and `theorem2_HIC` (the
general-`E` statements through the open lemma) are unchanged.

## 0. Files

* `HPC/Plane/LatticeCycleAux.lean` (531 lines): the combinatorics of the cycle (item 2). It also
  holds the skeleton's definitions `PolyConnected`, `InSq` and `InSqInt`, moved there unchanged so
  the combinatorial file does not depend on the main file. Proof-internal definitions and lemmas
  are in the namespace `HPC.Plane.LCyc`. The public addition is `exists_latticeCycle'`, the cycle
  with its exact length.
* `HPC/Plane/LatticeCycle.lean` (405 lines): the skeleton with items 1 and 3–5 completed, and
  item 2 derived from `exists_latticeCycle'`. The module header now describes the construction
  actually used.
* `HPC.lean`: `import HPC.Plane.LatticeCycle` added at the end.
* `Axioms.lean`: 13 lines added to the Pacific group under `-- density lemma, batch 110`, and 3
  lines added to the Duke group under `-- Theorem 2, in the plane (batch 110)`. The audit file is
  `doc/batches/audits/Axioms110.lean`, with output in `doc/batches/audits/axioms-batch110.txt`.
  The pre-edit `axioms.txt` is saved as `doc/batches/audits/axioms-before-batch110.txt`.
  `axioms.txt` is regenerated: 280 lines, up from 264. `sorryAx` is still in exactly 9 lines. The
  diff consists only of the 16 new lines.
* Filing: commission → `doc/batches/COMMISSION-batch110.md`; skeleton →
  `doc/batches/skeletons/LatticeCycle.lean`.
* No other existing file was edited. `OPEN.md` is unchanged.

## 1. The connected enumeration — proved

`exists_connected_enumeration`: statement as in the skeleton. The proof is by induction on the
length `k` of the enumerated prefix (`1 ≤ k ≤ |T|`). If `k < |T|`, the image of the prefix is a
nonempty proper subset of `T`. By `PolyConnected` it is not closed under adjacency within `T`, so
some square of `T` outside it is adjacent to an enumerated square. That square is appended with
`Function.update`.

The cycle construction does not use the enumeration directly. It runs the same induction on
subsets `A ⊆ T` with `|A| = k` (`LCyc.exists_inv_sub`), which avoids the index bookkeeping.

## 2. The cycle — proved, with a different splice (invariant changed)

`exists_latticeCycle`: statement as in the skeleton. `exists_latticeCycle'` (new) adds the exact
length:

\[ L = 26 N - 2 \qquad (N = |T|),\]

that is, 24 for one square and `+26` for each further square.

**Change of construction.** The skeleton replaces the five interior points of a whole free row
(invariant (a): seven consecutive points). I replace a single *edge* instead. This keeps the local
surgery to one insertion point and needs one case analysis (4 sides × 2 orientations), which
`decide` checks in the coordinates of square `0`. I did not check the skeleton's count of
`+16` per square, because that construction was not used.

*Notation.* `dvec i` (`i : Fin 4`) are the four unit directions. For a square `s` and side `i`,
`pA s i` and `pB s i` are the depth-1 points of the row along side `i` at offsets `4` and `3`
(`pA s i = 8 s + (4,4) + 3 dvec i`, and `pB` is one step back along the side).

*Invariant* (`LCyc.Inv T L c`, for the closed path `c 0, …, c (L-1)`):

* `2 ≤ L`, `L = 26 |T| - 2`, the points are pairwise distinct, and `c k`, `c ((k+1) mod L)` are a
  unit step apart for every `k < L`;
* (b) every point is a depth-1 point of a square of `T`, or one of the two middle points
  `pA s i + dvec i`, `pB s i + dvec i` of a side shared by two squares `s, s + dvec i ∈ T`;
* (c′) every square of `T` has a depth-1 point on the cycle (replaces (c));
* (a′) for every `s ∈ T` and every side `i` not shared within `T` (`s + dvec i ∉ T`), the pair
  `pA s i, pB s i` is an edge of the cycle, in one direction or the other (replaces (a)).

The direction issue the commission raised is handled by (a′), which allows either orientation, and
by the splice, which comes in two orientations `o : Bool`.

*Base.* The depth-1 loop of `s₁` (24 points, the boundary of `[1,7]²`, counterclockwise;
`LCyc.inv_base`).

*Step* (`LCyc.inv_grow`). Let `ℓ = s + dvec i ∉ T` with `s ∈ T`. By (a′) some edge `x → y` is the
middle pair of side `i` of `s`. Rotate the cycle so that `x → y` is the closing edge
(`LCyc.inv_rot`). Then append the 26-point detour (`LCyc.splice`):

\[ x + d,\ \text{the depth-1 loop of } \ell \text{ traversed the long way from } x + 2d \text{ to } y + 2d,\ y + d \qquad (d = \texttt{dvec}\ i).\]

Facts used, all checked by `decide` in the coordinates of square `0` and then translated:

* the detour has distinct points;
* consecutive detour points are a unit step apart, and so are its ends with `x` and `y`;
* every detour point is a depth-1 point of `ℓ` or one of `x + d`, `y + d`;
* for every side `j ≠ i + 2` of `ℓ`, the middle pair `pA ℓ j, pB ℓ j` is consecutive in the
  detour.

*Self-avoidance.* By (b), an old point is not a depth-1 point of `ℓ`, because depth-1 points of
distinct squares are distinct and side points are not depth-1 points. An old point is also not
one of `x + d`, `y + d`: a middle side point determines its side, and that side is not shared
within `T` because `ℓ ∉ T` (`LCyc.side_eq`).

*Old free pairs.* An old free pair other than `{x, y}` stays an edge, because a middle pair
determines its square and side (`LCyc.pair_eq`). The pair `{x, y}` belongs to side `i` of `s`,
which is now shared.

## 3. `exists_latticePath_of_polyomino` — proved

The cycle minus its closing step gives `n = L - 1 ≥ 23` (indeed `n = 26 N - 3`). Injectivity on
`Iic (L-1)` is injectivity on `Iio L`.

## 4. The squares of the plane — proved

* `exists_orthonormal_pair_span`: `stdOrthonormalBasis` reindexed by `finCongr h`, together with
  `OrthonormalBasis.sum_repr'`.
* `squaresMeeting_finite`: if `g ⊆ closedBall 0 R`, every square meeting `g` has indices in
  `[-M, M]²` with `M = ⌈R/δ⌉ + 1`.
* `exists_sq_mem`: `s = (⌊⟪x,e₁⟫/δ⌋, ⌊⟪x,e₂⟫/δ⌋)`. **Shape change:** the unused hypotheses `hon`
  and `hspan` are dropped. The square `sqSet` is defined through the two inner products, so
  neither hypothesis is needed.
* `diam_sqSet_le`: `x - y = a e₁ + b e₂` with `|a|, |b| ≤ δ`, so `‖x - y‖² = a² + b² ≤ 2δ²`.
* `latticePt_mem_sqSet`: `⟪latticePt e₁ e₂ (δ/8) p, e₁⟫ = (δ/8) p.1`, and similarly for `e₂`.
* `squaresMeeting_connected`: **shape change:** the unused hypotheses `hon` and `hspan` are
  dropped. The proof follows the docstring, with one simplification. Suppose `x ∈ g` lies in
  `a ∈ A` and `b ∉ A`. The indices differ by at most 1 in each coordinate. If they differ in only
  one coordinate, the squares are adjacent. If they differ in both, the single square
  `(a.1, b.2)` contains `x`, so it lies in `T`, and it is adjacent to both `a` and `b`. Only one
  of the two other squares at the corner is needed.

## 5. Assembly — proved

* `geomLemma'_of_finrank_two`: constants `δ = ε/4` and fine mesh `δ/8`, as in the docstring.
  Links have diameter `≤ 16 (δ/8) = ε/2 < ε`.
  * Union within `ε` of `g`: a point of the union is within `δ/8` of a point `z` of the polygonal
    path. `z` is within `δ/8` of a lattice point of the path (one step, by convexity of the
    closed ball). That lattice point is in a closed square meeting `g`, of diameter `≤ 2δ`. The
    total is `< δ/4 + 2δ < ε`.
  * `g` within `ε` of the union: `x ∈ g` lies in a square `s ∈ T`, which holds a depth-1 path
    point within `2δ`, which is within `δ/8` of the union.
* `dense_pseudoArcs_plane`, `theorem2_HIC_plane`: `dense_pseudoArcs_of'` and `theorem2_HIC_of'`
  applied to `geomLemma'_of_finrank_two`.
* `isGδ_snakeLike` (any metric space): `{K | IsSnakeLike K} = ⋂ i, (F_i)ᶜ` via
  `Most.isSnakeLike_iff`, with each `F_i` closed (`isClosed_notCoverable`).
* `dense_snakeLike_plane`: pseudo-arcs are snake-like, so the set is dense by `Dense.mono`.
* `theorem2_1951_plane`: the two statements combined.

## 6. Shape changes, summarised

1. `PolyConnected`, `InSq` and `InSqInt` moved, unchanged, to `HPC/Plane/LatticeCycleAux.lean`.
2. `exists_sq_mem` and `squaresMeeting_connected`: the unused hypotheses `hon` and `hspan` are
   removed.
3. New public theorem `exists_latticeCycle'`, giving the length formula `L = 26 N - 2`.
4. Invariant and splice changed (§2): one edge is replaced instead of a five-point row; (a) is
   replaced by (a′) and (c) by (c′); the gain is `26` points per square instead of `16`.

## 7. Not attempted

The five open targets; dimension `≥ 3` and Hilbert space.
