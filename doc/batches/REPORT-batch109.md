Commission read: `COMMISSION-batch109.md` — batch 109, threaded chains, and the band around a self-avoiding lattice path (density lemma, first half).

# Report, batch 109

**Refutations (all at degenerate parameters; each refutation is proved in Lean, and the statement
is corrected and proved):**

1. `stripSet_eq` is false for `m = 0`: `stripSet 0 = ∅`, while `(0, 1) × (0, 1)` is not empty
   (`stripSet_zero_ne`). The corrected `stripSet_eq` assumes `0 < m`. The inclusion
   `stripSet m ⊆ (0, 2m+1) × (0, 1)` holds for every `m` (`stripSet_subset`). This is the form the
   chain proof uses, so `m = 0` needs no special case there.
2. `stretchTri_subset_ball` is false for `k > n`, because the values of `c` past `n` are
   unconstrained. Take `n = 0`, `c i = (10 i, 0)`, `k = 1`: the stretch triangle `1` contains the
   midpoint of `c 0` and `c 1`, which is `5δ` from `c 1` (`stretchTri_subset_ball_false`). The
   corrected statement assumes `k ≤ n`.
3. `stretchTri_subset_thickening` is false for `n = 0`: the polygonal path is empty and the
   stretch triangle `0` is `{c 0}` (`stretchTri_subset_thickening_false`). The corrected statement
   assumes `0 < n`.

Every item is **proved**. There is no `sorry` in the three new files.

## 0. Files

* `HPC/Plane/Band.lean`: the skeleton with items 1–3 completed. Proof-internal coordinate
  definitions and lemmas are in the namespace `HPC.Plane.Band`.
* `HPC/Plane/BandChain.lean`: item 4 (the chain). It was split off so that `Band.lean` stays under
  1000 lines.
* `HPC/Plane/BandAux.lean`: elementary integer and real lemmas (`HPC.Plane.BandAux`): the four
  unit vectors, the band over one stretch in lattice coordinates (`locF`), the hat-function
  interpolation, and integer rounding.
* `HPC.lean`: `import HPC.Plane.Band` and `import HPC.Plane.BandChain` added at the end.
* `Axioms.lean`: 21 lines added to the Pacific group under the sub-comment
  `-- density lemma, batch 109`. Audit file: `doc/batches/audits/Axioms109.lean`, output in
  `doc/batches/audits/axioms-batch109.txt`. The pre-edit `axioms.txt` is saved as
  `doc/batches/audits/axioms-before-batch109.txt`. `axioms.txt` is regenerated (264 lines, up from
  243; `sorryAx` still in exactly 9 lines; the diff is only the 21 new lines).
* Filing: commission → `doc/batches/COMMISSION-batch109.md`; skeleton →
  `doc/batches/skeletons/Band.lean`.
* No other existing file was edited.

## 1. The parametrisation chosen for `roundedPath` / `roundedNormal`

The corners are **chamfered, not rounded**. Let `m_i` be the midpoint of step `i` and
`N_i = J u_i` the left unit normal of step `i`, where `u_i = c (i+1) - c i` and
`J (a, b) = (-b, a)`. Then

* `Γ = roundedPath` is the piecewise-linear interpolation with `Γ (i + 1/2) = m_i`;
* `ν = roundedNormal` is the piecewise-linear interpolation with `ν (i + 1/2) = N_i`.

Both are written as finite sums of hat functions, `Σ_{j<n} max 0 (1 - |τ - 1/2 - j|) • X_j`, so
they are continuous on all of `ℝ`. On stretch `k` (`1 ≤ k ≤ n - 1`, `τ = k - 1/2 + s`,
`s ∈ [0, 1]`):

* `Γ τ = (1 - s) m_{k-1} + s m_k`. On a straight stretch these are the two half-steps through
  `c k`. At a corner it is the chord between the two midpoints, a segment inside the stretch
  triangle.
* `ν τ = (1 - s) N_{k-1} + s N_k`. This is constant on a straight stretch. At a corner it is not
  unit length: `√2/2 ≤ ‖ν‖ ≤ 1`.

At a left turn the band over the corner stretch is `z - (1/2 + t)((1-s) u + s u')` in lattice
units, with `z = c k - u/2 + u'/2`. This is the polar picture of the commission, with the quarter
circle replaced by the chord. At a right turn the sign of `t` is reversed. Only the full stretches
are used: `τ ∈ [1/2, n - 1/2]`. The end half-steps from `c 0` and to `c n` are dropped. The end
lattice points are still within `δ/2` of `Γ (1/2) = m_0` and `Γ (n - 1/2) = m_{n-1}`.

**Why injectivity is easy with this choice** (`band_injOn`). The commission's three cases are
replaced by a single square argument. In lattice coordinates relative to `c k`, the band over
stretch `k` is `locF a b s t`, with `a = c (k-1) - c k` and `b = c (k+1) - c k` two distinct unit
vectors. For `|t| < 1/8`:

* it lies in the closed square `[-1/2, 1/2]²` (`locF_bound`);
* it lies in the open square for `0 < s < 1` (`locF_strict`);
* it is injective in `(s, t)` (`locF_inj`).

Each of these is checked over the 12 pairs `(a, b)`.

Now take two band points over stretches `k`, `k'` that coincide. If `c k = c k'`, then `k = k'`,
and `locF_inj` gives equal parameters. Otherwise the two closed unit squares around distinct
lattice points share only boundary, so both parameters are stretch ends (`s ∈ {0, 1}`). There the
band point is `m_i + t N_i`. Doubling its coordinates gives an integer point `c_i + c_{i+1}` plus
a perturbation of size `< 1/4`. So `c_i + c_{i+1}` is determined, hence the edge `{c_i, c_{i+1}}`
(`edge_of_sum`), hence `i` (self-avoidance) and then `t` (`mid_inj`).

`stretchTri_separated` is used only for the chain (disjointness of nonadjacent links), not for
`band_injOn`.

## 2. Items

### Item 1. Threaded chains — proved

`stripSet_eq` (with `0 < m`, see refutation 1), `IsThreadedChain`,
`isThreadedChain_of_isTameChain` (`f = Φ ∘ planeMap`), `exists_pseudoArc_in_threadedChain`,
`GeomLemma'`, `geomLemma'_of_geomLemma`, `dense_pseudoArcs_of'`, `theorem2_HIC_of'`. The three
proofs follow the originals line by line, with `f` in place of `Φ ∘ planeMap`.

**`IsMonotoneMap` needs nothing more than `ContinuousOn f M`.** Its definition is
`ContinuousOn f M ∧ f '' M = M' ∧ ∀ y ∈ M', IsConnected (M ∩ f ⁻¹' {y})`. Continuity on `M` follows
from `ContinuousOn f (stripSet m)` and `M ⊆ stripSet m`. The fibres are singletons by `InjOn f
(stripSet m)`. `theorem4_HIC` needs nothing else. `exists_pseudoArc_in_threadedChain` does not use
`[InnerProductSpace ℝ E]` (only the metric), so the instance is omitted there.

### Item 2. Lattice paths and stretch triangles — proved

* `stretchTri_subset_ball` (with `k ≤ n`, see refutation 2): the Euclidean closed ball of radius
  `δ/2` contains `c k` and both midpoints, and is convex.
* `stretchTri_subset_thickening` (with `0 < n`, see refutation 3): every stretch triangle lies in
  `closedBall (c k) (δ/2)`, and `c k` lies on the polygonal path.
* `stretchTri_separated`, as stated. Both cases use a single separating direction `w`, with the
  half-spaces handled by convexity (`stretchTri_inner_le`).
  * ℓ¹-distance `≥ 2`: take `w = (±1, ±1)`, with the sign of each coordinate of `c k' - c k`.
    Then `⟪· - c k, w⟫ ≤ δ/2` on stretch `k`, `⟪· - c k', w⟫ ≥ -δ/2` on stretch `k'`,
    `⟪c k' - c k, w⟫ ≥ 2δ` and `‖w‖ = √2`. This gives a distance of at least `δ/√2`.
  * Lattice-adjacent, `w = c k' - c k`: the arms of `c k` differ from `w` and the arms of `c k'`
    differ from `-w`, by self-avoidance and `k' ≥ k + 2`. Distinct unit vectors have dot product
    `≤ 0` (`dot_nonpos_of_ne`). This gives a distance of at least `δ`.

### Item 3. Rounded path, normal, band — proved (chamfered; §1)

* `roundedPath_continuousOn`, `roundedNormal_continuousOn`, `band_continuousOn`: proved as stated,
  since the maps are continuous everywhere. The unused hypotheses `hon` and `hδ` are dropped.
* `norm_roundedNormal`: **shape change**. It is `‖ν τ‖ ≤ 1` for `τ ∈ [1/2, n - 1/2]` (`2 ≤ n`),
  not `= 1`. Downstream only `≤ 1` is used.
* `roundedPath_mem_stretchTri`: stated for `1 ≤ k < n` and `τ ∈ [k - 1/2, k + 1/2]`. These
  stretches cover `[1/2, n - 1/2]` (`BandAux.exists_stretch`).
* `band_injOn`: on `[1/2, n - 1/2] × (-1/8, 1/8)`, with `2 ≤ n`.
* `roundedNormal` keeps the skeleton's `δ` argument (unused; named `_δ`) so that call sites keep
  the skeleton's shape.

### Item 4. The chain — proved (`HPC/Plane/BandChain.lean`)

* `threadMap p = band (1/2 + λ p.1, (p.2 - 1/2)/4)`, with `λ = chainLam n m = (n - 1)/(2m+1)`.
* `latticeLink j` is the open `δ/8`-thickening of `Γ` over `[1/2 + 2λj, 1/2 + λ(2j+3)]`.
* `latticeChain`, `latticeChain_link` (by `rfl`), `isThreadedChain_latticeChain`.
* `exists_threadedChain_of_latticePath`, with the commission's constants `16 δ` (the proof gives
  `13.25 δ`), `δ` and `δ`.

**Constants changed.** The parameter range has length `n - 1` instead of `n`, so
`λ = (n - 1)/(2m + 1)`. The condition `λ ∈ [3, 4)` becomes the hypotheses `6m + 4 ≤ n < 8m + 5` of
`latticeChain`, in place of `6m + 3 ≤ n < 6m + 9`. The band theorem takes `m = (n - 4)/6` and needs
**`n ≥ 22` instead of `21`** (for `m ≥ 3`). The constants `1/8` and `16 δ` are unchanged.

The proofs follow the commission:

* **Adjacency.** Links `j` and `j + 1` share `Γ (1/2 + λ(2j + 2))`. For `j' ≥ j + 2` the parameter
  gap is at least `λ ≥ 3`, so the two stretches are at least two apart (`roundedPath_far`). The
  separation `(√2/2) δ > δ/4` then makes the two `δ/8`-thickenings disjoint.
* **Threading.** Continuity and injectivity of `threadMap` on the strip come from `continuous_band`
  and `band_injOn`. The strip maps into `[1/2, n - 1/2] × (-1/8, 1/8)`, and `‖(t δ) • ν‖ < δ/8`.
* **Diameter.** Two points of a link lie in stretches at most 12 apart, since the parameters
  differ by `≤ 3λ < 12`. Consecutive lattice points are `δ` apart, so the bound is
  `δ/8 + δ/2 + 12 δ + δ/2 + δ/8 ≤ 16 δ`.
* **The union is within `δ` of the polygonal path:** `δ/8 + δ/2`.
* **Every `c i` is within `δ/2` of `Γ (i ± 1/2)`**, which lies in some link
  (`exists_link_param`).

## 3. Audit

`lake build HPC` succeeds. The only `declaration uses sorry` warnings are the five existing open
targets. The 21 new declarations listed in `axioms-batch109.txt` depend only on `propext`,
`Classical.choice` and `Quot.sound`. `sorryAx` still appears in exactly 9 lines of `axioms.txt`.

## 4. Not attempted

As instructed: the five open targets, the combinatorial lemma and the assembly (batch 110), and
dimension `≥ 3`. `exists_tame_chain_near` is unchanged.
