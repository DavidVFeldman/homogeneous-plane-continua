Commission read: `COMMISSION-batch98.md` (batch 98: the Cantor organ as a test of Theorem 11), with its skeleton `Organ98.lean`, saved as `HPC/Plane/Organ98.lean`; `import HPC.Plane.Organ98` is added at the end of `HPC.lean`.

# Report, batch 98

## Summary

* **Refutation first.** The gluing question **`isSnakeLike_union_of_terminal` is false**. It
  fails even when `T` is a nondegenerate arc and `H ∪ K` is a continuum. The skeleton statement is
  commented out in `HPC/Plane/Organ98.lean` with the reason, and replaced by two proved results:
  * `isSnakeLike_union_of_terminal_refuted`: the skeleton statement, negated over `Type`;
  * `two_organs_counterexample`: an explicit instance in the compact metric space
    `Organ × [0,1]`. It gives snake-like continua `H₂`, `K₂` with `H₂ ∩ K₂ = T₂`, where `T₂` is
    a nondegenerate arc that is terminal in both. `H₂ ∪ K₂` is a continuum and is **not**
    snake-like.
* **Item 1.** **The organ is snake-like** (`organ_isSnakeLike`, proved). So the organ is **not**
  a counterexample to Theorem 11.
* **Item 2.** `organ_condA_layer` is **proved**. `organ_condA_H_or_K` is **proved**, and
  condition A in fact holds at `p'` on **both** sides (`organ_condA_H`, `organ_condA_K`).
* **Item 3.** `IsTerminalIn` is defined as in the skeleton. `organ_layer_terminal` is **proved**:
  the good layer is terminal in the whole organ (`good_layer_terminal`). For the organ itself the
  gluing works: the two sides and their union are snake-like (`organ_sides_glue`). In general it
  does not (see the refutation above).
* **Axioms.** `Axioms98.lean` writes `axioms-batch98.txt`. Every batch-98 result uses only
  `propext`, `Classical.choice` and `Quot.sound`. `HPC/Plane/Organ98.lean` contains no `sorry`
  (the only occurrence is inside the commented-out false statement).
* **Files.** No existing file is edited, apart from the added import line in `HPC.lean`. New files:
  * `HPC/Plane/Organ98.lean`: the skeleton, plus the two-organ counterexample;
  * `HPC/Plane/OrganZig98.lean`: the zigzag maps;
  * `HPC/Plane/EpsMap98.lean`: the `ε`-map criterion;
  * `Axioms98.lean` and `axioms-batch98.txt`.
* **Shape changes.**
  * `isSnakeLike_union_of_terminal` is commented out (false) and replaced by
    `isSnakeLike_union_of_terminal_refuted`.
  * Added declarations: `organ_condA_H`, `organ_condA_K`, `good_layer_terminal`,
    `organ_sides_glue`, `two_organs_counterexample`, and small helpers.
  * All other skeleton statements are unchanged.

## 1. Refutation of the gluing question (item 3)

**Construction.** Write `t₀ = lam goodC` and work in the compact metric space
`Organ2 := Organ × [0,1]`.

* `H₂ = {(s, 0)}`: the organ at level `0`.
* `K₂ = {(s, t₀ - F s) : F s ≤ t₀}`: the left half `F⁻¹[0, t₀]` of the organ, lifted as the graph
  of `t₀ - F`. This is a homeomorphic copy of the left half.
* `T₂ = {(s, 0) : F s = t₀}`: the good layer at level `0`, an arc (`T2_nontrivial`).

**Properties, all proved.**

* `H₂ ∩ K₂ = T₂`. The graph of `t₀ - F` reaches level `0` exactly over the good layer.
* `H₂` and `K₂` are snake-like (`isSnakeLike_H2`, `isSnakeLike_K2`). Both use the zigzag maps of
  item 1 composed with the first projection; the bound on the second coordinate of `K₂` comes from
  uniform continuity of `F`. The subset form of the `ε`-map criterion is used
  (`isSnakeLike_of_epsMap`).
* `T₂` is terminal in `H₂` and in `K₂` (`terminal_H2`, `terminal_K2`). On both sets a point is
  determined by its first coordinate. The first projection of a subcontinuum is a subcontinuum of
  the organ meeting the good layer, so it lies in the layer or contains it
  (`good_layer_terminal`).
* `H₂ ∪ K₂` is a triod (`two_organs_isTriod`). Its core is `N = T₂`, and the three separated arms
  are:
  * the part of `H₂` left of the layer;
  * the part of `H₂` right of the layer;
  * `K₂ \ T₂`.

  The six separation conditions hold because each closure lies in an explicit closed set: level
  `0` with `F ≤ t₀`; level `0` with `F ≥ t₀`; and the graph with `F ≤ t₀`. A snake-like continuum
  is not a triod (`not_isTriod_of_isSnakeLike`, proved in an earlier batch), so `H₂ ∪ K₂` is not snake-like.

**Obstruction behind it.** Terminality of `T` does **not** put `T` at an end of the chains. In
the organ the good layer is terminal: every subcontinuum that leaves it contains it, because the
neighbouring strands accumulate on all of it from both sides. Yet every `ε`-chain of the organ runs
through the layer with organ on both sides. So `H` may already have arms on both sides of `T`. A
second continuum glued along `T` adds a third arm, and three arms cannot fit in a chain.

**Degenerate `T`.** The skeleton only assumes `T.Nonempty`, and for a one-point `T` the statement
fails for a trivial reason: two arcs meeting at an interior point of one of them form a simple
triod. A one-point `T` is terminal in anything. This case is also formalized:
`arcs_counterexample` (in `HPC/Plane/Organ98.lean`) takes, in the square `[-1,1]²`, the horizontal
diameter `Hs` and the upper vertical radius `Ks`. Both are snake-like (by the `ε`-map criterion,
with a coordinate as the map), they meet in the origin, which is terminal in both, and `Hs ∪ Ks`
is a continuum that is a triod, hence not snake-like. The two-organ example shows the failure
persists for nondegenerate `T`.

**Consequence for a repaired Theorem 11.** Any gluing lemma must ask more than terminality. For
example, it could require that, for every `ε`, `H` and `K` have `ε`-chains in which `T` meets only
the last few links (the continuum analogue of an end point). In the organ the gluing does work
(`organ_sides_glue`), because the good layer sits at the end of the chains of each *half*
`F⁻¹[0,t₀]`, `F⁻¹[t₀,1]`.

## 2. Item 1: the organ is snake-like

**Statement.** `organ_isSnakeLike : IsSnakeLike (univ : Set Organ)`, proved.

### 2.1 The `ε`-map criterion

These results are in `HPC/Plane/EpsMap98.lean`.

* `isSnakeLike_univ_of_epsMap`: a compact connected metric space is snake-like if, for every
  `ε > 0`, it admits a continuous `f : X → ℝ` whose fibres have diameter `< ε`.
* `isSnakeLike_of_epsMap`: the same for a subcontinuum `M`, where only fibres within `M` need to be
  small.

**Proof.**

1. Compactness turns small fibres into a uniform bound: there is `δ > 0` with
   `|f x - f y| < δ → dist x y < ε/2` (`exists_delta_of_fibres`).
2. The image `f(X)` is an interval `[a, b]`.
3. The links are the preimages of the intervals `(a + (i-1)h, a + (i+1)h)`, `i < ⌊(b-a)/h⌋ + 1`,
   with `h = δ/3`. Intervals two apart are disjoint. Neighbouring intervals overlap inside
   `[a, b]`, so the preimages overlap by surjectivity.
4. In the subset version the links are also cut down to a thin neighbourhood of `M`.

### 2.2 The zigzag maps

These are in `HPC/Plane/OrganZig98.lean`. Fix `n` and cut Cantor space into the `2ⁿ` cylinders `w`
of length `n`. For a cylinder `w`:

* its left gluing is along the gap whose index is the position of the last `1` of `w`;
* its right gluing is along the gap whose index is the position of the last `0` of `w`;
* a gluing is at the top for odd indices and at the bottom for even ones.

Let `v` be the binary value of `w`. The map depends on whether the two gluing indices have the
same parity:

* **Different parities** (`¬ Conf`). The cylinder is traversed once, over `[2v, 2v+2]`, by
  `2v + 2·(y or 1-y)`. The orientation runs from the height of the left gluing to that of the
  right gluing.
* **Same parity** (`Conf`). Then both indices have the parity of `n - 1`, because one of them is
  `n - 1`. Each half `w0`, `w1` has gluings of different parities: the halves are glued to each
  other along the gap of index `n`, whose parity is opposite. The halves are traversed over
  `[2v, 2v+1]` and `[2v+1, 2v+2]`.

This is the commission's zigzag. The naive level-`n` zigzag fails because, for example, at level
`3` the gluing pattern is `T B T T T B T`, not alternating. Splitting exactly the `Conf` cylinders
once makes it consistent.

**What is proved.**

* **Well defined on the organ** (`zz_pair`). Identified parameters get the same value. For a gap
  of index `m < n`, the right end of the left cylinder and the left end of the right cylinder both
  take the value `2v + 2` (`zz_pair_left`, `zz_pair_right`). This uses `bval` (binary value) going
  up by one (`pair_bval`). For `m = n` (the middle of a split cylinder) both sides take `2v + 1`
  (`zz_pair_mid`). For `m > n` the two parameters share their first `n + 1` digits.
* **Continuous** (`continuous_organZig`). The map depends on the first `n + 1` digits and is
  affine in the height. It descends through the quotient map `Phi`.
* **Small fibres** (`dist_le_of_organZig_eq`). Points with equal value are within `2 · 2⁻ⁿ`. Equal
  values either lie in the same unit (cylinder, or half of a split cylinder), where they force the
  same height, or at the common end of two adjacent units. In the second case, the converse of the
  binary increment (`exists_pair_of_bval_succ`) produces the gap pair joining them, and both
  points are within `2⁻ⁿ` of the glued point. Within a cylinder of length `n`, points at the same
  height are within `2⁻ⁿ` (`dist_pt_le_of_agree`, from the weight bounds `rr_le`).

**Answer to the commission's worry.** The commission's concern was that deeper strands approach
from one side only, which might break the chain. It does not: the deeper strands of a cylinder
lie inside that cylinder's unit, and a link is a horizontal band across the whole unit.

## 3. Item 2: Bing's nondegenerate branch on the organ

Here `g' = layer (lam goodC)`. It is the single strand of `goodC` (`layer_goodC`), because
`goodC` is the end of no gap. The point `p'` is `pt goodC 1`.

| statement | status | reason |
|---|---|---|
| `organ_condA_layer` | **proved** | `g'` is an arc and `p'` its top. A subcontinuum through `p'` is `pt goodC '' [a,1]`, irreducible between `p'` and `pt goodC a` (`condA_strand_top`, via the height coordinate). |
| `CondA H p'` (`organ_condA_H`) | **proved** | A subcontinuum `W ⊆ H` through `p'` either lies in `g'` (as above) or reaches left of `g'`. In the second case it contains `g'` (`strand_lft_subset`). Take `q` to be its least point in the lexicographic order: least `F`, then least position, which exists by compactness. Any subcontinuum through `p'` and `q` is order-convex and contains `g'`, so it is all of `W`. |
| `CondA K p'` (`organ_condA_K`) | **proved** | Symmetric: take `q` to be the greatest point of `W`. |
| `organ_condA_H_or_K` | **proved** | Via `organ_condA_H`. |

**Comparison with the commission's expectation.** The commission expected condition A to fail on
one side. It does not, because at a good layer the strands accumulate on all of `g'` from **both**
sides, alternating top and bottom gluings at every scale. A subcontinuum through `p'` that runs
into the neighbouring strands must therefore contain all of `g'`. So Bing's claim ("`p'` satisfies
condition A for `H` or `K`") is true here. What fails in Bing's nondegenerate branch is the later
amalgamation step (batch 96), and §1 shows that terminality alone cannot replace it.

## 4. Item 3: gluing along a nondegenerate terminal layer

* `IsTerminalIn` is defined as in the skeleton.
* `organ_layer_terminal` is **proved**. More generally, `good_layer_terminal` shows that a closed
  connected subset of the organ meeting the good layer either lies in it or contains it. If it has
  a point with `F < t₀` it contains the left strand; if it has a point with `F > t₀` it contains
  the right strand; both strands are `strand goodC`.
* `organ_sides_glue` (**proved**): `H`, `K` are snake-like, `H ∩ K = g'`, and `H ∪ K` (the whole
  organ) is snake-like. So in the organ the two sides do glue.
* `isSnakeLike_union_of_terminal` is **refuted** (§1).

## 5. Not attempted (per §4.3 of the commission)

`covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of `theorem10_1951`,
`exists_tame_chain_near`, `isArc_of_separatesPairs`, `exists_degenerate_interior_elt` (false),
`theorem11_1951_of_T10'`.

## 6. Next

Item 1 came out positive, so the organ does not refute Theorem 11, and Theorem 11 still needs a
proof that handles nondegenerate interior elements. The gluing lemma in its terminal-only form is
false (§1), so a repaired proof must either:

* use a stronger gluing hypothesis, with `T` at an end of the chains of each piece (in Bing's
  setting, the pieces `H`, `K` on the two sides of an element); or
* follow a different route, such as Fugate's.

The zigzag construction of §2.2 is itself an instance of the second kind. It builds the chains
directly from the order of the elements and the alternation of the gluings.
