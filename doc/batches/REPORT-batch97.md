Commission read: `COMMISSION-batch97.md` (batch 97: Q-deg, a degenerate interior element of Bing's decomposition), with its skeleton `Layers51.lean`, saved as `HPC/Plane/Layers51.lean`; `import HPC.Plane.Layers51` is added at the end of `HPC.lean`.

# Report, batch 97

## Summary

* **Refutations first.** **Q3 (`bingElt_degenerate_of_isContPt`) is false**, and so is
  **Q-deg (`exists_degenerate_interior_elt'`, i.e. `exists_degenerate_interior_elt` of
  `Theorem11.lean`)**. The counterexample is a `BingS` space in which *no* element is degenerate,
  while the elements are continuous at the points of uncountably many interior elements. Both
  skeleton statements are commented out in `HPC/Plane/Layers51.lean` with the reason. The proved
  negations are:
  * `bingElt_degenerate_of_isContPt_refuted :
    ¬ ∀ (S : Type) [MetricSpace S] [CompactSpace S], BingS S → ∀ x : S, IsContPt x → ¬ IsEndElt x → bingElt x = {x}`;
  * `exists_degenerate_interior_elt_refuted :
    ¬ ∀ (S : Type) [MetricSpace S] [CompactSpace S], BingS S → ∃ p : S, bingElt p = {p} ∧ ¬ IsEndElt p`;
  * `theorem11_hdeg_refuted`: the hypothesis `hdeg` of `theorem11_1951_of_T10`, in universe `0`,
    is the statement just refuted.
* **Q1.** `isMeagre_not_isContPt` (Fort's theorem for the element map) is **proved**.
  `isContPt_congr` is **open** (obstruction below).
* **Q2.** `exists_contPt_not_endElt` is **proved**.
* **Q3.** (a) **Refuted**, as above. (b) and (c) are answered below. `subcontinuum_of_isContPt` is
  **open**: it holds in the counterexample, but no general proof was found.
* **Q4.** `exists_degenerate_interior_elt'` is **refuted**. `theorem11_1951_of_T10'` is **open**:
  the route through Q-deg is closed.
* **Status of the batch-96 statements.**
  * `exists_degenerate_interior_elt` (`Theorem11.lean`) is **false**: it is refuted by
    `exists_degenerate_interior_elt_refuted` at `S := Org.Organ`. As the commission requires,
    `Theorem11.lean` is not edited, so its `sorry` stays. It must not be proved and should be
    regarded as refuted.
  * `theorem11_1951_of_T10` is still proved, with no `sorry`. But its hypothesis `hdeg` is false
    in universe `0` (`theorem11_hdeg_refuted`). So for `S : Type` the theorem is vacuous. It gives
    nothing towards Theorem 11.
* **Build and axioms.** `lake build HPC` passes. `Axioms97.lean` writes `axioms-batch97.txt`.
  Every proved batch-97 result uses only `propext`, `Classical.choice` and `Quot.sound`. The
  three open statements (`isContPt_congr`, `subcontinuum_of_isContPt`, `theorem11_1951_of_T10'`)
  and `exists_degenerate_interior_elt` show `sorryAx`.

**Files.**

| File | Contents |
| --- | --- |
| `HPC/Plane/Layers51.lean` | the skeleton: `IsContPt`; Fort (`isMeagre_not_isContPt`, with `MeetSet`, `isClosed_meetSet`, `bingElt_eventually_subset`); Q2; the refuted Q3, Q-deg (commented out) and their refutations; the three open statements |
| `HPC/Plane/CantorOrgan.lean` | the Cantor organ as a compact subset of `ℝ × ℝ`: weighted digit sums `lam`, `PP`, `QQ`; the embedding `psi`; `Organ`, `Phi`, the layer map `F` |
| `HPC/Plane/CantorOrganLayers.lean` | the layers `layer t = F ⁻¹' {t}`: the strands `strand (lft t)`, `strand (rgt t)`, the parametrisation `gam t` of a layer by `[0, 2]`, connectedness of the preimages of intervals |
| `HPC/Plane/CantorOrganCont.lean` | closure lemmas (a strand is a limit of strands from the left/right); good parameters; `mem_of_F_between` |
| `HPC/Plane/CantorOrganOrder.lean` | the lexicographic order `key`; subcontinua are order-convex (`ordConvex_of_continuum`); order-convex sets are connected (`isPreconnected_of_ordConvex`) |
| `HPC/Plane/CantorOrganBing.lean` | `organ_bingS`, `organ_bingElt`, `organ_bingElt_ne_singleton`, `organ_not_isEndElt`, `organ_layer_hausdorff` |
| `Axioms97.lean`, `axioms-batch97.txt` | `#print axioms` |

**Shape changes.**
* `bingElt_degenerate_of_isContPt` and `exists_degenerate_interior_elt'` are commented out because
  they are false. Their negations are stated over `S : Type` (the counterexample lives in
  `Type`).
* No existing file was edited. `Theorem11.lean` is unchanged.

## Refutation: the Cantor organ

**The space.** Start from `C × [0, 1]`, where `C` is the Cantor set. For every removed interval
`(a, b)` of `C`, identify `(a, 1)` with `(b, 1)` when the interval has odd generation, and `(a, 0)`
with `(b, 0)` when it has even generation. In Lean, Cantor space is `ℕ → Bool`. A digit sequence
`c` and a height `y` go to `psi c y = (y · P(c) + (1 − y) · Q(c), y) ∈ ℝ × ℝ`. Here `P` and `Q` are
digit sums with weights chosen so that `P(c) = P(c')` exactly when `c, c'` are the two endpoints
of an odd gap, and `Q` does the same for even gaps (`psi_eq_psi_iff`). `Organ` is the range, a
compact subset of the plane.

The map `F : Organ → [0, 1]` sends a point to the binary value `λ(c)` of its digit sequence. It
is continuous and well defined, because glued points have the same `λ`. Its fibres are the
**layers**:
* if `t` is not dyadic, the layer over `t` is a single vertical segment, `strand c`;
* if `t` is dyadic, it is two segments joined at the top or at the bottom (a "V"). This is
  `layer_eq`: `layer t = strand (lft t) ∪ strand (rgt t)`.

**`BingS` (`organ_bingS`).** Order the organ lexicographically by (layer, position in the layer).
Here "position" uses the parametrisation `gam t : [0, 2] → layer t`. Two facts carry everything:
* every subcontinuum is order-convex (`ordConvex_of_continuum`);
* every order-convex set is connected (`isPreconnected_of_ordConvex`).

The first fact rests on two lemmas:
* a subcontinuum reaching past a layer contains the corresponding strand (`strand_lft_subset`,
  `strand_rgt_subset`);
* a subcontinuum meets each layer in a connected set (`isPreconnected_inter_layer`).

From these:
* *hereditarily unicoherent*: an intersection of two order-convex sets is order-convex;
* *atriodic*: if `N ⊆ T` are continua, then `T ∖ N` has at most two order-convex pieces, below
  and above `N`, and each piece lies in a single part of any separation. So `T ∖ N` cannot have
  three mutually separated parts;
* *hereditarily decomposable*: cut a nondegenerate subcontinuum at a middle value of `F`. If `F`
  is constant on it, cut at a middle position inside the layer.

**Elements (`organ_bingElt`): `bingElt s = layer (F s)`.**
* `⊆`: preimages under `F` of small closed intervals are continua. Two nested ones around `F s`
  exclude any point of another layer.
* `⊇`: let `H` contain interiorly a continuum `H'` that contains `s` interiorly. A neighbourhood
  of a strand point meets the adjacent layers on that strand's side (`pt_mem_closure_left/right`).
  So `H'` contains the strand through `s` (`side_L'`, `side_R'`). That strand meets the other
  strand of the layer at a point of `H' ⊆ interior H`, so `H` also contains the other strand.
  At `t = 0` and `t = 1` the layer is a single strand (`lft_eq_rgt_zero`, `lft_eq_rgt_one`).

**Every element is nondegenerate (`organ_bingElt_ne_singleton`).** Each layer contains a whole
segment `strand c`.

**Interior layers are not end elements (`organ_not_isEndElt`).** If `0 < F r < 1`, the layer of
`r` separates layer `0` from layer `1`, via the open sets `F < F r` and `F > F r`.

**Continuity (`organ_layer_hausdorff`, `organ_isContPt`).** Let `c` be *good*, i.e. its digits end
in `011011…`; this is `goodC`. Then `c` is the only sequence with `λ = λ(c)`. By compactness,
sequences with `λ` close to `λ(c)` are close to `c`, so their `P` and `Q` are close to those of
`c`. Hence, at each height, points of nearby layers are close to points of `layer (λ c)`
(`dist_pt_same_height`). So the layers converge in the Hausdorff metric, and every point of
`layer (λ c)` is a continuity point of `x ↦ bingElt x`. The point `pt goodC 0` is a continuity
point, is not an end element, and has a nondegenerate element (`organ_contPt_nondegenerate`).

## Q1

**`isMeagre_not_isContPt`: proved.** The argument is a direct countable-boundary argument rather
than Fort's sets `A_n`. I did not find a form of Fort's theorem in Mathlib.

1. For `z ∈ S`, `r > 0`, let `MeetSet z r = {x | bingElt x ∩ closedBall z r ≠ ∅}`. It is closed
   (`isClosed_meetSet`), because its complement is the union of the elements contained in the
   open set `(closedBall z r)ᶜ`, which is open by `bingElt_usc`.
2. For each `n`, cover `S` by finitely many balls `ball z (1/(n+1))`.
3. Let `B` be the union, over all `n` and all chosen centres `z`, of the boundaries
   `MeetSet z r \ interior (MeetSet z r)`. These are countably many nowhere dense sets
   (`isNowhereDense_diff_interior`), so `B` is meagre.
4. If `x ∉ B`, then `x` is a continuity point. Fix `ε` and take `r < ε/4`.
   * Upper semicontinuity (`bingElt_eventually_subset`) puts `bingElt y` inside the
     `r`-thickening of `bingElt x` for `y` near `x`.
   * For each of the finitely many centres `z` with `x ∈ MeetSet z r`, `x` lies in the interior,
     so `y ∈ MeetSet z r` for `y` near `x`. Every point of `bingElt x` is within `r` of such a
     `z`, so it is within `2r` of `bingElt y`.
   * Hence `hausdorffDist (bingElt y) (bingElt x) ≤ 2r < ε`.

**`isContPt_congr`: open.** Continuity at `x` constrains only the elements of points near `x`.
Suppose an element `T` is the Hausdorff limit of the elements on one side, but the elements on the
other side converge only to a proper part `T₀` of `T`. Then points of `T ∖ closure T₀` would be
continuity points and points of `T₀` would not. I expect such a `BingS` space to exist: a Cantor
organ whose strands to the right of a good parameter have half height. I have not constructed it
in Lean, so this is a conjecture, not a result. In the organ itself the statement holds
trivially, because continuity depends only on the layer there.

## Q2

**`exists_contPt_not_endElt`: proved,** as the commission outlines:
* the two end elements (`exists_two_endElts`) are closed with empty interior
  (`bingElt_interior_eq_empty`), hence meagre;
* every end element lies in one of them (`at_most_two_endElts`);
* the non-continuity points are meagre (Q1);
* `S` is a nonempty compact metric space, hence Baire, so the union of these meagre sets is not
  all of `S` (`not_isMeagre_of_isOpen`).

## Q3

**(a) False** (refutation above). A `BingS` space can have nondegenerate elements that are
two-sided Hausdorff limits of elements. In the Cantor organ every non-dyadic layer is one.
Neither hereditary unicoherence nor atriodicity stops this. A continuous family of nondegenerate
layers over a *Cantor set* of parameters avoids the "rectangle" that a family over an interval
would give. The alternating top/bottom gluings make the space connected and irreducible without
creating a triod.

So Theorem 11 needs a route that copes with nondegenerate interior elements. Two refinements
fail:
* one-sided continuity: in the organ the continuity is two-sided;
* "the union of the nondegenerate elements is of first category": in the organ every element is
  nondegenerate, so that union is the whole space.

What remains is Bing's nondegenerate branch: condition A for `M = g'` (see batch 96).

**(b)** Here is what the batch-96 fact, hereditary decomposability and two-sided continuity give
together, at a non-dyadic layer `T` of the organ:
* every subcontinuum meeting `T` lies in `T` or contains `T`;
* `T` is an arc;
* HD holds throughout.

These properties are all consistent with `T` being nondegenerate. So no combination of them forces
degeneracy. The commission's check on the bar of `S₀` is correct: `cl C₁` meets the bar, but
neither contains nor is contained in it. So the batch-96 fact fails there, consistent with the bar
not being a continuity point. `subcontinuum_of_isContPt` itself is left **open** in general. It
holds in the organ, since subcontinua are order-convex. The general argument needs the elements
on both sides of `T` to converge to all of `T`, which `IsContPt x` does not provide (see Q1).

**(c)** One-sided continuity does not give degeneracy. Not even two-sided continuity does.

## Q4

* `exists_degenerate_interior_elt'`: **refuted** (`exists_degenerate_interior_elt_refuted`).
* `theorem11_1951_of_T10'`: **open**. The assembly through Q3 is impossible. The hypothesis
  `hdeg` of `theorem11_1951_of_T10` is false (`theorem11_hdeg_refuted`). The Cantor organ is a
  `BingS` space for which any proof must handle a nondegenerate interior element.

## Next

Q3 is refuted, so this is the commission's "Kuratowski's route" case, but sharpened: in the organ
*no* element is degenerate. So Theorem 11 cannot go through any degenerate element. It needs
Bing's nondegenerate branch: a point `p'` satisfying condition A for `M = g'`, plus a chain
construction that works with a nondegenerate `g'`. The organ is a good test space for that
branch. If Bing's Theorem 11 holds it must be snake-like, since it is `BingS`. Its elements are
arcs and V's.
