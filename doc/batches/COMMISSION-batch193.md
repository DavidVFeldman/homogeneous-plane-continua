# Commission: batch 193 — H–O Theorem 1, I: Theorems 4 and 8; plane graphs; `HOThm20`

**Go!** This batch runs on top of the batch-192 work. Four files come with it, as separate uploads:

* `COMMISSION-batch193.md`: this text, also pasted into the prompt.
* `HO16A.lean`: the skeleton.
  * Save it as `HPC/HO16/HO16A.lean` (a new directory). You may split it under `HPC/HO16/`.
  * Add `import HPC.HO16.HO16A` at the end of `HPC.lean`.
* `hoehn-oversteegen2016.pdf`: save as `doc/sources/hoehn-oversteegen2016.pdf`.
* `krasinkiewicz-minc1977.pdf`: save as `doc/sources/krasinkiewicz-minc1977.pdf`. Its first page is
  an interlibrary-loan cover sheet; the paper is pp. 675–680 of the Bulletin.

Page numbers below are the journal's: Hoehn–Oversteegen (H–O), Acta Math. 216 (2016), 177–216
(PDF page `n` is journal page `176 + n`); Krasinkiewicz–Minc (K–M), Bull. Acad. Polon. Sci. 25
(1977), 675–680.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule).** For every theorem whose hypotheses include a named `Prop` or a
  structure, the report gives a note with the two checks:
  1. the hypothesis is not refuted by a short argument from the set-up;
  2. it is not equivalent to the conclusion it is used for, unless the printed argument is a proof
     by contradiction.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "H–O Theorem 1, I (batch 193)");
  * `README.md`;
  * `LEDGER.md`: a new section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977";
  * `OPEN.md`;
  * `doc/notes/ho16.md` (new).

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 192

* **Delivery.** The download was current. Keep publishing the tarball and manifest (§11.4).
* **Copies.** The skeleton and commission are byte-identical to what I sent.
* **Audit.** `axioms.txt` has 2658 lines (2595 + 63 added, none removed), with `sorryAx` in none.
  * 62 of the new theorems use exactly the three standard axioms; `exists_between_three` uses
    `propext` only.
  * The five new files contain no `sorry`, `admit` or `axiom` outside comments. `OT82A.lean`
    changed only in its §7 comment.
  * Every fixed statement matches the skeleton. Dropping `hr` from `parity_flip_vertical_edge` is
    a generalization and is accepted, as are the shapes of the three "shape left to you" items.
* **Results.** `theoremC : TheoremC` with no hypotheses. Theorems A, B and C of H–O are now all in
  the main build. The quadrilateral proof of `parity_eq_of_perturb` is neater than the vertex-by-
  vertex one I proposed.
* **Ledger.** OT.8–OT.13 adopted. I agree that the count stays at sixteen: the counting rule waits
  for the printed statement of Theorem 3.2 to be settled.

## 1. The plan

**What the classification needs from H–O Theorem 1.** H–O p. 180: "It follows immediately from
Theorems B and C above and Theorem 1 that every indecomposable non-degenerate homogeneous plane
continuum is a pseudo-arc." Only one direction of Theorem 1 is used, and only for plane continua:
a non-degenerate plane continuum that is hereditarily indecomposable and has span zero is
snake-like (then it is a pseudo-arc by the definition `IsPseudoArc`, and `pseudoArc_unique`
identifies it).

**H–O's proof of that direction (p. 211).** Fix `ε`. Theorem 4 gives a `δ` such that, for any
graph `G` and arc `I` with ends `p`, `q` within `δ` of `X`, the set
`{(x, y) ∈ G × (I \ {p, q}) : d(x, y) < ε/6}` separates the two ends. A tree `T` with a map
`f : X → T` close to the identity comes from [31] (span zero ⇒ tree-like). Theorem 20 gives
`h : X → M` with `π₁ ∘ h` close to `f`; then `π₂ ∘ h` is an `ε`-map to the arc.

**The route here differs in three places** (my readings, to be recorded; §9):
* **Graphs, not trees.** Theorems 4, 15 and 20 are stated for graphs; the tree `T` is used only
  as a graph. For a hereditarily indecomposable plane continuum, which has empty interior, a fine
  grid and radial projections in its squares give the graph and the map (§6). Tree-likeness is not
  needed. (H–O cite [31] for it on pp. 191 and 211, a research announcement whose Lemma 5 and
  Theorem 6 carry no proof; on p. 212 they cite [46], Oversteegen–Tymchatyn, *On span and weakly
  chainable continua*, Fund. Math. 122 (1984), for the stronger "any continuum with surjective
  semispan zero is tree-like". Neither is formalized; the grid avoids both.)
* **Paths, not arcs.** The arc `I` is replaced by a continuous `γ : ℝ → E` and `I` by `[0, 1]`;
  the `ε`-map is the `t`-coordinate of `h`. No arc is needed.
* **Theorem 20 enters as a named `Prop`.** `HOThm20` is the forward direction of Theorem 20 for
  PL graphs (§2). It is proved in later batches (§8). This batch proves everything else on the
  route, so that the dependency map of the target has `HOThm20` as its only open input:
  ```
  homeomorph_pseudoArc_of_indec_homogeneous :
    HOThm20 → (M indecomposable homogeneous non-degenerate plane continuum) → M ≃ₜ pseudo-arc
  ```

**This batch.**
1. Definitions: PL graphs, fans, separation, `HOThm20` (§2).
2. K–M Lemma 2 for hereditarily indecomposable compacta (§3).
3. The core of H–O Theorem 8, (1) ⇒ (2): the decomposition and the map `h`, before any fold (§4).
4. H–O Theorem 4, path form (§5).
5. Plane approximations: empty interior, grid graphs, paths (§6).
6. The assembly (§7).

§4 is not on the dependency map of the target; it is the first piece of `HOThm20` and uses §3.
If the whole does not fit, do §2, §5, §6, §7 first.

Notation: `Pt = ℝ × ℝ` with the sup metric (a normed space; `Pt × ℝ` likewise). `thickening δ X`
is Mathlib's open `δ`-neighbourhood. `IsHereditarilyIndecomposable`, `IsSnakeLike`,
`IsPseudoArc`, `pseudoArc_unique`, `isSnakeLike_univ_of_epsMap` are in `HPC.Plane`;
`HOSpanZero`, `theoremC`, `plPath`, `exists_eps_chain` in `HPC.Span`; `hagopian76_theorem1` in
`HPC.Hagopian`; `IsHomogeneous`, `IsDecomposableSpace` in `HPC.Jones`. The cut-wire theorem is
`HPC.Plane.exists_split_of_no_continuum` (`Ingram68Star.lean`); Hausdorff limits of continua are
in `HPC/Plane/Most51.lean` (`Cont`, `Most.isConnected_of_tendsto`).

## 2. Definitions

1. **`IsPLGraph G`** (`G : Set E`, `E` a real normed space): a finite set `S` of pairs, each a
   nondegenerate segment `[s.1, s.2]`, with `G` their union, and two different pairs meeting at most
   in common endpoints. (H–O p. 183: "A graph is a space which is the union of finitely many arcs
   which intersect at most in endpoints"; p. 184: "(not necessarily connected) graph". The PL form
   is the one the later batches will use: subdivision does not change the set.) Two pairs
   `(a, b)`, `(b, a)` cannot both occur.
2. **`IsFanAt A y r Y`**: `Y = {y} ∪ ⋃ₖ [y, z k]` for finitely many `z k ≠ y`, the segments
   pairwise meeting only at `y`, `Y ⊆ A`, `Y` a neighbourhood of `y` in `A`, `diam Y < r`. (H–O
   p. 187: "a finite fan `Yⱼⁱ ⊂ G₂` (meaning `Yⱼⁱ` is the union of finitely many arcs, each having
   `yⱼⁱ` as one endpoint, and which are otherwise pairwise disjoint) such that `Yⱼⁱ` is the closure
   of an open neighborhood `Oⱼⁱ` of `yⱼⁱ` in `G₂`, and the diameter of `Yⱼⁱ` is less than `ε`".)
3. **`SeparatesIn Y M P Q`**: two open sets cover `Y \ M`, are disjoint on `Y \ M`, and contain
   `P` and `Q` respectively.
4. **`HOThm20`**: for every hereditarily indecomposable compact metric `X`, every PL graph `G` in
   a real normed space `E`, every continuous `f : X → E` with values in `G`, every
   `M ⊆ G × (0, 1)` separating `G × {0}` from `G × {1}` in `G × [0, 1]`, every open `U ⊇ M` and
   every `ε > 0`, there is a continuous `h : X → E × ℝ` with values in `U ∩ (G × [0, 1])` and
   `dist (f x) (h x).1 < ε`. (H–O Theorem 20, "only if"; their `U` is open in `G × [0, 1]`, which
   is the same thing.)

Lemmas (all expected short):
* `IsPLGraph.isCompact`.
* `IsPLGraph.exists_fan`: every point `y` of a PL graph has fans of every diameter `r > 0`. The
  segments through `y` are either several segments ending at `y` (take initial pieces `[y, y + t(w −
  y)]`) or one segment with `y` inside (take two halves); the other segments are at positive
  distance from `y`; a point of `G` within `ρ` of `y` on a segment `[y, w]` lies on `[y, z]` once
  `ρ ≤ ‖z − y‖`.
* `separatesIn_of_closed`: if `Y \ M ⊆ R₀ ∪ R₁` with `R₀`, `R₁` closed and disjoint, `P ⊆ R₀`,
  `Q ⊆ R₁`, then `SeparatesIn Y M P Q` (take `U = R₁ᶜ`, `V = R₀ᶜ`).

## 3. Krasinkiewicz–Minc, Lemma 2

**Statement** (`km77_lemma2`; H–O p. 187 quote it for continua and remark: "one can replace
'hereditarily indecomposable continuum' with 'hereditarily indecomposable compactum' in this
result; the proof is unchanged"). Let `X` be a hereditarily indecomposable compact metric space,
`A`, `B` disjoint closed sets, `U ⊇ A` and `V ⊇ B` open. Then there are closed `X₁, X₂, X₃` with
`X₁ ∪ X₂ ∪ X₃ = X`, `A ⊆ X₁`, `B ⊆ X₃`, `X₁ ∩ X₃ = ∅`, `X₁ ∩ X₂ ⊆ V`, `X₂ ∩ X₃ ⊆ U`.

K–M's names: `F₀ = X₁`, `F₁ = X₂`, `F₂ = X₃` ("(X, A, B) is crooked between U and V").

**Proof** (K–M p. 676, with Lemma 1 replaced by hereditary indecomposability):
1. Take open `U' ⊇ A`, `V' ⊇ B` with `cl U' ⊆ U`, `cl V' ⊆ V`, `cl U' ∩ cl V' = ∅`.
2. `A*` = union of the components of `X \ V'` meeting `A`; `B*` = union of the components of
   `X \ U'` meeting `B`. Both are closed (in a compact space, the union of the components of a
   closed set `K` meeting a closed set `C ⊆ K` is closed: a component missing `C` lies in a set
   clopen in `K` missing `C`; `HPC.Jones.exists_clopen_of_connectedComponentIn_disjoint`).
3. `A* ∩ B* = ∅`: for `p` in both, let `C₁` be the component of `p` in `X \ V'` and `C₂` that in
   `X \ U'`. `C₁` meets `A` and misses `B`; `C₂` meets `B` and misses `A`; `p ∈ C₁ ∩ C₂`. So
   `C₁ ∪ C₂` is a continuum and `C₁`, `C₂` are proper subcontinua covering it: it is decomposable,
   against hereditary indecomposability. (K–M: Lemma 1 gives a decomposable subcontinuum
   irreducible between `A` and `B`; here the decomposable `C₁ ∪ C₂` suffices.)
4. Cut wire in `X \ V'` between `A*` and `B* \ V'` (a continuum in `X \ V'` meeting `A*` lies in a
   component meeting `A`, so it misses `B*`): `X \ V' = D₁ ∪ D₂`, closed, disjoint, `A* ⊆ D₁`,
   `B* \ V' ⊆ D₂`. Then `B* ∩ D₁ = ∅`.
5. Cut wire in `X \ U'` between `B*` and `D₁ \ U'`: `X \ U' = E₁ ∪ E₂`, closed, disjoint,
   `B* ⊆ E₁`, `D₁ \ U' ⊆ E₂`.
6. `X₁ = D₁ ∪ (E₂ ∩ cl V')`, `X₂ = (D₂ ∩ E₂) ∪ (D₂ ∩ cl U') ∪ (E₂ ∩ cl V')`,
   `X₃ = E₁ ∪ (D₂ ∩ cl U')`. Checks (K–M's): `U' ⊆ D₁ ∪ (D₂ ∩ U')` and `V' ⊆ E₁ ∪ (E₂ ∩ V')`
   give the cover; `X₁ ∩ X₂ ⊆ cl V'`; `X₂ ∩ X₃ ⊆ cl U'`;
   `X₁ ∩ X₃ = D₁ ∩ E₁ = (D₁ \ U') ∩ E₁ ⊆ E₂ ∩ E₁ = ∅` (the other three intersections are empty
   because `D₁ ∩ D₂ = ∅`, `E₁ ∩ E₂ = ∅`, `cl U' ∩ cl V' = ∅`).

## 4. H–O Theorem 8, (1) ⇒ (2): the core

H–O's proof (pp. 187–189) builds, from `f : X → G` and the three sets `Gᵢ` of a simple fold, a map
`h : X → G` close to `f` and a closed cover `X₁, X₂, X₃` adapted to the `Gᵢ`; the lift to the fold
is then `(φ|Fᵢ)⁻¹ ∘ h` on `Xᵢ`. This item is that construction, stated without folds, so that the
fold representation can be fixed later.

**Statement** (`ho16_theorem8_core`). `X` hereditarily indecomposable compact metric; `E` a real
normed space; `G₁, G₃ ⊆ E` closed, `G = G₁ ∪ G₃`, `G₂ = G₁ ∩ G₃`, and
`cl(G₁ \ G₂) ∩ cl(G₃ \ G₂) = ∅` (H–O's (F2), (F3)). Write `B₁ = cl(G₁ \ G₂) ∩ G₂` and
`B₃ = cl(G₃ \ G₂) ∩ G₂` (these are H–O's `∂(G₁ \ G₂)` and `∂(G₃ \ G₂)`, the frontiers in `G`).
Assume `B₁`, `B₃` finite and that every point of `B₁ ∪ B₃` has fans in `G₂` of every diameter.
Then for continuous `f : X → G` and `ε > 0` there are a continuous `h : X → E` and closed
`X₁, X₂, X₃` with:
* `dist (f x) (h x) < ε`;
* `X₁ ∪ X₂ ∪ X₃ = X`, `X₁ ∩ X₃ = ∅`;
* `h(Xᵢ) ⊆ Gᵢ` (`i = 1, 2, 3`);
* `h(X₁ ∩ X₂) ⊆ B₃` and `h(X₂ ∩ X₃) ⊆ B₁`.

(H–O: "h(X₁∩X₂) ⊂ ∂(G₃\G₂) = ∂G₁" and "h(X₂∩X₃) ⊂ ∂(G₁\G₂) = ∂G₃".)

**Proof**, H–O's, with the details they leave out marked (†):
1. **Fans.** `B₁ ∪ B₃` is finite and `B₁ ∩ B₃ = ∅`. Choose for each `y ∈ B₁ ∪ B₃` a fan `Y_y` in
   `G₂` with `diam Y_y < ε`, the fans pairwise disjoint (†: H–O do not say so; it is needed in
   step 5).
2. **The sets `Kᵢ`.** `K₁ = f⁻¹(cl(G₁ \ G₂))`, `K₃ = f⁻¹(cl(G₃ \ G₂))`; closed and disjoint.
3. **Neighbourhoods.** Every `p ∈ cl(G₁ \ G₂)` has a ball `Bₚ` with
   `G ∩ Bₚ ⊆ cl(G₁ \ G₂) ∪ Y_p` if `p ∈ B₁`, and `G ∩ Bₚ ⊆ G₁ \ G₂` if `p ∉ G₂`. (For `p ∉ G₂`:
   `p ∈ G₁ \ G₃` and `G₃` is closed. For `p ∈ B₁`: `p ∉ cl(G₃ \ G₂)` by (F3), and `Y_p` is a
   neighbourhood of `p` in `G₂`.) Take `U₁` open with `K₁ ⊆ U₁ ⊆ f⁻¹(⋃ₚ Bₚ)`; likewise `U₃`; and
   shrink so that `cl U₁ ∩ cl U₃ = ∅` (convenient; with disjoint fans `U₁ ∩ U₃ = ∅` already
   follows, since a fan at a point of `B₃` misses `cl(G₁ \ G₂)`, and that is all step 5 uses).
   Then `f(U₁ \ K₁) ⊆ ⋃_{y ∈ B₁} (Y_y \ {y})`: such a point is in some `Y_p` with `p ∈ B₁`, and
   `f⁻¹(y) ⊆ K₁`.
4. **K–M** (§3) with `A = K₁`, `B = K₃`, `U = U₁`, `V = U₃`: closed `X₁, X₂, X₃` with
   `K₁ ⊆ X₁`, `K₃ ⊆ X₃`, `X₁ ∩ X₃ = ∅`, `X₁ ∩ X₂ ⊆ U₃`, `X₂ ∩ X₃ ⊆ U₁`.
5. **The map near `K₁`.** `W₁ = (X₂ ∪ X₃) ∩ U₁ = U₁ \ X₁` (because `X₁ ∩ X₂ ⊆ U₃` misses `U₁`)
   is open and misses `X₁ ⊇ K₁`, so
   `f(W₁) ⊆ ⋃_{y ∈ B₁} (Y_y \ {y})`. This set is the disjoint union of the half-open segments
   `(y, z]` of the fans, each closed in it; so `L' = f⁻¹((y, z]) ∩ W₁` is clopen in `W₁` for each
   segment `[y, z]`. On `cl L'`:
   * `cl L' ⊆ (X₂ ∪ X₃) ∩ cl U₁`, `f(cl L') ⊆ [y, z]`, and `cl L'` misses `X₁` (a point of
     `X₁ ∩ (X₂ ∪ X₃) ∩ cl U₁` is in `X₁ ∩ X₂ ⊆ U₃`, which misses `cl U₁`);
   * `cl L' \ L' ⊆ fr U₁`, and `X₂ ∩ X₃ ⊆ U₁` misses `fr U₁`.

   So `L'` is open in `X` and its frontier is `cl L' ∩ fr U₁` (H–O's `∂L′`, literally).
   Tietze: a continuous `h_{L'} : cl L' → [y, z]` with `h_{L'} = f` on `cl L' ∩ fr U₁` and
   `h_{L'} = y` on `X₂ ∩ X₃ ∩ cl L'` (parametrize `[y, z]` by `t ↦ y + t • (z − y)` and extend the
   real parameter). Distinct `L'` have
   disjoint closures (their `f`-values lie in disjoint `(y, z]`; `f ≠ y` on `cl L'` because
   `f⁻¹(y) ⊆ K₁ ⊆ X₁`).
6. **The same near `K₃`**, with `W₃ = (X₁ ∪ X₂) ∩ U₃` and value `y` on `X₁ ∩ X₂ ∩ cl L'`.
7. **Paste.** `h = f` on `A = (X₁ \ U₃) ∪ (X₂ \ (U₁ ∪ U₃)) ∪ (X₃ \ U₁)` (closed), `h = h_{L'}` on
   each `cl L'`. The pieces are finitely many closed sets covering `X`; they agree on overlaps
   (`A ∩ cl L' ⊆ fr U₁`, where `h_{L'} = f`).
8. **Checks.**
   * `dist (f x) (h x) < ε`: on `cl L'` both values lie in one fan.
   * `h(X₁) ⊆ G₁`: on `X₁ \ U₃`, `x ∉ X₃ ⊇ K₃`, so `f x ∉ G₃ \ G₂`, so `f x ∈ G₁`; on `X₁ ∩ U₃`
     the value is in a fan in `G₂ ⊆ G₁`. Likewise `h(X₃) ⊆ G₃`.
   * `h(X₂) ⊆ G₂`: off `U₁ ∪ U₃`, `f x ∉ cl(G₁ \ G₂) ∪ cl(G₃ \ G₂)`, so `f x ∈ G₂`; inside, fans.
   * `h(X₂ ∩ X₃) ⊆ B₁`: `X₂ ∩ X₃ ⊆ W₁`, so each such `x` lies in some `L'` where `h = y ∈ B₁`.
     Likewise `h(X₁ ∩ X₂) ⊆ B₃`.

## 5. H–O Theorem 4, path form

**Statement** (`ho16_theorem4`). `E` a proper metric space, `X ⊆ E` compact with
`HOSpanZero X`, `ε > 0`. There is `δ > 0` such that for every compact `G ⊆ thickening δ X` and
every continuous `γ : ℝ → E` with `γ[0, 1] ⊆ thickening δ X` and `X ⊆ thickening δ (γ[0, 1])`,
the set `M = {(x, t) : x ∈ G, 0 < t < 1, dist x (γ t) < ε}` separates `G × {0}` from `G × {1}` in
`G × [0, 1]`.

Changes from H–O (record): the arc `I` with ends `p`, `q` becomes `γ` on `[0, 1]`; `I \ {p, q}`
becomes `(0, 1)`; of `G` only `G ⊆ thickening δ X` is assumed (the other half of the Hausdorff
condition is not used); `X` need not be connected; `E` is any proper metric space instead of the
Hilbert cube.

**Compact ambient spaces.** `exists_split_of_no_continuum` and `HPC.Hagopian.limsup_isPreconnected`
assume `[CompactSpace S]`, and `E × ℝ`, `E × E` are not compact. Apply the cut wire in the subtype
`↥(Gₙ ×ˢ Icc 0 1)` (closed, so the pieces carry back as closed sets), and take the limit inside
`K × K` as below. A template for the limit is `HPC/Plane/Most51.lean`, lines 196–232
(`NonemptyCompacts.isCompact_subsets_of_isCompact`, `tendsto_subseq`, `Most.subset_of_tendsto`,
`Most.mem_of_tendsto`, `Most.tendsto_infDist`).

**Proof** (H–O p. 184). Suppose not, for some `ε`: for each `n` there are `Gₙ`, `γₙ` with `δ =
1/(n+1)` and `Mₙ` not separating.
1. **A continuum in `Dₙ = {(x, t) ∈ Gₙ × [0, 1] : ε ≤ dist x (γₙ t)}`** (compact) meeting both
   rows `t = 0` and `t = 1`: otherwise the cut-wire theorem splits `Dₙ = D⁰ ∪ D¹`, closed and
   disjoint, with the row-0 points of `Dₙ` in `D⁰` and the row-1 points in `D¹`; then
   `R₀ = D⁰ ∪ Gₙ × {0}` and `R₁ = D¹ ∪ Gₙ × {1}` are disjoint closed sets covering
   `(Gₙ × [0, 1]) \ Mₙ`, and `separatesIn_of_closed` gives a contradiction. (H–O: "This would mean
   (see e.g. [44, Theorem 5.2]) that … there is a continuum `Zₙ` … such that `d(x, y) ≥ ε` for all
   `(x, y) ∈ Zₙ`"; the cut wire is applied to `Dₙ` itself, so the end rows are not used.) Call the
   continuum `Zₙ`; its second projection is `[0, 1]`.
2. `Wₙ = {(x, γₙ t) : (x, t) ∈ Zₙ} ⊆ E × E` is a continuum with `dist ≥ ε` on it, first
   coordinates in `Gₙ`, second coordinates exactly `γₙ[0, 1]`.
3. **A limit.** All `Wₙ` lie in `K × K`, `K = cl(thickening 1 X)`, compact (proper space). Pass to
   a subsequence converging in the Hausdorff metric (nonempty compact subsets of a compact metric
   space form a compact space), with limit `W`: a continuum (`Most.isConnected_of_tendsto`, or the
   upper-limit lemma `HPC.Hagopian.limsup_isPreconnected`), `dist ≥ ε` on `W`, first coordinates
   in `X`, second coordinates exactly `X` (each `x ∈ X` is within `1/(n+1)` of some `γₙ tₙ`).
4. `Z = {p : X × X | (p.1, p.2) ∈ W}` is a subcontinuum of `X × X` with `π₁ Z ⊆ π₂ Z = X` missing
   the diagonal, against `HOSpanZero X`.

## 6. Plane approximations

1. **`interior_eq_empty_of_hi`**: if `M ⊆ Pt` and `univ : Set M` is hereditarily indecomposable,
   then `interior M = ∅`. A point of the interior has a closed sup-ball `Q ⊆ M`; `Q` is the union
   of its left and right closed halves, two proper subcontinua; its preimage in `M` is a
   decomposable subcontinuum.
2. **`exists_plGraph_approx`**: for compact `X ⊆ Pt` with empty interior and `δ > 0` there are a
   PL graph `G ⊆ thickening δ X` and `f : Pt → Pt`, continuous on `X`, with `f x ∈ G` and
   `dist (f x) x < δ` on `X`.
   * Grid of mesh `η = δ/2`: squares `Q = [iη, (i+1)η] × [jη, (j+1)η]`; let `𝒬` be the finite set
     of those meeting `X`.
   * For `Q ∈ 𝒬` choose `c_Q ∈ interior Q \ X` (empty interior of `X`).
   * Choose `c_Q` for every grid square (index the squares by `ℤ × ℤ`), so that `f` is defined on
     all of `Pt` without a dependent choice; only the squares meeting `X` matter.
   * Radial projection from `c_Q` onto the frontier of `Q = [p₁, q₁] × [p₂, q₂]`:
     `r_Q x = c + (μ (x − c))⁻¹ • (x − c)` with
     `μ(v) = max(v.1/(q₁ − c.1), −v.1/(c.1 − p₁), v.2/(q₂ − c.2), −v.2/(c.2 − p₂))`, positive and
     continuous for `v ≠ 0`, with `μ = 1` exactly on the frontier of `Q`; so `r_Q` is the identity
     there.
   * `f = r_Q` on `X ∩ Q`. Two grid squares meet only in their frontiers, where both projections
     are the identity; finitely many closed pieces, so `f` is continuous on `X`.
   * `G` = union of the edges of the squares in `𝒬`, each edge listed once with its lower-left end
     first. Distinct grid edges meet at most in a common end. `G ⊆ thickening δ X` and
     `dist (f x) x ≤ η < δ` because each square has sup-diameter `η` and meets `X`.
3. **`exists_path_approx`**: for compact connected `X ⊆ Pt` and `δ > 0` there is a continuous
   `γ : ℝ → Pt` with `γ[0, 1] ⊆ thickening δ X` and `X ⊆ thickening δ (γ[0, 1])`. Take a finite
   `δ/2`-net of `X`, join its points in turn by `δ/2`-chains in `X` (`exists_eps_chain`), and let
   `γ` be `plPath` through the resulting list (repeat a point if the list has one entry). Each
   segment has both ends in `X` and length `< δ/2`.

## 7. The assembly

1. **`ho16_theorem1_plane (h20 : HOThm20) (M : Set Pt) [CompactSpace M] [ConnectedSpace M]`**,
   with `univ : Set M` hereditarily indecomposable and `HOSpanZero M`: `IsSnakeLike (univ : Set M)`.
   Given `ε > 0`:
   1. §5 with `X = M` and `ε/6` gives `δ₀`; put `δ = min δ₀ (ε/6)`.
   2. §6.1, §6.2 with `δ`: a PL graph `G ⊆ thickening δ M` and `f`; §6.3: a path `γ`.
   3. §5 gives `SeparatesIn (G × [0, 1]) M' (G × {0}) (G × {1})` for
      `M' = {(x, t) : x ∈ G, 0 < t < 1, dist x (γ t) < ε/6}`.
   4. `U = {(x, t) : 0 < t < 1, dist x (γ t) < ε/6}` is open and contains `M'`.
   5. `h20` with `X = M`, `f ∘ coe`, `M'`, `U`, `ε/6`: a continuous `h`.
   6. `ψ = Prod.snd ∘ h : M → ℝ`. If `ψ x = ψ x' = t`, then
      `dist x (γ t) ≤ dist x (f x) + dist (f x) (h x).1 + dist (h x).1 (γ t) < δ + ε/6 + ε/6 ≤ ε/2`,
      and likewise for `x'`; so `dist x x' < ε`.
   7. `isSnakeLike_univ_of_epsMap`.
2. **`isPseudoArc_of_indec_homogeneous`**: with `IsHomogeneous M`, `¬ IsDecomposableSpace M` and
   `(univ : Set M).Nontrivial`: `IsPseudoArc (univ : Set M)`, from §7.1,
   `HPC.Hagopian.hagopian76_theorem1` (Theorem B) and `HPC.Span.theoremC` (Theorem C).
3. **`homeomorph_pseudoArc_of_indec_homogeneous`**: the same hypotheses give `M₀ : Set Pt` with
   `IsPseudoArc M₀` and `Nonempty (M ≃ₜ M₀)` (`pseudoArc_unique`, `Homeomorph.Set.univ`).

## 8. Later batches (for information; not commissioned)

The route I intend for `HOThm20`, following H–O §§4–7. Comments on it are welcome in the report.
* **Folds as sets.** A simple fold over `G` with sets `G₁, G₂, G₃` is realized inside `E × ℝ` as
  `F = graph(h₁|G₁) ∪ graph(1|G₂) ∪ graph(h₃|G₃)`, with `h₁ ≤ 1 ≤ h₃`, `h₁ = 1` exactly on `∂G₁`,
  `h₃ = 1` exactly on `∂G₃`, both linear on the segments of a subdivision; `φ` is the first
  projection. This satisfies (F1)–(F5) and avoids quotients; H–O's uniqueness remark (p. 186)
  makes it no loss. `F` is again a PL graph, in `E × ℝ`, so the induction runs over normed spaces.
* **Theorem 8 for folds** from §4 here: `g = (x ↦ (h x, height on Fᵢ))` on `Xᵢ`.
* Lemma 6, Proposition 7, Definition 9, Propositions 10–11; straight sets, stairwells and broken
  stairwells (Definitions 12, 13, 16); Proposition 17; Lemma 18; Proposition 19.
* **Theorem 15 without Claim 15.1.** H–O: "We leave it to the reader to show that there exists a
  set M′ having properties (1), (3), (5), and (6)". Instead: a sign function `u` (negative on the
  part of `G × [0, 1] \ U` on the `0` side, positive on the other), a generic piecewise linear
  approximation on a triangulation of `G × [0, 1]`, its zero set (a PL separator in `U` with
  finitely many folds, none over a vertex), then H–O's zig-zags (the three pieces of a zig-zag may
  lie on one curve, since sheets of a stairwell may overlap).
* Theorem 20, forward direction: `ho16_theorem20 : HOThm20`.

## 9. Places to check (ledger)

Open the section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977" in `LEDGER.md`, quoting the
printed sentences (check each against `doc/sources/hoehn-oversteegen2016.pdf`):
1. **Theorem 1, p. 211.** Restated as "A continuum X is homeomorphic to the pseudo-arc if and only
   if X is hereditarily indecomposable and has span zero." The statement on p. 180 has "A
   non-degenerate continuum". Without it the restatement is false: a one-point continuum is
   hereditarily indecomposable and has span zero. A misprint.
2. **[31] for tree-likeness (pp. 191 and 211).** "Because X has span zero, it is tree-like [31]"
   and "by [31] we have that X is tree-like". [31] is a research announcement (Topology Proc. 4,
   631–633): "A complete version will be published elsewhere"; its Lemma 5 and Theorem 6 have no
   proof there, and its Corollary 10 ("If X is a continuum and σ(X) = 0, then X is tree-like") is
   obtained on p. 633 from Corollary 9 with [4], [3] and [1] of its own list. On p. 212 H–O cite
   [46] (Oversteegen–Tymchatyn 1984) for the stronger "any continuum with surjective semispan zero
   is tree-like". Record: the citation on pp. 191 and 211 is to an announcement without proofs, and
   p. 212 supplies a published reference; neither is used on this route (a graph suffices, §1;
   plane continua get graphs from §6).
3. **Theorem 4's proof, p. 184.** Record that the cut wire is to be applied to
   `{(x, y) : d(x, y) ≥ ε}` (§5, step 1); with that reading the printed step is right. (The
   compactness of the hyperspace used in "accumulates on a continuum" is stated on p. 183.)
4. **Theorem 8's proof, pp. 187–189**: the fans must be pairwise disjoint (marked (†) in §4; not
   said). With that, `U₁ ∩ U₃ = ∅` follows from H–O's choice of the `Uᵢ`; `W₁ = U₁ \ X₁` is open, so
   `∂L′` has its literal meaning; and "`f(cl(Uᵢ \ Kᵢ)) ⊂ ⋃ⱼ Oⱼⁱ`" holds because a frontier point of
   `Kᵢ` maps to a frontier point of `cl(Gᵢ \ G₂)`, one of the `yⱼⁱ`. A gap in exposition; not
   counted.
5. **Theorem 8, (3) ⇒ (1), p. 189** (not on the route): "By [24] it suffices to show that X =
   X₁∪X₂∪X₃ where … X₁∩X₂ ⊂ U, and X₂∩X₃ ⊂ V", while the proof then shows "X₁∩X₂ ⊂ V" and
   "X₂∩X₃ ⊂ U", which is the form of [24] quoted on p. 187. `U` and `V` are interchanged in the
   first sentence. A misprint: the printed condition holds in every compactum (take `X₂ = X` and
   for `X₁`, `X₃` closed neighbourhoods of `A`, `B` inside `U`, `V` with disjoint closures), so it
   cannot be the criterion.
6. **K–M Lemma 2 (p. 676).** The proof is correct; for hereditarily indecomposable `X`, Lemma 1 is
   not needed (§3, step 3).
7. **Proof of Theorem 1, p. 211: "It follows that d_H(X,T)<δ."** From `d_sup(f, id_X) < δ` only
   `X ⊆ T_δ` and `f(X) ⊆ X_δ` follow; points of `T` off `f(X)` may be far from `X`, and Theorem 4
   needs both halves. Repair: replace `T` by `f(X)` (a subcontinuum of a tree, hence a tree). This
   route avoids it (only `G ⊆ thickening δ X` is needed, and §6 gives it). An unargued step.
8. **Theorem 1′, p. 212** ("A continuum X is homeomorphic to the pseudo-arc if and only if X is
   hereditarily indecomposable and has surjective semispan zero") has the defect of item 1: false
   for a one-point continuum.

Further candidates, for the batches of §8 (no need to check now; I will carry them in my ledger):
Lemma 6 ("The proofs of these properties are left to the reader", p. 185); "It is straightforward
to see" (p. 186) and "It is straightforward to check" (Proposition 7); the observations after
Definition 9; "Clearly G₁, G₂, and G₃ are all regular" (Proposition 11); Claim 15.1 (p. 195);
"for each point a ∈ Z′, the set M′∩{a}⋆ contains an odd number of points" (p. 196); "clearly S
irreducibly separates … because M′ does" (p. 197); "(S3) and (S5) are immediate from the
construction" (p. 198); the component `K` of `π(P₂)` on p. 209; "We further assume that the
numbers εᵢ are chosen small enough so that h(X)⊂U" (p. 210; redundant, since `h(X) ⊆ S ⊆ U`).
Misprints: "((φₙ)⋆∘…∘(φ₁)⋆)⁻¹(S)" (p. 209; the maps compose as `(φ₁)⋆∘…∘(φₙ)⋆`, as on p. 210);
"C₁ and C₂ are arcs which both have x as an endpoint" (p. 195, for `(x, y)`); "Since aᵢ ∈ C"
(p. 198, for `a_p`); "E(S″) ⊂ (F₁∩F₂)⋆ since S″ ⊂ (F₁∩F₂)⋆" (p. 202, for `F₁ ∪ F₂`).

## 10. Order

§2, then §3 and §5 and §6 (independent), then §4 (uses §3) and §7 (uses §5, §6).

## 11. Deliverables

1. **The items of §2–§7.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch193.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. **`LEDGER.md`:** §9.
3. **Notes:** `doc/notes/ho16.md`: the route of §1 and §8 in a few paragraphs, and what this batch
   proved.
4. **Publish the changes, as in batch 192.** At the end of the run:
   * create `doc/batches/batch193-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch193-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes (in particular for `HOThm20` as a hypothesis in §7);
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `homeomorph_pseudoArc_of_indec_homogeneous`, with every open input
     marked (`HOThm20` should be the only one);
   * what the classification now has.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`.
   * Nothing is left at the root.
