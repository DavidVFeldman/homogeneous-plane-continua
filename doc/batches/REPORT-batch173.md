Commission read: `doc/batches/COMMISSION-batch173.md` ("Commission: batch 173 — Part E, Hagopian 1976 XVIII: Theorem 1 — `Property3End` by descent; pockets; the ends of crossing components; T15–T17").

# Report, batch 173

## 0. Summary

* **A (Property 3 by descent): proved.** Property 3 holds unconditionally, for every extension `G`
  of `E` away from `k⁻¹(0)` and every layer `d⁻¹(v)` with `v < 1`:
  * `hagopian76_property3`: the conclusion of batch 172's `hagopian76_property3_of_end`, without the
    hypothesis `Property3End` and without `0 < v`;
  * `hagopian76_property3_domain`: Hagopian's form, a connected set over `D` whose closure meets
    both side segments.

  The route is the commission's (§1), with three changes:
  1. The set `T` is defined by a closed condition on a layer, `LayerCrossing`: a connected subset
     of the layer over `Cl D` meeting the two closed side segments. The axis is allowed in the
     condition and excluded afterwards. **The margin `μ` does not reappear.**
  2. D1 needs only one middle point `ψ(x)` over `D`.
  3. D2 uses a ball around that one point instead of `ρ₀`.

  `Property3End` is not proved and is no longer needed.
* **B (pockets): open.** Coarse monotonicity is now a lemma (`IsEps1.sep_of_gap`), but it does not
  confine pockets (§1.B).
* **C (the ends of crossing components): open.** D1 controls one translate. T17's `N` lies in an
  extension that D1 does not control (§1.C).
* **D (T15–T17): open; one step proved.** `crossing_length_pos`: below any `v₀ < 1`, crossings need
  parameter length at least some `λ > 0`. This is what Property 3 gives toward "`I` is finite"; it
  does not give finiteness (§1.D).
* **Nothing is refuted.** The count of defective proofs stays at fourteen.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76R` at the end of `HPC.lean`. The
regenerated `axioms.txt` has 1838 lines (1817 + 21), with `sorryAx` in none. All 21 new theorems use
only `propext`, `Classical.choice` and `Quot.sound`. No declaration uses `sorry`; the word occurs only
in the comment block at the end of `Hagopian76R.lean`, which holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76R.lean`: the skeleton, with the delivered statements and the open items commented out;
* `H76Descent.lean`: layer crossings, `IsCrossRegion`, D1, D2, the least element, the length bound.

Edited earlier files: the commented-out copies of Property 3 in `Hagopian76I.lean` (shape `True`) and
`Hagopian76P.lean` (the batch-171 shape, which `hagopian76_property3` now proves) are replaced by
one-line pointers. The copies in `Hagopian76J/L/M/O.lean` are kept: they quantify over all `v`,
including `v = 1`, or use other crossing notions, so they are not proved as stated. The batch-172
`property3_end` (`Hagopian76Q.lean`) is kept: it is not proved, only bypassed.

## 1. The items

STATUS lines, in order:
* `STATUS: A proved (hagopian76_property3, hagopian76_property3_domain; D1 crossing_from_layer_translate; D2 crossing_descends)`
* `STATUS: B open (pockets; coarse monotonicity proved as IsEps1.sep_of_gap, insufficient)`
* `STATUS: C open`
* `STATUS: D open (crossing_length_pos proved; "I is finite", Property 4, T15–T17 open)`

### 1.A Property 3 by descent

**The objects.**
* `IsCrossRegion M π F c₁ D′` (a `structure`) holds when:
  * `D′ ⊆ (3/22, 19/22) × (0, c₁)`;
  * `F[D′]` is open;
  * the frontier of `F[D′]` meets `π[M]` only over the axis and over the closed side segments
    `{3/22} × [0, c₁]`, `{19/22} × [0, c₁]`.

  `isCrossRegion_of_D` derives it from the output of `hagopian76_D` together with T7's
  `Disjoint I₂ (π[M])`.
* `LayerCrossing d π F c₁ D′ u` (a `def`) says that the layer `d⁻¹(u)` contains a connected `Z` over
  `Cl F[D′]` that meets `π⁻¹F[{3/22} × [0, c₁]]` and `π⁻¹F[{19/22} × [0, c₁]]`.
* `isClosed_layerCrossing`: the set of such `u` is closed. This is `crossing_set_closed` (batch 170)
  with `A`, `B`, `W` taken to be the two closed side sets and `π⁻¹[Cl F[D′]]`.
* `layerCrossing_disjoint`: a layer containing a layer crossing misses `E`.
  * A layer of `G` that meets `E` is a layer of `E` (`layer_mem_E_same`, from
    `hagopian76_initial_segment`).
  * A layer of `E` projects to the single point `F(t, 0)`.
  * That point cannot be both `F(3/22, ·)` and `F(19/22, ·)`.

  This replaces the commission's D1.1 and the height margin `μ`.

**D1 (`crossing_from_layer_translate`).** Take `ψ : M → M` **continuous**, with
`dist(y, ψ(y)) < 2ε₁`, `ψ[E] ⊆ d⁻¹(u)`, and one point `x ∈ E` with `k(x) ∈ [4/11, 7/11]` and `ψ(x)`
over `D`. Then `d⁻¹(u)` misses `E` and contains a layer crossing.
1. *`d⁻¹(u) ∩ E = ∅`.* Otherwise `d⁻¹(u)` is a layer `k⁻¹(t)` and contains `ψ(y₀)`, `ψ(y₁)`
   (`k(y₀) = 0`, `k(y₁) = 1`). If `t ≥ 3/22`, `EndCtl` (first half) gives
   `dist(y₀, ψ(y₀)) ≥ 4ε₁`. Otherwise `EndCtl` (second half) gives `dist(y₁, ψ(y₁)) ≥ 4ε₁`.
2. *The ends are not over `D`.* A point of `M` over `F[[3/22, 19/22] × [0, c]]` lies within `η` of
   some `e ∈ E` with `k(e) ∈ [3/22, 19/22]` (`pi_thin_near_layer`, `η = min(ε₁, 1/22)`). `EndCtl` puts
   `k⁻¹(0)` at distance `≥ 4ε₁` from such `e`, while `ψ(y₀)` is within `2ε₁` of `k⁻¹(0)`.
3. *Coarse monotonicity* (`IsEps1.sep_of_gap`): if `k(x) ≤ m/11` and `k(y) > (m + 1)/11`, then
   `dist(x, y) ≥ 4ε₁`, because they lie in pieces `i ≤ m` and `j ≥ m + 2`.
   * A point `ψ(y)` with `k(y) ≤ 7/11` is not over the right side segment: the nearby `e` has
     `k(e) > 18/22 > 8/11`.
   * A point `ψ(y)` with `k(y) ≥ 4/11` is not over the left side segment: `k(e) < 4/22 = 2/11`.
4. *Boundary bumping* (`exists_mem_closure_component_notMem`) in the continua `ψ[k⁻¹[[0, k(x)]]]`
   and `ψ[k⁻¹[[k(x), 1]]]`, from `ψ(x)`, relative to the open set over `D`.
   * The closure of each component contains a point not over `D`, hence over the frontier.
   * That point is not over `I₂`, which misses `π[M]`.
   * It is not over the axis, by step 1.
   * It is not over the far side, by step 3.

   So the left continuum reaches the left side segment and the right continuum reaches the right
   one. The union of the two closures is the layer crossing.

**D2 (`crossing_descends`).** Let `d⁻¹(v)`, `0 < v < 1`, contain a layer crossing `Z`.
1. `Cl Z` misses `E` (`layerCrossing_disjoint`). So `Cl Z` lies over
   `F[[3/22, 19/22] × (0, c₁]]` and meets both open side edges: it is a crossing in the sense of
   `hagopian76_property3_translate`. That theorem gives an `ε₁`-homeomorphism `h` with
   `h[G] ⊆ d⁻¹(v)` and `h[k⁻¹((4/11, 7/11))] ⊆ Cl Z`.
2. For `x` with `k(x) = 1/2`, the point `h(x) ∈ Cl Z` lies over `D`. Otherwise it is over the
   frontier: not over `I₂`, not over the axis, and not over either side by coarse monotonicity
   (with `dist(x, h(x)) < ε₁`).
3. Take a ball of radius `ρ` around `h(x)` inside the open set over `D`, and the shift `g` of
   `hagopian76_property3_shift` with `δ = min(ρ, ε₁)`. This gives `u ∈ (0, v)` with
   `g[d⁻¹(v)] = d⁻¹(u)`.
4. `ψ = g ∘ h` moves points less than `2ε₁`, maps `E` into `d⁻¹(u)`, and keeps `ψ(x)` over `D`.
   D1 gives a layer crossing in `d⁻¹(u)`.

**The least element (`property3_layer_aux`).** Suppose `d⁻¹(v)`, `v < 1`, contains a layer
crossing.
1. `T = {u ≤ v : LayerCrossing u}` is closed and nonempty; let `u` be its least element.
2. `u > 0`, since `d⁻¹(0) = k⁻¹(0) ⊆ E`, while a layer containing a crossing misses `E`.
3. `u ≤ v < 1`, so D2 gives an element of `T` below `u`. Contradiction.

**The two forms of Property 3.**
* `hagopian76_property3_domain`: take `Z = Cl B`.
* `hagopian76_property3` (thin-strip form):
  1. T7 gives an arc `I₂` at height `≤ c′` that misses `π[M]`.
  2. `hagopian76_D_aux` gives `D′`, which is a crossing region by `isCrossRegion_of_D`.
  3. `rect_domain_low` gives a low strip `(3/22, 19/22) × (0, c₀) ⊆ D′`.
  4. For `c = min(c₀, c′)`, the closure of a thin crossing lies over
     `F[[3/22, 19/22] × [0, c₀]] ⊆ F[Cl D′] ⊆ Cl F[D′]`, so it is a layer crossing.

**The commission's points, checked.**
* *D1.1–D1.5:* correct, in the forms above.
  * D1.1 uses `EndCtl` rather than "at most two adjacent pieces".
  * D1.3 is step 2.
  * D1.4 is `IsEps1.sep_of_gap` with gaps `m = 2` and `m = 7`. The commission's bounds `9/11 + η`
    and `2/11 − η` are not needed in this form.
* *D2, closed ends of `[4/11, 7/11]`:* not needed. One middle point suffices, since D1 recreates the
  crossing from the ends of the translate.
* *Closing the argument:* the set is defined by continua with closed properties, as proposed.
  * `X₀`, `X₁` are not needed: the side segments play their role.
  * `K_mid` is replaced by "over `Cl D`".
* *Uniformity of `μ`* ("Say what you find"):
  * **No margin is needed.** The commission's `K_mid` needed heights `≥ μ` to keep the crossing
    above the axis.
  * In the closed condition the axis is allowed. For `u ∈ T` it is excluded afterwards: a layer
    containing a layer crossing cannot meet `E`, since a layer of `E` projects to one point.
  * The top of `D` is `I₂`, which misses `π[M]`, so boundary bumping cannot leave through the top.
  * As the commission expected, a uniform `μ` for crossings in layers `d⁻¹(u)` with `u ↓ s` is not
    available. This was not needed and was not investigated further.
* *"`T` nonempty: `ψ = h`, `Γ = h[E]`":* the given crossing itself is the first element.

**Not covered.** The end element `d⁻¹(1)`, which Hagopian's "an element of the decomposition"
includes.
* The swallowing lemma (so `hagopian76_property3_translate`) and the shift both need `v < 1`.
* In T15–T17, Property 3 is used to show that `I` is finite. That use covers intervals reaching
  `1`; see 1.D.

### 1.B Pockets (open)

What is proved:
* Coarse monotonicity, `IsEps1.sep_of_gap`. A point of a translate `h′[E]` over abscissa `t` of
  the thin strip lies in `h′` of a piece whose index differs from that of `t` by at most one, plus
  the `η`-slack. This is steps 2–3 of D1.
* Hence a crossing continuum `Cl Cᵢ₋₁ ⊆ h′[E]` (`crossing_essential`) meets the middle abscissae
  only in `h′[k⁻¹[[3/11, 9/11]]]`, roughly.

Why it does not settle pockets (informal):
* A pocket `P` that touches the left side segment and reaches abscissa `1/2` has two boundary
  strands in `Cl Cᵢ₋₁`. Both run from near the left side to abscissa `1/2`.
* Coarse monotonicity puts both strands in `h′` of pieces 2–7. That is no contradiction: the
  pieces of `E` are not small (`IsEps1` separates non-adjacent pieces; it does not bound their
  diameters), and one translated piece can contain both strands.
* So pockets reaching the middle abscissae, where `L₆` lies, are not excluded by anything
  available.
* `CoverPocket` stays a proposed named `Prop`. It is not introduced as a definition, since no
  theorem uses it yet.

### 1.C The ends of crossing components (open)

Commission §2.C asks whether T17 can run with "crossing continuum containing a translate as in D1"
in place of "crossing component". Informal answer: this settles neither the first-component step
nor the `N` step.
* T17's "Let `Cᵢ₋₁` be the first component … met by extending `Cl Cᵢ` away from `X`" needs
  components: their first one is chosen in an extension of `Cl Cᵢ`.
  * The descent could run over layer crossings in the layers of `L`, as in 1.A. But
    "first … met by extending" orders crossings along the extension, not by a layer parameter of
    `G`.
  * Translating this needs the decomposition of `L` (a type A′ continuum by Lemma 1) and Property 3
    for `L`. `hagopian76_property3` gives the latter for extensions of `E` away from `k⁻¹(0)`, not
    for extensions of `Cl Cᵢ`.
* "The continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`" concerns `N ⊆ L`, which runs from
  `yᵢ` to `yᵢ₋₁` through `Cl Cᵢ`, `Cl Cᵢ₋₁` and the part of `L` between them. D1 controls the ends
  of one translate `ψ[E]`, which lie off `Cl D`. It says nothing about the part of `L` between two
  crossings.

### 1.D T15–T17 and the assembly (open; one step proved)

**`crossing_length_pos`.** Fix `v₀ < 1`. There is `λ > 0` such that every connected
`Z ⊆ d⁻¹[[x, y]]` with `y ≤ v₀`, lying over `Cl D` and meeting both closed side segments, has
`y − x ≥ λ`.

*Proof:* suppose not, and take `yₙ − xₙ → 0` and `xₙ → u`. The upper limit of `Zₙ` along a
subsequence:
* is connected (`limsup_isPreconnected`);
* lies in `d⁻¹(u)`, since eventually `Zₙ ⊆ d⁻¹[[u − ε, u + ε]]`, a closed set;
* lies over `Cl D` and meets both side segments.

So it is a layer crossing with `u ≤ v₀ < 1`, against `property3_layer_aux`.

**"It follows from Property 3 that `I` is finite": not derived.** `I` is the collection of `[x, y]`
such that `d⁻¹[[x, y]]` is irreducible with respect to containing a crossing component.
* Distinct intervals of `I` are non-nested, and they come from distinct, hence disjoint,
  components.
* Below `v₀ < 1` each interval has length `≥ λ` (`crossing_length_pos`).

Neither fact bounds the number of intervals:
* a family of pairwise non-nested intervals of length `≥ λ` can be infinite (`[t, t + λ]`,
  `t ∈ [0, 1 − λ]`);
* components of `F ∩ π⁻¹[D]` can accumulate, since `F` is not locally connected.

No argument for finiteness from Property 3 alone was found. The printed inference is recorded as not
evident: a gap in exposition, not a refutation.

**Not reached:** Property 4 and its base case ("Note that `[x₁, x₂]` does not have Property 4"),
the induction (Cases 1 and 2), Bing's lemma, and the assembly. No conditional form of Theorem 1 is
stated, because these steps are not formalized even conditionally.

## 2. Ledger entries (`LEDGER.md` §6, batch 173)

1. **p. 347, Property 3** (the four sentences). **Proved**, for every element `d⁻¹(v)` with `v < 1`
   and every extension of `E` away from `k⁻¹(0)` (`hagopian76_property3`,
   `hagopian76_property3_domain`).
   * "The first point `v`" is attained for the closed condition `LayerCrossing`.
   * "By Lemma 1 and Property 1" is supplied by the swallowing lemma.
   * The step "`d⁻¹(u)` contains a component … whose closure meets …", for which no argument is
     printed, is D1.
   * The end element `d⁻¹(1)` is not covered.
2. **p. 347:** "It follows from Property 3 that I is finite." **Open.** Only the length bound
   (`crossing_length_pos`) follows. The inference is not evident.
3. **p. 348:** "Note that [x₁, x₂] does not have Property 4." Not reached. **Open.**
4. **pp. 348–349:**
   * "Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J]": the pockets are **open**, and coarse
     monotonicity does not exclude them.
   * "the continuum N does not come within ε₂ of π⁻¹(p₄)": **open**.
   * "Let Cᵢ₋₁ be the first component …": not reached, **open**.

No statement of Hagopian's is refuted. The count stays at fourteen.

## 3. Axioms

Group *Hagopian 1976 XVIII (batch 173)* of `Axioms.lean`; the per-theorem output is in
`doc/batches/audits/axioms-batch173.txt`. Each of the 21 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* `crossing_from_layer_translate`, `crossing_descends`, `isCrossRegion_of_D`,
  `hagopian76_property3_domain`, `hagopian76_property3`, `crossing_length_pos`;
* `exists_eleventh_le`, `exists_eleventh_ge`, `IsEps1.sep_of_gap`, `isCompact_collar_image`,
  `rect_sub`, `layer_mem_E_same`, `isClosed_layer`, `isClosed_layerCrossing`, `mem_E_of_axis`,
  `pi_E_eq`, `layerCrossing_disjoint`, `crossing_from_layer_translate_aux`, `crossing_descends_aux`,
  `property3_layer_aux`, `crossing_length_pos_aux`.

Named `Prop`s and definitions introduced: `IsCrossRegion` (a `structure`) and `LayerCrossing` (a
`def … : Prop`). `Property3End` (batch 172) is no longer used by the main line.

## 4. Dependency map of Theorem 1, updated

```
T6/T7 ─ hagopian76_D ─ isCrossRegion_of_D ─┐
                                           │
T8/T9_full ─ crossing_essential            │
     │                                     │
 follows_crossing ─ hagopian76_property3_translate (swallowing lemma, batch 172)
                                           │
 pi_thin_near_layer, EndCtl, IsEps1.sep_of_gap
     │                                     │
 crossing_from_layer_translate (D1) ── crossing_descends (D2) ── hagopian76_property3_shift
                                           │
 crossing_set_closed ─ isClosed_layerCrossing
                                           │
                     property3_layer_aux ──┴─ hagopian76_property3 [PROVED]
                                           └─ hagopian76_property3_domain [PROVED]
                                           └─ crossing_length_pos [PROVED]
     │
   "I is finite" (hagopian76_I_finite)                                       [open]
   crossing_sides_cover_schoenflies [bottom + I₂] ── pockets (CoverPocket)   [open]
   crossing_component_ends (CrossingEnds)                                     [open]
     │
   T15–T17 (Property 4; Bing; Cases 1–2; first component)                     [open]
     │
   hagopian76_theorem1                                                        [open]
```

## 5. Skeleton proposal for what remains

```
-- D, first step
def Icoll (d) (π F c₁ D') : Set (unitInterval × unitInterval) := …   -- Hagopian's I
theorem hagopian76_I_finite … : (Icoll …).Finite                      -- needs an argument beyond
                                                                       -- Property 3 (§1.D)
-- B
def CoverPocket … : Prop
theorem crossing_sides_cover' … (hP : CoverPocket …) : … ⊆ belowSet … ∪ aboveSet …
-- C
theorem first_crossing_in_extension … : -- "the first component met by extending Cl Cᵢ away
                                        -- from X", via layer crossings in the layers of L
theorem N_far_from_p4 … : ∀ y ∈ N, ε₂ ≤ infDist (y : Pt) (π ⁻¹' {p₄})
-- D
theorem hagopian76_property4_base … ; theorem hagopian76_property4_step … ;
theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1_of (hI : …Finite) (hP : CoverPocket …) (hN : …) : Hagopian76Thm1
```

## 6. Build provenance

The run started from a checkout with the compiled Mathlib files present and no local build outputs of
`HPC`.
1. `lake build HPC.Hagopian.Hagopian76Q` was run first.
2. The new files were checked with `lake env lean`, then built with `lake build HPC.Hagopian.<file>`.
3. Then `lake build HPC`.
4. `axioms.txt` was regenerated with `lake env lean Axioms.lean > axioms.txt`; its first 1817 lines
   are unchanged.
