Commission read: `doc/batches/COMMISSION-batch171.md` ("Commission: batch 171 — Part E, Hagopian 1976 XVI: Theorem 1 — Property 3 without margins; positions through the side edges; the ends of crossing components; T15–T17").

# Report, batch 171

## 0. Summary

* **A (Property 3): reduced to an end case; the end case is open.** Neither of the two routes asked
  for is completed. A third route, through **Lemma 3 alone**, proves more than either would have at
  this stage: an interior layer `d⁻¹(v)` of a type A′ continuum that meets two distinct layers of a
  translate `h[E]` (any homeomorphism `h`) meets a translated end set `h[k⁻¹(0)]` or `h[k⁻¹(1)]`
  (`layer_meets_translate_end`). With `follows_crossing` this gives
  `hagopian76_property3_reduced`: a layer of `F` containing a crossing reaches, through every link on
  one side, an end link of the chain (`L₀, …, L₅` or `L₅, …, L₁₀`). No least `v` and no margins are
  used. What remains (the layer meets every `h[k⁻¹(t)]`, `t ≤ 6/11`, or every one with `t ≥ 5/11`)
  is open.
* **B (positions through the side edges): the bottom case proved; the `I₂` case, the side-edge
  definitions and the pockets open.** `crossing_bottom_below`: a component of `π⁻¹[D] − Z` whose
  closure reaches `π⁻¹` of the bottom edge is below `Z`, for any compact `Z` missing `π⁻¹` of the
  bottom edge (in particular `toPt K` for a subcontinuum `K` missing `E`).
* **C (the ends of a crossing component): open.**
* **D (T15–T17, the assembly): open.** Waits on A (end case), B and C.
* **E (the dichotomy, optional): the dichotomy is no longer needed.** `R(E)` lies in the composant
  `κ` of a point `x ∈ E`, so any homeomorphism with `h(x) ∉ κ` has `h[R(E)] ∩ R(E) = ∅`
  (`translate_Rset_disjoint`); no Baire category in `Homeo(M)` is needed. Taking `p`, `q` off the
  meagre `κ` instead of off `R(E)` gives **T12 (conditions 2–3) without `RsetDichotomy`**
  (`hagopian76_T12_uncond`). The dichotomy itself is not proved; it is bypassed.
* **Nothing is refuted.** No defective proof is added; the count stays at fourteen.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76P` at the end of `HPC.lean`. All 11
new theorems use only `propext`, `Classical.choice` and `Quot.sound`. The regenerated `axioms.txt`
has 1799 lines (1788 + 11), and `sorryAx` appears in none of them. No declaration uses `sorry`; the
word occurs only in the comment block at the end of `Hagopian76P.lean`, which holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76P.lean`: the skeleton, with the delivered statements and the open items commented out.
* `H76Prop3L3.lean`: `layer_meets_translate_end_aux`, `translate_params_ordConnected`,
  `layer_meets_translate_initial`.
* `H76Bottom.lean`: `isPreconnected_preimage_off`, `bottom_component_below_aux`.
* `H76GenericComp.lean`: `translate_Rset_disjoint`, `exists_generic_pq_comp_aux`.

Earlier files are not edited (no commented-out copy of a statement proved here existed in them).

## 1. The items

STATUS lines, in order: `STATUS: A open (reduced to the end case; layer_meets_translate_end and
hagopian76_property3_reduced proved)`; `STATUS: B open (bottom case proved)`; `STATUS: C open`;
`STATUS: D open (not reached)`; `STATUS: E proved in the form T13–T17 use (hagopian76_T12_uncond;
the dichotomy itself bypassed, not proved)`.

### 1.A Property 3 — reduced to the end case

**The route actually used (Lemma 3).** `lemma3_half` (batch 156) says: if `h[k⁻¹(s)]`
(`0 < s < 1`) meets `d⁻¹(u)` and misses the end sets of `F`, then `h[k⁻¹(s)] ⊆ d⁻¹(u)`. Apply it with
the roles exchanged: `E := F` (map `d`), `F := E` (map `k`), the homeomorphism `h⁻¹`, `s := v`. If
`C = d⁻¹(v)`, `0 < v < 1`, meets `h[k⁻¹(α)]` and misses `h[k⁻¹(0) ∪ k⁻¹(1)]`, then
`h⁻¹[C] ⊆ k⁻¹(α)`. Doing this for two values `α ≠ β` puts the nonempty `h⁻¹[C]` inside the disjoint
layers `k⁻¹(α)` and `k⁻¹(β)`.

* **`layer_meets_translate_end`**: `C` meets `h[k⁻¹(α)]` and `h[k⁻¹(β)]`, `α ≠ β`, implies `C`
  meets `h[k⁻¹(0)]` or `h[k⁻¹(1)]`. No smallness of `h` and no plane geometry.
* **`translate_params_ordConnected`**: `{t : C ∩ h[k⁻¹(t)] ≠ ∅} = k[E ∩ h⁻¹[C]]`, the image of a
  continuum (hereditary unicoherence), is an interval.
* **`layer_meets_translate_initial`**: hence, for `α < β` both met, `C` meets every `h[k⁻¹(t)]` with
  `t ≤ β`, or every one with `t ≥ α`.
* **`hagopian76_property3_reduced`**: in the set-up of `follows_crossing`, if a crossing `B` has
  `Cl B ⊆ d⁻¹(v)`, `0 < v < 1`, then for the homeomorphism `h` of `follows_crossing`
  (`Cl B ⊇ h[k⁻¹((4/11, 7/11))]`, link condition `h[piece (j + 1)] ⊆ Lⱼ`), `C` meets every
  `h[k⁻¹(t)]` with `t ≤ 6/11` or every one with `t ≥ 5/11`, and so meets `L₀, …, L₅` or
  `L₅, …, L₁₀`.

**Route A.1 (middle translates).** Not completed. The set of `v` whose layer contains a middle
translate `h[k⁻¹[[α, β]]]` for some `ε₁`-homeomorphism is not known to be closed: homeomorphisms do
not converge, and the limit continuum given by `crossing_set_closed` is only a continuum meeting two
compact sets. Recognising that limit as again containing a middle translate is item C's smallness
question (Lemma T run in the limit layer), which is open. The budgeting of `ε₁` against the shift
`g` (`g ∘ h` stays an `ε₁`-homeomorphism if `δ < ε₁ − sup dist(h, id)`, which is positive since `M`
is compact) is fine; closedness is the obstruction.

**Route A.2 (triod).** Checked, and it does not close the gap either.
* The triod is real: if `h[E] ∩ F ⊆ C`, `h[E] ⊄ F`, and `0 < v < 1`, then `C` with the arms
  `d⁻¹[[0, v)]`, `d⁻¹((v, 1]]` and `h[E] − F` is a triod (the three sets are mutually separated
  because `Cl(h[E] − F) ∩ F ⊆ h[E] ∩ F ⊆ C`). `0 < v < 1` is needed for the two arms of `F` to be
  nonempty.
* But `h[E] ∩ F ⊆ C` is not known. Lemma 4's strong form (layers of an extension are layers of the
  line) applies to `E ⊆ F` with a common end set; for the overlap `Q = h[E] ∩ F` it gives only that
  layers of `h[E]` inside the interior of `Q` lie in single layers of `F` (the argument of
  `lemma3_half`). When an end set of `h[E]` lies in `C`, `Q` can run from `C` along `F` and no triod
  appears. This is exactly the end case left by the Lemma 3 route; A.2 adds nothing beyond it.
* The arm of `h[E]` outside `F` can indeed coincide with part of an arm of `F` (when `Q` extends
  past `C`), which is the first point the commission asked to check.

**The end case (open).** `C = d⁻¹(v)` meets `h[k⁻¹(t)]` for every `t ≤ 6/11` (or every `t ≥ 5/11`).
(Informal, not formalized:) by `lemma3_half` (forward direction), every such `h[k⁻¹(t)]` that misses the end sets of `F` lies in
`C`; with `EndCtl` (`h` an `ε₁`-homeomorphism cannot move layers `≥ 3/22` onto `k⁻¹(0) = d⁻¹(0)`),
`C ⊇ h[k⁻¹[[3/22, 6/11]]]` unless `h[k⁻¹(t)]` meets the far end set `d⁻¹(1)`. Nothing in the
continuum theory available excludes a layer of `F` that contains an initial segment of a translate
of `E`; in Hagopian's proof this configuration is excluded only by the least-`v` argument, which is
where the margin problem sits. *Obstruction:* closedness of a margin-free crossing set, or a reason
from the plane why a layer crossing `D` cannot contain `h[k⁻¹[[3/22, 6/11]]]` and reach `L₀`.

### 1.B Positions through the side edges — the bottom case proved

**`isPreconnected_preimage_off`.** `π` (the quotient map collapsing the layers of `E`) is injective
off `E` (`eq_of_pi_eq_off`) and open there (`pi_isOpen_image_off`), and onto. So on `X = π⁻¹[G]`,
`G` open and missing `π[E]`, the restriction `π|X` is an injective open map onto `G`, and
`IsPreconnected.preimage_of_isOpenMap` gives `X` connected when `G` is.

**`crossing_bottom_below`** (`bottom_component_below_aux`), as commissioned:
1. `Q = [a, b] × [0, 1] ∩ F⁻¹[π[Z]]` is compact and misses the axis (`Z` misses `π⁻¹` of the bottom
   edge), so it lies above a height `c_K > 0` (`exists_height_below`).
2. The strip `S′ = (a, b) × (0, c′)`, `c′ = min(c₀, c_K)`, lies in `D′` (hypothesis `hlow`, the low
   strip of `rect_domain_low`), `G = F[S′]` is open (the collar is an embedding and `F[D′]` is open)
   and connected, misses `π[E]` and `π[Z]`.
3. `π⁻¹[G]` is connected (above), lies in `π⁻¹[D] − Z`, and contains a point over `F(t₀, c′/2)`.
4. A point `x` of the closure of the component `U` over the bottom edge has a neighbourhood whose
   points of `π⁻¹[D]` lie over `S′` (the trace of an open set of the plane on `F[R]` is
   `F[R ∩ {|y| < c′}]`); so `U` meets `π⁻¹[G]`, and `U ∪ π⁻¹[G]` joins `P` to the vertical below
   height `c′`.

*Shape:* the conclusion is the batch-169 `belowSet` (vertical anchor) with `u = c′`; the hypothesis
`hlow : ∃ c₀ > 0, (a, b) × (0, c₀) ⊆ D′` is what `rect_domain_low` provides in the setting of
`hagopian76_D`. The new definitions `belowSet′`, `aboveSet′` are not introduced: the bottom case does
not need them.

**Open.**
* *`I₂` case.* Needs that the points of `D′` within `δ` of the arc `I` form a connected set for small
  `δ`. No inner collar of `I` in `D′` exists in the project, and `I` is an arbitrary arc (`TArc`),
  so the balls around points of `I` meet `D′` in sets whose connectedness is a genuine plane-topology
  statement (local connectedness of `Cl D′` along `I`, from the Jordan–Schoenflies theorem). Not
  done.
* *Side edges, `belowSet′`, `aboveSet′`.* Disjointness with side-edge anchors needs a version of
  `rect_domain_crossing_separates` whose anchors lie on the frontier (the two side segments below and
  above the extreme points of `Z`); the existing Jordan-curve argument closes a curve through the
  vertical, not through the sides. Not done.
* *Pockets.* Unchanged from report 170 §1.B.

### 1.C The ends of a crossing component — open

* **Smallness.** The suggested argument needs, for a crossing component `C` essential to `h[R(E)]`,
  a point `h′(x′)` with `h′` `δ`-small and `k(x′)` in the middle range. `follows_crossing` gives
  `Cl C ⊇ h[k⁻¹((4/11, 7/11))]` with `h` an `ε₁`-homeomorphism, and `ε₁` is fixed before `D`, while
  Lemma T's `δ` is chosen after `D`. `pi_thin_near_layer` and Effros give a `δ`-small `h′` near a
  point of `E`, but the points of `Cl C` near `E` that `C` reaches near the left edge need not be of
  the form `h′(x′)` with `k(x′)` in the middle range: `C` meets the left edge at abscissa `3/22`,
  which is the end of the middle range, not inside it. **What I find:** the reduction of item A
  points the same way — the uncontrolled configuration is a crossing continuum that runs out along
  the chain to an end link. No proof either way.
* **Finer links** (informal assessment, not formalized). As the commission says, the loss is from the chain condition. Refining `L`
  (more links, same Property 1) would need Property 1 rerun for the finer chain: `exists_prop1`
  produces the chain from `ε₁` and the 11 pieces; with `n` pieces the loss is `1/n` at each end, so
  the middle translate grows to `(1/n·(a + 1), …)` and its ends approach the end links as `n` grows.
  This is not cheap in the present formalization: the number 11 is hard-wired in `chainG`, `piece`,
  `elev`, `EndCtl` and the link control of `crossing_essential`. Not done.

### 1.D T15–T17 and the assembly — open

Not reached. With item E, the assembly no longer needs `RsetDichotomy`: the shape becomes
`Hagopian76Thm1` itself. Property 4's base case still reduces to `π⁻¹[D]` connected (report 170
§1.E); the induction needs the end case of A, the `I₂` and side cases of B, and C.

### 1.E The dichotomy — bypassed (T12 without it)

**`translate_Rset_disjoint`.** `R(E) ⊆ κ`, the composant of `x ∈ E` (`Rset_subset_composant`,
batch 169). A homeomorphism carries `κ` onto the composant of `h(x)` (`image_composant`). Distinct
composants of the indecomposable `M` are disjoint (`composant_eq_or_disjoint'`). So `h(x) ∉ κ` gives
`h[R(E)] ⊆ h[κ]`, disjoint from `κ ⊇ R(E)`.

**`exists_generic_pq_comp_aux`.** The batch-169 proof of `exists_generic_pq_aux`, with the generic
points chosen off the meagre `κ` (`composant_isMeagre`) instead of off the meagre `R(E) ⊆ κ`; the
conclusion gains `h(x) ∉ κ` and `h₁(x) ∉ κ`. (Copied rather than generalized, since earlier files are
not edited.)

**`hagopian76_T12_uncond`.** `hagopian76_T12_of_dichotomy` without the hypothesis
`RsetDichotomy k`: conditions 2–3 of report 168's weakest T12 (`H` separates `p` from `f(p)`;
`h[R(E)] ∩ R(E) = ∅ = h₁[R(E)] ∩ R(E)`; the `p`-component crosses).

**On the commission's Baire route** (informal remark, not formalized). It works, and more simply
than proposed: the "bad" set
`{g : g[R(E)] ∩ R(E) ≠ ∅}` is contained in `{g : g(x) ∈ κ}`, and given any `g` and any `δ`, Effros
gives a `δ`-small `g′` with `g′(g(x))` in a composant other than `κ` (composants are dense and there
are uncountably many). So each closed set `{g : g[Fₙ] ∩ Fₘ ≠ ∅}` has empty interior. The question
the commission raised (moving meeting continua apart by a small homeomorphism) is answered by moving
one point off the composant. The dichotomy itself (if `g[R(E)]` meets `R(E)` then they are equal)
remains unproved, and is no longer used.

## 2. Ledger entries (`LEDGER.md` §6, batch 171)

1. **p. 347, Property 3:** "Let v be the first point of [0, 1] such that d⁻¹(v) contains a component
   of F ∩ π⁻¹[D] whose closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)]. By Lemma 1 and Property 1, L
   follows a type A′ continuum in d⁻¹(v) that meets L₆ ∩ π⁻¹[D]. By Lemmas 2 and 3, a homeomorphism g
   of M onto M and a point u of [0, v) exist such that gd⁻¹(v) = d⁻¹(u) … This contradicts the
   definition of v." **Reduced, open.** Lemma 3 alone excludes a layer containing a middle translate
   and missing both translated end sets (`hagopian76_property3_reduced`). The least `v` is not used.
   The end case is open; route A.2 does not reach it.
2. **p. 347:** "It follows from Property 3 that I is finite." Not reached. **Open.**
3. **p. 348:** "Note that [x₁, x₂] does not have Property 4." Not reached; reduces to `π⁻¹[D]`
   connected. **Open.**
4. **pp. 348–349:** "Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J]": the bottom case of the
   covering is proved (`crossing_bottom_below`); the `I₂` case and the side edges are open. "the
   continuum N does not come within ε₂ of π⁻¹(p₄)": needs item C, open. "Let Cᵢ₋₁ be the first
   component …": not reached. **Open.**
5. **The dichotomy:** not needed. T12 in the form T13–T17 use holds without it
   (`hagopian76_T12_uncond`): `h[R(E)] ∩ R(E) = ∅` follows from `h(x) ∉` the composant of `x`. The
   paper's tacit step is thereby supplied by a different argument; the dichotomy itself is still
   unproved.

No statement of Hagopian's is refuted. The count stays at fourteen.

## 3. Axioms

Group *Hagopian 1976 XVI (batch 171)* of `Axioms.lean`; the per-theorem output is in
`doc/batches/audits/axioms-batch171.txt`. Each of the 11 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* `layer_meets_translate_end`, `hagopian76_property3_reduced`, `crossing_bottom_below`,
  `hagopian76_T12_uncond`;
* `layer_meets_translate_end_aux`, `translate_params_ordConnected`,
  `layer_meets_translate_initial`;
* `isPreconnected_preimage_off`, `bottom_component_below_aux`;
* `translate_Rset_disjoint`, `exists_generic_pq_comp_aux`.

## 4. Dependency map of Theorem 1, updated

```
T6/T7 ─ hagopian76_D ─ hagopian76_K0 ─ K0_crosscut
            │               │
            │      crossing_translate (Lemma T) ── crossing_translate_in_aux
            │               │                                │
            │      K0_dense_low (Lemma T′)       crossing_piece_of_R (Lemma R)
            │               │                                │
            │               │        crossing_separates ─ crossing_pair_separates
            │               │                │               │
            │               │        crossing_sides [disjoint] ── crossing_sides_cover_frontier
            │               │                │          crossing_bottom_below [B: bottom]
            │               │                │          I₂ case, side edges [open]
T8/T9_full ─ crossing_essential ─ T12_parts12 │   isMeagre_Rset ─ composant_isMeagre
     │                                        │               │
 T9_pieces ─ follows_crossing  exists_generic_pq_comp_aux (p, q off the composant of x)
     │                                        │
     │          translate_Rset_disjoint [E] ──► hagopian76_T12_uncond   (RsetDichotomy not needed)
     │                                        │
     │           extChainInter ──► hagopian76_T13_uncond
     │                                        │
 lemma3_half ─ layer_meets_translate_end ─ hagopian76_property3_reduced [A: end case open]
                                              │
   T15–T17 (I finite; Property 4; Bing; covering cases; ends of Cᵢ₋₁)   [open]
                                              │
                               hagopian76_theorem1                      [open]
```

## 5. Skeleton proposal for what remains

```
-- A: the end case
theorem hagopian76_property3_end … (Cl B ⊆ layer d v, 0 < v < 1, B crossing,
    ∀ t ≤ 6/11, (layer d v ∩ h '' layer k t).Nonempty) : False
-- B
theorem collar_inner_I … : ∃ δ > 0, IsPreconnected {z ∈ D' | infDist z I < δ}
theorem crossing_top_above … (Z compact, missing π⁻¹ I₂) : … → P ∈ aboveSet …
def belowSet' … ; def aboveSet' … ; theorem crossing_sides_disjoint' …
-- C
theorem crossing_component_ends … : (toPt (closure B) ∩ L 1).Nonempty ∧ (toPt (closure B) ∩ L 9).Nonempty
-- D (no dichotomy needed any more)
theorem hagopian76_I_finite … ; theorem hagopian76_property4_base … ;
theorem hagopian76_property4_step … ; theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1 : Hagopian76Thm1
```

## 6. Build provenance

The run started from a checkout with no local build outputs of `HPC`; the compiled Mathlib files were
present. `lake build HPC` was run first. Each new file was then checked with
`lake build HPC.Hagopian.<file>`, then `lake build HPC`. `axioms.txt` was regenerated with
`lake env lean Axioms.lean > axioms.txt`.
