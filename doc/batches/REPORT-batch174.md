Commission read: `doc/batches/COMMISSION-batch174.md` ("Commission: batch 174 — Part E, Hagopian 1976 XIX: Theorem 1 — "`I` is finite"; the end element; pockets; T15–T17").

# Report, batch 174

## 0. Summary

* **A (Property 3 for the end element): proved.** `hagopian76_property3_end_element` is
  `hagopian76_property3` for every layer `d⁻¹(v)`, `v ∈ [0, 1]`. `hagopian76_property3_components`
  is the printed Property 3 for every element of the decomposition: no crossing component lies in a
  layer.
* **B ("`I` is finite"): proved.** `hagopian76_I_finite`, by the commission's route §1. Distinct
  members of `I` have disjoint interiors (`crossingIntervals_disjoint`), and this part does not use
  Property 3.
* **C (`J` and the `xᵢ`): `x₁ = 0`, `x₂ = e` proved; `x₂ₙ = 1` open.** `hagopian76_J_xs` gives `e`
  with `d⁻¹[[0, e]] = E` and `e < x` for every `[x, y] ∈ I`.
* **D (Property 4): base case proved; the top block open.** `hagopian76_property4_base` shows that
  `[x₁, x₂]` does not have Property 4.
* **E (the induction): open.** The pockets and the `N`/`ε₂` sentence are still open.
* **F (the assembly): open.** No conditional form is stated.
* **Nothing is refuted.** The count of defective proofs stays at fourteen.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76S` at the end of `HPC.lean`. The
regenerated `axioms.txt` has 1867 lines (1838 + 29: one line per new theorem, except
`IsIrreducibleInterval.layerSet_Ioo_subset_closure`, whose output wraps over three lines), with
`sorryAx` in none. All 27 new theorems use
only `propext`, `Classical.choice` and `Quot.sound`. No declaration uses `sorry`; the word occurs only
in the comment block at the end of `Hagopian76S.lean`, which holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76S.lean`: the skeleton, with the delivered statements, the named `Prop`
  `LastIntervalReachesOne`, and the open items commented out;
* `H76EndElement.lean`: the proper extension, Property 3 in every layer, the length bound in every
  layer;
* `H76IFinite.lean`: crossing components, irreducible intervals, `I`, disjoint interiors,
  finiteness;
* `H76JXs.lean`: `e`, `x₂ = e`, the base case of Property 4.

Edited earlier files, as the rules allow:
* `Hagopian76J.lean`: the commented-out batch-165 shape of Property 3 (crossing components in a
  layer, every `v`) is replaced by a pointer to `hagopian76_property3_components`.
* `Hagopian76R.lean`: the commented-out `hagopian76_I_finite` is replaced by a pointer.

The copies in `Hagopian76L/M/O.lean` are kept. They use the batch-167/168 `Crossing` notion (open
side edges, disjointness from `π⁻¹[I₂]`), and their hypotheses differ from the delivered ones (in
`M` and `O`, no "over `Cl D`" condition), so they are not proved as stated.

## 1. The items

STATUS lines, in order:
* `STATUS: A proved (hagopian76_property3_end_element, hagopian76_property3_components)`
* `STATUS: B proved (hagopian76_I_finite; crossingIntervals_disjoint)`
* `STATUS: C partly proved (hagopian76_J_xs: x₁ = 0, x₂ = e, e < x; x₂ₙ = 1 open)`
* `STATUS: D partly proved (hagopian76_property4_base; Property 4 for the last block open)`
* `STATUS: E open`
* `STATUS: F open`

### 1.A Property 3 for the end element

* `exists_end_extension`. Let `G` be an extension of `E` away from `k⁻¹(0)` with map `d`.
  `exists_proper_extension` (Lemma 4, with hereditary unicoherence and atriodicity from
  `hagopian75_lemma1`) gives `G′ ⊋ G` with `d′⁻¹(0) = d⁻¹(0) = k⁻¹(0)`. Then `ext_layers` (the strong
  form, applied to `G ⊆ G′`) gives `0 < s′ < 1` with `d′⁻¹(s′) = d⁻¹(1)` and `d′⁻¹[[0, s′]] = G`.
  `G′` is again an extension of `E` away from `k⁻¹(0)`.
* `layerCrossing_congr`: `LayerCrossing` depends only on the layer as a set.
* `property3_layer_all`: for `v < 1`, `property3_layer_aux` for `G`. For `v = 1`,
  `property3_layer_aux` for `G′` at `s′ < 1`. The height is the smaller of the two.
* `hagopian76_property3_end_element`: the same with `hagopian76_property3`. The hypotheses at the
  smaller height imply those at each larger height.
* `hagopian76_property3_components` (*shape added*): the printed statement. The closure of a
  crossing component inside `d⁻¹(v)` would be a layer crossing.

The commission's first alternative ("count components of `F′` instead") is not needed: Property 3
is a statement about one layer, and that layer is the same set in `F` and in `F′`.

### 1.B "`I` is finite"

**Definitions** (`H76IFinite.lean`):
* `crossSet G π F D' = G ∩ π⁻¹[F[D′]]`;
* `IsCrossingComponent G π F c₁ D' C`: `C` is a connected component (`connectedComponentIn`) of
  `crossSet`, and its closure meets both closed side segments, over `3/22` and over `19/22`, at
  heights in `[0, c₁]`;
* `IsIrreducibleInterval d C x y`: `C ⊆ d⁻¹[[x, y]]`, and `[x, y] ⊆ [x′, y′]` whenever
  `C ⊆ d⁻¹[[x′, y′]]`;
* `crossingIntervals d π F c₁ D'` (Hagopian's `I`): the pairs `(x, y)` that form an irreducible
  interval of some crossing component.

**Steps** (commission §1):
1. `exists_irreducibleInterval`: every nonempty `C ⊆ G` has an irreducible interval, given by the
   minimum and maximum of `d` on `Cl C`. `IsIrreducibleInterval.closure_meets`: `Cl C` meets both
   end layers. This gives `d[Cl C] ⊇ {x, y}`; together with step 2 this is §1.1.
2. `IsIrreducibleInterval.layerSet_Ioo_subset_closure`: `d⁻¹((x, y)) ⊆ Cl C`
   (`layerSet_Ioo_subset`).
3. Step 3 is used in this form: a point `w` of `d⁻¹(J)` lies in `Cl C₁`, and `d⁻¹(J)` is relatively
   open in `G`, so `C₁` meets `d⁻¹(J)`. The density of `d[C]` is not needed.
4. `mem_component_of_mem_closure_in`: a component of `S` contains every point of `S` in its
   closure. With `IsCrossingComponent.eq_of_mem_closure` this gives `crossingIntervals_disjoint`:
   distinct members of `I` have disjoint interiors (as real intervals). Property 3 is not used.
5. `crossing_length_pos_all`: every member has length `≥ λ`, applied to `Cl C`. This is
   `crossing_length_pos` with the condition `y ≤ v₀ < 1` removed, via `property3_layer_all`.
   `finite_of_disjoint_Ioo`: the left endpoints are `λ`-separated, so `⌊x/λ⌋` is injective on `I`
   with values at most `⌊1/λ⌋`.
6. The end element is covered by A, inside step 5.

Report 173 recorded "It follows from Property 3 that `I` is finite" as not evident. The missing
step was step 4: report 173 had only that the intervals are not nested.

### 1.C `J` and the `xᵢ`

`hagopian76_J_xs`: there is `e > 0` with `d⁻¹[[0, e]] = E` and `e < x` for every `[x, y] ∈ I`.
* *Shape:* the sequence `xᵢ` is not constructed. `J = I ∪ {[0, e]}` is finite by B. The statement
  is what the notes `x₁ = 0`, `x₂ = e` need: `[0, e]` meets no member of `I`, so it is a block of
  `St J` by itself.
* *"Is `x > e` needed, and true?"* It is true. It is needed so that `[0, e]` does not merge with a
  block of `I`. If `x = e` were possible, `x₂` would be the end of a longer block.
* *Proof:*
  * `G = E`: then `e = 1` and `I = ∅`, since no point of `E` lies over `D` (`crossSet_disjoint_E`).
  * Otherwise, `ext_layers` gives `d⁻¹(e) = k⁻¹(1)`. A crossing component `C` misses `E`, so
    `C ⊆ d⁻¹((e, 1])`, and irreducibility gives `e ≤ x`.
  * If `x = e`, then `Cl C` meets `k⁻¹(1)`, which lies over `F(1, 0)`. But `Cl C` lies over
    `F[[3/22, 19/22] × [0, c₁]]`, which misses `F(1, 0)` because `F` is injective.

`x₂ₙ = 1`: **open.** It is recorded as the named `Prop` `LastIntervalReachesOne` (some member of `I`
ends at `1`). This needs the irreducibility of Hagopian's `F` (T13). For a general extension it is
false: `G = E` gives `I = ∅`.
* *Obstruction:* let `y*` be the largest right endpoint, with `y* < 1`. Irreducibility would give a
  contradiction if `d⁻¹[[0, t]]`, `t ∈ (y*, 1)`, still separated `p` from `f(p)`.
* The tail `d⁻¹((t, 1])` meets `π⁻¹[D]` only in non-crossing components, whose closures miss a side
  segment.
* A non-crossing component can still separate `π⁻¹[D]`: a pocket against one side. So the cut need
  not keep the separation.
* This is the pocket problem again (B of batches 172–173).

### 1.D Property 4

* **Base case** (`hagopian76_property4_base`): "Note that `[x₁, x₂]` does not have Property 4."
  * For any `e` with `d⁻¹[[0, e]] = E`, the block `E` separates no two points in `π⁻¹[D]` (`SepIn`,
    the notion used for T13).
  * `E` misses `π⁻¹[D]`, and `π⁻¹[D]` is connected: `isPreconnected_preimage_off`, from `D′`
    connected (a hypothesis, supplied for Hagopian's domain by `rect_frontier_domain`).
  * Clause (2) fails for every point. This completes the reduction of report 170 §1.E.
* **Property 4 for `[x₂ₙ₋₁, x₂ₙ]`: open.** "The interval `[x₂ₙ₋₁, x₂ₙ]` has the following property"
  has no printed argument.
  * Clause (2), that only the last block separates, needs the other blocks dropped while the
    separation is kept. This meets the obstruction of 1.C, since the gaps between blocks still meet
    `π⁻¹[D]` in non-crossing components.
  * Clause (1) needs the point `yₙ ∈ K` and the essential-continuum set-up of T12 inside the
    statement.

### 1.E The induction (open)

What the induction uses (Case 1):
* With `P = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q`, the point `f(yᵢ₋₁)` lies in a component of `π⁻¹[D] − P` that is
  above `d⁻¹[I]` or below `d⁻¹[J]`.
* `f[N]` misses `P` because `N` stays `ε₂` away from `Q`.

* **Pockets.**
  * Step 2 of §1 (`IsIrreducibleInterval.layerSet_Ioo_subset_closure`) puts the whole layers
    `d⁻¹((x, y))` of a crossing block inside `Cl Cᵢ₋₁`.
  * A pocket against a side segment is bounded by a strand of `d⁻¹[[x, y]]`. That strand is a union
    of pieces of layers of `F`, not a translate of a short piece of `E`.
  * Coarse monotonicity (`IsEps1.sep_of_gap`) controls translates of `E`. It does not bound how far
    a strand of a layer of `F` reaches from the side.
  * So the commission's question ("Is that strand a union of layers of `F` with parameters that
    leave and re-enter the side?") has answer: it lies in the union of the layers over `[x, y]`, but
    nothing available limits its reach. Informal; not formalized.
* **`N`.**
  * Hagopian's reason is "Since `L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and `Cl Cᵢ`". `ε₂ ≤
    ρ(M, π⁻¹[I₁ ∪ I₂])` keeps `N` from passing `I₁` or `I₂` only if `N` lies in the part of `L` that
    follows the two crossing closures.
  * That needs the first-component argument and Property 3 for `L`, which is an extension of
    `Cl Cᵢ`, not of `E`. `hagopian76_property3` is for extensions of `E` away from `k⁻¹(0)`.
  * By Lemma 1, `L` is of type A′, but its decomposition is not related to `E`'s chain `L₀ … L₁₀`.

### 1.F The assembly (open)

Not stated, even conditionally.
* A conditional form would take Property 4 for the last block and the step as hypotheses.
* Both need the full set-up of T12/T13 (`K`, `h`, `f`, `p`, the irreducible `F`) and the blocks
  `xᵢ` inside a `Prop`. Writing such a `Prop` without a proof route would fix a shape that has not
  been checked.

## 2. Ledger entries (`LEDGER.md` §6, batch 174)

1. **p. 347:** "It follows from Property 3 that I is finite." **Proved** (`hagopian76_I_finite`).
   The omitted steps are 1–4 of §1.B. This supersedes the batch-173 entry ("not evident").
2. **p. 347–348:** "Note that x₁ = 0, x₂ = e, and x₂ₙ = 1."
   * `x₁ = 0`, `x₂ = e`: **proved** (`hagopian76_J_xs`, with `e < x`).
   * `x₂ₙ = 1`: **open**, a gap in exposition. It depends on the choice of `F`.
3. **p. 348:**
   * "Note that [x₁, x₂] does not have Property 4": **proved** (`hagopian76_property4_base`).
   * Property 4 for `[x₂ₙ₋₁, x₂ₙ]`: **open**.
   * "we now show that if I … has Property 4, then so does J": **open**.
4. **pp. 348–349, Cases 1 and 2:** "Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J]" (pockets),
   "the continuum N does not come within ε₂ of π⁻¹(p₄)", "Let Cᵢ₋₁ be the first component …": all
   **open**.
5. **Property 3 at the end element:** **proved** (`hagopian76_property3_components`,
   `hagopian76_property3_end_element`), through a proper extension.

No statement of Hagopian's is refuted. The count stays at fourteen.

## 3. Axioms

Group *Hagopian 1976 XIX (batch 174)* of `Axioms.lean`; the per-theorem output is in
`doc/batches/audits/axioms-batch174.txt`. Each of the 27 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* skeleton: `hagopian76_property3_end_element`, `hagopian76_property3_components`,
  `hagopian76_I_finite`, `hagopian76_J_xs`, `hagopian76_property4_base`;
* `H76EndElement.lean`: `layerCrossing_congr`, `exists_end_extension`, `property3_layer_all`,
  `property3_end_element_aux`, `crossing_length_pos_of_forall`, `crossing_length_pos_all`;
* `H76IFinite.lean`: `IsIrreducibleInterval.unique`, `isClosed_layerSet_Icc`,
  `exists_irreducibleInterval`, `IsIrreducibleInterval.closure_meets`,
  `IsIrreducibleInterval.layerSet_Ioo_subset_closure`, `mem_component_of_mem_closure_in`,
  `IsCrossingComponent.isConnected`, `IsCrossingComponent.subset`,
  `IsCrossingComponent.eq_of_mem_closure`, `crossingIntervals_disjoint`, `finite_of_disjoint_Ioo`,
  `I_finite_aux`, `property3_components_aux`;
* `H76JXs.lean`: `crossSet_disjoint_E`, `J_xs_aux`, `property4_base_aux`.

Definitions introduced: `crossSet`, `IsCrossingComponent`, `IsIrreducibleInterval`,
`crossingIntervals` (Hagopian's `I`). Named `Prop`: `LastIntervalReachesOne` (`def … : Prop`,
`x₂ₙ = 1`); no theorem assumes it.

## 4. Dependency map of Theorem 1, updated

```
property3_layer_aux (batch 173) ── exists_end_extension (Lemma 4 + ext_layers)
                │                              │
                └──────── property3_layer_all ─┴─ hagopian76_property3_end_element   [PROVED]
                                   │            └─ hagopian76_property3_components   [PROVED]
                       crossing_length_pos_all
                                   │
 layerSet_Ioo_subset ─ IsIrreducibleInterval.layerSet_Ioo_subset_closure
 mem_component_of_mem_closure_in ─ crossingIntervals_disjoint
                                   │
                       hagopian76_I_finite                                        [PROVED]
                                   │
 ext_layers, crossSet_disjoint_E ─ hagopian76_J_xs (x₁ = 0, x₂ = e)                 [PROVED]
                                   │   LastIntervalReachesOne (x₂ₙ = 1)            [open]
 isPreconnected_preimage_off ───── hagopian76_property4_base                        [PROVED]
                                   │
   Property 4 for [x₂ₙ₋₁, x₂ₙ] (T13 irreducibility; pockets)                       [open]
   induction, Cases 1–2 (pockets: CoverPocket; N and ε₂: CrossingEnds)             [open]
                                   │
   hagopian76_theorem1_final                                                       [open]
```

## 5. Skeleton proposal for what remains

```
-- the separation lemma that x₂ₙ = 1 and Property 4 (2) both need
theorem sepIn_of_cut … (hF : SepIn (π ⁻¹' D) (toPt F) p q)
    (htail : ∀ C, C component of (F \ F₀) ∩ π⁻¹[D] → ¬ (closure C crosses) → NoPocket C) :
    SepIn (π ⁻¹' D) (toPt F₀) p q
def NoPocket … : Prop   -- the closure of C together with one side segment bounds no
                        -- component of π⁻¹[D] − F containing p or q
theorem hagopian76_x2n_eq_one … (hFirr : T13 irreducibility) (hNP : NoPocket …) :
    LastIntervalReachesOne d π F c₁ D'
def Property4 … (i : ℕ) : Prop  -- with the set-up (K, h, f) of T12 and the blocks of St J
theorem hagopian76_property4_top … : Property4 … n
theorem hagopian76_property4_step … : Property4 … i → Property4 … (i - 1)
theorem hagopian76_theorem1_final : Hagopian76Thm1
```

## 6. Build provenance

The run started from a checkout with the compiled Mathlib files present and no local build outputs of
`HPC`.
1. `lake build HPC.Hagopian.Hagopian76R` was run first.
2. The new files were checked with `lake env lean`, then built with `lake build HPC.Hagopian.<file>`.
3. Then `lake build HPC`.
4. `axioms.txt` was regenerated with `lake env lean Axioms.lean > axioms.txt`; its first 1838 lines
   are unchanged.
