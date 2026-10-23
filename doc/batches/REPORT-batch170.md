Commission read: `doc/batches/COMMISSION-batch170.md` ("Commission: batch 170 — Part E, Hagopian 1976 XV: Theorem 1 — `ExtChainInter`; the covering half; \"follows\" for crossing components; Property 3; T15–T17 under `RsetDichotomy`").

# Report, batch 170

## 0. Summary

* **A (`ExtChainInter`): proved**, by the commission's route (`extChainInter_in`, `extChainInter`).
  No chain condition and no separation hypothesis are needed inside one extension `H`; for chains,
  the batch-169 `Prop` `ExtChainInter E (k⁻¹(0)) O p q` holds outright. **T13 is now
  unconditional** (`hagopian76_T13_uncond`).
* **B (the covering half): first step proved, the three cases open.** For a proper subcontinuum `K`
  of `M`, the closure of every component of `π⁻¹[D] − K` meets `π⁻¹[Fr D]`
  (`crossing_sides_cover_frontier`; `component_frontier_meets`, from
  `no_proper_subcontinuum_separates`). The bottom case, the `I₂` case and the side-edge pockets are
  not done.
* **C ("follows" for crossing components): proved** (`follows_crossing`), with the middle interval
  `(4/11, 7/11)` in place of the commission's `(3/11, 8/11)`.
* **D (Property 3): `crossing_set_closed` proved (with margins); the shift step and
  `hagopian76_property3` open.** The least `v` exists for the margin form
  (`hagopian76_first_crossing_param`). The obstruction is that the shift loses the margin (§1.D).
* **E (T15–T17, Theorem 1): open, not reached.** Waits on Property 3 and the covering half.
* **F (the dichotomy): not attempted.**
* **Nothing is refuted.** No defective proof is added; the count stays at fourteen.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76O` at the end of `HPC.lean`. All 19
new theorems use only `propext`, `Classical.choice` and `Quot.sound`. The regenerated `axioms.txt`
has 1788 lines (1769 + 19), and `sorryAx` appears in none of them. No declaration uses `sorry`; the
word occurs only in the comment block at the end of `Hagopian76O.lean`, which holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76O.lean`: the skeleton, with the delivered statements and the open items commented out.
* `H76ChainInter.lean`: `mem_layerSet_Icc_zero`, `extChainInter_in_aux`, `extChainInter_aux`.
* `H76Follows.lean`: `T9_pieces_aux`, `follows_crossing_aux`.
* `H76Cover.lean`: `component_frontier_meets`, `component_frontier_meets_of_subcontinuum`,
  `component_reaches_frontier_D`.
* `H76CrossClosed.lean`: `limsup_mem_of_tendsto`, `limsup_subset_of_eventually`,
  `limsup_isPreconnected`, `isClosed_crossing_params`, `crossing_set_closed`.

Earlier files edited: `Hagopian76N.lean`, one pointer line replacing the `ExtChainInter` open note.

## 1. The items

STATUS lines, in order: `STATUS: A proved`; `STATUS: A′ (T13 unconditional) proved`;
`STATUS: B open (first step proved)`; `STATUS: C proved`;
`STATUS: D open (crossing_set_closed proved with margins; shift and property 3 open)`;
`STATUS: E open (not reached)`; `STATUS: F open (not attempted)`.

### 1.A `ExtChainInter` — proved

**`extChainInter_in`.** Let `H` be an extension of `E` away from `k⁻¹(0)` (map `d`,
`layer d 0 = k⁻¹(0)`) and `c` a nonempty family of extensions of `E` away from `k⁻¹(0)`, all inside
`H`. Then `⋂ c` is an extension of `E` away from `k⁻¹(0)`.
1. For `Fᵢ ∈ c` (map `dᵢ`), `hagopian76_initial_segment` with `E := Fᵢ`, `k := dᵢ`, `F := H` gives
   `Fᵢ = d⁻¹[[0, sᵢ]]` (`layer d 0 = k⁻¹(0) = layer dᵢ 0`).
2. With `T = {sᵢ}` and `s* = inf T`: `x ∈ ⋂ c` iff `x ∈ H` and `d(x) ≤ sᵢ` for all `i`, iff
   `d(x) ≤ s*` (`le_csInf`, `csInf_le`). So `⋂ c = d⁻¹[[0, s*]]`.
3. `s* > 0`: otherwise `E ⊆ ⋂ c = d⁻¹(0) = k⁻¹(0)`, but `k` takes the value `1` on `E`.
4. `piece_map` (with `lsc_of_minimalAdmissible`) on `[0, s*]` gives a minimal admissible map on
   `⋂ c` whose layer over `0` is `layer d 0 = k⁻¹(0)`.

The commission's lower bound `s_E` is not needed, and neither are the chain condition and the
separation of the members.

**`extChainInter`** (the batch-169 `Prop`, unchanged statement): for a nonempty chain `c` and any
`F₀ ∈ c`, `⋂ c = ⋂ {F ∈ c | F ⊆ F₀}`, because every member is `⊆ F₀` or `⊇ F₀`. Then
`extChainInter_in` with `H := F₀`. So the commission's restriction "for chains inside a given `H`"
is not even needed.

**`hagopian76_T13_uncond`**: `hagopian76_T13` (batch 169) with `extChainInter` for its hypothesis.

### 1.B The covering half — first step proved; three cases open

**`component_frontier_meets`** (plane topology): if `O` is open and bounded, `Z` compact with
connected complement and `x ∈ O − Z`, then the closure of the component `U` of `x` in `O − Z` meets
`Fr O`. Otherwise `Cl U ∩ Zᶜ ⊆ U` (a point of `Cl U` off `Z` lies in `O`, and its own component,
open, meets `U`), so `U` is open and closed in the connected `Zᶜ`, hence `Zᶜ ⊆ U ⊆ O`, and the plane
would be bounded.

**`crossing_sides_cover_frontier`**: for a proper subcontinuum `K` of `M` (`d⁻¹[I]`, `d⁻¹[J]`, `P`
in T17), `no_proper_subcontinuum_separates` (batch 158) supplies the connected complement. With a
continuous `π` and `π⁻¹[D]` bounded, the closure of every component of `π⁻¹[D] − K` meets
`π⁻¹[Fr D]`, i.e. (by `hagopian76_D`) `π⁻¹` of `I₂`, of the bottom edge, or of a side edge.

**Open: the three cases.**
* *Bottom.* A component reaching `π⁻¹` of the bottom edge must be joined to the low part of the
  vertical. The bottom edge is `π⁻¹F[[a, b] × {0}]`, which contains layers of `E` (where `π` is not
  injective); the low strip below the lowest height of `K` has to be built in collar coordinates and
  shown to be connected after removing `K`. Not done.
* *`I₂`.* As commissioned: a thin neighbourhood of `I₂` inside `D`, minus `K`, connected (`K` misses
  `I₂` at positive distance). Not done.
* *Pockets at a side edge.* Not excluded by non-separation, as the commission says.

**What T17 needs (reading of pp. 348–349).** The positions used are those of `yᵢ`, `yᵢ₋₁` (points of
`K`, decided by `crossing_pair_separates` along `K₀`) and of `f(yᵢ)`, `f(yᵢ₋₁)`. Of the latter,
Hagopian says "Note that `f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`", and the covering is used once: "Hence
`f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`." `L₆` lies over abscissae in
`(5/11 − η, 8/11 + η)`, well inside `(3/22, 19/22)`, but a pocket bounded by `K` and a segment of a
side edge can reach that far, so the abscissa alone does not exclude it. What is needed is: **every
point of `L₆ ∩ π⁻¹[D] − d⁻¹[I ∪ J]` within `ε₃` of a point known to be above `d⁻¹[I]` (or below
`d⁻¹[J]`) is above `d⁻¹[I]` or below `d⁻¹[J]`**. With "below `Z`" redefined through the side edges
as well as the vertical (commission §1.B), the pocket case becomes a case of "below" or "above",
and the covering half reduces to the bottom and `I₂` cases plus a pocket argument along the side
edge. Shape proposal in §5.

### 1.C "Follows" for crossing components — proved

**`follows_crossing`.** In the set-up of `crossing_essential` (batch 167) there is `c > 0` such that
for every connected `B ⊆ M` over `F[[3/22, 19/22] × (0, c]]` whose closure meets both side edges:
`Cl B ∩ E = ∅`, and for an `ε₁`-homeomorphism `h` with Property 1's link condition
`h[piece (j + 1)] ⊆ Lⱼ`:
* `Cl B ⊆ h[E]`, `G = h⁻¹[Cl B] ⊆ E` is essential to `R(E)`;
* `Cl B ⊇ h[k⁻¹((4/11, 7/11))]`.

**Route.** `T9_pieces_aux` is the first half of `T9_aux` with the link condition of the homeomorphism
kept (it is the homeomorphism of Property 1 at a point of `B`). Link control at the left edge gives a
link `L_a ∋ x_L`, `a ≤ 2`, at the right edge `L_c ∋ x_R`, `c ≥ 8` (as in `crossing_essential_aux`).
For `x_L = h(e₁)`, `k(e₁) ∈ elev m₁` and `h(e₁) ∈ L_{m₁}` (link condition), so `L_{m₁}` meets `L_a`
and `m₁ ≤ a + 1 ≤ 3`, i.e. `k(e₁) ≤ 4/11`. Likewise `k(e₂) ≥ 7/11`. `layerSet_Ioo_subset` gives
`k⁻¹((k(e₁), k(e₂))) ⊆ G`.

**Difference from the commission.** The commission expected `G` to meet a layer in pieces `≤ 3` and one
in pieces `≥ 9`, giving `(3/11, 8/11)`. The chain property only gives `m ≤ a + 1`, so one link is lost
at each end: the bound is `(4/11, 7/11)`. Thus `Cl B` meets `L₄, L₅, L₆` along the translate (and
`L_a`, `L_c` at the ends). It does not show that `L₂, …, L₁₀` all meet `Cl B`.

**Is this enough for T17?** T17 uses "`L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and `Cl Cᵢ`" for: (i) "the
continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`" and (ii) the essentiality of `Cl Cᵢ₋₁` to
`h[R(E)]`. (ii) is given (the translate is `h[E]` with `h` small, essential by the two parameters).
For (i) the needed fact is that `N`, a subcontinuum of an extension `L` of `Cl Cᵢ` from `yᵢ` to
`yᵢ₋₁`, stays in the middle links, which uses the end sets of `Cl Cᵢ₋₁` and `Cl Cᵢ` being near the
side edges. `follows_crossing` places the parameters of the ends of `G` in `[0, 4/11]` and
`[7/11, 1]`, not near the end sets of `E`. So T17 (i) needs more than this weaker form: **the
translate must be small enough that its end pieces (`piece 1`, `piece 11`) lie outside `D`**, i.e.
the ends of `Cl Cᵢ₋₁` must be in `L₂` and `L₁₀`. This is where smallness is needed.

### 1.D Property 3 — `crossing_set_closed` proved; Property 3 open

**`crossing_set_closed`.** For a compact `F ⊆ M`, a continuous `d : F → [0, 1]` and closed sets `A`,
`B`, `W` of the plane, the set of `v` such that `d⁻¹(v)` contains a connected set inside `W` meeting
`A` and `B` is closed. Hence, if nonempty, it has a least element
(`hagopian76_first_crossing_param`).
* **Proof.** Take `vₙ → v` with connected `Zₙ ⊆ d⁻¹(vₙ) ∩ W`, points `aₙ ∈ Zₙ ∩ A`, `bₙ ∈ Zₙ ∩ B`. A
  subsequence has `aₙ → a`, `bₙ → b`. The upper limit `⋂_N Cl ⋃_{m ≥ N} Zₘ` lies in `W` and in
  `d⁻¹(v)`, contains `a ∈ A` and `b ∈ B`, and is connected.
* **`limsup_isPreconnected`** (compact Hausdorff, any connected `Zₙ` with a convergent selection).
  Given a closed cover `u ∪ v` of the upper limit `Λ` with `Λ ∩ u ∩ v = ∅` and `a ∈ u`, separate
  `Λ ∩ u`, `Λ ∩ v` by disjoint open `U`, `V`. Some `Cl ⋃_{m ≥ N} Zₘ − (U ∪ V)` is empty (directed
  family of closed sets with empty intersection), so `Zₘ ⊆ U ∪ V` for `m ≥ N`; `Zₘ` meets `U` near
  `a`, so `Zₘ ⊆ U`; hence `Λ ⊆ Cl U`, which misses `V ⊇ Λ ∩ v`.

**The margins.** Property 3's condition is: a component of `F ∩ π⁻¹[D]` contained in `d⁻¹(v)` whose
closure meets the *open* side edges `π⁻¹[(p₁, r)]`, `π⁻¹[(p₅, s)]`. Missing `E` and `π⁻¹[I₂]` and
meeting open edges are open conditions; they are not preserved by limits. So the closed set is
taken with margins: `A`, `B` are the closed edge segments `π⁻¹F[{a} × [μ, r₂ − μ]]`, etc., and `W`
the region over `F[[a, b] × [μ, c − μ]]`. This is the form commissioned (report 167 §5, "with
margins").

**Open: the shift and `hagopian76_property3`.** *Obstruction:*
1. The shift `g` (`hagopian76_property3_shift`, batch 161) is `δ`-small with `g[d⁻¹(v)] = d⁻¹(u)`,
   `u < v`. A connected `Q ⊆ d⁻¹(v)` crossing with margin `μ` goes to `g[Q] ⊆ d⁻¹(u)` crossing with
   margin `μ − δ` only. So `u` lies in the set for margin `μ − δ`, not `μ`, and the least `v` for
   margin `μ` is not contradicted. Lowering the margin each time gives no contradiction either: the
   least points `v_μ` decrease as `μ ↓ 0`, and their limit need not be a crossing parameter.
2. Hagopian's sentence "By Lemma 1 and Property 1, `L` follows a type A′ continuum in `d⁻¹(v)` that
   meets `L₆ ∩ π⁻¹[D]`" points to a margin-free route: by item C, `Cl Q` contains a middle translate
   `h[k⁻¹((4/11, 7/11))]`, so `d⁻¹(u) = g[d⁻¹(v)]` contains `gh[k⁻¹((4/11, 7/11))]`. Lemma T run in
   the ambient set `d⁻¹(u)` (`crossing_translate_in_aux`, batch 168) would recreate a crossing
   component of `F ∩ π⁻¹[D]` in `d⁻¹(u)` from scratch, with no margin bookkeeping. Two things are
   missing: Lemma T needs the translate by a small homeomorphism of a middle range *wider* than
   `[3/22, 19/22]` (it is applied to `k⁻¹[[a′, b′]]` with `a′ < a`, `b′ > b`), while item C gives
   only `(4/11, 7/11)`; and `g ∘ h` is `(δ + ε₁)`-small, while Lemma T's threshold is chosen after
   `D`. The first point is the same as §1.C's "translate must be small".
3. With these, the least `v` should be taken for the margin-free condition, whose closedness is then
   not known. A fix is to define the set through middle translates (closed under limits by
   `crossing_set_closed` applied with `A`, `B` the `ε₁`-neighbourhoods of two layers of `E`) and
   prove that every crossing component contains one (item C, strengthened).

### 1.E T15–T17, Theorem 1 — open (not reached)

* "It follows from Property 3 that `I` is finite": needs Property 3.
* `J`, the `xᵢ`: definitions; not formalized.
* Property 4, base case ("Note that `[x₁, x₂]` does not have Property 4"): `d⁻¹[[x₁, x₂]] = E`,
  which misses `π⁻¹[D]`, so it separates nothing in `π⁻¹[D]` — provided `yₙ`, `f(yₙ)` lie in one
  component of `π⁻¹[D] − E = π⁻¹[D]`, i.e. `π⁻¹[D]` connected. Not formalized.
* The induction ("Following Bing [2, p. 225]"), Cases 1 and 2: needs the covering half (§1.B), the
  first crossing component `Cᵢ₋₁` (its existence "follows from … an argument similar to the one for
  Property 3"), and the smallness of §1.C.

The assembly, if reached, would be stated as
`(∀ M E k, IsMinimalAdmissible E k → RsetDichotomy k) → Hagopian76Thm1` (commented-out shape at the
end of `Hagopian76O.lean`).

### 1.F The dichotomy — not attempted

## 2. Ledger entries (`LEDGER.md` §6, batch 170)

1. **p. 347, T13:** "Let F be a continuum that is irreducible with respect to the following
   properties … The existence of such a continuum F follows from Property 1 and the fact that
   Cl R(E) = Cl R(k⁻¹(0), E) (Lemma 6 (proof))." **Proved** (`hagopian76_T13_uncond`): Zorn with
   `extChainInter`. The argument used is Lemma 4 (strong form) and `piece_map`, not the printed
   reasons.
2. **p. 347, Property 3:** "Let v be the first point of [0, 1] such that d⁻¹(v) contains a component
   of F ∩ π⁻¹[D] whose closure meets π⁻¹[(p₁, r)] and π⁻¹[(p₅, s)]." **Proved with margins**
   (`crossing_set_closed`, `hagopian76_first_crossing_param`); for the printed open conditions,
   unargued. "By Lemma 1 and Property 1, L follows a type A′ continuum in d⁻¹(v) that meets
   L₆ ∩ π⁻¹[D]": proved in the weaker form of item C (`follows_crossing`). "This contradicts the
   definition of v": **unargued**; the shift loses the margin (§1.D). **Open.**
3. **p. 347:** "It follows from Property 3 that I is finite." Not reached. **Open.**
4. **p. 348, Property 4:** "Note that [x₁, x₂] does not have Property 4." Not reached; reduces to
   connectedness of `π⁻¹[D]` (§1.E). **Open.**
5. **pp. 348–349, the induction:** "Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J]." The first
   step of the covering is proved (`crossing_sides_cover_frontier`); the remaining cases are open.
   "Since L − {L₁, L₁₁} follows Cl Cᵢ₋₁ and Cl Cᵢ": the weaker form of item C does not suffice; the
   end pieces must lie outside `D` (§1.C). **Open.**
6. **The tacit dichotomy:** status unchanged (open; carried as `RsetDichotomy`). Theorem 1 is not
   verified, conditionally or otherwise.

No statement of Hagopian's is refuted. The count stays at fourteen.

## 3. Axioms

Group *Hagopian 1976 XV (batch 170)* of `Axioms.lean`; the per-theorem output is in
`doc/batches/audits/axioms-batch170.txt`. Each of the 19 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* `extChainInter_in`, `extChainInter`, `hagopian76_T13_uncond`, `crossing_sides_cover_frontier`,
  `follows_crossing`, `hagopian76_first_crossing_param`;
* `mem_layerSet_Icc_zero`, `extChainInter_in_aux`, `extChainInter_aux`;
* `T9_pieces_aux`, `follows_crossing_aux`;
* `component_frontier_meets`, `component_frontier_meets_of_subcontinuum`,
  `component_reaches_frontier_D`;
* `limsup_mem_of_tendsto`, `limsup_subset_of_eventually`, `limsup_isPreconnected`,
  `isClosed_crossing_params`, `crossing_set_closed`.

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
            │               │                │                    [B: first step; cases open]
T8/T9_full ─ crossing_essential ─ T12_parts12 │   isMeagre_Rset ─ exists_notMem_Rset
     │                                        │               │
 T9_pieces ─ follows_crossing [C]  T12_sides_aux ─ exists_generic_pq (p, q ∉ R(E); H separates)
                                              │
   Cl R(E) = M [open] ──► RsetDichotomy [open; hypothesis] ──► hagopian76_T12_of_dichotomy
                                              │
     extChainInter [A] ──► hagopian76_T13_uncond [A′]
                                              │
   crossing_set_closed [D, margins] ─ shift g ─ Property 3                [open]
                                              │
   T15–T17 (I finite; Property 4; Bing; covering cases; smallness of C)   [open]
                                              │
                               hagopian76_theorem1                        [open]
```

## 5. Skeleton proposal for what remains

```
-- B: positions through the vertical and the side edges
def belowSet' … (Z) : Set Pt  -- joined in π⁻¹[D] − Z to the vertical below Z or to a side edge
                               -- below the lowest point of Z on that edge
theorem crossing_sides_disjoint' … : Disjoint (belowSet' … Z) (aboveSet' … Z)
theorem crossing_sides_cover … (hK : Fold.Q78.IsContinuum K) (hKM : K ≠ univ) :
    π ⁻¹' (F '' D') \ toPt K ⊆ belowSet' … (toPt K) ∪ aboveSet' … (toPt K)
-- C, strengthened: the ends of a crossing component lie in L₂ and L₁₀
theorem follows_crossing_ends … : (toPt (closure B) ∩ L 1).Nonempty ∧ (toPt (closure B) ∩ L 9).Nonempty
-- D: a margin-free crossing set, closed through middle translates
theorem crossing_contains_middle_translate … ; theorem crossing_set_closed' …
theorem hagopian76_property3 … : ∀ v Z, Z ⊆ layer d v → … → ¬ Crossing Z
-- E
theorem hagopian76_I_finite … ; theorem hagopian76_property4_base … ;
theorem hagopian76_property4_step … ; theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1_cond :
    (∀ M E k, IsMinimalAdmissible E k → RsetDichotomy k) → Hagopian76Thm1
```

## 6. Build provenance

The run started from a checkout with no local build outputs of `HPC`; the compiled Mathlib files
were present. `lake build HPC` was run first (8632 jobs, success). Each new file was then checked
with `lake env lean`, then `lake build HPC.Hagopian.Hagopian76O`, then `lake build HPC`.
`axioms.txt` was regenerated with `lake env lean Axioms.lean > axioms.txt`.
