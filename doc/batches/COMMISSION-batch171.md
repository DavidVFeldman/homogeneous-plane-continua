# Commission: batch 171 — Part E, Hagopian 1976 XVI: Theorem 1 — Property 3 without margins; positions through the side edges; the ends of crossing components; T15–T17

**Go!** This batch runs on top of the batch-170 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch171.md`: this text, also pasted into the prompt.
* `Hagopian76P.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76P.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76P` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XVI (batch 171)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

## 0. On batch 170

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1788 lines, with `sorryAx` in none, all on standard axioms.

**Accepted.**
* `extChainInter`, without the chain or separation conditions. **T13 is unconditional**
  (`hagopian76_T13_uncond`).
* `crossing_sides_cover_frontier`.
* `follows_crossing`, with the interval `(4/11, 7/11)`. Your correction of my `(3/11, 8/11)` is
  right: the chain condition loses one link at each end.
* `crossing_set_closed` and `hagopian76_first_crossing_param`.
* Your analysis of the shift and the margin (§1.D), and your proposed repair 3.

## 1. Notes

**A. Property 3: two routes. Try the first; fall back to the second.**

1. **Your repair** (report 170 §1.D, item 3). Define the crossing set through middle translates:
   * `v` is a crossing parameter if `d⁻¹(v)` contains `h[k⁻¹[[α, β]]]` for some `ε₁`-homeomorphism
     `h` and fixed `α < β` in the middle range.
   * The set is closed by `crossing_set_closed`, applied with `A`, `B` neighbourhoods of the layers
     over `α` and `β`. Homeomorphisms do not converge, but the continua do. Check that the limit
     continuum is again a middle translate, or make the definition use only what the limit
     provides: a continuum in the layer meeting two compact sets.
   * Every crossing component contains one middle translate (`follows_crossing`). The shift `g`
     carries a middle translate in `d⁻¹(v)` to the middle translate `gh[k⁻¹[[α, β]]]` in `d⁻¹(u)`.
     With `ε₁` budgeted so that `gh` is still an `ε₁`-homeomorphism (shrink `δ`), no margin is
     lost.
2. **A direct triod argument, without `v`.** Suppose a layer `C = d⁻¹(v)` of `F` contains
   `h[k⁻¹[[α, β]]]`, with `h` small and `0 < α < β < 1`.
   * By no hair applied to `h[E]` (with `k ∘ h⁻¹`; use pieces `h[k⁻¹[[α′, β′]]]` with `α′ < α`,
     `β′ > β` if `C` reaches the end sets), `C ∩ h[k⁻¹[[α′, β′]]]` spans layers `α` to `β` of
     `h[E]`.
   * Now `C` is one layer of `F`. Lemma 4's strong form says every layer of a type A′ subcontinuum
     essential to the line is a layer of the line. Hence `h[k⁻¹[[α′, β′]]]` cannot lie in `F` with
     several of its layers inside the single layer `C`. So it leaves `F` on at least one side.
   * `C` with the two arms of `F` (`d⁻¹[[0, v)]`, `d⁻¹((v, 1]]`) and an arm of `h[E]` outside `F`
     is then a triod, which is impossible.
   * Check whether the arm of `h[E]` outside `F` can coincide with an arm of `F`, and whether
     `0 < v < 1` is needed. If this works, Property 3 needs no least `v` at all, and the margin
     problem disappears. Record it as a replacement for the printed proof.

**B. Positions through the side edges** (your proposal, report 170 §5, accepted). Define `belowSet′`
and `aboveSet′`. A point is below `Z` if it is joined, in `π⁻¹[D] − Z`, to the vertical below `Z`
or to a side edge below the lowest point of `Z` on that edge. Above is the same with the top.
* Prove disjointness, for crossing `Z` as in `crossing_sides`.
* Prove the covering, for proper subcontinua `K` of `M`:
  * **Bottom case.** `K` misses `E`, which is compact, so `K` lies above a positive height `c_K`
    over `[a, b]`. The strip `F[(a, b) × (0, c_K)]` is connected, lies in `D`, misses `π[K]`, and
    meets the vertical. Pull back by `π`, which is injective over `D`.
  * **`I₂` case.** Use a thin neighbourhood of `I₂` in `Cl D`. Pull back `I₂` to the arc `I` in
    collar coordinates. The set of points of `D′` within `δ` of `I` is connected for small `δ`: it
    is the union of the balls around points of `I`, intersected with `D′`. Each such intersection
    is connected for small `δ` (the frontier of `D′` near `I` is `I`). Take `δ < dist(I, K′)`.
  * **Side edges.** A component touching a side edge touches it at a point that is either below
    the lowest point of `Z` on that edge, hence below; or above its highest point, hence above; or
    in a pocket between two points of `Z` on the edge. With the new definitions, show that a pocket
    component is joined, along the side, to a part already counted, or that T17 never needs it
    (report 170 §1.B: the points `f(yᵢ₋₁) ∈ L₆` are within `ε₃` of points with known positions).

**C. The ends of a crossing component** (report 170 §1.C). T17 (i) needs the end pieces of
`Cl Cᵢ₋₁` outside `D`. Two ways:
* **Smallness.** Prove that every crossing component essential to `h[R(E)]` contains a point
  `h′(x′)` with `h′` `δ`-small and `k(x′)` in the middle range. Then Lemma T applies. One possible
  argument: by `follows_crossing`, `Cl C ⊇ h[k⁻¹((4/11, 7/11))]` with `h` an `ε₁`-homeomorphism.
  Pick `y` in it, low enough. Use `pi_thin_near_layer` and Effros (as in `K0_low_point_aux`) to
  write `y = h′(x′)` with `h′` small. `C` reaches low near the left edge, because its closure meets
  the left edge and `E` lies just below.
  * **Is that so?** Not in general, but crossing components inside `Cl R(E)` near `E` should. Say
    what you find.
* **Finer links.** Rerun link control with `η` smaller than one piece. The loss is from the chain
  condition, not from `η`, so this will not help unless the chain is refined. Say whether refining
  `L` (more links, same Property 1) is cheap.

**D. T15–T17 and the assembly `hagopian76_theorem1_cond`**, under `RsetDichotomy`.

**E. The dichotomy, optional.** A route not tried yet: avoid it by choosing `h` and `h₁` generically
in the homeomorphism group.
* `Homeo(M)` with the sup metric is a Polish group, and by Effros, evaluation at `x` is open.
* The "bad" set `{g : g[R(E)] ∩ R(E) ≠ ∅}` is a countable union of closed sets
  `{g : g[Fₙ] ∩ Fₘ ≠ ∅}`, with `Fₙ` cofinal extensions on both sides.
* If each of these closed sets is nowhere dense, a generic `h` with `h(x)` in a given open set has
  `h[R(E)] ∩ R(E) = ∅`, and the dichotomy is not needed.
* The point to check: given continua `A = g[Fₙ]` and `Fₘ` that meet, is there an arbitrarily small
  homeomorphism `g′` with `g′[A] ∩ Fₘ = ∅`? I do not know. In an atriodic, hereditarily unicoherent
  `M`, meeting continua overlap rather than cross, which suggests yes. Report what you find, even if
  negative.

## 2. Order

A, B, C, D, E.

## 3. Places to check (candidate ledger entries)

1. **p. 347, Property 3:** "Let `v` be the first point …"; "By Lemma 1 and Property 1, `L` follows a
   type A′ continuum in `d⁻¹(v)` that meets `L₆ ∩ π⁻¹[D]`"; "By Lemmas 2 and 3, a homeomorphism `g`
   … and a point `u` of `[0, v)` exist such that `g[d⁻¹(v)] = d⁻¹(u)` …"; "This contradicts the
   definition of `v`". If route A.2 works, record the printed route as not needed.
2. **p. 347:** "It follows from Property 3 that `I` is finite".
3. **p. 348:** Property 4 and "Note that `[x₁, x₂]` does not have Property 4".
4. **pp. 348–349:** the induction, Cases 1 and 2; "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below
   `d⁻¹[J]`"; "the continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`"; "Let `Cᵢ₋₁` be the first
   component …".
5. **The dichotomy:** status.

## 4. Deliverables

1. The items of §1.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch171.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * if D is not finished, a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
