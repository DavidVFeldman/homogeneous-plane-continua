# Commission: batch 173 — Part E, Hagopian 1976 XVIII: Theorem 1 — `Property3End` by descent; pockets; the ends of crossing components; T15–T17

**Go!** This batch runs on top of the batch-172 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch173.md`: this text, also pasted into the prompt.
* `Hagopian76R.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76R.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76R` at the end of `HPC.lean`.

No new sources are needed. **Upload only these two files at the start of the run.** Last time the
batch-171 files were uploaded again by mistake; you handled it correctly.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XVIII (batch 173)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

## 0. On batch 172

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1817 lines, with `sorryAx` in none, all on standard axioms.

**Accepted.**
* **The swallowing lemma** (`continuum_subset_layer_of_open`) and its consequences
  `translate_subset_layer`, `translate_extension_subset_layer` and
  `hagopian76_property3_translate`. This is the right reduction.
* `closure_Rset_subset_of_translate` and the two conditional forms of `Property3End`.
* `jordan_inner_collar`, `rect_frontier_domain`, and the `I₂` case
  (`crossing_sides_cover_schoenflies`).
* Your finding on pockets: Hagopian's "either above or below" has an unargued case. The ledger
  records it.

## 1. `Property3End` by descent: the shift no longer loses anything

Your remark (report 172 §1.A, note) is the key: what the least-`v` move must exclude is a layer
containing a whole translate. With the swallowing lemma, **the shift preserves crossing without
margins**. Check this argument.

**Lemma D1 (crossing from a translate in a layer).** Let `ψ : G → M` be **continuous** (not
necessarily a homeomorphism), with `dist(ψ(y), y) ≤ θ` for all `y`, where `θ < 2ε₁`. Suppose
`ψ[G] ⊆ d⁻¹(u)` for some `0 < u < 1`, and suppose `ψ[k⁻¹(t)] ⊆ π⁻¹[D]` for all
`t ∈ [4/11, 7/11]`. Then:
1. **`u > s`.** Otherwise `d⁻¹(u)` is a layer of `E`. It lies in at most two adjacent pieces, yet
   contains points within `θ < 2ε₁` of piece 1 and of piece 11. This contradicts `IsEps1.sep`
   (`4ε₁`). Hence `d⁻¹(u) ∩ E = ∅` (`layer_disjoint_of_not_subset`), and so `ψ[E] ∩ E = ∅`.
2. **`ψ[E]` misses `π⁻¹[I₂]`**, since it lies in `M`.
3. **The ends lie outside.** `ψ[k⁻¹(0)]` is within `θ` of `k⁻¹(0)`. By `EndCtl` (`4ε₁`) and
   `pi_thin_near_layer` (points over the thin strip lie within `η` of `k⁻¹[[3/22, 19/22]]`), it is
   not over the closed strip, hence not in `π⁻¹[Cl D]`. Likewise for `ψ[k⁻¹(1)]`.
4. **Coarse monotonicity.** A point of `ψ[piece m]` over the thin strip at abscissa near `t` lies
   within `θ + η < 4ε₁` of both piece `m` and the layer `t`. So piece `m` and the piece of `t` are
   adjacent (`IsEps1.sep`). Hence `Z_L = ψ[k⁻¹[[0, 5/11]]]` meets `π⁻¹[Cl D]` only at abscissae
   `< 19/22`, and `Z_R = ψ[k⁻¹[[6/11, 1]]]` only at abscissae `> 3/22`.
5. **Crossing.** This is Lemma T, step 4, with `ψ` in place of `h`:
   * boundary bumping in `Z_L` from the layer `ψ[k⁻¹(5/11)] ⊆ π⁻¹[D]` gives a point over the left
     open edge;
   * the same in `Z_R` gives a point over the right open edge;
   * the middle `ψ[k⁻¹[[4/11, 7/11]]]` is connected and inside `π⁻¹[D]`.

   So `d⁻¹(u) ⊇ ψ[E]` contains a connected subset of `F ∩ π⁻¹[D]` whose closure meets both open side
   edges.

**Lemma D2 (descent).** Suppose a crossing lies in `d⁻¹(v)`. Then `hagopian76_property3_translate`
gives an `ε₁`-homeomorphism `h` with `h[G] ⊆ d⁻¹(v)` and `h[k⁻¹((4/11, 7/11))] ⊆ Cl B`.
* `h[k⁻¹[[4/11, 7/11]]]` lies in `π⁻¹[D]` at a positive distance `ρ₀` from its complement. This needs
  checking at the closed ends `4/11`, `7/11`: use a slightly smaller closed interval inside
  `(4/11, 7/11)` and adjust D1 accordingly.
* For `δ < ρ₀`, the shift `g` (`hagopian76_property3_shift`) gives `u < v` with
  `g[d⁻¹(v)] = d⁻¹(u)`. So `ψ = g ∘ h` satisfies D1 with `θ = ε₁ + δ` and keeps the middle in
  `π⁻¹[D]`.
* Hence a crossing lies in `d⁻¹(u)`. **No margin is lost**: D1 recreates the crossing from the ends
  of the translate.

**Closing the argument: a closed set of continua, not of maps.** Iterating D2 accumulates the
shifts. Composites `gₙ ⋯ g₁ h` have bounds `ε₁ + Σ δᵢ`, and maps chosen along a sequence of
parameters need not converge (no equicontinuity). So the least element should be taken over a set
defined by continua with closed properties, not by maps.

**Definition.** Fix compact sets:
* `X₀`, the points of `M` within `2ε₁` of `k⁻¹(0)`;
* `X₁`, the same for `k⁻¹(1)`;
* `K_mid ⊆ π⁻¹[D]`, a compact neighbourhood of `h[k⁻¹[[4/11 + ζ, 7/11 − ζ]]]` with
  `dist(K_mid, complement of π⁻¹[D]) > 0`.

Let `T` be the set of `u ∈ (0, 1)` such that `d⁻¹(u)` contains a continuum `Γ` that meets `X₀`,
`X₁` and `K_mid`, and satisfies a closed form of D1.4 (coarse monotonicity). One possible form: `Γ`
is the union of continua `Γ₀ ∋ X₀`-point and `Γ₁ ∋ X₁`-point, meeting in `K_mid`, with
`Γ₀ ∩ π⁻¹[Cl D]` at abscissae `≤ 9/11 + η` and `Γ₁ ∩ π⁻¹[Cl D]` at abscissae `≥ 2/11 − η`.

* **`T` is closed:** hyperspace limits, as in `crossing_set_closed`, and upper semicontinuity of the
  layers.
* **`T` is nonempty:** `ψ = h` from `hagopian76_property3_translate`, with `Γ = h[E]`.
* **`0 ∉ Cl T`**, and every `u ∈ T` has `u > s`: D1.1 forbids layers in `E`.
* **From any `u ∈ T`, D1 gives a crossing in `d⁻¹(u)`.** Boundary bumping in `Γ₀` and `Γ₁` from
  `K_mid`. Hence, by D2, `h′[G] ⊆ d⁻¹(u)` for an `ε₁`-homeomorphism `h′`
  (`hagopian76_property3_translate` again). The shift gives `u′ < u` with `gh′[G] ⊆ d⁻¹(u′)`.
* **To place `u′` in `T` again,** the continuum `gh′[E]` must meet the same fixed `X₀`, `X₁`,
  `K_mid`.
  * `X₀` and `X₁` are fine: `h′` is `ε₁`-close, `g` is `δ`-close, and `ε₁ + δ < 2ε₁`.
  * `K_mid` is the delicate point. `h′` is a new homeomorphism whose middle is near the crossing in
    `d⁻¹(u)`, not necessarily near the fixed `K_mid`.
  * Fix: define `K_mid` as the closed set of points over `F[[5/11, 6/11] × [μ, c₀ − μ]]`, a compact
    piece of the thin band in the middle of `D`. Every crossing meets it, because a crossing passes
    the middle abscissae inside `D`, at heights bounded away from `0` and `c₀` by compactness and
    `Cl B ∩ E = ∅`. **Here the margin `μ` reappears.** Check whether `μ` can be chosen uniformly.
    For example: crossings in layers `d⁻¹(u)`, `u > s`, stay at height `≥ μ` above the axis over
    `[5/11, 6/11]`, uniformly in `u`, because the layers beyond `E` are at a positive distance from
    `E`. That fails as `u ↓ s`. Say what you find.
* So the least element of `T` contradicts D2.

If this works, `Property3End` is not needed. Property 3 is then proved by the least `u` of a closed
set, where the shift from the minimum produces a smaller element. That is Hagopian's argument, with
the swallowing lemma supplying what "By Lemma 1 and Property 1" was meant to give.

## 2. Items

**A. Property 3 by descent** (§1): `crossing_from_layer_translate` (D1), `crossing_descends` (D2),
and the closed formulation with the least element. Then `hagopian76_property3` unconditionally.

**B. Pockets** (`CoverPocket`). With Schoenflies square coordinates in hand:
* Does a point of `L₆ ∩ π⁻¹[D]` lie in a pocket of `Cl Cᵢ₋₁`? Link control puts `L₆` in the middle
  abscissae.
* A pocket component `P` touches `∂D′` only in a side segment `σ`. Every component of the pocket's
  complement in `D′` reaches the top or the bottom.
* Can `Cl Cᵢ₋₁` (a crossing continuum, essential to `h[R(E)]`, containing a middle translate
  `h′[k⁻¹((4/11, 7/11))]`) bound a pocket that reaches the middle abscissae? Coarse monotonicity
  (D1.4) of the translate inside `Cl Cᵢ₋₁` should confine pocket-forming excursions to the end
  pieces, near the sides. State what you can prove.

**C. The ends of crossing components** (`CrossingEnds`). D1 suggests that crossing continua
containing a translate with ends outside `D` are the natural objects. Check whether T17 can be run
with "crossing continuum containing a translate as in D1" in place of "crossing component", and
whether that settles "the continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`".

**D. T15–T17 and `hagopian76_theorem1`**, as far as A–C allow, with named `Prop`s for anything left
open.

## 3. Places to check (candidate ledger entries)

1. **p. 347, Property 3:** the four sentences, with the final status.
2. **p. 347:** "It follows from Property 3 that `I` is finite".
3. **p. 348:** Property 4 and its base case.
4. **pp. 348–349:** the induction; pockets; "the continuum `N` …"; "Let `Cᵢ₋₁` be the first component
   …".

## 4. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch173.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s are `def … : Prop`, listed in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
