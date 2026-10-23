# Commission: batch 175 — Part E, Hagopian 1976 XX: Theorem 1 — layers of `F` along a translate; no deep pockets; `x₂ₙ = 1`; Property 4; the induction

**Go!** This batch runs on top of the batch-174 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch175.md`: this text, also pasted into the prompt.
* `Hagopian76T.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76T.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76T` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XX (batch 175)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

## 0. On batch 174

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1867 lines, with `sorryAx` in none, all on standard axioms. The
  extra wrapped line is explained in your report.

**Accepted.**
* Property 3 for every element, through a proper extension.
* **"`I` is finite"**, with your observation that the disjointness of interiors does not use
  Property 3.
* `hagopian76_J_xs`, with `e < x`.
* `hagopian76_property4_base`.

**The pocket problem is now the gateway.** It blocks `x₂ₙ = 1`, Property 4 for the top block, and
the induction. §1 proposes a route.

## 1. No deep pockets: a route

Notation: `F` is an extension of `E` away from `k⁻¹(0)`, with map `d`. "Over the middle" means over
`F[[3/22 + 2/11, 19/22 − 2/11] × (0, c]]`. Check each step.

**P1. Along a translate, the layers of `F` are the translated layers of `E`.**
* Setting: `h` is an `ε₁`-homeomorphism, `[a″, b″] ⊆ (0, 1)`, and `Q = h[k⁻¹[[a″, b″]]] ⊆ F`. Suppose
  `Q` misses `d⁻¹(0) ∪ d⁻¹(1)` and the layers `h[k⁻¹(t)]`, `t ∈ (a″, b″)`, miss the end sets of `F`.
  * `lemma3_half` gives `h[k⁻¹(t)] ⊆ d⁻¹(φ(t))` for a function `φ`.
  * `φ` is injective. If two translated layers lay in one layer of `F`, the swallowing lemma would
    put the whole translate `h[G]` in that layer, and D1 would give a layer crossing, contradicting
    Property 3. Check that D1's hypotheses hold here (one middle point over `D`), or argue
    injectivity directly from `translate_subset_layer`.
  * `φ` is continuous and monotone: an injective map from an interval whose image is an interval
    (`translate_params_ordConnected`).
* **Claim: `d⁻¹(φ(t)) = h[k⁻¹(t)]` for `t ∈ (a″, b″)`.** Let `U = d⁻¹(φ(t))` and `A = h[k⁻¹(t)]`,
  and suppose `U ≠ A`. Take `Y = U ∪ h[k⁻¹[[t − σ, t + σ]]]`. Then `Y − A` is the union of three
  mutually separated nonempty sets:
  * `U − A`;
  * `h[k⁻¹[[t − σ, t)]]`;
  * `h[k⁻¹((t, t + σ]]]`.

  The two translate pieces lie in layers `φ(t′) ≠ φ(t)`, so they miss `U` (injectivity of `φ`) and
  each other. So `Y` is a triod, contradicting atriodicity (Hagopian 1975 Lemma 1). Check that the
  three sets are separated (closures), and that `U − A ≠ ∅` suffices.
* So, along `Q`, the layers of `F` are the translated layers `h[k⁻¹(t)]`. Each lies within `ε₁` of
  `k⁻¹(t)`, so its points over the thin strip have abscissa `t` up to one piece
  (`IsEps1.sep_of_gap`, `pi_thin_near_layer`).

**P2. Every point of `F` over the middle lies on such a translate inside `F`.**
* For `y ∈ F` over the thin strip, link control puts `y` in some `Lⱼ`, `1 ≤ j ≤ 9`. Property 1
  gives an `ε₁`-homeomorphism `h` with `y ∈ h[E]` and `h[piece (j + 1)] ⊆ Lⱼ`.
* Choose `[a″, b″]` with `a″ < 3/22 − 1/11` and `b″ > 19/22 + 1/11`, so that `Q = h[k⁻¹[[a″, b″]]]`
  runs from left of the strip to right of it. By `EndCtl`, `Q` misses `k⁻¹(0) = d⁻¹(0)`.
* By no hair for `F` (`hagopian76_no_hair` with `F` in place of `E`, or `subset_of_meets_avoids`),
  `Q ⊆ F` provided `Q` misses `d⁻¹(1)`.
  * **The far end set `d⁻¹(1)` is the delicate case.** If it meets `Q`, replace `F` by a proper
    extension `F′` (as in A of batch 174). The layers are the same, and `d′⁻¹(1)` is new and lies
    beyond.
  * Check whether this can repeat. Each extension's end set could again meet `Q`. A compactness
    or Baire argument over the extensions may be needed; or choose `Q` shorter.

**P3. No deep pockets.** Let `C` be a non-crossing component of `F ∩ π⁻¹[D]`, whose closure meets the
left side segment but not the right one. **Claim: `C` does not reach over the middle.**
* Suppose `y ∈ C` is over the middle. Take `h` and `Q ⊆ F` from P2, and `φ` from P1.
* `Cl C` is a continuum in `F` (in `π⁻¹[Cl D]`) with irreducible interval `[u_a, u_b]`. It contains
  the layers `d⁻¹((u_a, u_b))` (batch 174, step 2).
* If `φ([a″, b″]) ⊆ [u_a, u_b]`, then `Cl C` contains translated layers `h[k⁻¹(t)]` with
  `t > 19/22 + 1/11`. Those lie right of the right side, outside `Cl D`. Contradiction.
* Otherwise, say `φ` is increasing and `u_b` lies in `φ((t_y, b″))`, where `y ∈ h[k⁻¹(t_y)]`.
  * Every point of `Cl C` in a layer `d⁻¹(u)`, `u ∈ (φ(t_y), u_b]`, lies in a translated layer
    `h[k⁻¹(t)]` with `t ≥ t_y` (by P1). So it lies at abscissa `≥ t_y − 1/11`, which is far from the
    left side.
  * On the other side, `u_a` lies below `φ(t_y)`, and the part of `Cl C` in `d⁻¹[[u_a, φ(t_y)]]` must
    contain the point where `Cl C` meets the left side.
  * Run the same argument there, and conclude that `Cl C` meets the left side only in layers
    `d⁻¹(u)`, `u < φ(t_y)`, which lie at abscissa `≤ t_y + 1/11`. That gives no contradiction yet.
* **The real point.** `C` is a component of `F ∩ π⁻¹[D]`. The union of `C` and the translated
  layers `h[k⁻¹(t)]` for `t ∈ [t_y, 19/22 + 1/11]` that lie over `D` is connected: consecutive
  translated layers are joined by `Q`. So `C` contains `Q ∩ π⁻¹[D]`'s component through `y`, which
  crosses by Lemma T's step 4 (boundary bumping in `Q`), without smallness.
  * The points of `Q` over the strip have abscissa monotone in `t` up to one piece.
  * The ends of `Q` are outside the strip on opposite sides.
  * `Q` misses `E` and `π⁻¹[I₂]`.

  So `C` is crossing. Contradiction.
* **Check this last bullet carefully. If it holds, P1 is not even needed:** P2 together with Lemma T
  step 4 (with coarse monotonicity in place of smallness, as in D1) shows that **every** component
  of `F ∩ π⁻¹[D]` through a point over the middle is crossing.
  * D1 already did this for `ψ[E]` inside a layer. Here the ambient set is `F`, and `Q ⊆ F` by P2.
  * D1's step 1 (missing `E`) is replaced by `Q ∩ E = ∅`. That needs care, since `h` is an
    `ε₁`-homeomorphism, not a small one. Apply no hair to the continuum `Q` and `E`: `Q` misses
    `k⁻¹(0)` by `EndCtl`. Does it miss `k⁻¹(1)`? If not, `Q ⊇ E`'s far part. Check.

**P4. Consequences.**
* **`CoverPocket` for the points that matter.** Points over the middle lie in crossing components,
  hence in no pocket. Check what the induction needs: `f(yᵢ₋₁) ∈ L₆`, over abscissae
  `(5/11 − η, 8/11 + η)`, inside the middle if the middle is taken as `[3/11, 9/11]` or so. Adjust
  the "2/11" margins above to make this fit.
* **`x₂ₙ = 1`.** Let `t > y*`, where `y*` is the last right endpoint of `I`. Then `d⁻¹((t, 1])`
  meets `π⁻¹[D]` only in non-crossing components, which by P3 avoid the middle. `p` and `q` are over
  the middle, near `x`. A path from `p` to `q` in `π⁻¹[D] − d⁻¹[[0, t]]` can be kept inside the
  middle, where `F − d⁻¹[[0, t]]` has no points. So `d⁻¹[[0, t]]` separates `p` from `q` whenever
  `F` does. Check the "kept inside the middle" step: a path avoiding `d⁻¹[[0, t]]` might need to
  leave the middle to get around crossing components of `d⁻¹[[0, t]]`. Use instead: `F` separates
  `p` from `q`, so (Janiszewski, compact form) some component of `F ∩ Cl` (…) separates. A
  component of the tail is shallow and cannot separate two middle points. Make this precise.
* **Property 4 (2) for the top block:** the same argument with `d⁻¹[[x₂ₙ₋₁, x₂ₙ]]` and the gaps
  between blocks.

## 2. Items

**A.** P1, P2, P3 (or the shortcut in P3's last bullet), and `cover_pocket_middle`.

**B.** `hagopian76_x2n_eq_one` (P4), so `LastIntervalReachesOne` for Hagopian's `F`.

**C.** Property 4 for `[x₂ₙ₋₁, x₂ₙ]`.

**D.** The induction, Cases 1–2, with P4 for the pockets.
* The `N` sentence: with P2, `N ⊆ L` over the middle lies on translates, so "`L − {L₁, L₁₁}`
  follows" holds locally.
* `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])` keeps `N` from crossing `I₁ ∪ I₂`.

Say what remains.

**E. The assembly**, `hagopian76_theorem1`, or a conditional form with named `Prop`s for exactly
what remains.

## 3. Order

A, B, C, D, E.

## 4. Places to check (candidate ledger entries)

1. **p. 348:** "Note that `x₂ₙ = 1`".
2. **p. 348:** Property 4 for the top block.
3. **pp. 348–349:** Cases 1 and 2: "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`"; "the
   continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`"; "Let `Cᵢ₋₁` be the first component …".
4. **Atriodicity in P1:** record it as a new use of Hagopian 1975 Lemma 1, if P1 is used.

## 5. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch175.txt`.
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
