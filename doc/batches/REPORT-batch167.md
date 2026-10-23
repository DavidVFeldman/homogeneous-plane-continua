Commission read: `doc/batches/COMMISSION-batch167.md` ("Commission: batch 167 — Part E, Hagopian 1976 XII: Theorem 1 — crossing translates; the `p`-components; T12, Property 3, T13; then T15–T17").

# Report, batch 167

## 0. Summary

* **A (Lemma T, Lemma T′): proved.** `crossing_translate` and `K0_dense_low`. Every step of
  commission §1 goes through. Three steps are done by a different argument than the one sketched;
  details are in §1.A.
* **B (T12): parts (1)–(2) proved in a shape I chose; part (3) open.**
  * `hagopian76_T12_parts12`: Hagopian's `x`, and for every small `h` a crossing `p`-component
    `C ∋ p = h(x)` with `C ⊇ h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]`. `Cl C` is carried into a translate
    `h′[E]`, and `h′⁻¹[Cl C]` is essential to `R(E)`.
  * The same with `C` replaced by any connected set over the thin strip whose closure meets both
    side edges: `crossing_essential`.
  * The choice of `p`, `q` in distinct composants of `Cl R(E)`, and the separation by `R(E)`, are
    open (§1.B).
* **C (Property 3), D (T13), E (T15–T17, Theorem 1): not reached.** §1.C–E say what I checked and
  what is missing. §5 has a skeleton proposal.
* **F: not attempted.**
* **Nothing is refuted.** No defective proof is added; the count stays at fourteen.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76L` at the end of `HPC.lean`. All 18
new theorems use only `propext`, `Classical.choice` and `Quot.sound`. The regenerated `axioms.txt`
has 1722 lines (1704 + 18), and `sorryAx` appears in none of them. No declaration uses `sorry`. The
only occurrences of the word are in the comment block at the end of `Hagopian76L.lean`, which holds
the open shape proposals.

Files:
* `HPC/Hagopian/Hagopian76L.lean`: the skeleton, with the delivered statements.
* `H76Translate.lean`:
  * boundary bumping for components (`exists_mem_closure_component_notMem`);
  * the collar is open on open subsets of the open rectangle (`isOpen_collar_image`);
  * uniform collar coordinates (`collar_uniform`, `pi_near_collar`).
* `H76TranslateMain.lean`: Lemma T (`crossing_translate_aux`).
* `H76K0Dense.lean`: Lemma T′ (`K0_low_point_aux`, `K0_dense_low_aux`) and the crossing
  `p`-components (`T12_crossing_aux`).
* `H76CrossEss.lean`: `crossing_essential_aux` and `T12_parts12_aux`.

## 1. The items

STATUS lines, in order: `STATUS: A proved`; `STATUS: B parts (1)–(2) proved (shape), (3) open`;
`STATUS: C open (not reached)`; `STATUS: D open (not reached)`; `STATUS: E open (not reached)`.

### 1.A Lemma T and Lemma T′ — proved

**Set-up.** Everything is stated for a general interval `[a, b]` (Hagopian: `[3/22, 19/22]`). The
hypotheses on `I₂`, `D′` and `F[D′]` are exactly the conclusions of `hagopian76_D`. Fix
`0 < a′ < a` and `b < b′ < 1`.

**`crossing_translate` (Lemma T).** There is a height `c₀ > 0` with three properties: the low strip
`(a, b) × (0, c₀)` lies in `D′`, and `c₀ < r₂`, `c₀ < s₂`. For every `ζ > 0` and `η > 0` there is
`δ > 0` such that the following holds. Take `x ∈ E` with `k(x) ∈ [a + ζ, b − ζ]`, and a
`δ`-homeomorphism `h` of `M` with `h(x) ∉ E` and `π(h(x)) ∈ F[[0, 1] × (0, 1]]`. Then:
1. `Q = h[k⁻¹[[a′, b′]]]` misses `E`;
2. every `y ∈ k⁻¹[[a′, b′]]` has `π(h(y)) = F(z)` with `z ∈ (0, 1) × (0, c₀)` and
   `|z − (k(y), 0)| < η`;
3. `h[k⁻¹[[a + ζ/2, b − ζ/2]]] ⊆ C`, where `C` is the component of `M ∩ π⁻¹[D]` through `h(x)`;
4. `Cl C` meets `π⁻¹F[{a} × (0, r₂)]` and `π⁻¹F[{b} × (0, s₂)]`.

Step-by-step check of commission §1:
1. **`Q ∩ E = ∅`: as in the commission.**
   * `Q` misses `k⁻¹(0)` and `k⁻¹(1)`: by step 2, `π(h(y)) = F(z)` with `z` in the *open*
     rectangle, while `π[k⁻¹(0)] = F(0, 0)` and `π[k⁻¹(1)] = F(1, 0)`, and `F` is injective on the
     closed rectangle. No separate distance estimate is needed.
   * `hagopian76_no_hair` then applies to the continuum `Q` and the point `h(x) ∈ Q − E`.
2. **The band: as in the commission, by another route.**
   * *Route.* I did not use `pi_thin_near_layer`. Two uniform continuity facts give the estimate
     uniformly in `t`:
     * `π` is uniformly continuous on `M`;
     * the inverse of the collar is uniformly continuous on `F[[0, 1] × [−1, 1]]`.
     Points within `ρ` of `F(t, 0)`, `t ∈ [a′, b′]`, are `F(z)` with `z` in a thin open box around
     the axis and `|z − (t, 0)| < η` (`collar_uniform`). The box image is open
     (`isOpen_collar_image`), and a thickening of the compact set `F[[a′, b′] × {0}]` lies in it.
   * *The side of the axis.* `π[Q]` misses the axis, because a point of `M` over the axis lies in
     `E` (`mem_layer_of_pi_eq_gamma`). So `π[Q]` is a connected set inside the union of the open
     upper half `F[(0, 1) × (0, 1)]` and the open lower half `F[(0, 1) × (−1, 0)]`. These halves are
     disjoint. `π[Q]` contains `π(h(x))`, which is in the upper half, so all of `π[Q]` is there.
3. **Layer by layer: as in the commission.** Take `η ≤ ζ/2` and `η < c₀`. For
   `t ∈ [a + ζ/2, b − ζ/2]` the coordinates fall in `(a, b) × (0, c₀) ⊆ D′`. The layers with
   `t ≤ a − ζ/2` or `t ≥ b + ζ/2` are not used; only the end layers `t = a′` and `t = b′` are,
   in step 4.
4. **The `h(x)`-component crosses: as in the commission.**
   * The middle set `h[k⁻¹[[a + ζ/2, b − ζ/2]]]` is connected, lies in `M ∩ π⁻¹[D]` and contains
     `h(x)`, so it lies in `C`.
   * Boundary bumping in `Z = h[k⁻¹[[a′, a + ζ/2]]]` (`exists_mem_closure_component_notMem`, new). If
     `Z` is a continuum, `O` is open, `p ∈ Z ∩ O` and `Z ⊄ O`, then the closure of the component of
     `Z ∩ O` through `p` contains a point of `Z − O`.
     * The proof applies `exists_continuum_bump_compact` to `Z ∩ {dist(·, Oᶜ) ≥ r/2}`, where `r` is
       the least distance from the closure of the component to `Oᶜ`.
     * `Z ⊄ π⁻¹[D]`: the layer `t = a′` has abscissa `< a′ + η ≤ a`.
   * The point `q` found this way is in `Cl C − π⁻¹[D]`, so `π(q) ∈ Fr F[D′]`. By the frontier
     formula of `hagopian76_D` it lies on `I₂`, the bottom, the left edge or the right edge.
     * Not on `I₂`: its height is `< η < c₀`, and `I₂` lies above `c₀`.
     * Not on the bottom: its height is positive (step 2).
     * Not on the right edge: its abscissa is `< a + ζ < b`.
   * So `q ∈ π⁻¹F[{a} × (0, r₂)]`, using `c₀ < r₂`. The right side is symmetric.
   * Two hypotheses of the set-up, `0 < a` and `b < 1`, are not needed. They follow from
     `0 < a′ < a` and `b < b′ < 1`.

**`K0_dense_low` (Lemma T′).** For `t₀ ∈ (a, b)` there is `x ∈ k⁻¹(t₀)` with the following
property. Within any `ε > 0` of `x` some `q ∈ M` has `π(q) = F(t₀, u)` with `0 < u < ε`. Hence
`x ∈ Cl(M ∩ π⁻¹F[{t₀} × (0, w₂)])` for every `w₂ > 0`, which is `Cl(M ∩ K₀)` for the `K₀` of
`hagopian76_K0`.

Step-by-step check:
* **"Take `x₀ ∈ k⁻¹(11/22)` and points `y ∈ M − E` above, near `x₀`": changed.**
  * `M_meets_above` gives points of `π[M]` above the axis near the vertical, but not near a
    *prescribed* `x₀`.
  * Instead, take any `y` over `(t₀ − ζ, t₀ + ζ) × (0, c₁)`. `pi_thin_near_layer` gives a point
    `e ∈ E` near `y` with `k(e)` near `t₀`.
  * The homeomorphism `h` with `h(e) = y` comes from Effros' theorem
    (`effros_homogeneous_set`, the uniform form of Lemma 2). Lemma 2 at a fixed point would not
    give a `δ` that works for the varying `e`.
* **"π[h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]] … meets the vertical over `11/22` below `w`": as in the
  commission.**
  * Lemma T gives coordinates within `η` of the layers. The end layers lie strictly left and
    strictly right of `t₀`.
  * If the connected image missed the vertical, the disjoint open sets `F[(0, t₀) × (0, 1)]` and
    `F[(t₀, 1) × (0, 1)]` would separate it.
* **"By upper semicontinuity, a subsequence converges to a point `x ∈ k⁻¹(11/22)`": as in the
  commission.**
  * Compactness of `M` gives a convergent subsequence.
  * The limit satisfies `π(x) = F(t₀, 0) = γ(t₀)`, because `F` is continuous on the closed
    rectangle. So `x ∈ k⁻¹(t₀)` by `mem_layer_of_pi_eq_gamma`.

### 1.B T12 — parts (1)–(2) proved in a shape I chose; part (3) open

**`hagopian76_T12_parts12`.** The set-up has a height `c₉ > 0`. Build `D` over `[3/22, 19/22]` at
a height `c ≤ c₉`; this is possible because `hagopian76_T7` gives `I₂` at every height
`c′ ≤ c`. Let `t₀ ∈ (3/22, 19/22)`. Then there are `x ∈ k⁻¹(t₀)` and `ζ > 0` such that for every
`ε > 0` some `ε`-homeomorphism `h` has these properties:
* `p = h(x)` lies within `ε` of `x`, is off `E`, and lies on the vertical over `t₀` at a height
  `< ε`. So `p ∈ M ∩ K₀ ∩ W` for `ε` small.
* The `p`-component `C` of `M ∩ π⁻¹[D]` contains `h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]` and is
  crossing.
* `Cl C ⊆ h′[E]` for an `ε₁`-homeomorphism `h′`, and `h′⁻¹[Cl C]` is essential to `R(E)`.

**(2), "the closure of the p-component C … is essential to h[R(E)]".** This is
`crossing_essential`: a connected set over the thin strip of T8/T9 whose closure meets both side
edges is carried by T9 into a translate, and is essential there.
* At the left edge (abscissa `3/22`) the closure meets a link of index `≤ 2`, by
  `hagopian76_link_control` with `η ≤ 1/100`.
* At the right edge it meets a link of index `≥ 8`. Since `2 + 3 ≤ 8`, T9's essential clause
  applies.
* *Shape difference.* The homeomorphism is T9's `h′`, not Hagopian's `h` with `h(x) = p`. Showing
  that the same `h` works would need `h⁻¹[Cl C] ⊆ E`, Hagopian's "by Lemma 5", and I have not
  proved it.

**(1)** is the definition `f = h₁h⁻¹`, with `h₁(x) = q`. It waits on the choice of `q` in (3).

**(3) and the choice of `p`, `q`: open.** Points checked:
* **Is `Cl R(E) = M`?** Not settled; I have neither a proof nor a counterexample.
  * Hagopian treats `Cl R(E)` as a possibly proper subcontinuum (p. 343: "Since M is atriodic, R(E)
    is a composant of Cl R(E)").
  * If it is proper, it is nowhere dense in `M`. Then the points `p = h(x)` of Lemma T′ need not lie
    in `Cl R(E)`: they lie in the translate `h[E]`, and `h[E] ⊆ R(E)` is not known.
* **Composants of the points `p = h(x)` of Lemma T′.** The commission proposes: the crossing
  components through these points are pairwise disjoint or equal, and one composant contains only
  countably many disjoint crossing ones. **Checked: this does not follow from general continuum
  theory.**
  * A composant is a countable union of proper subcontinua, and one proper subcontinuum can contain
    uncountably many pairwise disjoint crossing continua.
  * Example: the Cantor comb `(Cantor set × [0, 1]) ∪ ([0, 1] × {1})` is a continuum. In the strip
    `[0, 1] × (0, 1)` it contains uncountably many disjoint arcs crossing from bottom to top.
  * So the claim needs a property specific to `M`, for example that each crossing component's
    closure is essential to a translate `h[R(E)]` (proved above for T9's `h′`) together with a
    finiteness statement for disjoint essential continua inside one proper subcontinuum. I have no
    proof of such a statement and no counterexample.
* **"By Property 1, R(E) intersects an arc in K that is irreducible between C and the q-component
  … and R(E) separates these components in π⁻¹[D]": open.**
  * Lemma T gives crossing *translates* `h[E]`, and these are not known to lie in `R(E)`.
  * The commission suggests sub-arcs of the "line" `R(E)` near `E`. But `R(E)` is a union of
    extensions of `E`, not an arc. A connected piece of `R(E) − E` close to `E` would need a type A′
    extension `F ⊋ E` whose layers near the end set `k⁻¹(1)` lie near `E`. Applying Lemma T to such
    a piece needs the analogue of step 1 (the piece misses `E`) and of step 2 (it lies above the
    axis). Neither is argued.
  * The ordering of crossing continua along `K₀` by height, and the three-part cut of `D` by two
    disjoint crossing continua, are planar facts. I did not formalize them, because the crossing
    pieces of `R(E)` they would be applied to are not available.

### 1.C Property 3 — open (not reached)

Same position as batch 166 §1.D. On the commission's question about the form: T15–T17 use crossing
components in two places.
* **The finiteness of `I`.** Here a crossing *continuum* `Z ⊆ F ∩ π⁻¹[Cl D] − E` is enough, if
  `Z` misses `π⁻¹[I₂]`.
* **The separation "d⁻¹[J] separates yᵢ from f(yᵢ) in π⁻¹[D]".** A connected set joining the two
  open side edges inside `Cl D`, off `I₂` and the bottom, should separate `D` (I expect a proof along
  the lines of `hagopian76_K0_crosscut`; not formalized).

So the continuum form should suffice for T15–T17, but I have proved neither form.
`crossing_set_closed` (the hyperspace limit) and the shift `g` with a margin are not attempted.

### 1.D T13 — open (not reached)

It waits on T12 (3): property 2 of `F`, "F separates p from f(p) in π⁻¹[D]", needs `f(p) = q` and the
separation by `R(E)`.

### 1.E T15–T17 and `hagopian76_theorem1` — open (not reached)

On the commission's question "is `yᵢ₋₁` of the form `h(x)` with `h` small?": in T17 (p. 348),
`yᵢ₋₁` is "a point of `K ∩ Cᵢ₋₁`". Here `Cᵢ₋₁` is "the first component of `M ∩ π⁻¹[D]` (whose
closure intersects `π⁻¹[⟨p₁, r⟩]` and `π⁻¹[⟨p₅, s⟩]`) that is met by extending `Cl Cᵢ` away from
`X`". Nothing in the text puts `yᵢ₋₁` in the orbit of `x` under small homeomorphisms.
* Lemma T applies to a component through a point `y` if `y = h(x′)` for some `x′ ∈ E` with `k(x′)`
  in the middle range and some small `h`.
* By `pi_thin_near_layer` and Effros this holds for every `y ∈ M` whose `π`-image lies in the thin
  strip over the middle range at height `< c₁`. Here `c₁` is the `c` of `pi_thin_near_layer` for
  the Effros `δ` of Lemma T. The argument is the one in the proof of `K0_low_point_aux`.
* So T17's "`L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁`" is available by Lemma T if `Cᵢ₋₁` has a point at
  height `< c₁` over the middle range.
* Missing: that `Cᵢ₋₁` has such a point. `Cᵢ₋₁` meets `K₀` because it is crossing
  (`hagopian76_K0_crosscut`), but it may meet it only high up.

## 2. Ledger entries (`LEDGER.md` §6, batch 167)

1. **p. 346, T9, "Note that the chain L − {L₁, L₁₁} follows Cl B".**
   * For the components T12 uses (through `p = h(x)`, `h` small): the substitute of commission
     §1/§2.B is proved (`hagopian76_T12_parts12`): `C ⊇ h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]`, and `C`
     is crossing.
   * For T17: available when `Cᵢ₋₁` has a point low enough over the middle range (§1.E).
   * In general: open.
2. **p. 347, T12.**
   * "To see this let x be a point of k⁻¹(p₃) ∩ Cl K": **true; proved**, with `x` from Lemma T′
     (`K0_dense_low`).
   * The choice of `p`, `q`: **open.**
   * "By Property 1, R(E) intersects an arc in K …": **unargued; open.**
3. **p. 347, Property 3.** Unchanged from batch 166 (three points); open.
4. **p. 347, T13, the existence sentence.** Not reached.
5. **pp. 347–349, T15–T17.** Not reached.
6. **Whether Cl R(E) = M.** Not settled; §1.B says what changes if it is not.

## 3. Axioms

Group *Hagopian 1976 XII (batch 167)* of `Axioms.lean`. The per-theorem output is in
`doc/batches/audits/axioms-batch167.txt`. Each of the 18 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* `crossing_translate`, `K0_dense_low`, `crossing_essential`, `hagopian76_T12_parts12`;
* `exists_mem_closure_component_notMem`, `isPreconnected_interval_set`, `collar_injOn`,
  `openRect_subset_rect`, `isOpen_collar_image`, `collar_uniform`, `pi_near_collar`;
* `dist_prod_lt`, `crossing_translate_aux`;
* `K0_low_point_aux`, `K0_dense_low_aux`, `T12_crossing_aux`;
* `crossing_essential_aux`, `T12_parts12_aux`.

`crossing_translate_aux` is compiled with `maxHeartbeats 1000000`, because the proof is long. This
does not affect the axioms.

## 4. Dependency map of Theorem 1, updated

```
T6/T7 (I₂ at any height c′ ≤ c) ─ hagopian76_D ─ hagopian76_K0 ─ K0_crosscut
                     │                 │
                     │        crossing_translate (Lemma T)  ← no_hair, Effros, collar
                     │                 │
                     │         K0_dense_low (Lemma T′) ← M_meets_above, pi_thin_near_layer
                     │                 │
T8/T9_full, link_control ─ crossing_essential
                     └────────────── hagopian76_T12_parts12   [T12 (1)–(2), proved, shape]
                                               │
                     T12 (3): p, q in distinct composants; R(E) separates   [open]
                                               │
                     T13 (F separates p from f(p))                           [open]
                                               │
   Property 3 (crossing_set_closed; shift g) ──┤                             [open]
                                               │
                     T15–T17 (I finite; Property 4; Bing)                    [open]
                                               │
                     hagopian76_theorem1                                      [open]
```

## 5. Skeleton proposal for what remains

```
-- B (3)
theorem hagopian76_T12 … :
    ∃ p ∈ M ∩ K₀, ∃ h h₁ : M ≃ₜ M, (∀ v, dist (h v) v < ε₃/2) ∧ (∀ v, dist (h₁ v) v < ε₃/2) ∧
      h x = p ∧ (h₁ x : Pt) ∈ K₀ ∧
      Separates (toPt (Rset k)) (p : Pt) (h₁ x : Pt) (π ⁻¹' (F '' D'))
-- first, the planar fact it needs
theorem crossing_pair_separates … (Z₁ Z₂ : disjoint crossing continua in π⁻¹[Cl D] − E − π⁻¹[I₂]) :
    the points of K₀ between them are separated in π⁻¹[D] from those below Z₁ and above Z₂
-- and the input that is missing
theorem crossing_piece_of_R … (x ∈ k⁻¹(t₀)) (ε > 0) :
    ∃ Z ⊆ Rset k, Fold.Q78.IsContinuum Z ∧ Disjoint Z E ∧ Crossing Z ∧ (toPt Z ∩ ball x ε).Nonempty
-- C
theorem crossing_set_closed … : IsClosed {v | ∃ Z ⊆ layer d v, Fold.Q78.IsContinuum Z ∧
    Disjoint Z E ∧ Disjoint (toPt Z) (π ⁻¹' I₂) ∧ Crossing Z}
theorem hagopian76_property3 … : ∀ v Z, Z ⊆ layer d v → Fold.Q78.IsContinuum Z →
    Disjoint Z E → Disjoint (toPt Z) (π ⁻¹' I₂) → ¬ Crossing Z
-- D, E
theorem hagopian76_T13 … ; theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1 : Hagopian76Thm1
```

`crossing_piece_of_R` comes before T12 (3). It would replace the translates of Lemma T with pieces
of `R(E)`.

## 6. Build provenance

Unchanged from batch 166, apart from the first build: the run started from a checkout with no
local build outputs of `HPC`, and the compiled Mathlib files were present. Building the import
closure of the skeleton took about 45 minutes.
