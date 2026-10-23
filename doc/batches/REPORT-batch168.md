Commission read: `doc/batches/COMMISSION-batch168.md` ("Commission: batch 168 — Part E, Hagopian 1976 XIII: Theorem 1 — crossing pieces of `R(E)`; what T13–T17 need of `p`, `q`; Property 3; T12 (3), T13").

# Report, batch 168

## 0. Summary

* **A (what T13–T17 use of `p`, `q`, `h`, `h₁`, `f`, `C`): done** (§1.A). The conditions
  "inaccessible", "distinct composants of `Cl R(E)`" and "`p`, `q ∈ Cl R(E)`" are not used. What is
  used is `p`, `f(p)` off the separating extension `F` and, in T17, `h[R(E)]` and `h₁[R(E)]` disjoint
  from `F ⊆ R(E)`. Hagopian gets both from `p`, `q ∉ R(E)`, plus a dichotomy that he leaves implicit
  ("`g[R(E)]` meets `R(E)` only if `g[R(E)] = R(E)`"). The weakest usable T12 is stated in §1.A.
* **B (Lemma R; crossing continua cut `D`): proved.**
  * `crossing_piece_of_R`: every step of commission §1 goes through. Two changes: `y` is taken in
    `R(X, E) − E` directly, and the crossing is proved by running Lemma T relative to any ambient set
    containing the translate. One addition: the crossing continuum lies in **one** extension `H` of
    `E` away from `X` and misses `E`.
  * `crossing_separates` (single continuum) and `crossing_pair_separates` (two continua, three parts
    along `K₀`): by the Jordan curve theorem in collar coordinates, as commissioned.
* **C (T12 (3)): proved in the commission's candidate shape, with a weaker separating set**
  (`hagopian76_T12`). `p = h₀(x)` and `q = h₁(x)` lie on `K₀`, with `h₀`, `h₁` `ε`-small. A crossing
  continuum `Cl B ⊆ H − E` of `R(X, E)` lies between them and separates `p` from `q` in `π⁻¹[D]`.
  Not shown: `p`, `q ∉ R(E)` (or `∉ H`). So `H` itself is not shown to separate (§1.C).
* **D (Property 3): open, not attempted** (§1.D).
* **E (T13, T15–T17, Theorem 1): open** (§1.E). T13 needs `p`, `q ∉ H`. The rest waits on Property 3
  and on the dichotomy of §1.A.
* **F (`Cl R(E) = M`?): no argument either way** (§1.F).
* **Nothing is refuted.** No defective proof is added; the count stays at fourteen.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76M` at the end of `HPC.lean`. All 14
new theorems use only `propext`, `Classical.choice` and `Quot.sound`. The regenerated `axioms.txt`
has 1736 lines (1722 + 14), and `sorryAx` appears in none of them. No declaration uses `sorry`; the
word occurs only in the comment block at the end of `Hagopian76M.lean` that holds the open shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76M.lean`: the skeleton, with the delivered statements (`crossing_piece_of_R`,
  `crossing_separates`, `crossing_pair_separates`, `hagopian76_T12`) and the open items commented out.
* `H76TranslateIn.lean`: Lemma T relative to an ambient set `A ⊇ Q` (`crossing_translate_in_aux`).
* `H76RPiece.lean`: `mem_closure_extUnion_diff`, Lemma R (`crossing_piece_of_R_aux`).
* `H76PairSep.lean`: the planar part: `rect_domain_crosscut_arc`, `seg_subset_rect_domain`,
  `mem_vsegment`, `rect_domain_crossing_separates`.
* `H76CrossSep.lean`: `injOn_pi_preimage`, `crossing_separates_aux`.
* `H76T12.lean`: `T12_part3_aux`.

## 1. The items

STATUS lines, in order: `STATUS: A done`; `STATUS: B proved`; `STATUS: C proved (shape; separating
set weaker than Hagopian's)`; `STATUS: D open (not attempted)`; `STATUS: E open`; `STATUS: F open`.

### 1.A What T13–T17 use of `p`, `q`, `h`, `h₁`, `f`, `C`

Read pp. 347–349 sentence by sentence. Here `F` is T13's continuum and `d` its decomposition.

1. **T13**, conditions 1–2 ("`F` is an extension of `E` in `M` away from `k⁻¹(0)`"; "`F` separates
   `p` from `f(p)` in `π⁻¹[D]`").
   * Uses `f(p) = q`, and `p`, `f(p) ∈ π⁻¹[D] − F`; the second is implicit in "separates".
   * **Existence** ("follows from Property 1 and the fact that `Cl R(E) = Cl R(k⁻¹(0), E)`") needs
     some extension away from `X = k⁻¹(0)` that separates `p` from `q`. T12 (3) as printed says
     `R(E)` separates. `R(E)` is not such an extension, and it contains `R(k⁻¹(1), E)`. The
     reference to `Cl R(E) = Cl R(X, E)` suggests a crossing piece of `R(X, E)` near `x`; this is
     what Lemma R now gives (§1.B). For such a piece in an extension `H` to make `H` separate, one
     needs `p`, `q ∉ H`. Hagopian has this from `p`, `q ∉ R(E)`.
   * **Irreducibility** (not argued by Hagopian). Extensions away from `X` form a chain (Lemma 4).
     The separating ones are closed upward among those missing `p` and `q`. The intersection of a
     decreasing chain of separating compact sets still separates: an arc from `p` to `q` in
     `π⁻¹[D]` missing the intersection misses one member, by compactness. That the intersection is
     again an extension is not argued; it is plausible from the chain structure of Lemma 4. It is
     not `E`, because `E` misses `π⁻¹[D]` and `π⁻¹[D]` is connected.
   * **So T13 uses:** `p`, `q ∉ F` (hence `∉` the separating extension) and the separation.
     **`p ∉ R(E)` is used here**, through `p`, `q ∉ F ⊆ R(E)`.
2. **`d`, Property 3, "I is finite", `J`, the `xᵢ`**: no use of `p`, `q`, `h`, `h₁` or `f`.
3. **Property 4 for `[x₂ₙ₋₁, x₂ₙ]`** ("there exists a point `yₙ` of `K` such that (1) the closure of
   the `yₙ`-component `Cₙ` … is essential to `h[R(E)]`, and (2) `d⁻¹[[x₂ₙ₋₁, x₂ₙ]]` separates `yₙ`
   from `f(yₙ)`").
   * The base case takes `yₙ = p`. It uses T12 (2) with **Hagopian's `h`** (`h(x) = p`), T13 (2),
     and, implicitly, that only the last block `d⁻¹[[x₂ₙ₋₁, x₂ₙ]]` is needed to separate (by
     irreducibility of `F`; unargued).
   * `h` is the fixed `ε₃/2`-homeomorphism. Property 2 is applied to `h[R(E)]`.
4. **"`[x₁, x₂]` does not have Property 4"**: `d⁻¹[[0, e]] = E` misses `π⁻¹[D]` (it lies over the
   bottom edge), and `π⁻¹[D] ≅ D` is connected, so `E` separates nothing in `π⁻¹[D]`. Nothing of
   `p`, `q` is used.
5. **The induction step (Cases 1 and 2).** Uses:
   * (a) `h` is an `ε₃`-homeomorphism, so Property 2 holds for `h[R(E)]`, and every `Cl Cᵢ` is
     essential to the **same** `h[R(E)]` ("Note that `Cl Cᵢ₋₁` is essential to `h[R(E)]`");
   * (b) `f = h₁h⁻¹` is an `ε₃`-homeomorphism: "`ρ(yᵢ₋₁, f(yᵢ₋₁)) < ε₃`", "`f(yᵢ₋₁)` belongs to
     `L₆ ∩ π⁻¹[D]`";
   * (c) "**Since no point of `N` is within `ε₂` of `Q`, the continuum `f[N]` does not intersect
     `P`**". Here `P = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q`. Disjointness from `Q` follows from (b), since
     `ε₃ < ε₂`. Disjointness from `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ⊆ F ⊆ R(E)` is not argued. It follows from
     `f[N] ⊆ f[h[R(E)]] = h₁[R(E)]` once **`h₁[R(E)] ∩ R(E) = ∅`**;
   * (d) the separations "`d⁻¹[J]` separates `yᵢ` from `f(yᵢ)`" need `yᵢ`, `f(yᵢ) ∉ F`. Here
     `yᵢ ∈ Cᵢ ⊆ h[R(E)]` and `f(yᵢ) ∈ h₁[R(E)]`, so it suffices that **`h[R(E)] ∩ R(E) = ∅`** and
     `h₁[R(E)] ∩ R(E) = ∅`.
6. **The answers to the commission's questions.**
   * **Is `p ∉ R(E)` used? Yes:** in T13 (`p`, `f(p) ∉ F`), and through (c)–(d) in T17, where it is
     needed as `h[R(E)] ∩ R(E) = ∅` and `h₁[R(E)] ∩ R(E) = ∅`. The step from `p = h(x) ∉ R(E)` to
     `h[R(E)] ∩ R(E) = ∅` needs the **dichotomy**: if `g[R(E)] ∩ R(E) ≠ ∅` then `g[R(E)] = R(E)`.
     Hagopian uses it tacitly. It is not proved here.
   * **Is "distinct composants of `Cl R(E)`" used beyond making `C` and the `q`-component different
     and `h[R(E)] ≠ h₁[R(E)]`? No.** No sentence of pp. 347–349 uses `h[R(E)] ≠ h₁[R(E)]` or any
     composant of `Cl R(E)` other than `R(E)`. What is used is that both `h[R(E)]` and `h₁[R(E)]`
     miss `R(E)`.
   * **Is `p`, `q ∈ Cl R(E)` used? No.**
   * **"Inaccessible": not used** (as found in batch 166).
   * **The separation statements used:**
     * T12 (3) is used only to produce T13's `F`. What is needed is an extension of `E` away from
       `k⁻¹(0)` that separates `p` from `f(p)` in `π⁻¹[D]`;
     * T13 (2), "`F` separates `p` from `f(p)`", is used only for the base case of Property 4;
     * Property 4 (2), "`d⁻¹[[x₂ₙ₋₁, x₂ₙ]]` separates `yₙ` from `f(yₙ)`", is used in T17 through
       the planar fact that a continuum crossing between two such separators lies between them
       ("`f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`"). This is the three-part cut of
       `crossing_pair_separates`, applied to `d⁻¹[I]` and `d⁻¹[J]`.
   * **T12 (2) with Hagopian's `h`.** The batch-167 shape gives T9's `h′` (an `ε₁`-homeomorphism),
     with `Cl C ⊆ h′[E]`. By the same dichotomy, `h′[R(E)]` and `h[R(E)]` share `p`, so they are
     equal, and then `Cl C` is essential to `h[R(E)]`.

**The weakest T12 that T13–T17 can use** (the shape proposed for the next batch). There are `p ∈ K₀`
and `ε₃/2`-homeomorphisms `h`, `h₁` with `h(x) = p` and `f = h₁h⁻¹`, such that
1. `Cl C_p` is essential to `h[R(E)]`;
2. some extension `F₀` of `E` away from `k⁻¹(0)` separates `p` from `f(p)` in `π⁻¹[D]` (in
   particular `p`, `f(p) ∉ F₀`);
3. `h[R(E)] ∩ R(E) = ∅` and `h₁[R(E)] ∩ R(E) = ∅`.

Condition 3 implies `p`, `q ∉ R(E)`. Conversely, `p`, `q ∉ R(E)` and the dichotomy give 3, and with
`hagopian76_T12_parts12` also 1. No condition on composants of `Cl R(E)` is needed; so the choice of
`p`, `q` needs no counting of composants on `K₀`. What remains is to find `p = h(x)` and `q = h₁(x)`
low on `K₀`, on the two sides of a crossing piece of `R(X, E)`, and **off `R(E)`** (§1.C).

### 1.B Lemma R and the separation — proved

**`crossing_piece_of_R`.** Set-up of `hagopian76_D` over `[a, b]`, with `hbelow` (no point of `π[M]`
just below the axis) and `0 < a′ < a`, `b < b′ < 1`. There is a height `c₀ > 0` with the following
property, for every `ζ > 0`, every `x ∈ E` with `k(x) ∈ [a + ζ, b − ζ]` and every `ε > 0`. Some
`ε`-homeomorphism `h` satisfies:
1. `h(x) ∈ R(X, E) − E`;
2. `Q = h[k⁻¹[[a′, b′]]] ⊆ R(X, E)` and `Q ∩ E = ∅`;
3. layer by layer, `π(h(y)) = F(z)` with `z ∈ (0, 1) × (0, c₀)` and `|z − (k(y), 0)| < ε`;
4. for every `A ⊇ Q`, the component of `A ∩ π⁻¹[D]` through `h(x)` contains
   `h[k⁻¹[[a + ζ/2, b − ζ/2]]]`, and its closure meets `π⁻¹F[{a} × (0, r₂)]` and
   `π⁻¹F[{b} × (0, s₂)]`. With `A = R(E)` this is the component of `R(E) ∩ π⁻¹[D]` of the commission;
   with `A = Q` its closure is a continuum inside `Q`;
5. the closure of the component of `Q ∩ π⁻¹[D]` through `h(x)` lies in `H − E` for **one**
   extension `H` of `E` away from `X`.

Step-by-step check of commission §1:
1. **Points of `R(E) − E` near `x`: as in the commission, with `R(X, E)`.**
   * `mem_closure_extUnion_diff`: every point of `E` is a limit of points of `R(X, E) − E`.
   * Proof: `Cl R(X, E)` is indecomposable (`hagopian76_lemma6_X`), and `E ≠ Cl R(X, E)` (Lemma 4:
     `E` has a proper extension). So `E` has empty interior in `Cl R(X, E)`
     (`HPC.T13.false_of_interior`).
   * Working with `R(X, E)` from the start removes the case "`y` in an extension away from
     `k⁻¹(1)`" and the passage through `σ ∘ k`.
2. **`π(y)` above the axis: as in the commission.**
   * For `y` near `x`, `π(y) = F(z)` with `z` in a small open box around `(k(x), 0)`.
   * `z₂ = 0` would put `y` in `E` (`mem_layer_of_pi_eq_gamma`).
   * `z₂ < 0` contradicts `hbelow`, the hypothesis of `hagopian76_D` that comes from
     `no_M_below`/T6.
3. **A small translate through `y`: as in the commission.** Lemma 2 at `x`.
4. **Its middle lies in `R(E)`: as in the commission, by a shorter route.** `Q ∩ E = ∅` comes from
   Lemma T (no hair), so `Q` misses `k⁻¹(0)` without the estimate "`h` small and `a′ > 0`". Then
   `Q ⊆ R(X, E)` by absorption.
5. **It crosses: as in the commission.** "The argument is the same as Lemma T step 4, run inside
   `G ⊆ R(E)`": `crossing_translate_in_aux` is Lemma T with the ambient set `M` of the component
   replaced by any `A ⊇ Q`. Steps 3–4 of Lemma T only use that `Q ⊆ A`.

**Added (item 5): one extension.**
* `absorb_point` gives extensions `H₀ ∋ g₀ ∈ h[k⁻¹(a′)]` and `H₁ ∋ g₁ ∈ h[k⁻¹(b′)]`. They are
  nested (Lemma 4); call the larger `H`.
* `H ∩ Q` is a continuum (hereditary unicoherence) through `g₀` and `g₁`. Its preimage under `h` is
  a subcontinuum of `E` meeting `k⁻¹(a′)` and `k⁻¹(b′)`, so it contains `k⁻¹((a′, b′))`
  (`layerSet_Ioo_subset`).
* The part of `Q` over `D` lies in `h[k⁻¹((a′, b′))]`: the end layers have abscissa within `η` of
  `a′ < a` or `b′ > b`. So it lies in `H`.

**`crossing_separates`.** For `D = F[D′]` and `K₀` up to the lowest point `F(t₀, w₂)` of `I₂`
(`hagopian76_K0`), let `B ⊆ π⁻¹[D]` be connected with compact closure. Assume:
* `Cl B` misses `π⁻¹[I₂]` and the points over the axis;
* `Cl B` meets both open side edges;
* `Cl B` misses the points of `K₀` at heights in `(0, u₁]` and in `[u₂, w₂)`.

Then no connected subset of `π⁻¹[D] − Cl B` contains a point over `F(t₀, u₁)` and a point over
`F(t₀, u₂)`. The hypothesis that `π` is injective on `π⁻¹[D]` is supplied by `injOn_pi_preimage`.

Proof, in collar coordinates (`rect_domain_crossing_separates`):
* A connected `S ⊆ D′ − Cl B′` through `(t₀, u₁)` and `(t₀, u₂)` gives a polygonal path in the
  component of the open set `D′ − Cl B′` (`exists_vpath_of_isConnected`).
* Together with the two vertical segments `[(t₀, 0), (t₀, u₁)]` and `[(t₀, u₂), (t₀, w₂)]`, loop
  erasure (`exists_sarc_of_vpath`) gives an arc `T` from `(t₀, 0)` to `(t₀, w₂) ∈ I` that misses
  `Cl B′`, with `T − {ends} ⊆ D′`. The low vertical segment lies in `D′` by
  `seg_subset_rect_domain`.
* `rect_domain_crosscut_arc` is `rect_domain_crosscut` (batch 166) with the segment replaced by any
  such arc. Same Jordan curve `I_L ∪ {a} × [0, r₂] ∪ [a, t₀] × {0} ∪ T`, same ray and half-disc
  argument. So `B′` cannot have closure meeting both open side edges, a contradiction.
* The transfer to `π⁻¹[D]` follows `K0_crosscut_aux`. The new point is that
  `Cl(π[B]) ⊆ π[Cl B]` (`Cl B` is compact), and that `π` is injective over `D`. Together they give
  `S′ ∩ Cl B′ = ∅`.

**`crossing_pair_separates`.** Two crossing sets `B₁` (between heights `u₁` and `u₂` on `K₀`) and
`B₂` (between `u₂` and `u₃`) cut `π⁻¹[D]` along `K₀` into three parts. No connected subset of
`π⁻¹[D] − (Cl B₁ ∪ Cl B₂)` contains two of the three points. Proof: three applications of
`crossing_separates`. Disjointness of `B₁` and `B₂` is not needed.

### 1.C T12 (3) — proved in the commission's candidate shape, with a weaker separating set

**`hagopian76_T12`.** Set-up of `hagopian76_D`/`hagopian76_K0` over `[a, b]`, `t₀ ∈ (a, b)`, `K₀` up
to `F(t₀, w₂)`. There is `x ∈ k⁻¹(t₀)` (Lemma T′) such that for every `ε > 0` there are:
* `ε`-homeomorphisms `h₀`, `h₁`, with `p = h₀(x)` and `q = h₁(x)` on `K₀` at heights
  `0 < u₁ < u₂ < w₂`;
* an extension `H` of `E` away from `X`, and a connected `B ⊆ π⁻¹[D]` with `Cl B` compact, contained
  in `H − E` and meeting both open side edges;
* such that `Cl B` separates `p` from `q` in `π⁻¹[D]`.

Then `f = h₁h₀⁻¹` is a `2ε`-homeomorphism with `f(p) = q`.

Construction (`T12_part3_aux`):
1. `q` from Lemma T′ inside the Lemma-2 neighbourhood `W` of `x`.
2. Lemma R at `x` with band height `< u₂`, so the crossing continuum lies below `q`.
3. `F(t₀, 0) ∉ π[Cl B]`, since every point of `Cl B` is strictly above the axis. Continuity of `F`
   gives a height `δ` below which the vertical misses `π[Cl B]`.
4. `p` from Lemma T′ inside `W` at height `< δ`.
5. `crossing_separates`. Its hypotheses on `Cl B` come from the band: `Cl B` misses the axis and
   `I₂`, because the low strip lies in `D′` and the ends of `I₂` lie above `c₀`.

**Against §1.A.**
* Provided: `p = h₀(x)` and `q = h₁(x)` in `K₀ ∩ W`, and a crossing continuum of `R(X, E)` between
  them that separates them. This answers commission §2.C's candidate, with `R(X, E)` in place of
  `R(E)` and one extension `H` holding the piece.
* **Not provided:**
  * `p`, `q ∉ H` (so that `H`, an extension away from `X`, separates them, as T13 needs), or
    `p`, `q ∉ R(E)`;
  * condition 3 of §1.A;
  * T12 (2) for `h₀`.
* **The commission's absorption check** ("a component of `M ∩ π⁻¹[D]` meeting `Z ⊆ R(E)` lies in
  `R(E)`"): **true**. The closure of such a component lies in `π⁻¹[Cl D]`. It misses `k⁻¹(0)`,
  because `π[k⁻¹(0)] = F(0, 0)` and `Cl D ⊆ F[[a, b] × [0, c]]` with `a > 0`. If it meets `Z ⊆ H`,
  it lies in `R(X, E)` by `subset_extUnion_of_meets`. Not formalized separately; it is that lemma.
* **Points off `R(E)`.**
  * The meagreness route does not work, as the commission suspected. `M ∩ K₀ ∩ W` lies over a
    vertical segment and can be a meagre subset of `M`, so it can lie inside the meagre composant
    `R(E)`.
  * The Effros route (`x′` off the countably many `Fₙ ∩ K₀`) needs each `Fₙ ∩ K₀` to be nowhere dense
    in `M ∩ K₀` near `x`. This does not follow from `Fₙ` being nowhere dense in `M`.
  * Needed, in one sentence: some point `h(x)` low on `K₀` near `x` with `h[R(E)] ≠ R(E)`.

### 1.D Property 3 — open (not attempted)

Unchanged from batch 167 (§1.C there). Still needed:
* the hyperspace limit of crossing continua in the layers `d⁻¹(vₙ)`, with a margin from `r`, `s`
  and `I₂` so that the limit still meets both open side edges;
* the shift `g` of Lemmas 2–3 with a margin.

`crossing_separates` settles the "separation" half of batch 167's remark: a crossing continuum
off `I₂` and the bottom separates `π⁻¹[D]` along `K₀`.

### 1.E T13, T15–T17, Theorem 1 — open

* **T13.** By §1.A, T13 needs an extension `H` away from `X` that separates `p` from `q`. Given
  `p`, `q ∉ H`, `hagopian76_T12` supplies one. The irreducible one needs the intersection lemma of
  §1.A.1.
* **T17's low point of `Cᵢ₋₁`** (report 167 §1.E): **Lemma R and Property 3 do not give it.**
  * Lemma R gives crossing pieces of `R(X, E)` through points near a given point of `E`.
  * Property 3 is about layers of `F`.
  * Neither says anything about the first crossing component `Cᵢ₋₁` met when extending `Cl Cᵢ`.
  * **Missing statement:** every crossing component `C` of `M ∩ π⁻¹[D]` whose closure is essential
    to `h[R(E)]` contains `h′[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]` for some small `h′`. Equivalently,
    "the chain follows `Cl C`" for all such `C`, the general T9 remark that has been open since
    batch 166.
* **T15–T17 and `hagopian76_theorem1`**: wait on Property 3, T13, the dichotomy, and the missing
  statement above.

### 1.F `Cl R(E) = M`?

No argument either way. Nothing proved in this batch depends on it. §1.A shows that `p`,
`q ∈ Cl R(E)` is not used, so the question no longer bears on T12–T17.

## 2. Ledger entries (`LEDGER.md` §6, batch 168)

1. **p. 347, T12.**
   * "Let `p` and `q` be points of `K ∩ (W − R(E))` that belong to distinct inaccessible composants
     of … `Cl R(E)`": of these conditions, **only `p`, `q ∉ R(E)` is used** (T13, T17), and only
     through `h[R(E)] ∩ R(E) = ∅ = h₁[R(E)] ∩ R(E)`, which needs an unstated dichotomy. The other
     conditions are not used.
   * "By Property 1, `R(E)` intersects an arc in `K` …": **true in the form of Lemma R** (crossing
     pieces of `R(X, E)` near `x`, low on `K₀`). The separation of the `p`- and `q`-components by
     such a piece is **proved** (`crossing_separates`, `hagopian76_T12`).
2. **p. 347, Property 3:** unchanged; open.
3. **p. 347, T13, the existence sentence:** **gap.** It needs `p`, `f(p) ∉` the separating
   extension, and an argument that the irreducible element exists; neither is given. Open.
4. **pp. 347–349, T15–T17.**
   * "It follows from Property 3 that `I` is finite": not reached.
   * Property 4 base case: needs that only the last block separates; unargued.
   * "Since no point of `N` is within `ε₂` of `Q`, the continuum `f[N]` does not intersect `P`":
     **gap.** Also needs `f[N] ∩ F = ∅`, i.e. `h₁[R(E)] ∩ R(E) = ∅`.
   * "Following Bing [2, p. 225]": the three-part cut by two crossing continua is proved
     (`crossing_pair_separates`).

## 3. Axioms

Group *Hagopian 1976 XIII (batch 168)* of `Axioms.lean`; the per-theorem output is in
`doc/batches/audits/axioms-batch168.txt`. Each of the 14 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* `crossing_piece_of_R`, `crossing_separates`, `crossing_pair_separates`, `hagopian76_T12`;
* `crossing_translate_in_aux`;
* `mem_closure_extUnion_diff`, `crossing_piece_of_R_aux`;
* `rect_domain_crosscut_arc`, `seg_subset_rect_domain`, `mem_vsegment`,
  `rect_domain_crossing_separates`;
* `injOn_pi_preimage`, `crossing_separates_aux`;
* `T12_part3_aux`.

`crossing_translate_in_aux` and `T12_part3_aux` are compiled with `maxHeartbeats 1000000`, and
`crossing_piece_of_R_aux` with `800000`; this does not affect the axioms.

## 4. Dependency map of Theorem 1, updated

```
T6/T7 ─ hagopian76_D ─ hagopian76_K0 ─ K0_crosscut
            │               │
            │      crossing_translate (Lemma T) ── crossing_translate_in_aux (relative form)
            │               │                                │
            │      K0_dense_low (Lemma T′)       crossing_piece_of_R (Lemma R)  ← Lemmas 2, 4, 6, absorption
            │               │                                │
            │               │        rect_domain_crosscut_arc ─ crossing_separates ─ crossing_pair_separates
            │               │                                │
T8/T9_full ─ crossing_essential ─ T12_parts12     hagopian76_T12 [(3), shape: Cl B ⊆ H separates p, q]
                                                             │
          R-dichotomy; p, q ∉ R(E) (or ∉ H)                  │                      [open]
                                                             │
                      T13 (irreducible separating extension) │                      [open]
                                                             │
   Property 3 (crossing_set_closed; shift g) ────────────────┤                      [open]
                                                             │
     T15–T17 (I finite; Property 4; Bing; "follows Cl Cᵢ₋₁")  │                      [open]
                                                             │
                                  hagopian76_theorem1                                [open]
```

## 5. Skeleton proposal for what remains

```
-- the dichotomy Hagopian uses tacitly (§1.A)
theorem Rset_homeo_dichotomy … (g : M ≃ₜ M) :
    (g '' Rset k ∩ Rset k).Nonempty → g '' Rset k = Rset k
-- points off R(E) (§1.C)
theorem exists_low_off_R … : ∀ ε > 0, ∃ h : M ≃ₜ M, (ε-small) ∧ (h x on K₀ below height ε) ∧
    h (x : M) ∉ Rset k
-- T12 in the weakest form of §1.A
theorem hagopian76_T12' … : ∃ p h h₁, (ε₃/2-small) ∧ h x = p ∧ IsEssential … (Cl C_p) ∧
    (∃ F₀, IsExtensionAway E (layer k 0) F₀ ∧ Separates F₀ p (h₁ x) (π⁻¹ D)) ∧
    Disjoint (h '' Rset k) (Rset k) ∧ Disjoint (h₁ '' Rset k) (Rset k)
-- T13: the irreducible element
theorem iInter_chain_extension … : (chain of extensions away from X, each separating p, q) →
    ⋂ is an extension away from X separating p, q
-- Property 3, as in report 167 §5 (continuum form, missing π⁻¹[I₂])
theorem crossing_set_closed …; theorem hagopian76_property3 …
-- T17's missing statement (§1.E)
theorem follows_essential_crossing … (C crossing component, Cl C essential to h[R(E)]) :
    ∃ h′ small, h′[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]] ⊆ C
theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1 : Hagopian76Thm1
```

## 6. Build provenance

The run started from a checkout with no local build outputs of `HPC`; the compiled Mathlib files were
present. Building the import closure of `HPC` took about 75 minutes. After that, each new file was
checked with `lake env lean` and the whole library with `lake build HPC`.
