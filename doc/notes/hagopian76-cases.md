# Hagopian 1976, pp. 348–349, Cases 1–2: a reconstruction in strand language

Batch 178 (commission 178 §8); E2.5 and E2.6 rewritten in batch 181 (commission 181 §3–§4). Status markers: **[proved]** means a Lean theorem without `sorry`
exists (named); **[Prop]** means the step is stated as a named `Prop` or a commented-out open shape
in `HPC/Hagopian/Hagopian76W.lean`; **[open]** means it is only described here.

## 0. Set-up and vocabulary

* `O = π⁻¹[D]`, `D = F[D′]`; `Y = π⁻¹[Fr D]` (compact, connected, misses `O`, contains `Fr O`:
  `pi_preimage_frontier_D`) **[proved]**.
* The low vertical `σ` over an abscissa `t₀` of the inner middle; the frame `lowFrame`
  **[proved]** (`lowFrame_hyps` gives its connectedness hypotheses when `O ∩ E = ∅`).
* A **crossing piece**: connected, in `O`, closed in `O`, compact closure missing `π⁻¹` of the
  bottom edge and of `I₂`, closure meeting both open side segments (`IsCrossingPiece`). Crossing
  pieces are pieces of `lowFrame` (`isPiece_of_isCrossingPiece`) **[proved]**.
* For pieces, `A(X)` (below) and `B(X)` (above); `X′ ≺ X` iff `X′ ⊆ A(X)`. Totality, antisymmetry,
  transitivity, no pockets (S4a–S4e) **[proved]**.
* A **strand** is the component of `M ∩ O` through a point over the inner middle (`strand_lemma`);
  its closure is a proper subcontinuum of `M` **[proved]**.
* "`W` lies between `X` and `Y`" means `Y ≺ W ≺ X` (or the symmetric order).
* Hagopian's notation: `I = [x₂ᵢ₋₁, x₂ᵢ]` has Property 4 with `yᵢ ∈ K`, `Cᵢ` the `yᵢ`-component;
  `J = [x₂ᵢ₋₃, x₂ᵢ₋₂]`; the gap continuum `Γ = d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]`.

## 1. E0: Property 4 (2) in strand terms

*Claim.* Let `y` be over the inner middle with the strands `S_y`, `S_{f(y)}` missing `F`. Then
`d⁻¹[B]` separates `y` from `f(y)` in `O` iff some crossing component of `d⁻¹[B] ∩ O` lies between
`S_y` and `S_{f(y)}`.

* (⇐) is the converse of SSL (`strand_separation_converse`) **[proved]**, once the component is a
  crossing piece and `S_y`, `S_{f(y)}` are crossing pieces.
* (⇒) is SSL with its corollary (`sepByCrossing_of_inner_crossing`) **[proved]**, given that every
  component of `d⁻¹[B] ∩ O` through a point of `σ` is a crossing piece. That hypothesis is 3c
  (`block_components_cross`) **[Prop]**, which rests on 3b (`InnerComponentsCross`) **[Prop]**.
* The strands of `yᵢ`, `f(yᵢ)` miss `F` when `yᵢ ∈ h[R(E)]`: `strand_misses_F_of_composant`
  **[proved]**. That they are crossing pieces is 4.B **[open]** (report §4.B).

## 2. E1: the case printed as "unless"

> Then `d⁻¹[J]` separates `yᵢ` from `f(yᵢ)` and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`.

*Reading.* If some `J`-strand (crossing component of `d⁻¹[J] ∩ O`) lies between `Cᵢ` and
`S_{f(yᵢ)}`, then by E0 (⇐) `d⁻¹[J]` separates `yᵢ` from `f(yᵢ)`; clause (1) of Property 4 for `J`
with `yᵢ₋₁ := yᵢ` is clause (1) for `I`. So `J` has Property 4.

*Status.* The implication is the converse of SSL plus bookkeeping; it is **[Prop]**
(`property4_step_unless`) only because the hypotheses "the `J`-strand is a crossing piece" and
"`Cᵢ`, `S_{f(yᵢ)}` are crossing pieces" are 3c and 4.B.

## 3. E2: the remaining case

No `J`-strand lies between `Cᵢ` and `S_{f(yᵢ)}`, while some `I`-strand `W` does (E0, ⇒, since
`d⁻¹[I]` separates). By S4b–S4d the `J`-strands lie all below both `Cᵢ` and `S_{f(yᵢ)}`, or all
above both (no `J`-strand is between, and the order is total on disjoint pieces).
Hagopian's "`yᵢ` is above `d⁻¹[J]`" is the first alternative read with `Cᵢ` on the far side; the
second alternative is symmetric under exchanging "above" and "below" (and is not treated in the
text).

### E2.1 The first strand **[open]**

* `L`: the shortest extension of `Cl Cᵢ` away from `X` in `h[R(E)]` containing a strand other
  than `Cᵢ`; `Cᵢ₋₁` is that strand. Existence of a shortest one needs a compactness argument over
  the extensions in `h[R(E)]` (the chain `ExtChainInter` of batch 170 gives intersections of chains
  of extensions) **[open]**.
* `L` misses `F`: `L ⊆ h[R(E)]` and `strand_misses_F_of_composant` **[proved]** (every proper
  subcontinuum through a point of `h[R(E)]` misses `F`).
* `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁` with `Cl Cᵢ₋₁` essential to `h[R(E)]`: `strand_essential` (batch 177) for the
  closure of a strand **[proved]**; the choice of `yᵢ₋₁ ∈ K` uses that `K` meets every strand of
  `h[R(E)]` over the inner middle, which is the T12 construction of `K` **[open]**.

### E2.2 `N` **[open]**

`N` is the subcontinuum of `L` essential to `h[R(E)]` with `yᵢ`, `yᵢ₋₁` in its end sets. In
Case 1, `N ∩ O` lies in the left parts of `Cᵢ`, `Cᵢ₋₁` and in stubs within `3/n` of the left side
(S6, `strand_fine_positions` **[proved]**), so `N` stays `ε₂` away from the low vertical `V` over
`15/22` provided `3/n + 2/n < 15/22 − 3/22 − ε₂`. Which end of `Cᵢ₋₁` `L` enters by is decided by
the order (S4) and is the definition of "Case 1" in strand terms: `L` reaches `Cᵢ₋₁` through the
left side segment.

### E2.3 The cap (Case 1)

`P := d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q`. Claim: `P` separates `yᵢ` from `f(yᵢ)` in the plane.

* **Tool [proved].** Two continua with disconnected intersection separate the plane
  (`separatesPlane_union_of_inter_disconnected`); separation in `O` is separation in the plane with
  `Y` adjoined (`sepIn_iff_separatesPts_union`).
* **(α), `Q`.** One segment of the vertical over `15/22` between consecutive points of
  `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` does not close the band when the band crosses that vertical several times:
  the band between the lowest `J`-strand and the highest `I`-strand above it is a union of strips,
  one for each pair of consecutive crossings of the vertical by `d⁻¹[J] ∪ Γ ∪ d⁻¹[I]`. The segment
  must be the one met first by `Cᵢ` coming from the left: it is the only segment on the boundary of
  the component of `O − (d⁻¹[J] ∪ Γ ∪ d⁻¹[I])` that contains the left part of `Cᵢ`. Replacing `Q` by
  the whole low vertical `V` changes the cap into a set whose complement may have more than two
  components, and step E2.5 (Janiszewski with `A ∪ B ⊇ P`) then needs `V ⊆ A ∩ B`, which is what the
  route of commission 178 §8 E2.5.1 uses. **Decision:** take `Q` the first segment met by `Cᵢ` from
  the left for the separation claim, and `V` for the local-to-global step. **[open]**
* **(β), "between `d⁻¹[I]` and `d⁻¹[J]`".** `I`-strands and `J`-strands can interleave in the order of
  S4. "Between" must mean: between the `J`-strand `S_J` and the `I`-strand `S_I` that bound the
  component of `O − (d⁻¹[J] ∪ d⁻¹[I])` containing the point, i.e. `S_J ≺ point-strand ≺ S_I` with no
  strand of `d⁻¹[J] ∪ d⁻¹[I]` strictly between. With the order of S4 this is well defined
  (S4b–S4d **[proved]**); the claim that `yᵢ₋₁` lies in such a component is **[open]**.
* **(γ), the bounded side.** The cap `P` is `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q`; the intersection of
  `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` with `Q` is two points (the ends of `Q`). With `A := ` the arc of the band from
  one end of `Q` to the other through the left side, and `B := Q`, unicoherence gives that `A ∪ B`
  separates the plane, and the bounded complementary domain is the one not containing `Y − Cl D`
  (`Y` is connected and unbounded parts of it are joined outside). Which of `yᵢ`, `f(yᵢ)` lies in the
  bounded domain is decided by the order: the one between `S_J` and `S_I`. **[open]** (the two-point
  intersection is not formalized).

### E2.4 Property 2 **[open]**

> for otherwise, a subcontinuum of `L` would violate Property 2

`H`: the subcontinuum of `L` from `Cl Cᵢ` to `yᵢ₋₁` (the part of `L` between its end set in `Cl Cᵢ`
and the layer of `L` through `yᵢ₋₁`); its end sets are `X ∩ H` and the layer through `yᵢ₋₁`. If
`ρ(yᵢ₋₁, d⁻¹[I]) < ε₃`, `H` together with the ε₃-close point of `d⁻¹[I]` gives a continuum
`ε₃`-close to `F` at both ends and essential to `h[R(E)]`, against `Property2At ε₂ ε₃`. The statement
`Property2At` is in the project (batch 176); the identification of `H` as an extension of a piece of
`h[E]` is **[open]**.

### E2.5 → §3.6–§3.7 of commission 181 (Case 1, the band and the ending)

Batch 181 replaces the Janiszewski route of E2.5 by a strand-wise ending (the old E2.5.2 bound was
wrong: the distance from `π⁻¹[[3/8, 5/8] × [0, c₁/2]]` to `Y` is `0`).

Printed (pp. 348–349):

> Consider the continuum `P` in `R²` that is the union of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` and an arc segment `Q`
> in `π⁻¹[D ∩ ⟨p₄, q₄⟩] − d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` that has one end point in `d⁻¹[I]` and the other in
> `d⁻¹[J]`. Since no point of `N` is within `ε₂` of `Q`, the continuum `f[N]` does not intersect `P`.
> Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`. It is not above `d⁻¹[I]` because
> `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃` and `ρ(yᵢ₋₁, f(yᵢ₋₁)) < ε₃`. Hence `J` has Property 4.

* **The set-up facts (§3.1) [proved].** `Mid` = the points of `M ∩ π⁻¹[D]` over
  `[1/2 − 2/n, 1/2 + 2/n]` (`midSet`). Two fields of `Thm1Setup`, chosen before `F`:
  `hε₃O` (points of `M − E` within `ε₃` of `Mid` lie in `π⁻¹[D]`; `exists_eps_mid_O`) and `hε₃S`
  (`Mid` is `ε₃`-far from the preimage of the closed side segments; `exists_eps_mid_sides`).
  `K ⊆ Mid` (`Thm1Setup.K_subset_mid`). p. 348 "Note that `f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`" is
  `f_mem_O_of_mem_K` (for `y ∈ K` with `h⁻¹(y) ∈ R(E)`).
* **The cap lemma (§3.2) [proved].** `above_closure_misses_bottom`: the closure of the region above a
  piece with compact closure missing the bottom edge misses `π⁻¹` of the open bottom edge.
  `cross_strand_near`: `a ∈ Mid` below a crossing piece `W`, `b` above it, `ρ(a, b) < ε₃` give
  `ρ(a, Cl W) < ε₃` (the segment `[a, b]` meets `Cl W`: it cannot leave `π⁻¹[D]` through `I₂`
  (`hε₂I`), the sides (`hε₃S`) or the open bottom edge (`above_closure_misses_bottom`)). The mirror
  `cross_strand_near_mirror` needs `a` to be `ε₃`-far from `π⁻¹` of the bottom edge, which is not
  uniform on `Mid`.
* **The band (§3.6) [Prop].** The field `band` of `Case1Witness`: `f(yᵢ₋₁)` above `S_I` or below
  `S_J`. Its parts: `Q` per (α); `P` separates the band (`separatesPlane_union_of_inter_disconnected`
  **[proved]**, not applied); `f[N] ∩ d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] = ∅` (by `hcomp`: `f[N] ⊆ h₁[R(E)]` misses `F`,
  as in `Thm1Setup.h₁_Rset_notMem_G` **[proved]** for points); `f[N] ∩ Q = ∅` **[open]** (the printed
  reason is about `π⁻¹(p₄)`, not `Q`).
* **The ending (§3.7) [proved].** `case1_ending`: a good point `y` between `S_J` and `S_I`, `ε₃`-far
  from `Cl S_I`, with `f(y)` above `S_I` or below `S_J`, gives Property 4 for `J`: above `S_I` is
  excluded by `cross_strand_near`; below `S_J` gives separation by the SSL converse
  (`property4_of_strand_sep`).
* **Case 1 (§3.8) [proved, conditional].** `case1`, from the named `Prop` `Case1Claims` (fields of
  `Case1Witness`: E2.1 `first`, §3.4 `between`, §3.5 `far`, §3.6 `band`).

### E2.6 → §4 of commission 181 (Case 2, sentence by sentence)

Printed (p. 349):

> Case 2. Suppose `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` intersect different elements of
> `{π⁻¹[⟨p₁, r⟩], π⁻¹[⟨p₅, s⟩]}`. We assume without loss of generality that `π⁻¹[⟨p₅, s⟩]` meets `Z`,
> `d⁻¹(x₂ᵢ₋₁)`, and `d⁻¹(x₂ᵢ₋₃)`. Define `Cᵢ₋₁`, `L`, `yᵢ₋₁`, and `N` as in Case 1. If `yᵢ₋₁` is
> above `d⁻¹[J]`, it is between `d⁻¹[I]` and `d⁻¹[J]`, and `f(yᵢ₋₁)` is above `d⁻¹[I]`. Since both
> `yᵢ` and `yᵢ₋₁` are within `ε₃` of `d⁻¹[I]`, it follows as in Case 1 that a subcontinuum of `L`
> violates Property 2. Hence `yᵢ₋₁` is below `d⁻¹[J]` and `f(yᵢ₋₁)` is above. Therefore `J` has
> Property 4.

* (a) "If `yᵢ₋₁` is above `d⁻¹[J]`, it is between": **[Prop]** (`Case2Witness.claim_a`); same
  obstruction as §3.4 (the configuration of report 180 §4.5).
* (b) "… and `f(yᵢ₋₁)` is above `d⁻¹[I]`": the good case (`f(yᵢ₋₁)` below `S_J`) is split off and
  gives Property 4 for `J` at once **[proved]** (`case2_ending`); the rest is **[Prop]**
  (`Case2Witness.claim_b`). The band of Case 1 is not printed for Case 2, where the gap continuum's
  end layers meet different sides; which `Q` closes it is open.
* (c) "both `yᵢ` and `yᵢ₋₁` are within `ε₃` of `d⁻¹[I]`": **[proved]** from (b) by `cross_strand_near`
  (inside `case2_ending`).
* (d) "a subcontinuum of `L` violates Property 2": **[Prop]** (`Case2Witness.claim_d`).
* (e) "Hence `yᵢ₋₁` is below `d⁻¹[J]` and `f(yᵢ₋₁)` is above": the second half is **[Prop]**
  (`Case2Witness.claim_e`); nothing printed excludes `f(yᵢ₋₁)` below `S_J` too (both points below
  every `J`-strand), and then `J` does not separate at `yᵢ₋₁`.
* `x₂ᵢ₋₃` in the hypothesis: reading it as `x₂ᵢ₋₂` would contradict the case hypothesis (both end
  layers would meet `π⁻¹[⟨p₅, s⟩]`), unless a layer meets both sides. As printed it is an extra
  assumption on `d⁻¹(x₂ᵢ₋₃)`; the conditional `case2` does not use it.
* **Case 2 [proved, conditional].** `case2`, from the named `Prop` `Case2Claims`.
* **The step [proved, conditional].** `hagopian76_property4_step_cond` from `BlockLayersMeetSides`,
  `Case1Claims`, `Case2Claims`; Theorem 1 from these and saturation: `hagopian76_theorem1_of_cases`.

### E3 The last step (`i = 2`) (batch 182)

At `i = 2`, `J = [x₁, x₂] = [0, e]` and `d⁻¹[J] = E`, which misses `π⁻¹[D]`: there are no
`J`-strands, and `d⁻¹(x₂) = k⁻¹(1)` lies over `γ(1) = F(1, 0)`, on neither side segment
(`blockLayersMeetSides_false`). Neither printed case applies. The step must show instead that
`I = [x₃, x₄]` does **not** have Property 4 (the printed induction ends with "Note that `[x₁, x₂]`
does not have Property 4 … The resulting contradiction will complete our proof").

Reading of Case 1 with the bottom edge in place of the `J`-strand:
* E0 gives an `I`-strand `S_I` with `y₂` and `f(y₂)` on opposite sides. "Between `d⁻¹[I]` and
  `d⁻¹[J]`" becomes "below `S_I`": nothing of `π⁻¹[D]` is below `E`.
* `C₁`, `L`, `y₁`, `N` as in E2.1–E2.2.
* The band `P = d⁻¹[[x₁, x₄]] ∪ Q`, `Q` the segment of the vertical over `15/22` from the bottom edge
  to the first point of `d⁻¹[I]`. Then `f(y₁)` is above `S_I` or below `E`; the second is impossible
  in `π⁻¹[D]`.
* "Above `S_I`" is excluded by the cap lemma and E2.4 (`ρ(y₁, Cl S_I) ≥ ε₃`).

**Formalized** (`H76Orient.lean`): `LastStepWitness` (good point `y` down from an `I`-strand,
`ρ(y, Cl S_I) ≥ ε₃`, `f(y)` up from `S_I`, in either orientation), `last_step_ending` (a witness gives
`False`), the named `Prop` `LastStepClaims` (a witness exists if `[x₃, x₄]` has Property 4) and
`not_property4_x3x4`. The step is a proof by contradiction, so `LastStepClaims` is equivalent to
`¬ Property4 [x₃, x₄]` by design.

**Where the gap continuum closes the band.** `d⁻¹[[x₂, x₃]]` starts at `k⁻¹(1)`, in the right region
`F[[19/22, 1] × [0, c₁]]` (`Thm1Setup.IsBlocks.layer_x2_meets_right`), to the right of `D`. Its other end
`d⁻¹(x₃)` is not located by anything proved: if it meets the right side segment the band closes on the
right, as in Case 1; if the left, the configuration is that of Case 2; if neither, it is not decided.
*Batch 185:* "neither" is excluded: for tight blocks with `m ≥ 2`, `d⁻¹(x₃)` meets a closed side
segment (`layer_x3_meets_side`, E6); which one is not decided.

### E4 Orientation (batch 182)

Printed: "For convenience we suppose `d⁻¹[J]` is below `d⁻¹[I]` and `f(yᵢ)` is above `d⁻¹[I]`.
(Other cases are handled with similar arguments to that given in this case.)"

`Thm1Setup.up o W`, `Thm1Setup.dn o W` (`H76Orient.lean`) are the two sides of `W`, exchanged by
`o : Bool` (`o = false`: up = above). With the mirror cap without extra hypothesis
(`cross_strand_near_above`, batch 182 §2.1: the segment `[a, b]` meets the frontier of the region
*above* `W`, which misses the open bottom edge), every step that uses the cap is symmetric:
`cross_strand_near_o`, `property4_step_unless_o`, `case1_ending_oriented`, `case2_ending_oriented`.

The `Bool` covers two of the four configurations: `d⁻¹[J]` on the side of `yᵢ` (printed: `J` below,
`f(yᵢ)` above; mirrored: `J` above, `f(yᵢ)` below). In the other two, `d⁻¹[J]` is on the side of
`f(yᵢ)`; then `yᵢ` is on the far side of both strands, and E1 leaves the case "`f(yᵢ)` between
`S_I` and `S_J`", in which the band argument would have to be run for `f(yᵢ)` rather than for a point
of `K`. That case is not treated; `StepFrame` asks for a `J`-strand on the side of `yᵢ`.

### E5 Bing 1960 as the model for pp. 348–349 (batch 183)

Hagopian: "Following Bing [2, p. 225]" (p. 348). Bing 1960, journal pp. 224–228 (PDF pages 16–20 of
`doc/sources/bing1960.pdf`), read from page images at 200 dpi. The commission's transcriptions agree
with the pages. One small inconsistency is Bing's own (p. 227): he supposes
"`ρ(q, x₂ᵢ₋₁x₂ᵢ) ≥ ε₄`" and then writes "It is not above `x₂ᵢ₋₁x₂ᵢ` because
`ρ(q, x₂ᵢ₋₁x₂ᵢ) > ε₄` and `ρ(q, h(q)) < ε₄`"; the weak inequality suffices. Bing's
`M′` is a continuum each of whose proper subcontinua is an arc, and `x₁x₂…x₂ₙ` is an arc in `A`.

**Dictionary** (commission 183 §1, checked against the pages):

| Hagopian 1976 | Bing 1960 |
| --- | --- |
| `K`, the low vertical over `p₃`; `yᵢ ∈ K` | `K`, the disc bounded by `a₁a₅`, `a₁r`, `rs`, `a₅s`; `p ∈ K·(M′ − A)` above `a₃` |
| `d⁻¹[I]`, `d⁻¹[J]`; `I` above `J` | arcs `x₂ᵢ₋₁x₂ᵢ`, `x₂ᵢ₊₁x₂ᵢ₊₂` (Bing's indices increase downward) |
| the gap continuum `d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]` | the gap arc `x₂ᵢx₂ᵢ₊₁` |
| `f = h₁h⁻¹`, an `ε₃`-homeomorphism | `h`, an `ε₄`-homeomorphism |
| Property 2 (`ε₂`, `ε₃`) | Property 18 (`ε₃`, `ε₄`) |
| `Cᵢ`, `Cᵢ₋₁`, `L`, `N` | `tu`, `vw`, the arc `tuvw` |
| `π⁻¹(p₄)` (Case 1) | `a₄` (Case 1); `a₂` in Case 2 |
| `L ∩ F = ∅` (composants) | `tuvw ⊆ M′ − A` (arc components) |
| the band `P = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q` | the simple closed curve `J` |

**Which of Bing's reasons carry over** (details: `LEDGER.md` §6, batch 183; report
`doc/batches/REPORT-batch183.md`):

| Bing's reason | Hagopian's step | Carries over? |
| --- | --- | --- |
| the arc `ab` (`a = p`, `b ∈ vw`; or `b = q`, `a ∈ tu`) | E2.4 | **yes**, steps 1–3: `e24_pair_between`, `e24_pair_below`, `minimalAdmissible_restrict`; steps 4–6 named (`E24Claims`) |
| the subarc of an arc between two points is an arc | `H ⊆ L` between two layers | **yes, with Lemma 5** (lower semicontinuity); in general metric spaces the layer-preserving restriction needs it |
| "It follows from the Jordan curve theorem that `q` lies between …" | "between" (Case 1) | **partly**: the separation of the two sides of the side subsegment `σ` carries over; the strand ends on the side lines (Bing: by construction) do not |
| "As a point moves from `p` to `q`, the image … does not intersect `J`. Hence `h(q)` is …" | Case 2 (b), (e) | **no**: `J` is a simple closed curve, and the side of `h(q)` follows from crossing parity; `P` is a continuum, with no parity argument |
| "no point of the arc `pq` in `M` is within `ε₄` of this vertical part of `J`" | `N` misses `Q` | **unargued in both** |
| `a₂` in Case 2 | `π⁻¹(p₄)` printed in both cases | **Bing's choice adopted** (`r = 7/22` in `FarFrom`) |

**Route of §2 (E2.4 by Bing's arc `ab`).**
1. `Cᵢ₋₁` between `yᵢ` and `S_I` (Bing: "`q` above `tu`"): `a = yᵢ`; `ρ(yᵢ, Cl S_I) < ε₃`
   (`cross_strand_near_o`); the segment to a near point of `S_I` meets `Cl Cᵢ₋₁` within `ε₃` of `yᵢ`
   (`Thm1Setup.near_strand_cross_o`). Result: `e24_pair_between`.
2. `yᵢ₋₁` down from `Cᵢ`, `S_I` up from `Cᵢ`, `ρ(yᵢ₋₁, Cl S_I) < ε₃`: `b = yᵢ₋₁`; the segment meets
   `Cl Cᵢ` within `ε₃` (`e24_pair_below`). Stated for the adjacent strand `S_I`; the printed form with
   all of `d⁻¹[I]` is not reached by this argument for an `I`-strand below `Cᵢ` (not decided).
3. `H = d⁻¹[[s, t]]` with the layers of `L` (`minimalAdmissible_restrict`); end sets `d⁻¹(s) ∋ a`,
   `d⁻¹(t) ∋ b`, so `ρ(T, V) < ε₃`.
4.–6. Far layer, essential, `FarFrom`: the named `Prop` `E24Claims`; with them Property 2 is violated
   (`property2_violation`; the far layer may be measured from either end set).
Assembly: `E24Data`, `E24Data.far` (the field `far` of `Case1WitnessO`; the field `claim_d` of
`Case2WitnessO`), `hagopian76_theorem1_of_cases3`.

**Route of §3 ("between", Case 1).** Let `A = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` and let `σ` be the part of the left
side segment between the points where `Cl S_J` and `Cl S_I` meet it. At the exit point `u ∉ A` of `L`
from `Cl Cᵢ`, the two sides of `σ` lie in different components of the complement of `A ∪ σ`
(unicoherence, `separatesPlane_union_of_inter_disconnected`). `L` misses `F`, so it stays in the outer
component until it meets `π⁻¹[D]` again. **Open:** that the outer component meets `π⁻¹[D]` only
through `σ`. It fails if, near an end of a strand, `F` has no points outside `D` (the strand only touches
the segment there): the outer component then passes around the end, and the batch-180 configuration
("`L` re-enters on the other side of a strand's end") is not excluded. `Γ` closes the region only
where it reaches the side segment between the strands; Bing's arcs end exactly at `x₂ᵢ`, `x₂ᵢ₊₁` on the
side line, where the gap arc begins, and that is what is missing for continua.

**Route of §4 (Case 2).** (a) as §3 at the right side segment, open for the same reason. (b), (e): in
Bing, `J` meets the vertical through `a₃` only in `x₂ᵢ₋₁x₂ᵢ` and in the vertical part, and the side
of `h(q)` follows from the parity of crossings, whatever route the gap arc takes (over the top or
underneath; checked on toy polygons, not formalized). So the `E`-side route (§4.3) is not a gap in
Bing, apart from the gap arc possibly entering `K`, which Bing does not discuss. For the continuum
`P`, no parity argument is available, and the Janiszewski form separates the two sides of `Q`, not
the two sides of `S_I`: open. (d): as §2 with `r = 7/22` (`Case2WitnessE24`).

**Route of §5 (the two other orientations).** The proposal fails as stated: `f(yᵢ)` need not lie in
`Mid` (E1's position clause gives abscissae in `(3/8, 5/8)` only), and the cap from `f(yᵢ)` uses
`hε₃S`, `hε₃O`, stated on `Mid`. A possible repair: choose `ε₃` so that the `ε₃`-neighbours of `Mid`
have abscissae within `4/n` of `1/2`, and state the two `ε₃` fields on that wider set. Also, that the
closure of the component of `f(yᵢ)` is essential to `h₁[R(E)]` does not follow from the essentiality
of `Cl Cᵢ` to `h[R(E)]`. Open.

**§6.3, the split by `Γ`.** Proposed: `Γ` joins the left ends of `S_J` and `S_I` (meets the left
side segment between them), or the right ends, or both. Conjectured exhaustive for `i ≥ 3`: `Γ` misses
the bottom edge (`Γ ∩ E = ∅`) and `I₂`, and it cannot join the strands inside the closed region between
them without cutting `Cᵢ`, a crossing piece missing `F`. Not formalized.

### E6 Saturation, runs and the case split (batch 185)

**Saturation (2e), closed.** Let `y = h(e) ∈ F` lie over `D` with `3/22 + 8/n < k(e) < 19/22 − 8/n`,
`K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]`, `K⁺ = F ∩ h[k⁻¹[[k(e), 1]]]`.
* *Neither half lies over `D`* (`half_in_O_false`). If `K⁻` did, take the tip
  `τ = min {k(e′) ≤ k(e) : h(e′) ∈ F}`; its layer meets `d⁻¹(1)` (`tip_meets_end_layer`). By S0,
  `h[E] ⊄ F` and `F ⊄ h[E]`. Lemma 7 of 1984 (`hagopian84_lemma7`, applied to `h[E]` and `F`) makes
  `h[k⁻¹(τ)]` a layer of `F`, hence `d⁻¹(1)`, which would lie over `D` — against
  `T12Data.end_layer_not_subset`. `K⁺` is the mirror.
* *Then the component of `y` crosses* (`noncrossing_half_in_O_steps45`): each half leaves `D`,
  `half_bump_side` and S0 put the exits over `3/22` and `19/22` respectively, both in the closure of
  the component; the heights are inside as in `side_point_open`.
* The chunk argument of batches 179–183 (the points `zⱼ`, the chunk, the edge case `F ∩ hⱼ[E] ⊆ Tⱼ`,
  `τ₁ = 1`) is not needed. The earlier tip results are kept.

**Runs.** For two type λ continua `(E, k)`, `(G, d)` whose intersection meets two layers of `E`, either
`E` lies in one layer of `G`, or `E ∩ G = k⁻¹[[a, b]] = d⁻¹[[a′, b′]]` with the layers matching
(`layers_agree`). An end of the common segment that is not an end of `E` is an end layer of `G`
(`translate_run`, `translate_run_right`, by atriodicity). What is not proved (§3.3 of the commission)
is that `F` leaves `D` along the translate of the strand through a crossing component `C` of
`F ∩ π⁻¹[D]`: `Cl C ⊆ h[E]` (`strand_lemma`) and `layers_agree` give a common segment, but the
degenerate case (`h[E]` inside one layer of `F`) and an end at `d⁻¹(0)` are not excluded, and no form
usable for "between" was found. So "between" (E2.5, report 183 §3) stays open.

**The case split for `i ≥ 3`, closed** (`blockLayersMeetSides3`; Lemma 7 not used). With tight blocks
and `3 ≤ i ≤ m`, `x₂ᵢ₋₁` is the left end `u` of a member `[u, v]` of `I`, and `x₂ᵢ₋₂` the right end of
one. For the crossing component `C` with interval `[u, v]`, `Cl C` meets `d⁻¹(u)`; if `d⁻¹(u)` were
inside `π⁻¹[D]`, so would be `d⁻¹[[u − η, u]]` (upper semicontinuity), a continuum meeting `C`, hence
inside `C ⊆ d⁻¹[[u, v]]` — impossible. So `d⁻¹(u)` meets `Fr π⁻¹[D]`, over a closed side segment
(not over `I₂` by T7, not over the bottom edge since `u > x₂`). Likewise `d⁻¹(x₂ᵢ₋₂)` with
`d⁻¹[[v′, v′ + η]]`. Which side is not determined by the argument. At `i = 2` the presupposition is
false (`blockLayersMeetSides_false`).

**Effect on E2–E3.** E2's saturation hypothesis and the case split are discharged:
`hagopian76_theorem1_of_cases4` needs only `StepFrame`, `LastStepClaims`, `Case1ClaimsE24`,
`Case2ClaimsE24`. In E3, `d⁻¹(x₃)` meets a closed side segment (`layer_x3_meets_side`: the argument
at the left end works already for `i = 2`, since `x₃ > x₂`; only the right end `x₂` fails at `i = 2`);
which side is still not decided, so the band at the last step is located up to the two sides.

## 4. Summary of named items

| Step | Status | Lean name |
| --- | --- | --- |
| order of pieces | proved | `crossing_piece_sides`, `crossing_piece_below_iff`, `crossing_piece_below_trans` |
| SSL and converse | proved | `strand_separation`, `strand_separation_converse` |
| strands miss `F` | proved | `strand_misses_F_of_composant` |
| unicoherence | proved | `separatesPlane_union_of_inter_disconnected` |
| 3b | Prop | `InnerComponentsCross` |
| 3c | proved (saturation as hypothesis) | `block_components_cross` (batch 181) |
| 4.B | open shape | `p_on_crossing_piece` |
| E0, E1 | proved (saturation as hypothesis) | `property4_strand`, `property4_step_unless_setup` (batch 181) |
| §3.1, cap lemma, ending of Case 1, (c) of Case 2 | proved | `f_mem_O_of_mem_K`, `cross_strand_near`, `case1_ending`, `case2_ending` (batch 181) |
| E2.1, §3.4–§3.6, Case 2 (a), (b), (d), (e) | Prop | `Case1Claims`, `Case2Claims` (batch 181) |
| E | proved, conditional | `hagopian76_property4_step_cond` (batch 181) |
| §1.1 certificate (batch 182) | proved | `blockLayersMeetSides_false` |
| last step (batch 182) | proved (ending), Prop (claims) | `last_step_ending`, `LastStepClaims`, `not_property4_x3x4` |
| orientation (batch 182) | proved | `cross_strand_near_above`, `cross_strand_near_o`, `case1_ending_oriented`, `case2_ending_oriented` |
| honest claims (batch 182) | Prop | `StepFrame`, `StepStrands`, `BlockLayersMeetSides3`, `Case1Claims'`, `Case2Claims'` |
| E, Theorem 1 (batch 182) | proved, conditional | `hagopian76_property4_step_cond2`, `hagopian76_theorem1_of_cases2` |
| E2.4 steps 1–2 (batch 183) | proved | `Thm1Setup.cap_point_o`, `Thm1Setup.near_strand_cross_o`, `e24_pair_between`, `e24_pair_below` |
| E2.4 step 3 (batch 183) | proved | `minimalAdmissible_restrict_of_lsc`, `minimalAdmissible_restrict` |
| E2.4 steps 4–6 (batch 183) | Prop | `E24Claims`, `Thm1Setup.FarFrom` |
| E2.4 (batch 183) | proved, conditional | `property2_violation`, `e24_between_false`, `e24_below_far`, `E24Data.far` |
| Theorem 1 (batch 183) | proved, conditional | `Case1ClaimsE24`, `Case2ClaimsE24`, `hagopian76_theorem1_of_cases3` |
| §3 between, §4 (a), (b), (e), §5, §6 (batch 183) | open | report `doc/batches/REPORT-batch183.md` |
| saturation 2e (batch 185) | proved | `half_in_O_false`, `noncrossing_half_in_O_steps45`, `innerComponentsCross_hagopian` |
| rigidity, runs (batch 185) | proved | `layers_agree`, `translate_run`, `translate_run_right` |
| case split `i ≥ 3`, `d⁻¹(x₃)` (batch 185) | proved | `blockLayersMeetSides3`, `layer_x3_meets_side` |
| Theorem 1 (batch 185) | proved, conditional | `hagopian76_theorem1_of_cases4` |
| §3.3 runs of `F`, §6 between with runs (batch 185) | open | report `doc/batches/REPORT-batch185.md` |
