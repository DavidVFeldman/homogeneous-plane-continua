# Commission: batch 181 — Part E, Hagopian 1976 XXVI: Theorem 1 — saturation; 3c; Case 1 strand by strand; Case 2 sentence by sentence

**Go!** This batch runs on top of the batch-180 work. Two files come with it, as separate uploads:

* `COMMISSION-batch181.md`: this text, also pasted into the prompt.
* `Hagopian76Z.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76Z.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76Z` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXVI (batch 181)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers;
  * `H76Thm1Setup.lean`, for the two fields of §3.1;
  * `H76Tip.lean`, if §1.4 relaxes a hypothesis there;
  * `doc/notes/hagopian76-cases.md`: rewrite E2.5 and E2.6 as §3 and §4 below say.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 180

* **Delivery.** The tarball and the manifest from `git diff` worked again. Keep doing it (§8.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2051 lines (2032 + 19 added, none removed), with `sorryAx` in none.
  All 21 audited declarations (19 new, 2 restated) use only the standard three axioms.

**Accepted, all of it.** This includes:
* the extra field for the vertical over `15/22`;
* `ε₂ = min(ε₁, δ, 1/4)` and `ε₃ = min(ε₃′, θ/2)`;
* the strengthened tip lemmas, which need only the extreme point over `D`;
* 2b as the case `b = τ + δ` of 2a;
* the non-vacuity notes.

**Two of my errors, found through your report** (ledger C.3):
1. **E2.5.2.** You are right that the distance from `π⁻¹[[3/8, 5/8] × [0, c₁/2]]` to `Y` is `0`.
   My cases note was wrong. §3 replaces the whole Janiszewski route of E2.5 with a strand-wise
   ending, which needs a different bound (§3.1–§3.2).
2. **Case 2.** Your answer to commission 180 §4.5 stands, but my question was the wrong one. In the
   printed case, `yᵢ₋₁` is *between* `d⁻¹[I]` and `d⁻¹[J]` and *within* `ε₃` of `d⁻¹[I]`. So
   "`Cᵢ₋₁` is above `d⁻¹[I]`" conflicts with the case it was meant to serve. §4 takes the printed
   sentences one at a time.

**Also corrected in my ledger.** "`f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`" (p. 348) was recorded as
verified. `eps3_positions_middle` assumes the membership. §3.1 supplies it.

## 1. Saturation: 2d and 2e

Target: `innerComponentsCross_hagopian (S : Thm1Setup M)` on `(3/22 + 8/n, 19/22 − 8/n)`. Your four
missing pieces (report 180 §2.5), with routes.

### 1.1 Step 2 of commission 178 §3b (`noncrossing_half_in_O`)

Let `y = h(e)` (S1) lie over the interval, and let `W` be its component in `F ∩ O`. If both `K⁻` and
`K⁺` leave `O`, then `W` is a crossing piece.
1. Boundary bumping in `K⁻` (`exists_mem_closure_component_notMem`) gives a component of `K⁻ ∩ O`
   through `y` whose closure meets `Fr O`. It lies in `W`.
2. That frontier point is not over `I₂` (T7).
3. It is not over the bottom edge. `W ⊆ F − E`, and the closure of `F − E` meets `E` only in the end
   layer `d⁻¹(e) = k⁻¹(1)`, which is not over `[3/22, 19/22]`. Compare the bottom-edge case in
   `degenerate_chunk_iii`.
4. It is not over the right side. By S0, a point of `h[k⁻¹[[0, k(e)]]]` over the collar has abscissa
   `< k(e) + 2/n < 19/22`.
5. So the closure of `W` meets the left side segment. Its height lies strictly between `0` and
   `r₂`, as in `side_point_open`.
6. The right side is symmetric, using `K⁺`.
7. The other fields of `IsCrossingPiece` hold as in `isCrossingPiece_of_crossingComponent`.

### 1.2 The points `zⱼ` (2d.3–2d.4)

As in your list:
* `zⱼ → c` in `F ∩ U` with `d(zⱼ) < 1`, by the void interior of `d⁻¹(1)` in `F`;
* for large `j`, the component `Wⱼ` is non-crossing (`crossing_components_finite`; a crossing
  component is closed in `O`; `c` lies in the non-crossing `W`);
* `zⱼ` lies over the interval of §1.1 for large `j`, since `c` lies over
  `(3/22 + 4/n, 19/22 − 4/n)`. If that is not enough for §1.1 at `zⱼ`, choose `c` with a larger
  margin; `n = 40` leaves room.

### 1.3 (iii) at `zⱼ` (2d.5)

As commission 180 §2.2: `c ∈ hⱼ[E]` would put `c` in the strand `Sⱼ` of `zⱼ`, hence `Sⱼ = S`, hence
`zⱼ ∈ S ⊆ h[E]`, against `zⱼ ∉ h[E]`.

### 1.4 The edge case

`tip_triod` takes any `b ≥ τ`. It does not ask for `K⁻ ⊆ O`, only for the extreme point to lie over
`D`. Use this:
1. **Take `b` up to `1`.** The edge case is then: every point of `F ∩ hⱼ[E]` off `d⁻¹(1)` lies on
   the tip layer `Tⱼ = hⱼ[k⁻¹(τ)]`. Otherwise `tip_triod` (or `tip_triod_on_tip_layer`) with
   `b = 1` applies, with (iii) from §1.3.
2. **If `F ∩ hⱼ[E] ⊆ Tⱼ`.** `Wⱼ` lies in the closure of the strand of `zⱼ`, hence in `hⱼ[E]`, hence
   in `Tⱼ`. By S0, the points of `Tⱼ` over the collar lie over abscissae within `2/n` of `τ`, inside
   `(3/22, 19/22)`. Boundary bumping in `F` (`F ⊄ O`, since `E ⊆ F`) makes the closure of `Wⱼ`
   meet `Fr O`. That is possible only over the bottom edge or over `I₂`, and both are excluded as
   in §1.1.
3. **Otherwise.** `Λ₁(zⱼ) = d⁻¹(1) ∩ hⱼ[E]` is a continuum with parameter interval `[τ, τ₁]`,
   `τ₁ > τ`. Every point of `F ∩ hⱼ[E]` with parameter `> τ` lies in `d⁻¹(1)`, so `F` misses
   `hⱼ[k⁻¹((τ₁, 1])]`.
   * If `τ₁ < 1`, use the mirror triod at `σ = τ₁`, with (i) given by `zⱼ` itself (parameter
     `τ ≠ σ`, off `d⁻¹(1)`).
   * `tip_triod_mirror` asks for the extreme point over `D`. It uses this only to bound `σ` away
     from `1` (`tip_param_high`). Relax that hypothesis to the bound itself (edit `H76Tip.lean`, or
     add a variant). Then check that `τ₁` satisfies it, or find the bound the proof really needs.
4. **If `τ₁ = 1`.** Then `d⁻¹(1)` contains `hⱼ[k⁻¹((τ, 1])]`, a whole end piece of the translate.
   Decide whether this contradicts 3a, no hair, or the void interior of `d⁻¹(1)` in `F`. If it
   resists, describe the configuration exactly.

### 1.5 2e

Assemble `innerComponentsCross_hagopian` from §1.1–§1.4 with `tip_triod`, its mirror,
`tip_triod_on_tip_layer` and `degenerate_chunk_iii`. Give the case tree in the report.

## 2. 3c, then E0 and E1

### 2.1 3c by the irreducible interval (`block_components_cross`)

Use your shape from the open block of `Hagopian76Y.lean`, with `InnerComponentsCross` as a
hypothesis. `lemma3_half` is not needed:
1. Take `z ∈ d⁻¹[B] ∩ O` over the interval, with `B = [x₂ᵢ₋₁, x₂ᵢ]`, and let `C` be the component
   of `z` in `F ∩ O`. By `InnerComponentsCross`, `C` is a crossing piece. Translate it to
   `IsCrossingComponent` (closed side segments).
2. Its irreducible interval `[u, v]` is in `I` and contains `d(z)`, since `C ⊆ d⁻¹[[u, v]]`.
3. `[u, v]` lies inside some block `B′` (`IsBlocks`). The blocks are pairwise disjoint (strict
   monotonicity), and `d(z) ∈ B ∩ B′`, so `B′ = B`.
4. So `C ⊆ d⁻¹[B]`, and the component of `z` in `d⁻¹[B] ∩ O` is `C`.

Corollary: the gap layers miss the points over the interval. Commission 178 §3c also claimed that
the end layers of blocks miss the middle. Drop that claim unless E0/E1 need it, and say whether they
do.

### 2.2 E0 and E1 (`property4_step_unless`)

The printed text (p. 348): "Suppose `I` has Property 4. For convenience we suppose `d⁻¹[J]` is below
`d⁻¹[I]` and `f(yᵢ)` is above `d⁻¹[I]`. (Other cases are handled with similar arguments to that
given in this case.) Then `d⁻¹[J]` separates `yᵢ` from `f(yᵢ)` in `π⁻¹[D]` and `J` has Property 4
unless `yᵢ` is above `d⁻¹[J]`, so we suppose `yᵢ` is between `d⁻¹[I]` and `d⁻¹[J]`."

In strand terms, with 3c and `sepByCrossing_of_inner_crossing`:
* Property 4 for `I` gives an `I`-strand `S_I` separating `yᵢ` from `f(yᵢ)`. Say `yᵢ` is below
  `S_I`.
* If some `J`-strand `S_J` has `yᵢ` below `S_J` and `S_J` below `S_I`, then `S_J` separates
  `yᵢ` from `f(yᵢ)` (S4d, then SSL converse). Property 4 for `J` holds at `yᵢ` itself.
* Otherwise `yᵢ` is "between", in the sense of (β).

**The parenthesis.** "Other cases are handled with similar arguments" covers four configurations:
`f(yᵢ)` above or below `S_I`, and the relative order of the blocks. Your frame is not symmetric
top to bottom: the bottom edge lies over `E`, the top over `I₂`. Say which cases are mirror images,
and what each mirror needs. For instance, the cap lemma of §3.2 needs its mirror: the region below
a crossing piece has closure missing `π⁻¹[I₂]`.

## 3. Case 1, strand by strand

The printed Case 1 (pp. 348–349) is quoted in `doc/notes/hagopian76-cases.md`. Here it is in strand
terms. Write `S_I` and `S_J` for the `I`-strand and the `J`-strand adjacent to the point in
question, as in (β).

### 3.1 Two fields of `Thm1Setup` (restate in place)

Both are chosen after `D` and before `F` and the package. Both hold for small `ε₃` by compactness.
Let `Mid` be the set of points of `M ∩ O` over abscissae in `[1/2 − 2/n, 1/2 + 2/n]`. It contains
`K`: `K₀` lies over `1/2`, and `p = h(x₀)` with `k(x₀) = 1/2` lies over that range by S0.
1. **`hε₃O`: every point of `M − E` within `ε₃` of a point of `Mid` lies in `O`.**
   * Route: a short segment from a point of `Mid` to a point outside `O` meets `Fr O`.
   * It cannot meet `π⁻¹[I₂]`, since `ε₃ < ε₂`.
   * It cannot meet the side preimages, by field 2.
   * Near the bottom edge, the only points of `M` outside `O` are those of `E`, because the strip
     below misses `M` (`hstrip`). Use the uniform continuity of `π` on a compact neighbourhood.
   * Consequence: `f(y) ∈ O` for `y ∈ K`. `f(y) ∉ E` because `f(y) ∈ h₁[R(E)]`, and `h₁[R(E)]`
     misses `R(E) ⊇ E` (the composant choice, `hcomp`). This is p. 348 "Note that `f(yᵢ₋₁)`
     belongs to `L₆ ∩ π⁻¹[D]`", and Property 4 needs it: `SepIn` asks for both points in `O`.
2. **`hε₃S`: every point of `Mid` is at distance `≥ ε₃` from `π⁻¹F[{3/22, 19/22} × [0, c₁]]`.**
   The closure of `Mid` and that preimage are disjoint compact sets.

### 3.2 The cap lemma

1. **`above_closure_misses_bottom`.** For a crossing piece `W` of `lowFrame`, the closure of
   `V.above W` misses `π⁻¹` of the open bottom edge. Route:
   * `D′` contains a low rectangle `(3/22, 19/22) × (0, c₀)` (`rect_domain_low`).
   * `π[Cl W]` is compact and misses the bottom edge, so it stays above some height `c_W > 0`.
   * The points of `O` over `(3/22, 19/22) × (0, min(c₀, c_W))` form a connected set. It misses
     `Cl W` and contains the foot of `σ`, so it lies in `V.below W`.
   * A point of `π⁻¹` of the open bottom edge has a neighbourhood whose part in `O` lies there.
2. **`cross_strand_near`.** Let `W` be a crossing piece, `a ∈ Mid ∩ V.below W`, `b ∈ V.above W`,
   and `dist a b < ε₃`. Then `ρ(a, Cl W) < ε₃`.
   * Route: the segment `[a, b]` is connected, so it meets the frontier of `V.above W`.
   * By 1, that frontier lies in `Cl W ∪ π⁻¹[I₂] ∪ π⁻¹(sides)`.
   * The last two are excluded by `hε₂I` (with `ε₃ < ε₂`) and `hε₃S`.
3. The mirror (§2.2): `V.below W` has closure missing `π⁻¹[I₂]`, if the mirror cases need it.

### 3.3 E2.1: `Cᵢ₋₁` and `L`

Printed (p. 348): "Let `Cᵢ₋₁` be the first component of `M ∩ π⁻¹[D]` (whose closure intersects
`π⁻¹[⟨p₁, r⟩]` and `π⁻¹[⟨p₅, s⟩]`) that is met by extending `Cl Cᵢ` away from `X` in `M`. The
existence of `Cᵢ₋₁` follows from the indecomposability of `Cl R(X, Cl Cᵢ)` (Lemma 6 (proof)) and an
argument similar to the one for Property 3. Note that `Cl Cᵢ₋₁` is essential to `h[R(E)]`. Let `L`
be the shortest extension of `Cl Cᵢ` away from `X` that contains `Cᵢ₋₁`."

Prove, or state as named `Prop`s:
1. some extension of `Cl Cᵢ` away from `X` meets a crossing component other than `Cᵢ`;
2. there is a first one, by intersecting a chain of extensions (`ExtChainInter`, batch 170);
3. `L`, the shortest extension containing it;
4. `Cᵢ₋₁` is a crossing piece contained in `M`, so `Thm1Setup.K_meets_crossing` gives `yᵢ₋₁`;
5. `Cl Cᵢ₋₁` is essential to `h[R(E)]`;
6. `L ∩ F = ∅`.

### 3.4 "`yᵢ₋₁` is between `d⁻¹[I]` and `d⁻¹[J]`" (p. 348, unargued)

"By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see that `yᵢ₋₁` is between `d⁻¹[I]` and
`d⁻¹[J]`." Decide whether this follows from:
* the Case 1 hypothesis (both `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` meet the left side, as does `Z`);
* the minimality of `L` and `L ∩ F = ∅`;
* the order of strands.

Your batch-180 configuration (`L` leaves `D` through a side segment and re-enters on the other side
of a strand's end) may block it here too. If it does, give it as a configuration for Case 1, and
state the claim as a named `Prop`.

### 3.5 E2.4

"The point `yᵢ₋₁` is below `Cᵢ` and `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`; for otherwise, a subcontinuum of `L`
would violate Property 2." Identify the subcontinuum `H` and its end sets, and check each hypothesis
of `Property2At`:
* `H` is essential to `h[R(E)]`;
* `H` has a minimal admissible decomposition;
* its end sets are within `ε₃`;
* some layer is farther than `ε₂` from the first end set.

Then the conclusion must fail: `H` does not come within `ε₂` of every point of `R(E)`.

### 3.6 The band

"Consider the continuum `P` … the union of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` and an arc segment `Q` in
`π⁻¹[D ∩ ⟨p₄, q₄⟩] − d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` that has one end point in `d⁻¹[I]` and the other in
`d⁻¹[J]`. Since no point of `N` is within `ε₂` of `Q`, the continuum `f[N]` does not intersect `P`.
Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`."
1. `Q` per (α): the segment of the vertical over `15/22` (the field `w₃`) that `Cᵢ` meets first from
   the left.
2. `P` separates the band, between `S_J` and `S_I` and left of `Q`, from `f(yᵢ)`. Use
   `separatesPlane_union_of_inter_disconnected`.
3. `f[N] ∩ d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] = ∅`. Indeed `f[N] ⊆ h₁[R(E)]`, `F ⊆ R(E)`, and `hcomp` makes
   `h₁[R(E)]` miss `R(E)`.
4. `f[N] ∩ Q = ∅`, from "`N` is `ε₂`-far from `Q`" and `ε₃ < ε₂`. The printed reason (p. 348) is
   about `π⁻¹(p₄)`, not `Q`. Prove it for `Q`:
   * the part of `N` in `O`, by positions (`hε₂V`);
   * the part of `N` outside `O`: a point of `M − E` within `ε₂` of `Q` lies in `O` or is joined
     to `Q` by a short segment through `π⁻¹[I₂]`, against `hε₂I`. `N ∩ E = ∅`, since `L ∩ F = ∅`.

   This may need `ε₂` small with respect to a modulus of continuity of `π` and to `cs`. If so, add
   that bound to the set-up (Property 2 holds at every `ε₂ > 0`).
5. So `f(yᵢ₋₁)` lies outside the band. Since `f(yᵢ₋₁) ∈ O − F` (§3.1), it is above `S_I` or below
   `S_J`.

### 3.7 The ending

"It is not above `d⁻¹[I]` because `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃` and `ρ(yᵢ₋₁, f(yᵢ₋₁)) < ε₃`. Hence `J`
has Property 4."
1. Not above `S_I`: by `cross_strand_near` with `a = yᵢ₋₁` and `W = S_I`, against E2.4.
2. So `f(yᵢ₋₁)` is below `S_J`, while `yᵢ₋₁` is above `S_J`. The SSL converse gives
   `SepIn O (Cl S_J) yᵢ₋₁ f(yᵢ₋₁)`, hence separation by `d⁻¹[J]`. With 3.3.5, Property 4 for `J`
   holds at `yᵢ₋₁`.

### 3.8 `case1`

State Case 1 as one theorem. Its hypotheses are the set-up, the blocks, Property 4 for `I`, the
Case 1 configuration, and named `Prop`s for whatever of §3.3–§3.6 stays open. Its conclusion is
Property 4 for `J`.

## 4. Case 2, sentence by sentence

Printed (p. 349): "Suppose `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` intersect different elements of
`{π⁻¹[⟨p₁, r⟩], π⁻¹[⟨p₅, s⟩]}`. We assume without loss of generality that `π⁻¹[⟨p₅, s⟩]` meets
`Z`, `d⁻¹(x₂ᵢ₋₁)`, and `d⁻¹(x₂ᵢ₋₃)`. Define `Cᵢ₋₁`, `L`, `yᵢ₋₁`, and `N` as in Case 1. If `yᵢ₋₁` is
above `d⁻¹[J]`, it is between `d⁻¹[I]` and `d⁻¹[J]`, and `f(yᵢ₋₁)` is above `d⁻¹[I]`. Since both
`yᵢ` and `yᵢ₋₁` are within `ε₃` of `d⁻¹[I]`, it follows as in Case 1 that a subcontinuum of `L`
violates Property 2. Hence `yᵢ₋₁` is below `d⁻¹[J]` and `f(yᵢ₋₁)` is above. Therefore `J` has
Property 4."

Note the third hypothesis names `x₂ᵢ₋₃`, not `x₂ᵢ₋₂`. Take each claim in turn.
* **(a) "If `yᵢ₋₁` is above `d⁻¹[J]`, it is between `d⁻¹[I]` and `d⁻¹[J]`."** That is, not above
  `S_I`. As in §3.4.
* **(b) "… and `f(yᵢ₋₁)` is above `d⁻¹[I]`."** Split off the good case first. If `yᵢ₋₁` is between
  and `f(yᵢ₋₁)` is below `S_J`, then `J` has Property 4 at once (§3.7.2). Otherwise (b) is the band
  argument of §3.6. Does the band of Case 1 exist in Case 2, where the gap continuum's ends meet
  different sides? With which `Q`?
* **(c) "Since both `yᵢ` and `yᵢ₋₁` are within `ε₃` of `d⁻¹[I]`."** By `cross_strand_near`, for
  `yᵢ` (below `S_I`, `f(yᵢ)` above) and for `yᵢ₋₁` (in the case of (b)).
* **(d) "… it follows as in Case 1 that a subcontinuum of `L` violates Property 2."** Identify the
  subcontinuum as in §3.5. Here both ends of `N`, not one, are near `d⁻¹[I]`.
* **(e) "Hence `yᵢ₋₁` is below `d⁻¹[J]` and `f(yᵢ₋₁)` is above."** When `yᵢ₋₁` is below `S_J`, the
  band leaves `f(yᵢ₋₁)` above `S_I` or below `S_J`. Nothing printed excludes the second, and then
  `J` does not separate. Decide whether it can be excluded:
  * by Property 2, applied to `N` and `f[N]`;
  * by the Case 2 configuration;
  * by choosing `yᵢ₋₁` differently in `K ∩ Cᵢ₋₁`.

  If not, give the configuration.

For each claim: proved, refuted (with the configuration), or a named `Prop`. Then state `case2` as
one theorem, conditional on what stays open.

## 5. The step

`hagopian76_property4_step` from §2.2, `case1` and `case2`, for the repaired set-up. It will be
conditional on the named `Prop`s of §3–§4. State it in its strongest conditional form, and update
`hagopian76_theorem1_of_step` if a cleaner reduction results.

## 6. Order

1. §1 (saturation), and §3.1–§3.2 (fields, cap lemma).
2. §2.
3. §3.3–§3.8.
4. §4, then §5.

## 7. Places to check (candidate ledger entries)

1. **p. 348, "Note that `f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`"**: the membership, through `hε₃O`.
2. **p. 349, "It is not above `d⁻¹[I]` because …"**: the segment may leave `π⁻¹[D]` through the
   bottom edge; the cap lemma.
3. **p. 348 / p. 349, `N` and `π⁻¹(p₄)` versus `N` and `Q`.**
4. **p. 348, "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` …"** (§3.4).
5. **p. 348, "(Other cases are handled with similar arguments …)"**: which cases are mirrors, and
   whether the frame's asymmetry matters.
6. **p. 349, Case 2**: claims (a)–(e), and "`x₂ᵢ₋₃`" in the hypothesis. Is it a misprint for
   `x₂ᵢ₋₂`?
7. **The end layer of `F`** (§1): the edge case.

## 8. Deliverables

1. The items of §1–§5.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch181.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. `doc/notes/hagopian76-cases.md`: replace E2.5 by §3.6–§3.7, E2.6 by §4, and mark what is proved.
4. **Publish the changes, as in batch 180.** At the end of the run:
   * create `doc/batches/batch181-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch181-MANIFEST.txt`;
   * publish both, as you published the report.
5. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
