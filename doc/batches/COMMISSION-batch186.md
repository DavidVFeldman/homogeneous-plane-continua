# Commission: batch 186 — Part E, Hagopian 1984 III: the quotient package; Lemmas 12–16

**Go!** This batch runs on top of the batch-185 work. Three files come with it, as separate uploads:

* `COMMISSION-batch186.md`: this text, also pasted into the prompt.
* `Hagopian84B.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian84B.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian84B` at the end of `HPC.lean`. It imports
    `HPC.Hagopian.Hagopian76AC`.
* `jones1975.pdf`: F. B. Jones, *Use of a new technique in homogeneous continua*, Houston J. Math.
  1 (1975), 57–62. Save it as `doc/sources/jones1975.pdf` (for §6).

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule).** For every theorem whose hypotheses include a named `Prop` or a
  structure standing for open work, the report gives a note with the two checks:
  1. the hypothesis is not refuted by a short argument from the set-up;
  2. it is not equivalent to the conclusion it is used for, unless the printed argument is a proof
     by contradiction.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1984 III (batch 186)");
  * `README.md`;
  * `LEDGER.md`: the Hagopian 1984 section;
  * `OPEN.md`;
  * `doc/notes/hagopian84.md`;
  * `Hagopian84A.lean`: delete the commented-out copies of statements proved here, leaving one-line
    pointers.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 185

* **Delivery.** The tarball and the manifest worked again. The project download is stale (1929
  lines); I overlaid the tarball on my batch-184 tree. Keep doing it (§9.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2261 lines (2197 + 64 added, none removed), with `sorryAx` in none.
  The 62 new declarations use only the standard three axioms. In `Hagopian76AC.lean`,
  `Hagopian76AB.lean` and `Hagopian84A.lean`, `sorry` occurs only inside comments.
* **Checked.** I read the statements of `hagopian84_lemma7`, `layers_agree`, `translate_run`,
  `innerComponentsCross_hagopian`, `blockLayersMeetSides3` and `hagopian76_theorem1_of_cases4`.
  The last takes exactly the four named `Prop`s, and saturation needs nothing beyond `Thm1Setup`.
* **Your Lemma 7 route** avoids the three printed atriodicity steps. I record "By Lemma 4, there is
  a continuum `H` of type λ in `M` such that (1) `E` is an essential subcontinuum of `H` that misses
  both end sets of `H`" as a gap in exposition: Lemma 4 extends `E` on one side only.
* **A slip I found (p. 340, Lemma 13).** Claim (5) is printed without `h`: "(5) if `0 ≤ r < t ≤ 1`
  and `k⁻¹(r) ∪ k⁻¹(t) ⊂ Lᵢ`, then `k⁻¹[[r, t]] ⊂ Lᵢ`." Its proof ("there exist numbers `r`, `s`,
  and `t` … such that `h[k⁻¹(s)] ⊂ Lᵢ`") and its use in (6) ("`h[E]` runs straight through `𝔏`")
  are about `h[k⁻¹(r)]`, `h[k⁻¹(t)]`, `h[k⁻¹[[r, t]]]`. Read (5) with `h`, and record the slip.
* **Indexing.** As in `Hagopian84A.lean`, the links are `L 0, …, L 4` (the paper's `L₁, …, L₅`), and
  `midUnion L = L 1 ∪ L 2 ∪ L 3` is `⋃𝔏′`. The paper's `P₃` is `P 2`. Below, paper indices appear
  only inside quotations.

## 1. The plan

With `N = M`, Theorem 1 of 1984 gives `Hagopian84Decomp`; with `NoArcIndecHomPlane` it gives
Theorem 1 of 1976 (`hagopian76_theorem1_of_jones`, verified). Lemma 7 and the two-sided extension
are done. What remains for `Hagopian84Decomp`:
* Lemmas 12–16;
* the construction of pp. 343–344: `K(Z)`, `X(Z)`, `F(Z)`, `J(Z)`, `𝒫(Z)`, the cover `𝔅`, the
  disjointness of `𝔇`, and claims (5) and (6);
* the arc in `M/𝔇` (unargued in the text).

Not needed with `N = M`: Lemmas 8 and 10, claim (4), the solenoid conclusion, and the last
paragraph of the proof (the elements of `𝔇` hereditarily indecomposable).

This batch: the quotient package (§2), which separates the topology of `M/𝔇` from the
construction; Lemmas 12–13 (§3); Lemmas 14–15 and the arc (§4); Lemma 16 (§5). Last, a
reconnaissance of Jones 1975 for the arc step (§6). The construction of pp. 343–344 is for a later
batch.

## 2. The quotient package

**2.1 Statement** (skeleton: `IsJonesDecomp84`, `hagopian84Decomp_of_package`). A setoid `r` on `M`
is a *Jones decomposition* if
1. it is upper semicontinuous (`IsUSCDecomp r`, `HPC/Jones/Decomp.lean`);
2. its classes are connected;
3. no class is `M`;
4. for some `δ > 0`, every `δ`-homeomorphism maps classes into classes;
5. some compact `C ⊆ M` carries a continuous surjection `c : C → [0, 1]` with `c x = c y ↔ r x y`
   for `x, y ∈ C`.

Prove `Hagopian84Decomp` from: every `M` as in `Hagopian84Decomp` has a Jones decomposition.

**2.2 Route.**
* `Y := Quotient r`. It is Hausdorff and second countable (`t2Space_quotient`,
  `metrizableSpace_quotient`) and compact (an image of `M`). Give it the metric of
  `TopologicalSpace.metrizableSpaceMetric`.
* `q := Quotient.mk r` is continuous and onto. Its fibres are the classes: connected by (2), proper
  by (3).
* **Homogeneity.** Let `G` be the homeomorphisms of `M` that are finite compositions of
  `δ`-homeomorphisms, with `δ` from (4). The inverse of a `δ`-homeomorphism is one, so each element
  of `G` respects `r` in both directions. The orbit of a point is open: it contains `Wset84 y δ`
  for each of its points `y`, open by `hagopian84_lemma1`. The orbits partition `M`, which is
  connected, so there is one orbit. Then use `exists_homeomorph_quotient`. This replaces the chain
  of points `vᵢ` on p. 344, which is the same argument written out.
* **The arc.** The composite `C → M → Y` is constant on the fibres of `c`. Since `c` is a closed map
  onto `[0, 1]`, it is a quotient map, so the composite factors through a continuous
  `φ : [0, 1] → Y`. By (5), `φ` is injective; from a compact space to a Hausdorff one it is an
  embedding. Take `α := range φ`.

The hypothesis of `hagopian84Decomp_of_package` stands for open work: give the non-vacuity note.

## 3. Lemmas 12 and 13: the chain

**3.1 Lemma 13** (p. 339): "Suppose `ε` is a positive number, `A` is a closed set that misses `E`,
and `B` is an open set that contains `k⁻¹(0) ∪ k⁻¹(1)`. Then `E` runs straight through a free normal
regular chain `𝒫 = {Pᵢ: 1 ≤ i ≤ 5}` in `M∖A` with the property that `B` contains `Cl(P₁ ∪ P₅)` and
for each component `K` of `⋃𝒫′` there is an ε-homeomorphism `h` of `M` onto `M` such that `Cl K` is
an essential subcontinuum of `h[E]`." Shape: the commented-out block of `Hagopian84A.lean`.

Route, following the printed proof with these additions.

1. **The links.** The numbers `x₀ < … < x₁₅` and `δ` as printed. `Lᵢ := W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)`,
   where `W(S, δ)` is the union of `Wset84 x δ` over `x ∈ S` (skeleton: `WsetOf`, `chainLinks84`).
   It is open by Lemma 1 and lies in the `δ`-neighbourhood of `S`.
2. **"Note that `𝔏` is a normal chain in `M∖A`"** (unargued). This follows from `δ < ρ(A, E)` and
   `2δ < ρ(k⁻¹[[0, xᵢ]], k⁻¹[[xᵢ₊₁, 1]])`. Consecutive links meet in `k⁻¹(x₃ᵢ₊₃)`.
3. **(1)–(4)** for a `δ`-homeomorphism `h`, as printed. Use Lemma 3 (`hagopian76_lemma3`) with the
   translate's map (`exists_image_map`), and Lemma 1 with Effros for (4). Two sentences are
   unargued: "It follows from the definition of `δ` that `r ∈ [x₂, x₁₃]∖[x₃ᵢ₋₃, x₃ᵢ]`", and "There
   exist a number `s` in `[x₃ᵢ₋₃, x₃ᵢ] ∩ [x₂, x₁₃]` …". My reading:
   * a layer `h[k⁻¹(r)]` that meets a link lies within `2δ` of that link's range of layers, so by
     the `½ρ` bounds `r` is within one step `xⱼ` of the range;
   * `s` at a meeting point is within one step of `r`;
   * the end-set hypotheses of Lemma 3 hold because `r, s ∈ [x₂, x₁₃]` and
     `2δ < ρ(k⁻¹[[0, x₁]], k⁻¹[[x₂, 1]])`, and the same at the far end.
4. **(5), the fold.** The printed reduction, "By (1), (2), and (3), there exist numbers `r`, `s`,
   and `t` (`0 ≤ r < s < t ≤ 1`) and an integer `i` (`1 ≤ i ≤ 4`) such that `h[k⁻¹(s)] ⊂ Lᵢ` and
   `h[k⁻¹(r) ∪ k⁻¹(t)] ⊂ Lᵢ₊₁∖Lᵢ`", is unargued and omits the mirror case. Split it in two.
   * **(a) Combinatorics** (skeleton: `exists_fold`). Put `Vᵢ := {u : h[k⁻¹(u)] ⊆ Lᵢ}`. These sets
     are open (upper semicontinuity of the layers, and (3)). They cover `[0, 1]` ((1) and (3)).
     Non-adjacent ones are disjoint (chain). Also `0 ∈ V₀∖V₁` and `1 ∈ V₄∖V₃` (by (2)). If some
     `Vᵢ` is not an interval, there is a *fold*: `r < s < t` and adjacent `p`, `q` with `s ∈ V_p`
     and `r, t ∈ V_q∖V_p`. My proof sketch:
     * each `u` lies in one `Vᵢ` or in two consecutive ones;
     * let `π(u) ∈ {1, 1½, …, 5}` be `i + 1` or `i + 1½` accordingly;
     * if some `Vᵢ` is not an interval, `π` is not monotone, so there are `u < w` with
       `π(u) > π(w)`;
     * let `m` be the least value of `π` on `[u, 1]`, taken at `s`.
     * If `m = q + 1½`: the last point of `[u, s]` outside `V_q`, and the first point of `[s, 1]`
       outside `V_q`, lie in `V_{q+1}∖V_q` (each lies in the closure of `V_q`, so in a neighbour of
       it, and `π ≥ m` there). This gives a fold.
     * If `m = q + 1` and `π(u) ≥ q + 2`: the same.
     * If `m = q + 1` and `π(u) = q + 1½`: go left of `u` from `0` (where `π = 1`). Either a point
       of `V_{q+1}∖V_q` appears before `s`, which is a fold around `s`; or one of `V_{q−1}∖V_q`
       appears, and then `u ∈ V_{q+1}`, with ends in `V_q∖V_{q+1}` on both sides, is a fold. When
       `q = 0`, take `r = 0`.

     Check the cases. The statement is all that matters.
   * **(b) Geometry: no fold.**
     * *Kind D* (`s ∈ Vᵢ`, `r, t ∈ Vᵢ₊₁∖Vᵢ`): Hagopian's argument with `g[k⁻¹[[0, x₃ᵢ₊₃]]]`.
       "Since `M` is atriodic … it follows that `g[k⁻¹[0, x₃ᵢ]] ⊂ h[k⁻¹[[r, t]]]`" is
       `subset_of_meets_avoids` (`H76Lemma3.lean`). The continuum meets the middle layer, and it
       misses the end layers of `h[k⁻¹[[r, t]]]`, which lie in `Lᵢ₊₁∖Lᵢ`. The contradiction is
       the distance from `g[k⁻¹(0)]` to `h[k⁻¹[[r, t]]]`.
     * *Kind U* (`s ∈ Vᵢ₊₁`, `r, t ∈ Vᵢ∖Vᵢ₊₁`): the mirror, with `g[k⁻¹[[x₃ᵢ₊₃, 1]]]` and
       `k⁻¹(1)`.

   So each `Vᵢ` is an interval, which is (5) with `h`. With (2) the intervals come in the order of
   the links.
5. **Regularity.** The text says: "Since `M` is atriodic, it follows from (6) and Lemma 6 that
   `Cl K` is an essential subcontinuum of `h[E]` that runs straight through `𝔏`." My reading:
   * `Cl K ⊆ Cl L 1 ∪ Cl L 2 ∪ Cl L 3`, which misses both end layers of `h[E]` (by (2) and
     normality);
   * `Cl K` meets `h[E]`, so `Cl K ⊆ h[E]` (`subset_of_meets_avoids`);
   * then `K = h[E] ∩ midUnion 𝔏 = h[k⁻¹((a, b))]` with `(a, b) = V₁ ∪ V₂ ∪ V₃`, an interval;
   * so `Cl K = h[k⁻¹[[a, b]]]` is essential (Lemma 6), and it runs straight: `a ∉ V₁`, so its
     end layer lies in `L 0∖L 1`.

   Every point of `midUnion 𝔏` lies on some `δ`-translate of `E` (definition of `W`), so every
   component meets one.
6. **The last paragraph** ("Since `δ < ε`, `M` is atriodic, and `𝒫` is a regular ordered
   refinement of `𝔏`, there is an ε-homeomorphism …") is unargued.
   * A component of `⋃𝒫′` lies in a component `K̂` of `⋃𝔏′`, so its closure lies in `h[E]`.
   * It is essential: it runs straight through `𝒫`, while a layer of `h[E]` meets at most two
     consecutive links.
   * The construction of 3.2 below also makes every component of `⋃𝒫′` a component of `⋃𝔏′`. If
     convenient, add that to Lemma 12's conclusion.

**3.2 Lemma 12** (p. 339): "Suppose `E` runs straight through a normal regular chain `𝔏 = {Lᵢ:
1 ≤ i ≤ 5}`. Suppose `k⁻¹(0) ⊂ L₁∖Cl L₂` and `k⁻¹(1) ⊂ L₅∖Cl L₄`. Then `E` runs straight through a
free normal regular ordered refinement of `𝔏`." Shape: the commented-out block. Three steps are
unargued; my readings:
1. "Since `𝔏` is regular, `E∖(A ∪ B)` is an essential subcontinuum of `E`": with the `Vᵢ` of 3.1.4
   for `h = id`, `E∖(A ∪ B) = k⁻¹[[a, b]]` with `0 < a < b < 1`.
2. "Since `M` is atriodic, `E∖(A ∪ B)` is a component of `M∖(A ∪ B)`": the component through it
   misses `k⁻¹(0) ⊆ A` and `k⁻¹(1) ⊆ B`, so it lies in `E` (`subset_of_meets_avoids`).
3. Moore 1962 Theorem 44: the compact form `exists_closed_split_of_no_connected`
   (`Fugate66BHU.lean`).
   * Applied to `M∖(A ∪ B)`, it gives disjoint closed sets `K₁ ⊇ E∖(A ∪ B)` and
     `K₂ ⊇ M∖⋃𝔏` covering `M∖(A ∪ B)`.
   * Take `C := M∖K₂`, so `Pᵢ = Lᵢ∖K₂` for `i = 1, 2, 3`.
   * `midUnion 𝔏` misses `A ∪ B`, so `⋃𝒫′ = midUnion 𝔏 ∩ K₁` is a union of components of
     `midUnion 𝔏`, and regularity carries over.
   * **Freeness** (unargued: "The chain `𝒫` … is a free normal regular ordered refinement").
     Suppose `y ∈ Bd ⋃𝒫` lies in `Cl ⋃𝒫′`. Then `y ∈ K₁ ⊆ ⋃𝔏`, and `y ∉ L 0 ∪ L 4`, so
     `y ∈ ⋃𝒫′`, which is absurd. Hence `y ∉ Cl ⋃𝒫′`, and `y ∈ Bd(L 0 ∪ L 4)`.

## 4. Lemmas 14 and 15; the arc

**4.1 The note on p. 341 and positivity.** "Note that since `𝒫` is regular, `Δ(𝒫)` is a
decomposition of `(⋃𝒫)∖Cl(P₁ ∪ P₅)`" (skeleton: `delta5_partition`). My reading:
* A layer of `Cl K` meeting `P 0` lies in it, and one meeting `Bd P 0` lies in `Bd P 0`. So the
  points of `⋃𝒫′∖Cl(P 0 ∪ P 4)` are covered by layers in `Δ(𝒫)`.
* An interior layer `Y` of `Cl K` inside `⋃𝒫′` lies in `K`: `K ∪ Y` lies between `K` and `Cl K`,
  so it is connected, and it lies in `⋃𝒫′`. So members of `Δ(𝒫)` from different components are
  disjoint.

Lemmas 14 and 15 use `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`. Its positivity is unargued (skeleton:
`delta5_dist_pos`). My reading:
* it suffices that `Cl ⋃Δ(𝒫) ⊆ ⋃𝒫′`;
* let `y` be a limit point of `⋃Δ(𝒫)` outside `⋃𝒫′`;
* if `y ∉ ⋃𝒫`, then `y ∈ Bd ⋃𝒫`, which by freeness misses `Cl ⋃𝒫′`, against `y ∈ Cl ⋃𝒫′`;
* so `y ∈ P 0 ∪ P 4`, an open set that misses `⋃Δ(𝒫)`, which is absurd.

**4.2 Lemma 14** (p. 341): "Suppose `𝒫` … is a free regular chain. Then the decomposition `Δ(𝒫)` of
`(⋃𝒫)∖Cl(P₁ ∪ P₅)` is continuous." Shape: the commented-out block (Hausdorff form).
* The printed "By Lemma 3, if `zᵢ` belongs to the open set `W(z, ε)` …, then there is an
  ε-homeomorphism `h` … such that `h[Z] = Zᵢ`" works with both layers in `Δ(𝒫)`.
* `Z` is an interior layer of `Cl K₀`. `Zᵢ` and `h[Z]` lie within `ε` of `⋃Δ(𝒫)`, which is at
  distance `2ε` from `M∖⋃𝒫′`, where the end sets lie.
* So `hagopian76_lemma3` applies; check its three hypotheses explicitly.
* For §2, upper semicontinuity is what is used.

**4.3 Lemma 15** (p. 341): "… there is a positive number `ε` such that if `Z ∈ Δ(𝒫)` and `h` is an
ε-homeomorphism of `M` onto `M`, then `h[Z] ∈ Ω(𝒫)`." Shape: the commented-out block.
* "By Lemma 3" does not suffice as printed. The layer `Y` of `Cl K′` through a point of `h[Z]` need
  not lie in `Δ(𝒫)`, and then Lemma 3's hypothesis "`Y` misses `h[`end sets of `Cl K]`" is not
  available.
* Proposal: take `ε` smaller than Hagopian's (the lemma only asks for some `ε`):
  `ε < ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`, and `2ε` less than the distance between `Cl P i` and `Cl P j` for
  `|i − j| ≥ 2`. Then:
  * `h[Z] ⊆ ⋃𝒫′` lies in one component `K′`;
  * `h[Cl K] ∩ Cl K′` meets two layers of `h[Cl K]`: otherwise `no_arm_at_interior_layer`, since
    the end layers of `Cl K′` lie outside `⋃𝒫′ ⊇ h[Z]`;
  * `layers_agree` (`h[Cl K]` against `Cl K′`) gives `h[Z]` a layer of `Cl K′`, unless `h[Cl K]`
    lies in one layer of `Cl K′`;
  * that degenerate case is impossible. `h` moves the end layers of `Cl K` into `P 0 ∪ P 1` and
    `P 3 ∪ P 4`, while a layer of `Cl K′` meets no two links `i`, `j` with `|i − j| ≥ 2`.

**4.4 The arc** (p. 344: "Since `M/𝔇` is an atriodic homogeneous continuum that contains an arc",
unargued; skeleton: `exists_interval_in_delta`). Let `Cl K` run straight through a normal chain.
* `Cl K` meets `P 2`: otherwise `P 0 ∪ P 1` and `P 3 ∪ P 4` separate it.
* The layer through such a point lies in `P 2` (a layer meeting `P 2` and `Bd P 2` would lie in
  `Bd P 2`), so it misses `Cl(P 0 ∪ P 4)` by normality.
* By upper semicontinuity the parameters of such layers form an open set, so it contains a closed
  interval `[a, b]`, `a < b`, of layers in `Δ(𝒫)`.

In the assembly, `C := layerSet c (Icc a b)` and the rescaled `c` give field (5) of §2.

## 5. Lemma 16

Lemma 16 (pp. 341–342): "Suppose `𝒫` … is a free regular chain. Suppose `K` is a component of `⋃𝒫′`
and `X` is an end set of `Cl K`. Suppose `F` is an extension of `Cl K` away from `X` and `𝔇` is the
decomposition of `F`. Then no element of `𝔇` intersects three consecutive links of `𝒫`." Shape:
the commented-out block.
* "Since no element of the decomposition of `Cl K` intersects three consecutive links of `𝒫`, it
  follows that `s > 0`": a layer meeting links `i` and `i + 2` meets `Bd P i` and so lies in it,
  by running straight.
* "Since `𝔇` is continuous (Lemma 5), `s ∉ S` and `s ≠ 1`": `S` is open by lower
  semicontinuity (`lsc_of_minimalAdmissible`).
* "Since `𝒫` is free, there exist a 3-linked subchain `𝔔` of `𝒫` and numbers `t`, `w` greater than
  `s` such that (1) …": unargued. Find an argument, or state the obstruction.
* The final appeal to uniqueness of the decomposition is `hagopian75_lemma3_unique`.

**Its role** (for your choice of shape). In Theorem 1, "By Lemmas 7 and 16, each element of the
decomposition of `F(Z)` that intersects `⋃𝒫′` is an element of the decomposition of the closure of
a component of `⋃𝒫′`." With `layers_agree` this needs only that no layer of `F(Z)` contains some
`Cl H`, the degenerate case. A layer containing `Cl H` meets all five links, so Lemma 16 excludes
it. If the printed proof resists, prove that weaker statement instead, and say so.

## 6. Last, if time remains: Jones 1975 (reconnaissance only)

`NoArcIndecHomPlane` (Bing 1960) will come from Jones 1975, which uses Effros to shorten Bing's
proof. Transcribe it into `doc/notes/jones75.md` from page images at 200 dpi or more. Map its
properties (a)–(e) and lemmas to the repository:
* the Effros corollary is `effros_homogeneous`;
* (a) and (b) are `hagopian75_lemma1`;
* list the plane topology each step needs, and what the repository has.

Propose a skeleton for a later batch. Do not formalize.

## 7. Order

1. §2. It is independent and short.
2. §3.1 steps 1–3, then the fold (step 4), then steps 5–6, then §3.2.
3. §4.1, §4.2, §4.3, §4.4.
4. §5.
5. §6.

## 8. Places to check (candidate ledger entries)

1. **Lemma 13 (5)** printed without `h` (p. 340). The fold reduction "By (1), (2), and (3), there
   exist …" is unargued, and the mirror case is not mentioned.
2. **Lemma 13**: "Note that `𝔏` is a normal chain in `M∖A`"; the positions of `r` and `s` in (3);
   the regularity sentence; the last paragraph.
3. **Lemma 12**: its three unargued steps, and freeness.
4. **Lemmas 14–15**: positivity of `½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`. Also whether Lemma 3 suffices in Lemma 15
   as printed (§4.3).
5. **Lemma 16**: "Since `𝒫` is free, there exist …".
6. **p. 344**: the arc; and the chain of points `vᵢ`, replaced by the orbit argument (harmless).

## 9. Deliverables

1. **The items of §2–§5.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch186.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report, each with its non-vacuity note.
2. **`LEDGER.md`:** a subsection "Hagopian 1984 III (batch 186)" in the Hagopian 1984 section, with
   the printed sentences quoted.
3. **Notes:** `doc/notes/hagopian84.md` (the package, the chain, the fold, Lemmas 14–16); and
   `doc/notes/jones75.md` if §6 is reached.
4. **Publish the changes, as in batch 185.** At the end of the run:
   * create `doc/batches/batch186-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch186-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `Hagopian84Decomp` (the 1984 route), and the open items of the 1976
     route as of batch 185, unchanged;
   * a skeleton proposal for the next step (the construction of pp. 343–344 and the assembly
     `hagopian84_decomp`).
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`.
   * Nothing is left at the root.
