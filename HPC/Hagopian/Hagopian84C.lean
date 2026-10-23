import HPC.Hagopian.H84Cover
import HPC.Hagopian.H84Lemma13

/-!
# Batch 187: Hagopian 1984 IV — Lemma 13 (chain part); Lemma 16′; the bridge `J(Z)`; `𝒫(Z)`

Built from the commission-187 skeleton (`doc/batches/skeletons/Hagopian84C.lean`). There is no
`sorry` in this file or its imports. Every item of the skeleton is proved; the steps after the cover
and the printed `⋃𝔅 = M` are proved in batch 188 (`Hagopian84D.lean`; `OPEN.md`, batch 188).

Source: Hagopian 1984 (`doc/sources/hagopian1984.pdf`), pp. 339–343. Route: commission 187.
Indexing as in `Hagopian84B.lean`: links `P 0, …, P 4` (the paper's `P₁, …, P₅`), `P 2` is the
paper's `P₃`, `midUnion P = ⋃𝒫′`. A *strand* is the closure of a component of `midUnion P`.

The proofs are in `H84Chain13.lean` (§2, the chain part), `H84Strand.lean` (§3),
`H84Bridge.lean` (§4, §5.1) and `H84Cover.lean` (§5.2).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §2. Lemma 13

Proved: the chain part (`chainLinks84_chain`), conditions (3)–(6) of "runs straight"
(`chainLinks84_runsStraight`), regularity (`chainLinks84_regular`) and Lemma 13 itself
(`hagopian84_lemma13`), in the batch-186 shapes. -/

section Lemma13

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- **§2, Lemma 13, the chain part** (p. 339: "Note that `𝔏` is a normal chain in `M∖A`", unargued;
ledger H84.18). There are numbers `x₀ = 0 < x₁ < ⋯ < x₁₅ = 1` (with `k⁻¹[[0, x₃]]` and
`k⁻¹[[x₁₂, 1]]` inside `B`, commission 187 §2.4) such that for every small enough `δ > 0` the links
`L i = W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)` form a normal chain in `M ∖ A` with `Cl(L 0 ∪ L 4) ⊆ B`, and every
`δ`-homeomorphism `h` satisfies conditions (1) and (2) of "runs straight" for `h[E]`, in the closure
form of `chainLinks84_runsStraight` (`h[k⁻¹(0)] ⊆ L 0 ∖ Cl L 1`, `h[k⁻¹(1)] ⊆ L 4 ∖ Cl L 3`).

*Proof* (`exists_x84`, `chainLinks84_chain_aux`): `W(S, δ)` lies in the `δ`-thickening of `S`;
segments of non-adjacent links, and the end layers against the segments of `L 1` and `L 3`, are
disjoint compact sets, hence a positive distance apart; `δ₀` is the least of these radii and of
those for `A` and `B`. -/
theorem chainLinks84_chain (hX : IsHomogeneous M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {A B : Set M} (hA : IsClosed A) (hAE : Disjoint A E)
    (hB : IsOpen B) (hBE : layer k 0 ∪ layer k 1 ⊆ B) :
    ∃ x : Fin 16 → unitInterval, StrictMono x ∧ x 0 = 0 ∧ x 15 = 1 ∧ ∃ δ₀ > 0, ∀ δ, 0 < δ →
      δ ≤ δ₀ → IsChain5 (chainLinks84 k x δ) ∧ IsNormal5 (chainLinks84 k x δ) ∧
      (⋃ i, chainLinks84 k x δ i) ⊆ Aᶜ ∧
      closure (chainLinks84 k x δ 0 ∪ chainLinks84 k x δ 4) ⊆ B ∧
      ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
        h '' E ⊆ ⋃ i, chainLinks84 k x δ i ∧
        h '' layer k 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) ∧
        h '' layer k 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3) := by
  obtain ⟨x, hx, hx0, hx15, hxB⟩ := exists_x84 hE hB hBE
  exact ⟨x, hx, hx0, hx15, chainLinks84_chain_aux hX hE hA hAE hB hx hx0 hx15 hxB⟩

/-- **§2, Lemma 13, steps (1)–(6)** (pp. 339–340; batch-186 shape, unchanged). There are numbers
`x₀ = 0 < ⋯ < x₁₅ = 1` and `0 < δ < ε` such that the links `L i = W(k⁻¹[[x₃ᵢ, x₃ᵢ₊₃]], δ)` form a
normal chain in `M ∖ A` with `Cl(L 0 ∪ L 4) ⊆ B`, and every `δ`-translate of `E` runs straight
through them with its end layers in `L 0 ∖ Cl L 1` and `L 4 ∖ Cl L 3`.

*Proof* (`chainLinks84_runsStraight_aux`, `H84Runs13.lean`): `δ` also below half of the fifteen gap
radii `ρ(k⁻¹[[0, xⱼ]], k⁻¹[[xⱼ₊₁, 1]])` (`exists_gap84`). (3), `link_dichotomy84`: a point
`h(z) = g(w)` gives `dist(z, w) < 2δ`, the gap bounds put both parameters in `[x₁, x₁₄]`, and Lemma 3
for `h⁻¹ ∘ g` gives `h[k⁻¹(r)] = g[k⁻¹(s)] ⊆ L i` (commission 187 §2.1, no uniform continuity). (4),
`layer_frontier84`: Effros with the room `δ − max dist(v, h v)` (§2.2). (5), `layer_convex84`: a
non-interval among the parameter sets gives a fold (`exists_fold`), and `no_fold84` excludes kinds D
and U (§2.3): the continuum `g[k⁻¹[[0, x₃ₚ₊₃]]]` (resp. `g[k⁻¹[[x₃ₚ, 1]]]`) lies in
`h[k⁻¹[[r, t]]]` by atriodicity, and then the gap bound `j = 0` (resp. `j = 14`) puts `r` (resp.
`t`) in the end segment, which forces `p = 0` (resp. `p = 4`). -/
theorem chainLinks84_runsStraight (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε)
    {A B : Set M} (hA : IsClosed A) (hAE : Disjoint A E) (hB : IsOpen B)
    (hBE : layer k 0 ∪ layer k 1 ⊆ B) :
    ∃ (x : Fin 16 → unitInterval) (δ : ℝ), 0 < δ ∧ δ < ε ∧ StrictMono x ∧ x 0 = 0 ∧ x 15 = 1 ∧
      IsChain5 (chainLinks84 k x δ) ∧ IsNormal5 (chainLinks84 k x δ) ∧
      (⋃ i, chainLinks84 k x δ i) ⊆ Aᶜ ∧
      closure (chainLinks84 k x δ 0 ∪ chainLinks84 k x δ 4) ⊆ B ∧
      ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∃ g : (h '' E) → unitInterval,
        IsMinimalAdmissible (h '' E) g ∧ RunsStraight g (chainLinks84 k x δ) ∧
        layer g 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) ∧
        layer g 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3) :=
  chainLinks84_runsStraight_aux hX hi hE hε hA hAE hB hBE

/-- **§2, Lemma 13, regularity** (p. 340: "Let `K` be a component of `⋃𝔏′`. Let `h` be a
`δ`-homeomorphism of `M` onto `M` such that `K ∩ h[E] ≠ ∅`. Since `M` is atriodic, it follows from
(6) and Lemma 6 that `Cl K` is an essential subcontinuum of `h[E]` that runs straight through
`𝔏`. Hence `𝔏` is regular.").

*Shape* (batch 186: "for `x`, `δ` as in `chainLinks84_runsStraight`"): the hypothesis `hrs` is the
last clause of `chainLinks84_runsStraight`. *Proof* (`chainLinks84_regular_aux`,
`strand_of_runsStraight84`): a point of `⋃𝔏′` is `h(v)` with `v ∈ E` (definition of `W`); `Cl K ⊆ h[E]`
by atriodicity; the parameter sets of the links are intervals, so `Cl K = h[E]`'s layers over
`[a, c]` with `b⁻¹(a) ⊆ L 0 ∖ L 1` and `b⁻¹(c) ⊆ L 4 ∖ L 3`; two consecutive parameter sets meet
(`params_adjacent_meet84`), which fixes the orientation. -/
theorem chainLinks84_regular (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} {x : Fin 16 → unitInterval} {δ : ℝ}
    (hch : IsChain5 (chainLinks84 k x δ)) (hn : IsNormal5 (chainLinks84 k x δ))
    (hrs : ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) → ∃ g : (h '' E) → unitInterval,
        IsMinimalAdmissible (h '' E) g ∧ RunsStraight g (chainLinks84 k x δ) ∧
        layer g 0 ⊆ chainLinks84 k x δ 0 \ closure (chainLinks84 k x δ 1) ∧
        layer g 1 ⊆ chainLinks84 k x δ 4 \ closure (chainLinks84 k x δ 3)) :
    IsRegular5 (chainLinks84 k x δ) ∧ ∀ y ∈ midUnion (chainLinks84 k x δ),
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) ∧ ∃ g : (h '' E) → unitInterval,
        IsMinimalAdmissible (h '' E) g ∧
        IsEssential84 g (closure (connectedComponentIn (midUnion (chainLinks84 k x δ)) y)) :=
  chainLinks84_regular_aux hX hi hch hn hrs

/-- **Lemma 13** (p. 339): "Suppose `ε` is a positive number, `A` is a closed set that misses `E`,
and `B` is an open set that contains `k⁻¹(0) ∪ k⁻¹(1)`. Then `E` runs straight through a free normal
regular chain `𝒫 = {Pᵢ : 1 ≤ i ≤ 5}` in `M∖A` with the property that `B` contains `Cl(P₁ ∪ P₅)` and
for each component `K` of `⋃𝒫′` there is an `ε`-homeomorphism `h` of `M` onto `M` such that `Cl K`
is an essential subcontinuum of `h[E]`." (Batch-186 shape, unchanged.)

*Proof* (`hagopian84_lemma13_aux`), as printed: `chainLinks84_runsStraight`,
`chainLinks84_regular`, the identity in (6) (so `E` runs straight through `𝔏`), Lemma 12
(`hagopian84_lemma12`), whose added clause makes each component of `⋃𝒫′` a component of `⋃𝔏′`. -/
theorem hagopian84_lemma13 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) {A B : Set M}
    (hA : IsClosed A) (hAE : Disjoint A E) (hB : IsOpen B) (hBE : layer k 0 ∪ layer k 1 ⊆ B) :
    ∃ P, IsChain5 P ∧ IsFree5 P ∧ IsNormal5 P ∧ IsRegular5 P ∧ RunsStraight k P ∧
      (⋃ i, P i) ⊆ Aᶜ ∧ closure (P 0 ∪ P 4) ⊆ B ∧
      ∀ x ∈ midUnion P, ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε) ∧
        ∃ g : (h '' E) → unitInterval, IsMinimalAdmissible (h '' E) g ∧
          IsEssential84 g (closure (connectedComponentIn (midUnion P) x)) :=
  hagopian84_lemma13_aux hX hi hE hε hA hAE hB hBE

end Lemma13

/-! ## §3. Lemma 16′ -/

section Lemma16

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§3.2, identification**: for `x ∈ ⋃𝒫∖Cl(P 0 ∪ P 4)`, the layer through `x` of the strand
through `x` is a member of `Δ(𝒫)` (hence the member containing `x`).

*Shape change:* `hn` (normality) is dropped (not used). *Proof* (`strand_layer_mem_delta_aux`): the
layer is a layer of the map given by regularity, which runs straight, so it misses `Cl P 0` and
`Cl P 4` (`layer_disjoint_closure_of_mem`). -/
theorem strand_layer_mem_delta {P : Fin 5 → Set M} (hP : IsChain5 P) (hr : IsRegular5 P) {x : M}
    (hx : x ∈ midUnion P) (hx0 : x ∉ closure (P 0 ∪ P 4))
    {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c)
    {t : unitInterval} (hxt : x ∈ layer c t) : layer c t ∈ Delta5 P :=
  strand_layer_mem_delta_aux hP hr hx hx0 hc hxt

/-- **§3.4, the degenerate alternative is impossible**: if `(F, d)` is type λ and its end layer
`d⁻¹(0)` misses `midUnion P`, no layer of `F` contains a strand.

*Proof* (`not_strand_subset_extension_layer_aux`): commission 187 §3.4, with the simplification that
step 3 uses a single limit point `z ∈ d⁻¹(α) ∩ Cl P 2` (closedness of the set of parameters whose
layer meets `Cl P 2`) instead of the Hausdorff limit of the `Zₙ`; Lemma 14 is not needed. -/
theorem not_strand_subset_extension_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {F : Set M} {d : F → unitInterval} (hd : IsMinimalAdmissible F d)
    (hd0 : Disjoint (layer d 0) (midUnion P)) {y : M} (hy : y ∈ midUnion P) (u : unitInterval) :
    ¬ closure (connectedComponentIn (midUnion P) y) ⊆ layer d u :=
  not_strand_subset_extension_layer_aux hX hi hP hn hf hr hd hd0 hy u

/-- **§3.1, Lemma 16′** (p. 343: "By Lemmas 7 and 16, each element of the decomposition of `F(Z)`
that intersects `⋃𝒫′` is an element of the decomposition of the closure of a component of
`⋃𝒫′`"), for any type λ `F` whose end layer `d⁻¹(0)` misses `midUnion P`.

*Proof* (`strand_layer_of_extension_aux`): the dichotomy of §3.3 (`strand_dichotomy`, from
`layers_agree` and `no_arm_at_interior_layer`), whose degenerate case is excluded by
`not_strand_subset_extension_layer`. -/
theorem strand_layer_of_extension (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {F : Set M} {d : F → unitInterval} (hd : IsMinimalAdmissible F d)
    (hd0 : Disjoint (layer d 0) (midUnion P)) {u : unitInterval} {y : M} (hy : y ∈ layer d u)
    (hym : y ∈ midUnion P) :
    ∃ c' : closure (connectedComponentIn (midUnion P) y) → unitInterval,
      IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) y)) c' ∧
        ∃ t, layer d u = layer c' t := by
  obtain ⟨c', hc', -, ht⟩ := strand_layer_of_extension_aux hX hi hP hn hf hr hd hd0 hy hym
  exact ⟨c', hc', ht⟩

/-- **Lemma 16 as printed** (pp. 341–342): "Suppose `𝒫` is a free regular chain. Suppose `K` is a
component of `⋃𝒫′` and `X` is an end set of `Cl K`. Suppose `F` is an extension of `Cl K` away from
`X` and `𝔇` is the decomposition of `F`. Then no element of `𝔇` intersects three consecutive links
of `𝒫`" (moved here from the commented-out block of `Hagopian84B.lean`).

*Shape change:* normality `hn` is added (Lemma 16′ uses it; the chain of Lemma 13 is normal), and
the hypothesis `Cl K ⊆ F` is dropped (not used). *Proof* (`hagopian84_lemma16_aux`, commission 187
§3.5): `d⁻¹(0) = c⁻¹(0)` is an end layer of the strand, so it misses `midUnion P`
(`strand_end_layer_not_mid`); a layer meeting `P i`, `P (i + 1)`, `P (i + 2)` meets `midUnion P`
(through `P (i + 1)`), so by Lemma 16′ it is a layer of a strand running straight through `𝒫`, and
then it lies in both `P i` and `P (i + 2)`, which are disjoint. Hagopian's subchain `𝔔` and his
step (1) are not needed. -/
theorem hagopian84_lemma16 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {x : M} (hx : x ∈ midUnion P)
    {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c) {F : Set M}
    {d : F → unitInterval} (hd : IsMinimalAdmissible F d) (hd0 : layer d 0 = layer c 0)
    (t : unitInterval) (i : ℕ) (hi3 : i + 2 < 5) :
    ¬ ((layer d t ∩ P ⟨i, by omega⟩).Nonempty ∧ (layer d t ∩ P ⟨i + 1, by omega⟩).Nonempty ∧
      (layer d t ∩ P ⟨i + 2, hi3⟩).Nonempty) :=
  hagopian84_lemma16_aux hX hi hP hn hf hr hx hc hd hd0 t i hi3

end Lemma16

/-! ## §4. The bridge `J(Z)` (p. 343) -/

section Bridge

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§4.2**: a member of `Ω(𝒫)∖Δ(𝒫)` lies in `Cl (P 0)` or in `Cl (P 4)`, and misses `Cl (P 2)`.

*Shape* (skeleton: `True`): `𝒫` a normal regular chain, `Z ∈ Ω(𝒫) ∖ Δ(𝒫)`. *Proof*
(`omega_not_delta_side_aux`): `Z` is a layer of the map given by regularity; it meets `Cl P 0` or
`Cl P 4`, and a layer meeting `Cl P i` lies in it (`layer_subset_closure_link`); normality. -/
theorem omega_not_delta_side {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hr : IsRegular5 P) {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) :
    (Z ⊆ closure (P 0) ∨ Z ⊆ closure (P 4)) ∧ Disjoint Z (closure (P 2)) :=
  omega_not_delta_side_aux hP hn hr hZ hZd

/-- **§4.4, the bridge** (p. 343, "Hence there is an essential subcontinuum `J(Z)` of `F(Z)` that
contains `Z`, misses `Cl P₃`, and has one end set in `K(Z) ∩ (⋃Δ(𝒫))` and the other end set in
`(⋃Δ(𝒫))∖K(Z)`"). The optional clause "the two end layers lie in different components" is not
added (see `exists_bridge84_aux` and the report §4).

*Proof* (`exists_bridge84_aux`): `bridge_setup` (§4.1–§4.2), `exists_ext_meeting_P2` (§4.3), then
§4.4 with `m₂` the largest parameter `≤ z₀` and `u*` the least parameter `≥ z₀` whose layer meets
`Cl P 2`, and `a`, `b` next to them inside the open set of parameters whose layer lies in
`midUnion P` and misses `Cl(P 0 ∪ P 4)`; Lemma 16′ makes those layers members of `Δ(𝒫)`. -/
theorem exists_bridge84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) :
    ∃ (J : Set M) (j : J → unitInterval), IsMinimalAdmissible J j ∧ (∃ t, Z = layer j t) ∧
      Disjoint J (closure (P 2)) ∧ layer j 0 ∈ Delta5 P ∧ layer j 1 ∈ Delta5 P ∧
      ∀ u, (layer j u ∩ midUnion P).Nonempty → ∃ y ∈ midUnion P,
        ∃ c' : closure (connectedComponentIn (midUnion P) y) → unitInterval,
          IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) y)) c' ∧
            ∃ t, layer j u = layer c' t :=
  exists_bridge84_aux hX hi hP hn hf hr hZ hZd

end Bridge

/-! ## §5. `𝒫(Z)` and the cover

Proved: **§5.1, `𝒫(Z)`** (`exists_chainZ84`, through Lemma 13 and the check `Z ∈ Δ(𝒫(Z))`,
`mem_delta_of_bridge_chain`); **§5.2, the finite cover** (`hagopian84_cover`, through
`exists_finite_cover84`). The printed closedness of `⋃𝔅` is not used here; its statement is
proved in batch 188 as a corollary of the finite cover (`sUnion_cover84_eq_univ` in
`Hagopian84D.lean`: `⋃𝔅 = M`); only the printed reason (freeness and (3)) is unargued (ledger
H84.29). -/

section ChainZ

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§5.1, `Z ∈ Δ(𝒫(Z))`** (commission 187 §5.1). Let `(J, j)` be a bridge of `Z ∈ Ω(𝒫) ∖ Δ(𝒫)`
(`Z` a layer of `J`) and `Q` a free normal regular chain through which `J` runs straight, with
`Cl(Q 0 ∪ Q 4) ⊆ ⋃Δ(𝒫)` (Hagopian's (3); Lemma 13 with `A = Cl P 2`, `B = ⋃Δ(𝒫)` would give such a
`Q`). Then `Z ∈ Δ(Q)`.

*Shape* (skeleton: prose only). *Proof* (`mem_delta_of_bridge_chain_aux`): `Z` lies in `Cl P 0` or
`Cl P 4` (`omega_not_delta_side`), so it misses `⋃Δ(𝒫) ⊇ Cl(Q 0 ∪ Q 4)` and lies in `midUnion Q`;
`j⁻¹(0)` misses `midUnion Q`; Lemma 16′ for `Q` makes `Z` a layer of a strand of `Q`. -/
theorem mem_delta_of_bridge_chain (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P Q : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P)
    (hQ : IsChain5 Q) (hQn : IsNormal5 Q) (hQf : IsFree5 Q) (hQr : IsRegular5 Q)
    {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) {J : Set M} {j : J → unitInterval}
    (hj : IsMinimalAdmissible J j) {t : unitInterval} (hZt : Z = layer j t)
    (hjs : RunsStraight j Q) (hB : closure (Q 0 ∪ Q 4) ⊆ ⋃₀ Delta5 P) : Z ∈ Delta5 Q :=
  mem_delta_of_bridge_chain_aux hX hi hP hn hr hQ hQn hQf hQr hZ hZd hj hZt hjs hB

open Classical in
/-- **§5.2, the cover, finite form** (p. 343: "it follows that `⋃𝔅` is a closed open subset of `M`.
Hence `𝔅` covers `M`", and "there exists a finite subcollection … of `𝔅` that covers `M`"). For a
free normal regular chain `𝒫` and any choice `Z ↦ Q Z` (for `Z ∈ Ω(𝒫) ∖ Δ(𝒫)`) of free regular
chains with `Z ∈ Δ(Q Z)` (`mem_delta_of_bridge_chain`) and Hagopian's (3), finitely many `Zᵢ` give
`M = ⋃Δ(𝒫) ∪ ⋃ᵢ ⋃Δ(Q Zᵢ)`.

*Proof* (`exists_finite_cover84_aux`): not through the closedness of the union of the whole family.
`C = Cl ⋃Δ(𝒫) ∖ ⋃Δ(𝒫)` is compact; each point of `C` lies in `⋃𝒫′ ∩ Cl(P 0 ∪ P 4)`, so the layer
`Z` through it of its strand is in `Ω(𝒫) ∖ Δ(𝒫)` and the point lies in `⋃Δ(Q Z)`; finitely many of
these open sets cover `C`; the union `U` of `⋃Δ(𝒫)` with them is open, and closed because
`Cl ⋃Δ(Q Z) ⊆ ⋃Δ(Q Z) ∪ Cl(Q Z 0 ∪ Q Z 4)` (freeness) and (3); `M` is connected. -/
theorem exists_finite_cover84 {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hf : IsFree5 P) (hr : IsRegular5 P) (Q : Set M → Fin 5 → Set M)
    (hQ : ∀ Z ∈ Omega5 P, Z ∉ Delta5 P → IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧ IsRegular5 (Q Z) ∧
      Z ∈ Delta5 (Q Z) ∧ closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P) :
    ∃ S : Finset (Set M), (∀ Z ∈ S, Z ∈ Omega5 P ∧ Z ∉ Delta5 P) ∧
      ∀ y : M, y ∈ ⋃₀ Delta5 P ∨ ∃ Z ∈ S, y ∈ ⋃₀ Delta5 (Q Z) :=
  exists_finite_cover84_aux hP hn hf hr Q hQ

/-- **§5.1, the chain `𝒫(Z)`** (p. 343: "By Lemma 13, `J(Z)` runs straight through a free normal
regular chain `𝒫(Z) = {Pᵢ(Z) : 1 ≤ i ≤ 5}` in `M∖Cl P₃` such that `⋃Δ(𝒫)` contains
`Cl(P₁(Z) ∪ P₅(Z))`"; "(The sets `A` and `B` in Lemma 13 are `Cl P₃` and `⋃Δ(𝒫)`,
respectively.)"), together with the check `Z ∈ Δ(𝒫(Z))` of commission 187 §5.1.

*Proof*: the bridge `J(Z)` (`exists_bridge84`) misses `Cl P 2` and has both end layers in `Δ(𝒫)`,
so Lemma 13 (`hagopian84_lemma13`) applies with `A = Cl P 2`, `B = ⋃Δ(𝒫)` (open,
`isOpen_sUnion_delta5`); then `mem_delta_of_bridge_chain`. -/
theorem exists_chainZ84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) :
    ∃ Q : Fin 5 → Set M, IsChain5 Q ∧ IsFree5 Q ∧ IsNormal5 Q ∧ IsRegular5 Q ∧ Z ∈ Delta5 Q ∧
      (⋃ i, Q i) ⊆ (closure (P 2))ᶜ ∧ closure (Q 0 ∪ Q 4) ⊆ ⋃₀ Delta5 P ∧
      ∃ (J : Set M) (j : J → unitInterval), IsMinimalAdmissible J j ∧ (∃ t, Z = layer j t) ∧
        RunsStraight j Q := by
  obtain ⟨J, j, hj, ⟨t, hZt⟩, hJd, hj0, hj1, -⟩ := exists_bridge84 hX hi hP hn hf hr hZ hZd
  obtain ⟨Q, hQc, hQf, hQn, hQr, hQrs, hQA, hQB, -⟩ := hagopian84_lemma13 hX hi hj one_pos
    isClosed_closure hJd.symm (isOpen_sUnion_delta5 hP hr)
    (union_subset (subset_sUnion_of_mem hj0) (subset_sUnion_of_mem hj1))
  exact ⟨Q, hQc, hQf, hQn, hQr,
    mem_delta_of_bridge_chain hX hi hP hn hr hQc hQn hQf hQr hZ hZd hj hZt hQrs hQB, hQA, hQB,
    J, j, hj, ⟨t, hZt⟩, hQrs⟩

open Classical in
/-- **§5.2, the finite cover, unconditional** (p. 343: "there exists a finite subcollection
`{⋃Δ(𝒫)} ∪ {⋃Δ(𝒫(Zᵢ)): 1 ≤ i ≤ n}` of `𝔅` that covers `M`"). For a free normal regular chain `𝒫`
there are finitely many `Zᵢ ∈ Ω(𝒫) ∖ Δ(𝒫)` and chains `𝒫(Zᵢ)` as in `exists_chainZ84` with
`M = ⋃Δ(𝒫) ∪ ⋃ᵢ ⋃Δ(𝒫(Zᵢ))`.

*Proof*: `exists_finite_cover84` with `𝒫(Z)` chosen by `exists_chainZ84`. The closedness of `⋃𝔅` for
the whole (uncountable) family, as printed, is not used. -/
theorem hagopian84_cover (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P)
    (hr : IsRegular5 P) :
    ∃ (S : Finset (Set M)) (Q : Set M → Fin 5 → Set M), (∀ Z ∈ S, Z ∈ Omega5 P ∧ Z ∉ Delta5 P ∧
      IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧ IsNormal5 (Q Z) ∧ IsRegular5 (Q Z) ∧ Z ∈ Delta5 (Q Z) ∧
      (⋃ i, Q Z i) ⊆ (closure (P 2))ᶜ ∧ closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P) ∧
      ∀ y : M, y ∈ ⋃₀ Delta5 P ∨ ∃ Z ∈ S, y ∈ ⋃₀ Delta5 (Q Z) := by
  set Q : Set M → Fin 5 → Set M := fun Z =>
    if h : Z ∈ Omega5 P ∧ Z ∉ Delta5 P then
      Classical.choose (exists_chainZ84 hX hi hP hn hf hr h.1 h.2) else fun _ => ∅ with hQdef
  have hQspec : ∀ Z (h : Z ∈ Omega5 P ∧ Z ∉ Delta5 P), Q Z =
      Classical.choose (exists_chainZ84 hX hi hP hn hf hr h.1 h.2) := fun Z h => by
    simp only [hQdef, dif_pos h]
  have hQ : ∀ Z ∈ Omega5 P, Z ∉ Delta5 P → IsChain5 (Q Z) ∧ IsFree5 (Q Z) ∧ IsNormal5 (Q Z) ∧
      IsRegular5 (Q Z) ∧ Z ∈ Delta5 (Q Z) ∧ (⋃ i, Q Z i) ⊆ (closure (P 2))ᶜ ∧
      closure (Q Z 0 ∪ Q Z 4) ⊆ ⋃₀ Delta5 P := by
    intro Z hZ hZd
    rw [hQspec Z ⟨hZ, hZd⟩]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ :=
      Classical.choose_spec (exists_chainZ84 hX hi hP hn hf hr hZ hZd)
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨S, hS, hcov⟩ := exists_finite_cover84 hP hn hf hr Q (fun Z hZ hZd => by
    obtain ⟨h1, h2, -, h4, h5, -, h7⟩ := hQ Z hZ hZd
    exact ⟨h1, h2, h4, h5, h7⟩)
  exact ⟨S, Q, fun Z hZ => ⟨(hS Z hZ).1, (hS Z hZ).2, hQ Z (hS Z hZ).1 (hS Z hZ).2⟩, hcov⟩

end ChainZ

end HPC.Hagopian
