import HPC.Hagopian.H76Prop1
import HPC.Hagopian.H76T9
import HPC.Hagopian.H76Lemma7
import HPC.Hagopian.H76Prop3

/-!
# Batch 161 skeleton: Hagopian 1976, Theorem 1 set-up (T4–T9, T11, T14: `ε₁`, the chain of
# elevenths, Property 1, Property 3); Lemma 7; Lemma 9

Batch 161 (`doc/batches/COMMISSION-batch161.md`; report `doc/batches/REPORT-batch161.md`). The
skeleton as uploaded is kept as `doc/batches/skeletons/Hagopian76F.lean`. Supporting proofs:

* `H76Eps1.lean` (T4): `piece` (moved there from this file, unchanged), `middle`, `IsEps1`,
  `exists_isEps1`, `isEps1_thickening_disjoint`;
* `H76Lemma8Sep.lean` (T5): `lemma8_caps_sep`, Lemma 8 with caps exposing Moore's open sets `C`, `D`;
* `H76Prop1.lean` (T5): `Wset` (moved there from this file, unchanged), `Gset`, `toPt_Wset_eq`,
  `follows_of_elev`, `chainG`, `chainG_isPlaneChain`, `chainG_follows`, `thickChain_follows`,
  `property1_aux`;
* `H76T9.lean` (T9): `T9_aux`;
* `H76Prop3.lean` (T14, Property 3): `layer_shift`, the step "By Lemmas 2 and 3";
* `H76Lemma7.lean` (Lemma 7): `lemma7_triod`, `Lemma7F`, `lemma7_of_F`,
  `exists_F_of_not_mem_composant`, `lemma7_of_F_composant`.

Shape changes are recorded at each statement and in the report (§1). Items that remain open are
commented out (no `sorry`), each with an `OPEN (batch 161)` note; obstructions in `OPEN.md`.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 343–347.

Indices: Hagopian's elevenths, links `Gᵢ`, `Lᵢ` (`1 ≤ i ≤ 11`) are `piece k i`, `chainG k ε₁ (i − 1)`,
`L (i − 1)` here (chains are indexed by `Fin 11`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## T4: `ε₁` -/

omit [CompactSpace M] [ConnectedSpace M] in
/-- **T4, `ε₁`** (pp. 345–346). *Shape change:* the conclusion also returns `IsEps1 k ε₁`, which
records the two families of the minimum used later — non-adjacent elevenths `4ε₁` apart (the
skeleton's family, not among Hagopian's four) and `ρ(k⁻¹(0) ∪ k⁻¹(1), k⁻¹[[1/11, 10/11]]) ≥ 3ε₁`
(Hagopian's third family; Property 1 needs it for the caps). The hypotheses `hX`, `hi` of the
skeleton are dropped (unused). The families with `Aᵢ`, `qᵢ` are not used by any step proved here. -/
theorem hagopian76_eps1 {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ ε₁ > 0, IsEps1 k ε₁ ∧ ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) →
      ∀ i ∈ Finset.Icc 1 11, ∀ j ∈ Finset.Icc 1 11, i + 1 < j →
        Disjoint (Metric.thickening ε₁ (toPt (h '' piece k i)))
                 (Metric.thickening ε₁ (toPt (h '' piece k j))) := by
  obtain ⟨ε₁, he⟩ := exists_isEps1 hE
  exact ⟨ε₁, he.pos, he, fun h hh i _ j hj hij =>
    isEps1_thickening_disjoint he h hh hij (Finset.mem_Icc.1 hj).2⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Ledger check 161.2** (p. 346): "if `h` is an `ε₁`-homeomorphism of `M` onto `M`, then the
chain formed by taking `ε₁`-neighborhoods in `R²` of the elements of
`{k⁻¹[[(i − 1)/11, i/11]] : 1 ≤ i ≤ 11}` follows `h[E]`" — true for `ε₁` with `IsEps1` (it needs the
family `IsEps1.sep`, which Hagopian's four families do not provide). `h[E]` carries the transported
map `b` (`exists_image_map`). -/
theorem hagopian76_eps1_chain {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {ε₁ : ℝ} (he : IsEps1 k ε₁) (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε₁)
    {b : (h '' E) → unitInterval} (hbE : IsMinimalAdmissible (h '' E) b)
    (hb : ∀ S, layerSet b S = h '' layerSet k S) :
    IsPlaneChain (thickChain k ε₁) ∧ Follows (thickChain k ε₁) b :=
  thickChain_follows hE he h hh hbE hb

/-! ## T5: `Wₓ`, `Gₓ`, the chain `{Gᵢ}`, `L`, Property 1 -/

omit [ConnectedSpace M] in
/-- **T5, `Gₓ`** (p. 346): "an open set in `{z ∈ R² : ρ(x, z) < ε₁}` such that `Wₓ = M ∩ Gₓ`".
Shape: the skeleton's, unchanged (`Wset` is in `H76Prop1.lean`; the canonical choice is `Gset`). -/
theorem exists_Gset (hX : IsHomogeneous M) {ε : ℝ} (hε : 0 < ε) (x : M) :
    ∃ G : Set Pt, IsOpen G ∧ G ⊆ Metric.ball (x : Pt) ε ∧ toPt (Wset M ε x) = M ∩ G :=
  exists_Gset_aux hX hε x

omit [ConnectedSpace M] in
/-- **T5, the chain `{Gᵢ}`** (p. 346): "For each `i` (`1 ≤ i ≤ 11`), let
`Gᵢ = ⋃{Gₓ : x ∈ k⁻¹[[(i − 1)/11, i/11]]}`" (`chainG`, 0-indexed). It is a chain, its links lie in
the `ε₁`-neighbourhoods of the elevenths, and it follows `h[E]` for every `ε₁`-homeomorphism `h`
(in particular it follows `E`). New statement (the skeleton folded it into Property 1). The links are
not collar rectangles; no later step proved here needs them to be. -/
theorem hagopian76_chain11 (hX : IsHomogeneous M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁) :
    IsPlaneChain (chainG k ε₁) ∧ Follows (chainG k ε₁) k ∧
      (∀ i : Fin 11, chainG k ε₁ i ⊆ thickening ε₁ (toPt (piece k ((i : ℕ) + 1)))) ∧
      ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) → ∀ b : (h '' E) → unitInterval,
        IsMinimalAdmissible (h '' E) b → (∀ S, layerSet b S = h '' layerSet k S) →
          Follows (chainG k ε₁) b :=
  ⟨chainG_isPlaneChain hX hE.2.1.2.1 he, chainG_follows_self hX hE he,
    chainG_subset_thickening k ε₁, fun h hh _ hbE hb => chainG_follows hX hE he h hh hbE hb⟩

/-- **T5, the refinement `L`, and Property 1** (p. 346). "Using the method described in the proof
of Lemma 8, we define an ordered refinement `L = {Lᵢ : 1 ≤ i ≤ 11}` of the chain
`{Gᵢ : 1 ≤ i ≤ 11}` that follows `E` and is free relative to `M` having the following property:
PROPERTY 1. For each point `y` of `M ∩ ⋃{Lᵢ : 2 ≤ i ≤ 10}`, there exists an `ε₁`-homeomorphism `h`
of `M` onto `M` such that `y` belongs to `h[E]` and `L` follows `h[E]`. (Here the open sets `A` and
`B` in the proof of Lemma 8 are in `G₁ − G₂` and `G₁₁ − G₁₀` respectively.)"

*Shape (left to the batch):* `L` is the Lemma-8 refinement with caps `U = G₁ − Cl G₂`,
`V = G₁₁ − Cl G₁₀` (so `A ⊆ G₁ − G₂`, `B ⊆ G₁₁ − G₁₀` as in the parenthesis); its shape
(`L₁ = G₁`, `L₁₁ = G₁₁`, `Lᵢ = C ∩ Gᵢ`) is returned. Property 1 is as printed, with `h[E]` carrying the
transported map `b`, and with the stronger conclusion that the `j`-th eleventh of `h[E]` lies in
`Lⱼ` for every `j` (T9 uses it). -/
theorem hagopian76_property1 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁) :
    ∃ (L : Fin 11 → Set Pt) (C : Set Pt), IsOpen C ∧ toPt E ⊆ C ∧
      L 0 = chainG k ε₁ 0 ∧ L (Fin.last 10) = chainG k ε₁ (Fin.last 10) ∧
      (∀ i, i ≠ 0 → i ≠ Fin.last 10 → L i = C ∩ chainG k ε₁ i) ∧
      IsOrderedRefinement L (chainG k ε₁) ∧ Follows L k ∧ IsFree M L ∧
      ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
        ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
          (∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) ∧
          ∃ b : (h '' E) → unitInterval, IsMinimalAdmissible (h '' E) b ∧
            (∀ S, layerSet b S = h '' layerSet k S) ∧ Follows L b :=
  property1_aux hX hi hE he

/-! ## T9 -/

/-- **T9** (p. 346), first sentence. "Suppose `B` is a component of `M ∩ π⁻¹[D]` that intersects
`⋃{Lᵢ : 4 ≤ i ≤ 8}`. Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is the
image of a subcontinuum of `E` (essential to `R(E)`) under an `ε₁`-homeomorphism."

*Shape (left to the batch):* stated for any open `O` of the plane (`π⁻¹[D]`) with the one property
of `D` (T8) that the proof uses — **(D)** every point of `M ∩ Cl O` lies in one of `L₂, …, L₁₀` —
and for any connected `B ⊆ M ∩ O` meeting one of these links (a component meeting
`L₄ ∪ … ∪ L₈` is a special case). `L` is any chain with Property 1 in the form of
`hagopian76_property1`. Conclusion: `Cl B ⊆ h[E]` and `h⁻¹[Cl B]` is a subcontinuum of `E`; it is
essential to `R(E)` whenever `Cl B` meets two links `Lₐ`, `L_c` with `c ≥ a + 3`. Open part: that
`Cl B` does reach such links, and "the chain `L − {L₁, L₁₁}` follows `Cl B`", depend on the
position of `D` in collar coordinates (T6–T8), not formalized. -/
theorem hagopian76_T9 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {O : Set Pt}
    (hO : ∀ x : M, (x : Pt) ∈ closure O → ∃ j : Fin 11, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧ (x : Pt) ∈ L j)
    {B : Set M} (hBc : IsPreconnected B) (hBO : toPt B ⊆ O) {y : M} (hyB : y ∈ B) {i : Fin 11}
    (hi1 : 1 ≤ (i : ℕ)) (hi9 : (i : ℕ) ≤ 9) (hyL : (y : Pt) ∈ L i) :
    ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ closure B ⊆ h '' E ∧
      Fold.Q78.IsContinuum (h ⁻¹' closure B) ∧ h ⁻¹' closure B ⊆ E ∧
      ∀ a c : Fin 11, (a : ℕ) + 3 ≤ c → (toPt (closure B) ∩ L a).Nonempty →
        (toPt (closure B) ∩ L c).Nonempty → IsEssential k (h ⁻¹' closure B) :=
  T9_aux hX hi hE he hLch hLG hP1 hO hBc hBO hyB hi1 hi9 hyL

/-! ## T11 and Property 3 (open) -/

-- `hagopian76_T11`: proved in batch 165, `Hagopian76J.lean` (with `K` replaced by
-- `π⁻¹[D ∩ ⟨p₃, q₃⟩]`).

/- **OPEN (batch 161, Property 3).** p. 347: "No component of `F ∩ π⁻¹[D]` whose closure meets both
`π⁻¹[⟨p₁, r⟩]` and `π⁻¹[⟨p₅, s⟩]` is contained in an element of the decomposition of `F`." Not
formalized. The proof needs (i) that the set of `v` such that `d⁻¹(v)` contains such a component has
a least element ("Let `v` be the first point of `[0, 1]` such that …"; no closedness argument is
given), and (ii) that the image `g[Q]` of such a component `Q ⊆ d⁻¹(v)` under the small
homeomorphism `g` with `gd⁻¹(v) = d⁻¹(u)` (Lemmas 2, 3) again contains, or lies in, a component of
`F ∩ π⁻¹[D]` whose closure meets both verticals. (ii) is a crossing property of `D` in collar
coordinates; the families `ρ(Aᵢ, Bᵢ)`, `ρ(E, π⁻¹(qᵢ))` of `ε₁` are presumably meant for it, but the
argument is not given. The step "By Lemma 1 and Property 1, `L` follows a type A′ continuum in
`d⁻¹(v)` that meets `L₆ ∩ π⁻¹[D]`" is the first sentence of T9 (`hagopian76_T9`) applied to the
closure of the component. The step "By Lemmas 2 and 3, a homeomorphism `g` of `M` onto `M` and a
point `u` of `[0, v)` exist such that `gd⁻¹(v) = d⁻¹(u)`" is proved
(`hagopian76_property3_shift`). -/

/-- **Property 3, the step "By Lemmas 2 and 3"** (p. 347): for a type A′ continuum `F` (map `d`),
an interior layer `d⁻¹(v)` and `δ > 0`, some `u ∈ (0, v)` and some `δ`-homeomorphism `g` have
`g[d⁻¹(v)] = d⁻¹(u)`. New statement (one step of Property 3). -/
theorem hagopian76_property3_shift (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {F : Set M} {d : F → unitInterval} (hF : IsMinimalAdmissible F d) {v : unitInterval}
    (hv0 : 0 < v) (hv1 : v < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : unitInterval, 0 < u ∧ u < v ∧ ∃ g : M ≃ₜ M, (∀ x, dist x (g x) < δ) ∧
      g '' layer d v = layer d u :=
  layer_shift hX hi hF hv0 hv1 hδ

/-! ## Lemma 7 -/

/-- **The triod of Lemma 7** (p. 344: "Note that `g[F] ∪ Hⱼ` is a triod in `M`"), written out: a
continuum through a point of a type A′ continuum `H` outside its end sets, missing a point of each
end set, lies in `H`. (The arms are taken at the layer of the point, so no case analysis on
`g[F] ∩ Hⱼ` is needed.) New statement. -/
theorem hagopian76_lemma7_triod (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {H : Set M} {d : H → unitInterval} (hH : IsMinimalAdmissible H d) {F : Set M}
    (hF : Fold.Q78.IsContinuum F) {u t v : M} (huH : u ∈ H) (hu0 : u ∉ layer d 0)
    (hu1 : u ∉ layer d 1) (huF : u ∈ F) (ht : t ∈ layer d 0) (hv : v ∈ layer d 1) (htF : t ∉ F)
    (hvF : v ∉ F) : F ⊆ H := by
  by_contra hFH
  exact lemma7_triod (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hH hF huH hu0 hu1
    huF ht hv htF hvF hFH

/-- **Lemma 7, reduced to one composant.** Lemma 7 (in the skeleton's shape) holds provided the
continuum `F` of the proof exists when `u`, `t` lie in the same composant of `Cl R(E)`; when they
lie in different composants it exists (`exists_F_of_not_mem_composant`). New statement. -/
theorem hagopian76_lemma7_of_F (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : ∀ p ∈ closure (Rset k), ∀ u ∈ closure (Rset k), ∀ t ∈ closure (Rset k), u ≠ t →
      t ∈ HPC.composant (closure (Rset k)) u → ∀ r > 0,
        ∃ F : Set M, Fold.Q78.IsContinuum F ∧ u ∈ F ∧ t ∉ F ∧ ∃ a ∈ F, dist a p < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε :=
  lemma7_of_F_composant hX hi hE hF hε

-- `hagopian76_lemma7`: proved in batch 162, `Hagopian76G.lean`.

/-! ## Lemma 9 -/

-- `hagopian76_lemma9` (Lemma 9, collar form): proved in batch 163, `Hagopian76H.lean`.

end Thm1

end HPC.Hagopian
