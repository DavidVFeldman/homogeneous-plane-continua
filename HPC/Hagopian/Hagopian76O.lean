import HPC.Hagopian.H76CrossClosed

/-!
# Batch 170: Hagopian 1976, Theorem 1 — `ExtChainInter`; the covering half; "follows" for
# crossing components; Property 3; T15–T17 and the assembly (under `RsetDichotomy` if necessary)

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 170 §1.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76O.lean`.

Supporting files:
* `H76ChainInter` — every member of a family of extensions inside one extension `H` (map `d`) is an
  initial segment `d⁻¹[[0, sᵢ]]`; the intersection is `d⁻¹[[0, inf sᵢ]]`, an extension by
  `piece_map` (`extChainInter_in_aux`); for chains, `ExtChainInter` outright (`extChainInter_aux`);
* `H76Follows` — T9's homeomorphism with Property 1's link condition kept (`T9_pieces_aux`);
  "follows" for crossing components (`follows_crossing_aux`);
* `H76Cover` — the first step of the covering half: components of `O − Z` reach `Fr O` when `Z`
  does not separate the plane (`component_frontier_meets`), in particular for proper subcontinua of
  `M`;
* `H76CrossClosed` — the upper limit of connected sets with a convergent selection is connected
  (`limsup_isPreconnected`); `crossing_set_closed`.

Shapes are recorded at each statement and in `doc/batches/REPORT-batch170.md`. Items left open are
commented out at the end, with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A. `ExtChainInter`, inside one extension** (commission 170 §1.A). The intersection of a
nonempty family of extensions of `E` away from `k⁻¹(0)`, all contained in one extension `H` of `E`
away from `k⁻¹(0)`, is an extension of `E` away from `k⁻¹(0)`.

*Shape (left to me):* no chain condition and no separation hypothesis are needed. *Proof:* the
commission's route. Each member is `d⁻¹[[0, sᵢ]]` (`hagopian76_initial_segment` with `E := Fᵢ`,
`F := H`); the intersection is `d⁻¹[[0, s*]]`, `s* = inf sᵢ`; `s* > 0` because `E ⊆ ⋂` and `E` is not
inside its end set `k⁻¹(0)` (`k` is onto); `piece_map` with `a = 0`, `b = s*`. -/
theorem extChainInter_in (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsExtensionAway E (layer k 0) H) {c : Set (Set M)} (hne : c.Nonempty)
    (hc : ∀ F ∈ c, F ⊆ H ∧ IsExtensionAway E (layer k 0) F) :
    IsExtensionAway E (layer k 0) (⋂₀ c) :=
  extChainInter_in_aux hX hi hE hH hne hc

/-- **A. `ExtChainInter` holds** (the `Prop` of batch 169, unchanged), for the end set `k⁻¹(0)` and
every `O`, `p`, `q`. A chain lies, below any of its members `F₀`, inside `F₀`, and the members above
`F₀` do not change the intersection; then `extChainInter_in`. -/
theorem extChainInter (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) (O : Set Pt) (p q : Pt) :
    ExtChainInter E (layer k 0) O p q :=
  extChainInter_aux hX hi hE O p q

/-- **A′. T13, unconditional** (p. 347): "Let `F` be a continuum that is irreducible with respect
to the following properties: 1. `F` is an extension of `E` in `M` away from `k⁻¹(0)`. 2. `F`
separates `p` from `f(p)` in `π⁻¹[D]`."

*Shape:* that of `hagopian76_T13` (batch 169) with `X₀ = k⁻¹(0)` and the hypothesis
`ExtChainInter` discharged by `extChainInter`. Given one separating extension `H` (supplied by
`exists_generic_pq`, with `O = π⁻¹[D]`, `q = f(p)`), there is a separating extension `F ⊆ H`
containing no other separating extension. -/
theorem hagopian76_T13_uncond (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {O : Set Pt} (hO : IsOpen O) {p q : Pt} {H : Set M}
    (hH : IsExtensionAway E (layer k 0) H) (hHs : SepIn O (toPt H) p q) :
    ∃ F ⊆ H, IsExtensionAway E (layer k 0) F ∧ SepIn O (toPt F) p q ∧
      ∀ F', IsExtensionAway E (layer k 0) F' → SepIn O (toPt F') p q → F' ⊆ F → F' = F :=
  hagopian76_T13 hO (extChainInter hX hi hE O p q) hH hHs

/-- **B, first step of the covering half** (commission 170 §1.B: "If `Fr U ⊆ Z`, then `Z`
separates the plane, which is impossible"). For a proper subcontinuum `K` of `M` (`d⁻¹[I]`,
`d⁻¹[J]`, `P` in T17), a continuous `π` and an open `D` with `π⁻¹[D]` bounded, the closure of every
component of `π⁻¹[D] − K` meets `π⁻¹[Fr D]` (by `hagopian76_D`, `π⁻¹` of `I₂`, the bottom edge, or
a side edge).

*Shape (left to me):* the remaining three cases of §1.B (bottom: below; `I₂`: above; pockets at the
side edges) are open; see the commented-out `crossing_sides_cover` below. -/
theorem crossing_sides_cover_frontier (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {K : Set M} (hK : Fold.Q78.IsContinuum K) (hKM : K ≠ univ) {π : Pt → Pt} (hπc : Continuous π)
    {D : Set Pt} (hD : IsOpen D) (hDb : Bornology.IsBounded (π ⁻¹' D)) {x : Pt}
    (hx : x ∈ π ⁻¹' D \ toPt K) :
    (closure (connectedComponentIn (π ⁻¹' D \ toPt K) x) ∩ π ⁻¹' frontier D).Nonempty :=
  component_reaches_frontier_D hX hi hK hKM hπc hD hDb hx

/-- **C. "Follows" for crossing components** (commission 170 §1.C). In the set-up of
`crossing_essential` there is a height `c > 0` such that for every connected `B ⊆ M` over
`F[[3/22, 19/22] × (0, c]]` whose closure meets both side edges: `Cl B` misses `E`, and for an
`ε₁`-homeomorphism `h` **with Property 1's link condition** `h[piece (j + 1)] ⊆ Lⱼ`:
* `Cl B ⊆ h[E]`, and `G = h⁻¹[Cl B] ⊆ E` is essential to `R(E)`;
* **`Cl B ⊇ h[k⁻¹((4/11, 7/11))]`.**

*Shape:* the crossing is a hypothesis. Link control puts the left end of `Cl B` in a link `L_a`,
`a ≤ 2`, and the right end in `L_c`, `c ≥ 8`; by the link condition and the chain property the
corresponding points of `G` have parameters `≤ 4/11` and `≥ 7/11` (the commission expected
`3/11` and `8/11`; one link is lost at each end because a link `Lⱼ` meeting `L_a` only gives
`j ≤ a + 1`); `layerSet_Ioo_subset` gives the middle. So `Cl B` meets `L₄`, `L₅`, `L₆` along
`h[k⁻¹((4/11, 7/11))]`, besides `L_a` and `L_c`. -/
theorem follows_crossing (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      Disjoint (closure B) E ∧ ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ closure B ⊆ h '' E ∧
        h ⁻¹' closure B ⊆ E ∧ IsEssential k (h ⁻¹' closure B) ∧
        (∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) ∧
        h '' layerSet k {t | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} ⊆ closure B :=
  follows_crossing_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1

end Thm1

/-- **D. `crossing_set_closed`, the least `v`** (p. 347: "Let `v` be the first point of `[0, 1]`
such that …"). For a compact `F ⊆ M` with a continuous `d : F → [0, 1]` and closed sets `A`, `B`,
`W` of the plane (the side edges and the region over `Cl D`, with margins): if some layer `d⁻¹(v)`
contains a connected set inside `W` meeting `A` and `B`, there is a least such `v`.

*Shape (left to me):* the margins are carried by the closed sets `A`, `B`, `W`; the open conditions
of Property 3 (crossing the *open* side edges, missing `E` and `π⁻¹[I₂]`) are not closed and are
not covered. *Proof:* `crossing_set_closed` (the upper limit of a subsequence is connected,
`limsup_isPreconnected`), and compactness of `[0, 1]`. -/
theorem hagopian76_first_crossing_param {M : Set Pt} {F : Set M} (hFc : IsCompact F)
    {d : F → unitInterval} (hd : Continuous d) {A B W : Set Pt} (hA : IsClosed A)
    (hB : IsClosed B) (hW : IsClosed W)
    (hne : ∃ v : unitInterval, ∃ Z : Set F, IsPreconnected Z ∧ Z ⊆ d ⁻¹' {v} ∧
      (∀ z ∈ Z, ((z : M) : Pt) ∈ W) ∧ (∃ z ∈ Z, ((z : M) : Pt) ∈ A) ∧
      ∃ z ∈ Z, ((z : M) : Pt) ∈ B) :
    ∃ v : unitInterval, (∃ Z : Set F, IsPreconnected Z ∧ Z ⊆ d ⁻¹' {v} ∧
      (∀ z ∈ Z, ((z : M) : Pt) ∈ W) ∧ (∃ z ∈ Z, ((z : M) : Pt) ∈ A) ∧
      ∃ z ∈ Z, ((z : M) : Pt) ∈ B) ∧
      ∀ u : unitInterval, (∃ Z : Set F, IsPreconnected Z ∧ Z ⊆ d ⁻¹' {u} ∧
        (∀ z ∈ Z, ((z : M) : Pt) ∈ W) ∧ (∃ z ∈ Z, ((z : M) : Pt) ∈ A) ∧
        ∃ z ∈ Z, ((z : M) : Pt) ∈ B) → v ≤ u := by
  obtain ⟨v, hv, hmin⟩ :=
    (crossing_set_closed hFc hd hA hB hW).isCompact.exists_isLeast hne
  exact ⟨v, hv, fun u hu => hmin hu⟩

/-! ## Open items

The obstructions are in `OPEN.md` (batch 170) and in `doc/batches/REPORT-batch170.md`.

**OPEN (B, `crossing_sides_cover`).** First step proved (`crossing_sides_cover_frontier`). The three
cases — a component reaching the bottom edge is below, one reaching `I₂` is above, and the pockets
at the side edges — are not done. Shape proposal (positions through the vertical and the side
edges, report §1.B):

theorem crossing_sides_cover … (hK : Fold.Q78.IsContinuum K) (hKM : K ≠ univ)
    (Z = toPt K crossing, missing the vertical at (0, u₁] and [u₂, w₂)) :
    π ⁻¹' (F '' D') \ toPt K ⊆ belowSet' π F D' t₀ u₁ (toPt K) ∪ aboveSet' π F D' t₀ u₂ w₂ (toPt K) := by
  sorry

**OPEN (D, `hagopian76_property3`).** `crossing_set_closed` (with margins) is proved. The shift
`g` (`hagopian76_property3_shift`, batch 161) is small, but it does not preserve a fixed margin:
`g[Q]` crosses with margin `μ − δ`, not `μ`, so the least `v` for margin `μ` is not contradicted.
The route through Lemma T (recreate the crossing in `d⁻¹(u)` from the middle translate that `Cl Q`
contains, item C) avoids the margin but needs Lemma T inside a layer of `F` for the composite
`g ∘ h`, which is `(δ + ε₁)`-small, not `δ`-small.

theorem hagopian76_property3 … : ∀ v Z, Z ⊆ layer d v → Fold.Q78.IsContinuum Z →
    Disjoint Z E → Disjoint (toPt Z) (π ⁻¹' I₂) → ¬ Crossing Z := by
  sorry

**OPEN (E, `hagopian76_T15_T17`, `hagopian76_theorem1_cond`).** Wait on B (the cases) and D; T15
("It follows from Property 3 that `I` is finite") needs Property 3; Property 4's base case and the
induction need the covering half. Skeleton proposal in report §5.

theorem hagopian76_theorem1_cond :
    (∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (E : Set M) (k : E → unitInterval),
      IsMinimalAdmissible E k → RsetDichotomy k) → Hagopian76Thm1 := by
  sorry
-/

end HPC.Hagopian
