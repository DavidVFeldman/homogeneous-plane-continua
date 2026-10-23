import HPC.Hagopian.H76JXs

/-!
# Batch 174: Hagopian 1976, Theorem 1 — "`I` is finite"; the end element; `J` and the `xᵢ`;
# Property 4; the induction; the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 174 §1–2.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76S.lean`.

Supporting files:
* `H76EndElement` — Property 3 at the end element through a proper extension (§1.6), and the
  length bound in every layer;
* `H76IFinite` — crossing components, irreducible intervals, Hagopian's `I`, disjoint interiors,
  finiteness (§1.1–1.5);
* `H76JXs` — `e`, `x₂ = e` (with `e < x` for every `[x, y] ∈ I`), and the base case of Property 4.

Shapes are recorded at each statement and in `doc/batches/REPORT-batch174.md`. Items left open are
commented out at the end, with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A. Property 3 for the end element `d⁻¹(1)`, via a proper extension** (commission 174 §1.6;
p. 347). Set-up of `hagopian76_property3`. There is `c > 0` such that no connected `B` over
`F[[3/22, 19/22] × (0, c]]` whose closure meets both open side edges has its closure in **any**
layer `d⁻¹(v)`, `v ∈ [0, 1]`, of the extension `G` (Hagopian's `F`).

*Shape (left to me):* the conclusion of `hagopian76_property3` with `v < 1` dropped. *Proof:* a
proper extension `G′ ⊋ G` away from `k⁻¹(0)` (Lemma 4, `exists_proper_extension`) has
`d′⁻¹(s′) = d⁻¹(1)` with `s′ < 1` (`ext_layers`), and Property 3 for `G′` excludes that layer
(`exists_end_extension`). The layer-crossing form is `property3_layer_all`. -/
theorem hagopian76_property3_end_element (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, ¬ closure B ⊆ layer d v :=
  property3_end_element_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hEG hX0

/-- **A′. Property 3 as printed, for every element of the decomposition** (p. 347: "No component of
`F ∩ π⁻¹[D]` whose closure meets both `π⁻¹[(p₁, r)]` and `π⁻¹[(p₅, s)]` is contained in an element
of the decomposition of `F`"). Set-up of `hagopian76_property3`; `D = F[D′]` of height `c₁ ≤ c`.
No crossing component (`IsCrossingComponent`) lies in a layer `d⁻¹(v)`, `v ∈ [0, 1]`.

*Shape (added):* the printed statement, now that the end element is covered; it replaces the
batch-165 shape proposal in `Hagopian76J.lean`. -/
theorem hagopian76_property3_components (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ C : Set M, IsCrossingComponent G π F c₁ D' C → ∀ v : unitInterval, ¬ C ⊆ layer d v :=
  property3_components_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hEG hX0

/-- **B. "It follows from Property 3 that `I` is finite"** (p. 347). Set-up of
`hagopian76_property3`. There is `c > 0` such that for every domain `D = F[D′]` of height `c₁ ≤ c`
(`IsCrossRegion`; Hagopian's `D` by `isCrossRegion_of_D`), Hagopian's collection `I`
(`crossingIntervals`: the `[x, y]` with `d⁻¹[[x, y]]` irreducible with respect to containing a
component of `G ∩ π⁻¹[D]` whose closure meets both closed side segments) is finite.

*Shape (left to me):* `I` is the set of pairs `(x, y)`; "irreducible" is minimality among the
intervals `[x′, y′]` with `C ⊆ d⁻¹[[x′, y′]]` (`IsIrreducibleInterval`). Distinct members have
disjoint interiors, `crossingIntervals_disjoint` (no Property 3 needed). *Proof:* commission 174
§1 (`I_finite_aux`). -/
theorem hagopian76_I_finite (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      (crossingIntervals d π F c₁ D').Finite :=
  I_finite_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hEG hX0

/-- **C. `e` and `x₂ = e`** (pp. 347–348: "Let `e` be the point of `[0, 1]` such that
`d⁻¹[[0, e]] = E` … Note that `x₁ = 0`, `x₂ = e`"). There is `e > 0` with `d⁻¹[[0, e]] = E`, and
`e < x` for every `[x, y] ∈ I`. Hence `[0, e]` is a block of `St J` by itself, `x₁ = 0`, `x₂ = e`.

*Shape (left to me):* the sequence `xᵢ` is not constructed (it is determined by the finite set
`J = I ∪ {[0, e]}`, `hagopian76_I_finite`); the statement gives what the two notes need. `x₂ₙ = 1`
is open (`LastIntervalReachesOne`, below). -/
theorem hagopian76_J_xs (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    (hπc : Continuous π) {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G) (hX0 : layer d 0 = layer k 0) {c₁ : ℝ}
    (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') :
    ∃ e : unitInterval, 0 < e ∧ layerSet d (Icc 0 e) = E ∧
      ∀ p ∈ crossingIntervals d π F c₁ D', e < p.1 :=
  J_xs_aux hX hi hE hπc hγπ hF hG hEG hX0 hc₁ hR.sub

omit [CompactSpace M] [ConnectedSpace M] in
/-- **D, base case** (p. 348: "Note that `[x₁, x₂]` does not have Property 4"). The block
`d⁻¹[[x₁, x₂]] = d⁻¹[[0, e]] = E` separates no point from any point in `π⁻¹[D]` (`SepIn`, the
notion of T13), so clause (2) of Property 4 fails for every `y`.

*Shape (left to me):* `D′` connected is a hypothesis (for Hagopian's domain, `rect_frontier_domain`,
batch 172). This settles report 170 §1.E's reduction. -/
theorem hagopian76_property4_base {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)}
    (hR : IsCrossRegion M π F c₁ D') (hD'c : IsPreconnected D')
    {G : Set M} {d : G → unitInterval} {e : unitInterval} (he : layerSet d (Icc 0 e) = E)
    (y z : Pt) : ¬ SepIn (π ⁻¹' (F '' D')) (toPt (layerSet d (Icc 0 e))) y z :=
  property4_base_aux hπ hπS hγπ hF hc₁ hR hD'c he y z

end Thm1

/-- **Named `Prop` for `x₂ₙ = 1`** (p. 348, "Note that … `x₂ₙ = 1`"): some interval of `I` ends at
`1`, i.e. the last block of `St J` reaches the end layer `d⁻¹(1)`. Open: it needs the irreducibility
of Hagopian's `F` with respect to separating `p` from `f(p)` (T13); it is false for a general
extension `G` (for instance `G = E`, where `I = ∅`). -/
def LastIntervalReachesOne {M : Set Pt} {G : Set M} (d : G → unitInterval) (π : Pt → Pt)
    (F : ℝ × ℝ → Pt) (c₁ : ℝ) (D' : Set (ℝ × ℝ)) : Prop :=
  ∃ p ∈ crossingIntervals d π F c₁ D', p.2 = 1

/-! ## Open items

The obstructions are in `OPEN.md` (batch 174) and in `doc/batches/REPORT-batch174.md`.

**OPEN (C, `x₂ₙ = 1`: `LastIntervalReachesOne`).** For Hagopian's `F` (irreducible with respect to
being an extension of `E` away from `k⁻¹(0)` that separates `p` from `f(p)` in `π⁻¹[D]`, T13): if no
interval of `I` reaches `1`, the part `d⁻¹((y*, 1])` beyond the last crossing block should be
removable while keeping the separation, against irreducibility. This needs that the components of
`π⁻¹[D] − F` are unchanged when a tail of `F` containing no crossing component is cut off; the tail
still meets `π⁻¹[D]` in non-crossing components (whose closures miss a side segment), and a
non-crossing component can still separate. Not proved.

theorem hagopian76_x2n_eq_one … (hFirr : … T13 irreducibility …) :
    LastIntervalReachesOne d π F c₁ D' := by
  sorry

**OPEN (D, Property 4 for `[x₂ₙ₋₁, x₂ₙ]`).** "The interval `[x₂ₙ₋₁, x₂ₙ]` has the following property:
4. There exists a point `yₙ` of `K` such that (1) the closure of the `yₙ`-component `Cₙ` of
`M ∩ π⁻¹[D]` is essential to `h[R(E)]`, and (2) `d⁻¹[[x₂ₙ₋₁, x₂ₙ]]` separates `yₙ` from `f(yₙ)` in
`π⁻¹[D]`." No argument is printed. Clause (2) needs that, of the blocks of `St J`, only the last
separates; this is the irreducibility of `F` (drop the other blocks one at a time), which runs into
the obstruction of `x₂ₙ = 1` above (the gaps between blocks meet `π⁻¹[D]` in non-crossing
components). Clause (1) needs the point `yₙ ∈ K` and the essential-continuum machinery of T12.

theorem hagopian76_property4 … : ∃ yₙ ∈ K, IsEssential (closure Cₙ) (h '' Rset E) ∧
    SepIn (π ⁻¹' (F '' D')) (toPt (layerSet d (Icc x₂ₙ₋₁ x₂ₙ))) yₙ (f yₙ) := by
  sorry

**OPEN (E, the induction, Cases 1 and 2).** "Following Bing [2, p. 225], we now show that if
`I = [x₂ᵢ₋₁, x₂ᵢ]` has Property 4, then so does `J = [x₂ᵢ₋₃, x₂ᵢ₋₂]`." Still open:
* the pockets in "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`": what the induction
  uses is that every point of `π⁻¹[D] − P` near `L₆` lies above `d⁻¹[I]` or below `d⁻¹[J]`, where `P`
  is `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` plus an arc `Q`. The layers of `Cl Cᵢ₋₁` over `(x, y)` lie in `Cl Cᵢ₋₁`
  (`IsIrreducibleInterval.layerSet_Ioo_subset_closure`), but a pocket is bounded by a strand of
  `d⁻¹[[x, y]]`, and nothing bounds how far a strand of a layer of `F` reaches from a side segment
  (coarse monotonicity controls translates of `E`, not layers of `F`);
* "the continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`": `N` lies in the shortest extension `L`
  of `Cl Cᵢ` containing `Cᵢ₋₁`; the printed reason, "Since `L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and
  `Cl Cᵢ`", uses that `L` minus its end links follows the two crossing closures, which needs
  Property 3 for `L` (an extension of `Cl Cᵢ`, not of `E`) and the first-component argument.

theorem hagopian76_property4_step … (hI : Property4 … i) : Property4 … (i - 1) := by
  sorry

**OPEN (F, the assembly).** Needs D and E. No conditional form is stated: Property 4 and its step are
not formalized even as named `Prop`s with the right set-up (the point set `K`, the homeomorphisms
`h`, `f` of T12, and the blocks `xᵢ`).

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
