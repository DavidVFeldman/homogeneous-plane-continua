import HPC.Hagopian.H76Descent

/-!
# Batch 173: Hagopian 1976, Theorem 1 — Property 3 by descent; pockets; the ends of crossing
# components; T15–T17 and the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 173 §1.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76R.lean`.

Supporting file: `H76Descent` — layer crossings (`LayerCrossing`, a closed condition on a layer),
Hagopian's domain in the form used (`IsCrossRegion`), D1, D2 and the least-element argument.

Shapes are recorded at each statement and in `doc/batches/REPORT-batch173.md`. Items left open are
commented out at the end, with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **D1 (crossing from a translate in a layer)** (commission 173 §1). Set-up: `E` with `ε₁`
(`IsEps1`, `EndCtl`), the quotient `π` with collar `F`, and an extension `G` of `E` away from
`k⁻¹(0)` with map `d`. There is `c > 0` such that for every domain `D = F[D′]` of height `c₁ ≤ c`
(`IsCrossRegion`), every **continuous** `ψ : M → M` with `dist(y, ψ(y)) < 2ε₁`, every layer
`d⁻¹(u)` containing `ψ[E]`, and every `x ∈ E` with `k(x) ∈ [4/11, 7/11]` and `ψ(x)` over `D`:
1. `d⁻¹(u)` misses `E` (D1.1);
2. `d⁻¹(u)` contains a layer crossing (D1.5).

*Shape (left to me):* the commission's hypothesis "`ψ[k⁻¹(t)] ⊆ π⁻¹[D]` for all
`t ∈ [4/11, 7/11]`" is weakened to one point `ψ(x)` over `D`; `ψ[E] ⊆ d⁻¹(u)` replaces
`ψ[G] ⊆ d⁻¹(u)`, and `0 < u < 1` is not needed. The crossing is the union of the closures of the
components through `ψ(x)` of `ψ[k⁻¹[[0, k(x)]]] ∩ π⁻¹[D]` and `ψ[k⁻¹[[k(x), 1]]] ∩ π⁻¹[D]`
(boundary bumping). D1.2 and D1.3 are used in the forms: `π⁻¹[I₂]` misses `M`, and `ψ` of an end
layer is not over `D` (`EndCtl` with `pi_thin_near_layer`). D1.4 (coarse monotonicity) is
`IsEps1.sep_of_gap`. -/
theorem crossing_from_layer_translate (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G) (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ ψ : M → M, Continuous ψ → (∀ v, dist v (ψ v) < 2 * ε₁) →
      ∀ u : unitInterval, ψ '' E ⊆ layer d u →
      ∀ x : E, 4 / 11 ≤ (k x : ℝ) → (k x : ℝ) ≤ 7 / 11 → π (ψ x : Pt) ∈ F '' D' →
      Disjoint (layer d u) E ∧ LayerCrossing d π F c₁ D' u :=
  crossing_from_layer_translate_aux hX hi hE he hend hπ.continuous hπS hγπ hF hG hEG hX0

/-- **D2 (descent)** (commission 173 §1). Set-up of `hagopian76_property3_translate`. There is
`c > 0` such that for every domain `D = F[D′]` of height `c₁ ≤ c`: if an interior layer `d⁻¹(v)`
(`0 < v < 1`) contains a layer crossing, so does some `d⁻¹(u)` with `0 < u < v`.

*Shape (left to me):* the crossing is a `LayerCrossing` (closed side segments, closure of `D`). The
commission's `ρ₀` is replaced by a ball around the single point `h(x)`, `k(x) = 1/2`, inside the
open set over `D` (so no smaller interval `[4/11 + ζ, 7/11 − ζ]` is needed); `δ = min(ρ, ε₁)`. -/
theorem crossing_descends (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
      ∀ v : unitInterval, 0 < v → v < 1 → LayerCrossing d π F c₁ D' v →
      ∃ u : unitInterval, 0 < u ∧ u < v ∧ LayerCrossing d π F c₁ D' u :=
  crossing_descends_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hEG hX0

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Hagopian's domain is a crossing region.** The output of `hagopian76_D` over `[3/22, 19/22]`
(frontier `I₂ ∪` axis `∪` side segments of heights `r₂, s₂ ≤ c₁`), with `I₂` missing `π[M]` (T7),
satisfies `IsCrossRegion`. -/
theorem isCrossRegion_of_D {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ r₂ s₂ : ℝ} {I₂ : Set Pt}
    {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c₁) (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
      F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂))
    (hIM : Disjoint I₂ (π '' M)) (hr₂ : r₂ ≤ c₁) (hs₂ : s₂ ≤ c₁) :
    IsCrossRegion M π F c₁ D' := by
  refine ⟨hDR, hFDo, ?_⟩
  rintro p ⟨hpf, hpM⟩
  rw [hFDf] at hpf
  rcases hpf with ((hI | hb) | ha) | hb'
  · exact absurd hpM (disjoint_left.1 hIM hI)
  · exact Or.inl (Or.inl hb)
  · exact Or.inl (Or.inr (image_mono (Set.prod_mono le_rfl (Icc_subset_Icc le_rfl hr₂)) ha))
  · exact Or.inr (image_mono (Set.prod_mono le_rfl (Icc_subset_Icc le_rfl hs₂)) hb')

/-- **A. Property 3, in Hagopian's form** (p. 347: "no layer `d⁻¹(v)`, `0 < v < 1`, contains a
component of `F ∩ π⁻¹[D]` whose closure meets `π⁻¹[(p₁, r)]` and `π⁻¹[(p₅, s)]`"). Set-up of
`hagopian76_property3_translate`. There is `c > 0` such that for every domain `D = F[D′]` of height
`c₁ ≤ c` (`IsCrossRegion`), no connected `B` over `D` whose closure meets the closed side segments
over `3/22` and `19/22` has its closure in a layer `d⁻¹(v)`, `v < 1`.

*Proof:* the closure of `B` is a layer crossing; `property3_layer_aux` (least element of the closed
set of crossing parameters, against D2). -/
theorem hagopian76_property3_domain (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
      ∀ B : Set M, IsPreconnected B → (∀ x ∈ B, π (x : Pt) ∈ F '' D') →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      ∀ v : unitInterval, v < 1 → ¬ closure B ⊆ layer d v := by
  obtain ⟨c, hc, hc1, hP3⟩ := property3_layer_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
    hG hEG hX0
  refine ⟨c, hc, hc1, fun c₁ D' hc₁ hR B hBc hBD hBl hBr v hv1 hBv => ?_⟩
  refine hP3 c₁ D' hc₁ hR v hv1 ⟨closure B, hBc.closure, hBv, ?_, hBl, hBr⟩
  have hWc : IsClosed {m : M | π (m : Pt) ∈ closure (F '' D')} :=
    isClosed_closure.preimage (hπ.continuous.comp continuous_subtype_val)
  exact closure_minimal (fun x hx => subset_closure (hBD x hx)) hWc

/-- **A. Property 3** (p. 347), **unconditionally**, in the thin-strip form of
`hagopian76_property3_of_end` (batch 172), whose hypothesis `Property3End` is dropped: there is
`c > 0` such that no connected `B` over `F[[3/22, 19/22] × (0, c]]` whose closure meets both open
side edges has its closure in a layer `d⁻¹(v)`, `v < 1`, of the extension `G`.

*Shape:* the conclusion of `hagopian76_property3_of_end` with `0 < v` dropped (the layer
`d⁻¹(0) = k⁻¹(0)` is covered too); `G` is any extension of `E` away from `k⁻¹(0)` (Hagopian's `F`
is one, chosen irreducible with respect to separating `p` from `f(p)`). The far end layer `d⁻¹(1)`,
which Hagopian's "an element of the decomposition" also includes, is not covered: the swallowing
lemma, hence `hagopian76_property3_translate`, needs an interior layer.

*Proof:* T7 gives an arc `I₂` missing `π[M]` at height `≤ c′`, `hagopian76_D_aux` the domain
`D = F[D′]` (a crossing region, `isCrossRegion_of_D`), and `rect_domain_low` a low strip
`(3/22, 19/22) × (0, c₀) ⊆ D′`. For `c = min(c₀, c′)` the closure of a thin crossing lies over
`Cl D` and meets the closed side segments, so it is a layer crossing, excluded by
`property3_layer_aux`. Hagopian's argument (the least `v`, the shift by Lemmas 2 and 3) with the
swallowing lemma (`hagopian76_property3_translate`) supplying "By Lemma 1 and Property 1". -/
theorem hagopian76_property3 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
      ∀ v : unitInterval, v < 1 → ¬ closure B ⊆ layer d v := by
  obtain ⟨c₃, hc₃, hc₃1, hP3⟩ := property3_layer_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG
    hP1 hG hEG hX0
  obtain ⟨c₇, hc₇, hc₇1, -, hT7⟩ := hagopian76_T7 hX hi hE hπ hπS hγπ hF (a := 3 / 22)
    (b := 19 / 22) (by norm_num) (by norm_num) (by norm_num) isOpen_univ (subset_univ _)
  set c' := min c₃ c₇ with hc'
  have hc'0 : 0 < c' := lt_min hc₃ hc₇
  have hc'1 : c' ≤ 1 := (min_le_right _ _).trans hc₇1
  obtain ⟨r, s, I₂, hI, hIR, hIM, hIs, hr, hs⟩ := hT7 c' hc'0 (min_le_right _ _)
  obtain ⟨r₂, s₂, D', hr₂, hs₂, -, -, hIarc, -, -, -, hDR, hDf, hFDo, -, -, -, hFDf⟩ :=
    hagopian76_D_aux hF (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (3 / 22 : ℝ) < 19 / 22)
      (by norm_num : (19 / 22 : ℝ) < 1) hc'0 hc'1 hI hIR hIs hr hs
  have hR : IsCrossRegion M π F c' D' := isCrossRegion_of_D hDR hFDo hFDf hIM hr₂.2 hs₂.2
  obtain ⟨c₀, hc₀, -, hc₀I⟩ := exists_height_below hIarc.isCompact fun z hz => hz.1.2.1
  have hlow : Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ Ioo 0 c₀ ⊆ D' :=
    rect_domain_low (r := ((3 / 22 : ℝ), r₂)) (s := ((19 / 22 : ℝ), s₂)) (by norm_num) hDR hDf hc₀
      fun z hz => (hc₀I z hz).le
  refine ⟨min c₀ c', lt_min hc₀ hc'0, (min_le_right _ _).trans hc'1,
    fun B hBc hBin hBl hBr v hv1 hBv => ?_⟩
  have hc₀' : min c₀ c' ≤ c₀ := min_le_left _ _
  have hcc' : min c₀ c' ≤ c' := min_le_right _ _
  /- The closed low strip lies in `F[Cl D′] ⊆ Cl F[D′]`. -/
  have hclD' : closure D' ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    (closure_mono hDR).trans (by
      rw [closure_prod_eq, closure_Ioo (by norm_num), closure_Ioo hc'0.ne]
      exact Set.prod_mono (Icc_subset_Icc (by norm_num) (by norm_num))
        (Icc_subset_Icc (by norm_num) hc'1))
  have hFc : ContinuousOn F (closure D') :=
    (continuousOn_iff_continuous_restrict.2 hF.1.continuous).mono hclD'
  have hstrip : F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 (min c₀ c')) ⊆ closure (F '' D') := by
    refine (image_mono ?_).trans hFc.image_closure
    refine subset_trans ?_ (closure_mono hlow)
    rw [closure_prod_eq, closure_Ioo (by norm_num), closure_Ioo hc₀.ne]
    exact Set.prod_mono le_rfl (Icc_subset_Icc le_rfl hc₀')
  have hWc : IsClosed {m : M | π (m : Pt) ∈ closure (F '' D')} :=
    isClosed_closure.preimage (hπ.continuous.comp continuous_subtype_val)
  have hside : ∀ {a' : ℝ},
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({a'} : Set ℝ) ×ˢ Ioc 0 (min c₀ c'))) →
      ∃ x ∈ closure B, π (x : Pt) ∈ F '' (({a'} : Set ℝ) ×ˢ Icc 0 c') := by
    rintro a' ⟨x, hx, hxF⟩
    refine ⟨x, hx, image_mono (Set.prod_mono le_rfl ?_) hxF⟩
    exact fun t (ht : t ∈ Ioc 0 (min c₀ c')) => (⟨ht.1.le, ht.2.trans hcc'⟩ : t ∈ Icc 0 c')
  refine hP3 c' D' (min_le_left _ _) hR v hv1 ⟨closure B, hBc.closure, hBv, ?_, hside hBl,
    hside hBr⟩
  refine closure_minimal (fun x hx => hstrip ?_) hWc
  obtain ⟨z, hz, hFz⟩ := hBin x hx
  exact ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2⟩, hFz⟩

/-- **D, first step toward "It follows from Property 3 that `I` is finite"** (p. 347). Set-up of
`hagopian76_property3_translate`; `D = F[D′]` of height `c₁ ≤ c`. Below any `v₀ < 1` there is
`λ > 0` such that every connected `Z ⊆ d⁻¹[[x, y]]` (`y ≤ v₀`) over `Cl D` meeting both closed side
segments has `y − x ≥ λ`. In particular each interval of Hagopian's collection `I` lying below `v₀`
has length `≥ λ`.

*Shape (added):* this is what the closedness argument gives from Property 3. It does not give
finiteness of `I`: see the report, §1.D. -/
theorem crossing_length_pos (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
      ∀ v₀ : unitInterval, v₀ < 1 → ∃ lam > 0, ∀ (x y : unitInterval) (Z : Set M), y ≤ v₀ →
      IsPreconnected Z → Z ⊆ layerSet d (Icc x y) →
      (∀ z ∈ Z, π (z : Pt) ∈ closure (F '' D')) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      lam ≤ (y : ℝ) - x :=
  crossing_length_pos_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hEG hX0

end Thm1

/-! ## Open items

The obstructions are in `OPEN.md` (batch 173) and in `doc/batches/REPORT-batch173.md`.

**OPEN (B, pockets: `CoverPocket`).** Coarse monotonicity (`IsEps1.sep_of_gap`) places every point
of a crossing continuum `Cl Cᵢ₋₁ ⊆ h′[E]` over abscissa `t` in `h′` of a piece adjacent to the
piece of `t`. It does not bound the reach of a pocket: both boundary strands of a pocket reaching
the middle abscissae may lie in `h′` of the same middle pieces, since no smallness of the layers or
pieces of `E` is available (`IsEps1` separates pieces, it does not make them small).

def CoverPocket … : Prop := -- no point of `L₆ ∩ π⁻¹[D]` lies in a pocket component of
                             -- `π⁻¹[D] − Cl Cᵢ₋₁`

theorem crossing_sides_cover' … (hP : CoverPocket …) :
    π ⁻¹' (F '' D') \ Z ⊆ belowSet π F D' t₀ u₁ Z ∪ aboveSet π F D' t₀ u₂ w₂ Z := by
  sorry

**OPEN (C, `CrossingEnds`).** T17's "the continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`"
concerns the shortest extension `L` of `Cl Cᵢ` containing `Cᵢ₋₁` and its subcontinuum `N`, not a
single translate. D1 controls one translate `ψ[E]` (its ends lie off `Cl D`), but `N` runs through
`Cl Cᵢ`, `Cl Cᵢ₋₁` and the part of `L` between them, about which D1 says nothing.

theorem crossing_component_ends … :
    (toPt (closure B) ∩ L 1).Nonempty ∧ (toPt (closure B) ∩ L 9).Nonempty := by
  sorry

**OPEN (D, T15–T17 and the assembly).** "`I` is finite" is not derived (only the length bound
`crossing_length_pos`); Property 4, its induction and the first-component argument are not
formalized, even conditionally.

-- `hagopian76_I_finite`: proved in batch 174, `Hagopian76S.lean`.

theorem hagopian76_T15_T17 … : False := by
  sorry

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
