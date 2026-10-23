import HPC.Hagopian.H76Uniform
import HPC.Hagopian.H76Nondeg

/-!
# Batch 179, §4: uniform heights (II) — every layer, `I` finite, Property 3 as printed, `x₂ₙ = 1`

Continuation of `H76Uniform`: the statements of `property3_layer_all`, `crossing_length_pos_all`,
`hagopian76_I_finite`, `hagopian76_property3_components` and `hagopian76_x2n_eq_one` with the
height chosen before `G`, and the nondegeneracy of `I` (§0.1) in the same form.

For `property3_layer_all` the uniform form is simpler than the original: the end layer `d⁻¹(1)` is an
interior layer of a proper extension `G′` (`exists_end_extension`), and the uniform height serves
`G′` as well as `G`, so no minimum of two heights is needed.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Uniform2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§4: Property 3 in every layer, uniform height** (`property3_layer_all` with `c` before `G`). -/
theorem property3_layer_all_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c →
      IsCrossRegion M π F c₁ D' → ∀ v : unitInterval, ¬ LayerCrossing d π F c₁ D' v := by
  obtain ⟨c, hc, hc1, hP⟩ := property3_layer_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨c, hc, hc1, fun G d hG hEG hX0 c₁ D' hc₁ hR v => ?_⟩
  rcases lt_or_eq_of_le (unitInterval.le_one' : v ≤ 1) with hv | rfl
  · exact hP G d hG hEG hX0 c₁ D' hc₁ hR v hv
  · obtain ⟨G', d', hG', -, hEG', hX0', s, -, hs1, hs, -⟩ := exists_end_extension hX hi hG hEG hX0
    rw [layerCrossing_congr hs.symm]
    exact hP G' d' hG' hEG' hX0' c₁ D' hc₁ hR s hs1

/-- **§4: the length bound, uniform height** (`crossing_length_pos_all` with `c` before `G`). -/
theorem crossing_length_pos_all_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c →
      IsCrossRegion M π F c₁ D' →
      ∃ lam > 0, ∀ (x y : unitInterval) (Z : Set M),
      IsPreconnected Z → Z ⊆ layerSet d (Icc x y) →
      (∀ z ∈ Z, π (z : Pt) ∈ closure (F '' D')) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      lam ≤ (y : ℝ) - x := by
  obtain ⟨c, hc, hc1, hP3⟩ := property3_layer_all_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  exact ⟨c, hc, hc1, fun G d hG hEG hX0 c₁ D' hc₁ hR =>
    crossing_length_pos_of_forall hG hπ.continuous hF (hc₁.trans hc1)
      (hP3 G d hG hEG hX0 c₁ D' hc₁ hR)⟩

/-- **§4: "`I` is finite", uniform height** (`hagopian76_I_finite` with `c` before `G`). -/
theorem hagopian76_I_finite_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c →
      IsCrossRegion M π F c₁ D' → (crossingIntervals d π F c₁ D').Finite := by
  obtain ⟨c, hc, hc1, hlen⟩ := crossing_length_pos_all_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨c, hc, hc1, fun G d hG hEG hX0 c₁ D' hc₁ hR => ?_⟩
  obtain ⟨lam, hlam, hl⟩ := hlen G d hG hEG hX0 c₁ D' hc₁ hR
  refine finite_of_disjoint_Ioo hlam (fun p hp => ?_)
    (fun p hp q hq hpq => crossingIntervals_disjoint hG hp hq hpq)
  obtain ⟨C, hC, hI⟩ := hp
  have hWc : IsClosed {m : M | π (m : Pt) ∈ closure (F '' D')} :=
    isClosed_closure.preimage (hπ.continuous.comp continuous_subtype_val)
  refine hl p.1 p.2 (closure C) hC.isConnected.isPreconnected.closure
    (closure_minimal hI.1 (isClosed_layerSet_Icc hG _ _)) (fun z hz => ?_) hC.2.1 hC.2.2
  exact (closure_minimal (s := C) (t := {m : M | π (m : Pt) ∈ closure (F '' D')})
    (fun m hm => subset_closure (hC.subset hm).2) hWc) hz

/-- **§4: Property 3 as printed, uniform height** (`hagopian76_property3_components` with `c`
before `G`): no crossing component lies in a layer `d⁻¹(v)`, `v ∈ [0, 1]`. -/
theorem hagopian76_property3_components_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c →
      IsCrossRegion M π F c₁ D' →
      ∀ C : Set M, IsCrossingComponent G π F c₁ D' C → ∀ v : unitInterval, ¬ C ⊆ layer d v := by
  obtain ⟨c, hc, hc1, hP⟩ := property3_layer_all_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨c, hc, hc1, fun G d hG hEG hX0 c₁ D' hc₁ hR C hC v hCv =>
    hP G d hG hEG hX0 c₁ D' hc₁ hR v
    ⟨closure C, hC.isConnected.isPreconnected.closure,
      closure_minimal hCv (isClosed_layer hG.isCompact hG.2.1.1 v), fun z hz => ?_, hC.2.1,
      hC.2.2⟩⟩
  exact (closure_minimal (s := C) (t := {m : M | π (m : Pt) ∈ closure (F '' D')})
    (fun m hm => subset_closure (hC.subset hm).2)
    (isClosed_closure.preimage (hπ.continuous.comp continuous_subtype_val))) hz

/-- **§0.1: the members of `I` are nondegenerate** (uniform height): for every extension `G` and
every domain of height `c₁ ≤ c`, each `[x, y] ∈ I` has `x < y`. From Property 3 as printed
(`hagopian76_property3_components_unif`) and `crossingIntervals_nondegenerate_of`. -/
theorem crossingIntervals_nondegenerate (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c →
      IsCrossRegion M π F c₁ D' → ∀ p ∈ crossingIntervals d π F c₁ D', p.1 < p.2 := by
  obtain ⟨c, hc, hc1, hP⟩ := hagopian76_property3_components_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  exact ⟨c, hc, hc1, fun G d hG hEG hX0 c₁ D' hc₁ hR =>
    crossingIntervals_nondegenerate_of (hP G d hG hEG hX0 c₁ D' hc₁ hR)⟩

/-- **§2d.4: finitely many crossing components** (uniform height): `I` is finite
(`hagopian76_I_finite_unif`) and nondegenerate (`crossingIntervals_nondegenerate`), and a member of
`I` determines its component (`crossingComponents_finite_of`). -/
theorem crossing_components_finite (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c →
      IsCrossRegion M π F c₁ D' → {C : Set M | IsCrossingComponent G π F c₁ D' C}.Finite := by
  obtain ⟨c, hc, hc1, hfin⟩ := hagopian76_I_finite_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  obtain ⟨c', hc', hc'1, hnd⟩ := crossingIntervals_nondegenerate hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨min c c', lt_min hc hc', (min_le_left _ _).trans hc1,
    fun G d hG hEG hX0 c₁ D' hc₁ hR => ?_⟩
  exact crossingComponents_finite_of hG
    (hfin G d hG hEG hX0 c₁ D' (hc₁.trans (min_le_left _ _)) hR)
    (hnd G d hG hEG hX0 c₁ D' (hc₁.trans (min_le_right _ _)) hR)

/-- **§4: "`x₂ₙ = 1`" from `SepByCrossing`, uniform height** (`hagopian76_x2n_eq_one` with `c`
before `G`, `O`, `p`, `q`). -/
theorem hagopian76_x2n_eq_one_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → G ≠ E → ∀ (O : Set Pt) (p q : Pt), SepIn O (toPt G) p q →
      (∀ F', IsExtensionAway E (layer k 0) F' → SepIn O (toPt F') p q → F' ⊆ G → F' = G) →
      ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      SepByCrossing G π F c₁ D' O p q → LastIntervalReachesOne d π F c₁ D' := by
  obtain ⟨c, hc, hc1, hfin⟩ := hagopian76_I_finite_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  exact ⟨c, hc, hc1, fun G d hG hEG hX0 hne O p q hsep hirr c₁ D' hc₁ hR hSBC =>
    x2n_eq_one_of_cut hX hi hE hG hEG hX0 hne (hfin G d hG hEG hX0 c₁ D' hc₁ hR) hsep hirr
      (tailCutKeepsSep_of_sepByCrossing hG hSBC)⟩

/-- **§4: Property 3 in the thin-strip form, uniform height** (`hagopian76_property3` with `c`
before `G`). The proof is the original one, with the height of `property3_layer_unif`. -/
theorem hagopian76_property3_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, v < 1 → ¬ closure B ⊆ layer d v := by
  obtain ⟨c₃, hc₃, hc₃1, hP3⟩ := property3_layer_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG
    hP1
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
    fun G d hG hEG hX0 B hBc hBin hBl hBr v hv1 hBv => ?_⟩
  have hP3 := hP3 G d hG hEG hX0
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

end Uniform2

end HPC.Hagopian
