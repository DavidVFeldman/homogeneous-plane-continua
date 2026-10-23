import HPC.Hagopian.Hagopian76D

/-!
# Batch 160 skeleton: Hagopian 1976, Lemma 6 (steps 1–8) and the unnumbered claims, Lemma 7;
# two-sided Schoenflies, the metric form of upper semicontinuity, Lemma 9

Save as `HPC/Hagopian/Hagopian76E.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76E` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report. When an item here proves
a statement left commented out in `Hagopian76D.lean`, delete the commented-out copy (allowed).

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345.

**Already in the repository** (report 159 §1.A, item 1, overlooked them):
* `hagopian76_lemma4_chain`: extensions away from `X` are linearly ordered by inclusion;
* `hagopian76_lemma4`: no maximal element;
* `hagopian76_lemma4_seq`: the strictly increasing sequence `{Fᵢ}` with `R(X, E) = ⋃ Fᵢ`;
* `hagopian76_initial_segment`: each smaller extension is an initial segment of each larger one,
  with its layers among the larger one's (apply it with `E := F`, since both have end set `X`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Lemma 6 -/

/-- **Lemma 6, first part** (pp. 342–343, steps 1–7): "First we prove that `Cl R(X, E)` is
indecomposable." Supporting lemmas for the steps are expected (commission §2 A). -/
theorem hagopian76_lemma6_X (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (extUnion E (layer k 0))) := by
  sorry

/-- **Lemma 6, the step "`Cl R(X, E) = Cl R(E)`"** (p. 343, step 8). -/
theorem hagopian76_closure_extUnion (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 0)) = closure (Rset k) := by
  sorry

/-- **Lemma 6** (p. 341). "The continuum `Cl R(E)` is indecomposable." -/
theorem hagopian76_lemma6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (Rset k)) := by
  sorry

/-- **"Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`"** (p. 343). -/
theorem hagopian76_Rset_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : M}
    (hx : x ∈ Rset k) : Rset k = HPC.composant (closure (Rset k)) x := by
  sorry

/-- **"Note that every continuum essential to `R(E)` is of type A′ (Lemma 5)"** (p. 343). -/
theorem hagopian76_essential_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsEssential k H) : IsTypeA' H := by
  sorry

/-! ## B. Lemma 7 -/

/-- **Lemma 7** (p. 343). -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry

/-! ## C. Upper semicontinuity in metric form -/

/-- **Layers near a layer are near it** (report 159 §5): upper semicontinuity of the decomposition
of `E` in metric form. -/
theorem layer_nbhd_small {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {ε : ℝ} (hε : 0 < ε) (s : unitInterval) :
    ∃ δ > 0, ∀ t : unitInterval, dist t s < δ →
      toPt (layer k t) ⊆ Metric.thickening ε (toPt (layer k s)) := by
  sorry

end Section2

/-! ## D. Two-sided Schoenflies -/

/-- **Schoenflies with two adjacent sides prescribed** (report 159 §5): bottom side on `φ`, left
side on `ψ`, the two arcs of `J` meeting only at their common first point. -/
theorem plane_schoenflies₂ {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J) {φ ψ : unitInterval → Pt}
    (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ) (hφJ : range φ ⊆ J) (hψJ : range ψ ⊆ J)
    (h0 : φ 0 = ψ 0) (hφψ : range φ ∩ range ψ = {φ 0}) :
    ∃ f : unitInterval × unitInterval → Pt, IsEmbedding f ∧ range f = J ∪ D ∧
      (∀ t, f (t, 0) = φ t) ∧ (∀ t, f (0, t) = ψ t) ∧
      f '' {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1} = D := by
  sorry

/-! ## E. Lemma 9 (restated from `Hagopian76D.lean`) -/

section Lemma9

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Lemma 9** (p. 344), collar form. -/
theorem hagopian76_lemma9 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {u y : unitInterval} (hu0 : 0 < u) (hu1 : u < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (huy : u ≠ y)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    DecompAccessibleC (π '' M) γ u y := by
  sorry

end Lemma9

end HPC.Hagopian
