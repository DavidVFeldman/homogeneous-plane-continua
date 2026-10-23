import HPC.Hagopian.Hagopian76B

/-!
# Batch 158 skeleton: Hagopian 1976, D1 closed by lower semicontinuity; Lemmas 5–7; Moore 1962
# Theorem 28; the arc parametrization; Lemma 9

Save as `HPC/Hagopian/Hagopian76C.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76C` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report. When an item here
proves a statement left commented out in `Hagopian76A.lean` or `Hagopian76B.lean`, delete the
commented-out copy (this edit is allowed).

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345; Bing 1960 p. 215
(`doc/sources/bing1960.pdf`); Moore 1962 Theorem 28, p. 156 (`doc/sources/moore1962-excerpts.pdf`).

**The route to D1** (commission §2 A). For an extension `F` of `E` away from `X` with `s = max d|E`,
`0 < s < 1`, `W = d⁻¹(s)` is a layer of `F` that is not an end set, so the decomposition of `F` is
lower semicontinuous at `W` (`hagopian76_lemma5_interior` applied to `F`). The layers of `F` below
`s` are layers of `E` (`hagopian76_lemma4_layers'`), and they converge, as their parameters increase
to `s`, into the single layer of `E` through any limit point in `W` (upper semicontinuity of `E`).
So `W` lies in one layer of `E`; since `k⁻¹(1) ⊆ W`, that layer is `k⁻¹(1)`, and `W = k⁻¹(1)`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. D1, in the strong form -/

/-- **The far layer is the far end set.** For an extension `F` of `E` away from `X`, with
`s = max d|E`: either `F = E`, or `0 < s < 1` and `d⁻¹(s) = k⁻¹(1)`. Proof: the commission's route
(file header). -/
theorem hagopian76_far_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) :
    F = E ∨ ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ layer d s = layer k 1 := by
  sorry

/-- **`E` is an initial segment of every extension** (the strong form; the batch-156 rendering
`layerSet d (Icc 0 s) = E`, true in this setting though stronger than the printed sentence; used on
p. 347: "Let `e` be the point of `[0, 1]` such that `d⁻¹[[0, e]] = E`"). Every layer of `E` is a
layer of `F`. -/
theorem hagopian76_initial_segment (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ layerSet d (Icc 0 s) = E ∧
      ∀ t : unitInterval, ∃ u : unitInterval, layer k t = layer d u := by
  sorry

/-! ## B. Lemma 5 (restated from the commented-out copies in `Hagopian76B.lean`) -/

/-- **Lemma 5** (p. 341). At an end set `X` of `E`, take an extension of `E` away from `Z` (Lemma 4,
applied to the reversed map); `X` lies in a layer of it that is not an end set, at which it is lower
semicontinuous; the layers of `E` near `X` are its layers (item A). Hagopian's two-sided `F` is not
needed. Then `hagopian76_lemma5_of_ends`. -/
theorem hagopian76_lemma5 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsContinuousDecomp (Setoid.ker k) := by
  sorry

/-- **The continuum `F` of Hagopian's proof of Lemma 5** (p. 341), from item A: two extensions
meet exactly in `E`. Not needed for Lemma 5 by the route above; prove it if it is short, otherwise
record that it is not needed. -/
theorem hagopian76_two_sided_extension (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (F₁ F₂ : Set M) (d : (F₁ ∪ F₂ : Set M) → unitInterval),
      IsExtensionAway E (layer k 0) F₁ ∧ IsExtensionAway E (layer k 1) F₂ ∧
      IsMinimalAdmissible (F₁ ∪ F₂) d ∧ Disjoint (layer d 0 ∪ layer d 1) E := by
  sorry

/-! ## C, D. Lemma 6, the unnumbered claims, Lemma 7 (restated from `Hagopian76B.lean`) -/

/-- **Lemma 6, the step "`Cl R(X, E) = Cl R(E)`"** (p. 343). -/
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

/-- **Lemma 7** (p. 343). -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry

end Section2

/-! ## E. Moore 1962 Theorem 28 -/

/-- **Moore 1962, Theorem 28** (p. 156). "If `D` is a simple domain and each of the two mutually
exclusive continua `H` and `K` is a subset of `D` [read: of `D ∪ J`] and each of them intersects
`J`, the boundary of `D`, then no pair of points of `H` separates two points of `K` from each other
on `J`." Here `D` is the bounded complementary domain of the simple closed curve `J`. Compare the
crossing-continua results of batch 151 (`sector_cyclic_order`). -/
theorem moore62_theorem28 {J D H K : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J) (hH : Fold.Q78.IsContinuum H)
    (hK : Fold.Q78.IsContinuum K) (hHK : Disjoint H K) (hHD : H ⊆ D ∪ J) (hKD : K ⊆ D ∪ J)
    {a b c f : Pt} (ha : a ∈ H ∩ J) (hb : b ∈ H ∩ J) (hc : c ∈ K ∩ J) (hf : f ∈ K ∩ J) (hab : a ≠ b) :
    connectedComponentIn (J \ {a, b}) c = connectedComponentIn (J \ {a, b}) f := by
  sorry

/-! ## F. The arc `π[E]` parametrized; decomposable accessibility; Lemma 9 -/

section Lemma9

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **`exists_quotient_plane` with the parametrization** `γ t = π(k⁻¹(t))` (report 157, §5). -/
theorem exists_quotient_plane' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (π : Pt → Pt) (γ : unitInterval → Pt), IsQuotientMap π ∧
      (∀ p q, π p = π q ↔ layerSetoid k p q) ∧ IsEmbedding γ ∧
      (∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) ∧ range γ = π '' toPt E := by
  sorry

/-- **Abutting on the same side** (Bing 1960, p. 215: "`cd` and `ef` are said to abut on opposite
sides of `ab` if there is a homeomorphism of `E²` onto itself that takes `ab` onto a horizontal
segment and `cd`, `ef` onto vertical segments which lie except for their points of contact with
`ab` on opposite sides of the line containing `ab`"), the same-side form. The shape is the one
proposed in report 157 §5. -/
def AbutSameSide (α C₁ C₂ : Set Pt) : Prop :=
  ∃ (φ : Pt ≃ₜ Pt) (a b x₁ x₂ h₁ h₂ : ℝ), a < x₁ ∧ x₁ < b ∧ a < x₂ ∧ x₂ < b ∧ 0 < h₁ ∧ 0 < h₂ ∧
    φ '' α = Icc a b ×ˢ {0} ∧ φ '' C₁ = {x₁} ×ˢ Icc 0 h₁ ∧ φ '' C₂ = {x₂} ×ˢ Icc 0 h₂

/-- **Decomposably accessible from a side** (p. 344): "there exist arc segments `A` and `B` in
`R² − π[M]` such that (1) `π[U] ∈ Cl A`, (2) `π[Y] ∈ Cl B`, and (3) `Cl A` and `Cl B` abut on the
same side of the arc `π[E]` in `R²` [2, p. 215]". With `γ` the parametrization of `π[E]`. -/
def DecompAccessible (πM : Set Pt) (γ : unitInterval → Pt) (u y : unitInterval) : Prop :=
  0 < u ∧ u < 1 ∧ 0 < y ∧ y < 1 ∧ u ≠ y ∧
    ∃ (A B : Set Pt) (a₀ b₀ : Pt), TArc a₀ (γ u) (closure A) ∧ TArc b₀ (γ y) (closure B) ∧
      A = closure A \ {γ u} ∧ B = closure B \ {γ y} ∧ Disjoint A πM ∧ Disjoint B πM ∧
      AbutSameSide (range γ) (closure A) (closure B)

/-- **Lemma 9** (p. 344). "Let `U` and `Y` be elements of the decomposition of `E` that are not end
sets. If `Y` is accessible from `R² − M`, then `U` and `Y` are decomposably accessible from a side of
`E`." For any `π`, `γ` as in `exists_quotient_plane'`. -/
theorem hagopian76_lemma9 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {u y : unitInterval} (hu0 : 0 < u) (hu1 : u < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (huy : u ≠ y)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    DecompAccessible (π '' M) γ u y := by
  sorry

end Lemma9

end HPC.Hagopian
