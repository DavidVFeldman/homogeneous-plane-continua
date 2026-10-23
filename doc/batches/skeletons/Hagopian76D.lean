import HPC.Hagopian.Hagopian76C

/-!
# Batch 159 skeleton: Hagopian 1976, Lemma 6 and the unnumbered claims, Lemma 7; the plane
# Schoenflies theorem and a two-sided collar of an arc; Lemma 8 with prescribed caps; Lemma 9

Save as `HPC/Hagopian/Hagopian76D.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76D` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report. When an item here proves
a statement left commented out in `Hagopian76C.lean`, delete the commented-out copy (allowed).

Sources: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345; Bing 1960 p. 215
(`doc/sources/bing1960.pdf`); Moore 1919 (`m19_schoenflies_boundary_proof`, `HPC/Moore/M19GBoundary.lean`);
the plane as a model of Moore's axioms (`mooreDecomp_ptSetoid`, `HPC/Jones/Jones55T2A.lean`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Lemma 6 and the unnumbered claims; B. Lemma 7 (restated from `Hagopian76C.lean`) -/

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

/-! ## C. Plane topology: Schoenflies, and a two-sided collar of an arc -/

/-- **The Schoenflies theorem in the plane, with prescribed boundary.** A simple closed curve `J`
of the plane, with its bounded complementary domain `D`, is the image of the boundary of the square
under an embedding of the closed square onto `J ∪ D` that restricts to a given parametrization of
`J` (as four arcs). From `m19_schoenflies_boundary_proof`, transported to `Pt` through the plane
model of Moore's axioms (`mooreDecomp_ptSetoid`, `spaceRestricted_topology`). Choose the exact
shape; the one below is a suggestion. -/
theorem plane_schoenflies {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J)
    {φ : unitInterval → Pt} (hφ : IsEmbedding φ) (hφJ : range φ ⊆ J) :
    ∃ f : unitInterval × unitInterval → Pt, IsEmbedding f ∧ range f = J ∪ D ∧
      (∀ t, f (t, 0) = φ t) ∧ f '' {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1} = D := by
  sorry

/-- A **two-sided collar** of the arc `γ`: an embedding `F` of `[0, 1] × [−1, 1]` into the plane with
`F(t, 0) = γ t` and `F` of the open rectangle open. In its coordinates `γ` is the horizontal segment
of Hagopian's "we assume without loss of generality that `π[E]` is lying on a horizontal line"
(pp. 345, 346). -/
def IsCollar (γ : unitInterval → Pt) (F : ℝ × ℝ → Pt) : Prop :=
  IsEmbedding ((Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1).restrict F) ∧
    (∀ t : unitInterval, F ((t : ℝ), 0) = γ t) ∧ IsOpen (F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1))

/-- **Every arc in the plane has a two-sided collar.** Route: join the end points of `γ` by two arcs
`β`, `β′` meeting `γ` and each other only at the end points, on the two sides (accessibility,
`accessible_of_cyclic`; the θ-curve lemmas of batches 153–154); apply `plane_schoenflies` to the
two simple closed curves `γ ∪ β`, `γ ∪ β′`, with the same parametrization `γ` of their common side,
and glue. -/
theorem exists_collar {γ : unitInterval → Pt} (hγ : IsEmbedding γ) : ∃ F, IsCollar γ F := by
  sorry

/-- **Decomposably accessible from a side** (p. 344), in collar form. Two layers `k⁻¹(u)`, `k⁻¹(y)`
(not end sets, `u ≠ y`) are decomposably accessible from a side if, for some collar `F` of `γ` and
some side `σ = ±1`, the vertical segments over `γ u` and `γ y` on that side, minus their feet, miss
`π[M]`. This replaces `DecompAccessible` (batch 158), whose `AbutSameSide` asks for a homeomorphism
of the whole plane; the two agree given Schoenflies (Bing's definition, p. 215, straightens the arc
and the two abutting arcs simultaneously). Record the comparison. -/
def DecompAccessibleC (πM : Set Pt) (γ : unitInterval → Pt) (u y : unitInterval) : Prop :=
  0 < u ∧ u < 1 ∧ 0 < y ∧ y < 1 ∧ u ≠ y ∧
    ∃ (F : ℝ × ℝ → Pt) (σ h₁ h₂ : ℝ), IsCollar γ F ∧ (σ = 1 ∨ σ = -1) ∧ 0 < h₁ ∧ h₁ ≤ 1 ∧
      0 < h₂ ∧ h₂ ≤ 1 ∧
      Disjoint (F '' ((fun r => ((u : ℝ), σ * r)) '' Ioc 0 h₁)) πM ∧
      Disjoint (F '' ((fun r => ((y : ℝ), σ * r)) '' Ioc 0 h₂)) πM

/-! ## D. Lemma 8 with prescribed caps; E. Lemma 9 -/

section Lemma9

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Lemma 8 with prescribed caps** (p. 346: "Using the method described in the proof of Lemma 8
… (Here the open sets `A` and `B` in the proof of Lemma 8 are in `G₁ − G₂` and `G₁₁ − G₁₀`
respectively.)"). *Shape left to you*: what Property 1 (batch 160) and Lemma 9 need from the
refinement `Lᵢ = C ∩ Gᵢ` (`1 < i < n`), `L₁ = G₁`, `Lₙ = Gₙ`, for given open `A ⊆ G₁`, `B ⊆ Gₙ`
with `E` a component of `M − (A ∪ B)`. -/
theorem hagopian76_lemma8_caps : True := by
  sorry

/-- **Lemma 9** (p. 344), collar form. "Let `U` and `Y` be elements of the decomposition of `E` that
are not end sets. If `Y` is accessible from `R² − M`, then `U` and `Y` are decomposably accessible
from a side of `E`." -/
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
