import HPC.Hagopian.Hagopian76A

/-!
# Batch 157 skeleton: Hagopian 1976, §2 continued (the first paragraph of Lemma 4; Lemmas 5–7)
# and the set-up of Theorem 1 (the quotient `R²/S`, the arc `π[E]`, accessibility)

Save as `HPC/Hagopian/Hagopian76B.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76B` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report. When an item here is
proved, delete its commented-out copy in `Hagopian76A.lean` (this edit is allowed).

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345, read from page images at
200 dpi. Batch 156 left D1, E, F, G open (`OPEN.md`).

**Standing remark** (batch 156): under the section hypotheses no type A′ `E` exists (Theorem 1), so
no statement here can be refuted inside a homogeneous indecomposable `M`; a statement can only be
proved, or shown not to follow from the hypotheses actually used (by a model without homogeneity).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## D1. The first paragraph of Lemma 4 -/

/-- **Lemma 4, first paragraph, as printed** (p. 341). "There exists a positive number `s` such that
`d[E] = [0, s]`. Since `F` is irreducible, for each positive number `r` less than `s`, the set
`d⁻¹(r)` is in `E`. Since the decompositions of `E` and `F` are minimal, each element of the
decomposition of `E` (except possibly `k⁻¹(1)`) is an element of the decomposition of `F`."

*Re-rendered.* The batch-156 skeleton wrote "`d[E] = [0, s]`" as `layerSet d (Icc 0 s) = E`, which
is stronger than the printed sentence (it also asks `d⁻¹(s) ⊆ E`); the half-bar model of `OPEN.md`
D1 separates the two. Here the first two sentences are rendered as printed (`d[E] = [0, s]`, and
`d⁻¹(r) ⊆ E` for `r < s`); only the third, the last clause, goes beyond
`hagopian76_lemma4_layers'`. -/
theorem hagopian76_lemma4_layers (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ (∀ r, r < s → layer d r ⊆ E) ∧ E ⊆ layerSet d (Icc 0 s) ∧
      (layer d s ∩ E).Nonempty ∧
      ∀ t : unitInterval, t ≠ 1 → ∃ u : unitInterval, layer k t = layer d u := by
  sorry

/-- **D1, the configuration to exclude** (the only way the printed paragraph can fail, by
`hagopian76_lemma4_layers'`): with `s = max d|E`, a layer `k⁻¹(t)`, `t < 1`, lying in `d⁻¹(s)`.
Equivalently `d⁻¹(s) ∩ E = k⁻¹[[t₀, 1]]` with `t₀ < 1`: an interval of layers of `E` with interior
in `E`, swallowed by one nowhere dense layer of `F`. -/
theorem hagopian76_no_swallowed_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) {t u : unitInterval}
    (ht : t < 1) (hsub : layer k t ⊆ layer d u) (hZ : (layer k 1 ∩ layer d u).Nonempty) : False := by
  sorry

/-! ## E. Lemma 5 -/

/-- **Lemma 5 at the layers other than the end sets.** Proposed route, without the continuum `F` of
Hagopian's proof: Lemma 3 with `F := E`. For `y ∈ Y = k⁻¹(c)`, `0 < c < 1`, `yᵢ ∈ Yᵢ → y` and
`p ∈ Y ∖ limsup Yᵢ`, take `η > 0` with `ρ(p, Yᵢ) ≥ η` for large `i` and `ε < η` below
`ρ(k⁻¹[[c − γ, c + γ]], X ∪ Z)`; Lemma 2 gives `ε`-homeomorphisms `h` with `h(y) = yᵢ` for large `i`;
Lemma 3 (`T = X`, `V = Z`, `U = Yᵢ`) gives `h[Y] = Yᵢ`, so `h(p) ∈ Yᵢ`, against `ρ(p, Yᵢ) ≥ η`. -/
theorem hagopian76_lemma5_interior (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k) (x : E)
    (hx0 : 0 < k x) (hx1 : k x < 1) : LSCAt (Setoid.ker k) x := by
  sorry

/-- **Lemma 5** (p. 341), restated verbatim. "The decomposition of `E` is continuous." The end sets
are where Hagopian's `F` (an extension on each side, end sets missing `E`) is needed, and where the
D1 configuration intervenes. -/
theorem hagopian76_lemma5 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsContinuousDecomp (Setoid.ker k) := by
  sorry

/-- **The continuum `F` of Lemma 5** (p. 341): "There exists a type A′ continuum `F` in `R(E)` that
is the union of two extensions of `E` such that the end sets `T` and `V` of `F` miss `E` (Lemma
4)." -/
theorem hagopian76_two_sided_extension (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (F₁ F₂ : Set M) (d : (F₁ ∪ F₂ : Set M) → unitInterval),
      IsExtensionAway E (layer k 0) F₁ ∧ IsExtensionAway E (layer k 1) F₂ ∧
      IsMinimalAdmissible (F₁ ∪ F₂) d ∧ Disjoint (layer d 0 ∪ layer d 1) E := by
  sorry

/-! ## F. Lemma 6 and the unnumbered claims (restated verbatim from `Hagopian76A.lean`) -/

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

/-! ## G. Lemma 7 (restated verbatim from `Hagopian76A.lean`) -/

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

/-! ## H. The set-up of Theorem 1 (pp. 344–345) -/

section Setup

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **"Since `M` is indecomposable and homogeneous, no proper subcontinuum of `M` separates `R²` [5,
Lemma 1 (second paragraph of proof)]"** (p. 344). To be extracted from the proof of
`hereditarilyUnicoherent_of_homogeneous_indecomposable` (`H75Lemma1.lean`). -/
theorem no_proper_subcontinuum_separates (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {K : Set M} (hK : Fold.Q78.IsContinuum K) (hKM : K ≠ univ) : ¬ SeparatesPlane (toPt K) := by
  sorry

open Classical in
/-- The key of the relation `S` (p. 344): a point of `E` goes to the parameter of its layer, a point
off `E` to itself. -/
noncomputable def layerKey {E : Set M} (k : E → unitInterval) (p : Pt) : unitInterval ⊕ Pt :=
  if h : ∃ hM : p ∈ M, (⟨p, hM⟩ : M) ∈ E then Sum.inl (k ⟨⟨p, h.1⟩, h.2⟩) else Sum.inr p

/-- **The relation `S`** (p. 345): "the equivalence relation on `R²` that relates distinct points
`p` and `q` if and only if `{p, q}` is a subset of an element of the decomposition of `E`". -/
noncomputable def layerSetoid {E : Set M} (k : E → unitInterval) : Setoid Pt :=
  Setoid.ker (layerKey k)

/-- **`S` satisfies Moore 1925's hypotheses** (compact connected nonseparating elements, upper
semicontinuous in Moore's form). Upper semicontinuity follows from the continuity of `k` and the
compactness of `E`; Lemma 5 is not needed. -/
theorem layerSetoid_mooreDecomp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    HPC.Moore.MooreDecomp (layerSetoid k) := by
  sorry

/-- **"Hence we can assume that the quotient space `R²/S` is `R²` [12]"** (p. 344), and "the arc
`π[E]`" (p. 345): a quotient map `π` of the plane onto the plane whose fibres are the classes of
`S`, carrying `E` onto an arc. From `m25_theorem22`. -/
theorem exists_quotient_plane (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ π : Pt → Pt, IsQuotientMap π ∧ (∀ p q, π p = π q ↔ layerSetoid k p q) ∧
      Nonempty (π '' toPt E ≃ₜ unitInterval) := by
  sorry

/-- A point `p` of the plane is **accessible from the complement** of `M`: it is the end of an arc
meeting `M` only in `p`. -/
def IsAccessibleFrom (M : Set Pt) (p : Pt) : Prop :=
  ∃ (x : Pt) (C : Set Pt), TArc x p C ∧ C ∩ M = {p}

/-- **"Since `M` is homogeneous, we can assume without loss of generality that `k⁻¹[(0, 1)]` is
accessible from `R² − M`"** (p. 345): some type A′ subcontinuum (the image of `E` under a
homeomorphism of `M`) has an accessible point in an interior layer. Needs: some point of `M` is
accessible from `R² − M`. -/
theorem exists_accessible_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (E' : Set M) (k' : E' → unitInterval) (h : M ≃ₜ M), E' = h '' E ∧
      IsMinimalAdmissible E' k' ∧ ∃ p ∈ layerSet k' (Ioo 0 1), IsAccessibleFrom M (p : Pt) := by
  sorry

end Setup

end HPC.Hagopian
