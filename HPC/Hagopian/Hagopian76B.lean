import HPC.Hagopian.Hagopian76A
import HPC.Hagopian.H76D1
import HPC.Hagopian.H76Lemma5
import HPC.Hagopian.H76Setup

/-!
# Batch 157 skeleton: Hagopian 1976, §2 continued (the first paragraph of Lemma 4; Lemmas 5–7)
# and the set-up of Theorem 1 (the quotient `R²/S`, the arc `π[E]`, accessibility)

Batch 157 (`doc/batches/COMMISSION-batch157.md`; report `doc/batches/REPORT-batch157.md`). The
skeleton is kept as `doc/batches/skeletons/Hagopian76B.lean`. Supporting proofs are in
`H76SepInv.lean`, `H76NoSep.lean`, `H76D1.lean`, `H76Lemma5.lean`, `H76Setup.lean`; the definitions
of the set-up (`layerKey`, `layerSetoid`, `IsAccessibleFrom`) are moved, verbatim, to
`H76BDefs.lean`. Items that remain open are commented out (no `sorry`), each with an
`OPEN (batch 157)` note; their obstructions are in `OPEN.md`. Shape changes are recorded at the
statement and in the report.

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

-- `hagopian76_lemma4_layers` (re-rendered): proved in batch 158, `Hagopian76C.lean`.

-- `hagopian76_no_swallowed_layer`: proved in batch 158, `Hagopian76C.lean`.

omit [CompactSpace M] [ConnectedSpace M] in
/-- **D1 ⇐ no swallowed layer** (batch 157, item A: "they are equivalent up to bookkeeping;
confirm this"). If no layer `k⁻¹(t)`, `t < 1`, lies in a layer of `F` meeting `k⁻¹(1)`, the first
paragraph of Lemma 4 holds as printed (re-rendered form). Homogeneity is not used; the step
supplied is that `k⁻¹(1)` lies in `d⁻¹(s)` (otherwise `d⁻¹[[0, u]]`, `u < s`, would be a proper
subcontinuum of `E` meeting both end sets). -/
theorem hagopian76_lemma4_layers_of_no_swallowed {E F : Set M} {k : E → unitInterval}
    {d : F → unitInterval} (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d)
    (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0)
    (hns : ∀ t u : unitInterval, t < 1 → layer k t ⊆ layer d u →
      (layer k 1 ∩ layer d u).Nonempty → False) :
    ∃ s : unitInterval, 0 < s ∧ (∀ r, r < s → layer d r ⊆ E) ∧ E ⊆ layerSet d (Icc 0 s) ∧
      (layer d s ∩ E).Nonempty ∧
      ∀ t : unitInterval, t ≠ 1 → ∃ u : unitInterval, layer k t = layer d u :=
  lemma4_layers_of_no_swallowed hE hF hEF hX0 hns

omit [CompactSpace M] [ConnectedSpace M] in
/-- **D1 ⇒ no swallowed layer**: the last clause of the first paragraph of Lemma 4 excludes the
configuration of `hagopian76_no_swallowed_layer`. -/
theorem hagopian76_no_swallowed_of_lemma4_layers {E F : Set M} {k : E → unitInterval}
    {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hlay : ∀ t : unitInterval, t ≠ 1 → ∃ u : unitInterval, layer k t = layer d u)
    {t u : unitInterval} (ht : t < 1) (hsub : layer k t ⊆ layer d u)
    (hZ : (layer k 1 ∩ layer d u).Nonempty) : False :=
  no_swallowed_of_lemma4_layers hE hlay ht hsub hZ

/-! ## E. Lemma 5 -/

/-- **Lemma 5 at the layers other than the end sets.** Proposed route, without the continuum `F` of
Hagopian's proof: Lemma 3 with `F := E`. For `y ∈ Y = k⁻¹(c)`, `0 < c < 1`, `yᵢ ∈ Yᵢ → y` and
`p ∈ Y ∖ limsup Yᵢ`, take `η > 0` with `ρ(p, Yᵢ) ≥ η` for large `i` and `ε < η` below
`ρ(k⁻¹[[c − γ, c + γ]], X ∪ Z)`; Lemma 2 gives `ε`-homeomorphisms `h` with `h(y) = yᵢ` for large `i`;
Lemma 3 (`T = X`, `V = Z`, `U = Yᵢ`) gives `h[Y] = Yᵢ`, so `h(p) ∈ Yᵢ`, against `ρ(p, Yᵢ) ≥ η`.

*Proof* (`lemma5_interior_aux`, `H76Lemma5.lean`): the route checks, in neighbourhood form. The
neighbourhood `W` of `Y` is the set of points `z` with `k z ∈ (c − γ, c + γ)` reached from points of
`Y` by `ε`-homeomorphisms (open by Lemma 2); for `z = h(y')` Lemma 3 gives `h[Y] = k⁻¹(k z)`, and
`h(y)` is a point of the layer of `z` within `ε` of `y`. -/
theorem hagopian76_lemma5_interior (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k) (x : E)
    (hx0 : 0 < k x) (hx1 : k x < 1) : LSCAt (Setoid.ker k) x :=
  lemma5_interior_aux hX hi hE x hx0 hx1

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Lemma 5, upper semicontinuity** (Hagopian: "Since `A` is upper semicontinuous, `Y` contains
`L`"): the decomposition into the layers of a continuous map on a compact space is u.s.c. -/
theorem hagopian76_lemma5_usc {E : Set M} [CompactSpace E] {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) : IsUSCDecomp (Setoid.ker k) :=
  isUSCDecomp_ker hE.2.1.1

/-- **Lemma 5, reduced to the end sets.** The decomposition of `E` is continuous as soon as it is
lower semicontinuous at the points of the two end sets (`hagopian76_lemma5_interior` and
`hagopian76_lemma5_usc` do the rest). -/
theorem hagopian76_lemma5_of_ends (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hends : ∀ x, (k x = 0 ∨ k x = 1) → LSCAt (Setoid.ker k) x) :
    IsContinuousDecomp (Setoid.ker k) :=
  lemma5_of_ends_aux hX hi hE hends

-- `hagopian76_lemma5`: proved in batch 158, `Hagopian76C.lean`.

/- OPEN (batch 157): `hagopian76_two_sided_extension` — the natural argument (irreducibility of `F₁ ∪ F₂`, then Kuratowski and the 1975 ¶2 argument as in `ext_of_branch`) needs the tails `d₁⁻¹[[s₁, 1]]`, `d₂⁻¹[[s₂, 1]]` to meet `E` only in `Z`, `X` respectively, so that `F₁ ∩ F₂ = E`: D1 at both ends. Without it the tails may overlap inside `E`. See `OPEN.md`, batch 157, item B.

/-- **The continuum `F` of Lemma 5** (p. 341): "There exists a type A′ continuum `F` in `R(E)` that
is the union of two extensions of `E` such that the end sets `T` and `V` of `F` miss `E` (Lemma
4)." -/
theorem hagopian76_two_sided_extension (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (F₁ F₂ : Set M) (d : (F₁ ∪ F₂ : Set M) → unitInterval),
      IsExtensionAway E (layer k 0) F₁ ∧ IsExtensionAway E (layer k 1) F₂ ∧
      IsMinimalAdmissible (F₁ ∪ F₂) d ∧ Disjoint (layer d 0 ∪ layer d 1) E := by
  sorry
-/

/-! ## F. Lemma 6 and the unnumbered claims (restated verbatim from `Hagopian76A.lean`) -/

/- OPEN (batch 157): `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`, `hagopian76_essential_typeA'` — each uses Lemma 5 at the end sets (the decomposition of an extension `F` is continuous at its end sets and has the decomposition of `E` as a subcollection, the latter being D1). Steps 1–8 of Lemma 6 are checked in `doc/batches/REPORT-batch157.md` §1.C; not formalized. See `OPEN.md`, batch 157, item C.

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
-/

/-! ## G. Lemma 7 (restated verbatim from `Hagopian76A.lean`) -/

/- OPEN (batch 157): `hagopian76_lemma7` — uses Lemma 5 (the decompositions of essential continua) and Lemma 6 (the limit points `t`, `u`, `p` in `Cl R(E)`, and the essential continuum `F` of `fhᵢ[R(E)]`); blocked by items B and C. See `OPEN.md`, batch 157, item D.

/-- **Lemma 7** (p. 343). -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry
-/

end Section2

/-! ## H. The set-up of Theorem 1 (pp. 344–345) -/

section Setup

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **"Since `M` is indecomposable and homogeneous, no proper subcontinuum of `M` separates `R²` [5,
Lemma 1 (second paragraph of proof)]"** (p. 344). To be extracted from the proof of
`hereditarilyUnicoherent_of_homogeneous_indecomposable` (`H75Lemma1.lean`).

*Proof* (`no_proper_subcontinuum_separates_aux`, `H76NoSep.lean`): the 1975 argument, with one
supplied step. The copies `h[K]` of `K` in the composants of `M` need not be known to separate the
plane (that would be Borsuk's invariance theorem); it suffices that each contains a separating
continuum, which is `exists_separating_subcontinuum_of_homeomorph` (`H76SepInv.lean`: `z − p` has no
logarithm on a separating `K`, every nonvanishing map has one on a tree-like continuum, and Bing's
Theorem 6 makes a continuum without separating subcontinua tree-like). -/
theorem no_proper_subcontinuum_separates (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {K : Set M} (hK : Fold.Q78.IsContinuum K) (hKM : K ≠ univ) : ¬ SeparatesPlane (toPt K) :=
  no_proper_subcontinuum_separates_aux hX hi hK hKM

/-! `layerKey`, `layerSetoid` (the relation `S`, p. 345) and `IsAccessibleFrom` are in
`H76BDefs.lean`, verbatim. -/

/-- **`S` satisfies Moore 1925's hypotheses** (compact connected nonseparating elements, upper
semicontinuous in Moore's form). Upper semicontinuity follows from the continuity of `k` and the
compactness of `E`; Lemma 5 is not needed.

*Proof* (`layerSetoid_mooreDecomp_aux`, `H76Setup.lean`): the elements are the layers of `E` and the
points off `E`; the layers are proper subcontinua of `M`, so `no_proper_subcontinuum_separates`
applies; Moore's u.s.c. is `layer_usc` (a closed-map argument for `k`). -/
theorem layerSetoid_mooreDecomp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    HPC.Moore.MooreDecomp (layerSetoid k) :=
  layerSetoid_mooreDecomp_aux hX hi hE

/-- **"Hence we can assume that the quotient space `R²/S` is `R²` [12]"** (p. 344), and "the arc
`π[E]`" (p. 345): a quotient map `π` of the plane onto the plane whose fibres are the classes of
`S`, carrying `E` onto an arc. From `m25_theorem22`.

*Proof* (`exists_quotient_plane_aux`): `π` is the quotient map followed by the homeomorphism of
Moore 1925 Theorem 22; `t ↦ π(k⁻¹(t))` is continuous (`k` is a quotient map) and injective on the
compact `[0, 1]`, with image `π[E]`. -/
theorem exists_quotient_plane (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ π : Pt → Pt, IsQuotientMap π ∧ (∀ p q, π p = π q ↔ layerSetoid k p q) ∧
      Nonempty (π '' toPt E ≃ₜ unitInterval) :=
  exists_quotient_plane_aux hX hi hE

/-- **"Since `M` is homogeneous, we can assume without loss of generality that `k⁻¹[(0, 1)]` is
accessible from `R² − M`"** (p. 345): some type A′ subcontinuum (the image of `E` under a
homeomorphism of `M`) has an accessible point in an interior layer. Needs: some point of `M` is
accessible from `R² − M`.

*Proof* (`exists_accessible_typeA'_aux`, `H76Setup.lean`): a point `p` of `M` nearest to a point off
`M` is the end of a straight segment meeting `M` only in `p` (`exists_accessible_point`); a
homeomorphism `h` of `M` takes a point of `k⁻¹(1/2)` to `p`, and `h[E]` carries the transported map
(`exists_image_map`).

*Shape change:* the hypothesis `hi` (indecomposability) is dropped; only homogeneity is used. -/
theorem exists_accessible_typeA' (hX : IsHomogeneous M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) :
    ∃ (E' : Set M) (k' : E' → unitInterval) (h : M ≃ₜ M), E' = h '' E ∧
      IsMinimalAdmissible E' k' ∧ ∃ p ∈ layerSet k' (Ioo 0 1), IsAccessibleFrom M (p : Pt) :=
  exists_accessible_typeA'_aux hX hE

end Setup

end HPC.Hagopian
