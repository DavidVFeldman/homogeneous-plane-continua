import HPC.Hagopian.Hagopian75

/-!
# Batch 156 skeleton: Hagopian 1976, §2 (Lemmas 2–8) and the consequences of Theorem 1

Save as `HPC/Hagopian/Hagopian76A.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76A` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report.

Source: C. L. Hagopian, *Indecomposable homogeneous plane continua are hereditarily
indecomposable*, Trans. AMS 224 (1976), 339–350 (`doc/sources/hagopian1976.pdf`), read from page
images at 200 dpi. Here `[5]` is Hagopian 1975 (`HPC/Hagopian/Hagopian75.lean`) and `[14]` is
Thomas 1966 (not in hand).

§2 (p. 340): "In this section `M` is an indecomposable homogeneous continuum in `R²` and `E` is a
type A′ subcontinuum of `M`. Let `k : E → [0, 1]` be the quotient map associated with the minimal
admissible decomposition of `E` [5, Lemma 3]. Hereafter, we shall refer to this decomposition as
simply *the decomposition* of `E`." In the skeleton, "the decomposition" is an admissible map whose
layers have void interior (`IsMinimalAdmissible`); by `hagopian75_lemma3_unique` its layers are
determined by `E`.

Lemma 9 and Theorem 1 (the quotient `R²/S`, decomposable accessibility, Properties 1–4) are for
batch 157.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! ## Definitions (p. 340) -/

section Defs

variable {X : Type*} [MetricSpace X]

/-- "The decomposition" of a type A′ continuum: an admissible map with layers of void interior, on
a continuum irreducible between two points. -/
def IsMinimalAdmissible (E : Set X) (k : E → unitInterval) : Prop :=
  (∃ a b, IsIrreducibleBetween E a b) ∧ IsAdmissibleMap E k ∧ ∀ t, interior (k ⁻¹' {t}) = ∅

/-- The union of the layers over a set of parameters, as a subset of the ambient space. -/
def layerSet {E : Set X} (k : E → unitInterval) (A : Set unitInterval) : Set X :=
  Subtype.val '' (k ⁻¹' A)

/-- `F` is an **extension of `E` away from `X₀`** (p. 340): "a continuum of type A′ that contains
`E` and has `X₀` as an end set". The end set is normalized to the layer over `0`. -/
def IsExtensionAway (E X₀ F : Set X) : Prop :=
  E ⊆ F ∧ ∃ d : F → unitInterval, IsMinimalAdmissible F d ∧ layer d 0 = X₀

/-- `R(X₀, E)`: the union of all extensions of `E` away from `X₀`. -/
def extUnion (E X₀ : Set X) : Set X := ⋃₀ {F | IsExtensionAway E X₀ F}

/-- `R(E) = R(X, E) ∪ R(Z, E)`, with `X = k⁻¹(0)` and `Z = k⁻¹(1)` the end sets of `E`. -/
def Rset {E : Set X} (k : E → unitInterval) : Set X :=
  extUnion E (layer k 0) ∪ extUnion E (layer k 1)

/-- A continuum **essential to `R(E)`** (p. 343): a continuum in `R(E)` "that intersects more than
one element of the decomposition of some extension of `E`". -/
def IsEssential {E : Set X} (k : E → unitInterval) (H : Set X) : Prop :=
  H ⊆ Rset k ∧ Fold.Q78.IsContinuum H ∧
    ∃ (F : Set X) (d : F → unitInterval), E ⊆ F ∧ IsMinimalAdmissible F d ∧
      (layer d 0 = layer k 0 ∨ layer d 0 = layer k 1) ∧
      ∃ t₁ t₂, t₁ ≠ t₂ ∧ (H ∩ layer d t₁).Nonempty ∧ (H ∩ layer d t₂).Nonempty

end Defs

/-! ### Chains in the plane (p. 340) -/

section Chains

variable {M : Set Pt}

/-- A subset of `M` as a subset of the plane. -/
def toPt (A : Set M) : Set Pt := Subtype.val '' A

/-- A *chain* in `R²` (p. 339): open sets `G₀, …, Gₙ` with `Gᵢ ∩ Gⱼ ≠ ∅` iff `|i − j| ≤ 1`. -/
structure IsPlaneChain {n : ℕ} (G : Fin (n + 1) → Set Pt) : Prop where
  isOpen : ∀ i, IsOpen (G i)
  meets : ∀ i j : Fin (n + 1), (G i ∩ G j).Nonempty ↔ (i : ℕ) ≤ j + 1 ∧ (j : ℕ) ≤ i + 1

/-- The chain `G` **follows** `E` (p. 340): it covers `E`, and
(1) `k⁻¹(0) ⊂ G₁` and `k⁻¹(1) ⊂ Gₙ`;
(2) each element of the decomposition of `E` lies in an element of `G`;
(3) if `0 ≤ r < s ≤ 1` and `k⁻¹(r) ∪ k⁻¹(s)` is contained in an element `Gᵢ` of `G`, then the union
of all elements of `G` that intersect `Gᵢ` contains `k⁻¹[[r, s]]`. -/
def Follows {n : ℕ} (G : Fin (n + 1) → Set Pt) {E : Set M} (k : E → unitInterval) : Prop :=
  toPt E ⊆ ⋃ i, G i ∧ toPt (layer k 0) ⊆ G 0 ∧ toPt (layer k 1) ⊆ G (Fin.last n) ∧
    (∀ t, ∃ i, toPt (layer k t) ⊆ G i) ∧
    ∀ r s : unitInterval, r < s → ∀ i, toPt (layer k r ∪ layer k s) ⊆ G i →
      toPt (layerSet k (Icc r s)) ⊆ ⋃ j ∈ {j | (G j ∩ G i).Nonempty}, G j

/-- The chain `G` is **free relative to `M`** (p. 340): `M ∩ Bd (St G) ⊂ M ∩ Bd (G₁ ∪ Gₙ)`. -/
def IsFree (M : Set Pt) {n : ℕ} (G : Fin (n + 1) → Set Pt) : Prop :=
  M ∩ frontier (⋃ i, G i) ⊆ frontier (G 0 ∪ G (Fin.last n))

/-- `L` is an **ordered refinement** of `G` (p. 340): a chain with `Lᵢ ⊂ Gᵢ` for each `i`. -/
def IsOrderedRefinement {n : ℕ} (L G : Fin (n + 1) → Set Pt) : Prop :=
  IsPlaneChain L ∧ ∀ i, L i ⊆ G i

end Chains

/-! ## §2. Lemmas 2–8 -/

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Lemma 2** (p. 340). "Suppose `ε` is a given positive number and `x` is a point of `M`. Then
`{y ∈ M: an ε-homeomorphism of M onto M takes x to y}` is an open subset of `M` that contains `x`
[5, Lemma 4 (proof)]." -/
theorem hagopian76_lemma2 (hX : IsHomogeneous M) {ε : ℝ} (hε : 0 < ε) (x : M) :
    IsOpen {y : M | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε} ∧
      x ∈ {y : M | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε} := by
  sorry

/-- **End sets** (p. 340): "No proper subcontinuum of `E` intersects both `X` and `Z` [14, Theorem
8, p. 14]." (`admissible_end_sets'`, batch 155, in this setting.) -/
theorem hagopian76_end_sets {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {K : Set M} (hKE : K ⊆ E) (hK : Fold.Q78.IsContinuum K) (h0 : (K ∩ layer k 0).Nonempty)
    (h1 : (K ∩ layer k 1).Nonempty) : K = E := by
  sorry

/-- **Lemma 3** (p. 340). "Let `Y` be an element of the decomposition of `E` distinct from the end
sets `X` and `Z` of `E`. Let `F` be a type A′ subcontinuum of `M` with end sets `T` and `V`, and let
`U` be an element of the decomposition of `F` distinct from `T` and `V`. Suppose `h` is a
homeomorphism of `M` onto `M` such that `U ∩ h[Y] ≠ ∅` and `U ∩ h[X ∪ Z] = ∅ = h[Y] ∩ (T ∪ V)`.
Then `h[Y] = U`." Proof: "This lemma follows from the argument presented in paragraphs 9 through 11
in the proof of Theorem 1 of [5]." The printed hypotheses carry no `ε`, unlike
`hagopian75_layer_invariant`; record what replaces it. -/
theorem hagopian76_lemma3 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E F : Set M}
    {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) {s u : unitInterval} (hs0 : 0 < s) (hs1 : s < 1) (hu0 : 0 < u)
    (hu1 : u < 1) (h : M ≃ₜ M) (h1 : (layer d u ∩ h '' layer k s).Nonempty)
    (h2 : Disjoint (layer d u) (h '' (layer k 0 ∪ layer k 1)))
    (h3 : Disjoint (h '' layer k s) (layer d 0 ∪ layer d 1)) :
    h '' layer k s = layer d u := by
  sorry

/-- **Lemma 4, first paragraph** (p. 341). "There exists a positive number `s` such that
`d[E] = [0, s]`. Since `F` is irreducible, for each positive number `r` less than `s`, the set
`d⁻¹(r)` is in `E`. Since the decompositions of `E` and `F` are minimal, each element of the
decomposition of `E` (except possibly `k⁻¹(1)`) is an element of the decomposition of `F`." -/
theorem hagopian76_lemma4_layers (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ layerSet d (Icc 0 s) = E ∧
      ∀ t : unitInterval, t ≠ 1 → ∃ u : unitInterval, layer k t = layer d u := by
  sorry

/-- **Lemma 4** (p. 340). "The collection `𝓕` of extensions of `E` away from the end set `X` is
linearly ordered by inclusion and does not have a maximal element." Proof (p. 341): "If `H` is an
element of `𝓕`, then `F ⊂ H` or `H ⊂ F`; for otherwise, the continuum `H ∩ d⁻¹[[s, 1]]` (Lemma 1)
would separate `F ∪ H` into three nonempty disjoint open sets"; and, for no maximal element, "it is
a proper subset of an element of `𝓕` that is contained in `F ∪ h⁻¹[F]` (Lemma 1)". -/
theorem hagopian76_lemma4 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsChain (· ⊆ ·) {F | IsExtensionAway E (layer k 0) F} ∧
      ∀ F ∈ {F | IsExtensionAway E (layer k 0) F},
        ∃ H ∈ {F | IsExtensionAway E (layer k 0) F}, F ⊂ H := by
  sorry

/-- **Lemma 4, the countable form used in Lemma 6** (p. 342). "Since `M` is second countable, there
exists a monotone strictly increasing sequence `{Fᵢ}` of elements of `𝓕` such that
`R(X, E) = ⋃ Fᵢ` (Lemma 4)." -/
theorem hagopian76_lemma4_seq (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ Fs : ℕ → Set M, StrictMono Fs ∧ (∀ i, IsExtensionAway E (layer k 0) (Fs i)) ∧
      extUnion E (layer k 0) = ⋃ i, Fs i := by
  sorry

/-- **Lemma 5** (p. 341). "The decomposition of `E` is continuous." -/
theorem hagopian76_lemma5 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsContinuousDecomp (Setoid.ker k) := by
  sorry

/-- **Lemma 6, the step "`Cl R(X, E) = Cl R(E)`"** (p. 343): "We complete this proof by showing that
`Cl R(X, E) = Cl R(E)` … (see the second paragraph in the proof of Theorem 1 of [5])." -/
theorem hagopian76_closure_extUnion (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 0)) = closure (Rset k) := by
  sorry

/-- **Lemma 6** (p. 341). "The continuum `Cl R(E)` is indecomposable." -/
theorem hagopian76_lemma6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (Rset k)) := by
  sorry

/-- **"Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`"** (p. 343, unnumbered). -/
theorem hagopian76_Rset_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : M}
    (hx : x ∈ Rset k) : Rset k = HPC.composant (closure (Rset k)) x := by
  sorry

/-- **"Note that every continuum essential to `R(E)` is of type A′ (Lemma 5)"** (p. 343,
unnumbered). -/
theorem hagopian76_essential_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsEssential k H) : IsTypeA' H := by
  sorry

/-- **Lemma 7** (p. 343). "For each positive number `ε`, there exists a positive number `δ` such
that if `h` is a `δ`-homeomorphism of `M` onto `M`, then `h[R(E)]` has the following property. If
`H` is a continuum essential to `h[R(E)]` with end sets `T` and `V` such that `ρ(T, V) < δ` and if
there exists an element `U` of the decomposition of `H` such that `ρ(T, U) > ε`, then each point of
`R(E)` is within `ε` of `H`." Shape: "essential to `h[R(E)]`" is read as `h⁻¹[H]` essential to
`R(E)`; `ρ` between sets is the infimum distance (attained, the sets being compact). -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry

/-- **Lemma 8** (p. 344). "Every chain in `R²` that follows `E` has an ordered refinement that
follows `E` and is free relative to `M`." Proof: "Since `M` is atriodic, there exist open sets `A`
and `B` in `G₁` and `Gₙ`, respectively, such that `E` is a component of `M − (A ∪ B)`." Then Moore
1962 Theorem 44, p. 15, gives disjoint open `C ⊃ E` and `D ⊃ M − St G` with
`C ∪ D ⊃ M − (A ∪ B)`, and `L₁ = G₁`, `Lₙ = Gₙ`, `Lᵢ = C ∩ Gᵢ`. -/
theorem hagopian76_lemma8 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {n : ℕ} (G : Fin (n + 1) → Set Pt)
    (hG : IsPlaneChain G) (hGE : Follows G k) :
    ∃ L : Fin (n + 1) → Set Pt, IsOrderedRefinement L G ∧ Follows L k ∧ IsFree M L := by
  sorry

end Section2

/-! ## Theorem 1 as a statement, and its consequences -/

/-- **Hagopian 1976, Theorem 1** (p. 345), as a statement: "If `M` is an indecomposable homogeneous
continuum in `R²`, then `M` is hereditarily indecomposable." (Proved in later batches.) -/
def Hagopian76Thm1 : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M →
    ¬ IsDecomposableSpace M → IsHereditarilyIndecomposable (univ : Set M)

section Consequences

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Hagopian 1976, Theorem 2** (p. 349). "Every homogeneous plane continuum that does not separate
the plane is hereditarily indecomposable." Proof: "Since every homogeneous nonseparating plane
continuum is indecomposable [4], [6], this theorem follows immediately from Theorem 1." Here [4] is
Gordh 1975 and [6] Jones 1951; the repository route is `jones55_two_domains'` (a decomposable
homogeneous plane continuum has two complementary domains). -/
theorem hagopian76_theorem2 (h1 : Hagopian76Thm1) (hX : IsHomogeneous M)
    (hns : ¬ SeparatesPlane M) : IsHereditarilyIndecomposable (univ : Set M) := by
  sorry

/-- **Hagopian 1975, Corollary** (p. 39). "If `M` is a homogeneous indecomposable plane continuum,
then no subcontinuum of `M` is hereditarily decomposable." (Nondegenerate subcontinua: Hagopian's
continua are nondegenerate.) -/
theorem hagopian75_corollary (h1 : Hagopian76Thm1) (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {H : Set M} (hH : Fold.Q78.IsContinuum H) (hnd : H.Nontrivial) :
    ¬ IsHereditarilyDecomposable H := by
  sorry

/-- **Hagopian 1975, Theorem 1** (p. 38), as printed: "Suppose `M` is a homogeneous indecomposable
plane continuum and `A` is a decomposable subcontinuum of `M`. Then `A` contains a homogeneous
indecomposable continuum." From Theorem 1 of 1976 the hypothesis is impossible. -/
theorem hagopian75_theorem1 (h1 : Hagopian76Thm1) (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {A : Set M} (hA : Fold.Q78.IsContinuum A)
    (hAd : ¬ Fold.Q78.IsIndecomposable A) :
    ∃ Y ⊆ A, Fold.Q78.IsContinuum Y ∧ Y.Nontrivial ∧ IsHomogeneous Y ∧
      Fold.Q78.IsIndecomposable Y := by
  sorry

/-- **Hagopian 1975, Theorem 2** (p. 39). "The simple closed curve is the only homogeneous plane
continuum that has a hereditarily decomposable subcontinuum." Proof (p. 40): the Corollary, Jones's
decomposition [Jones 1955, Theorem 2], and "if `H` meets more than one element of `G`, then `H`
contains an element of `G` [Jones 1955, Theorem 1]" (`jones55_c`). -/
theorem hagopian75_theorem2 (h1 : Hagopian76Thm1) (hX : IsHomogeneous M) {H : Set M}
    (hH : Fold.Q78.IsContinuum H) (hnd : H.Nontrivial) (hHd : IsHereditarilyDecomposable H) :
    Nonempty (M ≃ₜ Circle) := by
  sorry

/-- **Bing 1960 for plane continua** (Canad. J. Math. 12, title theorem): "A simple closed curve is
the only homogeneous bounded plane continuum that contains an arc." An arc is hereditarily
decomposable, so this is `hagopian75_theorem2`. -/
theorem bing60_plane (h1 : Hagopian76Thm1) (hX : IsHomogeneous M) {α : Set M}
    (hα : Nonempty (α ≃ₜ unitInterval)) : Nonempty (M ≃ₜ Circle) := by
  sorry

end Consequences

end HPC.Hagopian
