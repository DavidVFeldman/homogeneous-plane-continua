import HPC.Hagopian.Hagopian75

/-!
# Batch 156: the definitions of the skeleton `Hagopian76A.lean`

The definitions of the batch-156 skeleton (p. 340 of Hagopian 1976) and the statement
`Hagopian76Thm1`, verbatim, split off so that the supporting files `H76*.lean` can use them.
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

/-- **Hagopian 1976, Theorem 1** (p. 345), as a statement: "If `M` is an indecomposable homogeneous
continuum in `R²`, then `M` is hereditarily indecomposable." (Proved in later batches.) -/
def Hagopian76Thm1 : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M →
    ¬ IsDecomposableSpace M → IsHereditarilyIndecomposable (univ : Set M)

end HPC.Hagopian
