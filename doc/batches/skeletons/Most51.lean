import HPC.Plane.Monotone51
import Mathlib.Topology.MetricSpace.Closeds

/-!
# Bing, *Concerning hereditarily indecomposable continua*, §3: most compact continua are pseudo-arcs

Skeleton for batch 90 (save as `HPC/Plane/Most51.lean`; add `import HPC.Plane.Most51` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded; `theorem2_HIC` keeps its conclusion (if `exists_tame_chain_near` stays open,
`theorem2_HIC` is proved from it and the dependence is recorded).

`IsPseudoArc`, `IsSnakeLike`, `IsEpsChain`, `IsHereditarilyIndecomposable` are from
`Snake51.lean`, `EndPoints51.lean`, `PseudoArc51.lean`.
-/

namespace HPC.Plane

open Set TopologicalSpace Metric

/-! ### The hyperspace of compact continua -/

variable {S : Type*} [MetricSpace S]

/-- **The space of compact continua** `C(S)`: nonempty compact connected subsets of `S`, with the
Hausdorff metric inherited from `NonemptyCompacts S`. -/
def Cont (S : Type*) [MetricSpace S] : Type _ :=
  {K : NonemptyCompacts S // IsConnected (K : Set S)}

noncomputable instance : MetricSpace (Cont S) := Subtype.metricSpace

/-- The continua form a closed subset of the hyperspace (a Hausdorff limit of connected compacta
is connected); hence `Cont S` is complete when `S` is. -/
theorem isClosed_cont : IsClosed {K : NonemptyCompacts S | IsConnected (K : Set S)} := by
  sorry

instance [CompleteSpace S] : CompleteSpace (Cont S) := by
  sorry

/-- `F_i`: the continua that cannot be covered by a chain of mesh below `1/(i+1)`. Closed. -/
theorem isClosed_notCoverable (i : ℕ) :
    IsClosed {K : Cont S | ¬ ∃ (n : ℕ) (D : Chain S n), IsEpsChain D (1 / ((i : ℝ) + 1)) ∧
      (K.1 : Set S) ⊆ D.union} := by
  sorry

/-- `G_i`: the continua containing a subcontinuum `K₁ ∪ K₂` (connected, `K₁`, `K₂` continua) with
a point of `K₁` at distance `≥ 1/(i+1)` from `K₂` and a point of `K₂` at distance `≥ 1/(i+1)`
from `K₁`. Closed. -/
theorem isClosed_separated (i : ℕ) :
    IsClosed {K : Cont S | ∃ K₁ K₂ : Set S, K₁ ⊆ K.1 ∧ K₂ ⊆ K.1 ∧
      Fold.Q78.IsContinuum K₁ ∧ Fold.Q78.IsContinuum K₂ ∧ IsConnected (K₁ ∪ K₂) ∧
      (∃ x ∈ K₁, 1 / ((i : ℝ) + 1) ≤ infDist x K₂) ∧ (∃ y ∈ K₂, 1 / ((i : ℝ) + 1) ≤ infDist y K₁)} := by
  sorry

/-- The degenerate continua form a closed set. -/
theorem isClosed_degenerate : IsClosed {K : Cont S | ∃ x, (K.1 : Set S) = {x}} := by
  sorry

/-- **The pseudo-arcs form a `G_δ`** in `C(S)` (unconditional): the complement of the union of the
closed sets above. -/
theorem isGδ_pseudoArcs : IsGδ {K : Cont S | IsPseudoArc (K.1 : Set S)} := by
  sorry

/-! ### Density: a pseudo-arc near every continuum -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The standard box chain in `E`, along an orthonormal pair `e₁, e₂`: box `j` is
`2j < ⟪x,e₁⟫ < 2j+3`, `0 < ⟪x,e₂⟫ < 1`, and the component orthogonal to `e₁, e₂` of norm `< 1`.
(In the plane this is `stdRect j`.) -/
def stdBox (e₁ e₂ : E) (j : ℕ) : Set E :=
  {x | 2 * (j : ℝ) < inner ℝ x e₁ ∧ inner ℝ x e₁ < 2 * j + 3 ∧ 0 < inner ℝ x e₂ ∧ inner ℝ x e₂ < 1 ∧
    ‖x - (inner ℝ x e₁) • e₁ - (inner ℝ x e₂) • e₂‖ < 1}

/-- A **tame chain** in `E`: the image of the standard box chain under a homeomorphism of `E`
(batch 84's `IsTame`, in `E`). The report may weaken the homeomorphism to an open embedding of
a neighbourhood of the standard strip, recording the change. -/
def IsTameChain {m : ℕ} (D : Chain E m) : Prop :=
  ∃ (e₁ e₂ : E) (_ : Orthonormal ℝ ![e₁, e₂]) (Φ : E ≃ₜ E), ∀ j, D.link j = Φ '' stdBox e₁ e₂ j

/-- **A pseudo-arc inside a tame chain** (batch 84's construction in `E`): a pseudo-arc contained
in the union of the links and meeting every link. -/
theorem exists_pseudoArc_in_tameChain [CompleteSpace E] {m : ℕ} (hm : 3 ≤ m) (D : Chain E m)
    (hD : IsTameChain D) :
    ∃ h : Set E, IsPseudoArc h ∧ h ⊆ D.union ∧ ∀ j, (h ∩ D.link j).Nonempty := by
  sorry

/-- **The geometric lemma** (Bing's broken line and chain of spheres): near every compact
continuum `g` of `E` (`dim E ≥ 2`) there is a tame chain of small links whose union is within `ε`
of `g` and within `ε` of which `g` lies. Expected to be the hard part; may be left `sorry` with
the obstruction stated (COMMISSION-batch90.md §3.7). -/
theorem exists_tame_chain_near [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) {g : Set E}
    (hg : Fold.Q78.IsContinuum g) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsTameChain D ∧ (∀ j, diam (D.link j) < ε) ∧
      D.union ⊆ thickening ε g ∧ g ⊆ thickening ε D.union := by
  sorry

/-- **Density**: every compact continuum is a Hausdorff limit of pseudo-arcs. -/
theorem dense_pseudoArcs [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} := by
  sorry

/-- **Bing 1951 (Pacific J. Math.), Theorem 2.** In a complete real inner product space of
dimension at least two (Euclidean `n`-space with `n > 1`, or Hilbert space), the pseudo-arcs form a
dense `G_δ` in the space of compact continua: most compact continua are pseudo-arcs. -/
theorem theorem2_HIC [CompleteSpace E] (hdim : 2 ≤ Module.rank ℝ E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsPseudoArc (K.1 : Set E)} := by
  sorry

end HPC.Plane
