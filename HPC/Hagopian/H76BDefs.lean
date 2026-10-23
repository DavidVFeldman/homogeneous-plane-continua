import HPC.Hagopian.H76Defs
import HPC.Moore.Sec6Arc

/-!
# Batch 157: the definitions of the skeleton `Hagopian76B.lean`

The definitions of the set-up of Theorem 1 (Hagopian 1976, pp. 344–345), verbatim from the batch-157
skeleton, split off so that the supporting files can use them.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Setup

variable {M : Set Pt}

open Classical in
/-- The key of the relation `S` (p. 344): a point of `E` goes to the parameter of its layer, a point
off `E` to itself. -/
noncomputable def layerKey {E : Set M} (k : E → unitInterval) (p : Pt) : unitInterval ⊕ Pt :=
  if h : ∃ hM : p ∈ M, (⟨p, hM⟩ : M) ∈ E then Sum.inl (k ⟨⟨p, h.1⟩, h.2⟩) else Sum.inr p

/-- **The relation `S`** (p. 345): "the equivalence relation on `R²` that relates distinct points
`p` and `q` if and only if `{p, q}` is a subset of an element of the decomposition of `E`". -/
noncomputable def layerSetoid {E : Set M} (k : E → unitInterval) : Setoid Pt :=
  Setoid.ker (layerKey k)

/-- A point `p` of the plane is **accessible from the complement** of `M`: it is the end of an arc
meeting `M` only in `p`. -/
def IsAccessibleFrom (M : Set Pt) (p : Pt) : Prop :=
  ∃ (x : Pt) (C : Set Pt), TArc x p C ∧ C ∩ M = {p}

end Setup

end HPC.Hagopian
