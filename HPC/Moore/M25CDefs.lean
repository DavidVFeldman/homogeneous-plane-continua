import HPC.Moore.M25B
import HPC.Moore.Sec7B
import HPC.Moore.M19G

/-!
# Batch 147: Moore 1925 §I, part 3 — definitions (verbatim from the skeleton)

The skeleton is kept as `doc/batches/skeletons/Moore1925III.lean`; its definitions are copied here
unchanged. The theorems are proved in `M25CInt.lean` (item A), `M25C13.lean` (Theorems 13, 14),
`M25C15.lean` (Theorems 15–18), `M25C19.lean` (Theorem 19), `M25C20.lean` (Theorem 20, the topology,
Axioms 1–5, 8, 6′, 7′), `M25C6.lean` (Axioms 6, 7) and `M25C.lean` (Theorems 21, 22).

Sources: Moore, Trans. AMS 27 (1925), pp. 422–425 (`doc/sources/moore1925.pdf`); F.A. p. 163
(Axioms 6′, 7′; `doc/sources/moore1916.pdf`).

**Notation.** Moore writes `pxq` for an arc from `p` to `q`; the middle letter names the arc, and in
Theorem 18 it is also used as an element of it. The *interior* and *exterior* of a simple closed
curve of elements (p. 422: "Of the two domains which are complementary to a simple closed curve of
elements of `G`, the bounded one will be called the interior, and the unbounded one … the
exterior") are defined below as for `polyInterior`, without Theorem 11; Theorem 11 identifies them
with Moore's (`sccInterior_spec`).
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

/-- The interior of a set of elements: the elements off `J` whose complementary component has a
bounded point set. -/
def sccInterior (J : Set (Quotient r)) : Set (Quotient r) :=
  {x | x ∉ J ∧ Bornology.IsBounded (ptsOf r (connectedComponentIn Jᶜ x))}

/-- The exterior: the elements off `J` whose complementary component has an unbounded point set. -/
def sccExterior (J : Set (Quotient r)) : Set (Quotient r) :=
  {x | x ∉ J ∧ ¬ Bornology.IsBounded (ptsOf r (connectedComponentIn Jᶜ x))}

/-- *Region in the restricted sense* (p. 424): "the interior of some simple closed curve of elements
of `G`". -/
def restrictedRegion (R : Set (Quotient r)) : Prop :=
  ∃ J, IsSCCElt J ∧ R = sccInterior J

/-- The space of elements with the restricted regions. -/
def spaceRestricted (r : Setoid Pt) : Space (Quotient r) := ⟨{R | restrictedRegion R}⟩

namespace Space

variable {S : Type*} (σ : Space S)

/-- **Axiom 6′** (F.A. p. 163): "If `R` is a region and `AB` is an arc such that `AB − A` is a subset
of `R` then `(R + A) − AB` is connected." -/
def Axiom6' : Prop :=
  ∀ R ∈ σ.region, ∀ (A B : S) (C : Set S), σ.IsArc A B C → C \ {A} ⊆ R → σ.IsConn ((R ∪ {A}) \ C)

/-- **Axiom 7′** (F.A. p. 163): "Every boundary point of a region is a limit point of the exterior of
that region." -/
def Axiom7' : Prop := ∀ R ∈ σ.region, ∀ P ∈ σ.bdry R, σ.IsLimitPt P (σ.ext R)

end Space

end HPC.Moore
