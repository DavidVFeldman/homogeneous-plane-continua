import HPC.Moore.M19G
import HPC.Plane.Tree67

/-!
# Batch 145: Moore 1925 §I — definitions (verbatim from the skeleton)

Source: R. L. Moore, *Concerning upper semi-continuous collections of continua*, Trans. AMS 27 (1925),
416–428, §I, pp. 416–420 (`doc/sources/moore1925.pdf`). The skeleton is kept as
`doc/batches/skeletons/Moore1925I.lean`; its definitions are copied here unchanged, and its theorems
are proved in `M25Quot.lean`, `M25Plane.lean`, `M25Thm.lean` and collected in `M25A.lean`.

**Setting (p. 416).** `G` is an upper semi-continuous collection of mutually exclusive bounded
continua filling the plane `S`, no element separating `S`. Moore's u.s.c.: for each `g ∈ G` and
`e > 0` there is `d > 0` such that if `x ∈ G` is at lower distance `< d` from `g`, then `x` is at
upper distance `< e` from `g`. A *limit element* `p` of `K ⊆ G`: for every `e > 0`, some element of
`K` other than `p` is at upper distance `< e` from `p`.

**Modelling.** `G` is a `Setoid Pt`; the space of elements is `Quotient r`. `H̄` (Moore’s bar) is
`ptsOf r H = Quotient.mk r ⁻¹' H`.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable (r : Setoid Pt)

/-- The element containing `x`. -/
def elt (x : Pt) : Set Pt := {y | r y x}

/-- The point set `H̄` of a set `H` of elements. -/
def ptsOf (H : Set (Quotient r)) : Set Pt := Quotient.mk r ⁻¹' H

/-- **The standing hypothesis of §I.** -/
structure MooreDecomp : Prop where
  compact : ∀ x, IsCompact (elt r x)
  connected : ∀ x, IsConnected (elt r x)
  nonsep : ∀ x, ¬ SeparatesPlane (elt r x)
  /-- Moore's u.s.c. (lower distance `< d` ⇒ upper distance `< e`). -/
  usc : ∀ x, ∀ e > 0, ∃ d > 0, ∀ y, (∃ p ∈ elt r y, infDist p (elt r x) < d) →
    ∀ p ∈ elt r y, infDist p (elt r x) < e

variable {r}

/-- Moore's *limit element*: for every `e > 0` some element of `K` other than `p` lies at upper
distance `< e` from `p`. -/
def IsLimitElt (p : Quotient r) (K : Set (Quotient r)) : Prop :=
  ∀ e > 0, ∃ k ∈ K, k ≠ p ∧ ∀ y, Quotient.mk r y = k → ∀ z ∈ elt r y,
    ∀ x, Quotient.mk r x = p → infDist z (elt r x) < e

/-- **Moore's region** (p. 419): a bounded domain of elements with a connected boundary. "Bounded":
the point set `H̄` is bounded. -/
def mooreRegion (R : Set (Quotient r)) : Prop :=
  IsOpen R ∧ IsConnected R ∧ Bornology.IsBounded (ptsOf r R) ∧ IsConnected (frontier R)

/-- The space of elements with Moore's regions. -/
def spaceOfElts (r : Setoid Pt) : Space (Quotient r) := ⟨{R | mooreRegion R}⟩

end HPC.Moore
