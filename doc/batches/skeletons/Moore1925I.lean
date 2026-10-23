import HPC.Moore.M19G
import HPC.Plane.Tree67

/-!
# Batch 145 skeleton: Moore 1925 §I, part 1 (Theorems 1–4; Axioms 1, 2, 4, 5 for the space of elements)

Save as `HPC/Moore/M25A.lean` (splitting under `HPC/Moore/` is expected; adjust the imports to whatever
provides `planeFacts_holds`, `Pt`, `SeparatesPlane`, `polyInterior`, `IsSimpleClosedPolygon`); add
`import HPC.Moore.M25A` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be adjusted,
each change recorded at the statement and in the report.

Source: R. L. Moore, *Concerning upper semi-continuous collections of continua*, Trans. AMS 27 (1925),
416–428, §I, pp. 416–420 (`moore1925.pdf`, new). Transcribed from page images at 200 dpi.

**Setting (p. 416).** `G` is an upper semi-continuous collection of mutually exclusive bounded
continua filling the plane `S`, no element separating `S`. Moore's u.s.c.: for each `g ∈ G` and
`e > 0` there is `d > 0` such that if `x ∈ G` is at lower distance `< d` from `g`, then `x` is at
upper distance `< e` from `g`. Here `l(MN) = inf_{P∈M} dist(P, N)` and `u(MN) = sup_{P∈M} dist(P, N)`;
`M` is at upper distance `u(MN)` from `N`. A *limit element* `p` of `K ⊆ G`: for every `e > 0`, some
element of `K` other than `p` is at upper distance `< e` from `p`.

**Modelling.** `G` is a `Setoid Pt`; the space of elements is `Quotient r`. Moore's notions on sets
of elements (sum, mutually separated, connected, closed, continuum, bounded, domain, boundary,
complementary domain, outer boundary, simple closed curve, simple continuous arc; pp. 417–419) are
taken in the quotient topology, after `isLimitElt_iff` identifies Moore's limit element with
accumulation in the quotient. `H̄` (Moore’s bar) is `ptsOf r H = Quotient.mk r ⁻¹' H`.
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

section M25A

variable (hG : MooreDecomp r)
include hG

/-- Moore's u.s.c. is the open-set form: the quotient map is closed. -/
theorem isClosedMap_mk_plane : IsClosedMap (Quotient.mk r) := by
  sorry

/-- The quotient is Hausdorff, second countable, locally compact (so metrizable). -/
theorem quotient_metrizable_plane : TopologicalSpace.MetrizableSpace (Quotient r) := by
  sorry

/-- Moore's limit element is accumulation in the quotient topology ("the notion of limit point so
defined coincides … with the natural interpretation of limit element", p. 416). -/
theorem isLimitElt_iff {p : Quotient r} {K : Set (Quotient r)} :
    IsLimitElt p K ↔ AccPt p (Filter.principal K) := by
  sorry

/-- **Theorem 1** (p. 418). If `K` is a set of points and `H` is the set of elements meeting `K`,
then `H` is closed if `K` is closed, and connected if `K` is connected. -/
theorem m25_theorem1 {K : Set Pt} :
    (IsClosed K → IsClosed (Quotient.mk r '' K)) ∧
      (IsConnected K → IsConnected (Quotient.mk r '' K)) := by
  sorry

/-- **Plane fact (Brouwer, Math. Ann. 69; used in Theorem 3):** the boundary of a complementary
domain of a plane continuum is a continuum. State it in the generality needed (the complementary
domain of a closed connected set `H̄`). -/
theorem brouwer_boundary {M : Set Pt} (hM : IsClosed M) (hMc : IsConnected M) {D : Set Pt}
    (hD : ∃ x ∈ Mᶜ, D = connectedComponentIn Mᶜ x) : IsConnected (frontier D) := by
  sorry

/-- **Plane fact (Janiszewski 1913; used in Theorems 2 and 13):** if `A`, `B` are compact, `A ∩ B` is
connected (or empty), and neither separates `x` from `y`, then `A ∪ B` does not. The repository has
the polygonal form (`janiszewski_polygonal`); the compact form is needed here. -/
theorem janiszewski_compact {A B : Set Pt} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : IsConnected (A ∩ B) ∨ A ∩ B = ∅) {x y : Pt} (hxA : ¬ SeparatesPts A x y)
    (hxB : ¬ SeparatesPts B x y) : ¬ SeparatesPts (A ∪ B) x y := by
  sorry

/-- **Theorem 2** (p. 418). If `D` is a bounded complementary domain of a bounded continuum of
elements, `K` the outer boundary of `D`, and `p ∈ K`, then `K` is a continuum of elements and
`K − p` is connected.

*Reading.* Moore's *complementary domain* of a closed `H` (p. 417) is printed as "a domain … provided
the boundary of `D` is a subset of `H`" — no disjointness from `H`, no maximality (see §3 of the
commission). It is read here as a component of `Hᶜ`. The *outer boundary* of a bounded domain `D` is
the boundary of "the unbounded complementary domain of the boundary of `D`": here the frontier of an
unbounded component `E` of `(frontier D)ᶜ`. That there is exactly one such `E` is a further item
(`m25_unbounded_unique`). -/
theorem m25_theorem2 {M : Set (Quotient r)} (hM : IsClosed M) (hMc : IsConnected M)
    (hMb : Bornology.IsBounded (ptsOf r M)) {x : Quotient r} (hx : x ∉ M)
    (hDb : Bornology.IsBounded (ptsOf r (connectedComponentIn Mᶜ x)))
    {y : Quotient r} (hy : y ∉ frontier (connectedComponentIn Mᶜ x))
    (hE : ¬ Bornology.IsBounded
      (ptsOf r (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y)))
    {p : Quotient r}
    (hp : p ∈ frontier (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y)) :
    IsClosed (frontier (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y)) ∧
      IsConnected (frontier (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y)) ∧
      IsConnected
        (frontier (connectedComponentIn (frontier (connectedComponentIn Mᶜ x))ᶜ y) \ {p}) := by
  sorry

/-- "**The** unbounded complementary domain" (pp. 417, 418): a closed set of elements `H` with
`ptsOf r H` bounded has exactly one complementary component whose point set is unbounded. -/
theorem m25_unbounded_unique {H : Set (Quotient r)} (hH : IsClosed H)
    (hHb : Bornology.IsBounded (ptsOf r H)) :
    ∃ y ∉ H, ¬ Bornology.IsBounded (ptsOf r (connectedComponentIn Hᶜ y)) ∧
      ∀ z ∉ H, ¬ Bornology.IsBounded (ptsOf r (connectedComponentIn Hᶜ z)) →
        connectedComponentIn Hᶜ z = connectedComponentIn Hᶜ y := by
  sorry

/-- Moore's *domain* (p. 417): "a connected set `D` of elements of `G` such that for every element
`x` belonging to `D` there exists a positive number `d` such that if `y` is any element of `G` at an
upper distance from `x` less than `d` then `y` belongs to `D`". These are the connected open sets of
the quotient. -/
theorem m25_domain_iff {D : Set (Quotient r)} :
    (IsConnected D ∧ ∀ x, Quotient.mk r x ∈ D → ∃ d > 0, ∀ y,
        (∀ z ∈ elt r y, infDist z (elt r x) < d) → Quotient.mk r y ∈ D) ↔
      IsConnected D ∧ IsOpen D := by
  sorry

/-- **Theorem 3** (p. 419). For each element `p` and `e > 0` there is a region every element of which
is at upper distance `< e` from `p`. *The printed statement does not say that the region contains
`p`. The proof gives it (`p ⊆ D`) and Theorem 4 needs it, so `p ∈ R` is added.* (Moore uses a simple closed curve enclosing `p` within `e`,
"Theorem 1 of my paper *Concerning the separation of point sets by curves*"; the repository's
`planeFacts_holds.enclose` gives a polygon.) -/
theorem m25_theorem3 (p : Quotient r) {e : ℝ} (he : 0 < e) :
    ∃ R, mooreRegion R ∧ p ∈ R ∧ ∀ k ∈ R, ∀ y, Quotient.mk r y = k → ∀ z ∈ elt r y,
      ∀ x, Quotient.mk r x = p → infDist z (elt r x) < e := by
  sorry

/-- **Theorem 4** (p. 420). `p` is a limit element of `K` iff every region containing `p` contains an
element of `K` other than `p`. ("May be easily established with the help of Theorem 3.") -/
theorem m25_theorem4 {p : Quotient r} {K : Set (Quotient r)} :
    IsLimitElt p K ↔ (spaceOfElts r).IsLimitPt p K := by
  sorry

/-- **The unnumbered claim of p. 420.** "It may be shown that if the word 'point' as used in F. A. is
interpreted to mean 'element of `G`' … and the word 'region' … 'region of elements of `G`' as defined
above, then, for the space `S(G)` …, Axioms 1, 2, 4 and 5 and Theorem 4 of F. A. hold true", by
"methods largely analogous to those used in a similar connection in my paper *Concerning the prime
parts of a continuum*" (Math. Z. 22 (1925)). -/
theorem m25_axioms1245 :
    (spaceOfElts r).Axiom1 ∧ (spaceOfElts r).Axiom2 ∧ (spaceOfElts r).Axiom4 ∧
      (spaceOfElts r).Axiom5 ∧
      ∀ R ∈ (spaceOfElts r).region, R.Nonempty → R.Infinite := by
  sorry

/-- The region topology of `spaceOfElts r` is the quotient topology. -/
theorem spaceOfElts_topology : (spaceOfElts r).topology = (inferInstance : TopologicalSpace (Quotient r)) := by
  sorry

end M25A

end HPC.Moore
