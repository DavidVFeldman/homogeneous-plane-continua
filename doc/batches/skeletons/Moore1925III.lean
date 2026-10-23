import HPC.Moore.M25B

/-!
# Batch 147 skeleton: Moore 1925 §I, part 3 (Theorems 13–22): the space of elements is a plane

Save as `HPC/Moore/M25C.lean` (splitting under `HPC/Moore/` is expected); add `import HPC.Moore.M25C`
at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be adjusted, each change recorded
at the statement and in the report.

Sources: Moore, Trans. AMS 27 (1925), pp. 422–425 (`doc/sources/moore1925.pdf`); F.A. p. 163
(Axioms 6′, 7′; `doc/sources/moore1916.pdf`). Transcribed from page images at 200 dpi.

**Notation.** Moore writes `pxq` for an arc from `p` to `q`; the middle letter names the arc, and in
Theorem 18 it is also used as an element of it (see the docstring there). The *interior* and
*exterior* of a simple closed curve of elements (p. 422: "Of the two domains which are complementary
to a simple closed curve of elements of `G`, the bounded one will be called the interior, and the
unbounded one … the exterior") are defined below as for `polyInterior`, without Theorem 11; Theorem
11 identifies them with Moore's.
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

section M25C

variable (hG : MooreDecomp r)
include hG

/-- Theorem 11 in terms of `sccInterior`, `sccExterior`: for a simple closed curve of elements these
are Moore's interior and exterior (open, connected, bounded resp. unbounded, each with boundary `J`),
and `Jᶜ` is their disjoint union. -/
theorem sccInterior_spec {J : Set (Quotient r)} (hJ : IsSCCElt J) :
    IsOpen (sccInterior J) ∧ IsConnected (sccInterior J) ∧
      Bornology.IsBounded (ptsOf r (sccInterior J)) ∧ frontier (sccInterior J) = J ∧
      IsOpen (sccExterior J) ∧ IsConnected (sccExterior J) ∧
      ¬ Bornology.IsBounded (ptsOf r (sccExterior J)) ∧ frontier (sccExterior J) = J ∧
      Disjoint (sccInterior J) (sccExterior J) ∧ sccInterior J ∪ sccExterior J = Jᶜ := by
  sorry

/-- Two arcs from `p` to `q` with only `p`, `q` in common form a simple closed curve (used in the
statements of Theorems 15–18: "the simple closed curve formed by these two arcs"). -/
theorem isSCCElt_union {p q : Quotient r} {X Y : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hXY : X ∩ Y = {p, q}) : IsSCCElt (X ∪ Y) := by
  sorry

/-- A region in the restricted sense is a region in the original sense (p. 424, proof of Theorem 20:
"Since `R` is also a region in the original sense"). -/
theorem mooreRegion_of_restricted {R : Set (Quotient r)} (hR : restrictedRegion R) :
    mooreRegion R := by
  sorry

/-- **Theorem 13** (p. 422). If `R` is a region and `k` is either a single element or an arc every
element of which, except possibly one end element, belongs to `R`, then `R − k` is a domain. -/
theorem m25_theorem13 {R k : Set (Quotient r)} (hR : mooreRegion R)
    (hk : (∃ e, k = {e}) ∨ ∃ a b, IsArcElt a b k ∧ (k \ {a} ⊆ R ∨ k \ {b} ⊆ R)) :
    IsOpen (R \ k) ∧ IsConnected (R \ k) := by
  sorry

/-- **Theorem 14** (p. 423). Every region contains a simple closed curve of elements. -/
theorem m25_theorem14 {R : Set (Quotient r)} (hR : mooreRegion R) :
    ∃ J, IsSCCElt J ∧ J ⊆ R := by
  sorry

/-- **Theorem 15** (p. 423). `pxq`, `pyq` arcs from `p` to `q` with only `p`, `q` in common,
`J = pxq + pyq`, `R` its interior, `pzq` an arc all of whose elements except `p`, `q` lie in `R`;
`J₁ = pxq + pzq`, `J₂ = pyq + pzq`. Then (1) the interior `R₁` of `J₁` is a subset of `R`; (2) `pyq`
is, except for `p` and `q`, in the exterior of `R₁`; (3) `R₁` and the interior `R₂` of `J₂` are
disjoint. ("Closely analogous" to F.A. Theorem 24.) -/
theorem m25_theorem15 {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q})
    (hZR : Z \ {p, q} ⊆ sccInterior (X ∪ Y)) :
    sccInterior (X ∪ Z) ⊆ sccInterior (X ∪ Y) ∧ Y \ {p, q} ⊆ sccExterior (X ∪ Z) ∧
      Disjoint (sccInterior (X ∪ Z)) (sccInterior (Y ∪ Z)) := by
  sorry

/-- **Theorem 16** (p. 423). Under the hypothesis of Theorem 15, `R` is the sum of `R₁`, `R₂` and
`pzq − (p + q)`. ("Closely parallel" to F.A. Theorem 25.) -/
theorem m25_theorem16 {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q})
    (hZR : Z \ {p, q} ⊆ sccInterior (X ∪ Y)) :
    sccInterior (X ∪ Y) = sccInterior (X ∪ Z) ∪ sccInterior (Y ∪ Z) ∪ (Z \ {p, q}) := by
  sorry

/-- **Theorem 17** (p. 423). Three arcs from `p` to `q`, no two with a common element except `p`,
`q`: the interiors of the three closed curves they form in pairs are not mutually exclusive. ("A method
similar to that used in F.A. to prove Theorem 26.") -/
theorem m25_theorem17 {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q}) (hXZ : X ∩ Z = {p, q})
    (hYZ : Y ∩ Z = {p, q}) :
    ¬ (Disjoint (sccInterior (X ∪ Y)) (sccInterior (X ∪ Z)) ∧
      Disjoint (sccInterior (X ∪ Y)) (sccInterior (Y ∪ Z)) ∧
      Disjoint (sccInterior (X ∪ Z)) (sccInterior (Y ∪ Z))) := by
  sorry

/-- **Theorem 18** (pp. 423–424). `pxq`, `pyq` arcs with only their extremities in common, `J` the
curve they form, `pzq` an arc lying, except for its extremities, in the exterior of `J`;
`J₁ = pxq + pzq`, `J₂ = pyq + pzq`. Then "(1) either `y` is without `J₁` … or `x` is in the exterior of
`J₂`, (2) if `y` is without `J₁` then `x` is in the interior of `J₂` and the interior of `J₂` is the sum
of the interior of `J`, the interior of `J₁` and the set of elements `pxq − (p + q)`".

*Reading.* `x` and `y` are not introduced; they are read as the arcs' elements other than `p`, `q`
(all of them; record whether the condition depends on the choice), and "without" as "in the
exterior of". ("A method analogous to that used in F.A. to prove Theorem 27.") -/
theorem m25_theorem18 {p q : Quotient r} {X Y Z : Set (Quotient r)} (hX : IsArcElt p q X)
    (hY : IsArcElt p q Y) (hZ : IsArcElt p q Z) (hXY : X ∩ Y = {p, q})
    (hZE : Z \ {p, q} ⊆ sccExterior (X ∪ Y)) :
    (Y \ {p, q} ⊆ sccExterior (X ∪ Z) ∨ X \ {p, q} ⊆ sccExterior (Y ∪ Z)) ∧
      (Y \ {p, q} ⊆ sccExterior (X ∪ Z) →
        X \ {p, q} ⊆ sccInterior (Y ∪ Z) ∧
          sccInterior (Y ∪ Z) = sccInterior (X ∪ Y) ∪ sccInterior (X ∪ Z) ∪ (X \ {p, q})) := by
  sorry

/-- **Theorem 19** (p. 424). If `R` is a region and `p ∈ R`, there is a simple closed curve of
elements lying in `R` whose interior contains `p` and is a subset of `R`. ("With the use of Theorems
11, 12, 13, 17 and 18 … closely analogous to that employed to prove Theorem 36 in F.A.") -/
theorem m25_theorem19 {R : Set (Quotient r)} (hR : mooreRegion R) {p : Quotient r} (hp : p ∈ R) :
    ∃ J, IsSCCElt J ∧ J ⊆ R ∧ p ∈ sccInterior J ∧ sccInterior J ⊆ R := by
  sorry

/-- **Theorem 20** (p. 424). `p` is a limit element of `H` iff every region in the restricted sense
containing `p` contains an element of `H` other than `p`. -/
theorem m25_theorem20 {p : Quotient r} {H : Set (Quotient r)} :
    IsLimitElt p H ↔ (spaceRestricted r).IsLimitPt p H := by
  sorry

/-- The topology of the restricted regions is the quotient topology. -/
theorem spaceRestricted_topology :
    (spaceRestricted r).topology = (inferInstance : TopologicalSpace (Quotient r)) := by
  sorry

/-- **Theorem 21** (pp. 424–425). With the restricted regions, the space of elements satisfies
F.A.'s Axioms 1–8; along the way, Axioms 6′ and 7′ of Σ₂ (Moore's route to 6 and 7). -/
theorem m25_theorem21 :
    (spaceRestricted r).Axiom1 ∧ (spaceRestricted r).Axiom2 ∧ (spaceRestricted r).Axiom3 ∧
      (spaceRestricted r).Axiom4 ∧ (spaceRestricted r).Axiom5 ∧ (spaceRestricted r).Axiom6 ∧
      (spaceRestricted r).Axiom7 ∧ (spaceRestricted r).Axiom8 := by
  sorry

/-- Axioms 6′ and 7′ for the restricted regions ("a consequence of Theorems 11 and 13", p. 425). -/
theorem m25_axioms6'7' : (spaceRestricted r).Axiom6' ∧ (spaceRestricted r).Axiom7' := by
  sorry

/-- **Theorem 22** (p. 425), topological form: the space of elements is homeomorphic to the plane. -/
theorem m25_theorem22 : Nonempty (Quotient r ≃ₜ ℝ × ℝ) := by
  sorry

/-- **Theorem 22**, Moore's form: a one-to-one correspondence between the elements of `G` and the
points of the plane such that a point `P` is a limit point of a point set `M` iff the corresponding
element is a limit element (in Moore's sense) of the set of elements corresponding to `M`. -/
theorem m25_theorem22_moore :
    ∃ e : Quotient r ≃ ℝ × ℝ, ∀ (P : ℝ × ℝ) (M : Set (ℝ × ℝ)),
      AccPt P (Filter.principal M) ↔ IsLimitElt (e.symm P) (e.symm '' M) := by
  sorry

end M25C

end HPC.Moore
