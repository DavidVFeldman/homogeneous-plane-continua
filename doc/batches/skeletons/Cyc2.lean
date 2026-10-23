import HPC.Plane.Cyc1

/-!
# Batch 128: polygonal Janiszewski, part II — a separating graph contains an odd cycle;
# `JaniszewskiPoly` proved

Skeleton. Every `sorry` is a work item; shapes may be adjusted with the change recorded. Save as
`HPC/Plane/Cyc2.lean`, add `import HPC.Plane.Cyc2` at the end of the root `HPC.lean`.

**The statement** (`SeparatingGraphHasOddCycle`, `Cyc1`): if the proper graph `G` separates `x`
from `y`, some cycle `Z ⊆ G` has `cycParity Z x ≠ cycParity Z y`. With
`janiszewskiPoly_of_oddCycle` this gives `JaniszewskiPoly`.

**The design.** Let `C` be the component of `x` in `(graphSet G)ᶜ` (open, since `graphSet G` is
closed). For an edge `e ∈ G` the two **side strips** of `e` — the half-disks on one side of `e` at
the non-vertex points of `e`, with radii below the distance to the other segments — are
preconnected subsets of `(graphSet G)ᶜ`, so each lies in `C` or misses `C`. Put

    Z := {e ∈ G | C lies on exactly one side of e}.

1. **`Z` is a cycle.** Properness is inherited. Even degree at a vertex `w`: a small ball about `w`
   meets `graphSet G` only in the edges at `w`, and minus them it is a finite union of preconnected
   *sectors*, each adjacent to two consecutive edges (cyclically) and each in `C` or missing `C`;
   an edge at `w` is in `Z` iff its two adjacent sectors differ in `C`-membership; a cyclic sequence
   of booleans changes an even number of times. (The side strip of an edge at `w`, on a given side,
   meets the adjacent sector, so "side of `e`" and "sector adjacent to `e`" agree.)
2. **Odd parity, without paths.** On `(graphSet G)ᶜ` let `g z := [z ∈ C] + cycParity Z z ∈ ZMod 2`.
   Across a non-vertex point of an edge `e`, `[· ∈ C]` flips iff `e ∈ Z` (definition of `Z`, side
   strips), and `cycParity Z` flips iff `e ∈ Z` (`cycParity_flip` at a generic point of `e`; for
   `e ∉ Z` it is locally constant there, as `e` misses `graphSet Z` except at its ends); so `g`
   takes the same value on the two sides of every edge, and extends to a locally constant
   function on `ℝ² ∖ vertices G`, which is connected (the complement of a finite set in the plane;
   Mathlib: `Set.Countable.isPathConnected_compl_of_one_lt_rank`). Hence `g x = g y`, and with
   `x ∈ C`, `y ∉ C` this is `cycParity Z y ≠ cycParity Z x`.
-/

namespace HPC.Plane

open Set Metric

/-! ### Local structure at a non-vertex point of an edge -/

/-- The direction of a segment. -/
def segDir (e : Seg) : Pt := e.2 - e.1

/-- At a non-vertex point `p` of the edge `e` of the proper graph `G`, a small ball meets
`graphSet G` only in `segSet e`, and the ball minus `graphSet G` is the two half-disks
(`halfDisk` of `Jct2`), convex and nonempty. -/
theorem edge_local {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) {p : Pt}
    (hp : p ∈ segSet e) (hpv : p ∉ vertices G) :
    ∃ ρ > 0, ∀ ρ', 0 < ρ' → ρ' ≤ ρ →
      ball p ρ' ∩ graphSet G = ball p ρ' ∩ segSet e ∧
      ball p ρ' \ graphSet G = halfDisk p (segDir e) ρ' true ∪ halfDisk p (segDir e) ρ' false := by
  sorry

/-- The radius used for the side strips at `p`: half the distance from `p` to the union of the
other segments and of the two ends of `e` (positive at a non-vertex point of `e`). Any positive
function of `p` with `halfDisk p _ (sideRadius …) s ⊆ (graphSet G)ᶜ` serves; design it so that the
half-disks at nearby points of `e` overlap. -/
noncomputable def sideRadius (G : Finset Seg) (e : Seg) (p : Pt) : ℝ :=
  sorry

/-- **The side strip** of `e` on side `s`: the union of the half-disks on side `s` at the
non-vertex points of `e`. -/
def sideStrip (G : Finset Seg) (e : Seg) (s : Bool) : Set Pt :=
  ⋃ (p ∈ segSet e) (_ : p ∉ vertices G), halfDisk p (segDir e) (sideRadius G e p) s

theorem sideStrip_subset_compl {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G)
    (s : Bool) : sideStrip G e s ⊆ (graphSet G)ᶜ := by
  sorry

theorem sideStrip_nonempty {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) (s : Bool) :
    (sideStrip G e s).Nonempty := by
  sorry

/-- The side strip is preconnected (half-disks at nearby points of the open segment overlap;
`isPreconnected_biUnion_of_local_meet` over the preconnected open segment). -/
theorem sideStrip_isPreconnected {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G)
    (s : Bool) : IsPreconnected (sideStrip G e s) := by
  sorry

/-- A preconnected subset of `(graphSet G)ᶜ` lies in the component `C` of `x` or misses it. -/
theorem subset_or_disjoint_component {G : Finset Seg} {S : Set Pt} (hS : IsPreconnected S)
    (hSG : S ⊆ (graphSet G)ᶜ) (x : Pt) :
    S ⊆ connectedComponentIn (graphSet G)ᶜ x ∨ Disjoint S (connectedComponentIn (graphSet G)ᶜ x) := by
  sorry

/-! ### The odd set -/

open scoped Classical in
/-- **The candidate cycle**: the edges of `G` having the component of `x` on exactly one side. -/
noncomputable def oddSet (G : Finset Seg) (x : Pt) : Finset Seg :=
  G.filter fun e =>
    (sideStrip G e true ⊆ connectedComponentIn (graphSet G)ᶜ x) ≠
      (sideStrip G e false ⊆ connectedComponentIn (graphSet G)ᶜ x)

theorem oddSet_subset (G : Finset Seg) (x : Pt) : oddSet G x ⊆ G := by
  sorry

/-- **Sectors at a vertex.** For `w ∈ vertices G`, with `r` below the distance from `w` to the
segments not having `w` as an end: `ball w r ∩ graphSet G` is the union of the edges at `w` (cut
to the ball), and `ball w r \ graphSet G` is the union of finitely many preconnected sectors, one
between each pair of angularly consecutive edges at `w` (one sector if `deg G w = 1`). State the
lemma in the form `even_deg_oddSet` needs: a cyclic enumeration `e₀, …, e_{d−1}` of the edges at
`w` and sectors `σ₀, …, σ_{d−1}` with `σᵢ` adjacent to `eᵢ` and `e_{i+1}` — "adjacent" meaning that
the side strip of `eᵢ` on the appropriate side meets `σᵢ` (and the other side strip of `eᵢ` meets
`σ_{i−1}`). (Angles via `Complex.arg` or `Real.Angle` of `z − w`; sectors as images of
`(0, r) × (θᵢ, θ_{i+1})` under the polar map, hence preconnected.) -/
theorem vertex_sectors_placeholder : True := trivial

/-- **Even degree of the odd set at every vertex**: the `C`-membership of the sectors around `w`
is a cyclic sequence of booleans, an edge at `w` is in `oddSet` iff its two adjacent sectors
differ, and a cyclic boolean sequence changes an even number of times. (`deg G w = 1`: the single
edge has both sides in the same sector, so it is not in `oddSet`.) -/
theorem even_deg_oddSet {G : Finset Seg} (hG : IsProper G) (x : Pt) (w : Pt) :
    Even (deg (oddSet G x) w) := by
  sorry

theorem isCycle_oddSet {G : Finset Seg} (hG : IsProper G) (x : Pt) : IsCycle (oddSet G x) := by
  sorry

/-! ### The parity of the odd set differs at `x` and `y` -/

/-- `[· ∈ C] + cycParity (oddSet G x)` on `(graphSet G)ᶜ`. -/
noncomputable def gFun (G : Finset Seg) (x z : Pt) : ZMod 2 :=
  (if z ∈ connectedComponentIn (graphSet G)ᶜ x then 1 else 0) + cycParity (oddSet G x) z

/-- Across a non-vertex point `p` of an edge `e ∈ G`, `gFun` takes the same value on the two
half-disks: both summands flip iff `e ∈ oddSet G x`. (For the parity: `cycParity_flip` at a generic
point of `e` when `e ∈ oddSet`, and local constancy when `e ∉ oddSet` since then `p ∉ graphSet
(oddSet G x)`; the values on each half-disk are constant, and the half-disks at `p` lie in the
side strips, so one generic point per edge suffices.) -/
theorem gFun_eq_across_edge {G : Finset Seg} (hG : IsProper G) (x : Pt) {e : Seg} (he : e ∈ G)
    {p : Pt} (hp : p ∈ segSet e) (hpv : p ∉ vertices G) :
    ∃ ρ > 0, ∀ z₁ ∈ ball p ρ \ graphSet G, ∀ z₂ ∈ ball p ρ \ graphSet G,
      gFun G x z₁ = gFun G x z₂ := by
  sorry

/-- `gFun` is locally constant on `(graphSet G)ᶜ`. -/
theorem gFun_locallyConstant {G : Finset Seg} (hG : IsProper G) (x : Pt) {z : Pt}
    (hz : z ∉ graphSet G) : ∃ ρ > 0, ∀ z' ∈ ball z ρ, z' ∉ graphSet G → gFun G x z' = gFun G x z := by
  sorry

/-- **`gFun` is constant on `(graphSet G)ᶜ`**: it extends to a locally constant function on the
connected open set `(vertices G)ᶜ` (`Set.Countable.isPathConnected_compl_of_one_lt_rank`, or any
proof that the plane minus a finite set is connected). -/
theorem gFun_const {G : Finset Seg} (hG : IsProper G) (x : Pt) {z z' : Pt} (hz : z ∉ graphSet G)
    (hz' : z' ∉ graphSet G) : gFun G x z = gFun G x z' := by
  sorry

/-- **A separating graph has an odd cycle.** -/
theorem cycParity_oddSet_ne {G : Finset Seg} (hG : IsProper G) {x y : Pt}
    (hsep : SeparatesPts (graphSet G) x y) :
    cycParity (oddSet G x) x ≠ cycParity (oddSet G x) y := by
  sorry

theorem separatingGraphHasOddCycle : SeparatingGraphHasOddCycle := by
  sorry

/-- **Janiszewski for polygonal compacta.** -/
theorem janiszewskiPoly_holds : JaniszewskiPoly :=
  janiszewskiPoly_of_oddCycle separatingGraphHasOddCycle

end HPC.Plane
