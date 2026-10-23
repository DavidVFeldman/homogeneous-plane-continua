import HPC.Plane.Jct2

/-!
# Batch 127: polygonal Janiszewski, part I — straight-line graphs, mod-2 cycles, their parity,
# and Mayer–Vietoris for cycles

Skeleton. Every `sorry` is a work item; shapes may be adjusted with the change recorded. Save as
`HPC/Plane/Cyc1.lean`, add `import HPC.Plane.Cyc1` at the end of the root `HPC.lean`.

## The plan for `janiszewski` (batches 127–129)

The field asks: `A`, `B` compact, `A ∩ B` connected or empty, neither separates `x` from `y` ⇒
`A ∪ B` does not. It is used twice, both times with **polygonal** sets: in `crosscut'` with two
simple closed polygons, and in `exists_theta_point`, where the sets `A = closure C ∩ frontier h₁`,
`B = closure C ∩ frontier h₂` can be replaced by `closure (h₁ ∩ h₂) ∩ frontier hᵢ` (the proof goes
through verbatim) and these are finite unions of segments when `h₁`, `h₂` are polygon interiors,
which they are at the only call. So the field will be **weakened to polygonal compacta** (finite
unions of closed segments; batch 129 makes the change and re-proves the two uses), and proved by
mod-2 cycles:

* (i) **this batch**: straight-line graphs in proper position, subdivision, mod-2 cycles (every
  vertex of even degree), their east-ray parity (the `Jct1` machinery, edge-local: `crossesEast_jump`
  and the telescoping of vertex jumps over an even-degree graph), local constancy, additivity under
  symmetric difference, the flip across an edge, "different parity ⇒ separated", and
  Mayer–Vietoris: a cycle in `A ∪ B` with `A ∩ B` connected is the sum of a cycle in `A` and a cycle
  in `B`;
* (ii) **batch 128**: a graph that separates `x` from `y` contains a cycle of different parity at
  `x` and `y` (the edges having the component of `x` on exactly one side; even at every vertex by
  the sector structure around a vertex; odd parity by a path from `x` to `y` in general position);
* (iii) **batch 129**: assembly, the polygonal field, the two uses.

Conventions: `Pt = ℝ × ℝ`; a segment is an ordered pair of distinct points, its point set
`segment ℝ a b`. Representation choices (ordered vs unordered pairs, how "no two segments with the
same point set" is enforced) are yours; the Props below are what the later batches use.
-/

namespace HPC.Plane

open Set

/-! ### Straight-line graphs -/

/-- A segment: an ordered pair of points, meant distinct. -/
abbrev Seg := Pt × Pt

/-- The point set of a segment. -/
def segSet (s : Seg) : Set Pt := segment ℝ s.1 s.2

/-- The point set of a finite set of segments. -/
def graphSet (G : Finset Seg) : Set Pt := ⋃ s ∈ G, segSet s

/-- The end points of the segments of `G`. -/
def vertices (G : Finset Seg) : Finset Pt := G.image Prod.fst ∪ G.image Prod.snd

/-- **Proper position**: every segment nondegenerate, two distinct segments have distinct point
sets and meet at most in a common end point. -/
def IsProper (G : Finset Seg) : Prop :=
  (∀ s ∈ G, s.1 ≠ s.2) ∧
  (∀ s ∈ G, ∀ t ∈ G, s ≠ t → segSet s ≠ segSet t) ∧
  ∀ s ∈ G, ∀ t ∈ G, segSet s ≠ segSet t →
    segSet s ∩ segSet t ⊆ ({s.1, s.2} : Set Pt) ∩ ({t.1, t.2} : Set Pt)

/-- The degree of a point in `G`: the number of segments having it as an end point. -/
noncomputable def deg (G : Finset Seg) (w : Pt) : ℕ :=
  (G.filter fun s => w = s.1 ∨ w = s.2).card

/-- A **mod-2 cycle**: a proper graph with every degree even. -/
def IsCycle (G : Finset Seg) : Prop := IsProper G ∧ ∀ w, Even (deg G w)

/-- **Subdivision.** Every finite set of nondegenerate segments has a proper refinement with the
same point set, every piece lying in a segment of the original, and every original segment a union
of pieces. (Cut every segment at every point where it meets another segment's line in a point, and
at every end point of another segment lying on it; collinear overlaps are cut at all end points.) -/
theorem exists_proper_subdivision (S : Finset Seg) (hS : ∀ s ∈ S, s.1 ≠ s.2) :
    ∃ G : Finset Seg, IsProper G ∧ graphSet G = graphSet S ∧
      (∀ t ∈ G, ∃ s ∈ S, segSet t ⊆ segSet s) ∧
      (∀ s ∈ S, segSet s = ⋃ t ∈ G.filter (fun t => segSet t ⊆ segSet s), segSet t) := by
  sorry

/-- A subset of a proper graph is proper. -/
theorem IsProper.subset {G H : Finset Seg} (hG : IsProper G) (hHG : H ⊆ G) : IsProper H := by
  sorry

/-- `graphSet` is closed (a finite union of segments). -/
theorem isClosed_graphSet (G : Finset Seg) : IsClosed (graphSet G) := by
  sorry

/-! ### Parity of a cycle -/

/-- The east-ray crossing parity of a finite set of segments (`ceInd` from `Jct1`). -/
noncomputable def cycParity (G : Finset Seg) (x : Pt) : ZMod 2 := ∑ s ∈ G, ceInd x s.1 s.2

/-- Additivity: parity of a symmetric difference is the sum of the parities (edges in both cancel
mod 2). No properness needed. -/
theorem cycParity_symmDiff (G H : Finset Seg) (x : Pt) :
    cycParity (symmDiff G H) x = cycParity G x + cycParity H x := by
  sorry

/-- **The telescoping of vertex jumps over an even-degree graph** (the generalisation of
`sum_vJump_telescope`): `∑ s ∈ G, (vJump x s.1 + vJump x s.2) = 0` when every degree is even. -/
theorem sum_vJump_even (G : Finset Seg) (heven : ∀ w, Even (deg G w)) (x : Pt) :
    ∑ s ∈ G, (vJump x s.1 + vJump x s.2) = 0 := by
  sorry

/-- **Local constancy of the parity of a cycle** off its point set (`crossesEast_jump` per edge,
`sum_vJump_even` for the jumps). -/
theorem cycParity_locallyConstant {G : Finset Seg} (hG : ∀ w, Even (deg G w)) {x : Pt}
    (hx : x ∉ graphSet G) : ∃ ε > 0, ∀ y, dist y x < ε → cycParity G y = cycParity G x := by
  sorry

theorem cycParity_eq_of_isPreconnected {G : Finset Seg} (hG : ∀ w, Even (deg G w)) {S : Set Pt}
    (hS : IsPreconnected S) (hSG : S ⊆ (graphSet G)ᶜ) {x y : Pt} (hx : x ∈ S) (hy : y ∈ S) :
    cycParity G x = cycParity G y := by
  sorry

theorem cycParity_far (G : Finset Seg) : ∃ R : ℝ, ∀ x : Pt, R < x.1 → cycParity G x = 0 := by
  sorry

/-- **Different parity ⇒ separated**: if `cycParity G x ≠ cycParity G y` (with `G` of even degrees
and `x, y ∉ graphSet G`), then `graphSet G` separates `x` from `y`. -/
theorem separatesPts_of_cycParity_ne {G : Finset Seg} (hG : ∀ w, Even (deg G w)) {x y : Pt}
    (hx : x ∉ graphSet G) (hy : y ∉ graphSet G) (hne : cycParity G x ≠ cycParity G y) :
    SeparatesPts (graphSet G) x y := by
  sorry

/-- **The flip across an edge of a cycle**, at a point `p` of `segSet s` (`s ∈ G`) lying on no other
segment of `G` and at the height of no vertex (`Jct2`'s `parity_flip_at` for non-horizontal `s`,
`parity_flip_vertical` for horizontal `s`, with the hypotheses the report of batch 126 lists):
there are points arbitrarily close to `p` on the two sides of `s` with different parities. -/
theorem cycParity_flip {G : Finset Seg} (hG : IsCycle G) {s : Seg} (hs : s ∈ G) {p : Pt}
    (hp : p ∈ segSet s) (hother : ∀ t ∈ G, t ≠ s → p ∉ segSet t) (hpv : p ∉ vertices G)
    (hgen : s.1.2 ≠ s.2.2 → ∀ w ∈ vertices G, w.2 ≠ p.2) :
    ∀ ε > 0, ∃ z₁ z₂ : Pt, dist z₁ p < ε ∧ dist z₂ p < ε ∧ z₁ ∉ graphSet G ∧ z₂ ∉ graphSet G ∧
      cycParity G z₁ ≠ cycParity G z₂ := by
  sorry

/-! ### Mayer–Vietoris for cycles -/

/-- A finite union of segments that is connected and has two points is **graph-connected**: any
two of its vertices are joined by a walk along its segments. (State in the form you need for
`exists_cycle_decomposition`; the content is that a connected finite union of proper segments is
path-connected along the segments.) -/
theorem graph_connected_of_isConnected {G : Finset Seg} (hG : IsProper G)
    (hc : IsConnected (graphSet G)) {a b : Pt} (ha : a ∈ vertices G) (hb : b ∈ vertices G)
    (hab : a ≠ b) :
    ∃ P : Finset Seg, P ⊆ G ∧ ∀ w, Odd (deg P w) ↔ (w = a ∨ w = b) := by
  sorry

/-- **Mayer–Vietoris.** `K` proper; `A, B ⊆ K`; `Z ⊆ A ∪ B` a cycle; `graphSet A ∩ graphSet B`
connected or empty. Then `Z = Z_A Δ Z_B` with `Z_A ⊆ A`, `Z_B ⊆ B` cycles. (`Z_A₀ := Z ∩ A`,
`Z_B₀ := Z \ A ⊆ B`; the odd vertices of `Z_A₀` are odd for `Z_B₀` too and lie in
`graphSet A ∩ graphSet B`; there are evenly many; join them in pairs by walks `P` in the
segments of `A ∩ B` (`graph_connected_of_isConnected`, after noting that the segments of `K` inside
`graphSet A ∩ graphSet B` are exactly those of `A ∩ B`); `Z_A := Z_A₀ Δ ⋃P`, `Z_B := Z_B₀ Δ ⋃P`.) -/
theorem exists_cycle_decomposition {K A B Z : Finset Seg} (hK : IsProper K) (hA : A ⊆ K)
    (hB : B ⊆ K) (hZ : IsCycle Z) (hZAB : Z ⊆ A ∪ B)
    (hAB : IsConnected (graphSet A ∩ graphSet B) ∨ graphSet A ∩ graphSet B = ∅) :
    ∃ ZA ZB : Finset Seg, ZA ⊆ A ∧ ZB ⊆ B ∧ IsCycle ZA ∧ IsCycle ZB ∧ Z = symmDiff ZA ZB := by
  sorry

/-! ### What batch 128 will add (statements only, as `Prop`s; no `sorry`) -/

/-- **A separating graph contains an odd cycle** (batch 128): if the proper graph `G` separates
`x` from `y`, some cycle `Z ⊆ G` has `cycParity Z x ≠ cycParity Z y`. -/
def SeparatingGraphHasOddCycle : Prop :=
  ∀ (G : Finset Seg), IsProper G → ∀ x y : Pt, SeparatesPts (graphSet G) x y →
    ∃ Z : Finset Seg, Z ⊆ G ∧ IsCycle Z ∧ cycParity Z x ≠ cycParity Z y

/-- **Janiszewski for polygonal compacta** (the weakened field, batch 129): `A`, `B` finite unions
of segments, `A ∩ B` connected or empty, neither separating `x` from `y` ⇒ `A ∪ B` does not. -/
def JaniszewskiPoly : Prop :=
  ∀ (SA SB : Finset Seg), (∀ s ∈ SA, s.1 ≠ s.2) → (∀ s ∈ SB, s.1 ≠ s.2) →
    (IsConnected (graphSet SA ∩ graphSet SB) ∨ graphSet SA ∩ graphSet SB = ∅) →
    ∀ x y : Pt, ¬ SeparatesPts (graphSet SA) x y → ¬ SeparatesPts (graphSet SB) x y →
      ¬ SeparatesPts (graphSet SA ∪ graphSet SB) x y

/-- **Janiszewski from the odd cycle** (this batch, given the batch-128 statement as a hypothesis):
subdivide `SA ∪ SB` to a proper `K` (`exists_proper_subdivision`), take the pieces inside
`graphSet SA` as `A` and inside `graphSet SB` as `B`; if `A ∪ B` separates, an odd cycle `Z`
exists; decompose `Z = Z_A Δ Z_B`; by additivity one of them has different parities at `x`, `y`;
`separatesPts_of_cycParity_ne` then contradicts the hypothesis for `SA` or `SB`. -/
theorem janiszewskiPoly_of_oddCycle (h : SeparatingGraphHasOddCycle) : JaniszewskiPoly := by
  sorry

end HPC.Plane
