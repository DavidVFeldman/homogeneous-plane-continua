import HPC.Plane.Jct1

/-!
# Batch 126: the Jordan curve theorem for simple closed polygons, part II — the two sides are
# connected; `jct` discharged

Skeleton. Every `sorry` is a work item; shapes may be adjusted with the change recorded. Save as
`HPC/Plane/Jct2.lean`, add `import HPC.Plane.Jct2` at the end of the root `HPC.lean`.

With `Γ = polygonOf v` (`IsSimpleVertices v`), `U := {x ∉ Γ | parity v x = 1}`,
`V := {x ∉ Γ | parity v x = 0}`, part I gave: `U`, `V` open, disjoint, `Γᶜ = U ∪ V`, `U` nonempty
bounded, `V` unbounded. This batch: `U` and `V` connected, `frontier U = Γ = frontier V`. Then
`jct_polygon` is the field `PlaneFacts.jct`, and `planeFacts_of_enclose_janiszewski` builds
`PlaneFacts` from the two remaining fields.

**The design: parity does the side-consistency.** Near a point `p` of `Γ` interior to an edge `e`,
a small ball meets `Γ` in a chord and the ball minus the chord is two open half-disks (convex, so
connected), of different parities (the flip across *every* edge, `parity_flip_edge`; part I has it
for non-horizontal edges, and REPORT-batch125 §1 sketches the horizontal case by the vertex-jump
calculus). Near a vertex `w`, the ball minus the two rays is two preconnected pieces
(`ball_diff_rays`, `polygon_local_rays`), each of constant parity; the two half-disks of an edge at
`w` lie in the ball minus `Γ`, have different parities, so **the two pieces have different
parities**, and the odd piece contains the odd half-disk of *both* edges at `w`. So the odd
half-strips of the edges and the odd pieces at the vertices form a cyclic chain of connected sets,
consecutive ones meeting: their union `N₁` is connected, and likewise `N₀`. Every `x ∉ Γ` is joined
to `N₁ ∪ N₀` by a segment in `Γᶜ` (the segment from `x` towards any point of `Γ`, stopped at the
first point of `Γ`), whose parity is that of `x`. Hence `U = ⋃ (segments) ∪ N₁` is connected, and
`V` likewise. No orientation of the polygon is used anywhere.
-/

namespace HPC.Plane

open Set Metric

/-! ### Local structure at an interior point of an edge -/

/-- At a point `p` of the edge `i` that is not a vertex, a small ball meets `Γ` only in the line
of the edge: `ball p ρ ∩ polygonOf v = ball p ρ ∩ segment`, and the segment there is the chord of
the line `L_i` through the edge. -/
theorem polygon_local_chord {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) {p : Pt}
    (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) :
    ∃ ρ > 0, ball p ρ ∩ polygonOf v = ball p ρ ∩ polyEdge v i ∧
      ∀ z ∈ ball p ρ ∩ polyEdge v i,
        ∃ t : ℝ, z = p + t • (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) := by
  sorry

/-- The two open half-disks at `p`: the points of `ball p ρ` strictly on each side of the line of
the edge. (`sideOf p d z := (z - p).1 * d.2 - (z - p).2 * d.1`, the sign of the cross product
with the edge direction `d`.) -/
def halfDisk (p d : Pt) (ρ : ℝ) (s : Bool) : Set Pt :=
  {z | z ∈ ball p ρ ∧ (if s then 0 < (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1
                            else (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 < 0)}

theorem halfDisk_convex (p d : Pt) (ρ : ℝ) (s : Bool) : Convex ℝ (halfDisk p d ρ s) := by
  sorry

theorem halfDisk_nonempty (p d : Pt) (hd : d ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (s : Bool) :
    (halfDisk p d ρ s).Nonempty := by
  sorry

/-- The ball minus the chord is the two half-disks. -/
theorem ball_diff_chord {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) {p : Pt}
    (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) :
    ∃ ρ > 0, ∀ ρ', 0 < ρ' → ρ' ≤ ρ →
      ball p ρ' \ polygonOf v =
        halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ' true ∪
        halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ' false := by
  sorry

/-- **The parity flips across every edge**, horizontal ones included: the two half-disks at a
non-vertex point of an edge have different parities. (Non-horizontal edges: `exists_parity_flip`'s
argument at the given `p`, or move `p` along the edge inside the convex half-disks; horizontal
edges: REPORT-batch125 §1, "Notes for part II": compare `p ± (0, t)` with the vertex-jump
calculus — only the edge itself has exactly one end to the right of `p` at height `p.2`.) -/
theorem parity_flip_edge {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) {p : Pt}
    (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball p ρ ∩ polygonOf v ⊆ polyEdge v i) :
    ∀ z₁ ∈ halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ true,
    ∀ z₂ ∈ halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ false,
      parity v z₁ ≠ parity v z₂ := by
  sorry

/-! ### Local structure at a vertex -/

/-- At a vertex `w = v i`, with `ρ` from `polygon_local_rays`: the ball minus `Γ` is two preconnected
pieces (`ball_diff_rays`) of **different parities**, each piece of constant parity. (The two
half-disks of either edge at `w`, taken at a point of that edge inside the ball and with a radius
inside the ball, lie in the two pieces and have different parities by `parity_flip_edge`.) -/
theorem vertex_two_pieces {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) :
    ∃ ρ > 0, ∃ P₀ P₁ : Set Pt, IsPreconnected P₀ ∧ IsPreconnected P₁ ∧
      ball (v i) ρ \ polygonOf v = P₀ ∪ P₁ ∧
      (∀ z ∈ P₀, parity v z = 0) ∧ (∀ z ∈ P₁, parity v z = 1) ∧
      P₀.Nonempty ∧ P₁.Nonempty := by
  sorry

/-! ### The first hit, and the neighbourhood of `Γ` -/

/-- **The first hit.** From `x ∉ Γ`, the segment towards any `y ∈ Γ` meets `Γ` first at a point `p`:
the half-open segment `[x, p)` lies in `Γᶜ`. (`Γ` closed; `p := x + t₀ • (y − x)` with `t₀` the
infimum of the hitting parameters, attained.) -/
theorem exists_first_hit {n : ℕ} (v : Fin n → Pt) {x : Pt} (hx : x ∉ polygonOf v) (hn : 0 < n) :
    ∃ p ∈ polygonOf v, ∀ t : ℝ, 0 ≤ t → t < 1 → x + t • (p - x) ∉ polygonOf v := by
  sorry

/-- **Every point off `Γ` is joined, inside its parity class, to every ball about a point of `Γ`
of the right parity**: for `x ∉ Γ` there are `p ∈ Γ` and, for every `ρ > 0`, a point `z` of
`ball p ρ \ Γ` with `parity v z = parity v x` and a preconnected subset of `Γᶜ` containing `x`
and `z` (the segment `[x, z]`). -/
theorem exists_segment_to_boundary {n : ℕ} (v : Fin n → Pt) {x : Pt} (hx : x ∉ polygonOf v)
    (hn : 0 < n) :
    ∃ p ∈ polygonOf v, ∀ ρ > 0, ∃ z ∈ ball p ρ \ polygonOf v,
      parity v z = parity v x ∧ segment ℝ x z ⊆ (polygonOf v)ᶜ := by
  sorry

/-- **The parity-`e` neighbourhood of `Γ` is connected.** `N e := ⋃ over the finitely many local
pieces of parity `e`: for each vertex the piece of parity `e` from `vertex_two_pieces`, and for each
edge the half-disks of parity `e` at the points of the edge outside the vertex balls (a compact
sub-segment, covered by finitely many chord balls; consecutive half-disks on the same side meet,
since they are convex and overlap; the last ones meet the vertex pieces). Consecutive pieces of the
cycle meet, so the union is connected. State `N` as you build it; what later steps need is only
this theorem and `N_subset`. -/
def sideNbhd {n : ℕ} (v : Fin n → Pt) (e : ZMod 2) : Set Pt :=
  sorry

theorem sideNbhd_subset {n : ℕ} (v : Fin n → Pt) (e : ZMod 2) :
    sideNbhd v e ⊆ {x | x ∉ polygonOf v ∧ parity v x = e} := by
  sorry

theorem sideNbhd_isConnected {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) :
    IsConnected (sideNbhd v e) := by
  sorry

/-- Every point of `Γ` has, in every ball about it, points of `sideNbhd v e` for both `e`. -/
theorem sideNbhd_near {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) {p : Pt}
    (hp : p ∈ polygonOf v) : ∀ ρ > 0, (ball p ρ ∩ sideNbhd v e).Nonempty := by
  sorry

/-- Every point of `Γᶜ` of parity `e` is joined to `sideNbhd v e` by a segment in `Γᶜ`: the segment
of `exists_segment_to_boundary` ends in a local piece, which lies in `sideNbhd v e` — arrange the
definition of `sideNbhd` so that every point of `ball p ρ \ Γ` of parity `e`, for the local radius
`ρ` at `p`, belongs to it (or join by one more segment inside the convex half-disk / the piece). -/
theorem exists_segment_to_sideNbhd {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) {x : Pt}
    (hx : x ∉ polygonOf v) :
    ∃ z ∈ sideNbhd v (parity v x), segment ℝ x z ⊆ (polygonOf v)ᶜ := by
  sorry

/-! ### The theorem -/

/-- **Each parity class is connected.** -/
theorem isConnected_parity_set {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) :
    IsConnected {x | x ∉ polygonOf v ∧ parity v x = e} := by
  sorry

/-- **The frontier of each parity class is `Γ`.** (`⊆`: the class is open, and closed in `Γᶜ` by
local constancy. `⊇`: `sideNbhd_near` for the class and for the other class.) -/
theorem frontier_parity_set {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) :
    frontier {x | x ∉ polygonOf v ∧ parity v x = e} = polygonOf v := by
  sorry

/-- **The Jordan curve theorem for simple closed polygons** — the field `PlaneFacts.jct`, verbatim.
`U` is the odd parity class, `V` the even one. -/
theorem jct_polygon (J : Set Pt) (hJ : IsSimpleClosedPolygon J) :
    ∃ U V : Set Pt, IsOpen U ∧ IsOpen V ∧ Jᶜ = U ∪ V ∧ Disjoint U V ∧
      IsConnected U ∧ IsConnected V ∧ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      frontier U = J ∧ frontier V = J := by
  sorry

/-- `PlaneFacts` from its two remaining fields. -/
theorem planeFacts_of_enclose_janiszewski
    (henc : ∀ M : Set Pt, Fold.Q78.IsContinuum M → ¬ SeparatesPlane M →
      ∀ G : Set Pt, IsOpen G → M ⊆ G →
        ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ Disjoint J M ∧ M ⊆ polyInterior J ∧
          polyInterior J ⊆ G)
    (hjan : ∀ A B : Set Pt, IsCompact A → IsCompact B →
      (IsConnected (A ∩ B) ∨ A ∩ B = ∅) →
      ∀ x y : Pt, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y → ¬ SeparatesPts (A ∪ B) x y) :
    PlaneFacts :=
  ⟨jct_polygon, henc, hjan⟩

end HPC.Plane
