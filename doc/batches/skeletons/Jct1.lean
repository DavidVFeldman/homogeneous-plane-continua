import HPC.Plane.Tree7Comp
import HPC.Fold.Theorem4Only

/-!
# Batch 125: the Jordan curve theorem for simple closed polygons, part I — crossing parity;
# and Theorem 4 as printed with at least four coarse links

Skeleton. Every `sorry` is a work item; shapes may be adjusted with the change recorded. Save as
`HPC/Plane/Jct1.lean`, add `import HPC.Plane.Jct1` at the end of the root `HPC.lean`.

## Part I of `jct`

The field `PlaneFacts.jct` asks, for a simple closed polygon `Γ`: `Γᶜ = U ∪ V` with `U`, `V` open,
disjoint, connected, `U` bounded, `V` unbounded, `frontier U = Γ = frontier V`. The route is the
**parity of the number of crossings of the eastward ray** from `x` with `Γ`, by the half-open
rule: an edge from `a` to `b` is counted iff the heights of `a` and `b` straddle `x.2` half-openly
(`a.2 ≤ x.2 < b.2` or `b.2 ≤ x.2 < a.2`) and the point of the edge at height `x.2` lies strictly
to the right of `x`. This rule is defined for every `x ∉ Γ` with no general-position hypothesis:
horizontal edges are never counted, and at the height of a vertex the half-open convention counts
exactly the right number of the two edges there (both or neither if the edges leave the vertex on
the same side of the horizontal, exactly one if on opposite sides), which is what makes the parity
locally constant. This batch proves:

1. the parity is locally constant on `Γᶜ`, hence constant on preconnected subsets of `Γᶜ`;
2. it is `0` far to the east (and hence on the whole unbounded component of a far point);
3. it flips across every non-horizontal edge, and a simple closed polygon has such an edge;
   hence `Γᶜ` is not connected, and the set of odd parity is nonempty and bounded.

Part II (batch 126): at most two components, `frontier U = frontier V = Γ`; assembly of `jct`.

Conventions: `Pt = ℝ × ℝ`; `polygonOf`, `polyEdge`, `IsSimpleVertices`, `isSimpleClosedPolygon_iff`
from `Tree67`/`Tree7`.
-/

namespace HPC.Plane

open Set

/-! ### Crossing parity -/

/-- **The half-open east-ray crossing rule** for the segment from `a` to `b` and the point `x`:
the heights straddle `x.2` half-openly, and the point of the segment at height `x.2` is strictly to
the right of `x`. -/
def CrossesEast (x a b : Pt) : Prop :=
  ((a.2 ≤ x.2 ∧ x.2 < b.2) ∨ (b.2 ≤ x.2 ∧ x.2 < a.2)) ∧
    x.1 < a.1 + (x.2 - a.2) * (b.1 - a.1) / (b.2 - a.2)

open scoped Classical in
/-- The number of edges of the closed polygon `v` crossed by the east ray from `x`. -/
noncomputable def crossCount {n : ℕ} (v : Fin n → Pt) (x : Pt) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    CrossesEast x (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)).card

/-- The crossing parity. -/
noncomputable def parity {n : ℕ} (v : Fin n → Pt) (x : Pt) : ZMod 2 := (crossCount v x : ZMod 2)

/-- The rule is symmetric in the ends of the segment (the two disjuncts swap; the crossing
abscissa is the same point of the line). -/
theorem crossesEast_comm (x a b : Pt) : CrossesEast x a b ↔ CrossesEast x b a := by
  sorry

/-- A crossed segment meets the open east ray from `x` at the point of height `x.2`; in particular
`x ∉ segment ℝ a b` is not needed for the definition, but a point *on* the segment at height `x.2`
is never strictly to its own right: `x ∈ segment ℝ a b → ¬ CrossesEast x a b`. -/
theorem not_crossesEast_of_mem {x a b : Pt} (hx : x ∈ segment ℝ a b) : ¬ CrossesEast x a b := by
  sorry

/-- **Local constancy of a single edge's indicator away from the edge and away from the heights of
its ends.** If `x ∉ segment ℝ a b` and `x.2 ≠ a.2`, `x.2 ≠ b.2`, the indicator of `CrossesEast · a b`
is constant near `x`. -/
theorem crossesEast_locallyConstant_of_ne {x a b : Pt} (hx : x ∉ segment ℝ a b) (ha : x.2 ≠ a.2)
    (hb : x.2 ≠ b.2) :
    ∃ ε > 0, ∀ y, dist y x < ε → (CrossesEast y a b ↔ CrossesEast x a b) := by
  sorry

/-- **The vertex rule.** At a vertex `w = v i` of height `x.2` (with `x ≠ w`, `x ∉ Γ`), the two
edges at `w` (from `v (i−1)` to `w` and from `w` to `v (i+1)`) contribute, near `x`, a locally
constant parity: if the other ends of the two edges lie strictly on the same side of the
horizontal through `w`, both indicators switch together as `y.2` crosses the height; if on opposite
sides, exactly one of them is on at every `y` near `x` (half-open rule); a horizontal edge at `w`
contributes nothing and the rule passes to the next non-horizontal edge along the polygon. (State
and prove the version you need for `parity_locallyConstant`; the cleanest form may be a lemma on
*maximal horizontal runs* of the polygon: the sum of the indicators of the edges of a run and of
the two non-horizontal edges bounding it is locally constant in parity near any `x` off `Γ`.) -/
theorem vertex_rule_placeholder : True := trivial

/-- **The parity is locally constant on `Γᶜ`.** -/
theorem parity_locallyConstant {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) {x : Pt}
    (hx : x ∉ polygonOf v) : ∃ ε > 0, ∀ y, dist y x < ε → parity v y = parity v x := by
  sorry

/-- Parity is constant on preconnected subsets of `Γᶜ`. -/
theorem parity_eq_of_isPreconnected {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) {S : Set Pt}
    (hS : IsPreconnected S) (hSΓ : S ⊆ (polygonOf v)ᶜ) {x y : Pt} (hx : x ∈ S) (hy : y ∈ S) :
    parity v x = parity v y := by
  sorry

/-- **Parity is `0` far to the east**: beyond the largest abscissa of a vertex no edge is crossed. -/
theorem parity_far {n : ℕ} (v : Fin n → Pt) : ∃ R : ℝ, ∀ x : Pt, R < x.1 → parity v x = 0 := by
  sorry

/-- Hence parity is `0` on the complement of a large closed ball (which is connected: the
complement of a sup-metric ball is a union of four half-planes, `isConnected_compl_closedBall_pt`
of `Tree7Star`). -/
theorem parity_eq_zero_of_far {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) :
    ∃ R : ℝ, ∀ x : Pt, R < dist x 0 → parity v x = 0 := by
  sorry

/-- **Parity flips across a non-horizontal edge.** For `p` in the relative interior of a
non-horizontal edge `i` (not a vertex, `(v i).2 ≠ (v (i+1)).2`), the points `p ± t • (1, 0)` for
small `t > 0` are off `Γ` and have different parities: the edge `i` itself is crossed from the left
point and not from the right one, and every other edge's indicator is the same at both (they are
at positive distance from `p`, and `p.2` is not the height of a vertex unless … — handle the case
where `p.2` is the height of some vertex of another edge by moving `p` slightly along the edge,
which keeps it in the relative interior; the statement only needs *some* such `p` on the edge). -/
theorem exists_parity_flip {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n)
    (hne : (v i).2 ≠ (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).2) :
    ∃ p ∈ polyEdge v i, ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      (p.1 - t, p.2) ∉ polygonOf v ∧ (p.1 + t, p.2) ∉ polygonOf v ∧
      parity v (p.1 - t, p.2) ≠ parity v (p.1 + t, p.2) := by
  sorry

/-- A simple closed polygon has a non-horizontal edge (three distinct vertices cannot all lie on
one horizontal line with the edges meeting only at common vertices: on a line, three points in
cyclic order give a middle point lying in the segment of the other two…; more simply, if all edges
were horizontal all vertices would have the same height, and the edge from the leftmost vertex to
its successor and the edge from the rightmost to its successor cannot both avoid overlaps). -/
theorem exists_nonhorizontal_edge {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) :
    ∃ i : Fin n, (v i).2 ≠ (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).2 := by
  sorry

/-- **The complement of a simple closed polygon is not connected**, and the odd-parity set is a
nonempty bounded open set, the even-parity set a nonempty open set containing the complement of a
ball. -/
theorem polygon_separates {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) :
    ¬ IsConnected (polygonOf v)ᶜ ∧
      IsOpen {x | x ∉ polygonOf v ∧ parity v x = 1} ∧
      {x | x ∉ polygonOf v ∧ parity v x = 1}.Nonempty ∧
      Bornology.IsBounded {x | x ∉ polygonOf v ∧ parity v x = 1} ∧
      IsOpen {x | x ∉ polygonOf v ∧ parity v x = 0} ∧
      ∃ R : ℝ, ∀ x : Pt, R < dist x 0 → x ∈ {x | x ∉ polygonOf v ∧ parity v x = 0} := by
  sorry

end HPC.Plane

/-! ## Theorem 4 as printed, at least four coarse links -/

namespace HPC.Fold

open HPC.Chain

/-- **Bing's Theorem 4 as printed, `k ≥ 4`** (`Theorem4LiteralGe4`): the two-link form with the
only-clauses at both ends. (REPORT-batch124 Q3: the pair form of Theorem 3 at both ends at once —
a pair version of `two_core` for `K ≥ 5`, where the companions sit at `hh + 1` / `kk − 1`; a new
grouping at `K = 4`; the companions coincide only for `m ≤ 4`, i.e. here only at `K = 4` with
`s = r + 2`.) -/
theorem theorem4_literal_ge4 {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 4 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧ OnlyIn E β hβ r ∧ OnlyIn E β hβ s ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2 := by
  sorry

theorem theorem4LiteralGe4_holds : Theorem4LiteralGe4 :=
  fun _ _ _ _ hk _ _ hcr r s hrs hlow hhigh => theorem4_literal_ge4 hk hcr r s hrs hlow hhigh

end HPC.Fold
