import HPC.Plane.Tree67

/-!
# Batch 118: Bing 1951 (Duke), Theorem 6 relative to `PlaneFacts`

Skeleton (save as `HPC/Plane/Tree6.lean`; add `import HPC.Plane.Tree6` at the end of the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. No existing file is to be edited, except the audit.

The second and third paragraphs of Bing's proof (COMMISSION-batch117.md §1), relative to the
interface `PlaneFacts` (with its compact form of Janiszewski, batch 117). Plan:

1. polygonal arcs in connected open sets, and simple ones by loop erasure;
2. a simple closed polygon threaded through a circular chain of connected open sets
   (`p_1 p_2 ⋯ p_m p_1`, `p_i p_{i+1} ⊆ h_i`, consecutive arcs trimmed to meet only at `p_{i+1}`);
3. from `jct`: a connected unbounded set missing a simple closed polygon misses its interior;
   the interior is two-sided along the polygon — the points of the interior near an arc `α ⊆ Γ`
   lying in an open `h ⊇ α` form a connected set with `α` in its closure (`sides`);
4. **the point `q`** (Bing: "a boundary point of `h_1`, a boundary point of `h_2`, and a boundary
   point of `h_1 · h_2`" inside the curve), from `jct` and `janiszewski` — the one real use of the
   interface beyond `enclose`;
5. Theorem 6.
-/

namespace HPC.Plane

open Set Metric

/-! ### Polygonal arcs -/

/-- A **polygonal arc** from `p` to `q` with vertex list `w` (`p = w.head`, `q = w.getLast`): the
union of the segments between consecutive vertices. -/
def polyPathOf (w : List Pt) : Set Pt :=
  ⋃ i ∈ Finset.range (w.length - 1), segment ℝ (w.getD i 0) (w.getD (i + 1) 0)

/-- A **simple polygonal arc** from `p` to `q`: a vertex list with distinct vertices, `p ≠ q`,
adjacent segments meeting only at their common vertex, non-adjacent ones disjoint. -/
def IsSimplePolyArc (α : Set Pt) (p q : Pt) : Prop :=
  ∃ w : List Pt, 2 ≤ w.length ∧ w.Nodup ∧ w.head? = some p ∧ w.getLast? = some q ∧
    α = polyPathOf w ∧
    ∀ i j, i < j → j < w.length - 1 →
      segment ℝ (w.getD i 0) (w.getD (i + 1) 0) ∩ segment ℝ (w.getD j 0) (w.getD (j + 1) 0) ⊆
        if j = i + 1 then {w.getD j 0} else ∅

/-- A connected open set of the plane is polygonally connected. -/
theorem exists_polyPath_of_isConnected {h : Set Pt} (ho : IsOpen h) (hc : IsConnected h)
    {p q : Pt} (hp : p ∈ h) (hq : q ∈ h) :
    ∃ w : List Pt, w.head? = some p ∧ w.getLast? = some q ∧ polyPathOf w ⊆ h := by
  sorry

/-- **Loop erasure**: a polygonal path from `p` to `q ≠ p` contains a simple polygonal arc from
`p` to `q`. -/
theorem exists_simplePolyArc_of_polyPath {w : List Pt} {p q : Pt} (hp : w.head? = some p)
    (hq : w.getLast? = some q) (hpq : p ≠ q) :
    ∃ α, IsSimplePolyArc α p q ∧ α ⊆ polyPathOf w := by
  sorry

/-- A simple polygonal arc is compact and connected. -/
theorem IsSimplePolyArc.isContinuum {α : Set Pt} {p q : Pt} (h : IsSimplePolyArc α p q) :
    Fold.Q78.IsContinuum α := by
  sorry

/-- The initial part of a simple polygonal arc up to a point of it is a simple polygonal arc
(or the point itself), and the final part from it likewise. -/
theorem IsSimplePolyArc.split {α : Set Pt} {p q : Pt} (h : IsSimplePolyArc α p q) {x : Pt}
    (hx : x ∈ α) (hxp : x ≠ p) (hxq : x ≠ q) :
    ∃ α₁ α₂, IsSimplePolyArc α₁ p x ∧ IsSimplePolyArc α₂ x q ∧ α₁ ∪ α₂ = α ∧ α₁ ∩ α₂ = {x} := by
  sorry

/-- **The first point of a simple arc in a closed set** (walking from `p`): the arc up to it
meets the set only there. -/
theorem IsSimplePolyArc.exists_first_mem {α : Set Pt} {p q : Pt} (h : IsSimplePolyArc α p q)
    {K : Set Pt} (hK : IsClosed K) (hne : (α ∩ K).Nonempty) (hp : p ∉ K) :
    ∃ x ∈ α ∩ K, ∃ α₁, IsSimplePolyArc α₁ p x ∧ α₁ ⊆ α ∧ α₁ ∩ K = {x} := by
  sorry

/-! ### Threading a simple closed polygon through a circular chain -/

/-- A simple closed polygon decomposed into arcs: `Γ = ⋃ α i`, `α i` a simple polygonal arc from
`p i` to `p (i+1)` (indices mod `m`), consecutive arcs meeting only at their common end, others
disjoint. -/
def IsThreaded {m : ℕ} (Γ : Set Pt) (p : Fin m → Pt) (α : Fin m → Set Pt) : Prop :=
  2 < m ∧ Γ = ⋃ i, α i ∧ Function.Injective p ∧
    (∀ i, IsSimplePolyArc (α i) (p i) (p ⟨(i.val + 1) % m, Nat.mod_lt _ (Fin.pos i)⟩)) ∧
    (∀ i, α i ∩ α ⟨(i.val + 1) % m, Nat.mod_lt _ (Fin.pos i)⟩ =
      {p ⟨(i.val + 1) % m, Nat.mod_lt _ (Fin.pos i)⟩}) ∧
    ∀ i j, i ≠ j → (i.val + 1) % m ≠ j.val → (j.val + 1) % m ≠ i.val → Disjoint (α i) (α j)

/-- A threaded polygon is a simple closed polygon. -/
theorem IsThreaded.isSimpleClosedPolygon {m : ℕ} {Γ : Set Pt} {p : Fin m → Pt}
    {α : Fin m → Set Pt} (h : IsThreaded Γ p α) : IsSimpleClosedPolygon Γ := by
  sorry

/-- **Threading** (Bing: "Let `p_1 p_2 ⋯ p_m p_1` be a simple closed curve such that `p_1 p_2` lies
in `h_1`, …, `p_m p_1` lies in `h_m`"). For a circular chain `d 0, …, d (m-1)` (`m > 2`) of
*connected* open sets there are points `p i ∈ d (i-1) ∩ d i` and arcs `α i ⊆ d i` threading a
simple closed polygon. Choose `p i`, polygonal arcs in each `d i` (item 1), make each simple
(loop erasure), then trim consecutive arcs: cut `α i` at its first point on `α (i+1)` and start
`α (i+1)` there (`exists_first_mem`); non-consecutive arcs are disjoint because the links are. -/
theorem exists_threaded {m : ℕ} (hm : 2 < m) (d : Fin m → Set Pt) (hopen : ∀ i, IsOpen (d i))
    (hconn : ∀ i, IsConnected (d i))
    (hcirc : ∀ i j : Fin m, (d i ∩ d j).Nonempty ↔
      (((i : ℤ) - j).natAbs ≤ 1 ∨ (i.val = 0 ∧ j.val = m - 1) ∨ (j.val = 0 ∧ i.val = m - 1))) :
    ∃ (Γ : Set Pt) (p : Fin m → Pt) (α : Fin m → Set Pt), IsThreaded Γ p α ∧ ∀ i, α i ⊆ d i := by
  sorry

/-! ### Consequences of `jct` -/

/-- A connected unbounded set missing a compact `J` misses `polyInterior J` (it lies in one
component of `Jᶜ`, which is unbounded; the interior is the union of the bounded ones). No
Jordan curve theorem is needed. -/
theorem polyInterior_disjoint_of_unbounded {J W : Set Pt} (hW : IsConnected W)
    (hWu : ¬ Bornology.IsBounded W) (hWJ : Disjoint W J) : Disjoint W (polyInterior J) := by
  sorry

/-- **Local two-sidedness** (from `jct` and the geometry of a polygon): at every point `w` of a
simple closed polygon `Γ`, for all small radii the part of the interior in the ball about `w` is
nonempty and connected. (A small ball about `w` meets `Γ` in one segment, or in two segments
from `w` when `w` is a vertex, and is cut by them into two connected pieces; each piece lies in
one component of `Γᶜ`; `w` is a frontier point of both `U` and the exterior, so one piece is in
`U` and the other in the exterior.) *If this resists, state it as an added field of a
`PlaneFacts'` and record the change.* -/
theorem PlaneFacts.local_side (hPF : PlaneFacts) {Γ : Set Pt} (hΓ : IsSimpleClosedPolygon Γ)
    {w : Pt} (hw : w ∈ Γ) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ →
      (polyInterior Γ ∩ ball w r).Nonempty ∧ IsConnected (polyInterior Γ ∩ ball w r) := by
  sorry

/-- **Two-sidedness along an arc**: if `α ⊆ Γ` is connected and `h ⊇ α` is open, the points of
`U ∩ h` near `α` form a connected set `S` with `α ⊆ closure S`, and for a chosen `w ∈ α` the set
`S` contains the local piece `U ∩ ball w r` for some `r > 0`. (Finitely many balls of
`local_side`, small enough to lie in `h`, cover the compact `α`; the `U`-pieces of two balls
meeting at a point `w'` of `α` both contain the piece of a smaller ball about `w'`, hence meet;
`α` connected makes the union of the pieces connected.) -/
theorem PlaneFacts.sides (hPF : PlaneFacts) {Γ : Set Pt} (hΓ : IsSimpleClosedPolygon Γ)
    {α h : Set Pt} (hα : α ⊆ Γ) (hαc : IsConnected α) (hαcl : IsClosed α) (ho : IsOpen h)
    (hαh : α ⊆ h) {w : Pt} (hw : w ∈ α) :
    ∃ r > 0, ∃ S : Set Pt, IsConnected S ∧ S ⊆ polyInterior Γ ∩ h ∧ α ⊆ closure S ∧
      polyInterior Γ ∩ ball w r ⊆ S ∧ (polyInterior Γ ∩ ball w r).Nonempty := by
  sorry

/-! ### The point `q` -/

/-- **Bing's point `q`.** Let `Γ` be a simple closed polygon decomposed into three arcs
`α₁` (from `p₁` to `p₂`), `α₂` (from `p₂` to `p₃`) and `β` (from `p₃` to `p₁`) — connected closed
sets with `α₁ ∪ α₂ ∪ β = Γ`, `α₁ ∩ α₂ = {p₂}`, `α₂ ∩ β = {p₃}`, `β ∩ α₁ = {p₁}`, the `p`'s
distinct. Let `h₁ ⊇ α₁`, `h₂ ⊇ α₂`, `V ⊇ β` be open with `V ∩ h₁ ∩ h₂ = ∅`. Then some point `q`
of the interior of `Γ` is a frontier point of `h₁`, of `h₂`, and lies in the closure of `h₁ ∩ h₂`.

Proof from `jct` and `janiszewski`. By `sides` (applied to `α₁ ⊆ h₁` at `w = p₂` and at `w = p₁`,
to `α₂ ⊆ h₂` at `p₂` and `p₃`, to `β ⊆ V` at `p₃` and `p₁` — one connected `S` per arc, containing
the local pieces at both its ends: apply `sides` at one end and enlarge by the local piece at the
other, which meets `S`), there are connected `S₁ ⊆ U ∩ h₁`, `S₂ ⊆ U ∩ h₂`, `S_V ⊆ U ∩ V` whose
closures contain `α₁`, `α₂`, `β`, with `x ∈ S₁ ∩ S₂` (a point of the local piece at `p₂`, radius
below both), `y ∈ S₂ ∩ S_V` (at `p₃`), `z ∈ S₁ ∩ S_V` (at `p₁`). Let `C` be the component
of `U ∩ h₁ ∩ h₂` containing `x`, `A := closure C ∩ frontier h₁`, `B := closure C ∩ frontier h₂`
(compact). Suppose no `q`. Then `A ∩ B = ∅`: a common point in `U` would be a `q`; a common point
on `Γ` lies in `β ⊆ V` (not in `α₁ ∪ α₂ ⊆ h₁ ∪ h₂`, as it is a frontier point of both), and `V`
is an open set missing `h₁ ∩ h₂`, so it is not in `closure C`.
* `A ∪ B ∪ Γ` separates `x` from `y`: a path from `x` to `y` missing `Γ` stays in `U`, and `y ∉
  closure C` (`y ∉ closure h₁` because `y ∈ V ∩ h₂`, an open set missing `h₁`), so the path leaves
  `C` through `frontier C ∩ U ⊆ A ∪ B`.
* `B ∪ Γ` does not separate `x` from `y`: `S₂ ⊆ U ∩ h₂` is connected, contains both, and misses
  `B ⊆ frontier h₂` and `Γ`.
* `janiszewski` with `A ∪ Γ`, `B ∪ Γ` (compact, intersection `Γ`, connected): so `A ∪ Γ`
  separates `x` from `y`.
* `A ∪ Γ` does not separate `x` from `z` (`S₁`), hence separates `z` from `y`.
* But `S_V ⊆ U ∩ V` is connected, contains `y` and `z`, and misses `Γ` and `A` (`A ⊆ closure (h₁ ∩
  h₂)` and `V` is open missing `h₁ ∩ h₂`). Contradiction. -/
theorem PlaneFacts.exists_theta_point (hPF : PlaneFacts) {Γ α₁ α₂ β : Set Pt} {p₁ p₂ p₃ : Pt}
    (hΓ : IsSimpleClosedPolygon Γ) (hdec : α₁ ∪ α₂ ∪ β = Γ)
    (h₁c : IsConnected α₁) (h₂c : IsConnected α₂) (hβc : IsConnected β)
    (h₁₂ : α₁ ∩ α₂ = {p₂}) (h₂β : α₂ ∩ β = {p₃}) (hβ₁ : β ∩ α₁ = {p₁})
    (hp : p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃)
    {h₁ h₂ V : Set Pt} (ho₁ : IsOpen h₁) (ho₂ : IsOpen h₂) (hoV : IsOpen V)
    (hα₁ : α₁ ⊆ h₁) (hα₂ : α₂ ⊆ h₂) (hβ : β ⊆ V) (hV : V ∩ h₁ ∩ h₂ = ∅) :
    ∃ q ∈ polyInterior Γ, q ∈ frontier h₁ ∧ q ∈ frontier h₂ ∧ q ∈ closure (h₁ ∩ h₂) := by
  sorry

/-! ### Theorem 6 -/

/-- Components of `d₀ ∩ d` for `d` in the cover. -/
def compFamily (d₀ : Set Pt) (D : Finset (Set Pt)) : Set (Set Pt) :=
  {h | ∃ d ∈ D, ∃ x ∈ d₀ ∩ d, h = connectedComponentIn (d₀ ∩ d) x}

/-- **No three members of `compFamily` share a point** (distinct components of one `d₀ ∩ d` are
disjoint; components of three distinct `d`'s would give a triple point of `D`). -/
theorem compFamily_no_triple {d₀ : Set Pt} {D : Finset (Set Pt)}
    (hD : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅)
    {h₁ h₂ h₃ : Set Pt} (hh₁ : h₁ ∈ compFamily d₀ D) (hh₂ : h₂ ∈ compFamily d₀ D)
    (hh₃ : h₃ ∈ compFamily d₀ D) (h12 : h₁ ≠ h₂) (h23 : h₂ ≠ h₃) (h13 : h₁ ≠ h₃) :
    h₁ ∩ h₂ ∩ h₃ = ∅ := by
  sorry

/-- **No circular chain in `compFamily`** (the third paragraph): a circular chain `h_1, …, h_m`
of members, threaded by a simple closed polygon `Γ` (`exists_threaded`; the members are connected
open sets), with `β := α₃ ∪ ⋯ ∪ α_m ⊆ V := h₃ ∪ ⋯ ∪ h_m`, `V ∩ h₁ ∩ h₂ = ∅` (no triple); the
interior of `Γ` lies in `d₀` (`polyInterior_disjoint_of_unbounded` for `W = d₀ᶜ`, which is
connected and unbounded by `jct` and misses `Γ ⊆ d₀`); `exists_theta_point` gives `q ∈ d₀`, so
`q ∈ d` for some `d ∈ D`; `q ∈ closure (h₁ ∩ h₂)` makes `d` meet `d_a ∩ d_b` (`h₁ ⊆ d_a`,
`h₂ ⊆ d_b`, `a ≠ b`), so `d ∈ {d_a, d_b}`; but then `q ∈ d₀ ∩ d_a` is in the closure of the
component `h₁` of that open set and hence in `h₁`, contradicting `q ∈ frontier h₁`. -/
theorem compFamily_no_circular (hPF : PlaneFacts) {J : Set Pt} (hJ : IsSimpleClosedPolygon J)
    {D : Finset (Set Pt)} (hopen : ∀ d ∈ D, IsOpen d)
    (hD : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅)
    (hcov : polyInterior J ⊆ ⋃ d ∈ D, d) (G : Finset (Set Pt))
    (hG : ∀ h ∈ G, h ∈ compFamily (polyInterior J) D) : ¬ IsCircularChain G := by
  sorry

/-- **Bing 1951 (Duke), Theorem 6**, relative to `PlaneFacts`: a bounded plane continuum
containing no continuum that separates the plane is tree-like. -/
theorem theorem6_1951 (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) : IsTreeLike M := by
  sorry

end HPC.Plane
