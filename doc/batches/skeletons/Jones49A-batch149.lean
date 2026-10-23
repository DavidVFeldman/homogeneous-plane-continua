import HPC.Jones.Jones55T2

/-!
# Batch 149 skeleton: Jones 1949, ingredients (i) and (iv) — order, Menger's theorem on curves of
order 2, simple closed curves are circles, Whyburn's local separating point-order theorem

Save as `HPC/Jones/Jones49A.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49A` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Sources (page images, 150–200 dpi):
* K. Menger, *Kurventheorie* (1932; 2nd ed. Chelsea 1967, same pagination), p. 267, "Theorem über die
  Kurven zweiter Ordnung. Eine Kurve zweiter Ordnung ist ein Bogen oder ein topologischer Kreis, d. h.
  entweder mit einer Strecke oder mit einer Kreislinie homöomorph. Die Bogen sind unter den
  Kontinua dadurch gekennzeichnet, daß sie, abgesehen von zwei Endpunkten, nur Punkte zweiter
  Ordnung besitzen, die topologischen Kreise dadurch, daß sie nur Punkte zweiter Ordnung
  enthalten." (`doc/sources/menger-kurventheorie.pdf`, PDF p. 275.)
* G. T. Whyburn, *Analytic Topology* (1942), Ch. III §9, p. 61: definition of local separating
  point; (9.1); "(9.2) LOCAL SEPARATING POINT-ORDER THEOREM. All save a countable number of the local
  separating points of any locally compact separable metric space `L` are points of order 2 of `L`."
  (`doc/sources/whyburn1942.pdf`, PDF p. 75.) Jones 1949 cites it as "Theorem 9.1, p. 61".
* Jones 1949 (`doc/sources/jones1949.pdf`), p. 113: "If a point of `M` is of order 2 in `M`, then `M`
  is a simple closed curve [4]."
-/

namespace HPC.Jones

open Set Topology Metric

section Order

variable {X : Type*} [TopologicalSpace X]

/-- **Menger–Urysohn order `≤ n`**: `p` has arbitrarily small open neighbourhoods whose frontier has
at most `n` points. Check against Menger (*Kurventheorie*, Ch. IV) and Whyburn (Ch. III §2, p. 48)
and record any difference. -/
def OrderLE (p : X) (n : ℕ) : Prop :=
  ∀ U ∈ 𝓝 p, ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ (frontier V).Finite ∧ (frontier V).ncard ≤ n

/-- `p` is a point **of order `n`**: order `≤ n` and not `≤ n − 1`. -/
def HasOrder (p : X) (n : ℕ) : Prop := OrderLE p n ∧ ∀ m < n, ¬ OrderLE p m

/-- Order is a topological invariant. -/
theorem hasOrder_homeomorph {Y : Type*} [TopologicalSpace Y] (h : X ≃ₜ Y) {p : X} {n : ℕ} :
    HasOrder p n ↔ HasOrder (h p) n := by
  sorry

end Order

/-! ## (i) Simple closed curves are circles; Menger's theorem -/

/-- A topological simple closed curve (two arcs with only their ends in common, batch 138's
`Gen.TSCC`) in a Hausdorff space is homeomorphic to `Circle`. The converse is batch 148's
`tscc_circle`. -/
theorem tscc_homeomorph_circle {X : Type*} [TopologicalSpace X] [T2Space X] {J : Set X}
    (hJ : HPC.Moore.Gen.TSCC J) : Nonempty (J ≃ₜ Circle) := by
  sorry

/-- **Menger, p. 267 (the circle half):** a nondegenerate compact metric continuum all of whose
points are of order 2 is homeomorphic to a circle. -/
theorem menger_order_two {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] (h : ∀ p : X, HasOrder p 2) : Nonempty (X ≃ₜ Circle) := by
  sorry

/-- **Jones 1949, p. 113, first sentence of the proof:** "If a point of `M` is of order 2 in `M`,
then `M` is a simple closed curve [4]" — with `M` homogeneous (the hypothesis of Theorem 1 that makes
Menger's "all points" follow from "a point"). -/
theorem jones49_order_two {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] (hX : IsHomogeneous X) {p : X} (hp : HasOrder p 2) : Nonempty (X ≃ₜ Circle) := by
  sorry

/-! ## (iv) Whyburn's local separating point-order theorem -/

section Whyburn

variable {X : Type*} [MetricSpace X]

/-- Whyburn's *separating point of an open set `R`* (p. 61, as used in the proof of (9.1)): there is
a separation `R − p = R_a + R_b` (disjoint, relatively open in `R − p`) with `a ∈ R_a`, `b ∈ R_b`
both in the component of `R` containing `p`. Record the reading. -/
def IsSepPointOf (p : X) (R : Set X) : Prop :=
  p ∈ R ∧ ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ R \ {p} ⊆ A ∪ B ∧
    Disjoint (A ∩ (R \ {p})) (B ∩ (R \ {p})) ∧
    (A ∩ (connectedComponentIn R p \ {p})).Nonempty ∧
    (B ∩ (connectedComponentIn R p \ {p})).Nonempty

/-- Whyburn's *local separating point* (p. 61): "a separating point of some open set in `L`". -/
def IsLocalSepPoint (p : X) : Prop := ∃ R, IsOpen R ∧ IsSepPointOf p R

/-- **Whyburn (9.1).** "If `p` is a separating point of an open set `R` in `L` then it is also of
every open set `U` such that `p ⊂ U ⊂ R`." -/
theorem whyburn_9_1 [LocallyCompactSpace X] {p : X} {R U : Set X} (hR : IsOpen R)
    (hU : IsOpen U) (hpU : p ∈ U) (hUR : U ⊆ R) (h : IsSepPointOf p R) : IsSepPointOf p U := by
  sorry

/-- **Whyburn (9.2), the local separating point-order theorem.** In a locally compact separable
metric space, all but countably many local separating points are of order 2. (Through (8.4),
(8.41), and the non-separated cuttings of Ch. III §§2, 8; or directly for what Jones needs, see
`jones49_some_order_two`.) -/
theorem whyburn_9_2 [LocallyCompactSpace X] [TopologicalSpace.SeparableSpace X] :
    {p : X | IsLocalSepPoint p ∧ ¬ HasOrder p 2}.Countable := by
  sorry

/-- What Jones 1949 uses (end of Case 2): in an uncountable homogeneous compact metric continuum
with a local separating point, some point has order 2. -/
theorem jones49_some_order_two [CompactSpace X] [ConnectedSpace X] [Uncountable X]
    (hX : IsHomogeneous X) {p : X} (hp : IsLocalSepPoint p) : ∃ q : X, HasOrder q 2 := by
  sorry

end Whyburn

end HPC.Jones
