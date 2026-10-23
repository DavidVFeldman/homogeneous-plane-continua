import HPC.Jones.Jones49D

/-!
# Batch 153 skeleton: Whyburn 1939, §14 Corollary 1 — boundaries of complementary domains of a
compact semi-locally-connected cyclic plane continuum are simple closed curves

Save as `HPC/Jones/Jones49E.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49E` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Source: Whyburn, *Semi-locally-connected sets*, Amer. J. Math. 61 (1939), p. 749: "COROLLARY 1. If
`M` is a compact plane semi-locally-connected cyclic continuum, the boundary of every complementary
domain of `M` is a simple closed curve." (Stated without proof; footnote 16 refers to Wilder 1938,
Theorem 8a, first corollary.) Route: REPORT-batch150 §5 (d) and REPORT-batch152 §8. *Cyclic*: no cut
points.

Jones 1949 (p. 113) uses it as "Hence each element of `G` is a simple domain [6, 7]. Let the simple
closed curve `J` denote the boundary of an element `D` of `G`."
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane HPC.Moore.Gen

/-- A simple polygonal arc is a topological arc (bridge from `IsSimplePolyArc` to `TArc`). -/
theorem tarc_of_isSimplePolyArc {α : Set Pt} {p q : Pt} (h : IsSimplePolyArc α p q) :
    TArc p q α := by
  sorry

/-- **The arc theorem for Peano continua** (Moore–Mazurkiewicz; e.g. Whyburn, *Analytic Topology*,
Ch. II; Nadler 8.23): two distinct points of a locally connected compact connected metric space are
joined by an arc. -/
theorem exists_tarc_of_locallyConnected {X : Type*} [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyConnectedSpace X] {a b : X} (hab : a ≠ b) :
    ∃ C : Set X, TArc a b C := by
  sorry

/-- **Accessibility.** For `M` compact, connected, semi-locally connected and cyclic, every boundary
point `p` of a complementary domain `R` is the end of an arc from any point of `R` lying, except
for `p`, in `R`. -/
theorem accessible_of_cyclic {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt}
    (hx : x ∉ M) {p : Pt} (hp : p ∈ frontier (connectedComponentIn Mᶜ x)) {y : Pt}
    (hy : y ∈ connectedComponentIn Mᶜ x) (hyp : y ≠ p) :
    ∃ C : Set Pt, TArc y p C ∧ C \ {p} ⊆ connectedComponentIn Mᶜ x := by
  sorry

/-- **The boundary is cyclic.** Every cut point of `B = ∂R` is a cut point of `M` (via accessibility
and `jordan_curve_theorem`); `M` is cyclic. -/
theorem frontier_cyclic {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt}
    (hx : x ∉ M) :
    ∀ z : frontier (connectedComponentIn Mᶜ x),
      IsConnected ({z}ᶜ : Set (frontier (connectedComponentIn Mᶜ x))) := by
  sorry

/-- **A θ-curve in a cyclic Peano continuum that is not a circle.** *Shape left to you* (three arcs
with common ends and pairwise only the ends in common). Or, if the plane route of REPORT-batch152 §8
(every point of `B` of order 2, then `menger_order_two`) proves shorter, replace this item by that
and record why. -/
theorem theta_of_cyclic_peano : True := by
  sorry

/-- **Whyburn 1939, Corollary 1.** -/
theorem whyburn39_corollary1 {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    (hS : ∀ z : M, SemiLocConnAt z) (hcyc : ∀ z : M, IsConnected ({z}ᶜ : Set M)) {x : Pt}
    (hx : x ∉ M) : Nonempty (frontier (connectedComponentIn Mᶜ x) ≃ₜ Circle) := by
  sorry

end HPC.Jones
