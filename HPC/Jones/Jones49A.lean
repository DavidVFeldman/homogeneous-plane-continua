import HPC.Jones.Jones49Menger
import HPC.Jones.Jones49Why

/-!
# Batch 149 skeleton: Jones 1949, ingredients (i) and (iv) — order, Menger's theorem on curves of
order 2, simple closed curves are circles, Whyburn's local separating point-order theorem

The batch-149 skeleton (`doc/batches/skeletons/Jones49A-batch149.lean`) is split as follows; every
declaration is verbatim except where a shape change is recorded at the statement.

| item | declaration | file |
|---|---|---|
| A | `OrderLE`, `HasOrder`, `hasOrder_homeomorph` | `Jones49Order.lean` |
| B | `tscc_homeomorph_circle` | `Jones49Circle.lean` |
| C | `menger_order_two`, `jones49_order_two` | `Jones49Menger.lean` |
| D | `IsSepPointOf`, `IsLocalSepPoint`, `whyburn_9_1` (shape change: `hR` dropped) | `Jones49Why.lean` |
| D | `whyburn_9_2`, `jones49_some_order_two` | `Jones49B.lean` (proved in batch 150; open in batch 149) |

This file adds the reduction of `jones49_some_order_two` to `whyburn_9_2`
(`jones49_some_order_two_of_whyburn_9_2`, with the conclusion of (9.2) for the space as a
hypothesis), and the invariance of local separating points under homeomorphisms.

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

section Whyburn

variable {X : Type*} [MetricSpace X]

/-- Separating points of open sets are carried to separating points by homeomorphisms. -/
theorem IsSepPointOf.homeomorph (h : X ≃ₜ X) {p : X} {R : Set X} (hp : IsSepPointOf p R) :
    IsSepPointOf (h p) (h '' R) := by
  obtain ⟨hpR, A, B, hA, hB, hcov, hdisj, hAQ, hBQ⟩ := hp
  have himg : h '' R \ {h p} = h '' (R \ {p}) := by rw [image_diff h.injective, image_singleton]
  have hcomp : connectedComponentIn (h '' R) (h p) \ {h p} =
      h '' (connectedComponentIn R p \ {p}) := by
    rw [← h.image_connectedComponentIn hpR, image_diff h.injective, image_singleton]
  refine ⟨mem_image_of_mem _ hpR, h '' A, h '' B, h.isOpenMap _ hA, h.isOpenMap _ hB, ?_, ?_, ?_,
    ?_⟩
  · rw [himg, ← image_union]; exact image_mono hcov
  · rw [himg, ← image_inter h.injective, ← image_inter h.injective]
    exact (disjoint_image_iff h.injective).2 hdisj
  · rw [hcomp, ← image_inter h.injective]; exact hAQ.image _
  · rw [hcomp, ← image_inter h.injective]; exact hBQ.image _

/-- Local separating points are carried to local separating points by homeomorphisms. -/
theorem IsLocalSepPoint.homeomorph (h : X ≃ₜ X) {p : X} (hp : IsLocalSepPoint p) :
    IsLocalSepPoint (h p) := by
  obtain ⟨R, hR, hpR⟩ := hp
  exact ⟨h '' R, h.isOpenMap _ hR, hpR.homeomorph h⟩

/-- **The consequence Jones uses, from (9.2).** In an uncountable homogeneous compact metric space
with a local separating point, if (9.2) holds for the space, some point has order 2. (By
homogeneity every point is a local separating point, `IsLocalSepPoint.homeomorph`.) -/
theorem jones49_some_order_two_of_whyburn_9_2 [CompactSpace X] [Uncountable X]
    (hX : IsHomogeneous X) {p : X} (hp : IsLocalSepPoint p)
    (h92 : {q : X | IsLocalSepPoint q ∧ ¬ HasOrder q 2}.Countable) : ∃ q : X, HasOrder q 2 := by
  by_contra hno
  push_neg at hno
  have hsub : (univ : Set X) ⊆ {q | IsLocalSepPoint q ∧ ¬ HasOrder q 2} := fun q _ => by
    obtain ⟨g, hg⟩ := hX p q
    exact ⟨hg ▸ hp.homeomorph g, hno q⟩
  exact not_countable_univ (h92.mono hsub)

end Whyburn

end HPC.Jones
