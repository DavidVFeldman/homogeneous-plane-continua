import HPC.Plane.NonCut51

/-!
# Batch 95: Theorem 9 (Bing 1951), the two open steps

Skeleton (save as `HPC/Plane/Theorem9B.lean`; add `import HPC.Plane.Theorem9B` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. The targets are batch 93's `endElt_mem_bingH` (Q1) and
`bingH_irreducible_singleton` (Q3), whose `sorry`s are to be discharged by the results here if the
route closes; otherwise the strongest proved forms go here under their own names.

Notation: `S'` a nondegenerate subcontinuum of `S`, as a subtype with `CompactSpace S'` installed
from `hS'` (batch 94's shape); `bingElt` on `S'` is the element computed in `S'`.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Q1, route 1: an end element of `S` contains an end element of every subcontinuum containing it -/

/-- **QA. Elements of `S'` inside an element of `S` form an order-interval.** If two elements of
`S'` lie in `g = bingElt r` (`r ∈ S`), every element of `S'` separating them (in `S'`) lies in
`g`. -/
theorem elt_between_subset (hS : BingS S) {S' : Set S} (hS' : Fold.Q78.IsContinuum S')
    (hnd : S'.Nontrivial) {r : S} {e e' e'' : S'}
    (he : ((↑) : S' → S) '' (haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
      bingElt e) ⊆ bingElt r)
    (he' : ((↑) : S' → S) '' (haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
      bingElt e') ⊆ bingElt r)
    (hsep : haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
      Separates (bingElt e'') (bingElt e) (bingElt e')) :
    ((↑) : S' → S) '' (haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
      bingElt e'') ⊆ bingElt r := by
  sorry

/-- **QB. An end element of `S` contains an end element of every subcontinuum that contains it
properly.** -/
theorem endElt_contains_endElt_sub (hS : BingS S) {r : S} (hr : IsEndElt r) {S' : Set S}
    (hS' : Fold.Q78.IsContinuum S') (hnd : S'.Nontrivial) (hsub : bingElt r ⊆ S')
    (hne : bingElt r ≠ S') :
    haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1
    ∃ e : S', IsEndElt e ∧ ((↑) : S' → S) '' bingElt e ⊆ bingElt r := by
  sorry

/-- **QC. Q1 of Theorem 9**: an end element of `S` is a member of Bing's `H`
(batch 93's `endElt_mem_bingH`). From QB and Theorem 8 (c) for `S'`: with `e ⊆ g` an end element
of `S'` and `e'` the other end element of `S'`, any `p ∈ e'` makes `S'` irreducible from `g` to
`p`. -/
theorem endElt_mem_bingH' (hS : BingS S) {r : S} (hr : IsEndElt r) : BingH (bingElt r) := by
  sorry

/-! ## Q3: descent -/

/-- **Q3′ (descent).** If `h` is a nondegenerate member of `H`, then an end element of `h`
(computed in `h` as a space) is a member of `H`. With Brouwer reduction (batch 93) this gives Q3:
a minimal member is a point. -/
theorem endElt_of_bingH_mem_bingH (hS : BingS S) {h : Set S} (hh : BingH h) (hnd : h.Nontrivial) :
    haveI : CompactSpace h := isCompact_iff_compactSpace.mp hh.1.1
    ∃ e : h, IsEndElt e ∧ BingH (((↑) : h → S) '' bingElt e) := by
  sorry

/-- **Q3 from Q3′** (batch 93's `bingH_irreducible_singleton`). -/
theorem bingH_irreducible_singleton' (hS : BingS S) {h : Set S} (hh : BingH h)
    (hmin : ∀ h' : Set S, BingH h' → h' ⊆ h → h' = h) : ∃ p : S, h = {p} := by
  sorry

/-- **Theorem 9** (Bing 1951, p. 659), unconditional if QC and Q3 close. -/
theorem theorem9_1951' (hS : BingS S) {r : S} (hr : IsEndElt r) :
    ∃ p ∈ bingElt r, CondA (univ : Set S) p := by
  sorry

end HPC.Plane
