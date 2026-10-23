import HPC.HO16.Thm20
import HPC.HO16.Prop19Conn
import HPC.HO16.P208

/-!
# Batch 196: Hoehn–Oversteegen Theorem 1, IV — Proposition 19; Theorem 20 from Theorem 15

The skeleton `HO16D.lean` of commission 196, split under `HPC/HO16/`:

* `P19Defs.lean`: the skeleton's `p19T`, `p19α`, `HOThm15`; `HOProp19` (new: the statement of
  `ho16_prop19` as a named `Prop`, used to derive Theorem 20 before Proposition 19 was proved).
* `OrdFold.lean`: §2, `IsSimpleFoldOf.isOrdinaryPt_iff`.
* `P19Lib.lean`, `P19Ctx.lean`, `Prop19A.lean`–`Prop19D.lean`, `Prop19.lean`: §3,
  `ho16_prop19_full`.
* `Prop19Conn.lean`: §3, `ho16_prop19`, and `hoProp19_holds : HOProp19`.
* `P208.lean`: §4, `ho16_p208_false`.
* `Thm20.lean`: §5 with `HOProp19` as a hypothesis.
* This file: §5 in the skeleton's form, `HOProp19` discharged.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-- **The induction of Theorem 20** (pp. 209–210): a map of a hereditarily indecomposable
compactum to a connected PL graph `G` is approximated by the first coordinate of a map into any
set with a stairwell structure of odd height. -/
theorem ho16_lift_stairwell (k : ℕ) (hk : Odd k) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : Set E) (hG : IsPLGraph G) (hconn : IsConnected G) (S : Set (E × ℝ))
    (hS : HasStairwell G S k) (X : Type) [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X)) (f : X → E) (hf : Continuous f)
    (hfG : ∀ x, f x ∈ G) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : X → E × ℝ, Continuous h ∧ (∀ x, h x ∈ S) ∧ ∀ x, dist (f x) (h x).1 < ε :=
  ho16_lift_stairwell_of_prop19 hoProp19_holds k hk E G hG hconn S hS X hHI f hf hfG ε hε

/-- **H–O Theorem 20, forward direction**, from Theorem 15. -/
theorem ho16_theorem20_of_thm15 (h15 : HOThm15) : HOThm20 :=
  ho16_theorem20_of_thm15_prop19 hoProp19_holds h15

/-- The classification step of batch 193 with `HOThm15` as the only open input. -/
theorem homeomorph_pseudoArc_of_indec_homogeneous_of_thm15 (h15 : HOThm15) (M : Set Pt)
    [CompactSpace M] [ConnectedSpace M] (hhom : IsHomogeneous M)
    (hind : ¬ IsDecomposableSpace M) (hnt : (univ : Set M).Nontrivial) :
    ∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (M ≃ₜ M₀) :=
  homeomorph_pseudoArc_of_indec_homogeneous_of_thm15_prop19 hoProp19_holds h15 M hhom hind hnt

end HPC.HO16
