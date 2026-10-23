import HPC.Hagopian.Hagopian76T

/-!
# Batch 176 skeleton: Hagopian 1976, Theorem 1 — positions by `ε₃`; the cutting step; Property 4;
# the induction; the assembly

Save as `HPC/Hagopian/Hagopian76U.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76U` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 176 §1.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A.** For `ε₃` small, `ε₃`-images of points of `K` lie over abscissae in `[3/8, 5/8]`.
*Shape left to you.* -/
theorem eps3_positions_middle : True := by
  sorry

/-- **B.** Separation of middle points by a compact `X ⊆ F` is witnessed by crossing components in
`X`. *Shape left to you.* -/
theorem sep_by_crossing : True := by
  sorry

/-- **B′.** `TailCutKeepsSep`, hence `x₂ₙ = 1` for Hagopian's `F`. *Shape left to you.* -/
theorem hagopian76_x2n_eq_one : True := by
  sorry

/-- **C.** Property 4 for `[x₂ₙ₋₁, x₂ₙ]`, on a `T12Data` package. *Shape left to you.* -/
theorem hagopian76_property4_top : True := by
  sorry

/-- **D.** The induction step (Cases 1–2). *Shape left to you.* -/
theorem hagopian76_property4_step : True := by
  sorry

end Thm1

/-- **E. Theorem 1** (p. 345), or a conditional form. *Shape left to you.* -/
theorem hagopian76_theorem1_final : True := by
  sorry

end HPC.Hagopian
