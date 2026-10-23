import HPC.Hagopian.Hagopian76R

/-!
# Batch 174 skeleton: Hagopian 1976, Theorem 1 — "`I` is finite"; the end element; `J` and the
# `xᵢ`; Property 4; the induction; the assembly

Save as `HPC/Hagopian/Hagopian76S.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76S` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 174 §1–2.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A.** Property 3 for the end element `d⁻¹(1)`, via a proper extension. *Shape left to you.* -/
theorem hagopian76_property3_end_element : True := by
  sorry

/-- **B.** "It follows from Property 3 that `I` is finite" (p. 347). *Shape left to you.* -/
theorem hagopian76_I_finite : True := by
  sorry

/-- **C.** `J` and the `xᵢ`, with `x₁ = 0`, `x₂ = e`, `x₂ₙ = 1` (pp. 347–348). *Shape left to you.* -/
theorem hagopian76_J_xs : True := by
  sorry

/-- **D.** Property 4 for `[x₂ₙ₋₁, x₂ₙ]`, and its failure for `[x₁, x₂]` (p. 348).
*Shape left to you.* -/
theorem hagopian76_property4 : True := by
  sorry

/-- **E.** The induction (pp. 348–349): if `[x₂ᵢ₋₁, x₂ᵢ]` has Property 4 then so does
`[x₂ᵢ₋₃, x₂ᵢ₋₂]`. *Shape left to you.* -/
theorem hagopian76_property4_step : True := by
  sorry

end Thm1

/-- **F. Theorem 1** (p. 345). *Shape left to you.* -/
theorem hagopian76_theorem1_final : True := by
  sorry

end HPC.Hagopian
