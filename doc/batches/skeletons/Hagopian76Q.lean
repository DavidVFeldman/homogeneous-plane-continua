import HPC.Hagopian.Hagopian76P

/-!
# Batch 172 skeleton: Hagopian 1976, Theorem 1 — the end case of Property 3; the `I₂` case and the
# side edges by Schoenflies; the ends of crossing components; T15–T17 and the assembly

Save as `HPC/Hagopian/Hagopian76Q.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76Q` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 172 §1.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A. The end case of Property 3** (commission 172 §1.A), hence `hagopian76_property3`.
*Shape left to you.* -/
theorem hagopian76_property3 : True := by
  sorry

/-- **B. The inner collar of `I` in `D′`, and positions through the side edges** (Schoenflies).
*Shape left to you.* -/
theorem crossing_sides_cover_schoenflies : True := by
  sorry

/-- **C. The ends of crossing components.** *Shape left to you.* -/
theorem crossing_component_ends : True := by
  sorry

/-- **D. T15–T17** (pp. 347–349). Conclusion `False`, conditional on named `Prop`s for any step
left open. *Shape left to you.* -/
theorem hagopian76_T15_T17 : True := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345): `Hagopian76Thm1`, or conditional on named `Prop`s. *Shape left to
you.* -/
theorem hagopian76_theorem1_final : True := by
  sorry

end HPC.Hagopian
