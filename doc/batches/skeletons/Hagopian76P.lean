import HPC.Hagopian.Hagopian76O

/-!
# Batch 171 skeleton: Hagopian 1976, Theorem 1 — Property 3 without margins; positions through the
# side edges; the ends of crossing components; T15–T17 and the assembly

Save as `HPC/Hagopian/Hagopian76P.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76P` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 171 §1.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A. Property 3** (p. 347), by route A.1 (middle translates) or A.2 (triod).
*Shape left to you.* -/
theorem hagopian76_property3 : True := by
  sorry

/-- **B. Positions through the side edges**: disjointness and covering for proper subcontinua.
*Shape left to you.* -/
theorem crossing_sides_cover' : True := by
  sorry

/-- **C. The ends of a crossing component** lie in `L₂` and `L₁₀`, or the component contains a
small middle translate. *Shape left to you.* -/
theorem crossing_component_ends : True := by
  sorry

/-- **D. T15–T17** (pp. 347–349). Conclusion `False`, under `RsetDichotomy`.
*Shape left to you.* -/
theorem hagopian76_T15_T17 : True := by
  sorry

/-- **E.** (optional) A generic `h` has `h[R(E)] ∩ R(E) = ∅`. *Shape left to you.* -/
theorem generic_translate_disjoint : True := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345), under `RsetDichotomy` (stated explicitly), or unconditionally if E is
proved. *Shape left to you.* -/
theorem hagopian76_theorem1_cond : True := by
  sorry

end HPC.Hagopian
