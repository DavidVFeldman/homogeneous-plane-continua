import HPC.Hagopian.Hagopian76N

/-!
# Batch 170 skeleton: Hagopian 1976, Theorem 1 — `ExtChainInter`; the covering half; "follows" for
# crossing components; Property 3; T15–T17 and the assembly (under `RsetDichotomy` if necessary)

Save as `HPC/Hagopian/Hagopian76O.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76O` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 170 §1.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A.** The intersection of a nonempty chain of extensions of `E` away from `k⁻¹(0)`, all inside
one extension `H`, is an extension away from `k⁻¹(0)` (commission 170 §1.A: Lemma 4 strong form,
`inf` of the parameters, `piece_map`). *Shape left to you* (`ExtChainInter`, restricted to `H`). -/
theorem extChainInter_in : True := by
  sorry

/-- **A′. T13, unconditional** (p. 347). *Shape left to you.* -/
theorem hagopian76_T13_uncond : True := by
  sorry

/-- **B. The covering half** for proper subcontinua of `M` (`no_proper_subcontinuum_separates`), in
the form T17 needs (commission 170 §1.B). *Shape left to you.* -/
theorem crossing_sides_cover : True := by
  sorry

/-- **C. "Follows" for crossing components** (commission 170 §1.C). *Shape left to you.* -/
theorem follows_crossing : True := by
  sorry

/-- **D. Property 3** (p. 347), with `crossing_set_closed` and the shift. *Shape left to you.* -/
theorem hagopian76_property3 : True := by
  sorry

/-- **E. T15–T17** (pp. 347–349). Conclusion `False`, under `RsetDichotomy` if necessary.
*Shape left to you.* -/
theorem hagopian76_T15_T17 : True := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345), possibly conditional on `RsetDichotomy` (state the hypothesis
explicitly). *Shape left to you.* -/
theorem hagopian76_theorem1_cond : True := by
  sorry

end HPC.Hagopian
