import HPC.Hagopian.Hagopian76L

/-!
# Batch 168 skeleton: Hagopian 1976, Theorem 1 — crossing pieces of `R(E)`; the requirements of
# T13–T17 on `p`, `q`; T12 (3); Property 3; T13; then T15–T17 and the assembly

Save as `HPC/Hagopian/Hagopian76M.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76M` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Route: commission 168 §1.
Set-up as in `Hagopian76L.lean` (`hagopian76_D`, `hagopian76_K0`, `crossing_translate`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## B. Crossing pieces of `R(E)`; two crossing continua cut `D` -/

/-- **Lemma R** (commission 168 §1). Points `y ∈ R(E) − E` arbitrarily close to `x ∈ E` (middle
range); for small `h` with `h(x) = y`, `h[k⁻¹[[a′, b′]]] ⊆ R(E)` by absorption, it misses `E`, and
the component of `R(E) ∩ π⁻¹[D]` through `y` crosses. *Shape left to you* (report 167 §5). -/
theorem crossing_piece_of_R : True := by
  sorry

/-- **Two disjoint crossing continua cut `π⁻¹[D]` in three** along `K₀`. *Shape left to you.* -/
theorem crossing_pair_separates : True := by
  sorry

/-! ## C. T12 -/

/-- **T12** (p. 347), part (3) and the choice of `p`, `q`, in the form commission 168 §2.A finds
sufficient for T13–T17. *Shape left to you.* -/
theorem hagopian76_T12 : True := by
  sorry

/-! ## D. Property 3 -/

/-- **The least `v`**: the set of `v` whose layer of `d` contains a crossing continuum missing `E`
and `π⁻¹[I₂]` is closed. *Shape left to you.* -/
theorem crossing_set_closed : True := by
  sorry

/-- **Property 3** (p. 347), continuum form. *Shape left to you.* -/
theorem hagopian76_property3 : True := by
  sorry

/-! ## E. T13, T15–T17 -/

/-- **T13** (p. 347), with its existence sentence. *Shape left to you.* -/
theorem hagopian76_T13 : True := by
  sorry

/-- **T15–T17** (pp. 347–349). Conclusion `False` under the hypotheses of Theorem 1.
*Shape left to you.* -/
theorem hagopian76_T15_T17 : True := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345). The assembly. -/
theorem hagopian76_theorem1 : Hagopian76Thm1 := by
  sorry

end HPC.Hagopian
