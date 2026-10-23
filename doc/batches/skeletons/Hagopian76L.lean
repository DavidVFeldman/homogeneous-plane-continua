import HPC.Hagopian.Hagopian76K

/-!
# Batch 167 skeleton: Hagopian 1976, Theorem 1 — crossing translates; T12; Property 3; T13; then
# T15–T17 and the assembly

Save as `HPC/Hagopian/Hagopian76L.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76L` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 167 §1.
Set-up: `hagopian76_D` over `[3/22, 19/22]` (`D = F[D′]`, low strip of height `c₀`),
`hagopian76_K0` over `11/22`; `0 < a′ < 3/22`, `19/22 < b′ < 1`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Crossing translates -/

/-- **Lemma T** (commission 167 §1). For every `ζ > 0` there is `δ > 0` such that for every
`x ∈ E` with `k(x) ∈ [3/22 + ζ, 19/22 − ζ]` and every `δ`-homeomorphism `h` of `M` with `h(x) ∉ E`
and `π(h(x))` above the axis: `h[k⁻¹[[a′, b′]]]` misses `E`; its `π`-image lies in the band above
the axis below height `c₀`; `h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]] ⊆ π⁻¹[D]`; and the component of
`M ∩ π⁻¹[D]` containing `h(x)` has closure meeting both `π⁻¹F[{3/22} × (0, r₂)]` and
`π⁻¹F[{19/22} × (0, s₂)]`. *Shape left to you.* -/
theorem crossing_translate : True := by
  sorry

/-- **Lemma T′** (commission 167 §1). Points of `M ∩ K₀` at every small height; a limit point
`x ∈ k⁻¹(11/22)` of them, so that every neighbourhood of `x` in `M` meets `K₀`. This is Hagopian's
`x` ("let `x` be a point of `k⁻¹(p₃) ∩ Cl K`", p. 347). *Shape left to you.* -/
theorem K0_dense_low : True := by
  sorry

/-! ## B. T12 -/

/-- **T12** (p. 347): "A point `p` of `K` and three `ε₃`-homeomorphisms `f`, `h`, and `h₁` of `M`
onto `M` exist such that (1) `f = h₁h⁻¹`, (2) the closure of the `p`-component `C` of
`M ∩ π⁻¹[D]` is essential to `h[R(E)]`, and (3) `R(E)` separates `p` from `f(p)` in `π⁻¹[D]`."
With `p`, `q ∈ M ∩ K₀`. *Shape left to you* (report 166 §5 has a proposal). -/
theorem hagopian76_T12 : True := by
  sorry

/-! ## C. Property 3 -/

/-- **The least `v`** (p. 347, "Let `v` be the first point of `[0, 1]` such that …"): the set of
parameters whose layer of `d` contains a crossing continuum (or component) is closed. *Shape left
to you.* -/
theorem crossing_set_closed : True := by
  sorry

/-- **Property 3** (p. 347), in full. *Shape left to you.* -/
theorem hagopian76_property3 : True := by
  sorry

/-! ## D. T13 -/

/-- **T13** (p. 347): "Let `F` be a continuum that is irreducible with respect to the following
properties: 1. `F` is an extension of `E` in `M` away from `k⁻¹(0)`. 2. `F` separates `p` from
`f(p)` in `π⁻¹[D]`." With the existence sentence. *Shape left to you.* -/
theorem hagopian76_T13 : True := by
  sorry

/-! ## E. T15–T17 (if reached) -/

/-- **T15–T17** (pp. 347–349). Conclusion `False` under the hypotheses of Theorem 1.
*Shape left to you.* -/
theorem hagopian76_T15_T17 : True := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345). The assembly. -/
theorem hagopian76_theorem1 : Hagopian76Thm1 := by
  sorry

end HPC.Hagopian
