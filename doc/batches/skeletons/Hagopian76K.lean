import HPC.Hagopian.Hagopian76J

/-!
# Batch 166 skeleton: Hagopian 1976, Theorem 1 — `D` as a Jordan domain; the low part `K₀` of
# `K`; "`L − {L₁, L₁₁}` follows `Cl B`"; Property 3; T12, T13; then T15–T17 and the assembly

Save as `HPC/Hagopian/Hagopian76K.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76K` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report. Items stated as `True`
are *shape left to you*; quote the printed sentence each renders. Unproved items are commented out
with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349; Mazurkiewicz 1929
(`doc/sources/mazurkiewicz1929.pdf`) for T12. Abscissae of `p₁, …, p₅`: `3/22, 7/22, 11/22, 15/22,
19/22`. Lean index of Hagopian's `Lᵢ` is `i − 1`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## A. `D` as a Jordan domain (plane topology, in collar coordinates) -/

/-- **The domain under a crossing arc.** For an arc `I` as produced by `rect_crossing`, the simple
closed curve `I ∪ (bottom edge) ∪ (left edge up to r) ∪ (right edge up to s)` bounds an open
connected bounded set inside the open rectangle, with that curve as frontier (`jordan_curve_theorem`;
the complement of the closed rectangle is connected and unbounded and misses the curve). Hagopian's
`D` (p. 346) is the image of this set under the collar `F`. -/
theorem rect_domain {a b c : ℝ} (hab : a < b) (hc : 0 < c) {r s : ℝ × ℝ} {I : Set (ℝ × ℝ)}
    (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hr : r.1 = a) (hs : s.1 = b)
    (hIs : I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s}) :
    ∃ D : Set (ℝ × ℝ), IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      D ⊆ Ioo a b ×ˢ Ioo 0 c ∧
      frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
        ({b} : Set ℝ) ×ˢ Icc 0 s.2 := by
  sorry

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **T8, the domain** (p. 346): "Let `D` be the bounded complementary domain of
`I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩` in `R²`." `D = F[D′]` with `D′` from `rect_domain`, for `I₂`
from `hagopian76_T7` at a height below those of `hagopian76_T8` and `hagopian76_T11`. Include: `D`
open and connected, its frontier, `π⁻¹[D]` open, and that `D` meets `π[M]` (`M_meets_above`).
*Shape left to you.* -/
theorem hagopian76_D : True := by
  sorry

/-! ## B. The low part of `K` -/

/-- **`K₀`** (p. 347: "Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets both
`π⁻¹(p₃)` and `π⁻¹[I₂]`"). With `w` the lowest point of `I₂` on the vertical over `11/22`,
`K₀ = π⁻¹F[{11/22} × (0, w₂)]`. It is a component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]`, an open arc in `R² − E`,
and its closure meets `π⁻¹(p₃) = k⁻¹(11/22)` and `π⁻¹[I₂]`. The separation of T11 is carried by
the whole section (`hagopian76_T11`). *Shape left to you.* -/
theorem hagopian76_K0 : True := by
  sorry

/-! ## C. T9, last sentence -/

/-- **"Note that the chain `L − {L₁, L₁₁}` follows `Cl B`"** (p. 346), for a component `B` of
`M ∩ π⁻¹[D]` meeting `L₄ ∪ … ∪ L₈`. Route in commission 166 §1.C (the two ends of `Cl B` lie on the
side edges, on opposite sides). *Shape left to you.* -/
theorem hagopian76_T9_follows : True := by
  sorry

/-! ## D. Property 3 -/

/-- **Property 3** (p. 347), in full, for any extension `F` of `E` away from `k⁻¹(0)` with map `d`,
`d⁻¹(0) = k⁻¹(0)`: no component of `F ∩ π⁻¹[D]` whose closure meets `π⁻¹[⟨p₁, r⟩]` and
`π⁻¹[⟨p₅, s⟩]` lies in a layer of `d`. *Shape left to you* (report 165 §5 has a proposal). -/
theorem hagopian76_property3 : True := by
  sorry

/-! ## E. T12, T13 -/

/-- **T12** (p. 347): "A point `p` of `K` and three `ε₃`-homeomorphisms `f`, `h`, and `h₁` of `M`
onto `M` exist such that (1) `f = h₁h⁻¹`, (2) the closure of the `p`-component `C` of
`M ∩ π⁻¹[D]` is essential to `h[R(E)]`, and (3) `R(E)` separates `p` from `f(p)` in `π⁻¹[D]`."
With `p`, `q` in `K₀`. See commission 166 §1.E on "distinct inaccessible composants [10]".
*Shape left to you.* -/
theorem hagopian76_T12 : True := by
  sorry

/-- **T13** (p. 347): "Let `F` be a continuum that is irreducible with respect to the following
properties: 1. `F` is an extension of `E` in `M` away from `k⁻¹(0)`. 2. `F` separates `p` from
`f(p)` in `π⁻¹[D]`." With its existence ("follows from Property 1 and the fact that
`Cl R(E) = Cl R(k⁻¹(0), E)` (Lemma 6 (proof))"). *Shape left to you.* -/
theorem hagopian76_T13 : True := by
  sorry

/-! ## F. T15–T17 (if reached) -/

/-- **T15–T17** (pp. 347–349): the finite collection `I`, the points `xᵢ`, Property 4, and the
induction "Following Bing [2, p. 225]". Conclusion `False` under the hypotheses of Theorem 1.
*Shape left to you.* -/
theorem hagopian76_T15_T17 : True := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345). The assembly. -/
theorem hagopian76_theorem1 : Hagopian76Thm1 := by
  sorry

end HPC.Hagopian
