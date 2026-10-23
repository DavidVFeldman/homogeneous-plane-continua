import HPC.Hagopian.Hagopian76AA

/-!
# Batch 183 skeleton: Hagopian 1976, Theorem 1 — Bing's reasons for Cases 1–2; E2.4;
# the orientation; saturation

Save as `HPC/Hagopian/Hagopian76AB.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76AB` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders (Hagopian's, and
Bing's where §1 of the commission pairs them), and record each shape in the report. Unproved items
are commented out with an `OPEN` note, as before. Every theorem with a named `Prop` among its
hypotheses gets a non-vacuity note.

Sources: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 348–349; Bing 1960
(`doc/sources/bing1960.pdf`), pp. 225–227. Route: commission 183.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §2. E2.4 by Bing's arc `ab` -/

/-- **§2, E2.4** (p. 348: "The point `yᵢ₋₁` is below `Cᵢ` and `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`; for otherwise,
a subcontinuum of `L` would violate Property 2"; Bing p. 227: "If `q` were above `tu`, we would take
`p = a` …"): the subcontinuum `H` of `L` between a point of `Cl Cᵢ` and a point of `Cl Cᵢ₋₁` within
`ε₃` of each other, and the contradiction with Property 2. *Shape left to you.* -/
theorem property2_violation : True := by
  sorry

/-! ## §3. "Between" by Bing's Jordan-curve argument -/

/-- **§3** (p. 348: "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see that `yᵢ₋₁` is
between `d⁻¹[I]` and `d⁻¹[J]`"; Bing p. 226: "It follows from the Jordan curve theorem that `q` lies
between …"). *Shape left to you.* -/
theorem case1_between_bing : True := by
  sorry

/-! ## §4. Case 2 by Bing's closed curve -/

/-- **§4.1, (a)** (Bing p. 227: "If `v` is above `x₂ᵢ₊₁x₂ᵢ₊₂` it is between the points `x₂ᵢ` and
`x₂ᵢ₊₂`"). *Shape left to you.* -/
theorem case2_bing_a : True := by
  sorry

/-- **§4.2, (b) and (e)**: `f(yᵢ₋₁)` lies in the complementary domain of `P` that contains `f(yᵢ)`.
*Shape left to you.* -/
theorem case2_curve : True := by
  sorry

/-- **§4.3**: on which side of `D` the gap continuum passes, or the configuration in which it goes
around an end of `π[E]`. *Shape left to you.* -/
theorem case2_gap_side : True := by
  sorry

/-! ## §5. The other two orientations -/

/-- **§5**: Property 4 for points of `Mid ∩ π⁻¹[D]`, for `f` or `f⁻¹`, and the step in the
orientations with `d⁻¹[J]` on the side of `f(yᵢ)`. *Shape left to you.* -/
theorem property4_symm : True := by
  sorry

/-! ## §6. Smaller items -/

/-- **§6.1, E2.1 items 1–3, 5**: the first crossing component met by an extension of `Cl Cᵢ` away
from `X`, and the shortest `L`. *Shape left to you* (your proposal in report 182 §9 is
acceptable). -/
theorem exists_first_crossing : True := by
  sorry

/-- **§6.2**: steps 4–5 of `noncrossing_half_in_O`. *Shape left to you.* -/
theorem half_components_cross : True := by
  sorry

/-- **§6.2**: the points `zⱼ` and (iii) at `zⱼ`. *Shape left to you.* -/
theorem chunk_points : True := by
  sorry

/-- **§6.3**: the case split by the side on which `Γ` joins the ends of `S_J` and `S_I`.
*Shape left to you.* -/
theorem gap_side_split : True := by
  sorry

/-- **2e, saturation** for Hagopian's `F`, on `(3/22 + 8/n, 19/22 − 8/n)`. -/
theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345), or the strongest conditional form. -/
theorem hagopian76_theorem1_final : Hagopian76Thm1 := by
  sorry

end HPC.Hagopian
