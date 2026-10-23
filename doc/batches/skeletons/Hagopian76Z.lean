import HPC.Hagopian.Hagopian76Y

/-!
# Batch 181 skeleton: Hagopian 1976, Theorem 1 — saturation; 3c; Case 1 strand by strand;
# Case 2 sentence by sentence

Save as `HPC/Hagopian/Hagopian76Z.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76Z` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

The two fields of commission 181 §3.1 (`hε₃O`, `hε₃S`) are added to `Thm1Setup` in place, in
`H76Thm1Setup.lean`, with `exists_thm1Setup` restated.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 348–349. Route: commission 181.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. Saturation -/

/-- **§1.1** (commission 178 §3b, step 2): a component of `F ∩ O` through a point over
`(3/22 + 8/n, 19/22 − 8/n)` whose halves `K⁻`, `K⁺` both leave `O` is a crossing piece.
*Shape left to you* (your proposal `noncrossing_half_in_O`, report 180 §9, is acceptable). -/
theorem noncrossing_half_in_O : True := by
  sorry

/-- **§1.2–§1.3**: the points `zⱼ → c` with `d(zⱼ) < 1`, non-crossing components, and (iii).
*Shape left to you.* -/
theorem chunk_points : True := by
  sorry

/-- **§1.4**: the edge case, through `b = 1` in `tip_triod` and the mirror triod at `σ = τ₁`.
*Shape left to you.* -/
theorem chunk_edge_case : True := by
  sorry

/-- **2d**: a nondegenerate chunk of `d⁻¹(1)` through a non-crossing component is impossible.
*Shape left to you.* -/
theorem no_end_layer_chunk : True := by
  sorry

/-- **2e, saturation** for Hagopian's `F`, on `(3/22 + 8/n, 19/22 − 8/n)`. -/
theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  sorry

/-! ## §2. 3c, E0, E1 -/

/-- **§2.1, 3c** by the irreducible interval, with `InnerComponentsCross` as a hypothesis. Use the
shape in the open block of `Hagopian76Y.lean`. *Shape left to you.* -/
theorem block_components_cross : True := by
  sorry

/-- **§2.2, E0 and E1** (p. 348: "… and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`"), with
the cases of the parenthesis "(Other cases are handled with similar arguments …)".
*Shape left to you.* -/
theorem property4_step_unless : True := by
  sorry

/-! ## §3. Case 1 -/

/-- **§3.1**: for `y ∈ K`, `f(y) ∈ π⁻¹[D]` (p. 348: "Note that `f(yᵢ₋₁)` belongs to
`L₆ ∩ π⁻¹[D]`"), from `hε₃O` and `hcomp`. *Shape left to you.* -/
theorem f_mem_O_of_mem_K : True := by
  sorry

/-- **§3.2.1**: the region above a crossing piece of `lowFrame` has closure missing `π⁻¹` of the
open bottom edge (and the mirror: the region below misses `π⁻¹[I₂]`). *Shape left to you.* -/
theorem above_closure_misses_bottom : True := by
  sorry

/-- **§3.2.2, the cap lemma**: `a ∈ Mid` below a crossing piece `W`, `b` above it, `ρ(a, b) < ε₃`
imply `ρ(a, Cl W) < ε₃`. *Shape left to you.* -/
theorem cross_strand_near : True := by
  sorry

/-- **§3.3, E2.1**: `Cᵢ₋₁`, `L`, `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁`, `Cl Cᵢ₋₁` essential, `L ∩ F = ∅`.
*Shape left to you.* -/
theorem first_strand : True := by
  sorry

/-- **§3.4** ("By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see that `yᵢ₋₁` is between
`d⁻¹[I]` and `d⁻¹[J]`"). *Shape left to you.* -/
theorem case1_between : True := by
  sorry

/-- **§3.5, E2.4** ("for otherwise, a subcontinuum of `L` would violate Property 2"):
`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`. *Shape left to you.* -/
theorem property2_far_from_I : True := by
  sorry

/-- **§3.6.4**: no point of `N` is within `ε₂` of `Q` (p. 349). *Shape left to you.* -/
theorem N_far_from_Q : True := by
  sorry

/-- **§3.6, the band**: `f(yᵢ₋₁)` is above `S_I` or below `S_J`. *Shape left to you.* -/
theorem case1_band : True := by
  sorry

/-- **§3.8, Case 1**: Property 4 for `J`, conditional on the named `Prop`s of §3.3–§3.6 that stay
open. *Shape left to you.* -/
theorem case1 : True := by
  sorry

/-! ## §4. Case 2 -/

/-- **§4 (a)–(e)**: one statement per printed claim, proved, refuted, or a named `Prop`.
*Shape left to you.* -/
theorem case2_claims : True := by
  sorry

/-- **§4, Case 2**: Property 4 for `J`, conditional on what stays open. *Shape left to you.* -/
theorem case2 : True := by
  sorry

/-! ## §5. The step -/

/-- **The step** (Cases 1–2) for the repaired set-up, or its strongest conditional form. -/
theorem hagopian76_property4_step (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ)
    (hx : S.IsBlocks x m) : Property4Step S.D x m := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345), or the strongest conditional form. -/
theorem hagopian76_theorem1_final : Hagopian76Thm1 := by
  sorry

end HPC.Hagopian
