import HPC.Hagopian.Hagopian76W

/-!
# Batch 179 skeleton: Hagopian 1976, Theorem 1 — the end layer of `F`; `SepByCrossing` without
# conditions; uniform heights; the assembly; the step

Save as `HPC/Hagopian/Hagopian76X.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76X` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 179 §2–§6.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §2. Saturation -/

/-- **2a, the tip triod**: `K⁻ ⊆ O` with tip `τ`; if some point of `K⁻` lies off `d⁻¹(1)` and off
the tip layer, and `d⁻¹(1) ⊄ h[E]`, then `M` contains a triod. With its mirror form for `K⁺`.
*Shape left to you.* -/
theorem tip_triod : True := by
  sorry

/-- **2b**: the triod for a point on its own tip layer (through `K⁺_δ`). *Shape left to you.* -/
theorem tip_triod_on_tip_layer : True := by
  sorry

/-- **2d**: a nondegenerate chunk of `d⁻¹(1)` through a non-crossing inner component is impossible
(void interior of `d⁻¹(1)`, finitely many crossing components, 2a at nearby points).
*Shape left to you.* -/
theorem no_end_layer_chunk : True := by
  sorry

/-- **Finitely many crossing components** (from `crossingIntervals_disjoint`,
`IsCrossingComponent.eq_of_mem_closure`, `hagopian76_I_finite`). *Shape left to you.* -/
theorem crossing_components_finite : True := by
  sorry

/-- **2e, saturation**: `InnerComponentsCross` for Hagopian's `F`. *Shape left to you.* -/
theorem innerComponentsCross_hagopian : True := by
  sorry

/-! ## §3. Without conditions -/

/-- **3c**: blocks inherit saturation; gap layers and block end layers miss the inner middle.
*Shape left to you.* -/
theorem block_components_cross : True := by
  sorry

/-- **4.B**: `p` and `f(p)` lie on crossing pieces (with `Disjoint I₂ (π '' M)` from T7).
*Shape left to you.* -/
theorem p_on_crossing_piece : True := by
  sorry

/-- **3.3**: `SepByCrossing` for `(F, p, f(p))`, unconditional. *Shape left to you.* -/
theorem sep_by_crossing_uncond : True := by
  sorry

/-- **3.3**: "Note that `x₂ₙ = 1`" (p. 348), unconditional. *Shape left to you.* -/
theorem hagopian76_x2n_eq_one_final : True := by
  sorry

/-- **3.3**: Property 4 for the top block (p. 348), unconditional. *Shape left to you.* -/
theorem hagopian76_property4_top_final : True := by
  sorry

/-- **3.4**: the blocks, with nondegeneracy from `hagopian76_property3_components`.
*Shape left to you.* -/
theorem exists_blocks_uncond : True := by
  sorry

/-! ## §4. Uniform heights -/

/-- **§4**: Property 3, `I` finite, and the middle-crossing lemmas with the height chosen before
`G` (`∃ c, ∀ G d, …`). One statement per theorem listed in commission 179 §4.
*Shape left to you.* -/
theorem uniform_heights : True := by
  sorry

/-! ## §6. The induction step -/

/-- **E1** ("… and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`", p. 348).
*Shape left to you.* -/
theorem property4_step_unless : True := by
  sorry

/-- **E2.1**: the first strand `Cᵢ₋₁` and the shortest extension `L`. *Shape left to you.* -/
theorem first_strand : True := by
  sorry

/-- **E2.4** ("for otherwise, a subcontinuum of `L` would violate Property 2"):
`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`. *Shape left to you.* -/
theorem property2_far_from_I : True := by
  sorry

/-- **The cap, Case 1**: `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q` separates `yᵢ` from `f(yᵢ)`.
*Shape left to you.* -/
theorem case1_cap : True := by
  sorry

/-- **E2.5**: local to global. *Shape left to you.* -/
theorem case1_local_to_global : True := by
  sorry

/-- **Case 2** (p. 349). *Shape left to you.* -/
theorem case2 : True := by
  sorry

/-- **E**: `Property4Step` (Cases 1–2), or the strongest conditional form. *Shape left to you.* -/
theorem hagopian76_property4_step : True := by
  sorry

end Thm1

/-! ## §5. The assembly -/

/-- **§5**: `Thm1Setup` and Theorem 1 from the step alone:
`(∀ S : Thm1Setup, Property4Step S.D S.x S.n) → Hagopian76Thm1`. *Shape left to you.* -/
theorem hagopian76_theorem1_of_step : True := by
  sorry

/-- **Theorem 1** (p. 345), or the strongest conditional form. *Shape left to you.* -/
theorem hagopian76_theorem1_final : True := by
  sorry

end HPC.Hagopian
