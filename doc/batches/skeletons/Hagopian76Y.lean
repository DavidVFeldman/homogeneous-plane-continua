import HPC.Hagopian.Hagopian76X

/-!
# Batch 180 skeleton: Hagopian 1976, Theorem 1 — the set-up repaired; saturation; 3c; the step

Save as `HPC/Hagopian/Hagopian76Y.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76Y` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

`Thm1Setup`, `exists_thm1Setup` and `hagopian76_theorem1_of_step` are restated in place in
`H76Thm1Setup.lean` (commission 180 §1.2–§1.3); the statements below that mention `Thm1Setup`
refer to the repaired structure.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 180.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. The set-up -/

/-- **§1.1, certificate.** With `K = {p}`, Property 4 fails for every block below the top: it
would make the proper extension `d⁻¹[[0, x₂ᵢ₋₂]]` separate `p` from `f(p)` in `π⁻¹[D]`, against
`D.irr`. -/
theorem property4_lower_false_of_K_eq {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {F : ℝ × ℝ → Pt} {D' : Set (ℝ × ℝ)} {ε₃ : ℝ} (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) (D : T12Data E k π F D' ε₃) (hK : D.K = {D.p})
    {x : ℕ → unitInterval} {m : ℕ} (hx : StrictMonoOn x (Icc 1 (2 * m)))
    (hx2 : layerSet D.d (Icc 0 (x 2)) = E) (hxm : x (2 * m) = 1) {i : ℕ} (hi2 : 2 ≤ i)
    (him : i ≤ m) :
    ¬ Property4 D (x (2 * i - 3)) (x (2 * i - 2)) := by
  sorry

/-- **§1.2.2**: `hagopian76_T15_T17_cond3` with the package's composant data exposed (base point
`x₀` over `t₀`, `p = h x₀`, `h x₀` and `h₁ x₀` off the composant of `x₀`, `h` and `h₁`
`θ/4`-small) and `K₀` the points of `M` over the open low vertical. *Shape left to you.* -/
theorem hagopian76_T15_T17_cond4 : True := by
  sorry

/-- **§1.3, positive check**: every crossing piece inside `M` meets `K` (S4a with the new `K₀`).
This is what E2.1 uses to choose `yᵢ₋₁`. -/
theorem Thm1Setup.K_meets_crossing (S : Thm1Setup M) {C : Set Pt}
    (hC : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ C) (hCM : C ⊆ M) :
    (C ∩ toPt S.D.K).Nonempty := by
  sorry

/-! ## §2. Saturation -/

/-- **§2.1** (commission 178 §3b, step 3.1): if `K⁻ ⊆ O` with tip `τ`, then `d⁻¹(1)` meets the
tip layer `h[k⁻¹(τ)]`; hence `Λ₁ ∪ h[k⁻¹(τ)]` is a continuum. For any `θ/4`-homeomorphism `h` and
any `y = h(e)` over the inner middle. *Shape left to you.* -/
theorem tip_meets_end_layer : True := by
  sorry

/-- **2a, the tip triod**, with its mirror form for `K⁺`. *Shape left to you.* -/
theorem tip_triod : True := by
  sorry

/-- **2b**: the triod for a point on its own tip layer. *Shape left to you.* -/
theorem tip_triod_on_tip_layer : True := by
  sorry

/-- **2d**: a nondegenerate chunk of `d⁻¹(1)` through a non-crossing component is impossible, with
the margin of §2.2. *Shape left to you.* -/
theorem no_end_layer_chunk : True := by
  sorry

/-- **2e, saturation** for Hagopian's `F`, on `(3/22 + 8/n, 19/22 − 8/n)` (§2.2). -/
theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  sorry

/-! ## §3. 3c, E0, E1 -/

/-- **3c**: blocks inherit saturation; gap layers and block end layers miss the points over the
interval of §2.2. *Shape left to you.* -/
theorem block_components_cross : True := by
  sorry

/-- **E0, E1** ("… and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`", p. 348).
*Shape left to you.* -/
theorem property4_step_unless : True := by
  sorry

/-! ## §4. The induction step -/

/-- **E2.1**: the shortest extension `L`, the strand `Cᵢ₋₁`, and `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁`.
*Shape left to you.* -/
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

/-- **The step** (Cases 1–2) for the repaired set-up. -/
theorem hagopian76_property4_step (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ)
    (hx : S.IsBlocks x m) : Property4Step S.D x m := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345), from `hagopian76_theorem1_of_step`, `innerComponentsCross_hagopian`
and `hagopian76_property4_step`; or the strongest conditional form. -/
theorem hagopian76_theorem1_final : Hagopian76Thm1 := by
  sorry

end HPC.Hagopian
