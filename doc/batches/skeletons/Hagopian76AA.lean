import HPC.Hagopian.Hagopian76Z

/-!
# Batch 182 skeleton: Hagopian 1976, Theorem 1 — the last step; honest claims; saturation;
# E2.1 and E2.4

Save as `HPC/Hagopian/Hagopian76AA.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76AA` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before. Every theorem
with a named `Prop` among its hypotheses gets a non-vacuity note (commission 182, Rules).

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 348–349. Route: commission 182.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. The last step and the case split -/

/-- **§1.1, certificate**: the case split of p. 348 fails at `i = 2`, where
`d⁻¹(x₂) = d⁻¹(e) = k⁻¹(1)` lies over `γ(1)` and meets neither side segment. -/
theorem blockLayersMeetSides_false (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) : ¬ BlockLayersMeetSides S x m := by
  sorry

/-- **§1.2, the last step** (`i = 2`, `J = [x₁, x₂] = [0, e]`): a witness (good point `y` below an
`I`-strand `S_I`, `ρ(y, Cl S_I) ≥ ε₃`, `f(y)` above `S_I`) gives `False`. With the named `Prop`
`LastStepClaims` for its existence. *Shape left to you.* -/
theorem last_step_ending : True := by
  sorry

/-- **§1.3**: the case split for `3 ≤ i ≤ m`, or the weaker split by left and right regions.
*Shape left to you.* -/
theorem blockLayersMeetSides_ge_three : True := by
  sorry

/-! ## §2. Honest claims, and the reduction -/

/-- **§2.1**: the mirror of the cap lemma without the bottom-edge hypothesis. The segment `[a, b]`
meets the frontier of the region above `W`, which misses the bottom edge. -/
theorem cross_strand_near_above (S : Thm1Setup M) {W : Set Pt}
    (hW : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ W)
    (hWs : Disjoint (S.V.below W) (S.V.above W)) {a b : Pt} (ha : a ∈ midSet M S.π S.F S.D' S.n)
    (haW : a ∈ S.V.above W) (hbW : b ∈ S.V.below W) (hab : dist a b < S.ε₃) :
    infDist a (closure W) < S.ε₃ := by
  sorry

/-- **§2.2**: `case1_ending` for both orientations. *Shape left to you.* -/
theorem case1_ending_oriented : True := by
  sorry

/-- **§2.2**: `case2_ending` for both orientations. *Shape left to you.* -/
theorem case2_ending_oriented : True := by
  sorry

/-- **§2.4**: the step from `LastStepClaims`, the case split for `3 ≤ i ≤ m`, and the restated
`Case1Claims`, `Case2Claims` (no `¬ Property4 J`; the printed case hypothesis instead).
*Shape left to you.* -/
theorem hagopian76_property4_step_cond2 : True := by
  sorry

/-- **§2.4**: Theorem 1 from saturation and the restated claims. *Shape left to you.* -/
theorem hagopian76_theorem1_of_cases2 : True := by
  sorry

/-! ## §3. Saturation -/

/-- **§3.2** (commission 181 §1.1, step 3): the closure of `F − E` meets `E` only in `k⁻¹(1)`. -/
theorem closure_G_diff_E (S : Thm1Setup M) :
    closure (toPt S.D.G \ toPt S.E) ∩ toPt S.E ⊆ toPt (layer S.k 1) := by
  sorry

/-- **§3.1** (commission 181 §1.1): a non-crossing component has one half `K⁻` or `K⁺` inside
`π⁻¹[D]`; `K⁻` is a continuum by hereditary unicoherence. *Shape left to you* (the shape in the
open block of `Hagopian76Z.lean` is acceptable). -/
theorem noncrossing_half_in_O : True := by
  sorry

/-- **§3.3**: the points `zⱼ` and (iii) at `zⱼ` (commission 181 §1.2–§1.3). *Shape left to you.* -/
theorem chunk_points : True := by
  sorry

/-- **§3.4**: the edge cases `F ∩ hⱼ[E] ⊆ Tⱼ` and `τ₁ = 1`. *Shape left to you.* -/
theorem chunk_edge_case_full : True := by
  sorry

/-- **2e, saturation** for Hagopian's `F`, on `(3/22 + 8/n, 19/22 − 8/n)`. -/
theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  sorry

/-! ## §4. E2.1 and E2.4 -/

/-- **§4.1, E2.1** (p. 348: "Let `Cᵢ₋₁` be the first component … The existence of `Cᵢ₋₁` follows
from …"): `Cᵢ₋₁`, `L`, `L ∩ F = ∅`, and `GoodPoint yᵢ₋₁`. *Shape left to you.* -/
theorem first_strand : True := by
  sorry

/-- **§4.2, E2.4** ("for otherwise, a subcontinuum of `L` would violate Property 2"):
`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`. *Shape left to you.* -/
theorem property2_far_from_I : True := by
  sorry

/-! ## §5. Case 2, claim (e) -/

/-- **§5**: (e), by extending away from `Z`, or by Property 2 for `f[N]`; or the named `Prop` with
its configuration. *Shape left to you.* -/
theorem case2_claim_e : True := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345), or the strongest conditional form. -/
theorem hagopian76_theorem1_final : Hagopian76Thm1 := by
  sorry

end HPC.Hagopian
