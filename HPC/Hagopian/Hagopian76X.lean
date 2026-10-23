import HPC.Hagopian.H76Thm1Setup
import HPC.Hagopian.H76Uniform3

/-!
# Batch 179: Hagopian 1976, Theorem 1 — the end layer of `F`; `SepByCrossing` without
# conditions; uniform heights; the assembly; the step

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 179 §1–§6.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76X.lean`. Every skeleton item stated as
`True` has been given a shape; the delivered statements are in the supporting files below, and the
items left open are commented out at the end, with the obstructions in `OPEN.md`.

Supporting files (all under `HPC/Hagopian/`):
* `H76Nondeg` — §0.1 and §2d.4: `crossingIntervals_nondegenerate_of` (Property 3 as printed gives
  `x < y` for every `[x, y] ∈ I`) and `crossingComponents_finite_of` (finitely many crossing
  components);
* `H76Uniform`, `H76Uniform2`, `H76Uniform3` — §4: the heights of Property 3, of "`I` is finite",
  of `x₂ₙ = 1` and of the middle-crossing lemmas chosen before `G` (`…_unif`); with them
  `crossingIntervals_nondegenerate` and `crossing_components_finite`;
* `H76PieceB` — §3.2 (4.B): `isCrossingPiece_of_crossingComponent` and `p_on_crossing_piece`;
* `H76Final179` — §3.3–3.5: `sep_by_crossing_uncond`, `exists_blocks_uncond`,
  `hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`, `hagopian76_T15_T17_cond3`;
* `H76Thm1Setup` — §5: `Thm1Setup`, `exists_thm1Setup` (T1–T13 assembled) and
  `hagopian76_theorem1_of_step`.

Skeleton items and where they are:

| skeleton item | status | Lean |
|---|---|---|
| `tip_triod`, `tip_triod_on_tip_layer`, `no_end_layer_chunk` (2a, 2b, 2d) | open | — |
| `crossing_components_finite` (2d.4) | proved | `crossing_components_finite` |
| `innerComponentsCross_hagopian` (2e) | open | named `Prop` `InnerComponentsCross` |
| `block_components_cross` (3c) | open | — |
| `p_on_crossing_piece` (4.B) | proved | `p_on_crossing_piece` |
| `sep_by_crossing_uncond` (3.3) | proved, from 2e only | `sep_by_crossing_uncond` |
| `hagopian76_x2n_eq_one_final` | proved, from 2e only | `hagopian76_x2n_eq_one_final` |
| `hagopian76_property4_top_final` | proved, from 2e only | `hagopian76_property4_top_final` |
| `exists_blocks_uncond` (3.4) | proved, from `x₂ₙ = 1` only | `exists_blocks_uncond` |
| `uniform_heights` (§4) | proved | the `…_unif` theorems |
| `property4_step_unless`, `first_strand`, `property2_far_from_I`, `case1_cap`, `case1_local_to_global`, `case2`, `hagopian76_property4_step` (§6) | open | named `Prop` `Property4Step` |
| `hagopian76_theorem1_of_step` (§5) | proved, with 2e as a second hypothesis | `hagopian76_theorem1_of_step` |
| `hagopian76_theorem1_final` | open | — |
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## Open items

The obstructions are in `OPEN.md` (batch 179) and in `doc/batches/REPORT-batch179.md`.

(Batch 180: 2a, 2b and 2c are proved in `H76Tip.lean` (`tip_triod`, `tip_triod_on_tip_layer`,
`degenerate_chunk_iii`); the open items below are restated in `Hagopian76Y.lean`.)

**OPEN (2a, 2b, 2d, 2e: `tip_triod`, `tip_triod_on_tip_layer`, `no_end_layer_chunk`,
`innerComponentsCross_hagopian`).** Not formalized. Report §1.2 checks the route of commission 179
§2 informally and records two points: (i) in 2d.5 the statement "`hⱼ[E]` meets `O` over the inner
middle only inside `Sⱼ`" needs the point `c` over `(3/22 + 4/n, 19/22 − 4/n)`, not only over the
inner middle (S0 moves the parameter by `2/n`, and the strand contains only the translated layers
with parameter in `(3/22 + 2/n, 19/22 − 2/n)`); (ii) the triods of 2a, 2b need `Z = Λ₁ ∪ h[k⁻¹(τ)]`
to be a continuum (as in the definition of a triod); when `Λ₁` is nonempty this needs `Λ₁` to meet
the tip layer, which the commission does not address (to be checked). `InnerComponentsCross` stays a named
hypothesis of `sep_by_crossing_uncond`, `hagopian76_T15_T17_cond3` and
`hagopian76_theorem1_of_step`.

theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 3 / (S.n : ℝ)) (19 / 22 - 3 / (S.n : ℝ)) := by
  sorry

-- `block_components_cross` (3c): proved in batch 181 (`H76Block3c.lean`), with saturation as a hypothesis.

**OPEN (§6: E0, E1, E2.1, E2.4, the cap, E2.5, Case 2; `hagopian76_property4_step`).** E0 and E1
need 3c (the components of `d⁻¹[B] ∩ O` through the low vertical are pieces of the frame). E2.1
(the shortest extension `L`), E2.4 (the continuum `H ⊆ L`), the cap (`P ∩ Q` is the two ends of
`Q`), E2.5 (a second frame in `O_L`) and Case 2 are not started. See
`doc/notes/hagopian76-cases.md`.

theorem hagopian76_property4_step (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ)
    (hx : S.IsBlocks x m) : Property4Step S.D x m := by
  sorry

**OPEN (`hagopian76_theorem1_final`).** By `hagopian76_theorem1_of_step`, it follows from
`innerComponentsCross_hagopian` and `hagopian76_property4_step` (both above, for every set-up).

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
