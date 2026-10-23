import HPC.Hagopian.Hagopian76V

/-!
# Batch 178 skeleton: Hagopian 1976, Theorem 1 — the order of strands without Schoenflies;
# separation along the vertical; the end layer of `F`; unicoherence; the assembly; the step

Save as `HPC/Hagopian/Hagopian76W.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76W` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 178 §1–§8.
Notation (commission 178 §1): `O = π⁻¹[F[D′]]`, `Y = π⁻¹[Fr D]`, `σ` the low vertical over `1/2`,
*crossing piece*, `A(X)` / `B(X)` (below / above), `X′ ≺ X`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §5. Unicoherence of the plane -/

/-- **Two continua with disconnected intersection separate the plane** (the converse of
Janiszewski's theorem; unicoherence in separation form). Route (commission 178 §5):
`borsuk_exists_log` applied to `exp(πiφ)` on `A`, `exp(−πiφ)` on `B`,
`φ = d(·, K₁) / (d(·, K₁) + d(·, K₂))`. The closed-cover form is `HPC.Moore.plane_unicoherent`. -/
theorem separatesPlane_union_of_inter_disconnected {A B K₁ K₂ : Set Pt} (hA : IsCompact A)
    (hAc : IsConnected A) (hB : IsCompact B) (hBc : IsConnected B) (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂) (hAB : A ∩ B = K₁ ∪ K₂) (hK : Disjoint K₁ K₂) (hK₁n : K₁.Nonempty)
    (hK₂n : K₂.Nonempty) :
    SeparatesPlane (A ∪ B) := by
  sorry

/-- **Separation in a domain is separation in the plane with the frontier continuum adjoined**
(commission 178 §3a step 3, §5): for `Y` compact, connected, disjoint from `O`, containing
`Fr O`, and `X` compact, `SepIn O X p q ↔ SeparatesPts (X ∪ Y) p q` for `p, q ∈ O − X`.
*Shape left to you.* -/
theorem sepIn_iff_separatesPts_union : True := by
  sorry

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. The order of crossing pieces (S4, without Schoenflies) -/

/-- **S4a**: every crossing piece meets the low vertical `σ` (from `rect_domain_crosscut`).
*Shape left to you* (define `IsCrossingPiece` if useful). -/
theorem crossing_piece_meets_sigma : True := by
  sorry

/-- **S4b, totality**: for disjoint crossing pieces `X`, `X′`: `X′ ⊆ A(X)` or `X′ ⊆ B(X)`.
*Shape left to you.* -/
theorem crossing_piece_sides : True := by
  sorry

/-- **S4c, antisymmetry** (symmetric form): `X′ ⊆ A(X) ↔ X ⊆ B(X′)`. *Shape left to you.* -/
theorem crossing_piece_below_iff : True := by
  sorry

/-- **S4d, transitivity**: `X″ ≺ X′ ≺ X → X″ ≺ X`. *Shape left to you.* -/
theorem crossing_piece_below_trans : True := by
  sorry

/-! ## §2. Separation along the vertical -/

/-- **SSL**: if compact `Z ⊆ M` separates `x` from `y` in `O`, and `x`, `y` lie on crossing pieces
`X`, `Y` missing `Z`, then `Y ≺ X` (say) and some `z ∈ Z` on the open `σ`-segment between closest
points of `Y` and `X` exists; if the component `W_z` of `Z ∩ O` is crossing, `Y ≺ W_z ≺ X` and
`Cl W_z` separates `x` from `y`. With the converse. *Shape left to you.* -/
theorem strand_separation : True := by
  sorry

/-- **`SepByCrossing`, general form**: if every component of `Z ∩ O` meeting `σ` is crossing, and
the strands of `x`, `y` miss `Z`, then `SepIn O Z x y` gives separation by one crossing closure.
*Shape left to you.* -/
theorem sepByCrossing_of_inner_crossing : True := by
  sorry

/-! ## §3. The end layer of `F`, and saturation -/

/-- **3a**: for a `T12Data` package, `d⁻¹(1) ⊄ π⁻¹[D]` (irreducibility, Janiszewski,
`no_proper_subcontinuum_separates`). *Shape left to you.* -/
theorem T12Data.end_layer_not_subset : True := by
  sorry

/-- **3b, saturation** (`InnerComponentsCross D` if it stays open): every component of `F ∩ O`
through a point over the inner middle is crossing. *Shape left to you.* -/
theorem inner_components_cross : True := by
  sorry

/-- **3c**: blocks inherit saturation; gap layers and block end layers miss the inner middle of
`O`. *Shape left to you.* -/
theorem block_components_cross : True := by
  sorry

/-! ## §4. `SepByCrossing`, `x₂ₙ = 1`, the top block -/

/-- **4.A**: the base point `x₀` and the composant conditions `h x₀, h₁ x₀ ∉ composant x₀`, as
fields of `T12Data` or a companion `exists_T12Data'`; hence the strands of all points of
`h[R(E)] ∪ h₁[R(E)]` miss `F`. *Shape left to you.* -/
theorem strand_misses_F_of_composant : True := by
  sorry

/-- **4.C**: `SepByCrossing` for Hagopian's `F`, `p`, `f(p)`. *Shape left to you.* -/
theorem sep_by_crossing : True := by
  sorry

/-- **4.C**: `x₂ₙ = 1` ("Note that `x₂ₙ = 1`", p. 348). *Shape left to you.* -/
theorem hagopian76_x2n_eq_one_final : True := by
  sorry

/-- **4.C**: Property 4 for the top block (p. 348). *Shape left to you.* -/
theorem hagopian76_property4_top_final : True := by
  sorry

/-! ## §6. The blocks -/

/-- **C′**: the blocks are the components of `St J`; each block is a union of members of `J`;
`x₁ = 0`, `x₂ = e`, `x₂ₙ = 1`. *Shape left to you.* -/
theorem exists_blocks : True := by
  sorry

/-! ## §8. The induction step -/

/-- **E1** ("… and `J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`", p. 348): if a `J`-strand lies
between `Cᵢ` and the strand of `f(yᵢ)`, `J` has Property 4 with `yᵢ₋₁ = yᵢ`.
*Shape left to you.* -/
theorem property4_step_unless : True := by
  sorry

/-- **E2.1**: the first strand `Cᵢ₋₁` met by extending `Cl Cᵢ` away from `X` in `h[R(E)]`; `L`
misses `F` and meets the inner middle in whole strands except at its ends. *Shape left to you.* -/
theorem first_strand : True := by
  sorry

/-- **E2.2**: `N` stays `ε₂` away from the low vertical over `15/22` (Case 1).
*Shape left to you.* -/
theorem N_far_from_p4 : True := by
  sorry

/-- **E2.3, the cap** (Case 1): `P = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q` (or `∪ V`) separates `yᵢ` from `f(yᵢ)`
in the plane; checks (α), (β), (γ) of commission 178 §8. *Shape left to you.* -/
theorem case1_cap : True := by
  sorry

/-- **E2.4** ("for otherwise, a subcontinuum of `L` would violate Property 2"):
`ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`. *Shape left to you.* -/
theorem property2_far_from_I : True := by
  sorry

/-- **E2.5, local to global**: from separation by `P` to a `J`-strand between `Cᵢ₋₁` and the
strand of `f(yᵢ₋₁)`. *Shape left to you.* -/
theorem case1_local_to_global : True := by
  sorry

/-- **E2.6**: Case 2 (p. 349). *Shape left to you.* -/
theorem case2 : True := by
  sorry

/-- **E**: `Property4Step` (Cases 1–2), or the strongest conditional form. *Shape left to you.* -/
theorem hagopian76_property4_step : True := by
  sorry

end Thm1

/-! ## §7. The assembly -/

/-- **§7**: Theorem 1 from the step alone: `Thm1Setup` bundles T1–T13 with the constants in the
order of commission 177 §2, and `(∀ S : Thm1Setup, Property4Step S.D S.x S.n) → Hagopian76Thm1`
(with `InnerComponentsCross` as a second hypothesis if 3b stays open). *Shape left to you.* -/
theorem hagopian76_theorem1_of_step : True := by
  sorry

/-- **Theorem 1** (p. 345), or the strongest conditional form. *Shape left to you.* -/
theorem hagopian76_theorem1_final : True := by
  sorry

end HPC.Hagopian
