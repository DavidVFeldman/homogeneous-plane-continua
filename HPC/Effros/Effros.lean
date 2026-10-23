import HPC.Effros.Fat
import HPC.Effros.OpenMapping
import HPC.Effros.HomeoGroup

/-!
# Batch 134: the Effros theorem (van Mill's elementary proof) and Ungar's corollary

Part C of the classification project. The skeleton of the commission is kept verbatim at
`doc/batches/skeletons/Effros.lean`; this file and its three imports carry out every item.

Source: J. van Mill, *A note on the Effros theorem*, Amer. Math. Monthly 111 (2004), 801–806
(`doc/sources/vanmill2004.pdf`).

## Where the items are

* §A. Meager and fat sets (`HPC/Effros/Fat.lean`): `NowhereMeagre`, `IsFat`, `IsFat.mono`,
  `IsFat.diff_meagre` (Lemma 2.1), `nonempty_interior_closure_of_not_meagre`,
  `inter_nonempty_of_isFat` (Proposition 2.2), and its relative form
  `inter_nonempty_of_nowhereMeagre`, used in Proposition 3.5.
* §B. The open mapping principle (`HPC/Effros/OpenMapping.lean`): `exists_vanMill_basis`,
  `orbitPart`, `vanMill_3_1` … `vanMill_3_5`, `effros_open_mapping`, `isOpenMap_smul_left`.
* §C. The homeomorphism group (`HPC/Effros/HomeoGroup.lean`): the group, topology,
  `IsTopologicalGroup`, `PolishSpace`, the action, `ContinuousSMul`, `supMove`,
  `supMove_symm`, `supMove_symm_trans_le`, `hasBasis_supMove`, `supMove_ball_mem_nhds`.
* §D. Ungar's corollary (this file): `effros_homogeneous`, `effros_homogeneous_set`.

## Shape changes against the skeleton

* `vanMill_3_1`, `vanMill_3_3`: the unused hypothesis `U 0 = univ` is dropped.
* `vanMill_3_4`: the unused hypotheses `U 0 = univ` and "basis of `𝓝 1`" are dropped.
* `vanMill_3_5`: the unused hypothesis `U 0 = univ` is dropped.
* Proposition 2.2 is also proved in a relative form (`inter_nonempty_of_nowhereMeagre`: `S`
  nonempty and `S ⊆ closure T` instead of both dense); the skeleton's statement is a corollary.
-/

namespace HPC.Effros

open Set Topology Filter Metric MeasureTheory

/-! ### §D. Ungar's corollary -/

/-- **Effros–Ungar.** Let `Y` be a homogeneous compact metric space. For every `ε > 0` there is
`δ > 0` such that any two points at distance `< δ` are carried one to the other by a
homeomorphism moving no point by `ε` or more.

Proof: §B for the Polish group of §C; `orbitPart {h | supMove h < ε/2} z` is a neighbourhood of
`z` (`effros_open_mapping`). Take a Lebesgue number `δ` of the open cover by the interiors of these
sets. If `x, y ∈ U • z`, say `x = g z`, `y = h z`, then `y = (h * g⁻¹) x` with
`supMove (h * g⁻¹) ≤ supMove h + supMove g < ε`. -/
theorem effros_homogeneous {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    (hom : ∀ x y : Y, ∃ h : Y ≃ₜ Y, h x = y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : Y, dist x y < δ → ∃ h : Y ≃ₜ Y, h x = y ∧ ∀ z, dist (h z) z < ε := by
  haveI : MulAction.IsPretransitive (Y ≃ₜ Y) Y := ⟨fun x y => hom x y⟩
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨1, one_pos, fun x => isEmptyElim x⟩
  set N := {h : Y ≃ₜ Y | supMove Y h < ε / 2} with hNdef
  have hN : N ∈ 𝓝 1 := supMove_ball_mem_nhds (half_pos hε)
  have hcov : (univ : Set Y) ⊆ ⋃ z, interior (orbitPart N z) := fun z _ =>
    mem_iUnion.2 ⟨z, mem_interior_iff_mem_nhds.2 (effros_open_mapping z hN)⟩
  obtain ⟨δ, hδ, hleb⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ (fun _ => isOpen_interior) hcov
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  obtain ⟨z, hz⟩ := hleb x trivial
  obtain ⟨g, hg, hgx⟩ := interior_subset (hz (mem_ball_self hδ))
  obtain ⟨h, hh, hhy⟩ := interior_subset (hz (by rw [mem_ball, dist_comm]; exact hxy))
  simp only [homeo_smul_def] at hgx hhy
  refine ⟨h * g⁻¹, ?_, fun w => ?_⟩
  · rw [homeo_mul_apply, homeo_inv_def, ← hgx, Homeomorph.symm_apply_apply, hhy]
  · calc dist ((h * g⁻¹) w) w ≤ dist (h (g⁻¹ w)) (g⁻¹ w) + dist (g⁻¹ w) w :=
          dist_triangle _ _ _
      _ ≤ supMove Y h + supMove Y g⁻¹ :=
          add_le_add (dist_le_supMove h _) (dist_le_supMove g⁻¹ w)
      _ = supMove Y h + supMove Y g := by rw [supMove_inv]
      _ < ε / 2 + ε / 2 := add_lt_add hh hg
      _ = ε := add_halves ε

/-- The same for a compact subset of a metric space, homogeneous in its own topology (the form
needed for plane continua `M ⊆ Pt`). -/
theorem effros_homogeneous_set {E : Type*} [MetricSpace E] {M : Set E} (hM : IsCompact M)
    (hom : ∀ x y : M, ∃ h : M ≃ₜ M, h x = y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : M, dist x y < δ → ∃ h : M ≃ₜ M, h x = y ∧ ∀ z, dist (h z) z < ε := by
  haveI := isCompact_iff_compactSpace.mp hM
  exact effros_homogeneous hom hε

end HPC.Effros
