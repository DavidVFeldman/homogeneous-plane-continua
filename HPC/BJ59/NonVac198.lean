import HPC.BJ59.BJ59A

/-!
# Batch 198: non-vacuity (commission 198, §8)

* `bj_theorem2`–`bj_theorem4`: `X = [0, 1]`, `f = id` (fibres points) meets every hypothesis
  (`nonvac_arc_id`, `nonvac_bj_theorem2`, `nonvac_bj_theorem3`, `nonvac_bj_theorem4`);
* `bj_theorem6`: a two-map example with `n = m = 3` (`nonvac_bj_theorem6`);
* `circle_or_circleOfPA_of_decomposable`, `ho16_classification`: a plane circle meets the
  hypotheses on `M` (`nonvac_plane_circle`);
* `BJThm10`: its hypotheses are met by the two halves of any circle of pseudo-arcs
  (`nonvac_bjThm10_halves`), so by `BJPlaneExample`;
* `bj_theorem5`: only a degenerate witness of the repaired core (`nonvac_theorem5_repaired_degenerate`,
  chain with no links); point fibres cannot meet `hE` and `hEU` together
  (`bj_theorem5_hyps_fail_id`).
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane HPC.Jones HPC.HO16

/-- `[0, 1]` with `f = id` is a snake-like arc of continua. -/
theorem nonvac_arc_id :
    IsArcOfContinua (id : unitInterval → unitInterval) ∧ IsSnakeLike (univ : Set unitInterval) :=
  ⟨isArcOfContinua_id, isSnakeLike_univ_unitInterval⟩

/-- A point of `[0, 1]` from a real number in `[0, 1]`. -/
private def pt (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : unitInterval := ⟨r, h0, h1⟩

/-- `bj_theorem2` applied to `[0, 1]`, `f = id`, `a, b, c, d = 1/5, 2/5, 3/5, 4/5`. -/
theorem nonvac_bj_theorem2 :
    ∃ ε > 0, ∀ (n : ℕ) (D : Chain unitInterval n), IsEpsChain D ε → univ ⊆ D.union →
      ∀ i j k : Fin n, (D.link i ∩ id ⁻¹' Icc 0 (pt (1/5) (by norm_num) (by norm_num))).Nonempty →
        (D.link j ∩ id ⁻¹' Icc (pt (2/5) (by norm_num) (by norm_num))
          (pt (3/5) (by norm_num) (by norm_num))).Nonempty →
        (D.link k ∩ id ⁻¹' Icc (pt (4/5) (by norm_num) (by norm_num)) 1).Nonempty →
          (i < j ∧ j < k) ∨ (k < j ∧ j < i) :=
  bj_theorem2 isArcOfContinua_id isSnakeLike_univ_unitInterval
    (by change (0 : ℝ) < 1/5; norm_num) (by change (1/5 : ℝ) < 2/5; norm_num)
    (by change (2/5 : ℝ) < 3/5; norm_num) (by change (3/5 : ℝ) < 4/5; norm_num)
    (by change (4/5 : ℝ) < 1; norm_num)

/-- `bj_theorem3` applied to `[0, 1]`, `f = id`, `ε = 1/10`. -/
theorem nonvac_bj_theorem3 :
    ∃ (m : ℕ) (D : Chain unitInterval (m + 1)), IsEpsChain D (1/10) ∧ univ ⊆ D.union ∧
      (D.link 0 ∩ id ⁻¹' {0}).Nonempty ∧ (D.link (Fin.last m) ∩ id ⁻¹' {1}).Nonempty :=
  bj_theorem3 isArcOfContinua_id isSnakeLike_univ_unitInterval (by norm_num)

/-- `bj_theorem4` applied to `[0, 1]`, `f = id`, `U = (1/4, 3/4)`. -/
theorem nonvac_bj_theorem4 :
    ∃ A B : Set unitInterval, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧
      A ∪ B = {x : unitInterval | (1 / 4 : ℝ) < x ∧ (x : ℝ) < 3 / 4}ᶜ ∧
      id ⁻¹' {0} ⊆ A ∧ id ⁻¹' {1} ⊆ B := by
  refine bj_theorem4 isArcOfContinua_id isSnakeLike_univ_unitInterval
    ((isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const))
    ⟨pt (1/2) (by norm_num) (by norm_num), by norm_num [pt], by norm_num [pt]⟩ ?_
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ (hx | hx)
  · have : (x : ℝ) = 0 := congrArg Subtype.val hx
    linarith
  · have : (x : ℝ) = 1 := congrArg Subtype.val hx
    linarith

/-- `bj_theorem6` with `n = m = 3`: the constant map onto the middle link and the identity are
chain maps, each taking a link to `e₂` (index `1`). -/
theorem nonvac_bj_theorem6 :
    IsChainMap (fun _ : Fin 3 => (1 : Fin 3)) ∧ IsChainMap (fun i : Fin 3 => i) ∧
      ∃ i : Fin 3, (((1 : Fin 3) : ℤ) - (i : ℤ)).natAbs ≤ 1 := by
  have h₁ : IsChainMap (fun _ : Fin 3 => (1 : Fin 3)) := fun _ _ _ => by simp
  have h₂ : IsChainMap (fun i : Fin 3 => i) := fun _ _ h => h
  exact ⟨h₁, h₂, bj_theorem6 h₁ h₂ ⟨0, rfl⟩ ⟨1, rfl⟩⟩

/-- A plane circle meets the hypotheses on `M` of `circle_or_circleOfPA_of_decomposable` and
`ho16_classification`: compact, connected, non-degenerate, homogeneous and decomposable. -/
theorem nonvac_plane_circle : ∃ C : Set Pt, CompactSpace C ∧ ConnectedSpace C ∧
    (univ : Set C).Nontrivial ∧ IsHomogeneous C ∧ IsDecomposableSpace C := by
  obtain ⟨C, ⟨e⟩⟩ := exists_plane_circle
  haveI : ConnectedSpace Circle := Function.Surjective.connectedSpace (f := Circle.exp)
    (fun z => ⟨_, Circle.exp_arg z⟩) (map_continuous Circle.exp)
  refine ⟨C, e.symm.compactSpace, e.symm.surjective.connectedSpace e.symm.continuous, ?_,
    IsHomogeneous.of_homeomorph e.symm isHomogeneous_circle,
    IsDecomposableSpace.of_homeomorph e.symm isDecomposableSpace_circle⟩
  exact ⟨e.symm 1, mem_univ _, e.symm (Circle.exp Real.pi), mem_univ _,
    fun h => circle_exp_pi_ne_one (e.symm.injective h).symm⟩

/-- The hypotheses of `BJThm10` are met by the halves of a circle of pseudo-arcs. -/
theorem nonvac_bjThm10_halves {X : Type*} [MetricSpace X] {f : X → Circle} (hf : IsCircPAMap f)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    CompactSpace (halfSet f s) ∧ IsContArcPA (halfMap f hs) ∧
      IsSnakeLike (univ : Set (halfSet f s)) := by
  haveI := hf.compactSpace
  exact ⟨isCompact_iff_compactSpace.1 (isClosed_halfSet hf.cont s).isCompact,
    isContArcPA_halfMap hf hs, isSnakeLike_halfSet hf hs⟩

/-- The chain with no links. -/
private def emptyChain (X : Type*) [MetricSpace X] : Chain X 0 :=
  ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- The hypotheses of the repaired Theorem 5 without `hE`/`hUE` (`theorem5_repaired`) are jointly
satisfiable, but only degenerately: `[0, 1]`, `f = id`, `U = (1/4, 3/4)` and the chain with no
links. -/
theorem nonvac_theorem5_repaired_degenerate :
    ∃ A B : Set unitInterval, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧
      A ∪ B = {x : unitInterval | (1 / 4 : ℝ) < x ∧ (x : ℝ) < 3 / 4}ᶜ ∧
      id ⁻¹' {0} ⊆ A ∧ id ⁻¹' {1} ⊆ B := by
  obtain ⟨A, B, hA, hB, hAB, hU, h0, h1, -⟩ := theorem5_repaired
    (U := {x : unitInterval | (1 / 4 : ℝ) < x ∧ (x : ℝ) < 3 / 4}) isArcOfContinua_id IsOpenMap.id
    isSnakeLike_univ_unitInterval (fun t => isIndecomposable_singleton t) (emptyChain _)
    ((isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const))
    ⟨pt (1/2) (by norm_num) (by norm_num), by norm_num [pt], by norm_num [pt]⟩
    (by
      rw [Set.disjoint_left]
      rintro x ⟨h1, h2⟩ (hx | hx)
      · have : (x : ℝ) = 0 := congrArg Subtype.val hx
        linarith
      · have : (x : ℝ) = 1 := congrArg Subtype.val hx
        linarith)
    (fun _ i => i.elim0)
  exact ⟨A, B, hA, hB, hAB, hU, h0, h1⟩

/-- **`bj_theorem5`'s hypotheses fail for point fibres.** On `[0, 1]` with `f = id`, no chain
covering the space satisfies `hEU` for a nonempty `U`: a link through a point of `U` meets that
point's fibre only inside `U`. So a witness for `bj_theorem5` needs non-degenerate fibres (a
circle-of-pseudo-arcs-type space); none is available unconditionally. -/
theorem bj_theorem5_hyps_fail_id {n : ℕ} (E : Chain unitInterval n) (hE : univ ⊆ E.union)
    {U : Set unitInterval} (hUne : U.Nonempty) :
    ¬ ∀ t i, ¬ E.link i ∩ id ⁻¹' {t} ⊆ closure U := by
  intro h
  obtain ⟨p, hp⟩ := hUne
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hE (mem_univ p))
  refine h p i ?_
  rintro x ⟨-, hx⟩
  rw [mem_preimage, id, mem_singleton_iff] at hx
  exact subset_closure (hx ▸ hp)

end HPC.BJ59
