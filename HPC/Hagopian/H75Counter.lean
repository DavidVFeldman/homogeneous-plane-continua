import HPC.Hagopian.H75Basic

/-!
# Batch 155: two statements of the skeleton that are false as stated

* `not_admissible_end_sets`: the second half of `admissible_end_sets` ("a subcontinuum meeting both
  end layers is all of `E`") is false without the type A′ condition `hk0`. On `E = [0, 2] ⊆ ℝ`
  (irreducible between `0` and `2`), `k(x) = max 0 (x − 1)` is admissible; its end layer `k⁻¹(0)` is
  `[0, 1]`, and `K = [1, 2]` meets both end layers but is not `E`. With `hk0` the statement holds
  (`eq_of_meets_ends`, `admissible_end_sets'` in `Hagopian75.lean`).
* `arc_of_degenerate_layers'`: the corrected form of `arc_of_degenerate_layers` (see there for the
  counterexample to the printed form): if *every* layer of an admissible map is degenerate, `k` is a
  homeomorphism onto `[0, 1]`.
-/

namespace HPC.Hagopian

open Set Topology

/-- The admissible map `x ↦ max 0 (x − 1)` of `[0, 2]`. -/
noncomputable def endSetsMap : (Icc (0 : ℝ) 2) → unitInterval := fun x =>
  ⟨max 0 (x.1 - 1), le_max_left _ _, max_le zero_le_one (by linarith [x.2.2])⟩

theorem isIrreducibleBetween_Icc_zero_two : IsIrreducibleBetween (Icc (0 : ℝ) 2) 0 2 :=
  ⟨⟨isCompact_Icc, isConnected_Icc (by norm_num)⟩, ⟨le_rfl, by norm_num⟩, ⟨by norm_num, le_rfl⟩,
    fun _ hK hKE h0 h2 => Subset.antisymm hKE (hK.2.isPreconnected.Icc_subset h0 h2)⟩

theorem isAdmissibleMap_endSetsMap : IsAdmissibleMap (Icc (0 : ℝ) 2) endSetsMap := by
  refine ⟨?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_const.max (continuous_subtype_val.sub continuous_const)) _
  · intro t
    refine ⟨⟨1 + t, by linarith [t.2.1], by linarith [t.2.2]⟩, Subtype.ext ?_⟩
    simp only [endSetsMap, add_sub_cancel_left]
    exact max_eq_right t.2.1
  · intro t
    obtain ⟨y₀, hy₀⟩ : ∃ y, endSetsMap y = t := by
      refine ⟨⟨1 + t, by linarith [t.2.1], by linarith [t.2.2]⟩, Subtype.ext ?_⟩
      simp only [endSetsMap, add_sub_cancel_left]
      exact max_eq_right t.2.1
    refine ⟨⟨y₀, hy₀⟩, ?_⟩
    rw [← IsInducing.subtypeVal.isPreconnected_image]
    apply Set.OrdConnected.isPreconnected
    refine ⟨?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩ y ⟨hxy, hyz⟩
    have hyE : y ∈ Icc (0 : ℝ) 2 := ⟨x.2.1.trans hxy, hyz.trans z.2.2⟩
    refine ⟨⟨y, hyE⟩, ?_, rfl⟩
    have hx' : max 0 (x.1 - 1) = t.1 := congrArg Subtype.val (mem_singleton_iff.1 hx)
    have hz' : max 0 (z.1 - 1) = t.1 := congrArg Subtype.val (mem_singleton_iff.1 hz)
    refine mem_singleton_iff.2 (Subtype.ext ?_)
    show max 0 (y - 1) = t.1
    apply le_antisymm
    · rw [← hz']; exact max_le_max le_rfl (by linarith)
    · rw [← hx']; exact max_le_max le_rfl (by linarith)

/-- **`admissible_end_sets` is false as stated** (its second half, without `hk0`). -/
theorem not_admissible_end_sets :
    ¬ ∀ (E : Set ℝ) (a b : ℝ) (hE : IsIrreducibleBetween E a b), a ≠ b →
      ∀ k : E → unitInterval, IsAdmissibleMap E k →
        ((k ⟨a, hE.2.1⟩ = 0 ∧ k ⟨b, hE.2.2.1⟩ = 1) ∨ (k ⟨a, hE.2.1⟩ = 1 ∧ k ⟨b, hE.2.2.1⟩ = 0)) ∧
          ∀ K ⊆ E, Fold.Q78.IsContinuum K → (K ∩ layer k 0).Nonempty →
            (K ∩ layer k 1).Nonempty → K = E := by
  intro h
  have := (h _ 0 2 isIrreducibleBetween_Icc_zero_two (by norm_num) endSetsMap
    isAdmissibleMap_endSetsMap).2 (Icc 1 2) (Icc_subset_Icc (by norm_num) le_rfl)
    ⟨isCompact_Icc, isConnected_Icc (by norm_num)⟩
    ⟨1, ⟨le_rfl, by norm_num⟩, ⟨⟨1, by norm_num, by norm_num⟩, Subtype.ext (by simp [endSetsMap]),
      rfl⟩⟩
    ⟨2, ⟨by norm_num, le_rfl⟩, ⟨⟨2, by norm_num, le_rfl⟩, Subtype.ext (by norm_num [endSetsMap]),
      rfl⟩⟩
  have h0 : (0 : ℝ) ∈ Icc (1 : ℝ) 2 := this ▸ ⟨le_rfl, by norm_num⟩
  exact absurd h0.1 (by norm_num)

/-- **Paragraph 4's alternative, corrected**: if every layer is degenerate, `k` is a homeomorphism. -/
theorem arc_of_degenerate_layers' {X : Type*} [MetricSpace X] {E : Set X} (hEc : IsCompact E)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k)
    (hdeg : ∀ s : unitInterval, (layer k s).Subsingleton) : Nonempty (E ≃ₜ unitInterval) := by
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc
  have hinj : Function.Injective k := by
    intro x y hxy
    exact Subtype.ext (hdeg (k x) ⟨x, rfl, rfl⟩ ⟨y, hxy.symm, rfl⟩)
  exact ⟨(hk.1.homeoOfEquivCompactToT2 (f := Equiv.ofBijective k ⟨hinj, hk.2.1⟩))⟩

/-- **Paragraph 4's alternative, in the form used** ("`E` would contain an arc"): if every interior
layer is degenerate, `E` contains an arc, namely `k⁻¹[1/3, 2/3]`. -/
theorem exists_arc_of_degenerate_layers {X : Type*} [MetricSpace X] {E : Set X}
    (hEc : IsCompact E) {k : E → unitInterval} (hk : IsAdmissibleMap E k)
    (hdeg : ∀ s : unitInterval, 0 < s → s < 1 → (layer k s).Subsingleton) :
    ∃ A ⊆ E, Nonempty (A ≃ₜ unitInterval) := by
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc
  set F : Set E := k ⁻¹' {u | (1 / 3 : ℝ) ≤ u.1 ∧ u.1 ≤ 2 / 3}
  have hFc : IsClosed F := by
    refine IsClosed.preimage hk.1 ?_
    exact (isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc.isCompact
  set g : F → unitInterval := fun w => ⟨3 * ((k w).1 - 1 / 3), by
    have := w.2.1; linarith, by have := w.2.2; linarith⟩
  have hgc : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.mul ((continuous_subtype_val.comp
      (hk.1.comp continuous_subtype_val)).sub continuous_const)
  have hginj : Function.Injective g := by
    intro w w' hww'
    have h1 : (k w).1 = (k w').1 := by
      have := congrArg Subtype.val hww'
      simp only [g] at this
      linarith
    have hkw : k w = k w' := Subtype.ext h1
    have h0 : (0 : unitInterval) < k w := by
      show (0 : ℝ) < (k w).1; have := w.2.1; linarith
    have h1' : k w < 1 := by
      show (k w).1 < 1; have := w.2.2; linarith
    exact Subtype.ext (Subtype.ext (hdeg (k w) h0 h1' ⟨w, rfl, rfl⟩ ⟨w', hkw.symm, rfl⟩))
  have hgsurj : Function.Surjective g := by
    intro u
    obtain ⟨w, hw⟩ := hk.2.1 ⟨1 / 3 + u.1 / 3, by linarith [u.2.1], by linarith [u.2.2]⟩
    have hwF : w ∈ F := by
      show (1 / 3 : ℝ) ≤ (k w).1 ∧ (k w).1 ≤ 2 / 3
      rw [hw]; constructor <;> simp only <;> linarith [u.2.1, u.2.2]
    refine ⟨⟨w, hwF⟩, Subtype.ext ?_⟩
    simp only [g, hw]
    ring
  set e : F ≃ₜ unitInterval := hgc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hginj, hgsurj⟩)
  set f : F → X := fun w => ((w : E) : X)
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  refine ⟨range f, ?_, ⟨hf.toHomeomorph.symm.trans e⟩⟩
  rintro _ ⟨w, rfl⟩
  exact (w : E).2

end HPC.Hagopian
