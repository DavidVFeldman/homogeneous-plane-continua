import HPC.BJ59.Homog

/-!
# Batch 198, library: the circle, the pseudo-arc and circles of pseudo-arcs are distinct

* `isDecomposableSpace_circle`: the circle is the union of its two half-circles;
* `isDecomposableSpace_of_isCircPAMap`: a circle of pseudo-arcs is the union of its two halves;
* `not_isPseudoArc_of_ne_univ_circle`: no proper subset of the circle is a pseudo-arc (cut the
  circle at a missing point; the argument embeds the set in `ℝ`, where a non-degenerate continuum
  is an interval, which is decomposable);
* `exists_plane_circle`: a plane simple closed curve.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane HPC.Jones

/-- The image of a continuum under a continuous map is a continuum. -/
theorem isContinuum_range_halfC (s : ℝ) : Fold.Q78.IsContinuum (range (halfC s)) :=
  ⟨isCompact_range (continuous_halfC s), isConnected_range (continuous_halfC s)⟩

/-- **The circle is decomposable**: the two half-circles. -/
theorem isDecomposableSpace_circle : IsDecomposableSpace Circle := by
  refine ⟨_, _, isContinuum_range_halfC 1, isContinuum_range_halfC (-1), ?_, ?_,
    range_halfC_union⟩
  · obtain ⟨z, hz⟩ := exists_not_mem_range_halfC (s := 1) (Or.inl rfl)
    exact fun h => hz (h ▸ mem_univ z)
  · obtain ⟨z, hz⟩ := exists_not_mem_range_halfC (s := -1) (Or.inr rfl)
    exact fun h => hz (h ▸ mem_univ z)

theorem isContinuum_halfSet {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → Circle}
    (hf : IsCircPAMap f) (s : ℝ) : Fold.Q78.IsContinuum (halfSet f s) := by
  refine ⟨(isClosed_halfSet hf.cont s).isCompact, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hf.surj (halfC s 0); exact ⟨x, 0, hx.symm⟩
  · exact isPreconnected_preimage_of_monotone' hf.cont
      (fun z => (hf.fib z).1.1.2.isPreconnected)
      (isPreconnected_range (continuous_halfC s)) (fun z _ => hf.surj z)

/-- **A circle of pseudo-arcs is decomposable**: the two halves. -/
theorem isDecomposableSpace_of_isCircPAMap {X : Type*} [MetricSpace X] {f : X → Circle}
    (hf : IsCircPAMap f) : IsDecomposableSpace X := by
  haveI := hf.compactSpace
  have hne : ∀ {s : ℝ}, (s = 1 ∨ s = -1) → halfSet f s ≠ univ := fun hs h => by
    obtain ⟨z, hz⟩ := exists_not_mem_range_halfC hs
    obtain ⟨x, hx⟩ := hf.surj z
    have : x ∈ halfSet f _ := h ▸ mem_univ x
    exact hz (hx ▸ this)
  refine ⟨_, _, isContinuum_halfSet hf 1, isContinuum_halfSet hf (-1), hne (Or.inl rfl),
    hne (Or.inr rfl), ?_⟩
  ext x; simp only [mem_union, mem_univ, iff_true]
  have := range_halfC_union ▸ mem_univ (f x); exact this

/-- On the circle minus `exp π`, the argument is continuous; it is injective on the circle. -/
theorem continuousAt_arg_circle {w : Circle} (hw : w ≠ Circle.exp Real.pi) :
    ContinuousAt (fun u : Circle => Complex.arg (u : ℂ)) w := by
  refine (Complex.continuousAt_arg ?_).comp continuous_subtype_val.continuousAt
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push_neg at h
  apply hw
  have hn : Complex.normSq (w : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq]; simp
  have him : (w : ℂ).im = 0 := h.2
  rw [Complex.normSq_apply, him] at hn
  have hre : (w : ℂ).re = -1 := by nlinarith [h.1]
  apply Subtype.ext
  rw [Circle.coe_exp]
  apply Complex.ext <;> simp [hre, him]

theorem arg_injective_circle : Function.Injective (fun u : Circle => Complex.arg (u : ℂ)) := by
  intro u v h
  rw [← Circle.exp_arg u, ← Circle.exp_arg v]
  simp only at h
  rw [h]

/-- A non-degenerate interval is decomposable, so it is not hereditarily indecomposable. -/
theorem not_isHereditarilyIndecomposable_of_nontrivial_real {T : Set ℝ}
    (hT : Fold.Q78.IsContinuum T) (hnt : T.Nontrivial) : ¬ IsHereditarilyIndecomposable T := by
  intro hHI
  have hTeq := eq_Icc_of_connected_compact hT.2 hT.1
  set a := sInf T
  set b := sSup T
  have hab : a < b := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    rw [hTeq] at hx hy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact lt_of_le_of_lt hx.1 (lt_of_lt_of_le h hy.2)
    · exact lt_of_le_of_lt hy.1 (lt_of_lt_of_le h hx.2)
  set m := (a + b) / 2
  have ham : a ≤ m := by simp only [m]; linarith
  have hmb : m ≤ b := by simp only [m]; linarith
  obtain ⟨-, hind⟩ := hHI T subset_rfl hT
  have hA : Fold.Q78.IsContinuum (Icc a m) := ⟨isCompact_Icc, isConnected_Icc ham⟩
  have hB : Fold.Q78.IsContinuum (Icc m b) := ⟨isCompact_Icc, isConnected_Icc hmb⟩
  have hAT : Icc a m ⊆ T := by rw [hTeq]; exact Icc_subset_Icc le_rfl hmb
  have hBT : Icc m b ⊆ T := by rw [hTeq]; exact Icc_subset_Icc ham le_rfl
  have hABT : Icc a m ∪ Icc m b = T := by rw [hTeq, Icc_union_Icc_eq_Icc ham hmb]
  rcases hind (Icc a m) (Icc m b) hA hB hAT hBT hABT with h | h
  · have : b ∈ Icc a m := by rw [h, hTeq]; exact ⟨hab.le, le_rfl⟩
    have h2 := this.2; simp only [m] at h2; linarith
  · have : a ∈ Icc m b := by rw [h, hTeq]; exact ⟨le_rfl, hab.le⟩
    have h2 := this.1; simp only [m] at h2; linarith

/-- **No proper subset of the circle is a pseudo-arc.** -/
theorem not_isPseudoArc_of_ne_univ_circle {K : Set Circle} (hK : K ≠ univ) :
    ¬ IsPseudoArc K := by
  intro hPA
  obtain ⟨z, hz⟩ : ∃ z, z ∉ K := by
    by_contra h; push_neg at h; exact hK (eq_univ_of_forall h)
  set c : Circle := Circle.exp Real.pi * z⁻¹
  set φ : Circle → ℝ := fun w => Complex.arg ((c * w : Circle) : ℂ)
  have hcw : ∀ w ∈ K, c * w ≠ Circle.exp Real.pi := fun w hw h => by
    apply hz
    have : w = z := by
      have h' : Circle.exp Real.pi * z⁻¹ * w = Circle.exp Real.pi := h
      have h2 : z⁻¹ * w = 1 := mul_left_cancel (a := Circle.exp Real.pi) (by
        rw [← mul_assoc, h', mul_one])
      exact (inv_mul_eq_one.1 h2).symm
    exact this ▸ hw
  have hφinj : Function.Injective φ := fun u v h =>
    mul_left_cancel (arg_injective_circle h)
  have hmono : IsMonotoneMap φ K (φ '' K) := by
    refine ⟨fun w hw => ?_, rfl, ?_⟩
    · exact ((continuousAt_arg_circle (hcw w hw)).comp
        (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
    · rintro y ⟨w, hw, rfl⟩
      have : K ∩ φ ⁻¹' {φ w} = {w} := by
        ext u; simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨fun h => hφinj h.2, fun h => by subst h; exact ⟨hw, rfl⟩⟩
      rw [this]; exact isConnected_singleton
  have hT : Fold.Q78.IsContinuum (φ '' K) :=
    ⟨hPA.1.1.1.image_of_continuousOn hmono.1, hPA.1.1.2.image _ hmono.1⟩
  have hnt : (φ '' K).Nontrivial := by
    obtain ⟨u, hu, v, hv, huv⟩ := hPA.2.2
    exact ⟨φ u, ⟨u, hu, rfl⟩, φ v, ⟨v, hv, rfl⟩, fun h => huv (hφinj h)⟩
  exact not_isHereditarilyIndecomposable_of_nontrivial_real hT hnt
    (isHereditarilyIndecomposable_image hPA.1.1 hPA.2.1 hmono)

/-- **A plane simple closed curve.** -/
theorem exists_plane_circle : ∃ C : Set Pt, Nonempty (C ≃ₜ Circle) := by
  set j : Circle → Pt := fun z => ((z : ℂ).re, (z : ℂ).im)
  have hj : Continuous j :=
    (Complex.continuous_re.comp continuous_subtype_val).prodMk
      (Complex.continuous_im.comp continuous_subtype_val)
  have hinj : Function.Injective j := fun u v h => by
    simp only [j, Prod.mk.injEq] at h
    exact Subtype.ext (Complex.ext h.1 h.2)
  exact ⟨range j, ⟨(@Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _ (Equiv.ofInjective j hinj)
    (hj.subtype_mk _)).symm⟩⟩

end HPC.BJ59
