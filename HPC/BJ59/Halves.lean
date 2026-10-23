import HPC.BJ59.Defs
import HPC.BJ59.Transfer
import HPC.BJ59.Arc

/-!
# Batch 198, library: the halves of a circle of pseudo-arcs (commission 198, §4, step 1)

For an open continuous map `f : X → Circle` of a compact circle-like `X` onto the circle with
pseudo-arc fibres, and `s = ±1`, the preimage `f⁻¹(A_s)` of the half-circle
`A_s = {exp(s π t) : t ∈ [0, 1]}`, with `f` followed by the inverse parametrization of `A_s`, is a
continuous snake-like arc of pseudo-arcs (`isContArcPA_halfMap`, `isSnakeLike_halfSet`). Its end
fibres are `f⁻¹(1)` and `f⁻¹(−1)`.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane HPC.Jones

/-! ### The two half-circles -/

theorem halfC_zero (s : ℝ) : halfC s 0 = 1 := by simp [halfC]

theorem halfC_one_eq {s : ℝ} (hs : s = 1 ∨ s = -1) : halfC s 1 = Circle.exp Real.pi := by
  have : halfC s 1 = halfC 1 1 := by
    rcases hs with rfl | rfl
    · rfl
    · rw [halfC_eq_iff]; exact ⟨-1, by push_cast; ring⟩
  rw [this]; simp [halfC]

theorem range_halfC_union : range (halfC 1) ∪ range (halfC (-1)) = univ := by
  have hpi := Real.pi_pos
  refine eq_univ_of_forall fun z => ?_
  rw [← Circle.exp_arg z]
  have h1 := Complex.neg_pi_lt_arg (z : ℂ)
  have h2 := Complex.arg_le_pi (z : ℂ)
  by_cases h : 0 ≤ (z : ℂ).arg
  · left
    refine ⟨⟨(z : ℂ).arg / Real.pi, div_nonneg h hpi.le, (div_le_one hpi).2 h2⟩, ?_⟩
    simp only [halfC]; congr 1; field_simp
  · right
    push_neg at h
    refine ⟨⟨-(z : ℂ).arg / Real.pi, div_nonneg (by linarith) hpi.le,
      (div_le_one hpi).2 (by linarith)⟩, ?_⟩
    simp only [halfC]; congr 1; field_simp

theorem mem_range_halfC_inter {z : Circle} (h1 : z ∈ range (halfC 1))
    (h2 : z ∈ range (halfC (-1))) : z = 1 ∨ z = Circle.exp Real.pi := by
  have hpi := Real.pi_pos
  obtain ⟨t, rfl⟩ := h1
  obtain ⟨t', ht'⟩ := h2
  obtain ⟨m, hm⟩ := halfC_eq_iff.1 ht'
  have ht := t.2; have ht2 := t'.2
  simp only [Set.mem_Icc] at ht ht2
  have hm' : ((t' : ℝ) + t) = -2 * m := by nlinarith
  have hmr : (m : ℝ) ≤ 0 ∧ -1 ≤ (m : ℝ) := ⟨by linarith, by linarith⟩
  have : m = 0 ∨ m = -1 := by
    have a : m ≤ 0 := by exact_mod_cast hmr.1
    have b : -1 ≤ m := by exact_mod_cast hmr.2
    omega
  rcases this with rfl | rfl
  · left
    have : t = 0 := Subtype.ext (by simp at hm'; show (t : ℝ) = 0; linarith)
    rw [this, halfC_zero]
  · right
    have : t = 1 := Subtype.ext (by simp at hm'; show (t : ℝ) = 1; linarith)
    rw [this, halfC_one_eq (Or.inl rfl)]

/-- The point `exp(−s π / 2)` is not on the half-circle `A_s`. -/
theorem exists_not_mem_range_halfC {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ z : Circle, z ∉ range (halfC s) := by
  have hpi := Real.pi_pos
  refine ⟨Circle.exp (-s * Real.pi / 2), ?_⟩
  rintro ⟨t, ht⟩
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 ht
  have ht0 := t.2.1; have ht1 := t.2.2
  rcases hs with rfl | rfl
  · -- `π t = −π/2 + 2πm`
    have h : (t : ℝ) = -1 / 2 + 2 * m := by
      have : 1 * Real.pi * t = -1 * Real.pi / 2 + m * (2 * Real.pi) := hm
      field_simp at this; linarith
    have : (m : ℝ) ≥ 1 / 4 := by linarith
    have : (m : ℝ) ≤ 3 / 4 := by linarith
    have a : 1 ≤ m := by
      by_contra hc; push_neg at hc
      have : m ≤ 0 := by omega
      have : (m : ℝ) ≤ 0 := by exact_mod_cast this
      linarith
    have : (1 : ℝ) ≤ m := by exact_mod_cast a
    linarith
  · have h : (t : ℝ) = -1 / 2 - 2 * m := by
      have : -1 * Real.pi * t = - -1 * Real.pi / 2 + m * (2 * Real.pi) := hm
      field_simp at this; linarith
    have : (m : ℝ) ≤ -1 / 4 := by linarith
    have : (m : ℝ) ≥ -3 / 4 := by linarith
    have a : m ≤ -1 := by
      by_contra hc; push_neg at hc
      have : (0 : ℝ) ≤ m := by exact_mod_cast (show 0 ≤ m by omega)
      linarith
    have : (m : ℝ) ≤ -1 := by exact_mod_cast a
    linarith

/-- The parametrization of `A_s` by `[0, 1]`. -/
noncomputable def halfParam {s : ℝ} (hs : s = 1 ∨ s = -1) : unitInterval ≃ₜ range (halfC s) :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofInjective (halfC s) (injective_halfC hs))
    ((continuous_halfC s).subtype_mk _)

theorem halfParam_apply {s : ℝ} (hs : s = 1 ∨ s = -1) (t : unitInterval) :
    (halfParam hs t : Circle) = halfC s t := rfl

/-! ### The half of a circle of pseudo-arcs -/

/-- A continuous open map onto the circle with pseudo-arc fibres, of a circle-like space. -/
structure IsCircPAMap {X : Type*} [MetricSpace X] (f : X → Circle) : Prop where
  cont : Continuous f
  isOpenMap : IsOpenMap f
  surj : Function.Surjective f
  fib : ∀ z, IsPseudoArc (f ⁻¹' {z})
  circ : IsCircleLike (univ : Set X)

theorem isCircleOfPA_iff {X : Type*} [MetricSpace X] :
    IsCircleOfPA X ↔ ∃ f : X → Circle, IsCircPAMap f := by
  constructor
  · rintro ⟨hc, f, h1, h2, h3, h4⟩; exact ⟨f, h1, h2, h3, h4, hc⟩
  · rintro ⟨f, h1, h2, h3, h4, hc⟩; exact ⟨hc, f, h1, h2, h3, h4⟩

theorem IsCircPAMap.compactSpace {X : Type*} [MetricSpace X] {f : X → Circle}
    (hf : IsCircPAMap f) : CompactSpace X := isCompact_univ_iff.1 hf.circ.1.1

variable {X : Type*} [MetricSpace X]

/-- The half `f⁻¹(A_s)`. -/
def halfSet (f : X → Circle) (s : ℝ) : Set X := f ⁻¹' range (halfC s)

/-- The map of the half onto `[0, 1]`. -/
noncomputable def halfMap (f : X → Circle) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    halfSet f s → unitInterval := fun x => (halfParam hs).symm ⟨f x, x.2⟩

omit [MetricSpace X] in
theorem halfMap_eq_iff (f : X → Circle) {s : ℝ} (hs : s = 1 ∨ s = -1) (x : halfSet f s)
    (t : unitInterval) : halfMap f hs x = t ↔ f x = halfC s t := by
  unfold halfMap
  rw [Homeomorph.symm_apply_eq, Subtype.ext_iff, halfParam_apply]

theorem continuous_halfMap {f : X → Circle} (hf : Continuous f) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    Continuous (halfMap f hs) :=
  (halfParam hs).symm.continuous.comp ((hf.comp continuous_subtype_val).subtype_mk _)

theorem isOpenMap_halfMap {f : X → Circle} (hf : IsOpenMap f) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    IsOpenMap (halfMap f hs) := by
  intro V hV
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hV
  have himg : (fun x : halfSet f s => (⟨f x, x.2⟩ : range (halfC s))) '' (Subtype.val ⁻¹' W) =
      Subtype.val ⁻¹' (f '' W) := by
    ext ⟨z, hz⟩
    simp only [mem_image, mem_preimage, Subtype.mk.injEq]
    constructor
    · rintro ⟨⟨x, hx⟩, hxW, rfl⟩; exact ⟨x, hxW, rfl⟩
    · rintro ⟨x, hxW, rfl⟩; exact ⟨⟨x, hz⟩, hxW, rfl⟩
  have : halfMap f hs '' (Subtype.val ⁻¹' W) =
      (halfParam hs).symm '' (Subtype.val ⁻¹' (f '' W)) := by
    rw [← himg, image_image]; rfl
  rw [this]
  exact (halfParam hs).symm.isOpenMap _ (isOpen_induced (hf W hW))

omit [MetricSpace X] in
theorem surjective_halfMap {f : X → Circle} (hf : Function.Surjective f) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : Function.Surjective (halfMap f hs) := by
  intro t
  obtain ⟨x, hx⟩ := hf (halfC s t)
  exact ⟨⟨x, t, hx.symm⟩, (halfMap_eq_iff f hs _ t).2 hx⟩

theorem isClosed_halfSet {f : X → Circle} (hf : Continuous f) (s : ℝ) :
    IsClosed (halfSet f s) :=
  ((isCompact_range (continuous_halfC s)).isClosed).preimage hf

omit [MetricSpace X] in
/-- The fibre of the half over `t`, as the fibre of `f` over `halfC s t`. -/
theorem image_val_halfMap_fibre (f : X → Circle) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (t : unitInterval) :
    Subtype.val '' (halfMap f hs ⁻¹' {t}) = f ⁻¹' {halfC s t} := by
  ext x
  simp only [mem_image, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact (halfMap_eq_iff f hs y t).1 hy
  · intro hx
    exact ⟨⟨x, t, hx.symm⟩, (halfMap_eq_iff f hs _ t).2 hx, rfl⟩

/-- The fibre of the half over `t` is homeomorphic to the fibre of `f` over `z = halfC s t`. -/
noncomputable def halfFibreEquiv (f : X → Circle) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (t : unitInterval) (z : Circle) (hz : halfC s t = z) :
    (halfMap f hs ⁻¹' {t} : Set (halfSet f s)) ≃ₜ (f ⁻¹' {z} : Set X) :=
  (IsEmbedding.subtypeVal.homeomorphImage _).trans
    (Homeomorph.setCongr (by rw [image_val_halfMap_fibre, hz]))

@[simp] theorem halfFibreEquiv_apply (f : X → Circle) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (t : unitInterval) (z : Circle) (hz : halfC s t = z) (p) :
    (halfFibreEquiv f hs t z hz p : X) = p.1.1 := rfl

@[simp] theorem halfFibreEquiv_symm_apply (f : X → Circle) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (t : unitInterval) (z : Circle) (hz : halfC s t = z) (q) :
    ((halfFibreEquiv f hs t z hz).symm q : halfSet f s).1 = q.1 := by
  have := halfFibreEquiv_apply f hs t z hz ((halfFibreEquiv f hs t z hz).symm q)
  rw [Homeomorph.apply_symm_apply] at this
  exact this.symm

variable [CompactSpace X]

theorem isContArcPA_halfMap {f : X → Circle} (hf : IsCircPAMap f) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : IsContArcPA (halfMap f hs) := by
  haveI : CompactSpace (halfSet f s) := isCompact_iff_compactSpace.1
    (isClosed_halfSet hf.cont s).isCompact
  refine ⟨continuous_halfMap hf.cont hs, isOpenMap_halfMap hf.isOpenMap hs,
    surjective_halfMap hf.surj hs, fun t => ?_⟩
  apply isPseudoArc_subtype_of_image
  rw [image_val_halfMap_fibre]
  exact hf.fib _

theorem isSnakeLike_halfSet {f : X → Circle} (hf : IsCircPAMap f) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : IsSnakeLike (univ : Set (halfSet f s)) := by
  apply isSnakeLike_univ_of_isSnakeLike
  have hc : Fold.Q78.IsContinuum (halfSet f s) := by
    refine ⟨(isClosed_halfSet hf.cont s).isCompact, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hf.surj (halfC s 0); exact ⟨x, 0, hx.symm⟩
    · exact isPreconnected_preimage_of_monotone' hf.cont
        (fun z => (hf.fib z).1.1.2.isPreconnected)
        (isPreconnected_range (continuous_halfC s)) (fun z _ => hf.surj z)
  obtain ⟨z, hz⟩ := exists_not_mem_range_halfC hs
  obtain ⟨x, hx⟩ := hf.surj z
  refine isSnakeLike_of_subset_circleLike hf.circ hc (subset_univ _) fun h => ?_
  have : x ∈ halfSet f s := h ▸ mem_univ x
  exact hz (hx ▸ this)

end HPC.BJ59
