import HPC.BJ59.Atomic
import HPC.BJ59.CircleLike

/-!
# Batch 199: atomic circle maps — halves, gluing, uniqueness, homogeneity (commission 199, §4)

Batch 198's `exists_half_homeomorph`, `exists_homeomorph_glue`, `homeomorph_of_isCircPAMap` and
`isHomogeneous_of_isCircPAMap` use circle-likeness only to make the halves snake-like and for
compactness. Here they are generalized to `IsSnakeHalvesMap` (an open continuous map onto the
circle with pseudo-arc fibres whose two halves are snake-like) on a compact space, and instantiated
by `isSnakeLike_halfSet` for `IsCircPAMap` and by §3 for `IsAtomicCircPAMap`. `Halves.lean`,
`Glue.lean` and `Homog.lean` are not edited.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane HPC.Jones

/-- The half map of an atomic map is atomic. -/
theorem isAtomicMap_halfMap {X : Type*} [MetricSpace X] {f : X → Circle} (hf : IsAtomicMap f)
    {s : ℝ} (hs : s = 1 ∨ s = -1) : IsAtomicMap (halfMap f hs) := by
  intro t L hL ⟨x, hxL, hx⟩
  have hL' : Fold.Q78.IsContinuum (Subtype.val '' L : Set X) :=
    ⟨hL.1.image continuous_subtype_val, hL.2.image _ continuous_subtype_val.continuousOn⟩
  have hxf : f x = halfC s t := (halfMap_eq_iff f hs x t).1 hx
  rcases hf (halfC s t) _ hL' ⟨x, ⟨x, hxL, rfl⟩, hxf⟩ with h | h
  · left
    intro y hy
    exact (halfMap_eq_iff f hs y t).2 (h ⟨y, hy, rfl⟩)
  · right
    intro y hy
    obtain ⟨z, hz, hzy⟩ := h ((halfMap_eq_iff f hs y t).1 hy)
    rwa [← Subtype.ext hzy]

section CircleMaps

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The half of an open continuous map onto the circle with pseudo-arc fibres is a continuous arc
of pseudo-arcs (the proof of `isContArcPA_halfMap`, without circle-likeness). -/
theorem isContArcPA_halfMap' {f : X → Circle} (hc : Continuous f) (ho : IsOpenMap f)
    (hs' : Function.Surjective f) (hfib : ∀ z, IsPseudoArc (f ⁻¹' {z})) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : IsContArcPA (halfMap f hs) := by
  haveI : CompactSpace (halfSet f s) := isCompact_iff_compactSpace.1
    (isClosed_halfSet hc s).isCompact
  refine ⟨continuous_halfMap hc hs, isOpenMap_halfMap ho hs, surjective_halfMap hs' hs,
    fun t => ?_⟩
  apply isPseudoArc_subtype_of_image
  rw [image_val_halfMap_fibre]
  exact hfib _

theorem isContArcPA_halfMap_of_atomic {f : X → Circle} (hf : IsAtomicCircPAMap f) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : IsContArcPA (halfMap f hs) :=
  isContArcPA_halfMap' hf.cont hf.isOpenMap hf.surj hf.fib hs

/-- **The halves are snake-like**, without circle-likeness (compare `isSnakeLike_halfSet`). -/
theorem isSnakeLike_halfSet_of_atomic {f : X → Circle} (hf : IsAtomicCircPAMap f) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : IsSnakeLike (univ : Set (halfSet f s)) := by
  haveI : CompactSpace (halfSet f s) := isCompact_iff_compactSpace.1
    (isClosed_halfSet hf.cont s).isCompact
  have h := isContArcPA_halfMap_of_atomic hf hs
  exact isSnakeLike_of_atomic h.1 h.2.2.2 (isAtomicMap_halfMap hf.atomic hs)

end CircleMaps

/-! ### Maps with snake-like halves -/

/-- An open continuous map onto the circle with pseudo-arc fibres whose two halves are snake-like
(the hypotheses batch 198's gluing actually uses). -/
structure IsSnakeHalvesMap {X : Type*} [MetricSpace X] (f : X → Circle) : Prop where
  cont : Continuous f
  isOpenMap : IsOpenMap f
  surj : Function.Surjective f
  fib : ∀ z, IsPseudoArc (f ⁻¹' {z})
  halves : ∀ {s : ℝ} (hs : s = 1 ∨ s = -1), IsSnakeLike (univ : Set (halfSet f s))

theorem IsCircPAMap.isSnakeHalvesMap {X : Type*} [MetricSpace X] {f : X → Circle}
    (hf : IsCircPAMap f) : IsSnakeHalvesMap f := by
  haveI := hf.compactSpace
  exact ⟨hf.cont, hf.isOpenMap, hf.surj, hf.fib, fun hs => isSnakeLike_halfSet hf hs⟩

theorem IsAtomicCircPAMap.isSnakeHalvesMap {X : Type*} [MetricSpace X] [CompactSpace X]
    {f : X → Circle} (hf : IsAtomicCircPAMap f) : IsSnakeHalvesMap f :=
  ⟨hf.cont, hf.isOpenMap, hf.surj, hf.fib, fun hs => isSnakeLike_halfSet_of_atomic hf hs⟩

/-- Rotating an atomic map keeps it atomic (the fibres are the same sets). -/
theorem IsAtomicCircPAMap.mul_left {X : Type*} [MetricSpace X] {f : X → Circle}
    (hf : IsAtomicCircPAMap f) (c : Circle) : IsAtomicCircPAMap (fun x => c * f x) := by
  have hpre : ∀ z, (fun x => c * f x) ⁻¹' {z} = f ⁻¹' {c⁻¹ * z} := fun z => by
    ext x; simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  refine ⟨continuous_const.mul hf.cont, (Homeomorph.mulLeft c).isOpenMap.comp hf.isOpenMap,
    fun z => ?_, fun z => ?_, fun z L hL hm => ?_⟩
  · obtain ⟨x, hx⟩ := hf.surj (c⁻¹ * z); exact ⟨x, by simp [hx]⟩
  · rw [hpre]; exact hf.fib _
  · rw [hpre] at hm ⊢; exact hf.atomic _ L hL hm

section Glue

variable {X Y : Type} [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]

/-- **One half** (batch 198's `exists_half_homeomorph` for maps with snake-like halves). -/
theorem exists_half_homeomorph' (h10 : BJThm10) {f : X → Circle} {g : Y → Circle}
    (hf : IsSnakeHalvesMap f) (hg : IsSnakeHalvesMap g) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (kP : (f ⁻¹' {1} : Set X) ≃ₜ (g ⁻¹' {1} : Set Y))
    (kM : (f ⁻¹' {Circle.exp Real.pi} : Set X) ≃ₜ (g ⁻¹' {Circle.exp Real.pi} : Set Y)) :
    ∃ H : halfSet f s ≃ₜ halfSet g s, (∀ x, g (H x) = f x) ∧
      (∀ (x : halfSet f s) (hx : f x.1 = 1), (H x : Y) = kP ⟨x.1, hx⟩) ∧
      (∀ (x : halfSet f s) (hx : f x.1 = Circle.exp Real.pi), (H x : Y) = kM ⟨x.1, hx⟩) := by
  haveI : CompactSpace (halfSet f s) := isCompact_iff_compactSpace.1
    (isClosed_halfSet hf.cont s).isCompact
  haveI : CompactSpace (halfSet g s) := isCompact_iff_compactSpace.1
    (isClosed_halfSet hg.cont s).isCompact
  have e0 : halfC s 0 = 1 := halfC_zero s
  have e1 : halfC s 1 = Circle.exp Real.pi := halfC_one_eq hs
  let h₀ := (halfFibreEquiv f hs 0 1 e0).trans (kP.trans (halfFibreEquiv g hs 0 1 e0).symm)
  let h₁ := (halfFibreEquiv f hs 1 _ e1).trans (kM.trans (halfFibreEquiv g hs 1 _ e1).symm)
  obtain ⟨H, hH, hH0, hH1⟩ := h10 (halfSet f s) (halfSet g s) (halfMap f hs) (halfMap g hs)
    (isContArcPA_halfMap' hf.cont hf.isOpenMap hf.surj hf.fib hs)
    (isContArcPA_halfMap' hg.cont hg.isOpenMap hg.surj hg.fib hs) (hf.halves hs)
    (hg.halves hs) h₀ h₁
  refine ⟨H, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := (halfMap_eq_iff g hs (H x) _).1 (hH x)
    have h2 := (halfMap_eq_iff f hs x _).1 rfl
    rw [h1, ← h2]
  · have hx0 : x ∈ halfMap f hs ⁻¹' {0} := (halfMap_eq_iff f hs x 0).2 (hx.trans e0.symm)
    rw [hH0 x hx0]
    exact halfFibreEquiv_symm_apply g hs 0 1 e0 _
  · have hx1 : x ∈ halfMap f hs ⁻¹' {1} := (halfMap_eq_iff f hs x 1).2 (hx.trans e1.symm)
    rw [hH1 x hx1]
    exact halfFibreEquiv_symm_apply g hs 1 _ e1 _

/-- **Gluing** (batch 198's `exists_homeomorph_glue` for maps with snake-like halves). -/
theorem exists_homeomorph_glue' (h10 : BJThm10) {f : X → Circle} {g : Y → Circle}
    (hf : IsSnakeHalvesMap f) (hg : IsSnakeHalvesMap g)
    (kP : (f ⁻¹' {1} : Set X) ≃ₜ (g ⁻¹' {1} : Set Y))
    (kM : (f ⁻¹' {Circle.exp Real.pi} : Set X) ≃ₜ (g ⁻¹' {Circle.exp Real.pi} : Set Y)) :
    ∃ Φ : X ≃ₜ Y, (∀ x, g (Φ x) = f x) ∧ ∀ x (hx : f x = 1), Φ x = kP ⟨x, hx⟩ := by
  classical
  obtain ⟨Hu, hHu, hHu0, hHu1⟩ := exists_half_homeomorph' h10 hf hg (Or.inl rfl) kP kM
  obtain ⟨Hl, hHl, hHl0, hHl1⟩ := exists_half_homeomorph' h10 hf hg (Or.inr rfl) kP kM
  have hcov : ∀ z : Circle, z ∈ range (halfC 1) ∨ z ∈ range (halfC (-1)) := fun z => by
    have := range_halfC_union ▸ mem_univ z; exact this
  have hlow : ∀ x, f x ∉ range (halfC 1) → x ∈ halfSet f (-1) := fun x hx =>
    (hcov (f x)).resolve_left hx
  have hagree : ∀ x (hu : x ∈ halfSet f 1) (hl : x ∈ halfSet f (-1)),
      (Hu ⟨x, hu⟩ : Y) = Hl ⟨x, hl⟩ := by
    intro x hu hl
    rcases mem_range_halfC_inter hu hl with h | h
    · rw [hHu0 ⟨x, hu⟩ h, hHl0 ⟨x, hl⟩ h]
    · rw [hHu1 ⟨x, hu⟩ h, hHl1 ⟨x, hl⟩ h]
  let Φ : X → Y := fun x => if h : f x ∈ range (halfC 1) then (Hu ⟨x, h⟩ : Y)
    else (Hl ⟨x, hlow x h⟩ : Y)
  have hΦu : ∀ x (h : x ∈ halfSet f 1), Φ x = Hu ⟨x, h⟩ := fun x h => dif_pos h
  have hΦl : ∀ x (h : x ∈ halfSet f (-1)), Φ x = Hl ⟨x, h⟩ := fun x h => by
    by_cases hu : f x ∈ range (halfC 1)
    · rw [hΦu x hu]; exact hagree x hu h
    · exact dif_neg hu
  have hgΦ : ∀ x, g (Φ x) = f x := fun x => by
    by_cases hu : x ∈ halfSet f 1
    · rw [hΦu x hu]; exact hHu ⟨x, hu⟩
    · rw [hΦl x (hlow x hu)]; exact hHl ⟨x, _⟩
  have hcont : Continuous Φ := by
    rw [← continuousOn_univ]
    have hU : (univ : Set X) = halfSet f 1 ∪ halfSet f (-1) := by
      ext x; simp only [mem_univ, mem_union, true_iff]; exact hcov (f x)
    rw [hU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_halfSet hf.cont 1)
      (isClosed_halfSet hf.cont (-1))
    · rw [continuousOn_iff_continuous_restrict]
      have : (halfSet f 1).restrict Φ = fun x => (Hu x : Y) := funext fun x => hΦu x x.2
      rw [this]; exact continuous_subtype_val.comp Hu.continuous
    · rw [continuousOn_iff_continuous_restrict]
      have : (halfSet f (-1)).restrict Φ = fun x => (Hl x : Y) := funext fun x => hΦl x x.2
      rw [this]; exact continuous_subtype_val.comp Hl.continuous
  have hinj : Function.Injective Φ := by
    intro x x' h
    have hf' : f x = f x' := by rw [← hgΦ x, ← hgΦ x', h]
    by_cases hu : x ∈ halfSet f 1
    · have hu' : x' ∈ halfSet f 1 := by
        show f x' ∈ range (halfC 1); rw [← hf']; exact hu
      rw [hΦu x hu, hΦu x' hu'] at h
      exact congrArg Subtype.val (Hu.injective (Subtype.ext h))
    · have hl := hlow x hu
      have hl' : x' ∈ halfSet f (-1) := by
        show f x' ∈ range (halfC (-1)); rw [← hf']; exact hl
      rw [hΦl x hl, hΦl x' hl'] at h
      exact congrArg Subtype.val (Hl.injective (Subtype.ext h))
  have hsurj : Function.Surjective Φ := by
    intro y
    rcases hcov (g y) with h | h
    · refine ⟨(Hu.symm ⟨y, h⟩ : X), ?_⟩
      rw [hΦu _ (Hu.symm ⟨y, h⟩).2]; simp
    · refine ⟨(Hl.symm ⟨y, h⟩ : X), ?_⟩
      rw [hΦl _ (Hl.symm ⟨y, h⟩).2]; simp
  refine ⟨hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective Φ ⟨hinj, hsurj⟩), hgΦ,
    fun x hx => ?_⟩
  show Φ x = _
  have hu : x ∈ halfSet f 1 := ⟨0, (halfC_zero 1).trans hx.symm⟩
  rw [hΦu x hu]
  exact hHu0 ⟨x, hu⟩ hx

/-- Any two compact spaces with maps with snake-like halves are homeomorphic (given Theorem 10). -/
theorem homeomorph_of_isSnakeHalvesMap (h10 : BJThm10) {f : X → Circle} {g : Y → Circle}
    (hf : IsSnakeHalvesMap f) (hg : IsSnakeHalvesMap g) : Nonempty (X ≃ₜ Y) := by
  obtain ⟨kP⟩ := theorem1_HIC' (hf.fib 1) (hg.fib 1)
  obtain ⟨kM⟩ := theorem1_HIC' (hf.fib (Circle.exp Real.pi)) (hg.fib (Circle.exp Real.pi))
  obtain ⟨Φ, -, -⟩ := exists_homeomorph_glue' h10 hf hg kP kM
  exact ⟨Φ⟩

end Glue

/-- **Domokos–Prajs, Theorem 6.1, "if"** (p. 14), given Bing–Jones Theorem 10: a compact space with
an open atomic map onto the circle with pseudo-arc fibres is homeomorphic to every circle of
pseudo-arcs. -/
theorem dp22_theorem61 (h10 : BJThm10) {X Y : Type} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] {f : X → Circle} (hf : IsAtomicCircPAMap f) (hY : IsCircleOfPA Y) :
    Nonempty (X ≃ₜ Y) := by
  obtain ⟨g, hg⟩ := isCircleOfPA_iff.1 hY
  haveI := hg.compactSpace
  exact homeomorph_of_isSnakeHalvesMap h10 hf.isSnakeHalvesMap hg.isSnakeHalvesMap

/-- Two compact spaces with open atomic maps onto the circle with pseudo-arc fibres are
homeomorphic (given Theorem 10). -/
theorem homeomorph_of_atomic (h10 : BJThm10) {X Y : Type} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y] {f : X → Circle} {g : Y → Circle}
    (hf : IsAtomicCircPAMap f) (hg : IsAtomicCircPAMap g) : Nonempty (X ≃ₜ Y) :=
  homeomorph_of_isSnakeHalvesMap h10 hf.isSnakeHalvesMap hg.isSnakeHalvesMap

/-- **Homogeneity** (given Theorem 10), by rotating the map, as in
`isHomogeneous_of_isCircPAMap`. -/
theorem isHomogeneous_of_atomic (h10 : BJThm10) {X : Type} [MetricSpace X] [CompactSpace X]
    {f : X → Circle} (hf : IsAtomicCircPAMap f) : IsHomogeneous X := by
  intro x y
  set f₁ : X → Circle := fun p => (f x)⁻¹ * f p
  set f₂ : X → Circle := fun p => (f y)⁻¹ * f p
  have hf₁ : IsAtomicCircPAMap f₁ := hf.mul_left _
  have hf₂ : IsAtomicCircPAMap f₂ := hf.mul_left _
  have hx : x ∈ f₁ ⁻¹' {1} := by simp [f₁]
  have hy : y ∈ f₂ ⁻¹' {1} := by simp [f₂]
  obtain ⟨T⟩ := theorem1_HIC' (hf₁.fib 1) (hf₂.fib 1)
  obtain ⟨S, hS⟩ := homogeneous_of_isPseudoArc (hf₂.fib 1) _ y (T ⟨x, hx⟩).2 hy
  obtain ⟨kM⟩ := theorem1_HIC' (hf₁.fib (Circle.exp Real.pi)) (hf₂.fib (Circle.exp Real.pi))
  obtain ⟨Φ, -, hΦ⟩ := exists_homeomorph_glue' h10 hf₁.isSnakeHalvesMap hf₂.isSnakeHalvesMap
    (T.trans S) kM
  refine ⟨Φ, ?_⟩
  rw [hΦ x hx]
  have : (T.trans S) ⟨x, hx⟩ = ⟨y, hy⟩ := by
    rw [Homeomorph.trans_apply]; exact hS
  rw [this]

/-- A compact space with an open atomic map onto the circle with pseudo-arc fibres is a circle of
pseudo-arcs in Bing–Jones's sense, if there is one (given Theorem 10). -/
theorem isCircleOfPA_of_atomic (h10 : BJThm10) {X Y : Type} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] {f : X → Circle} (hf : IsAtomicCircPAMap f) (hY : IsCircleOfPA Y) :
    IsCircleOfPA X := by
  obtain ⟨e⟩ := dp22_theorem61 h10 hf hY
  exact ⟨isCircleLike_univ_of_homeomorph e hY.1, f, hf.cont, hf.isOpenMap, hf.surj, hf.fib⟩

end HPC.BJ59
