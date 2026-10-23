import HPC.BJ59.Halves

/-!
# Batch 198, library: gluing (commission 198, §4, steps 2–3)

From `BJThm10`: two circles of pseudo-arcs `(X, f)`, `(Y, g)` and homeomorphisms of the fibres
over `1` and over `−1 = exp π` give a homeomorphism `Φ : X ≃ₜ Y` with `g ∘ Φ = f` extending the one
over `1` (`exists_homeomorph_glue`). Each half is a continuous snake-like arc of pseudo-arcs
(`HPC/BJ59/Halves.lean`); `BJThm10` gives homeomorphisms of the upper halves and of the lower
halves extending the same end maps, and they glue along the closed cover by the two halves.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane HPC.Jones

variable {X Y : Type} [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]

/-- **One half.** `BJThm10` applied to the halves over `A_s`, with end maps induced by `kP` (over
`1`) and `kM` (over `exp π`). -/
theorem exists_half_homeomorph (h10 : BJThm10) {f : X → Circle} {g : Y → Circle}
    (hf : IsCircPAMap f) (hg : IsCircPAMap g) {s : ℝ} (hs : s = 1 ∨ s = -1)
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
    (isContArcPA_halfMap hf hs) (isContArcPA_halfMap hg hs) (isSnakeLike_halfSet hf hs)
    (isSnakeLike_halfSet hg hs) h₀ h₁
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

/-- **Gluing.** Homeomorphisms of the fibres over `1` and over `exp π` extend to a homeomorphism of
circles of pseudo-arcs covering the identity of the circle. -/
theorem exists_homeomorph_glue (h10 : BJThm10) {f : X → Circle} {g : Y → Circle}
    (hf : IsCircPAMap f) (hg : IsCircPAMap g)
    (kP : (f ⁻¹' {1} : Set X) ≃ₜ (g ⁻¹' {1} : Set Y))
    (kM : (f ⁻¹' {Circle.exp Real.pi} : Set X) ≃ₜ (g ⁻¹' {Circle.exp Real.pi} : Set Y)) :
    ∃ Φ : X ≃ₜ Y, (∀ x, g (Φ x) = f x) ∧ ∀ x (hx : f x = 1), Φ x = kP ⟨x, hx⟩ := by
  classical
  obtain ⟨Hu, hHu, hHu0, hHu1⟩ := exists_half_homeomorph h10 hf hg (Or.inl rfl) kP kM
  obtain ⟨Hl, hHl, hHl0, hHl1⟩ := exists_half_homeomorph h10 hf hg (Or.inr rfl) kP kM
  have hcov : ∀ z : Circle, z ∈ range (halfC 1) ∨ z ∈ range (halfC (-1)) := fun z => by
    have := range_halfC_union ▸ mem_univ z; exact this
  have hlow : ∀ x, f x ∉ range (halfC 1) → x ∈ halfSet f (-1) := fun x hx =>
    (hcov (f x)).resolve_left hx
  -- the two homeomorphisms agree on the overlap
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

end HPC.BJ59
