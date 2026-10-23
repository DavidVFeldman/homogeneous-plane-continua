import HPC.BJ59.Glue

/-!
# Batch 198, library: homogeneity and uniqueness of circles of pseudo-arcs, from `BJThm10`

* `homeomorph_of_isCircPAMap`: any two circles of pseudo-arcs are homeomorphic (glue with any
  homeomorphisms of the fibres over `1` and `exp π`, `theorem1_HIC'`);
* `isHomogeneous_of_isCircPAMap`: given `x`, `y`, rotate `f` so that `x` and `y` lie over `1`, take
  a homeomorphism of the two fibres over `1` carrying `x` to `y` (`theorem1_HIC'` and
  `homogeneous_of_isPseudoArc`) and glue (commission 198, §4, step 3).
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane HPC.Jones

/-- The circle is homogeneous: left multiplication. -/
theorem isHomogeneous_circle' : IsHomogeneous Circle := fun x y =>
  ⟨Homeomorph.mulLeft (y * x⁻¹), by simp⟩

/-- Rotating a circle of pseudo-arcs map. -/
theorem IsCircPAMap.mul_left {X : Type*} [MetricSpace X] {f : X → Circle} (hf : IsCircPAMap f)
    (c : Circle) : IsCircPAMap (fun x => c * f x) := by
  refine ⟨continuous_const.mul hf.cont, (Homeomorph.mulLeft c).isOpenMap.comp hf.isOpenMap,
    fun z => ?_, fun z => ?_, hf.circ⟩
  · obtain ⟨x, hx⟩ := hf.surj (c⁻¹ * z); exact ⟨x, by simp [hx]⟩
  · have : (fun x => c * f x) ⁻¹' {z} = f ⁻¹' {c⁻¹ * z} := by
      ext x; simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; simp
    rw [this]; exact hf.fib _

variable {X Y : Type} [MetricSpace X] [MetricSpace Y]

/-- **Any two circles of pseudo-arcs are homeomorphic**, from `BJThm10`. -/
theorem homeomorph_of_isCircPAMap (h10 : BJThm10) {f : X → Circle} {g : Y → Circle}
    (hf : IsCircPAMap f) (hg : IsCircPAMap g) : Nonempty (X ≃ₜ Y) := by
  haveI := hf.compactSpace
  haveI := hg.compactSpace
  obtain ⟨kP⟩ := theorem1_HIC' (hf.fib 1) (hg.fib 1)
  obtain ⟨kM⟩ := theorem1_HIC' (hf.fib (Circle.exp Real.pi)) (hg.fib (Circle.exp Real.pi))
  obtain ⟨Φ, -, -⟩ := exists_homeomorph_glue h10 hf hg kP kM
  exact ⟨Φ⟩

/-- **Each circle of pseudo-arcs is homogeneous**, from `BJThm10`. -/
theorem isHomogeneous_of_isCircPAMap (h10 : BJThm10) {f : X → Circle} (hf : IsCircPAMap f) :
    IsHomogeneous X := by
  haveI := hf.compactSpace
  intro x y
  set f₁ : X → Circle := fun p => (f x)⁻¹ * f p
  set f₂ : X → Circle := fun p => (f y)⁻¹ * f p
  have hf₁ : IsCircPAMap f₁ := hf.mul_left _
  have hf₂ : IsCircPAMap f₂ := hf.mul_left _
  have hx : x ∈ f₁ ⁻¹' {1} := by simp [f₁]
  have hy : y ∈ f₂ ⁻¹' {1} := by simp [f₂]
  obtain ⟨T⟩ := theorem1_HIC' (hf₁.fib 1) (hf₂.fib 1)
  obtain ⟨S, hS⟩ := homogeneous_of_isPseudoArc (hf₂.fib 1) _ y (T ⟨x, hx⟩).2 hy
  obtain ⟨kM⟩ := theorem1_HIC' (hf₁.fib (Circle.exp Real.pi)) (hf₂.fib (Circle.exp Real.pi))
  obtain ⟨Φ, -, hΦ⟩ := exists_homeomorph_glue h10 hf₁ hf₂ (T.trans S) kM
  refine ⟨Φ, ?_⟩
  rw [hΦ x hx]
  have : (T.trans S) ⟨x, hx⟩ = ⟨y, hy⟩ := by
    rw [Homeomorph.trans_apply]; exact hS
  rw [this]

end HPC.BJ59
