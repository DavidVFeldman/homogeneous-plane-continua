import HPC.Hagopian.Hagopian76W

/-!
# Batch 179, §0.1 and §2d.4: the members of `I` are nondegenerate; finitely many crossing components

* `crossingIntervals_nondegenerate_of`: if no crossing component lies in a layer `d⁻¹(v)` (Property 3
  as printed, `hagopian76_property3_components`), every member `[x, y]` of `I` has `x < y`
  (commission 179 §0.1).
* `crossingComponents_finite_of`: with `I` finite and nondegenerate, there are finitely many crossing
  components; a member of `I` determines its component (commission 179 §2d.4).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Nondeg

variable {M : Set Pt}

theorem layerSet_Icc_self {G : Set M} (d : G → unitInterval) (u : unitInterval) :
    layerSet d (Icc u u) = layer d u := by
  rw [Icc_self]; rfl

/-- **§0.1: nondegeneracy of `I` from Property 3.** If no crossing component of `G ∩ π⁻¹[D]` lies
in a layer `d⁻¹(v)`, every member `[x, y]` of `I` has `x < y`. -/
theorem crossingIntervals_nondegenerate_of {G : Set M} {d : G → unitInterval} {π : Pt → Pt}
    {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)}
    (hP3 : ∀ C : Set M, IsCrossingComponent G π F c₁ D' C → ∀ v : unitInterval,
      ¬ C ⊆ layer d v) :
    ∀ p ∈ crossingIntervals d π F c₁ D', p.1 < p.2 := by
  rintro ⟨x, y⟩ ⟨C, hC, hI⟩
  by_contra hxy
  push_neg at hxy
  obtain ⟨w, hw⟩ := hC.isConnected.nonempty
  obtain ⟨g, hg, -⟩ := hI.1 hw
  have hxy' : x = y := le_antisymm (hg.1.trans hg.2) hxy
  simp only at hxy'
  subst hxy'
  exact hP3 C hC x (by rw [← layerSet_Icc_self]; exact hI.1)

variable [CompactSpace M]

/-- Two crossing components with the same nondegenerate irreducible interval coincide (the
argument of `crossingIntervals_disjoint`). -/
theorem IsCrossingComponent.eq_of_irreducible {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)}
    {C₁ C₂ : Set M} (hC₁ : IsCrossingComponent G π F c₁ D' C₁)
    (hC₂ : IsCrossingComponent G π F c₁ D' C₂) {x y : unitInterval} (hxy : x < y)
    (hI₁ : IsIrreducibleInterval d C₁ x y) (hI₂ : IsIrreducibleInterval d C₂ x y) : C₁ = C₂ := by
  have hC₁G : C₁ ⊆ G := fun m hm => (hC₁.subset hm).1
  have hC₂G : C₂ ⊆ G := fun m hm => (hC₂.subset hm).1
  have hJo : IsOpen (d ⁻¹' Ioo x y) := isOpen_Ioo.preimage hG.2.1.1
  obtain ⟨V, hVo, hVJ⟩ := isOpen_induced_iff.1 hJo
  obtain ⟨t, ht⟩ := exists_between hxy
  obtain ⟨w, hw⟩ := hG.2.1.2.1 t
  have hwJ : d w ∈ Ioo x y := by rw [hw]; exact ht
  have hsub₁ := hI₁.layerSet_Ioo_subset_closure hG hC₁G hC₁.isConnected
  have hsub₂ := hI₂.layerSet_Ioo_subset_closure hG hC₂G hC₂.isConnected
  have hw₁ : (w : M) ∈ closure C₁ := hsub₁ ⟨w, hwJ, rfl⟩
  have hwV : (w : M) ∈ V := by
    have : w ∈ Subtype.val ⁻¹' V := by rw [hVJ]; exact hwJ
    exact this
  obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.1 hw₁ V hVo hwV
  have hzJ : (⟨z, hC₁G hzC⟩ : G) ∈ d ⁻¹' Ioo x y := by rw [← hVJ]; exact hzV
  have hz₂ : z ∈ closure C₂ := hsub₂ ⟨⟨z, hC₁G hzC⟩, hzJ, rfl⟩
  exact hC₁.eq_of_mem_closure hC₂ hzC hz₂

/-- **§2d.4: finitely many crossing components.** If `I` is finite and its members are
nondegenerate, the crossing components of `G ∩ π⁻¹[D]` form a finite set: each has an irreducible
interval (`exists_irreducibleInterval`), which lies in `I`, and determines it
(`IsCrossingComponent.eq_of_irreducible`). -/
theorem crossingComponents_finite_of {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)}
    (hfin : (crossingIntervals d π F c₁ D').Finite)
    (hnd : ∀ p ∈ crossingIntervals d π F c₁ D', p.1 < p.2) :
    {C : Set M | IsCrossingComponent G π F c₁ D' C}.Finite := by
  have hex : ∀ C ∈ {C : Set M | IsCrossingComponent G π F c₁ D' C},
      ∃ p : unitInterval × unitInterval, IsIrreducibleInterval d C p.1 p.2 := by
    intro C hC
    obtain ⟨x, y, h, -⟩ := exists_irreducibleInterval hG (fun m hm => (hC.subset hm).1)
      hC.isConnected.nonempty
    exact ⟨(x, y), h⟩
  choose! f hf using hex
  refine Set.Finite.of_finite_image (f := f) (hfin.subset ?_) ?_
  · rintro _ ⟨C, hC, rfl⟩
    exact ⟨C, hC, hf C hC⟩
  · intro C₁ hC₁ C₂ hC₂ heq
    have h2 : IsIrreducibleInterval d C₂ (f C₁).1 (f C₁).2 := by rw [heq]; exact hf C₂ hC₂
    exact IsCrossingComponent.eq_of_irreducible hG hC₁ hC₂ (hnd _ ⟨C₁, hC₁, hf C₁ hC₁⟩)
      (hf C₁ hC₁) h2

end Nondeg

end HPC.Hagopian
