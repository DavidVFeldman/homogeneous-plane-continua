import HPC.Jones.Jones49Order

/-!
# Batch 149, item B: a topological simple closed curve is homeomorphic to `Circle`

Two arcs `f₁, f₂ : [0, 1] → X` with common ends and nothing else in common are glued into the loop
`g : ℝ → X`, `g t = f₁ (2t)` on `[0, 1/2]` and `g t = f₂ (2 − 2t)` on `[1/2, 1]`; `g 0 = g 1`, so
`g` descends to `AddCircle 1` (`AddCircle.liftIco`). The induced map onto `J = C₁ ∪ C₂` is a
continuous bijection from a compact space onto a Hausdorff space, hence a homeomorphism; and
`AddCircle 1 ≃ₜ Circle` (`AddCircle.homeomorphCircle`).
-/

namespace HPC.Jones

open Set Topology unitInterval

/-- **Gluing two arcs along their ends** gives a copy of `Circle`. -/
theorem glue_circle {X : Type*} [TopologicalSpace X] [T2Space X] {f₁ f₂ : I → X}
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) (hi₁ : Function.Injective f₁)
    (hi₂ : Function.Injective f₂) (h0 : f₁ 0 = f₂ 0) (h1 : f₁ 1 = f₂ 1)
    (hint : range f₁ ∩ range f₂ ⊆ {f₁ 0, f₁ 1}) :
    Nonempty ((range f₁ ∪ range f₂ : Set X) ≃ₜ Circle) := by
  classical
  set p : ℝ → I := projIcc 0 1 zero_le_one with hp
  set g : ℝ → X := fun t => if t ≤ 1 / 2 then f₁ (p (2 * t)) else f₂ (p (2 - 2 * t))
  have hg : Continuous g := by
    refine Continuous.if_le
      (hc₁.comp (continuous_projIcc.comp (continuous_const.mul continuous_id)))
      (hc₂.comp (continuous_projIcc.comp (continuous_const.sub
        (continuous_const.mul continuous_id)))) continuous_id continuous_const ?_
    intro t ht
    subst ht
    have e1 : p (2 * (1 / 2)) = 1 := by norm_num [p]
    have e2 : p (2 - 2 * (1 / 2)) = 1 := by norm_num [p]
    simp only [e1, e2, h1]
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hg01 : g 0 = g (0 + 1) := by
    simp only [g, zero_add]
    norm_num
    have e1 : p 0 = 0 := by simp [p]
    rw [e1, h0]
  set G : AddCircle (1 : ℝ) → X := AddCircle.liftIco 1 0 g
  have hG : Continuous G := AddCircle.liftIco_continuous hg01 hg.continuousOn
  have hrep : ∀ x : AddCircle (1:ℝ), ∃ t ∈ Ico (0:ℝ) (0+1), (t : AddCircle (1:ℝ)) = x := by
    intro x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    refine ⟨toIcoMod (zero_lt_one' ℝ) 0 t, toIcoMod_mem_Ico _ _ _, ?_⟩
    rw [QuotientAddGroup.eq_iff_sub_mem, toIcoMod]
    simp [AddSubgroup.mem_zmultiples_iff]
  have hGt : ∀ t ∈ Ico (0:ℝ) (0+1), G t = g t := fun t ht => AddCircle.liftIco_coe_apply ht
  set S : Set X := range f₁ ∪ range f₂
  have hgS : ∀ t, g t ∈ S := by
    intro t; simp only [g]; split_ifs
    · exact Or.inl (mem_range_self _)
    · exact Or.inr (mem_range_self _)
  have hGS : ∀ x, G x ∈ S := by
    intro x; obtain ⟨t, ht, rfl⟩ := hrep x; rw [hGt t ht]; exact hgS t
  set G' : AddCircle (1:ℝ) → S := fun x => ⟨G x, hGS x⟩
  have hp_val : ∀ t ∈ Icc (0:ℝ) 1, (p t : ℝ) = t := fun t ht => by simp [p, projIcc_of_mem _ ht]
  have hinj : Function.Injective G' := by
    intro x y hxy
    obtain ⟨s, hs, rfl⟩ := hrep x
    obtain ⟨t, ht, rfl⟩ := hrep y
    have e : g s = g t := by
      have := congrArg Subtype.val hxy
      simp only [G'] at this
      rwa [hGt s hs, hGt t ht] at this
    rw [zero_add] at hs ht
    congr 1
    have key : ∀ {s t : ℝ}, s ∈ Ico (0:ℝ) 1 → t ∈ Ico (0:ℝ) 1 → s ≤ 1/2 → ¬ t ≤ 1/2 →
        f₁ (p (2 * s)) ≠ f₂ (p (2 - 2 * t)) := by
      intro s t hs ht hs2 ht2 e
      have hm : f₂ (p (2 - 2 * t)) ∈ range f₁ ∩ range f₂ := ⟨⟨_, e⟩, mem_range_self _⟩
      have hpt : (p (2 - 2 * t) : ℝ) = 2 - 2 * t :=
        hp_val _ ⟨by linarith [ht.2], by linarith⟩
      rcases hint hm with h | h
      · rw [h0] at h
        have := congrArg Subtype.val (hi₂ h)
        simp only [hpt, Icc.coe_zero] at this; linarith [ht.2]
      · rw [h1] at h
        have := congrArg Subtype.val (hi₂ h)
        simp only [hpt, Icc.coe_one] at this; linarith
    simp only [g] at e
    split_ifs at e with h₁ h₂ h₂
    · have := congrArg Subtype.val (hi₁ e)
      rw [hp_val _ ⟨by linarith [hs.1], by linarith⟩, hp_val _ ⟨by linarith [ht.1], by linarith⟩]
        at this
      linarith
    · exact absurd e (key hs ht h₁ h₂)
    · exact absurd e.symm (key ht hs h₂ h₁)
    · have := congrArg Subtype.val (hi₂ e)
      rw [hp_val _ ⟨by linarith [hs.2], by linarith⟩, hp_val _ ⟨by linarith [ht.2], by linarith⟩]
        at this
      linarith
  have hsurj : Function.Surjective G' := by
    rintro ⟨z, hz | hz⟩
    · obtain ⟨u, rfl⟩ := hz
      by_cases hu : (u : ℝ) = 1
      · refine ⟨((1/2 : ℝ) : AddCircle (1:ℝ)), Subtype.ext ?_⟩
        simp only [G']
        rw [hGt _ ⟨by norm_num, by norm_num⟩]
        simp only [g]; norm_num
        congr 1; ext; simp [p, hu]
      · refine ⟨(((u : ℝ) / 2 : ℝ) : AddCircle (1:ℝ)), Subtype.ext ?_⟩
        simp only [G']
        have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 hu
        rw [hGt _ ⟨by linarith [u.2.1], by linarith⟩]
        simp only [g]
        rw [if_pos (by linarith [u.2.2])]
        congr 1; ext; rw [hp_val _ ⟨by linarith [u.2.1], by linarith⟩]; ring
    · obtain ⟨u, rfl⟩ := hz
      by_cases hu : (u : ℝ) = 0
      · refine ⟨((0 : ℝ) : AddCircle (1:ℝ)), Subtype.ext ?_⟩
        simp only [G']
        rw [hGt _ ⟨le_rfl, by norm_num⟩]
        have : u = 0 := Subtype.ext hu
        subst this
        simp only [g]; norm_num
        rw [← h0]; congr 1; ext; simp [p]
      · refine ⟨((1 - (u : ℝ) / 2 : ℝ) : AddCircle (1:ℝ)), Subtype.ext ?_⟩
        simp only [G']
        have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hu)
        rw [hGt _ ⟨by linarith [u.2.2], by linarith⟩]
        simp only [g]
        by_cases hu1 : (u : ℝ) = 1
        · rw [if_pos (by linarith)]
          have : u = 1 := Subtype.ext hu1
          subst this
          rw [← h1]; congr 1; ext; simp [hp]; norm_num
        · rw [if_neg (by linarith [lt_of_le_of_ne u.2.2 hu1])]
          congr 1; ext; rw [hp_val _ ⟨by linarith [u.2.1], by linarith [u.2.2]⟩]; ring
  have hcont : Continuous G' := hG.subtype_mk _
  exact ⟨(hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G' ⟨hinj, hsurj⟩)).symm.trans
    (AddCircle.homeomorphCircle one_ne_zero)⟩

/-- A topological simple closed curve (two arcs with only their ends in common, batch 138's
`Gen.TSCC`) in a Hausdorff space is homeomorphic to `Circle`. The converse is batch 148's
`tscc_circle`. -/
theorem tscc_homeomorph_circle {X : Type*} [TopologicalSpace X] [T2Space X] {J : Set X}
    (hJ : HPC.Moore.Gen.TSCC J) : Nonempty (J ≃ₜ Circle) := by
  obtain ⟨A, B, C₁, C₂, ⟨-, f₁, hf₁, rfl, rfl, rfl⟩, ⟨-, f₂, hf₂, rfl, h0, h1⟩, hint, rfl⟩ := hJ
  exact glue_circle hf₁.continuous hf₂.continuous hf₁.injective hf₂.injective h0.symm h1.symm
    hint.subset

end HPC.Jones
