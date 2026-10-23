import HPC.HO16.LadderDefs

/-!
# Batch 197, §5 step 1: a sign function for a separator

Commission 197 §5, step 1, with a Lipschitz function in place of uniform continuity: for a
separator `M ⊆ G × (0, 1)` of `G × {0}` from `G × {1}` in `G⋆` and an open `U ⊇ M`, the function
`u = infDist · K₀ - infDist · K₁` (with `K = G⋆ \ (U ∩ G × (0, 1))`, `K₀ = K \ O₁`, `K₁ = K \ O₀`)
is `≤ 0` on `G × {0}`, `> 0` on `G × {1}`, and a point of `G⋆` within `δ` of a point where
`u ≤ 0` and of a point where `u > 0` lies in `U ∩ G × (0, 1)` (`exists_sign_fn`).
-/

namespace HPC.HO16

open Set Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

theorem abs_infDist_sub_le (K : Set (E × ℝ)) (p c : E × ℝ) :
    |infDist p K - infDist c K| ≤ dist p c := by
  rw [abs_le]
  constructor
  · have := infDist_le_infDist_add_dist (x := c) (y := p) (s := K)
    rw [dist_comm] at this
    linarith
  · have := infDist_le_infDist_add_dist (x := p) (y := c) (s := K)
    linarith

/-- **A sign function for a separator** (commission 197 §5, step 1). -/
theorem exists_sign_fn {G : Set E} (hGc : IsCompact G) (hGne : G.Nonempty) {M : Set (E × ℝ)}
    (hM : M ⊆ G ×ˢ Ioo (0 : ℝ) 1)
    (hsep : SeparatesIn (G ×ˢ Icc (0 : ℝ) 1) M (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ)))
    {U : Set (E × ℝ)} (hU : IsOpen U) (hMU : M ⊆ U) :
    ∃ (u : E × ℝ → ℝ) (δ : ℝ), 0 < δ ∧ (∀ x ∈ G, u (x, 0) ≤ 0) ∧ (∀ x ∈ G, 0 < u (x, 1)) ∧
      ∀ p ∈ G ×ˢ Icc (0 : ℝ) 1, ∀ c₁ c₂ : E × ℝ, dist p c₁ < δ → dist p c₂ < δ →
        u c₁ ≤ 0 → 0 < u c₂ → p ∈ U ∩ G ×ˢ Ioo (0 : ℝ) 1 := by
  obtain ⟨O₀, O₁, hO₀, hO₁, hcov, hdisj, h0, h1⟩ := hsep
  set Gs := G ×ˢ Icc (0 : ℝ) 1 with hGs
  set K := Gs \ (U ∩ univ ×ˢ Ioo (0 : ℝ) 1) with hK
  have hGsc : IsCompact Gs := hGc.prod isCompact_Icc
  have hKc : IsCompact K :=
    hGsc.diff (hU.inter (isOpen_univ.prod isOpen_Ioo))
  set K₀ := K \ O₁ with hK₀
  set K₁ := K \ O₀ with hK₁
  have hK₀c : IsCompact K₀ := hKc.diff hO₁
  have hK₁c : IsCompact K₁ := hKc.diff hO₀
  have hKM : ∀ p ∈ K, p ∈ Gs \ M := by
    intro p hp
    refine ⟨hp.1, fun hpM => hp.2 ⟨hMU hpM, mem_univ _, (hM hpM).2⟩⟩
  have hnot01 : ∀ p ∈ K, p ∈ O₁ → p ∉ O₀ := by
    intro p hp h1' h0'
    have : p ∈ O₀ ∩ O₁ ∩ (Gs \ M) := ⟨⟨h0', h1'⟩, hKM p hp⟩
    rw [hdisj] at this
    exact this
  have hdis : Disjoint K₀ K₁ := by
    rw [Set.disjoint_left]
    rintro p ⟨hpK, hp1⟩ ⟨-, hp0⟩
    rcases hcov (hKM p hpK) with h | h
    · exact hp0 h
    · exact hp1 h
  have hcov' : ∀ p ∈ K, p ∈ K₀ ∨ p ∈ K₁ := by
    intro p hp
    by_cases h : p ∈ O₁
    · exact Or.inr ⟨hp, hnot01 p hp h⟩
    · exact Or.inl ⟨hp, h⟩
  have hbot : ∀ x ∈ G, ((x, 0) : E × ℝ) ∈ K₀ := by
    intro x hx
    have hK' : ((x, 0) : E × ℝ) ∈ K :=
      ⟨⟨hx, by simp⟩, fun h => by simpa using h.2.2⟩
    refine ⟨hK', fun h1' => hnot01 _ hK' h1' (h0 ⟨hx, rfl⟩)⟩
  have htop : ∀ x ∈ G, ((x, 1) : E × ℝ) ∈ K₁ := by
    intro x hx
    have hK' : ((x, 1) : E × ℝ) ∈ K :=
      ⟨⟨hx, by simp⟩, fun h => by simpa using h.2.2⟩
    refine ⟨hK', fun h0' => hnot01 _ hK' (h1 ⟨hx, rfl⟩) h0'⟩
  obtain ⟨x₀, hx₀⟩ := hGne
  have hK₀ne : K₀.Nonempty := ⟨_, hbot x₀ hx₀⟩
  have hK₁ne : K₁.Nonempty := ⟨_, htop x₀ hx₀⟩
  set u : E × ℝ → ℝ := fun p => infDist p K₀ - infDist p K₁ with hu
  have hpos₀ : ∀ p ∈ K₀, u p < 0 := by
    intro p hp
    have h1' : 0 < infDist p K₁ :=
      (infDist_pos_iff_notMem_closure hK₁ne).1
        (by rw [hK₁c.isClosed.closure_eq]; exact Set.disjoint_left.1 hdis hp)
    simp only [hu, infDist_zero_of_mem hp]
    linarith
  have hpos₁ : ∀ p ∈ K₁, 0 < u p := by
    intro p hp
    have h0' : 0 < infDist p K₀ :=
      (infDist_pos_iff_notMem_closure hK₀ne).1
        (by rw [hK₀c.isClosed.closure_eq]; exact Set.disjoint_right.1 hdis hp)
    simp only [hu, infDist_zero_of_mem hp]
    linarith
  have hcont : Continuous u :=
    (continuous_infDist_pt K₀).sub (continuous_infDist_pt K₁)
  have hlip : ∀ p c, |u p - u c| ≤ 2 * dist p c := by
    intro p c
    have a1 := abs_infDist_sub_le K₀ p c
    have a2 := abs_infDist_sub_le K₁ p c
    calc |u p - u c| = |(infDist p K₀ - infDist c K₀) - (infDist p K₁ - infDist c K₁)| := by
          simp only [hu]; ring_nf
      _ ≤ |infDist p K₀ - infDist c K₀| + |infDist p K₁ - infDist c K₁| := abs_sub _ _
      _ ≤ 2 * dist p c := by linarith
  obtain ⟨ω, hω, hωK⟩ : ∃ ω > 0, ∀ p ∈ K, ω ≤ |u p| := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun p hp => by rw [hKe] at hp; exact absurd hp (notMem_empty p)⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne (continuous_abs.comp hcont).continuousOn
      refine ⟨|u p₀|, ?_, fun p hp => hmin hp⟩
      rcases hcov' p₀ hp₀ with h | h
      · exact abs_pos.2 (hpos₀ p₀ h).ne
      · exact abs_pos.2 (hpos₁ p₀ h).ne'
  refine ⟨u, ω / 4, by positivity, fun x hx => (hpos₀ _ (hbot x hx)).le,
    fun x hx => hpos₁ _ (htop x hx), ?_⟩
  intro p hp c₁ c₂ hc₁ hc₂ hu₁ hu₂
  have hpK : p ∉ K := by
    intro hpK
    have k := hωK p hpK
    have l1 := hlip p c₁
    have l2 := hlip p c₂
    rw [abs_le] at l1 l2
    rw [le_abs] at k
    rcases k with k | k <;> linarith
  have : p ∈ U ∩ univ ×ˢ Ioo (0 : ℝ) 1 := by
    by_contra h
    exact hpK ⟨hp, h⟩
  exact ⟨this.1, hp.1, this.2.2⟩

end

end HPC.HO16
