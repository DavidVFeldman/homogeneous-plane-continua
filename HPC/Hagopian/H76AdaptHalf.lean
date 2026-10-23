import HPC.Hagopian.H76Glue

/-!
# Batch 163, item A: the lower half-collar through the drop arc (`exists_lower_halfcollar`)
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- Facts about one of the two Schoenflies squares filling a half of the lower rectangle. -/
theorem halfcollar_side {y x₀ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hx0 : 0 < x₀) (hx1 : x₀ < 1)
    {β₁ C R : Set Pt} {ψ : unitInterval → Pt} (hψr : range ψ = β₁) (hψ0 : ψ 0 = (y, 0))
    (hβQ : β₁ \ {((y, 0) : Pt), (x₀, -1)} ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0)
    {f : unitInterval × unitInterval → Pt} {φ : unitInterval → Pt}
    (hf : IsEmbedding f) (hfr : range f = (β₁ ∪ C) ∪ R) (hf0 : ∀ t, f (t, 0) = φ t)
    (hfψ : ∀ t, f (0, t) = ψ t) (hRQ : R ⊆ (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0) \ β₁)
    (hCQ : C ⊆ frontier (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0))
    (hCax : ∀ z ∈ C, z.2 = 0 → z ∈ range φ) :
    (range f ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) ∧ (∀ p, f p ∈ β₁ → p.1 = 0) ∧
      (∀ p, (f p).2 = 0 → p.2 = 0) := by
  have hQcl : closure (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0) = Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0 := by
    rw [closure_prod_eq, closure_Ioo (by norm_num), closure_Ioo (by norm_num)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfr, ← hQcl]
    rintro z ((hz | hz) | hz)
    · by_cases hzab : z ∈ ({((y, 0) : Pt), (x₀, -1)} : Set Pt)
      · rw [hQcl]
        rcases hzab with rfl | rfl
        · exact ⟨⟨hy0.le, hy1.le⟩, by norm_num⟩
        · exact ⟨⟨hx0.le, hx1.le⟩, by norm_num⟩
      · exact subset_closure (hβQ ⟨hz, hzab⟩)
    · exact frontier_subset_closure (hCQ hz)
    · exact subset_closure (hRQ hz).1
  · intro p hp
    rw [← hψr] at hp
    obtain ⟨r, hr⟩ := hp
    have := hf.injective ((hfψ r).trans hr)
    rw [← this]
  · intro p hp
    have hz : f p ∈ range f := mem_range_self p
    rw [hfr] at hz
    obtain ⟨t, ht⟩ : ∃ t, f (t, 0) = f p := by
      rcases hz with (hz | hz) | hz
      · have : f p ∈ ({((y, 0) : Pt), (x₀, -1)} : Set Pt) := by
          by_contra h
          have := (hβQ ⟨hz, h⟩).2.2
          linarith
        rcases this with h | h
        · exact ⟨0, by rw [hfψ 0, hψ0, h]⟩
        · have := congrArg Prod.snd h
          rw [hp] at this
          norm_num at this
      · obtain ⟨t, ht⟩ := hCax _ hz hp
        exact ⟨t, (hf0 t).trans ht⟩
      · exact absurd hp (ne_of_lt (hRQ hz).1.2.2)
    have := hf.injective ht
    rw [← this]

/-- **A lower half-collar through the drop arc.** `β₁` is an arc from `(y, 0)` to `(x₀, -1)`
crossing the open rectangle `Q = (0, 1) × (-1, 0)`. Then there is a map `H` of `[0, 1] × [0, 1]`
onto `Cl Q`, an embedding, which is the identity on the top edge (`H (x, 0) = (x, 0)`), maps the
open square onto `Q`, meets the top edge only from it, and whose vertical over `y` runs along
`β₁`. (Two-sided Schoenflies in each of the two halves into which `β₁` cuts `Q`.) -/
theorem exists_lower_halfcollar {y x₀ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hx0 : 0 < x₀)
    (hx1 : x₀ < 1) {β₁ : Set Pt} (hβ : TArc ((y, 0) : Pt) (x₀, -1) β₁)
    (hβQ : β₁ \ {((y, 0) : Pt), (x₀, -1)} ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0) :
    ∃ H : ℝ × ℝ → Pt, Continuous H ∧
      (∀ x ∈ Icc (0 : ℝ) 1, H (x, 0) = (x, 0)) ∧
      InjOn H (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo H (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) ∧
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (H p).2 = 0 → p.2 = 0) ∧
      H '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0 ∧
      (∀ s, H (y, s) ∈ β₁) := by
  set Q : Set Pt := Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0 with hQ
  set a : Pt := (y, 0) with ha
  set b : Pt := (x₀, -1) with hb
  have hQo : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have hQc : IsConnected Q :=
    ((convex_Ioo _ _).prod (convex_Ioo _ _)).isConnected ⟨(1 / 2, -1 / 2), by norm_num [hQ]⟩
  have hQb : Bornology.IsBounded Q := (Metric.isBounded_Ioo _ _).prod (Metric.isBounded_Ioo _ _)
  have hQf := rect_frontier hy0 hy1 hx0 hx1
  have hfrQ : ∀ z ∈ frontier Q, z ∉ Q := fun z hz hzQ => hz.2 (hQo.interior_eq.symm ▸ hzQ)
  have hC₁ := rect_tarc₁ hy0 hx0
  have hC₂ := rect_tarc₂ hy1 hx1
  have hC12 := rect_inter hy0 hy1 hx0 hx1
  have hK : TSCC (rectC₁ y x₀ ∪ rectC₂ y x₀) := ⟨a, b, _, _, hC₁, hC₂, hC12, rfl⟩
  obtain ⟨R₁, R₂, ⟨hR₁o, hR₁c, hR₁b, hR₁f⟩, ⟨hR₂o, hR₂c, hR₂b, hR₂f⟩, hsplit, hR12⟩ :=
    plane_split hK hQo hQc hQb hQf hC₁ hC₂ hC12 rfl hβ hβQ
  have hR₁Q : R₁ ⊆ Q \ β₁ := hsplit ▸ subset_union_left
  have hR₂Q : R₂ ⊆ Q \ β₁ := hsplit ▸ subset_union_right
  have hβC : ∀ C ⊆ frontier Q, a ∈ C → b ∈ C → β₁ ∩ C = {a, b} := by
    intro C hC haC hbC
    apply Subset.antisymm
    · rintro z ⟨hzβ, hzC⟩
      by_contra hz
      exact hfrQ z (hC hzC) (hβQ ⟨hzβ, hz⟩)
    · rintro z (rfl | rfl)
      · exact ⟨hβ.left_mem, haC⟩
      · exact ⟨hβ.right_mem, hbC⟩
  have hC₁f : rectC₁ y x₀ ⊆ frontier Q := hQf ▸ subset_union_left
  have hC₂f : rectC₂ y x₀ ⊆ frontier Q := hQf ▸ subset_union_right
  have hβC₁ := hβC _ hC₁f hC₁.left_mem hC₁.right_mem
  have hβC₂ := hβC _ hC₂f hC₂.left_mem hC₂.right_mem
  have hJ₁ : TSCC (β₁ ∪ rectC₁ y x₀) := ⟨a, b, β₁, _, hβ, hC₁, hβC₁, rfl⟩
  have hJ₂ : TSCC (β₁ ∪ rectC₂ y x₀) := ⟨a, b, β₁, _, hβ, hC₂, hβC₂, rfl⟩
  have haβ : a ∈ β₁ := hβ.left_mem
  have hbβ : b ∈ β₁ := hβ.right_mem
  obtain ⟨-, ψ, hψ, hψr, hψ0, hψ1⟩ := hβ
  -- the bottom sides
  let φL : unitInterval → Pt := fun t => ((1 - (t : ℝ)) * y, 0)
  let φR : unitInterval → Pt := fun t => (y + (t : ℝ) * (1 - y), 0)
  have hφLe : IsEmbedding φL := by
    refine (Continuous.isClosedEmbedding (by fun_prop) fun u v huv => ?_).isEmbedding
    have h := congrArg Prod.fst huv
    simp only [φL] at h
    exact Subtype.ext (by have := mul_right_cancel₀ hy0.ne' h; linarith)
  have hφRe : IsEmbedding φR := by
    refine (Continuous.isClosedEmbedding (by fun_prop) fun u v huv => ?_).isEmbedding
    have h := congrArg Prod.fst huv
    simp only [φR] at h
    exact Subtype.ext (mul_right_cancel₀ (by linarith : (1 - y) ≠ 0) (by linarith))
  have hφL0 : φL 0 = a := by simp [φL, ha]
  have hφR0 : φR 0 = a := by simp [φR, ha]
  have hφLC : ∀ t, φL t ∈ rectC₁ y x₀ := fun t =>
    Or.inl (Or.inl ⟨⟨by nlinarith [t.2.1, t.2.2], by nlinarith [t.2.1, t.2.2]⟩, rfl⟩)
  have hφRC : ∀ t, φR t ∈ rectC₂ y x₀ := fun t =>
    Or.inl (Or.inl ⟨⟨by nlinarith [t.2.1, t.2.2], by nlinarith [t.2.1, t.2.2]⟩, rfl⟩)
  have hφψ : ∀ (φ : unitInterval → Pt) (C : Set Pt), φ 0 = a → (∀ t, φ t ∈ C) →
      (∀ t, (φ t).2 = 0) → β₁ ∩ C = {a, b} → range φ ∩ range ψ = {φ 0} := by
    intro φ C h0 hC h2 hβC'
    apply Subset.antisymm
    · rintro z ⟨⟨t, rfl⟩, hz⟩
      rw [hψr] at hz
      have : φ t ∈ β₁ ∩ C := ⟨hz, hC t⟩
      rw [hβC'] at this
      rcases this with h | h
      · rw [h, h0]; rfl
      · have := congrArg Prod.snd h
        rw [h2 t, hb] at this
        norm_num at this
    · rintro z rfl
      exact ⟨⟨0, rfl⟩, ⟨0, by rw [hψ0, h0]⟩⟩
  obtain ⟨fL, hfL, hfLr, hfL0, hfLψ, hfLo⟩ := plane_schoenflies₂ hJ₁ hR₁o hR₁c hR₁b hR₁f hφLe hψ
    (fun _ ⟨t, ht⟩ => ht ▸ Or.inr (hφLC t)) (hψr ▸ subset_union_left) (by rw [hφL0, hψ0])
    (hφψ φL _ hφL0 hφLC (fun _ => rfl) hβC₁)
  obtain ⟨fR, hfR, hfRr, hfR0, hfRψ, hfRo⟩ := plane_schoenflies₂ hJ₂ hR₂o hR₂c hR₂b hR₂f hφRe hψ
    (fun _ ⟨t, ht⟩ => ht ▸ Or.inr (hφRC t)) (hψr ▸ subset_union_left) (by rw [hφR0, hψ0])
    (hφψ φR _ hφR0 hφRC (fun _ => rfl) hβC₂)
  have hCaxL : ∀ z ∈ rectC₁ y x₀, z.2 = 0 → z ∈ range φL := fun z hz hz2 =>
    rectC₁_axis hy0 z hz hz2
  have hCaxR : ∀ z ∈ rectC₂ y x₀, z.2 = 0 → z ∈ range φR := fun z hz hz2 =>
    rectC₂_axis hy1 z hz hz2
  obtain ⟨hLr, -, hL2⟩ := halfcollar_side hy0 hy1 hx0 hx1 hψr hψ0 hβQ hfL hfLr hfL0 hfLψ hR₁Q
    hC₁f hCaxL
  obtain ⟨hRr, hRβ, hR2⟩ := halfcollar_side hy0 hy1 hx0 hx1 hψr hψ0 hβQ hfR hfRr hfR0 hfRψ hR₂Q
    hC₂f hCaxR
  have hLR : ∀ p q, fL p = fR q → fL p ∈ β₁ := by
    intro p q e
    have h1 : fL p ∈ (β₁ ∪ rectC₁ y x₀) ∪ R₁ := hfLr ▸ mem_range_self p
    have h2 : fL p ∈ (β₁ ∪ rectC₂ y x₀) ∪ R₂ := e ▸ hfRr ▸ mem_range_self q
    by_contra hz
    rcases h1 with (h | h) | h
    · exact hz h
    · rcases h2 with (h' | h') | h'
      · exact hz h'
      · have : fL p ∈ rectC₁ y x₀ ∩ rectC₂ y x₀ := ⟨h, h'⟩
        rw [hC12] at this
        rcases this with e' | e'
        · exact hz (e' ▸ haβ)
        · exact hz (e' ▸ hbβ)
      · exact hfrQ _ (hC₁f h) (hR₂Q h').1
    · rcases h2 with (h' | h') | h'
      · exact hz h'
      · exact hfrQ _ (hC₂f h') (hR₁Q h).1
      · exact disjoint_left.1 hR12 h h'
  have hLRψ : ∀ t, fL (0, t) = fR (0, t) := fun t => (hfLψ t).trans (hfRψ t).symm
  refine ⟨glueMap y fL fR, glueMap_continuous hfL.continuous hfR.continuous hLRψ,
    glueMap_top hy0 hy1 hfL0 hfR0,
    glueMap_injOn hy0 hy1 hfL.injective hfR.injective
      (fun p q e => hRβ q (e ▸ hLR p q e)),
    fun p _ => glueMap_mapsTo hLr hRr p, glueMap_snd hL2 hR2, ?_, fun s => ?_⟩
  · apply Subset.antisymm
    · refine glueMap_image_sub hy0 hy1 hfLo hfRo (fun z hz => (hR₁Q hz).1)
        (fun z hz => (hR₂Q hz).1) fun s hs => ?_
      have hsI : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
      rw [hfLψ]
      refine hβQ ⟨hψr ▸ mem_range_self _, ?_⟩
      have hPs0 : clampI s ≠ 0 := fun e => by
        have := congrArg Subtype.val e; rw [clampI_val hsI, Set.Icc.coe_zero] at this; linarith [hs.1]
      have hPs1 : clampI s ≠ 1 := fun e => by
        have := congrArg Subtype.val e; rw [clampI_val hsI, Set.Icc.coe_one] at this; linarith [hs.2]
      rintro (e | e)
      · exact hPs0 (hψ.injective (e.trans hψ0.symm))
      · exact hPs1 (hψ.injective (e.trans hψ1.symm))
    · intro z hz
      by_cases hzβ : z ∈ β₁
      · rw [← hψr] at hzβ
        obtain ⟨r, rfl⟩ := hzβ
        have hr0 : (0 : ℝ) < r := by
          rcases eq_or_lt_of_le r.2.1 with e | e
          · have : r = 0 := Subtype.ext e.symm
            rw [this, hψ0] at hz
            exact absurd hz.2.2 (by simp [ha])
          · exact e
        have hr1 : (r : ℝ) < 1 := by
          rcases eq_or_lt_of_le r.2.2 with e | e
          · have : r = 1 := Subtype.ext e
            rw [this, hψ1] at hz
            exact absurd hz.2.1 (by simp [hb])
          · exact e
        exact ⟨(y, r), ⟨⟨hy0, hy1⟩, hr0, hr1⟩, by rw [glueMap_vert, hfLψ, clampI_coe]⟩
      · exact glueMap_image_sup hy0 hy1 hfLo hfRo (hsplit ▸ ⟨hz, hzβ⟩)
  · rw [glueMap_vert, hfLψ, ← hψr]
    exact mem_range_self _

end HPC.Hagopian
