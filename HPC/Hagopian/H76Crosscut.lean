import HPC.Hagopian.H76DCollar

/-!
# Batch 166, item B (addition): the low segment is a cross-cut of the domain

`rect_domain_crosscut`: in the domain `D′` of `rect_domain_aux`, the open segment `{x₀} × (0, w₂)`
from the bottom edge up to the lowest point `w = (x₀, w₂)` of `I` over `x₀` separates the open left
edge from the open right edge: no connected subset of `D′` missing the segment has closure meeting
both. Proof with one Jordan curve, `J_L = I_L ∪ {a} × [0, r₂] ∪ [a, x₀] × {0} ∪ {x₀} × [0, w₂]`
(`I_L` the sub-arc of `I` from `r` to `w`): a point of the open right edge lies in the unbounded
domain of `J_L` (a horizontal ray to the right misses `J_L`), and the points of `D′` near a point of
the open left edge lie in the bounded one (a half-disc to the right of the edge).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **The low vertical segment is a cross-cut of `D′`.** -/
theorem rect_domain_crosscut {a b c : ℝ} (hab : a < b) {r s : ℝ × ℝ} {I D : Set (ℝ × ℝ)}
    (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hr : r.1 = a) (hs : s.1 = b)
    (hIs : I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s}) (hDo : IsOpen D)
    (hDR : D ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
      ({b} : Set ℝ) ×ˢ Icc 0 s.2) {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : 0 < w₂)
    (hwI : ((x₀, w₂) : ℝ × ℝ) ∈ I) (hsegI : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) I)
    {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hSD : S ⊆ D \ ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂)
    {p q : ℝ × ℝ} (hp : p ∈ ({a} : Set ℝ) ×ˢ Ioo 0 r.2) (hq : q ∈ ({b} : Set ℝ) ×ˢ Ioo 0 s.2)
    (hpS : p ∈ closure S) (hqS : q ∈ closure S) : False := by
  have hrI := hI.left_mem
  have hrR := hIR hrI
  have hr2 : 0 < r.2 := hrR.2.1
  have hwR := hIR hwI
  have hrw : r ≠ ((x₀, w₂) : ℝ × ℝ) := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    linarith [hx₀.1]
  obtain ⟨IL, hILI, hIL⟩ := hI.exists_sub hrI hwI hrw
  set PL : Set (ℝ × ℝ) :=
    ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪ Icc a x₀ ×ˢ {0} ∪ ({x₀} : Set ℝ) ×ˢ Icc 0 w₂ with hPLdef
  have hPL : TArc r ((x₀, w₂) : ℝ × ℝ) PL := by
    have h := tarc_frame hx₀.1 hr2 hw₂
    rwa [show ((a, r.2) : Pt) = r from Prod.ext hr.symm rfl] at h
  have hIPL : IL ∩ PL = {r, ((x₀, w₂) : ℝ × ℝ)} := by
    apply subset_antisymm
    · rintro ⟨z1, z2⟩ ⟨hzIL, hzP⟩
      have hzI := hILI hzIL
      have hzR := hIR hzI
      rcases hzP with ((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩)
      · have hx' : z1 = a := hx
        have : (z1, z2) ∈ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) :=
          ⟨hzI, Or.inl hx', hy.1, hzR.2.2⟩
        rw [hIs] at this
        rcases this with h | h
        · exact Or.inl h
        · exfalso
          have h1 := congrArg Prod.fst h
          simp only at h1
          linarith
      · have hy' : z2 = 0 := hy
        have := hzR.2.1
        simp only at this
        linarith
      · have hx' : z1 = x₀ := hx
        rcases eq_or_lt_of_le hy.2 with h | h
        · right; simp only at h; rw [hx', h]; rfl
        · rcases eq_or_lt_of_le hy.1 with h0 | h0
          · exfalso
            have := hzR.2.1
            simp only at this h0
            linarith
          · exact absurd hzI (disjoint_left.1 hsegI ⟨hx, h0, h⟩)
    · rintro z (rfl | rfl)
      · exact ⟨hIL.left_mem, hPL.left_mem⟩
      · exact ⟨hIL.right_mem, hPL.right_mem⟩
  have hJ : TSCC (IL ∪ PL) := ⟨r, _, IL, PL, hIL, hPL, hIPL, rfl⟩
  obtain ⟨U, O, hUo, -, hOo, -, hUO, hUOu, hUb, -, hUf, -⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hJ)
  have hJR : IL ∪ PL ⊆ Icc a b ×ˢ Icc 0 c := by
    rintro z (hz | ((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩))
    · have := hIR (hILI hz)
      exact ⟨this.1, this.2.1.le, this.2.2⟩
    · have hx' : z.1 = a := hx
      exact ⟨⟨hx'.ge, by rw [hx']; exact hab.le⟩, hy.1, hy.2.trans hrR.2.2⟩
    · have hy' : z.2 = 0 := hy
      exact ⟨⟨hx.1, hx.2.trans hx₀.2.le⟩, by rw [hy'], by rw [hy']; linarith [hrR.2.2, hr2]⟩
    · have hx' : z.1 = x₀ := hx
      exact ⟨⟨by rw [hx']; exact hx₀.1.le, by rw [hx']; exact hx₀.2.le⟩, hy.1,
        hy.2.trans hwR.2.2⟩
  have hCO : (Icc a b ×ˢ Icc 0 c : Set (ℝ × ℝ))ᶜ ⊆ O := by
    obtain ⟨hCc, hCb⟩ := isConnected_compl_rect a b 0 c
    have hsub : (Icc a b ×ˢ Icc 0 c : Set (ℝ × ℝ))ᶜ ⊆ U ∪ O := by
      rw [hUOu]; exact compl_subset_compl.2 hJR
    rcases hCc.isPreconnected.subset_or_subset hUo hOo hUO hsub with h | h
    · exact absurd (hUb.subset h) hCb
    · exact h
  -- `S` misses the curve
  have hSJ : S ⊆ U ∪ O := by
    rw [hUOu]
    intro z hzS hzJ
    obtain ⟨hzD, hzseg⟩ := hSD hzS
    have hzF : z ∉ frontier D := fun h => (hDo.frontier_eq ▸ h).2 hzD
    rcases hzJ with hzIL | ((hz1 | hz2) | hz3)
    · exact hzF (by rw [hDf]; exact Or.inl (Or.inl (Or.inl (hILI hzIL))))
    · exact hzF (by rw [hDf]; exact Or.inl (Or.inr hz1))
    · exact hzF (by
        rw [hDf]; exact Or.inl (Or.inl (Or.inr ⟨⟨hz2.1.1, hz2.1.2.trans hx₀.2.le⟩, hz2.2⟩)))
    · obtain ⟨hx, hy⟩ := hz3
      have hx' : z.1 = x₀ := hx
      rcases eq_or_lt_of_le hy.1 with h0 | h0
      · have := (hDR hzD).2.1
        linarith
      · rcases eq_or_lt_of_le hy.2 with h1 | h1
        · apply hzF
          rw [hDf]
          have : z = ((x₀, w₂) : ℝ × ℝ) := Prod.ext hx' h1
          rw [this]; exact Or.inl (Or.inl (Or.inl hwI))
        · exact hzseg ⟨hx, h0, h1⟩
  -- the right-edge point is in the unbounded domain
  obtain ⟨hq1, hq2⟩ := hq
  have hq1' : q.1 = b := hq1
  have hqO : q ∈ O := by
    set Ray : Set (ℝ × ℝ) := Ici b ×ˢ {q.2} with hRay
    have hRayc : IsPreconnected Ray :=
      ((convex_Ici b).prod (convex_singleton q.2)).isPreconnected
    have hRayJ : Ray ⊆ U ∪ O := by
      rw [hUOu]
      rintro z ⟨hz1, hz2⟩ hzJ
      have hz1' : b ≤ z.1 := hz1
      have hz2' : z.2 = q.2 := hz2
      rcases hzJ with hzIL | ((hz' | hz') | hz')
      · have hzI := hILI hzIL
        have hzR := hIR hzI
        have hzb : z.1 = b := le_antisymm hzR.1.2 hz1'
        have : z ∈ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) := ⟨hzI, Or.inr hzb, hzR.2.1.le, hzR.2.2⟩
        rw [hIs] at this
        rcases this with h | h
        · have h1 := congrArg Prod.fst h
          rw [hzb, hr] at h1
          linarith
        · have h2 := congrArg Prod.snd h
          rw [hz2'] at h2
          linarith [hq2.2]
      · have : z.1 = a := hz'.1
        linarith
      · linarith [hz'.1.2, hx₀.2]
      · have : z.1 = x₀ := hz'.1
        linarith [hx₀.2]
    rcases hRayc.subset_or_subset hUo hOo hUO hRayJ with h | h
    · exfalso
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall q).1 (hUb.subset h)
      have hmem : ((b + |R| + 1, q.2) : ℝ × ℝ) ∈ Ray :=
        ⟨show b ≤ b + |R| + 1 by linarith [abs_nonneg R], rfl⟩
      have h1 := hR hmem
      rw [Metric.mem_closedBall, Prod.dist_eq] at h1
      have h2 := (le_max_left _ _).trans h1
      rw [Real.dist_eq, hq1', show b + |R| + 1 - b = |R| + 1 by ring,
        abs_of_pos (by positivity)] at h2
      linarith [le_abs_self R]
    · exact h ⟨show b ≤ q.1 from hq1'.ge, rfl⟩
  -- the points of `D` near the left-edge point are in the bounded domain
  obtain ⟨hp1, hp2⟩ := hp
  have hp1' : p.1 = a := hp1
  set K : Set (ℝ × ℝ) := IL ∪ Icc a x₀ ×ˢ {0} ∪ ({x₀} : Set ℝ) ×ˢ Icc 0 w₂ with hKdef
  have hKc : IsCompact K :=
    (hIL.isCompact.union (isCompact_Icc.prod isCompact_singleton)).union
      (isCompact_singleton.prod isCompact_Icc)
  have hpK : p ∉ K := by
    rintro ((hpIL | ⟨-, hy⟩) | ⟨hx, -⟩)
    · have hpI := hILI hpIL
      have : p ∈ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) :=
        ⟨hpI, Or.inl hp1', hp2.1.le, (hIR hpI).2.2⟩
      rw [hIs] at this
      rcases this with h | h
      · have h2 := congrArg Prod.snd h
        linarith [hp2.2]
      · have h1 := congrArg Prod.fst h
        rw [hs] at h1
        linarith
    · have hy' : p.2 = 0 := hy
      linarith [hp2.1]
    · have : p.1 = x₀ := hx
      linarith [hx₀.1]
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hKc.isClosed.isOpen_compl p hpK
  set δ := min δ₀ (min p.2 (r.2 - p.2)) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ (lt_min hp2.1 (by linarith [hp2.2]))
  have hball2 : ∀ z, dist z p < δ → |z.2 - p.2| < δ := fun z hz =>
    lt_of_le_of_lt (by rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_right _ _) hz
  have hJa : ∀ z, dist z p < δ → z ∈ IL ∪ PL → z.1 = a := by
    intro z hz hzJ
    have hzK : z ∉ K := hball (mem_ball.2 (lt_of_lt_of_le hz (min_le_left _ _)))
    rcases hzJ with hzIL | ((hz1 | hz2) | hz3)
    · exact absurd (Or.inl (Or.inl hzIL)) hzK
    · exact hz1.1
    · exact absurd (Or.inl (Or.inr hz2)) hzK
    · exact absurd (Or.inr hz3) hzK
  -- the left half-disc lies in `O`
  have hLH : ∀ z, dist z p < δ → z.1 < a → z ∈ O := fun z _ hz =>
    hCO fun h => by linarith [h.1.1]
  -- the right half-disc lies in `U`
  set RH : Set (ℝ × ℝ) := ball p δ ∩ {z | a < z.1} with hRH
  have hRHc : IsPreconnected RH :=
    ((convex_ball p δ).inter (convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear a)).isPreconnected
  have hRHJ : RH ⊆ U ∪ O := by
    rw [hUOu]
    rintro z ⟨hzb, hza⟩ hzJ
    have := hJa z (mem_ball.1 hzb) hzJ
    have hza' : a < z.1 := hza
    linarith
  have hpU : p ∈ closure U := by
    apply frontier_subset_closure
    rw [hUf]
    exact Or.inr (Or.inl (Or.inl ⟨hp1, hp2.1.le, hp2.2.le⟩))
  obtain ⟨z, hzU, hzp⟩ := Metric.mem_closure_iff.1 hpU δ hδpos
  rw [dist_comm] at hzp
  have hzRH : z ∈ RH := by
    refine ⟨mem_ball.2 hzp, ?_⟩
    rcases lt_trichotomy z.1 a with h | h | h
    · exact absurd (hLH z hzp h) (disjoint_left.1 hUO hzU)
    · exfalso
      have hzJ : z ∈ IL ∪ PL := by
        refine Or.inr (Or.inl (Or.inl ⟨h, ?_, ?_⟩))
        · have := abs_lt.1 (hball2 z hzp)
          have := min_le_right δ₀ (min p.2 (r.2 - p.2))
          have := min_le_left p.2 (r.2 - p.2)
          linarith
        · have := abs_lt.1 (hball2 z hzp)
          have := min_le_right δ₀ (min p.2 (r.2 - p.2))
          have := min_le_right p.2 (r.2 - p.2)
          linarith
      have : z ∈ U ∪ O := Or.inl hzU
      rw [hUOu] at this
      exact this hzJ
    · exact h
  have hRHU : RH ⊆ U := by
    rcases hRHc.subset_or_subset hUo hOo hUO hRHJ with h | h
    · exact h
    · exact absurd (h hzRH) (disjoint_left.1 hUO hzU)
  obtain ⟨u, huS, hup⟩ := Metric.mem_closure_iff.1 hpS δ hδpos
  rw [dist_comm] at hup
  have huU : u ∈ U := hRHU ⟨mem_ball.2 hup, (hDR (hSD huS).1).1.1⟩
  obtain ⟨v, hvO, hvS⟩ := mem_closure_iff.1 hqS O hOo hqO
  rcases hS.subset_or_subset hUo hOo hUO hSJ with h | h
  · exact disjoint_left.1 hUO (h hvS) hvO
  · exact disjoint_left.1 hUO huU (h huS)

/-- **`K₀` is a cross-cut of `D`** (in the plane): no connected subset of `π⁻¹[D] − K₀` has closure
meeting both `π⁻¹F[{a} × (0, r₂)]` and `π⁻¹F[{b} × (0, s₂)]` (the open side edges `⟨p₁, r⟩`,
`⟨p₅, s⟩` without their ends). -/
theorem K0_crosscut_aux {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (x₀, w₂) ∈ I₂)
    (hseg : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    {S : Set Pt} (hS : IsPreconnected S)
    (hSD : S ⊆ π ⁻¹' (F '' D') \ π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂)))
    (hL : (closure S ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty)
    (hR : (closure S ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty) : False := by
  obtain ⟨hFemb, -, -⟩ := hF
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hFemb.continuous
  have hFinj : InjOn F R1 := fun z hz w hw h =>
    congrArg Subtype.val (hFemb.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)
  have hRR1 : Icc a b ×ˢ Icc 0 c ⊆ R1 :=
    fun z ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hDR1 : D' ⊆ R1 := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hz
    exact hRR1 ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩
  set T' := π '' S with hT'
  set T := R1 ∩ F ⁻¹' T' with hT
  have hT'D : T' ⊆ F '' D' := by
    rintro _ ⟨u, hu, rfl⟩; exact (hSD hu).1
  have hTD : T ⊆ D' \ ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂ := by
    rintro z ⟨hzR, u, huS, hu⟩
    obtain ⟨⟨y, hyD, hy⟩, hns⟩ := hSD huS
    have hyz : y = z := hFinj (hDR1 hyD) hzR (hy.trans hu)
    exact ⟨hyz ▸ hyD, fun hzs => hns ⟨z, hzs, hu.symm⟩⟩
  have hFT : F '' T = T' := by
    rw [hT, image_inter_preimage]; exact inter_eq_right.2 (hT'D.trans (image_mono hDR1))
  have hTpc : IsPreconnected T := by
    have hT'r : T' ⊆ range (R1.restrict F) := fun p hp => by
      obtain ⟨y, hyD, rfl⟩ := hT'D hp; exact ⟨⟨y, hDR1 hyD⟩, rfl⟩
    have h1 : IsPreconnected (R1.restrict F ⁻¹' T') := by
      rw [← hFemb.isInducing.isPreconnected_image, image_preimage_eq_of_subset hT'r]
      exact hS.image _ hπc.continuousOn
    have heq : T = Subtype.val '' (R1.restrict F ⁻¹' T') := by
      ext z
      constructor
      · rintro ⟨hzR, hzT⟩; exact ⟨⟨z, hzR⟩, hzT, rfl⟩
      · rintro ⟨z, hzT, rfl⟩; exact ⟨z.2, hzT⟩
    rw [heq]; exact h1.image _ continuous_subtype_val.continuousOn
  have hclT : closure T ⊆ Icc a b ×ˢ Icc 0 c :=
    closure_minimal (fun z hz => by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR (hTD hz).1
      exact ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩) (isClosed_Icc.prod isClosed_Icc)
  have hclTc : IsCompact (closure T) :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure hclT
  have hcl : ∀ z ∈ closure S, ∀ p ∈ R1, F p = π z → p ∈ closure T := by
    intro z hz p hpR hzp
    have h1 : π z ∈ closure T' := image_closure_subset_closure_image hπc ⟨z, hz, rfl⟩
    have h2 : closure T' ⊆ F '' closure T := by
      rw [← hFT]
      exact closure_minimal (image_mono subset_closure)
        (hclTc.image_of_continuousOn (hFc.mono (hclT.trans hRR1))).isClosed
    obtain ⟨p', hp', hFp'⟩ := h2 h1
    have : p' = p := hFinj (hRR1 (hclT hp')) hpR (hFp'.trans hzp.symm)
    rw [← this]; exact hp'
  have hr₂ := hI.left_mem.1.2
  have hs₂ := hI.right_mem.1.2
  obtain ⟨z₁, hz₁S, p, hp, hz₁p⟩ := hL
  obtain ⟨z₂, hz₂S, q, hq, hz₂q⟩ := hR
  have hpR : p ∈ R1 := by
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : p.1 = a := hp1
    exact hRR1 ⟨⟨hp1'.ge, by rw [hp1']; exact hab.le⟩, hp2.1.le, hp2.2.le.trans hr₂.2⟩
  have hqR : q ∈ R1 := by
    obtain ⟨hq1, hq2⟩ := hq
    have hq1' : q.1 = b := hq1
    exact hRR1 ⟨⟨by rw [hq1']; exact hab.le, hq1'.le⟩, hq2.1.le, hq2.2.le.trans hs₂.2⟩
  exact rect_domain_crosscut (r := ((a, r₂) : ℝ × ℝ)) (s := ((b, s₂) : ℝ × ℝ)) hab hI
    inter_subset_left rfl rfl hIs hDo hDR hDf hx₀ hw₂.1
    ⟨⟨⟨hx₀.1.le, hx₀.2.le⟩, hw₂⟩, hFw⟩ hseg hTpc hTD hp hq (hcl z₁ hz₁S p hpR hz₁p)
    (hcl z₂ hz₂S q hqR hz₂q)

end HPC.Hagopian
