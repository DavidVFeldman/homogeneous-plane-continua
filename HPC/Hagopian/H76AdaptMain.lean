import HPC.Hagopian.H76AdaptHalf

/-!
# Batch 163, item A: assembling the adapted collar (`collar_adapted_core`, `exists_collar_adapted_aux`)
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **Assembly.** Given a continuous collar `F` and a path `g` in collar coordinates which runs
through the open lower rectangle and ends at `(y, 0)`, the collar with the upper half of `F` and the
lower half-collar of `exists_lower_halfcollar` has its vertical below `γ y` inside `F[g[[t₁, 1]]]`. -/
theorem collar_adapted_core {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hFc : Continuous F)
    (hF : IsCollar γ F) {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1) {g : ℝ → Pt} {t₁ : ℝ}
    (ht₁ : t₁ < 1) (hgc : ContinuousOn g (Icc t₁ 1)) (hginj : InjOn g (Icc t₁ 1))
    (hg1 : g 1 = ((y : ℝ), 0))
    (hgQ : ∀ t, t₁ ≤ t → t < 1 → g t ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0) :
    ∃ F' : ℝ × ℝ → Pt, IsCollar γ F' ∧ ∃ c > 0,
      F' '' ({(y : ℝ)} ×ˢ Icc (-c) 0) ⊆ F '' (g '' Icc t₁ 1) := by
  have hy0' : (0 : ℝ) < y := hy0
  have hy1' : (y : ℝ) < 1 := hy1
  obtain ⟨x₀, hx0, hx1, β₁, hβ, hβQ, W, hW, hβW⟩ :=
    exists_drop_arc hy0' hy1' ht₁ hgc hginj hg1 hgQ
  obtain ⟨H, hHc, hHtop, hHinj, hHmaps, hH2, hHimg, hHy⟩ :=
    exists_lower_halfcollar hy0' hy1' hx0 hx1 hβ hβQ
  obtain ⟨hemb, h0, hopen⟩ := hF
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hFinj : InjOn F K := fun p hp q hq e =>
    congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) e)
  set P' : ℝ → ℝ := fun x => (projIcc (0 : ℝ) 1 zero_le_one x : ℝ) with hP'
  have hP'v : ∀ x ∈ Icc (0 : ℝ) 1, P' x = x := fun x hx => by
    simp only [hP', projIcc_of_mem _ hx]
  have hP'm : ∀ x, P' x ∈ Icc (0 : ℝ) 1 := fun x => (projIcc _ _ _ x).2
  have hP'c : Continuous P' := continuous_subtype_val.comp continuous_projIcc
  set F' : ℝ × ℝ → Pt := fun p =>
    if 0 ≤ p.2 then F (P' p.1, p.2) else F (H (P' p.1, -p.2)) with hF'
  have hF'U : ∀ p : ℝ × ℝ, 0 ≤ p.2 → F' p = F (P' p.1, p.2) := fun p hp => by
    rw [hF']; exact if_pos hp
  have hF'D : ∀ p : ℝ × ℝ, ¬ 0 ≤ p.2 → F' p = F (H (P' p.1, -p.2)) := fun p hp => by
    rw [hF']; exact if_neg hp
  have hF'c : Continuous F' := by
    rw [hF']
    refine Continuous.if_le ?_ ?_ continuous_const continuous_snd ?_
    · exact hFc.comp ((hP'c.comp continuous_fst).prodMk continuous_snd)
    · exact hFc.comp (hHc.comp ((hP'c.comp continuous_fst).prodMk continuous_snd.neg))
    · intro p hp
      simp only [← hp, neg_zero]
      rw [hHtop _ (hP'm _)]
  have hHK : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, H p ∈ K := fun p hp =>
    ⟨(hHmaps hp).1, ⟨(hHmaps hp).2.1, by linarith [(hHmaps hp).2.2]⟩⟩
  have hlow : ∀ p ∈ K, ¬ 0 ≤ p.2 → (P' p.1, -p.2) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp h => ⟨hP'm _, by linarith [not_le.1 h], by linarith [hp.2.1]⟩
  have hmixed : ∀ p ∈ K, ∀ q ∈ K, 0 ≤ p.2 → ¬ 0 ≤ q.2 → F' p ≠ F' q := by
    intro p hp q hq h1 h2 e
    rw [hF'U _ h1, hF'D _ h2, hP'v _ hp.1] at e
    have hpK : (p.1, p.2) ∈ K := hp
    have := hFinj hpK (hHK _ (hlow q hq h2)) e
    have hle := (hHmaps (hlow q hq h2)).2.2
    have hp2 : p.2 = (H (P' q.1, -q.2)).2 := congrArg Prod.snd this
    have h3 : (H (P' q.1, -q.2)).2 = 0 := by linarith
    have := hH2 _ (hlow q hq h2) h3
    simp only at this
    exact h2 (by linarith)
  refine ⟨F', ⟨?_, ?_, ?_⟩, ?_⟩
  · haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
    refine (Continuous.isClosedEmbedding (hF'c.comp continuous_subtype_val) ?_).isEmbedding
    rintro ⟨p, hp⟩ ⟨q, hq⟩ e
    change F' p = F' q at e
    apply Subtype.ext
    change p = q
    by_cases h1 : 0 ≤ p.2 <;> by_cases h2 : 0 ≤ q.2
    · rw [hF'U _ h1, hF'U _ h2, hP'v _ hp.1, hP'v _ hq.1] at e
      exact hFinj hp hq e
    · exact absurd e (hmixed p hp q hq h1 h2)
    · exact absurd e.symm (hmixed q hq p hp h2 h1)
    · rw [hF'D _ h1, hF'D _ h2] at e
      have := hHinj (hlow p hp h1) (hlow q hq h2)
        (hFinj (hHK _ (hlow p hp h1)) (hHK _ (hlow q hq h2)) e)
      simp only [Prod.mk.injEq] at this
      rw [hP'v _ hp.1, hP'v _ hq.1] at this
      exact Prod.ext this.1 (by linarith [this.2])
  · intro t
    rw [hF'U _ le_rfl]
    simp only
    rw [hP'v _ t.2]
    exact h0 t
  · have : F' '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) = F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
      apply Subset.antisymm
      · rintro _ ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
        have hxI := Ioo_subset_Icc_self hx
        by_cases h : 0 ≤ s
        · rw [hF'U _ h]
          simp only
          rw [hP'v _ hxI]
          exact ⟨(x, s), ⟨hx, hs⟩, rfl⟩
        · rw [hF'D _ h]
          simp only
          rw [hP'v _ hxI]
          have : H (x, -s) ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0 :=
            hHimg ▸ ⟨(x, -s), ⟨hx, by linarith [not_le.1 h], by linarith [hs.1]⟩, rfl⟩
          exact ⟨H (x, -s), ⟨this.1, this.2.1, by linarith [this.2.2]⟩, rfl⟩
      · rintro _ ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
        by_cases h : 0 ≤ s
        · refine ⟨(x, s), ⟨hx, hs⟩, ?_⟩
          rw [hF'U _ h]
          simp only
          rw [hP'v _ (Ioo_subset_Icc_self hx)]
        · have hmem : (x, s) ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0 := ⟨hx, hs.1, not_le.1 h⟩
          rw [← hHimg] at hmem
          obtain ⟨⟨u, r⟩, ⟨hu, hr⟩, hur⟩ := hmem
          refine ⟨(u, -r), ⟨hu, by linarith [hr.2], by linarith [hr.1]⟩, ?_⟩
          rw [hF'D _ (by simp only; linarith [hr.1])]
          simp only [neg_neg]
          rw [hP'v _ (Ioo_subset_Icc_self hu), hur]
    rw [this]; exact hopen
  · have hcont : ContinuousAt (fun s : ℝ => H ((y : ℝ), s)) 0 :=
      (hHc.comp (continuous_const.prodMk continuous_id)).continuousAt
    have hy00 : H ((y : ℝ), 0) = ((y : ℝ), 0) := hHtop _ ⟨hy0'.le, hy1'.le⟩
    have hW' : (fun s : ℝ => H ((y : ℝ), s)) ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
      hcont.preimage_mem_nhds (by rw [hy00]; exact hW)
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW'
    refine ⟨ε / 2, half_pos hε, ?_⟩
    rintro _ ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
    have hx' : x = y := hx
    subst hx'
    by_cases h : 0 ≤ s
    · have hs0 : s = 0 := le_antisymm hs.2 h
      rw [hF'U _ h]
      simp only
      rw [hP'v _ ⟨hy0'.le, hy1'.le⟩, hs0]
      exact ⟨g 1, ⟨1, ⟨ht₁.le, le_rfl⟩, rfl⟩, by rw [hg1]⟩
    · rw [hF'D _ h]
      simp only
      rw [hP'v _ ⟨hy0'.le, hy1'.le⟩]
      refine ⟨H ((y : ℝ), -s), hβW ⟨hHy _, hεW ?_⟩, rfl⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, not_le.1 h]

/-- **A collar in which a given transverse arc is vertical** (item A). -/
theorem exists_collar_adapted_aux {γ : unitInterval → Pt} (hγ : IsEmbedding γ) {y : unitInterval}
    (hy0 : 0 < y) (hy1 : y < 1) {b : Pt} {β : Set Pt} (hβ : TArc b (γ y) β)
    (hβγ : β ∩ range γ = {γ y}) :
    ∃ F : ℝ × ℝ → Pt, IsCollar γ F ∧ ∃ c > 0, F '' ({(y : ℝ)} ×ˢ Icc (-c) 0) ⊆ β := by
  classical
  obtain ⟨F₀, hF₀⟩ := exists_collar_aux hγ
  obtain ⟨F, hFc, hF, -⟩ := hF₀.exists_continuous
  have hF' := hF
  obtain ⟨hemb, h0, hopen⟩ := hF'
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  set O := Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 with hO
  have hOK : O ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hFinj : InjOn F K := fun p hp q hq e =>
    congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) e)
  obtain ⟨-, f, hf, hfr, hf0, hf1⟩ := hβ
  -- the inverse of the collar on its image
  set S := range (K.restrict F) with hS
  let Fi : Pt → Pt := fun p => if h : p ∈ S then ((hemb.toHomeomorph.symm ⟨p, h⟩ : K) : Pt) else 0
  have hFic : ContinuousOn Fi S := by
    rw [continuousOn_iff_continuous_restrict]
    have : S.restrict Fi = fun p : S => ((hemb.toHomeomorph.symm p : K) : Pt) := by
      funext p
      simp only [restrict_apply, Fi, dif_pos p.2]
      rfl
    rw [this]
    exact continuous_subtype_val.comp hemb.toHomeomorph.symm.continuous
  have hFiK : ∀ p ∈ S, Fi p ∈ K := fun p h => by
    simp only [Fi, dif_pos h]; exact (hemb.toHomeomorph.symm ⟨p, h⟩).2
  have hFFi : ∀ p ∈ S, F (Fi p) = p := fun p h => by
    simp only [Fi, dif_pos h]
    have h2 := congrArg Subtype.val (hemb.toHomeomorph.apply_symm_apply ⟨p, h⟩)
    rw [IsEmbedding.toHomeomorph_apply_coe] at h2
    exact h2
  have hFS : ∀ q ∈ K, F q ∈ S := fun q hq => ⟨⟨q, hq⟩, rfl⟩
  have hFiF : ∀ q ∈ K, Fi (F q) = q := fun q hq =>
    hFinj (hFiK _ (hFS q hq)) hq (hFFi _ (hFS q hq))
  -- the end of `β` inside the open collar rectangle
  have hγy : γ y = F ((y : ℝ), 0) := (h0 y).symm
  have hy0' : (0 : ℝ) < y := hy0
  have hy1' : (y : ℝ) < 1 := hy1
  have hyO : ((y : ℝ), (0 : ℝ)) ∈ O := ⟨⟨hy0', hy1'⟩, by norm_num, by norm_num⟩
  have hN : f ⁻¹' (F '' O) ∈ 𝓝 (1 : unitInterval) :=
    hf.continuous.continuousAt.preimage_mem_nhds
      (hopen.mem_nhds (by rw [hf1, hγy]; exact mem_image_of_mem _ hyO))
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  set t₁ : ℝ := max 0 (1 - ε / 2) with ht₁
  have ht₁1 : t₁ < 1 := max_lt (by norm_num) (by linarith)
  have ht₁0 : 0 ≤ t₁ := le_max_left _ _
  set P : ℝ → unitInterval := projIcc (0 : ℝ) 1 zero_le_one with hP
  have hPv : ∀ x ∈ Icc (0 : ℝ) 1, (P x : ℝ) = x := fun x hx => by rw [hP, projIcc_of_mem _ hx]
  have hfPN : ∀ t ∈ Icc t₁ 1, f (P t) ∈ F '' O := fun t ht => by
    apply hεN
    rw [mem_ball, Subtype.dist_eq, hPv _ ⟨ht₁0.trans ht.1, ht.2⟩]
    change dist t 1 < ε
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, le_max_right 0 (1 - ε / 2)]
  set g : ℝ → Pt := fun t => Fi (f (P t)) with hg
  have hfPS : ∀ t ∈ Icc t₁ 1, f (P t) ∈ S := fun t ht => by
    obtain ⟨q, hq, hqe⟩ := hfPN t ht
    rw [← hqe]; exact hFS q (hOK hq)
  have hgc : ContinuousOn g (Icc t₁ 1) :=
    hFic.comp (hf.continuous.comp continuous_projIcc).continuousOn fun t ht => hfPS t ht
  have hFg : ∀ t ∈ Icc t₁ 1, F (g t) = f (P t) := fun t ht => hFFi _ (hfPS t ht)
  have hgO : ∀ t ∈ Icc t₁ 1, g t ∈ O := fun t ht => by
    obtain ⟨q, hq, hqe⟩ := hfPN t ht
    simp only [hg]
    rw [← hqe, hFiF q (hOK hq)]
    exact hq
  have hginj : InjOn g (Icc t₁ 1) := fun t ht t' ht' e' => by
    have h1 : f (P t) = f (P t') := by rw [← hFg t ht, ← hFg t' ht', e']
    have h2 := congrArg Subtype.val (hf.injective h1)
    rwa [hPv _ ⟨ht₁0.trans ht.1, ht.2⟩, hPv _ ⟨ht₁0.trans ht'.1, ht'.2⟩] at h2
  have hP1 : P 1 = 1 := Subtype.ext (hPv 1 ⟨zero_le_one, le_rfl⟩)
  have hg1 : g 1 = ((y : ℝ), 0) := by
    simp only [hg]
    rw [hP1, hf1, hγy, hFiF _ (hOK hyO)]
  have hFgβ : ∀ t ∈ Icc t₁ 1, F (g t) ∈ β := fun t ht => by
    rw [hFg t ht, ← hfr]; exact mem_range_self _
  have hg2 : ∀ t, t₁ ≤ t → t < 1 → (g t).2 ≠ 0 := by
    intro t ht1 ht2 h2
    have hgt := hgO t ⟨ht1, ht2.le⟩
    have hmem : (g t).1 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hgt.1
    have hγ' : F (g t) = γ ⟨(g t).1, hmem⟩ := by
      rw [← h0 ⟨(g t).1, hmem⟩]
      congr 1
      exact Prod.ext rfl h2
    have : F (g t) ∈ β ∩ range γ := ⟨hFgβ t ⟨ht1, ht2.le⟩, hγ' ▸ mem_range_self _⟩
    rw [hβγ, hFg t ⟨ht1, ht2.le⟩, ← hf1] at this
    have h3 := congrArg Subtype.val (hf.injective this)
    rw [hPv _ ⟨ht₁0.trans ht1, ht2.le⟩] at h3
    exact ht2.ne h3
  have hpc : IsPreconnected ((fun t => (g t).2) '' Ico t₁ 1) :=
    isPreconnected_Ico.image _ ((continuous_snd.comp_continuousOn hgc).mono Ico_subset_Icc_self)
  by_cases hneg : ∀ t, t₁ ≤ t → t < 1 → (g t).2 < 0
  · obtain ⟨F', hF', c, hc, hsub⟩ := collar_adapted_core hFc hF hy0 hy1 ht₁1 hgc hginj hg1
      fun t ht1 ht2 => ⟨(hgO t ⟨ht1, ht2.le⟩).1, (hgO t ⟨ht1, ht2.le⟩).2.1, hneg t ht1 ht2⟩
    refine ⟨F', hF', c, hc, hsub.trans ?_⟩
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact hFgβ t ht
  · push_neg at hneg
    obtain ⟨t₀, ht₀1, ht₀2, ht₀⟩ := hneg
    have hpos : ∀ t, t₁ ≤ t → t < 1 → 0 < (g t).2 := by
      intro t ht1 ht2
      by_contra hc
      push_neg at hc
      have hlt : (g t).2 < 0 := lt_of_le_of_ne hc (hg2 t ht1 ht2)
      have := hpc.Icc_subset ⟨t, ⟨ht1, ht2⟩, rfl⟩ ⟨t₀, ⟨ht₀1, ht₀2⟩, rfl⟩ ⟨hlt.le, ht₀⟩
      obtain ⟨t', ⟨ht'1, ht'2⟩, ht'⟩ := this
      exact hg2 t' ht'1 ht'2 ht'
    set g' : ℝ → Pt := fun t => ((g t).1, -(g t).2) with hg'
    have hgc' : ContinuousOn g' (Icc t₁ 1) :=
      (continuous_fst.prodMk continuous_snd.neg).comp_continuousOn hgc
    have hginj' : InjOn g' (Icc t₁ 1) := fun t ht t' ht' e' => by
      simp only [hg', Prod.mk.injEq, neg_inj] at e'
      exact hginj ht ht' (Prod.ext e'.1 e'.2)
    have hg1' : g' 1 = ((y : ℝ), 0) := by simp [hg', hg1]
    obtain ⟨F', hF', c, hc, hsub⟩ := collar_adapted_core
      (hFc.comp (continuous_fst.prodMk continuous_snd.neg)) hF.flip hy0 hy1 ht₁1 hgc' hginj' hg1'
      fun t ht1 ht2 => ⟨(hgO t ⟨ht1, ht2.le⟩).1,
        by simp only [hg']; linarith [(hgO t ⟨ht1, ht2.le⟩).2.2], by
          simp only [hg']; linarith [hpos t ht1 ht2]⟩
    refine ⟨F', hF', c, hc, hsub.trans ?_⟩
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    change F ((g t).1, - -(g t).2) ∈ β
    rw [neg_neg]
    exact hFgβ t ht

end HPC.Hagopian
