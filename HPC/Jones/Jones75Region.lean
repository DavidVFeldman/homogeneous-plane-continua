import HPC.Jones.Jones75Shadow

/-!
# Jones 1975 II (batch 190), part 3: the region of a thin pass

Commission 190 §4 and §7: the small lemmas N1 (`thinPass_arc`), N2 (`tarc_lowest`), N4
(`IsPass.lc_left_mem_closure`), the facts (R1) (`region_pass`, `region_thin_above`), (R2)
(`region_cross`), and Lemma A of §5 (`region_lemmaA`). The region is `R_m = F(D_m)`, with `D_m`
from `rect_domain_aux`; everything is stated in collar coordinates.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **N2, lowest point on a vertical.** -/
theorem tarc_lowest {r s : ℝ × ℝ} {I : Set (ℝ × ℝ)} (hI : TArc r s I) {a b c : ℝ}
    (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hr : r.1 = a) (hs : s.1 = b) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) :
    ∃ w > 0, ((x₀, w) : ℝ × ℝ) ∈ I ∧ Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w) I := by
  obtain ⟨-, f, hf, hfr, hf0, hf1⟩ := hI
  have hgc : Continuous fun t => (f t).1 := continuous_fst.comp hf.continuous
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1 hgc
    (show x₀ ∈ Icc (f 0).1 (f 1).1 by rw [hf0, hf1, hr, hs]; exact ⟨hx₀.1.le, hx₀.2.le⟩)
  set Z := I ∩ {p | p.1 = x₀} with hZ
  have hIc : IsCompact I := hfr ▸ isCompact_range hf.continuous
  have hZc : IsCompact Z := hIc.inter_right (isClosed_eq continuous_fst continuous_const)
  have hZne : Z.Nonempty := ⟨f t, hfr ▸ mem_range_self t, ht⟩
  obtain ⟨p, ⟨hpI, hp1⟩, hmin⟩ := hZc.exists_isMinOn hZne continuous_snd.continuousOn
  refine ⟨p.2, (hIR hpI).2.1, ?_, ?_⟩
  · have : p = (x₀, p.2) := Prod.ext hp1 rfl
    rw [← this]; exact hpI
  · rw [Set.disjoint_left]
    rintro q ⟨hq1, hq2⟩ hqI
    have := isMinOn_iff.1 hmin q ⟨hqI, hq1⟩
    linarith [hq2.2]

section Region

variable {M : Set Pt} {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} {ℓ : ℝ → M}

/-- **N4, end points**: the end points of a pass are limits of its interior, in collar
coordinates. -/
theorem IsPass.lc_left_mem_closure (hF : IsCollar γ F) (hℓ : Continuous ℓ) {η : ℝ} (hη : η ≤ 1)
    {a b : ℝ} (h : IsPass F η ℓ a b) :
    lc F ℓ a ∈ closure (lc F ℓ '' Ioo a b) ∧ lc F ℓ b ∈ closure (lc F ℓ '' Ioo a b) := by
  have hc := h.continuousOn_lc hF hℓ hη
  constructor
  · refine ContinuousWithinAt.mem_closure_image ((hc a ⟨le_rfl, h.1.le⟩).mono
      Ioo_subset_Icc_self) ?_
    rw [closure_Ioo h.1.ne]; exact ⟨le_rfl, h.1.le⟩
  · refine ContinuousWithinAt.mem_closure_image ((hc b ⟨h.1.le, le_rfl⟩).mono
      Ioo_subset_Icc_self) ?_
    rw [closure_Ioo h.1.ne]; exact ⟨h.1.le, le_rfl⟩

theorem IsPass.lc_injOn (hF : IsCollar γ F) (hℓ : Function.Injective ℓ) {η : ℝ} (hη : η ≤ 1)
    {a b : ℝ} (h : IsPass F η ℓ a b) {s t : ℝ} (hs : s ∈ Icc a b) (ht : (ℓ t : Pt) ∈ F '' cRect)
    (e : lc F ℓ s = lc F ℓ t) : s = t := by
  have h1 := (h.lc_box hF hη hs).2
  have h2 := collarCoord_apply ht
  exact hℓ (Subtype.ext (h1.symm.trans (e ▸ h2)))

/-- **N1, the collar preimage of a thin upper pass**: an arc from `(¼, r₂)` to `(¾, s₂)` in
`[¼, ¾] × (0, η₂]`, meeting the two sides only in its end points. -/
theorem thinPass_arc (hF : IsCollar γ F) (hℓ : IsLine ℓ) {η₂ : ℝ} (hη₂ : η₂ ≤ 1) {am bm : ℝ}
    (hP : IsPass F (1 / 2) ℓ am bm) (hthin : PassThin F η₂ ℓ am bm)
    (habove : PassAbove F ℓ am bm) :
    TArc (lc F ℓ am) (lc F ℓ bm) (lc F ℓ '' Icc am bm) ∧
      lc F ℓ '' Icc am bm ⊆ Icc (1 / 4) (3 / 4) ×ˢ Ioc 0 η₂ ∧
      (lc F ℓ am).1 = 1 / 4 ∧ (lc F ℓ bm).1 = 3 / 4 ∧
      lc F ℓ '' Icc am bm ∩ (({1 / 4, 3 / 4} : Set ℝ) ×ˢ Icc 0 η₂) =
        {lc F ℓ am, lc F ℓ bm} := by
  have hη : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hl := hP.lc_left hF hη
  have hr := hP.lc_right hF hη
  have hsub : lc F ℓ '' Icc am bm ⊆ Icc (1 / 4) (3 / 4) ×ˢ Ioc 0 η₂ := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨hb, -⟩ := hP.lc_box hF hη ht
    obtain ⟨z, hz, e⟩ := hthin t ht
    obtain ⟨w, hw, hw0, e'⟩ := habove t ht
    have h1 : lc F ℓ t = z := lc_eq hF (box_sub_cRect hη₂ hz) e.symm
    have h2 : lc F ℓ t = w := lc_eq hF hw e'
    exact ⟨hb.1, h2 ▸ hw0, h1 ▸ hz.2.2⟩
  refine ⟨?_, hsub, hl, hr, ?_⟩
  · refine tarc_of_injOn hP.1 (hP.continuousOn_lc hF hℓ.1 hη) fun s hs t ht e => ?_
    exact hP.lc_injOn hF hℓ.2.1 hη hs (hP.mem_rect hη ht) e
  · apply subset_antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, hx, -⟩
      rcases eq_or_lt_of_le ht.1 with rfl | h1
      · exact Or.inl rfl
      rcases eq_or_lt_of_le ht.2 with rfl | h2
      · exact Or.inr rfl
      have := (hP.lc_int hF hη ⟨h1, h2⟩).1
      rcases hx with hx | hx
      · have h1 : (lc F ℓ t).1 = 1 / 4 := hx
        linarith [this.1]
      · have h1 : (lc F ℓ t).1 = 3 / 4 := hx
        linarith [this.2]
    · rintro _ (rfl | rfl)
      · have := hsub ⟨am, ⟨le_rfl, hP.1.le⟩, rfl⟩
        exact ⟨⟨am, ⟨le_rfl, hP.1.le⟩, rfl⟩, Or.inl hl, this.2.1.le, this.2.2⟩
      · have := hsub ⟨bm, ⟨hP.1.le, le_rfl⟩, rfl⟩
        exact ⟨⟨bm, ⟨hP.1.le, le_rfl⟩, rfl⟩, Or.inr hr, this.2.1.le, this.2.2⟩

/-- The frontier of the region of a thin pass, as given by `rect_domain_aux`. -/
def RegionFrontier (F : ℝ × ℝ → Pt) (ℓ : ℝ → M) (am bm : ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  frontier D = lc F ℓ '' Icc am bm ∪ Icc (1 / 4 : ℝ) (3 / 4) ×ˢ {0} ∪
    ({1 / 4} : Set ℝ) ×ˢ Icc 0 (lc F ℓ am).2 ∪ ({3 / 4} : Set ℝ) ×ˢ Icc 0 (lc F ℓ bm).2

/-- **§4, (R1)**: a pass other than the base pass and `P_m` whose interior meets `D_m` has its
interior in `D_m` and its end points on the two sides of `D_m`, below the end points of `P_m`. -/
theorem region_pass (hF : IsCollar γ F) (hγ : ∀ t : unitInterval, γ t = ℓ t) (hℓ : IsLine ℓ)
    {am bm : ℝ} (hP : IsPass F (1 / 2) ℓ am bm) {D : Set (ℝ × ℝ)} {η₂ : ℝ}
    (hDR : D ⊆ Ioo (1 / 4) (3 / 4) ×ˢ Ioo 0 η₂) (hDf : RegionFrontier F ℓ am bm D)
    {a b : ℝ} (h : IsPass F (1 / 2) ℓ a b) (hne0 : (a, b) ≠ (1 / 4, 3 / 4))
    (hnem : (a, b) ≠ (am, bm)) {u : ℝ} (hu : u ∈ Ioo a b) (huD : lc F ℓ u ∈ D) :
    (∀ s ∈ Ioo a b, lc F ℓ s ∈ D) ∧ lc F ℓ a ∈ ({1 / 4} : Set ℝ) ×ˢ Ioo 0 (lc F ℓ am).2 ∧
      lc F ℓ b ∈ ({3 / 4} : Set ℝ) ×ˢ Ioo 0 (lc F ℓ bm).2 := by
  have hη : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hab : Icc a b = Icc a b := rfl
  -- (i) the pass misses `P_m`
  have hi : ∀ s ∈ Icc a b, lc F ℓ s ∉ lc F ℓ '' Icc am bm := by
    rintro s hs ⟨t, ht, e⟩
    have := h.lc_injOn hF hℓ.2.1 hη hs (hP.mem_rect hη ht) e.symm
    subst this
    exact hnem (h.eq_of_mem hF hη hP hs ht)
  -- (ii) the pass misses the base arc
  have hii : ∀ s ∈ Icc a b, (lc F ℓ s).2 ≠ 0 := by
    intro s hs e
    obtain ⟨hz, hFe⟩ := h.lc_box hF hη hs
    refine hne0 (h.eq_base_of hF hγ hℓ.2.1 (by norm_num) hη hs (x := (lc F ℓ s).1)
      ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩ ?_)
    rw [← hFe]; congr 1; exact Prod.ext rfl e
  have hl := hP.lc_left hF hη
  have hl' := h.lc_left hF hη
  have hr' := h.lc_right hF hη
  set C := lc F ℓ '' Ioo a b with hC
  have hCc : IsPreconnected C :=
    isPreconnected_Ioo.image _ ((h.continuousOn_lc hF hℓ.1 hη).mono Ioo_subset_Icc_self)
  have hCD : C ⊆ D := by
    refine conn_sub_of_frontier hCc ?_ ⟨_, ⟨u, hu, rfl⟩, huD⟩
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hfr
    have hsI := Ioo_subset_Icc_self hs
    have hint := (h.lc_int hF hη hs).1
    rw [hDf] at hfr
    rcases hfr with ((hfr | ⟨-, hfr⟩) | ⟨hfr, -⟩) | ⟨hfr, -⟩
    · exact hi s hsI hfr
    · exact hii s hsI hfr
    · simp only [mem_singleton_iff] at hfr; linarith [hint.1]
    · simp only [mem_singleton_iff] at hfr; linarith [hint.2]
  refine ⟨fun s hs => hCD ⟨s, hs, rfl⟩, ?_, ?_⟩
  · have hcl := closure_mono hCD (h.lc_left_mem_closure hF hℓ.1 hη).1
    rw [closure_eq_self_union_frontier, hDf] at hcl
    have haI : a ∈ Icc a b := ⟨le_rfl, h.1.le⟩
    rcases hcl with hD | ((((hfr | ⟨-, hfr⟩) | ⟨hx, hy⟩) | ⟨hx, -⟩))
    · have := (hDR hD).1.1; rw [hl'] at this; exact absurd this (lt_irrefl _)
    · exact absurd hfr (hi a haI)
    · exact absurd hfr (hii a haI)
    · refine ⟨hx, lt_of_le_of_ne hy.1 (Ne.symm (hii a haI)), lt_of_le_of_ne hy.2 fun e => ?_⟩
      refine hi a haI ⟨am, ⟨le_rfl, hP.1.le⟩, ?_⟩
      exact Prod.ext (by rw [hl, hl']) e.symm
    · simp only [mem_singleton_iff] at hx; rw [hl'] at hx; norm_num at hx
  · have hcl := closure_mono hCD (h.lc_left_mem_closure hF hℓ.1 hη).2
    rw [closure_eq_self_union_frontier, hDf] at hcl
    have hbI : b ∈ Icc a b := ⟨h.1.le, le_rfl⟩
    have hrm := hP.lc_right hF hη
    rcases hcl with hD | ((((hfr | ⟨-, hfr⟩) | ⟨hx, -⟩) | ⟨hx, hy⟩))
    · have := (hDR hD).1.2; rw [hr'] at this; exact absurd this (lt_irrefl _)
    · exact absurd hfr (hi b hbI)
    · exact absurd hfr (hii b hbI)
    · simp only [mem_singleton_iff] at hx; rw [hr'] at hx; norm_num at hx
    · refine ⟨hx, lt_of_le_of_ne hy.1 (Ne.symm (hii b hbI)), lt_of_le_of_ne hy.2 fun e => ?_⟩
      refine hi b hbI ⟨bm, ⟨hP.1.le, le_rfl⟩, ?_⟩
      exact Prod.ext (by rw [hrm, hr']) e.symm

/-- **§4, (R1).3**: such a pass is thin and lies above the base arc. -/
theorem region_thin_above (hF : IsCollar γ F) {am bm : ℝ} {D : Set (ℝ × ℝ)} {η₂ : ℝ}
    (hDR : D ⊆ Ioo (1 / 4) (3 / 4) ×ˢ Ioo 0 η₂) (hr2 : (lc F ℓ am).2 ≤ η₂)
    (hs2 : (lc F ℓ bm).2 ≤ η₂) {a b : ℝ} (h : IsPass F (1 / 2) ℓ a b)
    (hR : (∀ s ∈ Ioo a b, lc F ℓ s ∈ D) ∧ lc F ℓ a ∈ ({1 / 4} : Set ℝ) ×ˢ Ioo 0 (lc F ℓ am).2 ∧
      lc F ℓ b ∈ ({3 / 4} : Set ℝ) ×ˢ Ioo 0 (lc F ℓ bm).2) :
    PassThin F η₂ ℓ a b ∧ PassAbove F ℓ a b := by
  have hη : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have key : ∀ s ∈ Icc a b, lc F ℓ s ∈ Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Ioc 0 η₂ := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | h1
    · obtain ⟨hx, hy⟩ := hR.2.1
      simp only [mem_singleton_iff] at hx
      exact ⟨⟨by rw [hx], by rw [hx]; norm_num⟩, hy.1, by linarith [hy.2]⟩
    rcases eq_or_lt_of_le hs.2 with rfl | h2
    · obtain ⟨hx, hy⟩ := hR.2.2
      simp only [mem_singleton_iff] at hx
      exact ⟨⟨by rw [hx]; norm_num, by rw [hx]⟩, hy.1, by linarith [hy.2]⟩
    have := hDR (hR.1 s ⟨h1, h2⟩)
    exact ⟨⟨this.1.1.le, this.1.2.le⟩, this.2.1, this.2.2.le⟩
  constructor
  · intro s hs
    have := key s hs
    exact ⟨lc F ℓ s, ⟨this.1, by linarith [this.2.1, this.2.2], this.2.2⟩, (h.lc_box hF hη hs).2⟩
  · intro s hs
    have := key s hs
    exact ⟨lc F ℓ s, box_sub_cRect hη (h.lc_box hF hη hs).1, this.2.1,
      (h.lc_box hF hη hs).2.symm⟩

/-- **§4, (R2)**: under the conclusion of (R1), the interior of the pass meets every low vertical
segment `{c} × (0, w_m(c))` (`rect_domain_crosscut`). -/
theorem region_cross (hF : IsCollar γ F) (hℓ : IsLine ℓ) {am bm : ℝ} {D : Set (ℝ × ℝ)} {η₂ : ℝ}
    (hI : TArc (lc F ℓ am) (lc F ℓ bm) (lc F ℓ '' Icc am bm))
    (hIR : lc F ℓ '' Icc am bm ⊆ Icc (1 / 4) (3 / 4) ×ˢ Ioc 0 η₂) (hr : (lc F ℓ am).1 = 1 / 4)
    (hs : (lc F ℓ bm).1 = 3 / 4)
    (hIs : lc F ℓ '' Icc am bm ∩ (({1 / 4, 3 / 4} : Set ℝ) ×ˢ Icc 0 η₂) =
        {lc F ℓ am, lc F ℓ bm})
    (hDo : IsOpen D) (hDR : D ⊆ Ioo (1 / 4) (3 / 4) ×ˢ Ioo 0 η₂)
    (hDf : RegionFrontier F ℓ am bm D) {a b : ℝ} (h : IsPass F (1 / 2) ℓ a b)
    (hR : (∀ s ∈ Ioo a b, lc F ℓ s ∈ D) ∧ lc F ℓ a ∈ ({1 / 4} : Set ℝ) ×ˢ Ioo 0 (lc F ℓ am).2 ∧
      lc F ℓ b ∈ ({3 / 4} : Set ℝ) ×ˢ Ioo 0 (lc F ℓ bm).2)
    {c w : ℝ} (hc : c ∈ Ioo (1 / 4 : ℝ) (3 / 4)) (hw : 0 < w)
    (hwI : ((c, w) : ℝ × ℝ) ∈ lc F ℓ '' Icc am bm)
    (hseg : Disjoint (({c} : Set ℝ) ×ˢ Ioo 0 w) (lc F ℓ '' Icc am bm)) :
    ∃ s ∈ Ioo a b, lc F ℓ s ∈ ({c} : Set ℝ) ×ˢ Ioo 0 w := by
  by_contra hno
  push_neg at hno
  have hη : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hcl := h.lc_left_mem_closure hF hℓ.1 hη
  refine rect_domain_crosscut (by norm_num : (1 / 4 : ℝ) < 3 / 4) hI hIR hr hs hIs hDo hDR hDf hc
    hw hwI hseg (S := lc F ℓ '' Ioo a b)
    (isPreconnected_Ioo.image _ ((h.continuousOn_lc hF hℓ.1 hη).mono Ioo_subset_Icc_self))
    ?_ hR.2.1 hR.2.2 hcl.1 hcl.2
  rintro _ ⟨s, hs', rfl⟩
  exact ⟨hR.1 s hs', hno s hs'⟩

/-- **§5, Lemma A**: no point of `ℓ((¾, a_m))` lies in `R_m` with first coordinate in the middle
band. -/
theorem region_lemmaA (hF : IsCollar γ F) (hγ : ∀ t : unitInterval, γ t = ℓ t) (hℓ : IsLine ℓ)
    {η₂ : ℝ} (hη₂ : η₂ ≤ 1) (hFB : FBProp F η₂ ℓ) {am bm : ℝ} (hP : IsPass F (1 / 2) ℓ am bm)
    {D : Set (ℝ × ℝ)} (hDR : D ⊆ Ioo (1 / 4) (3 / 4) ×ˢ Ioo 0 η₂)
    (hDf : RegionFrontier F ℓ am bm D) (hr2 : (lc F ℓ am).2 ≤ η₂) (hs2 : (lc F ℓ bm).2 ≤ η₂)
    (hH : ∀ a b, IsPass F (1 / 2) ℓ a b → PassThin F η₂ ℓ a b → PassAbove F ℓ a b → 3 / 4 < a →
      am ≤ a)
    {v : ℝ} (hv : v ∈ Ioo (3 / 4) am) {z : ℝ × ℝ} (hzD : z ∈ D)
    (hz1 : z.1 ∈ Icc (9 / 32 : ℝ) (23 / 32)) (e : (ℓ v : Pt) = F z) : False := by
  have hη : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hzR := hDR hzD
  obtain ⟨a, b, h, -, hvab⟩ := hFB v ⟨z, ⟨hz1, by linarith [hzR.2.1, hzR.2.2], hzR.2.2.le⟩, e.symm⟩
  have hlc : lc F ℓ v = z := lc_eq hF ⟨⟨by linarith [hzR.1.1], by linarith [hzR.1.2]⟩,
    by linarith [hzR.2.1], by linarith [hzR.2.2]⟩ e
  have hne0 : (a, b) ≠ (1 / 4, 3 / 4) := fun e' => by
    simp only [Prod.mk.injEq] at e'
    rw [e'.2] at hvab; linarith [hvab.2, hv.1]
  have hnem : (a, b) ≠ (am, bm) := fun e' => by
    simp only [Prod.mk.injEq] at e'
    rw [e'.1] at hvab; linarith [hvab.1, hv.2]
  have hR := region_pass hF hγ hℓ hP hDR hDf h hne0 hnem hvab (hlc ▸ hzD)
  obtain ⟨hthin, habove⟩ := region_thin_above hF hDR hr2 hs2 h hR
  have h34 : 3 / 4 < a := h.lt_of_mem hF hη (isPass_base hF hγ (by norm_num))
    (Ioo_subset_Icc_self hvab) hv.1
  have := hH a b h hthin habove h34
  linarith [hvab.1, hv.2]

end Region

end HPC.Hagopian
