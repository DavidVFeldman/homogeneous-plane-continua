import HPC.Jones.Jones75Region

/-!
# Jones 1975 II (batch 190), part 4: the trapping lemma

Commission 190 §5. The Jordan curve `J = σ ∪ ℓ[½, t_m]` (Step 2), the two sides `W_L ∋ T_L` and
`W_R ∋ T_R` (Steps 3–5, with N3 = `two_sides`), packaged as `trap_jordan`; then the trap itself
(Step 6, `trap_pass`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **N3, two sides at a point of `J`.** -/
theorem two_sides {J W W' A N : Set Pt} {p : Pt} (hW' : frontier W' = J) (hpJ : p ∈ J)
    (hN : IsOpen N) (hpN : p ∈ N) (hNA : N \ J ⊆ A) (hAW : A ⊆ W) (hWW : Disjoint W W')
    (hW'J : Disjoint W' J) : False := by
  have hp : p ∈ closure W' := frontier_subset_closure (hW' ▸ hpJ)
  obtain ⟨q, hqN, hqW'⟩ := mem_closure_iff.1 hp N hN hpN
  have hqJ : q ∉ J := fun h => Set.disjoint_left.1 hW'J hqW' h
  exact Set.disjoint_left.1 hWW (hAW (hNA ⟨hqN, hqJ⟩)) hqW'

section Trap

variable {M : Set Pt} {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} {ℓ : ℝ → M}

set_option maxHeartbeats 1600000 in
/-- **§5, Steps 2–5**: the Jordan curve `J = σ ∪ ℓ[½, t_m]` and the two components `W_L ⊇ T_L`,
`W_R ⊇ T_R ∪ {z_R}` of its complement, with (J1). -/
theorem trap_jordan (hF : IsCollar γ F) (hγ : ∀ t : unitInterval, γ t = ℓ t) (hℓ : IsLine ℓ)
    {am bm : ℝ} (hP : IsPass F (1 / 2) ℓ am bm) (ham : 3 / 4 < am) {η₂ : ℝ}
    (hIR : lc F ℓ '' Icc am bm ⊆ Icc (1 / 4) (3 / 4) ×ˢ Ioc 0 η₂) (hη₂ : η₂ < 1 / 2)
    {D : Set (ℝ × ℝ)} (hDR : D ⊆ Ioo (1 / 4) (3 / 4) ×ˢ Ioo 0 η₂)
    (hA : ∀ v ∈ Ioo (3 / 4) am, ∀ z ∈ D, z.1 ∈ Icc (9 / 32 : ℝ) (23 / 32) →
      (ℓ v : Pt) = F z → False)
    {hm : ℝ} (hm0 : 0 < hm) (hmI : ∀ z ∈ lc F ℓ '' Icc am bm, hm < z.2)
    (hlow : Ioo (1 / 4 : ℝ) (3 / 4) ×ˢ Ioo 0 hm ⊆ D)
    {wL ym wR : ℝ} (hwLI : ((3 / 8, wL) : ℝ × ℝ) ∈ lc F ℓ '' Icc am bm)
    (hwLs : Disjoint (({3 / 8} : Set ℝ) ×ˢ Ioo 0 wL) (lc F ℓ '' Icc am bm))
    (hwLD : ({3 / 8} : Set ℝ) ×ˢ Ioo 0 wL ⊆ D)
    (hymI : ((1 / 2, ym) : ℝ × ℝ) ∈ lc F ℓ '' Icc am bm)
    (hyms : Disjoint (({1 / 2} : Set ℝ) ×ˢ Ioo 0 ym) (lc F ℓ '' Icc am bm))
    (hymD : ({1 / 2} : Set ℝ) ×ˢ Ioo 0 ym ⊆ D)
    (hwRI : ((5 / 8, wR) : ℝ × ℝ) ∈ lc F ℓ '' Icc am bm)
    (hwRs : Disjoint (({5 / 8} : Set ℝ) ×ˢ Ioo 0 wR) (lc F ℓ '' Icc am bm))
    (hwRD : ({5 / 8} : Set ℝ) ×ˢ Ioo 0 wR ⊆ D)
    {tm tR : ℝ} (htm : tm ∈ Icc am bm) (htme : lc F ℓ tm = (1 / 2, ym))
    (htR : tR ∈ Icc am bm) (htRe : lc F ℓ tR = (5 / 8, wR)) (htmR : tm < tR) :
    ∃ J WL WR : Set Pt, IsClosed J ∧ IsOpen WL ∧ IsOpen WR ∧ Disjoint WL WR ∧
      WL ∪ WR = Jᶜ ∧
      (∀ v, tm < v → (ℓ v : Pt) ∈ J → ∃ y ∈ Ioo 0 ym, (ℓ v : Pt) = F (1 / 2, y)) ∧
      (∀ y ∈ Ioo 0 wL, F (3 / 8, y) ∈ WL) ∧ (∀ y ∈ Ioo 0 wR, F (5 / 8, y) ∈ WR) ∧
      (ℓ tR : Pt) ∈ WR := by
  have hη : (1 / 2 : ℝ) ≤ 1 := by norm_num
  set Im := lc F ℓ '' Icc am bm with hIm
  set L : ℝ → Pt := fun t => (ℓ t : Pt) with hL
  have hLc : Continuous L := continuous_subtype_val.comp hℓ.1
  have hLi : Function.Injective L := fun s t e => hℓ.2.1 (Subtype.ext e)
  have hbase : ∀ t ∈ Icc (0 : ℝ) 1, L t = F (t, 0) := fun t ht =>
    hF.base (ℓ := L) (fun t => hγ t) ht
  have hym : ym ≤ η₂ := (hIR hymI).2.2
  have hym0 : 0 < ym := (hIR hymI).2.1
  have hmym : hm < ym := hmI _ hymI
  have hmwL : hm < wL := hmI _ hwLI
  have hmwR : hm < wR := hmI _ hwRI
  have hwL0 : 0 < wL := (hIR hwLI).2.1
  have hwR0 : 0 < wR := (hIR hwRI).2.1
  have hDc : ∀ z ∈ D, z ∈ cRect := fun z hz => by
    have := hDR hz
    exact ⟨⟨by linarith [this.1.1], by linarith [this.1.2]⟩, by linarith [this.2.1],
      by linarith [this.2.2]⟩
  have hvc : ∀ y ∈ Icc (0 : ℝ) ym, ((1 / 2 : ℝ), y) ∈ cRect := fun y hy =>
    ⟨⟨by norm_num, by norm_num⟩, by linarith [hy.1], by linarith [hy.2]⟩
  have hLtm : L tm = F (1 / 2, ym) := by
    rw [← htme]; exact (hP.lc_box hF hη htm).2.symm
  have hLtR : L tR = F (5 / 8, wR) := by
    rw [← htRe]; exact (hP.lc_box hF hη htR).2.symm
  have hLo : L (1 / 2) = F (1 / 2, 0) := hbase _ ⟨by norm_num, by norm_num⟩
  have htm34 : 3 / 4 < tm := by linarith [htm.1]
  -- the two arcs
  set σ : Set Pt := (fun y => F (1 / 2, y)) '' Icc 0 ym with hσ
  set Λ : Set Pt := L '' Icc (1 / 2) tm with hΛ
  set J : Set Pt := Λ ∪ σ with hJ
  have hσarc : TArc (L (1 / 2)) (L tm) σ := by
    rw [hLo, hLtm]
    refine tarc_of_injOn (f := fun y : ℝ => F (1 / 2, y)) hym0 ?_ ?_
    · exact hF.contOn.comp (by fun_prop) fun y hy => hvc y hy
    · intro y hy y' hy' e
      have := hF.injOn (hvc y hy) (hvc y' hy') e
      exact congrArg Prod.snd this
  have hΛarc : TArc (L (1 / 2)) (L tm) Λ :=
    tarc_of_injOn (by linarith) hLc.continuousOn (hLi.injOn)
  -- points of `D` off `P_m` and off `X = ½`, in the column, are off `J`
  have hcol : ∀ z ∈ D, z ∉ Im → z.1 ∈ Icc (3 / 8 : ℝ) (5 / 8) → z.1 ≠ 1 / 2 → F z ∉ J := by
    intro z hzD hzI hz1 hz2 hzJ
    have hzc := hDc z hzD
    rcases hzJ with ⟨v, hv, e⟩ | ⟨y, hy, e⟩
    · rcases le_or_gt v (3 / 4) with hv1 | hv1
      · have := hF.injOn hzc ⟨⟨by linarith [hv.1], by linarith⟩, by norm_num, by norm_num⟩
          (e.symm.trans (hbase v ⟨by linarith [hv.1], by linarith⟩))
        have := (hDR hzD).2.1
        rw [‹z = (v, 0)›] at this
        exact lt_irrefl _ this
      rcases lt_or_ge v am with hv2 | hv2
      · exact hA v ⟨hv1, hv2⟩ z hzD ⟨by linarith [hz1.1], by linarith [hz1.2]⟩ e
      · exact hzI ⟨v, ⟨hv2, hv.2.trans htm.2⟩, lc_eq hF hzc e⟩
    · simp only at e
      exact hz2 (congrArg Prod.fst (hF.injOn (hvc y hy) hzc e)).symm
  -- `σ ∩ Λ = {o, x_m}`
  have hint : Λ ∩ σ = {L (1 / 2), L tm} := by
    apply subset_antisymm
    · rintro p ⟨⟨v, hv, rfl⟩, ⟨y, hy, e⟩⟩
      simp only at e
      rcases le_or_gt v (3 / 4) with hv1 | hv1
      · have := hF.injOn (hvc y hy) ⟨⟨by linarith [hv.1], by linarith⟩, by norm_num, by norm_num⟩
          (e.trans (hbase v ⟨by linarith [hv.1], by linarith⟩))
        simp only [Prod.mk.injEq] at this
        left; rw [← this.1]
      rcases lt_or_ge v am with hv2 | hv2
      · exfalso
        rcases eq_or_lt_of_le hy.1 with rfl | hy1
        · rw [← hLo] at e; have := hLi e; linarith
        rcases eq_or_lt_of_le hy.2 with rfl | hy2
        · rw [← hLtm] at e; have := hLi e; linarith [htm.1]
        exact hA v ⟨hv1, hv2⟩ (1 / 2, y) (hymD ⟨rfl, hy1, hy2⟩) ⟨by norm_num, by norm_num⟩ e.symm
      · right
        have hlcv : lc F ℓ v = (1 / 2, y) := lc_eq hF (hvc y hy) e.symm
        have hvI : ((1 / 2 : ℝ), y) ∈ Im := hlcv ▸ ⟨v, ⟨hv2, hv.2.trans htm.2⟩, rfl⟩
        have hy0 : 0 < y := (hIR hvI).2.1
        rcases eq_or_lt_of_le hy.2 with rfl | hy2
        · show L v = L tm; rw [hLtm]; exact e.symm
        · exact absurd hvI (Set.disjoint_left.1 hyms ⟨rfl, hy0, hy2⟩)
    · rintro p (rfl | rfl)
      · exact ⟨⟨1 / 2, ⟨le_rfl, by linarith⟩, rfl⟩, ⟨0, ⟨le_rfl, hym0.le⟩, hLo.symm⟩⟩
      · exact ⟨⟨tm, ⟨by linarith, le_rfl⟩, rfl⟩, ⟨ym, ⟨hym0.le, le_rfl⟩, hLtm.symm⟩⟩
  have hTS : TSCC J := ⟨L (1 / 2), L tm, Λ, σ, hΛarc, hσarc, hint, rfl⟩
  obtain ⟨Wi, Wo, hWio, -, hWoo, -, hWd, hWu, -, -, hWif, hWof⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hTS)
  have hJc : IsClosed J := hWif ▸ isClosed_frontier
  -- (J1)
  have hJ1 : ∀ v, tm < v → L v ∈ J → ∃ y ∈ Ioo 0 ym, L v = F (1 / 2, y) := by
    rintro v hv (⟨v', hv', e⟩ | ⟨y, hy, e⟩)
    · have := hLi e; linarith [hv'.2]
    · simp only at e
      refine ⟨y, ⟨lt_of_le_of_ne hy.1 ?_, lt_of_le_of_ne hy.2 ?_⟩, e.symm⟩
      · rintro rfl; rw [← hLo] at e; have := hLi e; linarith
      · rintro rfl; rw [← hLtm] at e; have := hLi e; linarith
  -- the two connected sets
  set CLc : Set (ℝ × ℝ) := Ico (3 / 8 : ℝ) (1 / 2) ×ˢ Ioo 0 hm ∪ ({3 / 8} : Set ℝ) ×ˢ Ioo 0 wL
    with hCLc
  set CRc : Set (ℝ × ℝ) := Ioc (1 / 2 : ℝ) (5 / 8) ×ˢ Ioo 0 hm ∪ ({5 / 8} : Set ℝ) ×ˢ Ioo 0 wR
    with hCRc
  have hCLD : CLc ⊆ D := by
    rintro z (⟨h1, h2⟩ | hz)
    · exact hlow ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, h2⟩
    · exact hwLD hz
  have hCRD : CRc ⊆ D := by
    rintro z (⟨h1, h2⟩ | hz)
    · exact hlow ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, h2⟩
    · exact hwRD hz
  have hCLp : IsPreconnected (F '' CLc) := by
    refine IsPreconnected.image ?_ _ (hF.contOn.mono fun z hz => hDc z (hCLD hz))
    refine IsPreconnected.union ((3 / 8 : ℝ), hm / 2) ⟨⟨le_rfl, by norm_num⟩, half_pos hm0,
      by linarith⟩ ⟨rfl, half_pos hm0, by linarith⟩
      ((convex_Ico _ _).prod (convex_Ioo _ _)).isPreconnected
      ((convex_singleton _).prod (convex_Ioo _ _)).isPreconnected
  have hCRp : IsPreconnected (F '' CRc) := by
    refine IsPreconnected.image ?_ _ (hF.contOn.mono fun z hz => hDc z (hCRD hz))
    refine IsPreconnected.union ((5 / 8 : ℝ), hm / 2) ⟨⟨by norm_num, le_rfl⟩, half_pos hm0,
      by linarith⟩ ⟨rfl, half_pos hm0, by linarith⟩
      ((convex_Ioc _ _).prod (convex_Ioo _ _)).isPreconnected
      ((convex_singleton _).prod (convex_Ioo _ _)).isPreconnected
  have hCLJ : F '' CLc ⊆ Jᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    refine hcol z (hCLD hz) ?_ ?_ ?_
    · rcases hz with ⟨-, h2⟩ | ⟨h1, h2⟩
      · intro hzI; have := hmI z hzI; linarith [h2.2]
      · intro hzI; exact Set.disjoint_left.1 hwLs ⟨h1, h2⟩ hzI
    · rcases hz with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨h1.1, by linarith [h1.2]⟩
      · simp only [mem_singleton_iff] at h1; rw [h1]; norm_num
    · rcases hz with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1.2.ne
      · simp only [mem_singleton_iff] at h1; rw [h1]; norm_num
  have hCRJ : F '' CRc ⊆ Jᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    refine hcol z (hCRD hz) ?_ ?_ ?_
    · rcases hz with ⟨-, h2⟩ | ⟨h1, h2⟩
      · intro hzI; have := hmI z hzI; linarith [h2.2]
      · intro hzI; exact Set.disjoint_left.1 hwRs ⟨h1, h2⟩ hzI
    · rcases hz with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨by linarith [h1.1], h1.2⟩
      · simp only [mem_singleton_iff] at h1; rw [h1]; norm_num
    · rcases hz with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1.1.ne'
      · simp only [mem_singleton_iff] at h1; rw [h1]; norm_num
  -- N3: the two sets are on different sides
  set N : Set Pt := F '' (Ioo (3 / 8 : ℝ) (5 / 8) ×ˢ Ioo 0 hm) with hN
  have hm1 : hm < 1 := by linarith
  have hNo : IsOpen N := isOpen_collar_image hF ((isOpen_Ioo).prod isOpen_Ioo)
    (fun z hz => ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1],
      by linarith [hz.2.2]⟩)
  have hpJ : F (1 / 2, hm / 2) ∈ J :=
    Or.inr ⟨hm / 2, ⟨(half_pos hm0).le, by linarith⟩, rfl⟩
  have hpN : F (1 / 2, hm / 2) ∈ N :=
    ⟨(1 / 2, hm / 2), ⟨⟨by norm_num, by norm_num⟩, half_pos hm0, by linarith⟩, rfl⟩
  have hNA : N \ J ⊆ F '' CLc ∪ F '' CRc := by
    rintro _ ⟨⟨z, ⟨hz1, hz2⟩, rfl⟩, hzJ⟩
    rcases lt_trichotomy z.1 (1 / 2) with h | h | h
    · exact Or.inl ⟨z, Or.inl ⟨⟨hz1.1.le, h⟩, hz2⟩, rfl⟩
    · exfalso
      refine hzJ (Or.inr ⟨z.2, ⟨hz2.1.le, by linarith [hz2.2]⟩, ?_⟩)
      simp only; congr 1; exact Prod.ext h.symm rfl
    · exact Or.inr ⟨z, Or.inl ⟨⟨h, hz1.2.le⟩, hz2⟩, rfl⟩
  have hside : ∀ W W' : Set Pt, IsOpen W → IsOpen W' → Disjoint W W' → W ∪ W' = Jᶜ →
      frontier W' = J → ¬ (F '' CLc ⊆ W ∧ F '' CRc ⊆ W) := by
    rintro W W' - - hd hu hf ⟨h1, h2⟩
    refine two_sides hf hpJ hNo hpN hNA (union_subset h1 h2) hd ?_
    rw [Set.disjoint_right]
    intro q hq hqW'
    have : q ∈ Jᶜ := hu ▸ Or.inr hqW'
    exact this hq
  have hWu' : Wo ∪ Wi = Jᶜ := by rw [union_comm]; exact hWu
  obtain ⟨WL, WR, hWLo, hWRo, hWd', hWu'', hCL, hCR⟩ : ∃ WL WR : Set Pt, IsOpen WL ∧ IsOpen WR ∧
      Disjoint WL WR ∧ WL ∪ WR = Jᶜ ∧ F '' CLc ⊆ WL ∧ F '' CRc ⊆ WR := by
    rcases hCLp.subset_or_subset hWio hWoo hWd (hWu ▸ hCLJ) with hL1 | hL1 <;>
    rcases hCRp.subset_or_subset hWio hWoo hWd (hWu ▸ hCRJ) with hR1 | hR1
    · exact absurd ⟨hL1, hR1⟩ (hside Wi Wo hWio hWoo hWd hWu hWof)
    · exact ⟨Wi, Wo, hWio, hWoo, hWd, hWu, hL1, hR1⟩
    · exact ⟨Wo, Wi, hWoo, hWio, hWd.symm, hWu', hL1, hR1⟩
    · exact absurd ⟨hL1, hR1⟩ (hside Wo Wi hWoo hWio hWd.symm hWu' hWif)
  refine ⟨J, WL, WR, hJc, hWLo, hWRo, hWd', hWu'', hJ1, fun y hy => hCL ⟨(3 / 8, y), Or.inr ⟨rfl, hy⟩, rfl⟩,
    fun y hy => hCR ⟨(5 / 8, y), Or.inr ⟨rfl, hy⟩, rfl⟩, ?_⟩
  -- Step 5: `z_R ∈ W_R`
  have hzJ : L tR ∉ J := by
    intro hJR
    obtain ⟨y, hy, e⟩ := hJ1 tR htmR hJR
    rw [hLtR] at e
    have := congrArg Prod.fst (hF.injOn ⟨⟨by norm_num, by norm_num⟩, by linarith [hwR0],
      by linarith [(hIR hwRI).2.2]⟩ (hvc y ⟨hy.1.le, hy.2.le⟩) e)
    norm_num at this
  have hzW : L tR ∈ WL ∪ WR := hWu''.symm ▸ hzJ
  rcases hzW with hzL | hzR
  · exfalso
    have hcl : L tR ∈ closure (F '' (({5 / 8} : Set ℝ) ×ˢ Ioo 0 wR)) := by
      rw [hLtR]
      refine ContinuousWithinAt.mem_closure_image ?_ ?_
      · exact (hF.contOn _ ⟨⟨by norm_num, by norm_num⟩, by linarith,
          by linarith [(hIR hwRI).2.2]⟩).mono fun z hz => hDc z (hwRD hz)
      · rw [closure_prod_eq, closure_singleton, closure_Ioo hwR0.ne]
        exact ⟨rfl, hwR0.le, le_rfl⟩
    obtain ⟨q, hqL, hqs⟩ := mem_closure_iff.1 hcl WL hWLo hzL
    obtain ⟨z, hz, rfl⟩ := hqs
    exact Set.disjoint_left.1 hWd' hqL (hCR ⟨z, Or.inr hz, rfl⟩)
  · exact hzR

set_option maxHeartbeats 1600000 in
/-- **§5, the trapping lemma** (commission 190 §5). Let `P_m = ℓ[a_m, b_m]` be a thin pass above
the base arc with `a_m > ¾`, and suppose (H): every thin upper pass starting after `¾` starts at or
after `a_m`. Then there is `h > 0` such that no pass starting after `b_m` has an interior point in
`F((3/8, 5/8) × (0, h))` (a part of the low strip of the region `R_m`).
(Shape left to us by the skeleton. (H) is stated through minimality, which is how §6 uses it; the
commission's (H) follows from it by (R1).3, see `region_lemmaA`.) -/
theorem trap_pass (hF : IsCollar γ F) (hγ : ∀ t : unitInterval, γ t = ℓ t) (hℓ : IsLine ℓ)
    {η₂ : ℝ} (hη₂ : 0 < η₂) (hη₂' : η₂ < 1 / 2) (hFB : FBProp F η₂ ℓ) {am bm : ℝ}
    (hP : IsPass F (1 / 2) ℓ am bm) (hthin : PassThin F η₂ ℓ am bm)
    (habove : PassAbove F ℓ am bm) (ham : 3 / 4 < am)
    (hH : ∀ a b, IsPass F (1 / 2) ℓ a b → PassThin F η₂ ℓ a b → PassAbove F ℓ a b → 3 / 4 < a →
      am ≤ a) :
    ∃ h > 0, ∀ a b, IsPass F (1 / 2) ℓ a b → bm < a → ∀ u ∈ Ioo a b,
      (ℓ u : Pt) ∉ F '' (Ioo (3 / 8) (5 / 8) ×ˢ Ioo 0 h) := by
  have hη : (1 / 2 : ℝ) ≤ 1 := by norm_num
  obtain ⟨hI, hIR, hr, hs, hIs⟩ := thinPass_arc hF hℓ (by linarith) hP hthin habove
  set Im := lc F ℓ '' Icc am bm with hIm
  obtain ⟨D, hDo, -, -, hDR, hDf⟩ :=
    rect_domain_aux (by norm_num : (1 / 4 : ℝ) < 3 / 4) hη₂ hI hIR hr hs hIs
  have hDf' : RegionFrontier F ℓ am bm D := hDf
  have hr2 : (lc F ℓ am).2 ≤ η₂ := (hIR ⟨am, ⟨le_rfl, hP.1.le⟩, rfl⟩).2.2
  have hs2 : (lc F ℓ bm).2 ≤ η₂ := (hIR ⟨bm, ⟨hP.1.le, le_rfl⟩, rfl⟩).2.2
  obtain ⟨hm, hm0, -, hmI⟩ := exists_height_below hI.isCompact fun z hz => (hIR hz).2.1
  have hlow := rect_domain_low (r := lc F ℓ am) (s := lc F ℓ bm)
    (by norm_num : (1 / 4 : ℝ) < 3 / 4) hDR hDf hm0 fun z hz => (hmI z hz).le
  have hseg := fun x₀ (hx₀ : x₀ ∈ Ioo (1 / 4 : ℝ) (3 / 4)) => tarc_lowest hI hIR hr hs hx₀
  obtain ⟨wL, hwL0, hwLI, hwLs⟩ := hseg (3 / 8) ⟨by norm_num, by norm_num⟩
  obtain ⟨ym, hym0, hymI, hyms⟩ := hseg (1 / 2) ⟨by norm_num, by norm_num⟩
  obtain ⟨wR, hwR0, hwRI, hwRs⟩ := hseg (5 / 8) ⟨by norm_num, by norm_num⟩
  have hsegD := fun x₀ (hx₀ : x₀ ∈ Ioo (1 / 4 : ℝ) (3 / 4)) w (hw : 0 < w)
    (hd : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w) Im) =>
    seg_subset_rect_domain (by norm_num : (1 / 4 : ℝ) < 3 / 4) hI hIR hDo hDR hDf hx₀ hw hd
  have hA : ∀ v ∈ Ioo (3 / 4) am, ∀ z ∈ D, z.1 ∈ Icc (9 / 32 : ℝ) (23 / 32) →
      (ℓ v : Pt) = F z → False := fun v hv z hz hz1 e =>
    region_lemmaA hF hγ hℓ (by linarith) hFB hP hDR hDf' hr2 hs2 hH hv hz hz1 e
  have hym : ym ≤ η₂ := (hIR hymI).2.2
  obtain ⟨tm, htm, htme⟩ := id hymI
  obtain ⟨tR, htR, htRe⟩ := id hwRI
  have hFm : ∀ s ∈ Icc am bm, F (lc F ℓ s) = ℓ s := fun s hs => (hP.lc_box hF hη hs).2
  have hmon : PassMon F (1 / 32) ℓ am bm := hFB.passMon hF hP htm
    ⟨(1 / 2, ym), ⟨⟨by norm_num, by norm_num⟩, by linarith, hym⟩, by rw [← htme]; exact hFm tm htm⟩
  have hcm : (1 / 2, ym) ∈ cRect := ⟨⟨by norm_num, by norm_num⟩, by linarith, by linarith⟩
  have hcR : (5 / 8, wR) ∈ cRect := ⟨⟨by norm_num, by norm_num⟩, by linarith,
    by linarith [(hIR hwRI).2.2]⟩
  have htmR : tm < tR := by
    rcases lt_trichotomy tm tR with h | h | h
    · exact h
    · subst h; rw [htme] at htRe; norm_num [Prod.ext_iff] at htRe
    · exfalso
      have := hmon tR tm htR.1 h htm.2 (5 / 8, wR) (1 / 2, ym) hcR hcm
        (by rw [← htRe]; exact (hFm tR htR).symm) (by rw [← htme]; exact (hFm tm htm).symm)
      norm_num at this
  obtain ⟨J, WL, WR, hJc, hWLo, hWRo, hWd, hWu, hJ1, hWL, hWR, hzR⟩ :=
    trap_jordan hF hγ hℓ hP ham hIR hη₂' hDR hA hm0 hmI hlow hwLI hwLs
      (hsegD (3 / 8) ⟨by norm_num, by norm_num⟩ wL hwL0 hwLs) hymI hyms
      (hsegD (1 / 2) ⟨by norm_num, by norm_num⟩ ym hym0 hyms) hwRI hwRs
      (hsegD (5 / 8) ⟨by norm_num, by norm_num⟩ wR hwR0 hwRs) htm htme htR htRe htmR
  set L : ℝ → Pt := fun t => (ℓ t : Pt) with hL
  have hLc : Continuous L := continuous_subtype_val.comp hℓ.1
  -- Step 6
  refine ⟨hm, hm0, fun a b h hba u hu huR => ?_⟩
  have hFl : ∀ s ∈ Icc a b, F (lc F ℓ s) = ℓ s := fun s hs => (h.lc_box hF hη hs).2
  have hcl : ∀ s ∈ Icc a b, lc F ℓ s ∈ cRect := fun s hs =>
    box_sub_cRect hη (h.lc_box hF hη hs).1
  obtain ⟨z, hz, e⟩ := huR
  have hzD : z ∈ D := hlow ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hlcu : lc F ℓ u = z := lc_eq hF ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
    by linarith [hz.2.1], by linarith [hz.2.2, (hIR hymI).2.2, hmI _ hymI]⟩ e.symm
  have hne0 : (a, b) ≠ (1 / 4, 3 / 4) := fun e' => by
    simp only [Prod.mk.injEq] at e'; linarith [hP.1, e'.1]
  have hnem : (a, b) ≠ (am, bm) := fun e' => by
    simp only [Prod.mk.injEq] at e'; linarith [hP.1]
  have hR := region_pass hF hγ hℓ hP hDR hDf' h hne0 hnem hu (hlcu ▸ hzD)
  obtain ⟨vL, hvL, hvLe⟩ := region_cross hF hℓ hI hIR hr hs hIs hDo hDR hDf' h hR
    (c := 3 / 8) ⟨by norm_num, by norm_num⟩ hwL0 hwLI hwLs
  have hvLI : vL ∈ Icc a b := Ioo_subset_Icc_self hvL
  have hvLx : (lc F ℓ vL).1 = 3 / 8 := hvLe.1
  have hLvL : L vL ∈ WL := by
    have := hWL (lc F ℓ vL).2 hvLe.2
    rwa [show F (3 / 8, (lc F ℓ vL).2) = L vL from
      (congrArg F (Prod.ext hvLx.symm rfl : ((3 / 8 : ℝ), (lc F ℓ vL).2) = lc F ℓ vL)).trans
        (hFl vL hvLI)] at this
  have hLvLJ : L vL ∉ J := by
    have : L vL ∈ WL ∪ WR := Or.inl hLvL
    rw [hWu] at this; exact this
  have htRvL : tR < vL := by linarith [htR.2, hvL.1]
  set Z := {v ∈ Icc tR vL | L v ∈ J} with hZ
  have hZc : IsClosed Z := hLc.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hJc
  have hZne : Z.Nonempty := by
    by_contra hZe
    have hsub : L '' Icc tR vL ⊆ WL ∪ WR := by
      rintro _ ⟨v, hv, rfl⟩
      rw [hWu]; intro hvJ
      exact hZe ⟨v, hv, hvJ⟩
    rcases (isPreconnected_Icc.image _ hLc.continuousOn).subset_or_subset hWLo hWRo hWd hsub
      with h1 | h1
    · exact Set.disjoint_left.1 hWd (h1 ⟨tR, ⟨le_rfl, htRvL.le⟩, rfl⟩) hzR
    · exact Set.disjoint_left.1 hWd hLvL (h1 ⟨vL, ⟨htRvL.le, le_rfl⟩, rfl⟩)
  have hZb : BddAbove Z := ⟨vL, fun v hv => hv.1.2⟩
  set ss := sSup Z with hss
  have hssZ : ss ∈ Z := hZc.csSup_mem hZne hZb
  have hssvL : ss < vL := lt_of_le_of_ne hssZ.1.2 fun e' => hLvLJ (e' ▸ hssZ.2)
  have hafter : ∀ v, ss < v → v ≤ vL → L v ∉ J := fun v hv hvL' hvJ => by
    have := le_csSup hZb ⟨⟨by linarith [hssZ.1.1], hvL'⟩, hvJ⟩
    linarith
  have hG : L '' Ioc ss vL ⊆ WL := by
    have hsub : L '' Ioc ss vL ⊆ WL ∪ WR := by
      rintro _ ⟨v, hv, rfl⟩; rw [hWu]; exact hafter v hv.1 hv.2
    rcases (isPreconnected_Ioc.image _ hLc.continuousOn).subset_or_subset hWLo hWRo hWd hsub
      with h1 | h1
    · exact h1
    · exact absurd (h1 ⟨vL, ⟨hssvL, le_rfl⟩, rfl⟩) (Set.disjoint_left.1 hWd hLvL)
  obtain ⟨ys, hys, hes⟩ := hJ1 ss (by linarith [hssZ.1.1]) hssZ.2
  have hcs : ((1 / 2 : ℝ), ys) ∈ cRect := ⟨⟨by norm_num, by norm_num⟩, by linarith [hys.1],
    by linarith [hys.2]⟩
  have hlcs : lc F ℓ ss = (1 / 2, ys) := lc_eq hF hcs hes
  have hssb : bm < ss := by
    by_contra hle
    push_neg at hle
    have : ((1 / 2 : ℝ), ys) ∈ Im := hlcs ▸ ⟨ss, ⟨by linarith [htR.1, hssZ.1.1], hle⟩, rfl⟩
    exact Set.disjoint_left.1 hyms
      (show ((1 / 2 : ℝ), ys) ∈ ({1 / 2} : Set ℝ) ×ˢ Ioo 0 ym from ⟨rfl, hys⟩) this
  obtain ⟨a', b', h', hmon', hss'⟩ := hFB ss
    ⟨(1 / 2, ys), ⟨⟨by norm_num, by norm_num⟩, by linarith [hys.1], by linarith [hys.2]⟩, hes.symm⟩
  have hssD : lc F ℓ ss ∈ D := by
    rw [hlcs]; exact hsegD (1 / 2) ⟨by norm_num, by norm_num⟩ ym hym0 hyms ⟨rfl, hys⟩
  have hne0' : (a', b') ≠ (1 / 4, 3 / 4) := fun e' => by
    simp only [Prod.mk.injEq] at e'; rw [e'.2] at hss'; linarith [hss'.2, hP.1]
  have hnem' : (a', b') ≠ (am, bm) := fun e' => by
    simp only [Prod.mk.injEq] at e'; rw [e'.2] at hss'; linarith [hss'.2]
  have hR' := region_pass hF hγ hℓ hP hDR hDf' h' hne0' hnem' hss' hssD
  have hssa : ss < a := by
    by_contra hle
    push_neg at hle
    have heq := h.eq_of_mem hF hη h' ⟨hle, by linarith [hvL.2]⟩ (Ioo_subset_Icc_self hss')
    simp only [Prod.mk.injEq] at heq
    have := hmon' ss vL hss'.1.le hssvL (by rw [← heq.2]; exact hvL.2.le) (1 / 2, ys)
      (lc F ℓ vL) hcs (hcl vL hvLI) hes (hFl vL hvLI).symm
    rw [hvLx] at this
    norm_num at this
  have hb'a : b' < a := by
    by_contra hle
    push_neg at hle
    have heq := h.eq_of_mem hF hη h' ⟨le_rfl, h.1.le⟩ ⟨by linarith [hss'.1], hle⟩
    simp only [Prod.mk.injEq] at heq
    linarith [hss'.1, heq.1]
  obtain ⟨vR, hvR, hvRe⟩ := region_cross hF hℓ hI hIR hr hs hIs hDo hDR hDf' h' hR'
    (c := 5 / 8) ⟨by norm_num, by norm_num⟩ hwR0 hwRI hwRs
  have hvRI : vR ∈ Icc a' b' := Ioo_subset_Icc_self hvR
  have hvRx : (lc F ℓ vR).1 = 5 / 8 := hvRe.1
  have hFl' : F (lc F ℓ vR) = ℓ vR := (h'.lc_box hF hη hvRI).2
  have hLvR : L vR ∈ WR := by
    have := hWR (lc F ℓ vR).2 hvRe.2
    rwa [show F (5 / 8, (lc F ℓ vR).2) = L vR from
      (congrArg F (Prod.ext hvRx.symm rfl : ((5 / 8 : ℝ), (lc F ℓ vR).2) = lc F ℓ vR)).trans
        hFl'] at this
  have hvRs : ss < vR := by
    rcases lt_trichotomy vR ss with h1 | h1 | h1
    · have := hmon' vR ss hvR.1.le h1 hss'.2.le (lc F ℓ vR) (1 / 2, ys)
        (box_sub_cRect hη (h'.lc_box hF hη hvRI).1) hcs hFl'.symm hes
      rw [hvRx] at this
      norm_num at this
    · rw [h1, hlcs] at hvRx; norm_num at hvRx
    · exact h1
  exact Set.disjoint_left.1 hWd (hG ⟨vR, ⟨hvRs, by linarith [hvR.2, hb'a, hvL.1]⟩, rfl⟩) hLvR

end Trap

end HPC.Hagopian
