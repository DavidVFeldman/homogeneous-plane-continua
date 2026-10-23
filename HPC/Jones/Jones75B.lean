import HPC.Jones.Jones75Trap

/-!
# Batch 190: Jones 1975 II — the planar core; `NoArcIndecHomPlane`; Theorem 1 of 1976

Source: report 189 §6.3, as repaired in commission 190 §2–§6 (the shadow lemma and the flow box
hold only in the middle band; the trap is rebuilt in the column `3/8 ≤ X ≤ 5/8`). Collar
coordinates: `F` a collar (`IsCollar`) of `γ = ℓ|[0,1]`, `F(t, 0) = ℓ(t)`; boxes
`F([¼, ¾] × [−η, η])`; `κ = 1/32`; middle band `[9/32, 23/32]`.

The skeleton of batch 190, split over five files under `HPC/Jones/`:

| skeleton item | here |
|---|---|
| §2 `IsPass`, `PassMon`, `IsPass.disjoint` (P1), `IsPass.finite` (P2) | `Jones75Pass.lean` |
| §2 `IsPass.above_or_below` (P4) | `Jones75Pass.lean` |
| §3 `shadow_pass`, `flow_box`, `exists_late_thin_pass` | `Jones75Shadow.lean` |
| §4 `region_of_thin_pass`: N1 `thinPass_arc`, N2 `tarc_lowest`, N4 `IsPass.lc_left_mem_closure`, (R1) `region_pass`, `region_thin_above`, (R2) `region_cross`, Lemma A `region_lemmaA` | `Jones75Region.lean` |
| §5 `trap_pass` (with N3 `two_sides` and Steps 2–5 `trap_jordan`) | `Jones75Trap.lean` |
| §6 `jones75_noArc`, `hagopian76_theorem1`, corollaries | here |

Shape changes (recorded in the report): (P4) and §4–§5, left as `True` in the skeleton, are stated
as above; `exists_late_thin_pass` takes the extra hypothesis `η ≤ 1` (needed for (P1)); the
hypothesis (H) of the trap is stated through minimality (`trap_pass`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Final

variable {M : Set Pt} {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} {ℓ : ℝ → M}

theorem IsPass.of_flip {η a b : ℝ} (h : IsPass (flipC F) η ℓ a b) : IsPass F η ℓ a b := by
  have := h.flip; rwa [flipC_flipC] at this

theorem PassThin.of_flip {η a b : ℝ} (h : PassThin (flipC F) η ℓ a b) : PassThin F η ℓ a b := by
  have := h.flip; rwa [flipC_flipC] at this

/-- A neighbourhood of `o = F(½, 0)` inside `F((3/8, 5/8) × (−h, h))`. -/
theorem exists_ball_box (hF : IsCollar γ F) {h : ℝ} (hh : 0 < h) :
    ∃ ρ > 0, ∀ p : Pt, dist p (F (1 / 2, 0)) < ρ →
      p ∈ F '' (Ioo (3 / 8 : ℝ) (5 / 8) ×ˢ Ioo (-h) h) := by
  set h' := min h 1 with hh'
  have h'0 : 0 < h' := lt_min hh one_pos
  have hO : IsOpen (F '' (Ioo (3 / 8 : ℝ) (5 / 8) ×ˢ Ioo (-h') h')) :=
    isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo) fun z hz =>
      ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1, min_le_right h 1],
        by linarith [hz.2.2, min_le_right h 1]⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO (F (1 / 2, 0))
    ⟨(1 / 2, 0), ⟨⟨by norm_num, by norm_num⟩, by linarith, h'0⟩, rfl⟩
  refine ⟨ρ, hρ, fun p hp => ?_⟩
  obtain ⟨z, ⟨hz1, hz2⟩, e⟩ := hball (mem_ball.2 hp)
  exact ⟨z, ⟨hz1, by linarith [hz2.1, min_le_left h 1], by linarith [hz2.2, min_le_left h 1]⟩, e⟩

/-- **§6, C2–C5**, once the first thin pass after `¾` lies above the base arc. -/
theorem jones75_final_aux (hF : IsCollar γ F) (hγ : ∀ t : unitInterval, γ t = ℓ t)
    (hℓ : IsLine ℓ) (hrec : ∀ T, ∀ ε > 0, ∃ u ≥ T, dist (ℓ u) (ℓ (1 / 2)) < ε) {η₂ : ℝ}
    (hη₂ : 0 < η₂) (hη₂' : η₂ < 1 / 2) (hFB : FBProp F η₂ ℓ)
    (hS2 : ∃ δ₂ > 0, ∀ u, dist (ℓ u) (ℓ (1 / 2)) < δ₂ →
      ∃ a b, IsPass F (1 / 2) ℓ a b ∧ PassThin F η₂ ℓ a b ∧ u ∈ Ioo a b)
    {a₁ b₁ : ℝ} (hP₁ : IsPass F (1 / 2) ℓ a₁ b₁) (hthin₁ : PassThin F η₂ ℓ a₁ b₁)
    (ha₁ : 3 / 4 < a₁)
    (hfirst : ∀ a b, IsPass F (1 / 2) ℓ a b → PassThin F η₂ ℓ a b → 3 / 4 < a → a₁ ≤ a)
    (habove₁ : PassAbove F ℓ a₁ b₁) : False := by
  have hη : (1 / 2 : ℝ) ≤ 1 := by norm_num
  set L : ℝ → Pt := fun t => (ℓ t : Pt) with hL
  have hLi : Function.Injective L := fun s t e => hℓ.2.1 (Subtype.ext e)
  have hbase : ∀ t ∈ Icc (0 : ℝ) 1, L t = F (t, 0) := fun t ht =>
    hF.base (ℓ := L) (fun t => hγ t) ht
  have hLo : L (1 / 2) = F (1 / 2, 0) := hbase _ ⟨by norm_num, by norm_num⟩
  -- C1: the trap for `P_{m₁}`
  obtain ⟨h₁, hh₁, htrap₁⟩ := trap_pass hF hγ hℓ hη₂ hη₂' hFB hP₁ hthin₁ habove₁ ha₁
    fun a b h ht _ ha => hfirst a b h ht ha
  obtain ⟨δ₂, hδ₂, hS2⟩ := hS2
  -- a point near `o` after time `T` lies in a thin pass after `T`, off the base arc
  have hnear : ∀ (h : ℝ), 0 < h → h ≤ 1 → ∀ T, 1 ≤ T → ∃ a b u x y, IsPass F (1 / 2) ℓ a b ∧
      PassThin F η₂ ℓ a b ∧ u ∈ Ioo a b ∧ T < u ∧ x ∈ Ioo (3 / 8 : ℝ) (5 / 8) ∧
      y ∈ Ioo (-h) h ∧ y ≠ 0 ∧ L u = F (x, y) := by
    intro h hh hh1 T hT
    obtain ⟨ρ, hρ, hball⟩ := exists_ball_box hF hh
    obtain ⟨u, hu, hud⟩ := hrec (T + 1) (min δ₂ ρ) (lt_min hδ₂ hρ)
    obtain ⟨a, b, hab, hthin, hu'⟩ := hS2 u (hud.trans_le (min_le_left _ _))
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, e⟩ := hball (L u) (by
      rw [← hLo]; exact (hud.trans_le (min_le_right _ _)))
    refine ⟨a, b, u, x, y, hab, hthin, hu', by linarith, hx, hy, fun hy0 => ?_, e.symm⟩
    subst hy0
    have := hLi (e.symm.trans (hbase x ⟨by linarith [hx.1], by linarith [hx.2]⟩).symm)
    linarith [hx.2]
  have hcR : ∀ x y, x ∈ Ioo (3 / 8 : ℝ) (5 / 8) → y ∈ Ioo (-1 : ℝ) 1 → (x, y) ∈ cRect :=
    fun x y hx hy => ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hy.1.le, hy.2.le⟩
  have hh₁' : min h₁ 1 ≤ 1 := min_le_right _ _
  -- C3: a thin pass below the base arc after `b₁`
  have hex₂ : ∃ a b, IsPass F (1 / 2) ℓ a b ∧ (PassThin F η₂ ℓ a b ∧ PassBelow F ℓ a b) ∧
      b₁ < a := by
    obtain ⟨a, b, u, x, y, hab, hthin, hu, hTu, hx, hy, hy0, e⟩ :=
      hnear (min h₁ 1) (lt_min hh₁ one_pos) hh₁' (b₁ + 1) (by linarith [hP₁.1])
    have hba : b₁ < a := hab.lt_of_mem hF hη hP₁ (Ioo_subset_Icc_self hu) (by linarith)
    rcases lt_or_gt_of_ne hy0 with hneg | hpos
    · refine ⟨a, b, hab, ⟨hthin, ?_⟩, hba⟩
      have hne : (a, b) ≠ (1 / 4, 3 / 4) := fun e' => by
        simp only [Prod.mk.injEq] at e'; linarith [hP₁.1]
      rcases hab.above_or_below hF hγ hℓ.1 hℓ.2.1 (by norm_num) hη hne with habv | hbel
      · exfalso
        obtain ⟨z, hz, hz0, ez⟩ := habv u (Ioo_subset_Icc_self hu)
        have := hF.injOn hz (hcR x y hx ⟨by linarith [hy.1, min_le_right h₁ 1], by
          linarith [hy.2, min_le_right h₁ 1]⟩) (ez.symm.trans e)
        rw [this] at hz0; simp only at hz0; linarith
      · exact hbel
    · exact absurd ⟨(x, y), ⟨hx, hpos, hy.2.trans_le (min_le_left _ _)⟩, e.symm⟩
        (htrap₁ a b hab hba u hu)
  obtain ⟨a₂, b₂, hP₂, ⟨hthin₂, hbel₂⟩, ha₂, hfirst₂⟩ :=
    exists_first_pass hF (by norm_num) hη hℓ.1
      (fun a b => PassThin F η₂ ℓ a b ∧ PassBelow F ℓ a b) b₁ hex₂
  -- C4: the trap for `P_{m₂}`, with the flipped collar
  obtain ⟨h₂, hh₂, htrap₂⟩ := trap_pass hF.flip hγ hℓ hη₂ hη₂' hFB.flip hP₂.flip hthin₂.flip
    hbel₂.flip (by linarith [hP₁.1]) fun a b h ht habv ha => by
      have h' := h.of_flip
      have hbel := habv.of_flip
      have ha1 := hfirst a b h' ht.of_flip ha
      rcases le_or_gt a b₁ with hab1 | hab1
      · exfalso
        have heq := h'.eq_of_mem hF hη hP₁ ⟨le_rfl, h'.1.le⟩ ⟨ha1, hab1⟩
        simp only [Prod.mk.injEq] at heq
        rw [heq.1, heq.2] at hbel
        exact habove₁.not_below hF hP₁.1.le hbel
      · exact hfirst₂ a b h' ⟨ht.of_flip, hbel⟩ hab1
  -- C5: the contradiction
  set h := min (min h₁ h₂) 1 with hhdef
  have hh0 : 0 < h := lt_min (lt_min hh₁ hh₂) one_pos
  obtain ⟨a, b, u, x, y, hab, -, hu, hTu, hx, hy, hy0, e⟩ :=
    hnear h hh0 (min_le_right _ _) (b₂ + 1) (by linarith [hP₂.1, hP₁.1])
  have hba : b₂ < a := hab.lt_of_mem hF hη hP₂ (Ioo_subset_Icc_self hu) (by linarith)
  have hm1 : h ≤ h₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : h ≤ h₂ := (min_le_left _ _).trans (min_le_right _ _)
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · refine htrap₂ a b hab.flip hba u hu ⟨(x, -y), ⟨hx, by linarith, by linarith [hy.1]⟩, ?_⟩
    simp only [neg_neg]; exact e.symm
  · exact htrap₁ a b hab (by linarith [hP₂.1]) u hu
      ⟨(x, y), ⟨hx, hpos, by linarith [hy.2]⟩, e.symm⟩

variable [CompactSpace M]

/-- **§6, the contradiction**: a line of a `JonesSetting` plane continuum has no collar of its arc
`ℓ[0, 1]`. -/
theorem jones75_contra (S : JonesSetting M) (hℓ : IsLine ℓ)
    (hγ : ∀ t : unitInterval, γ t = ℓ t) (hF : IsCollar γ F) : False := by
  obtain ⟨η₂, hη₂0, hη₂, hFB⟩ := flow_box S hℓ hγ hF (η := 1 / 2) (by norm_num) le_rfl
  have hFB' : FBProp F η₂ ℓ := hFB
  have hS2 := scale_two S hℓ hγ hF hη₂0 hη₂.le
  have hrec : ∀ T, ∀ ε > 0, ∃ u ≥ T, dist (ℓ u) (ℓ (1 / 2)) < ε :=
    mem_omegaLim_iff.1 (S.line_recurrent hℓ (mem_range_self _))
  obtain ⟨a₀, b₀, ha₀, hP₀, hthin₀⟩ :=
    exists_late_thin_pass S hℓ hγ hF hη₂0 hη₂ (by norm_num) (3 / 4)
  obtain ⟨a₁, b₁, hP₁, hthin₁, ha₁, hfirst⟩ := exists_first_pass hF (by norm_num) (by norm_num)
    hℓ.1 (fun a b => PassThin F η₂ ℓ a b) (3 / 4) ⟨a₀, b₀, hP₀, hthin₀, ha₀⟩
  have hne : (a₁, b₁) ≠ (1 / 4, 3 / 4) := fun e => by
    simp only [Prod.mk.injEq] at e; linarith [e.1]
  rcases hP₁.above_or_below hF hγ hℓ.1 hℓ.2.1 (by norm_num) (by norm_num) hne with hab | hbel
  · exact jones75_final_aux hF hγ hℓ hrec hη₂0 hη₂ hFB' hS2 hP₁ hthin₁ ha₁ hfirst hab
  · obtain ⟨δ₂, hδ₂, hS2'⟩ := hS2
    refine jones75_final_aux hF.flip hγ hℓ hrec hη₂0 hη₂ hFB'.flip ⟨δ₂, hδ₂, fun u hu => ?_⟩
      hP₁.flip hthin₁.flip ha₁ (fun a b h ht ha => hfirst a b h.of_flip ht.of_flip ha) hbel.flip
    obtain ⟨a, b, h, ht, hu'⟩ := hS2' u hu
    exact ⟨a, b, h.flip, ht.flip, hu'⟩

end Final

/-! ## §6. The Theorem and its corollaries -/

/-- **§6.1, the arc step** (Bing 1960, indecomposable case; Jones 1975, Theorem, by the route of
commission 190): no indecomposable homogeneous plane continuum contains an arc. -/
theorem jones75_noArc : NoArcIndecHomPlane := by
  intro Q _ _ hX hi α hα
  obtain ⟨e⟩ := hα
  have harc : ∃ (a b : Q) (A : Set Q), TArc a b A := by
    refine ⟨e.symm 0, e.symm 1, α, fun h => ?_, fun t => (e.symm t : Q),
      IsEmbedding.subtypeVal.comp e.symm.isEmbedding, ?_, rfl, rfl⟩
    · have := e.symm.injective (Subtype.ext h)
      exact zero_ne_one (congrArg Subtype.val this)
    · rw [show (fun t => (e.symm t : Q)) = Subtype.val ∘ e.symm from rfl, Set.range_comp,
        e.symm.surjective.range_eq, image_univ, Subtype.range_coe]
  have S := jonesSetting_of_plane hX hi harc
  obtain ⟨ℓ, hℓ, -⟩ := S.exists_line (e.symm 0 : Q)
  set γ : unitInterval → Pt := fun t => ((ℓ t : Q) : Pt) with hγ
  have hγc : Continuous γ := continuous_subtype_val.comp (hℓ.1.comp continuous_subtype_val)
  have hγi : Function.Injective γ := fun s t h =>
    Subtype.ext (hℓ.2.1 (Subtype.ext h))
  obtain ⟨F, hF⟩ := exists_collar (hγc.isClosedEmbedding hγi).isEmbedding
  exact jones75_contra S hℓ (fun t => rfl) hF

/-- **§6.2, Theorem 1 of Hagopian 1976** ("Every indecomposable homogeneous plane continuum is
hereditarily indecomposable"), unconditional. -/
theorem hagopian76_theorem1 : Hagopian76Thm1 :=
  hagopian76_theorem1_jones jones75_noArc

section Corollaries

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§6.3, Bing 1960 for plane continua**, unconditional: "A simple closed curve is the only
homogeneous bounded plane continuum that contains an arc." -/
theorem bing60_plane_uncond (hX : IsHomogeneous M) {α : Set M}
    (hα : Nonempty (α ≃ₜ unitInterval)) : Nonempty (M ≃ₜ Circle) :=
  bing60_plane hagopian76_theorem1 hX hα

/-- **§6.3, Hagopian 1976, Theorem 2**, unconditional: every homogeneous plane continuum that does
not separate the plane is hereditarily indecomposable. -/
theorem hagopian76_theorem2_uncond (hX : IsHomogeneous M) (hns : ¬ SeparatesPlane M) :
    IsHereditarilyIndecomposable (univ : Set M) :=
  hagopian76_theorem2 hagopian76_theorem1 hX hns

/-- **Hagopian 1975, Corollary**, unconditional: no nondegenerate subcontinuum of a homogeneous
indecomposable plane continuum is hereditarily decomposable. -/
theorem hagopian75_corollary_uncond (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {H : Set M} (hH : Fold.Q78.IsContinuum H) (hnd : H.Nontrivial) :
    ¬ IsHereditarilyDecomposable H :=
  hagopian75_corollary hagopian76_theorem1 hX hi hH hnd

/-- **Hagopian 1975, Theorem 2**, unconditional: the simple closed curve is the only homogeneous
plane continuum that has a (nondegenerate) hereditarily decomposable subcontinuum. -/
theorem hagopian75_theorem2_uncond (hX : IsHomogeneous M) {H : Set M}
    (hH : Fold.Q78.IsContinuum H) (hnd : H.Nontrivial) (hHd : IsHereditarilyDecomposable H) :
    Nonempty (M ≃ₜ Circle) :=
  hagopian75_theorem2 hagopian76_theorem1 hX hH hnd hHd

/-- **Hagopian 1975, Theorem 1, paragraph 4 supplied** (`hagopian75_theorem1_of_noArc`),
unconditional. -/
theorem hagopian75_theorem1_of_noArc_uncond (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M)
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) :
    ∃ Y ⊆ E, Fold.Q78.IsContinuum Y ∧ Y.Nontrivial ∧ IsHomogeneous Y ∧
      Fold.Q78.IsIndecomposable Y :=
  hagopian75_theorem1_of_noArc jones75_noArc hX hi hE hk hk0

end Corollaries

end HPC.Hagopian
