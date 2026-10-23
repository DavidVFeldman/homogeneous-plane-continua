import HPC.Jones.Jones75Pass

/-!
# Jones 1975 II (batch 190), part 2: the shadow lemma, the flow box, late thin passes

Commission 190 §3: the shadow lemma (`shadow_pass`, Effros and (O)), the flow box (`flow_box`, scale
1), thin passes and their (Mon) (`PassThin.passMon`), scale 2 (`scale_two`), and late thin passes
(`exists_late_thin_pass`). All of these hold in the middle band only.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Shadow

variable {M : Set Pt} [CompactSpace M]

/-- The flow box property (FB) for the thin height `η₂`: every point of the line in the middle band
`F([9/32, 23/32] × [−η₂, η₂])` lies inside a pass of the box of height `½` with (Mon). -/
def FBProp (F : ℝ × ℝ → Pt) (η₂ : ℝ) (ℓ : ℝ → M) : Prop :=
  ∀ u, (ℓ u : Pt) ∈ F '' (Icc (9 / 32) (23 / 32) ×ˢ Icc (-η₂) η₂) →
    ∃ a b, IsPass F (1 / 2) ℓ a b ∧ PassMon F (1 / 32) ℓ a b ∧ u ∈ Ioo a b

variable {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} {ℓ : ℝ → M}

omit [CompactSpace M] in
theorem FBProp.flip {η₂ : ℝ} (h : FBProp F η₂ ℓ) : FBProp (flipC F) η₂ ℓ := by
  intro u hu
  rw [flipC_image F (symm_prod _ (Or.inl rfl))] at hu
  obtain ⟨a, b, h1, h2, h3⟩ := h u hu
  exact ⟨a, b, h1.flip, h2.flip, h3⟩

/-- **§3.1, the shadow lemma** (Effros + (O)), in the middle band only. -/
theorem shadow_pass (S : JonesSetting M) (hℓ : IsLine ℓ)
    (hγ : ∀ t : unitInterval, γ t = ℓ t) (hF : IsCollar γ F) {η' : ℝ}
    (hη' : 0 < η') :
    ∃ δ > 0, ∀ x ∈ Icc (9 / 32 : ℝ) (23 / 32), ∀ u, dist (ℓ u) (ℓ x) < δ →
      ∃ a b, IsPass F η' ℓ a b ∧ PassMon F (1 / 32) ℓ a b ∧ u ∈ Ioo a b := by
  set W : Set Pt := F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) with hW
  have hWo : IsOpen W := hF.2.2
  have hWR : W ⊆ F '' cRect := image_mono openRect_subset_rect
  set X : Pt → ℝ := fun p => (collarCoord F p).1 with hX
  set Yc : Pt → ℝ := fun p => (collarCoord F p).2 with hYc
  have hXc : ContinuousOn X W :=
    continuous_fst.comp_continuousOn ((continuousOn_collarCoord hF).mono hWR)
  have hYcc : ContinuousOn Yc W :=
    continuous_snd.comp_continuousOn ((continuousOn_collarCoord hF).mono hWR)
  set L : ℝ → Pt := fun t => (ℓ t : Pt) with hL
  have hLc : Continuous L := continuous_subtype_val.comp hℓ.1
  have hbase : ∀ t ∈ Icc (0 : ℝ) 1, L t = F (t, 0) := fun t ht =>
    hF.base (ℓ := L) (fun t => hγ t) ht
  set K₀ : Set Pt := L '' Icc (3 / 16 : ℝ) (13 / 16 : ℝ) with hK₀
  have hK₀c : IsCompact K₀ := isCompact_Icc.image hLc
  have hK₀W : ∀ p ∈ K₀, W ∈ 𝓝 p := by
    rintro _ ⟨t, ht, rfl⟩
    refine hWo.mem_nhds ⟨(t, 0), ⟨⟨show (0 : ℝ) < t by linarith [ht.1],
      show t < 1 by linarith [ht.2]⟩, by norm_num, by norm_num⟩,
      (hbase t ⟨by linarith [ht.1], by linarith [ht.2]⟩).symm⟩
  have hcoord : ∀ t ∈ Icc (3 / 16 : ℝ) (13 / 16 : ℝ), collarCoord F (L t) = (t, 0) := fun t ht =>
    collarCoord_eq hF ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, by norm_num, by norm_num⟩
      (hbase t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  obtain ⟨ε₁, hε₁, hu₁⟩ := uniform_near_compact hK₀c hK₀W hXc (show (0 : ℝ) < 1 / 32 by norm_num)
  obtain ⟨ε₂, hε₂, hu₂⟩ := uniform_near_compact hK₀c hK₀W hYcc hη'
  obtain ⟨ε₀, hε₀, horient⟩ := S.orientation
  obtain ⟨δ, hδ, hEff⟩ := HPC.Effros.effros_homogeneous S.hom
    (lt_min hε₀ (lt_min hε₁ hε₂))
  refine ⟨δ, hδ, fun x hx u hux => ?_⟩
  obtain ⟨h, hhx, hhsmall⟩ := hEff (ℓ x) (ℓ u) (by rw [dist_comm]; exact hux)
  have hsm : ∀ z, dist z (h z) < min ε₀ (min ε₁ ε₂) := fun z => by
    rw [dist_comm]; exact hhsmall z
  obtain ⟨ψ, hψm, hψc, -, hψ⟩ := horient h (fun z => (hsm z).trans_le (min_le_left _ _))
    _ (hℓ.shift x) (by simp only [zero_add, hhx]; exact ⟨u - x, by simp⟩)
  set Ψ : ℝ → ℝ := fun t => ψ (t - x) + x with hΨ
  have hΨe : ∀ t, h (ℓ t) = ℓ (Ψ t) := fun t => by
    have := hψ (t - x)
    simp only [sub_add_cancel] at this
    exact this
  have hΨm : StrictMono Ψ := fun a b hab => by
    simp only [hΨ]; linarith [hψm (show a - x < b - x by linarith)]
  have hΨc : Continuous Ψ := (hψc.comp (continuous_sub_right x)).add continuous_const
  have hΨx : Ψ x = u := hℓ.2.1 ((hΨe x).symm.trans hhx)
  -- the estimate along the shadow
  have hest0 : ∀ t ∈ Icc (3 / 16 : ℝ) (13 / 16 : ℝ), L (Ψ t) ∈ W ∧ |X (L (Ψ t)) - t| < 1 / 32 ∧ |Yc (L (Ψ t))| < η' := by
    intro t ht
    have hd : dist (L t) (L (Ψ t)) < min ε₀ (min ε₁ ε₂) := by
      have := hsm (ℓ t)
      rw [hΨe, Subtype.dist_eq] at this
      exact this
    obtain ⟨hW1, hX1⟩ := hu₁ (L t) (mem_image_of_mem L ht) (L (Ψ t))
      (hd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    obtain ⟨-, hY1⟩ := hu₂ (L t) (mem_image_of_mem L ht) (L (Ψ t))
      (hd.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    simp only [hX, hYc, hcoord t ht] at hX1 hY1 ⊢
    exact ⟨hW1, hX1, by simpa using hY1⟩
  have hest : ∀ v ∈ Icc (Ψ (3 / 16 : ℝ)) (Ψ (13 / 16 : ℝ)), ∃ t ∈ Icc (3 / 16 : ℝ) (13 / 16 : ℝ), Ψ t = v ∧ L v ∈ W ∧
      |X (L v) - t| < 1 / 32 ∧ |Yc (L v)| < η' := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc (show (3 / 16 : ℝ) ≤ (13 / 16 : ℝ) by norm_num) hΨc.continuousOn hv
    exact ⟨t, ht, rfl, hest0 t ht⟩
  have hestW : ∀ v ∈ Icc (Ψ (3 / 16 : ℝ)) (Ψ (13 / 16 : ℝ)), L v ∈ W := fun v hv => by
    obtain ⟨_, _, _, h, _⟩ := hest v hv; exact h
  have hfc : ContinuousOn (fun v => X (L v)) (Icc (Ψ (3 / 16 : ℝ)) (Ψ (13 / 16 : ℝ))) :=
    hXc.comp hLc.continuousOn fun v hv => hestW v hv
  have hxs : x ∈ Icc (3 / 16 : ℝ) (13 / 16 : ℝ) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hu1 : Ψ (3 / 16 : ℝ) < u := hΨx ▸ hΨm (by linarith [hx.1])
  have hu2 : u < Ψ (13 / 16 : ℝ) := hΨx ▸ hΨm (by linarith [hx.2])
  have huI : u ∈ Icc (Ψ (3 / 16 : ℝ)) (Ψ (13 / 16 : ℝ)) := ⟨hu1.le, hu2.le⟩
  have hfu : 1 / 4 < X (L u) ∧ X (L u) < 3 / 4 := by
    obtain ⟨t, -, ht, -, h1, -⟩ := hest u huI
    have : t = x := hΨm.injective (ht.trans hΨx.symm)
    subst this
    constructor <;> linarith [abs_lt.1 h1, hx.1, hx.2]
  have hf1 : X (L (Ψ (3 / 16 : ℝ))) < 1 / 4 := by
    obtain ⟨t, ht, hte, -, h1, -⟩ := hest (Ψ (3 / 16 : ℝ)) ⟨le_rfl, (hΨm (by norm_num)).le⟩
    have : t = (3 / 16 : ℝ) := hΨm.injective hte
    subst this
    linarith [abs_lt.1 h1]
  have hf2 : 3 / 4 < X (L (Ψ (13 / 16 : ℝ))) := by
    obtain ⟨t, ht, hte, -, h1, -⟩ := hest (Ψ (13 / 16 : ℝ)) ⟨(hΨm (by norm_num)).le, le_rfl⟩
    have : t = (13 / 16 : ℝ) := hΨm.injective hte
    subst this
    linarith [abs_lt.1 h1]
  -- the start `a`
  set A := {v ∈ Icc (Ψ (3 / 16 : ℝ)) u | X (L v) ≤ 1 / 4} with hA
  have hAsub : Icc (Ψ (3 / 16 : ℝ)) u ⊆ Icc (Ψ (3 / 16 : ℝ)) (Ψ (13 / 16 : ℝ)) := Icc_subset_Icc le_rfl hu2.le
  have hAc : IsClosed A := (hfc.mono hAsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hAne : A.Nonempty := ⟨Ψ (3 / 16 : ℝ), ⟨le_rfl, hu1.le⟩, hf1.le⟩
  have hAb : BddAbove A := ⟨u, fun v hv => hv.1.2⟩
  set a := sSup A with ha
  have haA : a ∈ A := hAc.csSup_mem hAne hAb
  have hau : a < u := lt_of_le_of_ne haA.1.2 fun e => by
    have := haA.2; rw [e] at this; linarith [hfu.1]
  have hafter : ∀ v, a < v → v ≤ u → 1 / 4 < X (L v) := fun v hv hvu => by
    by_contra hle
    push_neg at hle
    have := le_csSup hAb ⟨⟨haA.1.1.trans hv.le, hvu⟩, hle⟩
    linarith
  have hfa : X (L a) = 1 / 4 := by
    obtain ⟨c, hc, hfc'⟩ := intermediate_value_Icc hau.le
      (hfc.mono (Icc_subset_Icc haA.1.1 hu2.le)) ⟨haA.2, hfu.1.le⟩
    have hca : c ≤ a := le_csSup hAb ⟨⟨haA.1.1.trans hc.1, hc.2⟩, hfc'.le⟩
    rw [← le_antisymm hca hc.1]; exact hfc'
  -- the end `b`
  set B := {v ∈ Icc u (Ψ (13 / 16 : ℝ)) | 3 / 4 ≤ X (L v)} with hB
  have hBsub : Icc u (Ψ (13 / 16 : ℝ)) ⊆ Icc (Ψ (3 / 16 : ℝ)) (Ψ (13 / 16 : ℝ)) := Icc_subset_Icc hu1.le le_rfl
  have hBc : IsClosed B := (hfc.mono hBsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hBne : B.Nonempty := ⟨Ψ (13 / 16 : ℝ), ⟨hu2.le, le_rfl⟩, hf2.le⟩
  have hBb : BddBelow B := ⟨u, fun v hv => hv.1.1⟩
  set b := sInf B with hb
  have hbB : b ∈ B := hBc.csInf_mem hBne hBb
  have hub : u < b := lt_of_le_of_ne hbB.1.1 fun e => by
    have := hbB.2; rw [← e] at this; linarith [hfu.2]
  have hbefore : ∀ v, u ≤ v → v < b → X (L v) < 3 / 4 := fun v huv hv => by
    by_contra hle
    push_neg at hle
    have := csInf_le hBb ⟨⟨huv, hv.le.trans hbB.1.2⟩, hle⟩
    linarith
  have hfb : X (L b) = 3 / 4 := by
    obtain ⟨c, hc, hfc'⟩ := intermediate_value_Icc hub.le
      (hfc.mono (Icc_subset_Icc hu1.le hbB.1.2)) ⟨hfu.2.le, hbB.2⟩
    have hcb : b ≤ c := csInf_le hBb ⟨⟨hc.1, hc.2.trans hbB.1.2⟩, hfc'.ge⟩
    rw [← le_antisymm hc.2 hcb]; exact hfc'
  have habI : Icc a b ⊆ Icc (Ψ (3 / 16 : ℝ)) (Ψ (13 / 16 : ℝ)) := Icc_subset_Icc haA.1.1 hbB.1.2
  have hFe : ∀ v ∈ Icc (Ψ (3 / 16 : ℝ)) (Ψ (13 / 16 : ℝ)), F (collarCoord F (L v)) = L v := fun v hv =>
    collarCoord_apply (hWR (hestW v hv))
  refine ⟨a, b, ⟨hau.trans hub, ?_, ?_, ?_⟩, ?_, hau, hub⟩
  · obtain ⟨t, -, -, -, -, hY⟩ := hest a (habI ⟨le_rfl, (hau.trans hub).le⟩)
    refine ⟨Yc (L a), ⟨by linarith [abs_lt.1 hY], by linarith [abs_lt.1 hY]⟩, ?_⟩
    calc (ℓ a : Pt) = F (collarCoord F (L a)) := (hFe a (habI ⟨le_rfl, (hau.trans hub).le⟩)).symm
      _ = F (1 / 4, Yc (L a)) := by congr 1; exact Prod.ext hfa rfl
  · obtain ⟨t, -, -, -, -, hY⟩ := hest b (habI ⟨(hau.trans hub).le, le_rfl⟩)
    refine ⟨Yc (L b), ⟨by linarith [abs_lt.1 hY], by linarith [abs_lt.1 hY]⟩, ?_⟩
    calc (ℓ b : Pt) = F (collarCoord F (L b)) := (hFe b (habI ⟨(hau.trans hub).le, le_rfl⟩)).symm
      _ = F (3 / 4, Yc (L b)) := by congr 1; exact Prod.ext hfb rfl
  · intro s hs
    have hsI := habI (Ioo_subset_Icc_self hs)
    obtain ⟨t, ht, hte, -, hX1, hY⟩ := hest s hsI
    refine ⟨collarCoord F (L s), ⟨(?_ : X (L s) ∈ Ioo (1 / 4 : ℝ) (3 / 4)),
      (⟨by linarith [abs_lt.1 hY], by linarith [abs_lt.1 hY]⟩ : Yc (L s) ∈ Ioo (-η') η')⟩,
      hFe s hsI⟩
    have hX2 := abs_lt.1 hX1
    rcases le_total s u with hsu | hsu
    · have htx : t ≤ x := by rw [← hΨm.le_iff_le, hte, hΨx]; exact hsu
      exact ⟨hafter s hs.1 hsu, by linarith [hx.2]⟩
    · have htx : x ≤ t := by rw [← hΨm.le_iff_le, hte, hΨx]; exact hsu
      exact ⟨by linarith [hx.1], hbefore s hsu hs.2⟩
  · intro v' v hv' hvv hv p' p hp' hp e' e
    have hv'I := habI ⟨hv', hvv.le.trans hv⟩
    have hvI := habI ⟨hv'.trans hvv.le, hv⟩
    obtain ⟨t', -, ht', -, hX', -⟩ := hest v' hv'I
    obtain ⟨t, -, ht, -, hX1, -⟩ := hest v hvI
    have h1 : collarCoord F (L v') = p' := collarCoord_eq hF hp' e'
    have h2 : collarCoord F (L v) = p := collarCoord_eq hF hp e
    have htt : t' < t := by rw [← ht', ← ht] at hvv; exact hΨm.lt_iff_lt.1 hvv
    simp only [hX, h1, h2] at hX' hX1
    linarith [abs_lt.1 hX', abs_lt.1 hX1]

omit [CompactSpace M] in
/-- Passes of a lower box are passes of a higher box (nesting). -/
theorem IsPass.mono {η η' : ℝ} (hηη : η ≤ η') {a b : ℝ} (h : IsPass F η ℓ a b) :
    IsPass F η' ℓ a b := by
  obtain ⟨hab, ⟨ya, hya, ea⟩, ⟨yb, hyb, eb⟩, hint⟩ := h
  refine ⟨hab, ⟨ya, ⟨by linarith [hya.1], by linarith [hya.2]⟩, ea⟩,
    ⟨yb, ⟨by linarith [hyb.1], by linarith [hyb.2]⟩, eb⟩, fun s hs => ?_⟩
  obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := hint s hs
  exact ⟨z, ⟨hz1, by linarith [hz2.1], by linarith [hz2.2]⟩, hz⟩

omit [CompactSpace M] in
/-- A pass of the box of height `η` is thin for `η`. -/
theorem IsPass.thin {η : ℝ} {a b : ℝ} (h : IsPass F η ℓ a b) : PassThin F η ℓ a b := fun s hs => by
  obtain ⟨z, hz, e⟩ := h.mem_box hs
  exact ⟨z, hz, e.symm⟩

omit [CompactSpace M] in
theorem PassThin.mono {η η' : ℝ} (hηη : η ≤ η') {a b : ℝ} (h : PassThin F η ℓ a b) :
    PassThin F η' ℓ a b := fun s hs => by
  obtain ⟨z, ⟨hz1, hz2⟩, e⟩ := h s hs
  exact ⟨z, ⟨hz1, by linarith [hz2.1], by linarith [hz2.2]⟩, e⟩

/-- **§3.2, the flow box (FB)**, in the middle band only: for the box of height `η ≤ ½` there is
`η₂ ∈ (0, η)` such that every point of `ℓ` in `F([9/32, 23/32] × [−η₂, η₂])` lies inside a pass of
the box of height `η` satisfying (Mon). -/
theorem flow_box (S : JonesSetting M) (hℓ : IsLine ℓ)
    (hγ : ∀ t : unitInterval, γ t = ℓ t) (hF : IsCollar γ F) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ η₂ > 0, η₂ < η ∧ ∀ u, (ℓ u : Pt) ∈ F '' (Icc (9 / 32) (23 / 32) ×ˢ Icc (-η₂) η₂) →
      ∃ a b, IsPass F η ℓ a b ∧ PassMon F (1 / 32) ℓ a b ∧ u ∈ Ioo a b := by
  obtain ⟨δ₁, hδ₁, hsh⟩ := shadow_pass S hℓ hγ hF hη
  haveI : CompactSpace cRect := isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have huc := CompactSpace.uniformContinuous_of_continuous hF.1.continuous
  obtain ⟨η₃, hη₃, hη₃F⟩ := Metric.uniformContinuous_iff.1 huc δ₁ hδ₁
  refine ⟨min (η₃ / 2) (η / 2), lt_min (half_pos hη₃) (half_pos hη),
    (min_le_right _ _).trans_lt (half_lt_self hη), fun u hu => ?_⟩
  obtain ⟨⟨x, y⟩, ⟨hx', hy'⟩, e⟩ := hu
  have hx : x ∈ Icc (9 / 32 : ℝ) (23 / 32) := hx'
  have hy : y ∈ Icc (-min (η₃ / 2) (η / 2)) (min (η₃ / 2) (η / 2)) := hy'
  have hm := min_le_left (η₃ / 2) (η / 2)
  have hm' := min_le_right (η₃ / 2) (η / 2)
  have hxy : (x, y) ∈ cRect := ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
    by linarith [hy.1], by linarith [hy.2]⟩
  have hx0 : (x, (0 : ℝ)) ∈ cRect := ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, by norm_num,
    by norm_num⟩
  refine hsh x hx u ?_
  rw [Subtype.dist_eq, ← e, hF.base (ℓ := fun t => (ℓ t : Pt)) (fun t => hγ t)
    ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  refine @hη₃F ⟨(x, y), hxy⟩ ⟨(x, 0), hx0⟩ ?_
  rw [Subtype.dist_eq, Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
    max_eq_right (abs_nonneg y)]
  exact (abs_le.2 ⟨hy.1, hy.2⟩).trans_lt (by linarith)

omit [CompactSpace M] in
/-- (FB′): a pass of the box of height `½` through a point of the middle band of the thin box has
(Mon). -/
theorem FBProp.passMon (hF : IsCollar γ F) {η₂ : ℝ} (hFB : FBProp F η₂ ℓ) {a b : ℝ}
    (h : IsPass F (1 / 2) ℓ a b) {s : ℝ} (hs : s ∈ Icc a b)
    (hsm : (ℓ s : Pt) ∈ F '' (Icc (9 / 32) (23 / 32) ×ˢ Icc (-η₂) η₂)) :
    PassMon F (1 / 32) ℓ a b := by
  obtain ⟨a', b', h', hm, hs'⟩ := hFB s hsm
  have := h.eq_of_mem hF (by norm_num) h' hs (Ioo_subset_Icc_self hs')
  simp only [Prod.mk.injEq] at this
  rw [this.1, this.2]; exact hm

/-- **§3.3, scale 2**: points of the line near `o = ℓ(½)` lie inside thin passes. -/
theorem scale_two (S : JonesSetting M) (hℓ : IsLine ℓ)
    (hγ : ∀ t : unitInterval, γ t = ℓ t) (hF : IsCollar γ F) {η₂ : ℝ} (hη₂ : 0 < η₂)
    (hη₂' : η₂ ≤ 1 / 2) :
    ∃ δ₂ > 0, ∀ u, dist (ℓ u) (ℓ (1 / 2)) < δ₂ →
      ∃ a b, IsPass F (1 / 2) ℓ a b ∧ PassThin F η₂ ℓ a b ∧ u ∈ Ioo a b := by
  obtain ⟨δ₂, hδ₂, hsh⟩ := shadow_pass S hℓ hγ hF (half_pos hη₂)
  refine ⟨δ₂, hδ₂, fun u hu => ?_⟩
  obtain ⟨a, b, h, -, hab⟩ := hsh (1 / 2) ⟨by norm_num, by norm_num⟩ u hu
  exact ⟨a, b, h.mono (by linarith), h.thin.mono (by linarith), hab⟩

/-- **§3.3, late thin passes** (recurrence): passes inside the thin box start arbitrarily late.
(Shape: the hypothesis `η ≤ 1`, needed for (P1), is added.) -/
theorem exists_late_thin_pass (S : JonesSetting M) (hℓ : IsLine ℓ)
    (hγ : ∀ t : unitInterval, γ t = ℓ t) (hF : IsCollar γ F) {η η₂ : ℝ} (hη₂ : 0 < η₂)
    (hη₂η : η₂ < η) (hη : η ≤ 1) (T : ℝ) :
    ∃ a b, T < a ∧ IsPass F η ℓ a b ∧
      ∀ s ∈ Icc a b, (ℓ s : Pt) ∈ F '' (Icc (1 / 4) (3 / 4) ×ˢ Icc (-η₂) η₂) := by
  obtain ⟨δ₂, hδ₂, hsh⟩ := shadow_pass S hℓ hγ hF (half_pos hη₂)
  have hT' : ∃ T' ≥ T, ∀ a b, IsPass F η ℓ a b → a ≤ T → T ≤ b → b ≤ T' := by
    by_cases hex : ∃ a₀ b₀, IsPass F η ℓ a₀ b₀ ∧ T ∈ Icc a₀ b₀
    · obtain ⟨a₀, b₀, h₀, hT₀⟩ := hex
      refine ⟨b₀, hT₀.2, fun a b h ha hb => ?_⟩
      have := h.eq_of_mem hF hη h₀ ⟨ha, hb⟩ hT₀
      simp only [Prod.mk.injEq] at this
      rw [this.2]
    · push_neg at hex
      exact ⟨T, le_rfl, fun a b h ha hb => absurd ⟨ha, hb⟩ (hex a b h)⟩
  obtain ⟨T', hTT, hT'⟩ := hT'
  have hrec := S.line_recurrent hℓ (mem_range_self (1 / 2 : ℝ))
  rw [mem_omegaLim_iff] at hrec
  obtain ⟨u, hu, hud⟩ := hrec (T' + 1) δ₂ hδ₂
  obtain ⟨a, b, h, -, hab⟩ := hsh (1 / 2) ⟨by norm_num, by norm_num⟩ u hud
  have h' := h.mono (by linarith : η₂ / 2 ≤ η)
  refine ⟨a, b, ?_, h', fun s hs => (h.thin.mono (by linarith)) s hs⟩
  by_contra hle
  push_neg at hle
  have := hT' a b h' hle (by linarith [hab.2])
  linarith [hab.2]

end Shadow

end HPC.Hagopian
