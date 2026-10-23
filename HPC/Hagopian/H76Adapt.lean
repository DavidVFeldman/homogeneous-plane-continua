import HPC.Hagopian.Hagopian76E

/-!
# Batch 163, item A: a collar in which a given transverse arc is vertical

Route (commission 163 §2.A, made concrete). Start from any collar `F` of `γ`
(`exists_collar`), made continuous on the whole plane by clamping. Near its end `γ y` the arc `β`
lies in the open collar rectangle, and, being connected and off `γ`, on one side of it; flipping
`F` if necessary, below. In collar coordinates the end piece of `β`, cut at its last exit from a
small box under `(y, 0)` and continued by a vertical segment down to the bottom side, is an arc
`β₁` from `(y, 0)` to a point `(x₀, -1)` of the bottom side, crossing the open lower rectangle
`Q = (0, 1) × (-1, 0)` (`exists_drop_arc`). `β₁` cuts `Q` into two Jordan domains
(`plane_split`); two-sided Schoenflies (`plane_schoenflies₂`) in each, with the bottom side on
the top edge of `Q` and the left side on `β₁`, glue to a new lower half-collar whose vertical over
`y` runs along `β₁` (`exists_lower_halfcollar`). The upper half of `F` is kept.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- A horizontal segment is an arc. -/
theorem tarc_hseg {a b : ℝ} (c : ℝ) (hab : a ≠ b) :
    TArc ((a, c) : Pt) (b, c) (uIcc a b ×ˢ {c}) := by
  have h : ((a, c) : Pt) ≠ (b, c) := fun e => hab (congrArg Prod.fst e)
  have := tarc_segment h
  rwa [← Prod.image_mk_segment_left, segment_eq_uIcc, ← prod_singleton] at this

/-- A vertical segment is an arc. -/
theorem tarc_vseg {a b : ℝ} (c : ℝ) (hab : a ≠ b) :
    TArc ((c, a) : Pt) (c, b) ({c} ×ˢ uIcc a b) := by
  have h : ((c, a) : Pt) ≠ (c, b) := fun e => hab (congrArg Prod.snd e)
  have := tarc_segment h
  rwa [← Prod.image_mk_segment_right, segment_eq_uIcc, ← singleton_prod] at this

/-- A collar turned upside down is a collar. -/
theorem IsCollar.flip {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) :
    IsCollar γ (fun q => F (q.1, -q.2)) := by
  obtain ⟨hemb, h0, hopen⟩ := hF
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hmaps : MapsTo (fun q : ℝ × ℝ => (q.1, -q.2)) K K := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only [mem_Icc] at hb
    exact ⟨ha, by simp only [mem_Icc]; constructor <;> linarith [hb.1, hb.2]⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have hfl : IsEmbedding (hmaps.restrict _ K K) := by
    refine (Continuous.isClosedEmbedding ?_ ?_).isEmbedding
    · exact (continuous_fst.prodMk continuous_snd.neg).restrict hmaps
    · rintro ⟨⟨a, b⟩, _⟩ ⟨⟨a', b'⟩, _⟩ e
      simp only [MapsTo.restrict, Subtype.map, Subtype.mk.injEq, Prod.mk.injEq, neg_inj] at e
      exact Subtype.ext (Prod.ext e.1 e.2)
  refine ⟨hemb.comp hfl, fun t => by simpa using h0 t, ?_⟩
  have : (fun q : ℝ × ℝ => F (q.1, -q.2)) '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) =
      F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
    ext z; constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      simp only [mem_Ioo] at hb
      exact ⟨(a, -b), ⟨ha, by simp only [mem_Ioo]; constructor <;> linarith [hb.1, hb.2]⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      simp only [mem_Ioo] at hb
      exact ⟨(a, -b), ⟨ha, by simp only [mem_Ioo]; constructor <;> linarith [hb.1, hb.2]⟩,
        by simp⟩
  rw [this]; exact hopen

/-- Every collar agrees on its rectangle with a collar continuous on the whole plane. -/
theorem IsCollar.exists_continuous {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) :
    ∃ G : ℝ × ℝ → Pt, Continuous G ∧ IsCollar γ G ∧
      ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, G q = F q := by
  obtain ⟨hemb, h0, hopen⟩ := hF
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  let r : ℝ × ℝ → K := fun q =>
    ⟨((projIcc (0 : ℝ) 1 zero_le_one q.1 : ℝ), (projIcc (-1 : ℝ) 1 (by norm_num) q.2 : ℝ)),
      ⟨(projIcc (0 : ℝ) 1 zero_le_one q.1).2, (projIcc (-1 : ℝ) 1 (by norm_num) q.2).2⟩⟩
  have hr : Continuous r := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hrK : ∀ q (hq : q ∈ K), r q = ⟨q, hq⟩ := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    apply Subtype.ext
    simp only [r, projIcc_of_mem _ ha, projIcc_of_mem _ hb]
  have hG : ∀ q ∈ K, K.restrict F (r q) = F q := fun q hq => by rw [hrK q hq]; rfl
  refine ⟨fun q => K.restrict F (r q), hemb.continuous.comp hr, ⟨?_, ?_, ?_⟩, hG⟩
  · have : K.restrict (fun q => K.restrict F (r q)) = K.restrict F := by
      funext ⟨q, hq⟩; exact hG q hq
    rw [this]; exact hemb
  · intro t
    show K.restrict F (r ((t : ℝ), 0)) = γ t
    rw [hG ((t : ℝ), 0) ⟨t.2, by norm_num⟩]; exact h0 t
  · have : (fun q => K.restrict F (r q)) '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) =
        F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
      refine image_congr fun q hq => hG q ?_
      exact ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩
    rw [this]; exact hopen

/-- **The drop arc.** `g` runs (continuously and injectively on `[t₁, 1]`) through the open lower
rectangle `Q = (0, 1) × (-1, 0)` and ends at `(y, 0)`. Cut at its last exit from a small box under
`(y, 0)` and continued by a vertical segment down to the bottom side, it gives an arc from `(y, 0)` to
a point `(x₀, -1)` crossing `Q`, which near `(y, 0)` is contained in `g[[t₁, 1]]`. -/
theorem exists_drop_arc {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) {g : ℝ → Pt} {t₁ : ℝ}
    (ht₁ : t₁ < 1) (hgc : ContinuousOn g (Icc t₁ 1)) (hginj : InjOn g (Icc t₁ 1))
    (hg1 : g 1 = (y, 0)) (hgQ : ∀ t, t₁ ≤ t → t < 1 → g t ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ < 1 ∧ ∃ β₁ : Set Pt, TArc ((y, 0) : Pt) (x₀, -1) β₁ ∧
      β₁ \ {((y, 0) : Pt), (x₀, -1)} ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0 ∧
      ∃ W ∈ 𝓝 ((y, 0) : Pt), β₁ ∩ W ⊆ g '' Icc t₁ 1 := by
  obtain ⟨⟨-, -⟩, hs₀1, hs₀0⟩ := hgQ t₁ le_rfl ht₁
  set s₀ := (g t₁).2
  set η := -s₀ / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set δ := min y (1 - y) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hy0 (by linarith))
  have hδy : δ < y := by rw [hδ]; linarith [min_le_left y (1 - y)]
  have hδy' : δ < 1 - y := by rw [hδ]; linarith [min_le_right y (1 - y)]
  set B : Set Pt := Ioo (y - δ) (y + δ) ×ˢ Ioo (-η) η with hB
  have hBo : IsOpen B := isOpen_Ioo.prod isOpen_Ioo
  set S := Icc t₁ 1 ∩ g ⁻¹' Bᶜ with hS
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hgc.preimage_isClosed_of_isClosed isClosed_Icc hBo.isClosed_compl) inter_subset_left
  have ht₁S : t₁ ∈ S := ⟨⟨le_rfl, ht₁.le⟩, fun h => by
    have := h.2.1
    linarith⟩
  obtain ⟨τ, hτS, hτmax⟩ := hSc.exists_isGreatest ⟨t₁, ht₁S⟩
  have hτ1' : τ ≤ 1 := hτS.1.2
  have ht₁τ : t₁ ≤ τ := hτmax ht₁S
  have h1B : g 1 ∈ B := by
    rw [hg1]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hη0⟩⟩
  have hτ1 : τ < 1 := lt_of_le_of_ne hτ1' (fun e => hτS.2 (e ▸ h1B))
  have hafter : ∀ t, τ < t → t ≤ 1 → g t ∈ B := fun t ht ht1 => by
    by_contra h
    exact absurd (hτmax ⟨⟨by linarith, ht1⟩, h⟩) (not_le.2 ht)
  have hτcl : g τ ∈ closure B := by
    have hcw : ContinuousWithinAt g (Ioc τ 1) τ :=
      (hgc τ ⟨ht₁τ, hτ1'⟩).mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
    have hmem : τ ∈ closure (Ioc τ 1) := by
      rw [closure_Ioc hτ1.ne]; exact ⟨le_rfl, hτ1'⟩
    exact closure_mono (image_subset_iff.2 fun t ht => hafter t ht.1 ht.2)
      (hcw.mem_closure_image hmem)
  rw [hB, closure_prod_eq, closure_Ioo (by linarith), closure_Ioo (by linarith)] at hτcl
  obtain ⟨hx₀cl, hs₁cl⟩ := hτcl
  obtain ⟨⟨hx₀0, hx₀1⟩, hs₁1, hs₁0⟩ := hgQ τ ht₁τ hτ1
  set x₀ := (g τ).1 with hx₀
  set s₁ := (g τ).2 with hs₁
  have hnotB : ¬ (x₀ ∈ Ioo (y - δ) (y + δ) ∧ s₁ ∈ Ioo (-η) η) := hτS.2
  -- the vertical segment
  set V : Set Pt := {x₀} ×ˢ Icc (-1) s₁ with hV
  have hVarc : TArc (g τ) (x₀, -1) V := by
    have := tarc_vseg x₀ (ne_of_gt hs₁1)
    rwa [uIcc_of_ge hs₁1.le] at this
  -- the end piece of `g`
  set A := g '' Icc τ 1 with hA
  have hAarc : TArc (g τ) ((y : ℝ), (0 : ℝ)) A := by
    have h1τ : (1 - τ) ≠ 0 := by linarith
    have hmem : ∀ u : unitInterval, τ + (u : ℝ) * (1 - τ) ∈ Icc τ 1 := fun u =>
      ⟨by nlinarith [u.2.1, u.2.2], by nlinarith [u.2.1, u.2.2]⟩
    have hc : Continuous (fun u : unitInterval => g (τ + (u : ℝ) * (1 - τ))) := by
      refine hgc.comp_continuous (by fun_prop) fun u => ?_
      exact ⟨le_trans ht₁τ (hmem u).1, (hmem u).2⟩
    have hinj : Function.Injective (fun u : unitInterval => g (τ + (u : ℝ) * (1 - τ))) := by
      intro u v huv
      have := hginj ⟨le_trans ht₁τ (hmem u).1, (hmem u).2⟩
        ⟨le_trans ht₁τ (hmem v).1, (hmem v).2⟩ huv
      exact Subtype.ext (mul_right_cancel₀ h1τ (by linarith))
    have hr : range (fun u : unitInterval => g (τ + (u : ℝ) * (1 - τ))) = A := by
      apply Subset.antisymm
      · rintro _ ⟨u, rfl⟩; exact ⟨_, hmem u, rfl⟩
      · rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
        have hu : (t - τ) / (1 - τ) ∈ Icc (0 : ℝ) 1 := by
          constructor
          · exact div_nonneg (by linarith) (by linarith)
          · rw [div_le_one (by linarith)]; linarith
        refine ⟨⟨_, hu⟩, ?_⟩
        simp only
        congr 1
        field_simp
        ring
    have := TArc.of_inj hc hinj
    have e0 : g (τ + ((0 : unitInterval) : ℝ) * (1 - τ)) = g τ := by simp
    have e1 : g (τ + ((1 : unitInterval) : ℝ) * (1 - τ)) = ((y : ℝ), (0 : ℝ)) := by
      simp [hg1]
    rw [e0, e1, hr] at this
    exact this
  have hAV : A ∩ V = {g τ} := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, ⟨htτ, ht1⟩, rfl⟩, hz1, hz2⟩
      rcases eq_or_lt_of_le htτ with h | h
      · rw [h]; rfl
      rcases eq_or_lt_of_le ht1 with h' | h'
      · subst h'
        rw [hg1] at hz2
        exact absurd hz2.2 (not_le.2 hs₁0)
      · exfalso
        have hB' := hafter t h ht1
        have hx : x₀ ∈ Ioo (y - δ) (y + δ) := by
          rw [← (mem_singleton_iff.1 hz1)]; exact hB'.1
        have hs : s₁ ∉ Ioo (-η) η := fun hs => hnotB ⟨hx, hs⟩
        have : s₁ ≤ -η := by
          by_contra hc
          push_neg at hc
          exact hs ⟨hc, by linarith⟩
        linarith [hB'.2.1, hz2.2]
    · rintro z rfl
      exact ⟨⟨τ, ⟨le_rfl, hτ1'⟩, rfl⟩, mem_singleton _, ⟨hs₁1.le, le_rfl⟩⟩
  have hβarc : TArc ((y : ℝ), (0 : ℝ)) (x₀, -1) (A ∪ V) := TArc.union hAarc.symm hVarc hAV
  refine ⟨x₀, hx₀0, hx₀1, A ∪ V, hβarc, ?_, Vᶜ, ?_, ?_⟩
  · rintro z ⟨hz | hz, hzab⟩
    · obtain ⟨t, ⟨htτ, ht1⟩, rfl⟩ := hz
      rcases eq_or_lt_of_le ht1 with h | h
      · exact absurd (Or.inl (h ▸ hg1)) hzab
      · exact hgQ t (le_trans ht₁τ htτ) h
    · obtain ⟨hz1, hz2⟩ := hz
      have hz1' : z.1 = x₀ := hz1
      refine ⟨by rw [hz1']; exact ⟨hx₀0, hx₀1⟩, ?_, by linarith [hz2.2]⟩
      by_contra hc
      have : z.2 = -1 := le_antisymm (not_lt.1 hc) hz2.1
      exact hzab (Or.inr (Prod.ext hz1' this))
  · refine (isClosed_singleton.prod isClosed_Icc).isOpen_compl.mem_nhds fun h => ?_
    have := h.2.2
    linarith
  · rintro z ⟨hz | hz, hzW⟩
    · exact image_mono (Icc_subset_Icc_left ht₁τ) hz
    · exact absurd hz hzW

end HPC.Hagopian
