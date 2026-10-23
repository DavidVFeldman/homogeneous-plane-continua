import HPC.Jones.Jones75Rev

/-!
# Jones 1975 I (batch 189), part 5: (L), no backtracking near an arc of a line

Commission 189 §5. The argument of the commission (Effros, (O), and the intermediate value theorem)
uses only a coordinate `X` that is continuous near the base arc `ℓ[0, 1]` and equal to the
parameter on it. It is therefore proved first for a `JonesSetting` and an abstract coordinate
(`JonesSetting.no_backtrack`), with the strip measured metrically: `ℓ v` lies within `η` of the base
point `ℓ (X (ℓ v))`. The collar form (`no_backtrack_in_collar`) follows, for a plane continuum and a
collar `F` of the base arc (`IsCollar`), with `X` the first collar coordinate and the strip
`F([κ, 1 − κ] × (−η, η))` of the commission.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section General

variable {Y : Type*} [MetricSpace Y]

/-- A function continuous on a neighbourhood `W` of a compact set `K` is uniformly continuous near
`K`: points within `ε` of `K` lie in `W`, with values close to those at the nearby point of `K`. -/
theorem uniform_near_compact {K W : Set Y} {X : Y → ℝ} (hK : IsCompact K)
    (hKW : ∀ p ∈ K, W ∈ 𝓝 p) (hX : ContinuousOn X W) {c : ℝ} (hc : 0 < c) :
    ∃ ε > 0, ∀ p ∈ K, ∀ p', dist p p' < ε → p' ∈ W ∧ |X p' - X p| < c := by
  have hloc : ∀ p : K, ∃ r > 0, ball (p : Y) r ⊆ W ∧ ∀ y ∈ ball (p : Y) r, |X y - X p| < c / 2 := by
    rintro ⟨p, hp⟩
    have hW := hKW p hp
    have hcont : ContinuousAt X p := hX.continuousAt hW
    obtain ⟨r₁, hr₁, hr₁W⟩ := Metric.mem_nhds_iff.1 hW
    obtain ⟨r₂, hr₂, hr₂X⟩ := Metric.continuousAt_iff.1 hcont (c / 2) (half_pos hc)
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hr₁W,
      fun y hy => ?_⟩
    have := hr₂X (lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _))
    rwa [Real.dist_eq] at this
  choose r hr hrW hrX using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (c := fun p : K => ball (p : Y) (r p))
    (fun _ => isOpen_ball) (fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, mem_ball_self (hr _)⟩)
  refine ⟨δ, hδ, fun p hp p' hpp' => ?_⟩
  obtain ⟨i, hi⟩ := hleb p hp
  have h1 : p ∈ ball (i : Y) (r i) := hi (mem_ball_self hδ)
  have h2 : p' ∈ ball (i : Y) (r i) := hi (by rw [mem_ball, dist_comm]; exact hpp')
  refine ⟨hrW i h2, ?_⟩
  have e1 := hrX i p' h2
  have e2 := hrX i p h1
  calc |X p' - X p| ≤ |X p' - X i| + |X p - X i| := by
        rw [abs_sub_comm (X p) (X i)]; exact abs_sub_le _ _ _
    _ < c / 2 + c / 2 := add_lt_add e1 e2
    _ = c := add_halves c

variable [CompactSpace Y]

/-- **§5, (L)**, for a `JonesSetting` and an abstract coordinate. Let `X` be continuous on a set
`W` which is a neighbourhood of every point `ℓ t`, `0 < t < 1`, of the base arc, with `X (ℓ t) = t`
there. For every `κ > 0` there is `η > 0` such that no piece `ℓ[u, β]` of the line, lying in the
strip `{p ∈ W : κ ≤ X p ≤ 1 − κ, d(p, ℓ (X p)) < η}`, has `X (ℓ β) ≤ X (ℓ u) − κ`. -/
theorem JonesSetting.no_backtrack (S : JonesSetting Y) {ℓ : ℝ → Y} (hℓ : IsLine ℓ) {W : Set Y}
    {X : Y → ℝ} (hX : ContinuousOn X W)
    (hbase : ∀ t ∈ Ioo (0 : ℝ) 1, X (ℓ t) = t ∧ W ∈ 𝓝 (ℓ t)) {κ : ℝ} (hκ : 0 < κ) :
    ∃ η > 0, ∀ u β, u ≤ β → (∀ v ∈ Icc u β, ℓ v ∈ W ∧ X (ℓ v) ∈ Icc κ (1 - κ) ∧
      dist (ℓ v) (ℓ (X (ℓ v))) < η) → X (ℓ u) - κ < X (ℓ β) := by
  obtain ⟨ε₀, hε₀, horient⟩ := S.orientation
  set K₀ := ℓ '' Icc (κ / 2) (1 - κ / 8) with hK₀
  have hIcc : ∀ t ∈ Icc (κ / 2) (1 - κ / 8), t ∈ Ioo (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨ε₁, hε₁, hunif⟩ := uniform_near_compact (isCompact_Icc.image hℓ.1)
    (by rintro _ ⟨t, ht, rfl⟩; exact (hbase t (hIcc t ht)).2) hX (by linarith : 0 < κ / 4)
  obtain ⟨δ, hδ, hEff⟩ := HPC.Effros.effros_homogeneous S.hom (lt_min hε₀ hε₁)
  refine ⟨δ, hδ, fun u β huβ hstrip => ?_⟩
  by_contra hback
  push_neg at hback
  set f : ℝ → ℝ := fun v => X (ℓ v) with hf
  have hfc : ContinuousOn f (Icc u β) :=
    hX.comp hℓ.1.continuousOn fun v hv => (hstrip v hv).1
  set s := f β with hs
  have hsI : s ∈ Icc κ (1 - κ) := (hstrip β ⟨huβ, le_rfl⟩).2.1
  set r := s + κ / 2 with hr
  -- the last time `u₁ ∈ [u, β]` with `f ≥ r`
  set T := {v ∈ Icc u β | r ≤ f v} with hT
  have hTc : IsClosed T := hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have huT : u ∈ T := ⟨⟨le_rfl, huβ⟩, by simp only [hf]; linarith⟩
  have hTb : BddAbove T := ⟨β, fun v hv => hv.1.2⟩
  set u₁ := sSup T with hu₁
  have hu₁T : u₁ ∈ T := hTc.csSup_mem ⟨u, huT⟩ hTb
  have hu₁β : u₁ < β := lt_of_le_of_ne hu₁T.1.2 fun e => by
    have := hu₁T.2; rw [e] at this; simp only [hf] at this hs; linarith
  have hafter : ∀ v, u₁ < v → v ≤ β → f v < r := fun v hv hvβ => by
    by_contra h
    push_neg at h
    have : v ≤ u₁ := le_csSup hTb ⟨⟨hu₁T.1.1.trans hv.le, hvβ⟩, h⟩
    linarith
  have hfu₁ : f u₁ = r := by
    have hsub : Icc u₁ β ⊆ Icc u β := Icc_subset_Icc hu₁T.1.1 le_rfl
    obtain ⟨v, hv, hvr⟩ := intermediate_value_Icc' hu₁β.le (hfc.mono hsub)
      ⟨(by simp only [hf] at hs ⊢; linarith : f β ≤ r), hu₁T.2⟩
    have hvu : v ≤ u₁ := le_csSup hTb ⟨hsub hv, hvr.ge⟩
    rw [← le_antisymm hvu hv.1]; exact hvr
  have hrI : r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hsI.1], by linarith [hsI.2]⟩
  -- the Effros homeomorphism `ℓ r ↦ ℓ u₁`, increasing on `ℓ` by (O)
  have hclose : dist (ℓ r) (ℓ u₁) < δ := by
    have := (hstrip u₁ hu₁T.1).2.2
    rw [show X (ℓ u₁) = r from hfu₁, dist_comm] at this
    exact this
  obtain ⟨h, hhr, hhsmall⟩ := hEff (ℓ r) (ℓ u₁) hclose
  have hsmall0 : ∀ x, dist x (h x) < ε₀ := fun x => by
    rw [dist_comm]; exact (hhsmall x).trans_le (min_le_left _ _)
  have hsmall1 : ∀ x, dist x (h x) < ε₁ := fun x => by
    rw [dist_comm]; exact (hhsmall x).trans_le (min_le_right _ _)
  obtain ⟨ψ, hψm, hψc, -, hψ⟩ := horient h hsmall0 _ (hℓ.shift r)
    (by
      simp only [zero_add, hhr]
      exact ⟨u₁ - r, by simp⟩)
  set Ψ : ℝ → ℝ := fun p => ψ (p - r) + r with hΨ
  have hΨe : ∀ p, h (ℓ p) = ℓ (Ψ p) := fun p => by
    have := hψ (p - r)
    simp only [sub_add_cancel] at this
    exact this
  have hΨm : StrictMono Ψ := fun a b hab => by
    simp only [hΨ]; linarith [hψm (show a - r < b - r by linarith)]
  have hΨc : Continuous Ψ := (hψc.comp (continuous_sub_right r)).add continuous_const
  have hΨr : Ψ r = u₁ := hℓ.2.1 ((hΨe r).symm.trans hhr)
  -- the key estimate: `X (h (ℓ t)) > t - κ/4` on the base
  have hest : ∀ t ∈ Icc (κ / 2) (1 - κ / 8), t - κ / 4 < X (h (ℓ t)) := fun t ht => by
    obtain ⟨-, habs⟩ := hunif (ℓ t) (mem_image_of_mem ℓ ht) (h (ℓ t)) (hsmall1 _)
    rw [(hbase t (hIcc t ht)).1] at habs
    linarith [neg_abs_le (X (h (ℓ t)) - t)]
  set t₀ := r + κ / 4 with ht₀
  have ht₀I : t₀ ∈ Icc (κ / 2) (1 - κ / 8) := ⟨by linarith [hsI.1], by linarith [hsI.2]⟩
  have hlt : u₁ < Ψ t₀ := hΨr ▸ hΨm (by linarith)
  rcases le_or_gt (Ψ t₀) β with hle | hgt
  · have h1 := hafter (Ψ t₀) hlt hle
    have h2 := hest t₀ ht₀I
    rw [hΨe] at h2
    simp only [hf] at h1
    linarith
  · obtain ⟨t', ht', ht'β⟩ := intermediate_value_Icc (by linarith : r ≤ t₀) hΨc.continuousOn
      ⟨hΨr ▸ hu₁β.le, hgt.le⟩
    have ht'I : t' ∈ Icc (κ / 2) (1 - κ / 8) :=
      ⟨by linarith [ht'.1, hsI.1], by linarith [ht'.2, ht₀I.2]⟩
    have h2 := hest t' ht'I
    rw [hΨe, ht'β] at h2
    simp only [hf] at hs
    linarith [ht'.1]

end General

section Plane

variable {M : Set Pt} [CompactSpace M]

/-- **§5, (L)**, collar form (commission 189 §5). Let `ℓ` be a line of a plane continuum `M`
satisfying `JonesSetting` (a compact subset of the plane; connectedness is not used), and `F` a collar (`IsCollar`) of its arc `γ = ℓ[0, 1]`. For every
`κ > 0` there is `η > 0` such that no piece `ℓ[u, β]` lying in the strip
`F([κ, 1 − κ] × (−η, η))` has its first collar coordinate decrease by `κ` or more: if `ℓ u = F(x₁, y₁)`
and `ℓ β = F(x₂, y₂)` (in the closed rectangle), then `x₂ > x₁ − κ`. (Shape: the skeleton left
§5 open with the placeholder `no_backtrack_in_collar : True`; this is the commission's claim.) -/
theorem no_backtrack_in_collar (S : JonesSetting M) {ℓ : ℝ → M} (hℓ : IsLine ℓ)
    {γ : unitInterval → Pt} (hγ : ∀ t : unitInterval, γ t = ℓ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {κ : ℝ} (hκ : 0 < κ) :
    ∃ η > 0, ∀ u β, u ≤ β → (∀ v ∈ Icc u β, ∃ x ∈ Icc κ (1 - κ), ∃ y ∈ Ioo (-η) η,
      (ℓ v : Pt) = F (x, y)) → ∀ x₁ y₁ x₂ y₂ : ℝ, (x₁, y₁) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 →
      (x₂, y₂) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → (ℓ u : Pt) = F (x₁, y₁) →
      (ℓ β : Pt) = F (x₂, y₂) → x₁ - κ < x₂ := by
  classical
  obtain ⟨hemb, h0, hopen⟩ := hF
  set R := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR
  set Ro := Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 with hRo
  set e := hemb.toHomeomorph with he
  have hRoR : Ro ⊆ R := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hmemr : ∀ q ∈ R, F q ∈ range (R.restrict F) := fun q hq => ⟨⟨q, hq⟩, rfl⟩
  -- the first collar coordinate
  let X : M → ℝ := fun p =>
    if h : (p : Pt) ∈ range (R.restrict F) then ((e.symm ⟨p, h⟩ : R) : ℝ × ℝ).1 else 0
  have hXF : ∀ (p : M) (q : ℝ × ℝ), q ∈ R → (p : Pt) = F q → X p = q.1 := by
    intro p q hq hpq
    have hm : (p : Pt) ∈ range (R.restrict F) := hpq ▸ hmemr q hq
    have h1 : e.symm ⟨p, hm⟩ = ⟨q, hq⟩ := by
      rw [Homeomorph.symm_apply_eq]
      apply Subtype.ext
      rw [he, IsEmbedding.toHomeomorph_apply_coe]
      exact hpq
    simp only [X, dif_pos hm, h1]
  set W : Set M := {p | (p : Pt) ∈ F '' Ro} with hW
  have hWo : IsOpen W := hopen.preimage continuous_subtype_val
  have hWr : ∀ p ∈ W, (p : Pt) ∈ range (R.restrict F) := fun p hp => by
    obtain ⟨q, hq, hqp⟩ := hp
    exact hqp ▸ hmemr q (hRoR hq)
  have hXc : ContinuousOn X W := by
    rw [continuousOn_iff_continuous_restrict]
    have : W.restrict X = fun w : W => ((e.symm ⟨(w : M), hWr w w.2⟩ : R) : ℝ × ℝ).1 := by
      funext w
      simp only [restrict, X, dif_pos (hWr w w.2)]
    rw [this]
    exact continuous_fst.comp (continuous_subtype_val.comp (e.symm.continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)))
  have hℓF : ∀ t ∈ Icc (0 : ℝ) 1, (ℓ t : Pt) = F (t, 0) := fun t ht => by
    have := h0 ⟨t, ht⟩
    rw [hγ] at this
    exact this.symm
  have hbase : ∀ t ∈ Ioo (0 : ℝ) 1, X (ℓ t) = t ∧ W ∈ 𝓝 (ℓ t) := fun t ht => by
    refine ⟨hXF _ (t, 0) ⟨Ioo_subset_Icc_self ht, by norm_num⟩
      (hℓF t (Ioo_subset_Icc_self ht)), hWo.mem_nhds ?_⟩
    exact ⟨(t, 0), ⟨ht, by norm_num⟩, (hℓF t (Ioo_subset_Icc_self ht)).symm⟩
  obtain ⟨η, hη, hL⟩ := S.no_backtrack hℓ hXc hbase hκ
  -- uniform continuity of `F` on the rectangle
  haveI : CompactSpace R := isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have huc := CompactSpace.uniformContinuous_of_continuous hemb.continuous
  obtain ⟨η', hη', hη'F⟩ := Metric.uniformContinuous_iff.1 huc η hη
  refine ⟨min η' 1, lt_min hη' one_pos, fun u β huβ hstrip x₁ y₁ x₂ y₂ h₁ h₂ hu hβ => ?_⟩
  have key : ∀ v ∈ Icc u β, ℓ v ∈ W ∧ X (ℓ v) ∈ Icc κ (1 - κ) ∧ dist (ℓ v) (ℓ (X (ℓ v))) < η := by
    intro v hv
    obtain ⟨x, hx, y, hy, hv⟩ := hstrip v hv
    have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hy1 : y ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hy.1, min_le_right η' 1], by linarith [hy.2, min_le_right η' 1]⟩
    have hxyR : (x, y) ∈ R := hRoR ⟨hxI, hy1⟩
    have hXv : X (ℓ v) = x := hXF _ _ hxyR hv
    refine ⟨⟨(x, y), ⟨hxI, hy1⟩, hv.symm⟩, hXv ▸ hx, ?_⟩
    rw [hXv, Subtype.dist_eq, hv, hℓF x (Ioo_subset_Icc_self hxI)]
    have hx0R : (x, (0 : ℝ)) ∈ R := ⟨Ioo_subset_Icc_self hxI, by norm_num⟩
    refine @hη'F ⟨(x, y), hxyR⟩ ⟨(x, 0), hx0R⟩ ?_
    rw [Subtype.dist_eq, Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
      max_eq_right (abs_nonneg y)]
    exact abs_lt.2 ⟨by linarith [hy.1, min_le_left η' 1], by linarith [hy.2, min_le_left η' 1]⟩
  have := hL u β huβ key
  rwa [hXF _ _ h₁ hu, hXF _ _ h₂ hβ] at this

end Plane

end HPC.Hagopian
