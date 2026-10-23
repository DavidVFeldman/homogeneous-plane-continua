import HPC.HO16.Prop19A

/-!
# Batch 196, §3: Proposition 19, the level `i₀` (pp. 204–205)

`S′_{i₀} = [φ⋆⁻¹(P₁) ∩ (F₁)⋆] ∪ [φ⋆⁻¹(P₂) ∩ (F₂)⋆] ∪ [φ⋆⁻¹(S_{i₀}) ∩ (F₃)⋆]` is straight
("clearly … straight", p. 204, supplied), `π(S′_{i₀}) = F₁ ∪ F₂ ∪ (F₃ ∩ φ⁻¹(π(S_{i₀})))`, and
(19.5)–(19.6) with (S6′): `𝓔(S′_{i₀}) = φ⋆⁻¹(α_{i₀}) ∪ (φ⋆⁻¹(β_{i₀}) ∩ (F₃)⋆)`.
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Prop19B

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
  {γ P₁ P₂ F₁ F₂ F₃ : Set (E × ℝ)}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem p19T_self (F₁ F₂ F₃ : Set (E × ℝ)) (T : ℕ → Set (E × ℝ)) (P₁ P₂ : Set (E × ℝ))
    (i₀ : ℕ) :
    p19T F₁ F₂ F₃ T P₁ P₂ i₀ i₀ =
      foldPre (F₁ ∪ F₂ ∪ F₃) P₁ ∩ F₁ ×ˢ Icc (0 : ℝ) 1 ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ F₂ ×ˢ Icc (0 : ℝ) 1 ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ F₃ ×ˢ Icc (0 : ℝ) 1 := if_pos rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem p19T_ne (F₁ F₂ F₃ : Set (E × ℝ)) (T : ℕ → Set (E × ℝ)) (P₁ P₂ : Set (E × ℝ))
    {i₀ i : ℕ} (h : i ≠ i₀) :
    p19T F₁ F₂ F₃ T P₁ P₂ i₀ i = foldPre (F₁ ∪ F₂ ∪ F₃) (T i) := if_neg h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem p19α_succ (F₁ F₂ F₃ : Set (E × ℝ)) (α : ℕ → Set (E × ℝ)) (i₀ : ℕ) :
    p19α F₁ F₂ F₃ α i₀ (i₀ + 1) = foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ F₃ ×ˢ Icc (0 : ℝ) 1 :=
  if_pos rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem p19α_ne (F₁ F₂ F₃ : Set (E × ℝ)) (α : ℕ → Set (E × ℝ)) {i₀ i : ℕ} (h : i ≠ i₀ + 1) :
    p19α F₁ F₂ F₃ α i₀ i = foldPre (F₁ ∪ F₂ ∪ F₃) (α i) := if_neg h

omit [NormedSpace ℝ E] in
theorem eq_of_phiStar_eq {q q' : (E × ℝ) × ℝ} (h1 : q.1 = q'.1) (h2 : phiStar q = phiStar q') :
    q = q' :=
  Prod.ext h1 (by have h3 := congrArg Prod.snd h2; exact h3)

namespace P19

variable (H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃)
include H

theorem Ti₀_straight : IsStraight G (T i₀) := (H.T_straight ⟨H.i₀_pos, H.i₀_le⟩).2

theorem γ_img_sub : Prod.fst '' γ ⊆ Prod.fst '' T i₀ := image_mono H.γ_sub_Ti₀

/-- `π(S′_{i₀}) = F₁ ∪ F₂ ∪ (F₃ ∩ φ⁻¹(π(S_{i₀})))`. -/
theorem image_T'₀ : Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ i₀ =
    F₁ ∪ F₂ ∪ (F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀)) := by
  rw [p19T_self, image_union, image_union, image_foldPre_inter H.P₁_straight.1,
    image_foldPre_inter H.P₂_straight.1, image_foldPre_inter H.Ti₀_straight.1,
    inter_eq_right.2 (subset_union_left.trans subset_union_left : F₁ ⊆ F₁ ∪ F₂ ∪ F₃),
    inter_eq_right.2 (subset_union_right.trans subset_union_left : F₂ ⊆ F₁ ∪ F₂ ∪ F₃),
    inter_eq_right.2 (subset_union_right : F₃ ⊆ F₁ ∪ F₂ ∪ F₃), ← H.img₁, ← H.img₂,
    inter_preimage_image_of_injOn H.inj₁ subset_rfl,
    inter_preimage_image_of_injOn H.inj₂ subset_rfl]

theorem isPLGraph_image_T'₀ :
    IsPLGraph (F₁ ∪ F₂ ∪ (F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀))) :=
  (H.F₁PL.union H.F₂PL).union
    (isPLGraph_sheet_inter_preimage H.F₃PL H.inj₃ H.Ti₀_straight.2.2.2 H.Ti₀_sub_img₃)

/-- The complement of `π(S′_{i₀})` in `F` lies in `F₃` over `G \ π(S_{i₀})`. -/
theorem compl_image_T'₀ : (F₁ ∪ F₂ ∪ F₃) \ (F₁ ∪ F₂ ∪ (F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀))) =
    F₃ ∩ Prod.fst ⁻¹' (G \ Prod.fst '' T i₀) := by
  ext x
  constructor
  · rintro ⟨hxF, hxX⟩
    have h1 : x ∉ F₁ := fun h => hxX (Or.inl (Or.inl h))
    have h2 : x ∉ F₂ := fun h => hxX (Or.inl (Or.inr h))
    have h3 : x ∈ F₃ := by
      rcases hxF with (h | h) | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    refine ⟨h3, ?_, fun hA => hxX (Or.inr ⟨h3, hA⟩)⟩
    rw [← H.imgF]; exact ⟨x, hxF, rfl⟩
  · rintro ⟨h3, hxG, hxA⟩
    refine ⟨Or.inr h3, ?_⟩
    rintro ((h | h) | h)
    · exact Set.disjoint_left.1 H.disj₁₃ h h3
    · have : x.1 ∈ Prod.fst '' (F₂ ∩ F₃) := ⟨x, ⟨h, h3⟩, rfl⟩
      rw [H.fr23] at this
      exact hxA (H.γ_img_sub this)
    · exact hxA h.2

/-- (19.5): `∂π(S′_{i₀}) = (F₃ \ F₂) ∩ φ⁻¹(∂π(S_{i₀}))`. -/
theorem relFrontier_T'₀ :
    relFrontier (F₁ ∪ F₂ ∪ F₃) (F₁ ∪ F₂ ∪ (F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀))) =
      (F₃ \ F₂) ∩ Prod.fst ⁻¹' relFrontier G (Prod.fst '' T i₀) := by
  have hXc := H.isPLGraph_image_T'₀.isCompact.isClosed
  have hAc : IsClosed (Prod.fst '' T i₀) := H.Ti₀_straight.2.2.2.isCompact.isClosed
  have hF₃c : IsClosed F₃ := H.F₃PL.isCompact.isClosed
  unfold relFrontier
  rw [hXc.closure_eq, H.compl_image_T'₀]
  ext x
  constructor
  · rintro ⟨hxX, hxc⟩
    have hx3 : x ∈ F₃ := closure_minimal inter_subset_left hF₃c hxc
    have hxGA : x.1 ∈ closure (G \ Prod.fst '' T i₀) :=
      map_mem_closure continuous_fst hxc fun p hp => hp.2
    have hxA : x.1 ∈ Prod.fst '' T i₀ := by
      rcases hxX with (h | h) | h
      · exact absurd hx3 (Set.disjoint_left.1 H.disj₁₃ h)
      · have : x.1 ∈ Prod.fst '' (F₂ ∩ F₃) := ⟨x, ⟨h, hx3⟩, rfl⟩
        rw [H.fr23] at this
        exact H.γ_img_sub this
      · exact h.2
    refine ⟨⟨hx3, fun hx2 => ?_⟩, subset_closure hxA, hxGA⟩
    -- near `π(γ)`, `π(S_{i₀})` agrees with `φ(F₃)`
    have hγ : x.1 ∈ Prod.fst '' γ := by
      rw [← H.fr23]; exact ⟨x, ⟨hx2, hx3⟩, rfl⟩
    have hB : Prod.fst '' γ ⊆ relFrontier G (Prod.fst '' T i₀) := by
      rw [← H.Ti₀_straight.image_endSet, H.endSet_Ti₀]
      exact image_mono subset_union_right
    obtain ⟨-, -, -, -, V, hV, hVeq⟩ := ho16_obs9_char H.hG H.Ti₀_straight.2.2.2
      H.Ti₀_straight.image_subset hB H.S4γ
    have hVx : Prod.fst ⁻¹' V ∈ 𝓝 x :=
      continuous_fst.continuousAt.preimage_mem_nhds (mem_nhdsSet_iff_forall.1 hV _ hγ)
    obtain ⟨x', hx'V, hx'3, -, hx'A⟩ := mem_closure_iff_nhds.1 hxc _ hVx
    have hx'σ : x'.1 ∈ sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀) := by
      rw [← H.img₃]; exact ⟨x', hx'3, rfl⟩
    have : x'.1 ∈ Prod.fst '' T i₀ ∩ V := by rw [← hVeq]; exact ⟨hx'σ, hx'V⟩
    exact hx'A this.1
  · rintro ⟨⟨hx3, hx2⟩, hxA, hxGA⟩
    rw [hAc.closure_eq] at hxA
    refine ⟨Or.inr ⟨hx3, hxA⟩, ?_⟩
    have hloc := (ho16_lemma6 H.hF).2.2.2.2.2.2.2.2.2.2.2.2.2
    exact lift_mem_closure (hloc x ⟨hx3, hx2⟩) diff_subset hxGA

/-- `S′_{i₀}` is straight (p. 204). -/
theorem straight_T'₀ : IsStraight (F₁ ∪ F₂ ∪ F₃) (p19T F₁ F₂ F₃ T P₁ P₂ i₀ i₀) := by
  have hFc := H.Fclosed
  have hF₁c := H.F₁PL.isCompact.isClosed
  have hF₂c := H.F₂PL.isCompact.isClosed
  have hF₃c := H.F₃PL.isCompact.isClosed
  have hP₁ := H.P₁_straight
  have hP₂ := H.P₂_straight
  have hT := H.Ti₀_straight
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p19T_self]
    rintro q ((h | h) | h)
    · exact h.1.1
    · exact h.1.1
    · exact h.1.1
  · rw [p19T_self]
    exact (((isClosed_foldPre hFc hP₁.2.1).inter (hF₁c.prod isClosed_Icc)).union
      ((isClosed_foldPre hFc hP₂.2.1).inter (hF₂c.prod isClosed_Icc))).union
      ((isClosed_foldPre hFc hT.2.1).inter (hF₃c.prod isClosed_Icc))
  · -- injectivity
    have same : ∀ {X : Set (E × ℝ)}, InjOn Prod.fst X → ∀ {q q' : (E × ℝ) × ℝ},
        phiStar q ∈ X → phiStar q' ∈ X → q.1 = q'.1 → q = q' := by
      intro X hX q q' hq hq' h1
      exact eq_of_phiStar_eq h1 (hX hq hq' (by simp [phiStar, h1]))
    have cross12 : ∀ {q q' : (E × ℝ) × ℝ}, q ∈ foldPre (F₁ ∪ F₂ ∪ F₃) P₁ ∩ F₁ ×ˢ Icc (0 : ℝ) 1 →
        q' ∈ foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ F₂ ×ˢ Icc (0 : ℝ) 1 → q.1 = q'.1 → q = q' := by
      intro q q' hq hq' h1
      have h12 : q.1 ∈ F₁ ∩ F₂ := ⟨hq.2.1, h1 ▸ hq'.2.1⟩
      have hE : phiStar q ∈ endSet G P₁ :=
        phiStar_mem_of_injOn hP₁.2.2.1 (endSet_subset G P₁) hq.1.2
          (by rw [← H.fr12]; exact ⟨q.1, h12, rfl⟩)
      exact same hP₂.2.2.1 (H.E_sub_P₂ hE) hq'.1.2 h1
    have cross23 : ∀ {q q' : (E × ℝ) × ℝ}, q ∈ foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ F₂ ×ˢ Icc (0 : ℝ) 1 →
        q' ∈ foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ F₃ ×ˢ Icc (0 : ℝ) 1 → q.1 = q'.1 → q = q' := by
      intro q q' hq hq' h1
      have h23 : q.1 ∈ F₂ ∩ F₃ := ⟨hq.2.1, h1 ▸ hq'.2.1⟩
      have hγ : q.1.1 ∈ Prod.fst '' γ := by rw [← H.fr23]; exact ⟨q.1, h23, rfl⟩
      have h1' : phiStar q ∈ γ := phiStar_mem_of_injOn hP₂.2.2.1 H.γ_sub_P₂ hq.1.2 hγ
      have h2' : phiStar q' ∈ γ := phiStar_mem_of_injOn hT.2.2.1 H.γ_sub_Ti₀ hq'.1.2 (h1 ▸ hγ)
      exact same hP₂.2.2.1 (H.γ_sub_P₂ h1') (H.γ_sub_P₂ h2') h1
    have cross13 : ∀ {q q' : (E × ℝ) × ℝ}, q ∈ foldPre (F₁ ∪ F₂ ∪ F₃) P₁ ∩ F₁ ×ˢ Icc (0 : ℝ) 1 →
        q' ∈ foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ F₃ ×ˢ Icc (0 : ℝ) 1 → q.1 = q'.1 → q = q' := by
      intro q q' hq hq' h1
      exact absurd (h1 ▸ hq'.2.1) (Set.disjoint_left.1 H.disj₁₃ hq.2.1)
    rw [p19T_self]
    rintro q ((hq | hq) | hq) q' ((hq' | hq') | hq') h1
    · exact same hP₁.2.2.1 hq.1.2 hq'.1.2 h1
    · exact cross12 hq hq' h1
    · exact cross13 hq hq' h1
    · exact (cross12 hq' hq h1.symm).symm
    · exact same hP₂.2.2.1 hq.1.2 hq'.1.2 h1
    · exact cross23 hq hq' h1
    · exact (cross13 hq' hq h1.symm).symm
    · exact (cross23 hq' hq h1.symm).symm
    · exact same hT.2.2.1 hq.1.2 hq'.1.2 h1
  · rw [H.image_T'₀]; exact H.isPLGraph_image_T'₀

/-- **(19.6) with (S6′)** (pp. 205–206): `𝓔(S′_{i₀}) = α′_{i₀} ∪ β′_{i₀}`, where
`α′_{i₀} = φ⋆⁻¹(α_{i₀})` and `β′_{i₀} = φ⋆⁻¹(β_{i₀}) ∩ (F₃)⋆`. -/
theorem endSet_T'₀ : endSet (F₁ ∪ F₂ ∪ F₃) (p19T F₁ F₂ F₃ T P₁ P₂ i₀ i₀) =
    foldPre (F₁ ∪ F₂ ∪ F₃) (α i₀) ∪
      foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ F₃ ×ˢ Icc (0 : ℝ) 1 := by
  have hT := H.Ti₀_straight
  have hi₀ : i₀ ∈ Icc 1 (k + 1) := ⟨H.i₀_pos, by have := H.i₀_le; omega⟩
  have hi₀1 : i₀ + 1 ∈ Icc 1 (k + 1) := ⟨by omega, by have := H.i₀_le; omega⟩
  have hfrA : relFrontier G (Prod.fst '' T i₀) =
      Prod.fst '' α i₀ ∪ Prod.fst '' α (i₀ + 1) ∪ Prod.fst '' γ := by
    rw [← hT.image_endSet, H.endSet_Ti₀, image_union, image_union]
  unfold endSet
  rw [H.image_T'₀, H.relFrontier_T'₀]
  ext q
  constructor
  · rintro ⟨hq, hq3, hqfr⟩
    have hq' : q ∈ foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ F₃ ×ˢ Icc (0 : ℝ) 1 := by
      rw [p19T_self] at hq
      rcases hq with (h | h) | h
      · exact absurd hq3.1 (Set.disjoint_left.1 H.disj₁₃ h.2.1)
      · exact absurd h.2.1 hq3.2
      · exact h
    have hE : phiStar q ∈ endSet G (T i₀) :=
      phiStar_mem_of_injOn hT.2.2.1 (endSet_subset G (T i₀)) hq'.1.2
        (by rw [hT.image_endSet]; exact hqfr)
    rw [H.endSet_Ti₀] at hE
    rcases hE with (h | h) | h
    · exact Or.inl ⟨hq'.1.1, h⟩
    · exact Or.inr ⟨⟨hq'.1.1, h⟩, hq'.2⟩
    · exfalso
      have : q.1 ∈ F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' γ) := ⟨hq3.1, phiStar q, h, rfl⟩
      rw [H.pre_γ₃] at this
      exact hq3.2 this.1
  · rintro (hq | ⟨hq, hq3⟩)
    · have h3 := H.pre_αi₀ ⟨hq.1.1, (fst_mem_of_mem_foldPre hq).2⟩
      refine ⟨?_, ⟨h3.1, fun h2 => h3.2 (Or.inr h2)⟩, ?_⟩
      · rw [p19T_self]
        exact Or.inr ⟨⟨hq.1, H.αi₀_sub_Ti₀ hq.2⟩, h3.1, hq.1.2⟩
      · rw [hfrA]; exact Or.inl (Or.inl (fst_mem_of_mem_foldPre hq).2)
    · refine ⟨?_, ⟨hq3.1, fun h2 => H.pre_α_disj₂₃ hi₀1 (fst_mem_of_mem_foldPre hq).2
        ⟨h2, hq3.1⟩⟩, ?_⟩
      · rw [p19T_self]
        exact Or.inr ⟨⟨hq.1, H.αi₀1_sub_Ti₀ hq.2⟩, hq3⟩
      · rw [hfrA]; exact Or.inl (Or.inr (fst_mem_of_mem_foldPre hq).2)

end P19

end Prop19B

end HPC.HO16
