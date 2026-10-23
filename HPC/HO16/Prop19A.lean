import HPC.HO16.P19Ctx

/-!
# Batch 196, §3: Proposition 19, straightness and end sets (pp. 203–206)

(19.4)–(19.9): the sets `S′ᵢ` (`i ≠ i₀`), `S′_{i₀}`, `P′₁`, `P′₂` of p. 203 are straight, with
the end sets H–O compute.
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Prop19A

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A part of a sheet lying over a PL graph is a PL graph. -/
theorem isPLGraph_sheet_inter_preimage {Fi : Set (E × ℝ)} {A : Set E} (hFi : IsPLGraph Fi)
    (hinj : InjOn Prod.fst Fi) (hA : IsPLGraph A) (hAF : A ⊆ Prod.fst '' Fi) :
    IsPLGraph (Fi ∩ Prod.fst ⁻¹' A) := by
  obtain ⟨K, P, hK, hP, hKP⟩ := hFi.inter_preimage_fst hA
  rw [hKP] at ⊢
  refine isPLGraph_union_finite hK hP fun p hp => ?_
  rw [← hKP]
  have hpF : p ∈ Fi ∩ Prod.fst ⁻¹' A := by rw [hKP]; exact Or.inr hp
  rw [mem_closure_iff_nhds]
  intro N hN
  have h1 := image_fst_mem_nhdsWithin hFi.isCompact hinj hpF.1 hN
  have h2 : p.1 ∈ closure (A \ {p.1}) := hA.mem_closure_diff_finite hpF.2 (finite_singleton _)
  obtain ⟨_, ⟨x, ⟨hxN, hxF⟩, rfl⟩, hxA, hxp⟩ :=
    inter_nonempty_of_mem_nhdsWithin h1 h2 (diff_subset.trans hAF)
  exact ⟨x, hxN, ⟨hxF, hxA⟩, fun h => hxp (by rw [mem_singleton_iff.1 h]; exact mem_singleton _)⟩

variable {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
  {γ P₁ P₂ F₁ F₂ F₃ : Set (E × ℝ)}

namespace P19

variable (H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃)
include H

theorem relFrontier_F₁ : relFrontier (F₁ ∪ F₂ ∪ F₃) F₁ = F₁ ∩ F₂ :=
  (ho16_lemma6 H.hF).2.2.2.2.2.2.1
theorem relFrontier_F₃ : relFrontier (F₁ ∪ F₂ ∪ F₃) F₃ = F₂ ∩ F₃ :=
  (ho16_lemma6 H.hF).2.2.2.2.2.2.2.1
theorem relFrontier_F₂ : relFrontier (F₁ ∪ F₂ ∪ F₃) F₂ = (F₁ ∩ F₂) ∪ (F₂ ∩ F₃) :=
  (ho16_lemma6 H.hF).2.2.2.2.2.2.2.2.1

/-- **(19.4)**: for `i ≠ i₀`, `S′ᵢ = φ⋆⁻¹(Sᵢ)` is straight with `𝓔(S′ᵢ) = φ⋆⁻¹(αᵢ) ∪ φ⋆⁻¹(βᵢ)`. -/
theorem straight_T {i : ℕ} (hi : i ∈ Icc 1 k) (hi₀ : i ≠ i₀) :
    IsStraight (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) (T i)) ∧
    endSet (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) (T i)) =
      foldPre (F₁ ∪ F₂ ∪ F₃) (α i) ∪ foldPre (F₁ ∪ F₂ ∪ F₃) (α (i + 1)) := by
  have hT := (H.T_straight hi).2
  obtain ⟨hE, -⟩ := H.endSet_T hi hi₀
  have hi1 : i ∈ Icc 1 (k + 1) := ⟨hi.1, by have := hi.2; omega⟩
  have hi2 : i + 1 ∈ Icc 1 (k + 1) := ⟨by omega, by have := hi.2; omega⟩
  have hfr : relFrontier G (Prod.fst '' T i) = Prod.fst '' α i ∪ Prod.fst '' α (i + 1) := by
    rw [← hT.image_endSet, hE, image_union]
  have hV : Disjoint (relFrontier G (Prod.fst '' T i)) (relFrontier G (Prod.fst '' P₂)) := by
    rw [hfr, H.relFrontier_G₂]
    exact disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨H.disj_α_E hi1, H.disj_α_γ hi1⟩,
      disjoint_union_right.2 ⟨H.disj_α_E hi2, H.disj_α_γ hi2⟩⟩
  obtain ⟨h1, h2, -⟩ := ho16_lemma18 H.hF hT (Or.inl hV)
  refine ⟨h1, ?_⟩
  rw [h2, hE, foldPre_union, H.relFrontier_F₂]
  ext q
  refine ⟨fun h => h.1, fun hq' => ⟨hq', ?_⟩⟩
  rintro ⟨hq | hq, -⟩ <;> rcases hq' with hq' | hq'
  · exact H.pre_α_disj₁₂ hi1 (fst_mem_of_mem_foldPre hq').2 hq
  · exact H.pre_α_disj₁₂ hi2 (fst_mem_of_mem_foldPre hq').2 hq
  · exact H.pre_α_disj₂₃ hi1 (fst_mem_of_mem_foldPre hq').2 hq
  · exact H.pre_α_disj₂₃ hi2 (fst_mem_of_mem_foldPre hq').2 hq

/-- **(19.8)**: `P′₁ = φ⋆⁻¹(P₂) ∩ (F₁ ∪ F₂)⋆` is straight with `𝓔(P′₁) = φ⋆⁻¹(γ_{i₀})`. -/
theorem straight_P'₁ :
    IsStraight (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∧
    endSet (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) =
      foldPre (F₁ ∪ F₂ ∪ F₃) γ := by
  obtain ⟨-, -, h3, h4⟩ := ho16_lemma18 H.hF H.P₂_straight
    (Or.inr ⟨univ, univ_mem, subset_rfl⟩)
  refine ⟨h3, ?_⟩
  rw [h4, H.endSet_P₂, foldPre_union, H.relFrontier_F₁, H.relFrontier_F₃]
  ext q
  constructor
  · rintro (⟨⟨hqE | hqγ, hq12⟩, hqn⟩ | ⟨⟨hqP, hq12⟩, hq23, -⟩)
    · exfalso
      apply hqn
      refine ⟨?_, hqE.1.2⟩
      rw [← H.pre_E]
      exact ⟨hq12.1, (fst_mem_of_mem_foldPre hqE).2⟩
    · exact hqγ
    · refine ⟨hqP.1, phiStar_mem_of_injOn H.P₂_straight.2.2.1 H.γ_sub_P₂ hqP.2 ?_⟩
      have : q.1.1 ∈ Prod.fst '' (F₂ ∩ F₃) := ⟨q.1, hq23, rfl⟩
      rwa [H.fr23] at this
  · intro hq
    left
    refine ⟨⟨Or.inr hq, H.pre_γ_sub ⟨hq.1.1, (fst_mem_of_mem_foldPre hq).2⟩, hq.1.2⟩, ?_⟩
    rintro ⟨h12, -⟩
    exact Set.disjoint_left.1 H.pre_γ_disj₁₂ ⟨hq.1.1, (fst_mem_of_mem_foldPre hq).2⟩ h12

/-- `∂π(S_{i₀}) ∩ ∂π(P₂) ⊆ π(γ_{i₀})` (p. 205). -/
theorem frontier_inter_sub :
    relFrontier G (Prod.fst '' T i₀) ∩ relFrontier G (Prod.fst '' P₂) ⊆ Prod.fst '' γ := by
  have hT := (H.T_straight ⟨H.i₀_pos, H.i₀_le⟩).2
  rintro y ⟨hy1, hy2⟩
  rw [H.relFrontier_G₂] at hy2
  rcases hy2 with hy2 | hy2
  · exfalso
    rw [← hT.image_endSet, H.endSet_Ti₀, image_union, image_union] at hy1
    rcases hy1 with (hy1 | hy1) | hy1
    · exact Set.disjoint_left.1 (H.disj_α_E ⟨H.i₀_pos, by have := H.i₀_le; omega⟩) hy1 hy2
    · exact Set.disjoint_left.1 (H.disj_α_E ⟨by omega, by have := H.i₀_le; omega⟩) hy1 hy2
    · exact Set.disjoint_left.1 H.disj_Eγ_img hy2 hy1
  · exact hy2

/-- **(19.9)**: `P′₂ = φ⋆⁻¹(S_{i₀}) ∩ (F₁ ∪ F₂)⋆` is straight with
`𝓔(P′₂) = 𝓔(P′₁) ∪ γ′_{i₀+1}`. -/
theorem straight_P'₂ :
    IsStraight (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∧
    endSet (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) =
      foldPre (F₁ ∪ F₂ ∪ F₃) γ ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 := by
  have hT := (H.T_straight ⟨H.i₀_pos, H.i₀_le⟩).2
  obtain ⟨W, hW, hWeq⟩ := H.S3W
  have hV : ∃ V ∈ 𝓝ˢ (relFrontier G (Prod.fst '' T i₀) ∩ relFrontier G (Prod.fst '' P₂)),
      Prod.fst '' P₂ ∩ V ⊆ Prod.fst '' T i₀ ∩ V :=
    ⟨W, nhdsSet_mono H.frontier_inter_sub hW, hWeq.subset⟩
  obtain ⟨-, -, h3, h4⟩ := ho16_lemma18 H.hF hT (Or.inr hV)
  have hi₀1 : i₀ + 1 ∈ Icc 1 (k + 1) := ⟨by omega, by have := H.i₀_le; omega⟩
  refine ⟨h3, ?_⟩
  rw [h4, H.endSet_Ti₀, foldPre_union, foldPre_union, H.relFrontier_F₁, H.relFrontier_F₃]
  ext q
  constructor
  · rintro (⟨⟨(hqa | hqb) | hqγ, hq12⟩, hqn⟩ | ⟨⟨hqT, hq12⟩, hq23, -⟩)
    · exfalso
      exact (H.pre_αi₀ ⟨hqa.1.1, (fst_mem_of_mem_foldPre hqa).2⟩).2 hq12.1
    · exact Or.inr ⟨hqb, hq12⟩
    · exact Or.inl hqγ
    · refine Or.inl ⟨hqT.1, phiStar_mem_of_injOn hT.2.2.1 H.γ_sub_Ti₀ hqT.2 ?_⟩
      have : q.1.1 ∈ Prod.fst '' (F₂ ∩ F₃) := ⟨q.1, hq23, rfl⟩
      rwa [H.fr23] at this
  · rintro (hq | ⟨hq, hq12⟩)
    · left
      refine ⟨⟨Or.inr hq, H.pre_γ_sub ⟨hq.1.1, (fst_mem_of_mem_foldPre hq).2⟩, hq.1.2⟩, ?_⟩
      rintro ⟨h12, -⟩
      exact Set.disjoint_left.1 H.pre_γ_disj₁₂ ⟨hq.1.1, (fst_mem_of_mem_foldPre hq).2⟩ h12
    · left
      refine ⟨⟨Or.inl (Or.inr hq), hq12⟩, ?_⟩
      rintro ⟨h12, -⟩
      exact H.pre_α_disj₁₂ hi₀1 (fst_mem_of_mem_foldPre hq).2 h12

end P19

end Prop19A

end HPC.HO16
