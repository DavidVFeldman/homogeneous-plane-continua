import HPC.HO16.P19Lib

/-!
# Batch 196, §3: the hypotheses of Proposition 19 and the basic facts about the fold

`P19 …` bundles the hypotheses of `ho16_prop19_full`. The lemmas `P19.*` are the observations
H–O use on pp. 203–208: (19.1)–(19.3) for the sheets `Fᵢ`, the preimages of `π(𝓔(P₁))` and
`π(γ)`, and the disjointness facts from (S5′), (S6′).
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Ctx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The hypotheses of Proposition 19 in the full fold (`ho16_prop19_full`). -/
structure P19 (G : Set E) (S : Set (E × ℝ)) (k i₀ : ℕ) (T α : ℕ → Set (E × ℝ))
    (γ P₁ P₂ F₁ F₂ F₃ : Set (E × ℝ)) : Prop where
  hG : IsPLGraph G
  hconn : IsConnected G
  h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂
  hγ : γ.Nonempty
  hE : (endSet G P₁).Nonempty
  hF : IsSimpleFoldOf G (Prod.fst '' P₁) (Prod.fst '' P₂)
      (sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀)) F₁ F₂ F₃

variable {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
  {γ P₁ P₂ F₁ F₂ F₃ : Set (E × ℝ)}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_gen_list {i : ℕ} (hi : i ∈ Icc 2 k) :
    Prod.fst '' α i ∈ ((List.range' 2 (k - 1)).map fun i => Prod.fst '' α i) :=
  List.mem_map.2 ⟨i, List.mem_range'_1.2 ⟨hi.1, by have := hi.2; omega⟩, rfl⟩

namespace P19

variable (H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃)
include H

theorem i₀_pos : 1 ≤ i₀ := H.h.1
theorem i₀_le : i₀ ≤ k := H.h.2.1
theorem T_straight {i : ℕ} (hi : i ∈ Icc 1 k) : (T i).Nonempty ∧ IsStraight G (T i) :=
  H.h.2.2.1 i hi
theorem P₁_straight : IsStraight G P₁ := H.h.2.2.2.2.1
theorem P₂_straight : IsStraight G P₂ := H.h.2.2.2.2.2.2.1
theorem S_eq : S = (⋃ i ∈ Icc 1 k, T i) ∪ P₁ ∪ P₂ := H.h.2.2.2.2.2.2.2.1
theorem endSet_T {i : ℕ} (hi : i ∈ Icc 1 k) (hi₀ : i ≠ i₀) :
    endSet G (T i) = α i ∪ α (i + 1) ∧ Disjoint (α i) (α (i + 1)) :=
  H.h.2.2.2.2.2.2.2.2.1 i hi hi₀
theorem endSet_Ti₀ : endSet G (T i₀) = α i₀ ∪ α (i₀ + 1) ∪ γ := H.h.2.2.2.2.2.2.2.2.2.1
theorem disj_αα : Disjoint (α i₀) (α (i₀ + 1)) := H.h.2.2.2.2.2.2.2.2.2.2.1
theorem disj_αγ : Disjoint (α i₀) γ := H.h.2.2.2.2.2.2.2.2.2.2.2.1
theorem disj_α'γ : Disjoint (α (i₀ + 1)) γ := H.h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem α_finite {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) : (α i).Finite :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi
theorem γ_finite : γ.Finite := H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem α_one : α 1 = ∅ := H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem α_last : α (k + 1) = ∅ := H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem endSet_P₂ : endSet G P₂ = endSet G P₁ ∪ γ := H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem disj_Eγ : Disjoint (endSet G P₁) γ := H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S3 : ∀ i ∈ Ico 1 k, ∃ V ∈ 𝓝ˢ (Prod.fst '' α (i + 1)),
    Prod.fst '' T i ∩ V = Prod.fst '' T (i + 1) ∩ V :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S3W : ∃ W ∈ 𝓝ˢ (Prod.fst '' γ), Prod.fst '' P₂ ∩ W = Prod.fst '' T i₀ ∩ W :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S4 : ∀ i ∈ Icc 1 k, HasConsCompl G (Prod.fst '' T i) (Prod.fst '' α i) ∧
    HasConsCompl G (Prod.fst '' T i) (Prod.fst '' α (i + 1)) :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S4γ : HasConsCompl G (Prod.fst '' T i₀) (Prod.fst '' γ) :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem gen : IsGeneric G (((List.range' 2 (k - 1)).map fun i => Prod.fst '' α i) ++
    [Prod.fst '' endSet G P₁, Prod.fst '' γ]) :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S6 : Disjoint (Prod.fst '' α i₀) (Prod.fst '' (P₁ ∪ P₂)) :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem S3V : ∃ V ∈ 𝓝ˢ (Prod.fst '' endSet G P₁), Prod.fst '' P₁ ∩ V = Prod.fst '' P₂ ∩ V :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S4P₂E : HasConsCompl G (Prod.fst '' P₂) (Prod.fst '' endSet G P₁) :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem S4P₂γ : HasConsCompl G (Prod.fst '' P₂) (Prod.fst '' γ) :=
  H.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fold :
    IsFoldTriple G (Prod.fst '' P₁) (Prod.fst '' P₂) (sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀)) ∧
    Prod.fst '' P₁ = sideOf G (Prod.fst '' endSet G P₁) (Prod.fst '' P₂) ∧
    sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀) = sideOf G (Prod.fst '' γ) (Prod.fst '' P₂) ∧
    relFrontier G (Prod.fst '' P₁) = Prod.fst '' endSet G P₁ ∧
    relFrontier G (sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀)) = Prod.fst '' γ ∧
    relFrontier G (Prod.fst '' P₂) = Prod.fst '' endSet G P₁ ∪ Prod.fst '' γ :=
  ho16_prop19_fold H.hG H.hconn H.h H.hE

theorem FPL : IsPLGraph (F₁ ∪ F₂ ∪ F₃) := H.hF.isPLGraph_union
theorem Fclosed : IsClosed (F₁ ∪ F₂ ∪ F₃) := H.FPL.isCompact.isClosed
theorem imgF : Prod.fst '' (F₁ ∪ F₂ ∪ F₃) = G := H.hF.image_union
theorem F₁PL : IsPLGraph F₁ := H.hF.2.1
theorem F₂PL : IsPLGraph F₂ := H.hF.2.2.1
theorem F₃PL : IsPLGraph F₃ := H.hF.2.2.2.1
theorem inj₁ : InjOn Prod.fst F₁ := H.hF.2.2.2.2.1
theorem img₁ : Prod.fst '' F₁ = Prod.fst '' P₁ := H.hF.2.2.2.2.2.1
theorem inj₂ : InjOn Prod.fst F₂ := H.hF.2.2.2.2.2.2.1
theorem img₂ : Prod.fst '' F₂ = Prod.fst '' P₂ := H.hF.2.2.2.2.2.2.2.1
theorem inj₃ : InjOn Prod.fst F₃ := H.hF.2.2.2.2.2.2.2.2.1
theorem img₃ : Prod.fst '' F₃ = sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀) :=
  H.hF.2.2.2.2.2.2.2.2.2.1
theorem disj₁₃ : Disjoint F₁ F₃ := H.hF.2.2.2.2.2.2.2.2.2.2.2.2

/-- (19.1) for the sheets: `φ(F₁ ∩ F₂) = π(𝓔(P₁))`. -/
theorem fr12 : Prod.fst '' (F₁ ∩ F₂) = Prod.fst '' endSet G P₁ := by
  rw [H.hF.2.2.2.2.2.2.2.2.2.2.1, H.fold.2.2.2.1]

/-- (19.2) for the sheets: `φ(F₂ ∩ F₃) = π(γ)`. -/
theorem fr23 : Prod.fst '' (F₂ ∩ F₃) = Prod.fst '' γ := by
  rw [H.hF.2.2.2.2.2.2.2.2.2.2.2.1, H.fold.2.2.2.2.1]

theorem relFrontier_G₂ : relFrontier G (Prod.fst '' P₂) =
    Prod.fst '' endSet G P₁ ∪ Prod.fst '' γ := H.fold.2.2.2.2.2

theorem Ti₀_sub_img₃ : Prod.fst '' T i₀ ⊆ Prod.fst '' F₃ := by
  rw [H.img₃]
  have hT := (H.T_straight ⟨H.i₀_pos, H.i₀_le⟩).2
  exact hT.2.2.2.subset_sideOf hT.image_subset (H.γ_finite.image _)

theorem γ_sub_Ti₀ : γ ⊆ T i₀ := by
  have := endSet_subset G (T i₀); rw [H.endSet_Ti₀] at this
  exact subset_union_right.trans this

theorem γ_sub_P₂ : γ ⊆ P₂ := by
  have := endSet_subset G P₂; rw [H.endSet_P₂] at this
  exact subset_union_right.trans this

theorem E_sub_P₂ : endSet G P₁ ⊆ P₂ := by
  have := endSet_subset G P₂; rw [H.endSet_P₂] at this
  exact subset_union_left.trans this

theorem αi₀_sub_Ti₀ : α i₀ ⊆ T i₀ := by
  have := endSet_subset G (T i₀); rw [H.endSet_Ti₀] at this
  exact subset_union_left.trans (subset_union_left.trans this)

theorem αi₀1_sub_Ti₀ : α (i₀ + 1) ⊆ T i₀ := by
  have := endSet_subset G (T i₀); rw [H.endSet_Ti₀] at this
  exact subset_union_right.trans (subset_union_left.trans this)

/-! ### Genericity -/

theorem gen_cross : ∀ a ∈ ((List.range' 2 (k - 1)).map fun i => Prod.fst '' α i),
    Disjoint a (Prod.fst '' endSet G P₁) ∧ Disjoint a (Prod.fst '' γ) := by
  have h := (List.pairwise_append.1 H.gen.2).2.2
  intro a ha
  exact ⟨h a ha _ (by simp), h a ha _ (by simp)⟩

theorem disj_Eγ_img : Disjoint (Prod.fst '' endSet G P₁) (Prod.fst '' γ) := by
  have h := (List.pairwise_append.1 H.gen.2).2.1
  simpa using h

theorem disj_α_E {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) :
    Disjoint (Prod.fst '' α i) (Prod.fst '' endSet G P₁) := by
  rcases eq_or_ne i 1 with rfl | h1
  · rw [H.α_one, image_empty]; exact empty_disjoint _
  rcases eq_or_ne i (k + 1) with rfl | h2
  · rw [H.α_last, image_empty]; exact empty_disjoint _
  exact (H.gen_cross _ (mem_gen_list ⟨by have := hi.1; omega, by have := hi.2; omega⟩)).1

theorem disj_α_γ {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) :
    Disjoint (Prod.fst '' α i) (Prod.fst '' γ) := by
  rcases eq_or_ne i 1 with rfl | h1
  · rw [H.α_one, image_empty]; exact empty_disjoint _
  rcases eq_or_ne i (k + 1) with rfl | h2
  · rw [H.α_last, image_empty]; exact empty_disjoint _
  exact (H.gen_cross _ (mem_gen_list ⟨by have := hi.1; omega, by have := hi.2; omega⟩)).2

theorem ordinary_E {y : E} (hy : y ∈ Prod.fst '' endSet G P₁) : IsOrdinaryPt G y :=
  (H.gen.1 _ (by simp)).2.2 y hy

theorem ordinary_γ {y : E} (hy : y ∈ Prod.fst '' γ) : IsOrdinaryPt G y :=
  (H.gen.1 _ (by simp)).2.2 y hy

theorem ordinary_frontier : ∀ y ∈ relFrontier G (Prod.fst '' P₂), IsOrdinaryPt G y := by
  intro y hy
  rw [H.relFrontier_G₂] at hy
  rcases hy with hy | hy
  · exact H.ordinary_E hy
  · exact H.ordinary_γ hy

/-! ### Preimages -/

/-- `φ⁻¹(π(𝓔(P₁))) ∩ (F₁ ∪ F₂) = ∂F₁` (p. 205, first observation). -/
theorem pre_E : (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' endSet G P₁) = F₁ ∩ F₂ := by
  rw [← H.fr12, union_inter_distrib_right,
    inter_preimage_image_of_injOn H.inj₁ inter_subset_left,
    inter_preimage_image_of_injOn H.inj₂ inter_subset_right, union_self]

/-- `φ⁻¹(π(γ)) ∩ F₃ = ∂F₃`. -/
theorem pre_γ₃ : F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' γ) = F₂ ∩ F₃ := by
  rw [← H.fr23, inter_preimage_image_of_injOn H.inj₃ inter_subset_right]

/-- `φ⁻¹(π(γ)) ∩ F₂ = ∂F₃`. -/
theorem pre_γ₂ : F₂ ∩ Prod.fst ⁻¹' (Prod.fst '' γ) = F₂ ∩ F₃ := by
  rw [← H.fr23, inter_preimage_image_of_injOn H.inj₂ inter_subset_left]

/-- `φ⁻¹(π(γ)) ⊆ F₁ ∪ F₂` (p. 205, second observation). -/
theorem pre_γ_sub : (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' γ) ⊆ F₁ ∪ F₂ := by
  rintro x ⟨(h | h) | h, hx⟩
  · exact Or.inl h
  · exact Or.inr h
  · have : x ∈ F₂ ∩ F₃ := H.pre_γ₃ ▸ ⟨h, hx⟩
    exact Or.inr this.1

/-- `φ⁻¹(π(γ)) ∩ ∂F₁ = ∅`. -/
theorem pre_γ_disj₁₂ : Disjoint ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' γ)) (F₁ ∩ F₂) := by
  refine Set.disjoint_left.2 fun x hx h12 => ?_
  have : x.1 ∈ Prod.fst '' endSet G P₁ := by rw [← H.fr12]; exact ⟨x, h12, rfl⟩
  exact Set.disjoint_left.1 H.disj_Eγ_img this hx.2

/-- (S6′): `φ⁻¹(π(α_{i₀})) ⊆ F₃ \ F₂`. -/
theorem pre_αi₀ : (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' α i₀) ⊆ F₃ \ (F₁ ∪ F₂) := by
  rintro x ⟨hx, hxα⟩
  have h12 : x ∉ F₁ ∪ F₂ := by
    rintro (h | h)
    · have : x.1 ∈ Prod.fst '' P₁ := by rw [← H.img₁]; exact ⟨x, h, rfl⟩
      exact Set.disjoint_left.1 H.S6 hxα (by rw [image_union]; exact Or.inl this)
    · have : x.1 ∈ Prod.fst '' P₂ := by rw [← H.img₂]; exact ⟨x, h, rfl⟩
      exact Set.disjoint_left.1 H.S6 hxα (by rw [image_union]; exact Or.inr this)
  rcases hx with h | h
  · exact absurd h h12
  · exact ⟨h, h12⟩

/-- Points over `π(αᵢ)` are not glueing points. -/
theorem pre_α_disj₁₂ {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) {x : E × ℝ}
    (hx : x.1 ∈ Prod.fst '' α i) : x ∉ F₁ ∩ F₂ := fun h12 => by
  have : x.1 ∈ Prod.fst '' endSet G P₁ := by rw [← H.fr12]; exact ⟨x, h12, rfl⟩
  exact Set.disjoint_left.1 (H.disj_α_E hi) hx this

theorem pre_α_disj₂₃ {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) {x : E × ℝ}
    (hx : x.1 ∈ Prod.fst '' α i) : x ∉ F₂ ∩ F₃ := fun h23 => by
  have : x.1 ∈ Prod.fst '' γ := by rw [← H.fr23]; exact ⟨x, h23, rfl⟩
  exact Set.disjoint_left.1 (H.disj_α_γ hi) hx this

/-- A point of `G` has a preimage in `F`. -/
theorem exists_lift {y : E} (hy : y ∈ G) : ∃ x ∈ F₁ ∪ F₂ ∪ F₃, x.1 = y := by
  rw [← H.imgF] at hy; exact hy

end P19

end Ctx

end HPC.HO16
