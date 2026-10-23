import HPC.HO16.Prop19D

/-!
# Batch 196, §3: Proposition 19 in the full fold (`ho16_prop19_full`)

The assembly of H–O's proof, pp. 203–208: (S1′)–(S6′) for the sets of p. 203 in any simple fold
with the `Gᵢ` of p. 202 (`ho16_prop19_fold`).
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Prop19

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem foldPre_split (F Fa Fb X : Set (E × ℝ)) (hF : F ⊆ Fa ∪ Fb) :
    foldPre F X = foldPre F X ∩ Fa ×ˢ Icc (0 : ℝ) 1 ∪ foldPre F X ∩ Fb ×ˢ Icc (0 : ℝ) 1 := by
  ext q
  constructor
  · intro hq
    rcases hF hq.1.1 with h | h
    · exact Or.inl ⟨hq, h, hq.1.2⟩
    · exact Or.inr ⟨hq, h, hq.1.2⟩
  · rintro (h | h) <;> exact h.1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A lift of a point of `X` to a sheet `Fi` lies in `φ⋆⁻¹(X) ∩ (Fi)⋆`. -/
theorem lift_mem_foldPre {G : Set E} {F Fi X : Set (E × ℝ)} (hXG : X ⊆ G ×ˢ Icc (0 : ℝ) 1)
    (hFi : Fi ⊆ F) {t p : E × ℝ} (ht : t ∈ X) (hp : p ∈ Fi) (hpt : p.1 = t.1) :
    ((p, t.2) : (E × ℝ) × ℝ) ∈ foldPre F X ∩ Fi ×ˢ Icc (0 : ℝ) 1 := by
  have h2 : t.2 ∈ Icc (0 : ℝ) 1 := (hXG ht).2
  refine ⟨⟨⟨hFi hp, h2⟩, ?_⟩, hp, h2⟩
  show (p.1, t.2) ∈ X
  rw [hpt]; exact ht

variable {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
  {γ P₁ P₂ F₁ F₂ F₃ : Set (E × ℝ)}

namespace P19

variable (H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃)
include H

/-- (S1′): the levels are nonempty and straight. -/
theorem S1'T {i : ℕ} (hi : i ∈ Icc 1 k) :
    (p19T F₁ F₂ F₃ T P₁ P₂ i₀ i).Nonempty ∧
      IsStraight (F₁ ∪ F₂ ∪ F₃) (p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) := by
  obtain ⟨⟨t, ht⟩, hT⟩ := H.T_straight hi
  rcases eq_or_ne i i₀ with rfl | hne
  · refine ⟨?_, H.straight_T'₀⟩
    obtain ⟨p, hp, hpt⟩ := H.Ti₀_sub_img₃ ⟨t, ht, rfl⟩
    rw [p19T_self]
    exact ⟨_, Or.inr (lift_mem_foldPre hT.1 subset_union_right ht hp hpt)⟩
  · refine ⟨?_, by rw [p19T_ne _ _ _ _ _ _ hne]; exact (H.straight_T hi hne).1⟩
    obtain ⟨p, hp, hpt⟩ := H.exists_lift (hT.1 ht).1
    rw [p19T_ne _ _ _ _ _ _ hne]
    exact ⟨_, (lift_mem_foldPre hT.1 subset_rfl ht hp hpt).1⟩

theorem P'₁_nonempty :
    (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1).Nonempty := by
  obtain ⟨t, ht⟩ := H.h.2.2.2.2.2.1
  obtain ⟨p, hp, hpt⟩ : t.1 ∈ Prod.fst '' F₂ := by rw [H.img₂]; exact ⟨t, ht, rfl⟩
  have : ((p, t.2) : (E × ℝ) × ℝ) ∈ foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ F₂ ×ˢ Icc (0 : ℝ) 1 :=
    lift_mem_foldPre H.P₂_straight.1 (subset_union_right.trans subset_union_left) ht hp hpt
  exact ⟨_, this.1, Or.inr this.2.1, this.2.2⟩

theorem P'₂_nonempty :
    (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1).Nonempty := by
  obtain ⟨t, ht⟩ := H.hγ
  obtain ⟨p, hp, hpt⟩ : t.1 ∈ Prod.fst '' F₂ := by rw [H.img₂]; exact ⟨t, H.γ_sub_P₂ ht, rfl⟩
  have : ((p, t.2) : (E × ℝ) × ℝ) ∈ foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ F₂ ×ˢ Icc (0 : ℝ) 1 :=
    lift_mem_foldPre H.Ti₀_straight.1 (subset_union_right.trans subset_union_left)
      (H.γ_sub_Ti₀ ht) hp hpt
  exact ⟨_, this.1, Or.inr this.2.1, this.2.2⟩

/-- (S2′) at the levels other than `i₀ + 1`. -/
theorem S2'T {i : ℕ} (hi : i ∈ Icc 1 k) (hne : i ≠ i₀ + 1) :
    endSet (F₁ ∪ F₂ ∪ F₃) (p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) =
        p19α F₁ F₂ F₃ α i₀ i ∪ p19α F₁ F₂ F₃ α i₀ (i + 1) ∧
      Disjoint (p19α F₁ F₂ F₃ α i₀ i) (p19α F₁ F₂ F₃ α i₀ (i + 1)) := by
  rcases eq_or_ne i i₀ with rfl | hne'
  · rw [p19α_ne _ _ _ _ hne, p19α_succ]
    exact ⟨H.endSet_T'₀, (disjoint_foldPre H.disj_αα).mono_right inter_subset_left⟩
  · rw [p19T_ne _ _ _ _ _ _ hne', p19α_ne _ _ _ _ hne, p19α_ne _ _ _ _ (by omega)]
    exact ⟨(H.straight_T hi hne').2, disjoint_foldPre (H.endSet_T hi hne').2⟩

theorem α'_finite' {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) : (p19α F₁ F₂ F₃ α i₀ i).Finite :=
  (foldPre_finite H.inj₁ H.inj₂ H.inj₃ (H.α_finite hi)).subset (p19α_sub _ _ _ _ _ _)

theorem α'_one : p19α F₁ F₂ F₃ α i₀ 1 = ∅ := by
  rw [p19α_ne _ _ _ _ (by have := H.i₀_pos; omega), H.α_one, foldPre_empty]

theorem α'_last : p19α F₁ F₂ F₃ α i₀ (k + 1) = ∅ := by
  unfold p19α
  split_ifs <;> simp [H.α_last, foldPre_empty]

/-- The sets of p. 203 lie in `φ⋆⁻¹(S)`. -/
theorem sub_foldPre_S :
    (⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ⊆
      foldPre (F₁ ∪ F₂ ∪ F₃) S := by
  have hT : ∀ i ∈ Icc 1 k, T i ⊆ S := fun i hi => by
    rw [H.S_eq]
    exact (subset_biUnion_of_mem (u := T) hi).trans (subset_union_left.trans subset_union_left)
  have hP₁ : P₁ ⊆ S := by rw [H.S_eq]; exact subset_union_right.trans subset_union_left
  have hP₂ : P₂ ⊆ S := by rw [H.S_eq]; exact subset_union_right
  have hi₀ : i₀ ∈ Icc 1 k := ⟨H.i₀_pos, H.i₀_le⟩
  rintro q ((hq | hq) | hq)
  · obtain ⟨i, hi, hq⟩ := mem_iUnion₂.1 hq
    rcases eq_or_ne i i₀ with rfl | hne
    · rw [p19T_self] at hq
      rcases hq with (h | h) | h
      · exact foldPre_mono subset_rfl hP₁ h.1
      · exact foldPre_mono subset_rfl hP₂ h.1
      · exact foldPre_mono subset_rfl (hT _ hi) h.1
    · rw [p19T_ne _ _ _ _ _ _ hne] at hq
      exact foldPre_mono subset_rfl (hT i hi) hq
  · exact foldPre_mono subset_rfl hP₂ hq.1
  · exact foldPre_mono subset_rfl (hT _ hi₀) hq.1

/-- **Proposition 19, `i₀ < k`**: a broken stairwell structure with a pit at level `i₀ + 1`. -/
theorem broken (hk : i₀ < k) : IsBrokenStairwellStr (F₁ ∪ F₂ ∪ F₃)
      ((⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      k (i₀ + 1) (p19T F₁ F₂ F₃ T P₁ P₂ i₀) (p19α F₁ F₂ F₃ α i₀)
      (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) := by
  have hi1 : i₀ + 1 ∈ Icc 1 k := ⟨by omega, hk⟩
  have hE1 := H.endSet_T hi1 (by omega)
  have hsplit := foldPre_split (F₁ ∪ F₂ ∪ F₃) F₃ (F₁ ∪ F₂) (α (i₀ + 1))
    (fun x hx => by rcases hx with h | h; exact Or.inr h; exact Or.inl h)
  refine ⟨by omega, hk, fun i hi => H.S1'T hi, H.P'₁_nonempty, H.straight_P'₁.1,
    H.P'₂_nonempty, H.straight_P'₂.1, rfl, fun i hi hne => H.S2'T hi hne, ?_, ?_, ?_, ?_,
    fun i hi => H.α'_finite' hi,
    (foldPre_finite H.inj₁ H.inj₂ H.inj₃ (H.α_finite H.i₀1_mem)).subset inter_subset_left,
    H.α'_one, H.α'_last, ?_, ?_, fun i hi => H.S3'T hi, H.S3'P, H.S3'γ hk,
    fun i hi => H.S4'T hi (fun _ => hk), H.S4'_i₀1_γ hk, H.S4'_P'₂_E, H.S4'_P'₂_γ,
    H.gen'_broken hk, H.S6'⟩
  · rw [p19T_ne _ _ _ _ _ _ (by omega), (H.straight_T hi1 (by omega)).2, p19α_succ,
      p19α_ne _ _ _ _ (by omega)]
    conv_lhs => rw [hsplit]
    ext q; simp only [mem_union]; tauto
  · rw [p19α_succ, p19α_ne _ _ _ _ (by omega)]
    exact (disjoint_foldPre hE1.2).mono_left inter_subset_left
  · rw [p19α_succ]
    exact Set.disjoint_left.2 fun q hq hq' => H.α₃_off ⟨hq.2.1, (fst_mem_of_mem_foldPre hq.1).2⟩
      hq'.2.1
  · rw [p19α_ne _ _ _ _ (by omega)]
    exact (disjoint_foldPre hE1.2.symm).mono_right inter_subset_left
  · rw [H.straight_P'₂.2, H.straight_P'₁.2]
  · rw [H.straight_P'₁.2]
    exact (disjoint_foldPre H.disj_α'γ.symm).mono_right inter_subset_left

/-- **Proposition 19, `i₀ = k`**: a stairwell structure of height `k`. -/
theorem stair (hk : i₀ = k) : IsStairwellStr (F₁ ∪ F₂ ∪ F₃)
    (⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) k (p19T F₁ F₂ F₃ T P₁ P₂ i₀)
    (p19α F₁ F₂ F₃ α i₀) := by
  have hne : ∀ i ∈ Icc 1 k, i ≠ i₀ + 1 := fun i hi => by have := hi.2; omega
  refine ⟨by have := H.i₀_pos; omega, fun i hi => H.S1'T hi, rfl, fun i hi => ?_, H.α'_one,
    H.α'_last, fun i hi => H.S3'T hi, fun i hi => H.S4'T hi (fun h => by have := hi.2; omega), H.gen'_stair⟩
  obtain ⟨h1, h2⟩ := H.S2'T hi (hne i hi)
  exact ⟨h1, h2, H.α'_finite' ⟨hi.1, by have := hi.2; omega⟩,
    H.α'_finite' ⟨by omega, by have := hi.2; omega⟩⟩

end P19

/-- **H–O Proposition 19 in the full fold** (pp. 202–208): for any simple fold with the
`Gᵢ` of p. 202 (`ho16_prop19_fold`), the sets of p. 203 form a broken stairwell structure of height
`k` with a pit at level `i₀ + 1` in `F⋆` if `i₀ < k`, and a stairwell structure of height `k` if
`i₀ = k`; all lie in `φ⋆⁻¹(S)`. `F` need not be connected. -/
theorem ho16_prop19_full {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
    {γ P₁ P₂ : Set (E × ℝ)} (hG : IsPLGraph G) (hconn : IsConnected G)
    (h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂) (hγ : γ.Nonempty)
    (hE : (endSet G P₁).Nonempty) {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G (Prod.fst '' P₁) (Prod.fst '' P₂)
      (sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀)) F₁ F₂ F₃) :
    (⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ⊆
      foldPre (F₁ ∪ F₂ ∪ F₃) S ∧
    (i₀ < k → IsBrokenStairwellStr (F₁ ∪ F₂ ∪ F₃)
      ((⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      k (i₀ + 1) (p19T F₁ F₂ F₃ T P₁ P₂ i₀) (p19α F₁ F₂ F₃ α i₀)
      (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)) ∧
    (i₀ = k → IsStairwellStr (F₁ ∪ F₂ ∪ F₃) (⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) k
      (p19T F₁ F₂ F₃ T P₁ P₂ i₀) (p19α F₁ F₂ F₃ α i₀)) := by
  have H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃ := ⟨hG, hconn, h, hγ, hE, hF⟩
  exact ⟨H.sub_foldPre_S, H.broken, H.stair⟩

end Prop19

end HPC.HO16
