import HPC.HO16.Prop19B

/-!
# Batch 196, §3: Proposition 19, images, (S3′), (S5′), (S6′) (pp. 207–208)

The images under `π` of the sets of p. 203, the neighbourhoods of (S3′) pulled back along `φ`
(away from `F₁ ∪ F₂` at levels `i₀`, `i₀ + 1`, away from `F₃` for `P′₂`/`S′_{i₀+1}`), genericity
(S5′) by `IsSimpleFoldOf.isOrdinaryPt_iff`, and (S6′).
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Prop19C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem p19α_sub (F₁ F₂ F₃ : Set (E × ℝ)) (α : ℕ → Set (E × ℝ)) (i₀ i : ℕ) :
    p19α F₁ F₂ F₃ α i₀ i ⊆ foldPre (F₁ ∪ F₂ ∪ F₃) (α i) := by
  unfold p19α; split_ifs
  · exact inter_subset_left
  · exact subset_rfl

omit [NormedSpace ℝ E] in
/-- Pulling a neighbourhood of a set back along `π`. -/
theorem preimage_fst_mem_nhdsSet {s : Set E} {t : Set (E × ℝ)} {V : Set E} (hV : V ∈ 𝓝ˢ s)
    (ht : ∀ x ∈ t, x.1 ∈ s) : Prod.fst ⁻¹' V ∈ 𝓝ˢ t :=
  mem_nhdsSet_iff_forall.2 fun x hx =>
    continuous_fst.continuousAt.preimage_mem_nhds (mem_nhdsSet_iff_forall.1 hV _ (ht x hx))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The algebra of the pulled back neighbourhoods of (S3′). -/
theorem inter_pullback_eq {A A' V₀ : Set E} {F' Y Y' U : Set (E × ℝ)}
    (h : A ∩ V₀ = A' ∩ V₀) (hY : Y ∩ U = F' ∩ Prod.fst ⁻¹' A ∩ U)
    (hY' : Y' ∩ U = F' ∩ Prod.fst ⁻¹' A' ∩ U) :
    Y ∩ (Prod.fst ⁻¹' V₀ ∩ U) = Y' ∩ (Prod.fst ⁻¹' V₀ ∩ U) := by
  ext x
  have h1 := Set.ext_iff.1 hY x
  have h2 := Set.ext_iff.1 hY' x
  have h3 := Set.ext_iff.1 h x.1
  simp only [mem_inter_iff, mem_preimage] at *
  tauto

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Disjointness transfers to sets lying over disjoint sets. -/
theorem disjoint_of_over {A B : Set E} {A' B' : Set (E × ℝ)} (h : Disjoint A B)
    (hA : ∀ x ∈ A', x.1 ∈ A) (hB : ∀ x ∈ B', x.1 ∈ B) : Disjoint A' B' :=
  Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 h (hA x hx) (hB x hx')

variable {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
  {γ P₁ P₂ F₁ F₂ F₃ : Set (E × ℝ)}

namespace P19

variable (H : P19 G S k i₀ T α γ P₁ P₂ F₁ F₂ F₃)
include H

/-! ### Images -/

theorem α_sub_T {i : ℕ} (hi : i ∈ Icc 1 k) : α i ⊆ T i := by
  rcases eq_or_ne i i₀ with rfl | hne
  · exact H.αi₀_sub_Ti₀
  · have := endSet_subset G (T i); rw [(H.endSet_T hi hne).1] at this
    exact subset_union_left.trans this

theorem α_subG {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) : α i ⊆ G ×ˢ Icc (0 : ℝ) 1 := by
  rcases eq_or_ne i (k + 1) with rfl | hne
  · rw [H.α_last]; exact empty_subset _
  · exact (H.α_sub_T ⟨hi.1, by have := hi.2; omega⟩).trans
      (H.T_straight ⟨hi.1, by have := hi.2; omega⟩).2.1

theorem γ_subG : γ ⊆ G ×ˢ Icc (0 : ℝ) 1 := H.γ_sub_Ti₀.trans H.Ti₀_straight.1

theorem i₀1_mem : i₀ + 1 ∈ Icc 1 (k + 1) := ⟨by omega, by have := H.i₀_le; omega⟩
theorem i₀_mem : i₀ ∈ Icc 1 (k + 1) := ⟨H.i₀_pos, by have := H.i₀_le; omega⟩

theorem img_T' {i : ℕ} (hi : i ∈ Icc 1 k) (hne : i ≠ i₀) :
    Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ i = (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' T i) := by
  rw [p19T_ne _ _ _ _ _ _ hne, image_foldPre (H.T_straight hi).2.1]

theorem img_α {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) :
    Prod.fst '' foldPre (F₁ ∪ F₂ ∪ F₃) (α i) =
      (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' α i) :=
  image_foldPre (H.α_subG hi)

theorem img_γ : Prod.fst '' foldPre (F₁ ∪ F₂ ∪ F₃) γ =
    (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' γ) :=
  image_foldPre H.γ_subG

theorem img_α₃ : Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ F₃ ×ˢ Icc (0 : ℝ) 1) =
    F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1)) := by
  rw [image_foldPre_inter (H.α_subG H.i₀1_mem), inter_eq_right.2 subset_union_right]

theorem img_α₁₂ :
    Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) =
      (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1)) := by
  rw [image_foldPre_inter (H.α_subG H.i₀1_mem), inter_eq_right.2 subset_union_left]

theorem img_P'₁ : Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) =
    (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' P₂) := by
  rw [image_foldPre_inter H.P₂_straight.1, inter_eq_right.2 subset_union_left]

theorem img_P'₂ : Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) =
    (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' T i₀) := by
  rw [image_foldPre_inter H.Ti₀_straight.1, inter_eq_right.2 subset_union_left]

/-- Points of `F₃` over `π(β_{i₀})` are not in `F₁ ∪ F₂`. -/
theorem α₃_off : F₃ ∩ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1)) ⊆ (F₁ ∪ F₂)ᶜ := by
  rintro x ⟨h3, hx⟩ (h | h)
  · exact Set.disjoint_left.1 H.disj₁₃ h h3
  · exact H.pre_α_disj₂₃ H.i₀1_mem hx ⟨h, h3⟩

/-- Points of `F₁ ∪ F₂` over `π(β_{i₀})` are not in `F₃`. -/
theorem α₁₂_off : (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1)) ⊆ F₃ᶜ :=
  fun x hx h3 => H.α₃_off ⟨h3, hx.2⟩ hx.1

theorem α₀_off : (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' α i₀) ⊆ (F₁ ∪ F₂)ᶜ :=
  fun x hx => (H.pre_αi₀ hx).2

theorem img_T'_off {i : ℕ} (hi : i ∈ Icc 1 k) :
    Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ i ∩ (F₁ ∪ F₂)ᶜ =
      (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' T i) ∩ (F₁ ∪ F₂)ᶜ := by
  rcases eq_or_ne i i₀ with rfl | hne
  · rw [H.image_T'₀]
    ext x; simp only [mem_inter_iff, mem_union, mem_compl_iff, mem_preimage]; tauto
  · rw [H.img_T' hi hne]

theorem α'_over (i : ℕ) : ∀ x ∈ Prod.fst '' p19α F₁ F₂ F₃ α i₀ i,
    x ∈ F₁ ∪ F₂ ∪ F₃ ∧ x.1 ∈ Prod.fst '' α i := by
  rintro _ ⟨q, hq, rfl⟩
  exact fst_mem_of_mem_foldPre (p19α_sub F₁ F₂ F₃ α i₀ i hq)

/-! ### (S3′) -/

/-- **(S3′) for the levels** (p. 207). -/
theorem S3'T {i : ℕ} (hi : i ∈ Ico 1 k) : ∃ V ∈ 𝓝ˢ (Prod.fst '' p19α F₁ F₂ F₃ α i₀ (i + 1)),
    Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ i ∩ V =
      Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ (i + 1) ∩ V := by
  obtain ⟨V₀, hV₀, hV₀eq⟩ := H.S3 i hi
  have hi' : i ∈ Icc 1 k := ⟨hi.1, hi.2.le⟩
  have hi1 : i + 1 ∈ Icc 1 k := ⟨by omega, hi.2⟩
  have hpre : Prod.fst ⁻¹' V₀ ∈ 𝓝ˢ (Prod.fst '' p19α F₁ F₂ F₃ α i₀ (i + 1)) :=
    preimage_fst_mem_nhdsSet hV₀ fun x hx => (H.α'_over (i + 1) x hx).2
  by_cases hc : i = i₀ ∨ i + 1 = i₀
  · have hU : IsOpen (F₁ ∪ F₂)ᶜ :=
      (H.F₁PL.isCompact.isClosed.union H.F₂PL.isCompact.isClosed).isOpen_compl
    have hoff : Prod.fst '' p19α F₁ F₂ F₃ α i₀ (i + 1) ⊆ (F₁ ∪ F₂)ᶜ := by
      rcases hc with rfl | h
      · rw [p19α_succ, H.img_α₃]; exact H.α₃_off
      · rw [p19α_ne _ _ _ _ (by omega), H.img_α ⟨by omega, by have := hi.2; omega⟩, h]
        exact H.α₀_off
    exact ⟨_, Filter.inter_mem hpre (hU.mem_nhdsSet.2 hoff),
      inter_pullback_eq hV₀eq (H.img_T'_off hi') (H.img_T'_off hi1)⟩
  · push_neg at hc
    refine ⟨Prod.fst ⁻¹' V₀ ∩ univ, Filter.inter_mem hpre univ_mem,
      inter_pullback_eq (F' := F₁ ∪ F₂ ∪ F₃) hV₀eq ?_ ?_⟩
    · rw [H.img_T' hi' hc.1]
    · rw [H.img_T' hi1 hc.2]

/-- **(S3′) for `P′₁`, `P′₂`** (p. 207). -/
theorem S3'P : ∃ V ∈ 𝓝ˢ (Prod.fst '' endSet (F₁ ∪ F₂ ∪ F₃)
      (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)),
    Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∩ V =
      Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∩ V := by
  obtain ⟨W, hW, hWeq⟩ := H.S3W
  rw [H.straight_P'₁.2, H.img_γ]
  refine ⟨Prod.fst ⁻¹' W ∩ univ,
    Filter.inter_mem (preimage_fst_mem_nhdsSet hW fun x hx => hx.2) univ_mem,
    inter_pullback_eq (F' := F₁ ∪ F₂) hWeq ?_ ?_⟩
  · rw [H.img_P'₁]
  · rw [H.img_P'₂]

/-- **(S3′) for `P′₂` and `S′_{i₀+1}` near `γ′_{i₀+1}`** (p. 207). -/
theorem S3'γ (hk : i₀ < k) : ∃ W ∈ 𝓝ˢ (Prod.fst ''
      (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)),
    Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∩ W =
      Prod.fst '' p19T F₁ F₂ F₃ T P₁ P₂ i₀ (i₀ + 1) ∩ W := by
  obtain ⟨V₀, hV₀, hV₀eq⟩ := H.S3 i₀ ⟨H.i₀_pos, hk⟩
  rw [H.img_α₁₂]
  have hU : IsOpen F₃ᶜ := H.F₃PL.isCompact.isClosed.isOpen_compl
  refine ⟨Prod.fst ⁻¹' V₀ ∩ F₃ᶜ,
    Filter.inter_mem (preimage_fst_mem_nhdsSet hV₀ fun x hx => hx.2)
      (hU.mem_nhdsSet.2 H.α₁₂_off),
    inter_pullback_eq (F' := F₁ ∪ F₂ ∪ F₃) hV₀eq ?_ ?_⟩
  · rw [H.img_P'₂]
    ext x; simp only [mem_inter_iff, mem_union, mem_compl_iff, mem_preimage]; tauto
  · rw [H.img_T' ⟨by omega, hk⟩ (by omega)]

/-! ### (S6′) -/

/-- **(S6′)** (p. 208): `π(α′_{i₀+1}) ∩ π(P′₁ ∪ P′₂) = ∅`. -/
theorem S6' : Disjoint (Prod.fst '' p19α F₁ F₂ F₃ α i₀ (i₀ + 1))
    (Prod.fst '' ((foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∪
      (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1))) := by
  rw [p19α_succ, H.img_α₃]
  refine Set.disjoint_left.2 fun x hx hx' => H.α₃_off hx ?_
  obtain ⟨q, hq | hq, rfl⟩ := hx'
  · exact hq.2.1
  · exact hq.2.1

/-! ### (S5′) -/

theorem ordinary_lift {x : E × ℝ} (hx : x ∈ F₁ ∪ F₂ ∪ F₃) (h : IsOrdinaryPt G x.1) :
    IsOrdinaryPt (F₁ ∪ F₂ ∪ F₃) x :=
  (H.hF.isOrdinaryPt_iff H.ordinary_frontier hx).2 h

theorem ordinary_α {i : ℕ} (hi : i ∈ Icc 2 k) {y : E} (hy : y ∈ Prod.fst '' α i) :
    IsOrdinaryPt G y :=
  (H.gen.1 _ (List.mem_append_left _ (mem_gen_list hi))).2.2 y hy

/-- A set of points of `F` over a generic set of `G`, finite, consists of ordinary points. -/
theorem generic_member {B : Set (E × ℝ)} {A : Set E} (hfin : B.Finite)
    (hover : ∀ x ∈ B, x ∈ F₁ ∪ F₂ ∪ F₃ ∧ x.1 ∈ A) (hA : ∀ y ∈ A, IsOrdinaryPt G y) :
    B.Finite ∧ B ⊆ F₁ ∪ F₂ ∪ F₃ ∧ ∀ x ∈ B, IsOrdinaryPt (F₁ ∪ F₂ ∪ F₃) x :=
  ⟨hfin, fun x hx => (hover x hx).1, fun x hx =>
    H.ordinary_lift (hover x hx).1 (hA _ (hover x hx).2)⟩

theorem α'_finite {i : ℕ} (hi : i ∈ Icc 1 (k + 1)) :
    (Prod.fst '' p19α F₁ F₂ F₃ α i₀ i).Finite :=
  ((foldPre_finite H.inj₁ H.inj₂ H.inj₃ (H.α_finite hi)).subset (p19α_sub _ _ _ _ _ _)).image _

/-- The pairwise disjointness of `⟨π(α′₂), …, π(α′_k)⟩`. -/
theorem gen'_pairwise :
    ((List.range' 2 (k - 1)).map fun i => Prod.fst '' p19α F₁ F₂ F₃ α i₀ i).Pairwise Disjoint := by
  have hP := (List.pairwise_append.1 H.gen.2).1
  rw [List.pairwise_map] at hP ⊢
  exact hP.imp fun h => disjoint_of_over h (fun x hx => (H.α'_over _ x hx).2)
    (fun x hx => (H.α'_over _ x hx).2)

theorem gen'_members {i : ℕ} (hi : i ∈ Icc 2 k) :
    (Prod.fst '' p19α F₁ F₂ F₃ α i₀ i).Finite ∧
      Prod.fst '' p19α F₁ F₂ F₃ α i₀ i ⊆ F₁ ∪ F₂ ∪ F₃ ∧
      ∀ x ∈ Prod.fst '' p19α F₁ F₂ F₃ α i₀ i, IsOrdinaryPt (F₁ ∪ F₂ ∪ F₃) x :=
  H.generic_member (H.α'_finite ⟨by have := hi.1; omega, by have := hi.2; omega⟩)
    (H.α'_over i) fun _ hy => H.ordinary_α hi hy

/-- **(S5)** for the stairwell of height `k` (`i₀ = k`). -/
theorem gen'_stair : IsGeneric (F₁ ∪ F₂ ∪ F₃)
    ((List.range' 2 (k - 1)).map fun i => Prod.fst '' p19α F₁ F₂ F₃ α i₀ i) := by
  refine ⟨fun B hB => ?_, H.gen'_pairwise⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hB
  rw [List.mem_range'_1] at hi
  exact H.gen'_members ⟨hi.1, by omega⟩

/-- **(S5′)** (p. 208) for the broken stairwell with a pit at level `i₀ + 1`. -/
theorem gen'_broken (hk : i₀ < k) : IsGeneric (F₁ ∪ F₂ ∪ F₃)
    (((List.range' 2 (k - 1)).map fun i => Prod.fst '' p19α F₁ F₂ F₃ α i₀ i) ++
      [Prod.fst '' endSet (F₁ ∪ F₂ ∪ F₃)
          (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1),
        Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)]) := by
  rw [H.straight_P'₁.2, H.img_γ, H.img_α₁₂]
  have hγo : ∀ x ∈ (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' γ),
      x ∈ F₁ ∪ F₂ ∪ F₃ ∧ x.1 ∈ Prod.fst '' γ := fun x hx => hx
  have hαo : ∀ x ∈ (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1)),
      x ∈ F₁ ∪ F₂ ∪ F₃ ∧ x.1 ∈ Prod.fst '' α (i₀ + 1) :=
    fun x hx => ⟨subset_union_left hx.1, hx.2⟩
  have hi₀1 : i₀ + 1 ∈ Icc 2 k := ⟨by have := H.i₀_pos; omega, hk⟩
  have hfinγ : ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' γ)).Finite := by
    rw [← H.img_γ]; exact (foldPre_finite H.inj₁ H.inj₂ H.inj₃ H.γ_finite).image _
  have hfinα : ((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' α (i₀ + 1))).Finite := by
    refine ((H.img_α H.i₀1_mem) ▸ ((foldPre_finite H.inj₁ H.inj₂ H.inj₃
      (H.α_finite H.i₀1_mem)).image Prod.fst)).subset ?_
    exact fun x hx => ⟨subset_union_left hx.1, hx.2⟩
  refine ⟨fun B hB => ?_, ?_⟩
  · rcases List.mem_append.1 hB with hB | hB
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hB
      rw [List.mem_range'_1] at hi
      exact H.gen'_members ⟨hi.1, by omega⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl
      · exact H.generic_member hfinγ hγo fun _ hy => H.ordinary_γ hy
      · exact H.generic_member hfinα hαo fun _ hy => H.ordinary_α hi₀1 hy
  · refine List.pairwise_append.2 ⟨H.gen'_pairwise, ?_, ?_⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
      exact disjoint_of_over (H.disj_α_γ H.i₀1_mem).symm (fun x hx => hx.2)
        (fun x hx => (hαo x hx).2)
    · intro a ha b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      have hi' := List.mem_range'_1.1 hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact disjoint_of_over (H.gen_cross _ (mem_gen_list ⟨hi'.1, by omega⟩)).2
          (fun x hx => (H.α'_over i x hx).2) (fun x hx => hx.2)
      · rcases eq_or_ne i (i₀ + 1) with rfl | hne
        · rw [p19α_succ, H.img_α₃]
          exact Set.disjoint_left.2 fun x hx hx' => H.α₃_off hx hx'.1
        · have hP := (List.pairwise_append.1 H.gen.2).1
          rw [List.pairwise_map] at hP
          have hd := hP.forall (fun a b h => h.symm) hi
            (List.mem_range'_1.2 ⟨by have := H.i₀_pos; omega, by omega⟩) hne
          exact disjoint_of_over hd (fun x hx => (H.α'_over i x hx).2) (fun x hx => (hαo x hx).2)

end P19

end Prop19C

end HPC.HO16
