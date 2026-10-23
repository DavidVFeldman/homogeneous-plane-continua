import HPC.HO16.StairLib

/-!
# Batch 195, §§4–8: straight sets, stairwells, Proposition 17, Lemma 18, the fold of Proposition 19

Part of the batch-195 skeleton `HO16C.lean` (commission 195), split under `HPC/HO16/`.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ## §4–§7. Straight sets, stairwells, Proposition 17, Lemma 18 -/

section Stairwells

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **p. 192, observation after Definition 12**: `π` restricted to `S \ 𝓔(S)` is an open map
into `G`. -/
theorem ho16_obs12 {G : Set E} {S : Set (E × ℝ)} (hG : IsPLGraph G) (hS : IsStraight G S)
    {U : Set (E × ℝ)} (hU : IsOpen U) :
    ∃ W : Set E, IsOpen W ∧ Prod.fst '' (U ∩ (S \ endSet G S)) = W ∩ G := by
  obtain ⟨hSG, hSc, hinj, -⟩ := hS
  have hScpt : IsCompact S := (hG.isCompact.prod isCompact_Icc).of_isClosed_subset hSc hSG
  have hcl : IsClosed (Prod.fst '' (S \ U)) :=
    ((hScpt.diff hU).image continuous_fst).isClosed
  refine ⟨(Prod.fst '' (S \ U))ᶜ ∩ (closure (G \ Prod.fst '' S))ᶜ,
    hcl.isOpen_compl.inter isClosed_closure.isOpen_compl, ?_⟩
  ext y
  constructor
  · rintro ⟨p, ⟨hpU, hpS, hpE⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, (hSG hpS).1⟩
    · rintro ⟨q, ⟨hqS, hqU⟩, hq⟩
      have := hinj hqS hpS hq
      subst this
      exact hqU hpU
    · intro h
      exact hpE ⟨hpS, subset_closure ⟨p, hpS, rfl⟩, h⟩
  · rintro ⟨⟨h1, h2⟩, hyG⟩
    have hyS : y ∈ Prod.fst '' S := by
      by_contra h
      exact h2 (subset_closure ⟨hyG, h⟩)
    obtain ⟨p, hpS, rfl⟩ := hyS
    refine ⟨p, ⟨?_, hpS, ?_⟩, rfl⟩
    · by_contra hpU
      exact h1 ⟨p, ⟨hpS, hpU⟩, rfl⟩
    · rintro ⟨-, -, h⟩
      exact h2 h

/-- **p. 193, observation after Definition 13**, relative to the component `C` (the form used in
Proposition 19 and Theorem 20). -/
theorem ho16_obs13_comp {G : Set E} {S : Set (E × ℝ)} {k : ℕ} {T α : ℕ → Set (E × ℝ)}
    (hG : IsPLGraph G) (h : IsStairwellStr G S k T α) {C : Set E} {p : E}
    (hC : C = connectedComponentIn G p)
    (hne : ∀ i ∈ Icc 1 k, (T i ∩ C ×ˢ Icc (0 : ℝ) 1).Nonempty) :
    IsStairwellStr C (S ∩ C ×ˢ Icc (0 : ℝ) 1) k (fun i => T i ∩ C ×ˢ Icc (0 : ℝ) 1)
      (fun i => α i ∩ C ×ˢ Icc (0 : ℝ) 1) := by
  subst hC
  obtain ⟨hk1, hS1, hSU, hS2, hα1, hαk, hS3, hS4, hS5⟩ := h
  have hTG : ∀ i ∈ Icc 1 k, T i ⊆ G ×ˢ Icc (0 : ℝ) 1 := fun i hi => (hS1 i hi).2.1
  have hαG : ∀ i ∈ Icc 1 k, α i ⊆ G ×ˢ Icc (0 : ℝ) 1 := fun i hi q hq =>
    hTG i hi (endSet_subset G (T i) (by rw [(hS2 i hi).1]; exact Or.inl hq))
  have hαG' : ∀ i ∈ Icc 1 k, α (i + 1) ⊆ G ×ˢ Icc (0 : ℝ) 1 := fun i hi q hq =>
    hTG i hi (endSet_subset G (T i) (by rw [(hS2 i hi).1]; exact Or.inr hq))
  refine ⟨hk1, fun i hi => ⟨hne i hi, (hS1 i hi).2.inter_comp hG p⟩, ?_, fun i hi => ?_, ?_, ?_,
    fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [hSU, iUnion₂_inter]
  · rw [hG.endSet_inter_comp p (hTG i hi), (hS2 i hi).1, union_inter_distrib_right]
    exact ⟨rfl, (hS2 i hi).2.1.mono inter_subset_left inter_subset_left,
      (hS2 i hi).2.2.1.subset inter_subset_left, (hS2 i hi).2.2.2.subset inter_subset_left⟩
  · simp [hα1]
  · simp [hαk]
  · obtain ⟨V, hV, hVeq⟩ := hS3 i hi
    have hi' : i ∈ Icc 1 k := ⟨hi.1, hi.2.le⟩
    have hi'' : i + 1 ∈ Icc 1 k := ⟨by icc_omega, hi.2⟩
    refine ⟨V, nhdsSet_mono (image_mono inter_subset_left) hV, ?_⟩
    rw [image_fst_inter_star (hTG i hi'), image_fst_inter_star (hTG (i + 1) hi''),
      inter_right_comm, hVeq, inter_right_comm]
  · rw [image_fst_inter_star (hTG i hi), image_fst_inter_star (hαG i hi),
      image_fst_inter_star (hαG' i hi)]
    exact ⟨(hS4 i hi).1.inter_comp hG p, (hS4 i hi).2.inter_comp hG p⟩
  · refine IsGeneric.of_forall₂ (fun x hx ho => ho.comp p hx) ?_ hS5
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    exact image_fst_inter_star_subset _ _

/-- **Claim 14.1** (p. 193): for connected `G` and odd `k`, every `x ∈ G` lies in `π(T i)` for
an odd number of `i ∈ {1, …, k}`. -/
theorem ho16_claim14_1 {G : Set E} {S : Set (E × ℝ)} {k : ℕ} {T α : ℕ → Set (E × ℝ)}
    (hG : IsPLGraph G) (hconn : IsConnected G) (h : IsStairwellStr G S k T α) (hk : Odd k)
    {x : E} (hx : x ∈ G) : Odd {i : ℕ | i ∈ Icc 1 k ∧ x ∈ Prod.fst '' T i}.ncard := by
  classical
  obtain ⟨hk1, hS1, -, hS2, hα1, hαk, hS3, hS4, -⟩ := h
  have hPL : ∀ i ∈ Icc 1 k, IsPLGraph (Prod.fst '' T i) := fun i hi => (hS1 i hi).2.2.2.2
  have hAG : ∀ i ∈ Icc 1 k, Prod.fst '' T i ⊆ G := fun i hi => (hS1 i hi).2.image_subset
  have hAne : ∀ i ∈ Icc 1 k, (Prod.fst '' T i).Nonempty := fun i hi => (hS1 i hi).1.image _
  have hfr : ∀ i ∈ Icc 1 k, Prod.fst '' α i ∪ Prod.fst '' α (i + 1) =
      relFrontier G (Prod.fst '' T i) := by
    intro i hi
    rw [← image_union, ← (hS2 i hi).1, (hS1 i hi).2.image_endSet]
  have hdj : ∀ i ∈ Icc 1 k, Disjoint (Prod.fst '' α i) (Prod.fst '' α (i + 1)) := by
    intro i hi
    have hsub : endSet G (T i) ⊆ T i := endSet_subset _ _
    rw [(hS2 i hi).1] at hsub
    exact disjoint_image_fst_of_injOn (hS1 i hi).2.2.2.1 (subset_union_left.trans hsub)
      (subset_union_right.trans hsub) (hS2 i hi).2.1
  have h11 : ∀ i ∈ Icc 1 k, IsFoldTriple G (sideOf G (Prod.fst '' α i) (Prod.fst '' T i))
      (Prod.fst '' T i) (sideOf G (Prod.fst '' α (i + 1)) (Prod.fst '' T i)) := fun i hi =>
    ho16_prop11 hG hconn (hPL i hi) (hAG i hi) (hAne i hi) (hfr i hi) (hdj i hi) (hS4 i hi).1
      (hS4 i hi).2
  have h10 : ∀ i ∈ Ico 1 k, sideOf G (Prod.fst '' α (i + 1)) (Prod.fst '' T i) =
      sideOf G (Prod.fst '' α (i + 1)) (Prod.fst '' T (i + 1)) := by
    intro i hi
    have hi' : i ∈ Icc 1 k := ⟨hi.1, hi.2.le⟩
    have hi'' : i + 1 ∈ Icc 1 k := ⟨by icc_omega, hi.2⟩
    obtain ⟨V, hV, hVeq⟩ := hS3 i hi
    have hB : Prod.fst '' α (i + 1) ⊆
        relFrontier G (Prod.fst '' T i) ∩ relFrontier G (Prod.fst '' T (i + 1)) := by
      intro y hy
      refine ⟨?_, ?_⟩
      · rw [← hfr i hi']; exact Or.inr hy
      · rw [← hfr (i + 1) hi'']; exact Or.inl hy
    exact (ho16_prop10 hG hconn (hPL i hi') (hPL (i + 1) hi'') (hAG i hi') (hAG (i + 1) hi'')
      (hAne i hi') (hAne (i + 1) hi'') hB (hS4 i hi').2 (hS4 (i + 1) hi'').1 hV hVeq).1
  set M : ℕ → Set E := fun i =>
    if i = 0 then G else sideOf G (Prod.fst '' α (i + 1)) (Prod.fst '' T i) with hMdef
  have hR : ∀ i ∈ Icc 1 k, sideOf G (Prod.fst '' α (i + 1)) (Prod.fst '' T i) = M i :=
    fun i hi => by rw [hMdef]; exact (if_neg (by icc_omega)).symm
  have hL : ∀ i ∈ Icc 1 k, sideOf G (Prod.fst '' α i) (Prod.fst '' T i) = M (i - 1) := by
    intro i hi
    rcases Nat.lt_or_ge 1 i with h1 | h1
    · have hM : M (i - 1) = sideOf G (Prod.fst '' α (i - 1 + 1)) (Prod.fst '' T (i - 1)) := by
        rw [hMdef]; exact if_neg (by icc_omega)
      have h10' := h10 (i - 1) ⟨by icc_omega, by icc_omega⟩
      rw [show i - 1 + 1 = i by icc_omega] at h10' hM
      rw [hM, h10']
    · have hi1 : i = 1 := by icc_omega
      subst hi1
      rw [hα1, image_empty, sideOf_empty_of_connected hG hconn (hAG 1 hi) (hAne 1 hi), hMdef]
      exact (if_pos rfl).symm
  have hMk : M k = G := by
    rw [← hR k ⟨hk1, le_rfl⟩, hαk, image_empty,
      sideOf_empty_of_connected hG hconn (hAG k ⟨hk1, le_rfl⟩) (hAne k ⟨hk1, le_rfl⟩)]
  have hmem : ∀ i ∈ Icc 1 k, (x ∈ Prod.fst '' T i ↔ x ∈ M (i - 1) ∧ x ∈ M i) := by
    intro i hi
    obtain ⟨-, -, -, -, -, -, -, h2, -⟩ := h11 i hi
    rw [← hL i hi, ← hR i hi]
    constructor
    · intro h
      rw [h2] at h
      exact h
    · intro h
      rw [h2]
      exact h
  have hor : ∀ i < k, x ∈ M i ∨ x ∈ M (i + 1) := by
    intro i hi
    obtain ⟨-, -, -, -, -, -, h1, -, -⟩ := h11 (i + 1) ⟨by icc_omega, by icc_omega⟩
    have : x ∈ sideOf G (Prod.fst '' α (i + 1)) (Prod.fst '' T (i + 1)) ∪
        sideOf G (Prod.fst '' α (i + 1 + 1)) (Prod.fst '' T (i + 1)) := by
      rw [h1]; exact hx
    rw [hL (i + 1) ⟨by icc_omega, by icc_omega⟩, hR (i + 1) ⟨by icc_omega, by icc_omega⟩, Nat.add_sub_cancel]
      at this
    exact this
  have hM0 : x ∈ M 0 := by rw [hMdef]; simp only [if_pos]; exact hx
  have hpar := parity_count (fun i => x ∈ M i) hM0 k hor
  have hxMk : x ∈ M k := by rw [hMk]; exact hx
  simp only [if_pos hxMk] at hpar
  have hcount : {i : ℕ | i ∈ Icc 1 k ∧ x ∈ Prod.fst '' T i}.ncard =
      ∑ i ∈ Finset.Icc 1 k, if x ∈ M (i - 1) ∧ x ∈ M i then 1 else 0 := by
    rw [← Finset.card_filter, ← Set.ncard_coe_finset]
    congr 1
    ext i
    simp only [mem_setOf_eq, Finset.coe_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hi, hxi⟩
      exact ⟨hi, (hmem i hi).1 hxi⟩
    · rintro ⟨hi, hxi⟩
      exact ⟨hi, (hmem i hi).2 hxi⟩
  rw [hcount, Nat.odd_iff]
  obtain ⟨j, rfl⟩ := hk
  omega

/-- **p. 193**: "if k is odd then π(S) = G", for connected `G`. -/
theorem ho16_odd_image {G : Set E} {S : Set (E × ℝ)} {k : ℕ} (hG : IsPLGraph G)
    (hconn : IsConnected G) (h : HasStairwell G S k) (hk : Odd k) : Prod.fst '' S = G := by
  obtain ⟨T, α, h⟩ := h
  have hTG : ∀ i ∈ Icc 1 k, Prod.fst '' T i ⊆ G := fun i hi => (h.2.1 i hi).2.image_subset
  apply Subset.antisymm
  · rw [h.2.2.1, image_iUnion₂]
    exact iUnion₂_subset hTG
  · intro x hx
    have hodd := ho16_claim14_1 hG hconn h hk hx
    obtain ⟨i, hi, hxi⟩ := Set.nonempty_of_ncard_ne_zero hodd.pos.ne'
    rw [h.2.2.1, image_iUnion₂]
    exact mem_iUnion₂.2 ⟨i, hi, hxi⟩

/-- **p. 194, height 1**: for connected `G`, `π` maps `S` homeomorphically onto `G`. -/
theorem ho16_height_one {G : Set E} {S : Set (E × ℝ)} {T α : ℕ → Set (E × ℝ)}
    (hG : IsPLGraph G) (hconn : IsConnected G) (h : IsStairwellStr G S 1 T α) :
    Prod.fst '' S = G ∧ InjOn Prod.fst S ∧ ContinuousOn (Function.invFunOn Prod.fst S) G ∧
      ∀ y ∈ G, Function.invFunOn Prod.fst S y ∈ S ∧ (Function.invFunOn Prod.fst S y).1 = y := by
  have hS : S = T 1 := by rw [h.2.2.1]; simp
  have hT := (h.2.1 1 ⟨le_rfl, le_rfl⟩).2
  have himg := ho16_odd_image hG hconn ⟨T, α, h⟩ odd_one
  rw [hS] at himg ⊢
  refine ⟨himg, hT.2.2.1, ?_, fun y hy => ?_⟩
  · rw [← himg]
    exact continuousOn_invFunOn_fst (hT.isCompact hG) hT.2.2.1
  · have hex : ∃ a ∈ T 1, a.1 = y := by rw [← himg] at hy; exact hy
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

/-- **p. 200, observation after Definition 16**, relative to the component `C`. -/
theorem ho16_obs16_comp {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
    {γ P₁ P₂ : Set (E × ℝ)} (hG : IsPLGraph G) (h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂)
    {C : Set E} {p : E} (hC : C = connectedComponentIn G p)
    (hne : ∀ i ∈ Icc 1 k, (T i ∩ C ×ˢ Icc (0 : ℝ) 1).Nonempty)
    (hne₁ : (P₁ ∩ C ×ˢ Icc (0 : ℝ) 1).Nonempty) (hne₂ : (P₂ ∩ C ×ˢ Icc (0 : ℝ) 1).Nonempty) :
    IsBrokenStairwellStr C (S ∩ C ×ˢ Icc (0 : ℝ) 1) k i₀ (fun i => T i ∩ C ×ˢ Icc (0 : ℝ) 1)
      (fun i => α i ∩ C ×ˢ Icc (0 : ℝ) 1) (γ ∩ C ×ˢ Icc (0 : ℝ) 1)
      (P₁ ∩ C ×ˢ Icc (0 : ℝ) 1) (P₂ ∩ C ×ˢ Icc (0 : ℝ) 1) := by
  subst hC
  obtain ⟨hi1, hik, hS1, hP₁ne, hP₁, hP₂ne, hP₂, hSU, hS2, hE, hD1, hD2, hD3, hfin, hγfin, hα1,
    hαk, hP₂E, hP₁γ, hS3, hV, hW, hS4, hc1, hc2, hc3, hgen, hS6⟩ := h
  have hTG : ∀ i ∈ Icc 1 k, T i ⊆ G ×ˢ Icc (0 : ℝ) 1 := fun i hi => (hS1 i hi).2.1
  have hαG : ∀ i ∈ Icc 1 k, α i ⊆ G ×ˢ Icc (0 : ℝ) 1 ∧ α (i + 1) ⊆ G ×ˢ Icc (0 : ℝ) 1 := by
    intro i hi
    by_cases h : i = i₀
    · subst h
      exact ⟨fun q hq => hTG i hi (endSet_subset G (T i) (by rw [hE]; exact Or.inl (Or.inl hq))),
        fun q hq => hTG i hi (endSet_subset G (T i) (by rw [hE]; exact Or.inl (Or.inr hq)))⟩
    · exact ⟨fun q hq => hTG i hi (endSet_subset G (T i) (by rw [(hS2 i hi h).1]; exact Or.inl hq)),
        fun q hq => hTG i hi (endSet_subset G (T i) (by rw [(hS2 i hi h).1]; exact Or.inr hq))⟩
  have hi₀ : i₀ ∈ Icc 1 k := ⟨hi1, hik⟩
  have hγG : γ ⊆ G ×ˢ Icc (0 : ℝ) 1 := fun q hq =>
    hTG i₀ hi₀ (endSet_subset G (T i₀) (by rw [hE]; exact Or.inr hq))
  have hE₁G : endSet G P₁ ⊆ G ×ˢ Icc (0 : ℝ) 1 := (endSet_subset G P₁).trans hP₁.1
  have hP₁E := hG.endSet_inter_comp p hP₁.1
  have hP₂E' := hG.endSet_inter_comp p hP₂.1
  refine ⟨hi1, hik, fun i hi => ⟨hne i hi, (hS1 i hi).2.inter_comp hG p⟩, hne₁,
    hP₁.inter_comp hG p, hne₂, hP₂.inter_comp hG p, ?_, fun i hi hii => ?_, ?_,
    hD1.mono inter_subset_left inter_subset_left, hD2.mono inter_subset_left inter_subset_left,
    hD3.mono inter_subset_left inter_subset_left,
    fun i hi => (hfin i hi).subset inter_subset_left, hγfin.subset inter_subset_left, ?_, ?_, ?_,
    ?_, fun i hi => ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSU, union_inter_distrib_right, union_inter_distrib_right, iUnion₂_inter]
  · rw [hG.endSet_inter_comp p (hTG i hi), (hS2 i hi hii).1, union_inter_distrib_right]
    exact ⟨rfl, (hS2 i hi hii).2.mono inter_subset_left inter_subset_left⟩
  · rw [hG.endSet_inter_comp p (hTG i₀ hi₀), hE, union_inter_distrib_right,
      union_inter_distrib_right]
  · simp [hα1]
  · simp [hαk]
  · rw [hP₂E', hP₁E, hP₂E, union_inter_distrib_right]
  · rw [hP₁E]
    exact hP₁γ.mono inter_subset_left inter_subset_left
  · obtain ⟨V, hV, hVeq⟩ := hS3 i hi
    have hi' : i ∈ Icc 1 k := ⟨hi.1, hi.2.le⟩
    have hi'' : i + 1 ∈ Icc 1 k := ⟨by icc_omega, hi.2⟩
    refine ⟨V, nhdsSet_mono (image_mono inter_subset_left) hV, ?_⟩
    rw [image_fst_inter_star (hTG i hi'), image_fst_inter_star (hTG (i + 1) hi''),
      inter_right_comm, hVeq, inter_right_comm]
  · obtain ⟨V, hV, hVeq⟩ := hV
    refine ⟨V, ?_, ?_⟩
    · rw [hP₁E]
      exact nhdsSet_mono (image_mono inter_subset_left) hV
    · rw [image_fst_inter_star hP₁.1, image_fst_inter_star hP₂.1, inter_right_comm, hVeq,
        inter_right_comm]
  · obtain ⟨W, hW, hWeq⟩ := hW
    refine ⟨W, nhdsSet_mono (image_mono inter_subset_left) hW, ?_⟩
    rw [image_fst_inter_star hP₂.1, image_fst_inter_star (hTG i₀ hi₀), inter_right_comm, hWeq,
      inter_right_comm]
  · rw [image_fst_inter_star (hTG i hi), image_fst_inter_star (hαG i hi).1,
      image_fst_inter_star (hαG i hi).2]
    exact ⟨(hS4 i hi).1.inter_comp hG p, (hS4 i hi).2.inter_comp hG p⟩
  · rw [image_fst_inter_star (hTG i₀ hi₀), image_fst_inter_star hγG]
    exact hc1.inter_comp hG p
  · rw [hP₁E, image_fst_inter_star hP₂.1, image_fst_inter_star hE₁G]
    exact hc2.inter_comp hG p
  · rw [image_fst_inter_star hP₂.1, image_fst_inter_star hγG]
    exact hc3.inter_comp hG p
  · refine IsGeneric.of_forall₂ (fun x hx ho => ho.comp p hx) ?_ hgen
    refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro i _
      exact image_fst_inter_star_subset _ _
    · refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
      · rw [hP₁E]
        exact image_fst_inter_star_subset _ _
      · exact image_fst_inter_star_subset _ _
  · refine hS6.mono (image_mono inter_subset_left) (image_mono ?_)
    exact union_subset_union inter_subset_left inter_subset_left

/-- **H–O Proposition 17** (p. 200), with H–O's relabelling: `P₁ = S₁`, `P₂ = S₂`,
`S'ᵢ = Sᵢ₊₂`, `α'₁ = ∅`, `α'ᵢ = αᵢ₊₂` (`i ≥ 2`), `γ'₁ = α₃`. The hypothesis `3 ≤ k` is not in
the printed statement (§6). -/
theorem ho16_prop17 {G : Set E} {S : Set (E × ℝ)} {k : ℕ} {T α : ℕ → Set (E × ℝ)}
    (h : IsStairwellStr G S k T α) (hk : 3 ≤ k) :
    IsBrokenStairwellStr G S (k - 2) 1 (fun i => T (i + 2))
      (fun i => if i = 1 then ∅ else α (i + 2)) (α 3) (T 1) (T 2) := by
  obtain ⟨hk1, hS1, hSU, hS2, hα1, hαk, hS3, hS4, hS5⟩ := h
  have hfin : ∀ j ∈ Icc 1 (k + 1), (α j).Finite := by
    intro j hj
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact (hS2 j ⟨hj.1, by icc_omega⟩).2.2.1
    · have : j = k + 1 := by icc_omega
      subst this
      rw [hαk]
      exact finite_empty
  have hE1 : endSet G (T 1) = α 2 := by
    rw [(hS2 1 ⟨le_rfl, by icc_omega⟩).1, hα1, empty_union]
  have hm : ∀ j, 1 ≤ j → j ≤ k → j ∈ Icc 1 k := fun j h1 h2 => ⟨h1, h2⟩
  refine ⟨le_rfl, by icc_omega, fun i hi => hS1 (i + 2) (hm _ (by icc_omega) (by icc_omega)),
    (hS1 1 (hm 1 le_rfl (by icc_omega))).1, (hS1 1 (hm 1 le_rfl (by icc_omega))).2,
    (hS1 2 (hm 2 (by icc_omega) (by icc_omega))).1, (hS1 2 (hm 2 (by icc_omega) (by icc_omega))).2, ?_,
    fun i hi hi1 => ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, (hS2 3 (hm 3 (by icc_omega) hk)).2.2.1,
    if_pos rfl, ?_, ?_, ?_, fun i hi => ?_, ?_, hS3 2 ⟨by icc_omega, by icc_omega⟩, fun i hi => ?_,
    (hS4 3 (hm 3 (by icc_omega) hk)).1, ?_, (hS4 2 (hm 2 (by icc_omega) (by icc_omega))).2, ?_, ?_⟩
  · rw [hSU]
    ext q
    simp only [mem_union, mem_iUnion, mem_Icc, exists_prop]
    constructor
    · rintro ⟨j, ⟨hj1, hj2⟩, hq⟩
      rcases (by icc_omega : j = 1 ∨ j = 2 ∨ 3 ≤ j) with rfl | rfl | h3
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq
      · refine Or.inl (Or.inl ⟨j - 2, ⟨by icc_omega, by icc_omega⟩, ?_⟩)
        rwa [Nat.sub_add_cancel (by icc_omega)]
    · rintro ((⟨i, ⟨hi1, hi2⟩, hq⟩ | hq) | hq)
      · exact ⟨i + 2, ⟨by icc_omega, by icc_omega⟩, hq⟩
      · exact ⟨1, ⟨le_rfl, by icc_omega⟩, hq⟩
      · exact ⟨2, ⟨by icc_omega, by icc_omega⟩, hq⟩
  · simp only
    rw [if_neg hi1, if_neg (by icc_omega)]
    exact (hS2 (i + 2) (hm _ (by icc_omega) (by icc_omega))).1 ▸
      ⟨rfl, (hS2 (i + 2) (hm _ (by icc_omega) (by icc_omega))).2.1⟩
  · simp only [if_pos, if_neg (by norm_num : (1 : ℕ) + 1 ≠ 1)]
    rw [(hS2 3 (hm 3 (by icc_omega) hk)).1, empty_union, union_comm]
  · simp
  · simp
  · simp only [if_neg (by norm_num : (1 : ℕ) + 1 ≠ 1)]
    exact (hS2 3 (hm 3 (by icc_omega) hk)).2.1.symm
  · simp only
    split_ifs
    · exact finite_empty
    · exact hfin (i + 2) ⟨by icc_omega, by icc_omega⟩
  · simp only
    rw [if_neg (by icc_omega), show k - 2 + 1 + 2 = k + 1 by icc_omega, hαk]
  · rw [hE1, (hS2 2 (hm 2 (by icc_omega) (by icc_omega))).1]
  · rw [hE1]
    exact (hS2 2 (hm 2 (by icc_omega) (by icc_omega))).2.1
  · simp only
    rw [if_neg (by icc_omega)]
    exact hS3 (i + 2) ⟨by icc_omega, by icc_omega⟩
  · rw [hE1]
    exact hS3 1 ⟨le_rfl, by icc_omega⟩
  · simp only
    rw [if_neg (by icc_omega : i + 1 ≠ 1)]
    refine ⟨?_, (hS4 (i + 2) (hm _ (by icc_omega) (by icc_omega))).2⟩
    split_ifs
    · rw [image_empty]
      exact hasConsCompl_empty _ _
    · exact (hS4 (i + 2) (hm _ (by icc_omega) (by icc_omega))).1
  · rw [hE1]
    exact (hS4 2 (hm 2 (by icc_omega) (by icc_omega))).1
  · have hlist : (List.range' 2 (k - 2 - 1)).map
        (fun i => Prod.fst '' (fun i => if i = 1 then (∅ : Set (E × ℝ)) else α (i + 2)) i) =
        (List.range' 4 (k - 3)).map (fun i => Prod.fst '' α i) := by
      rw [show k - 2 - 1 = k - 3 by icc_omega, List.range'_eq_map_range, List.range'_eq_map_range,
        List.map_map, List.map_map]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply]
      rw [if_neg (by icc_omega), show 2 + i + 2 = 4 + i by icc_omega]
    have hsplit : (List.range' 2 (k - 1)).map (fun i => Prod.fst '' α i) =
        [Prod.fst '' α 2, Prod.fst '' α 3] ++ (List.range' 4 (k - 3)).map (fun i => Prod.fst '' α i) := by
      rw [show k - 1 = k - 3 + 1 + 1 by icc_omega, List.range'_succ, List.range'_succ]
      rfl
    rw [hlist, hE1]
    rw [hsplit] at hS5
    exact hS5.perm List.perm_append_comm
  · simp only [if_pos, image_empty]
    exact empty_disjoint _

/-- **H–O Proposition 17**, existence form. -/
theorem ho16_prop17_exists {G : Set E} {S : Set (E × ℝ)} {k : ℕ} (h : HasStairwell G S k)
    (hk : 3 ≤ k) : HasBrokenStairwell G S (k - 2) 1 := by
  obtain ⟨T, α, h⟩ := h
  exact ⟨_, _, _, _, _, ho16_prop17 h hk⟩

/-- **p. 201, first remark**: if `γ_{i₀} = ∅`, then `⟨S₁, …, S_k⟩` is a stairwell structure for
`S₁ ∪ … ∪ S_k`. -/
theorem ho16_rem17_gamma {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
    {γ P₁ P₂ : Set (E × ℝ)} (h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂) (hγ : γ = ∅) :
    IsStairwellStr G (⋃ i ∈ Icc 1 k, T i) k T α := by
  obtain ⟨hi1, hik, hS1, -, -, -, -, -, hS2, hE, hD, -, -, hfin, -, hα1, hαk, -, -, hS3, -, -,
    hS4, -, -, -, hgen, -⟩ := h
  subst hγ
  refine ⟨by icc_omega, hS1, rfl, fun i hi => ?_, hα1, hαk, hS3, hS4,
    hgen.sublist (List.sublist_append_left _ _)⟩
  have hfi : (α i).Finite := hfin i ⟨hi.1, by icc_omega⟩
  have hfi' : (α (i + 1)).Finite := hfin (i + 1) ⟨by icc_omega, by icc_omega⟩
  by_cases h : i = i₀
  · subst h
    rw [hE, union_empty]
    exact ⟨rfl, hD, hfi, hfi'⟩
  · exact ⟨(hS2 i hi h).1, (hS2 i hi h).2, hfi, hfi'⟩

/-- **p. 201, second remark**: if `𝓔(P₁) = ∅` and `G` is connected, then `π(P₁) = G` and `⟨P₁⟩`
is a stairwell structure of height 1 for `P₁`.

Shape change (batch 195): the skeleton's hypothesis `IsPLGraph G` is not needed and has been
dropped. -/
theorem ho16_rem17_P1 {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
    {γ P₁ P₂ : Set (E × ℝ)} (hconn : IsConnected G)
    (h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂) (hE : endSet G P₁ = ∅) :
    Prod.fst '' P₁ = G ∧ IsStairwellStr G P₁ 1 (fun _ => P₁) (fun _ => ∅) := by
  obtain ⟨-, -, -, hP₁ne, hP₁, -⟩ := h
  have hfr : relFrontier G (Prod.fst '' P₁) = ∅ := by
    rw [← hP₁.image_endSet, hE, image_empty]
  have hcl : IsClosed (Prod.fst '' P₁) := hP₁.2.2.2.isCompact.isClosed
  have hπ : Prod.fst '' P₁ = G := by
    apply Subset.antisymm hP₁.image_subset
    refine IsPreconnected.subset_of_relClopenG hconn.isPreconnected subset_rfl hP₁.image_subset ?_ ?_ ?_
    · intro y hy
      refine mem_nhdsWithin.2 ⟨(closure (G \ Prod.fst '' P₁))ᶜ, isClosed_closure.isOpen_compl,
        fun h => ?_, ?_⟩
      · have : y ∈ relFrontier G (Prod.fst '' P₁) := ⟨subset_closure hy, h⟩
        rw [hfr] at this
        exact this
      · rintro w ⟨hw1, hwG⟩
        by_contra hw
        exact hw1 (subset_closure ⟨hwG, hw⟩)
    · rintro z ⟨-, hz⟩
      rwa [hcl.closure_eq] at hz
    · obtain ⟨y, hy⟩ := hP₁ne.image Prod.fst
      exact ⟨y, hP₁.image_subset hy, hy⟩
  refine ⟨hπ, le_rfl, fun _ _ => ⟨hP₁ne, hP₁⟩, by simp, fun _ _ => ?_, rfl, rfl,
    fun i hi => absurd hi.2 (by icc_omega), fun _ _ => ?_, ⟨by simp, by simp⟩⟩
  · rw [hE, union_empty]
    exact ⟨rfl, disjoint_empty _, finite_empty, finite_empty⟩
  · rw [image_empty]
    exact ⟨hasConsCompl_empty _ _, hasConsCompl_empty _ _⟩

/-- **Stretch (§8): the fold of Proposition 19** (pp. 202–203): `G₁ = π(P₁)`, `G₂ = π(P₂)`,
`G₃ = σ_{π(γ)}(π(S_{i₀}))` satisfy (F1)–(F3), with H–O's two identities and (19.1)–(19.3).

Shape change (batch 195): the skeleton's hypothesis `γ.Nonempty` is not needed and has been
dropped (the proof never uses it). -/
theorem ho16_prop19_fold {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
    {γ P₁ P₂ : Set (E × ℝ)} (hG : IsPLGraph G) (hconn : IsConnected G)
    (h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂)
    (hE : (endSet G P₁).Nonempty) :
    IsFoldTriple G (Prod.fst '' P₁) (Prod.fst '' P₂) (sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀)) ∧
    Prod.fst '' P₁ = sideOf G (Prod.fst '' endSet G P₁) (Prod.fst '' P₂) ∧
    sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀) = sideOf G (Prod.fst '' γ) (Prod.fst '' P₂) ∧
    relFrontier G (Prod.fst '' P₁) = Prod.fst '' endSet G P₁ ∧
    relFrontier G (sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀)) = Prod.fst '' γ ∧
    relFrontier G (Prod.fst '' P₂) = Prod.fst '' endSet G P₁ ∪ Prod.fst '' γ := by
  obtain ⟨hi1, hik, hS1, -, hP₁, hP₂ne, hP₂, -, -, hE', -, -, -, -, -, -, -, hP₂E, hP₁γ, -, hV, hW,
    -, hc24, hc25, hc26, -, -⟩ := h
  have hTi₀ := hS1 i₀ ⟨hi1, hik⟩
  have hfrP₂ : relFrontier G (Prod.fst '' P₂) = Prod.fst '' endSet G P₁ ∪ Prod.fst '' γ := by
    rw [← hP₂.image_endSet, hP₂E, image_union]
  have hsubP₂ : endSet G P₁ ∪ γ ⊆ P₂ := hP₂E ▸ endSet_subset G P₂
  have hdis : Disjoint (Prod.fst '' endSet G P₁) (Prod.fst '' γ) :=
    disjoint_image_fst_of_injOn hP₂.2.2.1 (subset_union_left.trans hsubP₂)
      (subset_union_right.trans hsubP₂) hP₁γ
  have h11 := ho16_prop11 hG hconn hP₂.2.2.2 hP₂.image_subset (hP₂ne.image _) hfrP₂.symm hdis
    hc25 hc26
  have hfr11 := ho16_prop11_frontier hG hP₂.2.2.2 hP₂.image_subset hfrP₂.symm hc25 hc26
  have hB1 : Prod.fst '' endSet G P₁ ⊆ relFrontier G (Prod.fst '' P₂) := by
    rw [hfrP₂]; exact subset_union_left
  have hid1 : Prod.fst '' P₁ = sideOf G (Prod.fst '' endSet G P₁) (Prod.fst '' P₂) :=
    ho16_obs9_unique hG hconn hP₂.2.2.2 hP₂.image_subset (hE.image _) hB1 hc25
      hP₁.image_subset hP₁.2.2.2.isCompact.isClosed hP₁.image_endSet.symm hV
  have hBγ : Prod.fst '' γ ⊆ relFrontier G (Prod.fst '' T i₀) ∩ relFrontier G (Prod.fst '' P₂) := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [← hTi₀.2.image_endSet, hE']
      exact image_mono subset_union_right hy
    · rw [hfrP₂]; exact Or.inr hy
  obtain ⟨W, hW, hWeq⟩ := hW
  have hid2 : sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀) =
      sideOf G (Prod.fst '' γ) (Prod.fst '' P₂) :=
    (ho16_prop10 hG hconn hTi₀.2.2.2.2 hP₂.2.2.2 hTi₀.2.image_subset hP₂.image_subset
      (hTi₀.1.image _) (hP₂ne.image _) hBγ hc24 hc26 hW hWeq.symm).1
  refine ⟨?_, hid1, hid2, hP₁.image_endSet.symm, ?_, hfrP₂⟩
  · rw [hid1, hid2]
    exact h11
  · rw [hid2]
    exact hfr11.2

end Stairwells

end HPC.HO16
