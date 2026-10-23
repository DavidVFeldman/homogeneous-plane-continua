import HPC.HO16.PLLib

/-!
# Batch 194, §5: set algebra of fold triples, and H–O Lemma 6

H–O p. 185: "We record here some basic properties of simple folds. The proofs of these
properties are left to the reader." Items (1), (2), (4), (5), (6), (7) are proved for every
`IsSimpleFoldOf` (`ho16_lemma6`); item (3) is part of the definition.

The first section collects the set algebra of a triple (`G₁ ∪ G₃ = G`, `G₂ = G₁ ∩ G₃`, `G₁`, `G₃`
closed), reused in §4, §6 and §7.
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Algebra

variable {α : Type*} [TopologicalSpace α] {G G₁ G₂ G₃ : Set α}

omit [TopologicalSpace α] in
theorem fold_diff_left (hcov : G₁ ∪ G₃ = G) (hG₂ : G₂ = G₁ ∩ G₃) : G \ G₁ = G₃ \ G₂ := by
  subst hcov hG₂; ext x; simp only [mem_diff, mem_union, mem_inter_iff]; tauto

omit [TopologicalSpace α] in
theorem fold_diff_right (hcov : G₁ ∪ G₃ = G) (hG₂ : G₂ = G₁ ∩ G₃) : G \ G₃ = G₁ \ G₂ := by
  subst hcov hG₂; ext x; simp only [mem_diff, mem_union, mem_inter_iff]; tauto

omit [TopologicalSpace α] in
theorem fold_diff_mid (hcov : G₁ ∪ G₃ = G) (hG₂ : G₂ = G₁ ∩ G₃) :
    G \ G₂ = (G₁ \ G₂) ∪ (G₃ \ G₂) := by
  subst hcov hG₂; ext x; simp only [mem_diff, mem_union, mem_inter_iff]; tauto

omit [TopologicalSpace α] in
theorem fold_diff_diff_left (hcov : G₁ ∪ G₃ = G) (hG₂ : G₂ = G₁ ∩ G₃) :
    G \ (G₁ \ G₂) = G₃ := by
  subst hcov hG₂; ext x; simp only [mem_diff, mem_union, mem_inter_iff]; tauto

omit [TopologicalSpace α] in
theorem fold_diff_diff_right (hcov : G₁ ∪ G₃ = G) (hG₂ : G₂ = G₁ ∩ G₃) :
    G \ (G₃ \ G₂) = G₁ := by
  subst hcov hG₂; ext x; simp only [mem_diff, mem_union, mem_inter_iff]; tauto

/-- `∂G₁ = cl (G₃ \ G₂) ∩ G₂`. -/
theorem relFrontier_left_eq (hG₁ : IsClosed G₁) (hG₃ : IsClosed G₃) (hcov : G₁ ∪ G₃ = G)
    (hG₂ : G₂ = G₁ ∩ G₃) : relFrontier G G₁ = closure (G₃ \ G₂) ∩ G₂ := by
  have hc : closure (G₃ \ G₂) ⊆ G₃ := closure_minimal diff_subset hG₃
  unfold relFrontier
  rw [hG₁.closure_eq, fold_diff_left hcov hG₂]
  ext x
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, hG₂ ▸ ⟨h1, hc h2⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨(hG₂ ▸ h2 : x ∈ G₁ ∩ G₃).1, h1⟩

/-- `∂G₃ = cl (G₁ \ G₂) ∩ G₂`. -/
theorem relFrontier_right_eq (hG₁ : IsClosed G₁) (hG₃ : IsClosed G₃) (hcov : G₁ ∪ G₃ = G)
    (hG₂ : G₂ = G₁ ∩ G₃) : relFrontier G G₃ = closure (G₁ \ G₂) ∩ G₂ := by
  have hG₂' : G₂ = G₃ ∩ G₁ := hG₂.trans (inter_comm _ _)
  exact relFrontier_left_eq hG₃ hG₁ ((union_comm _ _).trans hcov) hG₂'

theorem relFrontier_mid_eq (hG₁ : IsClosed G₁) (hG₃ : IsClosed G₃) (hcov : G₁ ∪ G₃ = G)
    (hG₂ : G₂ = G₁ ∩ G₃) : relFrontier G G₂ = relFrontier G G₁ ∪ relFrontier G G₃ := by
  rw [relFrontier_left_eq hG₁ hG₃ hcov hG₂, relFrontier_right_eq hG₁ hG₃ hcov hG₂]
  unfold relFrontier
  have hG₂c : IsClosed G₂ := hG₂ ▸ hG₁.inter hG₃
  rw [hG₂c.closure_eq, fold_diff_mid hcov hG₂, closure_union]
  ext x; simp only [mem_inter_iff, mem_union]; tauto

theorem relFrontier_disjoint (hG₁ : IsClosed G₁) (hG₃ : IsClosed G₃) (hcov : G₁ ∪ G₃ = G)
    (hG₂ : G₂ = G₁ ∩ G₃) (hF3 : Disjoint (closure (G₁ \ G₂)) (closure (G₃ \ G₂))) :
    Disjoint (relFrontier G G₁) (relFrontier G G₃) := by
  rw [relFrontier_left_eq hG₁ hG₃ hcov hG₂, relFrontier_right_eq hG₁ hG₃ hcov hG₂]
  exact (hF3.symm.mono inter_subset_left inter_subset_left)

theorem relFrontier_diff_left (hG₁ : IsClosed G₁) (hG₃ : IsClosed G₃) (hcov : G₁ ∪ G₃ = G)
    (hG₂ : G₂ = G₁ ∩ G₃) : relFrontier G (G₁ \ G₂) = relFrontier G G₃ := by
  rw [relFrontier_right_eq hG₁ hG₃ hcov hG₂]
  unfold relFrontier
  rw [fold_diff_diff_left hcov hG₂, hG₃.closure_eq]
  have hc : closure (G₁ \ G₂) ⊆ G₁ := closure_minimal diff_subset hG₁
  ext x
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, hG₂ ▸ ⟨hc h1, h2⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (hG₂ ▸ h2 : x ∈ G₁ ∩ G₃).2⟩

theorem relFrontier_diff_right (hG₁ : IsClosed G₁) (hG₃ : IsClosed G₃) (hcov : G₁ ∪ G₃ = G)
    (hG₂ : G₂ = G₁ ∩ G₃) : relFrontier G (G₃ \ G₂) = relFrontier G G₁ := by
  have hG₂' : G₂ = G₃ ∩ G₁ := hG₂.trans (inter_comm _ _)
  exact relFrontier_diff_left hG₃ hG₁ ((union_comm _ _).trans hcov) hG₂'

/-- A set `A` is a neighbourhood within `G` of every point outside `cl (G \ A)`. -/
theorem mem_nhdsWithin_of_not_mem_closure_diff {A : Set α} {y : α}
    (h : y ∉ closure (G \ A)) : A ∈ 𝓝[G] y :=
  mem_nhdsWithin.2 ⟨(closure (G \ A))ᶜ, isClosed_closure.isOpen_compl, h,
    fun _ ⟨hz1, hz2⟩ => by_contra fun hzA => hz1 (subset_closure ⟨hz2, hzA⟩)⟩

end Algebra

section Inj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- `Prod.fst` restricted to a compact set on which it is injective maps neighbourhoods to
relative neighbourhoods. -/
theorem image_fst_mem_nhdsWithin {K : Set (E × ℝ)} (hK : IsCompact K)
    (hinj : InjOn Prod.fst K) {p : E × ℝ} (hp : p ∈ K) {N : Set (E × ℝ)} (hN : N ∈ 𝓝 p) :
    Prod.fst '' (N ∩ K) ∈ 𝓝[Prod.fst '' K] p.1 := by
  set C := K \ interior N
  have hC : IsCompact (Prod.fst '' C) := (hK.diff isOpen_interior).image continuous_fst
  have hpC : p.1 ∉ Prod.fst '' C := by
    rintro ⟨q, ⟨hqK, hqN⟩, hq⟩
    have : q = p := hinj hqK hp hq
    subst this
    exact hqN (mem_interior_iff_mem_nhds.2 hN)
  refine mem_nhdsWithin.2 ⟨(Prod.fst '' C)ᶜ, hC.isClosed.isOpen_compl, hpC, ?_⟩
  rintro y ⟨hyC, ⟨q, hqK, rfl⟩⟩
  refine ⟨q, ⟨?_, hqK⟩, rfl⟩
  by_contra hqN
  exact hyC ⟨q, ⟨hqK, fun h => hqN (interior_subset h)⟩, rfl⟩

omit [NormedSpace ℝ E] in
/-- `Prod.fst` on a compact set on which it is injective has a continuous inverse. -/
theorem continuousOn_invFunOn_fst {K : Set (E × ℝ)} (hK : IsCompact K)
    (hinj : InjOn Prod.fst K) :
    ContinuousOn (Function.invFunOn Prod.fst K) (Prod.fst '' K) := by
  rintro _ ⟨p, hp, rfl⟩
  have hψp : Function.invFunOn Prod.fst K p.1 = p := hinj.leftInvOn_invFunOn hp
  rw [ContinuousWithinAt, hψp]
  intro N hN
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (image_fst_mem_nhdsWithin hK hinj hp hN) ?_
  rintro _ ⟨q, ⟨hqN, hqK⟩, rfl⟩
  show Function.invFunOn Prod.fst K q.1 ∈ N
  rw [hinj.leftInvOn_invFunOn hqK]
  exact hqN

end Inj

section Fold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsFoldTriple.isPLGraph {G G₁ G₂ G₃ : Set E} (h : IsFoldTriple G G₁ G₂ G₃) :
    IsPLGraph G := by
  obtain ⟨-, -, -, h1, -, h3, hcov, -⟩ := h
  exact hcov ▸ h1.union h3

theorem IsFoldTriple.relFrontier_left_finite {G G₁ G₂ G₃ : Set E}
    (h : IsFoldTriple G G₁ G₂ G₃) : (relFrontier G G₁).Finite := by
  have hG := h.isPLGraph
  obtain ⟨-, -, -, h1, -, -, hcov, -⟩ := h
  exact hG.relFrontier_finite h1 (hcov ▸ subset_union_left)

theorem IsFoldTriple.relFrontier_right_finite {G G₁ G₂ G₃ : Set E}
    (h : IsFoldTriple G G₁ G₂ G₃) : (relFrontier G G₃).Finite := by
  have hG := h.isPLGraph
  obtain ⟨-, -, -, -, -, h3, hcov, -⟩ := h
  exact hG.relFrontier_finite h3 (hcov ▸ subset_union_right)

/-- **H–O Lemma 6**, items (1), (2), (4), (5), (6), (7); item (3) is part of `IsSimpleFoldOf`
(each `Fᵢ` is a PL graph). -/
theorem ho16_lemma6 {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) :
    -- (1)
    relFrontier G G₂ = relFrontier G G₁ ∪ relFrontier G G₃ ∧
    Disjoint (relFrontier G G₁) (relFrontier G G₃) ∧
    -- (2)
    relFrontier G (G₁ \ G₂) = relFrontier G G₃ ∧ relFrontier G (G₃ \ G₂) = relFrontier G G₁ ∧
    -- (4)
    (F₁ ∩ F₂).Finite ∧ (F₂ ∩ F₃).Finite ∧
    -- (5)
    relFrontier (F₁ ∪ F₂ ∪ F₃) F₁ = F₁ ∩ F₂ ∧ relFrontier (F₁ ∪ F₂ ∪ F₃) F₃ = F₂ ∩ F₃ ∧
    relFrontier (F₁ ∪ F₂ ∪ F₃) F₂ = (F₁ ∩ F₂) ∪ (F₂ ∩ F₃) ∧
    -- (6)
    SeparatesIn (F₁ ∪ F₂ ∪ F₃) (F₁ ∩ F₂) (F₁ \ F₂) ((F₂ ∪ F₃) \ F₁) ∧
    SeparatesIn (F₁ ∪ F₂ ∪ F₃) (F₂ ∩ F₃) (F₃ \ F₂) ((F₁ ∪ F₂) \ F₃) ∧
    -- (7)
    (∀ p ∈ F₁ \ F₂, ∀ N ∈ 𝓝 p, Prod.fst '' (N ∩ F₁) ∈ 𝓝[G] p.1) ∧
    (∀ p ∈ F₂ \ (F₁ ∪ F₃), ∀ N ∈ 𝓝 p, Prod.fst '' (N ∩ F₂) ∈ 𝓝[G] p.1) ∧
    (∀ p ∈ F₃ \ F₂, ∀ N ∈ 𝓝 p, Prod.fst '' (N ∩ F₃) ∈ 𝓝[G] p.1) := by
  obtain ⟨hT, hP₁, hP₂, hP₃, hi₁, he₁, hi₂, he₂, hi₃, he₃, h12, h23, h13⟩ := hF
  have hT' := hT
  obtain ⟨-, -, -, hG₁, hG₂P, hG₃, hcov, hG₂, hF3⟩ := hT'
  have hG₁c := hG₁.isCompact.isClosed
  have hG₃c := hG₃.isCompact.isClosed
  have hF₁c := hP₁.isCompact.isClosed
  have hF₂c := hP₂.isCompact.isClosed
  have hF₃c := hP₃.isCompact.isClosed
  have hfin12 : (F₁ ∩ F₂).Finite :=
    Finite.of_finite_image (h12 ▸ hT.relFrontier_left_finite) (hi₁.mono inter_subset_left)
  have hfin23 : (F₂ ∩ F₃).Finite :=
    Finite.of_finite_image (h23 ▸ hT.relFrontier_right_finite) (hi₂.mono inter_subset_left)
  have hd13 : ∀ x, x ∈ F₁ → x ∈ F₃ → False := fun x h1 h3 => h13.ne_of_mem h1 h3 rfl
  refine ⟨relFrontier_mid_eq hG₁c hG₃c hcov hG₂, relFrontier_disjoint hG₁c hG₃c hcov hG₂ hF3,
    relFrontier_diff_left hG₁c hG₃c hcov hG₂, relFrontier_diff_right hG₁c hG₃c hcov hG₂,
    hfin12, hfin23, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (5)
  · unfold relFrontier
    rw [hF₁c.closure_eq]
    apply Subset.antisymm
    · rintro x ⟨hx1, hx2⟩
      have : closure ((F₁ ∪ F₂ ∪ F₃) \ F₁) ⊆ F₂ ∪ F₃ :=
        closure_minimal (fun y hy => by
          rcases hy with ⟨(h | h) | h, hn⟩
          · exact absurd h hn
          · exact Or.inl h
          · exact Or.inr h) (hF₂c.union hF₃c)
      rcases this hx2 with h | h
      · exact ⟨hx1, h⟩
      · exact absurd h (fun h' => hd13 x hx1 h')
    · rintro x ⟨hx1, hx2⟩
      refine ⟨hx1, closure_mono ?_ (hP₂.mem_closure_diff_finite hx2 hfin12)⟩
      rintro y ⟨hy2, hy⟩
      exact ⟨Or.inl (Or.inr hy2), fun hy1 => hy ⟨hy1, hy2⟩⟩
  · unfold relFrontier
    rw [hF₃c.closure_eq]
    apply Subset.antisymm
    · rintro x ⟨hx3, hx2⟩
      have : closure ((F₁ ∪ F₂ ∪ F₃) \ F₃) ⊆ F₁ ∪ F₂ :=
        closure_minimal (fun y hy => by
          rcases hy with ⟨(h | h) | h, hn⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hn) (hF₁c.union hF₂c)
      rcases this hx2 with h | h
      · exact absurd hx3 (fun h' => hd13 x h h')
      · exact ⟨h, hx3⟩
    · rintro x ⟨hx2, hx3⟩
      refine ⟨hx3, closure_mono ?_ (hP₂.mem_closure_diff_finite hx2 hfin23)⟩
      rintro y ⟨hy2, hy⟩
      exact ⟨Or.inl (Or.inr hy2), fun hy3 => hy ⟨hy2, hy3⟩⟩
  · unfold relFrontier
    rw [hF₂c.closure_eq]
    apply Subset.antisymm
    · rintro x ⟨hx2, hx⟩
      have : closure ((F₁ ∪ F₂ ∪ F₃) \ F₂) ⊆ F₁ ∪ F₃ :=
        closure_minimal (fun y hy => by
          rcases hy with ⟨(h | h) | h, hn⟩
          · exact Or.inl h
          · exact absurd h hn
          · exact Or.inr h) (hF₁c.union hF₃c)
      rcases this hx with h | h
      · exact Or.inl ⟨h, hx2⟩
      · exact Or.inr ⟨hx2, h⟩
    · rintro x (⟨hx1, hx2⟩ | ⟨hx2, hx3⟩)
      · refine ⟨hx2, closure_mono ?_ (hP₁.mem_closure_diff_finite hx1 hfin12)⟩
        rintro y ⟨hy1, hy⟩
        exact ⟨Or.inl (Or.inl hy1), fun hy2 => hy ⟨hy1, hy2⟩⟩
      · refine ⟨hx2, closure_mono ?_ (hP₃.mem_closure_diff_finite hx3 hfin23)⟩
        rintro y ⟨hy3, hy⟩
        exact ⟨Or.inr hy3, fun hy2 => hy ⟨hy2, hy3⟩⟩
  -- (6)
  · refine ⟨(F₂ ∪ F₃)ᶜ, F₁ᶜ, (hF₂c.union hF₃c).isOpen_compl, hF₁c.isOpen_compl, ?_, ?_, ?_, ?_⟩
    · rintro x ⟨hx, hxM⟩
      by_cases h1 : x ∈ F₁
      · left
        rintro (h2 | h3)
        · exact hxM ⟨h1, h2⟩
        · exact hd13 x h1 h3
      · exact Or.inr h1
    · ext x
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨⟨hU, hV⟩, hx, -⟩
      rcases hx with (h | h) | h
      · exact hV h
      · exact hU (Or.inl h)
      · exact hU (Or.inr h)
    · rintro x ⟨h1, h2⟩ (h2' | h3)
      · exact h2 h2'
      · exact hd13 x h1 h3
    · rintro x ⟨-, h1⟩; exact h1
  · refine ⟨(F₁ ∪ F₂)ᶜ, F₃ᶜ, (hF₁c.union hF₂c).isOpen_compl, hF₃c.isOpen_compl, ?_, ?_, ?_, ?_⟩
    · rintro x ⟨hx, hxM⟩
      by_cases h3 : x ∈ F₃
      · left
        rintro (h1 | h2)
        · exact hd13 x h1 h3
        · exact hxM ⟨h2, h3⟩
      · exact Or.inr h3
    · ext x
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨⟨hU, hV⟩, hx, -⟩
      rcases hx with (h | h) | h
      · exact hU (Or.inl h)
      · exact hU (Or.inr h)
      · exact hV h
    · rintro x ⟨h3, h2⟩ (h1 | h2')
      · exact hd13 x h1 h3
      · exact h2 h2'
    · rintro x ⟨-, h3⟩; exact h3
  -- (7)
  · rintro p ⟨hp1, hp2⟩ N hN
    have h := image_fst_mem_nhdsWithin hP₁.isCompact hi₁ hp1 hN
    rw [he₁] at h
    refine Filter.mem_of_superset (nhdsWithin_le_of_mem ?_ h) subset_rfl
    apply mem_nhdsWithin_of_not_mem_closure_diff
    intro hc
    have hmem : p.1 ∈ relFrontier G G₁ := by
      refine ⟨subset_closure (he₁ ▸ mem_image_of_mem _ hp1), hc⟩
    rw [← h12] at hmem
    obtain ⟨q, ⟨hq1, hq2⟩, hq⟩ := hmem
    exact hp2 (hi₁ hq1 hp1 hq ▸ hq2)
  · rintro p ⟨hp2, hp13⟩ N hN
    have h := image_fst_mem_nhdsWithin hP₂.isCompact hi₂ hp2 hN
    rw [he₂] at h
    refine Filter.mem_of_superset (nhdsWithin_le_of_mem ?_ h) subset_rfl
    apply mem_nhdsWithin_of_not_mem_closure_diff
    have hpG₂ : p.1 ∈ G₂ := he₂ ▸ mem_image_of_mem _ hp2
    rw [fold_diff_mid hcov hG₂, closure_union]
    rintro (hc | hc)
    · have hmem : p.1 ∈ relFrontier G G₃ := by
        rw [relFrontier_right_eq hG₁c hG₃c hcov hG₂]; exact ⟨hc, hpG₂⟩
      rw [← h23] at hmem
      obtain ⟨q, ⟨hq2, hq3⟩, hq⟩ := hmem
      exact hp13 (Or.inr (hi₂ hq2 hp2 hq ▸ hq3))
    · have hmem : p.1 ∈ relFrontier G G₁ := by
        rw [relFrontier_left_eq hG₁c hG₃c hcov hG₂]; exact ⟨hc, hpG₂⟩
      rw [← h12] at hmem
      obtain ⟨q, ⟨hq1, hq2⟩, hq⟩ := hmem
      exact hp13 (Or.inl (hi₂ hq2 hp2 hq ▸ hq1))
  · rintro p ⟨hp3, hp2⟩ N hN
    have h := image_fst_mem_nhdsWithin hP₃.isCompact hi₃ hp3 hN
    rw [he₃] at h
    refine Filter.mem_of_superset (nhdsWithin_le_of_mem ?_ h) subset_rfl
    apply mem_nhdsWithin_of_not_mem_closure_diff
    intro hc
    have hmem : p.1 ∈ relFrontier G G₃ := by
      refine ⟨subset_closure (he₃ ▸ mem_image_of_mem _ hp3), hc⟩
    rw [← h23] at hmem
    obtain ⟨q, ⟨hq2, hq3⟩, hq⟩ := hmem
    exact hp2 (hi₃ hq3 hp3 hq ▸ hq2)

end Fold

end HPC.HO16
