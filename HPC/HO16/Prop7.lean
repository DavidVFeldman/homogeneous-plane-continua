import HPC.HO16.Lemma6

/-!
# Batch 194, §7: H–O Proposition 7

H–O pp. 186–187: "Suppose that G is connected, and that ∂G₁ ≠ ∅ ≠ ∂G₃. Then there is a
component C of F such that φ(C) meets ∂G₁ and ∂G₃. Moreover, for any such component,
φ(C) = G, and if we let F′ᵢ = Fᵢ ∩ C for i = 1, 2, 3, then F′ = F′₁ ∪ F′₂ ∪ F′₃ is also a simple
fold on G, with projection map φ|F′ : F′ → G."

Route (commission 194, §7): the steps H–O leave unargued are supplied by Lemma (L)
(`disjoint_lift_of_disjoint_right`, `comp_not_disjoint_both`, `lift_subset_of_meets_both`):
for a component `K` of `G₂` with copies `Kᵢ = Fᵢ ∩ φ⁻¹(K)`,
(a) if `K` misses `∂G₃`, then `K₁ ∪ K₂` is clopen in `F` and misses every component `C` whose
projection meets `∂G₃`;
(b) if `K` meets `∂G₁` and `∂G₃`, then `K₁ ∪ K₂ ∪ K₃` is connected, so it lies in `C` as soon
as it meets `C`;
(c) `K` cannot miss both `∂G₁` and `∂G₃`.
The openness of `φ(C)` follows the commission's preferred route (no boundary bumping).
Statements symmetric under `1 ↔ 3` are derived from the swapped fold `IsSimpleFoldOf.symm`.
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Topo

variable {α : Type*} [TopologicalSpace α]

/-- A preconnected subset of `F` meeting a relatively clopen subset `A = F ∩ W` (with `W` open
and `A` closed) lies in `A`. -/
theorem subset_of_relClopen {F A W C : Set α} (hW : IsOpen W) (hA : IsClosed A)
    (hFW : F ∩ W = A) (hC : IsPreconnected C) (hCF : C ⊆ F) (hne : (C ∩ A).Nonempty) :
    C ⊆ A := by
  have hAW : A ⊆ W := fun y hy => by rw [← hFW] at hy; exact hy.2
  by_contra hsub
  rw [not_subset] at hsub
  obtain ⟨x, hxC, hxA⟩ := hsub
  obtain ⟨y, hyC, hyA⟩ := hne
  obtain ⟨z, hzC, hzW, hzA⟩ := hC W Aᶜ hW hA.isOpen_compl
    (fun y _ => by
      by_cases h : y ∈ A
      · exact Or.inl (hAW h)
      · exact Or.inr h)
    ⟨y, hyC, hAW hyA⟩ ⟨x, hxC, hxA⟩
  exact hzA (by rw [← hFW]; exact ⟨hCF hzC, hzW⟩)

/-- A subset which is a relative neighbourhood of each of its points is relatively open. -/
theorem exists_open_inter_eq {G K : Set α} (hKG : K ⊆ G) (h : ∀ y ∈ K, K ∈ 𝓝[G] y) :
    ∃ O, IsOpen O ∧ O ∩ G = K := by
  choose! u hu using fun y hy => mem_nhdsWithin.1 (h y hy)
  refine ⟨⋃ y ∈ K, u y, isOpen_biUnion (fun y hy => (hu y hy).1), ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hx, hxG⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
    exact (hu y hy).2.2 ⟨hxy, hxG⟩
  · intro x hx
    exact ⟨mem_biUnion hx (hu x hx).2.1, hKG hx⟩

end Topo

section PL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A component of a PL graph is a relative neighbourhood of each of its points. -/
theorem IsPLGraph.comp_mem_nhdsWithin {G : Set E} (hG : IsPLGraph G) {y x : E}
    (hx : x ∈ _root_.connectedComponentIn G y) : _root_.connectedComponentIn G y ∈ 𝓝[G] x := by
  classical
  rw [connectedComponentIn_eq hx]
  obtain ⟨S, -, hGS, -⟩ := hG
  set Z := ⋃ s ∈ S.filter (fun s => x ∉ segment ℝ s.1 s.2), segment ℝ s.1 s.2
  have hZ : IsClosed Z := isClosed_biUnion_segment _
  have hxZ : x ∉ Z := by
    intro h
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 h
    exact (Finset.mem_filter.1 hs).2 hxs
  refine mem_nhdsWithin.2 ⟨Zᶜ, hZ.isOpen_compl, hxZ, ?_⟩
  rintro z ⟨hzZ, hzG⟩
  have hzG' := hzG
  rw [hGS] at hzG'
  obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hzG'
  have hxs : x ∈ segment ℝ s.1 s.2 := by
    by_contra h
    exact hzZ (mem_biUnion (Finset.mem_filter.2 ⟨hs, h⟩) hzs)
  refine (convex_segment _ _).isPreconnected.subset_connectedComponentIn hxs ?_ hzs
  rw [hGS]
  exact subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2) hs

/-- A component of a PL graph is relatively open. -/
theorem IsPLGraph.exists_open_comp {G : Set E} (hG : IsPLGraph G) (y : E) :
    ∃ O, IsOpen O ∧ O ∩ G = _root_.connectedComponentIn G y :=
  exists_open_inter_eq (connectedComponentIn_subset G y) fun _ hx => hG.comp_mem_nhdsWithin hx

omit [NormedSpace ℝ E] in
/-- The copy `F ∩ φ⁻¹(K)` of a preconnected `K ⊆ φ(F)` is preconnected. -/
theorem isPreconnected_lift {F : Set (E × ℝ)} (hF : IsCompact F) (hinj : InjOn Prod.fst F)
    {K : Set E} (hK : IsPreconnected K) (hKF : K ⊆ Prod.fst '' F) :
    IsPreconnected (F ∩ Prod.fst ⁻¹' K) := by
  have : F ∩ Prod.fst ⁻¹' K = Function.invFunOn Prod.fst F '' K := by
    ext q
    constructor
    · rintro ⟨hq, hqK⟩
      exact ⟨q.1, hqK, hinj.leftInvOn_invFunOn hq⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Function.invFunOn_mem (hKF hy), ?_⟩
      show (Function.invFunOn Prod.fst F y).1 ∈ K
      rw [Function.invFunOn_eq (hKF hy)]
      exact hy
  rw [this]
  exact hK.image _ ((continuousOn_invFunOn_fst hF hinj).mono hKF)

end PL

section Fold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fold read backwards (`1 ↔ 3`). -/
theorem IsSimpleFoldOf.symm {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) : IsSimpleFoldOf G G₃ G₂ G₁ F₃ F₂ F₁ := by
  obtain ⟨⟨n₁, n₂, n₃, p₁, p₂, p₃, hcov, hG₂, hF3⟩, hP₁, hP₂, hP₃, hi₁, he₁, hi₂, he₂, hi₃,
    he₃, h12, h23, h13⟩ := hF
  exact ⟨⟨n₃, n₂, n₁, p₃, p₂, p₁, (union_comm _ _).trans hcov, hG₂.trans (inter_comm _ _),
    hF3.symm⟩, hP₃, hP₂, hP₁, hi₃, he₃, hi₂, he₂, hi₁, he₁, by rw [inter_comm]; exact h23,
    by rw [inter_comm]; exact h12, h13.symm⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem fold_union_symm (F₁ F₂ F₃ : Set (E × ℝ)) : F₃ ∪ F₂ ∪ F₁ = F₁ ∪ F₂ ∪ F₃ := by
  ext; simp only [mem_union]; tauto

/-- The glue points over `∂G₁`: the `F₁`- and `F₂`-points over `y ∈ ∂G₁` coincide. -/
theorem IsSimpleFoldOf.exists_glue {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) {y : E} (hy : y ∈ relFrontier G G₁) :
    ∃ q ∈ F₁ ∩ F₂, q.1 = y := by
  rw [← hF.2.2.2.2.2.2.2.2.2.2.1] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨q, hq, rfl⟩

theorem IsSimpleFoldOf.isPLGraph_union {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) : IsPLGraph (F₁ ∪ F₂ ∪ F₃) :=
  (hF.2.1.union hF.2.2.1).union hF.2.2.2.1

theorem IsSimpleFoldOf.image_union {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) : Prod.fst '' (F₁ ∪ F₂ ∪ F₃) = G := by
  obtain ⟨⟨-, -, -, -, -, -, hcov, hG₂, -⟩, -, -, -, -, he₁, -, he₂, -, he₃, -⟩ := hF
  rw [Set.image_union, Set.image_union, he₁, he₂, he₃, ← hcov, hG₂]
  ext; simp only [mem_union, mem_inter_iff]; tauto

/-- **Lemma (L)(a)**: if the component `K` of `G₂` through `y` misses `∂G₃`, then `K₁ ∪ K₂` misses
every component `C` of `F` whose projection meets `∂G₃`. -/
theorem disjoint_lift_of_disjoint_right {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ)
    (hC3 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₃).Nonempty) (y : E)
    (hK : Disjoint (connectedComponentIn G₂ y) (relFrontier G G₃)) :
    Disjoint (connectedComponentIn F p) ((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' connectedComponentIn G₂ y) := by
  obtain ⟨⟨-, -, -, hG₁, hG₂P, hG₃, hcov, hG₂, -⟩, hP₁, hP₂, hP₃, -, he₁, -, he₂, -, -, -, h23,
    h13⟩ := hF
  have hG₁c := hG₁.isCompact.isClosed
  have hG₃c := hG₃.isCompact.isClosed
  set K := connectedComponentIn G₂ y with hKdef
  have hKG₂ : K ⊆ G₂ := connectedComponentIn_subset _ _
  have hKc : IsClosed K := (hG₂P.connectedComponentIn y).isCompact.isClosed
  obtain ⟨O, hO, hOK⟩ := hG₂P.exists_open_comp y
  set O' := O \ closure (G₁ \ G₂)
  have hO'K : O' ∩ G₁ = K := by
    apply Subset.antisymm
    · rintro z ⟨⟨hzO, hzc⟩, hzG₁⟩
      have hzG₂ : z ∈ G₂ := by
        by_contra h; exact hzc (subset_closure ⟨hzG₁, h⟩)
      rw [hKdef, ← hOK]; exact ⟨hzO, hzG₂⟩
    · intro z hz
      have hzO : z ∈ O := by rw [hKdef, ← hOK] at hz; exact hz.1
      refine ⟨⟨hzO, fun hzc => ?_⟩, (hG₂ ▸ hKG₂ hz : z ∈ G₁ ∩ G₃).1⟩
      have : z ∈ relFrontier G G₃ := by
        rw [relFrontier_right_eq hG₁c hG₃c hcov hG₂]; exact ⟨hzc, hKG₂ hz⟩
      exact hK.ne_of_mem hz this rfl
  set A := (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' K
  set W := Prod.fst ⁻¹' O' ∩ F₃ᶜ
  have hW : IsOpen W :=
    ((hO.sdiff isClosed_closure).preimage continuous_fst).inter hP₃.isCompact.isClosed.isOpen_compl
  have hA : IsClosed A :=
    (hP₁.isCompact.isClosed.union hP₂.isCompact.isClosed).inter (hKc.preimage continuous_fst)
  have hG₂G₁ : G₂ ⊆ G₁ := hG₂ ▸ inter_subset_left
  have hFW : F ∩ W = A := by
    apply Subset.antisymm
    · rintro q ⟨hqF, hqO, hq3⟩
      rw [hFeq] at hqF
      have hq12 : q ∈ F₁ ∪ F₂ := by
        rcases hqF with h | h
        · exact h
        · exact absurd h hq3
      have hqG₁ : q.1 ∈ G₁ := by
        rcases hq12 with h | h
        · exact he₁ ▸ mem_image_of_mem _ h
        · exact hG₂G₁ (he₂ ▸ mem_image_of_mem _ h)
      exact ⟨hq12, (hO'K ▸ ⟨hqO, hqG₁⟩ : q.1 ∈ K)⟩
    · rintro q ⟨hq12, hqK⟩
      refine ⟨hFeq ▸ Or.inl hq12, ?_, fun hq3 => ?_⟩
      · have : q.1 ∈ O' ∩ G₁ := hO'K.symm ▸ hqK
        exact this.1
      · rcases hq12 with h | h
        · exact h13.ne_of_mem h hq3 rfl
        · have : q.1 ∈ relFrontier G G₃ := h23 ▸ mem_image_of_mem _ ⟨h, hq3⟩
          exact hK.ne_of_mem hqK this rfl
  rw [Set.disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro hne
  have hsub := subset_of_relClopen hW hA hFW (isPreconnected_connectedComponentIn)
    (connectedComponentIn_subset _ _) hne
  obtain ⟨z, ⟨q, hqC, rfl⟩, hz3⟩ := hC3
  exact hK.ne_of_mem (hsub hqC).2 hz3 rfl

/-- **Lemma (L)(c)**: a component of `G₂` cannot miss both `∂G₁` and `∂G₃`. -/
theorem comp_not_disjoint_both {G G₁ G₂ G₃ : Set E} (hT : IsFoldTriple G G₁ G₂ G₃)
    (hG : IsConnected G) (h₃ : (relFrontier G G₃).Nonempty) {y : E} (hy : y ∈ G₂) :
    ¬ (Disjoint (connectedComponentIn G₂ y) (relFrontier G G₁) ∧
      Disjoint (connectedComponentIn G₂ y) (relFrontier G G₃)) := by
  rintro ⟨hK1, hK3⟩
  obtain ⟨-, -, -, hG₁, hG₂P, hG₃, hcov, hG₂, -⟩ := hT
  have hG₁c := hG₁.isCompact.isClosed
  have hG₃c := hG₃.isCompact.isClosed
  set K := connectedComponentIn G₂ y with hKdef
  have hKG₂ : K ⊆ G₂ := connectedComponentIn_subset _ _
  have hKc : IsClosed K := (hG₂P.connectedComponentIn y).isCompact.isClosed
  obtain ⟨O, hO, hOK⟩ := hG₂P.exists_open_comp y
  set O' := O \ (closure (G₁ \ G₂) ∪ closure (G₃ \ G₂))
  have hG₂G : G₂ ⊆ G := fun z hz => hcov ▸ Or.inl (hG₂ ▸ hz : z ∈ G₁ ∩ G₃).1
  have hO'K : G ∩ O' = K := by
    apply Subset.antisymm
    · rintro z ⟨hzG, hzO, hzc⟩
      have hzG₂ : z ∈ G₂ := by
        by_contra h
        rw [← hcov] at hzG
        rcases hzG with h' | h'
        · exact hzc (Or.inl (subset_closure ⟨h', h⟩))
        · exact hzc (Or.inr (subset_closure ⟨h', h⟩))
      rw [hKdef, ← hOK]; exact ⟨hzO, hzG₂⟩
    · intro z hz
      have hzO : z ∈ O := by rw [hKdef, ← hOK] at hz; exact hz.1
      refine ⟨hG₂G (hKG₂ hz), hzO, ?_⟩
      rintro (hzc | hzc)
      · have : z ∈ relFrontier G G₃ := by
          rw [relFrontier_right_eq hG₁c hG₃c hcov hG₂]; exact ⟨hzc, hKG₂ hz⟩
        exact hK3.ne_of_mem hz this rfl
      · have : z ∈ relFrontier G G₁ := by
          rw [relFrontier_left_eq hG₁c hG₃c hcov hG₂]; exact ⟨hzc, hKG₂ hz⟩
        exact hK1.ne_of_mem hz this rfl
  have hGK := subset_of_relClopen (hO.sdiff (isClosed_closure.union isClosed_closure)) hKc hO'K
    hG.isPreconnected subset_rfl ⟨y, hG₂G hy, mem_connectedComponentIn hy⟩
  obtain ⟨z, hz⟩ := h₃
  have hzG₂ : z ∈ G₂ := by
    rw [relFrontier_right_eq hG₁c hG₃c hcov hG₂] at hz; exact hz.2
  exact hK3.ne_of_mem (hGK (hG₂G hzG₂)) hz rfl

/-- **Lemma (L)(b)**: if the component `K` of `G₂` through `y` meets `∂G₁` and `∂G₃`, its three
copies form a connected set; it lies in every component of `F` it meets. -/
theorem lift_subset_of_meets_both {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ) (y : E)
    (h1 : (connectedComponentIn G₂ y ∩ relFrontier G G₁).Nonempty)
    (h3 : (connectedComponentIn G₂ y ∩ relFrontier G G₃).Nonempty)
    (hne : (connectedComponentIn F p ∩ (F ∩ Prod.fst ⁻¹' connectedComponentIn G₂ y)).Nonempty) :
    F ∩ Prod.fst ⁻¹' connectedComponentIn G₂ y ⊆ connectedComponentIn F p := by
  have hF' := hF
  obtain ⟨⟨-, -, -, -, -, -, -, hG₂, -⟩, hP₁, hP₂, hP₃, hi₁, he₁, hi₂, he₂, hi₃, he₃, h12, h23,
    -⟩ := hF'
  set K := connectedComponentIn G₂ y with hKdef
  have hKG₂ : K ⊆ G₂ := connectedComponentIn_subset _ _
  have hKpc : IsPreconnected K := isPreconnected_connectedComponentIn
  have hG₂G₁ : G₂ ⊆ G₁ := hG₂ ▸ inter_subset_left
  have hG₂G₃ : G₂ ⊆ G₃ := hG₂ ▸ inter_subset_right
  have c1 := isPreconnected_lift hP₁.isCompact hi₁ hKpc (he₁.symm ▸ hKG₂.trans hG₂G₁)
  have c2 := isPreconnected_lift hP₂.isCompact hi₂ hKpc (he₂.symm ▸ hKG₂)
  have c3 := isPreconnected_lift hP₃.isCompact hi₃ hKpc (he₃.symm ▸ hKG₂.trans hG₂G₃)
  obtain ⟨z₁, hz₁K, hz₁⟩ := h1
  obtain ⟨z₃, hz₃K, hz₃⟩ := h3
  obtain ⟨q, ⟨hq1, hq2⟩, hqz⟩ := hF.exists_glue hz₁
  have hz₃' : z₃ ∈ Prod.fst '' (F₂ ∩ F₃) := h23.symm ▸ hz₃
  obtain ⟨q', ⟨hq'2, hq'3⟩, hq'z⟩ := hz₃'
  have c12 : IsPreconnected ((F₁ ∩ Prod.fst ⁻¹' K) ∪ (F₂ ∩ Prod.fst ⁻¹' K)) :=
    c1.union q ⟨hq1, by rw [mem_preimage, hqz]; exact hz₁K⟩
      ⟨hq2, by rw [mem_preimage, hqz]; exact hz₁K⟩ c2
  have c123 : IsPreconnected
      ((F₁ ∩ Prod.fst ⁻¹' K) ∪ (F₂ ∩ Prod.fst ⁻¹' K) ∪ (F₃ ∩ Prod.fst ⁻¹' K)) :=
    c12.union q' (Or.inr ⟨hq'2, by rw [mem_preimage, hq'z]; exact hz₃K⟩)
      ⟨hq'3, by rw [mem_preimage, hq'z]; exact hz₃K⟩ c3
  have heq : F ∩ Prod.fst ⁻¹' K =
      (F₁ ∩ Prod.fst ⁻¹' K) ∪ (F₂ ∩ Prod.fst ⁻¹' K) ∪ (F₃ ∩ Prod.fst ⁻¹' K) := by
    rw [hFeq, union_inter_distrib_right, union_inter_distrib_right]
  rw [heq] at hne ⊢
  obtain ⟨x, hxC, hx⟩ := hne
  rw [connectedComponentIn_eq hxC]
  exact c123.subset_connectedComponentIn hx (by rw [← heq, hFeq]; exact inter_subset_left)

/-- At a glue point `q ∈ F₁ ∩ F₂` of a component `C` whose projection meets `∂G₃`, `φ(C)` is a
neighbourhood of `φ(q)` in `G` (commission §7, step 3, preferred route). -/
theorem image_comp_mem_nhds_glue {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ)
    (hC3 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₃).Nonempty) {q : E × ℝ}
    (hqC : q ∈ connectedComponentIn F p) (hq1 : q ∈ F₁) (hq2 : q ∈ F₂) :
    Prod.fst '' connectedComponentIn F p ∈ 𝓝[G] q.1 := by
  have hFPL : IsPLGraph F := hFeq ▸ hF.isPLGraph_union
  obtain ⟨-, hdisj, -, -, -, -, -, -, -, -, -, -, -, h7₃⟩ := ho16_lemma6 hF
  have hF' := hF
  obtain ⟨⟨-, -, -, -, -, -, -, hG₂, -⟩, -, -, -, -, -, -, he₂, -, he₃, h12, h23, -⟩ := hF'
  set y := q.1 with hydef
  have hy1 : y ∈ relFrontier G G₁ := h12 ▸ mem_image_of_mem _ ⟨hq1, hq2⟩
  have hyG₂ : y ∈ G₂ := he₂ ▸ mem_image_of_mem _ hq2
  set K := connectedComponentIn G₂ y with hKdef
  have hyK : y ∈ K := mem_connectedComponentIn hyG₂
  have hK3 : (K ∩ relFrontier G G₃).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h
    have := disjoint_lift_of_disjoint_right hF hFeq p hC3 y h
    exact this.ne_of_mem hqC ⟨Or.inl hq1, hyK⟩ rfl
  have hsub := lift_subset_of_meets_both hF hFeq p y ⟨y, hyK, hy1⟩ hK3
    ⟨q, hqC, hFeq ▸ Or.inl (Or.inl hq1), hyK⟩
  have hyG₃ : y ∈ Prod.fst '' F₃ := he₃.symm ▸ (hG₂ ▸ hyG₂ : y ∈ G₁ ∩ G₃).2
  obtain ⟨r, hr3, hry⟩ := hyG₃
  have hrC : r ∈ connectedComponentIn F p :=
    hsub ⟨hFeq ▸ Or.inr hr3, by rw [mem_preimage, hry]; exact hyK⟩
  have hr2 : r ∉ F₂ := by
    intro hr2
    have : y ∈ relFrontier G G₃ := hry ▸ h23 ▸ mem_image_of_mem _ ⟨hr2, hr3⟩
    exact hdisj.ne_of_mem hy1 this rfl
  obtain ⟨u, hu, hru, huC⟩ := mem_nhdsWithin.1 (hFPL.comp_mem_nhdsWithin hrC)
  have h7 := h7₃ r ⟨hr3, hr2⟩ u (hu.mem_nhds hru)
  rw [hry] at h7
  refine Filter.mem_of_superset h7 ?_
  rintro _ ⟨w, ⟨hwu, hw3⟩, rfl⟩
  exact ⟨w, huC ⟨hwu, hFeq ▸ Or.inr hw3⟩, rfl⟩

/-- **Proposition 7, `φ(C) = G`** for a component `C` whose projection meets `∂G₁` and `∂G₃`. -/
theorem image_comp_eq {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hG : IsConnected G) {p : E × ℝ}
    (hp : p ∈ F₁ ∪ F₂ ∪ F₃)
    (hC1 : (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₁).Nonempty)
    (hC3 : (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₃).Nonempty) :
    Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p = G := by
  set F := F₁ ∪ F₂ ∪ F₃ with hFdef
  set C := connectedComponentIn F p with hCdef
  have hFPL : IsPLGraph F := hF.isPLGraph_union
  have hCc : IsCompact C := (hFPL.connectedComponentIn p).isCompact
  have hCG : Prod.fst '' C ⊆ G := hF.image_union ▸ image_mono (connectedComponentIn_subset F p)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h7₁, h7₂, h7₃⟩ := ho16_lemma6 hF
  have hsymm : F = F₃ ∪ F₂ ∪ F₁ := (fold_union_symm F₁ F₂ F₃).symm
  have hopen : ∀ y ∈ Prod.fst '' C, Prod.fst '' C ∈ 𝓝[G] y := by
    rintro _ ⟨q, hqC, rfl⟩
    have hqF : q ∈ F := connectedComponentIn_subset F p hqC
    obtain ⟨u, hu, hqu, huC⟩ := mem_nhdsWithin.1 (hFPL.comp_mem_nhdsWithin hqC)
    have hsup : ∀ {Fi : Set (E × ℝ)}, Fi ⊆ F → Prod.fst '' (u ∩ Fi) ⊆ Prod.fst '' C := by
      intro Fi hFi
      rintro _ ⟨w, ⟨hwu, hwi⟩, rfl⟩
      exact ⟨w, huC ⟨hwu, hFi hwi⟩, rfl⟩
    have s1 : F₁ ⊆ F := fun x hx => Or.inl (Or.inl hx)
    have s2 : F₂ ⊆ F := fun x hx => Or.inl (Or.inr hx)
    have s3 : F₃ ⊆ F := fun x hx => Or.inr hx
    have glue23 : q ∈ F₂ → q ∈ F₃ → Prod.fst '' C ∈ 𝓝[G] q.1 := fun h2 h3 =>
      image_comp_mem_nhds_glue hF.symm hsymm p hC1 hqC h3 h2
    rcases hqF with (hq1 | hq2) | hq3
    · by_cases hq2 : q ∈ F₂
      · exact image_comp_mem_nhds_glue hF rfl p hC3 hqC hq1 hq2
      · exact Filter.mem_of_superset (h7₁ q ⟨hq1, hq2⟩ u (hu.mem_nhds hqu)) (hsup s1)
    · by_cases hq1 : q ∈ F₁
      · exact image_comp_mem_nhds_glue hF rfl p hC3 hqC hq1 hq2
      · by_cases hq3 : q ∈ F₃
        · exact glue23 hq2 hq3
        · exact Filter.mem_of_superset
            (h7₂ q ⟨hq2, fun h => h.elim hq1 hq3⟩ u (hu.mem_nhds hqu)) (hsup s2)
    · by_cases hq2 : q ∈ F₂
      · exact glue23 hq2 hq3
      · exact Filter.mem_of_superset (h7₃ q ⟨hq3, hq2⟩ u (hu.mem_nhds hqu)) (hsup s3)
  obtain ⟨O, hO, hOC⟩ := exists_open_inter_eq hCG hopen
  refine Subset.antisymm hCG ?_
  refine subset_of_relClopen hO (hCc.image continuous_fst).isClosed
    (by rw [inter_comm]; exact hOC) hG.isPreconnected subset_rfl ?_
  exact ⟨p.1, hF.image_union ▸ mem_image_of_mem _ hp,
    mem_image_of_mem _ (mem_connectedComponentIn hp)⟩

/-- The union of the components of `G₂` missing `B`. -/
def compsMiss (G₂ B : Set E) : Set E :=
  ⋃ K ∈ {K | (∃ y ∈ G₂, K = connectedComponentIn G₂ y) ∧ Disjoint K B}, K

theorem isClosed_compsMiss {G₂ : Set E} (hG₂ : IsPLGraph G₂) (B : Set E) :
    IsClosed (compsMiss G₂ B) :=
  Set.Finite.isClosed_biUnion (hG₂.finite_components.subset fun _ hK => hK.1) fun _ hK => by
    obtain ⟨⟨y, -, rfl⟩, -⟩ := hK
    exact (hG₂.connectedComponentIn y).isCompact.isClosed

omit [NormedSpace ℝ E] in
theorem mem_compsMiss {G₂ B : Set E} {z : E} (hz : z ∈ G₂)
    (h : Disjoint (connectedComponentIn G₂ z) B) : z ∈ compsMiss G₂ B :=
  mem_biUnion (x := connectedComponentIn G₂ z) ⟨⟨z, hz, rfl⟩, h⟩ (mem_connectedComponentIn hz)

omit [NormedSpace ℝ E] in
theorem of_mem_compsMiss {G₂ B : Set E} {z : E} (hz : z ∈ compsMiss G₂ B) :
    z ∈ G₂ ∧ Disjoint (connectedComponentIn G₂ z) B := by
  obtain ⟨K, ⟨⟨y, -, rfl⟩, hK⟩, hzK⟩ := mem_iUnion₂.1 hz
  exact ⟨connectedComponentIn_subset _ _ hzK, connectedComponentIn_eq hzK ▸ hK⟩

/-- The closed sets `Z₁ = cl (G₁ \ G₂) ∪ (components of G₂ missing ∂G₁)` and
`Z₃ = cl (G₃ \ G₂) ∪ (components of G₂ missing ∂G₃)` are disjoint. -/
theorem Z_disjoint {G G₁ G₂ G₃ : Set E} (hT : IsFoldTriple G G₁ G₂ G₃) (hG : IsConnected G)
    (h₃ : (relFrontier G G₃).Nonempty) :
    Disjoint (closure (G₁ \ G₂) ∪ compsMiss G₂ (relFrontier G G₁))
      (closure (G₃ \ G₂) ∪ compsMiss G₂ (relFrontier G G₃)) := by
  have hT' := hT
  obtain ⟨-, -, -, hG₁, -, hG₃, hcov, hG₂, hF3⟩ := hT'
  have hG₁c := hG₁.isCompact.isClosed
  have hG₃c := hG₃.isCompact.isClosed
  rw [Set.disjoint_left]
  rintro z (hz1 | hz1) (hz3 | hz3)
  · exact hF3.ne_of_mem hz1 hz3 rfl
  · obtain ⟨hzG₂, hK⟩ := of_mem_compsMiss hz3
    have : z ∈ relFrontier G G₃ := by
      rw [relFrontier_right_eq hG₁c hG₃c hcov hG₂]; exact ⟨hz1, hzG₂⟩
    exact hK.ne_of_mem (mem_connectedComponentIn hzG₂) this rfl
  · obtain ⟨hzG₂, hK⟩ := of_mem_compsMiss hz1
    have : z ∈ relFrontier G G₁ := by
      rw [relFrontier_left_eq hG₁c hG₃c hcov hG₂]; exact ⟨hz3, hzG₂⟩
    exact hK.ne_of_mem (mem_connectedComponentIn hzG₂) this rfl
  · obtain ⟨hzG₂, hK1⟩ := of_mem_compsMiss hz1
    obtain ⟨-, hK3⟩ := of_mem_compsMiss hz3
    exact comp_not_disjoint_both hT hG h₃ hzG₂ ⟨hK1, hK3⟩

/-- **Proposition 7, existence**: some component of `F` has projection meeting `∂G₁` and `∂G₃`.
(H–O: "By (F2) and (F3), and since G is connected" — supplied here.) -/
theorem exists_comp_meets_both {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hG : IsConnected G)
    (h₁ : (relFrontier G G₁).Nonempty) (h₃ : (relFrontier G G₃).Nonempty) :
    ∃ p ∈ F₁ ∪ F₂ ∪ F₃,
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₁).Nonempty ∧
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₃).Nonempty := by
  have hF' := hF
  obtain ⟨hT, -, hP₂, -, -, -, hi₂, he₂, -, -, -, -, -⟩ := hF'
  have hT' := hT
  obtain ⟨-, -, -, hG₁, hG₂P, hG₃, hcov, hG₂, -⟩ := hT'
  have hG₁c := hG₁.isCompact.isClosed
  have hG₃c := hG₃.isCompact.isClosed
  by_contra hno
  -- every component of `G₂` misses `∂G₁` or `∂G₃`
  have hKone : ∀ z ∈ G₂, Disjoint (connectedComponentIn G₂ z) (relFrontier G G₁) ∨
      Disjoint (connectedComponentIn G₂ z) (relFrontier G G₃) := by
    intro z hz
    by_contra hboth
    rw [not_or, not_disjoint_iff_nonempty_inter, not_disjoint_iff_nonempty_inter] at hboth
    obtain ⟨⟨y₁, hy₁K, hy₁⟩, ⟨y₃, hy₃K, hy₃⟩⟩ := hboth
    obtain ⟨q, ⟨hq1, hq2⟩, hqy⟩ := hF.exists_glue hy₁
    set K := connectedComponentIn G₂ z
    have hKG₂ : K ⊆ G₂ := connectedComponentIn_subset _ _
    have hK2 := isPreconnected_lift hP₂.isCompact hi₂ isPreconnected_connectedComponentIn
      (he₂.symm ▸ hKG₂ : K ⊆ Prod.fst '' F₂)
    have hqK2 : q ∈ F₂ ∩ Prod.fst ⁻¹' K := ⟨hq2, by rw [mem_preimage, hqy]; exact hy₁K⟩
    have hsub := hK2.subset_connectedComponentIn hqK2
      (fun x hx => Or.inl (Or.inr hx.1) : F₂ ∩ Prod.fst ⁻¹' K ⊆ F₁ ∪ F₂ ∪ F₃)
    have himg : K ⊆ Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) q := by
      intro w hw
      obtain ⟨r, hr2, hrw⟩ := (he₂.symm ▸ hKG₂ hw : w ∈ Prod.fst '' F₂)
      exact ⟨r, hsub ⟨hr2, by rw [mem_preimage, hrw]; exact hw⟩, hrw⟩
    exact hno ⟨q, Or.inl (Or.inl hq1), ⟨y₁, himg hy₁K, hy₁⟩, ⟨y₃, himg hy₃K, hy₃⟩⟩
  have hdisj := Z_disjoint hT hG h₃
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₃, hz₃⟩ := h₃
  have hz₁' := hz₁
  have hz₃' := hz₃
  rw [relFrontier_left_eq hG₁c hG₃c hcov hG₂] at hz₁'
  rw [relFrontier_right_eq hG₁c hG₃c hcov hG₂] at hz₃'
  have hG₂G : G₂ ⊆ G := fun z hz => hcov ▸ Or.inl (hG₂ ▸ hz : z ∈ G₁ ∩ G₃).1
  obtain ⟨w, -, hw1, hw3⟩ := isPreconnected_closed_iff.1 hG.isPreconnected _ _
    (isClosed_closure.union (isClosed_compsMiss hG₂P _))
    (isClosed_closure.union (isClosed_compsMiss hG₂P _))
    (fun z hz => by
      by_cases hzG₂ : z ∈ G₂
      · rcases hKone z hzG₂ with h | h
        · exact Or.inl (Or.inr (mem_compsMiss hzG₂ h))
        · exact Or.inr (Or.inr (mem_compsMiss hzG₂ h))
      · rw [← hcov] at hz
        rcases hz with h | h
        · exact Or.inl (Or.inl (subset_closure ⟨h, hzG₂⟩))
        · exact Or.inr (Or.inl (subset_closure ⟨h, hzG₂⟩)))
    ⟨z₃, hG₂G hz₃'.2, Or.inl hz₃'.1⟩ ⟨z₁, hG₂G hz₁'.2, Or.inl hz₁'.1⟩
  exact hdisj.ne_of_mem hw1 hw3 rfl

/-- A point of `C ∩ (F₁ ∪ F₂)` over `G₂` lies over a component of `G₂` meeting `∂G₃`. -/
theorem comp_meets_right {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ)
    (hC3 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₃).Nonempty) {q : E × ℝ}
    (hqC : q ∈ connectedComponentIn F p) (hq : q ∈ F₁ ∪ F₂) (hqG₂ : q.1 ∈ G₂) :
    (connectedComponentIn G₂ q.1 ∩ relFrontier G G₃).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h
  exact (disjoint_lift_of_disjoint_right hF hFeq p hC3 q.1 h).ne_of_mem hqC
    ⟨hq, mem_connectedComponentIn hqG₂⟩ rfl

/-- The symmetric statement: a point of `C ∩ (F₂ ∪ F₃)` over `G₂` lies over a component of `G₂`
meeting `∂G₁`. -/
theorem comp_meets_left {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ)
    (hC1 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₁).Nonempty) {q : E × ℝ}
    (hqC : q ∈ connectedComponentIn F p) (hq : q ∈ F₂ ∪ F₃) (hqG₂ : q.1 ∈ G₂) :
    (connectedComponentIn G₂ q.1 ∩ relFrontier G G₁).Nonempty :=
  comp_meets_right hF.symm (hFeq.trans (fold_union_symm F₁ F₂ F₃).symm) p hC1 hqC
    (hq.symm) hqG₂

/-- **(M1)**: if the `F₂`-point over `y` is in `C`, so are all points of `F` over `y`. -/
theorem mem_comp_of_mid {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ)
    (hC1 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₁).Nonempty)
    (hC3 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₃).Nonempty) {q r : E × ℝ}
    (hqC : q ∈ connectedComponentIn F p) (hq2 : q ∈ F₂) (hr : r ∈ F) (hrq : r.1 = q.1) :
    r ∈ connectedComponentIn F p := by
  have hqG₂ : q.1 ∈ G₂ := hF.2.2.2.2.2.2.2.1 ▸ mem_image_of_mem _ hq2
  have hqF : q ∈ F := hFeq ▸ Or.inl (Or.inr hq2)
  exact lift_subset_of_meets_both hF hFeq p q.1
    (comp_meets_left hF hFeq p hC1 hqC (Or.inl hq2) hqG₂)
    (comp_meets_right hF hFeq p hC3 hqC (Or.inr hq2) hqG₂)
    ⟨q, hqC, hqF, mem_connectedComponentIn hqG₂⟩
    ⟨hr, by rw [mem_preimage, hrq]; exact mem_connectedComponentIn hqG₂⟩

/-- **(M2)**: if the `F₁`- and `F₃`-points over `y` are in `C`, so are all points of `F` over `y`. -/
theorem mem_comp_of_sides {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ)
    (hC1 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₁).Nonempty)
    (hC3 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₃).Nonempty)
    {q₁ q₃ r : E × ℝ} (hq₁C : q₁ ∈ connectedComponentIn F p) (hq₁ : q₁ ∈ F₁)
    (hq₃C : q₃ ∈ connectedComponentIn F p) (hq₃ : q₃ ∈ F₃) (h13 : q₃.1 = q₁.1)
    (hr : r ∈ F) (hrq : r.1 = q₁.1) : r ∈ connectedComponentIn F p := by
  have hG₂ := hF.1.2.2.2.2.2.2.2.1
  have hy1 : q₁.1 ∈ G₁ := hF.2.2.2.2.2.1 ▸ mem_image_of_mem _ hq₁
  have hy3 : q₁.1 ∈ G₃ := h13 ▸ hF.2.2.2.2.2.2.2.2.2.1 ▸ mem_image_of_mem _ hq₃
  have hqG₂ : q₁.1 ∈ G₂ := hG₂ ▸ ⟨hy1, hy3⟩
  have hm1 := comp_meets_left hF hFeq p hC1 hq₃C (Or.inr hq₃) (h13 ▸ hqG₂)
  rw [h13] at hm1
  exact lift_subset_of_meets_both hF hFeq p q₁.1 hm1
    (comp_meets_right hF hFeq p hC3 hq₁C (Or.inl hq₁) hqG₂)
    ⟨q₁, hq₁C, hFeq ▸ Or.inl (Or.inl hq₁), mem_connectedComponentIn hqG₂⟩
    ⟨hr, by rw [mem_preimage, hrq]; exact mem_connectedComponentIn hqG₂⟩

/-- **(M3)**: `G₁' \ G₂' ⊆ cl (G₁ \ G₂) ∪ (components of G₂ missing ∂G₁)`. -/
theorem left_diff_subset_Z {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ)
    (hC3 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₃).Nonempty) :
    Prod.fst '' (F₁ ∩ connectedComponentIn F p) \ Prod.fst '' (F₂ ∩ connectedComponentIn F p) ⊆
      closure (G₁ \ G₂) ∪ compsMiss G₂ (relFrontier G G₁) := by
  rintro y ⟨⟨q, ⟨hq1, hqC⟩, rfl⟩, hy2⟩
  have he₁ := hF.2.2.2.2.2.1
  have he₂ := hF.2.2.2.2.2.2.2.1
  by_cases hqG₂ : q.1 ∈ G₂
  · right
    refine mem_compsMiss hqG₂ ?_
    by_contra h
    rw [not_disjoint_iff_nonempty_inter] at h
    obtain ⟨r, hr2, hrq⟩ := (he₂.symm ▸ hqG₂ : q.1 ∈ Prod.fst '' F₂)
    have hrC := lift_subset_of_meets_both hF hFeq p q.1 h
      (comp_meets_right hF hFeq p hC3 hqC (Or.inl hq1) hqG₂)
      ⟨q, hqC, hFeq ▸ Or.inl (Or.inl hq1), mem_connectedComponentIn hqG₂⟩
      ⟨by rw [hFeq]; exact Or.inl (Or.inr hr2), by rw [mem_preimage, hrq]; exact mem_connectedComponentIn hqG₂⟩
    exact hy2 ⟨r, ⟨hr2, hrC⟩, hrq⟩
  · left
    exact subset_closure ⟨he₁ ▸ mem_image_of_mem _ hq1, hqG₂⟩

/-- **The frontier clause** of `F′`: `φ(F′₁ ∩ F′₂) = ∂G′₁`. -/
theorem frontier_clause {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ F : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hFeq : F = F₁ ∪ F₂ ∪ F₃) (p : E × ℝ)
    (hC1 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₁).Nonempty)
    (hC3 : (Prod.fst '' connectedComponentIn F p ∩ relFrontier G G₃).Nonempty)
    (hcov' : Prod.fst '' (F₁ ∩ connectedComponentIn F p) ∪
      Prod.fst '' (F₃ ∩ connectedComponentIn F p) = G)
    (hG₂' : Prod.fst '' (F₂ ∩ connectedComponentIn F p) =
      Prod.fst '' (F₁ ∩ connectedComponentIn F p) ∩ Prod.fst '' (F₃ ∩ connectedComponentIn F p)) :
    Prod.fst '' ((F₁ ∩ connectedComponentIn F p) ∩ (F₂ ∩ connectedComponentIn F p)) =
      relFrontier G (Prod.fst '' (F₁ ∩ connectedComponentIn F p)) := by
  set C := connectedComponentIn F p with hCdef
  have hFPL : IsPLGraph F := hFeq ▸ hF.isPLGraph_union
  have hCc : IsClosed C := (hFPL.connectedComponentIn p).isCompact.isClosed
  have hF' := hF
  obtain ⟨⟨-, -, -, hG₁, hG₂P, hG₃, hcov, hG₂, -⟩, hP₁, hP₂, hP₃, hi₁, he₁, hi₂, he₂, hi₃, he₃,
    h12, -, -⟩ := hF'
  have hG₁c := hG₁.isCompact.isClosed
  have hG₃c := hG₃.isCompact.isClosed
  have hc : ∀ {Fi : Set (E × ℝ)}, IsPLGraph Fi → IsClosed (Prod.fst '' (Fi ∩ C)) := fun hPi =>
    ((hPi.isCompact.inter_right hCc).image continuous_fst).isClosed
  rw [relFrontier_left_eq (hc hP₁) (hc hP₃) hcov' hG₂']
  have hsymm : F = F₃ ∪ F₂ ∪ F₁ := hFeq.trans (fold_union_symm F₁ F₂ F₃).symm
  apply Subset.antisymm
  · rintro _ ⟨q, ⟨⟨hq1, hqC⟩, ⟨hq2, -⟩⟩, rfl⟩
    refine ⟨?_, ⟨q, ⟨hq2, hqC⟩, rfl⟩⟩
    have hy1 : q.1 ∈ relFrontier G G₁ := h12 ▸ mem_image_of_mem _ ⟨hq1, hq2⟩
    rw [relFrontier_left_eq hG₁c hG₃c hcov hG₂] at hy1
    have hqG₂ : q.1 ∈ G₂ := hy1.2
    obtain ⟨r, hr3, hrq⟩ := (he₃.symm ▸ (hG₂ ▸ hqG₂ : q.1 ∈ G₁ ∩ G₃).2 : q.1 ∈ Prod.fst '' F₃)
    have hrC : r ∈ C := mem_comp_of_mid hF hFeq p hC1 hC3 hqC hq2 (hFeq ▸ Or.inr hr3) hrq
    obtain ⟨u, hu, hru, huC⟩ := mem_nhdsWithin.1 (hFPL.comp_mem_nhdsWithin hrC)
    have hN := image_fst_mem_nhdsWithin hP₃.isCompact hi₃ hr3 (hu.mem_nhds hru)
    rw [he₃, hrq] at hN
    obtain ⟨v, hv, hqv, hvsub⟩ := mem_nhdsWithin.1 hN
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨z, ⟨hzt, hzv⟩, hz3, hz2⟩ :=
      mem_closure_iff_nhds.1 hy1.1 (t ∩ v) (Filter.inter_mem ht (hv.mem_nhds hqv))
    obtain ⟨w, ⟨hwu, hw3⟩, rfl⟩ := hvsub ⟨hzv, hz3⟩
    refine ⟨w.1, hzt, ⟨w, ⟨hw3, huC ⟨hwu, hFeq ▸ Or.inr hw3⟩⟩, rfl⟩, ?_⟩
    rintro ⟨w', ⟨hw'2, -⟩, hw'⟩
    exact hz2 (hw' ▸ he₂ ▸ mem_image_of_mem _ hw'2)
  · rintro y ⟨hycl, ⟨q, ⟨hq2, hqC⟩, rfl⟩⟩
    have hZ : closure (Prod.fst '' (F₃ ∩ C) \ Prod.fst '' (F₂ ∩ C)) ⊆
        closure (G₃ \ G₂) ∪ compsMiss G₂ (relFrontier G G₃) :=
      closure_minimal (left_diff_subset_Z hF.symm hsymm p hC1)
        (isClosed_closure.union (isClosed_compsMiss hG₂P _))
    have hqG₂ : q.1 ∈ G₂ := he₂ ▸ mem_image_of_mem _ hq2
    rcases hZ hycl with h | h
    · have hy1 : q.1 ∈ relFrontier G G₁ := by
        rw [relFrontier_left_eq hG₁c hG₃c hcov hG₂]; exact ⟨h, hqG₂⟩
      obtain ⟨q', ⟨hq'1, hq'2⟩, hq'⟩ := hF.exists_glue hy1
      have : q' = q := hi₂ hq'2 hq2 hq'
      subst this
      exact ⟨q', ⟨⟨hq'1, hqC⟩, ⟨hq2, hqC⟩⟩, rfl⟩
    · exfalso
      obtain ⟨-, hK⟩ := of_mem_compsMiss h
      obtain ⟨z, hzK, hz⟩ := comp_meets_right hF hFeq p hC3 hqC (Or.inr hq2) hqG₂
      exact hK.ne_of_mem hzK hz rfl

/-- **H–O Proposition 7** (pp. 186–187): for connected `G` with `∂G₁ ≠ ∅ ≠ ∂G₃`, some component
`C` of `F` has `φ(C)` meeting `∂G₁` and `∂G₃`; for every such component, `φ(C) = G` and the
pieces `Fᵢ ∩ C` form a simple fold on `G`. -/
theorem ho16_prop7 {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃)
    (hG : IsConnected G) (h₁ : (relFrontier G G₁).Nonempty) (h₃ : (relFrontier G G₃).Nonempty) :
    (∃ p ∈ F₁ ∪ F₂ ∪ F₃,
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₁).Nonempty ∧
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₃).Nonempty) ∧
    ∀ p ∈ F₁ ∪ F₂ ∪ F₃,
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₁).Nonempty →
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₃).Nonempty →
      Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p = G ∧
      IsSimpleFoldOf G (Prod.fst '' (F₁ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p))
        (Prod.fst '' (F₂ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p))
        (Prod.fst '' (F₃ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p))
        (F₁ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p)
        (F₂ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p)
        (F₃ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p) := by
  refine ⟨exists_comp_meets_both hF hG h₁ h₃, fun p hp hC1 hC3 => ?_⟩
  have hCG := image_comp_eq hF hG hp hC1 hC3
  refine ⟨hCG, ?_⟩
  set F := F₁ ∪ F₂ ∪ F₃ with hFdef
  set C := connectedComponentIn F p with hCdef
  have hFPL : IsPLGraph F := hF.isPLGraph_union
  have hCc : IsClosed C := (hFPL.connectedComponentIn p).isCompact.isClosed
  have hF' := hF
  obtain ⟨hT, hP₁, hP₂, hP₃, hi₁, he₁, hi₂, he₂, hi₃, he₃, h12, h23, h13⟩ := hF'
  have hT' := hT
  obtain ⟨-, -, -, hG₁, hG₂P, hG₃, hcov, hG₂, -⟩ := hT'
  have hsymm : F = F₃ ∪ F₂ ∪ F₁ := (fold_union_symm F₁ F₂ F₃).symm
  have s1 : F₁ ⊆ F := fun x hx => Or.inl (Or.inl hx)
  have s2 : F₂ ⊆ F := fun x hx => Or.inl (Or.inr hx)
  have s3 : F₃ ⊆ F := fun x hx => Or.inr hx
  set G₁' := Prod.fst '' (F₁ ∩ C) with hG₁'
  set G₂' := Prod.fst '' (F₂ ∩ C) with hG₂'
  set G₃' := Prod.fst '' (F₃ ∩ C) with hG₃'
  -- (M1), (M2)
  have hM1 : ∀ y ∈ G₂', y ∈ G₁' ∧ y ∈ G₃' := by
    rintro _ ⟨q, ⟨hq2, hqC⟩, rfl⟩
    have hqG₂ : q.1 ∈ G₂ := he₂ ▸ mem_image_of_mem _ hq2
    have hq13 : q.1 ∈ G₁ ∩ G₃ := hG₂ ▸ hqG₂
    obtain ⟨r₁, hr₁, hr₁q⟩ := (he₁.symm ▸ hq13.1 : q.1 ∈ Prod.fst '' F₁)
    obtain ⟨r₃, hr₃, hr₃q⟩ := (he₃.symm ▸ hq13.2 : q.1 ∈ Prod.fst '' F₃)
    exact ⟨⟨r₁, ⟨hr₁, mem_comp_of_mid hF rfl p hC1 hC3 hqC hq2 (s1 hr₁) hr₁q⟩, hr₁q⟩,
      ⟨r₃, ⟨hr₃, mem_comp_of_mid hF rfl p hC1 hC3 hqC hq2 (s3 hr₃) hr₃q⟩, hr₃q⟩⟩
  have hG₂'eq : G₂' = G₁' ∩ G₃' := by
    apply Subset.antisymm
    · intro y hy; exact hM1 y hy
    · rintro _ ⟨⟨q₁, ⟨hq₁, hq₁C⟩, rfl⟩, ⟨q₃, ⟨hq₃, hq₃C⟩, h13'⟩⟩
      have hq13 : q₁.1 ∈ G₁ ∩ G₃ :=
        ⟨he₁ ▸ mem_image_of_mem _ hq₁, h13' ▸ he₃ ▸ mem_image_of_mem _ hq₃⟩
      obtain ⟨r, hr2, hrq⟩ := (he₂.symm ▸ (hG₂ ▸ hq13 : q₁.1 ∈ G₂) : q₁.1 ∈ Prod.fst '' F₂)
      exact ⟨r, ⟨hr2, mem_comp_of_sides hF rfl p hC1 hC3 hq₁C hq₁ hq₃C hq₃ h13' (s2 hr2) hrq⟩,
        hrq⟩
  have hcov' : G₁' ∪ G₃' = G := by
    apply Subset.antisymm
    · rintro _ (⟨q, ⟨hq, -⟩, rfl⟩ | ⟨q, ⟨hq, -⟩, rfl⟩)
      · exact hF.image_union ▸ mem_image_of_mem _ (s1 hq)
      · exact hF.image_union ▸ mem_image_of_mem _ (s3 hq)
    · intro y hy
      rw [← hCG] at hy
      obtain ⟨q, hqC, rfl⟩ := hy
      rcases connectedComponentIn_subset F p hqC with (hq1 | hq2) | hq3
      · exact Or.inl ⟨q, ⟨hq1, hqC⟩, rfl⟩
      · exact Or.inl (hM1 _ ⟨q, ⟨hq2, hqC⟩, rfl⟩).1
      · exact Or.inr ⟨q, ⟨hq3, hqC⟩, rfl⟩
  -- `C` meets `F₂`
  have hne₂ : G₂'.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, image_eq_empty] at hemp
    have hC2 : ∀ x ∈ C, x ∉ F₂ := fun x hx h2 => hemp.subset ⟨h2, hx⟩
    obtain ⟨_, ⟨q, hqC, rfl⟩, hq⟩ := hC1
    obtain ⟨_, ⟨q', hq'C, rfl⟩, hq'⟩ := hC3
    obtain ⟨g, ⟨hg1, hg2⟩, hgq⟩ := hF.exists_glue hq
    have hq'' : q'.1 ∈ Prod.fst '' (F₂ ∩ F₃) := h23.symm ▸ hq'
    obtain ⟨g', ⟨hg'2, hg'3⟩, hg'q⟩ := hq''
    have hq3 : q ∈ F₃ := by
      rcases connectedComponentIn_subset F p hqC with (h1 | h2) | h3
      · exact absurd (hi₁ hg1 h1 hgq ▸ hg2) (hC2 q hqC)
      · exact absurd h2 (hC2 q hqC)
      · exact h3
    have hq'1 : q' ∈ F₁ := by
      rcases connectedComponentIn_subset F p hq'C with (h1 | h2) | h3
      · exact h1
      · exact absurd h2 (hC2 q' hq'C)
      · exact absurd (hi₃ hg'3 h3 hg'q ▸ hg'2) (hC2 q' hq'C)
    obtain ⟨x, -, hx1, hx3⟩ := isPreconnected_closed_iff.1
      (isPreconnected_connectedComponentIn (F := F) (x := p)) F₁ F₃
      hP₁.isCompact.isClosed hP₃.isCompact.isClosed
      (fun x hx => by
        rcases connectedComponentIn_subset F p hx with (h1 | h2) | h3
        · exact Or.inl h1
        · exact absurd h2 (hC2 x hx)
        · exact Or.inr h3)
      ⟨q', hq'C, hq'1⟩ ⟨q, hqC, hq3⟩
    exact h13.ne_of_mem hx1 hx3 rfl
  have hPL : ∀ {Fi : Set (E × ℝ)}, IsPLGraph Fi → Fi ⊆ F → InjOn Prod.fst Fi →
      IsPLGraph (Fi ∩ C) ∧ IsPLGraph (Prod.fst '' (Fi ∩ C)) := by
    intro Fi hPi hFi hii
    have h := hFPL.inter_connectedComponentIn hPi hFi p
    exact ⟨h, h.image_fst (hii.mono inter_subset_left)⟩
  obtain ⟨hPL₁, hPL₁'⟩ := hPL hP₁ s1 hi₁
  obtain ⟨hPL₂, hPL₂'⟩ := hPL hP₂ s2 hi₂
  obtain ⟨hPL₃, hPL₃'⟩ := hPL hP₃ s3 hi₃
  have hF3' : Disjoint (closure (G₁' \ G₂')) (closure (G₃' \ G₂')) := by
    refine (Z_disjoint hT hG h₃).mono ?_ ?_
    · exact closure_minimal (left_diff_subset_Z hF rfl p hC3)
        (isClosed_closure.union (isClosed_compsMiss hG₂P _))
    · exact closure_minimal (left_diff_subset_Z hF.symm hsymm p hC1)
        (isClosed_closure.union (isClosed_compsMiss hG₂P _))
  have hFC₁ := frontier_clause hF rfl p hC1 hC3 hcov' hG₂'eq
  have hFC₃ := frontier_clause hF.symm hsymm p hC3 hC1 ((union_comm _ _).trans hcov')
    (hG₂'eq.trans (inter_comm _ _))
  rw [inter_comm] at hFC₃
  exact ⟨⟨hne₂.mono (fun y hy => (hM1 y hy).1), hne₂, hne₂.mono (fun y hy => (hM1 y hy).2),
    hPL₁', hPL₂', hPL₃', hcov', hG₂'eq, hF3'⟩, hPL₁, hPL₂, hPL₃,
    hi₁.mono inter_subset_left, rfl, hi₂.mono inter_subset_left, rfl,
    hi₃.mono inter_subset_left, rfl, hFC₁, hFC₃,
    h13.mono inter_subset_left inter_subset_left⟩

end Fold

end HPC.HO16
