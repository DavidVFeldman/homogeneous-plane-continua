import HPC.HO16.Stairwell

/-!
# Batch 195, §7: H–O Lemma 18

`F = F₁ ∪ F₂ ∪ F₃` a simple fold on `G` (`φ = Prod.fst`), `S ⊆ G⋆` straight, `A = π(S)`.
`π(φ⋆⁻¹(S)) = F ∩ φ⁻¹(A)` (`image_foldPre`). The proof is pointwise:

* `lift_mem_closure`: off `∂F₂`, `φ` is open on the sheet through the point (Lemma 6 (7)), so
  closure points of subsets of `G` lift;
* `lemma18_claim` (H–O's claim, p. 202): over `∂F₁ = F₁ ∩ F₂` (and, by symmetry, over
  `∂F₃ = F₂ ∩ F₃`) a whole neighbourhood in `F` maps into `A`; this is where the hypothesis on
  `∂π(S) ∩ ∂φ(F₂)` is used;
* non-isolation of the points of `F ∩ φ⁻¹(A)` and of `(F₁ ∪ F₂) ∩ φ⁻¹(A)` (regularity, with
  `IsPLGraph.inter_preimage_fst` and `isPLGraph_union_finite`);
* the frontier characterizations `lemma18_fr` and `lemma18_fr₂` (the end-set formulas).
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Lemma18

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem continuous_phiStar : Continuous (phiStar : (E × ℝ) × ℝ → E × ℝ) := by
  unfold phiStar
  fun_prop

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `π(φ⋆⁻¹(S) ∩ T⋆) = F ∩ T ∩ φ⁻¹(π(S))`. -/
theorem image_foldPre_inter {G : Set E} {F S : Set (E × ℝ)} (hSG : S ⊆ G ×ˢ Icc (0 : ℝ) 1)
    (T : Set (E × ℝ)) :
    Prod.fst '' (foldPre F S ∩ T ×ˢ Icc (0 : ℝ) 1) = (F ∩ T) ∩ Prod.fst ⁻¹' (Prod.fst '' S) := by
  ext x
  constructor
  · rintro ⟨q, ⟨⟨⟨hqF, -⟩, hqS⟩, hqT, -⟩, rfl⟩
    exact ⟨⟨hqF, hqT⟩, phiStar q, hqS, rfl⟩
  · rintro ⟨⟨hxF, hxT⟩, s, hsS, hsx⟩
    refine ⟨(x, s.2), ⟨⟨⟨hxF, (hSG hsS).2⟩, ?_⟩, hxT, (hSG hsS).2⟩, rfl⟩
    show (x.1, s.2) ∈ S
    rw [← hsx]
    exact hsS

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem image_foldPre {G : Set E} {F S : Set (E × ℝ)} (hSG : S ⊆ G ×ˢ Icc (0 : ℝ) 1) :
    Prod.fst '' foldPre F S = F ∩ Prod.fst ⁻¹' (Prod.fst '' S) := by
  ext x
  constructor
  · rintro ⟨q, ⟨⟨hqF, -⟩, hqS⟩, rfl⟩
    exact ⟨hqF, phiStar q, hqS, rfl⟩
  · rintro ⟨hxF, s, hsS, hsx⟩
    refine ⟨(x, s.2), ⟨⟨hxF, (hSG hsS).2⟩, ?_⟩, rfl⟩
    show (x.1, s.2) ∈ S
    rw [← hsx]
    exact hsS

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem injOn_foldPre {F S : Set (E × ℝ)} (hinj : InjOn Prod.fst S) (T : Set ((E × ℝ) × ℝ))
    (hT : T ⊆ foldPre F S) : InjOn Prod.fst T := by
  intro q hq q' hq' hqq
  have h := hinj (hT hq).2 (hT hq').2 (show (phiStar q).1 = (phiStar q').1 by
    simp [phiStar, hqq])
  exact Prod.ext hqq (by simpa [phiStar] using congrArg Prod.snd h)

omit [NormedSpace ℝ E] in
/-- Lifting closure points along a sheet on which `φ` is open. -/
theorem lift_mem_closure {G : Set E} {Fi : Set (E × ℝ)} {x : E × ℝ}
    (hloc : ∀ N ∈ 𝓝 x, Prod.fst '' (N ∩ Fi) ∈ 𝓝[G] x.1) {Y : Set E} (hYG : Y ⊆ G)
    (hY : x.1 ∈ closure Y) : x ∈ closure (Fi ∩ Prod.fst ⁻¹' Y) := by
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨_, ⟨z, ⟨hzN, hzF⟩, rfl⟩, hzY⟩ := inter_nonempty_of_mem_nhdsWithin (hloc N hN) hY hYG
  exact ⟨z, hzN, hzF, hzY⟩

/-- **H–O's claim in the proof of Lemma 18** (p. 202), over `∂F₁ = F₁ ∩ F₂`: a neighbourhood of
`x` in `F` lies in `F₁ ∪ F₂` and maps into `A`. -/
theorem lemma18_claim {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) {A : Set E}
    (hV : Disjoint (relFrontier G A) (relFrontier G G₂) ∨
      ∃ V ∈ 𝓝ˢ (relFrontier G A ∩ relFrontier G G₂), G₂ ∩ V ⊆ A ∩ V)
    {x : E × ℝ} (hx : x ∈ F₁ ∩ F₂) (hxA : x.1 ∈ A) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ (F₁ ∪ F₂ ∪ F₃) ⊆ (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A := by
  obtain ⟨⟨-, -, -, -, -, -, hcov, hG₂eq, hF3⟩, -, -, hF₃, -, hφ₁, -, hφ₂, -, -, h12, -, h13⟩ := hF
  have hG₂G : G₂ ⊆ G := fun z hz => by
    rw [hG₂eq] at hz; rw [← hcov]; exact Or.inl hz.1
  have hy1 : x.1 ∈ relFrontier G G₁ := by rw [← h12]; exact ⟨x, hx, rfl⟩
  have hyG₂ : x.1 ∈ G₂ := by rw [← hφ₂]; exact ⟨x, hx.2, rfl⟩
  have hyc : x.1 ∈ closure (G \ G₂) := closure_mono
    (diff_subset_diff_right (fun z hz => by rw [hG₂eq] at hz; exact hz.1)) hy1.2
  obtain ⟨V₀, hV₀, hyV₀, hV₀A⟩ : ∃ V₀, IsOpen V₀ ∧ x.1 ∈ V₀ ∧ G₂ ∩ V₀ ⊆ A := by
    by_cases hint : x.1 ∈ closure (G \ A)
    · have hyA : x.1 ∈ relFrontier G A := ⟨subset_closure hxA, hint⟩
      have hyG₂' : x.1 ∈ relFrontier G G₂ := ⟨subset_closure hyG₂, hyc⟩
      rcases hV with hd | ⟨V, hV, hVsub⟩
      · exact absurd hyG₂' (Set.disjoint_left.1 hd hyA)
      · have hVy : V ∈ 𝓝 x.1 := mem_nhdsSet_iff_forall.1 hV _ ⟨hyA, hyG₂'⟩
        exact ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hVy,
          fun z hz => (hVsub ⟨hz.1, interior_subset hz.2⟩).1⟩
    · refine ⟨(closure (G \ A))ᶜ, isClosed_closure.isOpen_compl, hint, ?_⟩
      rintro z ⟨hz2, hzc⟩
      by_contra hzA
      exact hzc (subset_closure ⟨hG₂G hz2, hzA⟩)
  have hy13 : x.1 ∉ closure (G₁ \ G₂) := by
    have : x.1 ∈ closure (G₃ \ G₂) := by rw [← fold_diff_left hcov hG₂eq]; exact hy1.2
    exact fun h => Set.disjoint_left.1 hF3 h this
  refine ⟨Prod.fst ⁻¹' (V₀ ∩ (closure (G₁ \ G₂))ᶜ) ∩ F₃ᶜ,
    ((hV₀.inter isClosed_closure.isOpen_compl).preimage continuous_fst).inter
      hF₃.isCompact.isClosed.isOpen_compl,
    ⟨⟨hyV₀, hy13⟩, fun h => Set.disjoint_left.1 h13 hx.1 h⟩, ?_⟩
  rintro z ⟨⟨⟨hzV, hzc⟩, hz3⟩, hzF⟩
  have hz12 : z ∈ F₁ ∪ F₂ := by
    rcases hzF with h | h
    · exact h
    · exact absurd h hz3
  refine ⟨hz12, hV₀A ⟨?_, hzV⟩⟩
  have hzG₁ : z.1 ∈ G₁ := by
    rcases hz12 with h | h
    · rw [← hφ₁]; exact ⟨z, h, rfl⟩
    · have : z.1 ∈ G₂ := by rw [← hφ₂]; exact ⟨z, h, rfl⟩
      rw [hG₂eq] at this
      exact this.1
  by_contra hz2
  exact hzc (subset_closure ⟨hzG₁, hz2⟩)

/-- The claim over `∂F₃ = F₂ ∩ F₃` (the fold read backwards). -/
theorem lemma18_claim' {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) {A : Set E}
    (hV : Disjoint (relFrontier G A) (relFrontier G G₂) ∨
      ∃ V ∈ 𝓝ˢ (relFrontier G A ∩ relFrontier G G₂), G₂ ∩ V ⊆ A ∩ V)
    {x : E × ℝ} (hx : x ∈ F₂ ∩ F₃) (hxA : x.1 ∈ A) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ (F₁ ∪ F₂ ∪ F₃) ⊆ (F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A := by
  obtain ⟨U, hU, hxU, hUsub⟩ := lemma18_claim hF.symm hV ⟨hx.2, hx.1⟩ hxA
  refine ⟨U, hU, hxU, ?_⟩
  rw [← fold_union_symm]
  intro z hz
  obtain ⟨h1, h2⟩ := hUsub hz
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The pointwise facts of Lemma 18, for a simple fold and a closed PL graph `A ⊆ G`. -/
theorem lemma18_points {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) {A : Set E} (hA : IsPLGraph A) (hAG : A ⊆ G)
    (hV : Disjoint (relFrontier G A) (relFrontier G G₂) ∨
      ∃ V ∈ 𝓝ˢ (relFrontier G A ∩ relFrontier G G₂), G₂ ∩ V ⊆ A ∩ V) :
    -- non-isolation in `(F₁ ∪ F₂) ∩ φ⁻¹(A)` and in `F ∩ φ⁻¹(A)`
    (∀ x ∈ (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A,
      x ∈ closure (((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A) \ {x})) ∧
    (∀ x ∈ (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A,
      x ∈ closure (((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A) \ {x})) ∧
    -- the frontier of `F ∩ φ⁻¹(A)`
    (∀ x ∈ (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A,
      x ∈ relFrontier (F₁ ∪ F₂ ∪ F₃) ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A) ↔
        x.1 ∈ relFrontier G A ∧ x ∉ relFrontier (F₁ ∪ F₂ ∪ F₃) F₂) ∧
    -- the frontier of `(F₁ ∪ F₂) ∩ φ⁻¹(A)`
    (∀ x ∈ (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A,
      x ∈ relFrontier (F₁ ∪ F₂ ∪ F₃) ((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A) ↔
        (x.1 ∈ relFrontier G A ∧ x ∉ relFrontier (F₁ ∪ F₂ ∪ F₃) F₁) ∨
          x ∈ relFrontier (F₁ ∪ F₂ ∪ F₃) F₃) := by
  obtain ⟨-, -, -, -, -, -, hfr1, hfr3, hfr2, -, -, hloc1, hloc2, hloc3⟩ := ho16_lemma6 hF
  have hcl : ∀ {x : E × ℝ}, x ∈ F₁ ∩ F₂ → x.1 ∈ A →
      ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ (F₁ ∪ F₂ ∪ F₃) ⊆ (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A :=
    fun hx hxA => lemma18_claim hF hV hx hxA
  have hcl' : ∀ {x : E × ℝ}, x ∈ F₂ ∩ F₃ → x.1 ∈ A →
      ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ (F₁ ∪ F₂ ∪ F₃) ⊆ (F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A :=
    fun hx hxA => lemma18_claim' hF hV hx hxA
  obtain ⟨⟨-, -, -, -, -, -, hcov, hG₂eq, -⟩, hF₁, hF₂, hF₃, -, hφ₁, -, hφ₂, -, hφ₃, -, -, h13⟩ :=
    hF
  have hFG : ∀ z ∈ F₁ ∪ F₂ ∪ F₃, z.1 ∈ G := by
    rintro z ((h | h) | h)
    · rw [← hcov, ← hφ₁]; exact Or.inl ⟨z, h, rfl⟩
    · have : z.1 ∈ G₂ := by rw [← hφ₂]; exact ⟨z, h, rfl⟩
      rw [hG₂eq] at this
      rw [← hcov]; exact Or.inl this.1
    · rw [← hcov, ← hφ₃]; exact Or.inr ⟨z, h, rfl⟩
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hF₁c : IsClosed F₁ := hF₁.isCompact.isClosed
  have hF₃c : IsClosed F₃ := hF₃.isCompact.isClosed
  -- a point not in the closure of `F \ X` when a neighbourhood lies in `X`
  have notcl : ∀ {X : Set (E × ℝ)} {x : E × ℝ} (U : Set (E × ℝ)), IsOpen U → x ∈ U →
      U ∩ (F₁ ∪ F₂ ∪ F₃) ⊆ X → x ∉ closure ((F₁ ∪ F₂ ∪ F₃) \ X) := by
    intro X x U hU hxU hUX hxc
    obtain ⟨z, hzU, hzF, hzX⟩ := mem_closure_iff.1 hxc U hU hxU
    exact hzX (hUX ⟨hzU, hzF⟩)
  -- points of `F₂` near a point of `F₂` over which `F` maps into `A`
  have nearF₂ : ∀ {X : Set (E × ℝ)} {x : E × ℝ} (U : Set (E × ℝ)), IsOpen U → x ∈ U →
      x ∈ F₂ → U ∩ F₂ ⊆ X → x ∈ closure (X \ {x}) := by
    intro X x U hU hxU hx2 hUX
    have hx2' : x ∈ closure (F₂ \ {x}) := hF₂.mem_closure_diff_finite hx2 (finite_singleton x)
    refine closure_mono ?_ (hU.inter_closure ⟨hxU, hx2'⟩)
    rintro z ⟨hzU, hz2, hzx⟩
    exact ⟨hUX ⟨hzU, hz2⟩, hzx⟩
  have hAx : ∀ x : E × ℝ, x.1 ∈ A → x.1 ∈ closure (A \ {x.1}) := fun x hx =>
    hA.mem_closure_diff_finite hx (finite_singleton _)
  have hsub : ∀ {Fi X : Set (E × ℝ)} {x : E × ℝ}, Fi ∩ Prod.fst ⁻¹' A ⊆ X →
      Fi ∩ Prod.fst ⁻¹' (A \ {x.1}) ⊆ X \ {x} := by
    intro Fi X x h z hz
    refine ⟨h ⟨hz.1, hz.2.1⟩, fun hzx => hz.2.2 ?_⟩
    rw [Set.mem_singleton_iff.1 hzx]
    rfl
  -- non-isolation in `X₂ = (F₁ ∪ F₂) ∩ φ⁻¹(A)`
  have noniso₂ : ∀ x ∈ (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A,
      x ∈ closure (((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A) \ {x}) := by
    rintro x ⟨hx, hxA⟩
    by_cases h12 : x ∈ F₁ ∩ F₂
    · obtain ⟨U, hU, hxU, hUX⟩ := hcl h12 hxA
      exact nearF₂ U hU hxU h12.2 fun z hz => hUX ⟨hz.1, Or.inl (Or.inr hz.2)⟩
    · by_cases h23 : x ∈ F₂ ∩ F₃
      · obtain ⟨U, hU, hxU, hUX⟩ := hcl' h23 hxA
        exact nearF₂ U hU hxU h23.1 fun z hz =>
          ⟨Or.inr hz.2, (hUX ⟨hz.1, Or.inl (Or.inr hz.2)⟩).2⟩
      · rcases hx with h1 | h2
        · exact closure_mono (hsub (by intro z hz; exact ⟨Or.inl hz.1, hz.2⟩))
            (lift_mem_closure (hloc1 x ⟨h1, fun h => h12 ⟨h1, h⟩⟩) (diff_subset.trans hAG)
              (hAx x hxA))
        · exact closure_mono (hsub (by intro z hz; exact ⟨Or.inr hz.1, hz.2⟩))
            (lift_mem_closure (hloc2 x ⟨h2, fun h => h.elim (fun h1 => h12 ⟨h1, h2⟩)
              fun h3 => h23 ⟨h2, h3⟩⟩) (diff_subset.trans hAG) (hAx x hxA))
  refine ⟨noniso₂, ?_, ?_, ?_⟩
  · rintro x ⟨hx, hxA⟩
    rcases hx with h12 | h3
    · exact closure_mono (diff_subset_diff_left (by intro z hz; exact ⟨Or.inl hz.1, hz.2⟩))
        (noniso₂ x ⟨h12, hxA⟩)
    · by_cases h2 : x ∈ F₂
      · exact closure_mono (diff_subset_diff_left (by intro z hz; exact ⟨Or.inl hz.1, hz.2⟩))
          (noniso₂ x ⟨Or.inr h2, hxA⟩)
      · exact closure_mono (hsub (by intro z hz; exact ⟨Or.inr hz.1, hz.2⟩))
          (lift_mem_closure (hloc3 x ⟨h3, h2⟩) (diff_subset.trans hAG) (hAx x hxA))
  · rintro x ⟨hx, hxA⟩
    rw [hfr2]
    constructor
    · rintro ⟨-, hxc⟩
      by_cases hb : x ∈ F₁ ∩ F₂ ∪ F₂ ∩ F₃
      · exfalso
        rcases hb with h12 | h23
        · obtain ⟨U, hU, hxU, hUX⟩ := hcl h12 hxA
          exact notcl U hU hxU (by intro z hz; exact ⟨Or.inl (hUX hz).1, (hUX hz).2⟩) hxc
        · obtain ⟨U, hU, hxU, hUX⟩ := hcl' h23 hxA
          refine notcl (X := (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A) U hU hxU ?_ hxc
          intro z hz
          refine ⟨?_, (hUX hz).2⟩
          rcases (hUX hz).1 with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
      · refine ⟨⟨subset_closure hxA, ?_⟩, hb⟩
        by_contra hint
        refine notcl (Prod.fst ⁻¹' (closure (G \ A))ᶜ)
          (isClosed_closure.isOpen_compl.preimage continuous_fst) hint ?_ hxc
        rintro z ⟨hzc, hzF⟩
        refine ⟨hzF, ?_⟩
        by_contra hzA
        exact hzc (subset_closure ⟨hFG z hzF, hzA⟩)
    · rintro ⟨⟨-, hyc⟩, hb⟩
      refine ⟨subset_closure ⟨hx, hxA⟩, ?_⟩
      have hY : ∀ {Fi : Set (E × ℝ)}, Fi ⊆ F₁ ∪ F₂ ∪ F₃ →
          Fi ∩ Prod.fst ⁻¹' (G \ A) ⊆ (F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' A) :=
        fun hFi z hz => ⟨hFi hz.1, fun h => hz.2.2 h.2⟩
      by_cases h2 : x ∈ F₂
      · have h2' : x ∈ F₂ \ (F₁ ∪ F₃) := ⟨h2, fun h => h.elim
          (fun h1 => hb (Or.inl ⟨h1, h2⟩)) fun h3 => hb (Or.inr ⟨h2, h3⟩)⟩
        exact closure_mono (hY fun z hz => Or.inl (Or.inr hz))
          (lift_mem_closure (hloc2 x h2') diff_subset hyc)
      · rcases hx with (h1 | h2'') | h3
        · exact closure_mono (hY fun z hz => Or.inl (Or.inl hz))
            (lift_mem_closure (hloc1 x ⟨h1, h2⟩) diff_subset hyc)
        · exact absurd h2'' h2
        · exact closure_mono (hY fun z hz => Or.inr hz)
            (lift_mem_closure (hloc3 x ⟨h3, h2⟩) diff_subset hyc)
  · rintro x ⟨hx, hxA⟩
    rw [hfr1, hfr3]
    by_cases h23 : x ∈ F₂ ∩ F₃
    · simp only [h23, or_true, iff_true]
      refine ⟨subset_closure ⟨hx, hxA⟩, ?_⟩
      have hx2 : x ∈ relFrontier (F₁ ∪ F₂ ∪ F₃) F₂ := by rw [hfr2]; exact Or.inr h23
      have hc := hx2.2
      have hsplit : (F₁ ∪ F₂ ∪ F₃) \ F₂ ⊆ (F₁ \ F₂) ∪ (F₃ \ F₂) := by
        rintro z ⟨(h | h) | h, hz2⟩
        · exact Or.inl ⟨h, hz2⟩
        · exact absurd h hz2
        · exact Or.inr ⟨h, hz2⟩
      have hc' := closure_mono hsplit hc
      rw [closure_union] at hc'
      rcases hc' with h | h
      · exact absurd (closure_minimal diff_subset hF₁c h) (Set.disjoint_right.1 h13 h23.2)
      · refine closure_mono ?_ h
        rintro z ⟨hz3, hz2⟩
        refine ⟨Or.inr hz3, fun hz => ?_⟩
        rcases hz.1 with h | h
        · exact Set.disjoint_left.1 h13 h hz3
        · exact hz2 h
    · by_cases h12 : x ∈ F₁ ∩ F₂
      · simp only [h12, not_true_eq_false, and_false, h23, or_false, iff_false]
        rintro ⟨-, hxc⟩
        obtain ⟨U, hU, hxU, hUX⟩ := hcl h12 hxA
        exact notcl U hU hxU hUX hxc
      · simp only [h12, not_false_eq_true, and_true, h23, or_false]
        have hx3 : x ∉ F₃ := by
          rcases hx with h1 | h2
          · exact fun h => Set.disjoint_left.1 h13 h1 h
          · exact fun h => h23 ⟨h2, h⟩
        constructor
        · rintro ⟨-, hxc⟩
          refine ⟨subset_closure hxA, ?_⟩
          by_contra hint
          refine notcl (Prod.fst ⁻¹' (closure (G \ A))ᶜ ∩ F₃ᶜ)
            ((isClosed_closure.isOpen_compl.preimage continuous_fst).inter hF₃c.isOpen_compl)
            ⟨hint, hx3⟩ ?_ hxc
          rintro z ⟨⟨hzc, hz3⟩, hzF⟩
          refine ⟨?_, ?_⟩
          · rcases hzF with h | h
            · exact h
            · exact absurd h hz3
          · by_contra hzA
            exact hzc (subset_closure ⟨hFG z hzF, hzA⟩)
        · rintro ⟨-, hyc⟩
          refine ⟨subset_closure ⟨hx, hxA⟩, ?_⟩
          have hY : ∀ {Fi : Set (E × ℝ)}, Fi ⊆ F₁ ∪ F₂ →
              Fi ∩ Prod.fst ⁻¹' (G \ A) ⊆ (F₁ ∪ F₂ ∪ F₃) \ ((F₁ ∪ F₂) ∩ Prod.fst ⁻¹' A) :=
            fun hFi z hz => ⟨Or.inl (hFi hz.1), fun h => hz.2.2 h.2⟩
          rcases hx with h1 | h2
          · exact closure_mono (hY fun z hz => Or.inl hz)
              (lift_mem_closure (hloc1 x ⟨h1, fun h => h12 ⟨h1, h⟩⟩) diff_subset hyc)
          · exact closure_mono (hY fun z hz => Or.inr hz)
              (lift_mem_closure (hloc2 x ⟨h2, fun h => h.elim (fun h1 => h12 ⟨h1, h2⟩) hx3⟩)
                diff_subset hyc)

/-- **H–O Lemma 18** (pp. 201–202). `F = F₁ ∪ F₂ ∪ F₃`; `S' = φ⋆⁻¹(S)` (inside `F⋆`);
`S'' = S' ∩ (F₁ ∪ F₂)⋆`; `(∂Fᵢ)⋆ = ∂Fᵢ × [0, 1]`, frontiers relative to `F`. -/
theorem ho16_lemma18 {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) {S : Set (E × ℝ)} (hS : IsStraight G S)
    (hV : Disjoint (relFrontier G (Prod.fst '' S)) (relFrontier G G₂) ∨
      ∃ V ∈ 𝓝ˢ (relFrontier G (Prod.fst '' S) ∩ relFrontier G G₂),
        G₂ ∩ V ⊆ Prod.fst '' S ∩ V) :
    -- (1)
    IsStraight (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) S) ∧
    endSet (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) S) =
      foldPre (F₁ ∪ F₂ ∪ F₃) (endSet G S) \
        relFrontier (F₁ ∪ F₂ ∪ F₃) F₂ ×ˢ Icc (0 : ℝ) 1 ∧
    -- (2)
    IsStraight (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) S ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) ∧
    endSet (F₁ ∪ F₂ ∪ F₃) (foldPre (F₁ ∪ F₂ ∪ F₃) S ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) =
      ((foldPre (F₁ ∪ F₂ ∪ F₃) (endSet G S) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) \
          relFrontier (F₁ ∪ F₂ ∪ F₃) F₁ ×ˢ Icc (0 : ℝ) 1) ∪
        (foldPre (F₁ ∪ F₂ ∪ F₃) S ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ∩
          relFrontier (F₁ ∪ F₂ ∪ F₃) F₃ ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨hSG, hSc, hSinj, hAPL⟩ := hS
  obtain ⟨noniso₂, noniso, hfrX, hfrX₂⟩ :=
    lemma18_points hF hAPL (by rintro _ ⟨q, hq, rfl⟩; exact (hSG hq).1) hV
  have hF₁ := hF.2.1
  have hF₂ := hF.2.2.1
  have hF₃ := hF.2.2.2.1
  have hFPL : IsPLGraph (F₁ ∪ F₂ ∪ F₃) := (hF₁.union hF₂).union hF₃
  have hF12c : IsClosed (F₁ ∪ F₂) := (hF₁.union hF₂).isCompact.isClosed
  have hX : Prod.fst '' foldPre (F₁ ∪ F₂ ∪ F₃) S =
      (F₁ ∪ F₂ ∪ F₃) ∩ Prod.fst ⁻¹' (Prod.fst '' S) := image_foldPre hSG
  have hX₂ : Prod.fst '' (foldPre (F₁ ∪ F₂ ∪ F₃) S ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1) =
      (F₁ ∪ F₂) ∩ Prod.fst ⁻¹' (Prod.fst '' S) := by
    rw [image_foldPre_inter hSG, inter_eq_right.2 (subset_union_left : F₁ ∪ F₂ ⊆ F₁ ∪ F₂ ∪ F₃)]
  have hclosed : IsClosed (foldPre (F₁ ∪ F₂ ∪ F₃) S) :=
    (hFPL.isCompact.isClosed.prod isClosed_Icc).inter (hSc.preimage continuous_phiStar)
  have PLof : ∀ {T : Set (E × ℝ)}, IsPLGraph T →
      (∀ x ∈ T ∩ Prod.fst ⁻¹' (Prod.fst '' S),
        x ∈ closure ((T ∩ Prod.fst ⁻¹' (Prod.fst '' S)) \ {x})) →
      IsPLGraph (T ∩ Prod.fst ⁻¹' (Prod.fst '' S)) := by
    intro T hT hni
    obtain ⟨K, P, hK, hP, hKP⟩ := hT.inter_preimage_fst hAPL
    rw [hKP] at hni ⊢
    exact isPLGraph_union_finite hK hP fun p hp => hni p (Or.inr hp)
  refine ⟨⟨inter_subset_left, hclosed, injOn_foldPre hSinj _ subset_rfl, ?_⟩, ?_,
    ⟨inter_subset_left.trans inter_subset_left, hclosed.inter (hF12c.prod isClosed_Icc),
      injOn_foldPre hSinj _ inter_subset_left, ?_⟩, ?_⟩
  · rw [hX]
    exact PLof hFPL noniso
  · ext q
    constructor
    · rintro ⟨hq, hqfr⟩
      rw [mem_preimage, hX] at hqfr
      obtain ⟨h1, h2⟩ := (hfrX q.1 ⟨hq.1.1, phiStar q, hq.2, rfl⟩).1 hqfr
      exact ⟨⟨hq.1, hq.2, h1⟩, fun h => h2 h.1⟩
    · rintro ⟨⟨hqF, hqS, hqA⟩, hq2⟩
      refine ⟨⟨hqF, hqS⟩, ?_⟩
      rw [mem_preimage, hX]
      exact (hfrX q.1 ⟨hqF.1, phiStar q, hqS, rfl⟩).2 ⟨hqA, fun h => hq2 ⟨h, hqF.2⟩⟩
  · rw [hX₂]
    exact PLof (hF₁.union hF₂) noniso₂
  · ext q
    constructor
    · rintro ⟨⟨hq, hq12⟩, hqfr⟩
      rw [mem_preimage, hX₂] at hqfr
      rcases (hfrX₂ q.1 ⟨hq12.1, phiStar q, hq.2, rfl⟩).1 hqfr with ⟨h1, h2⟩ | h3
      · exact Or.inl ⟨⟨⟨hq.1, hq.2, h1⟩, hq12⟩, fun h => h2 h.1⟩
      · exact Or.inr ⟨⟨hq, hq12⟩, h3, hq.1.2⟩
    · rintro (⟨⟨⟨hqF, hqS, hqA⟩, hq12⟩, hq1⟩ | ⟨⟨hq, hq12⟩, hq3, -⟩)
      · refine ⟨⟨⟨hqF, hqS⟩, hq12⟩, ?_⟩
        rw [mem_preimage, hX₂]
        exact (hfrX₂ q.1 ⟨hq12.1, phiStar q, hqS, rfl⟩).2
          (Or.inl ⟨hqA, fun h => hq1 ⟨h, hqF.2⟩⟩)
      · refine ⟨⟨hq, hq12⟩, ?_⟩
        rw [mem_preimage, hX₂]
        exact (hfrX₂ q.1 ⟨hq12.1, phiStar q, hq.2, rfl⟩).2 (Or.inr hq3)


end Lemma18

end HPC.HO16
