import HPC.Moore.M19DExtract

/-!
# Moore 1919, Theorem D: lenses

A *lens* about a point `O` of `J` is a closed curve `k = t + t′` made of an arc `t` within `I` and
an arc `t′` without `I` with the same ends `u`, `v` on `J`; it crosses `J` at `u` and `v`
(`crosses_of_lens`). `lens_data` gives, about each point `O` of `J` in an open set `V`, an arc `φ` of
`J` through `O` such that for any two points `φ x`, `φ y` of it there is a lens with ends `φ x`,
`φ y`, within `V`, whose interior contains the open arc `φ (x, y)`. The inner arc is drawn in a
pocket of `I` (Theorem 28 with `M = I`), the outer one in a pocket without `I` (Theorem 28 with
`M = ext I`), and the interior of the lens is computed by Theorem 27.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- **A lens crosses `J` at its ends.** -/
theorem crosses_of_lens (h1 : σ.Axiom1) {I t t' : Set S} {u v : S} (ht : @TArc S σ.topology u v t)
    (ht' : @TArc S σ.topology u v t') (htI : t \ {u, v} ⊆ I)
    (ht'E : t' \ {u, v} ⊆ (@closure S σ.topology I)ᶜ) : σ.Crosses I (t ∪ t') u := by
  letI := σ.topology
  haveI := t2Space h1
  have piece : ∀ {M Z : Set S}, TArc u v M → M \ {u, v} ⊆ Z →
      ∃ m Γ₁ Γ₂, TArc u m Γ₁ ∧ Γ₁ ∪ Γ₂ = M ∧ u ∉ Γ₂ ∧ IsClosed Γ₂ ∧ Γ₁ \ {u} ⊆ Z := by
    intro M Z hM hMZ
    obtain ⟨m, hmM, hmn⟩ := hM.nonempty_diff
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hmn
    obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hu, hi⟩ := hM.split hmM hmn.1 hmn.2
    refine ⟨m, Γ₁, Γ₂, hΓ₁, hu, fun h => hmn.1 ?_, hΓ₂.isClosed, ?_⟩
    · exact (Space.Quad.Cut.single hΓ₁.left_mem h hi).symm
    · rintro z ⟨hz, hzu⟩
      refine hMZ ⟨hu ▸ Or.inl hz, ?_⟩
      rintro (e | e)
      · exact hzu e
      · subst e
        exact hmn.2 (Space.Quad.Cut.single hz hΓ₂.right_mem hi).symm
  obtain ⟨m, Γ₁, Γ₂, hΓ₁, hΓu, huΓ, hΓc, hΓI⟩ := piece ht htI
  obtain ⟨m', Δ₁, Δ₂, hΔ₁, hΔu, huΔ, hΔc, hΔE⟩ := piece ht' ht'E
  refine ⟨Γ₂ᶜ ∩ Δ₂ᶜ, Filter.inter_mem (hΓc.isOpen_compl.mem_nhds huΓ)
    (hΔc.isOpen_compl.mem_nhds huΔ), m, m', Γ₁, Δ₁, hΓ₁.symm, hΔ₁, hΓI, hΔE, ?_⟩
  rintro z ⟨hz | hz, hzΓ, hzΔ⟩
  · rw [← hΓu] at hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact absurd hz hzΓ
  · rw [← hΔu] at hz
    rcases hz with hz | hz
    · exact Or.inr hz
    · exact absurd hz hzΔ

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Lenses about a point of `J`.** -/
theorem lens_data {J I : Set S} (hJI : σ.IsInteriorOf J I) {V : Set S}
    (hVo : @IsOpen S σ.topology V) {O : S} (hO : O ∈ J) (hOV : O ∈ V) :
    ∃ U, @IsOpen S σ.topology U ∧ O ∈ U ∧ ∃ φ : unitInterval → S,
      @IsEmbedding _ _ _ σ.topology φ ∧ range φ ⊆ J ∧ ∃ a b : unitInterval, 0 < a ∧ a < b ∧
      b < 1 ∧ U ∩ J ⊆ φ '' Ioo a b ∧ ∀ x y : unitInterval, 0 < x → x < y → y < 1 →
        ∃ k Wk, σ.IsInteriorOf k Wk ∧ k ∪ Wk ⊆ V ∧ k ∩ J = {φ x, φ y} ∧ φ '' Ioo x y ⊆ Wk ∧
          σ.Crosses I k (φ x) ∧ σ.Crosses I k (φ y) := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have th21 : ∀ {K R : Set S}, K ∈ σ.region → R ∈ σ.region → frontier R ⊆ closure K → R ⊆ K :=
    fun hK hR h => fa_theorem21 h1 h3 h4 h5 h7 hK hR
      (by rw [bdry_eq_frontier h1, cl_eq_closure h1]; exact h)
  have mkInt : ∀ {a b : S} {M N : Set S}, TArc a b M → TArc a b N → M ∩ N = {a, b} →
      ∃ P, σ.IsInteriorOf (M ∪ N) P := by
    intro a b M N hM hN hMN
    have hs : σ.IsSCC (M ∪ N) := (isSCC_iff_tscc h1 h3 h4 h51).mpr ⟨a, b, M, N, hM, hN, hMN, rfl⟩
    obtain ⟨P, hPr, hPb⟩ := h8 _ hs
    exact ⟨P, hs, hPr, hPb⟩
  obtain ⟨hIo, hIc, ⟨zI, hzI⟩, hfrI, hEo, -, -, -, hclI, hIJ, hEJ, hJc, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hJI
  have hJcl : J ⊆ closure I := fun z hz => hclI ▸ Or.inr hz
  have hOz : O ≠ zI := fun e => disjoint_left.mp hIJ (e ▸ hzI) hO
  obtain ⟨R', hR', hOR', hR'cl⟩ := exists_region_closure_subset h1
    (hVo.inter isOpen_compl_singleton) (⟨hOV, hOz⟩ : O ∈ V ∩ {zI}ᶜ)
  have hR'o : IsOpen R' := isOpen_region hR'
  -- the inner pocket
  obtain ⟨A₁, B₁, X₁, C₁, C₂, hX₁, hX₁o, hC₁, hC₂, hCi, hCu, hOC₁, hC₁R'⟩ :=
    fa_theorem28 h1 h2 h3 h4 h51 h6 h7 hJI hO hR' hOR' (Or.inl rfl)
  rw [isArc_iff_tarc h1 h3 h4 h51] at hX₁ hC₁ hC₂
  have hC₁J : C₁ ⊆ J := hCu ▸ subset_union_left
  have hOC₂ : O ∉ C₂ := fun h => hOC₁.2 (hCi ▸ (⟨hOC₁.1, h⟩ : O ∈ C₁ ∩ C₂))
  obtain ⟨R'', hR'', hOR'', hR''sub⟩ :=
    (isOpen_iff_region h1).mp (hR'o.sdiff hC₂.isClosed) O ⟨hOR', hOC₂⟩
  -- the outer pocket
  obtain ⟨A₂, B₂, X₂, D₁, D₂, hX₂, hX₂o, hD₁, hD₂, hDi, hDu, hOD₁, hD₁R''⟩ :=
    fa_theorem28 h1 h2 h3 h4 h51 h6 h7 hJI hO hR'' hOR'' (Or.inr rfl)
  rw [isArc_iff_tarc h1 h3 h4 h51] at hX₂ hD₁ hD₂
  rw [ext_eq_compl_closure h1] at hX₂o
  have hD₁J : D₁ ⊆ J := hDu ▸ subset_union_left
  have hD₁C₁ : D₁ ⊆ C₁ := by
    intro z hz
    have hzJ : z ∈ C₁ ∪ C₂ := hCu.symm ▸ hD₁J hz
    rcases hzJ with h | h
    · exact h
    · exact absurd h (hR''sub (hD₁R'' hz)).2
  have hX₁C₁ : X₁ ∩ C₁ = {A₁, B₁} := by
    apply subset_antisymm
    · rintro z ⟨hz, hzC⟩
      by_contra hn
      exact disjoint_left.mp hIJ (hX₁o ⟨hz, hn⟩).1 (hC₁J hzC)
    · rintro z (rfl | rfl)
      exacts [⟨hX₁.left_mem, hC₁.left_mem⟩, ⟨hX₁.right_mem, hC₁.right_mem⟩]
  have hX₂D₁ : X₂ ∩ D₁ = {A₂, B₂} := by
    apply subset_antisymm
    · rintro z ⟨hz, hzD⟩
      by_contra hn
      exact disjoint_left.mp hEJ (hX₂o ⟨hz, hn⟩).1 (hD₁J hzD)
    · rintro z (rfl | rfl)
      exacts [⟨hX₂.left_mem, hD₁.left_mem⟩, ⟨hX₂.right_mem, hD₁.right_mem⟩]
  obtain ⟨P, hP⟩ := mkInt hX₁ hC₁ hX₁C₁
  obtain ⟨P', hP'⟩ := mkInt hX₂ hD₁ hX₂D₁
  obtain ⟨hPo, -, -, hfrP, -, -, -, -, hclP, -⟩ := jordan h1 h2 h3 h4 h51 h7 hP
  obtain ⟨hP'o, -, -, hfrP', -, -, -, -, hclP', -⟩ := jordan h1 h2 h3 h4 h51 h7 hP'
  have hX₁cl : X₁ ⊆ C₁ ∪ I := by
    intro z hz
    by_cases hn : z ∈ ({A₁, B₁} : Set S)
    · rcases hn with rfl | rfl
      exacts [Or.inl hC₁.left_mem, Or.inl hC₁.right_mem]
    · exact Or.inr (hX₁o ⟨hz, hn⟩).1
  have hX₁R' : X₁ ⊆ R' := by
    intro z hz
    by_cases hn : z ∈ ({A₁, B₁} : Set S)
    · rcases hn with rfl | rfl
      exacts [hC₁R' hC₁.left_mem, hC₁R' hC₁.right_mem]
    · exact (hX₁o ⟨hz, hn⟩).2
  have hX₂R'' : X₂ ⊆ R'' := by
    intro z hz
    by_cases hn : z ∈ ({A₂, B₂} : Set S)
    · rcases hn with rfl | rfl
      exacts [hD₁R'' hD₁.left_mem, hD₁R'' hD₁.right_mem]
    · exact (hX₂o ⟨hz, hn⟩).2
  have hPI : P ⊆ I := th21 hJI.2.1 hP.2.1 (by
    rw [hfrP]
    refine union_subset (fun z hz => ?_) (hC₁J.trans hJcl)
    rcases hX₁cl hz with h | h
    exacts [hJcl (hC₁J h), subset_closure h])
  have hPR' : P ⊆ R' := th21 hR' hP.2.1 (by
    rw [hfrP]; exact (union_subset hX₁R' hC₁R').trans subset_closure)
  have hP'R'' : P' ⊆ R'' := th21 hR'' hP'.2.1 (by
    rw [hfrP']; exact (union_subset hX₂R'' hD₁R'').trans subset_closure)
  have hR''R' : R'' ⊆ R' := fun z hz => (hR''sub hz).1
  have hP'I : Disjoint P' I := by
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne
    have hsub : I ⊆ P' := by
      refine hIc.subset_left_of_subset_union hP'o isClosed_closure.isOpen_compl
        (disjoint_compl_right.mono_left subset_closure) ?_ (by
          rw [inter_comm]; exact nonempty_iff_ne_empty.mpr hne)
      intro z hz
      by_cases h : z ∈ P'
      · exact Or.inl h
      · right
        intro hcl
        have hfr : z ∈ frontier P' := ⟨hcl, by rwa [hP'o.interior_eq]⟩
        rw [hfrP'] at hfr
        rcases hfr with h' | h'
        · by_cases hn : z ∈ ({A₂, B₂} : Set S)
          · rcases hn with rfl | rfl
            · exact disjoint_left.mp hIJ hz (hD₁J hD₁.left_mem)
            · exact disjoint_left.mp hIJ hz (hD₁J hD₁.right_mem)
          · exact (hX₂o ⟨h', hn⟩).1 (subset_closure hz)
        · exact disjoint_left.mp hIJ hz (hD₁J h')
    have := hR'cl (subset_closure (hR''R' (hP'R'' (hsub hzI))))
    exact this.2 rfl
  have hP'E : P' ⊆ (closure I)ᶜ := by
    intro z hz hzcl
    obtain ⟨w, hw⟩ := mem_closure_iff.mp hzcl P' hP'o hz
    exact disjoint_left.mp hP'I hw.1 hw.2
  -- the arc `φ` of `J` and the open set `U`
  obtain ⟨-, φ, hφ, hφr, hφ0, hφ1⟩ := hD₁
  obtain ⟨s₀, hs₀⟩ : O ∈ range φ := hφr ▸ hOD₁.1
  have hs₀0 : 0 < s₀ := lt_of_le_of_ne nonneg' fun e => hOD₁.2 (Or.inl (by rw [← hs₀, ← e, hφ0]))
  have hs₀1 : s₀ < 1 := lt_of_le_of_ne le_one' fun e => hOD₁.2 (Or.inr (by rw [← hs₀, e, hφ1]; rfl))
  obtain ⟨a, ha0, has⟩ := exists_between hs₀0
  obtain ⟨b, hsb, hb1⟩ := exists_between hs₀1
  refine ⟨(D₂ ∪ φ '' Icc 0 a ∪ φ '' Icc b 1)ᶜ, ?_, ?_, φ, hφ, hφr ▸ hD₁J, a, b, ha0,
    has.trans hsb, hb1, ?_, ?_⟩
  · exact ((hD₂.isClosed.union (isCompact_Icc.image hφ.continuous).isClosed).union
      (isCompact_Icc.image hφ.continuous).isClosed).isOpen_compl
  · simp only [mem_compl_iff, mem_union, not_or]
    refine ⟨⟨fun h => hOD₁.2 ?_, ?_⟩, ?_⟩
    · have : O ∈ D₁ ∩ D₂ := ⟨hOD₁.1, h⟩
      rwa [hDi] at this
    · rintro ⟨s, hs, hsO⟩
      rw [← hs₀] at hsO
      exact absurd (hφ.injective hsO ▸ hs.2) (not_le.mpr has)
    · rintro ⟨s, hs, hsO⟩
      rw [← hs₀] at hsO
      exact absurd (hφ.injective hsO ▸ hs.1) (not_le.mpr hsb)
  · rintro z ⟨hzU, hzJ⟩
    simp only [mem_compl_iff, mem_union, not_or] at hzU
    obtain ⟨⟨hzD₂, hza⟩, hzb⟩ := hzU
    rw [← hDu] at hzJ
    rcases hzJ with hz | hz
    · rw [← hφr] at hz
      obtain ⟨s, rfl⟩ := hz
      refine ⟨s, ⟨?_, ?_⟩, rfl⟩
      · exact not_le.mp fun h => hza ⟨s, ⟨nonneg', h⟩, rfl⟩
      · exact not_le.mp fun h => hzb ⟨s, ⟨h, le_one'⟩, rfl⟩
    · exact absurd hz hzD₂
  -- the lenses
  intro x y hx hxy hy
  have huv : φ x ≠ φ y := fun e => hxy.ne (hφ.injective e)
  have hu : φ x ∈ D₁ := hφr ▸ mem_range_self x
  have hv : φ y ∈ D₁ := hφr ▸ mem_range_self y
  obtain ⟨t, ht, htP⟩ := exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 hP (Or.inl rfl)
    (Or.inr (hD₁C₁ hu)) (Or.inr (hD₁C₁ hv)) huv
  obtain ⟨t', ht', ht'P⟩ := exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 hP' (Or.inl rfl)
    (Or.inr hu) (Or.inr hv) huv
  have hc : TArc (φ x) (φ y) (φ '' Icc x y) := TArc.image_Icc hφ hxy
  have hcD : φ '' Icc x y ⊆ D₁ := hφr ▸ image_subset_range _ _
  have hcJ : φ '' Icc x y ⊆ J := hcD.trans hD₁J
  have htI : t \ {φ x, φ y} ⊆ I := htP.trans hPI
  have ht'E : t' \ {φ x, φ y} ⊆ (closure I)ᶜ := ht'P.trans hP'E
  have inter : ∀ {M : Set S} {Z : Set S}, φ x ∈ M → φ y ∈ M → M \ {φ x, φ y} ⊆ Z →
      Disjoint Z J → M ∩ φ '' Icc x y = {φ x, φ y} := by
    intro M Z hxM hyM hMZ hZJ
    apply subset_antisymm
    · rintro z ⟨hzM, hzc⟩
      by_contra hn
      exact disjoint_left.mp hZJ (hMZ ⟨hzM, hn⟩) (hcJ hzc)
    · rintro z (rfl | rfl)
      exacts [⟨hxM, hc.left_mem⟩, ⟨hyM, hc.right_mem⟩]
  have htc := inter ht.left_mem ht.right_mem htI hIJ
  have ht'c := inter ht'.left_mem ht'.right_mem ht'E hEJ
  have htt' : t' ∩ t = {φ x, φ y} := by
    apply subset_antisymm
    · rintro z ⟨hz', hz⟩
      by_contra hn
      exact ht'E ⟨hz', hn⟩ (subset_closure (htI ⟨hz, hn⟩))
    · rintro z (rfl | rfl)
      exacts [⟨ht'.left_mem, ht.left_mem⟩, ⟨ht'.right_mem, ht.right_mem⟩]
  obtain ⟨RL, hRL⟩ := mkInt hc ht (by rw [inter_comm]; exact htc)
  obtain ⟨R₁, hR₁⟩ := mkInt ht' hc ht'c
  obtain ⟨Wk, hWk⟩ := mkInt ht' ht htt'
  obtain ⟨-, -, -, hfrRL, -, -, -, -, hclRL, -⟩ := jordan h1 h2 h3 h4 h51 h7 hRL
  obtain ⟨-, -, -, hfrR₁, -, -, -, -, hclR₁, -⟩ := jordan h1 h2 h3 h4 h51 h7 hR₁
  have htP' : t ⊆ closure P := by
    intro z hz
    by_cases hn : z ∈ ({φ x, φ y} : Set S)
    · rw [hclP]; rcases hn with rfl | rfl
      exacts [Or.inr (Or.inr (hD₁C₁ hu)), Or.inr (Or.inr (hD₁C₁ hv))]
    · exact subset_closure (htP ⟨hz, hn⟩)
  have ht'P' : t' ⊆ closure P' := by
    intro z hz
    by_cases hn : z ∈ ({φ x, φ y} : Set S)
    · rw [hclP']; rcases hn with rfl | rfl
      exacts [Or.inr (Or.inr hu), Or.inr (Or.inr hv)]
    · exact subset_closure (ht'P ⟨hz, hn⟩)
  have hRLP : RL ⊆ P := th21 hP.2.1 hRL.2.1 (by
    rw [hfrRL, hclP]
    exact union_subset (fun z hz => Or.inr (Or.inr (hD₁C₁ (hcD hz))))
      (fun z hz => hclP ▸ htP' hz))
  have hR₁P' : R₁ ⊆ P' := th21 hP'.2.1 hR₁.2.1 (by
    rw [hfrR₁, hclP']
    exact union_subset (fun z hz => hclP' ▸ ht'P' hz)
      (fun z hz => Or.inr (Or.inr (hcD hz))))
  obtain ⟨Cpt, hCpt⟩ := hc.nonempty_diff
  obtain ⟨Dpt, hDpt⟩ := ht.nonempty_diff
  have hsep : σ.SeparatesOn (φ '' Icc x y ∪ t) (φ x) (φ y) Cpt Dpt (φ '' Icc x y) t :=
    ⟨(isArc_iff_tarc h1 h3 h4 h51).mpr hc, (isArc_iff_tarc h1 h3 h4 h51).mpr ht,
      by rw [inter_comm]; exact htc, rfl, hCpt, hDpt⟩
  have hXR : openArc (φ x) (φ y) t' ⊆ σ.ext RL := by
    rw [ext_eq_compl_closure h1]
    intro z hz hzcl
    exact ht'E hz (closure_mono (hRLP.trans hPI) hzcl)
  obtain ⟨-, H⟩ := fa_theorem27 h1 h2 h3 h4 h5 h7 h8 hRL hsep
    ((isArc_iff_tarc h1 h3 h4 h51).mpr ht') hXR hR₁ hWk
  have hDext : Dpt ∈ σ.ext R₁ := by
    rw [ext_eq_compl_closure h1, hclR₁]
    have hDI : Dpt ∈ I := htI hDpt
    rintro (h | h | h)
    · exact hP'E (hR₁P' h) (subset_closure hDI)
    · exact ht'E ⟨h, hDpt.2⟩ (subset_closure hDI)
    · exact disjoint_left.mp hIJ hDI (hcJ h)
  obtain ⟨-, hWeq⟩ := H hDext
  have hk : t' ∪ t ⊆ R' := by
    refine union_subset (fun z hz => ?_) (fun z hz => ?_)
    · by_cases hn : z ∈ ({φ x, φ y} : Set S)
      · rcases hn with rfl | rfl
        exacts [hR''R' (hD₁R'' hu), hR''R' (hD₁R'' hv)]
      · exact hR''R' (hP'R'' (ht'P ⟨hz, hn⟩))
    · by_cases hn : z ∈ ({φ x, φ y} : Set S)
      · rcases hn with rfl | rfl
        exacts [hR''R' (hD₁R'' hu), hR''R' (hD₁R'' hv)]
      · exact hPR' (htP ⟨hz, hn⟩)
  have hWR : Wk ⊆ R' := by
    rw [hWeq]
    refine union_subset (union_subset (fun z hz => hR''R' (hD₁R'' (hcD hz.1)))
      (hRLP.trans hPR')) (hR₁P'.trans (hP'R''.trans hR''R'))
  have hcross : ∀ {u v : S} {t t' : Set S}, TArc u v t → TArc u v t' → t \ {u, v} ⊆ I →
      t' \ {u, v} ⊆ (closure I)ᶜ → σ.Crosses I (t' ∪ t) u := fun h₁ h₂ h₃ h₄ => by
    rw [union_comm]; exact crosses_of_lens h1 h₁ h₂ h₃ h₄
  refine ⟨t' ∪ t, Wk, hWk, ?_, ?_, ?_, hcross ht ht' htI ht'E, ?_⟩
  · exact union_subset ((hk.trans subset_closure).trans fun z hz => (hR'cl hz).1)
      ((hWR.trans subset_closure).trans fun z hz => (hR'cl hz).1)
  · apply subset_antisymm
    · rintro z ⟨hz | hz, hzJ⟩
      · by_contra hn; exact disjoint_left.mp hEJ (ht'E ⟨hz, hn⟩) hzJ
      · by_contra hn; exact disjoint_left.mp hIJ (htI ⟨hz, hn⟩) hzJ
    · rintro z (rfl | rfl)
      exacts [⟨Or.inr ht.left_mem, hcJ hc.left_mem⟩, ⟨Or.inr ht.right_mem, hcJ hc.right_mem⟩]
  · rw [hWeq, ← image_Icc_diff hφ.injective]
    exact fun z hz => Or.inl (Or.inl hz)
  · exact hcross ht.symm ht'.symm (by rw [pair_comm]; exact htI) (by rw [pair_comm]; exact ht'E)

end Ax


end HPC.Moore
