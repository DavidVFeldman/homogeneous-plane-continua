import HPC.Hagopian.H76Above

/-!
# Batch 164, item B (second part): an accessible point of `M − E` above `π[E]`

Hagopian p. 346 (T7): "Let `y` be a point of `M ∩ L₆` that is accessible from `R² − M` such that
`π(y)` is above `π[E]`." Commission 164 §1 B.1: "take the first point of `π[M]` met by a … segment
coming from a point of the complement". Here the segment is straight in collar coordinates, from a
point of the complement (`exists_notMem_piM`) to a point of `π[M]` (`M_meets_above`), both in the
window `F((a, b) × (0, c))`; it is pulled back by `π`, a homeomorphism off `E`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section AboveAcc

variable {M : Set Pt}

/-- The collar window above the axis misses `range γ`. -/
theorem IsCollar.disjoint_range_above {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {S : Set (ℝ × ℝ)} (hS : S ⊆ Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : Disjoint (F '' S) (range γ) := by
  rw [disjoint_left]
  rintro _ ⟨q, hq, rfl⟩ ⟨t, ht⟩
  have hqK : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨(hS hq).1, by linarith [(hS hq).2.1], (hS hq).2.2⟩
  have htK : ((t : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := ⟨t.2, by norm_num, by norm_num⟩
  have := hF.1.injective (a₁ := ⟨q, hqK⟩) (a₂ := ⟨((t : ℝ), 0), htK⟩)
    (by simp only [restrict_apply]; rw [hF.2.1 t]; exact ht.symm)
  have h2 := congrArg (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 => (p : ℝ × ℝ).2) this
  simp only at h2
  linarith [(hS hq).2.1]

/-- **An accessible point of `M − E` above `π[E]`** (T7's `y`, p. 346). If some strip below
`γ([a, b])` misses `π[M]` (`no_M_below`, `hagopian76_T6`), then every window `F((a, b) × (0, c))`
above `γ((a, b))` contains `π(x)` for a point `x` of `M − E` accessible from `R² − M`. -/
theorem exists_accessible_above [CompactSpace M] [ConnectedSpace M] (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {c : ℝ} (hc : 0 < c) :
    ∃ x ∈ M, x ∉ toPt E ∧ IsAccessibleFrom M x ∧ π x ∈ F '' (Ioo a b ×ˢ Ioo 0 c) := by
  set c₁ := min c 1 with hc₁
  have hc₁0 : 0 < c₁ := lt_min hc one_pos
  have hc₁c : c₁ ≤ c := min_le_left _ _
  have hc₁1 : c₁ ≤ 1 := min_le_right _ _
  set R := Ioo a b ×ˢ Ioo (0 : ℝ) c₁ with hR
  have hRK : R ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun q hq =>
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, by linarith [hq.2.1], by linarith [hq.2.2]⟩
  have hRup : R ⊆ Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := fun q hq =>
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2.1, by linarith [hq.2.2]⟩
  have hRO : R ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := fun q hq =>
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, by linarith [hq.2.1], by linarith [hq.2.2]⟩
  have hRc : Convex ℝ R := (convex_Ioo a b).prod (convex_Ioo 0 c₁)
  have hWγ : Disjoint (F '' R) (range γ) := hF.disjoint_range_above hRup
  have hMc : IsCompact M := isCompact_iff_compactSpace.2 ‹CompactSpace M›
  have hπM : IsClosed (π '' M) := (hMc.image hπ.continuous).isClosed
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_restrict.2 hF.1.continuous
  have hFinj : InjOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := fun p hp q hq h =>
    congrArg Subtype.val (hF.1.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) h)
  -- a point of `π[M]` and a point of the complement in the window
  obtain ⟨_, ⟨P₁, hP₁, rfl⟩, hqM⟩ := M_meets_above hi hE hπ.continuous hπS hγπ hF ha hab hb
    hbelow hc₁0
  obtain ⟨_, ⟨P₀, hP₀, rfl⟩, hwM⟩ := exists_notMem_piM hi hE hπ hπS hγπ
    (hF.isOpen_image (isOpen_Ioo.prod isOpen_Ioo) hRO) ⟨_, mem_image_of_mem F hP₁⟩ hWγ
  have hP01 : P₀ ≠ P₁ := fun h => hwM (h ▸ hqM)
  -- the segment
  set ℓ : ℝ → ℝ × ℝ := fun s => P₀ + s • (P₁ - P₀) with hℓ
  have hℓR : ∀ s ∈ Icc (0 : ℝ) 1, ℓ s ∈ R := fun s hs => hRc.add_smul_sub_mem hP₀ hP₁ hs
  have hℓc : Continuous ℓ := by fun_prop
  set g : ℝ → Pt := fun s => F (ℓ s) with hg
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    hFc.comp hℓc.continuousOn fun s hs => hRK (hℓR s hs)
  have hginj : InjOn g (Icc (0 : ℝ) 1) := by
    intro s hs s' hs' h
    have h1 := hFinj (hRK (hℓR s hs)) (hRK (hℓR s' hs')) h
    have h1' : s • (P₁ - P₀) = s' • (P₁ - P₀) := add_left_cancel h1
    have h2 : (s - s') • (P₁ - P₀) = 0 := by rw [sub_smul, h1', sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · linarith [sub_eq_zero.1 h3]
    · exact absurd (sub_eq_zero.1 h3).symm hP01
  -- the first parameter in `π[M]`
  set S := Icc (0 : ℝ) 1 ∩ g ⁻¹' (π '' M) with hS
  have hSc : IsClosed S := hgc.preimage_isClosed_of_isClosed isClosed_Icc hπM
  have hg1 : g 1 = F P₁ := by simp [hg, hℓ]
  have hg0 : g 0 = F P₀ := by simp [hg, hℓ]
  have h1S : (1 : ℝ) ∈ S := ⟨⟨zero_le_one, le_rfl⟩, by rw [mem_preimage, hg1]; exact hqM⟩
  have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf S with hs₀
  have hs₀S : s₀ ∈ S := hSc.csInf_mem ⟨1, h1S⟩ hSbdd
  have hs₀pos : 0 < s₀ := by
    rcases hs₀S.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hs₀S.2
      rw [← h, mem_preimage, hg0] at this
      exact hwM this
  have hs₀1 : s₀ ≤ 1 := hs₀S.1.2
  have hbefore : ∀ s ∈ Icc (0 : ℝ) 1, g s ∈ π '' M → s₀ ≤ s := fun s hs hsM =>
    csInf_le hSbdd ⟨hs, hsM⟩
  -- the arc in the plane, as a map of `[0, 1]`
  have hmem : ∀ τ : unitInterval, s₀ * τ ∈ Icc (0 : ℝ) 1 := fun τ =>
    ⟨mul_nonneg hs₀pos.le τ.2.1, by nlinarith [τ.2.1, τ.2.2]⟩
  set f : unitInterval → Pt := fun τ => g (s₀ * τ) with hf
  have hfc : Continuous f :=
    hgc.comp_continuous (continuous_const.mul continuous_subtype_val) hmem
  have hfinj : Function.Injective f := fun τ τ' h => by
    have := hginj (hmem τ) (hmem τ') h
    exact Subtype.ext (mul_left_cancel₀ hs₀pos.ne' this)
  have hfW : ∀ τ, f τ ∈ F '' R := fun τ => ⟨_, hℓR _ (hmem τ), rfl⟩
  -- `π` off `E` is an open embedding
  have hEc : IsClosed (toPt E) := (isCompact_toPt hE.isCompact).isClosed
  set O := (toPt E)ᶜ with hO
  set j : O → Pt := fun z => π z with hj
  have hjc : Continuous j := hπ.continuous.comp continuous_subtype_val
  have hjinj : Function.Injective j := fun z z' h => Subtype.ext (eq_of_pi_eq_off hπS z'.2 h)
  have hjo : IsOpenMap j := by
    intro V hV
    have : j '' V = π '' (Subtype.val '' V) := by rw [image_image]
    rw [this]
    refine pi_isOpen_image_off hπ hπS (hEc.isOpen_compl.isOpenMap_subtype_val V hV) ?_
    rw [disjoint_left]
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hjemb : IsEmbedding j :=
    (IsOpenEmbedding.of_continuous_injective_isOpenMap hjc hjinj hjo).isEmbedding
  have hlift : ∀ τ, ∃ z : O, j z = f τ := fun τ => by
    obtain ⟨z, hz⟩ := hπ.surjective (f τ)
    refine ⟨⟨z, fun hzE => disjoint_left.1 hWγ (hfW τ) ?_⟩, hz⟩
    rw [← hz]; exact pi_mem_range_of_mem hγπ hzE
  choose u hu using hlift
  have hju : j ∘ u = f := funext hu
  have huc : Continuous u := hjemb.continuous_iff.2 (by rw [hju]; exact hfc)
  set f' : unitInterval → Pt := fun τ => (u τ : Pt) with hf'
  have hπf' : ∀ τ, π (f' τ) = f τ := hu
  have hf'c : Continuous f' := continuous_subtype_val.comp huc
  have hf'inj : Function.Injective f' := fun τ τ' h => hfinj (by rw [← hπf', ← hπf', h])
  have hf'emb : IsEmbedding f' := (hf'c.isClosedEmbedding hf'inj).isEmbedding
  -- the accessible point
  have hf1 : f 1 = g s₀ := by simp [hf]
  have hf0 : f 0 = g 0 := by simp [hf]
  obtain ⟨m, hmM, hm⟩ := hs₀S.2
  have hx : f' 1 = m := by
    have hmE : m ∉ toPt E := fun hmE => disjoint_left.1 hWγ (hf1 ▸ hfW 1)
      (hm ▸ pi_mem_range_of_mem hγπ hmE)
    exact eq_of_pi_eq_off hπS hmE (by rw [hπf', hf1, hm])
  refine ⟨f' 1, hx ▸ hmM, (u 1).2, ⟨f' 0, range f', ⟨?_, f', hf'emb, rfl, rfl, rfl⟩, ?_⟩, ?_⟩
  · intro h
    have := congrArg π h
    rw [hπf', hπf', hf0, hf1, hg0] at this
    exact hwM (this ▸ hs₀S.2)
  · apply Subset.antisymm
    · rintro _ ⟨⟨τ, rfl⟩, hzM⟩
      have h1 : g (s₀ * τ) ∈ π '' M := ⟨_, hzM, hπf' τ⟩
      have h2 := hbefore _ (hmem τ) h1
      have hτ : (τ : ℝ) = 1 := le_antisymm τ.2.2 (by
        by_contra h; push_neg at h; nlinarith)
      rw [show τ = 1 from Subtype.ext hτ]
      rfl
    · rintro _ rfl
      exact ⟨mem_range_self 1, hx ▸ hmM⟩
  · rw [hπf', hf1]
    obtain ⟨h1, h2⟩ := hℓR s₀ hs₀S.1
    exact ⟨ℓ s₀, ⟨h1, h2.1, lt_of_lt_of_le h2.2 hc₁c⟩, rfl⟩

/-- **A closed set missing `π[M]` pulls back to a set at positive distance from `M`** (the
positivity in the definition of `ε₂`, p. 346: "the minimum of `ε₁` and `ρ(M, π⁻¹[I₁ ∪ I₂])`"). -/
theorem exists_pos_dist_preimage [CompactSpace M] {π : Pt → Pt} (hπc : Continuous π) {I : Set Pt}
    (hI : IsClosed I) (hIM : Disjoint I (π '' M)) :
    ∃ δ > 0, ∀ m ∈ M, ∀ z, π z ∈ I → δ ≤ dist m z := by
  have hMc : IsCompact M := isCompact_iff_compactSpace.2 ‹CompactSpace M›
  have hdis : Disjoint M (π ⁻¹' I) := by
    rw [disjoint_left]
    intro m hm hmI
    exact disjoint_left.1 hIM hmI ⟨m, hm, rfl⟩
  obtain ⟨δ, hδ, hd⟩ := hdis.exists_cthickenings hMc (hI.preimage hπc)
  refine ⟨δ, hδ, fun m hm z hz => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h1 : z ∈ cthickening δ M :=
    mem_cthickening_of_dist_le z m δ M hm (by rw [dist_comm]; exact hlt.le)
  exact disjoint_left.1 hd h1 (self_subset_cthickening _ hz)

end AboveAcc

end HPC.Hagopian
