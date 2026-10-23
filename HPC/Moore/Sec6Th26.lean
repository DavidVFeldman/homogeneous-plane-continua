import HPC.Moore.Sec6Th25

/-!
# Moore, F.A. (1916), §6: Theorem 26, in the topological setting (batch 138)

**Theorem 26.** If `ACB`, `ADB`, `AFB` are three arcs, no two with a common point other than `A`
and `B`, the interiors of `ACBFA`, `ACBDA`, `ADBFA` are not mutually exclusive.

Moore's proof (pp. 143–144), with the arcs `K₁ = ACB`, `K₂ = ADB`, `K₃ = AFB` and interiors
`R`, `R₁`, `R₂`. Suppose they are mutually exclusive.

* Each open arc lies without the curve formed by the other two (`th26_aux`; for `ADB` this is
  Moore's \"`E` contains `ADB`\": were it within `J`, Theorem 24 would put `R₁` inside `R`).
* `Y` = the points without all three curves (Moore: \"It is clear that `Y` is composed of all
  points that are common to `E`, `E₁` and `E₂`\"); it is nonempty (Theorems 17 and 13: the closures
  of the three regions are compact, the space is not).
* `P ∈ Y`, an arc `PD` without `J`, its first point `O` on `ADB`; `PO − O ⊆ Y`. For every point of
  `Y` a similar arc reaches `ACB` through `Y`.
* Points `G₁ G₂ O H₂ H₁` on `ADB` and arcs `G₁P₁H₁` through `R₁`, `G₂P₂H₂` through `R₂`
  (\"It can easily be shown\", footnote \"Cf. proof of Theorem 25\": `exists_cross`); the closed curve
  `J̄ = G₁P₁H₁H₂P₂G₂G₁` with interior `R̄`.
* Moore's three cases. Here: if `R̄` met `ACB + AFB` it would contain it (it is connected and
  misses `J̄`), and then all of `Y` (Moore's Case II), which is impossible since `Y` is not bounded;
  if `R̄` met `Y` it would meet `ACB` through the arcs above (this replaces Moore's Case I, which
  used Theorem 25); so `O`, `A`, `B` are without `J̄`, `R̄` misses `ADB`, and `R̄ ⊆ R + R₁ + R₂`
  while meeting `R₁` and `R₂` (Case III). Moore's auxiliary curves `J̄₁`, `J̄₂` are not needed.
-/

namespace HPC.Moore

open Set Topology
open unitInterval (nonneg' le_one')

namespace Gen

variable {T : Type*} [TopologicalSpace T] [T2Space T] {reg : Set (Set T)}

/-- **The closed curve of two crossing arcs** (used in Theorems 25 and 26): if `α` joins
`f h`, `f k` and `β` joins `f hb`, `f kb` (`hb < h < k < kb`), both meeting the arc `f` only at
their ends and each other not at all, then `α + f[k, kb] + f[hb, h] + β` is a closed curve; it meets
the arc `f` in `f[hb, h] + f[k, kb]`. -/
theorem tscc_theta {f : unitInterval → T} (hf : IsEmbedding f) {α β : Set T}
    {h k hb kb : unitInterval} (hα : TArc (f h) (f k) α) (hβ : TArc (f hb) (f kb) β)
    (hbh : hb < h) (hhk : h < k) (hkkb : k < kb)
    (hαX : ∀ x ∈ α, x ∈ range f → x = f h ∨ x = f k)
    (hβX : ∀ x ∈ β, x ∈ range f → x = f hb ∨ x = f kb) (hαβ : Disjoint α β) :
    TSCC (α ∪ f '' Icc k kb ∪ (f '' Icc hb h ∪ β)) ∧
      ∀ v, f v ∈ α ∪ f '' Icc k kb ∪ (f '' Icc hb h ∪ β) → v ∈ Icc hb h ∨ v ∈ Icc k kb := by
  have hinj := hf.injective
  have hA1 : TArc (f h) (f kb) (α ∪ f '' Icc k kb) := by
    refine hα.union (TArc.image_Icc hf hkkb) (subset_antisymm ?_ ?_)
    · rintro x ⟨hxα, v, hv, rfl⟩
      rcases hαX _ hxα (mem_range_self v) with e | e
      · exact absurd (hinj e ▸ hv.1) (not_le.mpr hhk)
      · exact e
    · rintro x rfl; exact ⟨hα.right_mem, mem_image_of_mem f ⟨le_rfl, hkkb.le⟩⟩
  have hA2 : TArc (f h) (f kb) (f '' Icc hb h ∪ β) := by
    refine (TArc.image_Icc hf hbh).symm.union hβ (subset_antisymm ?_ ?_)
    · rintro x ⟨⟨v, hv, rfl⟩, hxβ⟩
      rcases hβX _ hxβ (mem_range_self v) with e | e
      · exact e
      · exact absurd (hinj e ▸ hv.2) (not_le.mpr (hhk.trans hkkb))
    · rintro x rfl; exact ⟨mem_image_of_mem f ⟨le_rfl, hbh.le⟩, hβ.left_mem⟩
  refine ⟨⟨f h, f kb, _, _, hA1, hA2, subset_antisymm ?_ ?_, rfl⟩, ?_⟩
  · rintro x ⟨hx1 | ⟨v, hv, rfl⟩, hx2 | hx2⟩
    · obtain ⟨v, hv, rfl⟩ := hx2
      rcases hαX _ hx1 (mem_range_self v) with e | e
      · exact Or.inl e
      · exact absurd (hinj e ▸ hv.2) (not_le.mpr hhk)
    · exact absurd hx2 (disjoint_left.mp hαβ hx1)
    · obtain ⟨w, hw, e⟩ := hx2
      exact absurd (hinj e ▸ hw.2) (not_le.mpr (lt_of_lt_of_le hhk hv.1))
    · rcases hβX _ hx2 (mem_range_self v) with e | e
      · exact absurd (hinj e ▸ hv.1) (not_le.mpr (hbh.trans hhk))
      · exact Or.inr e
  · rintro x (rfl | rfl)
    · exact ⟨Or.inl hα.left_mem, Or.inl (mem_image_of_mem f ⟨hbh.le, le_rfl⟩)⟩
    · exact ⟨Or.inr (mem_image_of_mem f ⟨hkkb.le, le_rfl⟩), Or.inr hβ.right_mem⟩
  · rintro v ((hx | ⟨w, hw, e⟩) | (⟨w, hw, e⟩ | hx))
    · rcases hαX _ hx (mem_range_self v) with e | e <;> have e' := hinj e <;> subst e'
      exacts [Or.inl ⟨hbh.le, le_rfl⟩, Or.inr ⟨le_rfl, hkkb.le⟩]
    · exact Or.inr (hinj e ▸ hw)
    · exact Or.inl (hinj e ▸ hw)
    · rcases hβX _ hx (mem_range_self v) with e | e <;> have e' := hinj e <;> subst e'
      exacts [Or.inl ⟨le_rfl, hbh.le⟩, Or.inr ⟨hkkb.le, le_rfl⟩]

omit [T2Space T] in
/-- **An arc misses an open set** whose boundary meets it in two intervals `f[a, b]`, `f[c, d]`,
if the three remaining pieces each contain a point without the closure. -/
theorem image_notMem_of_pieces {f : unitInterval → T} (hf : IsEmbedding f) {Rb Jb : Set T}
    (hRbo : IsOpen Rb) (hRbJ : frontier Rb = Jb) {a b c d : unitInterval} (hab : a ≤ b)
    (hbc : b < c) (hcd : c ≤ d) (hJ : ∀ v, f v ∈ Jb → v ∈ Icc a b ∨ v ∈ Icc c d)
    (hJ1 : f '' Icc a b ⊆ Jb) (hJ2 : f '' Icc c d ⊆ Jb) (h0 : f 0 ∉ closure Rb)
    {m : unitInterval} (hbm : b < m) (hmc : m < c) (hm : f m ∉ closure Rb)
    (h1 : f 1 ∉ closure Rb) : ∀ v, f v ∉ Rb := by
  have hpiece : ∀ s : Set unitInterval, IsPreconnected s →
      (∀ v ∈ s, v ∉ Icc a b ∧ v ∉ Icc c d) → (∃ v ∈ s, f v ∉ closure Rb) →
      ∀ v ∈ s, f v ∉ Rb := by
    intro s hs hsJ ⟨v₀, hv₀, hv₀c⟩ v hv hvRb
    have hpre : IsPreconnected (f '' s) := hs.image _ hf.continuous.continuousOn
    have hd : Disjoint (f '' s) (frontier Rb) := by
      rw [hRbJ]
      refine disjoint_left.mpr ?_
      rintro _ ⟨w, hw, rfl⟩ hwJ
      exact (hJ w hwJ).elim (hsJ w hw).1 (hsJ w hw).2
    exact conn_sub_ext_of_frontier hpre hd ⟨f v₀, mem_image_of_mem f hv₀, hv₀c⟩
      (mem_image_of_mem f hv) (subset_closure hvRb)
  intro v hv
  have hvJ : f v ∉ Jb := fun h' => notMem_of_mem_frontier hRbo (hRbJ ▸ h') hv
  rcases lt_or_ge v a with h1' | h1'
  · refine hpiece (Ico 0 a) isPreconnected_Ico (fun w hw => ⟨fun h' => ?_, fun h' => ?_⟩)
      ⟨0, ⟨le_rfl, lt_of_le_of_lt nonneg' h1'⟩, h0⟩ v ⟨nonneg', h1'⟩ hv
    · exact absurd h'.1 (not_le.mpr hw.2)
    · exact absurd h'.1 (not_le.mpr (hw.2.trans_le (hab.trans hbc.le)))
  rcases le_or_gt v b with h2 | h2
  · exact hvJ (hJ1 (mem_image_of_mem f ⟨h1', h2⟩))
  rcases lt_or_ge v c with h3 | h3
  · refine hpiece (Ioo b c) isPreconnected_Ioo (fun w hw => ⟨fun h' => ?_, fun h' => ?_⟩)
      ⟨m, ⟨hbm, hmc⟩, hm⟩ v ⟨h2, h3⟩ hv
    · exact absurd h'.2 (not_le.mpr hw.1)
    · exact absurd h'.1 (not_le.mpr hw.2)
  rcases le_or_gt v d with h4 | h4
  · exact hvJ (hJ2 (mem_image_of_mem f ⟨h3, h4⟩))
  · refine hpiece (Ioc d 1) isPreconnected_Ioc (fun w hw => ⟨fun h' => ?_, fun h' => ?_⟩)
      ⟨1, ⟨lt_of_lt_of_le h4 le_one', le_rfl⟩, h1⟩ v ⟨h4, le_one'⟩ hv
    · exact absurd h'.2 (not_le.mpr ((hbc.trans_le hcd).trans hw.1))
    · exact absurd h'.2 (not_le.mpr hw.1)

omit [T2Space T] in
theorem nonempty_of_mem_frontier {W : Set T} {x : T} (hx : x ∈ frontier W) : W.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hx

omit [T2Space T] in
/-- In Theorem 26, each open arc lies without the curve formed by the other two (were `Kc`
within `Ka + Kb`, Theorem 24 (1) would put the interior of `Kc + Ka` inside that of `Ka + Kb`). -/
theorem th26_aux (hopen : ∀ R ∈ reg, IsOpen R) (h21 : Th21Prop reg) {A B : T}
    {Ka Kb Kc Rab Rca : Set T} (hKa : TArc A B Ka) (hKc : TArc A B Kc)
    (hac : Ka ∩ Kc = {A, B}) (hbc : Kb ∩ Kc = {A, B}) (hRab : TInt reg (Ka ∪ Kb) Rab)
    (hRca : TInt reg (Kc ∪ Ka) Rca) (hdis : Disjoint Rab Rca) :
    Kc \ {A, B} ⊆ (closure Rab)ᶜ := by
  have hfr : Disjoint (Kc \ {A, B}) (frontier Rab) := by
    rw [hRab.2.2]
    refine disjoint_left.mpr fun x hx hx' => hx.2 ?_
    rcases hx' with h | h
    · rw [← hac]; exact ⟨h, hx.1⟩
    · rw [← hbc]; exact ⟨h, hx.1⟩
  by_cases hm : ((Kc \ {A, B}) ∩ Rab).Nonempty
  · have hsub := conn_sub_of_frontier hKc.isPreconnected_diff hfr hm
    have := th24_sub h21 hRab (Or.inl hKa.left_mem) (Or.inl hKa.right_mem) subset_union_left
      hsub hRca
    obtain ⟨y, hy⟩ := nonempty_of_mem_frontier (hRca.2.2 ▸ Or.inr hKa.left_mem : A ∈ frontier Rca)
    exact (disjoint_left.mp hdis (this hy) hy).elim
  · obtain ⟨x, hx⟩ := hKc.nonempty_diff
    refine conn_sub_ext_of_frontier hKc.isPreconnected_diff hfr ⟨x, hx, fun hcl => ?_⟩
    rw [closure_eq_union_frontier (hopen Rab hRab.2.1)] at hcl
    rcases hcl with h | h
    · exact hm ⟨x, hx, h⟩
    · exact disjoint_left.mp hfr hx h

/-- **Theorem 26**, topologically. -/
theorem th26 [LocallyConnectedSpace T] (hopen : ∀ R ∈ reg, IsOpen R)
    (hpc : ∀ R ∈ reg, IsPreconnected R) (h21 : Th21Prop reg) (harc : ArcConn T)
    (h8 : Ax8Prop reg) (hext : ∀ R ∈ reg, IsPreconnected (closure R)ᶜ)
    (hcpt : ∀ R ∈ reg, IsCompact (closure R)) (hnc : ¬ IsCompact (univ : Set T))
    {A B : T} {K₁ K₂ K₃ : Set T} (hK₁ : TArc A B K₁) (hK₂ : TArc A B K₂) (hK₃ : TArc A B K₃)
    (h12 : K₁ ∩ K₂ = {A, B}) (h13 : K₁ ∩ K₃ = {A, B}) (h23 : K₂ ∩ K₃ = {A, B})
    {R R₁ R₂ : Set T} (hR : TInt reg (K₁ ∪ K₃) R) (hR₁ : TInt reg (K₁ ∪ K₂) R₁)
    (hR₂ : TInt reg (K₂ ∪ K₃) R₂) :
    (R ∩ R₁).Nonempty ∨ (R ∩ R₂).Nonempty ∨ (R₁ ∩ R₂).Nonempty := by
  by_contra hcon
  simp only [not_or, not_nonempty_iff_eq_empty] at hcon
  obtain ⟨hRR₁, hRR₂, hR₁R₂⟩ := hcon
  have dRR₁ : Disjoint R R₁ := disjoint_iff_inter_eq_empty.mpr hRR₁
  have dRR₂ : Disjoint R R₂ := disjoint_iff_inter_eq_empty.mpr hRR₂
  have dR₁R₂ : Disjoint R₁ R₂ := disjoint_iff_inter_eq_empty.mpr hR₁R₂
  have hRo := hopen R hR.2.1
  have hR₁o := hopen R₁ hR₁.2.1
  have hR₂o := hopen R₂ hR₂.2.1
  have hfrR := hR.2.2
  have hfrR₁ := hR₁.2.2
  have hfrR₂ := hR₂.2.2
  -- each open arc is without the curve formed by the other two
  have hK₂ext : K₂ \ {A, B} ⊆ (closure R)ᶜ := th26_aux hopen h21 hK₁ hK₂ h12
    (by rw [inter_comm]; exact h23) hR (by rw [union_comm]; exact hR₁) dRR₁
  have hK₁ext : K₁ \ {A, B} ⊆ (closure R₂)ᶜ := th26_aux hopen h21 hK₂ hK₁
    (by rw [inter_comm]; exact h12) (by rw [inter_comm]; exact h13) hR₂ hR₁ dR₁R₂.symm
  have hK₃ext : K₃ \ {A, B} ⊆ (closure R₁)ᶜ := th26_aux hopen h21 hK₁ hK₃ h13 h23 hR₁
    (by rw [union_comm]; exact hR) dRR₁.symm
  have hAfr₂ : A ∈ frontier R₂ := hfrR₂ ▸ Or.inl hK₂.left_mem
  have hBfr₂ : B ∈ frontier R₂ := hfrR₂ ▸ Or.inl hK₂.right_mem
  have hAfr₁ : A ∈ frontier R₁ := hfrR₁ ▸ Or.inl hK₁.left_mem
  have hBfr₁ : B ∈ frontier R₁ := hfrR₁ ▸ Or.inl hK₁.right_mem
  have hR₁θ : ∀ x ∈ R₁, x ∉ K₁ ∪ K₃ := by
    intro x hx hx'
    have hxfr : x ∉ frontier R₁ := fun h => notMem_of_mem_frontier hR₁o h hx
    rcases hx' with h | h
    · exact hxfr (hfrR₁ ▸ Or.inl h)
    · by_cases hAB : x ∈ ({A, B} : Set T)
      · rcases hAB with rfl | rfl
        exacts [hxfr hAfr₁, hxfr hBfr₁]
      · exact hK₃ext ⟨h, hAB⟩ (subset_closure hx)
  have hR₂θ : ∀ x ∈ R₂, x ∉ K₁ ∪ K₃ := by
    intro x hx hx'
    have hxfr : x ∉ frontier R₂ := fun h => notMem_of_mem_frontier hR₂o h hx
    rcases hx' with h | h
    · by_cases hAB : x ∈ ({A, B} : Set T)
      · rcases hAB with rfl | rfl
        exacts [hxfr hAfr₂, hxfr hBfr₂]
      · exact hK₁ext ⟨h, hAB⟩ (subset_closure hx)
    · exact hxfr (hfrR₂ ▸ Or.inr h)
  -- the set `Y`
  set θ := K₁ ∪ K₂ ∪ K₃ with hθ
  have hθc : IsClosed θ := (hK₁.isClosed.union hK₂.isClosed).union hK₃.isClosed
  have hK₁cl : K₁ ⊆ closure R := fun x hx => frontier_subset_closure (hfrR ▸ Or.inl hx)
  have hK₃cl : K₃ ⊆ closure R := fun x hx => frontier_subset_closure (hfrR ▸ Or.inr hx)
  have hK₂cl : K₂ ⊆ closure R₁ := fun x hx => frontier_subset_closure (hfrR₁ ▸ Or.inr hx)
  set Y := (closure R)ᶜ ∩ (closure R₁)ᶜ ∩ (closure R₂)ᶜ with hY
  have hYo : IsOpen Y := (isClosed_closure.isOpen_compl.inter isClosed_closure.isOpen_compl).inter
    isClosed_closure.isOpen_compl
  have hYθ : ∀ x ∈ Y, x ∉ θ := by
    rintro x ⟨⟨h1, h2⟩, -⟩ ((h | h) | h)
    exacts [h1 (hK₁cl h), h2 (hK₂cl h), h1 (hK₃cl h)]
  have hdec : ∀ x, x ∉ θ → x ∈ R ∨ x ∈ R₁ ∨ x ∈ R₂ ∨ x ∈ Y := by
    intro x hx
    simp only [hθ, mem_union, not_or] at hx
    by_cases h1 : x ∈ closure R
    · rw [closure_eq_union_frontier hRo, hfrR] at h1
      rcases h1 with h | h | h
      exacts [Or.inl h, absurd h hx.1.1, absurd h hx.2]
    by_cases h2 : x ∈ closure R₁
    · rw [closure_eq_union_frontier hR₁o, hfrR₁] at h2
      rcases h2 with h | h | h
      exacts [Or.inr (Or.inl h), absurd h hx.1.1, absurd h hx.1.2]
    by_cases h3 : x ∈ closure R₂
    · rw [closure_eq_union_frontier hR₂o, hfrR₂] at h3
      rcases h3 with h | h | h
      exacts [Or.inr (Or.inr (Or.inl h)), absurd h hx.1.2, absurd h hx.2]
    exact Or.inr (Or.inr (Or.inr ⟨⟨h1, h2⟩, h3⟩))
  have hYconn : ∀ Z : Set T, IsPreconnected Z → (∀ x ∈ Z, x ∉ θ) → (Z ∩ Y).Nonempty →
      Z ⊆ Y := by
    intro Z hZ hZθ ⟨z, hzZ, hzY⟩
    have hd : ∀ W : Set T, frontier W ⊆ θ → Disjoint Z (frontier W) := fun W hW =>
      disjoint_left.mpr fun x hx hxW => hZθ x hx (hW hxW)
    have h1 := conn_sub_ext_of_frontier hZ (hd R (by
      rw [hfrR]; exact union_subset (subset_union_left.trans subset_union_left)
        subset_union_right)) ⟨z, hzZ, hzY.1.1⟩
    have h2 := conn_sub_ext_of_frontier hZ (hd R₁ (by rw [hfrR₁]; exact subset_union_left))
      ⟨z, hzZ, hzY.1.2⟩
    have h3 := conn_sub_ext_of_frontier hZ (hd R₂ (by
      rw [hfrR₂]; exact union_subset (subset_union_right.trans subset_union_left)
        subset_union_right)) ⟨z, hzZ, hzY.2⟩
    exact fun x hx => ⟨⟨h1 hx, h2 hx⟩, h3 hx⟩
  have hcover : ∀ W : Set T, IsCompact W → Y ⊆ W → False := by
    intro W hW hYW
    apply hnc
    have : (univ : Set T) ⊆ closure R ∪ closure R₁ ∪ closure R₂ ∪ W := by
      intro x _
      by_cases h1 : x ∈ closure R
      · exact Or.inl (Or.inl (Or.inl h1))
      by_cases h2 : x ∈ closure R₁
      · exact Or.inl (Or.inl (Or.inr h2))
      by_cases h3 : x ∈ closure R₂
      · exact Or.inl (Or.inr h3)
      exact Or.inr (hYW ⟨⟨h1, h2⟩, h3⟩)
    exact ((((hcpt R hR.2.1).union (hcpt R₁ hR₁.2.1)).union (hcpt R₂ hR₂.2.1)).union hW).of_isClosed_subset
      isClosed_univ this
  obtain ⟨P, hP⟩ : Y.Nonempty := by
    by_contra hne
    exact hcover ∅ isCompact_empty (by rw [not_nonempty_iff_eq_empty] at hne; rw [hne])
  -- the point `O` on `ADB`
  obtain ⟨D, hD⟩ := hK₂.nonempty_diff
  have hPD : P ≠ D := fun h => hYθ P hP (h ▸ Or.inl (Or.inr hD.1))
  obtain ⟨δ, hδE, hδ⟩ := harc _ isClosed_closure.isOpen_compl (hext R hR.2.1) P hP.1.1 D
    (hK₂ext hD) hPD
  obtain ⟨O, hOK₂, Γ₁, hΓ₁δ, hΓ₁, hΓ₁K⟩ := hδ.first_point hK₂.isClosed ⟨D, hδ.right_mem, hD.1⟩
    (fun h => hYθ P hP (Or.inl (Or.inr h)))
  have hOE : O ∈ (closure R)ᶜ := hδE (hΓ₁δ hΓ₁.right_mem)
  have hΓ₁Y : Γ₁ \ {O} ⊆ Y := by
    refine hYconn _ hΓ₁.isPreconnected_diff_right ?_ ⟨P, ⟨hΓ₁.left_mem, fun h => hYθ P hP
      (h ▸ Or.inl (Or.inr hOK₂))⟩, hP⟩
    intro x hx hxθ
    have hxE : x ∈ (closure R)ᶜ := hδE (hΓ₁δ hx.1)
    rcases hxθ with (h | h) | h
    · exact hxE (hK₁cl h)
    · exact hx.2 (by rw [← hΓ₁K]; exact ⟨hx.1, h⟩)
    · exact hxE (hK₃cl h)
  have hOclY : O ∈ closure Y := closure_mono hΓ₁Y hΓ₁.mem_closure_diff_right
  -- every point of `Y` reaches `ACB` through `Y`
  have hreach : ∀ Q ∈ Y, ∃ O₁ ∈ K₁, ∃ Γ : Set T, IsPreconnected Γ ∧ Q ∈ Γ ∧ O₁ ∈ Γ ∧
      Γ \ {O₁} ⊆ Y := by
    intro Q hQ
    obtain ⟨C, hC⟩ := hK₁.nonempty_diff
    have hQC : Q ≠ C := fun h => hYθ Q hQ (h ▸ Or.inl (Or.inl hC.1))
    obtain ⟨ε, hεE, hε⟩ := harc _ isClosed_closure.isOpen_compl (hext R₂ hR₂.2.1) Q hQ.2 C
      (hK₁ext hC) hQC
    obtain ⟨O₁, hO₁θ, Γ, hΓε, hΓ, hΓθ⟩ := hε.first_point hθc
      ⟨C, hε.right_mem, Or.inl (Or.inl hC.1)⟩ (hYθ Q hQ)
    have hO₁E : O₁ ∈ (closure R₂)ᶜ := hεE (hΓε hΓ.right_mem)
    have hO₁K₁ : O₁ ∈ K₁ := by
      rcases hO₁θ with (h | h) | h
      · exact h
      · exact absurd (frontier_subset_closure (hfrR₂ ▸ Or.inl h)) hO₁E
      · exact absurd (frontier_subset_closure (hfrR₂ ▸ Or.inr h)) hO₁E
    refine ⟨O₁, hO₁K₁, Γ, hΓ.isPreconnected, hΓ.left_mem, hΓ.right_mem, ?_⟩
    refine hYconn _ hΓ.isPreconnected_diff_right (fun x hx hxθ => hx.2 ?_)
      ⟨Q, ⟨hΓ.left_mem, fun h => hYθ Q hQ (h ▸ hO₁θ)⟩, hQ⟩
    rw [← hΓθ]; exact ⟨hx.1, hxθ⟩
  -- parametrize `ADB`; the crossing arcs
  obtain ⟨f, hf, hfr, hf0, hf1⟩ := hK₂.2
  have hinj := hf.injective
  have hfK : ∀ u, f u ∈ K₂ := fun u => hfr ▸ mem_range_self u
  obtain ⟨o, rfl⟩ : ∃ o, f o = O := by rw [← hfr] at hOK₂; exact hOK₂
  have hAcl : A ∈ closure R := hK₁cl hK₁.left_mem
  have hBcl : B ∈ closure R := hK₁cl hK₁.right_mem
  have ho0 : 0 < o := lt_of_le_of_ne nonneg' fun e => hOE (by rw [← e, hf0]; exact hAcl)
  have ho1 : o < 1 := lt_of_le_of_ne le_one' fun e => hOE (by rw [e, hf1]; exact hBcl)
  have hfθ : ∀ u, 0 < u → u < 1 → f u ∉ K₁ ∪ K₃ := by
    intro u h0 h1 h
    have hne : f u ∉ ({A, B} : Set T) := by
      rintro (e | e)
      · exact h0.ne' (hinj (e.trans hf0.symm))
      · exact h1.ne (hinj (e.trans hf1.symm))
    rcases h with h | h
    · exact hne (by rw [← h12]; exact ⟨h, hfK u⟩)
    · exact hne (by rw [← h23]; exact ⟨hfK u, h⟩)
  set N : unitInterval → unitInterval → Set T :=
    fun a b => (K₁ ∪ K₃ ∪ f '' Icc 0 a ∪ f '' Icc b 1)ᶜ with hN
  have hNo : ∀ a b, IsOpen (N a b) := fun a b =>
    (((hK₁.isClosed.union hK₃.isClosed).union (isCompact_Icc.image hf.continuous).isClosed).union
      (isCompact_Icc.image hf.continuous).isClosed).isOpen_compl
  have hNmem : ∀ a b q, a < q → q < b → f q ∈ N a b := by
    intro a b q haq hqb hmem
    have hq0 : 0 < q := lt_of_le_of_lt nonneg' haq
    have hq1 : q < 1 := lt_of_lt_of_le hqb le_one'
    rcases hmem with ((h | h) | h) | h
    · exact hfθ q hq0 hq1 (Or.inl h)
    · exact hfθ q hq0 hq1 (Or.inr h)
    · rw [hinj.mem_set_image] at h; exact absurd h.2 (not_le.mpr haq)
    · rw [hinj.mem_set_image] at h; exact absurd h.1 (not_le.mpr hqb)
  have hNpar : ∀ a b x, x ∈ K₂ ∪ (K₁ ∪ K₃) → x ∈ N a b → ∃ u, a < u ∧ u < b ∧ f u = x := by
    intro a b x hx hxN
    simp only [hN, mem_compl_iff, mem_union, not_or] at hxN
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hxN
    rcases hx with hx | hx | hx
    · rw [← hfr] at hx
      obtain ⟨u, rfl⟩ := hx
      exact ⟨u, not_le.mp fun h => hx3 (mem_image_of_mem f ⟨nonneg', h⟩),
        not_le.mp fun h => hx4 (mem_image_of_mem f ⟨h, le_one'⟩), rfl⟩
    · exact absurd hx hx1
    · exact absurd hx hx2
  have hNdis : ∀ (W : Set T) a b c, frontier W ⊆ K₂ ∪ (K₁ ∪ K₃) →
      Disjoint (frontier W ∩ N a b) (N b c) := by
    intro W a b c hW
    refine disjoint_left.mpr fun x ⟨hxW, hxN⟩ hxN' => ?_
    obtain ⟨u, -, hub, rfl⟩ := hNpar a b x (hW hxW) hxN
    exact hxN' (Or.inl (Or.inr (mem_image_of_mem f ⟨nonneg', hub.le⟩)))
  have hK₂fr₁ : K₂ ⊆ frontier R₁ := hfrR₁ ▸ subset_union_right
  have hK₂fr₂ : K₂ ⊆ frontier R₂ := hfrR₂ ▸ subset_union_left
  have hfr₁ : frontier R₁ ⊆ K₂ ∪ (K₁ ∪ K₃) := by
    rw [hfrR₁]; exact union_subset (subset_union_left.trans subset_union_right) subset_union_left
  have hfr₂ : frontier R₂ ⊆ K₂ ∪ (K₁ ∪ K₃) := by
    rw [hfrR₂]; exact union_subset subset_union_left (subset_union_right.trans subset_union_right)
  obtain ⟨q₁, hq₁0, hq₁o⟩ := exists_between ho0
  obtain ⟨q₂, hoq₂, hq₂1⟩ := exists_between ho1
  obtain ⟨G₁, ⟨hG₁fr, hG₁N⟩, H₁, ⟨hH₁fr, hH₁N⟩, α₁, hα₁, hα₁R⟩ := exists_cross harc hR₁o
    (hpc R₁ hR₁.2.1) (nonempty_of_mem_frontier hAfr₁) (hK₂fr₁ (hfK q₁)) (hK₂fr₁ (hfK q₂))
    ((hNo 0 o).mem_nhds (hNmem 0 o q₁ hq₁0 hq₁o)) ((hNo o 1).mem_nhds (hNmem o 1 q₂ hoq₂ hq₂1))
    (hNdis R₁ 0 o 1 hfr₁)
  obtain ⟨g₁, hg₁0, hg₁o, rfl⟩ := hNpar 0 o G₁ (hfr₁ hG₁fr) hG₁N
  obtain ⟨h₁, hoh₁, hh₁1, rfl⟩ := hNpar o 1 H₁ (hfr₁ hH₁fr) hH₁N
  obtain ⟨q₃, hg₁q₃, hq₃o⟩ := exists_between hg₁o
  obtain ⟨q₄, hoq₄, hq₄h₁⟩ := exists_between hoh₁
  obtain ⟨G₂, ⟨hG₂fr, hG₂N⟩, H₂, ⟨hH₂fr, hH₂N⟩, α₂, hα₂, hα₂R⟩ := exists_cross harc hR₂o
    (hpc R₂ hR₂.2.1) (nonempty_of_mem_frontier hAfr₂) (hK₂fr₂ (hfK q₃)) (hK₂fr₂ (hfK q₄))
    ((hNo g₁ o).mem_nhds (hNmem g₁ o q₃ hg₁q₃ hq₃o))
    ((hNo o h₁).mem_nhds (hNmem o h₁ q₄ hoq₄ hq₄h₁)) (hNdis R₂ g₁ o h₁ hfr₂)
  obtain ⟨g₂, hg₁g₂, hg₂o, rfl⟩ := hNpar g₁ o G₂ (hfr₂ hG₂fr) hG₂N
  obtain ⟨h₂, hoh₂, hh₂h₁, rfl⟩ := hNpar o h₁ H₂ (hfr₂ hH₂fr) hH₂N
  have hα₁X : ∀ x ∈ α₁, x ∈ range f → x = f g₁ ∨ x = f h₁ := by
    intro x hx hxX
    by_contra hne
    push_neg at hne
    exact notMem_of_mem_frontier hR₁o (hK₂fr₁ (hfr ▸ hxX)) (hα₁R ⟨hx, by simp [hne.1, hne.2]⟩)
  have hα₂X : ∀ x ∈ α₂, x ∈ range f → x = f g₂ ∨ x = f h₂ := by
    intro x hx hxX
    by_contra hne
    push_neg at hne
    exact notMem_of_mem_frontier hR₂o (hK₂fr₂ (hfr ▸ hxX)) (hα₂R ⟨hx, by simp [hne.1, hne.2]⟩)
  have hα₁sub : ∀ x ∈ α₁, x ∈ R₁ ∨ x = f g₁ ∨ x = f h₁ := by
    intro x hx
    by_cases hx' : x = f g₁ ∨ x = f h₁
    · exact Or.inr hx'
    · push_neg at hx'
      exact Or.inl (hα₁R ⟨hx, by simp [hx'.1, hx'.2]⟩)
  have hα₂sub : ∀ x ∈ α₂, x ∈ R₂ ∨ x = f g₂ ∨ x = f h₂ := by
    intro x hx
    by_cases hx' : x = f g₂ ∨ x = f h₂
    · exact Or.inr hx'
    · push_neg at hx'
      exact Or.inl (hα₂R ⟨hx, by simp [hx'.1, hx'.2]⟩)
  have hα₂₁ : Disjoint α₂ α₁ := by
    refine disjoint_left.mpr fun x hx2 hx1 => ?_
    rcases hα₂sub x hx2 with h2 | rfl | rfl
    · rcases hα₁sub x hx1 with h1 | rfl | rfl
      · exact disjoint_left.mp dR₁R₂ h1 h2
      · exact notMem_of_mem_frontier hR₂o (hK₂fr₂ (hfK g₁)) h2
      · exact notMem_of_mem_frontier hR₂o (hK₂fr₂ (hfK h₁)) h2
    · rcases hα₁X _ hx1 (mem_range_self _) with e | e <;> have e' := hinj e
      exacts [hg₁g₂.ne' e', (hg₂o.trans hoh₁).ne e']
    · rcases hα₁X _ hx1 (mem_range_self _) with e | e <;> have e' := hinj e
      exacts [(hg₁o.trans hoh₂).ne' e', hh₂h₁.ne e']
  obtain ⟨hJb, hJbf⟩ := tscc_theta hf hα₂ hα₁ hg₁g₂ (hg₂o.trans hoh₂) hh₂h₁ hα₂X hα₁X hα₂₁
  set Jb := α₂ ∪ f '' Icc h₂ h₁ ∪ (f '' Icc g₁ g₂ ∪ α₁) with hJbdef
  obtain ⟨Rb, hRbreg, hRbJ⟩ := h8 Jb hJb
  have hRbo := hopen Rb hRbreg
  -- `J̄` lies in `R₁' + R₂'` and misses `ACB + AFB`
  have hJbcl : Jb ⊆ closure R₁ ∪ closure R₂ := by
    rintro x ((hx | ⟨v, -, rfl⟩) | (⟨v, -, rfl⟩ | hx))
    · rcases hα₂sub x hx with h' | rfl | rfl
      exacts [Or.inr (subset_closure h'), Or.inl (hK₂cl (hfK _)), Or.inl (hK₂cl (hfK _))]
    · exact Or.inl (hK₂cl (hfK v))
    · exact Or.inl (hK₂cl (hfK v))
    · rcases hα₁sub x hx with h' | rfl | rfl
      exacts [Or.inl (subset_closure h'), Or.inl (hK₂cl (hfK _)), Or.inl (hK₂cl (hfK _))]
  have hJbK : Disjoint Jb (K₁ ∪ K₃) := by
    refine disjoint_left.mpr ?_
    rintro x ((hx | ⟨v, hv, rfl⟩) | (⟨v, hv, rfl⟩ | hx))
    · rcases hα₂sub x hx with h' | rfl | rfl
      · exact hR₂θ x h'
      · exact hfθ g₂ (hg₁0.trans hg₁g₂) (hg₂o.trans ho1)
      · exact hfθ h₂ (ho0.trans hoh₂) (hh₂h₁.trans hh₁1)
    · exact hfθ v ((ho0.trans hoh₂).trans_le hv.1) (hv.2.trans_lt hh₁1)
    · exact hfθ v (hg₁0.trans_le hv.1) (hv.2.trans_lt hg₂o |>.trans ho1)
    · rcases hα₁sub x hx with h' | rfl | rfl
      · exact hR₁θ x h'
      · exact hfθ g₁ hg₁0 (hg₁o.trans ho1)
      · exact hfθ h₁ (ho0.trans hoh₁) hh₁1
  have hYJb : Disjoint Y Jb := disjoint_left.mpr fun x hxY hxJ =>
    (hJbcl hxJ).elim hxY.1.2 hxY.2
  -- if `R̄` met `ACB + AFB` it would contain `Y`
  have hK13 : IsPreconnected (K₁ ∪ K₃) :=
    hK₁.isPreconnected.union A hK₁.left_mem hK₃.left_mem hK₃.isPreconnected
  have hK13fr : Disjoint (K₁ ∪ K₃) (frontier Rb) := hRbJ ▸ hJbK.symm
  have hnoK : ∀ x ∈ K₁ ∪ K₃, x ∉ Rb := by
    intro x hx hxRb
    have hsub := conn_sub_of_frontier hK13 hK13fr ⟨x, hx, hxRb⟩
    refine hcover _ (hcpt Rb hRbreg) fun Q hQ => subset_closure ?_
    obtain ⟨O₁, hO₁, Γ, hΓ, hQΓ, hO₁Γ, hΓY⟩ := hreach Q hQ
    have hΓfr : Disjoint Γ (frontier Rb) := by
      rw [hRbJ]
      refine disjoint_left.mpr fun y hy hyJ => ?_
      by_cases hyO : y = O₁
      · exact disjoint_left.mp hJbK hyJ (hyO ▸ Or.inl hO₁)
      · exact disjoint_left.mp hYJb (hΓY ⟨hy, hyO⟩) hyJ
    exact conn_sub_of_frontier hΓ hΓfr ⟨O₁, hO₁Γ, hsub (Or.inl hO₁)⟩ hQΓ
  -- `R̄` misses `Y`
  have hnoY : ∀ y ∈ Y, y ∉ Rb := by
    intro y hy hyRb
    obtain ⟨O₁, hO₁, Γ, hΓ, hyΓ, hO₁Γ, hΓY⟩ := hreach y hy
    have hΓfr : Disjoint Γ (frontier Rb) := by
      rw [hRbJ]
      refine disjoint_left.mpr fun z hz hzJ => ?_
      by_cases hzO : z = O₁
      · exact disjoint_left.mp hJbK hzJ (hzO ▸ Or.inl hO₁)
      · exact disjoint_left.mp hYJb (hΓY ⟨hz, hzO⟩) hzJ
    exact hnoK O₁ (Or.inl hO₁) (conn_sub_of_frontier hΓ hΓfr ⟨y, hyΓ, hyRb⟩ hO₁Γ)
  -- `O`, `A`, `B` are without `J̄`; `R̄` misses `ADB`
  have hclRb : closure Rb = Rb ∪ Jb := by rw [closure_eq_union_frontier hRbo, hRbJ]
  have hORb : f o ∉ closure Rb := by
    rw [hclRb]
    rintro (h | h)
    · obtain ⟨y, hyRb, hyY⟩ := mem_closure_iff_nhds.mp hOclY Rb (hRbo.mem_nhds h)
      exact hnoY y hyY hyRb
    · rcases hJbf o h with h' | h'
      · exact absurd h'.2 (not_le.mpr hg₂o)
      · exact absurd h'.1 (not_le.mpr hoh₂)
  have hARb : f 0 ∉ closure Rb := by
    rw [hclRb, hf0]
    rintro (h | h)
    · exact hnoK A (Or.inl hK₁.left_mem) h
    · exact disjoint_left.mp hJbK h (Or.inl hK₁.left_mem)
  have hBRb : f 1 ∉ closure Rb := by
    rw [hclRb, hf1]
    rintro (h | h)
    · exact hnoK B (Or.inl hK₁.right_mem) h
    · exact disjoint_left.mp hJbK h (Or.inl hK₁.right_mem)
  have hK₂Rb := image_notMem_of_pieces hf hRbo hRbJ hg₁g₂.le (hg₂o.trans hoh₂) hh₂h₁.le hJbf
    (fun x hx => Or.inr (Or.inl hx)) (fun x hx => Or.inl (Or.inr hx)) hARb hg₂o hoh₂ hORb hBRb
  -- `R̄ ⊆ R + R₁ + R₂` and meets `R₁` and `R₂`: Axiom 2 fails
  have hRbsub : Rb ⊆ R₁ ∪ (R ∪ R₂) := by
    intro x hx
    have hxθ : x ∉ θ := by
      rintro ((h | h) | h)
      · exact hnoK x (Or.inl h) hx
      · rw [← hfr] at h; obtain ⟨u, rfl⟩ := h; exact hK₂Rb u hx
      · exact hnoK x (Or.inr h) hx
    rcases hdec x hxθ with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact absurd hx (hnoY x h)
  obtain ⟨P₁, hP₁⟩ := hα₁.nonempty_diff
  obtain ⟨P₂, hP₂⟩ := hα₂.nonempty_diff
  have hP₁cl : P₁ ∈ closure Rb := frontier_subset_closure (hRbJ ▸ Or.inr (Or.inr hP₁.1))
  have hP₂cl : P₂ ∈ closure Rb := frontier_subset_closure (hRbJ ▸ Or.inl (Or.inl hP₂.1))
  obtain ⟨y₁, hy₁R₁, hy₁Rb⟩ := mem_closure_iff_nhds.mp hP₁cl R₁ (hR₁o.mem_nhds (hα₁R hP₁))
  obtain ⟨y₂, hy₂R₂, hy₂Rb⟩ := mem_closure_iff_nhds.mp hP₂cl R₂ (hR₂o.mem_nhds (hα₂R hP₂))
  have hdis' : Disjoint R₁ (R ∪ R₂) := disjoint_union_right.mpr ⟨dRR₁.symm, dR₁R₂⟩
  have := (hpc Rb hRbreg).subset_left_of_subset_union hR₁o (hRo.union hR₂o) hdis' hRbsub
    ⟨y₁, hy₁Rb, hy₁R₁⟩
  exact disjoint_left.mp dR₁R₂ (this hy₂Rb) hy₂R₂

end Gen

end HPC.Moore
