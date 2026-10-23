import HPC.Hagopian.H76ChainInter

/-!
# Batch 170, item C: "follows" for crossing components (commission 170 §1.C)

`T9_pieces_aux` is the first half of `T9_aux` (`H76T9.lean`) with Property 1's link condition
`h[piece (j + 1)] ⊆ L j` kept for the homeomorphism `h` it produces. `follows_crossing_aux`: for a
connected `B` over the thin strip whose closure meets both side edges, `Cl B ⊆ h[E]`, `h⁻¹[Cl B]` meets
a layer of `E` at a parameter `≤ 4/11` and one at a parameter `≥ 7/11` (link control at the edges,
then the link condition), so by `layerSet_Ioo_subset` it contains `k⁻¹((4/11, 7/11))`, i.e.
`Cl B ⊇ h[k⁻¹((4/11, 7/11))]`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Follows

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- T9's homeomorphism with the link condition of Property 1 kept. -/
theorem T9_pieces_aux (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁) {L : Fin 11 → Set Pt}
    (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {O : Set Pt}
    (hO : ∀ x : M, (x : Pt) ∈ closure O → ∃ j : Fin 11, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧ (x : Pt) ∈ L j)
    {B : Set M} (hBc : IsPreconnected B) (hBO : toPt B ⊆ O) {y : M} (hyB : y ∈ B) {i : Fin 11}
    (hi1 : 1 ≤ (i : ℕ)) (hi9 : (i : ℕ) ≤ 9) (hyL : (y : Pt) ∈ L i) :
    ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ closure B ⊆ h '' E ∧
      Fold.Q78.IsContinuum (h ⁻¹' closure B) ∧ h ⁻¹' closure B ⊆ E ∧
      ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  obtain ⟨h, hh, hyE, hpieces⟩ := hP1 y i hi1 hi9 hyL
  obtain ⟨b, hbE, hb⟩ := exists_image_map h hE
  have hclB : Fold.Q78.IsContinuum (closure B) :=
    ⟨isClosed_closure.isCompact, ⟨y, subset_closure hyB⟩, hBc.closure⟩
  have hmid : ∀ x ∈ closure B, ∃ j : Fin 11, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧ (x : Pt) ∈ L j := by
    intro x hx
    apply hO
    exact closure_mono hBO (image_closure_subset_closure_image continuous_subtype_val ⟨x, hx, rfl⟩)
  have havoid : Disjoint (closure B) (layer b 0 ∪ layer b 1) := by
    rw [disjoint_left]
    intro x hx hxe
    have hxe' : x ∈ h '' (layer k 0 ∪ layer k 1) := by
      rcases hxe with h0 | h1
      · have : x ∈ layerSet b {0} := h0
        rw [hb] at this
        exact image_mono subset_union_left this
      · have : x ∈ layerSet b {1} := h1
        rw [hb] at this
        exact image_mono subset_union_right this
    obtain ⟨e, he0, rfl⟩ := hxe'
    obtain ⟨j, hj1, hj9, hxj⟩ := hmid _ hx
    obtain ⟨_, ⟨m, hm, rfl⟩, hxm⟩ :=
      mem_thickening_iff.1 (chainG_subset_thickening k ε₁ j (hLG j hxj))
    have h1 := he.ends e he0 m (piece_subset_middle k hj1 hj9 hm)
    have h2 := hh e
    rw [Subtype.dist_eq] at h1 h2
    have := dist_triangle (e : Pt) ((h e : M) : Pt) (m : Pt)
    have := he.pos
    linarith
  have hhE : Fold.Q78.IsContinuum (h '' E) := by
    obtain ⟨⟨a₀, b₀, hab⟩, -, -⟩ := hbE
    exact hab.1
  have hsub : closure B ⊆ h '' E :=
    subset_of_meets_avoids hHU hAT hhE hbE.2.1 hclB ⟨y, hyE, subset_closure hyB⟩ havoid
  have hpre : h ⁻¹' closure B ⊆ E := by
    intro x hx
    obtain ⟨e, he, hex⟩ := hsub hx
    rw [← h.injective hex]
    exact he
  have hpreC : Fold.Q78.IsContinuum (h ⁻¹' closure B) := by
    rw [← h.image_symm]
    exact isContinuum_homeo_image h.symm hclB
  exact ⟨h, hh, hsub, hpreC, hpre, hpieces⟩

/-- **C. "Follows" for crossing components.** There is a height `c > 0` such that for every
connected `B ⊆ M` over `F[[3/22, 19/22] × (0, c]]` whose closure meets both side edges
(`π⁻¹F[{3/22} × (0, c]]`, `π⁻¹F[{19/22} × (0, c]]`): `Cl B` misses `E`, and for an
`ε₁`-homeomorphism `h` with Property 1's link condition `h[piece (j + 1)] ⊆ Lⱼ`,
`Cl B ⊆ h[E]`, `h⁻¹[Cl B] ⊆ E` is essential to `R(E)`, and `Cl B ⊇ h[k⁻¹((4/11, 7/11))]`. -/
theorem follows_crossing_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      Disjoint (closure B) E ∧ ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ closure B ⊆ h '' E ∧
        h ⁻¹' closure B ⊆ E ∧ IsEssential k (h ⁻¹' closure B) ∧
        (∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) ∧
        h '' layerSet k {t | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} ⊆ closure B := by
  obtain ⟨c₈, hc₈, hc₈1, -, hD⟩ :=
    hagopian76_T8 hX hi hE he hend hπ hπS hγπ hF hLch.isOpen hEL hLG
  set η := min ε₁ (1 / 100) with hηdef
  have hη : 0 < η := lt_min he.pos (by norm_num)
  have hη1 : η ≤ 1 / 100 := min_le_right _ _
  obtain ⟨cl, hcl, hcl1, -, hlc⟩ := hagopian76_link_control hX hi hE he hend hπ hπS hγπ hF
    hLch.isOpen hEL hLG hη (min_le_left _ _)
  have hm8 : min c₈ cl ≤ c₈ := min_le_left _ _
  have hml : min c₈ cl ≤ cl := min_le_right _ _
  refine ⟨min c₈ cl, lt_min hc₈ hcl, hm8.trans hc₈1,
    fun B hB hBs ⟨xL, hxLB, hxL⟩ ⟨xR, hxRB, hxR⟩ => ?_⟩
  have hlink : ∀ x : M, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 (min c₈ cl)) →
      ∃ z ∈ Icc (3 / 22) (19 / 22) ×ˢ Icc 0 cl, π (x : Pt) = F z ∧ (∃ j : Fin 11, (x : Pt) ∈ L j) ∧
        ∀ j : Fin 11, (x : Pt) ∈ L j → 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧
          ((j : ℝ) - 1) / 11 - η < z.1 ∧ z.1 < ((j : ℝ) + 2) / 11 + η := fun x hx =>
    hlc x (image_mono (prod_mono subset_rfl
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hml))) hx)
  have hdis : Disjoint (closure B) E :=
    closure_disjoint_E_of_above hX hi hE hπ.continuous hγπ hF
      (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (19 / 22 : ℝ) < 1) (hm8.trans hc₈1) hB hBs
  have hBne : B.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hxLB
    exact hxLB
  obtain ⟨y, hyB⟩ := hBne
  obtain ⟨zy, -, -, ⟨i, hyi⟩, hij⟩ := hlink y (hBs y hyB)
  obtain ⟨hi1, hi9, -, -⟩ := hij i hyi
  set O : Set Pt := π ⁻¹' (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 (min c₈ cl))) with hOd
  have hOR : O ⊆ π ⁻¹' (F '' (Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c₈)) :=
    preimage_mono (image_mono (Set.prod_mono subset_rfl
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hm8))))
  have hBO : toPt B ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩; exact hBs x hx
  obtain ⟨h, hmove, hBh, hGc, hBE, hpieces⟩ :=
    T9_pieces_aux hX hi hE he hLG hP1 (fun x hx => hD O hOR x hx) hB hBO hyB hi1 hi9 hyi
  have hR : ∀ {z : ℝ × ℝ}, z ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 cl →
      z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun hz =>
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  -- the left point lies in a link of index `≤ 2`
  obtain ⟨zL, hzL, hFzL⟩ := hxL
  have hzL1 : zL.1 = 3 / 22 := hzL.1
  have hzLs : zL ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 cl :=
    ⟨⟨by rw [hzL1], by rw [hzL1]; norm_num⟩, hzL.2.1.le, hzL.2.2.trans hml⟩
  obtain ⟨z', hz', hπz', ⟨jL, hjL⟩, hjLc⟩ :=
    hlink xL ⟨zL, ⟨hzLs.1, hzL.2⟩, hFzL⟩
  have hzz : z' = zL := collar_injOn hF (hR hz') (hR hzLs) (hπz'.symm.trans hFzL.symm)
  obtain ⟨-, -, hjL1, -⟩ := hjLc jL hjL
  rw [hzz, hzL1] at hjL1
  have hjL2 : (jL : ℕ) < 3 := by
    have : ((jL : ℕ) : ℝ) < 3 := by linarith
    exact_mod_cast this
  -- the right point lies in a link of index `≥ 8`
  obtain ⟨zR, hzR, hFzR⟩ := hxR
  have hzR1 : zR.1 = 19 / 22 := hzR.1
  have hzRs : zR ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 cl :=
    ⟨⟨by rw [hzR1]; norm_num, by rw [hzR1]⟩, hzR.2.1.le, hzR.2.2.trans hml⟩
  obtain ⟨z'', hz'', hπz'', ⟨jR, hjR⟩, hjRc⟩ :=
    hlink xR ⟨zR, ⟨hzRs.1, hzR.2⟩, hFzR⟩
  have hzz' : z'' = zR := collar_injOn hF (hR hz'') (hR hzRs) (hπz''.symm.trans hFzR.symm)
  obtain ⟨-, -, -, hjR1⟩ := hjRc jR hjR
  rw [hzz', hzR1] at hjR1
  have hjR2 : 7 < (jR : ℕ) := by
    have : (7 : ℝ) < ((jR : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  -- the parameters of the preimages
  have hin : ∀ (f : E) (m : Fin 11), k f ∈ elev m → (((h f : M)) : Pt) ∈ L m := fun f m hf =>
    hpieces m ⟨h f, ⟨f, by rw [piece_succ]; exact ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨e₁, he₁E, rfl⟩ := hBh hxLB
  obtain ⟨e₂, he₂E, rfl⟩ := hBh hxRB
  set f₁ : E := ⟨e₁, he₁E⟩
  set f₂ : E := ⟨e₂, he₂E⟩
  obtain ⟨m₁, hm₁⟩ := exists_elev (k f₁)
  obtain ⟨m₂, hm₂⟩ := exists_elev (k f₂)
  have hmm₁ := ((hLch.meets m₁ jL).1 ⟨_, hin f₁ m₁ hm₁, hjL⟩).1
  have hmm₂ := ((hLch.meets m₂ jR).1 ⟨_, hin f₂ m₂ hm₂, hjR⟩).2
  have hk₁ : (k f₁ : ℝ) ≤ 4 / 11 := by
    have h1 : ((m₁ : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show (m₁ : ℕ) ≤ 3 by omega)
    have := hm₁.2
    linarith
  have hk₂ : 7 / 11 ≤ (k f₂ : ℝ) := by
    have h1 : (7 : ℝ) ≤ ((m₂ : ℕ) : ℝ) := by exact_mod_cast (show 7 ≤ (m₂ : ℕ) by omega)
    have := hm₂.1
    linarith
  set G : Set M := h ⁻¹' closure B with hGdef
  have he₁G : e₁ ∈ G := hxLB
  have he₂G : e₂ ∈ G := hxRB
  have hIoo : layerSet k (Ioo (k f₁) (k f₂)) ⊆ G :=
    layerSet_Ioo_subset hE hBE hGc ⟨e₁, he₁G, f₁, rfl, rfl⟩ ⟨e₂, he₂G, f₂, rfl, rfl⟩
  refine ⟨hdis, h, hmove, hBh, hBE, ?_, hpieces, ?_⟩
  · refine ⟨hBE.trans (subset_Rset hE), hGc, E, k, subset_rfl, hE, Or.inl rfl,
      k f₁, k f₂, fun heq => ?_, ⟨e₁, he₁G, f₁, rfl, rfl⟩, ⟨e₂, he₂G, f₂, rfl, rfl⟩⟩
    have : (k f₁ : ℝ) = k f₂ := congrArg Subtype.val heq
    linarith
  · rintro _ ⟨x, ⟨f, hf, rfl⟩, rfl⟩
    have hfG : (f : M) ∈ G :=
      hIoo ⟨f, ⟨show (k f₁ : ℝ) < k f by linarith [hf.1],
        show (k f : ℝ) < k f₂ by linarith [hf.2]⟩, rfl⟩
    exact hfG

end Follows

end HPC.Hagopian
