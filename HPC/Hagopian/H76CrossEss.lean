import HPC.Hagopian.H76K0Dense

/-!
# Batch 167, item B (part): crossing continua over the thin strip are essential

`crossing_essential_aux`: a connected subset `B` of `M` lying over the thin strip of T8/T9 whose
closure meets both side edges (abscissae `3/22`, `19/22`) is carried by T9 into a translate `h[E]`,
and `h⁻¹[Cl B]` is essential to `R(E)`. This is the form in which Hagopian's T12 (2) ("the closure of
the `p`-component `C` of `M ∩ π⁻¹[D]` is essential to `h[R(E)]`") is available, with the
homeomorphism of T9 in place of the `h` with `h(x) = p`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section CrossEss

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Crossing continua over the thin strip are essential.** -/
theorem crossing_essential_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
        h ⁻¹' closure B ⊆ E ∧ IsEssential k (h ⁻¹' closure B) := by
  obtain ⟨c₉, hc₉, hc₉1, hT9⟩ :=
    hagopian76_T9_full hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  set η := min ε₁ (1 / 100) with hηdef
  have hη : 0 < η := lt_min he.pos (by norm_num)
  have hη1 : η ≤ 1 / 100 := min_le_right _ _
  obtain ⟨cl, hcl, hcl1, -, hlc⟩ := hagopian76_link_control hX hi hE he hend hπ hπS hγπ hF
    hLch.isOpen hEL hLG hη (min_le_left _ _)
  have hm9 : min c₉ cl ≤ c₉ := min_le_left _ _
  have hml : min c₉ cl ≤ cl := min_le_right _ _
  refine ⟨min c₉ cl, lt_min hc₉ hcl, hm9.trans hc₉1,
    fun B hB hBs ⟨xL, hxLB, hxL⟩ ⟨xR, hxRB, hxR⟩ => ?_⟩
  have hBs9 : ∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₉) := fun x hx =>
    image_mono (prod_mono subset_rfl (Ioc_subset_Ioc le_rfl hm9)) (hBs x hx)
  have hlink : ∀ x : M, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 (min c₉ cl)) →
      ∃ z ∈ Icc (3 / 22) (19 / 22) ×ˢ Icc 0 cl, π (x : Pt) = F z ∧ (∃ j : Fin 11, (x : Pt) ∈ L j) ∧
        ∀ j : Fin 11, (x : Pt) ∈ L j → 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧
          ((j : ℝ) - 1) / 11 - η < z.1 ∧ z.1 < ((j : ℝ) + 2) / 11 + η := fun x hx =>
    hlc x (image_mono (prod_mono subset_rfl
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hml))) hx)
  have hBne : B.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hxLB
    exact hxLB
  obtain ⟨y, hyB⟩ := hBne
  obtain ⟨zy, -, -, ⟨i, hi⟩, hij⟩ := hlink y (hBs y hyB)
  obtain ⟨hi1, hi9, -, -⟩ := hij i hi
  obtain ⟨hdis, h, hmove, hBh, -, hBE, hess⟩ := hT9 B hB hBs9 y hyB i hi1 hi9 hi
  refine ⟨hdis, h, hmove, hBh, hBE, ?_⟩
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
  exact hess jL jR (by omega) ⟨_, ⟨xL, hxLB, rfl⟩, hjL⟩ ⟨_, ⟨xR, hxRB, rfl⟩, hjR⟩

/-- **T12 (1) and (2)** (commission 167 §2.B), with the essential translate supplied by T9: for `D`
built at a height `c ≤ c₉` over `[3/22, 19/22]` and `t₀ ∈ (3/22, 19/22)`, there is `x` in the layer
over `t₀` such that every `ε`-homeomorphism `h` of Lemma T′/Lemma T (with `h(x) = p` on the vertical
over `t₀`, off `E`) has a crossing `p`-component `C ⊇ h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]`, and
`Cl C ⊆ h′[E]` with `h′⁻¹[Cl C]` essential to `R(E)` for an `ε₁`-homeomorphism `h′`. -/
theorem T12_parts12_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c₉ > 0, c₉ ≤ 1 ∧ ∀ (c r₂ s₂ : ℝ) (I₂ : Set Pt) (D' : Set (ℝ × ℝ)), c ≤ c₉ →
      (∃ c' > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c') 0)) (π '' M)) →
      TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂) (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) →
      I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c) →
      D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c →
      frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪
        Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
        ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂ →
      IsOpen (F '' D') →
      frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂) →
      ∀ t₀ ∈ Ioo (3 / 22 : ℝ) (19 / 22),
      ∃ x : E, (k x : ℝ) = t₀ ∧ ∃ ζ > 0, ∀ ε > 0, ∃ h : M ≃ₜ M, (∀ v, dist (h v) v < ε) ∧
        dist (h (x : M) : Pt) ((x : M) : Pt) < ε ∧
        (∃ u ∈ Ioo 0 ε, π (h (x : M) : Pt) = F (t₀, u)) ∧ h (x : M) ∉ E ∧
        toPt (h '' layerSet k {t | 3 / 22 + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 19 / 22 - ζ / 2}) ⊆
          connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt) ∧
        (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
          π ⁻¹' (F '' (({3 / 22} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
        (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
          π ⁻¹' (F '' (({19 / 22} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty ∧
        ∃ h' : M ≃ₜ M, (∀ v, dist v (h' v) < ε₁) ∧
          closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ⊆
            toPt (h' '' E) ∧
          IsEssential k (h' ⁻¹' (Subtype.val ⁻¹'
            closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)))) := by
  obtain ⟨c₉, hc₉, hc₉1, hess⟩ :=
    crossing_essential_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨c₉, hc₉, hc₉1, fun c r₂ s₂ I₂ D' hcc hbelow hI hIR hDR hDf hFDo hFDf t₀ ht₀ => ?_⟩
  have hc1 : c ≤ 1 := hcc.trans hc₉1
  obtain ⟨x, hkx, ζ, hζ, H⟩ := T12_crossing_aux hX hi hE hπ.continuous hπS hγπ hF
    (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (3 / 22 : ℝ) < 19 / 22)
    (by norm_num : (19 / 22 : ℝ) < 1) hc1 hbelow hI hIR hDR hDf hFDo hFDf ht₀
  refine ⟨x, hkx, ζ, hζ, fun ε hε => ?_⟩
  obtain ⟨h, h1, h2, h3, h4, hPC, hL, hR⟩ := H ε hε
  refine ⟨h, h1, h2, h3, h4, hPC, hL, hR, ?_⟩
  set C := connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt) with hCdef
  have hCM : C ⊆ M := fun z hz => (connectedComponentIn_subset _ _ hz).1
  have hMcl : IsClosed M := (isCompact_iff_compactSpace.2 ‹CompactSpace M›).isClosed
  have hclM : closure C ⊆ M := closure_minimal hCM hMcl
  set B : Set M := Subtype.val ⁻¹' C with hBdef
  have himg : Subtype.val '' B = C := by
    rw [hBdef, Subtype.image_preimage_coe, inter_eq_right.2 hCM]
  have hBpre : IsPreconnected B := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, himg]
    exact isPreconnected_connectedComponentIn
  have hclB : closure B = Subtype.val ⁻¹' closure C := by
    ext m
    rw [closure_subtype, himg]
    rfl
  have hr₂c : r₂ ≤ c := hI.left_mem.1.2.2
  have hs₂c : s₂ ≤ c := hI.right_mem.1.2.2
  have hBs : ∀ y ∈ B, π (y : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₉) := by
    intro y hy
    obtain ⟨d, hd, hFd⟩ := (connectedComponentIn_subset _ _ (show (y : Pt) ∈ C from hy)).2
    obtain ⟨⟨hd1, hd2⟩, hd3, hd4⟩ := hDR hd
    exact ⟨d, ⟨⟨hd1.le, hd2.le⟩, hd3, by linarith⟩, hFd⟩
  have hside : ∀ (e r : ℝ), r ≤ c →
      (closure C ∩ π ⁻¹' (F '' (({e} : Set ℝ) ×ˢ Ioo 0 r))).Nonempty →
      ∃ y ∈ closure B, π (y : Pt) ∈ F '' (({e} : Set ℝ) ×ˢ Ioc 0 c₉) := by
    rintro e r hr ⟨q, hqC, w, hw, hFw⟩
    refine ⟨⟨q, hclM hqC⟩, by rw [hclB]; exact hqC, w, ⟨hw.1, hw.2.1, by linarith [hw.2.2]⟩, hFw⟩
  obtain ⟨-, h', hmove', hBh, -, hessB⟩ :=
    hess B hBpre hBs (hside _ _ hr₂c hL) (hside _ _ hs₂c hR)
  refine ⟨h', hmove', fun q hq => ⟨⟨q, hclM hq⟩, hBh (by rw [hclB]; exact hq), rfl⟩, ?_⟩
  rw [← hclB]
  exact hessB

end CrossEss

end HPC.Hagopian
