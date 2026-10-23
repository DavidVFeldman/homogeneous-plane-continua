import HPC.Hagopian.H76Defs

/-!
# Batch 156, item I: the consequences of Hagopian 1976, Theorem 1

Each result takes `h1 : Hagopian76Thm1`.

* `isIndecomposable_of_h1_sub`: applied to a homogeneous indecomposable subcontinuum `Y` of `M`
  (moved into the plane as `N = Y`), `Hagopian76Thm1` makes every subcontinuum of `Y`
  indecomposable.
* `hagopian76_theorem2_aux`: a decomposable homogeneous plane continuum has two complementary
  domains (`jones55_two_domains'`), so a nonseparating one is indecomposable; Gordh 1975 and
  Jones 1951 are not used.
* `hagopian75_theorem2_aux`: for decomposable `M`, Jones's decomposition `{L_x}`
  (`jones55_theorem2'`) has degenerate elements, so `M` is its quotient, a circle.
* `isHereditarilyDecomposable_of_arc`: an arc is hereditarily decomposable.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Cons

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- A homogeneous indecomposable subcontinuum `Y` of a plane continuum: by `Hagopian76Thm1`, every
subcontinuum of `Y` is indecomposable. -/
theorem isIndecomposable_of_h1_sub (h1 : Hagopian76Thm1) {Y : Set M}
    (hYc : Fold.Q78.IsContinuum Y) (hYh : IsHomogeneous Y) (hYi : ¬ IsDecomposableSpace Y)
    {K : Set M} (hKY : K ⊆ Y) (hK : Fold.Q78.IsContinuum K) : Fold.Q78.IsIndecomposable K := by
  haveI : CompactSpace Y := isCompact_iff_compactSpace.mp hYc.1
  haveI : ConnectedSpace Y := isConnected_iff_connectedSpace.mp hYc.2
  set f : Y → Pt := fun y => ((y : M) : Pt)
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  set N : Set Pt := range f
  set φ : Y ≃ₜ N := hf.toHomeomorph
  haveI : CompactSpace N := isCompact_iff_compactSpace.mp (isCompact_range hf.continuous)
  haveI : ConnectedSpace N :=
    isConnected_iff_connectedSpace.mp (isConnected_range hf.continuous)
  set θ : N → M := fun p => (φ.symm p : M)
  have hθ : IsInducing θ := IsInducing.subtypeVal.comp φ.symm.isInducing
  have hθi : Function.Injective θ := Subtype.val_injective.comp φ.symm.injective
  have hθr : range θ = Y := by
    rw [show θ = Subtype.val ∘ φ.symm from rfl, range_comp, φ.symm.surjective.range_eq,
      image_univ, Subtype.range_coe]
  have hNh : IsHomogeneous N := by
    intro p q
    obtain ⟨g, hg⟩ := hYh (φ.symm p) (φ.symm q)
    exact ⟨φ.symm.trans (g.trans φ), by simp [hg]⟩
  have hNi : ¬ IsDecomposableSpace N := by
    rintro ⟨A, B, hA, hB, hAu, hBu, hAB⟩
    have hc : ∀ {S : Set N}, Fold.Q78.IsContinuum S → Fold.Q78.IsContinuum (φ.symm '' S) :=
      fun hS => ⟨hS.1.image φ.symm.continuous, hS.2.image _ φ.symm.continuous.continuousOn⟩
    have hne : ∀ {S : Set N}, S ≠ univ → φ.symm '' S ≠ univ := fun {S} hS h => by
      apply hS
      have h' : φ '' (φ.symm '' S) = φ '' univ := by rw [h]
      simpa only [← image_comp, φ.self_comp_symm, image_id, image_univ, φ.surjective.range_eq]
        using h'
    exact hYi ⟨φ.symm '' A, φ.symm '' B, hc hA, hc hB, hne hAu, hne hBu, by
      rw [← image_union, hAB, image_univ, φ.symm.surjective.range_eq]⟩
  have hHI := h1 N hNh hNi
  have hKr : K ⊆ range θ := hθr ▸ hKY
  have hK' := hHI (θ ⁻¹' K) (subset_univ _) (isContinuum_preimage_of_isInducing hθ hK hKr)
  refine ⟨hK, fun A B hA hB hAK hBK hAB => ?_⟩
  have hAr : A ⊆ range θ := hAK.trans hKr
  have hBr : B ⊆ range θ := hBK.trans hKr
  rcases hK'.2 (θ ⁻¹' A) (θ ⁻¹' B) (isContinuum_preimage_of_isInducing hθ hA hAr)
      (isContinuum_preimage_of_isInducing hθ hB hBr) (preimage_mono hAK) (preimage_mono hBK)
      (by rw [← preimage_union, hAB]) with h | h
  · left
    rw [← image_preimage_eq_of_subset hAr, h, image_preimage_eq_of_subset hKr]
  · right
    rw [← image_preimage_eq_of_subset hBr, h, image_preimage_eq_of_subset hKr]

/-- **Hagopian 1976, Theorem 2**, from `Hagopian76Thm1`. -/
theorem hagopian76_theorem2_aux (h1 : Hagopian76Thm1) (hX : IsHomogeneous M)
    (hns : ¬ SeparatesPlane M) : IsHereditarilyIndecomposable (univ : Set M) := by
  by_cases hd : IsDecomposableSpace M
  · exfalso
    obtain ⟨U, V, hUo, hUc, hVo, hVc, hUV, hUVc⟩ := jones55_two_domains' hX hd
    apply hns
    intro hcon
    rw [← hUVc] at hcon
    obtain ⟨z, -, hzU, hzV⟩ := hcon.2 U V hUo hVo subset_rfl
      (by obtain ⟨u, hu⟩ := hUc.1; exact ⟨u, Or.inl hu, hu⟩)
      (by obtain ⟨v, hv⟩ := hVc.1; exact ⟨v, Or.inr hv, hv⟩)
    exact hUV.le_bot ⟨hzU, hzV⟩
  · exact h1 M hX hd

/-- **Hagopian 1975, Corollary**, from `Hagopian76Thm1`. -/
theorem hagopian75_corollary_aux (h1 : Hagopian76Thm1) (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {H : Set M} (hH : Fold.Q78.IsContinuum H) (hnd : H.Nontrivial) :
    ¬ IsHereditarilyDecomposable H := by
  intro hHd
  have hI := h1 M hX hi H (subset_univ _) hH
  obtain ⟨A, B, hA, hB, hAH, hBH, hAB⟩ := hHd H subset_rfl hH hnd
  rcases hI.2 A B hA hB (hAB ▸ subset_union_left) (hAB ▸ subset_union_right) hAB with h | h
  · exact hAH h
  · exact hBH h

omit [CompactSpace M] [ConnectedSpace M] in
/-- A nondegenerate subcontinuum of a set that is decomposable as a space: the transfer used
twice below. -/
theorem isDecomposableSpace_of_sub {L : Set M} {A B : Set M} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (hAL : A ≠ L) (hBL : B ≠ L) (hAB : A ∪ B = L) :
    IsDecomposableSpace L := by
  have hAs : A ⊆ L := hAB ▸ subset_union_left
  have hBs : B ⊆ L := hAB ▸ subset_union_right
  refine ⟨Subtype.val ⁻¹' A, Subtype.val ⁻¹' B, isContinuum_val_preimage hAs hA,
    isContinuum_val_preimage hBs hB, ?_, ?_, ?_⟩
  · intro h
    apply hAL
    refine subset_antisymm hAs fun x hx => ?_
    have : (⟨x, hx⟩ : L) ∈ Subtype.val ⁻¹' A := h ▸ mem_univ _
    exact this
  · intro h
    apply hBL
    refine subset_antisymm hBs fun x hx => ?_
    have : (⟨x, hx⟩ : L) ∈ Subtype.val ⁻¹' B := h ▸ mem_univ _
    exact this
  · rw [← preimage_union, hAB]
    ext x
    simp

/-- **Hagopian 1975, Theorem 2**, from `Hagopian76Thm1`. -/
theorem hagopian75_theorem2_aux (h1 : Hagopian76Thm1) (hX : IsHomogeneous M) {H : Set M}
    (hH : Fold.Q78.IsContinuum H) (hnd : H.Nontrivial) (hHd : IsHereditarilyDecomposable H) :
    Nonempty (M ≃ₜ Circle) := by
  by_cases hd : IsDecomposableSpace M
  swap
  · exact absurd hHd (hagopian75_corollary_aux h1 hX hd hH hnd)
  obtain ⟨-, ⟨e⟩, hL⟩ := jones55_theorem2' hX hd
  obtain ⟨x₀, hx₀⟩ := hnd.nonempty
  -- the element `L_{x₀}` is degenerate
  have h0 : (Lset x₀).Subsingleton := by
    by_cases hsub : H ⊆ Lset x₀
    · exfalso
      have hI := isIndecomposable_of_h1_sub h1 (isContinuum_Lset x₀) (hL x₀).2.1
        (jones55_elements_indecomposable' hX hd x₀) hsub hH
      obtain ⟨A, B, hA, hB, hAH, hBH, hAB⟩ := hHd H subset_rfl hH hnd
      rcases hI.2 A B hA hB (hAB ▸ subset_union_left) (hAB ▸ subset_union_right) hAB with h | h
      · exact hAH h
      · exact hBH h
    · rw [not_subset] at hsub
      obtain ⟨y, hyH, hyL⟩ := hsub
      have hLH : Lset x₀ ⊆ H :=
        jones55_c hX hH ⟨x₀, hx₀, mem_Lset_self x₀⟩ ⟨y, hyH, hyL⟩
      by_contra hnt
      rw [not_subsingleton_iff] at hnt
      obtain ⟨A, B, hA, hB, hAL, hBL, hAB⟩ := hHd (Lset x₀) hLH (isContinuum_Lset x₀) hnt
      exact jones55_elements_indecomposable' hX hd x₀
        (isDecomposableSpace_of_sub hA hB hAL hBL hAB)
  -- hence every element is degenerate
  have hall : ∀ x : M, (Lset x).Subsingleton := by
    intro x
    obtain ⟨T, hT⟩ := hX x₀ x
    rw [← hT, Lset_homeomorph]
    exact h0.image _
  -- so `M` is the quotient
  haveI : T2Space (Quotient (lSetoid M)) := e.isEmbedding.t2Space
  have hinj : Function.Injective (Quotient.mk (lSetoid M)) := by
    intro a b hab
    have hr : Lset a = Lset b := Quotient.exact hab
    have ha : a ∈ Lset b := hr ▸ mem_Lset_self a
    exact hall b ha (mem_Lset_self b)
  let q : M ≃ Quotient (lSetoid M) :=
    Equiv.ofBijective _ ⟨hinj, Quotient.mk_surjective⟩
  have hq : Continuous q := continuous_quotient_mk'
  exact ⟨hq.homeoOfEquivCompactToT2.trans e⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **An arc is hereditarily decomposable.** A nondegenerate subcontinuum of an arc is the image
of a nondegenerate closed interval `[a, b]`, the union of the images of `[a, m]` and `[m, b]`,
`m = (a + b) / 2`. -/
theorem isHereditarilyDecomposable_of_arc {α : Set M} (e : α ≃ₜ unitInterval) :
    IsHereditarilyDecomposable α := by
  intro K hKα hK hKnt
  set g : unitInterval → M := fun t => (e.symm t : M)
  have hg : IsEmbedding g := IsEmbedding.subtypeVal.comp e.symm.isEmbedding
  have hgr : range g = α := by
    rw [show g = Subtype.val ∘ e.symm from rfl, range_comp, e.symm.surjective.range_eq,
      image_univ, Subtype.range_coe]
  have hKr : K ⊆ range g := hgr ▸ hKα
  set S : Set unitInterval := g ⁻¹' K
  have hS : Fold.Q78.IsContinuum S := isContinuum_preimage_of_isInducing hg.isInducing hK hKr
  have hKS : g '' S = K := image_preimage_eq_of_subset hKr
  -- the real picture
  set T : Set ℝ := Subtype.val '' S
  have hTc : IsCompact T := hS.1.image continuous_subtype_val
  have hTne : T.Nonempty := hS.2.1.image _
  have hTp : IsPreconnected T := hS.2.2.image _ continuous_subtype_val.continuousOn
  obtain ⟨a, haT, hamin⟩ := hTc.exists_isLeast hTne
  obtain ⟨b, hbT, hbmax⟩ := hTc.exists_isGreatest hTne
  have hSeq : ∀ t : unitInterval, t ∈ S ↔ (t : ℝ) ∈ Icc a b := by
    intro t
    constructor
    · intro ht
      exact ⟨hamin ⟨t, ht, rfl⟩, hbmax ⟨t, ht, rfl⟩⟩
    · intro ht
      obtain ⟨t', ht', heq⟩ := hTp.Icc_subset haT hbT ht
      rwa [← Subtype.ext heq]
  obtain ⟨a', ha'S, rfl⟩ := haT
  obtain ⟨b', hb'S, rfl⟩ := hbT
  have hab : (a' : ℝ) < b' := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hKnt
    obtain ⟨x', hx', rfl⟩ := hKS ▸ hx
    obtain ⟨y', hy', rfl⟩ := hKS ▸ hy
    have hx1 := (hSeq x').1 hx'
    have hy1 := (hSeq y').1 hy'
    by_contra hle
    push_neg at hle
    have hxe : x' = y' := Subtype.ext (by linarith [hx1.1, hx1.2, hy1.1, hy1.2])
    exact hxy (by rw [hxe])
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((a' : ℝ) + b') / 2 := ⟨_, rfl⟩
  have ha0 : (0 : ℝ) ≤ a' := a'.2.1
  have hb1 : (b' : ℝ) ≤ 1 := b'.2.2
  set S₁ : Set unitInterval := Subtype.val ⁻¹' Icc (a' : ℝ) m
  set S₂ : Set unitInterval := Subtype.val ⁻¹' Icc m (b' : ℝ)
  have hpiece : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ 1 →
      Fold.Q78.IsContinuum (g '' (Subtype.val ⁻¹' Icc c d : Set unitInterval)) := by
    intro c d hc hcd hd
    have himg : Subtype.val '' (Subtype.val ⁻¹' Icc c d : Set unitInterval) = Icc c d := by
      rw [Subtype.image_preimage_coe]
      exact inter_eq_right.2 fun x hx => (⟨hc.trans hx.1, hx.2.trans hd⟩ : x ∈ Icc (0 : ℝ) 1)
    have hc' : IsCompact (Subtype.val ⁻¹' Icc c d : Set unitInterval) :=
      (isClosed_Icc.preimage continuous_subtype_val).isCompact
    have hp : IsPreconnected (Subtype.val ⁻¹' Icc c d : Set unitInterval) := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, himg]
      exact isPreconnected_Icc
    refine ⟨hc'.image hg.continuous, ?_, hp.image _ hg.continuous.continuousOn⟩
    exact ⟨_, mem_image_of_mem g (show (⟨c, hc, hcd.trans hd⟩ : unitInterval) ∈
      (Subtype.val ⁻¹' Icc c d : Set unitInterval) from ⟨le_rfl, hcd⟩)⟩
  refine ⟨g '' S₁, g '' S₂, hpiece ha0 (by linarith) (by linarith),
    hpiece (by linarith) (by linarith) hb1, ?_, ?_, ?_⟩
  · intro h
    have hb : g b' ∈ g '' S₁ := h ▸ (hKS ▸ mem_image_of_mem g hb'S)
    obtain ⟨t, ht, hte⟩ := hb
    rw [hg.injective hte] at ht
    have := ht.2
    linarith
  · intro h
    have ha : g a' ∈ g '' S₂ := h ▸ (hKS ▸ mem_image_of_mem g ha'S)
    obtain ⟨t, ht, hte⟩ := ha
    rw [hg.injective hte] at ht
    have := ht.1
    linarith
  · rw [← image_union, ← hKS]
    congr 1
    ext t
    rw [hSeq]
    simp only [S₁, S₂, mem_union, mem_preimage, mem_Icc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
    · intro h
      rcases le_total (t : ℝ) m with h' | h'
      · exact Or.inl ⟨h.1, h'⟩
      · exact Or.inr ⟨h', h.2⟩

/-- **Bing 1960 for plane continua**, from `Hagopian76Thm1`. -/
theorem bing60_plane_aux (h1 : Hagopian76Thm1) (hX : IsHomogeneous M) {α : Set M}
    (hα : Nonempty (α ≃ₜ unitInterval)) : Nonempty (M ≃ₜ Circle) := by
  obtain ⟨e⟩ := hα
  set g : unitInterval → M := fun t => (e.symm t : M)
  have hg : IsEmbedding g := IsEmbedding.subtypeVal.comp e.symm.isEmbedding
  have hgr : range g = α := by
    rw [show g = Subtype.val ∘ e.symm from rfl, range_comp, e.symm.surjective.range_eq,
      image_univ, Subtype.range_coe]
  have hαc : Fold.Q78.IsContinuum α := by
    rw [← hgr]
    exact ⟨isCompact_range hg.continuous, isConnected_range hg.continuous⟩
  have hαnt : α.Nontrivial := by
    rw [← hgr]
    refine ⟨g 0, mem_range_self _, g 1, mem_range_self _, fun h => ?_⟩
    have := hg.injective h
    exact zero_ne_one (Subtype.ext_iff.1 this)
  exact hagopian75_theorem2_aux h1 hX hαc hαnt (isHereditarilyDecomposable_of_arc e)

end Cons

end HPC.Hagopian
