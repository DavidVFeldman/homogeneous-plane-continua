import HPC.Plane.Ingram68Core

/-!
# Batch 132, Part II (2): the property (∗) by the direct route

`ingramStar_holds : IngramStar S`, without circle-likeness (COMMISSION-batch132 §2, "alternative
route"). Let `M ⊊ Y ∪ A` be a subcontinuum and `z ∈ (Y ∪ A) ∖ M`; write `Y ∩ A = H ⊔ K`
(Ingram's Lemma 1).
* `z ∈ Y ∖ A` (or `A ∖ Y`): `isUnicoherent_of_not_mem_diff`. Cutting `Y` at `z` (cut wire,
  irreducibility from Lemma 2) puts `M` inside a hereditarily unicoherent continuum
  `C_H ∪ A ∪ C_K`.
* `z ∈ H` (or `K`) and `A ∖ Y ⊆ M`: `isUnicoherent_of_not_mem_piece`. Terminality of `H` in `A`
  (Lemma 2) lets `A` be replaced by a subcontinuum `A*` missing `z` with `Y ∪ A* = Y ∪ A`, and the
  first case applies.
-/

namespace HPC.Plane

open Set Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **The cut-wire theorem.** If no subcontinuum of the closed set `F`
meets both of the closed sets `E₁, E₂ ⊆ F`, then `F` splits into two disjoint closed sets, one
containing `E₁` and the other `E₂`. (Components are quasi-components in a compact Hausdorff
space: `connectedComponent_eq_iInter_isClopen`.) -/
theorem exists_split_of_no_continuum {F E₁ E₂ : Set S} (hF : IsClosed F) (h₁ : E₁ ⊆ F)
    (h₂ : E₂ ⊆ F) (c₁ : IsClosed E₁) (c₂ : IsClosed E₂)
    (h : ∀ C : Set S, Fold.Q78.IsContinuum C → C ⊆ F → (C ∩ E₁).Nonempty →
      (C ∩ E₂).Nonempty → False) :
    ∃ F₁ F₂ : Set S, IsClosed F₁ ∧ IsClosed F₂ ∧ Disjoint F₁ F₂ ∧ F = F₁ ∪ F₂ ∧ E₁ ⊆ F₁ ∧
      E₂ ⊆ F₂ := by
  classical
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  set E₁' : Set F := Subtype.val ⁻¹' E₁ with hE₁'
  set E₂' : Set F := Subtype.val ⁻¹' E₂ with hE₂'
  have hE₂c : IsCompact E₂' := (c₂.preimage continuous_subtype_val).isCompact
  have hE₁c : IsCompact E₁' := (c₁.preimage continuous_subtype_val).isCompact
  have hW : ∀ e ∈ E₁', ∃ W : Set F, IsClopen W ∧ e ∈ W ∧ Disjoint W E₂' := by
    intro e he
    have hC : E₂' ∩ ⋂ s : { s : Set F // IsClopen s ∧ e ∈ s }, (s : Set F) = ∅ := by
      rw [← connectedComponent_eq_iInter_isClopen]
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hz2 hzC
      exact h (Subtype.val '' connectedComponent e)
        ⟨(isClosed_connectedComponent.isCompact).image continuous_subtype_val,
          isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn⟩
        (by rintro _ ⟨w, -, rfl⟩; exact w.2) ⟨e, ⟨e, mem_connectedComponent, rfl⟩, he⟩
        ⟨z, ⟨z, hzC, rfl⟩, hz2⟩
    obtain ⟨u, hu⟩ := hE₂c.elim_finite_subfamily_closed
      (fun s : { s : Set F // IsClopen s ∧ e ∈ s } => (s : Set F)) (fun s => s.2.1.isClosed) hC
    refine ⟨⋂ i ∈ u, (i : Set F), isClopen_biInter_finset fun i _ => i.2.1,
      mem_iInter₂.mpr fun i _ => i.2.2, ?_⟩
    rw [disjoint_iff_inter_eq_empty, inter_comm]
    exact hu
  choose! W hWc hWe hWd using hW
  obtain ⟨t, htE, htfin, hcover⟩ := hE₁c.elim_finite_subcover_image (b := E₁') (c := W)
    (fun e he => (hWc e he).isOpen) (fun e he => mem_biUnion he (hWe e he))
  set U : Set F := ⋃ i ∈ t, W i with hU_def
  have hU : IsClopen U :=
    ⟨htfin.isClosed_biUnion fun i hi => (hWc i (htE hi)).isClosed,
      isOpen_biUnion fun i hi => (hWc i (htE hi)).isOpen⟩
  have hUd : Disjoint U E₂' := by
    rw [hU_def, disjoint_iUnion₂_left]
    exact fun i hi => hWd i (htE hi)
  refine ⟨Subtype.val '' U, Subtype.val '' Uᶜ,
    (hU.isClosed.isCompact.image continuous_subtype_val).isClosed,
    (hU.compl.isClosed.isCompact.image continuous_subtype_val).isClosed,
    (disjoint_image_iff Subtype.val_injective).mpr disjoint_compl_right, ?_, ?_, ?_⟩
  · rw [← image_union, union_compl_self, image_univ, Subtype.range_coe]
  · intro x hx
    exact ⟨⟨x, h₁ hx⟩, hcover hx, rfl⟩
  · intro x hx
    exact ⟨⟨x, h₂ hx⟩, fun h' => disjoint_left.mp hUd h' hx, rfl⟩

omit [CompactSpace S] in
/-- A subsingleton is unicoherent. -/
theorem isUnicoherent_of_subsingleton {M : Set S} (h : M.Subsingleton) : IsUnicoherent M := by
  intro P Q hP hQ hPQ
  obtain ⟨x, hx⟩ := hP.2.nonempty
  obtain ⟨y, hy⟩ := hQ.2.nonempty
  have hxy : x = y := h (hPQ ▸ Or.inl hx) (hPQ ▸ Or.inr hy)
  exact ⟨⟨x, hx, hxy ▸ hy⟩,
    (h.anti (inter_subset_left.trans (hPQ ▸ subset_union_left))).isPreconnected⟩

omit [CompactSpace S] in
/-- A subcontinuum of a hereditarily unicoherent set is unicoherent. -/
theorem isUnicoherent_of_subset_hu {T M : Set S} (hT : IsHereditarilyUnicoherent T)
    (hM : Fold.Q78.IsContinuum M) (hMT : M ⊆ T) : IsUnicoherent M := by
  by_cases hnt : M.Nontrivial
  · exact hT M hMT hM hnt
  · exact isUnicoherent_of_subsingleton (not_nontrivial_iff.mp hnt)

/-- The closure of the union of all subcontinua of `F` meeting `G`. -/
def satUnion (F G : Set S) : Set S :=
  closure (⋃₀ {L : Set S | Fold.Q78.IsContinuum L ∧ L ⊆ F ∧ (L ∩ G).Nonempty})

omit [CompactSpace S] in
theorem subset_satUnion {F G L : Set S} (hL : Fold.Q78.IsContinuum L) (hLF : L ⊆ F)
    (hLG : (L ∩ G).Nonempty) : L ⊆ satUnion F G :=
  (subset_sUnion_of_mem (show L ∈ {L : Set S | Fold.Q78.IsContinuum L ∧ L ⊆ F ∧
    (L ∩ G).Nonempty} from ⟨hL, hLF, hLG⟩)).trans subset_closure

omit [CompactSpace S] in
theorem satUnion_subset {F G : Set S} (hF : IsClosed F) : satUnion F G ⊆ F :=
  closure_minimal (sUnion_subset fun _ hL => hL.2.1) hF

theorem isContinuum_satUnion {F G : Set S} (hF : IsClosed F) (hG : Fold.Q78.IsContinuum G)
    (hGF : G ⊆ F) : Fold.Q78.IsContinuum (satUnion F G) := by
  obtain ⟨g, hg⟩ := hG.2.nonempty
  have hGmem : G ∈ {L : Set S | Fold.Q78.IsContinuum L ∧ L ⊆ F ∧ (L ∩ G).Nonempty} :=
    ⟨hG, hGF, ⟨g, hg, hg⟩⟩
  refine (isContinuum_closure_of_subset hF (sUnion_subset fun _ hL => hL.2.1) ?_
    ⟨g, subset_sUnion_of_mem hGmem hg⟩).1
  refine isPreconnected_of_forall g fun y ⟨L, hL, hyL⟩ => ⟨G ∪ L, union_subset
    (subset_sUnion_of_mem hGmem) (subset_sUnion_of_mem hL), Or.inl hg, Or.inr hyL, ?_⟩
  obtain ⟨x, hxL, hxG⟩ := hL.2.2
  exact hG.2.isPreconnected.union' ⟨x, hxG, hxL⟩ hL.1.2.isPreconnected

/-- **(∗), first case: a missing point of `Y ∖ A`.** Suppose `Y`, `A` are snake-like, meet,
`Y ∪ A` is atriodic, and `Y ∩ A` is not connected. A subcontinuum `M` of `Y ∪ A` missing a point
`z ∈ Y ∖ A` is unicoherent.

Proof. Write `Y ∩ A = H ⊔ K` (Lemma 1). Remove a ball `O` about `z` missing `M ∪ A`. No
subcontinuum of `Y ∖ O` meets both `H` and `K` (irreducibility, `eq_of_subset_of_split`), so
`Y ∖ O = Y₁ ⊔ Y₂` with `H ⊆ Y₁`, `K ⊆ Y₂` (cut wire). Every point of `M ∩ Y₁` lies on a continuum
in `Y₁` meeting `H` (boundary bumping), so `M ⊆ C_H ∪ A ∪ C_K`, where `C_H ⊆ Y₁` and `C_K ⊆ Y₂`
are the saturations of `H` and `K`. This continuum is hereditarily unicoherent: `C_H ∩ A = H`,
`(C_H ∪ A) ∩ C_K = K` (`isHereditarilyUnicoherent_union`). -/
theorem isUnicoherent_of_not_mem_diff {Y A M : Set S} {z : S} (hY : IsSnakeLike Y)
    (hA : IsSnakeLike A) (hne : (Y ∩ A).Nonempty) (hat : IsAtriodic (Y ∪ A))
    (hnc : ¬ IsConnected (Y ∩ A)) (hM : Fold.Q78.IsContinuum M) (hMX : M ⊆ Y ∪ A)
    (hzY : z ∈ Y) (hzA : z ∉ A) (hzM : z ∉ M) : IsUnicoherent M := by
  obtain ⟨H, K, hH, hK, hHK, hYA⟩ := ingram_lemma1 hY.1 hA.1 hat hne hnc
  have hYhu := isHereditarilyUnicoherent_of_isSnakeLike hY
  have hAhu := isHereditarilyUnicoherent_of_isSnakeLike hA
  have hHY : H ⊆ Y := fun x hx => (hYA ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ Y ∩ A).1
  have hHA : H ⊆ A := fun x hx => (hYA ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ Y ∩ A).2
  have hKY : K ⊆ Y := fun x hx => (hYA ▸ (Or.inr hx : x ∈ H ∪ K) : x ∈ Y ∩ A).1
  have hKA : K ⊆ A := fun x hx => (hYA ▸ (Or.inr hx : x ∈ H ∪ K) : x ∈ Y ∩ A).2
  by_cases hMY : M ⊆ Y
  · exact isUnicoherent_of_isSnakeLike (isSnakeLike_of_subcontinuum hY hM hMY)
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball z r ⊆ (M ∪ A)ᶜ :=
    Metric.isOpen_iff.mp (hM.1.isClosed.union hA.1.1.isClosed).isOpen_compl z
      (by simp [hzM, hzA])
  have hOM : ∀ {x}, x ∈ ball z r → x ∉ M := fun hx h => hball hx (Or.inl h)
  have hOA : ∀ {x}, x ∈ ball z r → x ∉ A := fun hx h => hball hx (Or.inr h)
  have hFc : IsClosed (Y \ ball z r) := hY.1.1.isClosed.sdiff isOpen_ball
  obtain ⟨Y₁, Y₂, c₁, c₂, d, hsplit, hHY₁, hKY₂⟩ := exists_split_of_no_continuum hFc
    (fun x hx => ⟨hHY hx, fun h => hOA h (hHA hx)⟩) (fun x hx => ⟨hKY hx, fun h => hOA h (hKA hx)⟩)
    hH.1.isClosed hK.1.isClosed (by
      intro C hC hCF ⟨x, hxC, hxH⟩ ⟨y, hyC, hyK⟩
      have hU : Fold.Q78.IsContinuum (C ∪ H ∪ K) :=
        isContinuum_union (isContinuum_union hC hH ⟨x, hxC, hxH⟩) hK ⟨y, Or.inl hyC, hyK⟩
      have e := eq_of_subset_of_split hY.1 hA.1 hH.1.isClosed hK.1.isClosed hH.2.nonempty
        hK.2.nonempty hHK hYA hat hU
        (union_subset (union_subset (hCF.trans diff_subset) hHY) hKY)
        (union_subset (subset_union_right.trans subset_union_left) subset_union_right)
      have hz : z ∈ C ∪ H ∪ K := e ▸ hzY
      rcases hz with (hz | hz) | hz
      · exact (hCF hz).2 (mem_ball_self hr)
      · exact hzA (hHA hz)
      · exact hzA (hKA hz))
  have hY₁Y : Y₁ ⊆ Y := fun x hx => (hsplit ▸ (Or.inl hx : x ∈ Y₁ ∪ Y₂) : x ∈ Y \ ball z r).1
  have hY₂Y : Y₂ ⊆ Y := fun x hx => (hsplit ▸ (Or.inr hx : x ∈ Y₁ ∪ Y₂) : x ∈ Y \ ball z r).1
  have hY₁A : ∀ x ∈ Y₁, x ∈ A → x ∈ H := fun x hx hxA => by
    rcases (hYA ▸ ⟨hY₁Y hx, hxA⟩ : x ∈ H ∪ K) with h | h
    · exact h
    · exact absurd (hKY₂ h) (disjoint_left.mp d hx)
  have hY₂A : ∀ x ∈ Y₂, x ∈ A → x ∈ K := fun x hx hxA => by
    rcases (hYA ▸ ⟨hY₂Y hx, hxA⟩ : x ∈ H ∪ K) with h | h
    · exact absurd (hHY₁ h) (disjoint_right.mp d hx)
    · exact h
  -- points of `M` outside `A` lie in `Y₁ ∪ Y₂`
  have hMcov : ∀ {w}, w ∈ M → w ∉ A → w ∈ Y₁ ∪ Y₂ := fun hwM hwA =>
    hsplit ▸ (⟨(hMX hwM).resolve_right hwA, fun h => hOM h hwM⟩ : _ ∈ Y \ ball z r)
  -- boundary bumping inside `Y₁` and `Y₂`
  have arm : ∀ {Y₁ Y₂ G : Set S}, IsClosed Y₁ → IsClosed Y₂ → Disjoint Y₁ Y₂ → Y₁ ⊆ Y →
      (∀ {w}, w ∈ M → w ∉ A → w ∈ Y₁ ∪ Y₂) → (∀ x ∈ Y₁, x ∈ A → x ∈ G) →
      ∀ m ∈ M ∩ Y₁, ∃ L : Set S, Fold.Q78.IsContinuum L ∧ L ⊆ Y₁ ∧ m ∈ L ∧ (L ∩ G).Nonempty := by
    intro Y₁ Y₂ G c₁ c₂ d hY₁Y hMcov hY₁A m hm
    have hne : M ∩ Y₁ ≠ M := by
      intro h
      apply hMY
      intro x hx
      exact hY₁Y (h.symm ▸ hx : x ∈ M ∩ Y₁).2
    obtain ⟨L, hL, hLF, hmL, x, hxL, hxcl⟩ :=
      exists_continuum_bump_closed hM (hM.1.isClosed.inter c₁) inter_subset_left hne hm
    refine ⟨L, hL, hLF.trans inter_subset_right, hmL, x, hxL, ?_⟩
    have hsub : M \ (M ∩ Y₁) ⊆ A ∪ Y₂ := by
      intro w ⟨hwM, hw⟩
      by_cases hwA : w ∈ A
      · exact Or.inl hwA
      rcases hMcov hwM hwA with h | h
      · exact absurd ⟨hwM, h⟩ hw
      · exact Or.inr h
    rcases closure_minimal hsub (hA.1.1.isClosed.union c₂) hxcl with h | h
    · exact hY₁A x (hLF hxL).2 h
    · exact absurd h (disjoint_left.mp d (hLF hxL).2)
  have armH := arm c₁ c₂ d hY₁Y hMcov hY₁A
  have armK := arm c₂ c₁ d.symm hY₂Y (fun hwM hwA => (hMcov hwM hwA).symm) hY₂A
  -- the saturations
  have hCH := isContinuum_satUnion c₁ hH hHY₁
  have hCK := isContinuum_satUnion c₂ hK hKY₂
  have hCHY₁ : satUnion Y₁ H ⊆ Y₁ := satUnion_subset c₁
  have hCKY₂ : satUnion Y₂ K ⊆ Y₂ := satUnion_subset c₂
  have hHCH : H ⊆ satUnion Y₁ H := subset_satUnion hH hHY₁ (by
    obtain ⟨x, hx⟩ := hH.2.nonempty; exact ⟨x, hx, hx⟩)
  have hKCK : K ⊆ satUnion Y₂ K := subset_satUnion hK hKY₂ (by
    obtain ⟨x, hx⟩ := hK.2.nonempty; exact ⟨x, hx, hx⟩)
  have e₁ : satUnion Y₁ H ∩ A = H := Subset.antisymm
    (fun x hx => hY₁A x (hCHY₁ hx.1) hx.2) (fun x hx => ⟨hHCH hx, hHA hx⟩)
  have e₂ : (satUnion Y₁ H ∪ A) ∩ satUnion Y₂ K = K := by
    refine Subset.antisymm (fun x ⟨hx, hx'⟩ => ?_) (fun x hx => ⟨Or.inr (hKA hx), hKCK hx⟩)
    rcases hx with hx | hx
    · exact absurd (hCKY₂ hx') (disjoint_left.mp d (hCHY₁ hx))
    · exact hY₂A x (hCKY₂ hx') hx
  have hU₁ : Fold.Q78.IsContinuum (satUnion Y₁ H ∪ A) := by
    obtain ⟨x, hx⟩ := hH.2.nonempty
    exact isContinuum_union hCH hA.1 ⟨x, hHCH hx, hHA hx⟩
  have hu₁ : IsHereditarilyUnicoherent (satUnion Y₁ H ∪ A) :=
    isHereditarilyUnicoherent_union hCH hA.1 (hYhu.mono (hCHY₁.trans hY₁Y)) hAhu
      (by rw [e₁]; exact hH.2)
  have hu₂ : IsHereditarilyUnicoherent (satUnion Y₁ H ∪ A ∪ satUnion Y₂ K) :=
    isHereditarilyUnicoherent_union hU₁ hCK hu₁ (hYhu.mono (hCKY₂.trans hY₂Y))
      (by rw [e₂]; exact hK.2)
  refine isUnicoherent_of_subset_hu hu₂ hM fun m hm => ?_
  by_cases hmA : m ∈ A
  · exact Or.inl (Or.inr hmA)
  rcases hMcov hm hmA with h | h
  · obtain ⟨L, hL, hLY, hmL, hLH⟩ := armH m ⟨hm, h⟩
    exact Or.inl (Or.inl (subset_satUnion hL hLY hLH hmL))
  · obtain ⟨L, hL, hLY, hmL, hLK⟩ := armK m ⟨hm, h⟩
    exact Or.inr (subset_satUnion hL hLY hLK hmL)


/-- **(∗), second case: a missing point of `H`, with `A ∖ Y ⊆ M`.** Then `A` is replaced by a
subcontinuum `A*` containing `A ∖ Y` and `K`, meeting `H`, and missing `z`, and the first case
applies to `Y ∪ A* = Y ∪ A`. `A*` is the saturation in `A ∖ O` (`O` a ball about `z` missing
`M ∪ K`, so `O ∩ A ⊆ H`) of a continuum `G ⊇ K` meeting `H`; terminality of `H` in `A`
(Lemma 2) makes every arm through a point of `A ∖ Y` meet `G`. -/
theorem isUnicoherent_of_not_mem_piece {Y A H K M : Set S} {z : S} (hY : IsSnakeLike Y)
    (hA : IsSnakeLike A) (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K)
    (hHK : Disjoint H K) (hYA : Y ∩ A = H ∪ K) (hat : IsAtriodic (Y ∪ A))
    (hM : Fold.Q78.IsContinuum M) (hMX : M ⊆ Y ∪ A) (hzH : z ∈ H) (hzM : z ∉ M)
    (hAY : A \ Y ⊆ M) : IsUnicoherent M := by
  have hAhu := isHereditarilyUnicoherent_of_isSnakeLike hA
  have hHY : H ⊆ Y := fun x hx => (hYA ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ Y ∩ A).1
  have hHA : H ⊆ A := fun x hx => (hYA ▸ (Or.inl hx : x ∈ H ∪ K) : x ∈ Y ∩ A).2
  have hKY : K ⊆ Y := fun x hx => (hYA ▸ (Or.inr hx : x ∈ H ∪ K) : x ∈ Y ∩ A).1
  have hKA : K ⊆ A := fun x hx => (hYA ▸ (Or.inr hx : x ∈ H ∪ K) : x ∈ Y ∩ A).2
  have hzK : z ∉ K := fun h => disjoint_left.mp hHK hzH h
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball z r ⊆ (M ∪ K)ᶜ :=
    Metric.isOpen_iff.mp (hM.1.isClosed.union hK.1.isClosed).isOpen_compl z
      (by simp [hzM, hzK])
  have hOA : ∀ {x}, x ∈ ball z r → x ∈ A → x ∈ H := by
    intro x hxO hxA
    have hxY : x ∈ Y := by
      by_contra h
      exact hball hxO (Or.inl (hAY ⟨hxA, h⟩))
    rcases (hYA ▸ ⟨hxY, hxA⟩ : x ∈ H ∪ K) with h | h
    · exact h
    · exact absurd (Or.inr h) (hball hxO)
  have hterm : IsTerminalSub A H :=
    (ingram_lemma2 hA.1 hY.1 hH hK hHK (by rw [inter_comm]; exact hYA)
      (by rw [union_comm]; exact hat) hAhu).1
  set F := A \ ball z r with hF_def
  have hFc : IsClosed F := hA.1.1.isClosed.sdiff isOpen_ball
  have hFne : F ≠ A := fun h => (h.symm ▸ hHA hzH : z ∈ F).2 (mem_ball_self hr)
  have hclH : closure (A \ F) ⊆ H := closure_minimal (fun x hx => by
    have hxO : x ∈ ball z r := by_contra fun h => hx.2 ⟨hx.1, h⟩
    exact hOA hxO hx.1) hH.1.isClosed
  -- an arm in `A ∖ O` through any point of `F`, meeting `H`
  have bump : ∀ x ∈ F, ∃ L : Set S, Fold.Q78.IsContinuum L ∧ L ⊆ F ∧ x ∈ L ∧
      (L ∩ H).Nonempty := by
    intro x hx
    obtain ⟨L, hL, hLF, hxL, y, hyL, hycl⟩ := exists_continuum_bump_closed hA.1 hFc diff_subset
      hFne hx
    exact ⟨L, hL, hLF, hxL, y, hyL, hclH hycl⟩
  obtain ⟨k, hk⟩ := hK.2.nonempty
  have hkF : k ∈ F := ⟨hKA hk, fun h => hball h (Or.inr hk)⟩
  have hKF : K ⊆ F := fun x hx => ⟨hKA hx, fun h => hball h (Or.inr hx)⟩
  obtain ⟨Γ, hΓ, hΓF, hkΓ, hΓH⟩ := bump k hkF
  set G := Γ ∪ K with hG_def
  have hG : Fold.Q78.IsContinuum G := isContinuum_union hΓ hK ⟨k, hkΓ, hk⟩
  have hGF : G ⊆ F := union_subset hΓF hKF
  set A' := satUnion F G with hA'_def
  have hA' : Fold.Q78.IsContinuum A' := isContinuum_satUnion hFc hG hGF
  have hA'F : A' ⊆ F := satUnion_subset hFc
  have hA'A : A' ⊆ A := hA'F.trans diff_subset
  have hGA' : G ⊆ A' := subset_satUnion hG hGF (by
    obtain ⟨x, hx⟩ := hG.2.nonempty; exact ⟨x, hx, hx⟩)
  have hzA' : z ∉ A' := fun h => (hA'F h).2 (mem_ball_self hr)
  -- `A ∖ Y ⊆ A'`
  have hAYA' : A \ Y ⊆ A' := by
    intro a ha
    have haF : a ∈ F := ⟨ha.1, fun h => hball h (Or.inl (hAY ha))⟩
    obtain ⟨L, hL, hLF, haL, hLH⟩ := bump a haF
    refine subset_satUnion hL hLF ?_ haL
    rcases hterm.2.2 L G hL hG (hLF.trans diff_subset) (hGF.trans diff_subset) hLH
      (hΓH.mono (inter_subset_inter_left _ subset_union_left)) with h | h
    · rcases h haL with h' | h'
      · exact absurd (hHY h') ha.2
      · exact ⟨a, haL, h'⟩
    · rcases h (Or.inr hk) with h' | h'
      · exact ⟨k, h', Or.inr hk⟩
      · exact absurd h' (disjoint_right.mp hHK hk)
  have hYA' : Y ∪ A' = Y ∪ A := by
    refine Subset.antisymm (union_subset_union_right _ hA'A) (union_subset subset_union_left ?_)
    intro x hx
    by_cases hxY : x ∈ Y
    · exact Or.inl hxY
    · exact Or.inr (hAYA' ⟨hx, hxY⟩)
  have hA's : IsSnakeLike A' := isSnakeLike_of_subcontinuum hA hA' hA'A
  -- `Y ∩ A'` meets `H` and `K` only
  obtain ⟨h₀, hh₀Γ, hh₀H⟩ := hΓH
  have hsplit : Y ∩ A' = (H ∩ A') ∪ (K ∩ A') := by
    rw [← union_inter_distrib_right, ← hYA]
    ext x
    exact ⟨fun ⟨hxY, hxA'⟩ => ⟨⟨hxY, hA'A hxA'⟩, hxA'⟩, fun ⟨⟨hxY, _⟩, hxA'⟩ => ⟨hxY, hxA'⟩⟩
  have hne' : (Y ∩ A').Nonempty := ⟨k, hKY hk, hGA' (Or.inr hk)⟩
  have hnc' : ¬ IsConnected (Y ∩ A') := by
    rw [hsplit]
    exact fun h => not_isPreconnected_of_split (hH.1.isClosed.inter hA'.1.isClosed)
      (hK.1.isClosed.inter hA'.1.isClosed) ⟨h₀, hh₀H, hGA' (Or.inl hh₀Γ)⟩
      ⟨k, hk, hGA' (Or.inr hk)⟩ (hHK.mono inter_subset_left inter_subset_left) h.isPreconnected
  exact isUnicoherent_of_not_mem_diff hY hA's hne' (hYA' ▸ hat) hnc' hM (hYA' ▸ hMX)
    (hHY hzH) hzA' hzM

/-- **(∗) holds.** Suppose `Y` and `A` are snake-like and meet, `Y ∪ A` is atriodic, and
`Y ∩ A` is not connected. Then every proper subcontinuum of `Y ∪ A` is unicoherent.

Route: direct (COMMISSION-batch132 §2, "alternative route"), without circle-likeness. A missing
point in `Y ∖ A` or `A ∖ Y`: `isUnicoherent_of_not_mem_diff`. Otherwise every missing point is in
`Y ∩ A = H ⊔ K`, and `A ∖ Y ⊆ M`: `isUnicoherent_of_not_mem_piece`. -/
theorem ingramStar_holds : IngramStar S := by
  intro Y A hY hA hne hat hnc M hMX hM hMne
  obtain ⟨z, hzX, hzM⟩ : ∃ z ∈ Y ∪ A, z ∉ M := by
    by_contra h
    push_neg at h
    exact hMne (Subset.antisymm hMX h)
  by_cases hw : ∃ w ∈ Y ∪ A, w ∉ M ∧ (w ∉ A ∨ w ∉ Y)
  · obtain ⟨w, hwX, hwM, hw⟩ := hw
    rcases hw with hwA | hwY
    · exact isUnicoherent_of_not_mem_diff hY hA hne hat hnc hM hMX
        (hwX.resolve_right hwA) hwA hwM
    · exact isUnicoherent_of_not_mem_diff hA hY (by rwa [inter_comm])
        (by rwa [union_comm]) (by rwa [inter_comm]) hM (by rwa [union_comm])
        (hwX.resolve_left hwY) hwY hwM
  push_neg at hw
  obtain ⟨H, K, hH, hK, hHK, hYA⟩ := ingram_lemma1 hY.1 hA.1 hat hne hnc
  have hAY : A \ Y ⊆ M := fun a ⟨haA, haY⟩ => by
    by_contra h
    exact haY (hw a (Or.inr haA) h).2
  obtain ⟨hzA, hzY⟩ := hw z hzX hzM
  rcases (hYA ▸ ⟨hzY, hzA⟩ : z ∈ H ∪ K) with hzH | hzK
  · exact isUnicoherent_of_not_mem_piece hY hA hH hK hHK hYA hat hM hMX hzH hzM hAY
  · exact isUnicoherent_of_not_mem_piece hY hA hK hH hHK.symm (by rw [hYA, union_comm]) hat hM
      hMX hzK hzM hAY

end HPC.Plane
