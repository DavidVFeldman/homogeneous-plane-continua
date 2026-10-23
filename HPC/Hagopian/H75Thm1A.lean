import HPC.Hagopian.H75Lemma1
import HPC.Hagopian.H75Transfer
import HPC.Effros.Effros

/-!
# Batch 155, item H: Theorem 1, paragraphs 1–3 (a type A′ subcontinuum)

`M` is a homogeneous indecomposable plane continuum; `A = B ∪ C`, `b ∈ B ∖ C`, `c ∈ C ∖ B`, and `E` is
irreducible between `b` and `c`, `E ⊆ B ∪ C`.

**Paragraph 2** (`no_indecomposable_interior_aux`). Suppose `I ⊆ E` is an indecomposable continuum
containing a nonempty set `Q = O ∩ E`, `O` open.

* `I ⊆ B` or `I ⊆ C`: `I ∩ B` and `I ∩ C` are continua or empty (hereditary unicoherence,
  `isContinuum_inter_of_HU`), and `I` is their union.
* Say `I ⊆ B` (the other case is symmetric, with `b` for `c`). Then `c ∉ I`, and boundary bumping
  (`exists_continuum_bump_closed`) gives a continuum `F ⊆ E ∖ O` through `c` meeting
  `closure Q ⊆ I` at a point `x`. (Hagopian takes for `F` the component of `c` in `E − Q`; any such
  continuum will do, and `c ∉ Q` since `c ∉ B ⊇ I ⊇ Q`.)
* Fix `q ∈ Q` and `ε = min (dist(c, B), dist(q, F))`. By Effros (`effros_homogeneous`) there is
  `δ > 0` such that points closer than `δ` are exchanged by homeomorphisms moving no point by `ε`.
  As composants of `I` are meagre in `I` (Baire), the ball `B(x, δ)` contains points `x₁`, `x₂` of
  `I` with `x`, `x₁`, `x₂` in three different composants of `I`. Let `f(x) = x₁`, `g(x) = x₂`.
  Then (1) holds by the choice; (2) `f(c), g(c) ∉ B` as `ε ≤ dist(c, B)`; (3) `q ∉ f[F] ∪ g[F]` as
  `ε ≤ dist(q, F)`. So Hagopian's `f`, `g` exist with `W = B(x, δ)`, and `f(x)`, `g(x)` are taken in
  composants of `I` other than that of `x` (which is the composant `F` meets).
* **`F`, `f[F]`, `g[F]` are mutually disjoint** (Hagopian gives no argument). If `F ∩ f[F] ≠ ∅`,
  `P = F ∪ f[F]` is a continuum, `P ∩ I` is a continuum (hereditary unicoherence) containing `x` and
  `f(x)`, which lie in different composants of `I`; so `P ∩ I = I` and `q ∈ F ∪ f[F]`, against
  `q ∉ O ⊇ … ` (`F ∩ O = ∅`) and (3). The same for the other two pairs.
* **The triod.** `B ∪ F ∪ f[F] ∪ g[F]` has core `B`: each of `F`, `f[F]`, `g[F]` meets `B` (at `x`,
  `f(x)`, `g(x)` — all in `I ⊆ B`), none lies in `B` (`c`, `f(c)`, `g(c)`), and they are pairwise
  disjoint; the three pieces `F ∖ B`, `f[F] ∖ B`, `g[F] ∖ B` are separated because each closure lies
  in the closed piece it came from (`isTriod_of_core`). This contradicts atriodicity (Lemma 1).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Thm1A

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- Under hereditary unicoherence, two continua with a common point meet in a continuum. -/
theorem isContinuum_inter_of_HU (hHU : IsHereditarilyUnicoherent (univ : Set M)) {P Q : Set M}
    (hP : Fold.Q78.IsContinuum P) (hQ : Fold.Q78.IsContinuum Q) (hne : (P ∩ Q).Nonempty) :
    Fold.Q78.IsContinuum (P ∩ Q) := by
  refine ⟨hP.1.inter_right hQ.1.isClosed, ?_⟩
  by_cases hnt : (P ∪ Q).Nontrivial
  · exact hHU (P ∪ Q) (subset_univ _) (isContinuum_union hP hQ hne) hnt P Q hP hQ rfl
  · rw [Set.not_nontrivial_iff] at hnt
    exact ⟨hne, (hnt.anti (inter_subset_left.trans subset_union_left)).isPreconnected⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- An indecomposable continuum, as a space, is not decomposable. -/
theorem not_isDecomposableSpace_of_isIndecomposable {I : Set M} (hI : Fold.Q78.IsIndecomposable I) :
    ¬ IsDecomposableSpace I := by
  rintro ⟨H, K, hH, hK, hHu, hKu, hHK⟩
  have hsub : ∀ S : Set I, Subtype.val '' S ⊆ I := fun S => by rintro _ ⟨z, -, rfl⟩; exact z.2
  have hun : Subtype.val '' H ∪ Subtype.val '' K = I := by
    rw [← image_union, hHK, image_univ, Subtype.range_coe]
  have himg : ∀ S : Set I, Subtype.val '' S = I → S = univ := by
    intro S hS
    refine eq_univ_of_forall fun z => ?_
    have : (z : M) ∈ Subtype.val '' S := by rw [hS]; exact z.2
    obtain ⟨w, hw, hwz⟩ := this
    rwa [Subtype.ext hwz] at hw
  rcases hI.2 _ _ (isContinuum_val_image hH) (isContinuum_val_image hK) (hsub H) (hsub K) hun with
    h | h
  · exact hHu (himg H h)
  · exact hKu (himg K h)

omit [CompactSpace M] [ConnectedSpace M] in
/-- Points in different composants of `I` lie in no proper subcontinuum of `I`. -/
theorem subset_of_notMem_composant {I : Set M} {u v : I} (huv : v ∉ Jones.composant u) {K : Set M}
    (hK : Fold.Q78.IsContinuum K) (hKI : K ⊆ I) (hu : (u : M) ∈ K) (hv : (v : M) ∈ K) : I ⊆ K := by
  by_contra hne
  apply huv
  refine ⟨Subtype.val ⁻¹' K, isContinuum_val_preimage hKI hK, ?_, hu, hv⟩
  intro h
  apply hne
  intro z hz
  have : (⟨z, hz⟩ : I) ∈ (Subtype.val ⁻¹' K : Set I) := h ▸ mem_univ _
  exact this

omit [ConnectedSpace M] in
/-- **Paragraph 2, the case `I ⊆ B`.** -/
theorem no_indecomposable_interior_core (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {B E I O : Set M} {c : M} (hB : Fold.Q78.IsContinuum B) (hE : Fold.Q78.IsContinuum E)
    (hcE : c ∈ E) (hcB : c ∉ B) (hI : Fold.Q78.IsIndecomposable I) (hIB : I ⊆ B)
    (hO : IsOpen O) (hQne : (O ∩ E).Nonempty) (hQI : O ∩ E ⊆ I) : False := by
  classical
  have hcI : c ∉ I := fun h => hcB (hIB h)
  have hIc : IsClosed I := hI.1.1.isClosed
  -- `F`, by boundary bumping
  have hEO : IsClosed (E \ O) := hE.1.isClosed.sdiff hO
  have hEOne : E \ O ≠ E := by
    obtain ⟨z, hzO, hzE⟩ := hQne
    intro h
    have : z ∈ E \ O := by rw [h]; exact hzE
    exact this.2 hzO
  obtain ⟨F, hF, hFsub, hcF, x, hxF, hxcl⟩ :=
    exists_continuum_bump_closed hE hEO diff_subset hEOne ⟨hcE, fun h => hcI (hQI ⟨h, hcE⟩)⟩
  have hclQ : closure (E \ (E \ O)) ⊆ I := by
    refine closure_minimal ?_ hIc
    rintro z ⟨hzE, hz⟩
    have hzO : z ∈ O := by
      by_contra h
      exact hz ⟨hzE, h⟩
    exact hQI ⟨hzO, hzE⟩
  have hxI : x ∈ I := hclQ hxcl
  have hFO : Disjoint F O := disjoint_left.2 fun z hz hzO => (hFsub hz).2 hzO
  obtain ⟨q, hqO, hqE⟩ := hQne
  have hqI : q ∈ I := hQI ⟨hqO, hqE⟩
  have hqF : q ∉ F := fun h => disjoint_left.1 hFO h hqO
  -- `I` is nondegenerate
  have hInt : I.Nontrivial := by
    by_contra hnt
    rw [Set.not_nontrivial_iff] at hnt
    have hOE : O ∩ E = {q} := Subset.antisymm (fun z hz => hnt (hQI hz) hqI)
      (singleton_subset_iff.2 ⟨hqO, hqE⟩)
    rcases isPreconnected_iff_subset_of_disjoint.1 hE.2.isPreconnected O {q}ᶜ hO
      isOpen_compl_singleton (fun z hz => by
        by_cases h : z = q
        · exact Or.inl (h ▸ hqO)
        · exact Or.inr h)
      (by
        ext z
        simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        intro hzE hzO hzq
        have : z ∈ O ∩ E := ⟨hzO, hzE⟩
        rw [hOE] at this
        exact hzq this) with h | h
    · have : c ∈ O ∩ E := ⟨h hcE, hcE⟩
      rw [hOE] at this
      exact hcI (this ▸ hqI)
    · exact h hqE rfl
  -- the composants of `I`
  haveI : CompactSpace I := isCompact_iff_compactSpace.mp hI.1.1
  haveI : ConnectedSpace I := isConnected_iff_connectedSpace.mp hI.1.2
  haveI : Nontrivial I := by
    obtain ⟨a, ha, a', ha', haa'⟩ := hInt
    exact ⟨⟨⟨a, ha⟩, ⟨a', ha'⟩, fun h => haa' (congrArg Subtype.val h)⟩⟩
  have hiI := not_isDecomposableSpace_of_isIndecomposable hI
  -- `ε`
  have hBne : B.Nonempty := ⟨x, hIB hxI⟩
  have hFne : F.Nonempty := ⟨c, hcF⟩
  set ε := min (infDist c B) (infDist q F) with hεdef
  have hε : 0 < ε := lt_min ((hB.1.isClosed.notMem_iff_infDist_pos hBne).1 hcB)
    ((hF.1.isClosed.notMem_iff_infDist_pos hFne).1 hqF)
  obtain ⟨δ, hδ, hhom⟩ := HPC.Effros.effros_homogeneous hX hε
  -- three composants of `I` near `x`
  set x' : I := ⟨x, hxI⟩
  set W : Set I := Subtype.val ⁻¹' ball x δ
  have hWo : IsOpen W := isOpen_ball.preimage continuous_subtype_val
  have hWne : W.Nonempty := ⟨x', mem_ball_self hδ⟩
  obtain ⟨x₁, hx₁W, hx₁⟩ := exists_notMem_of_isMeagre hWo hWne (composant_isMeagre' hiI x')
  obtain ⟨x₂, hx₂W, hx₂⟩ := exists_notMem_of_isMeagre hWo hWne
    ((composant_isMeagre' hiI x').union (composant_isMeagre' hiI x₁))
  rw [mem_union, not_or] at hx₂
  -- the homeomorphisms `f`, `g`
  obtain ⟨f, hfx, hfmove⟩ := hhom x x₁ (by rw [dist_comm]; exact hx₁W)
  obtain ⟨g, hgx, hgmove⟩ := hhom x x₂ (by rw [dist_comm]; exact hx₂W)
  have hfc : f c ∉ B := by
    intro h
    have h1 := infDist_le_dist_of_mem (x := c) h
    have h2 := hfmove c
    rw [dist_comm] at h2
    have : ε ≤ infDist c B := min_le_left _ _
    linarith
  have hgc : g c ∉ B := by
    intro h
    have h1 := infDist_le_dist_of_mem (x := c) h
    have h2 := hgmove c
    rw [dist_comm] at h2
    have : ε ≤ infDist c B := min_le_left _ _
    linarith
  have hqf : ∀ h : M ≃ₜ M, (∀ z, dist (h z) z < ε) → q ∉ h '' F := by
    rintro h hmove ⟨v, hv, rfl⟩
    have h1 := infDist_le_dist_of_mem (x := h v) hv
    have h2 := hmove v
    have : ε ≤ infDist (h v) F := min_le_right _ _
    linarith
  have hfF := isContinuum_homeo_image f hF
  have hgF := isContinuum_homeo_image g hF
  -- pairwise disjointness
  have key : ∀ {P₁ P₂ : Set M} {u v : I}, v ∉ Jones.composant u → Fold.Q78.IsContinuum P₁ →
      Fold.Q78.IsContinuum P₂ → (u : M) ∈ P₁ → (v : M) ∈ P₂ → q ∉ P₁ → q ∉ P₂ →
      (P₁ ∩ P₂) = ∅ := by
    intro P₁ P₂ u v huv h₁ h₂ hu hv hq₁ hq₂
    by_contra hne
    have hP := isContinuum_union h₁ h₂ (nonempty_iff_ne_empty.2 hne)
    have hPI := isContinuum_inter_of_HU hHU hP hI.1 ⟨u, Or.inl hu, u.2⟩
    have hsub := subset_of_notMem_composant huv hPI inter_subset_right ⟨Or.inl hu, u.2⟩
      ⟨Or.inr hv, v.2⟩
    rcases (hsub hqI).1 with h | h
    · exact hq₁ h
    · exact hq₂ h
  have hxf : ((x₁ : I) : M) ∈ f '' F := ⟨x, hxF, hfx⟩
  have hxg : ((x₂ : I) : M) ∈ g '' F := ⟨x, hxF, hgx⟩
  have hqfF := hqf f hfmove
  have hqgF := hqf g hgmove
  have d₁₂ := key hx₁ hF hfF hxF hxf hqF hqfF
  have d₁₃ := key hx₂.1 hF hgF hxF hxg hqF hqgF
  have d₂₃ := key hx₂.2 hfF hgF hxf hxg hqfF hqgF
  -- the triod
  have hT := isTriod_of_core hB hF hfF hgF ⟨x, hxF, hIB hxI⟩ ⟨x₁, hxf, hIB x₁.2⟩
    ⟨x₂, hxg, hIB x₂.2⟩ (d₁₂ ▸ empty_subset _) (d₁₃ ▸ empty_subset _) (d₂₃ ▸ empty_subset _)
    (fun h => hcB (h hcF)) (fun h => hfc (h ⟨c, hcF, rfl⟩)) (fun h => hgc (h ⟨c, hcF, rfl⟩))
  exact hAT _ (subset_univ _) hT

omit [ConnectedSpace M] in
/-- **Paragraph 2.** -/
theorem no_indecomposable_interior_aux (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {B C E : Set M} {b c : M} (hB : Fold.Q78.IsContinuum B)
    (hC : Fold.Q78.IsContinuum C) (hb : b ∈ B \ C) (hc : c ∈ C \ B)
    (hE : IsIrreducibleBetween E b c) (hEBC : E ⊆ B ∪ C) :
    ∀ I ⊆ E, Fold.Q78.IsContinuum I → (interior (Subtype.val ⁻¹' I : Set E)).Nonempty →
      ¬ Fold.Q78.IsIndecomposable I := by
  intro I hIE _ hint hI
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 (isOpen_interior (s := (Subtype.val ⁻¹' I : Set E)))
  have hQI : O ∩ E ⊆ I := by
    rintro z ⟨hzO, hzE⟩
    have : (⟨z, hzE⟩ : E) ∈ interior (Subtype.val ⁻¹' I : Set E) := by rw [← hOeq]; exact hzO
    exact (interior_subset this : (⟨z, hzE⟩ : E) ∈ (Subtype.val ⁻¹' I : Set E))
  have hQne : (O ∩ E).Nonempty := by
    obtain ⟨⟨z, hzE⟩, hz⟩ := hint
    rw [← hOeq] at hz
    exact ⟨z, hz, hzE⟩
  -- `I ⊆ B` or `I ⊆ C`
  have hIBC : I ⊆ B ∨ I ⊆ C := by
    by_cases hIB : (I ∩ B).Nonempty
    · by_cases hIC : (I ∩ C).Nonempty
      · rcases hI.2 _ _ (isContinuum_inter_of_HU hHU hI.1 hB hIB)
          (isContinuum_inter_of_HU hHU hI.1 hC hIC) inter_subset_left inter_subset_left
          (by rw [← inter_union_distrib_left]; exact inter_eq_left.2 (hIE.trans hEBC)) with h | h
        · exact Or.inl (h ▸ inter_subset_right)
        · exact Or.inr (h ▸ inter_subset_right)
      · rw [not_nonempty_iff_eq_empty] at hIC
        exact Or.inl fun z hz => ((hIE.trans hEBC) hz).resolve_right fun h =>
          (hIC ▸ (⟨hz, h⟩ : z ∈ I ∩ C) : z ∈ (∅ : Set M))
    · rw [not_nonempty_iff_eq_empty] at hIB
      exact Or.inr fun z hz => ((hIE.trans hEBC) hz).resolve_left fun h =>
        (hIB ▸ (⟨hz, h⟩ : z ∈ I ∩ B) : z ∈ (∅ : Set M))
  rcases hIBC with h | h
  · exact no_indecomposable_interior_core hX hHU hAT hB hE.1 hE.2.2.1 hc.2 hI h hO hQne hQI
  · exact no_indecomposable_interior_core hX hHU hAT hC hE.1 hE.2.1 hb.2 hI h hO hQne hQI

omit [ConnectedSpace M] in
/-- **Paragraphs 1–3.** A decomposable subcontinuum contains a continuum of type A′. -/
theorem exists_typeA'_aux (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {A : Set M} (hA : Fold.Q78.IsContinuum A) (hAd : ¬ Fold.Q78.IsIndecomposable A) :
    ∃ E ⊆ A, IsTypeA' E := by
  have : ∃ B C : Set M, Fold.Q78.IsContinuum B ∧ Fold.Q78.IsContinuum C ∧ B ⊆ A ∧ C ⊆ A ∧
      B ∪ C = A ∧ B ≠ A ∧ C ≠ A := by
    by_contra hcon
    push_neg at hcon
    apply hAd
    refine ⟨hA, fun B C hB hC hBA hCA hBC => ?_⟩
    by_contra hne
    push_neg at hne
    exact hne.2 (hcon B C hB hC hBA hCA hBC hne.1)
  obtain ⟨B, C, hB, hC, hBA, hCA, hBC, hBne, hCne⟩ := this
  obtain ⟨b, hbA, hbC⟩ : ∃ b ∈ A, b ∉ C := by
    by_contra h; push_neg at h; exact hCne (Subset.antisymm hCA h)
  obtain ⟨c, hcA, hcB⟩ : ∃ c ∈ A, c ∉ B := by
    by_contra h; push_neg at h; exact hBne (Subset.antisymm hBA h)
  have hbB : b ∈ B := by rw [← hBC] at hbA; exact hbA.resolve_right hbC
  have hcC : c ∈ C := by rw [← hBC] at hcA; exact hcA.resolve_left hcB
  obtain ⟨E, hEA, hE⟩ := HPC.exists_irreducible hA hbA hcA
  refine ⟨E, hEA, isTypeA'_of_decomposable hE ?_⟩
  exact no_indecomposable_interior_aux hX hHU hAT hB hC ⟨hbB, hbC⟩ ⟨hcC, hcB⟩ hE
    (hBC ▸ hEA)

end Thm1A

end HPC.Hagopian
