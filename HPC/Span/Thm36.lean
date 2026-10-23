import HPC.Span.Cook
import HPC.Jones.Jones75B

/-!
# Batch 191, §5: Oversteegen–Tymchatyn 1982, Theorem 3.6 (indecomposable case) from Corollary 3.5

* `not_surjSemiSpanPos_univ` (§5.1–§5.8), for an abstract homogeneous, indecomposable, hereditarily
  indecomposable compact metric continuum.
* `ot82_theorem36_of_cor35`, `theoremC_of_cor35` (§5.9).

Two simplifications of the commission's route, both recorded in the report:
* §5.4: instead of the sequence `Kᵢ` (components of `M ∖ B(q, 1/i)`), one `δ`-dense proper
  subcontinuum is taken directly (`exists_dense_proper_subcontinuum`): the proper subcontinua
  through a point are directed by union (indecomposability) and their union, the composant, is
  dense; compactness picks one.
* §5.1/§5.8: the constant `3ε` is replaced by `α`, the minimum of `d` on `Z`; Effros is applied
  with `α` itself, which already keeps `W` off the diagonal.
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Hagopian

section Thm36

variable {X : Type*} [MetricSpace X]

/-- Two proper subcontinua of an indecomposable space that meet have a proper subcontinuum as
union. -/
theorem union_proper_of_indec (hi : ¬ IsDecomposableSpace X) {H K : Set X}
    (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K) (hHu : H ≠ univ) (hKu : K ≠ univ)
    (hHK : (H ∩ K).Nonempty) :
    Fold.Q78.IsContinuum (H ∪ K) ∧ H ∪ K ≠ univ :=
  ⟨⟨hH.1.union hK.1, IsConnected.union hHK hH.2 hK.2⟩, fun h => hi ⟨H, K, hH, hK, hHu, hKu, h⟩⟩

/-- **§5.4** (a variant of the commission's sequence `Kᵢ`): a nondegenerate indecomposable
continuum has, for every `δ > 0`, a `δ`-dense proper subcontinuum. The proper subcontinua through
a point have dense union (the composant) and are directed by union; compactness picks one. -/
theorem exists_dense_proper_subcontinuum [CompactSpace X] [ConnectedSpace X] [Nontrivial X]
    (hi : ¬ IsDecomposableSpace X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set X, Fold.Q78.IsContinuum K ∧ K ≠ univ ∧ ∀ y, ∃ z ∈ K, dist z y < δ := by
  obtain ⟨x⟩ := ‹Nontrivial X›.to_nonempty
  set ι := {K : Set X // Fold.Q78.IsContinuum K ∧ K ≠ univ ∧ x ∈ K}
  have hsing : ({x} : Set X) ≠ univ := by
    obtain ⟨y, hy⟩ := exists_ne x
    intro h
    exact hy ((h ▸ mem_univ y : y ∈ ({x} : Set X)))
  haveI : Nonempty ι := ⟨⟨{x}, ⟨isCompact_singleton, isConnected_singleton⟩, hsing, rfl⟩⟩
  have hcov : univ ⊆ ⋃ K : ι, thickening δ K.1 := by
    rintro y -
    obtain ⟨c, hcb, K, hK, hKu, hxK, hcK⟩ :=
      (composant_dense x).inter_open_nonempty (ball y δ) isOpen_ball ⟨y, mem_ball_self hδ⟩
    refine mem_iUnion.2 ⟨⟨K, hK, hKu, hxK⟩, mem_thickening_iff.2 ⟨c, hcK, ?_⟩⟩
    rw [mem_ball] at hcb
    rwa [dist_comm]
  have hdir : Directed (· ⊆ ·) (fun K : ι => thickening δ K.1) := by
    intro K L
    obtain ⟨hU, hUu⟩ := union_proper_of_indec hi K.2.1 L.2.1 K.2.2.1 L.2.2.1 ⟨x, K.2.2.2, L.2.2.2⟩
    exact ⟨⟨K.1 ∪ L.1, hU, hUu, Or.inl K.2.2.2⟩, thickening_subset_of_subset δ subset_union_left,
      thickening_subset_of_subset δ subset_union_right⟩
  obtain ⟨K, hK⟩ := isCompact_univ.elim_directed_cover (fun K : ι => thickening δ K.1)
    (fun K => isOpen_thickening) hcov hdir
  refine ⟨K.1, K.2.1, K.2.2.1, fun y => ?_⟩
  obtain ⟨z, hz, hzy⟩ := mem_thickening_iff.1 (hK (mem_univ y))
  exact ⟨z, hz, by rwa [dist_comm]⟩

/-- **§5.2, the reduction**: a witness of positive semi-span of the whole space can be chosen
with the second projection either not onto, or onto and irreducible for that. -/
theorem exists_reduced_witness {Z : Set (X × X)} (hZ : Fold.Q78.IsContinuum Z) (hoff : OffDiag Z)
    (h1 : Prod.fst '' Z = univ) :
    ∃ Z' : Set (X × X), Fold.Q78.IsContinuum Z' ∧ OffDiag Z' ∧ Prod.fst '' Z' = univ ∧
      (Prod.snd '' Z' ≠ univ ∨ ∀ W ⊆ Z', Fold.Q78.IsContinuum W → Prod.snd '' W = univ → W = Z') := by
  by_cases h2 : Prod.snd '' Z = univ
  · obtain ⟨Z₀, hZ₀Z, hZ₀, hP₀, hmin⟩ := brouwer_reduction hZ (fun W => Prod.snd '' W = univ) h2
      (by
        intro c hne hc hall
        obtain ⟨-, himg⟩ := isContinuum_sInter_chain hne hc fun W hW => (hall W hW).1
        show Prod.snd '' ⋂₀ c = univ
        rw [himg continuous_snd]
        exact eq_univ_of_forall fun y => mem_iInter₂.2 fun W hW => (hall W hW).2.2 ▸ mem_univ y)
    have hoff₀ : OffDiag Z₀ := fun p hp => hoff p (hZ₀Z hp)
    by_cases h1₀ : Prod.fst '' Z₀ = univ
    · exact ⟨Z₀, hZ₀, hoff₀, h1₀, Or.inr hmin⟩
    · exact ⟨Prod.swap '' Z₀, isContinuum_swap hZ₀, offDiag_swap hoff₀,
        by rw [fst_image_swap]; exact hP₀, Or.inl (by rw [snd_image_swap]; exact h1₀)⟩
  · exact ⟨Z, hZ, hoff, h1, Or.inl h2⟩

/-- **O–T Theorem 3.6, core** (commission §5.1–§5.8), for an abstract compact metric continuum:
if `X` is homogeneous, indecomposable and hereditarily indecomposable, and no proper subcontinuum
has positive surjective semi-span, then neither has `X`. -/
theorem not_surjSemiSpanPos_univ [CompactSpace X] [ConnectedSpace X] (hom : IsHomogeneous X)
    (hi : ¬ IsDecomposableSpace X) (hHI : IsHereditarilyIndecomposable (univ : Set X))
    (h35 : ∀ A : Set X, Fold.Q78.IsContinuum A → A ≠ univ → ¬ SurjSemiSpanPos A) :
    ¬ SurjSemiSpanPos (univ : Set X) := by
  rintro ⟨Z₁, -, hZ₁, hoff₁, h1₁⟩
  -- §5.2
  obtain ⟨Z, hZ, hoff, h1, hred⟩ := exists_reduced_witness hZ₁ hoff₁ h1₁
  -- `X` is nondegenerate
  haveI : Nontrivial X := by
    obtain ⟨p, hp⟩ := hZ.2.nonempty
    exact ⟨⟨p.1, p.2, hoff p hp⟩⟩
  -- §5.1
  obtain ⟨α, hα, hdα⟩ := exists_pos_le_dist hZ hoff
  -- §5.3
  obtain ⟨δ, hδ, heff⟩ := HPC.Effros.effros_homogeneous hom hα
  -- §5.4
  obtain ⟨K, hK, hKu, hKd⟩ := exists_dense_proper_subcontinuum hi hδ
  -- §5.5 (Cook)
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.1
  haveI : ConnectedSpace Z := isConnected_iff_connectedSpace.mp hZ.2
  set f : Z → X := fun w => w.1.1 with hfdef
  have hf : Continuous f := continuous_fst.comp continuous_subtype_val
  have hS : range f = univ := by
    rw [show f = Prod.fst ∘ Subtype.val from rfl, range_comp, Subtype.range_coe, h1]
  obtain ⟨k₀, hk₀⟩ := hK.2.nonempty
  obtain ⟨w₀, hw₀, hw₀k⟩ := h1.symm ▸ mem_univ k₀
  set x₀ : Z := ⟨w₀, hw₀⟩
  have hx₀ : f x₀ ∈ K := by show w₀.1 ∈ K; rw [hw₀k]; exact hk₀
  have hcook := cook67_theorem4 hf hS hHI hK (subset_univ K) hx₀
  set C := connectedComponentIn (f ⁻¹' K) x₀
  have hCc : IsCompact C :=
    (isClosed_connectedComponentIn_of_isClosed' (hK.1.isClosed.preimage hf) x₀).isCompact
  set W : Set (X × X) := Subtype.val '' C with hWdef
  have hWZ : W ⊆ Z := Subtype.coe_image_subset _ _
  have hW : Fold.Q78.IsContinuum W :=
    ⟨hCc.image continuous_subtype_val, IsConnected.image (isConnected_connectedComponentIn_iff.2
      (show x₀ ∈ f ⁻¹' K from hx₀)) Subtype.val continuous_subtype_val.continuousOn⟩
  have hW1 : Prod.fst '' W = K := by rw [image_image]; exact hcook
  clear_value W
  set G := Prod.snd '' W with hGdef
  have hG : Fold.Q78.IsContinuum G :=
    ⟨hW.1.image continuous_snd, hW.2.image _ continuous_snd.continuousOn⟩
  -- §5.7: `g(Cᵢ)` is proper
  have hGu : G ≠ univ := by
    intro hGu
    rcases hred with h2 | hmin
    · exact h2 (eq_univ_of_univ_subset (hGu ▸ image_mono hWZ))
    · have := hmin W hWZ hW hGu
      rw [this, h1] at hW1
      exact hKu hW1.symm
  -- §5.6
  obtain ⟨y, hy⟩ := hG.2.nonempty
  obtain ⟨x, hxK, hxy⟩ := hKd y
  obtain ⟨h, hxy', hmove⟩ := heff x y hxy
  set H := h '' K with hHdef
  have hH : Fold.Q78.IsContinuum H := ⟨hK.1.image h.continuous, hK.2.image _ h.continuous.continuousOn⟩
  have hHu : H ≠ univ := by
    intro hHu
    apply hKu
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨k, hk, hkz⟩ := (hHu ▸ mem_univ (h z) : h z ∈ H)
    exact h.injective hkz ▸ hk
  -- §5.8
  set W' : Set (X × X) := Prod.map h id '' W
  have hW' : Fold.Q78.IsContinuum W' :=
    ⟨hW.1.image (h.continuous.prodMap continuous_id),
      hW.2.image _ (h.continuous.prodMap continuous_id).continuousOn⟩
  have hoff' : OffDiag W' := by
    rintro _ ⟨p, hp, rfl⟩ hpe
    have h1' := hdα p (hWZ hp)
    have h2' := hmove p.1
    simp only [Prod.map_fst, Prod.map_snd, id] at hpe
    rw [hpe, dist_comm] at h2'
    linarith
  have hW'1 : Prod.fst '' W' = H := by
    rw [hHdef, ← hW1, image_image, image_image]; rfl
  have hW'2 : Prod.snd '' W' = G := by rw [image_image]; rfl
  rcases nested_of_hi hHI hG hH (subset_univ _) (subset_univ _)
      ⟨y, hy, hxy' ▸ mem_image_of_mem h hxK⟩ with hGH | hHG
  · refine h35 H hH hHu ⟨W', ?_, hW', hoff', hW'1⟩
    intro p hp
    exact ⟨hW'1 ▸ mem_image_of_mem _ hp, hGH (hW'2 ▸ mem_image_of_mem _ hp)⟩
  · refine h35 G hG hGu ⟨Prod.swap '' W', ?_, isContinuum_swap hW', offDiag_swap hoff', by
      rw [fst_image_swap, hW'2]⟩
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hW'2 ▸ mem_image_of_mem _ hp, hHG (hW'1 ▸ mem_image_of_mem _ hp)⟩

end Thm36


/-- **O–T Corollary 3.5** (p. 139), as a named claim: "If `X` is an indecomposable, homogeneous
plane continuum, then every proper subcontinuum of `X` has surjective semi-span equal to zero." -/
def OTCor35 : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M → ¬ IsDecomposableSpace M →
    ∀ A : Set M, Fold.Q78.IsContinuum A → A ≠ univ → ¬ SurjSemiSpanPos A

/-- **Theorem C** (Hoehn–Oversteegen 2016, p. 180): "Every homogeneous indecomposable plane
continuum has span zero." -/
def TheoremC : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M → ¬ IsDecomposableSpace M →
    HOSpanZero M

/-- **O–T Theorem 3.6, second sentence** (p. 140), from Corollary 3.5. -/
theorem ot82_theorem36_of_cor35 (h35 : OTCor35) (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) : SemiSpanZero M := by
  intro A hA hpos
  by_cases hAu : A = univ
  · subst hAu
    exact not_surjSemiSpanPos_univ hX hi (hagopian76_theorem1 M hX hi)
      (fun A hA hAu => h35 M hX hi A hA hAu) hpos
  · exact h35 M hX hi A hA hAu hpos

/-- **§5.9**: Theorem C from Corollary 3.5. -/
theorem theoremC_of_cor35 (h35 : OTCor35) : TheoremC := fun M _ _ hX hi =>
  semiSpanZero_iff_hoSpanZero.1 (ot82_theorem36_of_cor35 h35 M hX hi)

end HPC.Span
