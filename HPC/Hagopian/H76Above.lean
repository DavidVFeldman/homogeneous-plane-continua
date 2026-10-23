import HPC.Hagopian.H76Reparam

/-!
# Batch 164, item B (first part): points of `π[M]` above `π[E]`, and an accessible one

Commission 164 §1 B.1. `no_M_below` gives a strip below `γ([a, b])` missing `π[M]`. If a strip above
also missed `π[M]`, the preimage of the two strips together with `γ((a, b))` would be an open set of
`R²` meeting `M` only inside the proper subcontinuum `k⁻¹[[a, b]]`, which would then have interior
in `M`: impossible in an indecomposable continuum (`M_meets_above`). An accessible point of `M − E`
above `π[E]` is then the first point of `π[M]` met on a segment, in collar coordinates, from a point
of the complement to a point of `π[M]` (`exists_accessible_above`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Above

variable {M : Set Pt}

/-! ## `π` off `E` -/

/-- Two points of the plane with the same image under `π`, one of them off `E`, are equal. -/
theorem eq_of_pi_eq_off {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {z u : Pt} (hu : u ∉ toPt E)
    (h : π z = π u) : z = u := by
  have hrel := (hπS z u).1 h
  change layerKey k z = layerKey k u at hrel
  rw [layerKey_of_notMem k hu] at hrel
  by_cases hz : z ∈ toPt E
  · obtain ⟨e, he⟩ := mem_toPt_iff.1 hz
    rw [← he, layerKey_of_mem] at hrel
    exact absurd hrel Sum.inl_ne_inr
  · rw [layerKey_of_notMem k hz] at hrel
    exact Sum.inr_injective hrel

/-- A point of `E` goes into `range γ`. -/
theorem pi_mem_range_of_mem {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {z : Pt}
    (hz : z ∈ toPt E) : π z ∈ range γ := by
  obtain ⟨e, rfl⟩ := mem_toPt_iff.1 hz
  exact ⟨k e, (hγπ (k e) _ ⟨e, ⟨e, rfl, rfl⟩, rfl⟩).symm⟩

/-- `π` is an open map on the complement of `E`. -/
theorem pi_isOpen_image_off {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {U : Set Pt}
    (hU : IsOpen U) (hUE : Disjoint U (toPt E)) : IsOpen (π '' U) := by
  rw [← hπ.isOpen_preimage]
  have : π ⁻¹' (π '' U) = U := by
    apply Subset.antisymm
    · rintro z ⟨u, hu, hzu⟩
      rw [eq_of_pi_eq_off hπS (disjoint_left.1 hUE hu) hzu.symm]; exact hu
    · exact subset_preimage_image π U
  rw [this]; exact hU

/-! ## B.1: `π[M]` approaches `γ([a, b])` from above -/

/-- **Points of `π[M]` just above `π[E]`** (commission 164 §1 B.1). If, over `[a, b] ⊆ (0, 1)`
(`a < b`), some strip below `γ([a, b])` misses `π[M]` (as `no_M_below` gives), then every strip
above `γ((a, b))` meets `π[M]`. -/
theorem M_meets_above [CompactSpace M] [ConnectedSpace M] (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {c : ℝ} (hc : 0 < c) : (F '' (Ioo a b ×ˢ Ioo 0 c) ∩ π '' M).Nonempty := by
  obtain ⟨c', hc', hdis⟩ := hbelow
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hk := hE.2.1.2.1
  set c'' := min (min c c') 1 with hc''
  have hc''0 : 0 < c'' := lt_min (lt_min hc hc') one_pos
  have hc''c : c'' ≤ c := (min_le_left _ _).trans (min_le_left _ _)
  have hc''c' : c'' ≤ c' := (min_le_left _ _).trans (min_le_right _ _)
  have hc''1 : c'' ≤ 1 := min_le_right _ _
  set W := Ioo a b ×ˢ Ioo (-c'') c'' with hW
  have hWO : W ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := fun q hq =>
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  have hUo : IsOpen (F '' W) := hF.isOpen_image (isOpen_Ioo.prod isOpen_Ioo) hWO
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha.le, by linarith⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hb.le⟩
  set H : Set M := Subtype.val '' (k ⁻¹' Icc ⟨a, haI⟩ ⟨b, hbI⟩) with hH
  -- points of `M` over the window lie in `H`
  have hsub : ∀ m : M, π m ∈ F '' W → m ∈ H := by
    rintro m ⟨⟨s, r⟩, ⟨hs, hr⟩, hsr⟩
    rcases lt_trichotomy r 0 with hr0 | rfl | hr0
    · exfalso
      exact disjoint_left.1 hdis ⟨(s, r), ⟨⟨hs.1.le, hs.2.le⟩, by linarith [hr.1], hr0⟩, hsr⟩
        ⟨m, m.2, rfl⟩
    · have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h1 : π m = γ ⟨s, hsI⟩ := by rw [← hsr]; exact hF.2.1 ⟨s, hsI⟩
      obtain ⟨e, he, hem⟩ := mem_layer_of_pi_eq hk hπS hγπ h1
      refine ⟨e, ?_, hem⟩
      show k e ∈ Icc _ _
      rw [show k e = ⟨s, hsI⟩ from he]
      exact ⟨Subtype.mk_le_mk.2 hs.1.le, Subtype.mk_le_mk.2 hs.2.le⟩
    · exfalso
      have : π m ∈ F '' (Ioo a b ×ˢ Ioo 0 c) ∩ π '' M :=
        ⟨⟨(s, r), ⟨hs, hr0, by linarith [hr.2]⟩, hsr⟩, ⟨m, m.2, rfl⟩⟩
      rw [hne] at this; exact this
  -- the open set of `M` over the window
  set V : Set M := {m : M | π m ∈ F '' W} with hV
  have hVo : IsOpen V := hUo.preimage (hπc.comp continuous_subtype_val)
  have hmid : (a + b) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨e₀, he₀⟩ := hk ⟨(a + b) / 2, hmid⟩
  have hV0 : (e₀ : M) ∈ V := by
    show π ((e₀ : M) : Pt) ∈ F '' W
    rw [hγπ _ _ ⟨e₀, ⟨e₀, he₀, rfl⟩, rfl⟩, ← hF.2.1]
    exact ⟨_, ⟨⟨by linarith, by linarith⟩, by linarith, hc''0⟩, rfl⟩
  have hint : (interior H).Nonempty :=
    ⟨e₀, interior_maximal (fun m hm => hsub m hm) hVo hV0⟩
  -- `H` is a proper subcontinuum
  have hHc : Fold.Q78.IsContinuum H :=
    isContinuum_img hE.isCompact hE.2.1 isClosed_Icc isPreconnected_Icc
      (nonempty_Icc.2 (Subtype.mk_le_mk.2 hab.le))
  obtain ⟨e₁, he₁⟩ := hk 0
  have hHu : H ≠ univ := by
    intro h
    have : (e₁ : M) ∈ H := h ▸ mem_univ _
    obtain ⟨e, he, hee⟩ := this
    have : e = e₁ := Subtype.ext hee
    subst this
    have h2 : (⟨a, haI⟩ : unitInterval) ≤ k e := he.1
    rw [he₁] at h2
    exact absurd (Subtype.mk_le_mk.1 h2) (not_le.2 ha)
  rw [interior_eq_empty_of_proper hi hHc hHu] at hint
  exact not_nonempty_empty hint

/-! ## `π[M]` has no interior off `π[E]` -/

/-- **`π[M]` contains no open set off `π[E]`**: such an open set would pull back to an open subset
of the plane inside `M`, and a small closed disc in it would be a proper subcontinuum of `M` with
interior. -/
theorem exists_notMem_piM [CompactSpace M] [ConnectedSpace M] (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {W : Set Pt} (hWo : IsOpen W)
    (hWne : W.Nonempty) (hWγ : Disjoint W (range γ)) : ∃ w ∈ W, w ∉ π '' M := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨w₀, hw₀⟩ := hWne
  obtain ⟨m₀, hm₀M, hm₀⟩ := hcon w₀ hw₀
  have hEc : IsClosed (toPt E) := (isCompact_toPt hE.isCompact).isClosed
  have hoff : ∀ z, π z ∈ W → z ∉ toPt E := fun z hz hzE =>
    disjoint_left.1 hWγ hz (pi_mem_range_of_mem hγπ hzE)
  set U := π ⁻¹' W ∩ (toPt E)ᶜ with hU
  have hUo : IsOpen U := (hWo.preimage hπ.continuous).inter hEc.isOpen_compl
  have hUM : U ⊆ M := by
    rintro z ⟨hzW, hzE⟩
    obtain ⟨m, hm, hmz⟩ := hcon _ hzW
    have hmE : m ∉ toPt E := hoff m (hmz ▸ hzW)
    rw [eq_of_pi_eq_off hπS hmE hmz.symm]; exact hm
  have hm₀W : π m₀ ∈ W := by rw [hm₀]; exact hw₀
  have hm₀U : m₀ ∈ U := ⟨hm₀W, hoff m₀ hm₀W⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo m₀ hm₀U
  -- the closed disc of radius `r/2` as a subset of `M`
  set H : Set M := Subtype.val ⁻¹' closedBall m₀ (r / 2) with hH
  have hBM : closedBall m₀ (r / 2) ⊆ M := fun z hz =>
    hUM (hball (closedBall_subset_ball (by linarith) hz))
  have himg : Subtype.val '' H = closedBall m₀ (r / 2) := by
    rw [hH, Subtype.image_preimage_coe, inter_eq_right.2 hBM]
  have hHc : Fold.Q78.IsContinuum H := by
    refine ⟨(isClosed_closedBall.preimage continuous_subtype_val).isCompact, ?_, ?_⟩
    · exact ⟨⟨m₀, hm₀M⟩, by simp [hH, (half_pos hr).le]⟩
    · rw [← IsInducing.subtypeVal.isPreconnected_image, himg]
      exact (convex_closedBall m₀ (r / 2)).isPreconnected
  set z₁ : Pt := m₀ + (3 * r / 4, 0) with hz₁
  have hz₁d : dist z₁ m₀ = 3 * r / 4 := by
    rw [hz₁, dist_eq_norm, add_sub_cancel_left, Prod.norm_def]
    simp only [norm_zero, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith), max_eq_left (by linarith)]
  have hz₁M : z₁ ∈ M := hUM (hball (by rw [mem_ball, hz₁d]; linarith))
  have hHu : H ≠ univ := by
    intro h
    have : (⟨z₁, hz₁M⟩ : M) ∈ H := h ▸ mem_univ _
    have h2 : dist z₁ m₀ ≤ r / 2 := this
    rw [hz₁d] at h2; linarith
  have hint : (interior H).Nonempty := by
    have hsub : (Subtype.val ⁻¹' ball m₀ (r / 2) : Set M) ⊆ H :=
      preimage_mono ball_subset_closedBall
    have hin : (⟨m₀, hm₀M⟩ : M) ∈ (Subtype.val ⁻¹' ball m₀ (r / 2) : Set M) :=
      mem_ball_self (half_pos hr)
    exact ⟨_, interior_maximal hsub (isOpen_ball.preimage continuous_subtype_val) hin⟩
  rw [interior_eq_empty_of_proper hi hHc hHu] at hint
  exact not_nonempty_empty hint

end Above

end HPC.Hagopian
