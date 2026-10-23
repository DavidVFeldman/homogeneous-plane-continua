import HPC.Hagopian.H76NoSep
import HPC.Hagopian.H76D1
import HPC.Hagopian.H76BDefs
import HPC.Moore.M25C

/-!
# Batch 157, item E: the set-up of Theorem 1 (Hagopian 1976, pp. 344–345)

* `elt_layerSetoid_of_mem`, `elt_layerSetoid_of_notMem`: the elements of `S` are the layers of `E`
  and the points off `E`.
* `layerSetoid_mooreDecomp_aux`: `S` satisfies Moore 1925's hypotheses. The layers are compact and
  connected; they do not separate the plane by `no_proper_subcontinuum_separates_aux`; Moore's
  upper semicontinuity comes from the continuity of `k` and compactness (`layer_usc`). Lemma 5 is
  not used.
* `exists_quotient_plane_aux`: `π` is the quotient map followed by the homeomorphism of Moore 1925
  Theorem 22; `t ↦ π(k⁻¹(t))` is a continuous injection of `[0, 1]` onto `π[E]`.
* `exists_accessible_point`: a point of `M` nearest to a point off `M` is the end of a straight
  segment meeting `M` only there.
* `exists_accessible_typeA'_aux`: that point is moved into an interior layer by a homeomorphism of
  `M` (homogeneity); the image of `E` is again of type A′ (`exists_image_map`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Setup

variable {M : Set Pt}

/-! ### The elements of `S` -/

theorem layerKey_of_mem {E : Set M} (k : E → unitInterval) (e : E) :
    layerKey k ((e : M) : Pt) = Sum.inl (k e) := by
  have h : ∃ hM : ((e : M) : Pt) ∈ M, (⟨(e : M), hM⟩ : M) ∈ E := ⟨(e : M).2, e.2⟩
  simp only [layerKey, dif_pos h]

theorem layerKey_of_notMem {E : Set M} (k : E → unitInterval) {p : Pt} (hp : p ∉ toPt E) :
    layerKey k p = Sum.inr p := by
  have h : ¬ ∃ hM : p ∈ M, (⟨p, hM⟩ : M) ∈ E := fun ⟨hM, hE⟩ => hp ⟨⟨p, hM⟩, hE, rfl⟩
  simp only [layerKey, dif_neg h]

theorem mem_toPt_iff {E : Set M} {p : Pt} : p ∈ toPt E ↔ ∃ e : E, ((e : M) : Pt) = p :=
  ⟨fun ⟨m, hm, h⟩ => ⟨⟨m, hm⟩, h⟩, fun ⟨e, h⟩ => ⟨e, e.2, h⟩⟩

/-- The layer `k⁻¹(t)` as a subset of the plane. -/
theorem toPt_layer_eq {E : Set M} (k : E → unitInterval) (t : unitInterval) :
    toPt (layer k t) = {p | ∃ e : E, k e = t ∧ ((e : M) : Pt) = p} := by
  ext p; constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩; exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, ⟨e, he, rfl⟩, rfl⟩

theorem elt_layerSetoid_of_mem {E : Set M} (k : E → unitInterval) (e : E) :
    HPC.Moore.elt (layerSetoid k) ((e : M) : Pt) = toPt (layer k (k e)) := by
  rw [toPt_layer_eq]
  ext p
  simp only [HPC.Moore.elt, mem_setOf_eq]
  change layerKey k p = layerKey k ((e : M) : Pt) ↔ _
  rw [layerKey_of_mem]
  constructor
  · intro h
    by_cases hp : p ∈ toPt E
    · obtain ⟨e', rfl⟩ := mem_toPt_iff.1 hp
      rw [layerKey_of_mem] at h
      exact ⟨e', Sum.inl_injective h, rfl⟩
    · rw [layerKey_of_notMem k hp] at h; cases h
  · rintro ⟨e', he', rfl⟩
    rw [layerKey_of_mem, he']

theorem elt_layerSetoid_of_notMem {E : Set M} (k : E → unitInterval) {x : Pt} (hx : x ∉ toPt E) :
    HPC.Moore.elt (layerSetoid k) x = {x} := by
  ext p
  simp only [HPC.Moore.elt, mem_setOf_eq, mem_singleton_iff]
  change layerKey k p = layerKey k x ↔ _
  rw [layerKey_of_notMem k hx]
  constructor
  · intro h
    by_cases hp : p ∈ toPt E
    · obtain ⟨e', rfl⟩ := mem_toPt_iff.1 hp
      rw [layerKey_of_mem] at h; cases h
    · rw [layerKey_of_notMem k hp] at h; exact Sum.inr_injective h
  · rintro rfl; rw [layerKey_of_notMem k hx]

/-! ### Moore's upper semicontinuity of the layers -/

/-- **Upper semicontinuity of the layers**, in Moore's form: a layer that comes within `d` of the
layer `k⁻¹(t)` lies within `e` of it. (Continuity of `k` on the compact `E`.) -/
theorem layer_usc {E : Set M} [CompactSpace E] {k : E → unitInterval} (hk : Continuous k)
    (t : unitInterval) (htne : (layer k t).Nonempty) {e : ℝ} (he : 0 < e) :
    ∃ d > 0, ∀ s : unitInterval, (∃ p ∈ toPt (layer k s), infDist p (toPt (layer k t)) < d) →
      ∀ p ∈ toPt (layer k s), infDist p (toPt (layer k t)) < e := by
  set Lt := toPt (layer k t) with hLt
  have hLtc : IsCompact Lt := by
    refine ((isClosed_singleton.preimage hk).isCompact.image continuous_subtype_val).image
      continuous_subtype_val
  have hLtne : Lt.Nonempty := htne.image _
  set g : E → ℝ := fun z => infDist ((z : M) : Pt) Lt with hg
  have hgc : Continuous g :=
    (continuous_infDist_pt Lt).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hg0 : ∀ z : E, k z = t → g z = 0 := fun z hz =>
    infDist_zero_of_mem ⟨(z : M), ⟨z, hz, rfl⟩, rfl⟩
  have hgpos : ∀ z : E, k z ≠ t → 0 < g z := fun z hz => by
    refine (hLtc.isClosed.notMem_iff_infDist_pos hLtne).1 fun hm => hz ?_
    rw [hLt, toPt_layer_eq] at hm
    obtain ⟨e', he', hee'⟩ := hm
    have : e' = z := Subtype.ext (Subtype.ext hee')
    rw [← this, he']
  -- `C = {g ≥ e}` and its image
  set C : Set E := {z | e ≤ g z} with hC
  have hCc : IsCompact C := (isClosed_le continuous_const hgc).isCompact
  have hkC : IsClosed (k '' C) := (hCc.image hk).isClosed
  have htC : t ∉ k '' C := by
    rintro ⟨z, hz, hzt⟩
    have : e ≤ g z := hz
    rw [hg0 z hzt] at this; linarith
  set W : Set E := k ⁻¹' (k '' C)ᶜ with hW
  have hWo : IsOpen W := hkC.isOpen_compl.preimage hk
  have hWc : IsCompact Wᶜ := hWo.isClosed_compl.isCompact
  -- a positive lower bound of `g` off `W`
  obtain ⟨d₀, hd₀, hd₀W⟩ : ∃ d₀ > 0, ∀ z ∈ Wᶜ, d₀ ≤ g z := by
    rcases (Wᶜ).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun z hz => by rw [h] at hz; exact absurd hz (notMem_empty z)⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hWc.exists_isMinOn h hgc.continuousOn
      refine ⟨g z₁, hgpos z₁ fun hzt => hz₁ ?_, fun z hz => hmin hz⟩
      show k z₁ ∈ (k '' C)ᶜ
      rw [hzt]; exact htC
  refine ⟨min e d₀, lt_min he hd₀, fun s ⟨p, hp, hpd⟩ p' hp' => ?_⟩
  rw [toPt_layer_eq] at hp hp'
  obtain ⟨z, hzs, rfl⟩ := hp
  obtain ⟨z', hz's, rfl⟩ := hp'
  have hzW : z ∈ W := by
    by_contra hzW
    have := hd₀W z hzW
    have : g z < min e d₀ := hpd
    linarith [min_le_right e d₀]
  have hsC : s ∉ k '' C := by rw [← hzs]; exact hzW
  have hz'C : z' ∉ C := fun h => hsC ⟨z', h, hz's⟩
  simp only [hC, mem_setOf_eq, not_le] at hz'C
  exact hz'C

variable [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
theorem isCompact_toPt {E : Set M} (hE : IsCompact E) : IsCompact (toPt E) :=
  hE.image continuous_subtype_val

omit [CompactSpace M] [ConnectedSpace M] in
/-- A layer of a type A′ continuum is a proper subset of `M`. -/
theorem layer_ne_univ {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (t : unitInterval) : layer k t ≠ univ := by
  intro h
  obtain ⟨⟨a, b, hab⟩, -, hint⟩ := hE
  have hall : ∀ e : E, k e = t := fun e => by
    have : (e : M) ∈ layer k t := h ▸ mem_univ _
    obtain ⟨e', he', hee'⟩ := this
    rw [← Subtype.ext hee']; exact he'
  have : k ⁻¹' {t} = univ := eq_univ_of_forall hall
  have h2 := hint t
  rw [this, interior_univ] at h2
  exact (eq_empty_iff_forall_notMem.1 h2) ⟨a, hab.2.1⟩ (mem_univ _)

omit [CompactSpace M] [ConnectedSpace M] in
theorem isContinuum_layer_min {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (t : unitInterval) : Fold.Q78.IsContinuum (layer k t) :=
  isContinuum_layer hE.isCompact hE.2.1 t

/-- **`S` satisfies Moore 1925's hypotheses.** -/
theorem layerSetoid_mooreDecomp_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    HPC.Moore.MooreDecomp (layerSetoid k) := by
  have hEc := hE.isCompact
  haveI : CompactSpace E := isCompact_iff_compactSpace.1 hEc
  have hk : Continuous k := hE.2.1.1
  have hTc : IsCompact (toPt E) := isCompact_toPt hEc
  have hlayer : ∀ e : E, Fold.Q78.IsContinuum (toPt (layer k (k e))) := fun e =>
    isContinuum_val_image (isContinuum_layer_min hE (k e))
  have hpt : ∀ x : Pt, ¬ SeparatesPlane {x} := fun x hs =>
    hs (isConnected_compl_singleton_of_one_lt_rank (by simp; norm_num) x)
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x e he => ?_⟩
  · by_cases hx : x ∈ toPt E
    · obtain ⟨e, rfl⟩ := mem_toPt_iff.1 hx
      rw [elt_layerSetoid_of_mem]; exact (hlayer e).1
    · rw [elt_layerSetoid_of_notMem k hx]; exact isCompact_singleton
  · by_cases hx : x ∈ toPt E
    · obtain ⟨e, rfl⟩ := mem_toPt_iff.1 hx
      rw [elt_layerSetoid_of_mem]; exact (hlayer e).2
    · rw [elt_layerSetoid_of_notMem k hx]; exact isConnected_singleton
  · by_cases hx : x ∈ toPt E
    · obtain ⟨e, rfl⟩ := mem_toPt_iff.1 hx
      rw [elt_layerSetoid_of_mem]
      exact no_proper_subcontinuum_separates_aux hX hi (isContinuum_layer_min hE (k e))
        (layer_ne_univ hE (k e))
    · rw [elt_layerSetoid_of_notMem k hx]; exact hpt x
  · by_cases hx : x ∈ toPt E
    · obtain ⟨e₀, rfl⟩ := mem_toPt_iff.1 hx
      rw [elt_layerSetoid_of_mem]
      obtain ⟨d, hd, hdu⟩ := layer_usc hk (k e₀) ⟨(e₀ : M), e₀, rfl, rfl⟩ he
      refine ⟨min d e, lt_min hd he, fun y ⟨p, hp, hpd⟩ p' hp' => ?_⟩
      by_cases hy : y ∈ toPt E
      · obtain ⟨e₁, rfl⟩ := mem_toPt_iff.1 hy
        rw [elt_layerSetoid_of_mem] at hp hp'
        exact hdu (k e₁) ⟨p, hp, lt_of_lt_of_le hpd (min_le_left _ _)⟩ p' hp'
      · rw [elt_layerSetoid_of_notMem k hy] at hp hp'
        rw [mem_singleton_iff.1 hp'] ; rw [mem_singleton_iff.1 hp] at hpd
        exact lt_of_lt_of_le hpd (min_le_right _ _)
    · rw [elt_layerSetoid_of_notMem k hx]
      have hEne : (toPt E).Nonempty := by
        obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE
        exact ⟨_, a, hab.2.1, rfl⟩
      have hρ : 0 < infDist x (toPt E) := (hTc.isClosed.notMem_iff_infDist_pos hEne).1 hx
      refine ⟨min e (infDist x (toPt E)), lt_min he hρ, fun y ⟨p, hp, hpd⟩ p' hp' => ?_⟩
      rw [infDist_singleton] at hpd ⊢
      by_cases hy : y ∈ toPt E
      · exfalso
        obtain ⟨e₁, rfl⟩ := mem_toPt_iff.1 hy
        rw [elt_layerSetoid_of_mem] at hp
        have hpE : p ∈ toPt E := by
          obtain ⟨_, ⟨z, -, rfl⟩, rfl⟩ := hp; exact ⟨z, z.2, rfl⟩
        have h1 : infDist x (toPt E) ≤ dist x p := infDist_le_dist_of_mem hpE
        rw [dist_comm] at h1
        linarith [min_le_right e (infDist x (toPt E))]
      · rw [elt_layerSetoid_of_notMem k hy] at hp hp'
        rw [mem_singleton_iff.1 hp']; rw [mem_singleton_iff.1 hp] at hpd
        exact lt_of_lt_of_le hpd (min_le_left _ _)

/-! ### The quotient `R²/S` and the arc `π[E]` -/

/-- **The quotient map onto the plane, and the arc `π[E]`.** -/
theorem exists_quotient_plane_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ π : Pt → Pt, IsQuotientMap π ∧ (∀ p q, π p = π q ↔ layerSetoid k p q) ∧
      Nonempty (π '' toPt E ≃ₜ unitInterval) := by
  have hm := layerSetoid_mooreDecomp_aux hX hi hE
  obtain ⟨φ⟩ := HPC.Moore.m25_theorem22 hm
  set π : Pt → Pt := fun p => φ (Quotient.mk (layerSetoid k) p) with hπ
  have hπq : IsQuotientMap π := φ.isQuotientMap.comp isQuotientMap_quotient_mk'
  have hπeq : ∀ p q, π p = π q ↔ layerSetoid k p q := fun p q => by
    simp only [hπ, φ.injective.eq_iff]
    exact Quotient.eq
  refine ⟨π, hπq, hπeq, ?_⟩
  -- the arc
  haveI : CompactSpace E := isCompact_iff_compactSpace.1 hE.isCompact
  have hk : Continuous k := hE.2.1.1
  have hks : Function.Surjective k := hE.2.1.2.1
  choose σ hσ using hks
  set γ : unitInterval → Pt := fun t => π ((σ t : M) : Pt) with hγ
  have hrel : ∀ e : E, layerSetoid k ((σ (k e) : M) : Pt) ((e : M) : Pt) := fun e => by
    change layerKey k _ = layerKey k _
    rw [layerKey_of_mem, layerKey_of_mem, hσ]
  have hγk : γ ∘ k = fun e : E => π ((e : M) : Pt) := funext fun e => (hπeq _ _).2 (hrel e)
  have hkq : IsQuotientMap k := (hk.isClosedMap).isQuotientMap hk (hE.2.1.2.1)
  have hγc : Continuous γ := by
    rw [hkq.continuous_iff, hγk]
    exact hπq.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hγi : Function.Injective γ := fun t t' h => by
    have := (hπeq _ _).1 h
    change layerKey k _ = layerKey k _ at this
    rw [layerKey_of_mem, layerKey_of_mem, hσ, hσ] at this
    exact Sum.inl_injective this
  have hrange : range γ = π '' toPt E := by
    ext z; constructor
    · rintro ⟨t, rfl⟩; exact ⟨_, ⟨(σ t : M), (σ t).2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨k ⟨m, hm⟩, ?_⟩
      have := congrFun hγk ⟨m, hm⟩
      simpa using this
  have e₁ : unitInterval ≃ₜ range γ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective γ hγi) (hγc.subtype_mk _)
  exact ⟨(Homeomorph.setCongr hrange.symm).trans e₁.symm⟩

/-! ### Accessibility -/

omit [ConnectedSpace M] in
/-- **Some point of `M` is accessible from `R² − M`**: a point of `M` nearest to a point `x` off `M`
is the end of the straight segment from `x`, which meets `M` only there. -/
theorem exists_accessible_point (hne : M.Nonempty) : ∃ p ∈ M, IsAccessibleFrom M p := by
  have hMc : IsCompact M := isCompact_iff_compactSpace.2 inferInstance
  obtain ⟨R, hR⟩ := hMc.isBounded.subset_closedBall (0 : Pt)
  set x : Pt := (|R| + 1, 0)
  have hxM : x ∉ M := by
    intro h
    have := hR h
    simp only [x, mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, norm_zero] at this
    rw [abs_of_pos (by positivity : (0:ℝ) < |R| + 1)] at this
    linarith [le_abs_self R, le_max_left (|R| + 1) 0]
  obtain ⟨p, hpM, hpd⟩ := hMc.exists_infDist_eq_dist hne x
  have hxp : x ≠ p := fun h => hxM (h ▸ hpM)
  set f : unitInterval → Pt := fun t => AffineMap.lineMap x p (t : ℝ) with hf
  refine ⟨p, hpM, x, range f, ⟨hxp, f, ?_, rfl, ?_, ?_⟩, ?_⟩
  · have hc : Continuous f := (AffineMap.lineMap_continuous).comp continuous_subtype_val
    refine (hc.isClosedEmbedding fun s t hst => ?_).isEmbedding
    exact Subtype.ext ((AffineMap.lineMap_injective ℝ hxp) hst)
  · simp [hf]
  · simp [hf]
  · ext z
    simp only [mem_inter_iff, mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, rfl⟩, hzM⟩
      simp only [hf] at hzM ⊢
      by_contra hne'
      have ht : (t : ℝ) < 1 := by
        rcases lt_or_eq_of_le t.2.2 with h | h
        · exact h
        · exact absurd (by simp [h]) hne'
      have h1 : dist x (AffineMap.lineMap x p (t : ℝ)) = |(t : ℝ)| * dist x p := by
        rw [dist_left_lineMap, Real.norm_eq_abs]
      have h2 : infDist x M ≤ dist x (AffineMap.lineMap x p (t : ℝ)) := infDist_le_dist_of_mem hzM
      rw [hpd, h1, abs_of_nonneg t.2.1] at h2
      have hd : 0 < dist x p := dist_pos.2 hxp
      nlinarith
    · rintro rfl
      exact ⟨⟨1, by simp [hf]⟩, hpM⟩

/-- **An accessible point in an interior layer** (p. 345, "we can assume without loss of generality
that `k⁻¹[(0, 1)]` is accessible from `R² − M`"). -/
theorem exists_accessible_typeA'_aux (hX : IsHomogeneous M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) :
    ∃ (E' : Set M) (k' : E' → unitInterval) (h : M ≃ₜ M), E' = h '' E ∧
      IsMinimalAdmissible E' k' ∧ ∃ p ∈ layerSet k' (Ioo 0 1), IsAccessibleFrom M (p : Pt) := by
  obtain ⟨m₀⟩ : Nonempty M := inferInstance
  obtain ⟨p, hpM, hacc⟩ := exists_accessible_point (M := M) ⟨m₀, m₀.2⟩
  set half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨e, he⟩ := hE.2.1.2.1 half
  obtain ⟨h, hh⟩ := hX (e : M) ⟨p, hpM⟩
  obtain ⟨b, hb, hbl⟩ := exists_image_map h hE
  refine ⟨h '' E, b, h, rfl, hb, ⟨p, hpM⟩, ?_, hacc⟩
  rw [hbl]
  refine ⟨(e : M), ⟨e, ?_, rfl⟩, hh⟩
  show k e ∈ Ioo 0 1
  rw [he]
  constructor
  · show (0 : ℝ) < 1 / 2; norm_num
  · show (1 / 2 : ℝ) < 1; norm_num

end Setup

end HPC.Hagopian
