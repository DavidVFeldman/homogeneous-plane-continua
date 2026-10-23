import HPC.Hagopian.Hagopian76AB

/-!
# Batch 184, §3: monotone images and the plane quotient (Hagopian 1984, p. 346)

Commission 184 §3, pieces 1–2 of the assembly of Jones's plan.

* `isPreconnected_preimage_of_monotone`: for a continuous surjection `q` of a compact space onto a
  Hausdorff space with connected fibres, the preimage of a (pre)connected set is (pre)connected.
* `isDecomposableSpace_of_monotone_image`: a decomposition of the image lifts to one of the domain;
  hence a monotone image of an indecomposable continuum is indecomposable.
* `fibreSetoid`: the decomposition of the plane into the fibres of `q : M → Y` and the points off
  `M` (as `layerSetoid`, `H76BDefs.lean`, with a map onto any `Y` in place of a map onto `[0, 1]`).
* `fibreSetoid_mooreDecomp`: it satisfies Moore 1925's hypotheses when every fibre is a proper
  subcontinuum of a homogeneous indecomposable plane continuum `M`
  (`no_proper_subcontinuum_separates`; Moore's upper semicontinuity from compactness, `fibre_usc`).
* `exists_plane_quotient_of_monotone_aux`: by Moore 1925 Theorem 22 (`m25_theorem22`) the quotient of
  the plane is the plane, and `Y` is homeomorphic to the image of `M`, a compact plane set.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ### Monotone maps -/

section Monotone

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]

/-- **Preimages under a monotone map.** For a continuous surjection `q` of a compact space onto a
Hausdorff space whose fibres are preconnected, the preimage of a preconnected set is
preconnected. -/
theorem isPreconnected_preimage_of_monotone {q : X → Y} (hq : Continuous q)
    (hqs : Function.Surjective q) (hf : ∀ y, IsPreconnected (q ⁻¹' {y})) {A : Set Y}
    (hA : IsPreconnected A) : IsPreconnected (q ⁻¹' A) := by
  rw [isPreconnected_closed_iff] at hA ⊢
  intro u v hu hv huv hu' hv'
  have hqc : IsClosedMap q := hq.isClosedMap
  obtain ⟨y, hyA, ⟨x₁, hx₁u, hx₁y⟩, ⟨x₂, hx₂v, hx₂y⟩⟩ :=
    hA (q '' u) (q '' v) (hqc u hu) (hqc v hv) (fun y hy => by
      obtain ⟨x, rfl⟩ := hqs y
      rcases huv (show x ∈ q ⁻¹' A from hy) with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · exact Or.inr ⟨x, h, rfl⟩)
      (by obtain ⟨x, hxA, hxu⟩ := hu'; exact ⟨q x, hxA, x, hxu, rfl⟩)
      (by obtain ⟨x, hxA, hxv⟩ := hv'; exact ⟨q x, hxA, x, hxv, rfl⟩)
  have hF := hf y
  rw [isPreconnected_closed_iff] at hF
  obtain ⟨z, hz, hzu, hzv⟩ := hF u v hu hv
    (fun z hz => huv (by have h : q z = y := hz; show q z ∈ A; rw [h]; exact hyA))
    ⟨x₁, hx₁y, hx₁u⟩ ⟨x₂, hx₂y, hx₂v⟩
  refine ⟨z, ?_, hzu, hzv⟩
  have h : q z = y := hz
  show q z ∈ A
  rw [h]; exact hyA

end Monotone

/-- **Preimages of subcontinua** under a monotone map are subcontinua. -/
theorem isContinuum_preimage_of_monotone {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] {q : X → Y} (hq : Continuous q)
    (hqs : Function.Surjective q) (hf : ∀ y, IsConnected (q ⁻¹' {y})) {A : Set Y}
    (hA : Fold.Q78.IsContinuum A) : Fold.Q78.IsContinuum (q ⁻¹' A) :=
  ⟨(hA.1.isClosed.preimage hq).isCompact,
    hA.2.nonempty.preimage hqs,
    isPreconnected_preimage_of_monotone hq hqs (fun y => (hf y).2) hA.2.2⟩

/-- **§3, monotone images.** If a compact metric space `X` maps onto a metric space `Y` by a
continuous map with connected fibres, a decomposition of `Y` into two proper subcontinua lifts to a
decomposition of `X` (the preimages are proper subcontinua whose union is `X`). -/
theorem isDecomposableSpace_of_monotone_image {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] {q : X → Y} (hq : Continuous q) (hqs : Function.Surjective q)
    (hf : ∀ y, IsConnected (q ⁻¹' {y})) (hY : IsDecomposableSpace Y) : IsDecomposableSpace X := by
  obtain ⟨H, K, hH, hK, hHu, hKu, hHK⟩ := hY
  have hne : ∀ {S : Set Y}, S ≠ univ → q ⁻¹' S ≠ univ := fun {S} hS h =>
    hS (by rw [← hqs.image_preimage S, h, image_univ, hqs.range_eq])
  exact ⟨q ⁻¹' H, q ⁻¹' K, isContinuum_preimage_of_monotone hq hqs hf hH,
    isContinuum_preimage_of_monotone hq hqs hf hK, hne hHu, hne hKu,
    by rw [← preimage_union, hHK, preimage_univ]⟩

/-! ### The decomposition of the plane by the fibres -/

section PlaneQuot

variable {M : Set Pt} {Y : Type*}

open Classical in
/-- The key of the decomposition: a point of `M` goes to its image under `q`, a point off `M` to
itself. -/
noncomputable def fibreKey (q : M → Y) (p : Pt) : Y ⊕ Pt :=
  if h : p ∈ M then Sum.inl (q ⟨p, h⟩) else Sum.inr p

/-- **The decomposition of the plane** into the fibres of `q` and the points off `M` (commission 184
§1, step 3: "Extend `𝔇` by the points of the plane off `M`"). -/
noncomputable def fibreSetoid (q : M → Y) : Setoid Pt :=
  Setoid.ker (fibreKey q)

theorem fibreKey_of_mem (q : M → Y) (m : M) : fibreKey q (m : Pt) = Sum.inl (q m) := by
  simp only [fibreKey, dif_pos m.2, Subtype.coe_eta]

theorem fibreKey_of_notMem (q : M → Y) {p : Pt} (hp : p ∉ M) : fibreKey q p = Sum.inr p := by
  simp only [fibreKey, dif_neg hp]

theorem elt_fibreSetoid_of_mem (q : M → Y) (m : M) :
    HPC.Moore.elt (fibreSetoid q) (m : Pt) = toPt (q ⁻¹' {q m}) := by
  ext p
  simp only [HPC.Moore.elt, mem_setOf_eq]
  change fibreKey q p = fibreKey q (m : Pt) ↔ _
  rw [fibreKey_of_mem]
  constructor
  · intro h
    by_cases hp : p ∈ M
    · rw [show p = ((⟨p, hp⟩ : M) : Pt) from rfl, fibreKey_of_mem] at h
      exact ⟨⟨p, hp⟩, Sum.inl_injective h, rfl⟩
    · rw [fibreKey_of_notMem q hp] at h; cases h
  · rintro ⟨m', hm', rfl⟩
    rw [fibreKey_of_mem, show q m' = q m from hm']

theorem elt_fibreSetoid_of_notMem (q : M → Y) {x : Pt} (hx : x ∉ M) :
    HPC.Moore.elt (fibreSetoid q) x = {x} := by
  ext p
  simp only [HPC.Moore.elt, mem_setOf_eq, mem_singleton_iff]
  change fibreKey q p = fibreKey q x ↔ _
  rw [fibreKey_of_notMem q hx]
  constructor
  · intro h
    by_cases hp : p ∈ M
    · rw [show p = ((⟨p, hp⟩ : M) : Pt) from rfl, fibreKey_of_mem] at h; cases h
    · rw [fibreKey_of_notMem q hp] at h; exact Sum.inr_injective h
  · rintro rfl; rw [fibreKey_of_notMem q hx]

variable [CompactSpace M] [TopologicalSpace Y] [T2Space Y]

/-- **Upper semicontinuity of the fibres**, in Moore's form (as `layer_usc`, with any Hausdorff
target): a fibre that comes within `d` of the fibre through `m₀` lies within `e` of it. -/
theorem fibre_usc {q : M → Y} (hq : Continuous q) (m₀ : M) {e : ℝ} (he : 0 < e) :
    ∃ d > 0, ∀ m : M, (∃ p ∈ toPt (q ⁻¹' {q m}), infDist p (toPt (q ⁻¹' {q m₀})) < d) →
      ∀ p ∈ toPt (q ⁻¹' {q m}), infDist p (toPt (q ⁻¹' {q m₀})) < e := by
  set L := toPt (q ⁻¹' {q m₀}) with hL
  have hLc : IsCompact L :=
    ((isClosed_singleton.preimage hq).isCompact.image continuous_subtype_val)
  have hLne : L.Nonempty := ⟨_, m₀, rfl, rfl⟩
  set g : M → ℝ := fun z => infDist (z : Pt) L with hg
  have hgc : Continuous g := (continuous_infDist_pt L).comp continuous_subtype_val
  have hg0 : ∀ z : M, q z = q m₀ → g z = 0 := fun z hz => infDist_zero_of_mem ⟨z, hz, rfl⟩
  have hgpos : ∀ z : M, q z ≠ q m₀ → 0 < g z := fun z hz => by
    refine (hLc.isClosed.notMem_iff_infDist_pos hLne).1 fun hm => hz ?_
    obtain ⟨z', hz', hzz'⟩ := hm
    have : z' = z := Subtype.ext hzz'
    rw [← this]; exact hz'
  set C : Set M := {z | e ≤ g z} with hC
  have hCc : IsCompact C := (isClosed_le continuous_const hgc).isCompact
  have hqC : IsClosed (q '' C) := (hCc.image hq).isClosed
  have htC : q m₀ ∉ q '' C := by
    rintro ⟨z, hz, hzt⟩
    have : e ≤ g z := hz
    rw [hg0 z hzt] at this; linarith
  set W : Set M := q ⁻¹' (q '' C)ᶜ with hW
  have hWo : IsOpen W := hqC.isOpen_compl.preimage hq
  have hWc : IsCompact Wᶜ := hWo.isClosed_compl.isCompact
  obtain ⟨d₀, hd₀, hd₀W⟩ : ∃ d₀ > 0, ∀ z ∈ Wᶜ, d₀ ≤ g z := by
    rcases (Wᶜ).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun z hz => by rw [h] at hz; exact absurd hz (notMem_empty z)⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hWc.exists_isMinOn h hgc.continuousOn
      refine ⟨g z₁, hgpos z₁ fun hzt => hz₁ ?_, fun z hz => hmin hz⟩
      show q z₁ ∈ (q '' C)ᶜ
      rw [hzt]; exact htC
  refine ⟨min e d₀, lt_min he hd₀, fun m ⟨p, hp, hpd⟩ p' hp' => ?_⟩
  obtain ⟨z, hzs, rfl⟩ := hp
  obtain ⟨z', hz's, rfl⟩ := hp'
  have hzW : z ∈ W := by
    by_contra hzW
    have := hd₀W z hzW
    have : g z < min e d₀ := hpd
    linarith [min_le_right e d₀]
  have hsC : q m ∉ q '' C := by rw [← mem_singleton_iff.1 hzs]; exact hzW
  have hz'C : z' ∉ C := fun h => hsC ⟨z', h, mem_singleton_iff.1 hz's⟩
  simp only [hC, mem_setOf_eq, not_le] at hz'C
  exact hz'C

variable [ConnectedSpace M]

/-- **The decomposition satisfies Moore 1925's hypotheses**: its elements are the fibres of `q`,
which are proper subcontinua of `M` and so do not separate the plane
(`no_proper_subcontinuum_separates`), and the points off `M`; upper semicontinuity is `fibre_usc`
on `M` and the positive distance from a point off `M` to `M`. -/
theorem fibreSetoid_mooreDecomp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {q : M → Y} (hq : Continuous q) (hf : ∀ y, IsConnected (q ⁻¹' {y}))
    (hne : ∀ y, q ⁻¹' {y} ≠ univ) : HPC.Moore.MooreDecomp (fibreSetoid q) := by
  have hMc : IsCompact M := isCompact_iff_compactSpace.2 inferInstance
  have hfib : ∀ m : M, Fold.Q78.IsContinuum (q ⁻¹' {q m}) := fun m =>
    ⟨(isClosed_singleton.preimage hq).isCompact, hf (q m)⟩
  have hpt : ∀ x : Pt, ¬ SeparatesPlane {x} := fun x hs =>
    hs (isConnected_compl_singleton_of_one_lt_rank (by simp; norm_num) x)
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x e he => ?_⟩
  · by_cases hx : x ∈ M
    · rw [show x = ((⟨x, hx⟩ : M) : Pt) from rfl, elt_fibreSetoid_of_mem]
      exact (isContinuum_val_image (hfib _)).1
    · rw [elt_fibreSetoid_of_notMem q hx]; exact isCompact_singleton
  · by_cases hx : x ∈ M
    · rw [show x = ((⟨x, hx⟩ : M) : Pt) from rfl, elt_fibreSetoid_of_mem]
      exact (isContinuum_val_image (hfib _)).2
    · rw [elt_fibreSetoid_of_notMem q hx]; exact isConnected_singleton
  · by_cases hx : x ∈ M
    · rw [show x = ((⟨x, hx⟩ : M) : Pt) from rfl, elt_fibreSetoid_of_mem]
      exact no_proper_subcontinuum_separates hX hi (hfib _) (hne _)
    · rw [elt_fibreSetoid_of_notMem q hx]; exact hpt x
  · by_cases hx : x ∈ M
    · rw [show x = ((⟨x, hx⟩ : M) : Pt) from rfl, elt_fibreSetoid_of_mem]
      obtain ⟨d, hd, hdu⟩ := fibre_usc hq ⟨x, hx⟩ he
      refine ⟨min d e, lt_min hd he, fun y ⟨p, hp, hpd⟩ p' hp' => ?_⟩
      by_cases hy : y ∈ M
      · rw [show y = ((⟨y, hy⟩ : M) : Pt) from rfl, elt_fibreSetoid_of_mem] at hp hp'
        exact hdu ⟨y, hy⟩ ⟨p, hp, lt_of_lt_of_le hpd (min_le_left _ _)⟩ p' hp'
      · rw [elt_fibreSetoid_of_notMem q hy] at hp hp'
        rw [mem_singleton_iff.1 hp']; rw [mem_singleton_iff.1 hp] at hpd
        exact lt_of_lt_of_le hpd (min_le_right _ _)
    · rw [elt_fibreSetoid_of_notMem q hx]
      have hMne : M.Nonempty := by
        obtain ⟨m⟩ := (inferInstance : Nonempty M); exact ⟨m, m.2⟩
      have hρ : 0 < infDist x M := (hMc.isClosed.notMem_iff_infDist_pos hMne).1 hx
      refine ⟨min e (infDist x M), lt_min he hρ, fun y ⟨p, hp, hpd⟩ p' hp' => ?_⟩
      rw [infDist_singleton] at hpd ⊢
      by_cases hy : y ∈ M
      · exfalso
        rw [show y = ((⟨y, hy⟩ : M) : Pt) from rfl, elt_fibreSetoid_of_mem] at hp
        have hpM : p ∈ M := by obtain ⟨z, -, rfl⟩ := hp; exact z.2
        have h1 : infDist x M ≤ dist x p := infDist_le_dist_of_mem hpM
        rw [dist_comm] at h1
        linarith [min_le_right e (infDist x M)]
      · rw [elt_fibreSetoid_of_notMem q hy] at hp hp'
        rw [mem_singleton_iff.1 hp']; rw [mem_singleton_iff.1 hp] at hpd
        exact lt_of_lt_of_le hpd (min_le_left _ _)

/-- **The plane quotient** (Moore 1925 Theorem 22, as in `exists_quotient_plane`): `π` is the
quotient map of the plane by `fibreSetoid q` followed by the homeomorphism of Theorem 22; then
`y ↦ π(σ y)`, for a section `σ` of `q`, is a continuous injection of the compact `Y` onto `π[M]`. -/
theorem exists_plane_quotient_of_monotone_aux (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) [CompactSpace Y] {q : M → Y} (hq : Continuous q)
    (hqs : Function.Surjective q) (hf : ∀ y, IsConnected (q ⁻¹' {y}))
    (hne : ∀ y, q ⁻¹' {y} ≠ univ) : ∃ Q : Set Pt, IsCompact Q ∧ Nonempty (Y ≃ₜ Q) := by
  have hm := fibreSetoid_mooreDecomp hX hi hq hf hne
  obtain ⟨φ⟩ := HPC.Moore.m25_theorem22 hm
  set π : Pt → Pt := fun p => φ (Quotient.mk (fibreSetoid q) p) with hπ
  have hπc : Continuous π := φ.continuous.comp continuous_quotient_mk'
  have hπeq : ∀ p p', π p = π p' ↔ fibreSetoid q p p' := fun p p' => by
    simp only [hπ, φ.injective.eq_iff]
    exact Quotient.eq
  choose σ hσ using hqs
  set γ : Y → Pt := fun y => π (σ y : Pt) with hγ
  have hγq : γ ∘ q = fun m : M => π (m : Pt) := funext fun m => by
    refine (hπeq _ _).2 ?_
    change fibreKey q _ = fibreKey q _
    rw [fibreKey_of_mem, fibreKey_of_mem, hσ]
  have hqq : IsQuotientMap q := hq.isClosedMap.isQuotientMap hq (fun y => ⟨σ y, hσ y⟩)
  have hγc : Continuous γ := by
    rw [hqq.continuous_iff, hγq]
    exact hπc.comp continuous_subtype_val
  have hγi : Function.Injective γ := fun y y' h => by
    have := (hπeq _ _).1 h
    change fibreKey q _ = fibreKey q _ at this
    rw [fibreKey_of_mem, fibreKey_of_mem, hσ, hσ] at this
    exact Sum.inl_injective this
  have e₁ : Y ≃ₜ range γ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective γ hγi) (hγc.subtype_mk _)
  exact ⟨range γ, isCompact_range hγc, ⟨e₁⟩⟩

end PlaneQuot

end HPC.Hagopian
