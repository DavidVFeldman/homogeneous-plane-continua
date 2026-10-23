import HPC.Hagopian.Hagopian76P

/-!
# Batch 172, item B: the inner collar of an arc of a Jordan curve, and the `I₂` case

Commission 172 §1.B: "`D′` is the bounded domain of a simple closed curve `J`. By
`plane_schoenflies` (batch 159) there is a homeomorphism of the plane taking `J` to the unit circle
and `D′` to the open disc. In disc coordinates, the points of the disc within `δ` of an arc of the
circle form a connected set. Pull this back to get the inner collar of `I` (the `I₂` case). Choose
`δ` below the distance from `I` to the compact `Z′`."

The batch-159 Schoenflies theorem in the project is the *square* form: an embedding
`f : [0, 1]² → R²` onto `J ∪ D` with `f(t, 0) = φ(t)` for a given arc `φ` of `J` and the open square
onto `D`. The collar is then the image of a thin strip `(0, 1) × (0, δ)`, with `δ` below the height
of the compact `f⁻¹[Q]`; no metric in disc coordinates is needed.

* `jordan_inner_collar`: for an arc `φ` of the Jordan curve `J = ∂D` and a closed `Q` missing the
  arc, there is an open connected `N ⊆ D` missing `Q` such that every point of the arc has a
  neighbourhood `V` with `V ∩ D ⊆ N`;
* `rect_frontier_domain`: a domain `D′` of the shape of `hagopian76_D` (open, inside the rectangle,
  frontier the arc `I` plus the frame) is the bounded complementary domain of the simple closed
  curve `∂D′`, hence connected;
* `top_component_above_aux`: **the `I₂` case**: for a compact `Z` missing `π⁻¹[I₂]`, every point of
  `π⁻¹[D] − Z` whose component in `π⁻¹[D] − Z` has closure meeting `π⁻¹[I₂]` is **above** `Z`
  (`aboveSet`), for a height `u ∈ (0, w₂)`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones HPC.Moore.Gen

section InnerCollar

/-- **The inner collar of an arc of a Jordan curve** (Schoenflies, square form). -/
theorem jordan_inner_collar {J D : Set Pt} (hJ : TSCC J) (hD : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (hDJ : frontier D = J) {φ : unitInterval → Pt}
    (hφ : IsEmbedding φ) (hφJ : range φ ⊆ J) {Q : Set Pt} (hQ : IsClosed Q)
    (hQφ : Disjoint Q (range φ)) :
    ∃ N : Set Pt, IsOpen N ∧ IsPreconnected N ∧ N ⊆ D ∧ Disjoint N Q ∧
      ∀ p ∈ range φ, ∃ V ∈ 𝓝 p, V ∩ D ⊆ N := by
  obtain ⟨f, hf, hfr, hf0, hfD⟩ := plane_schoenflies hJ hD hDc hDb hDJ hφ hφJ
  set Sq : Set (unitInterval × unitInterval) := {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1}
    with hSq
  -- the height of `f⁻¹[Q]`
  set K : Set (unitInterval × unitInterval) := f ⁻¹' Q with hK
  have hKc : IsCompact K := (hQ.preimage hf.continuous).isCompact
  set K' : Set (ℝ × ℝ) := (fun p : unitInterval × unitInterval => ((p.1 : ℝ), (p.2 : ℝ))) '' K
    with hK'
  have hK'c : IsCompact K' := hKc.image (by fun_prop)
  have hK'0 : ∀ z ∈ K', 0 < z.2 := by
    rintro _ ⟨p, hp, rfl⟩
    show 0 < (p.2 : ℝ)
    rcases (unitInterval.nonneg p.2).lt_or_eq with h | h
    · exact h
    · exfalso
      have hp2 : p.2 = 0 := Subtype.ext h.symm
      have : f p = φ p.1 := by rw [← hf0 p.1, ← hp2]
      exact disjoint_left.1 hQφ (show f p ∈ Q from hp) ⟨p.1, this.symm⟩
  obtain ⟨δ, hδ, hδ1, hδK⟩ := exists_height_below hK'c hK'0
  set Wδ : Set (unitInterval × unitInterval) := {p | (p.2 : ℝ) < δ} with hWδ
  have hWδo : IsOpen Wδ := isOpen_lt (by fun_prop) continuous_const
  have hSqo : IsOpen Sq := by
    have h1 : IsOpen {p : unitInterval × unitInterval | 0 < p.1} :=
      isOpen_lt continuous_const continuous_fst
    have h2 : IsOpen {p : unitInterval × unitInterval | p.1 < 1} :=
      isOpen_lt continuous_fst continuous_const
    have h3 : IsOpen {p : unitInterval × unitInterval | 0 < p.2} :=
      isOpen_lt continuous_const continuous_snd
    have h4 : IsOpen {p : unitInterval × unitInterval | p.2 < 1} :=
      isOpen_lt continuous_snd continuous_const
    exact h1.inter (h2.inter (h3.inter h4))
  -- open sets of the square are traces of open sets of the plane
  have htrace : ∀ U : Set (unitInterval × unitInterval), IsOpen U →
      ∃ V : Set Pt, IsOpen V ∧ f ⁻¹' V = U := fun U hU => by
    obtain ⟨V, hV, hVe⟩ := hf.isInducing.isOpen_iff.1 hU
    exact ⟨V, hV, hVe⟩
  set N := f '' (Sq ∩ Wδ) with hN
  have hND : N ⊆ D := by rw [← hfD]; exact image_mono inter_subset_left
  obtain ⟨V, hV, hVe⟩ := htrace _ (hSqo.inter hWδo)
  have hNeq : N = V ∩ D := by
    apply Subset.antisymm
    · intro q hq
      refine ⟨?_, hND hq⟩
      obtain ⟨p, hp, rfl⟩ := hq
      show p ∈ f ⁻¹' V
      rw [hVe]; exact hp
    · rintro q ⟨hqV, hqD⟩
      rw [← hfD] at hqD
      obtain ⟨p, hp, rfl⟩ := hqD
      have : p ∈ f ⁻¹' V := hqV
      rw [hVe] at this
      exact ⟨p, this, rfl⟩
  refine ⟨N, hNeq ▸ hV.inter hD, ?_, hND, ?_, ?_⟩
  · -- the strip is connected
    have hstrip : Sq ∩ Wδ = (Ioo (0 : unitInterval) 1) ×ˢ
        {t : unitInterval | 0 < t ∧ (t : ℝ) < δ} := by
      ext p
      simp only [hSq, hWδ, mem_inter_iff, mem_setOf_eq, mem_prod, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, h2, h3, -⟩, h5⟩; exact ⟨⟨h1, h2⟩, h3, h5⟩
      · rintro ⟨⟨h1, h2⟩, h3, h5⟩
        refine ⟨⟨h1, h2, h3, ?_⟩, h5⟩
        show (p.2 : ℝ) < 1
        linarith
    have hoc : OrdConnected {t : unitInterval | 0 < t ∧ (t : ℝ) < δ} := by
      constructor
      rintro x ⟨hx0, -⟩ y ⟨-, hy⟩ z ⟨hxz, hzy⟩
      exact ⟨lt_of_lt_of_le hx0 hxz, lt_of_le_of_lt (show (z : ℝ) ≤ y from hzy) hy⟩
    have hpc : IsPreconnected (Sq ∩ Wδ) := by
      rw [hstrip]
      exact isPreconnected_Ioo.prod hoc.isPreconnected
    exact hpc.image f hf.continuous.continuousOn
  · rw [disjoint_left]
    rintro _ ⟨p, ⟨-, hpW⟩, rfl⟩ hpQ
    have := hδK _ ⟨p, hpQ, rfl⟩
    exact absurd hpW (not_lt.2 this.le)
  · rintro _ ⟨t, rfl⟩
    obtain ⟨V₁, hV₁, hV₁e⟩ := htrace _ hWδo
    refine ⟨V₁, hV₁.mem_nhds ?_, ?_⟩
    · rw [← hf0 t]
      show ((t, 0) : unitInterval × unitInterval) ∈ f ⁻¹' V₁
      rw [hV₁e]
      show ((0 : unitInterval) : ℝ) < δ
      simpa using hδ
    · rintro q ⟨hqV, hqD⟩
      rw [← hfD] at hqD
      obtain ⟨p, hp, rfl⟩ := hqD
      have : p ∈ f ⁻¹' V₁ := hqV
      rw [hV₁e] at this
      exact ⟨p, ⟨hp, this⟩, rfl⟩

/-- **The domain under a crossing arc is the Jordan domain of its frontier.** A domain `D′` of the
shape used in `hagopian76_D` (open, inside the open rectangle, with frontier the arc `I` and the
frame) has a simple closed curve as frontier, and is connected and bounded. -/
theorem rect_frontier_domain {a b c : ℝ} (hab : a < b) {r s : ℝ × ℝ} {I D : Set (ℝ × ℝ)}
    (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hr : r.1 = a) (hs : s.1 = b)
    (hIs : I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s}) (hDo : IsOpen D)
    (hDR : D ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
      ({b} : Set ℝ) ×ˢ Icc 0 s.2) :
    TSCC (frontier D) ∧ IsConnected D ∧ Bornology.IsBounded D := by
  have hrI := hIR hI.left_mem
  have hsI := hIR hI.right_mem
  have hr2 : 0 < r.2 := hrI.2.1
  have hs2 : 0 < s.2 := hsI.2.1
  set U : Set (ℝ × ℝ) :=
    ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪ Icc a b ×ˢ {0} ∪ ({b} : Set ℝ) ×ˢ Icc 0 s.2 with hUdef
  have hU : TArc r s U := by
    have h := tarc_frame hab hr2 hs2
    rwa [show ((a, r.2) : Pt) = r from Prod.ext hr.symm rfl,
      show ((b, s.2) : Pt) = s from Prod.ext hs.symm rfl] at h
  have hIU : I ∩ U = {r, s} := by
    apply subset_antisymm
    · rintro p ⟨hpI, hpU⟩
      rw [← hIs]
      refine ⟨hpI, ?_⟩
      have hpR := hIR hpI
      obtain ⟨x, y⟩ := p
      rcases hpU with ((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩)
      · simp only [mem_singleton_iff] at hx; subst hx
        exact ⟨Or.inl rfl, hpR.2.1.le, hpR.2.2⟩
      · simp only [mem_singleton_iff] at hy; subst hy
        exact absurd hpR.2.1 (lt_irrefl _)
      · simp only [mem_singleton_iff] at hx; subst hx
        exact ⟨Or.inr rfl, hpR.2.1.le, hpR.2.2⟩
    · rintro p (rfl | rfl)
      · exact ⟨hI.left_mem, hU.left_mem⟩
      · exact ⟨hI.right_mem, hU.right_mem⟩
  have hJeq : frontier D = I ∪ U := by
    rw [hDf, hUdef]; ext p; simp only [mem_union]; tauto
  have hJ : TSCC (frontier D) := hJeq ▸ ⟨r, s, I, U, hI, hU, hIU, rfl⟩
  have hDb : Bornology.IsBounded D :=
    ((isCompact_Icc.prod isCompact_Icc).isBounded).subset
      (hDR.trans (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
  obtain ⟨Din, Dout, hio, hic, hoo, hoc, hdisj, hun, hib, hob, hif, hof⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hJ)
  have hDJ : Disjoint D (frontier D) := by
    rw [disjoint_left]
    intro x hx hxf
    rw [frontier, hDo.interior_eq] at hxf
    exact hxf.2 hx
  have hDne : D.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, frontier_empty] at hJeq
    have : r ∈ (∅ : Set (ℝ × ℝ)) := hJeq ▸ Or.inl hI.left_mem
    exact this
  -- `D` misses the unbounded domain
  have hDout : ∀ x ∈ D, x ∉ Dout := by
    intro x hxD hxO
    have hsub : Dout ⊆ D := conn_sub_of_frontier hoc.isPreconnected
      (by rw [disjoint_left]; intro y hyO hyf; rw [hJeq] at hyf
          have : y ∈ (frontier D)ᶜ := by rw [← hun]; exact Or.inr hyO
          exact this (hJeq ▸ hyf)) ⟨x, hxO, hxD⟩
    exact hob (hDb.subset hsub)
  have hDin : D ⊆ Din := by
    intro x hxD
    have : x ∈ (frontier D)ᶜ := fun h => disjoint_left.1 hDJ hxD h
    rw [← hun] at this
    rcases this with h | h
    · exact h
    · exact absurd h (hDout x hxD)
  have hDinD : Din ⊆ D := by
    obtain ⟨x, hx⟩ := hDne
    refine conn_sub_of_frontier hic.isPreconnected ?_ ⟨x, hDin hx, hx⟩
    rw [disjoint_left]
    intro y hyI hyf
    have : y ∈ (frontier D)ᶜ := by rw [← hun]; exact Or.inl hyI
    exact this hyf
  have hDeq : D = Din := Subset.antisymm hDin hDinD
  exact ⟨hJ, hDeq ▸ hic, hDb⟩

end InnerCollar

section Top

variable {M : Set Pt}

/-- **B, the `I₂` case.** Set-up of `crossing_bottom_below`, with the arc `I` of `hagopian76_D`
(`I = [a, b] × (0, c] ∩ F⁻¹[I₂]`, from `(a, r₂)` to `(b, s₂)`) on the frontier of `D′`, and
`F(t₀, w₂) ∈ I₂` the lowest point of `I₂` over `t₀`. For a compact `Z` missing `π⁻¹[I₂]` there is
`u ∈ (0, w₂)` such that every point of `π⁻¹[D] − Z` whose component in `π⁻¹[D] − Z` has closure
meeting `π⁻¹[I₂]` is above `Z` (`aboveSet`, anchored on the vertical over `t₀` at heights
`[u, w₂)`). -/
theorem top_component_above_aux {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDo : IsOpen D')
    (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D')) {Z : Set Pt} (hZc : IsCompact Z) (hZI : Disjoint Z (π ⁻¹' I₂))
    {t₀ w₂ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂)) :
    ∃ u ∈ Ioo 0 w₂, ∀ P ∈ π ⁻¹' (F '' D') \ Z,
      (closure (connectedComponentIn (π ⁻¹' (F '' D') \ Z) P) ∩ π ⁻¹' I₂).Nonempty →
      P ∈ aboveSet π F D' t₀ u w₂ Z := by
  set Iarc := Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂ with hIarc
  have hIarcR : Iarc ⊆ Icc a b ×ˢ Ioc 0 c := inter_subset_left
  obtain ⟨hJ, hDc, hDb⟩ := rect_frontier_domain hab hI hIarcR rfl rfl hIs hDo hDR hDf
  obtain ⟨-, φ, hφ, hφr, -, -⟩ := hI
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hF.1.continuous
  have hR1c : IsCompact R1 := isCompact_Icc.prod isCompact_Icc
  have hπc := hπ.continuous
  have hDR1 : D' ⊆ R1 := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hz
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hIR1 : Icc a b ×ˢ Ioc 0 c ⊆ R1 := fun z hz =>
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  -- the closed set `Q` of collar points over `Z`
  set Q : Set (ℝ × ℝ) := R1 ∩ F ⁻¹' (π '' Z) with hQ
  have hQc : IsClosed Q :=
    hFc.preimage_isClosed_of_isClosed hR1c.isClosed (hZc.image hπc).isClosed
  have hQI : Disjoint Q (range φ) := by
    rw [hφr, disjoint_left]
    rintro z ⟨-, w, hwZ, hw⟩ ⟨-, hzI⟩
    exact disjoint_left.1 hZI hwZ (show π w ∈ I₂ by rw [hw]; exact hzI)
  have hφJ : range φ ⊆ frontier D' := by
    rw [hφr, hDf]; intro z hz; exact Or.inl (Or.inl (Or.inl hz))
  obtain ⟨N, hNo, hNc, hND, hNQ, hNnb⟩ :=
    jordan_inner_collar hJ hDo hDc hDb rfl hφ hφJ hQc hQI
  have hNR : N ⊆ R1 := hND.trans hDR1
  set G := F '' N with hG
  -- `G` is open and connected
  have hGo : IsOpen G := by
    have hSo : IsOpen (Subtype.val ⁻¹' N : Set R1) := hNo.preimage continuous_subtype_val
    obtain ⟨V, hV, hVe⟩ := hF.1.isInducing.isOpen_iff.1 hSo
    have hGeq : G = F '' D' ∩ V := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨⟨z, hND hz, rfl⟩, ?_⟩
        have : (⟨z, hNR hz⟩ : R1) ∈ R1.restrict F ⁻¹' V := by rw [hVe]; exact hz
        exact this
      · rintro ⟨⟨z, hz, rfl⟩, hzV⟩
        have : (⟨z, hDR1 hz⟩ : R1) ∈ R1.restrict F ⁻¹' V := hzV
        rw [hVe] at this
        exact ⟨z, this, rfl⟩
    rw [hGeq]; exact hFDo.inter hV
  have hGc : IsPreconnected G := hNc.image F (hFc.mono hNR)
  -- `π⁻¹[G]` misses `E` and `Z`
  have hGE : Disjoint (π ⁻¹' G) (toPt E) := by
    rw [disjoint_left]
    rintro x ⟨z, hz, hzx⟩ hxE
    obtain ⟨t, ht⟩ := pi_mem_range_of_mem hγπ hxE
    have h0 : ((t : ℝ), (0 : ℝ)) ∈ R1 := ⟨⟨t.2.1, t.2.2⟩, by norm_num, by norm_num⟩
    have : z = ((t : ℝ), (0 : ℝ)) := collar_injOn hF (hNR hz) h0
      (by rw [hzx, ← ht, hF.2.1 t])
    have := (hDR (hND hz)).2.1
    rw [‹z = _›] at this
    exact lt_irrefl _ this
  have hGZ : Disjoint (π ⁻¹' G) Z := by
    rw [disjoint_left]
    rintro x ⟨z, hz, hzx⟩ hxZ
    exact disjoint_left.1 hNQ hz ⟨hNR hz, x, hxZ, hzx.symm⟩
  have hGpre := isPreconnected_preimage_off hπ hπS hGo hGc hGE
  have hGD : π ⁻¹' G ⊆ π ⁻¹' (F '' D') \ Z := fun x hx =>
    ⟨image_mono hND hx, disjoint_left.1 hGZ hx⟩
  -- the anchor on the vertical, just below `F(t₀, w₂)`
  have htw : ((t₀, w₂) : ℝ × ℝ) ∈ range φ := by
    rw [hφr]; exact ⟨⟨⟨ht₀.1.le, ht₀.2.le⟩, hw₂⟩, hFw⟩
  obtain ⟨V₀, hV₀, hV₀N⟩ := hNnb _ htw
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV₀
  set u := max (w₂ - ε / 2) (w₂ / 2) with hu
  have hw₂0 := hw₂.1
  have hu0 : 0 < u := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have huw : u < w₂ := max_lt (by linarith) (by linarith)
  have huV : ((t₀, u) : ℝ × ℝ) ∈ V₀ := by
    apply hεV
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    refine max_lt hε ?_
    rw [abs_lt]
    constructor <;> linarith [le_max_left (w₂ - ε / 2) (w₂ / 2)]
  have hIcpt : IsCompact Iarc := by
    rw [← hφr]; exact isCompact_range hφ.continuous
  have huD : ((t₀, u) : ℝ × ℝ) ∈ D' :=
    rect_domain_vert (r := ((a, r₂) : ℝ × ℝ)) (s := ((b, s₂) : ℝ × ℝ)) hab hIcpt
      (fun z hz => (hIarcR hz).2.1) hDR hDf ht₀ hw₂0 hseg
      ⟨rfl, hu0, huw⟩
  have huN : ((t₀, u) : ℝ × ℝ) ∈ N := hV₀N ⟨huV, huD⟩
  obtain ⟨P₀, hP₀⟩ := hπ.surjective (F (t₀, u))
  have hP₀G : P₀ ∈ π ⁻¹' G := by
    show π P₀ ∈ G
    rw [hP₀]; exact ⟨(t₀, u), huN, rfl⟩
  refine ⟨u, ⟨hu0, huw⟩, fun P hP hcl => ?_⟩
  set O := π ⁻¹' (F '' D') \ Z with hO
  set U := connectedComponentIn O P with hU
  have hUc : IsPreconnected U := isPreconnected_connectedComponentIn
  have hUO : U ⊆ O := connectedComponentIn_subset _ _
  have hPU : P ∈ U := mem_connectedComponentIn hP
  -- `U` meets `π⁻¹[G]`
  obtain ⟨x, hxU, hxI⟩ := hcl
  obtain ⟨z₀, hz₀R, hz₀⟩ := hIR hxI
  have hz₀φ : z₀ ∈ range φ := by
    rw [hφr]; exact ⟨hz₀R, show F z₀ ∈ I₂ by rw [hz₀]; exact hxI⟩
  obtain ⟨V₁, hV₁, hV₁N⟩ := hNnb _ hz₀φ
  obtain ⟨V₂, hV₂V₁, hV₂o, hz₀V₂⟩ := _root_.mem_nhds_iff.1 hV₁
  obtain ⟨V, hV, hVeq⟩ := hF.1.isInducing.isOpen_iff.1
    (hV₂o.preimage continuous_subtype_val : IsOpen (Subtype.val ⁻¹' V₂ : Set R1))
  have hFz₀V : F z₀ ∈ V := by
    have : (⟨z₀, hIR1 hz₀R⟩ : R1) ∈ R1.restrict F ⁻¹' V := by rw [hVeq]; exact hz₀V₂
    exact this
  have hxV : x ∈ π ⁻¹' V := by show π x ∈ V; rw [← hz₀]; exact hFz₀V
  obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.1 hxU _ (hV.preimage hπc) hxV
  have hyG : y ∈ π ⁻¹' G := by
    obtain ⟨hyD, -⟩ := hUO hyU
    obtain ⟨z, hzD, hzy⟩ := hyD
    have hzV : (⟨z, hDR1 hzD⟩ : R1) ∈ R1.restrict F ⁻¹' V := by
      show F z ∈ V; rw [hzy]; exact hyV
    rw [hVeq] at hzV
    exact ⟨z, hV₁N ⟨hV₂V₁ hzV, hzD⟩, hzy⟩
  refine ⟨U ∪ π ⁻¹' G, hUc.union y hyU hyG hGpre, union_subset hUO hGD, Or.inl hPU,
    P₀, Or.inr hP₀G, ?_⟩
  rw [hP₀]
  exact ⟨(t₀, u), ⟨rfl, le_rfl, huw⟩, rfl⟩

end Top

end HPC.Hagopian
