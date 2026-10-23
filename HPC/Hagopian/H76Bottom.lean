import HPC.Hagopian.H76Prop3L3

/-!
# Batch 171, item B: the bottom case of the covering half

Commission 171 §1.B, bottom case: "`K` misses `E`, which is compact, so `K` lies above a positive
height `c_K` over `[a, b]`. The strip `F[(a, b) × (0, c_K)]` is connected, lies in `D`, misses
`π[K]`, and meets the vertical. Pull back by `π`, which is injective over `D`."

* `isPreconnected_preimage_off`: for the quotient map `π` (which collapses only the layers of
  `E`), the preimage of an open connected set missing `π[E]` is connected (`π` is an open
  injection off `E`);
* `bottom_component_below_aux`: for a compact `Z` missing `π⁻¹` of the bottom edge
  `F[[a, b] × {0}]`, there is a height `u > 0` such that every point `P` of `π⁻¹[D] − Z` whose
  component in `π⁻¹[D] − Z` has closure meeting `π⁻¹` of the bottom edge is **below** `Z`
  (`belowSet π F D′ t₀ u Z`, for any `t₀ ∈ (a, b)`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones HPC.Moore.Gen

section Bottom

variable {M : Set Pt}

/-- **The preimage under `π` of an open connected set off `π[E]` is connected.** -/
theorem isPreconnected_preimage_off {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {G : Set Pt}
    (hGo : IsOpen G) (hG : IsPreconnected G) (hGE : Disjoint (π ⁻¹' G) (toPt E)) :
    IsPreconnected (π ⁻¹' G) := by
  set X := π ⁻¹' G with hXdef
  have hXo : IsOpen X := hGo.preimage hπ.continuous
  set f : X → Pt := fun x => π x with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (eq_of_pi_eq_off hπS (disjoint_left.1 hGE y.2) hxy)
  have hopen : IsOpenMap f := by
    intro U hU
    obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
    have himg : f '' (Subtype.val ⁻¹' W) = π '' (W ∩ X) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, ⟨hx, x.2⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
    rw [himg]
    exact pi_isOpen_image_off hπ hπS (hW.inter hXo)
      (hGE.mono_left inter_subset_right)
  have hrange : G ⊆ range f := by
    intro p hp
    obtain ⟨x, rfl⟩ := hπ.surjective p
    exact ⟨⟨x, hp⟩, rfl⟩
  have h1 : IsPreconnected (f ⁻¹' G) := hG.preimage_of_isOpenMap hinj hopen hrange
  have h2 : f ⁻¹' G = univ := eq_univ_of_forall fun x => x.2
  rw [h2] at h1
  have := h1.image (Subtype.val : X → Pt) continuous_subtype_val.continuousOn
  simpa using this

/-- **B, the bottom case.** Set-up: `π` the quotient map collapsing the layers of `E` onto the arc
`γ`, `F` a collar of `γ`, `D′ ⊆ (a, b) × (0, c)` containing a low strip `(a, b) × (0, c₀)`. For a
compact `Z` missing `π⁻¹` of the bottom edge `F[[a, b] × {0}]` there is `u > 0` such that every
point of `π⁻¹[D] − Z` whose component in `π⁻¹[D] − Z` has closure meeting `π⁻¹` of the bottom edge
is below `Z`, relative to the vertical over any `t₀ ∈ (a, b)`. -/
theorem bottom_component_below_aux {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hb : b < 1) (hc1 : c ≤ 1) {D' : Set (ℝ × ℝ)}
    (hDo : IsOpen (F '' D')) (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hlow : ∃ c₀ > 0, Ioo a b ×ˢ Ioo 0 c₀ ⊆ D') {Z : Set Pt} (hZc : IsCompact Z)
    (hZb : Disjoint Z (π ⁻¹' (F '' (Icc a b ×ˢ {0})))) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ u > 0, ∀ P ∈ π ⁻¹' (F '' D') \ Z,
      (closure (connectedComponentIn (π ⁻¹' (F '' D') \ Z) P) ∩
        π ⁻¹' (F '' (Icc a b ×ˢ {0}))).Nonempty →
      P ∈ belowSet π F D' t₀ u Z := by
  obtain ⟨c₀, hc₀, hc₀D⟩ := hlow
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hF.1.continuous
  have hR1c : IsCompact R1 := isCompact_Icc.prod isCompact_Icc
  have hπc := hπ.continuous
  -- the height of `Z` above the bottom edge
  set Q : Set (ℝ × ℝ) := (Icc a b ×ˢ Icc 0 1) ∩ F ⁻¹' (π '' Z) with hQ
  have hQR : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ R1 := fun z hz =>
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1], hz.2.2⟩
  have hQc : IsCompact Q := by
    have hcl : IsClosed (Icc a b ×ˢ Icc (0 : ℝ) 1) := isClosed_Icc.prod isClosed_Icc
    have h1 : IsClosed (R1 ∩ F ⁻¹' (π '' Z)) :=
      hFc.preimage_isClosed_of_isClosed hR1c.isClosed (hZc.image hπc).isClosed
    have : Q = (Icc a b ×ˢ Icc (0 : ℝ) 1) ∩ (R1 ∩ F ⁻¹' (π '' Z)) := by
      ext z; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hQR h1, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    rw [this]
    exact (hR1c.of_isClosed_subset h1 inter_subset_left).inter_left hcl
  have hQ0 : ∀ z ∈ Q, 0 < z.2 := by
    rintro z ⟨⟨hz1, hz2, -⟩, w, hwZ, hw⟩
    rcases hz2.lt_or_eq with h | h
    · exact h
    · exfalso
      refine disjoint_left.1 hZb hwZ ⟨z, ⟨hz1, ?_⟩, hw.symm⟩
      exact mem_singleton_iff.2 h.symm
  obtain ⟨cK, hcK, hcK1, hcKQ⟩ := exists_height_below hQc hQ0
  set c' := min c₀ cK with hc'
  have hc'0 : 0 < c' := lt_min hc₀ hcK
  have hc'c₀ : c' ≤ c₀ := min_le_left _ _
  have hc'K : c' ≤ cK := min_le_right _ _
  set S' : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo 0 c' with hS'
  have hS'D : S' ⊆ D' := fun z hz => hc₀D ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hc'c₀⟩
  have hS'R : S' ⊆ R1 := fun z hz =>
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1],
      by linarith [hz.2.2, hcK1]⟩
  set G := F '' S' with hG
  -- `G` is open and connected
  have hDR1 : D' ⊆ R1 := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hz
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hGo : IsOpen G := by
    have hSo : IsOpen (Subtype.val ⁻¹' S' : Set R1) :=
      (isOpen_Ioo.prod isOpen_Ioo).preimage continuous_subtype_val
    obtain ⟨V, hV, hVe⟩ := hF.1.isInducing.isOpen_iff.1 hSo
    have hGeq : G = F '' D' ∩ V := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨⟨z, hS'D hz, rfl⟩, ?_⟩
        have : (⟨z, hS'R hz⟩ : R1) ∈ R1.restrict F ⁻¹' V := by rw [hVe]; exact hz
        exact this
      · rintro ⟨⟨z, hz, rfl⟩, hzV⟩
        have : (⟨z, hDR1 hz⟩ : R1) ∈ R1.restrict F ⁻¹' V := hzV
        rw [hVe] at this
        exact ⟨z, this, rfl⟩
    rw [hGeq]; exact hDo.inter hV
  have hGc : IsPreconnected G :=
    (((convex_Ioo a b).prod (convex_Ioo 0 c')).isPreconnected).image F (hFc.mono hS'R)
  -- `π⁻¹[G]` misses `E` and `Z`
  have hGE : Disjoint (π ⁻¹' G) (toPt E) := by
    rw [disjoint_left]
    rintro x ⟨z, hz, hzx⟩ hxE
    obtain ⟨t, ht⟩ := pi_mem_range_of_mem hγπ hxE
    have h0 : ((t : ℝ), (0 : ℝ)) ∈ R1 := ⟨⟨t.2.1, t.2.2⟩, by norm_num, by norm_num⟩
    have : z = ((t : ℝ), (0 : ℝ)) := collar_injOn hF (hS'R hz) h0
      (by rw [hzx, ← ht, hF.2.1 t])
    have := hz.2.1
    rw [‹z = _›] at this
    exact lt_irrefl _ this
  have hGZ : Disjoint (π ⁻¹' G) Z := by
    rw [disjoint_left]
    rintro x ⟨z, hz, hzx⟩ hxZ
    have hzQ : z ∈ Q := ⟨⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le,
      by linarith [hz.2.2, hcK1]⟩, x, hxZ, hzx.symm⟩
    have := hcKQ z hzQ
    linarith [hz.2.2]
  have hGpre := isPreconnected_preimage_off hπ hπS hGo hGc hGE
  have hGD : π ⁻¹' G ⊆ π ⁻¹' (F '' D') \ Z := fun x hx =>
    ⟨image_mono hS'D hx, disjoint_left.1 hGZ hx⟩
  -- the anchor on the vertical
  obtain ⟨P₀, hP₀⟩ := hπ.surjective (F (t₀, c' / 2))
  have hP₀G : P₀ ∈ π ⁻¹' G := by
    show π P₀ ∈ G
    rw [hP₀]; exact ⟨(t₀, c' / 2), ⟨ht₀, by positivity, by linarith⟩, rfl⟩
  refine ⟨c', hc'0, fun P hP hcl => ?_⟩
  set O := π ⁻¹' (F '' D') \ Z with hO
  have hOo : IsOpen O := (hDo.preimage hπc).sdiff hZc.isClosed
  set U := connectedComponentIn O P with hU
  have hUo : IsOpen U := hOo.connectedComponentIn
  have hUc : IsPreconnected U := isPreconnected_connectedComponentIn
  have hUO : U ⊆ O := connectedComponentIn_subset _ _
  have hPU : P ∈ U := mem_connectedComponentIn hP
  -- `U` meets `π⁻¹[G]`
  obtain ⟨x, hxU, z₀, ⟨hz₀1, hz₀2⟩, hx⟩ := hcl
  have hz₀R : z₀ ∈ R1 := ⟨⟨by linarith [hz₀1.1], by linarith [hz₀1.2]⟩,
    by rw [mem_singleton_iff.1 hz₀2]; norm_num, by rw [mem_singleton_iff.1 hz₀2]; norm_num⟩
  -- a neighbourhood `V` of `F z₀` whose trace on `F[R1]` is `F[R1 ∩ {|y| < c'}]`
  set W : Set (ℝ × ℝ) := univ ×ˢ Ioo (-c') c' with hW
  have hWo : IsOpen W := isOpen_univ.prod isOpen_Ioo
  obtain ⟨V, hV, hVeq⟩ := hF.1.isInducing.isOpen_iff.1
    (hWo.preimage continuous_subtype_val : IsOpen (Subtype.val ⁻¹' W : Set R1))
  have hFz₀V : F z₀ ∈ V := by
    have : (⟨z₀, hz₀R⟩ : R1) ∈ R1.restrict F ⁻¹' V := by
      rw [hVeq]
      refine ⟨mem_univ _, ?_⟩
      show z₀.2 ∈ Ioo (-c') c'
      rw [mem_singleton_iff.1 hz₀2]; exact ⟨by linarith, hc'0⟩
    exact this
  have hxV : x ∈ π ⁻¹' V := by show π x ∈ V; rw [← hx]; exact hFz₀V
  obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.1 hxU _ (hV.preimage hπc) hxV
  have hyG : y ∈ π ⁻¹' G := by
    obtain ⟨hyD, -⟩ := hUO hyU
    obtain ⟨z, hzD, hzy⟩ := hyD
    have hzR : z ∈ R1 := hDR1 hzD
    have hzV : (⟨z, hzR⟩ : R1) ∈ R1.restrict F ⁻¹' V := by
      show F z ∈ V; rw [hzy]; exact hyV
    rw [hVeq] at hzV
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := hDR hzD
    exact ⟨z, ⟨⟨h1, h2⟩, h3, hzV.2.2⟩, hzy⟩
  -- the connected set `U ∪ π⁻¹[G]`
  refine ⟨U ∪ π ⁻¹' G, hUc.union y hyU hyG hGpre, union_subset hUO hGD, Or.inl hPU,
    P₀, Or.inr hP₀G, ?_⟩
  rw [hP₀]
  exact ⟨(t₀, c' / 2), ⟨rfl, by positivity, by linarith⟩, rfl⟩

end Bottom

end HPC.Hagopian
