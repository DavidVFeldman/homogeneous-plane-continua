import HPC.Hagopian.Hagopian76P

/-!
# Batch 172, item A: a layer that contains an open piece of a continuum contains the continuum

Commission 172 §1.A asks for the end case of Property 3. This file proves a lemma that settles the
end case of the batch-171 reduction, and reduces Property 3 to one configuration:

* `continuum_subset_layer_of_open` (**the swallowing lemma**): let `G` be a type A′ continuum of
  `M` (minimal admissible map `d`), `C = d⁻¹(v)` one of its layers, and `W ⊆ G` a continuum. If a
  nonempty relatively open subset of `W` lies in `C`, then `W ⊆ C`.

  *Proof.* Suppose `w ∈ W` has `d(w) = u₁ ≠ v`, say `v < u₁`. `W` meets `d⁻¹(v)` and `d⁻¹(u₁)`, so
  it contains `d⁻¹((v, u₁))` (`layerSet_Ioo_subset`). Let `x ∈ W ∩ V ⊆ C`. Lower semicontinuity of
  the decomposition of `G` (Lemma 5, `lsc_of_minimalAdmissible`) gives an open `Wo ⊇ C` all of whose
  layers meet `V`. The continuum `d⁻¹[[v, m]]` (`m` between `v` and `u₁`) is not `C`, so it has a
  point of `Wo` off `C`; its layer meets `V`, inside `d⁻¹((v, u₁)) ⊆ W`. That point lies in
  `W ∩ V ⊆ C`, but not in the layer `d⁻¹(v)`. The case `u₁ < v` is the reversed map.
* `translate_subset_layer`: if an interior layer `d⁻¹(v)` (`0 < v < 1`) of `G` contains the
  translate `h[k⁻¹(A)]` of the layers of `E` over a nonempty open `A`, then it contains the whole
  translate `h[E]`. (Apply the swallowing lemma to `W = h[E] ∩ G`, a continuum by hereditary
  unicoherence; then `h[E]` meets `G` and misses its end sets, so `h[E] ⊆ G`, `subset_of_meets_avoids`.)
* `translate_extension_subset_layer`: if moreover `G = F` is an extension of `E` away from
  `k⁻¹(0)`, then `h[F] ⊆ d⁻¹(v)` (apply `translate_subset_layer` to `F` itself: `E = d⁻¹[[0, s]]`
  contains the open piece `d⁻¹[[0, s))`).
* `layer_disjoint_of_not_subset`: a layer of an extension `F` not inside `E` misses `E`
  (commission 172 §1.A.1: `v > s`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Swallow

variable {M : Set Pt}

/-- The layers over an open set of parameters form a relatively open subset of `E`. -/
theorem layerSet_eq_inter_open {E : Set M} {k : E → unitInterval} (hk : Continuous k)
    {A : Set unitInterval} (hA : IsOpen A) : ∃ V : Set M, IsOpen V ∧ layerSet k A = E ∩ V := by
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1 (hA.preimage hk)
  refine ⟨V, hV, ?_⟩
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e.2, ?_⟩
    have : e ∈ Subtype.val ⁻¹' V := by rw [hVe]; exact he
    exact this
  · rintro ⟨hxE, hxV⟩
    refine ⟨⟨x, hxE⟩, ?_, rfl⟩
    have : (⟨x, hxE⟩ : E) ∈ Subtype.val ⁻¹' V := hxV
    rw [hVe] at this
    exact this

/-- A point of `G` lies in the layer of its own parameter. -/
theorem mem_layer_self {G : Set M} (d : G → unitInterval) (x : G) : (x : M) ∈ layer d (d x) :=
  ⟨x, rfl, rfl⟩

/-- The parameter of a point of a layer. -/
theorem param_of_mem_layer {G : Set M} {d : G → unitInterval} {x : G} {v : unitInterval}
    (hx : (x : M) ∈ layer d v) : d x = v := by
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  subst this
  exact hy

variable [CompactSpace M] [ConnectedSpace M]

/-- The one-sided core of the swallowing lemma (`v < d(w)`). -/
theorem swallow_core (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) {W : Set M}
    (hW : Fold.Q78.IsContinuum W) (hWG : W ⊆ G) {v : unitInterval} {V : Set M} (hV : IsOpen V)
    (hne : (W ∩ V).Nonempty) (hWV : W ∩ V ⊆ layer d v) {w : G} (hwW : (w : M) ∈ W)
    (hvw : v < d w) : False := by
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hG.isCompact
  have hL := lsc_of_minimalAdmissible hX hi hG
  obtain ⟨x, hxW, hxV⟩ := hne
  have hxG : x ∈ G := hWG hxW
  set x' : G := ⟨x, hxG⟩ with hx'
  have hx'v : d x' = v := param_of_mem_layer (hWV ⟨hxW, hxV⟩)
  set u₁ := d w with hu₁
  have hseg : layerSet d (Ioo v u₁) ⊆ W :=
    layerSet_Ioo_subset hG hWG hW ⟨x, hxW, hx'v ▸ mem_layer_self d x'⟩
      ⟨w, hwW, mem_layer_self d w⟩
  set m : unitInterval := ⟨((v : ℝ) + u₁) / 2, by
    constructor
    · have := v.2.1; have := u₁.2.1; linarith
    · have := v.2.2; have := u₁.2.2; linarith⟩ with hm
  have hvw' : (v : ℝ) < u₁ := hvw
  have hvm : v < m := by show (v : ℝ) < ((v : ℝ) + u₁) / 2; linarith
  have hmu : m < u₁ := by show ((v : ℝ) + u₁) / 2 < u₁; linarith
  have hCc : IsClosed (layer d v) :=
    (isCompact_img hG.isCompact hG.2.1.1 isClosed_singleton).isClosed
  -- the open set of lower semicontinuity
  obtain ⟨Wo, hWo, hCWo, hWoV⟩ := hL x' x' (show (Setoid.ker d) x' x' from rfl) (Subtype.val ⁻¹' V)
    (hV.preimage continuous_subtype_val) hxV
  obtain ⟨Wo', hWo', hWoe⟩ := isOpen_induced_iff.1 hWo
  have hCWo' : layer d v ⊆ Wo' := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Wo := hCWo (show d y = d x' by rw [hx'v]; exact hy)
    rw [← hWoe] at hy'
    exact hy'
  -- a point of `d⁻¹[[v, m]]` in `Wo'` off `C`
  set S := layerSet d (Icc v m) with hS
  have hSc : IsPreconnected S :=
    (isContinuum_img hG.isCompact hG.2.1 isClosed_Icc isPreconnected_Icc
      ⟨v, le_rfl, hvm.le⟩).2.isPreconnected
  have hz : ∃ z ∈ S, z ∈ Wo' ∧ z ∉ layer d v := by
    by_contra hcon
    push_neg at hcon
    rcases isPreconnected_iff_subset_of_disjoint.1 hSc Wo' (layer d v)ᶜ hWo' hCc.isOpen_compl
        (fun s hs => by
          by_cases hsC : s ∈ layer d v
          · exact Or.inl (hCWo' hsC)
          · exact Or.inr hsC)
        (by
          ext s
          simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
          intro hsS hsW hsC
          exact hsC (hcon s hsS hsW)) with h | h
    · obtain ⟨y, hy⟩ := layer_nonempty hG.2.1.2.1 m
      have hyS : y ∈ S := by
        obtain ⟨y', hy', rfl⟩ := hy
        exact ⟨y', by rw [mem_preimage, mem_singleton_iff.1 hy']; exact ⟨hvm.le, le_rfl⟩, rfl⟩
      have := hcon y hyS (h hyS)
      exact absurd (layer_param_eq hy this) (ne_of_gt hvm)
    · have hxS : x ∈ S := ⟨x', by rw [mem_preimage, hx'v]; exact ⟨le_rfl, hvm.le⟩, rfl⟩
      exact h hxS (hx'v ▸ mem_layer_self d x')
  obtain ⟨z, ⟨z', hz'S, rfl⟩, hzWo, hzC⟩ := hz
  have hz'Wo : z' ∈ Wo := by rw [← hWoe]; exact hzWo
  obtain ⟨y, hy, hyV⟩ := hWoV z' hz'Wo
  have hyz : d y = d z' := hy
  have hz'v : d z' ≠ v := fun h => hzC (h ▸ mem_layer_self d z')
  have hz1 : v < d z' := lt_of_le_of_ne hz'S.1 (Ne.symm hz'v)
  have hyseg : (y : M) ∈ layerSet d (Ioo v u₁) :=
    ⟨y, by rw [mem_preimage, hyz]; exact ⟨hz1, lt_of_le_of_lt hz'S.2 hmu⟩, rfl⟩
  have hyC := hWV ⟨hseg hyseg, hyV⟩
  exact hz'v (hyz ▸ param_of_mem_layer hyC)

/-- **The swallowing lemma.** A subcontinuum `W` of a type A′ continuum `G` that has a nonempty
relatively open subset `W ∩ V` inside a layer `d⁻¹(v)` of `G` lies in that layer. -/
theorem continuum_subset_layer_of_open (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) {W : Set M}
    (hW : Fold.Q78.IsContinuum W) (hWG : W ⊆ G) {v : unitInterval} {V : Set M} (hV : IsOpen V)
    (hne : (W ∩ V).Nonempty) (hWV : W ∩ V ⊆ layer d v) : W ⊆ layer d v := by
  intro p hpW
  by_contra hpC
  set w : G := ⟨p, hWG hpW⟩
  have hwv : d w ≠ v := fun h => hpC (h ▸ mem_layer_self d w)
  rcases lt_or_gt_of_ne hwv with h | h
  · -- reverse the map
    have hG' := hG.symm_comp
    have hlay : ∀ t, layer (unitInterval.symm ∘ d) (unitInterval.symm t) = layer d t := by
      intro t; rw [layer_symm_comp, unitInterval.symm_symm]
    refine swallow_core hX hi hG' hW hWG (v := unitInterval.symm v) hV hne (by rw [hlay]; exact hWV)
      (w := w) hpW ?_
    show (1 - (v : ℝ)) < 1 - (d w : ℝ)
    have : (d w : ℝ) < v := h
    linarith
  · exact swallow_core hX hi hG hW hWG hV hne hWV hpW h

/-- **A layer containing an open piece of a translate contains the translate.** If an interior
layer `d⁻¹(v)` (`0 < v < 1`) of a type A′ continuum `G` contains `h[k⁻¹(A)]` for a nonempty open set
`A` of parameters, then `h[E] ⊆ d⁻¹(v)`. -/
theorem translate_subset_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {v : unitInterval} (hv0 : 0 < v) (hv1 : v < 1) (h : M ≃ₜ M)
    {A : Set unitInterval} (hA : IsOpen A) (hAne : A.Nonempty)
    (hsub : h '' layerSet k A ⊆ layer d v) : h '' E ⊆ layer d v := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  obtain ⟨a, b, hab⟩ := hE.1
  obtain ⟨a', b', hab'⟩ := hG.1
  have hk := hE.2.1
  have hd := hG.2.1
  have hEc := hab.1
  have hGc := hab'.1
  have hCG : layer d v ⊆ G := fun _ ⟨y, _, hy⟩ => hy ▸ y.2
  obtain ⟨V₀, hV₀, hV₀e⟩ := layerSet_eq_inter_open hk.1 hA
  obtain ⟨t, ht⟩ := hAne
  obtain ⟨e, he⟩ := hk.2.1 t
  have heA : (e : M) ∈ layerSet k A := ⟨e, by rw [mem_preimage, he]; exact ht, rfl⟩
  have hheC : h e ∈ layer d v := hsub ⟨e, heA, rfl⟩
  have hhE := isContinuum_homeo_image h hEc
  have hWc : Fold.Q78.IsContinuum (h '' E ∩ G) :=
    isContinuum_inter_of_HU hHU hhE hGc ⟨h e, ⟨e, e.2, rfl⟩, hCG hheC⟩
  have hV : IsOpen (h '' V₀) := h.isOpenMap _ hV₀
  have hWV : (h '' E ∩ G) ∩ h '' V₀ ⊆ layer d v := by
    rintro p ⟨⟨hpE, -⟩, hpV⟩
    apply hsub
    rw [hV₀e, image_inter h.injective]
    exact ⟨hpE, hpV⟩
  have hne : ((h '' E ∩ G) ∩ h '' V₀).Nonempty := by
    have heV : (e : M) ∈ V₀ := by rw [hV₀e] at heA; exact heA.2
    exact ⟨h e, ⟨⟨e, e.2, rfl⟩, hCG hheC⟩, e, heV, rfl⟩
  have hW := continuum_subset_layer_of_open hX hi hG hWc
    inter_subset_right hV hne hWV
  have hEG : h '' E ⊆ G := by
    refine subset_of_meets_avoids hHU hAT hGc hd hhE ⟨h e, hCG hheC, e, e.2, rfl⟩ ?_
    rw [disjoint_left]
    rintro p hpE hpX
    have hpG : p ∈ G := by
      rcases hpX with ⟨y, -, rfl⟩ | ⟨y, -, rfl⟩ <;> exact y.2
    have hpC := hW ⟨hpE, hpG⟩
    set p' : G := ⟨p, hpG⟩
    have hpv : d p' = v := param_of_mem_layer hpC
    rcases hpX with hp0 | hp1
    · have := param_of_mem_layer (x := p') hp0
      rw [hpv] at this
      exact absurd this (ne_of_gt hv0)
    · have := param_of_mem_layer (x := p') hp1
      rw [hpv] at this
      exact absurd this (ne_of_lt hv1)
  exact fun p hp => hW ⟨hp, hEG hp⟩

/-- **The translate of an extension.** If `F` is an extension of `E` away from `k⁻¹(0)` (map `d`)
and an interior layer `d⁻¹(v)` contains `h[E]`, then it contains `h[F]`. -/
theorem translate_extension_subset_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E F : Set M} {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F) (hX0 : layer d 0 = layer k 0) {v : unitInterval}
    (hv0 : 0 < v) (hv1 : v < 1) (h : M ≃ₜ M) (hhE : h '' E ⊆ layer d v) :
    h '' F ⊆ layer d v := by
  obtain ⟨s, hs0, hseg, -⟩ := hagopian76_initial_segment hX hi hE hF hEF hX0
  refine translate_subset_layer hX hi hF hF hv0 hv1 h (A := Iio s) isOpen_Iio ⟨0, hs0⟩ ?_
  refine (image_mono ?_).trans hhE
  rw [← hseg]
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, ⟨unitInterval.nonneg', le_of_lt hy⟩, rfl⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **A layer of an extension beyond `E`** (commission 172 §1.A.1): with `E = d⁻¹[[0, s]]`, a layer
`d⁻¹(v)` not contained in `E` misses `E`. -/
theorem layer_disjoint_of_not_subset {E F : Set M} {d : F → unitInterval} {s : unitInterval}
    (hseg : layerSet d (Icc 0 s) = E) {v : unitInterval} (hv : ¬ layer d v ⊆ E) :
    Disjoint (layer d v) E := by
  have hsv : s < v := by
    by_contra hle
    push_neg at hle
    apply hv
    rw [← hseg]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy) ▸ hle⟩, rfl⟩
  rw [disjoint_left]
  rintro p ⟨y, hy, rfl⟩ hpE
  rw [← hseg] at hpE
  obtain ⟨y', hy', hyy⟩ := hpE
  have : y' = y := Subtype.ext hyy
  subst this
  rw [mem_preimage, mem_singleton_iff.1 hy] at hy'
  exact absurd hy'.2 (not_le.2 hsv)

end Swallow

end HPC.Hagopian
