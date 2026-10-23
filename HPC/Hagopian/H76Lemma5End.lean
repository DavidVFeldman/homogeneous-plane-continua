import HPC.Hagopian.H76Far

/-!
# Batch 158, item B: Lemma 5 at the end sets

Hagopian 1976, Lemma 5 (p. 341): "The decomposition of `E` is continuous." Batch 157 proved it at the
layers other than the end sets (`lemma5_interior_aux`) and reduced it to the end sets
(`lemma5_of_ends_aux`). At the end set `X = k⁻¹(0)` (commission 158, item B):

1. take a proper extension `G` of `E` away from `Z = k⁻¹(1)` (Lemma 4, `exists_proper_extension`,
   applied to the reversed map `1 − k`);
2. item A (`far_layer_aux`, applied to `1 − k`) makes `X` a layer `D⁻¹(s)`, `0 < s < 1`, of `G`, and
   every layer of `E` a layer of `G` (`ext_layers`);
3. the decomposition of `G` is lower semicontinuous at `X` (`lemma5_interior_aux` applied to `G`),
   and this passes to `E` (`lscAt_of_ext`).

At `Z` the same, with an extension away from `X`. Hagopian's two-sided `F` is not used.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Lemma5End

/-- The reversed map of a minimal admissible map is minimal admissible. -/
theorem IsMinimalAdmissible.symm_comp {X : Type*} [MetricSpace X] {E : Set X}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsMinimalAdmissible E (unitInterval.symm ∘ k) :=
  ⟨hE.1, isAdmissibleMap_symm hE.2.1, interior_symm_fibre hE.2.2⟩

/-- The layers of the reversed map. -/
theorem layer_symm_comp {X : Type*} {E : Set X} (k : E → unitInterval) (t : unitInterval) :
    layer (unitInterval.symm ∘ k) t = layer k (unitInterval.symm t) := by
  ext x
  simp only [layer, mem_image, mem_preimage, Function.comp_apply, mem_singleton_iff]
  constructor
  · rintro ⟨y, h, rfl⟩; exact ⟨y, by rw [← h, unitInterval.symm_symm], rfl⟩
  · rintro ⟨y, h, rfl⟩; exact ⟨y, by rw [h, unitInterval.symm_symm], rfl⟩

variable {M : Set Pt}

/-- **The layers of `E` are layers of a proper extension** (item A, packaged): for an extension
`F ≠ E` of `E` away from `k⁻¹(0)`, there is `0 < s < 1` with `d⁻¹(s) = k⁻¹(1)`,
`d⁻¹[[0, s]] = E`, and the layer of `F` through a point of `E` is its layer in `E`. -/
theorem ext_layers [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E F : Set M} {k : E → unitInterval} {d : F → unitInterval}
    (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F)
    (hX0 : layer d 0 = layer k 0) (hne : F ≠ E) :
    ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ layer d s = layer k 1 ∧ layerSet d (Icc 0 s) = E ∧
      (∀ z : E, layer d (d ⟨z, hEF z.2⟩) = layer k (k z)) ∧
      ∀ t : unitInterval, ∃ u : unitInterval, layer k t = layer d u := by
  obtain ⟨s, hs0, hlow, hup, hin, heq, hle, -, h1, h2⟩ := far_layer_aux hX hi hE hF hEF hX0
  have hs1 : s < 1 := lt_of_le_of_ne unitInterval.le_one' (fun h => hne (h1 h))
  have hW := h2 hs1
  refine ⟨s, hs0, hs1, hW, ?_, fun z => ?_, fun t => ?_⟩
  · refine Subset.antisymm ?_ hup
    rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    rcases hy.lt_or_eq with h | h
    · exact hlow ⟨y, ⟨unitInterval.nonneg', h⟩, rfl⟩
    · have : (y : M) ∈ layer d s := ⟨y, h, rfl⟩
      rw [hW] at this
      exact layer_subset_dom k 1 this
  · obtain ⟨u, hu⟩ := hin (k z)
    have hzu : (z : M) ∈ layer d u := hu ⟨z, rfl, rfl⟩
    have hu' : u = d ⟨z, hEF z.2⟩ := layer_param_eq hzu ⟨⟨z, hEF z.2⟩, rfl, rfl⟩
    rw [← hu']
    rcases (hle _ u hu).lt_or_eq with h | rfl
    · exact (heq _ u h hu).symm
    · have hz1 : (z : M) ∈ layer k 1 := hW ▸ hzu
      have : k z = 1 := layer_param_eq ⟨z, rfl, rfl⟩ hz1
      rw [hW, this]
  · obtain ⟨u, hu⟩ := hin t
    rcases (hle t u hu).lt_or_eq with h | rfl
    · exact ⟨u, heq t u h hu⟩
    · obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 t
      have ht : t = 1 := layer_param_eq hx (hW ▸ hu hx)
      exact ⟨u, by rw [ht, hW]⟩

/-- **`E` is an initial segment of every extension** (item A, the strong form): `d⁻¹[[0, s]] = E`
and every layer of `E` is a layer of `F`. If `F = E`, then `s = 1` and the two decompositions
coincide (both inclusions of `far_layer_aux` apply). -/
theorem initial_segment_aux [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E F : Set M} {k : E → unitInterval} {d : F → unitInterval}
    (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F)
    (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ layerSet d (Icc 0 s) = E ∧
      ∀ t : unitInterval, ∃ u : unitInterval, layer k t = layer d u := by
  by_cases hne : F = E
  · subst hne
    obtain ⟨s, -, -, hup, hin, heq, -, hZ, -, -⟩ := far_layer_aux hX hi hE hF hEF hX0
    obtain ⟨-, -, -, -, hin', -, -, -, -, -⟩ := far_layer_aux hX hi hF hE hEF hX0.symm
    have hs1 : s = 1 := by
      obtain ⟨y, hy⟩ := hF.2.1.2.1 1
      obtain ⟨y', hy's, hyy⟩ := hup y.2
      have : y' = y := Subtype.ext hyy
      have h2 : d y ∈ Icc 0 s := this ▸ hy's
      rw [hy] at h2
      exact le_antisymm unitInterval.le_one' h2.2
    subst hs1
    refine ⟨1, zero_lt_one, ?_, fun t => ?_⟩
    · ext x
      constructor
      · rintro ⟨y, -, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, ⟨unitInterval.nonneg', unitInterval.le_one'⟩, rfl⟩
    obtain ⟨u, hu⟩ := hin t
    by_cases hu1 : u = 1
    · subst hu1
      obtain ⟨u', hu'⟩ := hin' 1
      have hks := hE.2.1.2.1
      obtain ⟨x, hx⟩ := layer_nonempty hks t
      have ht : t = u' := layer_param_eq hx (hu' (hu hx))
      subst ht
      exact ⟨1, Subset.antisymm hu hu'⟩
    · exact ⟨u, heq t u (lt_of_le_of_ne unitInterval.le_one' hu1) hu⟩
  · obtain ⟨s, hs0, -, -, hseg, -, hlay⟩ := ext_layers hX hi hE hF hEF hX0 hne
    exact ⟨s, hs0, hseg, hlay⟩

/-- **Lower semicontinuity passes to a subcontinuum whose layers are layers of the larger one.** -/
theorem lscAt_of_ext {E G : Set M} [CompactSpace E] [CompactSpace G] {k : E → unitInterval}
    {D : G → unitInterval} (hEG : E ⊆ G)
    (hlay : ∀ z : E, layer D (D ⟨z, hEG z.2⟩) = layer k (k z)) (x : E)
    (hG : LSCAt (Setoid.ker D) ⟨x, hEG x.2⟩) : LSCAt (Setoid.ker k) x := by
  intro y hy V hV hyV
  obtain ⟨V', hV'o, rfl⟩ := isOpen_induced_iff.1 hV
  have hmem : ∀ z w : E, k z = k w → D ⟨z, hEG z.2⟩ = D ⟨w, hEG w.2⟩ := by
    intro z w h
    have : (z : M) ∈ layer D (D ⟨w, hEG w.2⟩) := by
      rw [hlay w, ← h]; exact ⟨z, rfl, rfl⟩
    exact layer_param_eq ⟨_, rfl, rfl⟩ this
  obtain ⟨W, hWo, hWc, hWz⟩ := hG ⟨y, hEG y.2⟩ (hmem y x hy) (Subtype.val ⁻¹' V')
    (hV'o.preimage continuous_subtype_val) hyV
  have hinc : Continuous (fun z : E => (⟨z, hEG z.2⟩ : G)) :=
    continuous_subtype_val.subtype_mk _
  refine ⟨(fun z : E => (⟨z, hEG z.2⟩ : G)) ⁻¹' W, hWo.preimage hinc,
    fun z hz => hWc (hmem z x hz), fun z hz => ?_⟩
  obtain ⟨v, hv, hvV⟩ := hWz _ hz
  have : (v : M) ∈ layer k (k z) := by
    rw [← hlay z]; exact ⟨v, hv, rfl⟩
  obtain ⟨e, he, hev⟩ := this
  exact ⟨e, he, show (e : M) ∈ V' by rw [hev]; exact hvV⟩

/-- **Lemma 5 at an end set**, in the form: lower semicontinuity of `E` at a point of the layer that
an extension makes interior. -/
theorem lscAt_end_aux [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E : Set M} [CompactSpace E] {k k' : E → unitInterval}
    (hE' : IsMinimalAdmissible E k') (hkk : ∀ z w, k z = k w ↔ k' z = k' w) (x : E)
    (hx : k' x = 1) : LSCAt (Setoid.ker k) x := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  obtain ⟨G, hEG, D, hD, hD0⟩ := exists_proper_extension hX hHU hAT hE'
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hD.isCompact
  obtain ⟨s, hs0, hs1, hW, -, hlay, -⟩ := ext_layers hX hi hE' hD hEG.1 hD0 hEG.ne'
  have hker : Setoid.ker k = Setoid.ker k' := by
    ext z w; exact hkk z w
  rw [hker]
  refine lscAt_of_ext hEG.1 hlay x ?_
  have hxs : D ⟨x, hEG.1 x.2⟩ = s := by
    have : (x : M) ∈ layer D s := by rw [hW, ← hx]; exact ⟨x, rfl, rfl⟩
    exact (layer_param_eq this ⟨_, rfl, rfl⟩).symm
  exact lemma5_interior_aux hX hi hD _ (hxs ▸ hs0) (hxs ▸ hs1)

/-- **Lemma 5** (p. 341): the decomposition of `E` is continuous. -/
theorem lemma5_aux [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E : Set M} [CompactSpace E] {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) : IsContinuousDecomp (Setoid.ker k) := by
  refine lemma5_of_ends_aux hX hi hE fun x hx => ?_
  rcases hx with hx0 | hx1
  · refine lscAt_end_aux hX hi hE.symm_comp (fun z w => ?_) x (by simp [hx0])
    simp only [Function.comp_apply]
    exact ⟨fun h => by rw [h], fun h => by simpa using congrArg unitInterval.symm h⟩
  · exact lscAt_end_aux hX hi hE (fun z w => Iff.rfl) x hx1

end Lemma5End

end HPC.Hagopian
