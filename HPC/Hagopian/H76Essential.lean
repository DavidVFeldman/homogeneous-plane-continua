import HPC.Hagopian.H76Composant

/-!
# Batch 160, item A: "every continuum essential to `R(E)` is of type A′ (Lemma 5)" (p. 343)

Let `H` be essential to `R(E)`: a continuum in `R(E) = R(X, E) ∪ R(Z, E)` meeting two layers of some
extension of `E`.

* If `H ⊆ R(X, E)`, then `H` lies in one extension `G` away from `X` (`exists_ext_of_subset`), and
  meets two layers of `G` (the layers of `E`, and of a smaller extension, are layers of `G`; if the
  given extension is away from `Z`, the two points lie in `E`, since the two sides meet only in `E`,
  `ext_inter_subset`). Then `isTypeA'_of_subcontinuum` with Lemma 5 (`essential_typeA'_of_subset`).
* If `H ⊆ R(Z, E)`: the same for the reversed map.
* Otherwise `H` meets `X` and `Z` (absorption), so `H ⊇ E`; `H ∩ R(X, E)` lies in one extension `K`
  away from `X`, and `H ∩ R(Z, E)` in one extension `Q` away from `Z` (`exists_ext_cover`; otherwise
  `H ∪ F₀ ⊇ Cl R(E)` and `H = Cl R(E)`, which is impossible as `R(E)` is not closed). With `b` a
  point of `H ∩ K` farthest out in `K` and `a` a point of `H ∩ Q` farthest out in `Q`, `H` is
  irreducible between `a` and `b` (Lemma 5 in `K` and `Q`), and `H ⊆ (H ∩ Q) ∪ (H ∩ K)` with
  `a ∉ K`, `b ∉ Q`; Kuratowski's criterion with the 1975 ¶2 argument (`isTypeA'_of_decomposable`,
  `no_indecomposable_interior_aux`) makes `H` of type A′ (`essential_typeA'_two_sided`).

The containment of report 158 §1.C (an essential continuum lies in one extension) is
`exists_ext_of_subset`; it uses that `R(X, E)` is not closed (`not_isClosed_extUnion`, from Lemma 6),
not the point `c` of step 5.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Ess

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- Lemma 5, in the form used here. -/
theorem lsc_of_minimalAdmissible (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {G : Set M} {d : G → unitInterval} (hd : IsMinimalAdmissible G d) :
    ∀ x, LSCAt (Setoid.ker d) x := by
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hd.isCompact
  exact (hagopian76_lemma5 hX hi hd).2

omit [CompactSpace M] [ConnectedSpace M] in
theorem Rset_symm_comp {E : Set M} (k : E → unitInterval) :
    Rset (unitInterval.symm ∘ k) = Rset k := by
  unfold Rset
  rw [layer_symm_comp, layer_symm_comp, unitInterval.symm_zero,
    unitInterval.symm_one, union_comm]

omit [CompactSpace M] [ConnectedSpace M] in
theorem IsEssential.symm_comp {E : Set M} {k : E → unitInterval} {H : Set M}
    (hH : IsEssential k H) : IsEssential (unitInterval.symm ∘ k) H := by
  obtain ⟨hHR, hHc, F, d, hEF, hd, hdX, rest⟩ := hH
  refine ⟨by rw [Rset_symm_comp]; exact hHR, hHc, F, d, hEF, hd, ?_, rest⟩
  rw [layer_symm_comp, layer_symm_comp, unitInterval.symm_zero, unitInterval.symm_one]
  exact hdX.symm

omit [CompactSpace M] [ConnectedSpace M] in
/-- The far layer of `E` sits at the top of `E` inside an extension. -/
theorem end_layer_param {E F : Set M} {k : E → unitInterval} {d : F → unitInterval}
    (hE : IsMinimalAdmissible E k) (hd : IsMinimalAdmissible F d) {σ u : unitInterval}
    (hseg : layerSet d (Icc 0 σ) = E) (h0 : layer d 0 = layer k 0) (h1 : layer k 1 = layer d u) :
    u = σ := by
  have hFc : Fold.Q78.IsContinuum F := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hd; exact hab.1
  obtain ⟨v, hv⟩ := hd.2.1.2.1 u
  have hvE : (v : M) ∈ E := by
    have : (v : M) ∈ layer k 1 := by rw [h1]; exact ⟨v, hv, rfl⟩
    exact img_subset _ this
  have huσ : u ≤ σ := by
    have : (v : M) ∈ layerSet d (Icc 0 σ) := by rw [hseg]; exact hvE
    have h := (mem_layerSet_val.1 this).2
    rwa [hv] at h
  have hsub : layerSet d (Icc 0 u) ⊆ E := by
    rw [← hseg]; rintro _ ⟨w, hw, rfl⟩; exact ⟨w, ⟨hw.1, hw.2.trans huσ⟩, rfl⟩
  have hc := isContinuum_img hFc.1 hd.2.1 (S := Icc 0 u) isClosed_Icc isPreconnected_Icc
    ⟨0, le_rfl, unitInterval.nonneg'⟩
  obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 0
  obtain ⟨z, hz⟩ := layer_nonempty hE.2.1.2.1 1
  have hx' : x ∈ layerSet d (Icc 0 u) := by
    rw [← h0] at hx; obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, ⟨unitInterval.nonneg', by rw [show d w = 0 from hw]; exact unitInterval.nonneg'⟩, rfl⟩
  have hz' : z ∈ layerSet d (Icc 0 u) := by
    rw [h1] at hz; obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, ⟨unitInterval.nonneg', by rw [show d w = u from hw]⟩, rfl⟩
  have heq := end_sets_aux hE hsub hc ⟨x, hx', hx⟩ ⟨z, hz', hz⟩
  obtain ⟨w, hw⟩ := hd.2.1.2.1 σ
  have hwE : (w : M) ∈ E := by
    rw [← hseg]; exact mem_layerSet_val.2 (show d w ∈ Icc 0 σ from ⟨unitInterval.nonneg', hw.le⟩)
  rw [← heq] at hwE
  have h := (mem_layerSet_val.1 hwE).2
  rw [hw] at h
  exact le_antisymm huσ h

/-- **Case `H ⊆ R(X, E)`.** -/
theorem essential_typeA'_of_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsEssential k H) (hHR : H ⊆ extUnion E (layer k 0)) : IsTypeA' H := by
  obtain ⟨-, hHc, F, d, hEF, hd, hdX, t₁, t₂, ht, h₁, h₂⟩ := hH
  obtain ⟨G, hG, hHG⟩ := exists_ext_of_subset hX hi hE hHc hHR
  have hlayer_ne : ∀ {Y : Set M} {g : Y → unitInterval}, IsMinimalAdmissible Y g →
      ∀ {a b : unitInterval}, layer g a = layer g b → a = b := by
    intro Y g hg a b hab
    obtain ⟨y, hy⟩ := layer_nonempty hg.2.1.2.1 a
    exact layer_param_eq hy (hab ▸ hy)
  -- an extension `G'` containing `H` and meeting `H` in two of its layers
  obtain ⟨G', hHG', dG, hdG, u₁, u₂, hu, hu₁, hu₂⟩ : ∃ G' : Set M, H ⊆ G' ∧
      ∃ dG : G' → unitInterval, IsMinimalAdmissible G' dG ∧ ∃ u₁ u₂ : unitInterval, u₁ ≠ u₂ ∧
        (H ∩ layer dG u₁).Nonempty ∧ (H ∩ layer dG u₂).Nonempty := by
    rcases hdX with hdX | hdX
    · obtain ⟨G', hG', hFG', hGG'⟩ := ext_upper hX hi hE ⟨hEF, d, hd, hdX⟩ hG
      obtain ⟨-, dG, hdG, hdGX⟩ := hG'
      obtain ⟨-, -, -, hlay⟩ := hagopian76_initial_segment hX hi hd hdG hFG' (hdGX.trans hdX.symm)
      obtain ⟨u₁, hu₁⟩ := hlay t₁
      obtain ⟨u₂, hu₂⟩ := hlay t₂
      refine ⟨G', hHG.trans hGG', dG, hdG, u₁, u₂, fun h => ht ?_, hu₁ ▸ h₁, hu₂ ▸ h₂⟩
      exact hlayer_ne hd (hu₁.trans (h ▸ hu₂.symm))
    · obtain ⟨p₁, hp₁H, hp₁⟩ := h₁
      obtain ⟨p₂, hp₂H, hp₂⟩ := h₂
      have hp₁E : p₁ ∈ E := ext_inter_subset hX hi hE hG ⟨hEF, d, hd, hdX⟩
        ⟨hHG hp₁H, img_subset _ hp₁⟩
      have hp₂E : p₂ ∈ E := ext_inter_subset hX hi hE hG ⟨hEF, d, hd, hdX⟩
        ⟨hHG hp₂H, img_subset _ hp₂⟩
      have hdX' : layer d 0 = layer (unitInterval.symm ∘ k) 0 := by
        rw [layer_symm_comp, unitInterval.symm_zero]; exact hdX
      obtain ⟨-, -, -, hlayF⟩ := hagopian76_initial_segment hX hi hE.symm_comp hd hEF hdX'
      have hk12 : k ⟨p₁, hp₁E⟩ ≠ k ⟨p₂, hp₂E⟩ := by
        intro hkeq
        obtain ⟨v, hv⟩ := hlayF (unitInterval.symm (k ⟨p₁, hp₁E⟩))
        rw [layer_symm_comp, unitInterval.symm_symm] at hv
        have hq₁ : p₁ ∈ layer d v := by rw [← hv]; exact ⟨⟨p₁, hp₁E⟩, rfl, rfl⟩
        have hq₂ : p₂ ∈ layer d v := by rw [← hv, hkeq]; exact ⟨⟨p₂, hp₂E⟩, rfl, rfl⟩
        exact ht ((layer_param_eq hp₁ hq₁).trans (layer_param_eq hq₂ hp₂))
      obtain ⟨hEG, dG, hdG, hdGX⟩ := hG
      obtain ⟨-, -, -, hlay⟩ := hagopian76_initial_segment hX hi hE hdG hEG hdGX
      obtain ⟨u₁, hu₁⟩ := hlay (k ⟨p₁, hp₁E⟩)
      obtain ⟨u₂, hu₂⟩ := hlay (k ⟨p₂, hp₂E⟩)
      refine ⟨G, hHG, dG, hdG, u₁, u₂, fun h => hk12 ?_, ⟨p₁, hp₁H, ?_⟩, ⟨p₂, hp₂H, ?_⟩⟩
      · exact hlayer_ne hE (hu₁.trans (h ▸ hu₂.symm))
      · rw [← hu₁]; exact ⟨⟨p₁, hp₁E⟩, rfl, rfl⟩
      · rw [← hu₂]; exact ⟨⟨p₂, hp₂E⟩, rfl, rfl⟩
  haveI : CompactSpace G' := isCompact_iff_compactSpace.mp hdG.isCompact
  obtain ⟨-, -, -, -, hA'⟩ := isTypeA'_of_subcontinuum hdG (lsc_of_minimalAdmissible hX hi hdG)
    hHG' hHc hu hu₁ hu₂
  exact hA'

/-- **`R(E)` is not closed.** -/
theorem not_isClosed_Rset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) : ¬ IsClosed (Rset k) := by
  intro hRc
  have hHU := hagopian75_lemma1_hu hX hi
  have hI := lemma6_aux hX hi hE
  rw [hRc.closure_eq] at hI
  obtain ⟨p, hp⟩ := layer_nonempty hE.2.1.2.1 0
  have hpE : p ∈ E := img_subset _ hp
  have hER : E ⊆ Rset k :=
    (IsExtensionAway.subset_extUnion ⟨subset_rfl, k, hE, rfl⟩).trans subset_union_left
  obtain ⟨b, hbR, hb⟩ := T13.exists_not_mem_proper_subcontinua hI (hER hpE)
  rcases hbR with ⟨F, hF, hbF⟩ | ⟨F, hF, hbF⟩
  · have hFR : F ⊆ Rset k := (IsExtensionAway.subset_extUnion hF).trans subset_union_left
    refine hb F (IsExtensionAway.isContinuum hF) hFR (fun heq => ?_) (hF.1 hpE) hbF
    obtain ⟨-, d, hd, -⟩ := hF
    exact not_indec_of_minimalAdmissible hHU hd (by rw [heq]; exact hI)
  · have hFR : F ⊆ Rset k := (IsExtensionAway.subset_extUnion hF).trans subset_union_right
    refine hb F (IsExtensionAway.isContinuum hF) hFR (fun heq => ?_) (hF.1 hpE) hbF
    obtain ⟨-, d, hd, -⟩ := hF
    exact not_indec_of_minimalAdmissible hHU hd (by rw [heq]; exact hI)

/-- **A continuum in `R(E)` through a point of `X`: its part in `R(X, E)` lies in one extension away
from `X`.** -/
theorem exists_ext_cover (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hHc : Fold.Q78.IsContinuum H) (hHR : H ⊆ Rset k) (hHX : (H ∩ layer k 0).Nonempty) :
    ∃ K, IsExtensionAway E (layer k 0) K ∧ H ∩ extUnion E (layer k 0) ⊆ K := by
  have hHU := hagopian75_lemma1_hu hX hi
  obtain ⟨Fs, hmono, hFs, hRU⟩ := hagopian76_lemma4_seq hX hi hE
  by_contra hcon
  push_neg at hcon
  have hnot : ∀ j, ¬ (H ∩ extUnion E (layer k 0) ⊆ Fs j) := fun j => hcon _ (hFs j)
  obtain ⟨g₀, hg₀H, hg₀X⟩ := hHX
  have hsub := subset_union_of_escape hX hi hmono hFs hRU hHc hg₀H
    (IsExtensionAway.end_subset (hFs 0) hg₀X) hnot
  have hI := lemma6_aux hX hi hE
  have hRI : Rset k ⊆ closure (Rset k) := subset_closure
  have hF0R : Fs 0 ⊆ Rset k := (IsExtensionAway.subset_extUnion (hFs 0)).trans subset_union_left
  have hcov : closure (Rset k) ⊆ H ∪ Fs 0 := by
    rw [← closure_extUnion_aux hX hi hE]
    exact closure_minimal hsub (hHc.1.isClosed.union (IsExtensionAway.isContinuum (hFs 0)).1.isClosed)
  have hU : H ∪ Fs 0 = closure (Rset k) :=
    Subset.antisymm (union_subset (hHR.trans hRI) (hF0R.trans hRI)) hcov
  rcases hI.2 H (Fs 0) hHc (IsExtensionAway.isContinuum (hFs 0)) (hHR.trans hRI) (hF0R.trans hRI)
      hU with h | h
  · apply not_isClosed_Rset hX hi hE
    have : Rset k = closure (Rset k) := Subset.antisymm hRI (h ▸ hHR)
    rw [this]; exact isClosed_closure
  · obtain ⟨-, d, hd, -⟩ := hFs 0
    exact not_indec_of_minimalAdmissible hHU hd (by rw [h]; exact hI)

/-- **The two-sided case.** -/
theorem essential_typeA'_two_sided (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hHc : Fold.Q78.IsContinuum H) (hHR : H ⊆ Rset k) (hnX : ¬ H ⊆ extUnion E (layer k 0))
    (hnZ : ¬ H ⊆ extUnion E (layer k 1)) : IsTypeA' H := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  have hEc : Fold.Q78.IsContinuum E := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE; exact hab.1
  set k' := unitInterval.symm ∘ k with hk'
  have hE' : IsMinimalAdmissible E k' := hE.symm_comp
  have hk'0 : layer k' 0 = layer k 1 := by rw [layer_symm_comp, unitInterval.symm_zero]
  have hk'1 : layer k' 1 = layer k 0 := by rw [layer_symm_comp, unitInterval.symm_one]
  -- `H` meets `X`
  have hHX : (H ∩ layer k 0).Nonempty := by
    by_contra hdis
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdis
    obtain ⟨h, hhH, hhX⟩ : ∃ h ∈ H, h ∈ extUnion E (layer k 0) := by
      by_contra hn; push_neg at hn
      exact hnZ fun y hy => (hHR hy).resolve_left (hn y hy)
    obtain ⟨K, hK, hhK⟩ := hhX
    exact hnX (subset_extUnion_of_meets hX hHU hAT hK hHc hdis ⟨h, hhH, hhK⟩)
  -- `H` meets `Z`
  have hHZ : (H ∩ layer k 1).Nonempty := by
    by_contra hdis
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdis
    obtain ⟨x₀, hx₀H, hx₀X⟩ := hHX
    have hEZ : IsExtensionAway E (layer k' 0) E := ⟨subset_rfl, k', hE', rfl⟩
    have := subset_extUnion_of_meets hX hHU hAT hEZ hHc (by rw [hk'0]; exact hdis)
      ⟨x₀, hx₀H, img_subset _ hx₀X⟩
    rw [hk'0] at this
    exact hnZ this
  -- `E ⊆ H`
  have hEH : E ⊆ H := by
    obtain ⟨x₀, hx₀H, hx₀X⟩ := hHX
    obtain ⟨z₀, hz₀H, hz₀Z⟩ := hHZ
    have hHE := isContinuum_inter_of_HU hHU hHc hEc ⟨x₀, hx₀H, img_subset _ hx₀X⟩
    have := end_sets_aux hE inter_subset_right hHE ⟨x₀, ⟨hx₀H, img_subset _ hx₀X⟩, hx₀X⟩
      ⟨z₀, ⟨hz₀H, img_subset _ hz₀Z⟩, hz₀Z⟩
    rw [← this]; exact inter_subset_left
  -- the two extensions
  obtain ⟨K, hK, hHK⟩ := exists_ext_cover hX hi hE hHc hHR hHX
  obtain ⟨Q, hQ', hHQ'⟩ := exists_ext_cover hX hi hE' hHc (by rw [Rset_symm_comp]; exact hHR)
    (by rw [hk'0]; exact hHZ)
  rw [hk'0] at hQ' hHQ'
  have hKQ := ext_inter_subset hX hi hE hK hQ'
  have hKc := IsExtensionAway.isContinuum hK
  have hQc := IsExtensionAway.isContinuum hQ'
  have hEK := hK.1
  have hEQ := hQ'.1
  have hHKQ : H ⊆ K ∪ Q := by
    intro y hy
    rcases hHR hy with h | h
    · exact Or.inl (hHK ⟨hy, h⟩)
    · exact Or.inr (hHQ' ⟨hy, h⟩)
  obtain ⟨b₀, hb₀H, hb₀E⟩ : ∃ b₀ ∈ H ∩ K, b₀ ∉ E := by
    by_contra hn; push_neg at hn
    apply hnZ
    intro y hy
    rcases hHKQ hy with h | h
    · exact IsExtensionAway.subset_extUnion hQ' (hEQ (hn y ⟨hy, h⟩))
    · exact IsExtensionAway.subset_extUnion hQ' h
  obtain ⟨a₀, ha₀H, ha₀E⟩ : ∃ a₀ ∈ H ∩ Q, a₀ ∉ E := by
    by_contra hn; push_neg at hn
    apply hnX
    intro y hy
    rcases hHKQ hy with h | h
    · exact IsExtensionAway.subset_extUnion hK h
    · exact IsExtensionAway.subset_extUnion hK (hEK (hn y ⟨hy, h⟩))
  obtain ⟨-, dK, hdK, hdKX⟩ := hK
  obtain ⟨-, e, he, heZ⟩ := hQ'
  have heZ' : layer e 0 = layer k' 0 := by rw [hk'0]; exact heZ
  obtain ⟨s, -, hsegK, -⟩ := hagopian76_initial_segment hX hi hE hdK hEK hdKX
  obtain ⟨σ, -, hsegQ, hlayQ⟩ := hagopian76_initial_segment hX hi hE' he hEQ heZ'
  obtain ⟨u, hu⟩ := hlayQ 1
  have huσ : u = σ := end_layer_param hE' he hsegQ heZ' hu
  have hXu : layer k 0 = layer e σ := by rw [← hk'1, hu, huσ]
  have hLK := lsc_of_minimalAdmissible hX hi hdK
  have hLQ := lsc_of_minimalAdmissible hX hi he
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hdK.isCompact
  haveI : CompactSpace Q := isCompact_iff_compactSpace.mp he.isCompact
  -- the extreme points `b ∈ H ∩ K`, `a ∈ H ∩ Q`
  have hSKc : IsCompact (Subtype.val ⁻¹' H : Set K) :=
    (hHc.1.isClosed.preimage continuous_subtype_val).isCompact
  have hSQc : IsCompact (Subtype.val ⁻¹' H : Set Q) :=
    (hHc.1.isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨b, hbH, hbmax⟩ := hSKc.exists_isMaxOn ⟨⟨b₀, hb₀H.2⟩, hb₀H.1⟩ hdK.2.1.1.continuousOn
  obtain ⟨a, haH, hamax⟩ := hSQc.exists_isMaxOn ⟨⟨a₀, ha₀H.2⟩, ha₀H.1⟩ he.2.1.1.continuousOn
  have hb₀s : s < dK ⟨b₀, hb₀H.2⟩ := lt_of_not_ge fun h =>
    hb₀E (by rw [← hsegK]; exact mem_layerSet_val (y := ⟨b₀, hb₀H.2⟩) |>.2 ⟨unitInterval.nonneg', h⟩)
  have ha₀σ : σ < e ⟨a₀, ha₀H.2⟩ := lt_of_not_ge fun h =>
    ha₀E (by rw [← hsegQ]; exact mem_layerSet_val (y := ⟨a₀, ha₀H.2⟩) |>.2 ⟨unitInterval.nonneg', h⟩)
  have hbs : s < dK b := lt_of_lt_of_le hb₀s (hbmax (show (⟨b₀, hb₀H.2⟩ : K) ∈ _ from hb₀H.1))
  have haσ : σ < e a := lt_of_lt_of_le ha₀σ (hamax (show (⟨a₀, ha₀H.2⟩ : Q) ∈ _ from ha₀H.1))
  have hbE : (b : M) ∉ E := fun h => by
    have : (b : M) ∈ layerSet dK (Icc 0 s) := by rw [hsegK]; exact h
    exact absurd (mem_layerSet_val.1 this).2 (not_le.2 hbs)
  have haE : (a : M) ∉ E := fun h => by
    have : (a : M) ∈ layerSet e (Icc 0 σ) := by rw [hsegQ]; exact h
    exact absurd (mem_layerSet_val.1 this).2 (not_le.2 haσ)
  have hbQ : (b : M) ∉ Q := fun h => hbE (hKQ ⟨b.2, h⟩)
  have haK : (a : M) ∉ K := fun h => haE (hKQ ⟨h, a.2⟩)
  have hβ : 0 < dK b := lt_of_le_of_lt unitInterval.nonneg' hbs
  have hβ' : 0 < e a := lt_of_le_of_lt unitInterval.nonneg' haσ
  -- the pieces `H ∩ K`, `H ∩ Q` are initial segments
  have hpiece : ∀ H' ⊆ H, Fold.Q78.IsContinuum H' → (a : M) ∈ H' → (b : M) ∈ H' → H ⊆ H' := by
    intro H' hH'H hH'c haH' hbH'
    have hH'K := isContinuum_inter_of_HU hHU hH'c hKc ⟨b, hbH', b.2⟩
    have hH'Q := isContinuum_inter_of_HU hHU hH'c hQc ⟨a, haH', a.2⟩
    obtain ⟨y, hyH', hyK, hyQ⟩ := meets_inter_of_cover hH'c.2.2 hKc.1.isClosed hQc.1.isClosed
      (hH'H.trans hHKQ) ⟨b, hbH', b.2⟩ ⟨a, haH', a.2⟩
    have hyE : y ∈ E := hKQ ⟨hyK, hyQ⟩
    -- `X ⊆ H'`
    let y' : Q := ⟨y, hyQ⟩
    have hyσ : e y' ≤ σ := by
      have : (y' : M) ∈ layerSet e (Icc 0 σ) := by rw [hsegQ]; exact hyE
      exact (mem_layerSet_val.1 this).2
    have hIoo := layerSet_Ioo_subset he inter_subset_right hH'Q ⟨y, ⟨hyH', hyQ⟩, y', rfl, rfl⟩
      ⟨a, ⟨haH', a.2⟩, a, rfl, rfl⟩
    have hXH' : layer k 0 ⊆ H' := by
      rw [hXu]
      rcases eq_or_lt_of_le hyσ with h | h
      · have := layer_subset_closure_Ioo he hLQ haσ
        rw [← h] at this ⊢
        exact fun v hv => (closure_minimal hIoo hH'Q.1.isClosed (this hv)).1
      · rintro _ ⟨v, hv, rfl⟩
        have hv' : e v = σ := hv
        exact (hIoo (mem_layerSet_val.2 (show e v ∈ Ioo (e y') (e a) by
          rw [hv']; exact ⟨h, haσ⟩))).1
    -- `H ∩ K ⊆ H'`
    have hKseg : ∀ H'' ⊆ H, Fold.Q78.IsContinuum H'' → (b : M) ∈ H'' → layer k 0 ⊆ H'' →
        H'' ∩ K = layerSet dK (Icc 0 (dK b)) := by
      intro H'' hH''H hH''c hbH'' hXH''
      have hc := isContinuum_inter_of_HU hHU hH''c hKc ⟨b, hbH'', b.2⟩
      obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 0
      refine eq_layerSet_of_subcontinuum hdK hLK inter_subset_right hc hβ
        ⟨x, ⟨hXH'' hx, hEK (img_subset _ hx)⟩, by rw [hdKX]; exact hx⟩
        ⟨b, ⟨hbH'', b.2⟩, b, rfl, rfl⟩ ?_
      rintro v ⟨hvH, hvK⟩
      exact mem_layerSet_val.2 (show dK ⟨v, hvK⟩ ∈ Icc 0 (dK b) from
        ⟨unitInterval.nonneg', hbmax (show (⟨v, hvK⟩ : K) ∈ _ from hH''H hvH)⟩)
    have hK' : H' ∩ K = H ∩ K := by
      rw [hKseg H' hH'H hH'c hbH' hXH', hKseg H subset_rfl hHc hbH.out (hXH'.trans hH'H)]
    -- `H ∩ Q ⊆ H'`
    have hEH' : E ⊆ H' := fun v hv => by
      have : v ∈ H ∩ K := ⟨hEH hv, hEK hv⟩
      rw [← hK'] at this; exact this.1
    have hQseg : ∀ H'' ⊆ H, Fold.Q78.IsContinuum H'' → (a : M) ∈ H'' → E ⊆ H'' →
        H'' ∩ Q = layerSet e (Icc 0 (e a)) := by
      intro H'' hH''H hH''c haH'' hEH''
      have hc := isContinuum_inter_of_HU hHU hH''c hQc ⟨a, haH'', a.2⟩
      obtain ⟨z, hz⟩ := layer_nonempty hE.2.1.2.1 1
      refine eq_layerSet_of_subcontinuum he hLQ inter_subset_right hc hβ'
        ⟨z, ⟨hEH'' (img_subset _ hz), hEQ (img_subset _ hz)⟩, by rw [heZ]; exact hz⟩
        ⟨a, ⟨haH'', a.2⟩, a, rfl, rfl⟩ ?_
      rintro v ⟨hvH, hvQ⟩
      exact mem_layerSet_val.2 (show e ⟨v, hvQ⟩ ∈ Icc 0 (e a) from
        ⟨unitInterval.nonneg', hamax (show (⟨v, hvQ⟩ : Q) ∈ _ from hH''H hvH)⟩)
    have hQ'' : H' ∩ Q = H ∩ Q := by
      rw [hQseg H' hH'H hH'c haH' hEH', hQseg H subset_rfl hHc haH.out hEH]
    intro v hv
    rcases hHKQ hv with h | h
    · have : v ∈ H ∩ K := ⟨hv, h⟩
      rw [← hK'] at this; exact this.1
    · have : v ∈ H ∩ Q := ⟨hv, h⟩
      rw [← hQ''] at this; exact this.1
  have hirr : IsIrreducibleBetween H a b :=
    ⟨hHc, haH, hbH, fun H' hH'c hH'H haH' hbH' =>
      Subset.antisymm hH'H (hpiece H' hH'H hH'c haH' hbH')⟩
  have hHQc := isContinuum_inter_of_HU hHU hHc hQc ⟨a, haH, a.2⟩
  have hHKc := isContinuum_inter_of_HU hHU hHc hKc ⟨b, hbH, b.2⟩
  refine isTypeA'_of_decomposable hirr (no_indecomposable_interior_aux hX hHU hAT hHQc hHKc
    ⟨⟨haH, a.2⟩, fun h => haK h.2⟩ ⟨⟨hbH, b.2⟩, fun h => hbQ h.2⟩ hirr ?_)
  intro v hv
  rcases hHKQ hv with h | h
  · exact Or.inr ⟨hv, h⟩
  · exact Or.inl ⟨hv, h⟩

/-- **"Every continuum essential to `R(E)` is of type A′."** -/
theorem essential_typeA'_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M} (hH : IsEssential k H) :
    IsTypeA' H := by
  by_cases hX0 : H ⊆ extUnion E (layer k 0)
  · exact essential_typeA'_of_subset hX hi hE hH hX0
  by_cases hX1 : H ⊆ extUnion E (layer k 1)
  · have h := hX1
    rw [← unitInterval.symm_zero, ← layer_symm_comp] at h
    exact essential_typeA'_of_subset hX hi hE.symm_comp hH.symm_comp h
  exact essential_typeA'_two_sided hX hi hE hH.2.1 hH.1 hX0 hX1

end Ess

end HPC.Hagopian
