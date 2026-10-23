import HPC.Hagopian.Hagopian76N

/-!
# Batch 170, item A: `ExtChainInter` (commission 170 §1.A)

Every member of a family of extensions of `E` away from `k⁻¹(0)` lying inside one extension `H`
(map `d`) is an initial segment `d⁻¹[[0, sᵢ]]` of `H` (`hagopian76_initial_segment`, Lemma 4 strong
form). The intersection is `d⁻¹[[0, s*]]`, `s* = inf sᵢ`; `s* > 0` since `E ⊆ ⋂` and `E` is not
contained in its end set `k⁻¹(0)`; `piece_map` makes it an extension away from `layer d 0 = k⁻¹(0)`.
For a chain, the intersection equals the intersection of the members inside any one member, so
`ExtChainInter E (k⁻¹(0)) O p q` holds outright (`extChainInter_aux`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section ChainInter

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
theorem mem_layerSet_Icc_zero {H : Set M} {d : H → unitInterval} {s : unitInterval} {x : M} :
    x ∈ layerSet d (Icc 0 s) ↔ ∃ hx : x ∈ H, d ⟨x, hx⟩ ≤ s := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy.2⟩
  · rintro ⟨hx, hle⟩
    exact ⟨⟨x, hx⟩, ⟨unitInterval.nonneg', hle⟩, rfl⟩

/-- **A, inside one extension.** The intersection of a nonempty family of extensions of `E` away
from `k⁻¹(0)`, all contained in one extension `H` away from `k⁻¹(0)`, is an extension of `E` away
from `k⁻¹(0)`. (No chain condition is needed.) -/
theorem extChainInter_in_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsExtensionAway E (layer k 0) H) {c : Set (Set M)} (hne : c.Nonempty)
    (hc : ∀ F ∈ c, F ⊆ H ∧ IsExtensionAway E (layer k 0) F) :
    IsExtensionAway E (layer k 0) (⋂₀ c) := by
  obtain ⟨-, d, hd, hd0⟩ := hH
  have hseg : ∀ F ∈ c, ∃ s : unitInterval, layerSet d (Icc 0 s) = F := by
    intro F hF
    obtain ⟨hFH, -, dF, hdF, hdF0⟩ := hc F hF
    obtain ⟨s, -, hs, -⟩ := hagopian76_initial_segment hX hi hdF hd hFH (hd0.trans hdF0.symm)
    exact ⟨s, hs⟩
  set T : Set ℝ := {t | ∃ s : unitInterval, (s : ℝ) = t ∧ layerSet d (Icc 0 s) ∈ c} with hTdef
  have hTne : T.Nonempty := by
    obtain ⟨F, hF⟩ := hne
    obtain ⟨s, hs⟩ := hseg F hF
    exact ⟨s, s, rfl, hs ▸ hF⟩
  have hTbdd : BddBelow T := ⟨0, by rintro _ ⟨s, rfl, -⟩; exact unitInterval.nonneg'⟩
  have hσ0 : 0 ≤ sInf T := le_csInf hTne (by rintro _ ⟨s, rfl, -⟩; exact unitInterval.nonneg')
  have hσ1 : sInf T ≤ 1 := by
    obtain ⟨t, ht⟩ := hTne
    refine (csInf_le hTbdd ht).trans ?_
    obtain ⟨s, hst, -⟩ := ht
    rw [← hst]
    exact unitInterval.le_one'
  set s' : unitInterval := ⟨sInf T, hσ0, hσ1⟩ with hs'def
  have hint : ⋂₀ c = layerSet d (Icc 0 s') := by
    ext x
    rw [mem_sInter, mem_layerSet_Icc_zero]
    constructor
    · intro hx
      obtain ⟨F, hF⟩ := hne
      have hxH : x ∈ H := (hc F hF).1 (hx F hF)
      refine ⟨hxH, ?_⟩
      show ((d ⟨x, hxH⟩ : unitInterval) : ℝ) ≤ sInf T
      refine le_csInf hTne ?_
      rintro _ ⟨s, rfl, hs⟩
      obtain ⟨_, hle⟩ := mem_layerSet_Icc_zero.1 (hx _ hs)
      exact hle
    · rintro ⟨hxH, hle⟩ F hF
      obtain ⟨s, hs⟩ := hseg F hF
      rw [← hs]
      refine mem_layerSet_Icc_zero.2 ⟨hxH, ?_⟩
      show ((d ⟨x, hxH⟩ : unitInterval) : ℝ) ≤ s
      exact (show ((d ⟨x, hxH⟩ : unitInterval) : ℝ) ≤ sInf T from hle).trans
        (csInf_le hTbdd ⟨s, rfl, hs ▸ hF⟩)
  have hEsub : E ⊆ ⋂₀ c := fun x hx F hF => (hc F hF).2.1 hx
  have hpos : (0 : unitInterval) < s' := by
    rcases (unitInterval.nonneg' (t := s')).lt_or_eq with h | h
    · exact h
    exfalso
    obtain ⟨e, he⟩ := hE.2.1.2.1 1
    have heE : (e : M) ∈ ⋂₀ c := hEsub e.2
    rw [hint, mem_layerSet_Icc_zero] at heE
    obtain ⟨heH, hle⟩ := heE
    have hd0' : d ⟨e, heH⟩ = 0 := le_antisymm (h ▸ hle) unitInterval.nonneg'
    have hmem : (e : M) ∈ layer d 0 := ⟨⟨e, heH⟩, hd0', rfl⟩
    rw [hd0] at hmem
    obtain ⟨y, hy, hye⟩ := hmem
    have : y = e := Subtype.ext hye
    rw [this, mem_preimage, mem_singleton_iff, he] at hy
    exact one_ne_zero hy
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hd.isCompact
  obtain ⟨p, hp, hp0, -⟩ := piece_map hd (lsc_of_minimalAdmissible hX hi hd) hpos hint
  exact ⟨hEsub, p, hp, hp0.trans hd0⟩

/-- **A. `ExtChainInter` holds** with the end set `k⁻¹(0)`: the intersection of a nonempty chain
of extensions of `E` away from `k⁻¹(0)` is again one. (The separation hypothesis of
`ExtChainInter` is not used.) -/
theorem extChainInter_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) (O : Set Pt) (p q : Pt) :
    ExtChainInter E (layer k 0) O p q := by
  intro c hne hch hc
  obtain ⟨F₀, hF₀⟩ := hne
  set c' : Set (Set M) := {F | F ∈ c ∧ F ⊆ F₀} with hc'def
  have heq : ⋂₀ c = ⋂₀ c' := by
    refine Subset.antisymm (sInter_subset_sInter fun F hF => hF.1) fun x hx F hF => ?_
    rcases hch.total hF hF₀ with h | h
    · exact hx F ⟨hF, h⟩
    · exact h (hx F₀ ⟨hF₀, subset_rfl⟩)
  rw [heq]
  exact extChainInter_in_aux hX hi hE (hc F₀ hF₀).1 ⟨F₀, hF₀, subset_rfl⟩
    fun F hF => ⟨hF.2, (hc F hF.1).1⟩

end ChainInter

end HPC.Hagopian
