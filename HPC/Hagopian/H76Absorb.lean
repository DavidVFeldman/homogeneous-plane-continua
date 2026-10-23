import HPC.Hagopian.H76NoMax

/-!
# Batch 160, item A: absorption

`absorb_point`: in a compact, homogeneous, hereditarily unicoherent, atriodic space, let `F` have a
minimal admissible map `d` with end set `X = d⁻¹(0)`, and let `G` be a continuum that misses `X` and
meets `F`. Then every point `g` of `G` lies in a continuum `H ⊇ F` with a minimal admissible map whose
end set at `0` is `X`. Proof: an irreducible continuum `H` from a point of `X` to `g` inside `F ∪ G`
contains `F` (three continua through a point of `H ∩ F ∩ G`: `H ∩ F`, the tail of `F` beyond it,
and `H ∩ G`; atriodicity), so `H = F ∪ (H ∩ G)`, and the extension step applies
(`ext_of_irreducible_union_eq`).

`subset_extUnion_of_meets`: hence a continuum missing `X` that meets an extension of `E` away from
`X` lies in `R(X, E)`. This is Hagopian's "Since `M` is atriodic, it follows that `f[L]` is a subset
of `R(X, E)`" (p. 342, step 5 of Lemma 6), in a form that does not depend on `f`.

`ext_of_irreducible_union_eq` is `ext_of_irreducible_union` (`H76NoMaxBasic.lean`, batch 156) with
its conclusion stated for the continuum `F ∪ C` itself rather than for some `H ⊋ F`; the proof is
the same (copied, since existing files are not edited in this batch).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Absorb

variable {M : Set Pt}

/-- **The extension step from an irreducible union**, for the union itself. -/
theorem ext_of_irreducible_union_eq [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {F : Set M} {d : F → unitInterval} (hF : IsMinimalAdmissible F d) {C : Set M}
    (hC : Fold.Q78.IsContinuum C) (hCX : Disjoint C (layer d 0)) {x₀ z : M}
    (hx₀ : x₀ ∈ layer d 0) (hzC : z ∈ C) (hzF : z ∉ F)
    (hirr : IsIrreducibleBetween (F ∪ C) x₀ z) :
    ∃ D : (F ∪ C : Set M) → unitInterval, IsMinimalAdmissible (F ∪ C) D ∧
      layer D 0 = layer d 0 := by
  obtain ⟨⟨a, b, hab⟩, hd, hd0⟩ := hF
  have hFc := hab.1
  obtain ⟨x0, hx0, rfl⟩ := hx₀
  have hx0X : (x0 : M) ∈ layer d 0 := ⟨x0, hx0, rfl⟩
  have hx0C : (x0 : M) ∉ C := fun h => disjoint_left.1 hCX h hx0X
  have hFH : F ⊆ F ∪ C := subset_union_left
  have hHc := hirr.1
  have hx0H : (x0 : M) ∈ F ∪ C := hirr.2.1
  -- type A′
  have hTA : IsTypeA' (F ∪ C) := isTypeA'_of_decomposable hirr
    (no_indecomposable_interior_aux hX hHU hAT hFc hC ⟨x0.2, hx0C⟩ ⟨hzC, hzF⟩ hirr subset_rfl)
  obtain ⟨-, D₀, hD₀, hD₀0⟩ := hTA
  obtain ⟨D, hD, hD0, hDx₀⟩ : ∃ D : (F ∪ C : Set M) → unitInterval,
      IsAdmissibleMap (F ∪ C) D ∧ (∀ t, interior (D ⁻¹' {t}) = ∅) ∧ D ⟨x0, hx0H⟩ = 0 := by
    rcases end_layers hirr hD₀ with h | h
    · exact ⟨D₀, hD₀, hD₀0, h.1⟩
    · refine ⟨unitInterval.symm ∘ D₀, isAdmissibleMap_symm hD₀, interior_symm_fibre hD₀0, ?_⟩
      simp only [Function.comp_apply]
      rw [h.1]; exact unitInterval.symm_one
  -- `X ⊆ D⁻¹(0)`
  have hXc : Fold.Q78.IsContinuum (layer d 0) := isContinuum_layer hFc.1 hd 0
  have hXH : layer d 0 ⊆ F ∪ C := (img_subset _).trans hFH
  have hXD : ∀ y : (F ∪ C : Set M), (y : M) ∈ layer d 0 → D y = 0 := by
    intro y hy
    by_contra hne
    have hpos : 0 < D y := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm hne)
    have hsub : ∀ v : (F ∪ C : Set M), D v ∈ Ioo 0 (D y) → (v : M) ∈ layer d 0 := by
      intro v hv
      exact layer_subset_of_meets' hirr hD hXH hXc ⟨x0, hx0X, ⟨x0, hx0H⟩, hDx₀, rfl⟩
        ⟨y, hy, y, rfl, rfl⟩ hv.1 hv.2 ⟨v, rfl, rfl⟩
    set V : Set F := (D ∘ inclusion hFH) ⁻¹' Ioo 0 (D y) with hVdef
    have hVo : IsOpen V := isOpen_Ioo.preimage (hD.1.comp (continuous_inclusion hFH))
    have hVX : V ⊆ d ⁻¹' {0} := fun w hw => val_mem_img.1 (hsub (inclusion hFH w) hw)
    obtain ⟨m, hm0, hm1⟩ := exists_between hpos
    obtain ⟨v, hv⟩ := hD.2.1 m
    have hvX := hsub v (by rw [hv]; exact ⟨hm0, hm1⟩)
    have hvF : (v : M) ∈ F := img_subset _ hvX
    have hmem : (⟨v, hvF⟩ : F) ∈ V := by
      show D (inclusion hFH ⟨v, hvF⟩) ∈ Ioo 0 (D y)
      have : inclusion hFH ⟨(v : M), hvF⟩ = v := rfl
      rw [this, hv]; exact ⟨hm0, hm1⟩
    have := interior_maximal hVX hVo hmem
    rw [hd0 0] at this; exact this
  -- `m`: the least value of `d` on `F ∩ C`
  obtain ⟨w₀, hw₀H, hw₀F, hw₀C⟩ := meets_inter_of_cover hHc.2.2 hFc.1.isClosed hC.1.isClosed
    subset_rfl ⟨x0, hx0H, x0.2⟩ ⟨z, hirr.2.2.1, hzC⟩
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc.1
  set SC : Set F := Subtype.val ⁻¹' C
  have hSCc : IsCompact SC := (hC.1.isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨wm, hwmC, hwmmin⟩ := hSCc.exists_isMinOn ⟨⟨w₀, hw₀F⟩, hw₀C⟩ hd.1.continuousOn
  have hpos_of_C : ∀ w : F, (w : M) ∈ C → 0 < d w := fun w hw =>
    lt_of_le_of_ne unitInterval.nonneg' fun h0 =>
      disjoint_left.1 hCX hw ⟨w, h0.symm, rfl⟩
  have hm : 0 < d wm := hpos_of_C wm hwmC
  -- an open subset of `F ∪ C` inside `d⁻¹[0, r)`
  have hO : ∀ r : unitInterval, 0 < r → r ≤ d wm →
      layerSet d (Ico 0 r) ⊆ layer D 0 → False := by
    intro r hr0 hrm hsub
    set R := Subtype.val '' (d ⁻¹' Ici r) with hRdef
    have hRc : IsClosed R := (isCompact_img hFc.1 hd.1 isClosed_Ici).isClosed
    set O : Set (F ∪ C : Set M) := Subtype.val ⁻¹' (Cᶜ ∩ Rᶜ) with hOdef
    have hOo : IsOpen O :=
      (hC.1.isClosed.isOpen_compl.inter hRc.isOpen_compl).preimage continuous_subtype_val
    have hx0O : (⟨x0, hx0H⟩ : (F ∪ C : Set M)) ∈ O := by
      refine ⟨hx0C, fun h => ?_⟩
      have h' : d x0 ∈ Ici r := val_mem_img.1 h
      have h0 : d x0 = 0 := hx0
      rw [h0] at h'
      exact absurd (lt_of_lt_of_le hr0 h') (lt_irrefl _)
    have hOD : O ⊆ D ⁻¹' {0} := by
      intro v hv
      have hvF : (v : M) ∈ F := (v.2).resolve_right hv.1
      have hlt : d ⟨v, hvF⟩ < r := lt_of_not_ge fun h => hv.2 ⟨⟨v, hvF⟩, h, rfl⟩
      obtain ⟨v', hv', hvv⟩ := hsub ⟨⟨v, hvF⟩, ⟨unitInterval.nonneg', hlt⟩, rfl⟩
      have : v' = v := Subtype.ext hvv
      rw [← this]; exact hv'
    have := interior_maximal hOD hOo hx0O
    rw [hD0 0] at this; exact this
  -- `D⁻¹(0) ⊆ X`
  have hKc : Fold.Q78.IsContinuum (layer D 0) := isContinuum_layer hHc.1 hD 0
  have hx0K : (x0 : M) ∈ layer D 0 := ⟨⟨x0, hx0H⟩, hDx₀, rfl⟩
  have hKH : layer D 0 ⊆ F ∪ C := img_subset _
  have hKX : layer D 0 ⊆ layer d 0 := by
    intro y hyK
    by_contra hyX
    obtain ⟨w, hwK, hw0⟩ : ∃ w : F, (w : M) ∈ layer D 0 ∧ 0 < d w := by
      by_cases hyF : y ∈ F
      · refine ⟨⟨y, hyF⟩, hyK, lt_of_le_of_ne unitInterval.nonneg' fun h => hyX ?_⟩
        exact ⟨⟨y, hyF⟩, h.symm, rfl⟩
      · have hyC : y ∈ C := (hKH hyK).resolve_left hyF
        obtain ⟨w', hw'K, hw'F, hw'C⟩ := meets_inter_of_cover hKc.2.2 hFc.1.isClosed
          hC.1.isClosed hKH ⟨x0, hx0K, x0.2⟩ ⟨y, hyK, hyC⟩
        exact ⟨⟨w', hw'F⟩, hw'K, hpos_of_C ⟨w', hw'F⟩ hw'C⟩
    have hKFc := isContinuum_inter_of_HU hHU hKc hFc ⟨x0, hx0K, x0.2⟩
    refine hO (min (d w) (d wm)) (lt_min hw0 hm) (min_le_right _ _) ?_
    rintro _ ⟨v, hv, rfl⟩
    rcases eq_or_lt_of_le hv.1 with h | h
    · exact ⟨⟨v, hFH v.2⟩, hXD _ ⟨v, h.symm, rfl⟩, rfl⟩
    · exact (layer_subset_of_meets' hab hd inter_subset_right hKFc
        ⟨x0, ⟨hx0K, x0.2⟩, hx0X⟩ ⟨w, ⟨hwK, w.2⟩, w, rfl, rfl⟩ h
        (lt_of_lt_of_le hv.2 (min_le_left _ _)) ⟨v, rfl, rfl⟩).1
  refine ⟨D, ⟨⟨x0, z, hirr⟩, hD, hD0⟩, Subset.antisymm hKX fun y hy => ?_⟩
  have hyH := hXH hy
  exact ⟨⟨y, hyH⟩, hXD ⟨y, hyH⟩ hy, rfl⟩


/-- **Absorption.** A continuum `G` missing the end set `d⁻¹(0)` of `F` and meeting `F`: each of its
points lies in an extension of `F` away from `d⁻¹(0)`. -/
theorem absorb_point [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {F : Set M} {d : F → unitInterval} (hF : IsMinimalAdmissible F d) {G : Set M}
    (hG : Fold.Q78.IsContinuum G) (hGX : Disjoint G (layer d 0)) (hGF : (G ∩ F).Nonempty)
    {g : M} (hg : g ∈ G) :
    ∃ H : Set M, F ⊆ H ∧ g ∈ H ∧ ∃ D : H → unitInterval, IsMinimalAdmissible H D ∧
      layer D 0 = layer d 0 := by
  by_cases hgF : g ∈ F
  · exact ⟨F, subset_rfl, hgF, d, hF, rfl⟩
  have hF' := hF
  obtain ⟨⟨a, b, hab⟩, hd, hd0⟩ := hF
  have hFc := hab.1
  obtain ⟨x0, hx0⟩ := hd.2.1 0
  have hx0X : (x0 : M) ∈ layer d 0 := ⟨x0, hx0, rfl⟩
  have hx0G : (x0 : M) ∉ G := fun h => disjoint_left.1 hGX h hx0X
  have hW : Fold.Q78.IsContinuum (F ∪ G) := by
    obtain ⟨y, hyG, hyF⟩ := hGF
    exact isContinuum_union hFc hG ⟨y, hyF, hyG⟩
  obtain ⟨H, hHW, hH⟩ := exists_irreducible hW (Or.inl x0.2 : (x0 : M) ∈ F ∪ G) (Or.inr hg)
  have hHF := isContinuum_inter_of_HU hHU hH.1 hFc ⟨x0, hH.2.1, x0.2⟩
  have hHG := isContinuum_inter_of_HU hHU hH.1 hG ⟨g, hH.2.2.1, hg⟩
  have key : (H ∩ F ∩ layer d 1).Nonempty → F ⊆ H := fun h1 => by
    have := end_sets_aux hF' inter_subset_right hHF ⟨x0, ⟨hH.2.1, x0.2⟩, hx0X⟩ h1
    rw [← this]; exact inter_subset_left
  obtain ⟨y, hyH, hyF, hyG⟩ := meets_inter_of_cover hH.1.2.2 hFc.1.isClosed hG.1.isClosed hHW
    ⟨x0, hH.2.1, x0.2⟩ ⟨g, hH.2.2.1, hg⟩
  set y' : F := ⟨y, hyF⟩
  have hy0 : 0 < d y' := lt_of_le_of_ne unitInterval.nonneg' fun h =>
    hx0G (by exact absurd ⟨y', h.symm, rfl⟩ (fun h' => disjoint_left.1 hGX hyG h'))
  have hFH : F ⊆ H := by
    rcases eq_or_lt_of_le (unitInterval.le_one' : d y' ≤ 1) with h1 | h1
    · exact key ⟨y, ⟨hyH, hyF⟩, y', h1, rfl⟩
    have hN₂ : Fold.Q78.IsContinuum (layerSet d (Icc (d y') 1)) :=
      isContinuum_img hFc.1 hd isClosed_Icc isPreconnected_Icc ⟨d y', le_rfl, unitInterval.le_one'⟩
    have hyN₂ : y ∈ layerSet d (Icc (d y') 1) := ⟨y', ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩
    rcases three_continua hHU hAT hHF hN₂ hHG ⟨hyH, hyF⟩ hyN₂ ⟨hyH, hyG⟩ with h | h | h
    · exfalso
      rcases h ⟨hH.2.1, x0.2⟩ with ⟨v, hv, hveq⟩ | ⟨-, h'⟩
      · have : v = x0 := Subtype.ext hveq
        subst this
        have h0 : d v = 0 := hx0
        have := hv.1
        rw [h0] at this
        exact absurd (lt_of_lt_of_le hy0 this) (lt_irrefl _)
      · exact hx0G h'
    · obtain ⟨t, ht⟩ := hd.2.1 1
      have htN : (t : M) ∈ layerSet d (Icc (d y') 1) :=
        ⟨t, show d t ∈ Icc (d y') 1 by rw [ht]; exact ⟨unitInterval.le_one', le_rfl⟩, rfl⟩
      have htH : (t : M) ∈ H := by
        rcases h htN with h' | h'
        · exact h'.1
        · exact h'.1
      exact key ⟨t, ⟨htH, t.2⟩, t, ht, rfl⟩
    · exfalso
      rcases h ⟨hH.2.2.1, hg⟩ with h' | h'
      · exact hgF h'.2
      · exact hgF (img_subset _ h')
  have hHeq : F ∪ (H ∩ G) = H := by
    apply Subset.antisymm (union_subset hFH inter_subset_left)
    intro v hv
    rcases hHW hv with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨hv, h'⟩
  have hirr : IsIrreducibleBetween (F ∪ (H ∩ G)) x0 g := by rw [hHeq]; exact hH
  obtain ⟨D, hD, hDX⟩ := ext_of_irreducible_union_eq hX hHU hAT hF' hHG
    (hGX.mono_left inter_subset_right) hx0X ⟨hH.2.2.1, hg⟩ hgF hirr
  exact ⟨F ∪ (H ∩ G), subset_union_left, Or.inr ⟨hH.2.2.1, hg⟩, D, hD, hDX⟩

/-- **A continuum missing `X` that meets an extension away from `X` lies in `R(X, E)`.** -/
theorem subset_extUnion_of_meets [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {E : Set M} {k : E → unitInterval} {F : Set M} (hF : IsExtensionAway E (layer k 0) F)
    {G : Set M} (hG : Fold.Q78.IsContinuum G) (hGX : Disjoint G (layer k 0))
    (hGF : (G ∩ F).Nonempty) : G ⊆ extUnion E (layer k 0) := by
  obtain ⟨hEF, d, hd, hdX⟩ := hF
  intro g hg
  obtain ⟨H, hFH, hgH, D, hD, hDX⟩ := absorb_point hX hHU hAT hd hG (hdX ▸ hGX) hGF hg
  exact ⟨H, ⟨hEF.trans hFH, D, hD, hDX.trans hdX⟩, hgH⟩

end Absorb

end HPC.Hagopian
