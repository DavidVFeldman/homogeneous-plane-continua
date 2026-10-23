import HPC.Hagopian.H76Lemma4

/-!
# Lemma 4 of Hagopian 1976: the extension step, given the branching continuum

Hagopian (p. 341): "Since `F` is irreducible between `X` and `d⁻¹(1)`, it is a proper subset of an
element of `𝓕` that is contained in `F ∪ h⁻¹[F]` (Lemma 1)." The step splits into two halves:

1. a continuum `C` (Hagopian's piece of `h⁻¹[F]`) with `∅ ≠ C ∩ F ⊆ d⁻¹(1)` and `C ⊄ F`;
2. given such a `C`, a proper extension `H ⊋ F` away from `X` inside `F ∪ C`.

This file proves the second half (`ext_of_branch`) and derives Lemma 4 and its countable form from
the first half as a hypothesis (`lemma4_of_branch`, `lemma4_seq_of_branch`).

**`ext_of_branch`.** Let `x₀ ∈ X = d⁻¹(0)` and `z ∈ C ∖ F`; `H` is a subcontinuum of `F ∪ C`
irreducible between `x₀` and `z`.
* `F ⊆ H`: `H ∩ F` is a continuum (hereditary unicoherence) through `x₀`; since `H ⊆ F ∪ C` is
  connected, `H ∩ F` meets `C`, hence meets `d⁻¹(1)`; so `H ∩ F = F` (end sets).
* `H` is of type A′: Kuratowski's criterion (`isTypeA'_of_decomposable`) with the 1975 ¶2 argument
  (`no_indecomposable_interior_aux`, with `B = F`, `C = C`).
* Its minimal map `D`, normalized by `D(x₀) = 0`, has `D⁻¹(0) = X`.
  * `X ⊆ D⁻¹(0)`: if `D` took a value `t > 0` on the continuum `X`, then `D⁻¹(0, t) ⊆ X` (interval
    lemma), an open subset of `H` inside `F`, so `X` would have interior in `F`.
  * `D⁻¹(0) ⊆ F`: otherwise `D⁻¹(0) ∩ F` meets `C`, hence `d⁻¹(1)`, so `F ⊆ D⁻¹(0)`; but `H ∖ C` is
    open in `H`, nonempty and inside `F`.
  * `D⁻¹(0) ⊆ X`: otherwise `D⁻¹(0)` contains `d⁻¹[0, t)` for some `t > 0` (interval lemma in `F`),
    which is open in `H` (it is `H ∖ (C ∪ d⁻¹[t, 1])`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Lemma4Ext

section Symm

variable {X : Type*} [MetricSpace X] {E : Set X} {k : E → unitInterval}

/-- Reversing an admissible map gives an admissible map. -/
theorem isAdmissibleMap_symm (hk : IsAdmissibleMap E k) :
    IsAdmissibleMap E (unitInterval.symm ∘ k) := by
  refine ⟨unitInterval.continuous_symm.comp hk.1, fun t => ?_, fun t => ?_⟩
  · obtain ⟨y, hy⟩ := hk.2.1 (unitInterval.symm t)
    exact ⟨y, by simp [hy]⟩
  · have : (unitInterval.symm ∘ k) ⁻¹' {t} = k ⁻¹' {unitInterval.symm t} := by
      ext y; simp only [mem_preimage, Function.comp_apply, mem_singleton_iff]
      constructor
      · intro h; rw [← h, unitInterval.symm_symm]
      · intro h; rw [h, unitInterval.symm_symm]
    rw [this]; exact hk.2.2 _

/-- Reversing a map preserves "layers with empty interior". -/
theorem interior_symm_fibre (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) (t : unitInterval) :
    interior ((unitInterval.symm ∘ k) ⁻¹' {t}) = ∅ := by
  have : (unitInterval.symm ∘ k) ⁻¹' {t} = k ⁻¹' {unitInterval.symm t} := by
    ext y; simp only [mem_preimage, Function.comp_apply, mem_singleton_iff]
    constructor
    · intro h; rw [← h, unitInterval.symm_symm]
    · intro h; rw [h, unitInterval.symm_symm]
  rw [this]; exact hk0 _

end Symm

variable {M : Set Pt}


/-- A connected set covered by two closed sets, meeting both, meets their intersection. -/
theorem meets_inter_of_cover {K P Q : Set M} (hK : IsPreconnected K) (hP : IsClosed P)
    (hQ : IsClosed Q) (hKPQ : K ⊆ P ∪ Q) (hKP : (K ∩ P).Nonempty) (hKQ : (K ∩ Q).Nonempty) :
    (K ∩ (P ∩ Q)).Nonempty :=
  isPreconnected_closed_iff.1 hK P Q hP hQ hKPQ hKP hKQ

/-- **The extension step, given the branching continuum.** If `F` has a minimal admissible map `d`
and `C` is a continuum with `∅ ≠ C ∩ F ⊆ d⁻¹(1)` and `C ⊄ F`, then some continuum `H ⊋ F` has a
minimal admissible map `D` with `D⁻¹(0) = d⁻¹(0)`. -/
theorem ext_of_branch [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {F : Set M} {d : F → unitInterval} (hF : IsMinimalAdmissible F d) {C : Set M}
    (hC : Fold.Q78.IsContinuum C) (hCF : (C ∩ F).Nonempty) (hCT : C ∩ F ⊆ layer d 1)
    (hCnF : ¬ C ⊆ F) :
    ∃ H : Set M, F ⊂ H ∧ ∃ D : H → unitInterval, IsMinimalAdmissible H D ∧
      layer D 0 = layer d 0 := by
  obtain ⟨⟨a, b, hab⟩, hd, hd0⟩ := hF
  have hFc := hab.1
  obtain ⟨x₀, hx₀⟩ := hd.2.1 0
  have hx₀X : (x₀ : M) ∈ layer d 0 := ⟨x₀, hx₀, rfl⟩
  have hCd : ∀ y : F, (y : M) ∈ C → d y = 1 := fun y hy => val_mem_img.1 (hCT ⟨hy, y.2⟩)
  have hx₀C : (x₀ : M) ∉ C := fun h => by
    have := hCd x₀ h; rw [hx₀] at this; exact zero_ne_one this
  obtain ⟨z, hzC, hzF⟩ := not_subset.1 hCnF
  have hN : Fold.Q78.IsContinuum (F ∪ C) :=
    HPC.Plane.isContinuum_union hFc hC (by rw [inter_comm]; exact hCF)
  obtain ⟨H, hHN, hH⟩ := HPC.exists_irreducible hN (Or.inl x₀.2) (Or.inr hzC)
  have hHc := hH.1
  have hx₀H : (x₀ : M) ∈ H := hH.2.1
  have hzH : z ∈ H := hH.2.2.1
  -- `F ⊆ H`
  have hFH : F ⊆ H := by
    have hHF := isContinuum_inter_of_HU hHU hHc hFc ⟨x₀, hx₀H, x₀.2⟩
    obtain ⟨w, hwH, hwF, hwC⟩ := meets_inter_of_cover hHc.2.2 hFc.1.isClosed hC.1.isClosed hHN
      ⟨x₀, hx₀H, x₀.2⟩ ⟨z, hzH, hzC⟩
    have h1 : (H ∩ F ∩ layer d 1).Nonempty := ⟨w, ⟨hwH, hwF⟩, hCT ⟨hwC, hwF⟩⟩
    have h0 : (H ∩ F ∩ layer d 0).Nonempty := ⟨x₀, ⟨hx₀H, x₀.2⟩, hx₀X⟩
    have := eq_of_meets_ends hab hd hd0 inter_subset_right hHF h0 h1
    rw [← this]; exact inter_subset_left
  -- `H` is of type A′
  have hTA : IsTypeA' H := isTypeA'_of_decomposable hH
    (no_indecomposable_interior_aux hX hHU hAT hFc hC ⟨x₀.2, hx₀C⟩ ⟨hzC, hzF⟩ hH hHN)
  obtain ⟨-, D₀, hD₀, hD₀0⟩ := hTA
  obtain ⟨D, hD, hD0, hDx₀⟩ : ∃ D : H → unitInterval, IsAdmissibleMap H D ∧
      (∀ t, interior (D ⁻¹' {t}) = ∅) ∧ D ⟨x₀, hx₀H⟩ = 0 := by
    rcases end_layers hH hD₀ with h | h
    · exact ⟨D₀, hD₀, hD₀0, h.1⟩
    · refine ⟨unitInterval.symm ∘ D₀, isAdmissibleMap_symm hD₀, interior_symm_fibre hD₀0, ?_⟩
      simp only [Function.comp_apply]
      rw [h.1]; exact unitInterval.symm_one
  -- `X ⊆ D⁻¹(0)`
  have hXc : Fold.Q78.IsContinuum (layer d 0) := isContinuum_layer hFc.1 hd 0
  have hXH : layer d 0 ⊆ H := (img_subset _).trans hFH
  have hXD : ∀ y : H, (y : M) ∈ layer d 0 → D y = 0 := by
    intro y hy
    by_contra hne
    have hpos : 0 < D y := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm hne)
    have hsub : ∀ v : H, D v ∈ Ioo 0 (D y) → (v : M) ∈ layer d 0 := by
      intro v hv
      exact layer_subset_of_meets' hH hD hXH hXc ⟨x₀, hx₀X, ⟨x₀, hx₀H⟩, hDx₀, rfl⟩
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
  -- `D⁻¹(0) ⊆ F`
  have hKc : Fold.Q78.IsContinuum (layer D 0) := isContinuum_layer hHc.1 hD 0
  have hx₀K : (x₀ : M) ∈ layer D 0 := ⟨⟨x₀, hx₀H⟩, hDx₀, rfl⟩
  have hKH : layer D 0 ⊆ H := img_subset _
  set W : Set H := Subtype.val ⁻¹' Cᶜ with hWdef
  have hWo : IsOpen W := hC.1.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hx₀W : (⟨x₀, hx₀H⟩ : H) ∈ W := hx₀C
  have hWF : ∀ v ∈ W, (v : M) ∈ F := fun v hv => (hHN v.2).resolve_right hv
  have hKF : layer D 0 ⊆ F := by
    by_contra hnot
    obtain ⟨y, hyK, hyF⟩ := not_subset.1 hnot
    have hyC : y ∈ C := (hHN (hKH hyK)).resolve_left hyF
    obtain ⟨w, hwK, hwF, hwC⟩ := meets_inter_of_cover hKc.2.2 hFc.1.isClosed hC.1.isClosed
      (hKH.trans hHN) ⟨x₀, hx₀K, x₀.2⟩ ⟨y, hyK, hyC⟩
    have hKFc := isContinuum_inter_of_HU hHU hKc hFc ⟨x₀, hx₀K, x₀.2⟩
    have hKFeq := eq_of_meets_ends hab hd hd0 inter_subset_right hKFc ⟨x₀, ⟨hx₀K, x₀.2⟩, hx₀X⟩
      ⟨w, ⟨hwK, hwF⟩, hCT ⟨hwC, hwF⟩⟩
    have hFK : F ⊆ layer D 0 := by rw [← hKFeq]; exact inter_subset_left
    have hWD : W ⊆ D ⁻¹' {0} := by
      intro v hv
      obtain ⟨v', hv', hvv⟩ := hFK (hWF v hv)
      have : v' = v := Subtype.ext hvv
      rw [← this]; exact hv'
    have := interior_maximal hWD hWo hx₀W
    rw [hD0 0] at this; exact this
  -- `D⁻¹(0) ⊆ X`
  have hKX : layer D 0 ⊆ layer d 0 := by
    intro y hyK
    have hyF := hKF hyK
    by_contra hyX
    have ht0 : 0 < d ⟨y, hyF⟩ :=
      lt_of_le_of_ne unitInterval.nonneg' fun h => hyX ⟨⟨y, hyF⟩, h.symm, rfl⟩
    have hsub : ∀ w : F, d w < d ⟨y, hyF⟩ → (w : M) ∈ layer D 0 := by
      intro w hw
      rcases eq_or_lt_of_le (unitInterval.nonneg' : 0 ≤ d w) with h | h
      · have hwX : (w : M) ∈ layer d 0 := ⟨w, h.symm, rfl⟩
        exact ⟨⟨w, hFH w.2⟩, hXD _ hwX, rfl⟩
      · exact layer_subset_of_meets' hab hd hKF hKc ⟨x₀, hx₀K, hx₀X⟩
          ⟨y, hyK, ⟨y, hyF⟩, rfl, rfl⟩ h hw ⟨w, rfl, rfl⟩
    set R := Subtype.val '' (d ⁻¹' Ici (d ⟨y, hyF⟩)) with hRdef
    have hRc : IsClosed R := (isCompact_img hFc.1 hd.1 isClosed_Ici).isClosed
    set W' : Set H := Subtype.val ⁻¹' (Cᶜ ∩ Rᶜ) with hW'def
    have hW'o : IsOpen W' :=
      (hC.1.isClosed.isOpen_compl.inter hRc.isOpen_compl).preimage continuous_subtype_val
    have hx₀W' : (⟨x₀, hx₀H⟩ : H) ∈ W' := by
      refine ⟨hx₀C, fun h => ?_⟩
      have h' : d x₀ ∈ Ici (d ⟨y, hyF⟩) := val_mem_img.1 h
      rw [hx₀] at h'
      exact absurd (lt_of_lt_of_le ht0 h') (lt_irrefl _)
    have hW'D : W' ⊆ D ⁻¹' {0} := by
      intro v hv
      have hvF : (v : M) ∈ F := (hHN v.2).resolve_right hv.1
      have hlt : d ⟨v, hvF⟩ < d ⟨y, hyF⟩ :=
        lt_of_not_ge fun h => hv.2 ⟨⟨v, hvF⟩, h, rfl⟩
      obtain ⟨v', hv', hvv⟩ := hsub _ hlt
      have : v' = v := Subtype.ext hvv
      rw [← this]; exact hv'
    have := interior_maximal hW'D hW'o hx₀W'
    rw [hD0 0] at this; exact this
  refine ⟨H, ⟨hFH, fun h => hzF (h hzH)⟩, D, ⟨⟨x₀, z, hH⟩, hD, hD0⟩,
    Subset.antisymm hKX fun y hy => ?_⟩
  have hyH := hXH hy
  exact ⟨⟨y, hyH⟩, hXD ⟨y, hyH⟩ hy, rfl⟩

/-- **Lemma 4, from the branching continuum.** If every extension `F` of `E` away from `X` (with its
map `d`) admits a continuum `C` with `∅ ≠ C ∩ F ⊆ d⁻¹(1)` and `C ⊄ F`, then `𝓕` is a chain without a
maximal element. -/
theorem lemma4_of_branch [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hbranch : ∀ (F : Set M) (d : F → unitInterval), E ⊆ F → IsMinimalAdmissible F d →
      layer d 0 = layer k 0 → ∃ C : Set M, Fold.Q78.IsContinuum C ∧ (C ∩ F).Nonempty ∧
        C ∩ F ⊆ layer d 1 ∧ ¬ C ⊆ F) :
    IsChain (· ⊆ ·) {F | IsExtensionAway E (layer k 0) F} ∧
      ∀ F ∈ {F | IsExtensionAway E (layer k 0) F},
        ∃ H ∈ {F | IsExtensionAway E (layer k 0) F}, F ⊂ H := by
  refine ⟨fun _ hF _ hH _ => ext_chain hHU hAT hE hF hH, ?_⟩
  rintro F ⟨hEF, d, hd, hdX⟩
  obtain ⟨C, hC, hCF, hCT, hCnF⟩ := hbranch F d hEF hd hdX
  obtain ⟨H, hFH, D, hD, hDX⟩ := ext_of_branch hX hHU hAT hd hC hCF hCT hCnF
  exact ⟨H, ⟨hEF.trans hFH.1, D, hD, hDX.trans hdX⟩, hFH⟩

/-- **Lemma 4, the countable form, from the branching continuum** (via `lemma4_of_branch` and
`exists_strictMono_seq_of_chain`). -/
theorem lemma4_seq_of_branch [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hbranch : ∀ (F : Set M) (d : F → unitInterval), E ⊆ F → IsMinimalAdmissible F d →
      layer d 0 = layer k 0 → ∃ C : Set M, Fold.Q78.IsContinuum C ∧ (C ∩ F).Nonempty ∧
        C ∩ F ⊆ layer d 1 ∧ ¬ C ⊆ F) :
    ∃ Fs : ℕ → Set M, StrictMono Fs ∧ (∀ i, IsExtensionAway E (layer k 0) (Fs i)) ∧
      extUnion E (layer k 0) = ⋃ i, Fs i :=
  have h4 := lemma4_of_branch hX hHU hAT hE hbranch
  exists_strictMono_seq_of_chain h4.1
    (fun _ ⟨_, _, ⟨⟨_, _, hab⟩, _, _⟩, _⟩ => hab.1.1.isClosed) ⟨E, subset_rfl, k, hE, rfl⟩ h4.2

end Lemma4Ext

end HPC.Hagopian
