import HPC.Hagopian.H76Lemma4Ext

/-!
# Lemma 4 of Hagopian 1976, "no maximal element": general tools

Tools for the proof of "no maximal element" (`H76NoMax.lean`), for a continuum `F` with a minimal
admissible map `d` (layers `F_S = d⁻¹(S)`, written `layerSet d S`):
* `layer_one_subset_closure`: the end layer `d⁻¹(1)` lies in the closure of `d⁻¹(s, 1)`;
* `tail_subset`: a continuum through a point of `d⁻¹(1)` and a point `y` of `F` with `d(y) < 1`
  contains the tail `d⁻¹(d(y), 1]` (hereditary unicoherence and the interval lemma);
* `false_of_layer_open`: a layer of a second continuum `B` (map `b`) cannot contain a tail
  `d⁻¹(s, 1)` of `F` while `F` contains a neighbourhood `b⁻¹(β₁, β₂)` of that layer;
* `three_continua`: in an atriodic, hereditarily unicoherent space, of three continua with a common
  point one lies in the union of the other two;
* `exists_image_map`: a homeomorphism carries a minimal admissible map to one on the image;
* `ext_of_irreducible_union`: the extension step from a continuum `C` missing `d⁻¹(0)` such that
  `F ∪ C` is irreducible from `d⁻¹(0)` to a point of `C ∖ F`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section NoMaxBasic

variable {M : Set Pt}

/-- The end layer `d⁻¹(1)` lies in the closure of `d⁻¹(s, 1)`, for `s < 1`. -/
theorem layer_one_subset_closure {F : Set M} {d : F → unitInterval} (hd : Continuous d)
    (hd0 : ∀ t, interior (d ⁻¹' {t}) = ∅) {s : unitInterval} (hs : s < 1) :
    layer d 1 ⊆ closure (layerSet d (Ioo s 1)) := by
  rintro _ ⟨w, hw, rfl⟩
  have hw1 : d w = 1 := hw
  have hcl : w ∈ closure (d ⁻¹' Ioo s 1) := by
    rw [_root_.mem_closure_iff]
    intro o ho hwo
    have ho' : IsOpen (o ∩ d ⁻¹' Ioi s) := ho.inter (isOpen_Ioi.preimage hd)
    have hwo' : w ∈ o ∩ d ⁻¹' Ioi s := ⟨hwo, by rw [mem_preimage, hw1]; exact hs⟩
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hsub : o ∩ d ⁻¹' Ioi s ⊆ d ⁻¹' {1} := by
      intro v ⟨hvo, hvs⟩
      by_contra hv1
      have hlt : d v < 1 := lt_of_le_of_ne unitInterval.le_one' hv1
      have : v ∈ o ∩ d ⁻¹' Ioo s 1 := ⟨hvo, hvs, hlt⟩
      rw [hne] at this; exact this
    have := interior_maximal hsub ho' hwo'
    rw [hd0 1] at this; exact this
  exact image_closure_subset_closure_image continuous_subtype_val ⟨w, hcl, rfl⟩

/-- **Tails.** A continuum `K` through a point of `d⁻¹(1)` and through a point `y` of `F` with
`d(y) < 1` contains `d⁻¹(d(y), 1]`. -/
theorem tail_subset (hHU : IsHereditarilyUnicoherent (univ : Set M)) {F : Set M}
    {d : F → unitInterval} (hF : IsMinimalAdmissible F d) {K : Set M}
    (hK : Fold.Q78.IsContinuum K) {p : M} (hpK : p ∈ K) (hp : p ∈ layer d 1) (y : F)
    (hyK : (y : M) ∈ K) (hy1 : d y < 1) : layerSet d (Ioc (d y) 1) ⊆ K := by
  obtain ⟨⟨a, b, hab⟩, hd, hd0⟩ := hF
  have hKF := isContinuum_inter_of_HU hHU hK hab.1 ⟨y, hyK, y.2⟩
  have hmid : layerSet d (Ioo (d y) 1) ⊆ K := by
    rintro _ ⟨v, hv, rfl⟩
    exact (layer_subset_of_meets' hab hd inter_subset_right hKF
      ⟨y, ⟨hyK, y.2⟩, y, rfl, rfl⟩ ⟨p, ⟨hpK, img_subset _ hp⟩, hp⟩ hv.1 hv.2
      ⟨v, rfl, rfl⟩).1
  rintro _ ⟨v, hv, rfl⟩
  rcases eq_or_lt_of_le hv.2 with h | h
  · exact closure_minimal hmid hK.1.isClosed
      (layer_one_subset_closure hd.1 hd0 hy1 ⟨v, h, rfl⟩)
  · exact hmid ⟨v, ⟨hv.1, h⟩, rfl⟩

/-- **A layer cannot swallow an open tail.** If `F ⊇ b⁻¹(β₁, β₂)` with `β₁ < u < β₂` and the layer
`b⁻¹(u)` contains `d⁻¹(s, 1)` (`s < 1`), then `b⁻¹(u)` has interior in `B`: impossible. -/
theorem false_of_layer_open {F B : Set M} {d : F → unitInterval} {b : B → unitInterval}
    (hd : IsAdmissibleMap F d) (hb : Continuous b) (hb0 : ∀ t, interior (b ⁻¹' {t}) = ∅)
    {s u β₁ β₂ : unitInterval} (hs : s < 1) (h₁ : β₁ < u) (h₂ : u < β₂)
    (hBF : layerSet b (Ioo β₁ β₂) ⊆ F) (hFB : layerSet d (Ioo s 1) ⊆ layer b u) : False := by
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1 (isOpen_Ioo.preimage hd.1 :
    IsOpen (d ⁻¹' Ioo s 1))
  set S : Set B := Subtype.val ⁻¹' V ∩ b ⁻¹' Ioo β₁ β₂ with hSdef
  have hSo : IsOpen S := (hV.preimage continuous_subtype_val).inter (isOpen_Ioo.preimage hb)
  have hSu : S ⊆ b ⁻¹' {u} := by
    intro v ⟨hvV, hvb⟩
    have hvF : (v : M) ∈ F := hBF ⟨v, hvb, rfl⟩
    have hmem : (⟨v, hvF⟩ : F) ∈ d ⁻¹' Ioo s 1 := by rw [← hVeq]; exact hvV
    obtain ⟨v', hv', hvv⟩ := hFB ⟨⟨v, hvF⟩, hmem, rfl⟩
    have : v' = v := Subtype.ext hvv
    rw [← this]; exact hv'
  obtain ⟨m, hm0, hm1⟩ := exists_between hs
  obtain ⟨w, hw⟩ := hd.2.1 m
  have hwmem : w ∈ d ⁻¹' Ioo s 1 := by rw [mem_preimage, hw]; exact ⟨hm0, hm1⟩
  obtain ⟨v, hv, hvw⟩ := hFB ⟨w, hwmem, rfl⟩
  have hvS : v ∈ S := by
    refine ⟨?_, ?_⟩
    · show (v : M) ∈ V
      have : w ∈ Subtype.val ⁻¹' V := by rw [hVeq]; exact hwmem
      rw [hvw]; exact this
    · have hbv : b v = u := hv
      show b v ∈ Ioo β₁ β₂
      rw [hbv]; exact ⟨h₁, h₂⟩
  have := interior_maximal hSu hSo hvS
  rw [hb0 u] at this; exact this

/-- **Three continua.** In an atriodic, hereditarily unicoherent space, of three continua with a
common point one lies in the union of the other two. -/
theorem three_continua (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {K₁ K₂ K₃ : Set M} (h₁ : Fold.Q78.IsContinuum K₁)
    (h₂ : Fold.Q78.IsContinuum K₂) (h₃ : Fold.Q78.IsContinuum K₃) {c : M} (hc₁ : c ∈ K₁)
    (hc₂ : c ∈ K₂) (hc₃ : c ∈ K₃) :
    K₁ ⊆ K₂ ∪ K₃ ∨ K₂ ⊆ K₁ ∪ K₃ ∨ K₃ ⊆ K₁ ∪ K₂ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨n₁, n₂, n₃⟩ := hcon
  have c₁₂ := isContinuum_inter_of_HU hHU h₁ h₂ ⟨c, hc₁, hc₂⟩
  have c₁₃ := isContinuum_inter_of_HU hHU h₁ h₃ ⟨c, hc₁, hc₃⟩
  have c₂₃ := isContinuum_inter_of_HU hHU h₂ h₃ ⟨c, hc₂, hc₃⟩
  have hN : Fold.Q78.IsContinuum (K₁ ∩ K₂ ∪ K₁ ∩ K₃ ∪ K₂ ∩ K₃) :=
    HPC.Plane.isContinuum_union (HPC.Plane.isContinuum_union c₁₂ c₁₃ ⟨c, ⟨hc₁, hc₂⟩, hc₁, hc₃⟩)
      c₂₃ ⟨c, Or.inl ⟨hc₁, hc₂⟩, hc₂, hc₃⟩
  have hT := isTriod_of_core hN h₁ h₂ h₃ ⟨c, hc₁, Or.inl (Or.inl ⟨hc₁, hc₂⟩)⟩
    ⟨c, hc₂, Or.inl (Or.inl ⟨hc₁, hc₂⟩)⟩ ⟨c, hc₃, Or.inl (Or.inl ⟨hc₁, hc₂⟩)⟩
    (fun x hx => Or.inl (Or.inl hx)) (fun x hx => Or.inl (Or.inr hx)) (fun x hx => Or.inr hx)
    (fun h => n₁ fun x hx => by
      rcases h hx with (⟨-, h⟩ | ⟨-, h⟩) | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h)
    (fun h => n₂ fun x hx => by
      rcases h hx with (⟨h, -⟩ | ⟨h, -⟩) | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr h)
    (fun h => n₃ fun x hx => by
      rcases h hx with (⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr h)
  exact hAT _ (subset_univ _) hT

/-- **Homeomorphic images.** A homeomorphism `h` carries a minimal admissible map of `F` to one of
`h[F]`, whose layers are the images of the layers of `F`. -/
theorem exists_image_map (h : M ≃ₜ M) {F : Set M} {d : F → unitInterval}
    (hF : IsMinimalAdmissible F d) :
    ∃ b : (h '' F) → unitInterval, IsMinimalAdmissible (h '' F) b ∧
      ∀ S, layerSet b S = h '' layerSet d S := by
  obtain ⟨⟨a₀, b₀, hab⟩, hd, hd0⟩ := hF
  set e := h.image F with he
  have hpre : ∀ S, (d ∘ e.symm) ⁻¹' S = e '' (d ⁻¹' S) := fun S => by
    rw [preimage_comp, e.preimage_symm]
  refine ⟨d ∘ e.symm, ⟨⟨h a₀, h b₀, ?_⟩, ⟨hd.1.comp e.symm.continuous, ?_, ?_⟩, ?_⟩, ?_⟩
  · refine ⟨isContinuum_homeo_image h hab.1, mem_image_of_mem h hab.2.1,
      mem_image_of_mem h hab.2.2.1, fun K hK hKs ha hb => ?_⟩
    have hsub : h.symm '' K ⊆ F := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKs hy
      simpa using hx
    have := hab.2.2.2 (h.symm '' K) (isContinuum_homeo_image h.symm hK) hsub
      ⟨h a₀, ha, h.symm_apply_apply a₀⟩ ⟨h b₀, hb, h.symm_apply_apply b₀⟩
    rw [← this]
    ext x
    constructor
    · intro hx; exact ⟨h.symm x, ⟨x, hx, rfl⟩, h.apply_symm_apply x⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; rw [h.apply_symm_apply]; exact hy
  · intro t
    obtain ⟨w, hw⟩ := hd.2.1 t
    exact ⟨e w, by simp [hw]⟩
  · intro t
    rw [hpre]
    exact (hd.2.2 t).image _ e.continuous.continuousOn
  · intro t
    rw [hpre, ← e.image_interior, hd0 t, image_empty]
  · intro S
    simp only [layerSet, hpre, image_image]
    rfl

/-- **The extension step from an irreducible union.** Let `C` be a continuum missing `d⁻¹(0)`, with
`z ∈ C ∖ F`, such that `F ∪ C` is irreducible between a point `x₀` of `d⁻¹(0)` and `z`. Then
`F ∪ C ⊋ F` has a minimal admissible map `D` with `D⁻¹(0) = d⁻¹(0)`. -/
theorem ext_of_irreducible_union [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {F : Set M} {d : F → unitInterval} (hF : IsMinimalAdmissible F d) {C : Set M}
    (hC : Fold.Q78.IsContinuum C) (hCX : Disjoint C (layer d 0)) {x₀ z : M}
    (hx₀ : x₀ ∈ layer d 0) (hzC : z ∈ C) (hzF : z ∉ F)
    (hirr : IsIrreducibleBetween (F ∪ C) x₀ z) :
    ∃ H : Set M, F ⊂ H ∧ ∃ D : H → unitInterval, IsMinimalAdmissible H D ∧
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
  refine ⟨F ∪ C, ⟨hFH, fun h => hzF (h (Or.inr hzC))⟩, D, ⟨⟨x0, z, hirr⟩, hD, hD0⟩,
    Subset.antisymm hKX fun y hy => ?_⟩
  have hyH := hXH hy
  exact ⟨⟨y, hyH⟩, hXD ⟨y, hyH⟩ hy, rfl⟩

end NoMaxBasic

end HPC.Hagopian
