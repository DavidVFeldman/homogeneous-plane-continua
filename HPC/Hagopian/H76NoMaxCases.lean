import HPC.Hagopian.H76NoMaxBasic

/-!
# Lemma 4 of Hagopian 1976, "no maximal element": the two extension cases

`F` (map `d`, end sets `X = d⁻¹(0)`, `T = d⁻¹(1)`) and a second continuum `B` (map `b`), in the
situation of Hagopian's proof, where `B = h⁻¹[F]`.

* `ext_of_subset` (`F ⊆ B`). If `p ∈ T ∩ b⁻¹(u)` (`u < 1`) and `b⁻¹[u, 1]` misses `X`, then
  `F ∪ b⁻¹[u, 1]` is a proper extension. Suppose `b⁻¹(1) ⊆ F`. Then `F ⊇ b⁻¹(b(x₀), 1)`. The
  continua `b⁻¹[u, 1]` and `b⁻¹[u', u]` both lie in `F`, pass through `p`, and leave `T`, so both
  contain a tail of `F` (`tail_subset`). Then `b⁻¹(u)` contains a tail, which is impossible
  (`false_of_layer_open`). So some `z ∈ b⁻¹(1)` lies outside `F`. Any continuum in `F ∪ b⁻¹[u, 1]`
  from `x₀` to `z` contains `b⁻¹(b(x₀), 1) ∋ p`, hence `F`, hence everything.
* `ext_of_side` (the configuration where a layer of `B` contains a tail). Suppose `b⁻¹(u)` contains
  `d⁻¹(s, 1]`, `b⁻¹[0, u) ⊆ d⁻¹[0, s']` (`s < s' < 1`), `F ∩ B` misses `b⁻¹(u, 1]`, and `B` misses
  `X`. Then `F ∪ Cl b⁻¹(u, 1]` is a proper extension. Every point of `d⁻¹(s', 1)` is a limit of
  `b⁻¹(u, 1]`, since `b⁻¹(u)` has void interior in `B` and `b⁻¹[0, u)` stays in `d⁻¹[0, s']`. So a
  continuum in the union from `x₀` to a point of `b⁻¹(1)` contains `b⁻¹(u, 1]`, its closure, a tail
  of `F`, `T`, and finally `F`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section NoMaxCases

variable {M : Set Pt}

/-- An open subset `b⁻¹(α, β)` of `B` contained in `F ⊆ B` lies in no layer of `F`. -/
theorem not_subset_layer_of_open {F B : Set M} {d : F → unitInterval} {b : B → unitInterval}
    (hd0 : ∀ t, interior (d ⁻¹' {t}) = ∅) (hb : IsAdmissibleMap B b) (hFB : F ⊆ B)
    {α β : unitInterval} (hαβ : α < β) (hsub : layerSet b (Ioo α β) ⊆ F) (t : unitInterval) :
    ¬ layerSet b (Ioo α β) ⊆ layer d t := by
  intro hlay
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 (isOpen_Ioo.preimage hb.1 :
    IsOpen (b ⁻¹' Ioo α β))
  set S : Set F := Subtype.val ⁻¹' O with hSdef
  have hSo : IsOpen S := hO.preimage continuous_subtype_val
  have hSt : S ⊆ d ⁻¹' {t} := by
    intro w hw
    have hwB : (⟨w, hFB w.2⟩ : B) ∈ b ⁻¹' Ioo α β := by rw [← hOeq]; exact hw
    obtain ⟨w', hw', hww⟩ := hlay ⟨⟨w, hFB w.2⟩, hwB, rfl⟩
    have : w' = w := Subtype.ext hww
    rw [← this]; exact hw'
  obtain ⟨m, hm1, hm2⟩ := exists_between hαβ
  obtain ⟨v, hv⟩ := hb.2.1 m
  have hvI : v ∈ b ⁻¹' Ioo α β := by rw [mem_preimage, hv]; exact ⟨hm1, hm2⟩
  have hvF : (v : M) ∈ F := hsub ⟨v, hvI, rfl⟩
  have hvS : (⟨v, hvF⟩ : F) ∈ S := by
    show (v : M) ∈ O
    have : v ∈ Subtype.val ⁻¹' O := by rw [hOeq]; exact hvI
    exact this
  have := interior_maximal hSt hSo hvS
  rw [hd0 t] at this; exact this

/-- **Case `F ⊆ B`.** -/
theorem ext_of_subset [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {F B : Set M} {d : F → unitInterval} {b : B → unitInterval} (hF : IsMinimalAdmissible F d)
    (hB : IsMinimalAdmissible B b) (hFB : F ⊆ B) {u : unitInterval} (hu1 : u < 1)
    (hfarX : Disjoint (layerSet b (Icc u 1)) (layer d 0)) {p : M} (hp1 : p ∈ layer d 1)
    (hpu : p ∈ layer b u) :
    ∃ H : Set M, F ⊂ H ∧ ∃ D : H → unitInterval, IsMinimalAdmissible H D ∧
      layer D 0 = layer d 0 := by
  have hF' := hF
  obtain ⟨⟨a, a', hab⟩, hd, hd0⟩ := hF
  obtain ⟨⟨c, c', hcc⟩, hb, hb0⟩ := hB
  have hFc := hab.1
  have hBc := hcc.1
  obtain ⟨x0, hx0⟩ := hd.2.1 0
  have hx0X : (x0 : M) ∈ layer d 0 := ⟨x0, hx0, rfl⟩
  set x0B : B := ⟨x0, hFB x0.2⟩ with hx0Bdef
  have hbx0 : b x0B < u := lt_of_not_ge fun h =>
    disjoint_left.1 hfarX ⟨x0B, ⟨h, unitInterval.le_one'⟩, rfl⟩ hx0X
  have hpF : p ∈ F := img_subset _ hp1
  obtain ⟨pb, hpb, rfl⟩ := hpu
  have hbp : b pb = u := hpb
  have hK' := isContinuum_img hBc.1 hb isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 hu1.le)
  have hpK' : (pb : M) ∈ layerSet b (Icc u 1) := ⟨pb, ⟨hbp.ge, unitInterval.le_one'⟩, rfl⟩
  -- some `z ∈ b⁻¹(1)` lies outside `F`
  obtain ⟨z, hz1, hzF⟩ : ∃ z ∈ layer b 1, z ∉ F := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨zb, hzb⟩ := hb.2.1 1
    have hmidF : layerSet b (Ioo (b x0B) 1) ⊆ F := by
      rintro _ ⟨v, hv, rfl⟩
      exact layer_subset_of_meets' hcc hb hFB hFc ⟨x0, x0.2, x0B, rfl, rfl⟩
        ⟨zb, hcon _ ⟨zb, hzb, rfl⟩, zb, hzb, rfl⟩ hv.1 hv.2 ⟨v, rfl, rfl⟩
    obtain ⟨u', hu'1, hu'2⟩ := exists_between hbx0
    have hK'F : layerSet b (Icc u 1) ⊆ F := by
      rintro _ ⟨v, hv, rfl⟩
      rcases eq_or_lt_of_le hv.2 with h | h
      · exact hcon _ ⟨v, h, rfl⟩
      · exact hmidF ⟨v, ⟨(hu'1.trans hu'2).trans_le hv.1, h⟩, rfl⟩
    have hK'' :=
      isContinuum_img hBc.1 hb isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 hu'2.le)
    have hpK'' : (pb : M) ∈ layerSet b (Icc u' u) := ⟨pb, ⟨hbp ▸ hu'2.le, hbp.le⟩, rfl⟩
    -- points of `F` off `T` in each
    have hI1 : layerSet b (Ioo u 1) ⊆ F := fun y ⟨v, hv, hvy⟩ =>
      hmidF ⟨v, ⟨(hu'1.trans hu'2).trans hv.1, hv.2⟩, hvy⟩
    have hI2 : layerSet b (Ioo u' u) ⊆ F := fun y ⟨v, hv, hvy⟩ =>
      hmidF ⟨v, ⟨hu'1.trans hv.1, hv.2.trans hu1⟩, hvy⟩
    obtain ⟨y1, hy1, hy1T⟩ := not_subset.1 (not_subset_layer_of_open hd0 hb hFB hu1 hI1 1)
    obtain ⟨y2, hy2, hy2T⟩ := not_subset.1 (not_subset_layer_of_open hd0 hb hFB hu'2 hI2 1)
    set w1 : F := ⟨y1, hI1 hy1⟩
    set w2 : F := ⟨y2, hI2 hy2⟩
    have hw1 : d w1 < 1 := lt_of_le_of_ne unitInterval.le_one' fun h => hy1T ⟨w1, h, rfl⟩
    have hw2 : d w2 < 1 := lt_of_le_of_ne unitInterval.le_one' fun h => hy2T ⟨w2, h, rfl⟩
    have hy1K : y1 ∈ layerSet b (Icc u 1) := by
      obtain ⟨v, hv, rfl⟩ := hy1; exact ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩
    have hy2K : y2 ∈ layerSet b (Icc u' u) := by
      obtain ⟨v, hv, rfl⟩ := hy2; exact ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩
    have ht1 := tail_subset hHU hF' hK' hpK' hp1 w1 hy1K hw1
    have ht2 := tail_subset hHU hF' hK'' hpK'' hp1 w2 hy2K hw2
    have hbad : layerSet d (Ioo (max (d w1) (d w2)) 1) ⊆ layer b u := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨v1, hv1, hv1e⟩ := ht1 ⟨v, ⟨(le_max_left _ _).trans_lt hv.1, hv.2.le⟩, rfl⟩
      obtain ⟨v2, hv2, hv2e⟩ := ht2 ⟨v, ⟨(le_max_right _ _).trans_lt hv.1, hv.2.le⟩, rfl⟩
      have : v1 = v2 := Subtype.ext (hv1e.trans hv2e.symm)
      rw [this] at hv1
      exact ⟨v2, le_antisymm hv2.2 hv1.1, hv2e⟩
    exact false_of_layer_open hd hb.1 hb0 (max_lt hw1 hw2) hu'2 hu1
      (fun y ⟨v, hv, hvy⟩ => hmidF ⟨v, ⟨hu'1.trans hv.1, hv.2⟩, hvy⟩) hbad
  -- the extension
  set C := layerSet b (Icc u 1) with hCdef
  have hzC : z ∈ C := by
    obtain ⟨v, hv, rfl⟩ := hz1
    have hv' : b v = 1 := hv
    exact ⟨v, ⟨hv' ▸ hu1.le, hv'.le⟩, rfl⟩
  have hirr : IsIrreducibleBetween (F ∪ C) x0 z := by
    refine ⟨HPC.Plane.isContinuum_union hFc hK' ⟨pb, hpF, hpK'⟩, Or.inl x0.2, Or.inr hzC, ?_⟩
    intro L hL hLs hx0L hzL
    refine Subset.antisymm hLs ?_
    have hLB : L ⊆ B := hLs.trans (union_subset hFB (img_subset _))
    obtain ⟨zb', hzb', rfl⟩ := hz1
    have hmid : layerSet b (Ioo (b x0B) 1) ⊆ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact layer_subset_of_meets' hcc hb hLB hL ⟨x0, hx0L, x0B, rfl, rfl⟩
        ⟨zb', hzL, zb', hzb', rfl⟩ hv.1 hv.2 ⟨v, rfl, rfl⟩
    have hpL : (pb : M) ∈ L := hmid ⟨pb, ⟨hbp ▸ hbx0, hbp ▸ hu1⟩, rfl⟩
    have hLF := isContinuum_inter_of_HU hHU hL hFc ⟨x0, hx0L, x0.2⟩
    have hFL : F ⊆ L := by
      have := eq_of_meets_ends hab hd hd0 inter_subset_right hLF ⟨x0, ⟨hx0L, x0.2⟩, hx0X⟩
        ⟨pb, ⟨hpL, hpF⟩, hp1⟩
      rw [← this]; exact inter_subset_left
    have hCL : C ⊆ L := by
      rintro _ ⟨v, hv, rfl⟩
      rcases eq_or_lt_of_le hv.2 with h | h
      · exact closure_minimal hmid hL.1.isClosed
          (layer_one_subset_closure hb.1 hb0 (hbx0.trans hu1) ⟨v, h, rfl⟩)
      · exact hmid ⟨v, ⟨hbx0.trans_le hv.1, h⟩, rfl⟩
    exact union_subset hFL hCL
  exact ext_of_irreducible_union hX hHU hAT hF' hK' hfarX hx0X hzC hzF hirr

/-- **The configuration where a layer of `B` contains a tail of `F`.** -/
theorem ext_of_side [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {F B : Set M} {d : F → unitInterval} {b : B → unitInterval} (hF : IsMinimalAdmissible F d)
    (hB : IsMinimalAdmissible B b) (hBX : Disjoint B (layer d 0)) {u s s' : unitInterval}
    (hu1 : u < 1) (hss' : s < s') (hs'1 : s' < 1)
    (hbad : layerSet d (Ioc s 1) ⊆ layer b u)
    (hnear : layerSet b (Iio u) ⊆ layerSet d (Icc 0 s'))
    (hfar : Disjoint (F ∩ B) (layerSet b (Ioi u))) :
    ∃ H : Set M, F ⊂ H ∧ ∃ D : H → unitInterval, IsMinimalAdmissible H D ∧
      layer D 0 = layer d 0 := by
  have hF' := hF
  obtain ⟨⟨a, a', hab⟩, hd, hd0⟩ := hF
  obtain ⟨⟨c, c', hcc⟩, hb, hb0⟩ := hB
  have hFc := hab.1
  have hBc := hcc.1
  set P := layerSet b (Ioi u) with hPdef
  set C' := closure P with hC'def
  have hPB : P ⊆ B := img_subset _
  have hC'B : C' ⊆ B := closure_minimal hPB hBc.1.isClosed
  obtain ⟨zb, hzb⟩ := hb.2.1 1
  have hzP : (zb : M) ∈ P := ⟨zb, show b zb ∈ Ioi u by rw [hzb]; exact hu1, rfl⟩
  have hPconn : IsPreconnected P :=
    (hb.isPreconnected_preimage hBc.1 isPreconnected_Ioi).image _
      continuous_subtype_val.continuousOn
  have hC' : Fold.Q78.IsContinuum C' :=
    ⟨isClosed_closure.isCompact, ⟨zb, subset_closure hzP⟩, hPconn.closure⟩
  -- accumulation
  have hacc : layerSet d (Ioo s' 1) ⊆ C' := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hvw⟩ := hbad ⟨w, ⟨hss'.trans hw.1, hw.2.le⟩, rfl⟩
    set Q := layerSet d (Icc 0 s') with hQdef
    have hQc : IsClosed Q := (isCompact_img hFc.1 hd.1 isClosed_Icc).isClosed
    have hwQ : (w : M) ∉ Q := by
      rintro ⟨w', hw', hww⟩
      have : w' = w := Subtype.ext hww
      rw [this] at hw'
      exact absurd (lt_of_lt_of_le hw.1 hw'.2) (lt_irrefl _)
    have hvcl : v ∈ closure (b ⁻¹' Ioi u) := by
      rw [_root_.mem_closure_iff]
      intro o ho hvo
      have ho' : IsOpen (o ∩ Subtype.val ⁻¹' Qᶜ) :=
        ho.inter (hQc.isOpen_compl.preimage continuous_subtype_val)
      have hvo' : v ∈ o ∩ Subtype.val ⁻¹' Qᶜ := ⟨hvo, by
        show (v : M) ∉ Q
        rw [hvw]; exact hwQ⟩
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have hsub : o ∩ Subtype.val ⁻¹' Qᶜ ⊆ b ⁻¹' {u} := by
        intro v' ⟨hv'o, hv'Q⟩
        rcases lt_trichotomy (b v') u with hlt | heq | hgt
        · exact absurd (hnear ⟨v', hlt, rfl⟩) hv'Q
        · exact heq
        · have : v' ∈ o ∩ b ⁻¹' Ioi u := ⟨hv'o, hgt⟩
          rw [hne] at this; simp at this
      have := interior_maximal hsub ho' hvo'
      rw [hb0 u] at this; exact this
    rw [← hvw]
    exact image_closure_subset_closure_image continuous_subtype_val ⟨v, hvcl, rfl⟩
  have hzF : (zb : M) ∉ F := fun h => disjoint_left.1 hfar ⟨h, zb.2⟩ hzP
  have hC'X : Disjoint C' (layer d 0) := disjoint_of_subset_left hC'B hBX
  obtain ⟨x0, hx0⟩ := hd.2.1 0
  have hx0X : (x0 : M) ∈ layer d 0 := ⟨x0, hx0, rfl⟩
  have hmidne : (layerSet d (Ioo s' 1)).Nonempty := by
    obtain ⟨m, hm1, hm2⟩ := exists_between hs'1
    obtain ⟨w, hw⟩ := hd.2.1 m
    exact ⟨w, w, show d w ∈ Ioo s' 1 by rw [hw]; exact ⟨hm1, hm2⟩, rfl⟩
  have hirr : IsIrreducibleBetween (F ∪ C') x0 zb := by
    refine ⟨HPC.Plane.isContinuum_union hFc hC' ?_, Or.inl x0.2, Or.inr (subset_closure hzP),
      ?_⟩
    · obtain ⟨y, hy⟩ := hmidne; exact ⟨y, img_subset _ hy, hacc hy⟩
    intro L hL hLs hx0L hzL
    refine Subset.antisymm hLs ?_
    have hLC := isContinuum_inter_of_HU hHU hL hC' ⟨zb, hzL, subset_closure hzP⟩
    obtain ⟨w, hwL, hwF, hwC⟩ := meets_inter_of_cover hL.2.2 hFc.1.isClosed hC'.1.isClosed hLs
      ⟨x0, hx0L, x0.2⟩ ⟨zb, hzL, subset_closure hzP⟩
    have hwB : w ∈ B := hC'B hwC
    have hwu : b ⟨w, hwB⟩ = u := by
      have h1 : w ∉ P := fun h => disjoint_left.1 hfar ⟨hwF, hwB⟩ h
      have h2 : w ∈ layerSet b (Ici u) :=
        closure_minimal (show P ⊆ layerSet b (Ici u) from fun y ⟨v, hv, hvy⟩ =>
            ⟨v, show u ≤ b v from le_of_lt hv, hvy⟩)
          (isCompact_img hBc.1 hb.1 isClosed_Ici).isClosed hwC
      obtain ⟨v, hv, hvw⟩ := h2
      have : v = ⟨w, hwB⟩ := Subtype.ext hvw
      rw [← this]
      have hv' : u ≤ b v := hv
      rcases eq_or_lt_of_le hv' with h | h
      · exact h.symm
      · exact absurd ⟨v, h, hvw⟩ h1
    have hmid : layerSet b (Ioo u 1) ⊆ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact (layer_subset_of_meets' hcc hb (inter_subset_right.trans hC'B) hLC
        ⟨w, ⟨hwL, hwC⟩, ⟨w, hwB⟩, hwu, rfl⟩ ⟨zb, ⟨hzL, subset_closure hzP⟩, zb, hzb, rfl⟩
        hv.1 hv.2 ⟨v, rfl, rfl⟩).1
    have hPL : P ⊆ L := by
      rintro _ ⟨v, hv, rfl⟩
      rcases eq_or_lt_of_le (show b v ≤ 1 from unitInterval.le_one') with h | h
      · exact closure_minimal hmid hL.1.isClosed
          (layer_one_subset_closure hb.1 hb0 hu1 ⟨v, h, rfl⟩)
      · exact hmid ⟨v, ⟨hv, h⟩, rfl⟩
    have hC'L : C' ⊆ L := closure_minimal hPL hL.1.isClosed
    have hFL : F ⊆ L := by
      have hLF := isContinuum_inter_of_HU hHU hL hFc ⟨x0, hx0L, x0.2⟩
      obtain ⟨p', hp'⟩ := hd.2.1 1
      have hp'L : (p' : M) ∈ L := closure_minimal (hacc.trans hC'L) hL.1.isClosed
        (layer_one_subset_closure hd.1 hd0 hs'1 ⟨p', hp', rfl⟩)
      have := eq_of_meets_ends hab hd hd0 inter_subset_right hLF ⟨x0, ⟨hx0L, x0.2⟩, hx0X⟩
        ⟨p', ⟨hp'L, p'.2⟩, p', hp', rfl⟩
      rw [← this]; exact inter_subset_left
    exact union_subset hFL hC'L
  exact ext_of_irreducible_union hX hHU hAT hF' hC' hC'X hx0X (subset_closure hzP) hzF hirr

end NoMaxCases

end HPC.Hagopian
