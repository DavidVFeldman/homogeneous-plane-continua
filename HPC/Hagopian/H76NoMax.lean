import HPC.Hagopian.H76NoMaxCases
import HPC.Hagopian.H76Lemma2

/-!
# Lemma 4 of Hagopian 1976: no maximal element

`exists_proper_extension`. In a compact, homogeneous, hereditarily unicoherent, atriodic space,
every continuum `F` with a minimal admissible map `d` has a proper extension `H ⊋ F` with the same
end layer `d⁻¹(0)`. This is Hagopian's "no maximal element" (p. 341), with the step he leaves
unargued supplied.

Hagopian's set-up. Let `p ∈ T = d⁻¹(1)` and `ε = ρ(X, d⁻¹[1/2, 1])`. By Lemma 2 there are a point
`q ∈ d⁻¹(1/2, 1)` and an `ε`-homeomorphism `h` with `h(p) = q`. Put `u = d(q)` and `B = h⁻¹[F]`, with
map `b` and layers `b⁻¹(t) = h⁻¹[d⁻¹(t)]`. Then `p ∈ b⁻¹(u)`, `b⁻¹[1/2, 1]` misses `X`, and `b⁻¹(0)`
misses `d⁻¹[1/2, 1]`.

The proof is a case analysis.
* `F ⊆ B`: `ext_of_subset`.
* `F ⊄ B`: then `B` misses `X`. One of the halves `C₀ = b⁻¹[0, u]`, `C₁ = b⁻¹[u, 1]` (both through
  `p`) may meet `F` only in `T`. Then `ext_of_branch` applies; if `C₁ ⊆ F`, then `C₀` is the half to
  use.
* Otherwise both halves contain a tail of `F` (`tail_subset`), so the layer `b⁻¹(u)` contains a tail
  `d⁻¹(s, 1]`. Then `F ∩ B` cannot meet both sides of `b⁻¹(u)` (`false_of_layer_open`). The three
  continua `d⁻¹[0, u]`, `d⁻¹[u, 1]`, `h[d⁻¹[0, s']]` have a common point in `d⁻¹(u)`, so one of them
  lies in the union of the other two (`three_continua`). The third alternative would give `F ⊆ B`.
  The first gives `b⁻¹[0, u) ⊆ d⁻¹[0, s']`, and the second the same with the sides exchanged. In
  either case `ext_of_side` applies, in the second case to the reversed map of `B`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section NoMax

variable {M : Set Pt}

/-- **No maximal element.** Every continuum with a minimal admissible map has a proper extension
with the same end layer `d⁻¹(0)`. -/
theorem exists_proper_extension [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {F : Set M} {d : F → unitInterval} (hF : IsMinimalAdmissible F d) :
    ∃ H : Set M, F ⊂ H ∧ ∃ D : H → unitInterval, IsMinimalAdmissible H D ∧
      layer D 0 = layer d 0 := by
  have hF' := hF
  obtain ⟨⟨a, a', hab⟩, hd, hd0⟩ := hF
  have hFc := hab.1
  set half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩ with hhalfdef
  have hhalf0 : (0 : unitInterval) < half := by
    show (0 : ℝ) < 1 / 2; norm_num
  have hhalf1 : half < 1 := by
    show (1 / 2 : ℝ) < 1; norm_num
  set Y := layerSet d (Icc half 1) with hYdef
  have hXc : IsCompact (layer d 0) := isCompact_img hFc.1 hd.1 isClosed_singleton
  have hYc : IsClosed Y := (isCompact_img hFc.1 hd.1 isClosed_Icc).isClosed
  have hXY : Disjoint (layer d 0) Y := by
    rw [disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww⟩
    have : w' = w := Subtype.ext hww
    rw [this] at hw'
    have h0 : d w = 0 := hw
    have hw'' : half ≤ d w := hw'.1
    rw [h0] at hw''
    exact absurd hw'' (not_le.2 hhalf0)
  obtain ⟨r, hr0, hr⟩ := exists_pos_forall_lt_edist hXc hYc hXY
  set ε : ℝ := (r : ℝ) with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact_mod_cast hr0
  have hfar : ∀ x ∈ layer d 0, ∀ y ∈ Y, ε < dist x y := by
    intro x hx y hy
    have h1 : ENNReal.ofReal (r : ℝ) < ENNReal.ofReal (dist x y) := by
      rw [ENNReal.ofReal_coe_nnreal, ← edist_dist]; exact hr x hx y hy
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
  -- `p`, `q`, `h`
  obtain ⟨p', hp'⟩ := hd.2.1 1
  have hp1 : (p' : M) ∈ layer d 1 := ⟨p', hp', rfl⟩
  obtain ⟨hWo, hpW⟩ := lemma2_aux hX hε (p' : M)
  set W := {y : M | ∃ h : M ≃ₜ M, h p' = y ∧ ∀ v, dist v (h v) < ε} with hWdef
  set O : Set F := Subtype.val ⁻¹' W ∩ d ⁻¹' Ioi half with hOdef
  have hOo : IsOpen O := (hWo.preimage continuous_subtype_val).inter (isOpen_Ioi.preimage hd.1)
  have hp'O : p' ∈ O := ⟨hpW, by rw [mem_preimage, hp']; exact hhalf1⟩
  have hO1 : ¬ O ⊆ d ⁻¹' {1} := fun h => by
    have := interior_maximal h hOo hp'O
    rw [hd0 1] at this; exact this
  obtain ⟨q', ⟨hq'W, hq'half⟩, hq'1⟩ := not_subset.1 hO1
  set u := d q' with hudef
  have hu1 : u < 1 := lt_of_le_of_ne unitInterval.le_one' hq'1
  have hhalfu : half < u := hq'half
  have hu0 : 0 < u := hhalf0.trans hhalfu
  obtain ⟨h, hhp, hhmove⟩ := hq'W
  set g := h.symm with hgdef
  have hgmove : ∀ v, dist v (g v) < ε := fun v => by
    have := hhmove (g v)
    rw [h.apply_symm_apply] at this
    rwa [dist_comm]
  set B := g '' F with hBdef
  obtain ⟨b, hB, hbS⟩ : ∃ b : B → unitInterval, IsMinimalAdmissible B b ∧
      ∀ S, layerSet b S = g '' layerSet d S := exists_image_map g hF'
  have hB' := hB
  obtain ⟨⟨c, c', hcc⟩, hb, hb0⟩ := hB
  have hBc := hcc.1
  have hpu : (p' : M) ∈ layer b u := by
    show (p' : M) ∈ layerSet b {u}
    rw [hbS]
    exact ⟨q', ⟨q', rfl, rfl⟩, by rw [← hhp]; exact h.symm_apply_apply _⟩
  -- the two distance facts
  have f1 : ∀ S ⊆ Icc half 1, Disjoint (layerSet b S) (layer d 0) := by
    intro S hS
    rw [hbS, disjoint_left]
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩ hyX
    have h1 := hfar _ hyX w ⟨w, hS hw, rfl⟩
    have h2 := hhmove (g w)
    rw [h.apply_symm_apply] at h2
    linarith
  have f2 : Disjoint (layer b 0) Y := by
    show Disjoint (layerSet b {0}) Y
    rw [hbS, disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hy
    have h1 := hfar x hx _ hy
    have h2 := hgmove x
    linarith
  -- Case `F ⊆ B`
  by_cases hFB : F ⊆ B
  · exact ext_of_subset hX hHU hAT hF' hB' hFB hu1
      (f1 _ fun t ht => ⟨hhalfu.le.trans ht.1, ht.2⟩) hp1 hpu
  -- Case `F ⊄ B`
  have hpB : (p' : M) ∈ B := img_subset _ hpu
  have hpF : (p' : M) ∈ F := p'.2
  have hJ := isContinuum_inter_of_HU hHU hFc hBc ⟨p', hpF, hpB⟩
  have hBX : Disjoint B (layer d 0) := by
    rw [disjoint_left]
    intro x hxB hxX
    apply hFB
    have := eq_of_meets_ends hab hd hd0 inter_subset_left hJ ⟨x, ⟨img_subset _ hxX, hxB⟩, hxX⟩
      ⟨p', ⟨hpF, hpB⟩, hp1⟩
    rw [← this]; exact inter_subset_right
  set C0 := layerSet b (Icc 0 u) with hC0def
  set C1 := layerSet b (Icc u 1) with hC1def
  have hC0 := isContinuum_img hBc.1 hb isClosed_Icc isPreconnected_Icc
    (nonempty_Icc.2 (unitInterval.nonneg' : (0 : unitInterval) ≤ u))
  have hC1 := isContinuum_img hBc.1 hb isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 hu1.le)
  obtain ⟨pb, hpb, hpbe⟩ := hpu
  have hbp : b pb = u := hpb
  have hpC0 : (p' : M) ∈ C0 := ⟨pb, ⟨unitInterval.nonneg', hbp.le⟩, hpbe⟩
  have hpC1 : (p' : M) ∈ C1 := ⟨pb, ⟨hbp.ge, unitInterval.le_one'⟩, hpbe⟩
  have hY1 : layer d 1 ⊆ Y := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : d w = 1 := hw
    exact ⟨w, show d w ∈ Icc half 1 by rw [hw']; exact ⟨hhalf1.le, le_rfl⟩, rfl⟩
  by_cases h0 : C0 ∩ F ⊆ layer d 1
  · refine ext_of_branch hX hHU hAT hF' hC0 ⟨p', hpC0, hpF⟩ h0 ?_
    intro hsub
    obtain ⟨z0, hz0⟩ := hb.2.1 0
    have hz0C : (z0 : M) ∈ C0 := ⟨z0, ⟨hz0.ge, by rw [hz0]; exact unitInterval.nonneg'⟩, rfl⟩
    exact disjoint_left.1 f2 ⟨z0, hz0, rfl⟩ (hY1 (h0 ⟨hz0C, hsub hz0C⟩))
  obtain ⟨y0, ⟨hy0C, hy0F⟩, hy0T⟩ := not_subset.1 h0
  set w0 : F := ⟨y0, hy0F⟩ with hw0def
  have hw0 : d w0 < 1 := lt_of_le_of_ne unitInterval.le_one' fun h => hy0T ⟨w0, h, rfl⟩
  have ht0 := tail_subset hHU hF' hC0 hpC0 hp1 w0 hy0C hw0
  by_cases h1 : C1 ∩ F ⊆ layer d 1
  · by_cases hC1F : C1 ⊆ F
    · exfalso
      obtain ⟨z1, hz1⟩ := hb.2.1 1
      have hz1C1 : (z1 : M) ∈ C1 := ⟨z1, ⟨by rw [hz1]; exact hu1.le, hz1.le⟩, rfl⟩
      obtain ⟨wz, hwz, hwze⟩ := h1 ⟨hz1C1, hC1F hz1C1⟩
      have hwz' : d wz = 1 := hwz
      obtain ⟨v, hv, hve⟩ := ht0 ⟨wz, show d wz ∈ Ioc (d w0) 1 by rw [hwz']; exact ⟨hw0, le_rfl⟩,
        hwze⟩
      have : v = z1 := Subtype.ext hve
      rw [this] at hv
      have hv2 : b z1 ≤ u := hv.2
      rw [hz1] at hv2
      exact absurd hv2 (not_le.2 hu1)
    · exact ext_of_branch hX hHU hAT hF' hC1 ⟨p', hpC1, hpF⟩ h1 hC1F
  -- the configuration: `b⁻¹(u)` contains a tail of `F`
  obtain ⟨y1, ⟨hy1C, hy1F⟩, hy1T⟩ := not_subset.1 h1
  set w1 : F := ⟨y1, hy1F⟩ with hw1def
  have hw1 : d w1 < 1 := lt_of_le_of_ne unitInterval.le_one' fun h => hy1T ⟨w1, h, rfl⟩
  have ht1 := tail_subset hHU hF' hC1 hpC1 hp1 w1 hy1C hw1
  set s := max (d w0) (d w1) with hsdef
  have hs1 : s < 1 := max_lt hw0 hw1
  have hbad : layerSet d (Ioc s 1) ⊆ layer b u := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨v0, hv0, hv0e⟩ := ht0 ⟨v, ⟨(le_max_left _ _).trans_lt hv.1, hv.2⟩, rfl⟩
    obtain ⟨v1, hv1, hv1e⟩ := ht1 ⟨v, ⟨(le_max_right _ _).trans_lt hv.1, hv.2⟩, rfl⟩
    have : v0 = v1 := Subtype.ext (hv0e.trans hv1e.symm)
    rw [this] at hv0
    exact ⟨v1, le_antisymm hv0.2 hv1.1, hv1e⟩
  obtain ⟨s', hss', hs'1⟩ := exists_between hs1
  -- `F ∩ B` does not meet both sides of `b⁻¹(u)`
  have hside : ¬ ((F ∩ B ∩ layerSet b (Iio u)).Nonempty ∧
      (F ∩ B ∩ layerSet b (Ioi u)).Nonempty) := by
    rintro ⟨⟨_, hyJ, v, hv, rfl⟩, ⟨_, hy'J, v', hv', rfl⟩⟩
    refine false_of_layer_open hd hb.1 hb0 hs1 hv hv' ?_
      (fun x ⟨w, hw, hwx⟩ => hbad ⟨w, ⟨hw.1, hw.2.le⟩, hwx⟩)
    rintro _ ⟨t, ht, rfl⟩
    exact (layer_subset_of_meets' hcc hb inter_subset_right hJ ⟨v, hyJ, v, rfl, rfl⟩
      ⟨v', hy'J, v', rfl, rfl⟩ ht.1 ht.2 ⟨t, rfl, rfl⟩).1
  -- the three continua
  obtain ⟨ws, hws⟩ := hd.2.1 s'
  have hwsbad : (ws : M) ∈ layer b u :=
    hbad ⟨ws, show d ws ∈ Ioc s 1 by rw [hws]; exact ⟨hss', unitInterval.le_one'⟩, rfl⟩
  have hc : h ws ∈ layer d u := by
    have hlay : layer b u = g '' layer d u := hbS {u}
    rw [hlay] at hwsbad
    obtain ⟨a0, ha0, ha0e⟩ := hwsbad
    have : h (ws : M) = a0 := by rw [← ha0e]; exact h.apply_symm_apply a0
    rw [this]; exact ha0
  set K1 := layerSet d (Icc 0 u) with hK1def
  set K2 := layerSet d (Icc u 1) with hK2def
  set K3 := h '' layerSet d (Icc 0 s') with hK3def
  have hK1 := isContinuum_img hFc.1 hd isClosed_Icc isPreconnected_Icc
    (nonempty_Icc.2 (unitInterval.nonneg' : (0 : unitInterval) ≤ u))
  have hK2 := isContinuum_img hFc.1 hd isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 hu1.le)
  have hK3 := isContinuum_homeo_image h (isContinuum_img hFc.1 hd isClosed_Icc
    isPreconnected_Icc (nonempty_Icc.2 (unitInterval.nonneg' : (0 : unitInterval) ≤ s')))
  obtain ⟨wc, hwc, hwce⟩ := hc
  have hwc' : d wc = u := hwc
  have hcK1 : h ws ∈ K1 := ⟨wc, ⟨unitInterval.nonneg', hwc'.le⟩, hwce⟩
  have hcK2 : h ws ∈ K2 := ⟨wc, ⟨hwc'.ge, unitInterval.le_one'⟩, hwce⟩
  have hcK3 : h ws ∈ K3 :=
    ⟨ws, ⟨ws, show d ws ∈ Icc 0 s' by rw [hws]; exact ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, rfl⟩
  rcases three_continua hHU hAT hK1 hK2 hK3 hcK1 hcK2 hcK3 with hi | hii | hiii
  · -- `b⁻¹[0, u) ⊆ d⁻¹[0, s']`
    have hnear : layerSet b (Iio u) ⊆ layerSet d (Icc 0 s') := by
      rw [hbS]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      rcases hi ⟨w, ⟨unitInterval.nonneg', le_of_lt hw⟩, rfl⟩ with h2 | h3
      · obtain ⟨w', hw', hww⟩ := h2
        have : w' = w := Subtype.ext hww
        rw [this] at hw'
        exact absurd hw'.1 (not_le.2 hw)
      · obtain ⟨c0, hc0, hc0e⟩ := h3
        have : g w = c0 := by rw [← hc0e]; exact h.symm_apply_apply c0
        rw [this]; exact hc0
    have hfarJ : Disjoint (F ∩ B) (layerSet b (Ioi u)) := by
      rw [disjoint_left]
      intro y hyJ hyP
      obtain ⟨z0, hz0⟩ := hb.2.1 0
      have hz0I : (z0 : M) ∈ layerSet b (Iio u) :=
        ⟨z0, show b z0 < u by rw [hz0]; exact hu0, rfl⟩
      exact hside ⟨⟨z0, ⟨img_subset _ (hnear hz0I), z0.2⟩, hz0I⟩, ⟨y, hyJ, hyP⟩⟩
    exact ext_of_side hX hHU hAT hF' hB' hBX hu1 hss' hs'1 hbad hnear hfarJ
  · -- `b⁻¹(u, 1] ⊆ d⁻¹[0, s']`: the same with the map of `B` reversed
    have hnear : layerSet b (Ioi u) ⊆ layerSet d (Icc 0 s') := by
      rw [hbS]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      rcases hii ⟨w, ⟨le_of_lt hw, unitInterval.le_one'⟩, rfl⟩ with h2 | h3
      · obtain ⟨w', hw', hww⟩ := h2
        have : w' = w := Subtype.ext hww
        rw [this] at hw'
        exact absurd hw'.2 (not_le.2 hw)
      · obtain ⟨c0, hc0, hc0e⟩ := h3
        have : g w = c0 := by rw [← hc0e]; exact h.symm_apply_apply c0
        rw [this]; exact hc0
    have hfarJ : Disjoint (F ∩ B) (layerSet b (Iio u)) := by
      rw [disjoint_left]
      intro y hyJ hyP
      obtain ⟨z1, hz1⟩ := hb.2.1 1
      have hz1I : (z1 : M) ∈ layerSet b (Ioi u) :=
        ⟨z1, show u < b z1 by rw [hz1]; exact hu1, rfl⟩
      exact hside ⟨⟨y, hyJ, hyP⟩, ⟨z1, ⟨img_subset _ (hnear hz1I), z1.2⟩, hz1I⟩⟩
    have hBσ : IsMinimalAdmissible B (unitInterval.symm ∘ b) :=
      ⟨⟨c, c', hcc⟩, isAdmissibleMap_symm hb, interior_symm_fibre hb0⟩
    refine ext_of_side hX hHU hAT hF' hBσ hBX (u := unitInterval.symm u) ?_ hss' hs'1 ?_ ?_ ?_
    · rw [← unitInterval.symm_zero, unitInterval.symm_lt_symm]; exact hu0
    · intro x hx
      obtain ⟨v, hv, hve⟩ := hbad hx
      have hv' : b v = u := hv
      exact ⟨v, show unitInterval.symm (b v) = unitInterval.symm u by rw [hv'], hve⟩
    · rintro _ ⟨v, hv, rfl⟩
      have hv' : unitInterval.symm (b v) < unitInterval.symm u := hv
      rw [unitInterval.symm_lt_symm] at hv'
      exact hnear ⟨v, hv', rfl⟩
    · rw [disjoint_left]
      rintro _ hyJ ⟨v, hv, rfl⟩
      have hv' : unitInterval.symm u < unitInterval.symm (b v) := hv
      rw [unitInterval.symm_lt_symm] at hv'
      exact disjoint_left.1 hfarJ hyJ ⟨v, hv', rfl⟩
  · -- `h[d⁻¹[0, s']] ⊆ F`: then `F ⊆ B`
    exfalso
    apply hFB
    intro x hx
    by_cases hxs : d ⟨x, hx⟩ ≤ s'
    · have hhx : h x ∈ K1 ∪ K2 := hiii ⟨x, ⟨⟨x, hx⟩, ⟨unitInterval.nonneg', hxs⟩, rfl⟩, rfl⟩
      have hhxF : h x ∈ F := by
        rcases hhx with h' | h'
        · exact img_subset _ h'
        · exact img_subset _ h'
      exact ⟨h x, hhxF, h.symm_apply_apply x⟩
    · exact img_subset _
        (hbad ⟨⟨x, hx⟩, ⟨hss'.trans (not_le.1 hxs), unitInterval.le_one'⟩, rfl⟩)

/-- **Lemma 4** (p. 340), from `exists_proper_extension` and `ext_chain`. -/
theorem lemma4_aux [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsChain (· ⊆ ·) {F | IsExtensionAway E (layer k 0) F} ∧
      ∀ F ∈ {F | IsExtensionAway E (layer k 0) F},
        ∃ H ∈ {F | IsExtensionAway E (layer k 0) F}, F ⊂ H := by
  refine ⟨fun _ hF _ hH _ => ext_chain hHU hAT hE hF hH, ?_⟩
  rintro F ⟨hEF, d, hd, hdX⟩
  obtain ⟨H, hFH, D, hD, hDX⟩ := exists_proper_extension hX hHU hAT hd
  exact ⟨H, ⟨hEF.trans hFH.1, D, hD, hDX.trans hdX⟩, hFH⟩

/-- **Lemma 4, the countable form** (p. 342). -/
theorem lemma4_seq_aux [CompactSpace M] (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ Fs : ℕ → Set M, StrictMono Fs ∧ (∀ i, IsExtensionAway E (layer k 0) (Fs i)) ∧
      extUnion E (layer k 0) = ⋃ i, Fs i :=
  have h4 := lemma4_aux hX hHU hAT hE
  exists_strictMono_seq_of_chain h4.1
    (fun _ ⟨_, _, ⟨⟨_, _, hab⟩, _, _⟩, _⟩ => hab.1.1.isClosed) ⟨E, subset_rfl, k, hE, rfl⟩ h4.2

end NoMax

end HPC.Hagopian
