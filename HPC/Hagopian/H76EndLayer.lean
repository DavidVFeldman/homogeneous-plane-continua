import HPC.Hagopian.Hagopian76V
import HPC.Hagopian.H76Unicoh

/-!
# Batch 178, §3a: the end layer of `F` is not over `D`

`T12Data.end_layer_not_subset_aux`: for a `T12Data` package (with `O = π⁻¹[D]` open and missing
`E`, and any compact `Y` missing `O` and containing `Fr O`), the end layer `d⁻¹(1)` of `F = D.G`
does not lie in `O`.

*Proof* (commission 178 §3a): if `G = E`, the layer lies in `E`, which misses `O`. Otherwise
`d⁻¹[[0, s]] = E` with `s < 1` (`ext_layers`). If `d⁻¹(1) ⊆ O`, compactness gives `s₁ ∈ [s, 1)` with
`B := d⁻¹[[s₁, 1]] ⊆ O`. Put `A := d⁻¹[[0, s₁]]`, an extension of `E` away from `k⁻¹(0)`
(`piece_map`), and `A ≠ G`. `G` separates `p` from `f(p)` in `O`, so `(A ∪ Y) ∪ B` separates them in
the plane (`sepIn_iff_separatesPts_union_aux`); `(A ∪ Y) ∩ B = d⁻¹(s₁)` is connected, and the proper
subcontinuum `B` separates nothing (`no_proper_subcontinuum_separates`), so by Janiszewski
(`janiszewski_compact`) `A ∪ Y` separates them, i.e. `A` separates them in `O`. Irreducibility
(`D.irr`) gives `A = G`, a contradiction.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones HPC.Moore.Gen

section EndLayer

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- A set separating two points separates the plane. -/
theorem separatesPlane_of_separatesPts {B : Set Pt} {x y : Pt} (h : SeparatesPts B x y) :
    SeparatesPlane B := by
  intro hc
  obtain ⟨hx, hy, hxy⟩ := h
  exact hxy (hc.isPreconnected.subset_connectedComponentIn hx subset_rfl hy)

/-- **3a: the end layer `d⁻¹(1)` of `F` does not lie over `D`** (commission 178 §3a). -/
theorem T12Data.end_layer_not_subset_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {F : ℝ × ℝ → Pt} {D' : Set (ℝ × ℝ)} {ε₃ : ℝ} (D : T12Data E k π F D' ε₃)
    (hOo : IsOpen (π ⁻¹' (F '' D'))) (hdisj : Disjoint (π ⁻¹' (F '' D')) (toPt E))
    {Y : Set Pt} (hY : IsCompact Y) (hYO : Disjoint Y (π ⁻¹' (F '' D')))
    (hfr : frontier (π ⁻¹' (F '' D')) ⊆ Y) :
    ¬ toPt (layer D.d 1) ⊆ π ⁻¹' (F '' D') := by
  intro hsub
  set O := π ⁻¹' (F '' D') with hO
  have hG := D.hG
  haveI : CompactSpace D.G := isCompact_iff_compactSpace.mp hG.isCompact
  obtain ⟨g1, hg1⟩ := hG.2.1.2.1 1
  have hg1O : ((g1 : M) : Pt) ∈ O := hsub ⟨g1, ⟨g1, hg1, rfl⟩, rfl⟩
  by_cases hGE : D.G = E
  · have : (g1 : M) ∈ E := hGE.le g1.2
    exact disjoint_left.1 hdisj hg1O ⟨g1, this, rfl⟩
  obtain ⟨s, hs0, hs1, -, hsE, -, -⟩ := ext_layers hX hi hE hG D.hEG D.hX0 hGE
  -- the parameter bound `s₁`
  have hdc : Continuous D.d := hG.2.1.1
  have hKc : IsCompact {g : D.G | ((g : M) : Pt) ∉ O} :=
    (hOo.preimage (continuous_subtype_val.comp continuous_subtype_val)).isClosed_compl.isCompact
  obtain ⟨s₁, hss₁, hs₁1, hbound⟩ : ∃ s₁ : unitInterval, s ≤ s₁ ∧ s₁ < 1 ∧
      ∀ g : D.G, ((g : M) : Pt) ∉ O → D.d g < s₁ := by
    rcases Set.eq_empty_or_nonempty {g : D.G | ((g : M) : Pt) ∉ O} with hK | hK
    · refine ⟨s, le_rfl, hs1, fun g hg => ?_⟩
      have : g ∈ ({g : D.G | ((g : M) : Pt) ∉ O} : Set D.G) := hg
      rw [hK] at this
      exact this.elim
    · obtain ⟨g₀, hg₀, hmax⟩ := hKc.exists_isMaxOn hK
        (continuous_subtype_val.comp hdc).continuousOn
      have hlt : D.d g₀ < 1 := lt_of_le_of_ne unitInterval.le_one'
        fun h => hg₀ (hsub ⟨g₀, ⟨g₀, h, rfl⟩, rfl⟩)
      have hlt' : ((D.d g₀ : unitInterval) : ℝ) < 1 := hlt
      have hs1' : (s : ℝ) < 1 := hs1
      set r : ℝ := (max (s : ℝ) (D.d g₀ : ℝ) + 1) / 2 with hr
      have hmax1 : max (s : ℝ) (D.d g₀ : ℝ) < 1 := max_lt hs1' hlt'
      have hr0 : 0 ≤ r := by
        have := le_max_left (s : ℝ) (D.d g₀ : ℝ)
        have := s.2.1
        linarith
      have hr1 : r < 1 := by linarith
      refine ⟨⟨r, hr0, hr1.le⟩, ?_, hr1, fun g hg => ?_⟩
      · show (s : ℝ) ≤ r
        have := le_max_left (s : ℝ) (D.d g₀ : ℝ)
        linarith
      · show ((D.d g : unitInterval) : ℝ) < r
        have h1 : ((D.d g : unitInterval) : ℝ) ≤ D.d g₀ := hmax hg
        have := le_max_right (s : ℝ) (D.d g₀ : ℝ)
        linarith
  have hs₁0 : 0 < s₁ := lt_of_lt_of_le hs0 hss₁
  set A := layerSet D.d (Icc 0 s₁) with hA
  set B := layerSet D.d (Icc s₁ 1) with hB
  have hBO : toPt B ⊆ O := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    by_contra h
    exact (hbound g h).not_ge hg.1
  have hEA : E ⊆ A := by
    rw [← hsE]; exact layerSet_mono D.d (Icc_subset_Icc le_rfl hss₁)
  obtain ⟨pA, hpA, hpA0, -⟩ := piece_map hG (lsc_of_minimalAdmissible hX hi hG) hs₁0 (P := A) rfl
  have hextA : IsExtensionAway E (layer k 0) A := ⟨hEA, pA, hpA, hpA0.trans D.hX0⟩
  have hAG : A ⊆ D.G := layerSet_subset D.d _
  have hAne : A ≠ D.G := by
    intro h
    have : (g1 : M) ∈ A := by rw [h]; exact g1.2
    obtain ⟨g', hg', hgg'⟩ := this
    have : g' = g1 := Subtype.ext hgg'
    subst this
    have h1 : (1 : unitInterval) ≤ s₁ := by rw [← hg1]; exact hg'.2
    exact absurd (lt_of_lt_of_le hs₁1 h1) (lt_irrefl _)
  -- the separation in the plane
  have hsepG := D.sep
  have hpts := (sepIn_iff_separatesPts_union_aux hOo hYO hfr hsepG.1 hsepG.2.1).1 hsepG
  have hGAB : toPt D.G = toPt A ∪ toPt B := by
    have h1 : toPt A ∪ toPt B = toPt (layerSet D.d (Icc 0 s₁ ∪ Icc s₁ 1)) := by
      simp only [hA, hB, toPt, layerSet, preimage_union, image_union]
    have h2 : Icc 0 s₁ ∪ Icc s₁ 1 = (univ : Set unitInterval) := by
      ext u
      simp only [mem_union, mem_Icc, mem_univ, iff_true]
      rcases le_total u s₁ with h | h
      · exact Or.inl ⟨unitInterval.nonneg', h⟩
      · exact Or.inr ⟨h, unitInterval.le_one'⟩
    rw [h1, h2]
    simp [layerSet, toPt]
  rw [hGAB, union_right_comm] at hpts
  -- `B` separates nothing
  have hBc : Fold.Q78.IsContinuum B :=
    isContinuum_img hG.isCompact hG.2.1 isClosed_Icc isPreconnected_Icc ⟨s₁, le_rfl,
      unitInterval.le_one'⟩
  obtain ⟨g0, hg0⟩ := hG.2.1.2.1 0
  have hBM : B ≠ univ := by
    intro h
    have : (g0 : M) ∈ B := by rw [h]; exact mem_univ _
    obtain ⟨g', hg', hgg'⟩ := this
    have : g' = g0 := Subtype.ext hgg'
    subst this
    have h1 : s₁ ≤ 0 := by rw [← hg0]; exact hg'.1
    exact absurd (lt_of_lt_of_le hs₁0 h1) (lt_irrefl _)
  have hnB : ¬ SeparatesPts (toPt B) (D.p : Pt) ((D.h.symm.trans D.h₁) D.p : Pt) := fun h =>
    no_proper_subcontinuum_separates hX hi hBc hBM (separatesPlane_of_separatesPts h)
  -- `(A ∪ Y) ∩ B = d⁻¹(s₁)`, connected
  have hinter : (toPt A ∪ Y) ∩ toPt B = toPt (layer D.d s₁) := by
    ext z
    constructor
    · rintro ⟨hzA | hzY, hzB⟩
      · obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hzA
        obtain ⟨_, ⟨b, hb, hab⟩, hz⟩ := hzB
        have hba : b = a := Subtype.ext (Subtype.ext (hab ▸ hz))
        subst hba
        exact ⟨b, ⟨b, le_antisymm ha.2 hb.1, rfl⟩, rfl⟩
      · exact (disjoint_left.1 hYO hzY (hBO hzB)).elim
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      have hg' : D.d g = s₁ := hg
      exact ⟨Or.inl ⟨g, ⟨g, ⟨unitInterval.nonneg', hg'.le⟩, rfl⟩, rfl⟩,
        ⟨g, ⟨g, ⟨hg'.ge, unitInterval.le_one'⟩, rfl⟩, rfl⟩⟩
  have hconn : IsConnected ((toPt A ∪ Y) ∩ toPt B) := by
    rw [hinter]
    exact (isContinuum_layer hG.isCompact hG.2.1 s₁).2.image _ continuous_subtype_val.continuousOn
  have hAYc : IsCompact (toPt A ∪ Y) := (isCompact_toPt_layerSet hG 0 s₁).union hY
  have hsepA : SeparatesPts (toPt A ∪ Y) (D.p : Pt) ((D.h.symm.trans D.h₁) D.p : Pt) := by
    by_contra hnA
    exact HPC.Moore.janiszewski_compact hAYc (isCompact_toPt_layerSet hG s₁ 1) (Or.inl hconn)
      hnA hnB hpts
  have hAsub : toPt A ⊆ toPt D.G := image_mono hAG
  have hsepA' : SepIn O (toPt A) (D.p : Pt) ((D.h.symm.trans D.h₁) D.p : Pt) :=
    (sepIn_iff_separatesPts_union_aux hOo hYO hfr ⟨hsepG.1.1, fun h => hsepG.1.2 (hAsub h)⟩
      ⟨hsepG.2.1.1, fun h => hsepG.2.1.2 (hAsub h)⟩).2 hsepA
  exact hAne (D.irr A hextA hsepA' hAG)

end EndLayer

end HPC.Hagopian
