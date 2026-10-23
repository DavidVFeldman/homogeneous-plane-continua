import HPC.Hagopian.Hagopian76AA

/-!
# Batch 183, §2.3: the subcontinuum of `L` between two layers (`minimalAdmissible_restrict`)

Commission 183 §2, step 3: "`H`: the subcontinuum of `L` between the layer of `L` through `a` and
the layer through `b`, with the decomposition of `L` restricted and reparametrized. You proposed
`minimalAdmissible_restrict`."

* `minimalAdmissible_restrict_of_lsc`: in any metric space, if the decomposition of `G` is lower
  semicontinuous (the conclusion of Lemma 5), then for `a < b` the union `d⁻¹[[a, b]]` with the map
  `(d − a)/(b − a)` is irreducible, admissible, with layers of void interior, and its layers are the
  layers `d⁻¹(s)`, `a ≤ s ≤ b`; the end sets are `d⁻¹(a)` and `d⁻¹(b)`.
* `minimalAdmissible_restrict`: in a homogeneous indecomposable `M`, by Lemma 5
  (`lsc_of_minimalAdmissible`) the hypothesis is automatic.

**Shape change.** The batch-182 proposal asked only for *some* minimal admissible map on
`d⁻¹[[a, b]]`, with no lower-semicontinuity hypothesis. E2.4 needs more: the end sets must be the
layers `d⁻¹(a) ∋ a` and `d⁻¹(b) ∋ b`, so the statement here records the layers. That version needs
the hypothesis in general metric spaces (report §2.3, not formalized: two `sin(1/x)` curves
converge to a common limit bar from the two sides, the right one only to the upper half of the
bar. If you cut at the bar, the lower half of the bar is open in `d⁻¹[[a, 1]]`. That set is still
of type A′, but under another decomposition, whose first end set is a point). In Hagopian's `M` the
hypothesis holds (Lemma 5).

The proof follows `isTypeA'_of_subcontinuum` (batch 158, `H76Sub.lean`), with the set fixed in
advance and the layers recorded.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Restrict

variable {X : Type*} [MetricSpace X]

/-- The parameter `a + t (b − a)` of `[a, b]`. -/
def restrictParam (a b : unitInterval) (hab : a ≤ b) (t : unitInterval) : unitInterval :=
  ⟨a + t * (b - a), by
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have ha0 : (0 : ℝ) ≤ a := a.2.1
    have hb1 : (b : ℝ) ≤ 1 := b.2.2
    have hab' : (a : ℝ) ≤ b := hab
    constructor <;> nlinarith⟩

theorem restrictParam_mem (a b : unitInterval) (hab : a ≤ b) (t : unitInterval) :
    restrictParam a b hab t ∈ Icc a b := by
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hab' : (a : ℝ) ≤ b := hab
  constructor
  · show (a : ℝ) ≤ a + t * (b - a); nlinarith
  · show (a : ℝ) + t * (b - a) ≤ b; nlinarith

theorem restrictParam_zero (a b : unitInterval) (hab : a ≤ b) : restrictParam a b hab 0 = a := by
  apply Subtype.ext; simp [restrictParam]

theorem restrictParam_one (a b : unitInterval) (hab : a ≤ b) : restrictParam a b hab 1 = b := by
  apply Subtype.ext; simp [restrictParam]

/-- **§2.3, `minimalAdmissible_restrict` (general form).** If `d` is a minimal admissible map on
`G` whose decomposition is lower semicontinuous, then for `a < b` the set `H = d⁻¹[[a, b]]` has a
minimal admissible map `e` whose layers are the layers of `d` over `[a, b]`:
`e⁻¹(t) = d⁻¹(a + t (b − a))`. In particular `e⁻¹(0) = d⁻¹(a)` and `e⁻¹(1) = d⁻¹(b)`. -/
theorem minimalAdmissible_restrict_of_lsc {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {a b : unitInterval}
    (hab : a < b) :
    ∃ e : layerSet d (Icc a b) → unitInterval, IsMinimalAdmissible (layerSet d (Icc a b)) e ∧
      ∀ t, layer e t = layer d (restrictParam a b hab.le t) := by
  have hd := hG.2.1
  set H := layerSet d (Icc a b) with hHdef
  have hHG : H ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hH : Fold.Q78.IsContinuum H :=
    isContinuum_img hG.isCompact hd isClosed_Icc isPreconnected_Icc ⟨a, le_rfl, hab.le⟩
  obtain ⟨ga, hga⟩ := hd.2.1 a
  obtain ⟨gb, hgb⟩ := hd.2.1 b
  have hgaH : (ga : X) ∈ H := ⟨ga, show d ga ∈ Icc a b by rw [hga]; exact ⟨le_rfl, hab.le⟩, rfl⟩
  have hgbH : (gb : X) ∈ H := ⟨gb, show d gb ∈ Icc a b by rw [hgb]; exact ⟨hab.le, le_rfl⟩, rfl⟩
  have hla : ∀ K : Set X, (ga : X) ∈ K → (K ∩ layer d a).Nonempty := fun K hK =>
    ⟨ga, hK, ga, hga, rfl⟩
  have hlb : ∀ K : Set X, (gb : X) ∈ K → (K ∩ layer d b).Nonempty := fun K hK =>
    ⟨gb, hK, gb, hgb, rfl⟩
  have hirr : IsIrreducibleBetween H (ga : X) (gb : X) := by
    refine ⟨hH, hgaH, hgbH, fun K hK hKH hp hq => ?_⟩
    exact eq_layerSet_of_subcontinuum hG hL (hKH.trans hHG) hK hab (hla K hp) (hlb K hq) hKH
  have hba : (0 : ℝ) < (b : ℝ) - a := sub_pos.2 hab
  have hval : ∀ x : H, (a : ℝ) ≤ d (Set.inclusion hHG x) ∧ (d (Set.inclusion hHG x) : ℝ) ≤ b := by
    intro x
    obtain ⟨g, hg, hgx⟩ := x.2
    have : Set.inclusion hHG x = g := Subtype.ext hgx.symm
    rw [this]
    exact ⟨hg.1, hg.2⟩
  let k' : H → unitInterval := fun x =>
    ⟨((d (Set.inclusion hHG x) : ℝ) - a) / (b - a),
      div_nonneg (by linarith [(hval x).1]) hba.le,
      (div_le_one hba).2 (by linarith [(hval x).2])⟩
  set sv := restrictParam a b hab.le with hsv
  have hk'iff : ∀ (x : H) (t : unitInterval), k' x = t ↔ d (Set.inclusion hHG x) = sv t := by
    intro x t
    rw [← Subtype.coe_inj, ← Subtype.coe_inj]
    change ((d (Set.inclusion hHG x) : ℝ) - a) / (b - a) = t ↔
      (d (Set.inclusion hHG x) : ℝ) = a + t * (b - a)
    rw [div_eq_iff hba.ne']
    constructor <;> intro h <;> linarith
  have hmemH : ∀ g : G, d g ∈ Icc a b → (g : X) ∈ H := fun g hg => ⟨g, hg, rfl⟩
  have hfib : ∀ t, Subtype.val '' (k' ⁻¹' {t}) = layer d (sv t) := by
    intro t
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Set.inclusion hHG y, (hk'iff y t).1 hy, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      have hgt : d g = sv t := hg
      have hgH : (g : X) ∈ H := hmemH g (hgt ▸ restrictParam_mem a b hab.le t)
      exact ⟨⟨g, hgH⟩, (hk'iff ⟨g, hgH⟩ t).2 hg, rfl⟩
  refine ⟨k', ⟨⟨_, _, hirr⟩, ⟨?_, fun t => ?_, fun t => ?_⟩, fun t => ?_⟩, hfib⟩
  · refine Continuous.subtype_mk ?_ _
    exact ((continuous_subtype_val.comp (hd.1.comp (continuous_inclusion hHG))).sub
      continuous_const).div_const _
  · obtain ⟨g, hg⟩ := hd.2.1 (sv t)
    have hgH : (g : X) ∈ H := hmemH g (hg ▸ restrictParam_mem a b hab.le t)
    exact ⟨⟨g, hgH⟩, (hk'iff ⟨g, hgH⟩ t).2 hg⟩
  · have hc : IsConnected (layer d (sv t)) := by
      have := hd.2.2 (sv t)
      exact this.image _ continuous_subtype_val.continuousOn
    rw [← hfib t] at hc
    exact ⟨hc.nonempty.of_image, Topology.IsInducing.subtypeVal.isPreconnected_image.1 hc.2⟩
  · by_contra hne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
    have hxO := isOpen_interior (s := k' ⁻¹' {t})
    obtain ⟨O', hO'o, hO'eq⟩ := isOpen_induced_iff.1 hxO
    have hsubfib : ∀ y : H, (y : X) ∈ O' → d (Set.inclusion hHG y) = sv t := fun y hy =>
      (hk'iff y t).1 (interior_subset (s := k' ⁻¹' {t})
        (show y ∈ interior (k' ⁻¹' {t}) by rw [← hO'eq]; exact hy))
    have hxO' : (x : X) ∈ O' := by rw [← hO'eq] at hx; exact hx
    have hxt := hsubfib x hxO'
    by_cases hint : (sv t : unitInterval) ∈ Ioo a b
    · have hopen : IsOpen ({g : G | (g : X) ∈ O'} ∩ d ⁻¹' Ioo a b) :=
        (hO'o.preimage continuous_subtype_val).inter (isOpen_Ioo.preimage hd.1)
      have hsub' : {g : G | (g : X) ∈ O'} ∩ d ⁻¹' Ioo a b ⊆ d ⁻¹' {sv t} := by
        rintro g ⟨hgO, hgI⟩
        have hgH : (g : X) ∈ H := hmemH g ⟨hgI.1.le, hgI.2.le⟩
        exact hsubfib ⟨g, hgH⟩ hgO
      have := interior_maximal hsub' hopen
      rw [hG.2.2 (sv t)] at this
      exact this ⟨hxO', hxt ▸ hint⟩
    · have hend : sv t = a ∨ sv t = b := by
        have h1 := (restrictParam_mem a b hab.le t).1
        have h2 := (restrictParam_mem a b hab.le t).2
        simp only [mem_Ioo, not_and_or, not_lt] at hint
        rcases hint with h | h
        · exact Or.inl (le_antisymm h h1)
        · exact Or.inr (le_antisymm h2 h)
      have hxl : (x : X) ∈ layer d (sv t) := ⟨Set.inclusion hHG x, hxt, rfl⟩
      have hcl : (x : X) ∈ closure (layerSet d (Ioo a b)) := by
        rcases hend with h | h
        · exact layer_subset_closure_Ioo hG hL hab (h ▸ hxl)
        · exact layer_subset_closure_Ioo' hG hL hab (h ▸ hxl)
      obtain ⟨_, hgO, g, hgI, rfl⟩ := mem_closure_iff.1 hcl O' hO'o hxO'
      have hgH : (g : X) ∈ H := hmemH g ⟨hgI.1.le, hgI.2.le⟩
      have hgt : d g = sv t := hsubfib ⟨g, hgH⟩ hgO
      have hgI' : d g ∈ Ioo a b := hgI
      rcases hend with h | h
      · rw [hgt, h] at hgI'; exact lt_irrefl _ hgI'.1
      · rw [hgt, h] at hgI'; exact lt_irrefl _ hgI'.2

end Restrict

section RestrictM

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§2.3, `minimalAdmissible_restrict`** (commission 183 §2 step 3; batch-182 proposal). In a
homogeneous indecomposable plane continuum `M`, for a minimal admissible `(L, d)` and `a < b`, the
subcontinuum `d⁻¹[[a, b]]` of `L` has a minimal admissible map whose layers are the layers
`d⁻¹(a + t (b − a))`; its end sets are `d⁻¹(a)` and `d⁻¹(b)`. (Lemma 5 supplies the lower
semicontinuity of `minimalAdmissible_restrict_of_lsc`.) -/
theorem minimalAdmissible_restrict (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {L : Set M} {d : L → unitInterval} (hL : IsMinimalAdmissible L d) {a b : unitInterval}
    (hab : a < b) :
    ∃ e : layerSet d (Icc a b) → unitInterval, IsMinimalAdmissible (layerSet d (Icc a b)) e ∧
      ∀ t, layer e t = layer d (restrictParam a b hab.le t) := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL.isCompact
  exact minimalAdmissible_restrict_of_lsc hL (lsc_of_minimalAdmissible hX hi hL) hab

end RestrictM

end HPC.Hagopian
