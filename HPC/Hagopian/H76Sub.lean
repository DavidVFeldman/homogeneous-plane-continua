import HPC.Hagopian.H76Lemma5End

/-!
# Batch 158, toward item C: subcontinua of a type A′ continuum with continuous decomposition

Hagopian 1976, p. 343: "Note that every continuum essential to `R(E)` is of type A′ (Lemma 5)." The
part of this remark that follows from Lemma 5 alone: if `G` is irreducible with a minimal admissible
map `d` whose decomposition is lower semicontinuous at every element (Lemma 5), then a subcontinuum
`H` of `G` meeting two layers is the union `d⁻¹[[a, b]]` of the layers between its extreme ones, and is
of type A′ (`isTypeA'_of_subcontinuum`):

* `layerSet_Ioo_subset`: `H` contains `d⁻¹((a, b))` — otherwise `d⁻¹[[0, a]] ∪ H ∪ d⁻¹[[b, 1]]` is a
  subcontinuum of `G` meeting both end sets that misses a point of `G` (irreducibility);
* `layer_subset_closure_Ioo`: `d⁻¹(a) ⊆ Cl d⁻¹((a, b))`, by lower semicontinuity at `d⁻¹(a)`;
* the map `(d − a)/(b − a)` on `H` is admissible with layers of void interior in `H`.

What remains for the remark is the containment of an essential continuum in one extension (from
step 5 of Lemma 6; `OPEN.md`, batch 158, item C).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Jones

section Sub

variable {X : Type*} [MetricSpace X]

/-- A subcontinuum of `G` meeting the layers `d⁻¹(a)` and `d⁻¹(b)` contains `d⁻¹((a, b))`. -/
theorem layerSet_Ioo_subset {G : Set X} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    {K : Set X} (hKG : K ⊆ G) (hK : Fold.Q78.IsContinuum K) {a b : unitInterval}
    (ha : (K ∩ layer d a).Nonempty) (hb : (K ∩ layer d b).Nonempty) :
    layerSet d (Ioo a b) ⊆ K := by
  have hGc := hG.isCompact
  have hd := hG.2.1
  have hA0 : Fold.Q78.IsContinuum (layerSet d (Icc 0 a)) :=
    isContinuum_img hGc hd isClosed_Icc isPreconnected_Icc ⟨0, le_rfl, unitInterval.nonneg'⟩
  have hA1 : Fold.Q78.IsContinuum (layerSet d (Icc b 1)) :=
    isContinuum_img hGc hd isClosed_Icc isPreconnected_Icc ⟨1, unitInterval.le_one', le_rfl⟩
  obtain ⟨p, hpK, hpa⟩ := ha
  obtain ⟨q, hqK, hqb⟩ := hb
  have hpA0 : p ∈ layerSet d (Icc 0 a) := by
    obtain ⟨y, hy, rfl⟩ := hpa
    exact ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy).le⟩, rfl⟩
  have hqA1 : q ∈ layerSet d (Icc b 1) := by
    obtain ⟨y, hy, rfl⟩ := hqb
    exact ⟨y, ⟨(mem_singleton_iff.1 hy).ge, unitInterval.le_one'⟩, rfl⟩
  set A := layerSet d (Icc 0 a) ∪ K ∪ layerSet d (Icc b 1) with hAdef
  have hAc : Fold.Q78.IsContinuum A :=
    ⟨(hA0.1.union hK.1).union hA1.1,
      IsConnected.union ⟨q, Or.inr hqK, hqA1⟩ (IsConnected.union ⟨p, hpA0, hpK⟩ hA0.2 hK.2) hA1.2⟩
  have hAG : A ⊆ G := by
    refine union_subset (union_subset ?_ hKG) ?_
    · rintro _ ⟨y, -, rfl⟩; exact y.2
    · rintro _ ⟨y, -, rfl⟩; exact y.2
  have h0 : (A ∩ layer d 0).Nonempty := by
    obtain ⟨y, hy⟩ := hd.2.1 0
    exact ⟨y, Or.inl (Or.inl ⟨y, ⟨by rw [hy], by rw [hy]; exact unitInterval.nonneg'⟩, rfl⟩),
      y, hy, rfl⟩
  have h1 : (A ∩ layer d 1).Nonempty := by
    obtain ⟨y, hy⟩ := hd.2.1 1
    exact ⟨y, Or.inr ⟨y, ⟨by rw [hy]; exact unitInterval.le_one', by rw [hy]⟩, rfl⟩, y, hy, rfl⟩
  have hAeq := end_sets_aux hG hAG hAc h0 h1
  clear_value A
  rintro _ ⟨y, ⟨hya, hyb⟩, rfl⟩
  have hyA : (y : X) ∈ A := hAeq ▸ y.2
  rw [hAdef] at hyA
  rcases hyA with (h | h) | h
  · obtain ⟨y', hy', hyy⟩ := h
    have : y' = y := Subtype.ext hyy
    subst this
    exact absurd hy'.2 (not_le.2 hya)
  · exact h
  · obtain ⟨y', hy', hyy⟩ := h
    have : y' = y := Subtype.ext hyy
    subst this
    exact absurd hy'.1 (not_le.2 hyb)

/-- **Lower semicontinuity at `d⁻¹(a)`**: every point of `d⁻¹(a)` is a limit of points of the layers
`d⁻¹(t)`, `a < t < b`. -/
theorem layer_subset_closure_Ioo {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {a b : unitInterval}
    (hab : a < b) : layer d a ⊆ closure (layerSet d (Ioo a b)) := by
  have hd := hG.2.1
  rintro _ ⟨y, hya, rfl⟩
  have hya' : d y = a := hya
  have hAB : layerSet d (Ioc a 1) ∪ layer d a = layerSet d (Icc a 1) := by
    ext x
    simp only [layerSet, layer, mem_union, mem_image, mem_preimage, mem_Ioc, mem_Icc,
      mem_singleton_iff]
    constructor
    · rintro (⟨z, ⟨h1, h2⟩, rfl⟩ | ⟨z, h, rfl⟩)
      · exact ⟨z, ⟨h1.le, h2⟩, rfl⟩
      · exact ⟨z, ⟨h.ge, h ▸ unitInterval.le_one'⟩, rfl⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      rcases h1.lt_or_eq with h | h
      · exact Or.inl ⟨z, ⟨h, h2⟩, rfl⟩
      · exact Or.inr ⟨z, h.symm, rfl⟩
  have hpc : IsPreconnected (layerSet d (Ioc a 1) ∪ layer d a) := by
    rw [hAB]
    exact (isContinuum_img hG.isCompact hd isClosed_Icc isPreconnected_Icc
      ⟨1, unitInterval.le_one', le_rfl⟩).2.isPreconnected
  have hBc : IsClosed (layer d a) := (isCompact_img hG.isCompact hd.1 isClosed_singleton).isClosed
  have hAn : (layerSet d (Ioc a 1)).Nonempty := by
    obtain ⟨z, hz⟩ := hd.2.1 b
    exact ⟨z, z, ⟨by rw [hz]; exact hab, by rw [hz]; exact unitInterval.le_one'⟩, rfl⟩
  obtain ⟨_, hx₁cl, x₁, hx₁a, rfl⟩ :=
    closure_inter_of_preconnected hpc hBc hAn (layer_nonempty hd.2.1 a)
  have hx₁a' : d x₁ = a := hx₁a
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨W, hWo, hWc, hWz⟩ := hL x₁ y (show d y = d x₁ by rw [hya', hx₁a']) (ball y ε)
    isOpen_ball (mem_ball_self hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hWo x₁ (hWc (mem_cls_self x₁))
  have hba : (0 : ℝ) < (b : ℝ) - a := sub_pos.2 hab
  obtain ⟨δ', hδ', hcont⟩ := Metric.continuousAt_iff.1 (hd.1.continuousAt (x := x₁)) _ hba
  obtain ⟨_, ⟨z, hzI, rfl⟩, hzd⟩ := Metric.mem_closure_iff.1 hx₁cl (min δ δ') (lt_min hδ hδ')
  have hz1 : dist z x₁ < δ := by
    rw [dist_comm]; exact lt_of_lt_of_le hzd (min_le_left _ _)
  have hz2 : dist z x₁ < δ' := by
    rw [dist_comm]; exact lt_of_lt_of_le hzd (min_le_right _ _)
  have hzW : z ∈ W := hball (mem_ball.2 hz1)
  have hzb : d z < b := by
    have h := hcont hz2
    rw [hx₁a', Subtype.dist_eq, Real.dist_eq] at h
    have := (abs_lt.1 h).2
    exact Subtype.coe_lt_coe.1 (by linarith)
  obtain ⟨v, hv, hvV⟩ := hWz z hzW
  have hv' : d v = d z := hv
  refine ⟨v, ⟨v, ⟨hv' ▸ hzI.1, hv' ▸ hzb⟩, rfl⟩, ?_⟩
  rw [dist_comm]; exact hvV

/-- The same at the upper layer `d⁻¹(b)`, by the reversed map. -/
theorem layer_subset_closure_Ioo' {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {a b : unitInterval}
    (hab : a < b) : layer d b ⊆ closure (layerSet d (Ioo a b)) := by
  have hker : Setoid.ker (unitInterval.symm ∘ d) = Setoid.ker d := by
    ext z w
    change unitInterval.symm (d z) = unitInterval.symm (d w) ↔ d z = d w
    exact ⟨fun h => by simpa using congrArg unitInterval.symm h, fun h => by rw [h]⟩
  have hab' : unitInterval.symm b < unitInterval.symm a := by
    rw [← Subtype.coe_lt_coe, unitInterval.coe_symm_eq, unitInterval.coe_symm_eq]
    have : (a : ℝ) < b := hab
    linarith
  have h := layer_subset_closure_Ioo hG.symm_comp (hker ▸ hL) hab'
  rw [layer_symm_comp, unitInterval.symm_symm] at h
  have hset : layerSet (unitInterval.symm ∘ d) (Ioo (unitInterval.symm b) (unitInterval.symm a)) =
      layerSet d (Ioo a b) := by
    have : unitInterval.symm ⁻¹' Ioo (unitInterval.symm b) (unitInterval.symm a) = Ioo a b := by
      ext t
      simp only [mem_preimage, mem_Ioo, ← Subtype.coe_lt_coe, unitInterval.coe_symm_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [layerSet, preimage_comp, this]
  rwa [hset] at h

/-- **A subcontinuum meeting the extreme layers `d⁻¹(a)`, `d⁻¹(b)` is `d⁻¹[[a, b]]`.** -/
theorem eq_layerSet_of_subcontinuum {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {K : Set X} (hKG : K ⊆ G)
    (hK : Fold.Q78.IsContinuum K) {a b : unitInterval} (hab : a < b)
    (ha : (K ∩ layer d a).Nonempty) (hb : (K ∩ layer d b).Nonempty)
    (hKab : K ⊆ layerSet d (Icc a b)) : K = layerSet d (Icc a b) := by
  refine subset_antisymm hKab ?_
  have hIoo := layerSet_Ioo_subset hG hKG hK ha hb
  have hcl : closure (layerSet d (Ioo a b)) ⊆ K := hK.1.isClosed.closure_subset_iff.2 hIoo
  rintro _ ⟨y, ⟨h1, h2⟩, rfl⟩
  rcases h1.lt_or_eq with h1 | h1
  · rcases h2.lt_or_eq with h2 | h2
    · exact hIoo ⟨y, ⟨h1, h2⟩, rfl⟩
    · exact hcl (layer_subset_closure_Ioo' hG hL hab ⟨y, h2, rfl⟩)
  · exact hcl (layer_subset_closure_Ioo hG hL hab ⟨y, h1.symm, rfl⟩)

/-- **A subcontinuum of `G` meeting two layers is of type A′** (the part of Hagopian's p. 343 remark
that follows from Lemma 5): it is `d⁻¹[[a, b]]`, irreducible between its two extreme layers, with the
admissible map `(d − a)/(b − a)`. -/
theorem isTypeA'_of_subcontinuum {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {H : Set X} (hHG : H ⊆ G)
    (hH : Fold.Q78.IsContinuum H) {t₁ t₂ : unitInterval} (ht : t₁ ≠ t₂)
    (h₁ : (H ∩ layer d t₁).Nonempty) (h₂ : (H ∩ layer d t₂).Nonempty) :
    ∃ a b : unitInterval, a < b ∧ H = layerSet d (Icc a b) ∧ IsTypeA' H := by
  have hd := hG.2.1
  -- the extreme layers
  set S : Set G := Subtype.val ⁻¹' H with hS
  have hSc : IsCompact S := (hH.1.isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨_, hx1, g1, hg1, rfl⟩ := h₁
  obtain ⟨_, hx2, g2, hg2, rfl⟩ := h₂
  have hg₀S : g1 ∈ S := hx1
  obtain ⟨ga, hgaS, hmin⟩ := hSc.exists_isMinOn ⟨g1, hg₀S⟩ hd.1.continuousOn
  obtain ⟨gb, hgbS, hmax⟩ := hSc.exists_isMaxOn ⟨g1, hg₀S⟩ hd.1.continuousOn
  set a := d ga
  set b := d gb
  have hsub : H ⊆ layerSet d (Icc a b) := fun x hx =>
    ⟨⟨x, hHG hx⟩, ⟨hmin (show (⟨x, hHG hx⟩ : G) ∈ S from hx),
      hmax (show (⟨x, hHG hx⟩ : G) ∈ S from hx)⟩, rfl⟩
  have hab : a < b := by
    have e1 : d g1 = t₁ := hg1
    have e2 : d g2 = t₂ := hg2
    have l1 := hmin (show g1 ∈ S from hx1)
    have u1 := hmax (show g1 ∈ S from hx1)
    have l2 := hmin (show g2 ∈ S from hx2)
    have u2 := hmax (show g2 ∈ S from hx2)
    simp only [mem_setOf_eq] at l1 u1 l2 u2
    refine lt_of_le_of_ne (l1.trans u1) fun h => ht ?_
    rw [← e1, ← e2]
    exact le_antisymm (u1.trans (h.symm.le.trans l2)) (u2.trans (h.symm.le.trans l1))
  have hla : (H ∩ layer d a).Nonempty := ⟨ga, hgaS, ga, rfl, rfl⟩
  have hlb : (H ∩ layer d b).Nonempty := ⟨gb, hgbS, gb, rfl, rfl⟩
  have hHeq := eq_layerSet_of_subcontinuum hG hL hHG hH hab hla hlb hsub
  refine ⟨a, b, hab, hHeq, ⟨(ga : X), (gb : X), hH, hgaS, hgbS, fun K hK hKH hp hq => ?_⟩, ?_⟩
  · -- irreducibility
    rw [hHeq]
    exact eq_layerSet_of_subcontinuum hG hL (hKH.trans hHG) hK hab ⟨ga, hp, ga, rfl, rfl⟩
      ⟨gb, hq, gb, rfl, rfl⟩ (hKH.trans hsub)
  -- the rescaled map
  have hba : (0 : ℝ) < (b : ℝ) - a := sub_pos.2 hab
  have hval : ∀ x : H, (a : ℝ) ≤ d (Set.inclusion hHG x) ∧ (d (Set.inclusion hHG x) : ℝ) ≤ b :=
    fun x => ⟨hmin (show Set.inclusion hHG x ∈ S from x.2),
      hmax (show Set.inclusion hHG x ∈ S from x.2)⟩
  let k' : H → unitInterval := fun x =>
    ⟨((d (Set.inclusion hHG x) : ℝ) - a) / (b - a),
      div_nonneg (by linarith [(hval x).1]) hba.le,
      (div_le_one hba).2 (by linarith [(hval x).2])⟩
  -- the parameter in `G` of the layer `k'⁻¹(t)`
  have hsv : ∀ t : unitInterval, (0 : ℝ) ≤ a + t * (b - a) ∧ (a : ℝ) + t * (b - a) ≤ 1 := fun t => by
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have ha0 : (0 : ℝ) ≤ a := a.2.1
    have hb1 : (b : ℝ) ≤ 1 := b.2.2
    constructor <;> nlinarith
  let sv : unitInterval → unitInterval := fun t => ⟨a + t * (b - a), hsv t⟩
  have hk'iff : ∀ (x : H) (t : unitInterval), k' x = t ↔ d (Set.inclusion hHG x) = sv t := by
    intro x t
    rw [← Subtype.coe_inj, ← Subtype.coe_inj]
    change ((d (Set.inclusion hHG x) : ℝ) - a) / (b - a) = t ↔
      (d (Set.inclusion hHG x) : ℝ) = a + t * (b - a)
    rw [div_eq_iff hba.ne']
    constructor <;> intro h <;> linarith
  have hsvI : ∀ t, (sv t : ℝ) ∈ Icc (a : ℝ) b := fun t => by
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    change (a : ℝ) + t * (b - a) ∈ Icc (a : ℝ) b
    constructor <;> nlinarith
  have hmemH : ∀ g : G, d g ∈ Icc a b → (g : X) ∈ H := fun g hg => hHeq ▸ ⟨g, hg, rfl⟩
  have hfib : ∀ t, Subtype.val '' (k' ⁻¹' {t}) = layer d (sv t) := by
    intro t
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Set.inclusion hHG y, (hk'iff y t).1 hy, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      have hgH : (g : X) ∈ H := hmemH g ⟨(hsvI t).1.trans_eq (congrArg Subtype.val hg).symm |>
        fun h => Subtype.coe_le_coe.1 h, Subtype.coe_le_coe.1
          ((congrArg Subtype.val (show d g = sv t from hg)).le.trans (hsvI t).2)⟩
      exact ⟨⟨g, hgH⟩, (hk'iff ⟨g, hgH⟩ t).2 hg, rfl⟩
  refine ⟨k', ⟨?_, fun t => ?_, fun t => ?_⟩, fun t => ?_⟩
  · -- continuity
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_subtype_val.comp (hd.1.comp (continuous_inclusion hHG))).sub
      continuous_const).div_const _
  · -- surjectivity
    obtain ⟨g, hg⟩ := hd.2.1 (sv t)
    have hgH : (g : X) ∈ H := hmemH g ⟨Subtype.coe_le_coe.1 (by rw [hg]; exact (hsvI t).1),
      Subtype.coe_le_coe.1 (by rw [hg]; exact (hsvI t).2)⟩
    exact ⟨⟨g, hgH⟩, (hk'iff ⟨g, hgH⟩ t).2 hg⟩
  · -- connected fibres
    have hc : IsConnected (layer d (sv t)) := by
      have := hd.2.2 (sv t)
      exact this.image _ continuous_subtype_val.continuousOn
    rw [← hfib t] at hc
    exact ⟨hc.nonempty.of_image, Topology.IsInducing.subtypeVal.isPreconnected_image.1 hc.2⟩
  · -- void interiors
    by_contra hne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
    have hxO := isOpen_interior (s := k' ⁻¹' {t})
    obtain ⟨O', hO'o, hO'eq⟩ := isOpen_induced_iff.1 hxO
    have hsubfib : ∀ y : H, (y : X) ∈ O' → d (Set.inclusion hHG y) = sv t := fun y hy =>
      (hk'iff y t).1 (interior_subset (s := k' ⁻¹' {t}) (show y ∈ interior (k' ⁻¹' {t}) by rw [← hO'eq]; exact hy))
    have hxO' : (x : X) ∈ O' := by rw [← hO'eq] at hx; exact hx
    have hxt := hsubfib x hxO'
    by_cases hint : (sv t : unitInterval) ∈ Ioo a b
    · -- an interior layer: an open set of `G` inside `d⁻¹(sv t)`
      have hopen : IsOpen ({g : G | (g : X) ∈ O'} ∩ d ⁻¹' Ioo a b) :=
        (hO'o.preimage continuous_subtype_val).inter (isOpen_Ioo.preimage hd.1)
      have hsub' : {g : G | (g : X) ∈ O'} ∩ d ⁻¹' Ioo a b ⊆ d ⁻¹' {sv t} := by
        rintro g ⟨hgO, hgI⟩
        have hgH : (g : X) ∈ H := hmemH g ⟨hgI.1.le, hgI.2.le⟩
        exact hsubfib ⟨g, hgH⟩ hgO
      have := interior_maximal hsub' hopen
      rw [hG.2.2 (sv t)] at this
      exact this ⟨hxO', hxt ▸ hint⟩
    · -- an end layer: points of `d⁻¹((a, b))` come close
      have hend : sv t = a ∨ sv t = b := by
        have h1 := (hsvI t).1
        have h2 := (hsvI t).2
        simp only [mem_Ioo, not_and_or, not_lt] at hint
        rcases hint with h | h
        · exact Or.inl (le_antisymm h (Subtype.coe_le_coe.1 h1))
        · exact Or.inr (le_antisymm (Subtype.coe_le_coe.1 h2) h)
      have hxl : (x : X) ∈ layer d (sv t) := ⟨Set.inclusion hHG x, hxt, rfl⟩
      have hcl : (x : X) ∈ closure (layerSet d (Ioo a b)) := by
        rcases hend with h | h
        · exact layer_subset_closure_Ioo hG hL hab (h ▸ hxl)
        · exact layer_subset_closure_Ioo' hG hL hab (h ▸ hxl)
      obtain ⟨_, hgO, g, hgI, rfl⟩ := mem_closure_iff.1 hcl O' hO'o hxO'
      have hgH : (g : X) ∈ H := hmemH g ⟨hgI.1.le, hgI.2.le⟩
      have := hsubfib ⟨g, hgH⟩ hgO
      have hgt : d g = sv t := this
      have hgI' : d g ∈ Ioo a b := hgI
      rcases hend with h | h
      · rw [hgt, h] at hgI'; exact lt_irrefl _ hgI'.1
      · rw [hgt, h] at hgI'; exact lt_irrefl _ hgI'.2

end Sub

end HPC.Hagopian
