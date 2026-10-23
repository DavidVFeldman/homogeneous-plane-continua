import HPC.Hagopian.Hagopian76Q

/-!
# Batch 173, item A: Property 3 by descent (supporting file)

Commission 173 §1. The objects of the descent are *layer crossings*: connected subsets `Z` of one
layer `d⁻¹(u)` of the extension `G`, lying over the closure of Hagopian's domain `D = F[D′]` and
meeting the two closed side segments over `3/22` and `19/22` (`LayerCrossing`). The set of such
`u` is closed (`isClosed_layerCrossing`, from `crossing_set_closed`); it is defined by continua, not
by maps, as the commission asks.

* `IsCrossRegion`: the properties of `D = F[D′]` used (open, inside the open strip of height `c₁`
  over `(3/22, 19/22)`, frontier meeting `π[M]` only over the axis and the two side segments: the
  top arc `I₂` misses `π[M]`, T7).
* `layerCrossing_disjoint`: a layer containing a layer crossing misses `E` (commission D1.1, in the
  form: a layer of `E` projects to one point of the axis).
* `crossing_from_layer_translate_aux` (**D1**): a layer `d⁻¹(u)` containing `ψ[E]`, for a continuous
  `ψ : M → M` moving points less than `2ε₁` and with one middle point `ψ(x)`, `k(x) ∈ [4/11, 7/11]`,
  over `D`, misses `E` and contains a layer crossing. Boundary bumping in `ψ[k⁻¹[[0, k(x)]]]` and
  `ψ[k⁻¹[[k(x), 1]]]` from `ψ(x)`; the frontier point is not over `I₂` (misses `π[M]`), not over
  the axis (the layer misses `E`), and not over the far side (coarse monotonicity, `IsEps1.sep`).
* `crossing_descends_aux` (**D2**): a layer crossing in an interior layer `d⁻¹(v)` gives one in
  some `d⁻¹(u)`, `0 < u < v`: `hagopian76_property3_translate` gives `h` with `h[G] ⊆ d⁻¹(v)`; the
  point `h(x)`, `k(x) = 1/2`, lies over `D`; the shift `g` (`hagopian76_property3_shift`) small
  enough to keep `gh(x)` over `D`; then D1 with `ψ = g ∘ h`.
* `property3_layer_aux`: no interior layer contains a layer crossing (least element of the closed
  set of crossing parameters below `v`, against D2).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## Elevenths -/

theorem exists_eleventh_le {t : ℝ} (ht0 : 0 ≤ t) {m : ℕ} (hm1 : 1 ≤ m) (hm : t ≤ m / 11) :
    ∃ i : ℕ, i ≤ m ∧ ((i : ℝ) - 1) / 11 ≤ t ∧ t ≤ (i : ℝ) / 11 := by
  rcases Nat.eq_zero_or_pos ⌈11 * t⌉₊ with h | h
  · refine ⟨1, hm1, by norm_num; exact ht0, ?_⟩
    have := Nat.ceil_eq_zero.1 h
    norm_num; linarith
  · refine ⟨⌈11 * t⌉₊, Nat.ceil_le.2 (by linarith), ?_, ?_⟩
    · have := Nat.ceil_lt_add_one (show 0 ≤ 11 * t by linarith)
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 11)]; linarith
    · have := Nat.le_ceil (11 * t)
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 11)]; linarith

theorem exists_eleventh_ge {t : ℝ} (ht1 : t ≤ 1) {m : ℕ} (hm : (m : ℝ) / 11 < t) :
    ∃ j : ℕ, m + 1 ≤ j ∧ j ≤ 11 ∧ ((j : ℝ) - 1) / 11 ≤ t ∧ t ≤ (j : ℝ) / 11 := by
  have hm' : (m : ℝ) < 11 * t := by
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 11)] at hm; linarith
  refine ⟨⌈11 * t⌉₊, Nat.lt_ceil.2 hm', Nat.ceil_le.2 (by push_cast; linarith), ?_, ?_⟩
  · have := Nat.ceil_lt_add_one (show 0 ≤ 11 * t by linarith [Nat.cast_nonneg (α := ℝ) m])
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 11)]; linarith
  · have := Nat.le_ceil (11 * t)
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 11)]; linarith

variable {M : Set Pt}

/-- **Coarse separation** (`IsEps1.sep`): points of `E` whose parameters are separated by a gap of
one eleventh lie in pieces two apart, so at distance `≥ 4ε₁`. -/
theorem IsEps1.sep_of_gap {E : Set M} {k : E → unitInterval} {ε₁ : ℝ} (he : IsEps1 k ε₁)
    {m : ℕ} (hm1 : 1 ≤ m) {x y : E} (hx : (k x : ℝ) ≤ m / 11) (hy : ((m : ℝ) + 1) / 11 < k y) :
    4 * ε₁ ≤ dist (x : M) (y : M) := by
  obtain ⟨i, hi, hi1, hi2⟩ := exists_eleventh_le (k x).2.1 hm1 hx
  obtain ⟨j, hj, hj11, hj1, hj2⟩ := exists_eleventh_ge (k y).2.2 (m := m + 1) (by push_cast; exact hy)
  exact he.sep i j (by omega) hj11 _ ⟨x, ⟨hi1, hi2⟩, rfl⟩ _ ⟨y, ⟨hj1, hj2⟩, rfl⟩

/-- The collar image of a compact subset of the closed rectangle is compact. -/
theorem isCompact_collar_image {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hSR : S ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :
    IsCompact (F '' S) := by
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_restrict.2 hF.1.continuous
  exact hS.image_of_continuousOn (hFc.mono hSR)

theorem rect_sub {a b c : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hc : c ≤ 1) :
    Icc a b ×ˢ Icc 0 c ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun z ⟨⟨h1, h2⟩, h3, h4⟩ =>
  ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-! ## Layers of an extension meeting `E` -/

section Layers

variable [CompactSpace M] [ConnectedSpace M]

/-- A layer of an extension `G` of `E` (away from `k⁻¹(0)`) that meets `E` is a layer of `E`: all
its points lie in `E`, with the same parameter. -/
theorem layer_mem_E_same (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G) (hX0 : layer d 0 = layer k 0) {u : unitInterval}
    {e : E} (heu : (e : M) ∈ layer d u) {q : M} (hq : q ∈ layer d u) :
    ∃ w : E, (w : M) = q ∧ k w = k e := by
  obtain ⟨-, -, -, hlay⟩ := hagopian76_initial_segment hX hi hE hG hEG hX0
  obtain ⟨u₁, hu₁⟩ := hlay (k e)
  have he1 : (e : M) ∈ layer k (k e) := ⟨e, rfl, rfl⟩
  rw [hu₁] at he1
  have := layer_param_eq he1 heu
  subst this
  rw [← hu₁] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  exact ⟨w, rfl, hw⟩

end Layers

/-! ## Hagopian's domain and layer crossings -/

/-- **Hagopian's domain `D = F[D′]`** over `[3/22, 19/22]`, of height `c₁`, with the properties the
descent uses: `D′` lies in the open strip `(3/22, 19/22) × (0, c₁)`, `F[D′]` is open, and the
frontier of `F[D′]` meets `π[M]` only over the axis and over the two closed side segments (the top
arc `I₂` misses `π[M]`, T7). `isCrossRegion_of_D` derives it from the output of `hagopian76_D`. -/
structure IsCrossRegion (M : Set Pt) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (c₁ : ℝ)
    (D' : Set (ℝ × ℝ)) : Prop where
  sub : D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c₁
  isOpen : IsOpen (F '' D')
  frontier_sub : frontier (F '' D') ∩ π '' M ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
    F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)

/-- **A layer crossing** in the layer `d⁻¹(u)`: a connected subset of the layer lying over the
closure of `D = F[D′]` and meeting the closed side segments over `3/22` and over `19/22` (heights in
`[0, c₁]`). Commission 173 §1: the set `T` is defined by continua with closed properties. -/
def LayerCrossing {G : Set M} (d : G → unitInterval) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (c₁ : ℝ)
    (D' : Set (ℝ × ℝ)) (u : unitInterval) : Prop :=
  ∃ Z : Set M, IsPreconnected Z ∧ Z ⊆ layer d u ∧ (∀ z ∈ Z, π (z : Pt) ∈ closure (F '' D')) ∧
    (∃ z ∈ Z, π (z : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) ∧
    (∃ z ∈ Z, π (z : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁))

theorem isClosed_layer {G : Set M} {d : G → unitInterval} (hG : IsCompact G) (hd : Continuous d)
    (u : unitInterval) : IsClosed (layer d u) :=
  (isCompact_img hG hd isClosed_singleton).isClosed

/-- **The set of crossing parameters is closed** (`crossing_set_closed`). -/
theorem isClosed_layerCrossing {G : Set M} (hGc : IsCompact G) {d : G → unitInterval}
    (hd : Continuous d) {π : Pt → Pt} (hπc : Continuous π) {γ : unitInterval → Pt}
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {c₁ : ℝ} (hc₁ : c₁ ≤ 1) (D' : Set (ℝ × ℝ)) :
    IsClosed {u | LayerCrossing d π F c₁ D' u} := by
  have hA : IsClosed (π ⁻¹' (F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁))) :=
    ((isCompact_collar_image hF (isCompact_singleton.prod isCompact_Icc)
      ((Set.prod_mono (by simp) le_rfl).trans (rect_sub (a := 3 / 22) (b := 3 / 22) (by norm_num)
        (by norm_num) hc₁)))).isClosed.preimage hπc
  have hB : IsClosed (π ⁻¹' (F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁))) :=
    ((isCompact_collar_image hF (isCompact_singleton.prod isCompact_Icc)
      ((Set.prod_mono (by simp) le_rfl).trans (rect_sub (a := 19 / 22) (b := 19 / 22) (by norm_num)
        (by norm_num) hc₁)))).isClosed.preimage hπc
  have hW : IsClosed (π ⁻¹' closure (F '' D')) := isClosed_closure.preimage hπc
  convert crossing_set_closed hGc hd hA hB hW using 1
  ext u
  simp only [mem_setOf_eq, LayerCrossing]
  constructor
  · rintro ⟨Z, hZc, hZl, hZW, ⟨a, haZ, haA⟩, ⟨b, hbZ, hbB⟩⟩
    have hZG : Z ⊆ G := fun z hz => by obtain ⟨y, -, hy⟩ := hZl hz; exact hy ▸ y.2
    have himg : (Subtype.val : G → M) '' (Subtype.val ⁻¹' Z) = Z := by
      rw [Subtype.image_preimage_coe]; exact inter_eq_right.2 hZG
    refine ⟨Subtype.val ⁻¹' Z, ?_, fun z hz => ?_, fun z hz => hZW _ hz, ?_, ?_⟩
    · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]; exact hZc
    · obtain ⟨y, hy, hyz⟩ := hZl hz
      have : y = z := Subtype.ext hyz
      subst this; exact hy
    · exact ⟨⟨a, hZG haZ⟩, haZ, haA⟩
    · exact ⟨⟨b, hZG hbZ⟩, hbZ, hbB⟩
  · rintro ⟨Z, hZc, hZd, hZW, ⟨a, haZ, haA⟩, ⟨b, hbZ, hbB⟩⟩
    refine ⟨Subtype.val '' Z, hZc.image _ continuous_subtype_val.continuousOn, ?_, ?_,
      ⟨a, ⟨a, haZ, rfl⟩, haA⟩, ⟨b, ⟨b, hbZ, rfl⟩, hbB⟩⟩
    · rintro _ ⟨z, hz, rfl⟩; exact ⟨z, hZd hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩; exact hZW z hz

section Crossing

variable [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- A point of `M` over the axis `F[[0, 1] × {0}]` lies in `E`. -/
theorem mem_E_of_axis {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {q : M} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hq : π (q : Pt) = F (t, 0)) : q ∈ E := by
  obtain ⟨w, hw, -⟩ := mem_layer_of_pi_eq_gamma (t := ⟨t, ht⟩) hE hπS hγπ
    (hq.trans (hF.2.1 ⟨t, ht⟩))
  exact hw ▸ w.2

omit [CompactSpace M] [ConnectedSpace M] in
/-- The image of a point of `E` under `π` is `F(k(e), 0)`. -/
theorem pi_E_eq {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) (e : E) :
    π ((e : M) : Pt) = F ((k e : ℝ), 0) := by
  rw [hγπ (k e) _ ⟨(e : M), ⟨e, rfl, rfl⟩, rfl⟩, hF.2.1 (k e)]

/-- **A layer containing a layer crossing misses `E`** (commission D1.1). A layer of `G` meeting
`E` is a layer of `E` (`layer_mem_E_same`), which projects to the single point `F(t, 0)` of the
axis; it cannot meet both side segments. -/
theorem layerCrossing_disjoint (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} {u : unitInterval}
    (hu : LayerCrossing d π F c₁ D' u) : Disjoint (layer d u) E := by
  obtain ⟨Z, -, hZl, -, ⟨za, hza, hzaA⟩, ⟨zb, hzb, hzbB⟩⟩ := hu
  rw [disjoint_left]
  intro e' he'u he'E
  obtain ⟨wa, rfl, hwa⟩ := layer_mem_E_same hX hi hE hG hEG hX0 (e := ⟨e', he'E⟩) he'u (hZl hza)
  obtain ⟨wb, rfl, hwb⟩ := layer_mem_E_same hX hi hE hG hEG hX0 (e := ⟨e', he'E⟩) he'u (hZl hzb)
  obtain ⟨⟨a', w₁⟩, ⟨ha', hw₁⟩, hFa⟩ := hzaA
  obtain ⟨⟨b', w₂⟩, ⟨hb', hw₂⟩, hFb⟩ := hzbB
  simp only [mem_singleton_iff] at ha' hb'
  subst ha' hb'
  have hka := collar_injOn hF ⟨⟨(k wa).2.1, (k wa).2.2⟩, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num⟩, by linarith [hw₁.1], by linarith [hw₁.2]⟩
    ((pi_E_eq hγπ hF wa).symm.trans hFa.symm)
  have hkb := collar_injOn hF ⟨⟨(k wb).2.1, (k wb).2.2⟩, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num⟩, by linarith [hw₂.1], by linarith [hw₂.2]⟩
    ((pi_E_eq hγπ hF wb).symm.trans hFb.symm)
  have h1 : (k wa : ℝ) = 3 / 22 := congrArg Prod.fst hka
  have h2 : (k wb : ℝ) = 19 / 22 := congrArg Prod.fst hkb
  rw [hwa] at h1; rw [hwb] at h2
  linarith

/-- **D1 (crossing from a translate in a layer)**, commission 173 §1. There is a height `c > 0` such
that for every domain `D = F[D′]` of height `c₁ ≤ c` (`IsCrossRegion`), every continuous
`ψ : M → M` moving points less than `2ε₁`, every layer `d⁻¹(u)` of `G` containing `ψ[E]`, and every
`x ∈ E` with `k(x) ∈ [4/11, 7/11]` and `ψ(x)` over `D`: the layer misses `E` and contains a layer
crossing. -/
theorem crossing_from_layer_translate_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G) (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ ψ : M → M, Continuous ψ → (∀ v, dist v (ψ v) < 2 * ε₁) →
      ∀ u : unitInterval, ψ '' E ⊆ layer d u →
      ∀ x : E, 4 / 11 ≤ (k x : ℝ) → (k x : ℝ) ≤ 7 / 11 → π (ψ x : Pt) ∈ F '' D' →
      Disjoint (layer d u) E ∧ LayerCrossing d π F c₁ D' u := by
  have hε := he.pos
  set η := min ε₁ (1 / 22) with hη
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε₁ := min_le_left _ _
  have hη22 : η ≤ 1 / 22 := min_le_right _ _
  obtain ⟨c, hc, hc1, hthin⟩ := pi_thin_near_layer hE hπc hπS hγπ hF (a := 3 / 22) (b := 19 / 22)
    (by norm_num) (by norm_num) hη0
  refine ⟨c, hc, hc1, fun c₁ D' hc₁ hR ψ hψc hψ u hψu x hx1 hx2 hψx => ?_⟩
  have hnear : ∀ (q : M) (z : ℝ × ℝ), z ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁ →
      π (q : Pt) = F z →
      ∃ e : E, (k e : ℝ) ∈ Icc (3 / 22 : ℝ) (19 / 22) ∧ |(k e : ℝ) - z.1| < η ∧
        dist q (e : M) < η := by
    intro q z hz hqz
    obtain ⟨e, he1, he2, he3⟩ :=
      hthin q z ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩ hqz
    exact ⟨e, he1, he2, by rw [Subtype.dist_eq]; exact he3⟩
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  obtain ⟨y₀, hy₀⟩ := hE.2.1.2.1 0
  obtain ⟨y₁, hy₁⟩ := hE.2.1.2.1 1
  have hk₀ : (k y₀ : ℝ) = 0 := by rw [hy₀]; rfl
  have hk₁ : (k y₁ : ℝ) = 1 := by rw [hy₁]; rfl
  /- (1) The layer misses `E`. -/
  have hdisj : Disjoint (layer d u) E := by
    rw [disjoint_left]
    intro e' he'u he'E
    obtain ⟨w₀, hw₀, hkw₀⟩ := layer_mem_E_same hX hi hE hG hEG hX0 (e := ⟨e', he'E⟩) he'u
      (hψu (mem_image_of_mem ψ y₀.2))
    obtain ⟨w₁, hw₁, hkw₁⟩ := layer_mem_E_same hX hi hE hG hEG hX0 (e := ⟨e', he'E⟩) he'u
      (hψu (mem_image_of_mem ψ y₁.2))
    by_cases ht : (3 / 22 : ℝ) ≤ (k ⟨e', he'E⟩ : ℝ)
    · have := hend.1 (y₀ : M) ⟨y₀, by show (k y₀ : ℝ) ≤ 2 / 22; rw [hk₀]; norm_num, rfl⟩ (w₀ : M)
        ⟨w₀, by show (3 / 22 : ℝ) ≤ (k w₀ : ℝ); rw [hkw₀]; exact ht, rfl⟩
      rw [hw₀] at this
      linarith [hψ y₀]
    · push_neg at ht
      have := hend.2 (y₁ : M) ⟨y₁, by show (20 / 22 : ℝ) ≤ (k y₁ : ℝ); rw [hk₁]; norm_num, rfl⟩
        (w₁ : M) ⟨w₁, by show (k w₁ : ℝ) ≤ 19 / 22; rw [hkw₁]; linarith, rfl⟩
      rw [hw₁] at this
      linarith [hψ y₁]
  /- The open set over `D`. -/
  set O : Set M := {m | π (m : Pt) ∈ F '' D'} with hOdef
  have hOo : IsOpen O := hR.isOpen.preimage (hπc.comp continuous_subtype_val)
  have hclO : ∀ C ⊆ O, closure C ⊆ {m : M | π (m : Pt) ∈ closure (F '' D')} := fun C hC =>
    closure_minimal (fun m hm => subset_closure (hC hm))
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))
  have hfr : ∀ q : M, π (q : Pt) ∈ closure (F '' D') → q ∉ O →
      (∃ t ∈ Icc (3 / 22 : ℝ) (19 / 22), π (q : Pt) = F (t, 0)) ∨
      (∃ w ∈ Icc 0 c₁, π (q : Pt) = F (3 / 22, w)) ∨
      (∃ w ∈ Icc 0 c₁, π (q : Pt) = F (19 / 22, w)) := by
    intro q hq hqO
    have hfront : π (q : Pt) ∈ frontier (F '' D') := by
      rw [hR.isOpen.frontier_eq]; exact ⟨hq, hqO⟩
    rcases hR.frontier_sub ⟨hfront, ⟨q, q.2, rfl⟩⟩ with
      (⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩ | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩) | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩
    · simp only [mem_singleton_iff] at hz2
      subst hz2
      exact Or.inl ⟨z₁, hz1, hFz.symm⟩
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      exact Or.inr (Or.inl ⟨z₂, hz2, hFz.symm⟩)
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      exact Or.inr (Or.inr ⟨z₂, hz2, hFz.symm⟩)
  /- Coarse monotonicity. -/
  have hnotb : ∀ y : E, (k y : ℝ) ≤ 7 / 11 → ∀ w ∈ Icc 0 c₁,
      π (ψ y : Pt) ≠ F (19 / 22, w) := by
    intro y hy w hw hq
    obtain ⟨e, -, he2, he3⟩ := hnear (ψ y) (19 / 22, w) ⟨⟨by norm_num, le_rfl⟩, hw⟩ hq
    have h2 := (abs_lt.1 he2).1
    have := he.sep_of_gap (m := 7) (by norm_num) (x := y) (y := e) (by push_cast; linarith)
      (by push_cast; linarith)
    linarith [dist_triangle (y : M) (ψ y) (e : M), hψ y]
  have hnota : ∀ y : E, 4 / 11 ≤ (k y : ℝ) → ∀ w ∈ Icc 0 c₁,
      π (ψ y : Pt) ≠ F (3 / 22, w) := by
    intro y hy w hw hq
    obtain ⟨e, -, he2, he3⟩ := hnear (ψ y) (3 / 22, w) ⟨⟨le_rfl, by norm_num⟩, hw⟩ hq
    have h2 := (abs_lt.1 he2).2
    have := he.sep_of_gap (m := 2) (by norm_num) (x := e) (y := y) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [dist_comm] at he3
    linarith [dist_triangle (e : M) (ψ y) (y : M), hψ y, dist_comm (y : M) (ψ y)]
  /- The ends are not over `D`. -/
  have hy₀O : ψ y₀ ∉ O := by
    intro hO
    obtain ⟨z, hz, hFz⟩ := hDsub hO
    obtain ⟨e, he1, -, he3⟩ := hnear (ψ y₀) z hz hFz.symm
    have := hend.1 (y₀ : M) ⟨y₀, by show (k y₀ : ℝ) ≤ 2 / 22; rw [hk₀]; norm_num, rfl⟩ (e : M)
      ⟨e, he1.1, rfl⟩
    linarith [dist_triangle (y₀ : M) (ψ y₀) (e : M), hψ y₀]
  have hy₁O : ψ y₁ ∉ O := by
    intro hO
    obtain ⟨z, hz, hFz⟩ := hDsub hO
    obtain ⟨e, he1, -, he3⟩ := hnear (ψ y₁) z hz hFz.symm
    have := hend.2 (y₁ : M) ⟨y₁, by show (20 / 22 : ℝ) ≤ (k y₁ : ℝ); rw [hk₁]; norm_num, rfl⟩
      (e : M) ⟨e, he1.2, rfl⟩
    linarith [dist_triangle (y₁ : M) (ψ y₁) (e : M), hψ y₁]
  /- Boundary bumping. -/
  have hbump : ∀ S : Set unitInterval, IsClosed S → IsPreconnected S → k x ∈ S →
      ∀ y' : E, k y' ∈ S → ψ y' ∉ O → ∃ q ∈ ψ '' layerSet k S, q ∉ O ∧
        q ∈ closure (connectedComponentIn (ψ '' layerSet k S ∩ O) (ψ x)) := by
    intro S hS hSp hxS y' hy'S hy'O
    have hZc : Fold.Q78.IsContinuum (layerSet k S) :=
      isContinuum_img hE.isCompact hE.2.1 hS hSp ⟨_, hxS⟩
    exact exists_mem_closure_component_notMem (hZc.1.image hψc)
      (hZc.2.isPreconnected.image _ hψc.continuousOn) hOo ⟨(x : M), ⟨x, hxS, rfl⟩, rfl⟩ hψx
      (fun hsub => hy'O (hsub ⟨(y' : M), ⟨y', hy'S, rfl⟩, rfl⟩))
  have hlayc := isClosed_layer hG.isCompact hG.2.1.1 u
  have hcomp : ∀ S : Set unitInterval,
      closure (connectedComponentIn (ψ '' layerSet k S ∩ O) (ψ x)) ⊆ layer d u :=
    fun S => closure_minimal ((connectedComponentIn_subset _ _).trans
      (inter_subset_left.trans ((image_mono (img_subset S)).trans hψu))) hlayc
  have hcompO : ∀ S : Set unitInterval, connectedComponentIn (ψ '' layerSet k S ∩ O) (ψ x) ⊆ O :=
    fun S => (connectedComponentIn_subset _ _).trans inter_subset_right
  have haxis : ∀ q ∈ layer d u, ∀ t ∈ Icc (3 / 22 : ℝ) (19 / 22), π (q : Pt) ≠ F (t, 0) :=
    fun q hq t ht hqt => disjoint_left.1 hdisj hq
      (mem_E_of_axis hE hπS hγπ hF ⟨by linarith [ht.1], by linarith [ht.2]⟩ hqt)
  obtain ⟨qL, ⟨_, ⟨yL, hyL, rfl⟩, rfl⟩, hqLO, hqLcl⟩ :=
    hbump (Iic (k x)) isClosed_Iic isPreconnected_Iic (mem_Iic.2 le_rfl) y₀
      (show k y₀ ≤ k x by rw [hy₀]; exact unitInterval.nonneg') hy₀O
  obtain ⟨qR, ⟨_, ⟨yR, hyR, rfl⟩, rfl⟩, hqRO, hqRcl⟩ :=
    hbump (Ici (k x)) isClosed_Ici isPreconnected_Ici (mem_Ici.2 le_rfl) y₁
      (show k x ≤ k y₁ by rw [hy₁]; exact unitInterval.le_one') hy₁O
  have hkyL : (k yL : ℝ) ≤ 7 / 11 := le_trans (Subtype.coe_le_coe.2 hyL) hx2
  have hkyR : 4 / 11 ≤ (k yR : ℝ) := le_trans hx1 (Subtype.coe_le_coe.2 hyR)
  have hqLW := hclO _ (hcompO _) hqLcl
  have hqRW := hclO _ (hcompO _) hqRcl
  have hL : ∃ w ∈ Icc 0 c₁, π (ψ yL : Pt) = F (3 / 22, w) := by
    rcases hfr _ hqLW hqLO with ⟨t, ht, h⟩ | h | ⟨w, hw, h⟩
    · exact absurd h (haxis _ (hcomp _ hqLcl) t ht)
    · exact h
    · exact absurd h (hnotb yL hkyL w hw)
  have hRt : ∃ w ∈ Icc 0 c₁, π (ψ yR : Pt) = F (19 / 22, w) := by
    rcases hfr _ hqRW hqRO with ⟨t, ht, h⟩ | ⟨w, hw, h⟩ | h
    · exact absurd h (haxis _ (hcomp _ hqRcl) t ht)
    · exact absurd h (hnota yR hkyR w hw)
    · exact h
  have hxmem : ∀ S : Set unitInterval, k x ∈ S →
      ψ x ∈ connectedComponentIn (ψ '' layerSet k S ∩ O) (ψ x) := fun S hxS =>
    mem_connectedComponentIn ⟨⟨(x : M), ⟨x, hxS, rfl⟩, rfl⟩, hψx⟩
  refine ⟨hdisj, closure (connectedComponentIn (ψ '' layerSet k (Iic (k x)) ∩ O) (ψ x)) ∪
    closure (connectedComponentIn (ψ '' layerSet k (Ici (k x)) ∩ O) (ψ x)), ?_, ?_, ?_, ?_, ?_⟩
  · exact IsPreconnected.union (ψ x) (subset_closure (hxmem (Iic (k x)) (mem_Iic.2 le_rfl)))
      (subset_closure (hxmem (Ici (k x)) (mem_Ici.2 le_rfl)))
      isPreconnected_connectedComponentIn.closure isPreconnected_connectedComponentIn.closure
  · exact union_subset (hcomp _) (hcomp _)
  · rintro z (hz | hz)
    · exact hclO _ (hcompO _) hz
    · exact hclO _ (hcompO _) hz
  · obtain ⟨w, hw, h⟩ := hL
    exact ⟨_, Or.inl hqLcl, ⟨(3 / 22, w), ⟨rfl, hw⟩, h.symm⟩⟩
  · obtain ⟨w, hw, h⟩ := hRt
    exact ⟨_, Or.inr hqRcl, ⟨(19 / 22, w), ⟨rfl, hw⟩, h.symm⟩⟩

/-- **D2 (descent)**, commission 173 §1. There is a height `c > 0` such that for every domain
`D = F[D′]` of height `c₁ ≤ c`: a layer crossing in an interior layer `d⁻¹(v)` (`0 < v < 1`) gives a
layer crossing in some `d⁻¹(u)` with `0 < u < v`. No margin is lost: D1 recreates the crossing from
the ends of the translate. -/
theorem crossing_descends_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ v : unitInterval, 0 < v → v < 1 → LayerCrossing d π F c₁ D' v →
      ∃ u : unitInterval, 0 < u ∧ u < v ∧ LayerCrossing d π F c₁ D' u := by
  have hε := he.pos
  have hπc := hπ.continuous
  set η := min ε₁ (1 / 22) with hη
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε₁ := min_le_left _ _
  have hη22 : η ≤ 1 / 22 := min_le_right _ _
  obtain ⟨cP, hcP, hcP1, hP⟩ := hagopian76_property3_translate hX hi hE he hend hπ hπS hγπ hF
    hLch hEL hLG hP1 hG hEG hX0
  obtain ⟨cD, hcD, hcD1, hD1⟩ := crossing_from_layer_translate_aux hX hi hE he hend hπc hπS hγπ hF
    hG hEG hX0
  obtain ⟨cT, hcT, hcT1, hthin⟩ := pi_thin_near_layer hE hπc hπS hγπ hF (a := 3 / 22)
    (b := 19 / 22) (by norm_num) (by norm_num) hη0
  refine ⟨min cP (min cD cT), lt_min hcP (lt_min hcD hcT), (min_le_left _ _).trans hcP1,
    fun c₁ D' hc₁ hR v hv0 hv1 hv => ?_⟩
  have hc₁P : c₁ ≤ cP := hc₁.trans (min_le_left _ _)
  have hc₁D : c₁ ≤ cD := hc₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc₁T : c₁ ≤ cT := hc₁.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc₁1 : c₁ ≤ 1 := hc₁P.trans hcP1
  have hdisj := layerCrossing_disjoint hX hi hE hγπ hF hG hEG hX0 hc₁1 hv
  obtain ⟨Z, hZc, hZl, hZW, ⟨za, hza, hzaA⟩, ⟨zb, hzb, hzbB⟩⟩ := hv
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  have hclD : closure (F '' D') ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    closure_minimal hDsub (isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc)
      (rect_sub (by norm_num) (by norm_num) hc₁1)).isClosed
  have hlayc := isClosed_layer hG.isCompact hG.2.1.1 v
  have hWc : IsClosed {m : M | π (m : Pt) ∈ closure (F '' D')} :=
    isClosed_closure.preimage (hπc.comp continuous_subtype_val)
  have hBl : closure Z ⊆ layer d v := closure_minimal hZl hlayc
  have hBW : closure Z ⊆ {m : M | π (m : Pt) ∈ closure (F '' D')} := closure_minimal hZW hWc
  /- Heights: points of the layer over the closed strip are off the axis. -/
  have hpos : ∀ q ∈ layer d v, ∀ z ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁,
      π (q : Pt) = F z → 0 < z.2 := by
    rintro q hq ⟨z₁, z₂⟩ ⟨hz1, hz2⟩ hqz
    rcases hz2.1.lt_or_eq with h | h
    · exact h
    · exfalso
      simp only at h
      subst h
      exact disjoint_left.1 hdisj hq
        (mem_E_of_axis hE hπS hγπ hF ⟨by linarith [hz1.1], by linarith [hz1.2]⟩ hqz)
  /- (a) `Cl Z` is a crossing in the form of `hagopian76_property3_translate`. -/
  have hstrip : ∀ x ∈ closure Z, π (x : Pt) ∈ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Ioc 0 cP) := by
    intro x hx
    obtain ⟨z, hz, hFz⟩ := hclD (hBW hx)
    exact ⟨z, ⟨hz.1, hpos x (hBl hx) z hz hFz.symm, hz.2.2.trans hc₁P⟩, hFz⟩
  have hside : ∀ {a' : ℝ}, a' ∈ Icc (3 / 22 : ℝ) (19 / 22) → ∀ q ∈ Z,
      π (q : Pt) ∈ F '' (({a'} : Set ℝ) ×ˢ Icc 0 c₁) →
      π (q : Pt) ∈ F '' (({a'} : Set ℝ) ×ˢ Ioc 0 cP) := by
    rintro a' ha' q hq ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩
    simp only [mem_singleton_iff] at hz1
    subst hz1
    have := hpos q (hZl hq) (z₁, z₂) ⟨ha', hz2⟩ hFz.symm
    exact ⟨(z₁, z₂), ⟨rfl, this, hz2.2.trans hc₁P⟩, hFz⟩
  obtain ⟨-, h, hh, hmid, hhG⟩ := hP (closure Z) hZc.closure hstrip
    ⟨za, subset_closure (subset_closure hza),
      hside ⟨le_rfl, by norm_num⟩ za hza hzaA⟩
    ⟨zb, subset_closure (subset_closure hzb),
      hside ⟨by norm_num, le_rfl⟩ zb hzb hzbB⟩ v hv0 hv1 (by rw [closure_closure]; exact hBl)
  /- (b) The point `p = h(x)`, `k(x) = 1/2`, lies over `D`. -/
  obtain ⟨x, hx⟩ := hE.2.1.2.1 ⟨1 / 2, by norm_num, by norm_num⟩
  have hkx : (k x : ℝ) = 1 / 2 := by rw [hx]
  have hpB : h x ∈ closure Z := by
    have := hmid ⟨(x : M), ⟨x, show (4 / 11 : ℝ) < (k x : ℝ) ∧ (k x : ℝ) < 7 / 11 by
      rw [hkx]; norm_num, rfl⟩, rfl⟩
    rwa [closure_closure] at this
  have hnear : ∀ (q : M) (z : ℝ × ℝ), z ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁ →
      π (q : Pt) = F z → ∃ e : E, |(k e : ℝ) - z.1| < η ∧ dist q (e : M) < η := by
    intro q z hz hqz
    obtain ⟨e, -, he2, he3⟩ :=
      hthin q z ⟨hz.1, by linarith [hz.2.1, hc₁T], by linarith [hz.2.2, hc₁T]⟩ hqz
    exact ⟨e, he2, by rw [Subtype.dist_eq]; exact he3⟩
  have hpO : π (h x : Pt) ∈ F '' D' := by
    by_contra hpO
    have hfront : π (h x : Pt) ∈ frontier (F '' D') := by
      rw [hR.isOpen.frontier_eq]; exact ⟨hBW hpB, hpO⟩
    have hhx := hh x
    rcases hR.frontier_sub ⟨hfront, ⟨_, (h x).2, rfl⟩⟩ with
      (⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩ | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩) | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩
    · simp only [mem_singleton_iff] at hz2
      subst hz2
      exact disjoint_left.1 hdisj (hBl hpB)
        (mem_E_of_axis hE hπS hγπ hF ⟨by linarith [hz1.1], by linarith [hz1.2]⟩ hFz.symm)
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      obtain ⟨e, he2, he3⟩ := hnear (h x) (3 / 22, z₂) ⟨⟨le_rfl, by norm_num⟩, hz2⟩ hFz.symm
      have h2 := (abs_lt.1 he2).2
      have := he.sep_of_gap (m := 2) (by norm_num) (x := e) (y := x) (by push_cast; linarith)
        (by push_cast; rw [hkx]; norm_num)
      linarith [dist_triangle (e : M) (h x) (x : M), dist_comm (e : M) (h x),
        dist_comm (x : M) (h x)]
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      obtain ⟨e, he2, he3⟩ := hnear (h x) (19 / 22, z₂) ⟨⟨by norm_num, le_rfl⟩, hz2⟩ hFz.symm
      have h2 := (abs_lt.1 he2).1
      have hx7 : (k x : ℝ) ≤ ((7 : ℕ) : ℝ) / 11 := by rw [hkx]; norm_num
      have := he.sep_of_gap (m := 7) (by norm_num) (x := x) (y := e) hx7 (by push_cast; linarith)
      linarith [dist_triangle (x : M) (h x) (e : M)]
  /- (c) The shift. -/
  have hOo : IsOpen {m : M | π (m : Pt) ∈ F '' D'} :=
    hR.isOpen.preimage (hπc.comp continuous_subtype_val)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hOo (h x) hpO
  obtain ⟨u, hu0, huv, g, hg, hgv⟩ := hagopian76_property3_shift hX hi hG hv0 hv1
    (lt_min hδ₀ hε : 0 < min δ₀ ε₁)
  refine ⟨u, hu0, huv, ?_⟩
  have hψc : Continuous (fun m => g (h m)) := g.continuous.comp h.continuous
  have hψ : ∀ m : M, dist m (g (h m)) < 2 * ε₁ := fun m => by
    linarith [dist_triangle m (h m) (g (h m)), hh m, hg (h m), min_le_right δ₀ ε₁]
  have hψu : (fun m => g (h m)) '' E ⊆ layer d u := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← hgv]
    exact ⟨h m, hhG ⟨m, hEG hm, rfl⟩, rfl⟩
  have hψx : π (g (h x) : Pt) ∈ F '' D' := by
    have : g (h x) ∈ ball (h x) δ₀ := by
      rw [mem_ball, dist_comm]
      exact lt_of_lt_of_le (hg (h x)) (min_le_left _ _)
    exact hball this
  exact (hD1 c₁ D' hc₁D hR (fun m => g (h m)) hψc hψ u hψu x (by rw [hkx]; norm_num)
    (by rw [hkx]; norm_num) hψx).2

/-- **No interior layer contains a layer crossing** (commission 173 §1, the least element of a
closed set). The crossing parameters below `v` form a closed set (`isClosed_layerCrossing`); its
least element `u` is positive (the layer `d⁻¹(0) = k⁻¹(0)` lies in `E`, while a layer containing a
crossing misses `E`), and D2 gives a smaller element. -/
theorem property3_layer_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ v : unitInterval, v < 1 → ¬ LayerCrossing d π F c₁ D' v := by
  obtain ⟨c, hc, hc1, hD2⟩ := crossing_descends_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG
    hP1 hG hEG hX0
  refine ⟨c, hc, hc1, fun c₁ D' hc₁ hR v hv1 hv => ?_⟩
  have hc₁1 : c₁ ≤ 1 := hc₁.trans hc1
  set T := {u | LayerCrossing d π F c₁ D' u} ∩ Iic v with hT
  have hTc : IsClosed T :=
    (isClosed_layerCrossing hG.isCompact hG.2.1.1 hπ.continuous hF hc₁1 D').inter isClosed_Iic
  obtain ⟨u, ⟨huT, huv⟩, hleast⟩ := hTc.isCompact.exists_isLeast ⟨v, hv, mem_Iic.2 le_rfl⟩
  have hu0 : 0 < u := by
    rcases eq_or_lt_of_le (unitInterval.nonneg' : (0 : unitInterval) ≤ u) with h | h
    · exfalso
      have hdisj := layerCrossing_disjoint hX hi hE hγπ hF hG hEG hX0 hc₁1 huT
      rw [← h, hX0] at hdisj
      obtain ⟨e, he⟩ := layer_nonempty hE.2.1.2.1 0
      exact disjoint_left.1 hdisj he (by obtain ⟨y, -, rfl⟩ := he; exact y.2)
    · exact h
  obtain ⟨u', -, hu'u, hu'⟩ := hD2 c₁ D' hc₁ hR u hu0 (lt_of_le_of_lt huv hv1) huT
  exact absurd (hleast ⟨hu', hu'u.le.trans huv⟩) (not_le.2 hu'u)

end Crossing

end HPC.Hagopian

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Length

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Crossings need parameter length** (toward "It follows from Property 3 that `I` is finite",
p. 347). Below any `v₀ < 1`, a connected set inside `d⁻¹[[x, y]]` lying over `Cl D` and meeting both
closed side segments has `y − x ≥ λ` for a fixed `λ > 0`. *Proof:* otherwise the upper limit of a
sequence with `y − x → 0` is a layer crossing in a layer `d⁻¹(u)`, `u ≤ v₀ < 1`
(`limsup_isPreconnected`), against `property3_layer_aux`. -/
theorem crossing_length_pos_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ v₀ : unitInterval, v₀ < 1 → ∃ lam > 0, ∀ (x y : unitInterval) (Z : Set M), y ≤ v₀ →
      IsPreconnected Z → Z ⊆ layerSet d (Icc x y) →
      (∀ z ∈ Z, π (z : Pt) ∈ closure (F '' D')) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      lam ≤ (y : ℝ) - x := by
  obtain ⟨c, hc, hc1, hP3⟩ := property3_layer_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
    hG hEG hX0
  refine ⟨c, hc, hc1, fun c₁ D' hc₁ hR v₀ hv₀ => ?_⟩
  have hc₁1 : c₁ ≤ 1 := hc₁.trans hc1
  have hπc := hπ.continuous
  by_contra hcon
  push_neg at hcon
  choose x y Z hyv hZc hZl hZW hZa hZb hlen using fun n : ℕ => hcon (1 / ((n : ℝ) + 1))
    (by positivity)
  choose a haZ haA using hZa
  choose b hbZ hbB using hZb
  obtain ⟨⟨u, p⟩, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq
    (x := fun n => (x n, a n)) (fun _ => mem_univ _)
  have hxu : Tendsto (fun n => x (φ n)) atTop (𝓝 u) := (continuous_fst.tendsto _).comp hlim
  have hap : Tendsto (fun n => a (φ n)) atTop (𝓝 p) := (continuous_snd.tendsto _).comp hlim
  have hxy : ∀ n, x n ≤ y n := fun n => by
    obtain ⟨w, hw, -⟩ := hZl n (haZ n)
    exact hw.1.trans hw.2
  have hlen0 : Tendsto (fun n => ((y (φ n) : ℝ) - x (φ n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    refine squeeze_zero (fun n => ?_) (fun n => (hlen (φ n)).le) h1
    have := hxy (φ n)
    exact sub_nonneg.2 (Subtype.coe_le_coe.2 this)
  set Lim := ⋂ N, closure (⋃ m ≥ N, Z (φ m)) with hLim
  have hGc : IsClosed G := hG.isCompact.isClosed
  have hband : ∀ ε > 0, ∀ᶠ n in atTop, Z (φ n) ⊆ layerSet d {t | dist t u ≤ ε} := by
    intro ε hε
    have h1 := (Metric.tendsto_nhds.1 hxu) (ε / 2) (by linarith)
    have h2 := (Metric.tendsto_nhds.1 hlen0) (ε / 2) (by linarith)
    filter_upwards [h1, h2] with n hn1 hn2
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hZl _ hz
    refine ⟨w, ?_, rfl⟩
    show dist (d w) u ≤ ε
    rw [Real.dist_eq, abs_lt] at hn2
    have hd1 : dist (d w) u ≤ dist (d w) (x (φ n)) + dist (x (φ n)) u := dist_triangle _ _ _
    have hd2 : dist (d w) (x (φ n)) ≤ (y (φ n) : ℝ) - x (φ n) := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith [Subtype.coe_le_coe.2 hw.1])]
      linarith [Subtype.coe_le_coe.2 hw.2]
    linarith [hn1.le]
  have hLimL : Lim ⊆ layer d u := by
    intro z hz
    have hzG : z ∈ G := by
      refine limsup_subset_of_eventually hGc (Eventually.of_forall fun n => ?_) hz
      intro w hw
      obtain ⟨w', -, rfl⟩ := hZl _ hw
      exact w'.2
    refine ⟨⟨z, hzG⟩, ?_, rfl⟩
    refine mem_singleton_iff.2 (eq_of_forall_dist_le fun ε hε => ?_)
    have := limsup_subset_of_eventually (isCompact_img hG.isCompact hG.2.1.1
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)).isClosed
      (hband ε hε) hz
    obtain ⟨w, hw, hwz⟩ := this
    have : w = ⟨z, hzG⟩ := Subtype.ext hwz
    subst this
    exact hw
  have huv : u ≤ v₀ := (isClosed_Iic : IsClosed (Iic v₀)).mem_of_tendsto hxu
    (Eventually.of_forall fun n => (hxy (φ n)).trans (hyv (φ n)))
  have hA : IsClosed {m : M | π (m : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)} :=
    (isCompact_collar_image hF (isCompact_singleton.prod isCompact_Icc)
      ((Set.prod_mono (by simp) le_rfl).trans (rect_sub (a := 3 / 22) (b := 3 / 22)
        (by norm_num) (by norm_num) hc₁1))).isClosed.preimage
      (hπc.comp continuous_subtype_val)
  obtain ⟨⟨q, q'⟩, -, ψ, hψ, hlim2⟩ := isCompact_univ.tendsto_subseq
    (x := fun n => (b (φ n), a (φ n))) (fun _ => mem_univ _)
  have hbq : Tendsto (fun n => b (φ (ψ n))) atTop (𝓝 q) := (continuous_fst.tendsto _).comp hlim2
  refine hP3 c₁ D' hc₁ hR u (lt_of_le_of_lt huv hv₀) ⟨Lim, ?_, hLimL, ?_, ⟨p, ?_, ?_⟩, ⟨q, ?_, ?_⟩⟩
  · exact limsup_isPreconnected (fun n => hZc (φ n)) (fun n => haZ (φ n)) hap
  · exact fun z hz => limsup_subset_of_eventually
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))
      (Eventually.of_forall fun n => fun w hw => hZW _ w hw) hz
  · exact limsup_mem_of_tendsto (fun n => haZ (φ n)) hap
  · exact hA.mem_of_tendsto hap (Eventually.of_forall fun n => haA (φ n))
  · have hsub : ⋂ N, closure (⋃ m ≥ N, Z (φ (ψ m))) ⊆ Lim := by
      refine subset_iInter fun N => ?_
      refine (iInter_subset _ N).trans (closure_mono (iUnion₂_subset fun m hm => ?_))
      exact subset_biUnion_of_mem (u := fun i => Z (φ i)) (le_trans hm (hψ.id_le m))
    exact hsub (limsup_mem_of_tendsto (fun n => hbZ (φ (ψ n))) hbq)
  · have hB : IsClosed {m : M | π (m : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)} :=
      (isCompact_collar_image hF (isCompact_singleton.prod isCompact_Icc)
        ((Set.prod_mono (by simp) le_rfl).trans (rect_sub (a := 19 / 22) (b := 19 / 22)
          (by norm_num) (by norm_num) hc₁1))).isClosed.preimage
        (hπc.comp continuous_subtype_val)
    exact hB.mem_of_tendsto hbq (Eventually.of_forall fun n => hbB (φ (ψ n)))

end Length

end HPC.Hagopian
