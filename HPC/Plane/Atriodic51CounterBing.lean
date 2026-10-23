import HPC.Plane.Atriodic51Counter

/-!
# Batch 92: the example `S₀` satisfies Bing's standing hypothesis

`S₀` (`HPC/Plane/Atriodic51Counter.lean`) is a nondegenerate continuum which is atriodic,
hereditarily unicoherent and hereditarily decomposable (`bingS_S₀`). Together with
`not_partition_S₀` this refutes the partition clause of `theorem8_1951`
(the one-layer reading of Bing's Theorem 8; Bing's own statement is `theorem8_1951'`)
(`theorem8_1951_false`).

The proof goes through one closure property `Crit` of subsets of `S₀`, phrased with the height
`z.1.2` and the abscissa `z.1.1` of a point:
* every point at a nonzero height between two heights of `W` lies in `W` (a point of `S₀` is
  determined by its height when that height is nonzero);
* if `W` has heights `≤ 0` and `≥ 0`, it meets the bar `B = [0,2] × {0}`;
* `W ∩ B` is convex;
* if `W` has a height `≤ 0` and a height `> 0`, then `W ⊇ [0,1] × {0}`;
  if `W` has a height `≥ 0` and a height `< 0`, then `W ⊇ [1,2] × {0}`.
Every subcontinuum has `Crit` (`crit_of`), `Crit` is closed under intersection (`Crit.inter`),
and every set with `Crit` is connected (`Crit.isPreconnected`). Hereditary unicoherence and
hereditary decomposability follow at once; atriodicity is a pigeonhole argument
(`not_isTriod`).
-/

namespace HPC.Plane.Counter92

open Set Topology Metric

/-! ## Points of `S₀` -/

lemma S₀_cases (z : S₀) : (0 < z.1.2 ∧ z.1.2 ≤ 1 ∧ z.1.1 = cA z.1.2) ∨
    (z.1.2 = 0 ∧ 0 ≤ z.1.1 ∧ z.1.1 ≤ 2) ∨
    (-1 ≤ z.1.2 ∧ z.1.2 < 0 ∧ z.1.1 = 1 + cA (-z.1.2)) := z.2

lemma x_nonneg (z : S₀) : 0 ≤ z.1.1 := by
  rcases S₀_cases z with ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
  · rw [h]; exact (cA_mem _).1
  · exact h
  · rw [h]; linarith [(cA_mem (-z.1.2)).1]

lemma x_le_two (z : S₀) : z.1.1 ≤ 2 := by
  rcases S₀_cases z with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · rw [h]; linarith [(cA_mem z.1.2).2]
  · exact h
  · rw [h]; linarith [(cA_mem (-z.1.2)).2]

lemma x_le_one_of_pos (z : S₀) (hz : 0 < z.1.2) : z.1.1 ≤ 1 := by
  rcases S₀_cases z with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
  · rw [h]; exact (cA_mem _).2
  · linarith
  · linarith

lemma one_le_x_of_neg (z : S₀) (hz : z.1.2 < 0) : 1 ≤ z.1.1 := by
  rcases S₀_cases z with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩
  · linarith
  · linarith
  · rw [h]; linarith [(cA_mem (-z.1.2)).1]

lemma hgt_ge (z : S₀) : -1 ≤ z.1.2 := by
  rcases S₀_cases z with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> linarith

lemma hgt_le (z : S₀) : z.1.2 ≤ 1 := by
  rcases S₀_cases z with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ <;> linarith

/-- A point of `S₀` at a nonzero height is determined by its height. -/
lemma eq_of_hgt {z w : S₀} (h : z.1.2 = w.1.2) (h0 : z.1.2 ≠ 0) : z = w := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · have hw : w.1.2 < 0 := h ▸ hn
    rcases S₀_cases z with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, hz⟩
    · linarith
    · linarith
    rcases S₀_cases w with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, hw'⟩
    · linarith
    · linarith
    exact Subtype.ext (Prod.ext (by rw [hz, hw', h]) h)
  · have hw : 0 < w.1.2 := h ▸ hp
    rcases S₀_cases z with ⟨-, -, hz⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩
    rotate_left
    · linarith
    · linarith
    rcases S₀_cases w with ⟨-, -, hw'⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩
    rotate_left
    · linarith
    · linarith
    exact Subtype.ext (Prod.ext (by rw [hz, hw', h]) h)

lemma eq_of_bar {z w : S₀} (hz : z.1.2 = 0) (hw : w.1.2 = 0) (hx : z.1.1 = w.1.1) : z = w :=
  Subtype.ext (Prod.ext hx (hz.trans hw.symm))

lemma exists_hgt {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) (h0 : t ≠ 0) : ∃ u : S₀, u.1.2 = t := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · exact ⟨c₂ (t := -t) (by linarith) (by linarith), by simp [c₂]⟩
  · exact ⟨c₁ hp h2, rfl⟩

/-! ## The closure property -/

/-- The closure property shared by all subcontinua of `S₀`. -/
structure Crit (W : Set S₀) : Prop where
  hgt_mem : ∀ z ∈ W, ∀ w ∈ W, ∀ u : S₀, z.1.2 ≤ u.1.2 → u.1.2 ≤ w.1.2 → u.1.2 ≠ 0 → u ∈ W
  zero_mem : ∀ z ∈ W, ∀ w ∈ W, z.1.2 ≤ 0 → 0 ≤ w.1.2 → ∃ u ∈ W, u.1.2 = 0
  bar_mem : ∀ z ∈ W, ∀ w ∈ W, ∀ u : S₀, z.1.2 = 0 → w.1.2 = 0 → u.1.2 = 0 →
    z.1.1 ≤ u.1.1 → u.1.1 ≤ w.1.1 → u ∈ W
  pos_bar : ∀ z ∈ W, ∀ w ∈ W, z.1.2 ≤ 0 → 0 < w.1.2 → ∀ u : S₀, u.1.2 = 0 → u.1.1 ≤ 1 → u ∈ W
  neg_bar : ∀ z ∈ W, ∀ w ∈ W, 0 ≤ z.1.2 → w.1.2 < 0 → ∀ u : S₀, u.1.2 = 0 → 1 ≤ u.1.1 → u ∈ W

lemma mem_of_hgt {Y : Set S₀} (hY : IsPreconnected Y) {z w u : S₀} (hz : z ∈ Y) (hw : w ∈ Y)
    (h1 : z.1.2 ≤ u.1.2) (h2 : u.1.2 ≤ w.1.2) (h0 : u.1.2 ≠ 0) : u ∈ Y := by
  obtain ⟨v, hv, hvu⟩ := exists_height hY hz hw ⟨h1, h2⟩
  rwa [eq_of_hgt hvu (by rw [hvu]; exact h0)] at hv

lemma bar_mem_of_pos {Y : Set S₀} (hYc : IsClosed Y) (hY : IsPreconnected Y) {z w : S₀}
    (hz : z ∈ Y) (hw : w ∈ Y) (hz0 : z.1.2 ≤ 0) (hw0 : 0 < w.1.2) (u : S₀) (hu : u.1.2 = 0)
    (hu1 : u.1.1 ≤ 1) : u ∈ Y := by
  rw [← hYc.closure_eq]
  refine mem_closure_of_forall fun ε hε => ?_
  obtain ⟨t, ht0, htε, ht1, hct⟩ := exists_cA_eq (x_nonneg u) hu1 (lt_min hε hw0)
  refine ⟨c₁ ht0 ht1, mem_of_hgt hY hz hw (show z.1.2 ≤ t by linarith)
    (show t ≤ w.1.2 by linarith [htε.trans_le (min_le_right _ _)]) (show t ≠ 0 from ht0.ne'), ?_⟩
  rw [dist_S₀]
  simp only [c₁, hct, hu, dist_self, Real.dist_eq, sub_zero, abs_of_pos ht0]
  exact max_lt hε (htε.trans_le (min_le_left _ _))

lemma bar_mem_of_neg {Y : Set S₀} (hYc : IsClosed Y) (hY : IsPreconnected Y) {z w : S₀}
    (hz : z ∈ Y) (hw : w ∈ Y) (hz0 : 0 ≤ z.1.2) (hw0 : w.1.2 < 0) (u : S₀) (hu : u.1.2 = 0)
    (hu1 : 1 ≤ u.1.1) : u ∈ Y := by
  rw [← hYc.closure_eq]
  refine mem_closure_of_forall fun ε hε => ?_
  obtain ⟨t, ht0, htε, ht1, hct⟩ := exists_cA_eq (x := u.1.1 - 1) (by linarith)
    (by linarith [x_le_two u]) (lt_min hε (neg_pos.mpr hw0))
  refine ⟨c₂ ht0 ht1, mem_of_hgt hY hw hz
    (show w.1.2 ≤ -t by linarith [htε.trans_le (min_le_right _ _)])
    (show -t ≤ z.1.2 by linarith) (show -t ≠ 0 by linarith), ?_⟩
  rw [dist_S₀]
  simp only [c₂, hct, hu, Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht0]
  refine max_lt ?_ (htε.trans_le (min_le_left _ _))
  rw [show 1 + (u.1.1 - 1) - u.1.1 = 0 by ring, abs_zero]; exact hε

lemma bar_convex {Y : Set S₀} (hYc : IsClosed Y) (hY : IsPreconnected Y) {z w u : S₀}
    (hz : z ∈ Y) (hw : w ∈ Y) (hz0 : z.1.2 = 0) (hw0 : w.1.2 = 0) (hu0 : u.1.2 = 0)
    (h1 : z.1.1 ≤ u.1.1) (h2 : u.1.1 ≤ w.1.1) : u ∈ Y := by
  by_contra huY
  have hne : ∀ v ∈ Y, v.1.1 ≠ u.1.1 := by
    intro v hv hvx
    rcases lt_trichotomy v.1.2 0 with hn | h0 | hp
    · exact huY (bar_mem_of_neg hYc hY hz hv hz0.ge hn u hu0 (hvx ▸ one_le_x_of_neg v hn))
    · exact huY (by rwa [eq_of_bar h0 hu0 hvx] at hv)
    · exact huY (bar_mem_of_pos hYc hY hz hv hz0.le hp u hu0 (hvx ▸ x_le_one_of_pos v hp))
  have hc : Continuous fun v : S₀ => v.1.1 := continuous_fst.comp continuous_subtype_val
  rcases eq_or_lt_of_le h1 with e1 | l1
  · exact huY (by rwa [eq_of_bar hz0 hu0 e1] at hz)
  rcases eq_or_lt_of_le h2 with e2 | l2
  · exact huY (by rwa [← eq_of_bar hu0 hw0 e2] at hw)
  obtain ⟨v, -, hv1, hv2⟩ := hY {v | v.1.1 < u.1.1} {v | u.1.1 < v.1.1}
    (isOpen_lt hc continuous_const) (isOpen_lt continuous_const hc)
    (fun v hv => lt_or_gt_of_ne (hne v hv)) ⟨z, hz, l1⟩ ⟨w, hw, l2⟩
  exact lt_asymm (show v.1.1 < u.1.1 from hv1) (show u.1.1 < v.1.1 from hv2)

/-- Every closed connected subset of `S₀` has the closure property. -/
lemma crit_of {Y : Set S₀} (hYc : IsClosed Y) (hY : IsPreconnected Y) : Crit Y where
  hgt_mem _ hz _ hw _ h1 h2 h0 := mem_of_hgt hY hz hw h1 h2 h0
  zero_mem _ hz _ hw h1 h2 := exists_height hY hz hw ⟨h1, h2⟩
  bar_mem _ hz _ hw _ hz0 hw0 hu0 h1 h2 := bar_convex hYc hY hz hw hz0 hw0 hu0 h1 h2
  pos_bar _ hz _ hw h1 h2 u hu hu1 := bar_mem_of_pos hYc hY hz hw h1 h2 u hu hu1
  neg_bar _ hz _ hw h1 h2 u hu hu1 := bar_mem_of_neg hYc hY hz hw h1 h2 u hu hu1

lemma Crit.inter {H K : Set S₀} (hH : Crit H) (hK : Crit K) : Crit (H ∩ K) where
  hgt_mem z hz w hw u h1 h2 h0 :=
    ⟨hH.hgt_mem z hz.1 w hw.1 u h1 h2 h0, hK.hgt_mem z hz.2 w hw.2 u h1 h2 h0⟩
  zero_mem z hz w hw h1 h2 := by
    rcases eq_or_lt_of_le h1 with e | l
    · exact ⟨z, hz, e⟩
    rcases eq_or_lt_of_le h2 with e | l'
    · exact ⟨w, hw, e.symm⟩
    refine ⟨bar (x := 0) le_rfl (by norm_num), ⟨hH.pos_bar z hz.1 w hw.1 h1 l' _ rfl ?_,
      hK.pos_bar z hz.2 w hw.2 h1 l' _ rfl ?_⟩, rfl⟩ <;> simp [bar]
  bar_mem z hz w hw u hz0 hw0 hu0 h1 h2 :=
    ⟨hH.bar_mem z hz.1 w hw.1 u hz0 hw0 hu0 h1 h2, hK.bar_mem z hz.2 w hw.2 u hz0 hw0 hu0 h1 h2⟩
  pos_bar z hz w hw h1 h2 u hu hu1 :=
    ⟨hH.pos_bar z hz.1 w hw.1 h1 h2 u hu hu1, hK.pos_bar z hz.2 w hw.2 h1 h2 u hu hu1⟩
  neg_bar z hz w hw h1 h2 u hu hu1 :=
    ⟨hH.neg_bar z hz.1 w hw.1 h1 h2 u hu hu1, hK.neg_bar z hz.2 w hw.2 h1 h2 u hu hu1⟩

lemma crit_univ : Crit (univ : Set S₀) where
  hgt_mem _ _ _ _ _ _ _ _ := mem_univ _
  zero_mem _ _ _ _ _ _ := ⟨bar (x := 0) le_rfl (by norm_num), mem_univ _, rfl⟩
  bar_mem _ _ _ _ _ _ _ _ _ _ := mem_univ _
  pos_bar _ _ _ _ _ _ _ _ _ := mem_univ _
  neg_bar _ _ _ _ _ _ _ _ _ := mem_univ _

lemma crit_hgt_le (m : ℝ) : Crit {z : S₀ | z.1.2 ≤ m} where
  hgt_mem _ _ _ hw _ _ h2 _ := h2.trans hw
  zero_mem _ _ w hw _ h2 := ⟨bar (x := 0) le_rfl (by norm_num), show (0 : ℝ) ≤ m from h2.trans hw,
    rfl⟩
  bar_mem z hz _ _ _ hz0 _ hu0 _ _ := by
    show _ ≤ m; rw [hu0]; have : z.1.2 ≤ m := hz; rwa [hz0] at this
  pos_bar _ _ w hw _ h2 _ hu _ := by show _ ≤ m; rw [hu]; exact h2.le.trans hw
  neg_bar z hz _ _ h1 _ _ hu _ := by show _ ≤ m; rw [hu]; exact h1.trans hz

lemma crit_le_hgt (m : ℝ) : Crit {z : S₀ | m ≤ z.1.2} where
  hgt_mem _ hz _ _ _ h1 _ _ := le_trans hz h1
  zero_mem z hz _ _ h1 _ := ⟨bar (x := 0) le_rfl (by norm_num), show m ≤ (0 : ℝ) from hz.trans h1,
    rfl⟩
  bar_mem z hz _ _ _ hz0 _ hu0 _ _ := by
    show m ≤ _; rw [hu0]; have : m ≤ z.1.2 := hz; rwa [hz0] at this
  pos_bar z hz _ _ h1 _ _ hu _ := by show m ≤ _; rw [hu]; exact hz.trans h1
  neg_bar _ _ w hw _ h2 _ hu _ := by show m ≤ _; rw [hu]; exact hw.trans h2.le

lemma crit_bar_le (m : ℝ) : Crit {z : S₀ | z.1.2 = 0 ∧ z.1.1 ≤ m} where
  hgt_mem _ hz _ hw _ h1 h2 h0 := absurd (le_antisymm (h2.trans hw.1.le) (hz.1 ▸ h1)) h0
  zero_mem z hz _ _ _ _ := ⟨z, hz, hz.1⟩
  bar_mem _ _ _ hw _ _ _ hu0 _ h2 := ⟨hu0, h2.trans hw.2⟩
  pos_bar _ _ _ hw _ h2 _ _ _ := absurd hw.1 h2.ne'
  neg_bar _ _ _ hw _ h2 _ _ _ := absurd hw.1 h2.ne

lemma crit_le_bar (m : ℝ) : Crit {z : S₀ | z.1.2 = 0 ∧ m ≤ z.1.1} where
  hgt_mem _ hz _ hw _ h1 h2 h0 := absurd (le_antisymm (h2.trans hw.1.le) (hz.1 ▸ h1)) h0
  zero_mem z hz _ _ _ _ := ⟨z, hz, hz.1⟩
  bar_mem _ hz _ _ _ _ _ hu0 h1 _ := ⟨hu0, hz.2.trans h1⟩
  pos_bar _ _ _ hw _ h2 _ _ _ := absurd hw.1 h2.ne'
  neg_bar _ _ _ hw _ h2 _ _ _ := absurd hw.1 h2.ne

/-! ## Sets with the closure property are connected -/

/-- The parametrization of `C₁`. -/
noncomputable def arc1 (r : ℝ) : ℝ × ℝ := (cA r, r)
/-- The parametrization of `C₂` (by depth). -/
noncomputable def arc2 (r : ℝ) : ℝ × ℝ := (1 + cA r, -r)

lemma continuousOn_arc1 : ContinuousOn arc1 (Ioi 0) :=
  continuousOn_cA.prodMk continuousOn_id

lemma continuousOn_arc2 : ContinuousOn arc2 (Ioi 0) :=
  (continuousOn_const.add continuousOn_cA).prodMk continuousOn_id.neg

lemma pre_of_ambient {P : Set (ℝ × ℝ)} (hP : IsPreconnected P) (hPS : P ⊆ S₀) :
    IsPreconnected (Subtype.val ⁻¹' P : Set S₀) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
    inter_eq_right.mpr hPS]
  exact hP

lemma isPreconnected_tail1 {t : ℝ} (ht : 0 < t) :
    IsPreconnected (arc1 '' Ioc 0 t ∪ Icc 0 1 ×ˢ {0}) := by
  have hI : IsPreconnected (arc1 '' Ioc 0 t) :=
    isPreconnected_Ioc.image _ (continuousOn_arc1.mono Ioc_subset_Ioi_self)
  refine hI.subset_closure subset_union_left (union_subset subset_closure ?_)
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, hy⟩
  rw [mem_singleton_iff] at hy; subst hy
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨r, hr0, hrε, -, hcr⟩ := exists_cA_eq hx0 hx1 (lt_min hε ht)
  refine ⟨arc1 r, mem_image_of_mem _ ⟨hr0, (hrε.trans_le (min_le_right _ _)).le⟩, ?_⟩
  rw [Prod.dist_eq]
  simp only [arc1, hcr, dist_self, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hr0]
  exact max_lt hε (hrε.trans_le (min_le_left _ _))

lemma isPreconnected_tail2 {t : ℝ} (ht : 0 < t) :
    IsPreconnected (arc2 '' Ioc 0 t ∪ Icc 1 2 ×ˢ {0}) := by
  have hI : IsPreconnected (arc2 '' Ioc 0 t) :=
    isPreconnected_Ioc.image _ (continuousOn_arc2.mono Ioc_subset_Ioi_self)
  refine hI.subset_closure subset_union_left (union_subset subset_closure ?_)
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, hy⟩
  rw [mem_singleton_iff] at hy; subst hy
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨r, hr0, hrε, -, hcr⟩ := exists_cA_eq (x := x - 1) (by linarith) (by linarith)
    (lt_min hε ht)
  refine ⟨arc2 r, mem_image_of_mem _ ⟨hr0, (hrε.trans_le (min_le_right _ _)).le⟩, ?_⟩
  rw [Prod.dist_eq]
  simp only [arc2, hcr, Real.dist_eq, zero_sub, neg_neg, abs_of_pos hr0]
  refine max_lt ?_ (hrε.trans_le (min_le_left _ _))
  rw [show x - (1 + (x - 1)) = 0 by ring, abs_zero]; exact hε

lemma bar_piece {W : Set S₀} (hW : Crit W) {z w : S₀} (hz : z ∈ W) (hw : w ∈ W)
    (hz0 : z.1.2 = 0) (hw0 : w.1.2 = 0) (hzw : z.1.1 ≤ w.1.1) :
    ∃ t ⊆ W, z ∈ t ∧ w ∈ t ∧ IsPreconnected t := by
  refine ⟨Subtype.val ⁻¹' (Icc z.1.1 w.1.1 ×ˢ {0}), ?_, ⟨⟨le_rfl, hzw⟩, hz0⟩,
    ⟨⟨hzw, le_rfl⟩, hw0⟩, pre_of_ambient (isPreconnected_Icc.prod isPreconnected_singleton) ?_⟩
  · rintro v ⟨⟨h1, h2⟩, hv⟩
    exact hW.bar_mem z hz w hw v hz0 hw0 hv h1 h2
  · rintro ⟨x, y⟩ ⟨⟨h1, h2⟩, hy⟩
    rw [mem_singleton_iff] at hy
    exact Or.inr (Or.inl ⟨hy, (x_nonneg z).trans h1, h2.trans (x_le_two w)⟩)

lemma Crit.isPreconnected {W : Set S₀} (hW : Crit W) : IsPreconnected W := by
  rcases W.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h]; exact isPreconnected_empty
  by_cases hbar : ∃ b ∈ W, b.1.2 = 0
  · obtain ⟨b, hb, hb0⟩ := hbar
    refine isPreconnected_of_forall b fun y hy => ?_
    rcases lt_trichotomy y.1.2 0 with hn | h0 | hp
    · -- through the tail of `C₂`
      set e := bar (x := max b.1.1 1) (le_max_of_le_right zero_le_one)
        (max_le (x_le_two b) one_le_two) with he_def
      have he : e ∈ W := hW.neg_bar b hb y hy hb0.ge hn e rfl (le_max_right _ _)
      obtain ⟨t₁, ht₁W, hbt, het, ht₁⟩ := bar_piece hW hb he hb0 rfl (le_max_left _ _)
      refine ⟨Subtype.val ⁻¹' (arc2 '' Ioc 0 (-y.1.2) ∪ Icc 1 2 ×ˢ {0}) ∪ t₁, ?_,
        Or.inr hbt, Or.inl (Or.inl ⟨-y.1.2, ⟨by linarith, le_rfl⟩, ?_⟩), ?_⟩
      · refine union_subset ?_ ht₁W
        rintro v (⟨r, ⟨hr0, hr⟩, hv⟩ | ⟨⟨h1, -⟩, hv⟩)
        · have hvr : v.1.2 = -r := by rw [← hv]; rfl
          exact hW.hgt_mem y hy b hb v (by linarith) (by linarith) (by linarith)
        · exact hW.neg_bar b hb y hy hb0.ge hn v hv h1
      · rcases S₀_cases y with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩
        · linarith
        · linarith
        · simp only [arc2]; rw [← h, neg_neg]
      · refine IsPreconnected.union e (Or.inr ⟨⟨le_max_right _ _, max_le (x_le_two b)
          one_le_two⟩, rfl⟩) het (pre_of_ambient (isPreconnected_tail2 (by linarith)) ?_) ht₁
        rintro _ (⟨r, ⟨hr0, hr⟩, rfl⟩ | ⟨⟨h1, h2⟩, hv⟩)
        · refine Or.inr (Or.inr ⟨?_, by simp only [arc2]; linarith, by simp [arc2]⟩)
          simp only [arc2]; linarith [hgt_ge y]
        · exact Or.inr (Or.inl ⟨hv, by linarith, h2⟩)
    · rcases le_total b.1.1 y.1.1 with h | h
      · exact bar_piece hW hb hy hb0 h0 h
      · obtain ⟨t, htW, hyt, hbt, ht⟩ := bar_piece hW hy hb h0 hb0 h
        exact ⟨t, htW, hbt, hyt, ht⟩
    · -- through the tail of `C₁`
      set e := bar (x := min b.1.1 1) (le_min (x_nonneg b) zero_le_one)
        ((min_le_right _ _).trans one_le_two) with he_def
      have he : e ∈ W := hW.pos_bar b hb y hy hb0.le hp e rfl (min_le_right _ _)
      obtain ⟨t₁, ht₁W, het, hbt, ht₁⟩ := bar_piece hW he hb rfl hb0 (min_le_left _ _)
      refine ⟨Subtype.val ⁻¹' (arc1 '' Ioc 0 y.1.2 ∪ Icc 0 1 ×ˢ {0}) ∪ t₁, ?_,
        Or.inr hbt, Or.inl (Or.inl ⟨y.1.2, ⟨hp, le_rfl⟩, ?_⟩), ?_⟩
      · refine union_subset ?_ ht₁W
        rintro v (⟨r, ⟨hr0, hr⟩, hv⟩ | ⟨⟨-, h1⟩, hv⟩)
        · have hvr : v.1.2 = r := by rw [← hv]; rfl
          exact hW.hgt_mem b hb y hy v (by linarith) (by linarith) (by linarith)
        · exact hW.pos_bar b hb y hy hb0.le hp v hv h1
      · rcases S₀_cases y with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
        · simp only [arc1]; rw [← h]
        · linarith
        · linarith
      · refine IsPreconnected.union e (Or.inr ⟨⟨le_min (x_nonneg b) zero_le_one,
          min_le_right _ _⟩, rfl⟩) het (pre_of_ambient (isPreconnected_tail1 hp) ?_) ht₁
        rintro _ (⟨r, ⟨hr0, hr⟩, rfl⟩ | ⟨⟨h1, h2⟩, hv⟩)
        · exact Or.inl ⟨hr0, hr.trans (hgt_le y), rfl⟩
        · exact Or.inr (Or.inl ⟨hv, h1, by linarith⟩)
  · push_neg at hbar
    refine isPreconnected_of_forall x₀ fun y hy => ?_
    have hx0 := hbar x₀ hx₀
    have hy0 := hbar y hy
    rcases lt_or_gt_of_ne hx0 with hxn | hxp
    · have hyn : y.1.2 < 0 := by
        by_contra hc
        obtain ⟨u, hu, hu0⟩ := hW.zero_mem x₀ hx₀ y hy hxn.le (not_lt.mp hc)
        exact hbar u hu hu0
      have key : ∀ z ∈ W, ∀ w ∈ W, z.1.2 < 0 → w.1.2 < 0 → z.1.2 ≤ w.1.2 →
          ∃ t ⊆ W, z ∈ t ∧ w ∈ t ∧ IsPreconnected t := by
        intro z hz w hw hzn hwn hzw
        refine ⟨Subtype.val ⁻¹' (arc2 '' Icc (-w.1.2) (-z.1.2)), ?_, ?_, ?_,
          pre_of_ambient (isPreconnected_Icc.image _ (continuousOn_arc2.mono fun r hr =>
            show (0 : ℝ) < r by linarith [hr.1])) ?_⟩
        · rintro v ⟨r, ⟨h1, h2⟩, hv⟩
          have hvr : v.1.2 = -r := by rw [← hv]; rfl
          exact hW.hgt_mem z hz w hw v (by linarith) (by linarith) (by linarith)
        · refine ⟨-z.1.2, ⟨by linarith, le_rfl⟩, ?_⟩
          rcases S₀_cases z with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩
          · linarith
          · linarith
          · simp only [arc2]; rw [← h, neg_neg]
        · refine ⟨-w.1.2, ⟨le_rfl, by linarith⟩, ?_⟩
          rcases S₀_cases w with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩
          · linarith
          · linarith
          · simp only [arc2]; rw [← h, neg_neg]
        · rintro _ ⟨r, ⟨h1, h2⟩, rfl⟩
          refine Or.inr (Or.inr ⟨?_, by simp only [arc2]; linarith, by simp [arc2]⟩)
          simp only [arc2]; linarith [hgt_ge z]
      rcases le_total x₀.1.2 y.1.2 with h | h
      · exact key x₀ hx₀ y hy hxn hyn h
      · obtain ⟨t, htW, hyt, hxt, ht⟩ := key y hy x₀ hx₀ hyn hxn h
        exact ⟨t, htW, hxt, hyt, ht⟩
    · have hyp : 0 < y.1.2 := by
        by_contra hc
        obtain ⟨u, hu, hu0⟩ := hW.zero_mem y hy x₀ hx₀ (not_lt.mp hc) hxp.le
        exact hbar u hu hu0
      have key : ∀ z ∈ W, ∀ w ∈ W, 0 < z.1.2 → 0 < w.1.2 → z.1.2 ≤ w.1.2 →
          ∃ t ⊆ W, z ∈ t ∧ w ∈ t ∧ IsPreconnected t := by
        intro z hz w hw hzp hwp hzw
        refine ⟨Subtype.val ⁻¹' (arc1 '' Icc z.1.2 w.1.2), ?_, ?_, ?_,
          pre_of_ambient (isPreconnected_Icc.image _ (continuousOn_arc1.mono fun r hr =>
            show (0 : ℝ) < r by linarith [hr.1])) ?_⟩
        · rintro v ⟨r, ⟨h1, h2⟩, hv⟩
          have hvr : v.1.2 = r := by rw [← hv]; rfl
          exact hW.hgt_mem z hz w hw v (by linarith) (by linarith) (by linarith)
        · refine ⟨z.1.2, ⟨le_rfl, hzw⟩, ?_⟩
          rcases S₀_cases z with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
          · simp only [arc1]; rw [← h]
          · linarith
          · linarith
        · refine ⟨w.1.2, ⟨hzw, le_rfl⟩, ?_⟩
          rcases S₀_cases w with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
          · simp only [arc1]; rw [← h]
          · linarith
          · linarith
        · rintro _ ⟨r, ⟨h1, h2⟩, rfl⟩
          exact Or.inl ⟨show (0 : ℝ) < r by linarith, h2.trans (hgt_le w), rfl⟩
      rcases le_total x₀.1.2 y.1.2 with h | h
      · exact key x₀ hx₀ y hy hxp hyp h
      · obtain ⟨t, htW, hyt, hxt, ht⟩ := key y hy x₀ hx₀ hyp hxp h
        exact ⟨t, htW, hxt, hyt, ht⟩

/-! ## Bing's standing hypothesis for `S₀` -/

lemma continuous_hgt : Continuous fun v : S₀ => v.1.2 := continuous_snd.comp continuous_subtype_val
lemma continuous_xc : Continuous fun v : S₀ => v.1.1 := continuous_fst.comp continuous_subtype_val

lemma connectedSpace_S₀ : ConnectedSpace S₀ := by
  haveI : Nonempty S₀ := ⟨p₀⟩
  exact connectedSpace_iff_univ.mpr ⟨univ_nonempty, crit_univ.isPreconnected⟩

lemma nontrivial_S₀ : Nontrivial S₀ :=
  ⟨⟨p₀, q₀, fun h => by
    have := congrArg (fun z : S₀ => z.1.1) h
    simp only [p₀, q₀, bar] at this
    norm_num at this⟩⟩

/-- `S₀` is hereditarily unicoherent. -/
lemma hu_S₀ : IsHereditarilyUnicoherent (univ : Set S₀) := by
  intro K _ hK _ H L hH hL hHL
  obtain ⟨h, hh⟩ := hH.2.1
  obtain ⟨l, hl⟩ := hL.2.1
  obtain ⟨x, -, hx⟩ := isPreconnected_closed_iff.mp hK.2.2 H L hH.1.isClosed hL.1.isClosed
    hHL.symm.subset ⟨h, by rw [← hHL]; exact Or.inl hh, hh⟩ ⟨l, by rw [← hHL]; exact Or.inr hl, hl⟩
  exact ⟨⟨x, hx⟩, ((crit_of hH.1.isClosed hH.2.2).inter
    (crit_of hL.1.isClosed hL.2.2)).isPreconnected⟩

/-- `S₀` is hereditarily decomposable. -/
lemma hd_S₀ : IsHereditarilyDecomposable (univ : Set S₀) := by
  intro K _ hK hnt
  have hKc := crit_of hK.1.isClosed hK.2.2
  have piece : ∀ C : Set S₀, Crit C → IsClosed C → (K ∩ C).Nonempty →
      Fold.Q78.IsContinuum (K ∩ C) := fun C hC hCc hne =>
    ⟨hK.1.inter_right hCc, hne, (hKc.inter hC).isPreconnected⟩
  by_cases hh : ∃ z ∈ K, ∃ w ∈ K, z.1.2 < w.1.2
  · obtain ⟨z, hz, w, hw, hzw⟩ := hh
    set m := (z.1.2 + w.1.2) / 2 with hm
    refine ⟨K ∩ {v | v.1.2 ≤ m}, K ∩ {v | m ≤ v.1.2},
      piece _ (crit_hgt_le m) (isClosed_le continuous_hgt continuous_const)
        ⟨z, hz, show z.1.2 ≤ m by linarith⟩,
      piece _ (crit_le_hgt m) (isClosed_le continuous_const continuous_hgt)
        ⟨w, hw, show m ≤ w.1.2 by linarith⟩, ?_, ?_, ?_⟩
    · intro h
      have : w ∈ K ∩ {v | v.1.2 ≤ m} := by rw [h]; exact hw
      exact absurd this.2 (by show ¬ w.1.2 ≤ m; linarith)
    · intro h
      have : z ∈ K ∩ {v | m ≤ v.1.2} := by rw [h]; exact hz
      exact absurd this.2 (by show ¬ m ≤ z.1.2; linarith)
    · rw [← inter_union_distrib_left]
      exact inter_eq_left.mpr fun v _ => by
        rcases le_total v.1.2 m with h | h
        · exact Or.inl h
        · exact Or.inr h
  · push_neg at hh
    obtain ⟨z, hz, w, hw, hzw⟩ := hnt
    have heq : z.1.2 = w.1.2 := le_antisymm (hh w hw z hz) (hh z hz w hw)
    have hz0 : z.1.2 = 0 := by
      by_contra h0; exact hzw (eq_of_hgt heq h0)
    have hall : ∀ v ∈ K, v.1.2 = 0 := fun v hv =>
      le_antisymm (hz0 ▸ hh z hz v hv) (hz0 ▸ hh v hv z hz)
    have hx : z.1.1 ≠ w.1.1 := fun h => hzw (eq_of_bar hz0 (hall w hw) h)
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ K, ∃ b ∈ K, a.1.1 < b.1.1 := by
      rcases lt_or_gt_of_ne hx with h | h
      · exact ⟨z, hz, w, hw, h⟩
      · exact ⟨w, hw, z, hz, h⟩
    set m := (a.1.1 + b.1.1) / 2 with hm
    refine ⟨K ∩ {v | v.1.2 = 0 ∧ v.1.1 ≤ m}, K ∩ {v | v.1.2 = 0 ∧ m ≤ v.1.1},
      piece _ (crit_bar_le m) ((isClosed_eq continuous_hgt continuous_const).inter
        (isClosed_le continuous_xc continuous_const))
        ⟨a, ha, hall a ha, show a.1.1 ≤ m by linarith⟩,
      piece _ (crit_le_bar m) ((isClosed_eq continuous_hgt continuous_const).inter
        (isClosed_le continuous_const continuous_xc))
        ⟨b, hb, hall b hb, show m ≤ b.1.1 by linarith⟩, ?_, ?_, ?_⟩
    · intro h
      have : b ∈ K ∩ {v | v.1.2 = 0 ∧ v.1.1 ≤ m} := by rw [h]; exact hb
      exact absurd this.2.2 (by show ¬ b.1.1 ≤ m; linarith)
    · intro h
      have : a ∈ K ∩ {v | v.1.2 = 0 ∧ m ≤ v.1.1} := by rw [h]; exact ha
      exact absurd this.2.2 (by show ¬ m ≤ a.1.1; linarith)
    · rw [← inter_union_distrib_left]
      exact inter_eq_left.mpr fun v hv => by
        rcases le_total v.1.1 m with h | h
        · exact Or.inl ⟨hall v hv, h⟩
        · exact Or.inr ⟨hall v hv, h⟩

/-! ### Atriodicity -/

/-- If `T ∖ N = A ∪ B ∪ C` with `A` separated from `B` and `C`, then `N ∪ A` is a closed
connected set. -/
lemma union_piece {T N A B C : Set S₀} (hT : IsPreconnected T) (hTc : IsClosed T)
    (hN : IsPreconnected N) (hNc : IsClosed N) (hNne : N.Nonempty) (hNT : N ⊆ T)
    (hA : A ⊆ T) (hcov : ∀ x ∈ T, x ∈ N ∨ x ∈ A ∨ x ∈ B ∨ x ∈ C)
    (h2 : Disjoint A (closure B)) (h4 : Disjoint A (closure C))
    (h1 : Disjoint (closure A) B) (h3 : Disjoint (closure A) C) :
    IsClosed (N ∪ A) ∧ IsPreconnected (N ∪ A) := by
  have hclA : closure A ⊆ N ∪ A := by
    intro x hx
    rcases hcov x (closure_minimal hA hTc hx) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (disjoint_left.mp h1 hx)
    · exact absurd h (disjoint_left.mp h3 hx)
  have hclosed : IsClosed (N ∪ A) := by
    rw [← closure_subset_iff_isClosed, closure_union, hNc.closure_eq]
    exact union_subset subset_union_left hclA
  have key : ∀ F G : Set S₀, IsClosed F → IsClosed G → N ∪ A ⊆ F ∪ G →
      (N ∪ A) ∩ (F ∩ G) = ∅ → N ⊆ F → ((N ∪ A) ∩ G).Nonempty → False := by
    intro F G hF hG hcov' hem hNF' ⟨g, hgNA, hgG⟩
    have hPA : (N ∪ A) ∩ G ⊆ A := by
      rintro x ⟨hx | hx, hxG⟩
      · exact absurd (show x ∈ (N ∪ A) ∩ (F ∩ G) from ⟨Or.inl hx, hNF' hx, hxG⟩)
          (by rw [hem]; exact notMem_empty _)
      · exact hx
    obtain ⟨n, hn⟩ := hNne
    have hcovT : T ⊆ (N ∪ A) ∩ G ∪ (((N ∪ A) ∩ F) ∪ closure B ∪ closure C) := by
      intro x hx
      rcases hcov x hx with h | h | h | h
      · exact Or.inr (Or.inl (Or.inl ⟨Or.inl h, hNF' h⟩))
      · rcases hcov' (Or.inr h) with h' | h'
        · exact Or.inr (Or.inl (Or.inl ⟨Or.inr h, h'⟩))
        · exact Or.inl ⟨Or.inr h, h'⟩
      · exact Or.inr (Or.inl (Or.inr (subset_closure h)))
      · exact Or.inr (Or.inr (subset_closure h))
    obtain ⟨x, -, hxP, hxQ⟩ := isPreconnected_closed_iff.mp hT ((N ∪ A) ∩ G)
      (((N ∪ A) ∩ F) ∪ closure B ∪ closure C) (hclosed.inter hG)
      (((hclosed.inter hF).union isClosed_closure).union isClosed_closure) hcovT
      ⟨g, hA (hPA ⟨hgNA, hgG⟩), hgNA, hgG⟩
      ⟨n, hNT hn, Or.inl (Or.inl ⟨Or.inl hn, hNF' hn⟩)⟩
    have hxA := hPA hxP
    rcases hxQ with (hxF | hxB) | hxC
    · exact absurd (show x ∈ (N ∪ A) ∩ (F ∩ G) from ⟨hxP.1, hxF.2, hxP.2⟩)
        (by rw [hem]; exact notMem_empty _)
    · exact disjoint_left.mp h2 hxA hxB
    · exact disjoint_left.mp h4 hxA hxC
  refine ⟨hclosed, isPreconnected_closed_iff.mpr fun F G hF hG hcovFG hNF hNG => ?_⟩
  by_contra hne
  have hem : (N ∪ A) ∩ (F ∩ G) = ∅ := not_nonempty_iff_eq_empty.mp hne
  have hNsub : N ⊆ F ∪ G := subset_union_left.trans hcovFG
  by_cases hNG' : (N ∩ G).Nonempty
  · by_cases hNF' : (N ∩ F).Nonempty
    · obtain ⟨x, hxN, hx⟩ := isPreconnected_closed_iff.mp hN F G hF hG hNsub hNF' hNG'
      exact hne ⟨x, Or.inl hxN, hx⟩
    · have hNG'' : N ⊆ G := fun x hx => (hNsub hx).resolve_left fun h => hNF' ⟨x, hx, h⟩
      exact key G F hG hF (fun x hx => (hcovFG hx).symm) (by rw [inter_comm G F]; exact hem)
        hNG'' hNF
  · have hNF'' : N ⊆ F := fun x hx => (hNsub hx).resolve_right fun h => hNG' ⟨x, hx, h⟩
    exact key F G hF hG hcovFG hem hNF'' hNG

lemma exists_ne_zero_between {a b : ℝ} (h : a < b) : ∃ t, a < t ∧ t < b ∧ t ≠ 0 := by
  by_cases h1 : a < 0 ∧ 0 < b
  · exact ⟨b / 2, by linarith, by linarith, by linarith⟩
  · refine ⟨(a + b) / 2, by linarith, by linarith, fun h0 => h1 ⟨?_, ?_⟩⟩ <;> linarith

/-- Where a point outside the continuum `N` can lie: above all of `N`, below all of `N`, or on the
bar to the left or to the right of `N ∩ B`. -/
lemma kind {N : Set S₀} (hN : Crit N) {zm zM : S₀} (hzm : zm ∈ N) (hzM : zM ∈ N) {a : S₀}
    (ha : a ∉ N) :
    zM.1.2 < a.1.2 ∨ a.1.2 < zm.1.2 ∨ (a.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ a.1.1 < n.1.1) ∨
      (a.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ n.1.1 < a.1.1) := by
  by_cases hU : zM.1.2 < a.1.2
  · exact Or.inl hU
  by_cases hD : a.1.2 < zm.1.2
  · exact Or.inr (Or.inl hD)
  push_neg at hU hD
  have h0 : a.1.2 = 0 := by
    by_contra h0; exact ha (hN.hgt_mem zm hzm zM hzM a hD hU h0)
  obtain ⟨n, hn, hn0⟩ := hN.zero_mem zm hzm zM hzM (by rwa [h0] at hD) (by rwa [h0] at hU)
  rcases lt_trichotomy a.1.1 n.1.1 with h | h | h
  · exact Or.inr (Or.inr (Or.inl ⟨h0, n, hn, hn0, h⟩))
  · exact absurd (by rwa [← eq_of_bar h0 hn0 h] at hn) ha
  · exact Or.inr (Or.inr (Or.inr ⟨h0, n, hn, hn0, h⟩))

section conflicts

variable {N X Y : Set S₀} (hX : Crit (N ∪ X)) (hY : Crit (N ∪ Y)) (dXY : Disjoint X Y)
  (dXN : Disjoint X N) (dYN : Disjoint Y N)
include hX hY dXY dXN dYN

omit hX hY dXN dYN in
lemma conflict {u : S₀} (hux : u ∈ N ∪ X) (huy : u ∈ N ∪ Y) (hun : u ∉ N) : False :=
  disjoint_left.mp dXY (hux.resolve_left hun) (huy.resolve_left hun)

omit dXN dYN in
lemma no_up_up {zM a a' : S₀} (hzM : zM ∈ N) (hNmax : ∀ n ∈ N, n.1.2 ≤ zM.1.2) (ha : a ∈ X)
    (ha' : a' ∈ Y) (hu : zM.1.2 < a.1.2) (hu' : zM.1.2 < a'.1.2) : False := by
  obtain ⟨t, ht1, ht2, ht0⟩ := exists_ne_zero_between (lt_min hu hu')
  have h1 := ht2.trans_le (min_le_left _ _)
  have h2 := ht2.trans_le (min_le_right _ _)
  obtain ⟨u, rfl⟩ := exists_hgt (by linarith [hgt_ge zM]) (by linarith [hgt_le a]) ht0
  exact conflict dXY (hX.hgt_mem zM (Or.inl hzM) a (Or.inr ha) u ht1.le h1.le ht0)
    (hY.hgt_mem zM (Or.inl hzM) a' (Or.inr ha') u ht1.le h2.le ht0)
    (fun hn => by linarith [hNmax u hn])

omit dXN dYN in
lemma no_down_down {zm a a' : S₀} (hzm : zm ∈ N) (hNmin : ∀ n ∈ N, zm.1.2 ≤ n.1.2) (ha : a ∈ X)
    (ha' : a' ∈ Y) (hd : a.1.2 < zm.1.2) (hd' : a'.1.2 < zm.1.2) : False := by
  obtain ⟨t, ht1, ht2, ht0⟩ := exists_ne_zero_between (max_lt hd hd')
  have h1 := (le_max_left _ _).trans_lt ht1
  have h2 := (le_max_right _ _).trans_lt ht1
  obtain ⟨u, rfl⟩ := exists_hgt (by linarith [hgt_ge a]) (by linarith [hgt_le zm]) ht0
  exact conflict dXY (hX.hgt_mem a (Or.inr ha) zm (Or.inl hzm) u h1.le ht2.le ht0)
    (hY.hgt_mem a' (Or.inr ha') zm (Or.inl hzm) u h2.le ht2.le ht0)
    (fun hn => by linarith [hNmin u hn])

lemma no_left_left {a a' : S₀} (ha : a ∈ X) (ha' : a' ∈ Y)
    (hL : a.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ a.1.1 < n.1.1)
    (hL' : a'.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ a'.1.1 < n.1.1) : False := by
  obtain ⟨h0, n, hn, hn0, hlt⟩ := hL
  obtain ⟨h0', n', hn', hn0', hlt'⟩ := hL'
  rcases le_total a.1.1 a'.1.1 with h | h
  · exact conflict dXY (hX.bar_mem a (Or.inr ha) n' (Or.inl hn') a' h0 hn0' h0' h hlt'.le)
      (Or.inr ha') (disjoint_left.mp dYN ha')
  · exact conflict dXY (Or.inr ha) (hY.bar_mem a' (Or.inr ha') n (Or.inl hn) a h0' hn0 h0 h hlt.le)
      (disjoint_left.mp dXN ha)

lemma no_right_right {a a' : S₀} (ha : a ∈ X) (ha' : a' ∈ Y)
    (hR : a.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ n.1.1 < a.1.1)
    (hR' : a'.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ n.1.1 < a'.1.1) : False := by
  obtain ⟨h0, n, hn, hn0, hlt⟩ := hR
  obtain ⟨h0', n', hn', hn0', hlt'⟩ := hR'
  rcases le_total a.1.1 a'.1.1 with h | h
  · exact conflict dXY (Or.inr ha) (hY.bar_mem n (Or.inl hn) a' (Or.inr ha') a hn0 h0' h0 hlt.le h)
      (disjoint_left.mp dXN ha)
  · exact conflict dXY (hX.bar_mem n' (Or.inl hn') a (Or.inr ha) a' hn0' h0 h0' hlt'.le h)
      (Or.inr ha') (disjoint_left.mp dYN ha')

omit hY dXN in
lemma no_up_left {zM a a' : S₀} (hNmax : ∀ n ∈ N, n.1.2 ≤ zM.1.2) (ha : a ∈ X) (ha' : a' ∈ Y)
    (hu : zM.1.2 < a.1.2) (hL : a'.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ a'.1.1 < n.1.1) : False := by
  obtain ⟨h0', n, hn, hn0, hlt⟩ := hL
  have hpos : 0 < a.1.2 := by linarith [hNmax n hn]
  have he : bar (x := 0) le_rfl (by norm_num) ∈ N ∪ X :=
    hX.pos_bar n (Or.inl hn) a (Or.inr ha) hn0.le hpos _ rfl (by simp [bar])
  exact conflict dXY (hX.bar_mem _ he n (Or.inl hn) a' rfl hn0 h0'
    (by simp only [bar]; exact x_nonneg a') hlt.le) (Or.inr ha') (disjoint_left.mp dYN ha')

omit hY dXN in
lemma no_down_right {zm a a' : S₀} (hNmin : ∀ n ∈ N, zm.1.2 ≤ n.1.2) (ha : a ∈ X) (ha' : a' ∈ Y)
    (hd : a.1.2 < zm.1.2) (hR : a'.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ n.1.1 < a'.1.1) : False := by
  obtain ⟨h0', n, hn, hn0, hlt⟩ := hR
  have hneg : a.1.2 < 0 := by linarith [hNmin n hn]
  have he : bar (x := 2) (by norm_num) le_rfl ∈ N ∪ X :=
    hX.neg_bar n (Or.inl hn) a (Or.inr ha) hn0.ge hneg _ rfl (by simp [bar])
  exact conflict dXY (hX.bar_mem n (Or.inl hn) _ he a' hn0 rfl h0' hlt.le
    (by simp only [bar]; exact x_le_two a')) (Or.inr ha') (disjoint_left.mp dYN ha')

/-- Two points of different pieces cannot be of the same kind, nor of kinds (up, left) or
(down, right). -/
lemma no_pair {zm zM a a' : S₀} (hzm : zm ∈ N) (hzM : zM ∈ N)
    (hNmin : ∀ n ∈ N, zm.1.2 ≤ n.1.2) (hNmax : ∀ n ∈ N, n.1.2 ≤ zM.1.2) (ha : a ∈ X)
    (ha' : a' ∈ Y) :
    ¬ ((zM.1.2 < a.1.2 ∧ zM.1.2 < a'.1.2) ∨ (a.1.2 < zm.1.2 ∧ a'.1.2 < zm.1.2) ∨
      ((a.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ a.1.1 < n.1.1) ∧
        (a'.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ a'.1.1 < n.1.1)) ∨
      ((a.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ n.1.1 < a.1.1) ∧
        (a'.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ n.1.1 < a'.1.1)) ∨
      (zM.1.2 < a.1.2 ∧ (a'.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ a'.1.1 < n.1.1)) ∨
      ((a.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ a.1.1 < n.1.1) ∧ zM.1.2 < a'.1.2) ∨
      (a.1.2 < zm.1.2 ∧ (a'.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ n.1.1 < a'.1.1)) ∨
      ((a.1.2 = 0 ∧ ∃ n ∈ N, n.1.2 = 0 ∧ n.1.1 < a.1.1) ∧ a'.1.2 < zm.1.2)) := by
  rintro (⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩)
  · exact no_up_up hX hY dXY hzM hNmax ha ha' h h'
  · exact no_down_down hX hY dXY hzm hNmin ha ha' h h'
  · exact no_left_left hX hY dXY dXN dYN ha ha' h h'
  · exact no_right_right hX hY dXY dXN dYN ha ha' h h'
  · exact no_up_left hX dXY dYN hNmax ha ha' h h'
  · exact no_up_left hY dXY.symm dXN hNmax ha' ha h' h
  · exact no_down_right hX dXY dYN hNmin ha ha' h h'
  · exact no_down_right hY dXY.symm dXN hNmin ha' ha h' h

end conflicts

/-- `S₀` contains no triod. -/
lemma not_isTriod (T : Set S₀) : ¬ IsTriod T := by
  rintro ⟨hT, N, hN, hNT, A, B, C, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hdec, h1, h2, h3, h4, h5, h6⟩
  have hsub : ∀ x, x ∈ A ∪ B ∪ C → x ∈ T \ N := fun x hx => by rw [hdec]; exact hx
  have hAT : A ⊆ T \ N := fun x hx => hsub x (Or.inl (Or.inl hx))
  have hBT : B ⊆ T \ N := fun x hx => hsub x (Or.inl (Or.inr hx))
  have hCT : C ⊆ T \ N := fun x hx => hsub x (Or.inr hx)
  have hcov : ∀ x ∈ T, x ∈ N ∨ x ∈ A ∨ x ∈ B ∨ x ∈ C := by
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    have : x ∈ A ∪ B ∪ C := by rw [← hdec]; exact ⟨hx, hxN⟩
    rcases this with (h | h) | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hTc := hT.1.isClosed
  have hNc := hN.1.isClosed
  have pA := union_piece hT.2.2 hTc hN.2.2 hNc hN.2.1 hNT (fun x hx => (hAT hx).1) hcov
    h2 h4 h1 h3
  have pB := union_piece (A := B) (B := A) (C := C) hT.2.2 hTc hN.2.2 hNc hN.2.1 hNT
    (fun x hx => (hBT hx).1) (fun x hx => by rcases hcov x hx with h | h | h | h <;> tauto)
    h1.symm h6 h2.symm h5
  have pC := union_piece (A := C) (B := A) (C := B) hT.2.2 hTc hN.2.2 hNc hN.2.1 hNT
    (fun x hx => (hCT hx).1) (fun x hx => by rcases hcov x hx with h | h | h | h <;> tauto)
    h3.symm h5.symm h4.symm h6.symm
  have cA' := crit_of pA.1 pA.2
  have cB' := crit_of pB.1 pB.2
  have cC' := crit_of pC.1 pC.2
  have cN := crit_of hNc hN.2.2
  obtain ⟨zm, hzm, hmin⟩ := hN.1.exists_isMinOn hN.2.1 continuous_hgt.continuousOn
  obtain ⟨zM, hzM, hmax⟩ := hN.1.exists_isMaxOn hN.2.1 continuous_hgt.continuousOn
  have hNmin : ∀ n ∈ N, zm.1.2 ≤ n.1.2 := fun n hn => hmin hn
  have hNmax : ∀ n ∈ N, n.1.2 ≤ zM.1.2 := fun n hn => hmax hn
  have dAB : Disjoint A B := h1.mono_left subset_closure
  have dAC : Disjoint A C := h3.mono_left subset_closure
  have dBC : Disjoint B C := h5.mono_left subset_closure
  have dAN : Disjoint A N := disjoint_left.mpr fun x hx hxN => (hAT hx).2 hxN
  have dBN : Disjoint B N := disjoint_left.mpr fun x hx hxN => (hBT hx).2 hxN
  have dCN : Disjoint C N := disjoint_left.mpr fun x hx hxN => (hCT hx).2 hxN
  have pAB := no_pair cA' cB' dAB dAN dBN hzm hzM hNmin hNmax ha hb
  have pAC := no_pair cA' cC' dAC dAN dCN hzm hzM hNmin hNmax ha hc
  have pBC := no_pair cB' cC' dBC dBN dCN hzm hzM hNmin hNmax hb hc
  have ka := kind cN hzm hzM (disjoint_left.mp dAN ha)
  have kb := kind cN hzm hzM (disjoint_left.mp dBN hb)
  have kc := kind cN hzm hzM (disjoint_left.mp dCN hc)
  rcases ka with ka | ka | ka | ka <;> rcases kb with kb | kb | kb | kb <;>
    rcases kc with kc | kc | kc | kc <;>
    first
      | exact pAB (Or.inl ⟨ka, kb⟩)
      | exact pAB (Or.inr (Or.inl ⟨ka, kb⟩))
      | exact pAB (Or.inr (Or.inr (Or.inl ⟨ka, kb⟩)))
      | exact pAB (Or.inr (Or.inr (Or.inr (Or.inl ⟨ka, kb⟩))))
      | exact pAB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ka, kb⟩)))))
      | exact pAB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ka, kb⟩))))))
      | exact pAB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ka, kb⟩)))))))
      | exact pAB (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨ka, kb⟩))))))))
      | exact pAC (Or.inl ⟨ka, kc⟩)
      | exact pAC (Or.inr (Or.inl ⟨ka, kc⟩))
      | exact pAC (Or.inr (Or.inr (Or.inl ⟨ka, kc⟩)))
      | exact pAC (Or.inr (Or.inr (Or.inr (Or.inl ⟨ka, kc⟩))))
      | exact pAC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ka, kc⟩)))))
      | exact pAC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ka, kc⟩))))))
      | exact pAC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ka, kc⟩)))))))
      | exact pAC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨ka, kc⟩))))))))
      | exact pBC (Or.inl ⟨kb, kc⟩)
      | exact pBC (Or.inr (Or.inl ⟨kb, kc⟩))
      | exact pBC (Or.inr (Or.inr (Or.inl ⟨kb, kc⟩)))
      | exact pBC (Or.inr (Or.inr (Or.inr (Or.inl ⟨kb, kc⟩))))
      | exact pBC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨kb, kc⟩)))))
      | exact pBC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨kb, kc⟩))))))
      | exact pBC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨kb, kc⟩)))))))
      | exact pBC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨kb, kc⟩))))))))

/-- **`S₀` satisfies Bing's standing hypothesis**: a nondegenerate continuum, atriodic,
hereditarily unicoherent and hereditarily decomposable. -/
theorem bingS_S₀ : BingS S₀ where
  connected := connectedSpace_S₀
  nontrivial := nontrivial_S₀
  atriodic T _ := not_isTriod T
  hu := hu_S₀
  hd := hd_S₀

/-- **The one-layer reading of Bing's Theorem 8 (`theorem8_1951`) is false; Bing's own statement
is `theorem8_1951'`.** For the continuum `S₀`, which satisfies Bing's standing
hypothesis, the third conjunct of the conclusion (`q ∈ g p → g p = g q`) fails. -/
theorem theorem8_1951_false :
    ¬ ∀ (S : Type) [MetricSpace S] [CompactSpace S], BingS S →
      (∀ p : S, Fold.Q78.IsContinuum (gElt p)) ∧
      (∀ p : S, p ∈ gElt p) ∧ (∀ p q : S, q ∈ gElt p → gElt p = gElt q) ∧
      (∀ (p : S) (U : Set S), IsOpen U → gElt p ⊆ U →
        IsOpen (⋃ q ∈ {q | gElt q ⊆ U}, gElt q)) ∧
      (∀ p q r : S, gElt p ≠ gElt q → gElt q ≠ gElt r → gElt p ≠ gElt r →
        Separates (gElt p) (gElt q) (gElt r) ∨ Separates (gElt q) (gElt p) (gElt r) ∨
          Separates (gElt r) (gElt p) (gElt q)) ∧
      (∀ p : S, interior (gElt p) = ∅) ∧
      (∀ r s : S, (∀ q q' : S, gElt q ≠ gElt r → gElt q' ≠ gElt r → gElt q ≠ gElt q' →
          ¬ Separates (gElt r) (gElt q) (gElt q')) →
        (∀ q q' : S, gElt q ≠ gElt s → gElt q' ≠ gElt s → gElt q ≠ gElt q' →
          ¬ Separates (gElt s) (gElt q) (gElt q')) →
        gElt r ≠ gElt s →
        ∀ M : Set S, Fold.Q78.IsContinuum M → r ∈ M → s ∈ M → M = univ) :=
  theorem8_1951_false_of_bingS bingS_S₀

end HPC.Plane.Counter92
