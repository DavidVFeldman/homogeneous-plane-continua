import HPC.Plane.Atriodic51BElt

/-!
# Batch 93: Bing's elements on the batch-92 continuum `S₀` — supporting lemmas

* horizontal windows `{a ≤ y ≤ b}` of `S₀` are continua (batch 92's closure property `Crit`), and a
  window contains interiorly a smaller window containing a given point interiorly;
* the mirror image of batch 92's `barL_subset_of_interior`: a continuum containing a point of
  `[1, 2] × {0}` interiorly contains `[1, 2] × {0}` (through the tail of `C₂`).
-/

namespace HPC.Plane.Counter92

open Set Topology Metric

/-- A horizontal window of `S₀`. -/
def window (a b : ℝ) : Set S₀ := {z | a ≤ z.1.2 ∧ z.1.2 ≤ b}

lemma isContinuum_window {a b : ℝ} {c : S₀} (hc : c ∈ window a b) :
    Fold.Q78.IsContinuum (window a b) := by
  have hcrit : Crit (window a b) := (crit_le_hgt a).inter (crit_hgt_le b)
  exact ⟨((isClosed_le continuous_const continuous_hgt).inter
    (isClosed_le continuous_hgt continuous_const)).isCompact, ⟨c, hc⟩, hcrit.isPreconnected⟩

lemma open_window_subset_interior (a b : ℝ) :
    {z : S₀ | a < z.1.2 ∧ z.1.2 < b} ⊆ interior (window a b) :=
  interior_maximal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    ((isOpen_lt continuous_const continuous_hgt).inter (isOpen_lt continuous_hgt continuous_const))

/-- A window around the height of `c` contains `c` doubly interiorly. -/
lemma containsNested_window {a b : ℝ} {c : S₀} (ha : a < c.1.2) (hb : c.1.2 < b) :
    ContainsNested (window a b) c := by
  refine ⟨window ((a + c.1.2) / 2) ((c.1.2 + b) / 2),
    isContinuum_window (c := c) ⟨by linarith, by linarith⟩, fun z hz => ?_, ?_⟩
  · exact open_window_subset_interior a b ⟨by linarith [hz.1], by linarith [hz.2]⟩
  · exact open_window_subset_interior _ _ ⟨by linarith, by linarith⟩

/-- The right half of the bar. -/
def barR : Set S₀ := {z | z.1.2 = 0 ∧ 1 ≤ z.1.1}

/-- A continuum containing a point of `[1,2] × {0}` interiorly contains `[1,2] × {0}`. -/
lemma barR_subset_of_interior {Z : Set S₀} (hZ : Fold.Q78.IsContinuum Z) {b : S₀}
    (hb0 : b.1.2 = 0) (hb1 : 1 ≤ b.1.1) (hbZ : b ∈ interior Z) : barR ⊆ Z := by
  rintro u ⟨hu0, hu1⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hbZ
  obtain ⟨ε, hε, hball⟩ := hbZ
  obtain ⟨t₁, ht₀, htε, ht₁, hct⟩ := exists_cA_eq (x := b.1.1 - 1) (by linarith)
    (by linarith [x_le_two b]) hε
  have hc₂Z : c₂ ht₀ ht₁ ∈ Z := hball (by
    rw [mem_ball, dist_S₀]
    simp only [c₂, hct, hb0, Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht₀]
    refine max_lt ?_ htε
    rw [show 1 + (b.1.1 - 1) - b.1.1 = 0 by ring, abs_zero]; exact hε)
  have hbZ' : b ∈ Z := hball (mem_ball_self hε)
  rw [← hZ.1.isClosed.closure_eq]
  refine mem_closure_of_forall fun δ hδ => ?_
  obtain ⟨t, ht0, htδ, ht1, hct'⟩ := exists_cA_eq (x := u.1.1 - 1) (by linarith)
    (by linarith [x_le_two u]) (lt_min hδ ht₀)
  obtain ⟨v, hvZ, hv⟩ := exists_height hZ.2.2 hc₂Z hbZ' (s := -t)
    ⟨by simp only [c₂]; linarith [htδ.trans_le (min_le_right _ _)], by rw [hb0]; linarith⟩
  rw [eq_c₂ v ht0 ht1 hv] at hvZ
  refine ⟨_, hvZ, ?_⟩
  rw [dist_S₀]
  simp only [c₂, hct', hu0, Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht0]
  refine max_lt ?_ (htδ.trans_le (min_le_left _ _))
  rw [show 1 + (u.1.1 - 1) - u.1.1 = 0 by ring, abs_zero]; exact hδ

end HPC.Plane.Counter92
