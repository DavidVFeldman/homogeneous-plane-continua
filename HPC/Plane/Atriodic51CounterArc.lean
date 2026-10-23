import HPC.Plane.Atriodic51CounterBing

/-!
# Batch 92: the decomposition space of `S₀` is not Hausdorff

For the continuum `S₀` of `HPC/Plane/Atriodic51Counter.lean`, every bar point `b = (x, 0)` with
`0 ≤ x < 1` has `g b = [0, 1] × {0}` (`gElt_bar`), while `g (1, 0) ⊇ [0, 2] × {0}`. Bar points
`(x, 0)` with `x < 1` accumulate at `(1, 0)`, so in the quotient of `S₀` by `p ~ q ⇔ g p = g q`
the classes of `p = (1/2, 0)` and `q = (1, 0)` cannot be separated: the quotient is not Hausdorff
(`quotient_not_t2`), hence not an arc, and `isArc_of_separatesPairs` is false as stated
(`isArc_of_separatesPairs_false`).
-/

namespace HPC.Plane.Counter92

open Set Topology Metric

/-- The left half of the bar. -/
def barL : Set S₀ := {z | z.1.2 = 0 ∧ z.1.1 ≤ 1}

/-- The part of `C₁` below height `ε`. -/
def C₁lo (ε : ℝ) : Set S₀ := {z | 0 < z.1.2 ∧ z.1.2 < ε}

lemma isPreconnected_C₁lo {ε : ℝ} (hε1 : ε ≤ 1) : IsPreconnected (C₁lo ε) := by
  have : C₁lo ε = Subtype.val ⁻¹' (arc1 '' Ioo 0 ε) := by
    ext z
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨z.1.2, ⟨h0, h1⟩, ?_⟩
      rcases S₀_cases z with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
      · simp only [arc1]; rw [← h]
      · linarith
      · linarith
    · rintro ⟨r, ⟨h0, h1⟩, hr⟩
      have : z.1.2 = r := by rw [← hr]; rfl
      exact ⟨this ▸ h0, this ▸ h1⟩
  rw [this]
  refine pre_of_ambient (isPreconnected_Ioo.image _ (continuousOn_arc1.mono fun r hr => hr.1)) ?_
  rintro _ ⟨r, ⟨h0, h1⟩, rfl⟩
  exact Or.inl ⟨h0, show r ≤ 1 by linarith, rfl⟩

lemma closure_C₁lo_subset (ε : ℝ) :
    closure (C₁lo ε) ⊆ {z : S₀ | z.1.1 ≤ 1 ∧ 0 ≤ z.1.2 ∧ z.1.2 ≤ ε} := by
  refine closure_minimal (fun z hz => ⟨x_le_one_of_pos z hz.1, hz.1.le, hz.2.le⟩) ?_
  exact (isClosed_le continuous_xc continuous_const).inter
    ((isClosed_le continuous_const continuous_hgt).inter
      (isClosed_le continuous_hgt continuous_const))

lemma bar_mem_closure_C₁lo {ε : ℝ} (hε : 0 < ε) {u : S₀} (hu0 : u.1.2 = 0) (hu1 : u.1.1 ≤ 1) :
    u ∈ closure (C₁lo ε) := by
  refine mem_closure_of_forall fun δ hδ => ?_
  obtain ⟨t, ht0, htδ, ht1, hct⟩ := exists_cA_eq (x_nonneg u) hu1 (lt_min hδ hε)
  refine ⟨c₁ ht0 ht1, ⟨ht0, htδ.trans_le (min_le_right _ _)⟩, ?_⟩
  rw [dist_S₀]
  simp only [c₁, hct, hu0, dist_self, Real.dist_eq, sub_zero, abs_of_pos ht0]
  exact max_lt hδ (htδ.trans_le (min_le_left _ _))

lemma bar_mem_interior_C₁lo {ε : ℝ} (hε : 0 < ε) {b : S₀} (hb0 : b.1.2 = 0) (hb1 : b.1.1 < 1) :
    b ∈ interior (closure (C₁lo ε)) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨min ε (1 - b.1.1), lt_min hε (by linarith), fun z hz => ?_⟩
  rw [mem_ball, dist_S₀] at hz
  have hx := (le_max_left _ _).trans_lt hz
  have hy := (le_max_right _ _).trans_lt hz
  rw [Real.dist_eq, abs_lt] at hx hy
  rw [hb0] at hy
  have h1 := min_le_left ε (1 - b.1.1)
  have h2 := min_le_right ε (1 - b.1.1)
  rcases S₀_cases z with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨-, h, -⟩
  · exact subset_closure ⟨h, by linarith⟩
  · exact bar_mem_closure_C₁lo hε h (by linarith)
  · linarith [one_le_x_of_neg z h]

lemma isContinuum_closure_C₁lo {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Fold.Q78.IsContinuum (closure (C₁lo ε)) := by
  obtain ⟨t, ht0, htε, ht1, -⟩ := exists_cA_eq (x := 0) le_rfl zero_le_one hε
  exact ⟨isClosed_closure.isCompact, ⟨c₁ ht0 ht1, subset_closure ⟨ht0, htε⟩⟩,
    (isPreconnected_C₁lo hε1).closure⟩

/-- A continuum containing a point of `[0,1] × {0}` interiorly contains `[0,1] × {0}`. -/
lemma barL_subset_of_interior {Z : Set S₀} (hZ : Fold.Q78.IsContinuum Z) {b : S₀}
    (hb0 : b.1.2 = 0) (hb1 : b.1.1 ≤ 1) (hbZ : b ∈ interior Z) : barL ⊆ Z := by
  rintro u ⟨hu0, hu1⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hbZ
  obtain ⟨ε, hε, hball⟩ := hbZ
  obtain ⟨t₁, ht₀, htε, ht₁, hct⟩ := exists_cA_eq (x_nonneg b) hb1 hε
  have hc₁Z : c₁ ht₀ ht₁ ∈ Z := hball (by
    rw [mem_ball, dist_S₀]
    simp only [c₁, hct, hb0, dist_self, Real.dist_eq, sub_zero, abs_of_pos ht₀]
    exact max_lt hε htε)
  have hbZ' : b ∈ Z := hball (mem_ball_self hε)
  rw [← hZ.1.isClosed.closure_eq]
  refine mem_closure_of_forall fun δ hδ => ?_
  obtain ⟨t, ht0, htδ, ht1, hct'⟩ := exists_cA_eq (x_nonneg u) hu1 (lt_min hδ ht₀)
  obtain ⟨v, hvZ, hv⟩ := exists_height hZ.2.2 hbZ' hc₁Z (s := t)
    ⟨by rw [hb0]; exact ht0.le, (htδ.trans_le (min_le_right _ _)).le⟩
  rw [eq_c₁ v ht0 ht1 hv] at hvZ
  refine ⟨_, hvZ, ?_⟩
  rw [dist_S₀]
  simp only [c₁, hct', hu0, dist_self, Real.dist_eq, sub_zero, abs_of_pos ht0]
  exact max_lt hδ (htδ.trans_le (min_le_left _ _))

/-- **Bing's element of a point of `[0,1) × {0}`** is `[0,1] × {0}`. -/
theorem gElt_bar {b : S₀} (hb0 : b.1.2 = 0) (hb1 : b.1.1 < 1) : gElt b = barL := by
  refine subset_antisymm (fun z hz => ?_) fun u hu =>
    mem_sInter.mpr fun Z ⟨hZ, hbZ⟩ => barL_subset_of_interior hZ hb0 hb1.le hbZ hu
  have key : ∀ ε, 0 < ε → ε ≤ 1 → z.1.1 ≤ 1 ∧ 0 ≤ z.1.2 ∧ z.1.2 ≤ ε := fun ε hε hε1 =>
    closure_C₁lo_subset ε (HPC.Plane.gElt_subset (isContinuum_closure_C₁lo hε hε1)
      (bar_mem_interior_C₁lo hε hb0 hb1) hz)
  obtain ⟨hx, hy0, -⟩ := key 1 one_pos le_rfl
  refine ⟨le_antisymm ?_ hy0, hx⟩
  by_contra hpos
  push_neg at hpos
  have := (key (min 1 (z.1.2 / 2)) (lt_min one_pos (by linarith)) (min_le_left _ _)).2.2
  linarith [min_le_right 1 (z.1.2 / 2)]

/-- **The decomposition space of `S₀` is not Hausdorff.** -/
theorem quotient_not_t2 : ¬ T2Space (Quotient (Setoid.ker (gElt (S := S₀)))) := by
  intro hT2
  have hne : (Quotient.mk _ p₀ : Quotient (Setoid.ker (gElt (S := S₀)))) ≠ Quotient.mk _ q₀ :=
    fun h => gElt_not_partition_S₀.2 (Quotient.exact h)
  obtain ⟨U, V, -, hV, hpU, hqV, hUV⟩ := t2_separation hne
  have hV' : IsOpen (Quotient.mk (Setoid.ker (gElt (S := S₀))) ⁻¹' V) :=
    hV.preimage continuous_quotient_mk'
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV' q₀ hqV
  set s := max (1 - δ / 2) (1 / 2) with hs
  have hs1 : s < 1 := max_lt (by linarith) (by norm_num)
  have hs0 : 0 ≤ s := le_max_of_le_right (by norm_num)
  have hmem : bar hs0 (by linarith) ∈ ball q₀ δ := by
    rw [mem_ball, dist_S₀]
    simp only [q₀, bar, dist_self, Real.dist_eq]
    rw [abs_of_neg (by linarith)]
    refine max_lt ?_ hδ
    have := le_max_left (1 - δ / 2) (1 / 2)
    linarith
  have hbV := hball hmem
  have hbp : (Quotient.mk _ (bar hs0 (by linarith)) : Quotient (Setoid.ker (gElt (S := S₀)))) =
      Quotient.mk _ p₀ := Quotient.sound (show gElt _ = gElt p₀ by
    rw [gElt_bar rfl hs1, gElt_bar (b := p₀) rfl (by simp [p₀, bar]; norm_num)])
  rw [mem_preimage, hbp] at hbV
  exact disjoint_left.mp hUV hpU hbV

/-- **`isArc_of_separatesPairs` is false**: for `S₀`, which satisfies Bing's standing hypothesis,
the quotient by `p ~ q ⇔ g p = g q` is not Hausdorff, hence not homeomorphic to `[0, 1]`. -/
theorem isArc_of_separatesPairs_false :
    ¬ ∀ (S : Type) [MetricSpace S] [CompactSpace S], BingS S →
      Nonempty (Quotient (Setoid.ker (gElt (S := S))) ≃ₜ unitInterval) := fun h => by
  obtain ⟨e⟩ := h S₀ bingS_S₀
  exact quotient_not_t2 e.isEmbedding.t2Space

end HPC.Plane.Counter92
