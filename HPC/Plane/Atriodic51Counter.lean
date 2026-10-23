import HPC.Plane.Atriodic51

-- Note (batch 93): the one-layer definition `gElt` refuted in this file is the batch-92
-- commission's transcription, not Bing's definition. Bing (p. 658) takes the intersection of "all
-- continua which contain interiorly a continuum that contains `p` interiorly". Bing's elements are
-- `bingElt` (`HPC/Plane/Atriodic51BElt.lean`, used in `HPC/Plane/Atriodic51B.lean`), and on `S₀`
-- they are the curve points and the bar (`Counter92.bingElt_curve`, `Counter92.bingElt_bar`).
/-!
# Batch 92: The one-layer elements `g p` need not partition — a planar example

`S₀ ⊆ ℝ × ℝ` is the union of
* `C₁ = {(c t, t) : 0 < t ≤ 1}` with `c t = (1 + sin (1/t)) / 2 ∈ [0, 1]`, a sine curve above the
  `x`-axis whose limit set is the segment `[0, 1] × {0}`;
* the segment `B = [0, 2] × {0}`;
* `C₂ = {(1 + c t, -t) : 0 < t ≤ 1}`, a sine curve below the `x`-axis whose limit set is
  `[1, 2] × {0}`.

For `p = (1/2, 0)`, `q = (1, 0)`, `x = (3/2, 0)`:
* `closure C₁ = C₁ ∪ [0,1] × {0}` is a continuum containing `p` interiorly and missing `x`, so
  `x ∉ g p`;
* every continuum containing `p` interiorly contains a tail of `C₁`, hence `q`: `q ∈ g p`;
* every continuum containing `q` interiorly contains a tail of `C₂`, hence `x`: `x ∈ g q`.

So `q ∈ g p` but `g p ≠ g q` (`gElt_not_partition_S₀`). This is the third conjunct of the
conclusion of `theorem8_1951`. `S₀` is snake-like (chainable) and therefore satisfies Bing's
standing hypothesis (atriodic, hereditarily unicoherent, hereditarily decomposable); that last
fact is **not** formalized here, so `theorem8_1951_false_of_bingS` is stated with `BingS S₀` as a
hypothesis.
-/

namespace HPC.Plane.Counter92

open Set Topology Metric

/-- The horizontal profile of the sine curves, with values in `[0, 1]`. -/
noncomputable def cA (t : ℝ) : ℝ := (1 + Real.sin (1 / t)) / 2

/-- The example continuum. -/
def S₀ : Set (ℝ × ℝ) :=
  {z | (0 < z.2 ∧ z.2 ≤ 1 ∧ z.1 = cA z.2) ∨ (z.2 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ 2) ∨
    (-1 ≤ z.2 ∧ z.2 < 0 ∧ z.1 = 1 + cA (-z.2))}

lemma cA_mem (t : ℝ) : 0 ≤ cA t ∧ cA t ≤ 1 := by
  unfold cA
  constructor <;> linarith [Real.neg_one_le_sin (1 / t), Real.sin_le_one (1 / t)]

lemma continuousOn_cA : ContinuousOn cA (Ioi 0) := by
  unfold cA
  refine ContinuousOn.div_const (continuousOn_const.add ?_) _
  exact Real.continuous_sin.comp_continuousOn
    (continuousOn_const.div continuousOn_id fun x hx => ne_of_gt hx)

/-- Every value in `[0, 1]` is taken by `cA` at arbitrarily small positive `t ≤ 1`. -/
lemma exists_cA_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧ t ≤ 1 ∧ cA t = x := by
  set a := Real.arcsin (2 * x - 1) with ha
  have ha1 : -(Real.pi / 2) ≤ a := Real.neg_pi_div_two_le_arcsin _
  have hsin : Real.sin a = 2 * x - 1 := Real.sin_arcsin (by linarith) (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hpi := Real.pi_gt_three
  set D := a + 2 * Real.pi * ((n : ℝ) + 1) with hD
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD1 : 1 < D := by nlinarith
  have hDε : 1 / ε < D := by nlinarith
  refine ⟨1 / D, by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by linarith)]
    rw [div_lt_iff₀ hε] at hDε
    linarith
  · rw [div_le_one (by linarith)]; linarith
  · unfold cA
    rw [one_div_one_div]
    have : Real.sin D = Real.sin a := by
      rw [hD]
      have := Real.sin_add_int_mul_two_pi a ((n : ℤ) + 1)
      push_cast at this
      rw [← this]; ring_nf
    rw [this, hsin]; ring

lemma S₀_eq : S₀ = (Icc 0 2 ×ˢ Icc (-1) 1) ∩ {z | z.2 ≤ 0 ∨ z.1 = cA z.2} ∩
    {z | 0 ≤ z.2 ∨ z.1 = 1 + cA (-z.2)} := by
  ext ⟨x, y⟩
  simp only [S₀, mem_setOf_eq, mem_inter_iff, mem_prod, mem_Icc]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · have := cA_mem y
      refine ⟨⟨⟨⟨by linarith, by linarith⟩, by linarith, h2⟩, Or.inr h3⟩, Or.inl h1.le⟩
    · subst h1
      exact ⟨⟨⟨⟨h2, h3⟩, by norm_num, by norm_num⟩, Or.inl le_rfl⟩, Or.inl le_rfl⟩
    · have := cA_mem (-y)
      refine ⟨⟨⟨⟨by linarith, by linarith⟩, h1, by linarith⟩, Or.inl h2.le⟩, Or.inr h3⟩
  · rintro ⟨⟨⟨⟨hx0, hx2⟩, hy0, hy1⟩, hP⟩, hN⟩
    rcases lt_trichotomy y 0 with hy | hy | hy
    · exact Or.inr (Or.inr ⟨hy0, hy, hN.resolve_left (by linarith)⟩)
    · exact Or.inr (Or.inl ⟨hy, hx0, hx2⟩)
    · exact Or.inl ⟨hy, hy1, hP.resolve_left (by linarith)⟩

lemma isClosed_S₀ : IsClosed S₀ := by
  rw [S₀_eq]
  refine ((isClosed_Icc.prod isClosed_Icc).inter ?_).inter ?_
  · rw [← isOpen_compl_iff]
    have : {z : ℝ × ℝ | z.2 ≤ 0 ∨ z.1 = cA z.2}ᶜ =
        {z : ℝ × ℝ | 0 < z.2} ∩ (fun z : ℝ × ℝ => z.1 - cA z.2) ⁻¹' {0}ᶜ := by
      ext z; simp only [mem_compl_iff, mem_setOf_eq, not_or, not_le, mem_inter_iff,
        mem_preimage, mem_singleton_iff, sub_eq_zero]
    rw [this]
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_lt continuous_const continuous_snd)
      isOpen_compl_singleton
    exact continuous_fst.continuousOn.sub
      (continuousOn_cA.comp continuous_snd.continuousOn fun z hz => hz)
  · rw [← isOpen_compl_iff]
    have : {z : ℝ × ℝ | 0 ≤ z.2 ∨ z.1 = 1 + cA (-z.2)}ᶜ =
        {z : ℝ × ℝ | z.2 < 0} ∩ (fun z : ℝ × ℝ => z.1 - (1 + cA (-z.2))) ⁻¹' {0}ᶜ := by
      ext z; simp only [mem_compl_iff, mem_setOf_eq, not_or, not_le, mem_inter_iff,
        mem_preimage, mem_singleton_iff, sub_eq_zero]
    rw [this]
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_lt continuous_snd continuous_const)
      isOpen_compl_singleton
    refine continuous_fst.continuousOn.sub (continuousOn_const.add ?_)
    exact continuousOn_cA.comp continuous_snd.neg.continuousOn fun z hz => by
      simp only [mem_setOf_eq] at hz; simp only [mem_Ioi]; linarith

lemma isCompact_S₀ : IsCompact S₀ := by
  refine ((isCompact_Icc (a := (0:ℝ)) (b := 2)).prod
    (isCompact_Icc (a := (-1:ℝ)) (b := 1))).of_isClosed_subset isClosed_S₀ ?_
  rw [S₀_eq]; exact fun z hz => hz.1.1

instance : CompactSpace S₀ := isCompact_iff_compactSpace.mp isCompact_S₀

/-- The point of `C₁` at height `t`. -/
noncomputable def c₁ {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : S₀ := ⟨(cA t, t), Or.inl ⟨h0, h1, rfl⟩⟩

/-- The point of `C₂` at depth `t`. -/
noncomputable def c₂ {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : S₀ :=
  ⟨(1 + cA t, -t), Or.inr (Or.inr ⟨by linarith, by linarith, by rw [neg_neg]⟩)⟩

/-- A bar point. -/
def bar {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2) : S₀ := ⟨(x, 0), Or.inr (Or.inl ⟨rfl, h0, h2⟩)⟩

lemma eq_c₁ (z : S₀) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hz : z.1.2 = t) : z = c₁ h0 h1 := by
  obtain ⟨⟨x, y⟩, hz'⟩ := z
  simp only at hz; subst hz
  rcases hz' with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
  · simp only at h; subst h; rfl
  · simp only at h; linarith
  · simp only at h; linarith

lemma eq_c₂ (z : S₀) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hz : z.1.2 = -t) : z = c₂ h0 h1 := by
  obtain ⟨⟨x, y⟩, hz'⟩ := z
  simp only at hz; subst hz
  rcases hz' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩
  · simp only at h; linarith
  · simp only at h; linarith
  · simp only [neg_neg] at h; subst h; rfl

lemma dist_S₀ (z w : S₀) : dist z w = max (dist z.1.1 w.1.1) (dist z.1.2 w.1.2) := by
  rw [Subtype.dist_eq, Prod.dist_eq]

/-- A preconnected subset of `S₀` meeting heights `a ≤ b` meets every height in between. -/
lemma exists_height {Z : Set S₀} (hZ : IsPreconnected Z) {z w : S₀} (hz : z ∈ Z) (hw : w ∈ Z)
    {s : ℝ} (hs : s ∈ Icc z.1.2 w.1.2) : ∃ u ∈ Z, u.1.2 = s := by
  have hc : Continuous fun u : S₀ => u.1.2 := continuous_snd.comp continuous_subtype_val
  obtain ⟨u, hu, rfl⟩ := (hZ.image _ hc.continuousOn).Icc_subset (mem_image_of_mem _ hz)
    (mem_image_of_mem _ hw) hs
  exact ⟨u, hu, rfl⟩

lemma mem_closure_of_forall {Z : Set S₀} {z : S₀}
    (h : ∀ ε > 0, ∃ w ∈ Z, dist w z < ε) : z ∈ closure Z :=
  Metric.mem_closure_iff.mpr fun ε hε => by
    obtain ⟨w, hw, hd⟩ := h ε hε
    exact ⟨w, hw, by rw [dist_comm]; exact hd⟩

/-- `p = (1/2, 0)`. -/
noncomputable def p₀ : S₀ := bar (x := 1 / 2) (by norm_num) (by norm_num)
/-- `q = (1, 0)`. -/
noncomputable def q₀ : S₀ := bar (x := 1) (by norm_num) (by norm_num)
/-- `x = (3/2, 0)`. -/
noncomputable def x₀ : S₀ := bar (x := 3 / 2) (by norm_num) (by norm_num)

/-- The curve `C₁` as a subset of `S₀`. -/
def C₁ : Set S₀ := {z | 0 < z.1.2}

lemma isConnected_C₁ : IsConnected C₁ := by
  have : C₁ = range fun t : Ioc (0 : ℝ) 1 => c₁ t.2.1 t.2.2 := by
    ext z
    constructor
    · intro hz
      have h1 : z.1.2 ≤ 1 := by
        rcases z.2 with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
        · exact h
        · exact absurd h (ne_of_gt hz)
        · exact absurd hz (not_lt.mpr h.le)
      exact ⟨⟨z.1.2, hz, h1⟩, (eq_c₁ z hz h1 rfl).symm⟩
    · rintro ⟨t, rfl⟩; exact t.2.1
  rw [this]
  haveI : ConnectedSpace (Ioc (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioc (by norm_num))
  refine isConnected_range ?_
  refine Continuous.subtype_mk ?_ _
  refine Continuous.prodMk ?_ continuous_subtype_val
  exact continuousOn_iff_continuous_restrict.mp
    (continuousOn_cA.mono fun (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) => ht.1)

/-- `closure C₁ ⊆ {x ≤ 1}`. -/
lemma closure_C₁_subset : closure C₁ ⊆ {z : S₀ | z.1.1 ≤ 1} := by
  refine closure_minimal ?_ (isClosed_le (continuous_fst.comp continuous_subtype_val)
    continuous_const)
  intro z hz
  rcases z.2 with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
  · simp only [mem_setOf_eq]; rw [h]; exact (cA_mem _).2
  · exact absurd h (ne_of_gt hz)
  · exact absurd hz (not_lt.mpr h.le)

lemma bar_mem_closure_C₁ {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    bar h0 (h1.trans (by norm_num)) ∈ closure C₁ := by
  refine mem_closure_of_forall fun ε hε => ?_
  obtain ⟨t, ht0, htε, ht1, hct⟩ := exists_cA_eq h0 h1 hε
  refine ⟨c₁ ht0 ht1, ht0, ?_⟩
  rw [dist_S₀]
  simp only [c₁, bar, hct, dist_self, Real.dist_eq, sub_zero, abs_of_pos ht0]
  exact max_lt hε htε

/-- `p` is interior to `closure C₁`. -/
lemma p₀_mem_interior : p₀ ∈ interior (closure C₁) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨1 / 4, by norm_num, fun z hz => ?_⟩
  rw [mem_ball, dist_S₀] at hz
  have hx := (le_max_left _ _).trans_lt hz
  have hy := (le_max_right _ _).trans_lt hz
  simp only [p₀, bar, Real.dist_eq, sub_zero] at hx hy
  rw [abs_lt] at hx hy
  rcases z.2 with ⟨h, -⟩ | ⟨h, h0, -⟩ | ⟨-, -, h⟩
  · exact subset_closure h
  · have : z = bar h0 (by linarith) := Subtype.ext (Prod.ext rfl h)
    rw [this]; exact bar_mem_closure_C₁ h0 (by linarith)
  · have := (cA_mem (-z.1.2)).1
    linarith

lemma isContinuum_closure_C₁ : Fold.Q78.IsContinuum (closure C₁) :=
  ⟨isClosed_closure.isCompact, isConnected_C₁.closure⟩

/-- `x ∉ g p`. -/
lemma x₀_not_mem_gElt_p₀ : x₀ ∉ gElt p₀ := fun h => by
  have := closure_C₁_subset (HPC.Plane.gElt_subset isContinuum_closure_C₁ p₀_mem_interior h)
  simp only [x₀, bar, mem_setOf_eq] at this
  norm_num at this

/-- `q ∈ g p`: a continuum containing `p` interiorly contains a tail of `C₁`. -/
lemma q₀_mem_gElt_p₀ : q₀ ∈ gElt p₀ := by
  refine mem_sInter.mpr fun Z ⟨hZ, hpZ⟩ => ?_
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hpZ
  obtain ⟨ε, hε, hball⟩ := hpZ
  obtain ⟨t₁, ht₀, htε, ht₁, hct⟩ := exists_cA_eq (x := 1 / 2) (by norm_num) (by norm_num) hε
  have hc₁Z : c₁ ht₀ ht₁ ∈ Z := hball (by
    rw [mem_ball, dist_S₀]
    simp only [c₁, p₀, bar, hct, dist_self, Real.dist_eq, sub_zero, abs_of_pos ht₀]
    exact max_lt hε htε)
  have hpZ' : p₀ ∈ Z := hball (mem_ball_self hε)
  rw [← hZ.1.isClosed.closure_eq]
  refine mem_closure_of_forall fun δ hδ => ?_
  obtain ⟨t, ht0, htδ, ht1, hct'⟩ := exists_cA_eq (x := 1) (by norm_num) le_rfl
    (lt_min hδ ht₀)
  obtain ⟨u, huZ, hu⟩ := exists_height hZ.2.2 hpZ' hc₁Z (s := t)
    ⟨by simp [p₀, bar]; exact ht0.le, (htδ.trans_le (min_le_right _ _)).le⟩
  rw [eq_c₁ u ht0 ht1 hu] at huZ
  refine ⟨_, huZ, ?_⟩
  rw [dist_S₀]
  simp only [c₁, q₀, bar, hct', dist_self, Real.dist_eq, sub_zero, abs_of_pos ht0]
  exact max_lt hδ (htδ.trans_le (min_le_left _ _))

/-- `x ∈ g q`: a continuum containing `q` interiorly contains a tail of `C₂`. -/
lemma x₀_mem_gElt_q₀ : x₀ ∈ gElt q₀ := by
  refine mem_sInter.mpr fun Z ⟨hZ, hqZ⟩ => ?_
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hqZ
  obtain ⟨ε, hε, hball⟩ := hqZ
  obtain ⟨t₁, ht₀, htε, ht₁, hct⟩ := exists_cA_eq (x := 0) le_rfl (by norm_num) hε
  have hc₂Z : c₂ ht₀ ht₁ ∈ Z := hball (by
    rw [mem_ball, dist_S₀]
    simp only [c₂, q₀, bar, hct, add_zero, dist_self, Real.dist_eq, sub_zero, abs_neg,
      abs_of_pos ht₀]
    exact max_lt hε htε)
  have hqZ' : q₀ ∈ Z := hball (mem_ball_self hε)
  rw [← hZ.1.isClosed.closure_eq]
  refine mem_closure_of_forall fun δ hδ => ?_
  obtain ⟨t, ht0, htδ, ht1, hct'⟩ := exists_cA_eq (x := 1 / 2) (by norm_num) (by norm_num)
    (lt_min hδ ht₀)
  obtain ⟨u, huZ, hu⟩ := exists_height hZ.2.2 hc₂Z hqZ' (s := -t)
    ⟨by simp only [c₂]; linarith [htδ.trans_le (min_le_right _ _)],
      by simp [q₀, bar]; exact ht0.le⟩
  rw [eq_c₂ u ht0 ht1 hu] at huZ
  refine ⟨_, huZ, ?_⟩
  rw [dist_S₀]
  simp only [c₂, x₀, bar, hct', Real.dist_eq]
  have := htδ.trans_le (min_le_left _ _)
  refine max_lt ?_ ?_
  · norm_num; exact hδ
  · rw [sub_zero, abs_neg, abs_of_pos ht0]; exact this

/-- **The one-layer elements do not partition `S₀`**: `q ∈ g p` but `g p ≠ g q`. -/
theorem gElt_not_partition_S₀ : q₀ ∈ gElt p₀ ∧ gElt p₀ ≠ gElt q₀ :=
  ⟨q₀_mem_gElt_p₀, fun h => x₀_not_mem_gElt_p₀ (h ▸ x₀_mem_gElt_q₀)⟩

/-- The partition clause of Theorem 8 fails for `S₀`. -/
theorem not_partition_S₀ : ¬ ∀ p q : S₀, q ∈ gElt p → gElt p = gElt q := fun h =>
  gElt_not_partition_S₀.2 (h _ _ gElt_not_partition_S₀.1)

/-- **`theorem8_1951` (the one-layer reading) is false as soon as `S₀` satisfies Bing's standing hypothesis** (which it
does, being snake-like; not formalized here). Its conclusion fails for `S₀` at the third conjunct
(`q ∈ g p → g p = g q`). -/
theorem theorem8_1951_false_of_bingS (hS : BingS S₀) :
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
        ∀ M : Set S, Fold.Q78.IsContinuum M → r ∈ M → s ∈ M → M = univ) := fun h =>
  not_partition_S₀ (h S₀ hS).2.2.1

end HPC.Plane.Counter92
