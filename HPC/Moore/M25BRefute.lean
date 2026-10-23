import HPC.Moore.M25BPts

/-!
# Batch 146: the printed statements refuted (Theorems 2, 7, 10, 11; Mullikin's Theorem 5)

All examples live in the decomposition of the plane into its points (`M25BPts.lean`).
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

/-! ## Theorem 2 as printed -/

/-- The slit disc: the open (sup-metric) unit disc minus the radius `[0, 1/2] × {0}`. -/
def slitDisc : Set Pt := ball (0 : Pt) 1 \ hseg 0 (1 / 2) 0

theorem mem_ball_zero_one {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) : ((x, y) : Pt) ∈ ball (0 : Pt) 1 := by
  rw [mem_ball, Prod.dist_eq]
  simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
  exact max_lt hx hy

theorem isOpen_slitDisc : IsOpen slitDisc :=
  isOpen_ball.sdiff (isCompact_hseg _ _ _).isClosed

theorem isConnected_slitDisc : IsConnected slitDisc :=
  isConnected_convex_diff_hseg (convex_ball _ _) (show (-1 / 2 : ℝ) < 0 by norm_num)
    (show (1 / 2 : ℝ) < 3 / 4 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (mem_ball_zero_one (by norm_num [abs_of_neg]) (by norm_num [abs_of_pos]))
    (mem_ball_zero_one (by norm_num [abs_of_neg]) (by norm_num [abs_of_neg]))
    (mem_ball_zero_one (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos]))

theorem hseg_subset_frontier_slitDisc : hseg 0 (1 / 2) 0 ⊆ frontier slitDisc := by
  intro z hz
  refine ⟨hseg_subset_closure (s := slitDisc) (fun w hw δ hδ hδ' => ?_) hz, ?_⟩
  · refine ⟨?_, ?_⟩
    swap
    · rintro ⟨-, h⟩
      have : (0 : ℝ) + δ = 0 := h
      linarith
    obtain ⟨⟨h1, h2⟩, -⟩ := hw
    exact mem_ball_zero_one (by rw [abs_lt]; constructor <;> linarith)
      (by rw [abs_lt]; constructor <;> linarith)
  · rw [isOpen_slitDisc.interior_eq]
    exact fun h => h.2 hz

/-- **Theorem 2 under the printed definitions is false.** Decomposition into points; `M` the closed
unit disc, `D` the open disc minus the radius `T = [0, 1/2] × {0}`, `E` the plane minus `T`. Then `E`
is an unbounded complementary domain, in the printed sense, of the boundary of `D` (its boundary `T`
lies in the boundary of `D`), and the omission of the element `(1/4, 0)` disconnects `T`. -/
theorem not_m25_theorem2_printed :
    ¬ ∀ (r : Setoid Pt), MooreDecomp r →
      ∀ M D E : Set (Quotient r), IsClosed M → IsConnected M → Bornology.IsBounded (ptsOf r M) →
        IsComplDomPrinted M D → Bornology.IsBounded (ptsOf r D) →
        IsComplDomPrinted (frontier D) E → ¬ Bornology.IsBounded (ptsOf r E) →
        ∀ p ∈ frontier E, IsConnected (frontier E) ∧ IsConnected (frontier E \ {p}) := by
  intro h
  set T := hseg 0 (1 / 2) 0
  have hT := isCompact_hseg 0 (1 / 2) 0
  have hpT : ((1 / 4, 0) : Pt) ∈ T := ⟨⟨by norm_num, by norm_num⟩, rfl⟩
  have key := h ptSetoid mooreDecomp_ptSetoid (ptHomeo '' closedBall 0 1) (ptHomeo '' slitDisc)
    (ptHomeo '' Tᶜ) (ptHomeo.isClosed_image.2 isClosed_closedBall)
    (ptHomeo.isConnected_image.2 ⟨⟨0, mem_closedBall_self zero_le_one⟩,
      (convex_closedBall _ _).isPreconnected⟩)
    (by rw [ptsOf_ptHomeo_image]; exact isBounded_closedBall)
    ⟨ptHomeo.isOpen_image.2 isOpen_slitDisc, ptHomeo.isConnected_image.2 isConnected_slitDisc, by
      rw [← ptHomeo.image_frontier]
      refine image_mono (frontier_subset_closure.trans (closure_minimal ?_ isClosed_closedBall))
      exact diff_subset.trans ball_subset_closedBall⟩
    (by rw [ptsOf_ptHomeo_image]; exact isBounded_ball.subset diff_subset)
    ⟨ptHomeo.isOpen_image.2 hT.isClosed.isOpen_compl,
      ptHomeo.isConnected_image.2 (isConnected_compl_hseg _ _ _), by
      rw [← ptHomeo.image_frontier, ← ptHomeo.image_frontier, frontier_compl_hseg]
      exact image_mono hseg_subset_frontier_slitDisc⟩
    (by
      rw [ptsOf_ptHomeo_image]
      intro hb
      apply NormedSpace.unbounded_univ ℝ Pt
      rw [← union_compl_self T]
      exact hT.isBounded.union hb)
    (ptHomeo (1 / 4, 0))
    (by rw [← ptHomeo.image_frontier, frontier_compl_hseg]; exact mem_image_of_mem _ hpT)
  have hc := key.2
  rw [← ptHomeo.image_frontier, frontier_compl_hseg, ← image_singleton,
    ← image_diff ptHomeo.injective, ptHomeo.isConnected_image] at hc
  have ha : ((0 : ℝ), (0 : ℝ)) ∈ T \ {((1 / 4 : ℝ), (0 : ℝ))} :=
    ⟨⟨⟨le_rfl, by norm_num⟩, rfl⟩, by simp⟩
  have hb : ((1 / 2 : ℝ), (0 : ℝ)) ∈ T \ {((1 / 4 : ℝ), (0 : ℝ))} :=
    ⟨⟨⟨by norm_num, le_rfl⟩, rfl⟩, by simp⟩
  refine not_isPreconnected_of_split (u := {p : Pt | p.1 < 1 / 4}) (v := {p : Pt | 1 / 4 < p.1})
    (isOpen_lt continuous_fst continuous_const) (isOpen_lt continuous_const continuous_fst)
    (disjoint_left.2 fun z (h1 : z.1 < 1 / 4) (h2 : 1 / 4 < z.1) => lt_asymm h1 h2) ?_
    ha (show (0 : ℝ) < 1 / 4 by norm_num) hb (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
    hc.isPreconnected
  rintro z ⟨⟨-, hz2⟩, hz⟩
  rcases lt_trichotomy z.1 (1 / 4) with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd (Prod.ext h1 (mem_singleton_iff.1 hz2)) hz
  · exact Or.inr h1


/-! ## Theorems 10 and 11 as printed -/

/-- Two disjoint parallel segments. -/
def twoSegs : Set Pt := hseg 0 1 0 ∪ hseg 0 1 1

theorem exists_mem_hseg_ne {a b : ℝ} (h : a < b) (c : ℝ) (x y : Pt) :
    ∃ z ∈ hseg a b c, z ≠ x ∧ z ≠ y := by
  have hinf : (hseg a b c).Infinite := by
    rw [hseg, prod_singleton]
    exact (Icc_infinite h).image fun s _ t _ hst => (Prod.mk.inj hst).1
  obtain ⟨z, hz, hz'⟩ := (hinf.diff (toFinite {x, y})).nonempty
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz'
  exact ⟨z, hz, hz'⟩

theorem twoSegs_subset : twoSegs ⊆ {p : Pt | p.2 < 1 / 2} ∪ {p | 1 / 2 < p.2} := by
  rintro z (⟨-, h⟩ | ⟨-, h⟩) <;> rw [mem_singleton_iff] at h
  · left; show z.2 < 1 / 2; rw [h]; norm_num
  · right; show 1 / 2 < z.2; rw [h]; norm_num

theorem isOpen_snd_lt_half : IsOpen {p : Pt | p.2 < 1 / 2} :=
  isOpen_lt continuous_snd continuous_const

theorem isOpen_snd_gt_half : IsOpen {p : Pt | 1 / 2 < p.2} :=
  isOpen_lt continuous_const continuous_snd

theorem disjoint_snd_half : Disjoint {p : Pt | p.2 < 1 / 2} {p | 1 / 2 < p.2} :=
  disjoint_left.2 fun x (h1 : x.2 < 1 / 2) (h2 : 1 / 2 < x.2) => lt_asymm h1 h2

theorem isConnected_compl_twoSegs : IsConnected twoSegsᶜ := by
  have e : twoSegsᶜ = ({p : Pt | 1 / 4 < p.2} \ hseg 0 1 1) ∪ ({p : Pt | p.2 < 3 / 4} \ hseg 0 1 0) := by
    ext p
    simp only [twoSegs, hseg, mem_compl_iff, mem_union, mem_diff, mem_prod, mem_Icc,
      mem_singleton_iff, mem_setOf_eq]
    constructor
    · intro h
      by_cases hp : 1 / 4 < p.2
      · exact Or.inl ⟨hp, fun h' => h (Or.inr h')⟩
      · exact Or.inr ⟨by linarith, fun h' => h (Or.inl h')⟩
    · rintro (⟨hp, h⟩ | ⟨hp, h⟩) (⟨hx, h'⟩ | ⟨hx, h'⟩)
      · linarith
      · exact h ⟨hx, h'⟩
      · exact h ⟨hx, h'⟩
      · linarith
  rw [e]
  refine IsConnected.union ⟨(-1, 1 / 2), ⟨by norm_num, fun h => by norm_num [hseg] at h⟩,
      ⟨by norm_num, fun h => by norm_num [hseg] at h⟩⟩
    (isConnected_convex_diff_hseg (convex_snd_gt _) (show (-1 : ℝ) < 0 by norm_num)
      (show (1 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 1 / 4 by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
    (isConnected_convex_diff_hseg (convex_snd_lt _) (show (-1 : ℝ) < 0 by norm_num)
      (show (1 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 1 / 4 by norm_num)
      (by norm_num) (by norm_num) (by norm_num))

/-- Two disjoint segments, as a set of elements of the decomposition into points, are a simple
closed curve in the printed sense. -/
theorem isSCCEltPrinted_twoSegs : IsSCCEltPrinted (ptHomeo '' twoSegs) := by
  refine ⟨?_, ?_⟩
  · rw [ptsOf_ptHomeo_image]
    exact ((isCompact_hseg _ _ _).union (isCompact_hseg _ _ _)).isBounded
  rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ - hc
  rw [← image_singleton, ← image_insert_eq, ← image_diff ptHomeo.injective,
    ptHomeo.isConnected_image] at hc
  obtain ⟨z₀, hz₀, hz₀x, hz₀y⟩ := exists_mem_hseg_ne (zero_lt_one' ℝ) 0 x y
  obtain ⟨z₁, hz₁, hz₁x, hz₁y⟩ := exists_mem_hseg_ne (zero_lt_one' ℝ) 1 x y
  refine not_isPreconnected_of_split isOpen_snd_lt_half isOpen_snd_gt_half disjoint_snd_half
    (diff_subset.trans twoSegs_subset) (a := z₀) ⟨Or.inl hz₀, by simp [hz₀x, hz₀y]⟩ ?_
    (b := z₁) ⟨Or.inr hz₁, by simp [hz₁x, hz₁y]⟩ ?_ hc.isPreconnected
  · show z₀.2 < 1 / 2; rw [mem_singleton_iff.1 hz₀.2]; norm_num
  · show 1 / 2 < z₁.2; rw [mem_singleton_iff.1 hz₁.2]; norm_num

/-- **Theorem 10 under the printed definition of simple closed curve is false**: in the
decomposition into points, two disjoint segments form a bounded set disconnected by the omission of
any two of its elements, and it is not the union of two arcs from `(0, 0)` to `(1, 0)` (each such
arc is connected, hence lies in the lower segment). -/
theorem not_m25_theorem10_printed :
    ¬ ∀ (r : Setoid Pt), MooreDecomp r →
      ∀ J : Set (Quotient r), IsSCCEltPrinted J → ∀ p ∈ J, ∀ q ∈ J, p ≠ q →
        ∃ a b, IsArcElt p q a ∧ IsArcElt p q b ∧ a ∪ b = J ∧ a ∩ b = {p, q} := by
  intro h
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ twoSegs := Or.inl ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ twoSegs := Or.inl ⟨⟨zero_le_one, le_rfl⟩, rfl⟩
  have h2 : ((0 : ℝ), (1 : ℝ)) ∈ twoSegs := Or.inr ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  obtain ⟨a, b, ha, hb, hab, -⟩ := h ptSetoid mooreDecomp_ptSetoid _ isSCCEltPrinted_twoSegs
    _ (mem_image_of_mem _ h0) _ (mem_image_of_mem _ h1)
    (fun e => by simpa using ptHomeo.injective e)
  -- an arc of the family containing `(0, 0)` lies in the lower half plane
  have low : ∀ c : Set (Quotient ptSetoid), IsConnected c → ptHomeo (0, 0) ∈ c →
      c ⊆ ptHomeo '' twoSegs → ptHomeo ⁻¹' c ⊆ {p : Pt | p.2 < 1 / 2} := by
    intro c hc h0c hcJ
    have hsub : ptHomeo ⁻¹' c ⊆ twoSegs := by
      intro z hz
      obtain ⟨w, hw, hwz⟩ := hcJ hz
      rwa [← ptHomeo.injective hwz]
    rcases (ptHomeo.isPreconnected_preimage.2 hc.isPreconnected).subset_or_subset
        isOpen_snd_lt_half isOpen_snd_gt_half disjoint_snd_half (hsub.trans twoSegs_subset) with
      hl | hl
    · exact hl
    · have : ((0 : ℝ), (0 : ℝ)) ∈ {p : Pt | 1 / 2 < p.2} := hl h0c
      norm_num at this
  have hla := low a ha.2.2.1 ha.2.2.2.2.1 (hab ▸ subset_union_left)
  have hlb := low b hb.2.2.1 hb.2.2.2.2.1 (hab ▸ subset_union_right)
  have : ptHomeo (0, 1) ∈ a ∪ b := hab ▸ mem_image_of_mem _ h2
  rcases this with h' | h'
  · have : ((0 : ℝ), (1 : ℝ)) ∈ {p : Pt | p.2 < 1 / 2} := hla h'
    norm_num at this
  · have : ((0 : ℝ), (1 : ℝ)) ∈ {p : Pt | p.2 < 1 / 2} := hlb h'
    norm_num at this

/-- The complement of `ptHomeo '' S` is not the union of two disjoint nonempty open sets when the
complement of `S` is connected. -/
theorem no_two_domains_of_isConnected_compl {S : Set Pt} (hS : IsConnected Sᶜ)
    {I E : Set (Quotient ptSetoid)} (hI : IsOpen I) (hIc : IsConnected I) (hE : IsOpen E)
    (hEc : IsConnected E) (hIE : Disjoint I E) (h : I ∪ E = (ptHomeo '' S)ᶜ) : False := by
  rw [← ptHomeo.image_compl] at h
  exact false_of_split (ptHomeo.isConnected_image.2 hS).isPreconnected hI hE hIc.nonempty
    hEc.nonempty hIE h

/-- **Theorem 11 under the printed definition is false** (same example: the complement of two
disjoint segments is connected). -/
theorem not_m25_theorem11_printed :
    ¬ ∀ (r : Setoid Pt), MooreDecomp r →
      ∀ J : Set (Quotient r), IsSCCEltPrinted J → J.Nonempty →
        ∃ I E : Set (Quotient r), IsOpen I ∧ IsConnected I ∧ IsOpen E ∧ IsConnected E ∧
          Disjoint I E ∧ I ∪ E = Jᶜ := by
  intro h
  obtain ⟨I, E, hI, hIc, hE, hEc, hIE, hIEJ⟩ := h ptSetoid mooreDecomp_ptSetoid _
    isSCCEltPrinted_twoSegs ⟨_, mem_image_of_mem _
      (show ((0 : ℝ), (0 : ℝ)) ∈ twoSegs from Or.inl ⟨⟨le_rfl, zero_le_one⟩, rfl⟩)⟩
  exact no_two_domains_of_isConnected_compl isConnected_compl_twoSegs hI hIc hE hEc hIE hIEJ

/-- **Theorem 11 needs `J.Nontrivial`** (the condition added in the corrected definition
`IsSCCElt`): a single element is closed, connected, bounded and (vacuously) disconnected by the
omission of any two of its elements, but its complement is connected. -/
theorem not_m25_theorem11_singleton :
    ¬ ∀ (r : Setoid Pt), MooreDecomp r →
      ∀ J : Set (Quotient r), IsClosed J → IsConnected J → IsSCCEltPrinted J →
        ∃ I E : Set (Quotient r), IsOpen I ∧ IsConnected I ∧ IsOpen E ∧ IsConnected E ∧
          Disjoint I E ∧ I ∪ E = Jᶜ := by
  intro h
  have hJ : ptHomeo '' {(0 : Pt)} = {ptHomeo 0} := image_singleton
  obtain ⟨I, E, hI, hIc, hE, hEc, hIE, hIEJ⟩ := h ptSetoid mooreDecomp_ptSetoid
    (ptHomeo '' {(0 : Pt)}) (ptHomeo.isClosed_image.2 isClosed_singleton)
    (ptHomeo.isConnected_image.2 isConnected_singleton)
    ⟨by rw [ptsOf_ptHomeo_image]; exact Bornology.isBounded_singleton, by
      rw [hJ]
      rintro x hx y hy hxy
      exact absurd ((mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm) hxy⟩
  exact no_two_domains_of_isConnected_compl (isConnected_compl_singleton_pt 0) hI hIc hE hEc hIE
    hIEJ

/-! ## Mullikin's Theorem 5 as printed -/

/-- **Mullikin 1922, Theorem 5, as printed, is false.** `M₁ = M₂ = [0, 1/2] × {0}`,
`K₁ = [0, 1/4) × {0}`, `K₂ = [1/4, 1/2] × {0}`: all hypotheses hold (`K₁`, `K₂` are mutually
exclusive connected sets whose sum is `M₁ ∩ M₂`), but `S − M₁ − M₂` is connected. -/
theorem not_mullikin_theorem5_printed :
    ¬ ∀ M₁ M₂ K₁ K₂ : Set Pt, IsCompact M₁ → IsConnected M₁ → IsCompact M₂ → IsConnected M₂ →
      ¬ SeparatesPlane M₁ → ¬ SeparatesPlane M₂ → M₁ ∩ M₂ = K₁ ∪ K₂ → IsConnected K₁ →
      IsConnected K₂ → Disjoint K₁ K₂ →
      ∃ U V : Set Pt, IsOpen U ∧ IsConnected U ∧ IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
        U ∪ V = (M₁ ∪ M₂)ᶜ := by
  intro h
  have hM := isCompact_hseg 0 (1 / 2) 0
  have hMc := isConnected_hseg (show (0 : ℝ) ≤ 1 / 2 by norm_num) 0
  have hs : ¬ SeparatesPlane (hseg 0 (1 / 2) 0) := by
    rw [SeparatesPlane, not_not]; exact isConnected_compl_hseg _ _ _
  obtain ⟨U, V, hU, hUc, hV, hVc, hUV, hUVeq⟩ := h _ _ (Ico 0 (1 / 4) ×ˢ {0}) (hseg (1 / 4) (1 / 2) 0)
    hM hMc hM hMc hs hs
    (by rw [inter_self, hseg, hseg, ← union_prod, Ico_union_Icc_eq_Icc (by norm_num) (by norm_num)])
    ((isConnected_Ico (by norm_num)).prod isConnected_singleton)
    (isConnected_hseg (by norm_num) 0)
    (disjoint_left.2 fun z hz1 hz2 => by
      have h1 := hz1.1.2
      have h2 := hz2.1.1
      linarith)
  rw [union_self] at hUVeq
  exact false_of_split (isConnected_compl_hseg _ _ _).isPreconnected hU hV hUc.nonempty
    hVc.nonempty hUV hUVeq


/-! ## Theorem 7 as printed -/

/-- The horizontal axis, as elements of the decomposition into points. -/
def ptLine (t : ℝ) : Quotient ptSetoid := ptHomeo (t, 0)

theorem isEmbedding_ptLine : IsEmbedding ptLine :=
  ptHomeo.isEmbedding.comp (Function.LeftInverse.isEmbedding (f := Prod.fst)
    (g := fun t : ℝ => ((t, 0) : Pt)) (fun _ => rfl) continuous_fst
    (continuous_id.prodMk continuous_const))

theorem ptLine_injective : Function.Injective ptLine := isEmbedding_ptLine.injective

theorem isCutArc_Icc_real {a b : ℝ} (h : a < b) : IsCutArc a b (Icc a b) :=
  ⟨h.ne, isCompact_Icc, isConnected_Icc h.le, left_mem_Icc.2 h.le, right_mem_Icc.2 h.le,
    fun x hx hxa hxb hc => by
      have := hc.isPreconnected.Icc_subset (a := a) (b := b) ⟨left_mem_Icc.2 h.le, hxa.symm⟩
        ⟨right_mem_Icc.2 h.le, hxb.symm⟩ hx
      exact this.2 rfl⟩

theorem isArcElt_ptLine {a b : ℝ} (h : a < b) :
    IsArcElt (ptLine a) (ptLine b) (ptLine '' Icc a b) := by
  have himg : ptLine '' Icc a b = ptHomeo '' ((fun t : ℝ => ((t, 0) : Pt)) '' Icc a b) :=
    (image_image (fun x : Pt => ptHomeo x) (fun t : ℝ => ((t, 0) : Pt)) _).symm
  refine ((isCutArc_Icc_real h).image isEmbedding_ptLine).isArcElt ?_ ?_
  · rw [himg, ptHomeo.isClosed_image]
    exact (isCompact_Icc.image (continuous_id.prodMk continuous_const)).isClosed
  · rw [himg, ptsOf_ptHomeo_image]
    exact (isCompact_Icc.image (continuous_id.prodMk continuous_const)).isBounded

theorem accPt_zero_Ioc : AccPt (0 : ℝ) (Filter.principal (Ioc 0 (1 / 4))) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  have h1 : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
  have h2 := min_le_left ε (1 / 4)
  have h3 := min_le_right ε (1 / 4)
  refine ⟨min ε (1 / 4) / 2, ⟨hεU ?_, by constructor <;> linarith⟩, by positivity⟩
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

/-- **Theorem 7 as printed is false** ("then `p` is a limit element of the set `H`", with `p` the
extremity of the arc `pq`). *Restated* (the skeleton's placeholder was `True`): the printed
equivalence, with `AccPt p` on the left. Counterexample in the decomposition into points:
`pq = [0, 1] × {0}`, `x = (1/2, 0)`, `H = (0, 1/4] × {0}`. The extremity `p = (0, 0)` is a limit
element of `H`, but the arc `[3/8, 5/8] × {0}` contains `x`, not as an extremity, and no element of
`H`. -/
theorem not_m25_theorem7_printed :
    ¬ ∀ (r : Setoid Pt), MooreDecomp r → ∀ (p q x : Quotient r) (K H : Set (Quotient r)),
      IsArcElt p q K → x ∈ K → x ≠ p → x ≠ q → H ⊆ K →
      (AccPt p (Filter.principal H) ↔
        ∀ a b L, IsArcElt a b L → L ⊆ K → x ∈ L → x ≠ a → x ≠ b → ∃ h ∈ H ∩ L, h ≠ x) := by
  intro h
  have hx : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have key := h ptSetoid mooreDecomp_ptSetoid (ptLine 0) (ptLine 1) (ptLine (1 / 2))
    (ptLine '' Icc 0 1) (ptLine '' Ioc 0 (1 / 4)) (isArcElt_ptLine one_pos)
    (mem_image_of_mem _ hx) (fun e => by norm_num at e; exact absurd (ptLine_injective e) (by norm_num))
    (fun e => absurd (ptLine_injective e) (by norm_num))
    (image_mono fun t ht => ⟨ht.1.le, by linarith [ht.2]⟩)
  have hacc : AccPt (ptLine 0) (Filter.principal (ptLine '' Ioc 0 (1 / 4))) := by
    rw [← Filter.map_principal]
    exact accPt_zero_Ioc.map isEmbedding_ptLine.continuous.continuousAt ptLine_injective
  obtain ⟨_, ⟨⟨s, hs, rfl⟩, ⟨t, ht, hst⟩⟩, -⟩ := key.1 hacc (ptLine (3 / 8)) (ptLine (5 / 8))
    (ptLine '' Icc (3 / 8) (5 / 8)) (isArcElt_ptLine (by norm_num))
    (image_mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (mem_image_of_mem _ ⟨by norm_num, by norm_num⟩)
    (fun e => absurd (ptLine_injective e) (by norm_num))
    (fun e => absurd (ptLine_injective e) (by norm_num))
  have := ptLine_injective hst
  linarith [hs.2, ht.1]


/-! ## Moore 1920, Theorem 4, at a one-point set -/

/-- **Moore 1920, Theorem 4, as printed, fails for a one-point set.** Definition 4 (p. 342: "A simple
closed curve is a closed, connected, and bounded point-set which is disconnected by the omission of
any two of its points") is satisfied vacuously by a single point, which is not the sum of two simple
continuous arcs (an arc has two distinct end points). The conclusion is weakened here to "the union
of two cut-point arcs" (the clause "that have only their end points in common" is dropped), which
makes the refutation stronger. -/
theorem not_moore1920_theorem4_singleton :
    ¬ ∀ M : Set Pt, IsClosed M → IsConnected M → Bornology.IsBounded M →
      (∀ x ∈ M, ∀ y ∈ M, x ≠ y → ¬ IsConnected (M \ {x, y})) →
      ∃ (A B C D : Pt) (a b : Set Pt), IsCutArc A B a ∧ IsCutArc C D b ∧ a ∪ b = M := by
  intro h
  obtain ⟨A, B, C, D, a, b, ha, -, hab⟩ := h {0} isClosed_singleton isConnected_singleton
    Bornology.isBounded_singleton (fun x hx y hy hxy =>
      absurd ((mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm) hxy)
  have hA : A ∈ ({0} : Set Pt) := hab ▸ Or.inl ha.2.2.2.1
  have hB : B ∈ ({0} : Set Pt) := hab ▸ Or.inl ha.2.2.2.2.1
  exact ha.1 ((mem_singleton_iff.1 hA).trans (mem_singleton_iff.1 hB).symm)

end HPC.Moore
