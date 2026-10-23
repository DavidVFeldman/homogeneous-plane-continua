import HPC.HO16.KM77

/-!
# Batch 193, §4: H–O Theorem 8, (1) ⇒ (2), the core

Commission 193, §4; skeleton `HO16A.lean`, statement `ho16_theorem8_core` (unchanged).
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane

/-! ## §4. H–O Theorem 8, (1) ⇒ (2): the core (commission §4) -/

/-- What the proof of Theorem 8 uses of a fan. -/
theorem IsFanAt.props {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A Y : Set E} {y : E}
    {r : ℝ} (h : IsFanAt A y r Y) :
    IsClosed Y ∧ Y ⊆ A ∧ (∀ p ∈ Y, segment ℝ y p ⊆ Y) ∧ Y ∈ 𝓝[A] y ∧ Y ⊆ ball y r := by
  obtain ⟨n, z, -, rfl, hYA, -, hnhds, hdiam⟩ := h
  have hcpt : IsCompact (insert y (⋃ k, segment ℝ y (z k))) :=
    (isCompact_iUnion fun k => by
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous).insert y
  refine ⟨hcpt.isClosed, hYA, fun p hp => ?_, hnhds, fun p hp => ?_⟩
  · rcases hp with rfl | hp
    · rw [segment_same]
      exact singleton_subset_iff.2 (mem_insert _ _)
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hp
      exact ((convex_segment y (z k)).segment_subset (left_mem_segment _ _ _) hk).trans
        ((subset_iUnion (fun k => segment ℝ y (z k)) k).trans (subset_insert _ _))
  · rw [mem_ball]
    exact (dist_le_diam_of_mem hcpt.isBounded hp (mem_insert _ _)).trans_lt hdiam

/-- A choice of centres for pairwise disjoint sets. -/
theorem exists_center_fun {E : Type*} (B : Set E) (Y : E → Set E)
    (hdisj : ∀ y ∈ B, ∀ y' ∈ B, y ≠ y' → Disjoint (Y y) (Y y')) :
    ∃ c : E → E, ∀ y ∈ B, ∀ p ∈ Y y, c p = y := by
  classical
  refine ⟨fun p => if h : ∃ y ∈ B, p ∈ Y y then h.choose else p, fun y hy p hp => ?_⟩
  have h : ∃ y ∈ B, p ∈ Y y := ⟨y, hy, hp⟩
  simp only [dif_pos h]
  obtain ⟨hy', hp'⟩ := h.choose_spec
  by_contra hne
  exact Set.disjoint_left.1 (hdisj _ hy' y hy hne) hp' hp

/-- The centre map is locally constant along `f` on `W`. -/
theorem continuousOn_center_comp {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {B : Set E} (hB : B.Finite) {Y : E → Set E} (hYc : ∀ y ∈ B, IsClosed (Y y))
    (hdisj : ∀ y ∈ B, ∀ y' ∈ B, y ≠ y' → Disjoint (Y y) (Y y')) {c : E → E}
    (hc : ∀ y ∈ B, ∀ p ∈ Y y, c p = y) {f : X → E} (hf : Continuous f) {W : Set X}
    (hW : IsOpen W) (hWY : ∀ x ∈ W, ∃ y ∈ B, f x ∈ Y y) : ContinuousOn (fun x => c (f x)) W := by
  intro x₀ hx₀
  obtain ⟨y₀, hy₀, hfy₀⟩ := hWY x₀ hx₀
  set O := W ∩ f ⁻¹' (⋃ y ∈ B \ {y₀}, Y y)ᶜ
  have hO : IsOpen O := hW.inter (((hB.diff).isClosed_biUnion fun y hy =>
    hYc y hy.1).isOpen_compl.preimage hf)
  have hx₀O : x₀ ∈ O := by
    refine ⟨hx₀, fun h => ?_⟩
    obtain ⟨y, ⟨hyB, hyne⟩, hfy⟩ := mem_iUnion₂.1 h
    exact Set.disjoint_left.1 (hdisj y hyB y₀ hy₀ hyne) hfy hfy₀
  refine (continuousAt_const (y := y₀)).congr ?_ |>.continuousWithinAt
  filter_upwards [hO.mem_nhds hx₀O] with x ⟨hxW, hxn⟩
  obtain ⟨y, hy, hfy⟩ := hWY x hxW
  by_cases hyy : y = y₀
  · subst hyy
    exact (hc y hy _ hfy).symm
  · exact absurd (mem_iUnion₂.2 ⟨y, ⟨hy, hyy⟩, hfy⟩) hxn

/-- A correction `(1 - u) • φ` on an open set `W`, extended by `0`, is continuous when `u = 1`
or a neighbourhood missing `W` is available at each point off `W`. -/
theorem continuous_correction {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W O : Set X} [DecidablePred (· ∈ W)] (hW : IsOpen W) (hO : IsOpen O) (hOW : Disjoint O W)
    {u : X → ℝ} (hu : Continuous u) {φ : X → E} (hφ : ContinuousOn φ W) {r : ℝ} (hr : 0 ≤ r)
    (hφr : ∀ x ∈ W, ‖φ x‖ ≤ r) (hcov : ∀ x, x ∉ W → u x = 1 ∨ x ∈ O) :
    Continuous fun x => if x ∈ W then (1 - u x) • φ x else 0 := by
  classical
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  by_cases hx₀ : x₀ ∈ W
  · have h1 : ContinuousAt (fun x => (1 - u x) • φ x) x₀ :=
      ((continuousAt_const.sub hu.continuousAt)).smul (hφ.continuousAt (hW.mem_nhds hx₀))
    refine h1.congr ?_
    filter_upwards [hW.mem_nhds hx₀] with x hx
    simp only [if_pos hx]
  · rcases hcov x₀ hx₀ with h1 | hO₀
    · show Tendsto _ _ _
      simp only [if_neg hx₀]
      have ht : Tendsto (fun x => |1 - u x| * r) (𝓝 x₀) (𝓝 0) := by
        have : Tendsto (fun x => |1 - u x| * r) (𝓝 x₀) (𝓝 (|1 - u x₀| * r)) :=
          ((continuous_const.sub hu).abs.mul continuous_const).continuousAt
        rwa [h1, sub_self, abs_zero, zero_mul] at this
      refine squeeze_zero_norm (fun x => ?_) ht
      split_ifs with hx
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hφr x hx) (abs_nonneg _)
      · rw [norm_zero]
        exact mul_nonneg (abs_nonneg _) hr
    · refine (continuousAt_const (y := (0 : E))).congr ?_
      filter_upwards [hO.mem_nhds hO₀] with x hx
      have : x ∉ W := fun h => Set.disjoint_left.1 hOW hx h
      simp only [if_neg this]

/-- An open neighbourhood of one side `C` of the graph, meeting the graph only in `C` and in
fans at the points of `C ∩ G₂`. -/
theorem exists_open_nbhd_side {E : Type*} [MetricSpace E] {G G₂ C C' : Set E} (Y : E → Set E)
    (hC' : IsClosed C') (hCC' : Disjoint C C')
    (hloc : ∀ p ∈ C, p ∉ G₂ → ∃ s > 0, ∀ q ∈ G, q ∈ ball p s → q ∈ C)
    (hY : ∀ p ∈ C ∩ G₂, Y p ∈ 𝓝[G₂] p)
    (hsplit : ∀ q ∈ G, q ∈ G₂ ∨ q ∈ C ∨ q ∈ C') :
    ∃ N, IsOpen N ∧ C ⊆ N ∧ ∀ q ∈ G, q ∈ N → q ∈ C ∨ ∃ y ∈ C ∩ G₂, q ∈ Y y := by
  have key : ∀ p ∈ C, ∃ s > 0, ∀ q ∈ G, q ∈ ball p s → q ∈ C ∨ ∃ y ∈ C ∩ G₂, q ∈ Y y := by
    intro p hp
    by_cases hp2 : p ∈ G₂
    · obtain ⟨s₁, hs₁, h₁⟩ := Metric.mem_nhdsWithin_iff.1 (hY p ⟨hp, hp2⟩)
      have hpC' : p ∈ C'ᶜ := fun h => Set.disjoint_left.1 hCC' hp h
      obtain ⟨s₂, hs₂, h₂⟩ := Metric.isOpen_iff.1 hC'.isOpen_compl p hpC'
      refine ⟨min s₁ s₂, lt_min hs₁ hs₂, fun q hqG hq => ?_⟩
      rcases hsplit q hqG with h | h | h
      exacts [Or.inr ⟨p, ⟨hp, hp2⟩, h₁ ⟨ball_subset_ball (min_le_left _ _) hq, h⟩⟩, Or.inl h,
        absurd h (h₂ (ball_subset_ball (min_le_right _ _) hq))]
    · obtain ⟨s, hs, h⟩ := hloc p hp hp2
      exact ⟨s, hs, fun q hqG hq => Or.inl (h q hqG hq)⟩
  choose! s hs hprop using key
  refine ⟨⋃ p ∈ C, ball p (s p), isOpen_biUnion fun p _ => isOpen_ball,
    fun p hp => mem_iUnion₂.2 ⟨p, hp, mem_ball_self (hs p hp)⟩, fun q hqG hq => ?_⟩
  obtain ⟨p, hp, hqp⟩ := mem_iUnion₂.1 hq
  exact hprop p hp q hqG hqp

/-- **H–O Theorem 8, (1) ⇒ (2), before lifting to a fold** (pp. 187–189). From `f : X → G` and
sets `G₁, G₂, G₃` satisfying H–O's (F2), (F3), with finite frontiers `B₁ = cl(G₁ \ G₂) ∩ G₂`,
`B₃ = cl(G₃ \ G₂) ∩ G₂` that have fans in `G₂`: a map `h` close to `f` and a closed cover
`X₁, X₂, X₃` with `h(Xᵢ) ⊆ Gᵢ`, `h(X₁ ∩ X₂) ⊆ B₃`, `h(X₂ ∩ X₃) ⊆ B₁`, `X₁ ∩ X₃ = ∅`. -/
theorem ho16_theorem8_core {X : Type*} [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G G₁ G₂ G₃ : Set E}
    (hG₁ : IsClosed G₁) (hG₃ : IsClosed G₃) (hcov : G₁ ∪ G₃ = G) (hG₂ : G₂ = G₁ ∩ G₃)
    (hF3 : Disjoint (closure (G₁ \ G₂)) (closure (G₃ \ G₂)))
    (hfin₁ : (closure (G₁ \ G₂) ∩ G₂).Finite) (hfin₃ : (closure (G₃ \ G₂) ∩ G₂).Finite)
    (hfan : ∀ y ∈ (closure (G₁ \ G₂) ∪ closure (G₃ \ G₂)) ∩ G₂, ∀ r : ℝ, 0 < r →
      ∃ Y, IsFanAt G₂ y r Y)
    {f : X → E} (hf : Continuous f) (hfG : ∀ x, f x ∈ G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : X → E) (X₁ X₂ X₃ : Set X), Continuous h ∧ (∀ x, dist (f x) (h x) < ε) ∧
      IsClosed X₁ ∧ IsClosed X₂ ∧ IsClosed X₃ ∧ X₁ ∪ X₂ ∪ X₃ = univ ∧ Disjoint X₁ X₃ ∧
      (∀ x ∈ X₁, h x ∈ G₁) ∧ (∀ x ∈ X₂, h x ∈ G₂) ∧ (∀ x ∈ X₃, h x ∈ G₃) ∧
      (∀ x ∈ X₁ ∩ X₂, h x ∈ closure (G₃ \ G₂) ∩ G₂) ∧
      (∀ x ∈ X₂ ∩ X₃, h x ∈ closure (G₁ \ G₂) ∩ G₂) := by
  classical
  set C₁ := closure (G₁ \ G₂) with hC₁def
  set C₃ := closure (G₃ \ G₂) with hC₃def
  have hC₁G : C₁ ⊆ G₁ := closure_minimal diff_subset hG₁
  have hC₃G : C₃ ⊆ G₃ := closure_minimal diff_subset hG₃
  have hG₂₁ : G₂ ⊆ G₁ := hG₂ ▸ inter_subset_left
  have hG₂₃ : G₂ ⊆ G₃ := hG₂ ▸ inter_subset_right
  have hsplit₁ : ∀ q ∈ G, q ∈ G₂ ∨ q ∈ C₁ ∨ q ∈ C₃ := by
    intro q hq
    by_cases h2 : q ∈ G₂
    · exact Or.inl h2
    · rw [← hcov] at hq
      rcases hq with h | h
      · exact Or.inr (Or.inl (subset_closure ⟨h, h2⟩))
      · exact Or.inr (Or.inr (subset_closure ⟨h, h2⟩))
  have hsplit₃ : ∀ q ∈ G, q ∈ G₂ ∨ q ∈ C₃ ∨ q ∈ C₁ := fun q hq => by
    rcases hsplit₁ q hq with h | h | h
    exacts [Or.inl h, Or.inr (Or.inr h), Or.inr (Or.inl h)]
  -- Step 1: the radius and the fans.
  set B := (C₁ ∩ G₂) ∪ (C₃ ∩ G₂) with hBdef
  have hBfin : B.Finite := hfin₁.union hfin₃
  have hr_ev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ≤ ε ∧
      ∀ p ∈ B ×ˢ B, p.1 ≠ p.2 → 2 * r ≤ dist p.1 p.2 := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds (eventually_le_nhds hε)) ?_
    refine (Filter.eventually_all_finite (hBfin.prod hBfin)).2 fun p _ => ?_
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun _ h => absurd hp h
    · have : 0 < dist p.1 p.2 / 2 := half_pos (dist_pos.2 hp)
      exact nhdsWithin_le_nhds ((eventually_le_nhds this).mono fun r hr _ => by linarith)
  obtain ⟨r, ⟨hrε, hrB⟩, hr0⟩ := (hr_ev.and self_mem_nhdsWithin).exists
  have hr0 : (0 : ℝ) < r := hr0
  have hfan' : ∀ y ∈ B, ∃ Y : Set E, IsClosed Y ∧ Y ⊆ G₂ ∧ (∀ p ∈ Y, segment ℝ y p ⊆ Y) ∧
      Y ∈ 𝓝[G₂] y ∧ Y ⊆ ball y r := by
    intro y hy
    have hy' : y ∈ (C₁ ∪ C₃) ∩ G₂ := by
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      exacts [⟨Or.inl h1, h2⟩, ⟨Or.inr h1, h2⟩]
    obtain ⟨Y, hY⟩ := hfan y hy' r hr0
    exact ⟨Y, hY.props⟩
  choose! Y hYc hYG hYstar hYn hYball using hfan'
  have hYdisj : ∀ y ∈ B, ∀ y' ∈ B, y ≠ y' → Disjoint (Y y) (Y y') := by
    intro y hy y' hy' hne
    rw [Set.disjoint_left]
    intro p hp hp'
    have h1 := hYball y hy hp
    have h2 := hYball y' hy' hp'
    rw [mem_ball] at h1 h2
    have h3 := hrB (y, y') ⟨hy, hy'⟩ hne
    have h4 := dist_triangle_left y y' p
    simp only at h3
    linarith
  have hYd₁ : ∀ y ∈ C₁ ∩ G₂, ∀ y' ∈ C₁ ∩ G₂, y ≠ y' → Disjoint (Y y) (Y y') :=
    fun y hy y' hy' => hYdisj y (Or.inl hy) y' (Or.inl hy')
  have hYd₃ : ∀ y ∈ C₃ ∩ G₂, ∀ y' ∈ C₃ ∩ G₂, y ≠ y' → Disjoint (Y y) (Y y') :=
    fun y hy y' hy' => hYdisj y (Or.inr hy) y' (Or.inr hy')
  obtain ⟨c₁, hc₁⟩ := exists_center_fun (C₁ ∩ G₂) Y hYd₁
  obtain ⟨c₃, hc₃⟩ := exists_center_fun (C₃ ∩ G₂) Y hYd₃
  -- Step 3: neighbourhoods of the two sides.
  obtain ⟨N₁, hN₁o, hC₁N₁, hN₁⟩ := exists_open_nbhd_side (G := G) (G₂ := G₂) (C := C₁)
    (C' := C₃) Y isClosed_closure hF3 (fun p hp hp2 => by
      have hpG₃ : p ∉ G₃ := fun h => hp2 (hG₂ ▸ ⟨hC₁G hp, h⟩)
      obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.1 hG₃.isOpen_compl p hpG₃
      refine ⟨s, hs, fun q hqG hq => ?_⟩
      have hq3 : q ∉ G₃ := hball hq
      have hq1 : q ∈ G₁ := by rw [← hcov] at hqG; exact hqG.resolve_right hq3
      exact subset_closure ⟨hq1, fun h => hq3 (hG₂₃ h)⟩)
    (fun p hp => hYn p (Or.inl hp)) hsplit₁
  obtain ⟨N₃, hN₃o, hC₃N₃, hN₃⟩ := exists_open_nbhd_side (G := G) (G₂ := G₂) (C := C₃)
    (C' := C₁) Y isClosed_closure hF3.symm (fun p hp hp2 => by
      have hpG₁ : p ∉ G₁ := fun h => hp2 (hG₂ ▸ ⟨h, hC₃G hp⟩)
      obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.1 hG₁.isOpen_compl p hpG₁
      refine ⟨s, hs, fun q hqG hq => ?_⟩
      have hq1 : q ∉ G₁ := hball hq
      have hq3 : q ∈ G₃ := by rw [← hcov] at hqG; exact hqG.resolve_left hq1
      exact subset_closure ⟨hq3, fun h => hq1 (hG₂₁ h)⟩)
    (fun p hp => hYn p (Or.inr hp)) hsplit₃
  -- Step 2 and the open sets `U₁`, `U₃`.
  set K₁ := f ⁻¹' C₁ with hK₁def
  set K₃ := f ⁻¹' C₃ with hK₃def
  have hK₁c : IsClosed K₁ := isClosed_closure.preimage hf
  have hK₃c : IsClosed K₃ := isClosed_closure.preimage hf
  have hK13 : Disjoint K₁ K₃ := hF3.preimage f
  obtain ⟨O₁, O₃, hO₁, hO₃, hK₁O, hK₃O, hO13⟩ := normal_separation hK₁c hK₃c hK13
  set U₁ := O₁ ∩ f ⁻¹' N₁ with hU₁def
  set U₃ := O₃ ∩ f ⁻¹' N₃ with hU₃def
  have hU₁o : IsOpen U₁ := hO₁.inter (hN₁o.preimage hf)
  have hU₃o : IsOpen U₃ := hO₃.inter (hN₃o.preimage hf)
  have hK₁U : K₁ ⊆ U₁ := fun x hx => ⟨hK₁O hx, hC₁N₁ hx⟩
  have hK₃U : K₃ ⊆ U₃ := fun x hx => ⟨hK₃O hx, hC₃N₃ hx⟩
  have hU13 : Disjoint U₁ U₃ := hO13.mono inter_subset_left inter_subset_left
  -- Step 4: Krasinkiewicz–Minc.
  obtain ⟨X₁, X₂, X₃, hX₁, hX₂, hX₃, hXcov, hK₁X, hK₃X, hX13, hX12, hX23⟩ :=
    km77_lemma2 hHI hK₁c hK₃c hK13 hU₁o hU₃o hK₁U hK₃U
  have hmem : ∀ x, x ∈ X₁ ∨ x ∈ X₂ ∨ x ∈ X₃ := fun x => by
    have : x ∈ X₁ ∪ X₂ ∪ X₃ := hXcov ▸ mem_univ x
    rcases this with (h | h) | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]
  set W₁ := U₁ \ X₁ with hW₁def
  set W₃ := U₃ \ X₃ with hW₃def
  have hW₁o : IsOpen W₁ := hU₁o.sdiff hX₁
  have hW₃o : IsOpen W₃ := hU₃o.sdiff hX₃
  have hW13 : ∀ x, x ∈ W₁ → x ∉ W₃ := fun x h1 h3 => Set.disjoint_left.1 hU13 h1.1 h3.1
  have hW₁Y : ∀ x ∈ W₁, ∃ y ∈ C₁ ∩ G₂, f x ∈ Y y := by
    rintro x ⟨⟨-, hxN⟩, hxX⟩
    rcases hN₁ (f x) (hfG x) hxN with h | h
    · exact absurd (hK₁X h) hxX
    · exact h
  have hW₃Y : ∀ x ∈ W₃, ∃ y ∈ C₃ ∩ G₂, f x ∈ Y y := by
    rintro x ⟨⟨-, hxN⟩, hxX⟩
    rcases hN₃ (f x) (hfG x) hxN with h | h
    · exact absurd (hK₃X h) hxX
    · exact h
  -- Step 5: Urysohn functions.
  obtain ⟨u₁, hu₁0, hu₁1, hu₁I⟩ := exists_continuous_zero_one_of_isClosed (hX₂.inter hX₃)
    hU₁o.isClosed_compl (Set.disjoint_left.2 fun x hx hxU => hxU (hX23 hx))
  obtain ⟨u₃, hu₃0, hu₃1, hu₃I⟩ := exists_continuous_zero_one_of_isClosed (hX₁.inter hX₂)
    hU₃o.isClosed_compl (Set.disjoint_left.2 fun x hx hxU => hxU (hX12 hx))
  set g₁ : X → E := fun x => if x ∈ W₁ then (1 - u₁ x) • (c₁ (f x) - f x) else 0 with hg₁
  set g₃ : X → E := fun x => if x ∈ W₃ then (1 - u₃ x) • (c₃ (f x) - f x) else 0 with hg₃
  set h : X → E := fun x => f x + g₁ x + g₃ x with hhdef
  -- the values of `h`
  have hseg : ∀ (y p : E) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → p + (1 - t) • (y - p) ∈ segment ℝ y p ∧
      dist p (p + (1 - t) • (y - p)) ≤ dist p y := by
    intro y p t ht
    refine ⟨⟨1 - t, t, by linarith [ht.2], ht.1, by ring, by module⟩, ?_⟩
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ht.2]), dist_comm, dist_eq_norm]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])
  have hval₁ : ∀ x ∈ W₁, ∃ y ∈ C₁ ∩ G₂, h x ∈ Y y ∧ dist (f x) (h x) < r ∧
      (u₁ x = 0 → h x = y) := by
    intro x hx
    obtain ⟨y, hy, hfy⟩ := hW₁Y x hx
    have hcy : c₁ (f x) = y := hc₁ y hy (f x) hfy
    have hhx : h x = f x + (1 - u₁ x) • (y - f x) := by
      simp only [hhdef, hg₁, hg₃, if_pos hx, if_neg (hW13 x hx), add_zero, hcy]
    obtain ⟨hs1, hs2⟩ := hseg y (f x) (u₁ x) (hu₁I x)
    have hfr : dist (f x) y < r := hYball y (Or.inl hy) hfy
    refine ⟨y, hy, ?_, ?_, fun h0 => ?_⟩
    · rw [hhx]; exact hYstar y (Or.inl hy) (f x) hfy hs1
    · rw [hhx]; exact hs2.trans_lt hfr
    · rw [hhx, h0, sub_zero, one_smul, add_sub_cancel]
  have hval₃ : ∀ x ∈ W₃, ∃ y ∈ C₃ ∩ G₂, h x ∈ Y y ∧ dist (f x) (h x) < r ∧
      (u₃ x = 0 → h x = y) := by
    intro x hx
    obtain ⟨y, hy, hfy⟩ := hW₃Y x hx
    have hcy : c₃ (f x) = y := hc₃ y hy (f x) hfy
    have hx1 : x ∉ W₁ := fun h1 => hW13 x h1 hx
    have hhx : h x = f x + (1 - u₃ x) • (y - f x) := by
      simp only [hhdef, hg₁, hg₃, if_pos hx, if_neg hx1, add_zero, hcy]
    obtain ⟨hs1, hs2⟩ := hseg y (f x) (u₃ x) (hu₃I x)
    have hfr : dist (f x) y < r := hYball y (Or.inr hy) hfy
    refine ⟨y, hy, ?_, ?_, fun h0 => ?_⟩
    · rw [hhx]; exact hYstar y (Or.inr hy) (f x) hfy hs1
    · rw [hhx]; exact hs2.trans_lt hfr
    · rw [hhx, h0, sub_zero, one_smul, add_sub_cancel]
  have hval₀ : ∀ x, x ∉ W₁ → x ∉ W₃ → h x = f x := by
    intro x h1 h3
    simp only [hhdef, hg₁, hg₃, if_neg h1, if_neg h3, add_zero]
  refine ⟨h, X₁, X₂, X₃, ?_, ?_, hX₁, hX₂, hX₃, hXcov, hX13, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    have hcont₁ : Continuous g₁ := by
      refine continuous_correction (O := U₁ \ (X₂ ∪ X₃)) hW₁o (hU₁o.sdiff (hX₂.union hX₃)) ?_
        u₁.continuous ((continuousOn_center_comp hfin₁ (fun y hy => hYc y (Or.inl hy)) hYd₁ hc₁
          hf hW₁o hW₁Y).sub hf.continuousOn) hr0.le ?_ ?_
      · rw [Set.disjoint_left]
        rintro x ⟨-, hx23⟩ ⟨-, hx1⟩
        rcases hmem x with h' | h' | h'
        exacts [hx1 h', hx23 (Or.inl h'), hx23 (Or.inr h')]
      · intro x hx
        obtain ⟨y, hy, hfy⟩ := hW₁Y x hx
        rw [hc₁ y hy (f x) hfy, ← dist_eq_norm, dist_comm]
        exact (hYball y (Or.inl hy) hfy).le
      · intro x hx
        by_cases hxU : x ∈ U₁
        · have hx1 : x ∈ X₁ := by
            by_contra h'
            exact hx ⟨hxU, h'⟩
          refine Or.inr ⟨hxU, ?_⟩
          rintro (h2 | h3)
          · exact Set.disjoint_left.1 hU13 hxU (hX12 ⟨hx1, h2⟩)
          · exact Set.disjoint_left.1 hX13 hx1 h3
        · exact Or.inl (hu₁1 hxU)
    have hcont₃ : Continuous g₃ := by
      refine continuous_correction (O := U₃ \ (X₁ ∪ X₂)) hW₃o (hU₃o.sdiff (hX₁.union hX₂)) ?_
        u₃.continuous ((continuousOn_center_comp hfin₃ (fun y hy => hYc y (Or.inr hy)) hYd₃ hc₃
          hf hW₃o hW₃Y).sub hf.continuousOn) hr0.le ?_ ?_
      · rw [Set.disjoint_left]
        rintro x ⟨-, hx12⟩ ⟨-, hx3⟩
        rcases hmem x with h' | h' | h'
        exacts [hx12 (Or.inl h'), hx12 (Or.inr h'), hx3 h']
      · intro x hx
        obtain ⟨y, hy, hfy⟩ := hW₃Y x hx
        rw [hc₃ y hy (f x) hfy, ← dist_eq_norm, dist_comm]
        exact (hYball y (Or.inr hy) hfy).le
      · intro x hx
        by_cases hxU : x ∈ U₃
        · have hx3 : x ∈ X₃ := by
            by_contra h'
            exact hx ⟨hxU, h'⟩
          refine Or.inr ⟨hxU, ?_⟩
          rintro (h1 | h2)
          · exact Set.disjoint_left.1 hX13 h1 hx3
          · exact Set.disjoint_left.1 hU13 (hX23 ⟨h2, hx3⟩) hxU
        · exact Or.inl (hu₃1 hxU)
    exact (hf.add hcont₁).add hcont₃
  · intro x
    by_cases h1 : x ∈ W₁
    · obtain ⟨y, -, -, hd, -⟩ := hval₁ x h1
      linarith
    by_cases h3 : x ∈ W₃
    · obtain ⟨y, -, -, hd, -⟩ := hval₃ x h3
      linarith
    rw [hval₀ x h1 h3, dist_self]
    exact hε
  · intro x hx
    have h1 : x ∉ W₁ := fun h' => h'.2 hx
    by_cases h3 : x ∈ W₃
    · obtain ⟨y, hy, hY', -, -⟩ := hval₃ x h3
      exact hG₂₁ (hYG y (Or.inr hy) hY')
    rw [hval₀ x h1 h3]
    have hxU : x ∉ U₃ := fun h' => h3 ⟨h', fun h'' => Set.disjoint_left.1 hX13 hx h''⟩
    have hfC : f x ∉ C₃ := fun h' => hxU (hK₃U h')
    rcases hsplit₁ (f x) (hfG x) with h' | h' | h'
    exacts [hG₂₁ h', hC₁G h', absurd h' hfC]
  · intro x hx
    by_cases h1 : x ∈ W₁
    · obtain ⟨y, hy, hY', -, -⟩ := hval₁ x h1
      exact hYG y (Or.inl hy) hY'
    by_cases h3 : x ∈ W₃
    · obtain ⟨y, hy, hY', -, -⟩ := hval₃ x h3
      exact hYG y (Or.inr hy) hY'
    rw [hval₀ x h1 h3]
    have hxU₁ : x ∉ U₁ := by
      intro hxU
      have hx1 : x ∈ X₁ := by
        by_contra h'
        exact h1 ⟨hxU, h'⟩
      exact Set.disjoint_left.1 hU13 hxU (hX12 ⟨hx1, hx⟩)
    have hxU₃ : x ∉ U₃ := by
      intro hxU
      have hx3 : x ∈ X₃ := by
        by_contra h'
        exact h3 ⟨hxU, h'⟩
      exact Set.disjoint_left.1 hU13 (hX23 ⟨hx, hx3⟩) hxU
    rcases hsplit₁ (f x) (hfG x) with h' | h' | h'
    · exact h'
    · exact absurd (hK₁U h') hxU₁
    · exact absurd (hK₃U h') hxU₃
  · intro x hx
    have h3 : x ∉ W₃ := fun h' => h'.2 hx
    by_cases h1 : x ∈ W₁
    · obtain ⟨y, hy, hY', -, -⟩ := hval₁ x h1
      exact hG₂₃ (hYG y (Or.inl hy) hY')
    rw [hval₀ x h1 h3]
    have hxU : x ∉ U₁ := fun h' => h1 ⟨h', fun h'' => Set.disjoint_left.1 hX13 h'' hx⟩
    have hfC : f x ∉ C₁ := fun h' => hxU (hK₁U h')
    rcases hsplit₁ (f x) (hfG x) with h' | h' | h'
    exacts [hG₂₃ h', absurd h' hfC, hC₃G h']
  · rintro x ⟨hx1, hx2⟩
    have hxW : x ∈ W₃ := ⟨hX12 ⟨hx1, hx2⟩, fun h' => Set.disjoint_left.1 hX13 hx1 h'⟩
    obtain ⟨y, hy, -, -, hy0⟩ := hval₃ x hxW
    rw [hy0 (hu₃0 ⟨hx1, hx2⟩)]
    exact hy
  · rintro x ⟨hx2, hx3⟩
    have hxW : x ∈ W₁ := ⟨hX23 ⟨hx2, hx3⟩, fun h' => Set.disjoint_left.1 hX13 h' hx3⟩
    obtain ⟨y, hy, -, -, hy0⟩ := hval₁ x hxW
    rw [hy0 (hu₁0 ⟨hx2, hx3⟩)]
    exact hy

end HPC.HO16
