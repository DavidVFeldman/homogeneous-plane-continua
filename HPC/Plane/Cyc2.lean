import HPC.Plane.Cyc1
import HPC.Plane.Cyc2Circle

/-!
# Batch 128: polygonal Janiszewski, part II — a separating graph contains an odd cycle;
# `JaniszewskiPoly` proved

COMMISSION-batch128.md. The skeleton of the commission (`doc/batches/skeletons/Cyc2.lean`) with
every `sorry` replaced by a proof. Nothing in this file is `sorry`; nothing was refuted. Changes of
shape (recorded in REPORT-batch128):

* **`sideRadius`** (the design item) is half the distance from `p` to `otherSegs G e`, the union of
  the other segments of `G` and of the two ends of `e`. It is `1/2`-Lipschitz
  (`sideRadius_lipschitz`), so half-disks at nearby points of the open edge overlap, and the ball
  of that radius meets the graph only in the open edge (`mem_segSet_of_mem_ball_sideRadius`).
* **The sector lemma** (`vertex_sectors_placeholder`) is replaced by `vertex_arcs`, a
  one-dimensional form: on a small Euclidean circle `circPt w ρ` about `w`, parametrised on
  `(α, α + 2π)` with a base angle `α` off the graph, each edge at `w` is crossed exactly once, at
  an angle `θ e` (distinct edges at distinct angles, nothing else crossed), and the circle runs
  just before `θ e` in the side strip of `e` on one side and just after it on the other. The arcs
  between consecutive crossings play the part of the sectors; no sorting of the edges by angle is
  needed, because the count is done by the jump formula `zmod2_jump_sum` (`Cyc2Circle`): along
  the circle, `[· ∈ C]` jumps by `[e ∈ oddSet]` at `θ e`, and the total jump around the closed
  loop is `0`. Angles: `Complex.arg` for existence, `Real.Angle.cos_sin_inj` for uniqueness
  modulo `2π`.
* `sideStrip_subset_compl` takes `G`, `e`, `s` only (properness and `e ∈ G` are not needed).
* `gFun` (and `side_jump`) are stated under `open Classical in`: membership in a connected
  component is not decidable, so the skeleton's `gFun` does not compile as written.
* `edge_local` is proved in the skeleton's form (`∀ ρ' ≤ ρ`).
-/

namespace HPC.Plane

open Set Metric Filter Topology

/-! ### Elementary facts on proper graphs -/

/-- The direction of a segment. -/
def segDir (e : Seg) : Pt := e.2 - e.1

theorem segDir_ne_zero {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) :
    segDir e ≠ 0 := sub_ne_zero.2 (hG.1 e he).symm

/-- A point of an edge which is not a vertex lies on no other edge. -/
theorem not_mem_other_seg {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) {p : Pt}
    (hp : p ∈ segSet e) (hpv : p ∉ vertices G) : ∀ t ∈ G, t ≠ e → p ∉ segSet t := by
  intro t ht hte hpt
  have hne : segSet e ≠ segSet t := hG.2.1 e he t ht (Ne.symm hte)
  have h := (hG.2.2 e he t ht hne ⟨hp, hpt⟩).1
  rcases h with h | h
  · exact hpv (mem_vertices.2 ⟨e, he, Or.inl h⟩)
  · exact hpv (mem_vertices.2 ⟨e, he, Or.inr (Set.mem_singleton_iff.1 h)⟩)

/-- A point of an edge other than its ends is not a vertex. -/
theorem not_mem_vertices_of_ne_ends {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G)
    {p : Pt} (hp : p ∈ segSet e) (h1 : p ≠ e.1) (h2 : p ≠ e.2) : p ∉ vertices G := by
  intro hv
  obtain ⟨t, ht, hpt⟩ := mem_vertices.1 hv
  have hpt' : p ∈ segSet t := by
    rcases hpt with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  by_cases hte : t = e
  · subst hte
    rcases hpt with h | h
    · exact h1 h
    · exact h2 h
  · have hne : segSet e ≠ segSet t := hG.2.1 e he t ht (Ne.symm hte)
    rcases (hG.2.2 e he t ht hne ⟨hp, hpt'⟩).1 with h | h
    · exact h1 h
    · exact h2 (Set.mem_singleton_iff.1 h)

theorem vertices_mono {G H : Finset Seg} (h : G ⊆ H) : vertices G ⊆ vertices H := fun w hw => by
  obtain ⟨s, hs, hw⟩ := mem_vertices.1 hw
  exact mem_vertices.2 ⟨s, h hs, hw⟩

theorem vertices_subset_graphSet (G : Finset Seg) : (↑(vertices G) : Set Pt) ⊆ graphSet G :=
  fun w hw => by
    obtain ⟨s, hs, hw⟩ := mem_vertices.1 hw
    exact end_mem_graphSet hs hw

theorem midpoint_mem_segSet (e : Seg) : midpoint ℝ e.1 e.2 ∈ segSet e :=
  mem_segment_iff_wbtw.2 (wbtw_midpoint ℝ _ _)

theorem midpoint_ne_ends {e : Seg} (h : e.1 ≠ e.2) :
    midpoint ℝ e.1 e.2 ≠ e.1 ∧ midpoint ℝ e.1 e.2 ≠ e.2 :=
  ⟨fun h' => h ((midpoint_eq_left_iff ℝ).1 h'), fun h' => h ((midpoint_eq_right_iff ℝ).1 h')⟩

theorem midpoint_not_mem_vertices {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) :
    midpoint ℝ e.1 e.2 ∉ vertices G :=
  not_mem_vertices_of_ne_ends hG he (midpoint_mem_segSet e) (midpoint_ne_ends (hG.1 e he)).1
    (midpoint_ne_ends (hG.1 e he)).2

/-! ### Local structure at a non-vertex point of an edge -/

/-- The other segments of `G` together with the two ends of `e`: a closed set missing every
non-vertex point of `e`. -/
def otherSegs (G : Finset Seg) (e : Seg) : Set Pt :=
  (⋃ t ∈ G.erase e, segSet t) ∪ {e.1, e.2}

theorem isClosed_otherSegs (G : Finset Seg) (e : Seg) : IsClosed (otherSegs G e) :=
  (isClosed_biUnion_finset fun _ _ => (isCompact_segment' _ _).isClosed).union
    (Set.toFinite _).isClosed

theorem otherSegs_nonempty (G : Finset Seg) (e : Seg) : (otherSegs G e).Nonempty :=
  ⟨e.1, Or.inr (Set.mem_insert _ _)⟩

theorem not_mem_otherSegs {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) {p : Pt}
    (hp : p ∈ segSet e) (hpv : p ∉ vertices G) : p ∉ otherSegs G e := by
  rintro (h | h)
  · obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.1 h
    exact not_mem_other_seg hG he hp hpv t (Finset.mem_of_mem_erase ht)
      (Finset.ne_of_mem_erase ht) hpt
  · rcases h with h | h
    · exact hpv (mem_vertices.2 ⟨e, he, Or.inl h⟩)
    · exact hpv (mem_vertices.2 ⟨e, he, Or.inr (Set.mem_singleton_iff.1 h)⟩)

/-- The radius used for the side strips at `p`: half the distance from `p` to the union of the
other segments and of the two ends of `e` (positive at a non-vertex point of `e`). -/
noncomputable def sideRadius (G : Finset Seg) (e : Seg) (p : Pt) : ℝ :=
  infDist p (otherSegs G e) / 2

theorem sideRadius_pos {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) {p : Pt}
    (hp : p ∈ segSet e) (hpv : p ∉ vertices G) : 0 < sideRadius G e p := by
  unfold sideRadius
  have hnc : p ∉ closure (otherSegs G e) := by
    rw [(isClosed_otherSegs G e).closure_eq]; exact not_mem_otherSegs hG he hp hpv
  have := (infDist_pos_iff_notMem_closure (x := p) (otherSegs_nonempty G e)).1 hnc
  linarith

/-- `sideRadius` is `1/2`-Lipschitz. -/
theorem sideRadius_lipschitz (G : Finset Seg) (e : Seg) (p q : Pt) :
    sideRadius G e p ≤ sideRadius G e q + dist p q / 2 := by
  unfold sideRadius
  have := infDist_le_infDist_add_dist (s := otherSegs G e) (x := p) (y := q)
  linarith

/-- Within `sideRadius` of `p`, the graph is the segment `e` minus its ends. -/
theorem mem_segSet_of_mem_ball_sideRadius {G : Finset Seg} {e : Seg} {p z : Pt}
    (hz : z ∈ ball p (sideRadius G e p)) (hzG : z ∈ graphSet G) :
    z ∈ segSet e ∧ z ≠ e.1 ∧ z ≠ e.2 := by
  have hpos : 0 ≤ infDist p (otherSegs G e) := infDist_nonneg
  have hlt : dist z p < infDist p (otherSegs G e) := by
    have := mem_ball.1 hz; unfold sideRadius at this; linarith
  have hno : z ∉ otherSegs G e := by
    intro hz'
    have := infDist_le_dist_of_mem (x := p) hz'
    rw [dist_comm] at this; linarith
  refine ⟨?_, fun h => hno (Or.inr (Or.inl h)), fun h => hno (Or.inr (Or.inr h))⟩
  obtain ⟨t, ht, hzt⟩ := mem_graphSet.1 hzG
  by_cases hte : t = e
  · exact hte ▸ hzt
  · exact absurd (Or.inl (Set.mem_iUnion₂.2 ⟨t, Finset.mem_erase.2 ⟨hte, ht⟩, hzt⟩)) hno

/-- At a non-vertex point `p` of the edge `e` of the proper graph `G`, a small ball meets
`graphSet G` only in `segSet e`, and the ball minus `graphSet G` is the two half-disks
(`halfDisk` of `Jct2`), convex and nonempty. -/
theorem edge_local {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) {p : Pt}
    (hp : p ∈ segSet e) (hpv : p ∉ vertices G) :
    ∃ ρ > 0, ∀ ρ', 0 < ρ' → ρ' ≤ ρ →
      ball p ρ' ∩ graphSet G = ball p ρ' ∩ segSet e ∧
      ball p ρ' \ graphSet G = halfDisk p (segDir e) ρ' true ∪ halfDisk p (segDir e) ρ' false := by
  set d := segDir e with hd_def
  have hd : d ≠ 0 := segDir_ne_zero hG he
  have hR := sideRadius_pos hG he hp hpv
  have hp' : p ∈ segment ℝ e.1 e.2 := hp
  rw [segment_eq_image'] at hp'
  obtain ⟨s₀, ⟨hs0, hs1⟩, hps⟩ := hp'
  have hs0' : 0 < s₀ := lt_of_le_of_ne hs0 fun h =>
    hpv (mem_vertices.2 ⟨e, he, Or.inl (by rw [← hps, ← h]; simp)⟩)
  have hs1' : s₀ < 1 := lt_of_le_of_ne hs1 fun h =>
    hpv (mem_vertices.2 ⟨e, he, Or.inr (by rw [← hps, h]; simp)⟩)
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hm : 0 < min s₀ (1 - s₀) := lt_min hs0' (by linarith)
  refine ⟨min (sideRadius G e p) (min s₀ (1 - s₀) * ‖d‖), lt_min hR (mul_pos hm hdn),
    fun ρ' hρ' hρ'le => ?_⟩
  have hon : ∀ z ∈ ball p ρ', (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 = 0 → z ∈ segSet e := by
    intro z hz hc
    obtain ⟨τ, rfl⟩ := eq_add_smul_of_cross_zero hd hc
    have h1 : |τ| * ‖d‖ < min s₀ (1 - s₀) * ‖d‖ := by
      have := mem_ball.1 hz
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at this
      exact this.trans_le (hρ'le.trans (min_le_right _ _))
    have hτ : |τ| < min s₀ (1 - s₀) := lt_of_mul_lt_mul_right h1 hdn.le
    rw [abs_lt] at hτ
    show _ ∈ segment ℝ _ _
    rw [segment_eq_image']
    refine ⟨s₀ + τ, ⟨by linarith [min_le_left s₀ (1 - s₀)],
      by linarith [min_le_right s₀ (1 - s₀)]⟩, ?_⟩
    rw [← hps]; beta_reduce; rw [add_smul, hd_def, segDir]; abel
  have hcross_edge : ∀ z ∈ segSet e, (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 = 0 :=
    fun z hz => cross_zero_of_mem_segment hz hp
  have hball_G : ∀ z ∈ ball p ρ', z ∈ graphSet G → z ∈ segSet e := fun z hz hzG =>
    (mem_segSet_of_mem_ball_sideRadius
      (ball_subset_ball (hρ'le.trans (min_le_left _ _)) hz) hzG).1
  constructor
  · ext z
    constructor
    · rintro ⟨hzb, hzG⟩; exact ⟨hzb, hball_G z hzb hzG⟩
    · rintro ⟨hzb, hze⟩; exact ⟨hzb, mem_graphSet.2 ⟨e, he, hze⟩⟩
  · ext z
    simp only [mem_diff, mem_union]
    constructor
    · rintro ⟨hzb, hzG⟩
      have hc : (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 ≠ 0 := fun hc =>
        hzG (mem_graphSet.2 ⟨e, he, hon z hzb hc⟩)
      rcases lt_or_gt_of_ne hc with h | h
      · exact Or.inr (mem_halfDisk_false (mem_ball.1 hzb) h)
      · exact Or.inl (mem_halfDisk_true (mem_ball.1 hzb) h)
    · rintro (⟨hzb, hz⟩ | ⟨hzb, hz⟩)
      · refine ⟨hzb, fun hzG => ?_⟩
        have := hcross_edge z (hball_G z hzb hzG)
        simp only [if_true] at hz; linarith
      · refine ⟨hzb, fun hzG => ?_⟩
        have := hcross_edge z (hball_G z hzb hzG)
        simp only [Bool.false_eq_true, if_false] at hz; linarith

/-- **The side strip** of `e` on side `s`: the union of the half-disks on side `s` at the
non-vertex points of `e`. -/
def sideStrip (G : Finset Seg) (e : Seg) (s : Bool) : Set Pt :=
  ⋃ (p ∈ segSet e) (_ : p ∉ vertices G), halfDisk p (segDir e) (sideRadius G e p) s

theorem halfDisk_subset_sideStrip {G : Finset Seg} {e : Seg} {p : Pt} (hp : p ∈ segSet e)
    (hpv : p ∉ vertices G) {ρ : ℝ} (hρ : ρ ≤ sideRadius G e p) (s : Bool) :
    halfDisk p (segDir e) ρ s ⊆ sideStrip G e s := by
  intro z hz
  refine Set.mem_iUnion₂.2 ⟨p, hp, Set.mem_iUnion.2 ⟨hpv, ?_⟩⟩
  exact ⟨ball_subset_ball hρ hz.1, hz.2⟩

/-- The half-disks of radius `≤ sideRadius` at a non-vertex point miss the graph. -/
theorem halfDisk_subset_compl {G : Finset Seg} {e : Seg} {p : Pt}
    (hp : p ∈ segSet e) {ρ : ℝ} (hρ : ρ ≤ sideRadius G e p) (s : Bool) :
    halfDisk p (segDir e) ρ s ⊆ (graphSet G)ᶜ := by
  intro z hz hzG
  have hze := (mem_segSet_of_mem_ball_sideRadius (ball_subset_ball hρ hz.1) hzG).1
  have h0 := cross_zero_of_mem_segment hze hp
  have h2 := hz.2
  unfold segDir at h2
  cases s
  · simp only [Bool.false_eq_true, if_false] at h2; linarith
  · simp only [if_true] at h2; linarith

theorem sideStrip_subset_compl (G : Finset Seg) (e : Seg) (s : Bool) :
    sideStrip G e s ⊆ (graphSet G)ᶜ := by
  intro z hz
  obtain ⟨p, hp, hz⟩ := Set.mem_iUnion₂.1 hz
  obtain ⟨-, hz⟩ := Set.mem_iUnion.1 hz
  exact halfDisk_subset_compl hp le_rfl s hz

theorem sideStrip_nonempty {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) (s : Bool) :
    (sideStrip G e s).Nonempty := by
  obtain ⟨z, hz⟩ := halfDisk_nonempty (midpoint ℝ e.1 e.2) (segDir e) (segDir_ne_zero hG he)
    (sideRadius_pos hG he (midpoint_mem_segSet e) (midpoint_not_mem_vertices hG he)) s
  exact ⟨z, halfDisk_subset_sideStrip (midpoint_mem_segSet e) (midpoint_not_mem_vertices hG he)
    le_rfl s hz⟩

/-- The non-vertex points of an edge form the open segment. -/
theorem nonvertex_eq_openSegment {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G) :
    {p | p ∈ segSet e ∧ p ∉ vertices G} = openSegment ℝ e.1 e.2 := by
  have h12 := hG.1 e he
  ext p
  constructor
  · rintro ⟨hp, hpv⟩
    have hp' : p ∈ segment ℝ e.1 e.2 := hp
    rw [← insert_endpoints_openSegment] at hp'
    rcases hp' with h | h | h
    · exact absurd (mem_vertices.2 ⟨e, he, Or.inl h⟩) hpv
    · exact absurd (mem_vertices.2 ⟨e, he, Or.inr h⟩) hpv
    · exact h
  · intro hp
    refine ⟨openSegment_subset_segment ℝ _ _ hp, not_mem_vertices_of_ne_ends hG he
      (openSegment_subset_segment ℝ _ _ hp) ?_ ?_⟩
    · rintro rfl; exact h12 (left_mem_openSegment_iff.1 hp)
    · rintro rfl; exact h12 (right_mem_openSegment_iff.1 hp)

/-- Moving the centre of a half-disk along the line of `d` keeps the side. -/
theorem mem_halfDisk_of_shift {p p' d z : Pt} {ρ ρ' : ℝ} {s : Bool}
    (hpp' : (p.1 - p'.1) * d.2 - (p.2 - p'.2) * d.1 = 0) (hz : z ∈ halfDisk p d ρ s)
    (hz' : dist z p' < ρ') : z ∈ halfDisk p' d ρ' s := by
  refine ⟨mem_ball.2 hz', ?_⟩
  have h2 := hz.2
  have : (z.1 - p'.1) * d.2 - (z.2 - p'.2) * d.1 =
      ((z.1 - p.1) * d.2 - (z.2 - p.2) * d.1) + ((p.1 - p'.1) * d.2 - (p.2 - p'.2) * d.1) := by
    ring
  rw [this, hpp', add_zero]
  exact h2

/-- The side strip is preconnected (half-disks at nearby points of the open segment overlap;
`isPreconnected_biUnion_of_local_meet` over the preconnected open segment). -/
theorem sideStrip_isPreconnected {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G)
    (s : Bool) : IsPreconnected (sideStrip G e s) := by
  have hnv := nonvertex_eq_openSegment hG he
  have hmem : ∀ p ∈ openSegment ℝ e.1 e.2, p ∈ segSet e ∧ p ∉ vertices G := fun p hp => by
    rw [← hnv] at hp; exact hp
  have heq : sideStrip G e s =
      ⋃ p ∈ openSegment ℝ e.1 e.2, halfDisk p (segDir e) (sideRadius G e p) s := by
    ext z
    simp only [sideStrip, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨p, hp, hpv, hz⟩
      exact ⟨p, by rw [← hnv]; exact ⟨hp, hpv⟩, hz⟩
    · rintro ⟨p, hp, hz⟩
      exact ⟨p, (hmem p hp).1, (hmem p hp).2, hz⟩
  rw [heq]
  refine isPreconnected_biUnion_of_local_meet (convex_openSegment _ _).isPreconnected _
    (fun p => sideRadius G e p / 2)
    (fun p hp => half_pos (sideRadius_pos hG he (hmem p hp).1 (hmem p hp).2))
    (fun p _ => (halfDisk_convex _ _ _ _).isPreconnected) ?_
  intro p hp p' hp' hpp'
  have hR := sideRadius_pos hG he (hmem p hp).1 (hmem p hp).2
  have hdist : dist p' p < sideRadius G e p / 2 := mem_ball.1 hpp'
  have hlip := sideRadius_lipschitz G e p p'
  rw [dist_comm] at hlip
  obtain ⟨z, hz⟩ := halfDisk_nonempty p (segDir e) (segDir_ne_zero hG he)
    (by positivity : 0 < sideRadius G e p / 4) s
  refine ⟨z, ⟨ball_subset_ball (by linarith) hz.1, hz.2⟩, ?_⟩
  refine mem_halfDisk_of_shift (cross_zero_of_mem_segment (hmem p hp).1 (hmem p' hp').1) hz ?_
  have h1 : dist z p < sideRadius G e p / 4 := mem_ball.1 hz.1
  calc dist z p' ≤ dist z p + dist p p' := dist_triangle _ _ _
    _ < sideRadius G e p' := by rw [dist_comm p p']; linarith

/-- A preconnected subset of `(graphSet G)ᶜ` lies in the component `C` of `x` or misses it. -/
theorem subset_or_disjoint_component {G : Finset Seg} {S : Set Pt} (hS : IsPreconnected S)
    (hSG : S ⊆ (graphSet G)ᶜ) (x : Pt) :
    S ⊆ connectedComponentIn (graphSet G)ᶜ x ∨ Disjoint S (connectedComponentIn (graphSet G)ᶜ x) := by
  rcases Set.disjoint_or_nonempty_inter S (connectedComponentIn (graphSet G)ᶜ x) with h | ⟨y, hyS, hyC⟩
  · exact Or.inr h
  · left
    rw [connectedComponentIn_eq hyC]
    exact hS.subset_connectedComponentIn hyS hSG

/-- Membership in the component of `x` is locally constant off the graph. -/
theorem memC_eventually (G : Finset Seg) (x : Pt) {z : Pt} (hz : z ∉ graphSet G) :
    ∀ᶠ y in 𝓝 z, (y ∈ connectedComponentIn (graphSet G)ᶜ x ↔
      z ∈ connectedComponentIn (graphSet G)ᶜ x) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_graphSet G).isOpen_compl z hz
  filter_upwards [ball_mem_nhds z hε] with y hy
  rcases subset_or_disjoint_component (convex_ball z ε).isPreconnected hball x with h | h
  · exact ⟨fun _ => h (mem_ball_self hε), fun _ => h hy⟩
  · exact ⟨fun h' => absurd h' (h.notMem_of_mem_left hy),
      fun h' => absurd h' (h.notMem_of_mem_left (mem_ball_self hε))⟩

/-- A point of a side strip is in the component `C` iff the whole strip is. -/
theorem mem_C_iff_of_mem_sideStrip {G : Finset Seg} (hG : IsProper G) {e : Seg} (he : e ∈ G)
    {s : Bool} (x : Pt) {z : Pt} (hz : z ∈ sideStrip G e s) :
    z ∈ connectedComponentIn (graphSet G)ᶜ x ↔
      sideStrip G e s ⊆ connectedComponentIn (graphSet G)ᶜ x := by
  rcases subset_or_disjoint_component (sideStrip_isPreconnected hG he s)
    (sideStrip_subset_compl G e s) x with h | h
  · exact ⟨fun _ => h, fun h' => h' hz⟩
  · exact ⟨fun h' => absurd h' (h.notMem_of_mem_left hz),
      fun h' => absurd (h' hz) (h.notMem_of_mem_left hz)⟩

/-! ### The odd set -/

open scoped Classical in
/-- **The candidate cycle**: the edges of `G` having the component of `x` on exactly one side. -/
noncomputable def oddSet (G : Finset Seg) (x : Pt) : Finset Seg :=
  G.filter fun e =>
    (sideStrip G e true ⊆ connectedComponentIn (graphSet G)ᶜ x) ≠
      (sideStrip G e false ⊆ connectedComponentIn (graphSet G)ᶜ x)

theorem oddSet_subset (G : Finset Seg) (x : Pt) : oddSet G x ⊆ G := by
  classical
  unfold oddSet
  convert Finset.filter_subset _ G

theorem mem_oddSet {G : Finset Seg} {x : Pt} {e : Seg} (he : e ∈ G) :
    e ∈ oddSet G x ↔ ((sideStrip G e true ⊆ connectedComponentIn (graphSet G)ᶜ x) ≠
      (sideStrip G e false ⊆ connectedComponentIn (graphSet G)ᶜ x)) := by
  classical
  unfold oddSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

open Classical in
/-- The jump of `[· ∈ C]` across an edge, as a `ZMod 2` identity. -/
theorem side_jump {G : Finset Seg} {x : Pt} {e : Seg} (he : e ∈ G) (s : Bool) :
    ((if sideStrip G e s ⊆ connectedComponentIn (graphSet G)ᶜ x then 1 else 0 : ZMod 2) +
      (if e ∈ oddSet G x then 1 else 0)) =
      if sideStrip G e (!s) ⊆ connectedComponentIn (graphSet G)ᶜ x then 1 else 0 := by
  by_cases h1 : sideStrip G e true ⊆ connectedComponentIn (graphSet G)ᶜ x <;>
  by_cases h2 : sideStrip G e false ⊆ connectedComponentIn (graphSet G)ᶜ x <;>
  cases s <;> simp [h1, h2, mem_oddSet he] <;> decide

/-! ### The circle about a vertex: crossings and arcs -/

/-- The other end of an edge at `w`. -/
noncomputable def othEnd (w : Pt) (e : Seg) : Pt := if w = e.1 then e.2 else e.1

theorem segSet_eq_othEnd {w : Pt} {e : Seg} (hwe : w = e.1 ∨ w = e.2) :
    segSet e = segment ℝ w (othEnd w e) := by
  unfold othEnd segSet
  split_ifs with h
  · rw [h]
  · rcases hwe with h' | h'
    · exact absurd h' h
    · rw [h', segment_symm]

theorem ne_othEnd {w : Pt} {e : Seg} (h12 : e.1 ≠ e.2) (hwe : w = e.1 ∨ w = e.2) :
    w ≠ othEnd w e := by
  unfold othEnd
  split_ifs with h
  · rw [h]; exact h12
  · rcases hwe with h' | h'
    · exact absurd h' h
    · rw [h']; exact h12.symm

theorem segDir_eq_of_eq {w : Pt} {e : Seg} (h : w = e.1) : segDir e = othEnd w e - w := by
  simp [segDir, othEnd, h]

theorem segDir_eq_of_ne {w : Pt} {e : Seg} (hwe : w = e.1 ∨ w = e.2) (h : w ≠ e.1) :
    segDir e = -(othEnd w e - w) := by
  rcases hwe with h' | h'
  · exact absurd h' h
  · simp only [segDir, othEnd, if_neg h]; rw [h', neg_sub]

theorem exists_pos_lt_finset {ι : Type*} (E : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ E, 0 < f i)
    {r : ℝ} (hr : 0 < r) : ∃ ρ > 0, ρ < r ∧ ∀ i ∈ E, ρ < f i := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨r / 2, by linarith, by linarith, by simp⟩
  | insert a E ha ih =>
    obtain ⟨ρ, hρ, hρr, hρE⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := hf a (Finset.mem_insert_self _ _)
    refine ⟨min ρ (f a / 2), lt_min hρ (by linarith), (min_le_left _ _).trans_lt hρr, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt (hρE i hi)

theorem int_eq_zero_of_two_pi_mul {x : ℝ} {k : ℤ} (hk : x = 2 * Real.pi * k)
    (h1 : -(2 * Real.pi) < x) (h2 : x < 2 * Real.pi) : k = 0 := by
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by
    by_contra hc; push_neg at hc; nlinarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hc; push_neg at hc; nlinarith
  have a1 : k < 1 := by exact_mod_cast hk1
  have a2 : -1 < k := by exact_mod_cast hk2
  omega

theorem eNorm_circPt_sub (w : Pt) {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) : eNorm (circPt w ρ t - w) = ρ := by
  unfold eNorm circPt
  simp only [Prod.fst_sub, Prod.snd_sub, add_sub_cancel_left]
  rw [show (ρ * Real.cos t) ^ 2 + (ρ * Real.sin t) ^ 2 = ρ ^ 2 by
    have := Real.cos_sq_add_sin_sq t
    calc (ρ * Real.cos t) ^ 2 + (ρ * Real.sin t) ^ 2
        = ρ ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = ρ ^ 2 := by rw [this, mul_one]]
  exact Real.sqrt_sq hρ

theorem circ_cross_formula {w u : Pt} {ρ N θ₀ : ℝ} (h1 : N * Real.cos θ₀ = u.1)
    (h2 : N * Real.sin θ₀ = u.2) (t : ℝ) :
    ((circPt w ρ t).1 - (circPt w ρ θ₀).1) * u.2 - ((circPt w ρ t).2 - (circPt w ρ θ₀).2) * u.1 =
      ρ * N * Real.sin (θ₀ - t) := by
  simp only [circPt]
  rw [← h1, ← h2, Real.sin_sub]
  ring

/-- Near a vertex `w`, the segments not having `w` as an end stay away. -/
theorem exists_vertex_radius {G : Finset Seg} (hG : IsProper G) {w : Pt}
    (hw : ∃ e ∈ G, w = e.1 ∨ w = e.2) :
    ∃ r > 0, ∀ t ∈ G, ¬ (w = t.1 ∨ w = t.2) → ∀ z ∈ ball w r, z ∉ segSet t := by
  classical
  obtain ⟨e, he, hwe⟩ := hw
  set K := ⋃ t ∈ G.filter (fun t => ¬ (w = t.1 ∨ w = t.2)), segSet t with hK
  have hKc : IsClosed K := isClosed_biUnion_finset fun t _ => (isCompact_segment' _ _).isClosed
  have hwK : w ∉ K := by
    intro h
    obtain ⟨t, ht, hwt⟩ := Set.mem_iUnion₂.1 h
    obtain ⟨htG, hnt⟩ := Finset.mem_filter.1 ht
    have hte : e ≠ t := by rintro rfl; exact hnt hwe
    have hwe' : w ∈ segSet e := by
      rcases hwe with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    rcases (hG.2.2 e he t htG (hG.2.1 e he t htG hte) ⟨hwe', hwt⟩).2 with h' | h'
    · exact hnt (Or.inl h')
    · exact hnt (Or.inr h')
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl w hwK
  exact ⟨r, hr, fun t ht hnt z hz hzt =>
    hball hz (Set.mem_iUnion₂.2 ⟨t, Finset.mem_filter.2 ⟨ht, hnt⟩, hzt⟩)⟩

/-- **The arcs at a vertex** (the form of the sector lemma used here). For a point `w` which is
an end of some edge, there are a radius `ρ`, a base angle `α` and crossing angles `θ e` for the
edges `e` at `w` such that, along the Euclidean circle `circPt w ρ` on `(α, α + 2π)`: the base
point is off the graph; each edge at `w` is crossed exactly once, at `θ e`, distinct edges at
distinct angles, and nothing else is crossed; and just before `θ e` the circle runs in the side
strip of `e` on some side `s`, just after it in the side strip on side `!s`. (The arcs between
consecutive crossings play the part of the sectors.) -/
theorem vertex_arcs {G : Finset Seg} (hG : IsProper G) {w : Pt}
    (hw : ∃ e ∈ G, w = e.1 ∨ w = e.2) :
    ∃ ρ > 0, ∃ α : ℝ, ∃ θ : Seg → ℝ,
      circPt w ρ α ∉ graphSet G ∧
      (∀ e ∈ G, (w = e.1 ∨ w = e.2) → θ e ∈ Ioo α (α + 2 * Real.pi)) ∧
      (∀ e ∈ G, ∀ e' ∈ G, (w = e.1 ∨ w = e.2) → (w = e'.1 ∨ w = e'.2) → θ e = θ e' → e = e') ∧
      (∀ t ∈ Ioo α (α + 2 * Real.pi), circPt w ρ t ∈ graphSet G →
        ∃ e ∈ G, (w = e.1 ∨ w = e.2) ∧ t = θ e) ∧
      (∀ e ∈ G, (w = e.1 ∨ w = e.2) → ∃ s : Bool,
        (∀ᶠ t in 𝓝[<] θ e, circPt w ρ t ∈ sideStrip G e s) ∧
        (∀ᶠ t in 𝓝[>] θ e, circPt w ρ t ∈ sideStrip G e (!s))) := by
  classical
  obtain ⟨r, hr, hfar⟩ := exists_vertex_radius hG hw
  set E := G.filter fun e => w = e.1 ∨ w = e.2 with hE
  have hEmem : ∀ e, e ∈ E ↔ e ∈ G ∧ (w = e.1 ∨ w = e.2) := fun e => Finset.mem_filter
  have hu0 : ∀ e ∈ G, (w = e.1 ∨ w = e.2) → othEnd w e - w ≠ 0 := fun e he hwe =>
    sub_ne_zero.2 (ne_othEnd (hG.1 e he) hwe).symm
  obtain ⟨ρ, hρ, hρr, hρN⟩ := exists_pos_lt_finset E (fun e => eNorm (othEnd w e - w))
    (fun e he => eNorm_pos (hu0 e ((hEmem e).1 he).1 ((hEmem e).1 he).2)) hr
  have hρN' : ∀ e ∈ G, (w = e.1 ∨ w = e.2) → ρ < eNorm (othEnd w e - w) := fun e he hwe =>
    hρN e ((hEmem e).2 ⟨he, hwe⟩)
  have hcross_iff : ∀ e ∈ G, (w = e.1 ∨ w = e.2) → ∀ t, circPt w ρ t ∈ segSet e ↔
      ∃ k : ℤ, t - dirAngle (othEnd w e - w) = 2 * Real.pi * k := by
    intro e he hwe t
    rw [segSet_eq_othEnd hwe,
      circPt_mem_segment_iff (ne_othEnd (hG.1 e he) hwe) hρ (hρN' e he hwe)]
    obtain ⟨a1, a2⟩ := exists_angle (hu0 e he hwe)
    constructor
    · rintro ⟨h1, h2⟩
      exact angle_unique (eNorm_pos (hu0 e he hwe)) h1 h2 a1 a2
    · rintro ⟨k, hk⟩
      rw [show t = dirAngle (othEnd w e - w) + k * (2 * Real.pi) by linarith,
        Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
      exact ⟨a1, a2⟩
  obtain ⟨α, hαI, hαB⟩ := (Set.Ioo_infinite (zero_lt_one' ℝ)).exists_notMem_finset
    (E.image fun e => dirAngle (othEnd w e - w))
  have hα_nc : ∀ e ∈ G, (w = e.1 ∨ w = e.2) → ∀ k : ℤ,
      α - dirAngle (othEnd w e - w) ≠ 2 * Real.pi * k := by
    intro e he hwe k hk
    have hmem := dirAngle_mem_Ioc (othEnd w e - w)
    have h3 := Real.pi_gt_three
    have hk0 := int_eq_zero_of_two_pi_mul hk (by linarith [hαI.1, hmem.2])
      (by linarith [hαI.2, hmem.1])
    subst hk0
    apply hαB
    exact Finset.mem_image.2 ⟨e, (hEmem e).2 ⟨he, hwe⟩, by simp at hk; linarith⟩
  set θ : Seg → ℝ := fun e => toIocMod Real.two_pi_pos α (dirAngle (othEnd w e - w)) with hθ
  have hθk : ∀ e, ∃ k : ℤ, θ e - dirAngle (othEnd w e - w) = 2 * Real.pi * k := by
    intro e
    refine ⟨-toIocDiv Real.two_pi_pos α (dirAngle (othEnd w e - w)), ?_⟩
    simp only [hθ]
    rw [toIocMod_sub_self, zsmul_eq_mul]
    push_cast; ring
  have hθI : ∀ e ∈ G, (w = e.1 ∨ w = e.2) → θ e ∈ Ioo α (α + 2 * Real.pi) := by
    intro e he hwe
    have hmem := toIocMod_mem_Ioc Real.two_pi_pos α (dirAngle (othEnd w e - w))
    refine ⟨hmem.1, lt_of_le_of_ne hmem.2 fun h => ?_⟩
    obtain ⟨k, hk⟩ := hθk e
    apply hα_nc e he hwe (k - 1)
    have : θ e = α + 2 * Real.pi := h
    push_cast
    rw [mul_sub]
    linarith
  have hθmem : ∀ e ∈ G, (w = e.1 ∨ w = e.2) → circPt w ρ (θ e) ∈ segSet e := fun e he hwe =>
    (hcross_iff e he hwe (θ e)).2 (hθk e)
  have hin_ball : ∀ t, circPt w ρ t ∈ ball w r := fun t =>
    mem_ball.2 ((dist_circPt_le w hρ.le t).trans_lt hρr)
  have hinc : ∀ t, ∀ e ∈ G, circPt w ρ t ∈ segSet e → (w = e.1 ∨ w = e.2) := fun t e he h => by
    by_contra hn
    exact hfar e he hn _ (hin_ball t) h
  have hnv : ∀ e ∈ G, (w = e.1 ∨ w = e.2) → ∀ t, circPt w ρ t ∈ segSet e →
      circPt w ρ t ∉ vertices G := by
    intro e he hwe t ht
    have hne_w : circPt w ρ t ≠ w := fun h => by
      have := eNorm_circPt_sub w hρ.le t
      rw [h, sub_self] at this
      simp [eNorm] at this
      linarith
    have hne_o : circPt w ρ t ≠ othEnd w e := fun h => by
      have := eNorm_circPt_sub w hρ.le t
      rw [h] at this
      have := hρN' e he hwe
      linarith
    apply not_mem_vertices_of_ne_ends hG he ht
    · intro h
      unfold othEnd at hne_o
      split_ifs at hne_o with h1
      · exact hne_w (h.trans h1.symm)
      · exact hne_o h
    · intro h
      unfold othEnd at hne_o
      split_ifs at hne_o with h1
      · exact hne_o h
      · rcases hwe with h' | h'
        · exact h1 h'
        · exact hne_w (h.trans h'.symm)
  refine ⟨ρ, hρ, α, θ, ?_, hθI, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨e, he, hce⟩ := mem_graphSet.1 h
    have hwe := hinc α e he hce
    obtain ⟨k, hk⟩ := (hcross_iff e he hwe α).1 hce
    exact hα_nc e he hwe k hk
  · intro e he e' he' hwe hwe' hθe
    have h1 := hθmem e he hwe
    have h2 := hθmem e' he' hwe'
    rw [hθe] at h1
    by_contra hne
    exact not_mem_other_seg hG he' h2 (hnv e' he' hwe' _ h2) e he hne h1
  · intro t ht hG'
    obtain ⟨e, he, hce⟩ := mem_graphSet.1 hG'
    have hwe := hinc t e he hce
    refine ⟨e, he, hwe, ?_⟩
    obtain ⟨k, hk⟩ := (hcross_iff e he hwe t).1 hce
    obtain ⟨k', hk'⟩ := hθk e
    exact eq_of_two_pi_mul ht (hθI e he hwe) le_rfl (k := k - k') (by push_cast; linarith)
  · intro e he hwe
    have hq_seg := hθmem e he hwe
    have hqv := hnv e he hwe _ hq_seg
    have hR := sideRadius_pos hG he hq_seg hqv
    have hN := eNorm_pos (hu0 e he hwe)
    obtain ⟨c1, c2⟩ := (circPt_mem_segment_iff (ne_othEnd (hG.1 e he) hwe) hρ (hρN' e he hwe)
      (θ e)).1 (by rw [← segSet_eq_othEnd hwe]; exact hq_seg)
    have hform := fun t => circ_cross_formula (w := w) (ρ := ρ) c1 c2 t
    have hnear : ∀ᶠ t in 𝓝 (θ e),
        dist (circPt w ρ t) (circPt w ρ (θ e)) < sideRadius G e (circPt w ρ (θ e)) :=
      Metric.tendsto_nhds.1 ((continuous_circPt w ρ).tendsto (θ e)) _ hR
    have hL : ∀ᶠ t in 𝓝[<] θ e,
        dist (circPt w ρ t) (circPt w ρ (θ e)) < sideRadius G e (circPt w ρ (θ e)) ∧
          0 < Real.sin (θ e - t) := by
      filter_upwards [nhdsWithin_le_nhds hnear,
        Ioo_mem_nhdsLT (show θ e - Real.pi < θ e by linarith [Real.pi_pos])] with t h1 h2
      exact ⟨h1, Real.sin_pos_of_pos_of_lt_pi (by linarith [h2.2]) (by linarith [h2.1])⟩
    have hRt : ∀ᶠ t in 𝓝[>] θ e,
        dist (circPt w ρ t) (circPt w ρ (θ e)) < sideRadius G e (circPt w ρ (θ e)) ∧
          Real.sin (θ e - t) < 0 := by
      filter_upwards [nhdsWithin_le_nhds hnear,
        Ioo_mem_nhdsGT (show θ e < θ e + Real.pi by linarith [Real.pi_pos])] with t h1 h2
      refine ⟨h1, ?_⟩
      have := Real.sin_pos_of_pos_of_lt_pi (x := t - θ e) (by linarith [h2.1]) (by linarith [h2.2])
      rw [show θ e - t = -(t - θ e) by ring, Real.sin_neg]
      linarith
    have hpos : 0 < ρ * eNorm (othEnd w e - w) := mul_pos hρ hN
    have hsub := fun s => halfDisk_subset_sideStrip (G := G) hq_seg hqv le_rfl s
    by_cases h1 : w = e.1
    · refine ⟨true, ?_, ?_⟩
      · filter_upwards [hL] with t ht
        apply hsub true
        apply mem_halfDisk_true ht.1
        rw [segDir_eq_of_eq h1, hform t]
        exact mul_pos hpos ht.2
      · filter_upwards [hRt] with t ht
        apply hsub false
        apply mem_halfDisk_false ht.1
        rw [segDir_eq_of_eq h1, hform t]
        exact mul_neg_of_pos_of_neg hpos ht.2
    · refine ⟨false, ?_, ?_⟩
      · filter_upwards [hL] with t ht
        apply hsub false
        apply mem_halfDisk_false ht.1
        rw [segDir_eq_of_ne hwe h1]
        simp only [Prod.fst_neg, Prod.snd_neg]
        have := hform t
        have := mul_pos hpos ht.2
        linarith
      · filter_upwards [hRt] with t ht
        apply hsub true
        apply mem_halfDisk_true ht.1
        rw [segDir_eq_of_ne hwe h1]
        simp only [Prod.fst_neg, Prod.snd_neg]
        have := hform t
        have := mul_neg_of_pos_of_neg hpos ht.2
        linarith

/-- **Even degree of the odd set at every vertex**: the `C`-membership along the circle about `w`
changes exactly at the crossings of the edges of `oddSet` (`vertex_arcs`, `side_jump`), and a
function on a closed loop changes an even number of times (`zmod2_jump_sum`). -/
theorem even_deg_oddSet {G : Finset Seg} (hG : IsProper G) (x : Pt) (w : Pt) :
    Even (deg (oddSet G x) w) := by
  classical
  by_cases hw : ∃ e ∈ G, w = e.1 ∨ w = e.2
  swap
  · have : deg (oddSet G x) w = 0 := by
      unfold deg
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro s hs hws
      exact hw ⟨s, oddSet_subset G x hs, hws⟩
    rw [this]; exact Even.zero
  obtain ⟨ρ, hρ, α, θ, hα, hθI, hθinj, hcross, hside⟩ := vertex_arcs hG hw
  set C := connectedComponentIn (graphSet G)ᶜ x with hC
  set E := G.filter fun e => w = e.1 ∨ w = e.2 with hE
  set F : ℝ → ZMod 2 := fun t => if circPt w ρ t ∈ C then 1 else 0 with hF
  set T := E.image θ with hT
  set δ : ℝ → ZMod 2 :=
    fun t => if t ∈ (E.filter (· ∈ oddSet G x)).image θ then 1 else 0 with hδdef
  have hinjE : ∀ e ∈ E, ∀ e' ∈ E, θ e = θ e' → e = e' := fun e he e' he' h =>
    hθinj e (Finset.mem_filter.1 he).1 e' (Finset.mem_filter.1 he').1
      (Finset.mem_filter.1 he).2 (Finset.mem_filter.1 he').2 h
  have hδ : ∀ e ∈ E, δ (θ e) = if e ∈ oddSet G x then 1 else 0 := by
    intro e heE
    by_cases ho : e ∈ oddSet G x
    · rw [if_pos ho, hδdef]
      simp only
      rw [if_pos (Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨heE, ho⟩, rfl⟩)]
    · rw [if_neg ho, hδdef]
      simp only
      rw [if_neg]
      intro h
      obtain ⟨e', he', hθe⟩ := Finset.mem_image.1 h
      obtain ⟨he'E, ho'⟩ := Finset.mem_filter.1 he'
      exact ho (hinjE e' he'E e heE hθe ▸ ho')
  have hcirc_off : ∀ t ∈ Icc α (α + 2 * Real.pi), t ∉ T → circPt w ρ t ∉ graphSet G := by
    intro t ht htT hG'
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact hα (h ▸ hG')
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', circPt_add_two_pi] at hG'; exact hα hG'
    obtain ⟨e, heG, hwe, rfl⟩ := hcross t ⟨h, h'⟩ hG'
    exact htT (Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨heG, hwe⟩, rfl⟩)
  have key := zmod2_jump_sum F δ T.card α (α + 2 * Real.pi) T rfl
    (by linarith [Real.pi_pos]) ?_ ?_ ?_
  · have hper : F (α + 2 * Real.pi) = F α := by simp only [hF, circPt_add_two_pi]
    rw [hper] at key
    have hsum : ∑ t ∈ T, δ t = 0 := by
      have := congrArg (· - F α) key
      simp only [sub_self, add_sub_cancel_left] at this
      exact this.symm
    rw [hT, Finset.sum_image hinjE, Finset.sum_congr rfl hδ, Finset.sum_boole] at hsum
    rw [even_iff_deg_cast]
    have hfil : (oddSet G x).filter (fun s => w = s.1 ∨ w = s.2) =
        E.filter (· ∈ oddSet G x) := by
      ext s
      simp only [hE, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨oddSet_subset G x h1, h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
    unfold deg
    rw [hfil]
    exact hsum
  · intro t ht
    obtain ⟨e, heE, rfl⟩ := Finset.mem_image.1 ht
    exact hθI e (Finset.mem_filter.1 heE).1 (Finset.mem_filter.1 heE).2
  · intro t ht htT
    have hoff := hcirc_off t ht htT
    have hev := ((continuous_circPt w ρ).tendsto t).eventually (memC_eventually G x hoff)
    filter_upwards [hev] with t' ht'
    simp only [hF]
    rw [if_congr ht' rfl rfl]
  · intro t ht
    obtain ⟨e, heE, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨heG, hwe⟩ := Finset.mem_filter.1 heE
    obtain ⟨s, hl, hr⟩ := hside e heG hwe
    refine ⟨if sideStrip G e s ⊆ C then 1 else 0, ?_, ?_⟩
    · filter_upwards [hl] with t' ht'
      simp only [hF]
      rw [if_congr (mem_C_iff_of_mem_sideStrip hG heG x ht') rfl rfl]
    · filter_upwards [hr] with t' ht'
      simp only [hF]
      rw [if_congr (mem_C_iff_of_mem_sideStrip hG heG x ht') rfl rfl, hδ e heE, side_jump heG s]

theorem isCycle_oddSet {G : Finset Seg} (hG : IsProper G) (x : Pt) : IsCycle (oddSet G x) :=
  ⟨hG.subset (oddSet_subset G x), even_deg_oddSet hG x⟩

/-! ### The parity of the odd set differs at `x` and `y` -/

open Classical in
/-- `[· ∈ C] + cycParity (oddSet G x)` on `(graphSet G)ᶜ`. -/
noncomputable def gFun (G : Finset Seg) (x z : Pt) : ZMod 2 :=
  (if z ∈ connectedComponentIn (graphSet G)ᶜ x then 1 else 0) + cycParity (oddSet G x) z

/-- The parity of the odd set is constant on each side strip. -/
theorem cycParity_eq_on_sideStrip {G : Finset Seg} (hG : IsProper G) (x : Pt) {e : Seg}
    (he : e ∈ G) {s : Bool} {z₁ z₂ : Pt} (h₁ : z₁ ∈ sideStrip G e s) (h₂ : z₂ ∈ sideStrip G e s) :
    cycParity (oddSet G x) z₁ = cycParity (oddSet G x) z₂ :=
  cycParity_eq_of_isPreconnected (isCycle_oddSet hG x).1.1 (isCycle_oddSet hG x).2
    (sideStrip_isPreconnected hG he s)
    ((sideStrip_subset_compl G e s).trans
      (Set.compl_subset_compl.2 (graphSet_mono (oddSet_subset G x)))) h₁ h₂

/-- **The parity of the odd set flips across `e` iff `e ∈ oddSet`.** For `e ∈ oddSet` this is
`cycParity_flip` at a generic point of `e`; for `e ∉ oddSet` local constancy at the midpoint. -/
theorem cycParity_sideStrip_ne_iff {G : Finset Seg} (hG : IsProper G) (x : Pt) {e : Seg}
    (he : e ∈ G) {z₁ z₂ : Pt} (h₁ : z₁ ∈ sideStrip G e true) (h₂ : z₂ ∈ sideStrip G e false) :
    cycParity (oddSet G x) z₁ ≠ cycParity (oddSet G x) z₂ ↔ e ∈ oddSet G x := by
  have hZc := isCycle_oddSet hG x
  constructor
  · intro hne
    by_contra hnot
    apply hne
    have hp := midpoint_mem_segSet e
    have hpv := midpoint_not_mem_vertices hG he
    have hpZ : midpoint ℝ e.1 e.2 ∉ graphSet (oddSet G x) := by
      intro h
      obtain ⟨t, ht, hpt⟩ := mem_graphSet.1 h
      by_cases hte : t = e
      · exact hnot (hte ▸ ht)
      · exact not_mem_other_seg hG he hp hpv t (oddSet_subset G x ht) hte hpt
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.1 (isClosed_graphSet (oddSet G x)).isOpen_compl _ hpZ
    have hR := sideRadius_pos hG he hp hpv
    have hε' : 0 < min ε (sideRadius G e (midpoint ℝ e.1 e.2)) := lt_min hε hR
    obtain ⟨y₁, hy₁⟩ := halfDisk_nonempty _ (segDir e) (segDir_ne_zero hG he) hε' true
    obtain ⟨y₂, hy₂⟩ := halfDisk_nonempty _ (segDir e) (segDir_ne_zero hG he) hε' false
    have hs₁ := halfDisk_subset_sideStrip hp hpv (min_le_right _ _) true hy₁
    have hs₂ := halfDisk_subset_sideStrip hp hpv (min_le_right _ _) false hy₂
    rw [cycParity_eq_on_sideStrip hG x he h₁ hs₁, cycParity_eq_on_sideStrip hG x he h₂ hs₂]
    exact cycParity_eq_of_isPreconnected hZc.1.1 hZc.2 (convex_ball _ ε).isPreconnected hball
      (ball_subset_ball (min_le_left _ _) hy₁.1) (ball_subset_ball (min_le_left _ _) hy₂.1)
  · intro heZ
    have he1 : e.1 ∈ vertices (oddSet G x) := mem_vertices.2 ⟨e, heZ, Or.inl rfl⟩
    have he2 : e.2 ∈ vertices (oddSet G x) := mem_vertices.2 ⟨e, heZ, Or.inr rfl⟩
    obtain ⟨p, hp, hpv, hgen⟩ : ∃ p ∈ segSet e, p ∉ vertices G ∧
        (e.1.2 ≠ e.2.2 → ∀ w ∈ vertices (oddSet G x), w.2 ≠ p.2) := by
      by_cases hh : e.1.2 = e.2.2
      · exact ⟨midpoint ℝ e.1 e.2, midpoint_mem_segSet e, midpoint_not_mem_vertices hG he,
          fun h => absurd hh h⟩
      · obtain ⟨p, hp, -, hpF⟩ := exists_near_on_segment (left_mem_segment ℝ e.1 e.2)
          ((vertices (oddSet G x)).image Prod.snd) 0 1
          (by simp only [zero_mul, one_mul, zero_add, Prod.snd_sub]
              exact sub_ne_zero.2 (Ne.symm hh)) one_pos
        have hpF' : ∀ w ∈ vertices (oddSet G x), w.2 ≠ p.2 := fun w hw h =>
          hpF (Finset.mem_image.2 ⟨w, hw, by rw [h]; ring⟩)
        refine ⟨p, hp, not_mem_vertices_of_ne_ends hG he hp ?_ ?_, fun _ => hpF'⟩
        · rintro rfl; exact hpF' _ he1 rfl
        · rintro rfl; exact hpF' _ he2 rfl
    have hother : ∀ t ∈ oddSet G x, t ≠ e → p ∉ segSet t := fun t ht hte =>
      not_mem_other_seg hG he hp hpv t (oddSet_subset G x ht) hte
    have hpvZ : p ∉ vertices (oddSet G x) := fun h => hpv (vertices_mono (oddSet_subset G x) h)
    obtain ⟨ρ₀, hρ₀, hloc⟩ := edge_local hG he hp hpv
    have hR := sideRadius_pos hG he hp hpv
    have hε : 0 < min ρ₀ (sideRadius G e p) := lt_min hρ₀ hR
    obtain ⟨y₁, y₂, hd₁, hd₂, hy₁Z, hy₂Z, hne⟩ :=
      cycParity_flip hZc heZ hp hother hpvZ hgen _ hε
    have hstrip : ∀ y, dist y p < min ρ₀ (sideRadius G e p) → y ∉ graphSet (oddSet G x) →
        ∃ s, y ∈ sideStrip G e s := by
      intro y hy hyZ
      have hyG : y ∉ graphSet G := by
        intro hyG
        have := (mem_segSet_of_mem_ball_sideRadius
          (ball_subset_ball (min_le_right _ _) (mem_ball.2 hy)) hyG).1
        exact hyZ (mem_graphSet.2 ⟨e, heZ, this⟩)
      have : y ∈ ball p (min ρ₀ (sideRadius G e p)) \ graphSet G := ⟨mem_ball.2 hy, hyG⟩
      rw [(hloc _ hε (min_le_left _ _)).2] at this
      rcases this with h | h
      · exact ⟨true, halfDisk_subset_sideStrip hp hpv (min_le_right _ _) true h⟩
      · exact ⟨false, halfDisk_subset_sideStrip hp hpv (min_le_right _ _) false h⟩
    obtain ⟨s₁, hs₁⟩ := hstrip y₁ hd₁ hy₁Z
    obtain ⟨s₂, hs₂⟩ := hstrip y₂ hd₂ hy₂Z
    intro heq
    apply hne
    cases s₁ <;> cases s₂
    · exact cycParity_eq_on_sideStrip hG x he hs₁ hs₂
    · rw [cycParity_eq_on_sideStrip hG x he hs₁ h₂, cycParity_eq_on_sideStrip hG x he hs₂ h₁, heq]
    · rw [cycParity_eq_on_sideStrip hG x he hs₁ h₁, cycParity_eq_on_sideStrip hG x he hs₂ h₂, heq]
    · exact cycParity_eq_on_sideStrip hG x he hs₁ hs₂

theorem zmod2_add_eq_add_of_iff : ∀ a₁ a₂ p₁ p₂ : ZMod 2, (a₁ ≠ a₂ ↔ p₁ ≠ p₂) →
    a₁ + p₁ = a₂ + p₂ := by decide

/-- `gFun` takes one value on the union of the two side strips of an edge. -/
theorem gFun_eq_of_mem_sideStrip {G : Finset Seg} (hG : IsProper G) (x : Pt) {e : Seg}
    (he : e ∈ G) {s₁ s₂ : Bool} {z₁ z₂ : Pt} (h₁ : z₁ ∈ sideStrip G e s₁)
    (h₂ : z₂ ∈ sideStrip G e s₂) : gFun G x z₁ = gFun G x z₂ := by
  classical
  have key : ∀ {y₁ y₂ : Pt}, y₁ ∈ sideStrip G e true → y₂ ∈ sideStrip G e false →
      gFun G x y₁ = gFun G x y₂ := by
    intro y₁ y₂ hy₁ hy₂
    unfold gFun
    rw [if_congr (mem_C_iff_of_mem_sideStrip hG he x hy₁) rfl rfl,
      if_congr (mem_C_iff_of_mem_sideStrip hG he x hy₂) rfl rfl]
    apply zmod2_add_eq_add_of_iff
    rw [cycParity_sideStrip_ne_iff hG x he hy₁ hy₂, mem_oddSet he]
    by_cases a : sideStrip G e true ⊆ connectedComponentIn (graphSet G)ᶜ x <;>
    by_cases b : sideStrip G e false ⊆ connectedComponentIn (graphSet G)ᶜ x <;>
    simp [a, b]
  have same : ∀ {s : Bool} {y₁ y₂ : Pt}, y₁ ∈ sideStrip G e s → y₂ ∈ sideStrip G e s →
      gFun G x y₁ = gFun G x y₂ := by
    intro s y₁ y₂ hy₁ hy₂
    unfold gFun
    rw [if_congr (mem_C_iff_of_mem_sideStrip hG he x hy₁) rfl rfl,
      if_congr (mem_C_iff_of_mem_sideStrip hG he x hy₂) rfl rfl,
      cycParity_eq_on_sideStrip hG x he hy₁ hy₂]
  cases s₁ <;> cases s₂
  · exact same h₁ h₂
  · exact (key h₂ h₁).symm
  · exact key h₁ h₂
  · exact same h₁ h₂

/-- Across a non-vertex point `p` of an edge `e ∈ G`, `gFun` takes the same value on the two
half-disks. -/
theorem gFun_eq_across_edge {G : Finset Seg} (hG : IsProper G) (x : Pt) {e : Seg} (he : e ∈ G)
    {p : Pt} (hp : p ∈ segSet e) (hpv : p ∉ vertices G) :
    ∃ ρ > 0, ∀ z₁ ∈ ball p ρ \ graphSet G, ∀ z₂ ∈ ball p ρ \ graphSet G,
      gFun G x z₁ = gFun G x z₂ := by
  obtain ⟨ρ₀, hρ₀, hloc⟩ := edge_local hG he hp hpv
  have hR := sideRadius_pos hG he hp hpv
  refine ⟨min ρ₀ (sideRadius G e p), lt_min hρ₀ hR, ?_⟩
  have hside : ∀ z ∈ ball p (min ρ₀ (sideRadius G e p)) \ graphSet G,
      ∃ s, z ∈ sideStrip G e s := by
    intro z hz
    rw [(hloc _ (lt_min hρ₀ hR) (min_le_left _ _)).2] at hz
    rcases hz with hz | hz
    · exact ⟨true, halfDisk_subset_sideStrip hp hpv (min_le_right _ _) true hz⟩
    · exact ⟨false, halfDisk_subset_sideStrip hp hpv (min_le_right _ _) false hz⟩
  intro z₁ hz₁ z₂ hz₂
  obtain ⟨s₁, h₁⟩ := hside z₁ hz₁
  obtain ⟨s₂, h₂⟩ := hside z₂ hz₂
  exact gFun_eq_of_mem_sideStrip hG x he h₁ h₂

/-- `gFun` is locally constant on `(graphSet G)ᶜ`. -/
theorem gFun_locallyConstant {G : Finset Seg} (hG : IsProper G) (x : Pt) {z : Pt}
    (hz : z ∉ graphSet G) : ∃ ρ > 0, ∀ z' ∈ ball z ρ, z' ∉ graphSet G → gFun G x z' = gFun G x z := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_graphSet G).isOpen_compl z hz
  refine ⟨ε, hε, fun z' hz' _ => ?_⟩
  have hpar : cycParity (oddSet G x) z' = cycParity (oddSet G x) z :=
    cycParity_eq_of_isPreconnected (isCycle_oddSet hG x).1.1 (isCycle_oddSet hG x).2
      (convex_ball z ε).isPreconnected
      (hball.trans (Set.compl_subset_compl.2 (graphSet_mono (oddSet_subset G x)))) hz'
      (mem_ball_self hε)
  have hC : (z' ∈ connectedComponentIn (graphSet G)ᶜ x) ↔
      (z ∈ connectedComponentIn (graphSet G)ᶜ x) := by
    rcases subset_or_disjoint_component (convex_ball z ε).isPreconnected hball x with h | h
    · exact ⟨fun _ => h (mem_ball_self hε), fun _ => h hz'⟩
    · exact ⟨fun h' => absurd h' (h.notMem_of_mem_left hz'),
        fun h' => absurd h' (h.notMem_of_mem_left (mem_ball_self hε))⟩
  unfold gFun
  rw [hpar, if_congr hC rfl rfl]

/-- **`gFun` is constant on `(graphSet G)ᶜ`**: it is locally constant across every non-vertex
point of the graph, and the plane minus the finitely many vertices is connected
(`Set.Countable.isConnected_compl_of_one_lt_rank`). -/
theorem gFun_const {G : Finset Seg} (hG : IsProper G) (x : Pt) {z z' : Pt} (hz : z ∉ graphSet G)
    (hz' : z' ∉ graphSet G) : gFun G x z = gFun G x z' := by
  set S : Set Pt := (↑(vertices G) : Set Pt)ᶜ with hS_def
  have hS : IsPreconnected S :=
    ((vertices G).finite_toSet.countable.isConnected_compl_of_one_lt_rank
      (by rw [rank_prod', Module.rank_self]; norm_num)).isPreconnected
  have hmemS : ∀ y, y ∉ graphSet G → y ∈ S := fun y hy hv => hy (vertices_subset_graphSet G hv)
  have hloc : ∀ y ∈ S, ∃ ρ > 0, ∀ y₁ ∈ ball y ρ, ∀ y₂ ∈ ball y ρ, y₁ ∉ graphSet G →
      y₂ ∉ graphSet G → gFun G x y₁ = gFun G x y₂ := by
    intro y hy
    by_cases hyG : y ∈ graphSet G
    · obtain ⟨e, he, hye⟩ := mem_graphSet.1 hyG
      obtain ⟨ρ, hρ, h⟩ := gFun_eq_across_edge hG x he hye hy
      exact ⟨ρ, hρ, fun y₁ h₁ y₂ h₂ hn₁ hn₂ => h y₁ ⟨h₁, hn₁⟩ y₂ ⟨h₂, hn₂⟩⟩
    · obtain ⟨ρ, hρ, h⟩ := gFun_locallyConstant hG x hyG
      exact ⟨ρ, hρ, fun y₁ h₁ y₂ h₂ hn₁ hn₂ => (h y₁ h₁ hn₁).trans (h y₂ h₂ hn₂).symm⟩
  have hdense : ∀ y ∈ S, ∀ ε > 0, ∃ y' ∈ ball y ε, y' ∉ graphSet G := by
    intro y hy ε hε
    by_cases hyG : y ∈ graphSet G
    · obtain ⟨e, he, hye⟩ := mem_graphSet.1 hyG
      obtain ⟨ρ, hρ, h⟩ := edge_local hG he hye hy
      have hm : 0 < min ε ρ := lt_min hε hρ
      obtain ⟨y', hy'⟩ := halfDisk_nonempty y (segDir e) (segDir_ne_zero hG he) hm true
      have : y' ∈ ball y (min ε ρ) \ graphSet G := by
        rw [(h _ hm (min_le_right _ _)).2]; exact Or.inl hy'
      exact ⟨y', ball_subset_ball (min_le_left _ _) this.1, this.2⟩
    · exact ⟨y, mem_ball_self hε, hyG⟩
  let P : Pt → Pt → Prop := fun a b => ∃ ρ₁ > 0, ∃ ρ₂ > 0, ∀ y₁ ∈ ball a ρ₁, ∀ y₂ ∈ ball b ρ₂,
    y₁ ∉ graphSet G → y₂ ∉ graphSet G → gFun G x y₁ = gFun G x y₂
  have hP : P z z' := by
    refine hS.induction₂' P ?_ ?_ (hmemS z hz) (hmemS z' hz')
    · intro a ha
      obtain ⟨ρ, hρ, h⟩ := hloc a ha
      have : ∀ᶠ b in 𝓝 a, P a b ∧ P b a := by
        filter_upwards [ball_mem_nhds a (half_pos hρ)] with b hb
        have hsub : ball b (ρ / 2) ⊆ ball a ρ := by
          intro y hy
          rw [mem_ball] at hy hb ⊢
          linarith [dist_triangle y b a]
        exact ⟨⟨ρ, hρ, ρ / 2, half_pos hρ, fun y₁ h₁ y₂ h₂ => h y₁ h₁ y₂ (hsub h₂)⟩,
          ⟨ρ / 2, half_pos hρ, ρ, hρ, fun y₁ h₁ y₂ h₂ => h y₁ (hsub h₁) y₂ h₂⟩⟩
      exact nhdsWithin_le_nhds this
    · rintro a b c - hb - ⟨ρ₁, hρ₁, ρ₂, hρ₂, h₁⟩ ⟨ρ₃, hρ₃, ρ₄, hρ₄, h₂⟩
      obtain ⟨y', hy', hy'G⟩ := hdense b hb (min ρ₂ ρ₃) (lt_min hρ₂ hρ₃)
      refine ⟨ρ₁, hρ₁, ρ₄, hρ₄, fun y₁ hy₁ y₂ hy₂ hn₁ hn₂ => ?_⟩
      exact (h₁ y₁ hy₁ y' (ball_subset_ball (min_le_left _ _) hy') hn₁ hy'G).trans
        (h₂ y' (ball_subset_ball (min_le_right _ _) hy') y₂ hy₂ hy'G hn₂)
  obtain ⟨ρ₁, hρ₁, ρ₂, hρ₂, h⟩ := hP
  exact h z (mem_ball_self hρ₁) z' (mem_ball_self hρ₂) hz hz'

/-- **A separating graph has an odd cycle.** -/
theorem cycParity_oddSet_ne {G : Finset Seg} (hG : IsProper G) {x y : Pt}
    (hsep : SeparatesPts (graphSet G) x y) :
    cycParity (oddSet G x) x ≠ cycParity (oddSet G x) y := by
  obtain ⟨hx, hy, hyC⟩ := hsep
  have h := gFun_const hG x hx hy
  have hxC : x ∈ connectedComponentIn (graphSet G)ᶜ x := mem_connectedComponentIn hx
  unfold gFun at h
  rw [if_pos hxC, if_neg hyC, zero_add] at h
  intro h'
  rw [h'] at h
  exact one_ne_zero (add_eq_right.1 h)

theorem separatingGraphHasOddCycle : SeparatingGraphHasOddCycle := fun G hG x _ hsep =>
  ⟨oddSet G x, oddSet_subset G x, isCycle_oddSet hG x, cycParity_oddSet_ne hG hsep⟩

/-- **Janiszewski for polygonal compacta.** -/
theorem janiszewskiPoly_holds : JaniszewskiPoly :=
  janiszewskiPoly_of_oddCycle separatingGraphHasOddCycle

end HPC.Plane
