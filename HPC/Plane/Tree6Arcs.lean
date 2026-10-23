import HPC.Plane.Tree6Local

/-!
# Batch 118, auxiliary: polygonal paths and simple polygonal arcs (vertex functions)

Polygonal paths are handled here through a vertex function `v : ℕ → Pt` and a vertex count `n`
(`vpath v n`, the union of the segments `v i — v (i+1)`, `i + 1 < n`); the list form of the
skeleton (`polyPathOf`, `IsSimplePolyArc` in `HPC/Plane/Tree6.lean`) is the special case
`v i = w.getD i 0`, `n = w.length`.

* polygonal connectivity of connected open sets (`exists_vpath_of_isConnected`);
* loop erasure by a shortest path (`exists_sarc_of_vpath`): a path with the fewest vertices is
  simple, since a repeated vertex, a backtrack or a crossing gives a shorter one;
* compactness and connectedness of polygonal paths;
* the first point of a simple arc in a closed set; reversal; concatenation; closing two arcs into a
  simple closed polygon.
-/

namespace HPC.Plane

open Set Metric

/-- The polygonal path with vertices `v 0, …, v (n-1)`. -/
def vpath (v : ℕ → Pt) (n : ℕ) : Set Pt :=
  ⋃ i ∈ Finset.range (n - 1), segment ℝ (v i) (v (i + 1))

/-- A simple polygonal arc, in vertex-function form: at least two vertices, distinct; consecutive
segments meet only in their common vertex; non-consecutive segments are disjoint. -/
def IsSArc (v : ℕ → Pt) (n : ℕ) : Prop :=
  2 ≤ n ∧ (∀ i j, i < j → j < n → v i ≠ v j) ∧
    (∀ i, i + 2 < n →
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v (i + 1)) (v (i + 2)) ⊆ {v (i + 1)}) ∧
    (∀ i j, i + 1 < j → j + 1 < n →
      Disjoint (segment ℝ (v i) (v (i + 1))) (segment ℝ (v j) (v (j + 1))))

theorem mem_vpath {v : ℕ → Pt} {n : ℕ} {x : Pt} :
    x ∈ vpath v n ↔ ∃ i, i + 1 < n ∧ x ∈ segment ℝ (v i) (v (i + 1)) := by
  simp only [vpath, mem_iUnion, Finset.mem_range, exists_prop]
  constructor <;> rintro ⟨i, hi, hx⟩ <;> exact ⟨i, by omega, hx⟩

theorem segment_subset_vpath {v : ℕ → Pt} {n i : ℕ} (hi : i + 1 < n) :
    segment ℝ (v i) (v (i + 1)) ⊆ vpath v n :=
  fun _ hx => mem_vpath.2 ⟨i, hi, hx⟩

theorem vpath_subset_iff {v : ℕ → Pt} {n : ℕ} {S : Set Pt} :
    vpath v n ⊆ S ↔ ∀ i, i + 1 < n → segment ℝ (v i) (v (i + 1)) ⊆ S := by
  constructor
  · exact fun h i hi => (segment_subset_vpath hi).trans h
  · intro h x hx
    obtain ⟨i, hi, hx⟩ := mem_vpath.1 hx
    exact h i hi hx

theorem vpath_congr {v v' : ℕ → Pt} {n : ℕ} (h : ∀ i, i < n → v i = v' i) :
    vpath v n = vpath v' n := by
  ext x
  simp only [mem_vpath]
  constructor <;> rintro ⟨i, hi, hx⟩ <;> refine ⟨i, hi, ?_⟩
  · rwa [← h i (by omega), ← h (i + 1) hi]
  · rwa [h i (by omega), h (i + 1) hi]

/-- Appending a vertex. -/
theorem vpath_snoc (v : ℕ → Pt) {n : ℕ} (hn : 1 ≤ n) (y : Pt) :
    vpath (fun i => if i < n then v i else y) (n + 1) = vpath v n ∪ segment ℝ (v (n - 1)) y := by
  ext x
  simp only [mem_vpath, mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases Nat.lt_or_ge (i + 1) n with h | h
    · left
      refine ⟨i, h, ?_⟩
      simpa [show i < n by omega, h] using hx
    · right
      have hi' : i = n - 1 := by omega
      subst hi'
      simpa [show n - 1 < n by omega, show ¬ (n - 1 + 1 < n) by omega] using hx
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, by omega, by simpa [show i < n by omega, hi] using hx⟩
    · refine ⟨n - 1, by omega, ?_⟩
      simpa [show n - 1 < n by omega, show ¬ (n - 1 + 1 < n) by omega] using hx

/-! ### Polygonal connectivity -/

/-- **A connected open set of the plane is polygonally connected.** -/
theorem exists_vpath_of_isConnected {h : Set Pt} (ho : IsOpen h) (hc : IsConnected h)
    {p q : Pt} (hp : p ∈ h) (hq : q ∈ h) :
    ∃ (v : ℕ → Pt) (n : ℕ), 1 ≤ n ∧ v 0 = p ∧ v (n - 1) = q ∧ vpath v n ⊆ h := by
  set R := {y | ∃ (v : ℕ → Pt) (n : ℕ), 1 ≤ n ∧ v 0 = p ∧ v (n - 1) = y ∧ vpath v n ⊆ h}
    with hR
  have hext : ∀ y ∈ R, ∀ y', segment ℝ y y' ⊆ h → y' ∈ R := by
    rintro y ⟨v, n, hn, h0, hy, hsub⟩ y' hseg
    refine ⟨fun i => if i < n then v i else y', n + 1, by omega, ?_, ?_, ?_⟩
    · simp [show 0 < n by omega, h0]
    · simp
    · rw [vpath_snoc v hn y']; exact union_subset hsub (hy ▸ hseg)
  have hpR : p ∈ R := ⟨fun _ => p, 1, le_rfl, rfl, rfl, by simp [vpath]⟩
  set u := {y | ∃ ε > 0, ball y ε ⊆ h ∧ ball y ε ⊆ R} with hu
  set w := {y | ∃ ε > 0, ball y ε ⊆ h ∧ Disjoint (ball y ε) R} with hw
  have hsmall : ∀ (y : Pt) (ε : ℝ) (y' : Pt), 0 < ε → y' ∈ ball y (ε / 2) →
      ball y' (ε / 2) ⊆ ball y ε := by
    intro y ε y' hε hy'
    refine ball_subset_ball' ?_
    rw [mem_ball] at hy'
    linarith
  have huo : IsOpen u := by
    rw [Metric.isOpen_iff]
    rintro y ⟨ε, hε, h1, h2⟩
    exact ⟨ε / 2, by positivity, fun y' hy' => ⟨ε / 2, by positivity,
      (hsmall y ε y' hε hy').trans h1, (hsmall y ε y' hε hy').trans h2⟩⟩
  have hwo : IsOpen w := by
    rw [Metric.isOpen_iff]
    rintro y ⟨ε, hε, h1, h2⟩
    exact ⟨ε / 2, by positivity, fun y' hy' => ⟨ε / 2, by positivity,
      (hsmall y ε y' hε hy').trans h1, h2.mono_left (hsmall y ε y' hε hy')⟩⟩
  have hcov : h ⊆ u ∪ w := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ho y hy
    by_cases hyR : y ∈ R
    · exact Or.inl ⟨ε, hε, hball, fun y' hy' => hext y hyR y'
        (((convex_ball y ε).segment_subset (mem_ball_self hε) hy').trans hball)⟩
    · refine Or.inr ⟨ε, hε, hball, Set.disjoint_left.2 fun y' hy' hy'R => hyR ?_⟩
      exact hext y' hy'R y (((convex_ball y ε).segment_subset hy' (mem_ball_self hε)).trans hball)
  have hdis : h ∩ (u ∩ w) = ∅ := by
    apply eq_empty_of_forall_notMem
    rintro y ⟨-, ⟨ε, hε, -, h1⟩, ⟨ε', hε', -, h2⟩⟩
    have hy : y ∈ ball y (min ε ε') := mem_ball_self (lt_min hε hε')
    exact h2.notMem_of_mem_left (ball_subset_ball (min_le_right _ _) hy)
      (h1 (ball_subset_ball (min_le_left _ _) hy))
  rcases isPreconnected_iff_subset_of_disjoint.1 hc.isPreconnected u w huo hwo hcov hdis with
    hsub | hsub
  · obtain ⟨ε, hε, -, h2⟩ := hsub hq
    exact h2 (mem_ball_self hε)
  · obtain ⟨ε, hε, -, h2⟩ := hsub hp
    exact absurd hpR (h2.notMem_of_mem_left (mem_ball_self hε))

/-! ### Loop erasure -/

/-- A backtrack: if the segments `a — b` and `b — c` share a point other than `b`, the segment
`a — c` lies in their union. -/
theorem segment_subset_of_backtrack {a b c z : Pt} (hz1 : z ∈ segment ℝ a b)
    (hz2 : z ∈ segment ℝ b c) (hzb : z ≠ b) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  rw [segment_symm] at hz1
  rw [segment_eq_image'] at hz1 hz2
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hz1
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := hz2
  have hs0' : s ≠ 0 := by rintro rfl; simp at hs; exact hzb hs.symm
  have ht0' : t ≠ 0 := by rintro rfl; simp at ht; exact hzb ht.symm
  have hst : s • (a - b) = t • (c - b) := by
    have := hs.trans ht.symm
    simpa using this
  rcases le_total s t with h | h
  · -- `c` lies on `b — a`
    have hc : c ∈ segment ℝ a b := by
      rw [segment_symm, segment_eq_image']
      refine ⟨s / t, ⟨div_nonneg hs0 ht0, (div_le_one (lt_of_le_of_ne ht0 (Ne.symm ht0'))).2 h⟩,
        ?_⟩
      simp only
      rw [div_eq_mul_inv, mul_comm, ← smul_smul, hst, smul_smul, inv_mul_cancel₀ ht0', one_smul]
      abel
    exact ((convex_segment a b).segment_subset (left_mem_segment _ _ _) hc).trans
      subset_union_left
  · have ha : a ∈ segment ℝ b c := by
      rw [segment_eq_image']
      refine ⟨t / s, ⟨div_nonneg ht0 hs0, (div_le_one (lt_of_le_of_ne hs0 (Ne.symm hs0'))).2 h⟩,
        ?_⟩
      simp only
      rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hst, smul_smul, inv_mul_cancel₀ hs0', one_smul]
      abel
    exact ((convex_segment b c).segment_subset ha (right_mem_segment _ _ _)).trans
      subset_union_right

/-- **Loop erasure.** A polygonal path from `p` to `q ≠ p` contains a simple polygonal arc from
`p` to `q`: a path inside it with the fewest vertices is simple. -/
theorem exists_sarc_of_vpath {v : ℕ → Pt} {n : ℕ} {p q : Pt} (hn : 1 ≤ n) (h0 : v 0 = p)
    (h1 : v (n - 1) = q) (hpq : p ≠ q) :
    ∃ (u : ℕ → Pt) (k : ℕ), IsSArc u k ∧ u 0 = p ∧ u (k - 1) = q ∧ vpath u k ⊆ vpath v n := by
  classical
  set S := vpath v n
  have hex : ∃ k, ∃ u : ℕ → Pt, 1 ≤ k ∧ u 0 = p ∧ u (k - 1) = q ∧ vpath u k ⊆ S :=
    ⟨n, v, hn, h0, h1, subset_rfl⟩
  obtain ⟨u, hk1, hu0, hu1, huS⟩ := Nat.find_spec hex
  set k := Nat.find hex with hk
  have hmin : ∀ k' < k, ∀ u' : ℕ → Pt, 1 ≤ k' → u' 0 = p → u' (k' - 1) = q →
      ¬ vpath u' k' ⊆ S := fun k' hk' u' h1 h2 h3 h4 =>
    Nat.find_min hex hk' ⟨u', h1, h2, h3, h4⟩
  have hseg : ∀ i, i + 1 < k → segment ℝ (u i) (u (i + 1)) ⊆ S :=
    vpath_subset_iff.1 huS
  refine ⟨u, k, ⟨?_, ?_, ?_, ?_⟩, hu0, hu1, huS⟩
  · by_contra h
    have : k = 1 := by omega
    rw [this] at hu1
    exact hpq (hu0.symm.trans hu1)
  · -- distinct vertices
    intro i j hij hj heq
    refine hmin (k - (j - i)) (by omega) (fun m => if m ≤ i then u m else u (m + (j - i)))
      (by omega) (by simp [hu0]) ?_ ?_
    · by_cases hc : k - (j - i) - 1 ≤ i
      · have : j = k - 1 := by omega
        simp only [hc, if_true]
        rw [show k - (j - i) - 1 = i by omega, heq, this, hu1]
      · simp only [hc, if_false]
        rw [show k - (j - i) - 1 + (j - i) = k - 1 by omega, hu1]
    · refine vpath_subset_iff.2 fun m hm => ?_
      by_cases hm1 : m + 1 ≤ i
      · simp only [show m ≤ i by omega, hm1, if_true]
        exact hseg m (by omega)
      by_cases hm2 : m = i
      · subst hm2
        simp only [le_refl, if_true, show ¬ (m + 1 ≤ m) by omega, if_false]
        rw [heq, show m + 1 + (j - m) = j + 1 by omega]
        exact hseg j (by omega)
      · simp only [show ¬ m ≤ i by omega, show ¬ (m + 1 ≤ i) by omega, if_false]
        rw [show m + 1 + (j - i) = m + (j - i) + 1 by omega]
        exact hseg _ (by omega)
  · -- consecutive segments
    intro i hi z ⟨hz1, hz2⟩
    by_contra hzb
    refine hmin (k - 1) (by omega) (fun m => if m ≤ i then u m else u (m + 1)) (by omega)
      (by simp [hu0]) ?_ ?_
    · simp only [show ¬ (k - 1 - 1 ≤ i) by omega, if_false]
      rw [show k - 1 - 1 + 1 = k - 1 by omega, hu1]
    · refine vpath_subset_iff.2 fun m hm => ?_
      by_cases hm1 : m + 1 ≤ i
      · simp only [show m ≤ i by omega, hm1, if_true]
        exact hseg m (by omega)
      by_cases hm2 : m = i
      · subst hm2
        simp only [le_refl, if_true, show ¬ (m + 1 ≤ m) by omega, if_false]
        refine (segment_subset_of_backtrack hz1 hz2 hzb).trans (union_subset ?_ ?_)
        · exact hseg m (by omega)
        · exact hseg (m + 1) (by omega)
      · simp only [show ¬ m ≤ i by omega, show ¬ (m + 1 ≤ i) by omega, if_false]
        exact hseg _ (by omega)
  · -- non-consecutive segments
    intro i j hij hj
    rw [Set.disjoint_left]
    intro z hz1 hz2
    refine hmin (k - (j - i - 1)) (by omega)
      (fun m => if m ≤ i then u m else if m = i + 1 then z else u (m + (j - i - 1)))
      (by omega) (by simp [hu0]) ?_ ?_
    · simp only [show ¬ (k - (j - i - 1) - 1 ≤ i) by omega,
        show ¬ (k - (j - i - 1) - 1 = i + 1) by omega, if_false]
      rw [show k - (j - i - 1) - 1 + (j - i - 1) = k - 1 by omega, hu1]
    · refine vpath_subset_iff.2 fun m hm => ?_
      by_cases hm1 : m + 1 ≤ i
      · simp only [show m ≤ i by omega, hm1, if_true]
        exact hseg m (by omega)
      by_cases hm2 : m = i
      · subst hm2
        simp only [le_refl, if_true, show ¬ (m + 1 ≤ m) by omega, if_false]
        exact ((convex_segment _ _).segment_subset (left_mem_segment _ _ _) hz1).trans
          (hseg m (by omega))
      by_cases hm3 : m = i + 1
      · subst hm3
        simp only [show ¬ (i + 1 ≤ i) by omega, show ¬ (i + 1 + 1 ≤ i) by omega,
          show ¬ (i + 1 + 1 = i + 1) by omega, if_false, if_true]
        rw [show i + 1 + 1 + (j - i - 1) = j + 1 by omega]
        exact ((convex_segment _ _).segment_subset hz2 (right_mem_segment _ _ _)).trans
          (hseg j (by omega))
      · simp only [show ¬ m ≤ i by omega, show ¬ (m + 1 ≤ i) by omega, hm3,
          show ¬ (m + 1 = i + 1) by omega, if_false]
        rw [show m + 1 + (j - i - 1) = m + (j - i - 1) + 1 by omega]
        exact hseg _ (by omega)

/-! ### Compactness, connectedness, vertices -/

theorem isCompact_vpath (v : ℕ → Pt) (n : ℕ) : IsCompact (vpath v n) :=
  (Finset.range (n - 1)).isCompact_biUnion fun _ _ => isCompact_segment' _ _

theorem vertex_mem_vpath {v : ℕ → Pt} {n k : ℕ} (hn : 2 ≤ n) (hk : k < n) : v k ∈ vpath v n := by
  rcases Nat.lt_or_ge (k + 1) n with h | h
  · exact segment_subset_vpath h (left_mem_segment _ _ _)
  · have : k = (k - 1) + 1 := by omega
    rw [this]
    exact segment_subset_vpath (by omega) (right_mem_segment _ _ _)

theorem isConnected_vpath (v : ℕ → Pt) {n : ℕ} (hn : 2 ≤ n) : IsConnected (vpath v n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      have : vpath v 2 = segment ℝ (v 0) (v 1) := by
        ext x; simp only [mem_vpath]
        constructor
        · rintro ⟨i, hi, hx⟩; obtain rfl : i = 0 := by omega
          exact hx
        · intro hx; exact ⟨0, by omega, hx⟩
      rw [this]
      exact ⟨⟨_, left_mem_segment _ _ _⟩, (convex_segment _ _).isPreconnected⟩
    · have heq : vpath v (n + 1) = vpath v n ∪ segment ℝ (v (n - 1)) (v n) := by
        rw [← vpath_snoc v (by omega) (v n)]
        exact vpath_congr fun i hi => by
          by_cases h' : i < n
          · simp [h']
          · simp [show i = n by omega]
      rw [heq]
      exact (ih h).union ⟨v (n - 1), vertex_mem_vpath h (by omega), left_mem_segment _ _ _⟩
        ⟨⟨_, left_mem_segment _ _ _⟩, (convex_segment _ _).isPreconnected⟩

/-- In a simple arc, a vertex lies only on the (one or two) segments through it. -/
theorem IsSArc.vertex_mem_seg {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) {k i : ℕ} (hk : k < n)
    (hi : i + 1 < n) (hki : v k ∈ segment ℝ (v i) (v (i + 1))) : i = k ∨ i + 1 = k := by
  obtain ⟨hn, hd, hc, hnc⟩ := h
  by_contra hne
  push_neg at hne
  rcases Nat.lt_or_ge (k + 1) n with hk1 | hk1
  · -- `v k` is on the segment `k`
    have hkk : v k ∈ segment ℝ (v k) (v (k + 1)) := left_mem_segment _ _ _
    rcases lt_trichotomy i k with hik | hik | hik
    · -- `i + 1 < k`
      have : i + 1 < k := by omega
      exact (hnc i k this hk1).notMem_of_mem_left hki hkk
    · exact hne.1 hik
    · rcases Nat.lt_or_ge (k + 1) i with h' | h'
      · exact (hnc k i h' hi).notMem_of_mem_left hkk hki
      · have : i = k + 1 := by omega
        subst this
        have := hc k (by omega) ⟨hkk, hki⟩
        exact hd k (k + 1) (by omega) hk1 this
  · have hk' : k = n - 1 := by omega
    have hkk : v k ∈ segment ℝ (v (k - 1)) (v (k - 1 + 1)) := by
      rw [show k - 1 + 1 = k by omega]; exact right_mem_segment _ _ _
    rcases Nat.lt_or_ge (i + 1) (k - 1) with h' | h'
    · exact (hnc i (k - 1) h' (by omega)).notMem_of_mem_left hki hkk
    · have : i = k - 2 := by omega
      subst this
      have h2 := hc (k - 2) (by omega)
      rw [show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = k by omega] at h2
      rw [show k - 1 + 1 = k by omega] at hkk
      rw [show k - 2 + 1 = k - 1 by omega] at hki
      have := h2 ⟨hki, hkk⟩
      exact hd (k - 1) k (by omega) hk this.symm

theorem IsSArc.start_mem_seg {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) {i : ℕ} (hi : i + 1 < n)
    (h0 : v 0 ∈ segment ℝ (v i) (v (i + 1))) : i = 0 := by
  rcases h.vertex_mem_seg (by omega) hi h0 with h' | h' <;> omega

theorem IsSArc.end_mem_seg {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) {i : ℕ} (hi : i + 1 < n)
    (h0 : v (n - 1) ∈ segment ℝ (v i) (v (i + 1))) : i = n - 2 := by
  rcases h.vertex_mem_seg (by omega) hi h0 with h' | h' <;> omega

/-! ### The first point in a closed set -/

/-- **The first point of a simple arc in a closed set** (walking from `v 0`): the arc up to it is
a simple arc meeting the set only there. -/
theorem IsSArc.exists_first_mem {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) {K : Set Pt}
    (hK : IsClosed K) (hne : (vpath v n ∩ K).Nonempty) (hp : v 0 ∉ K) :
    ∃ x ∈ vpath v n ∩ K, ∃ (u : ℕ → Pt) (k : ℕ), IsSArc u k ∧ u 0 = v 0 ∧ u (k - 1) = x ∧
      vpath u k ⊆ vpath v n ∧ vpath u k ∩ K = {x} := by
  classical
  obtain ⟨hn, hd, hc, hnc⟩ := h
  have hex : ∃ i, i + 1 < n ∧ (segment ℝ (v i) (v (i + 1)) ∩ K).Nonempty := by
    obtain ⟨y, hy, hyK⟩ := hne
    obtain ⟨i, hi, hyi⟩ := mem_vpath.1 hy
    exact ⟨i, hi, y, hyi, hyK⟩
  obtain ⟨hi₀, hne₀⟩ := Nat.find_spec hex
  set i₀ := Nat.find hex with hi₀def
  have hmin : ∀ i < i₀, ¬ (segment ℝ (v i) (v (i + 1)) ∩ K).Nonempty := fun i hi h' =>
    Nat.find_min hex hi ⟨by omega, h'⟩
  set f : ℝ → Pt := fun t => v i₀ + t • (v (i₀ + 1) - v i₀) with hf
  have hfc : Continuous f := by fun_prop
  set T := Icc (0 : ℝ) 1 ∩ f ⁻¹' K with hT
  have hTc : IsCompact T := isCompact_Icc.inter_right (hK.preimage hfc)
  have hTne : T.Nonempty := by
    obtain ⟨y, hy, hyK⟩ := hne₀
    rw [segment_eq_image'] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨t, ht, hyK⟩
  obtain ⟨t₀, ⟨ht₀I, ht₀K⟩, ht₀min⟩ := hTc.exists_isLeast hTne
  set x := f t₀ with hx
  have hdv : v (i₀ + 1) - v i₀ ≠ 0 := sub_ne_zero.2 (hd i₀ (i₀ + 1) (by omega) hi₀).symm
  have hxseg : x ∈ segment ℝ (v i₀) (v (i₀ + 1)) := by
    rw [segment_eq_image']; exact ⟨t₀, ht₀I, rfl⟩
  have ht₀pos : 0 < t₀ := by
    rcases ht₀I.1.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hxv : x = v i₀ := by simp [hx, hf, ← h']
      rcases Nat.eq_zero_or_pos i₀ with h0 | h0
      · exact hp (by rw [← h0, ← hxv]; exact ht₀K)
      · refine hmin (i₀ - 1) (by omega) ⟨x, ?_, ht₀K⟩
        rw [hxv, show i₀ - 1 + 1 = i₀ by omega]; exact right_mem_segment _ _ _
  have hxne : ∀ m, m ≤ i₀ → x ≠ v m := by
    intro m hm hxm
    have hS : IsSArc v n := ⟨hn, hd, hc, hnc⟩
    rcases hS.vertex_mem_seg (by omega) hi₀ (hxm ▸ hxseg) with h' | h'
    · subst h'
      have : t₀ • (v (i₀ + 1) - v i₀) = 0 := by
        have := hxm; simp only [hx, hf] at this
        simpa using this
      rcases smul_eq_zero.1 this with h'' | h''
      · linarith
      · exact hdv h''
    · omega
  have hsub : segment ℝ (v i₀) x ⊆ segment ℝ (v i₀) (v (i₀ + 1)) :=
    (convex_segment _ _).segment_subset (left_mem_segment _ _ _) hxseg
  set u : ℕ → Pt := fun m => if m ≤ i₀ then v m else x with hu
  have hseg_u : ∀ m, m + 1 < i₀ + 2 → segment ℝ (u m) (u (m + 1)) ⊆
      segment ℝ (v m) (v (m + 1)) := by
    intro m hm
    by_cases hm' : m + 1 ≤ i₀
    · simp [hu, hm', show m ≤ i₀ by omega]
    · have : m = i₀ := by omega
      subst this
      simpa [hu] using hsub
  refine ⟨x, ⟨segment_subset_vpath hi₀ hxseg, ht₀K⟩, u, i₀ + 2, ⟨by omega, ?_, ?_, ?_⟩,
    by simp [hu], by simp [hu], ?_, ?_⟩
  · intro m m' hmm' hm'
    by_cases h' : m' ≤ i₀
    · simp only [hu, h', show m ≤ i₀ by omega, if_true]
      exact hd m m' hmm' (by omega)
    · simp only [hu, h', show m ≤ i₀ by omega, if_true, if_false]
      exact fun h'' => hxne m (by omega) h''.symm
  · intro m hm
    have h1 := hseg_u m (by omega)
    have h2 := hseg_u (m + 1) (by omega)
    have hum : u (m + 1) = v (m + 1) := by simp [hu, show m + 1 ≤ i₀ by omega]
    rw [hum] at h1 h2 ⊢
    exact (inter_subset_inter h1 h2).trans (hc m (by omega))
  · intro m m' hmm' hm'
    exact (hnc m m' hmm' (by omega)).mono (hseg_u m (by omega)) (hseg_u m' (by omega))
  · exact vpath_subset_iff.2 fun m hm => (hseg_u m hm).trans (segment_subset_vpath (by omega))
  · apply subset_antisymm
    · rintro y ⟨hy, hyK⟩
      obtain ⟨m, hm, hym⟩ := mem_vpath.1 hy
      by_cases hm' : m + 1 ≤ i₀
      · exact absurd ⟨y, hseg_u m hm hym, hyK⟩ (hmin m (by omega))
      · have : m = i₀ := by omega
        subst this
        simp only [hu, le_refl, if_true, show ¬ (i₀ + 1 ≤ i₀) by omega, if_false] at hym
        rw [segment_eq_image'] at hym
        obtain ⟨s, hs, rfl⟩ := hym
        have hfs : v i₀ + s • (x - v i₀) = f (s * t₀) := by
          simp only [hf, hx]; rw [add_sub_cancel_left, smul_smul]
        show v i₀ + s • (x - v i₀) ∈ ({x} : Set Pt)
        change v i₀ + s • (x - v i₀) ∈ K at hyK
        rw [hfs] at hyK ⊢
        have hle := ht₀min ⟨⟨mul_nonneg hs.1 ht₀I.1, by nlinarith [hs.2, ht₀I.2, hs.1]⟩, hyK⟩
        have : s = 1 := by
          rcases hs.2.lt_or_eq with h' | h'
          · nlinarith
          · exact h'
        rw [this, one_mul]
        rfl
    · rintro y rfl
      refine ⟨segment_subset_vpath (n := i₀ + 2) (i := i₀) (by omega) ?_, ht₀K⟩
      simp only [hu, le_refl, if_true, show ¬ (i₀ + 1 ≤ i₀) by omega, if_false]
      exact right_mem_segment _ _ _

/-! ### Reversal and concatenation -/

theorem rev_segment (v : ℕ → Pt) {n i : ℕ} (hi : i + 1 < n) :
    segment ℝ (v (n - 1 - i)) (v (n - 1 - (i + 1))) =
      segment ℝ (v (n - 2 - i)) (v (n - 2 - i + 1)) := by
  rw [show n - 1 - (i + 1) = n - 2 - i by omega, show n - 1 - i = n - 2 - i + 1 by omega,
    segment_symm]

theorem vpath_reverse (v : ℕ → Pt) (n : ℕ) : vpath (fun i => v (n - 1 - i)) n = vpath v n := by
  ext x
  simp only [mem_vpath]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨n - 2 - i, by omega, by rwa [rev_segment v hi] at hx⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨n - 2 - i, by omega, ?_⟩
    rw [rev_segment v (by omega), show n - 2 - (n - 2 - i) = i by omega]
    exact hx

theorem IsSArc.reverse {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) :
    IsSArc (fun i => v (n - 1 - i)) n := by
  obtain ⟨hn, hd, hc, hnc⟩ := h
  refine ⟨hn, fun i j hij hj => (hd (n - 1 - j) (n - 1 - i) (by omega) (by omega)).symm, ?_, ?_⟩
  · intro i hi
    simp only
    have h1 := rev_segment v (n := n) (i := i) (by omega)
    have h2 := rev_segment v (n := n) (i := i + 1) (by omega)
    rw [h1, h2, show n - 2 - (i + 1) = n - 3 - i by omega, show n - 2 - i = n - 3 - i + 1 by omega,
      show n - 1 - (i + 1) = n - 3 - i + 1 by omega, inter_comm]
    exact hc (n - 3 - i) (by omega)
  · intro i j hij hj
    simp only
    rw [rev_segment v (by omega), rev_segment v (by omega)]
    exact (hnc (n - 2 - j) (n - 2 - i) (by omega) (by omega)).symm

/-- The concatenation of two vertex functions (the second starting where the first ends). -/
def vcat (v : ℕ → Pt) (n : ℕ) (u : ℕ → Pt) : ℕ → Pt :=
  fun i => if i < n then v i else u (i - (n - 1))

theorem vcat_seg_left {v u : ℕ → Pt} {n i : ℕ} (hi : i + 1 < n) :
    segment ℝ (vcat v n u i) (vcat v n u (i + 1)) = segment ℝ (v i) (v (i + 1)) := by
  simp [vcat, show i < n by omega, hi]

theorem vcat_seg_right {v u : ℕ → Pt} {n i : ℕ} (hn : 1 ≤ n) (hvu : v (n - 1) = u 0)
    (hi : n - 1 ≤ i) :
    segment ℝ (vcat v n u i) (vcat v n u (i + 1)) =
      segment ℝ (u (i - (n - 1))) (u (i - (n - 1) + 1)) := by
  simp only [vcat, show ¬ (i + 1 < n) by omega, if_false]
  rw [show i + 1 - (n - 1) = i - (n - 1) + 1 by omega]
  by_cases h : i < n
  · have : i = n - 1 := by omega
    subst this
    simp [show n - 1 < n by omega, hvu]
  · simp only [h, if_false]

theorem vpath_vcat {v u : ℕ → Pt} {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hvu : v (n - 1) = u 0) :
    vpath (vcat v n u) (n + k - 1) = vpath v n ∪ vpath u k := by
  ext x
  simp only [mem_vpath, mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases Nat.lt_or_ge (i + 1) n with h | h
    · exact Or.inl ⟨i, h, by rwa [vcat_seg_left h] at hx⟩
    · exact Or.inr ⟨i - (n - 1), by omega, by rwa [vcat_seg_right hn hvu (by omega)] at hx⟩
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
    · exact ⟨i, by omega, by rwa [vcat_seg_left hi]⟩
    · refine ⟨i + (n - 1), by omega, ?_⟩
      rw [vcat_seg_right hn hvu (by omega), show i + (n - 1) - (n - 1) = i by omega]
      exact hx

/-- **Concatenation**: simple arcs `a → b` and `b → c` meeting only at `b` form a simple arc
`a → c`. -/
theorem IsSArc.concat {v u : ℕ → Pt} {n k : ℕ} (hv : IsSArc v n) (hu : IsSArc u k)
    (hvu : v (n - 1) = u 0) (hmeet : vpath v n ∩ vpath u k = {u 0}) :
    IsSArc (vcat v n u) (n + k - 1) := by
  have hv' := hv
  have hu' := hu
  obtain ⟨hn, hd, hc, hnc⟩ := hv
  obtain ⟨hk, hd', hc', hnc'⟩ := hu
  have hL : ∀ i, i + 1 < n → segment ℝ (vcat v n u i) (vcat v n u (i + 1)) ⊆ vpath v n :=
    fun i hi => (vcat_seg_left hi).symm ▸ segment_subset_vpath hi
  have hR : ∀ i, n - 1 ≤ i → i + 1 < n + k - 1 →
      segment ℝ (vcat v n u i) (vcat v n u (i + 1)) ⊆ vpath u k :=
    fun i h1 h2 => (vcat_seg_right (by omega) hvu h1).symm ▸ segment_subset_vpath (by omega)
  have hvL : ∀ i, i < n → vcat v n u i = v i := fun i hi => by simp [vcat, hi]
  have hvR : ∀ i, n - 1 ≤ i → vcat v n u i = u (i - (n - 1)) := by
    intro i hi
    by_cases h : i < n
    · have : i = n - 1 := by omega
      simp [vcat, this, hvu]
    · simp [vcat, h]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i j hij hj
    by_cases hjn : j < n
    · rw [hvL i (by omega), hvL j hjn]; exact hd i j hij hjn
    by_cases hin : n - 1 ≤ i
    · rw [hvR i hin, hvR j (by omega)]; exact hd' _ _ (by omega) (by omega)
    · rw [hvL i (by omega), hvR j (by omega)]
      intro heq
      have hmem : v i ∈ vpath v n ∩ vpath u k :=
        ⟨vertex_mem_vpath hn (by omega), heq ▸ vertex_mem_vpath hk (by omega)⟩
      rw [hmeet] at hmem
      have h1 : v i = v (n - 1) := hmem.trans hvu.symm
      exact hd i (n - 1) (by omega) (by omega) h1
  · intro i hi
    by_cases h1 : i + 2 < n
    · rw [vcat_seg_left (by omega), vcat_seg_left (by omega), hvL (i + 1) (by omega)]
      exact hc i h1
    by_cases h2 : n - 1 ≤ i
    · rw [vcat_seg_right (by omega) hvu h2, vcat_seg_right (by omega) hvu (by omega),
        hvR (i + 1) (by omega), show i + 1 - (n - 1) = i - (n - 1) + 1 by omega]
      exact hc' _ (by omega)
    · have hi' : i = n - 2 := by omega
      intro z hz
      have hz' : z ∈ vpath v n ∩ vpath u k := ⟨hL i (by omega) hz.1, hR (i + 1) (by omega) hi hz.2⟩
      rw [hmeet] at hz'
      rw [hz', hvR (i + 1) (by omega), show i + 1 - (n - 1) = 0 by omega]
      rfl
  · intro i j hij hj
    by_cases h1 : j + 1 < n
    · rw [vcat_seg_left (by omega), vcat_seg_left h1]; exact hnc i j hij h1
    by_cases h2 : n - 1 ≤ i
    · rw [vcat_seg_right (by omega) hvu h2, vcat_seg_right (by omega) hvu (by omega)]
      exact hnc' _ _ (by omega) (by omega)
    · rw [Set.disjoint_left]
      intro z hz1 hz2
      have hz' : z ∈ vpath v n ∩ vpath u k := ⟨hL i (by omega) hz1, hR j (by omega) hj hz2⟩
      rw [hmeet] at hz'
      rw [vcat_seg_left (by omega)] at hz1
      rw [vcat_seg_right (by omega) hvu (by omega)] at hz2
      have e1 := hv'.end_mem_seg (i := i) (by omega) (by rw [hvu, ← hz']; exact hz1)
      have e2 := hu'.start_mem_seg (i := j - (n - 1)) (by omega) (by rw [← hz']; exact hz2)
      omega

/-- **The final part of a simple arc** from one of its points: a simple arc from `x` to the end,
inside the arc. (Reverse, take the first point in `{x}`, reverse back.) -/
theorem IsSArc.exists_suffix {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) {x : Pt}
    (hx : x ∈ vpath v n) (hxe : x ≠ v (n - 1)) :
    ∃ (u : ℕ → Pt) (k : ℕ), IsSArc u k ∧ u 0 = x ∧ u (k - 1) = v (n - 1) ∧
      vpath u k ⊆ vpath v n := by
  have hr := h.reverse
  have hrp := vpath_reverse v n
  obtain ⟨x', ⟨-, hx'⟩, u, k, hu, hu0, hu1, husub, -⟩ := hr.exists_first_mem (K := {x})
    isClosed_singleton ⟨x, by rw [hrp]; exact hx, rfl⟩ (by simpa using hxe.symm)
  rw [mem_singleton_iff] at hx'
  subst hx'
  refine ⟨fun i => u (k - 1 - i), k, hu.reverse, by simpa using hu1, ?_, ?_⟩
  · simp only [Nat.sub_self]; rw [hu0]; simp
  · rw [vpath_reverse, ← hrp]; exact husub

/-! ### Closing two arcs into a simple closed polygon -/

/-- A criterion for a simple closed polygon in terms of a vertex function `W` with `W N = W 0`. -/
theorem isSimpleClosedPolygon_of_cyclic (W : ℕ → Pt) {N : ℕ} (hN : 3 ≤ N) (hW : W N = W 0)
    (hinj : ∀ i j, i < j → j < N → W i ≠ W j)
    (hcons : ∀ i, i + 1 < N → segment ℝ (W i) (W (i + 1)) ∩ segment ℝ (W (i + 1)) (W (i + 2)) ⊆
      {W i, W (i + 1)})
    (hwrap : segment ℝ (W (N - 1)) (W N) ∩ segment ℝ (W 0) (W 1) ⊆ {W (N - 1), W N})
    (hdis : ∀ i j, i + 1 < j → j < N → ¬ (i = 0 ∧ j = N - 1) →
      Disjoint (segment ℝ (W i) (W (i + 1))) (segment ℝ (W j) (W (j + 1)))) :
    IsSimpleClosedPolygon (vpath W (N + 1)) := by
  have hnext : ∀ i : Fin N, W ((i.val + 1) % N) = W (i.val + 1) := by
    intro i
    rcases succ_mod_cases i.isLt with ⟨h1, -⟩ | ⟨h1, h2⟩
    · rw [h1]
    · rw [h1, h2, hW]
  refine ⟨N, hN, fun i => W i.val, ?_, ?_, ?_⟩
  · ext x
    simp only [polygonOf, mem_iUnion, mem_vpath]
    constructor
    · rintro ⟨i, hi, hx⟩
      have h' : W ((i + 1) % N) = W (i + 1) := hnext ⟨i, by omega⟩
      exact ⟨⟨i, by omega⟩, by simp only; rw [h']; exact hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨i.val, by omega, by simpa [hnext] using hx⟩
  · intro i j hij
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact absurd hij (hinj _ _ h j.isLt)
    · exact Fin.ext h
    · exact absurd hij.symm (hinj _ _ h i.isLt)
  · intro i j hij
    simp only [hnext]
    -- consecutive pairs
    have hc : ∀ a b : Fin N, (a.val + 1) % N = b.val →
        segment ℝ (W a) (W (a.val + 1)) ∩ segment ℝ (W b) (W (b.val + 1)) ⊆ {W a, W b} := by
      intro a b hab
      rcases succ_mod_cases a.isLt with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hab
        rw [← hab]
        exact hcons a h2
      · rw [h1] at hab
        rw [← hab]
        have ha : a.val = N - 1 := by omega
        rw [ha, show N - 1 + 1 = N by omega, hW]
        intro z hz
        have := hwrap (by rw [hW]; exact hz)
        rwa [hW] at this
    refine ⟨fun hadj => ?_, fun hnadj => ?_⟩
    · rcases hadj with h | h
      · exact (hc i j h).trans (by
          intro z hz; rcases hz with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl))
      · rw [inter_comm]
        exact (hc j i h).trans (by
          intro z hz; rcases hz with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl)
    · push_neg at hnadj
      have hne := Fin.val_ne_of_ne hij
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have h1 : i.val + 1 < j.val := by
          rcases succ_mod_cases i.isLt with ⟨h1, -⟩ | ⟨h1, h2⟩ <;> omega
        refine hdis i j h1 j.isLt fun ⟨h2, h3⟩ => hnadj.2 ?_
        rw [h3, h2, Nat.sub_add_cancel (by omega), Nat.mod_self]
      · have h1 : j.val + 1 < i.val := by
          rcases succ_mod_cases j.isLt with ⟨h1, -⟩ | ⟨h1, h2⟩ <;> omega
        refine (hdis j i h1 i.isLt fun ⟨h2, h3⟩ => hnadj.1 ?_).symm
        rw [h3, h2, Nat.sub_add_cancel (by omega), Nat.mod_self]

/-- **Two simple arcs `a → c` and `c → a` meeting only at `a` and `c` form a simple closed
polygon.** -/
theorem isSimpleClosedPolygon_of_two_arcs {v u : ℕ → Pt} {n k : ℕ} (hv : IsSArc v n)
    (hu : IsSArc u k) (hvu : v (n - 1) = u 0) (huv : u (k - 1) = v 0)
    (hmeet : vpath v n ∩ vpath u k = {v 0, u 0}) :
    IsSimpleClosedPolygon (vpath v n ∪ vpath u k) := by
  have hv' := hv
  have hu' := hu
  obtain ⟨hn, hd, hc, hnc⟩ := hv
  obtain ⟨hk, hd', hc', hnc'⟩ := hu
  have hac : v 0 ≠ u 0 := hvu ▸ hd 0 (n - 1) (by omega) (by omega)
  set W := vcat v n u with hWdef
  have hvL : ∀ i, i < n → W i = v i := fun i hi => by simp [hWdef, vcat, hi]
  have hvR : ∀ i, n - 1 ≤ i → W i = u (i - (n - 1)) := by
    intro i hi
    by_cases h : i < n
    · have : i = n - 1 := by omega
      simp [hWdef, vcat, this, hvu]
    · simp [hWdef, vcat, h]
  have hmem : ∀ {z}, z ∈ vpath v n → z ∈ vpath u k → z = v 0 ∨ z = u 0 := by
    intro z h1 h2
    have : z ∈ vpath v n ∩ vpath u k := ⟨h1, h2⟩
    rw [hmeet] at this
    exact this
  have hN : 3 ≤ n + k - 2 := by
    by_contra hlt
    have hn2 : n = 2 := by omega
    have hk2 : k = 2 := by omega
    subst hn2; subst hk2
    have h1 : midpoint ℝ (v 0) (u 0) ∈ vpath v 2 := by
      refine segment_subset_vpath (i := 0) (by omega) ?_
      rw [show (0 : ℕ) + 1 = 2 - 1 by rfl, hvu]; exact midpoint_mem_segment _ _
    have h2 : midpoint ℝ (v 0) (u 0) ∈ vpath u 2 := by
      refine segment_subset_vpath (i := 0) (by omega) ?_
      rw [show (0 : ℕ) + 1 = 2 - 1 by rfl, huv, segment_symm]; exact midpoint_mem_segment _ _
    rcases hmem h1 h2 with h | h
    · exact hac ((midpoint_eq_left_iff ℝ).1 h)
    · exact hac ((midpoint_eq_right_iff ℝ).1 h)
  have heq : vpath v n ∪ vpath u k = vpath W (n + k - 2 + 1) := by
    rw [show n + k - 2 + 1 = n + k - 1 by omega, hWdef, vpath_vcat (by omega) (by omega) hvu]
  rw [heq]
  have hsegL : ∀ i, i + 1 < n → segment ℝ (W i) (W (i + 1)) = segment ℝ (v i) (v (i + 1)) :=
    fun i hi => vcat_seg_left hi
  have hsegR : ∀ i, n - 1 ≤ i → segment ℝ (W i) (W (i + 1)) =
      segment ℝ (u (i - (n - 1))) (u (i - (n - 1) + 1)) :=
    fun i hi => vcat_seg_right (by omega) hvu hi
  refine isSimpleClosedPolygon_of_cyclic W hN ?_ ?_ ?_ ?_ ?_
  · rw [hvR _ (by omega), show n + k - 2 - (n - 1) = k - 1 by omega, huv, hvL 0 (by omega)]
  · intro i j hij hj
    by_cases hjn : j < n
    · rw [hvL i (by omega), hvL j hjn]; exact hd i j hij hjn
    by_cases hin : n - 1 ≤ i
    · rw [hvR i hin, hvR j (by omega)]; exact hd' _ _ (by omega) (by omega)
    · rw [hvL i (by omega), hvR j (by omega)]
      intro heq'
      rcases hmem (vertex_mem_vpath hn (by omega : i < n))
        (heq' ▸ vertex_mem_vpath hk (by omega)) with h | h
      · rw [h, ← huv] at heq'
        exact hd' _ _ (by omega) (by omega) heq'.symm
      · rw [h] at heq'
        exact hd' 0 _ (by omega) (by omega) heq'
  · intro i hi
    by_cases h1 : i + 2 < n
    · rw [hsegL i (by omega), show i + 2 = i + 1 + 1 by omega, hsegL (i + 1) (by omega),
        hvL i (by omega), hvL (i + 1) (by omega)]
      exact (hc i h1).trans (singleton_subset_iff.2 (Or.inr rfl))
    by_cases h2 : n - 1 ≤ i
    · rw [hsegR i h2, show i + 2 = i + 1 + 1 by omega, hsegR (i + 1) (by omega),
        hvR (i + 1) (by omega), show i + 1 - (n - 1) = i - (n - 1) + 1 by omega]
      exact (hc' _ (by omega)).trans (singleton_subset_iff.2 (Or.inr rfl))
    · have hi' : i = n - 2 := by omega
      rw [show i + 2 = i + 1 + 1 by omega, hsegL i (by omega), hsegR (i + 1) (by omega)]
      rintro z ⟨hz1, hz2⟩
      rcases hmem (segment_subset_vpath (by omega) hz1) (segment_subset_vpath (by omega) hz2)
        with h | h
      · have := hv'.start_mem_seg (i := i) (by omega) (h ▸ hz1)
        left; rw [h, hvL i (by omega), this]
      · right
        rw [h, hvR (i + 1) (by omega), show i + 1 - (n - 1) = 0 by omega]
        rfl
  · have hlast : segment ℝ (W (n + k - 2 - 1)) (W (n + k - 2)) =
        segment ℝ (u (k - 2)) (u (k - 2 + 1)) := by
      have := hsegR (n + k - 2 - 1) (by omega)
      rwa [show n + k - 2 - 1 + 1 = n + k - 2 by omega,
        show n + k - 2 - 1 - (n - 1) = k - 2 by omega] at this
    rw [hlast, hsegL 0 (by omega)]
    rintro z ⟨hz1, hz2⟩
    rcases hmem (segment_subset_vpath (by omega) hz2) (segment_subset_vpath (by omega) hz1)
      with h | h
    · right
      rw [h, hvR _ (by omega), show n + k - 2 - (n - 1) = k - 1 by omega, huv]
      rfl
    · have := hu'.start_mem_seg (i := k - 2) (by omega) (h ▸ hz1)
      left
      rw [h, hvR _ (by omega), show n + k - 2 - 1 - (n - 1) = k - 2 by omega, this]
  · intro i j hij hj hnot
    by_cases h1 : j + 1 < n
    · rw [hsegL i (by omega), hsegL j h1]; exact hnc i j hij h1
    by_cases h2 : n - 1 ≤ i
    · rw [hsegR i h2, hsegR j (by omega)]
      exact hnc' _ _ (by omega) (by omega)
    · rw [hsegL i (by omega), hsegR j (by omega), Set.disjoint_left]
      intro z hz1 hz2
      rcases hmem (segment_subset_vpath (by omega) hz1) (segment_subset_vpath (by omega) hz2)
        with h | h
      · have e1 := hv'.start_mem_seg (i := i) (by omega) (h ▸ hz1)
        have e2 := hu'.end_mem_seg (i := j - (n - 1)) (by omega) (by rw [huv, ← h]; exact hz2)
        exact hnot ⟨e1, by omega⟩
      · have e1 := hv'.end_mem_seg (i := i) (by omega) (by rw [hvu, ← h]; exact hz1)
        have e2 := hu'.start_mem_seg (i := j - (n - 1)) (by omega) (h ▸ hz2)
        omega

/-! ### A simple closed polygon threaded through three connected open sets -/

theorem IsSArc.start_mem {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) : v 0 ∈ vpath v n :=
  vertex_mem_vpath h.1 (by have := h.1; omega)

theorem IsSArc.end_mem {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) : v (n - 1) ∈ vpath v n :=
  vertex_mem_vpath h.1 (by have := h.1; omega)

/-- A simple polygonal arc between two distinct points of a connected open set, inside it. -/
theorem exists_sarc_in {h : Set Pt} (ho : IsOpen h) (hc : IsConnected h) {p q : Pt}
    (hp : p ∈ h) (hq : q ∈ h) (hpq : p ≠ q) :
    ∃ (v : ℕ → Pt) (n : ℕ), IsSArc v n ∧ v 0 = p ∧ v (n - 1) = q ∧ vpath v n ⊆ h := by
  obtain ⟨v, n, hn, h0, h1, hsub⟩ := exists_vpath_of_isConnected ho hc hp hq
  obtain ⟨u, k, hu, hu0, hu1, husub⟩ := exists_sarc_of_vpath hn h0 h1 hpq
  exact ⟨u, k, hu, hu0, hu1, husub.trans hsub⟩

/-- **Threading through three sets.** Three connected open sets, pairwise meeting, with no point
common to all three, contain three simple polygonal arcs `α₀ ⊆ A₀`, `α₁ ⊆ A₁`, `α₂ ⊆ A₂`, joined
end to end at `p₁ ∈ α₀ ∩ α₁`, `p₂ ∈ α₁ ∩ α₂`, `p₀ ∈ α₂ ∩ α₀`, whose union is a simple closed
polygon. (Polygonal arcs `p₀ → p₁ → p₂ → p₀`, then three trims at first points.) -/
theorem theta_polygon_of_three {A₀ A₁ A₂ : Set Pt} (ho₀ : IsOpen A₀) (ho₁ : IsOpen A₁)
    (ho₂ : IsOpen A₂) (hc₀ : IsConnected A₀) (hc₁ : IsConnected A₁) (hc₂ : IsConnected A₂)
    (h₀₁ : (A₀ ∩ A₁).Nonempty) (h₁₂ : (A₁ ∩ A₂).Nonempty) (h₂₀ : (A₂ ∩ A₀).Nonempty)
    (ht : A₀ ∩ A₁ ∩ A₂ = ∅) :
    ∃ (Γ α₀ α₁ α₂ : Set Pt) (p₀ p₁ p₂ : Pt), IsSimpleClosedPolygon Γ ∧ α₀ ∪ α₁ ∪ α₂ = Γ ∧
      IsConnected α₀ ∧ IsConnected α₁ ∧ IsConnected α₂ ∧
      p₁ ∈ α₀ ∩ α₁ ∧ p₂ ∈ α₁ ∩ α₂ ∧ p₀ ∈ α₂ ∩ α₀ ∧ α₀ ⊆ A₀ ∧ α₁ ⊆ A₁ ∧ α₂ ⊆ A₂ := by
  have hnt : ∀ {z : Pt}, z ∈ A₀ → z ∈ A₁ → z ∈ A₂ → False := fun {z} h0 h1 h2 => by
    have hz : z ∈ A₀ ∩ A₁ ∩ A₂ := ⟨⟨h0, h1⟩, h2⟩
    rw [ht] at hz; exact hz
  obtain ⟨p₁, hp₁0, hp₁1⟩ := h₀₁
  obtain ⟨p₂, hp₂1, hp₂2⟩ := h₁₂
  obtain ⟨p₀, hp₀2, hp₀0⟩ := h₂₀
  obtain ⟨g0, n0, hg0, hg00, hg01, hg0A⟩ := exists_sarc_in ho₀ hc₀ hp₀0 hp₁0
    (fun h => hnt hp₀0 (by rw [h]; exact hp₁1) hp₀2)
  obtain ⟨g1, n1, hg1, hg10, hg11, hg1A⟩ := exists_sarc_in ho₁ hc₁ hp₁1 hp₂1
    (fun h => hnt hp₁0 hp₁1 (by rw [h]; exact hp₂2))
  obtain ⟨g2, n2, hg2, hg20, hg21, hg2A⟩ := exists_sarc_in ho₂ hc₂ hp₂2 hp₀2
    (fun h => hnt (by rw [h]; exact hp₀0) hp₂1 hp₂2)
  -- step 1: cut `g0` at its first point on `g1`
  obtain ⟨x₁, ⟨hx₁0, hx₁1⟩, u0, k0, hu0, hu00, hu01, hu0sub, hu0K⟩ :=
    hg0.exists_first_mem (K := vpath g1 n1) (isCompact_vpath _ _).isClosed
      ⟨p₁, hg01 ▸ hg0.end_mem, hg10 ▸ hg1.start_mem⟩
      (by rw [hg00]; exact fun h => hnt hp₀0 (hg1A h) hp₀2)
  have hx₁A0 : x₁ ∈ A₀ := hg0A hx₁0
  have hx₁A1 : x₁ ∈ A₁ := hg1A hx₁1
  obtain ⟨w1, m1, hw1, hw10, hw11, hw1sub⟩ := hg1.exists_suffix hx₁1
    (by rw [hg11]; exact fun h => hnt hx₁A0 hx₁A1 (h ▸ hp₂2))
  -- step 2: cut the rest of `g1` at its first point on `g2`
  obtain ⟨x₂, ⟨hx₂1, hx₂2⟩, u1, k1, hu1, hu10, hu11, hu1sub, hu1K⟩ :=
    hw1.exists_first_mem (K := vpath g2 n2) (isCompact_vpath _ _).isClosed
      ⟨p₂, by rw [← hg11, ← hw11]; exact hw1.end_mem, hg20 ▸ hg2.start_mem⟩
      (by rw [hw10]; exact fun h => hnt hx₁A0 hx₁A1 (hg2A h))
  have hx₂A1 : x₂ ∈ A₁ := hg1A (hw1sub hx₂1)
  have hx₂A2 : x₂ ∈ A₂ := hg2A hx₂2
  obtain ⟨w2, m2, hw2, hw20, hw21, hw2sub⟩ := hg2.exists_suffix hx₂2
    (by rw [hg21]; exact fun h => hnt (h ▸ hp₀0) hx₂A1 hx₂A2)
  -- step 3: cut the rest of `g2` at its first point on the first piece of `g0`
  obtain ⟨x₀, ⟨hx₀2, hx₀0⟩, u2, k2, hu2, hu20, hu21, hu2sub, hu2K⟩ :=
    hw2.exists_first_mem (K := vpath u0 k0) (isCompact_vpath _ _).isClosed
      ⟨p₀, by rw [← hg21, ← hw21]; exact hw2.end_mem, hg00 ▸ hu00 ▸ hu0.start_mem⟩
      (by rw [hw20]; exact fun h => hnt (hg0A (hu0sub h)) hx₂A1 hx₂A2)
  have hx₀A2 : x₀ ∈ A₂ := hg2A (hw2sub hx₀2)
  obtain ⟨v0, l0, hv0, hv00, hv01, hv0sub⟩ := hu0.exists_suffix hx₀0
    (by rw [hu01]; exact fun h => hnt hx₁A0 hx₁A1 (h ▸ hx₀A2))
  -- the three arcs
  have hm01 : vpath v0 l0 ∩ vpath u1 k1 = {u1 0} := by
    apply subset_antisymm
    · rw [hu10, hw10, ← hu0K]
      exact inter_subset_inter hv0sub (hu1sub.trans hw1sub)
    · rintro z rfl
      exact ⟨by rw [hu10, hw10, ← hu01, ← hv01]; exact hv0.end_mem, hu1.start_mem⟩
  have hm12 : vpath u1 k1 ∩ vpath u2 k2 = {x₂} := by
    apply subset_antisymm
    · rw [← hu1K]
      exact inter_subset_inter subset_rfl (hu2sub.trans hw2sub)
    · rintro z rfl
      exact ⟨by rw [← hu11]; exact hu1.end_mem, by rw [← hw20, ← hu20]; exact hu2.start_mem⟩
  have hm20 : vpath u2 k2 ∩ vpath v0 l0 = {x₀} := by
    apply subset_antisymm
    · rw [← hu2K]
      exact inter_subset_inter subset_rfl hv0sub
    · rintro z rfl
      exact ⟨by rw [← hu21]; exact hu2.end_mem, by rw [← hv00]; exact hv0.start_mem⟩
  have hβ := hv0.concat hu1 (by rw [hv01, hu01, hu10, hw10]) hm01
  have hl0 := hv0.1
  have hk1 := hu1.1
  have hβp : vpath (vcat v0 l0 u1) (l0 + k1 - 1) = vpath v0 l0 ∪ vpath u1 k1 :=
    vpath_vcat (by omega) (by omega) (by rw [hv01, hu01, hu10, hw10])
  have hβ0 : vcat v0 l0 u1 0 = x₀ := by simp [vcat, show 0 < l0 by omega, hv00]
  have hβ1 : vcat v0 l0 u1 (l0 + k1 - 1 - 1) = x₂ := by
    simp only [vcat, show ¬ (l0 + k1 - 1 - 1 < l0) by omega, if_false]
    rw [show l0 + k1 - 1 - 1 - (l0 - 1) = k1 - 1 by omega, hu11]
  have hΓ := isSimpleClosedPolygon_of_two_arcs hβ hu2 (by rw [hβ1, hu20, hw20])
    (by rw [hu21, hβ0]) (by
      rw [hβp, union_inter_distrib_right, inter_comm (vpath v0 l0), hm20, hm12, hβ0, hu20, hw20]
      exact Set.singleton_union)
  rw [hβp] at hΓ
  refine ⟨_, vpath v0 l0, vpath u1 k1, vpath u2 k2, x₀, x₁, x₂, hΓ, rfl,
    isConnected_vpath _ hv0.1, isConnected_vpath _ hu1.1, isConnected_vpath _ hu2.1,
    ⟨by rw [← hu01, ← hv01]; exact hv0.end_mem, by rw [← hw10, ← hu10]; exact hu1.start_mem⟩,
    ⟨by rw [← hu11]; exact hu1.end_mem, by rw [← hw20, ← hu20]; exact hu2.start_mem⟩,
    ⟨by rw [← hu21]; exact hu2.end_mem, by rw [← hv00]; exact hv0.start_mem⟩,
    hv0sub.trans (hu0sub.trans hg0A), hu1sub.trans (hw1sub.trans hg1A),
    hu2sub.trans (hw2sub.trans hg2A)⟩

end HPC.Plane
