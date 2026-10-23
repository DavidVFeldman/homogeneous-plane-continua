import HPC.Plane.Jct1

/-!
# Batch 126: the Jordan curve theorem for simple closed polygons, part II — the two sides are
# connected; `jct` discharged

COMMISSION-batch126.md. The skeleton of the commission (`doc/batches/skeletons/Jct2.lean`) with
every `sorry` replaced by a proof. Nothing in this file is `sorry`. All statements of the skeleton
are kept verbatim; the changes (recorded in REPORT-batch126) are:

* **`sideNbhd` (the `def` to be designed)** is the union of *all* preconnected local pieces:
  `sideNbhd v e = ⋃ (w ∈ Γ) (r > 0) (_ : IsPreconnected (S_e ∩ ball w r)), S_e ∩ ball w r`, where
  `S_e = {x ∉ Γ | parity v x = e}`. No finite cover and no cutting of the edges is needed: the
  pieces at one point `w` pairwise meet (both parities accumulate at `w`), and the pieces at nearby
  points meet, so `isPreconnected_biUnion_of_local_meet` (batch 118) over the connected set `Γ`
  gives `sideNbhd_isConnected`. By `isConnected_parity_set`, `sideNbhd v e` is in fact all of `S_e`.
* **The key lemma of the main line is `mem_closure_parity_set`**: every point of `Γ` is in the
  closure of both parity classes. It is proved from the two flips at *generic* points of an edge
  (`parity_flip_at`: a non-horizontal edge at a height which is no vertex height, the horizontal
  displacement of `exists_parity_flip`; `parity_flip_vertical`: a horizontal edge at any non-vertex
  point, the vertical displacement with the vertex-jump calculus — summed over all edges the jumps
  cancel, and the edge itself contributes the extra `1`), the generic points being dense in every
  edge (`exists_near_on_segment`). With it, `local_side_of_split` (batch 118) gives the connected
  local pieces at every point of `Γ` (`local_piece`); vertices need no separate treatment.
* `vertex_two_pieces` is proved from `polygon_local_rays`, `ball_diff_rays` and
  `mem_closure_parity_set` (so it holds at every point of `Γ`, not only at vertices);
  `parity_flip_edge` is proved (from `parity_flip_at` / `parity_flip_vertical` and the convexity of
  the half-disks) but the main line does not need it, nor `polygon_local_chord`, `halfDisk_*`,
  `ball_diff_chord`.
* Auxiliary statements added: `parity_flip_at`, `parity_flip_vertical`, `mem_closure_parity_set`,
  `local_piece`, `isPreconnected_polygonOf`, `segment_subset_of_first_hit`, and elementary helpers.
-/

namespace HPC.Plane

open Set Metric Filter Topology

/-! ### Auxiliary facts -/

theorem zmod2_cases : ∀ z e : ZMod 2, z = e ∨ z = e + 1 := by decide

theorem zmod2_ne_add_one : ∀ e : ZMod 2, e ≠ e + 1 := by decide

theorem zmod2_eq_of_ne' : ∀ z w e : ZMod 2, z ≠ w → z = e ∨ w = e := by decide

theorem zmod2_eq_of_ne {z w : ZMod 2} (h : z ≠ w) (e : ZMod 2) : z = e ∨ w = e :=
  zmod2_eq_of_ne' z w e h

theorem next_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ : Fin n) ≠ i := by
  intro h
  have := congrArg Fin.val h
  simp only at this
  rcases succ_mod_cases i.isLt with ⟨h1, -⟩ | ⟨h1, h2⟩ <;> omega

theorem edge_ends_ne {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) :
    v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i ≠ 0 := by
  intro h
  exact next_ne_self (by have := hv.1; omega) i (hv.2.1 (sub_eq_zero.1 h))

theorem dist_shift_snd (p : Pt) (s : ℝ) : dist ((p.1, p.2 + s) : Pt) p = |s| := by
  rw [Prod.dist_eq]; simp

theorem dist_shift_snd_sub (p : Pt) (s : ℝ) : dist ((p.1, p.2 - s) : Pt) p = |s| := by
  rw [Prod.dist_eq]; simp

theorem dist_shift_fst (p : Pt) (s : ℝ) : dist ((p.1 + s, p.2) : Pt) p = |s| := by
  rw [Prod.dist_eq]; simp

theorem dist_shift_fst_sub (p : Pt) (s : ℝ) : dist ((p.1 - s, p.2) : Pt) p = |s| := by
  rw [Prod.dist_eq]; simp

/-- An affine function with nonzero slope avoids a finite set at parameters arbitrarily close to
any `s₀ ∈ [0, 1]`, inside `(0, 1)`. -/
theorem exists_param_avoid (F : Finset ℝ) (α β : ℝ) (hβ : β ≠ 0) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s ∈ Ioo (0 : ℝ) 1, |s - s₀| < δ ∧ α + β * s ∉ F := by
  obtain ⟨h0, h1⟩ := hs₀
  have hlt : max 0 (s₀ - δ) < min 1 (s₀ + δ) := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by norm_num, by linarith⟩, by linarith, by linarith⟩
  obtain ⟨s, hsI, hsF⟩ := (Set.Ioo_infinite hlt).exists_notMem_finset
    (F.image fun y => (y - α) / β)
  obtain ⟨h2, h3⟩ := hsI
  rw [max_lt_iff] at h2
  rw [lt_min_iff] at h3
  refine ⟨s, ⟨h2.1, h3.1⟩, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩, fun h =>
    hsF (Finset.mem_image.2 ⟨_, h, by field_simp; ring⟩)⟩

/-- Near any point `q` of a segment `[a, b]` there is a point `p` of the segment at which the
linear form `c₁ x + c₂ y` (nonconstant along the segment) avoids a given finite set. -/
theorem exists_near_on_segment {a b q : Pt} (hq : q ∈ segment ℝ a b) (F : Finset ℝ)
    (c₁ c₂ : ℝ) (hc : c₁ * (b - a).1 + c₂ * (b - a).2 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ segment ℝ a b, dist p q < ε ∧ c₁ * p.1 + c₂ * p.2 ∉ F := by
  rw [segment_eq_image'] at hq ⊢
  obtain ⟨s₀, hs₀, rfl⟩ := hq
  have hδ : 0 < ε / (‖b - a‖ + 1) := div_pos hε (by positivity)
  obtain ⟨s, hs, hss, hsF⟩ := exists_param_avoid F (c₁ * a.1 + c₂ * a.2)
    (c₁ * (b - a).1 + c₂ * (b - a).2) hc hs₀ hδ
  refine ⟨a + s • (b - a), ⟨s, Ioo_subset_Icc_self hs, rfl⟩, ?_, ?_⟩
  · rw [dist_eq_norm, show a + s • (b - a) - (a + s₀ • (b - a)) = (s - s₀) • (b - a) by
      rw [sub_smul]; abel, norm_smul, Real.norm_eq_abs]
    calc |s - s₀| * ‖b - a‖ ≤ |s - s₀| * (‖b - a‖ + 1) := by
          have := abs_nonneg (s - s₀); nlinarith
      _ < ε / (‖b - a‖ + 1) * (‖b - a‖ + 1) := by
          apply mul_lt_mul_of_pos_right hss (by positivity)
      _ = ε := by field_simp
  · intro h
    apply hsF
    convert h using 1
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- From `x`, the points `x + t • (p - x)` with `t < 1` come arbitrarily close to `p`. -/
theorem exists_param_near_end (x p : Pt) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ dist (x + t • (p - x)) p < r := by
  set δ := min (1 / 2 : ℝ) (r / (2 * (‖p - x‖ + 1)))
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ r / (2 * (‖p - x‖ + 1)) := min_le_right _ _
  refine ⟨1 - δ, by linarith, by linarith, ?_⟩
  rw [dist_eq_norm, show x + (1 - δ) • (p - x) - p = (-δ) • (p - x) by
    rw [sub_smul, one_smul, neg_smul]; abel, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos hδ0]
  have hn := norm_nonneg (p - x)
  calc δ * ‖p - x‖ ≤ r / (2 * (‖p - x‖ + 1)) * ‖p - x‖ :=
        mul_le_mul_of_nonneg_right hδ2 hn
    _ < r := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

theorem polygonOf_nonempty {n : ℕ} (v : Fin n → Pt) (hn : 0 < n) : (polygonOf v).Nonempty :=
  ⟨v ⟨0, hn⟩, mem_iUnion.2 ⟨⟨0, hn⟩, left_mem_segment _ _ _⟩⟩

/-- A closed polygon is preconnected: consecutive edges share a vertex. -/
theorem isPreconnected_polygonOf {n : ℕ} (v : Fin n → Pt) : IsPreconnected (polygonOf v) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : polygonOf v = ∅ := by
      ext x; simp only [polygonOf, mem_iUnion, mem_empty_iff_false, iff_false]
      rintro ⟨i, -⟩; exact i.elim0
    rw [this]; exact isPreconnected_empty
  set s : ℕ → Set Pt := fun k => polyEdge v ⟨k % n, Nat.mod_lt _ hn⟩ with hs
  have hU : polygonOf v = ⋃ k, s k := by
    ext x
    simp only [polygonOf, mem_iUnion, hs]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i.val, ?_⟩
      have : (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [this]; exact hi
    · rintro ⟨k, hk⟩; exact ⟨_, hk⟩
  rw [hU]
  refine IsPreconnected.iUnion_of_chain (fun k => (convex_segment _ _).isPreconnected)
    fun k => ⟨v ⟨(k + 1) % n, Nat.mod_lt _ hn⟩, ?_, ?_⟩
  · simp only [hs, polyEdge]
    have : (⟨(k % n + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨(k + 1) % n, Nat.mod_lt _ hn⟩ :=
      Fin.ext (Nat.mod_add_mod k n 1)
    rw [this]; exact right_mem_segment _ _ _
  · simp only [hs, polyEdge, Order.succ_eq_add_one]
    exact left_mem_segment _ _ _

/-! ### The flips -/

/-- **The flip at a point of generic height of a non-horizontal edge** (`exists_parity_flip` at a
given point): if `p` lies on the non-horizontal edge `i` and no vertex has the height of `p`, the
points `p ∓ t • (1, 0)` for small `t > 0` are off `Γ` and have different parities. -/
theorem parity_flip_at {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n)
    (hne : (v i).2 ≠ (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).2) {p : Pt}
    (hp : p ∈ polyEdge v i) (hcv : ∀ k, (v k).2 ≠ p.2) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      (p.1 - t, p.2) ∉ polygonOf v ∧ (p.1 + t, p.2) ∉ polygonOf v ∧
      parity v (p.1 - t, p.2) ≠ parity v (p.1 + t, p.2) := by
  classical
  set a := v i with ha
  set b := v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ with hb
  have hpv : ∀ k, p ≠ v k := fun k h => hcv k (by rw [← h])
  have hoff : ∀ j, j ≠ i → p ∉ polyEdge v j := fun j hj => not_mem_polyEdge_of_ne hv hj hp hpv
  have hpX : p.1 = a.1 + (p.2 - a.2) * (b.1 - a.1) / (b.2 - a.2) := fst_eq_of_mem_segment hp hne
  have hstr' : (a.2 ≤ p.2 ∧ p.2 < b.2) ∨ (b.2 ≤ p.2 ∧ p.2 < a.2) := by
    obtain ⟨s, t, hs, ht, hst, hpe⟩ := hp
    obtain rfl : s = 1 - t := by linarith
    have h2 : p.2 - a.2 = t * (b.2 - a.2) := by rw [← hpe]; simp [ha, hb]; ring
    have h2' : b.2 - p.2 = (1 - t) * (b.2 - a.2) := by rw [← hpe]; simp [ha, hb]; ring
    have hca : a.2 ≠ p.2 := hcv i
    have hcb : b.2 ≠ p.2 := hcv _
    rcases lt_or_gt_of_ne hne with h | h
    · have h3 : a.2 ≤ p.2 := by have := mul_nonneg ht (sub_pos.2 h).le; linarith
      have h4 : p.2 ≤ b.2 := by have := mul_nonneg hs (sub_pos.2 h).le; linarith
      exact Or.inl ⟨h3, lt_of_le_of_ne h4 hcb.symm⟩
    · have h3 : b.2 ≤ p.2 := by have := mul_nonneg ht (sub_pos.2 h).le; nlinarith
      have h4 : p.2 ≤ a.2 := by have := mul_nonneg hs (sub_pos.2 h).le; nlinarith
      exact Or.inr ⟨h3, lt_of_le_of_ne h4 hca.symm⟩
  have hE : ∀ᶠ y in 𝓝 p, ∀ j : Fin n, j ≠ i → y ∉ polyEdge v j ∧
      ceInd y (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
        ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · have h1 : ∀ᶠ y in 𝓝 p, y ∉ polyEdge v j :=
        (isCompact_segment' _ _).isClosed.isOpen_compl.mem_nhds (hoff j hj)
      have h2 := ceInd_eventually_eq (hoff j hj) (Ne.symm (hcv j)) (Ne.symm (hcv _))
      filter_upwards [h1, h2] with y hy1 hy2 _ using ⟨hy1, hy2⟩
  obtain ⟨ε, hε, hεE⟩ := Metric.eventually_nhds_iff.1 hE
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  have hdist : ∀ s : ℝ, |s| < ε → dist ((p.1 + s, p.2) : Pt) p < ε := fun s hs => by
    rw [Prod.dist_eq]; simp [hs]
  have hm := hεE (hdist (-t) (by rw [abs_neg, abs_of_pos ht]; exact htε))
  have hpl := hεE (hdist t (by rw [abs_of_pos ht]; exact htε))
  simp only [← sub_eq_add_neg] at hm
  have hoffi : ∀ s : ℝ, s ≠ 0 → ((p.1 + s, p.2) : Pt) ∉ polyEdge v i := fun s hs h => by
    have := fst_eq_of_mem_segment h hne
    simp only at this
    exact hs (by linarith)
  have hnot : ∀ s : ℝ, s ≠ 0 → (∀ j : Fin n, j ≠ i → ((p.1 + s, p.2) : Pt) ∉ polyEdge v j) →
      ((p.1 + s, p.2) : Pt) ∉ polygonOf v := fun s hs hj h => by
    obtain ⟨j, hj'⟩ := Set.mem_iUnion.1 h
    by_cases hji : j = i
    · subst hji; exact hoffi s hs hj'
    · exact hj j hji hj'
  have hcrossm : ceInd (p.1 - t, p.2) a b = 1 := by
    simp only [ceInd, CrossesEast]; rw [if_pos]
    exact ⟨hstr', by linarith⟩
  have hcrossp : ceInd (p.1 + t, p.2) a b = 0 := by
    simp only [ceInd, CrossesEast]; rw [if_neg]
    rintro ⟨_, h⟩; linarith
  refine ⟨?_, hnot t ht.ne' fun j hj => (hpl j hj).1, ?_⟩
  · have := hnot (-t) (neg_ne_zero.2 ht.ne') fun j hj => by
      have := (hm j hj).1; rwa [sub_eq_add_neg] at this
    rwa [← sub_eq_add_neg] at this
  · rw [parity_eq_sum, parity_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : ∀ q : Pt, (∀ j : Fin n, j ≠ i → q ∉ polyEdge v j ∧
        ceInd q (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
          ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)) →
        ∑ j ∈ Finset.univ.erase i,
          ceInd q (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
        ∑ j ∈ Finset.univ.erase i,
          ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) := fun q hq =>
      Finset.sum_congr rfl fun j hj => (hq j (Finset.ne_of_mem_erase hj)).2
    rw [hrest _ hm, hrest _ hpl]
    change ceInd (p.1 - t, p.2) a b + _ ≠ ceInd (p.1 + t, p.2) a b + _
    rw [hcrossm, hcrossp, zero_add]
    intro h
    have := congrArg (· - ∑ j ∈ Finset.univ.erase i,
      ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)) h
    simp only [add_sub_cancel_right, sub_self] at this
    exact one_ne_zero this

/-- **The flip across a horizontal edge**: at a non-vertex point `p` of a horizontal edge, the
points `p ± t • (0, 1)` for small `t > 0` are off `Γ` and have different parities. (Vertex-jump
calculus: summed over all edges the jumps cancel, and the edge itself contributes the extra `1`,
having exactly one end to the right of `p` at the height of `p`.) -/
theorem parity_flip_vertical {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n)
    (hhor : (v i).2 = (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).2) {p : Pt}
    (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      (p.1, p.2 + t) ∉ polygonOf v ∧ (p.1, p.2 - t) ∉ polygonOf v ∧
      parity v (p.1, p.2 + t) ≠ parity v (p.1, p.2 - t) := by
  classical
  set a := v i with ha
  set b := v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ with hb
  have hoff : ∀ j, j ≠ i → p ∉ polyEdge v j := fun j hj => not_mem_polyEdge_of_ne hv hj hp hpv
  have hedge2 : ∀ z ∈ polyEdge v i, z.2 = a.2 := by
    rintro z ⟨s, t, hs, ht, hst, rfl⟩
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [← hhor]; linear_combination a.2 * hst
  have hpa : p.2 = a.2 := hedge2 p hp
  have hA : a.2 = p.2 := hpa.symm
  have hB : b.2 = p.2 := hhor.symm.trans hpa.symm
  have hbetw : (a.1 < p.1 ∧ p.1 < b.1) ∨ (b.1 < p.1 ∧ p.1 < a.1) := by
    obtain ⟨s, t, hs, ht, hst, hpe⟩ := hp
    obtain rfl : s = 1 - t := by linarith
    have h1 : p.1 - a.1 = t * (b.1 - a.1) := by rw [← hpe]; simp [ha, hb]; ring
    have h1' : b.1 - p.1 = (1 - t) * (b.1 - a.1) := by rw [← hpe]; simp [ha, hb]; ring
    have hpa1 : p.1 ≠ a.1 := fun h => hpv i (Prod.ext h hpa)
    have hpb1 : p.1 ≠ b.1 := fun h => hpv _ (Prod.ext h (hpa.trans hhor))
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · left; constructor
      · have := mul_nonneg ht (sub_pos.2 h).le
        exact lt_of_le_of_ne (by linarith) (Ne.symm hpa1)
      · have := mul_nonneg hs (sub_pos.2 h).le
        exact lt_of_le_of_ne (by linarith) hpb1
    · exfalso; apply hpa1; rw [h, sub_self, mul_zero] at h1; linarith
    · right; constructor
      · have := mul_nonneg ht (sub_pos.2 h).le
        exact lt_of_le_of_ne (by nlinarith) (Ne.symm hpb1)
      · have := mul_nonneg hs (sub_pos.2 h).le
        exact lt_of_le_of_ne (by nlinarith) hpa1
  have hJi : vJump p a + vJump p b = 1 := by
    rcases hbetw with h | h
    · simp [vJump, hA, hB, h.2, not_lt.2 h.1.le]
    · simp [vJump, hA, hB, h.2, not_lt.2 h.1.le]
  have hno : ∀ z : Pt, ceInd z a b = 0 := by
    intro z
    unfold ceInd; rw [if_neg]
    rintro ⟨h | h, -⟩ <;> linarith [h.1, h.2]
  have hE : ∀ᶠ y in 𝓝 p, ∀ j : Fin n, j ≠ i → y ∉ polyEdge v j ∧
      (p.2 ≤ y.2 → ceInd y (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
        ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)) ∧
      (y.2 < p.2 → ceInd y (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) +
        ceInd p (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
        vJump p (v j) + vJump p (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · have h1 : ∀ᶠ y in 𝓝 p, y ∉ polyEdge v j :=
        (isCompact_segment' _ _).isClosed.isOpen_compl.mem_nhds (hoff j hj)
      filter_upwards [h1, crossesEast_jump (hoff j hj)] with y hy1 hy2 _ using
        ⟨hy1, fun h => ceInd_congr (hy2.1 h), hy2.2⟩
  obtain ⟨ε, hε, hεE⟩ := Metric.eventually_nhds_iff.1 hE
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  have hdist : ∀ s : ℝ, |s| < ε → dist ((p.1, p.2 + s) : Pt) p < ε := fun s hs => by
    rw [dist_shift_snd]; exact hs
  have hm := hεE (hdist (-t) (by rw [abs_neg, abs_of_pos ht]; exact htε))
  have hpl := hεE (hdist t (by rw [abs_of_pos ht]; exact htε))
  simp only [← sub_eq_add_neg] at hm
  have hnot : ∀ z : Pt, z.2 ≠ p.2 → (∀ j : Fin n, j ≠ i → z ∉ polyEdge v j) →
      z ∉ polygonOf v := fun z hz hj h => by
    obtain ⟨j, hj'⟩ := Set.mem_iUnion.1 h
    by_cases hji : j = i
    · subst hji; exact hz ((hedge2 z hj').trans hA)
    · exact hj j hji hj'
  refine ⟨hnot _ (by simp only; linarith) fun j hj => (hpl j hj).1,
    hnot _ (by simp only; linarith) fun j hj => (hm j hj).1, ?_⟩
  have hsum : parity v (p.1, p.2 + t) + parity v (p.1, p.2 - t) = 1 := by
    rw [parity_eq_sum, parity_eq_sum, ← Finset.sum_add_distrib]
    calc _ = ∑ j : Fin n, ((vJump p (v j) +
            vJump p (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)) +
            if j = i then 1 else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j = i
          · subst hj
            change ceInd _ a b + ceInd _ a b = (vJump p a + vJump p b) + if j = j then 1 else 0
            rw [hno, hno, hJi, if_pos rfl]; decide
          · rw [if_neg hj, add_zero, (hpl j hj).2.1 (by simp only; linarith), add_comm]
            exact (hm j hj).2.2 (by linarith)
      _ = 1 := by
          rw [Finset.sum_add_distrib, sum_vJump_telescope, zero_add]
          simp
  intro h
  rw [h, zmod2_add_self] at hsum
  exact zero_ne_one hsum

/-- **Both parities accumulate at every point of `Γ`.** -/
theorem mem_closure_parity_set {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2)
    {w : Pt} (hw : w ∈ polygonOf v) : w ∈ closure {x | x ∉ polygonOf v ∧ parity v x = e} := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 hw
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hd := edge_ends_ne hv i
  have key : ∀ q z₁ z₂ : Pt, dist q w < ε / 2 → dist z₁ q < ε / 2 → dist z₂ q < ε / 2 →
      z₁ ∉ polygonOf v → z₂ ∉ polygonOf v → parity v z₁ ≠ parity v z₂ →
      ∃ y ∈ {x | x ∉ polygonOf v ∧ parity v x = e}, dist w y < ε := by
    intro q z₁ z₂ hq h1 h2 hz1 hz2 hne
    rcases zmod2_eq_of_ne hne e with h | h
    · exact ⟨z₁, ⟨hz1, h⟩, by linarith [dist_triangle w q z₁, dist_comm z₁ q, dist_comm q w]⟩
    · exact ⟨z₂, ⟨hz2, h⟩, by linarith [dist_triangle w q z₂, dist_comm z₂ q, dist_comm q w]⟩
  by_cases hh : (v i).2 = (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).2
  · have hc : (1 : ℝ) * (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i).1 +
        0 * (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i).2 ≠ 0 := by
      intro h1; apply hd
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero,
        Prod.snd_zero] at h1 ⊢ <;> linarith
    obtain ⟨p, hp, hpq, hpF⟩ := exists_near_on_segment hi
      (Finset.univ.image fun k => 1 * (v k).1 + 0 * (v k).2) 1 0 hc (half_pos hε)
    have hpv : ∀ k, p ≠ v k := fun k h => hpF (Finset.mem_image.2 ⟨k, Finset.mem_univ _, by
      rw [h]⟩)
    obtain ⟨ε', hε', hflip⟩ := parity_flip_vertical hv i hh hp hpv
    have ht : 0 < min ε' (ε / 2) / 2 := by positivity
    have ht1 : min ε' (ε / 2) / 2 < ε' := by linarith [min_le_left ε' (ε / 2)]
    have ht2 : min ε' (ε / 2) / 2 < ε / 2 := by linarith [min_le_right ε' (ε / 2)]
    obtain ⟨h1, h2, h3⟩ := hflip _ ht ht1
    refine key p _ _ hpq ?_ ?_ h1 h2 h3 <;>
      simp only [dist_shift_snd, dist_shift_snd_sub, abs_of_pos ht, ht2]
  · have hc : (0 : ℝ) * (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i).1 +
        1 * (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i).2 ≠ 0 := by
      intro h1; apply hh
      simp only [Prod.fst_sub, Prod.snd_sub] at h1
      linarith
    obtain ⟨p, hp, hpq, hpF⟩ := exists_near_on_segment hi
      (Finset.univ.image fun k => 0 * (v k).1 + 1 * (v k).2) 0 1 hc (half_pos hε)
    have hcv : ∀ k, (v k).2 ≠ p.2 := fun k h => hpF (Finset.mem_image.2 ⟨k, Finset.mem_univ _, by
      rw [h]; ring⟩)
    obtain ⟨ε', hε', hflip⟩ := parity_flip_at hv i hh hp hcv
    have ht : 0 < min ε' (ε / 2) / 2 := by positivity
    have ht1 : min ε' (ε / 2) / 2 < ε' := by linarith [min_le_left ε' (ε / 2)]
    have ht2 : min ε' (ε / 2) / 2 < ε / 2 := by linarith [min_le_right ε' (ε / 2)]
    obtain ⟨h1, h2, h3⟩ := hflip _ ht ht1
    refine key p _ _ hpq ?_ ?_ h1 h2 h3 <;>
      simp only [dist_shift_fst, dist_shift_fst_sub, abs_of_pos ht, ht2]

/-! ### Local structure at an interior point of an edge -/

theorem cross_zero_of_mem_segment {a b z p : Pt} (hz : z ∈ segment ℝ a b)
    (hp : p ∈ segment ℝ a b) : (z.1 - p.1) * (b - a).2 - (z.2 - p.2) * (b - a).1 = 0 := by
  rw [segment_eq_image'] at hz hp
  obtain ⟨s, -, rfl⟩ := hz
  obtain ⟨s', -, rfl⟩ := hp
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  ring

theorem eq_add_smul_of_cross_zero {d z p : Pt} (hd : d ≠ 0)
    (hc : (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 = 0) : ∃ τ : ℝ, z = p + τ • d := by
  by_cases h1 : d.1 = 0
  · have h2 : d.2 ≠ 0 := fun h2 => hd (Prod.ext h1 h2)
    rw [h1, mul_zero, sub_zero, mul_eq_zero] at hc
    rcases hc with hc | hc
    · refine ⟨(z.2 - p.2) / d.2, Prod.ext ?_ ?_⟩
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, h1, mul_zero]; linarith
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; field_simp; ring
    · exact absurd hc h2
  · refine ⟨(z.1 - p.1) / d.1, Prod.ext ?_ ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; field_simp; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; field_simp; linarith

/-- At a point `p` of the edge `i` that is not a vertex, a small ball meets `Γ` only in the line
of the edge: `ball p ρ ∩ polygonOf v = ball p ρ ∩ segment`, and the segment there is the chord of
the line `L_i` through the edge. -/
theorem polygon_local_chord {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) {p : Pt}
    (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) :
    ∃ ρ > 0, ball p ρ ∩ polygonOf v = ball p ρ ∩ polyEdge v i ∧
      ∀ z ∈ ball p ρ ∩ polyEdge v i,
        ∃ t : ℝ, z = p + t • (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) := by
  classical
  set K := ⋃ j ∈ (Finset.univ.erase i), polyEdge v j with hK_def
  have hK : IsClosed K := isClosed_biUnion_finset fun j _ => (isCompact_segment' _ _).isClosed
  have hpK : p ∉ K := by
    simp only [K, mem_iUnion, not_exists]
    intro j hj
    exact not_mem_polyEdge_of_ne hv (Finset.ne_of_mem_erase hj) hp hpv
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl p hpK
  refine ⟨ρ, hρ, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨hzb, hzΓ⟩
      refine ⟨hzb, ?_⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hzΓ
      by_cases hji : j = i
      · rw [← hji]; exact hj
      · exact absurd (mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩, hj⟩)
          (hball hzb)
    · rintro ⟨hzb, hze⟩
      exact ⟨hzb, mem_iUnion.2 ⟨i, hze⟩⟩
  · rintro z ⟨-, hz⟩
    have hz' : z ∈ segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) := hz
    have hp' : p ∈ segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) := hp
    rw [segment_eq_image'] at hz' hp'
    obtain ⟨s, -, rfl⟩ := hz'
    obtain ⟨s', -, rfl⟩ := hp'
    exact ⟨s - s', by beta_reduce; rw [sub_smul]; abel⟩

/-- The two open half-disks at `p`: the points of `ball p ρ` strictly on each side of the line of
the edge. (`sideOf p d z := (z - p).1 * d.2 - (z - p).2 * d.1`, the sign of the cross product
with the edge direction `d`.) -/
def halfDisk (p d : Pt) (ρ : ℝ) (s : Bool) : Set Pt :=
  {z | z ∈ ball p ρ ∧ (if s then 0 < (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1
                            else (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 < 0)}

theorem mem_halfDisk_true {p d z : Pt} {ρ : ℝ} (hz : dist z p < ρ)
    (h : 0 < (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1) : z ∈ halfDisk p d ρ true :=
  ⟨mem_ball.2 hz, by simpa using h⟩

theorem mem_halfDisk_false {p d z : Pt} {ρ : ℝ} (hz : dist z p < ρ)
    (h : (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 < 0) : z ∈ halfDisk p d ρ false :=
  ⟨mem_ball.2 hz, by simpa using h⟩

theorem halfDisk_convex (p d : Pt) (ρ : ℝ) (s : Bool) : Convex ℝ (halfDisk p d ρ s) := by
  cases s
  · have : halfDisk p d ρ false =
        ball p ρ ∩ {x : Pt | 0 < (-d.2) * (x.1 - p.1) + d.1 * (x.2 - p.2)} := by
      ext z
      simp only [halfDisk, mem_setOf_eq, mem_inter_iff, Bool.false_eq_true, if_false]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    rw [this]; exact convex_inter_halfplane _ (convex_ball p ρ) p _ _
  · have : halfDisk p d ρ true =
        ball p ρ ∩ {x : Pt | 0 < d.2 * (x.1 - p.1) + (-d.1) * (x.2 - p.2)} := by
      ext z
      simp only [halfDisk, mem_setOf_eq, mem_inter_iff, if_true]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    rw [this]; exact convex_inter_halfplane _ (convex_ball p ρ) p _ _

theorem halfDisk_nonempty (p d : Pt) (hd : d ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (s : Bool) :
    (halfDisk p d ρ s).Nonempty := by
  have hd2 : 0 < d.1 ^ 2 + d.2 ^ 2 := by
    by_cases h1 : d.1 = 0
    · have h2 : d.2 ≠ 0 := fun h2 => hd (Prod.ext h1 h2)
      have := pow_pos (abs_pos.2 h2) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg d.1]
    · have := pow_pos (abs_pos.2 h1) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg d.2]
  have hM : 0 < |d.1| + |d.2| + 1 := by positivity
  set τ0 := ρ / (2 * (|d.1| + |d.2| + 1)) with hτ0
  have hτ0p : 0 < τ0 := by positivity
  have hτM : τ0 * (|d.1| + |d.2| + 1) = ρ / 2 := by rw [hτ0]; field_simp
  have hb1 : τ0 * |d.1| < ρ := by nlinarith [abs_nonneg d.1, abs_nonneg d.2]
  have hb2 : τ0 * |d.2| < ρ := by nlinarith [abs_nonneg d.1, abs_nonneg d.2]
  have key : ∀ τ : ℝ, |τ| = τ0 → dist ((p.1 + τ * d.2, p.2 - τ * d.1) : Pt) p < ρ := by
    intro τ hτ
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [add_sub_cancel_left, sub_sub_cancel_left, abs_neg, abs_mul, hτ]
    exact max_lt hb2 hb1
  cases s
  · refine ⟨_, mem_halfDisk_false (key (-τ0) (by rw [abs_neg, abs_of_pos hτ0p])) ?_⟩
    have : (p.1 + -τ0 * d.2 - p.1) * d.2 - (p.2 - -τ0 * d.1 - p.2) * d.1 =
      -(τ0 * (d.1 ^ 2 + d.2 ^ 2)) := by ring
    rw [this]; exact neg_neg_of_pos (mul_pos hτ0p hd2)
  · refine ⟨_, mem_halfDisk_true (key τ0 (abs_of_pos hτ0p)) ?_⟩
    have : (p.1 + τ0 * d.2 - p.1) * d.2 - (p.2 - τ0 * d.1 - p.2) * d.1 =
      τ0 * (d.1 ^ 2 + d.2 ^ 2) := by ring
    rw [this]; exact mul_pos hτ0p hd2

/-- The ball minus the chord is the two half-disks. -/
theorem ball_diff_chord {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) {p : Pt}
    (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) :
    ∃ ρ > 0, ∀ ρ', 0 < ρ' → ρ' ≤ ρ →
      ball p ρ' \ polygonOf v =
        halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ' true ∪
        halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ' false := by
  obtain ⟨ρ₁, hρ₁, hch, -⟩ := polygon_local_chord hv i hp hpv
  set d := v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i with hd_def
  have hd : d ≠ 0 := edge_ends_ne hv i
  have hp' : p ∈ segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) := hp
  rw [segment_eq_image'] at hp'
  obtain ⟨s₀, ⟨hs0, hs1⟩, hps⟩ := hp'
  have hs0' : 0 < s₀ := lt_of_le_of_ne hs0 fun h => hpv i (by rw [← hps, ← h]; simp)
  have hs1' : s₀ < 1 := lt_of_le_of_ne hs1 fun h =>
    hpv ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ (by rw [← hps, h]; simp)
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hm : 0 < min s₀ (1 - s₀) := lt_min hs0' (by linarith)
  refine ⟨min ρ₁ (min s₀ (1 - s₀) * ‖d‖), lt_min hρ₁ (mul_pos hm hdn), fun ρ' hρ' hρ'le => ?_⟩
  have hon : ∀ z ∈ ball p ρ', (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 = 0 →
      z ∈ polyEdge v i := by
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
    rw [← hps]; beta_reduce; rw [add_smul, hd_def]; abel
  have hcross_edge : ∀ z ∈ polyEdge v i, (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 = 0 :=
    fun z hz => cross_zero_of_mem_segment hz hp
  ext z
  simp only [mem_diff, mem_union]
  constructor
  · rintro ⟨hzb, hzΓ⟩
    have hc : (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 ≠ 0 := fun hc =>
      hzΓ (mem_iUnion.2 ⟨i, hon z hzb hc⟩)
    rcases lt_or_gt_of_ne hc with h | h
    · exact Or.inr (mem_halfDisk_false (mem_ball.1 hzb) h)
    · exact Or.inl (mem_halfDisk_true (mem_ball.1 hzb) h)
  · have hoff : ∀ z ∈ ball p ρ', z ∈ polygonOf v →
        (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 = 0 := by
      intro z hzb hzΓ
      have : z ∈ ball p ρ₁ ∩ polygonOf v :=
        ⟨ball_subset_ball (hρ'le.trans (min_le_left _ _)) hzb, hzΓ⟩
      rw [hch] at this
      exact hcross_edge z this.2
    rintro (⟨hzb, hz⟩ | ⟨hzb, hz⟩)
    · refine ⟨hzb, fun hzΓ => ?_⟩
      have := hoff z hzb hzΓ
      simp only [if_true] at hz; linarith
    · refine ⟨hzb, fun hzΓ => ?_⟩
      have := hoff z hzb hzΓ
      simp only [Bool.false_eq_true, if_false] at hz; linarith

/-- **The parity flips across every edge**, horizontal ones included: the two half-disks at a
non-vertex point of an edge have different parities. -/
theorem parity_flip_edge {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) {p : Pt}
    (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball p ρ ∩ polygonOf v ⊆ polyEdge v i) :
    ∀ z₁ ∈ halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ true,
    ∀ z₂ ∈ halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ false,
      parity v z₁ ≠ parity v z₂ := by
  set d := v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i with hd_def
  have hd : d ≠ 0 := edge_ends_ne hv i
  have hcross_edge : ∀ z ∈ polyEdge v i, (z.1 - p.1) * d.2 - (z.2 - p.2) * d.1 = 0 :=
    fun z hz => cross_zero_of_mem_segment hz hp
  have hHoff : ∀ s, halfDisk p d ρ s ⊆ (polygonOf v)ᶜ := by
    intro s z hz hzΓ
    have h0 := hcross_edge z (hball ⟨hz.1, hzΓ⟩)
    have h2 := hz.2
    cases s
    · simp only [Bool.false_eq_true, if_false] at h2; linarith
    · simp only [if_true] at h2; linarith
  have hconst : ∀ s, ∀ x ∈ halfDisk p d ρ s, ∀ y ∈ halfDisk p d ρ s, parity v x = parity v y :=
    fun s x hx y hy =>
      parity_eq_of_isPreconnected (halfDisk_convex p d ρ s).isPreconnected (hHoff s) hx hy
  suffices h : ∃ y₁ ∈ halfDisk p d ρ true, ∃ y₂ ∈ halfDisk p d ρ false,
      parity v y₁ ≠ parity v y₂ by
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := h
    intro z₁ hz₁ z₂ hz₂
    rw [hconst true z₁ hz₁ y₁ hy₁, hconst false z₂ hz₂ y₂ hy₂]
    exact hne
  by_cases hh : (v i).2 = (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).2
  · have hd2 : d.2 = 0 := by simp only [hd_def, Prod.snd_sub, hh, sub_self]
    have hd1 : d.1 ≠ 0 := fun h => hd (Prod.ext h hd2)
    obtain ⟨ε, hε, hflip⟩ := parity_flip_vertical hv i hh hp hpv
    have ht : 0 < min ε ρ / 2 := by positivity
    have htε : min ε ρ / 2 < ε := by linarith [min_le_left ε ρ]
    have htρ : min ε ρ / 2 < ρ := by linarith [min_le_right ε ρ]
    obtain ⟨-, -, hne⟩ := hflip _ ht htε
    have hdp : dist ((p.1, p.2 + min ε ρ / 2) : Pt) p < ρ := by
      rw [dist_shift_snd, abs_of_pos ht]; exact htρ
    have hdm : dist ((p.1, p.2 - min ε ρ / 2) : Pt) p < ρ := by
      rw [dist_shift_snd_sub, abs_of_pos ht]; exact htρ
    rcases lt_or_gt_of_ne hd1 with h | h
    · exact ⟨_, mem_halfDisk_true hdp (by simp only [hd2]; nlinarith), _,
        mem_halfDisk_false hdm (by simp only [hd2]; nlinarith), hne⟩
    · exact ⟨_, mem_halfDisk_true hdm (by simp only [hd2]; nlinarith), _,
        mem_halfDisk_false hdp (by simp only [hd2]; nlinarith), hne.symm⟩
  · have hd2 : d.2 ≠ 0 := fun h => hh (by simp only [hd_def, Prod.snd_sub] at h; linarith)
    have hc : (0 : ℝ) * d.1 + 1 * d.2 ≠ 0 := by simpa using hd2
    obtain ⟨q, hq, hqp, hqF⟩ := exists_near_on_segment hp
      (Finset.univ.image fun k => 0 * (v k).1 + 1 * (v k).2) 0 1 hc (half_pos hρ)
    have hcv : ∀ k, (v k).2 ≠ q.2 := fun k h => hqF (Finset.mem_image.2 ⟨k, Finset.mem_univ _, by
      rw [h]; ring⟩)
    obtain ⟨ε, hε, hflip⟩ := parity_flip_at hv i hh hq hcv
    have ht : 0 < min ε (ρ / 2) / 2 := by positivity
    have htε : min ε (ρ / 2) / 2 < ε := by linarith [min_le_left ε (ρ / 2)]
    have htρ : min ε (ρ / 2) / 2 < ρ / 2 := by linarith [min_le_right ε (ρ / 2)]
    obtain ⟨-, -, hne⟩ := hflip _ ht htε
    have hcq := hcross_edge q hq
    have hdq : ∀ s : ℝ, |s| < ρ / 2 → dist ((q.1 + s, q.2) : Pt) p < ρ := by
      intro s hs
      have : dist ((q.1 + s, q.2) : Pt) q = |s| := dist_shift_fst q s
      linarith [dist_triangle ((q.1 + s, q.2) : Pt) q p]
    have hdp := hdq (min ε (ρ / 2) / 2) (by rwa [abs_of_pos ht])
    have hdm := hdq (-(min ε (ρ / 2) / 2)) (by rwa [abs_neg, abs_of_pos ht])
    simp only [← sub_eq_add_neg] at hdm
    rcases lt_or_gt_of_ne hd2 with h | h
    · exact ⟨_, mem_halfDisk_true hdm (by simp only; nlinarith), _,
        mem_halfDisk_false hdp (by simp only; nlinarith), hne⟩
    · exact ⟨_, mem_halfDisk_true hdp (by simp only; nlinarith), _,
        mem_halfDisk_false hdm (by simp only; nlinarith), hne.symm⟩

/-! ### The split of the complement -/

theorem compl_eq_union_parity_sets {n : ℕ} (v : Fin n → Pt) (e : ZMod 2) :
    (polygonOf v)ᶜ = {x | x ∉ polygonOf v ∧ parity v x = e} ∪
      {x | x ∉ polygonOf v ∧ parity v x = e + 1} := by
  ext x
  simp only [mem_compl_iff, mem_union, mem_setOf_eq]
  constructor
  · intro hx
    rcases zmod2_cases (parity v x) e with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (h | h) <;> exact h.1

theorem disjoint_parity_sets {n : ℕ} (v : Fin n → Pt) (e : ZMod 2) :
    Disjoint {x | x ∉ polygonOf v ∧ parity v x = e}
      {x | x ∉ polygonOf v ∧ parity v x = e + 1} := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h1⟩ ⟨-, h2⟩
  exact zmod2_ne_add_one e (h1.symm.trans h2)

/-- The local pieces of a parity class at a point of `Γ`: for small `r`, the parity-`e` points of
`ball w r` form a nonempty connected set (one of the two pieces of `ball_diff_rays`). -/
theorem local_piece {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) {w : Pt}
    (hw : w ∈ polygonOf v) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ →
      ({x | x ∉ polygonOf v ∧ parity v x = e} ∩ ball w r).Nonempty ∧
      IsConnected ({x | x ∉ polygonOf v ∧ parity v x = e} ∩ ball w r) :=
  local_side_of_split (isSimpleClosedPolygon_iff.2 ⟨n, v, hv, rfl⟩) (isOpen_parity_set v e)
    (isOpen_parity_set v (e + 1)) (compl_eq_union_parity_sets v e) (disjoint_parity_sets v e) hw
    (mem_closure_parity_set hv e hw) (mem_closure_parity_set hv (e + 1) hw)

/-! ### Local structure at a vertex -/

/-- At a vertex `w = v i`, with `ρ` from `polygon_local_rays`: the ball minus `Γ` is two preconnected
pieces (`ball_diff_rays`) of **different parities**, each piece of constant parity. -/
theorem vertex_two_pieces {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n) :
    ∃ ρ > 0, ∃ P₀ P₁ : Set Pt, IsPreconnected P₀ ∧ IsPreconnected P₁ ∧
      ball (v i) ρ \ polygonOf v = P₀ ∪ P₁ ∧
      (∀ z ∈ P₀, parity v z = 0) ∧ (∀ z ∈ P₁, parity v z = 1) ∧
      P₀.Nonempty ∧ P₁.Nonempty := by
  have hΓ := isSimpleClosedPolygon_iff.2 ⟨n, v, hv, rfl⟩
  have hw : v i ∈ polygonOf v := mem_iUnion.2 ⟨i, left_mem_segment _ _ _⟩
  obtain ⟨ρ, hρ, a, b, ha, hb, hab, hloc⟩ := polygon_local_rays hΓ hw
  obtain ⟨Q₁, Q₂, h1, h2, hQ⟩ := ball_diff_rays (v i) a b ha hb hab hρ
  have hdiff : ball (v i) ρ \ polygonOf v = Q₁ ∪ Q₂ := by
    rw [← hQ]; ext x
    simp only [mem_diff]
    constructor
    · rintro ⟨hxb, hxΓ⟩
      refine ⟨hxb, fun hr => hxΓ ?_⟩
      have : x ∈ (rayFrom (v i) a ∪ rayFrom (v i) b) ∩ ball (v i) ρ := ⟨hr, hxb⟩
      rw [← hloc] at this; exact this.1
    · rintro ⟨hxb, hxr⟩
      refine ⟨hxb, fun hΓx => hxr ?_⟩
      have : x ∈ polygonOf v ∩ ball (v i) ρ := ⟨hΓx, hxb⟩
      rw [hloc] at this; exact this.1
  have hQsub : Q₁ ∪ Q₂ ⊆ (polygonOf v)ᶜ := by rw [← hdiff]; exact fun x hx => hx.2
  have hs1 : Q₁ ⊆ (polygonOf v)ᶜ := subset_union_left.trans hQsub
  have hs2 : Q₂ ⊆ (polygonOf v)ᶜ := subset_union_right.trans hQsub
  have hz : ∀ e : ZMod 2, ∃ z, z ∈ Q₁ ∪ Q₂ ∧ parity v z = e := fun e => by
    obtain ⟨y, hy, hdy⟩ := Metric.mem_closure_iff.1 (mem_closure_parity_set hv e hw) ρ hρ
    exact ⟨y, by rw [← hdiff]; exact ⟨by rw [mem_ball, dist_comm]; exact hdy, hy.1⟩, hy.2⟩
  obtain ⟨z₀, hz₀, hp₀⟩ := hz 0
  obtain ⟨z₁, hz₁, hp₁⟩ := hz 1
  rcases hz₀ with h0 | h0 <;> rcases hz₁ with h1' | h1'
  · have := parity_eq_of_isPreconnected h1 hs1 h0 h1'
    rw [hp₀, hp₁] at this; exact absurd this zero_ne_one
  · exact ⟨ρ, hρ, Q₁, Q₂, h1, h2, hdiff,
      fun z hz => (parity_eq_of_isPreconnected h1 hs1 hz h0).trans hp₀,
      fun z hz => (parity_eq_of_isPreconnected h2 hs2 hz h1').trans hp₁, ⟨z₀, h0⟩, ⟨z₁, h1'⟩⟩
  · exact ⟨ρ, hρ, Q₂, Q₁, h2, h1, by rw [hdiff, union_comm],
      fun z hz => (parity_eq_of_isPreconnected h2 hs2 hz h0).trans hp₀,
      fun z hz => (parity_eq_of_isPreconnected h1 hs1 hz h1').trans hp₁, ⟨z₀, h0⟩, ⟨z₁, h1'⟩⟩
  · have := parity_eq_of_isPreconnected h2 hs2 h0 h1'
    rw [hp₀, hp₁] at this; exact absurd this zero_ne_one

/-! ### The first hit, and the neighbourhood of `Γ` -/

/-- **The first hit.** From `x ∉ Γ`, the segment towards any `y ∈ Γ` meets `Γ` first at a point `p`:
the half-open segment `[x, p)` lies in `Γᶜ`. -/
theorem exists_first_hit {n : ℕ} (v : Fin n → Pt) {x : Pt} (hx : x ∉ polygonOf v) (hn : 0 < n) :
    ∃ p ∈ polygonOf v, ∀ t : ℝ, 0 ≤ t → t < 1 → x + t • (p - x) ∉ polygonOf v := by
  classical
  set y := v ⟨0, hn⟩
  have hy : y ∈ polygonOf v := mem_iUnion.2 ⟨⟨0, hn⟩, left_mem_segment _ _ _⟩
  set f : ℝ → Pt := fun t => x + t • (y - x) with hf_def
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  set T := Icc (0 : ℝ) 1 ∩ f ⁻¹' polygonOf v
  have hT : IsCompact T := isCompact_Icc.inter_right ((isClosed_polygonOf v).preimage hf)
  have hTne : T.Nonempty := ⟨1, ⟨⟨zero_le_one, le_rfl⟩, by simp [f, hy]⟩⟩
  have ht₀ : sInf T ∈ T := hT.sInf_mem hTne
  refine ⟨f (sInf T), ht₀.2, fun t ht0 ht1 hmem => ?_⟩
  have hxt : x + t • (f (sInf T) - x) = f (t * sInf T) := by
    simp only [f]; rw [add_sub_cancel_left, smul_smul]
  rw [hxt] at hmem
  have h01 := ht₀.1
  have hle : sInf T ≤ t * sInf T :=
    csInf_le hT.bddBelow ⟨⟨mul_nonneg ht0 h01.1, by nlinarith [h01.1, h01.2]⟩, hmem⟩
  have h0 : sInf T = 0 := by nlinarith [h01.1]
  apply hx
  have := ht₀.2
  rw [h0] at this
  simpa [f] using this

/-- The segment from `x` to a point `x + t • (p - x)`, `t < 1`, of a first-hit segment lies off
`Γ`. -/
theorem segment_subset_of_first_hit {n : ℕ} {v : Fin n → Pt} {x p : Pt}
    (hp : ∀ t : ℝ, 0 ≤ t → t < 1 → x + t • (p - x) ∉ polygonOf v) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : segment ℝ x (x + t • (p - x)) ⊆ (polygonOf v)ᶜ := by
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz
  show x + s • (x + t • (p - x) - x) ∈ _
  rw [add_sub_cancel_left, smul_smul]
  exact hp _ (mul_nonneg hs0 ht0) (by nlinarith)

/-- **Every point off `Γ` is joined, inside its parity class, to every ball about a point of `Γ`
of the right parity.** -/
theorem exists_segment_to_boundary {n : ℕ} (v : Fin n → Pt) {x : Pt} (hx : x ∉ polygonOf v)
    (hn : 0 < n) :
    ∃ p ∈ polygonOf v, ∀ ρ > 0, ∃ z ∈ ball p ρ \ polygonOf v,
      parity v z = parity v x ∧ segment ℝ x z ⊆ (polygonOf v)ᶜ := by
  obtain ⟨p, hp, hhit⟩ := exists_first_hit v hx hn
  refine ⟨p, hp, fun ρ hρ => ?_⟩
  obtain ⟨t, ht0, ht1, hdist⟩ := exists_param_near_end x p hρ
  have hseg := segment_subset_of_first_hit hhit ht0 ht1
  refine ⟨x + t • (p - x), ⟨by rw [mem_ball]; exact hdist, hseg (right_mem_segment _ _ _)⟩, ?_,
    hseg⟩
  exact parity_eq_of_isPreconnected (convex_segment _ _).isPreconnected hseg
    (right_mem_segment _ _ _) (left_mem_segment _ _ _)

/-- **The parity-`e` neighbourhood of `Γ`**: the union of all the preconnected local pieces
`{x ∉ Γ | parity v x = e} ∩ ball w r`, `w ∈ Γ`, `r > 0`. -/
def sideNbhd {n : ℕ} (v : Fin n → Pt) (e : ZMod 2) : Set Pt :=
  ⋃ (w ∈ polygonOf v) (r : ℝ) (_ : 0 < r)
    (_ : IsPreconnected ({x | x ∉ polygonOf v ∧ parity v x = e} ∩ ball w r)),
    {x | x ∉ polygonOf v ∧ parity v x = e} ∩ ball w r

theorem sideNbhd_subset {n : ℕ} (v : Fin n → Pt) (e : ZMod 2) :
    sideNbhd v e ⊆ {x | x ∉ polygonOf v ∧ parity v x = e} := by
  intro x hx
  simp only [sideNbhd, mem_iUnion] at hx
  obtain ⟨w, -, r, -, -, hx⟩ := hx
  exact hx.1

theorem sideNbhd_isConnected {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) :
    IsConnected (sideNbhd v e) := by
  have hn : 0 < n := by have := hv.1; omega
  set S := {x | x ∉ polygonOf v ∧ parity v x = e} with hS
  have hloc : ∀ w ∈ polygonOf v, ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      (S ∩ ball w r').Nonempty ∧ IsConnected (S ∩ ball w r') := fun w hw => local_piece hv e hw
  choose! r₀ hr₀ hr₀c using hloc
  set P : Pt → Set Pt := fun w =>
    ⋃ (r : ℝ) (_ : 0 < r) (_ : IsPreconnected (S ∩ ball w r)), S ∩ ball w r with hP
  have hsub : ∀ w, ∀ r, 0 < r → IsPreconnected (S ∩ ball w r) → S ∩ ball w r ⊆ P w :=
    fun w r hr hc x hx => by simp only [P, mem_iUnion]; exact ⟨r, hr, hc, hx⟩
  have hEq : sideNbhd v e = ⋃ w ∈ polygonOf v, P w := rfl
  have hclos : ∀ w ∈ polygonOf v, ∀ r > 0, (S ∩ ball w r).Nonempty := fun w hw r hr => by
    obtain ⟨y, hy, hdy⟩ := Metric.mem_closure_iff.1 (mem_closure_parity_set hv e hw) r hr
    exact ⟨y, hy, by rw [mem_ball, dist_comm]; exact hdy⟩
  have hbase : ∀ w ∈ polygonOf v, S ∩ ball w (r₀ w) ⊆ P w := fun w hw =>
    hsub w _ (hr₀ w hw) (hr₀c w hw _ (hr₀ w hw) le_rfl).2.isPreconnected
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := polygonOf_nonempty v hn
    obtain ⟨y, hy⟩ := hclos w hw (r₀ w) (hr₀ w hw)
    exact ⟨y, by rw [hEq]; exact mem_biUnion hw (hbase w hw hy)⟩
  · rw [hEq]
    refine isPreconnected_biUnion_of_local_meet (isPreconnected_polygonOf v) P r₀ hr₀ ?_ ?_
    · intro w hw
      refine isPreconnected_of_forall_pair fun x hx y hy => ?_
      simp only [P, mem_iUnion] at hx hy
      obtain ⟨r₁, hr₁, hc₁, hx⟩ := hx
      obtain ⟨r₂, hr₂, hc₂, hy⟩ := hy
      obtain ⟨z, hz⟩ := hclos w hw (min r₁ r₂) (lt_min hr₁ hr₂)
      refine ⟨(S ∩ ball w r₁) ∪ (S ∩ ball w r₂),
        union_subset (hsub w r₁ hr₁ hc₁) (hsub w r₂ hr₂ hc₂), Or.inl hx, Or.inr hy, ?_⟩
      exact IsPreconnected.union z ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
        ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩ hc₁ hc₂
    · intro w hw w' hw' hb
      have hs : 0 < min (r₀ w') (r₀ w - dist w' w) :=
        lt_min (hr₀ w' hw') (by rw [mem_ball] at hb; linarith)
      obtain ⟨y, hyS, hy⟩ := hclos w' hw' _ hs
      have hy1 : y ∈ ball w' (r₀ w') := ball_subset_ball (min_le_left _ _) hy
      have hy2 : y ∈ ball w (r₀ w) := by
        rw [mem_ball] at hy ⊢
        have := dist_triangle y w' w
        have : dist y w' < r₀ w - dist w' w := hy.trans_le (min_le_right _ _)
        linarith
      exact ⟨y, hbase w hw ⟨hyS, hy2⟩, hbase w' hw' ⟨hyS, hy1⟩⟩

/-- Every point of `Γ` has, in every ball about it, points of `sideNbhd v e` for both `e`. -/
theorem sideNbhd_near {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) {p : Pt}
    (hp : p ∈ polygonOf v) : ∀ ρ > 0, (ball p ρ ∩ sideNbhd v e).Nonempty := by
  intro ρ hρ
  obtain ⟨r₀, hr₀, hc⟩ := local_piece hv e hp
  have hm : 0 < min ρ r₀ := lt_min hρ hr₀
  obtain ⟨⟨y, hy⟩, hcon⟩ := hc _ hm (min_le_right _ _)
  refine ⟨y, ball_subset_ball (min_le_left _ _) hy.2, ?_⟩
  simp only [sideNbhd, mem_iUnion]
  exact ⟨p, hp, _, hm, hcon.isPreconnected, hy⟩

/-- Every point of `Γᶜ` of parity `e` is joined to `sideNbhd v e` by a segment in `Γᶜ`. -/
theorem exists_segment_to_sideNbhd {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) {x : Pt}
    (hx : x ∉ polygonOf v) :
    ∃ z ∈ sideNbhd v (parity v x), segment ℝ x z ⊆ (polygonOf v)ᶜ := by
  have hn : 0 < n := by have := hv.1; omega
  obtain ⟨p, hp, hhit⟩ := exists_first_hit v hx hn
  obtain ⟨r₀, hr₀, hc⟩ := local_piece hv (parity v x) hp
  obtain ⟨t, ht0, ht1, hdist⟩ := exists_param_near_end x p hr₀
  have hseg := segment_subset_of_first_hit hhit ht0 ht1
  refine ⟨x + t • (p - x), ?_, hseg⟩
  simp only [sideNbhd, mem_iUnion]
  refine ⟨p, hp, r₀, hr₀, (hc r₀ hr₀ le_rfl).2.isPreconnected,
    ⟨hseg (right_mem_segment _ _ _), ?_⟩, ?_⟩
  · exact parity_eq_of_isPreconnected (convex_segment _ _).isPreconnected hseg
      (right_mem_segment _ _ _) (left_mem_segment _ _ _)
  · rw [mem_ball]; exact hdist

/-! ### The theorem -/

/-- **Each parity class is connected.** -/
theorem isConnected_parity_set {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) :
    IsConnected {x | x ∉ polygonOf v ∧ parity v x = e} := by
  obtain ⟨⟨s₀, hs₀⟩, hpre⟩ := sideNbhd_isConnected hv e
  refine ⟨⟨s₀, sideNbhd_subset v e hs₀⟩, isPreconnected_of_forall s₀ fun y hy => ?_⟩
  obtain ⟨z, hz, hseg⟩ := exists_segment_to_sideNbhd hv hy.1
  rw [hy.2] at hz
  refine ⟨sideNbhd v e ∪ segment ℝ y z, union_subset (sideNbhd_subset v e) ?_, Or.inl hs₀,
    Or.inr (left_mem_segment _ _ _),
    hpre.union z hz (right_mem_segment _ _ _) (convex_segment _ _).isPreconnected⟩
  intro u hu
  exact ⟨hseg hu, (parity_eq_of_isPreconnected (convex_segment _ _).isPreconnected hseg hu
    (left_mem_segment _ _ _)).trans hy.2⟩

/-- **The frontier of each parity class is `Γ`.** -/
theorem frontier_parity_set {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (e : ZMod 2) :
    frontier {x | x ∉ polygonOf v ∧ parity v x = e} = polygonOf v := by
  rw [(isOpen_parity_set v e).frontier_eq]
  ext z
  constructor
  · rintro ⟨hzc, hzS⟩
    by_contra hzΓ
    rcases zmod2_cases (parity v z) e with h | h
    · exact hzS ⟨hzΓ, h⟩
    · have : closure {x | x ∉ polygonOf v ∧ parity v x = e} ⊆
          {x | x ∉ polygonOf v ∧ parity v x = e + 1}ᶜ :=
        closure_minimal (disjoint_parity_sets v e).subset_compl_right
          (isOpen_parity_set v (e + 1)).isClosed_compl
      exact this hzc ⟨hzΓ, h⟩
  · intro hz
    exact ⟨mem_closure_parity_set hv e hz, fun h => h.1 hz⟩

/-- **The Jordan curve theorem for simple closed polygons** — the field `PlaneFacts.jct`, verbatim.
`U` is the odd parity class, `V` the even one. -/
theorem jct_polygon (J : Set Pt) (hJ : IsSimpleClosedPolygon J) :
    ∃ U V : Set Pt, IsOpen U ∧ IsOpen V ∧ Jᶜ = U ∪ V ∧ Disjoint U V ∧
      IsConnected U ∧ IsConnected V ∧ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      frontier U = J ∧ frontier V = J := by
  obtain ⟨n, v, hv, rfl⟩ := isSimpleClosedPolygon_iff.1 hJ
  obtain ⟨-, -, -, hbdd, -, R, hR⟩ := polygon_separates hv
  refine ⟨{x | x ∉ polygonOf v ∧ parity v x = 1}, {x | x ∉ polygonOf v ∧ parity v x = 0},
    isOpen_parity_set v 1, isOpen_parity_set v 0, ?_, ?_, isConnected_parity_set hv 1,
    isConnected_parity_set hv 0, hbdd, ?_, frontier_parity_set hv 1, frontier_parity_set hv 0⟩
  · rw [compl_eq_union_parity_sets v 0, zero_add, union_comm]
  · have := (disjoint_parity_sets v 0).symm
    rwa [zero_add] at this
  · intro hb
    obtain ⟨C, hC⟩ := hb.subset_closedBall (0 : Pt)
    set x : Pt := (max R C + 1, 0)
    have h1 : max R C + 1 ≤ dist x 0 := by
      rw [Prod.dist_eq]
      refine le_trans ?_ (le_max_left _ _)
      rw [Real.dist_eq]
      simp only [x, Prod.fst_zero, sub_zero]
      exact le_abs_self _
    have := hC (hR x (by linarith [le_max_left R C]))
    rw [mem_closedBall] at this
    linarith [le_max_right R C]

/-- `PlaneFacts` from its two remaining fields (batch 129: the `janiszewski` field, and so `hjan`,
asks polygonal sets; with `janiszewski_polygonal` the interface reduces to `enclose`:
`planeFacts_of_enclose`, `HPC/Plane/JanPoly.lean`). -/
theorem planeFacts_of_enclose_janiszewski
    (henc : ∀ M : Set Pt, Fold.Q78.IsContinuum M → ¬ SeparatesPlane M →
      ∀ G : Set Pt, IsOpen G → M ⊆ G →
        ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ Disjoint J M ∧ M ⊆ polyInterior J ∧
          polyInterior J ⊆ G)
    (hjan : ∀ A B : Set Pt, IsPolygonal A → IsPolygonal B →
      (IsConnected (A ∩ B) ∨ A ∩ B = ∅) →
      ∀ x y : Pt, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y → ¬ SeparatesPts (A ∪ B) x y) :
    PlaneFacts :=
  ⟨jct_polygon, henc, hjan⟩

end HPC.Plane
