import HPC.Plane.Jct1

/-!
# Batch 192, §3: parity tools (commission 192 §3)

Three facts about the crossing parity `HPC.Plane.parity` of a closed polygon, none of which needs
the polygon to be simple:

* `parity_eq_zero_of_not_mem_convex` (§3.1): the parity vanishes off a compact convex set
  containing the vertices (separation by a half-plane, then `parity_eq_zero_of_far`).
* `parity_eq_of_perturb` (§3.2): moving every vertex by at most `ρ` does not change the parity at a
  point farther than `ρ` from the polygon. The proof differs from the commission's (one vertex at a
  time): all vertices are moved at once, and the difference of the two parities is written as the
  sum of the parities of the quadrilaterals `[v i, v (i+1), w (i+1), w i]` (the "rungs"
  `[v i, w i]` cancel mod 2); each quadrilateral lies in the closed `ρ`-thickening of the edge
  `[v i, v (i+1)]`, a compact convex set not containing the point, so §3.1 applies.
* `parity_flip_vertical_edge` (§3.3): the flip across a nondegenerate vertical edge.
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane

/-- The coordinates of a point of a segment lie between those of its ends. -/
theorem mem_segment_coords {u u' z : Pt} (h : z ∈ segment ℝ u u') :
    z.1 ∈ uIcc u.1 u'.1 ∧ z.2 ∈ uIcc u.2 u'.2 := by
  have := Prod.segment_subset u u' h
  rw [segment_eq_uIcc, segment_eq_uIcc] at this
  exact this

/-- A closed polygon lies in every convex set containing its vertices. -/
theorem polygonOf_subset_of_convex {n : ℕ} (v : Fin n → Pt) {C : Set Pt} (hC : Convex ℝ C)
    (hv : ∀ i, v i ∈ C) : polygonOf v ⊆ C := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  exact hC.segment_subset (hv _) (hv _) hi

/-- **§3.1**: the parity vanishes off a compact convex set containing the vertices. -/
theorem parity_eq_zero_of_not_mem_convex {n : ℕ} (v : Fin n → Pt) {C : Set Pt}
    (hC : Convex ℝ C) (hCc : IsCompact C) (hv : ∀ i, v i ∈ C) {z : Pt} (hz : z ∉ C) :
    parity v z = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [parity_eq_sum]
  obtain ⟨f, u, hfu, huz⟩ := geometric_hahn_banach_closed_point hC hCc.isClosed hz
  set H : Set Pt := {y | u < f y}
  have hHc : Convex ℝ H := convex_halfSpace_gt f.isLinear u
  have hHΓ : H ⊆ (polygonOf v)ᶜ := fun y hy hyΓ =>
    lt_asymm (hfu y (polygonOf_subset_of_convex v hC hv hyΓ)) hy
  set a := v ⟨0, hn⟩
  set w := z - a
  have hfw : 0 < f w := by
    have := hfu a (hv _)
    simp only [w, map_sub]; linarith
  have hw : w ≠ 0 := fun h => by rw [h, map_zero] at hfw; exact lt_irrefl _ hfw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  obtain ⟨R, hR⟩ := parity_eq_zero_of_far v
  set T : ℝ := (|R| + ‖z‖ + 1) / ‖w‖
  have hT : 0 ≤ T := by positivity
  have hzT : z + T • w ∈ H := by
    show u < f (z + T • w)
    rw [map_add, map_smul, smul_eq_mul]
    nlinarith
  have hfar : R < dist (z + T • w) 0 := by
    rw [dist_zero_right]
    have h1 : ‖T • w‖ = |R| + ‖z‖ + 1 := by
      rw [norm_smul, Real.norm_of_nonneg hT, div_mul_cancel₀ _ hwpos.ne']
    have h2 := norm_sub_norm_le (T • w) (-z)
    rw [norm_neg, sub_neg_eq_add, add_comm] at h2
    linarith [le_abs_self R]
  rw [parity_eq_of_isPreconnected hHc.isPreconnected hHΓ (x := z) (y := z + T • w) huz hzT]
  exact hR _ hfar

/-- The parity of a quadrilateral, edge by edge. -/
theorem parity_four (a b c d x : Pt) :
    parity ![a, b, c, d] x = ceInd x a b + ceInd x b c + ceInd x c d + ceInd x d a := by
  rw [parity_eq_sum, Fin.sum_univ_four]
  rfl

/-- **§3.2, vertex perturbation**: moving every vertex by at most `ρ` does not change the parity at
a point farther than `ρ` from the polygon. -/
theorem parity_eq_of_perturb {n : ℕ} (v w : Fin n → Pt) {ρ : ℝ} (hvw : ∀ i, dist (v i) (w i) ≤ ρ)
    {z : Pt} (hz : ρ < infDist z (polygonOf v)) : parity v z = parity w z := by
  -- the quadrilaterals have parity `0` at `z`
  have hquad : ∀ i : Fin n, parity ![v i, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩,
      w ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩, w i] z = 0 := by
    intro i
    set j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩
    set S := segment ℝ (v i) (v j)
    have hρ0 : 0 ≤ ρ := (dist_nonneg).trans (hvw i)
    refine parity_eq_zero_of_not_mem_convex _ ((convex_segment (v i) (v j)).cthickening ρ)
      ((isCompact_segment' (v i) (v j)).cthickening) ?_ ?_
    · intro k
      fin_cases k
      · exact self_subset_cthickening _ (left_mem_segment ℝ _ _)
      · exact self_subset_cthickening _ (right_mem_segment ℝ _ _)
      · exact mem_cthickening_of_dist_le _ (v j) _ _ (right_mem_segment ℝ _ _)
          (by rw [dist_comm]; exact hvw j)
      · exact mem_cthickening_of_dist_le _ (v i) _ _ (left_mem_segment ℝ _ _)
          (by rw [dist_comm]; exact hvw i)
    · intro hzS
      have hSne : S.Nonempty := ⟨v i, left_mem_segment ℝ _ _⟩
      rw [(isCompact_segment' _ _).isClosed.cthickening_eq_biUnion_closedBall hρ0] at hzS
      obtain ⟨y, hyS, hzy⟩ := mem_iUnion₂.1 hzS
      have hyΓ : y ∈ polygonOf v := mem_iUnion.2 ⟨i, hyS⟩
      have := infDist_le_dist_of_mem hyΓ (x := z)
      rw [mem_closedBall] at hzy
      linarith
  have h2 : (2 : ZMod 2) = 0 := rfl
  apply zmod2_eq_of_add_eq_zero
  rw [parity_eq_sum, parity_eq_sum, ← Finset.sum_add_distrib]
  have hrot : ∑ i : Fin n, ceInd z (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)
      (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) = ∑ i : Fin n, ceInd z (v i) (w i) := by
    simp only [next_eq_finRotate]
    exact Equiv.sum_comp (finRotate n) (fun i => ceInd z (v i) (w i))
  calc ∑ i : Fin n, (ceInd z (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) +
        ceInd z (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩))
      = ∑ i : Fin n, (parity ![v i, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩,
          w ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩, w i] z +
          (ceInd z (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)
            (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) + ceInd z (v i) (w i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [parity_four, ceInd_comm z (w _) (w i), ceInd_comm z (w i) (v i)]
        linear_combination (-(ceInd z (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)
            (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) + ceInd z (v i) (w i))) * h2
    _ = 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_eq_zero fun i _ => hquad i, zero_add,
          Finset.sum_add_distrib, hrot, zmod2_add_self]

/-- **§3.3, the flip across a vertical edge.** If edge `i` is a nondegenerate segment on the line
`x = c`, the point `b` is inside it, and every other edge stays farther than `r` from `b`, then the
parities just left and just right of `b` differ. (The skeleton's hypothesis `0 < r` is dropped: it
follows from `0 < ξ < r`.) -/
theorem parity_flip_vertical_edge {n : ℕ} (v : Fin n → Pt) (i : Fin n) {c : ℝ}
    (hi : (v i).1 = c) (hi' : (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).1 = c)
    (hne : v i ≠ v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)
    {b : Pt} (hb : b ∈ openSegment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩))
    {r : ℝ} (hfar : ∀ j : Fin n, j ≠ i → ∀ z ∈ polyEdge v j, r < dist z b)
    {ξ : ℝ} (hξ : 0 < ξ) (hξr : ξ < r) :
    parity v (c + ξ, b.2) ≠ parity v (c - ξ, b.2) := by
  set p := v i
  set q := v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩
  obtain ⟨α, β, hα, hβ, hαβ, hbab⟩ := hb
  have hb1 : b.1 = c := by
    rw [← hbab]; simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hi, hi']
    rw [← add_mul, hαβ, one_mul]
  have hb2 : b.2 = α * p.2 + β * q.2 := by
    rw [← hbab]; simp [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hpq2 : p.2 ≠ q.2 := fun h => hne (Prod.ext (hi.trans hi'.symm) h)
  -- the edge `i`
  have hedge : ceInd (c + ξ, b.2) p q + ceInd (c - ξ, b.2) p q = 1 := by
    have hstr : (p.2 ≤ b.2 ∧ b.2 < q.2) ∨ (q.2 ≤ b.2 ∧ b.2 < p.2) := by
      have hα' : α = 1 - β := by linarith
      rw [hα'] at hb2
      rcases lt_or_gt_of_ne hpq2 with h | h
      · left; constructor <;> nlinarith [mul_pos hβ (sub_pos.2 h), mul_pos hα (sub_pos.2 h)]
      · right; constructor <;> nlinarith [mul_pos hβ (sub_pos.2 h), mul_pos hα (sub_pos.2 h)]
    have hX : p.1 + (b.2 - p.2) * (q.1 - p.1) / (q.2 - p.2) = c := by
      rw [hi, hi', sub_self, mul_zero, zero_div, add_zero]
    have h1 : ¬ CrossesEast (c + ξ, b.2) p q := by
      rintro ⟨-, h⟩; simp only at h; rw [hX] at h; linarith
    have h2 : CrossesEast (c - ξ, b.2) p q := by
      refine ⟨hstr, ?_⟩; simp only; rw [hX]; linarith
    simp only [ceInd, if_neg h1, if_pos h2, zero_add]
  -- the other edges
  have hother : ∀ j : Fin n, j ≠ i →
      ceInd (c + ξ, b.2) (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) =
        ceInd (c - ξ, b.2) (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) := by
    intro j hj
    apply ceInd_congr
    set e := v j
    set e' := v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩
    unfold CrossesEast
    simp only
    constructor
    · rintro ⟨hs, hlt⟩
      refine ⟨hs, ?_⟩
      have hm := mem_segment_of_straddle hs
      have hd := hfar j hj _ hm
      rw [Prod.dist_eq, Real.dist_eq, dist_self, hb1, max_eq_left (abs_nonneg _)] at hd
      rcases abs_cases (e.1 + (b.2 - e.2) * (e'.1 - e.1) / (e'.2 - e.2) - c) with ⟨h, -⟩ | ⟨h, -⟩
      · linarith
      · linarith
    · rintro ⟨hs, hlt⟩
      refine ⟨hs, ?_⟩
      have hm := mem_segment_of_straddle hs
      have hd := hfar j hj _ hm
      rw [Prod.dist_eq, Real.dist_eq, dist_self, hb1, max_eq_left (abs_nonneg _)] at hd
      rcases abs_cases (e.1 + (b.2 - e.2) * (e'.1 - e.1) / (e'.2 - e.2) - c) with ⟨h, -⟩ | ⟨h, -⟩
      · linarith
      · linarith
  intro heq
  have hsum : parity v (c + ξ, b.2) + parity v (c - ξ, b.2) = 1 := by
    rw [parity_eq_sum, parity_eq_sum, ← Finset.sum_add_distrib,
      Finset.sum_eq_single i (fun j _ hj => by rw [hother j hj, zmod2_add_self])
        (fun h => absurd (Finset.mem_univ i) h)]
    exact hedge
  rw [heq, zmod2_add_self] at hsum
  exact absurd hsum (by decide)

end HPC.Span
