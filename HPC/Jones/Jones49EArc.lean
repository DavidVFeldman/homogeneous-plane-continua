import HPC.Moore.Thm15
import HPC.Moore.Sec6Lim
import HPC.Plane.Tree6

/-!
# Batch 153: arcs (Whyburn 1939, Corollary 1, items A and B)

* `tarc_vpath`, `tarc_of_isSimplePolyArc'`: a simple polygonal arc is a topological arc (item A).
  Induction on the number of vertices, gluing one segment at a time (`TArc.union`).
* `exists_tarc_in_open`: in a compact, locally connected metric space, two distinct points of a
  connected open set are joined by an arc inside it (item B, in the form for open sets). The proof
  is Moore's nested-chain proof of F.A. Theorem 15 (`HPC.Moore.exists_irreducible`, batch 137),
  with the regions taken to be the connected open sets, followed by the arc characterization
  `isIrreducibleConnected_iff_arc`.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore.Gen

/-! ### Item A: polygonal arcs -/

/-- A nondegenerate segment is an arc. -/
theorem tarc_segment {a b : Pt} (hab : a ≠ b) : TArc a b (segment ℝ a b) := by
  have hf : Continuous (fun t : unitInterval => AffineMap.lineMap a b (t : ℝ)) :=
    (AffineMap.lineMap_continuous).comp continuous_subtype_val
  have hinj : Function.Injective (fun t : unitInterval => AffineMap.lineMap a b (t : ℝ)) := by
    intro s t hst
    exact Subtype.ext ((AffineMap.lineMap_injective ℝ hab) hst)
  have h := TArc.of_inj hf hinj
  have hr : range (fun t : unitInterval => AffineMap.lineMap a b (t : ℝ)) = segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    ext z
    simp only [mem_range, mem_image, mem_Icc]
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, ⟨t.2.1, t.2.2⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
  rw [hr] at h
  simpa using h

/-- The initial pieces of a simple polygonal arc (vertex-function form) are arcs. -/
theorem tarc_vpath {v : ℕ → Pt} {n : ℕ} (h : IsSArc v n) :
    ∀ k, 2 ≤ k → k ≤ n → TArc (v 0) (v (k - 1)) (vpath v k) := by
  obtain ⟨hn, hd, hc, hnc⟩ := h
  intro k hk2 hkn
  induction k, hk2 using Nat.le_induction with
  | base =>
    have : vpath v 2 = segment ℝ (v 0) (v 1) := by
      ext x; simp only [mem_vpath]
      constructor
      · rintro ⟨i, hi, hx⟩
        obtain rfl : i = 0 := by omega
        exact hx
      · intro hx; exact ⟨0, by omega, hx⟩
    rw [this]
    exact tarc_segment (hd 0 1 (by omega) (by omega))
  | succ k hk ih =>
    have ih := ih (by omega)
    have hsplit : vpath v (k + 1) = vpath v k ∪ segment ℝ (v (k - 1)) (v k) := by
      ext x
      simp only [mem_vpath, mem_union]
      constructor
      · rintro ⟨i, hi, hx⟩
        rcases Nat.lt_or_ge (i + 1) k with h | h
        · exact Or.inl ⟨i, h, hx⟩
        · right
          obtain rfl : i = k - 1 := by omega
          rwa [show k - 1 + 1 = k by omega] at hx
      · rintro (⟨i, hi, hx⟩ | hx)
        · exact ⟨i, by omega, hx⟩
        · exact ⟨k - 1, by omega, by rwa [show k - 1 + 1 = k by omega]⟩
    rw [hsplit, show k + 1 - 1 = k by omega]
    refine ih.union (tarc_segment (hd (k - 1) k (by omega) (by omega))) ?_
    apply subset_antisymm
    · rintro x ⟨hx1, hx2⟩
      obtain ⟨i, hi, hxi⟩ := mem_vpath.1 hx1
      rcases Nat.lt_or_ge (i + 2) k with h | h
      · have hd := hnc i (k - 1) (by omega) (by omega)
        rw [show k - 1 + 1 = k by omega] at hd
        exact (disjoint_left.mp hd hxi hx2).elim
      · obtain rfl : i = k - 2 := by omega
        have := hc (k - 2) (by omega)
        rw [show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = k by omega] at this
        rw [show k - 2 + 1 = k - 1 by omega] at hxi
        exact this ⟨hxi, hx2⟩
    · rintro x rfl
      exact ⟨ih.right_mem, left_mem_segment ℝ _ _⟩

/-- **Item A.** A simple polygonal arc is a topological arc. -/
theorem tarc_of_isSimplePolyArc' {α : Set Pt} {p q : Pt} (h : IsSimplePolyArc α p q) :
    TArc p q α := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := isSimplePolyArc_iff.1 h
  exact tarc_vpath hv n hv.1 le_rfl

/-- Two distinct points of a connected open plane set are joined by an arc inside it. -/
theorem exists_tarc_of_isOpen_plane {W : Set Pt} (hWo : IsOpen W) (hWc : IsConnected W) {a b : Pt}
    (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b) : ∃ C ⊆ W, TArc a b C := by
  obtain ⟨w, hw0, hw1, hwW⟩ := exists_polyPath_of_isConnected hWo hWc ha hb
  obtain ⟨α, hα, hαw⟩ := exists_simplePolyArc_of_polyPath hw0 hw1 hab
  exact ⟨α, hαw.trans hwW, tarc_of_isSimplePolyArc' hα⟩

/-! ### Item B: the arc theorem -/

/-- **The arc theorem for connected open subsets of Peano continua.** In a compact, locally
connected metric space, two distinct points of a connected open set `U` are joined by an arc in
`U`. Moore's nested simple chains (`HPC.Moore.exists_irreducible`) with the connected open sets as
regions give a compact connected subset of `U` irreducible between the points; it is an arc by
`isIrreducibleConnected_iff_arc`. -/
theorem exists_tarc_in_open {X : Type*} [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (hUc : IsPreconnected U) {a b : X} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a ≠ b) : ∃ C ⊆ U, TArc a b C := by
  let σ : HPC.Moore.Space X := ⟨{R | IsOpen R ∧ IsPreconnected R}⟩
  have hsmall : ∀ V : Set X, IsOpen V → ∀ x ∈ V, ∀ ε > 0,
      ∃ R ∈ σ.region, x ∈ R ∧ closure R ⊆ V ∧ R ⊆ ball x ε := by
    intro V hV x hx ε hε
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV x hx
    set r' := min (r / 2) ε with hr'
    have hr'0 : 0 < r' := lt_min (by linarith) hε
    refine ⟨connectedComponentIn (ball x r') x,
      ⟨isOpen_ball.connectedComponentIn, isPreconnected_connectedComponentIn⟩,
      mem_connectedComponentIn (mem_ball_self hr'0), ?_, ?_⟩
    · refine (closure_mono (connectedComponentIn_subset _ _)).trans
        ((closure_ball_subset_closedBall).trans ((closedBall_subset_ball ?_).trans hrV))
      have : r' ≤ r / 2 := min_le_left _ _
      linarith
    · exact (connectedComponentIn_subset _ _).trans (ball_subset_ball (min_le_right _ _))
  obtain ⟨C, hCU, hCc, hCp, haC, hbC, hirr⟩ := HPC.Moore.exists_irreducible (σ := σ)
    (fun R hR => hR.1) (fun R hR => hR.2) (fun R _ => isClosed_closure.isCompact) hsmall hU hUc
    ha hb hab
  refine ⟨C, hCU, hab, (HPC.Moore.isIrreducibleConnected_iff_arc hab).1
    ⟨hCc, ⟨⟨a, haC⟩, hCp⟩, haC, hbC, fun H hHC hne hAH hBH hH => hne ?_⟩⟩
  exact hirr H hHC hH.isPreconnected hAH hBH

/-- **Item B (the arc theorem for Peano continua).** -/
theorem exists_tarc_of_locallyConnected' {X : Type*} [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyConnectedSpace X] {a b : X} (hab : a ≠ b) :
    ∃ C : Set X, TArc a b C := by
  obtain ⟨C, -, hC⟩ := exists_tarc_in_open isOpen_univ isPreconnected_univ (mem_univ a)
    (mem_univ b) hab
  exact ⟨C, hC⟩

end HPC.Jones
