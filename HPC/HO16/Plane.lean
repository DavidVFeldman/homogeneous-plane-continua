import HPC.HO16.Defs
import HPC.HO16.Grid
import HPC.Span.OT82Strip

/-!
# Batch 193, §6: plane approximations

Commission 193, §6; skeleton `HO16A.lean`, statements unchanged.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Span

/-! ## §6. Plane approximations (commission §6) -/

/-- A compact connected subset of `M` gives a continuum in the subtype `M`. -/
theorem isContinuum_preimage_val_of {E : Type*} [MetricSpace E] {S M : Set E} (hSM : S ⊆ M)
    (hS : IsCompact S) (hSc : IsConnected S) :
    Fold.Q78.IsContinuum (Subtype.val ⁻¹' S : Set M) := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set M) = S := by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hSM]
  refine ⟨by rw [Subtype.isCompact_iff, himg]; exact hS, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hSc.1
    exact ⟨⟨x, hSM hx⟩, hx⟩
  · rw [← IsInducing.subtypeVal.isPreconnected_image, himg]
    exact hSc.2

/-- **§6.1**: a hereditarily indecomposable plane set has empty interior. -/
theorem interior_eq_empty_of_hi {M : Set Pt} (hHI : IsHereditarilyIndecomposable (univ : Set M)) :
    interior M = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  set r := ε / 2
  have hr : 0 < r := by positivity
  have hQM : closedBall x r ⊆ M := (closedBall_subset_ball (by simp only [r]; linarith)).trans hball
  set L := closedBall x r ∩ {p : Pt | p.1 ≤ x.1}
  set R := closedBall x r ∩ {p : Pt | x.1 ≤ p.1}
  have hcpt : ∀ T : Set Pt, IsClosed T → IsCompact (closedBall x r ∩ T) := fun T hT =>
    (isCompact_closedBall x r).inter_right hT
  have hconn : ∀ T : Set Pt, Convex ℝ T → x ∈ T → IsConnected (closedBall x r ∩ T) :=
    fun T hT hxT => ⟨⟨x, mem_closedBall_self hr.le, hxT⟩,
      ((convex_closedBall x r).inter hT).isPreconnected⟩
  have hL := isContinuum_preimage_val_of (M := M) (inter_subset_left.trans hQM)
    (hcpt _ (isClosed_le continuous_fst continuous_const))
    (hconn {p : Pt | p.1 ≤ x.1} (convex_halfSpace_le (LinearMap.fst ℝ ℝ ℝ).isLinear x.1) (le_refl x.1))
  have hR := isContinuum_preimage_val_of (M := M) (inter_subset_left.trans hQM)
    (hcpt _ (isClosed_le continuous_const continuous_fst))
    (hconn {p : Pt | x.1 ≤ p.1} (convex_halfSpace_ge (LinearMap.fst ℝ ℝ ℝ).isLinear x.1) (le_refl x.1))
  have hQ := isContinuum_preimage_val_of (M := M) hQM (isCompact_closedBall x r)
    (by simpa using hconn univ convex_univ (mem_univ x))
  have hunion : (Subtype.val ⁻¹' L : Set M) ∪ Subtype.val ⁻¹' R = Subtype.val ⁻¹' closedBall x r := by
    ext p
    simp only [mem_union, mem_preimage, L, R, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      rcases le_total (p : Pt).1 x.1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hp1 : ((x.1 + r, x.2) : Pt) ∈ closedBall x r := by
    rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp [abs_of_pos hr, hr.le]
  have hp2 : ((x.1 - r, x.2) : Pt) ∈ closedBall x r := by
    rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp [abs_of_pos hr, hr.le]
  rcases (hHI _ (subset_univ _) hQ).2 _ _ hL hR (fun p hp => hp.1) (fun p hp => hp.1) hunion
    with h | h
  · have : (⟨(x.1 + r, x.2), hQM hp1⟩ : M) ∈ (Subtype.val ⁻¹' L : Set M) := by
      rw [h]; exact hp1
    have := this.2
    simp only [mem_setOf_eq] at this
    linarith
  · have : (⟨(x.1 - r, x.2), hQM hp2⟩ : M) ∈ (Subtype.val ⁻¹' R : Set M) := by
      rw [h]; exact hp2
    have := this.2
    simp only [mem_setOf_eq] at this
    linarith

-- §6.2, `exists_plGraph_approx`, is in `HPC/HO16/Grid.lean` (statement unchanged).

/-- A chain from `x₀` in a preconnected set passing through every point of a finite set. -/
theorem exists_chain_through {E : Type*} [PseudoMetricSpace E] {X : Set E}
    (hX : IsPreconnected X) {η : ℝ} (hη : 0 < η) {x₀ : E} (hx₀ : x₀ ∈ X) (T : Finset E)
    (hT : ↑T ⊆ X) :
    ∃ (m : ℕ) (c : ℕ → E), c 0 = x₀ ∧ (∀ j, c j ∈ X) ∧ (∀ j < m, dist (c j) (c (j + 1)) < η) ∧
      ∀ t ∈ T, ∃ j ≤ m, c j = t := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun _ => x₀, rfl, fun _ => hx₀, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun t ht => absurd ht (Finset.notMem_empty t)⟩
  | insert t T htT ih =>
    obtain ⟨m, c, hc0, hcX, hcd, hcT⟩ := ih (fun x hx => hT (Finset.mem_insert_of_mem hx))
    obtain ⟨m', d, hd0, hdm, hdX, hdd⟩ := exists_eps_chain hX hη (hcX m)
      (hT (Finset.mem_insert_self t T))
    refine ⟨m + m', fun j => if j ≤ m then c j else d (j - m), by simp [hc0], fun j => ?_,
      fun j hj => ?_, fun u hu => ?_⟩
    · dsimp only; split_ifs
      · exact hcX j
      · exact hdX _
    · dsimp only
      by_cases h1 : j + 1 ≤ m
      · rw [if_pos (by omega), if_pos h1]
        exact hcd j (by omega)
      · by_cases h2 : j ≤ m
        · have hj : j = m := by omega
          subst hj
          rw [if_pos le_rfl, if_neg h1, ← hd0, show j + 1 - j = 0 + 1 by omega]
          exact hdd 0 (by omega)
        · rw [if_neg h2, if_neg h1, show j + 1 - m = (j - m) + 1 by omega]
          exact hdd _ (by omega)
    · rcases Finset.mem_insert.1 hu with rfl | hu
      · refine ⟨m + m', le_rfl, ?_⟩
        dsimp only
        split_ifs with h
        · have : m' = 0 := by omega
          subst this
          rw [show m + 0 = m by omega, ← hdm, hd0]
        · rw [show m + m' - m = m' by omega, hdm]
      · obtain ⟨j, hj, hcj⟩ := hcT u hu
        exact ⟨j, by omega, by simp only [if_pos hj, hcj]⟩

/-- A point of a segment is no farther from its first end than the other end is. -/
theorem dist_le_of_mem_segment' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b p : E} (hp : p ∈ segment ℝ a b) : dist p a ≤ dist a b := by
  obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := mem_segment_iff_param.1 hp
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0,
    dist_comm, dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) hu1

/-- **§6.3**: a path close to a plane continuum. -/
theorem exists_path_approx {X : Set Pt} (hX : IsCompact X) (hXc : IsConnected X) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ γ : ℝ → Pt, Continuous γ ∧ γ '' Icc (0 : ℝ) 1 ⊆ thickening δ X ∧
      X ⊆ thickening δ (γ '' Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hXc.nonempty
  obtain ⟨T, hTX, hTf, hcov⟩ := finite_cover_balls_of_compact hX (half_pos hδ)
  obtain ⟨m, c, -, hcX, hcd, hcT⟩ := exists_chain_through hXc.isPreconnected (half_pos hδ) hx₀
    hTf.toFinset (by simpa using hTX)
  -- pad to `m + 1 ≥ 1` segments
  set c' : ℕ → Pt := fun j => c (min j m)
  have hc'X : ∀ j, c' j ∈ X := fun j => hcX _
  have hc'd : ∀ j < m + 1, dist (c' j) (c' (j + 1)) < δ / 2 := by
    intro j hj
    simp only [c']
    rcases Nat.lt_or_ge j m with h | h
    · rw [min_eq_left h.le, min_eq_left (by omega)]
      exact hcd j h
    · rw [min_eq_right h, min_eq_right (by omega), dist_self]
      exact half_pos hδ
  have hc'T : ∀ x ∈ X, ∃ j ≤ m + 1, dist x (c' j) < δ / 2 := by
    intro x hx
    obtain ⟨t, htT, hxt⟩ := mem_iUnion₂.1 (hcov hx)
    obtain ⟨j, hj, hcj⟩ := hcT t (hTf.mem_toFinset.2 htT)
    refine ⟨j, by omega, ?_⟩
    simp only [c', min_eq_left hj, hcj]
    exact hxt
  set a : Fin (m + 1 + 1) → Pt := fun k => c' k
  have hfin : ∀ j, j ≤ m + 1 → finExt a j = c' j := fun j hj => by
    rw [finExt_of_le a hj]
  have hs : 0 < m + 1 := Nat.succ_pos m
  refine ⟨plPath a, continuous_plPath a, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨j, hj, l, hl, -, hpl⟩ := plPath_eq_piece hs ht
    rw [hpl a]
    have hseg := plPath_mem_segment hl a (j := j)
    rw [hfin j hj.le, hfin (j + 1) hj] at hseg ⊢
    refine mem_thickening_iff.2 ⟨c' j, hc'X j, ?_⟩
    calc _ ≤ dist (c' j) (c' (j + 1)) := dist_le_of_mem_segment' hseg
      _ < δ / 2 := hc'd j hj
      _ < δ := half_lt_self hδ
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := hc'T x hx
    refine mem_thickening_iff.2 ⟨c' j, ⟨(j : ℝ) / (m + 1 : ℕ), ⟨by positivity, ?_⟩, ?_⟩, ?_⟩
    · rw [div_le_one (by positivity)]
      exact_mod_cast hj
    · have := plPath_at hs a ⟨j, Nat.lt_succ_of_le hj⟩
      simpa using this
    · linarith

end HPC.HO16
