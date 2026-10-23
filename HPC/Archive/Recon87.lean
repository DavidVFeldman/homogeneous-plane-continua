import HPC.PseudoArc.Recon86
import HPC.PseudoArc.T13Step

/-!
# Batch 87, item 1: time-ordering folds with three-link blocks

`Description.IsCoveringFold₃` is `Description.IsCoveringFold` (`HPC/PseudoArc/Recon86.lean`) with
the one-link clause replaced by the three-link clause used everywhere else in the repository
(Theorem 3, Theorem 4, `theorem4_pair`, `exists_step`): every block lies in the union of three
consecutive links of `D_m` (`unionRange j 3`). The other four clauses are unchanged.

`Description.coveringStep_of_folds₃`: if such folds exist with `m` and `k` arbitrarily deep, then
`CoveringStep` holds. The closures-in-`D_L` clause comes from a Lebesgue number of the cover of
`closure D_{L+1}` by the links of `D_L`, exactly as in `Description.exists_step`: a three-link
block has diameter at most `3 ε_m`.
-/

namespace HPC

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace Description

variable {P Q : X}

/-- **A time-ordering fold with three-link blocks.** As `IsCoveringFold`, but each block lies in
the union of three consecutive links of `D_m`. -/
structure IsCoveringFold₃ (Δ : Description X P Q) (P' Q' R : X) (W : Set X) (k m q : ℕ)
    (β : Fin (Δ.n k) → Fin q) (b : Fin q) : Prop where
  block : Chain.IsBlockMap β
  small : ∀ u : Fin q, ∃ j : ℕ, ∀ t, β t = u → (Δ.D k).link t ⊆ (Δ.D m).unionRange j 3
  first : ∀ t, P' ∈ (Δ.D k).link t → (β t).val = 0
  last : ∀ t, Q' ∈ (Δ.D k).link t → (β t).val = q - 1
  atR : ∀ t, R ∈ (Δ.D k).link t → β t = b
  le_b : ∀ t, ((Δ.D k).link t ∩ W).Nonempty → β t ≤ b

/-- A one-link time-ordering fold is a three-link one. -/
theorem IsCoveringFold.toFold₃ {Δ : Description X P Q} {P' Q' R : X} {W : Set X} {k m q : ℕ}
    {β : Fin (Δ.n k) → Fin q} {b : Fin q} (h : Δ.IsCoveringFold P' Q' R W k m q β b) :
    Δ.IsCoveringFold₃ P' Q' R W k m q β b where
  block := h.block
  small u := by
    obtain ⟨s, hs⟩ := h.small u
    exact ⟨s.val, fun t ht => (hs t ht).trans
      (Chain.link_subset_unionRange _ s le_rfl (by omega))⟩
  first := h.first
  last := h.last
  atR := h.atR
  le_b := h.le_b

/-- **`CoveringStep` from three-link time-ordering folds.** If for every `m₀` there are levels
`m, k ≥ m₀` and a time-ordering fold of `D_k` whose blocks lie in three consecutive links of
`D_m`, then `CoveringStep Δ P' Q' R W` holds. -/
theorem coveringStep_of_folds₃ [CompactSpace X] (Δ : Description X P Q) {P' Q' R : X}
    (hP' : P' ∈ Δ.M) (hQ' : Q' ∈ Δ.M) (hR : R ∈ Δ.M) {W : Set X} (hW : W ⊆ Δ.M)
    (hfold : ∀ m₀, ∃ m, m₀ ≤ m ∧ ∃ k, m₀ ≤ k ∧
      ∃ q, ∃ β : Fin (Δ.n k) → Fin q, ∃ b, Δ.IsCoveringFold₃ P' Q' R W k m q β b) :
    CoveringStep Δ P' Q' R W := by
  intro L
  -- a Lebesgue number of the cover of `closure D_{L+1}` by the links of `D_L`
  have hKc : IsCompact (closure (Δ.D (L + 1)).union) := isClosed_closure.isCompact
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hKc (fun t => (Δ.D L).isOpen t)
    (Δ.closure_union_subset (Nat.lt_succ_self L))
  set η := min δ (1 / ((L : ℝ) + 1)) with hη
  have hηpos : 0 < η := lt_min hδ (by positivity)
  obtain ⟨m0, hm0⟩ : ∃ m0, ∀ m, m0 ≤ m → Δ.ε m < η / 3 :=
    eventually_atTop.mp (Δ.ε_tendsto.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨m, hm, k, hk, q, β, b, hF⟩ := hfold (max m0 (L + 1))
  have hεm : Δ.ε m < η / 3 := hm0 m (le_of_max_le_left hm)
  have hLk : L + 1 ≤ k := le_of_max_le_right hk
  have hβ := hF.block
  set F := (Δ.D k).ofBlocks β hβ with hFdef
  have hmem : ∀ x ∈ Δ.M, ∃ t, x ∈ (Δ.D k).link t := fun x hx =>
    mem_iUnion.mp (Δ.M_subset_union k hx)
  have hlinkF : ∀ (u : Fin q) (x : X), x ∈ F.link u ↔ ∃ t, β t = u ∧ x ∈ (Δ.D k).link t := by
    intro u x
    rw [hFdef, Chain.ofBlocks_link]
    simp only [mem_iUnion, mem_setOf_eq, exists_prop]
  have hq : 0 < q := by
    obtain ⟨t, -⟩ := hmem P' hP'
    exact lt_of_le_of_lt (Nat.zero_le _) (β t).isLt
  -- a block lies in three consecutive links of `D_m`, so its points are within `3 ε_m`
  have hdist : ∀ u, ∀ x ∈ F.link u, ∀ y ∈ F.link u, dist x y ≤ 3 * Δ.ε m := by
    intro u x hx y hy
    obtain ⟨j, hj⟩ := hF.small u
    obtain ⟨t, ht, hxt⟩ := (hlinkF u x).mp hx
    obtain ⟨t', ht', hyt⟩ := (hlinkF u y).mp hy
    exact Chain.dist_le_of_mem_unionRange (Δ.bdd m) (Δ.diam_le m) (hj t ht hxt) (hj t' ht' hyt)
  -- the chain from `P'` to `Q'`
  have hfrom : F.IsFrom P' Q' := by
    refine ⟨hq, ?_, ?_, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hmem P' hP'
      exact (hlinkF _ _).mpr ⟨t, Fin.ext (hF.first t ht), ht⟩
    · obtain ⟨t, ht⟩ := hmem Q' hQ'
      exact (hlinkF _ _).mpr ⟨t, Fin.ext (hF.last t ht), ht⟩
    · intro u hu
      obtain ⟨t, rfl, ht⟩ := (hlinkF u P').mp hu
      exact Fin.ext (hF.first t ht)
    · intro u hu
      obtain ⟨t, rfl, ht⟩ := (hlinkF u Q').mp hu
      exact Fin.ext (hF.last t ht)
  refine ⟨k, by omega, q, F, hfrom, Chain.ofBlocks_isConsolidationOf _ β hβ, ?_, ?_, ?_⟩
  · -- closures of blocks in links of `D_L`
    intro u
    obtain ⟨x0, hx0⟩ := F.link_nonempty u
    have hx0K : x0 ∈ closure (Δ.D (L + 1)).union := by
      obtain ⟨t, -, hxt⟩ := (hlinkF u x0).mp hx0
      exact subset_closure (Chain.union_subset_of_refines (Δ.refines_of_le hLk)
        (mem_iUnion.mpr ⟨t, hxt⟩))
    obtain ⟨t, ht⟩ := hleb x0 hx0K
    refine ⟨t, subset_trans ?_ ht⟩
    have hsub : F.link u ⊆ closedBall x0 (3 * Δ.ε m) := fun y hy => by
      rw [mem_closedBall]; exact hdist u y hy x0 hx0
    refine subset_trans (isClosed_closedBall.closure_subset_iff.mpr hsub)
      (closedBall_subset_ball ?_)
    linarith [min_le_left δ (1 / ((L : ℝ) + 1))]
  · -- small diameters
    intro u
    refine diam_le_of_forall_dist_le (by positivity) (fun x hx y hy => ?_)
    have := hdist u x hx y hy
    linarith [min_le_right δ (1 / ((L : ℝ) + 1))]
  · -- covering `W` up to `R`
    have h0b : (⟨0, hq⟩ : Fin q) ≤ b := Fin.le_def.mpr (Nat.zero_le _)
    refine ⟨hq, b, h0b, ?_, ?_⟩
    · refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · obtain ⟨t, ht⟩ := hmem P' hP'
        exact (hlinkF _ _).mpr ⟨t, Fin.ext (by simp [hF.first t ht]), ht⟩
      · obtain ⟨t, ht⟩ := hmem R hR
        refine (hlinkF _ _).mpr ⟨t, ?_, ht⟩
        rw [hF.atR t ht]
        ext; simp only; omega
      · intro v hv
        obtain ⟨t, htv, ht⟩ := (hlinkF _ P').mp hv
        have h1 := hF.first t ht
        have h2 := congrArg Fin.val htv
        simp only at h2
        ext; simp only; omega
      · intro v hv
        obtain ⟨t, htv, ht⟩ := (hlinkF _ R).mp hv
        have h1 := hF.atR t ht
        have h2 := v.isLt
        ext; simp only at htv ⊢
        rw [h1] at htv
        have := congrArg Fin.val htv
        simp only at this
        omega
    · intro w hw
      obtain ⟨t, ht⟩ := hmem w (hW hw)
      have hle := hF.le_b t ⟨w, ht, hw⟩
      exact Chain.mem_span.mpr ⟨β t, Fin.le_def.mpr (Nat.zero_le _), hle,
        (hlinkF _ _).mpr ⟨t, rfl, ht⟩⟩

end Description

end HPC
