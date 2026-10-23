import HPC.Plane.Snake51

/-!
# The skeleton's planar step is false

Batch 84 (COMMISSION-batch84.md §3.1). The skeleton's `exists_rect_chain_following` asks, for
*every* onto pattern with unit steps and *every* `ε > 0`, for a fine rectangle chain of mesh `< ε`
following the pattern with closures inside the coarse links. Counterexample: the rectangle chain
`(0,1)×(0,1)`, `(1/2,21/2)×(0,1)`, `(10,11)×(0,1)` (it has room), the identity pattern on `Fin 3`
and `ε = 1`. The fine link `D'_1` meets `D'_0 ⊆ (0,1)×(0,1)` and `D'_2 ⊆ (10,11)×(0,1)`, so it has
diameter at least `9`.
-/

namespace HPC.Plane

open Set

/-- The skeleton's statement of `exists_rect_chain_following`, verbatim, as a proposition. -/
def RectStepSkeleton : Prop :=
  ∀ {m : ℕ} (D : Chain Pt m), IsRectChain D →
    ∀ {n : ℕ} (x : Fin n → Fin m), Function.Surjective x →
    (∀ t t' : Fin n, t'.val = t.val + 1 → ((x t' : ℤ) - (x t : ℤ)).natAbs ≤ 1) →
    0 < n → ∀ {ε : ℝ}, 0 < ε →
    ∃ D' : Chain Pt n, IsRectChain D' ∧
      (∀ t, Metric.diam (D'.link t) < ε) ∧
      (∀ t, closure (D'.link t) ⊆ D.link (x t)) ∧
      (∀ (t : Fin n) (l : Fin m), (D'.link t ∩ D.link l).Nonempty →
        ∃ t' : Fin n, (t'.val ≤ t.val + 1 ∧ t.val ≤ t'.val + 1) ∧ l = x t')

namespace Counter

/-- Left ends of the three rectangles. -/
noncomputable def lo : Fin 3 → ℝ := ![0, 1 / 2, 10]
/-- Right ends of the three rectangles. -/
noncomputable def hi : Fin 3 → ℝ := ![1, 21 / 2, 11]

/-- The three rectangles. -/
noncomputable def rect (i : Fin 3) : Set Pt := Ioo (lo i) (hi i) ×ˢ Ioo 0 1

theorem rect_inter_nonempty_iff (i j : Fin 3) :
    (rect i ∩ rect j).Nonempty ↔ lo j < hi i ∧ lo i < hi j := by
  have hij : ∀ k, lo k < hi k := by intro k; fin_cases k <;> norm_num [lo, hi]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨h1, h2⟩, -⟩, ⟨h3, h4⟩, -⟩
    simp only at h1 h2 h3 h4
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have := hij i; have := hij j
    have e1 := le_max_left (lo i) (lo j)
    have e2 := le_max_right (lo i) (lo j)
    have e3 : max (lo i) (lo j) < min (hi i) (hi j) :=
      max_lt (lt_min (hij i) h2) (lt_min h1 (hij j))
    have e4 := min_le_left (hi i) (hi j)
    have e5 := min_le_right (hi i) (hi j)
    refine ⟨((max (lo i) (lo j) + min (hi i) (hi j)) / 2, 1 / 2), ⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      simp only <;> first | linarith | norm_num

/-- The coarse chain of the counterexample. -/
noncomputable def chain : Chain Pt 3 where
  link := rect
  isOpen _ := isOpen_Ioo.prod isOpen_Ioo
  adjacent i j := by
    rw [rect_inter_nonempty_iff]
    fin_cases i <;> fin_cases j <;> norm_num [lo, hi]

theorem closure_rect (i : Fin 3) : closure (rect i) = Icc (lo i) (hi i) ×ˢ Icc 0 1 := by
  have : lo i < hi i := by fin_cases i <;> norm_num [lo, hi]
  rw [rect, closure_prod_eq, closure_Ioo this.ne, closure_Ioo (by norm_num)]

theorem isRectChain : IsRectChain chain := by
  refine ⟨fun i => ⟨lo i, hi i, 0, 1, by fin_cases i <;> norm_num [lo, hi], by norm_num, rfl⟩,
    fun i => ?_⟩
  refine ⟨(![1 / 4, 5, 43 / 4] i, 1 / 2), ?_, ?_⟩
  · show _ ∈ rect i
    fin_cases i <;> norm_num [rect, lo, hi]
  · simp only [mem_iUnion, mem_setOf_eq, not_exists]
    intro j hj hmem
    change _ ∈ closure (rect j) at hmem
    rw [closure_rect] at hmem
    obtain ⟨⟨h1, h2⟩, -⟩ := hmem
    fin_cases i <;> fin_cases j <;> simp [lo, hi] at h1 h2 hj <;> linarith

end Counter

/-- **The skeleton's `exists_rect_chain_following` is false.** -/
theorem rectStepSkeleton_false : ¬ RectStepSkeleton := by
  intro h
  obtain ⟨D', -, hdiam, hcl, -⟩ := h Counter.chain Counter.isRectChain (x := id)
    Function.surjective_id (fun t t' ht => by simp only [id]; omega) (by norm_num)
    (ε := 1) one_pos
  obtain ⟨p, hp1, hp0⟩ := (D'.adjacent 1 0).mpr (by decide)
  obtain ⟨q, hq1, hq2⟩ := (D'.adjacent 1 2).mpr (by decide)
  have hp := hcl 0 (subset_closure hp0)
  have hq := hcl 2 (subset_closure hq2)
  have hb : Bornology.IsBounded (D'.link 1) := by
    refine (Metric.isBounded_Icc ((0 : ℝ), (0 : ℝ)) (11, 1)).subset ?_
    intro r hr
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcl 1 (subset_closure hr)
    simp only [id, Counter.lo, Counter.hi] at h1 h2
    norm_num at h1 h2
    exact ⟨⟨by linarith, h3.le⟩, ⟨by linarith, h4.le⟩⟩
  have hd := Metric.dist_le_diam_of_mem hb hp1 hq1
  have hlt := hdiam 1
  obtain ⟨⟨-, hp2⟩, -⟩ := hp
  obtain ⟨⟨hq3, -⟩, -⟩ := hq
  change p.1 < Counter.hi 0 at hp2
  rw [show Counter.hi 0 = 1 by simp [Counter.hi]] at hp2
  change Counter.lo 2 < q.1 at hq3
  rw [show Counter.lo 2 = 10 by simp [Counter.lo]] at hq3
  have : q.1 - p.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    refine le_trans ?_ (le_max_left _ _)
    rw [Real.dist_eq, abs_sub_comm]; exact le_abs_self _
  linarith

end HPC.Plane
