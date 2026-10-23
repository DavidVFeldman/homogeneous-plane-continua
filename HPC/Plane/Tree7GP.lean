import HPC.Plane.Tree7Cross

/-!
# Batch 119, auxiliary: lines, and non-parallel segments

`lineSet p e` is the line through `p` with direction `e`, written as the zero set of
`(q.1 - p.1) * e.2 - (q.2 - p.2) * e.1`: closed, and with empty interior when `e ≠ 0`; a finite
union of lines has empty interior, so it does not contain a ball. Two segments with non-parallel
directions meet in at most one point.
-/

namespace HPC.Plane

open Set Metric

/-- The line through `p` with direction `e` (the whole plane if `e = 0`). -/
def lineSet (p e : Pt) : Set Pt := {q | (q.1 - p.1) * e.2 - (q.2 - p.2) * e.1 = 0}

theorem isClosed_lineSet (p e : Pt) : IsClosed (lineSet p e) :=
  isClosed_eq (by fun_prop) continuous_const

theorem interior_lineSet {p e : Pt} (he : e ≠ 0) : interior (lineSet p e) = ∅ := by
  apply eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior q hq
  have hpos : 0 < e.1 ^ 2 + e.2 ^ 2 := by
    rcases e with ⟨e1, e2⟩
    by_contra h
    push_neg at h
    have h1 : e1 = 0 := by nlinarith [sq_nonneg e1, sq_nonneg e2]
    have h2 : e2 = 0 := by nlinarith [sq_nonneg e1, sq_nonneg e2]
    exact he (by simp [h1, h2])
  set M := max |e.1| |e.2| + 1 with hM
  have hM0 : 0 < M := by positivity
  set τ := ε / (2 * M) with hτ
  have hτ0 : 0 < τ := by positivity
  have hin : q + (τ * e.2, -(τ * e.1)) ∈ ball q ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_pos hτ0]
    have h1 : |e.1| < M := by have := le_max_left |e.1| |e.2|; linarith
    have h2 : |e.2| < M := by have := le_max_right |e.1| |e.2|; linarith
    have hτM : τ * M = ε / 2 := by rw [hτ]; field_simp
    refine max_lt ?_ ?_
    · calc τ * |e.2| ≤ τ * M := by gcongr
        _ < ε := by linarith
    · calc τ * |e.1| ≤ τ * M := by gcongr
        _ < ε := by linarith
  have h1 := interior_subset hq
  have h2 := interior_subset (hball hin)
  simp only [lineSet, mem_setOf_eq, Prod.fst_add, Prod.snd_add] at h1 h2
  nlinarith

/-- A finite union of lines has empty interior. -/
theorem interior_biUnion_lineSet {ι : Type*} (S : Finset ι) (p e : ι → Pt)
    (he : ∀ k ∈ S, e k ≠ 0) : interior (⋃ k ∈ S, lineSet (p k) (e k)) = ∅ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S haS ih =>
    rw [Finset.set_biUnion_insert, union_comm]
    rw [interior_union_isClosed_of_interior_empty
      (isClosed_biUnion_finset fun k _ => isClosed_lineSet _ _)
      (interior_lineSet (he a (Finset.mem_insert_self a S)))]
    exact ih fun k hk => he k (Finset.mem_insert_of_mem hk)

/-- A ball is not inside a finite union of lines. -/
theorem exists_mem_ball_notMem_lines {ι : Type*} (S : Finset ι) (p e : ι → Pt)
    (he : ∀ k ∈ S, e k ≠ 0) (c : Pt) {l : ℝ} (hl : 0 < l) :
    ∃ t ∈ ball c l, t ∉ ⋃ k ∈ S, lineSet (p k) (e k) := by
  by_contra h
  push_neg at h
  have : c ∈ interior (⋃ k ∈ S, lineSet (p k) (e k)) :=
    interior_mono h (isOpen_ball.subset_interior_iff.2 subset_rfl (mem_ball_self hl))
  rw [interior_biUnion_lineSet S p e he] at this
  exact this

/-- Two segments with non-parallel directions meet in at most one point. -/
theorem segment_inter_subsingleton {a b e d : Pt} (h : ¬ ∃ c : ℝ, b - a = c • (d - e)) :
    (segment ℝ a b ∩ segment ℝ e d).Subsingleton := by
  rintro p ⟨hp1, hp2⟩ q ⟨hq1, hq2⟩
  rw [segment_eq_image'] at hp1 hp2 hq1 hq2
  obtain ⟨s, -, rfl⟩ := hp1
  obtain ⟨s', -, hs'⟩ := hq1
  obtain ⟨u, -, hu⟩ := hp2
  obtain ⟨u', -, hu'⟩ := hq2
  simp only at hs' hu hu'
  by_cases hss : s = s'
  · rw [← hs', hss]
  · exfalso
    apply h
    refine ⟨(u - u') / (s - s'), ?_⟩
    have hd : s - s' ≠ 0 := sub_ne_zero.2 hss
    have key : (s - s') • (b - a) = (u - u') • (d - e) := by
      have : (a + s • (b - a)) - (a + s' • (b - a)) = (e + u • (d - e)) - (e + u' • (d - e)) := by
        rw [hu, hu', hs']
      simpa [sub_smul] using this
    rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- A point `q` of a translated segment puts the translation on a line. -/
theorem lineSet_of_mem_segment_translate {x y q t : Pt} (h : q ∈ segment ℝ (x + t) (y + t)) :
    t ∈ lineSet (q - x) (y - x) := by
  obtain ⟨s, -, -, e1, e2⟩ := mem_segment_prod.1 h
  simp only [lineSet, mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
    at e1 e2 ⊢
  linear_combination (-(y.2 - x.2)) * e1 + (y.1 - x.1) * e2

/-- A translated point `z + t` on a segment puts the translation on a line. -/
theorem lineSet_of_translate_mem_segment {x y z t : Pt} (h : z + t ∈ segment ℝ x y) :
    t ∈ lineSet (x - z) (if y - x = 0 then (1, 0) else y - x) := by
  obtain ⟨s, -, -, e1, e2⟩ := mem_segment_prod.1 h
  split_ifs with hyx
  · have h1 : y.1 = x.1 := by have := congrArg Prod.fst hyx; simp at this; linarith
    have h2 : y.2 = x.2 := by have := congrArg Prod.snd hyx; simp at this; linarith
    simp only [lineSet, mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, h2]
      at e1 e2 ⊢
    rw [sub_self, mul_zero, add_zero] at e2
    linarith
  · simp only [lineSet, mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      at e1 e2 ⊢
    linear_combination (y.2 - x.2) * e1 - (y.1 - x.1) * e2

/-- Parallel segments meeting after a translation put the translation on a line. -/
theorem lineSet_of_parallel {x y z w t : Pt} {c : ℝ} (hc : y - x = c • (w - z))
    (hm : (segment ℝ x y ∩ segment ℝ (z + t) (w + t)).Nonempty) :
    t ∈ lineSet (x - z) (w - z) := by
  obtain ⟨q, hq1, hq2⟩ := hm
  obtain ⟨s, -, -, e1, e2⟩ := mem_segment_prod.1 hq1
  obtain ⟨u, -, -, f1, f2⟩ := mem_segment_prod.1 hq2
  have g1 : y.1 - x.1 = c * (w.1 - z.1) := by have := congrArg Prod.fst hc; simpa using this
  have g2 : y.2 - x.2 = c * (w.2 - z.2) := by have := congrArg Prod.snd hc; simpa using this
  simp only [lineSet, mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
    at e1 e2 f1 f2 ⊢
  linear_combination (w.2 - z.2) * e1 - (w.2 - z.2) * f1 - (w.1 - z.1) * e2 + (w.1 - z.1) * f2
    + (w.2 - z.2) * s * g1 - (w.1 - z.1) * s * g2

end HPC.Plane
