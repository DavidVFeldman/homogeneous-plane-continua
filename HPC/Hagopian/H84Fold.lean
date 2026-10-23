import Mathlib

/-!
# Batch 186, §3.1 step 4(a): folds (combinatorics)

Five open subsets `V 0, …, V 4` of `[0, 1]` covering it, non-adjacent ones disjoint, with
`0 ∈ V 0 ∖ V 1` and `1 ∈ V 4 ∖ V 3`. If one of them is not an interval, there is a *fold*: a point
`s ∈ V p` between two points of `V q ∖ V p`, for adjacent `p`, `q`.

*Proof* (not the π-argument of the commission; a sweep from left to right). Index the sets by `ℕ`
(`W j = ∅` for `j ≥ 5`). Assume there is no fold.
* *Ends* (`left_end`, `right_end`): if `u ∈ W p` and `x < u` with `x ∉ W p`, the last point `c` of
  `[x, u]` outside `W p` lies in a neighbour `W q` of `W p` (its open neighbourhood meets
  `(c, u] ⊆ W p`). Same on the right.
* *Bubbles*: a point of `W p` with points outside `W p` on both sides has two such ends; without a
  fold they lie in different neighbours.
* *Sweep* (`sweep_step`): suppose `a ∈ W p`, no point left of `a` is in a later set, and no point
  `≥ a` is in an earlier set. Then `W p` is an interval (a gap would produce a bubble whose two ends
  are forced into the same neighbour), and the first point `α > a` outside `W p` lies in `W (p+1)`,
  with the same two properties for `p + 1`. Start at `a = 0`, `p = 0`.
-/

namespace HPC.Hagopian

namespace FoldAux

open Set

/-- Adjacent indices. -/
def Adj (p q : ℕ) : Prop := p + 1 = q ∨ q + 1 = p

/-- A fold of the family `W`. -/
def HasFold (W : ℕ → Set unitInterval) : Prop :=
  ∃ r s t : unitInterval, r < s ∧ s < t ∧ ∃ p q, Adj p q ∧ s ∈ W p ∧ r ∈ W q \ W p ∧ t ∈ W q \ W p

variable {W : ℕ → Set unitInterval}

/-- The last point `c` of `[x, u]` outside `W p` lies in a neighbour of `W p`. -/
theorem left_end (hW : ∀ i, IsOpen (W i)) (hcov : ∀ u, ∃ i, u ∈ W i)
    (hdisj : ∀ i j, i + 1 < j → Disjoint (W i) (W j)) {p : ℕ} {u x : unitInterval}
    (hu : u ∈ W p) (hxu : x < u) (hx : x ∉ W p) :
    ∃ c, x ≤ c ∧ c < u ∧ c ∉ W p ∧ ∃ q, c ∈ W q ∧ Adj p q := by
  obtain ⟨c, ⟨hcS, hxc, hcu⟩, hmax⟩ :=
    ((hW p).isClosed_compl.inter isClosed_Icc).isCompact.exists_isGreatest
      (s := (W p)ᶜ ∩ Icc x u) ⟨x, hx, le_rfl, hxu.le⟩
  have hcu' : c < u := lt_of_le_of_ne hcu (by rintro rfl; exact hcS hu)
  have hint : ∀ w, c < w → w ≤ u → w ∈ W p := by
    intro w hcw hwu
    by_contra hw
    exact absurd (hmax ⟨hw, hxc.trans hcw.le, hwu⟩) (not_le.2 hcw)
  obtain ⟨q, hq⟩ := hcov c
  refine ⟨c, hxc, hcu', hcS, q, hq, ?_⟩
  obtain ⟨l, hl, hsub⟩ := exists_Ico_subset_of_mem_nhds ((hW q).mem_nhds hq) ⟨u, hcu'⟩
  obtain ⟨w, hw1, hw2⟩ := exists_between (lt_min hl hcu')
  have hwq : w ∈ W q := hsub ⟨hw1.le, hw2.trans_le (min_le_left _ _)⟩
  have hwp : w ∈ W p := hint w hw1 (hw2.trans_le (min_le_right _ _)).le
  have hne : q ≠ p := by rintro rfl; exact hcS hq
  have h1 : ¬ q + 1 < p := fun h => disjoint_left.1 (hdisj q p h) hwq hwp
  have h2 : ¬ p + 1 < q := fun h => disjoint_left.1 (hdisj p q h) hwp hwq
  unfold Adj; omega

/-- The first point `d` of `[u, y]` outside `W p` lies in a neighbour of `W p`, and `[u, d)` lies
in `W p`. -/
theorem right_end (hW : ∀ i, IsOpen (W i)) (hcov : ∀ u, ∃ i, u ∈ W i)
    (hdisj : ∀ i j, i + 1 < j → Disjoint (W i) (W j)) {p : ℕ} {u y : unitInterval}
    (hu : u ∈ W p) (huy : u < y) (hy : y ∉ W p) :
    ∃ d, u < d ∧ d ≤ y ∧ d ∉ W p ∧ (∀ w, u ≤ w → w < d → w ∈ W p) ∧ ∃ q, d ∈ W q ∧ Adj p q := by
  obtain ⟨d, ⟨hdS, hud, hdy⟩, hmin⟩ :=
    ((hW p).isClosed_compl.inter isClosed_Icc).isCompact.exists_isLeast
      (s := (W p)ᶜ ∩ Icc u y) ⟨y, hy, huy.le, le_rfl⟩
  have hud' : u < d := lt_of_le_of_ne hud (by rintro rfl; exact hdS hu)
  have hint : ∀ w, u ≤ w → w < d → w ∈ W p := by
    intro w huw hwd
    by_contra hw
    exact absurd (hmin ⟨hw, huw, hwd.le.trans hdy⟩) (not_le.2 hwd)
  obtain ⟨q, hq⟩ := hcov d
  refine ⟨d, hud', hdy, hdS, hint, q, hq, ?_⟩
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds ((hW q).mem_nhds hq) ⟨u, hud'⟩
  obtain ⟨w, hw1, hw2⟩ := exists_between (max_lt hl hud')
  have hwq : w ∈ W q := hsub ⟨(le_max_left _ _).trans_lt hw1, hw2.le⟩
  have hwp : w ∈ W p := hint w ((le_max_right _ _).trans hw1.le) hw2
  have hne : q ≠ p := by rintro rfl; exact hdS hq
  have h1 : ¬ q + 1 < p := fun h => disjoint_left.1 (hdisj q p h) hwq hwp
  have h2 : ¬ p + 1 < q := fun h => disjoint_left.1 (hdisj p q h) hwp hwq
  unfold Adj; omega

/-- **The sweep step.** -/
theorem sweep_step (hW : ∀ i, IsOpen (W i)) (hcov : ∀ u, ∃ i, u ∈ W i)
    (hdisj : ∀ i j, i + 1 < j → Disjoint (W i) (W j)) (hnf : ¬ HasFold W) {p : ℕ}
    {a : unitInterval} (hA : a ∈ W p) (hB : ∀ u, u < a → ∀ j, p < j → u ∉ W j)
    (hC : ∀ u, a ≤ u → ∀ j, j < p → u ∉ W j) (hlow : a = 0 ∨ (0 : unitInterval) ∉ W p)
    (hhigh : (1 : unitInterval) ∉ W p ∨ W (p + 1) = ∅) :
    (W p).OrdConnected ∧ ((1 : unitInterval) ∉ W p → ∃ α, α ∈ W (p + 1) ∧
      (∀ u, u < α → ∀ j, p + 1 < j → u ∉ W j) ∧ (∀ u, α ≤ u → ∀ j, j < p + 1 → u ∉ W j)) := by
  -- a bubble whose two ends are both `≥ a`, or both `< a`, gives a fold
  have fold_of : ∀ c s d q, c < s → s < d → s ∈ W p → c ∉ W p → d ∉ W p → c ∈ W q → d ∈ W q →
      Adj p q → False := fun c s d q h1 h2 hs hc hd hcq hdq hpq =>
    hnf ⟨c, s, d, h1, h2, p, q, hpq, hs, ⟨hcq, hc⟩, ⟨hdq, hd⟩⟩
  -- the neighbour of a point `≥ a` is `W (p + 1)`
  have up : ∀ v q, a ≤ v → v ∈ W q → Adj p q → q = p + 1 := by
    intro v q hv hq hpq
    rcases hpq with h | h
    · exact h.symm
    · exact absurd hq (hC v hv q (by omega))
  have down : ∀ v q, v < a → v ∈ W q → Adj p q → q + 1 = p := by
    intro v q hv hq hpq
    rcases hpq with h | h
    · exact absurd hq (hB v hv q (by omega))
    · exact h
  -- a point `u ≥ a` of `W p` with a point `α ∈ [a, u)` outside `W p` gives a fold
  have no_upper_bubble : (1 : unitInterval) ∉ W p → ∀ α u, a ≤ α → α < u → α ∉ W p → u ∈ W p →
      False := by
    intro h1 α u haα hαu hα hu
    have hu1 : u < 1 := lt_of_le_of_ne unitInterval.le_one' (by rintro rfl; exact h1 hu)
    obtain ⟨c, hαc, hcu, hc, qc, hcq, hpc⟩ := left_end hW hcov hdisj hu hαu hα
    obtain ⟨d, hud, -, hd, -, qd, hdq, hpd⟩ := right_end hW hcov hdisj hu hu1 h1
    have e1 := up c qc (haα.trans hαc) hcq hpc
    have e2 := up d qd (haα.trans (hαu.trans hud).le) hdq hpd
    subst e1
    rw [e2] at hdq
    exact fold_of c u d _ hcu hud hu hc hd hcq hdq hpc
  refine ⟨⟨fun x hx y hy z hz => ?_⟩, fun h1 => ?_⟩
  · by_contra hzW
    have hxz : x < z := lt_of_le_of_ne hz.1 (by rintro rfl; exact hzW hx)
    have hzy : z < y := lt_of_le_of_ne hz.2 (by rintro rfl; exact hzW hy)
    rcases le_or_gt a z with haz | hza
    · have haz' : a < z := lt_of_le_of_ne haz (by rintro rfl; exact hzW hA)
      obtain ⟨α, haα, hαz, hα, -, q, hαq, hpq⟩ := right_end hW hcov hdisj hA haz' hzW
      have e := up α q haα.le hαq hpq
      rcases hhigh with h1 | h5
      · exact no_upper_bubble h1 α y haα.le (hαz.trans_lt hzy) hα hy
      · subst e
        rw [h5] at hαq
        exact hαq
    · rcases hlow with rfl | h0
      · exact absurd hza (not_lt.2 (unitInterval.nonneg z))
      · have hx0 : 0 < x := lt_of_le_of_ne (unitInterval.nonneg x) (by rintro rfl; exact h0 hx)
        obtain ⟨c, -, hcx, hc, qc, hcq, hpc⟩ := left_end hW hcov hdisj hx hx0 h0
        obtain ⟨d, hxd, hdz, hd, -, qd, hdq, hpd⟩ := right_end hW hcov hdisj hx hxz hzW
        have e1 := down c qc ((hcx.trans hxz).trans hza) hcq hpc
        have e2 := down d qd (hdz.trans_lt hza) hdq hpd
        have : qd = qc := by omega
        rw [this] at hdq
        exact fold_of c x d qc hcx hxd hx hc hd hcq hdq hpc
  · have ha1 : a < 1 := lt_of_le_of_ne unitInterval.le_one' (by rintro rfl; exact h1 hA)
    obtain ⟨α, haα, -, hα, hint, q, hαq, hpq⟩ := right_end hW hcov hdisj hA ha1 h1
    have e := up α q haα.le hαq hpq
    subst e
    refine ⟨α, hαq, fun u hu j hj huj => ?_, fun u hu j hj huj => ?_⟩
    · rcases lt_or_ge u a with hua | hau
      · exact hB u hua j (by omega) huj
      · exact disjoint_left.1 (hdisj p j (by omega)) (hint u hau hu) huj
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjp | rfl
      · exact hC u (haα.le.trans hu) j hjp huj
      · have hαu : α < u := lt_of_le_of_ne hu (by rintro rfl; exact hα huj)
        exact no_upper_bubble h1 α u haα.le hαu hα huj

/-- **Folds, `ℕ`-indexed form.** -/
theorem exists_fold_nat (hW : ∀ i, IsOpen (W i)) (hcov : ∀ u, ∃ i, u ∈ W i)
    (hdisj : ∀ i j, i + 1 < j → Disjoint (W i) (W j)) (h5 : ∀ j, 5 ≤ j → W j = ∅)
    (h0 : (0 : unitInterval) ∈ W 0 \ W 1) (h1 : (1 : unitInterval) ∈ W 4 \ W 3)
    (hnc : ∃ i, ¬ (W i).OrdConnected) : HasFold W := by
  by_contra hnf
  have z_notin : ∀ p, 1 ≤ p → (0 : unitInterval) ∉ W p := by
    intro p hp h
    rcases Nat.lt_or_ge 1 p with hp' | hp'
    · exact disjoint_left.1 (hdisj 0 p (by omega)) h0.1 h
    · exact h0.2 (by rwa [show p = 1 by omega] at h)
  have o_notin : ∀ p, p ≤ 3 → (1 : unitInterval) ∉ W p := by
    intro p hp h
    rcases Nat.lt_or_ge p 3 with hp' | hp'
    · exact disjoint_left.1 (hdisj p 4 (by omega)) h h1.1
    · exact h1.2 (by rwa [show p = 3 by omega] at h)
  have step := fun p a hA hB hC hlow hhigh =>
    sweep_step (W := W) hW hcov hdisj hnf (p := p) (a := a) hA hB hC hlow hhigh
  obtain ⟨c0, n0⟩ := step 0 0 h0.1 (fun u hu => absurd hu (not_lt.2 (unitInterval.nonneg u)))
    (fun _ _ j hj => absurd hj (Nat.not_lt_zero j)) (Or.inl rfl) (Or.inl (o_notin 0 (by omega)))
  obtain ⟨a1, hA1, hB1, hC1⟩ := n0 (o_notin 0 (by omega))
  obtain ⟨c1, n1⟩ := step 1 a1 hA1 hB1 hC1 (Or.inr (z_notin 1 le_rfl))
    (Or.inl (o_notin 1 (by omega)))
  obtain ⟨a2, hA2, hB2, hC2⟩ := n1 (o_notin 1 (by omega))
  obtain ⟨c2, n2⟩ := step 2 a2 hA2 hB2 hC2 (Or.inr (z_notin 2 (by omega)))
    (Or.inl (o_notin 2 (by omega)))
  obtain ⟨a3, hA3, hB3, hC3⟩ := n2 (o_notin 2 (by omega))
  obtain ⟨c3, n3⟩ := step 3 a3 hA3 hB3 hC3 (Or.inr (z_notin 3 (by omega)))
    (Or.inl (o_notin 3 (by omega)))
  obtain ⟨a4, hA4, hB4, hC4⟩ := n3 (o_notin 3 (by omega))
  obtain ⟨c4, -⟩ := step 4 a4 hA4 hB4 hC4 (Or.inr (z_notin 4 (by omega))) (Or.inr (h5 5 le_rfl))
  obtain ⟨i, hi⟩ := hnc
  rcases Nat.lt_or_ge i 5 with hi5 | hi5
  · interval_cases i <;> contradiction
  · exact hi (h5 i hi5 ▸ Set.ordConnected_empty)

end FoldAux

open Set FoldAux

/-- **§3.1 step 4(a), folds.** Statement of the skeleton, unchanged. -/
theorem exists_fold_aux {V : Fin 5 → Set unitInterval} (hV : ∀ i, IsOpen (V i))
    (hcov : ∀ u, ∃ i, u ∈ V i) (hdisj : ∀ i j : Fin 5, (i : ℕ) + 1 < j → Disjoint (V i) (V j))
    (h0 : (0 : unitInterval) ∈ V 0 \ V 1) (h1 : (1 : unitInterval) ∈ V 4 \ V 3)
    (hnc : ∃ i, ¬ (V i).OrdConnected) :
    ∃ r s t : unitInterval, r < s ∧ s < t ∧ ∃ p q : Fin 5, ((p : ℕ) + 1 = q ∨ (q : ℕ) + 1 = p) ∧
      s ∈ V p ∧ r ∈ V q \ V p ∧ t ∈ V q \ V p := by
  classical
  set W : ℕ → Set unitInterval := fun j => if h : j < 5 then V ⟨j, h⟩ else ∅ with hWdef
  have hWV : ∀ i : Fin 5, W i = V i := fun i => by simp [hWdef, i.isLt]
  have hWbig : ∀ j, 5 ≤ j → W j = ∅ := fun j hj => by simp [hWdef, show ¬ j < 5 by omega]
  have hlt : ∀ j u, u ∈ W j → j < 5 := fun j u hu => by
    by_contra h; rw [hWbig j (by omega)] at hu; exact hu
  have hW : ∀ i, IsOpen (W i) := fun j => by
    rcases Nat.lt_or_ge j 5 with h | h
    · simpa [hWV ⟨j, h⟩] using hV ⟨j, h⟩
    · rw [hWbig j h]; exact isOpen_empty
  obtain ⟨r, s, t, hrs, hst, p, q, hpq, hs, hr, ht⟩ := exists_fold_nat hW
    (fun u => let ⟨i, hi⟩ := hcov u; ⟨i, by rw [hWV]; exact hi⟩)
    (fun i j hij => by
      rcases Nat.lt_or_ge j 5 with hj | hj
      · have := hdisj ⟨i, by omega⟩ ⟨j, hj⟩ hij
        rwa [← hWV ⟨i, by omega⟩, ← hWV ⟨j, hj⟩] at this
      · rw [hWbig j hj]; exact disjoint_empty _)
    hWbig (by simpa [hWdef] using h0) (by simpa [hWdef] using h1)
    (let ⟨i, hi⟩ := hnc; ⟨i, by rw [hWV]; exact hi⟩)
  have hp := hlt p s hs
  have hq := hlt q r hr.1
  refine ⟨r, s, t, hrs, hst, ⟨p, hp⟩, ⟨q, hq⟩, hpq, ?_, ?_, ?_⟩
  · rw [← hWV]; exact hs
  · rw [← hWV, ← hWV]; exact hr
  · rw [← hWV, ← hWV]; exact ht

end HPC.Hagopian
