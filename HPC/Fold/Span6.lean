import HPC.Fold.Open

/-!
# `S3` at span six

`s3_near_extreme` settles every basepoint within two of an extreme, so the first span carrying
any content is six, at the single interior level `L + 3 = H - 3`. This file settles it: at span
six both arms of a faithful crooked sequence fold onto one walk, at every basepoint.

The argument has two halves, and they divide the work in a way earlier batches did not try:
the folding half uses **no crookedness at all**, and the crookedness is used only to choose
between two walks.

* **The walks.** `walk6 L` is `L+2, L+3, L+4, L+5, L+4, L+3, L+2, L+1` — the Λ-itinerary from
  the off-center base `L + 2`, peaking at `H - 1` and ending at `L + 1`; `walk6' L` is its
  reflection `L+4, L+3, L+2, L+1, L+2, L+3, L+4, L+5`.

* **The folding half** (`foldsOnto_walk6_of_lowLate`). Any 1-Lipschitz arm in `[L, L+6]` based
  at `L + 3` folds onto `walk6 L` as soon as it satisfies `LowLate`: before ever reaching the
  bottom `L` it has either reached `H - 1`, or reached `L + 1` and afterwards `H - 2`. The fold
  is explicit — a nascPhased ascending assignment `min 3 (max 0 (f j + nascPhase f j - (L+3)))`, where
  `nascPhase` counts non-ascending steps up to two, switched once to the descending assignment
  `3 + max (L + 4 - f j) 0`.

* **The crooked half** (`span6_dichotomy`). One application of the crookedness clause to an
  `H`-time and an `L`-time, plus pure logic, shows that either both arms are `LowLate` or both
  arms are `HighLate` (the reflected condition). This is where the two arms are tied together,
  and it is the step the batch-33 refutation `no_common_walk_pairA_pairB` says cannot be
  replaced by treating the arms separately.

`s3_span_six` is the conclusion of `S3` for every sequence of span at most six, and
`theorem3_span_six` is Bing's Theorem 3 in the block reading for a crooked chain whose
minimal-index range is at most six.
-/

namespace HPC.Fold

open Classical

/-! ## The two walks -/

/-- The span-six walk from the off-center base `L + 2`: up to `L + 5`, then down to `L + 1`. -/
def walk6 (L : ℤ) (u : ℕ) : ℤ := if u ≤ 3 then L + 2 + (u : ℤ) else L + 8 - (u : ℤ)

/-- The reflection of `walk6`: down from `L + 4` to `L + 1`, then up to `L + 5`. -/
def walk6' (L : ℤ) (u : ℕ) : ℤ := 2 * L + 6 - walk6 L u

/-! ## The two arm conditions -/

/-- **`LowLate`**: before the arm ever reaches the bottom `L` it has reached `H - 1`, or it has
reached `L + 1` and after that `H - 2`. -/
def LowLate {m : ℕ} (f : Fin m → ℤ) (L H : ℤ) : Prop :=
  ∀ d : Fin m, f d = L →
    (∃ j : Fin m, j.val < d.val ∧ H - 1 ≤ f j) ∨
    (∃ j j' : Fin m, j.val < j'.val ∧ j'.val < d.val ∧ f j ≤ L + 1 ∧ H - 2 ≤ f j')

/-- **`HighLate`**: the reflection of `LowLate`, with the roles of the two extremes swapped. -/
def HighLate {m : ℕ} (f : Fin m → ℤ) (L H : ℤ) : Prop :=
  ∀ d : Fin m, f d = H →
    (∃ j : Fin m, j.val < d.val ∧ f j ≤ L + 1) ∨
    (∃ j j' : Fin m, j.val < j'.val ∧ j'.val < d.val ∧ H - 1 ≤ f j ∧ f j' ≤ L + 2)

/-! ## The nascPhase -/

/-- One non-ascending step has occurred by time `j`. -/
noncomputable def nasc1 {m : ℕ} (f : Fin m → ℤ) (j : Fin m) : ℤ :=
  if ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t then 1 else 0

/-- Two non-ascending steps have occurred by time `j`. -/
noncomputable def nasc2 {m : ℕ} (f : Fin m → ℤ) (j : Fin m) : ℤ :=
  if ∃ t t' : Fin m, t.val < t'.val ∧ t'.val ≤ j.val ∧ NonAscAt f t ∧ NonAscAt f t' then 1 else 0

/-- The number of non-ascending steps up to time `j`, capped at two. -/
noncomputable def nascPhase {m : ℕ} (f : Fin m → ℤ) (j : Fin m) : ℤ := nasc1 f j + nasc2 f j

theorem nascPhase_nonneg {m : ℕ} (f : Fin m → ℤ) (j : Fin m) : 0 ≤ nascPhase f j := by
  simp only [nascPhase, nasc1, nasc2]
  split <;> split <;> norm_num

theorem nascPhase_le_two {m : ℕ} (f : Fin m → ℤ) (j : Fin m) : nascPhase f j ≤ 2 := by
  simp only [nascPhase, nasc1, nasc2]
  split <;> split <;> norm_num

theorem nascPhase_zero {m : ℕ} (f : Fin m → ℤ) (j : Fin m) (hj : j.val = 0) : nascPhase f j = 0 := by
  have h1 : ¬ ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t := by
    rintro ⟨t, ht, hNA⟩
    have := hNA.1
    omega
  have h2 : ¬ ∃ t t' : Fin m, t.val < t'.val ∧ t'.val ≤ j.val ∧ NonAscAt f t ∧ NonAscAt f t' := by
    rintro ⟨t, t', ht, ht', -, -⟩
    omega
  simp only [nascPhase, nasc1, nasc2]
  rw [if_neg h1, if_neg h2]
  norm_num

theorem nascPhase_mono {m : ℕ} (f : Fin m → ℤ) (j j' : Fin m) (h : j.val ≤ j'.val) :
    nascPhase f j ≤ nascPhase f j' := by
  simp only [nascPhase, nasc1, nasc2]
  have m1 : (if ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t then (1:ℤ) else 0) ≤
      (if ∃ t : Fin m, t.val ≤ j'.val ∧ NonAscAt f t then (1:ℤ) else 0) := by
    split
    · rename_i hc
      obtain ⟨t, ht, hNA⟩ := hc
      rw [if_pos ⟨t, by omega, hNA⟩]
    · split <;> norm_num
  have m2 : (if ∃ t t' : Fin m, t.val < t'.val ∧ t'.val ≤ j.val ∧ NonAscAt f t ∧ NonAscAt f t'
        then (1:ℤ) else 0) ≤
      (if ∃ t t' : Fin m, t.val < t'.val ∧ t'.val ≤ j'.val ∧ NonAscAt f t ∧ NonAscAt f t'
        then (1:ℤ) else 0) := by
    split
    · rename_i hc
      obtain ⟨t, t', h1, h2, h3, h4⟩ := hc
      rw [if_pos ⟨t, t', h1, by omega, h3, h4⟩]
    · split <;> norm_num
  omega

/-- The nascPhase rises by at most one per step, and only at a non-ascending step. -/
theorem nascPhase_step {m : ℕ} (f : Fin m → ℤ) (j j' : Fin m) (hjj' : j'.val = j.val + 1) :
    nascPhase f j' ≤ nascPhase f j + 1 ∧ (nascPhase f j < nascPhase f j' → f j' ≤ f j) := by
  have hna : NonAscAt f j' → f j' ≤ f j := fun h => h.2 j (by omega)
  by_cases h1 : ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t
  · -- one non-ascending step has already occurred
    have e1j : nasc1 f j = 1 := if_pos h1
    have e1j' : nasc1 f j' = 1 := if_pos (by obtain ⟨t, ht, h⟩ := h1; exact ⟨t, by omega, h⟩)
    by_cases h2 : ∃ t t' : Fin m, t.val < t'.val ∧ t'.val ≤ j.val ∧ NonAscAt f t ∧ NonAscAt f t'
    · have e2j : nasc2 f j = 1 := if_pos h2
      have e2j' : nasc2 f j' = 1 :=
        if_pos (by obtain ⟨t, t', a, b, c, d⟩ := h2; exact ⟨t, t', a, by omega, c, d⟩)
      refine ⟨by simp only [nascPhase, e1j, e1j', e2j, e2j']; omega, fun hlt => ?_⟩
      simp only [nascPhase, e1j, e1j', e2j, e2j'] at hlt
      omega
    · have e2j : nasc2 f j = 0 := if_neg h2
      refine ⟨?_, fun hlt => ?_⟩
      · have : nasc2 f j' ≤ 1 := by unfold nasc2; split <;> omega
        simp only [nascPhase, e1j, e1j', e2j]
        omega
      · -- the phase rose, so the second non-ascending step is at `j'`
        have h2' : ∃ t t' : Fin m, t.val < t'.val ∧ t'.val ≤ j'.val ∧ NonAscAt f t ∧ NonAscAt f t' := by
          by_contra hno
          have : nasc2 f j' = 0 := if_neg hno
          simp only [nascPhase, e1j, e1j', e2j, this] at hlt
          omega
        obtain ⟨t, t', hlt', ht', hNA, hNA'⟩ := h2'
        have : t'.val = j'.val := by
          by_contra hc
          exact h2 ⟨t, t', hlt', by omega, hNA, hNA'⟩
        exact hna (by rwa [show t' = j' from Fin.ext this] at hNA')
  · -- no non-ascending step yet, so none before `j` and the pair condition is empty
    have e1j : nasc1 f j = 0 := if_neg h1
    have e2j : nasc2 f j = 0 := by
      refine if_neg ?_
      rintro ⟨t, t', hlt, ht, hNA, -⟩
      exact h1 ⟨t, by omega, hNA⟩
    have e2j' : nasc2 f j' = 0 := by
      refine if_neg ?_
      rintro ⟨t, t', hlt, ht, hNA, -⟩
      exact h1 ⟨t, by omega, hNA⟩
    refine ⟨?_, fun hlt => ?_⟩
    · have : nasc1 f j' ≤ 1 := by unfold nasc1; split <;> omega
      simp only [nascPhase, e1j, e2j, e2j']
      omega
    · have h1' : ∃ t : Fin m, t.val ≤ j'.val ∧ NonAscAt f t := by
        by_contra hno
        have : nasc1 f j' = 0 := if_neg hno
        simp only [nascPhase, e1j, e2j, e2j', this] at hlt
        omega
      obtain ⟨t, ht, hNA⟩ := h1'
      have : t.val = j'.val := by
        by_contra hc
        exact h1 ⟨t, by omega, hNA⟩
      exact hna (by rwa [show t = j' from Fin.ext this] at hNA)

/-- Two non-ascending steps by the time the arm has dropped by two. -/
theorem nascPhase_eq_two_of_drop {m : ℕ} (f : Fin m → ℤ) (hm : 0 < m) (hf : IsLip f) (p : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (j : Fin m) (hj : f j ≤ p - 2) : nascPhase f j = 2 := by
  obtain ⟨t1, ht1, hmin1⟩ := exists_least_index (fun t => f t ≤ p - 1) ⟨j, by omega⟩
  obtain ⟨t2, ht2, hmin2⟩ := exists_least_index (fun t => f t ≤ p - 2) ⟨j, hj⟩
  have ht1pos : 0 < t1.val := by
    rcases Nat.eq_zero_or_pos t1.val with h | h
    · exfalso
      rw [show t1 = (⟨0, hm⟩ : Fin m) from Fin.ext (show t1.val = 0 from h)] at ht1
      omega
    · exact h
  have ht2pos : 0 < t2.val := by
    rcases Nat.eq_zero_or_pos t2.val with h | h
    · exfalso
      rw [show t2 = (⟨0, hm⟩ : Fin m) from Fin.ext (show t2.val = 0 from h)] at ht2
      omega
    · exact h
  have hNA1 : NonAscAt f t1 := by
    refine ⟨ht1pos, fun t' ht' => ?_⟩
    have := hmin1 t' (by omega)
    omega
  have hNA2 : NonAscAt f t2 := by
    refine ⟨ht2pos, fun t' ht' => ?_⟩
    have := hmin2 t' (by omega)
    omega
  have h12 : t1.val < t2.val := by
    have hle : t1.val ≤ t2.val := by
      by_contra hc
      exact hmin1 t2 (by omega) (by omega)
    rcases Nat.lt_or_ge t1.val t2.val with h | h
    · exact h
    · exfalso
      have heq : t1 = t2 := Fin.ext (by omega)
      -- the predecessor of `t1` is at level `≥ p`, so the step down to `≤ p − 2` is too big
      have hpred : ∀ t' : Fin m, t'.val + 1 = t1.val → p ≤ f t' := by
        intro t' ht'
        have := hmin1 t' (by omega)
        omega
      obtain ⟨t', ht'⟩ : ∃ t' : Fin m, t'.val + 1 = t1.val :=
        ⟨⟨t1.val - 1, by have := t1.isLt; omega⟩, by show t1.val - 1 + 1 = t1.val; omega⟩
      have hlip := hf t' t1 (by omega)
      have := hpred t' ht'
      rw [heq] at hlip
      rw [abs_le] at hlip
      omega
  have ht2j : t2.val ≤ j.val := by
    by_contra hc
    exact hmin2 j (by omega) hj
  have e1 : nasc1 f j = 1 := if_pos ⟨t1, by omega, hNA1⟩
  have e2 : nasc2 f j = 1 := if_pos ⟨t1, t2, h12, ht2j, hNA1, hNA2⟩
  simp only [nascPhase, e1, e2]
  omega

/-! ## The fold -/

/-- The ascending assignment. -/
noncomputable def aVal {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (j : Fin m) : ℤ :=
  min 3 (max 0 (f j + nascPhase f j - (L + 3)))

/-- The descending assignment. -/
def bVal {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (j : Fin m) : ℤ := 3 + max (L + 4 - f j) 0

theorem walk6_low (L : ℤ) (u : ℕ) (h : u ≤ 3) : walk6 L u = L + 2 + (u : ℤ) := if_pos h

theorem walk6_high (L : ℤ) (u : ℕ) (h : ¬ u ≤ 3) : walk6 L u = L + 8 - (u : ℤ) := if_neg h

theorem aVal_nonneg {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (j : Fin m) : 0 ≤ aVal f L j := by
  simp only [aVal]
  omega

theorem aVal_le_three {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (j : Fin m) : aVal f L j ≤ 3 := by
  simp only [aVal]
  omega

theorem bVal_bounds {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (j : Fin m) (hL : L ≤ f j) :
    3 ≤ bVal f L j ∧ bVal f L j ≤ 7 := by
  simp only [bVal]
  omega

/-- The ascending assignment lands in its window whenever the arm is above the bottom. -/
theorem aVal_window {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (j : Fin m) (h1 : L + 1 ≤ f j)
    (h2 : f j ≤ L + 6) : |f j - walk6 L (aVal f L j).toNat| ≤ 1 := by
  have hn := aVal_nonneg f L j
  have h3 := aVal_le_three f L j
  have hcast : ((aVal f L j).toNat : ℤ) = aVal f L j := Int.toNat_of_nonneg hn
  have hle : (aVal f L j).toNat ≤ 3 := by omega
  rw [walk6_low L _ hle, hcast, abs_le]
  have hp1 := nascPhase_nonneg f j
  have hp2 := nascPhase_le_two f j
  simp only [aVal] at *
  omega

/-- The descending assignment always lands in its window. -/
theorem bVal_window {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (j : Fin m) (h1 : L ≤ f j)
    (h2 : f j ≤ L + 6) : |f j - walk6 L (bVal f L j).toNat| ≤ 1 := by
  obtain ⟨hb1, hb2⟩ := bVal_bounds f L j h1
  have hcast : ((bVal f L j).toNat : ℤ) = bVal f L j := Int.toNat_of_nonneg (by omega)
  by_cases hc : (bVal f L j).toNat ≤ 3
  · rw [walk6_low L _ hc, hcast, abs_le]
    simp only [bVal] at *
    omega
  · rw [walk6_high L _ hc, hcast, abs_le]
    simp only [bVal] at *
    omega

theorem aVal_lip {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ) (j j' : Fin m)
    (hjj' : j'.val = j.val + 1) : |aVal f L j' - aVal f L j| ≤ 1 := by
  have h1 := hf j j' hjj'
  obtain ⟨hs1, hs2⟩ := nascPhase_step f j j' hjj'
  have hm := nascPhase_mono f j j' (by omega)
  rw [abs_le] at h1 ⊢
  simp only [aVal]
  by_cases hc : nascPhase f j < nascPhase f j'
  · have := hs2 hc
    omega
  · omega

theorem bVal_lip {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ) (j j' : Fin m)
    (hjj' : j'.val = j.val + 1) : |bVal f L j' - bVal f L j| ≤ 1 := by
  have h1 := hf j j' hjj'
  rw [abs_le] at h1 ⊢
  simp only [bVal]
  omega

/-- **The folding half.** A 1-Lipschitz arm in `[L, L+6]` based at `L + 3` that is `LowLate`
folds onto `walk6 L`. No crookedness is used. -/
theorem foldsOnto_walk6_of_lowLate {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 3) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 6)
    (hS : LowLate f L (L + 6)) :
    FoldsOnto f 8 (walk6 L) := by
  classical
  -- the switch time: the ascending assignment is valid before it, and the junction is legal
  have key : ∃ s : ℕ, 1 ≤ s ∧ (∀ j : Fin m, j.val < s → L + 1 ≤ f j) ∧
      (∀ j j0 : Fin m, j.val = s → j0.val + 1 = s → L + 4 ≤ f j ∧ 2 ≤ aVal f L j0) := by
    by_cases hex : ∃ d : Fin m, f d = L
    · obtain ⟨a, ha, hamin⟩ := exists_least_index (fun d => f d = L) hex
      have hapos : 0 < a.val := by
        rcases Nat.eq_zero_or_pos a.val with h | h
        · exfalso
          rw [show a = (⟨0, hm⟩ : Fin m) from Fin.ext (show a.val = 0 from h)] at ha
          omega
        · exact h
      have hbefore : ∀ j : Fin m, j.val < a.val → L + 1 ≤ f j := by
        intro j hj
        have h1 := hamin j hj
        have h2 := hL j
        omega
      rcases hS a ha with ⟨j0, hj0a, hj0⟩ | ⟨j1, j2, h12, h2a, hj1, hj2⟩
      · -- the arm has reached `H − 1` before the bottom
        obtain ⟨jh, ⟨hjha, hjh⟩, -⟩ :=
          exists_least_index (fun t => t.val < a.val ∧ L + 5 ≤ f t) ⟨j0, hj0a, by omega⟩
        refine ⟨jh.val + 1, by omega, fun j hj => hbefore j (by omega), ?_⟩
        intro j jj0 hjs hj0s
        have hjj0 : jj0 = jh := Fin.ext (by omega)
        subst hjj0
        have hstep := hf jj0 j (by omega)
        rw [abs_le] at hstep
        have hp := nascPhase_nonneg f jj0
        refine ⟨by omega, ?_⟩
        simp only [aVal]
        omega
      · -- the arm has reached `L + 1` and afterwards `H − 2`
        obtain ⟨jh, ⟨hjh1, hjh2⟩, hjhmin⟩ :=
          exists_least_index (fun t => j1.val < t.val ∧ L + 4 ≤ f t) ⟨j2, h12, by omega⟩
        have hjhle : jh.val ≤ j2.val := by
          by_contra hc
          exact hjhmin j2 (by omega) ⟨h12, by omega⟩
        refine ⟨jh.val, by omega, fun j hj => hbefore j (by omega), ?_⟩
        intro j jj0 hjs hj0s
        have hjjh : j = jh := Fin.ext (by omega)
        subst hjjh
        refine ⟨hjh2, ?_⟩
        have hph : nascPhase f jj0 = 2 := by
          have h2' : nascPhase f j1 = 2 :=
            nascPhase_eq_two_of_drop f hm hf (L + 3) h0 j1 (by omega)
          have hmono := nascPhase_mono f j1 jj0 (by omega)
          have hle2 := nascPhase_le_two f jj0
          omega
        have hstep := hf jj0 j (by omega)
        rw [abs_le] at hstep
        simp only [aVal]
        omega
    · -- the arm never reaches the bottom
      refine ⟨m, by omega, ?_, ?_⟩
      · intro j hj
        have h1 : f j ≠ L := fun h => hex ⟨j, h⟩
        have h2 := hL j
        omega
      · intro j jj0 hjs _
        exact absurd j.isLt (by omega)
  obtain ⟨s, hs1, hs2, hs3⟩ := key
  refine ⟨fun j => if j.val < s then (aVal f L j).toNat else (bVal f L j).toNat,
    ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · -- inside the walk
    intro j
    by_cases hc : j.val < s
    · rw [if_pos hc]
      have h1 := aVal_nonneg f L j
      have h2 := aVal_le_three f L j
      omega
    · rw [if_neg hc]
      obtain ⟨h1, h2⟩ := bVal_bounds f L j (hL j)
      omega
  · -- 1-Lipschitz
    intro j j' hjj'
    by_cases hc : j.val < s <;> by_cases hc' : j'.val < s
    · rw [if_pos hc, if_pos hc']
      have h1 := aVal_lip f hf L j j' hjj'
      have h2 := aVal_nonneg f L j
      have h3 := aVal_nonneg f L j'
      rw [abs_le] at h1 ⊢
      omega
    · -- the junction
      rw [if_pos hc, if_neg hc']
      obtain ⟨hfj', haj⟩ := hs3 j' j (by omega) (by omega)
      have hb : bVal f L j' = 3 := by simp only [bVal]; omega
      have h2 := aVal_le_three f L j
      rw [hb, abs_le]
      omega
    · exact absurd hjj' (by omega)
    · rw [if_neg hc, if_neg hc']
      have h1 := bVal_lip f hf L j j' hjj'
      obtain ⟨h2, h3⟩ := bVal_bounds f L j (hL j)
      obtain ⟨h4, h5⟩ := bVal_bounds f L j' (hL j')
      rw [abs_le] at h1 ⊢
      omega
  · -- the basepoint is at time zero
    intro j hj
    have hz : aVal f L j = 0 := by
      have hph := nascPhase_zero f j hj
      have hfj : f j = L + 3 := by
        rw [show j = (⟨0, hm⟩ : Fin m) from Fin.ext hj]
        exact h0
      simp only [aVal, hph, hfj]
      omega
    rw [if_pos (by omega), hz]
    rfl
  · -- every level inside its window
    intro j
    by_cases hc : j.val < s
    · rw [if_pos hc]
      exact aVal_window f L j (hs2 j hc) (hH j)
    · rw [if_neg hc]
      exact bVal_window f L j (hL j) (hH j)

/-- The reflected form: a `HighLate` arm folds onto `walk6' L`. -/
theorem foldsOnto_walk6'_of_highLate {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 3) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 6)
    (hS : HighLate f L (L + 6)) :
    FoldsOnto f 8 (walk6' L) := by
  set g : Fin m → ℤ := fun j => 2 * L + 6 - f j with hg
  have hglip : IsLip g := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [hg]
    rw [abs_le] at this ⊢
    omega
  have hg0 : g ⟨0, hm⟩ = L + 3 := by simp only [hg]; omega
  have hgL : ∀ j, L ≤ g j := fun j => by have := hH j; simp only [hg]; omega
  have hgH : ∀ j, g j ≤ L + 6 := fun j => by have := hL j; simp only [hg]; omega
  have hgS : LowLate g L (L + 6) := by
    intro d hd
    have hfd : f d = L + 6 := by simp only [hg] at hd; omega
    rcases hS d hfd with ⟨j, hjd, hj⟩ | ⟨j, j', hjj', hj'd, hj, hj'⟩
    · exact Or.inl ⟨j, hjd, by simp only [hg]; omega⟩
    · exact Or.inr ⟨j, j', hjj', hj'd, by simp only [hg]; omega, by simp only [hg]; omega⟩
  obtain ⟨β, h1, h2, h3, h4⟩ := foldsOnto_walk6_of_lowLate hm g hglip L hg0 hgL hgH hgS
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [hg] at this
  simp only [walk6']
  rw [abs_le] at this ⊢
  omega

/-! ## The dichotomy -/

/-- No arm can fail both conditions: the two witnesses would be in the wrong order. -/
theorem not_lowLate_highLate {m : ℕ} (f : Fin m → ℤ) (L H : ℤ) (hLH : L + 3 ≤ H)
    (h1 : ¬ LowLate f L H) (h2 : ¬ HighLate f L H) : False := by
  rw [LowLate] at h1
  rw [HighLate] at h2
  push_neg at h1 h2
  obtain ⟨a, ha, hna1, -⟩ := h1
  obtain ⟨b, hb, hnb1, -⟩ := h2
  rcases lt_trichotomy b.val a.val with hlt | heq | hgt
  · have := hna1 b hlt
    omega
  · rw [show b = a from Fin.ext heq] at hb
    omega
  · have := hnb1 a hgt
    omega

/-- **The crooked half.** One application of the crookedness clause to an `H`-time before the
basepoint and an `L`-time after it. -/
theorem lowLate_armG_of_not_highLate_armT {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (H L : ℤ) (hLH : L + 3 ≤ H)
    (h1 : ¬ LowLate (armG ρ i) L H) (h2 : ¬ HighLate (armT ρ i) L H) : False := by
  rw [LowLate] at h1
  rw [HighLate] at h2
  push_neg at h1 h2
  obtain ⟨dG, hdG, -, hG2⟩ := h1
  obtain ⟨dT, hdT, hT1, -⟩ := h2
  have hi := i.isLt
  have hdGlt := dG.isLt
  have hdTlt := dT.isLt
  have ha : ρ ⟨i.val + dG.val, by omega⟩ = L := hdG
  have hb : ρ ⟨i.val - dT.val, by omega⟩ = H := hdT
  have hba : (⟨i.val - dT.val, by omega⟩ : Fin n) < ⟨i.val + dG.val, by omega⟩ := by
    rw [Fin.lt_def]
    show i.val - dT.val < i.val + dG.val
    rcases Nat.eq_zero_or_pos dT.val with h | h
    · rcases Nat.eq_zero_or_pos dG.val with h' | h'
      · exfalso
        rw [show (⟨i.val - dT.val, by omega⟩ : Fin n) = ⟨i.val + dG.val, by omega⟩ from
          Fin.ext (by show i.val - dT.val = i.val + dG.val; omega), ha] at hb
        omega
      · omega
    · omega
  obtain ⟨r, r', hbr, hrr', hr'a, -, hcase⟩ :=
    hcr.crooked ⟨i.val - dT.val, by omega⟩ ⟨i.val + dG.val, by omega⟩ hba H L
      ⟨⟨i.val - dT.val, by omega⟩, by simp, by omega, by
        have := hcr.le (⟨i.val - dT.val, by omega⟩ : Fin n); omega⟩
      ⟨⟨i.val + dG.val, by omega⟩, by simp, by omega, by
        have := hcr.le (⟨i.val + dG.val, by omega⟩ : Fin n); omega⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, -⟩, ⟨-, hr'2⟩⟩ := hcase (by omega)
  have hwr' := hcr.width r'
  have hrlt : i.val - dT.val < r.val := hbr
  have hrr'lt : r.val < r'.val := hrr'
  have hr'alt : r'.val < i.val + dG.val := hr'a
  have hrn := r.isLt
  have hr'n := r'.isLt
  rcases le_or_gt r.val i.val with hcase' | hcase'
  · -- the low witness is in the backward arm, before its `H`-time
    have he : armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    have := hT1 ⟨i.val - r.val, by omega⟩ (by show i.val - r.val < dT.val; omega)
    omega
  · -- both witnesses are in the forward arm, before its `L`-time
    have he : armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r := by
      show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
    have he' : armG ρ i ⟨r'.val - i.val, by omega⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    have := hG2 ⟨r.val - i.val, by omega⟩ ⟨r'.val - i.val, by omega⟩
      (by show r.val - i.val < r'.val - i.val; omega)
      (by show r'.val - i.val < dG.val; omega) (by omega)
    omega

/-- The mirror of `lowLate_armG_of_not_highLate_armT`. -/
theorem lowLate_armT_of_not_highLate_armG {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (H L : ℤ) (hLH : L + 3 ≤ H)
    (h1 : ¬ LowLate (armT ρ i) L H) (h2 : ¬ HighLate (armG ρ i) L H) : False := by
  rw [LowLate] at h1
  rw [HighLate] at h2
  push_neg at h1 h2
  obtain ⟨dT, hdT, -, hT2⟩ := h1
  obtain ⟨dG, hdG, hG1, -⟩ := h2
  have hi := i.isLt
  have hdGlt := dG.isLt
  have hdTlt := dT.isLt
  have ha : ρ ⟨i.val - dT.val, by omega⟩ = L := hdT
  have hb : ρ ⟨i.val + dG.val, by omega⟩ = H := hdG
  have hab : (⟨i.val - dT.val, by omega⟩ : Fin n) < ⟨i.val + dG.val, by omega⟩ := by
    rw [Fin.lt_def]
    show i.val - dT.val < i.val + dG.val
    rcases Nat.eq_zero_or_pos dT.val with h | h
    · rcases Nat.eq_zero_or_pos dG.val with h' | h'
      · exfalso
        rw [show (⟨i.val - dT.val, by omega⟩ : Fin n) = ⟨i.val + dG.val, by omega⟩ from
          Fin.ext (by show i.val - dT.val = i.val + dG.val; omega), hb] at ha
        omega
      · omega
    · omega
  obtain ⟨r, r', har, hrr', hr'b, hcase, -⟩ :=
    hcr.crooked ⟨i.val - dT.val, by omega⟩ ⟨i.val + dG.val, by omega⟩ hab L H
      ⟨⟨i.val - dT.val, by omega⟩, by simp, by omega, by
        have := hcr.le (⟨i.val - dT.val, by omega⟩ : Fin n); omega⟩
      ⟨⟨i.val + dG.val, by omega⟩, by simp, by omega, by
        have := hcr.le (⟨i.val + dG.val, by omega⟩ : Fin n); omega⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨-, hr1⟩, ⟨hr'2, -⟩⟩ := hcase (by omega)
  have hwr := hcr.width r
  have harlt : i.val - dT.val < r.val := har
  have hrr'lt : r.val < r'.val := hrr'
  have hr'blt : r'.val < i.val + dG.val := hr'b
  have hrn := r.isLt
  have hr'n := r'.isLt
  rcases le_or_gt r'.val i.val with hcase' | hcase'
  · -- both witnesses are in the backward arm, before its `L`-time
    have he : armT ρ i ⟨i.val - r'.val, by omega⟩ = ρ r' := by
      show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
    have he' : armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    have := hT2 ⟨i.val - r'.val, by omega⟩ ⟨i.val - r.val, by omega⟩
      (by show i.val - r'.val < i.val - r.val; omega)
      (by show i.val - r.val < dT.val; omega) (by omega)
    omega
  · -- the low witness is in the forward arm, before its `H`-time
    have he : armG ρ i ⟨r'.val - i.val, by omega⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    have := hG1 ⟨r'.val - i.val, by omega⟩ (by show r'.val - i.val < dG.val; omega)
    omega

/-- **The dichotomy.** Either both arms are `LowLate` or both arms are `HighLate`. -/
theorem span6_dichotomy {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) (H L : ℤ)
    (hLH : L + 3 ≤ H) :
    (LowLate (armG ρ i) L H ∧ LowLate (armT ρ i) L H) ∨
      (HighLate (armG ρ i) L H ∧ HighLate (armT ρ i) L H) := by
  by_cases hG : LowLate (armG ρ i) L H
  · by_cases hT : LowLate (armT ρ i) L H
    · exact Or.inl ⟨hG, hT⟩
    · refine Or.inr ⟨?_, ?_⟩
      · by_contra hc
        exact lowLate_armT_of_not_highLate_armG hcr i H L hLH hT hc
      · by_contra hc
        exact not_lowLate_highLate (armT ρ i) L H hLH hT hc
  · refine Or.inr ⟨?_, ?_⟩
    · by_contra hc
      exact not_lowLate_highLate (armG ρ i) L H hLH hG hc
    · by_contra hc
      exact lowLate_armG_of_not_highLate_armT hcr i H L hLH hG hc

/-! ## `S3` at span six -/

/-- **`S3` at every span up to six.** The first span at which the crookedness is indispensable
(`not_near_extreme_three`), settled. -/
theorem s3_span_six {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 6) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i
  · exact s3_near_extreme ρ i H L hlip hLb hHb hLH hnear
  · push_neg at hnear
    obtain ⟨hlow, hhigh⟩ := hnear
    have hi := i.isLt
    have hHeq : H = L + 6 := by omega
    have hpi : ρ i = L + 3 := by omega
    have hmG : 0 < n - i.val := by omega
    have hmT : 0 < i.val + 1 := by omega
    have hG0 : armG ρ i ⟨0, hmG⟩ = L + 3 := by
      show ρ ⟨i.val + 0, _⟩ = L + 3
      rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
      exact hpi
    have hT0 : armT ρ i ⟨0, hmT⟩ = L + 3 := by
      show ρ ⟨i.val - 0, _⟩ = L + 3
      rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
      exact hpi
    have hGL : ∀ j, L ≤ armG ρ i j := fun j => hLb _
    have hGH : ∀ j, armG ρ i j ≤ L + 6 := by
      intro j
      have hj := j.isLt
      have h := hHb (⟨i.val + j.val, by omega⟩ : Fin n)
      have e : armG ρ i j = ρ (⟨i.val + j.val, by omega⟩ : Fin n) := rfl
      omega
    have hTL : ∀ j, L ≤ armT ρ i j := fun j => hLb _
    have hTH : ∀ j, armT ρ i j ≤ L + 6 := by
      intro j
      have hj := j.isLt
      have h := hHb (⟨i.val - j.val, by omega⟩ : Fin n)
      have e : armT ρ i j = ρ (⟨i.val - j.val, by omega⟩ : Fin n) := rfl
      omega
    rcases span6_dichotomy hcr i H L hLH with ⟨hg, ht⟩ | ⟨hg, ht⟩
    · rw [hHeq] at hg ht
      exact ⟨8, walk6 L,
        foldsOnto_walk6_of_lowLate hmG _ (armG_isLip hlip i) L hG0 hGL hGH hg,
        foldsOnto_walk6_of_lowLate hmT _ (armT_isLip hlip i) L hT0 hTL hTH ht⟩
    · rw [hHeq] at hg ht
      exact ⟨8, walk6' L,
        foldsOnto_walk6'_of_highLate hmG _ (armG_isLip hlip i) L hG0 hGL hGH hg,
        foldsOnto_walk6'_of_highLate hmT _ (armT_isLip hlip i) L hT0 hTL hTH ht⟩

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, for a crooked chain whose links
run through at most seven consecutive links of `D`. -/
theorem theorem3_span_six {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D)
    (hspan : ∀ t t' : Fin n, ((hcr.1.minIdx t : ℕ) : ℤ) ≤ ((hcr.1.minIdx t' : ℕ) : ℤ) + 6)
    (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  set σ : Fin n → ℤ := fun t => ((href.maxIdx t : ℕ) : ℤ) with hσ
  obtain ⟨tL, -, htL⟩ := Finset.exists_min_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  obtain ⟨tH, -, htH⟩ := Finset.exists_max_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  set L : ℤ := ρ tL with hL
  set H : ℤ := ρ tH with hH
  have hLf : ∀ t, L ≤ ρ t := fun t => htL t (Finset.mem_univ t)
  have hHf : ∀ t, ρ t ≤ H := fun t => htH t (Finset.mem_univ t)
  by_cases hdeg : H ≤ L + 2
  · refine exists_blocks_first_of_range_le_two hn href i (href.minIdx tL).val (fun t => ?_)
    have h1 := hLf t
    have h2 := hHf t
    simp only [hρ, hL, hH] at h1 h2 hdeg
    omega
  · have hcase : L + 3 ≤ H := by omega
    have hsix : H ≤ L + 6 := hspan tH tL
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedIvF ρ σ := isCrookedIvF_minIdx_maxIdx hcr
    obtain ⟨len, c, hG, hT⟩ := s3_span_six ρ σ i H L hlip hcrook hLf hHf hcase hsix
    exact exists_blocks_first_of_folds href i _ _ hG hT

end HPC.Fold
