import HPC.Fold.Leg4Crit

/-!
# Refuting a criterion of the wide four-leg engine by a linear scan

Each clause of `Leg4Crit` (`HPC/Fold/Leg4Crit.lean`) says: *for every trigger `d`, one of a
handful of increasing chains of landmarks is completed strictly before `d`.* Deciding such a
clause naively costs a cube in the length of the arm, which is out of reach of the kernel for the
arms the census produces; but a chain of at most three links is recognised by a single left-to-
right scan carrying one flag per link, which costs a *linear* pass.

`chainScan` is that scan and `chainScan_one`, `chainScan_two`, `chainScan_three` say exactly what
its three flags mean. The three lemmas `not_leg4CritG_of_floor`, `not_leg4CritG_of_deep` and
`not_leg4CritG_of_ceil` then refute a criterion from a trigger together with the scans that report
its disjuncts unfinished, and `not_leg4CritG_of_base` refutes it from the base condition alone.

This is what makes the audit of batch 58 feasible: an arm of 175 links is put to the kernel
against all twenty-nine parameter sets of the window, at linear cost each.
-/

namespace HPC.Fold

/-! ## The scan -/

/-- **The scan for an increasing chain of at most three conditions.** After `j` steps the three
flags say: `c₁` has fired; `c₁` then `c₂` have fired in that order; `c₁`, `c₂`, `c₃` have fired in
that order — all strictly before `j`. -/
def chainScan (c₁ c₂ c₃ : ℕ → Bool) : ℕ → Bool × Bool × Bool
  | 0 => (false, false, false)
  | j + 1 =>
      let s := chainScan c₁ c₂ c₃ j
      (s.1 || c₁ j, s.2.1 || (s.1 && c₂ j), s.2.2 || (s.2.1 && c₃ j))

theorem chainScan_one (c₁ c₂ c₃ : ℕ → Bool) (j : ℕ) :
    (chainScan c₁ c₂ c₃ j).1 = true ↔ ∃ k, k < j ∧ c₁ k = true := by
  induction j with
  | zero => simp [chainScan]
  | succ j ih =>
    simp only [chainScan, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, hc⟩ | hc)
      · exact ⟨k, by omega, hc⟩
      · exact ⟨j, by omega, hc⟩
    · rintro ⟨k, hk, hc⟩
      rcases Nat.lt_or_ge k j with h | h
      · exact Or.inl ⟨k, h, hc⟩
      · have : k = j := by omega
        exact Or.inr (this ▸ hc)

theorem chainScan_two (c₁ c₂ c₃ : ℕ → Bool) (j : ℕ) :
    (chainScan c₁ c₂ c₃ j).2.1 = true ↔
      ∃ k k', k < k' ∧ k' < j ∧ c₁ k = true ∧ c₂ k' = true := by
  induction j with
  | zero => simp [chainScan]
  | succ j ih =>
    simp only [chainScan, Bool.or_eq_true, Bool.and_eq_true, ih, chainScan_one]
    constructor
    · rintro (⟨k, k', h1, h2, h3, h4⟩ | ⟨⟨k, hk, hc⟩, hc2⟩)
      · exact ⟨k, k', h1, by omega, h3, h4⟩
      · exact ⟨k, j, hk, by omega, hc, hc2⟩
    · rintro ⟨k, k', h1, h2, h3, h4⟩
      rcases Nat.lt_or_ge k' j with h | h
      · exact Or.inl ⟨k, k', h1, h, h3, h4⟩
      · have hk' : k' = j := by omega
        subst hk'
        exact Or.inr ⟨⟨k, h1, h3⟩, h4⟩

theorem chainScan_three (c₁ c₂ c₃ : ℕ → Bool) (j : ℕ) :
    (chainScan c₁ c₂ c₃ j).2.2 = true ↔
      ∃ k k' k'', k < k' ∧ k' < k'' ∧ k'' < j ∧ c₁ k = true ∧ c₂ k' = true ∧ c₃ k'' = true := by
  induction j with
  | zero => simp [chainScan]
  | succ j ih =>
    simp only [chainScan, Bool.or_eq_true, Bool.and_eq_true, ih, chainScan_two]
    constructor
    · rintro (⟨k, k', k'', h1, h2, h3, h4, h5, h6⟩ | ⟨⟨k, k', h1, h2, h3, h4⟩, hc3⟩)
      · exact ⟨k, k', k'', h1, h2, by omega, h4, h5, h6⟩
      · exact ⟨k, k', j, h1, h2, by omega, h3, h4, hc3⟩
    · rintro ⟨k, k', k'', h1, h2, h3, h4, h5, h6⟩
      rcases Nat.lt_or_ge k'' j with h | h
      · exact Or.inl ⟨k, k', k'', h1, h2, h, h4, h5, h6⟩
      · have hk'' : k'' = j := by omega
        subst hk''
        exact Or.inr ⟨⟨k, k', h1, h2, h4, h5⟩, h6⟩

/-! ## Reading an arm at a natural-number index -/

/-- The value of an arm at a natural-number index, `0` outside its range. -/
def valAt {m : ℕ} (f : Fin m → ℤ) (j : ℕ) : ℤ := if h : j < m then f ⟨j, h⟩ else 0

theorem valAt_coe {m : ℕ} (f : Fin m → ℤ) (k : Fin m) : valAt f k.val = f k := by
  simp [valAt, k.isLt]

/-! ## The three clauses, refuted by their scans -/

/-- The base condition alone refutes the criterion. -/
theorem not_leg4CritG_of_base {m : ℕ} {p lo hi : Fin m → ℤ} {H K M P : ℤ} (d : Fin m)
    (hd : d.val = 0) (h : ¬ (P - 1 ≤ p d ∧ p d ≤ P ∧ p d ≤ K - 1)) :
    ¬ Leg4CritG p lo hi H K M P := fun hc => h (hc.1 d hd)

/-- **The floor announcement fails.** -/
theorem not_leg4CritG_of_floor {m : ℕ} {p lo hi : Fin m → ℤ} {H K M P : ℤ} (d : Fin m)
    (htrig : p d ≤ P - 3)
    (h1 : (chainScan (fun j => decide (K ≤ valAt hi j)) (fun _ => false) (fun _ => false)
             d.val).1 = false)
    (h2 : (chainScan (fun j => decide (valAt lo j ≤ P - 2))
             (fun j => decide (K - 1 ≤ valAt hi j)) (fun _ => false) d.val).2.1 = false) :
    ¬ Leg4CritG p lo hi H K M P := by
  intro hc
  rcases hc.2.1 d htrig with ⟨k, hk, hkv⟩ | ⟨k, k', hkk', hk'd, h3, h4⟩
  · rw [← Bool.not_eq_true] at h1
    exact h1 ((chainScan_one _ _ _ _).2 ⟨k.val, hk, by simp [valAt_coe, hkv]⟩)
  · rw [← Bool.not_eq_true] at h2
    exact h2 ((chainScan_two _ _ _ _).2
      ⟨k.val, k'.val, hkk', hk'd, by simp [valAt_coe, h3], by simp [valAt_coe, h4]⟩)

/-- **The deep-floor announcement fails.** -/
theorem not_leg4CritG_of_deep {m : ℕ} {p lo hi : Fin m → ℤ} {H K M P : ℤ} (d : Fin m)
    (htrig : p d ≤ P - 4)
    (h1 : (chainScan (fun j => decide (K + 2 ≤ valAt hi j)) (fun _ => false) (fun _ => false)
             d.val).1 = false)
    (h2 : (chainScan (fun j => decide (valAt lo j ≤ M - 1))
             (fun j => decide (H - 2 ≤ valAt hi j)) (fun _ => false) d.val).2.1 = false)
    (h3 : (chainScan (fun j => decide (K + 1 ≤ valAt hi j)) (fun j => decide (valAt lo j ≤ M))
             (fun j => decide (H - 2 ≤ valAt hi j)) d.val).2.2 = false) :
    ¬ Leg4CritG p lo hi H K M P := by
  intro hc
  rcases hc.2.2.1 d htrig with ⟨k, hk, hkv⟩ | ⟨k, k', hkk', hk'd, ha, hb⟩ |
    ⟨k, k', k'', h4, h5, h6, ha, hb, hcc⟩
  · rw [← Bool.not_eq_true] at h1
    exact h1 ((chainScan_one _ _ _ _).2 ⟨k.val, hk, by simp [valAt_coe, hkv]⟩)
  · rw [← Bool.not_eq_true] at h2
    exact h2 ((chainScan_two _ _ _ _).2
      ⟨k.val, k'.val, hkk', hk'd, by simp [valAt_coe, ha], by simp [valAt_coe, hb]⟩)
  · rw [← Bool.not_eq_true] at h3
    exact h3 ((chainScan_three _ _ _ _).2
      ⟨k.val, k'.val, k''.val, h4, h5, h6, by simp [valAt_coe, ha], by simp [valAt_coe, hb],
        by simp [valAt_coe, hcc]⟩)

/-- **The ceiling announcement fails.** -/
theorem not_leg4CritG_of_ceil {m : ℕ} {p lo hi : Fin m → ℤ} {H K M P : ℤ} (d : Fin m)
    (htrig : K + 2 ≤ p d)
    (h1 : (chainScan (fun j => decide (valAt lo j ≤ M - 1)) (fun _ => false) (fun _ => false)
             d.val).1 = false)
    (h2 : (chainScan (fun j => decide (K + 1 ≤ valAt hi j))
             (fun j => decide (valAt lo j ≤ M + 1)) (fun _ => false) d.val).2.1 = false)
    (h3 : (chainScan (fun j => decide (valAt lo j ≤ P - 2)) (fun j => decide (K ≤ valAt hi j))
             (fun j => decide (valAt lo j ≤ M + 1)) d.val).2.2 = false) :
    ¬ Leg4CritG p lo hi H K M P := by
  intro hc
  rcases hc.2.2.2 d htrig with ⟨k, hk, hkv⟩ | ⟨k, k', hkk', hk'd, ha, hb⟩ |
    ⟨k, k', k'', h4, h5, h6, ha, hb, hcc⟩
  · rw [← Bool.not_eq_true] at h1
    exact h1 ((chainScan_one _ _ _ _).2 ⟨k.val, hk, by simp [valAt_coe, hkv]⟩)
  · rw [← Bool.not_eq_true] at h2
    exact h2 ((chainScan_two _ _ _ _).2
      ⟨k.val, k'.val, hkk', hk'd, by simp [valAt_coe, ha], by simp [valAt_coe, hb]⟩)
  · rw [← Bool.not_eq_true] at h3
    exact h3 ((chainScan_three _ _ _ _).2
      ⟨k.val, k'.val, k''.val, h4, h5, h6, by simp [valAt_coe, ha], by simp [valAt_coe, hb],
        by simp [valAt_coe, hcc]⟩)

end HPC.Fold
