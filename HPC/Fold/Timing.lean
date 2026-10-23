import HPC.Fold.Minimal
import HPC.Fold.CrossArm
import HPC.Fold.General

/-!
# The timing law of Theorem 7, on arms

`minGap` (`HPC/Fold/Minimal.lean`, batch 30) says: if one link of a faithful crooked sequence
meets level `l` and another, distinct, link meets level `l + d`, the sequence has at least `z d`
links, where `z` is Bing's recurrence (`HPC/Fold/OffCenter.lean`), `z = 1, 2, 3, 6, 13, 30, …`.
With `isCrookedIvF_restrict` (a window of a faithful crooked sequence is one) this bounds how
fast an arm can move: `d` levels take at least `z d - 1` steps, so three levels take five steps,
four take twelve, five take twenty-nine.

The bounds proved in batch 42 from the one-arm clause `CrookUp` are four, seven and twelve
(`crookUp_climb3`, `crookUp_climb4`, `crookUp_climb5`). The one-arm clause does not see `σ`.

`minGap` needs the two levels exactly `d` apart; for a difference of at least `d` one also needs
`z` monotone, which was not yet in the repository. `z_mono` supplies it, so `armG_three_levels`
and `armT_three_levels` read a difference of *at least* three levels.

The last statement applies this to `s3_span_nine_mid_low_of_lamProfile`, whose index clause
`5 ≤ j` is then implied by the level `L + 7`: an arm of a faithful crooked sequence that stands
three levels above its basepoint does so no earlier than step `z 3 - 1 = 5`.
-/

namespace HPC.Fold

/-! ## `z` is monotone -/

/-- Two consecutive steps of the recurrence, for the induction. -/
theorem z_mono_aux : ∀ m : ℕ, z m ≤ z (m + 1) ∧ z (m + 1) ≤ z (m + 2)
  | 0 => ⟨by decide, by decide⟩
  | m + 1 => by
      obtain ⟨h1, h2⟩ := z_mono_aux m
      refine ⟨h2, ?_⟩
      have h3 := z_pos (m + 1)
      have h4 := z_pos (m + 2)
      have he : z (m + 3) = 2 * z (m + 2) + z (m + 1) - 2 := rfl
      show z (m + 2) ≤ z (m + 3)
      omega

/-- Bing's recurrence is monotone. Needed to turn a gap of *at least* `d` levels into the
bound `z d`. -/
theorem z_mono {a b : ℕ} (h : a ≤ b) : z a ≤ z b := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst this; exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge a (k + 1) with h' | h'
      · exact le_trans (ih (by omega)) (z_mono_aux k).1
      · have : a = k + 1 := by omega
        subst this; exact le_rfl

/-! ## Timing on the two arms -/

/-- **Timing on the forward arm.** If the forward arm from `i` stands at two levels exactly `d`
apart at steps `s < t`, then `z d ≤ t - s + 1`: the window between them is itself a faithful
crooked sequence, and `minGap` counts its links. -/
theorem armG_gap {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (s t : Fin (n - i.val)) (hst : s.val < t.val) (d : ℕ)
    (hd : armG ρ i s + d = armG ρ i t ∨ armG ρ i t + d = armG ρ i s) :
    z d ≤ t.val - s.val + 1 := by
  have hi := i.isLt
  have hsn := s.isLt
  have htn := t.isLt
  have hab : i.val + s.val ≤ i.val + t.val := by omega
  have hbn : i.val + t.val < n := by omega
  have hrestr := isCrookedIvF_restrict hcr (i.val + s.val) (i.val + t.val) hab hbn
  set m : ℕ := i.val + t.val - (i.val + s.val) with hm
  have hmpos : 0 < m := by omega
  have hne : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨m, by omega⟩ := by
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega
  -- the two endpoints of the window, as links of the ambient sequence
  have hS : (⟨i.val + s.val + (0 : ℕ), by omega⟩ : Fin n) = ⟨i.val + s.val, by omega⟩ :=
    Fin.ext (by simp)
  have hT : (⟨i.val + s.val + m, by omega⟩ : Fin n) = ⟨i.val + t.val, by omega⟩ :=
    Fin.ext (by simp; omega)
  have hGs : armG ρ i s = ρ (⟨i.val + s.val, by omega⟩ : Fin n) := rfl
  have hGt : armG ρ i t = ρ (⟨i.val + t.val, by omega⟩ : Fin n) := rfl
  have hles : ρ (⟨i.val + s.val, by omega⟩ : Fin n) ≤ σ ⟨i.val + s.val, by omega⟩ := hcr.le _
  have hlet : ρ (⟨i.val + t.val, by omega⟩ : Fin n) ≤ σ ⟨i.val + t.val, by omega⟩ := hcr.le _
  have key : z d ≤ m + 1 := by
    rcases hd with h | h
    · refine minGap d hrestr ⟨0, by omega⟩ ⟨m, by omega⟩ (armG ρ i s) ?_ ?_ ?_ ?_ hne
      · simp only [hS]; exact le_of_eq hGs.symm
      · simp only [hS]; rw [hGs]; exact hles
      · simp only [hT]; rw [← hGt]; omega
      · simp only [hT]; rw [show armG ρ i s + (d : ℤ) = armG ρ i t from h, hGt]; exact hlet
    · refine minGap d hrestr ⟨m, by omega⟩ ⟨0, by omega⟩ (armG ρ i t) ?_ ?_ ?_ ?_ (Ne.symm hne)
      · simp only [hT]; exact le_of_eq hGt.symm
      · simp only [hT]; rw [hGt]; exact hlet
      · simp only [hS]; rw [← hGs]; omega
      · simp only [hS]; rw [show armG ρ i t + (d : ℤ) = armG ρ i s from h, hGs]; exact hles
  omega

/-- **Timing on the backward arm.** -/
theorem armT_gap {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (s t : Fin (i.val + 1)) (hst : s.val < t.val) (d : ℕ)
    (hd : armT ρ i s + d = armT ρ i t ∨ armT ρ i t + d = armT ρ i s) :
    z d ≤ t.val - s.val + 1 := by
  have hi := i.isLt
  have hsn := s.isLt
  have htn := t.isLt
  have hab : i.val - t.val ≤ i.val - s.val := by omega
  have hbn : i.val - s.val < n := by omega
  have hrestr := isCrookedIvF_restrict hcr (i.val - t.val) (i.val - s.val) hab hbn
  set m : ℕ := i.val - s.val - (i.val - t.val) with hm
  have hmpos : 0 < m := by omega
  have hne : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨m, by omega⟩ := by
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega
  have hS : (⟨i.val - t.val + (0 : ℕ), by omega⟩ : Fin n) = ⟨i.val - t.val, by omega⟩ :=
    Fin.ext (by simp)
  have hT : (⟨i.val - t.val + m, by omega⟩ : Fin n) = ⟨i.val - s.val, by omega⟩ :=
    Fin.ext (by simp; omega)
  have hGs : armT ρ i s = ρ (⟨i.val - s.val, by omega⟩ : Fin n) := rfl
  have hGt : armT ρ i t = ρ (⟨i.val - t.val, by omega⟩ : Fin n) := rfl
  have hles : ρ (⟨i.val - s.val, by omega⟩ : Fin n) ≤ σ ⟨i.val - s.val, by omega⟩ := hcr.le _
  have hlet : ρ (⟨i.val - t.val, by omega⟩ : Fin n) ≤ σ ⟨i.val - t.val, by omega⟩ := hcr.le _
  have key : z d ≤ m + 1 := by
    rcases hd with h | h
    · refine minGap d hrestr ⟨m, by omega⟩ ⟨0, by omega⟩ (armT ρ i s) ?_ ?_ ?_ ?_ (Ne.symm hne)
      · simp only [hT]; exact le_of_eq hGs.symm
      · simp only [hT]; rw [hGs]; exact hles
      · simp only [hS]; rw [← hGt]; omega
      · simp only [hS]; rw [show armT ρ i s + (d : ℤ) = armT ρ i t from h, hGt]; exact hlet
    · refine minGap d hrestr ⟨0, by omega⟩ ⟨m, by omega⟩ (armT ρ i t) ?_ ?_ ?_ ?_ hne
      · simp only [hS]; exact le_of_eq hGt.symm
      · simp only [hS]; rw [hGt]; exact hlet
      · simp only [hT]; rw [← hGs]; omega
      · simp only [hT]; rw [show armT ρ i t + (d : ℤ) = armT ρ i s from h, hGs]; exact hles
  omega

/-- A forward arm that rises three levels above its basepoint does so no earlier than step
five: `z 3 = 6`. -/
theorem armG_three_levels {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (j : Fin (n - i.val)) (h : ρ i + 3 ≤ armG ρ i j) : 5 ≤ j.val := by
  have hi := i.isLt
  have hj := j.isLt
  have h0 : armG ρ i ⟨0, by omega⟩ = ρ i := by
    show ρ ⟨i.val + 0, by omega⟩ = ρ i
    congr 1
  have hjpos : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with hz | hp
    · exfalso
      have : j = (⟨0, by omega⟩ : Fin (n - i.val)) := Fin.ext (by simp [hz])
      rw [this, h0] at h
      omega
    · exact hp
  set D : ℕ := (armG ρ i j - ρ i).toNat with hD
  have hDeq : (D : ℤ) = armG ρ i j - ρ i := Int.toNat_of_nonneg (by omega)
  have hD3 : 3 ≤ D := by omega
  have hgap := armG_gap hcr i ⟨0, by omega⟩ j (by simpa using hjpos) D
    (Or.inl (by rw [h0]; omega))
  have hz3 : z 3 = 6 := by decide
  have := z_mono hD3
  simp only at hgap
  omega

/-- A backward arm that rises three levels above its basepoint does so no earlier than step
five. -/
theorem armT_three_levels {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (j : Fin (i.val + 1)) (h : ρ i + 3 ≤ armT ρ i j) : 5 ≤ j.val := by
  have hi := i.isLt
  have hj := j.isLt
  have h0 : armT ρ i ⟨0, by omega⟩ = ρ i := by
    show ρ ⟨i.val - 0, by omega⟩ = ρ i
    congr 1
  have hjpos : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with hz | hp
    · exfalso
      have : j = (⟨0, by omega⟩ : Fin (i.val + 1)) := Fin.ext (by simp [hz])
      rw [this, h0] at h
      omega
    · exact hp
  set D : ℕ := (armT ρ i j - ρ i).toNat with hD
  have hDeq : (D : ℤ) = armT ρ i j - ρ i := Int.toNat_of_nonneg (by omega)
  have hD3 : 3 ≤ D := by omega
  have hgap := armT_gap hcr i ⟨0, by omega⟩ j (by simpa using hjpos) D
    (Or.inl (by rw [h0]; omega))
  have hz3 : z 3 = 6 := by decide
  have := z_mono hD3
  simp only at hgap
  omega

/-- **The Λ-criterion at the branch `L + 4`, without its index clause.** Served if each arm
stands at `L + 7` before it ever drops to `L + 1`. -/
theorem s3_span_nine_mid_low_of_lam {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 4)
    (hG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ L + 7 ≤ armG ρ i j)
    (hT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ L + 7 ≤ armT ρ i j) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  refine s3_span_nine_mid_low_of_lamProfile ρ i H L hlip hLb hHb hH hp ?_ ?_
  · intro d hd
    obtain ⟨j, hj1, hj2⟩ := hG d hd
    exact ⟨j, hj1, armG_three_levels hcr i j (by omega), hj2⟩
  · intro d hd
    obtain ⟨j, hj1, hj2⟩ := hT d hd
    exact ⟨j, hj1, armT_three_levels hcr i j (by omega), hj2⟩

end HPC.Fold
