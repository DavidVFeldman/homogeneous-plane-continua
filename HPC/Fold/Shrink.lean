import HPC.Fold.ExitReach

/-!
# Shrinking the valley conjectures to their non-vacuous cores

`HighExitValley` asks that an arm which exceeds `hStar + 1` after its peak index has visited
`L + 1` in between. When the cap in `hStar` binds — `hStar = max (H − 1) p` — no arm can exceed
`hStar + 1 = H` at all, and the clause is vacuous. In the down-form corpus the cap binds at
99.97 % of basepoints; the clause has bite at 452 arm-instances in three million.

This file proves the vacuity, proves two structural facts about the non-vacuous case, and
restates the conjecture restricted to that case. `LowExitPeak` is handled by the same three
statements reflected — sound here because reflection is applied only to definitions and to
lemmas with no crookedness anywhere beneath them (batch 16 §4).

English proofs: COMMISSION-batch17.md §3. Delivered complete: no `sorry` remains.

Two remarks on the delivery. In `demands_lt_of_open` the ambient hypotheses `hHρ`, `hLρ` and
`hrange` turn out to be unnecessary — the conclusion follows from `hopen` alone, by the
arithmetic of `min`/`max` — and they are kept as commissioned. In `pre_drop_eq` the hypothesis
`hd'` is read, as commissioned, as `d'` being the immediate predecessor of `d`.
-/

namespace HPC.Fold

variable {m : ℕ} {A : Fin m → ℤ}

/-- When the cap binds, the valley clause is vacuous: nothing exceeds `H ≤ h + 1`. -/
theorem valleyBefore_of_cap (H L h : ℤ) (hHA : ∀ j, A j ≤ H) (hcap : H - 1 ≤ h) (s : ℕ) :
    ValleyBefore A L h s := by
  intro u _ hu
  have := hHA u
  omega

/-- An arm that exceeds `h + 1 ≥ hStarArm + 1` does so only after its first drop: the index
lies outside the prefix on which `hStarArm` is the maximum. -/
theorem exists_drop_before_exceed (hm : 0 < m) (p h : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hdem : hStarArm A p ≤ h) (u : Fin m) (hu : h + 1 < A u) :
    ∃ d : Fin m, d < u ∧ A d ≤ p - 2 ∧ ∀ j : Fin m, j < d → p - 1 ≤ A j := by
  classical
  have hp : p ≤ h := le_trans (le_hStarArm hm A p h0) hdem
  -- some index at or before `u` drops
  have hex : ∃ j : Fin m, j.val ≤ u.val ∧ A j ≤ p - 2 := by
    by_contra hcon
    push_neg at hcon
    have hwin : ∀ j' : Fin m, j' ≤ u → p - 1 ≤ A j' := by
      intro j' hj'
      have := hcon j' (Fin.le_def.1 hj')
      omega
    have := le_hStarArm_of_window A p u hwin
    omega
  obtain ⟨d, ⟨hdu, hdA⟩, hdmin⟩ :=
    exists_least_index (fun j : Fin m => j.val ≤ u.val ∧ A j ≤ p - 2) hex
  have hdne : d.val ≠ u.val := by
    intro hcon
    have : A d = A u := by rw [Fin.ext (show d.val = u.val from hcon)]
    omega
  refine ⟨d, Fin.lt_def.2 (by omega), hdA, fun j hj => ?_⟩
  have hjd : j.val < d.val := Fin.lt_def.1 hj
  by_contra hcon
  exact hdmin j hjd ⟨by omega, by omega⟩

/-- Just before its first drop an arm stands at exactly `p − 1`. -/
theorem pre_drop_eq (hA : IsLip A) (p : ℤ) (d : Fin m) (hd : A d ≤ p - 2)
    (hpre : ∀ j : Fin m, j < d → p - 1 ≤ A j) (d' : Fin m) (hd' : d'.val + 1 = d.val) :
    A d' = p - 1 := by
  have hlow : p - 1 ≤ A d' := hpre d' (Fin.lt_def.2 (by omega))
  have hlip : |A d - A d'| ≤ 1 := hA d' d hd'.symm
  rw [abs_le] at hlip
  omega

/-- **The non-vacuous core.** `HighExitValley` restricted to basepoints where the cap does not
bind — both arms' demands, `p`, and `L + 1` all below `H − 1`. -/
def HighExitValleyOpen : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    hStar ρ i H L < max (H - 1) (ρ i) →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        armG ρ i j + phase (armG ρ i) j < hStar ρ i H L) →
      ValleyBefore (armG ρ i) L (hStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        armT ρ i j + phase (armT ρ i) j < hStar ρ i H L) →
      ValleyBefore (armT ρ i) L (hStar ρ i H L) s)

/-- The restriction loses nothing. -/
theorem highExitValley_iff_open : HighExitValley ↔ HighExitValleyOpen := by
  constructor
  · intro hHEV n ρ i H L hLip hCr hL hH hrange _
    exact hHEV n ρ i H L hLip hCr hL hH hrange
  · intro hOpen n ρ i H L hLip hCr hL hH hrange
    by_cases hopen : hStar ρ i H L < max (H - 1) (ρ i)
    · exact hOpen n ρ i H L hLip hCr hL hH hrange hopen
    · push_neg at hopen
      have hcap : H - 1 ≤ hStar ρ i H L :=
        le_trans (le_max_left _ _) hopen
      refine ⟨fun s _ => ?_, fun s _ => ?_⟩
      · exact valleyBefore_of_cap H L _ (fun j => hH _) hcap s
      · exact valleyBefore_of_cap H L _ (fun j => hH _) hcap s

/-- In the non-vacuous case both demands sit strictly below `H − 1`: neither arm reaches
`H − 1` before its first drop, although `H` is attained somewhere.

The ambient hypotheses `hHρ`, `hLρ` and `hrange` are unnecessary and are kept as
commissioned. -/
theorem demands_lt_of_open {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (_hHρ : ∀ t, ρ t ≤ H) (_hLρ : ∀ t, L ≤ ρ t) (_hrange : L + 3 ≤ H)
    (hopen : hStar ρ i H L < max (H - 1) (ρ i)) :
    hStarArm (armG ρ i) (ρ i) < H - 1 ∧ hStarArm (armT ρ i) (ρ i) < H - 1 ∧ ρ i < H - 1 := by
  rw [hStar] at hopen
  have h1 : min (max (max (hStarArm (armG ρ i) (ρ i)) (hStarArm (armT ρ i) (ρ i)))
      (max (ρ i) (L + 1))) (max (H - 1) (ρ i)) =
      max (max (hStarArm (armG ρ i) (ρ i)) (hStarArm (armT ρ i) (ρ i))) (max (ρ i) (L + 1)) := by
    rcases min_cases (max (max (hStarArm (armG ρ i) (ρ i)) (hStarArm (armT ρ i) (ρ i)))
      (max (ρ i) (L + 1))) (max (H - 1) (ρ i)) with ⟨he, -⟩ | ⟨he, -⟩
    · exact he
    · rw [he] at hopen; omega
  rw [h1] at hopen
  have hG : hStarArm (armG ρ i) (ρ i) ≤
      max (max (hStarArm (armG ρ i) (ρ i)) (hStarArm (armT ρ i) (ρ i))) (max (ρ i) (L + 1)) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hT : hStarArm (armT ρ i) (ρ i) ≤
      max (max (hStarArm (armG ρ i) (ρ i)) (hStarArm (armT ρ i) (ρ i))) (max (ρ i) (L + 1)) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hp : ρ i ≤
      max (max (hStarArm (armG ρ i) (ρ i)) (hStarArm (armT ρ i) (ρ i))) (max (ρ i) (L + 1)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hmax : max (H - 1) (ρ i) = H - 1 ∨ max (H - 1) (ρ i) = ρ i := max_choice _ _
  rcases hmax with he | he <;> rw [he] at hopen <;> omega

end HPC.Fold
