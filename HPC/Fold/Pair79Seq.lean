import HPC.Fold.Pair79Any

/-!
# Batch 79: the folds with a fake end link, read on a sequence indexed by `Fin n`

`EvUp f i a F` (resp. `EvDown`) is the event which forbids starting the walk just above (resp.
below) the basepoint `i`: one of the two arms of `f` on `[0, a]` (the forward one continued by a
fake link at level `F`) reaches `f i + 3` (resp. `f i - 3`) without going below (resp. above)
`f i` first. `finfold_low` / `finfold_high` are the folds of `Pair79Ends` transported to
`Fin n`.
-/

namespace HPC.Fold.B79

open Z77

variable {n : ℕ}

/-- The event forbidding a start just above `f i`. -/
def EvUp (f : Fin n → ℤ) (i a : Fin n) (F : ℤ) : Prop :=
  (∃ t : Fin n, t ≤ a ∧ f t = f i + 3 ∧
      ∀ t' : Fin n, (i < t' ∧ t' < t) ∨ (t < t' ∧ t' < i) → f i ≤ f t') ∨
    (F = f i + 3 ∧ ∀ t' : Fin n, i ≤ t' → t' ≤ a → f i ≤ f t')

/-- The event forbidding a start just below `f i`. -/
def EvDown (f : Fin n → ℤ) (i a : Fin n) (F : ℤ) : Prop :=
  (∃ t : Fin n, t ≤ a ∧ f t = f i - 3 ∧
      ∀ t' : Fin n, (i < t' ∧ t' < t) ∨ (t < t' ∧ t' < i) → f t' ≤ f i) ∨
    (F = f i - 3 ∧ ∀ t' : Fin n, i ≤ t' → t' ≤ a → f t' ≤ f i)

theorem evUp_reflect (f : Fin n → ℤ) (K : ℤ) (i a : Fin n) (F : ℤ) :
    EvUp (fun t => K - f t) i a (K - F) ↔ EvDown f i a F := by
  unfold EvUp EvDown
  simp only []
  constructor
  · rintro (⟨t, h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨t, h1, by omega, fun t' ht' => by have := h3 t' ht'; omega⟩
    · exact Or.inr ⟨by omega, fun t' a1 a2 => by have := h2 t' a1 a2; omega⟩
  · rintro (⟨t, h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨t, h1, by omega, fun t' ht' => by have := h3 t' ht'; omega⟩
    · exact Or.inr ⟨by omega, fun t' a1 a2 => by have := h2 t' a1 a2; omega⟩

theorem highExt_zero (f : Fin n → ℤ) (i a : Fin n) (F : ℤ) :
    highExt (reindex f i) (a.val - i.val) F 0 = f i := by
  unfold highExt
  rw [if_neg (by omega)]
  have := reindex_fin f i i
  simpa using this

theorem highExt_pos (f : Fin n → ℤ) (i a : Fin n) (hia : i ≤ a) (F : ℤ) (j : ℕ)
    (hj : j ≤ a.val - i.val) :
    highExt (reindex f i) (a.val - i.val) F (j : ℤ) = f ⟨i.val + j, by omega⟩ := by
  unfold highExt
  rw [if_neg (by omega)]
  exact reindex_nat_right f i j (by omega)

theorem highExt_neg (f : Fin n → ℤ) (i a : Fin n) (F : ℤ) (j : ℕ) (hj : j ≤ i.val) :
    highExt (reindex f i) (a.val - i.val) F (-(j : ℤ)) = f ⟨i.val - j, by omega⟩ := by
  unfold highExt
  rw [if_neg (by omega)]
  exact reindex_nat_left f i j (by omega)

theorem okAbove_of_not_evUp (f : Fin n → ℤ) (i a : Fin n) (hia : i ≤ a) (F : ℤ)
    (h : ¬ EvUp f i a F) :
    OKAbove (highExt (reindex f i) (a.val - i.val) F) (extM i.val (a.val - i.val)) := by
  have hia' : i.val ≤ a.val := hia
  have ha := a.isLt
  intro e dr hdr harm hall
  apply h
  rw [highExt_zero f i a] at harm hall
  cases e
  · simp only [extM, Bool.false_eq_true, if_false] at hdr
    simp only [arm, Bool.false_eq_true, if_false] at harm hall
    rw [highExt_neg f i a F dr (by omega)] at harm
    refine Or.inl ⟨⟨i.val - dr, by omega⟩, by rw [Fin.le_def]; simp only; omega, harm, ?_⟩
    rintro t' (⟨a1, a2⟩ | ⟨a1, a2⟩)
    · rw [Fin.lt_def] at a1 a2; simp only at a2; omega
    · rw [Fin.lt_def] at a1 a2; simp only at a1
      have := hall (i.val - t'.val) (by omega)
      rw [highExt_neg f i a F _ (by omega)] at this
      have e : (⟨i.val - (i.val - t'.val), by omega⟩ : Fin n) = t' := Fin.ext (by simp only; omega)
      rwa [e] at this
  · simp only [extM, if_true] at hdr
    simp only [arm, if_true] at harm hall
    rcases lt_or_eq_of_le (show dr ≤ a.val - i.val + 1 by omega) with hd | hd
    · rw [highExt_pos f i a hia F dr (by omega)] at harm
      refine Or.inl ⟨⟨i.val + dr, by omega⟩, by rw [Fin.le_def]; simp only; omega, harm, ?_⟩
      rintro t' (⟨a1, a2⟩ | ⟨a1, a2⟩)
      · rw [Fin.lt_def] at a1 a2; simp only at a2
        have := hall (t'.val - i.val) (by omega)
        rw [highExt_pos f i a hia F _ (by omega)] at this
        have e : (⟨i.val + (t'.val - i.val), by omega⟩ : Fin n) = t' :=
          Fin.ext (by simp only; omega)
        rwa [e] at this
      · rw [Fin.lt_def] at a1 a2; simp only at a1; omega
    · subst hd
      have hF : highExt (reindex f i) (a.val - i.val) F (((a.val - i.val + 1 : ℕ)) : ℤ) = F := by
        unfold highExt; rw [if_pos (by push_cast; ring)]
      rw [hF] at harm
      refine Or.inr ⟨harm, fun t' a1 a2 => ?_⟩
      rw [Fin.le_def] at a1 a2
      have := hall (t'.val - i.val) (by omega)
      rw [highExt_pos f i a hia F _ (by omega)] at this
      have e : (⟨i.val + (t'.val - i.val), by omega⟩ : Fin n) = t' :=
        Fin.ext (by simp only; omega)
      rwa [e] at this

theorem okBelow_of_not_evDown (f : Fin n → ℤ) (i a : Fin n) (hia : i ≤ a) (F : ℤ)
    (h : ¬ EvDown f i a F) :
    OKBelow (highExt (reindex f i) (a.val - i.val) F) (extM i.val (a.val - i.val)) := by
  have hia' : i.val ≤ a.val := hia
  have ha := a.isLt
  intro e dr hdr harm hall
  apply h
  rw [highExt_zero f i a] at harm hall
  cases e
  · simp only [extM, Bool.false_eq_true, if_false] at hdr
    simp only [arm, Bool.false_eq_true, if_false] at harm hall
    rw [highExt_neg f i a F dr (by omega)] at harm
    refine Or.inl ⟨⟨i.val - dr, by omega⟩, by rw [Fin.le_def]; simp only; omega, harm, ?_⟩
    rintro t' (⟨a1, a2⟩ | ⟨a1, a2⟩)
    · rw [Fin.lt_def] at a1 a2; simp only at a2; omega
    · rw [Fin.lt_def] at a1 a2; simp only at a1
      have := hall (i.val - t'.val) (by omega)
      rw [highExt_neg f i a F _ (by omega)] at this
      have e : (⟨i.val - (i.val - t'.val), by omega⟩ : Fin n) = t' := Fin.ext (by simp only; omega)
      rwa [e] at this
  · simp only [extM, if_true] at hdr
    simp only [arm, if_true] at harm hall
    rcases lt_or_eq_of_le (show dr ≤ a.val - i.val + 1 by omega) with hd | hd
    · rw [highExt_pos f i a hia F dr (by omega)] at harm
      refine Or.inl ⟨⟨i.val + dr, by omega⟩, by rw [Fin.le_def]; simp only; omega, harm, ?_⟩
      rintro t' (⟨a1, a2⟩ | ⟨a1, a2⟩)
      · rw [Fin.lt_def] at a1 a2; simp only at a2
        have := hall (t'.val - i.val) (by omega)
        rw [highExt_pos f i a hia F _ (by omega)] at this
        have e : (⟨i.val + (t'.val - i.val), by omega⟩ : Fin n) = t' :=
          Fin.ext (by simp only; omega)
        rwa [e] at this
      · rw [Fin.lt_def] at a1 a2; simp only at a1; omega
    · subst hd
      have hF : highExt (reindex f i) (a.val - i.val) F (((a.val - i.val + 1 : ℕ)) : ℤ) = F := by
        unfold highExt; rw [if_pos (by push_cast; ring)]
      rw [hF] at harm
      refine Or.inr ⟨harm, fun t' a1 a2 => ?_⟩
      rw [Fin.le_def] at a1 a2
      have := hall (t'.val - i.val) (by omega)
      rw [highExt_pos f i a hia F _ (by omega)] at this
      have e : (⟨i.val + (t'.val - i.val), by omega⟩ : Fin n) = t' :=
        Fin.ext (by simp only; omega)
      rwa [e] at this

end HPC.Fold.B79
