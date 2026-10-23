import HPC.Fold.Pair79Fold

/-!
# Batch 79: the folds with a fake end link, start of the walk chosen

`fold_low_end_mode` is `B78.fold_low_end` in which the walk starts at `S 0 - 1` or `S 0 + 1` as
chosen (under the corresponding first-direction condition), and which also reports that the arm
indices next to the basepoint whose values stay within one of the start are at time `0`.
`fold_high_end_mode` is the same with a fake link at the top level `Hb` appended instead of one
at level `0`; it is what the fold read on the greatest coarse indices needs.
-/

namespace HPC.Fold.B79

open Z77

/-- The sequence with a fake link at level `0` appended after position `q`. -/
def lowExt (S : ℤ → ℤ) (q : ℕ) (x : ℤ) : ℤ := if x = (q : ℤ) + 1 then 0 else S x

/-- The sequence with a fake link at level `Hb` appended after position `q`. -/
def highExt (S : ℤ → ℤ) (q : ℕ) (Hb : ℤ) (x : ℤ) : ℤ := if x = (q : ℤ) + 1 then Hb else S x

/-- The arm lengths of the extended sequence. -/
def extM (p q : ℕ) (e : Bool) : ℕ := if e then q + 2 else p + 1

/-- **The fold with a fake low end, start chosen.** -/
theorem fold_low_end_mode (S : ℤ → ℤ) (p q : ℕ) (Hb : ℤ)
    (hcr : CrkOn S (-(p : ℤ)) q)
    (hlip : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → |S (x + 1) - S x| ≤ 1)
    (hnn : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → 0 ≤ S x)
    (hH : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → S x ≤ Hb)
    (hend : S q ≤ 1)
    (hmeet : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → 3 ≤ S x →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ S y ≤ 1 ∧ S x - 2 ≤ S y' ∧ S y' ≤ S x - 1)
    (above : Bool)
    (hok : if above then OKAbove (lowExt S q) (extM p q) else OKBelow (lowExt S q) (extM p q)) :
    ∃ (c : ℕ → ℤ) (βR βL : ℕ → ℕ) (U : ℕ),
      βR 0 = 0 ∧ βL 0 = 0 ∧
      (∀ j, j < q → |((βR (j + 1) : ℕ) : ℤ) - ((βR j : ℕ) : ℤ)| ≤ 1) ∧
      (∀ j, j < p → |((βL (j + 1) : ℕ) : ℤ) - ((βL j : ℕ) : ℤ)| ≤ 1) ∧
      (∀ j : ℕ, j ≤ q → |S j - c (βR j)| ≤ 1) ∧
      (∀ j : ℕ, j ≤ p → |S (-(j : ℤ)) - c (βL j)| ≤ 1) ∧
      |(U : ℤ) - ((βR q : ℕ) : ℤ)| ≤ 1 ∧ c U ≤ 1 ∧
      c 0 = S 0 + (if above then 1 else -1) ∧
      (∀ j : ℕ, j ≤ q → (∀ i : ℕ, i ≤ j → |S i - c 0| ≤ 1) → βR j = 0) ∧
      (∀ j : ℕ, j ≤ p → (∀ i : ℕ, i ≤ j → |S (-(i : ℤ)) - c 0| ≤ 1) → βL j = 0) ∧
      (q = 0 → |c 0| ≤ 1 → U = 0) := by
  classical
  set S' : ℤ → ℤ := lowExt S q with hS'
  have hS'eq : ∀ x : ℤ, x ≤ q → S' x = S x := by
    intro x hx; simp only [hS', lowExt]; rw [if_neg (by omega)]
  have hS'q1 : S' ((q : ℤ) + 1) = 0 := by simp [hS', lowExt]
  set M : Bool → ℕ := extM p q with hMdef
  have hcr' : CrkOn S' (1 - M false) (M true - 1) := by
    have e1 : (1 : ℤ) - ((M false : ℕ) : ℤ) = -(p : ℤ) := by simp [hMdef, extM]
    have e2 : ((M true : ℕ) : ℤ) - 1 = (q : ℤ) + 1 := by simp [hMdef, extM]; ring
    rw [e1, e2]
    intro s t hs hst ht
    rcases lt_or_eq_of_le ht with ht' | ht'
    · have ht'' : t ≤ q := by omega
      obtain ⟨h1, h2⟩ := hcr s t hs hst ht''
      rw [hS'eq s (by omega), hS'eq t ht'']
      constructor
      · intro h
        obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h1 h
        exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
          by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
          by rw [hS'eq r' (by omega)]; exact a7⟩
      · intro h
        obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h2 h
        exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
          by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
          by rw [hS'eq r' (by omega)]; exact a7⟩
    · subst ht'
      rw [hS'eq s (by omega), hS'q1]
      have hs0 := hnn s hs (by omega)
      constructor
      · intro h; omega
      · intro h
        have hsq : s < q := by
          rcases lt_or_eq_of_le (show s ≤ q by omega) with h' | h'
          · exact h'
          · subst h'; omega
        obtain ⟨y, y', a1, a2, a3, a4, a5, a6⟩ := hmeet s hs hsq (by omega)
        have hy0 := hnn y (by omega) (by omega)
        refine ⟨y, y', a1, a2, by omega, ?_, ?_, ?_, ?_⟩
        · rw [hS'eq y (by omega)]; exact hy0
        · rw [hS'eq y (by omega)]; omega
        · rw [hS'eq y' (by omega)]; exact a5
        · rw [hS'eq y' (by omega)]; exact a6
  have harmT : ∀ j : ℕ, arm S' true j = S' j := fun j => by simp [arm]
  have harmF : ∀ j : ℕ, arm S' false j = S' (-(j : ℤ)) := fun j => by simp [arm]
  have hlipA : ∀ e, LipOn (arm S' e) (M e) := by
    intro e j hj
    cases e
    · simp only [hMdef, extM, Bool.false_eq_true, if_false] at hj
      rw [harmF, harmF, hS'eq _ (by omega), hS'eq _ (by omega), abs_sub_comm]
      have := hlip (-((j + 1 : ℕ) : ℤ)) (by push_cast; omega) (by push_cast; omega)
      push_cast at this ⊢
      rw [show -((j : ℤ) + 1) + 1 = -(j : ℤ) by ring] at this
      exact this
    · simp only [hMdef, extM, if_true] at hj
      rw [harmT, harmT]
      rcases lt_or_eq_of_le (show j ≤ q by omega) with hjq | hjq
      · rw [hS'eq _ (by push_cast; omega), hS'eq _ (by omega)]
        have := hlip (j : ℤ) (by omega) (by exact_mod_cast hjq)
        push_cast; exact this
      · rw [hjq]
        push_cast
        rw [hS'q1, hS'eq _ le_rfl]
        have := hnn q (by omega) le_rfl
        rw [abs_le]; constructor <;> omega
  have hHb : 0 ≤ Hb := le_trans (hnn 0 (by omega) (by omega)) (hH 0 (by omega) (by omega))
  have hLA : ∀ e j, j < M e → (0 : ℤ) ≤ arm S' e j := by
    intro e j hj
    cases e
    · simp only [hMdef, extM, Bool.false_eq_true, if_false] at hj
      rw [harmF, hS'eq _ (by omega)]; exact hnn _ (by omega) (by omega)
    · simp only [hMdef, extM, if_true] at hj
      rw [harmT]
      rcases lt_or_eq_of_le (show j ≤ q + 1 by omega) with hjq | hjq
      · rw [hS'eq _ (by omega)]; exact hnn _ (by omega) (by omega)
      · rw [hjq]; push_cast; rw [hS'q1]
  have hHA : ∀ e j, j < M e → arm S' e j ≤ Hb := by
    intro e j hj
    cases e
    · simp only [hMdef, extM, Bool.false_eq_true, if_false] at hj
      rw [harmF, hS'eq _ (by omega)]; exact hH _ (by omega) (by omega)
    · simp only [hMdef, extM, if_true] at hj
      rw [harmT]
      rcases lt_or_eq_of_le (show j ≤ q + 1 by omega) with hjq | hjq
      · rw [hS'eq _ (by omega)]; exact hH _ (by omega) (by omega)
      · rw [hjq]; push_cast; rw [hS'q1]; exact hHb
  have hM : ∀ e, 0 < M e := by intro e; cases e <;> simp [hMdef, extM]
  have hS'0 : S' 0 = S 0 := hS'eq 0 (by omega)
  set T0 : ℤ := S 0 + (if above then 1 else -1) with hT0def
  obtain ⟨ts, hfit⟩ : ∃ ts : List ℤ, ∀ e, Fit (arm S' e) (M e) 0 T0 ts := by
    cases above
    · simp only [Bool.false_eq_true, if_false] at hok
      obtain ⟨ts, h⟩ := greedy_fit_below hcr' hlipA hLA hHA hM hok
      refine ⟨ts, fun e => ?_⟩
      have := h e; rw [hS'0] at this; simpa [hT0def, sub_eq_add_neg] using this
    · simp only [if_true] at hok
      obtain ⟨ts, h⟩ := greedy_fit_above hcr' hlipA hLA hHA hM hok
      refine ⟨ts, fun e => ?_⟩
      have := h e; rw [hS'0] at this; simpa [hT0def] using this
  have hT0 : |S 0 - T0| ≤ 1 := by
    simp only [hT0def]; cases above <;> simp
  have hfold : ∀ e, ∃ β : ℕ → ℕ, β 0 = 0 ∧ (∀ j, 0 ≤ j → j < M e → β j < jlen T0 ts) ∧
      (∀ j, 0 ≤ j → j + 1 < M e → |((β (j + 1) : ℕ) : ℤ) - ((β j : ℕ) : ℤ)| ≤ 1) ∧
      (∀ j, 0 ≤ j → j < M e → |arm S' e j - jwalk T0 ts (β j)| ≤ 1) ∧
      (∀ j, 0 ≤ j → j < M e → (∀ i, 0 ≤ i → i ≤ j → |arm S' e i - T0| ≤ 1) → β j = 0) :=
    fun e => fold_of_fit_zero (hlipA e) ts 0 T0 (hfit e)
      (by rw [arm_zero, hS'0]; exact hT0)
  obtain ⟨βT, a1, -, a3, a4, a5⟩ := hfold true
  obtain ⟨βF, b1, -, b3, b4, b5⟩ := hfold false
  have hc0 : jwalk T0 ts 0 = T0 := jwalk_zero T0 ts
  refine ⟨jwalk T0 ts, βT, βF, βT (q + 1), a1, b1, ?_, ?_, ?_, ?_, ?_, ?_, hc0, ?_, ?_, ?_⟩
  · intro j hj; exact a3 j (Nat.zero_le _) (by simp [hMdef, extM]; omega)
  · intro j hj; exact b3 j (Nat.zero_le _) (by simp [hMdef, extM]; omega)
  · intro j hj
    have := a4 j (Nat.zero_le _) (by simp [hMdef, extM]; omega)
    rwa [harmT, hS'eq _ (by exact_mod_cast hj)] at this
  · intro j hj
    have := b4 j (Nat.zero_le _) (by simp [hMdef, extM]; omega)
    rwa [harmF, hS'eq _ (by omega)] at this
  · have := a3 q (Nat.zero_le _) (by simp [hMdef, extM])
    exact this
  · have := a4 (q + 1) (Nat.zero_le _) (by simp [hMdef, extM])
    rw [harmT] at this
    push_cast at this
    rw [hS'q1, abs_le] at this
    omega
  · intro j hj hall
    refine a5 j (Nat.zero_le _) (by simp [hMdef, extM]; omega) (fun i _ hi => ?_)
    rw [harmT, hS'eq _ (by omega)]
    rw [hc0] at hall
    exact hall i hi
  · intro j hj hall
    refine b5 j (Nat.zero_le _) (by simp [hMdef, extM]; omega) (fun i _ hi => ?_)
    rw [harmF, hS'eq _ (by omega)]
    rw [hc0] at hall
    exact hall i hi
  · intro hq0 hc
    subst hq0
    refine a5 1 (Nat.zero_le _) (by simp [hMdef, extM]) (fun i _ hi => ?_)
    rw [harmT]
    rcases (show i = 0 ∨ i = 1 by omega) with h | h
    · subst h; rw [Nat.cast_zero, hS'0]; exact hT0
    · subst h
      have : S' ((1 : ℕ) : ℤ) = 0 := by simpa using hS'q1
      rw [this]; rw [hc0] at hc; rwa [abs_sub_comm, sub_zero]

/-- **The fold with a fake high end, start chosen.** As `fold_low_end_mode` with a fake link at
level `Hb` appended; the time `U` then has walk value at least `Hb - 1`. -/
theorem fold_high_end_mode (S : ℤ → ℤ) (p q : ℕ) (Hb : ℤ)
    (hcr : CrkOn S (-(p : ℤ)) q)
    (hlip : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → |S (x + 1) - S x| ≤ 1)
    (hnn : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → 0 ≤ S x)
    (hH : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → S x ≤ Hb)
    (hend : Hb - 1 ≤ S q)
    (hmeet : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → S x + 3 ≤ Hb →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ Hb - 2 ≤ S y ∧ S y ≤ Hb - 1 ∧ S x ≤ S y' ∧
        S y' ≤ S x + 1)
    (above : Bool)
    (hok : if above then OKAbove (highExt S q Hb) (extM p q)
      else OKBelow (highExt S q Hb) (extM p q)) :
    ∃ (c : ℕ → ℤ) (βR βL : ℕ → ℕ) (U : ℕ),
      βR 0 = 0 ∧ βL 0 = 0 ∧
      (∀ j, j < q → |((βR (j + 1) : ℕ) : ℤ) - ((βR j : ℕ) : ℤ)| ≤ 1) ∧
      (∀ j, j < p → |((βL (j + 1) : ℕ) : ℤ) - ((βL j : ℕ) : ℤ)| ≤ 1) ∧
      (∀ j : ℕ, j ≤ q → |S j - c (βR j)| ≤ 1) ∧
      (∀ j : ℕ, j ≤ p → |S (-(j : ℤ)) - c (βL j)| ≤ 1) ∧
      |(U : ℤ) - ((βR q : ℕ) : ℤ)| ≤ 1 ∧ Hb - 1 ≤ c U ∧
      c 0 = S 0 + (if above then 1 else -1) ∧
      (∀ j : ℕ, j ≤ q → (∀ i : ℕ, i ≤ j → |S i - c 0| ≤ 1) → βR j = 0) ∧
      (∀ j : ℕ, j ≤ p → (∀ i : ℕ, i ≤ j → |S (-(i : ℤ)) - c 0| ≤ 1) → βL j = 0) := by
  classical
  set S' : ℤ → ℤ := highExt S q Hb with hS'
  have hS'eq : ∀ x : ℤ, x ≤ q → S' x = S x := by
    intro x hx; simp only [hS', highExt]; rw [if_neg (by omega)]
  have hS'q1 : S' ((q : ℤ) + 1) = Hb := by simp [hS', highExt]
  set M : Bool → ℕ := extM p q with hMdef
  have hcr' : CrkOn S' (1 - M false) (M true - 1) := by
    have e1 : (1 : ℤ) - ((M false : ℕ) : ℤ) = -(p : ℤ) := by simp [hMdef, extM]
    have e2 : ((M true : ℕ) : ℤ) - 1 = (q : ℤ) + 1 := by simp [hMdef, extM]; ring
    rw [e1, e2]
    intro s t hs hst ht
    rcases lt_or_eq_of_le ht with ht' | ht'
    · have ht'' : t ≤ q := by omega
      obtain ⟨h1, h2⟩ := hcr s t hs hst ht''
      rw [hS'eq s (by omega), hS'eq t ht'']
      constructor
      · intro h
        obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h1 h
        exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
          by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
          by rw [hS'eq r' (by omega)]; exact a7⟩
      · intro h
        obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h2 h
        exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
          by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
          by rw [hS'eq r' (by omega)]; exact a7⟩
    · subst ht'
      rw [hS'eq s (by omega), hS'q1]
      have hsH := hH s hs (by omega)
      constructor
      · intro h
        have hsq : s < q := by
          rcases lt_or_eq_of_le (show s ≤ q by omega) with h' | h'
          · exact h'
          · subst h'; omega
        obtain ⟨y, y', a1, a2, a3, a4, a5, a6, a7⟩ := hmeet s hs hsq h
        refine ⟨y, y', a1, a2, by omega, ?_, ?_, ?_, ?_⟩
        · rw [hS'eq y (by omega)]; exact a4
        · rw [hS'eq y (by omega)]; exact a5
        · rw [hS'eq y' (by omega)]; exact a6
        · rw [hS'eq y' (by omega)]; exact a7
      · intro h; omega
  have harmT : ∀ j : ℕ, arm S' true j = S' j := fun j => by simp [arm]
  have harmF : ∀ j : ℕ, arm S' false j = S' (-(j : ℤ)) := fun j => by simp [arm]
  have hlipA : ∀ e, LipOn (arm S' e) (M e) := by
    intro e j hj
    cases e
    · simp only [hMdef, extM, Bool.false_eq_true, if_false] at hj
      rw [harmF, harmF, hS'eq _ (by omega), hS'eq _ (by omega), abs_sub_comm]
      have := hlip (-((j + 1 : ℕ) : ℤ)) (by push_cast; omega) (by push_cast; omega)
      push_cast at this ⊢
      rw [show -((j : ℤ) + 1) + 1 = -(j : ℤ) by ring] at this
      exact this
    · simp only [hMdef, extM, if_true] at hj
      rw [harmT, harmT]
      rcases lt_or_eq_of_le (show j ≤ q by omega) with hjq | hjq
      · rw [hS'eq _ (by push_cast; omega), hS'eq _ (by omega)]
        have := hlip (j : ℤ) (by omega) (by exact_mod_cast hjq)
        push_cast; exact this
      · rw [hjq]
        push_cast
        rw [hS'q1, hS'eq _ le_rfl]
        have := hH q (by omega) le_rfl
        rw [abs_le]; constructor <;> omega
  have hHb : 0 ≤ Hb := le_trans (hnn 0 (by omega) (by omega)) (hH 0 (by omega) (by omega))
  have hLA : ∀ e j, j < M e → (0 : ℤ) ≤ arm S' e j := by
    intro e j hj
    cases e
    · simp only [hMdef, extM, Bool.false_eq_true, if_false] at hj
      rw [harmF, hS'eq _ (by omega)]; exact hnn _ (by omega) (by omega)
    · simp only [hMdef, extM, if_true] at hj
      rw [harmT]
      rcases lt_or_eq_of_le (show j ≤ q + 1 by omega) with hjq | hjq
      · rw [hS'eq _ (by omega)]; exact hnn _ (by omega) (by omega)
      · rw [hjq]; push_cast; rw [hS'q1]; exact hHb
  have hHA : ∀ e j, j < M e → arm S' e j ≤ Hb := by
    intro e j hj
    cases e
    · simp only [hMdef, extM, Bool.false_eq_true, if_false] at hj
      rw [harmF, hS'eq _ (by omega)]; exact hH _ (by omega) (by omega)
    · simp only [hMdef, extM, if_true] at hj
      rw [harmT]
      rcases lt_or_eq_of_le (show j ≤ q + 1 by omega) with hjq | hjq
      · rw [hS'eq _ (by omega)]; exact hH _ (by omega) (by omega)
      · rw [hjq]; push_cast; rw [hS'q1]
  have hM : ∀ e, 0 < M e := by intro e; cases e <;> simp [hMdef, extM]
  have hS'0 : S' 0 = S 0 := hS'eq 0 (by omega)
  set T0 : ℤ := S 0 + (if above then 1 else -1) with hT0def
  obtain ⟨ts, hfit⟩ : ∃ ts : List ℤ, ∀ e, Fit (arm S' e) (M e) 0 T0 ts := by
    cases above
    · simp only [Bool.false_eq_true, if_false] at hok
      obtain ⟨ts, h⟩ := greedy_fit_below hcr' hlipA hLA hHA hM hok
      refine ⟨ts, fun e => ?_⟩
      have := h e; rw [hS'0] at this; simpa [hT0def, sub_eq_add_neg] using this
    · simp only [if_true] at hok
      obtain ⟨ts, h⟩ := greedy_fit_above hcr' hlipA hLA hHA hM hok
      refine ⟨ts, fun e => ?_⟩
      have := h e; rw [hS'0] at this; simpa [hT0def] using this
  have hT0 : |S 0 - T0| ≤ 1 := by
    simp only [hT0def]; cases above <;> simp
  have hfold : ∀ e, ∃ β : ℕ → ℕ, β 0 = 0 ∧ (∀ j, 0 ≤ j → j < M e → β j < jlen T0 ts) ∧
      (∀ j, 0 ≤ j → j + 1 < M e → |((β (j + 1) : ℕ) : ℤ) - ((β j : ℕ) : ℤ)| ≤ 1) ∧
      (∀ j, 0 ≤ j → j < M e → |arm S' e j - jwalk T0 ts (β j)| ≤ 1) ∧
      (∀ j, 0 ≤ j → j < M e → (∀ i, 0 ≤ i → i ≤ j → |arm S' e i - T0| ≤ 1) → β j = 0) :=
    fun e => fold_of_fit_zero (hlipA e) ts 0 T0 (hfit e)
      (by rw [arm_zero, hS'0]; exact hT0)
  obtain ⟨βT, a1, -, a3, a4, a5⟩ := hfold true
  obtain ⟨βF, b1, -, b3, b4, b5⟩ := hfold false
  have hc0 : jwalk T0 ts 0 = T0 := jwalk_zero T0 ts
  refine ⟨jwalk T0 ts, βT, βF, βT (q + 1), a1, b1, ?_, ?_, ?_, ?_, ?_, ?_, hc0, ?_, ?_⟩
  · intro j hj; exact a3 j (Nat.zero_le _) (by simp [hMdef, extM]; omega)
  · intro j hj; exact b3 j (Nat.zero_le _) (by simp [hMdef, extM]; omega)
  · intro j hj
    have := a4 j (Nat.zero_le _) (by simp [hMdef, extM]; omega)
    rwa [harmT, hS'eq _ (by exact_mod_cast hj)] at this
  · intro j hj
    have := b4 j (Nat.zero_le _) (by simp [hMdef, extM]; omega)
    rwa [harmF, hS'eq _ (by omega)] at this
  · have := a3 q (Nat.zero_le _) (by simp [hMdef, extM])
    exact this
  · have := a4 (q + 1) (Nat.zero_le _) (by simp [hMdef, extM])
    rw [harmT] at this
    push_cast at this
    rw [hS'q1, abs_le] at this
    omega
  · intro j hj hall
    refine a5 j (Nat.zero_le _) (by simp [hMdef, extM]; omega) (fun i _ hi => ?_)
    rw [harmT, hS'eq _ (by omega)]
    rw [hc0] at hall
    exact hall i hi
  · intro j hj hall
    refine b5 j (Nat.zero_le _) (by simp [hMdef, extM]; omega) (fun i _ hi => ?_)
    rw [harmF, hS'eq _ (by omega)]
    rw [hc0] at hall
    exact hall i hi

end HPC.Fold.B79
