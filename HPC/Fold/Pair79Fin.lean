import HPC.Fold.Pair79Seq

/-!
# Batch 79: the folds with a fake end link on a sequence indexed by `Fin n`

`finfold_low` (fake link at level `0` after `a`) and `finfold_high` (fake link at level `Hb`
after `a`) are `fold_low_end_mode` / `fold_high_end_mode` read on `Fin n` from a basepoint `i`,
with the first direction given by the absence of the corresponding event.
-/

namespace HPC.Fold.B79

open Z77

variable {n : ℕ}

/-- Folds of the two arms of `reindex f i`, glued into one schedule on `[0, a]`. -/
theorem transport (f : Fin n → ℤ) (i a : Fin n) (hia : i ≤ a) (c : ℕ → ℤ) (βR βL : ℕ → ℕ)
    (U : ℕ) (h0R : βR 0 = 0) (h0L : βL 0 = 0)
    (hlR : ∀ j, j < a.val - i.val → |((βR (j + 1) : ℕ) : ℤ) - ((βR j : ℕ) : ℤ)| ≤ 1)
    (hlL : ∀ j, j < i.val → |((βL (j + 1) : ℕ) : ℤ) - ((βL j : ℕ) : ℤ)| ≤ 1)
    (hwR : ∀ j : ℕ, j ≤ a.val - i.val → |reindex f i j - c (βR j)| ≤ 1)
    (hwL : ∀ j : ℕ, j ≤ i.val → |reindex f i (-(j : ℤ)) - c (βL j)| ≤ 1)
    (hU : |(U : ℤ) - ((βR (a.val - i.val) : ℕ) : ℤ)| ≤ 1)
    (hc0 : |f i - c 0| ≤ 1)
    (hzR : ∀ j : ℕ, j ≤ a.val - i.val → (∀ i' : ℕ, i' ≤ j → |reindex f i i' - c 0| ≤ 1) →
      βR j = 0)
    (hzL : ∀ j : ℕ, j ≤ i.val → (∀ i' : ℕ, i' ≤ j → |reindex f i (-(i' : ℤ)) - c 0| ≤ 1) →
      βL j = 0) :
    ∃ β : Fin n → ℕ, β i = 0 ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(β t' : ℤ) - β t| ≤ 1) ∧
      (∀ t : Fin n, t ≤ a → |f t - c (β t)| ≤ 1) ∧
      |(U : ℤ) - β a| ≤ 1 ∧
      (∀ t : Fin n, t ≤ a → (t.val + 1 = i.val ∨ t.val = i.val + 1) → |f t - c 0| ≤ 1 →
        β t = 0) := by
  classical
  have hia' : i.val ≤ a.val := hia
  have han := a.isLt
  have hSR : ∀ t : Fin n, i ≤ t → reindex f i ((t.val - i.val : ℕ) : ℤ) = f t := by
    intro t hit
    rw [Fin.le_def] at hit
    rw [reindex_nat_right f i _ (by have := t.isLt; omega)]
    exact congrArg f (Fin.ext (by simp only; omega))
  have hSL : ∀ t : Fin n, t < i → reindex f i (-((i.val - t.val : ℕ) : ℤ)) = f t := by
    intro t hti
    rw [Fin.lt_def] at hti
    rw [reindex_nat_left f i _ (by omega)]
    exact congrArg f (Fin.ext (by simp only; omega))
  have hS0 : reindex f i 0 = f i := by simpa using reindex_fin f i i
  refine ⟨fun t => if i ≤ t then βR (t.val - i.val) else βL (i.val - t.val), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [le_refl, if_true, Nat.sub_self, h0R]
  · intro t t' htt' ht'a
    rw [Fin.le_def] at ht'a
    simp only []
    by_cases h1 : i ≤ t
    · have h1' : i ≤ t' := by rw [Fin.le_def] at h1 ⊢; omega
      rw [if_pos h1, if_pos h1']
      rw [Fin.le_def] at h1
      rw [show t'.val - i.val = (t.val - i.val) + 1 by omega]
      exact hlR _ (by omega)
    · rw [if_neg h1]
      rw [Fin.le_def] at h1
      by_cases h2 : i ≤ t'
      · rw [if_pos h2]
        rw [Fin.le_def] at h2
        rw [show t'.val - i.val = 0 by omega, h0R, show i.val - t.val = 0 + 1 by omega]
        have := hlL 0 (by omega)
        rw [h0L] at this
        rw [abs_sub_comm]; simpa using this
      · rw [if_neg h2]
        rw [Fin.le_def] at h2
        rw [show i.val - t.val = (i.val - t'.val) + 1 by omega, abs_sub_comm]
        exact hlL _ (by omega)
  · intro t hta
    simp only []
    by_cases h1 : i ≤ t
    · rw [if_pos h1]
      have := hwR (t.val - i.val) (by rw [Fin.le_def] at hta h1; omega)
      rw [hSR t h1] at this
      exact this
    · rw [if_neg h1]
      have h1' : t < i := lt_of_not_ge h1
      have := hwL (i.val - t.val) (by omega)
      rw [hSL t h1'] at this
      exact this
  · simp only [hia, if_true]
    exact hU
  · intro t hta ht hft
    rw [Fin.le_def] at hta
    simp only []
    rcases ht with ht | ht
    · rw [if_neg (by rw [Fin.le_def]; omega)]
      refine hzL (i.val - t.val) (by omega) (fun i' hi' => ?_)
      rcases (show i' = 0 ∨ i' = 1 by omega) with h | h
      · subst h; simpa [hS0] using hc0
      · subst h
        have := hSL t (by rw [Fin.lt_def]; omega)
        rw [show i.val - t.val = 1 by omega] at this
        rw [this]; exact hft
    · rw [if_pos (by rw [Fin.le_def]; omega)]
      refine hzR (t.val - i.val) (by omega) (fun i' hi' => ?_)
      rcases (show i' = 0 ∨ i' = 1 by omega) with h | h
      · subst h; simpa [hS0] using hc0
      · subst h
        have := hSR t (by rw [Fin.le_def]; omega)
        rw [show t.val - i.val = 1 by omega] at this
        rw [this]; exact hft

/-- Values of `reindex f i` inside the range. -/
theorem reindex_val (f : Fin n → ℤ) (i : Fin n) (x : ℤ) (h1 : -(i.val : ℤ) ≤ x)
    (h2 : (i : ℤ) + x < n) : reindex f i x = f ⟨((i : ℤ) + x).toNat, by omega⟩ :=
  B78.reindex_eq f i x (by omega) h2

/-- **The fold with a fake low end on `Fin n`.** -/
theorem finfold_low (f : Fin n → ℤ) (i a : Fin n) (hia : i ≤ a) (Hb : ℤ)
    (hcr : CrkOn (reindex f i) (-(i.val : ℤ)) ((n : ℤ) - 1 - i.val))
    (hlip : ∀ t t' : Fin n, t'.val = t.val + 1 → |f t' - f t| ≤ 1)
    (hnn : ∀ t, 0 ≤ f t) (hH : ∀ t, f t ≤ Hb) (hend : f a ≤ 1)
    (hmeet : ∀ t : Fin n, t < a → 3 ≤ f t → ∃ y y' : Fin n, t < y ∧ y < y' ∧ y' < a ∧
      f y ≤ 1 ∧ f t - 2 ≤ f y' ∧ f y' ≤ f t - 1)
    (above : Bool) (hok : if above then ¬ EvUp f i a 0 else ¬ EvDown f i a 0) :
    ∃ (c : ℕ → ℤ) (β : Fin n → ℕ) (U : ℕ), β i = 0 ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(β t' : ℤ) - β t| ≤ 1) ∧
      (∀ t : Fin n, t ≤ a → |f t - c (β t)| ≤ 1) ∧
      |(U : ℤ) - β a| ≤ 1 ∧ c U ≤ 1 ∧ c 0 = f i + (if above then 1 else -1) ∧
      (∀ t : Fin n, t ≤ a → (t.val + 1 = i.val ∨ t.val = i.val + 1) → |f t - c 0| ≤ 1 →
        β t = 0) ∧
      (a = i → |c 0| ≤ 1 → U = 0) := by
  classical
  set S := reindex f i with hS
  have hia' : i.val ≤ a.val := hia
  have han := a.isLt
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = a.val - i.val := ⟨_, rfl⟩
  have hCrk : CrkOn S (-(i.val : ℤ)) q := by
    intro x y hx hxy hy
    exact hcr x y hx hxy (by omega)
  have hSval : ∀ (x : ℤ) (h1 : -(i.val : ℤ) ≤ x) (h2 : x ≤ q),
      S x = f ⟨((i : ℤ) + x).toNat, by omega⟩ :=
    fun x h1 h2 => reindex_val f i x h1 (by omega)
  have hlipS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x < q → |S (x + 1) - S x| ≤ 1 := by
    intro x h1 h2
    rw [hSval (x + 1) (by omega) (by omega), hSval x h1 (by omega)]
    exact hlip _ _ (by simp only; omega)
  have hnnS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x ≤ q → 0 ≤ S x := by
    intro x h1 h2; rw [hSval x h1 h2]; exact hnn _
  have hHS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x ≤ q → S x ≤ Hb := by
    intro x h1 h2; rw [hSval x h1 h2]; exact hH _
  have hendS : S q ≤ 1 := by
    rw [hSval q (by omega) le_rfl]
    have he : (⟨((i : ℤ) + q).toNat, by omega⟩ : Fin n) = a := Fin.ext (by simp only; omega)
    rw [he]; exact hend
  have hmeetS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x < q → 3 ≤ S x →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ S y ≤ 1 ∧ S x - 2 ≤ S y' ∧ S y' ≤ S x - 1 := by
    intro x h1 h2 h3
    rw [hSval x h1 (by omega)] at h3 ⊢
    set t : Fin n := ⟨((i : ℤ) + x).toNat, by omega⟩ with ht
    have htv : (t.val : ℤ) = i + x := by simp only [ht]; omega
    obtain ⟨y, y', a1, a2, a3, a4, a5, a6⟩ := hmeet t (by rw [Fin.lt_def]; omega) h3
    rw [Fin.lt_def] at a1 a2 a3
    have ey : (⟨((i : ℤ) + ((y : ℤ) - i)).toNat, by omega⟩ : Fin n) = y :=
      Fin.ext (by simp only; omega)
    have ey' : (⟨((i : ℤ) + ((y' : ℤ) - i)).toNat, by omega⟩ : Fin n) = y' :=
      Fin.ext (by simp only; omega)
    refine ⟨(y : ℤ) - i, (y' : ℤ) - i, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hSval _ (by omega) (by omega), ey]; exact a4
    · rw [hSval _ (by omega) (by omega), ey']; exact a5
    · rw [hSval _ (by omega) (by omega), ey']; exact a6
  have hok' : if above then OKAbove (lowExt S q) (extM i.val q)
      else OKBelow (lowExt S q) (extM i.val q) := by
    cases above
    · simp only [Bool.false_eq_true, if_false] at hok ⊢
      have := okBelow_of_not_evDown f i a hia 0 hok
      rw [← hq] at this; exact this
    · simp only [if_true] at hok ⊢
      have := okAbove_of_not_evUp f i a hia 0 hok
      rw [← hq] at this; exact this
  obtain ⟨c, βR, βL, U, h0R, h0L, hlR, hlL, hwR, hwL, hU, hcU, hc0, hzR, hzL, hU0⟩ :=
    fold_low_end_mode S i.val q Hb hCrk hlipS hnnS hHS hendS hmeetS above hok'
  have hS0 : S 0 = f i := by simpa using reindex_fin f i i
  have hc0' : |f i - c 0| ≤ 1 := by
    rw [hc0, hS0]; cases above <;> simp
  subst hq
  obtain ⟨β, b1, b2, b3, b4, b5⟩ := transport f i a hia c βR βL U h0R h0L hlR hlL hwR hwL hU
    hc0' hzR hzL
  refine ⟨c, β, U, b1, b2, b3, b4, hcU, by rw [hc0, hS0], b5, fun hai => ?_⟩
  subst hai
  exact hU0 (by simp)

/-- **The fold with a fake low end on `Fin n`**, first direction whichever is available. -/
theorem finfold_low_any (f : Fin n → ℤ) (i a : Fin n) (hia : i ≤ a) (Hb : ℤ)
    (hcr : CrkOn (reindex f i) (-(i.val : ℤ)) ((n : ℤ) - 1 - i.val))
    (hlip : ∀ t t' : Fin n, t'.val = t.val + 1 → |f t' - f t| ≤ 1)
    (hnn : ∀ t, 0 ≤ f t) (hH : ∀ t, f t ≤ Hb) (hend : f a ≤ 1)
    (hmeet : ∀ t : Fin n, t < a → 3 ≤ f t → ∃ y y' : Fin n, t < y ∧ y < y' ∧ y' < a ∧
      f y ≤ 1 ∧ f t - 2 ≤ f y' ∧ f y' ≤ f t - 1)
    : ∃ (above : Bool) (c : ℕ → ℤ) (β : Fin n → ℕ) (U : ℕ), β i = 0 ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(β t' : ℤ) - β t| ≤ 1) ∧
      (∀ t : Fin n, t ≤ a → |f t - c (β t)| ≤ 1) ∧
      |(U : ℤ) - β a| ≤ 1 ∧ c U ≤ 1 ∧ c 0 = f i + (if above then 1 else -1) ∧
      (∀ t : Fin n, t ≤ a → (t.val + 1 = i.val ∨ t.val = i.val + 1) → |f t - c 0| ≤ 1 →
        β t = 0) ∧
      (a = i → |c 0| ≤ 1 → U = 0) := by
  classical
  set S := reindex f i with hS
  have hia' : i.val ≤ a.val := hia
  have han := a.isLt
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = a.val - i.val := ⟨_, rfl⟩
  have hCrk : CrkOn S (-(i.val : ℤ)) q := by
    intro x y hx hxy hy
    exact hcr x y hx hxy (by omega)
  have hSval : ∀ (x : ℤ) (h1 : -(i.val : ℤ) ≤ x) (h2 : x ≤ q),
      S x = f ⟨((i : ℤ) + x).toNat, by omega⟩ :=
    fun x h1 h2 => reindex_val f i x h1 (by omega)
  have hlipS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x < q → |S (x + 1) - S x| ≤ 1 := by
    intro x h1 h2
    rw [hSval (x + 1) (by omega) (by omega), hSval x h1 (by omega)]
    exact hlip _ _ (by simp only; omega)
  have hnnS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x ≤ q → 0 ≤ S x := by
    intro x h1 h2; rw [hSval x h1 h2]; exact hnn _
  have hHS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x ≤ q → S x ≤ Hb := by
    intro x h1 h2; rw [hSval x h1 h2]; exact hH _
  have hendS : S q ≤ 1 := by
    rw [hSval q (by omega) le_rfl]
    have he : (⟨((i : ℤ) + q).toNat, by omega⟩ : Fin n) = a := Fin.ext (by simp only; omega)
    rw [he]; exact hend
  have hmeetS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x < q → 3 ≤ S x →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ S y ≤ 1 ∧ S x - 2 ≤ S y' ∧ S y' ≤ S x - 1 := by
    intro x h1 h2 h3
    rw [hSval x h1 (by omega)] at h3 ⊢
    set t : Fin n := ⟨((i : ℤ) + x).toNat, by omega⟩ with ht
    have htv : (t.val : ℤ) = i + x := by simp only [ht]; omega
    obtain ⟨y, y', a1, a2, a3, a4, a5, a6⟩ := hmeet t (by rw [Fin.lt_def]; omega) h3
    rw [Fin.lt_def] at a1 a2 a3
    have ey : (⟨((i : ℤ) + ((y : ℤ) - i)).toNat, by omega⟩ : Fin n) = y :=
      Fin.ext (by simp only; omega)
    have ey' : (⟨((i : ℤ) + ((y' : ℤ) - i)).toNat, by omega⟩ : Fin n) = y' :=
      Fin.ext (by simp only; omega)
    refine ⟨(y : ℤ) - i, (y' : ℤ) - i, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hSval _ (by omega) (by omega), ey]; exact a4
    · rw [hSval _ (by omega) (by omega), ey']; exact a5
    · rw [hSval _ (by omega) (by omega), ey']; exact a6
  obtain ⟨above, hok'⟩ := ok_lowExt S i.val q hCrk hnnS hendS hmeetS
  obtain ⟨c, βR, βL, U, h0R, h0L, hlR, hlL, hwR, hwL, hU, hcU, hc0, hzR, hzL, hU0⟩ :=
    fold_low_end_mode S i.val q Hb hCrk hlipS hnnS hHS hendS hmeetS above hok'
  have hS0 : S 0 = f i := by simpa using reindex_fin f i i
  have hc0' : |f i - c 0| ≤ 1 := by
    rw [hc0, hS0]; cases above <;> simp
  subst hq
  obtain ⟨β, b1, b2, b3, b4, b5⟩ := transport f i a hia c βR βL U h0R h0L hlR hlL hwR hwL hU
    hc0' hzR hzL
  refine ⟨above, c, β, U, b1, b2, b3, b4, hcU, by rw [hc0, hS0], b5, fun hai => ?_⟩
  subst hai
  exact hU0 (by simp)

/-- **The fold with a fake high end on `Fin n`.** -/
theorem finfold_high (f : Fin n → ℤ) (i a : Fin n) (hia : i ≤ a) (Hb : ℤ)
    (hcr : CrkOn (reindex f i) (-(i.val : ℤ)) ((n : ℤ) - 1 - i.val))
    (hlip : ∀ t t' : Fin n, t'.val = t.val + 1 → |f t' - f t| ≤ 1)
    (hnn : ∀ t, 0 ≤ f t) (hH : ∀ t, f t ≤ Hb) (hend : Hb - 1 ≤ f a)
    (hmeet : ∀ t : Fin n, t < a → f t + 3 ≤ Hb → ∃ y y' : Fin n, t < y ∧ y < y' ∧ y' < a ∧
      Hb - 2 ≤ f y ∧ f y ≤ Hb - 1 ∧ f t ≤ f y' ∧ f y' ≤ f t + 1)
    (above : Bool) (hok : if above then ¬ EvUp f i a Hb else ¬ EvDown f i a Hb) :
    ∃ (c : ℕ → ℤ) (β : Fin n → ℕ) (U : ℕ), β i = 0 ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(β t' : ℤ) - β t| ≤ 1) ∧
      (∀ t : Fin n, t ≤ a → |f t - c (β t)| ≤ 1) ∧
      |(U : ℤ) - β a| ≤ 1 ∧ Hb - 1 ≤ c U ∧ c 0 = f i + (if above then 1 else -1) ∧
      (∀ t : Fin n, t ≤ a → (t.val + 1 = i.val ∨ t.val = i.val + 1) → |f t - c 0| ≤ 1 →
        β t = 0) := by
  classical
  set S := reindex f i with hS
  have hia' : i.val ≤ a.val := hia
  have han := a.isLt
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = a.val - i.val := ⟨_, rfl⟩
  have hCrk : CrkOn S (-(i.val : ℤ)) q := by
    intro x y hx hxy hy
    exact hcr x y hx hxy (by omega)
  have hSval : ∀ (x : ℤ) (h1 : -(i.val : ℤ) ≤ x) (h2 : x ≤ q),
      S x = f ⟨((i : ℤ) + x).toNat, by omega⟩ :=
    fun x h1 h2 => reindex_val f i x h1 (by omega)
  have hlipS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x < q → |S (x + 1) - S x| ≤ 1 := by
    intro x h1 h2
    rw [hSval (x + 1) (by omega) (by omega), hSval x h1 (by omega)]
    exact hlip _ _ (by simp only; omega)
  have hnnS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x ≤ q → 0 ≤ S x := by
    intro x h1 h2; rw [hSval x h1 h2]; exact hnn _
  have hHS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x ≤ q → S x ≤ Hb := by
    intro x h1 h2; rw [hSval x h1 h2]; exact hH _
  have hendS : Hb - 1 ≤ S q := by
    rw [hSval q (by omega) le_rfl]
    have he : (⟨((i : ℤ) + q).toNat, by omega⟩ : Fin n) = a := Fin.ext (by simp only; omega)
    rw [he]; exact hend
  have hmeetS : ∀ x : ℤ, -(i.val : ℤ) ≤ x → x < q → S x + 3 ≤ Hb →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ Hb - 2 ≤ S y ∧ S y ≤ Hb - 1 ∧ S x ≤ S y' ∧
        S y' ≤ S x + 1 := by
    intro x h1 h2 h3
    rw [hSval x h1 (by omega)] at h3 ⊢
    set t : Fin n := ⟨((i : ℤ) + x).toNat, by omega⟩ with ht
    have htv : (t.val : ℤ) = i + x := by simp only [ht]; omega
    obtain ⟨y, y', a1, a2, a3, a4, a5, a6, a7⟩ := hmeet t (by rw [Fin.lt_def]; omega) h3
    rw [Fin.lt_def] at a1 a2 a3
    have ey : (⟨((i : ℤ) + ((y : ℤ) - i)).toNat, by omega⟩ : Fin n) = y :=
      Fin.ext (by simp only; omega)
    have ey' : (⟨((i : ℤ) + ((y' : ℤ) - i)).toNat, by omega⟩ : Fin n) = y' :=
      Fin.ext (by simp only; omega)
    refine ⟨(y : ℤ) - i, (y' : ℤ) - i, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [hSval _ (by omega) (by omega), ey]; exact a4
    · rw [hSval _ (by omega) (by omega), ey]; exact a5
    · rw [hSval _ (by omega) (by omega), ey']; exact a6
    · rw [hSval _ (by omega) (by omega), ey']; exact a7
  have hok' : if above then OKAbove (highExt S q Hb) (extM i.val q)
      else OKBelow (highExt S q Hb) (extM i.val q) := by
    cases above
    · simp only [Bool.false_eq_true, if_false] at hok ⊢
      have := okBelow_of_not_evDown f i a hia Hb hok
      rw [← hq] at this; exact this
    · simp only [if_true] at hok ⊢
      have := okAbove_of_not_evUp f i a hia Hb hok
      rw [← hq] at this; exact this
  obtain ⟨c, βR, βL, U, h0R, h0L, hlR, hlL, hwR, hwL, hU, hcU, hc0, hzR, hzL⟩ :=
    fold_high_end_mode S i.val q Hb hCrk hlipS hnnS hHS hendS hmeetS above hok'
  have hS0 : S 0 = f i := by simpa using reindex_fin f i i
  have hc0' : |f i - c 0| ≤ 1 := by
    rw [hc0, hS0]; cases above <;> simp
  subst hq
  obtain ⟨β, b1, b2, b3, b4, b5⟩ := transport f i a hia c βR βL U h0R h0L hlR hlL hwR hwL hU
    hc0' hzR hzL
  exact ⟨c, β, U, b1, b2, b3, b4, hcU, by rw [hc0, hS0], b5⟩

end HPC.Fold.B79
