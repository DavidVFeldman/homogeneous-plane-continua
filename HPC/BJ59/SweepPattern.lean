import HPC.BJ59.Sweep

/-!
# Batch 202, §4.2–4.3: the sweep pattern

The pattern of commission 202 §4.2. Sweeps of length `L = S z(m−2) z(m−1)`; three sweeps per
period; period `j` has window `[swB m j, swT m j]` with `swT m j = ⌊(j + m)/2⌋` and
`swB m j = ⌈(j + 2 − m)/2⌉`; sweep `n` goes up iff `n + m` is even (this is the commission's
rule "period `j` starts at the bottom iff `j + m` is even, and the sweeps alternate", since
`n = 3j + r` has the parity of `j + r`).
-/

namespace HPC.BJ59

open HPC.Fold HPC.Plane

/-- `Q = 6 S z(m−2) z(m−1)`, the number of new links per old link (commission §4.2). -/
def sweepQ (m S : ℕ) : ℕ := 6 * S * HPC.Fold.z (m - 2) * HPC.Fold.z (m - 1)

/-- The length of a sweep, `L = S z(m−2) z(m−1)`. -/
def sweepL (m S : ℕ) : ℕ := S * z (m - 2) * z (m - 1)

theorem sweepQ_eq (m S : ℕ) : sweepQ m S = 6 * sweepL m S := by
  unfold sweepQ sweepL; ring

/-- The top of the window of period `j`. -/
def swT (m : ℕ) (j : ℤ) : ℤ := (j + m) / 2

/-- The bottom of the window of period `j`. -/
def swB (m : ℕ) (j : ℤ) : ℤ := -(((m : ℤ) - 2 - j) / 2)

/-- The width of the window of period `j`. -/
def swD (m : ℕ) (j : ℤ) : ℕ := (swT m j - swB m j).toNat

/-- The stutter of period `j`. -/
def swK (m S : ℕ) (j : ℤ) : ℕ := sweepL m S / z (swD m j)

/-- Sweep `n` at position `u` (`0 ≤ u < L`). -/
def swVal (m S : ℕ) (n : ℤ) (u : ℕ) : ℤ :=
  if (n + m) % 2 = 0 then swB m (n / 3) + stut (swD m (n / 3)) (swK m S (n / 3)) u
  else swT m (n / 3) - stut (swD m (n / 3)) (swK m S (n / 3)) u

/-- **The sweep pattern.** -/
def sweepX (m S : ℕ) (t : ℤ) : ℤ := swVal m S (t / sweepL m S) (t % sweepL m S).toNat

section Arith

variable {m S : ℕ}

theorem swT_even {j : ℤ} (h : (j + m) % 2 = 0) : 2 * swT m j = j + m := by
  unfold swT; omega

theorem swT_odd {j : ℤ} (h : (j + m) % 2 ≠ 0) : 2 * swT m j = j + m - 1 := by
  unfold swT; omega

theorem swB_even {j : ℤ} (h : (j + m) % 2 = 0) : 2 * swB m j = j + 2 - m := by
  unfold swB; omega

theorem swB_odd {j : ℤ} (h : (j + m) % 2 ≠ 0) : 2 * swB m j = j + 3 - m := by
  unfold swB; omega

theorem swD_even (hm : 2 ≤ m) {j : ℤ} (h : (j + m) % 2 = 0) : swD m j = m - 1 := by
  have h1 := swT_even h; have h2 := swB_even h
  unfold swD; omega

theorem swD_odd (hm : 3 ≤ m) {j : ℤ} (h : (j + m) % 2 ≠ 0) : swD m j = m - 2 := by
  have h1 := swT_odd h; have h2 := swB_odd h
  unfold swD; omega

theorem swD_eq (hm : 3 ≤ m) (j : ℤ) : (swD m j : ℤ) = swT m j - swB m j := by
  by_cases h : (j + m) % 2 = 0
  · have h1 := swT_even h; have h2 := swB_even h
    unfold swD; omega
  · have h1 := swT_odd h; have h2 := swB_odd h
    unfold swD; omega

theorem swK_mul (hm : 3 ≤ m) (j : ℤ) : swK m S j * z (swD m j) = sweepL m S := by
  unfold swK sweepL
  by_cases h : (j + m) % 2 = 0
  · rw [swD_even (by omega) h, show m - 1 = m - 1 from rfl]
    rw [Nat.div_mul_cancel (Dvd.intro_left _ rfl)]
  · rw [swD_odd hm h]
    rw [Nat.div_mul_cancel ⟨S * z (m - 1), by ring⟩]

theorem swK_eq (hm : 3 ≤ m) (j : ℤ) :
    swK m S j = S * z (m - 2) ∨ swK m S j = S * z (m - 1) := by
  unfold swK sweepL
  by_cases h : (j + m) % 2 = 0
  · left; rw [swD_even (by omega) h, Nat.mul_div_cancel _ (z_pos _)]
  · right; rw [swD_odd hm h, show S * z (m - 2) * z (m - 1) = S * z (m - 1) * z (m - 2) by ring,
      Nat.mul_div_cancel _ (z_pos _)]

theorem swK_pos (hm : 3 ≤ m) (hS : 1 ≤ S) (j : ℤ) : 0 < swK m S j := by
  rcases swK_eq (S := S) hm j with e | e <;> rw [e] <;> exact Nat.mul_pos hS (z_pos _)

theorem S_dvd_swK (hm : 3 ≤ m) (j : ℤ) : S ∣ swK m S j := by
  rcases swK_eq (S := S) hm j with e | e <;> rw [e] <;> exact Dvd.intro _ rfl

theorem sweepL_ge (hm : 5 ≤ m) (hS : 1 ≤ S) : 4 ≤ sweepL m S := by
  unfold sweepL
  have h3 : 6 ≤ z (m - 2) := by
    have := z_ge_of_le (show 3 ≤ m - 2 by omega); simpa [z] using this
  have h4 : 6 ≤ z (m - 1) := by
    have := z_ge_of_le (show 3 ≤ m - 1 by omega); simpa [z] using this
  have : 1 * 6 * 6 ≤ S * z (m - 2) * z (m - 1) := by gcongr
  omega

end Arith

theorem stut_zero' (d K : ℕ) : stut d K 0 = 0 := by
  unfold stut; simp [bingF_zero]

theorem stut_last (d K : ℕ) (hK : 0 < K) : stut d K (K * z d - 1) = d := by
  unfold stut
  apply bingF_top
  have hz := z_pos d
  have : K * (z d - 1) ≤ K * z d - 1 := by
    rw [Nat.mul_sub_one]; have : K ≤ K * z d := Nat.le_mul_of_pos_right K hz; omega
  exact (Nat.le_div_iff_mul_le hK).mpr (by rw [mul_comm]; exact this)

section Block

variable {m S : ℕ}

/-- Decomposition of an index into a sweep and a position. -/
theorem sweep_decomp {L : ℕ} (hL : 0 < L) (t : ℤ) :
    t = (t / L) * L + ((t % L).toNat : ℤ) ∧ (t % L).toNat < L := by
  have h1 := Int.emod_nonneg t (show (L : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos t (show (0 : ℤ) < L by omega)
  have h3 := Int.mul_ediv_add_emod t L
  constructor
  · rw [Int.toNat_of_nonneg h1]; linarith [mul_comm (L : ℤ) (t / L)]
  · omega

theorem sweepX_block (hL : 0 < sweepL m S) (n : ℤ) (u : ℕ) (hu : u < sweepL m S) :
    sweepX m S (n * sweepL m S + u) = swVal m S n u := by
  unfold sweepX
  have hL' : (sweepL m S : ℤ) ≠ 0 := by omega
  have e1 : (n * sweepL m S + u) / (sweepL m S : ℤ) = n := by
    rw [add_comm, Int.add_mul_ediv_right _ _ hL', Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    simp
  have e2 : (n * sweepL m S + u) % (sweepL m S : ℤ) = u := by
    rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [e1, e2]; simp

theorem swVal_zero (n : ℤ) :
    swVal m S n 0 = if (n + m) % 2 = 0 then swB m (n / 3) else swT m (n / 3) := by
  unfold swVal; simp [stut_zero']

theorem swVal_last (hm : 5 ≤ m) (hS : 1 ≤ S) (n : ℤ) :
    swVal m S n (sweepL m S - 1) = if (n + m) % 2 = 0 then swT m (n / 3) else swB m (n / 3) := by
  have hK := swK_mul (S := S) (by omega : 3 ≤ m) (n / 3)
  have hd := swD_eq (by omega : 3 ≤ m) (n / 3)
  have hl : stut (swD m (n / 3)) (swK m S (n / 3)) (sweepL m S - 1) = swD m (n / 3) := by
    rw [← hK]; exact stut_last _ _ (swK_pos (by omega) hS _)
  unfold swVal; rw [hl]; split_ifs <;> omega

theorem swVal_range (hm : 5 ≤ m) (n : ℤ) (u : ℕ) :
    swB m (n / 3) ≤ swVal m S n u ∧ swVal m S n u ≤ swT m (n / 3) := by
  have hd := swD_eq (by omega : 3 ≤ m) (n / 3)
  have hr := stut_range (swD m (n / 3)) (swK m S (n / 3)) u
  unfold swVal; split_ifs <;> omega

theorem sw_win_up {n : ℤ} (h : (n + m) % 2 = 0) :
    swT m ((n + 1) / 3) = swT m (n / 3) ∧
      (swB m ((n + 1) / 3) = swB m (n / 3) ∨ swB m ((n + 1) / 3) = swB m (n / 3) + 1) := by
  unfold swT swB; omega

theorem sw_win_down {n : ℤ} (h : ¬ (n + m) % 2 = 0) :
    swB m ((n + 1) / 3) = swB m (n / 3) ∧
      (swT m ((n + 1) / 3) = swT m (n / 3) ∨ swT m ((n + 1) / 3) = swT m (n / 3) + 1) := by
  unfold swT swB; omega

theorem swVal_junction (hm : 5 ≤ m) (hS : 1 ≤ S) (n : ℤ) :
    swVal m S (n + 1) 0 = swVal m S n (sweepL m S - 1) := by
  rw [swVal_zero, swVal_last hm hS]
  by_cases h : (n + m) % 2 = 0
  · rw [if_neg (by omega), if_pos h]; exact (sw_win_up h).1
  · rw [if_pos (by omega), if_neg h]; exact (sw_win_down h).1

theorem swT_add2 (j : ℤ) : swT m (j + 2) = swT m j + 1 := by unfold swT; omega

theorem swB_add2 (j : ℤ) : swB m (j + 2) = swB m j + 1 := by unfold swB; omega

theorem swD_add2 (j : ℤ) : swD m (j + 2) = swD m j := by
  unfold swD; rw [swT_add2, swB_add2]; congr 1; ring

theorem swVal_add6 (n : ℤ) (u : ℕ) : swVal m S (n + 6) u = swVal m S n u + 1 := by
  have e1 : (n + 6) / 3 = n / 3 + 2 := by omega
  have e2 : ((n + 6 + m) % 2 = 0) ↔ ((n + m) % 2 = 0) := by omega
  unfold swVal swK
  rw [e1, swD_add2, swT_add2, swB_add2]
  by_cases h : (n + m) % 2 = 0
  · rw [if_pos (e2.mpr h), if_pos h]; ring
  · rw [if_neg (fun h' => h (e2.mp h')), if_neg h]; ring

end Block

/-- A pattern constant on the aligned blocks `[S c, S c + S)` with unit steps is `S`-slow. -/
theorem slow_of_factor (x : ℤ → ℤ) (S : ℕ) (hS : 1 ≤ S) (hstep : ∀ t, |x (t + 1) - x t| ≤ 1)
    (hf : ∀ t, x t = x (S * (t / S))) : ∀ s t, x s + 2 ≤ x t → (S : ℤ) ≤ |s - t| := by
  have hS' : (0 : ℤ) < S := by omega
  set w : ℤ → ℤ := fun c => x (S * c) with hw
  have wstep : ∀ c, |w (c + 1) - w c| ≤ 1 := by
    intro c
    have e1 : x (S * c + S - 1) = x (S * c) := by
      rw [hf]; congr 2
      rw [show S * c + S - 1 = (S - 1) + c * S by ring, Int.add_mul_ediv_right _ _ hS'.ne',
        Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      simp
    have := hstep (S * c + S - 1)
    rw [e1, show S * c + S - 1 + 1 = S * (c + 1) by ring] at this
    exact this
  have wlip : ∀ a b, a ≤ b → |w b - w a| ≤ b - a := by
    intro a b hab
    induction b, hab using Int.le_induction with
    | base => simp
    | succ b _ ih =>
        have := wstep b
        rw [abs_le] at this ih ⊢
        constructor <;> linarith
  intro s t hst
  rw [hf s, hf t] at hst
  have hs1 := Int.mul_ediv_add_emod s S
  have hs2 := Int.emod_nonneg s hS'.ne'
  have hs3 := Int.emod_lt_of_pos s hS'
  have ht1 := Int.mul_ediv_add_emod t S
  have ht2 := Int.emod_nonneg t hS'.ne'
  have ht3 := Int.emod_lt_of_pos t hS'
  rcases le_total (s / S) (t / S) with h | h
  · have := wlip _ _ h
    rw [abs_le] at this
    have h2 : s / S + 2 ≤ t / S := by simp only [hw] at this; linarith
    have : S * (s / S + 2) ≤ S * (t / S) := by nlinarith
    rw [abs_sub_comm]; exact le_trans (by nlinarith) (le_abs_self _)
  · have := wlip _ _ h
    rw [abs_le] at this
    have h2 : t / S + 2 ≤ s / S := by simp only [hw] at this; linarith
    have : S * (t / S + 2) ≤ S * (s / S) := by nlinarith
    exact le_trans (by nlinarith) (le_abs_self _)

section Props

variable {m S : ℕ}

theorem sweepL_pos (hm : 5 ≤ m) (hS : 1 ≤ S) : 0 < sweepL m S := by
  have := sweepL_ge hm hS; omega

/-- §4.3 1: period. -/
theorem sweepX_period (hm : 5 ≤ m) (hS : 1 ≤ S) (t : ℤ) :
    sweepX m S (t + sweepQ m S) = sweepX m S t + 1 := by
  have hL := sweepL_pos hm hS
  obtain ⟨e, hu⟩ := sweep_decomp hL t
  rw [sweepQ_eq]
  conv_lhs => rw [e]
  conv_rhs => rw [e]
  rw [show (t / ↑(sweepL m S)) * ↑(sweepL m S) + ↑(t % ↑(sweepL m S)).toNat + ↑(6 * sweepL m S)
      = (t / ↑(sweepL m S) + 6) * ↑(sweepL m S) + ↑(t % ↑(sweepL m S)).toNat by push_cast; ring,
    sweepX_block hL _ _ hu, sweepX_block hL _ _ hu, swVal_add6]

/-- §4.3 2: unit steps. -/
theorem sweepX_step (hm : 5 ≤ m) (hS : 1 ≤ S) (t : ℤ) :
    |sweepX m S (t + 1) - sweepX m S t| ≤ 1 := by
  have hL := sweepL_pos hm hS
  obtain ⟨e, hu⟩ := sweep_decomp hL t
  set n := t / ↑(sweepL m S)
  set u := (t % ↑(sweepL m S)).toNat
  rw [e]
  by_cases hu1 : u + 1 < sweepL m S
  · rw [show n * ↑(sweepL m S) + ↑u + 1 = n * ↑(sweepL m S) + ↑(u + 1) by push_cast; ring,
      sweepX_block hL _ _ hu1, sweepX_block hL _ _ hu]
    have := stut_lip (swD m (n / 3)) (swK m S (n / 3)) u
    unfold swVal; split_ifs
    · simpa using this
    · rw [abs_le] at this ⊢; constructor <;> linarith
  · have hu2 : u = sweepL m S - 1 := by omega
    rw [show n * ↑(sweepL m S) + ↑u + 1 = (n + 1) * ↑(sweepL m S) + ((0 : ℕ) : ℤ) by
        rw [hu2]; push_cast [Nat.cast_sub (show 1 ≤ sweepL m S by omega)]; ring,
      sweepX_block hL _ _ hL, sweepX_block hL _ _ hu, hu2, swVal_junction hm hS]
    simp

/-- The pattern factors through `t ↦ ⌊t / S⌋`. -/
theorem sweepX_factor (hm : 5 ≤ m) (hS : 1 ≤ S) (t : ℤ) :
    sweepX m S t = sweepX m S (S * (t / S)) := by
  have hL := sweepL_pos hm hS
  obtain ⟨e, hu⟩ := sweep_decomp hL t
  set n := t / ↑(sweepL m S)
  set u := (t % ↑(sweepL m S)).toNat
  have hSL : S ∣ sweepL m S := ⟨z (m - 2) * z (m - 1), by unfold sweepL; ring⟩
  obtain ⟨L', hL'⟩ := hSL
  have hS' : (0 : ℤ) < S := by omega
  have key : (S : ℤ) * (t / S) = n * ↑(sweepL m S) + ↑(S * (u / S)) := by
    conv_lhs => rw [e]
    rw [hL']; push_cast
    rw [show n * (↑S * ↑L') + (u : ℤ) = (u : ℤ) + (n * L') * S by ring,
      Int.add_mul_ediv_right _ _ hS'.ne']
    rw [show ((u : ℤ) / S) = ((u / S : ℕ) : ℤ) by push_cast; rfl]
    push_cast; ring
  have hu' : S * (u / S) < sweepL m S := lt_of_le_of_lt (Nat.mul_div_le u S) hu
  rw [key, sweepX_block hL _ _ hu']
  conv_lhs => rw [e, sweepX_block hL _ _ hu]
  obtain ⟨K', hK'⟩ := S_dvd_swK (S := S) (by omega : 3 ≤ m) (n / 3)
  have hst : stut (swD m (n / 3)) (swK m S (n / 3)) (S * (u / S)) =
      stut (swD m (n / 3)) (swK m S (n / 3)) u := by
    unfold stut; congr 1
    rw [hK', Nat.mul_div_mul_left _ _ (by omega : 0 < S), Nat.div_div_eq_div_mul]
  unfold swVal; rw [hst]

/-- §4.3 3: `S`-slow. -/
theorem sweepX_slow (hm : 5 ≤ m) (hS : 1 ≤ S) :
    ∀ s t, sweepX m S s + 2 ≤ sweepX m S t → (S : ℤ) ≤ |s - t| :=
  slow_of_factor _ S hS (sweepX_step hm hS) (sweepX_factor hm hS)

/-- Values in the window of the period. -/
theorem sweepX_range (hm : 5 ≤ m) (hS : 1 ≤ S) (t : ℤ) :
    swB m (t / sweepL m S / 3) ≤ sweepX m S t ∧ sweepX m S t ≤ swT m (t / sweepL m S / 3) := by
  have hL := sweepL_pos hm hS
  obtain ⟨e, hu⟩ := sweep_decomp hL t
  have := swVal_range (S := S) hm (t / sweepL m S) (t % ↑(sweepL m S)).toNat
  conv => enter [1, 2]; rw [e, sweepX_block hL _ _ hu]
  conv => enter [2, 1]; rw [e, sweepX_block hL _ _ hu]
  exact this

/-- The window bounds, numerically. -/
theorem sw_bounds (j : ℤ) : 2 * swT m j ≤ j + m ∧ j + 2 - m ≤ 2 * swB m j := by
  unfold swT swB; omega

/-- §4.3 4: nesting. -/
theorem sweepX_nest (hm : 5 ≤ m) (hS : 1 ≤ S) (t : ℤ) :
    |(sweepX m S t : ℝ) - (1 / 4 + (t : ℝ) / sweepQ m S)| ≤ (m : ℝ) / 2 - 1 / 4 := by
  have hL := sweepL_pos hm hS
  have hr := sweepX_range hm hS t
  have hLz : (0 : ℤ) < sweepL m S := by exact_mod_cast hL
  have hd1 : (t / (sweepL m S : ℤ)) * sweepL m S ≤ t := Int.ediv_mul_le t hLz.ne'
  have hd2 : t < (t / (sweepL m S : ℤ) + 1) * sweepL m S := by
    have := Int.lt_ediv_add_one_mul_self t hLz; linarith
  rw [sweepQ_eq]; push_cast
  generalize t / (sweepL m S : ℤ) = n at hr hd1 hd2
  generalize hj : n / 3 = j at hr
  generalize sweepL m S = L at hd1 hd2 hLz ⊢
  have hb := sw_bounds (m := m) j
  have hn : 3 * j ≤ n ∧ n ≤ 3 * j + 2 := by omega
  have h1 : 3 * j * (L : ℤ) ≤ t := by
    have : 3 * j * (L : ℤ) ≤ n * L := by nlinarith
    omega
  have h2 : t < 3 * (j + 1) * (L : ℤ) := by
    have : (n + 1) * (L : ℤ) ≤ 3 * (j + 1) * L := by nlinarith
    omega
  have hx1 : 2 * sweepX m S t ≤ j + m := by omega
  have hx2 : j + 2 - m ≤ 2 * sweepX m S t := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLz
  have r1 : (3 * j * L : ℝ) ≤ t := by exact_mod_cast h1
  have r2 : (t : ℝ) < 3 * (j + 1) * L := by exact_mod_cast h2
  have rx1 : 2 * (sweepX m S t : ℝ) ≤ j + m := by exact_mod_cast hx1
  have rx2 : (j : ℝ) + 2 - m ≤ 2 * sweepX m S t := by exact_mod_cast hx2
  have d1 : (j : ℝ) / 2 ≤ t / (6 * L) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have d2 : (t : ℝ) / (6 * L) < (j + 1) / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  rw [abs_le]; constructor <;> linarith

/-- §4.3 5: survival. -/
theorem sweepX_surv (hm : 5 ≤ m) (hS : 1 ≤ S) (l : ℤ) (y : ℝ)
    (hy : |y - l| ≤ (m : ℝ) / 2 - 1 / 2) :
    ∃ t, sweepX m S t = l ∧
      |y - (1 / 4 + (t : ℝ) / sweepQ m S)| ≤ 1 / 4 - 1 / (2 * (sweepQ m S : ℝ)) := by
  have hL := sweepL_pos hm hS
  set L := sweepL m S with hLdef
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hq : (sweepQ m S : ℝ) = 6 * L := by rw [sweepQ_eq]; push_cast; ring
  set Y : ℝ := 6 * L * y - 3 * L / 2 with hY
  set n : ℤ := ⌊Y / L⌋ with hn
  have hn1 : (n : ℝ) ≤ Y / L := Int.floor_le _
  have hn2 : Y / L < n + 1 := Int.lt_floor_add_one _
  have hYn1 : (n : ℝ) * L ≤ Y := by rwa [le_div_iff₀ hLr] at hn1
  have hYn2 : Y < (n + 1) * L := by rwa [div_lt_iff₀ hLr] at hn2
  rw [abs_le] at hy
  have hlo : (6 * l - 3 * m + 1 : ℝ) < n + 1 := by
    have : (6 * l - 3 * m + 3 / 2 : ℝ) * L ≤ Y := by rw [hY]; nlinarith
    have : (6 * l - 3 * m + 3 / 2 : ℝ) < n + 1 := by
      by_contra hc; push_neg at hc; nlinarith
    linarith
  have hhi : (n : ℝ) < 6 * l + 3 * m - 4 := by
    have : Y ≤ (6 * l + 3 * m - 9 / 2 : ℝ) * L := by rw [hY]; nlinarith
    have : (n : ℝ) ≤ 6 * l + 3 * m - 9 / 2 := by
      by_contra hc; push_neg at hc; nlinarith
    linarith
  have hlo' : 6 * l - 3 * m + 1 ≤ n := by
    have : (6 * l - 3 * m : ℝ) < n := by linarith
    exact_mod_cast (show ((6 * l - 3 * m : ℤ) : ℝ) < n by push_cast; linarith)
  have hhi' : n ≤ 6 * l + 3 * m - 5 := by
    have : (n : ℝ) < ((6 * l + 3 * m - 4 : ℤ) : ℝ) := by push_cast; linarith
    have := (Int.cast_lt (R := ℝ)).mp this
    omega
  have hwin : swB m (n / 3) ≤ l ∧ l ≤ swT m (n / 3) := by unfold swT swB; omega
  -- the sweep `n` visits `l`
  have hv0 : sweepX m S (n * L + ((0 : ℕ) : ℤ)) = swVal m S n 0 := sweepX_block hL n 0 hL
  have hv1 : sweepX m S (n * L + ((L - 1 : ℕ) : ℤ)) = swVal m S n (L - 1) :=
    sweepX_block hL n (L - 1) (by omega)
  rw [swVal_zero] at hv0
  rw [swVal_last hm hS] at hv1
  obtain ⟨v, v1, v2, v3⟩ := exists_eq_of_lipZ (sweepX m S) (sweepX_step hm hS)
    (a := n * L + ((0 : ℕ) : ℤ)) (c := n * L + ((L - 1 : ℕ) : ℤ)) (by push_cast; omega) (v := l)
    (by rw [hv0, hv1]; split_ifs <;> omega)
  refine ⟨v, v3, ?_⟩
  have hv1' : (n : ℝ) * L ≤ v := by
    have : n * (L : ℤ) ≤ v := by push_cast at v1; linarith
    exact_mod_cast this
  have hv2' : (v : ℝ) ≤ n * L + L - 1 := by
    have : v ≤ n * (L : ℤ) + L - 1 := by push_cast [Nat.cast_sub (show 1 ≤ L by omega)] at v2; linarith
    exact_mod_cast this
  have key : y - (1 / 4 + (v : ℝ) / sweepQ m S) = (Y - v) / (6 * L) := by
    rw [hq, hY]; field_simp; ring
  rw [key, hq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 6 * L), div_le_iff₀ (by positivity)]
  have : (1 / 4 - 1 / (2 * (6 * L)) : ℝ) * (6 * L) = 3 * L / 2 - 1 / 2 := by field_simp; ring
  rw [this, abs_le]; constructor <;> nlinarith

/-- The value at a junction. -/
theorem sweepX_junction (hm : 5 ≤ m) (hS : 1 ≤ S) (n : ℤ) :
    sweepX m S ((n + 1) * sweepL m S) = swVal m S n (sweepL m S - 1) := by
  have hL := sweepL_pos hm hS
  have := sweepX_block hL (n + 1) 0 hL
  rw [Nat.cast_zero, add_zero] at this
  rw [this, swVal_junction hm hS]

/-- Each sweep, closed at its junction, is crooked. -/
theorem sweepX_block_crooked (hm : 5 ≤ m) (hS : 1 ≤ S) (n : ℤ) :
    PatCrookedOnZ (sweepX m S) (n * sweepL m S) ((n + 1) * sweepL m S) := by
  have hL := sweepL_pos hm hS
  have hc0 := stut_crooked (swD m (n / 3)) (swK m S (n / 3)) (swK_pos (by omega) hS _)
  rw [swK_mul (by omega)] at hc0
  have hc1 : PatCrookedOn (swVal m S n) 0 (sweepL m S - 1) := by
    by_cases h : (n + m) % 2 = 0
    · have := hc0.shift 0 (swB m (n / 3))
      simp only [add_zero, Nat.sub_zero] at this
      exact this.congr (fun u _ _ => by simp [swVal, h])
    · exact (hc0.neg (swT m (n / 3))).congr (fun u _ _ => by simp [swVal, h])
  have hc2 := HPC.BJ59.PatCrookedOn.toZ hc1 (n * sweepL m S) (sweepX m S)
    (fun u _ hu => sweepX_block hL n u (by omega))
  have hc3 := hc2.extend (by
    rw [sweepX_block hL n _ (by omega)]
    rw [show n * (sweepL m S : ℤ) + ((sweepL m S - 1 : ℕ) : ℤ) + 1 = (n + 1) * sweepL m S by
      push_cast [Nat.cast_sub (show 1 ≤ sweepL m S by omega)]; ring]
    exact sweepX_junction hm hS n)
  convert hc3 using 1
  · simp
  · push_cast [Nat.cast_sub (show 1 ≤ sweepL m S by omega)]; ring

/-- §4.3 6: crookedness on every window of `Q/2 + 4` indices. -/
theorem sweepX_crook (hm : 5 ≤ m) (hS : 1 ≤ S) (a : ℤ) :
    PatCrookedOn (fun u : ℕ => sweepX m S (a + u)) 0 (sweepQ m S / 2 + 3) := by
  have hL := sweepL_pos hm hS
  have hL4 := sweepL_ge hm hS
  have hLz : (0 : ℤ) < sweepL m S := by exact_mod_cast hL
  apply PatCrookedOnZ.toNat
  refine sweep_lemma (sweepX m S) (sweepL m S) hLz (fun n => swB m (n / 3))
    (fun n => swT m (n / 3)) (fun n => (n + m) % 2 = 0) (sweepX_step hm hS) ?_ ?_
    (sweepX_block_crooked hm hS) (fun n => by omega) (fun n h => sw_win_up h)
    (fun n h => sw_win_down h) ?_
  · intro n u h1 h2
    rcases lt_or_eq_of_le h2 with h2 | h2
    · have e : u = n * sweepL m S + ((u - n * sweepL m S).toNat : ℕ) := by omega
      rw [e, sweepX_block hL _ _ (by
        have : u - n * sweepL m S < sweepL m S := by
          have : (n + 1) * (sweepL m S : ℤ) = n * sweepL m S + sweepL m S := by ring
          omega
        omega)]
      exact swVal_range hm n _
    · rw [h2, sweepX_junction hm hS]
      exact swVal_range hm n _
  · intro n
    rw [sweepX_junction hm hS, swVal_last hm hS]
  · intro p₁ p₂ p₃ h12 h23 hlo hhi e1 e2 e3
    have ev : ∀ p : ℤ, (swB m (p / 3) ≠ swB m ((p - 1) / 3) ∨
        swT m (p / 3) ≠ swT m ((p - 1) / 3)) → p % 3 = 0 := by
      intro p hp
      by_contra hc
      have : p / 3 = (p - 1) / 3 := by omega
      rcases hp with h | h <;> exact h (by rw [this])
    have q1 := ev p₁ e1
    have q2 := ev p₂ e2
    have q3 := ev p₃ e3
    have h13 : p₁ + 6 ≤ p₃ := by omega
    have hQ : ((sweepQ m S / 2 + 3 : ℕ) : ℤ) = 3 * sweepL m S + 3 := by
      rw [sweepQ_eq]; push_cast; omega
    rw [hQ] at hhi
    have : (p₁ + 6) * (sweepL m S : ℤ) ≤ p₃ * sweepL m S := by nlinarith
    have : (4 : ℤ) ≤ sweepL m S := by exact_mod_cast hL4
    nlinarith

/-- **The sweep pattern** (commission 202 §4.2–4.3): period; unit steps; `S`-slow; nesting
(window radius `m/2 − 1/4`); survival; crookedness on every window of `Q/2 + 4` indices. -/
theorem exists_sweepPattern (m S : ℕ) (hm : 5 ≤ m) (hS : 1 ≤ S) :
    ∃ x : ℤ → ℤ,
      (∀ t : ℤ, x (t + sweepQ m S) = x t + 1) ∧
      (∀ t, |x (t + 1) - x t| ≤ 1) ∧
      (∀ s t, x s + 2 ≤ x t → (S : ℤ) ≤ |s - t|) ∧
      (∀ t, |(x t : ℝ) - (1 / 4 + (t : ℝ) / sweepQ m S)| ≤ (m : ℝ) / 2 - 1 / 4) ∧
      (∀ (l : ℤ) (y : ℝ), |y - l| ≤ (m : ℝ) / 2 - 1 / 2 →
        ∃ t, x t = l ∧
          |y - (1 / 4 + (t : ℝ) / sweepQ m S)| ≤ 1 / 4 - 1 / (2 * (sweepQ m S : ℝ))) ∧
      (∀ a : ℤ, HPC.Fold.PatCrookedOn (fun u : ℕ => x (a + u)) 0 (sweepQ m S / 2 + 3)) :=
  ⟨sweepX m S, sweepX_period hm hS, sweepX_step hm hS, sweepX_slow hm hS, sweepX_nest hm hS,
    sweepX_surv hm hS, sweepX_crook hm hS⟩

end Props

end HPC.BJ59
