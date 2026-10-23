import Mathlib

/-!
# Joint positions of a fine chain following a slow pattern

Batch 84, the combinatorial core of the planar step. For a pattern `x : Fin n → Fin m` with unit
steps which is `N`-*slow* (values two apart are taken at indices at least `N` apart), we place the
*joint* `t` (between fine links `t - 1` and `t`, `0 ≤ t ≤ n`) at a horizontal position `P t` in
the coordinates of the standard coarse chain `(2j, 2j+3) × (0,1)`:

* a *transition* joint (the pattern changes from `j` to `j ± 1`) sits in the middle of the
  overlap of the two coarse links, at `2 min + 5/2`;
* a *stay* joint (value `j` on both sides) sits in the private part `[2j + 5/4, 2j + 7/4]`, at
  `2j + 3/2 + f/4` where `f = (ℓ - r)/(ℓ + r)`, with `ℓ`, `r` the distances to the nearest links
  of value `j - 1`, `j + 1` (capped at `2N`).

Fine link `t` will span horizontally from `P t` to `P (t+1)`. The results `link_bounds`,
`link_tight`, `link_small`, `link_first`, `link_last` are what the construction needs.
-/

namespace HPC.Plane.Joints

open Finset

variable {n m : ℕ} (x : Fin n → Fin m) (N : ℕ)

/-- The pattern extended to all of `ℕ` (constant after the last index). -/
def xe (t : ℕ) : ℤ :=
  if h : t < n then (x ⟨t, h⟩ : ℤ) else if h2 : 0 < n then (x ⟨n - 1, by omega⟩ : ℤ) else 0

/-- Doubled distance from joint `t` to (the centre of) link `s`. -/
def dd (t s : ℕ) : ℕ := Int.natAbs (2 * (s : ℤ) + 1 - 2 * t)

/-- Doubled distance from joint `t` to the nearest link of value `v`, capped at `2N`. -/
def dv (t : ℕ) (v : ℤ) : ℕ :=
  (univ.filter (fun s : Fin n => (x s : ℤ) = v)).fold min (2 * N) (fun s : Fin n => dd t s)

/-- The stay coordinate `(ℓ - r)/(ℓ + r)`. -/
noncomputable def fpos (t : ℕ) : ℝ :=
  (((dv x N t (xe x t - 1) : ℕ) : ℝ) - (dv x N t (xe x t + 1) : ℕ)) /
    (((dv x N t (xe x t - 1) : ℕ) : ℝ) + (dv x N t (xe x t + 1) : ℕ))

/-- The horizontal position of joint `t`. -/
noncomputable def P (t : ℕ) : ℝ :=
  if xe x (t - 1) = xe x t then 2 * (xe x t : ℝ) + 3 / 2 + fpos x N t / 4
  else 2 * (min (xe x (t - 1)) (xe x t) : ℝ) + 5 / 2

/-- Unit steps. -/
def UnitSteps : Prop := ∀ t t' : Fin n, t'.val = t.val + 1 → ((x t' : ℤ) - (x t : ℤ)).natAbs ≤ 1

/-- `N`-slow: values at least two apart are taken at indices at least `N` apart. -/
def Slow : Prop := ∀ s s' : Fin n, (x s : ℤ) + 2 ≤ x s' → N ≤ ((s : ℤ) - (s' : ℤ)).natAbs

variable {x N}

/-! ### The extended pattern -/

theorem xe_of_lt {t : ℕ} (h : t < n) : xe x t = x ⟨t, h⟩ := by simp [xe, h]

theorem xe_nonneg (t : ℕ) : 0 ≤ xe x t := by
  unfold xe; split_ifs <;> simp

theorem xe_lt (t : ℕ) (hm : 0 < m) : xe x t < m := by
  unfold xe; split_ifs <;> simp [hm]

theorem xe_eq_of_ge (hn : 0 < n) {t : ℕ} (h : n - 1 ≤ t) : xe x t = xe x (n - 1) := by
  unfold xe
  by_cases ht : t < n
  · have : t = n - 1 := by omega
    subst this; rfl
  · simp [ht, hn, show n - 1 < n by omega]

theorem xe_step (hx : UnitSteps x) (t : ℕ) : |xe x (t + 1) - xe x t| ≤ 1 := by
  by_cases h : t + 1 < n
  · rw [xe_of_lt h, xe_of_lt (by omega : t < n)]
    have := hx ⟨t, by omega⟩ ⟨t + 1, h⟩ rfl
    rw [abs_le]; omega
  · by_cases hn : 0 < n
    · rw [xe_eq_of_ge hn (by omega : n - 1 ≤ t + 1), xe_eq_of_ge hn (by omega : n - 1 ≤ t)]; simp
    · have : n = 0 := by omega
      subst this; simp [xe]

theorem xe_step' (hx : UnitSteps x) (t : ℕ) :
    xe x (t - 1) = xe x t ∨ xe x (t - 1) = xe x t + 1 ∨ xe x (t - 1) + 1 = xe x t := by
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp
  · have := xe_step hx (t - 1)
    rw [show t - 1 + 1 = t by omega, abs_le] at this
    omega

/-! ### Distances -/

theorem dv_le_cap (t : ℕ) (v : ℤ) : dv x N t v ≤ 2 * N := by
  unfold dv; rw [Finset.fold_min_le]; left; exact le_rfl

theorem dv_le {t : ℕ} {v : ℤ} (s : Fin n) (hs : (x s : ℤ) = v) : dv x N t v ≤ dd t s := by
  unfold dv; rw [Finset.fold_min_le]; right; exact ⟨s, by simp [hs], le_rfl⟩

theorem dv_cases (t : ℕ) (v : ℤ) :
    dv x N t v = 2 * N ∨ ∃ s : Fin n, (x s : ℤ) = v ∧ dd t s ≤ dv x N t v := by
  have h := (Finset.fold_min_le (s := univ.filter (fun s : Fin n => (x s : ℤ) = v))
    (f := fun s : Fin n => dd t s) (b := 2 * N) (c := dv x N t v)).mp le_rfl
  rcases h with h | ⟨s, hs, h⟩
  · left; exact le_antisymm (dv_le_cap t v) h
  · right; exact ⟨s, by simpa using hs, h⟩

theorem dd_succ_le (t s : ℕ) : dd (t + 1) s ≤ dd t s + 2 := by
  unfold dd; push_cast; omega

theorem dd_le_succ (t s : ℕ) : dd t s ≤ dd (t + 1) s + 2 := by
  unfold dd; push_cast; omega

theorem dv_succ_le (t : ℕ) (v : ℤ) : dv x N (t + 1) v ≤ dv x N t v + 2 := by
  rcases dv_cases (x := x) (N := N) t v with h | ⟨s, hs, h⟩
  · have := dv_le_cap (x := x) (N := N) (t + 1) v; omega
  · have := dv_le (N := N) (t := t + 1) s hs
    have := dd_succ_le t s; omega

theorem dv_le_succ (t : ℕ) (v : ℤ) : dv x N t v ≤ dv x N (t + 1) v + 2 := by
  rcases dv_cases (x := x) (N := N) (t + 1) v with h | ⟨s, hs, h⟩
  · have := dv_le_cap (x := x) (N := N) t v; omega
  · have := dv_le (N := N) (t := t) s hs
    have := dd_le_succ t s; omega

/-- Slowness bounds the sum of the two distances from below. -/
theorem dv_sum_ge (hs : Slow x N) (t : ℕ) (j : ℤ) :
    2 * N ≤ dv x N t (j - 1) + dv x N t (j + 1) := by
  rcases dv_cases (x := x) (N := N) t (j - 1) with h1 | ⟨s1, hs1, h1⟩
  · omega
  rcases dv_cases (x := x) (N := N) t (j + 1) with h2 | ⟨s2, hs2, h2⟩
  · omega
  have := hs s1 s2 (by omega)
  have e1 : dd t s1 + dd t s2 ≥ 2 * ((s1 : ℤ) - (s2 : ℤ)).natAbs := by unfold dd; omega
  omega

theorem dv_neg_one (t : ℕ) : dv x N t (-1) = 2 * N := by
  rcases dv_cases (x := x) (N := N) t (-1) with h | ⟨s, hs, -⟩
  · exact h
  · have : (0 : ℤ) ≤ (x s : ℤ) := by positivity
    omega

theorem dv_top (t : ℕ) : dv x N t (m : ℤ) = 2 * N := by
  rcases dv_cases (x := x) (N := N) t (m : ℤ) with h | ⟨s, hs, -⟩
  · exact h
  · have : ((x s : ℕ) : ℤ) < m := by exact_mod_cast (x s).isLt
    omega

/-! ### The stay coordinate -/

section fpos

variable (hs : Slow x N) (hN : 1 ≤ N)
include hs hN

theorem sum_pos (t : ℕ) :
    (0 : ℝ) < (dv x N t (xe x t - 1) : ℝ) + (dv x N t (xe x t + 1) : ℝ) := by
  have := dv_sum_ge hs t (xe x t)
  have h : (2 : ℝ) * N ≤ (dv x N t (xe x t - 1) : ℝ) + (dv x N t (xe x t + 1) : ℝ) := by
    exact_mod_cast this
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

theorem fpos_bounds (t : ℕ) : -1 ≤ fpos x N t ∧ fpos x N t ≤ 1 := by
  have hp := sum_pos hs hN t
  unfold fpos
  set a := (dv x N t (xe x t - 1) : ℝ)
  set b := (dv x N t (xe x t + 1) : ℝ)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  constructor
  · rw [le_div_iff₀ hp]; linarith
  · rw [div_le_iff₀ hp]; linarith

/-- Near a link of value `j + 1`, the stay coordinate is close to `1`. -/
theorem fpos_ge_of_near (t : ℕ) (hr : dv x N t (xe x t + 1) ≤ 3) :
    1 - 3 / (N : ℝ) ≤ fpos x N t := by
  have hp := sum_pos hs hN t
  have hsum : (2 : ℝ) * N ≤ (dv x N t (xe x t - 1) : ℝ) + (dv x N t (xe x t + 1) : ℝ) := by
    exact_mod_cast dv_sum_ge hs t (xe x t)
  have hr' : (dv x N t (xe x t + 1) : ℝ) ≤ 3 := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold fpos
  set a := (dv x N t (xe x t - 1) : ℝ)
  set b := (dv x N t (xe x t + 1) : ℝ)
  have hb : 0 ≤ b := by positivity
  rw [le_div_iff₀ hp]
  have h3 : 3 / (N : ℝ) * (a + b) ≥ 3 / (N : ℝ) * (2 * N) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have h4 : 3 / (N : ℝ) * (2 * N) = 6 := by field_simp; ring
  nlinarith

/-- Near a link of value `j - 1`, the stay coordinate is close to `-1`. -/
theorem fpos_le_of_near (t : ℕ) (hl : dv x N t (xe x t - 1) ≤ 3) :
    fpos x N t ≤ -1 + 3 / (N : ℝ) := by
  have hp := sum_pos hs hN t
  have hsum : (2 : ℝ) * N ≤ (dv x N t (xe x t - 1) : ℝ) + (dv x N t (xe x t + 1) : ℝ) := by
    exact_mod_cast dv_sum_ge hs t (xe x t)
  have hl' : (dv x N t (xe x t - 1) : ℝ) ≤ 3 := by exact_mod_cast hl
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold fpos
  set a := (dv x N t (xe x t - 1) : ℝ)
  set b := (dv x N t (xe x t + 1) : ℝ)
  have ha : 0 ≤ a := by positivity
  rw [div_le_iff₀ hp]
  have h3 : 3 / (N : ℝ) * (a + b) ≥ 3 / (N : ℝ) * (2 * N) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have h4 : 3 / (N : ℝ) * (2 * N) = 6 := by field_simp; ring
  nlinarith

/-- Consecutive stay coordinates with the same value differ by at most `2 / N`. -/
theorem fpos_step (t : ℕ) (he : xe x (t + 1) = xe x t) :
    |fpos x N (t + 1) - fpos x N t| ≤ 2 / (N : ℝ) := by
  have hp := sum_pos hs hN t
  have hp' := sum_pos hs hN (t + 1)
  have hsum' : (2 : ℝ) * N ≤ (dv x N (t + 1) (xe x (t + 1) - 1) : ℝ) +
      (dv x N (t + 1) (xe x (t + 1) + 1) : ℝ) := by
    exact_mod_cast dv_sum_ge hs (t + 1) (xe x (t + 1))
  unfold fpos
  rw [he] at hp' hsum' ⊢
  have l1 := dv_succ_le (x := x) (N := N) t (xe x t - 1)
  have l2 := dv_le_succ (x := x) (N := N) t (xe x t - 1)
  have r1 := dv_succ_le (x := x) (N := N) t (xe x t + 1)
  have r2 := dv_le_succ (x := x) (N := N) t (xe x t + 1)
  set a := (dv x N t (xe x t - 1) : ℕ)
  set b := (dv x N t (xe x t + 1) : ℕ)
  set a' := (dv x N (t + 1) (xe x t - 1) : ℕ)
  set b' := (dv x N (t + 1) (xe x t + 1) : ℕ)
  have l1' : (a' : ℝ) ≤ a + 2 := by exact_mod_cast l1
  have l2' : (a : ℝ) ≤ a' + 2 := by exact_mod_cast l2
  have r1' : (b' : ℝ) ≤ b + 2 := by exact_mod_cast r1
  have r2' : (b : ℝ) ≤ b' + 2 := by exact_mod_cast r2
  have ha : (0 : ℝ) ≤ a := by positivity
  have hb : (0 : ℝ) ≤ b := by positivity
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_sub_div _ _ hp'.ne' hp.ne', abs_div, abs_of_pos (mul_pos hp' hp), div_le_div_iff₀
    (mul_pos hp' hp) (by positivity)]
  have key : |((a' : ℝ) - b') * (a + b) - (a' + b') * (a - b)| ≤ 4 * (a + b) := by
    have e : ((a' : ℝ) - b') * (a + b) - (a' + b') * (a - b) = 2 * ((a' - a) * b - a * (b' - b)) := by
      ring
    rw [e, abs_le]
    constructor <;> nlinarith
  calc |((a' : ℝ) - b') * (a + b) - (a' + b') * (a - b)| * N ≤ 4 * (a + b) * N :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = 2 * ((2 * N) * (a + b)) := by ring
    _ ≤ 2 * ((a' + b') * (a + b)) := by
        have := mul_le_mul_of_nonneg_right hsum' hp.le
        linarith

end fpos

/-! ### Positions of joints -/

section positions

theorem P_stay {t : ℕ} (h : xe x (t - 1) = xe x t) :
    P x N t = 2 * (xe x t : ℝ) + 3 / 2 + fpos x N t / 4 := by
  simp [P, h]

theorem P_up {t : ℕ} (h : xe x (t - 1) = xe x t + 1) :
    P x N t = 2 * (xe x t : ℝ) + 5 / 2 := by
  have hne : xe x (t - 1) ≠ xe x t := by omega
  simp only [P, hne, if_false]
  rw [min_eq_right (by exact_mod_cast (show xe x t ≤ xe x (t - 1) by omega))]

theorem P_down {t : ℕ} (h : xe x (t - 1) + 1 = xe x t) :
    P x N t = 2 * (xe x t : ℝ) + 1 / 2 := by
  have hne : xe x (t - 1) ≠ xe x t := by omega
  simp only [P, hne, if_false]
  rw [min_eq_left (by exact_mod_cast (show xe x (t - 1) ≤ xe x t by omega))]
  have : ((xe x (t - 1) : ℤ) : ℝ) = (xe x t : ℝ) - 1 := by
    rw [← h]; push_cast; ring
  rw [this]; ring

variable (hs : Slow x N) (hN : 12 ≤ N)
include hs hN

theorem P_stay_bounds {t : ℕ} (h : xe x (t - 1) = xe x t) :
    2 * (xe x t : ℝ) + 5 / 4 ≤ P x N t ∧ P x N t ≤ 2 * (xe x t : ℝ) + 7 / 4 := by
  rw [P_stay h]
  have := fpos_bounds hs (by omega) t
  constructor <;> linarith [this.1, this.2]

theorem P_stay_near_up {t : ℕ} (h : xe x (t - 1) = xe x t) (s : Fin n)
    (hsv : (x s : ℤ) = xe x t + 1) (hd : dd t s ≤ 3) :
    2 * (xe x t : ℝ) + 7 / 4 - 3 / (4 * N) ≤ P x N t := by
  rw [P_stay h]
  have := fpos_ge_of_near hs (by omega) t ((dv_le s hsv).trans hd)
  have e : 3 / (4 * (N : ℝ)) = (3 / N) / 4 := by field_simp
  rw [e]; linarith

theorem P_stay_near_down {t : ℕ} (h : xe x (t - 1) = xe x t) (s : Fin n)
    (hsv : (x s : ℤ) = xe x t - 1) (hd : dd t s ≤ 3) :
    P x N t ≤ 2 * (xe x t : ℝ) + 5 / 4 + 3 / (4 * N) := by
  rw [P_stay h]
  have := fpos_le_of_near hs (by omega) t ((dv_le s hsv).trans hd)
  have e : 3 / (4 * (N : ℝ)) = (3 / N) / 4 := by field_simp
  rw [e]; linarith

theorem P_stay_step {t : ℕ} (h0 : xe x (t - 1) = xe x t) (h1 : xe x t = xe x (t + 1)) :
    |P x N (t + 1) - P x N t| ≤ 1 / (2 * N) := by
  rw [P_stay h0, P_stay (t := t + 1) (by simpa using h1), ← h1]
  have := fpos_step hs (by omega) t h1.symm
  have e : 1 / (2 * (N : ℝ)) = (2 / N) / 4 := by field_simp; ring
  rw [e]
  rw [show 2 * (xe x t : ℝ) + 3 / 2 + fpos x N (t + 1) / 4 - (2 * (xe x t : ℝ) + 3 / 2 +
      fpos x N t / 4) = (fpos x N (t + 1) - fpos x N t) / 4 by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  gcongr

theorem fpos_nonneg_of_bottom {t : ℕ} (h : xe x t = 0) : 0 ≤ fpos x N t := by
  have hp := sum_pos hs (by omega) t
  unfold fpos
  rw [h] at hp ⊢
  simp only [zero_sub, zero_add] at hp ⊢
  rw [dv_neg_one] at hp ⊢
  apply div_nonneg _ hp.le
  have := dv_le_cap (x := x) (N := N) t 1
  have : ((dv x N t 1 : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast this
  linarith

theorem fpos_nonpos_of_top {t : ℕ} (h : xe x t = (m : ℤ) - 1) : fpos x N t ≤ 0 := by
  have hp := sum_pos hs (by omega) t
  unfold fpos
  rw [h] at hp ⊢
  simp only [sub_add_cancel] at hp ⊢
  rw [dv_top] at hp ⊢
  apply div_nonpos_of_nonpos_of_nonneg _ hp.le
  have := dv_le_cap (x := x) (N := N) t ((m : ℤ) - 1 - 1)
  have : ((dv x N t ((m : ℤ) - 1 - 1) : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast this
  linarith

end positions

/-! ### Links -/

section links

variable (hx : UnitSteps x) (hs : Slow x N) (hN : 12 ≤ N)
include hx hs hN

omit hx hs hN in
theorem int_le_of_lt {a b : ℤ} {c : ℝ} (hc : c ≤ 2) (h : 2 * (a : ℝ) < 2 * b + c) : a ≤ b := by
  by_contra hne
  have : b + 1 ≤ a := by omega
  have : (b : ℝ) + 1 ≤ a := by exact_mod_cast this
  linarith

omit hx hs hN in
theorem int_ge_of_lt {a b : ℤ} {c : ℝ} (hc : c ≤ 2) (h : 2 * (b : ℝ) + 1 - c < 2 * a + 3) :
    b - 1 ≤ a := by
  by_contra hne
  have : a + 2 ≤ b := by omega
  have : (a : ℝ) + 2 ≤ b := by exact_mod_cast this
  linarith

/-- The six shapes of a link. -/
theorem link_cases {t : ℕ} (ht : t < n) :
    (xe x (t - 1) = xe x t ∧ xe x t = xe x (t + 1) ∧
      |P x N (t + 1) - P x N t| ≤ 1 / (2 * N)) ∨
    (1 ≤ t ∧ xe x (t - 1) = xe x t + 1 ∧ xe x t = xe x (t + 1) ∧
      P x N t = 2 * (xe x t : ℝ) + 5 / 2 ∧
      2 * (xe x t : ℝ) + 7 / 4 - 3 / (4 * N) ≤ P x N (t + 1)) ∨
    (1 ≤ t ∧ xe x (t - 1) + 1 = xe x t ∧ xe x t = xe x (t + 1) ∧
      P x N t = 2 * (xe x t : ℝ) + 1 / 2 ∧
      P x N (t + 1) ≤ 2 * (xe x t : ℝ) + 5 / 4 + 3 / (4 * N)) ∨
    (t + 1 < n ∧ xe x (t - 1) = xe x t ∧ xe x t + 1 = xe x (t + 1) ∧
      2 * (xe x t : ℝ) + 7 / 4 - 3 / (4 * N) ≤ P x N t ∧
      P x N (t + 1) = 2 * (xe x t : ℝ) + 5 / 2) ∨
    (t + 1 < n ∧ xe x (t - 1) = xe x t ∧ xe x t = xe x (t + 1) + 1 ∧
      P x N t ≤ 2 * (xe x t : ℝ) + 5 / 4 + 3 / (4 * N) ∧
      P x N (t + 1) = 2 * (xe x t : ℝ) + 1 / 2) ∨
    (1 ≤ t ∧ t + 1 < n ∧ xe x (t - 1) = xe x (t + 1) ∧ xe x (t - 1) ≠ xe x t ∧
      P x N t = P x N (t + 1)) := by
  have hn : 0 < n := by omega
  have j0 := xe_step' hx t
  have j1 := xe_step' hx (t + 1)
  simp only [Nat.add_sub_cancel] at j1
  -- a transition at joint `t` forces `1 ≤ t`
  have ht0 : xe x (t - 1) ≠ xe x t → 1 ≤ t := by
    intro h; rcases Nat.eq_zero_or_pos t with e | e
    · subst e; simp at h
    · exact e
  -- a transition at joint `t + 1` forces `t + 1 < n`
  have ht1 : xe x t ≠ xe x (t + 1) → t + 1 < n := by
    intro h; by_contra hc
    exact h (by rw [xe_eq_of_ge hn (by omega : n - 1 ≤ t), xe_eq_of_ge hn (by omega : n - 1 ≤ t + 1)])
  rcases j0 with a | a | a <;> rcases j1 with b | b | b
  · left; exact ⟨a, b, P_stay_step hs hN a b⟩
  · -- stay, then down
    have h1 := ht1 (by omega)
    right; right; right; right; left
    refine ⟨h1, a, b, ?_, ?_⟩
    · refine P_stay_near_down hs hN a ⟨t + 1, h1⟩ ?_ ?_
      · rw [← xe_of_lt h1]; omega
      · simp [dd]; omega
    · have := P_up (x := x) (N := N) (t := t + 1) (by simpa using b)
      rw [this, show (xe x (t + 1) : ℝ) = (xe x t : ℝ) - 1 by
        rw [show xe x t = xe x (t + 1) + 1 from b]; push_cast; ring]
      ring
  · -- stay, then up
    have h1 := ht1 (by omega)
    right; right; right; left
    refine ⟨h1, a, b, ?_, ?_⟩
    · refine P_stay_near_up hs hN a ⟨t + 1, h1⟩ ?_ ?_
      · rw [← xe_of_lt h1]; omega
      · simp [dd]; omega
    · have := P_down (x := x) (N := N) (t := t + 1) (by simpa using b)
      rw [this, ← b]; push_cast; ring
  · -- up (coming from above), then stay
    have h0 := ht0 (by omega)
    right; left
    refine ⟨h0, a, b, P_up a, ?_⟩
    have hb : xe x (t + 1 - 1) = xe x (t + 1) := by simpa using b
    have := P_stay_near_up hs hN hb ⟨t - 1, by omega⟩ ?_ ?_
    · rw [← b] at this; exact this
    · rw [← xe_of_lt (by omega : t - 1 < n), ← b, a]
    · simp [dd]; omega
  · -- from above, then down: impossible
    exfalso
    have h0 := ht0 (by omega)
    have h1 := ht1 (by omega)
    have := hs ⟨t + 1, h1⟩ ⟨t - 1, by omega⟩ (by
      rw [← xe_of_lt h1, ← xe_of_lt (by omega : t - 1 < n)]; omega)
    simp at this; omega
  · -- from above, then up: turning
    have h0 := ht0 (by omega)
    have h1 := ht1 (by omega)
    right; right; right; right; right
    refine ⟨h0, h1, by omega, by omega, ?_⟩
    rw [P_up a, P_down (t := t + 1) (by simpa using b), ← b]; push_cast; ring
  · -- from below, then stay
    have h0 := ht0 (by omega)
    right; right; left
    refine ⟨h0, a, b, P_down a, ?_⟩
    have hb : xe x (t + 1 - 1) = xe x (t + 1) := by simpa using b
    have := P_stay_near_down hs hN hb ⟨t - 1, by omega⟩ ?_ ?_
    · rw [← b] at this; exact this
    · rw [← xe_of_lt (by omega : t - 1 < n), ← b]; omega
    · simp [dd]; omega
  · -- from below, then down: turning
    have h0 := ht0 (by omega)
    have h1 := ht1 (by omega)
    right; right; right; right; right
    refine ⟨h0, h1, by omega, by omega, ?_⟩
    rw [P_down a, P_up (t := t + 1) (by simpa using b)]
    rw [show (xe x (t + 1) : ℝ) = (xe x t : ℝ) - 1 by
        rw [show xe x t = xe x (t + 1) + 1 from b]; push_cast; ring]
    ring
  · -- from below, then up: impossible
    exfalso
    have h0 := ht0 (by omega)
    have h1 := ht1 (by omega)
    have := hs ⟨t - 1, by omega⟩ ⟨t + 1, h1⟩ (by
      rw [← xe_of_lt h1, ← xe_of_lt (by omega : t - 1 < n)]; omega)
    simp at this; omega

omit hx hs hN in
theorem le_of_two_lt {a b : ℤ} {c : ℝ} (hc : c ≤ 2) (h : 2 * (a : ℝ) < 2 * b + c) : a ≤ b := by
  by_contra hne
  have : b + 1 ≤ a := by omega
  have : (b : ℝ) + 1 ≤ a := by exact_mod_cast this
  linarith

omit hx hs hN in
theorem ge_of_two_lt {a b : ℤ} {c : ℝ} (hc : c ≤ 2) (h : 2 * (b : ℝ) - c < 2 * a) : b ≤ a := by
  by_contra hne
  have : a + 1 ≤ b := by omega
  have : (a : ℝ) + 1 ≤ b := by exact_mod_cast this
  linarith

/-- Everything the planar step needs about fine link `t`: its horizontal span
`[min (P t) (P (t+1)), max (P t) (P (t+1))]` lies well inside coarse link `x t`; enlarged by
`1/10` it meets only coarse links named by `x` at `t - 1`, `t`, `t + 1`; and it is either short
or inside an overlap zone. -/
theorem link_facts {t : ℕ} (ht : t < n) :
    (2 * (xe x t : ℝ) + 1 / 2 ≤ min (P x N t) (P x N (t + 1)) ∧
      max (P x N t) (P x N (t + 1)) ≤ 2 * (xe x t : ℝ) + 5 / 2) ∧
    (∀ l : ℕ, 2 * (l : ℝ) < max (P x N t) (P x N (t + 1)) + 1 / 10 →
      min (P x N t) (P x N (t + 1)) - 1 / 10 < 2 * l + 3 →
      ∃ t' : Fin n, (t'.val ≤ t + 1 ∧ t ≤ t'.val + 1) ∧ (l : ℤ) = x t') ∧
    (max (P x N t) (P x N (t + 1)) - min (P x N t) (P x N (t + 1)) ≤ 1 / (2 * N) ∨
      ∃ k : ℕ, 2 * (k : ℝ) + 8 / 5 + 1 / 20 ≤ min (P x N t) (P x N (t + 1)) ∧
        max (P x N t) (P x N (t + 1)) ≤ 2 * (k : ℝ) + 17 / 5 - 1 / 20) := by
  have hn : 0 < n := by omega
  have hN' : (12 : ℝ) ≤ N := by exact_mod_cast hN
  have h34 : 3 / (4 * (N : ℝ)) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hN2 : 0 < 1 / (2 * (N : ℝ)) := by positivity
  have hj0 : 0 ≤ xe x t := xe_nonneg t
  have xt : (x ⟨t, ht⟩ : ℤ) = xe x t := (xe_of_lt ht).symm
  -- generic closing of the tightness clause from explicit bounds
  have tight_of : ∀ (lo hi : ℝ) (a b : ℤ) (ta tb : Fin n),
      (ta.val ≤ t + 1 ∧ t ≤ ta.val + 1) → (tb.val ≤ t + 1 ∧ t ≤ tb.val + 1) →
      (x ta : ℤ) = a → (x tb : ℤ) = b → b = a + 1 →
      hi ≤ 2 * (b : ℝ) + 19 / 10 → 2 * (a : ℝ) + 11 / 10 ≤ lo →
      ∀ l : ℕ, 2 * (l : ℝ) < hi + 1 / 10 → lo - 1 / 10 < 2 * l + 3 →
      ∃ t' : Fin n, (t'.val ≤ t + 1 ∧ t ≤ t'.val + 1) ∧ (l : ℤ) = x t' := by
    intro lo hi a b ta tb hta htb ha hb hab hhi hlo l hl1 hl2
    have u1 : (l : ℤ) ≤ b := le_of_two_lt (c := 2) (by norm_num) (by push_cast; linarith)
    have u2 : a ≤ (l : ℤ) := ge_of_two_lt (c := 2) (by norm_num) (by push_cast; linarith)
    rcases (show (l : ℤ) = a ∨ (l : ℤ) = b by omega) with e | e
    · exact ⟨ta, hta, by rw [e, ha]⟩
    · exact ⟨tb, htb, by rw [e, hb]⟩
  have self : (t ≤ t + 1 ∧ t ≤ t + 1) := ⟨by omega, by omega⟩
  rcases link_cases hx hs hN ht with
    ⟨a, b, hd⟩ | ⟨t1, a, b, e0, e1⟩ | ⟨t1, a, b, e0, e1⟩ | ⟨t1, a, b, e0, e1⟩ |
      ⟨t1, a, b, e0, e1⟩ | ⟨t1, t2, a, b, e⟩
  · -- stay, stay
    have b0 := P_stay_bounds hs hN a
    have b1 := P_stay_bounds hs hN (t := t + 1) (by simpa using b)
    rw [← b] at b1
    have hlo : 2 * (xe x t : ℝ) + 5 / 4 ≤ min (P x N t) (P x N (t + 1)) := le_min b0.1 b1.1
    have hhi : max (P x N t) (P x N (t + 1)) ≤ 2 * (xe x t : ℝ) + 7 / 4 := max_le b0.2 b1.2
    refine ⟨⟨by linarith, by linarith⟩, ?_, Or.inl ?_⟩
    · intro l hl1 hl2
      have u1 : (l : ℤ) ≤ xe x t := le_of_two_lt (c := 37 / 20) (by norm_num) (by push_cast; linarith)
      have u2 : xe x t ≤ (l : ℤ) := ge_of_two_lt (c := 37 / 20) (by norm_num) (by push_cast; linarith)
      exact ⟨⟨t, ht⟩, self, by rw [xt]; omega⟩
    · rcases le_total (P x N t) (P x N (t + 1)) with h | h
      · rw [max_eq_right h, min_eq_left h]; rw [abs_le] at hd; linarith
      · rw [max_eq_left h, min_eq_right h]; rw [abs_le] at hd; linarith
  · -- from above, stay
    have b1 := P_stay_bounds hs hN (t := t + 1) (by simpa using b)
    rw [← b] at b1
    have hmin : min (P x N t) (P x N (t + 1)) = P x N (t + 1) := min_eq_right (by linarith)
    have hmax : max (P x N t) (P x N (t + 1)) = P x N t := max_eq_left (by linarith)
    rw [hmin, hmax]
    refine ⟨⟨by linarith, by linarith⟩, ?_, Or.inr ?_⟩
    · exact tight_of _ _ (xe x t) (xe x t + 1) ⟨t, ht⟩ ⟨t - 1, by omega⟩ self ⟨by simp; omega, by simp; omega⟩
        xt (by rw [← xe_of_lt (by omega : t - 1 < n)]; omega) rfl (by push_cast; linarith) (by linarith)
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hj0
      have hk' : (xe x t : ℝ) = k := by rw [hk]; rfl
      exact ⟨k, by rw [← hk']; linarith, by rw [← hk']; linarith⟩
  · -- from below, stay
    have b1 := P_stay_bounds hs hN (t := t + 1) (by simpa using b)
    rw [← b] at b1
    have hmin : min (P x N t) (P x N (t + 1)) = P x N t := min_eq_left (by linarith)
    have hmax : max (P x N t) (P x N (t + 1)) = P x N (t + 1) := max_eq_right (by linarith)
    rw [hmin, hmax]
    have hj1 : 0 ≤ xe x t - 1 := by have := xe_nonneg (x := x) (t - 1); omega
    refine ⟨⟨by linarith, by linarith⟩, ?_, Or.inr ?_⟩
    · exact tight_of _ _ (xe x t - 1) (xe x t) ⟨t - 1, by omega⟩ ⟨t, ht⟩ ⟨by simp; omega, by simp; omega⟩ self
        (by rw [← xe_of_lt (by omega : t - 1 < n)]; omega) xt (by ring)
        (by linarith) (by push_cast; linarith)
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hj1
      have hk' : (xe x t : ℝ) - 1 = k := by
        have : ((xe x t - 1 : ℤ) : ℝ) = (k : ℝ) := by rw [hk]; rfl
        push_cast at this; exact this
      exact ⟨k, by rw [← hk']; linarith, by rw [← hk']; linarith⟩
  · -- stay, then up
    have b0 := P_stay_bounds hs hN a
    have hmin : min (P x N t) (P x N (t + 1)) = P x N t := min_eq_left (by linarith)
    have hmax : max (P x N t) (P x N (t + 1)) = P x N (t + 1) := max_eq_right (by linarith)
    rw [hmin, hmax]
    refine ⟨⟨by linarith, by linarith⟩, ?_, Or.inr ?_⟩
    · exact tight_of _ _ (xe x t) (xe x t + 1) ⟨t, ht⟩ ⟨t + 1, t1⟩ self ⟨le_refl _, by show t ≤ t + 1 + 1; omega⟩
        xt (by rw [← xe_of_lt t1]; omega) rfl (by push_cast; linarith) (by linarith)
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hj0
      have hk' : (xe x t : ℝ) = k := by rw [hk]; rfl
      exact ⟨k, by rw [← hk']; linarith, by rw [← hk']; linarith⟩
  · -- stay, then down
    have b0 := P_stay_bounds hs hN a
    have hmin : min (P x N t) (P x N (t + 1)) = P x N (t + 1) := min_eq_right (by linarith)
    have hmax : max (P x N t) (P x N (t + 1)) = P x N t := max_eq_left (by linarith)
    rw [hmin, hmax]
    have hj1 : 0 ≤ xe x t - 1 := by
      have := xe_nonneg (x := x) (t + 1); omega
    refine ⟨⟨by linarith, by linarith⟩, ?_, Or.inr ?_⟩
    · exact tight_of _ _ (xe x t - 1) (xe x t) ⟨t + 1, t1⟩ ⟨t, ht⟩ ⟨le_refl _, by show t ≤ t + 1 + 1; omega⟩ self
        (by rw [← xe_of_lt t1]; omega) xt (by ring)
        (by linarith) (by push_cast; linarith)
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hj1
      have hk' : (xe x t : ℝ) - 1 = k := by
        have : ((xe x t - 1 : ℤ) : ℝ) = (k : ℝ) := by rw [hk]; rfl
        push_cast at this; exact this
      exact ⟨k, by rw [← hk']; linarith, by rw [← hk']; linarith⟩
  · -- turning
    rw [← e, min_self, max_self]
    have hprev := xe_step' hx t
    have hm1 : (x ⟨t - 1, by omega⟩ : ℤ) = xe x (t - 1) := (xe_of_lt (by omega)).symm
    have hp1 : (x ⟨t + 1, t2⟩ : ℤ) = xe x (t + 1) := (xe_of_lt t2).symm
    rcases hprev with c | c | c
    · exact absurd c b
    · rw [P_up c]
      refine ⟨⟨by linarith, by linarith⟩, ?_, Or.inl (by rw [sub_self]; positivity)⟩
      exact tight_of _ _ (xe x t) (xe x t + 1) ⟨t, ht⟩ ⟨t - 1, by omega⟩ self ⟨by simp; omega, by simp; omega⟩
        xt (by rw [hm1]; omega) rfl (by push_cast; linarith) (by linarith)
    · rw [P_down c]
      refine ⟨⟨by linarith, by linarith⟩, ?_, Or.inl (by rw [sub_self]; positivity)⟩
      exact tight_of _ _ (xe x t - 1) (xe x t) ⟨t - 1, by omega⟩ ⟨t, ht⟩ ⟨by simp; omega, by simp; omega⟩ self
        (by rw [hm1]; omega) xt (by ring) (by linarith) (by push_cast; linarith)

omit hx in
/-- All joints lie over the standard chain. -/
theorem P_range (hm : 0 < m) (t : ℕ) : 1 / 2 ≤ P x N t ∧ P x N t ≤ 2 * (m : ℝ) - 1 / 4 := by
  have hlt := xe_lt (x := x) t hm
  have hlt' := xe_lt (x := x) (t - 1) hm
  have h0 := xe_nonneg (x := x) t
  have h0' := xe_nonneg (x := x) (t - 1)
  by_cases h : xe x (t - 1) = xe x t
  · have := P_stay_bounds hs hN h
    have e1 : (0 : ℝ) ≤ xe x t := by exact_mod_cast h0
    have e2 : (xe x t : ℝ) ≤ m - 1 := by
      have : xe x t ≤ (m : ℤ) - 1 := by omega
      exact_mod_cast this
    constructor <;> linarith [this.1, this.2]
  · simp only [P, h, if_false]
    rw [← Int.cast_min]
    have e1 : (0 : ℤ) ≤ min (xe x (t - 1)) (xe x t) := le_min h0' h0
    have e2 : min (xe x (t - 1)) (xe x t) ≤ (m : ℤ) - 2 := by
      rcases le_total (xe x (t - 1)) (xe x t) with c | c
      · rw [min_eq_left c]; omega
      · rw [min_eq_right c]; omega
    have e1' : (0 : ℝ) ≤ ((min (xe x (t - 1)) (xe x t) : ℤ) : ℝ) := by exact_mod_cast e1
    have e2' : ((min (xe x (t - 1)) (xe x t) : ℤ) : ℝ) ≤ (m : ℝ) - 2 := by exact_mod_cast e2
    constructor <;> linarith

omit hx in
/-- If the pattern starts with two links of value `0`, the first two joints lie in
`[3/2, 7/4]`. -/
theorem P_first (hn : 2 ≤ n) (h0 : (x ⟨0, by omega⟩ : ℕ) = 0) (h1 : (x ⟨1, by omega⟩ : ℕ) = 0) :
    (3 / 2 ≤ P x N 0 ∧ P x N 0 ≤ 7 / 4) ∧ (3 / 2 ≤ P x N 1 ∧ P x N 1 ≤ 7 / 4) := by
  have e0 : xe x 0 = 0 := by rw [xe_of_lt (by omega)]; simp [h0]
  have e1 : xe x 1 = 0 := by rw [xe_of_lt (by omega)]; simp [h1]
  have s0 : xe x (0 - 1) = xe x 0 := rfl
  have s1 : xe x (1 - 1) = xe x 1 := by simp [e0, e1]
  have f0 := fpos_nonneg_of_bottom hs hN e0
  have f1 := fpos_nonneg_of_bottom hs hN e1
  have g0 := fpos_bounds hs (by omega) 0
  have g1 := fpos_bounds hs (by omega) 1
  rw [P_stay s0, P_stay s1, e0, e1]
  push_cast
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [g0.2, g1.2]

omit hx in
/-- If the pattern ends with two links of value `m - 1`, the last two joints lie in
`[2m - 3/4, 2m - 1/2]`. -/
theorem P_last (hm : 0 < m) (hn : 2 ≤ n) (h0 : (x ⟨n - 1, by omega⟩ : ℕ) = m - 1)
    (h1 : (x ⟨n - 2, by omega⟩ : ℕ) = m - 1) :
    (2 * (m : ℝ) - 3 / 4 ≤ P x N (n - 1) ∧ P x N (n - 1) ≤ 2 * (m : ℝ) - 1 / 2) ∧
    (2 * (m : ℝ) - 3 / 4 ≤ P x N n ∧ P x N n ≤ 2 * (m : ℝ) - 1 / 2) := by
  have e0 : xe x (n - 1) = (m : ℤ) - 1 := by
    rw [xe_of_lt (by omega)]; rw [h0]; push_cast [Nat.cast_sub (by omega : 1 ≤ m)]; ring
  have e1 : xe x (n - 2) = (m : ℤ) - 1 := by
    rw [xe_of_lt (by omega)]; rw [h1]; push_cast [Nat.cast_sub (by omega : 1 ≤ m)]; ring
  have en : xe x n = (m : ℤ) - 1 := by rw [xe_eq_of_ge (by omega) (by omega), e0]
  have s0 : xe x (n - 1 - 1) = xe x (n - 1) := by
    rw [show n - 1 - 1 = n - 2 by omega, e0, e1]
  have s1 : xe x (n - 1) = xe x n := by rw [e0, en]
  have f0 := fpos_nonpos_of_top hs hN e0
  have f1 := fpos_nonpos_of_top hs hN en
  have g0 := fpos_bounds hs (by omega) (n - 1)
  have g1 := fpos_bounds hs (by omega) n
  rw [P_stay s0, P_stay (t := n) s1, e0, en]
  push_cast
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [g0.1, g1.1]

end links

end HPC.Plane.Joints
