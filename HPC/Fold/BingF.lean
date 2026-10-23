import HPC.Fold.Minimal

/-!
# Bing's pattern as a function of the index

Batch 82. `bingF d u` is the `u`-th term of `bingPath 0 d` (`0`-indexed), defined by structural
recursion on `d` so that its three pieces can be addressed by index arithmetic:

* `u < z (d-1)`: the pattern `bingF (d-1)` (Bing's `F[1, z(n-1)]`);
* the next `z (d-2) - 1` indices: the reflected pattern `(d-1) - bingF (d-2)` (Bing's `F''`);
* the last `z (d-1) - 1` indices: the shifted pattern `1 + bingF (d-1)` (Bing's `F'''`).

Beyond its length the function is constant, equal to `d`.
-/

namespace HPC.Fold

/-- Bing's pattern `bingPath 0 d` as a function of the index. -/
def bingF : ℕ → ℕ → ℤ
  | 0, _ => 0
  | 1, u => min (u : ℤ) 1
  | 2, u => min (u : ℤ) 2
  | d + 3, u =>
      if u < z (d + 2) then bingF (d + 2) u
      else if u < z (d + 2) + z (d + 1) - 1 then ((d : ℤ) + 2) - bingF (d + 1) (u - (z (d + 2) - 1))
      else 1 + bingF (d + 2) (u - (z (d + 2) + z (d + 1) - 2))

theorem z_succ3 (d : ℕ) : z (d + 3) = 2 * z (d + 2) + z (d + 1) - 2 := rfl

theorem z_two_le (d : ℕ) (hd : 1 ≤ d) : 2 ≤ z d := by
  have := z_ge_of_le hd
  simpa [z] using this

theorem z_three_le (d : ℕ) (hd : 2 ≤ d) : 3 ≤ z d := by
  have := z_ge_of_le hd
  simpa [z] using this

theorem bingF_zero : ∀ d : ℕ, bingF d 0 = 0
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | d + 3 => by
      rw [bingF, if_pos (by have := z_pos (d + 2); omega)]
      exact bingF_zero (d + 2)

/-- From its last index on, the pattern is constant, equal to `d`. -/
theorem bingF_top : ∀ d u : ℕ, z d - 1 ≤ u → bingF d u = d
  | 0, _, _ => rfl
  | 1, u, hu => by
      have : z 1 = 2 := rfl
      simp only [bingF]; push_cast; omega
  | 2, u, hu => by
      have : z 2 = 3 := rfl
      simp only [bingF]; push_cast; omega
  | d + 3, u, hu => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rw [z_succ3] at hu
      rw [bingF, if_neg (by omega), if_neg (by omega),
        bingF_top (d + 2) _ (by omega)]
      push_cast; ring

/-- The three pieces of the pattern, as a case split. -/
theorem bingF_A (d u : ℕ) (hu : u < z (d + 2)) : bingF (d + 3) u = bingF (d + 2) u := by
  rw [bingF, if_pos hu]

theorem bingF_B (d u : ℕ) (hu1 : z (d + 2) - 1 ≤ u) (hu2 : u < z (d + 2) + z (d + 1) - 1) :
    bingF (d + 3) u = ((d : ℤ) + 2) - bingF (d + 1) (u - (z (d + 2) - 1)) := by
  rcases Nat.lt_or_ge u (z (d + 2)) with h | h
  · have hu : u = z (d + 2) - 1 := by omega
    rw [bingF, if_pos h, hu, Nat.sub_self, bingF_zero, bingF_top (d + 2) _ le_rfl]
    push_cast; ring
  · rw [bingF, if_neg (by omega), if_pos hu2]

theorem bingF_C (d u : ℕ) (hu : z (d + 2) + z (d + 1) - 2 ≤ u) :
    bingF (d + 3) u = 1 + bingF (d + 2) (u - (z (d + 2) + z (d + 1) - 2)) := by
  have hB := z_two_le (d + 1) (by omega)
  rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h | h
  · have hu' : u = z (d + 2) + z (d + 1) - 2 := by omega
    have hA := z_pos (d + 2)
    rw [bingF_B d u (by omega) h, bingF_top (d + 1) _ (by omega), hu', Nat.sub_self, bingF_zero]
    push_cast; ring
  · rw [bingF, if_neg (by omega), if_neg (by omega)]

theorem bingF_range : ∀ d u : ℕ, 0 ≤ bingF d u ∧ bingF d u ≤ d
  | 0, _ => by simp [bingF]
  | 1, u => by simp only [bingF]; omega
  | 2, u => by simp only [bingF]; omega
  | d + 3, u => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
      · rw [bingF_A d u h1]; have := bingF_range (d + 2) u; push_cast; omega
      rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) h2]
        have := bingF_range (d + 1) (u - (z (d + 2) - 1)); push_cast at *; omega
      · rw [bingF_C d u (by omega)]
        have := bingF_range (d + 2) (u - (z (d + 2) + z (d + 1) - 2)); push_cast at *; omega

theorem bingF_nonneg (d u : ℕ) : 0 ≤ bingF d u := (bingF_range d u).1
theorem bingF_le (d u : ℕ) : bingF d u ≤ d := (bingF_range d u).2

/-- Consecutive terms differ by at most one. -/
theorem bingF_lip : ∀ d u : ℕ, |bingF d (u + 1) - bingF d u| ≤ 1
  | 0, _ => by simp [bingF]
  | 1, u => by simp only [bingF]; rw [abs_le]; push_cast; omega
  | 2, u => by simp only [bingF]; rw [abs_le]; push_cast; omega
  | d + 3, u => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rcases Nat.lt_or_ge (u + 1) (z (d + 2)) with h1 | h1
      · rw [bingF_A d u (by omega), bingF_A d (u + 1) h1]; exact bingF_lip (d + 2) u
      rcases Nat.lt_or_ge (u + 1) (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) (by omega), bingF_B d (u + 1) (by omega) h2]
        have := bingF_lip (d + 1) (u - (z (d + 2) - 1))
        rw [show u + 1 - (z (d + 2) - 1) = u - (z (d + 2) - 1) + 1 by omega]
        rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
      · rw [bingF_C d u (by omega), bingF_C d (u + 1) (by omega)]
        have := bingF_lip (d + 2) (u - (z (d + 2) + z (d + 1) - 2))
        rw [show u + 1 - (z (d + 2) + z (d + 1) - 2) = u - (z (d + 2) + z (d + 1) - 2) + 1 by
          omega]
        rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]

theorem bingF_one (d : ℕ) (hd : 1 ≤ d) : bingF d 1 = 1 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d, hd with
    | 1, _ => rfl
    | 2, _ => rfl
    | d + 3, _ =>
        rw [bingF_A d 1 (by have := z_three_le (d + 2) (by omega); omega)]
        exact ih (d + 2) (by omega) (by omega)

theorem bingF_two (d : ℕ) (hd : 2 ≤ d) : bingF d 2 = 2 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d, hd with
    | 2, _ => rfl
    | d + 3, _ =>
        rw [bingF_A d 2 (by have := z_three_le (d + 2) (by omega); omega)]
        exact ih (d + 2) (by omega) (by omega)

/-- Level `0` is taken only at the first index. -/
theorem bingF_eq_zero : ∀ d u : ℕ, u < z d → bingF d u = 0 → u = 0
  | 0, u, hu, _ => by have : z 0 = 1 := rfl; omega
  | 1, u, _, h => by simp only [bingF] at h; omega
  | 2, u, _, h => by simp only [bingF] at h; omega
  | d + 3, u, hu, h => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
      · rw [bingF_A d u h1] at h; exact bingF_eq_zero (d + 2) u h1 h
      rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) h2] at h
        have := bingF_le (d + 1) (u - (z (d + 2) - 1)); push_cast at *; omega
      · rw [bingF_C d u (by omega)] at h
        have := bingF_nonneg (d + 2) (u - (z (d + 2) + z (d + 1) - 2)); omega

/-- The top level `d` is taken only from the last index on. -/
theorem bingF_eq_top : ∀ d u : ℕ, bingF d u = d → z d - 1 ≤ u
  | 0, u, _ => by have : z 0 = 1 := rfl; omega
  | 1, u, h => by have : z 1 = 2 := rfl; simp only [bingF] at h; omega
  | 2, u, h => by have : z 2 = 3 := rfl; simp only [bingF] at h; omega
  | d + 3, u, h => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rw [z_succ3]
      rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
      · rw [bingF_A d u h1] at h; have := bingF_le (d + 2) u; push_cast at *; omega
      rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) h2] at h
        have := bingF_nonneg (d + 1) (u - (z (d + 2) - 1)); push_cast at *; omega
      · rw [bingF_C d u (by omega)] at h
        have := bingF_eq_top (d + 2) (u - (z (d + 2) + z (d + 1) - 2)) (by push_cast at *; omega)
        omega

/-- The pattern read backwards is the pattern reflected. -/
theorem bingF_rev : ∀ d u : ℕ, u < z d → bingF d (z d - 1 - u) = d - bingF d u
  | 0, u, _ => by simp [bingF]
  | 1, u, hu => by have : z 1 = 2 := rfl; simp only [bingF]; push_cast; omega
  | 2, u, hu => by have : z 2 = 3 := rfl; simp only [bingF]; push_cast; omega
  | d + 3, u, hu => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      have hz := z_succ3 d
      rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
      · -- `u` in the first piece, its mirror in the last
        rw [bingF_A d u h1, bingF_C d _ (by omega),
          show z (d + 3) - 1 - u - (z (d + 2) + z (d + 1) - 2) = z (d + 2) - 1 - u by omega,
          bingF_rev (d + 2) u h1]
        push_cast; ring
      rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) h2, bingF_B d _ (by omega) (by omega),
          show z (d + 3) - 1 - u - (z (d + 2) - 1) = z (d + 1) - 1 - (u - (z (d + 2) - 1)) by
            omega,
          bingF_rev (d + 1) _ (by omega)]
        push_cast; ring
      · have hu' : z (d + 3) - 1 - u < z (d + 2) := by omega
        rw [bingF_C d u (by omega), bingF_A d _ hu']
        have := bingF_rev (d + 2) (u - (z (d + 2) + z (d + 1) - 2)) (by omega)
        rw [show z (d + 2) - 1 - (u - (z (d + 2) + z (d + 1) - 2)) = z (d + 3) - 1 - u by
          omega] at this
        rw [this]; push_cast; ring

end HPC.Fold

namespace HPC.Fold

/-- The value predicted for `bingPath a b` at index `u`. -/
def bingVal (a b : ℤ) (u : ℕ) : ℤ :=
  if a ≤ b then a + bingF (b - a).natAbs u else a - bingF (b - a).natAbs u

theorem bingF_small (d u : ℕ) (hd : d ≤ 2) (hu : u ≤ d) : bingF d u = u := by
  interval_cases d <;> simp only [bingF] <;> omega

theorem flatMap_natCast (l : List ℕ) :
    List.flatMap (fun a : ℕ => [(a : ℤ)]) l = l.map (fun a : ℕ => (a : ℤ)) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem bingPath_getElem_aux : ∀ (N : ℕ) (a b : ℤ), (b - a).natAbs ≤ N →
    ∀ (u : ℕ) (hu : u < (bingPath a b).length), (bingPath a b)[u] = bingVal a b u
  | 0, a, b, hN, u, hu => by
      have hab : b = a := by omega
      subst hab
      have hl := bingPath_length b b
      simp at hl
      simp only [bingPath_base (show |b - b| ≤ 2 by simp), bingRun, le_refl, if_true, bingVal,
        sub_self, List.getElem_map]
      simp [bingF]
  | N + 1, a, b, hN, u, hu => by
      have hlen := bingPath_length a b
      rw [toNat_abs] at hlen
      by_cases hs : |b - a| ≤ 2
      · have hs' := (abs_le_two_iff _).1 hs
        rw [hlen] at hu
        simp only [bingPath_base hs]
        unfold bingRun bingVal
        have hz : z (b - a).natAbs = (b - a).natAbs + 1 := by
          rcases (show (b - a).natAbs = 0 ∨ (b - a).natAbs = 1 ∨ (b - a).natAbs = 2 by omega)
            with h | h | h <;> rw [h] <;> rfl
        split_ifs with hab
        · rw [bingF_small _ u hs' (by omega)]; simp [flatMap_natCast]
        · rw [bingF_small _ u hs' (by omega)]; simp [flatMap_natCast]
      · have hd : ¬ (b - a).natAbs ≤ 2 := fun h => hs ((abs_le_two_iff _).2 h)
        obtain ⟨d, hd'⟩ : ∃ d, (b - a).natAbs = d + 3 := ⟨(b - a).natAbs - 3, by omega⟩
        have hA3 := z_three_le (d + 2) (by omega)
        have hB2 := z_two_le (d + 1) (by omega)
        have hz := z_succ3 d
        by_cases hab : a < b
        · have e1 : ∀ v (hv : v < (bingPath a (b - 1)).length),
              (bingPath a (b - 1))[v] = a + bingF (d + 2) v := fun v hv => by
            rw [bingPath_getElem_aux N a (b - 1) (by omega) v hv, bingVal, if_pos (by omega),
              show (b - 1 - a).natAbs = d + 2 by omega]
          have e2 : ∀ v (hv : v < (bingPath (b - 1) (a + 1)).length),
              (bingPath (b - 1) (a + 1))[v] = (b - 1) - bingF (d + 1) v := fun v hv => by
            rw [bingPath_getElem_aux N (b - 1) (a + 1) (by omega) v hv, bingVal,
              if_neg (by omega), show (a + 1 - (b - 1)).natAbs = d + 1 by omega]
          have e3 : ∀ v (hv : v < (bingPath (a + 1) b).length),
              (bingPath (a + 1) b)[v] = (a + 1) + bingF (d + 2) v := fun v hv => by
            rw [bingPath_getElem_aux N (a + 1) b (by omega) v hv, bingVal, if_pos (by omega),
              show (b - (a + 1)).natAbs = d + 2 by omega]
          have l1 := bingPath_length a (b - 1)
          have l2 := bingPath_length (b - 1) (a + 1)
          have l3 := bingPath_length (a + 1) b
          rw [toNat_abs, show (b - 1 - a).natAbs = d + 2 by omega] at l1
          rw [toNat_abs, show (a + 1 - (b - 1)).natAbs = d + 1 by omega] at l2
          rw [toNat_abs, show (b - (a + 1)).natAbs = d + 2 by omega] at l3
          simp only [bingPath_up hs hab]
          rw [bingVal, if_pos (by omega), hd']
          rw [bingPath_up hs hab] at hu
          simp only [List.length_append, List.length_tail] at hu
          rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
          · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega),
              e1, bingF_A d u h1]
          rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
          · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega),
              List.getElem_tail, e2, bingF_B d u (by omega) h2]
            simp only [l1]
            rw [show u - z (d + 2) + 1 = u - (z (d + 2) - 1) by omega]
            omega
          · rw [List.getElem_append_right (by simp; omega), List.getElem_tail, e3,
              bingF_C d u (by omega)]
            simp only [List.length_append, List.length_tail, l1, l2]
            rw [show u - (z (d + 2) + (z (d + 1) - 1)) + 1 = u - (z (d + 2) + z (d + 1) - 2) by
              omega]
            ring
        · have e1 : ∀ v (hv : v < (bingPath a (b + 1)).length),
              (bingPath a (b + 1))[v] = a - bingF (d + 2) v := fun v hv => by
            rw [bingPath_getElem_aux N a (b + 1) (by omega) v hv, bingVal, if_neg (by omega),
              show (b + 1 - a).natAbs = d + 2 by omega]
          have e2 : ∀ v (hv : v < (bingPath (b + 1) (a - 1)).length),
              (bingPath (b + 1) (a - 1))[v] = (b + 1) + bingF (d + 1) v := fun v hv => by
            rw [bingPath_getElem_aux N (b + 1) (a - 1) (by omega) v hv, bingVal,
              if_pos (by omega), show (a - 1 - (b + 1)).natAbs = d + 1 by omega]
          have e3 : ∀ v (hv : v < (bingPath (a - 1) b).length),
              (bingPath (a - 1) b)[v] = (a - 1) - bingF (d + 2) v := fun v hv => by
            rw [bingPath_getElem_aux N (a - 1) b (by omega) v hv, bingVal, if_neg (by omega),
              show (b - (a - 1)).natAbs = d + 2 by omega]
          have l1 := bingPath_length a (b + 1)
          have l2 := bingPath_length (b + 1) (a - 1)
          have l3 := bingPath_length (a - 1) b
          rw [toNat_abs, show (b + 1 - a).natAbs = d + 2 by omega] at l1
          rw [toNat_abs, show (a - 1 - (b + 1)).natAbs = d + 1 by omega] at l2
          rw [toNat_abs, show (b - (a - 1)).natAbs = d + 2 by omega] at l3
          simp only [bingPath_down hs hab]
          rw [bingVal, if_neg (by omega), hd']
          rw [bingPath_down hs hab] at hu
          simp only [List.length_append, List.length_tail] at hu
          rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
          · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega),
              e1, bingF_A d u h1]
          rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
          · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega),
              List.getElem_tail, e2, bingF_B d u (by omega) h2]
            simp only [l1]
            rw [show u - z (d + 2) + 1 = u - (z (d + 2) - 1) by omega]
            omega
          · rw [List.getElem_append_right (by simp; omega), List.getElem_tail, e3,
              bingF_C d u (by omega)]
            simp only [List.length_append, List.length_tail, l1, l2]
            rw [show u - (z (d + 2) + (z (d + 1) - 1)) + 1 = u - (z (d + 2) + z (d + 1) - 2) by
              omega]
            ring

/-- `bingF d` is `bingPath 0 d` read by index. -/
theorem bingPath_zero_getElem (d : ℕ) (u : ℕ) (hu : u < (bingPath 0 (d : ℤ)).length) :
    (bingPath 0 (d : ℤ))[u] = bingF d u := by
  rw [bingPath_getElem_aux d 0 d (by omega) u hu, bingVal, if_pos (by omega)]
  simp

end HPC.Fold
