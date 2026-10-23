import HPC.Fold.Leaf

/-!
# Bing 1948 Theorem 3 at span seven

Batch 37 settled span six by a method this file carries further. Its two halves are separated
again, and both are generalised.

* **The crooked half, at arbitrary levels.** `LowAt f tl th` and `HighAt f tl th` are the
  span-six conditions with the two extreme levels replaced by two free parameters: `LowAt` says
  that before the arm ever falls to `tl` it has reached `th`, or has been at `tl + 1` and after
  that at `th - 2`; `HighAt` says that before the arm ever rises to `th` it has been at `tl + 1`.
  `dichotomy_at`: for **every** pair of levels with `tl + 3 ≤ th`, at every basepoint of every
  faithful crooked sequence, either both arms are `LowAt tl th` or both arms are `HighAt tl th`.
  This is `span6_dichotomy` with the levels freed, and it is what lets a single crookedness clause
  be applied at several level pairs at one basepoint.

* **The folding half, at arbitrary basepoints, with a greedy assignment.** `bumpWalk p H` is the
  one-bump walk from `p - 1` up to `H - 1` and down to `L + 1`. The ascending assignment is no
  longer the capped phase count of batch 37 but the *greedy* one: `ascVal` is the largest legal
  time, which has the closed form `min A (min j (runMin f j + j - p + 2))`, where `runMin f j` is
  the running minimum of `f k - k`. `foldsOnto_bumpWalk_of_switch` then needs only this:

  > before the arm first falls to `p - 3` there is a time `s ≥ H - p` at which it stands at
  > `H - 2`.

  No crookedness is used, so the reflected form is free. The greedy assignment subsumes batch
  37's capped phase count: at span six the condition `LowLate` implies this one.

* **What follows.** `s3_of_lowAt` and `s3_of_highAt`: at *any* span, if both arms are
  `LowAt (ρ i - 3) H`, or both are `HighAt L (ρ i + 3)`, the basepoint is served. With the
  dichotomy, `s3_of_not_highAt` and `s3_of_not_lowAt`: **the only basepoints not settled are
  those at which both arms are `HighAt (ρ i - 3) H` and both arms are `LowAt L (ρ i + 3)`.**
  At span seven this is the one remaining case, and it is settled here.

* **The leaf case.** For an arm of span seven the remaining basepoints sit at height `L + 3` or
  `L + 4`. Each is served by one explicit thirteen-time walk, `walk7` and its reflection
  `walk7'`, and the folds onto them, `foldsOnto_walk7_of_leaf` and `foldsOnto_walk7'_of_leaf`,
  are proved in `HPC/Fold/Leaf.lean` by a greedy time assignment carrying an explicit inductive
  invariant. The `L + 3` leaf needs one isolated crookedness clause, packaged as `Zig`; the
  `L + 4` leaf needs none.

Both commissioned statements, `s3_span_seven` and `theorem3_span_seven`, are proved at the end
of the file; no `sorry` remains.
-/

namespace HPC.Fold

open Classical

/-! ## The conditions, at arbitrary levels (`LowAt`, `HighAt`: see `HPC/Fold/Leaf.lean`) -/

/-- No arm can fail both conditions: the two witnesses would be in the wrong order. -/
theorem not_lowAt_highAt {m : ℕ} (f : Fin m → ℤ) (tl th : ℤ) (hlt : tl < th)
    (h1 : ¬ LowAt f tl th) (h2 : ¬ HighAt f tl th) : False := by
  rw [LowAt] at h1
  rw [HighAt] at h2
  push_neg at h1 h2
  obtain ⟨a, ha, hna, -⟩ := h1
  obtain ⟨b, hb, hnb⟩ := h2
  rcases lt_trichotomy b.val a.val with hlt' | heq | hgt
  · have := hna b hlt'
    omega
  · rw [show b = a from Fin.ext heq] at hb
    omega
  · have := hnb a hgt
    omega

/-- **The crooked half.** One application of the crookedness clause to a `th`-time before the
basepoint and a `tl`-time after it. -/
theorem lowAt_armG_of_not_highAt_armT {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (tl th : ℤ) (hLH : tl + 3 ≤ th)
    (h1 : ¬ LowAt (armG ρ i) tl th) (h2 : ¬ HighAt (armT ρ i) tl th) : False := by
  rw [LowAt] at h1
  rw [HighAt] at h2
  push_neg at h1 h2
  obtain ⟨dG, hdG, -, hG2⟩ := h1
  obtain ⟨dT, hdT, hT1⟩ := h2
  have hi := i.isLt
  have hdGlt := dG.isLt
  have hdTlt := dT.isLt
  have ha : ρ ⟨i.val + dG.val, by omega⟩ ≤ tl := hdG
  have hb : th ≤ ρ ⟨i.val - dT.val, by omega⟩ := hdT
  have hba : (⟨i.val - dT.val, by omega⟩ : Fin n) < ⟨i.val + dG.val, by omega⟩ := by
    rw [Fin.lt_def]
    show i.val - dT.val < i.val + dG.val
    rcases Nat.eq_zero_or_pos dT.val with h | h
    · rcases Nat.eq_zero_or_pos dG.val with h' | h'
      · exfalso
        rw [show (⟨i.val - dT.val, by omega⟩ : Fin n) = ⟨i.val + dG.val, by omega⟩ from
          Fin.ext (by show i.val - dT.val = i.val + dG.val; omega)] at hb
        omega
      · omega
    · omega
  set hlev : ℤ := ρ ⟨i.val - dT.val, by omega⟩ with hhlev
  set klev : ℤ := ρ ⟨i.val + dG.val, by omega⟩ with hklev
  obtain ⟨r, r', hbr, hrr', hr'a, -, hcase⟩ :=
    hcr.crooked ⟨i.val - dT.val, by omega⟩ ⟨i.val + dG.val, by omega⟩ hba hlev klev
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
  · -- the low witness is in the backward arm, before its `th`-time
    have he : armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    have := hT1 ⟨i.val - r.val, by omega⟩ (by show i.val - r.val < dT.val; omega)
    omega
  · -- both witnesses are in the forward arm, before its `tl`-time
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

/-- The mirror of `lowAt_armG_of_not_highAt_armT`. -/
theorem lowAt_armT_of_not_highAt_armG {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (tl th : ℤ) (hLH : tl + 3 ≤ th)
    (h1 : ¬ LowAt (armT ρ i) tl th) (h2 : ¬ HighAt (armG ρ i) tl th) : False := by
  rw [LowAt] at h1
  rw [HighAt] at h2
  push_neg at h1 h2
  obtain ⟨dT, hdT, -, hT2⟩ := h1
  obtain ⟨dG, hdG, hG1⟩ := h2
  have hi := i.isLt
  have hdGlt := dG.isLt
  have hdTlt := dT.isLt
  have ha : ρ ⟨i.val - dT.val, by omega⟩ ≤ tl := hdT
  have hb : th ≤ ρ ⟨i.val + dG.val, by omega⟩ := hdG
  have hab : (⟨i.val - dT.val, by omega⟩ : Fin n) < ⟨i.val + dG.val, by omega⟩ := by
    rw [Fin.lt_def]
    show i.val - dT.val < i.val + dG.val
    rcases Nat.eq_zero_or_pos dT.val with h | h
    · rcases Nat.eq_zero_or_pos dG.val with h' | h'
      · exfalso
        rw [show (⟨i.val - dT.val, by omega⟩ : Fin n) = ⟨i.val + dG.val, by omega⟩ from
          Fin.ext (by show i.val - dT.val = i.val + dG.val; omega)] at ha
        omega
      · omega
    · omega
  set hlev : ℤ := ρ ⟨i.val - dT.val, by omega⟩ with hhlev
  set klev : ℤ := ρ ⟨i.val + dG.val, by omega⟩ with hklev
  obtain ⟨r, r', har, hrr', hr'b, hcase, -⟩ :=
    hcr.crooked ⟨i.val - dT.val, by omega⟩ ⟨i.val + dG.val, by omega⟩ hab hlev klev
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
  · -- both witnesses are in the backward arm, before its `tl`-time
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
  · -- the low witness is in the forward arm, before its `th`-time
    have he : armG ρ i ⟨r'.val - i.val, by omega⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    have := hG1 ⟨r'.val - i.val, by omega⟩ (by show r'.val - i.val < dG.val; omega)
    omega

/-- **The dichotomy, at arbitrary levels.** At every basepoint of every faithful crooked
sequence, and for every pair of levels three apart, either both arms are `LowAt` or both arms are
`HighAt`. `span6_dichotomy` is the case `tl = L`, `th = H`. -/
theorem dichotomy_at {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) (tl th : ℤ)
    (hLH : tl + 3 ≤ th) :
    (LowAt (armG ρ i) tl th ∧ LowAt (armT ρ i) tl th) ∨
      (HighAt (armG ρ i) tl th ∧ HighAt (armT ρ i) tl th) := by
  by_cases hG : LowAt (armG ρ i) tl th
  · by_cases hT : LowAt (armT ρ i) tl th
    · exact Or.inl ⟨hG, hT⟩
    · refine Or.inr ⟨?_, ?_⟩
      · by_contra hc
        exact lowAt_armT_of_not_highAt_armG hcr i tl th hLH hT hc
      · by_contra hc
        exact not_lowAt_highAt (armT ρ i) tl th (by omega) hT hc
  · refine Or.inr ⟨?_, ?_⟩
    · by_contra hc
      exact not_lowAt_highAt (armG ρ i) tl th (by omega) hG hc
    · by_contra hc
      exact lowAt_armG_of_not_highAt_armT hcr i tl th hLH hG hc


/-! ## The running minimum and the greedy ascending assignment -/

/-- The running minimum of `f k - k` over the times up to `j`. -/
noncomputable def runMin {m : ℕ} (f : Fin m → ℤ) (j : Fin m) : ℤ :=
  Finset.inf' (Finset.univ.filter fun k : Fin m => k.val ≤ j.val)
    ⟨j, by simp⟩ fun k => f k - (k.val : ℤ)

theorem runMin_le {m : ℕ} (f : Fin m → ℤ) (j k : Fin m) (h : k.val ≤ j.val) :
    runMin f j ≤ f k - (k.val : ℤ) := by
  refine Finset.inf'_le (fun k : Fin m => f k - (k.val : ℤ)) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

theorem le_runMin {m : ℕ} (f : Fin m → ℤ) (j : Fin m) (c : ℤ)
    (h : ∀ k : Fin m, k.val ≤ j.val → c ≤ f k - (k.val : ℤ)) : c ≤ runMin f j :=
  Finset.le_inf' _ _ (by intro k hk; exact h k (by simpa using hk))

theorem runMin_mono {m : ℕ} (f : Fin m → ℤ) (j j' : Fin m) (h : j.val ≤ j'.val) :
    runMin f j' ≤ runMin f j :=
  le_runMin f j _ fun k hk => runMin_le f j' k (by omega)

/-- One step of the running minimum. -/
theorem runMin_step {m : ℕ} (f : Fin m → ℤ) (j j' : Fin m) (h : j'.val = j.val + 1) :
    min (runMin f j) (f j' - (j'.val : ℤ)) ≤ runMin f j' := by
  refine le_runMin f j' _ fun k hk => ?_
  rcases Nat.lt_or_ge k.val j'.val with hc | hc
  · exact le_trans (min_le_left _ _) (runMin_le f j k (by omega))
  · rw [show k = j' from Fin.ext (by omega)]
    exact min_le_right _ _

/-- The running minimum of a 1-Lipschitz sequence is at least `f j - j`. -/
theorem le_runMin_of_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (j : Fin m) :
    f j - (j.val : ℤ) ≤ runMin f j := by
  refine le_runMin f j _ fun k hk => ?_
  have := abs_sub_le_of_isLip hf (j.val - k.val) k j (by omega)
  rw [abs_le] at this
  have : f j - f k ≤ ((j.val - k.val : ℕ) : ℤ) := this.2
  have hc : ((j.val - k.val : ℕ) : ℤ) = (j.val : ℤ) - (k.val : ℤ) := by
    push_cast [Nat.cast_sub hk]; ring
  omega

/-! ## The one-bump walk and the two assignments -/

/-- The one-bump walk based at `p - 1`: up to the peak `H - 1`, then down to `L + 1`. -/
def bumpWalk (p H : ℤ) (u : ℕ) : ℤ := if (u : ℤ) ≤ H - p then p - 1 + (u : ℤ) else 2 * H - p - 1 - u

/-- The number of times of `bumpWalk`. -/
def bumpWalkLen (p L H : ℤ) : ℕ := (2 * H - p - L - 1).toNat

theorem bumpWalk_up (p H : ℤ) (u : ℕ) (h : (u : ℤ) ≤ H - p) : bumpWalk p H u = p - 1 + (u : ℤ) :=
  if_pos h

theorem bumpWalk_down (p H : ℤ) (u : ℕ) (h : ¬ (u : ℤ) ≤ H - p) :
    bumpWalk p H u = 2 * H - p - 1 - u := if_neg h

/-- The greedy ascending assignment: the largest legal time on the ascending leg. -/
noncomputable def ascVal {m : ℕ} (f : Fin m → ℤ) (p H : ℤ) (j : Fin m) : ℤ :=
  min (H - p) (min (j.val : ℤ) (runMin f j + (j.val : ℤ) - p + 2))

/-- The descending assignment. -/
def descVal {m : ℕ} (f : Fin m → ℤ) (p H : ℤ) (j : Fin m) : ℤ := (H - p) + max (H - 2 - f j) 0

theorem ascVal_le {m : ℕ} (f : Fin m → ℤ) (p H : ℤ) (j : Fin m) : ascVal f p H j ≤ H - p :=
  min_le_left _ _

theorem ascVal_nonneg {m : ℕ} (f : Fin m → ℤ) (p H : ℤ) (j : Fin m) (hpH : p + 2 ≤ H)
    (hlow : ∀ k : Fin m, k.val ≤ j.val → p - 2 ≤ f k) : 0 ≤ ascVal f p H j := by
  have h1 : p - 2 - (j.val : ℤ) ≤ runMin f j :=
    le_runMin f j _ fun k hk => by
      have := hlow k hk
      have : (k.val : ℤ) ≤ (j.val : ℤ) := by exact_mod_cast hk
      omega
  have h2 : (0 : ℤ) ≤ (j.val : ℤ) := Int.natCast_nonneg _
  simp only [ascVal, le_min_iff]
  omega

/-- The greedy assignment lands in its window. -/
theorem ascVal_window {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (hm : 0 < m) (p H : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (j : Fin m) (hj : f j ≤ H) :
    f j - p ≤ ascVal f p H j ∧ ascVal f p H j ≤ f j - p + 2 := by
  constructor
  · have h1 : f j - p ≤ H - p := by omega
    have h2 : f j - p ≤ (j.val : ℤ) := by
      have := abs_sub_le_of_isLip hf j.val ⟨0, hm⟩ j (by simp)
      rw [abs_le] at this
      have := this.2
      omega
    have h3 : f j - p ≤ runMin f j + (j.val : ℤ) - p + 2 := by
      have := le_runMin_of_isLip hf j
      omega
    simp only [ascVal, le_min_iff]
    exact ⟨h1, h2, h3⟩
  · have := runMin_le f j j (le_refl _)
    calc ascVal f p H j ≤ runMin f j + (j.val : ℤ) - p + 2 :=
          le_trans (min_le_right _ _) (min_le_right _ _)
      _ ≤ f j - p + 2 := by omega

theorem ascVal_lip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (p H : ℤ) (j j' : Fin m)
    (hjj' : j'.val = j.val + 1) : |ascVal f p H j' - ascVal f p H j| ≤ 1 := by
  have hstep := hf j j' hjj'
  rw [abs_le] at hstep
  have hmono := runMin_mono f j j' (by omega)
  have hst := runMin_step f j j' hjj'
  have hle := runMin_le f j j (le_refl _)
  have hcast : (j'.val : ℤ) = (j.val : ℤ) + 1 := by rw [hjj']; push_cast; ring
  rw [abs_le]
  simp only [ascVal, min_le_iff] at *
  omega

theorem descVal_bounds {m : ℕ} (f : Fin m → ℤ) (p L H : ℤ) (j : Fin m) (hL : L ≤ f j)
    (hLH : L + 2 ≤ H) :
    H - p ≤ descVal f p H j ∧ descVal f p H j ≤ 2 * H - p - L - 2 := by
  simp only [descVal]
  omega

theorem descVal_window {m : ℕ} (f : Fin m → ℤ) (p L H : ℤ) (j : Fin m) (hL : L ≤ f j)
    (hH : f j ≤ H) (hpH : p + 2 ≤ H) (hLp : L + 2 ≤ p) :
    |f j - bumpWalk p H (descVal f p H j).toNat| ≤ 1 := by
  obtain ⟨hb1, hb2⟩ := descVal_bounds f p L H j hL (by omega)
  have hcast : ((descVal f p H j).toNat : ℤ) = descVal f p H j := Int.toNat_of_nonneg (by omega)
  by_cases hc : ((descVal f p H j).toNat : ℤ) ≤ H - p
  · rw [bumpWalk_up p H _ hc, hcast, abs_le]
    simp only [descVal] at *
    omega
  · rw [bumpWalk_down p H _ hc, hcast, abs_le]
    simp only [descVal] at *
    omega

theorem descVal_lip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (p H : ℤ) (j j' : Fin m)
    (hjj' : j'.val = j.val + 1) : |descVal f p H j' - descVal f p H j| ≤ 1 := by
  have h1 := hf j j' hjj'
  rw [abs_le] at h1 ⊢
  simp only [descVal]
  omega

/-! ## The folding half -/

/-- **The folding half, with no crookedness.** A 1-Lipschitz arm in `[L, H]` based at an interior
level `p` folds onto `bumpWalk p H` as soon as it satisfies the *switch condition*: before the arm
ever falls to `p - 3` there is a time `s ≥ H - p` at which it stands at `H - 2` or above. -/
theorem foldsOnto_bumpWalk_of_switch {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (p L H : ℤ) (h0 : f ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hp1 : L + 2 ≤ p) (hp2 : p + 2 ≤ H)
    (hsw : ∀ d : Fin m, f d ≤ p - 3 →
      ∃ s : Fin m, s.val < d.val ∧ H - p ≤ (s.val : ℤ) ∧ H - 2 ≤ f s) :
    FoldsOnto f (bumpWalkLen p L H) (bumpWalk p H) := by
  classical
  -- the switch time
  have key : ∃ s : ℕ, 1 ≤ s ∧ (∀ j : Fin m, j.val < s → p - 2 ≤ f j) ∧
      (∀ j j0 : Fin m, j.val = s → j0.val + 1 = s →
        H - 2 ≤ f j ∧ H - p - 1 ≤ ascVal f p H j0) := by
    by_cases hex : ∃ d : Fin m, f d ≤ p - 3
    · obtain ⟨a, ha, hamin⟩ := exists_least_index (fun d => f d ≤ p - 3) hex
      have hbefore : ∀ j : Fin m, j.val < a.val → p - 2 ≤ f j := by
        intro j hj
        have := hamin j hj
        omega
      obtain ⟨s, hsa, hsA, hsf⟩ := hsw a ha
      refine ⟨s.val, ?_, fun j hj => hbefore j (by omega), ?_⟩
      · have : (2 : ℤ) ≤ (s.val : ℤ) := le_trans (by omega) hsA
        omega
      · intro j j0 hjs hj0s
        have hjs' : j = s := Fin.ext hjs
        subst hjs'
        refine ⟨hsf, ?_⟩
        have hstep := hf j0 j (by omega)
        rw [abs_le] at hstep
        have hrm : f j0 - (j0.val : ℤ) ≤ runMin f j0 := le_runMin_of_isLip hf j0
        have hcast : (j.val : ℤ) = (j0.val : ℤ) + 1 := by
          have : j.val = j0.val + 1 := by omega
          rw [this]; push_cast; ring
        simp only [ascVal, le_min_iff]
        refine ⟨by omega, by omega, by omega⟩
    · push_neg at hex
      refine ⟨m, by omega, fun j _ => by have := hex j; omega, ?_⟩
      intro j _ hjs _
      exact absurd j.isLt (by omega)
  obtain ⟨s, hs1, hs2, hs3⟩ := key
  refine ⟨fun j => if j.val < s then (ascVal f p H j).toNat else (descVal f p H j).toNat,
    ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · -- inside the walk
    intro j
    by_cases hc : j.val < s
    · rw [if_pos hc]
      have h1 := ascVal_nonneg f p H j hp2 (fun k hk => hs2 k (by omega))
      have h2 := ascVal_le f p H j
      simp only [bumpWalkLen]
      omega
    · rw [if_neg hc]
      obtain ⟨h1, h2⟩ := descVal_bounds f p L H j (hL j) (by omega)
      simp only [bumpWalkLen]
      omega
  · -- 1-Lipschitz
    intro j j' hjj'
    by_cases hc : j.val < s <;> by_cases hc' : j'.val < s
    · rw [if_pos hc, if_pos hc']
      have h1 := ascVal_lip hf p H j j' hjj'
      have h2 := ascVal_nonneg f p H j hp2 (fun k hk => hs2 k (by omega))
      have h3 := ascVal_nonneg f p H j' hp2 (fun k hk => hs2 k (by omega))
      rw [abs_le] at h1 ⊢
      omega
    · -- the junction
      rw [if_pos hc, if_neg hc']
      obtain ⟨hfj', haj⟩ := hs3 j' j (by omega) (by omega)
      have hb : descVal f p H j' = H - p := by simp only [descVal]; omega
      have h2 := ascVal_le f p H j
      have h3 := ascVal_nonneg f p H j hp2 (fun k hk => hs2 k (by omega))
      rw [hb, abs_le]
      omega
    · exact absurd hjj' (by omega)
    · rw [if_neg hc, if_neg hc']
      have h1 := descVal_lip hf p H j j' hjj'
      obtain ⟨h2, h3⟩ := descVal_bounds f p L H j (hL j) (by omega)
      obtain ⟨h4, h5⟩ := descVal_bounds f p L H j' (hL j') (by omega)
      rw [abs_le] at h1 ⊢
      omega
  · -- the basepoint is at time zero
    intro j hj
    have hz : ascVal f p H j = 0 := by
      have hj0 : j = (⟨0, hm⟩ : Fin m) := Fin.ext hj
      subst hj0
      have hrm := runMin_le f ⟨0, hm⟩ ⟨0, hm⟩ (le_refl _)
      have := ascVal_nonneg f p H ⟨0, hm⟩ hp2 (fun k hk => by
        have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (by omega)
        subst this; omega)
      simp only [ascVal, le_min_iff] at *
      omega
    rw [if_pos (by omega), hz]
    rfl
  · -- every level inside its window
    intro j
    by_cases hc : j.val < s
    · rw [if_pos hc]
      have hw := ascVal_window hf hm p H h0 j (hH j)
      have hnn := ascVal_nonneg f p H j hp2 (fun k hk => hs2 k (by omega))
      have hle := ascVal_le f p H j
      have hcast : ((ascVal f p H j).toNat : ℤ) = ascVal f p H j := Int.toNat_of_nonneg hnn
      have hup : ((ascVal f p H j).toNat : ℤ) ≤ H - p := by omega
      rw [bumpWalk_up p H _ hup, hcast, abs_le]
      omega
    · rw [if_neg hc]
      exact descVal_window f p L H j (hL j) (hH j) hp2 hp1

/-- The reflection of the one-bump walk: down from `p + 1` to `L + 1`, then up to `H - 1`. -/
def bumpWalk' (p L H : ℤ) (u : ℕ) : ℤ := L + H - bumpWalk (L + H - p) H u

/-- **The reflected folding half.** The mirror of `foldsOnto_bumpWalk_of_switch`: no crookedness
hypothesis lies beneath it, so reflecting the arm is legitimate. -/
theorem foldsOnto_bumpWalk'_of_switch {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (p L H : ℤ) (h0 : f ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hp1 : L + 2 ≤ p) (hp2 : p + 2 ≤ H)
    (hsw : ∀ d : Fin m, p + 3 ≤ f d →
      ∃ s : Fin m, s.val < d.val ∧ p - L ≤ (s.val : ℤ) ∧ f s ≤ L + 2) :
    FoldsOnto f (bumpWalkLen (L + H - p) L H) (bumpWalk' p L H) := by
  set g : Fin m → ℤ := fun j => L + H - f j with hg
  have hglip : IsLip g := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [hg]
    rw [abs_le] at this ⊢
    omega
  have hg0 : g ⟨0, hm⟩ = L + H - p := by simp only [hg, h0]
  have hgL : ∀ j, L ≤ g j := fun j => by have := hH j; simp only [hg]; omega
  have hgH : ∀ j, g j ≤ H := fun j => by have := hL j; simp only [hg]; omega
  have hgsw : ∀ d : Fin m, g d ≤ (L + H - p) - 3 →
      ∃ s : Fin m, s.val < d.val ∧ H - (L + H - p) ≤ (s.val : ℤ) ∧ H - 2 ≤ g s := by
    intro d hd
    have hfd : p + 3 ≤ f d := by simp only [hg] at hd; omega
    obtain ⟨s, hs1, hs2, hs3⟩ := hsw d hfd
    exact ⟨s, hs1, by omega, by simp only [hg]; omega⟩
  obtain ⟨β, h1, h2, h3, h4⟩ :=
    foldsOnto_bumpWalk_of_switch hm g hglip (L + H - p) L H hg0 hgL hgH (by omega) (by omega) hgsw
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [hg] at this
  simp only [bumpWalk']
  rw [abs_le] at this ⊢
  omega

/-! ## From the conditions to the switch -/

/-- **`LowAt` supplies the switch.** At an interior basepoint, with the low level within one of
`p - 3` and the high level at the top of the band, `LowAt` gives exactly the switch condition
the folding half needs. -/
theorem switch_of_lowAt {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f) (p H tl : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (htl1 : p - 3 ≤ tl) (htl2 : tl ≤ p - 2) (hlow : LowAt f tl H) :
    ∀ d : Fin m, f d ≤ p - 3 →
      ∃ s : Fin m, s.val < d.val ∧ H - p ≤ (s.val : ℤ) ∧ H - 2 ≤ f s := by
  intro d hd
  rcases hlow d (by omega) with ⟨j, hjd, hj⟩ | ⟨j, j', hjj', hj'd, hj, hj'⟩
  · -- the arm has reached the top
    refine ⟨j, hjd, ?_, by omega⟩
    have := abs_sub_le_of_isLip hf j.val ⟨0, hm⟩ j (by simp)
    rw [abs_le] at this
    have := this.2
    omega
  · -- the arm has been low and afterwards high
    refine ⟨j', by omega, ?_, by omega⟩
    have hjpos : 0 < j.val := by
      rcases Nat.eq_zero_or_pos j.val with h | h
      · exfalso
        rw [show j = (⟨0, hm⟩ : Fin m) from Fin.ext h, h0] at hj
        omega
      · exact h
    have hstep := abs_sub_le_of_isLip hf (j'.val - j.val) j j' (by omega)
    rw [abs_le] at hstep
    have h2 := hstep.2
    have hc : ((j'.val - j.val : ℕ) : ℤ) = (j'.val : ℤ) - (j.val : ℤ) := by
      push_cast [Nat.cast_sub (by omega : j.val ≤ j'.val)]; ring
    have hj1 : (1 : ℤ) ≤ (j.val : ℤ) := by exact_mod_cast hjpos
    omega

/-- **`HighAt` supplies the reflected switch.** -/
theorem switch'_of_highAt {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f) (p L th : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (hth1 : th ≤ p + 3) (hth2 : p + 2 ≤ th) (hhigh : HighAt f L th) :
    ∀ d : Fin m, p + 3 ≤ f d →
      ∃ s : Fin m, s.val < d.val ∧ p - L ≤ (s.val : ℤ) ∧ f s ≤ L + 2 := by
  intro d hd
  obtain ⟨j, hjd, hj⟩ := hhigh d (by omega)
  have hbound := abs_sub_le_of_isLip hf j.val ⟨0, hm⟩ j (by simp)
  rw [abs_le] at hbound
  have hj0 : p - (L + 1) ≤ (j.val : ℤ) := by
    have := hbound.1
    omega
  rcases le_or_gt (p - L) ((j.val : ℤ)) with hc | hc
  · exact ⟨j, hjd, hc, by omega⟩
  · -- one step short: the next time is still low, and it is still before `d`
    have hjval : (j.val : ℤ) = p - L - 1 := by omega
    have hjd' : j.val + 1 < d.val := by
      rcases Nat.lt_or_ge (j.val + 1) d.val with h | h
      · exact h
      · exfalso
        have hjd2 : j.val + 1 = d.val := by omega
        have := hf j d (by omega)
        rw [abs_le] at this
        omega
    refine ⟨⟨j.val + 1, by omega⟩, by simpa using hjd', ?_, ?_⟩
    · push_cast
      omega
    · have := hf j ⟨j.val + 1, by omega⟩ (by simp)
      rw [abs_le] at this
      omega

/-! ## What the two halves give -/

/-- **Both arms `LowAt` settles the basepoint**, at every span. No crookedness is used: the
dichotomy is what supplies the hypothesis. -/
theorem s3_of_lowAt {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L tl : ℤ) (hlip : IsLip ρ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hp1 : L + 2 ≤ ρ i) (hp2 : ρ i + 2 ≤ H)
    (htl1 : ρ i - 3 ≤ tl) (htl2 : tl ≤ ρ i - 2)
    (hG : LowAt (armG ρ i) tl H) (hT : LowAt (armT ρ i) tl H) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by
    show ρ ⟨i.val + 0, _⟩ = ρ i
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
  have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by
    show ρ ⟨i.val - 0, _⟩ = ρ i
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
  refine ⟨bumpWalkLen (ρ i) L H, bumpWalk (ρ i) H, ?_, ?_⟩
  · exact foldsOnto_bumpWalk_of_switch hmG _ (armG_isLip hlip i) (ρ i) L H hG0
      (fun j => hLb _) (fun j => hHb _) hp1 hp2
      (switch_of_lowAt hmG (armG_isLip hlip i) (ρ i) H tl hG0 htl1 htl2 hG)
  · exact foldsOnto_bumpWalk_of_switch hmT _ (armT_isLip hlip i) (ρ i) L H hT0
      (fun j => hLb _) (fun j => hHb _) hp1 hp2
      (switch_of_lowAt hmT (armT_isLip hlip i) (ρ i) H tl hT0 htl1 htl2 hT)

/-- **Both arms `HighAt` settles the basepoint**, the reflection of `s3_of_lowAt`. -/
theorem s3_of_highAt {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L th : ℤ) (hlip : IsLip ρ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hp1 : L + 2 ≤ ρ i) (hp2 : ρ i + 2 ≤ H)
    (hth1 : th ≤ ρ i + 3) (hth2 : ρ i + 2 ≤ th)
    (hG : HighAt (armG ρ i) L th) (hT : HighAt (armT ρ i) L th) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by
    show ρ ⟨i.val + 0, _⟩ = ρ i
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
  have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by
    show ρ ⟨i.val - 0, _⟩ = ρ i
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
  refine ⟨bumpWalkLen (L + H - ρ i) L H, bumpWalk' (ρ i) L H, ?_, ?_⟩
  · exact foldsOnto_bumpWalk'_of_switch hmG _ (armG_isLip hlip i) (ρ i) L H hG0
      (fun j => hLb _) (fun j => hHb _) hp1 hp2
      (switch'_of_highAt hmG (armG_isLip hlip i) (ρ i) L th hG0 hth1 hth2 hG)
  · exact foldsOnto_bumpWalk'_of_switch hmT _ (armT_isLip hlip i) (ρ i) L H hT0
      (fun j => hLb _) (fun j => hHb _) hp1 hp2
      (switch'_of_highAt hmT (armT_isLip hlip i) (ρ i) L th hT0 hth1 hth2 hT)

/-- **The basepoints the two halves settle, at every span.** Unless both arms are `HighAt` at the
levels `(ρ i - 3, H)`, the dichotomy hands both arms the `LowAt` condition and the bump walk
serves them. -/
theorem s3_of_not_highAt {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ) (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hnh : ¬ (HighAt (armG ρ i) (ρ i - 3) H ∧ HighAt (armT ρ i) (ρ i - 3) H)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i
  · exact s3_near_extreme ρ i H L hlip hLb hHb hLH hnear
  · push_neg at hnear
    obtain ⟨hlow, hhigh⟩ := hnear
    rcases dichotomy_at hcr i (ρ i - 3) H (by omega) with ⟨hg, ht⟩ | ⟨hg, ht⟩
    · exact s3_of_lowAt ρ i H L (ρ i - 3) hlip hLb hHb (by omega) (by omega) (by omega)
        (by omega) hg ht
    · exact absurd ⟨hg, ht⟩ hnh

/-- The mirror: unless both arms are `LowAt` at the levels `(L, ρ i + 3)`, the dichotomy hands
both arms the `HighAt` condition and the reflected bump walk serves them. -/
theorem s3_of_not_lowAt {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ) (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hnl : ¬ (LowAt (armG ρ i) L (ρ i + 3) ∧ LowAt (armT ρ i) L (ρ i + 3))) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i
  · exact s3_near_extreme ρ i H L hlip hLb hHb hLH hnear
  · push_neg at hnear
    obtain ⟨hlow, hhigh⟩ := hnear
    rcases dichotomy_at hcr i L (ρ i + 3) (by omega) with ⟨hg, ht⟩ | ⟨hg, ht⟩
    · exact absurd ⟨hg, ht⟩ hnl
    · exact s3_of_highAt ρ i H L (ρ i + 3) hlip hLb hHb (by omega) (by omega) (by omega)
        (by omega) hg ht

/-- **What is left of span seven.** At span seven — indeed at every span — a basepoint can fail to
be settled by the two halves only if both arms are simultaneously `HighAt (ρ i - 3) H` and
`LowAt L (ρ i + 3)`. -/
theorem s3_span_seven_of_cases {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ) (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hrest : ¬ ((HighAt (armG ρ i) (ρ i - 3) H ∧ HighAt (armT ρ i) (ρ i - 3) H) ∧
      (LowAt (armG ρ i) L (ρ i + 3) ∧ LowAt (armT ρ i) L (ρ i + 3)))) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hh : HighAt (armG ρ i) (ρ i - 3) H ∧ HighAt (armT ρ i) (ρ i - 3) H
  · exact s3_of_not_lowAt ρ σ i H L hlip hcr hLb hHb hLH (fun hl => hrest ⟨hh, hl⟩)
  · exact s3_of_not_highAt ρ σ i H L hlip hcr hLb hHb hLH hh

/-! ## The crookedness clause the leaf walks need -/

/-- **`Zig` on the forward arm.** One instance of the crookedness clause: between a time at
`L + 1` or below and a later time at `H` the arm has been at `H - 2` or above and, after that,
at `L + 2` or below. -/
theorem zig_armG {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L H : ℤ)
    (hLH : L + 4 ≤ H) : Zig (armG ρ i) L H := by
  intro s t hst hs ht
  have hi := i.isLt
  have hslt := s.isLt
  have htlt := t.isLt
  have hS : ρ ⟨i.val + s.val, by omega⟩ ≤ L + 1 := hs
  have hT : H ≤ ρ ⟨i.val + t.val, by omega⟩ := ht
  have hST : (⟨i.val + s.val, by omega⟩ : Fin n) < ⟨i.val + t.val, by omega⟩ := by
    rw [Fin.lt_def]; exact Nat.add_lt_add_left hst _
  obtain ⟨r, r', h1, h2, h3, hcase, -⟩ :=
    hcr.crooked ⟨i.val + s.val, by omega⟩ ⟨i.val + t.val, by omega⟩ hST
      (ρ ⟨i.val + s.val, by omega⟩) (ρ ⟨i.val + t.val, by omega⟩)
      ⟨⟨i.val + s.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      ⟨⟨i.val + t.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨-, hr1⟩, hr2, -⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hrlt : i.val + s.val < r.val := h1
  have hrr' : r.val < r'.val := h2
  have hr'lt : r'.val < i.val + t.val := h3
  have hrn := r.isLt
  have hr'n := r'.isLt
  refine ⟨⟨r.val - i.val, by omega⟩, ⟨r'.val - i.val, by omega⟩, by simp; omega, by simp; omega,
    by simp; omega, ?_, ?_⟩
  · show H - 2 ≤ ρ ⟨i.val + (r.val - i.val), by omega⟩
    rw [show (⟨i.val + (r.val - i.val), by omega⟩ : Fin n) = r from
      Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)]
    omega
  · show ρ ⟨i.val + (r'.val - i.val), by omega⟩ ≤ L + 2
    rw [show (⟨i.val + (r'.val - i.val), by omega⟩ : Fin n) = r' from
      Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)]
    omega

/-- **`Zig` on the backward arm.** The same clause, read through the reversed index order. -/
theorem zig_armT {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L H : ℤ)
    (hLH : L + 4 ≤ H) : Zig (armT ρ i) L H := by
  intro s t hst hs ht
  have hi := i.isLt
  have hslt := s.isLt
  have htlt := t.isLt
  have hS : ρ ⟨i.val - s.val, by omega⟩ ≤ L + 1 := hs
  have hT : H ≤ ρ ⟨i.val - t.val, by omega⟩ := ht
  have hST : (⟨i.val - t.val, by omega⟩ : Fin n) < ⟨i.val - s.val, by omega⟩ := by
    rw [Fin.lt_def]
    show i.val - t.val < i.val - s.val
    omega
  obtain ⟨r, r', h1, h2, h3, -, hcase⟩ :=
    hcr.crooked ⟨i.val - t.val, by omega⟩ ⟨i.val - s.val, by omega⟩ hST
      (ρ ⟨i.val - t.val, by omega⟩) (ρ ⟨i.val - s.val, by omega⟩)
      ⟨⟨i.val - t.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      ⟨⟨i.val - s.val, by omega⟩, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨hr1, -, hr2⟩ := hcase (by omega)
  have hwr' := hcr.width r'
  have hrlt : i.val - t.val < r.val := h1
  have hrr' : r.val < r'.val := h2
  have hr'lt : r'.val < i.val - s.val := h3
  have hrn := r.isLt
  have hr'n := r'.isLt
  refine ⟨⟨i.val - r'.val, by omega⟩, ⟨i.val - r.val, by omega⟩, by simp; omega, by simp; omega,
    by simp; omega, ?_, ?_⟩
  · show H - 2 ≤ ρ ⟨i.val - (i.val - r'.val), by omega⟩
    rw [show (⟨i.val - (i.val - r'.val), by omega⟩ : Fin n) = r' from
      Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)]
    omega
  · show ρ ⟨i.val - (i.val - r.val), by omega⟩ ≤ L + 2
    rw [show (⟨i.val - (i.val - r.val), by omega⟩ : Fin n) = r from
      Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)]
    omega

/-! ## The commissioned targets -/

/-- **`S3` at span seven.** -/
theorem s3_span_seven {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 7) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases h6 : H ≤ L + 6
  · exact s3_span_six ρ σ i H L hlip hcr hLb hHb hLH h6
  · have hH7 : H = L + 7 := by omega
    by_cases hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i
    · exact s3_near_extreme ρ i H L hlip hLb hHb hLH hnear
    · push_neg at hnear
      obtain ⟨hlow, hhigh⟩ := hnear
      by_cases hh : HighAt (armG ρ i) (ρ i - 3) H ∧ HighAt (armT ρ i) (ρ i - 3) H
      · by_cases hl : LowAt (armG ρ i) L (ρ i + 3) ∧ LowAt (armT ρ i) L (ρ i + 3)
        · -- the leaf: both arms `HighAt (ρ i - 3) H` and both arms `LowAt L (ρ i + 3)`
          obtain ⟨hhG, hhT⟩ := hh
          obtain ⟨hlG, hlT⟩ := hl
          have hi := i.isLt
          have hmG : 0 < n - i.val := by omega
          have hmT : 0 < i.val + 1 := by omega
          have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by
            show ρ ⟨i.val + 0, _⟩ = ρ i
            rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
          have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by
            show ρ ⟨i.val - 0, _⟩ = ρ i
            rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
          have hGL : ∀ j, L ≤ armG ρ i j := fun j => hLb _
          have hGH : ∀ j, armG ρ i j ≤ L + 7 := by
            intro j
            have hj := j.isLt
            have h := hHb (⟨i.val + j.val, by omega⟩ : Fin n)
            have e : armG ρ i j = ρ (⟨i.val + j.val, by omega⟩ : Fin n) := rfl
            omega
          have hTL : ∀ j, L ≤ armT ρ i j := fun j => hLb _
          have hTH : ∀ j, armT ρ i j ≤ L + 7 := by
            intro j
            have hj := j.isLt
            have h := hHb (⟨i.val - j.val, by omega⟩ : Fin n)
            have e : armT ρ i j = ρ (⟨i.val - j.val, by omega⟩ : Fin n) := rfl
            omega
          rcases (show ρ i = L + 3 ∨ ρ i = L + 4 by omega) with hp | hp
          · have e1 : ρ i - 3 = L := by omega
            have e2 : ρ i + 3 = L + 6 := by omega
            rw [e1, hH7] at hhG hhT
            rw [e2] at hlG hlT
            exact ⟨13, walk7 L,
              foldsOnto_walk7_of_leaf hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                hhG hlG (zig_armG hcr i L (L + 7) (by omega)),
              foldsOnto_walk7_of_leaf hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                hhT hlT (zig_armT hcr i L (L + 7) (by omega))⟩
          · have e1 : ρ i - 3 = L + 1 := by omega
            have e2 : ρ i + 3 = L + 7 := by omega
            rw [e1, hH7] at hhG hhT
            rw [e2] at hlG hlT
            exact ⟨13, walk7' L,
              foldsOnto_walk7'_of_leaf hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                hhG hlG,
              foldsOnto_walk7'_of_leaf hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                hhT hlT⟩
        · exact s3_of_not_lowAt ρ σ i H L hlip hcr hLb hHb hLH hl
      · exact s3_of_not_highAt ρ σ i H L hlip hcr hLb hHb hLH hh

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, for a crooked chain whose
minimal-index range is at most seven. -/
theorem theorem3_span_seven {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n)
    (hspan : ∀ s t : Fin n, (hcr.1.minIdx t : ℤ) ≤ (hcr.1.minIdx s : ℤ) + 7) :
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
    have hseven : H ≤ L + 7 := hspan tL tH
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedIvF ρ σ := isCrookedIvF_minIdx_maxIdx hcr
    obtain ⟨len, c, hG, hT⟩ := s3_span_seven ρ σ i H L hlip hcrook hLf hHf hcase hseven
    exact exists_blocks_first_of_folds href i _ _ hG hT

end HPC.Fold
