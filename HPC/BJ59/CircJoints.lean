import HPC.Plane.Joints

/-!
# Batch 202, §5: joint positions for lifted patterns

The joint positions of batch 84 (`HPC/Plane/Joints.lean`) are defined for finite patterns
`Fin n → Fin m`. For a lifted pattern `x : ℤ → ℤ` of degree one (`x (t + Q) = x t + 1`) we
use one finite window: the restriction of `x` to the indices `−M, …, QN + M − 1`
(`M = S + 3`), with values shifted to be positive. The joint position of an integer index `t` is
read off the window at the representative of `t` modulo `QN`, shifted by `2N` per period
(`jointZ`). The only non-local point, the joint at the end of the window, is handled by a shift
lemma (`P_shift`): joint positions are determined by the pattern near the joint.

`link_facts_Z` is `Joints.link_facts` for every integer index.
-/

namespace HPC.BJ59

open HPC.Plane HPC.Plane.Joints

namespace CircJ

/-! ### Joint positions are local -/

section Shift

variable {n m : ℕ} (x : Fin n → Fin m) (N : ℕ)

theorem dv_shift {t D : ℕ} {c : ℤ} (hlo : N ≤ t) (hn : t + D + N ≤ n)
    (hsh : ∀ s : ℕ, t ≤ s + N → s + 1 ≤ t + N → xe x (s + D) = xe x s + c) (v : ℤ) :
    dv x N (t + D) (v + c) = dv x N t v := by
  apply le_antisymm
  · rcases dv_cases (x := x) (N := N) t v with h | ⟨s, hs, hd⟩
    · rw [h]; exact dv_le_cap _ _
    · by_cases hcap : dv x N t v = 2 * N
      · rw [hcap]; exact dv_le_cap _ _
      · have hlt : dd t s < 2 * N := lt_of_le_of_lt hd
          (lt_of_le_of_ne (dv_le_cap _ _) hcap)
        unfold dd at hlt
        have hs1 : t ≤ s.val + N := by omega
        have hs2 : s.val + 1 ≤ t + N := by omega
        have hsD : s.val + D < n := by omega
        have e := hsh s.val hs1 hs2
        rw [xe_of_lt hsD, xe_of_lt s.isLt] at e
        refine le_trans (dv_le (x := x) (N := N) (t := t + D) ⟨s.val + D, hsD⟩
          (by rw [e, hs])) (le_trans (le_of_eq ?_) hd)
        unfold dd; push_cast; congr 1; ring
  · rcases dv_cases (x := x) (N := N) (t + D) (v + c) with h | ⟨s, hs, hd⟩
    · rw [h]; exact dv_le_cap _ _
    · by_cases hcap : dv x N (t + D) (v + c) = 2 * N
      · rw [hcap]; exact dv_le_cap _ _
      · have hlt : dd (t + D) s < 2 * N := lt_of_le_of_lt hd
          (lt_of_le_of_ne (dv_le_cap _ _) hcap)
        unfold dd at hlt
        have hsD : D ≤ s.val := by omega
        have hs1 : t ≤ (s.val - D) + N := by omega
        have hs2 : (s.val - D) + 1 ≤ t + N := by omega
        set s0 : Fin n := ⟨s.val - D, by omega⟩ with hs0
        have e := hsh (s.val - D) hs1 hs2
        rw [show s.val - D + D = s.val by omega, xe_of_lt s.isLt,
          xe_of_lt (show s.val - D < n by omega)] at e
        have e' : ((x s0 : ℕ) : ℤ) = v := by rw [hs0]; linarith
        refine le_trans (dv_le (x := x) (N := N) (t := t) s0 e') (le_trans (le_of_eq ?_) hd)
        rw [hs0]
        unfold dd; congr 1; push_cast [Nat.cast_sub hsD]; ring

/-- **Joint positions are local**: a pattern that repeats, shifted by `c`, around the joints `t`
and `t + D` has joint positions differing by `2c`. -/
theorem P_shift {t D : ℕ} {c : ℤ} (hN1 : 1 ≤ N) (ht : 1 ≤ t) (hlo : N ≤ t) (hn : t + D + N ≤ n)
    (hsh : ∀ s : ℕ, t ≤ s + N + 1 → s + 1 ≤ t + N → xe x (s + D) = xe x s + c) :
    P x N (t + D) = P x N t + 2 * c := by
  have hsh' : ∀ s : ℕ, t ≤ s + N → s + 1 ≤ t + N → xe x (s + D) = xe x s + c :=
    fun s h1 h2 => hsh s (by omega) h2
  have e0 : xe x (t + D) = xe x t + c := hsh t (by omega) (by omega)
  have e1 : xe x (t + D - 1) = xe x (t - 1) + c := by
    rw [show t + D - 1 = (t - 1) + D by omega]; exact hsh (t - 1) (by omega) (by omega)
  have hf : fpos x N (t + D) = fpos x N t := by
    unfold fpos
    rw [e0, show xe x t + c - 1 = (xe x t - 1) + c by ring,
      show xe x t + c + 1 = (xe x t + 1) + c by ring, dv_shift x N hlo hn hsh',
      dv_shift x N hlo hn hsh']
  unfold P
  rw [e0, e1, hf]
  by_cases h : xe x (t - 1) = xe x t
  · rw [if_pos (by rw [h]), if_pos h]; push_cast; ring
  · rw [if_neg (by intro h'; exact h (by linarith)), if_neg h]
    push_cast
    rw [min_add_add_right]; ring

end Shift

/-! ### The window of a lifted pattern -/

section Window

variable (x : ℤ → ℤ) (Q N S : ℕ)

/-- The half-margin of the window. -/
def wM : ℕ := S + 3

/-- The period in indices. -/
def wD : ℕ := Q * N

/-- The length of the window. -/
def wn : ℕ := wD Q N + 2 * wM S

/-- The value shift of the window. -/
def wb : ℤ := x (-(wM S : ℤ)) - wn Q N S - 1

variable {x}

theorem abs_sub_le_of_step (hstep : ∀ t, |x (t + 1) - x t| ≤ 1) (a c : ℤ) :
    |x a - x c| ≤ |a - c| := by
  have key : ∀ a c : ℤ, a ≤ c → |x c - x a| ≤ c - a := by
    intro a c hac
    induction c, hac using Int.le_induction with
    | base => simp
    | succ c _ ih =>
        have := hstep c
        rw [abs_le] at this ih ⊢
        constructor <;> linarith
  rcases le_total a c with h | h
  · rw [abs_sub_comm (x a), abs_sub_comm a, abs_of_nonneg (sub_nonneg.mpr h)]; exact key a c h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]; exact key c a h

theorem wval_bounds (hstep : ∀ t, |x (t + 1) - x t| ≤ 1) (s : ℕ) (hs : s < wn Q N S) :
    2 ≤ x (s - wM S) - wb x Q N S ∧ x (s - wM S) - wb x Q N S ≤ 2 * wn Q N S := by
  have := abs_sub_le_of_step hstep (s - wM S) (-(wM S : ℤ))
  rw [show (s : ℤ) - wM S - -(wM S : ℤ) = s by ring, abs_of_nonneg (Int.natCast_nonneg s)] at this
  rw [abs_le] at this
  unfold wb
  constructor <;> omega

/-- The window pattern: `s ↦ x (s − M) − b`. -/
def xw (hstep : ∀ t, |x (t + 1) - x t| ≤ 1) : Fin (wn Q N S) → Fin (2 * wn Q N S + 3) :=
  fun s => ⟨(x (s - wM S) - wb x Q N S).toNat, by
    have := wval_bounds Q N S hstep s s.isLt; omega⟩

variable (hstep : ∀ t, |x (t + 1) - x t| ≤ 1)

theorem xw_val (s : Fin (wn Q N S)) :
    (((xw Q N S hstep s : Fin _) : ℕ) : ℤ) = x (s - wM S) - wb x Q N S := by
  have := wval_bounds Q N S hstep s s.isLt
  simp only [xw]; omega

theorem xe_xw {s : ℕ} (hs : s < wn Q N S) :
    xe (xw Q N S hstep) s = x (s - wM S) - wb x Q N S := by
  rw [xe_of_lt hs, xw_val]

theorem xw_unitSteps : UnitSteps (xw Q N S hstep) := by
  intro t t' h
  rw [xw_val, xw_val]
  have := hstep (t - wM S)
  rw [show (t' : ℤ) - wM S = (t : ℤ) - wM S + 1 by rw [h]; push_cast; ring]
  rw [abs_le] at this
  omega

theorem xw_slow (hslow : ∀ s t, x s + 2 ≤ x t → (S : ℤ) ≤ |s - t|) :
    Slow (xw Q N S hstep) S := by
  intro s s' h
  rw [xw_val, xw_val] at h
  have := hslow _ _ (show x (s - wM S) + 2 ≤ x (s' - wM S) by omega)
  rw [show (s : ℤ) - wM S - (s' - wM S) = s - s' by ring, Int.abs_eq_natAbs] at this
  omega

/-- **The joint position of an integer index** (commission §5, "Joint positions"). -/
noncomputable def jointZ (t : ℤ) : ℝ :=
  P (xw Q N S hstep) S ((t % (wD Q N : ℤ)) + wM S).toNat + 2 * (wb x Q N S : ℝ) +
    2 * N * (t / (wD Q N : ℤ) : ℤ)

variable (hper : ∀ t, x (t + Q) = x t + 1)
include hper

omit hstep in
theorem x_add_mul (t j : ℤ) : x (t + j * Q) = x t + j := by
  induction j using Int.induction_on with
  | zero => simp
  | succ j ih => rw [show t + (j + 1) * Q = (t + j * Q) + Q by ring, hper, ih]; ring
  | pred j ih =>
      have := hper (t + (-j - 1) * Q)
      rw [show t + (-j - 1) * Q + Q = t + (-j : ℤ) * Q by ring, ih] at this
      linarith

omit hstep in
theorem x_add_D (t j : ℤ) : x (t + j * wD Q N) = x t + j * N := by
  have := x_add_mul Q hper t (j * N)
  rw [show t + j * N * (Q : ℤ) = t + j * (wD Q N : ℕ) by unfold wD; push_cast; ring] at this
  rw [this]

omit hper in
theorem jointZ_add (t : ℤ) (hD : 0 < wD Q N) :
    jointZ Q N S hstep (t + wD Q N) = jointZ Q N S hstep t + 2 * N := by
  unfold jointZ
  have hD' : (wD Q N : ℤ) ≠ 0 := by omega
  rw [Int.add_emod_right, Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hD']
  push_cast; ring

/-- The joint after the last link of a period, read off the window. -/
theorem jointZ_succ (hS : 12 ≤ S) (hD : 0 < wD Q N) (t : ℤ) :
    jointZ Q N S hstep (t + 1) =
      P (xw Q N S hstep) S ((t % (wD Q N : ℤ)) + wM S).toNat.succ + 2 * (wb x Q N S : ℝ) +
        2 * N * (t / (wD Q N : ℤ) : ℤ) := by
  have hDz : (0 : ℤ) < wD Q N := by exact_mod_cast hD
  have h0 := Int.emod_nonneg t hDz.ne'
  have h1 := Int.emod_lt_of_pos t hDz
  have e := Int.mul_ediv_add_emod t (wD Q N)
  unfold jointZ
  by_cases hr : t % (wD Q N : ℤ) + 1 < wD Q N
  · have em : (t + 1) % (wD Q N : ℤ) = t % (wD Q N : ℤ) + 1 := by
      rw [Int.add_emod, Int.emod_eq_of_lt (by norm_num) (by omega : (1 : ℤ) < wD Q N)]
      exact Int.emod_eq_of_lt (by omega) hr
    have ed : (t + 1) / (wD Q N : ℤ) = t / (wD Q N : ℤ) := by
      have := Int.mul_ediv_add_emod (t + 1) (wD Q N)
      rw [em] at this
      have h3 : (wD Q N : ℤ) * ((t + 1) / (wD Q N : ℤ)) = (wD Q N : ℤ) * (t / (wD Q N : ℤ)) := by
        linarith
      exact mul_left_cancel₀ hDz.ne' h3
    rw [em, ed, show (t % (wD Q N : ℤ) + 1 + wM S).toNat = (t % (wD Q N : ℤ) + wM S).toNat.succ by
      omega]
  · have hr' : t % (wD Q N : ℤ) = wD Q N - 1 := by omega
    have em : (t + 1) % (wD Q N : ℤ) = 0 := by
      have : t + 1 = (t / (wD Q N : ℤ) + 1) * wD Q N := by rw [add_mul]; linarith
      rw [this]; simp
    have ed : (t + 1) / (wD Q N : ℤ) = t / (wD Q N : ℤ) + 1 := by
      have : t + 1 = (t / (wD Q N : ℤ) + 1) * wD Q N := by rw [add_mul]; linarith
      rw [this, Int.mul_ediv_cancel _ (by omega : (wD Q N : ℤ) ≠ 0)]
    rw [em, ed, hr', show ((wD Q N : ℤ) - 1 + wM S).toNat.succ = wM S + wD Q N by omega,
      show ((0 : ℤ) + wM S).toNat = wM S by omega]
    -- the shift lemma
    have hsh := P_shift (xw Q N S hstep) S (t := wM S) (D := wD Q N) (c := N) (by omega)
      (by unfold wM; omega)
      (by unfold wM; omega) (by unfold wn wM; omega) (by
        intro s h1 h2
        rw [xe_xw Q N S hstep (by unfold wn wM at *; omega),
          xe_xw Q N S hstep (by unfold wn wM at *; omega)]
        push_cast
        have := x_add_D Q N hper ((s : ℤ) - wM S) 1
        rw [show (s : ℤ) - wM S + 1 * (wD Q N : ℤ) = (s : ℤ) + wD Q N - wM S by ring] at this
        rw [this]; ring)
    rw [hsh]; push_cast; ring

/-- `Joints.link_facts` for every integer index (commission §5: "the lemmas of `Joints`
transfer"). -/
theorem link_facts_Z (hS : 12 ≤ S) (hD : 0 < wD Q N)
    (hslow : ∀ s t, x s + 2 ≤ x t → (S : ℤ) ≤ |s - t|) (t : ℤ) :
    (2 * (x t : ℝ) + 1 / 2 ≤ min (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) ∧
      max (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) ≤ 2 * (x t : ℝ) + 5 / 2) ∧
    (∀ l : ℤ, 2 * (l : ℝ) < max (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) + 1 / 10 →
      min (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) - 1 / 10 < 2 * l + 3 →
      ∃ t' : ℤ, |t' - t| ≤ 1 ∧ x t' = l) ∧
    (max (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) -
        min (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) ≤ 1 / (2 * S) ∨
      ∃ k : ℤ, 2 * (k : ℝ) + 8 / 5 + 1 / 20 ≤
          min (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) ∧
        max (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) ≤ 2 * (k : ℝ) + 17 / 5 - 1 / 20) := by
  have hDz : (0 : ℤ) < wD Q N := by exact_mod_cast hD
  have h0 := Int.emod_nonneg t hDz.ne'
  have h1 := Int.emod_lt_of_pos t hDz
  have et := Int.mul_ediv_add_emod t (wD Q N)
  set r := t % (wD Q N : ℤ) with hr
  set j := t / (wD Q N : ℤ) with hj
  set idx := (r + wM S).toNat with hidx
  have hidx' : (idx : ℤ) = r + wM S := by omega
  have hidxn : idx < wn Q N S := by unfold wn; omega
  have hP0 : jointZ Q N S hstep t = P (xw Q N S hstep) S idx + 2 * (wb x Q N S : ℝ) +
      2 * N * (j : ℝ) := rfl
  have hP1 : jointZ Q N S hstep (t + 1) = P (xw Q N S hstep) S (idx + 1) +
      2 * (wb x Q N S : ℝ) + 2 * N * (j : ℝ) := jointZ_succ Q N S hstep hper hS hD t
  have hxe : xe (xw Q N S hstep) idx = x t - N * j - wb x Q N S := by
    rw [xe_xw Q N S hstep hidxn, hidx']
    have := x_add_D Q N hper r j
    rw [show r + j * (wD Q N : ℤ) = t by linarith [mul_comm (wD Q N : ℤ) j]] at this
    rw [show r + (wM S : ℤ) - wM S = r by ring, this]; ring
  have hxe2 := wval_bounds Q N S hstep idx hidxn
  rw [← xe_xw Q N S hstep hidxn] at hxe2
  obtain ⟨⟨f1, f2⟩, f3, f4⟩ := Joints.link_facts (xw_unitSteps Q N S hstep)
    (xw_slow Q N S hstep hslow) hS hidxn
  set A : ℝ := 2 * (wb x Q N S : ℝ) + 2 * N * (j : ℝ) with hA
  have emin : min (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) =
      min (P (xw Q N S hstep) S idx) (P (xw Q N S hstep) S (idx + 1)) + A := by
    have e : ∀ a : ℝ, a + 2 * (wb x Q N S : ℝ) + 2 * N * (j : ℝ) = a + A := fun a => by
      rw [hA]; ring
    rw [hP0, hP1, e, e, min_add_add_right]
  have emax : max (jointZ Q N S hstep t) (jointZ Q N S hstep (t + 1)) =
      max (P (xw Q N S hstep) S idx) (P (xw Q N S hstep) S (idx + 1)) + A := by
    have e : ∀ a : ℝ, a + 2 * (wb x Q N S : ℝ) + 2 * N * (j : ℝ) = a + A := fun a => by
      rw [hA]; ring
    rw [hP0, hP1, e, e, max_add_add_right]
  have hxe' : ((xe (xw Q N S hstep) idx : ℤ) : ℝ) = (x t : ℝ) - N * j - wb x Q N S := by
    rw [hxe]; push_cast; ring
  rw [hxe'] at f1 f2
  rw [emin, emax]
  refine ⟨⟨by rw [hA]; linarith, by rw [hA]; linarith⟩, ?_, ?_⟩
  · intro l hl1 hl2
    set lf := l - wb x Q N S - N * j with hlf
    have hlx : x t - 1 ≤ l := by
      have : ((x t : ℤ) : ℝ) - 2 < l := by rw [hA] at hl2; linarith
      have : (x t - 2 : ℤ) < l := by exact_mod_cast (by push_cast; linarith : ((x t - 2 : ℤ) : ℝ) < l)
      omega
    have hlf0 : 0 ≤ lf := by omega
    have hcast : ((lf.toNat : ℕ) : ℝ) = (l : ℝ) - wb x Q N S - N * j := by
      rw [show ((lf.toNat : ℕ) : ℝ) = ((lf.toNat : ℤ) : ℝ) from rfl, Int.toNat_of_nonneg hlf0,
        hlf]; push_cast; ring
    obtain ⟨t', ht', e⟩ := f3 lf.toNat (by rw [hcast]; rw [hA] at hl1; linarith)
      (by rw [hcast]; rw [hA] at hl2; linarith)
    rw [Int.toNat_of_nonneg hlf0, xw_val] at e
    refine ⟨(t' : ℤ) - wM S + j * wD Q N, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith [mul_comm (wD Q N : ℤ) j]
    · rw [x_add_D Q N hper]; linarith
  · rcases f4 with h | ⟨k, hk1, hk2⟩
    · left; linarith
    · right
      refine ⟨k + wb x Q N S + N * j, ?_, ?_⟩
      · push_cast; rw [hA]; linarith
      · push_cast; rw [hA]; linarith

end Window

end CircJ

end HPC.BJ59
