import Mathlib

/-!
# Pattern following: the combinatorial core

Batch 80. A purely combinatorial statement about integer sequences from which Bing's
Theorem 6 (pattern following) is derived in `PatGeom.lean`.

* `σ : ℕ → ℤ` is the reading of a fine chain `F` (times `0, …, T`) in a reference chain `R`
  (positions `p : ℤ`); it moves by at most one and is *crooked*: whenever two times are at
  positions at least three apart, strictly between them there is first a time near the later
  position and then a time near the earlier one.
* `τ : ℤ → ℤ` is a reading of `R` in a coarse chain `D`; it is *`w`-slow*: positions at most `w`
  apart have readings at most one apart. (Geometrically: every `R`-link within `w` of position
  `p` lies in the `D`-link `τ p`.)
* A value `v` is *allowed* at time `f` with radius `d` (`Al`) if some position within `d` of
  `σ f` reads `v`.

The main result `realize` says that for every pattern `x` (a sequence moving by at most one)
going from its minimum to its maximum, an `F`-interval going from the minimum to the maximum
admits a lift `φ` into the pattern, moving by at most one, with `x (φ f)` allowed at `f`.
-/

namespace HPC.PatCore

section Defs

variable (σ : ℕ → ℤ)

/-- The value `v` is allowed at time `f` with radius `d`. -/
def Al (τ : ℤ → ℤ) (d : ℕ) (f : ℕ) (v : ℤ) : Prop := ∃ p : ℤ, |p - σ f| ≤ d ∧ τ p = v

/-- A lift of the pattern `x` (indices in `[p, q]`) over the time interval `[a, b]`, starting at
index `i` and ending at index `j`. -/
def Real (τ : ℤ → ℤ) (w : ℕ) (x : ℕ → ℤ) (p q a b i j : ℕ) : Prop :=
  ∃ φ : ℕ → ℕ, φ a = i ∧ φ b = j ∧
    (∀ f, a ≤ f → f < b → (φ (f + 1) : ℤ) - φ f ≤ 1 ∧ (φ f : ℤ) - φ (f + 1) ≤ 1) ∧
    ∀ f, a ≤ f → f ≤ b → p ≤ φ f ∧ φ f ≤ q ∧ Al σ τ w f (x (φ f))

/-- The fine reading: moves by at most one, crooked up to time `T`. -/
structure Setting (T : ℕ) : Prop where
  lip : ∀ f, |σ (f + 1) - σ f| ≤ 1
  crook : ∀ f f', f < f' → f' ≤ T → 3 ≤ |σ f - σ f'| →
    ∃ r s, f < r ∧ r < s ∧ s < f' ∧ |σ r - σ f'| ≤ 2 ∧ |σ s - σ f| ≤ 2

end Defs

/-- The coarse reading is `w`-slow. -/
def Slow (w : ℕ) (τ : ℤ → ℤ) : Prop := ∀ p p' : ℤ, |p - p'| ≤ w → |τ p - τ p'| ≤ 1

/-- Hypotheses of the main induction. -/
structure Good (σ : ℕ → ℤ) (T B : ℕ) (τ : ℤ → ℤ) (x : ℕ → ℤ) (p q a b e : ℕ) : Prop where
  pq : p ≤ q
  ab : a ≤ b
  bT : b ≤ T
  len : q - p ≤ b - a
  xstep : ∀ i, p ≤ i → i < q → |x (i + 1) - x i| ≤ 1
  xlo : ∀ i, p ≤ i → i ≤ q → x p ≤ x i
  xhi : ∀ i, p ≤ i → i ≤ q → x i ≤ x q
  rlo : ∀ f, a ≤ f → f ≤ b → x p ≤ τ (σ f)
  rhi : ∀ f, a ≤ f → f ≤ b → τ (σ f) ≤ x q
  anca : Al σ τ e a (x p)
  ancb : Al σ τ e b (x q)
  budget : e + 2 * (q - p) ≤ B

variable {σ : ℕ → ℤ} {T : ℕ}

/-! ## Elementary facts -/

theorem slow_lip {w : ℕ} {τ : ℤ → ℤ} (hw : 1 ≤ w) (hs : Slow w τ) (p : ℤ) :
    |τ (p + 1) - τ p| ≤ 1 :=
  hs (p + 1) p (by rw [show p + 1 - p = 1 by ring]; simp; exact_mod_cast hw)

theorem sigma_dist (hS : Setting σ T) (f k : ℕ) : |σ (f + k) - σ f| ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hS.lip (f + k)
    rw [show f + (k + 1) = f + k + 1 by ring]
    calc |σ (f + k + 1) - σ f| = |(σ (f + k + 1) - σ (f + k)) + (σ (f + k) - σ f)| := by ring_nf
      _ ≤ |σ (f + k + 1) - σ (f + k)| + |σ (f + k) - σ f| := abs_add_le _ _
      _ ≤ 1 + k := by linarith
      _ = ((k + 1 : ℕ) : ℤ) := by push_cast; ring

theorem sigma_dist' (hS : Setting σ T) {f f' : ℕ} (h : f ≤ f') :
    |σ f' - σ f| ≤ (f' : ℤ) - f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := sigma_dist hS f k
  push_cast; simpa using this

theorem sigma_dist_abs (hS : Setting σ T) (f f' : ℕ) :
    |σ f' - σ f| ≤ |(f' : ℤ) - f| := by
  rcases le_total f f' with h | h
  · exact (sigma_dist' hS h).trans (le_abs_self _)
  · rw [abs_sub_comm, abs_sub_comm (f' : ℤ)]
    exact (sigma_dist' hS h).trans (le_abs_self _)

theorem al_mono {τ : ℤ → ℤ} {d d' f : ℕ} {v : ℤ} (h : d ≤ d') (hA : Al σ τ d f v) :
    Al σ τ d' f v := by
  obtain ⟨p, hp, hv⟩ := hA
  exact ⟨p, hp.trans (by exact_mod_cast h), hv⟩

theorem al_canon (τ : ℤ → ℤ) (f : ℕ) : Al σ τ 0 f (τ (σ f)) := ⟨σ f, by simp, rfl⟩

theorem al_move (hS : Setting σ T) {τ : ℤ → ℤ} {d f f' : ℕ} {v : ℤ} (k : ℕ)
    (hk : |(f' : ℤ) - f| ≤ k) (hA : Al σ τ d f v) : Al σ τ (d + k) f' v := by
  obtain ⟨p, hp, hv⟩ := hA
  refine ⟨p, ?_, hv⟩
  have h1 := sigma_dist_abs hS f f'
  calc |p - σ f'| = |(p - σ f) - (σ f' - σ f)| := by ring_nf
    _ ≤ |p - σ f| + |σ f' - σ f| := abs_sub _ _
    _ ≤ d + k := by linarith
    _ = ((d + k : ℕ) : ℤ) := by push_cast; ring

theorem tri_up {a b c k m : ℤ} (h1 : |a - b| ≤ k) (h2 : |b - c| ≤ m) : |a - c| ≤ k + m :=
  (abs_sub_le a b c).trans (by linarith)

theorem tri_lo {a b c k m : ℤ} (h1 : k ≤ |a - b|) (h2 : |b - c| ≤ m) : k - m ≤ |a - c| := by
  have := abs_sub_le a c b
  rw [abs_sub_comm c b] at this
  linarith

theorem two_le_abs {u v : ℤ} (h : u + 2 ≤ v ∨ v + 2 ≤ u) : 2 ≤ |u - v| := by
  rcases h with h | h
  · exact le_abs.mpr (Or.inr (by linarith))
  · exact le_abs.mpr (Or.inl (by linarith))

theorem natdist_le {f f' k : ℕ} (h : f' ≤ f + k) (h' : f ≤ f' + k) :
    |(f' : ℤ) - f| ≤ (k : ℕ) := by
  rw [abs_le]; constructor <;> omega

/-- Allowed values are within one of the canonical reading. -/
theorem al_near {w : ℕ} {τ : ℤ → ℤ} (hs : Slow w τ) {d f : ℕ} {v : ℤ} (hd : d ≤ w)
    (hA : Al σ τ d f v) : |τ (σ f) - v| ≤ 1 := by
  obtain ⟨p, hp, rfl⟩ := hA
  exact hs _ _ (by rw [abs_sub_comm]; exact hp.trans (by exact_mod_cast hd))

/-- Values two apart are read only at positions more than `w` apart. -/
theorem far_of_slow {w : ℕ} {τ : ℤ → ℤ} (hs : Slow w τ) {p p' : ℤ}
    (h : 2 ≤ |τ p - τ p'|) : (w : ℤ) + 1 ≤ |p - p'| := by
  by_contra hc
  have := hs p p' (by push_neg at hc; linarith)
  linarith

/-- Times allowed at values two apart are far apart. -/
theorem al_far {w : ℕ} {τ : ℤ → ℤ} (hs : Slow w τ) {d d' f f' : ℕ}
    {v v' : ℤ} (hA : Al σ τ d f v) (hA' : Al σ τ d' f' v') (hv : 2 ≤ |v - v'|) :
    (w : ℤ) + 1 - d - d' ≤ |σ f - σ f'| := by
  obtain ⟨p, hp, rfl⟩ := hA
  obtain ⟨p', hp', rfl⟩ := hA'
  have h := far_of_slow hs hv
  have : |p - p'| ≤ |p - σ f| + |σ f - σ f'| + |σ f' - p'| := by
    calc |p - p'| = |(p - σ f) + (σ f - σ f') + (σ f' - p')| := by ring_nf
      _ ≤ |(p - σ f) + (σ f - σ f')| + |σ f' - p'| := abs_add_le _ _
      _ ≤ |p - σ f| + |σ f - σ f'| + |σ f' - p'| := by linarith [abs_add_le (p - σ f) (σ f - σ f')]
  rw [abs_sub_comm (σ f') p'] at this
  linarith

/-- Time distance dominates position distance. -/
theorem time_ge (hS : Setting σ T) {f f' : ℕ} (h : f ≤ f') {c : ℤ} (hc : c ≤ |σ f - σ f'|) :
    c ≤ (f' : ℤ) - f := by
  have := sigma_dist' hS h
  rw [abs_sub_comm] at hc
  linarith

/-- Discrete intermediate values. -/
theorem ivt_nat (g : ℕ → ℤ) (hg : ∀ k, |g (k + 1) - g k| ≤ 1) :
    ∀ (k : ℕ) (u : ℤ), (g 0 ≤ u ∧ u ≤ g k) ∨ (g k ≤ u ∧ u ≤ g 0) → ∃ j, j ≤ k ∧ g j = u := by
  intro k
  induction k with
  | zero => intro u h; exact ⟨0, le_rfl, by omega⟩
  | succ k ih =>
    intro u h
    have hl := hg k
    rw [abs_le] at hl
    by_cases hu : (g 0 ≤ u ∧ u ≤ g k) ∨ (g k ≤ u ∧ u ≤ g 0)
    · obtain ⟨j, hj, hj'⟩ := ih u hu
      exact ⟨j, by omega, hj'⟩
    · exact ⟨k + 1, le_rfl, by omega⟩

/-- Intermediate values between two positions, located near the first one. -/
theorem ivt_between {w : ℕ} {τ : ℤ → ℤ} (hw : 1 ≤ w) (hs : Slow w τ) (p p' : ℤ) (u : ℤ)
    (h : (τ p ≤ u ∧ u ≤ τ p') ∨ (τ p' ≤ u ∧ u ≤ τ p)) :
    ∃ p'', |p'' - p| ≤ |p' - p| ∧ τ p'' = u := by
  rcases le_total p p' with hpp | hpp
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, p' = p + k := ⟨(p' - p).toNat, by omega⟩
    obtain ⟨j, hj, hj'⟩ := ivt_nat (fun j => τ (p + j))
      (fun j => by have := slow_lip hw hs (p + j); push_cast; rwa [← add_assoc]) k u
      (by simp only [Nat.cast_zero, add_zero]; rw [← hk]; exact h)
    refine ⟨p + j, ?_, hj'⟩
    rw [hk]; simp only [add_sub_cancel_left]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]; exact_mod_cast hj
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, p' = p - k := ⟨(p - p').toNat, by omega⟩
    obtain ⟨j, hj, hj'⟩ := ivt_nat (fun j => τ (p - j))
      (fun j => by
        have := slow_lip hw hs (p - (j + 1))
        push_cast
        rw [show p - ((j : ℤ) + 1) + 1 = p - j by ring] at this
        rw [abs_sub_comm]; exact this) k u
      (by simp only [Nat.cast_zero, sub_zero]; rw [← hk]; exact h)
    refine ⟨p - j, ?_, hj'⟩
    rw [hk]
    rw [show p - (j : ℤ) - p = -(j : ℤ) by ring, show p - (k : ℤ) - p = -(k : ℤ) by ring,
      abs_neg, abs_neg]
    simp only [Nat.abs_cast]; exact_mod_cast hj

/-! ## Lifts: gluing, symmetries, ramps -/

section Real

variable {τ : ℤ → ℤ} {w : ℕ} {x : ℕ → ℤ}

theorem real_glue {p q a m b i j k : ℕ} (h1 : Real σ τ w x p q a m i j)
    (h2 : Real σ τ w x p q m b j k) (ham : a ≤ m) (hmb : m ≤ b) :
    Real σ τ w x p q a b i k := by
  obtain ⟨φ1, h1a, h1m, h1l, h1v⟩ := h1
  obtain ⟨φ2, h2m, h2b, h2l, h2v⟩ := h2
  refine ⟨fun f => if f ≤ m then φ1 f else φ2 f, ?_, ?_, ?_, ?_⟩
  · simp [ham, h1a]
  · by_cases hbm : b ≤ m
    · have : b = m := le_antisymm hbm hmb
      subst this
      simp [h1m, ← h2m, h2b]
    · simp [hbm, h2b]
  · intro f hf1 hf2
    by_cases hfm : f + 1 ≤ m
    · have : f ≤ m := by omega
      simp only [hfm, this, if_true]
      exact h1l f hf1 (by omega)
    · by_cases hfm' : f ≤ m
      · have : f = m := by omega
        subst this
        simp only [hfm, hfm', if_true, if_false]
        rw [h1m, ← h2m]
        exact h2l f le_rfl (by omega)
      · simp only [hfm, hfm', if_false]
        exact h2l f (by omega) hf2
  · intro f hf1 hf2
    by_cases hfm : f ≤ m
    · simp only [hfm, if_true]; exact h1v f hf1 hfm
    · simp only [hfm, if_false]; exact h2v f (by omega) hf2

theorem real_widen {p q p' q' a b i j : ℕ} (h : Real σ τ w x p' q' a b i j) (hp : p ≤ p')
    (hq : q' ≤ q) : Real σ τ w x p q a b i j := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := h
  exact ⟨φ, h1, h2, h3, fun f hf1 hf2 => by
    obtain ⟨a1, a2, a3⟩ := h4 f hf1 hf2; exact ⟨by omega, by omega, a3⟩⟩

theorem al_neg_iff {d f : ℕ} {v : ℤ} : Al σ (fun z => -τ z) d f (-v) ↔ Al σ τ d f v := by
  constructor
  · rintro ⟨p, hp, hv⟩; exact ⟨p, hp, by simpa using hv⟩
  · rintro ⟨p, hp, hv⟩; exact ⟨p, hp, by simp [hv]⟩

theorem real_of_neg {p q a b i j : ℕ}
    (h : Real σ (fun z => -τ z) w (fun k => -x k) p q a b i j) : Real σ τ w x p q a b i j := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := h
  exact ⟨φ, h1, h2, h3, fun f hf1 hf2 => by
    obtain ⟨a1, a2, a3⟩ := h4 f hf1 hf2; exact ⟨a1, a2, al_neg_iff.mp a3⟩⟩

theorem real_reflect {p q a b i j : ℕ}
    (h : Real σ τ w (fun k => x (p + q - k)) p q a b i j) :
    Real σ τ w x p q a b (p + q - i) (p + q - j) := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := h
  refine ⟨fun f => p + q - φ f, by simp [h1], by simp [h2], ?_, ?_⟩
  · intro f hf1 hf2
    obtain ⟨a1, a2, -⟩ := h4 f hf1 (by omega)
    obtain ⟨b1, b2, -⟩ := h4 (f + 1) (by omega) (by omega)
    obtain ⟨c1, c2⟩ := h3 f hf1 hf2
    simp only []
    constructor <;> push_cast [show φ f ≤ p + q by omega, show φ (f + 1) ≤ p + q by omega] <;>
      linarith
  · intro f hf1 hf2
    obtain ⟨a1, a2, a3⟩ := h4 f hf1 hf2
    refine ⟨?_, ?_, a3⟩ <;> dsimp only <;> omega

theorem slow_neg (hs : Slow w τ) : Slow w (fun z => -τ z) := by
  intro a b h
  have := hs a b h
  rw [show -τ a - -τ b = -(τ a - τ b) by ring, abs_neg]
  exact this

/-- The constant lift over a single time. -/
theorem real_point {p q a i : ℕ} (hp : p ≤ i) (hq : i ≤ q) (hA : Al σ τ w a (x i)) :
    Real σ τ w x p q a a i i :=
  ⟨fun _ => i, rfl, rfl, fun f h1 h2 => by omega, fun f h1 h2 => by
    have : f = a := by omega
    subst this; exact ⟨hp, hq, hA⟩⟩

/-- One step from index `i` to index `i + 1`. -/
theorem real_step {p q a i : ℕ} (hp : p ≤ i) (hq : i + 1 ≤ q) (hA : Al σ τ w a (x i))
    (hA' : Al σ τ w (a + 1) (x (i + 1))) : Real σ τ w x p q a (a + 1) i (i + 1) := by
  refine ⟨fun f => if f ≤ a then i else i + 1, by simp, by simp, ?_, ?_⟩
  · intro f h1 h2
    have : f = a := by omega
    subst this; simp
  · intro f h1 h2
    by_cases hf : f ≤ a
    · have : f = a := by omega
      subst this; simp only [le_refl, if_true]; exact ⟨hp, by omega, hA⟩
    · have : f = a + 1 := by omega
      subst this; simp only [hf, if_false]; exact ⟨by omega, hq, hA'⟩

/-- The ramp: if every value of the pattern on `[p, q]` is allowed throughout `[a, b]` and the
interval is long enough, the pattern is lifted. -/
theorem real_ramp {p q a b : ℕ} (hpq : p ≤ q) (hlen : q - p ≤ b - a)
    (hA : ∀ f, a ≤ f → f ≤ b → ∀ i, p ≤ i → i ≤ q → Al σ τ w f (x i)) :
    Real σ τ w x p q a b p q := by
  refine ⟨fun f => min (p + (f - a)) q, by simp; omega, by simp; omega, ?_, ?_⟩
  · intro f h1 h2
    simp only []
    constructor <;> omega
  · intro f h1 h2
    refine ⟨?_, ?_, hA f h1 h2 _ ?_ ?_⟩ <;> dsimp only <;> omega

end Real

end HPC.PatCore
