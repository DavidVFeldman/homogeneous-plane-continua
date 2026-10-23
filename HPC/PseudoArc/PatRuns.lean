import HPC.PseudoArc.PatMain

/-!
# Pattern following: lifts over runs

Batch 80. Consequences of the core theorem `HPC.PatCore.realize` used for Bing's Theorem 5:
lifts over an arbitrary time interval `[a, b]` of the fine reading (time shift), in reverse
(time reversal), and over *excursions* — intervals where the coarse reading starts and ends at
the minimum (or at the maximum) of the pattern. `run_lift` combines the four cases: whenever the
coarse reading lies between the two end values of the pattern and is at one of the two end values
at both ends of the interval, the pattern admits a lift over the interval.
-/

namespace HPC.PatCore

variable {σ : ℕ → ℤ} {T W : ℕ} {τ : ℤ → ℤ} {x : ℕ → ℤ}

/-! ## Time shift and time reversal -/

theorem setting_shift (hS : Setting σ T) {a b : ℕ} (hb : b ≤ T) :
    Setting (fun f => σ (a + f)) (b - a) := by
  constructor
  · intro f; simpa [add_assoc] using hS.lip (a + f)
  · intro f f' hff' hf' h3
    obtain ⟨r, s, h1, h2, h3', h4, h5⟩ := hS.crook (a + f) (a + f') (by omega) (by omega) h3
    refine ⟨r - a, s - a, by omega, by omega, by omega, ?_, ?_⟩
    · rw [show a + (r - a) = r by omega]; exact h4
    · rw [show a + (s - a) = s by omega]; exact h5

theorem real_of_shift {a b M i j : ℕ} (hab : a ≤ b)
    (h : Real (fun f => σ (a + f)) τ W x 0 M 0 (b - a) i j) : Real σ τ W x 0 M a b i j := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := h
  refine ⟨fun f => φ (f - a), by simpa using h1, by simpa using h2, ?_, ?_⟩
  · intro f hf1 hf2
    have := h3 (f - a) (Nat.zero_le _) (by omega)
    dsimp only
    rw [show f + 1 - a = f - a + 1 by omega]; exact this
  · intro f hf1 hf2
    obtain ⟨a1, a2, p, hp, hv⟩ := h4 (f - a) (Nat.zero_le _) (by omega)
    refine ⟨a1, a2, p, ?_, hv⟩
    simp only at hp
    rw [show a + (f - a) = f by omega] at hp; exact hp

theorem setting_rev (hS : Setting σ T) {a b : ℕ} (hb : b ≤ T) :
    Setting (fun f => σ (b - f)) (b - a) := by
  constructor
  · intro f
    by_cases hf : f < b
    · have := hS.lip (b - (f + 1))
      rw [show b - (f + 1) + 1 = b - f by omega, abs_sub_comm] at this
      exact this
    · rw [show b - (f + 1) = b - f by omega]; simp
  · intro f f' hff' hf' h3
    rw [abs_sub_comm] at h3
    obtain ⟨r, s, h1, h2, h3', h4, h5⟩ := hS.crook (b - f') (b - f) (by omega) (by omega) h3
    refine ⟨b - s, b - r, by omega, by omega, by omega, ?_, ?_⟩
    · rw [show b - (b - s) = s by omega]; exact h5
    · rw [show b - (b - r) = r by omega]; exact h4

theorem real_of_rev {a b M i j : ℕ} (hab : a ≤ b)
    (h : Real (fun f => σ (b - f)) τ W x 0 M 0 (b - a) i j) : Real σ τ W x 0 M a b j i := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := h
  refine ⟨fun f => φ (b - f), by simpa using h2, by simpa using h1, ?_, ?_⟩
  · intro f hf1 hf2
    have := h3 (b - (f + 1)) (Nat.zero_le _) (by omega)
    rw [show b - (f + 1) + 1 = b - f by omega] at this
    exact ⟨this.2, this.1⟩
  · intro f hf1 hf2
    obtain ⟨a1, a2, p, hp, hv⟩ := h4 (b - f) (Nat.zero_le _) (by omega)
    refine ⟨a1, a2, p, ?_, hv⟩
    simp only at hp
    rw [show b - (b - f) = f by omega] at hp; exact hp

/-! ## Ramps up and down -/

section Ramps

variable {M a b : ℕ}

/-- The core theorem over an arbitrary time interval. -/
theorem run_up (hS : Setting σ T) (hs : Slow W τ) (hW : 4 * (M + 1) + 10 ≤ W) (hab : a ≤ b)
    (hb : b ≤ T) (hxs : ∀ i, i < M → |x (i + 1) - x i| ≤ 1) (hxlo : ∀ i, i ≤ M → x 0 ≤ x i)
    (hxhi : ∀ i, i ≤ M → x i ≤ x M) (hrlo : ∀ f, a ≤ f → f ≤ b → x 0 ≤ τ (σ f))
    (hrhi : ∀ f, a ≤ f → f ≤ b → τ (σ f) ≤ x M) (ha : τ (σ a) = x 0) (hbv : τ (σ b) = x M)
    (hlen : M ≤ b - a) : Real σ τ W x 0 M a b 0 M := by
  have h := realize (σ := fun f => σ (a + f)) (T := b - a) (N := M + 1) (x := x)
    (setting_shift hS hb) hW hs (by omega) (fun i hi => hxs i (by omega))
    (fun i hi => hxlo i (by omega)) (fun i hi => by simpa using hxhi i (by omega))
    (fun f hf => hrlo _ (by omega) (by omega)) (fun f hf => by simpa using hrhi _ (by omega) (by omega)) (by simpa using ha) (by simpa [show a + (b - a) = b by omega] using hbv)
    (by omega)
  simp only [Nat.add_sub_cancel] at h
  exact real_of_shift hab h

/-- The core theorem over an arbitrary time interval, the reading going down. -/
theorem run_down (hS : Setting σ T) (hs : Slow W τ) (hW : 4 * (M + 1) + 10 ≤ W) (hab : a ≤ b)
    (hb : b ≤ T) (hxs : ∀ i, i < M → |x (i + 1) - x i| ≤ 1) (hxlo : ∀ i, i ≤ M → x 0 ≤ x i)
    (hxhi : ∀ i, i ≤ M → x i ≤ x M) (hrlo : ∀ f, a ≤ f → f ≤ b → x 0 ≤ τ (σ f))
    (hrhi : ∀ f, a ≤ f → f ≤ b → τ (σ f) ≤ x M) (ha : τ (σ a) = x M) (hbv : τ (σ b) = x 0)
    (hlen : M ≤ b - a) : Real σ τ W x 0 M a b M 0 := by
  have h := realize (σ := fun f => σ (b - f)) (T := b - a) (N := M + 1) (x := x)
    (setting_rev hS hb) hW hs (by omega) (fun i hi => hxs i (by omega))
    (fun i hi => hxlo i (by omega)) (fun i hi => by simpa using hxhi i (by omega))
    (fun f hf => hrlo _ (by omega) (by omega)) (fun f hf => by simpa using hrhi _ (by omega) (by omega)) (by simpa using hbv) (by simpa [show b - (b - a) = a by omega] using ha)
    (by omega)
  simp only [Nat.add_sub_cancel] at h
  exact real_of_rev hab h

end Ramps

/-! ## Excursions -/

/-- Distinct readings two apart force a long time interval. -/
theorem long_of_gap (hS : Setting σ T) (hs : Slow W τ) {f f' : ℕ} (h : f ≤ f')
    (hg : τ (σ f) + 2 ≤ τ (σ f') ∨ τ (σ f') + 2 ≤ τ (σ f)) : W < f' - f := by
  by_contra hcon
  have h1 := sigma_dist' hS h
  have h2 := hs (σ f') (σ f) (by
    have : ((f' : ℤ) - f) ≤ W := by omega
    exact h1.trans this)
  rw [abs_le] at h2
  omega

/-- The first index at which a pattern reaches a value. -/
theorem exists_first_reach {M : ℕ} {c : ℤ} (hxs : ∀ i, i < M → |x (i + 1) - x i| ≤ 1)
    (h0 : x 0 < c) (hM : c ≤ x M) :
    ∃ p, p ≤ M ∧ x p = c ∧ ∀ i, i ≤ p → x i ≤ c := by
  classical
  have hex : ∃ p, p ≤ M ∧ x p = c := by
    obtain ⟨j, hj, hj'⟩ := ivt_nat (fun k => x (min k M)) (fun k => by
      by_cases hk : k < M
      · dsimp only; rw [min_eq_left (by omega), min_eq_left (by omega)]; exact hxs k hk
      · dsimp only; rw [min_eq_right (by omega), min_eq_right (by omega)]; simp) M c
      (Or.inl ⟨by simp; omega, by simp; omega⟩)
    exact ⟨min j M, by omega, hj'⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro i hi
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj, hj'⟩ := ivt_nat (fun k => x (min k i)) (fun k => by
      by_cases hk : k < i
      · dsimp only; rw [min_eq_left (by omega), min_eq_left (by omega)]
        exact hxs k (by have := (Nat.find_spec hex).1; omega)
      · dsimp only; rw [min_eq_right (by omega), min_eq_right (by omega)]; simp) i c
      (Or.inl ⟨by simp; omega, by simp; omega⟩)
  have hji : min j i < Nat.find hex := by
    rcases Nat.lt_or_ge (min j i) i with h | h
    · omega
    · exfalso
      have : min j i = i := by omega
      rw [this] at hj'
      omega
  exact Nat.find_min hex hji ⟨by have := (Nat.find_spec hex).1; omega, hj'⟩

/-- **Excursion from the minimum.** If the reading starts and ends at the first value of the
pattern (its minimum) and stays below the last value, the pattern admits a lift from index `0`
back to index `0`. -/
theorem run_exc (hS : Setting σ T) (hs : Slow W τ) {M a b : ℕ} (hW : 4 * (M + 1) + 10 ≤ W)
    (hM : 1 ≤ M) (hab : a ≤ b) (hb : b ≤ T) (hxs : ∀ i, i < M → |x (i + 1) - x i| ≤ 1)
    (hxlo : ∀ i, i ≤ M → x 0 ≤ x i) (hx1 : x 1 = x 0 + 1)
    (hrlo : ∀ f, a ≤ f → f ≤ b → x 0 ≤ τ (σ f)) (hrhi : ∀ f, a ≤ f → f ≤ b → τ (σ f) ≤ x M)
    (ha : τ (σ a) = x 0) (hbv : τ (σ b) = x 0) : Real σ τ W x 0 M a b 0 0 := by
  obtain ⟨t, ht, htmax⟩ := (Finset.Icc a b).exists_max_image (fun f => τ (σ f))
    ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  rw [Finset.mem_Icc] at ht
  simp only [Finset.mem_Icc] at htmax
  set c := τ (σ t) with hc
  rcases eq_or_lt_of_le (show x 0 ≤ c from hrlo t ht.1 ht.2) with hc0 | hc0
  · refine ⟨fun _ => 0, rfl, rfl, fun f _ _ => by simp, fun f hf1 hf2 => ⟨le_rfl, Nat.zero_le _, ?_⟩⟩
    have h1 := hrlo f hf1 hf2
    have h2 := htmax f ⟨hf1, hf2⟩
    exact ⟨σ f, by simp, by simp only; omega⟩
  · have hkey : ∃ p, p ≤ M ∧ x p = c ∧ (∀ i, i ≤ p → x i ≤ c) ∧
        ∀ f f', f ≤ f' → ((τ (σ f) = x 0 ∧ τ (σ f') = c) ∨ (τ (σ f) = c ∧ τ (σ f') = x 0)) →
          p ≤ f' - f := by
      rcases eq_or_lt_of_le (show x 0 + 1 ≤ c by omega) with hc1 | hc1
      · refine ⟨1, hM, by omega, fun i hi => ?_, fun f f' hff' h => ?_⟩
        · rcases Nat.lt_or_ge i 1 with h | h
          · rw [show i = 0 by omega]; omega
          · rw [show i = 1 by omega]; omega
        · have : f ≠ f' := by rintro rfl; omega
          omega
      · obtain ⟨p, hpM, hpc, hple⟩ := exists_first_reach hxs hc0 (hrhi t ht.1 ht.2)
        refine ⟨p, hpM, hpc, hple, fun f f' hff' h => ?_⟩
        have := long_of_gap hS hs hff' (by omega)
        omega
    obtain ⟨p, hpM, hpc, hple, hlen⟩ := hkey
    have hup : Real σ τ W x 0 p a t 0 p :=
      run_up hS hs (by omega) ht.1 (by omega) (fun i hi => hxs i (by omega))
        (fun i hi => hxlo i (by omega)) (fun i hi => by rw [hpc]; exact hple i hi)
        (fun f h1 h2 => hrlo f h1 (by omega))
        (fun f h1 h2 => by rw [hpc]; exact htmax f ⟨h1, by omega⟩) ha hpc.symm
        (hlen a t ht.1 (Or.inl ⟨ha, rfl⟩))
    have hdown : Real σ τ W x 0 p t b p 0 :=
      run_down hS hs (by omega) ht.2 hb (fun i hi => hxs i (by omega))
        (fun i hi => hxlo i (by omega)) (fun i hi => by rw [hpc]; exact hple i hi)
        (fun f h1 h2 => hrlo f (by omega) h2)
        (fun f h1 h2 => by rw [hpc]; exact htmax f ⟨by omega, h2⟩) hpc.symm hbv
        (hlen t b ht.2 (Or.inr ⟨rfl, hbv⟩))
    exact real_widen (real_glue hup hdown ht.1 ht.2) le_rfl hpM

/-- **Excursion from the maximum**, by reflecting and negating `run_exc`. -/
theorem run_exc_top (hS : Setting σ T) (hs : Slow W τ) {M a b : ℕ} (hW : 4 * (M + 1) + 10 ≤ W)
    (hM : 1 ≤ M) (hab : a ≤ b) (hb : b ≤ T) (hxs : ∀ i, i < M → |x (i + 1) - x i| ≤ 1)
    (hxhi : ∀ i, i ≤ M → x i ≤ x M) (hxM1 : x (M - 1) + 1 = x M)
    (hrlo : ∀ f, a ≤ f → f ≤ b → x 0 ≤ τ (σ f)) (hrhi : ∀ f, a ≤ f → f ≤ b → τ (σ f) ≤ x M)
    (ha : τ (σ a) = x M) (hbv : τ (σ b) = x M) : Real σ τ W x 0 M a b M M := by
  have h := run_exc (τ := fun z => -τ z) (x := fun k => -x (0 + M - k)) hS (slow_neg hs) hW hM
    hab hb
    (fun i hi => by
      have := hxs (M - i - 1) (by omega)
      rw [show M - i - 1 + 1 = M - i by omega] at this
      simp only [zero_add]
      rw [show M - (i + 1) = M - i - 1 by omega, abs_sub_comm]
      rw [show -x (M - i) - -x (M - i - 1) = -(x (M - i) - x (M - i - 1)) by ring, abs_neg]
      exact this)
    (fun i hi => by simp only [zero_add, Nat.sub_zero]; have := hxhi (M - i) (by omega); omega)
    (by simp only [zero_add, Nat.sub_zero]; omega)
    (fun f h1 h2 => by simp only [zero_add, Nat.sub_zero]; have := hrhi f h1 h2; omega)
    (fun f h1 h2 => by simp only [zero_add, Nat.sub_self]; have := hrlo f h1 h2; omega)
    (by simp only [zero_add, Nat.sub_zero]; omega) (by simp only [zero_add, Nat.sub_zero]; omega)
  have h2 := real_reflect (p := 0) (q := M) (real_of_neg (x := fun k => x (0 + M - k)) h)
  simpa using h2

/-- **Lifts over runs.** If the coarse reading stays between the first and the last value of the
pattern (its minimum and maximum), and is at one of these two values at both ends of the time
interval, the pattern admits a lift over the interval. -/
theorem run_lift (hS : Setting σ T) (hs : Slow W τ) {M a b : ℕ} (hW : 4 * (M + 1) + 10 ≤ W)
    (hM : 1 ≤ M) (hab : a ≤ b) (hb : b ≤ T) (hxs : ∀ i, i < M → |x (i + 1) - x i| ≤ 1)
    (hxlo : ∀ i, i ≤ M → x 0 ≤ x i) (hxhi : ∀ i, i ≤ M → x i ≤ x M) (hx1 : x 1 = x 0 + 1)
    (hxM1 : x (M - 1) + 1 = x M) (hgap : x 0 + 2 ≤ x M)
    (hrlo : ∀ f, a ≤ f → f ≤ b → x 0 ≤ τ (σ f)) (hrhi : ∀ f, a ≤ f → f ≤ b → τ (σ f) ≤ x M)
    (ha : τ (σ a) = x 0 ∨ τ (σ a) = x M) (hbv : τ (σ b) = x 0 ∨ τ (σ b) = x M) :
    ∃ i j, Real σ τ W x 0 M a b i j := by
  rcases ha with ha | ha <;> rcases hbv with hbv | hbv
  · exact ⟨0, 0, run_exc hS hs hW hM hab hb hxs hxlo hx1 hrlo hrhi ha hbv⟩
  · have := long_of_gap hS hs hab (Or.inl (by omega))
    exact ⟨0, M, run_up hS hs hW hab hb hxs hxlo hxhi hrlo hrhi ha hbv (by omega)⟩
  · have := long_of_gap hS hs hab (Or.inr (by omega))
    exact ⟨M, 0, run_down hS hs hW hab hb hxs hxlo hxhi hrlo hrhi ha hbv (by omega)⟩
  · exact ⟨M, M, run_exc_top hS hs hW hM hab hb hxs hxhi hxM1 hrlo hrhi ha hbv⟩

end HPC.PatCore
