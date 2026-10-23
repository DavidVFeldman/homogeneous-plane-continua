import HPC.PseudoArc.PatCore

/-!
# Pattern following: the main induction

The cases of the induction proving `realize` (see `PatCore.lean` for the setting). The
induction is on the length of the time interval; the pattern is split as in Bing's proof of
Theorem 5 (COMMISSION-batch80.md §3):

* `case_const` — the pattern is constant;
* `case_plateau`, `case_plateau_end` — Bing's (P4): a repeated first (or last) value;
* `case_amp1` — the pattern takes only two adjacent values;
* `case_return` — Bing's (P5): the pattern returns to its minimum; crookedness splits the
  interval in three;
* `case_noreturn` — Bing's (P6): the pattern never returns to its minimum.
-/

namespace HPC.PatCore

variable {σ : ℕ → ℤ} {T B w : ℕ}

/-- The induction hypothesis: lifts exist over all intervals shorter than `n`. -/
def IH (σ : ℕ → ℤ) (T B w n : ℕ) : Prop :=
  ∀ (τ : ℤ → ℤ) (x : ℕ → ℤ) (p q a b e : ℕ), b - a < n → Slow w τ →
    Good σ T B τ x p q a b e → Real σ τ w x p q a b p q

section Cases

variable {τ : ℤ → ℤ} {x : ℕ → ℤ} {p q a b e : ℕ}

theorem Good.e_le (hG : Good σ T B τ x p q a b e) (hBw : 2 * B + 10 ≤ w) : e ≤ w := by
  have := hG.budget; omega

theorem Good.ell_a (hG : Good σ T B τ x p q a b e) (hBw : 2 * B + 10 ≤ w) (hs : Slow w τ) :
    τ (σ a) ≤ x p + 1 := by
  have := al_near hs (hG.e_le hBw) hG.anca
  rw [abs_le] at this; linarith

theorem Good.ell_b (hG : Good σ T B τ x p q a b e) (hBw : 2 * B + 10 ≤ w) (hs : Slow w τ) :
    x q - 1 ≤ τ (σ b) := by
  have := al_near hs (hG.e_le hBw) hG.ancb
  rw [abs_le] at this; linarith

theorem ell_lip (hS : Setting σ T) (hw : 1 ≤ w) (hs : Slow w τ) (f : ℕ) :
    |τ (σ (f + 1)) - τ (σ f)| ≤ 1 :=
  hs _ _ ((hS.lip f).trans (by exact_mod_cast hw))

/-- Constant pattern: the ramp. -/
theorem case_const (hG : Good σ T B τ x p q a b e) (heq : x q = x p) :
    Real σ τ w x p q a b p q := by
  refine real_ramp hG.pq hG.len (fun f hf1 hf2 i hi1 hi2 => ?_)
  have : x i = τ (σ f) := by
    linarith [hG.xlo i hi1 hi2, hG.xhi i hi1 hi2, hG.rlo f hf1 hf2, hG.rhi f hf1 hf2]
  rw [this]
  exact al_mono (Nat.zero_le _) (al_canon τ f)

/-- Bing's (P4): the first value is repeated. -/
theorem case_plateau (hS : Setting σ T) (hBw : 2 * B + 10 ≤ w) (hs : Slow w τ)
    (hG : Good σ T B τ x p q a b e) (ih : IH σ T B w (b - a)) (hne : x q ≠ x p)
    (h1 : x (p + 1) = x p) : Real σ τ w x p q a b p q := by
  have hpq : p < q := by
    rcases Nat.lt_or_ge p q with h | h
    · exact h
    · exact absurd (by rw [show q = p by have := hG.pq; omega]) hne
  have hlen := hG.len
  have hab : a + 1 ≤ b := by omega
  have hA1 : Al σ τ (e + 1) (a + 1) (x p) :=
    al_move hS 1 (by push_cast; simp) hG.anca
  have hG' : Good σ T B τ x (p + 1) q (a + 1) b (e + 1) :=
    { pq := hpq
      ab := hab
      bT := hG.bT
      len := by omega
      xstep := fun i h1 h2 => hG.xstep i (by omega) h2
      xlo := fun i h1' h2 => by rw [h1]; exact hG.xlo i (by omega) h2
      xhi := fun i h1 h2 => hG.xhi i (by omega) h2
      rlo := fun f h1' h2 => by rw [h1]; exact hG.rlo f (by omega) h2
      rhi := fun f h1 h2 => hG.rhi f (by omega) h2
      anca := by rw [h1]; exact hA1
      ancb := al_mono (by omega) hG.ancb
      budget := by have := hG.budget; omega }
  have hR := ih τ x (p + 1) q (a + 1) b (e + 1) (by omega) hs hG'
  have hstep : Real σ τ w x p q a (a + 1) p (p + 1) :=
    real_step le_rfl (by omega) (al_mono (hG.e_le hBw) hG.anca)
      (by rw [h1]; exact al_mono (by have := hG.budget; omega) hA1)
  exact real_glue hstep (real_widen hR (by omega) le_rfl) (by omega) hab

/-- Bing's (P4) at the other end: the last value is repeated. -/
theorem case_plateau_end (hS : Setting σ T) (hBw : 2 * B + 10 ≤ w) (hs : Slow w τ)
    (hG : Good σ T B τ x p q a b e) (ih : IH σ T B w (b - a)) (hne : x q ≠ x p)
    (h1 : x (q - 1) = x q) : Real σ τ w x p q a b p q := by
  have hpq : p < q := by
    rcases Nat.lt_or_ge p q with h | h
    · exact h
    · exact absurd (by rw [show q = p by have := hG.pq; omega]) hne
  have hlen := hG.len
  have hab : a + 1 ≤ b := by omega
  have hA1 : Al σ τ (e + 1) (b - 1) (x q) :=
    al_move hS 1 (by rw [Nat.cast_sub (by omega)]; push_cast; simp) hG.ancb
  have hG' : Good σ T B τ x p (q - 1) a (b - 1) (e + 1) :=
    { pq := by omega
      ab := by omega
      bT := by have := hG.bT; omega
      len := by omega
      xstep := fun i h1 h2 => hG.xstep i h1 (by omega)
      xlo := fun i h1 h2 => hG.xlo i h1 (by omega)
      xhi := fun i h1' h2 => by rw [h1]; exact hG.xhi i h1' (by omega)
      rlo := fun f h1 h2 => hG.rlo f h1 (by omega)
      rhi := fun f h1' h2 => by rw [h1]; exact hG.rhi f h1' (by omega)
      anca := al_mono (by omega) hG.anca
      ancb := by rw [h1]; exact hA1
      budget := by have := hG.budget; omega }
  have hR := ih τ x p (q - 1) a (b - 1) (e + 1) (by omega) hs hG'
  have hstep : Real σ τ w x p q (b - 1) b (q - 1) q := by
    have := real_step (σ := σ) (τ := τ) (w := w) (x := x) (p := p) (q := q) (a := b - 1)
      (i := q - 1) (by omega) (by omega)
      (by rw [h1]; exact al_mono (by have := hG.budget; omega) hA1)
      (by rw [show q - 1 + 1 = q by omega, show b - 1 + 1 = b by omega]
          exact al_mono (hG.e_le hBw) hG.ancb)
    rwa [show q - 1 + 1 = q by omega, show b - 1 + 1 = b by omega] at this
  exact real_glue (real_widen hR le_rfl (by omega)) hstep (by omega) (by omega)

/-- A time near which both values of a two-valued pattern are allowed. -/
theorem amp1_both (hS : Setting σ T) (hBw : 2 * B + 10 ≤ w)
    (hG : Good σ T B τ x p q a b e) (hamp : x q = x p + 1) :
    ∃ f0, a ≤ f0 ∧ f0 ≤ b ∧ Al σ τ (e + 1) f0 (x p) ∧ Al σ τ (e + 1) f0 (x q) := by
  classical
  have hw1 : 1 ≤ w := by omega
  by_cases ha : τ (σ a) = x q
  · exact ⟨a, le_rfl, hG.ab, al_mono (by omega) hG.anca,
      ha ▸ al_mono (Nat.zero_le _) (al_canon τ a)⟩
  by_cases hb : τ (σ b) = x p
  · exact ⟨b, hG.ab, le_rfl, hb ▸ al_mono (Nat.zero_le _) (al_canon τ b),
      al_mono (by omega) hG.ancb⟩
  have hla : τ (σ a) = x p := by
    have := hG.rlo a le_rfl hG.ab; have := hG.rhi a le_rfl hG.ab; omega
  have hlb : τ (σ b) = x q := by
    have := hG.rlo b hG.ab le_rfl; have := hG.rhi b hG.ab le_rfl; omega
  have hex : ∃ f, a ≤ f ∧ τ (σ f) = x q := ⟨b, hG.ab, hlb⟩
  set f1 := Nat.find hex with hf1
  have hspec := Nat.find_spec hex
  have hf1b : f1 ≤ b := Nat.find_min' hex ⟨hG.ab, hlb⟩
  have hf1a : a < f1 := by
    rcases Nat.lt_or_ge a f1 with h | h
    · exact h
    · have : f1 = a := le_antisymm h hspec.1
      rw [← hf1, this] at hspec; exact absurd hspec.2 ha
  have hprev : τ (σ (f1 - 1)) = x p := by
    have hmin := Nat.find_min hex (show f1 - 1 < f1 by omega)
    have h1 : ¬ τ (σ (f1 - 1)) = x q := fun h => hmin ⟨by omega, h⟩
    have := hG.rlo (f1 - 1) (by omega) (by omega)
    have := hG.rhi (f1 - 1) (by omega) (by omega)
    omega
  refine ⟨f1 - 1, by omega, by omega, hprev ▸ al_mono (Nat.zero_le _) (al_canon τ _), ?_⟩
  have := al_move hS (d := 0) (f := f1) (f' := f1 - 1) 1
    (by rw [Nat.cast_sub (by omega)]; push_cast; simp) (hspec.2 ▸ al_canon τ f1)
  exact al_mono (by omega) this

/-- The pattern takes the two values `x p` and `x p + 1`, with no repeated first or last
value: follow the canonical reading, switching from the first pair of indices to the last pair
inside a window where both values are allowed. -/
theorem case_amp1 (hS : Setting σ T) (hBw : 2 * B + 10 ≤ w)
    (hG : Good σ T B τ x p q a b e) (hamp : x q = x p + 1)
    (h1 : x (p + 1) ≠ x p) (h2 : x (q - 1) ≠ x q) : Real σ τ w x p q a b p q := by
  classical
  have hpq : p < q := by
    rcases Nat.lt_or_ge p q with h | h
    · exact h
    · have : q = p := by have := hG.pq; omega
      rw [this] at hamp; omega
  have hlen := hG.len
  have hbud := hG.budget
  have hval : ∀ i, p ≤ i → i ≤ q → x i = x p ∨ x i = x q := by
    intro i hi1 hi2; have := hG.xlo i hi1 hi2; have := hG.xhi i hi1 hi2; omega
  have hx1 : x (p + 1) = x q := by
    rcases hval (p + 1) (by omega) (by omega) with h | h
    · exact absurd h h1
    · exact h
  have hxq1 : x (q - 1) = x p := by
    rcases hval (q - 1) (by omega) (by omega) with h | h
    · exact h
    · exact absurd h h2
  have hell : ∀ f, a ≤ f → f ≤ b → τ (σ f) = x p ∨ τ (σ f) = x q := by
    intro f hf1 hf2; have := hG.rlo f hf1 hf2; have := hG.rhi f hf1 hf2; omega
  -- short intervals: both values are allowed everywhere
  by_cases hshort : b - a + e ≤ w
  · refine real_ramp hG.pq hlen (fun f hf1 hf2 i hi1 hi2 => ?_)
    rcases hval i hi1 hi2 with h | h <;> rw [h]
    · have := al_move hS (f := a) (f' := f) (f - a) (natdist_le (by omega) (by omega)) hG.anca
      exact al_mono (by omega) this
    · have := al_move hS (f := b) (f' := f) (b - f) (natdist_le (by omega) (by omega)) hG.ancb
      exact al_mono (by omega) this
  push_neg at hshort
  obtain ⟨f0, hf0a, hf0b, hA0, hA0'⟩ := amp1_both hS hBw hG hamp
  set W := q - p with hW
  set u := max (a + 1) (min f0 (b - 1 - W)) with hu
  have hua : a + 1 ≤ u := le_max_left _ _
  have hub : u + W + 1 ≤ b := by omega
  have hnear : ∀ f, u ≤ f → f ≤ u + W → |(f : ℤ) - f0| ≤ (W + 1 : ℕ) := by
    intro f hf1 hf2
    rw [abs_le]; push_cast; constructor <;> omega
  have hboth : ∀ f, u ≤ f → f ≤ u + W → ∀ i, p ≤ i → i ≤ q → Al σ τ w f (x i) := by
    intro f hf1 hf2 i hi1 hi2
    rcases hval i hi1 hi2 with h | h <;> rw [h]
    · exact al_mono (by omega) (al_move hS (W + 1) (hnear f hf1 hf2) hA0)
    · exact al_mono (by omega) (al_move hS (W + 1) (hnear f hf1 hf2) hA0')
  set tog : ℕ → ℕ := fun f => if τ (σ f) = x q then 1 else 0 with htog
  have htog1 : ∀ f, tog f ≤ 1 := fun f => by simp only [htog]; split_ifs <;> omega
  set φ : ℕ → ℕ := fun f =>
    if f ≤ a then p else if f < u then p + tog f
    else if f < u + W then min (p + 1 + (f - u)) (q - 1)
    else if f < b then q - 1 + tog f else q with hφ
  refine ⟨φ, by simp [hφ], ?_, ?_, ?_⟩
  · simp only [hφ]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · intro f hf1 hf2
    have t1 := htog1 f
    have t2 := htog1 (f + 1)
    simp only [hφ]
    constructor <;> split_ifs <;> omega
  · intro f hf1 hf2
    -- allowedness of the canonical toggle
    have htogA : ∀ i, (x i = x p ∧ x (i + 1) = x q) → Al σ τ w f (x (i + tog f)) := by
      rintro i ⟨hi, hi'⟩
      simp only [htog]
      split_ifs with hq
      · rw [hi', ← hq]; exact al_mono (Nat.zero_le _) (al_canon τ f)
      · have : τ (σ f) = x p := by
          rcases hell f hf1 hf2 with h | h
          · exact h
          · exact absurd h hq
        rw [add_zero, hi, ← this]; exact al_mono (Nat.zero_le _) (al_canon τ f)
    have t1 := htog1 f
    simp only [hφ]
    split_ifs with c1 c2 c3 c4
    · have : f = a := by omega
      subst this; exact ⟨le_rfl, by omega, al_mono (hG.e_le hBw) hG.anca⟩
    · exact ⟨by omega, by omega, htogA p ⟨rfl, hx1⟩⟩
    · exact ⟨by omega, by omega, hboth f (by omega) (by omega) _ (by omega) (by omega)⟩
    · refine ⟨by omega, by omega, ?_⟩
      exact htogA (q - 1) ⟨hxq1, by rw [show q - 1 + 1 = q by omega]⟩
    · have : f = b := by omega
      subst this; exact ⟨by omega, le_rfl, al_mono (hG.e_le hBw) hG.ancb⟩

/-- Bing's (P5): the pattern returns to its minimum. Crookedness, applied between the start
of the interval and the first time above the peak of the pattern before its return, splits the
interval into an ascent, a descent and the rest. -/
theorem case_return (hS : Setting σ T) (hBw : 2 * B + 10 ≤ w) (hs : Slow w τ)
    (hG : Good σ T B τ x p q a b e) (ih : IH σ T B w (b - a)) (hA2 : x p + 2 ≤ x q)
    (hx1 : x (p + 1) = x p + 1) (hret : ∃ i, p < i ∧ i ≤ q ∧ x i = x p) :
    Real σ τ w x p q a b p q := by
  classical
  have hw1 : 1 ≤ w := by omega
  have hlen := hG.len
  have hbud := hG.budget
  have hew := hG.e_le hBw
  have hpq : p + 2 ≤ q := by
    rcases (show q = p ∨ q = p + 1 ∨ p + 2 ≤ q by have := hG.pq; omega) with h | h | h
    · rw [h] at hA2; omega
    · have h1 := hG.xstep p le_rfl (by omega)
      rw [← h, abs_le] at h1; omega
    · exact h
  -- the first return and the peak before it
  set ir := Nat.find hret with hir_def
  have hir := Nat.find_spec hret
  have hir2 : p + 2 ≤ ir := by
    rcases (show ir = p + 1 ∨ p + 2 ≤ ir by omega) with h | h
    · have := hir.2.2; rw [← hir_def, h, hx1] at this; omega
    · exact h
  obtain ⟨ic, hic_mem, hic_max⟩ := Finset.exists_max_image (Finset.Icc p ir) x
    ⟨p, by simp; omega⟩
  rw [Finset.mem_Icc] at hic_mem
  have hmax : ∀ i, p ≤ i → i ≤ ir → x i ≤ x ic := fun i h1 h2 =>
    hic_max i (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  set c := x ic with hc
  have hc1 : x p + 1 ≤ c := by rw [← hx1]; exact hmax (p + 1) (by omega) (by omega)
  have hxir : x ir = x p := hir.2.2
  have hicp : p < ic := by
    rcases Nat.lt_or_ge p ic with h | h
    · exact h
    · have : ic = p := by omega
      rw [this] at hc; omega
  have hicr : ic < ir := by
    rcases Nat.lt_or_ge ic ir with h | h
    · exact h
    · have : ic = ir := by omega
      rw [this, hxir] at hc; omega
  have hirq : ir ≤ q := hir.2.1
  -- the first time above the peak (or the end)
  have hex : ∃ f, a ≤ f ∧ (c + 1 ≤ τ (σ f) ∨ f = b) := ⟨b, hG.ab, Or.inr rfl⟩
  set fs := Nat.find hex with hfs_def
  have hfs := Nat.find_spec hex
  have hfsb : fs ≤ b := Nat.find_min' hex ⟨hG.ab, Or.inr rfl⟩
  have hbelow : ∀ f, a ≤ f → f < fs → τ (σ f) ≤ c := by
    intro f h1 h2
    have := Nat.find_min hex h2
    push_neg at this
    have := this h1
    omega
  have hla := hG.ell_a hBw hs
  have hfsa : a < fs := by
    rcases Nat.lt_or_ge a fs with h | h
    · exact h
    · have h' : fs = a := le_antisymm h hfs.1
      rcases hfs.2 with h2 | h2
      · rw [← hfs_def, h'] at h2; omega
      · rw [← hfs_def, h'] at h2; omega
  obtain ⟨v, hv2, hcv, hAv⟩ : ∃ v, x p + 2 ≤ v ∧ c ≤ v ∧ Al σ τ e fs v := by
    by_cases h : c + 1 ≤ τ (σ fs)
    · have h1 := hbelow (fs - 1) (by omega) (by omega)
      have h2 := ell_lip hS hw1 hs (fs - 1)
      rw [show fs - 1 + 1 = fs by omega, abs_le] at h2
      refine ⟨c + 1, by omega, by omega, ?_⟩
      have : τ (σ fs) = c + 1 := by omega
      rw [← this]; exact al_mono (Nat.zero_le _) (al_canon τ fs)
    · have h' : fs = b := by rcases hfs.2 with h2 | h2 <;> [exact absurd h2 h; exact h2]
      refine ⟨x q, hA2, hG.xhi ic (by omega) (by omega), ?_⟩
      rw [h']; exact hG.ancb
  -- crookedness between `a` and `fs`
  have hBw' : (2 * B + 10 : ℤ) ≤ w := by exact_mod_cast hBw
  have hbud' : (e : ℤ) + 2 * ((q - p : ℕ) : ℤ) ≤ B := by exact_mod_cast hbud
  have hfar : (w : ℤ) + 1 - e - e ≤ |σ a - σ fs| :=
    al_far hs hG.anca hAv (two_le_abs (Or.inl hv2))
  obtain ⟨r, s, har, hrs, hsfs, hr, hsd⟩ :=
    hS.crook a fs hfsa (hfsb.trans hG.bT) (by linarith)
  have hAr : Al σ τ (e + 2) r c := by
    obtain ⟨pv, hpv, hpv'⟩ := hAv
    obtain ⟨p'', hp'', hp''v⟩ := ivt_between hw1 hs (σ r) pv c
      (Or.inl ⟨hbelow r (by omega) (by omega), by rw [hpv']; exact hcv⟩)
    refine ⟨p'', ?_, hp''v⟩
    have := tri_up hpv (by rw [abs_sub_comm]; exact hr : |σ fs - σ r| ≤ 2)
    push_cast; linarith
  have hAs : Al σ τ (e + 2) s (x p) := by
    obtain ⟨pv, hpv, hpv'⟩ := hG.anca
    refine ⟨pv, ?_, hpv'⟩
    have := tri_up hpv (by rw [abs_sub_comm]; exact hsd : |σ a - σ s| ≤ 2)
    push_cast; linarith
  have hfar2 : (w : ℤ) + 1 - (e + 2 : ℕ) - e ≤ |σ s - σ b| :=
    al_far hs hAs hG.ancb (two_le_abs (Or.inl hA2))
  -- lengths of the three pieces
  have hdar := tri_lo hfar (by rw [abs_sub_comm]; exact hr : |σ fs - σ r| ≤ 2)
  have hdrs' : (w : ℤ) + 1 - e - e - 2 - 2 ≤ |σ r - σ s| := by
    rw [abs_sub_comm] at hdar
    have hsd' : |σ a - σ s| ≤ 2 := by rw [abs_sub_comm]; exact hsd
    have := tri_lo hdar hsd'
    rw [abs_sub_comm] at hdar
    linarith
  have tar := time_ge hS har.le hdar
  have trs := time_ge hS hrs.le hdrs'
  have tsb := time_ge hS (show s ≤ b by omega) hfar2
  push_cast at tsb
  have hL1 : q - p ≤ r - a := by
    have : ((q - p : ℕ) : ℤ) ≤ (r : ℤ) - a := by linarith
    omega
  have hL2 : q - p ≤ s - r := by
    have : ((q - p : ℕ) : ℤ) ≤ (s : ℤ) - r := by linarith
    omega
  have hL3 : q - p ≤ b - s := by
    have : ((q - p : ℕ) : ℤ) ≤ (b : ℤ) - s := by linarith
    omega
  have G1 : Good σ T B τ x p ic a r (e + 2) :=
    { pq := hicp.le
      ab := har.le
      bT := by have := hG.bT; omega
      len := by omega
      xstep := fun i h1 h2 => hG.xstep i h1 (by omega)
      xlo := fun i h1 h2 => hG.xlo i h1 (by omega)
      xhi := fun i h1 h2 => hmax i h1 (by omega)
      rlo := fun f h1 h2 => hG.rlo f h1 (by omega)
      rhi := fun f h1 h2 => hbelow f h1 (by omega)
      anca := al_mono (by omega) hG.anca
      ancb := hAr
      budget := by omega }
  have G2 : Good σ T B (fun z => -τ z) (fun k => -x k) ic ir r s (e + 2) :=
    { pq := hicr.le
      ab := hrs.le
      bT := by have := hG.bT; omega
      len := by omega
      xstep := fun i h1 h2 => by
        have := hG.xstep i (by omega) (by omega)
        rwa [show -x (i + 1) - -x i = -(x (i + 1) - x i) by ring, abs_neg]
      xlo := fun i h1 h2 => by have := hmax i (by omega) h2; linarith
      xhi := fun i h1 h2 => by have := hG.xlo i (by omega) (by omega); linarith
      rlo := fun f h1 h2 => by have := hbelow f (by omega) (by omega); linarith
      rhi := fun f h1 h2 => by have := hG.rlo f (by omega) (by omega); linarith
      anca := al_neg_iff.mpr hAr
      ancb := by
        show Al σ (fun z => -τ z) (e + 2) s (-x ir)
        rw [hxir]; exact al_neg_iff.mpr hAs
      budget := by omega }
  have G3 : Good σ T B τ x ir q s b (e + 2) :=
    { pq := hirq
      ab := by omega
      bT := hG.bT
      len := by omega
      xstep := fun i h1 h2 => hG.xstep i (by omega) h2
      xlo := fun i h1 h2 => by rw [hxir]; exact hG.xlo i (by omega) h2
      xhi := fun i h1 h2 => hG.xhi i (by omega) h2
      rlo := fun f h1 h2 => by rw [hxir]; exact hG.rlo f (by omega) h2
      rhi := fun f h1 h2 => hG.rhi f (by omega) h2
      anca := by rw [hxir]; exact hAs
      ancb := al_mono (by omega) hG.ancb
      budget := by omega }
  have R1 := ih τ x p ic a r (e + 2) (by omega) hs G1
  have R2 := real_of_neg (ih _ _ ic ir r s (e + 2) (by omega) (slow_neg hs) G2)
  have R3 := ih τ x ir q s b (e + 2) (by omega) hs G3
  exact real_glue (real_glue (real_widen R1 le_rfl (by omega))
    (real_widen R2 (by omega) (by omega)) har.le hrs.le) (real_widen R3 (by omega) le_rfl)
    (by omega) (by omega)

/-- Bing's (P6): the pattern never returns to its minimum. After the last time at the minimum
the rest of the pattern is lifted; before it, the excursions are lifted by splitting at their
highest time. -/
theorem case_noreturn (hS : Setting σ T) (hBw : 2 * B + 10 ≤ w) (hs : Slow w τ)
    (hG : Good σ T B τ x p q a b e) (ih : IH σ T B w (b - a)) (hA2 : x p + 2 ≤ x q)
    (hx1 : x (p + 1) = x p + 1) (hnoret : ∀ i, p < i → i ≤ q → x i ≠ x p) :
    Real σ τ w x p q a b p q := by
  classical
  have hw1 : 1 ≤ w := by omega
  have hlen := hG.len
  have hbud := hG.budget
  have hew := hG.e_le hBw
  have hBw' : (2 * B + 10 : ℤ) ≤ w := by exact_mod_cast hBw
  have hbud' : (e : ℤ) + 2 * ((q - p : ℕ) : ℤ) ≤ B := by exact_mod_cast hbud
  have hpq : p + 2 ≤ q := by
    rcases (show q = p ∨ q = p + 1 ∨ p + 2 ≤ q by have := hG.pq; omega) with h | h | h
    · rw [h] at hA2; omega
    · have h1 := hG.xstep p le_rfl (by omega)
      rw [← h, abs_le] at h1; omega
    · exact h
  have hxgt : ∀ i, p < i → i ≤ q → x p + 1 ≤ x i := fun i h1 h2 => by
    have := hG.xlo i h1.le h2; have := hnoret i h1 h2; omega
  -- the last time at the minimum
  let P : ℕ → Prop := fun f => a ≤ f ∧ (f = a ∨ τ (σ f) = x p)
  have hPa : P a := ⟨le_rfl, Or.inl rfl⟩
  set g := Nat.findGreatest P b with hg_def
  have hgP : P g := Nat.findGreatest_spec hG.ab hPa
  have hgb : g ≤ b := Nat.findGreatest_le b
  have hafter : ∀ f, g < f → f ≤ b → x p + 1 ≤ τ (σ f) := by
    intro f h1 h2
    have hnot := Nat.findGreatest_is_greatest h1 h2
    have hga : a ≤ g := hgP.1
    have hr := hG.rlo f (by omega) h2
    by_contra hc
    exact hnot ⟨by omega, Or.inr (by omega)⟩
  have hAg : Al σ τ e g (x p) := by
    rcases hgP.2 with h | h
    · rw [h]; exact hG.anca
    · rw [← h]; exact al_mono (Nat.zero_le _) (al_canon τ g)
  have hfarg : (w : ℤ) + 1 - e - e ≤ |σ g - σ b| :=
    al_far hs hAg hG.ancb (two_le_abs (Or.inl hA2))
  have tgb := time_ge hS hgb hfarg
  have hgb' : g < b := by omega
  -- the anchor after the last visit
  have hAg1 : Al σ τ (e + 1) (g + 1) (x (p + 1)) := by
    rw [hx1]
    by_cases hl : τ (σ g) = x p
    · have h1 := hafter (g + 1) (by omega) (by omega)
      have h2 := ell_lip hS hw1 hs g
      rw [abs_le] at h2
      have : τ (σ (g + 1)) = x p + 1 := by omega
      rw [← this]; exact al_mono (Nat.zero_le _) (al_canon τ _)
    · have hga : g = a := by
        rcases hgP.2 with h | h
        · exact h
        · exact absurd h hl
      have hla := hG.ell_a hBw hs
      have hra := hG.rlo a le_rfl hG.ab
      have hv : τ (σ g) = x p + 1 := by rw [hga] at hl ⊢; omega
      have h0 : Al σ τ 0 g (x p + 1) := by rw [← hv]; exact al_canon τ g
      have := al_move hS (f := g) (f' := g + 1) 1 (natdist_le (by omega) (by omega)) h0
      exact al_mono (by omega) this
  -- the rest of the pattern after the last visit
  have hLt : q - (p + 1) ≤ b - (g + 1) := by
    have : ((q - p : ℕ) : ℤ) ≤ (b : ℤ) - g := by linarith
    omega
  have Gt : Good σ T B τ x (p + 1) q (g + 1) b (e + 1) :=
    { pq := by omega
      ab := by omega
      bT := hG.bT
      len := hLt
      xstep := fun i h1 h2 => hG.xstep i (by omega) h2
      xlo := fun i h1 h2 => by rw [hx1]; exact hxgt i (by omega) h2
      xhi := fun i h1 h2 => hG.xhi i (by omega) h2
      rlo := fun f h1 h2 => by rw [hx1]; exact hafter f (by omega) h2
      rhi := fun f h1 h2 => hG.rhi f (by omega) h2
      anca := hAg1
      ancb := al_mono (by omega) hG.ancb
      budget := by omega }
  have Rt := ih τ x (p + 1) q (g + 1) b (e + 1) (by have := hgP.1; omega) hs Gt
  have Rs : Real σ τ w x p q g (g + 1) p (p + 1) :=
    real_step le_rfl (by omega) (al_mono hew hAg) (al_mono (by omega) hAg1)
  -- the excursions before the last visit
  have Re : Real σ τ w x p q a g p p := by
    rcases eq_or_lt_of_le hgP.1 with hga | hga
    · rw [← hga]; exact real_point le_rfl hG.pq (al_mono hew hG.anca)
    have hlg : τ (σ g) = x p := by
      rcases hgP.2 with h | h
      · omega
      · exact h
    obtain ⟨pk, hpk_mem, hpk_max⟩ := Finset.exists_max_image (Finset.Icc a g)
      (fun f => τ (σ f)) ⟨a, by simp; omega⟩
    rw [Finset.mem_Icc] at hpk_mem
    have hmaxE : ∀ f, a ≤ f → f ≤ g → τ (σ f) ≤ τ (σ pk) := fun f h1 h2 =>
      hpk_max f (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    by_cases hE : τ (σ pk) ≤ x p + 1
    · -- the excursions stay within one of the minimum: follow the canonical reading
      refine ⟨fun f => if f = a ∨ f = g then p else if τ (σ f) = x p + 1 then p + 1 else p,
        by simp, by simp, ?_, ?_⟩
      · intro f h1 h2
        dsimp only
        constructor <;> split_ifs <;> omega
      · intro f h1 h2
        dsimp only
        have hE' := hmaxE f h1 h2
        have hr := hG.rlo f h1 (by omega)
        split_ifs with c1 c2
        · refine ⟨le_rfl, by omega, ?_⟩
          rcases c1 with h | h
          · rw [h]; exact al_mono hew hG.anca
          · rw [h, ← hlg]; exact al_mono (Nat.zero_le _) (al_canon τ g)
        · refine ⟨by omega, by omega, ?_⟩
          rw [hx1, ← c2]; exact al_mono (Nat.zero_le _) (al_canon τ f)
        · refine ⟨le_rfl, by omega, ?_⟩
          have : τ (σ f) = x p := by omega
          rw [← this]; exact al_mono (Nat.zero_le _) (al_canon τ f)
    push_neg at hE
    set E := τ (σ pk) with hE_def
    have hEq : E ≤ x q := hG.rhi pk hpk_mem.1 (by omega)
    -- the first index of the pattern at the peak value
    have hstepc : ∀ (i : ℕ), i ≤ q - p → ∀ k : ℕ,
        |x (p + min (k + 1) i) - x (p + min k i)| ≤ 1 := by
      intro i hi k
      rcases Nat.lt_or_ge k i with h | h
      · rw [min_eq_left (show k + 1 ≤ i by omega), min_eq_left h.le]
        have := hG.xstep (p + k) (by omega) (by omega)
        rwa [show p + (k + 1) = p + k + 1 by omega]
      · rw [min_eq_right (show i ≤ k + 1 by omega), min_eq_right h]; simp
    have hexi : ∃ i, p ≤ i ∧ i ≤ q ∧ x i = E := by
      obtain ⟨j, hj, hj'⟩ := ivt_nat (fun k => x (p + min k (q - p))) (hstepc (q - p) le_rfl)
        (q - p) E (Or.inl ⟨by simp; linarith [hG.rlo pk hpk_mem.1 (by omega)], by
          simp only [min_self]; rw [show p + (q - p) = q by omega]; exact hEq⟩)
      exact ⟨p + min j (q - p), by omega, by omega, hj'⟩
    set ie := Nat.find hexi with hie_def
    have hie := Nat.find_spec hexi
    have hxie : x ie = E := hie.2.2
    have hieq : ie ≤ q := hie.2.1
    have hbelowE : ∀ i, p ≤ i → i ≤ ie → x i ≤ E := by
      intro i h1 h2
      by_contra hc
      push_neg at hc
      obtain ⟨j, hj, hj'⟩ := ivt_nat (fun k => x (p + min k (i - p)))
        (hstepc (i - p) (by omega)) (i - p) E (Or.inl ⟨by simp; linarith, by
          simp only [min_self]; rw [show p + (i - p) = i by omega]; exact hc.le⟩)
      have hmin := Nat.find_min' hexi (m := p + min j (i - p)) ⟨by omega, by omega, hj'⟩
      have : p + min j (i - p) = i := by omega
      rw [this] at hj'
      linarith
    have hiep : p < ie := by
      rcases Nat.lt_or_ge p ie with h | h
      · exact h
      · have : ie = p := by have := hie.1; omega
        rw [this] at hxie; linarith
    -- the ascent to the peak
    have hfu : (w : ℤ) + 1 - e - (0 : ℕ) ≤ |σ a - σ pk| :=
      al_far hs hG.anca (al_canon τ pk) (two_le_abs (Or.inl (by omega)))
    have tu := time_ge hS hpk_mem.1 hfu
    push_cast at tu
    have hfd : (w : ℤ) + 1 - (0 : ℕ) - (0 : ℕ) ≤ |σ pk - σ g| :=
      al_far hs (al_canon τ pk) (by rw [← hlg] at *; exact al_canon τ g)
        (two_le_abs (Or.inr (by rw [hlg]; omega)))
    have td := time_ge hS hpk_mem.2 hfd
    push_cast at td
    have Gu : Good σ T B τ x p ie a pk e :=
      { pq := hiep.le
        ab := hpk_mem.1
        bT := by have := hG.bT; omega
        len := by
          have : ((q - p : ℕ) : ℤ) ≤ (pk : ℤ) - a := by linarith
          omega
        xstep := fun i h1 h2 => hG.xstep i h1 (by omega)
        xlo := fun i h1 h2 => hG.xlo i h1 (by omega)
        xhi := fun i h1 h2 => by rw [hxie]; exact hbelowE i h1 h2
        rlo := fun f h1 h2 => hG.rlo f h1 (by omega)
        rhi := fun f h1 h2 => by rw [hxie]; exact hmaxE f h1 (by omega)
        anca := hG.anca
        ancb := by rw [hxie]; exact al_mono (Nat.zero_le _) (al_canon τ pk)
        budget := by omega }
    have Ru := ih τ x p ie a pk e (by omega) hs Gu
    -- the descent from the peak: reflect the pattern and negate the readings
    have Gd : Good σ T B (fun z => -τ z) (fun k => -x (p + ie - k)) p ie pk g 0 :=
      { pq := hiep.le
        ab := hpk_mem.2
        bT := by have := hG.bT; omega
        len := by
          have : ((q - p : ℕ) : ℤ) ≤ (g : ℤ) - pk := by linarith
          omega
        xstep := fun i h1 h2 => by
          have := hG.xstep (p + ie - (i + 1)) (by omega) (by omega)
          rw [show p + ie - (i + 1) + 1 = p + ie - i by omega] at this
          rw [show -x (p + ie - (i + 1)) - -x (p + ie - i) =
            x (p + ie - i) - x (p + ie - (i + 1)) by ring]
          exact this
        xlo := fun i h1 h2 => by
          have := hbelowE (p + ie - i) (by omega) (by omega)
          rw [show p + ie - p = ie by omega, hxie]; linarith
        xhi := fun i h1 h2 => by
          have := hG.xlo (p + ie - i) (by omega) (by omega)
          rw [show p + ie - ie = p by omega]; linarith
        rlo := fun f h1 h2 => by
          have := hmaxE f (by omega) h2
          rw [show p + ie - p = ie by omega, hxie]; linarith
        rhi := fun f h1 h2 => by
          have := hG.rlo f (by omega) (by omega)
          rw [show p + ie - ie = p by omega]; linarith
        anca := by
          show Al σ (fun z => -τ z) 0 pk (-x (p + ie - p))
          rw [show p + ie - p = ie by omega, hxie]
          exact al_neg_iff.mpr (al_canon τ pk)
        ancb := by
          show Al σ (fun z => -τ z) 0 g (-x (p + ie - ie))
          rw [show p + ie - ie = p by omega, ← hlg]
          exact al_neg_iff.mpr (al_canon τ g)
        budget := by omega }
    have Rd0 := ih _ _ p ie pk g 0 (by omega) (slow_neg hs) Gd
    have Rd := real_reflect (real_of_neg (x := fun k => x (p + ie - k)) Rd0)
    rw [show p + ie - p = ie by omega, show p + ie - ie = p by omega] at Rd
    exact real_glue (real_widen Ru le_rfl hieq) (real_widen Rd le_rfl hieq) hpk_mem.1 hpk_mem.2
  exact real_glue (real_glue Re Rs hgP.1 (by omega)) (real_widen Rt (by omega) le_rfl)
    (by omega) (by omega)


/-! ## The induction -/

theorem main_step (hS : Setting σ T) (hBw : 2 * B + 10 ≤ w) (n : ℕ) (ih : IH σ T B w n)
    (τ : ℤ → ℤ) (x : ℕ → ℤ) (p q a b e : ℕ) (hn : b - a = n) (hs : Slow w τ)
    (hG : Good σ T B τ x p q a b e) : Real σ τ w x p q a b p q := by
  subst hn
  by_cases h0 : x q = x p
  · exact case_const hG h0
  by_cases h1 : x (p + 1) = x p
  · exact case_plateau hS hBw hs hG ih h0 h1
  have hpq : p < q := by
    rcases Nat.lt_or_ge p q with h | h
    · exact h
    · exact absurd (by rw [show q = p by have := hG.pq; omega]) h0
  have hx1 : x (p + 1) = x p + 1 := by
    have h2 := hG.xlo (p + 1) (by omega) (by omega)
    have h3 := hG.xstep p le_rfl hpq
    rw [abs_le] at h3
    omega
  have hqp := hG.xhi p le_rfl hG.pq
  by_cases hamp : x q = x p + 1
  · by_cases h2 : x (q - 1) = x q
    · exact case_plateau_end hS hBw hs hG ih h0 h2
    · exact case_amp1 hS hBw hG hamp h1 h2
  have hA2 : x p + 2 ≤ x q := by omega
  by_cases hret : ∃ i, p < i ∧ i ≤ q ∧ x i = x p
  · exact case_return hS hBw hs hG ih hA2 hx1 hret
  · push_neg at hret
    exact case_noreturn hS hBw hs hG ih hA2 hx1 hret

theorem ih_all (hS : Setting σ T) (hBw : 2 * B + 10 ≤ w) (n : ℕ) : IH σ T B w n := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro τ x p q a b e hlt hs hG
    exact main_step hS hBw (b - a) (ihn (b - a) hlt) τ x p q a b e rfl hs hG

end Cases

/-- **The combinatorial core of pattern following.** Let `x` be a pattern of length `N`
(consecutive values at most one apart) whose first value is its minimum and whose last value is
its maximum. If the fine reading `σ` is crooked up to time `T`, the coarse reading `τ` is
`w`-slow with `w ≥ 4N + 10`, the canonical readings `τ (σ f)` stay between the minimum and the
maximum of `x`, start at the minimum and end at the maximum, and `T ≥ N - 1`, then there is a
lift `φ : [0, T] → [0, N - 1]` moving by at most one, from `0` to `N - 1`, with `x (φ f)`
allowed at `f` with radius `w`. -/
theorem realize {σ : ℕ → ℤ} {T w N : ℕ} (hS : Setting σ T) (hw : 4 * N + 10 ≤ w)
    {τ : ℤ → ℤ} (hs : Slow w τ) {x : ℕ → ℤ} (hN : 1 ≤ N)
    (hxs : ∀ i, i + 1 < N → |x (i + 1) - x i| ≤ 1)
    (hxlo : ∀ i, i < N → x 0 ≤ x i) (hxhi : ∀ i, i < N → x i ≤ x (N - 1))
    (hrlo : ∀ f, f ≤ T → x 0 ≤ τ (σ f)) (hrhi : ∀ f, f ≤ T → τ (σ f) ≤ x (N - 1))
    (h0 : τ (σ 0) = x 0) (hT : τ (σ T) = x (N - 1)) (hlen : N - 1 ≤ T) :
    Real σ τ w x 0 (N - 1) 0 T 0 (N - 1) := by
  have hG : Good σ T (2 * (N - 1)) τ x 0 (N - 1) 0 T 0 :=
    { pq := Nat.zero_le _
      ab := Nat.zero_le _
      bT := le_rfl
      len := by omega
      xstep := fun i _ h2 => hxs i (by omega)
      xlo := fun i _ h2 => hxlo i (by omega)
      xhi := fun i _ h2 => hxhi i (by omega)
      rlo := fun f _ h2 => hrlo f h2
      rhi := fun f _ h2 => hrhi f h2
      anca := h0 ▸ al_canon τ 0
      ancb := hT ▸ al_canon τ T
      budget := by omega }
  exact ih_all hS (by omega) (T + 1) τ x 0 (N - 1) 0 T 0 (by omega) hs hG

end HPC.PatCore
