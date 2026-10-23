import HPC.Fold.Leg3Mid

/-!
# Folding onto a four-leg walk

`HPC/Fold/Leg3.lean` and `HPC/Fold/Leg3Mid.lean` fold an arm onto a three-leg walk.  At a
basepoint standing exactly four levels above the floor of a band of width eight, two of the four
branches are served by no three-leg walk at all, and a fourth leg is needed.  This file is the
corresponding engine.

The walk `leg4Walk L H K M P` runs from `P - 1` up to the peak `K`, down to the valley `M`, up to
`H - 1`, and down to `L + 1`.  The fold is again the greedy time assignment (`gstep4`, `gseq4`):
at each step the arm is carried as far along the walk as its new level allows.  The invariant
`gseq4_inv` is the window condition `Val4` together with six progress clauses, each switched on by
a feature of the arm's past:

```
E  : the arm has been at P - 2 or below
R  : the arm has been at K or above, or E and after that at K - 1 or above
E2 : the arm has been at K + 1 or above, or E and after that at K or above
S  : the arm has been at M - 1 or below, or E2 and after that at M + 1 or below
S2 : the arm has been at M - 1 or below, or at K + 1 or above and after that at M or below
T  : the arm has been at K + 2 or above, or S2 and after that at H - 2 or above
```

The arm enters only through three announcements — this is the whole interface of the engine:

* **floor.** Every descent to `M - 1` or below is preceded by a time at `K` or above, or by a time
  at `P - 2` or below followed by one at `K - 1` or above.
* **deep floor.** Every descent to `M - 2` or below is preceded by a time at `K + 2` or above, or
  by a time at `M - 1` or below followed by one at `H - 2` or above, or by three times, in order,
  at `K + 1` or above, at `M` or below, and at `H - 2` or above.
* **ceiling.** Every ascent to `K + 2` or above is preceded by a time at `M - 1` or below, or by
  two times, in order, at `K + 1` or above and at `M + 1` or below, or by three times, in order,
  at `P - 2` or below, at `K` or above, and at `M + 1` or below.

No crookedness is used inside the engine, so its reflection is free.
-/

namespace HPC.Fold

/-! ## The walk -/

/-- The four-leg walk: from `P - 1` up to the peak `K`, down to the valley `M`, up to `H - 1`,
down to `L + 1`. -/
def leg4Walk (L H K M P : ℤ) (u : ℕ) : ℤ :=
  if (u : ℤ) ≤ K - P + 1 then P - 1 + (u : ℤ)
  else if (u : ℤ) ≤ 2 * K - P + 1 - M then 2 * K - P + 1 - (u : ℤ)
  else if (u : ℤ) ≤ 2 * K - P + H - 2 * M then (u : ℤ) - (2 * K - P + 1) + 2 * M
  else 2 * K - P + 2 * H - 2 * M - 1 - (u : ℤ)

/-- The number of times of `leg4Walk`. -/
def leg4Len (L H K M P : ℤ) : ℕ := (2 * K - P + 2 * H - 2 * M - L - 1).toNat

/-- **The window condition.** `Val4 L H K M P v u` says that the walk time `u` serves the level
`v`, written out on the four monotone legs. -/
def Val4 (L H K M P : ℤ) (v u : ℤ) : Prop :=
  (0 ≤ u ∧ u ≤ K - P + 1 ∧ v - P ≤ u ∧ u ≤ v - P + 2) ∨
  (K - P + 1 ≤ u ∧ u ≤ 2 * K - P + 1 - M ∧ 2 * K - P - v ≤ u ∧ u ≤ 2 * K - P + 2 - v) ∨
  (2 * K - P + 1 - M ≤ u ∧ u ≤ 2 * K - P + H - 2 * M ∧
    v + 2 * K - P - 2 * M ≤ u ∧ u ≤ v + 2 * K - P + 2 - 2 * M) ∨
  (2 * K - P + H - 2 * M ≤ u ∧ u ≤ 2 * K - P + 2 * H - 2 * M - L - 2 ∧
    2 * K - P + 2 * H - 2 * M - 2 - v ≤ u ∧ u ≤ 2 * K - P + 2 * H - 2 * M - v)

instance (L H K M P v u : ℤ) : Decidable (Val4 L H K M P v u) := by unfold Val4; infer_instance

theorem val4_bounds {L H K M P v u : ℤ} (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1) (hLP : L + 2 ≤ P)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (h : Val4 L H K M P v u) :
    0 ≤ u ∧ u ≤ 2 * K - P + 2 * H - 2 * M - L - 2 := by
  unfold Val4 at h; omega

/-- A legal time is inside the window of its level. -/
theorem val4_walk {L H K M P v u : ℤ} (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1) (hLP : L + 2 ≤ P)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (h : Val4 L H K M P v u) :
    |v - leg4Walk L H K M P u.toNat| ≤ 1 := by
  obtain ⟨h0, hlast⟩ := val4_bounds hPK hKH hLP hLM hMP h
  have hcast : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg h0
  unfold Val4 at h
  unfold leg4Walk
  by_cases hc1 : ((u.toNat : ℕ) : ℤ) ≤ K - P + 1
  · rw [if_pos hc1, abs_le]; omega
  · rw [if_neg hc1]
    by_cases hc2 : ((u.toNat : ℕ) : ℤ) ≤ 2 * K - P + 1 - M
    · rw [if_pos hc2, abs_le]; omega
    · rw [if_neg hc2]
      by_cases hc3 : ((u.toNat : ℕ) : ℤ) ≤ 2 * K - P + H - 2 * M
      · rw [if_pos hc3, abs_le]; omega
      · rw [if_neg hc3, abs_le]; omega

/-! ## The greedy step -/

/-- One greedy step: advance along the walk if the new level allows it, else stay, else
retreat. -/
def gstep4 (L H K M P : ℤ) (v q : ℤ) : ℤ :=
  if Val4 L H K M P v (q + 1) then q + 1 else if Val4 L H K M P v q then q else q - 1

theorem gstep4_dist (L H K M P v q : ℤ) :
    q - 1 ≤ gstep4 L H K M P v q ∧ gstep4 L H K M P v q ≤ q + 1 := by
  unfold gstep4; split_ifs <;> omega

/-- The three cases of a greedy step, uniformly. -/
theorem gstep4_elim {L H K M P v q : ℤ} {Q : ℤ → Prop}
    (hup : Val4 L H K M P v (q + 1) → Q (q + 1))
    (hmid : ¬ Val4 L H K M P v (q + 1) → Val4 L H K M P v q → Q q)
    (hdown : ¬ Val4 L H K M P v (q + 1) → ¬ Val4 L H K M P v q → Q (q - 1)) :
    Q (gstep4 L H K M P v q) := by
  unfold gstep4
  by_cases h1 : Val4 L H K M P v (q + 1)
  · rw [if_pos h1]; exact hup h1
  · rw [if_neg h1]
    by_cases h2 : Val4 L H K M P v q
    · rw [if_pos h2]; exact hmid h1 h2
    · rw [if_neg h2]; exact hdown h1 h2

/-- A lower bound on the greedy time: any legal position within reach is a lower bound, and so
is any position the greedy cannot have fallen below. -/
theorem gstep4_lower {L H K M P v' q b : ℤ} (hbq : b ≤ q + 1)
    (hb : b ≤ q - 1 ∨ Val4 L H K M P v' b) : b ≤ gstep4 L H K M P v' q := by
  unfold gstep4
  split_ifs with h1 h2
  · omega
  · rcases hb with h | h
    · omega
    · by_contra hc
      have e : b = q + 1 := by omega
      exact h1 (e ▸ h)
  · rcases hb with h | h
    · omega
    · by_contra hc
      rcases (show b = q + 1 ∨ b = q by omega) with e | e
      · exact h1 (e ▸ h)
      · exact h2 (e ▸ h)

/-- The greedy step lands on a legal position as soon as one of the three positions within reach
is legal. -/
theorem val4_gstep_of {L H K M P v' q : ℤ}
    (h : Val4 L H K M P v' (q + 1) ∨ Val4 L H K M P v' q ∨ Val4 L H K M P v' (q - 1)) :
    Val4 L H K M P v' (gstep4 L H K M P v' q) := by
  unfold gstep4
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · rcases h with h' | h' | h'
    · exact absurd h' h1
    · exact absurd h' h2
    · exact h'

set_option maxHeartbeats 4000000 in
/-- **The greedy step stays legal.**  The three exclusions are exactly what the arm's conditions
supply: a step to the valley floor needs the descending leg, a step below it the last leg, and a
step above the peak the third leg. -/
theorem val4_gstep {L H K M P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ M - 1 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hK : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q) :
    Val4 L H K M P v' (gstep4 L H K M P v' q) := by
  refine val4_gstep_of ?_
  by_cases c1 : Val4 L H K M P v' (q + 1)
  · exact Or.inl c1
  by_cases c2 : Val4 L H K M P v' q
  · exact Or.inr (Or.inl c2)
  refine Or.inr (Or.inr ?_)
  unfold Val4 at hval c1 c2 ⊢
  push_neg at c1 c2
  rcases hval with h | h | h | h <;> omega

/-- Everything a greedy step guarantees, packaged so that `omega` can use it. -/
theorem gstep4_facts {L H K M P v' q : ℤ} (A : ℤ → Prop)
    (hnew : Val4 L H K M P v' (gstep4 L H K M P v' q))
    (hA : ∀ g : ℤ, Val4 L H K M P v' g → (g = q + 1 ∨ g = q ∨ g = q - 1) →
      (Val4 L H K M P v' (q + 1) → g = q + 1) →
      (¬ Val4 L H K M P v' (q + 1) → Val4 L H K M P v' q → g = q) → A g) :
    A (gstep4 L H K M P v' q) := by
  revert hnew
  refine gstep4_elim (Q := fun g => Val4 L H K M P v' g → A g) ?_ ?_ ?_
  · intro h1 hn; exact hA _ hn (Or.inl rfl) (fun _ => rfl) (fun h => absurd h1 h)
  · intro h1 h2 hn; exact hA _ hn (Or.inr (Or.inl rfl)) (fun h => absurd h h1) (fun _ _ => rfl)
  · intro h1 h2 hn
    exact hA _ hn (Or.inr (Or.inr rfl)) (fun h => absurd h h1) (fun _ h => absurd h h2)

/-! ## The progress clauses

Each clause records that one lower bound on the greedy time survives a step, either because it
already held or because the new level triggers it.  They are grouped by the feature they belong
to, one group per leg boundary.  Each is proved the same way: the bound is within reach of the
old time, and the position it names is legal for the new level, so the greedy time is at least
that position. -/

set_option maxHeartbeats 1000000 in
/-- The progress clauses for the end of the first leg. -/
theorem prog4_E {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ M - 1 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q) :
    (min (v - P + 2) (K - P + 1) ≤ q → min (v' - P + 2) (K - P + 1) ≤ gstep4 L H K M P v' q) ∧
    (v' ≤ P - 2 → min (v' - P + 2) (K - P + 1) ≤ gstep4 L H K M P v' q) := by
  refine ⟨?_, ?_⟩ <;>
    (intros
     refine gstep4_lower ?_ ?_
     · unfold Val4 at hval; omega
     · unfold Val4 at hval ⊢; omega)

set_option maxHeartbeats 1000000 in
/-- The progress clauses for the start of the second leg. -/
theorem prog4_R {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ M - 1 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q) :
    (2 * K - P - v ≤ q → 2 * K - P - v' ≤ gstep4 L H K M P v' q) ∧
    (K ≤ v' → 2 * K - P - v' ≤ gstep4 L H K M P v' q) ∧
    (min (v - P + 2) (K - P + 1) ≤ q → K - 1 ≤ v' → 2 * K - P - v' ≤ gstep4 L H K M P v' q) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (intros
     refine gstep4_lower ?_ ?_
     · unfold Val4 at hval; omega
     · unfold Val4 at hval ⊢; omega)

set_option maxHeartbeats 1000000 in
/-- The progress clauses for the end of the second leg. -/
theorem prog4_E2 {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ M - 1 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q) :
    (min (2 * K - P + 2 - v) (2 * K - P + 1 - M) ≤ q →
      min (2 * K - P + 2 - v') (2 * K - P + 1 - M) ≤ gstep4 L H K M P v' q) ∧
    (K + 1 ≤ v' → min (2 * K - P + 2 - v') (2 * K - P + 1 - M) ≤ gstep4 L H K M P v' q) ∧
    (min (v - P + 2) (K - P + 1) ≤ q → K ≤ v' →
      min (2 * K - P + 2 - v') (2 * K - P + 1 - M) ≤ gstep4 L H K M P v' q) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (intros
     refine gstep4_lower ?_ ?_
     · unfold Val4 at hval; omega
     · unfold Val4 at hval ⊢; omega)

set_option maxHeartbeats 1000000 in
/-- The progress clauses for the start of the third leg. -/
theorem prog4_S {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ M - 1 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q) :
    (v + 2 * K - P - 2 * M ≤ q → v' + 2 * K - P - 2 * M ≤ gstep4 L H K M P v' q) ∧
    (v' ≤ M - 1 → v' + 2 * K - P - 2 * M ≤ gstep4 L H K M P v' q) ∧
    (min (2 * K - P + 2 - v) (2 * K - P + 1 - M) ≤ q → v' ≤ M + 1 →
      v' + 2 * K - P - 2 * M ≤ gstep4 L H K M P v' q) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (intros
     refine gstep4_lower ?_ ?_
     · unfold Val4 at hval; omega
     · unfold Val4 at hval ⊢; omega)

set_option maxHeartbeats 1000000 in
/-- The progress clauses for the end of the third leg. -/
theorem prog4_S2 {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ M - 1 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q) :
    (min (v + 2 * K - P + 2 - 2 * M) (2 * K - P + H - 2 * M) ≤ q →
      min (v' + 2 * K - P + 2 - 2 * M) (2 * K - P + H - 2 * M) ≤ gstep4 L H K M P v' q) ∧
    (v' ≤ M - 1 →
      min (v' + 2 * K - P + 2 - 2 * M) (2 * K - P + H - 2 * M) ≤ gstep4 L H K M P v' q) ∧
    (min (2 * K - P + 2 - v) (2 * K - P + 1 - M) ≤ q → v' ≤ M →
      min (v' + 2 * K - P + 2 - 2 * M) (2 * K - P + H - 2 * M) ≤ gstep4 L H K M P v' q) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (intros
     refine gstep4_lower ?_ ?_
     · unfold Val4 at hval; omega
     · unfold Val4 at hval ⊢; omega)

set_option maxHeartbeats 1000000 in
/-- The progress clauses for the last leg. -/
theorem prog4_T {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ M - 1 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q) :
    (2 * K - P + 2 * H - 2 * M - 2 - v ≤ q →
      2 * K - P + 2 * H - 2 * M - 2 - v' ≤ gstep4 L H K M P v' q) ∧
    (K + 2 ≤ v' → 2 * K - P + 2 * H - 2 * M - 2 - v' ≤ gstep4 L H K M P v' q) ∧
    (min (v + 2 * K - P + 2 - 2 * M) (2 * K - P + H - 2 * M) ≤ q → H - 2 ≤ v' →
      2 * K - P + 2 * H - 2 * M - 2 - v' ≤ gstep4 L H K M P v' q) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (intros
     refine gstep4_lower ?_ ?_
     · unfold Val4 at hval; omega
     · unfold Val4 at hval ⊢; omega)

/-! ## The greedy time sequence -/

/-- The greedy walk time of a sequence of levels. -/
def gseq4 (L H K M P : ℤ) (u : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | (j + 1) => gstep4 L H K M P (u (j + 1)) (gseq4 L H K M P u j)

theorem gseq4_zero (L H K M P : ℤ) (u : ℕ → ℤ) : gseq4 L H K M P u 0 = 0 := rfl

theorem gseq4_succ (L H K M P : ℤ) (u : ℕ → ℤ) (j : ℕ) :
    gseq4 L H K M P u (j + 1) = gstep4 L H K M P (u (j + 1)) (gseq4 L H K M P u j) := rfl

set_option maxHeartbeats 1000000 in
/-- **The invariant.**  A level sequence based at `P` inside `[L, H]` whose descents to the valley
floor, descents below it and ascents above the peak are announced by the features keeps the greedy
time legal. -/
theorem gseq4_inv (L H K M P : ℤ) (u : ℕ → ℤ) (N : ℕ) (E R E2 S S2 T : ℕ → Prop)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hu0 : u 0 = P)
    (hlo : ∀ j, j ≤ N → L ≤ u j) (hhi : ∀ j, j ≤ N → u j ≤ H)
    (hlip : ∀ j, j + 1 ≤ N → u j - 1 ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1)
    (hE0 : ¬ E 0) (hR0 : ¬ R 0) (hE20 : ¬ E2 0) (hS0 : ¬ S 0) (hS20 : ¬ S2 0) (hT0 : ¬ T 0)
    (hEs : ∀ j, j + 1 ≤ N → E (j + 1) → E j ∨ u (j + 1) ≤ P - 2)
    (hRs : ∀ j, j + 1 ≤ N → R (j + 1) → R j ∨ K ≤ u (j + 1) ∨ (E j ∧ K - 1 ≤ u (j + 1)))
    (hE2s : ∀ j, j + 1 ≤ N → E2 (j + 1) → E2 j ∨ K + 1 ≤ u (j + 1) ∨ (E j ∧ K ≤ u (j + 1)))
    (hSs : ∀ j, j + 1 ≤ N → S (j + 1) → S j ∨ u (j + 1) ≤ M - 1 ∨ (E2 j ∧ u (j + 1) ≤ M + 1))
    (hS2s : ∀ j, j + 1 ≤ N → S2 (j + 1) → S2 j ∨ u (j + 1) ≤ M - 1 ∨
      (E2 j ∧ u (j + 1) ≤ M))
    (hTs : ∀ j, j + 1 ≤ N → T (j + 1) → T j ∨ K + 2 ≤ u (j + 1) ∨ (S2 j ∧ H - 2 ≤ u (j + 1)))
    (hfloor : ∀ j, j + 1 ≤ N → u (j + 1) ≤ M - 1 → R j)
    (hdeep : ∀ j, j + 1 ≤ N → u (j + 1) ≤ M - 2 → T j)
    (hceil : ∀ j, j + 1 ≤ N → K + 2 ≤ u (j + 1) → S j) :
    ∀ j, j ≤ N → Val4 L H K M P (u j) (gseq4 L H K M P u j) ∧
      (E j → min (u j - P + 2) (K - P + 1) ≤ gseq4 L H K M P u j) ∧
      (R j → 2 * K - P - u j ≤ gseq4 L H K M P u j) ∧
      (E2 j → min (2 * K - P + 2 - u j) (2 * K - P + 1 - M) ≤ gseq4 L H K M P u j) ∧
      (S j → u j + 2 * K - P - 2 * M ≤ gseq4 L H K M P u j) ∧
      (S2 j → min (u j + 2 * K - P + 2 - 2 * M) (2 * K - P + H - 2 * M) ≤
        gseq4 L H K M P u j) ∧
      (T j → 2 * K - P + 2 * H - 2 * M - 2 - u j ≤ gseq4 L H K M P u j) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨?_, fun h => absurd h hE0, fun h => absurd h hR0, fun h => absurd h hE20,
        fun h => absurd h hS0, fun h => absurd h hS20, fun h => absurd h hT0⟩
      rw [gseq4_zero, hu0]
      unfold Val4
      omega
  | succ j ih =>
      intro hj
      obtain ⟨hval, hE, hR, hE2, hS, hS2, hT⟩ := ih (by omega)
      have hv0 := hlo j (by omega)
      have hvH := hhi j (by omega)
      have hv'0 := hlo (j + 1) hj
      have hv'H := hhi (j + 1) hj
      obtain ⟨hl1, hl2⟩ := hlip j hj
      have ha0 : u (j + 1) ≤ M - 1 → 2 * K - P - u j ≤ gseq4 L H K M P u j :=
        fun h => hR (hfloor j hj h)
      have ha0' : u (j + 1) ≤ M - 2 →
          2 * K - P + 2 * H - 2 * M - 2 - u j ≤ gseq4 L H K M P u j :=
        fun h => hT (hdeep j hj h)
      have haK : K + 2 ≤ u (j + 1) → u j + 2 * K - P - 2 * M ≤ gseq4 L H K M P u j :=
        fun h => hS (hceil j hj h)
      have hnew : Val4 L H K M P (u (j + 1)) (gseq4 L H K M P u (j + 1)) := by
        rw [gseq4_succ]
        exact val4_gstep hLP hPL hPK hKH hLM hMP hPM hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p1, p2⟩ :=
        prog4_E hLP hPL hPK hKH hLM hMP hPM hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p3, p4, p5⟩ :=
        prog4_R hLP hPL hPK hKH hLM hMP hPM hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p6, p7, p8⟩ :=
        prog4_E2 hLP hPL hPK hKH hLM hMP hPM hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p9, p10, p11⟩ :=
        prog4_S hLP hPL hPK hKH hLM hMP hPM hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p12, p13, p13'⟩ :=
        prog4_S2 hLP hPL hPK hKH hLM hMP hPM hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p14, p15, p16⟩ :=
        prog4_T hLP hPL hPK hKH hLM hMP hPM hMK hHK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      rw [gseq4_succ] at hnew ⊢
      refine ⟨hnew, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rcases hEs j hj h with h' | h'
        · exact p1 (hE h')
        · exact p2 h'
      · intro h
        rcases hRs j hj h with h' | h' | h'
        · exact p3 (hR h')
        · exact p4 h'
        · exact p5 (hE h'.1) h'.2
      · intro h
        rcases hE2s j hj h with h' | h' | h'
        · exact p6 (hE2 h')
        · exact p7 h'
        · exact p8 (hE h'.1) h'.2
      · intro h
        rcases hSs j hj h with h' | h' | h'
        · exact p9 (hS h')
        · exact p10 h'
        · exact p11 (hE2 h'.1) h'.2
      · intro h
        rcases hS2s j hj h with h' | h' | h'
        · exact p12 (hS2 h')
        · exact p13 h'
        · exact p13' (hE2 h'.1) h'.2
      · intro h
        rcases hTs j hj h with h' | h' | h'
        · exact p14 (hT h')
        · exact p15 h'
        · exact p16 (hS2 h'.1) h'.2

/-! ## From legal times to a fold -/

/-- A legal greedy time sequence is a fold onto `leg4Walk`. -/
theorem foldsOnto_leg4_of_val4 {m : ℕ} (f : Fin m → ℤ) (L H K M P : ℤ) (u : ℕ → ℤ)
    (hLP : L + 2 ≤ P) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2)
    (hu : ∀ j : Fin m, u j.val = f j)
    (hval : ∀ j : Fin m, Val4 L H K M P (u j.val) (gseq4 L H K M P u j.val)) :
    FoldsOnto f (leg4Len L H K M P) (leg4Walk L H K M P) := by
  refine ⟨fun j => (gseq4 L H K M P u j.val).toNat, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro j
    obtain ⟨h1, h2⟩ := val4_bounds hPK hKH hLP hLM hMP (hval j)
    simp only [leg4Len]
    omega
  · intro j j' hjj'
    obtain ⟨h1, h2⟩ := val4_bounds hPK hKH hLP hLM hMP (hval j)
    obtain ⟨h3, h4⟩ := val4_bounds hPK hKH hLP hLM hMP (hval j')
    have hstep : gseq4 L H K M P u j'.val =
        gstep4 L H K M P (u j'.val) (gseq4 L H K M P u j.val) := by
      rw [show j'.val = j.val + 1 from hjj', gseq4_succ]
    obtain ⟨h5, h6⟩ := gstep4_dist L H K M P (u j'.val) (gseq4 L H K M P u j.val)
    rw [abs_le]
    omega
  · intro j hj
    have h : gseq4 L H K M P u j.val = 0 := by rw [hj, gseq4_zero]
    rw [h]
    rfl
  · intro j
    have h := hval j
    rw [hu j] at h
    exact val4_walk hPK hKH hLP hLM hMP h

/-! ## The fold, with the announcements as hypotheses -/

set_option maxHeartbeats 1000000 in
/-- **The four-leg fold.**  A 1-Lipschitz arm in `[L, H]` based at `P` folds onto
`leg4Walk L H K M P` as soon as its descents to `M - 1`, its descents to `M - 2` and its ascents
to `K + 2` are announced. -/
theorem foldsOnto_leg4 {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L H K M P : ℤ)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hPM : P - 2 ≤ M) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (h0 : f ⟨0, hm⟩ = P) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hfloor : ∀ d : Fin m, f d ≤ M - 1 →
      (∃ k : Fin m, k.val < d.val ∧ K ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ P - 2 ∧ K - 1 ≤ f k'))
    (hdeep : ∀ d : Fin m, f d ≤ M - 2 →
      (∃ k : Fin m, k.val < d.val ∧ K + 2 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ M - 1 ∧ H - 2 ≤ f k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        K + 1 ≤ f k ∧ f k' ≤ M ∧ H - 2 ≤ f k''))
    (hceil : ∀ d : Fin m, K + 2 ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ M - 1) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ K + 1 ≤ f k ∧ f k' ≤ M + 1) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        f k ≤ P - 2 ∧ K ≤ f k' ∧ f k'' ≤ M + 1)) :
    FoldsOnto f (leg4Len L H K M P) (leg4Walk L H K M P) := by
  classical
  set u : ℕ → ℤ := fun k => if h : k < m then f ⟨k, h⟩ else P with hudef
  have hu : ∀ j : Fin m, u j.val = f j := by
    intro j
    simp only [hudef, j.isLt, dif_pos]
  refine foldsOnto_leg4_of_val4 f L H K M P u hLP hPK hKH hLM hMP hu ?_
  set E : ℕ → Prop := fun j => ∃ k : Fin m, k.val ≤ j ∧ f k ≤ P - 2 with hEdef
  set R : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ K ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ P - 2 ∧ K - 1 ≤ f k') with hRdef
  set E2 : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ K + 1 ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ P - 2 ∧ K ≤ f k') with hE2def
  set S : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ f k ≤ M - 1) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ K + 1 ≤ f k ∧ f k' ≤ M + 1) ∨
    (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val ≤ j ∧
      f k ≤ P - 2 ∧ K ≤ f k' ∧ f k'' ≤ M + 1) with hSdef
  set S2 : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ f k ≤ M - 1) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ K + 1 ≤ f k ∧ f k' ≤ M) with hS2def
  set T : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ K + 2 ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ M - 1 ∧ H - 2 ≤ f k') ∨
    (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val ≤ j ∧
      K + 1 ≤ f k ∧ f k' ≤ M ∧ H - 2 ≤ f k'') with hTdef
  have key := gseq4_inv L H K M P u (m - 1) E R E2 S S2 T hLP hPL hPK hKH hLM hMP hPM hMK hHK
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (key j.val (by have := j.isLt; omega)).1
  -- `u 0 = P`
  · have e : u 0 = f ⟨0, hm⟩ := by simpa using hu ⟨0, hm⟩
    rw [e, h0]
  -- the band
  · intro j hj
    have hjm : j < m := by omega
    have e : u j = f ⟨j, hjm⟩ := by simpa using hu ⟨j, hjm⟩
    have := hL ⟨j, hjm⟩
    omega
  · intro j hj
    have hjm : j < m := by omega
    have e : u j = f ⟨j, hjm⟩ := by simpa using hu ⟨j, hjm⟩
    have := hH ⟨j, hjm⟩
    omega
  -- Lipschitz
  · intro j hj
    have hjm : j < m := by omega
    have hj1m : j + 1 < m := by omega
    have e1 : u j = f ⟨j, hjm⟩ := by simpa using hu ⟨j, hjm⟩
    have e2 : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
    have := hf ⟨j, hjm⟩ ⟨j + 1, hj1m⟩ rfl
    rw [abs_le] at this
    omega
  -- the features are absent at time zero
  · rintro ⟨k, hk, hkf⟩
    have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
    rw [this, h0] at hkf; omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', -, -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', -, -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
    · omega
  -- the feature updates
  · rintro j hj ⟨k, hk, hkf⟩
    rcases Nat.lt_or_ge k.val (j + 1) with h | h
    · exact Or.inl ⟨k, by omega, hkf⟩
    · right
      have hj1m : j + 1 < m := by omega
      have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
      have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
      rw [hk1] at hkf
      omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; left
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
      · refine Or.inr (Or.inr ⟨⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; left
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
      · refine Or.inr (Or.inr ⟨⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; left
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr (Or.inl ⟨k, k', hkk', by omega, hkf, hk'f⟩))
      · refine Or.inr (Or.inr ⟨Or.inl ⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
    · rcases Nat.lt_or_ge k''.val (j + 1) with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', by omega, hkf, hk'f, hk''f⟩))
      · refine Or.inr (Or.inr ⟨Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k'' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k''.val = j + 1 by omega)
        rw [hk1] at hk''f
        omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; left
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
      · refine Or.inr (Or.inr ⟨Or.inl ⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; left
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr (Or.inl ⟨k, k', hkk', by omega, hkf, hk'f⟩))
      · refine Or.inr (Or.inr ⟨Or.inl ⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
    · rcases Nat.lt_or_ge k''.val (j + 1) with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', by omega, hkf, hk'f, hk''f⟩))
      · refine Or.inr (Or.inr ⟨Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k'' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k''.val = j + 1 by omega)
        rw [hk1] at hk''f
        omega
  -- a descent to the valley floor is announced
  · intro j hj hzero
    have hj1m : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
    rcases hfloor ⟨j + 1, hj1m⟩ (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, hkf⟩
    · exact Or.inr ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, hk'f⟩
  -- a descent below it is announced
  · intro j hj hzero
    have hj1m : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
    rcases hdeep ⟨j + 1, hj1m⟩ (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, hkf⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, hk'f⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', by simpa using Nat.lt_succ_iff.mp hk'',
        hkf, hk'f, hk''f⟩)
  -- an ascent to `K + 2` is announced
  · intro j hj hceil'
    have hj1m : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
    rcases hceil ⟨j + 1, hj1m⟩ (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, hkf⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, hk'f⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', by simpa using Nat.lt_succ_iff.mp hk'',
        hkf, hk'f, hk''f⟩)

end HPC.Fold
