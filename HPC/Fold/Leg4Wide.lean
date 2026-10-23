import HPC.Fold.Leg4
import HPC.Fold.Span8Mid4

/-!
# The four-leg engine with a higher base and a deeper valley

`HPC/Fold/Leg4.lean` folds an arm onto the four-leg walk `leg4Walk L H K M P` — from `P - 1` up to
the peak `K`, down to the valley `M`, up to `H - 1`, down to `L + 1` — but only inside the window

```
L + 2 ≤ P ≤ L + 4,   P + 1 ≤ K ≤ H - 1,   L + 1 ≤ M,   M = P - 2,   M + 3 ≤ K,   H ≤ K + 3
```

so the base is at most `L + 4` and the valley exactly two below it. The walks the branch `L + 5`
needs are outside that window on both counts: the shortest walk serving the hardest pairs of the
censuses is `5 → 7 → 3 → 8 → 1`, which is `leg4Walk L (L + 9) (L + 7) (L + 3) (L + 6)` — base
`L + 6`, valley three below the base. This file is the engine for the whole family:

```
L + 2 ≤ P ≤ L + 6,   P ≤ K ≤ H - 1,   L + 1 ≤ M ≤ P - 2,   M + 3 ≤ K,   H ≤ K + 3
```

Three things change, and only three.

* **The base may sit anywhere in `[P - 1, P]`**, not at `P` exactly — which is what an arm of the
  branch `L + 5` supplies, its basepoint standing at `L + 5 = P - 1` for the walk above. (When the
  first leg is a single step, `K = P`, the base must also be below the peak: `f 0 ≤ K - 1`, which
  is automatic as soon as `P < K`.)
* **The valley is free**: any `M` between `L + 1` and `P - 2`, not `P - 2` exactly; and the first
  leg may be a single step (`K = P`), which is what the mirror shapes need.
* **The two floor announcements are read at `P - 3` and `P - 4`**, where `HPC/Fold/Leg4.lean` reads
  them at `M - 1` and `M - 2`. For `M = P - 2` those are the same two levels, so this engine
  contains the old one on its own window; for a deeper valley they are the levels that matter,
  because what the greedy has to survive is a descent measured from the *base*, not from the
  valley:

  * **floor.** Every descent to `P - 3` or below is preceded by a time at `K` or above, or by a
    time at `P - 2` or below followed by one at `K - 1` or above.
  * **deep floor.** Every descent to `P - 4` or below is preceded by a time at `K + 2` or above, or
    by a time at `M - 1` or below followed by one at `H - 2` or above, or by three times, in order,
    at `K + 1` or above, at `M` or below, and at `H - 2` or above.
  * **ceiling.** Unchanged: every ascent to `K + 2` or above is preceded by a time at `M - 1` or
    below, or by two times, in order, at `K + 1` or above and at `M + 1` or below, or by three
    times, in order, at `P - 2` or below, at `K` or above, and at `M + 1` or below.

The raising of the two floor announcements is forced, not decorative: `engine-batch55.c` exhibits
arms which satisfy the announcements *as `HPC/Fold/Leg4.lean` states them* at `P = L + 6`,
`M = P - 3` and do not fold onto the walk at all. Read at `P - 3` and `P - 4` instead, the same
program finds no failure of the invariant at any parameter set of the window above.

Everything else — the walk, its length, the window condition `Val4`, the greedy step `gstep4`, the
greedy sequence `gseq4` and the reflected walk `leg4Walk'` — is imported unchanged, so the two
engines fold onto the same walks by the same itineraries. No crookedness is used inside the engine,
so its reflection is free: `foldsOnto_leg4W_refl` transports a fold of the reflected arm onto
`leg4Walk` into a fold of the arm onto `leg4Walk'`.
-/

namespace HPC.Fold


theorem val4_boundsW {L H K M P v u : ℤ} (hPK : P ≤ K) (hKH : K ≤ H - 1) (hLP : L + 2 ≤ P)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (h : Val4 L H K M P v u) :
    0 ≤ u ∧ u ≤ 2 * K - P + 2 * H - 2 * M - L - 2 := by
  unfold Val4 at h; omega

/-- A legal time is inside the window of its level. -/
theorem val4_walkW {L H K M P v u : ℤ} (hPK : P ≤ K) (hKH : K ≤ H - 1) (hLP : L + 2 ≤ P)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (h : Val4 L H K M P v u) :
    |v - leg4Walk L H K M P u.toNat| ≤ 1 := by
  obtain ⟨h0, hlast⟩ := val4_boundsW hPK hKH hLP hLM hMP h
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

set_option maxHeartbeats 4000000 in
/-- **The greedy step stays legal.**  The three exclusions are exactly what the arm's conditions
supply: a step to the valley floor needs the descending leg, a step below it the last leg, and a
step above the peak the third leg. -/
theorem val4_gstepW {L H K M P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ P - 4 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
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

/-! ## The progress clauses

Each clause records that one lower bound on the greedy time survives a step, either because it
already held or because the new level triggers it.  They are grouped by the feature they belong
to, one group per leg boundary.  Each is proved the same way: the bound is within reach of the
old time, and the position it names is legal for the new level, so the greedy time is at least
that position. -/

set_option maxHeartbeats 1000000 in
/-- The progress clauses for the end of the first leg. -/
theorem prog4_EW {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ P - 4 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
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
theorem prog4_RW {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ P - 4 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
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
theorem prog4_E2W {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ P - 4 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
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
theorem prog4_SW {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ P - 4 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
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
theorem prog4_S2W {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ P - 4 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
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
theorem prog4_TW {L H K M P v q v' : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K)
    (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ P - 4 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
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


set_option maxHeartbeats 1000000 in
/-- **The invariant.**  A level sequence based at `P` inside `[L, H]` whose descents to the valley
floor, descents below it and ascents above the peak are announced by the features keeps the greedy
time legal. -/
theorem gseq4_invW (L H K M P : ℤ) (u : ℕ → ℤ) (N : ℕ) (E R E2 S S2 T : ℕ → Prop)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hu0 : P - 1 ≤ u 0) (hu0' : u 0 ≤ P)
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
    (hfloor : ∀ j, j + 1 ≤ N → u (j + 1) ≤ P - 3 → R j)
    (hdeep : ∀ j, j + 1 ≤ N → u (j + 1) ≤ P - 4 → T j)
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
      rw [gseq4_zero]
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
      have ha0 : u (j + 1) ≤ P - 3 → 2 * K - P - u j ≤ gseq4 L H K M P u j :=
        fun h => hR (hfloor j hj h)
      have ha0' : u (j + 1) ≤ P - 4 →
          2 * K - P + 2 * H - 2 * M - 2 - u j ≤ gseq4 L H K M P u j :=
        fun h => hT (hdeep j hj h)
      have haK : K + 2 ≤ u (j + 1) → u j + 2 * K - P - 2 * M ≤ gseq4 L H K M P u j :=
        fun h => hS (hceil j hj h)
      have hnew : Val4 L H K M P (u (j + 1)) (gseq4 L H K M P u (j + 1)) := by
        rw [gseq4_succ]
        exact val4_gstepW hLP hPL hPK hKH hLM hMP hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p1, p2⟩ :=
        prog4_EW hLP hPL hPK hKH hLM hMP hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p3, p4, p5⟩ :=
        prog4_RW hLP hPL hPK hKH hLM hMP hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p6, p7, p8⟩ :=
        prog4_E2W hLP hPL hPK hKH hLM hMP hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p9, p10, p11⟩ :=
        prog4_SW hLP hPL hPK hKH hLM hMP hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p12, p13, p13'⟩ :=
        prog4_S2W hLP hPL hPK hKH hLM hMP hMK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
      obtain ⟨p14, p15, p16⟩ :=
        prog4_TW hLP hPL hPK hKH hLM hMP hMK hHK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK
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


/-- A legal greedy time sequence is a fold onto `leg4Walk`. -/
theorem foldsOnto_leg4W_of_val4 {m : ℕ} (f : Fin m → ℤ) (L H K M P : ℤ) (u : ℕ → ℤ)
    (hLP : L + 2 ≤ P) (hPK : P ≤ K) (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2)
    (hu : ∀ j : Fin m, u j.val = f j)
    (hval : ∀ j : Fin m, Val4 L H K M P (u j.val) (gseq4 L H K M P u j.val)) :
    FoldsOnto f (leg4Len L H K M P) (leg4Walk L H K M P) := by
  refine ⟨fun j => (gseq4 L H K M P u j.val).toNat, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro j
    obtain ⟨h1, h2⟩ := val4_boundsW hPK hKH hLP hLM hMP (hval j)
    simp only [leg4Len]
    omega
  · intro j j' hjj'
    obtain ⟨h1, h2⟩ := val4_boundsW hPK hKH hLP hLM hMP (hval j)
    obtain ⟨h3, h4⟩ := val4_boundsW hPK hKH hLP hLM hMP (hval j')
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
    exact val4_walkW hPK hKH hLP hLM hMP h

set_option maxHeartbeats 1000000 in
/-- **The four-leg fold.**  A 1-Lipschitz arm in `[L, H]` based at `P` folds onto
`leg4Walk L H K M P` as soon as its descents to `M - 1`, its descents to `M - 2` and its ascents
to `K + 2` are announced. -/
theorem foldsOnto_leg4W {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L H K M P : ℤ)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (h0lo : P - 1 ≤ f ⟨0, hm⟩) (h0hi : f ⟨0, hm⟩ ≤ P) (h0K : f ⟨0, hm⟩ ≤ K - 1) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hfloor : ∀ d : Fin m, f d ≤ P - 3 →
      (∃ k : Fin m, k.val < d.val ∧ K ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ P - 2 ∧ K - 1 ≤ f k'))
    (hdeep : ∀ d : Fin m, f d ≤ P - 4 →
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
  refine foldsOnto_leg4W_of_val4 f L H K M P u hLP hPK hKH hLM hMP hu ?_
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
  have key := gseq4_invW L H K M P u (m - 1) E R E2 S S2 T hLP hPL hPK hKH hLM hMP hMK hHK
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (key j.val (by have := j.isLt; omega)).1
  -- the base is at `P - 1` or `P`
  · have e : u 0 = f ⟨0, hm⟩ := by simpa using hu ⟨0, hm⟩
    rw [e]; exact h0lo
  · have e : u 0 = f ⟨0, hm⟩ := by simpa using hu ⟨0, hm⟩
    rw [e]; exact h0hi
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
    rw [this] at hkf; omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this] at hkf; omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this] at hkf; omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', -, -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this] at hkf; omega
    · omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this] at hkf; omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', -, -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this] at hkf; omega
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


/-! ## The reflection, and the walk the branch `L + 5` needs -/

/-- A fold of the reflected arm onto `leg4Walk` is a fold of the arm onto `leg4Walk'`. -/
theorem foldsOnto_leg4W_refl {m : ℕ} (f : Fin m → ℤ) (L H K M P : ℤ)
    (h : FoldsOnto (fun j => L + H - f j) (leg4Len L H K M P) (leg4Walk L H K M P)) :
    FoldsOnto f (leg4Len L H K M P) (leg4Walk' L H K M P) := by
  obtain ⟨β, h1, h2, h3, h4⟩ := h
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have hb := h4 j
  dsimp only at hb
  simp only [leg4Walk']
  rw [abs_le] at hb ⊢
  omega

/-- **The walk `L+5 → L+7 → L+3 → L+8 → L+1`.**  An arm based at `L + 5` or `L + 6` inside the band
`[L, L + 9]` folds onto it as soon as its descents to `L + 3`, its descents to `L + 2` and its
ascents to `L + 9` are announced. This is the walk the censuses of batches 53–55 need at the
basepoints of the branch `L + 5` that no walk of at most three turns serves. -/
theorem foldsOnto_walk5738 {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0lo : L + 5 ≤ f ⟨0, hm⟩) (h0hi : f ⟨0, hm⟩ ≤ L + 6)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hfloor : ∀ d : Fin m, f d ≤ L + 3 →
      (∃ k : Fin m, k.val < d.val ∧ L + 7 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 4 ∧ L + 6 ≤ f k'))
    (hdeep : ∀ d : Fin m, f d ≤ L + 2 →
      (∃ k : Fin m, k.val < d.val ∧ L + 9 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 2 ∧ L + 7 ≤ f k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        L + 8 ≤ f k ∧ f k' ≤ L + 3 ∧ L + 7 ≤ f k''))
    (hceil : ∀ d : Fin m, L + 9 ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ L + 2) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 8 ≤ f k ∧ f k' ≤ L + 4) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        f k ≤ L + 4 ∧ L + 7 ≤ f k' ∧ f k'' ≤ L + 4)) :
    FoldsOnto f (leg4Len L (L + 9) (L + 7) (L + 3) (L + 6))
      (leg4Walk L (L + 9) (L + 7) (L + 3) (L + 6)) := by
  refine foldsOnto_leg4W hm f hf L (L + 9) (L + 7) (L + 3) (L + 6) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hL hH ?_ ?_ ?_
  · intro d hd
    rcases hfloor d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr ⟨k, k', hkk', hk', by omega, by omega⟩
  · intro d hd
    rcases hdeep d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by omega, by omega, by omega⟩)
  · intro d hd
    rcases hceil d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by omega, by omega, by omega⟩)

/-- **The mirror walk `L+4 → L+3 → L+7 → L+1 → L+8`.**  It is the reflection of
`leg4Walk L (L + 9) (L + 6) (L + 2) (L + 6)`, so it is the walk of the engine at `K = P` (a first
leg of one step) and `M = P - 4` (a valley four below the base) — both outside the window of
`HPC/Fold/Leg4.lean`, both inside the window of this file.  An arm based at `L + 4` inside the band
`[L, L + 9]` folds onto it as soon as its ascents to `L + 6`, its ascents to `L + 7` and its
descents to `L + 1` are announced. -/
theorem foldsOnto_walk4371 {m : ℕ} (hm : 0 < m) (g : Fin m → ℤ) (hg : IsLip g) (L : ℤ)
    (h0 : g ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ g j) (hH : ∀ j, g j ≤ L + 9)
    (hup6 : ∀ d : Fin m, L + 6 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 3) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 5 ≤ g k ∧ g k' ≤ L + 4))
    (hup7 : ∀ d : Fin m, L + 7 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 1) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 8 ≤ g k ∧ g k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        g k ≤ L + 2 ∧ L + 7 ≤ g k' ∧ g k'' ≤ L + 2))
    (hdown1 : ∀ d : Fin m, g d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 8 ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ g k ≤ L + 2 ∧ L + 6 ≤ g k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        L + 5 ≤ g k ∧ g k' ≤ L + 3 ∧ L + 6 ≤ g k'')) :
    FoldsOnto g (leg4Len L (L + 9) (L + 6) (L + 2) (L + 6))
      (leg4Walk' L (L + 9) (L + 6) (L + 2) (L + 6)) := by
  set f : Fin m → ℤ := fun j => L + (L + 9) - g j with hfdef
  have hflip : IsLip f := by
    intro j j' hjj'
    have := hg j j' hjj'
    simp only [hfdef]
    rw [abs_le] at this ⊢
    omega
  refine foldsOnto_leg4W_refl g L (L + 9) (L + 6) (L + 2) (L + 6) ?_
  refine foldsOnto_leg4W hm f hflip L (L + 9) (L + 6) (L + 2) (L + 6) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [hfdef, h0]; ring_nf; omega) (by simp only [hfdef, h0]; ring_nf; omega)
    (by simp only [hfdef, h0]; ring_nf; omega)
    (fun j => by have := hH j; simp only [hfdef]; omega)
    (fun j => by have := hL j; simp only [hfdef]; omega) ?_ ?_ ?_
  -- floor, read at `P - 3 = L + 3`: the reflection of the ascents to `L + 6`
  · intro d hd
    have hgd : L + 6 ≤ g d := by simp only [hfdef] at hd; omega
    rcases hup6 d hgd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, hk, by simp only [hfdef]; omega⟩
    · exact Or.inr ⟨k, k', hkk', hk', by simp only [hfdef]; omega, by simp only [hfdef]; omega⟩
  -- deep floor, read at `P - 4 = L + 2`: the reflection of the ascents to `L + 7`
  · intro d hd
    have hgd : L + 7 ≤ g d := by simp only [hfdef] at hd; omega
    rcases hup7 d hgd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by simp only [hfdef]; omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by simp only [hfdef]; omega,
        by simp only [hfdef]; omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by simp only [hfdef]; omega,
        by simp only [hfdef]; omega, by simp only [hfdef]; omega⟩)
  -- ceiling: the reflection of the descents to `L + 1`
  · intro d hd
    have hgd : g d ≤ L + 1 := by simp only [hfdef] at hd; omega
    rcases hdown1 d hgd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by simp only [hfdef]; omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by simp only [hfdef]; omega,
        by simp only [hfdef]; omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by simp only [hfdef]; omega,
        by simp only [hfdef]; omega, by simp only [hfdef]; omega⟩)


end HPC.Fold
