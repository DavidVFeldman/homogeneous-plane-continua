import HPC.Fold.Leg4Wide
import HPC.Fold.Landmark

/-!
# An exact criterion for a four-leg walk

`foldsOnto_leg4W` (`HPC/Fold/Leg4Wide.lean`) is *sufficient* for an arm to fold onto
`leg4Walk L H K M P`, and batch 58 showed how far from necessary it is: there is a 175-link arm of
Bing's own chain that folds onto a walk of the family and meets the criterion of no parameter set
of the window (`not_leg4CritClosesL5`, `HPC/Fold/Audit58.lean`). For three legs the two halves met
(`foldsOnto_leg3deep_iff_landmark`), and the exactness was what made the branch `L + 4` decidable
arm by arm. This file supplies the missing exact criterion for four legs.

## The sentence

The walk `leg4Walk L H K M P` runs from `P - 1` up to the peak `K`, down to the valley `M`, up to
`H - 1`, and down to `L + 1`. Its three landmark positions are

```
A = K - P + 1        (level K, the peak)
B = 2K - P + 1 - M   (level M, the valley)
C = 2K - P + H - 2M  (level H - 1, the top of the third leg)
```

and the level `v` of a step of the arm is served, at the earliest, by the position

```
2K - P - v                 for v ≤ P - 3   (the second leg)
2K - P + 2H - 2M - 2 - v   for v ≤ M - 2   (the fourth leg)
v + 2K - P - 2M            for v ≥ K + 2   (the third leg)
```

`foldsOnto_landmark1`, `foldsOnto_landmark2` and `foldsOnto_landmark3` then read off, for each of
the three kinds of step, a chain of earlier steps of the arm at the landmark levels, with the index
gaps the walk's own positions dictate. That conjunction is `Leg4Land f H K M P`:

* **floor.** Before every descent to `P - 3` or below there is a time at `K - 1` or above, at index
  at least `A`, and at least `K - 1 - f d` steps earlier.
* **deep floor.** Before every descent to `M - 2` or below there are three times, in order, at
  `K - 1` or above, at `M + 1` or below and at `H - 2` or above, the first at index at least `A`,
  the gaps at least `K - M`, `H - 1 - M` and `H - 2 - f d`.
* **ceiling.** Before every ascent to `K + 2` or above there are two times, in order, at `K - 1` or
  above and at `M + 1` or below, the first at index at least `A`, the gaps at least `K - M` and
  `f d - M - 1`.

## The theorem

`foldsOnto_leg4_iff_leg4Land`: for a 1-Lipschitz arm of the band `[L, H]` whose first level is
within one of `P - 1`, folding onto `leg4Walk L H K M P` **is** the landmark sentence, at every
parameter set of the window of the wide engine. Necessity is the itinerary's intermediate value
theorem; sufficiency is the greedy of `HPC/Fold/Leg4.lean` run against a new invariant
(`gseq4_invLand`) whose bounds carry the *index* of the landmark as well as its level:

```
(1)                 q j ≥ min (j, u j - P + 2, A)
(2)   a ≤ j - n  →  q j ≥ min (A + n, 2K - P + 2 - u j, B)
(2')  a ≤ j      →  q j ≥ 2K - P - u j
(3)   b ≤ j - n  →  q j ≥ min (B + n, u j + 2K - P + 2 - 2M, C)
(3')  b ≤ j      →  q j ≥ u j + 2K - P - 2M
(4)   c ≤ j      →  q j ≥ 2K - P + 2H - 2M - 2 - u j
```

where `a`, `b`, `c` range over the landmark chains of the sentence. The two bounds carrying a time
credit `n` are what the index gaps of the sentence buy: the gap `K - M` of the sentence is exactly
`B - A`, so a valley landmark that far after a peak landmark puts the greedy at the valley
position `B`, and the gap `H - 1 - M` is exactly `C - B`.

The criterion of the engine is recovered as a corollary on its own window
(`leg4Land_of_leg4Crit` is not attempted; the engine remains available as `foldsOnto_leg4W`).
-/

namespace HPC.Fold

/-! ## The landmark sentence -/

/-- **The landmark sentence of the four-leg walk `leg4Walk L H K M P`.** -/
def Leg4Land {m : ℕ} (f : Fin m → ℤ) (H K M P : ℤ) : Prop :=
  (∀ d : Fin m, f d ≤ P - 3 →
      ∃ j : Fin m, K - P + 1 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + (K - 1 - f d) ≤ (d.val : ℤ) ∧
        K - 1 ≤ f j) ∧
  (∀ d : Fin m, f d ≤ M - 2 →
      ∃ j k l : Fin m, K - P + 1 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + (K - M) ≤ (k.val : ℤ) ∧
        (k.val : ℤ) + (H - 1 - M) ≤ (l.val : ℤ) ∧ (l.val : ℤ) + (H - 2 - f d) ≤ (d.val : ℤ) ∧
        K - 1 ≤ f j ∧ f k ≤ M + 1 ∧ H - 2 ≤ f l) ∧
  (∀ d : Fin m, K + 2 ≤ f d →
      ∃ j k : Fin m, K - P + 1 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + (K - M) ≤ (k.val : ℤ) ∧
        (k.val : ℤ) + (f d - M - 1) ≤ (d.val : ℤ) ∧ K - 1 ≤ f j ∧ f k ≤ M + 1)

/-! ## Three landmarks -/

/-- **Three landmarks.** The same as `foldsOnto_landmark2` with three landmarks
`q0 ≤ q1 ≤ q2` before the position `q3` that the arm's level at `d` forces. -/
theorem foldsOnto_landmark3 {m len : ℕ} {f : Fin m → ℤ} {c : ℕ → ℤ}
    (h : FoldsOnto f len c) (d : Fin m) (q0 q1 q2 q3 : ℕ) (h01 : q0 ≤ q1) (h12 : q1 ≤ q2)
    (h23 : q2 ≤ q3)
    (hd : ∀ p : ℕ, p < len → |f d - c p| ≤ 1 → q3 ≤ p) :
    ∃ j k l : Fin m, q0 ≤ j.val ∧ j.val + (q1 - q0) ≤ k.val ∧ k.val + (q2 - q1) ≤ l.val ∧
      l.val + (q3 - q2) ≤ d.val ∧ |f j - c q0| ≤ 1 ∧ |f k - c q1| ≤ 1 ∧ |f l - c q2| ≤ 1 := by
  obtain ⟨β, hlen, hs, hz, hval⟩ := h
  have hdm := d.isLt
  have hzm : 0 < m := by omega
  set z : Fin m := ⟨0, hzm⟩ with hzdef
  have hβz : β z = 0 := hz z rfl
  have hq3 : q3 ≤ β d := hd (β d) (hlen d) (hval d)
  obtain ⟨l, -, hld, hlβ⟩ :=
    beta_hits hs d.val d rfl q2 (by omega) z (by simp [hzdef]) (by omega)
  obtain ⟨k, -, hkl, hkβ⟩ :=
    beta_hits hs l.val l rfl q1 (by omega) z (by simp [hzdef]) (by omega)
  obtain ⟨j, -, hjk, hjβ⟩ :=
    beta_hits hs k.val k rfl q0 (by omega) z (by simp [hzdef]) (by omega)
  refine ⟨j, k, l, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := beta_le_val hz hs j.val j rfl
    omega
  · have := beta_dist hs (k.val - j.val) j k (by omega)
    push_cast at this
    omega
  · have := beta_dist hs (l.val - k.val) k l (by omega)
    push_cast at this
    omega
  · have := beta_dist hs (d.val - l.val) l d (by omega)
    push_cast at this
    omega
  · have := hval j
    rwa [hjβ] at this
  · have := hval k
    rwa [hkβ] at this
  · have := hval l
    rwa [hlβ] at this

/-! ## The positions of the four-leg walk -/

section Positions

variable {L H K M P : ℤ}

/-- The length of the four-leg walk, as an integer. -/
theorem leg4Len_cast (hPK : P ≤ K) (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M)
    (hMP : M ≤ P - 2) :
    ((leg4Len L H K M P : ℕ) : ℤ) = 2 * K - P + 2 * H - 2 * M - L - 1 := by
  simp only [leg4Len]
  omega

/-- The level of the peak landmark. -/
theorem leg4Walk_peak (hPK : P ≤ K) :
    leg4Walk L H K M P (K - P + 1).toNat = K := by
  have hc : (((K - P + 1).toNat : ℕ) : ℤ) = K - P + 1 := Int.toNat_of_nonneg (by omega)
  unfold leg4Walk
  rw [if_pos (by omega)]
  omega

/-- The level of the valley landmark. -/
theorem leg4Walk_valley (hPK : P ≤ K) (hMP : M ≤ P - 2) :
    leg4Walk L H K M P (2 * K - P + 1 - M).toNat = M := by
  have hc : (((2 * K - P + 1 - M).toNat : ℕ) : ℤ) = 2 * K - P + 1 - M :=
    Int.toNat_of_nonneg (by omega)
  unfold leg4Walk
  rw [if_neg (by omega), if_pos (by omega)]
  omega

/-- The level of the top landmark. -/
theorem leg4Walk_top (hPK : P ≤ K) (hKH : K ≤ H - 1) (hMP : M ≤ P - 2) :
    leg4Walk L H K M P (2 * K - P + H - 2 * M).toNat = H - 1 := by
  have hc : (((2 * K - P + H - 2 * M).toNat : ℕ) : ℤ) = 2 * K - P + H - 2 * M :=
    Int.toNat_of_nonneg (by omega)
  unfold leg4Walk
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  omega

/-- A descent to `P - 3` or below is served only by the second leg and later. -/
theorem leg4Walk_floor_pos {v : ℤ} {p : ℕ} (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hMP : M ≤ P - 2) (hv : v ≤ P - 3)
    (h : |v - leg4Walk L H K M P p| ≤ 1) : 2 * K - P - v ≤ (p : ℤ) := by
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
  rw [abs_le] at h
  unfold leg4Walk at h
  split_ifs at h <;> omega

/-- A descent to `M - 2` or below is served only by the fourth leg. -/
theorem leg4Walk_deep_pos {v : ℤ} {p : ℕ} (hMP : M ≤ P - 2) (hv : v ≤ M - 2)
    (h : |v - leg4Walk L H K M P p| ≤ 1) : 2 * K - P + 2 * H - 2 * M - 2 - v ≤ (p : ℤ) := by
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
  rw [abs_le] at h
  unfold leg4Walk at h
  split_ifs at h <;> omega

/-- An ascent to `K + 2` or above is served only by the third leg and later. -/
theorem leg4Walk_ceil_pos {v : ℤ} {p : ℕ} (hv : K + 2 ≤ v)
    (h : |v - leg4Walk L H K M P p| ≤ 1) : v + 2 * K - P - 2 * M ≤ (p : ℤ) := by
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
  rw [abs_le] at h
  unfold leg4Walk at h
  split_ifs at h <;> omega

end Positions

/-! ## Necessity -/

/-- **The landmark sentence is necessary.** An arm that folds onto `leg4Walk L H K M P`
satisfies it. -/
theorem leg4Land_of_foldsOnto {m : ℕ} {f : Fin m → ℤ} {L H K M P : ℤ}
    (hPK : P ≤ K) (hKH : K ≤ H - 1) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K)
    (h : FoldsOnto f (leg4Len L H K M P) (leg4Walk L H K M P)) :
    Leg4Land f H K M P := by
  have hA : (((K - P + 1).toNat : ℕ) : ℤ) = K - P + 1 := Int.toNat_of_nonneg (by omega)
  have hB : (((2 * K - P + 1 - M).toNat : ℕ) : ℤ) = 2 * K - P + 1 - M :=
    Int.toNat_of_nonneg (by omega)
  have hC : (((2 * K - P + H - 2 * M).toNat : ℕ) : ℤ) = 2 * K - P + H - 2 * M :=
    Int.toNat_of_nonneg (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    have hq : (((2 * K - P - f d).toNat : ℕ) : ℤ) = 2 * K - P - f d :=
      Int.toNat_of_nonneg (by omega)
    have hpos : ∀ p : ℕ, p < leg4Len L H K M P →
        |f d - leg4Walk L H K M P p| ≤ 1 → (2 * K - P - f d).toNat ≤ p := by
      intro p _ hpv
      have := leg4Walk_floor_pos (L := L) (H := H) (K := K) (M := M) (P := P)
        hPK hKH hMP hd hpv
      omega
    obtain ⟨j, hj0, hjd, hjv⟩ :=
      foldsOnto_landmark1 h d (K - P + 1).toNat (2 * K - P - f d).toNat (by omega) hpos
    rw [leg4Walk_peak hPK, abs_le] at hjv
    exact ⟨j, by omega, by
      have : ((j.val + ((2 * K - P - f d).toNat - (K - P + 1).toNat) : ℕ) : ℤ) ≤ (d.val : ℤ) := by
        exact_mod_cast Int.ofNat_le.mpr hjd
      push_cast at this
      omega, by omega⟩
  · intro d hd
    have hq : (((2 * K - P + 2 * H - 2 * M - 2 - f d).toNat : ℕ) : ℤ) =
        2 * K - P + 2 * H - 2 * M - 2 - f d := Int.toNat_of_nonneg (by omega)
    have hpos : ∀ p : ℕ, p < leg4Len L H K M P →
        |f d - leg4Walk L H K M P p| ≤ 1 →
        (2 * K - P + 2 * H - 2 * M - 2 - f d).toNat ≤ p := by
      intro p _ hpv
      have := leg4Walk_deep_pos (L := L) (H := H) (K := K) (M := M) (P := P) hMP hd hpv
      omega
    obtain ⟨j, k, l, hj0, hjk, hkl, hld, hjv, hkv, hlv⟩ :=
      foldsOnto_landmark3 h d (K - P + 1).toNat (2 * K - P + 1 - M).toNat
        (2 * K - P + H - 2 * M).toNat (2 * K - P + 2 * H - 2 * M - 2 - f d).toNat
        (by omega) (by omega) (by omega) hpos
    rw [leg4Walk_peak hPK, abs_le] at hjv
    rw [leg4Walk_valley hPK hMP, abs_le] at hkv
    rw [leg4Walk_top hPK hKH hMP, abs_le] at hlv
    have c1 : ((j.val + ((2 * K - P + 1 - M).toNat - (K - P + 1).toNat) : ℕ) : ℤ) ≤ (k.val : ℤ) :=
      by exact_mod_cast Int.ofNat_le.mpr hjk
    have c2 : ((k.val + ((2 * K - P + H - 2 * M).toNat - (2 * K - P + 1 - M).toNat) : ℕ) : ℤ) ≤
        (l.val : ℤ) := by exact_mod_cast Int.ofNat_le.mpr hkl
    have c3 : ((l.val + ((2 * K - P + 2 * H - 2 * M - 2 - f d).toNat -
        (2 * K - P + H - 2 * M).toNat) : ℕ) : ℤ) ≤ (d.val : ℤ) := by
      exact_mod_cast Int.ofNat_le.mpr hld
    push_cast at c1 c2 c3
    exact ⟨j, k, l, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro d hd
    have hq : (((f d + 2 * K - P - 2 * M).toNat : ℕ) : ℤ) = f d + 2 * K - P - 2 * M :=
      Int.toNat_of_nonneg (by omega)
    have hpos : ∀ p : ℕ, p < leg4Len L H K M P →
        |f d - leg4Walk L H K M P p| ≤ 1 → (f d + 2 * K - P - 2 * M).toNat ≤ p := by
      intro p _ hpv
      have := leg4Walk_ceil_pos (L := L) (H := H) (K := K) (M := M) (P := P) hd hpv
      omega
    obtain ⟨j, k, hj0, hjk, hkd, hjv, hkv⟩ :=
      foldsOnto_landmark2 h d (K - P + 1).toNat (2 * K - P + 1 - M).toNat
        (f d + 2 * K - P - 2 * M).toNat (by omega) (by omega) hpos
    rw [leg4Walk_peak hPK, abs_le] at hjv
    rw [leg4Walk_valley hPK hMP, abs_le] at hkv
    have c1 : ((j.val + ((2 * K - P + 1 - M).toNat - (K - P + 1).toNat) : ℕ) : ℤ) ≤ (k.val : ℤ) :=
      by exact_mod_cast Int.ofNat_le.mpr hjk
    have c2 : ((k.val + ((f d + 2 * K - P - 2 * M).toNat -
        (2 * K - P + 1 - M).toNat) : ℕ) : ℤ) ≤ (d.val : ℤ) := by
      exact_mod_cast Int.ofNat_le.mpr hkd
    push_cast at c1 c2
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-! ## Sufficiency: the progress clauses of the landmark invariant

Each clause says that one lower bound on the greedy time survives a step. The three hypotheses
`h0`, `h0'`, `hKq` are the same in every case — the bound the floor trigger supplies, the one the
deep trigger supplies, the one the ceiling trigger supplies — but the triggers are the walk's own,
at `P - 3`, `M - 2` and `K + 2`, where the engine of `HPC/Fold/Leg4Wide.lean` reads the second at
`P - 4`. Two of the bounds carry a *time credit* `w`, which is what the index gaps of the landmark
sentence buy; the credit is never below the position of the landmark it starts from, which is the
hypothesis `hw`. -/

section Progress

variable {L H K M P v q v' w : ℤ}

/-- A lower bound on the greedy step: when the step can advance it does, and otherwise the
position named is legal or already behind. -/
theorem gstep4_lower2 {b : ℤ} (hbq : b ≤ q + 1)
    (hb : ¬ Val4 L H K M P v' (q + 1) → (b ≤ q - 1 ∨ Val4 L H K M P v' b)) :
    b ≤ gstep4 L H K M P v' q := by
  by_cases c1 : Val4 L H K M P v' (q + 1)
  · unfold gstep4; rw [if_pos c1]; omega
  · exact gstep4_lower hbq (hb c1)

set_option maxHeartbeats 1000000 in
/-- **The step keeps the greedy time legal**, under the three announcements read at the walk's own
trigger levels. -/
theorem val4_gstepLand
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q)
    :
    Val4 L H K M P v' (gstep4 L H K M P v' q) := by
  refine val4_gstep_of ?_
  by_cases c1 : Val4 L H K M P v' (q + 1)
  · exact Or.inl c1
  by_cases c2 : Val4 L H K M P v' q
  · exact Or.inr (Or.inl c2)
  refine Or.inr (Or.inr ?_)
  unfold Val4 at hval c1 c2 ⊢
  push_neg at c1 c2
  rcases le_or_gt v' (M - 2) with hd | hd
  · have hq1 := h0 (by omega)
    have hq2 := h0' hd
    rcases hval with h | h | h | h <;> omega
  · rcases le_or_gt v' (P - 3) with hf | hf
    · have hq1 := h0 hf
      rcases hval with h | h | h | h <;> omega
    · rcases le_or_gt (K + 2) v' with hc | hc
      · have hq3 := hKq hc
        rcases hval with h | h | h | h <;> omega
      · rcases hval with h | h | h | h <;> omega

set_option maxHeartbeats 1000000 in
/-- **The first leg**, tracked against the step index. -/
theorem progLand_1 {j : ℤ}
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q)
    (hqj : q ≤ j)
    (hb : min (min j (v - P + 2)) (K - P + 1) ≤ q) :
    min (min (j + 1) (v' - P + 2)) (K - P + 1) ≤ gstep4 L H K M P v' q := by
  refine gstep4_lower2 (by unfold Val4 at hval; omega) ?_
  intro c1
  unfold Val4 at hval c1 ⊢
  push_neg at c1
  rcases le_or_gt v' (M - 2) with hd | hd
  · have hq1 := h0 (by omega)
    have hq2 := h0' hd
    rcases hval with h | h | h | h <;> omega
  · rcases le_or_gt v' (P - 3) with hf | hf
    · have hq1 := h0 hf
      rcases hval with h | h | h | h <;> omega
    · rcases le_or_gt (K + 2) v' with hc | hc
      · have hq3 := hKq hc
        rcases hval with h | h | h | h <;> omega
      · rcases hval with h | h | h | h <;> omega

set_option maxHeartbeats 1000000 in
/-- **The second leg**, with the time credit. -/
theorem progLand_2
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q)
    (hw : K - P + 1 ≤ w)
    (hb : min (min w (2 * K - P + 2 - v)) (2 * K - P + 1 - M) ≤ q) :
    min (min (w + 1) (2 * K - P + 2 - v')) (2 * K - P + 1 - M) ≤ gstep4 L H K M P v' q := by
  refine gstep4_lower2 (by unfold Val4 at hval; omega) ?_
  intro c1
  unfold Val4 at hval c1 ⊢
  push_neg at c1
  rcases le_or_gt v' (M - 2) with hd | hd
  · have hq1 := h0 (by omega)
    have hq2 := h0' hd
    rcases hval with h | h | h | h <;> omega
  · rcases le_or_gt v' (P - 3) with hf | hf
    · have hq1 := h0 hf
      rcases hval with h | h | h | h <;> omega
    · rcases le_or_gt (K + 2) v' with hc | hc
      · have hq3 := hKq hc
        rcases hval with h | h | h | h <;> omega
      · rcases hval with h | h | h | h <;> omega

set_option maxHeartbeats 1000000 in
/-- **The second leg**, tracked at the near end. -/
theorem progLand_2'
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q)
    (hb : 2 * K - P - v ≤ q) :
    2 * K - P - v' ≤ gstep4 L H K M P v' q := by
  refine gstep4_lower2 (by unfold Val4 at hval; omega) ?_
  intro c1
  unfold Val4 at hval c1 ⊢
  push_neg at c1
  rcases le_or_gt v' (M - 2) with hd | hd
  · have hq1 := h0 (by omega)
    have hq2 := h0' hd
    rcases hval with h | h | h | h <;> omega
  · rcases le_or_gt v' (P - 3) with hf | hf
    · have hq1 := h0 hf
      rcases hval with h | h | h | h <;> omega
    · rcases le_or_gt (K + 2) v' with hc | hc
      · have hq3 := hKq hc
        rcases hval with h | h | h | h <;> omega
      · rcases hval with h | h | h | h <;> omega

set_option maxHeartbeats 1000000 in
/-- **The third leg**, with the time credit. -/
theorem progLand_3
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q)
    (hw : 2 * K - P + 1 - M ≤ w)
    (hb : min (min w (v + 2 * K - P + 2 - 2 * M)) (2 * K - P + H - 2 * M) ≤ q) :
    min (min (w + 1) (v' + 2 * K - P + 2 - 2 * M)) (2 * K - P + H - 2 * M) ≤
      gstep4 L H K M P v' q := by
  refine gstep4_lower2 (by unfold Val4 at hval; omega) ?_
  intro c1
  unfold Val4 at hval c1 ⊢
  push_neg at c1
  rcases le_or_gt v' (M - 2) with hd | hd
  · have hq1 := h0 (by omega)
    have hq2 := h0' hd
    rcases hval with h | h | h | h <;> omega
  · rcases le_or_gt v' (P - 3) with hf | hf
    · have hq1 := h0 hf
      rcases hval with h | h | h | h <;> omega
    · rcases le_or_gt (K + 2) v' with hc | hc
      · have hq3 := hKq hc
        rcases hval with h | h | h | h <;> omega
      · rcases hval with h | h | h | h <;> omega

set_option maxHeartbeats 1000000 in
/-- **The third leg**, tracked at the near end. -/
theorem progLand_3'
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hv0 : L ≤ v) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q)
    (hb : v + 2 * K - P - 2 * M ≤ q) :
    v' + 2 * K - P - 2 * M ≤ gstep4 L H K M P v' q := by
  refine gstep4_lower2 (by unfold Val4 at hval; omega) ?_
  intro c1
  unfold Val4 at hval c1 ⊢
  push_neg at c1
  rcases le_or_gt v' (M - 2) with hd | hd
  · have hq1 := h0 (by omega)
    have hq2 := h0' hd
    rcases hval with h | h | h | h <;> omega
  · rcases le_or_gt v' (P - 3) with hf | hf
    · have hq1 := h0 hf
      rcases hval with h | h | h | h <;> omega
    · rcases le_or_gt (K + 2) v' with hc | hc
      · have hq3 := hKq hc
        rcases hval with h | h | h | h <;> omega
      · rcases hval with h | h | h | h <;> omega

set_option maxHeartbeats 1000000 in
/-- **The last leg.** -/
theorem progLand_4
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val4 L H K M P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q)
    (h0' : v' ≤ M - 2 → 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q)
    (hKq : K + 2 ≤ v' → v + 2 * K - P - 2 * M ≤ q)
    (hb : 2 * K - P + 2 * H - 2 * M - 2 - v ≤ q) :
    2 * K - P + 2 * H - 2 * M - 2 - v' ≤ gstep4 L H K M P v' q := by
  refine gstep4_lower2 (by unfold Val4 at hval; omega) ?_
  intro c1
  unfold Val4 at hval c1 ⊢
  push_neg at c1
  rcases le_or_gt v' (M - 2) with hd | hd
  · have hq1 := h0 (by omega)
    have hq2 := h0' hd
    rcases hval with h | h | h | h <;> omega
  · rcases le_or_gt v' (P - 3) with hf | hf
    · have hq1 := h0 hf
      rcases hval with h | h | h | h <;> omega
    · rcases le_or_gt (K + 2) v' with hc | hc
      · have hq3 := hKq hc
        rcases hval with h | h | h | h <;> omega
      · rcases hval with h | h | h | h <;> omega

end Progress

/-! ## The invariant -/

/-- The greedy time never runs ahead of the step index. -/
theorem gseq4_le_index (L H K M P : ℤ) (u : ℕ → ℤ) :
    ∀ j : ℕ, gseq4 L H K M P u j ≤ (j : ℤ) := by
  intro j
  induction j with
  | zero => rw [gseq4_zero]; simp
  | succ j ih =>
      rw [gseq4_succ]
      have := (gstep4_dist L H K M P (u (j + 1)) (gseq4 L H K M P u j)).2
      push_cast
      omega

set_option maxHeartbeats 1000000 in
/-- **The landmark invariant.** A level sequence based within one of `P - 1` inside `[L, H]` whose
descents to `P - 3`, descents to `M - 2` and ascents to `K + 2` are announced by landmark chains
keeps the greedy time legal; the six bounds are the ones the chains earn. -/
theorem gseq4_invLand (L H K M P : ℤ) (u : ℕ → ℤ) (N : ℕ)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (hu0 : P - 2 ≤ u 0) (hu0' : u 0 ≤ P)
    (hlo : ∀ j, j ≤ N → L ≤ u j) (hhi : ∀ j, j ≤ N → u j ≤ H)
    (hlip : ∀ j, j + 1 ≤ N → u j - 1 ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1)
    (hfloor : ∀ j, j + 1 ≤ N → u (j + 1) ≤ P - 3 → ∃ a : ℕ,
      K - P + 1 ≤ (a : ℤ) ∧ K - 1 ≤ u a ∧ (a : ℤ) + (K - 1 - u (j + 1)) ≤ ((j : ℤ) + 1))
    (hdeep : ∀ j, j + 1 ≤ N → u (j + 1) ≤ M - 2 → ∃ a b c : ℕ,
      K - P + 1 ≤ (a : ℤ) ∧ K - 1 ≤ u a ∧ (a : ℤ) + (K - M) ≤ (b : ℤ) ∧ u b ≤ M + 1 ∧
      (b : ℤ) + (H - 1 - M) ≤ (c : ℤ) ∧ H - 2 ≤ u c ∧
      (c : ℤ) + (H - 2 - u (j + 1)) ≤ ((j : ℤ) + 1))
    (hceil : ∀ j, j + 1 ≤ N → K + 2 ≤ u (j + 1) → ∃ a b : ℕ,
      K - P + 1 ≤ (a : ℤ) ∧ K - 1 ≤ u a ∧ (a : ℤ) + (K - M) ≤ (b : ℤ) ∧ u b ≤ M + 1 ∧
      (b : ℤ) + (u (j + 1) - M - 1) ≤ ((j : ℤ) + 1)) :
    ∀ j, j ≤ N →
      Val4 L H K M P (u j) (gseq4 L H K M P u j) ∧
      (min (min (j : ℤ) (u j - P + 2)) (K - P + 1) ≤ gseq4 L H K M P u j) ∧
      (∀ a n : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → a + n ≤ j →
        min (min (K - P + 1 + (n : ℤ)) (2 * K - P + 2 - u j)) (2 * K - P + 1 - M) ≤
          gseq4 L H K M P u j) ∧
      (∀ a : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → a ≤ j →
        2 * K - P - u j ≤ gseq4 L H K M P u j) ∧
      (∀ a b n : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → (a : ℤ) + (K - M) ≤ (b : ℤ) →
        u b ≤ M + 1 → b + n ≤ j →
        min (min (2 * K - P + 1 - M + (n : ℤ)) (u j + 2 * K - P + 2 - 2 * M))
          (2 * K - P + H - 2 * M) ≤ gseq4 L H K M P u j) ∧
      (∀ a b : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → (a : ℤ) + (K - M) ≤ (b : ℤ) →
        u b ≤ M + 1 → b ≤ j → u j + 2 * K - P - 2 * M ≤ gseq4 L H K M P u j) ∧
      (∀ a b c : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → (a : ℤ) + (K - M) ≤ (b : ℤ) →
        u b ≤ M + 1 → (b : ℤ) + (H - 1 - M) ≤ (c : ℤ) → H - 2 ≤ u c → c ≤ j →
        2 * K - P + 2 * H - 2 * M - 2 - u j ≤ gseq4 L H K M P u j) := by
  intro j
  induction j with
  | zero =>
      intro _
      have hz : gseq4 L H K M P u 0 = 0 := gseq4_zero L H K M P u
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hz]; unfold Val4; omega
      · rw [hz]; push_cast; omega
      · intro a n ha _ hle
        have ha0 : ((a : ℕ) : ℤ) = 0 := by
          have : a = 0 := by omega
          simp [this]
        omega
      · intro a ha _ hle
        have ha0 : ((a : ℕ) : ℤ) = 0 := by
          have : a = 0 := by omega
          simp [this]
        omega
      · intro a b n ha _ hab _ hle
        have ha0 : ((a : ℕ) : ℤ) = 0 := by
          have : a = 0 := by omega
          simp [this]
        have hb0 : ((b : ℕ) : ℤ) = 0 := by
          have : b = 0 := by omega
          simp [this]
        omega
      · intro a b ha _ hab _ hle
        have ha0 : ((a : ℕ) : ℤ) = 0 := by
          have : a = 0 := by omega
          simp [this]
        have hb0 : ((b : ℕ) : ℤ) = 0 := by
          have : b = 0 := by omega
          simp [this]
        omega
      · intro a b c ha _ hab _ hbc _ hle
        have ha0 : ((a : ℕ) : ℤ) = 0 := by
          have : a = 0 := by omega
          simp [this]
        have hb0 : ((b : ℕ) : ℤ) = 0 := by
          have : b = 0 := by omega
          simp [this]
        have hc0 : ((c : ℕ) : ℤ) = 0 := by
          have : c = 0 := by omega
          simp [this]
        omega
  | succ j ih =>
      intro hj
      obtain ⟨hval, ihB1, ihB2, ihB2', ihB3, ihB3', ihB4⟩ := ih (by omega)
      have hv0 := hlo j (by omega)
      have hvH := hhi j (by omega)
      have hv'0 := hlo (j + 1) hj
      have hv'H := hhi (j + 1) hj
      obtain ⟨hl1, hl2⟩ := hlip j hj
      have hqj : gseq4 L H K M P u j ≤ (j : ℤ) := gseq4_le_index L H K M P u j
      -- the three bounds the announcements supply
      have ha0 : u (j + 1) ≤ P - 3 → 2 * K - P - u j ≤ gseq4 L H K M P u j := by
        intro hv
        obtain ⟨a, ha1, ha2, ha3⟩ := hfloor j hj hv
        exact ihB2' a ha1 ha2 (by omega)
      have ha0' : u (j + 1) ≤ M - 2 →
          2 * K - P + 2 * H - 2 * M - 2 - u j ≤ gseq4 L H K M P u j := by
        intro hv
        obtain ⟨a, b, c, ha1, ha2, hab, hb2, hbc, hc2, hc3⟩ := hdeep j hj hv
        exact ihB4 a b c ha1 ha2 hab hb2 hbc hc2 (by omega)
      have haK : K + 2 ≤ u (j + 1) → u j + 2 * K - P - 2 * M ≤ gseq4 L H K M P u j := by
        intro hv
        obtain ⟨a, b, ha1, ha2, hab, hb2, hb3⟩ := hceil j hj hv
        exact ihB3' a b ha1 ha2 hab hb2 (by omega)
      -- legality
      have hnew : Val4 L H K M P (u (j + 1)) (gseq4 L H K M P u (j + 1)) := by
        rw [gseq4_succ]
        exact val4_gstepLand hLP hPL hPK hKH hLM hMP hMK hHK hv0 hvH hv'0 hv'H hl1 hl2 hval
          ha0 ha0' haK
      -- the first-leg bound
      have hB1 : min (min ((j : ℤ) + 1) (u (j + 1) - P + 2)) (K - P + 1) ≤
          gseq4 L H K M P u (j + 1) := by
        rw [gseq4_succ]
        exact progLand_1 hLP hPL hPK hKH hLM hMP hMK hHK hv0 hvH hv'0 hv'H hl1 hl2 hval
          ha0 ha0' haK hqj ihB1
      -- the second-leg bound with the credit
      have hB2 : ∀ a n : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → a + n ≤ j + 1 →
          min (min (K - P + 1 + (n : ℤ)) (2 * K - P + 2 - u (j + 1))) (2 * K - P + 1 - M) ≤
            gseq4 L H K M P u (j + 1) := by
        intro a n ha1 ha2 hle
        rcases Nat.lt_or_ge (a + n) (j + 1) with hlt | hge
        · rw [gseq4_succ]
          have := ihB2 a n ha1 ha2 (by omega)
          have hh := progLand_2 (w := K - P + 1 + (n : ℤ)) hLP hPL hPK hKH hLM hMP hMK hHK
            hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK (by omega) (by omega)
          omega
        · rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            have : a = j + 1 := by omega
            subst this
            push_cast
            push_cast at hB1 ha1
            omega
          · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            rw [gseq4_succ]
            have := ihB2 a n' ha1 ha2 (by omega)
            have hh := progLand_2 (w := K - P + 1 + (n' : ℤ)) hLP hPL hPK hKH hLM hMP hMK hHK
              hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK (by omega) (by omega)
            push_cast
            push_cast at hh
            omega
      -- the second-leg bound at the near end
      have hB2' : ∀ a : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → a ≤ j + 1 →
          2 * K - P - u (j + 1) ≤ gseq4 L H K M P u (j + 1) := by
        intro a ha1 ha2 hle
        rcases Nat.lt_or_ge a (j + 1) with hlt | hge
        · rw [gseq4_succ]
          exact progLand_2' hLP hPL hPK hKH hLM hMP hMK hHK hvH hv'0 hv'H hl1 hl2 hval
            ha0 ha0' haK (ihB2' a ha1 ha2 (by omega))
        · have : a = j + 1 := by omega
          subst this
          push_cast at hB1 ha1 ⊢
          omega
      -- the third-leg bound with the credit
      have hB3 : ∀ a b n : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → (a : ℤ) + (K - M) ≤ (b : ℤ) →
          u b ≤ M + 1 → b + n ≤ j + 1 →
          min (min (2 * K - P + 1 - M + (n : ℤ)) (u (j + 1) + 2 * K - P + 2 - 2 * M))
            (2 * K - P + H - 2 * M) ≤ gseq4 L H K M P u (j + 1) := by
        intro a b n ha1 ha2 hab hb2 hle
        rcases Nat.lt_or_ge (b + n) (j + 1) with hlt | hge
        · rw [gseq4_succ]
          have := ihB3 a b n ha1 ha2 hab hb2 (by omega)
          have hh := progLand_3 (w := 2 * K - P + 1 - M + (n : ℤ)) hLP hPL hPK hKH hLM hMP hMK
            hHK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK (by omega) (by omega)
          omega
        · rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            have hbj : b = j + 1 := by omega
            subst hbj
            have hcast : (((K - M).toNat : ℕ) : ℤ) = K - M := Int.toNat_of_nonneg (by omega)
            have := hB2 a (K - M).toNat ha1 ha2 (by omega)
            push_cast at this ⊢
            omega
          · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            rw [gseq4_succ]
            have := ihB3 a b n' ha1 ha2 hab hb2 (by omega)
            have hh := progLand_3 (w := 2 * K - P + 1 - M + (n' : ℤ)) hLP hPL hPK hKH hLM hMP hMK
              hHK hv0 hvH hv'0 hv'H hl1 hl2 hval ha0 ha0' haK (by omega) (by omega)
            push_cast
            push_cast at hh
            omega
      -- the third-leg bound at the near end
      have hB3' : ∀ a b : ℕ, K - P + 1 ≤ (a : ℤ) → K - 1 ≤ u a → (a : ℤ) + (K - M) ≤ (b : ℤ) →
          u b ≤ M + 1 → b ≤ j + 1 →
          u (j + 1) + 2 * K - P - 2 * M ≤ gseq4 L H K M P u (j + 1) := by
        intro a b ha1 ha2 hab hb2 hle
        rcases Nat.lt_or_ge b (j + 1) with hlt | hge
        · rw [gseq4_succ]
          exact progLand_3' hLP hPL hPK hKH hLM hMP hMK hHK hv0 hv'0 hv'H hl1 hl2 hval
            ha0 ha0' haK (ihB3' a b ha1 ha2 hab hb2 (by omega))
        · have hbj : b = j + 1 := by omega
          subst hbj
          have hcast : (((K - M).toNat : ℕ) : ℤ) = K - M := Int.toNat_of_nonneg (by omega)
          have := hB2 a (K - M).toNat ha1 ha2 (by omega)
          push_cast at this ⊢
          omega
      refine ⟨hnew, ?_, hB2, hB2', hB3, hB3', ?_⟩
      · push_cast
        push_cast at hB1
        omega
      · intro a b c ha1 ha2 hab hb2 hbc hc2 hle
        rcases Nat.lt_or_ge c (j + 1) with hlt | hge
        · rw [gseq4_succ]
          exact progLand_4 hLP hPL hPK hKH hLM hMP hMK hHK hv'0 hv'H hl1 hl2 hval
            ha0 ha0' haK (ihB4 a b c ha1 ha2 hab hb2 hbc hc2 (by omega))
        · have hcj : c = j + 1 := by omega
          subst hcj
          have hcast : (((H - 1 - M).toNat : ℕ) : ℤ) = H - 1 - M := Int.toNat_of_nonneg (by omega)
          have := hB3 a b (H - 1 - M).toNat ha1 ha2 hab hb2 (by omega)
          push_cast at this ⊢
          omega

/-! ## The exact criterion -/

set_option maxHeartbeats 1000000 in
/-- **The landmark sentence is sufficient.** A 1-Lipschitz arm of the band `[L, H]` whose first
level is within one of `P - 1` and which satisfies `Leg4Land` folds onto `leg4Walk L H K M P`. -/
theorem foldsOnto_leg4_of_leg4Land {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L H K M P : ℤ) (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (h0lo : P - 2 ≤ f ⟨0, hm⟩) (h0hi : f ⟨0, hm⟩ ≤ P)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hland : Leg4Land f H K M P) :
    FoldsOnto f (leg4Len L H K M P) (leg4Walk L H K M P) := by
  classical
  obtain ⟨hfl, hdp, hcl⟩ := hland
  set u : ℕ → ℤ := fun k => if h : k < m then f ⟨k, h⟩ else P with hudef
  have hu : ∀ j : Fin m, u j.val = f j := by
    intro j
    simp only [hudef, j.isLt, dif_pos]
  have hufin : ∀ (k : ℕ) (hk : k < m), u k = f ⟨k, hk⟩ := by
    intro k hk
    simpa using hu ⟨k, hk⟩
  refine foldsOnto_leg4W_of_val4 f L H K M P u hLP hPK hKH hLM hMP hu ?_
  have key := gseq4_invLand L H K M P u (m - 1) hLP hPL hPK hKH hLM hMP hMK hHK
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (key j.val (by have := j.isLt; omega)).1
  · rw [hufin 0 hm]; exact h0lo
  · rw [hufin 0 hm]; exact h0hi
  · intro j hj
    have hjm : j < m := by omega
    rw [hufin j hjm]
    exact hL _
  · intro j hj
    have hjm : j < m := by omega
    rw [hufin j hjm]
    exact hH _
  · intro j hj
    have hjm : j < m := by omega
    have hj1m : j + 1 < m := by omega
    have := hf ⟨j, hjm⟩ ⟨j + 1, hj1m⟩ rfl
    rw [abs_le] at this
    rw [hufin j hjm, hufin (j + 1) hj1m]
    omega
  · intro j hj hv
    have hj1m : j + 1 < m := by omega
    rw [hufin (j + 1) hj1m] at hv ⊢
    obtain ⟨a, ha1, ha3, ha2⟩ := hfl ⟨j + 1, hj1m⟩ hv
    refine ⟨a.val, ha1, ?_, ?_⟩
    · rw [hufin a.val a.isLt]
      exact ha2
    · push_cast at ha3 ⊢
      omega
  · intro j hj hv
    have hj1m : j + 1 < m := by omega
    rw [hufin (j + 1) hj1m] at hv ⊢
    obtain ⟨a, b, c, ha1, hab, hbc, hcd, ha2, hb2, hc2⟩ := hdp ⟨j + 1, hj1m⟩ hv
    refine ⟨a.val, b.val, c.val, ha1, ?_, hab, ?_, hbc, ?_, ?_⟩
    · rw [hufin a.val a.isLt]; exact ha2
    · rw [hufin b.val b.isLt]; exact hb2
    · rw [hufin c.val c.isLt]; exact hc2
    · push_cast at hcd ⊢
      omega
  · intro j hj hv
    have hj1m : j + 1 < m := by omega
    rw [hufin (j + 1) hj1m] at hv ⊢
    obtain ⟨a, b, ha1, hab, hbd, ha2, hb2⟩ := hcl ⟨j + 1, hj1m⟩ hv
    refine ⟨a.val, b.val, ha1, ?_, hab, ?_, ?_⟩
    · rw [hufin a.val a.isLt]; exact ha2
    · rw [hufin b.val b.isLt]; exact hb2
    · push_cast at hbd ⊢
      omega

/-- **The criterion of a four-leg walk is exact.** For a 1-Lipschitz arm of the band `[L, H]`
whose first level is within one of the walk's first level `P - 1`, folding onto
`leg4Walk L H K M P` is *equivalent* to the landmark sentence, at every parameter set of the
window of the wide engine. This is for four legs what `foldsOnto_leg3deep_iff_landmark` is for
three. -/
theorem foldsOnto_leg4_iff_leg4Land {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L H K M P : ℤ) (hLP : L + 2 ≤ P) (hPL : P ≤ L + 6) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) (hMK : M + 3 ≤ K) (hHK : H ≤ K + 3)
    (h0lo : P - 2 ≤ f ⟨0, hm⟩) (h0hi : f ⟨0, hm⟩ ≤ P)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) :
    FoldsOnto f (leg4Len L H K M P) (leg4Walk L H K M P) ↔ Leg4Land f H K M P :=
  ⟨fun h => leg4Land_of_foldsOnto hPK hKH hMP hMK h,
   fun h => foldsOnto_leg4_of_leg4Land hm f hf L H K M P hLP hPL hPK hKH hLM hMP hMK hHK
     h0lo h0hi hL hH h⟩

end HPC.Fold
