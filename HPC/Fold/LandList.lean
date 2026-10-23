import HPC.Fold.LandmarkChain
import HPC.Fold.Leg4Land

/-!
# A walk as a list of levels, and its landmark sentence

Question 3 of the batch-61 commission asks for the statement of the landmark sentence in general:
*a walk as a list of turning levels, the sentence as a conjunction over its legs*. This file is
that statement, together with the half of it that is a theorem.

## The walk

`walkList s ts` is the walk that starts at the level `s` and turns, in order, at the levels of the
list `ts`, moving one level per time between turns; `walkLen s ts` is its number of times,
`walkStop s ts k` the time of its `k`-th turn (`walkStop s ts 0 = 0`, the start) and
`walkLevel s ts k` the level there. The four-leg walk of the engine is the case of four turning
levels (`leg4Walk_eq_walkList`).

## The sentence

`LandWalk f s ts` is the conjunction, over the turns `r` of the walk, of

> whenever the arm's level at a time `d` is served **only** by the walk's times `walkStop s ts r`
> and later, there are times `j 0 ≤ ⋯ ≤ j r = d` of the arm at which it is within one of the
> levels `walkLevel s ts u`, with every gap `j (u+1) - j u` at least the walk's own gap
> `walkStop s ts (u+1) - walkStop s ts u`.

For four turning levels this is `Leg4Land` clause by clause: the three clauses of `Leg4Land` are
the cases `r = 1, 2, 3` read at the three trigger levels, with the earliest serving time computed
by `leg4Walk_floor_pos`, `leg4Walk_deep_pos` and `leg4Walk_ceil_pos`.

## What is proved

`landWalk_of_foldsOnto`: **the sentence is necessary for a walk of any shape**, immediately from
`foldsOnto_landmarkN` (`HPC/Fold/LandmarkChain.lean`) — the walk's turn times are an increasing
chain of positions, and that is all the chain theorem needs. Sufficiency — the invariant of
`gseq4_invLand` with two bounds per interior leg — is not proved here and is the open half.
-/

namespace HPC.Fold

/-! ## The walk of a list of levels -/

/-- **The walk through a list of turning levels.** From `s`, one level per time, turning at each
level of `ts` in turn; after the last turn it stands still. -/
def walkList : ℤ → List ℤ → ℕ → ℤ
  | s, [], _ => s
  | s, t :: ts, p =>
      if p < (t - s).natAbs then s + (if s ≤ t then (p : ℤ) else -(p : ℤ))
      else walkList t ts (p - (t - s).natAbs)

/-- The number of times of `walkList s ts`. -/
def walkLen : ℤ → List ℤ → ℕ
  | _, [] => 1
  | s, t :: ts => (t - s).natAbs + walkLen t ts

/-- The time of the `k`-th turn of `walkList s ts`; `k = 0` is the start. Beyond the last turn it
is the time of the last turn. -/
def walkStop : ℤ → List ℤ → ℕ → ℕ
  | _, [], _ => 0
  | _, _ :: _, 0 => 0
  | s, t :: ts, (k + 1) => (t - s).natAbs + walkStop t ts k

/-- The level of the `k`-th turn of `walkList s ts`. -/
def walkLevel : ℤ → List ℤ → ℕ → ℤ
  | s, [], _ => s
  | s, _ :: _, 0 => s
  | _, t :: ts, (k + 1) => walkLevel t ts k

@[simp] theorem walkList_nil (s : ℤ) (p : ℕ) : walkList s [] p = s := rfl

theorem walkList_cons_lt {s t : ℤ} {ts : List ℤ} {p : ℕ} (h : p < (t - s).natAbs) :
    walkList s (t :: ts) p = s + (if s ≤ t then (p : ℤ) else -(p : ℤ)) := by
  rw [walkList, if_pos h]

theorem walkList_cons_ge {s t : ℤ} {ts : List ℤ} {p : ℕ} (h : (t - s).natAbs ≤ p) :
    walkList s (t :: ts) p = walkList t ts (p - (t - s).natAbs) := by
  rw [walkList, if_neg (by omega)]

/-- The walk starts where it is told to. -/
@[simp] theorem walkList_zero (s : ℤ) (ts : List ℤ) : walkList s ts 0 = s := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      by_cases h : 0 < (t - s).natAbs
      · rw [walkList_cons_lt h]; simp
      · have hts : t = s := by omega
        rw [walkList_cons_ge (by omega), Nat.zero_sub, ih, hts]

/-- The turn times increase. -/
theorem walkStop_mono (s : ℤ) (ts : List ℤ) (k : ℕ) :
    walkStop s ts k ≤ walkStop s ts (k + 1) := by
  induction ts generalizing s k with
  | nil => simp [walkStop]
  | cons t ts ih =>
      cases k with
      | zero => simp [walkStop]
      | succ k => simpa [walkStop] using ih t k

/-- **The walk is at the `k`-th turning level at the `k`-th turn time.** -/
theorem walkList_walkStop (s : ℤ) (ts : List ℤ) (k : ℕ) :
    walkList s ts (walkStop s ts k) = walkLevel s ts k := by
  induction ts generalizing s k with
  | nil => rfl
  | cons t ts ih =>
      cases k with
      | zero => simpa [walkStop, walkLevel] using walkList_zero s (t :: ts)
      | succ k =>
          have : walkStop s (t :: ts) (k + 1) = (t - s).natAbs + walkStop t ts k := rfl
          rw [this, walkList_cons_ge (by omega)]
          simpa [walkLevel] using ih t k

/-- **The walk moves by at most one level per time.** -/
theorem walkList_step (s : ℤ) (ts : List ℤ) (p : ℕ) :
    |walkList s ts (p + 1) - walkList s ts p| ≤ 1 := by
  induction ts generalizing s p with
  | nil => simp
  | cons t ts ih =>
      rcases Nat.lt_or_ge (p + 1) (t - s).natAbs with h | h
      · rw [walkList_cons_lt h, walkList_cons_lt (by omega)]
        split_ifs <;> (rw [abs_le]; push_cast; omega)
      · rcases Nat.lt_or_ge p (t - s).natAbs with h' | h'
        · -- the step crosses the turn
          have hp : p + 1 = (t - s).natAbs := by omega
          rw [walkList_cons_ge (by omega), walkList_cons_lt h', hp]
          simp only [Nat.sub_self, walkList_zero]
          split_ifs <;> (rw [abs_le]; push_cast; omega)
        · rw [walkList_cons_ge (by omega), walkList_cons_ge h']
          have : p + 1 - (t - s).natAbs = (p - (t - s).natAbs) + 1 := by omega
          rw [this]
          exact ih t (p - (t - s).natAbs)

/-! ## The landmark sentence of a walk of any shape -/

/-- **The landmark sentence of the walk `walkList s ts`.** For every turn `r` of the walk: if the
arm's level at a time `d` is served only by the walk's times `walkStop s ts r` and later, then the
arm passes through all the earlier turning levels in order, with the gaps the walk's own turn times
dictate.

For four turning levels this is `Leg4Land`, clause by clause. -/
def LandWalk {m : ℕ} (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) : Prop :=
  ∀ (r : ℕ) (d : Fin m),
    (∀ p : ℕ, p < walkLen s ts → |f d - walkList s ts p| ≤ 1 → walkStop s ts r ≤ p) →
    ∃ j : ℕ → Fin m, j r = d ∧ walkStop s ts 0 ≤ (j 0).val ∧
      (∀ u, u < r → (j u).val + (walkStop s ts (u + 1) - walkStop s ts u) ≤ (j (u + 1)).val) ∧
      (∀ u, u < r → |f (j u) - walkLevel s ts u| ≤ 1)

/-- **The landmark sentence is necessary, for a walk of any shape.** An arm that folds onto
`walkList s ts` satisfies `LandWalk f s ts`.

This is the general form of `leg4Land_of_foldsOnto`: the walk is given by its list of turning
levels, and the sentence is the conjunction over its legs. -/
theorem landWalk_of_foldsOnto {m : ℕ} {f : Fin m → ℤ} {s : ℤ} {ts : List ℤ}
    (h : FoldsOnto f (walkLen s ts) (walkList s ts)) : LandWalk f s ts := by
  intro r d hd
  obtain ⟨j, hjr, hj0, hjgap, hjv⟩ :=
    foldsOnto_landmarkN h d r (walkStop s ts) (walkStop_mono s ts) hd
  refine ⟨j, hjr, hj0, hjgap, ?_⟩
  intro u hu
  have := hjv u hu
  rwa [walkList_walkStop] at this

/-! ## The four-leg walk is a walk of four levels

`leg4Walk L H K M P` runs from `P - 1` up to `K`, down to `M`, up to `H - 1` and down to `L + 1`,
so it is `walkList (P - 1) [K, M, H - 1, L + 1]`, and its turn times are the positions
`A = K - P + 1`, `B = 2K - P + 1 - M`, `C = 2K - P + H - 2M` of `HPC/Fold/Leg4Land.lean`. -/

section Leg4

variable {L H K M P : ℤ}

/-- The length of the four-leg walk, read off the list of its turning levels. -/
theorem walkLen_leg4 (hPK : P ≤ K) (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2) :
    walkLen (P - 1) [K, M, H - 1, L + 1] = leg4Len L H K M P := by
  simp only [walkLen]
  unfold leg4Len
  omega

/-- The turn times of the four-leg walk. -/
theorem walkStop_leg4_one (hPK : P ≤ K) :
    walkStop (P - 1) [K, M, H - 1, L + 1] 1 = (K - P + 1).toNat := by
  simp only [walkStop]
  omega

theorem walkStop_leg4_two (hPK : P ≤ K) (hMP : M ≤ P - 2) :
    walkStop (P - 1) [K, M, H - 1, L + 1] 2 = (2 * K - P + 1 - M).toNat := by
  simp only [walkStop]
  omega

theorem walkStop_leg4_three (hPK : P ≤ K) (hKH : K ≤ H - 1) (hMP : M ≤ P - 2) :
    walkStop (P - 1) [K, M, H - 1, L + 1] 3 = (2 * K - P + H - 2 * M).toNat := by
  simp only [walkStop]
  omega

/-- **The four-leg walk of the engine is the walk of its four turning levels.** -/
theorem leg4Walk_eq_walkList (hPK : P ≤ K) (hKH : K ≤ H - 1) (hLM : L + 1 ≤ M) (hMP : M ≤ P - 2)
    (p : ℕ) (hp : p < leg4Len L H K M P) :
    walkList (P - 1) [K, M, H - 1, L + 1] p = leg4Walk L H K M P p := by
  have hlen : (p : ℤ) < 2 * K - P + 2 * H - 2 * M - L - 1 := by
    have h := hp
    unfold leg4Len at h
    omega
  rcases Nat.lt_or_ge p (K - (P - 1)).natAbs with hA | hA
  · rw [walkList_cons_lt hA]
    unfold leg4Walk
    split_ifs <;> omega
  rw [walkList_cons_ge hA]
  rcases Nat.lt_or_ge (p - (K - (P - 1)).natAbs) (M - K).natAbs with hB | hB
  · rw [walkList_cons_lt hB]
    unfold leg4Walk
    split_ifs <;> omega
  rw [walkList_cons_ge hB]
  rcases Nat.lt_or_ge (p - (K - (P - 1)).natAbs - (M - K).natAbs) (H - 1 - M).natAbs with hC | hC
  · rw [walkList_cons_lt hC]
    unfold leg4Walk
    split_ifs <;> omega
  rw [walkList_cons_ge hC]
  rcases Nat.lt_or_ge (p - (K - (P - 1)).natAbs - (M - K).natAbs - (H - 1 - M).natAbs)
      (L + 1 - (H - 1)).natAbs with hD | hD
  · rw [walkList_cons_lt hD]
    unfold leg4Walk
    split_ifs <;> omega
  · rw [walkList_cons_ge hD, walkList_nil]
    unfold leg4Walk
    split_ifs <;> omega

end Leg4

end HPC.Fold
