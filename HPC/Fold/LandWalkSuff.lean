import HPC.Fold.LandList

/-!
# The general engine: the greedy, the invariant and the sufficiency statement

Batch 61 stated the landmark sentence for a walk of any shape (`LandWalk`, `HPC/Fold/LandList.lean`)
and proved it **necessary** for folding (`landWalk_of_foldsOnto`). The missing half is sufficiency,
and question 3 of batch 62 asks for it *as a statement*: the invariant of `gseq4_invLand` with two
bounds per interior leg and the credit equal to the gap of consecutive turn times, read over
`walkList s ts`.

This file supplies the three pieces.

## The greedy, for a walk of any shape

`gseqWalk s ts u` is the greedy time-assignment of `HPC/Fold/Leg4.lean` with the four-leg walk
replaced by `walkList s ts`: at each step the time advances if the next time serves the new level,
stays if the current one does, and otherwise retreats. `foldsOnto_of_gseqWalk` is the whole of what
the greedy is for — **if the greedy time always serves the arm's level, the arm folds onto the
walk** — and is proved here for a walk of any shape.

## The invariant

`LandChainAt f s ts r a` is a landmark chain of the sentence: times `a 0 ≤ ⋯ ≤ a r` of the arm at
the walk's first `r + 1` turning levels, with the gaps the walk's own turn times dictate.
`WalkInvLand` is then two bounds per leg, uniform in the leg:

```
(capped)    a r + n ≤ j  →  min (min (walkStop r + n) (walkStop r + |u j − walkLevel r| + 1))
                                (walkStop (r+1))                   ≤ q j
(uncapped)  a r     ≤ j  →  walkStop r + |u j − walkLevel r|       ≤ q j + 1
```

For the four-leg walk these are exactly the six bounds of `gseq4_invLand`: the first at `r = 0`
with the credit `j` is `(1)`, at `r = 1` it is `(2)` and at `r = 2` it is `(3)`; the second at
`r = 1, 2, 3` is `(2′)`, `(3′)`, `(4)`. The credit `n` is the number of steps by which the chain's
last landmark precedes `j`, and it is spendable because the sentence's own gap between consecutive
landmarks is the gap of the walk's consecutive turn times.

## The statement

`LandWalkSuffices` is the sufficiency half, for a walk of any shape and an arm every one of whose
levels the walk serves. `landWalk_iff_foldsOnto_of_suffices` records that with it the landmark
sentence *is* folding, which is what the engine would be. The proof of `LandWalkSuffices` — the
induction of `gseq4_invLand` carried out over `walkList s ts` — is not in this batch.
-/

namespace HPC.Fold

/-! ## The greedy for a walk of any shape -/

/-- A time of the walk serves a level. -/
def ValWalk (s : ℤ) (ts : List ℤ) (v : ℤ) (q : ℕ) : Prop :=
  q < walkLen s ts ∧ |v - walkList s ts q| ≤ 1

open Classical in
/-- One greedy step: advance if the next time serves the level, stay if the current one does,
otherwise retreat. -/
noncomputable def gstepWalk (s : ℤ) (ts : List ℤ) (v : ℤ) (q : ℕ) : ℕ :=
  if ValWalk s ts v (q + 1) then q + 1 else if ValWalk s ts v q then q else q - 1

/-- The greedy time never moves by more than one. -/
theorem gstepWalk_dist (s : ℤ) (ts : List ℤ) (v : ℤ) (q : ℕ) :
    q - 1 ≤ gstepWalk s ts v q ∧ gstepWalk s ts v q ≤ q + 1 := by
  unfold gstepWalk
  split_ifs <;> omega

open Classical in
/-- The greedy time-assignment of a level sequence. -/
noncomputable def gseqWalk (s : ℤ) (ts : List ℤ) (u : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => gstepWalk s ts (u (j + 1)) (gseqWalk s ts u j)

@[simp] theorem gseqWalk_zero (s : ℤ) (ts : List ℤ) (u : ℕ → ℤ) : gseqWalk s ts u 0 = 0 := rfl

theorem gseqWalk_succ (s : ℤ) (ts : List ℤ) (u : ℕ → ℤ) (j : ℕ) :
    gseqWalk s ts u (j + 1) = gstepWalk s ts (u (j + 1)) (gseqWalk s ts u j) := rfl

/-- **The greedy is all that folding needs.** If the greedy time serves the arm's level at every
index, the arm folds onto the walk. This is `foldsOnto_leg4W_of_val4` for a walk of any shape. -/
theorem foldsOnto_of_gseqWalk {m : ℕ} (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) (u : ℕ → ℤ)
    (hval : ∀ j : Fin m, ValWalk s ts (f j) (gseqWalk s ts u j.val)) :
    FoldsOnto f (walkLen s ts) (walkList s ts) := by
  refine ⟨fun j => gseqWalk s ts u j.val, fun j => (hval j).1, ?_, ?_, fun j => (hval j).2⟩
  · intro j j' hjj'
    have hstep : gseqWalk s ts u (j.val + 1) =
        gstepWalk s ts (u (j.val + 1)) (gseqWalk s ts u j.val) := rfl
    have hd := gstepWalk_dist s ts (u (j.val + 1)) (gseqWalk s ts u j.val)
    show |((gseqWalk s ts u j'.val : ℕ) : ℤ) - ((gseqWalk s ts u j.val : ℕ) : ℤ)| ≤ 1
    rw [hjj', hstep, abs_le]
    omega
  · intro j hj
    show gseqWalk s ts u j.val = 0
    rw [hj, gseqWalk_zero]

/-! ## The landmark chain and the invariant -/

/-- **A landmark chain of the sentence.** Times `a 0 ≤ ⋯ ≤ a r` of the arm at the walk's first
`r + 1` turning levels, separated by the gaps of the walk's own turn times. This is the chain
`LandWalk` produces, read as a predicate. -/
def LandChainAt {m : ℕ} (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) (r : ℕ) (a : ℕ → Fin m) : Prop :=
  walkStop s ts 0 ≤ (a 0).val ∧
    (∀ w, w < r → (a w).val + (walkStop s ts (w + 1) - walkStop s ts w) ≤ (a (w + 1)).val) ∧
    (∀ w, w ≤ r → |f (a w) - walkLevel s ts w| ≤ 1)

/-- **The invariant of the general engine**, two bounds per leg. The capped bound spends a credit
`n` — the number of steps by which the chain's last landmark precedes the index — against the
walk's own turn times; the uncapped bound is the same two levels weaker and needs no credit. -/
def WalkInvLand {m : ℕ} (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) (u : ℕ → ℤ) (q : ℕ → ℕ) : Prop :=
  ∀ j : ℕ,
    (∀ (r n : ℕ) (a : ℕ → Fin m), LandChainAt f s ts r a → (a r).val + n ≤ j →
      min (min (walkStop s ts r + n)
            (walkStop s ts r + (u j - walkLevel s ts r).natAbs + 1))
          (walkStop s ts (r + 1)) ≤ q j) ∧
    (∀ (r : ℕ) (a : ℕ → Fin m), LandChainAt f s ts r a → (a r).val ≤ j →
      walkStop s ts r + (u j - walkLevel s ts r).natAbs ≤ q j + 1)

/-- The chain a landmark sentence produces is a chain of `LandChainAt`. -/
theorem landChainAt_of_landWalk {m : ℕ} {f : Fin m → ℤ} {s : ℤ} {ts : List ℤ}
    (h : LandWalk f s ts) (r : ℕ) (d : Fin m)
    (hd : ∀ p : ℕ, p < walkLen s ts → |f d - walkList s ts p| ≤ 1 → walkStop s ts (r + 1) ≤ p) :
    ∃ a : ℕ → Fin m, a (r + 1) = d ∧ LandChainAt f s ts r a := by
  obtain ⟨a, har, ha0, hagap, haval⟩ := h (r + 1) d hd
  exact ⟨a, har, ha0, fun w hw => hagap w (by omega), fun w hw => haval w (by omega)⟩

/-! ## The sufficiency statement -/

/-- **The sufficiency half of the general engine.** For a 1-Lipschitz arm starting within one of
the walk's first level and every one of whose levels some time of the walk serves, the landmark
sentence implies folding.

This is the statement question 3 asks for; its proof is the induction of `gseq4_invLand` carried
out against `WalkInvLand` over `walkList s ts`, and is not in this batch. -/
def LandWalkSuffices : Prop :=
  ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ),
    IsLip f →
    |f ⟨0, hm⟩ - s| ≤ 1 →
    (∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) →
    LandWalk f s ts →
    FoldsOnto f (walkLen s ts) (walkList s ts)

/-- **With sufficiency the landmark sentence is folding**, for a walk of any shape: necessity is
`landWalk_of_foldsOnto`. -/
theorem landWalk_iff_foldsOnto_of_suffices (h : LandWalkSuffices) {m : ℕ} (hm : 0 < m)
    (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) (hlip : IsLip f) (h0 : |f ⟨0, hm⟩ - s| ≤ 1)
    (hband : ∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) :
    LandWalk f s ts ↔ FoldsOnto f (walkLen s ts) (walkList s ts) :=
  ⟨fun hl => h m hm f s ts hlip h0 hband hl, landWalk_of_foldsOnto⟩

end HPC.Fold
