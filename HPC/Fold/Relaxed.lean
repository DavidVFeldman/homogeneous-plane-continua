import HPC.Fold.ProfileP
import HPC.Fold.Decide

/-!
# The relaxed valley criterion serves no walk of the branch by itself

Batch 50 measured what the residual configuration of `cross_valley_profile` costs: with no
exceptional case at all, when one arm of a branch pair fails the valley clause, the other arm
stands at `L + 3` or below at a step at least four before each of its ascents to `L + 7`
(`cross_valley_armT_low3`, `cross_valley_armG_low3`, `HPC/Fold/CrossValley.lean`). That is the
V-criterion with `L + 3` where the criterion asks `L + 2`, and the commission of batch 51 asks
whether the relaxed clause is by itself enough for a fold onto *some* walk, since
`unserved_three_walks` needs only some walk.

The answer is no for each walk the development uses, and the witnesses are short. `Relaxed f L`
below is the clause; the five theorems say that an arm satisfying it need not fold onto the Λ-walk,
the V-walk, `w₃`, `w₄` or `w₅`, each refuted by an arm of at most nine steps decided in the kernel
through `foldsB_iff` (`HPC/Fold/Decide.lean`).

Two of the witnesses are instructive. `4, 3, 2, 1` satisfies the clause vacuously — it never
reaches `L + 7` — and folds onto neither `w₃` nor `w₅` nor the Λ-walk, because a descent to `L + 1`
at the step three is too early for any of them. `4, 5` is the same story for `w₄`, whose trough
comes first: that is the content of the new clause `MidW4`. So the relaxed clause constrains an
arm only above `L + 7`, and the walks are separated by what they ask below.

A search outside Lean (`census-batch51.py` and the report of this batch) finds no walk of at most
three turns, over the band and the basepoints of the branch, that serves every arm satisfying the
relaxed clause; and, in the other direction, every arm of at most twelve steps that satisfies it
folds onto at least one of the five. Neither is a theorem here; the five refutations are.
-/

namespace HPC.Fold

/-- **The relaxed valley clause of batch 50.** Before every ascent to `L + 7` a time at `L + 3` or
below, at a step at least four. -/
def Relaxed {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ e : Fin m, L + 7 ≤ f e → ∃ j : Fin m, j.val < e.val ∧ 4 ≤ j.val ∧ f j ≤ L + 3

instance (m : ℕ) (f : Fin m → ℤ) (L : ℤ) : Decidable (Relaxed f L) := by
  unfold Relaxed; infer_instance

/-! ## The two witnesses -/

/-- The arm `L+4, L+3, L+2, L+1`: it never reaches `L + 7`, so it satisfies the relaxed clause
with nothing to check. -/
def relaxDown : Fin 4 → ℤ := ![4, 3, 2, 1]

/-- The arm `L+4, L+5`: the same, and it rises at once. -/
def relaxUp : Fin 2 → ℤ := ![4, 5]

/-- The arm `L+4, L+3, L+2, L+2, L+3, L+4, L+5, L+6, L+7`: its one ascent to `L + 7` is announced
by its step `4`, where it stands at `L + 3`. -/
def relaxVee : Fin 9 → ℤ := ![4, 3, 2, 2, 3, 4, 5, 6, 7]

theorem relaxDown_relaxed : Relaxed relaxDown 0 := by decide

theorem relaxUp_relaxed : Relaxed relaxUp 0 := by decide

theorem relaxVee_relaxed : Relaxed relaxVee 0 := by decide

/-! ## The five refutations -/

/-- The relaxed clause does not give the Λ-walk. -/
theorem not_foldsOnto_lam_relaxDown :
    ¬ FoldsOnto relaxDown (lamLen (0 + 3) (0 + 9) 0) (lamCenter (0 + 3) (0 + 9) 0) := by
  decide +kernel

/-- The relaxed clause does not give the V-walk based at `L + 5` — the walk the crossing asks
for. -/
theorem not_foldsOnto_vee_relaxVee :
    ¬ FoldsOnto relaxVee (veeLen (0 + 5) (0 + 9) 0) (veeCenter (0 + 5) (0 + 9) 0) := by
  decide +kernel

/-- The relaxed clause does not give `w₃`. -/
theorem not_foldsOnto_w3_relaxDown :
    ¬ FoldsOnto relaxDown (leg3Len 0 (0 + 9) (0 + 6) (0 + 4))
      (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4)) := by
  decide +kernel

/-- The relaxed clause does not give `w₄`. -/
theorem not_foldsOnto_w4_relaxUp :
    ¬ FoldsOnto relaxUp (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
      (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2)) := by
  decide +kernel

/-- The relaxed clause does not give `w₅`. -/
theorem not_foldsOnto_w5_relaxDown :
    ¬ FoldsOnto relaxDown (leg3Len 0 (0 + 9) (0 + 7) (0 + 4))
      (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4)) := by
  decide +kernel

/-- **The relaxed clause serves no one of the five walks.** For each of the five walks of the
development there is an arm of the band based at `L + 4` satisfying the relaxed clause and not
folding onto it. -/
theorem relaxed_serves_no_walk :
    (Relaxed relaxDown 0 ∧
      ¬ FoldsOnto relaxDown (lamLen (0 + 3) (0 + 9) 0) (lamCenter (0 + 3) (0 + 9) 0) ∧
      ¬ FoldsOnto relaxDown (leg3Len 0 (0 + 9) (0 + 6) (0 + 4))
        (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4)) ∧
      ¬ FoldsOnto relaxDown (leg3Len 0 (0 + 9) (0 + 7) (0 + 4))
        (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4))) ∧
    (Relaxed relaxUp 0 ∧
      ¬ FoldsOnto relaxUp (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
        (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2))) ∧
    (Relaxed relaxVee 0 ∧
      ¬ FoldsOnto relaxVee (veeLen (0 + 5) (0 + 9) 0) (veeCenter (0 + 5) (0 + 9) 0)) :=
  ⟨⟨relaxDown_relaxed, not_foldsOnto_lam_relaxDown, not_foldsOnto_w3_relaxDown,
      not_foldsOnto_w5_relaxDown⟩,
    ⟨relaxUp_relaxed, not_foldsOnto_w4_relaxUp⟩,
    ⟨relaxVee_relaxed, not_foldsOnto_vee_relaxVee⟩⟩

end HPC.Fold
