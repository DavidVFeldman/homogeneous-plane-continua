import HPC.Fold.Decide
import HPC.Fold.ThreeWalks

/-!
# The σ-route loses the basepoint: a counterexample, decided by the kernel

The reflection of the general model sends `(ρ, σ)` to `(9 − σ, 9 − ρ)`, so the branch `L + 5` of
`ρ` is the branch `L + 4` of `τ = 9 − σ`, and the theorems of the branch `L + 4` apply to the
`τ`-pair. What the branch `L + 5` of `ρ` actually needs, however, is a fold of the arms of `9 − ρ`,
which sits one level above `τ` wherever the link is non-thin. COMMISSION.md §2 question 2 asks
whether a fold of the `τ`-pair onto one of the five walks of the branch `L + 4` always yields a
fold of the pair of `9 − ρ` onto *some* walk of that list — an implication batch 54 measured and
found to hold at every basepoint of its corpus.

It does not hold. This file carries one of the 501 basepoints of `census-batch55.c` at which it
fails, shrunk by the census to a window of 71 links, and puts every verdict to the kernel:

* the `τ`-pair folds onto the V-walk and `w₄` — both arms;
* the pair of `9 − ρ` folds onto **none** of the five: for each walk, one of its two arms is
  exhibited and the fold is refuted;
* the branch hypothesis holds where it is asked: both arms of `ρ` are `LowAt`, and both arms of
  `τ` are `HighAt`, with `τ` at `L + 4` at the basepoint.

So the σ-route cannot be repaired by allowing the walk to change: at this basepoint no walk of the
five serves `9 − ρ` at all. (The pair itself is faithful — `IsCrookedIvF` is not a decidable
predicate as stated, since it quantifies over all levels, and the census's own test is what
certifies it; everything below is about the arms, and is decided here.)

The arms are read off base-sixteen numerals by `armOf`, exactly as in the audits of batches 50–52.
-/

set_option maxRecDepth 40000000

namespace HPC.Fold

namespace Audit55

/-- The arm whose level at the step `i` is the `i`-th base-sixteen digit of `n`. -/
def armOf (n : ℕ) (m : ℕ) : Fin m → ℤ := fun i => (((n >>> (4 * i.val)) &&& 15 : ℕ) : ℤ)

instance (m : ℕ) (f : Fin m → ℤ) (tl th : ℤ) : Decidable (LowAt f tl th) := by
  unfold LowAt; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) (tl th : ℤ) : Decidable (HighAt f tl th) := by
  unfold HighAt; infer_instance

/-! ## The pair

The window is `sigma-route counterexample 1 [mix 0]: window [408, 478] of 986, basepoint 9 of 71 links`.

`ρ`: `8 7 6 7 6 5 6 6 6 5 5 5 4 5 5 5 6 6 6 5 6 5 4 5 5 5 4 4 4 3 4 5 4 5 6 5 4 5 5 5 6 6 6 5 5 5 4 5 6 5 4 4 4 3 4 4 4 5 6 5 4 5 4 3 4 5 4 3 4 3 2`.

`σ`: `8 7 6 7 6 5 6 7 6 5 6 5 4 5 6 5 6 7 6 6 6 5 4 5 6 5 4 5 4 3 4 5 4 5 6 5 5 5 6 6 6 7 6 5 6 5 5 5 6 5 4 5 4 3 4 5 4 5 6 5 4 5 4 4 4 5 4 3 4 3 2`.

The basepoint is the index where `ρ` stands at `L + 5`; the arms below are read from it, outwards.
-/

/-- the forward arm of `τ = 9 − σ`, 62 steps.

Levels: `4 3 4 5 4 3 4 3 2 3 3 3 4 5 4 3 4 5 4 5 6 5 4 5 4 3 4 4 4 3 3 3 2 3 4 3 4 4 4 3 4 5 4 5 6 5 4 5
4 3 4 5 4 5 5 5 4 5 6 5 6 7`. -/
def tG : Fin 62 → ℤ :=
  armOf 0x76565455545434545654543444343233344434545654543454333234345434 62

/-- the backward arm of `τ = 9 − σ`, 10 steps.

Levels: `4 3 2 3 4 3 2 3 2 1`. -/
def tT : Fin 10 → ℤ :=
  armOf 0x1232343234 10

/-- the forward arm of `9 − ρ`, 62 steps.

Levels: `4 4 4 5 4 4 4 3 3 3 4 3 4 5 4 4 4 5 5 5 6 5 4 5 4 3 4 5 4 4 4 3 3 3 4 4 4 5 4 3 4 5 5 5 6 5 5 5
4 3 4 5 4 5 6 5 4 5 6 5 6 7`. -/
def rG : Fin 62 → ℤ :=
  armOf 0x76565456545434555655543454443334445434545655544454343334445444 62

/-- the backward arm of `9 − ρ`, 10 steps.

Levels: `4 3 3 3 4 3 2 3 2 1`. -/
def rT : Fin 10 → ℤ :=
  armOf 0x1232343334 10

/-- the forward arm of `ρ`, 62 steps.

Levels: `5 5 5 4 5 5 5 6 6 6 5 6 5 4 5 5 5 4 4 4 3 4 5 4 5 6 5 4 5 5 5 6 6 6 5 5 5 4 5 6 5 4 4 4 3 4 4 4
5 6 5 4 5 4 3 4 5 4 3 4 3 2`. -/
def pG : Fin 62 → ℤ :=
  armOf 0x23434543454565444344456545556665554565454344455545656665554555 62

/-- the backward arm of `ρ`, 10 steps.

Levels: `5 6 6 6 5 6 7 6 7 8`. -/
def pT : Fin 10 → ℤ :=
  armOf 0x8767656665 10

/-! ## The hypotheses of the branch -/

theorem pG_lowAt : LowAt pG (0 + 1) (0 + 8) := by decide +kernel
theorem pT_lowAt : LowAt pT (0 + 1) (0 + 8) := by decide +kernel
theorem tG_highAt : HighAt tG (0 + 1) (0 + 8) := by decide +kernel
theorem tT_highAt : HighAt tT (0 + 1) (0 + 8) := by decide +kernel
theorem tG_base : tG ⟨0, by omega⟩ = 0 + 4 := by decide +kernel
theorem pG_base : pG ⟨0, by omega⟩ = 0 + 5 := by decide +kernel

/-! ## The `τ`-pair folds -/

theorem tG_folds_Vee :
    FoldsOnto tG (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0) := by
  decide +kernel
theorem tT_folds_Vee :
    FoldsOnto tT (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0) := by
  decide +kernel
theorem tG_folds_w4 :
    FoldsOnto tG (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
      (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2)) := by
  decide +kernel
theorem tT_folds_w4 :
    FoldsOnto tT (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
      (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2)) := by
  decide +kernel

/-! ## The pair of `9 − ρ` folds onto none of the five -/

theorem rT_not_folds_Lam :
    ¬ (FoldsOnto rT (lamLen (0 + 3) (0 + 9) 0)
      (lamCenter (0 + 3) (0 + 9) 0)) := by
  decide +kernel
theorem rG_not_folds_Vee :
    ¬ (FoldsOnto rG (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0)) := by
  decide +kernel
theorem rT_not_folds_w3 :
    ¬ (FoldsOnto rT (leg3Len 0 (0 + 9) (0 + 6) (0 + 4))
      (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4))) := by
  decide +kernel
theorem rG_not_folds_w4 :
    ¬ (FoldsOnto rG (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
      (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2))) := by
  decide +kernel
theorem rT_not_folds_w5 :
    ¬ (FoldsOnto rT (leg3Len 0 (0 + 9) (0 + 7) (0 + 4))
      (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4))) := by
  decide +kernel

/-! ## The counterexample, assembled -/

/-- **The σ-route loses the basepoint.** At this basepoint the `τ`-pair folds onto the V-walk, while no
walk of the five serves the pair of `9 − ρ`: for each of the five, one arm of `9 − ρ` refuses it.
-/
theorem sigma_route_walk_not_transported :
    (FoldsOnto tG (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0) ∧
      FoldsOnto tT (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0)) ∧
    ¬ (FoldsOnto rT (lamLen (0 + 3) (0 + 9) 0)
      (lamCenter (0 + 3) (0 + 9) 0)) ∧
    ¬ (FoldsOnto rG (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0)) ∧
    ¬ (FoldsOnto rT (leg3Len 0 (0 + 9) (0 + 6) (0 + 4))
      (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4))) ∧
    ¬ (FoldsOnto rG (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
      (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2))) ∧
    ¬ (FoldsOnto rT (leg3Len 0 (0 + 9) (0 + 7) (0 + 4))
      (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4))) :=
  ⟨⟨tG_folds_Vee, tT_folds_Vee⟩, rT_not_folds_Lam, rG_not_folds_Vee, rT_not_folds_w3,
    rG_not_folds_w4, rT_not_folds_w5⟩

end Audit55

end HPC.Fold
