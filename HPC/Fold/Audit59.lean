import HPC.Fold.Audit58
import HPC.Fold.Leg4Land

/-!
# The 175-link arm of batch 58, read by the exact criterion

`not_leg4CritClosesL5` (`HPC/Fold/Audit58.lean`) refutes the closure of the branch `L + 5` by the
*criteria* of the four-leg engine at a 175-link window of Bing's chain `bing 0 9`: its forward arm
meets the criterion of none of the twenty-nine parameter sets of the window, in either
orientation. Question 2 of COMMISSION.md asks which walks of the family serve that arm, and what
the exact criterion of question 1 says about it.

**Nine of the fifty-eight (parameter set, orientation) pairs serve it, and all nine have their
valley at `L + 1` and are read through the reflection of the arm.** This file proves it in the
kernel, by the dynamic program of `HPC/Fold/Decide.lean`, for all nine; the census
(`census-batch59.c`) reports that no other pair does.

The shape of the nine is the point. A walk with `M = L + 1` has *no* deep-floor trigger — there is
no level `M - 2 = L - 1` in the band — so the third clause of the landmark sentence
(`HPC/Fold/Leg4Land.lean`) is vacuous on it, and what the arm has to supply is two landmarks, not
four: a time at `K - 1` or above at index at least `K - P + 1`, and a time at `L + 2` or below
`K - 1` steps later. On this arm the greedy chain is at the indices `2` and `34` for
`(P, K, M) = (L + 5, L + 6, L + 1)`. The engine's criterion, by contrast, asks at its deep-floor
announcement for a landmark at `H - 2 = L + 7` before *every* descent to `P - 4`, and that is what
fails here: the announcement is read at `P - 4`, four levels below the base, where the walk's own
trigger is `M - 2`, and for `M = L + 1` the two are far apart.

So the answer to question 2 is that the arm is served, that the exact criterion says so, and that
the criterion of the engine misses it because its floor announcements are read at the base rather
than at the valley.
-/

set_option maxRecDepth 20000000

namespace HPC.Fold

namespace Audit59

open Audit58

/-! ## The nine walks that serve the arm

Each is the wide engine's walk `leg4Walk 0 9 K 1 P`, read on the reflection `armFR` of the arm —
equivalently, the arm itself folds onto the reflected walk `leg4Walk' 0 9 K 1 P`. -/

theorem serves_4_6_1 : FoldsOnto armFR (leg4Len 0 9 6 1 4) (leg4Walk 0 9 6 1 4) :=
  foldsOnto_of_foldsB (by decide +kernel)

theorem serves_4_7_1 : FoldsOnto armFR (leg4Len 0 9 7 1 4) (leg4Walk 0 9 7 1 4) :=
  foldsOnto_of_foldsB (by decide +kernel)

theorem serves_4_8_1 : FoldsOnto armFR (leg4Len 0 9 8 1 4) (leg4Walk 0 9 8 1 4) :=
  foldsOnto_of_foldsB (by decide +kernel)

theorem serves_5_6_1 : FoldsOnto armFR (leg4Len 0 9 6 1 5) (leg4Walk 0 9 6 1 5) :=
  foldsOnto_of_foldsB (by decide +kernel)

theorem serves_5_7_1 : FoldsOnto armFR (leg4Len 0 9 7 1 5) (leg4Walk 0 9 7 1 5) :=
  foldsOnto_of_foldsB (by decide +kernel)

theorem serves_5_8_1 : FoldsOnto armFR (leg4Len 0 9 8 1 5) (leg4Walk 0 9 8 1 5) :=
  foldsOnto_of_foldsB (by decide +kernel)

theorem serves_6_6_1 : FoldsOnto armFR (leg4Len 0 9 6 1 6) (leg4Walk 0 9 6 1 6) :=
  foldsOnto_of_foldsB (by decide +kernel)

theorem serves_6_7_1 : FoldsOnto armFR (leg4Len 0 9 7 1 6) (leg4Walk 0 9 7 1 6) :=
  foldsOnto_of_foldsB (by decide +kernel)

theorem serves_6_8_1 : FoldsOnto armFR (leg4Len 0 9 8 1 6) (leg4Walk 0 9 8 1 6) :=
  foldsOnto_of_foldsB (by decide +kernel)

/-! ## What the exact criterion says about it

The landmark sentence of the serving walk holds on the arm — by `leg4Land_of_foldsOnto`, since the
arm folds — while the criterion of the engine fails on it (`Audit58.no_refl_5_6_1`). The two
together are the gap between the engine and the exact criterion, at an explicit faithful arm of
Bing's own chain. -/

/-- **The exact criterion holds where the engine's criterion fails.** -/
theorem land_5_6_1 : Leg4Land armFR 9 6 1 5 :=
  leg4Land_of_foldsOnto (L := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    serves_5_6_1

/-- The criterion of the engine, at the same parameter set, fails (batch 58). -/
theorem not_crit_5_6_1 : ¬ Leg4Crit armFR (0 + 9) 6 1 5 := Audit58.no_refl_5_6_1

/-! ## The basepoint is served

The basepoint of the pair is its first link, so the backward arm is that link alone. Both arms of
the basepoint fold onto the reflected walk `L+5 → L+3 → L+8 → L+1 → L+8`, which is the conclusion
`s3_span_nine_mid5` asks for at this basepoint — the one basepoint at which batch 58 showed that
no criterion of the engine holds. -/

theorem serves_armF_5_6_1 :
    FoldsOnto (armG rho175 basept) (leg4Len 0 9 6 1 5) (leg4Walk' 0 9 6 1 5) :=
  foldsOnto_leg4W_refl _ 0 9 6 1 5 serves_5_6_1

theorem serves_armT_5_6_1 :
    FoldsOnto (armT rho175 basept) (leg4Len 0 9 6 1 5) (leg4Walk' 0 9 6 1 5) :=
  foldsOnto_of_foldsB (by decide +kernel)

/-- **The basepoint of the batch-58 witness is served by a walk of the family.** -/
theorem pair_folds :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG rho175 basept) len c ∧ FoldsOnto (armT rho175 basept) len c :=
  ⟨leg4Len 0 9 6 1 5, leg4Walk' 0 9 6 1 5, serves_armF_5_6_1, serves_armT_5_6_1⟩

end Audit59

end HPC.Fold
