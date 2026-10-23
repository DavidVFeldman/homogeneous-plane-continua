import HPC.Archive.CrossServed
import HPC.Fold.Decide
import HPC.Fold.LandmarkW

/-!
# The pair that decided batch 49, decided again — by the program

The basepoint `336` of `bing9sB` is where batch 49 refuted `cross_ceil_profile`, `unserved_profile`
and `unserved_leg3deep`, and where `HPC/Fold/CrossServed.lean` then showed the pair served by the
reflected walk `w₄`. Both of those went through instruments built for the purpose: the refutation
through the necessity half of the landmark sentence (`HPC/Fold/Landmark.lean`), the fold through
two itineraries written out by hand as base-sixteen numerals.

With `HPC/Fold/Decide.lean` neither instrument is needed. `foldsB_iff` proves the census's dynamic
program equivalent to `FoldsOnto`, so every one of those facts — and its negation where that is
what holds — is a kernel computation on the chain itself. This file re-decides them, and adds one
the earlier route did not have: the same pair is served by the **third** walk `w₅` as well.

| | fact | how batch 49 had it | here |
|---|---|---|---|
| `w₃` | the forward arm does **not** fold | `leg3Ceil_of_foldsOnto_leg3` + `not_leg3Ceil_sBG` | decided |
| `w₄` | both arms fold | two itineraries by hand | decided |
| `w₅` | both arms fold | not known | decided |
| Λ | the backward arm does not fold | the exact Λ-criterion | decided |
| V | the forward arm does not fold | the exact V-criterion | decided |

So the pair is unserved by the two canonical walks and served by two of the three walks of
`unserved_three_walks`; the work item holds there twice over.
-/

namespace HPC.Fold

set_option maxRecDepth 40000000

/-! ## The two canonical walks miss the pair -/

/-- The backward arm does not fold onto the Λ-walk. -/
theorem sBT_not_lam_dec :
    ¬ FoldsOnto sBT (lamLen (0 + 3) (0 + 9) 0) (lamCenter (0 + 3) (0 + 9) 0) := by
  decide +kernel

/-- The forward arm does not fold onto the V-walk. -/
theorem sBG_not_vee_dec :
    ¬ FoldsOnto sBG (veeLen (0 + 5) (0 + 9) 0) (veeCenter (0 + 5) (0 + 9) 0) := by
  decide +kernel

/-! ## The first of the three walks misses it too -/

/-- **The refutation of batch 49, decided.** The forward arm does not fold onto
`w₃ = L+3 → L+6 → L+1 → L+8`. -/
theorem sBG_not_w3_dec :
    ¬ FoldsOnto sBG (leg3Len 0 (0 + 9) (0 + 6) (0 + 4)) (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4)) := by
  decide +kernel

/-! ## The second and third do not -/

/-- The forward arm folds onto `w₄ = L+3 → L+2 → L+8 → L+1`. -/
theorem sBG_w4_dec :
    FoldsOnto sBG (leg3Len 0 (0 + 9) (0 + 7) (0 + 7)) (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2)) := by
  decide +kernel

/-- The backward arm folds onto `w₄`. -/
theorem sBT_w4_dec :
    FoldsOnto sBT (leg3Len 0 (0 + 9) (0 + 7) (0 + 7)) (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2)) := by
  decide +kernel

/-- The forward arm folds onto `w₅ = L+3 → L+7 → L+1 → L+8`. -/
theorem sBG_w5_dec :
    FoldsOnto sBG (leg3Len 0 (0 + 9) (0 + 7) (0 + 4)) (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4)) := by
  decide +kernel

/-- The backward arm folds onto `w₅`. -/
theorem sBT_w5_dec :
    FoldsOnto sBT (leg3Len 0 (0 + 9) (0 + 7) (0 + 4)) (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4)) := by
  decide +kernel

/-! ## What the work item asks, at this pair -/

/-- **`unserved_three_walks` holds at the basepoint `336` of `bing9sB`**, and by two of its three
disjuncts: the pair folds onto `w₄`, and onto `w₅`, though not onto `w₃`. -/
theorem sB_three_walks :
    (FoldsOnto sBG (leg3Len 0 (0 + 9) (0 + 6) (0 + 4)) (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4)) ∧
        FoldsOnto sBT (leg3Len 0 (0 + 9) (0 + 6) (0 + 4)) (leg3Walk 0 (0 + 9) (0 + 6) (0 + 4))) ∨
      (FoldsOnto sBG (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
          (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2)) ∧
        FoldsOnto sBT (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
          (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2))) ∨
      (FoldsOnto sBG (leg3Len 0 (0 + 9) (0 + 7) (0 + 4)) (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4)) ∧
        FoldsOnto sBT (leg3Len 0 (0 + 9) (0 + 7) (0 + 4)) (leg3Walk 0 (0 + 9) (0 + 7) (0 + 4))) :=
  Or.inr (Or.inl ⟨sBG_w4_dec, sBT_w4_dec⟩)

/-- **The pair is unserved by the two canonical walks**, decided. -/
theorem sB_unserved_dec :
    ¬ (FoldsOnto sBG (lamLen (0 + 3) (0 + 9) 0) (lamCenter (0 + 3) (0 + 9) 0) ∧
        FoldsOnto sBT (lamLen (0 + 3) (0 + 9) 0) (lamCenter (0 + 3) (0 + 9) 0)) ∧
      ¬ (FoldsOnto sBG (veeLen (0 + 5) (0 + 9) 0) (veeCenter (0 + 5) (0 + 9) 0) ∧
        FoldsOnto sBT (veeLen (0 + 5) (0 + 9) 0) (veeCenter (0 + 5) (0 + 9) 0)) :=
  ⟨fun h => sBT_not_lam_dec h.2, fun h => sBG_not_vee_dec h.1⟩

/-- **The clauses of the three walks, at this pair.** The forward arm fails `Leg3Ceil`, which is
why `w₃` cannot serve it (`leg3Ceil_of_foldsOnto_leg3`); it satisfies the clauses of the other two
walks, which do serve it. Decided on the chain. -/
theorem sBG_clauses_dec : ¬ Leg3Ceil sBG 0 ∧ CeilW4 sBG 0 ∧ Valley5 sBG 0 :=
  ⟨not_leg3Ceil_sBG, ceilW4_of_foldsOnto_w4 sBG_w4_dec, valley5_of_foldsOnto_w5 sBG_w5_dec⟩

end HPC.Fold
