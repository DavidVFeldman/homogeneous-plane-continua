import HPC.Fold.Audit52
import HPC.Fold.ArmReflectGap

/-!
# Three walks are not enough at the branch `L + 5`

At the branch `L + 4` an unserved pair folds, over every census of this repository, onto one of the
three walks `w₃`, `w₄`, `w₅`; that is the standing work item `unserved_three_walks`. The reflection
of §1 of `HPC/Fold/ArmReflect.lean` carries the three walks to the basepoint `L + 5`, and the
obvious guess is that the reflected item holds there. **It does not.**

The pair below comes from the general model: it is the two arms at a basepoint of the branch
`L + 5` of a mixture of shavings and fills of `bing 0 9`, truncated to their first fifty-seven
steps. Where the arms come from is not part of the statement — everything the refutation uses is
decided on the two arms themselves. Both arms are 1-Lipschitz, stay in the band `[0, 9]`,
start at `0 + 5`, are `LowAt (L + 1) (L + 8)` — the branch hypothesis — and satisfy the two
crookedness clauses `CrookUp` and `CrookDown` that the model delivers for every arm. The pair is
unserved by both reflected canonical walks — the forward arm misses the Λ-walk based at `L + 4`
and the backward arm the V-walk based at `L + 6` — and the backward arm folds onto none of the
three reflected walks at all: every verdict below is decided in the kernel.

So `not_threeWalks5Arms`: the arm-level form of the work item, read at the branch `L + 5` through
the reflection, is false. The census `census-batch52.c` finds 771 such basepoints among the 74 884
unserved basepoints of the branch `L + 5` over its corpus, all of them in mixtures of several
shavings and fills; single shavings, single fills and the thin chains have none. It also finds that
adding the two *unreflected* walks `L+5 → L+7 → L+1 → L+8` and `L+4 → L+7 → L+1 → L+8` — the
shortest walks it finds serving the missed pairs — leaves 166 of them unserved, so the branch
`L + 5` is not a list of five walks either.

Together with `HPC/Fold/ArmReflectGap.lean` this is the negative half of the commission's third
question: the *criteria* of the branch `L + 4` reflect, its *crookedness clauses* and its *list of
walks* do not.
-/

set_option maxRecDepth 40000000

namespace HPC.Fold

namespace ReflectMiss

open Audit52 (armOf)

/-- The forward arm: `5 5 6 7 6 5 5 5 4 5 6 5 4 5 4 3 4 4 4 5 6 5 4 5 6 5 6 6 6 5 5 5 4 5 6 5 4 5 4
3 4 5 4 5 5 5 4 5 4 3 4 5 4 3 3 3 2`. -/
def missG : Fin 57 → ℤ := armOf 0x233345434545554543454565455566656545654443454565455567655 57

/-- The backward arm: `5 5 4 5 5 5 6 7 6 5 6 7 6 7 8 7 6 6 6 5 6 7 6 5 6 5 4 5 5 5 6 7 6 5 5 5 4 5 6
5 4 4 4 3 4 5 4 5 5 5 4 5 5 5 6 7 6`. -/
def missT : Fin 57 → ℤ := armOf 0x676555455545434445654555676555456567656667876765676555455 57

/-! ## The two arms are arms of the branch -/

theorem missG_isLip : IsLip missG := by decide +kernel

theorem missT_isLip : IsLip missT := by decide +kernel

theorem missG_lb : ∀ j, (0 : ℤ) ≤ missG j := by decide +kernel

theorem missG_ub : ∀ j, missG j ≤ 0 + 9 := by decide +kernel

theorem missT_lb : ∀ j, (0 : ℤ) ≤ missT j := by decide +kernel

theorem missT_ub : ∀ j, missT j ≤ 0 + 9 := by decide +kernel

theorem missG_base : missG ⟨0, by norm_num⟩ = 0 + 5 := by decide +kernel

theorem missT_base : missT ⟨0, by norm_num⟩ = 0 + 5 := by decide +kernel

theorem missG_lowAt : LowAt missG (0 + 1) (0 + 8) := by decide +kernel

theorem missT_lowAt : LowAt missT (0 + 1) (0 + 8) := by decide +kernel

theorem missG_crookUp : CrookUp missG := by decide +kernel

theorem missG_crookDown : CrookDown missG := by decide +kernel

theorem missT_crookUp : CrookUp missT := by decide +kernel

theorem missT_crookDown : CrookDown missT := by decide +kernel

/-! ## The pair is unserved, and no reflected walk folds both arms -/

/-- The forward arm does not fold onto the Λ-walk based at `L + 4`, the reflection of the V-walk of
the branch `L + 4`. -/
theorem missG_not_lam4 :
    ¬ FoldsOnto missG (lamLen (0 + 4) (0 + 9) 0) (lamCenter (0 + 4) (0 + 9) 0) := by
  decide +kernel

/-- The backward arm does not fold onto the V-walk based at `L + 6`, the reflection of the Λ-walk
of the branch `L + 4`. -/
theorem missT_not_vee6 :
    ¬ FoldsOnto missT (veeLen (0 + 6) (0 + 9) 0) (veeCenter (0 + 6) (0 + 9) 0) := by
  decide +kernel

/-- The reflection of `w₃` does not fold the backward arm. -/
theorem missT_not_w3R :
    ¬ FoldsOnto missT (leg3Len 0 (0 + 9) (0 + 6) (0 + 4)) (leg3Walk' 0 (0 + 9) (0 + 6) (0 + 5)) := by
  decide +kernel

/-- The reflection of `w₄` does not fold the backward arm. -/
theorem missT_not_w4R :
    ¬ FoldsOnto missT (leg3Len 0 (0 + 9) (0 + 7) (0 + 7)) (leg3Walk 0 (0 + 9) (0 + 7) (0 + 7)) := by
  decide +kernel

/-- The reflection of `w₅` does not fold the backward arm. -/
theorem missT_not_w5R :
    ¬ FoldsOnto missT (leg3Len 0 (0 + 9) (0 + 7) (0 + 4)) (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 5)) := by
  decide +kernel

/-! ## The refutation -/

/-- **The work item of the branch `L + 4`, reflected to the branch `L + 5` and read on arms.** For
two 1-Lipschitz arms of the band based at `L + 5`, satisfying the branch hypothesis and the two
crookedness clauses the model delivers, and unserved by the two reflected canonical walks, one of
the three reflected walks folds both. -/
def ThreeWalks5Arms : Prop :=
  ∀ {mg mt : ℕ} (hg : 0 < mg) (ht : 0 < mt) (g : Fin mg → ℤ) (t : Fin mt → ℤ),
    IsLip g → IsLip t → CrookUp g → CrookDown g → CrookUp t → CrookDown t →
    (∀ j, (0 : ℤ) ≤ g j) → (∀ j, g j ≤ 0 + 9) → (∀ j, (0 : ℤ) ≤ t j) → (∀ j, t j ≤ 0 + 9) →
    g ⟨0, hg⟩ = 0 + 5 → t ⟨0, ht⟩ = 0 + 5 →
    LowAt g (0 + 1) (0 + 8) → LowAt t (0 + 1) (0 + 8) →
    ¬ (FoldsOnto g (lamLen (0 + 4) (0 + 9) 0) (lamCenter (0 + 4) (0 + 9) 0) ∧
        FoldsOnto t (lamLen (0 + 4) (0 + 9) 0) (lamCenter (0 + 4) (0 + 9) 0)) →
    ¬ (FoldsOnto g (veeLen (0 + 6) (0 + 9) 0) (veeCenter (0 + 6) (0 + 9) 0) ∧
        FoldsOnto t (veeLen (0 + 6) (0 + 9) 0) (veeCenter (0 + 6) (0 + 9) 0)) →
    (FoldsOnto g (leg3Len 0 (0 + 9) (0 + 6) (0 + 4)) (leg3Walk' 0 (0 + 9) (0 + 6) (0 + 5)) ∧
        FoldsOnto t (leg3Len 0 (0 + 9) (0 + 6) (0 + 4)) (leg3Walk' 0 (0 + 9) (0 + 6) (0 + 5))) ∨
      (FoldsOnto g (leg3Len 0 (0 + 9) (0 + 7) (0 + 7)) (leg3Walk 0 (0 + 9) (0 + 7) (0 + 7)) ∧
        FoldsOnto t (leg3Len 0 (0 + 9) (0 + 7) (0 + 7)) (leg3Walk 0 (0 + 9) (0 + 7) (0 + 7))) ∨
      (FoldsOnto g (leg3Len 0 (0 + 9) (0 + 7) (0 + 4)) (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 5)) ∧
        FoldsOnto t (leg3Len 0 (0 + 9) (0 + 7) (0 + 4)) (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 5)))

/-- **Three walks are not enough at the branch `L + 5`.** -/
theorem not_threeWalks5Arms : ¬ ThreeWalks5Arms := by
  intro h
  rcases h (by norm_num) (by norm_num) missG missT missG_isLip missT_isLip missG_crookUp
      missG_crookDown missT_crookUp missT_crookDown missG_lb missG_ub missT_lb missT_ub
      missG_base missT_base missG_lowAt missT_lowAt (fun hc => missG_not_lam4 hc.1)
      (fun hc => missT_not_vee6 hc.2) with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
  · exact missT_not_w3R h2
  · exact missT_not_w4R h2
  · exact missT_not_w5R h2

end ReflectMiss

end HPC.Fold
