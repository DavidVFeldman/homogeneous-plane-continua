import HPC.Fold.Timing
import HPC.Fold.DichotomyFaithful

/-!
# The two walks of span nine are split at one basepoint

`HPC/Fold/Span9Profile.lean` serves the open branch at `L + 4` in two ways: by the Λ-walk based
at `L + 3`, whose exact criterion is `CritLamProfile`, and by the V-walk based at `L + 5`, whose
exact criterion is `CritVeeProfile`. Both lemmas ask their criterion of *both* arms. The census of
batch 42 reported that no actual pair of the branch splits the two criteria between its arms; that
census held its arms in buffers of 512 entries and skipped every basepoint with a longer arm, so
at length 986 it saw ten of the 182 basepoints of the branch. The class is not empty.

This file exhibits a member of it, inside a sequence whose faithfulness is already proved in the
repository: `ceSeq`, Bing's 409-link chain `bing 0 8` (`HPC/Fold/DichotomyWitness.lean`,
`HPC/Fold/DichotomyFaithful.lean`), at the basepoint `138`, which stands at level `4` in the band
`[0, 9]`. Both arms are `HighAt (L + 1) (L + 8)`, so the basepoint satisfies every hypothesis of
the branch that `s3_span_nine_except` leaves open, and

* the backward arm never rises to `L + 7` at all and drops to `L + 1` at its step `39`, so it does
  not fold onto the Λ-walk (`not_foldsOnto_lam_armT_mix`);
* the forward arm rises to `L + 7` at its step `31`, having been at `L + 2` only at its step `2`,
  which is too early for the walk, so it does not fold onto the V-walk
  (`not_foldsOnto_vee_armG_mix`).

Neither of the two walks folds both arms (`mix_no_common_walk_of_the_two`). Whatever closes the
branch at `L + 4` must therefore be a third walk, and the last section of this file exhibits one:
both arms fold onto the four-leg walk `L+3 → L+6 → L+1 → L+8` (`mix_served_by_four_leg`). The
census `census-batch43.c` finds that walk serving every mixed pair it meets — all 55 of the
986-link chain `bing 0 9`, which has span exactly nine with both ends attained — and finds no
walk of at most three turns that serves every branch pair.

The band here is `[0, 9]` while the chain itself has span eight, so this basepoint is in fact
served, by `s3_span_eight`. What the witness settles is the *method*: the branch hypotheses of
`s3_span_nine_except` do not imply either criterion, so neither walk can discharge them.
-/

namespace HPC.Fold

/-! ## The basepoint -/

/-- Basepoint `138` of Bing's 409-link chain, at level `4`. -/
def mixBase : Fin 409 := ⟨138, by norm_num⟩

/-- The forward arm from the basepoint: 271 links. -/
def mixG : Fin (409 - mixBase.val) → ℤ := armG ceSeq mixBase

/-- The backward arm from the basepoint: 139 links. -/
def mixT : Fin (mixBase.val + 1) → ℤ := armT ceSeq mixBase

theorem mixBase_level : ceSeq mixBase = 4 := rfl

theorem mixG_zero : mixG ⟨0, by decide⟩ = 4 := rfl
theorem mixT_zero : mixT ⟨0, by decide⟩ = 4 := rfl

theorem mixG_isLip : IsLip mixG := armG_isLip ceSeq_isLip mixBase
theorem mixT_isLip : IsLip mixT := armT_isLip ceSeq_isLip mixBase

theorem mixG_lb : ∀ j, (0 : ℤ) ≤ mixG j := fun _ => ceSeq_lb _
theorem mixT_lb : ∀ j, (0 : ℤ) ≤ mixT j := fun _ => ceSeq_lb _

theorem mixG_ub : ∀ j, mixG j ≤ 9 := fun _ => le_trans (ceSeq_ub _) (by norm_num)
theorem mixT_ub : ∀ j, mixT j ≤ 9 := fun _ => le_trans (ceSeq_ub _) (by norm_num)

/-! ## The basepoint lies in the open branch -/

/-- The forward arm stands at `L + 2` at its step two. -/
theorem mixG_two : mixG ⟨2, by decide⟩ = 2 := rfl

/-- The forward arm does not reach `L + 8` before its step 270. -/
theorem mixG_late_high : ∀ d : Fin (409 - mixBase.val), 8 ≤ mixG d → 2 < d.val := by
  decide +kernel

/-- **The forward arm is `HighAt (L + 1) (L + 8)`.** -/
theorem mixG_highAt : HighAt mixG 1 8 := by
  intro d hd
  exact ⟨⟨2, by decide⟩, mixG_late_high d hd, by rw [mixG_two]; norm_num⟩

/-- The backward arm never rises above `L + 6`. -/
theorem mixT_le_six : ∀ j : Fin (mixBase.val + 1), mixT j ≤ 6 := by decide +kernel

/-- **The backward arm is `HighAt (L + 1) (L + 8)`**, vacuously. -/
theorem mixT_highAt : HighAt mixT 1 8 := by
  intro d hd
  exact absurd (mixT_le_six d) (by omega)

/-! ## The Λ-walk does not fold the backward arm -/

/-- The backward arm drops to `L + 1` at its step thirty-nine. -/
theorem mixT_thirtynine : mixT ⟨39, by decide⟩ = 1 := rfl

/-- The descent profile of the Λ-walk fails on the backward arm: it is at `L + 1` at its step
thirty-nine without ever having stood at `L + 7`. -/
theorem not_critLamProfile_mixT : ¬ CritLamProfile mixT 3 9 := by
  rw [critLamProfile_iff_of_isLip mixT_isLip]
  intro h
  obtain ⟨j, -, -, hj⟩ := h ⟨39, by decide⟩ (by rw [mixT_thirtynine]; norm_num)
  have hk : κ (3 : ℤ) 9 = 8 := by simp only [κ]; omega
  rw [hk] at hj
  exact absurd (mixT_le_six j) (by omega)

/-- **The backward arm does not fold onto the Λ-walk** based at `L + 3` with peak `L + 8`. -/
theorem not_foldsOnto_lam_armT_mix :
    ¬ FoldsOnto mixT (lamLen 3 9 0) (lamCenter 3 9 0) := by
  rw [foldsOnto_lam_iff_profile (by decide) mixT mixT_isLip 3 9 0 (by norm_num)
    (by rw [mixT_zero]; rw [abs_le]; norm_num) mixT_lb mixT_ub]
  exact not_critLamProfile_mixT

/-! ## The V-walk does not fold the forward arm -/

/-- The forward arm rises to `L + 7` at its step thirty-one. -/
theorem mixG_thirtyone : mixG ⟨31, by decide⟩ = 7 := rfl

/-- Before that it has been at `L + 2` only at its step two, which the walk reaches too early:
from its step four on it stays at `L + 3` or above until after step thirty-one. -/
theorem mixG_no_valley_before : ∀ j : Fin (409 - mixBase.val),
    4 ≤ j.val → j.val < 31 → 3 ≤ mixG j := by decide +kernel

/-- The ascent profile of the V-walk fails on the forward arm. -/
theorem not_critVeeProfile_mixG : ¬ CritVeeProfile mixG 5 0 := by
  rw [critVeeProfile_iff_of_isLip mixG_isLip 5 0 (by norm_num)]
  intro h
  obtain ⟨j, hj1, hj2, hj3⟩ := h ⟨31, by decide⟩ (by rw [mixG_thirtyone]; norm_num)
  have h4 : 4 ≤ j.val := by
    have : (4 : ℤ) ≤ (j.val : ℤ) := by omega
    exact_mod_cast this
  have := mixG_no_valley_before j h4 (by omega)
  omega

/-- **The forward arm does not fold onto the V-walk** based at `L + 5` through the valley
`L + 1`. -/
theorem not_foldsOnto_vee_armG_mix :
    ¬ FoldsOnto mixG (veeLen 5 9 0) (veeCenter 5 9 0) := by
  rw [foldsOnto_vee_iff_profile (by decide) mixG mixG_isLip 5 9 0 (by norm_num)
    (by rw [mixG_zero]; rw [abs_le]; norm_num) mixG_lb mixG_ub]
  exact not_critVeeProfile_mixG

/-! ## What the witness says -/

/-- **The open branch at `L + 4` is not served by either of the two walks.** The basepoint `138`
of `ceSeq` satisfies every hypothesis of the branch — the sequence is faithful and crooked, it
lies in the band `[0, 9]`, the basepoint stands at `0 + 4`, and both arms are
`HighAt (L + 1) (L + 8)` — and the Λ-walk based at `L + 3` fails on its backward arm while the
V-walk based at `L + 5` fails on its forward arm. -/
theorem mix_no_common_walk_of_the_two :
    IsLip ceSeq ∧ IsCrookedIvF ceSeq ceSeq ∧
    (∀ t, (0 : ℤ) ≤ ceSeq t) ∧ (∀ t, ceSeq t ≤ 9) ∧
    ceSeq mixBase = 0 + 4 ∧
    HighAt (armG ceSeq mixBase) (0 + 1) (0 + 8) ∧
    HighAt (armT ceSeq mixBase) (0 + 1) (0 + 8) ∧
    ¬ (FoldsOnto (armG ceSeq mixBase) (lamLen 3 9 0) (lamCenter 3 9 0) ∧
       FoldsOnto (armT ceSeq mixBase) (lamLen 3 9 0) (lamCenter 3 9 0)) ∧
    ¬ (FoldsOnto (armG ceSeq mixBase) (veeLen 5 9 0) (veeCenter 5 9 0) ∧
       FoldsOnto (armT ceSeq mixBase) (veeLen 5 9 0) (veeCenter 5 9 0)) := by
  refine ⟨ceSeq_isLip, ceSeq_faithful, fun t => ceSeq_lb t,
    fun t => le_trans (ceSeq_ub t) (by norm_num), rfl,
    by simpa using mixG_highAt, by simpa using mixT_highAt, ?_, ?_⟩
  · rintro ⟨-, h⟩
    exact not_foldsOnto_lam_armT_mix h
  · rintro ⟨h, -⟩
    exact not_foldsOnto_vee_armG_mix h

/-! ## The third walk: the pair is served after all

The census `census-batch43.c` finds every mixed pair it meets served by the four-leg walk
`L+3 → L+6 → L+1 → L+8`, and by no walk of fewer turns. Here that walk is exhibited at the
witness, with the two time-assignments written out: the arms fold onto it, so the basepoint is
served — by a walk the span-nine argument does not yet have. -/

/-- The four-leg walk `L+3 → L+6 → L+1 → L+8`, sixteen centers. -/
def w4list : List ℤ := [3, 4, 5, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8]

/-- The walk as a function of time. -/
def w4 (u : ℕ) : ℤ := w4list.getD u 0

/-- The time-assignment of the forward arm. -/
def betaGlist : List ℕ :=
  [   0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1,
   2, 3, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3,
   4, 5, 4, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 4, 5, 6, 5, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0,
   0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
   0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 1, 0, 1, 2, 1,
   0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 9, 10, 11, 10, 9, 10, 11,
   10, 11, 12, 11, 10, 11, 10, 9, 10, 11, 10, 11, 12, 11, 10, 11, 12, 11, 12, 13, 12, 11, 12, 11, 10, 11, 12, 11, 10, 11,
   10, 9, 10, 11, 10, 11, 12, 11, 10, 11, 12, 11, 12, 13, 12, 11, 12, 11, 10, 11, 12, 11, 12, 13, 12, 11, 12, 13, 12, 13,
   14]

/-- The time-assignment of the backward arm. -/
def betaTlist : List ℕ :=
  [   0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5,
   4, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 4, 5, 6, 5, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 4, 5,
   6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 6, 5,
   6, 7, 6, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 7, 6, 7, 8]

def betaG (u : ℕ) : ℕ := betaGlist.getD u 0
def betaT (u : ℕ) : ℕ := betaTlist.getD u 0

theorem betaG_lt : ∀ j : Fin (409 - mixBase.val), betaG j.val < 16 := by decide +kernel

theorem betaG_step : ∀ j : Fin (409 - mixBase.val), j.val + 1 < 409 - mixBase.val →
    |(betaG (j.val + 1) : ℤ) - (betaG j.val : ℤ)| ≤ 1 := by decide +kernel

theorem betaG_cover : ∀ j : Fin (409 - mixBase.val), |mixG j - w4 (betaG j.val)| ≤ 1 := by
  decide +kernel

theorem betaT_lt : ∀ j : Fin (mixBase.val + 1), betaT j.val < 16 := by decide +kernel

theorem betaT_step : ∀ j : Fin (mixBase.val + 1), j.val + 1 < mixBase.val + 1 →
    |(betaT (j.val + 1) : ℤ) - (betaT j.val : ℤ)| ≤ 1 := by decide +kernel

theorem betaT_cover : ∀ j : Fin (mixBase.val + 1), |mixT j - w4 (betaT j.val)| ≤ 1 := by
  decide +kernel

/-- **The forward arm folds onto the four-leg walk.** -/
theorem foldsOnto_four_leg_mixG : FoldsOnto mixG 16 w4 := by
  refine ⟨fun j => betaG j.val, betaG_lt, ?_, ?_, betaG_cover⟩
  · intro j j' hjj'
    show |(betaG j'.val : ℤ) - (betaG j.val : ℤ)| ≤ 1
    rw [hjj']
    exact betaG_step j (by have := j'.isLt; omega)
  · intro j hj
    show betaG j.val = 0
    rw [hj]
    rfl

/-- **The backward arm folds onto the four-leg walk.** -/
theorem foldsOnto_four_leg_mixT : FoldsOnto mixT 16 w4 := by
  refine ⟨fun j => betaT j.val, betaT_lt, ?_, ?_, betaT_cover⟩
  · intro j j' hjj'
    show |(betaT j'.val : ℤ) - (betaT j.val : ℤ)| ≤ 1
    rw [hjj']
    exact betaT_step j (by have := j'.isLt; omega)
  · intro j hj
    show betaT j.val = 0
    rw [hj]
    rfl

/-- **The witness pair is served — by the third walk.** The two arms of the basepoint that
neither the Λ-walk nor the V-walk folds do fold onto one common walk, the four-leg
`L+3 → L+6 → L+1 → L+8`. -/
theorem mix_served_by_four_leg :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ceSeq mixBase) len c ∧ FoldsOnto (armT ceSeq mixBase) len c :=
  ⟨16, w4, foldsOnto_four_leg_mixG, foldsOnto_four_leg_mixT⟩

end HPC.Fold
