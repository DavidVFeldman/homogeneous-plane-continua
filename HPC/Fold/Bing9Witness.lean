import HPC.Fold.Bing9

/-!
# The work item `unserved_high8` is false

`HPC/Fold/Bing9.lean` puts Bing's 986-link chain `bing 0 9` into Lean and proves it faithful. This
file reads it at the basepoint `278`, which stands at level `4`, and refutes there the work item
`unserved_high8` of batch 44: *a branch pair folding onto neither canonical walk has, on each arm,
a time at `L + 1` or below before every ascent to `L + 8`.*

The basepoint satisfies every hypothesis of the branch — the chain is faithful and crooked, it
lies in the band `[0, 9]` with both ends attained, the basepoint stands at `0 + 4`, and both arms
are `HighAt (L + 1) (L + 8)` — and neither canonical walk folds both arms:

* the backward arm drops to `L + 1` at its step `39` having never stood above `L + 6`, so the
  Λ-walk based at `L + 3` does not fold it (`not_foldsOnto_lam_b9T`);
* the forward arm rises to `L + 7` at its step `31`, having been at `L + 2` only at its step `2`,
  which the V-walk based at `L + 5` reaches too early (`not_foldsOnto_vee_b9G`).

But the forward arm stands at `L + 8` at its step `130` and never at `L + 1` or below before it:
it stays in `[L + 2, L + 7]` throughout. So the conclusion of the work item fails
(`not_highAt_b9G`, `not_unservedHigh8`).

Thirty-three of the 182 basepoints of the branch of `bing 0 9` refute it the same way
(`census-batch45b.c`). What the three-leg walk of `HPC/Fold/Leg3Deep.lean` really asks at the
ceiling is the weaker announcement `CeilAnn`, which this arm does satisfy, and on which the branch
is re-split in `HPC/Fold/Mixed.lean`.
-/

namespace HPC.Fold

/-! ## The basepoint and its arms -/

/-- Basepoint `278` of `bing 0 9`, at level `4`. -/
def b9Base : Fin 986 := ⟨278, by decide⟩

/-- The forward arm from the basepoint: 708 links. -/
@[simp] theorem b9Base_val : b9Base.val = 278 := rfl

def b9G : Fin (986 - b9Base.val) → ℤ := armG bing9 b9Base

/-- The backward arm from the basepoint: 279 links. -/
def b9T : Fin (b9Base.val + 1) → ℤ := armT bing9 b9Base

theorem b9Base_level : bing9 b9Base = 4 := by decide +kernel

theorem b9G_zero : b9G ⟨0, by decide⟩ = 4 := by decide +kernel
theorem b9T_zero : b9T ⟨0, by decide⟩ = 4 := by decide +kernel

theorem b9G_isLip : IsLip b9G := armG_isLip bing9_isLip b9Base
theorem b9T_isLip : IsLip b9T := armT_isLip bing9_isLip b9Base

theorem b9G_lb : ∀ j, (0 : ℤ) ≤ b9G j := fun _ => bing9_lb _
theorem b9T_lb : ∀ j, (0 : ℤ) ≤ b9T j := fun _ => bing9_lb _
theorem b9G_ub : ∀ j, b9G j ≤ 9 := fun _ => bing9_ub _
theorem b9T_ub : ∀ j, b9T j ≤ 9 := fun _ => bing9_ub _

/-! ## The basepoint lies in the open branch -/

/-- The forward arm stands at `L + 2` at its step two. -/
theorem b9G_two : b9G ⟨2, by decide⟩ = 2 := by decide +kernel

/-- The forward arm does not reach `L + 8` before its step 130. -/
theorem b9G_late_high : ∀ d : Fin (986 - b9Base.val), 8 ≤ b9G d → 2 < d.val := by decide +kernel

/-- **The forward arm is `HighAt (L + 1) (L + 8)`.** -/
theorem b9G_highAt : HighAt b9G 1 8 := by
  intro d hd
  exact ⟨⟨2, by decide⟩, b9G_late_high d hd, by rw [b9G_two]; norm_num⟩

/-- The backward arm never rises above `L + 7`. -/
theorem b9T_le_seven : ∀ j : Fin (b9Base.val + 1), b9T j ≤ 7 := by decide +kernel

/-- **The backward arm is `HighAt (L + 1) (L + 8)`**, vacuously. -/
theorem b9T_highAt : HighAt b9T 1 8 := by
  intro d hd
  exact absurd (b9T_le_seven d) (by omega)

/-! ## The Λ-walk does not fold the backward arm -/

/-- The backward arm drops to `L + 1` at its step thirty-nine. -/
theorem b9T_thirtynine : b9T ⟨39, by decide⟩ = 1 := by decide +kernel

/-- Before that step it never stands above `L + 6`. -/
theorem b9T_before_thirtynine : ∀ j : Fin (b9Base.val + 1), j.val < 39 → b9T j ≤ 6 := by
  decide +kernel

/-- The ascent profile of the Λ-walk fails on the backward arm. -/
theorem not_critLamProfile_b9T : ¬ CritLamProfile b9T 3 9 := by
  rw [critLamProfile_iff_of_isLip b9T_isLip]
  intro h
  obtain ⟨j, hj, -, hjv⟩ := h ⟨39, by decide⟩ (by rw [b9T_thirtynine]; norm_num)
  have hk : κ (3 : ℤ) 9 = 8 := by simp only [κ]; omega
  rw [hk] at hjv
  have := b9T_before_thirtynine j hj
  omega

/-- **The backward arm does not fold onto the Λ-walk** based at `L + 3` with peak `L + 8`. -/
theorem not_foldsOnto_lam_b9T : ¬ FoldsOnto b9T (lamLen 3 9 0) (lamCenter 3 9 0) := by
  rw [foldsOnto_lam_iff_profile (by norm_num) b9T b9T_isLip 3 9 0 (by norm_num)
    (by rw [b9T_zero]; rw [abs_le]; norm_num) b9T_lb b9T_ub]
  exact not_critLamProfile_b9T

/-! ## The V-walk does not fold the forward arm -/

/-- The forward arm rises to `L + 7` at its step thirty-one. -/
theorem b9G_thirtyone : b9G ⟨31, by decide⟩ = 7 := by decide +kernel

/-- From its step four to its step thirty-one it stays at `L + 3` or above, so the only time it
has stood at `L + 2` is its step two, which the V-walk reaches too early. -/
theorem b9G_no_valley_before : ∀ j : Fin (986 - b9Base.val),
    4 ≤ j.val → j.val < 31 → 3 ≤ b9G j := by decide +kernel

/-- The descent profile of the V-walk fails on the forward arm. -/
theorem not_critVeeProfile_b9G : ¬ CritVeeProfile b9G 5 0 := by
  rw [critVeeProfile_iff_of_isLip b9G_isLip 5 0 (by norm_num)]
  intro h
  obtain ⟨j, hj1, hj2, hj3⟩ := h ⟨31, by decide⟩ (by rw [b9G_thirtyone]; norm_num)
  have h4 : 4 ≤ j.val := by
    have : (4 : ℤ) ≤ (j.val : ℤ) := by omega
    exact_mod_cast this
  have := b9G_no_valley_before j h4 (by omega)
  omega

/-- **The forward arm does not fold onto the V-walk** based at `L + 5` through the valley
`L + 1`. -/
theorem not_foldsOnto_vee_b9G : ¬ FoldsOnto b9G (veeLen 5 9 0) (veeCenter 5 9 0) := by
  rw [foldsOnto_vee_iff_profile (by norm_num) b9G b9G_isLip 5 9 0 (by norm_num)
    (by rw [b9G_zero]; rw [abs_le]; norm_num) b9G_lb b9G_ub]
  exact not_critVeeProfile_b9G

/-! ## The ascent that is not announced by the floor -/

/-- The forward arm stands at `L + 8` at its step 130. -/
theorem b9G_onethirty : b9G ⟨130, by decide⟩ = 8 := by decide +kernel

/-- Before that step it never drops to `L + 1`. -/
theorem b9G_before_onethirty : ∀ j : Fin (986 - b9Base.val), j.val < 130 → 2 ≤ b9G j := by
  decide +kernel

/-- **The forward arm is not `HighAt L (L + 8)`.** -/
theorem not_highAt_b9G : ¬ HighAt b9G 0 8 := by
  intro h
  obtain ⟨j, hj, hjv⟩ := h ⟨130, by decide⟩ (le_of_eq b9G_onethirty.symm)
  have := b9G_before_onethirty j hj
  omega

/-! ## The refutation -/

/-- The statement of the batch-44 work item `unserved_high8`: a pair of the open branch at
`L + 4` that folds onto neither canonical walk has, on each arm, a time at `L + 1` or below before
every ascent to `L + 8`. -/
def UnservedHigh8 : Prop :=
  ∀ {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) →
    (∃ t, ρ t = L) → (∃ t, ρ t = L + 9) → ρ i = L + 4 →
    HighAt (armG ρ i) (L + 1) (L + 8) → HighAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)) →
    ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) →
    HighAt (armG ρ i) L (L + 8) ∧ HighAt (armT ρ i) L (L + 8)

/-- **The work item of batch 44 is false.** The basepoint `278` of `bing 0 9` satisfies every one
of its hypotheses and not its conclusion. -/
theorem not_unservedHigh8 : ¬ UnservedHigh8 := by
  intro h
  have hlam : ¬ (FoldsOnto (armG bing9 b9Base) (lamLen (0 + 3) (0 + 9) 0)
      (lamCenter (0 + 3) (0 + 9) 0) ∧
    FoldsOnto (armT bing9 b9Base) (lamLen (0 + 3) (0 + 9) 0) (lamCenter (0 + 3) (0 + 9) 0)) := by
    rintro ⟨-, h2⟩
    exact not_foldsOnto_lam_b9T (by simpa using h2)
  have hvee : ¬ (FoldsOnto (armG bing9 b9Base) (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0) ∧
    FoldsOnto (armT bing9 b9Base) (veeLen (0 + 5) (0 + 9) 0) (veeCenter (0 + 5) (0 + 9) 0)) := by
    rintro ⟨h1, -⟩
    exact not_foldsOnto_vee_b9G (by simpa using h1)
  have := h bing9 bing9 b9Base 0 bing9_isLip bing9_faithful bing9_lb
    (fun t => by simpa using bing9_ub t) bing9_attains_bot (by simpa using bing9_attains_top)
    (by simpa using b9Base_level) (by simpa using b9G_highAt) (by simpa using b9T_highAt)
    hlam hvee
  exact not_highAt_b9G (by simpa using this.1)

end HPC.Fold
