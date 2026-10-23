import HPC.Fold.Bing9Shave

/-!
# Both work items of the branch `L + 4` are false in the general model

`HPC/Fold/Mixed.lean` leaves the branch `L + 4` resting on two work items — a pair of the branch
that folds onto neither canonical walk announces, on each arm, its ascents to `L + 8`
(`unserved_ceiling`) and its descents to `L + 1` (`unserved_valley`). Both are theorems for a
**thin** sequence (`HPC/Fold/MixedThin.lean`). This file refutes both in the **general** model, on
the two shaved copies of `bing 0 9` of `HPC/Fold/Bing9Shave.lean`.

## The valley item

`bing9sA` — `bing 0 9` with the peak at index `128` shaved from `6` to `5` — at its basepoint
`138`, which stands at level `4`. Both arms are `HighAt (L + 1) (L + 8)`; the Λ-walk fails on the
backward arm, which drops to `L + 1` at its step `39` having never stood above `L + 5`, and the
V-walk fails on the forward arm, which rises to `L + 7` at its step `31` having stood at `L + 2`
only at its step `2`. So the pair folds onto neither canonical walk — and the backward arm's
descent at step `39` is announced by nothing: before it the arm stays in `[L + 2, L + 5]`, so
there is neither an earlier time at `L + 6` nor an earlier descent to `L + 1` followed by a time
at `L + 5`.

The single shaved link is what does it: unshaved, that arm stands at `L + 6` at its step `10`,
which announces the descent. Shaved, the link still *meets* `L + 6` — the crookedness clause is
satisfied exactly as before — but the point sequence does not stand there.

## The ceiling item

`bing9sB` — `bing 0 9` with the peak at index `309` shaved from `7` to `6` — at its basepoint
`336`. Again both arms are `HighAt (L + 1) (L + 8)` and neither canonical walk folds both: the
Λ-walk fails on the backward arm (first descent to `L + 1` at its step `97`, never above `L + 6`
before it) and the V-walk on the forward arm (first ascent to `L + 7` at its step `31`, at
`L + 2` only at its step `2`). The forward arm then rises to `L + 8` at its step `72` with none of
the three announcements: before that step it never drops below `L + 2`, and after its first time
at `L + 7`, which is its step `31`, it never drops to `L + 2` again before the ascent.

## What survives

Every pair the censuses of batch 46 met is still served by a walk of at most three legs, so the
branch itself is not refuted — only the two statements through which `HPC/Fold/Mixed.lean` reached
it. See `census-batch46d.c` and `census-batch46e.c`.
-/

namespace HPC.Fold

/-! ## The valley witness: `bing9sA` at its basepoint `138` -/

/-- Basepoint `138` of the first shaved chain, at level `4`. -/
def sABase : Fin 986 := ⟨138, by norm_num⟩

@[simp] theorem sABase_val : sABase.val = 138 := rfl

/-- The forward arm from the basepoint: 848 links. -/
def sAG : Fin (986 - sABase.val) → ℤ := armG bing9sA sABase

/-- The backward arm from the basepoint: 139 links. -/
def sAT : Fin (sABase.val + 1) → ℤ := armT bing9sA sABase

theorem sABase_level : bing9sA sABase = 4 := by decide +kernel

theorem sAG_zero : sAG ⟨0, by decide⟩ = 4 := by decide +kernel
theorem sAT_zero : sAT ⟨0, by decide⟩ = 4 := by decide +kernel

theorem sAG_isLip : IsLip sAG := armG_isLip bing9sA_isLip sABase
theorem sAT_isLip : IsLip sAT := armT_isLip bing9sA_isLip sABase

theorem sAG_lb : ∀ j, (0 : ℤ) ≤ sAG j := fun _ => bing9sA_lb _
theorem sAT_lb : ∀ j, (0 : ℤ) ≤ sAT j := fun _ => bing9sA_lb _
theorem sAG_ub : ∀ j, sAG j ≤ 9 := fun _ => bing9sA_ub _
theorem sAT_ub : ∀ j, sAT j ≤ 9 := fun _ => bing9sA_ub _

/-- The forward arm stands at `L + 2` at its step two. -/
theorem sAG_two : sAG ⟨2, by decide⟩ = 2 := by decide +kernel

/-- The forward arm does not reach `L + 8` before its step three. -/
theorem sAG_late_high : ∀ d : Fin (986 - sABase.val), 8 ≤ sAG d → 2 < d.val := by decide +kernel

/-- **The forward arm is `HighAt (L + 1) (L + 8)`.** -/
theorem sAG_highAt : HighAt sAG 1 8 := by
  intro d hd
  exact ⟨⟨2, by decide⟩, sAG_late_high d hd, by rw [sAG_two]; norm_num⟩

/-- The backward arm never rises above `L + 6`. -/
theorem sAT_le_six : ∀ j : Fin (sABase.val + 1), sAT j ≤ 6 := by decide +kernel

/-- **The backward arm is `HighAt (L + 1) (L + 8)`**, vacuously. -/
theorem sAT_highAt : HighAt sAT 1 8 := by
  intro d hd
  exact absurd (sAT_le_six d) (by omega)

/-- The backward arm drops to `L + 1` at its step thirty-nine. -/
theorem sAT_thirtynine : sAT ⟨39, by decide⟩ = 1 := by decide +kernel

/-- Before that step it stays in `[L + 2, L + 5]`. -/
theorem sAT_before_thirtynine : ∀ j : Fin (sABase.val + 1), j.val < 39 →
    2 ≤ sAT j ∧ sAT j ≤ 5 := by decide +kernel

/-- The ascent profile of the Λ-walk fails on the backward arm. -/
theorem not_critLamProfile_sAT : ¬ CritLamProfile sAT 3 9 := by
  rw [critLamProfile_iff_of_isLip sAT_isLip]
  intro h
  obtain ⟨j, hj, -, hjv⟩ := h ⟨39, by decide⟩ (by rw [sAT_thirtynine]; norm_num)
  have hk : κ (3 : ℤ) 9 = 8 := by simp only [κ]; omega
  rw [hk] at hjv
  have := (sAT_before_thirtynine j hj).2
  omega

/-- **The Λ-walk does not fold the backward arm.** -/
theorem not_foldsOnto_lam_sAT : ¬ FoldsOnto sAT (lamLen 3 9 0) (lamCenter 3 9 0) := by
  rw [foldsOnto_lam_iff_profile (by norm_num) sAT sAT_isLip 3 9 0 (by norm_num)
    (by rw [sAT_zero]; rw [abs_le]; norm_num) sAT_lb sAT_ub]
  exact not_critLamProfile_sAT

/-- The forward arm rises to `L + 7` at its step thirty-one. -/
theorem sAG_thirtyone : sAG ⟨31, by decide⟩ = 7 := by decide +kernel

/-- From its step four to its step thirty-one the forward arm stays at `L + 3` or above. -/
theorem sAG_no_valley_before : ∀ j : Fin (986 - sABase.val),
    4 ≤ j.val → j.val < 31 → 3 ≤ sAG j := by decide +kernel

/-- The descent profile of the V-walk fails on the forward arm. -/
theorem not_critVeeProfile_sAG : ¬ CritVeeProfile sAG 5 0 := by
  rw [critVeeProfile_iff_of_isLip sAG_isLip 5 0 (by norm_num)]
  intro h
  obtain ⟨j, hj1, hj2, hj3⟩ := h ⟨31, by decide⟩ (by rw [sAG_thirtyone]; norm_num)
  have h4 : 4 ≤ j.val := by
    have : (4 : ℤ) ≤ (j.val : ℤ) := by omega
    exact_mod_cast this
  have := sAG_no_valley_before j h4 (by omega)
  omega

/-- **The V-walk does not fold the forward arm.** -/
theorem not_foldsOnto_vee_sAG : ¬ FoldsOnto sAG (veeLen 5 9 0) (veeCenter 5 9 0) := by
  rw [foldsOnto_vee_iff_profile (by norm_num) sAG sAG_isLip 5 9 0 (by norm_num)
    (by rw [sAG_zero]; rw [abs_le]; norm_num) sAG_lb sAG_ub]
  exact not_critVeeProfile_sAG

/-- **The backward arm does not announce its descent at step thirty-nine.** Before it the arm
stays in `[L + 2, L + 5]`: there is no earlier time at `L + 6`, and no earlier descent to `L + 1`
at all, so neither form of the valley announcement holds. -/
theorem not_valleyAnn_sAT :
    ¬ (∀ d : Fin (sABase.val + 1), sAT d ≤ 1 →
        (∃ k : Fin (sABase.val + 1), k.val < d.val ∧ 6 ≤ sAT k) ∨
        (∃ k k' : Fin (sABase.val + 1), k.val < k'.val ∧ k'.val < d.val ∧
          sAT k ≤ 1 ∧ 5 ≤ sAT k')) := by
  intro h
  rcases h ⟨39, by decide⟩ (by rw [sAT_thirtynine]) with ⟨k, hk, hkv⟩ | ⟨k, k', hkk', hk', hkv, -⟩
  · have := (sAT_before_thirtynine k hk).2
    omega
  · have hk39 : k'.val < 39 := hk'
    have := (sAT_before_thirtynine k (by omega)).1
    omega

/-! ## The ceiling witness: `bing9sB` at its basepoint `336` -/

/-- Basepoint `336` of the second shaved chain, at level `4`. -/
def sBBase : Fin 986 := ⟨336, by norm_num⟩

@[simp] theorem sBBase_val : sBBase.val = 336 := rfl

/-- The forward arm from the basepoint: 650 links. -/
def sBG : Fin (986 - sBBase.val) → ℤ := armG bing9sB sBBase

/-- The backward arm from the basepoint: 337 links. -/
def sBT : Fin (sBBase.val + 1) → ℤ := armT bing9sB sBBase

theorem sBBase_level : bing9sB sBBase = 4 := by decide +kernel

theorem sBG_zero : sBG ⟨0, by decide⟩ = 4 := by decide +kernel
theorem sBT_zero : sBT ⟨0, by decide⟩ = 4 := by decide +kernel

theorem sBG_isLip : IsLip sBG := armG_isLip bing9sB_isLip sBBase
theorem sBT_isLip : IsLip sBT := armT_isLip bing9sB_isLip sBBase

theorem sBG_lb : ∀ j, (0 : ℤ) ≤ sBG j := fun _ => bing9sB_lb _
theorem sBT_lb : ∀ j, (0 : ℤ) ≤ sBT j := fun _ => bing9sB_lb _
theorem sBG_ub : ∀ j, sBG j ≤ 9 := fun _ => bing9sB_ub _
theorem sBT_ub : ∀ j, sBT j ≤ 9 := fun _ => bing9sB_ub _

/-- The forward arm stands at `L + 2` at its step two. -/
theorem sBG_two : sBG ⟨2, by decide⟩ = 2 := by decide +kernel

/-- The forward arm does not reach `L + 8` before its step three. -/
theorem sBG_late_high : ∀ d : Fin (986 - sBBase.val), 8 ≤ sBG d → 2 < d.val := by decide +kernel

/-- **The forward arm is `HighAt (L + 1) (L + 8)`.** -/
theorem sBG_highAt : HighAt sBG 1 8 := by
  intro d hd
  exact ⟨⟨2, by decide⟩, sBG_late_high d hd, by rw [sBG_two]; norm_num⟩

/-- The backward arm never rises above `L + 7`. -/
theorem sBT_le_seven : ∀ j : Fin (sBBase.val + 1), sBT j ≤ 7 := by decide +kernel

/-- **The backward arm is `HighAt (L + 1) (L + 8)`**, vacuously. -/
theorem sBT_highAt : HighAt sBT 1 8 := by
  intro d hd
  exact absurd (sBT_le_seven d) (by omega)

/-- The backward arm drops to `L + 1` at its step ninety-seven. -/
theorem sBT_ninetyseven : sBT ⟨97, by decide⟩ = 1 := by decide +kernel

/-- Before that step it never stands above `L + 6`. -/
theorem sBT_before_ninetyseven : ∀ j : Fin (sBBase.val + 1), j.val < 97 → sBT j ≤ 6 := by
  decide +kernel

/-- The ascent profile of the Λ-walk fails on the backward arm. -/
theorem not_critLamProfile_sBT : ¬ CritLamProfile sBT 3 9 := by
  rw [critLamProfile_iff_of_isLip sBT_isLip]
  intro h
  obtain ⟨j, hj, -, hjv⟩ := h ⟨97, by decide⟩ (by rw [sBT_ninetyseven]; norm_num)
  have hk : κ (3 : ℤ) 9 = 8 := by simp only [κ]; omega
  rw [hk] at hjv
  have := sBT_before_ninetyseven j hj
  omega

/-- **The Λ-walk does not fold the backward arm.** -/
theorem not_foldsOnto_lam_sBT : ¬ FoldsOnto sBT (lamLen 3 9 0) (lamCenter 3 9 0) := by
  rw [foldsOnto_lam_iff_profile (by norm_num) sBT sBT_isLip 3 9 0 (by norm_num)
    (by rw [sBT_zero]; rw [abs_le]; norm_num) sBT_lb sBT_ub]
  exact not_critLamProfile_sBT

/-- The forward arm rises to `L + 7` at its step thirty-one. -/
theorem sBG_thirtyone : sBG ⟨31, by decide⟩ = 7 := by decide +kernel

/-- From its step four to its step thirty-one the forward arm stays at `L + 3` or above. -/
theorem sBG_no_valley_before : ∀ j : Fin (986 - sBBase.val),
    4 ≤ j.val → j.val < 31 → 3 ≤ sBG j := by decide +kernel

/-- The descent profile of the V-walk fails on the forward arm. -/
theorem not_critVeeProfile_sBG : ¬ CritVeeProfile sBG 5 0 := by
  rw [critVeeProfile_iff_of_isLip sBG_isLip 5 0 (by norm_num)]
  intro h
  obtain ⟨j, hj1, hj2, hj3⟩ := h ⟨31, by decide⟩ (by rw [sBG_thirtyone]; norm_num)
  have h4 : 4 ≤ j.val := by
    have : (4 : ℤ) ≤ (j.val : ℤ) := by omega
    exact_mod_cast this
  have := sBG_no_valley_before j h4 (by omega)
  omega

/-- **The V-walk does not fold the forward arm.** -/
theorem not_foldsOnto_vee_sBG : ¬ FoldsOnto sBG (veeLen 5 9 0) (veeCenter 5 9 0) := by
  rw [foldsOnto_vee_iff_profile (by norm_num) sBG sBG_isLip 5 9 0 (by norm_num)
    (by rw [sBG_zero]; rw [abs_le]; norm_num) sBG_lb sBG_ub]
  exact not_critVeeProfile_sBG

/-- The forward arm stands at `L + 8` at its step seventy-two. -/
theorem sBG_seventytwo : sBG ⟨72, by decide⟩ = 8 := by decide +kernel

/-- Before that step the arm never drops below `L + 2`. -/
theorem sBG_before_seventytwo : ∀ j : Fin (986 - sBBase.val), j.val < 72 → 2 ≤ sBG j := by
  decide +kernel

/-- Its first time at `L + 7` before that step is its step thirty-one, and from there to the
ascent it stays at `L + 3` or above. -/
theorem sBG_window_seventytwo : ∀ j : Fin (986 - sBBase.val), j.val < 72 →
    (7 ≤ sBG j → 31 ≤ j.val) ∧ (31 < j.val → 3 ≤ sBG j) := by decide +kernel

/-- **The forward arm does not announce its ascent at step seventy-two.** It never drops to
`L + 1` or below before it, which kills the first and the third form of the announcement, and
every time at `L + 7` before it is at step thirty-one or later, after which the arm stays at
`L + 3` or above, which kills the second. -/
theorem not_ceilAnn_sBG : ¬ CeilAnn sBG 0 := by
  intro h
  rcases h ⟨72, by decide⟩ (by rw [sBG_seventytwo]; norm_num) with
    ⟨k, hk, hkv⟩ | ⟨k, k', hkk', hk', hkv, hk'v⟩ | ⟨k, k', k'', hkk', hk'k'', hk'', hkv, -, -⟩
  · have hk72 : k.val < 72 := hk
    have := sBG_before_seventytwo k hk72
    omega
  · have hk72 : k'.val < 72 := hk'
    have h1 := (sBG_window_seventytwo k (by omega)).1 hkv
    have h2 := (sBG_window_seventytwo k' hk72).2 (by omega)
    omega
  · have hk72 : k''.val < 72 := hk''
    have := sBG_before_seventytwo k (by omega)
    omega

/-! ## The two refutations -/

/-- The statement of the work item `unserved_ceiling` of `HPC/Fold/Mixed.lean`. -/
def UnservedCeiling : Prop :=
  ∀ {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) →
    (∃ t, ρ t = L) → (∃ t, ρ t = L + 9) → ρ i = L + 4 →
    HighAt (armG ρ i) (L + 1) (L + 8) → HighAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)) →
    ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) →
    CeilAnn (armG ρ i) L ∧ CeilAnn (armT ρ i) L

/-- The statement of the work item `unserved_valley` of `HPC/Fold/Mixed.lean`. -/
def UnservedValley : Prop :=
  ∀ {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) →
    (∃ t, ρ t = L) → (∃ t, ρ t = L + 9) → ρ i = L + 4 →
    HighAt (armG ρ i) (L + 1) (L + 8) → HighAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)) →
    ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
       FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) →
    (∀ d : Fin (m - i.val), armG ρ i d ≤ L + 1 →
      (∃ k : Fin (m - i.val), k.val < d.val ∧ L + 6 ≤ armG ρ i k) ∨
      (∃ k k' : Fin (m - i.val), k.val < k'.val ∧ k'.val < d.val ∧
        armG ρ i k ≤ L + 1 ∧ L + 5 ≤ armG ρ i k')) ∧
    (∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      (∃ k : Fin (i.val + 1), k.val < d.val ∧ L + 6 ≤ armT ρ i k) ∨
      (∃ k k' : Fin (i.val + 1), k.val < k'.val ∧ k'.val < d.val ∧
        armT ρ i k ≤ L + 1 ∧ L + 5 ≤ armT ρ i k'))

/-- **The ceiling work item is false in the general model.** The basepoint `336` of the shaved
chain `bing9sB` satisfies every hypothesis and not the conclusion. -/
theorem not_unservedCeiling : ¬ UnservedCeiling := by
  intro h
  have hlam : ¬ (FoldsOnto (armG bing9sB sBBase) (lamLen (0 + 3) (0 + 9) 0)
      (lamCenter (0 + 3) (0 + 9) 0) ∧
    FoldsOnto (armT bing9sB sBBase) (lamLen (0 + 3) (0 + 9) 0)
      (lamCenter (0 + 3) (0 + 9) 0)) := by
    rintro ⟨-, h2⟩
    exact not_foldsOnto_lam_sBT (by simpa [sBT] using h2)
  have hvee : ¬ (FoldsOnto (armG bing9sB sBBase) (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0) ∧
    FoldsOnto (armT bing9sB sBBase) (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0)) := by
    rintro ⟨h1, -⟩
    exact not_foldsOnto_vee_sBG (by simpa [sBG] using h1)
  have := h bing9sB bing9 sBBase 0 bing9sB_isLip bing9sB_faithful bing9sB_lb
    (fun t => by simpa using bing9sB_ub t) bing9sB_attains_bot (by simpa using bing9sB_attains_top)
    (by simpa using sBBase_level) (by simpa [sBG] using sBG_highAt) (by simpa [sBT] using sBT_highAt)
    hlam hvee
  exact not_ceilAnn_sBG (by simpa [sBG] using this.1)

/-- **The valley work item is false in the general model.** The basepoint `138` of the shaved
chain `bing9sA` satisfies every hypothesis and not the conclusion. -/
theorem not_unservedValley : ¬ UnservedValley := by
  intro h
  have hlam : ¬ (FoldsOnto (armG bing9sA sABase) (lamLen (0 + 3) (0 + 9) 0)
      (lamCenter (0 + 3) (0 + 9) 0) ∧
    FoldsOnto (armT bing9sA sABase) (lamLen (0 + 3) (0 + 9) 0)
      (lamCenter (0 + 3) (0 + 9) 0)) := by
    rintro ⟨-, h2⟩
    exact not_foldsOnto_lam_sAT (by simpa [sAT] using h2)
  have hvee : ¬ (FoldsOnto (armG bing9sA sABase) (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0) ∧
    FoldsOnto (armT bing9sA sABase) (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0)) := by
    rintro ⟨h1, -⟩
    exact not_foldsOnto_vee_sAG (by simpa [sAG] using h1)
  have := h bing9sA bing9 sABase 0 bing9sA_isLip bing9sA_faithful bing9sA_lb
    (fun t => by simpa using bing9sA_ub t) bing9sA_attains_bot (by simpa using bing9sA_attains_top)
    (by simpa using sABase_level) (by simpa [sAG] using sAG_highAt) (by simpa [sAT] using sAT_highAt)
    hlam hvee
  exact not_valleyAnn_sAT (by simpa [sAT] using this.2)

end HPC.Fold
