import HPC.Fold.Bing9
import HPC.Fold.Shave

/-!
# Two shaved copies of `bing 0 9`

`HPC/Fold/Shave.lean` proves that lowering a strict local maximum of a faithful sequence by one,
leaving the link's upper end where it was, gives a faithful crooked pair again. This file applies
it twice to Bing's 986-link chain `bing 0 9`:

* `bing9sA` — the peak at index `128`, which stands at level `6` between two links at level `5`,
  is shaved to `5`; the link still meets `6`;
* `bing9sB` — the peak at index `309`, which stands at level `7` between two links at level `6`,
  is shaved to `6`; the link still meets `7`.

Both are genuinely general pairs: `σ ≠ ρ` at one link. Both have span exactly nine with both ends
attained — the shaved link is interior and neither end is touched — so both satisfy every
hypothesis the branch statements of `HPC/Fold/Mixed.lean` make about the sequence.
`HPC/Fold/Bing9ShaveWitness.lean` reads a basepoint of each and refutes there one of the two work
items of that file.
-/

namespace HPC.Fold

/-! ## The peaks -/

/-- The peak of `bing 0 9` at index `128`. -/
def pkA : Fin 986 := ⟨128, by norm_num⟩

/-- The peak of `bing 0 9` at index `309`. -/
def pkB : Fin 986 := ⟨309, by norm_num⟩

theorem bing9_pkA : bing9 pkA = 6 := by decide +kernel
theorem bing9_pkB : bing9 pkB = 7 := by decide +kernel

/-- Both neighbours of the peak `128` stand at level `5`. -/
theorem bing9_nbr_pkA : ∀ u : Fin 986, ((u : ℤ) - (pkA : ℤ)).natAbs = 1 → bing9 u = 5 := by
  decide +kernel

/-- Both neighbours of the peak `309` stand at level `6`. -/
theorem bing9_nbr_pkB : ∀ u : Fin 986, ((u : ℤ) - (pkB : ℤ)).natAbs = 1 → bing9 u = 6 := by
  decide +kernel

/-! ## The two shaved chains -/

/-- `bing 0 9` with the peak at index `128` shaved from `6` to `5`. -/
def bing9sA : Fin 986 → ℤ := fun t => if t.val = 128 then 5 else bing9 t

/-- `bing 0 9` with the peak at index `309` shaved from `7` to `6`. -/
def bing9sB : Fin 986 → ℤ := fun t => if t.val = 309 then 6 else bing9 t

theorem bing9sA_at : bing9sA pkA = bing9 pkA - 1 := by rw [bing9_pkA]; rfl

theorem bing9sB_at : bing9sB pkB = bing9 pkB - 1 := by rw [bing9_pkB]; rfl

theorem bing9sA_off : ∀ u : Fin 986, u ≠ pkA → bing9sA u = bing9 u := by
  intro u hu
  have : u.val ≠ 128 := fun h => hu (Fin.ext h)
  simp [bing9sA, this]

theorem bing9sB_off : ∀ u : Fin 986, u ≠ pkB → bing9sB u = bing9 u := by
  intro u hu
  have : u.val ≠ 309 := fun h => hu (Fin.ext h)
  simp [bing9sB, this]

/-- **The first shaved chain is faithful**, and genuinely general: its link at `128` runs from
level `5` to level `6`. -/
theorem bing9sA_faithful : IsCrookedIvF bing9sA bing9 :=
  isCrookedIvF_shave bing9_faithful pkA rfl
    (fun u hu => by rw [bing9_nbr_pkA u hu, bing9_pkA]; omega) bing9sA_at bing9sA_off

/-- **The second shaved chain is faithful**, and genuinely general: its link at `309` runs from
level `6` to level `7`. -/
theorem bing9sB_faithful : IsCrookedIvF bing9sB bing9 :=
  isCrookedIvF_shave bing9_faithful pkB rfl
    (fun u hu => by rw [bing9_nbr_pkB u hu, bing9_pkB]; omega) bing9sB_at bing9sB_off

theorem bing9sA_isLip : IsLip bing9sA :=
  isLip_shave bing9_isLip pkA (fun u hu => by rw [bing9_nbr_pkA u hu, bing9_pkA]; omega)
    bing9sA_at bing9sA_off

theorem bing9sB_isLip : IsLip bing9sB :=
  isLip_shave bing9_isLip pkB (fun u hu => by rw [bing9_nbr_pkB u hu, bing9_pkB]; omega)
    bing9sB_at bing9sB_off

/-! ## The band -/

theorem bing9sA_lb : ∀ t, (0 : ℤ) ≤ bing9sA t := by
  intro t
  by_cases h : t.val = 128
  · simp [bing9sA, h]
  · simp only [bing9sA, h, if_false]
    exact bing9_lb t

theorem bing9sB_lb : ∀ t, (0 : ℤ) ≤ bing9sB t := by
  intro t
  by_cases h : t.val = 309
  · simp [bing9sB, h]
  · simp only [bing9sB, h, if_false]
    exact bing9_lb t

theorem bing9sA_ub : ∀ t, bing9sA t ≤ 9 := by
  intro t
  by_cases h : t.val = 128
  · simp [bing9sA, h]
  · simp only [bing9sA, h, if_false]
    exact bing9_ub t

theorem bing9sB_ub : ∀ t, bing9sB t ≤ 9 := by
  intro t
  by_cases h : t.val = 309
  · simp [bing9sB, h]
  · simp only [bing9sB, h, if_false]
    exact bing9_ub t

theorem bing9sA_attains_bot : ∃ t, bing9sA t = 0 := ⟨⟨0, by norm_num⟩, by decide +kernel⟩
theorem bing9sA_attains_top : ∃ t, bing9sA t = 9 := ⟨⟨985, by norm_num⟩, by decide +kernel⟩
theorem bing9sB_attains_bot : ∃ t, bing9sB t = 0 := ⟨⟨0, by norm_num⟩, by decide +kernel⟩
theorem bing9sB_attains_top : ∃ t, bing9sB t = 9 := ⟨⟨985, by norm_num⟩, by decide +kernel⟩

/-- The first shaved chain differs from its own link data: at `128` the point sequence stands at
`5` while the link meets `6`. So the pair is **not** thin. -/
theorem bing9sA_not_thin : ¬ ∀ u, bing9 u = bing9sA u := by
  intro h
  have := h pkA
  rw [bing9_pkA] at this
  exact absurd this (by decide +kernel)

/-- The second shaved chain is not thin either. -/
theorem bing9sB_not_thin : ¬ ∀ u, bing9 u = bing9sB u := by
  intro h
  have := h pkB
  rw [bing9_pkB] at this
  exact absurd this (by decide +kernel)

end HPC.Fold
