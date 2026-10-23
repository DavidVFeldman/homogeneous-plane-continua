import HPC.Fold.Dichotomy

/-!
# A counterexample to `OffDichotomy`

Batch 24's census of the dichotomy reached induction depth seven: `bing 0 n` for `n ≤ 7`, the
subchains of `bing 0 7`, and the exhaustive faithful corpus to length nine. At depth **eight**
the dichotomy fails. Bing's chain `bing 0 8` — 409 links, levels `0 … 8`, faithful with
`σ = ρ` — has eight basepoints at which no base center `c₀ ∈ {p − 1, p, p + 1}` puts both arms
on time at the bottom or both on time at the top; the first is the basepoint `57`, of level
three. The failure is proved here, unconditionally, from the explicit chain.

What the failure looks like at basepoint `57` (`L = 0`, `H = 8`, `p = 3`; `T` is the backward
arm, 58 links, `G` the forward arm, 352 links):

* `T` rises to `4` at its first step and only reaches level `5`, so it is never on time at the
  top (the top band is `H − 2 = 6`), and it leaves the base window upward before reaching the
  bottom band for `c₀ = 2` and `c₀ = 3`;
* at `c₀ = 4`, `T` *is* on time at the bottom, but `G` is not: `G` climbs to `6` at its
  thirteenth link, above `c₀ + 1 = 5`, while its only earlier visit to the bottom band is at
  index one, too early for the ladder token, which cannot be at the bottom before index
  `c₀ − L − 1 = 3`.

So the reduction of `F2PrimeOff` to `OffDichotomy` is lossy: at this same basepoint
`F2PrimeOff` itself still holds, on the non-self ladder `offLam 2 5 0 8` (verified in the
census of REPORT-batch25.md), which is why nothing proved in batches 6–24 is affected.

The faithfulness of the 409-link chain, `IsCrookedIvF ceSeq ceSeq`, is proved in
`HPC/Fold/DichotomyFaithful.lean`; the refutation of `OffDichotomy` is stated here with it as
an explicit hypothesis, and discharged there (`not_offDichotomy`).
-/

namespace HPC.Fold

/-- Bing's chain `bing 0 8`: the 409 links of the recursive construction from level `0` to
level `8`, as a literal. -/
def ce8 : List ℤ :=
  [0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 
   3, 4, 3, 2, 3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 3, 2, 3, 4, 3, 
   4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 3, 2, 
   3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 
   4, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 
   5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 5, 
   6, 5, 4, 5, 4, 3, 4, 5, 4, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 
   5, 4, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 3, 2, 3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 
   4, 3, 4, 5, 4, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 3, 4, 
   3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 6, 5, 6, 7, 
   6, 5, 6, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 3, 4, 3, 2, 3, 4, 
   3, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 
   4, 5, 6, 5, 4, 5, 4, 3, 4, 5, 4, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 5, 6, 5, 4, 5, 6, 5, 6, 7, 6, 
   5, 6, 7, 6, 7, 8]

set_option maxRecDepth 10000000 in
/-- The literal really is Bing's chain: the recursive construction from level `0` to level `8`
of `HPC/Fold/OffCenter.lean`. -/
theorem ce8_eq_bingPath : bingPath 0 8 = ce8 := by
  rw [bingPath_eq_aux 8 0 8 (by decide)]
  rfl

/-- Its length is the value `z 8 = 409` of Bing's recurrence. -/
theorem ce8_length : ce8.length = 409 := by
  rw [← ce8_eq_bingPath, bingPath_length]
  decide

/-- The counterexample chain, as a sequence. -/
def ceSeq : Fin 409 → ℤ := fun t => ce8.getD t.val 0

/-- The basepoint: index `57`, of level three. -/
def ceBase : Fin 409 := ⟨57, by norm_num⟩

@[simp] theorem ceBase_val : ceBase.val = 57 := rfl

theorem ceSeq_isLip : IsLip ceSeq := by
  unfold IsLip
  decide +kernel

theorem ceSeq_lb : ∀ t, (0 : ℤ) ≤ ceSeq t := by decide +kernel

theorem ceSeq_ub : ∀ t, ceSeq t ≤ 8 := by decide +kernel

theorem ceSeq_attains_bot : ∃ t, ceSeq t = 0 := ⟨⟨0, by norm_num⟩, rfl⟩

theorem ceSeq_attains_top : ∃ t, ceSeq t = 8 := ⟨⟨408, by norm_num⟩, rfl⟩

theorem ceSeq_base : ceSeq ceBase = 3 := rfl

/-! ## The six refutations

The backward arm never reaches the top band, so it is on time at the top for no center; for
`c₀ = 2` and `c₀ = 3` it is not on time at the bottom either, and for `c₀ = 4` it is the
forward arm that fails at the bottom. -/

/-- The backward arm stays at or below level five: it never reaches the top band `H − 2 = 6`. -/
theorem ceT_le_five : ∀ j : Fin (ceBase.val + 1), armT ceSeq ceBase j ≤ 5 := by decide +kernel

/-- The backward arm ends at the bottom level. -/
theorem ceT_last : armT ceSeq ceBase ⟨57, by simp⟩ = 0 := by decide +kernel

/-- The backward arm's first step is upward, to level four. -/
theorem ceT_one : armT ceSeq ceBase ⟨1, by simp⟩ = 4 := by decide +kernel

/-- Its fourth link is at level five. -/
theorem ceT_four : armT ceSeq ceBase ⟨4, by simp⟩ = 5 := by decide +kernel

/-- The forward arm reaches level six at its thirteenth link. -/
theorem ceG_thirteen : armG ceSeq ceBase ⟨13, by simp⟩ = 6 := by decide +kernel

/-- The backward arm is never on time at the top, for any of the three centers. -/
theorem ce_not_topOnTime_T {c : ℤ} (h1 : 2 ≤ c) (h2 : c ≤ 4) :
    ¬ TopOnTime (armT ceSeq ceBase) c 8 := by
  refine not_topOnTime_of_fall ⟨57, by simp⟩ (by rw [ceT_last]; omega) ?_
  intro j _ _
  have h3 := ceT_le_five j
  have h4 : (6 : ℤ) ≤ max (8 - 2) c := le_max_left _ _
  omega

/-- At `c₀ = 2` the backward arm rises above the window at its first step, before any visit to
the bottom band. -/
theorem ce_not_bottomOnTime_T2 : ¬ BottomOnTime (armT ceSeq ceBase) 2 0 := by
  refine not_bottomOnTime_of_rise ⟨1, by simp⟩ (by rw [ceT_one]; omega) ?_
  intro j hj hlt
  have h1 : (⟨1, by simp⟩ : Fin (ceBase.val + 1)).val = 1 := rfl
  omega

/-- At `c₀ = 3` likewise, at the fourth step, the two admissible earlier indices being above
the bottom band. -/
theorem ce_not_bottomOnTime_T3 : ¬ BottomOnTime (armT ceSeq ceBase) 3 0 := by
  refine not_bottomOnTime_of_rise ⟨4, by simp⟩ (by rw [ceT_four]; omega) ?_
  decide +kernel

/-- At `c₀ = 4` the forward arm climbs to level six before it can reach the bottom band on
schedule: its only earlier visit to the band is at index one, and the ladder token cannot be at
the bottom before index three. -/
theorem ce_not_bottomOnTime_G4 : ¬ BottomOnTime (armG ceSeq ceBase) 4 0 := by
  refine not_bottomOnTime_of_rise ⟨13, by simp⟩ (by rw [ceG_thirteen]; omega) ?_
  decide +kernel

/-- **The dichotomy fails at basepoint 57 of `bing 0 8`.** -/
theorem ce_not_offDichotomyAt : ¬ OffDichotomyAt ceSeq ceBase 8 0 := by
  rintro ⟨c₀, hc₀, hcL, hcH, hcase⟩
  rw [ceSeq_base] at hc₀
  have hc : c₀ = 2 ∨ c₀ = 3 ∨ c₀ = 4 := by omega
  rcases hcase with ⟨hBG, hBT⟩ | ⟨hTG, hTT⟩
  · rcases hc with rfl | rfl | rfl
    · exact ce_not_bottomOnTime_T2 hBT
    · exact ce_not_bottomOnTime_T3 hBT
    · exact ce_not_bottomOnTime_G4 hBG
  · rcases hc with rfl | rfl | rfl
    · exact ce_not_topOnTime_T (by norm_num) (by norm_num) hTT
    · exact ce_not_topOnTime_T (by norm_num) (by norm_num) hTT
    · exact ce_not_topOnTime_T (by norm_num) (by norm_num) hTT

/-- **`OffDichotomy` is false**, given the faithfulness of the witness chain (verified
computationally, see the module docstring). -/
theorem not_offDichotomy_of_faithful (hcr : IsCrookedIvF ceSeq ceSeq) : ¬ OffDichotomy := by
  intro hd
  exact ce_not_offDichotomyAt
    (hd 409 ceSeq ceSeq ceBase 8 0 ceSeq_isLip hcr ceSeq_lb ceSeq_ub (by norm_num)
      ceSeq_attains_bot ceSeq_attains_top)

end HPC.Fold
