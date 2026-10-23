import HPC.Fold.CrossWitness

/-!
# The refuted pair is served, by the reflected walk

`HPC/Fold/CrossWitness.lean` refutes `unserved_leg3deep` at the basepoint `336` of `bing9sB`: the
pair is unserved and its forward arm does not fold onto the third walk `L+3 → L+6 → L+1 → L+8`.
This file shows that the pair is nevertheless **served** — by the reflection of that walk,

```
w₄ = L+3 → L+2 → L+8 → L+1,   leg3Walk' L (L+9) (L+7) (L+2),   fifteen times,
```

whose levels above `L` are `3,2,3,4,5,6,7,8,7,6,5,4,3,2,1`. So what the refutation takes away is
one walk, not the branch: `s3_span_nine_mid4` is re-split in `HPC/Fold/Mixed.lean` on
`unserved_three_walks`, which offers three walks instead of one, and this is the first pair at
which the second of the three is needed.

The folds are exhibited rather than derived: an itinerary is given for each arm, as a base-sixteen
numeral in the manner of `bing9Nat`, and the three conditions of `FoldsOnto` — the positions stay
inside the walk, they move by at most one per step, and each is within one of the arm's level —
are checked by the kernel.
-/

namespace HPC.Fold

/-! ## The two itineraries -/

/-- The itinerary of the forward arm onto `w₄`: 650 walk positions, base sixteen. -/
def sBw4GNat : ℕ := 220226785461834509617175729748578602544224066912211512269044994340520478159620356243197129655341983390317643225922301691372274052418655873625996301403754827192915750239983256270337993571134668823804471971378360710830249510955641307199644520269118751798396266756732861288621527675493497821662424246009589390597049363692579543687189362534162738478043285449408558554894721681057351527186127668723627238825246589610257951361083797528634474908999899454821984910948461093490387251300596207945824354242599172029197815292950395588779990528772060214900635183901981704660204418568463650641000674457761244084809369626776411573426680887705378561855502313580916565642557769241369528179575088802775152943963359842175832275277616714551529758974537538044117306394328305707676382336184309812120518656

/-- The walk position of the forward arm at its step `i`. -/
def sBw4G (i : ℕ) : ℕ := (sBw4GNat >>> (4 * i)) &&& 15

/-- The itinerary of the backward arm onto `w₄`: 337 walk positions, base sixteen. -/
def sBw4TNat : ℕ := 5707069300571120151498168958785588824791324467329967194060679169851893854034196279499618734849258651964898695348163731518920431336011656971185191954664950750592443386610533005817417895233025277186008772737008936723291817431858639915951456316658959575435618756414212679802265065078903834796221195304870883544423445501402285023400007916412343779410814627480959551995822276111821118841338362452282293301162512

/-- The walk position of the backward arm at its step `i`. -/
def sBw4T (i : ℕ) : ℕ := (sBw4TNat >>> (4 * i)) &&& 15

/-- The reflected walk of the branch has fifteen times. -/
theorem leg3Len_w4 : leg3Len 0 (0 + 9) (0 + 7) (0 + 7) = 15 := by
  simp only [leg3Len]
  omega

/-! ## The step conditions, read along the itinerary -/

def sBw4GStepChk : Bool :=
  (List.range 649).all fun i =>
    decide (sBw4G (i + 1) ≤ sBw4G i + 1 ∧ sBw4G i ≤ sBw4G (i + 1) + 1)

set_option maxRecDepth 10000000 in
theorem sBw4GStepChk_true : sBw4GStepChk = true := by decide +kernel

def sBw4TStepChk : Bool :=
  (List.range 336).all fun i =>
    decide (sBw4T (i + 1) ≤ sBw4T i + 1 ∧ sBw4T i ≤ sBw4T (i + 1) + 1)

set_option maxRecDepth 10000000 in
theorem sBw4TStepChk_true : sBw4TStepChk = true := by decide +kernel

theorem sBw4G_step : ∀ i : ℕ, i + 1 < 650 →
    sBw4G (i + 1) ≤ sBw4G i + 1 ∧ sBw4G i ≤ sBw4G (i + 1) + 1 := by
  have h := sBw4GStepChk_true
  rw [sBw4GStepChk, List.all_eq_true] at h
  intro i hi
  have := h i (List.mem_range.2 (by omega))
  simpa using this

theorem sBw4T_step : ∀ i : ℕ, i + 1 < 337 →
    sBw4T (i + 1) ≤ sBw4T i + 1 ∧ sBw4T i ≤ sBw4T (i + 1) + 1 := by
  have h := sBw4TStepChk_true
  rw [sBw4TStepChk, List.all_eq_true] at h
  intro i hi
  have := h i (List.mem_range.2 (by omega))
  simpa using this

/-! ## The two folds -/

set_option maxRecDepth 10000000 in
theorem sBw4G_lt : ∀ j : Fin (986 - sBBase.val), sBw4G j.val < 15 := by decide +kernel

set_option maxRecDepth 10000000 in
theorem sBw4T_lt : ∀ j : Fin (sBBase.val + 1), sBw4T j.val < 15 := by decide +kernel

set_option maxRecDepth 10000000 in
theorem sBw4G_zero : ∀ j : Fin (986 - sBBase.val), j.val = 0 → sBw4G j.val = 0 := by
  decide +kernel

set_option maxRecDepth 10000000 in
theorem sBw4T_zero : ∀ j : Fin (sBBase.val + 1), j.val = 0 → sBw4T j.val = 0 := by
  decide +kernel

set_option maxRecDepth 10000000 in
theorem sBw4G_val : ∀ j : Fin (986 - sBBase.val),
    |sBG j - leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2) (sBw4G j.val)| ≤ 1 := by decide +kernel

set_option maxRecDepth 10000000 in
theorem sBw4T_val : ∀ j : Fin (sBBase.val + 1),
    |sBT j - leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2) (sBw4T j.val)| ≤ 1 := by decide +kernel

/-- **The forward arm folds onto the reflected walk.** -/
theorem foldsOnto_w4_sBG :
    FoldsOnto sBG (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
      (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2)) := by
  refine ⟨fun j => sBw4G j.val, ?_, ?_, sBw4G_zero, sBw4G_val⟩
  · intro j
    rw [leg3Len_w4]
    exact sBw4G_lt j
  · intro j j' hjj'
    have hj' : j'.val < 650 := j'.isLt
    have := sBw4G_step j.val (by omega)
    show |((sBw4G j'.val : ℤ)) - ((sBw4G j.val : ℤ))| ≤ 1
    rw [hjj', abs_le]
    omega

/-- **The backward arm folds onto the reflected walk.** -/
theorem foldsOnto_w4_sBT :
    FoldsOnto sBT (leg3Len 0 (0 + 9) (0 + 7) (0 + 7))
      (leg3Walk' 0 (0 + 9) (0 + 7) (0 + 2)) := by
  refine ⟨fun j => sBw4T j.val, ?_, ?_, sBw4T_zero, sBw4T_val⟩
  · intro j
    rw [leg3Len_w4]
    exact sBw4T_lt j
  · intro j j' hjj'
    have hj' : j'.val < 337 := j'.isLt
    have := sBw4T_step j.val (by omega)
    show |((sBw4T j'.val : ℤ)) - ((sBw4T j.val : ℤ))| ≤ 1
    rw [hjj', abs_le]
    omega

/-- **The pair the refutation is about is served after all.** Both arms of the basepoint `336` of
`bing9sB` fold onto `L+3 → L+2 → L+8 → L+1`, so `s3_span_nine_mid4` holds at that basepoint even
though the third walk misses it. -/
theorem sB_served :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG bing9sB sBBase) len c ∧ FoldsOnto (armT bing9sB sBBase) len c :=
  ⟨_, _, foldsOnto_w4_sBG, foldsOnto_w4_sBT⟩

end HPC.Fold
