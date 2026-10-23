import HPC.Fold.ClosureF

/-!
# The off-center one-bump family, Bing's chains, and `F2PrimeOff`

Every itinerary proposed in batches 6–23 started at a window centered on the basepoint level
`p`. The schedules that exist at the refuting chains start at a window with `p` on an edge. This
file defines the one-bump family with base center `c₀ ∈ {p − 1, p, p + 1}`, states `F2PrimeOff`
— both arms fold onto one member — and derives Theorem 3 in the block reading from it through
batch 6's bridge, with no `SegLam`.

It also builds Bing's own crooked chains from the recursion behind his Theorem 7 recurrence,
proves the recurrence for that construction, and checks membership of the small ones in the
faithful model. These are the only chains in the repository that reach the inductive case of
Theorem 3; the batch-23 71-term witness is `bing 0 6`.

Evidence for `F2PrimeOff` (§2 of COMMISSION.md, reproduced and extended in REPORT-batch24.md):
no failure at any basepoint of `bing 0 n` for `n ≤ 7`, of the 7 559 subchains of `bing 0 7` of
length ≥ 9 and span ≥ 5 (665 322 basepoints), of the two batch-23 witnesses, or of the faithful
exhaustive corpus to length 9.

English proofs and sketches: COMMISSION.md §3. Delivered: every ordinary item is proved, and
of the search item `f2PrimeOff` the monotone case and a reduction to the combinatorial
statement `OffDichotomy`; `f2PrimeOff` itself is neither proved nor refuted and is kept,
commented out, at the end. No `sorry` remains.
-/

namespace HPC.Fold

/-! ## The family -/

/-- Λ from `c₀`: up to `h`, down to `L + 1`, up to `H − 1`. Returns the length and the walk. -/
def offLam (c₀ h L H : ℤ) : ℕ × (ℕ → ℤ) :=
  let a := (h - c₀).toNat + 1            -- c₀ … h
  let b := (h - 1 - (L + 1)).toNat + 1   -- h−1 … L+1
  let d := (H - 1 - (L + 2)).toNat + 1   -- L+2 … H−1
  (a + b + d, fun u =>
    if u < a then c₀ + u
    else if u < a + b then h - 1 - ((u - a : ℕ) : ℤ)
    else L + 2 + ((u - a - b : ℕ) : ℤ))

/-- V from `c₀`: down to `l`, up to `H − 1`, down to `L + 1`. -/
def offVee (c₀ l L H : ℤ) : ℕ × (ℕ → ℤ) :=
  let a := (c₀ - l).toNat + 1
  let b := (H - 1 - (l + 1)).toNat + 1
  let d := (H - 2 - (L + 1)).toNat + 1
  (a + b + d, fun u =>
    if u < a then c₀ - u
    else if u < a + b then l + 1 + ((u - a : ℕ) : ℤ)
    else H - 2 - ((u - a - b : ℕ) : ℤ))

/-- **`F2PrimeOff`.** Both arms fold onto one member of the off-center family. -/
def F2PrimeOff : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    ∃ c₀ : ℤ, (c₀ = ρ i - 1 ∨ c₀ = ρ i ∨ c₀ = ρ i + 1) ∧ L + 1 ≤ c₀ ∧ c₀ ≤ H - 1 ∧
      ((∃ h, c₀ ≤ h ∧ h ≤ H - 1 ∧
          FoldsOnto (armG ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2 ∧
          FoldsOnto (armT ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2) ∨
       (∃ l, L + 1 ≤ l ∧ l ≤ c₀ ∧
          FoldsOnto (armG ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2 ∧
          FoldsOnto (armT ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2))

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, conditional on `F2PrimeOff`. The
range condition `L + 3 ≤ H` is discharged separately: below it, one or two blocks by level
suffice (batch 9's degenerate branch). -/
theorem theorem3_of_F2PrimeOff (hF2 : F2PrimeOff) {X : Type*} [MetricSpace X] {n k : ℕ}
    (hn : 0 < n) {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  set σ : Fin n → ℤ := fun t => ((href.maxIdx t : ℕ) : ℤ) with hσ
  obtain ⟨tL, -, htL⟩ := Finset.exists_min_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  obtain ⟨tH, -, htH⟩ := Finset.exists_max_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  set L : ℤ := ρ tL with hL
  set H : ℤ := ρ tH with hH
  have hLf : ∀ t, L ≤ ρ t := fun t => htL t (Finset.mem_univ t)
  have hHf : ∀ t, ρ t ≤ H := fun t => htH t (Finset.mem_univ t)
  by_cases hdeg : H ≤ L + 2
  · refine exists_blocks_first_of_range_le_two hn href i (href.minIdx tL).val (fun t => ?_)
    have h1 := hLf t
    have h2 := hHf t
    simp only [hρ, hL, hH] at h1 h2 hdeg
    omega
  · have hcase : L + 3 ≤ H := by omega
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedIvF ρ σ := isCrookedIvF_minIdx_maxIdx hcr
    obtain ⟨c₀, -, -, -, hfold⟩ :=
      hF2 n ρ σ i H L hlip hcrook hLf hHf hcase ⟨tL, hL.symm⟩ ⟨tH, hH.symm⟩
    rcases hfold with ⟨h, -, -, hG, hT⟩ | ⟨l, -, -, hG, hT⟩
    · exact exists_blocks_first_of_folds href i _ _ hG hT
    · exact exists_blocks_first_of_folds href i _ _ hG hT

/-! ## Bing's chains -/

/-- Bing's recursive crooked path from level `a` to level `b`, endpoints included. -/
def bingPath (a b : ℤ) : List ℤ :=
  if _h : |b - a| ≤ 2 then
    if a ≤ b then (List.range (b - a).toNat.succ).map (fun u => a + u)
    else (List.range (a - b).toNat.succ).map (fun u => a - u)
  else if a < b then
    bingPath a (b - 1) ++ (bingPath (b - 1) (a + 1)).tail ++ (bingPath (a + 1) b).tail
  else
    bingPath a (b + 1) ++ (bingPath (b + 1) (a - 1)).tail ++ (bingPath (a - 1) b).tail
termination_by (|b - a|).toNat
decreasing_by
  all_goals (
    simp only [← Int.natCast_natAbs, Int.toNat_natCast] at *
    omega)

/-- The monotone run from `a` to `b`, endpoints included: the base case of `bingPath`. -/
def bingRun (a b : ℤ) : List ℤ :=
  if a ≤ b then (List.range (b - a).toNat.succ).map (fun u => a + u)
  else (List.range (a - b).toNat.succ).map (fun u => a - u)

theorem bingPath_base {a b : ℤ} (h : |b - a| ≤ 2) : bingPath a b = bingRun a b := by
  rw [bingPath, dif_pos h, bingRun]

theorem bingPath_up {a b : ℤ} (h : ¬ |b - a| ≤ 2) (hab : a < b) :
    bingPath a b =
      bingPath a (b - 1) ++ (bingPath (b - 1) (a + 1)).tail ++ (bingPath (a + 1) b).tail := by
  rw [bingPath, dif_neg h, if_pos hab]

theorem bingPath_down {a b : ℤ} (h : ¬ |b - a| ≤ 2) (hab : ¬ a < b) :
    bingPath a b =
      bingPath a (b + 1) ++ (bingPath (b + 1) (a - 1)).tail ++ (bingPath (a - 1) b).tail := by
  rw [bingPath, dif_neg h, if_neg hab]

/-- A fuel-driven, structurally recursive copy of `bingPath`. Well-founded recursion does not
reduce in the kernel, so the concrete chains below are evaluated through this copy. -/
def bingAux : ℕ → ℤ → ℤ → List ℤ
  | 0, a, b => bingRun a b
  | m + 1, a, b =>
      if |b - a| ≤ 2 then bingRun a b
      else if a < b then
        bingAux m a (b - 1) ++ (bingAux m (b - 1) (a + 1)).tail ++ (bingAux m (a + 1) b).tail
      else
        bingAux m a (b + 1) ++ (bingAux m (b + 1) (a - 1)).tail ++ (bingAux m (a - 1) b).tail

/-- The fuel measure, in the form `omega` understands. -/
theorem toNat_abs (x : ℤ) : (|x|).toNat = x.natAbs := by
  simp only [← Int.natCast_natAbs, Int.toNat_natCast]

/-- The base-case test, in the form `omega` understands. -/
theorem abs_le_two_iff (x : ℤ) : |x| ≤ 2 ↔ x.natAbs ≤ 2 := by
  simp only [← Int.natCast_natAbs]
  omega

/-- The fuel bound, in the form the recursive calls need. -/
theorem fuel_le {x : ℤ} {m : ℕ} (h : x.natAbs ≤ m) : (|x|).toNat ≤ m := by
  rw [toNat_abs]; exact h

/-- With enough fuel the copy agrees with `bingPath`. -/
theorem bingPath_eq_aux : ∀ (m : ℕ) (a b : ℤ), (|b - a|).toNat ≤ m → bingPath a b = bingAux m a b
  | 0, a, b, hm => by
      rw [toNat_abs] at hm
      rw [bingPath_base ((abs_le_two_iff _).2 (by omega)), bingAux]
  | m + 1, a, b, hm => by
      rw [toNat_abs] at hm
      by_cases h : |b - a| ≤ 2
      · rw [bingPath_base h, bingAux, if_pos h]
      · have hd : ¬ (b - a).natAbs ≤ 2 := fun hc => h ((abs_le_two_iff _).2 hc)
        by_cases hab : a < b
        · have e1 : bingPath a (b - 1) = bingAux m a (b - 1) :=
            bingPath_eq_aux m a (b - 1) (fuel_le (by omega))
          have e2 : bingPath (b - 1) (a + 1) = bingAux m (b - 1) (a + 1) :=
            bingPath_eq_aux m (b - 1) (a + 1) (fuel_le (by omega))
          have e3 : bingPath (a + 1) b = bingAux m (a + 1) b :=
            bingPath_eq_aux m (a + 1) b (fuel_le (by omega))
          rw [bingPath_up h hab, bingAux, if_neg h, if_pos hab, e1, e2, e3]
        · have e1 : bingPath a (b + 1) = bingAux m a (b + 1) :=
            bingPath_eq_aux m a (b + 1) (fuel_le (by omega))
          have e2 : bingPath (b + 1) (a - 1) = bingAux m (b + 1) (a - 1) :=
            bingPath_eq_aux m (b + 1) (a - 1) (fuel_le (by omega))
          have e3 : bingPath (a - 1) b = bingAux m (a - 1) b :=
            bingPath_eq_aux m (a - 1) b (fuel_le (by omega))
          rw [bingPath_down h hab, bingAux, if_neg h, if_neg hab, e1, e2, e3]

/-- Bing's recurrence, as a function. `z 1 = 2`, `z 2 = 3`. -/
def z : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | n + 3 => 2 * z (n + 2) + z (n + 1) - 2

/-- Every value of the recurrence is positive (needed to take tails). -/
theorem z_pos_aux : ∀ m : ℕ, 1 ≤ z m ∧ 1 ≤ z (m + 1) ∧ 1 ≤ z (m + 2)
  | 0 => ⟨by decide, by decide, by decide⟩
  | m + 1 => by
      obtain ⟨-, h1, h2⟩ := z_pos_aux m
      refine ⟨h1, h2, ?_⟩
      show 1 ≤ z (m + 3)
      have he : z (m + 3) = 2 * z (m + 2) + z (m + 1) - 2 := rfl
      omega

theorem z_pos (m : ℕ) : 1 ≤ z m := (z_pos_aux m).1

/-- The monotone run has the obvious length. -/
theorem bingRun_length (a b : ℤ) : (bingRun a b).length = (b - a).natAbs + 1 := by
  unfold bingRun
  split <;> simp <;> omega

/-- The length of the construction, by induction on the fuel. -/
theorem bingPath_length_aux : ∀ (m : ℕ) (a b : ℤ), (|b - a|).toNat ≤ m →
    (bingPath a b).length = z (b - a).natAbs
  | 0, a, b, hm => by
      rw [toNat_abs] at hm
      rw [bingPath_base ((abs_le_two_iff _).2 (by omega)), bingRun_length]
      have h0 : (b - a).natAbs = 0 := by omega
      rw [h0]
      decide
  | m + 1, a, b, hm => by
      rw [toNat_abs] at hm
      by_cases h : |b - a| ≤ 2
      · rw [bingPath_base h, bingRun_length]
        have hle : (b - a).natAbs ≤ 2 := (abs_le_two_iff _).1 h
        have hcases : (b - a).natAbs = 0 ∨ (b - a).natAbs = 1 ∨ (b - a).natAbs = 2 := by omega
        rcases hcases with h0 | h0 | h0 <;> rw [h0] <;> decide
      · have hd : ¬ (b - a).natAbs ≤ 2 := fun hc => h ((abs_le_two_iff _).2 hc)
        have hz : z (b - a).natAbs
            = 2 * z ((b - a).natAbs - 1) + z ((b - a).natAbs - 2) - 2 := by
          obtain ⟨p, hp⟩ : ∃ p, (b - a).natAbs = p + 3 := ⟨(b - a).natAbs - 3, by omega⟩
          have he : z (p + 3) = 2 * z (p + 2) + z (p + 1) - 2 := rfl
          rw [hp]
          simpa using he
        have p1 := z_pos ((b - a).natAbs - 1)
        have p2 := z_pos ((b - a).natAbs - 2)
        by_cases hab : a < b
        · have e1 := bingPath_length_aux m a (b - 1) (fuel_le (by omega))
          have e2 := bingPath_length_aux m (b - 1) (a + 1) (fuel_le (by omega))
          have e3 := bingPath_length_aux m (a + 1) b (fuel_le (by omega))
          rw [show (b - 1 - a).natAbs = (b - a).natAbs - 1 by omega] at e1
          rw [show (a + 1 - (b - 1)).natAbs = (b - a).natAbs - 2 by omega] at e2
          rw [show (b - (a + 1)).natAbs = (b - a).natAbs - 1 by omega] at e3
          rw [bingPath_up h hab]
          simp only [List.length_append, List.length_tail, e1, e2, e3]
          omega
        · have e1 := bingPath_length_aux m a (b + 1) (fuel_le (by omega))
          have e2 := bingPath_length_aux m (b + 1) (a - 1) (fuel_le (by omega))
          have e3 := bingPath_length_aux m (a - 1) b (fuel_le (by omega))
          rw [show (b + 1 - a).natAbs = (b - a).natAbs - 1 by omega] at e1
          rw [show (a - 1 - (b + 1)).natAbs = (b - a).natAbs - 2 by omega] at e2
          rw [show (b - (a - 1)).natAbs = (b - a).natAbs - 1 by omega] at e3
          rw [bingPath_down h hab]
          simp only [List.length_append, List.length_tail, e1, e2, e3]
          omega

/-- The construction has the length of the recurrence (the content of Bing's Theorem 7 that
concerns the construction; minimality is not claimed here). -/
theorem bingPath_length (a b : ℤ) : (bingPath a b).length = z (|b - a|).toNat := by
  rw [toNat_abs]
  exact bingPath_length_aux (b - a).natAbs a b (fuel_le le_rfl)

theorem z_small : z 3 = 6 ∧ z 4 = 13 ∧ z 5 = 30 ∧ z 6 = 71 ∧ z 7 = 170 ∧ z 8 = 409 := by
  decide

/-- The chain as a sequence. -/
def bing (a b : ℤ) : Fin (bingPath a b).length → ℤ := fun t => (bingPath a b).get t

set_option maxRecDepth 10000 in
/-- `bing 0 4` as a list. -/
theorem bingPath_04 : bingPath 0 4 = [0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4] := by
  rw [bingPath_eq_aux 4 0 4 (by decide)]
  rfl

set_option maxRecDepth 100000 in
/-- `bing 0 5` as a list. -/
theorem bingPath_05 : bingPath 0 5 =
    [0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5] := by
  rw [bingPath_eq_aux 5 0 5 (by decide)]
  rfl

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- `bing 0 4` is a member of the faithful model with `σ = ρ`. -/
theorem bing04_faithful : IsCrookedIvF (bing 0 4) (bing 0 4) := by
  show IsCrookedIvF (fun t => (bingPath 0 4).get t) (fun t => (bingPath 0 4).get t)
  rw [bingPath_04]
  exact isCrookedIvF_of_check2 (by unfold IsCrookedIvFCheck2 ivEnd clampIdx; decide +kernel)

set_option maxRecDepth 40000000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 20000000 in
set_option maxHeartbeats 20000000 in
/-- `bing 0 5` likewise. -/
theorem bing05_faithful : IsCrookedIvF (bing 0 5) (bing 0 5) := by
  show IsCrookedIvF (fun t => (bingPath 0 5).get t) (fun t => (bingPath 0 5).get t)
  rw [bingPath_05]
  exact isCrookedIvF_of_check2 (by unfold IsCrookedIvFCheck2 ivEnd clampIdx; decide +kernel)

set_option maxRecDepth 400000 in
/-- The batch-23 71-term witness is Bing's chain `bing 0 6`. -/
theorem lpSeq_eq_bing06 : (bingPath 0 6).map id = [0,1,2,1,2,3,2,1,2,3,2,3,4,3,2,3,2,1,2,3,2,3,4,3,2,3,4,3,4,5,4,3,4,3,2,3,4,3,2,3,2,1,2,3,2,3,4,3,2,3,4,3,4,5,4,3,4,3,2,3,4,3,4,5,4,3,4,5,4,5,6] := by
  rw [bingPath_eq_aux 6 0 6 (by decide)]
  rfl

/-! ## Two ladders

The two members of the family with `h = c₀`, respectively `l = c₀`, are *ladders*:
`offLam c₀ c₀ L H` descends from `c₀` to the bottom and then climbs to `H - 1`, and
`offVee c₀ c₀ L H` is its reflection. Past the bottom (respectively the top) the climb covers
every level, so an arm that has crossed can be tracked whatever it does; the whole constraint
is the crossing. Two special cases are settled outright here — `p ≤ L + 1` and `H - 1 ≤ p`, in
which the arm never has to cross — and the general crossing criterion is isolated below. -/

/-- A 1-Lipschitz sequence moves by at most the number of steps. -/
theorem abs_sub_le_of_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) :
    ∀ (d : ℕ) (j k : Fin m), k.val = j.val + d → |f k - f j| ≤ (d : ℤ) := by
  intro d
  induction d with
  | zero =>
      intro j k hk
      rw [show k = j from Fin.ext (by omega)]
      simp
  | succ d ih =>
      intro j k hk
      have hd : j.val + d < m := by have := k.isLt; omega
      have h1 := ih j ⟨j.val + d, hd⟩ rfl
      have h2 := hf ⟨j.val + d, hd⟩ k (by show k.val = j.val + d + 1; omega)
      rw [abs_le] at h1 h2 ⊢
      push_cast
      omega

/-- The forward arm starts at the basepoint level. -/
theorem armG_zero {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (j : Fin (n - i.val)) (hj : j.val = 0) :
    armG ρ i j = ρ i := by
  simp only [armG]
  congr 1
  exact Fin.ext (by simp [hj])

/-- The backward arm starts at the basepoint level. -/
theorem armT_zero {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (j : Fin (i.val + 1)) (hj : j.val = 0) :
    armT ρ i j = ρ i := by
  simp only [armT]
  congr 1
  exact Fin.ext (by simp [hj])

/-- **The ascending ladder.** An arm starting at or below `L + 1` folds onto `offLam (L+1)
(H-1) L H`, whose first run is the ladder of centers `L+1, …, H-1`. -/
theorem foldsOnto_lam_ladder {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (L H : ℤ)
    (hLb : ∀ j, L ≤ f j) (hHb : ∀ j, f j ≤ H) (hLH : L + 3 ≤ H)
    (h0 : ∀ j : Fin m, j.val = 0 → f j ≤ L + 1) :
    FoldsOnto f (offLam (L + 1) (H - 1) L H).1 (offLam (L + 1) (H - 1) L H).2 := by
  refine ⟨fun j => (min (f j) (H - 1) - (L + 1)).toNat, ?_, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    have := hLb j; have := hHb j
    simp only [offLam]
    omega
  · intro j j' hjj'
    dsimp only
    have := hf j j' hjj'
    rw [abs_le] at this ⊢
    have := hLb j; have := hHb j; have := hLb j'; have := hHb j'
    omega
  · intro j hj
    dsimp only
    have := h0 j hj
    have := hLb j
    omega
  · intro j
    dsimp only
    have h1 := hLb j; have h2 := hHb j
    simp only [offLam]
    rw [if_pos (by omega), abs_le]
    omega

/-- **The descending ladder.** An arm starting at or above `H - 1` folds onto `offVee (H-1)
(L+1) L H`, whose first run is the ladder of centers `H-1, …, L+1`. -/
theorem foldsOnto_vee_ladder {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (L H : ℤ)
    (hLb : ∀ j, L ≤ f j) (hHb : ∀ j, f j ≤ H) (hLH : L + 3 ≤ H)
    (h0 : ∀ j : Fin m, j.val = 0 → H - 1 ≤ f j) :
    FoldsOnto f (offVee (H - 1) (L + 1) L H).1 (offVee (H - 1) (L + 1) L H).2 := by
  refine ⟨fun j => ((H - 1) - max (f j) (L + 1)).toNat, ?_, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    have := hLb j; have := hHb j
    simp only [offVee]
    omega
  · intro j j' hjj'
    dsimp only
    have := hf j j' hjj'
    rw [abs_le] at this ⊢
    have := hLb j; have := hHb j; have := hLb j'; have := hHb j'
    omega
  · intro j hj
    dsimp only
    have := h0 j hj
    have := hHb j
    omega
  · intro j
    dsimp only
    have h1 := hLb j; have h2 := hHb j
    simp only [offVee]
    rw [if_pos (by omega), abs_le]
    omega

/-- **The monotone case of `F2PrimeOff`.** At a basepoint whose level is within one of an
extreme, one ladder takes both arms, and no crookedness is needed. -/
theorem f2PrimeOff_monotone {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hmono : ρ i ≤ L + 1 ∨ H - 1 ≤ ρ i) :
    ∃ c₀ : ℤ, (c₀ = ρ i - 1 ∨ c₀ = ρ i ∨ c₀ = ρ i + 1) ∧ L + 1 ≤ c₀ ∧ c₀ ≤ H - 1 ∧
      ((∃ h, c₀ ≤ h ∧ h ≤ H - 1 ∧
          FoldsOnto (armG ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2 ∧
          FoldsOnto (armT ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2) ∨
       (∃ l, L + 1 ≤ l ∧ l ≤ c₀ ∧
          FoldsOnto (armG ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2 ∧
          FoldsOnto (armT ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2)) := by
  have hGL : ∀ j, L ≤ armG ρ i j := fun j => hLb _
  have hGH : ∀ j, armG ρ i j ≤ H := fun j => hHb _
  have hTL : ∀ j, L ≤ armT ρ i j := fun j => hLb _
  have hTH : ∀ j, armT ρ i j ≤ H := fun j => hHb _
  have hi := hLb i
  have hi' := hHb i
  rcases hmono with hlow | hhigh
  · refine ⟨L + 1, by omega, le_rfl, by omega, Or.inl ⟨H - 1, by omega, le_rfl, ?_, ?_⟩⟩
    · exact foldsOnto_lam_ladder _ (armG_isLip hlip i) L H hGL hGH hLH
        (fun j hj => by rw [armG_zero ρ i j hj]; omega)
    · exact foldsOnto_lam_ladder _ (armT_isLip hlip i) L H hTL hTH hLH
        (fun j hj => by rw [armT_zero ρ i j hj]; omega)
  · refine ⟨H - 1, by omega, by omega, le_rfl, Or.inr ⟨L + 1, le_rfl, by omega, ?_, ?_⟩⟩
    · exact foldsOnto_vee_ladder _ (armG_isLip hlip i) L H hGL hGH hLH
        (fun j hj => by rw [armG_zero ρ i j hj]; omega)
    · exact foldsOnto_vee_ladder _ (armT_isLip hlip i) L H hTL hTH hLH
        (fun j hj => by rw [armT_zero ρ i j hj]; omega)

/-- **`F2PrimeOff` at span three.** With `H = L + 3` every basepoint level is within one of an
extreme, so the conclusion holds at every basepoint. -/
theorem f2PrimeOff_span_three {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hspan : H = L + 3) :
    ∃ c₀ : ℤ, (c₀ = ρ i - 1 ∨ c₀ = ρ i ∨ c₀ = ρ i + 1) ∧ L + 1 ≤ c₀ ∧ c₀ ≤ H - 1 ∧
      ((∃ h, c₀ ≤ h ∧ h ≤ H - 1 ∧
          FoldsOnto (armG ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2 ∧
          FoldsOnto (armT ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2) ∨
       (∃ l, L + 1 ≤ l ∧ l ≤ c₀ ∧
          FoldsOnto (armG ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2 ∧
          FoldsOnto (armT ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2)) := by
  refine f2PrimeOff_monotone ρ i H L hlip hLb hHb (by omega) ?_
  have := hLb i
  have := hHb i
  omega

/-! ## The crossing criterion, and a reduction of `F2PrimeOff`

The fold onto the V-ladder `offLam c₀ c₀ L H` needs the arm to arrive at the bottom position
*on schedule*: the token starts at position `0` and moves at most one position per index, so
by the index `j` at which it reaches the bottom the arm must have stayed, at each earlier index
`k`, at level at most `min (L+2) c₀ + (j - k)` — the highest level the window it can occupy at
that time contains — and never above `c₀ + 1`. Past the bottom nothing constrains it. -/

/-- The arm reaches the bottom of the V-ladder `offLam c₀ c₀ L H` on schedule: either it stays
inside the descending run's windows throughout, or some index `j`, no earlier than the bottom
position, is reached on schedule. -/
def BottomOnTime {m : ℕ} (f : Fin m → ℤ) (c₀ L : ℤ) : Prop :=
  (∀ k, f k ≤ c₀ + 1) ∨
  ∃ j : Fin m, (c₀ - L - 2).toNat + 1 ≤ j.val ∧
    ∀ k : Fin m, k.val ≤ j.val →
      f k ≤ c₀ + 1 ∧ f k ≤ min (L + 2) c₀ + ((j.val : ℤ) - (k.val : ℤ))

/-- The reflected criterion: the arm reaches the top of the Λ-ladder `offVee c₀ c₀ L H` on
schedule. -/
def TopOnTime {m : ℕ} (f : Fin m → ℤ) (c₀ H : ℤ) : Prop :=
  BottomOnTime (fun k => - f k) (-c₀) (-H)

set_option maxHeartbeats 1000000 in
/-- **The V-ladder fold.** `BottomOnTime` is enough to fold an arm onto `offLam c₀ c₀ L H`. -/
theorem foldsOnto_offLam_self {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (c₀ L H : ℤ)
    (hcL : L + 1 ≤ c₀) (hcH : c₀ ≤ H - 1) (hLH : L + 3 ≤ H)
    (hLb : ∀ k, L ≤ f k) (hHb : ∀ k, f k ≤ H)
    (h0 : ∀ k : Fin m, k.val = 0 → |f k - c₀| ≤ 1)
    (hB : BottomOnTime f c₀ L) :
    FoldsOnto f (offLam c₀ c₀ L H).1 (offLam c₀ c₀ L H).2 := by
  rcases hB with hle | ⟨j, hj, hpre⟩
  · -- the arm never leaves the descending run's windows
    refine ⟨fun k => min k.val ((c₀ - max (f k) (L + 1)).toNat), ?_, ?_, ?_, ?_⟩
    · intro k
      dsimp only
      have := hLb k
      simp only [offLam]
      omega
    · intro k k' hkk'
      dsimp only
      have := hf k k' hkk'
      rw [abs_le] at this ⊢
      have := hLb k; have := hLb k'
      push_cast
      omega
    · intro k hk
      dsimp only
      omega
    · intro k
      dsimp only
      have hl := hLb k
      have hu := hle k
      have hlag : (c₀ : ℤ) - 1 - k.val ≤ f k := by
        have hm : 0 < m := k.pos
        have h0' := h0 ⟨0, hm⟩ rfl
        have := abs_sub_le_of_isLip hf k.val ⟨0, hm⟩ k (by show k.val = 0 + k.val; omega)
        rw [abs_le] at this h0'
        omega
      simp only [offLam]
      split_ifs <;> rw [abs_le] <;> omega
  · -- the arm crosses the bottom on schedule
    refine ⟨fun k => if k.val ≤ j.val
        then min k.val (max ((c₀ - L - 2).toNat + 1 - (j.val - k.val))
          ((c₀ - max (f k) (L + 1)).toNat))
        else min (if f k ≤ L + 1 then (c₀ - L - 2).toNat + 1
                  else (c₀ - L - 2).toNat + 1 + 1 + (min (f k) (H - 1) - (L + 2)).toNat)
          ((c₀ - L - 2).toNat + 1 + (k.val - j.val)), ?_, ?_, ?_, ?_⟩
    · intro k
      dsimp only
      have h1 := hLb k; have h2 := hHb k
      simp only [offLam]
      split_ifs <;> omega
    · intro k k' hkk'
      dsimp only
      have hstep := hf k k' hkk'
      rw [abs_le] at hstep
      have hl1 := hLb k; have hl2 := hLb k'
      have hu1 := hHb k; have hu2 := hHb k'
      by_cases hc : k'.val ≤ j.val
      · rw [if_pos hc, if_pos (by omega), abs_le]
        omega
      · by_cases hc2 : k.val ≤ j.val
        · have hkj : k.val = j.val := by omega
          have hfj := (hpre k (by omega)).2
          rw [if_pos hc2, if_neg hc, abs_le, hkj]
          split_ifs <;> omega
        · rw [if_neg hc2, if_neg hc, abs_le]
          split_ifs <;> omega
    · intro k hk
      dsimp only
      rw [if_pos (by omega)]
      omega
    · intro k
      dsimp only
      have hl := hLb k; have hu := hHb k
      have hm : 0 < m := k.pos
      have h00 := h0 ⟨0, hm⟩ rfl
      rw [abs_le] at h00
      have hd0 := abs_sub_le_of_isLip hf k.val ⟨0, hm⟩ k (by show k.val = 0 + k.val; omega)
      rw [abs_le] at hd0
      simp only [offLam]
      by_cases hc : k.val ≤ j.val
      · rw [if_pos hc]
        have hp := hpre k hc
        split_ifs <;> rw [abs_le] <;> omega
      · rw [if_neg hc]
        have hpj := (hpre j le_rfl).2
        have hdj := abs_sub_le_of_isLip hf (k.val - j.val) j k (by omega)
        rw [abs_le] at hdj
        have hlj := hLb j
        split_ifs <;> rw [abs_le] <;> omega

/-- The Λ-ladder is the reflection of the V-ladder: same length. -/
theorem offVee_self_len (c₀ L H : ℤ) :
    (offVee c₀ c₀ L H).1 = (offLam (-c₀) (-c₀) (-H) (-L)).1 := by
  simp only [offVee, offLam]
  omega

/-- The Λ-ladder is the reflection of the V-ladder: negated walk. -/
theorem offVee_self_walk (c₀ L H : ℤ) :
    (offVee c₀ c₀ L H).2 = fun u => - ((offLam (-c₀) (-c₀) (-H) (-L)).2 u) := by
  funext u
  simp only [offVee, offLam]
  split_ifs <;> omega

/-- **The Λ-ladder fold.** `TopOnTime` is enough to fold an arm onto `offVee c₀ c₀ L H`. -/
theorem foldsOnto_offVee_self {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (c₀ L H : ℤ)
    (hcL : L + 1 ≤ c₀) (hcH : c₀ ≤ H - 1) (hLH : L + 3 ≤ H)
    (hLb : ∀ k, L ≤ f k) (hHb : ∀ k, f k ≤ H)
    (h0 : ∀ k : Fin m, k.val = 0 → |f k - c₀| ≤ 1)
    (hT : TopOnTime f c₀ H) :
    FoldsOnto f (offVee c₀ c₀ L H).1 (offVee c₀ c₀ L H).2 := by
  have hneg : IsLip (fun k => - f k) := by
    intro k k' hkk'
    have := hf k k' hkk'
    simp only [abs_le] at this ⊢
    omega
  rw [offVee_self_len, offVee_self_walk, foldsOnto_neg]
  refine foldsOnto_offLam_self (fun k => - f k) hneg (-c₀) (-H) (-L) (by omega) (by omega)
    (by omega) (fun k => ?_) (fun k => ?_) (fun k hk => ?_) hT
  · show -H ≤ - f k
    have := hHb k
    omega
  · show - f k ≤ -L
    have := hLb k
    omega
  · show |(- f k) - (-c₀)| ≤ 1
    have := h0 k hk
    rw [abs_le] at this ⊢
    omega

/-- **The dichotomy.** At every basepoint, for one of the three base centers, both arms cross
the bottom on schedule, or both cross the top on schedule. This is what is left of
`F2PrimeOff` after the two ladder folds: it fails at no basepoint of the corpus of
COMMISSION.md §2. -/
def OffDichotomy : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    ∃ c₀ : ℤ, (c₀ = ρ i - 1 ∨ c₀ = ρ i ∨ c₀ = ρ i + 1) ∧ L + 1 ≤ c₀ ∧ c₀ ≤ H - 1 ∧
      ((BottomOnTime (armG ρ i) c₀ L ∧ BottomOnTime (armT ρ i) c₀ L) ∨
       (TopOnTime (armG ρ i) c₀ H ∧ TopOnTime (armT ρ i) c₀ H))

/-- **The reduction.** `F2PrimeOff` follows from the dichotomy: the two ladders do the rest. -/
theorem f2PrimeOff_of_offDichotomy (hd : OffDichotomy) : F2PrimeOff := by
  intro n ρ σ i H L hlip hcr hLb hHb hLH hL hH
  obtain ⟨c₀, hc₀, hc₀L, hc₀H, hcase⟩ := hd n ρ σ i H L hlip hcr hLb hHb hLH hL hH
  have hGL : ∀ k, L ≤ armG ρ i k := fun k => hLb _
  have hGH : ∀ k, armG ρ i k ≤ H := fun k => hHb _
  have hTL : ∀ k, L ≤ armT ρ i k := fun k => hLb _
  have hTH : ∀ k, armT ρ i k ≤ H := fun k => hHb _
  have hG0 : ∀ k : Fin (n - i.val), k.val = 0 → |armG ρ i k - c₀| ≤ 1 := by
    intro k hk
    rw [armG_zero ρ i k hk, abs_le]
    omega
  have hT0 : ∀ k : Fin (i.val + 1), k.val = 0 → |armT ρ i k - c₀| ≤ 1 := by
    intro k hk
    rw [armT_zero ρ i k hk, abs_le]
    omega
  refine ⟨c₀, hc₀, hc₀L, hc₀H, ?_⟩
  rcases hcase with ⟨hBG, hBT⟩ | ⟨hTG, hTT⟩
  · exact Or.inl ⟨c₀, le_rfl, hc₀H,
      foldsOnto_offLam_self _ (armG_isLip hlip i) c₀ L H hc₀L hc₀H hLH hGL hGH hG0 hBG,
      foldsOnto_offLam_self _ (armT_isLip hlip i) c₀ L H hc₀L hc₀H hLH hTL hTH hT0 hBT⟩
  · exact Or.inr ⟨c₀, hc₀L, le_rfl,
      foldsOnto_offVee_self _ (armG_isLip hlip i) c₀ L H hc₀L hc₀H hLH hGL hGH hG0 hTG,
      foldsOnto_offVee_self _ (armT_isLip hlip i) c₀ L H hc₀L hc₀H hLH hTL hTH hT0 hTT⟩

-- Commented-out statement `f2PrimeOff`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
