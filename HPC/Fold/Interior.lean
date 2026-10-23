import HPC.Fold.Minimal

/-!
# The interior case of `S3ZigFree`

Batch 29 closed every basepoint within two of an extreme and reduced the rest to the interior
(`s3ZigFree_of_interior`), and showed the reduction sharp: the straight descent `6,5,4,3,2,1,0`
based at its middle admits no walk of unit steps at all, so the interior needs crookedness.
Batch 30 supplies what crookedness gives — length. Between a link at `L` and a later link at `H`
a faithful crooked sequence has at least `2(H − L) − 1` indices (`timing_slack'`), while a
unit-step walk crosses the band in `H − L − 2`. The token has slack at every span.

What remains is to turn slack into a walk. `s3ZigFreeInterior` is **not** proved here and no
counterexample to it was found; it is kept, commented out, at the end, and nothing in the file
depends on it. What is delivered:

* the timing items: `armG_index_gap` and `armT_index_gap`, the arm-index forms of
  `index_gap_of_level_gap'`, and from them `arm_timing`, `arm_timing_back` and
  `both_arms_timing`. The commissioned `arm_timing` is false as stated — `not_armTimingClaim`
  refutes it on `cutSeq` — and is replaced by the same statement with the interior hypotheses of
  `both_arms_timing`, under which the bound is `z 3 − 1 = 5`, not `2`;
* the two one-turn walks based at the basepoint's own level, `veeAt` and `lamAt`, their
  membership in the free family, their values (`zigWalk_veeAt_val_down`, `zigWalk_veeAt_val_up`
  and mirrors) and the tracking folds onto them (`foldsOnto_veeAt`, `foldsOnto_lamAt`) — the
  interior analogue of batch 29's ladders — with the two interior cases they settle
  (`s3ZigFreeInterior_descentFirst`, `s3ZigFreeInterior_ascentFirst`);
* why they are not all of it: the first leg of such a walk is one-sided
  (`foldsOnto_veeAt_descent_first`, `foldsOnto_lamAt_ascent_first`), so a basepoint whose two
  arms make opposite demands on the token — one needing it above the base early, the other
  below — is served by no one-turn walk (`not_oneTurn_of_opposite`). The census finds such
  basepoints from span eight on;
* the induction step for walks with more legs: `zigWalk_cons_length`, `zigWalk_cons_val_tail`
  and `foldsOnto_prefixLeg`, which prefix one leg to a walk and to a fold.

English sketch: COMMISSION-batch31.md §3; the census is `census-batch31.c` with its output in
`census-batch31.log`; the results are in REPORT-batch31.md.
-/

namespace HPC.Fold

/-- **The interior case.** What `s3ZigFree_of_interior` reduces `S3ZigFree` to. -/
def S3ZigFreeInterior : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2

/-! ## Timing along an arm

`index_gap_of_level_gap'` reads on the two arms of a basepoint: an arm that has moved `d`
levels has spent at least `z d − 1` indices doing it. -/

/-- **The forward arm's timing.** The arm-index form of `index_gap_of_level_gap'`: the level
the forward arm has reached at arm-index `j` is at level distance at most `z⁻¹ (j+1)` from the
basepoint. Stated as the bound on `z`, which is how it is used. -/
theorem armG_index_gap {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (i : Fin n)
    (j : Fin (n - i.val)) : z (|armG ρ i j - ρ i|).toNat ≤ j.val + 1 := by
  have hi := i.isLt
  have hj := j.isLt
  have hidx : i.val + j.val < n := by omega
  rcases Nat.eq_zero_or_pos j.val with h0 | hpos
  · have heq : (⟨i.val + j.val, hidx⟩ : Fin n) = i := Fin.ext (by simp [h0])
    have he : armG ρ i j = ρ i := congrArg ρ heq
    have hz : z 0 = 1 := rfl
    rw [he, sub_self]
    simp only [abs_zero, Int.toNat_zero, hz]
    omega
  · have hlt : i < (⟨i.val + j.val, hidx⟩ : Fin n) := Fin.lt_def.mpr (by simp; omega)
    have hg := index_gap_of_level_gap' hf i ⟨i.val + j.val, hidx⟩ hlt
    have hsub : (⟨i.val + j.val, hidx⟩ : Fin n).val - i.val = j.val := by simp
    rw [hsub] at hg
    exact hg

/-- **The backward arm's timing.** The mirror image of `armG_index_gap`. -/
theorem armT_index_gap {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (i : Fin n)
    (j : Fin (i.val + 1)) : z (|armT ρ i j - ρ i|).toNat ≤ j.val + 1 := by
  have hi := i.isLt
  have hj := j.isLt
  have hidx : i.val - j.val < n := by omega
  rcases Nat.eq_zero_or_pos j.val with h0 | hpos
  · have heq : (⟨i.val - j.val, hidx⟩ : Fin n) = i := Fin.ext (by simp [h0])
    have he : armT ρ i j = ρ i := congrArg ρ heq
    have hz : z 0 = 1 := rfl
    rw [he, sub_self]
    simp only [abs_zero, Int.toNat_zero, hz]
    omega
  · have hlt : (⟨i.val - j.val, hidx⟩ : Fin n) < i :=
      Fin.lt_def.mpr (show i.val - j.val < i.val by omega)
    have hg := index_gap_of_level_gap' hf ⟨i.val - j.val, hidx⟩ i hlt
    have hsub : i.val - (⟨i.val - j.val, hidx⟩ : Fin n).val = j.val := by simp; omega
    rw [hsub] at hg
    have habs : |ρ i - armT ρ i j| = |armT ρ i j - ρ i| := abs_sub_comm _ _
    show z (|armT ρ i j - ρ i|).toNat ≤ j.val + 1
    rw [← habs]
    exact hg

-- Commented-out statement `arm_timing` removed in batch 103; see `LEDGER.md`.

/-- The commissioned statement of `arm_timing`, as a `Prop`, so that it can be refuted. -/
def ArmTimingClaim : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (L H : ℤ), IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H → ∀ (i : Fin n) (j : Fin (n - i.val)),
      (armG ρ i j = L ∨ armG ρ i j = H) →
      (H - L - 2).toNat ≤ j.val ∨ ρ i = L ∨ ρ i = H

/-- **The commissioned `arm_timing` is false**: a basepoint one level below the top reaches the
top at arm-index `1`, and `H − L − 2` exceeds `1` at every span above four. -/
theorem not_armTimingClaim : ¬ ArmTimingClaim := by
  intro h
  have hb : (armG cutSeq (⟨11, by norm_num⟩ : Fin 37) (⟨1, by norm_num⟩ : Fin (37 - 11)) = 3 ∨
      armG cutSeq (⟨11, by norm_num⟩ : Fin 37) (⟨1, by norm_num⟩ : Fin (37 - 11)) = 7) := by
    decide
  have := h 37 cutSeq cutSeq 3 7 cutSeq_faithful (by decide) (by decide) (by norm_num)
    (⟨11, by norm_num⟩ : Fin 37) (⟨1, by norm_num⟩ : Fin (37 - 11)) hb
  revert this
  decide

/-- **The forward arm's timing at an interior basepoint.** The arm-local form of
`timing_slack'`, which is what a fold construction consumes: an arm of a faithful crooked
sequence based three or more levels inside the band cannot reach an extreme before arm-index
`z 3 − 1 = 5`.

This is the commissioned `arm_timing` with the interior hypotheses on `ρ i` added — without
them it is false (`not_armTimingClaim`) — and with the bound that the timing argument gives.
`hLb`, `hHb` and `hLH` are those of the commissioned statement; the proof does not need them,
the interior hypotheses being what carries the argument. -/
theorem arm_timing {n : ℕ} {ρ σ : Fin n → ℤ} (L H : ℤ) (hf : IsCrookedIvF ρ σ) (i : Fin n)
    (hlo : L + 3 ≤ ρ i) (hhi : ρ i ≤ H - 3)
    (j : Fin (n - i.val)) (hj : armG ρ i j = L ∨ armG ρ i j = H) :
    5 ≤ j.val := by
  have hg := armG_index_gap hf i j
  have habs : 3 ≤ |armG ρ i j - ρ i| := by
    rcases hj with h | h <;> rw [h]
    · rw [abs_sub_comm, abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  have h3 : 3 ≤ (|armG ρ i j - ρ i|).toNat := by omega
  have hlin := z_gt_linear _ h3
  omega

/-- **The backward arm's timing at an interior basepoint**, the mirror image of `arm_timing`. -/
theorem arm_timing_back {n : ℕ} {ρ σ : Fin n → ℤ} (L H : ℤ) (hf : IsCrookedIvF ρ σ) (i : Fin n)
    (hlo : L + 3 ≤ ρ i) (hhi : ρ i ≤ H - 3)
    (j : Fin (i.val + 1)) (hj : armT ρ i j = L ∨ armT ρ i j = H) :
    5 ≤ j.val := by
  have hg := armT_index_gap hf i j
  have habs : 3 ≤ |armT ρ i j - ρ i| := by
    rcases hj with h | h <;> rw [h]
    · rw [abs_sub_comm, abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  have h3 : 3 ≤ (|armT ρ i j - ρ i|).toNat := by omega
  have hlin := z_gt_linear _ h3
  omega

/-- **The two arms cannot both reach an extreme early**, as commissioned. The bound the proof
gives is `5`, not `2` (`arm_timing`, `arm_timing_back`); the hypotheses `hLb`, `hHb` and `hLH`
of the commissioned statement are not needed, the interior hypotheses on `ρ i` being what
carries the argument, and are kept because the statement asks for them. -/
theorem both_arms_timing {n : ℕ} {ρ σ : Fin n → ℤ} (L H : ℤ) (hf : IsCrookedIvF ρ σ)
    (_hLb : ∀ t, L ≤ ρ t) (_hHb : ∀ t, ρ t ≤ H) (_hLH : L + 3 ≤ H) (i : Fin n)
    (hlo : L + 3 ≤ ρ i) (hhi : ρ i ≤ H - 3) :
    (∀ j : Fin (n - i.val), armG ρ i j = L ∨ armG ρ i j = H → 2 ≤ j.val) ∧
    (∀ j : Fin (i.val + 1), armT ρ i j = L ∨ armT ρ i j = H → 2 ≤ j.val) :=
  ⟨fun j hj => le_trans (by norm_num) (arm_timing L H hf i hlo hhi j hj),
   fun j hj => le_trans (by norm_num) (arm_timing_back L H hf i hlo hhi j hj)⟩

/-! ## The two walks based at an interior level

`ladderUp` and `ladderDown` (batch 29) are the walks based at an extreme band, and
`FoldsOnto` pins the walk's first level to within one of the basepoint's, so an interior
basepoint needs a walk that starts at its own level. `veeAt L H b` descends from `b` to `L + 1`
and then sweeps to `H − 1`; `lamAt L H b` is its mirror image. Both are in the free family for
every `b` strictly inside the band — the exemption of the first amplitude is again exactly what
allows it, the first leg being shorter than the sweep that follows.
-/

/-- The vee walk based at `b`: down to `L + 1`, then up to `H − 1`. -/
def veeAt (L H b : ℤ) : List ℤ := [b, L + 1, H - 1]

/-- The lam walk based at `b`: up to `H − 1`, then down to `L + 1`. -/
def lamAt (L H b : ℤ) : List ℤ := [b, H - 1, L + 1]

theorem isZigFree_veeAt (L H b : ℤ) (hLH : L + 3 ≤ H) (hb1 : L + 2 ≤ b) (hb2 : b ≤ H - 1) :
    IsZigFree L H (veeAt L H b) := by
  refine ⟨?_, by simp [veeAt], ?_, ?_, ?_⟩
  · intro t ht
    simp only [veeAt, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> omega
  · intro j hj
    simp only [veeAt, List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    norm_num [veeAt]
    nlinarith
  · intro j hj hj'
    simp only [veeAt, List.length_cons, List.length_nil] at hj'
    omega
  · left
    norm_num [veeAt]

theorem isZigFree_lamAt (L H b : ℤ) (hLH : L + 3 ≤ H) (hb1 : L + 1 ≤ b) (hb2 : b ≤ H - 2) :
    IsZigFree L H (lamAt L H b) := by
  refine ⟨?_, by simp [lamAt], ?_, ?_, ?_⟩
  · intro t ht
    simp only [lamAt, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> omega
  · intro j hj
    simp only [lamAt, List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    norm_num [lamAt]
    nlinarith
  · intro j hj hj'
    simp only [lamAt, List.length_cons, List.length_nil] at hj'
    omega
  · right
    norm_num [lamAt]

/-! ### The values of the two walks -/

theorem zigLevels_veeAt (L H b : ℤ) :
    zigLevels (veeAt L H b) = b :: (stepRun b (L + 1) ++ stepRun (L + 1) (H - 1)) := by
  simp [veeAt, zigLevels, zigTail]

theorem zigLevels_lamAt (L H b : ℤ) :
    zigLevels (lamAt L H b) = b :: (stepRun b (H - 1) ++ stepRun (H - 1) (L + 1)) := by
  simp [lamAt, zigLevels, zigTail]

theorem zigWalk_veeAt_length (L H b : ℤ) (hLH : L + 3 ≤ H) (hb : L + 1 ≤ b) :
    (zigWalk (veeAt L H b)).1 = (b - L - 1).toNat + (H - L - 2).toNat + 1 := by
  simp [zigWalk, zigLevels_veeAt, stepRun_length]
  omega

theorem zigWalk_lamAt_length (L H b : ℤ) (hLH : L + 3 ≤ H) (hb : b ≤ H - 1) :
    (zigWalk (lamAt L H b)).1 = (H - 1 - b).toNat + (H - L - 2).toNat + 1 := by
  simp [zigWalk, zigLevels_lamAt, stepRun_length]
  omega

/-- On its first leg the vee at `b` is at level `b − u` at time `u`. -/
theorem zigWalk_veeAt_val_down (L H b : ℤ) (hb : L + 1 ≤ b) (u : ℕ)
    (hu : u ≤ (b - L - 1).toNat) : (zigWalk (veeAt L H b)).2 u = b - u := by
  rw [zigWalk]
  simp only [zigLevels_veeAt]
  cases u with
  | zero => simp
  | succ k =>
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by rw [stepRun_length]; omega),
        stepRun_getD_down _ k b (by omega) (by omega)]
      push_cast
      ring

/-- On its second leg the vee at `b` is at level `L + 1 + v` at time `(b − L − 1) + v`. -/
theorem zigWalk_veeAt_val_up (L H b : ℤ) (hLH : L + 3 ≤ H) (hb : L + 1 ≤ b) (v : ℕ)
    (hv : v ≤ (H - L - 2).toNat) :
    (zigWalk (veeAt L H b)).2 ((b - L - 1).toNat + v) = L + 1 + v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · rw [Nat.add_zero, zigWalk_veeAt_val_down L H b hb _ le_rfl]
    push_cast
    omega
  · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    have hlen : (stepRun b (L + 1)).length = (b - L - 1).toNat := by
      rw [stepRun_length]; omega
    rw [zigWalk]
    simp only [zigLevels_veeAt]
    rw [show (b - L - 1).toNat + (w + 1) = ((b - L - 1).toNat + w) + 1 from by omega,
      List.getD_cons_succ, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
      show (b - L - 1).toNat + w - (b - L - 1).toNat = w from by omega,
      stepRun_getD_up _ w (L + 1) (by omega) (by omega)]
    push_cast
    ring

/-- On its first leg the lam at `b` is at level `b + u` at time `u`. -/
theorem zigWalk_lamAt_val_up (L H b : ℤ) (hb : b ≤ H - 1) (u : ℕ)
    (hu : u ≤ (H - 1 - b).toNat) : (zigWalk (lamAt L H b)).2 u = b + u := by
  rw [zigWalk]
  simp only [zigLevels_lamAt]
  cases u with
  | zero => simp
  | succ k =>
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by rw [stepRun_length]; omega),
        stepRun_getD_up _ k b (by omega) (by omega)]
      push_cast
      ring

/-- On its second leg the lam at `b` is at level `H − 1 − v` at time `(H − 1 − b) + v`. -/
theorem zigWalk_lamAt_val_down (L H b : ℤ) (hLH : L + 3 ≤ H) (hb : b ≤ H - 1) (v : ℕ)
    (hv : v ≤ (H - L - 2).toNat) :
    (zigWalk (lamAt L H b)).2 ((H - 1 - b).toNat + v) = H - 1 - v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · rw [Nat.add_zero, zigWalk_lamAt_val_up L H b hb _ le_rfl]
    push_cast
    omega
  · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    have hlen : (stepRun b (H - 1)).length = (H - 1 - b).toNat := by
      rw [stepRun_length]; omega
    rw [zigWalk]
    simp only [zigLevels_lamAt]
    rw [show (H - 1 - b).toNat + (w + 1) = ((H - 1 - b).toNat + w) + 1 from by omega,
      List.getD_cons_succ, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
      show (H - 1 - b).toNat + w - (H - 1 - b).toNat = w from by omega,
      stepRun_getD_down _ w (H - 1) (by omega) (by omega)]
    push_cast
    ring

/-! ### Tracking on the two walks -/

/-- **Tracking on the vee.** An arm confined to `[L, H]` that starts at `b` and stays at or
below `b + 1` until it first reaches `L + 1` folds onto `veeAt L H b`: the token follows the
arm's level down the first leg and, from the arm's first visit to `L + 1` onwards, along the
sweep, clamped to the band. The hypothesis is exactly what the first leg can serve: while the
token is on it the walk offers no level above `b`. -/
theorem foldsOnto_veeAt {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (L H b : ℤ) (hLH : L + 3 ≤ H)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) (hb1 : L + 2 ≤ b) (hb2 : b ≤ H - 1)
    (h0 : ∀ j : Fin m, j.val = 0 → f j = b)
    (hpre : ∀ j : Fin m, (∀ j' : Fin m, j'.val ≤ j.val → L + 2 ≤ f j') → f j ≤ b + 1) :
    FoldsOnto f (zigWalk (veeAt L H b)).1 (zigWalk (veeAt L H b)).2 := by
  classical
  set A : Fin m → Prop := fun j => ∃ j' : Fin m, j'.val ≤ j.val ∧ f j' ≤ L + 1 with hAdef
  have hAmono : ∀ j j' : Fin m, j.val ≤ j'.val → A j → A j' := by
    rintro j j' hjj' ⟨k, hk, hkv⟩
    exact ⟨k, by omega, hkv⟩
  have hnotA : ∀ j : Fin m, ¬ A j → L + 2 ≤ f j ∧ f j ≤ b + 1 := by
    intro j hj
    have hall : ∀ j' : Fin m, j'.val ≤ j.val → L + 2 ≤ f j' := by
      intro j' hj'
      by_contra hc
      exact hj ⟨j', hj', by omega⟩
    exact ⟨hall j le_rfl, hpre j hall⟩
  refine ⟨fun j => if A j then (b - L - 1).toNat + min (f j - (L + 1)).toNat (H - L - 2).toNat
      else min (b - f j).toNat (b - L - 1).toNat, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [zigWalk_veeAt_length L H b hLH (by omega)]
    by_cases hj : A j
    · simp only [if_pos hj]; omega
    · simp only [if_neg hj]; omega
  · intro j j' hjj'
    have h1 := hf j j' hjj'
    rw [abs_le] at h1
    by_cases hj : A j
    · have hj' : A j' := hAmono j j' (by omega) hj
      simp only [if_pos hj, if_pos hj']
      rw [abs_le]
      push_cast
      omega
    · by_cases hj2 : A j'
      · obtain ⟨k, hk, hkv⟩ := hj2
        have hkj : k.val = j'.val := by
          by_contra hc
          exact hj ⟨k, by omega, hkv⟩
        have hkeq : k = j' := Fin.ext hkj
        rw [hkeq] at hkv
        have hfj := (hnotA j hj).1
        simp only [if_neg hj, if_pos (hAmono j' j' le_rfl ⟨j', le_rfl, hkv⟩)]
        rw [abs_le]
        push_cast
        omega
      · have hb := hnotA j hj
        have hb' := hnotA j' hj2
        simp only [if_neg hj, if_neg hj2]
        rw [abs_le]
        push_cast
        omega
  · intro j hj0
    have hfj : f j = b := h0 j hj0
    have hnA : ¬ A j := by
      rintro ⟨k, hk, hkv⟩
      have hkeq : k = j := Fin.ext (by omega)
      rw [hkeq, hfj] at hkv
      omega
    simp only [if_neg hnA, hfj]
    simp
  · intro j
    by_cases hj : A j
    · simp only [if_pos hj]
      rw [zigWalk_veeAt_val_up L H b hLH (by omega) _ (min_le_right _ _), abs_le]
      have := hL j
      have := hH j
      omega
    · obtain ⟨hlo2, hhi2⟩ := hnotA j hj
      simp only [if_neg hj]
      rw [zigWalk_veeAt_val_down L H b (by omega) _ (min_le_right _ _), abs_le]
      omega

/-- **Tracking on the lam**, the mirror image of `foldsOnto_veeAt`. -/
theorem foldsOnto_lamAt {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (L H b : ℤ) (hLH : L + 3 ≤ H)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) (hb1 : L + 1 ≤ b) (hb2 : b ≤ H - 2)
    (h0 : ∀ j : Fin m, j.val = 0 → f j = b)
    (hpre : ∀ j : Fin m, (∀ j' : Fin m, j'.val ≤ j.val → f j' ≤ H - 2) → b - 1 ≤ f j) :
    FoldsOnto f (zigWalk (lamAt L H b)).1 (zigWalk (lamAt L H b)).2 := by
  classical
  set A : Fin m → Prop := fun j => ∃ j' : Fin m, j'.val ≤ j.val ∧ H - 1 ≤ f j' with hAdef
  have hAmono : ∀ j j' : Fin m, j.val ≤ j'.val → A j → A j' := by
    rintro j j' hjj' ⟨k, hk, hkv⟩
    exact ⟨k, by omega, hkv⟩
  have hnotA : ∀ j : Fin m, ¬ A j → f j ≤ H - 2 ∧ b - 1 ≤ f j := by
    intro j hj
    have hall : ∀ j' : Fin m, j'.val ≤ j.val → f j' ≤ H - 2 := by
      intro j' hj'
      by_contra hc
      exact hj ⟨j', hj', by omega⟩
    exact ⟨hall j le_rfl, hpre j hall⟩
  refine ⟨fun j => if A j then (H - 1 - b).toNat + min (H - 1 - f j).toNat (H - L - 2).toNat
      else min (f j - b).toNat (H - 1 - b).toNat, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [zigWalk_lamAt_length L H b hLH (by omega)]
    by_cases hj : A j
    · simp only [if_pos hj]; omega
    · simp only [if_neg hj]; omega
  · intro j j' hjj'
    have h1 := hf j j' hjj'
    rw [abs_le] at h1
    by_cases hj : A j
    · have hj' : A j' := hAmono j j' (by omega) hj
      simp only [if_pos hj, if_pos hj']
      rw [abs_le]
      push_cast
      omega
    · by_cases hj2 : A j'
      · obtain ⟨k, hk, hkv⟩ := hj2
        have hkj : k.val = j'.val := by
          by_contra hc
          exact hj ⟨k, by omega, hkv⟩
        have hkeq : k = j' := Fin.ext hkj
        rw [hkeq] at hkv
        have hfj := (hnotA j hj).1
        simp only [if_neg hj, if_pos (hAmono j' j' le_rfl ⟨j', le_rfl, hkv⟩)]
        rw [abs_le]
        push_cast
        omega
      · have hb := hnotA j hj
        have hb' := hnotA j' hj2
        simp only [if_neg hj, if_neg hj2]
        rw [abs_le]
        push_cast
        omega
  · intro j hj0
    have hfj : f j = b := h0 j hj0
    have hnA : ¬ A j := by
      rintro ⟨k, hk, hkv⟩
      have hkeq : k = j := Fin.ext (by omega)
      rw [hkeq, hfj] at hkv
      omega
    simp only [if_neg hnA, hfj]
    simp
  · intro j
    by_cases hj : A j
    · simp only [if_pos hj]
      rw [zigWalk_lamAt_val_down L H b hLH (by omega) _ (min_le_right _ _), abs_le]
      have := hL j
      have := hH j
      omega
    · obtain ⟨hhi2, hlo2⟩ := hnotA j hj
      simp only [if_neg hj]
      rw [zigWalk_lamAt_val_up L H b (by omega) _ (min_le_right _ _), abs_le]
      omega

/-! ### The first leg is one-sided

The hypothesis of `foldsOnto_veeAt` is not far from necessary, and the reason is the shape of
the walk: while the token is on the first leg of the vee the walk offers no level above `b`, so
an arm that rises two above `b` must have brought the token past the foot of the leg first, and
the token is at the foot only when the arm is within one of `L + 1`. This is what makes the
interior case hard: a basepoint whose forward arm rises two above the base before coming within
one of `L + 1`, and whose backward arm falls two below the base before coming within one of
`H − 1`, is served by no one-turn walk at all. The census finds basepoints served by no one-turn walk
from span eight on — 8 of the 319 interior basepoints of `bing 0 8`, and 9 755 of the 13 635 of
`bing 0 12`, over the three admissible bases `ρ i` and `ρ i ± 1`. -/

/-- **The vee's first leg is one-sided.** An arm that rises two above the base of the vee has
already come within one of the foot of the first leg. -/
theorem foldsOnto_veeAt_descent_first {m : ℕ} (f : Fin m → ℤ) (L H b : ℤ) (hb1 : L + 2 ≤ b)
    (h : FoldsOnto f (zigWalk (veeAt L H b)).1 (zigWalk (veeAt L H b)).2)
    (j0 : Fin m) (hrise : b + 2 ≤ f j0) :
    ∃ j1 : Fin m, j1.val < j0.val ∧ f j1 ≤ L + 2 := by
  obtain ⟨β, hlt, hlip, h0, hw⟩ := h
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) j0.isLt
  have h00 : β ⟨0, hm⟩ = 0 := h0 _ rfl
  have hgt : (b - L - 1).toNat < β j0 := by
    by_contra hc
    have hle : β j0 ≤ (b - L - 1).toNat := by omega
    have hval := hw j0
    rw [zigWalk_veeAt_val_down L H b (by omega) _ hle, abs_le] at hval
    omega
  obtain ⟨t, -, ht2, ht3⟩ :=
    exists_lt_eq_of_lip hlip (b - L - 1).toNat j0.val ⟨0, hm⟩ j0 (by simp) (by omega) hgt
  refine ⟨t, ht2, ?_⟩
  have hval := hw t
  rw [ht3, zigWalk_veeAt_val_down L H b (by omega) _ le_rfl, abs_le] at hval
  omega

/-- **The lam's first leg is one-sided**, the mirror image. -/
theorem foldsOnto_lamAt_ascent_first {m : ℕ} (f : Fin m → ℤ) (L H b : ℤ) (hb2 : b ≤ H - 2)
    (h : FoldsOnto f (zigWalk (lamAt L H b)).1 (zigWalk (lamAt L H b)).2)
    (j0 : Fin m) (hfall : f j0 ≤ b - 2) :
    ∃ j1 : Fin m, j1.val < j0.val ∧ H - 2 ≤ f j1 := by
  obtain ⟨β, hlt, hlip, h0, hw⟩ := h
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) j0.isLt
  have h00 : β ⟨0, hm⟩ = 0 := h0 _ rfl
  have hgt : (H - 1 - b).toNat < β j0 := by
    by_contra hc
    have hle : β j0 ≤ (H - 1 - b).toNat := by omega
    have hval := hw j0
    rw [zigWalk_lamAt_val_up L H b (by omega) _ hle, abs_le] at hval
    omega
  obtain ⟨t, -, ht2, ht3⟩ :=
    exists_lt_eq_of_lip hlip (H - 1 - b).toNat j0.val ⟨0, hm⟩ j0 (by simp) (by omega) hgt
  refine ⟨t, ht2, ?_⟩
  have hval := hw t
  rw [ht3, zigWalk_lamAt_val_up L H b (by omega) _ le_rfl, abs_le] at hval
  omega

/-- **No one-turn walk serves a basepoint whose two arms make opposite demands.** If the
forward arm rises two above the base before coming within one of `L + 1`, and the backward arm
falls two below the base before coming within one of `H − 1`, then neither the vee nor the lam
at that base folds both arms. The mirror case — the forward arm falling early and the backward
arm rising early — is this statement with the two arms exchanged. So the interior case is not a
matter of choosing the right one-turn walk: it needs walks with more legs. -/
theorem not_oneTurn_of_opposite {m m' : ℕ} (fG : Fin m → ℤ) (fT : Fin m' → ℤ) (L H b : ℤ)
    (hb1 : L + 2 ≤ b) (hb2 : b ≤ H - 2)
    (hG : ∃ j0 : Fin m, b + 2 ≤ fG j0 ∧ ∀ j : Fin m, j.val < j0.val → L + 3 ≤ fG j)
    (hT : ∃ j0 : Fin m', fT j0 ≤ b - 2 ∧ ∀ j : Fin m', j.val < j0.val → fT j ≤ H - 3) :
    ¬ (FoldsOnto fG (zigWalk (veeAt L H b)).1 (zigWalk (veeAt L H b)).2 ∧
       FoldsOnto fT (zigWalk (veeAt L H b)).1 (zigWalk (veeAt L H b)).2) ∧
    ¬ (FoldsOnto fG (zigWalk (lamAt L H b)).1 (zigWalk (lamAt L H b)).2 ∧
       FoldsOnto fT (zigWalk (lamAt L H b)).1 (zigWalk (lamAt L H b)).2) := by
  obtain ⟨jG, hjG1, hjG2⟩ := hG
  obtain ⟨jT, hjT1, hjT2⟩ := hT
  constructor
  · rintro ⟨hfold, -⟩
    obtain ⟨j1, hj1, hj2⟩ := foldsOnto_veeAt_descent_first fG L H b hb1 hfold jG hjG1
    have := hjG2 j1 hj1
    omega
  · rintro ⟨-, hfold⟩
    obtain ⟨j1, hj1, hj2⟩ := foldsOnto_lamAt_ascent_first fT L H b hb2 hfold jT hjT1
    have := hjT2 j1 hj1
    omega

/-! ## Prefixing a leg

A walk with more than one turn is reached from a shorter one by prefixing a leg, which is what
`isZigFree_cons` does for the family. The two lemmas below do it for the walk and for a fold:
the walk of `b :: ts` is the leg from `b` to the head of `ts` followed by the walk of `ts`
(`zigWalk_cons_length`, `zigWalk_cons_val_tail`), and a fold of the arm's tail onto the walk of
`ts` extends to a fold of the whole arm onto the walk of `b :: ts` as soon as the token can be
brought along the arm's first indices to the far end of the new leg (`foldsOnto_cons`). This is
the induction step any multi-leg construction needs; what it does not supply is the choice of
leg. -/

theorem zigLevels_cons_cons (b t1 : ℤ) (r : List ℤ) :
    zigLevels (b :: t1 :: r) = b :: (stepRun b t1 ++ zigTail t1 r) := by
  simp [zigLevels, zigTail]

/-- The last level of a leg is its target. -/
theorem stepRun_getD_last (a c : ℤ) (h : a ≠ c) :
    (stepRun a c).getD ((c - a).natAbs - 1) 0 = c := by
  rcases le_or_gt a c with hle | hgt
  · have hpos : 0 < (c - a).natAbs := by omega
    rw [stepRun_getD_up _ _ a hle (by omega)]
    omega
  · have hpos : 0 < (c - a).natAbs := by omega
    rw [stepRun_getD_down _ _ a (by omega) (by omega)]
    omega

/-- **The walk of `b :: ts` is one leg longer than the walk of `ts`.** -/
theorem zigWalk_cons_length (b t1 : ℤ) (r : List ℤ) :
    (zigWalk (b :: t1 :: r)).1 = (t1 - b).natAbs + (zigWalk (t1 :: r)).1 := by
  show (zigLevels (b :: t1 :: r)).length = (t1 - b).natAbs + (zigLevels (t1 :: r)).length
  rw [zigLevels_cons_cons, show zigLevels (t1 :: r) = t1 :: zigTail t1 r from rfl]
  simp only [List.length_cons, List.length_append, stepRun_length]
  omega

/-- **The walk of `b :: ts`, after the new leg, is the walk of `ts`.** -/
theorem zigWalk_cons_val_tail (b t1 : ℤ) (r : List ℤ) (v : ℕ) :
    (zigWalk (b :: t1 :: r)).2 ((t1 - b).natAbs + v) = (zigWalk (t1 :: r)).2 v := by
  have hlen : (stepRun b t1).length = (t1 - b).natAbs := stepRun_length b t1
  show (zigLevels (b :: t1 :: r)).getD ((t1 - b).natAbs + v) 0
    = (zigLevels (t1 :: r)).getD v 0
  rw [zigLevels_cons_cons]
  show (b :: (stepRun b t1 ++ zigTail t1 r)).getD ((t1 - b).natAbs + v) 0
    = (t1 :: zigTail t1 r).getD v 0
  rcases Nat.eq_zero_or_pos (t1 - b).natAbs with hD | hD
  · have hbt : b = t1 := by omega
    subst hbt
    have hnil : stepRun b b = [] := by rw [stepRun]; simp
    rw [hnil, hD]
    simp
  · rcases Nat.eq_zero_or_pos v with rfl | hv
    · have hne : b ≠ t1 := by omega
      obtain ⟨w, hw⟩ : ∃ w, (t1 - b).natAbs = w + 1 := ⟨(t1 - b).natAbs - 1, by omega⟩
      rw [Nat.add_zero, hw, List.getD_cons_succ,
        List.getD_append _ _ _ _ (by rw [hlen]; omega)]
      have hlast := stepRun_getD_last b t1 hne
      rw [hw] at hlast
      simpa using hlast
    · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      rw [show (t1 - b).natAbs + (w + 1) = ((t1 - b).natAbs + w) + 1 from by omega,
        List.getD_cons_succ, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
        show (t1 - b).natAbs + w - (t1 - b).natAbs = w from by omega, List.getD_cons_succ]

/-- **Prefixing a leg to a fold.** If the arm's tail from index `e` folds onto the walk of `ts`,
and the first `e` indices of the arm carry the token from the start of the new leg to its far
end, then the whole arm folds onto the walk of `b :: ts`. The prefix is given as a function on
`ℕ`, which is all the construction uses. -/
theorem foldsOnto_prefixLeg {m : ℕ} (f : Fin m → ℤ) (b t1 : ℤ) (r : List ℤ) (e : ℕ) (he : e < m)
    (g : ℕ → ℕ) (hg0 : g 0 = 0) (hge : g e = (t1 - b).natAbs)
    (hgle : ∀ k, k ≤ e → g k ≤ (t1 - b).natAbs)
    (hglip : ∀ k, k < e → ((g (k + 1) : ℤ) - (g k : ℤ)).natAbs ≤ 1)
    (hgval : ∀ (k : ℕ) (h : k < m), k ≤ e →
      |f ⟨k, h⟩ - (zigWalk (b :: t1 :: r)).2 (g k)| ≤ 1)
    (htail : FoldsOnto (fun j : Fin (m - e) => f ⟨e + j.val, by omega⟩)
      (zigWalk (t1 :: r)).1 (zigWalk (t1 :: r)).2) :
    FoldsOnto f (zigWalk (b :: t1 :: r)).1 (zigWalk (b :: t1 :: r)).2 := by
  classical
  obtain ⟨βt, htlt, htlip, ht0, htw⟩ := htail
  set D := (t1 - b).natAbs with hD
  have ht0' : βt ⟨0, by omega⟩ = 0 := ht0 _ rfl
  refine ⟨fun j => if j.val ≤ e then g j.val else D + βt ⟨j.val - e, by have := j.isLt; omega⟩,
    ?_, ?_, ?_, ?_⟩
  · intro j
    rw [zigWalk_cons_length]
    by_cases hj : j.val ≤ e
    · have h1 := hgle j.val hj
      have h2 := htlt ⟨0, by omega⟩
      simp only [if_pos hj]
      omega
    · have := htlt ⟨j.val - e, by have := j.isLt; omega⟩
      simp only [if_neg hj]
      omega
  · intro j j' hjj'
    by_cases hj' : j'.val ≤ e
    · have hj : j.val ≤ e := by omega
      simp only [if_pos hj, if_pos hj']
      have h2 := hglip j.val (by omega)
      rw [show j'.val = j.val + 1 from hjj', abs_le]
      omega
    · by_cases hj : j.val ≤ e
      · -- the boundary: `j.val = e`
        have hje : j.val = e := by omega
        have hj'e : j'.val - e = 1 := by omega
        have h1 : βt ⟨j'.val - e, by have := j'.isLt; omega⟩ = βt ⟨1, by omega⟩ := by
          congr 1
          exact Fin.ext (by omega)
        have h2 := htlip ⟨0, by omega⟩ ⟨1, by omega⟩ rfl
        rw [ht0'] at h2
        rw [abs_le] at h2
        simp only [if_neg hj', h1, hje, hge]
        rw [abs_le]
        push_cast
        omega
      · have h1 : (⟨j'.val - e, by have := j'.isLt; omega⟩ : Fin (m - e)).val =
            (⟨j.val - e, by have := j.isLt; omega⟩ : Fin (m - e)).val + 1 := by simp; omega
        have h2 := htlip ⟨j.val - e, by have := j.isLt; omega⟩
          ⟨j'.val - e, by have := j'.isLt; omega⟩ h1
        rw [abs_le] at h2
        simp only [if_neg hj, if_neg hj']
        rw [abs_le]
        push_cast
        omega
  · intro j hj0
    have hle : j.val ≤ e := by omega
    dsimp only
    rw [if_pos hle, hj0, hg0]
  · intro j
    by_cases hj : j.val ≤ e
    · simp only [if_pos hj]
      have := hgval j.val j.isLt hj
      simpa using this
    · simp only [if_neg hj]
      have hw := htw ⟨j.val - e, by have := j.isLt; omega⟩
      rw [zigWalk_cons_val_tail]
      have hje : (⟨e + (j.val - e), by have := j.isLt; omega⟩ : Fin m) = j :=
        Fin.ext (by simp; omega)
      simpa [hje] using hw

/-! ### What the two walks settle

The vee at the basepoint's own level serves a basepoint both of whose arms descend to `L + 1`
before either rises two above the basepoint; the lam serves the mirror case. This is the
interior analogue of `s3ZigFree_near_extreme`, and it is sharp for a one-turn walk: while the
token is on the first leg the walk offers no level on the far side of the basepoint, so an arm
that crosses to the far side before reaching the band it was sent to needs a walk with more
legs. -/

/-- **The interior case when both arms descend first.** -/
theorem s3ZigFreeInterior_descentFirst {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ)
    (i : Fin n) (L H : ℤ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hlo : L + 2 ≤ ρ i) (hhi : ρ i ≤ H - 1)
    (hG : ∀ j : Fin (n - i.val),
      (∀ j' : Fin (n - i.val), j'.val ≤ j.val → L + 2 ≤ armG ρ i j') → armG ρ i j ≤ ρ i + 1)
    (hT : ∀ j : Fin (i.val + 1),
      (∀ j' : Fin (i.val + 1), j'.val ≤ j.val → L + 2 ≤ armT ρ i j') → armT ρ i j ≤ ρ i + 1) :
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 := by
  have hlip := hf.isLip
  refine ⟨veeAt L H (ρ i), isZigFree_veeAt L H (ρ i) hLH hlo hhi, ?_, ?_⟩
  · exact foldsOnto_veeAt _ (armG_isLip hlip i) L H (ρ i) hLH (fun j => hLb _) (fun j => hHb _)
      hlo hhi (fun j hj => armG_zero ρ i j hj) hG
  · exact foldsOnto_veeAt _ (armT_isLip hlip i) L H (ρ i) hLH (fun j => hLb _) (fun j => hHb _)
      hlo hhi (fun j hj => armT_zero ρ i j hj) hT

/-- **The interior case when both arms ascend first.** -/
theorem s3ZigFreeInterior_ascentFirst {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ)
    (i : Fin n) (L H : ℤ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hlo : L + 1 ≤ ρ i) (hhi : ρ i ≤ H - 2)
    (hG : ∀ j : Fin (n - i.val),
      (∀ j' : Fin (n - i.val), j'.val ≤ j.val → armG ρ i j' ≤ H - 2) → ρ i - 1 ≤ armG ρ i j)
    (hT : ∀ j : Fin (i.val + 1),
      (∀ j' : Fin (i.val + 1), j'.val ≤ j.val → armT ρ i j' ≤ H - 2) → ρ i - 1 ≤ armT ρ i j) :
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 := by
  have hlip := hf.isLip
  refine ⟨lamAt L H (ρ i), isZigFree_lamAt L H (ρ i) hLH hlo hhi, ?_, ?_⟩
  · exact foldsOnto_lamAt _ (armG_isLip hlip i) L H (ρ i) hLH (fun j => hLb _) (fun j => hHb _)
      hlo hhi (fun j hj => armG_zero ρ i j hj) hG
  · exact foldsOnto_lamAt _ (armT_isLip hlip i) L H (ρ i) hLH (fun j => hLb _) (fun j => hHb _)
      hlo hhi (fun j hj => armT_zero ρ i j hj) hT

-- Commented-out statement `s3ZigFreeInterior`, `s3ZigFree`, `s3`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
