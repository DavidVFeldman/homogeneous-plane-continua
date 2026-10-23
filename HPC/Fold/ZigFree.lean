import HPC.Fold.Zigzag

/-!
# `S3ZigFree`

Batch 28's gate refuted `S3Zig` structurally: a zig sequence cannot begin in an extreme band,
so no walk of that family starts within one of a basepoint at an extreme level
(`zig_base_lower`, `zig_base_upper`, `not_s3Zig`). `IsZigFree` exempts the first amplitude,
requiring only `|t₂ − t₁| < |t₃ − t₂| < ⋯`, and that exemption is exactly what an extreme
basepoint needs.

Delivered here: the base-free witness `isZigFree_base_free`; the closure of the free family
under prefixing a zig sequence by a sweep of any amplitude (`isZigFree_cons`); the two ladders
`[L+1, H−1, L+1]` and `[H−1, L+1, H−1]`, with the values of their walks
(`zigWalk_ladderUp_val`, `zigWalk_ladderDown_val`); the tracking fold of an arbitrary arm onto
the ladder whose foot is within one of the arm's first level (`foldsOnto_ladderUp`,
`foldsOnto_ladderDown`) — the token follows the arm's level, clamped to the band and held back
so that it never runs ahead of the index; hence `S3ZigFree` at every basepoint within two of an
extreme (`s3ZigFree_near_extreme`), which is precisely the range of basepoints at which `IsZig`
has no walk at all, the reduction of `S3ZigFree` to its interior basepoints
(`s3ZigFree_of_interior`), and `S3ZigFree` at every span up to five (`s3ZigFree_span_five`).
The near-extreme range is sharp while the crookedness is unused: three levels in, a straight
descent defeats every walk of unit steps (`no_zigWalk_fold_veeSeq`, `not_near_extreme_three`).

`s3ZigFree` itself is neither proved nor refuted, and is kept, commented out, at the end. No
`sorry` remains outside that block.
-/

namespace HPC.Fold

/-! ## The base-free witness -/

/-- The two chain endpoints are exactly where `IsZig` fails and `IsZigFree` is needed: a zig
sequence may open with a sweep of any amplitude, so it may start at `L + 1`. -/
theorem isZigFree_base_free (L H : ℤ) (hLH : L + 3 ≤ H) :
    IsZigFree L H [L + 1, H - 1, L + 1] := by
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> omega
  · intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    norm_num
    nlinarith
  · intro j hj hj'
    simp only [List.length_cons, List.length_nil] at hj'
    omega
  · right
    norm_num

/-- **The free family is closed at the open end.** A zig sequence may be prefixed by a sweep
of any amplitude — the exemption of the first amplitude is exactly what allows it — provided
only that the new step alternates with the old first one. Since `zigWalk` starts at the head of
the sequence, this is the step that moves a walk's start to where a basepoint needs it. -/
theorem isZigFree_cons {L H b : ℤ} {ts : List ℤ} (h : IsZig L H ts)
    (hb1 : L + 1 ≤ b) (hb2 : b ≤ H - 1)
    (halt : (ts[0]! - b) * (ts[1]! - ts[0]!) < 0) :
    IsZigFree L H (b :: ts) := by
  have hlen := h.len
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨hb1, hb2⟩
    · exact h.bounds t ht
  · simp only [List.length_cons]; omega
  · intro j hj
    simp only [List.length_cons] at hj
    match j with
    | 0 => simpa using halt
    | (j + 1) =>
        simp only [List.getElem!_cons_succ]
        exact h.alt j (by omega)
  · intro j hj1 hj2
    simp only [List.length_cons] at hj2
    match j with
    | 0 => omega
    | (j + 1) =>
        simp only [List.getElem!_cons_succ]
        exact h.amp j (by omega)
  · have e1 : (b :: ts).length - 2 = (ts.length - 2) + 1 := by simp; omega
    have e2 : (b :: ts).length - 1 = (ts.length - 1) + 1 := by simp; omega
    rw [e1, e2, List.getElem!_cons_succ, List.getElem!_cons_succ]
    exact h.ends

/-! ## The two ladders -/

/-- The ascending ladder: the walk `L+1 ↗ H−1 ↘ L+1`. -/
def ladderUp (L H : ℤ) : List ℤ := [L + 1, H - 1, L + 1]

/-- The descending ladder: the walk `H−1 ↘ L+1 ↗ H−1`. -/
def ladderDown (L H : ℤ) : List ℤ := [H - 1, L + 1, H - 1]

theorem isZigFree_ladderUp (L H : ℤ) (hLH : L + 3 ≤ H) : IsZigFree L H (ladderUp L H) :=
  isZigFree_base_free L H hLH

theorem isZigFree_ladderDown (L H : ℤ) (hLH : L + 3 ≤ H) : IsZigFree L H (ladderDown L H) := by
  refine ⟨?_, by simp [ladderDown], ?_, ?_, ?_⟩
  · intro t ht
    simp only [ladderDown, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> omega
  · intro j hj
    simp only [ladderDown, List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    norm_num [ladderDown]
    nlinarith
  · intro j hj hj'
    simp only [ladderDown, List.length_cons, List.length_nil] at hj'
    omega
  · left
    norm_num [ladderDown]

/-! ## The values of a step run -/

/-- An ascending step run takes the value `a + k + 1` at index `k`. -/
theorem stepRun_getD_up (b : ℤ) : ∀ (k : ℕ) (a : ℤ), a ≤ b → k < (b - a).toNat →
    (stepRun a b).getD k 0 = a + k + 1 := by
  intro k
  induction k with
  | zero =>
      intro a hab hk
      have hne : ¬ a = b := by omega
      have hlt : a < b := by omega
      rw [stepRun]
      simp only [dif_neg hne, dif_pos hlt]
      simp
  | succ k ih =>
      intro a hab hk
      have hne : ¬ a = b := by omega
      have hlt : a < b := by omega
      rw [stepRun]
      simp only [dif_neg hne, dif_pos hlt, List.getD_cons_succ]
      rw [ih (a + 1) (by omega) (by omega)]
      push_cast
      ring

/-- A descending step run takes the value `a − k − 1` at index `k`. -/
theorem stepRun_getD_down (b : ℤ) : ∀ (k : ℕ) (a : ℤ), b ≤ a → k < (a - b).toNat →
    (stepRun a b).getD k 0 = a - k - 1 := by
  intro k
  induction k with
  | zero =>
      intro a hab hk
      have hne : ¬ a = b := by omega
      have hlt : ¬ a < b := by omega
      rw [stepRun]
      simp only [dif_neg hne, dif_neg hlt]
      simp
  | succ k ih =>
      intro a hab hk
      have hne : ¬ a = b := by omega
      have hlt : ¬ a < b := by omega
      rw [stepRun]
      simp only [dif_neg hne, dif_neg hlt, List.getD_cons_succ]
      rw [ih (a - 1) (by omega) (by omega)]
      push_cast
      ring

/-! ## The values of a ladder walk -/

theorem zigLevels_ladderUp (L H : ℤ) :
    zigLevels (ladderUp L H) = (L + 1) :: (stepRun (L + 1) (H - 1) ++ stepRun (H - 1) (L + 1)) := by
  simp [ladderUp, zigLevels, zigTail]

theorem zigLevels_ladderDown (L H : ℤ) :
    zigLevels (ladderDown L H) = (H - 1) :: (stepRun (H - 1) (L + 1) ++ stepRun (L + 1) (H - 1)) := by
  simp [ladderDown, zigLevels, zigTail]

theorem zigWalk_ladderUp_length (L H : ℤ) (hLH : L + 3 ≤ H) :
    (zigWalk (ladderUp L H)).1 = 2 * (H - L - 2).toNat + 1 := by
  simp [zigWalk, zigLevels_ladderUp, stepRun_length]
  omega

theorem zigWalk_ladderDown_length (L H : ℤ) (hLH : L + 3 ≤ H) :
    (zigWalk (ladderDown L H)).1 = 2 * (H - L - 2).toNat + 1 := by
  simp [zigWalk, zigLevels_ladderDown, stepRun_length]
  omega

/-- On its first leg the ascending ladder is at level `L + 1 + u` at time `u`. -/
theorem zigWalk_ladderUp_val (L H : ℤ) (hLH : L + 3 ≤ H) (u : ℕ) (hu : u ≤ (H - L - 2).toNat) :
    (zigWalk (ladderUp L H)).2 u = L + 1 + u := by
  rw [zigWalk]
  simp only [zigLevels_ladderUp]
  cases u with
  | zero => simp
  | succ k =>
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by rw [stepRun_length]; omega),
        stepRun_getD_up _ k (L + 1) (by omega) (by omega)]
      push_cast
      ring

/-- On its first leg the descending ladder is at level `H − 1 − u` at time `u`. -/
theorem zigWalk_ladderDown_val (L H : ℤ) (hLH : L + 3 ≤ H) (u : ℕ)
    (hu : u ≤ (H - L - 2).toNat) : (zigWalk (ladderDown L H)).2 u = H - 1 - u := by
  rw [zigWalk]
  simp only [zigLevels_ladderDown]
  cases u with
  | zero => simp
  | succ k =>
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by rw [stepRun_length]; omega),
        stepRun_getD_down _ k (H - 1) (by omega) (by omega)]
      push_cast
      ring

/-! ## The tracking fold -/

/-- **Tracking, upward.** An arm confined to `[L, H]` whose first level is at most `L + 2`
folds onto the ascending ladder: the token follows the arm's level, clamped to the band, and
held back so that it never runs ahead of the index. The hold-back is what covers the start at
`L + 2`: where it bites, the arm has ascended at full speed from `L + 2`, and the token, one
level behind, is still within one. -/
theorem foldsOnto_ladderUp {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (L H : ℤ) (hLH : L + 3 ≤ H)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) (h0 : ∀ j : Fin m, j.val = 0 → f j ≤ L + 2) :
    FoldsOnto f (zigWalk (ladderUp L H)).1 (zigWalk (ladderUp L H)).2 := by
  have hstart : ∀ j : Fin m, f j ≤ L + 2 + j.val := by
    intro j
    have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have h1 := abs_sub_le_of_isLip hf j.val ⟨0, hm⟩ j (by simp)
    have h2 := h0 ⟨0, hm⟩ rfl
    rw [abs_le] at h1
    omega
  refine ⟨fun j => min (min (f j - (L + 1)).toNat (H - L - 2).toNat) j.val, ?_, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    rw [zigWalk_ladderUp_length L H hLH]
    omega
  · intro j j' hjj'
    dsimp only
    have h1 := hf j j' hjj'
    rw [abs_le] at h1
    rw [abs_le]
    push_cast
    omega
  · intro j hj
    dsimp only
    simp [hj]
  · intro j
    dsimp only
    have hle : min (min (f j - (L + 1)).toNat (H - L - 2).toNat) j.val ≤ (H - L - 2).toNat := by
      omega
    rw [zigWalk_ladderUp_val L H hLH _ hle, abs_le]
    have := hL j; have := hH j; have := hstart j
    omega

/-- **Tracking, downward.** The mirror image: an arm whose first level is at least `H − 2`
folds onto the descending ladder. -/
theorem foldsOnto_ladderDown {m : ℕ} (f : Fin m → ℤ) (hf : IsLip f) (L H : ℤ) (hLH : L + 3 ≤ H)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) (h0 : ∀ j : Fin m, j.val = 0 → H - 2 ≤ f j) :
    FoldsOnto f (zigWalk (ladderDown L H)).1 (zigWalk (ladderDown L H)).2 := by
  have hstart : ∀ j : Fin m, H - 2 - j.val ≤ f j := by
    intro j
    have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have h1 := abs_sub_le_of_isLip hf j.val ⟨0, hm⟩ j (by simp)
    have h2 := h0 ⟨0, hm⟩ rfl
    rw [abs_le] at h1
    omega
  refine ⟨fun j => min (min (H - 1 - f j).toNat (H - L - 2).toNat) j.val, ?_, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    rw [zigWalk_ladderDown_length L H hLH]
    omega
  · intro j j' hjj'
    dsimp only
    have h1 := hf j j' hjj'
    rw [abs_le] at h1
    rw [abs_le]
    push_cast
    omega
  · intro j hj
    dsimp only
    simp [hj]
  · intro j
    dsimp only
    have hle : min (min (H - 1 - f j).toNat (H - L - 2).toNat) j.val ≤ (H - L - 2).toNat := by
      omega
    rw [zigWalk_ladderDown_val L H hLH _ hle, abs_le]
    have := hL j; have := hH j; have := hstart j
    omega

/-! ## `S3ZigFree` near an extreme -/

/-- **`S3ZigFree` near an extreme.** At a basepoint whose level is within two of an extreme
both arms fold onto one ladder of the free family, at any span, and no crookedness is needed.
These are exactly the basepoints at which `IsZig` has no walk at all (`zig_base_lower`,
`zig_base_upper`), so the exemption of the first amplitude is what makes them reachable. -/
theorem s3ZigFree_near_extreme {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i) :
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 := by
  rcases hnear with hlow | hhigh
  · refine ⟨ladderUp L H, isZigFree_ladderUp L H hLH, ?_, ?_⟩
    · exact foldsOnto_ladderUp _ (armG_isLip hlip i) L H hLH (fun j => hLb _) (fun j => hHb _)
        (fun j hj => by rw [armG_zero ρ i j hj]; exact hlow)
    · exact foldsOnto_ladderUp _ (armT_isLip hlip i) L H hLH (fun j => hLb _) (fun j => hHb _)
        (fun j hj => by rw [armT_zero ρ i j hj]; exact hlow)
  · refine ⟨ladderDown L H, isZigFree_ladderDown L H hLH, ?_, ?_⟩
    · exact foldsOnto_ladderDown _ (armG_isLip hlip i) L H hLH (fun j => hLb _) (fun j => hHb _)
        (fun j hj => by rw [armG_zero ρ i j hj]; exact hhigh)
    · exact foldsOnto_ladderDown _ (armT_isLip hlip i) L H hLH (fun j => hLb _) (fun j => hHb _)
        (fun j hj => by rw [armT_zero ρ i j hj]; exact hhigh)

/-- **The reduction of `S3ZigFree` to its interior basepoints.** With `s3ZigFree_near_extreme`
the statement holds in full as soon as it holds at basepoints at least three above the bottom
and three below the top, so only spans six and above carry any content. -/
theorem s3ZigFree_of_interior
    (h : ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
      IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
      (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
      ∃ ts : List ℤ, IsZigFree L H ts ∧
        FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2) :
    S3ZigFree := by
  intro n ρ σ i H L hlip hcr hLb hHb hLH hL hH
  rcases le_or_gt (ρ i) (L + 2) with hlow | hlow
  · exact s3ZigFree_near_extreme ρ i H L hlip hLb hHb hLH (Or.inl hlow)
  · rcases le_or_gt (H - 2) (ρ i) with hhigh | hhigh
    · exact s3ZigFree_near_extreme ρ i H L hlip hLb hHb hLH (Or.inr hhigh)
    · exact h n ρ σ i H L hlip hcr hLb hHb hLH hL hH (by omega) (by omega)

/-- **`S3ZigFree` at every span up to five**, the base of the induction: at span five and below
every level is within two of an extreme. -/
theorem s3ZigFree_span_five {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hspan : H ≤ L + 5) :
    ∃ ts : List ℤ, IsZigFree L H ts ∧
      FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2 := by
  have h1 := hLb i
  have h2 := hHb i
  exact s3ZigFree_near_extreme ρ i H L hlip hLb hHb hLH (by omega)

/-! ## Sharpness: at level `L + 3` the crookedness is indispensable

`s3ZigFree_near_extreme` asks nothing of the sequence but that it be 1-Lipschitz and confined
to `[L, H]`. That is possible only within two of an extreme. Three levels in, the straight
descent `6, 5, 4, 3, 2, 1, 0` based at its middle already defeats every walk of unit steps,
whatever turning sequence produces it: the forward arm reaches `L` three indices on and the
backward arm reaches `H` three indices back, so the token would have to be within one of `L`
and within one of `H` at two times no more than three apart, and the walk moves one level per
step. So the interior cases left by `s3ZigFree_of_interior` cannot be settled without using
the crookedness.
-/

/-- A walk of unit steps moves at most `d` levels in `d` steps. -/
theorem zigWalk_dist_le (ts : List ℤ) :
    ∀ (d u : ℕ), u + d < (zigWalk ts).1 →
      |(zigWalk ts).2 (u + d) - (zigWalk ts).2 u| ≤ (d : ℤ) := by
  intro d
  induction d with
  | zero => intro u _; simp
  | succ d ih =>
      intro u hu
      have h1 := ih u (by omega)
      have h2 := le_of_eq (zigWalk_step ts (u + d) (by omega))
      rw [abs_le] at h1 h2 ⊢
      have he : u + (d + 1) = (u + d) + 1 := by omega
      rw [he]
      push_cast
      omega

/-- The straight descent from `H = 6` to `L = 0`; its middle index is at level `3 = L + 3`. -/
def veeSeq : Fin 7 → ℤ := ![6, 5, 4, 3, 2, 1, 0]

theorem veeSeq_isLip : IsLip veeSeq := by unfold IsLip; decide

/-- The basepoint, at level `3 = L + 3 = H - 3`. -/
def veeBase : Fin 7 := ⟨3, by decide⟩

/-- The index at which the forward arm reaches `L`. -/
def veeG : Fin (7 - veeBase.val) := ⟨3, by decide⟩

/-- The index at which the backward arm reaches `H`. -/
def veeT : Fin (veeBase.val + 1) := ⟨3, by decide⟩

/-- **No walk of unit steps serves the basepoint.** Not merely no member of the free family:
no turning sequence whatever. -/
theorem no_zigWalk_fold_veeSeq :
    ¬ ∃ ts : List ℤ,
      FoldsOnto (armG veeSeq veeBase) (zigWalk ts).1 (zigWalk ts).2 ∧
      FoldsOnto (armT veeSeq veeBase) (zigWalk ts).1 (zigWalk ts).2 := by
  rintro ⟨ts, ⟨bG, hGlt, hGlip, hG0, hGw⟩, ⟨bT, hTlt, hTlip, hT0, hTw⟩⟩
  have hGv : armG veeSeq veeBase veeG = 0 := by decide
  have hTv : armT veeSeq veeBase veeT = 6 := by decide
  have hple : bG veeG ≤ 3 := le_index_of_lip hGlip (by decide) (hG0 ⟨0, by decide⟩ rfl) 3 _ rfl
  have hqle : bT veeT ≤ 3 := le_index_of_lip hTlip (by decide) (hT0 ⟨0, by decide⟩ rfl) 3 _ rfl
  have hcp : (zigWalk ts).2 (bG veeG) ≤ 1 := by
    have := hGw veeG
    rw [hGv, abs_le] at this
    omega
  have hcq : 5 ≤ (zigWalk ts).2 (bT veeT) := by
    have := hTw veeT
    rw [hTv, abs_le] at this
    omega
  have hGlt' := hGlt veeG
  have hTlt' := hTlt veeT
  rcases le_total (bG veeG) (bT veeT) with hpq | hpq
  · have hd := zigWalk_dist_le ts (bT veeT - bG veeG) (bG veeG) (by omega)
    rw [show bG veeG + (bT veeT - bG veeG) = bT veeT by omega, abs_le] at hd
    omega
  · have hd := zigWalk_dist_le ts (bG veeG - bT veeT) (bT veeT) (by omega)
    rw [show bT veeT + (bG veeG - bT veeT) = bG veeG by omega, abs_le] at hd
    omega

/-- **`s3ZigFree_near_extreme` is sharp.** Its range cannot be widened to three levels from an
extreme while the crookedness is still unused. -/
theorem not_near_extreme_three
    (h : ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
      IsLip ρ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
      (ρ i ≤ L + 3 ∨ H - 3 ≤ ρ i) →
      ∃ ts : List ℤ, IsZigFree L H ts ∧
        FoldsOnto (armG ρ i) (zigWalk ts).1 (zigWalk ts).2 ∧
        FoldsOnto (armT ρ i) (zigWalk ts).1 (zigWalk ts).2) : False := by
  obtain ⟨ts, -, hG, hT⟩ := h 7 veeSeq veeBase 6 0 veeSeq_isLip (by decide) (by decide)
    (by norm_num) (Or.inl (by decide))
  exact no_zigWalk_fold_veeSeq ⟨ts, hG, hT⟩

-- Commented-out statement `s3ZigFree`, `s3`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
