import HPC.Fold.DichotomyWitness

/-!
# The witness chain is faithful

`HPC/Fold/DichotomyWitness.lean` refutes `OffDichotomy` from the faithfulness of the 409-link
chain `ceSeq`. This file proves that faithfulness, so the refutation is unconditional.

Deciding `IsCrookedIvF ceSeq ceSeq` by the criteria of `HPC/Fold/Faithful.lean` and
`HPC/Fold/ClosureF.lean` is out of reach at this length: they quantify over all pairs of
indices and search for the two intermediate links, and the kernel exhausted 50 GB without
finishing. Two observations make the check cheap.

* **Monotonicity in the far index.** The crookedness clause for a pair `s < t` and levels
  `x, y` asks for `s < r < r' < t` with prescribed levels. If it holds for some `t₀ ≤ t` it
  holds for `t`. So it is enough to check, for each `s` and each pair of levels `x, y`, the
  *least* `t₀ > s` at which `y` is met — one check per `(s, x, y)` instead of one per pair.
* **A numeral for the chain.** The levels are `0 … 8`, so the whole chain is one natural
  number in base sixteen, and a link is read off by a shift and a mask — two machine
  operations, rather than walking a list.

Together these turn a computation the kernel could not finish into one it does in a few
minutes.
-/

namespace HPC.Fold

/-! ## The chain as a numeral -/

/-- The 409 links of `ceSeq`, as the base-sixteen digits of one natural number. -/
def ceNat : ℕ := 1616084577085363976657228336329747394757311389540103723711686578449453705010060495336099400317470310237094885181426860333552480908930978346148828830707395594506719049501924484908051759786157351534597963827828959611997009611268851984236576784305288911904852121017714112839156823632937613597761758329725125920631087344079853616645659664313707911927064747596185971056181884673281921186362471290708746814544168765536427378676561968822473616254567988880271639433485948626426761301030793400428925456

/-- Reading a link off the numeral. -/
def rhoN (i : ℕ) : ℕ := (ceNat >>> (4 * i)) &&& 15

theorem rhoN_eq : ∀ i : Fin 409, ceSeq i = (rhoN i.val : ℤ) := by decide +kernel

theorem rhoN_lt : ∀ i : Fin 409, rhoN i.val < 9 := by decide +kernel

/-! ## The search -/

/-- `y` is met at `i`: it is the level of `i − 1`, of `i`, or of `i + 1`. -/
def levHas (i y : ℕ) : Bool :=
  (i != 0 && rhoN (i - 1) == y) || rhoN i == y || (i + 1 < 409 && rhoN (i + 1) == y)

/-- The least index at or after `s`, within the given fuel, at which `y` is met. -/
def firstLev (y : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 409 ≤ s then none else if levHas s y then some s else firstLev y fuel (s + 1)

/-- The least index at or after `s`, within the given fuel, whose level is `v`. -/
def firstVal (v : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 409 ≤ s then none else if rhoN s == v then some s else firstVal v fuel (s + 1)

/-- The crookedness clause for the level pair `(x, y)` at `s`, checked at the least index at
which `y` is met. -/
def checkOne (s x y : ℕ) : Bool :=
  if x + 3 ≤ y then
    match firstLev y (409 - s) (s + 1) with
    | none => true
    | some t0 =>
      match firstVal (y - 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match firstVal (x + 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else if y + 3 ≤ x then
    match firstLev y (409 - s) (s + 1) with
    | none => true
    | some t0 =>
      match firstVal (y + 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match firstVal (x - 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else true

def checkS (s : ℕ) : Bool :=
  (List.range 9).all fun x =>
    if levHas s x then (List.range 9).all fun y => checkOne s x y else true

def checkAll : Bool := (List.range 409).all checkS

set_option maxRecDepth 10000000 in
/-- The check passes. Kernel evaluation, a few minutes. -/
theorem checkAll_true : checkAll = true := by decide +kernel

/-! ## The specifications of the two searches -/

theorem firstVal_spec : ∀ (v fuel s r : ℕ), firstVal v fuel s = some r →
    s ≤ r ∧ r < 409 ∧ rhoN r = v := by
  intro v fuel
  induction fuel with
  | zero => intro s r h; simp [firstVal] at h
  | succ f ih =>
    intro s r h
    rw [firstVal] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hs
      split at h
      · rename_i hv
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨le_rfl, by omega, by simpa using hv⟩
      · have := ih (s + 1) r h
        exact ⟨by omega, this.2.1, this.2.2⟩

theorem firstLev_le : ∀ (y fuel s t : ℕ), s ≤ t → t < 409 → t < s + fuel → levHas t y = true →
    ∃ t0, firstLev y fuel s = some t0 ∧ t0 ≤ t := by
  intro y fuel
  induction fuel with
  | zero => intro s t h1 _ h2 _; omega
  | succ f ih =>
    intro s t h1 hlt409 h2 h3
    rw [firstLev]
    split
    · omega
    · split
      · exact ⟨s, rfl, h1⟩
      · rename_i hne
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact absurd h3 (by simpa using hne)
        · exact ih (s + 1) t (by omega) hlt409 (by omega) h3

/-! ## Faithfulness -/

theorem levHas_of_near {s u : Fin 409} (h : ((u : ℤ) - s.val).natAbs ≤ 1) :
    levHas s.val (rhoN u.val) = true := by
  have hu := u.isLt
  have hs := s.isLt
  have hcase : s.val = u.val + 1 ∨ u.val = s.val ∨ u.val = s.val + 1 := by omega
  rcases hcase with h1 | h1 | h1
  · have hs0 : s.val ≠ 0 := by omega
    have hval : rhoN (s.val - 1) = rhoN u.val := by rw [show s.val - 1 = u.val by omega]
    simp [levHas, hval, hs0]
  · simp [levHas, h1]
  · have hlt : s.val + 1 < 409 := by omega
    have hval : rhoN (s.val + 1) = rhoN u.val := by rw [h1]
    simp [levHas, hval, hlt]

theorem checkOne_true {s x y : ℕ} (hs : s < 409) (hx : levHas s x = true) (hxlt : x < 9)
    (hylt : y < 9) : checkOne s x y = true := by
  have h := checkAll_true
  rw [checkAll, List.all_eq_true] at h
  have hS := h s (List.mem_range.2 hs)
  rw [checkS, List.all_eq_true] at hS
  have hx' := hS x (List.mem_range.2 hxlt)
  rw [if_pos hx, List.all_eq_true] at hx'
  exact hx' y (List.mem_range.2 hylt)

theorem ceSeq_faithful : IsCrookedIvF ceSeq ceSeq := by
  refine ⟨fun t => le_rfl, fun t => by omega, ?_, ?_⟩
  · intro t t' htt'
    have h := ceSeq_isLip t t' htt'
    rw [abs_le] at h
    omega
  · rintro s t hst h k ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
    have hxv : h = (rhoN u.val : ℤ) := by rw [← rhoN_eq u]; omega
    have hyv : k = (rhoN v.val : ℤ) := by rw [← rhoN_eq v]; omega
    set x := rhoN u.val with hxdef
    set y := rhoN v.val with hydef
    have hxlt : x < 9 := rhoN_lt u
    have hylt : y < 9 := rhoN_lt v
    have hsx : levHas s.val x = true := levHas_of_near hu
    have hty : levHas t.val y = true := levHas_of_near hv
    have hs : s.val < 409 := s.isLt
    have ht : t.val < 409 := t.isLt
    have hstv : s.val < t.val := hst
    have hchk := checkOne_true hs hsx hxlt hylt
    have hcases : x + 3 ≤ y ∨ y + 3 ≤ x := by
      rw [hxv, hyv] at habs
      rcases abs_cases ((x : ℤ) - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    -- the least index after `s` at which `y` is met
    obtain ⟨t0, ht0, ht0le⟩ :=
      firstLev_le y (409 - s.val) (s.val + 1) t.val (by omega) ht (by omega) hty
    rcases hcases with hc | hc
    · rw [checkOne, if_pos hc] at hchk
      simp only [ht0] at hchk
      cases hr : firstVal (y - 1) (t0 - s.val) (s.val + 1) with
      | none => simp [hr] at hchk
      | some r =>
        simp only [hr] at hchk
        obtain ⟨hr1, hr2, hr3⟩ := firstVal_spec _ _ _ _ hr
        by_cases hrt : t0 ≤ r
        · simp [hrt] at hchk
        · rw [if_neg hrt] at hchk
          cases hr' : firstVal (x + 1) (t0 - r) (r + 1) with
          | none => simp [hr'] at hchk
          | some r2 =>
            simp only [hr'] at hchk
            obtain ⟨hs1, hs2, hs3⟩ := firstVal_spec _ _ _ _ hr'
            have hlt2 : r2 < t0 := by simpa using hchk
            refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · intro _
              have e1 : ceSeq ⟨r, hr2⟩ = ((y - 1 : ℕ) : ℤ) := by rw [rhoN_eq ⟨r, hr2⟩, hr3]
              have e2 : ceSeq ⟨r2, hs2⟩ = ((x + 1 : ℕ) : ℤ) := by rw [rhoN_eq ⟨r2, hs2⟩, hs3]
              rw [e1, e2, hxv, hyv]
              push_cast [Nat.cast_sub (by omega : 1 ≤ y)]
              omega
            · intro hcon
              rw [hxv, hyv] at hcon
              omega
    · rw [checkOne, if_neg (by omega : ¬ (x + 3 ≤ y)), if_pos hc] at hchk
      simp only [ht0] at hchk
      cases hr : firstVal (y + 1) (t0 - s.val) (s.val + 1) with
      | none => simp [hr] at hchk
      | some r =>
        simp only [hr] at hchk
        obtain ⟨hr1, hr2, hr3⟩ := firstVal_spec _ _ _ _ hr
        by_cases hrt : t0 ≤ r
        · simp [hrt] at hchk
        · rw [if_neg hrt] at hchk
          cases hr' : firstVal (x - 1) (t0 - r) (r + 1) with
          | none => simp [hr'] at hchk
          | some r2 =>
            simp only [hr'] at hchk
            obtain ⟨hs1, hs2, hs3⟩ := firstVal_spec _ _ _ _ hr'
            have hlt2 : r2 < t0 := by simpa using hchk
            refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · simp only [Fin.lt_def]; omega
            · intro hcon
              rw [hxv, hyv] at hcon
              omega
            · intro _
              have e1 : ceSeq ⟨r, hr2⟩ = ((y + 1 : ℕ) : ℤ) := by rw [rhoN_eq ⟨r, hr2⟩, hr3]
              have e2 : ceSeq ⟨r2, hs2⟩ = ((x - 1 : ℕ) : ℤ) := by rw [rhoN_eq ⟨r2, hs2⟩, hs3]
              rw [e1, e2, hxv, hyv]
              push_cast [Nat.cast_sub (by omega : 1 ≤ x)]
              omega

/-- **`OffDichotomy` is false.** -/
theorem not_offDichotomy : ¬ OffDichotomy := not_offDichotomy_of_faithful ceSeq_faithful

end HPC.Fold
