import HPC.Fold.Faithful

/-!
# Faithfulness of an explicit pair, checked by a search

`IsCrookedIvF` quantifies its crookedness clause over two integers, so it is not decidable as it
stands; `IsCrookedIvFCheck` (`HPC/Fold/Faithful.lean`) replaces the integers by the ends of the
intervals of two neighbouring links and is decidable, but deciding it costs a fourth power in the
length of the pair, which the kernel cannot pay for the pairs the censuses produce.

This file is the search that batch 57 wrote out by hand for its 71-link pair
(`HPC/Fold/Audit57.lean`), stated once for a pair of any length whose levels lie in `[0, lev)`:

* a link `i` **carries** the level `l` when `ρ i ≤ l ≤ σ i`;
* a level is **met** at `i` when it is carried by `i - 1`, `i` or `i + 1`;
* the clause for a level pair `(x, y)` at `s` is checked at the **least** index after `s` at which
  `y` is met, which suffices because the clause is monotone in the far index.

The cost is one pass over the pair for each link and each pair of levels.

The pair is presented by two digit functions `rd sd : ℕ → ℕ`, as the audits present it — each link
a digit of a numeral. `checkAll` is the search, and `isCrookedIvF_of_search` turns it, together
with the three pointwise clauses of the model (which are decided directly), into `IsCrookedIvF`.
-/

namespace HPC.Fold

namespace PairCheck

variable (n lev : ℕ) (rd sd : ℕ → ℕ)

/-- The link `i` carries the level `l`. -/
def ivHas (i l : ℕ) : Bool := decide (i < n) && decide (rd i ≤ l) && decide (l ≤ sd i)

/-- The level `y` is met at `i`. -/
def levHas (i y : ℕ) : Bool :=
  (decide (i ≠ 0) && ivHas n rd sd (i - 1) y) || ivHas n rd sd i y || ivHas n rd sd (i + 1) y

/-- The least index at or after `s`, within the given fuel, at which `y` is met. -/
def firstLev (y : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if n ≤ s then none else if levHas n rd sd s y then some s else firstLev y fuel (s + 1)

/-- The least index at or after `s`, within the given fuel, carrying the level `v`. -/
def firstIv (v : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if n ≤ s then none else if ivHas n rd sd s v then some s else firstIv v fuel (s + 1)

/-- The crookedness clause for the level pair `(x, y)` at `s`, checked at the least index at
which `y` is met. -/
def checkOne (s x y : ℕ) : Bool :=
  if x + 3 ≤ y then
    match firstLev n rd sd y (n - s) (s + 1) with
    | none => true
    | some t0 =>
      match firstIv n rd sd (y - 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match firstIv n rd sd (x + 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else if y + 3 ≤ x then
    match firstLev n rd sd y (n - s) (s + 1) with
    | none => true
    | some t0 =>
      match firstIv n rd sd (y + 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match firstIv n rd sd (x - 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else true

/-- The clause at `s`, for every pair of levels the link `s` meets. -/
def checkS (s : ℕ) : Bool :=
  (List.range lev).all fun x =>
    if levHas n rd sd s x then (List.range lev).all fun y => checkOne n rd sd s x y else true

/-- The search, over every link. -/
def checkAll : Bool := (List.range n).all (checkS n lev rd sd)

/-! ## The two searches -/

theorem firstIv_spec : ∀ (v fuel s r : ℕ), firstIv n rd sd v fuel s = some r →
    s ≤ r ∧ r < n ∧ ivHas n rd sd r v = true := by
  intro v fuel
  induction fuel with
  | zero => intro s r h; simp [firstIv] at h
  | succ f ih =>
    intro s r h
    rw [firstIv] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hs
      split at h
      · rename_i hv
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨le_rfl, by omega, hv⟩
      · have := ih (s + 1) r h
        exact ⟨by omega, this.2.1, this.2.2⟩

theorem firstLev_le : ∀ (y fuel s t : ℕ), s ≤ t → t < n → t < s + fuel →
    levHas n rd sd t y = true → ∃ t0, firstLev n rd sd y fuel s = some t0 ∧ t0 ≤ t := by
  intro y fuel
  induction fuel with
  | zero => intro s t h1 _ h2 _; omega
  | succ f ih =>
    intro s t h1 hltn h2 h3
    rw [firstLev]
    split
    · omega
    · split
      · exact ⟨s, rfl, h1⟩
      · rename_i hne
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact absurd h3 (by simpa using hne)
        · exact ih (s + 1) t (by omega) hltn (by omega) h3

theorem checkOne_true (h : checkAll n lev rd sd = true) {s x y : ℕ} (hs : s < n)
    (hx : levHas n rd sd s x = true) (hxlt : x < lev) (hylt : y < lev) :
    checkOne n rd sd s x y = true := by
  rw [checkAll, List.all_eq_true] at h
  have hS := h s (List.mem_range.2 hs)
  rw [checkS, List.all_eq_true] at hS
  have hx' := hS x (List.mem_range.2 hxlt)
  rw [if_pos hx, List.all_eq_true] at hx'
  exact hx' y (List.mem_range.2 hylt)

/-! ## The bridge to the model -/

variable {n lev rd sd}

/-- The point sequence of the pair. -/
def rhoOf (n : ℕ) (rd : ℕ → ℕ) : Fin n → ℤ := fun i => (rd i.val : ℤ)

/-- The upper end of each link. -/
def sigOf (n : ℕ) (sd : ℕ → ℕ) : Fin n → ℤ := fun i => (sd i.val : ℤ)

theorem ivHas_iff {i l : ℕ} (hi : i < n) :
    ivHas n rd sd i l = true ↔
      (rhoOf n rd ⟨i, hi⟩ ≤ (l : ℤ) ∧ (l : ℤ) ≤ sigOf n sd ⟨i, hi⟩) := by
  simp only [ivHas, rhoOf, sigOf, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hi, by exact_mod_cast h1⟩, by exact_mod_cast h2⟩

theorem levHas_of_carry {s u : Fin n} (h : ((u : ℤ) - s.val).natAbs ≤ 1) {l : ℕ}
    (hl : ivHas n rd sd u.val l = true) : levHas n rd sd s.val l = true := by
  have hu := u.isLt
  have hs := s.isLt
  have hcase : s.val = u.val + 1 ∨ u.val = s.val ∨ u.val = s.val + 1 := by omega
  rcases hcase with h1 | h1 | h1
  · have hs0 : s.val ≠ 0 := by omega
    have he : s.val - 1 = u.val := by omega
    simp [levHas, he, hl, hs0]
  · simp [levHas, h1 ▸ hl]
  · have he : s.val + 1 = u.val := by omega
    simp [levHas, he, hl]

/-- **The search suffices.** The three pointwise clauses of the model are decided directly; the
crookedness clause is the search. -/
theorem isCrookedIvF_of_search
    (hle : ∀ t : Fin n, rhoOf n rd t ≤ sigOf n sd t)
    (hw : ∀ t : Fin n, sigOf n sd t ≤ rhoOf n rd t + 1)
    (hadj : ∀ t t' : Fin n, t'.val = t.val + 1 →
      max (sigOf n sd t) (sigOf n sd t') ≤ min (rhoOf n rd t) (rhoOf n rd t') + 1)
    (hlev : ∀ t : Fin n, sigOf n sd t < (lev : ℤ))
    (h : checkAll n lev rd sd = true) :
    IsCrookedIvF (rhoOf n rd) (sigOf n sd) := by
  have hnn : ∀ t : Fin n, (0 : ℤ) ≤ rhoOf n rd t := by
    intro t; simp only [rhoOf]; positivity
  refine ⟨hle, hw, hadj, ?_⟩
  rintro s t hst hh k ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
  have hh0 : 0 ≤ hh := le_trans (hnn u) hu1
  have hhl : hh < lev := lt_of_le_of_lt hu2 (hlev u)
  have hk0 : 0 ≤ k := le_trans (hnn v) hv1
  have hkl : k < lev := lt_of_le_of_lt hv2 (hlev v)
  set x : ℕ := hh.toNat with hxdef
  set y : ℕ := k.toNat with hydef
  have hxc : (x : ℤ) = hh := Int.toNat_of_nonneg hh0
  have hyc : (y : ℤ) = k := Int.toNat_of_nonneg hk0
  have hxlt : x < lev := by omega
  have hylt : y < lev := by omega
  have hux : ivHas n rd sd u.val x = true := (ivHas_iff u.isLt).2 (by rw [hxc]; exact ⟨hu1, hu2⟩)
  have hvy : ivHas n rd sd v.val y = true := (ivHas_iff v.isLt).2 (by rw [hyc]; exact ⟨hv1, hv2⟩)
  have hsx : levHas n rd sd s.val x = true := levHas_of_carry hu hux
  have hty : levHas n rd sd t.val y = true := levHas_of_carry hv hvy
  have hs : s.val < n := s.isLt
  have ht : t.val < n := t.isLt
  have hstv : s.val < t.val := hst
  have hchk := checkOne_true n lev rd sd h hs hsx hxlt hylt
  have hcases : x + 3 ≤ y ∨ y + 3 ≤ x := by
    rw [← hxc, ← hyc] at habs
    rcases abs_cases ((x : ℤ) - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  obtain ⟨t0, ht0, ht0le⟩ :=
    firstLev_le n rd sd y (n - s.val) (s.val + 1) t.val (by omega) ht (by omega) hty
  rcases hcases with hc | hc
  · rw [checkOne, if_pos hc] at hchk
    simp only [ht0] at hchk
    cases hr : firstIv n rd sd (y - 1) (t0 - s.val) (s.val + 1) with
    | none => simp [hr] at hchk
    | some r =>
      simp only [hr] at hchk
      obtain ⟨hr1, hr2, hr3⟩ := firstIv_spec n rd sd _ _ _ _ hr
      by_cases hrt : t0 ≤ r
      · simp [hrt] at hchk
      · rw [if_neg hrt] at hchk
        cases hr' : firstIv n rd sd (x + 1) (t0 - r) (r + 1) with
        | none => simp [hr'] at hchk
        | some r2 =>
          simp only [hr'] at hchk
          obtain ⟨hs1, hs2, hs3⟩ := firstIv_spec n rd sd _ _ _ _ hr'
          have hlt2 : r2 < t0 := by simpa using hchk
          have e1 := (ivHas_iff hr2).1 hr3
          have e2 := (ivHas_iff hs2).1 hs3
          have ey : ((y - 1 : ℕ) : ℤ) = k - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ y)]; push_cast; omega
          have ex : ((x + 1 : ℕ) : ℤ) = hh + 1 := by push_cast; omega
          rw [ey] at e1
          rw [ex] at e2
          refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [Fin.lt_def]; omega
          · simp only [Fin.lt_def]; omega
          · simp only [Fin.lt_def]; omega
          · intro _; exact ⟨e1, e2⟩
          · intro hcon; omega
  · rw [checkOne, if_neg (by omega : ¬ (x + 3 ≤ y)), if_pos hc] at hchk
    simp only [ht0] at hchk
    cases hr : firstIv n rd sd (y + 1) (t0 - s.val) (s.val + 1) with
    | none => simp [hr] at hchk
    | some r =>
      simp only [hr] at hchk
      obtain ⟨hr1, hr2, hr3⟩ := firstIv_spec n rd sd _ _ _ _ hr
      by_cases hrt : t0 ≤ r
      · simp [hrt] at hchk
      · rw [if_neg hrt] at hchk
        cases hr' : firstIv n rd sd (x - 1) (t0 - r) (r + 1) with
        | none => simp [hr'] at hchk
        | some r2 =>
          simp only [hr'] at hchk
          obtain ⟨hs1, hs2, hs3⟩ := firstIv_spec n rd sd _ _ _ _ hr'
          have hlt2 : r2 < t0 := by simpa using hchk
          have e1 := (ivHas_iff hr2).1 hr3
          have e2 := (ivHas_iff hs2).1 hs3
          have ey : ((y + 1 : ℕ) : ℤ) = k + 1 := by push_cast; omega
          have ex : ((x - 1 : ℕ) : ℤ) = hh - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ x)]; push_cast; omega
          rw [ey] at e1
          rw [ex] at e2
          refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [Fin.lt_def]; omega
          · simp only [Fin.lt_def]; omega
          · simp only [Fin.lt_def]; omega
          · intro hcon; omega
          · intro _; exact ⟨e1, e2⟩

end PairCheck

end HPC.Fold
