import HPC.Fold.Decide
import HPC.Fold.ArmReflect
import HPC.Fold.Leg3Profile

/-!
# The valley crossing does not reflect: a faithful counterexample at the branch `L + 5`

The branch `L + 4` of span nine closed in batch 56 on two crossings, of which the first is
`cross_valley_vee_pair` (`HPC/Fold/ValleyFar.lean`):

> if either arm of a pair of the branch fails `Leg3Valley`, then **both** arms fold onto the
> V-walk based at `L + 5`.

Question 1 of COMMISSION.md asks whether the branch `L + 5` yields to the same law, read through
the reflection of each arm — the interval clause of `IsCrookedIvF` is symmetric under
`(ρ, σ) ↦ (a − σ, a − ρ)` and `ivSep` is stated on intervals, so the two bounds of batch 56 are
available at the reflected levels as well.

**It does not.** `ReflValleyCrossL5` below is that statement, written out with each arm replaced
by its reflection `armRefl (L + (L + 9))` and the basepoint level by `L + 5`; it is false, and
this file proves it at an explicit faithful pair.

The pair is the window `[676, 746]` of a faithful random mixture of Bing's chain `bing 0 9` (986
links) drawn by `census-batch57.c` (log `census-batch57.log`): 71 links, with the basepoint at the
index `56`,
where `ρ` stands at `L + 5`. Every verdict is put to the kernel, faithfulness included:

* `faithful` — `IsCrookedIvF rho71 sig71`, by the interval form of the search of
  `HPC/Fold/DichotomyFaithful.lean`: for each link `s` and each pair of levels `(x, y)` at
  distance three or more, the clause is checked at the *least* index at which `y` is met, which
  suffices because the clause is monotone in the far index;
* the branch hypotheses — `ρ` at `L + 5` at the basepoint, the band `[L, L + 9]`, and both arms
  `LowAt (L + 1) (L + 8)`;
* the failure — the reflection of the forward arm fails `Leg3Valley`;
* the refutation — the reflection of the *backward* arm does not fold onto the V-walk based at
  `L + 5`, by the dynamic program of `HPC/Fold/Decide.lean`.

So the reflected valley crossing is not a theorem of the general model, and the level it is short
of is the one the census measures: at this basepoint, and at every other failure the census finds,
the witness the V-criterion asks for is missing in *point* form but present in *interval* form —
the partner arm has a link whose interval meets the level, but whose `ρ` sits one above it. The
timing law recovers the index; it does not recover the level.
-/

set_option maxRecDepth 10000000

namespace HPC.Fold

/-- **The valley crossing of the branch `L + 4`, read through the reflection of each arm.**
This is `cross_valley_vee_pair` (`HPC/Fold/ValleyFar.lean`) with the basepoint at `L + 5`, the
branch hypothesis `LowAt` in place of `HighAt`, and every arm replaced by its reflection in the
level `L + (L + 9)`. It is refuted by `not_reflValleyCrossL5` below. -/
def ReflValleyCrossL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    (¬ Leg3Valley (armRefl (L + (L + 9)) (armG ρ i)) L ∨
      ¬ Leg3Valley (armRefl (L + (L + 9)) (armT ρ i)) L) →
    FoldsOnto (armRefl (L + (L + 9)) (armG ρ i)) (veeLen (L + 5) (L + 9) L)
        (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armRefl (L + (L + 9)) (armT ρ i)) (veeLen (L + 5) (L + 9) L)
        (veeCenter (L + 5) (L + 9) L)

namespace Audit57

/-! ## The pair

`ρ`: `2 3 3 3 4 5 4 3 4 5 4 5 6 5 4 5 4 3 4 5 4 5 5 5 4 5 5 5 6 6 6 5 6 5 4 5 6 5 4 4 4 3 4 4 4 5
6 5 4 5 6 5 6 7 6 5 5 5 4 5 6 5 6 7 6 5 6 6 6 7 8`.

`σ`: `2 3 4 3 4 5 4 3 4 5 4 5 6 5 5 5 4 4 4 5 5 5 6 5 4 5 6 5 6 7 6 5 6 5 5 5 6 5 5 5 4 3 4 5 4 5
6 5 4 5 6 5 6 7 6 6 6 5 4 5 6 5 6 7 6 5 6 7 6 7 8`.

Both are carried as one natural number each, in base sixteen, the link `i` being the `i`-th
digit. -/

/-- The 71 links of `ρ`. -/
def rhoNat : ℕ := 0x87666567656545556765654565444344456545656665554555454345456545434543332

/-- The 71 links of `σ`. -/
def sigNat : ℕ := 0x87676567656545666765654565454345556555656765654565554445556545434543432

/-- Reading a link of `ρ` off the numeral. -/
def rhoD (i : ℕ) : ℕ := (rhoNat >>> (4 * i)) &&& 15

/-- Reading a link of `σ` off the numeral. -/
def sigD (i : ℕ) : ℕ := (sigNat >>> (4 * i)) &&& 15

/-- The point sequence of the pair. -/
def rho71 : Fin 71 → ℤ := fun i => (rhoD i.val : ℤ)

/-- The upper end of the interval of each link. -/
def sig71 : Fin 71 → ℤ := fun i => (sigD i.val : ℤ)

/-- The basepoint: `ρ` stands at `L + 5` there, with `L = 0`. -/
def basept : Fin 71 := ⟨56, by omega⟩

/-! ## Faithfulness

The search of `HPC/Fold/DichotomyFaithful.lean`, in its interval form: a link `i` *carries* the
level `l` when `ρ i ≤ l ≤ σ i`, a level is *met* at `i` when it is carried by `i − 1`, `i` or
`i + 1`, and the clause for the level pair `(x, y)` at `s` is checked at the least index after `s`
at which `y` is met. -/

/-- The link `i` carries the level `l`. -/
def ivHas (i l : ℕ) : Bool := decide (i < 71) && decide (rhoD i ≤ l) && decide (l ≤ sigD i)

/-- The level `y` is met at `i`. -/
def levHas (i y : ℕ) : Bool :=
  (decide (i ≠ 0) && ivHas (i - 1) y) || ivHas i y || ivHas (i + 1) y

/-- The least index at or after `s`, within the given fuel, at which `y` is met. -/
def firstLev (y : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 71 ≤ s then none else if levHas s y then some s else firstLev y fuel (s + 1)

/-- The least index at or after `s`, within the given fuel, carrying the level `v`. -/
def firstIv (v : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 71 ≤ s then none else if ivHas s v then some s else firstIv v fuel (s + 1)

/-- The crookedness clause for the level pair `(x, y)` at `s`, checked at the least index at
which `y` is met. -/
def checkOne (s x y : ℕ) : Bool :=
  if x + 3 ≤ y then
    match firstLev y (71 - s) (s + 1) with
    | none => true
    | some t0 =>
      match firstIv (y - 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match firstIv (x + 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else if y + 3 ≤ x then
    match firstLev y (71 - s) (s + 1) with
    | none => true
    | some t0 =>
      match firstIv (y + 1) (t0 - s) (s + 1) with
      | none => false
      | some r =>
        if t0 ≤ r then false else
          match firstIv (x - 1) (t0 - r) (r + 1) with
          | none => false
          | some r' => decide (r' < t0)
  else true

def checkS (s : ℕ) : Bool :=
  (List.range 10).all fun x =>
    if levHas s x then (List.range 10).all fun y => checkOne s x y else true

def checkAll : Bool := (List.range 71).all checkS

/-- The check passes; kernel evaluation. -/
theorem checkAll_true : checkAll = true := by decide +kernel

/-! ## The specifications of the two searches -/

theorem firstIv_spec : ∀ (v fuel s r : ℕ), firstIv v fuel s = some r →
    s ≤ r ∧ r < 71 ∧ ivHas r v = true := by
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

theorem firstLev_le : ∀ (y fuel s t : ℕ), s ≤ t → t < 71 → t < s + fuel → levHas t y = true →
    ∃ t0, firstLev y fuel s = some t0 ∧ t0 ≤ t := by
  intro y fuel
  induction fuel with
  | zero => intro s t h1 _ h2 _; omega
  | succ f ih =>
    intro s t h1 hlt71 h2 h3
    rw [firstLev]
    split
    · omega
    · split
      · exact ⟨s, rfl, h1⟩
      · rename_i hne
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact absurd h3 (by simpa using hne)
        · exact ih (s + 1) t (by omega) hlt71 (by omega) h3

theorem checkOne_true {s x y : ℕ} (hs : s < 71) (hx : levHas s x = true) (hxlt : x < 10)
    (hylt : y < 10) : checkOne s x y = true := by
  have h := checkAll_true
  rw [checkAll, List.all_eq_true] at h
  have hS := h s (List.mem_range.2 hs)
  rw [checkS, List.all_eq_true] at hS
  have hx' := hS x (List.mem_range.2 hxlt)
  rw [if_pos hx, List.all_eq_true] at hx'
  exact hx' y (List.mem_range.2 hylt)

/-! ## The bridge between the numerals and the two sequences -/

theorem ivHas_iff {i l : ℕ} (hi : i < 71) :
    ivHas i l = true ↔ (rho71 ⟨i, hi⟩ ≤ (l : ℤ) ∧ (l : ℤ) ≤ sig71 ⟨i, hi⟩) := by
  simp only [ivHas, rho71, sig71, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hi, by exact_mod_cast h1⟩, by exact_mod_cast h2⟩

theorem levHas_of_carry {s u : Fin 71} (h : ((u : ℤ) - s.val).natAbs ≤ 1) {l : ℕ}
    (hl : ivHas u.val l = true) : levHas s.val l = true := by
  have hu := u.isLt
  have hs := s.isLt
  have hcase : s.val = u.val + 1 ∨ u.val = s.val ∨ u.val = s.val + 1 := by omega
  rcases hcase with h1 | h1 | h1
  · have hs0 : s.val ≠ 0 := by omega
    have : s.val - 1 = u.val := by omega
    simp [levHas, this, hl, hs0]
  · simp [levHas, h1 ▸ hl]
  · have : s.val + 1 = u.val := by omega
    simp [levHas, this, hl]

/-! ## The pair is faithful -/

theorem faithful : IsCrookedIvF rho71 sig71 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro s t hst h k ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
  -- the two levels lie in `[0, 9]`
  have hrl : ∀ j : Fin 71, 0 ≤ rho71 j := by decide
  have hsu : ∀ j : Fin 71, sig71 j ≤ 9 := by decide
  have hh0 : 0 ≤ h := le_trans (hrl u) hu1
  have hh9 : h ≤ 9 := le_trans hu2 (hsu u)
  have hk0 : 0 ≤ k := le_trans (hrl v) hv1
  have hk9 : k ≤ 9 := le_trans hv2 (hsu v)
  set x : ℕ := h.toNat with hxdef
  set y : ℕ := k.toNat with hydef
  have hxc : (x : ℤ) = h := Int.toNat_of_nonneg hh0
  have hyc : (y : ℤ) = k := Int.toNat_of_nonneg hk0
  have hxlt : x < 10 := by omega
  have hylt : y < 10 := by omega
  have hux : ivHas u.val x = true := (ivHas_iff u.isLt).2 (by rw [hxc]; exact ⟨hu1, hu2⟩)
  have hvy : ivHas v.val y = true := (ivHas_iff v.isLt).2 (by rw [hyc]; exact ⟨hv1, hv2⟩)
  have hsx : levHas s.val x = true := levHas_of_carry hu hux
  have hty : levHas t.val y = true := levHas_of_carry hv hvy
  have hs : s.val < 71 := s.isLt
  have ht : t.val < 71 := t.isLt
  have hstv : s.val < t.val := hst
  have hchk := checkOne_true hs hsx hxlt hylt
  have hcases : x + 3 ≤ y ∨ y + 3 ≤ x := by
    rw [← hxc, ← hyc] at habs
    rcases abs_cases ((x : ℤ) - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  obtain ⟨t0, ht0, ht0le⟩ :=
    firstLev_le y (71 - s.val) (s.val + 1) t.val (by omega) ht (by omega) hty
  rcases hcases with hc | hc
  · rw [checkOne, if_pos hc] at hchk
    simp only [ht0] at hchk
    cases hr : firstIv (y - 1) (t0 - s.val) (s.val + 1) with
    | none => simp [hr] at hchk
    | some r =>
      simp only [hr] at hchk
      obtain ⟨hr1, hr2, hr3⟩ := firstIv_spec _ _ _ _ hr
      by_cases hrt : t0 ≤ r
      · simp [hrt] at hchk
      · rw [if_neg hrt] at hchk
        cases hr' : firstIv (x + 1) (t0 - r) (r + 1) with
        | none => simp [hr'] at hchk
        | some r2 =>
          simp only [hr'] at hchk
          obtain ⟨hs1, hs2, hs3⟩ := firstIv_spec _ _ _ _ hr'
          have hlt2 : r2 < t0 := by simpa using hchk
          have e1 := (ivHas_iff hr2).1 hr3
          have e2 := (ivHas_iff hs2).1 hs3
          have ey : ((y - 1 : ℕ) : ℤ) = k - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ y)]; push_cast; omega
          have ex : ((x + 1 : ℕ) : ℤ) = h + 1 := by push_cast; omega
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
    cases hr : firstIv (y + 1) (t0 - s.val) (s.val + 1) with
    | none => simp [hr] at hchk
    | some r =>
      simp only [hr] at hchk
      obtain ⟨hr1, hr2, hr3⟩ := firstIv_spec _ _ _ _ hr
      by_cases hrt : t0 ≤ r
      · simp [hrt] at hchk
      · rw [if_neg hrt] at hchk
        cases hr' : firstIv (x - 1) (t0 - r) (r + 1) with
        | none => simp [hr'] at hchk
        | some r2 =>
          simp only [hr'] at hchk
          obtain ⟨hs1, hs2, hs3⟩ := firstIv_spec _ _ _ _ hr'
          have hlt2 : r2 < t0 := by simpa using hchk
          have e1 := (ivHas_iff hr2).1 hr3
          have e2 := (ivHas_iff hs2).1 hs3
          have ey : ((y + 1 : ℕ) : ℤ) = k + 1 := by push_cast; omega
          have ex : ((x - 1 : ℕ) : ℤ) = h - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ x)]; push_cast; omega
          rw [ey] at e1
          rw [ex] at e2
          refine ⟨⟨r, hr2⟩, ⟨r2, hs2⟩, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [Fin.lt_def]; omega
          · simp only [Fin.lt_def]; omega
          · simp only [Fin.lt_def]; omega
          · intro hcon; omega
          · intro _; exact ⟨e1, e2⟩

/-! ## The branch hypotheses, the failure and the refutation -/

instance (m : ℕ) (f : Fin m → ℤ) (tl th : ℤ) : Decidable (LowAt f tl th) := by
  unfold LowAt; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) (L : ℤ) : Decidable (Leg3Valley f L) := by
  unfold Leg3Valley; infer_instance

theorem base_level : rho71 basept = 0 + 5 := by decide

theorem band_lo : ∀ t, (0 : ℤ) ≤ rho71 t := by decide

theorem band_hi : ∀ t, rho71 t ≤ 0 + 9 := by decide

theorem lowAt_armG : LowAt (armG rho71 basept) (0 + 1) (0 + 8) := by decide +kernel

theorem lowAt_armT : LowAt (armT rho71 basept) (0 + 1) (0 + 8) := by decide +kernel

/-- The reflection of the forward arm fails the valley clause. -/
theorem not_leg3Valley_reflG :
    ¬ Leg3Valley (armRefl (0 + (0 + 9)) (armG rho71 basept)) 0 := by decide +kernel

/-- The reflection of the backward arm does not fold onto the V-walk based at `L + 5`. -/
theorem not_folds_reflT :
    ¬ FoldsOnto (armRefl (0 + (0 + 9)) (armT rho71 basept)) (veeLen (0 + 5) (0 + 9) 0)
      (veeCenter (0 + 5) (0 + 9) 0) :=
  not_foldsOnto_of_foldsB (by decide +kernel)

end Audit57

/-- **The valley crossing does not reflect.** At the basepoint `56` of the 71-link faithful pair
of `Audit57` the reflection of one arm fails `Leg3Valley` while the reflection of the other does
not fold onto the V-walk, so the reflected crossing is false in the general model. -/
theorem not_reflValleyCrossL5 : ¬ ReflValleyCrossL5 := by
  intro h
  exact Audit57.not_folds_reflT
    ((h 71 Audit57.rho71 Audit57.sig71 Audit57.basept 0 Audit57.faithful Audit57.band_lo
      Audit57.band_hi Audit57.base_level Audit57.lowAt_armG Audit57.lowAt_armT
      (Or.inl Audit57.not_leg3Valley_reflG)).2)

end HPC.Fold
