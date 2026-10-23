import HPC.Fold.Distance71
import HPC.Fold.Decide

/-!
# The distance is false: a faithful counterexample at a high-run crossing

Batch 70 left the branch `L + 5` owing one statement at a high-run crossing of the trichotomy: the
distance, `NearLowBandT` / `NearLowBandG` — *a time of the pair at `L + 2` or below within 67 steps
before the basepoint, or at `L + 1` or below within 166, or at the floor within 405*. On the whole
corpus of batch 70 and batch 71 — 7040 faithful pairs, 2 444 297 basepoints, 1351 crossings, 229
high-run crossings in 52 configurations — the first reading holds at every one, the nearest such
time never leaving the range 56 to 65.

**It is false.** Batch 71 §2.4 asked for a construction rather than more sampling, and the
construction succeeds: `break-batch71.c` lengthens the partner's approach to the basepoint of a
stored high-run crossing — reflecting and re-appending a stretch of the approach that stays at
`L + 3` or above — and the edited pair stays faithful, stays a crossing of the trichotomy, keeps
its high run, and pushes the nearest time at `L + 2` or below from 60 steps to 185. At the 2229
high-run crossings the construction produces, **all three** readings of `NearLowBandT` fail (the
nearest time at `L + 1` or below is 307 to 424 steps away, against 166; the nearest at the floor
884 to 1001, against 405).

The witness below is the shortest window of the most extreme of them that still breaks the
statement (`min-batch71.c`, log `min-batch71.log`, stored in `witness-batch71-min.txt` and
re-checked independently by `check71.py`, log `check71.log`): **290 links**, basepoint `104`, the
`w8` side the *backward* arm. Every verdict here is put to the kernel, faithfulness included, in
the manner of `HPC/Fold/Audit57.lean`.

**What the counterexample does and does not touch.** It refutes the *hypothesis* the batch-69 and
batch-70 assemblies carry, not the statement they prove: at all 2229 constructed crossings the
ceiling clause `Ceil72` still holds on both arms, both arms still satisfy the landmark sentence of
`w72`, and four walks of the four-leg family serve both arms. So `S3` at span nine is untouched,
and what is now known is that the reading of batch 69 — the pairing from a low time near the
basepoint — is **not** the source of the ceiling clause in general. The distance is not the
branch's remaining obligation; `Ceil72` itself is.

The extreme break itself is a faithful pair of 1106 links whose band is exactly `[L, L + 9]`
(`witness-batch71.txt`); the 290-link window below has band `[L + 2, L + 9]`, which satisfies every
hypothesis of the assembly (`s3_span_nine_mid5_of_cross_highRun_band_armT` asks only for the two
bounds `L ≤ ρ` and `ρ ≤ L + 9`), and both are checked by `check71.py`.
-/

set_option maxRecDepth 10000000
set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 4000

namespace HPC.Fold

/-- **The distance, as a general statement about high-run crossings.** At a crossing of the
trichotomy at the branch `L + 5`, the arm that runs high has a time of the pair at one of the three
levels the pairing can be read from, within the bound that reading gives, on the other side of the
basepoint. This is the one hypothesis the batch-70 assembly still carries; it is refuted by
`not_nearLowBandCrossL5` below. -/
def NearLowBandCrossL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    TriCrossL5 ρ i L →
    (HighRunG ρ i L → NearLowBandT ρ i L) ∧ (HighRunT ρ i L → NearLowBandG ρ i L)

namespace Audit71

/-! ## The pair

`ρ`: `9 8 7 8 7 6 7 8 7 6 7 6 5 6 7 6 7 7 7 6 7 6 5 6 7 6 5 6 5 4 5 6 5 6 7 6 5 6 7 6 7 8 7 6 7 6 5 6 7 6 5 6 5 4 5 6 5 6 6 6 5 6 5 4 5 6 5 4 5 4 3 4 4 4 5 6 5 4 5 6 5 6 6 6 5 6 5 4 5 6 5 6 6 6 5 6 7 6 7 8 7 6 7 6 5 6 6 6 5 6 5 4 5 6 5 6 6 6 5 5 5 4 5 6 5 4 5 4 3 4 5 4 5 6 5 4 5 5 5 6 6 6 5 6 5 4 5 6 5 4 5 4 3 4 4 4 5 5 5 4 4 4 3 4 4 4 3 4 4 4 5 5 5 4 4 4 3 4 5 4 5 6 5 4 5 6 5 6 6 6 5 5 5 4 5 6 5 4 5 4 3 4 5 4 5 6 5 4 5 5 5 6 6 6 5 6 5 4 5 6 5 6 6 6 5 6 6 6 5 6 5 4 5 6 5 6 6 6 5 5 5 4 5 6 5 4 5 4 3 4 5 4 5 6 5 4 5 5 5 6 6 6 5 6 5 4 5 6 5 4 5 4 3 4 4 4 5 5 5 4 4 4 3 4 4 4 3 4 3 2`.

`σ`: `9 8 7 8 7 6 7 8 7 6 7 6 6 6 7 6 7 8 7 6 7 6 5 6 7 6 6 6 5 5 5 6 5 6 7 6 5 6 7 6 7 8 7 7 7 6 5 6 7 6 5 6 5 5 5 6 5 6 7 6 5 6 5 5 5 6 5 4 5 4 3 4 5 5 5 6 5 4 5 6 5 6 7 6 6 6 5 5 5 6 5 6 7 6 5 6 7 7 7 8 7 6 7 6 5 6 7 6 5 6 5 5 5 6 5 6 7 6 5 6 5 5 5 6 5 5 5 4 3 4 5 5 5 6 5 4 5 6 5 6 7 6 6 6 5 5 5 6 5 4 5 4 4 4 5 4 5 6 5 5 5 4 4 4 5 4 4 4 5 5 5 6 5 4 5 4 4 4 5 4 5 6 5 5 5 6 6 6 7 6 5 6 5 4 5 6 5 5 5 4 3 4 5 5 5 6 5 5 5 6 5 6 7 6 5 6 5 5 5 6 5 6 7 6 5 6 7 6 5 6 5 5 5 6 5 6 7 6 5 6 5 5 5 6 5 5 5 4 3 4 5 5 5 6 5 4 5 6 5 6 7 6 6 6 5 5 5 6 5 4 5 4 4 4 5 4 5 6 5 5 5 4 4 4 5 4 3 4 3 2`.

Both are carried as one natural number each, in base sixteen, the link `i` being the `i`-th
digit. -/

/-- The 290 links of `ρ`. -/
def rhoNat : ℕ := 0x23434443444555444345456545656665554565454345456545556665654565666566656545656665554565454345456545556665654565454344455544434443444555444345456545656665554565454345456545556665654565666567678767656665654565666565456544434545654565666565456567656767876765676565456567656767776765676787678789

/-- The 290 links of `σ`. -/
def sigNat : ℕ := 0x23434544455565454445456555666765654565554345556555656765655565676567656555656765655565554345556545656766655565454445456555444544455565454445456555666765654565554345556555656765655565676567678777656765655566676565456555434545655565676565556567656777876765676565556667656767876766676787678789

/-- Reading a link of `ρ` off the numeral. -/
def rhoD (i : ℕ) : ℕ := (rhoNat >>> (4 * i)) &&& 15

/-- Reading a link of `σ` off the numeral. -/
def sigD (i : ℕ) : ℕ := (sigNat >>> (4 * i)) &&& 15

/-- The point sequence of the pair. -/
def rho290 : Fin 290 → ℤ := fun i => (rhoD i.val : ℤ)

/-- The upper end of the interval of each link. -/
def sig290 : Fin 290 → ℤ := fun i => (sigD i.val : ℤ)

/-- The basepoint: `ρ` stands at `L + 5` there, with `L = 0`. -/
def basept : Fin 290 := ⟨104, by omega⟩

/-! ## Faithfulness

The search of `HPC/Fold/DichotomyFaithful.lean`, in its interval form: a link `i` *carries* the
level `l` when `ρ i ≤ l ≤ σ i`, a level is *met* at `i` when it is carried by `i − 1`, `i` or
`i + 1`, and the clause for the level pair `(x, y)` at `s` is checked at the least index after `s`
at which `y` is met. -/

/-- The link `i` carries the level `l`. -/
def ivHas (i l : ℕ) : Bool := decide (i < 290) && decide (rhoD i ≤ l) && decide (l ≤ sigD i)

/-- The level `y` is met at `i`. -/
def levHas (i y : ℕ) : Bool :=
  (decide (i ≠ 0) && ivHas (i - 1) y) || ivHas i y || ivHas (i + 1) y

/-- The least index at or after `s`, within the given fuel, at which `y` is met. -/
def firstLev (y : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 290 ≤ s then none else if levHas s y then some s else firstLev y fuel (s + 1)

/-- The least index at or after `s`, within the given fuel, carrying the level `v`. -/
def firstIv (v : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 290 ≤ s then none else if ivHas s v then some s else firstIv v fuel (s + 1)

/-- The crookedness clause for the level pair `(x, y)` at `s`, checked at the least index at
which `y` is met. -/
def checkOne (s x y : ℕ) : Bool :=
  if x + 3 ≤ y then
    match firstLev y (290 - s) (s + 1) with
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
    match firstLev y (290 - s) (s + 1) with
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

def checkAll : Bool := (List.range 290).all checkS

/-- The check passes; kernel evaluation. -/
theorem checkAll_true : checkAll = true := by decide +kernel

/-! ## The specifications of the two searches -/

theorem firstIv_spec : ∀ (v fuel s r : ℕ), firstIv v fuel s = some r →
    s ≤ r ∧ r < 290 ∧ ivHas r v = true := by
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

theorem firstLev_le : ∀ (y fuel s t : ℕ), s ≤ t → t < 290 → t < s + fuel → levHas t y = true →
    ∃ t0, firstLev y fuel s = some t0 ∧ t0 ≤ t := by
  intro y fuel
  induction fuel with
  | zero => intro s t h1 _ h2 _; omega
  | succ f ih =>
    intro s t h1 hlt290 h2 h3
    rw [firstLev]
    split
    · omega
    · split
      · exact ⟨s, rfl, h1⟩
      · rename_i hne
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact absurd h3 (by simpa using hne)
        · exact ih (s + 1) t (by omega) hlt290 (by omega) h3

theorem checkOne_true {s x y : ℕ} (hs : s < 290) (hx : levHas s x = true) (hxlt : x < 10)
    (hylt : y < 10) : checkOne s x y = true := by
  have h := checkAll_true
  rw [checkAll, List.all_eq_true] at h
  have hS := h s (List.mem_range.2 hs)
  rw [checkS, List.all_eq_true] at hS
  have hx' := hS x (List.mem_range.2 hxlt)
  rw [if_pos hx, List.all_eq_true] at hx'
  exact hx' y (List.mem_range.2 hylt)

/-! ## The bridge between the numerals and the two sequences -/

theorem ivHas_iff {i l : ℕ} (hi : i < 290) :
    ivHas i l = true ↔ (rho290 ⟨i, hi⟩ ≤ (l : ℤ) ∧ (l : ℤ) ≤ sig290 ⟨i, hi⟩) := by
  simp only [ivHas, rho290, sig290, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hi, by exact_mod_cast h1⟩, by exact_mod_cast h2⟩

theorem levHas_of_carry {s u : Fin 290} (h : ((u : ℤ) - s.val).natAbs ≤ 1) {l : ℕ}
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

theorem faithful : IsCrookedIvF rho290 sig290 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rintro s t hst h k ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
  -- the two levels lie in `[0, 9]`
  have hrl : ∀ j : Fin 290, 0 ≤ rho290 j := by decide +kernel
  have hsu : ∀ j : Fin 290, sig290 j ≤ 9 := by decide +kernel
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
  have hs : s.val < 290 := s.isLt
  have ht : t.val < 290 := t.isLt
  have hstv : s.val < t.val := hst
  have hchk := checkOne_true hs hsx hxlt hylt
  have hcases : x + 3 ≤ y ∨ y + 3 ≤ x := by
    rw [← hxc, ← hyc] at habs
    rcases abs_cases ((x : ℤ) - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  obtain ⟨t0, ht0, ht0le⟩ :=
    firstLev_le y (290 - s.val) (s.val + 1) t.val (by omega) ht (by omega) hty
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


/-! ## The branch hypotheses, the high run, and the failure of the distance -/

instance (m : ℕ) (f : Fin m → ℤ) : Decidable (IsLip f) := by
  unfold IsLip; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) (tl th : ℤ) : Decidable (LowAt f tl th) := by
  unfold LowAt; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) (H K M P : ℤ) : Decidable (Leg4Land f H K M P) := by
  unfold Leg4Land; infer_instance

instance {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Decidable (HighRunT ρ i L) := by
  unfold HighRunT; infer_instance

instance {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Decidable (NearLowBandG ρ i L) := by
  unfold NearLowBandG; infer_instance

theorem lip : IsLip rho290 := by decide +kernel

theorem base_level : rho290 basept = 0 + 5 := by decide +kernel

theorem band_lo : ∀ t, (0 : ℤ) ≤ rho290 t := by decide +kernel

theorem band_hi : ∀ t, rho290 t ≤ 0 + 9 := by decide +kernel

theorem lowAt_armG : LowAt (armG rho290 basept) (0 + 1) (0 + 8) := by decide +kernel

theorem lowAt_armT : LowAt (armT rho290 basept) (0 + 1) (0 + 8) := by decide +kernel

/-- The forward arm is not a `w8` arm. -/
theorem not_w8_armG : ¬ Leg4Land (armG rho290 basept) (0 + 9) (0 + 8) (0 + 1) (0 + 5) := by
  decide +kernel

/-- The backward arm is neither a `wb` arm nor a `w3` arm. -/
theorem not_wb_armT :
    ¬ Leg4Land (armRefl (0 + (0 + 9)) (armT rho290 basept)) (0 + 9) (0 + 6) (0 + 2) (0 + 4) := by
  decide +kernel

theorem not_w3_armT :
    ¬ Leg4Land (armRefl (0 + (0 + 9)) (armT rho290 basept)) (0 + 9) (0 + 6) (0 + 1) (0 + 4) := by
  decide +kernel

/-- The basepoint is a crossing of the trichotomy. -/
theorem cross : TriCrossL5 rho290 basept 0 :=
  ⟨fun h => not_w8_armG h.1, fun h => not_w3_armT h.2, fun h => not_wb_armT h.2⟩

/-- The backward arm runs high: it reaches `L + 9` with nothing at `L + 2` or below before it. -/
theorem highRun_armT : HighRunT rho290 basept 0 := by decide +kernel

/-- **The distance fails**: the pair has no time at `L + 2` or below within 67 steps past the
basepoint, none at `L + 1` or below within 166, and none at the floor within 405. -/
theorem not_nearLowBandG : ¬ NearLowBandG rho290 basept 0 := by decide +kernel

end Audit71

/-- **The distance is not a theorem of the general model.** At the basepoint `104` of the 290-link
faithful pair of `Audit71` the backward arm runs high at a crossing of the trichotomy, and the pair
has no time at `L + 2` or below within 67 steps of the basepoint on the forward side — nor at
`L + 1` or below within 166, nor at the floor within 405. -/
theorem not_nearLowBandCrossL5 : ¬ NearLowBandCrossL5 := by
  intro h
  exact Audit71.not_nearLowBandG
    ((h 290 Audit71.rho290 Audit71.sig290 Audit71.basept 0 Audit71.lip Audit71.faithful
      Audit71.band_lo Audit71.band_hi Audit71.base_level Audit71.lowAt_armG Audit71.lowAt_armT
      Audit71.cross).2 Audit71.highRun_armT)

end HPC.Fold
