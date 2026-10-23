import HPC.Fold.Valley72
import HPC.Fold.Decide

/-!
# The valley at `L + 3` is not a fact about a running arm: a faithful counterexample

Batch 71 reduced what the branch `L + 5` owes at a high-run crossing to one landmark pair on the
**running** arm — `Valley3BeforeNine`, equivalently `Ceil72` — and had never seen it fail. Batch 72
asks where it is a fact, and the answer is that the **crossing** is the hypothesis that carries it:
at a basepoint of the branch, with `LowAt` on both arms and nothing else, a running arm can fail it.

The census `census-batch72.c` (log `census-batch72.log`) measures the statement in five classes over
the batch-70 corpus, unchanged — 7040 faithful pairs, 3 151 162 basepoints of the band, 2 444 297 of
the branch, 1351 crossings, 229 high-run crossings:

| class | arms | holds | fails |
| --- | --- | --- | --- |
| the band, `LowAt` asked of nothing | 478 735 | 284 659 | **194 076** |
| the band, `LowAt` on the running arm | 478 735 | 284 659 | **194 076** |
| the branch, `LowAt` on both arms | 478 735 | 284 659 | **194 076** |
| a running arm at a crossing | 229 | 229 | 0 |
| the running arm of a high-run crossing | 229 | 229 | 0 |

The witness below is the shortest window of the first failure the census stores
(`witness-batch72-c2.txt`, trimmed by `min-batch72.c` to `witness-batch72-min.txt`, re-checked
independently by `check72.py`): **78 links**, a thin window of Bing's own chain `bpath 0 9`, with
the basepoint at index `1`, the forward arm running high — its first ascent at arm index 76 — and no
landmark pair before that ascent. Every verdict is put to the kernel, faithfulness included, in the
manner of `HPC/Fold/Audit71.lean`; no `native_decide`.

**What it does and does not touch.** It does not touch `S3`: at the witness, and at all 194 076
failures the census records, a walk of the four-leg family serves both arms. What it settles is the
placement of the statement batch 71 left open — it is a statement about a running arm **at a
crossing**, and the census's line "at every failure the two arms share the walk `w8`" is the reason:
a running arm is always a `w8` arm (`leg4Land_w8_of_run`), so a failing basepoint is a crossing only
if the partner is not a `w8` arm, which no edit of `break-batch72.c` achieved in 55 829 attempts.
-/

set_option maxRecDepth 10000000
set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 4000

namespace HPC.Fold

/-- **The landmark pair, as a general statement about the branch.** At a basepoint of the branch
`L + 5` of a faithful pair of the band, an arm that runs high has the landmark pair of `Ceil72`
before its first ascent. This is the statement batch 71 left the branch owing, with the crossing
dropped; it is refuted by `not_valley3BranchL5` below. -/
def Valley3BranchL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    (HighRunG ρ i L → Valley3BeforeNine (armG ρ i) L) ∧
      (HighRunT ρ i L → Valley3BeforeNine (armT ρ i) L)

namespace Audit72

/-! ## The pair

`ρ = σ`: `4 5 6 5 4 5 4 3 4 5 4 5 6 5 4 5 6 5 6 7 6 5 6 5 4 5 6 5 6 7 6 5 6 7 6 7 8 7 6 7 6 5 6 7 6 5
6 5 4 5 6 5 6 7 6 5 6 7 6 7 8 7 6 7 6 5 6 7 6 7 8 7 6 7 8 7 8 9` — a thin pair, the window
`908 … 985` of the 986-link Bing chain `bpath 0 9` stored as `witness-batch72-c2.txt`.

Both sequences are carried as one natural number each, in base sixteen, the link `i` being the
`i`-th digit. -/

/-- The 78 links of `ρ`. -/
def rhoNat : ℕ := 0x987876787676567678767656765654565676567678767656765654565676565456545434545654

/-- The 78 links of `σ`. -/
def sigNat : ℕ := 0x987876787676567678767656765654565676567678767656765654565676565456545434545654

/-- Reading a link of `ρ` off the numeral. -/
def rhoD (i : ℕ) : ℕ := (rhoNat >>> (4 * i)) &&& 15

/-- Reading a link of `σ` off the numeral. -/
def sigD (i : ℕ) : ℕ := (sigNat >>> (4 * i)) &&& 15

/-- The point sequence of the pair. -/
def rho78 : Fin 78 → ℤ := fun i => (rhoD i.val : ℤ)

/-- The upper end of the interval of each link. -/
def sig78 : Fin 78 → ℤ := fun i => (sigD i.val : ℤ)

/-- The basepoint: `ρ` stands at `L + 5` there, with `L = 0`. -/
def basept : Fin 78 := ⟨1, by omega⟩

/-! ## Faithfulness

The search of `HPC/Fold/DichotomyFaithful.lean`, in its interval form: a link `i` *carries* the
level `l` when `ρ i ≤ l ≤ σ i`, a level is *met* at `i` when it is carried by `i − 1`, `i` or
`i + 1`, and the clause for the level pair `(x, y)` at `s` is checked at the least index after `s`
at which `y` is met. -/

/-- The link `i` carries the level `l`. -/
def ivHas (i l : ℕ) : Bool := decide (i < 78) && decide (rhoD i ≤ l) && decide (l ≤ sigD i)

/-- The level `y` is met at `i`. -/
def levHas (i y : ℕ) : Bool :=
  (decide (i ≠ 0) && ivHas (i - 1) y) || ivHas i y || ivHas (i + 1) y

/-- The least index at or after `s`, within the given fuel, at which `y` is met. -/
def firstLev (y : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 78 ≤ s then none else if levHas s y then some s else firstLev y fuel (s + 1)

/-- The least index at or after `s`, within the given fuel, carrying the level `v`. -/
def firstIv (v : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, s =>
    if 78 ≤ s then none else if ivHas s v then some s else firstIv v fuel (s + 1)

/-- The crookedness clause for the level pair `(x, y)` at `s`, checked at the least index at
which `y` is met. -/
def checkOne (s x y : ℕ) : Bool :=
  if x + 3 ≤ y then
    match firstLev y (78 - s) (s + 1) with
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
    match firstLev y (78 - s) (s + 1) with
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

def checkAll : Bool := (List.range 78).all checkS

/-- The check passes; kernel evaluation. -/
theorem checkAll_true : checkAll = true := by decide +kernel

/-! ## The specifications of the two searches -/

theorem firstIv_spec : ∀ (v fuel s r : ℕ), firstIv v fuel s = some r →
    s ≤ r ∧ r < 78 ∧ ivHas r v = true := by
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

theorem firstLev_le : ∀ (y fuel s t : ℕ), s ≤ t → t < 78 → t < s + fuel → levHas t y = true →
    ∃ t0, firstLev y fuel s = some t0 ∧ t0 ≤ t := by
  intro y fuel
  induction fuel with
  | zero => intro s t h1 _ h2 _; omega
  | succ f ih =>
    intro s t h1 hlt78 h2 h3
    rw [firstLev]
    split
    · omega
    · split
      · exact ⟨s, rfl, h1⟩
      · rename_i hne
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact absurd h3 (by simpa using hne)
        · exact ih (s + 1) t (by omega) hlt78 (by omega) h3

theorem checkOne_true {s x y : ℕ} (hs : s < 78) (hx : levHas s x = true) (hxlt : x < 10)
    (hylt : y < 10) : checkOne s x y = true := by
  have h := checkAll_true
  rw [checkAll, List.all_eq_true] at h
  have hS := h s (List.mem_range.2 hs)
  rw [checkS, List.all_eq_true] at hS
  have hx' := hS x (List.mem_range.2 hxlt)
  rw [if_pos hx, List.all_eq_true] at hx'
  exact hx' y (List.mem_range.2 hylt)

/-! ## The bridge between the numerals and the two sequences -/

theorem ivHas_iff {i l : ℕ} (hi : i < 78) :
    ivHas i l = true ↔ (rho78 ⟨i, hi⟩ ≤ (l : ℤ) ∧ (l : ℤ) ≤ sig78 ⟨i, hi⟩) := by
  simp only [ivHas, rho78, sig78, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hi, by exact_mod_cast h1⟩, by exact_mod_cast h2⟩

theorem levHas_of_carry {s u : Fin 78} (h : ((u : ℤ) - s.val).natAbs ≤ 1) {l : ℕ}
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

theorem faithful : IsCrookedIvF rho78 sig78 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rintro s t hst h k ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
  -- the two levels lie in `[0, 9]`
  have hrl : ∀ j : Fin 78, 0 ≤ rho78 j := by decide +kernel
  have hsu : ∀ j : Fin 78, sig78 j ≤ 9 := by decide +kernel
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
  have hs : s.val < 78 := s.isLt
  have ht : t.val < 78 := t.isLt
  have hstv : s.val < t.val := hst
  have hchk := checkOne_true hs hsx hxlt hylt
  have hcases : x + 3 ≤ y ∨ y + 3 ≤ x := by
    rw [← hxc, ← hyc] at habs
    rcases abs_cases ((x : ℤ) - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  obtain ⟨t0, ht0, ht0le⟩ :=
    firstLev_le y (78 - s.val) (s.val + 1) t.val (by omega) ht (by omega) hty
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

instance {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Decidable (HighRunG ρ i L) := by
  unfold HighRunG; infer_instance

instance {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Decidable (Valley3BeforeNine f L) := by
  unfold Valley3BeforeNine; infer_instance

instance {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Decidable (Ceil72 f L) := by
  unfold Ceil72; infer_instance

theorem lip : IsLip rho78 := by decide +kernel

theorem base_level : rho78 basept = 0 + 5 := by decide +kernel

theorem band_lo : ∀ t, (0 : ℤ) ≤ rho78 t := by decide +kernel

theorem band_hi : ∀ t, rho78 t ≤ 0 + 9 := by decide +kernel

theorem lowAt_armG : LowAt (armG rho78 basept) (0 + 1) (0 + 8) := by decide +kernel

theorem lowAt_armT : LowAt (armT rho78 basept) (0 + 1) (0 + 8) := by decide +kernel

/-- The forward arm runs high: it reaches `L + 9` — at arm index 76 — with nothing at `L + 2` or
below before it. -/
theorem highRun_armG : HighRunG rho78 basept 0 := by decide +kernel

/-- **The landmark pair is not there.** The forward arm has no peak at `L + 6` or above at arm
index three or more with a time at `L + 3` or below five steps later and six steps before its
ascent: its only time at `L + 3` or below sits at arm index 6, and nothing at `L + 6` or above
precedes it. -/
theorem not_valley3_armG : ¬ Valley3BeforeNine (armG rho78 basept) 0 := by decide +kernel

/-- **And so the ceiling clause fails too**, as `ceil72_of_valley3BeforeNine` and
`valley3BeforeNine_of_ceil72` say it must. -/
theorem not_ceil72_armG : ¬ Ceil72 (armG rho78 basept) 0 := by decide +kernel

end Audit72

/-- **The landmark pair of the ceiling clause is not a fact about a running arm of the branch.** At
the basepoint `1` of the 78-link faithful pair of `Audit72` — a window of Bing's chain `bpath 0 9` —
the band is `[L, L + 9]`, both arms satisfy `LowAt (L + 1) (L + 8)`, the forward arm runs high, and
`Valley3BeforeNine` fails on it; equivalently `Ceil72` fails on it. So the statement the branch at
`L + 5` owes at a high-run crossing (batch 71 §2.6) needs the **crossing**: it is false for a
running arm of a faithful pair with the branch hypothesis alone. -/
theorem not_valley3BranchL5 : ¬ Valley3BranchL5 := by
  intro h
  exact Audit72.not_valley3_armG
    ((h 78 Audit72.rho78 Audit72.sig78 Audit72.basept 0 Audit72.lip Audit72.faithful
      Audit72.band_lo Audit72.band_hi Audit72.base_level Audit72.lowAt_armG
      Audit72.lowAt_armT).1 Audit72.highRun_armG)

end HPC.Fold
