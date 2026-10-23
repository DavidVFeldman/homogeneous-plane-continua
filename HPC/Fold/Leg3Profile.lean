import HPC.Fold.Leg3Deep
import HPC.Fold.Profile

/-!
# The three-leg walk, asked for in profile form

`foldsOnto_leg3_deep` (`HPC/Fold/Leg3Deep.lean`) folds an arm based at `L + 4` onto the walk

```
L+3, L+4, L+5, L+6, L+5, L+4, L+3, L+2, L+1, L+2, L+3, L+4, L+5, L+6, L+7, L+8
```

as soon as two announcements hold, each of which asks the arm for a time **at** the peak level
`L + 6`. Batch 46 refuted both as necessary conditions, and they are refuted for the same reason
the general model is hard: the crookedness clause of the general model returns a *link* meeting
`L + 6`, whose point may stand at `L + 5`.

The walk does not need `L + 6`. Its window tolerance is one, so an arm standing at `L + 5` when
the walk stands at its peak is tracked exactly as well — provided it stands there *late enough*.
That is the same trade the Λ-criterion of `HPC/Fold/Profile.lean` makes: `CritLamProfile` asks for
the level `κ - 1`, one below the peak, at an index at least `κ - p`. This file states the two
announcements in that form:

* `Leg3Valley` — every descent to `L + 1` at a step `d` is preceded by a time at `L + 5` or above
  at a step `j` with `3 ≤ j` and `j + 5 ≤ d`;
* `Leg3Ceil` — every ascent to `L + 8` at a step `d` is preceded by such a `j` and, after it, by a
  time at `L + 2` or below at a step `k` with `j + 5 ≤ k` and `k + 6 ≤ d`.

The three index bounds are the three landmarks of the walk: it stands at `L + 6` at its position
`3`, at `L + 1` at its position `8`, and at `L + 7` at its position `14`, and it advances at most
one position per step.

`foldsOnto_leg3deep_profile` is the statement that these two suffice. It is a statement about
1-Lipschitz arms alone — no crookedness, exactly like `foldsOnto_leg3_deep`. The evidence that
preceded the proof is `census-batch47c.c`: over **every** 1-Lipschitz arm in `[0, 9]` of
length at most sixteen starting at `L + 4` (11 809 035 of them at length sixteen) no arm meets the
criterion and fails to fold, while 59 982 of the 7 183 837 folding arms fail the criterion, so it
is sufficient and nearly necessary; and over two million random arms of lengths 17 to 196 there is
again no arm meeting it that fails to fold.

## The proof, in batch 48

The greedy time `gseq3` of `HPC/Fold/Leg3.lean` is carried by four numerical invariants instead
of the four history features of `HPC/Fold/Leg3Deep.lean`, and it is the *clock* — the walk
advances at most one position per step, so its position at step `t` is at most `t` — that
replaces the peak level in each of them. Writing `q t` for the greedy time and `a t = u t - L`
for the arm's height above the floor:

* **the clock** `min (min t (a t - 2)) 3 ≤ q t`: before the greedy time reaches the peak position
  `3`, it is at least the arm's own first-leg position `a t - 2`, and at least the step count;
* **`R`** — once the arm has stood at `L + 5` or above at a step `3` or later, `8 - a t ≤ q t`
  for ever after: the clock puts the greedy time at the peak position `3` at that step, which is
  the `R` bound there, and the bound then propagates;
* **the slack clock** `min (min (10 - a t) 8) (t - j + 3) ≤ q t` for every landmark `j` as above:
  after the landmark the greedy time gains one position per step until it reaches the far end
  `min (10 - a t) 8` of the second leg. This is where `j + 5 ≤ k` is spent: five steps carry the
  greedy time from the peak position `3` to the valley position `8`;
* **`S`** — once the slack clock has reached the valley at a step `k` where the arm stands at
  `L + 2` or below, `a t + 6 ≤ q t` for ever after, which is the `S` bound.

`prog3_profile` is the one-step lemma for the four, `gseq3_inv_profile` the induction.
-/

namespace HPC.Fold

/-- **The valley clause in profile form.** Every descent to `L + 1` is preceded by a time at
`L + 5` or above, at a step at least `3` and at least five steps before the descent. -/
def Leg3Valley {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 →
    ∃ j : Fin m, 3 ≤ j.val ∧ j.val + 5 ≤ d.val ∧ L + 5 ≤ f j

/-- **The ceiling clause in profile form.** Every ascent to `L + 8` is preceded by a time at
`L + 5` or above at a step at least `3`, and after it by a time at `L + 2` or below, five steps
later or more, itself six steps or more before the ascent. -/
def Leg3Ceil {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 8 ≤ f d →
    ∃ j k : Fin m, 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 6 ≤ d.val ∧
      L + 5 ≤ f j ∧ f k ≤ L + 2

/-- **The valley clause in the form the proof consumes.** Of the two index bounds of
`Leg3Valley` only `3 ≤ j` is spent: the descent has to come after the landmark, not five steps
after it. -/
def Leg3ValleyMin {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ j.val ∧ j.val < d.val ∧ L + 5 ≤ f j

/-- **The ceiling clause in the form the proof consumes.** Of the three index bounds of
`Leg3Ceil` two are spent, `3 ≤ j` and `j + 5 ≤ k`; the ascent has only to come after `k`. -/
def Leg3CeilMin {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 8 ≤ f d →
    ∃ j k : Fin m, 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val < d.val ∧
      L + 5 ≤ f j ∧ f k ≤ L + 2

/-- The commissioned clauses are the ones the proof consumes. -/
theorem leg3ValleyMin_of_leg3Valley {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : Leg3Valley f L) :
    Leg3ValleyMin f L := by
  intro d hd
  obtain ⟨j, h3, h5, hj⟩ := h d hd
  exact ⟨j, h3, by omega, hj⟩

/-- The commissioned clauses are the ones the proof consumes. -/
theorem leg3CeilMin_of_leg3Ceil {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : Leg3Ceil f L) :
    Leg3CeilMin f L := by
  intro d hd
  obtain ⟨j, k, h3, hjk, hkd, hj, hk⟩ := h d hd
  exact ⟨j, k, h3, hjk, by omega, hj, hk⟩

set_option maxHeartbeats 4000000 in
/-- **The progress clauses of the profile form**, at the band `[L, L + 9]`, the peak `L + 6` and
the basepoint `L + 4`. In order: the clock, the `R` bound, the `S` bound, the far end of the
second leg, and the slack clock — a greedy time that is past the peak and short of the far end
advances by one position at every step. -/
theorem prog3_profile {L v q v' : ℤ} (hv0 : L ≤ v) (hvH : v ≤ L + 9) (hv'0 : L ≤ v')
    (hv'H : v' ≤ L + 9) (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1)
    (hnew : Val3 L (L + 9) (L + 6) (L + 4) v' (gstep3 L (L + 9) (L + 6) (L + 4) v' q)) :
    (∀ n : ℤ, min (min n (v - L - 2)) 3 ≤ q →
        min (min (n + 1) (v' - L - 2)) 3 ≤ gstep3 L (L + 9) (L + 6) (L + 4) v' q) ∧
    (L + 8 - v ≤ q → L + 8 - v' ≤ gstep3 L (L + 9) (L + 6) (L + 4) v' q) ∧
    (v - L + 6 ≤ q → v' - L + 6 ≤ gstep3 L (L + 9) (L + 6) (L + 4) v' q) ∧
    (min (L + 10 - v) 8 ≤ q → min (L + 10 - v') 8 ≤ gstep3 L (L + 9) (L + 6) (L + 4) v' q) ∧
    (∀ n : ℤ, L + 8 - v ≤ q → min (min (L + 10 - v) 8) n ≤ q →
        min (min (L + 10 - v') 8) (n + 1) ≤ gstep3 L (L + 9) (L + 6) (L + 4) v' q) := by
  refine gstep3_facts
    (fun g => (∀ n : ℤ, min (min n (v - L - 2)) 3 ≤ q → min (min (n + 1) (v' - L - 2)) 3 ≤ g) ∧
      (L + 8 - v ≤ q → L + 8 - v' ≤ g) ∧
      (v - L + 6 ≤ q → v' - L + 6 ≤ g) ∧
      (min (L + 10 - v) 8 ≤ q → min (L + 10 - v') 8 ≤ g) ∧
      (∀ n : ℤ, L + 8 - v ≤ q → min (min (L + 10 - v) 8) n ≤ q →
        min (min (L + 10 - v') 8) (n + 1) ≤ g)) hnew ?_
  intro g hgv hcase hmax hstay
  unfold Val3 at hgv hmax hstay
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega

set_option maxHeartbeats 1000000 in
/-- **The invariant in profile form.** A 1-Lipschitz level sequence in `[L, L + 9]` based at
`L + 4` whose descents to `L + 1` and ascents to `L + 8` are announced in profile form keeps the
greedy time legal, and carries the clock, the `R` bound, the slack clock and the `S` bound. -/
theorem gseq3_inv_profile (L : ℤ) (u : ℕ → ℤ) (N : ℕ)
    (hu0 : u 0 = L + 4)
    (hlo : ∀ j, j ≤ N → L ≤ u j) (hhi : ∀ j, j ≤ N → u j ≤ L + 9)
    (hlip : ∀ j, j + 1 ≤ N → u j - 1 ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1)
    (hvalley : ∀ d, d ≤ N → u d ≤ L + 1 → ∃ j, 3 ≤ j ∧ j < d ∧ L + 5 ≤ u j)
    (hceil : ∀ d, d ≤ N → L + 8 ≤ u d →
      ∃ j k, 3 ≤ j ∧ j + 5 ≤ k ∧ k < d ∧ L + 5 ≤ u j ∧ u k ≤ L + 2) :
    ∀ t, t ≤ N →
      Val3 L (L + 9) (L + 6) (L + 4) (u t) (gseq3 L (L + 9) (L + 6) (L + 4) u t) ∧
      min (min (t : ℤ) (u t - L - 2)) 3 ≤ gseq3 L (L + 9) (L + 6) (L + 4) u t ∧
      ((∃ j, j ≤ t ∧ 3 ≤ j ∧ L + 5 ≤ u j) →
        L + 8 - u t ≤ gseq3 L (L + 9) (L + 6) (L + 4) u t) ∧
      (∀ j, j ≤ t → 3 ≤ j → L + 5 ≤ u j →
        min (min (L + 10 - u t) 8) ((t : ℤ) - (j : ℤ) + 3) ≤
          gseq3 L (L + 9) (L + 6) (L + 4) u t) ∧
      ((∃ j k, k ≤ t ∧ 3 ≤ j ∧ j + 5 ≤ k ∧ L + 5 ≤ u j ∧ u k ≤ L + 2) →
        u t - L + 6 ≤ gseq3 L (L + 9) (L + 6) (L + 4) u t) := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [gseq3_zero, hu0]
        unfold Val3
        omega
      · rw [gseq3_zero, hu0]
        push_cast
        omega
      · rintro ⟨j, hj, h3, -⟩
        omega
      · intro j hj h3 _
        omega
      · rintro ⟨j, k, hk, h3, hjk, -, -⟩
        omega
  | succ t ih =>
      intro ht
      obtain ⟨hval, hclock, hR, hC, hS⟩ := ih (by omega)
      have hv0 := hlo t (by omega)
      have hvH := hhi t (by omega)
      have hv'0 := hlo (t + 1) ht
      have hv'H := hhi (t + 1) ht
      obtain ⟨hl1, hl2⟩ := hlip t ht
      have hcast : ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by push_cast; ring
      -- the two announcements, read at the step `t + 1`
      have hA0 : u (t + 1) ≤ L + 1 → L + 8 - u t ≤ gseq3 L (L + 9) (L + 6) (L + 4) u t := by
        intro h
        obtain ⟨j, h3, hj5, hju⟩ := hvalley (t + 1) ht h
        exact hR ⟨j, by omega, h3, hju⟩
      have hA1 : L + 8 ≤ u (t + 1) → u t - L + 6 ≤ gseq3 L (L + 9) (L + 6) (L + 4) u t := by
        intro h
        obtain ⟨j, k, h3, hjk, hkd, hju, hku⟩ := hceil (t + 1) ht h
        exact hS ⟨j, k, by omega, h3, hjk, hju, hku⟩
      have hnew : Val3 L (L + 9) (L + 6) (L + 4) (u (t + 1))
          (gseq3 L (L + 9) (L + 6) (L + 4) u (t + 1)) := by
        rw [gseq3_succ]
        refine val3_gstep_deep (by omega) (by omega) (by omega) (by omega) hv0 hvH hv'0 hv'H
          hl1 hl2 hval ?_ ?_
        · intro h
          have := hA0 (by omega)
          omega
        · intro h
          have := hA1 (by omega)
          omega
      obtain ⟨p1, p2, p3, p4, p5⟩ :=
        prog3_profile hv0 hvH hv'0 hv'H hl1 hl2 (by rw [← gseq3_succ]; exact hnew)
      rw [gseq3_succ] at hnew ⊢
      -- the clock
      have hclock' : min (min ((t + 1 : ℕ) : ℤ) (u (t + 1) - L - 2)) 3 ≤
          gstep3 L (L + 9) (L + 6) (L + 4) (u (t + 1)) (gseq3 L (L + 9) (L + 6) (L + 4) u t) := by
        have := p1 (t : ℤ) hclock
        rw [hcast]
        exact this
      -- the `R` bound
      have hR' : (∃ j, j ≤ t + 1 ∧ 3 ≤ j ∧ L + 5 ≤ u j) →
          L + 8 - u (t + 1) ≤
            gstep3 L (L + 9) (L + 6) (L + 4) (u (t + 1))
              (gseq3 L (L + 9) (L + 6) (L + 4) u t) := by
        rintro ⟨j, hj, h3, hju⟩
        rcases Nat.lt_or_ge j (t + 1) with h | h
        · exact p2 (hR ⟨j, by omega, h3, hju⟩)
        · have hjt : j = t + 1 := by omega
          rw [hjt] at hju
          have h3' : (3 : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by exact_mod_cast show 3 ≤ t + 1 by omega
          omega
      -- the slack clock
      have hC' : ∀ j, j ≤ t + 1 → 3 ≤ j → L + 5 ≤ u j →
          min (min (L + 10 - u (t + 1)) 8) (((t + 1 : ℕ) : ℤ) - (j : ℤ) + 3) ≤
            gstep3 L (L + 9) (L + 6) (L + 4) (u (t + 1))
              (gseq3 L (L + 9) (L + 6) (L + 4) u t) := by
        intro j hj h3 hju
        rcases Nat.lt_or_ge j (t + 1) with h | h
        · have hRt := hR ⟨j, by omega, h3, hju⟩
          have hCt := hC j (by omega) h3 hju
          have := p5 ((t : ℤ) - (j : ℤ) + 3) hRt hCt
          rw [hcast]
          have e : (t : ℤ) - (j : ℤ) + 3 + 1 = (t : ℤ) + 1 - (j : ℤ) + 3 := by ring
          rw [e] at this
          exact this
        · have hjt : j = t + 1 := by omega
          have hjc : ((j : ℕ) : ℤ) = ((t + 1 : ℕ) : ℤ) := by rw [hjt]
          rw [hjt] at hju
          have h3' : (3 : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by exact_mod_cast show 3 ≤ t + 1 by omega
          omega
      refine ⟨hnew, hclock', hR', hC', ?_⟩
      -- the `S` bound
      rintro ⟨j, k, hk, h3, hjk, hju, hku⟩
      rcases Nat.lt_or_ge k (t + 1) with h | h
      · exact p3 (hS ⟨j, k, by omega, h3, hjk, hju, hku⟩)
      · have hkt : k = t + 1 := by omega
        rw [hkt] at hku
        have hCk := hC' j (by omega) h3 hju
        have hjk' : ((j : ℕ) : ℤ) + 5 ≤ ((t + 1 : ℕ) : ℤ) := by
          exact_mod_cast show j + 5 ≤ t + 1 by omega
        omega

set_option maxHeartbeats 1000000 in
/-- **The three-leg fold, asked for one level lower, in its sharpest form.** A 1-Lipschitz arm in
`[L, L + 9]` based at `L + 4` whose two clauses hold *in the form the proof consumes* folds onto
`leg3Walk L (L + 9) (L + 6) (L + 4)`, the walk `L+3 → L+6 → L+1 → L+8`.

This is `foldsOnto_leg3_deep` with each demand for a time at the peak level `L + 6` lowered to
`L + 5` and paid for by an index clause. What makes it the right next step is the level: the
general crookedness clause returns links meeting `L + 6`, that is times of `ρ` at `L + 5` or
above, which is exactly what these clauses ask.

The commissioned clauses carry two index bounds the proof never spends — `j + 5 ≤ d` at the
valley and `k + 6 ≤ d` at the ceiling — because a landmark once reached is kept: the `R` and `S`
bounds propagate from the landmark to the event at no cost. What is spent is `3 ≤ j`, which is
the clock reaching the peak position, and `j + 5 ≤ k`, which is the slack clock crossing from the
peak position to the valley position. -/
theorem foldsOnto_leg3deep_profile_min {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hvalley : Leg3ValleyMin f L) (hceil : Leg3CeilMin f L) :
    FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) := by
  classical
  set u : ℕ → ℤ := fun k => if h : k < m then f ⟨k, h⟩ else L + 4 with hudef
  have hu : ∀ j : Fin m, u j.val = f j := by
    intro j
    simp only [hudef, j.isLt, dif_pos]
  have hu' : ∀ j, ∀ h : j < m, u j = f ⟨j, h⟩ := by
    intro j h
    simpa using hu ⟨j, h⟩
  refine foldsOnto_leg3_of_val3 f L (L + 9) (L + 6) (L + 4) u (by omega) (by omega) (by omega)
    hu ?_
  have key := gseq3_inv_profile L u (m - 1) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (key j.val (by have := j.isLt; omega)).1
  -- `u 0 = L + 4`
  · rw [hu' 0 hm, h0]
  -- the band
  · intro j hj
    have hjm : j < m := by omega
    rw [hu' j hjm]
    exact hL _
  · intro j hj
    have hjm : j < m := by omega
    rw [hu' j hjm]
    exact hH _
  -- Lipschitz
  · intro j hj
    have hjm : j < m := by omega
    have hj1m : j + 1 < m := by omega
    have := hf ⟨j, hjm⟩ ⟨j + 1, hj1m⟩ rfl
    rw [abs_le] at this
    rw [hu' j hjm, hu' (j + 1) hj1m]
    omega
  -- the valley clause
  · intro d hd hdu
    have hdm : d < m := by omega
    rw [hu' d hdm] at hdu
    obtain ⟨j, h3, hj5, hju⟩ := hvalley ⟨d, hdm⟩ hdu
    exact ⟨j.val, h3, hj5, by rw [hu' j.val j.isLt]; exact hju⟩
  -- the ceiling clause
  · intro d hd hdu
    have hdm : d < m := by omega
    rw [hu' d hdm] at hdu
    obtain ⟨j, k, h3, hjk, hkd, hju, hku⟩ := hceil ⟨d, hdm⟩ hdu
    exact ⟨j.val, k.val, h3, hjk, hkd, by rw [hu' j.val j.isLt]; exact hju,
      by rw [hu' k.val k.isLt]; exact hku⟩

/-- **The three-leg fold, asked for one level lower.** A 1-Lipschitz arm in `[L, L + 9]` based at
`L + 4` whose two profile clauses hold folds onto `leg3Walk L (L + 9) (L + 6) (L + 4)`, the walk
`L+3 → L+6 → L+1 → L+8`. The commissioned form of `foldsOnto_leg3deep_profile_min`. -/
theorem foldsOnto_leg3deep_profile {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hvalley : Leg3Valley f L) (hceil : Leg3Ceil f L) :
    FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) :=
  foldsOnto_leg3deep_profile_min hm f hf L h0 hL hH (leg3ValleyMin_of_leg3Valley hvalley)
    (leg3CeilMin_of_leg3Ceil hceil)

/-! ## Which arms can fail a profile clause

Neither clause can fail on an arm that the two canonical walks miss. This is the profile form of
`valley_or_vee` and `ceiling_or_lam` (`HPC/Fold/Mixed.lean`), and it is sharper: what the two
lemmas below rule out is a *failure*, not an unannounced event, so an arm failing `Leg3Valley`
is served by the V-walk and an arm failing `Leg3Ceil` by the Λ-walk, with no hypothesis on the
other arm. Both are statements about arms alone; crookedness enters only as the timing law
(`crookUp_climb4`, `crookDown_fall3`, `crookDown_fall4`, `crookUp_climb5`) and as one application
of the clause `CrookUp` at the ceiling. -/

/-- **An arm that fails the valley clause is served by the V-walk.** If the arm stands at `L + 1`
or below at a step `d` at which `Leg3Valley` fails — so that it has not stood at `L + 5` or above
at any step in `[3, d - 5]` — then it folds onto the V-walk based at `L + 5`.

That step `d` is itself the witness the V-profile asks for: the V-criterion wants, before each
ascent to `L + 7`, a time at `L + 2` or below at an index at least four, and `crookDown_fall3`
puts `d` at index four or later. An ascent to `L + 7` *before* `d` is impossible: it would be six
levels above `d` in fewer steps than the clause allows, and its own index would fall inside the
window `[3, d - 5]` where the failure forbids `L + 5`. -/
theorem leg3Valley_or_vee {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcrd : CrookDown f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    Leg3Valley f L ∨ FoldsOnto f (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
  by_cases hex : ∃ d : Fin m, f d ≤ L + 1 ∧
      ∀ j : Fin m, 3 ≤ j.val → j.val + 5 ≤ d.val → f j ≤ L + 4
  · obtain ⟨d, hd, hno⟩ := hex
    refine Or.inr ((foldsOnto_vee_iff_profile hm f hf (L + 5) (L + 9) L (by omega)
      (by rw [h0, abs_le]; omega) hL hH).mpr ?_)
    rw [critVeeProfile_iff_of_isLip hf (L + 5) L (by omega)]
    intro e he
    have hd0 : 0 < d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd (congrArg f (Fin.ext h : d = ⟨0, hm⟩)) (by omega)
      · exact h
    have hfall := crookDown_fall3 hf hcrd ⟨0, hm⟩ d (by simpa using hd0) (by omega)
    simp only at hfall
    refine ⟨d, ?_, by omega, by omega⟩
    -- an ascent to `L + 7` cannot precede the failing descent
    rcases lt_trichotomy d.val e.val with h | h | h
    · exact h
    · exact absurd (congrArg f (Fin.ext h : d = e)) (by omega)
    · exfalso
      have he0 : 3 ≤ e.val := by
        have := abs_sub_le_of_isLip hf e.val ⟨0, hm⟩ e (by simp)
        rw [abs_le] at this
        omega
      have hgap : e.val + 6 ≤ d.val := by
        have := abs_sub_le_of_isLip hf (d.val - e.val) e d (by omega)
        rw [abs_le] at this
        have hc : ((d.val - e.val : ℕ) : ℤ) = (d.val : ℤ) - (e.val : ℤ) := by
          push_cast [Nat.cast_sub (le_of_lt h)]; ring
        omega
      exact absurd (hno e he0 (by omega)) (by omega)
  · push_neg at hex
    refine Or.inl (fun d hd => ?_)
    obtain ⟨j, hj3, hj5, hjf⟩ := hex d hd
    exact ⟨j, hj3, hj5, by omega⟩

/-- **An arm that fails the ceiling clause is served by the Λ-walk.** If the arm stands at `L + 8`
or above at a step `D` at which `Leg3Ceil` fails, then it folds onto the Λ-walk based at `L + 3`.

The step `D` is the peak witness the Λ-profile asks for, and `crookUp_climb4` puts it at index
seven or later; what has to be ruled out is a descent to `L + 1` *before* `D`. One application of
`CrookUp` between such a descent and `D` produces a time at `L + 6` or above followed by one at
`L + 2` or below, and the three timing laws place the two of them exactly where `Leg3Ceil` asks:
four steps after the descent, seven steps apart, and twelve steps before `D`. -/
theorem leg3Ceil_or_lam {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcru : CrookUp f)
    (hcrd : CrookDown f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j)
    (hH : ∀ j, f j ≤ L + 9) :
    Leg3Ceil f L ∨ FoldsOnto f (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
  by_cases hex : ∃ D : Fin m, L + 8 ≤ f D ∧
      ∀ j k : Fin m, 3 ≤ j.val → j.val + 5 ≤ k.val → k.val + 6 ≤ D.val → L + 5 ≤ f j →
        L + 2 < f k
  · obtain ⟨D, hD, hno⟩ := hex
    refine Or.inr (foldsOnto_lam_of_profile hm f hf (L + 3) (L + 9) L (by omega)
      (by rw [h0, abs_le]; omega) hL hH ?_)
    have hk : κ (L + 3) (L + 9) = L + 8 := by simp only [κ]; omega
    rw [critLamProfile_iff_of_isLip hf, hk]
    intro d hd
    have hD0 : 0 < D.val := by
      rcases Nat.eq_zero_or_pos D.val with h | h
      · exact absurd (congrArg f (Fin.ext h : D = ⟨0, hm⟩)) (by omega)
      · exact h
    have hclimb := crookUp_climb4 hf hcru ⟨0, hm⟩ D (by simpa using hD0) (by omega)
    simp only at hclimb
    refine ⟨D, ?_, by omega, by omega⟩
    -- a descent to `L + 1` cannot precede the failing ascent
    rcases lt_trichotomy D.val d.val with h | h | h
    · exact h
    · exact absurd (congrArg f (Fin.ext h : D = d)) (by omega)
    · exfalso
      have hd0 : 0 < d.val := by
        rcases Nat.eq_zero_or_pos d.val with h' | h'
        · exact absurd (congrArg f (Fin.ext h' : d = ⟨0, hm⟩)) (by omega)
        · exact h'
      have hfall := crookDown_fall3 hf hcrd ⟨0, hm⟩ d (by simpa using hd0) (by omega)
      simp only at hfall
      obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
        hcru.levels (L + 1) (L + 8) (by omega) d D h (by omega) hD
      have hu' : u.val + 7 ≤ u'.val := crookDown_fall4 hf hcrd u u' h2 (by omega)
      have hD' : u'.val + 12 ≤ D.val := crookUp_climb5 hf hcru u' D h3 (by omega)
      exact absurd (hno u u' (by omega) (by omega) (by omega) (by omega)) (by omega)
  · push_neg at hex
    refine Or.inl (fun d hd => ?_)
    obtain ⟨j, k, hj3, hjk, hkd, hjf, hkf⟩ := hex d hd
    exact ⟨j, k, hj3, hjk, hkd, hjf, by omega⟩

end HPC.Fold
