import HPC.Fold.Span6

/-!
# The two leaf walks of span seven

At span seven the two halves of the span-six method leave exactly one case at each interior
basepoint (`s3_span_seven_of_cases` in `HPC/Fold/Span7.lean`): both arms `HighAt (ρ i - 3) H`
and both arms `LowAt L (ρ i + 3)`.  At span seven the interior basepoints are `L + 3` and
`L + 4`, and this file serves each of them with a thirteen-time walk:

* `walk7 L`, for the basepoint `L + 3`: up from `L + 2` to `L + 5`, down to `L + 1`, up to
  `L + 6`;
* `walk7' L`, for the basepoint `L + 4`: its reflection, down from `L + 5` to `L + 2`, up to
  `L + 6`, down to `L + 1`.

The fold is built by a **greedy** time assignment: at each step the arm is carried as far along
the walk as the new level allows (`gstep7`, `gseq`).  `gseq_inv` is the invariant that keeps the
greedy assignment legal; it consists of the window condition `Val7` together with four progress
clauses, each switched on by a feature of the arm's past.  Both leaf folds are instances.

The basepoint `L + 4` needs no crookedness: `HighAt (L + 1) H` and `LowAt L H` alone place every
1-Lipschitz arm on `walk7' L`.  The basepoint `L + 3` needs one crookedness clause, isolated here
as `Zig`: between a time at `L + 1` or below and a later time at `H`, the arm has been at `H - 2`
or above and, after that, at `L + 2` or below.  Without it the arm `L+3, L+2, L+1, L+2, …, L+7`
defeats the walk.
-/

namespace HPC.Fold

/-! ## The conditions, at arbitrary levels -/

/-- **`LowAt f tl th`**: before the arm ever falls to `tl` it has reached `th`, or it has been at
`tl + 1` and after that at `th - 2`. For `tl = L` and `th = H` this is `LowLate` with its first
clause strengthened from `H - 1` to `H`. -/
def LowAt {m : ℕ} (f : Fin m → ℤ) (tl th : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ tl →
    (∃ j : Fin m, j.val < d.val ∧ th ≤ f j) ∨
    (∃ j j' : Fin m, j.val < j'.val ∧ j'.val < d.val ∧ f j ≤ tl + 1 ∧ th - 2 ≤ f j')

/-- **`HighAt f tl th`**: before the arm ever rises to `th` it has been at `tl + 1`. This is the
one-clause form; the dichotomy never needs the second clause of the reflected `HighLate`. -/
def HighAt {m : ℕ} (f : Fin m → ℤ) (tl th : ℤ) : Prop :=
  ∀ d : Fin m, th ≤ f d → ∃ j : Fin m, j.val < d.val ∧ f j ≤ tl + 1

/-! ## The two walks -/

/-- **The span-seven walk at the basepoint `L + 3`**: `L+2, L+3, L+4, L+5, L+4, L+3, L+2, L+1,
L+2, L+3, L+4, L+5, L+6`. -/
def walk7 (L : ℤ) (u : ℕ) : ℤ :=
  if u ≤ 3 then L + 2 + (u : ℤ) else if u ≤ 7 then L + 8 - (u : ℤ) else L + (u : ℤ) - 6

/-- **The span-seven walk at the basepoint `L + 4`**, the reflection of `walk7`: `L+5, L+4, L+3,
L+2, L+3, L+4, L+5, L+6, L+5, L+4, L+3, L+2, L+1`. -/
def walk7' (L : ℤ) (u : ℕ) : ℤ := 2 * L + 7 - walk7 L u

/-! ## The isolated crookedness clause -/

/-- **`Zig f L H`**: between a time at `L + 1` or below and a later time at `H` or above, the arm
has been at `H - 2` or above and, after that, at `L + 2` or below.  This is one instance of the
crookedness clause, read on an arm. -/
def Zig {m : ℕ} (f : Fin m → ℤ) (L H : ℤ) : Prop :=
  ∀ s t : Fin m, s.val < t.val → f s ≤ L + 1 → H ≤ f t →
    ∃ u u' : Fin m, s.val < u.val ∧ u.val < u'.val ∧ u'.val < t.val ∧
      H - 2 ≤ f u ∧ f u' ≤ L + 2

/-! ## The window condition and the greedy step -/

/-- **`Val7 v u`**: the walk time `u` serves the level `L + v`, i.e. `|v - (walk7 L u - L)| ≤ 1`,
written out on the three monotone pieces of the walk. -/
def Val7 (v u : ℤ) : Prop :=
  (0 ≤ u ∧ u ≤ 3 ∧ v - 3 ≤ u ∧ u ≤ v - 1) ∨
  (3 ≤ u ∧ u ≤ 7 ∧ 7 - v ≤ u ∧ u ≤ 9 - v) ∨
  (7 ≤ u ∧ u ≤ 12 ∧ v + 5 ≤ u ∧ u ≤ v + 7)

instance (v u : ℤ) : Decidable (Val7 v u) := by unfold Val7; infer_instance

theorem val7_bounds {v u : ℤ} (h : Val7 v u) : 0 ≤ u ∧ u ≤ 12 := by
  unfold Val7 at h; omega

/-- A legal time is inside the window of its level. -/
theorem val7_walk7 {L v u : ℤ} (h : Val7 (v - L) u) : |v - walk7 L u.toNat| ≤ 1 := by
  obtain ⟨h0, h12⟩ := val7_bounds h
  have hcast : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg h0
  unfold Val7 at h
  unfold walk7
  rcases le_or_gt (u.toNat) 3 with hc | hc
  · rw [if_pos hc, abs_le]; omega
  · rw [if_neg (Nat.not_le.2 hc)]
    rcases le_or_gt (u.toNat) 7 with hc2 | hc2
    · rw [if_pos hc2, abs_le]
      have : (4 : ℤ) ≤ u := by omega
      omega
    · rw [if_neg (Nat.not_le.2 hc2), abs_le]
      have : (8 : ℤ) ≤ u := by omega
      omega

/-- **One greedy step**: advance along the walk if the new level allows it, else stay, else
retreat. -/
def gstep7 (v q : ℤ) : ℤ := if Val7 v (q + 1) then q + 1 else if Val7 v q then q else q - 1

theorem gstep7_up {v q : ℤ} (h : Val7 v (q + 1)) : gstep7 v q = q + 1 := by
  unfold gstep7; rw [if_pos h]

theorem gstep7_mid {v q : ℤ} (h1 : ¬ Val7 v (q + 1)) (h2 : Val7 v q) : gstep7 v q = q := by
  unfold gstep7; rw [if_neg h1, if_pos h2]

theorem gstep7_down {v q : ℤ} (h1 : ¬ Val7 v (q + 1)) (h2 : ¬ Val7 v q) :
    gstep7 v q = q - 1 := by
  unfold gstep7; rw [if_neg h1, if_neg h2]

theorem gstep7_dist (v q : ℤ) : q - 1 ≤ gstep7 v q ∧ gstep7 v q ≤ q + 1 := by
  unfold gstep7; split_ifs <;> omega

/-- The three cases of a greedy step, uniformly. -/
theorem gstep7_elim {v q : ℤ} {P : ℤ → Prop}
    (hup : Val7 v (q + 1) → P (q + 1))
    (hmid : ¬ Val7 v (q + 1) → Val7 v q → P q)
    (hdown : ¬ Val7 v (q + 1) → ¬ Val7 v q → P (q - 1)) : P (gstep7 v q) := by
  by_cases h1 : Val7 v (q + 1)
  · rw [gstep7_up h1]; exact hup h1
  · by_cases h2 : Val7 v q
    · rw [gstep7_mid h1 h2]; exact hmid h1 h2
    · rw [gstep7_down h1 h2]; exact hdown h1 h2

set_option maxHeartbeats 1000000 in
/-- **The greedy step stays legal.**  The two exclusions are exactly what the arm conditions
supply: a step down to the bottom needs the walk time `7` to be within reach, and a step up to
the top needs the far end. -/
theorem val7_gstep {v q v' : ℤ} (hv0 : 0 ≤ v) (hv7 : v ≤ 7) (hv'0 : 0 ≤ v') (hv'7 : v' ≤ 7)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val7 v q)
    (h0 : v' = 0 → 7 - v ≤ q) (h7 : v' = 7 → v + 5 ≤ q) :
    Val7 v' (gstep7 v' q) := by
  refine gstep7_elim (P := fun g => Val7 v' g) (fun h => h) (fun _ h => h) ?_
  intro h1 h2
  unfold Val7 at hval h1 h2 ⊢
  push_neg at h1 h2
  omega

/-- Everything a greedy step guarantees, packaged so that `omega` can use it. -/
theorem gstep7_facts {v' q : ℤ} (A : ℤ → Prop) (hnew : Val7 v' (gstep7 v' q))
    (hA : ∀ g : ℤ, Val7 v' g → (g = q + 1 ∨ g = q ∨ g = q - 1) →
      (Val7 v' (q + 1) → g = q + 1) → (¬ Val7 v' (q + 1) → Val7 v' q → g = q) → A g) :
    A (gstep7 v' q) := by
  revert hnew
  refine gstep7_elim (P := fun g => Val7 v' g → A g) ?_ ?_ ?_
  · intro h1 hn; exact hA _ hn (Or.inl rfl) (fun _ => rfl) (fun h => absurd h1 h)
  · intro h1 h2 hn; exact hA _ hn (Or.inr (Or.inl rfl)) (fun h => absurd h h1) (fun _ _ => rfl)
  · intro h1 h2 hn
    exact hA _ hn (Or.inr (Or.inr rfl)) (fun h => absurd h h1) (fun _ h => absurd h h2)

set_option maxHeartbeats 2000000 in
/-- **The progress clauses.**  Each records that one lower bound on the greedy time survives a
step, either because it already held or because the new level triggers it. -/
theorem prog7 {v q v' : ℤ} (hv0 : 0 ≤ v) (hv7 : v ≤ 7) (hv'0 : 0 ≤ v') (hv'7 : v' ≤ 7)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hnew : Val7 v' (gstep7 v' q)) :
    (min (v - 1) 3 ≤ q → min (v' - 1) 3 ≤ gstep7 v' q) ∧
    (v' ≤ 1 → min (v' - 1) 3 ≤ gstep7 v' q) ∧
    (min (9 - v) 7 ≤ q → min (9 - v') 7 ≤ gstep7 v' q) ∧
    (min (v - 1) 3 ≤ q → 5 ≤ v' → min (9 - v') 7 ≤ gstep7 v' q) ∧
    (6 ≤ v' → min (9 - v') 7 ≤ gstep7 v' q) ∧
    (7 - v ≤ q → 7 - v' ≤ gstep7 v' q) ∧
    (5 ≤ v' → 7 - v' ≤ gstep7 v' q) ∧
    (min (v - 1) 3 ≤ q → 4 ≤ v' → 7 - v' ≤ gstep7 v' q) ∧
    (v + 5 ≤ q → v' + 5 ≤ gstep7 v' q) ∧
    (min (9 - v) 7 ≤ q → v' ≤ 2 → v' + 5 ≤ gstep7 v' q) ∧
    (v' ≤ 0 → v' + 5 ≤ gstep7 v' q) := by
  refine gstep7_facts
    (fun g => (min (v - 1) 3 ≤ q → min (v' - 1) 3 ≤ g) ∧ (v' ≤ 1 → min (v' - 1) 3 ≤ g) ∧
      (min (9 - v) 7 ≤ q → min (9 - v') 7 ≤ g) ∧
      (min (v - 1) 3 ≤ q → 5 ≤ v' → min (9 - v') 7 ≤ g) ∧
      (6 ≤ v' → min (9 - v') 7 ≤ g) ∧ (7 - v ≤ q → 7 - v' ≤ g) ∧ (5 ≤ v' → 7 - v' ≤ g) ∧
      (min (v - 1) 3 ≤ q → 4 ≤ v' → 7 - v' ≤ g) ∧ (v + 5 ≤ q → v' + 5 ≤ g) ∧
      (min (9 - v) 7 ≤ q → v' ≤ 2 → v' + 5 ≤ g) ∧ (v' ≤ 0 → v' + 5 ≤ g)) hnew ?_
  intro g hgv hcase hmax hstay
  unfold Val7 at hgv hmax hstay
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> omega

/-! ## The greedy time sequence -/

/-- The greedy walk time of a sequence of levels, measured from `L`. -/
def gseq (u : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | (j + 1) => gstep7 (u (j + 1)) (gseq u j)

theorem gseq_zero (u : ℕ → ℤ) : gseq u 0 = 0 := rfl

theorem gseq_succ (u : ℕ → ℤ) (j : ℕ) : gseq u (j + 1) = gstep7 (u (j + 1)) (gseq u j) := rfl

/-- **The invariant.**  A level sequence based at `3` inside `[0, 7]` whose descents to `0` and
ascents to `7` are announced by the four features keeps the greedy time legal. -/
theorem gseq_inv (u : ℕ → ℤ) (N : ℕ) (E E2 R S : ℕ → Prop)
    (hu0 : u 0 = 3)
    (hlo : ∀ j, j ≤ N → 0 ≤ u j) (hhi : ∀ j, j ≤ N → u j ≤ 7)
    (hlip : ∀ j, j + 1 ≤ N → u j - 1 ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1)
    (hE0 : ¬ E 0) (hE20 : ¬ E2 0) (hR0 : ¬ R 0) (hS0 : ¬ S 0)
    (hEs : ∀ j, j + 1 ≤ N → E (j + 1) → E j ∨ u (j + 1) ≤ 1)
    (hE2s : ∀ j, j + 1 ≤ N → E2 (j + 1) → E2 j ∨ (E j ∧ 5 ≤ u (j + 1)) ∨ 6 ≤ u (j + 1))
    (hRs : ∀ j, j + 1 ≤ N → R (j + 1) → R j ∨ 5 ≤ u (j + 1) ∨ (E j ∧ 4 ≤ u (j + 1)))
    (hSs : ∀ j, j + 1 ≤ N → S (j + 1) → S j ∨ (E2 j ∧ u (j + 1) ≤ 2) ∨ u (j + 1) ≤ 0)
    (hzero : ∀ j, j + 1 ≤ N → u (j + 1) ≤ 0 → R j)
    (hseven : ∀ j, j + 1 ≤ N → 7 ≤ u (j + 1) → S j) :
    ∀ j, j ≤ N → Val7 (u j) (gseq u j) ∧ (E j → min (u j - 1) 3 ≤ gseq u j) ∧
      (E2 j → min (9 - u j) 7 ≤ gseq u j) ∧ (R j → 7 - u j ≤ gseq u j) ∧
      (S j → u j + 5 ≤ gseq u j) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨?_, fun h => absurd h hE0, fun h => absurd h hE20, fun h => absurd h hR0,
        fun h => absurd h hS0⟩
      rw [gseq_zero, hu0]
      unfold Val7
      omega
  | succ j ih =>
      intro hj
      obtain ⟨hval, hE, hE2, hR, hS⟩ := ih (by omega)
      have hv0 := hlo j (by omega)
      have hv7 := hhi j (by omega)
      have hv'0 := hlo (j + 1) hj
      have hv'7 := hhi (j + 1) hj
      obtain ⟨hl1, hl2⟩ := hlip j hj
      have hnew : Val7 (u (j + 1)) (gseq u (j + 1)) := by
        rw [gseq_succ]
        refine val7_gstep hv0 hv7 hv'0 hv'7 hl1 hl2 hval ?_ ?_
        · intro h; exact hR (hzero j hj (by omega))
        · intro h; exact hS (hseven j hj (by omega))
      obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
        prog7 hv0 hv7 hv'0 hv'7 hl1 hl2 (by rw [← gseq_succ]; exact hnew)
      rw [gseq_succ] at hnew ⊢
      refine ⟨hnew, ?_, ?_, ?_, ?_⟩
      · intro h
        rcases hEs j hj h with h' | h'
        · exact p1 (hE h')
        · exact p2 h'
      · intro h
        rcases hE2s j hj h with h' | h' | h'
        · exact p3 (hE2 h')
        · exact p4 (hE h'.1) h'.2
        · exact p5 h'
      · intro h
        rcases hRs j hj h with h' | h' | h'
        · exact p6 (hR h')
        · exact p7 h'
        · exact p8 (hE h'.1) h'.2
      · intro h
        rcases hSs j hj h with h' | h' | h'
        · exact p9 (hS h')
        · exact p10 (hE2 h'.1) h'.2
        · exact p11 h'

/-! ## From legal times to a fold -/

/-- A legal greedy time sequence is a fold onto `walk7 L`. -/
theorem foldsOnto_walk7_of_val7 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) (u : ℕ → ℤ)
    (hu : ∀ j : Fin m, u j.val = f j - L)
    (hval : ∀ j : Fin m, Val7 (u j.val) (gseq u j.val)) :
    FoldsOnto f 13 (walk7 L) := by
  refine ⟨fun j => (gseq u j.val).toNat, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro j
    obtain ⟨h1, h2⟩ := val7_bounds (hval j)
    omega
  · intro j j' hjj'
    obtain ⟨h1, h2⟩ := val7_bounds (hval j)
    obtain ⟨h3, h4⟩ := val7_bounds (hval j')
    have hstep : gseq u j'.val = gstep7 (u j'.val) (gseq u j.val) := by
      rw [show j'.val = j.val + 1 from hjj', gseq_succ]
    obtain ⟨h5, h6⟩ := gstep7_dist (u j'.val) (gseq u j.val)
    rw [abs_le]
    omega
  · intro j hj
    have h : gseq u j.val = 0 := by rw [hj, gseq_zero]
    rw [h]
    rfl
  · intro j
    have h := hval j
    rw [hu j] at h
    exact val7_walk7 h

/-! ## The leaf fold at the basepoint `L + 3` -/

/-- **The leaf fold at the basepoint `L + 3`.**  `HighAt L H` and `Zig` announce every ascent to
`H`, and `LowAt L (H - 1)` announces every descent to `L`. -/
theorem foldsOnto_walk7_of_leaf {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 3) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 7)
    (hhigh : HighAt f L (L + 7)) (hlow : LowAt f L (L + 6)) (hzig : Zig f L (L + 7)) :
    FoldsOnto f 13 (walk7 L) := by
  classical
  set u : ℕ → ℤ := fun k => if h : k < m then f ⟨k, h⟩ - L else 0 with hudef
  have hu : ∀ j : Fin m, u j.val = f j - L := by
    intro j
    simp only [hudef, j.isLt, dif_pos]
  refine foldsOnto_walk7_of_val7 f L u hu ?_
  set E : ℕ → Prop := fun j => ∃ k : Fin m, k.val ≤ j ∧ f k ≤ L + 1 with hEdef
  set E2 : ℕ → Prop := fun j => ∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ L + 1 ∧
    L + 5 ≤ f k' with hE2def
  set R : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ L + 5 ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ L + 1 ∧ L + 4 ≤ f k') with hRdef
  set S : ℕ → Prop := fun j => ∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧
    k''.val ≤ j ∧ f k ≤ L + 1 ∧ L + 5 ≤ f k' ∧ f k'' ≤ L + 2 with hSdef
  have key := gseq_inv u (m - 1) E E2 R S ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (key j.val (by have := j.isLt; omega)).1
  -- `u 0 = 3`
  · have e : u 0 = f ⟨0, hm⟩ - L := by simpa using hu ⟨0, hm⟩
    rw [e, h0]; ring
  -- lower bound
  · intro j hj
    have hjm : j < m := by omega
    have e : u j = f ⟨j, hjm⟩ - L := by simpa using hu ⟨j, hjm⟩
    have := hL ⟨j, hjm⟩
    omega
  -- upper bound
  · intro j hj
    have hjm : j < m := by omega
    have e : u j = f ⟨j, hjm⟩ - L := by simpa using hu ⟨j, hjm⟩
    have := hH ⟨j, hjm⟩
    omega
  -- Lipschitz
  · intro j hj
    have hjm : j < m := by omega
    have hj1m : j + 1 < m := by omega
    have e1 : u j = f ⟨j, hjm⟩ - L := by simpa using hu ⟨j, hjm⟩
    have e2 : u (j + 1) = f ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
    have := hf ⟨j, hjm⟩ ⟨j + 1, hj1m⟩ rfl
    rw [abs_le] at this
    omega
  -- the four features are absent at time zero
  · rintro ⟨k, hk, hkf⟩
    have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
    rw [this, h0] at hkf; omega
  · rintro ⟨k, k', hkk', hk', -, -⟩
    omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
  · rintro ⟨k, k', k'', hkk', hk'k'', hk'', -, -, -⟩
    omega
  -- the feature updates
  · rintro j hj ⟨k, hk, hkf⟩
    rcases Nat.lt_or_ge k.val (j + 1) with h | h
    · exact Or.inl ⟨k, by omega, hkf⟩
    · right
      have hj1m : j + 1 < m := by omega
      have e : u (j + 1) = f ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
      have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
      rw [hk1] at hkf
      omega
  · rintro j hj ⟨k, k', hkk', hk', hkf, hk'f⟩
    rcases Nat.lt_or_ge k'.val (j + 1) with h | h
    · exact Or.inl ⟨k, k', hkk', by omega, hkf, hk'f⟩
    · refine Or.inr (Or.inl ⟨⟨k, by omega, hkf⟩, ?_⟩)
      have hj1m : j + 1 < m := by omega
      have e : u (j + 1) = f ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
      have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
      rw [hk1] at hk'f
      omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; left
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
      · refine Or.inr (Or.inr ⟨⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
  · rintro j hj ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    rcases Nat.lt_or_ge k''.val (j + 1) with h | h
    · exact Or.inl ⟨k, k', k'', hkk', hk'k'', by omega, hkf, hk'f, hk''f⟩
    · refine Or.inr (Or.inl ⟨⟨k, k', hkk', by omega, hkf, hk'f⟩, ?_⟩)
      have hj1m : j + 1 < m := by omega
      have e : u (j + 1) = f ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
      have hk1 : k'' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k''.val = j + 1 by omega)
      rw [hk1] at hk''f
      omega
  -- a descent to the bottom is announced by `LowAt`
  · intro j hj hzero
    have hj1m : j + 1 < m := by omega
    have hval : f ⟨j + 1, hj1m⟩ ≤ L := by
      have e : u (j + 1) = f ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
      omega
    rcases hlow ⟨j + 1, hj1m⟩ hval with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, by omega⟩
    · exact Or.inr ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, by omega⟩
  -- an ascent to the top is announced by `HighAt` and `Zig`
  · intro j hj hseven
    have hj1m : j + 1 < m := by omega
    have hval : L + 7 ≤ f ⟨j + 1, hj1m⟩ := by
      have e : u (j + 1) = f ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
      omega
    obtain ⟨s, hs, hsf⟩ := hhigh ⟨j + 1, hj1m⟩ hval
    obtain ⟨a, b, hsa, hab, hb, haf, hbf⟩ := hzig s ⟨j + 1, hj1m⟩ hs hsf hval
    exact ⟨s, a, b, hsa, hab, by simpa using Nat.lt_succ_iff.mp hb, hsf, by omega, hbf⟩

/-! ## The leaf fold at the basepoint `L + 4` -/

/-- **The leaf fold at the basepoint `L + 4`.**  No crookedness is used: `HighAt (L + 1) H` and
`LowAt L H` place the arm on the reflected walk. -/
theorem foldsOnto_walk7'_of_leaf {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 7)
    (hhigh : HighAt f (L + 1) (L + 7)) (hlow : LowAt f L (L + 7)) :
    FoldsOnto f 13 (walk7' L) := by
  classical
  set g : Fin m → ℤ := fun j => 2 * L + 7 - f j with hgdef
  have hglip : IsLip g := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [hgdef]
    rw [abs_le] at this ⊢
    omega
  have hgfold : FoldsOnto g 13 (walk7 L) := by
    set u : ℕ → ℤ := fun k => if h : k < m then g ⟨k, h⟩ - L else 0 with hudef
    have hu : ∀ j : Fin m, u j.val = g j - L := by
      intro j
      simp only [hudef, j.isLt, dif_pos]
    refine foldsOnto_walk7_of_val7 g L u hu ?_
    set E : ℕ → Prop := fun _ => False with hEdef
    set E2 : ℕ → Prop := fun j => ∃ k : Fin m, k.val ≤ j ∧ f k ≤ L + 1 with hE2def
    set R : ℕ → Prop := fun j => ∃ k : Fin m, k.val ≤ j ∧ f k ≤ L + 2 with hRdef
    set S : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ L + 7 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ L + 1 ∧ L + 5 ≤ f k') with hSdef
    have key := gseq_inv u (m - 1) E E2 R S ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro j
      exact (key j.val (by have := j.isLt; omega)).1
    · have e : u 0 = g ⟨0, hm⟩ - L := by simpa using hu ⟨0, hm⟩
      simp only [hgdef] at e
      rw [e, h0]; ring
    · intro j hj
      have hjm : j < m := by omega
      have e : u j = g ⟨j, hjm⟩ - L := by simpa using hu ⟨j, hjm⟩
      simp only [hgdef] at e
      have := hH ⟨j, hjm⟩
      omega
    · intro j hj
      have hjm : j < m := by omega
      have e : u j = g ⟨j, hjm⟩ - L := by simpa using hu ⟨j, hjm⟩
      simp only [hgdef] at e
      have := hL ⟨j, hjm⟩
      omega
    · intro j hj
      have hjm : j < m := by omega
      have hj1m : j + 1 < m := by omega
      have e1 : u j = g ⟨j, hjm⟩ - L := by simpa using hu ⟨j, hjm⟩
      have e2 : u (j + 1) = g ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
      simp only [hgdef] at e1 e2
      have := hf ⟨j, hjm⟩ ⟨j + 1, hj1m⟩ rfl
      rw [abs_le] at this
      omega
    · exact id
    · rintro ⟨k, hk, hkf⟩
      have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · rintro ⟨k, hk, hkf⟩
      have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
      · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
        rw [this, h0] at hkf; omega
      · omega
    · exact fun j _ h => absurd h id
    · rintro j hj ⟨k, hk, hkf⟩
      rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl ⟨k, by omega, hkf⟩
      · right; right
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = g ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
        simp only [hgdef] at e
        have : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [this] at hkf
        omega
    · rintro j hj ⟨k, hk, hkf⟩
      rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl ⟨k, by omega, hkf⟩
      · right; left
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = g ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
        simp only [hgdef] at e
        have : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [this] at hkf
        omega
    · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
      · rcases Nat.lt_or_ge k.val (j + 1) with h | h
        · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
        · right; right
          have hj1m : j + 1 < m := by omega
          have e : u (j + 1) = g ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
          simp only [hgdef] at e
          have : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
          rw [this] at hkf
          omega
      · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
        · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
        · refine Or.inr (Or.inl ⟨⟨k, by omega, hkf⟩, ?_⟩)
          have hj1m : j + 1 < m := by omega
          have e : u (j + 1) = g ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
          simp only [hgdef] at e
          have : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
          rw [this] at hk'f
          omega
    -- a descent of `g` to the bottom is an ascent of `f` to the top, announced by `HighAt`
    · intro j hj hzero
      have hj1m : j + 1 < m := by omega
      have e : u (j + 1) = g ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
      simp only [hgdef] at e
      have hval : L + 7 ≤ f ⟨j + 1, hj1m⟩ := by omega
      obtain ⟨k, hk, hkf⟩ := hhigh ⟨j + 1, hj1m⟩ hval
      exact ⟨k, by simpa using Nat.lt_succ_iff.mp hk, by omega⟩
    -- an ascent of `g` to the top is a descent of `f` to the bottom, announced by `LowAt`
    · intro j hj hsev
      have hj1m : j + 1 < m := by omega
      have e : u (j + 1) = g ⟨j + 1, hj1m⟩ - L := by simpa using hu ⟨j + 1, hj1m⟩
      simp only [hgdef] at e
      have hval : f ⟨j + 1, hj1m⟩ ≤ L := by omega
      rcases hlow ⟨j + 1, hj1m⟩ hval with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
      · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, hkf⟩
      · exact Or.inr ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, by omega⟩
  obtain ⟨β, h1, h2, h3, h4⟩ := hgfold
  refine ⟨β, h1, h2, h3, ?_⟩
  intro j
  have := h4 j
  simp only [hgdef, walk7'] at this ⊢
  rw [abs_le] at this ⊢
  omega

end HPC.Fold
