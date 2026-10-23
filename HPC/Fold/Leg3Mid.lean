import HPC.Fold.Leg3

/-!
# The three-leg fold at a middle basepoint

`HPC/Fold/Leg3.lean` folds an arm based at `P` onto `leg3Walk L H K P` for `L + 2 ≤ P ≤ L + 3`.
This file is the same engine with the basepoint allowed one level higher, `L + 2 ≤ P ≤ L + 4`,
which is what a basepoint standing exactly four levels above the floor needs.

Nothing about the walk changes: it is still `leg3Walk L H K P`, from `P - 1` up to the peak `K`,
down to `L + 1`, up to `H - 1`, with the greedy time assignment `gseq3` of `HPC/Fold/Leg3.lean`.
What changes is the *height at which the announcements are read*.  In the original engine the
features are phrased at `L`, `L + 1`, `L + 2`; here they are phrased at `P - 3`, `P - 2`, `P - 1`,
which is the same thing when `P = L + 3` and is one level higher when `P = L + 4`.  The reason is
that the walk starts at `P - 1`, so the first window covers the levels `P - 2`, `P - 1`, `P`: a
descent below `P - 2` is what the walk cannot serve at the start, and it is exactly that descent
which has to be announced.

* **floor.** Every descent to `P - 3` or below is preceded by a time at `K` or above, or by a time
  at `P - 2` or below followed by one at `K - 1` or above.
* **ceiling.** Every ascent to `K + 2` or above is preceded by a time at `P - 3` or below, or by
  two times, in order, at `K + 1` or above and at `P - 1` or below, or by three times, in order,
  at `P - 2` or below, at `K` or above, and at `P - 1` or below.

`foldsOnto_leg3M` is the resulting fold; for `P ≤ L + 3` it is `foldsOnto_leg3` verbatim.
-/

namespace HPC.Fold

set_option maxHeartbeats 1000000 in
/-- **The greedy step stays legal.**  The two exclusions are exactly what the arm's conditions
supply: a step to the floor needs the valley of the walk to be within reach, and a step to
`K + 2` or above needs the far leg. -/
theorem val3_gstepM {L H K P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val3 L H K P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q) (hK : K + 2 ≤ v' → v - 2 * L - P + 2 * K - 2 ≤ q) :
    Val3 L H K P v' (gstep3 L H K P v' q) := by
  refine gstep3_elim (Q := fun g => Val3 L H K P v' g) (fun h => h) (fun _ h => h) ?_
  intro h1 h2
  unfold Val3 at hval h1 h2 ⊢
  push_neg at h1 h2
  omega

/-- Everything a greedy step guarantees, packaged so that `omega` can use it. -/
theorem gstep3_factsM {L H K P v' q : ℤ} (A : ℤ → Prop)
    (hnew : Val3 L H K P v' (gstep3 L H K P v' q))
    (hA : ∀ g : ℤ, Val3 L H K P v' g → (g = q + 1 ∨ g = q ∨ g = q - 1) →
      (Val3 L H K P v' (q + 1) → g = q + 1) →
      (¬ Val3 L H K P v' (q + 1) → Val3 L H K P v' q → g = q) → A g) :
    A (gstep3 L H K P v' q) := by
  revert hnew
  refine gstep3_elim (Q := fun g => Val3 L H K P v' g → A g) ?_ ?_ ?_
  · intro h1 hn; exact hA _ hn (Or.inl rfl) (fun _ => rfl) (fun h => absurd h1 h)
  · intro h1 h2 hn; exact hA _ hn (Or.inr (Or.inl rfl)) (fun h => absurd h h1) (fun _ _ => rfl)
  · intro h1 h2 hn
    exact hA _ hn (Or.inr (Or.inr rfl)) (fun h => absurd h h1) (fun _ h => absurd h h2)


set_option maxHeartbeats 2000000 in
/-- **The progress clauses.**  Each records that one lower bound on the greedy time survives a
step, either because it already held or because the new level triggers it. -/
theorem prog3M {L H K P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q) (hKq : K + 2 ≤ v' → v - 2 * L - P + 2 * K - 2 ≤ q)
    (hold : Val3 L H K P v q) (hnew : Val3 L H K P v' (gstep3 L H K P v' q)) :
    (min (v - P + 2) (K - P + 1) ≤ q → min (v' - P + 2) (K - P + 1) ≤ gstep3 L H K P v' q) ∧
    (v' ≤ P - 2 → min (v' - P + 2) (K - P + 1) ≤ gstep3 L H K P v' q) ∧
    (min (2 * K - P + 2 - v) (2 * K - P - L) ≤ q →
      min (2 * K - P + 2 - v') (2 * K - P - L) ≤ gstep3 L H K P v' q) ∧
    (min (v - P + 2) (K - P + 1) ≤ q → K ≤ v' →
      min (2 * K - P + 2 - v') (2 * K - P - L) ≤ gstep3 L H K P v' q) ∧
    (K + 1 ≤ v' → min (2 * K - P + 2 - v') (2 * K - P - L) ≤ gstep3 L H K P v' q) ∧
    (2 * K - P - v ≤ q → 2 * K - P - v' ≤ gstep3 L H K P v' q) ∧
    (K ≤ v' → 2 * K - P - v' ≤ gstep3 L H K P v' q) ∧
    (min (v - P + 2) (K - P + 1) ≤ q → K - 1 ≤ v' → 2 * K - P - v' ≤ gstep3 L H K P v' q) ∧
    (v - 2 * L - P + 2 * K - 2 ≤ q → v' - 2 * L - P + 2 * K - 2 ≤ gstep3 L H K P v' q) ∧
    (min (2 * K - P + 2 - v) (2 * K - P - L) ≤ q → v' ≤ L + 2 →
      v' - 2 * L - P + 2 * K - 2 ≤ gstep3 L H K P v' q) ∧
    (v' ≤ P - 3 → v' - 2 * L - P + 2 * K - 2 ≤ gstep3 L H K P v' q) := by
  refine gstep3_factsM
    (fun g => (min (v - P + 2) (K - P + 1) ≤ q → min (v' - P + 2) (K - P + 1) ≤ g) ∧
      (v' ≤ P - 2 → min (v' - P + 2) (K - P + 1) ≤ g) ∧
      (min (2 * K - P + 2 - v) (2 * K - P - L) ≤ q →
        min (2 * K - P + 2 - v') (2 * K - P - L) ≤ g) ∧
      (min (v - P + 2) (K - P + 1) ≤ q → K ≤ v' →
        min (2 * K - P + 2 - v') (2 * K - P - L) ≤ g) ∧
      (K + 1 ≤ v' → min (2 * K - P + 2 - v') (2 * K - P - L) ≤ g) ∧
      (2 * K - P - v ≤ q → 2 * K - P - v' ≤ g) ∧
      (K ≤ v' → 2 * K - P - v' ≤ g) ∧
      (min (v - P + 2) (K - P + 1) ≤ q → K - 1 ≤ v' → 2 * K - P - v' ≤ g) ∧
      (v - 2 * L - P + 2 * K - 2 ≤ q → v' - 2 * L - P + 2 * K - 2 ≤ g) ∧
      (min (2 * K - P + 2 - v) (2 * K - P - L) ≤ q → v' ≤ L + 2 →
        v' - 2 * L - P + 2 * K - 2 ≤ g) ∧
      (v' ≤ P - 3 → v' - 2 * L - P + 2 * K - 2 ≤ g)) hnew ?_
  intro g hgv hcase hmax hstay
  unfold Val3 at hgv hmax hstay hold
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega


set_option maxHeartbeats 1000000 in
/-- **The invariant.**  A level sequence based at `P` inside `[L, H]` whose descents to the floor
and ascents to `K + 2` are announced by the features keeps the greedy time legal. -/
theorem gseq3_invM (L H K P : ℤ) (u : ℕ → ℤ) (N : ℕ) (E E2 R S : ℕ → Prop)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
    (hu0 : u 0 = P)
    (hlo : ∀ j, j ≤ N → L ≤ u j) (hhi : ∀ j, j ≤ N → u j ≤ H)
    (hlip : ∀ j, j + 1 ≤ N → u j - 1 ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1)
    (hE0 : ¬ E 0) (hE20 : ¬ E2 0) (hR0 : ¬ R 0) (hS0 : ¬ S 0)
    (hEs : ∀ j, j + 1 ≤ N → E (j + 1) → E j ∨ u (j + 1) ≤ P - 2)
    (hE2s : ∀ j, j + 1 ≤ N → E2 (j + 1) → E2 j ∨ (E j ∧ K ≤ u (j + 1)) ∨ K + 1 ≤ u (j + 1))
    (hRs : ∀ j, j + 1 ≤ N → R (j + 1) → R j ∨ K ≤ u (j + 1) ∨ (E j ∧ K - 1 ≤ u (j + 1)))
    (hSs : ∀ j, j + 1 ≤ N → S (j + 1) → S j ∨ (E2 j ∧ u (j + 1) ≤ L + 2) ∨ u (j + 1) ≤ P - 3)
    (hfloor : ∀ j, j + 1 ≤ N → u (j + 1) ≤ P - 3 → R j)
    (hceil : ∀ j, j + 1 ≤ N → K + 2 ≤ u (j + 1) → S j) :
    ∀ j, j ≤ N → Val3 L H K P (u j) (gseq3 L H K P u j) ∧
      (E j → min (u j - P + 2) (K - P + 1) ≤ gseq3 L H K P u j) ∧
      (E2 j → min (2 * K - P + 2 - u j) (2 * K - P - L) ≤ gseq3 L H K P u j) ∧
      (R j → 2 * K - P - u j ≤ gseq3 L H K P u j) ∧
      (S j → u j - 2 * L - P + 2 * K - 2 ≤ gseq3 L H K P u j) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨?_, fun h => absurd h hE0, fun h => absurd h hE20, fun h => absurd h hR0,
        fun h => absurd h hS0⟩
      rw [gseq3_zero, hu0]
      unfold Val3
      omega
  | succ j ih =>
      intro hj
      obtain ⟨hval, hE, hE2, hR, hS⟩ := ih (by omega)
      have hv0 := hlo j (by omega)
      have hvH := hhi j (by omega)
      have hv'0 := hlo (j + 1) hj
      have hv'H := hhi (j + 1) hj
      obtain ⟨hl1, hl2⟩ := hlip j hj
      have hnew : Val3 L H K P (u (j + 1)) (gseq3 L H K P u (j + 1)) := by
        rw [gseq3_succ]
        refine val3_gstepM hLP hPL hPK hKH hv0 hvH hv'0 hv'H hl1 hl2 hval ?_ ?_
        · intro h; exact hR (hfloor j hj h)
        · intro h; exact hS (hceil j hj h)
      obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
        prog3M hLP hPL hPK hKH hv0 hvH hv'0 hv'H hl1 hl2
          (fun h => hR (hfloor j hj h)) (fun h => hS (hceil j hj h)) hval
          (by rw [← gseq3_succ]; exact hnew)
      rw [gseq3_succ] at hnew ⊢
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


/-! ## The fold, with the announcements as hypotheses -/

/-- **The three-leg fold.**  A 1-Lipschitz arm in `[L, H]` based at `P` folds onto
`leg3Walk L H K P` as soon as

* every descent to the floor `L` is preceded by a time at `K` or above, or by a time at `L + 1`
  or below followed by one at `K - 1` or above, and
* every ascent to `K + 2` or above is preceded by a time at `L`, or by two times, in order, at
  `K + 1` or above and at `L + 2` or below, or by three times, in order, at `L + 1` or below, at
  `K` or above, and at `L + 2` or below.

No crookedness is used: these two announcements are what the dichotomy and the crookedness clause
supply at the point of use. -/
theorem foldsOnto_leg3M {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L H K P : ℤ)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
    (h0 : f ⟨0, hm⟩ = P) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hfloor : ∀ d : Fin m, f d ≤ P - 3 →
      (∃ k : Fin m, k.val < d.val ∧ K ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ P - 2 ∧ K - 1 ≤ f k'))
    (hceil : ∀ d : Fin m, K + 2 ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ P - 3) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ K + 1 ≤ f k ∧ f k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        f k ≤ P - 2 ∧ K ≤ f k' ∧ f k'' ≤ L + 2)) :
    FoldsOnto f (leg3Len L H K P) (leg3Walk L H K P) := by
  classical
  set u : ℕ → ℤ := fun k => if h : k < m then f ⟨k, h⟩ else P with hudef
  have hu : ∀ j : Fin m, u j.val = f j := by
    intro j
    simp only [hudef, j.isLt, dif_pos]
  refine foldsOnto_leg3_of_val3 f L H K P u hLP hPK hKH hu ?_
  set E : ℕ → Prop := fun j => ∃ k : Fin m, k.val ≤ j ∧ f k ≤ P - 2 with hEdef
  set E2 : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ K + 1 ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ P - 2 ∧ K ≤ f k') with hE2def
  set R : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ K ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ P - 2 ∧ K - 1 ≤ f k') with hRdef
  set S : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ f k ≤ P - 3) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ K + 1 ≤ f k ∧ f k' ≤ L + 2) ∨
    (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val ≤ j ∧
      f k ≤ P - 2 ∧ K ≤ f k' ∧ f k'' ≤ L + 2) with hSdef
  have key := gseq3_invM L H K P u (m - 1) E E2 R S hLP hPL hPK hKH ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (key j.val (by have := j.isLt; omega)).1
  -- `u 0 = P`
  · have e : u 0 = f ⟨0, hm⟩ := by simpa using hu ⟨0, hm⟩
    rw [e, h0]
  -- the band
  · intro j hj
    have hjm : j < m := by omega
    have e : u j = f ⟨j, hjm⟩ := by simpa using hu ⟨j, hjm⟩
    have := hL ⟨j, hjm⟩
    omega
  · intro j hj
    have hjm : j < m := by omega
    have e : u j = f ⟨j, hjm⟩ := by simpa using hu ⟨j, hjm⟩
    have := hH ⟨j, hjm⟩
    omega
  -- Lipschitz
  · intro j hj
    have hjm : j < m := by omega
    have hj1m : j + 1 < m := by omega
    have e1 : u j = f ⟨j, hjm⟩ := by simpa using hu ⟨j, hjm⟩
    have e2 : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
    have := hf ⟨j, hjm⟩ ⟨j + 1, hj1m⟩ rfl
    rw [abs_le] at this
    omega
  -- the features are absent at time zero
  · rintro ⟨k, hk, hkf⟩
    have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
    rw [this, h0] at hkf; omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', -, -⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', -, -, -⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf; omega
    · omega
    · omega
  -- the feature updates
  · rintro j hj ⟨k, hk, hkf⟩
    rcases Nat.lt_or_ge k.val (j + 1) with h | h
    · exact Or.inl ⟨k, by omega, hkf⟩
    · right
      have hj1m : j + 1 < m := by omega
      have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
      have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
      rw [hk1] at hkf
      omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; right
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
      · refine Or.inr (Or.inl ⟨⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; left
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
      · refine Or.inr (Or.inr ⟨⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
  · rintro j hj (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩)
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · right; right
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [hk1] at hkf
        omega
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr (Or.inl ⟨k, k', hkk', by omega, hkf, hk'f⟩))
      · refine Or.inr (Or.inl ⟨Or.inl ⟨k, by omega, hkf⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [hk1] at hk'f
        omega
    · rcases Nat.lt_or_ge k''.val (j + 1) with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', by omega, hkf, hk'f, hk''f⟩))
      · refine Or.inr (Or.inl ⟨Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩, ?_⟩)
        have hj1m : j + 1 < m := by omega
        have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
        have hk1 : k'' = (⟨j + 1, hj1m⟩ : Fin m) := Fin.ext (show k''.val = j + 1 by omega)
        rw [hk1] at hk''f
        omega
  -- a descent to the floor is announced
  · intro j hj hzero
    have hj1m : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
    rcases hfloor ⟨j + 1, hj1m⟩ (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, hkf⟩
    · exact Or.inr ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, hk'f⟩
  -- an ascent to `K + 2` is announced
  · intro j hj hceil'
    have hj1m : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hj1m⟩ := by simpa using hu ⟨j + 1, hj1m⟩
    rcases hceil ⟨j + 1, hj1m⟩ (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, hkf⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, hk'f⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', by simpa using Nat.lt_succ_iff.mp hk'',
        hkf, hk'f, hk''f⟩)


end HPC.Fold
