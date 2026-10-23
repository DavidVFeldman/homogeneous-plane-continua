import HPC.Fold.Leg3

/-!
# The three-leg walk from a basepoint three levels above its valley

`HPC/Fold/Leg3.lean` folds an arm onto `leg3Walk L H K P` — from `P - 1` up to the peak `K`, down
to the valley `L + 1`, up to `H - 1` — for a basepoint `P` with `L + 2 ≤ P ≤ L + 3`. The bound
`P ≤ L + 3` is what makes the valley reachable at once: at `P = L + 3` the level `L + 1` is inside
the window of the walk time `0`, so a descent to the valley needs no announcement, and only
descents to the floor `L` do.

At `P = L + 4` that is false — the arm `L+4, L+3, L+2, L+1` folds onto no prefix of the walk — and
one more announcement is needed: *every* descent to `L + 1`, not only to `L`, must be preceded by
a time at the peak. That is the only change. The walk, the window condition `Val3`, the greedy
step `gstep3` and the greedy sequence `gseq3` are the ones of `HPC/Fold/Leg3.lean`; the invariant
carries the same four features

```
E  : the arm has been at L + 1 or below
E2 : E, and after that the arm has been at K or above, or the arm has been at K + 1 or above
R  : the arm has been at K or above, or E and after that at K - 1 or above
S  : E2, and after that the arm has been at L + 2 or below, or the arm has been at L
```

and the same eleven progress clauses, with `R` now demanded one level higher.

The walk this makes available at a band of width nine and a basepoint `L + 4` is
`L+3 → L+6 → L+1 → L+8`, which is the walk the censuses of batches 43 and 44 find serving every
pair of the open span-nine branch that the Λ-walk and the V-walk miss. No walk of any engine in
the repository before this one has its valley at `L + 1` and its basepoint at `L + 4`.
-/

namespace HPC.Fold

set_option maxHeartbeats 1000000 in
/-- **The greedy step stays legal**, at a basepoint up to `L + 4`. The exclusion at the floor is
demanded one level higher than in `val3_gstep`: a step to `L + 1` already needs the valley of the
walk to be within reach. -/
theorem val3_gstep_deep {L H K P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val3 L H K P v q)
    (h0 : v' ≤ L + 1 → 2 * K - P - v ≤ q) (hK : K + 2 ≤ v' → v - 2 * L - P + 2 * K - 2 ≤ q) :
    Val3 L H K P v' (gstep3 L H K P v' q) := by
  refine gstep3_elim (Q := fun g => Val3 L H K P v' g) (fun h => h) (fun _ h => h) ?_
  intro h1 h2
  unfold Val3 at hval h1 h2 ⊢
  push_neg at h1 h2
  omega

set_option maxHeartbeats 2000000 in
/-- **The progress clauses**, at a basepoint up to `L + 4`. -/
theorem prog3_deep {L H K P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K)
    (hKH : K ≤ H - 1) (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1)
    (h0 : v' ≤ L + 1 → 2 * K - P - v ≤ q) (hKq : K + 2 ≤ v' → v - 2 * L - P + 2 * K - 2 ≤ q)
    (hold : Val3 L H K P v q) (hnew : Val3 L H K P v' (gstep3 L H K P v' q)) :
    (min (v - P + 2) (K - P + 1) ≤ q → min (v' - P + 2) (K - P + 1) ≤ gstep3 L H K P v' q) ∧
    (v' ≤ L + 1 → min (v' - P + 2) (K - P + 1) ≤ gstep3 L H K P v' q) ∧
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
    (v' ≤ L → v' - 2 * L - P + 2 * K - 2 ≤ gstep3 L H K P v' q) := by
  refine gstep3_facts
    (fun g => (min (v - P + 2) (K - P + 1) ≤ q → min (v' - P + 2) (K - P + 1) ≤ g) ∧
      (v' ≤ L + 1 → min (v' - P + 2) (K - P + 1) ≤ g) ∧
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
      (v' ≤ L → v' - 2 * L - P + 2 * K - 2 ≤ g)) hnew ?_
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
/-- **The invariant**, at a basepoint up to `L + 4`: descents to the valley `L + 1` and ascents
to `K + 2` are announced by the features. -/
theorem gseq3_inv_deep (L H K P : ℤ) (u : ℕ → ℤ) (N : ℕ) (E E2 R S : ℕ → Prop)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
    (hu0 : u 0 = P)
    (hlo : ∀ j, j ≤ N → L ≤ u j) (hhi : ∀ j, j ≤ N → u j ≤ H)
    (hlip : ∀ j, j + 1 ≤ N → u j - 1 ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1)
    (hE0 : ¬ E 0) (hE20 : ¬ E2 0) (hR0 : ¬ R 0) (hS0 : ¬ S 0)
    (hEs : ∀ j, j + 1 ≤ N → E (j + 1) → E j ∨ u (j + 1) ≤ L + 1)
    (hE2s : ∀ j, j + 1 ≤ N → E2 (j + 1) → E2 j ∨ (E j ∧ K ≤ u (j + 1)) ∨ K + 1 ≤ u (j + 1))
    (hRs : ∀ j, j + 1 ≤ N → R (j + 1) → R j ∨ K ≤ u (j + 1) ∨ (E j ∧ K - 1 ≤ u (j + 1)))
    (hSs : ∀ j, j + 1 ≤ N → S (j + 1) → S j ∨ (E2 j ∧ u (j + 1) ≤ L + 2) ∨ u (j + 1) ≤ L)
    (hvalley : ∀ j, j + 1 ≤ N → u (j + 1) ≤ L + 1 → R j)
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
        refine val3_gstep_deep hLP hPL hPK hKH hv0 hvH hv'0 hv'H hl1 hl2 hval ?_ ?_
        · intro h; exact hR (hvalley j hj h)
        · intro h; exact hS (hceil j hj h)
      obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
        prog3_deep hLP hPL hPK hKH hv0 hvH hv'0 hv'H hl1 hl2
          (fun h => hR (hvalley j hj h)) (fun h => hS (hceil j hj h)) hval
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

set_option maxHeartbeats 1000000 in
/-- **The three-leg fold from a basepoint three levels above the valley.** A 1-Lipschitz arm in
`[L, H]` based at `P ≤ L + 4` folds onto `leg3Walk L H K P` as soon as

* every descent to `L + 1` is preceded by a time at `K` or above, or by a time at `L + 1` or
  below followed by one at `K - 1` or above, and
* every ascent to `K + 2` or above is preceded by a time at `L`, or by two times, in order, at
  `K + 1` or above and at `L + 2` or below, or by three times, in order, at `L + 1` or below, at
  `K` or above, and at `L + 2` or below.

This is `foldsOnto_leg3` with the floor announcement read one level higher, which is what a
basepoint at `L + 4` costs. No crookedness is used. -/
theorem foldsOnto_leg3_deep {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L H K P : ℤ)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
    (h0 : f ⟨0, hm⟩ = P) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hvalley : ∀ d : Fin m, f d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ K ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 1 ∧ K - 1 ≤ f k'))
    (hceil : ∀ d : Fin m, K + 2 ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ L) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ K + 1 ≤ f k ∧ f k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        f k ≤ L + 1 ∧ K ≤ f k' ∧ f k'' ≤ L + 2)) :
    FoldsOnto f (leg3Len L H K P) (leg3Walk L H K P) := by
  classical
  set u : ℕ → ℤ := fun k => if h : k < m then f ⟨k, h⟩ else P with hudef
  have hu : ∀ j : Fin m, u j.val = f j := by
    intro j
    simp only [hudef, j.isLt, dif_pos]
  refine foldsOnto_leg3_of_val3 f L H K P u hLP hPK hKH hu ?_
  set E : ℕ → Prop := fun j => ∃ k : Fin m, k.val ≤ j ∧ f k ≤ L + 1 with hEdef
  set E2 : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ K + 1 ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ L + 1 ∧ K ≤ f k') with hE2def
  set R : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ K ≤ f k) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ f k ≤ L + 1 ∧ K - 1 ≤ f k') with hRdef
  set S : ℕ → Prop := fun j => (∃ k : Fin m, k.val ≤ j ∧ f k ≤ L) ∨
    (∃ k k' : Fin m, k.val < k'.val ∧ k'.val ≤ j ∧ K + 1 ≤ f k ∧ f k' ≤ L + 2) ∨
    (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val ≤ j ∧
      f k ≤ L + 1 ∧ K ≤ f k' ∧ f k'' ≤ L + 2) with hSdef
  have key := gseq3_inv_deep L H K P u (m - 1) E E2 R S hLP hPL hPK hKH ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    rw [this, h0] at hkf
    omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf
      omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf
      omega
    · omega
  · rintro (⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩)
    · have : k = (⟨0, hm⟩ : Fin m) := Fin.ext (show k.val = 0 by omega)
      rw [this, h0] at hkf
      omega
    · omega
    · omega
  -- the features grow only as stated
  · intro j hj hnew
    obtain ⟨k, hk, hkf⟩ := hnew
    rcases Nat.lt_or_ge k.val (j + 1) with h | h
    · exact Or.inl ⟨k, by omega, hkf⟩
    · have hkj : k.val = j + 1 := by omega
      have hjm : j + 1 < m := by omega
      have e : u (j + 1) = f ⟨j + 1, hjm⟩ := by simpa using hu ⟨j + 1, hjm⟩
      have : k = (⟨j + 1, hjm⟩ : Fin m) := Fin.ext hkj
      rw [this] at hkf
      exact Or.inr (by omega)
  · intro j hj hnew
    have hjm : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hjm⟩ := by simpa using hu ⟨j + 1, hjm⟩
    rcases hnew with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · have : k = (⟨j + 1, hjm⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [this] at hkf
        exact Or.inr (Or.inr (by omega))
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
      · have : k' = (⟨j + 1, hjm⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [this] at hk'f
        exact Or.inr (Or.inl ⟨⟨k, by omega, hkf⟩, by omega⟩)
  · intro j hj hnew
    have hjm : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hjm⟩ := by simpa using hu ⟨j + 1, hjm⟩
    rcases hnew with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · have : k = (⟨j + 1, hjm⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [this] at hkf
        exact Or.inr (Or.inl (by omega))
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩)
      · have : k' = (⟨j + 1, hjm⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [this] at hk'f
        exact Or.inr (Or.inr ⟨⟨k, by omega, hkf⟩, by omega⟩)
  · intro j hj hnew
    have hjm : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hjm⟩ := by simpa using hu ⟨j + 1, hjm⟩
    rcases hnew with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · rcases Nat.lt_or_ge k.val (j + 1) with h | h
      · exact Or.inl (Or.inl ⟨k, by omega, hkf⟩)
      · have : k = (⟨j + 1, hjm⟩ : Fin m) := Fin.ext (show k.val = j + 1 by omega)
        rw [this] at hkf
        exact Or.inr (Or.inr (by omega))
    · rcases Nat.lt_or_ge k'.val (j + 1) with h | h
      · exact Or.inl (Or.inr (Or.inl ⟨k, k', hkk', by omega, hkf, hk'f⟩))
      · have : k' = (⟨j + 1, hjm⟩ : Fin m) := Fin.ext (show k'.val = j + 1 by omega)
        rw [this] at hk'f
        exact Or.inr (Or.inl ⟨Or.inl ⟨k, by omega, hkf⟩, by omega⟩)
    · rcases Nat.lt_or_ge k''.val (j + 1) with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', by omega, hkf, hk'f, hk''f⟩))
      · have : k'' = (⟨j + 1, hjm⟩ : Fin m) := Fin.ext (show k''.val = j + 1 by omega)
        rw [this] at hk''f
        exact Or.inr (Or.inl ⟨Or.inr ⟨k, k', hkk', by omega, hkf, hk'f⟩, by omega⟩)
  -- the two announcements
  · intro j hj hd
    have hjm : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hjm⟩ := by simpa using hu ⟨j + 1, hjm⟩
    rcases hvalley ⟨j + 1, hjm⟩ (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, hkf⟩
    · exact Or.inr ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, hk'f⟩
  · intro j hj hd
    have hjm : j + 1 < m := by omega
    have e : u (j + 1) = f ⟨j + 1, hjm⟩ := by simpa using hu ⟨j + 1, hjm⟩
    rcases hceil ⟨j + 1, hjm⟩ (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, by simpa using Nat.lt_succ_iff.mp hk, hkf⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', by simpa using Nat.lt_succ_iff.mp hk', hkf, hk'f⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', by simpa using Nat.lt_succ_iff.mp hk'',
        hkf, hk'f, hk''f⟩)

end HPC.Fold
