import HPC.Fold.ProfileK

/-!
# The profile engine at an arbitrary trough, and the exact criterion for `w₄`

`HPC/Fold/ProfileK.lean` reads the batch-48 engine with the peak `K` as a parameter, and the
basepoint `P` still inside `[L + 2, L + 4]`. This file removes that restriction, and with it the
last of the three walks of `unserved_three_walks` gets an engine.

## Why the basepoint had to move

`w₄ = L+3 → L+2 → L+8 → L+1` is the reflection of a three-leg walk: with `g = 2L + 9 - f` the walk
becomes `leg3Walk L (L + 9) (L + 7) (L + 7)`, whose trough `P` is its own peak `K = L + 7`, and the
arm of the branch — based at `L + 4` — becomes an arm based at `L + 5 = P - 2`. So the engine is
needed at a basepoint far above `L + 4`, and for an arm that starts two levels *below* the walk's
trough rather than at it. Both are removed here:

* the announcement of the descents is asked at the threshold `P - 3`, which is what the walk's
  first leg fails to serve, rather than at `L + 1`; for `P ≤ L + 4` that is the same clause or a
  weaker one, so nothing is lost at the old basepoints;
* the arm is allowed to start anywhere in `[P - 2, P]`, the window of the walk's first position.

`val3_gstepP`, `prog3_profileP` and `gseq3_invP` are the one-step lemma, the progress clauses and
the induction; `foldsOnto_leg3_profileP_min` is the engine.

## The criterion for `w₄`

Read through the reflection, the engine asks of an arm `f` of the branch exactly two sentences:

* `MidW4` — before every ascent to `L + 5` a time at `L + 3` or below, at a step at least `1` and
  at least two steps earlier. This is the clause the walk's *trough* forces, and it is what was
  missing: `w₄` descends before it climbs, so an arm that rises at once folds onto no prefix of it.
* `BottomW4` — the floor clause of `HPC/Fold/LandmarkW.lean`.

Both are necessary (`midW4_of_foldsOnto_w4`, `bottomW4_of_foldsOnto_w4`), and together with
`CeilW4` — which `MidW4` implies in the form the proof consumes — they are sufficient. So
`foldsOnto_w4_iff_landmark`: for a 1-Lipschitz arm of the band based at `L + 4`, folding onto `w₄`
is **equivalent** to `MidW4 ∧ CeilW4 ∧ BottomW4`, and all three walks of the branch now have an
exact criterion.
-/

namespace HPC.Fold

/-! ## The walk, at a trough that may be its own peak -/

/-- `val3_bounds` with `P = K` allowed. -/
theorem val3_bounds' {L H K P v u : ℤ} (hPK : P ≤ K) (hKH : K ≤ H - 1) (hLP : L + 2 ≤ P)
    (h : Val3 L H K P v u) : 0 ≤ u ∧ u ≤ 2 * K - P - 2 * L + H - 2 := by
  unfold Val3 at h; omega

/-- `val3_walk` with `P = K` allowed. -/
theorem val3_walk' {L H K P v u : ℤ} (hPK : P ≤ K) (hKH : K ≤ H - 1) (hLP : L + 2 ≤ P)
    (h : Val3 L H K P v u) : |v - leg3Walk L H K P u.toNat| ≤ 1 := by
  obtain ⟨h0, hlast⟩ := val3_bounds' hPK hKH hLP h
  have hcast : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg h0
  unfold Val3 at h
  unfold leg3Walk
  by_cases hc1 : ((u.toNat : ℕ) : ℤ) ≤ K - P + 1
  · rw [if_pos hc1, abs_le]; omega
  · rw [if_neg hc1]
    by_cases hc2 : ((u.toNat : ℕ) : ℤ) ≤ 2 * K - P - L
    · rw [if_pos hc2, abs_le]; omega
    · rw [if_neg hc2, abs_le]; omega

/-- `foldsOnto_leg3_of_val3` with `P = K` allowed. -/
theorem foldsOnto_leg3_of_val3' {m : ℕ} (f : Fin m → ℤ) (L H K P : ℤ) (u : ℕ → ℤ)
    (hLP : L + 2 ≤ P) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hu : ∀ j : Fin m, u j.val = f j)
    (hval : ∀ j : Fin m, Val3 L H K P (u j.val) (gseq3 L H K P u j.val)) :
    FoldsOnto f (leg3Len L H K P) (leg3Walk L H K P) := by
  refine ⟨fun j => (gseq3 L H K P u j.val).toNat, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro j
    obtain ⟨h1, h2⟩ := val3_bounds' hPK hKH hLP (hval j)
    simp only [leg3Len]
    omega
  · intro j j' hjj'
    obtain ⟨h1, h2⟩ := val3_bounds' hPK hKH hLP (hval j)
    obtain ⟨h3, h4⟩ := val3_bounds' hPK hKH hLP (hval j')
    have hstep : gseq3 L H K P u j'.val = gstep3 L H K P (u j'.val) (gseq3 L H K P u j.val) := by
      rw [show j'.val = j.val + 1 from hjj', gseq3_succ]
    obtain ⟨h5, h6⟩ := gstep3_dist L H K P (u j'.val) (gseq3 L H K P u j.val)
    rw [abs_le]
    omega
  · intro j hj
    have h : gseq3 L H K P u j.val = 0 := by rw [hj, gseq3_zero]
    rw [h]
    rfl
  · intro j
    have h := hval j
    rw [hu j] at h
    exact val3_walk' hPK hKH hLP h

/-! ## The one-step lemmas -/

set_option maxHeartbeats 1000000 in
/-- **The greedy step stays legal at an arbitrary trough.** The exclusion at the bottom is asked
at the threshold `P - 3`: a step below the reach of the walk's first leg needs the descending leg
to be within reach. -/
theorem val3_gstepP {L H K P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1) (hval : Val3 L H K P v q)
    (h0 : v' ≤ P - 3 → 2 * K - P - v ≤ q) (hK : K + 2 ≤ v' → v - 2 * L - P + 2 * K - 2 ≤ q) :
    Val3 L H K P v' (gstep3 L H K P v' q) := by
  refine gstep3_elim (Q := fun g => Val3 L H K P v' g) (fun h => h) (fun _ h => h) ?_
  intro h1 h2
  unfold Val3 at hval h1 h2 ⊢
  push_neg at h1 h2
  omega

set_option maxHeartbeats 4000000 in
/-- **The progress clauses at an arbitrary trough.** In order: the clock, the `R` bound, the `S`
bound, the far end of the second leg, and the slack clock. -/
theorem prog3_profileP {L H K P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (hv0 : L ≤ v) (hvH : v ≤ H) (hv'0 : L ≤ v') (hv'H : v' ≤ H)
    (hvv1 : v - 1 ≤ v') (hvv2 : v' ≤ v + 1)
    (hnew : Val3 L H K P v' (gstep3 L H K P v' q)) :
    (∀ n : ℤ, min (min n (v - P + 2)) (K - P + 1) ≤ q →
        min (min (n + 1) (v' - P + 2)) (K - P + 1) ≤ gstep3 L H K P v' q) ∧
    (2 * K - P - v ≤ q → 2 * K - P - v' ≤ gstep3 L H K P v' q) ∧
    (v - 2 * L - P + 2 * K - 2 ≤ q → v' - 2 * L - P + 2 * K - 2 ≤ gstep3 L H K P v' q) ∧
    (min (2 * K - P + 2 - v) (2 * K - P - L) ≤ q →
      min (2 * K - P + 2 - v') (2 * K - P - L) ≤ gstep3 L H K P v' q) ∧
    (∀ n : ℤ, 2 * K - P - v ≤ q → min (min (2 * K - P + 2 - v) (2 * K - P - L)) n ≤ q →
        min (min (2 * K - P + 2 - v') (2 * K - P - L)) (n + 1) ≤ gstep3 L H K P v' q) := by
  refine gstep3_facts
    (fun g => (∀ n : ℤ, min (min n (v - P + 2)) (K - P + 1) ≤ q →
        min (min (n + 1) (v' - P + 2)) (K - P + 1) ≤ g) ∧
      (2 * K - P - v ≤ q → 2 * K - P - v' ≤ g) ∧
      (v - 2 * L - P + 2 * K - 2 ≤ q → v' - 2 * L - P + 2 * K - 2 ≤ g) ∧
      (min (2 * K - P + 2 - v) (2 * K - P - L) ≤ q →
        min (2 * K - P + 2 - v') (2 * K - P - L) ≤ g) ∧
      (∀ n : ℤ, 2 * K - P - v ≤ q → min (min (2 * K - P + 2 - v) (2 * K - P - L)) n ≤ q →
        min (min (2 * K - P + 2 - v') (2 * K - P - L)) (n + 1) ≤ g)) hnew ?_
  intro g hgv hcase hmax hstay
  unfold Val3 at hgv hmax hstay
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega
  · intros; omega

/-! ## The induction -/

set_option maxHeartbeats 2000000 in
/-- **The invariant in profile form, at an arbitrary trough.** A 1-Lipschitz level sequence in
`[L, H]` starting inside the window of the walk's first position whose descents below `P - 3` and
ascents to `K + 2` are announced in profile form keeps the greedy time legal. -/
theorem gseq3_invP (L H K P : ℤ) (a b : ℕ) (u : ℕ → ℤ) (N : ℕ)
    (hLP : L + 2 ≤ P) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (ha : (a : ℤ) = K - P + 1) (hb : (b : ℤ) = K - L - 1)
    (hu0lo : P - 2 ≤ u 0) (hu0hi : u 0 ≤ P)
    (hlo : ∀ j, j ≤ N → L ≤ u j) (hhi : ∀ j, j ≤ N → u j ≤ H)
    (hlip : ∀ j, j + 1 ≤ N → u j - 1 ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1)
    (hvalley : ∀ d, d ≤ N → u d ≤ P - 3 → ∃ j, a ≤ j ∧ j < d ∧ K - 1 ≤ u j)
    (hceil : ∀ d, d ≤ N → K + 2 ≤ u d →
      ∃ j k, a ≤ j ∧ j + b ≤ k ∧ k < d ∧ K - 1 ≤ u j ∧ u k ≤ L + 2) :
    ∀ t, t ≤ N →
      Val3 L H K P (u t) (gseq3 L H K P u t) ∧
      min (min (t : ℤ) (u t - P + 2)) (K - P + 1) ≤ gseq3 L H K P u t ∧
      ((∃ j, j ≤ t ∧ a ≤ j ∧ K - 1 ≤ u j) → 2 * K - P - u t ≤ gseq3 L H K P u t) ∧
      (∀ j, j ≤ t → a ≤ j → K - 1 ≤ u j →
        min (min (2 * K - P + 2 - u t) (2 * K - P - L)) ((t : ℤ) - (j : ℤ) + (K - P + 1)) ≤
          gseq3 L H K P u t) ∧
      ((∃ j k, k ≤ t ∧ a ≤ j ∧ j + b ≤ k ∧ K - 1 ≤ u j ∧ u k ≤ L + 2) →
        u t - 2 * L - P + 2 * K - 2 ≤ gseq3 L H K P u t) := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [gseq3_zero]
        unfold Val3
        omega
      · rw [gseq3_zero]
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
      have hA0 : u (t + 1) ≤ P - 3 → 2 * K - P - u t ≤ gseq3 L H K P u t := by
        intro h
        obtain ⟨j, h3, hj5, hju⟩ := hvalley (t + 1) ht h
        exact hR ⟨j, by omega, h3, hju⟩
      have hA1 : K + 2 ≤ u (t + 1) → u t - 2 * L - P + 2 * K - 2 ≤ gseq3 L H K P u t := by
        intro h
        obtain ⟨j, k, h3, hjk, hkd, hju, hku⟩ := hceil (t + 1) ht h
        exact hS ⟨j, k, by omega, h3, hjk, hju, hku⟩
      have hnew : Val3 L H K P (u (t + 1)) (gseq3 L H K P u (t + 1)) := by
        rw [gseq3_succ]
        exact val3_gstepP hLP hPK hKH hv0 hvH hv'0 hv'H hl1 hl2 hval hA0 hA1
      obtain ⟨p1, p2, p3, p4, p5⟩ :=
        prog3_profileP hLP hPK hKH hv0 hvH hv'0 hv'H hl1 hl2
          (by rw [← gseq3_succ]; exact hnew)
      rw [gseq3_succ] at hnew ⊢
      have hclock' : min (min ((t + 1 : ℕ) : ℤ) (u (t + 1) - P + 2)) (K - P + 1) ≤
          gstep3 L H K P (u (t + 1)) (gseq3 L H K P u t) := by
        have := p1 (t : ℤ) hclock
        rw [hcast]
        exact this
      have hR' : (∃ j, j ≤ t + 1 ∧ a ≤ j ∧ K - 1 ≤ u j) →
          2 * K - P - u (t + 1) ≤ gstep3 L H K P (u (t + 1)) (gseq3 L H K P u t) := by
        rintro ⟨j, hj, h3, hju⟩
        rcases Nat.lt_or_ge j (t + 1) with h | h
        · exact p2 (hR ⟨j, by omega, h3, hju⟩)
        · have hjt : j = t + 1 := by omega
          rw [hjt] at hju
          have h3' : (a : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by exact_mod_cast show a ≤ t + 1 by omega
          omega
      have hC' : ∀ j, j ≤ t + 1 → a ≤ j → K - 1 ≤ u j →
          min (min (2 * K - P + 2 - u (t + 1)) (2 * K - P - L))
              (((t + 1 : ℕ) : ℤ) - (j : ℤ) + (K - P + 1)) ≤
            gstep3 L H K P (u (t + 1)) (gseq3 L H K P u t) := by
        intro j hj h3 hju
        rcases Nat.lt_or_ge j (t + 1) with h | h
        · have hRt := hR ⟨j, by omega, h3, hju⟩
          have hCt := hC j (by omega) h3 hju
          have := p5 ((t : ℤ) - (j : ℤ) + (K - P + 1)) hRt hCt
          rw [hcast]
          have e : (t : ℤ) - (j : ℤ) + (K - P + 1) + 1 = (t : ℤ) + 1 - (j : ℤ) + (K - P + 1) := by
            ring
          rw [e] at this
          exact this
        · have hjt : j = t + 1 := by omega
          have hjc : ((j : ℕ) : ℤ) = ((t + 1 : ℕ) : ℤ) := by rw [hjt]
          rw [hjt] at hju
          have h3' : (a : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by exact_mod_cast show a ≤ t + 1 by omega
          omega
      refine ⟨hnew, hclock', hR', hC', ?_⟩
      rintro ⟨j, k, hk, h3, hjk, hju, hku⟩
      rcases Nat.lt_or_ge k (t + 1) with h | h
      · exact p3 (hS ⟨j, k, by omega, h3, hjk, hju, hku⟩)
      · have hkt : k = t + 1 := by omega
        rw [hkt] at hku
        have hCk := hC' j (by omega) h3 hju
        have hjk' : ((j : ℕ) : ℤ) + (b : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by
          exact_mod_cast show j + b ≤ t + 1 by omega
        omega

/-! ## The engine -/

set_option maxHeartbeats 1000000 in
/-- **The three-leg fold at an arbitrary trough, asked for one level lower.** A 1-Lipschitz arm in
`[L, H]` starting inside the window of the walk's first position, whose descents below `P - 3` and
ascents to `K + 2` are announced by a time at `K - 1` at a step at least the peak position, folds
onto `leg3Walk L H K P`. -/
theorem foldsOnto_leg3_profileP_min {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L H K P : ℤ) (a b : ℕ)
    (hLP : L + 2 ≤ P) (hPK : P ≤ K) (hKH : K ≤ H - 1)
    (ha : (a : ℤ) = K - P + 1) (hb : (b : ℤ) = K - L - 1)
    (h0lo : P - 2 ≤ f ⟨0, hm⟩) (h0hi : f ⟨0, hm⟩ ≤ P) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hvalley : ∀ d : Fin m, f d ≤ P - 3 →
      ∃ j : Fin m, a ≤ j.val ∧ j.val < d.val ∧ K - 1 ≤ f j)
    (hceil : ∀ d : Fin m, K + 2 ≤ f d →
      ∃ j k : Fin m, a ≤ j.val ∧ j.val + b ≤ k.val ∧ k.val < d.val ∧
        K - 1 ≤ f j ∧ f k ≤ L + 2) :
    FoldsOnto f (leg3Len L H K P) (leg3Walk L H K P) := by
  classical
  set u : ℕ → ℤ := fun k => if h : k < m then f ⟨k, h⟩ else P with hudef
  have hu : ∀ j : Fin m, u j.val = f j := by
    intro j
    simp only [hudef, j.isLt, dif_pos]
  have hu' : ∀ j, ∀ h : j < m, u j = f ⟨j, h⟩ := by
    intro j h
    simpa using hu ⟨j, h⟩
  refine foldsOnto_leg3_of_val3' f L H K P u hLP hPK hKH hu ?_
  have key := gseq3_invP L H K P a b u (m - 1) hLP hPK hKH ha hb ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (key j.val (by have := j.isLt; omega)).1
  · rw [hu' 0 hm]; exact h0lo
  · rw [hu' 0 hm]; exact h0hi
  · intro j hj
    have hjm : j < m := by omega
    rw [hu' j hjm]
    exact hL _
  · intro j hj
    have hjm : j < m := by omega
    rw [hu' j hjm]
    exact hH _
  · intro j hj
    have hjm : j < m := by omega
    have hj1m : j + 1 < m := by omega
    have := hf ⟨j, hjm⟩ ⟨j + 1, hj1m⟩ rfl
    rw [abs_le] at this
    rw [hu' j hjm, hu' (j + 1) hj1m]
    omega
  · intro d hd hdu
    have hdm : d < m := by omega
    rw [hu' d hdm] at hdu
    obtain ⟨j, h3, hj5, hju⟩ := hvalley ⟨d, hdm⟩ hdu
    exact ⟨j.val, h3, hj5, by rw [hu' j.val j.isLt]; exact hju⟩
  · intro d hd hdu
    have hdm : d < m := by omega
    rw [hu' d hdm] at hdu
    obtain ⟨j, k, h3, hjk, hkd, hju, hku⟩ := hceil ⟨d, hdm⟩ hdu
    exact ⟨j.val, k.val, h3, hjk, hkd, by rw [hu' j.val j.isLt]; exact hju,
      by rw [hu' k.val k.isLt]; exact hku⟩

/-! ## The reflected walk `w₄` -/

/-- **The trough clause of `w₄`.** Before every ascent to `L + 5` a time at `L + 3` or below, at a
step at least `1` and at least two steps earlier. This is the clause the walk's trough forces, and
the one that separates `w₄` from the two walks that climb first. -/
def MidW4 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 5 ≤ f d → ∃ j : Fin m, 1 ≤ j.val ∧ j.val + 2 ≤ d.val ∧ f j ≤ L + 3

/-- **The trough clause in the form the proof consumes.** Only `1 ≤ j` and `j < d` are spent. -/
def MidW4Min {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 5 ≤ f d → ∃ j : Fin m, 1 ≤ j.val ∧ j.val < d.val ∧ f j ≤ L + 3

/-- **The floor clause in the form the proof consumes.** Of the three index bounds of `BottomW4`
two are spent, `1 ≤ j` and `j + 6 ≤ k`. -/
def BottomW4Min {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L → ∃ j k : Fin m, 1 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val < d.val ∧
    f j ≤ L + 3 ∧ L + 7 ≤ f k

/-- The commissioned clause is the one the proof consumes. -/
theorem midW4Min_of_midW4 {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : MidW4 f L) : MidW4Min f L := by
  intro d hd
  obtain ⟨j, h1, h2, hj⟩ := h d hd
  exact ⟨j, h1, by omega, hj⟩

/-- The commissioned clause is the one the proof consumes. -/
theorem bottomW4Min_of_bottomW4 {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : BottomW4 f L) :
    BottomW4Min f L := by
  intro d hd
  obtain ⟨j, k, h1, hjk, hkd, hj, hk⟩ := h d hd
  exact ⟨j, k, h1, hjk, by omega, hj, hk⟩

/-- An ascent to `L + 5` is served only by the positions `3` and later of `w₄`. -/
theorem leg3Walk_w4_mid_pos {L v : ℤ} {p : ℕ} (hp : p < 15) (hv : L + 5 ≤ v)
    (h : |v - leg3Walk' L (L + 9) (L + 7) (L + 2) p| ≤ 1) : 3 ≤ p := by
  rw [leg3Walk_w4_val L p hp, abs_le] at h
  by_contra hc
  interval_cases p <;> simp_all <;> omega

/-- **The trough clause of `w₄` is necessary.** An arm folding onto `L+3 → L+2 → L+8 → L+1` has,
before every ascent to `L + 5`, a time at `L + 3` or below at a step at least `1` and at least two
steps earlier. -/
theorem midW4_of_foldsOnto_w4 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 7))
      (leg3Walk' L (L + 9) (L + 7) (L + 2))) :
    MidW4 f L := by
  intro d hd
  have hpos : ∀ p : ℕ, p < leg3Len L (L + 9) (L + 7) (L + 7) →
      |f d - leg3Walk' L (L + 9) (L + 7) (L + 2) p| ≤ 1 → 3 ≤ p := by
    intro p hp hpv
    rw [leg3Len_w4'] at hp
    exact leg3Walk_w4_mid_pos hp hd hpv
  obtain ⟨j, hj0, hjd, hjv⟩ := foldsOnto_landmark1 h d 1 3 (by norm_num) hpos
  rw [leg3Walk_w4_one, abs_le] at hjv
  exact ⟨j, hj0, by omega, by omega⟩

/-- **The engine for `w₄`.** A 1-Lipschitz arm of `[L, L + 9]` based at `L + 4` whose ascents to
`L + 5` and descents to `L` are announced — the first by a time at `L + 3` or below at a step at
least `1`, the second by such a time followed six steps later or more by a time at `L + 7` or
above — folds onto `w₄ = L+3 → L+2 → L+8 → L+1`.

The proof reflects the arm in the level `2L + 9`, where the walk becomes
`leg3Walk L (L + 9) (L + 7) (L + 7)`, a three-leg walk whose trough is its own peak, and applies
the engine at that trough. -/
theorem foldsOnto_w4_profile_min {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hmid : MidW4Min f L) (hbot : BottomW4Min f L) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk' L (L + 9) (L + 7) (L + 2)) := by
  set g : Fin m → ℤ := fun j => L + (L + 9) - f j with hg
  have hglip : IsLip g := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [hg]
    rw [abs_le] at this ⊢
    omega
  have hgL : ∀ j, L ≤ g j := fun j => by have := hH j; simp only [hg]; omega
  have hgH : ∀ j, g j ≤ L + 9 := fun j => by have := hL j; simp only [hg]; omega
  have hgvalley : ∀ d : Fin m, g d ≤ (L + 7) - 3 →
      ∃ j : Fin m, 1 ≤ j.val ∧ j.val < d.val ∧ (L + 7) - 1 ≤ g j := by
    intro d hd
    have hfd : L + 5 ≤ f d := by simp only [hg] at hd; omega
    obtain ⟨j, h1, hjd, hjf⟩ := hmid d hfd
    exact ⟨j, h1, hjd, by simp only [hg]; omega⟩
  have hgceil : ∀ d : Fin m, (L + 7) + 2 ≤ g d →
      ∃ j k : Fin m, 1 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val < d.val ∧
        (L + 7) - 1 ≤ g j ∧ g k ≤ L + 2 := by
    intro d hd
    have hfd : f d ≤ L := by simp only [hg] at hd; omega
    obtain ⟨j, k, h1, hjk, hkd, hjf, hkf⟩ := hbot d hfd
    exact ⟨j, k, h1, hjk, hkd, by simp only [hg]; omega, by simp only [hg]; omega⟩
  obtain ⟨β, h1, h2, h3, h4⟩ :=
    foldsOnto_leg3_profileP_min hm g hglip L (L + 9) (L + 7) (L + 7) 1 6 (by omega) (by omega)
      (by omega) (by push_cast; ring) (by push_cast; ring)
      (by simp only [hg, h0]; omega) (by simp only [hg, h0]; omega) hgL hgH hgvalley hgceil
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [hg] at this
  simp only [leg3Walk']
  rw [show L + (L + 9) - (L + 2) = L + 7 by ring] at *
  rw [abs_le] at this ⊢
  omega

/-- **The criterion for the reflected walk is exact.** For a 1-Lipschitz arm of the band
`[L, L + 9]` based at `L + 4`, folding onto `w₄ = L+3 → L+2 → L+8 → L+1` is equivalent to the
landmark sentence of that walk: the trough clause `MidW4` at its ascents to `L + 5`, the ceiling
clause `CeilW4` at its ascents to `L + 8`, and the floor clause `BottomW4` at its descents to `L`.
Necessity is the itinerary's intermediate value theorem; sufficiency needs only `MidW4` and
`BottomW4`, since in the form the proof consumes `MidW4` already implies `CeilW4`. -/
theorem foldsOnto_w4_iff_landmark {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 7)) (leg3Walk' L (L + 9) (L + 7) (L + 2)) ↔
      (MidW4 f L ∧ CeilW4 f L ∧ BottomW4 f L) := by
  constructor
  · intro h
    exact ⟨midW4_of_foldsOnto_w4 h, ceilW4_of_foldsOnto_w4 h, bottomW4_of_foldsOnto_w4 h⟩
  · rintro ⟨hmid, -, hbot⟩
    exact foldsOnto_w4_profile_min hm f hf L h0 hL hH (midW4Min_of_midW4 hmid)
      (bottomW4Min_of_bottomW4 hbot)

end HPC.Fold
