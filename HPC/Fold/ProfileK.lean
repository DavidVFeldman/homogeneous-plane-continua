import HPC.Fold.LandmarkW

/-!
# The profile engine at an arbitrary peak, and the exact criterion for `w₅`

Batch 48 lowered the demands of the three-leg engine by one level and paid for the level with
index clauses: `foldsOnto_leg3deep_profile_min` (`HPC/Fold/Leg3Profile.lean`) folds a 1-Lipschitz
arm of `[L, L + 9]` based at `L + 4` onto `w₃ = L+3 → L+6 → L+1 → L+8` from announcements that ask
a time at `L + 5` — one below the walk's peak — at a step at least `3`. That engine is stated at
the peak `L + 6`, and its constants `3`, `5`, `8`, `L + 5`, `L + 8` are the positions and levels of
that one walk.

This file restates it with the peak as a parameter. Nothing in the argument depends on the peak
being `L + 6`: the clock reaches the peak position `K - P + 1`, the slack clock crosses from the
peak position to the valley position `2K - P - L`, and the announcements ask a time at `K - 1`
followed by a time at `L + 2`, exactly as before. `foldsOnto_leg3_profileK_min` is the engine,
`prog3_profileK` its one-step lemma and `gseq3_invK` its induction.

## What it gives

At `K = L + 6` it is the batch-48 engine (`foldsOnto_leg3deep_profile_min` is recovered as
`foldsOnto_w3_profileK`). At `K = L + 7` it is an engine for the third of the three walks of
`unserved_three_walks`, `w₅ = L+3 → L+7 → L+1 → L+8`, and there the two halves **meet**:

* necessity (`valley5_of_foldsOnto_w5`, `topW5_of_foldsOnto_w5`, `HPC/Fold/LandmarkW.lean`) gives
  `Valley5` — a time at `L + 6` at a step at least `4`, five steps or more before every descent to
  `L + 1` — and `TopW5` — a time at `L + 6` at a step at least `4`, then a time at `L + 2` six
  steps later or more, itself seven steps or more before every ascent to `L + 9`;
* sufficiency (`foldsOnto_w5_profile_min`) asks exactly those two sentences, with only the index
  bounds the proof spends.

So `foldsOnto_w5_iff_landmark`: for a 1-Lipschitz arm of the band based at `L + 4`, folding onto
`w₅` is **equivalent** to `Valley5 ∧ TopW5`. That is the second of the three walks of the branch to
get an exact criterion, after `w₃` (`foldsOnto_leg3deep_iff_landmark`); the peak of `w₅` is
`L + 7`, so the walk serves `L + 8` from its peak and only ascents to `L + 9` are announced.
-/

namespace HPC.Fold

/-! ## The one-step lemma -/

set_option maxHeartbeats 4000000 in
/-- **The progress clauses of the profile form, at an arbitrary peak.** In order: the clock, the
`R` bound, the `S` bound, the far end of the second leg, and the slack clock — a greedy time that
is past the peak and short of the far end advances by one position at every step. -/
theorem prog3_profileK {L H K P v q v' : ℤ} (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4)
    (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
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
/-- **The invariant in profile form, at an arbitrary peak.** A 1-Lipschitz level sequence in
`[L, H]` based at `P` whose descents to `L + 1` and ascents to `K + 2` are announced in profile
form keeps the greedy time legal, and carries the clock, the `R` bound, the slack clock and the
`S` bound.

The two index constants are the walk's own: `a = K - P + 1` is the peak position and `b = K - L - 1`
the number of positions from the peak to the valley. -/
theorem gseq3_invK (L H K P : ℤ) (a b : ℕ) (u : ℕ → ℤ) (N : ℕ)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
    (ha : (a : ℤ) = K - P + 1) (hb : (b : ℤ) = K - L - 1)
    (hu0 : u 0 = P)
    (hlo : ∀ j, j ≤ N → L ≤ u j) (hhi : ∀ j, j ≤ N → u j ≤ H)
    (hlip : ∀ j, j + 1 ≤ N → u j - 1 ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1)
    (hvalley : ∀ d, d ≤ N → u d ≤ L + 1 → ∃ j, a ≤ j ∧ j < d ∧ K - 1 ≤ u j)
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
      have hA0 : u (t + 1) ≤ L + 1 → 2 * K - P - u t ≤ gseq3 L H K P u t := by
        intro h
        obtain ⟨j, h3, hj5, hju⟩ := hvalley (t + 1) ht h
        exact hR ⟨j, by omega, h3, hju⟩
      have hA1 : K + 2 ≤ u (t + 1) → u t - 2 * L - P + 2 * K - 2 ≤ gseq3 L H K P u t := by
        intro h
        obtain ⟨j, k, h3, hjk, hkd, hju, hku⟩ := hceil (t + 1) ht h
        exact hS ⟨j, k, by omega, h3, hjk, hju, hku⟩
      have hnew : Val3 L H K P (u (t + 1)) (gseq3 L H K P u (t + 1)) := by
        rw [gseq3_succ]
        refine val3_gstep_deep hLP hPL hPK hKH hv0 hvH hv'0 hv'H hl1 hl2 hval ?_ ?_
        · intro h
          have := hA0 (by omega)
          omega
        · intro h
          have := hA1 (by omega)
          omega
      obtain ⟨p1, p2, p3, p4, p5⟩ :=
        prog3_profileK hLP hPL hPK hKH hv0 hvH hv'0 hv'H hl1 hl2
          (by rw [← gseq3_succ]; exact hnew)
      rw [gseq3_succ] at hnew ⊢
      -- the clock
      have hclock' : min (min ((t + 1 : ℕ) : ℤ) (u (t + 1) - P + 2)) (K - P + 1) ≤
          gstep3 L H K P (u (t + 1)) (gseq3 L H K P u t) := by
        have := p1 (t : ℤ) hclock
        rw [hcast]
        exact this
      -- the `R` bound
      have hR' : (∃ j, j ≤ t + 1 ∧ a ≤ j ∧ K - 1 ≤ u j) →
          2 * K - P - u (t + 1) ≤ gstep3 L H K P (u (t + 1)) (gseq3 L H K P u t) := by
        rintro ⟨j, hj, h3, hju⟩
        rcases Nat.lt_or_ge j (t + 1) with h | h
        · exact p2 (hR ⟨j, by omega, h3, hju⟩)
        · have hjt : j = t + 1 := by omega
          rw [hjt] at hju
          have h3' : (a : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by exact_mod_cast show a ≤ t + 1 by omega
          omega
      -- the slack clock
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
      -- the `S` bound
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
/-- **The three-leg fold at an arbitrary peak, asked for one level lower.** A 1-Lipschitz arm in
`[L, H]` based at `P` whose descents to `L + 1` and ascents to `K + 2` are announced by a time at
`K - 1` — one below the peak — at a step at least the peak position, folds onto
`leg3Walk L H K P`. -/
theorem foldsOnto_leg3_profileK_min {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L H K P : ℤ) (a b : ℕ)
    (hLP : L + 2 ≤ P) (hPL : P ≤ L + 4) (hPK : P + 1 ≤ K) (hKH : K ≤ H - 1)
    (ha : (a : ℤ) = K - P + 1) (hb : (b : ℤ) = K - L - 1)
    (h0 : f ⟨0, hm⟩ = P) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hvalley : ∀ d : Fin m, f d ≤ L + 1 →
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
  refine foldsOnto_leg3_of_val3 f L H K P u hLP hPK hKH hu ?_
  have key := gseq3_invK L H K P a b u (m - 1) hLP hPL hPK hKH ha hb ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (key j.val (by have := j.isLt; omega)).1
  · rw [hu' 0 hm, h0]
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

/-! ## The first walk again -/

/-- **The batch-48 engine is the case `K = L + 6`.** -/
theorem foldsOnto_w3_profileK {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hvalley : Leg3ValleyMin f L) (hceil : Leg3CeilMin f L) :
    FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) := by
  refine foldsOnto_leg3_profileK_min hm f hf L (L + 9) (L + 6) (L + 4) 3 5 (by omega) (by omega)
    (by omega) (by omega) (by push_cast; ring) (by push_cast; ring) h0 hL hH ?_ ?_
  · intro d hd
    obtain ⟨j, h3, hjd, hju⟩ := hvalley d hd
    exact ⟨j, h3, hjd, by omega⟩
  · intro d hd
    obtain ⟨j, k, h3, hjk, hkd, hju, hku⟩ := hceil d (by omega)
    exact ⟨j, k, h3, hjk, hkd, by omega, hku⟩

/-! ## The third walk: sufficiency at the landmark level -/

/-- **The valley clause of `w₅` in the form the proof consumes.** Of the two index bounds of
`Valley5` only `4 ≤ j` is spent. -/
def Valley5Min {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 4 ≤ j.val ∧ j.val < d.val ∧ L + 6 ≤ f j

/-- **The ceiling clause of `w₅` in the form the proof consumes.** Of the three index bounds of
`TopW5` two are spent, `4 ≤ j` and `j + 6 ≤ k`. -/
def TopW5Min {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 9 ≤ f d →
    ∃ j k : Fin m, 4 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val < d.val ∧
      L + 6 ≤ f j ∧ f k ≤ L + 2

/-- The commissioned clause is the one the proof consumes. -/
theorem valley5Min_of_valley5 {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : Valley5 f L) :
    Valley5Min f L := by
  intro d hd
  obtain ⟨j, h4, hj5, hju⟩ := h d hd
  exact ⟨j, h4, by omega, hju⟩

/-- The commissioned clause is the one the proof consumes. -/
theorem topW5Min_of_topW5 {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : TopW5 f L) : TopW5Min f L := by
  intro d hd
  obtain ⟨j, k, h4, hjk, hkd, hju, hku⟩ := h d hd
  exact ⟨j, k, h4, hjk, by omega, hju, hku⟩

/-- **The deep walk serves an arm that announces at the landmark level.** The engine at
`K = L + 7`: a 1-Lipschitz arm of `[L, L + 9]` based at `L + 4` whose descents to `L + 1` and
ascents to `L + 9` are announced by a time at `L + 6` — one below the walk's peak — folds onto
`w₅ = L+3 → L+7 → L+1 → L+8`. -/
theorem foldsOnto_w5_profile_min {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hvalley : Valley5Min f L) (hceil : TopW5Min f L) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4)) := by
  refine foldsOnto_leg3_profileK_min hm f hf L (L + 9) (L + 7) (L + 4) 4 6 (by omega) (by omega)
    (by omega) (by omega) (by push_cast; ring) (by push_cast; ring) h0 hL hH ?_ ?_
  · intro d hd
    obtain ⟨j, h4, hjd, hju⟩ := hvalley d hd
    exact ⟨j, h4, hjd, by omega⟩
  · intro d hd
    obtain ⟨j, k, h4, hjk, hkd, hju, hku⟩ := hceil d (by omega)
    exact ⟨j, k, h4, hjk, hkd, by omega, hku⟩

/-- **The criterion for the deep walk is exact.** For a 1-Lipschitz arm of the band `[L, L + 9]`
based at `L + 4`, folding onto `w₅ = L+3 → L+7 → L+1 → L+8` is equivalent to the landmark sentence
of that walk: `Valley5` at its descents to `L + 1` and `TopW5` at its ascents to `L + 9`.
Necessity is the itinerary's intermediate value theorem (`HPC/Fold/LandmarkW.lean`); sufficiency is
the profile engine at the peak `L + 7`. -/
theorem foldsOnto_w5_iff_landmark {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4)) ↔
      (Valley5 f L ∧ TopW5 f L) := by
  constructor
  · intro h
    exact ⟨valley5_of_foldsOnto_w5 h, topW5_of_foldsOnto_w5 h⟩
  · rintro ⟨hv, hc⟩
    exact foldsOnto_w5_profile_min hm f hf L h0 hL hH (valley5Min_of_valley5 hv)
      (topW5Min_of_topW5 hc)

end HPC.Fold
