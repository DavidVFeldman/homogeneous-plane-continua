import HPC.Fold.Crook

/-!
# The ascent profile: the exact criterion for the Λ-fold, from any nearby start

Lemma F1 (`foldsOnto_lam_iff`, `HPC/Fold/Itinerary.lean`) decides when an arm folds onto the
Λ-itinerary, but only for an arm that starts **at** the base of the walk, and its criterion
`CritLam` is a list of events: a link at the peak, or two links one below it, or one such link
preceded by a non-ascending step. Both restrictions matter for `S3`, because the walk that has to
serve the two arms of a basepoint is based one level below the basepoint, and because a list of
events is the wrong vocabulary: what decides the fold is not *which* events occur but *how many
steps* the arm needs to get high, since the walk time at index `j` never exceeds `j`.

This file replaces the event list by the **ascent profile**.

* `AscReach f p K j` says that the arm's first `j + 1` levels leave room to stand, at index `j`,
  at the peak time `K - p`: the index `j` is at least `K - p`, and every earlier level `f k` is at
  least `K - 1 - (j - k)`, which is exactly what the time assignment needs in order to have
  climbed to the peak by `j`.
* `CritLamProfile f p H` asks that before the arm ever drops to `p - 2` it has reached the peak
  time in that sense.

`foldsOnto_lam_of_profile` and `profile_of_foldsOnto_lam` prove that this is the exact criterion,
for any arm starting within one of `p`. `critLamProfile_of_critLam` records that the criterion is
implied by `CritLam` in the case F1 covers, so nothing is lost.

The time assignment is the explicit two-phase greedy `pseq`: while below the peak time it is
`min (q + 1) (v - p + 1)`, the largest time the level allows; past the peak time it is
`min (q + 1) (min (2K - p - v + 1) (2K - p - L - 1))`, the largest time on the descending leg.
-/

namespace HPC.Fold

/-! ## The two-phase greedy -/

/-- One step of the profile fold: advance along the ascending leg as far as the new level `v`
allows, or, past the peak time, along the descending leg. -/
def pstep (p K L : ℤ) (v q : ℤ) : ℤ :=
  if q + 1 ≤ K - p then min (q + 1) (v - p + 1)
  else min (q + 1) (min (2 * K - p - v + 1) (2 * K - p - L - 1))

/-- The time assignment of the profile fold. -/
def pseq (p K L : ℤ) (u : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => pstep p K L (u (j + 1)) (pseq p K L u j)

theorem pseq_zero (p K L : ℤ) (u : ℕ → ℤ) : pseq p K L u 0 = 0 := rfl

theorem pseq_succ (p K L : ℤ) (u : ℕ → ℤ) (j : ℕ) :
    pseq p K L u (j + 1) = pstep p K L (u (j + 1)) (pseq p K L u j) := rfl

/-- **The window condition.** The time `q` serves the level `v`: on the ascending leg the centre
is `p + q`, on the descending leg it is `2K - p - q`. -/
def PVal (p K L : ℤ) (v q : ℤ) : Prop :=
  (0 ≤ q ∧ q ≤ K - p ∧ v - p - 1 ≤ q ∧ q ≤ v - p + 1) ∨
  (K - p ≤ q ∧ q ≤ 2 * K - p - L - 1 ∧ 2 * K - p - v - 1 ≤ q ∧ q ≤ 2 * K - p - v + 1)

/-- Past the peak time the greedy stays past the peak time. -/
theorem pstep_ge (p K L v q : ℤ) (hLK : L + 1 ≤ K) (hv : v ≤ K + 1) (hq : K - p ≤ q) :
    K - p ≤ pstep p K L v q := by
  unfold pstep
  rw [if_neg (by omega)]
  simp only [le_min_iff]
  omega

/-- One greedy step keeps the window condition. The only thing the arm must supply is that it
does not drop to `p - 2` before the peak time has been reached. -/
theorem pval_pstep (p K L v v' q : ℤ) (hLp : L + 2 ≤ p) (hpK : p ≤ K)
    (hv'L : L ≤ v') (hv'K : v' ≤ K + 1) (hvv : v - 1 ≤ v') (hvv' : v' ≤ v + 1)
    (hval : PVal p K L v q) (hfloor : q < K - p → p - 1 ≤ v') :
    PVal p K L v' (pstep p K L v' q) := by
  unfold PVal at hval ⊢
  unfold pstep
  split_ifs with h
  · have hv' := hfloor (by omega)
    simp only [min_def]
    split_ifs <;> omega
  · simp only [min_def]
    split_ifs <;> omega

/-- A greedy step moves by at most one. -/
theorem pstep_dist (p K L v v' q : ℤ) (hLK : L + 1 ≤ K)
    (hv'K : v' ≤ K + 1) (hvv : v - 1 ≤ v') (hvv' : v' ≤ v + 1) (hval : PVal p K L v q) :
    q - 1 ≤ pstep p K L v' q ∧ pstep p K L v' q ≤ q + 1 := by
  unfold PVal at hval
  unfold pstep
  constructor
  · split_ifs <;> simp only [min_def] <;> split_ifs <;> omega
  · split_ifs <;> simp only [min_def] <;> split_ifs <;> omega

/-- Once the greedy is past the peak time it stays there, at every later index. -/
theorem pseq_mono_ge (p K L : ℤ) (u : ℕ → ℤ) (hLK : L + 1 ≤ K) (i : ℕ)
    (h : K - p ≤ pseq p K L u i) :
    ∀ j, i ≤ j → (∀ t, t ≤ j → u t ≤ K + 1) → K - p ≤ pseq p K L u j := by
  intro j
  induction j with
  | zero =>
      intro hij _
      have : i = 0 := by omega
      subst this
      exact h
  | succ n ih =>
      intro hij hu
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · have hn : K - p ≤ pseq p K L u n := ih (by omega) (fun t ht => hu t (by omega))
        rw [pseq_succ]
        exact pstep_ge p K L _ _ hLK (hu (n + 1) le_rfl) hn
      · have : i = n + 1 := by omega
        subst this
        exact h

/-- **The ascent profile reaches the peak time.** If the index `j` is at least `K - p` and every
level up to `j` is at least `K - 1 - (j - k)`, the greedy stands at the peak time by `j`. -/
theorem pseq_ge_of_ascReach (p K L : ℤ) (u : ℕ → ℤ) (j : ℕ) (hLK : L + 1 ≤ K)
    (hj : K - p ≤ (j : ℤ)) (hhi : ∀ k, k ≤ j → u k ≤ K + 1)
    (hprof : ∀ k, k ≤ j → K - 1 - ((j : ℤ) - (k : ℤ)) ≤ u k) :
    K - p ≤ pseq p K L u j := by
  have key : ∀ i, i ≤ j → min (i : ℤ) (K - p - ((j : ℤ) - (i : ℤ))) ≤ pseq p K L u i := by
    intro i
    induction i with
    | zero => intro _; simp only [pseq_zero, Nat.cast_zero]; omega
    | succ n ih =>
        intro hn
        have hIH := ih (by omega)
        rw [pseq_succ]
        rcases le_or_gt (K - p) (pseq p K L u n) with hge | hlt
        · have := pstep_ge p K L (u (n + 1)) (pseq p K L u n) hLK (hhi (n + 1) hn) hge
          push_cast
          omega
        · have hb : pstep p K L (u (n + 1)) (pseq p K L u n)
              = min (pseq p K L u n + 1) (u (n + 1) - p + 1) := by
            unfold pstep; rw [if_pos (by omega)]
          have hu1 := hprof (n + 1) hn
          rw [hb]
          simp only [le_min_iff, min_le_iff] at *
          push_cast at *
          omega
  have := key j le_rfl
  simp only [min_le_iff] at this
  omega

/-! ## The criterion -/

/-- `AscReach f p K j`: at index `j` there is room to stand at the peak time `K - p`. -/
def AscReach {m : ℕ} (f : Fin m → ℤ) (p K : ℤ) (j : Fin m) : Prop :=
  K - p ≤ (j.val : ℤ) ∧ ∀ k : Fin m, k.val ≤ j.val → K - 1 - ((j.val : ℤ) - (k.val : ℤ)) ≤ f k

/-- **The ascent-profile criterion.** Before the arm ever drops to `p - 2` it has reached the
peak time of the Λ-walk based at `p`. -/
def CritLamProfile {m : ℕ} (f : Fin m → ℤ) (p H : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ p - 2 → ∃ j : Fin m, j.val < d.val ∧ AscReach f p (κ p H) j

/-- **The criterion, read off.** For a 1-Lipschitz arm the profile condition at `j` says no more
than that the arm stands at `K - 1` at the index `j`, which must itself be at least `K - p`:
every earlier level is then automatically high enough, because the arm cannot have climbed
faster than one level per step. -/
theorem ascReach_iff_of_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (p K : ℤ) (j : Fin m) :
    AscReach f p K j ↔ (K - p ≤ (j.val : ℤ) ∧ K - 1 ≤ f j) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa using h2 j le_rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    have := abs_sub_le_of_isLip hf (j.val - k.val) k j (by omega)
    rw [abs_le] at this
    have hcast : ((j.val - k.val : ℕ) : ℤ) = (j.val : ℤ) - (k.val : ℤ) := by
      push_cast [Nat.cast_sub hk]; ring
    omega

/-- **The criterion, in the form it is used.** Before the arm ever drops to `p - 2` it stands at
the peak level `κ - 1`, at an index at least `κ - p`. -/
theorem critLamProfile_iff_of_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (p H : ℤ) :
    CritLamProfile f p H ↔
      ∀ d : Fin m, f d ≤ p - 2 →
        ∃ j : Fin m, j.val < d.val ∧ κ p H - p ≤ (j.val : ℤ) ∧ κ p H - 1 ≤ f j := by
  unfold CritLamProfile
  constructor
  · intro h d hd
    obtain ⟨j, hj, hrest⟩ := h d hd
    exact ⟨j, hj, (ascReach_iff_of_isLip hf _ _ j).mp hrest⟩
  · intro h d hd
    obtain ⟨j, hj, h1, h2⟩ := h d hd
    exact ⟨j, hj, (ascReach_iff_of_isLip hf _ _ j).mpr ⟨h1, h2⟩⟩

/-! ## Sufficiency -/

/-- **The profile fold.** An arm starting within one of `p`, with values in `[L, H]`, folds onto
the Λ-itinerary based at `p` as soon as the ascent-profile criterion holds. -/
theorem foldsOnto_lam_of_profile {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L : ℤ)
    (hLp : L + 2 ≤ p) (h0 : |f ⟨0, hm⟩ - p| ≤ 1)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) (hc : CritLamProfile f p H) :
    FoldsOnto f (lamLen p H L) (lamCenter p H L) := by
  classical
  set K : ℤ := κ p H with hK
  have hpK : p ≤ K := le_κ p H
  have hHK : H - 1 ≤ K := le_max_left _ _
  have hLK : L + 2 ≤ K := by omega
  set u : ℕ → ℤ := fun k => if h : k < m then f ⟨k, h⟩ else p with hudef
  have hu : ∀ j : Fin m, u j.val = f j := by
    intro j; simp only [hudef, j.isLt, dif_pos]
  have hulo : ∀ k, k < m → L ≤ u k := by
    intro k hk; rw [show u k = f ⟨k, hk⟩ from by simp [hudef, hk]]; exact hL _
  have huhi : ∀ k, k < m → u k ≤ K + 1 := by
    intro k hk
    rw [show u k = f ⟨k, hk⟩ from by simp [hudef, hk]]
    have := hH ⟨k, hk⟩; omega
  have hulip : ∀ k, k + 1 < m → u k - 1 ≤ u (k + 1) ∧ u (k + 1) ≤ u k + 1 := by
    intro k hk
    have hkm : k < m := by omega
    rw [show u k = f ⟨k, hkm⟩ from by simp [hudef, hkm],
      show u (k + 1) = f ⟨k + 1, hk⟩ from by simp [hudef, hk]]
    have := hf ⟨k, hkm⟩ ⟨k + 1, hk⟩ rfl
    rw [abs_le] at this
    omega
  -- the crossing supplied by the criterion
  have hcross : ∀ j : ℕ, j + 1 < m → u (j + 1) ≤ p - 2 → K - p ≤ pseq p K L u j := by
    intro j hjm hj
    have hjm' : j + 1 < m := hjm
    have hj' : f ⟨j + 1, hjm'⟩ ≤ p - 2 := by
      rwa [show u (j + 1) = f ⟨j + 1, hjm'⟩ from by simp [hudef, hjm']] at hj
    obtain ⟨i, hij, hi1, hi2⟩ := hc ⟨j + 1, hjm'⟩ hj'
    have hij' : i.val < j + 1 := hij
    have hreach : K - p ≤ pseq p K L u i.val := by
      refine pseq_ge_of_ascReach p K L u i.val (by omega) hi1
        (fun k hk => huhi k (by have := i.isLt; omega)) ?_
      intro k hk
      have hkm : k < m := by have := i.isLt; omega
      rw [show u k = f ⟨k, hkm⟩ from by simp [hudef, hkm]]
      exact hi2 ⟨k, hkm⟩ hk
    exact pseq_mono_ge p K L u (by omega) i.val hreach j (by omega)
      (fun t ht => huhi t (by omega))
  -- the window condition, by induction
  have hval : ∀ j : ℕ, j < m → PVal p K L (u j) (pseq p K L u j) := by
    intro j
    induction j with
    | zero =>
        intro _
        have h0' : |u 0 - p| ≤ 1 := by
          rw [show u 0 = f ⟨0, hm⟩ from by simp [hudef, hm]]; exact h0
        rw [abs_le] at h0'
        left
        rw [pseq_zero]
        omega
    | succ n ih =>
        intro hn
        have hnm : n < m := by omega
        have hprev := ih hnm
        rw [pseq_succ]
        refine pval_pstep p K L (u n) (u (n + 1)) _ hLp hpK (hulo _ hn) (huhi _ hn)
          (hulip n hn).1 (hulip n hn).2 hprev ?_
        intro hlt
        by_contra hcon
        have := hcross n hn (by omega)
        omega
  -- package
  refine ⟨fun j => (pseq p K L u j.val).toNat, ?_, ?_, ?_, ?_⟩
  · intro j
    have h := hval j.val j.isLt
    unfold PVal at h
    rw [lt_lamLen_iff]
    have : ((pseq p K L u j.val).toNat : ℤ) = pseq p K L u j.val := by
      apply Int.toNat_of_nonneg; omega
    rw [this]
    have : max (K - L - 1) 0 = K - L - 1 := by omega
    rw [hK] at *
    omega
  · intro j j' hjj'
    have h1 := hval j.val j.isLt
    have h2 := hval j'.val j'.isLt
    have hstep : pseq p K L u j'.val = pstep p K L (u j'.val) (pseq p K L u j.val) := by
      rw [hjj', pseq_succ]
    have hjm1 : j.val + 1 < m := by have := j'.isLt; omega
    have hlip1 := hulip j.val hjm1
    have hd := pstep_dist p K L (u j.val) (u j'.val) (pseq p K L u j.val) (by omega)
      (huhi _ j'.isLt) (by rw [hjj']; omega) (by rw [hjj']; omega) h1
    unfold PVal at h1 h2
    have e1 : ((pseq p K L u j.val).toNat : ℤ) = pseq p K L u j.val := by
      apply Int.toNat_of_nonneg; omega
    have e2 : ((pseq p K L u j'.val).toNat : ℤ) = pseq p K L u j'.val := by
      apply Int.toNat_of_nonneg; omega
    rw [e1, e2, abs_le]
    omega
  · intro j hj
    have h0' : pseq p K L u j.val = 0 := by rw [hj, pseq_zero]
    show (pseq p K L u j.val).toNat = 0
    rw [h0']
    rfl
  · intro j
    have h := hval j.val j.isLt
    have hq0 : 0 ≤ pseq p K L u j.val := by unfold PVal at h; omega
    have e : ((pseq p K L u j.val).toNat : ℤ) = pseq p K L u j.val := Int.toNat_of_nonneg hq0
    rw [← hu j]
    rcases le_or_gt (pseq p K L u j.val) (K - p) with hc1 | hc1
    · rw [lamCenter_asc _ _ _ _ (by rw [e]; exact hc1), e, abs_le]
      unfold PVal at h
      omega
    · rw [lamCenter_desc _ _ _ _ (by rw [e]; omega), e, abs_le]
      unfold PVal at h
      omega

/-! ## Necessity -/

/-- **The criterion is necessary.** -/
theorem profile_of_foldsOnto_lam {m : ℕ} (f : Fin m → ℤ) (p H L : ℤ)
    (hfold : FoldsOnto f (lamLen p H L) (lamCenter p H L)) : CritLamProfile f p H := by
  classical
  obtain ⟨β, hlt, hlip, hz, hw⟩ := hfold
  set K : ℤ := κ p H with hK
  have hpK : p ≤ K := le_κ p H
  -- the centre at a time, as an inequality
  have hcen : ∀ (j : Fin m), |f j - lamCenter p H L (β j)| ≤ 1 := hw
  -- `β` is bounded by the index
  have hβle : ∀ j : Fin m, (β j : ℤ) ≤ (j.val : ℤ) := by
    intro j
    obtain ⟨jv, hjv⟩ : ∃ jv, j.val = jv := ⟨j.val, rfl⟩
    induction jv generalizing j with
    | zero =>
        have : β j = 0 := hz j hjv
        simp [this, hjv]
    | succ n ih =>
        have hnm : n < m := by have := j.isLt; omega
        have hstep := hlip ⟨n, hnm⟩ j (by omega)
        have := ih ⟨n, hnm⟩ rfl
        rw [abs_le] at hstep
        push_cast at this ⊢
        omega
  intro d hd
  -- the time at `d` is past the peak
  have hdesc : K - p < (β d : ℤ) := by
    by_contra hcon
    have := hcen d
    rw [lamCenter_asc _ _ _ _ (by omega), abs_le] at this
    omega
  -- the least index at the peak time or beyond
  have hex : ∃ j : Fin m, K - p ≤ (β j : ℤ) := ⟨d, by omega⟩
  obtain ⟨j, hj, hjmin⟩ := exists_least_index (fun j : Fin m => K - p ≤ (β j : ℤ)) hex
  have hjd : j.val < d.val := by
    by_contra hcon
    have hdj : d.val ≤ j.val := by omega
    have := hjmin d
    rcases lt_or_ge d.val j.val with h | h
    · exact absurd (by omega : K - p ≤ (β d : ℤ)) (this h)
    · have hjd' : j = d := Fin.ext (by omega)
      subst hjd'
      -- at `j = d` the previous index is below the peak time, so `β d ≤ K - p`
      rcases Nat.eq_zero_or_pos j.val with h0 | h0
      · have : β j = 0 := hz j h0
        omega
      · have hnm : j.val - 1 < m := by have := j.isLt; omega
        have hprev := hjmin ⟨j.val - 1, hnm⟩ (by simp; omega)
        have hstep := hlip ⟨j.val - 1, hnm⟩ j (by simp; omega)
        rw [abs_le] at hstep
        push_cast at hprev hstep
        omega
  refine ⟨j, hjd, ?_, ?_⟩
  · have := hβle j
    omega
  · intro k hk
    rcases eq_or_lt_of_le hk with he | hlt'
    · -- `k = j`: the time is exactly the peak time, so the level is at least `K - 1`
      have hkj : k = j := Fin.ext he
      subst hkj
      have hpeak : (β k : ℤ) = K - p := by
        rcases Nat.eq_zero_or_pos k.val with h0 | h0
        · have : β k = 0 := hz k h0
          have := hβle k
          omega
        · have hnm : k.val - 1 < m := by have := k.isLt; omega
          have hprev := hjmin ⟨k.val - 1, hnm⟩ (by simp; omega)
          have hstep := hlip ⟨k.val - 1, hnm⟩ k (by simp; omega)
          rw [abs_le] at hstep
          push_cast at hprev hstep
          omega
      have hck := hcen k
      rw [lamCenter_asc _ _ _ _ (by omega), abs_le] at hck
      omega
    · -- `k < j`: the time is below the peak time, so the leg is ascending
      have hbk : (β k : ℤ) < K - p := by
        by_contra hcon
        exact absurd (by omega : K - p ≤ (β k : ℤ)) (hjmin k hlt')
      have hstep : (β j : ℤ) - (β k : ℤ) ≤ (j.val : ℤ) - (k.val : ℤ) := by
        have key : ∀ t : ℕ, ∀ a b : Fin m, a.val + t = b.val →
            (β b : ℤ) - (β a : ℤ) ≤ (t : ℤ) := by
          intro t
          induction t with
          | zero => intro a b hab; have : a = b := Fin.ext (by omega); subst this; omega
          | succ n ih =>
              intro a b hab
              have hnm : a.val + n < m := by have := b.isLt; omega
              have h1 := ih a ⟨a.val + n, hnm⟩ rfl
              have h2 := hlip ⟨a.val + n, hnm⟩ b (by simp; omega)
              rw [abs_le] at h2
              push_cast at h1 h2 ⊢
              omega
        have := key (j.val - k.val) k j (by omega)
        push_cast at this
        omega
      have hcenk := hcen k
      rw [lamCenter_asc _ _ _ _ (by omega), abs_le] at hcenk
      have hjb : K - p ≤ (β j : ℤ) := hj
      omega

/-- **The exact criterion**, both directions. -/
theorem foldsOnto_lam_iff_profile {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L : ℤ)
    (hLp : L + 2 ≤ p) (h0 : |f ⟨0, hm⟩ - p| ≤ 1) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) :
    FoldsOnto f (lamLen p H L) (lamCenter p H L) ↔ CritLamProfile f p H :=
  ⟨profile_of_foldsOnto_lam f p H L,
    foldsOnto_lam_of_profile hm f hf p H L hLp h0 hL hH⟩

/-- Nothing is lost: on the arms F1 covers — those that start exactly at `p` — the event
criterion `CritLam` implies the profile criterion. -/
theorem critLamProfile_of_critLam {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) (hc : CritLam f p H) :
    CritLamProfile f p H :=
  profile_of_foldsOnto_lam f p H L (foldsOnto_lam_of_crit hm f hf p H L h0 hL hH hc)

/-! ## The reflected criterion, for the V-itinerary -/

/-- The descent profile: the criterion of the reflected arm. -/
def CritVeeProfile {m : ℕ} (f : Fin m → ℤ) (p L : ℤ) : Prop :=
  CritLamProfile (fun j => - f j) (-p) (-L)

/-- **The V-fold.** The mirror of `foldsOnto_lam_iff_profile`: an arm starting within one of `p`
folds onto the V-itinerary — down to the valley `L + 1`, then up to `H - 1` — exactly when the
descent profile holds. -/
theorem foldsOnto_vee_iff_profile {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L : ℤ)
    (hpH : p + 2 ≤ H) (h0 : |f ⟨0, hm⟩ - p| ≤ 1) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H) :
    FoldsOnto f (veeLen p H L) (veeCenter p H L) ↔ CritVeeProfile f p L := by
  have hneg : IsLip (fun j => - f j) := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [abs_le] at this ⊢
    omega
  have key := foldsOnto_lam_iff_profile hm (fun j => - f j) hneg (-p) (-L) (-H)
    (by omega) (by simp only; rw [abs_le] at h0 ⊢; omega)
    (fun j => by simp only; have := hH j; omega) (fun j => by simp only; have := hL j; omega)
  show FoldsOnto f (lamLen (-p) (-L) (-H)) (fun u => - lamCenter (-p) (-L) (-H) u) ↔ _
  rw [foldsOnto_neg]
  exact key

/-- **The descent profile, read off.** Before the arm ever rises to `p + 2` it stands at the
valley level `L + 2` or below, at an index at least `p - L - 1`. -/
theorem critVeeProfile_iff_of_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (p L : ℤ)
    (hLp : L + 1 ≤ p) :
    CritVeeProfile f p L ↔
      ∀ d : Fin m, p + 2 ≤ f d →
        ∃ j : Fin m, j.val < d.val ∧ p - L - 1 ≤ (j.val : ℤ) ∧ f j ≤ L + 2 := by
  have hneg : IsLip (fun j => - f j) := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [abs_le] at this ⊢
    omega
  have hk : κ (-p) (-L) = -(L + 1) := by
    simp only [κ]
    omega
  unfold CritVeeProfile
  rw [critLamProfile_iff_of_isLip hneg, hk]
  constructor
  · intro h d hd
    obtain ⟨j, hj, h1, h2⟩ := h d (by omega)
    exact ⟨j, hj, by omega, by omega⟩
  · intro h d hd
    obtain ⟨j, hj, h1, h2⟩ := h d (by omega)
    exact ⟨j, hj, by omega, by omega⟩

/-! ## What crookedness gives: a crooked arm climbs slowly

The profile criterion asks for a high level at a late enough index, and that is exactly what
crookedness supplies: a crooked arm cannot climb three levels in three steps, nor four levels in
six. This is the information the event vocabulary of the dichotomy does not record. -/

/-- **Three levels need four steps.** -/
theorem crookUp_climb3 {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (hcr : CrookUp f)
    (s t : Fin m) (hst : s.val < t.val) (h3 : f s + 3 ≤ f t) : s.val + 4 ≤ t.val := by
  obtain ⟨u, u', hsu, huu', hu't, hu1, hu2, hu3, hu4⟩ := hcr s t hst h3
  have hdu := abs_sub_le_of_isLip hf (u.val - s.val) s u (by omega)
  have hdt := abs_sub_le_of_isLip hf (t.val - u'.val) u' t (by omega)
  rw [abs_le] at hdu hdt
  have e1 : ((u.val - s.val : ℕ) : ℤ) = (u.val : ℤ) - (s.val : ℤ) := by
    push_cast [Nat.cast_sub (le_of_lt hsu)]; ring
  have e2 : ((t.val - u'.val : ℕ) : ℤ) = (t.val : ℤ) - (u'.val : ℤ) := by
    push_cast [Nat.cast_sub (le_of_lt hu't)]; ring
  omega

/-- **Four levels need seven steps.** -/
theorem crookUp_climb4 {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (hcr : CrookUp f)
    (s t : Fin m) (hst : s.val < t.val) (h4 : f s + 4 ≤ f t) : s.val + 7 ≤ t.val := by
  obtain ⟨u, u', hsu, huu', hu't, hu1, hu2, hu3, hu4⟩ := hcr s t hst (by omega)
  have hdu := abs_sub_le_of_isLip hf (u.val - s.val) s u (by omega)
  rw [abs_le] at hdu
  have e1 : ((u.val - s.val : ℕ) : ℤ) = (u.val : ℤ) - (s.val : ℤ) := by
    push_cast [Nat.cast_sub (le_of_lt hsu)]; ring
  have hrest := crookUp_climb3 hf hcr u' t hu't (by omega)
  omega

/-- **Five levels need twelve steps.** -/
theorem crookUp_climb5 {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (hcr : CrookUp f)
    (s t : Fin m) (hst : s.val < t.val) (h5 : f s + 5 ≤ f t) : s.val + 12 ≤ t.val := by
  obtain ⟨u, u', hsu, huu', hu't, hu1, hu2, hu3, hu4⟩ := hcr s t hst (by omega)
  have hrestu := crookUp_climb3 hf hcr s u hsu (by omega)
  have hrest := crookUp_climb4 hf hcr u' t hu't (by omega)
  omega

/-- **Three levels down need four steps.** -/
theorem crookDown_fall3 {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (hcr : CrookDown f)
    (s t : Fin m) (hst : s.val < t.val) (h3 : f t + 3 ≤ f s) : s.val + 4 ≤ t.val := by
  obtain ⟨u, u', hsu, huu', hu't, hu1, hu2, hu3, hu4⟩ := hcr s t hst h3
  have hdu := abs_sub_le_of_isLip hf (u.val - s.val) s u (by omega)
  have hdt := abs_sub_le_of_isLip hf (t.val - u'.val) u' t (by omega)
  rw [abs_le] at hdu hdt
  have e1 : ((u.val - s.val : ℕ) : ℤ) = (u.val : ℤ) - (s.val : ℤ) := by
    push_cast [Nat.cast_sub (le_of_lt hsu)]; ring
  have e2 : ((t.val - u'.val : ℕ) : ℤ) = (t.val : ℤ) - (u'.val : ℤ) := by
    push_cast [Nat.cast_sub (le_of_lt hu't)]; ring
  omega

/-- **Four levels down need seven steps.** -/
theorem crookDown_fall4 {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) (hcr : CrookDown f)
    (s t : Fin m) (hst : s.val < t.val) (h4 : f t + 4 ≤ f s) : s.val + 7 ≤ t.val := by
  obtain ⟨u, u', hsu, huu', hu't, hu1, hu2, hu3, hu4⟩ := hcr s t hst (by omega)
  have hfirst := crookDown_fall3 hf hcr s u hsu (by omega)
  have hdt := abs_sub_le_of_isLip hf (t.val - u'.val) u' t (by omega)
  rw [abs_le] at hdt
  have e2 : ((t.val - u'.val : ℕ) : ℤ) = (t.val : ℤ) - (u'.val : ℤ) := by
    push_cast [Nat.cast_sub (le_of_lt hu't)]; ring
  omega

/-- **Reaching the ceiling is enough.** For a crooked arm starting at `p + 1` or below, an index
at which the arm stands at `p + 5` is at least `7`, so it witnesses the ascent profile of the
Λ-walk based at `p` with peak `p + 5`: there the index hypothesis costs nothing. (At the level
`p + 4` it is not free: a crooked arm can stand at `p + 4` already at index `4`, and the census
`census-batch42f.c` exhibits arms that then fail to fold.) -/
theorem ascReach_of_top {m : ℕ} {f : Fin m → ℤ} (hm : 0 < m) (hf : IsLip f) (hcr : CrookUp f)
    (p : ℤ) (h0 : f ⟨0, hm⟩ ≤ p + 1) (j : Fin m) (hj : p + 5 ≤ f j) :
    AscReach f p (p + 5) j := by
  have hj0 : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd (show f j = f ⟨0, hm⟩ from by
        rw [show j = ⟨0, hm⟩ from Fin.ext (by omega)]) (by omega)
    · exact h
  have hclimb := crookUp_climb4 hf hcr ⟨0, hm⟩ j (by simpa using hj0) (by omega)
  rw [ascReach_iff_of_isLip hf]
  simp only at hclimb ⊢
  omega

/-! ## The two profiles from a first event

At a band of width six above the base — `H = p + 6`, which is span nine read from the basepoint
`p + 1` — the timing law turns two *announcements* into the two profiles. Announcing the ceiling
`p + 5` before the floor gives the Λ-fold; announcing the floor before the ceiling gives the
V-fold. Neither announcement carries an index, because crookedness supplies it. -/

/-- **The ascent profile from a ceiling announcement.** -/
theorem critLamProfile_of_top_before {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f)
    (hcr : CrookUp f) (p H : ℤ) (hH : H = p + 6) (h0 : f ⟨0, hm⟩ ≤ p + 1)
    (hann : ∀ d : Fin m, f d ≤ p - 2 → ∃ j : Fin m, j.val < d.val ∧ p + 5 ≤ f j) :
    CritLamProfile f p H := by
  intro d hd
  obtain ⟨j, hj, hjv⟩ := hann d hd
  refine ⟨j, hj, ?_⟩
  have hk : κ p H = p + 5 := by
    simp only [κ, hH]
    omega
  rw [hk]
  exact ascReach_of_top hm hf hcr p h0 j hjv

/-- **The descent profile from a floor announcement.** -/
theorem critVeeProfile_of_floor_before {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f)
    (hcr : CrookDown f) (p L : ℤ) (hpL : p = L + 5) (h0 : p - 1 ≤ f ⟨0, hm⟩)
    (hann : ∀ d : Fin m, p + 2 ≤ f d → ∃ j : Fin m, j.val < d.val ∧ f j ≤ L + 1) :
    CritVeeProfile f p L := by
  rw [critVeeProfile_iff_of_isLip hf p L (by omega)]
  intro d hd
  obtain ⟨j, hj, hjv⟩ := hann d hd
  have hj0 : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd (show f j = f ⟨0, hm⟩ from by
        rw [show j = ⟨0, hm⟩ from Fin.ext (by omega)]) (by omega)
    · exact h
  have hfall := crookDown_fall3 hf hcr ⟨0, hm⟩ j (by simpa using hj0) (by omega)
  simp only at hfall
  exact ⟨j, hj, by omega, by omega⟩

/-- **The ascent profile from a ceiling announcement, one band narrower.** Here the peak is
`p + 4`, so the announcement is at `p + 4` and the trigger is a drop to `p - 2`. -/
theorem critLamProfile_of_top_before' {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f)
    (hcr : CrookUp f) (p H : ℤ) (hH : H = p + 5) (h0 : f ⟨0, hm⟩ ≤ p + 1)
    (hann : ∀ d : Fin m, f d ≤ p - 2 → ∃ j : Fin m, j.val < d.val ∧ p + 4 ≤ f j) :
    CritLamProfile f p H := by
  intro d hd
  obtain ⟨j, hj, hjv⟩ := hann d hd
  have hk : κ p H = p + 4 := by
    simp only [κ, hH]
    omega
  have hj0 : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd (show f j = f ⟨0, hm⟩ from by
        rw [show j = ⟨0, hm⟩ from Fin.ext (by omega)]) (by omega)
    · exact h
  have hclimb := crookUp_climb3 hf hcr ⟨0, hm⟩ j (by simpa using hj0) (by omega)
  simp only at hclimb
  refine ⟨j, hj, ?_⟩
  rw [ascReach_iff_of_isLip hf, hk]
  omega

/-- **The descent profile from a floor announcement, one band deeper.** Here the base is
`L + 6`, so the valley time is `5` and the announcement at `L + 1` is four levels down. -/
theorem critVeeProfile_of_floor_before' {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hf : IsLip f)
    (hcr : CrookDown f) (p L : ℤ) (hpL : p = L + 6) (h0 : p - 1 ≤ f ⟨0, hm⟩)
    (hann : ∀ d : Fin m, p + 2 ≤ f d → ∃ j : Fin m, j.val < d.val ∧ f j ≤ L + 1) :
    CritVeeProfile f p L := by
  rw [critVeeProfile_iff_of_isLip hf p L (by omega)]
  intro d hd
  obtain ⟨j, hj, hjv⟩ := hann d hd
  have hj0 : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd (show f j = f ⟨0, hm⟩ from by
        rw [show j = ⟨0, hm⟩ from Fin.ext (by omega)]) (by omega)
    · exact h
  have hfall := crookDown_fall4 hf hcr ⟨0, hm⟩ j (by simpa using hj0) (by omega)
  simp only at hfall
  exact ⟨j, hj, by omega, by omega⟩

/-! ## The interface to `S3` -/

/-- If both arms of a basepoint satisfy the ascent-profile criterion at one base `p` within one
of the basepoint's level, the basepoint is served: the two arms fold onto the one Λ-walk based
at `p`. -/
theorem exists_folds_of_profile {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L p : ℤ)
    (hlip : IsLip ρ) (hLp : L + 2 ≤ p) (h0 : |ρ i - p| ≤ 1)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hG : CritLamProfile (armG ρ i) p H) (hT : CritLamProfile (armT ρ i) p H) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by simp [armG]
  have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by simp [armT]
  refine ⟨lamLen p H L, lamCenter p H L, ?_, ?_⟩
  · exact foldsOnto_lam_of_profile hmG _ (armG_isLip hlip i) p H L hLp (by rw [hG0]; exact h0)
      (fun j => hLb _) (fun j => hHb _) hG
  · exact foldsOnto_lam_of_profile hmT _ (armT_isLip hlip i) p H L hLp (by rw [hT0]; exact h0)
      (fun j => hLb _) (fun j => hHb _) hT

/-- The V-mirror of `exists_folds_of_profile`. -/
theorem exists_folds_of_veeProfile {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L p : ℤ)
    (hlip : IsLip ρ) (hpH : p + 2 ≤ H) (h0 : |ρ i - p| ≤ 1)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hG : CritVeeProfile (armG ρ i) p L) (hT : CritVeeProfile (armT ρ i) p L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by simp [armG]
  have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by simp [armT]
  refine ⟨veeLen p H L, veeCenter p H L, ?_, ?_⟩
  · exact (foldsOnto_vee_iff_profile hmG _ (armG_isLip hlip i) p H L hpH
      (by rw [hG0]; exact h0) (fun j => hLb _) (fun j => hHb _)).mpr hG
  · exact (foldsOnto_vee_iff_profile hmT _ (armT_isLip hlip i) p H L hpH
      (by rw [hT0]; exact h0) (fun j => hLb _) (fun j => hHb _)).mpr hT

end HPC.Fold
