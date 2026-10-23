import HPC.Fold.Faithful

/-!
# The three conjectures, over the faithful model

`IsCrookedIvF` (batch 22) is, by two theorems, exactly the class of `(minIdx, maxIdx)` pairs
of chains crooked in the 1948 sense. The batch-16 route is restated over it here and its three
hypotheses posed as theorems to find. Search permitted, as in batches 18–19.

A counterexample to any of the three is a success and is to be reported first. By
`realization` it is a chain, so it refutes a statement about Bing's objects — the first such
refutation this project would have produced, all earlier ones having been about sequences
outside the class.

English sketches: COMMISSION.md §3. Delivered complete: no `sorry` remains.

## What this batch found

**All three conjectures are false over the faithful model, and so is `F2PrimeF`.**
`ExitReachFWitness.lean` exhibits a forty-two term member of the model at which both
disjuncts of `ExitReachF` fail, and at which `F2PrimeF` fails as well;
`ValleyFWitness.lean` exhibits a seventy-one term member refuting `HighExitValleyF` and
`LowExitPeakF`. By `realization` these are `(minIdx, maxIdx)` pairs of actual chains, so the
batch-16 route is refuted at genuine chains and not merely at sequences outside the class.

The three theorems to find, and the two corollaries that depended on them, are therefore kept
below only as commented-out statements, with the refutations named in their place.
-/

namespace HPC.Fold

/-! ## Statements -/

def ExitReachF : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
      (OkLam (armG ρ i) (ρ i) (hStar ρ i H L) ∧ OkLam (armT ρ i) (ρ i) (hStar ρ i H L)) ∨
      (OkVee (armG ρ i) (ρ i) (lStar ρ i H L) ∧ OkVee (armT ρ i) (ρ i) (lStar ρ i H L))

def HighExitValleyF : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        armG ρ i j + phase (armG ρ i) j < hStar ρ i H L) →
      ValleyBefore (armG ρ i) L (hStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        armT ρ i j + phase (armT ρ i) j < hStar ρ i H L) →
      ValleyBefore (armT ρ i) L (hStar ρ i H L) s)

def LowExitPeakF : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        - armG ρ i j + phase (fun j => - armG ρ i j) j < - lStar ρ i H L) →
      ValleyBefore (fun j => - armG ρ i j) (-H) (- lStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        - armT ρ i j + phase (fun j => - armT ρ i j) j < - lStar ρ i H L) →
      ValleyBefore (fun j => - armT ρ i j) (-H) (- lStar ρ i H L) s)

/-- The batch-16 assembly, over the faithful model. The crookedness hypothesis is only passed
through to the three inputs, so the batch-20 proof transfers verbatim. -/
theorem f2PrimeF_of_exitReachF (h1 : ExitReachF) (h2 : HighExitValleyF)
    (h3 : LowExitPeakF) : F2PrimeF := by
  intro n ρ σ i H L hlip hcr hL hH hLH hattL hattH
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := Nat.succ_pos _
  have h0G : armG ρ i ⟨0, hmG⟩ = ρ i := congrArg ρ (Fin.ext (by simp))
  have h0T : armT ρ i ⟨0, hmT⟩ = ρ i := congrArg ρ (Fin.ext (by simp))
  have hLG : ∀ j, L ≤ armG ρ i j := fun j => hL _
  have hLT : ∀ j, L ≤ armT ρ i j := fun j => hL _
  have hHG : ∀ j, armG ρ i j ≤ H := fun j => hH _
  have hHT : ∀ j, armT ρ i j ≤ H := fun j => hH _
  rcases h1 n ρ σ i H L hlip hcr hL hH hLH hattL hattH with ⟨hokG, hokT⟩ | ⟨hokG, hokT⟩
  · obtain ⟨hvG, hvT⟩ := h2 n ρ σ i H L hlip hcr hL hH hLH hattL hattH
    refine Or.inl ⟨?_, ?_⟩
    · exact segLam_of_okLam hmG (ρ i) H L _ (armG_isLip hlip i) h0G hLG hHG
        (le_hStar ρ i H L) (hStar_dem_armG ρ i H L) hokG hvG
    · exact segLam_of_okLam hmT (ρ i) H L _ (armT_isLip hlip i) h0T hLT hHT
        (le_hStar ρ i H L) (hStar_dem_armT ρ i H L) hokT hvT
  · obtain ⟨hvG, hvT⟩ := h3 n ρ σ i H L hlip hcr hL hH hLH hattL hattH
    have hnegG : IsLip (fun j => - armG ρ i j) := by
      intro j j' hjj'
      have := armG_isLip hlip i j j' hjj'
      simp only [abs_le] at this ⊢
      omega
    have hnegT : IsLip (fun j => - armT ρ i j) := by
      intro j j' hjj'
      have := armT_isLip hlip i j j' hjj'
      simp only [abs_le] at this ⊢
      omega
    have hdemG : hStarArm (fun j => - armG ρ i j) (- ρ i) ≤ - lStar ρ i H L ∨
        (-L) - 1 ≤ - lStar ρ i H L := by
      have := lStar_dem_armG ρ i H L
      simp only [lStarArm] at this
      omega
    have hdemT : hStarArm (fun j => - armT ρ i j) (- ρ i) ≤ - lStar ρ i H L ∨
        (-L) - 1 ≤ - lStar ρ i H L := by
      have := lStar_dem_armT ρ i H L
      simp only [lStarArm] at this
      omega
    refine Or.inr ⟨?_, ?_⟩
    · exact segLam_of_okLam hmG (- ρ i) (-L) (-H) _ hnegG (by rw [h0G])
        (fun j => by have := hHG j; omega)
        (fun j => by have := hLG j; omega)
        (by have := lStar_le ρ i H L; omega) hdemG hokG hvG
    · exact segLam_of_okLam hmT (- ρ i) (-L) (-H) _ hnegT (by rw [h0T])
        (fun j => by have := hHT j; omega)
        (fun j => by have := hLT j; omega)
        (by have := lStar_le ρ i H L; omega) hdemT hokT hvT

/-! ## A lemma the sketches want: both crookedness forms on one sequence -/

/-- The upper index sequence obeys the up form of batch 13.

The crookedness clause of the faithful model is instantiated at `h := σ s`, `k := σ t`, with
the forced-meeting witnesses `u := s` and `u := t`; the width bound `σ r ≤ ρ r + 1` then reads
the two conclusions `ρ r ≤ k ∓ 1 ≤ σ r` as the up-form windows. -/
theorem IsCrookedIvF.isCrookedSeqUp {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvF ρ σ) :
    IsCrookedSeqUp σ := by
  intro s t hst habs
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
    h.crooked s t hst (σ s) (σ t) ⟨s, by simp, h.le s, le_rfl⟩ ⟨t, by simp, h.le t, le_rfl⟩
      (by rw [abs_sub_comm]; exact habs)
  refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
  · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hasc hlt
    have := h.width r
    have := h.width r'
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hdesc hlt
    have := h.width r
    have := h.width r'
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-! ## A cheaper decidable criterion for membership in the faithful model

`IsCrookedIvFCheck` (batch 22) quantifies the two meeting indices over all of `Fin n`, so
deciding it on concrete data costs `n²` per pair of indices. The forced meetings only ever
involve the two neighbours, so quantifying over the three offsets `−1, 0, +1` — clamped into
range, which at the ends repeats the index itself — is enough, and costs nine per pair. -/

/-- The index `s + d`, clamped into `Fin n`. -/
def clampIdx {n : ℕ} (s : Fin n) (d : ℤ) : Fin n :=
  ⟨min (((s.val : ℤ) + d).toNat) (n - 1), by have := s.isLt; omega⟩

/-- Every index within one of `s` is `s` shifted by one of the three clamped offsets. -/
theorem exists_clampIdx {n : ℕ} {s u : Fin n} (h : ((u : ℤ) - (s : ℤ)).natAbs ≤ 1) :
    ∃ d : Fin 3, u = clampIdx s ((d.val : ℤ) - 1) := by
  have hs := s.isLt
  have hu := u.isLt
  have hcase : u.val + 1 = s.val ∨ u.val = s.val ∨ u.val = s.val + 1 := by omega
  rcases hcase with hc | hc | hc
  · exact ⟨0, Fin.ext (by simp only [clampIdx]; omega)⟩
  · exact ⟨1, Fin.ext (by simp only [clampIdx]; omega)⟩
  · exact ⟨2, Fin.ext (by simp only [clampIdx]; omega)⟩

/-- The least index strictly between `lo` and `hi` whose interval contains the level `a`. -/
def findMeet {n : ℕ} (ρ σ : Fin n → ℤ) (lo hi : ℕ) (a : ℤ) : Option (Fin n) :=
  (List.finRange n).find?
    (fun r => lo < r.val && r.val < hi && decide (ρ r ≤ a) && decide (a ≤ σ r))

theorem findMeet_spec {n : ℕ} {ρ σ : Fin n → ℤ} {lo hi : ℕ} {a : ℤ} {r : Fin n}
    (h : findMeet ρ σ lo hi a = some r) : lo < r.val ∧ r.val < hi ∧ ρ r ≤ a ∧ a ≤ σ r := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- A link meeting `a` strictly between `s` and `t`, followed by a later one meeting `b`. -/
def meetPair {n : ℕ} (ρ σ : Fin n → ℤ) (s t : Fin n) (a b : ℤ) : Bool :=
  match findMeet ρ σ s.val t.val a with
  | none => false
  | some r => (findMeet ρ σ r.val t.val b).isSome

theorem meetPair_spec {n : ℕ} {ρ σ : Fin n → ℤ} {s t : Fin n} {a b : ℤ}
    (h : meetPair ρ σ s t a b = true) :
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧ (ρ r ≤ a ∧ a ≤ σ r) ∧ (ρ r' ≤ b ∧ b ≤ σ r') := by
  unfold meetPair at h
  cases hr : findMeet ρ σ s.val t.val a with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some r =>
    rw [hr] at h
    simp only at h
    obtain ⟨hs, ht, ha1, ha2⟩ := findMeet_spec hr
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hs', ht', hb1, hb2⟩ := findMeet_spec hr'
    exact ⟨r, r', Fin.lt_def.2 hs, Fin.lt_def.2 hs', Fin.lt_def.2 ht', ⟨ha1, ha2⟩, hb1, hb2⟩

/-- The cheap decidable form of `IsCrookedIvF`: the meeting indices are quantified over the
three clamped offsets rather than over all of `Fin n`, and the two intermediate links are
produced by `meetPair` instead of being searched for by an existential. -/
def IsCrookedIvFCheck2 {n : ℕ} (ρ σ : Fin n → ℤ) : Prop :=
  (∀ t, ρ t ≤ σ t) ∧ (∀ t, σ t ≤ ρ t + 1) ∧
  (∀ t t' : Fin n, t'.val = t.val + 1 → max (σ t) (σ t') ≤ min (ρ t) (ρ t') + 1) ∧
  (∀ s t : Fin n, s < t → ∀ du dv : Fin 3, ∀ b b' : Bool,
    3 ≤ |ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) -
         ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1))| →
      (if ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) <
          ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) then
        meetPair ρ σ s t (ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) - 1)
          (ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) + 1)
      else
        meetPair ρ σ s t (ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) + 1)
          (ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) - 1)) = true)

/-- The cheap criterion suffices. -/
theorem isCrookedIvF_of_check2 {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvFCheck2 ρ σ) :
    IsCrookedIvF ρ σ := by
  obtain ⟨hle, hw, hadj, hcr⟩ := h
  have hf0 : ∀ w : Fin n, ivEnd ρ σ false w = ρ w := fun _ => rfl
  have hf1 : ∀ w : Fin n, ivEnd ρ σ true w = σ w := fun _ => rfl
  have key : ∀ (s t : Fin n), s < t → ∀ (du dv : Fin 3) (b b' : Bool),
      3 ≤ |ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) -
           ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1))| →
      ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
        (ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) <
            ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) →
          (ρ r ≤ ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) - 1 ∧
            ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) - 1 ≤ σ r) ∧
          (ρ r' ≤ ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) + 1 ∧
            ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) + 1 ≤ σ r')) ∧
        (ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) <
            ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) →
          (ρ r ≤ ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) + 1 ∧
            ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1)) + 1 ≤ σ r) ∧
          (ρ r' ≤ ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) - 1 ∧
            ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) - 1 ≤ σ r')) := by
    intro s t hst du dv b b' habs
    have hb := hcr s t hst du dv b b' habs
    by_cases hlt : ivEnd ρ σ b (clampIdx s ((du.val : ℤ) - 1)) <
        ivEnd ρ σ b' (clampIdx t ((dv.val : ℤ) - 1))
    · rw [if_pos hlt] at hb
      obtain ⟨r, r', h1, h2, h3, ha, hbb⟩ := meetPair_spec hb
      exact ⟨r, r', h1, h2, h3, fun _ => ⟨ha, hbb⟩, fun hcon => absurd hcon (by omega)⟩
    · rw [if_neg hlt] at hb
      obtain ⟨r, r', h1, h2, h3, ha, hbb⟩ := meetPair_spec hb
      exact ⟨r, r', h1, h2, h3, fun hcon => absurd hcon hlt, fun _ => ⟨ha, hbb⟩⟩
  refine ⟨hle, hw, hadj, ?_⟩
  rintro s t hst hh kk ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
  obtain ⟨du, rfl⟩ := exists_clampIdx hu
  obtain ⟨dv, rfl⟩ := exists_clampIdx hv
  have hbu : hh = ivEnd ρ σ false (clampIdx s ((du.val : ℤ) - 1)) ∨
      hh = ivEnd ρ σ true (clampIdx s ((du.val : ℤ) - 1)) := by
    rw [hf0, hf1]
    have := hw (clampIdx s ((du.val : ℤ) - 1))
    omega
  have hbv : kk = ivEnd ρ σ false (clampIdx t ((dv.val : ℤ) - 1)) ∨
      kk = ivEnd ρ σ true (clampIdx t ((dv.val : ℤ) - 1)) := by
    rw [hf0, hf1]
    have := hw (clampIdx t ((dv.val : ℤ) - 1))
    omega
  rcases hbu with e | e <;> rcases hbv with e' | e' <;> subst e <;> subst e'
  · exact key s t hst du dv false false habs
  · exact key s t hst du dv false true habs
  · exact key s t hst du dv true false habs
  · exact key s t hst du dv true true habs

/-! ## The combined Synchronization Lemma

A single sequence in the faithful model carries the down form on `ρ` and the up form on `σ`,
and one instance of the faithful crookedness clause delivers both pinnings at once: across an
exit at `p + 2` and one at `p − 2` with the window intact — `p − 1 ≤ ρ` below and `σ ≤ p + 1`
above — there is a link whose lower end is exactly `p − 1` followed by one whose upper end is
exactly `p + 1`, or, in the ascending direction, the reverse. -/

/-- **The combined Synchronization Lemma**, descending form. -/
theorem IsCrookedIvF.sync_comb {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (p : ℤ)
    {u v : Fin n} (huv : u < v) (hu : ρ u = p + 2) (hv : ρ v = p - 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ ρ w ∧ σ w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ ρ j = p - 1 ∧ σ k = p + 1 := by
  have hlu := hf.le u
  have hlv := hf.le v
  obtain ⟨r, r', h1, h2, h3, -, hdesc⟩ :=
    hf.crooked u v huv (p + 2) (p - 2) ⟨u, by simp, by omega, by omega⟩
      ⟨v, by simp, by omega, by omega⟩
      (by rw [show p + 2 - (p - 2) = (4 : ℤ) by ring]; norm_num)
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hdesc (by omega)
  obtain ⟨hr1, -⟩ := hmid r h1 (h2.trans h3)
  obtain ⟨-, hr'2⟩ := hmid r' (h1.trans h2) h3
  exact ⟨r, r', h1, h2, h3, by omega, by omega⟩

/-- **The combined Synchronization Lemma**, ascending form. -/
theorem IsCrookedIvF.sync_comb' {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (p : ℤ)
    {u v : Fin n} (huv : u < v) (hu : ρ u = p - 2) (hv : ρ v = p + 2)
    (hmid : ∀ w : Fin n, u < w → w < v → p - 1 ≤ ρ w ∧ σ w ≤ p + 1) :
    ∃ j k : Fin n, u < j ∧ j < k ∧ k < v ∧ σ j = p + 1 ∧ ρ k = p - 1 := by
  have hlu := hf.le u
  have hlv := hf.le v
  obtain ⟨r, r', h1, h2, h3, hasc, -⟩ :=
    hf.crooked u v huv (p - 2) (p + 2) ⟨u, by simp, by omega, by omega⟩
      ⟨v, by simp, by omega, by omega⟩
      (by rw [show p - 2 - (p + 2) = (-4 : ℤ) by ring]; norm_num)
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hasc (by omega)
  obtain ⟨-, hr2⟩ := hmid r h1 (h2.trans h3)
  obtain ⟨hr'1, -⟩ := hmid r' (h1.trans h2) h3
  exact ⟨r, r', h1, h2, h3, by omega, by omega⟩

/-! ## The arms of a crooked sequence are crooked -/

/-- The forward arm inherits the down form: the two witnesses of a pair of arm indices lie
between them, hence in the arm. -/
theorem isCrookedSeq_armG {n : ℕ} {ρ : Fin n → ℤ} (hc : IsCrookedSeq ρ) (i : Fin n) :
    IsCrookedSeq (armG ρ i) := by
  intro s t hst habs
  have hi := i.isLt
  have hs := s.isLt
  have ht := t.isLt
  have hstv : s.val < t.val := hst
  have hS : (⟨i.val + s.val, by omega⟩ : Fin n) < ⟨i.val + t.val, by omega⟩ := by
    simp only [Fin.lt_def]; omega
  have hSv : armG ρ i s = ρ ⟨i.val + s.val, by omega⟩ := rfl
  have hTv : armG ρ i t = ρ ⟨i.val + t.val, by omega⟩ := rfl
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
    hc ⟨i.val + s.val, by omega⟩ ⟨i.val + t.val, by omega⟩ hS (by rw [← hSv, ← hTv]; exact habs)
  have h1v : i.val + s.val < r.val := h1
  have h2v : r.val < r'.val := h2
  have h3v : r'.val < i.val + t.val := h3
  have hrlt := r.isLt
  have hr'lt := r'.isLt
  have hRv : armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r :=
    congrArg ρ (Fin.ext (by simp only; omega))
  have hR'v : armG ρ i ⟨r'.val - i.val, by omega⟩ = ρ r' :=
    congrArg ρ (Fin.ext (by simp only; omega))
  refine ⟨⟨r.val - i.val, by omega⟩, ⟨r'.val - i.val, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fin.lt_def]; omega
  · simp only [Fin.lt_def]; omega
  · simp only [Fin.lt_def]; omega
  · intro hlt
    rw [hRv, hR'v]
    rw [hSv, hTv] at hlt ⊢
    obtain ⟨e1, e2⟩ := hasc hlt
    exact ⟨e1, e2⟩
  · intro hlt
    rw [hRv, hR'v]
    rw [hSv, hTv] at hlt ⊢
    obtain ⟨e1, e2⟩ := hdesc hlt
    exact ⟨e1, e2⟩

/-- The backward arm inherits the down form as well: reading the pair in the original order
exchanges the two witnesses and the two cases, and the bounds match. -/
theorem isCrookedSeq_armT {n : ℕ} {ρ : Fin n → ℤ} (hc : IsCrookedSeq ρ) (i : Fin n) :
    IsCrookedSeq (armT ρ i) := by
  intro s t hst habs
  have hi := i.isLt
  have hs := s.isLt
  have ht := t.isLt
  have hstv : s.val < t.val := hst
  have hS : (⟨i.val - t.val, by omega⟩ : Fin n) < ⟨i.val - s.val, by omega⟩ := by
    simp only [Fin.lt_def]; omega
  have hSv : armT ρ i t = ρ ⟨i.val - t.val, by omega⟩ := rfl
  have hTv : armT ρ i s = ρ ⟨i.val - s.val, by omega⟩ := rfl
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
    hc ⟨i.val - t.val, by omega⟩ ⟨i.val - s.val, by omega⟩ hS
      (by rw [← hSv, ← hTv, abs_sub_comm]; exact habs)
  have h1v : i.val - t.val < r.val := h1
  have h2v : r.val < r'.val := h2
  have h3v : r'.val < i.val - s.val := h3
  have hrlt := r.isLt
  have hr'lt := r'.isLt
  have hRv : armT ρ i ⟨i.val - r'.val, by omega⟩ = ρ r' :=
    congrArg ρ (Fin.ext (by simp only; omega))
  have hR'v : armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r :=
    congrArg ρ (Fin.ext (by simp only; omega))
  refine ⟨⟨i.val - r'.val, by omega⟩, ⟨i.val - r.val, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fin.lt_def]; omega
  · simp only [Fin.lt_def]; omega
  · simp only [Fin.lt_def]; omega
  · intro hlt
    rw [hRv, hR'v]
    rw [hSv, hTv] at hlt ⊢
    obtain ⟨e1, e2⟩ := hdesc (by omega)
    omega
  · intro hlt
    rw [hRv, hR'v]
    rw [hSv, hTv] at hlt ⊢
    obtain ⟨e1, e2⟩ := hasc (by omega)
    omega

/-! ## The valley clause, reduced to a visit at the global minimum -/

/-- **The mechanism of the `HighExitValleyF` sketch.** If the arm attains the ambient minimum
`L` before every index at which it exceeds `h + 1`, then the valley clause holds at every `s`
passing the peak-index test.

Crookedness on the pair `(l, u)` — an index carrying `L` and one carrying at least `h + 2`,
so a gap of at least three — puts a near-target witness `r` at level at least `h`, which
forces `s ≤ r` because every index before `s` has phase-adjusted level below `h`; the
near-source witness `r'` that follows it is at `L + 1` or below, and that is the visit. -/
theorem valleyBefore_of_attains_min {m : ℕ} {A : Fin m → ℤ} (hc : IsCrookedSeq A) (L h : ℤ)
    (hLh : L + 1 ≤ h) (s : ℕ)
    (hs : ∀ j : Fin m, j.val < s → A j + phase A j < h)
    (hmin : ∀ u : Fin m, h + 1 < A u → ∃ l : Fin m, l < u ∧ A l = L) :
    ValleyBefore A L h s := by
  intro u hsu hu
  obtain ⟨l, hlu, hlL⟩ := hmin u hu
  have habs : 3 ≤ |A u - A l| := by
    rw [hlL, abs_of_nonneg (by omega : (0 : ℤ) ≤ A u - L)]
    omega
  obtain ⟨r, r', h1, h2, h3, hasc, -⟩ := hc l u hlu habs
  obtain ⟨⟨e1, -⟩, ⟨-, e4⟩⟩ := hasc (by omega)
  have hsr : s ≤ r.val := by
    by_contra hcon
    have := hs r (by omega)
    rcases phase_zero_or_one A r with hp | hp <;> omega
  have h2v : r.val < r'.val := h2
  have h3v : r'.val < u.val := h3
  exact ⟨r', by omega, by omega, by omega⟩

/-- The sub-claim of the batch-19 mechanism, over the faithful model: an arm that exceeds
`hStar + 1` has attained the ambient minimum `L` earlier on the same arm.

`highExitValleyF_of_attainsMin` shows this is all that `HighExitValleyF` needs. It is
**false** over the faithful model: `not_attainsMinBeforeExceedF` in `ClosureFWitness.lean`
refutes it at a thirty-term chain — a chain at which `HighExitValleyF` itself still holds, so
what fails there is the mechanism and not the conjecture. (Once `HighExitValleyF` is known to
be false the sub-claim is refuted by the reduction as well, but only the thirty-term witness
separates the two.) -/
def AttainsMinBeforeExceedF : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    (∀ u : Fin (n - i.val), hStar ρ i H L + 1 < armG ρ i u →
      ∃ l : Fin (n - i.val), l < u ∧ armG ρ i l = L) ∧
    (∀ u : Fin (i.val + 1), hStar ρ i H L + 1 < armT ρ i u →
      ∃ l : Fin (i.val + 1), l < u ∧ armT ρ i l = L)

/-- `L + 1` never exceeds the bump height, once the range is at least three. -/
theorem le_hStar_of_range {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) (hLH : L + 3 ≤ H) :
    L + 1 ≤ hStar ρ i H L := by
  simp only [hStar, le_min_iff, le_max_iff]
  omega

/-- **`HighExitValleyF` follows from the sub-claim.** -/
theorem highExitValleyF_of_attainsMin (h : AttainsMinBeforeExceedF) : HighExitValleyF := by
  intro n ρ σ i H L hlip hcr hL hH hLH hattL hattH
  obtain ⟨hG, hT⟩ := h n ρ σ i H L hlip hcr hL hH hLH hattL hattH
  have hseq : IsCrookedSeq ρ := hcr.isCrookedIv.isCrookedSeq
  have hLh : L + 1 ≤ hStar ρ i H L := le_hStar_of_range ρ i H L hLH
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · exact valleyBefore_of_attains_min (isCrookedSeq_armG hseq i) L _ hLh s hs hG
  · exact valleyBefore_of_attains_min (isCrookedSeq_armT hseq i) L _ hLh s hs hT

-- Commented-out statement `exitReachF`, `highExitValleyF`, `lowExitPeakF` removed in batch 103; see `LEDGER.md`.

-- Commented-out statement `f2PrimeF`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
