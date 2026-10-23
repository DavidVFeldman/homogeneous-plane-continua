import HPC.Fold.Exits

/-!
# A crooked arm cannot climb monotonically, and what that buys

A crooked sequence that rises three or more levels must contain a non-ascending step on the
way, because crookedness demands a reversal between the two endpoints. Hence its `phase` is
already `1` when it peaks, and the phase's spare unit lets an arm whose demand falls one short
of `hStar` still reach `hStar` in the phase-adjusted sense.

This is what closes the case the previous batches left open: the two arms' demands need not be
equal, only within one.

`Agreement` is recorded as a definition, not proved.

English proofs: COMMISSION.md §3.
-/

namespace HPC.Fold

variable {m : ℕ} {A : Fin m → ℤ}

/-- Step extraction: if no index of `(a, a + k]` carries a non-ascending step, then the
sequence climbs by at least one level at each of those `k` steps. -/
private theorem climb_of_no_nonAsc (A : Fin m → ℤ) (a : ℕ) (ha : a < m) :
    ∀ (k : ℕ) (hk : a + k < m),
      (∀ t : Fin m, a < t.val → t.val ≤ a + k → ¬ NonAscAt A t) →
      A ⟨a, ha⟩ + k ≤ A ⟨a + k, hk⟩ := by
  intro k
  induction k with
  | zero => intro hk _; simp
  | succ k ih =>
      intro hk hno
      have hk' : a + k < m := by omega
      have h1 : A ⟨a, ha⟩ + k ≤ A ⟨a + k, hk'⟩ :=
        ih hk' fun t h1 h2 => hno t h1 (by omega)
      have h2 : ¬ NonAscAt A ⟨a + (k + 1), hk⟩ :=
        hno _ (show a < a + (k + 1) by omega) le_rfl
      have h3 : A ⟨a + k, hk'⟩ < A ⟨a + (k + 1), hk⟩ := by
        by_contra hcon
        refine h2 ⟨show 0 < a + (k + 1) by omega, fun t' ht' => ?_⟩
        have ht'val : t'.val + 1 = a + (k + 1) := ht'
        have ht'eq : t' = (⟨a + k, hk'⟩ : Fin m) := Fin.ext (show t'.val = a + k by omega)
        rw [ht'eq]
        omega
      push_cast
      omega

/-- **The Phase Lemma.** If a crooked sequence rises by three or more from index `0` to index
`j`, some index at or before `j` is a non-ascending step. -/
theorem exists_nonAsc_of_climb (hc : IsCrookedSeq A) (hm : 0 < m) (p : ℤ)
    (h0 : A ⟨0, hm⟩ = p) (j : Fin m) (hj : p + 3 ≤ A j) :
    ∃ t : Fin m, t ≤ j ∧ NonAscAt A t := by
  have hjpos : 0 < j.val := by
    by_contra hcon
    have : j = (⟨0, hm⟩ : Fin m) := Fin.ext (show j.val = 0 by omega)
    rw [this, h0] at hj
    omega
  have hlt : (⟨0, hm⟩ : Fin m) < j := Fin.lt_def.2 (by simpa using hjpos)
  have habs : 3 ≤ |A j - A ⟨0, hm⟩| := by
    rw [h0, abs_of_nonneg (by omega : (0:ℤ) ≤ A j - p)]
    omega
  obtain ⟨r, r', h1, h2, h3, hasc, -⟩ := hc ⟨0, hm⟩ j hlt habs
  obtain ⟨⟨hr1, -⟩, ⟨-, hr'2⟩⟩ := hasc (by rw [h0]; omega)
  rw [h0] at hr'2
  by_contra hcon
  push_neg at hcon
  have hno : ∀ t : Fin m, r.val < t.val → t.val ≤ r'.val → ¬ NonAscAt A t := by
    intro t ht1 ht2 hNA
    exact hcon t (Fin.le_def.2 (by have := Fin.lt_def.1 h3; omega)) hNA
  have hrr' : r.val < r'.val := Fin.lt_def.1 h2
  have hkey := climb_of_no_nonAsc A r.val r.isLt (r'.val - r.val)
    (by omega) (fun t ht1 ht2 => hno t ht1 (by omega))
  have hre : (⟨r.val + (r'.val - r.val), by omega⟩ : Fin m) = r' :=
    Fin.ext (show r.val + (r'.val - r.val) = r'.val by omega)
  rw [hre] at hkey
  have hrr : (⟨r.val, r.isLt⟩ : Fin m) = r := Fin.ext rfl
  rw [hrr] at hkey
  have : (1 : ℤ) ≤ ((r'.val - r.val : ℕ) : ℤ) := by
    have : 1 ≤ r'.val - r.val := by omega
    exact_mod_cast this
  omega

/-- Hence the phase is `1` at any index where the sequence stands three or more above its
start. -/
theorem phase_eq_one_of_climb (hc : IsCrookedSeq A) (hm : 0 < m) (p : ℤ)
    (h0 : A ⟨0, hm⟩ = p) (j : Fin m) (hj : p + 3 ≤ A j) :
    phase A j = 1 := by
  obtain ⟨t, ht, hNA⟩ := exists_nonAsc_of_climb hc hm p h0 j hj
  exact phase_eq_one A j ⟨t, Fin.le_def.1 ht, hNA⟩

/-- **The one-short lemma.** An arm whose demand is at least `h − 1`, and whose demand is at
least `p + 3`, reaches `h` in the phase-adjusted sense at or before its first drop. -/
theorem exists_peak_index_of_one_short (hc : IsCrookedSeq A) (hm : 0 < m) (p h : ℤ)
    (h0 : A ⟨0, hm⟩ = p) (hdem : h - 1 ≤ hStarArm A p) (hhigh : p + 3 ≤ hStarArm A p) :
    ∃ s : Fin m, h ≤ A s + phase A s ∧ ∀ j : Fin m, j ≤ s → p - 1 ≤ A j := by
  obtain ⟨s, hs, hpre⟩ := hStarArm_mem hm A p h0
  refine ⟨s, ?_, hpre⟩
  have hph : phase A s = 1 :=
    phase_eq_one_of_climb hc hm p h0 s (by rw [hs]; exact hhigh)
  rw [hph, hs]
  omega

/-- The complementary small case: if the demand is below `p + 3`, the arm never rises far, and
the whole window argument is finite. Recorded as the residual obligation. -/
def SmallDemandCase : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    hStar ρ i H L ≤ ρ i + 3 →
      (SegLam (armG ρ i) (ρ i) H L (hStar ρ i H L) ∧
       SegLam (armT ρ i) (ρ i) H L (hStar ρ i H L)) ∨
      (SegVee (armG ρ i) (ρ i) H L (lStar ρ i H L) ∧
       SegVee (armT ρ i) (ρ i) H L (lStar ρ i H L))

/-- **Agreement.** For a crooked sequence and any basepoint, the two arms' peak demands differ
by at most one, or their valley demands do.

Verified on 10 109 166 basepoints: every crooked 1-Lipschitz sequence of length at most 13 on
six levels, and random crooked sequences to length 90. The gap `min (|Δh|, |Δl|)` was `0` in
7 617 820 cases and `1` in 2 491 346; never `2` or more.

This supersedes `Exclusion` and `Balance` of batch 10 as the central conjecture: it is the
statement the whole dichotomy needs, and it mentions neither itineraries nor exits. -/
def Agreement : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n), IsLip ρ → IsCrookedSeq ρ →
    |hStarArm (armG ρ i) (ρ i) - hStarArm (armT ρ i) (ρ i)| ≤ 1 ∨
    |lStarArm (armG ρ i) (ρ i) - lStarArm (armT ρ i) (ρ i)| ≤ 1

end HPC.Fold
