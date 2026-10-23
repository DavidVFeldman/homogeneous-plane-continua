import HPC.Fold.Dichotomy

/-!
# `S3`: the folding statement with the itinerary existentially quantified

Ten formulations of the folding dichotomy have named a family of itineraries in advance and
been refuted. The reason is measurable. For each basepoint of Bing's chains, let `k` be the
least number of turning targets in an itinerary onto which both arms fold; the maximum of `k`
over basepoints is `⌊span/2⌋ − 1`, exactly, for spans 4 through 10. The one-bump family of
batch 24 is the case `k = 3`, which is why `F2PrimeOff` holds through span 9 and fails at span
10 — at eight basepoints of `bing 0 10`, all at level 5, where the least itinerary has four
turning targets and two of them are interior levels, not extremes.

So no family with a bounded number of turning points can witness Theorem 3, and this file
states the target with the itinerary existentially quantified. `exists_blocks_first_of_folds`
(batch 6) already accepts an arbitrary `len` and `c`, so `theorem3_of_S3` is immediate.

English sketch: COMMISSION.md §4. Delivered: every ordinary item is proved, together with
`s3_near_extreme` and the cut lemmas the inductive step rests on; `s3` itself is neither proved
nor refuted, and is kept, commented out, at the end. No `sorry` remains outside that block.
-/

namespace HPC.Fold

/-- **`S3`.** From any basepoint of a faithful crooked sequence with attained extremes, both
arms fold onto a common itinerary. No shape, length or turning count is prescribed. -/
def S3 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, conditional on `S3`. -/
theorem theorem3_of_S3 (hS3 : S3) {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  set σ : Fin n → ℤ := fun t => ((href.maxIdx t : ℕ) : ℤ) with hσ
  obtain ⟨tL, -, htL⟩ := Finset.exists_min_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  obtain ⟨tH, -, htH⟩ := Finset.exists_max_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  set L : ℤ := ρ tL with hL
  set H : ℤ := ρ tH with hH
  have hLf : ∀ t, L ≤ ρ t := fun t => htL t (Finset.mem_univ t)
  have hHf : ∀ t, ρ t ≤ H := fun t => htH t (Finset.mem_univ t)
  by_cases hdeg : H ≤ L + 2
  · refine exists_blocks_first_of_range_le_two hn href i (href.minIdx tL).val (fun t => ?_)
    have h1 := hLf t
    have h2 := hHf t
    simp only [hρ, hL, hH] at h1 h2 hdeg
    omega
  · have hcase : L + 3 ≤ H := by omega
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedIvF ρ σ := isCrookedIvF_minIdx_maxIdx hcr
    obtain ⟨len, c, hG, hT⟩ :=
      hS3 n ρ σ i H L hlip hcrook hLf hHf hcase ⟨tL, hL.symm⟩ ⟨tH, hH.symm⟩
    exact exists_blocks_first_of_folds href i _ _ hG hT

/-- `F2PrimeOff` implies `S3`: the one-bump itineraries are itineraries. Recorded so that the
batch-24 and batch-25 work is visibly subsumed rather than discarded. -/
theorem s3_of_f2PrimeOff (h : F2PrimeOff) : S3 := by
  intro n ρ σ i H L hlip hcr hLb hHb hLH hL hH
  obtain ⟨c₀, -, -, -, hfold⟩ := h n ρ σ i H L hlip hcr hLb hHb hLH hL hH
  rcases hfold with ⟨h', -, -, hG, hT⟩ | ⟨l, -, -, hG, hT⟩
  · exact ⟨_, _, hG, hT⟩
  · exact ⟨_, _, hG, hT⟩

/-- The base of the induction, from batch 25. -/
theorem s3_span_five {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hspan : H ≤ L + 5) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  obtain ⟨c₀, -, -, -, hfold⟩ := f2PrimeOff_span_five ρ i H L hlip hLb hHb hLH hspan
  rcases hfold with ⟨h', -, -, hG, hT⟩ | ⟨l, -, -, hG, hT⟩
  · exact ⟨_, _, hG, hT⟩
  · exact ⟨_, _, hG, hT⟩

/-! ## Splitting an arm

The induction builds an itinerary by extending a shorter one, so it needs a fold that starts
at a prescribed time and a lemma that glues two folds at a split index. Neither mentions
crookedness.
-/

/-- `FoldsOnto` with the start time prescribed. `FoldsFrom f len c 0` is `FoldsOnto f len c`. -/
def FoldsFrom {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) (u₀ : ℕ) : Prop :=
  ∃ β : Fin m → ℕ, (∀ j, β j < len) ∧
    (∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
    (∀ j : Fin m, j.val = 0 → β j = u₀) ∧
    ∀ j, |f j - c (β j)| ≤ 1

theorem foldsOnto_iff_foldsFrom {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) :
    FoldsOnto f len c ↔ FoldsFrom f len c 0 := Iff.rfl

/-- Extending the walk past `len` does not disturb a fold that stays inside `len`. -/
theorem foldsFrom_extend {m : ℕ} (f : Fin m → ℤ) (len len' : ℕ) (c c' : ℕ → ℤ) (u₀ : ℕ)
    (hle : len ≤ len') (hagree : ∀ u, u < len → c' u = c u) (h : FoldsFrom f len c u₀) :
    FoldsFrom f len' c' u₀ := by
  obtain ⟨β, hlt, hlip, h0, hw⟩ := h
  exact ⟨β, fun j => lt_of_lt_of_le (hlt j) hle, hlip, h0,
    fun j => by rw [hagree _ (hlt j)]; exact hw j⟩

/-- **The gluing lemma.** An arm that folds on its prefix, arriving at time `u₁` at the split
index, and whose suffix folds from `u₁`, folds whole. This is the step Bing's proof performs
where it says "by a similar line of argument". -/
theorem foldsFrom_split {m : ℕ} (f : Fin m → ℤ) (len : ℕ) (c : ℕ → ℤ) (u₀ u₁ : ℕ)
    (s : ℕ) (hs : s < m)
    (hpre : ∃ β : Fin (s + 1) → ℕ, (∀ j, β j < len) ∧
      (∀ j j' : Fin (s + 1), j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) ∧
      (∀ j : Fin (s + 1), j.val = 0 → β j = u₀) ∧
      (∀ j : Fin (s + 1), j.val = s → β j = u₁) ∧
      ∀ j : Fin (s + 1), |f ⟨j.val, by omega⟩ - c (β j)| ≤ 1)
    (hsuf : FoldsFrom (fun j : Fin (m - s) => f ⟨s + j.val, by omega⟩) len c u₁) :
    FoldsFrom f len c u₀ := by
  classical
  obtain ⟨βp, hplt, hplip, hp0, hps, hpw⟩ := hpre
  obtain ⟨βs, hslt, hslip, hs0, hsw⟩ := hsuf
  have hz : βs ⟨0, by omega⟩ = u₁ := hs0 _ rfl
  refine ⟨fun j => if h : j.val ≤ s then βp ⟨j.val, by omega⟩
      else βs ⟨j.val - s, by have := j.isLt; omega⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val ≤ s
    · simp only [dif_pos hj]; exact hplt _
    · simp only [dif_neg hj]; exact hslt _
  · intro j j' hjj'
    have hjm := j.isLt
    have hj'm := j'.isLt
    by_cases hj' : j'.val ≤ s
    · have hj : j.val ≤ s := by omega
      simp only [dif_pos hj, dif_pos hj']
      exact hplip ⟨j.val, by omega⟩ ⟨j'.val, by omega⟩ (by simpa using hjj')
    · by_cases hj : j.val ≤ s
      · -- the seam: `j.val = s`, `j'.val = s + 1`
        simp only [dif_pos hj, dif_neg hj', hps ⟨j.val, by omega⟩ (show j.val = s by omega)]
        have := hslip ⟨0, by omega⟩ ⟨j'.val - s, by omega⟩ (by simp; omega)
        rw [hz] at this
        simpa using this
      · simp only [dif_neg hj, dif_neg hj']
        exact hslip ⟨j.val - s, by omega⟩ ⟨j'.val - s, by omega⟩ (by simp; omega)
  · intro j hj
    simp only [dif_pos (show j.val ≤ s by omega)]
    exact hp0 _ hj
  · intro j
    have hjm := j.isLt
    by_cases hj : j.val ≤ s
    · simp only [dif_pos hj]
      have := hpw ⟨j.val, by omega⟩
      simpa using this
    · simp only [dif_neg hj]
      have := hsw ⟨j.val - s, by omega⟩
      simp only at this
      have he : (⟨s + (j.val - s), by omega⟩ : Fin m) = j := Fin.ext (by simp; omega)
      rw [he] at this
      exact this

/-! ## The near-extreme case, and the cut the induction rests on -/

/-- **`S3` near an extreme.** At a basepoint whose level is within two of an extreme both arms
fold onto one self-ladder, at any span; this is batch 25's `f2PrimeOff_near_extreme`, read as
an itinerary. -/
theorem s3_near_extreme {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  obtain ⟨c₀, -, -, -, hfold⟩ := f2PrimeOff_near_extreme ρ i H L hlip hLb hHb hLH hnear
  rcases hfold with ⟨h, -, -, hG, hT⟩ | ⟨l, -, -, hG, hT⟩
  · exact ⟨_, _, hG, hT⟩
  · exact ⟨_, _, hG, hT⟩

/-- **The reduction of `S3` to its interior basepoints.** With `s3_near_extreme` the statement
holds in full as soon as it holds at basepoints at least three above the bottom and three below
the top — so only spans six and above carry any content. -/
theorem s3_of_interior
    (h : ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
      IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
      (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
      ∃ (len : ℕ) (c : ℕ → ℤ),
        FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c) :
    S3 := by
  intro n ρ σ i H L hlip hcr hLb hHb hLH hL hH
  rcases le_or_gt (ρ i) (L + 2) with hlow | hlow
  · exact s3_near_extreme ρ i H L hlip hLb hHb hLH (Or.inl hlow)
  · rcases le_or_gt (H - 2) (ρ i) with hhigh | hhigh
    · exact s3_near_extreme ρ i H L hlip hLb hHb hLH (Or.inr hhigh)
    · exact h n ρ σ i H L hlip hcr hLb hHb hLH hL hH (by omega) (by omega)

/-- **The cut.** Between an index at the bottom and a later one at the top, a faithful crooked
sequence comes within one of the top and then, after that, within one of the bottom. This is
the crookedness clause of the model at the pair `(a, b)`, with the two extreme levels. -/
theorem crookedIvF_cut {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) {L H : ℤ}
    {a b : Fin n} (hab : a < b) (ha : ρ a = L) (hb : ρ b = H) (hLH : L + 3 ≤ H) :
    ∃ r r' : Fin n, a < r ∧ r < r' ∧ r' < b ∧ H - 2 ≤ ρ r ∧ ρ r' ≤ L + 1 := by
  have hma : ∃ u : Fin n, ((u : ℤ) - a.val).natAbs ≤ 1 ∧ ρ u ≤ L ∧ L ≤ σ u :=
    ⟨a, by simp, le_of_eq ha, by rw [← ha]; exact hf.le a⟩
  have hmb : ∃ u : Fin n, ((u : ℤ) - b.val).natAbs ≤ 1 ∧ ρ u ≤ H ∧ H ≤ σ u :=
    ⟨b, by simp, le_of_eq hb, by rw [← hb]; exact hf.le b⟩
  obtain ⟨r, r', h1, h2, h3, hup, -⟩ :=
    hf.crooked a b hab L H hma hmb (by rw [abs_sub_comm, abs_of_nonneg (by omega)]; omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, -⟩ := hup (by omega)
  have hwr := hf.width r
  exact ⟨r, r', h1, h2, h3, by omega, hr'1⟩

/-- **The cut, at its first crossings.** Taking the two indices of `crookedIvF_cut` as early as
possible pins their levels and bands the two pieces: up to `r` the sequence stays at or below
`H − 3`, and from `r` to `r'` it stays at or above `L + 2`. These are the first two of the
three pieces of COMMISSION.md §4. The level at `r'` is pinned only from above: when the span
is exactly three the first crossing of the bottom band can land on `L` itself. -/
theorem crookedIvF_cut_first {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    {L H : ℤ} {a b : Fin n} (hab : a < b) (ha : ρ a = L) (hb : ρ b = H) (hLH : L + 3 ≤ H) :
    ∃ r r' : Fin n, a < r ∧ r < r' ∧ r' < b ∧ ρ r = H - 2 ∧ ρ r' ≤ L + 1 ∧
      (∀ t : Fin n, a < t → t < r → ρ t ≤ H - 3) ∧
      (∀ t : Fin n, r < t → t < r' → L + 2 ≤ ρ t) := by
  classical
  obtain ⟨R, R', hR, hRR', hR'b, hRup, hR'lo⟩ := crookedIvF_cut hf hab ha hb hLH
  -- the first index after `a` within one of the top
  obtain ⟨r, ⟨har, hrup⟩, hrmin⟩ :=
    exists_least_index (fun j => a < j ∧ H - 2 ≤ ρ j) ⟨R, hR, hRup⟩
  have hrR : r.val ≤ R.val := by
    by_contra hc
    exact (hrmin R (by omega)) ⟨hR, hRup⟩
  have hbelow : ∀ t : Fin n, a < t → t < r → ρ t ≤ H - 3 := by
    intro t h1 h2
    have := hrmin t h2
    by_contra hc
    exact this ⟨h1, by omega⟩
  have hreq : ρ r = H - 2 := by
    have hpos : 0 < r.val := lt_of_le_of_lt (Nat.zero_le _) har
    have hq : (⟨r.val - 1, by omega⟩ : Fin n).val + 1 = r.val := by simp; omega
    have hstep := hlip ⟨r.val - 1, by omega⟩ r hq.symm
    rw [abs_le] at hstep
    rcases eq_or_lt_of_le (show a.val ≤ r.val - 1 by omega) with he | hlt
    · have : (⟨r.val - 1, by omega⟩ : Fin n) = a := Fin.ext he.symm
      rw [this, ha] at hstep
      omega
    · have := hbelow ⟨r.val - 1, by omega⟩ hlt (by simp [Fin.lt_def]; omega)
      omega
  -- the first index after `r` within one of the bottom
  have hrR' : r < R' := lt_of_le_of_lt hrR hRR'
  obtain ⟨r', ⟨hrr', hr'lo⟩, hr'min⟩ :=
    exists_least_index (fun j => r < j ∧ ρ j ≤ L + 1) ⟨R', hrR', hR'lo⟩
  have hr'R' : r'.val ≤ R'.val := by
    by_contra hc
    exact (hr'min R' (by omega)) ⟨hrR', hR'lo⟩
  have habove : ∀ t : Fin n, r < t → t < r' → L + 2 ≤ ρ t := by
    intro t h1 h2
    have := hr'min t h2
    by_contra hc
    exact this ⟨h1, by omega⟩
  exact ⟨r, r', har, hrr', lt_of_le_of_lt hr'R' hR'b,
    hreq, hr'lo, hbelow, habove⟩

-- Commented-out statement `s3`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
