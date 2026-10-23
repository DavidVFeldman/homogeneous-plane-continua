import HPC.Fold.ClosureTight

/-!
# The interval model: the faithful transport of crookedness to sequences

`IsCrookedSeq ρ` (batch 7) is what the minimal-index sequence of a crooked chain satisfies. It
is a necessary condition only. Every refutation from batch 15 on — `Agreement`, `MixedGap`,
`F2Prime`, `F2PrimeTight`, `F2PrimeFree`, and the three tight conjectures — was a refutation of a
statement whose hypothesis was `IsCrookedSeq`, by a sequence satisfying it; and none of those
sequences is the minimal-index sequence of any chain crooked in the 1948 sense. The interval
model — each link recorded by the interval of coarse indices whose links contain it — is
complete for realizability, and over it the batch-16 route holds on every one of 19 210 975
basepoints of genuinely crooked chains of length ≤ 8 on six levels and 65 878 more from random
crooked chains to length 30.

This file defines the model, proves that a crooked chain lands in it, proves that the two
sequence-model witnesses are not chains, and restates the batch-16 route over it.

English proofs: COMMISSION-batch20.md §§2–4. Delivered complete: no `sorry` remains.

Two remarks on the delivery.

* The two non-realizability theorems are proved by the decision-tree route, not by `decide`:
  each needs only **two** instances of the crookedness clause, found by the search in
  `census-batch20.py`. For `badSeq` they are `(s,t,h,k) = (0,2,1,4)` and `(0,8,1,5)`; for
  `fpSeq` they are `(0,7,5,1)` and `(5,7,4,1)`, and the first of these forces `σ 5 = 4`,
  after which the second has no room for its two intermediate links. The trees given in the
  commission are longer than necessary; the shorter ones are verified exhaustively over all
  `2⁹` respectively `2¹⁴` interval patterns by the script.
* The batch-16 assembly copies over verbatim: no lemma in the chain consumes crookedness
  directly — `f2PrimeTight_of_exitReachTight` only passes it to its three hypotheses — so
  `IsCrookedIv ρ σ` can be passed instead without any appeal to
  `IsCrookedIv.isCrookedSeq`.

One warning about the census quoted above, which is the commission's: it stops at short chains.
`HPC/Fold/IntervalWitness.lean` refutes `ExitReachIv`, `LowExitPeakIv` and `F2PrimeIv` at
genuine interval chains of lengths 22 and 24 on six levels, so the route stated below does not
reach Theorem 3 over this model either, and `theorem3_of_F2PrimeIv` has a false hypothesis.
`HighExitValleyIv` is so far unrefuted.
-/

namespace HPC.Fold

/-- An interval sequence: `ρ t ≤ σ t ≤ ρ t + 1`, with consecutive intervals within distance
one, and the 1948 crookedness condition read on the intervals — a link *meets* coarse index
`j` iff `j ∈ [ρ t, σ t]` (the model most favourable to crookedness), and *lies in* `j` iff the
same. -/
structure IsCrookedIv {n : ℕ} (ρ σ : Fin n → ℤ) : Prop where
  le : ∀ t, ρ t ≤ σ t
  width : ∀ t, σ t ≤ ρ t + 1
  adj : ∀ t t' : Fin n, t'.val = t.val + 1 → ρ t' ≤ σ t + 1 ∧ ρ t ≤ σ t' + 1
  crooked : ∀ s t : Fin n, s < t → ∀ h k : ℤ,
    ρ s ≤ h → h ≤ σ s → ρ t ≤ k → k ≤ σ t → 3 ≤ |h - k| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (h < k → (ρ r ≤ k - 1 ∧ k - 1 ≤ σ r) ∧ (ρ r' ≤ h + 1 ∧ h + 1 ≤ σ r')) ∧
      (k < h → (ρ r ≤ k + 1 ∧ k + 1 ≤ σ r) ∧ (ρ r' ≤ h - 1 ∧ h - 1 ≤ σ r'))

open HPC.Chain in
/-- One application of 1948 crookedness, read on the containing coarse indices: if `E.link s`
lies in `D.link a` and `E.link t` lies in `D.link b` with the two indices at distance at least
three, there are two links between them whose index intervals contain the index adjacent to
the far one on the near side, and then the index adjacent to the near one on the far side. -/
theorem crookedIv_step {X : Type*} [MetricSpace X] {m c : ℕ}
    {E : Chain X m} {D : Chain X c} (hcr : E.IsCrookedIn' D) {s t : Fin m} (hst : s < t)
    (a b : Fin c) (ha : E.link s ⊆ D.link a) (hb : E.link t ⊆ D.link b)
    (hab : 3 ≤ |(a : ℤ) - (b : ℤ)|) :
    ∃ r r' : Fin m, s < r ∧ r < r' ∧ r' < t ∧
      ((a : ℤ) < (b : ℤ) →
        (((hcr.1.minIdx r : ℕ) : ℤ) ≤ (b : ℤ) - 1 ∧ (b : ℤ) - 1 ≤ ((hcr.1.maxIdx r : ℕ) : ℤ)) ∧
        (((hcr.1.minIdx r' : ℕ) : ℤ) ≤ (a : ℤ) + 1 ∧
          (a : ℤ) + 1 ≤ ((hcr.1.maxIdx r' : ℕ) : ℤ))) ∧
      ((b : ℤ) < (a : ℤ) →
        (((hcr.1.minIdx r : ℕ) : ℤ) ≤ (b : ℤ) + 1 ∧ (b : ℤ) + 1 ≤ ((hcr.1.maxIdx r : ℕ) : ℤ)) ∧
        (((hcr.1.minIdx r' : ℕ) : ℤ) ≤ (a : ℤ) - 1 ∧
          (a : ℤ) - 1 ≤ ((hcr.1.maxIdx r' : ℕ) : ℤ))) := by
  have href := hcr.1
  have hmeet_s : (E.link s ∩ D.link a).Nonempty := by
    obtain ⟨z, hz⟩ := E.link_nonempty s
    exact ⟨z, hz, ha hz⟩
  have hmeet_t : (E.link t ∩ D.link b).Nonempty := by
    obtain ⟨z, hz⟩ := E.link_nonempty t
    exact ⟨z, hz, hb hz⟩
  rcases lt_or_gt_of_ne (fun (hab' : (a : ℤ) = (b : ℤ)) => by
      rw [hab'] at hab; simp at hab) with hlt | hgt
  · -- ascending: `a` before `b`
    have hidx : a.val + 2 < b.val := by
      rcases abs_cases ((a : ℤ) - (b : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    obtain ⟨r, r', hbtw, hr, hr'⟩ := hcr.2 a b hidx s t hmeet_s hmeet_t
    have horder : s < r ∧ r < r' ∧ r' < t := by
      rcases hbtw with hb' | hb'
      · exact hb'
      · exact absurd hst (not_lt.mpr ((hb'.2.2.trans hb'.2.1).trans hb'.1).le)
    refine ⟨r, r', horder.1, horder.2.1, horder.2.2, fun _ => ⟨⟨?_, ?_⟩, ?_, ?_⟩,
      fun hcon => absurd hcon (by omega)⟩
    · have := Fin.le_def.mp (minIdx_le href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (minIdx_le href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r' hr'); simp only [] at this; omega
  · -- descending: `b` before `a`
    have hidx : b.val + 2 < a.val := by
      rcases abs_cases ((a : ℤ) - (b : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    obtain ⟨r, r', hbtw, hr, hr'⟩ := hcr.2 b a hidx t s hmeet_t hmeet_s
    -- the order runs from `t` back to `s`, so `s < r' < r < t`
    have horder : s < r' ∧ r' < r ∧ r < t := by
      rcases hbtw with hb' | hb'
      · exact absurd hst (not_lt.mpr ((hb'.1.trans hb'.2.1).trans hb'.2.2).le)
      · exact ⟨hb'.2.2, hb'.2.1, hb'.1⟩
    refine ⟨r', r, horder.1, horder.2.1, horder.2.2, fun hcon => absurd hcon (by omega),
      fun _ => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · have := Fin.le_def.mp (minIdx_le href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (minIdx_le href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r hr); simp only [] at this; omega

open HPC.Chain in
/-- A chain crooked in the 1948 sense lands in the interval model via `(minIdx, maxIdx)`. -/
theorem isCrookedIv_minIdx_maxIdx {X : Type*} [MetricSpace X] {m k : ℕ}
    {E : Chain X m} {D : Chain X k} (h : E.IsCrookedIn' D) :
    IsCrookedIv (fun t => (h.1.minIdx t : ℤ)) (fun t => (h.1.maxIdx t : ℤ)) := by
  have href := h.1
  have hle : ∀ t, ((href.minIdx t : ℕ) : ℤ) ≤ ((href.maxIdx t : ℕ) : ℤ) := by
    intro t
    have := Fin.le_def.mp (minIdx_le href t (maxIdx_subset href t))
    exact_mod_cast this
  have hwidth : ∀ t, ((href.maxIdx t : ℕ) : ℤ) ≤ ((href.minIdx t : ℕ) : ℤ) + 1 := by
    intro t
    have hadj := subset_adjacent_of_subset href t (minIdx_subset href t) (maxIdx_subset href t)
    have := hle t
    omega
  refine ⟨hle, hwidth, ?_, ?_⟩
  · intro t t' htt'
    have hlip := minIdx_lip href t t' htt'
    have h1 := hle t
    have h2 := hle t'
    constructor <;> omega
  · intro s t hst hh kk hs1 hs2 ht1 ht2 habs
    -- the width bound pins `hh` to one of the two ends of the interval at `s`, and `kk` at `t`
    have hs := hwidth s
    have ht := hwidth t
    have hcase_s : hh = ((href.minIdx s : ℕ) : ℤ) ∨ hh = ((href.maxIdx s : ℕ) : ℤ) := by
      simp only [] at hs1 hs2; omega
    have hcase_t : kk = ((href.minIdx t : ℕ) : ℤ) ∨ kk = ((href.maxIdx t : ℕ) : ℤ) := by
      simp only [] at ht1 ht2; omega
    -- in each case `E.link s` lies in the coarse link with index `hh`, and likewise at `t`
    obtain ⟨a, ha, hav⟩ : ∃ a : Fin k, E.link s ⊆ D.link a ∧ ((a : ℕ) : ℤ) = hh := by
      rcases hcase_s with he | he
      · exact ⟨href.minIdx s, minIdx_subset href s, he.symm⟩
      · exact ⟨href.maxIdx s, maxIdx_subset href s, he.symm⟩
    obtain ⟨b, hb, hbv⟩ : ∃ b : Fin k, E.link t ⊆ D.link b ∧ ((b : ℕ) : ℤ) = kk := by
      rcases hcase_t with he | he
      · exact ⟨href.minIdx t, minIdx_subset href t, he.symm⟩
      · exact ⟨href.maxIdx t, maxIdx_subset href t, he.symm⟩
    obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
      crookedIv_step h hst a b ha hb (by rw [hav, hbv]; exact habs)
    refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hasc (by omega)
      omega
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hdesc (by omega)
      omega

/-- The interval model implies the down form on `ρ` — consistency with batch 7. -/
theorem IsCrookedIv.isCrookedSeq {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIv ρ σ) :
    IsCrookedSeq ρ := by
  intro s t hst habs
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
    h.crooked s t hst (ρ s) (ρ t) le_rfl (h.le s) le_rfl (h.le t)
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

/-! ## The sequence-model witnesses are not chains -/

/-- The batch-15 witness admits no interval structure making it crooked.

Two instances of the crookedness clause suffice. If `σ 2 = 4`, the pair `s = 0, t = 2` with
`h = 1, k = 4` needs two links strictly between indices `0` and `2`, and there is only one.
If `σ 2 = 3`, the pair `s = 0, t = 8` with `h = 1, k = 5` needs a link whose interval contains
`4` — so at an index carrying level `3` or `4`, hence at index `2` or later — followed by a
*later* link whose interval contains `2` — so at an index carrying level `1` or `2`, hence at
index `3` or earlier. Only `r = 2`, `r' = 3` can do it, and `σ 2 = 3` rules it out. -/
theorem badSeq_not_realizable : ∀ σ : Fin 9 → ℤ, ¬ IsCrookedIv badSeq σ := by
  intro σ hIv
  have hσ2 : badSeq 2 = 3 := by decide
  have hσ8 : badSeq 8 = 5 := by decide
  have hσ0 : badSeq 0 = 1 := by decide
  have hcase : σ 2 = 3 ∨ σ 2 = 4 := by
    have h1 := hIv.le 2
    have h2 := hIv.width 2
    omega
  rcases hcase with h2 | h2
  · -- the long pair: the two intermediate links are forced to indices `2` and `3`
    obtain ⟨r, r', hr1, hr2, hr3, hasc, -⟩ :=
      hIv.crooked 0 8 (by decide) 1 5 (by omega) (by have := hIv.le 0; omega) (by omega)
        (by have := hIv.le 8; omega) (by norm_num)
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hasc (by norm_num)
    have hwr := hIv.width r
    have hwr' := hIv.width r'
    -- `r` carries level `3` or `4`, `r'` carries level `1` or `2`
    have hhigh : ∀ u : Fin 9, 3 ≤ badSeq u → 2 ≤ u.val := by decide
    have hlow : ∀ u : Fin 9, badSeq u ≤ 2 → u.val ≤ 3 := by decide
    have hr : 2 ≤ r.val := hhigh r (by omega)
    have hr' : r'.val ≤ 3 := hlow r' (by omega)
    rw [Fin.lt_def] at hr2
    have hreq : r = 2 := Fin.ext (by omega)
    rw [hreq] at e2
    omega
  · -- the short pair: no room for two intermediate links
    obtain ⟨r, r', hr1, hr2, hr3, -, -⟩ :=
      hIv.crooked 0 2 (by decide) 1 4 (by omega) (by have := hIv.le 0; omega) (by omega)
        (by omega) (by norm_num)
    rw [Fin.lt_def] at hr1 hr2 hr3
    omega

/-- The batch-19 witness admits no interval structure making it crooked.

Two instances again. The pair `s = 0, t = 7` with `h = 5, k = 1` needs a link whose interval
contains `2` — level `1` or `2`, so index `4` or `6` — followed by a later link, before `7`,
whose interval contains `4` — level `3` or `4`, so index `5`; whence `σ 5 = 4`. Then the pair
`s = 5, t = 7` with `h = 4, k = 1` needs two links strictly between indices `5` and `7`, and
there is only one. -/
theorem fpSeq_not_realizable : ∀ σ : Fin 14 → ℤ, ¬ IsCrookedIv fpSeq σ := by
  intro σ hIv
  have hf0 : fpSeq 0 = 5 := by decide
  have hf5 : fpSeq 5 = 3 := by decide
  have hf7 : fpSeq 7 = 1 := by decide
  -- first instance: the two intermediate links are forced to indices `4` or `6`, and `5`
  have h5 : σ 5 = 4 := by
    obtain ⟨r, r', hr1, hr2, hr3, -, hdesc⟩ :=
      hIv.crooked 0 7 (by decide) 5 1 (by omega) (by have := hIv.le 0; omega) (by omega)
        (by have := hIv.le 7; omega) (by norm_num)
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hdesc (by norm_num)
    have hwr := hIv.width r
    have hwr' := hIv.width r'
    have hlow : ∀ u : Fin 14, 1 ≤ fpSeq u → fpSeq u ≤ 2 → u.val < 7 → 4 ≤ u.val := by decide
    have hhigh : ∀ u : Fin 14, 3 ≤ fpSeq u → fpSeq u ≤ 4 → 4 < u.val → u.val < 7 →
        u.val = 5 := by decide
    rw [Fin.lt_def] at hr2 hr3
    have hr : 4 ≤ r.val := hlow r (by omega) (by omega) (by omega)
    have hr'5 : r'.val = 5 := hhigh r' (by omega) (by omega) (by omega) (by omega)
    have hreq : r' = 5 := Fin.ext (by omega)
    rw [hreq] at e4
    have := hIv.width 5
    omega
  -- second instance: no room for two intermediate links
  obtain ⟨r, r', hr1, hr2, hr3, -, -⟩ :=
    hIv.crooked 5 7 (by decide) 4 1 (by omega) (by omega) (by omega)
      (by have := hIv.le 7; omega) (by norm_num)
  rw [Fin.lt_def] at hr1 hr2 hr3
  omega

/-! ## The batch-16 route, over the interval model -/

def F2PrimeIv : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIv ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
      (SegLam (armG ρ i) (ρ i) H L (hStar ρ i H L) ∧
       SegLam (armT ρ i) (ρ i) H L (hStar ρ i H L)) ∨
      (SegVee (armG ρ i) (ρ i) H L (lStar ρ i H L) ∧
       SegVee (armT ρ i) (ρ i) H L (lStar ρ i H L))

def ExitReachIv : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIv ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
      (OkLam (armG ρ i) (ρ i) (hStar ρ i H L) ∧ OkLam (armT ρ i) (ρ i) (hStar ρ i H L)) ∨
      (OkVee (armG ρ i) (ρ i) (lStar ρ i H L) ∧ OkVee (armT ρ i) (ρ i) (lStar ρ i H L))

def HighExitValleyIv : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIv ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        armG ρ i j + phase (armG ρ i) j < hStar ρ i H L) →
      ValleyBefore (armG ρ i) L (hStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        armT ρ i j + phase (armT ρ i) j < hStar ρ i H L) →
      ValleyBefore (armT ρ i) L (hStar ρ i H L) s)

def LowExitPeakIv : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIv ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∃ t, ρ t = L) → (∃ t, ρ t = H) →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        - armG ρ i j + phase (fun j => - armG ρ i j) j < - lStar ρ i H L) →
      ValleyBefore (fun j => - armG ρ i j) (-H) (- lStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        - armT ρ i j + phase (fun j => - armT ρ i j) j < - lStar ρ i H L) →
      ValleyBefore (fun j => - armT ρ i j) (-H) (- lStar ρ i H L) s)

/-- The batch-16 assembly, over the interval model. -/
theorem f2PrimeIv_of_exitReachIv (h1 : ExitReachIv) (h2 : HighExitValleyIv)
    (h3 : LowExitPeakIv) : F2PrimeIv := by
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

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, conditional on `F2PrimeIv`. -/
theorem theorem3_of_F2PrimeIv (hF2 : F2PrimeIv) {X : Type*} [MetricSpace X] {n k : ℕ}
    (hn : 0 < n) {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
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
    have hcrook : IsCrookedIv ρ σ := isCrookedIv_minIdx_maxIdx hcr
    have hLi : L ≤ ρ i := hLf i
    have hiH : ρ i ≤ H := hHf i
    rcases hF2 n ρ σ i H L hlip hcrook hLf hHf hcase ⟨tL, hL.symm⟩ ⟨tH, hH.symm⟩ with
      ⟨hG, hT⟩ | ⟨hG, hT⟩
    · exact exists_blocks_first_of_segLam href i (ρ i) H L (hStar ρ i H L) rfl hG hT
        (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf
        (by simp only [hStar]; omega) (by simp only [hStar]; omega) hLi
        (by simp only [hStar]; omega)
    · exact exists_blocks_first_of_segVee href i (ρ i) H L (lStar ρ i H L) rfl hG hT
        (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf
        (by simp only [lStar]; omega) (by simp only [lStar]; omega) hiH
        (by simp only [lStar]; omega)

end HPC.Fold
