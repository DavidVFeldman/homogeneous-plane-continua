import HPC.Fold.Phase

/-!
# Agreement reduced to one configuration

An arm cannot both climb to `p + 2` while never having dropped below `p − 1`, and drop to
`p − 2` while never having risen above `p + 1`: whichever of the two witnessing indices comes
first contradicts the other's prefix condition. This needs no crookedness and no Lipschitz
property.

It reduces `Agreement` to a single configuration — one arm rising first, the other dropping
first, with both gaps at least two — recorded here as `MixedGap`.

English proofs: COMMISSION-batch12.md. Delivered complete: no `sorry` remains.

## How the arm symmetry of the reduction is handled

The reduction needs `MixedGap` with the roles of the two arms exchanged. The two arms have
different index types, so a literal swap is not available. Instead the swap is realised by
*reversing the sequence*: `revSeq ρ t = ρ (n − 1 − t)` with the basepoint `revIdx i`
exchanges `armG` and `armT`, and `IsLip` and `IsCrookedSeq` are both preserved by reversal
(`isLip_revSeq`, `isCrookedSeq_revSeq`). Since `MixedGap` is universally quantified over all
sequences and basepoints, applying it to the reversed data yields the mirrored form
(`mixedGap_swap`). The residual index-type mismatch is absorbed by `hStarArm_congr`, which
compares two arms of provably equal length agreeing pointwise.
-/

namespace HPC.Fold

variable {m : ℕ} {A : Fin m → ℤ}

/-! ## 1. The single-arm lemma -/

/-- The reflected form of `hStarArm_mem`: an arm attains its valley demand at an index all of
whose predecessors stay at or below `p + 1`. -/
theorem lStarArm_mem (hm : 0 < m) (f : Fin m → ℤ) (p : ℤ) (h0 : f ⟨0, hm⟩ = p) :
    ∃ k : Fin m, f k = lStarArm f p ∧ ∀ k' : Fin m, k' ≤ k → f k' ≤ p + 1 := by
  obtain ⟨k, hk, hk'⟩ := hStarArm_mem hm (fun j => - f j) (-p) (by simp [h0])
  refine ⟨k, ?_, fun k' hk'' => ?_⟩
  · simp only [lStarArm]; omega
  · have := hk' k' hk''; simp only at this; omega

/-- The reflection of `le_hStarArm`: the valley demand never exceeds the starting level. -/
theorem lStarArm_le (hm : 0 < m) (f : Fin m → ℤ) (p : ℤ) (h0 : f ⟨0, hm⟩ = p) :
    lStarArm f p ≤ p := by
  have := le_hStarArm hm (fun j => - f j) (-p) (by simp [h0])
  simp only [lStarArm]
  omega

/-- **The single-arm lemma.** No arm has both a high demand and a low one. -/
theorem not_hStarArm_and_lStarArm (hm : 0 < m) (p : ℤ) (h0 : A ⟨0, hm⟩ = p) :
    ¬ (p + 2 ≤ hStarArm A p ∧ lStarArm A p ≤ p - 2) := by
  rintro ⟨hh, hl⟩
  obtain ⟨j, hj, hjpre⟩ := hStarArm_mem hm A p h0
  obtain ⟨k, hk, hkpre⟩ := lStarArm_mem hm A p h0
  rcases le_total k j with hkj | hjk
  · have := hjpre k hkj; omega
  · have := hkpre j hjk; omega

/-- Contrapositive, in the form the reduction uses. -/
theorem le_lStarArm_of_hStarArm (hm : 0 < m) (p : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hh : p + 2 ≤ hStarArm A p) : p - 1 ≤ lStarArm A p := by
  by_contra hc
  exact not_hStarArm_and_lStarArm hm p h0 ⟨hh, by omega⟩

theorem hStarArm_le_of_lStarArm (hm : 0 < m) (p : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hl : lStarArm A p ≤ p - 2) : hStarArm A p ≤ p + 1 := by
  by_contra hc
  exact not_hStarArm_and_lStarArm hm p h0 ⟨by omega, hl⟩

/-! ## 2. Reversal, and the exchange of the two arms -/

/-- Two arms of provably equal length that agree pointwise have the same peak demand. -/
theorem hStarArm_congr {m m' : ℕ} (f : Fin m → ℤ) (g : Fin m' → ℤ) (p : ℤ) (hmm : m = m')
    (hfg : ∀ (j : ℕ) (hj : j < m) (hj' : j < m'), f ⟨j, hj⟩ = g ⟨j, hj'⟩) :
    hStarArm f p = hStarArm g p := by
  subst hmm
  have : f = g := funext fun j => by simpa using hfg j.val j.isLt j.isLt
  rw [this]

/-- The same for the valley demand. -/
theorem lStarArm_congr {m m' : ℕ} (f : Fin m → ℤ) (g : Fin m' → ℤ) (p : ℤ) (hmm : m = m')
    (hfg : ∀ (j : ℕ) (hj : j < m) (hj' : j < m'), f ⟨j, hj⟩ = g ⟨j, hj'⟩) :
    lStarArm f p = lStarArm g p := by
  simp only [lStarArm]
  rw [hStarArm_congr (fun j => - f j) (fun j => - g j) (-p) hmm
    (fun j hj hj' => by simp only; rw [hfg j hj hj'])]

/-- The reversal of a sequence. -/
def revSeq {n : ℕ} (ρ : Fin n → ℤ) : Fin n → ℤ := fun t => ρ ⟨n - 1 - t.val, by omega⟩

/-- The reversal of an index. -/
def revIdx {n : ℕ} (i : Fin n) : Fin n := ⟨n - 1 - i.val, by omega⟩

theorem revSeq_revIdx {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) : revSeq ρ (revIdx i) = ρ i := by
  have hi := i.isLt
  exact congrArg ρ (Fin.ext (by simp only [revIdx]; omega))

theorem isLip_revSeq {n : ℕ} {ρ : Fin n → ℤ} (h : IsLip ρ) : IsLip (revSeq ρ) := by
  intro j j' hjj'
  have hj := j.isLt
  have hj' := j'.isLt
  have key := h ⟨n - 1 - j'.val, by omega⟩ ⟨n - 1 - j.val, by omega⟩ (by simp only; omega)
  simp only [revSeq]
  rw [abs_sub_comm]
  exact key

theorem isCrookedSeq_revSeq {n : ℕ} {ρ : Fin n → ℤ} (h : IsCrookedSeq ρ) :
    IsCrookedSeq (revSeq ρ) := by
  intro s t hst habs
  have hs := s.isLt
  have ht := t.isLt
  have hstv : s.val < t.val := hst
  have hST : (⟨n - 1 - t.val, by omega⟩ : Fin n) < ⟨n - 1 - s.val, by omega⟩ := by
    simp only [Fin.lt_def]; omega
  have hSv : revSeq ρ t = ρ ⟨n - 1 - t.val, by omega⟩ := rfl
  have hTv : revSeq ρ s = ρ ⟨n - 1 - s.val, by omega⟩ := rfl
  obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
    h ⟨n - 1 - t.val, by omega⟩ ⟨n - 1 - s.val, by omega⟩ hST (by rw [← hSv, ← hTv, abs_sub_comm]; exact habs)
  have h1v : n - 1 - t.val < r.val := h1
  have h2v : r.val < r'.val := h2
  have h3v : r'.val < n - 1 - s.val := h3
  have hr := r.isLt
  have hr' := r'.isLt
  refine ⟨⟨n - 1 - r'.val, by omega⟩, ⟨n - 1 - r.val, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fin.lt_def]; omega
  · simp only [Fin.lt_def]; omega
  · simp only [Fin.lt_def]; omega
  · intro hlt
    have hRv : revSeq ρ ⟨n - 1 - r'.val, by omega⟩ = ρ r' :=
      congrArg ρ (Fin.ext (by simp only; omega))
    have hR'v : revSeq ρ ⟨n - 1 - r.val, by omega⟩ = ρ r :=
      congrArg ρ (Fin.ext (by simp only; omega))
    rw [hRv, hR'v]
    rw [hSv, hTv] at hlt ⊢
    obtain ⟨e1, e2⟩ := hdesc (by omega)
    omega
  · intro hlt
    have hRv : revSeq ρ ⟨n - 1 - r'.val, by omega⟩ = ρ r' :=
      congrArg ρ (Fin.ext (by simp only; omega))
    have hR'v : revSeq ρ ⟨n - 1 - r.val, by omega⟩ = ρ r :=
      congrArg ρ (Fin.ext (by simp only; omega))
    rw [hRv, hR'v]
    rw [hSv, hTv] at hlt ⊢
    obtain ⟨e1, e2⟩ := hasc (by omega)
    omega

/-- Reversing the sequence turns the forward arm at the reversed basepoint into the backward
arm at the original one. -/
theorem armG_revSeq_apply {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (j : ℕ)
    (hj : j < n - (revIdx i).val) (hj' : j < i.val + 1) :
    armG (revSeq ρ) (revIdx i) ⟨j, hj⟩ = armT ρ i ⟨j, hj'⟩ := by
  have hi := i.isLt
  simp only [armG, armT, revSeq, revIdx] at *
  exact congrArg ρ (Fin.ext (by simp only; omega))

/-- ...and the backward arm at the reversed basepoint into the forward arm. -/
theorem armT_revSeq_apply {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (j : ℕ)
    (hj : j < (revIdx i).val + 1) (hj' : j < n - i.val) :
    armT (revSeq ρ) (revIdx i) ⟨j, hj⟩ = armG ρ i ⟨j, hj'⟩ := by
  have hi := i.isLt
  simp only [armG, armT, revSeq, revIdx] at *
  exact congrArg ρ (Fin.ext (by simp only; omega))

/-! ## 3. `MixedGap` -/

/-- The residual configuration: one arm's peak demand exceeds the other's by two or more, and
the *other* arm's valley demand falls below the first arm's by two or more. The single-arm
lemma kills the aligned configuration; this mixed one needs crookedness.

Verified empty on 2 604 840 crooked basepoints (all crooked sequences of length 12 on six
levels). -/
def MixedGap : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n), IsLip ρ → IsCrookedSeq ρ →
    ¬ (hStarArm (armT ρ i) (ρ i) + 2 ≤ hStarArm (armG ρ i) (ρ i) ∧
       lStarArm (armT ρ i) (ρ i) + 2 ≤ lStarArm (armG ρ i) (ρ i))

/-- The mirrored form of `MixedGap`, obtained from `MixedGap` itself by reversing the
sequence, which exchanges the two arms. -/
theorem mixedGap_swap (h : MixedGap) {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n)
    (hlip : IsLip ρ) (hcr : IsCrookedSeq ρ) :
    ¬ (hStarArm (armG ρ i) (ρ i) + 2 ≤ hStarArm (armT ρ i) (ρ i) ∧
       lStarArm (armG ρ i) (ρ i) + 2 ≤ lStarArm (armT ρ i) (ρ i)) := by
  have hi := i.isLt
  have hkey := h n (revSeq ρ) (revIdx i) (isLip_revSeq hlip) (isCrookedSeq_revSeq hcr)
  rw [revSeq_revIdx] at hkey
  have hlen : n - (revIdx i).val = i.val + 1 := by simp only [revIdx]; omega
  have hlen' : (revIdx i).val + 1 = n - i.val := by simp only [revIdx]; omega
  have e1 : hStarArm (armG (revSeq ρ) (revIdx i)) (ρ i) = hStarArm (armT ρ i) (ρ i) :=
    hStarArm_congr _ _ _ hlen (armG_revSeq_apply ρ i)
  have e2 : hStarArm (armT (revSeq ρ) (revIdx i)) (ρ i) = hStarArm (armG ρ i) (ρ i) :=
    hStarArm_congr _ _ _ hlen' (armT_revSeq_apply ρ i)
  have e3 : lStarArm (armG (revSeq ρ) (revIdx i)) (ρ i) = lStarArm (armT ρ i) (ρ i) :=
    lStarArm_congr _ _ _ hlen (armG_revSeq_apply ρ i)
  have e4 : lStarArm (armT (revSeq ρ) (revIdx i)) (ρ i) = lStarArm (armG ρ i) (ρ i) :=
    lStarArm_congr _ _ _ hlen' (armT_revSeq_apply ρ i)
  rw [e1, e2, e3, e4] at hkey
  exact hkey

/-! ## 4. The reduction -/

/-- **The reduction.** `MixedGap` and its mirror imply `Agreement`. -/
theorem agreement_of_mixedGap (h : MixedGap) : Agreement := by
  intro n ρ i hlip hcr
  by_contra hcon
  push_neg at hcon
  obtain ⟨hAbs, hBbs⟩ := hcon
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := Nat.succ_pos _
  have h0G : armG ρ i ⟨0, hmG⟩ = ρ i := congrArg ρ (Fin.ext (by simp))
  have h0T : armT ρ i ⟨0, hmT⟩ = ρ i := congrArg ρ (Fin.ext (by simp))
  have hpG : ρ i ≤ hStarArm (armG ρ i) (ρ i) := le_hStarArm hmG _ _ h0G
  have hpT : ρ i ≤ hStarArm (armT ρ i) (ρ i) := le_hStarArm hmT _ _ h0T
  have hqG : lStarArm (armG ρ i) (ρ i) ≤ ρ i := lStarArm_le hmG _ _ h0G
  have hqT : lStarArm (armT ρ i) (ρ i) ≤ ρ i := lStarArm_le hmT _ _ h0T
  have hA : 2 ≤ |hStarArm (armG ρ i) (ρ i) - hStarArm (armT ρ i) (ρ i)| := by omega
  have hB : 2 ≤ |lStarArm (armG ρ i) (ρ i) - lStarArm (armT ρ i) (ρ i)| := by omega
  rcases abs_cases (hStarArm (armG ρ i) (ρ i) - hStarArm (armT ρ i) (ρ i)) with ⟨ea, _⟩ | ⟨ea, _⟩ <;>
    rcases abs_cases (lStarArm (armG ρ i) (ρ i) - lStarArm (armT ρ i) (ρ i)) with ⟨eb, _⟩ | ⟨eb, _⟩
  · -- hT + 2 ≤ hG and lT + 2 ≤ lG : forbidden by `MixedGap`
    exact h n ρ i hlip hcr ⟨by omega, by omega⟩
  · -- hT + 2 ≤ hG and lG + 2 ≤ lT : then lG ≥ p − 1 and lG ≤ p − 2
    have := le_lStarArm_of_hStarArm hmG (ρ i) h0G (by omega)
    omega
  · -- hG + 2 ≤ hT and lT + 2 ≤ lG : then lT ≥ p − 1 and lT ≤ p − 2
    have := le_lStarArm_of_hStarArm hmT (ρ i) h0T (by omega)
    omega
  · -- hG + 2 ≤ hT and lG + 2 ≤ lT : forbidden by the mirror of `MixedGap`
    exact mixedGap_swap h ρ i hlip hcr ⟨by omega, by omega⟩

end HPC.Fold
