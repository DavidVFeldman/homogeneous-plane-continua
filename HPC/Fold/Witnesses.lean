import HPC.Fold.Symmetry

/-!
# The witnesses in the residual configuration

`MixedGapUp_witnesses` (batch 13) is discharged here. In the configuration `MixedGapUp`
forbids, one arm's first exit from `[p − 1, p + 1]` is upward and the other's is downward,
with the window intact between them — so `sync_up` applies with those two exits as witnesses.

The construction uses the single-arm lemma of batch 12 and the first-exit argument, and **no
crookedness**: only the Lipschitz property and the definitions of the two demands.

Applying `sync_up` then places a link at exactly `p + 1` strictly between the two exits, and
the case analysis on which arm carries it is where the next step must go.

English proofs: COMMISSION-batch14.md §3. Delivered complete: no `sorry` remains.

## Two corrections

* The two exits are found in the order *drop then rise*, so the interval `[u, v]` is
  **ascending** and it is `sync_up'`, not `sync_up`, that applies to it. `sync_up'` pins the
  *first* of its two witnesses at `p + 1` and leaves the second in `[p − 1, p]` — the reverse
  of the order the commission asks for in §3. The commissioned conclusion is nevertheless
  obtained, by applying crookedness a second time on the shorter interval `[u, a]` between the
  drop and that `p + 1` link: see `exists_peak_link_between`.
* `hStarArm_eq_of_peak_on_T` needs the hypothesis that the `p + 1` link lies before the
  backward arm's first drop, which the commissioned statement omits; see the note on that
  theorem. It is restored in the form the caller has it, and the commissioned statement is
  kept verbatim, commented out, at the end of the file.
-/

namespace HPC.Fold

variable {m : ℕ} {A : Fin m → ℤ}

/-! ## First exits -/

/-- If an arm's peak demand reaches `p + 2`, it has a first rise: an index at which it equals
`p + 2` with every earlier index inside the window. -/
theorem exists_first_rise (hm : 0 < m) (hA : IsLip A) (p : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hh : p + 2 ≤ hStarArm A p) :
    ∃ r : Fin m, A r = p + 2 ∧ ∀ j : Fin m, j < r → p - 1 ≤ A j ∧ A j ≤ p + 1 := by
  classical
  obtain ⟨j₀, hj₀, hj₀'⟩ := hStarArm_mem hm A p h0
  have hj₀2 : p + 2 ≤ A j₀ := by omega
  obtain ⟨r, hr, hrmin⟩ := exists_least_index (fun j => p + 2 ≤ A j) ⟨j₀, hj₀2⟩
  have hrj₀ : r.val ≤ j₀.val := by
    by_contra hc
    exact hrmin j₀ (by omega) hj₀2
  have hrpos : 0 < r.val := by
    by_contra hc
    rw [show r = ⟨0, hm⟩ from Fin.ext (show r.val = 0 by omega), h0] at hr
    omega
  have hbelow : ∀ j : Fin m, j.val < r.val → p - 1 ≤ A j ∧ A j ≤ p + 1 := by
    intro j hj
    refine ⟨hj₀' j (Fin.le_def.2 (by omega)), ?_⟩
    have := hrmin j hj
    omega
  have hstep := hA ⟨r.val - 1, by omega⟩ r (by simp; omega)
  rw [abs_le] at hstep
  have hpre := hbelow ⟨r.val - 1, by omega⟩ (by simp; omega)
  refine ⟨r, by omega, fun j hj => hbelow j (Fin.lt_def.1 hj)⟩

/-- If an arm's valley demand reaches `p − 2`, it has a first drop. -/
theorem exists_first_drop (hm : 0 < m) (hA : IsLip A) (p : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hl : lStarArm A p ≤ p - 2) :
    ∃ d : Fin m, A d = p - 2 ∧ ∀ j : Fin m, j < d → p - 1 ≤ A j ∧ A j ≤ p + 1 := by
  have hA' : IsLip (fun j => - A j) := by
    intro j j' hjj'
    have h := hA j j' hjj'
    have : -A j' - -A j = -(A j' - A j) := by ring
    rw [this, abs_neg]
    exact h
  have h0' : (fun j => - A j) ⟨0, hm⟩ = -p := by simp [h0]
  have hh : -p + 2 ≤ hStarArm (fun j => - A j) (-p) := by
    have hdef : lStarArm A p = - hStarArm (fun j => - A j) (-p) := rfl
    omega
  obtain ⟨r, hr, hrw⟩ := exists_first_rise hm hA' (-p) h0' hh
  have hrv : -A r = -p + 2 := hr
  refine ⟨r, by omega, fun j hj => ?_⟩
  have := hrw j hj
  simp only at this
  omega

/-! ## The witnesses -/

/-- **`MixedGapUp_witnesses` discharged.** In the residual configuration the two exits exist,
the drop on the backward arm and the rise on the forward arm, with the window intact between
them. No crookedness is used. -/
theorem mixedGapUp_witnesses : MixedGapUp_witnesses := by
  intro n ρ i hlip _hcr hgapH hgapL
  have hin : i.val < n := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := Nat.succ_pos _
  have h0G : armG ρ i ⟨0, hmG⟩ = ρ i := by
    show ρ ⟨i.val + 0, _⟩ = ρ i
    congr 1
  have h0T : armT ρ i ⟨0, hmT⟩ = ρ i := by
    show ρ ⟨i.val - 0, _⟩ = ρ i
    congr 1
  -- the two demands of the residual configuration
  have hpT : ρ i ≤ hStarArm (armT ρ i) (ρ i) := le_hStarArm hmT _ _ h0T
  have hG2 : ρ i + 2 ≤ hStarArm (armG ρ i) (ρ i) := by omega
  have hqG : lStarArm (armG ρ i) (ρ i) ≤ ρ i := lStarArm_le hmG _ _ h0G
  have hT2 : lStarArm (armT ρ i) (ρ i) ≤ ρ i - 2 := by omega
  obtain ⟨rG, hrG, hrGw⟩ := exists_first_rise hmG (armG_isLip hlip i) (ρ i) h0G hG2
  obtain ⟨dT, hdT, hdTw⟩ := exists_first_drop hmT (armT_isLip hlip i) (ρ i) h0T hT2
  have hrGpos : 0 < rG.val := by
    by_contra hc
    rw [show rG = ⟨0, hmG⟩ from Fin.ext (show rG.val = 0 by omega), h0G] at hrG
    omega
  have hdTpos : 0 < dT.val := by
    by_contra hc
    rw [show dT = ⟨0, hmT⟩ from Fin.ext (show dT.val = 0 by omega), h0T] at hdT
    omega
  have hdTle : dT.val ≤ i.val := by have := dT.isLt; omega
  have hrGlt : i.val + rG.val < n := by have := rG.isLt; omega
  refine ⟨⟨i.val - dT.val, by omega⟩, ⟨i.val + rG.val, by omega⟩, Fin.lt_def.2 (by simp; omega),
    ?_, ?_, ?_⟩
  · show ρ ⟨i.val - dT.val, _⟩ = ρ i - 2
    exact hdT
  · show ρ ⟨i.val + rG.val, _⟩ = ρ i + 2
    exact hrG
  · intro w hwu hwv
    have hw1 : i.val - dT.val < w.val := by simpa [Fin.lt_def] using hwu
    have hw2 : w.val < i.val + rG.val := by simpa [Fin.lt_def] using hwv
    rcases lt_trichotomy w.val i.val with hlt | heq | hgt
    · have hb : (⟨i.val - w.val, by omega⟩ : Fin (i.val + 1)) < dT := Fin.lt_def.2 (by simp; omega)
      have := hdTw _ hb
      have hval : armT ρ i ⟨i.val - w.val, by omega⟩ = ρ w := by
        show ρ ⟨i.val - (i.val - w.val), _⟩ = ρ w
        congr 1
        exact Fin.ext (by simp; omega)
      rw [hval] at this
      exact this
    · rw [show w = i from Fin.ext heq]
      omega
    · have ha : (⟨w.val - i.val, by omega⟩ : Fin (n - i.val)) < rG := Fin.lt_def.2 (by simp; omega)
      have := hrGw _ ha
      have hval : armG ρ i ⟨w.val - i.val, by omega⟩ = ρ w := by
        show ρ ⟨i.val + (w.val - i.val), _⟩ = ρ w
        congr 1
        exact Fin.ext (by simp; omega)
      rw [hval] at this
      exact this

/-! ## What `sync_up` then gives -/

/-- Applying the Synchronization Lemma at those witnesses places a link at exactly `p + 1`
strictly between the two exits, preceded by one in `[p − 1, p]`.

Because the exits come in the order *drop then rise*, the interval is ascending and the
ascending form `sync_up'` is what applies; it pins its *first* witness at `p + 1`. To get the
commissioned order — a link in `[p − 1, p]` and only then the link at `p + 1` — crookedness is
applied once more, on the interval from the drop to that `p + 1` link, whose endpoints differ
by exactly `3`. -/
theorem exists_peak_link_between {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n)
    (hlip : IsLip ρ) (hcr : IsCrookedSeqUp ρ)
    (hgapH : hStarArm (armT ρ i) (ρ i) + 2 ≤ hStarArm (armG ρ i) (ρ i))
    (hgapL : lStarArm (armT ρ i) (ρ i) + 2 ≤ lStarArm (armG ρ i) (ρ i)) :
    ∃ u v j k : Fin n, u < j ∧ j < k ∧ k < v ∧
      ρ u = ρ i - 2 ∧ ρ v = ρ i + 2 ∧
      (∀ w : Fin n, u < w → w < v → ρ i - 1 ≤ ρ w ∧ ρ w ≤ ρ i + 1) ∧
      ρ i - 1 ≤ ρ j ∧ ρ j ≤ ρ i ∧ ρ k = ρ i + 1 := by
  obtain ⟨u, v, huv, hu, hv, hwin⟩ := mixedGapUp_witnesses n ρ i hlip hcr hgapH hgapL
  -- the ascending form of the sharpened Synchronization Lemma: a link at exactly `p + 1`
  obtain ⟨a, b, hua, hab, hbv, hpa, -, -⟩ := sync_up' hcr (ρ i) u v huv hu hv hwin
  -- crookedness again, on the shorter interval `[u, a]`, to put a link in `[p − 1, p]` first
  have habs : 3 ≤ |ρ a - ρ u| := by
    have hd : ρ a - ρ u = 3 := by omega
    rw [hd]; norm_num
  obtain ⟨r, r', hur, hrr', hr'a, hasc, -⟩ := hcr u a hua habs
  obtain ⟨-, h3, h4⟩ := hasc (by omega)
  exact ⟨u, v, r', a, hur.trans hrr', hr'a, hab.trans hbv, hu, hv, hwin, by omega, by omega, hpa⟩

/-- Any level attained at an index all of whose predecessors stay at or above `p − 1` is a
lower bound for the arm's peak demand. -/
theorem le_hStarArm_of_window {m : ℕ} (A : Fin m → ℤ) (p : ℤ) (b : Fin m)
    (hb : ∀ j' : Fin m, j' ≤ b → p - 1 ≤ A j') : A b ≤ hStarArm A p := by
  classical
  set S : Set ℤ := {v : ℤ | ∃ j : Fin m, A j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ A j'}
  have hsub : S ⊆ Set.range A := by
    rintro v ⟨j, rfl, -⟩
    exact ⟨j, rfl⟩
  have hbdd : BddAbove S := ((Set.finite_range A).subset hsub).bddAbove
  exact le_csSup hbdd ⟨b, rfl, hb⟩

/-- The case analysis. The `p + 1` link lies on one side of the basepoint or the other. If it
lies on the backward arm — strictly before that arm's first drop — then the backward arm's peak
demand is exactly `p + 1`, and the gap hypothesis forces the forward arm's demand to `p + 3`
or more.

**Correction.** The commissioned statement (kept verbatim below, commented out) asks only that
the link lie at a global index `k ≤ i`; but the English proof of §4 uses that `k` is strictly
between the two exits, through which it concludes that `k` sits *before the backward arm's
first drop*. That is exactly what is needed, and it does not follow from `k ≤ i`: a link at
`p + 1` lying beyond the arm's first drop is not admissible for `hStarArm`, whose defining set
only contains levels attained with the window intact up to that point. The hypothesis is
therefore restored here in the form the caller has it: every global index between `k` and `i`
stays at or above `p − 1`, which is precisely what `exists_peak_link_between` supplies for its
own `k` (its window clause, applied on `[k, i] ⊆ (u, v)`).

The hypotheses `hlip` and `hcr` turn out to be unnecessary — only the two demand inequalities
and the window are used — and are kept as commissioned. -/
theorem hStarArm_eq_of_peak_on_T {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n)
    (_hlip : IsLip ρ) (_hcr : IsCrookedSeqUp ρ)
    (hgapH : hStarArm (armT ρ i) (ρ i) + 2 ≤ hStarArm (armG ρ i) (ρ i))
    (hgapL : lStarArm (armT ρ i) (ρ i) + 2 ≤ lStarArm (armG ρ i) (ρ i))
    (k : Fin n) (hk : k ≤ i) (hval : ρ k = ρ i + 1)
    (hwin : ∀ w : Fin n, k ≤ w → w ≤ i → ρ i - 1 ≤ ρ w) :
    hStarArm (armT ρ i) (ρ i) = ρ i + 1 ∧
    ρ i + 3 ≤ hStarArm (armG ρ i) (ρ i) := by
  have hin : i.val < n := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := Nat.succ_pos _
  have h0G : armG ρ i ⟨0, hmG⟩ = ρ i := by
    show ρ ⟨i.val + 0, _⟩ = ρ i
    congr 1
  have h0T : armT ρ i ⟨0, hmT⟩ = ρ i := by
    show ρ ⟨i.val - 0, _⟩ = ρ i
    congr 1
  -- the backward arm's peak demand is at most `p + 1`
  have hqG : lStarArm (armG ρ i) (ρ i) ≤ ρ i := lStarArm_le hmG _ _ h0G
  have hT2 : lStarArm (armT ρ i) (ρ i) ≤ ρ i - 2 := by omega
  have hupper : hStarArm (armT ρ i) (ρ i) ≤ ρ i + 1 :=
    hStarArm_le_of_lStarArm hmT (ρ i) h0T hT2
  -- and at least `p + 1`, since the link at `k` is admissible
  have hkle : k.val ≤ i.val := Fin.le_def.1 hk
  have hbval : armT ρ i ⟨i.val - k.val, by omega⟩ = ρ k := by
    show ρ ⟨i.val - (i.val - k.val), _⟩ = ρ k
    congr 1
    exact Fin.ext (by simp; omega)
  have hadm : ∀ j' : Fin (i.val + 1), j' ≤ ⟨i.val - k.val, by omega⟩ →
      ρ i - 1 ≤ armT ρ i j' := by
    intro j' hj'
    have hj'le : j'.val ≤ i.val - k.val := Fin.le_def.1 hj'
    have hj'lt : j'.val ≤ i.val := by have := j'.isLt; omega
    show ρ i - 1 ≤ ρ ⟨i.val - j'.val, by omega⟩
    exact hwin _ (Fin.le_def.2 (show k.val ≤ i.val - j'.val by omega))
      (Fin.le_def.2 (show i.val - j'.val ≤ i.val by omega))
  have hlower := le_hStarArm_of_window (armT ρ i) (ρ i) ⟨i.val - k.val, by omega⟩ hadm
  rw [hbval, hval] at hlower
  exact ⟨by omega, by omega⟩

-- Commented-out statement `hStarArm_eq_of_peak_on_T'` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
