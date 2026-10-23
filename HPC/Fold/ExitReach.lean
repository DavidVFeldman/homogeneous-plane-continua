import HPC.Fold.Refutations

/-!
# `ExitReach`: the corrected replacement for `Agreement`

`Agreement` compared the two arms' raw demands and is false (batch 15). The error was that
`hStar` is *capped* at `max (H − 1) p`, so a large demand on one arm does not raise the height
the other arm must reach. In the refuting sequence the demands are `5` and `3` but `hStar` is
`4`, and both arms clear it.

`ExitReach` states the dichotomy in terms of first exits and phase-adjusted reach, with no
`SegLam`: an arm is fine for the Λ family if it never drops below `p − 1` at all, or if its
phase-adjusted level reaches `hStar` before its first drop.

Checked under the **down** form — what `minIdx` satisfies, and what `F2Prime` is stated over —
on 1 932 166 basepoints across lengths 9 to 12: no failure, and in every instance `ExitReach`
implied the folding condition for both arms outright.

English proofs: COMMISSION-batch16.md §3. Delivered complete: no `sorry` remains.

## Two remarks on the delivery

* **`hdem` is kept as commissioned and discharged at the call site.** `le_succ_of_no_drop` and
  `segLam_of_okLam_no_drop` take the disjunction `hStarArm A p ≤ h ∨ H - 1 ≤ h` exactly as
  written. That it is what `hStar` supplies is recorded separately as `hStar_dem_armG` and
  `hStar_dem_armT`, proved by unfolding the `min`/`max`: if the cap does not bind, `hStar` is
  the floored maximum of the two demands, hence at least this arm's; if it binds, `hStar` is
  `max (H − 1) p ≥ H − 1`. The same shape on the valley side is `lStar_dem_armG`,
  `lStar_dem_armT`.

* **The V case needs a reflected valley clause, which `HighExitValley` does not supply.**
  `SegVee`, `OkVee` and `lStar` are all defined by negation, so the conversion of §3 and §4 to
  the V case is a matter of applying the same lemmas to `fun j => - A j`, and indeed no
  crookedness hypothesis enters those lemmas. But the *valley* hypothesis of
  `segLam_of_peak_before_drop` becomes, for the negated arm, the statement that the arm reaches
  `H − 1` before it goes below `lStar − 1`; and `HighExitValley` is a statement about the
  original sequence at `hStar`, whose own hypotheses include `IsCrookedSeq ρ`, which is **not**
  preserved by negation (batch 13, `not_isCrookedSeq_neg`). So `HighExitValley` cannot be
  transported to the reflected data, and the V branch genuinely needs its reflection as a
  separate assumption. It is recorded here as `LowExitPeak` — literally `HighExitValley` read
  through the negation, at `lStar` — and `f2Prime_of_exitReach` takes it as a third hypothesis.
  `PeakBefore` gives the same condition in unnegated form, and `valleyBefore_neg_iff` records
  the two are the same statement.
-/

namespace HPC.Fold

variable {m : ℕ} {A : Fin m → ℤ}

/-- The arm drops out of the window below. -/
def DropsBelow (A : Fin m → ℤ) (p : ℤ) : Prop := ∃ j, A j ≤ p - 2

/-- The greatest phase-adjusted level the arm attains strictly before its first drop; the
greatest over the whole arm if it never drops. Compare `hStarArm`, which omits the phase. -/
noncomputable def hReach (A : Fin m → ℤ) (p : ℤ) : ℤ :=
  sSup {v : ℤ | ∃ j : Fin m, A j + phase A j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ A j'}

noncomputable def lReach (A : Fin m → ℤ) (p : ℤ) : ℤ := - hReach (fun j => - A j) (-p)

/-- The per-arm condition for the Λ family. -/
def OkLam (A : Fin m → ℤ) (p h : ℤ) : Prop := ¬ DropsBelow A p ∨ h ≤ hReach A p

/-- The per-arm condition for the V family. -/
def OkVee (A : Fin m → ℤ) (p l : ℤ) : Prop := OkLam (fun j => - A j) (-p) (-l)

/-! ## The two suprema -/

/-- The set `hReach` is the supremum of. -/
private def reachSet (A : Fin m → ℤ) (p : ℤ) : Set ℤ :=
  {v : ℤ | ∃ j : Fin m, A j + phase A j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ A j'}

private theorem reachSet_bddAbove (A : Fin m → ℤ) (p : ℤ) : BddAbove (reachSet A p) := by
  have hsub : reachSet A p ⊆ Set.range (fun j => A j + phase A j) := by
    rintro v ⟨j, rfl, -⟩
    exact ⟨j, rfl⟩
  exact ((Set.finite_range _).subset hsub).bddAbove

private theorem reachSet_nonempty (hm : 0 < m) (p : ℤ) (h0 : A ⟨0, hm⟩ = p) :
    (reachSet A p).Nonempty := by
  refine ⟨A ⟨0, hm⟩ + phase A ⟨0, hm⟩, ⟨0, hm⟩, rfl, fun j' hj' => ?_⟩
  have hj'z : j'.val ≤ 0 := Fin.le_def.1 hj'
  have hj'0 : j' = (⟨0, hm⟩ : Fin m) := Fin.ext (show j'.val = 0 by omega)
  rw [hj'0, h0]
  omega

theorem hStarArm_le_hReach (hm : 0 < m) (p : ℤ) (h0 : A ⟨0, hm⟩ = p) :
    hStarArm A p ≤ hReach A p := by
  obtain ⟨j, hj, hjpre⟩ := hStarArm_mem hm A p h0
  have hmem : A j + phase A j ∈ reachSet A p := ⟨j, rfl, hjpre⟩
  have hle : A j + phase A j ≤ hReach A p :=
    le_csSup (reachSet_bddAbove A p) hmem
  rcases phase_zero_or_one A j with e | e <;> omega

theorem hReach_mem (hm : 0 < m) (p : ℤ) (h0 : A ⟨0, hm⟩ = p) :
    ∃ j : Fin m, A j + phase A j = hReach A p ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ A j' :=
  Int.csSup_mem (reachSet_nonempty hm p h0) (reachSet_bddAbove A p)

/-! ## The no-drop branch -/

/-- An arm that never drops is confined to `[p − 1, h + 1]` at the capped height, because its
maximum is its own demand, `hStar` is at least that demand unless the cap binds, and when the
cap binds `hStar = H − 1` while the arm is bounded by `H`. -/
theorem le_succ_of_no_drop (hm : 0 < m) (p h H : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hnd : ¬ DropsBelow A p) (hHA : ∀ j, A j ≤ H) (hdem : hStarArm A p ≤ h ∨ H - 1 ≤ h)
    (j : Fin m) : p - 1 ≤ A j ∧ A j ≤ h + 1 := by
  have hnd' : ∀ j : Fin m, p - 1 ≤ A j := by
    intro j
    by_contra hc
    exact hnd ⟨j, by omega⟩
  have hmax := le_hStarArm_of_no_drop hm h0 hnd' j
  have := hHA j
  exact ⟨hnd' j, by rcases hdem with hd | hd <;> omega⟩

/-- Hence the no-drop branch of `OkLam` gives `SegLam` with no further hypothesis. -/
theorem segLam_of_okLam_no_drop (hm : 0 < m) (p h H L : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hnd : ¬ DropsBelow A p) (hHA : ∀ j, A j ≤ H) (hLA : ∀ j, L ≤ A j)
    (hdem : hStarArm A p ≤ h ∨ H - 1 ≤ h) :
    SegLam A p H L h :=
  segLam_of_bounded hm h0 hLA (fun j => le_succ_of_no_drop hm p h H h0 hnd hHA hdem j)

/-! ## The drop branch -/

/-- If the arm's phase-adjusted level reaches `h` at or before its first drop, the peak index
required by `segLam_of_peak_before_drop` exists with the window intact below it. -/
theorem exists_peak_index_of_hReach (hm : 0 < m) (p h : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hr : h ≤ hReach A p) :
    ∃ s : ℕ, s < m ∧
      (∀ hs : s < m, h ≤ A ⟨s, hs⟩ + phase A ⟨s, hs⟩) ∧
      (∀ j : Fin m, j.val < s → A j + phase A j < h) ∧
      (∀ j : Fin m, j.val < s → p - 1 ≤ A j) := by
  classical
  obtain ⟨j₀, hj₀, hj₀pre⟩ := hReach_mem hm p h0
  obtain ⟨s, hs, hsmin⟩ :=
    exists_least_index (fun j : Fin m => h ≤ A j + phase A j) ⟨j₀, by omega⟩
  have hsj₀ : s.val ≤ j₀.val := by
    by_contra hc
    exact hsmin j₀ (by omega) (by omega)
  refine ⟨s.val, s.isLt, ?_, ?_, ?_⟩
  · intro hs'
    rwa [show (⟨s.val, hs'⟩ : Fin m) = s from Fin.ext rfl]
  · exact fun j hj => lt_of_not_ge (hsmin j hj)
  · exact fun j hj => hj₀pre j (Fin.le_def.2 (by omega))

/-! ## The per-arm assembly -/

/-- Both branches of `OkLam` together: with the valley clause available at whatever peak index
the arm produces, `OkLam` gives `SegLam`. -/
theorem segLam_of_okLam (hm : 0 < m) (p H L h : ℤ) (hA : IsLip A) (h0 : A ⟨0, hm⟩ = p)
    (hLA : ∀ j, L ≤ A j) (hHA : ∀ j, A j ≤ H) (hph : p ≤ h)
    (hdem : hStarArm A p ≤ h ∨ H - 1 ≤ h) (hok : OkLam A p h)
    (hvalley : ∀ s : ℕ, (∀ j : Fin m, j.val < s → A j + phase A j < h) →
      ValleyBefore A L h s) :
    SegLam A p H L h := by
  rcases hok with hnd | hr
  · exact segLam_of_okLam_no_drop hm p h H L h0 hnd hHA hLA hdem
  · obtain ⟨s, hs, hpeak, hmin, hnodrop⟩ := exists_peak_index_of_hReach hm p h h0 hr
    exact segLam_of_peak_before_drop hm hA h0 hph hLA s hs hpeak hmin hnodrop
      (hvalley s hmin)

/-! ## What `hStar` and `lStar` supply -/

/-- The disjunction `hdem` for the forward arm at the height `hStar`: either the cap does not
bind, and `hStar` is at least this arm's demand, or it does, and `hStar ≥ H − 1`. -/
theorem hStar_dem_armG {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) :
    hStarArm (armG ρ i) (ρ i) ≤ hStar ρ i H L ∨ H - 1 ≤ hStar ρ i H L := by
  simp only [hStar, le_min_iff, le_max_iff]
  omega

/-- The same for the backward arm. -/
theorem hStar_dem_armT {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) :
    hStarArm (armT ρ i) (ρ i) ≤ hStar ρ i H L ∨ H - 1 ≤ hStar ρ i H L := by
  simp only [hStar, le_min_iff, le_max_iff]
  omega

/-- The valley-side disjunction for the forward arm, in the shape the reflected `hdem` asks
for: `hStarArm` of the negated arm is `- lStarArm`, and the reflected `H − 1` is `- L − 1`. -/
theorem lStar_dem_armG {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) :
    lStar ρ i H L ≤ lStarArm (armG ρ i) (ρ i) ∨ lStar ρ i H L ≤ L + 1 := by
  simp only [lStar, max_le_iff, min_le_iff]
  omega

theorem lStar_dem_armT {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) :
    lStar ρ i H L ≤ lStarArm (armT ρ i) (ρ i) ∨ lStar ρ i H L ≤ L + 1 := by
  simp only [lStar, max_le_iff, min_le_iff]
  omega

theorem le_hStar {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) : ρ i ≤ hStar ρ i H L := by
  simp only [hStar, le_min_iff, le_max_iff]
  omega

theorem lStar_le {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) : lStar ρ i H L ≤ ρ i := by
  simp only [lStar, max_le_iff, min_le_iff]
  omega

/-! ## The reflected valley clause -/

/-- The reflection of `ValleyBefore`: past the index `s`, the arm does not go below `l − 1`
without having visited `H − 1` or above in between. -/
def PeakBefore {m : ℕ} (A : Fin m → ℤ) (H l : ℤ) (s : ℕ) : Prop :=
  ∀ u : Fin m, s ≤ u.val → A u < l - 1 →
    ∃ j : Fin m, s ≤ j.val ∧ j.val < u.val ∧ H - 1 ≤ A j

/-- `PeakBefore` is exactly `ValleyBefore` for the negated arm. -/
theorem valleyBefore_neg_iff {m : ℕ} (A : Fin m → ℤ) (H l : ℤ) (s : ℕ) :
    ValleyBefore (fun j => - A j) (-H) (-l) s ↔ PeakBefore A H l s := by
  constructor
  · intro h u hu hlt
    obtain ⟨j, hj1, hj2, hj3⟩ := h u hu (by simp only; omega)
    exact ⟨j, hj1, hj2, by simp only at hj3; omega⟩
  · intro h u hu hlt
    obtain ⟨j, hj1, hj2, hj3⟩ := h u hu (by simp only at hlt; omega)
    exact ⟨j, hj1, hj2, by simp only; omega⟩

/-- **LowExitPeak.** The reflection of `HighExitValley` through the negation, at `lStar`: at
the valley height, both arms satisfy `PeakBefore` at their own valley indices.

This is not derivable from `HighExitValley`, whose hypotheses include `IsCrookedSeq ρ`, a
condition not preserved by negating the sequence (batch 13). It is stated here in the negated
shape in which `segLam_of_peak_before_drop` consumes it; `valleyBefore_neg_iff` converts it to
the unnegated `PeakBefore` form. -/
def LowExitPeak : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
    (∀ s : ℕ, (∀ j : Fin (n - i.val), j.val < s →
        (- armG ρ i j) + phase (fun j' => - armG ρ i j') j < - lStar ρ i H L) →
      ValleyBefore (fun j' => - armG ρ i j') (-H) (- lStar ρ i H L) s) ∧
    (∀ s : ℕ, (∀ j : Fin (i.val + 1), j.val < s →
        (- armT ρ i j) + phase (fun j' => - armT ρ i j') j < - lStar ρ i H L) →
      ValleyBefore (fun j' => - armT ρ i j') (-H) (- lStar ρ i H L) s)

/-! ## The statement -/

/-- **`ExitReach`.** The corrected dichotomy. Replaces `Agreement`, which batch 15 refutes. -/
def ExitReach : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ), IsLip ρ → IsCrookedSeq ρ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
      (OkLam (armG ρ i) (ρ i) (hStar ρ i H L) ∧ OkLam (armT ρ i) (ρ i) (hStar ρ i H L)) ∨
      (OkVee (armG ρ i) (ρ i) (lStar ρ i H L) ∧ OkVee (armT ρ i) (ρ i) (lStar ρ i H L))

/-- **`ExitReach` and the valley clauses give `F2Prime`.**

The third hypothesis is the reflection of the second; see the module docstring for why it is
needed and cannot be derived from `HighExitValley`. -/
theorem f2Prime_of_exitReach (h1 : ExitReach) (h2 : HighExitValley) (h3 : LowExitPeak) :
    F2Prime := by
  intro n ρ i H L hlip hcr hL hH hLH
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := Nat.succ_pos _
  have h0G : armG ρ i ⟨0, hmG⟩ = ρ i := congrArg ρ (Fin.ext (by simp))
  have h0T : armT ρ i ⟨0, hmT⟩ = ρ i := congrArg ρ (Fin.ext (by simp))
  have hLG : ∀ j, L ≤ armG ρ i j := fun j => hL _
  have hLT : ∀ j, L ≤ armT ρ i j := fun j => hL _
  have hHG : ∀ j, armG ρ i j ≤ H := fun j => hH _
  have hHT : ∀ j, armT ρ i j ≤ H := fun j => hH _
  rcases h1 n ρ i H L hlip hcr hL hH hLH with ⟨hokG, hokT⟩ | ⟨hokG, hokT⟩
  · -- the Λ case
    obtain ⟨hvG, hvT⟩ := h2 n ρ i H L hlip hcr hL hH hLH
    refine Or.inl ⟨?_, ?_⟩
    · exact segLam_of_okLam hmG (ρ i) H L _ (armG_isLip hlip i) h0G hLG hHG
        (le_hStar ρ i H L) (hStar_dem_armG ρ i H L) hokG hvG
    · exact segLam_of_okLam hmT (ρ i) H L _ (armT_isLip hlip i) h0T hLT hHT
        (le_hStar ρ i H L) (hStar_dem_armT ρ i H L) hokT hvT
  · -- the V case: the same lemmas applied to the negated arms
    obtain ⟨hvG, hvT⟩ := h3 n ρ i H L hlip hcr hL hH hLH
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

end HPC.Fold
