import HPC.Fold.Closure

/-!
# All three tight conjectures are false, and so is the one-bump folding condition itself

**Counterexamples first, as the commission asks.** All three tight statements posed for this
batch are refuted by explicit down-crooked 1-Lipschitz sequences *with both extremes attained*,
so the attainment hypotheses added in batch 18 were necessary but are not sufficient. With them
falls `F2PrimeTight`, and — the substantive point — so does `F2PrimeFree`, the form of the
folding condition in which the bump height, the valley depth and the bounds `H`, `L` are all
existentially quantified over exactly what `exists_blocks_first_of_segLam` and
`exists_blocks_first_of_segVee` require. The failure is therefore not about how `hStar` and
`lStar` are computed: at the basepoint below there is *no* one-bump fold at all.

The witnesses, all with `H = max ρ` and `L = min ρ`:

* `ρ = 5,4,3,3,2,3,2,1,2,3,2,1,1,0`, basepoint `5`, `p = 3`, `H = 5`, `L = 0`
  — refutes `ExitReachTight`, `F2PrimeTight` and `F2PrimeFree`;
* `ρ = 3,4,4,5,6,5,4,4,3,4,3,2,3,4,3,2,2,1`, basepoint `2`, `p = 4`, `H = 6`, `L = 1`
  — refutes `LowExitPeakTight`;
* `ρ = 6,5,4,4,3,4,3,2,3,4,3,2,2,1,2,2,3,4,3,2,2,1,2,1,0`, basepoint `9`, `p = 4`, `H = 6`,
  `L = 0` — refutes `HighExitValleyOpenTight`, hence `HighExitValleyTight`.

## What goes wrong

At the first witness the two arms are

    G = 3,2,1,2,3,2,1,1,0        T = 3,2,3,3,4,5

and the Λ side and the V side each split the two arms apart, at *every* admissible height:

* `SegLam G` forces `hb ≤ 3`, because `G` leaves the window below at index `2` and so cannot
  have a peak index after it, while `SegLam T` forces `hb ≥ 4`, because at a lower height `T`
  must close its excursion at a level `≤ L + 1 = 1`, and `T` never descends below `2`;
* dually `SegVee T` forces `lb ≥ 2` — the negated arm's phase-adjusted reach is `−2` — while
  `SegVee G` fails for every `lb ≥ 2`, since the negated arm would have to close at `H − 1 = 4`
  or above after its peak, and from the peak on it never exceeds `3`.

Since `hb` and `lb` are pinned in the batch-18 statements at `hStar = 4` and `lStar = 1`, the
same basepoint also refutes `ExitReachTight` and `F2PrimeTight`, by the reaches
`hReach G = 3 < 4` and `hReach (−T) = −2 < −1`.

The other two witnesses are the valley and peak clauses failing with bite: in the third, both
demands are `4`, the cap `max (H − 1) p = 5` does not bind — so the basepoint is open and
batch 17's shrinking does not apply — index `0` is admissible on the backward arm, which rises
to `6 > hStar + 1` while never visiting `L + 1 = 1`.

## What survives

`theorem3_of_F2PrimeFree` is proved: Bing 1948, Theorem 3 in the block reading still follows
from the free folding condition, exactly as it followed from `F2PrimeTight`. But the hypothesis
is now known to be false, so the derivation of Theorem 3 by one-bump folds at an arbitrary
basepoint is closed off: any repair has to leave the family of fold targets used since batch 6.

English sketches: COMMISSION-batch19.md §3.
-/

namespace HPC.Fold

/-! ## Two general tools -/

/-- A bound on the phase-adjusted levels *of the indices whose predecessors stay in the window*
bounds `hReach`. This refines `hReach_le_of_all`, whose hypothesis is the unconditional bound;
the first witness below needs the conditional form, since its arm climbs back to the basepoint
level after leaving the window. -/
theorem hReach_le_of_pre {m : ℕ} {A : Fin m → ℤ} (hm : 0 < m) (p c : ℤ) (h0 : A ⟨0, hm⟩ = p)
    (hub : ∀ k : Fin m, (∀ k' : Fin m, k' ≤ k → p - 1 ≤ A k') → A k + phase A k ≤ c) :
    hReach A p ≤ c := by
  classical
  set S : Set ℤ :=
    {v : ℤ | ∃ j : Fin m, A j + phase A j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ A j'}
  have hne : S.Nonempty := by
    refine ⟨A ⟨0, hm⟩ + phase A ⟨0, hm⟩, ⟨0, hm⟩, rfl, fun j' hj' => ?_⟩
    have hj'z : j'.val ≤ 0 := Fin.le_def.1 hj'
    rw [show j' = (⟨0, hm⟩ : Fin m) from Fin.ext (show j'.val = 0 by omega), h0]
    omega
  refine csSup_le hne ?_
  rintro v ⟨j, rfl, hj⟩
  exact hub j hj

/-- `SegLam` fails if the arm leaves the window `[p − 1, h + 1]` somewhere and every peak index
has a window violation strictly before it. This generalizes `not_segLam_of_no_peak`, which is
the case where there is no peak index at all. -/
theorem not_segLam_of_window_or_peak {m : ℕ} (f : Fin m → ℤ) (p H L h : ℤ)
    (hbad : ∃ j : Fin m, f j < p - 1 ∨ h + 1 < f j)
    (hno : ∀ s : Fin m, h ≤ f s + phase f s →
      ∃ j : Fin m, j.val < s.val ∧ (f j < p - 1 ∨ h + 1 < f j)) :
    ¬ SegLam f p H L h := by
  rintro ⟨s, t, hst, htm, h1, h2, -, -, -⟩
  by_cases hsm : s < m
  · obtain ⟨j, hj, hviol⟩ := hno ⟨s, hsm⟩ (h2 hsm)
    have := h1 j hj
    omega
  · obtain ⟨j, hviol⟩ := hbad
    have hjs : j.val < s := by have := j.isLt; omega
    have := h1 j hjs
    omega

/-! ## Witness 1: `ExitReachTight`, `F2PrimeTight` and `F2PrimeFree`

    ρ = 5,4,3,3,2,3,2,1,2,3,2,1,1,0    basepoint 5,  p = 3,  H = 5,  L = 0

`H = 5` is attained at index 0 and `L = 0` at index 13. The arms are

    G = 3,2,1,2,3,2,1,1,0        T = 3,2,3,3,4,5

with `hStarArm T = 5` and `lStarArm G = 0`, so `hStar = min 5 (max 4 3) = 4` and
`lStar = max 0 (min 1 3) = 1`. -/

def fpSeq : Fin 14 → ℤ := ![5, 4, 3, 3, 2, 3, 2, 1, 2, 3, 2, 1, 1, 0]

/-- Its basepoint. -/
def fpPt : Fin 14 := ⟨5, by omega⟩

@[simp] theorem fpPt_val : fpPt.val = 5 := rfl

/-- The level at the basepoint. -/
theorem fpSeq_pt : fpSeq fpPt = 3 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem fpSeq_isLip : IsLip fpSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [fpSeq]

set_option maxRecDepth 4000000 in
/-- And down-crooked. -/
theorem fpSeq_isCrookedSeq : IsCrookedSeq fpSeq := by unfold IsCrookedSeq; decide

set_option maxRecDepth 10000 in
/-- The backward arm's peak demand. -/
theorem fpSeq_hStarArm_T : hStarArm (armT fpSeq fpPt) 3 = 5 :=
  hStarArm_eq_of_attained _ _ _ ⟨5, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
/-- The forward arm's valley demand, in negated form. -/
theorem fpSeq_hStarArm_negG : hStarArm (fun j => - armG fpSeq fpPt j) (-3) = 0 :=
  hStarArm_eq_of_attained _ _ _ ⟨8, by decide⟩ (by decide) (by decide) (by decide)

/-- The bump height is the cap. -/
theorem fpSeq_hStar : (4 : ℤ) ≤ hStar fpSeq fpPt 5 0 := by
  have h := fpSeq_hStarArm_T
  rw [hStar, fpSeq_pt]
  simp only [le_min_iff, le_max_iff]
  omega

/-- The valley depth is the floor. -/
theorem fpSeq_lStar : lStar fpSeq fpPt 5 0 ≤ 1 := by
  have h : lStarArm (armG fpSeq fpPt) 3 = 0 := by
    rw [lStarArm, fpSeq_hStarArm_negG]; omega
  rw [lStar, fpSeq_pt]
  simp only [max_le_iff, min_le_iff]
  omega

/-- The forward arm leaves the window below at index `2`, so only its first two indices count
towards `hReach`, and there it is phase-adjusted at most `3`. -/
theorem fpSeq_bound_G (k : Fin (14 - fpPt.val))
    (hk : ∀ k' : Fin (14 - fpPt.val), k' ≤ k → (3 : ℤ) - 1 ≤ armG fpSeq fpPt k') :
    armG fpSeq fpPt k + phase (armG fpSeq fpPt) k ≤ 3 := by
  have hd : ∀ k : Fin (14 - fpPt.val),
      (∀ k' : Fin (14 - fpPt.val), k' ≤ k → (3 : ℤ) - 1 ≤ armG fpSeq fpPt k') →
      k.val ≤ 1 := by decide
  have hk1 := hd k hk
  rcases phase_zero_or_one (armG fpSeq fpPt) k with e | e
  · have hb : ∀ k : Fin (14 - fpPt.val), k.val ≤ 1 → armG fpSeq fpPt k ≤ 3 := by decide
    have := hb k hk1
    rw [e]; omega
  · have hpos := pos_of_phase_eq_one _ _ e
    have hb : ∀ k : Fin (14 - fpPt.val), 0 < k.val → k.val ≤ 1 →
        armG fpSeq fpPt k ≤ 2 := by decide
    have := hb k hpos hk1
    rw [e]; omega

/-- The negated backward arm never reaches `−1` in the phase-adjusted sense. -/
theorem fpSeq_bound_negT (k : Fin (fpPt.val + 1)) :
    (- armT fpSeq fpPt k) + phase (fun j => - armT fpSeq fpPt j) k ≤ -2 := by
  have hph : ∀ k : Fin (fpPt.val + 1), k.val ≤ 1 →
      ¬ ∃ t : Fin (fpPt.val + 1), t.val ≤ k.val ∧
        NonAscAt (fun j => - armT fpSeq fpPt j) t := by decide
  by_cases hk : k.val ≤ 1
  · rw [phase_eq_zero _ _ (hph k hk)]
    have hb : ∀ k : Fin (fpPt.val + 1), k.val ≤ 1 → 2 ≤ armT fpSeq fpPt k := by decide
    have := hb k hk
    omega
  · have hb : ∀ k : Fin (fpPt.val + 1), ¬ k.val ≤ 1 → 3 ≤ armT fpSeq fpPt k := by decide
    have := hb k hk
    rcases phase_zero_or_one (fun j => - armT fpSeq fpPt j) k with e | e <;> rw [e] <;> omega

/-- So the forward arm's reach falls one short of `hStar`. -/
theorem fpSeq_hReach_G : hReach (armG fpSeq fpPt) 3 ≤ 3 :=
  hReach_le_of_pre (by decide) 3 3 (by decide) fpSeq_bound_G

/-- And the negated backward arm's reach falls one short of `−lStar`. -/
theorem fpSeq_hReach_negT : hReach (fun j => - armT fpSeq fpPt j) (-3) ≤ -2 :=
  hReach_le_of_all (by decide) (-3) (-2) (by decide) fpSeq_bound_negT

/-- **`ExitReachTight` is false.** -/
theorem not_exitReachTight : ¬ ExitReachTight := by
  intro h
  have key := h 14 fpSeq fpPt 5 0 fpSeq_isLip fpSeq_isCrookedSeq
    (by decide) (by decide) (by norm_num) ⟨⟨13, by decide⟩, by decide⟩ ⟨⟨0, by decide⟩, by decide⟩
  rw [fpSeq_pt] at key
  have hh := fpSeq_hStar
  have hl := fpSeq_lStar
  rcases key with ⟨hG, -⟩ | ⟨-, hT⟩
  · rcases hG with hnd | hr
    · exact hnd ⟨⟨8, by decide⟩, by decide⟩
    · have := fpSeq_hReach_G
      omega
  · rcases hT with hnd | hr
    · exact hnd ⟨⟨5, by decide⟩, by decide⟩
    · have := fpSeq_hReach_negT
      omega

/-- The forward arm has no usable peak index at any height above `3`: every index at which it
is phase-adjusted at least `4` is preceded by index `2`, where it is below `p − 1`. -/
theorem fpSeq_no_peak_G (s : Fin (14 - fpPt.val))
    (hs : (4 : ℤ) ≤ armG fpSeq fpPt s + phase (armG fpSeq fpPt) s) :
    ∃ j : Fin (14 - fpPt.val), j.val < s.val ∧ armG fpSeq fpPt j < (3 : ℤ) - 1 := by
  by_cases hbig : 3 ≤ s.val
  · exact ⟨⟨2, by decide⟩, by show (2 : ℕ) < s.val; omega, by decide⟩
  · exfalso
    rcases phase_zero_or_one (armG fpSeq fpPt) s with e | e
    · have hb : ∀ s : Fin (14 - fpPt.val), ¬ 3 ≤ s.val → armG fpSeq fpPt s ≤ 3 := by decide
      have := hb s hbig
      rw [e] at hs; omega
    · have hpos := pos_of_phase_eq_one _ _ e
      have hb : ∀ s : Fin (14 - fpPt.val), 0 < s.val → ¬ 3 ≤ s.val →
          armG fpSeq fpPt s ≤ 2 := by decide
      have := hb s hpos hbig
      rw [e] at hs; omega

/-- **`F2PrimeTight` is false**, at the same basepoint. -/
theorem not_f2PrimeTight : ¬ F2PrimeTight := by
  intro h
  have key := h 14 fpSeq fpPt 5 0 fpSeq_isLip fpSeq_isCrookedSeq
    (by decide) (by decide) (by norm_num) ⟨⟨13, by decide⟩, by decide⟩ ⟨⟨0, by decide⟩, by decide⟩
  rw [fpSeq_pt] at key
  have hh := fpSeq_hStar
  have hl := fpSeq_lStar
  rcases key with ⟨hG, -⟩ | ⟨-, hT⟩
  · refine not_segLam_of_window_or_peak _ 3 5 0 _
      ⟨⟨2, by decide⟩, Or.inl (by decide)⟩ (fun s hs => ?_) hG
    obtain ⟨j, hj, hviol⟩ := fpSeq_no_peak_G s (by omega)
    exact ⟨j, hj, Or.inl hviol⟩
  · refine not_segLam_of_no_peak _ (-3) 0 (-5) _ (fun j => ?_) ⟨⟨5, by decide⟩, by decide⟩ hT
    have := fpSeq_bound_negT j
    omega

/-! ### The free form fails too

The four lemmas below pin down, for each side of the dichotomy, the exact set of heights and
depths each arm admits; they are disjoint. -/

/-- The forward arm admits no Λ-height above `3`. -/
theorem fpSeq_segLam_G_le (H L hb : ℤ) (h : SegLam (armG fpSeq fpPt) 3 H L hb) : hb ≤ 3 := by
  obtain ⟨s, t, hst, htm, h1, h2, -, -, -⟩ := h
  have hs2 : s ≤ 2 := by
    by_contra hcon
    have h2v : armG fpSeq fpPt ⟨2, by decide⟩ < 3 - 1 := by decide
    have := (h1 ⟨2, by decide⟩ (by show (2 : ℕ) < s; omega)).1
    omega
  have hsm : s < 14 - fpPt.val := by simp only [fpPt_val]; omega
  have hpk := h2 hsm
  rcases phase_zero_or_one (armG fpSeq fpPt) ⟨s, hsm⟩ with e | e
  · have hb : ∀ k : Fin (14 - fpPt.val), k.val ≤ 2 → armG fpSeq fpPt k ≤ 3 := by decide
    have := hb ⟨s, hsm⟩ hs2
    rw [e] at hpk; omega
  · have hpos := pos_of_phase_eq_one _ _ e
    have hb : ∀ k : Fin (14 - fpPt.val), 0 < k.val → k.val ≤ 2 →
        armG fpSeq fpPt k ≤ 2 := by decide
    have := hb ⟨s, hsm⟩ hpos hs2
    rw [e] at hpk; omega

/-- The backward arm admits no Λ-height below `4`. -/
theorem fpSeq_segLam_T_ge (H L hb : ℤ) (hL : L ≤ 0)
    (h : SegLam (armT fpSeq fpPt) 3 H L hb) : 4 ≤ hb := by
  obtain ⟨s, t, hst, htm, -, -, h3, h4, h5⟩ := h
  by_contra hcon
  push_neg at hcon
  have hs0 : s = 0 := by
    by_contra hs
    have h0 : armT fpSeq fpPt ⟨0, by decide⟩ + phase (armT fpSeq fpPt) ⟨0, by decide⟩ = 3 := by
      rw [phase_at_zero]
      decide
    have := h3 ⟨0, by decide⟩ (by show (0 : ℕ) < s; omega)
    omega
  subst hs0
  have hmT : fpPt.val + 1 = 6 := rfl
  have ht5 : t ≤ 5 := by
    by_contra hcon'
    have : (5 : ℕ) < t := by omega
    have := (h4 ⟨5, by decide⟩ (by decide) this).2
    have hv : armT fpSeq fpPt ⟨5, by decide⟩ = 5 := by decide
    omega
  rcases h5 with rfl | ⟨hlt, hlast⟩
  · omega
  · have hb : ∀ j : Fin (fpPt.val + 1), (2 : ℤ) ≤ armT fpSeq fpPt j := by decide
    have hjlt : t - 1 < fpPt.val + 1 := by omega
    have := hlast ⟨t - 1, hjlt⟩ (by show t - 1 + 1 = t; omega)
    have := hb ⟨t - 1, hjlt⟩
    omega

/-- The backward arm admits no V-depth below `2`. -/
theorem fpSeq_segVee_T_ge (H L lb : ℤ) (h : SegVee (armT fpSeq fpPt) 3 H L lb) : 2 ≤ lb := by
  obtain ⟨s, t, hst, htm, h1, h2, -, -, -⟩ := h
  by_cases hsm : s < fpPt.val + 1
  · have hp := h2 hsm
    simp only at hp
    have := fpSeq_bound_negT ⟨s, hsm⟩
    omega
  · have hv : - armT fpSeq fpPt ⟨5, by decide⟩ < -3 - 1 := by decide
    have h1' := (h1 ⟨5, by decide⟩ (by show (5 : ℕ) < s; simp only [fpPt_val] at hsm ⊢; omega)).1
    simp only at h1'
    omega

/-- And the forward arm admits no V-depth at or above `2`. -/
theorem fpSeq_not_segVee_G (H L lb : ℤ) (hH : 5 ≤ H) (hlb : 2 ≤ lb) :
    ¬ SegVee (armG fpSeq fpPt) 3 H L lb := by
  rintro ⟨s, t, hst, htm, -, -, h3, h4, h5⟩
  by_cases hsm : s < 14 - fpPt.val
  · have ht8 : t ≤ 8 := by
      by_contra hcon
      have h8 : (8 : ℕ) < t := by simp only [fpPt_val] at htm; omega
      have h8' := (h4 ⟨8, by decide⟩ (by simp only [fpPt_val] at hsm ⊢; omega) h8).2
      simp only at h8'
      have hv : - armG fpSeq fpPt ⟨8, by decide⟩ = 0 := by decide
      omega
    rcases h5 with rfl | ⟨hlt, hlast⟩
    · simp only [fpPt_val] at ht8; omega
    · have hb : ∀ j : Fin (14 - fpPt.val), (-3 : ℤ) ≤ - armG fpSeq fpPt j := by decide
      have hjlt : t - 1 < 14 - fpPt.val := by simp only [fpPt_val]; omega
      have hlast' := hlast ⟨t - 1, hjlt⟩ (by show t - 1 + 1 = t; omega)
      simp only at hlast'
      have := hb ⟨t - 1, hjlt⟩
      omega
  · have hph : phase (fun j => - armG fpSeq fpPt j) ⟨2, by decide⟩ = 0 := by
      refine phase_eq_zero _ _ ?_
      decide
    have hv : - armG fpSeq fpPt ⟨2, by decide⟩ = -1 := by decide
    have h3' := h3 ⟨2, by decide⟩ (by show (2 : ℕ) < s; simp only [fpPt_val] at hsm ⊢; omega)
    simp only at h3'
    rw [hph, hv] at h3'
    omega

/-- **`F2Prime`, free.** The one-bump folding condition with nothing pinned: the bounds `H` and
`L`, and the bump height `hb`, respectively the valley depth `lb`, are existentially quantified
over exactly the hypotheses of `exists_blocks_first_of_segLam` and
`exists_blocks_first_of_segVee`. It is the weakest form of the condition from which Theorem 3
still follows — and it is false. -/
def F2PrimeFree : Prop :=
  ∀ (n : ℕ) (ρ : Fin n → ℤ) (i : Fin n), IsLip ρ → IsCrookedSeq ρ →
    (∃ H L hb : ℤ, (∀ t, L ≤ ρ t) ∧ (∀ t, ρ t ≤ H) ∧ ρ i ≤ hb ∧ hb ≤ max (H - 1) (ρ i) ∧
        L ≤ ρ i ∧ L + 1 ≤ hb ∧
        SegLam (armG ρ i) (ρ i) H L hb ∧ SegLam (armT ρ i) (ρ i) H L hb) ∨
    (∃ H L lb : ℤ, (∀ t, L ≤ ρ t) ∧ (∀ t, ρ t ≤ H) ∧ lb ≤ ρ i ∧ min (L + 1) (ρ i) ≤ lb ∧
        ρ i ≤ H ∧ lb + 1 ≤ H ∧
        SegVee (armG ρ i) (ρ i) H L lb ∧ SegVee (armT ρ i) (ρ i) H L lb)

/-- **`F2PrimeFree` is false**, at the same basepoint: no height serves both arms on the Λ
side, and no depth serves both on the V side. -/
theorem not_f2PrimeFree : ¬ F2PrimeFree := by
  intro h
  rcases h 14 fpSeq fpPt fpSeq_isLip fpSeq_isCrookedSeq with
    ⟨H, L, hb, hLf, hHf, hph, hcap, hLp, hLh, hG, hT⟩ |
    ⟨H, L, lb, hLf, hHf, hlp, hfl, hpH, hlH, hG, hT⟩
  · rw [fpSeq_pt] at hG hT
    have hL0 : L ≤ 0 := by
      have := hLf ⟨13, by decide⟩
      have hv : fpSeq ⟨13, by decide⟩ = 0 := by decide
      omega
    have h1 := fpSeq_segLam_G_le H L hb hG
    have h2 := fpSeq_segLam_T_ge H L hb hL0 hT
    omega
  · rw [fpSeq_pt] at hG hT
    have hH5 : 5 ≤ H := by
      have := hHf ⟨0, by decide⟩
      have hv : fpSeq ⟨0, by decide⟩ = 5 := by decide
      omega
    exact fpSeq_not_segVee_G H L lb hH5 (fpSeq_segVee_T_ge H L lb hT) hG

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, from `F2PrimeFree`. The proof is
that of `theorem3_of_F2PrimeTight` with the supplied data used in place of the maximum, the
minimum and `hStar`. Since `F2PrimeFree` is false, this is the end of the road for the
one-bump route, not a proof of Theorem 3. -/
theorem theorem3_of_F2PrimeFree (hF2 : F2PrimeFree) {X : Type*} [MetricSpace X] {n k : ℕ}
    (_hn : 0 < n) {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  have hlip : IsLip ρ := by
    intro t t' htt'
    have := minIdx_lip href t t' htt'
    simp only [hρ]
    rw [abs_le]
    omega
  have hcrook : IsCrookedSeq ρ := isCrookedSeq_minIdx hcr
  rcases hF2 n ρ i hlip hcrook with
    ⟨H, L, hb, hLf, hHf, hph, hcap, hLp, hLh, hG, hT⟩ |
    ⟨H, L, lb, hLf, hHf, hlp, hfl, hpH, hlH, hG, hT⟩
  · exact exists_blocks_first_of_segLam href i (ρ i) H L hb rfl hG hT
      (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf hph hcap hLp hLh
  · exact exists_blocks_first_of_segVee href i (ρ i) H L lb rfl hG hT
      (armG_isLip hlip i) (armT_isLip hlip i) hLf hHf hlp hfl hpH hlH

/-! ## Witness 2: `LowExitPeakTight`

    ρ = 3,4,4,5,6,5,4,4,3,4,3,2,3,4,3,2,2,1    basepoint 2,  p = 4,  H = 6,  L = 1

`H = 6` is attained at index 4 and `L = 1` at index 17. The arms are

    G = 4,5,6,5,4,4,3,4,3,2,3,4,3,2,2,1        T = 4,4,3

with `lStarArm G = 4` and `lStarArm T = 3`, so `lStar = 3`. On the forward arm `s = 4` is
admissible — the first four phase-adjusted negated levels are `−4, −4, −5, −4`, all below
`−lStar = −3` — and at `u = 15` the negated arm is at `−1 > −lStar + 1`. The clause then asks
for an index in `[4, 15)` at which the arm is at `H − 1 = 5` or above; from index `4` on the
arm never again exceeds `4`. -/

def lpSeq : Fin 18 → ℤ := ![3, 4, 4, 5, 6, 5, 4, 4, 3, 4, 3, 2, 3, 4, 3, 2, 2, 1]

/-- Its basepoint. -/
def lpPt : Fin 18 := ⟨2, by omega⟩

/-- The level at the basepoint. -/
theorem lpSeq_pt : lpSeq lpPt = 4 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem lpSeq_isLip : IsLip lpSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [lpSeq]

set_option maxRecDepth 4000000 in
/-- And down-crooked. -/
theorem lpSeq_isCrookedSeq : IsCrookedSeq lpSeq := by unfold IsCrookedSeq; decide

set_option maxRecDepth 10000 in
/-- The forward arm's valley demand, in negated form. -/
theorem lpSeq_hStarArm_negG : hStarArm (fun j => - armG lpSeq lpPt j) (-4) = -4 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
/-- The backward arm's valley demand, in negated form. -/
theorem lpSeq_hStarArm_negT : hStarArm (fun j => - armT lpSeq lpPt j) (-4) = -3 :=
  hStarArm_eq_of_attained _ _ _ ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- The valley depth, exactly. -/
theorem lpSeq_lStar : lStar lpSeq lpPt 6 1 = 3 := by
  have hG : lStarArm (armG lpSeq lpPt) 4 = 4 := by
    rw [lStarArm, lpSeq_hStarArm_negG]; omega
  have hT : lStarArm (armT lpSeq lpPt) 4 = 3 := by
    rw [lStarArm, lpSeq_hStarArm_negT]; omega
  rw [lStar, lpSeq_pt, hG, hT]
  decide

/-- Index `4` is an admissible peak index for the negated forward arm. -/
theorem lpSeq_admissible (j : Fin (18 - lpPt.val)) (hj : j.val < 4) :
    (- armG lpSeq lpPt j) + phase (fun j' => - armG lpSeq lpPt j') j < -3 := by
  rcases phase_zero_or_one (fun j' => - armG lpSeq lpPt j') j with e | e
  · have hb : ∀ j : Fin (18 - lpPt.val), j.val < 4 → - armG lpSeq lpPt j ≤ -4 := by decide
    have := hb j hj
    rw [e]; omega
  · have hpos := pos_of_phase_eq_one _ _ e
    have hb : ∀ j : Fin (18 - lpPt.val), 0 < j.val → j.val < 4 →
        - armG lpSeq lpPt j ≤ -5 := by decide
    have := hb j hpos hj
    rw [e]; omega

/-- **`LowExitPeakTight` is false.** -/
theorem not_lowExitPeakTight : ¬ LowExitPeakTight := by
  intro h
  obtain ⟨hG, -⟩ := h 18 lpSeq lpPt 6 1 lpSeq_isLip lpSeq_isCrookedSeq
    (by decide) (by decide) (by norm_num) ⟨⟨17, by decide⟩, by decide⟩ ⟨⟨4, by decide⟩, by decide⟩
  rw [lpSeq_lStar] at hG
  obtain ⟨j, hj1, hj2, hj3⟩ := hG 4 (fun j hj => lpSeq_admissible j hj) ⟨15, by decide⟩
    (by decide) (by decide)
  have hb : ∀ j : Fin (18 - lpPt.val), 4 ≤ j.val → j.val < 15 →
      ¬ (- armG lpSeq lpPt j ≤ -6 + 1) := by decide
  exact hb j hj1 hj2 hj3

/-! ## Witness 3: `HighExitValleyOpenTight` and `HighExitValleyTight`

    ρ = 6,5,4,4,3,4,3,2,3,4,3,2,2,1,2,2,3,4,3,2,2,1,2,1,0    basepoint 9,
    p = 4,  H = 6,  L = 0

`H = 6` is attained at index 0 and `L = 0` at index 24. Both arms have demand `4`, so
`hStar = 4`, one below the cap `max (H − 1) p = 5`: the basepoint is open, and batch 17's
shrinking does not make the clause vacuous. Index `0` is admissible on the backward arm

    T = 4,3,2,3,4,3,4,4,5,6

— vacuously, there being no earlier index — and at `u = 9` the arm is at `6 > hStar + 1 = 5`.
The clause asks for a visit to `L + 1 = 1` before `u`, and the arm never goes below `2`. -/

def hvSeq : Fin 25 → ℤ :=
  ![6, 5, 4, 4, 3, 4, 3, 2, 3, 4, 3, 2, 2, 1, 2, 2, 3, 4, 3, 2, 2, 1, 2, 1, 0]

/-- Its basepoint. -/
def hvPt : Fin 25 := ⟨9, by omega⟩

/-- The level at the basepoint. -/
theorem hvSeq_pt : hvSeq hvPt = 4 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem hvSeq_isLip : IsLip hvSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [hvSeq]

set_option maxRecDepth 8000000 in
/-- And down-crooked. -/
theorem hvSeq_isCrookedSeq : IsCrookedSeq hvSeq := by unfold IsCrookedSeq; decide

set_option maxRecDepth 40000 in
/-- The forward arm's peak demand. -/
theorem hvSeq_hStarArm_G : hStarArm (armG hvSeq hvPt) 4 = 4 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 40000 in
/-- The backward arm's peak demand. -/
theorem hvSeq_hStarArm_T : hStarArm (armT hvSeq hvPt) 4 = 4 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

/-- The bump height, exactly; it is one below the cap, so the basepoint is open. -/
theorem hvSeq_hStar : hStar hvSeq hvPt 6 0 = 4 := by
  rw [hStar, hvSeq_pt, hvSeq_hStarArm_G, hvSeq_hStarArm_T]
  decide

/-- **`HighExitValleyOpenTight` is false.** -/
theorem not_highExitValleyOpenTight : ¬ HighExitValleyOpenTight := by
  intro h
  obtain ⟨-, hT⟩ := h 25 hvSeq hvPt 6 0 hvSeq_isLip hvSeq_isCrookedSeq
    (by decide) (by decide) (by norm_num) ⟨⟨24, by decide⟩, by decide⟩ ⟨⟨0, by decide⟩, by decide⟩
    (by rw [hvSeq_hStar, hvSeq_pt]; decide)
  rw [hvSeq_hStar] at hT
  obtain ⟨j, -, hj2, hj3⟩ := hT 0 (fun j hj => absurd hj (by omega)) ⟨9, by decide⟩
    (by decide) (by decide)
  have hb : ∀ j : Fin (hvPt.val + 1), j.val < 9 → ¬ (armT hvSeq hvPt j ≤ 0 + 1) := by decide
  exact hb j hj2 hj3

/-- **`HighExitValleyTight` is false**, through batch 17's shrinking. -/
theorem not_highExitValleyTight : ¬ HighExitValleyTight := fun h =>
  not_highExitValleyOpenTight (highExitValleyTight_iff_open.mp h)

-- Commented-out statement `exitReachTight`, `highExitValleyOpenTight`, `lowExitPeakTight`, `highExitValleyTight`, `f2PrimeTight`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
