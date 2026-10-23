import HPC.Fold.Itinerary

/-!
# Folding onto the one-bump itinerary (Lemma F1′)

The Λ-itinerary of `Itinerary.lean` is replaced by a family with an adjustable bump:

    Λ(h) = p ↑ h ↓ L+1 ↑ H−1,    p ≤ h ≤ max (H−1) p.

`Λ(p)` is the V-itinerary, `Λ(H−1)` the three-leg walk, and the old `Λ*` a prefix of
`Λ(H−1)`. The three legs have nested level-regions `[p−1, h+1] ⊆ [L, h+1] ⊆ [L, H]`, so an
arm's fold moves through the legs once, never back. The sufficient condition is that the arm
splits into three consecutive segments lying in those regions, with a peak arrival at the
first seam and a valley arrival at the second.

This is a *sufficient* condition with an explicit assignment, not a characterization. It is
what the corrected dichotomy (F2′, still open) is to be checked against.

English proofs: COMMISSION-batch8.md §3. Delivered complete: no `sorry` remains.

Two corrections to the commissioned statements were forced, both by explicit counterexamples
that are part of the delivery (`segLamC_not_foldsOnto`, `bump_degenerate_not_foldsOnto`):

* the commissioned segmented condition is kept verbatim as `SegLamC`, but it does **not**
  imply a fold: at the second seam it must also be required that the second segment is
  nonempty whenever the third one is used.  `SegLam` is `SegLamC` with that clause added
  (`SegLam_imp_SegLamC` records that the delivered condition is the stronger one);
* `L + 1 ≤ h` is required in `segLam_foldsOnto` (as it already was in `bumpCenter_lip`):
  for `h = L` the walk itself jumps by three and no fold need exist.
-/

namespace HPC.Fold

/-! ## The one-bump itinerary -/

/-- Ascending-leg length: `a = h − p`. -/
def bumpA (p h : ℤ) : ℤ := h - p

/-- Descending-leg length: `b = h − L − 1`, ending at center `L + 1`. -/
def bumpB (h L : ℤ) : ℤ := h - L - 1

/-- Total number of times: `a + b + (H − L − 2) + 1`, clamped at zero. -/
def bumpLen (p H L h : ℤ) : ℕ := (bumpA p h + max (bumpB h L) 0 + max (H - L - 2) 0 + 1).toNat

/-- Centers: `p + u` while `u ≤ a`; `h − (u − a)` while `u ≤ a + b`; `L + 1 + (u − a − b)`
thereafter. -/
def bumpCenter (p H L h : ℤ) (u : ℕ) : ℤ :=
  if (u : ℤ) ≤ bumpA p h then p + u
  else if (u : ℤ) ≤ bumpA p h + bumpB h L then h - ((u : ℤ) - bumpA p h)
  else L + 1 + ((u : ℤ) - bumpA p h - bumpB h L)

/-- The center at an arbitrary time, as a three-way test on an integer equal to that time. -/
theorem bumpCenter_eq (p H L h : ℤ) (u : ℕ) (X : ℤ) (hX : (u : ℤ) = X) :
    bumpCenter p H L h u =
      if X ≤ h - p then p + X
      else if X ≤ (h - p) + (h - L - 1) then h - (X - (h - p))
      else L + 1 + (X - (h - p) - (h - L - 1)) := by
  simp only [bumpCenter, bumpA, bumpB, hX]

theorem bumpCenter_zero (p H L h : ℤ) (hph : p ≤ h) : bumpCenter p H L h 0 = p := by
  rw [bumpCenter_eq p H L h 0 0 (by simp)]
  rw [if_pos (by omega)]
  ring

theorem bumpCenter_lip (p H L h : ℤ) (_hph : p ≤ h) (hL : L + 1 ≤ h) (u : ℕ)
    (_hu : u + 1 < bumpLen p H L h) :
    |bumpCenter p H L h (u + 1) - bumpCenter p H L h u| ≤ 1 := by
  rw [bumpCenter_eq p H L h (u + 1) ((u : ℤ) + 1) (by push_cast; ring),
    bumpCenter_eq p H L h u (u : ℤ) rfl, abs_le]
  have hu0 : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg u
  split_ifs <;> omega

/-- `Λ(κ)` is the old `Λ*` on the first two legs: the one-bump family extends the
Λ-itinerary of batch 6. -/
theorem bumpCenter_eq_lamCenter (p H L : ℤ) (u : ℕ)
    (hu : (u : ℤ) ≤ bumpA p (κ p H) + bumpB (κ p H) L) :
    bumpCenter p H L (κ p H) u = lamCenter p H L u := by
  simp only [bumpA, bumpB] at hu
  simp only [bumpCenter, lamCenter, bumpA, bumpB]
  split_ifs <;> omega

/-! ## The phase, as in F1 -/

open Classical in
/-- `φ j = 1` once a non-ascending step has occurred at or before `j`. -/
noncomputable def phase {m : ℕ} (f : Fin m → ℤ) (j : Fin m) : ℤ :=
  if ∃ t : Fin m, t ≤ j ∧ NonAscAt f t then 1 else 0

theorem phase_eq_one {m : ℕ} (f : Fin m → ℤ) (j : Fin m)
    (hj : ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t) : phase f j = 1 := by
  classical
  obtain ⟨t, ht, hNA⟩ := hj
  exact if_pos ⟨t, Fin.le_def.2 ht, hNA⟩

theorem phase_eq_zero {m : ℕ} (f : Fin m → ℤ) (j : Fin m)
    (hj : ¬ ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t) : phase f j = 0 := by
  classical
  refine if_neg ?_
  rintro ⟨t, ht, hNA⟩
  exact hj ⟨t, Fin.le_def.1 ht, hNA⟩

/-- The phase is `0` or `1`. -/
theorem phase_zero_or_one {m : ℕ} (f : Fin m → ℤ) (j : Fin m) :
    phase f j = 0 ∨ phase f j = 1 := by
  classical
  by_cases hj : ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t
  · exact Or.inr (phase_eq_one f j hj)
  · exact Or.inl (phase_eq_zero f j hj)

theorem phase_zero {m : ℕ} (f : Fin m → ℤ) (hm : 0 < m) : phase f ⟨0, hm⟩ = 0 := by
  refine phase_eq_zero f _ ?_
  rintro ⟨t, ht, hNA⟩
  have h1 : t.val ≤ 0 := ht
  have h2 := hNA.1
  omega

/-- The phase never decreases. -/
theorem phase_mono {m : ℕ} (f : Fin m → ℤ) {j j' : Fin m} (hjj' : j.val ≤ j'.val) :
    phase f j ≤ phase f j' := by
  classical
  by_cases hj : ∃ t : Fin m, t.val ≤ j.val ∧ NonAscAt f t
  · obtain ⟨t, ht, hNA⟩ := hj
    rw [phase_eq_one f j ⟨t, ht, hNA⟩, phase_eq_one f j' ⟨t, by omega, hNA⟩]
  · rw [phase_eq_zero f j hj]
    rcases phase_zero_or_one f j' with h | h <;> omega

/-- At a step where the phase goes `0 → 1` the witness must be the step itself, so `f` does
not ascend there. -/
theorem phase_step_nonasc {m : ℕ} {f : Fin m → ℤ} {j j' : Fin m} (hjj' : j'.val = j.val + 1)
    (hj : phase f j = 0) (hj' : phase f j' = 1) : f j' ≤ f j := by
  classical
  have hex : ∃ t : Fin m, t.val ≤ j'.val ∧ NonAscAt f t := by
    by_contra hno
    rw [phase_eq_zero f j' hno] at hj'
    omega
  obtain ⟨t, ht, hNA⟩ := hex
  by_cases htj : t.val ≤ j.val
  · rw [phase_eq_one f j ⟨t, htj, hNA⟩] at hj; omega
  · rw [show t = j' from Fin.ext (by omega)] at hNA
    exact hNA.2 j (by omega)

/-- `f + φ` is 1-Lipschitz: where `φ` steps up, `f` does not ascend. -/
theorem phase_add_isLip {m : ℕ} {f : Fin m → ℤ} (hf : IsLip f) :
    IsLip (fun j => f j + phase f j) := by
  intro j j' hjj'
  have hfs := hf j j' hjj'
  have hmono := phase_mono f (j := j) (j' := j') (by omega)
  rw [abs_le] at hfs ⊢
  rcases phase_zero_or_one f j with hj | hj <;> rcases phase_zero_or_one f j' with hj' | hj'
  · simp only; omega
  · have := phase_step_nonasc hjj' hj hj'
    simp only; omega
  · simp only; omega
  · simp only; omega

/-! ## The segmented sufficient condition -/

/-- The commissioned segmented condition, kept verbatim for the record. It is *not* by itself
sufficient for a fold: see `segLamC_not_foldsOnto`. The delivered condition `SegLam` adds, at
the second seam, that the middle segment is nonempty. -/
def SegLamC {m : ℕ} (f : Fin m → ℤ) (p H L h : ℤ) : Prop :=
  ∃ s t : ℕ, s ≤ t ∧ t ≤ m ∧
    (∀ j : Fin m, j.val < s → p - 1 ≤ f j ∧ f j ≤ h + 1) ∧
    (∀ hs : s < m, h ≤ f ⟨s, hs⟩ + phase f ⟨s, hs⟩) ∧
    (∀ j : Fin m, j.val < s → f j + phase f j < h) ∧
    (∀ j : Fin m, s ≤ j.val → j.val < t → L ≤ f j ∧ f j ≤ h + 1) ∧
    (t = m ∨ ∀ j : Fin m, j.val + 1 = t → f j ≤ L + 1)

/-- The arm splits at `s ≤ t` into leg-1, leg-2 and leg-3 segments.
* before `s`: levels in `[p−1, h+1]`;
* at `s`: the peak is reached in the phase-adjusted sense, `h ≤ f s + φ s`, and `s` is least
  with that property (so the leg-1 assignment stays below the peak time before it);
* between `s` and `t`: levels in `[L, h+1]`;
* at the second seam: either `t = m` (leg 3 never needed) or the middle segment is nonempty
  and the valley was reached, meaning the level just before `t` is at most `L + 1`.
Levels after `t` are unconstrained beyond `[L, H]`, which holds by hypothesis. -/
def SegLam {m : ℕ} (f : Fin m → ℤ) (p H L h : ℤ) : Prop :=
  ∃ s t : ℕ, s ≤ t ∧ t ≤ m ∧
    (∀ j : Fin m, j.val < s → p - 1 ≤ f j ∧ f j ≤ h + 1) ∧
    (∀ hs : s < m, h ≤ f ⟨s, hs⟩ + phase f ⟨s, hs⟩) ∧
    (∀ j : Fin m, j.val < s → f j + phase f j < h) ∧
    (∀ j : Fin m, s ≤ j.val → j.val < t → L ≤ f j ∧ f j ≤ h + 1) ∧
    (t = m ∨ (s < t ∧ ∀ j : Fin m, j.val + 1 = t → f j ≤ L + 1))

/-- The delivered condition is the stronger one. -/
theorem SegLam_imp_SegLamC {m : ℕ} (f : Fin m → ℤ) (p H L h : ℤ) (hs : SegLam f p H L h) :
    SegLamC f p H L h := by
  obtain ⟨s, t, h1, h2, h3, h4, h5, h6, h7⟩ := hs
  exact ⟨s, t, h1, h2, h3, h4, h5, h6, h7.imp id fun hh => hh.2⟩

/-- **Lemma F1′.** The segmented condition gives a fold onto the one-bump itinerary. -/
theorem segLam_foldsOnto {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L h : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (hLf : ∀ j, L ≤ f j) (hHf : ∀ j, f j ≤ H)
    (hph : p ≤ h) (_hhH : h ≤ max (H - 1) p) (_hLp : L ≤ p) (hLh : L + 1 ≤ h)
    (hseg : SegLam f p H L h) :
    FoldsOnto f (bumpLen p H L h) (bumpCenter p H L h) := by
  classical
  obtain ⟨s, t, hst, htm, hseg1, hseg2, hseg3, hseg4, hseg5⟩ := hseg
  have hglip := phase_add_isLip hf
  -- the integer-valued assignment
  set F : Fin m → ℤ := fun j =>
    if j.val < s then max 0 (f j + phase f j - p)
    else if j.val < t then (h - p) + max 0 (h - 1 - f j)
    else (h - p) + (h - L - 1) + max 0 (f j - (L + 2)) with hF
  have hF1 : ∀ j : Fin m, j.val < s → F j = max 0 (f j + phase f j - p) := by
    intro j hj; simp only [hF]; rw [if_pos hj]
  have hF2 : ∀ j : Fin m, ¬ j.val < s → j.val < t → F j = (h - p) + max 0 (h - 1 - f j) := by
    intro j hj hj'; simp only [hF]; rw [if_neg hj, if_pos hj']
  have hF3 : ∀ j : Fin m, ¬ j.val < s → ¬ j.val < t →
      F j = (h - p) + (h - L - 1) + max 0 (f j - (L + 2)) := by
    intro j hj hj'; simp only [hF]; rw [if_neg hj, if_neg hj']
  -- nonnegativity and the upper bound
  have hnn : ∀ j, 0 ≤ F j := by
    intro j
    by_cases hc1 : j.val < s
    · rw [hF1 j hc1]; omega
    · by_cases hc2 : j.val < t
      · rw [hF2 j hc1 hc2]; omega
      · rw [hF3 j hc1 hc2]; omega
  have hub : ∀ j, F j ≤ (h - p) + (h - L - 1) + max (H - L - 2) 0 := by
    intro j
    have hL1 := hLf j
    have hH1 := hHf j
    by_cases hc1 : j.val < s
    · rw [hF1 j hc1]
      have := hseg3 j hc1
      omega
    · by_cases hc2 : j.val < t
      · rw [hF2 j hc1 hc2]
        have := hseg4 j (by omega) hc2
        omega
      · rw [hF3 j hc1 hc2]; omega
  have hlen : ∀ j, (F j).toNat < bumpLen p H L h := by
    intro j
    have h1 := hnn j
    have h2 := hub j
    simp only [bumpLen, bumpA, bumpB]
    omega
  refine ⟨fun j => (F j).toNat, hlen, ?_, ?_, ?_⟩
  · -- Lipschitz
    intro j j' hjj'
    have hcast : ∀ k : Fin m, ((F k).toNat : ℤ) = F k := fun k => Int.toNat_of_nonneg (hnn k)
    rw [hcast, hcast, abs_le]
    have hfs := hf j j' hjj'
    rw [abs_le] at hfs
    by_cases hc1 : j.val < s
    · by_cases hc1' : j'.val < s
      · -- both in leg 1
        rw [hF1 j hc1, hF1 j' hc1']
        have := hglip j j' hjj'
        simp only at this
        rw [abs_le] at this
        omega
      · -- the first seam
        have hs' : j'.val = s := by omega
        have hsm : s < m := by rw [← hs']; exact j'.isLt
        have hjs : (⟨s, hsm⟩ : Fin m) = j' := Fin.ext hs'.symm
        have hpk : h ≤ f j' + phase f j' := by
          have := hseg2 hsm; rwa [hjs] at this
        have hlow := hseg3 j hc1
        have hgl := hglip j j' hjj'
        simp only at hgl
        rw [abs_le] at hgl
        have hφj := phase_zero_or_one f j
        have hφj' := phase_zero_or_one f j'
        rw [hF1 j hc1]
        by_cases hc2' : j'.val < t
        · rw [hF2 j' hc1' hc2']
          omega
        · -- impossible: `s = t` forces `t = m`
          exfalso
          have hts : t = s := by omega
          rcases hseg5 with h5 | ⟨h5, -⟩
          · have := j'.isLt; omega
          · omega
    · by_cases hc1' : j'.val < s
      · exfalso; omega
      · by_cases hc2 : j.val < t
        · by_cases hc2' : j'.val < t
          · -- both in leg 2
            rw [hF2 j hc1 hc2, hF2 j' hc1' hc2']
            omega
          · -- the second seam
            have ht' : j'.val = t := by omega
            have hvalley : f j ≤ L + 1 := by
              rcases hseg5 with h5 | ⟨-, h5⟩
              · exact absurd (h5 ▸ ht' ▸ j'.isLt) (by omega)
              · exact h5 j (by omega)
            have hL1 := hLf j
            rw [hF2 j hc1 hc2, hF3 j' hc1' hc2']
            omega
        · -- both in leg 3
          have hc2' : ¬ j'.val < t := by omega
          rw [hF3 j hc1 hc2, hF3 j' hc1' hc2']
          omega
  · -- start
    intro j hj
    have hj0 : j = ⟨0, hm⟩ := Fin.ext hj
    subst hj0
    show (F ⟨0, hm⟩).toNat = 0
    have hφ0 : phase f ⟨0, hm⟩ = 0 := phase_zero f hm
    by_cases hc1 : (0 : ℕ) < s
    · rw [hF1 ⟨0, hm⟩ hc1, h0, hφ0]
      simp
    · by_cases hc2 : (0 : ℕ) < t
      · have hsm : s < m := by omega
        have hpk := hseg2 hsm
        rw [show (⟨s, hsm⟩ : Fin m) = ⟨0, hm⟩ from Fin.ext (show s = 0 by omega), hφ0,
          h0] at hpk
        rw [hF2 ⟨0, hm⟩ hc1 hc2, h0]
        omega
      · exfalso
        have hts : t = 0 := by omega
        rcases hseg5 with h5 | ⟨h5, -⟩ <;> omega
  · -- windows
    intro j
    have hcast : ((F j).toNat : ℤ) = F j := Int.toNat_of_nonneg (hnn j)
    rw [bumpCenter_eq p H L h _ (F j) hcast, abs_le]
    have hL1 := hLf j
    have hH1 := hHf j
    by_cases hc1 : j.val < s
    · have hw := hseg1 j hc1
      have hlow := hseg3 j hc1
      have hφj := phase_zero_or_one f j
      rw [hF1 j hc1]
      split_ifs <;> omega
    · by_cases hc2 : j.val < t
      · have hw := hseg4 j (by omega) hc2
        rw [hF2 j hc1 hc2]
        split_ifs <;> omega
      · rw [hF3 j hc1 hc2]
        split_ifs <;> omega

/-- A nondegenerate instance, recording that the segmented condition is satisfiable and that
F1′ really produces a fold: the ascending arm `0, 1, 2` with `p = 0`, `h = 2`, `L = 0`,
`H = 3` splits with `s = 2`, `t = m`. -/
theorem segLam_ascending_example :
    SegLam (fun j : Fin 3 => (j.val : ℤ)) 0 3 0 2 ∧
      FoldsOnto (fun j : Fin 3 => (j.val : ℤ)) (bumpLen 0 3 0 2) (bumpCenter 0 3 0 2) := by
  have hph0 : ∀ j : Fin 3, phase (fun j : Fin 3 => (j.val : ℤ)) j = 0 := by
    intro j
    refine phase_eq_zero _ _ ?_
    rintro ⟨t, ht, htpos, h2⟩
    have := h2 ⟨t.val - 1, by omega⟩ (by simp; omega)
    simp only at this
    omega
  have hseg : SegLam (fun j : Fin 3 => (j.val : ℤ)) 0 3 0 2 := by
    refine ⟨2, 3, by omega, by omega, ?_, ?_, ?_, ?_, Or.inl rfl⟩
    · intro j hj; simp only; omega
    · intro hs; rw [hph0]; simp
    · intro j hj; rw [hph0]; simp only; omega
    · intro j hj hj'; have := j.isLt; simp only; omega
  refine ⟨hseg, segLam_foldsOnto (by omega) _ ?_ 0 3 0 2 rfl (fun j => by positivity)
    (fun j => by have := j.isLt; omega) (by omega) (by omega) (by omega) (by omega) hseg⟩
  intro j j' hjj'
  simp only
  rw [hjj']
  push_cast
  rw [abs_le]
  omega

/-! ### The two commissioned statements that fail, with their counterexamples -/

/-- The commissioned condition `SegLamC` does not imply a fold. With `p = h = 3`, `L = 0`,
`H = 6` the arm `3, 4, 5, 6` satisfies `SegLamC` with `s = t = 0` (all its clauses being
vacuous), but it cannot fold: the walk descends to `1` before it climbs, and the arm never
descends. This is why `SegLam` asks for a nonempty middle segment at the second seam. -/
theorem segLamC_not_foldsOnto :
    ∃ (m : ℕ) (_ : 0 < m) (f : Fin m → ℤ) (p H L h : ℤ),
      IsLip f ∧ (∀ hm : 0 < m, f ⟨0, hm⟩ = p) ∧ (∀ j, L ≤ f j) ∧ (∀ j, f j ≤ H) ∧
        p ≤ h ∧ h ≤ max (H - 1) p ∧ L ≤ p ∧ L + 1 ≤ h ∧
        SegLamC f p H L h ∧ ¬ FoldsOnto f (bumpLen p H L h) (bumpCenter p H L h) := by
  classical
  refine ⟨4, by omega, fun j => 3 + (j.val : ℤ), 3, 6, 0, 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro j j' hjj'; simp only; rw [hjj']; push_cast; rw [abs_le]; omega
  · intro _; simp
  · intro j; simp only; positivity
  · intro j; have := j.isLt; simp only; omega
  · omega
  · omega
  · omega
  · omega
  · -- `s = t = 0`
    exact ⟨0, 0, le_rfl, by omega, by rintro j ⟨⟩, by
      intro hs
      have := phase_zero (fun j : Fin 4 => 3 + (j.val : ℤ)) (by omega)
      rw [show (⟨0, hs⟩ : Fin 4) = ⟨0, by omega⟩ from Fin.ext rfl, this]
      norm_num, by rintro j ⟨⟩, by intro j hj hj'; omega, Or.inr (by intro j hj; omega)⟩
  · -- no fold
    rintro ⟨β, hlt, hlip, hz, hw⟩
    have hlen : bumpLen 3 6 0 3 = 7 := by decide
    have hc0 : bumpCenter 3 6 0 3 0 = 3 := by decide
    have hc1 : bumpCenter 3 6 0 3 1 = 2 := by decide
    have hβ0 : β ⟨0, by omega⟩ = 0 := hz _ rfl
    have h1 := hlip ⟨0, by omega⟩ ⟨1, by omega⟩ rfl
    have h2 := hlip ⟨1, by omega⟩ ⟨2, by omega⟩ rfl
    rw [hβ0] at h1
    rw [abs_le] at h1 h2
    -- `β 1 ≤ 1`, and the window at index 1 rules out `β 1 = 1`
    have hb1 : β ⟨1, by omega⟩ = 0 := by
      rcases Nat.lt_or_ge (β ⟨1, by omega⟩) 1 with hlt1 | hge1
      · omega
      · exfalso
        have : β ⟨1, by omega⟩ = 1 := by omega
        have hwin := hw ⟨1, by omega⟩
        rw [this, hc1] at hwin
        simp only at hwin
        rw [abs_le] at hwin
        norm_num at hwin
    rw [hb1] at h2
    have hwin2 := hw ⟨2, by omega⟩
    simp only at hwin2
    rw [abs_le] at hwin2
    rcases Nat.lt_or_ge (β ⟨2, by omega⟩) 1 with hlt2 | hge2
    · have : β ⟨2, by omega⟩ = 0 := by omega
      rw [this, hc0] at hwin2
      norm_num at hwin2
    · have : β ⟨2, by omega⟩ = 1 := by omega
      rw [this, hc1] at hwin2
      norm_num at hwin2

/-- The hypothesis `L + 1 ≤ h` of `segLam_foldsOnto` cannot be dropped. With `p = h = L = 0`
and `H = 2` the walk consists of the single center `0`, while the arm `0, 1, 2` satisfies
`SegLam` with `s = 0`, `t = 2`. -/
theorem bump_degenerate_not_foldsOnto :
    ∃ (m : ℕ) (_ : 0 < m) (f : Fin m → ℤ) (p H L h : ℤ),
      IsLip f ∧ (∀ hm : 0 < m, f ⟨0, hm⟩ = p) ∧ (∀ j, L ≤ f j) ∧ (∀ j, f j ≤ H) ∧
        p ≤ h ∧ h ≤ max (H - 1) p ∧ L ≤ p ∧
        SegLam f p H L h ∧ ¬ FoldsOnto f (bumpLen p H L h) (bumpCenter p H L h) := by
  classical
  refine ⟨3, by omega, fun j => (j.val : ℤ), 0, 2, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j j' hjj'; simp only; rw [hjj']; push_cast; rw [abs_le]; omega
  · intro _; simp
  · intro j; simp only; positivity
  · intro j; have := j.isLt; simp only; omega
  · omega
  · omega
  · omega
  · -- `s = 0`, `t = 2`
    refine ⟨0, 2, by omega, by omega, by rintro j ⟨⟩, ?_, by rintro j ⟨⟩, ?_,
      Or.inr ⟨by omega, ?_⟩⟩
    · intro hs
      have := phase_zero (fun j : Fin 3 => (j.val : ℤ)) (by omega)
      rw [show (⟨0, hs⟩ : Fin 3) = ⟨0, by omega⟩ from Fin.ext rfl, this]
      norm_num
    · intro j hj hj'; have := j.isLt; simp only; omega
    · intro j hj; simp only; omega
  · -- no fold: the walk has one time
    rintro ⟨β, hlt, hlip, hz, hw⟩
    have hlen : bumpLen 0 2 0 0 = 1 := by decide
    have hβ2 : β ⟨2, by omega⟩ = 0 := by have := hlt ⟨2, by omega⟩; omega
    have hwin := hw ⟨2, by omega⟩
    rw [hβ2, show bumpCenter 0 2 0 0 0 = 0 from by decide] at hwin
    simp only at hwin
    rw [abs_le] at hwin
    norm_num at hwin

/-! ## The reflected family -/

def veeBumpLen (p H L l : ℤ) : ℕ := bumpLen (-p) (-L) (-H) (-l)
def veeBumpCenter (p H L l : ℤ) (u : ℕ) : ℤ := - bumpCenter (-p) (-L) (-H) (-l) u
def SegVee {m : ℕ} (f : Fin m → ℤ) (p H L l : ℤ) : Prop :=
  SegLam (fun j => - f j) (-p) (-L) (-H) (-l)

theorem segVee_foldsOnto {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (p H L l : ℤ)
    (h0 : f ⟨0, hm⟩ = p) (hLf : ∀ j, L ≤ f j) (hHf : ∀ j, f j ≤ H)
    (hlp : l ≤ p) (hLl : min (L + 1) p ≤ l) (hpH : p ≤ H) (hlH : l + 1 ≤ H)
    (hseg : SegVee f p H L l) :
    FoldsOnto f (veeBumpLen p H L l) (veeBumpCenter p H L l) := by
  have hneg : IsLip (fun j => - f j) := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [abs_le] at this ⊢
    omega
  have key := segLam_foldsOnto hm (fun j => - f j) hneg (-p) (-L) (-H) (-l)
    (by simp only; rw [h0]) (fun j => by simp only; have := hHf j; omega)
    (fun j => by simp only; have := hLf j; omega) (by omega)
    (by simp only [le_max_iff] at *; omega) (by omega) (by omega) hseg
  show FoldsOnto f (bumpLen (-p) (-L) (-H) (-l))
    (fun u => - bumpCenter (-p) (-L) (-H) (-l) u)
  rw [foldsOnto_neg]
  exact key

/-! ## Consequence for chains -/

open HPC.Chain in
/-- If both arms of the minimal-index sequence satisfy the segmented condition at a common
bump height, then `E` has a block consolidation with every block inside three consecutive
links of `D` and `d_i` in the first block. Bing 1948 Theorem 3, block reading, three-link
form — conditional on the segmented condition, which F2′ is to supply. -/
theorem exists_blocks_first_of_segLam {X : Type*} [MetricSpace X] {n k : ℕ}
    {E : Chain X n} {D : Chain X k} (h : E.Refines D) (i : Fin n) (p H L hb : ℤ)
    (hp : p = (h.minIdx i : ℤ))
    (hG : SegLam (armG (fun t => (h.minIdx t : ℤ)) i) p H L hb)
    (hT : SegLam (armT (fun t => (h.minIdx t : ℤ)) i) p H L hb)
    (hGlip : IsLip (armG (fun t => (h.minIdx t : ℤ)) i))
    (hTlip : IsLip (armT (fun t => (h.minIdx t : ℤ)) i))
    (hLf : ∀ t, L ≤ (h.minIdx t : ℤ)) (hHf : ∀ t, (h.minIdx t : ℤ) ≤ H)
    (hph : p ≤ hb) (hhH : hb ≤ max (H - 1) p) (hLp : L ≤ p) (hLh : L + 1 ≤ hb) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG (fun t => (h.minIdx t : ℤ)) i ⟨0, hmG⟩ = p := by
    simp only [armG]
    rw [hp]
    congr 2
  have hT0 : armT (fun t => (h.minIdx t : ℤ)) i ⟨0, hmT⟩ = p := by
    simp only [armT]
    rw [hp]
    congr 2
  have hfoldG := segLam_foldsOnto hmG _ hGlip p H L hb hG0
    (fun j => hLf _) (fun j => hHf _) hph hhH hLp hLh hG
  have hfoldT := segLam_foldsOnto hmT _ hTlip p H L hb hT0
    (fun j => hLf _) (fun j => hHf _) hph hhH hLp hLh hT
  exact exists_blocks_first_of_folds h i (bumpLen p H L hb) (bumpCenter p H L hb)
    hfoldG hfoldT

end HPC.Fold
