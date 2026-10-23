import HPC.Fold.OffCenter

/-!
# `OffDichotomy`

Batch 24 reduced `F2PrimeOff` to `OffDichotomy`: at every basepoint of a faithful crooked
sequence with attained extremes, for one base center `c ∈ {p − 1, p, p + 1}`, both arms satisfy
`BottomOnTime c L` or both satisfy `TopOnTime c H`. This file poses it, with the corollaries.

Delivered in this batch: the single-arm exit lemma off center (`arm_first_exit`), the two
trivial criteria (`bottomOnTime_of_le`, `topOnTime_of_ge`), the *near-extreme* case of the
dichotomy — every basepoint whose level is within **two** of an extreme
(`offDichotomyAt_near_extreme`), which strengthens batch 24's monotone case from one to two and
settles every span up to five (`f2PrimeOff_near_extreme`, `f2PrimeOff_span_five`) — and the
reduction of `OffDichotomy` to its interior basepoints (`offDichotomy_of_interior`).

`offDichotomy` itself is **false**: `HPC/Fold/DichotomyWitness.lean` exhibits a basepoint of
Bing's 409-link chain `bing 0 8` at which no base center works, and
`HPC/Fold/DichotomyFaithful.lean` proves that chain faithful, hence `not_offDichotomy`. It is
kept, commented out, at the end, together with the two statements that would have followed
from it. No `sorry` remains.

English sketch: COMMISSION-batch25.md §3.
-/

namespace HPC.Fold

/-! ## The single-arm exit lemma, off center -/

/-- **The single-arm exit lemma, off center.** No arm both rises above `c + 1` and falls below
`c − 1` before whichever of the two happens first; consequently every arm has a first exit
direction or none. Stated as the disjunction the dichotomy needs.

The commissioned form carried the hypotheses `IsLip f` and `|f k − c| ≤ 1` at the initial
index; as COMMISSION-batch25.md §3.1 anticipates for the first, neither is used, and both are
dropped. -/
theorem arm_first_exit {m : ℕ} (f : Fin m → ℤ) (c : ℤ) :
    (∀ k, f k ≤ c + 1) ∨ (∀ k, c - 1 ≤ f k) ∨
    (∃ j : Fin m, c + 1 < f j ∧ ∀ k, k ≤ j → c - 1 ≤ f k) ∨
    (∃ j : Fin m, f j < c - 1 ∧ ∀ k, k ≤ j → f k ≤ c + 1) := by
  classical
  by_cases hup : ∃ j : Fin m, c + 1 < f j
  · by_cases hdn : ∃ j : Fin m, f j < c - 1
    · obtain ⟨a, ha⟩ := hup
      obtain ⟨b, hb⟩ := hdn
      have hu : ∃ n : ℕ, ∃ h : n < m, c + 1 < f ⟨n, h⟩ := ⟨a.val, a.isLt, by simpa using ha⟩
      have hd : ∃ n : ℕ, ∃ h : n < m, f ⟨n, h⟩ < c - 1 := ⟨b.val, b.isLt, by simpa using hb⟩
      obtain ⟨hu1, hu2⟩ := Nat.find_spec hu
      obtain ⟨hd1, hd2⟩ := Nat.find_spec hd
      rcases lt_trichotomy (Nat.find hu) (Nat.find hd) with hlt | heq | hgt
      · -- the first exit is upward: nothing has fallen below `c − 1` yet
        refine Or.inr (Or.inr (Or.inl ⟨⟨Nat.find hu, hu1⟩, hu2, ?_⟩))
        intro k hk
        by_contra hcon
        push_neg at hcon
        have : Nat.find hd ≤ k.val := Nat.find_le ⟨k.isLt, by simpa using hcon⟩
        have hk' : k.val ≤ Nat.find hu := hk
        omega
      · exfalso
        have he : (⟨Nat.find hu, hu1⟩ : Fin m) = ⟨Nat.find hd, hd1⟩ := by simp [heq]
        rw [he] at hu2
        omega
      · -- the first exit is downward
        refine Or.inr (Or.inr (Or.inr ⟨⟨Nat.find hd, hd1⟩, hd2, ?_⟩))
        intro k hk
        by_contra hcon
        push_neg at hcon
        have : Nat.find hu ≤ k.val := Nat.find_le ⟨k.isLt, by simpa using hcon⟩
        have hk' : k.val ≤ Nat.find hd := hk
        omega
    · push_neg at hdn
      exact Or.inr (Or.inl hdn)
  · push_neg at hup
    exact Or.inl hup

/-! ## The two criteria in their trivial cases -/

/-- An arm that never rises above `c₀ + 1` is on time at the bottom: the first clause of the
definition. -/
theorem bottomOnTime_of_le {m : ℕ} {f : Fin m → ℤ} {c₀ L : ℤ} (h : ∀ k, f k ≤ c₀ + 1) :
    BottomOnTime f c₀ L := Or.inl h

/-- An arm that never falls below `c₀ − 1` is on time at the top. -/
theorem topOnTime_of_ge {m : ℕ} {f : Fin m → ℤ} {c₀ H : ℤ} (h : ∀ k, c₀ - 1 ≤ f k) :
    TopOnTime f c₀ H :=
  Or.inl fun k => by
    have := h k
    show - f k ≤ - c₀ + 1
    omega

/-! ## Refuting the two criteria -/

/-- **Refuting `BottomOnTime`.** If the arm rises above `c + 1` at some index `u`, and at every
admissible index before `u` it is still above the bottom band, then it is not on time at the
bottom: no crossing index can be at or after `u` (the window is broken there), and none before
`u` is in the band. -/
theorem not_bottomOnTime_of_rise {m : ℕ} {f : Fin m → ℤ} {c L : ℤ} (u : Fin m)
    (hu : c + 1 < f u)
    (hpre : ∀ j : Fin m, (c - L - 2).toNat + 1 ≤ j.val → j.val < u.val → min (L + 2) c < f j) :
    ¬ BottomOnTime f c L := by
  rintro (h | ⟨j, hj, hall⟩)
  · exact absurd (h u) (by omega)
  · by_cases hle : u.val ≤ j.val
    · exact absurd (hall u hle).1 (by omega)
    · have h1 := (hall j le_rfl).2
      have h2 := hpre j hj (by omega)
      simp only [sub_self, add_zero] at h1
      omega

/-- **Refuting `TopOnTime`**, by reflection. -/
theorem not_topOnTime_of_fall {m : ℕ} {f : Fin m → ℤ} {c H : ℤ} (u : Fin m)
    (hu : f u < c - 1)
    (hpre : ∀ j : Fin m, (H - c - 2).toNat + 1 ≤ j.val → j.val < u.val → f j < max (H - 2) c) :
    ¬ TopOnTime f c H := by
  refine not_bottomOnTime_of_rise (f := fun k => - f k) (c := -c) (L := -H) u (by simp; omega) ?_
  intro j h1 h2
  have hidx : (-c - -H - 2 : ℤ) = H - c - 2 := by ring
  rw [hidx] at h1
  have := hpre j h1 h2
  have hmm : min (-H + 2) (-c) = - max (H - 2) c := by omega
  show min (-H + 2) (-c) < - f j
  rw [hmm]
  omega

/-! ## The dichotomy at one basepoint -/

/-- The conclusion of `OffDichotomy` at a single basepoint. -/
def OffDichotomyAt {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ) : Prop :=
  ∃ c₀ : ℤ, (c₀ = ρ i - 1 ∨ c₀ = ρ i ∨ c₀ = ρ i + 1) ∧ L + 1 ≤ c₀ ∧ c₀ ≤ H - 1 ∧
    ((BottomOnTime (armG ρ i) c₀ L ∧ BottomOnTime (armT ρ i) c₀ L) ∨
     (TopOnTime (armG ρ i) c₀ H ∧ TopOnTime (armT ρ i) c₀ H))

/-- **The near-extreme case of the dichotomy.** At a basepoint whose level is within *two* of
an extreme the dichotomy holds outright, and with the trivial clause of the criterion: at
`c₀ = L + 1` no arm can fall below `c₀ − 1 = L`, and at `c₀ = H − 1` none can rise above
`c₀ + 1 = H`. No crookedness, and no Lipschitz condition, is needed. -/
theorem offDichotomyAt_near_extreme {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i) :
    OffDichotomyAt ρ i H L := by
  have hi := hLb i
  have hi' := hHb i
  rcases hnear with hlow | hhigh
  · refine ⟨L + 1, by omega, le_rfl, by omega, Or.inr ⟨?_, ?_⟩⟩
    · refine topOnTime_of_ge fun k => ?_
      have : L ≤ armG ρ i k := hLb _
      omega
    · refine topOnTime_of_ge fun k => ?_
      have : L ≤ armT ρ i k := hLb _
      omega
  · refine ⟨H - 1, by omega, by omega, le_rfl, Or.inl ⟨?_, ?_⟩⟩
    · refine bottomOnTime_of_le fun k => ?_
      have : armG ρ i k ≤ H := hHb _
      omega
    · refine bottomOnTime_of_le fun k => ?_
      have : armT ρ i k ≤ H := hHb _
      omega

/-- The pointwise reduction: the dichotomy at a basepoint gives `F2PrimeOff`'s conclusion
there, through the two ladder folds of batch 24. -/
theorem f2PrimeOff_of_offDichotomyAt {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hd : OffDichotomyAt ρ i H L) :
    ∃ c₀ : ℤ, (c₀ = ρ i - 1 ∨ c₀ = ρ i ∨ c₀ = ρ i + 1) ∧ L + 1 ≤ c₀ ∧ c₀ ≤ H - 1 ∧
      ((∃ h, c₀ ≤ h ∧ h ≤ H - 1 ∧
          FoldsOnto (armG ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2 ∧
          FoldsOnto (armT ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2) ∨
       (∃ l, L + 1 ≤ l ∧ l ≤ c₀ ∧
          FoldsOnto (armG ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2 ∧
          FoldsOnto (armT ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2)) := by
  obtain ⟨c₀, hc₀, hc₀L, hc₀H, hcase⟩ := hd
  have hGL : ∀ k, L ≤ armG ρ i k := fun k => hLb _
  have hGH : ∀ k, armG ρ i k ≤ H := fun k => hHb _
  have hTL : ∀ k, L ≤ armT ρ i k := fun k => hLb _
  have hTH : ∀ k, armT ρ i k ≤ H := fun k => hHb _
  have hG0 : ∀ k : Fin (n - i.val), k.val = 0 → |armG ρ i k - c₀| ≤ 1 := by
    intro k hk
    rw [armG_zero ρ i k hk, abs_le]
    omega
  have hT0 : ∀ k : Fin (i.val + 1), k.val = 0 → |armT ρ i k - c₀| ≤ 1 := by
    intro k hk
    rw [armT_zero ρ i k hk, abs_le]
    omega
  refine ⟨c₀, hc₀, hc₀L, hc₀H, ?_⟩
  rcases hcase with ⟨hBG, hBT⟩ | ⟨hTG, hTT⟩
  · exact Or.inl ⟨c₀, le_rfl, hc₀H,
      foldsOnto_offLam_self _ (armG_isLip hlip i) c₀ L H hc₀L hc₀H hLH hGL hGH hG0 hBG,
      foldsOnto_offLam_self _ (armT_isLip hlip i) c₀ L H hc₀L hc₀H hLH hTL hTH hT0 hBT⟩
  · exact Or.inr ⟨c₀, hc₀L, le_rfl,
      foldsOnto_offVee_self _ (armG_isLip hlip i) c₀ L H hc₀L hc₀H hLH hGL hGH hG0 hTG,
      foldsOnto_offVee_self _ (armT_isLip hlip i) c₀ L H hc₀L hc₀H hLH hTL hTH hT0 hTT⟩

/-- **`F2PrimeOff` near an extreme.** At a basepoint whose level is within two of an extreme
the conclusion of `F2PrimeOff` holds, on a self-ladder. This strengthens batch 24's
`f2PrimeOff_monotone`, which needed the level within one. -/
theorem f2PrimeOff_near_extreme {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i) :
    ∃ c₀ : ℤ, (c₀ = ρ i - 1 ∨ c₀ = ρ i ∨ c₀ = ρ i + 1) ∧ L + 1 ≤ c₀ ∧ c₀ ≤ H - 1 ∧
      ((∃ h, c₀ ≤ h ∧ h ≤ H - 1 ∧
          FoldsOnto (armG ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2 ∧
          FoldsOnto (armT ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2) ∨
       (∃ l, L + 1 ≤ l ∧ l ≤ c₀ ∧
          FoldsOnto (armG ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2 ∧
          FoldsOnto (armT ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2)) :=
  f2PrimeOff_of_offDichotomyAt ρ i H L hlip hLb hHb hLH
    (offDichotomyAt_near_extreme ρ i H L hLb hHb hLH hnear)

/-- **`F2PrimeOff` up to span five.** With `H ≤ L + 5` every basepoint level is within two of
an extreme, so the conclusion holds at every basepoint, with no crookedness. This subsumes
batch 24's `f2PrimeOff_span_three`. -/
theorem f2PrimeOff_span_five {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H) (hLH : L + 3 ≤ H)
    (hspan : H ≤ L + 5) :
    ∃ c₀ : ℤ, (c₀ = ρ i - 1 ∨ c₀ = ρ i ∨ c₀ = ρ i + 1) ∧ L + 1 ≤ c₀ ∧ c₀ ≤ H - 1 ∧
      ((∃ h, c₀ ≤ h ∧ h ≤ H - 1 ∧
          FoldsOnto (armG ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2 ∧
          FoldsOnto (armT ρ i) (offLam c₀ h L H).1 (offLam c₀ h L H).2) ∨
       (∃ l, L + 1 ≤ l ∧ l ≤ c₀ ∧
          FoldsOnto (armG ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2 ∧
          FoldsOnto (armT ρ i) (offVee c₀ l L H).1 (offVee c₀ l L H).2)) :=
  f2PrimeOff_near_extreme ρ i H L hlip hLb hHb hLH (by
    rcases le_or_gt (ρ i) (L + 2) with h | h
    · exact Or.inl h
    · exact Or.inr (by omega))

/-! ## What is left of the dichotomy

Only the interior basepoints — level at least three above the bottom and three below the top,
hence only spans six and above. -/

/-- **The reduction of `OffDichotomy` to its interior basepoints.** It is in the interior that
the statement fails: the counterexample of `HPC/Fold/DichotomyWitness.lean` is at level three
above the bottom and five below the top. -/
theorem offDichotomy_of_interior
    (h : ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
      IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H →
      (∃ t, ρ t = L) → (∃ t, ρ t = H) → L + 3 ≤ ρ i → ρ i ≤ H - 3 →
      OffDichotomyAt ρ i H L) :
    OffDichotomy := by
  intro n ρ σ i H L hlip hcr hLb hHb hLH hL hH
  rcases le_or_gt (ρ i) (L + 2) with hlow | hlow
  · exact offDichotomyAt_near_extreme ρ i H L hLb hHb hLH (Or.inl hlow)
  · rcases le_or_gt (H - 2) (ρ i) with hhigh | hhigh
    · exact offDichotomyAt_near_extreme ρ i H L hLb hHb hLH (Or.inr hhigh)
    · exact h n ρ σ i H L hlip hcr hLb hHb hLH hL hH (by omega) (by omega)

-- Commented-out statement `offDichotomy`, `f2PrimeOff`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
