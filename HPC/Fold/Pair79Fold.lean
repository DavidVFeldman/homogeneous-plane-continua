import HPC.Fold.Splice78

/-!
# Batch 79: the greedy fold with a chosen first direction, and what it says at time `0`

`greedy_fit` (batch 77) starts its jump walk at `S 0 - 1` (first phase up) whenever that is
possible and at `S 0 + 1` otherwise. For two-link basepoints the choice matters, so here the two
branches are separate lemmas (`greedy_fit_below`, `greedy_fit_above`), `fold_of_fit_zero` records
that every arm index at the start of an arm whose values stay within one of the walk's start is
at time `0`, and `fold_low_end_mode` / `fold_high_end_mode` are the batch-78 fold with a fake end
link (low, resp. high) with the start of the walk chosen.
-/

namespace HPC.Fold.Z77

section Main

variable {S : ℤ → ℤ} {M : Bool → ℕ} {L H : ℤ}

/-- The first-direction condition allowing the walk to start just below `S 0`. -/
def OKBelow (S : ℤ → ℤ) (M : Bool → ℕ) : Prop :=
  ∀ e dr, dr < M e → arm S e dr = S 0 - 3 → (∀ j, j < dr → arm S e j ≤ S 0) → False

/-- The first-direction condition allowing the walk to start just above `S 0`. -/
def OKAbove (S : ℤ → ℤ) (M : Bool → ℕ) : Prop :=
  ∀ e dr, dr < M e → arm S e dr = S 0 + 3 → (∀ j, j < dr → S 0 ≤ arm S e j) → False

/-- **The greedy zigzag started just below the basepoint.** -/
theorem greedy_fit_below (hS : CrkOn S (1 - M false) (M true - 1))
    (hlip : ∀ e, LipOn (arm S e) (M e))
    (hL : ∀ e j, j < M e → L ≤ arm S e j) (hH : ∀ e j, j < M e → arm S e j ≤ H)
    (hM : ∀ e, 0 < M e) (hA : OKBelow S M) :
    ∃ ts : List ℤ, ∀ e, Fit (arm S e) (M e) 0 (S 0 - 1) ts := by
  have hp1 := hL true 0 (hM true)
  have hp2 := hH true 0 (hM true)
  rw [arm_zero] at hp1 hp2
  set p := S 0 with hp
  obtain ⟨ts, hts⟩ := main_up hS hlip hL hH _ (p - 1) (p + 1) (fun _ => some 0) le_rfl
    (by omega) (by omega) (by omega)
    (fun e τ h => by cases h; exact ⟨hM e, by rw [arm_zero, ← hp, abs_le]; omega⟩)
    (fun e τ h j hj => by cases h; omega)
    (fun e τ h dr _ hdrM hdr hle => by
      cases h
      exact hA e dr hdrM (by rw [hdr]; ring) (fun j hj => by have := hle j (by omega) hj; omega))
  exact ⟨ts, fun e => hts e 0 rfl⟩

/-- **The greedy zigzag started just above the basepoint.** -/
theorem greedy_fit_above (hS : CrkOn S (1 - M false) (M true - 1))
    (hlip : ∀ e, LipOn (arm S e) (M e))
    (hL : ∀ e j, j < M e → L ≤ arm S e j) (hH : ∀ e j, j < M e → arm S e j ≤ H)
    (hM : ∀ e, 0 < M e) (hB : OKAbove S M) :
    ∃ ts : List ℤ, ∀ e, Fit (arm S e) (M e) 0 (S 0 + 1) ts := by
  have hp1 := hL true 0 (hM true)
  have hp2 := hH true 0 (hM true)
  rw [arm_zero] at hp1 hp2
  set p := S 0 with hp
  have hst : ∀ e τ, (fun _ => some 0 : Bool → Option ℕ) e = some τ →
      τ < M e ∧ |arm S e τ - (p + 1)| ≤ 1 := fun e τ h => by
    cases h; exact ⟨hM e, by rw [arm_zero, ← hp, abs_le]; omega⟩
  obtain ⟨t2, nxt2, g1, G2, G3, G4, G5⟩ := down_step (arm S) M (fun _ => some 0) (p + 1) (p - 1) L
    hlip hL (by omega) hst
    (fun e τ h dr _ hdrM hdr hge => by
      cases h
      exact hB e dr hdrM (by rw [hdr]; ring) (fun j hj => by have := hge j (by omega) hj; omega))
  have leg_down : ∀ rest, (∀ e σ, nxt2 e = some σ → Fit (arm S e) (M e) σ t2 rest) →
      ∀ e, Fit (arm S e) (M e) 0 (p + 1) (t2 :: rest) := by
    intro rest hrest e
    refine ⟨by rw [abs_of_nonpos (by omega)]; omega, ?_⟩
    cases hne : nxt2 e with
    | none =>
      left
      intro j hj1 hj2
      obtain ⟨h1, h2⟩ := G3 e 0 rfl hne j hj1 hj2
      simp only [Env]; omega
    | some σ' =>
      right
      obtain ⟨q1, q2, q3, q4⟩ := G4 e 0 σ' rfl hne
      refine ⟨σ', q1.le, q2, by rw [arr, if_neg (by omega)]; exact q3, ?_, hrest e σ' hne⟩
      intro j hj1 hj2
      simp only [Env]
      rcases lt_or_eq_of_le hj2 with h | h
      · obtain ⟨h1, h2⟩ := q4 j hj1 h; omega
      · subst h; omega
  rcases G5 with hall2 | ⟨hLt2, e1, τ1, σ1, dr1, k01, k02, k03, k04, k05, k06⟩
  · exact ⟨[t2], leg_down [] (fun e σ h => by rw [hall2 e] at h; cases h)⟩
  have hpre' : ∀ e σ', nxt2 e = some σ' → ∀ j, j < σ' → t2 ≤ arm S e j := by
    intro e σ' hne2 j hj
    obtain ⟨-, -, -, q4⟩ := G4 e 0 σ' rfl hne2
    have := (q4 j (Nat.zero_le _) hj).1; omega
  have hnf' := nofail_up hS nxt2 (p + 1) t2 (by omega) hpre'
    ⟨e1, dr1, k04, k05, fun j hj => by
      cases k01
      have := (k06 j (Nat.zero_le _) hj).1; omega,
     fun τ h => by rw [k02] at h; cases h; exact k03.le⟩
  have hst' : ∀ e σ', nxt2 e = some σ' → σ' < M e ∧ |arm S e σ' - t2| ≤ 1 := by
    intro e σ' hne2
    obtain ⟨-, q2, q3, -⟩ := G4 e 0 σ' rfl hne2
    exact ⟨q2, by rw [q3]; norm_num⟩
  obtain ⟨rest, hrest⟩ := main_up hS hlip hL hH _ t2 (p + 1) nxt2 le_rfl
    (by omega) (by omega) hLt2 hst' hpre' hnf'
  exact ⟨t2 :: rest, leg_down _ hrest⟩

end Main

/-- An arm value within one of the start of a leg sits at leg position `0`. -/
theorem legPos_eq_zero (a b x : ℤ) (h : |x - a| ≤ 1) : legPos a b x = 0 := by
  unfold legPos
  rw [abs_le] at h
  split_ifs <;> omega

/-- **`fold_of_fit`, with time `0` recorded**: every index of the arm up to which the arm has
stayed within one of the walk's start is sent to time `0`. -/
theorem fold_of_fit_zero {f : ℕ → ℤ} {m : ℕ} (hlip : ∀ j, j + 1 < m → |f (j + 1) - f j| ≤ 1) :
    ∀ (ts : List ℤ) (τ : ℕ) (a : ℤ), Fit f m τ a ts → |f τ - a| ≤ 1 →
      ∃ β : ℕ → ℕ, β τ = 0 ∧ (∀ j, τ ≤ j → j < m → β j < jlen a ts) ∧
        (∀ j, τ ≤ j → j + 1 < m → |((β (j + 1) : ℕ) : ℤ) - ((β j : ℕ) : ℤ)| ≤ 1) ∧
        (∀ j, τ ≤ j → j < m → |f j - jwalk a ts (β j)| ≤ 1) ∧
        (∀ j, τ ≤ j → j < m → (∀ i, τ ≤ i → i ≤ j → |f i - a| ≤ 1) → β j = 0) := by
  intro ts
  induction ts with
  | nil => intro τ a h; exact absurd h (by simp [Fit])
  | cons b rest ih =>
    intro τ a hfit hstart
    obtain ⟨h3, hfit⟩ := hfit
    have hβ0 : legPos a b (f τ) = 0 := legPos_eq_zero a b _ hstart
    have hjl := jlen_pos b rest
    rcases hfit with hdone | ⟨τ', hττ', hτ'm, harr, henv, hrest⟩
    · refine ⟨fun j => legPos a b (f j), hβ0, ?_, ?_, ?_, ?_⟩
      · intro j _ _
        have := legPos_le a b (f j) h3
        simp only [jlen]; omega
      · intro j _ hj
        exact legPos_lip a b _ _ (hlip j hj)
      · intro j hj hjm
        exact jwalk_legPos a b (f j) rest h3 (hdone j hj hjm)
      · intro j hj _ hall
        exact legPos_eq_zero a b _ (hall j hj le_rfl)
    · have hstart' : |f τ' - b| ≤ 1 := by
        rw [harr]; unfold arr; split_ifs <;> simp
      obtain ⟨β', hβ'0, hβ'lt, hβ'lip, hβ'w, -⟩ := ih τ' b hrest hstart'
      have hposτ' : legPos a b (f τ') = legLen a b := by
        rw [harr]; unfold legPos legLen arr
        rcases abs_sub_cases a b with ⟨hab, he⟩ | ⟨hab, he⟩ <;> rw [he] at h3 ⊢ <;>
          simp only [hab, if_true, if_false] <;> omega
      have harr_far : 2 ≤ |f τ' - a| := by
        rw [harr]; unfold arr
        rcases abs_sub_cases a b with ⟨hab, he⟩ | ⟨hab, he⟩ <;> rw [he] at h3 <;>
          simp only [hab, if_true, if_false]
        · rw [abs_of_nonneg (by omega)]; omega
        · rw [abs_of_nonpos (by omega)]; omega
      refine ⟨fun j => if j ≤ τ' then legPos a b (f j) else legLen a b + β' j, ?_, ?_, ?_, ?_,
        ?_⟩
      · simp only [hττ', if_true]; exact hβ0
      · intro j hj hjm
        simp only [jlen]
        split_ifs with hjτ
        · have := legPos_le a b (f j) h3; omega
        · have := hβ'lt j (by omega) hjm; omega
      · intro j hj hjm
        simp only []
        by_cases h1 : j + 1 ≤ τ'
        · rw [if_pos h1, if_pos (by omega)]
          exact legPos_lip a b _ _ (hlip j hjm)
        · rw [if_neg h1]
          by_cases h2 : j ≤ τ'
          · rw [if_pos h2]
            have hj' : j = τ' := by omega
            subst hj'
            rw [hposτ']
            have := hβ'lip j le_rfl hjm
            rw [hβ'0] at this
            push_cast at this ⊢
            simpa using this
          · rw [if_neg h2]
            have := hβ'lip j (by omega) hjm
            push_cast
            simpa using this
      · intro j hj hjm
        simp only []
        split_ifs with hjτ
        · exact jwalk_legPos a b (f j) rest h3 (henv j hj hjτ)
        · have hw := hβ'w j (by omega) hjm
          have hne : legLen a b + β' j ≠ 0 := by
            have : 0 < legLen a b := by
              unfold legLen
              rcases abs_sub_cases a b with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he] at h3 ⊢ <;> omega
            omega
          simp only [jwalk, hne, if_false, show ¬ (legLen a b + β' j < legLen a b) by omega,
            Nat.add_sub_cancel_left]
          exact hw
      · intro j hj hjm hall
        have hjτ' : j ≤ τ' ∨ τ' < j := le_or_gt j τ'
        rcases hjτ' with h | h
        · simp only [h, if_true]; exact legPos_eq_zero a b _ (hall j hj le_rfl)
        · exfalso
          have := hall τ' hττ' h.le
          omega

end HPC.Fold.Z77
