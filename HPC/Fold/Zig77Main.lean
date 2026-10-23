import HPC.Fold.Span
import HPC.Fold.Zig77Walk
import HPC.Fold.Zig77Crook
import HPC.Fold.Zig77Step

/-!
# `S3` at every span

The greedy jump zigzag of `HPC/Fold/Zig77Step.lean`, run on the two arms of a basepoint, never gets
stuck: whenever a phase would fail to widen the zigzag, the crookedness clause is violated
(`up_core`, `down_core`, `HPC/Fold/Zig77Crook.lean`). It stops after finitely many phases, since
every phase widens the zigzag by at least one level and the arms are bounded. The turning levels it
produces satisfy the phase condition `Fit` for both arms, and `fold_of_fit`
(`HPC/Fold/Zig77Walk.lean`) turns that into a common fold onto the jump walk. This proves `S3`.
-/

namespace HPC.Fold.Z77

/-- The arm on side `e` of a sequence re-indexed at the basepoint: `true` reads forwards,
`false` backwards. -/
def arm (S : ℤ → ℤ) (e : Bool) (j : ℕ) : ℤ := S (if e then (j : ℤ) else -(j : ℤ))

/-- The sequence read so that the arm on side `e` is its left arm. -/
def sside (S : ℤ → ℤ) (e : Bool) : ℤ → ℤ := if e then fun x => S (-x) else S

theorem arm_eq_sside_left (S : ℤ → ℤ) (e : Bool) (j : ℕ) :
    arm S e j = sside S e (-(j : ℤ)) := by
  cases e <;> simp [arm, sside]

theorem arm_not_eq_sside_right (S : ℤ → ℤ) (e : Bool) (j : ℕ) :
    arm S (!e) j = sside S e (j : ℤ) := by
  cases e <;> simp [arm, sside]

theorem arm_zero (S : ℤ → ℤ) (e : Bool) : arm S e 0 = S 0 := by
  cases e <;> simp [arm]

theorem crkOn_sside {S : ℤ → ℤ} {M : Bool → ℕ} (hS : CrkOn S (1 - M false) (M true - 1))
    (e : Bool) : CrkOn (sside S e) (1 - M e) (M (!e) - 1) := by
  cases e
  · simpa [sside] using hS
  · have h := hS.reverse
    rw [show -((M true : ℤ) - 1) = 1 - (M true : ℤ) by ring,
      show -(1 - (M false : ℤ)) = (M false : ℤ) - 1 by ring] at h
    simpa [sside] using h

theorem bool_eq_not_of_ne {e e0 : Bool} (h : e0 ≠ e) : e0 = !e := by
  cases e <;> cases e0 <;> simp_all

/-! ## Why no phase gets stuck -/

/-- **An up phase is never stuck.** -/
theorem nofail_up {S : ℤ → ℤ} {M : Bool → ℕ} (hS : CrkOn S (1 - M false) (M true - 1))
    (st : Bool → Option ℕ) (a b : ℤ) (hab : b ≤ a)
    (hpre : ∀ e τ, st e = some τ → ∀ j, j < τ → b ≤ arm S e j)
    (hdet : ∃ e0 d, d < M e0 ∧ arm S e0 d = a + 2 ∧ (∀ j, j < d → b ≤ arm S e0 j) ∧
      ∀ τ, st e0 = some τ → τ ≤ d) :
    ∀ e τ, st e = some τ → ∀ dr, τ ≤ dr → dr < M e → arm S e dr = b - 2 →
      (∀ j, τ ≤ j → j < dr → arm S e j ≤ a - 1) → False := by
  intro e τ hst dr hτdr hdrM hdr hle
  obtain ⟨e0, d, hdM, hd, hdb, hdτ⟩ := hdet
  by_cases he : e0 = e
  · subst he
    have hτd := hdτ τ hst
    have hddr : d < dr := by
      rcases lt_trichotomy d dr with h | h | h
      · exact h
      · subst h; rw [hd] at hdr; omega
      · have := hdb dr h; omega
    have := hle d hτd hddr
    omega
  · have he0 := bool_eq_not_of_ne he
    subst he0
    refine up_core (crkOn_sside hS e) τ dr d a b hab (by omega) (by omega) ?_ ?_ ?_ ?_ ?_
    · intro j hj; rw [← arm_eq_sside_left]; exact hpre e τ hst j hj
    · intro j hj1 hj2; rw [← arm_eq_sside_left]; exact hle j hj1 hj2
    · rw [← arm_eq_sside_left]; exact hdr
    · intro j hj; rw [← arm_not_eq_sside_right]; exact hdb j hj
    · rw [← arm_not_eq_sside_right]; exact hd

/-- **A down phase is never stuck.** -/
theorem nofail_down {S : ℤ → ℤ} {M : Bool → ℕ} (hS : CrkOn S (1 - M false) (M true - 1))
    (stb sta : Bool → Option ℕ) (a b : ℤ) (hab : b ≤ a)
    (hpre : ∀ e τ, stb e = some τ → ∀ j, j < τ → b ≤ arm S e j)
    (hup : ∀ e σ, sta e = some σ → ∃ τ, stb e = some τ ∧ τ ≤ σ ∧
      ∀ j, τ ≤ j → j < σ → arm S e j ≤ a - 2)
    (hdet : ∃ e0 τ0 σ0 d, stb e0 = some τ0 ∧ sta e0 = some σ0 ∧ σ0 < d ∧ d < M e0 ∧
      arm S e0 d = b - 2 ∧ ∀ j, τ0 ≤ j → j < d → arm S e0 j ≤ a - 1) :
    ∀ e σ, sta e = some σ → ∀ rise, σ ≤ rise → rise < M e → arm S e rise = a + 2 →
      (∀ j, σ ≤ j → j < rise → b + 1 ≤ arm S e j) → False := by
  intro e σ hsta rise hσr hrM hr hge
  obtain ⟨e0, τ0, σ0, d, hb0, ha0, hσd, hdM, hd, hdle⟩ := hdet
  obtain ⟨τ, hbτ, hτσ, hτle⟩ := hup e σ hsta
  by_cases he : e0 = e
  · subst he
    rw [ha0] at hsta; cases hsta
    rw [hb0] at hbτ; cases hbτ
    have hrd : rise < d := by
      rcases lt_trichotomy rise d with h | h | h
      · exact h
      · subst h; rw [hr] at hd; omega
      · have := hge d hσd.le h; omega
    have := hdle rise (by omega) hrd
    omega
  · have he0 := bool_eq_not_of_ne he
    subst he0
    refine down_core (crkOn_sside hS e) τ σ rise τ0 d a b hab (by omega) (by omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro j hj; rw [← arm_eq_sside_left]; exact hpre e τ hbτ j hj
    · intro j hj1 hj2; rw [← arm_eq_sside_left]; exact hτle j hj1 hj2
    · intro j hj1 hj2; rw [← arm_eq_sside_left]; exact hge j hj1 hj2
    · rw [← arm_eq_sside_left]; exact hr
    · intro j hj; rw [← arm_not_eq_sside_right]; exact hpre (!e) τ0 hb0 j hj
    · intro j hj1 hj2; rw [← arm_not_eq_sside_right]; exact hdle j hj1 hj2
    · rw [← arm_not_eq_sside_right]; exact hd

/-- **The first phase can go one way or the other.** -/
theorem first_direction {S : ℤ → ℤ} {M : Bool → ℕ} (hS : CrkOn S (1 - M false) (M true - 1)) :
    (∀ e dr, dr < M e → arm S e dr = S 0 - 3 → (∀ j, j < dr → arm S e j ≤ S 0) → False) ∨
    (∀ e dr, dr < M e → arm S e dr = S 0 + 3 → (∀ j, j < dr → S 0 ≤ arm S e j) → False) := by
  by_contra hc
  push_neg at hc
  obtain ⟨⟨e1, d1, hd1M, hd1, hd1le, -⟩, ⟨e2, d2, hd2M, hd2, hd2ge, -⟩⟩ := hc
  by_cases he : e2 = e1
  · subst he
    rcases lt_trichotomy d1 d2 with h | h | h
    · have := hd2ge d1 h; omega
    · subst h; omega
    · have := hd1le d2 h; omega
  · have he2 := bool_eq_not_of_ne he
    subst he2
    refine up_core (crkOn_sside hS e1) 0 d1 d2 (S 0 + 1) (S 0 - 1) (by omega) (by omega)
      (by omega) ?_ ?_ ?_ ?_ ?_
    · intro j hj; omega
    · intro j _ hj2; rw [← arm_eq_sside_left]; have := hd1le j hj2; omega
    · rw [← arm_eq_sside_left]; rw [hd1]; ring
    · intro j hj; rw [← arm_not_eq_sside_right]; have := hd2ge j hj; omega
    · rw [← arm_not_eq_sside_right]; rw [hd2]; ring

/-! ## The main induction -/

section Main

variable {S : ℤ → ℤ} {M : Bool → ℕ} {L H : ℤ}

/-- **The greedy zigzag, from an up phase.** From a state at bottom `b` (previous top `a`) in
which the next up phase is not stuck, the zigzag runs to the end, and every live arm fits it. -/
theorem main_up (hS : CrkOn S (1 - M false) (M true - 1)) (hlip : ∀ e, LipOn (arm S e) (M e))
    (hL : ∀ e j, j < M e → L ≤ arm S e j) (hH : ∀ e j, j < M e → arm S e j ≤ H) :
    ∀ (N : ℕ) (b a : ℤ) (st : Bool → Option ℕ), ((H + 1 - a) + (b - L + 1)).toNat ≤ N →
      b + 2 ≤ a → a ≤ H + 1 → L - 1 ≤ b →
      (∀ e τ, st e = some τ → τ < M e ∧ |arm S e τ - b| ≤ 1) →
      (∀ e τ, st e = some τ → ∀ j, j < τ → b ≤ arm S e j) →
      (∀ e τ, st e = some τ → ∀ dr, τ ≤ dr → dr < M e → arm S e dr = b - 2 →
        (∀ j, τ ≤ j → j < dr → arm S e j ≤ a - 1) → False) →
      ∃ ts : List ℤ, ∀ e τ, st e = some τ → Fit (arm S e) (M e) τ b ts := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro b a st hN hba haH hLb hst hpre hnf
  obtain ⟨t, nxt, ht1, P2, P3, P4, P5⟩ := up_step (arm S) M st a b H hlip hH hba hst hnf
  have leg_up : ∀ rest, (∀ e σ, nxt e = some σ → Fit (arm S e) (M e) σ t rest) →
      ∀ e τ, st e = some τ → Fit (arm S e) (M e) τ b (t :: rest) := by
    intro rest hrest e τ hse
    refine ⟨by rw [abs_of_nonneg (by omega)]; omega, ?_⟩
    cases hne : nxt e with
    | none =>
      left
      intro j hj1 hj2
      obtain ⟨h1, h2⟩ := P3 e τ hse hne j hj1 hj2
      simp only [Env]; omega
    | some σ =>
      right
      obtain ⟨q1, q2, q3, q4⟩ := P4 e τ σ hse hne
      refine ⟨σ, q1.le, q2, by rw [arr, if_pos (by omega)]; exact q3, ?_, hrest e σ hne⟩
      intro j hj1 hj2
      simp only [Env]
      rcases lt_or_eq_of_le hj2 with h | h
      · obtain ⟨h1, h2⟩ := q4 j hj1 h; omega
      · subst h; omega
  rcases P5 with hall | ⟨htH, e0, τ0, σ0, dr0, h01, h02, h03, h04, h05, h06⟩
  · exact ⟨[t], leg_up [] (fun e σ h => by rw [hall e] at h; cases h)⟩
  have hup : ∀ e σ, nxt e = some σ → ∃ τ, st e = some τ ∧ τ ≤ σ ∧
      ∀ j, τ ≤ j → j < σ → arm S e j ≤ t - 2 := by
    intro e σ hne
    cases hse : st e with
    | none => rw [P2 e hse] at hne; cases hne
    | some τ =>
      obtain ⟨q1, -, -, q4⟩ := P4 e τ σ hse hne
      exact ⟨τ, rfl, q1.le, fun j hj1 hj2 => (q4 j hj1 hj2).2⟩
  have hnfd := nofail_down hS st nxt t b (by omega) hpre hup
    ⟨e0, τ0, σ0, dr0, h01, h02, h03, h04, h05, fun j hj1 hj2 => (h06 j hj1 hj2).2⟩
  have hstd : ∀ e σ, nxt e = some σ → σ < M e ∧ |arm S e σ - t| ≤ 1 := by
    intro e σ hne
    obtain ⟨τ, hse, -, -⟩ := hup e σ hne
    obtain ⟨-, q2, q3, -⟩ := P4 e τ σ hse hne
    exact ⟨q2, by rw [q3]; norm_num⟩
  obtain ⟨t2, nxt2, g1, G2, G3, G4, G5⟩ := down_step (arm S) M nxt t b L hlip hL (by omega) hstd hnfd
  have leg_down : ∀ rest, (∀ e σ, nxt2 e = some σ → Fit (arm S e) (M e) σ t2 rest) →
      ∀ e σ, nxt e = some σ → Fit (arm S e) (M e) σ t (t2 :: rest) := by
    intro rest hrest e σ hse
    refine ⟨by rw [abs_of_nonpos (by omega)]; omega, ?_⟩
    cases hne : nxt2 e with
    | none =>
      left
      intro j hj1 hj2
      obtain ⟨h1, h2⟩ := G3 e σ hse hne j hj1 hj2
      simp only [Env]; omega
    | some σ' =>
      right
      obtain ⟨q1, q2, q3, q4⟩ := G4 e σ σ' hse hne
      refine ⟨σ', q1.le, q2, by rw [arr, if_neg (by omega)]; exact q3, ?_, hrest e σ' hne⟩
      intro j hj1 hj2
      simp only [Env]
      rcases lt_or_eq_of_le hj2 with h | h
      · obtain ⟨h1, h2⟩ := q4 j hj1 h; omega
      · subst h; omega
  rcases G5 with hall2 | ⟨hLt2, e1, τ1, σ1, dr1, k01, k02, k03, k04, k05, k06⟩
  · exact ⟨[t, t2], leg_up _ (leg_down [] (fun e σ h => by rw [hall2 e] at h; cases h))⟩
  have hbelow : ∀ e σ, nxt e = some σ → ∀ j, j < σ → t2 ≤ arm S e j := by
    intro e σ hne j hj
    obtain ⟨τ, hse, -, -⟩ := hup e σ hne
    obtain ⟨-, -, -, q4⟩ := P4 e τ σ hse hne
    rcases lt_or_ge j τ with h | h
    · have := hpre e τ hse j h; omega
    · have := (q4 j h hj).1; omega
  have hpre' : ∀ e σ', nxt2 e = some σ' → ∀ j, j < σ' → t2 ≤ arm S e j := by
    intro e σ' hne2 j hj
    cases hne : nxt e with
    | none => rw [G2 e hne] at hne2; cases hne2
    | some σ =>
      obtain ⟨-, -, -, q4⟩ := G4 e σ σ' hne hne2
      rcases lt_or_ge j σ with h | h
      · exact hbelow e σ hne j h
      · have := (q4 j h hj).1; omega
  have hnf' := nofail_up hS nxt2 t t2 (by omega) hpre'
    ⟨e1, dr1, k04, k05, fun j hj => by
      rcases lt_or_ge j τ1 with h | h
      · exact hbelow e1 τ1 k01 j h
      · have := (k06 j h hj).1; omega,
     fun τ h => by rw [k02] at h; cases h; exact k03.le⟩
  have hst' : ∀ e σ', nxt2 e = some σ' → σ' < M e ∧ |arm S e σ' - t2| ≤ 1 := by
    intro e σ' hne2
    cases hne : nxt e with
    | none => rw [G2 e hne] at hne2; cases hne2
    | some σ =>
      obtain ⟨-, q2, q3, -⟩ := G4 e σ σ' hne hne2
      exact ⟨q2, by rw [q3]; norm_num⟩
  obtain ⟨rest, hrest⟩ := ih ((H + 1 - t) + (t2 - L + 1)).toNat (by omega) t2 t nxt2 le_rfl
    (by omega) htH hLt2 hst' hpre' hnf'
  exact ⟨t :: t2 :: rest, leg_up _ (leg_down _ hrest)⟩

/-- **The greedy zigzag from the basepoint.** Both arms fit one jump walk starting within one of
the basepoint's level. -/
theorem greedy_fit (hS : CrkOn S (1 - M false) (M true - 1)) (hlip : ∀ e, LipOn (arm S e) (M e))
    (hL : ∀ e j, j < M e → L ≤ arm S e j) (hH : ∀ e j, j < M e → arm S e j ≤ H)
    (hM : ∀ e, 0 < M e) :
    ∃ (T0 : ℤ) (ts : List ℤ), |S 0 - T0| ≤ 1 ∧ ∀ e, Fit (arm S e) (M e) 0 T0 ts := by
  have hp1 := hL true 0 (hM true)
  have hp2 := hH true 0 (hM true)
  rw [arm_zero] at hp1 hp2
  set p := S 0 with hp
  rcases first_direction hS with hA | hB
  · -- up first, from the pseudo-state `p - 1`, `p + 1`
    obtain ⟨ts, hts⟩ := main_up hS hlip hL hH _ (p - 1) (p + 1) (fun _ => some 0) le_rfl
      (by omega) (by omega) (by omega)
      (fun e τ h => by cases h; exact ⟨hM e, by rw [arm_zero, ← hp, abs_le]; omega⟩)
      (fun e τ h j hj => by cases h; omega)
      (fun e τ h dr _ hdrM hdr hle => by
        cases h
        exact hA e dr hdrM (by rw [hdr]; ring) (fun j hj => by have := hle j (by omega) hj; omega))
    exact ⟨p - 1, ts, by norm_num, fun e => hts e 0 rfl⟩
  · -- down first
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
    · exact ⟨p + 1, [t2], by norm_num,
        leg_down [] (fun e σ h => by rw [hall2 e] at h; cases h)⟩
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
    exact ⟨p + 1, t2 :: rest, by norm_num, leg_down _ hrest⟩

end Main

/-! ## `S3` -/

/-- A fold read on `ℕ` gives `FoldsOnto`. -/
theorem foldsOnto_of_nat {m : ℕ} (f : Fin m → ℤ) (g : ℕ → ℤ) (hfg : ∀ j : Fin m, f j = g j.val)
    (len : ℕ) (c : ℕ → ℤ) (β : ℕ → ℕ) (h0 : β 0 = 0) (hlt : ∀ j, 0 ≤ j → j < m → β j < len)
    (hl : ∀ j, 0 ≤ j → j + 1 < m → |((β (j + 1) : ℕ) : ℤ) - ((β j : ℕ) : ℤ)| ≤ 1)
    (hc : ∀ j, 0 ≤ j → j < m → |g j - c (β j)| ≤ 1) : FoldsOnto f len c := by
  refine ⟨fun j => β j.val, fun j => hlt j.val (Nat.zero_le _) j.isLt, ?_, ?_, ?_⟩
  · intro j j' hjj'
    have := hl j.val (Nat.zero_le _) (by have := j'.isLt; omega)
    simp only [hjj']; exact this
  · intro j hj; simp only [hj, h0]
  · intro j; rw [hfg]; exact hc j.val (Nat.zero_le _) j.isLt

/-- **`S3`**, at every span: from any basepoint of a faithful crooked sequence, both arms fold
onto one common walk — the greedy jump zigzag. -/
theorem s3_zig : S3 := by
  intro n ρ σ i H L hlip hcrook hLf hHf _ _ _
  set S := reindex ρ i with hSdef
  set M : Bool → ℕ := fun e => if e then n - i.val else i.val + 1 with hMdef
  have hi := i.isLt
  have hS : CrkOn S (1 - M false) (M true - 1) := by
    have h := crkOn_of_isCrookedIvF hcrook i
    have e1 : (1 : ℤ) - ((M false : ℕ) : ℤ) = -(i : ℤ) := by simp [hMdef]
    have e2 : ((M true : ℕ) : ℤ) - 1 = (n : ℤ) - 1 - i := by
      simp only [hMdef, if_true]; rw [Nat.cast_sub hi.le]; ring
    rw [e1, e2]; exact h
  have harmT : ∀ j (hj : j < M true), arm S true j =
      ρ ⟨i.val + j, by have : j < n - i.val := by simpa [hMdef] using hj
                       omega⟩ := by
    intro j hj
    simp only [arm, if_true, hSdef]
    exact reindex_nat_right ρ i j (by simpa [hMdef] using hj)
  have harmF : ∀ j, j < M false → arm S false j = ρ ⟨i.val - j, by omega⟩ := by
    intro j hj
    simp only [arm, hSdef, Bool.false_eq_true, if_false]
    exact reindex_nat_left ρ i j (by simpa [hMdef] using hj)
  have hlipA : ∀ e, LipOn (arm S e) (M e) := by
    intro e j hj
    cases e
    · rw [harmF j (by omega), harmF (j + 1) hj, abs_sub_comm]
      exact hlip _ _ (by simp only [hMdef] at hj ⊢; simp at hj; omega)
    · rw [harmT j (by omega), harmT (j + 1) hj]
      exact hlip _ _ (by simp only; omega)
  have hLA : ∀ e j, j < M e → L ≤ arm S e j := by
    intro e j hj; cases e
    · rw [harmF j hj]; exact hLf _
    · rw [harmT j hj]; exact hLf _
  have hHA : ∀ e j, j < M e → arm S e j ≤ H := by
    intro e j hj; cases e
    · rw [harmF j hj]; exact hHf _
    · rw [harmT j hj]; exact hHf _
  have hM : ∀ e, 0 < M e := by intro e; cases e <;> simp [hMdef]
  obtain ⟨T0, ts, hT0, hfit⟩ := greedy_fit hS hlipA hLA hHA hM
  have hfold : ∀ e, ∃ β : ℕ → ℕ, β 0 = 0 ∧ (∀ j, 0 ≤ j → j < M e → β j < jlen T0 ts) ∧
      (∀ j, 0 ≤ j → j + 1 < M e → |((β (j + 1) : ℕ) : ℤ) - ((β j : ℕ) : ℤ)| ≤ 1) ∧
      ∀ j, 0 ≤ j → j < M e → |arm S e j - jwalk T0 ts (β j)| ≤ 1 := fun e =>
    fold_of_fit (hlipA e) ts 0 T0 (hfit e) (by rw [arm_zero]; exact hT0)
  obtain ⟨βT, a1, a2, a3, a4⟩ := hfold true
  obtain ⟨βF, b1, b2, b3, b4⟩ := hfold false
  refine ⟨jlen T0 ts, jwalk T0 ts, ?_, ?_⟩
  · exact foldsOnto_of_nat _ (arm S true)
      (fun j => by rw [harmT j.val (by simp [hMdef])]; rfl) _ _ βT a1
      (fun j h1 h2 => a2 j h1 (by simpa [hMdef] using h2))
      (fun j h1 h2 => a3 j h1 (by simpa [hMdef] using h2))
      (fun j h1 h2 => a4 j h1 (by simpa [hMdef] using h2))
  · exact foldsOnto_of_nat _ (arm S false)
      (fun j => by rw [harmF j.val (by have := j.isLt; simp [hMdef]; omega)]; rfl) _ _ βF b1
      (fun j h1 h2 => b2 j h1 (by simpa [hMdef] using h2))
      (fun j h1 h2 => b3 j h1 (by simpa [hMdef] using h2))
      (fun j h1 h2 => b4 j h1 (by simpa [hMdef] using h2))

end HPC.Fold.Z77
