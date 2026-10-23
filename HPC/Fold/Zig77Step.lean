import Mathlib

/-!
# One phase of the greedy jump zigzag

A phase runs a leg from the current turning level `b` upwards. Each arm still running entered the
phase at its own time `τ` (within one of `b`). The next turning level `t` is the least, over the
arms that eventually drop below `b - 1`, of one more than the highest level the arm reaches before
that drop. Every arm then either stays in `[b - 1, t - 2]` for good (it is finished) or first
reaches `t - 1` at a time `σ`, before which it stays in `[b - 1, t - 2]`.

`up_step` states this for two arms, indexed by `Bool`, under the hypothesis that no running arm
drops to `b - 2` while staying at `a - 1` or below (so that `t ≥ a + 1`). `down_step` is its
reflection. Nothing here uses crookedness.
-/

namespace HPC.Fold.Z77

/-- 1-Lipschitz on `[0, m)`. -/
def LipOn (f : ℕ → ℤ) (m : ℕ) : Prop := ∀ j, j + 1 < m → |f (j + 1) - f j| ≤ 1

theorem LipOn.neg {f : ℕ → ℤ} {m : ℕ} (h : LipOn f m) : LipOn (fun j => -f j) m := by
  intro j hj
  have := h j hj
  rw [abs_le] at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- The first drop below `b - 1` after `τ`, which is at `b - 2`. -/
theorem first_drop {f : ℕ → ℤ} {m τ : ℕ} {b : ℤ} (hlip : LipOn f m)
    (hfτ : b - 1 ≤ f τ) (hd : ∃ j, τ ≤ j ∧ j < m ∧ f j < b - 1) :
    ∃ dr, τ < dr ∧ dr < m ∧ f dr = b - 2 ∧ ∀ j, τ ≤ j → j < dr → b - 1 ≤ f j := by
  classical
  let P : ℕ → Prop := fun j => τ ≤ j ∧ j < m ∧ f j < b - 1
  have hP : ∃ j, P j := hd
  set dr := Nat.find hP with hdr
  have hspec : P dr := Nat.find_spec hP
  have hmin : ∀ j, j < dr → ¬ P j := fun j hj => Nat.find_min hP hj
  obtain ⟨h1, h2, h3⟩ := hspec
  have hgt : τ < dr := by
    rcases Nat.lt_or_ge τ dr with h | h
    · exact h
    · have : dr = τ := le_antisymm h h1
      rw [this] at h3; omega
  have hbefore : ∀ j, τ ≤ j → j < dr → b - 1 ≤ f j := by
    intro j hj1 hj2
    by_contra hc
    exact hmin j hj2 ⟨hj1, by omega, by omega⟩
  refine ⟨dr, hgt, h2, ?_, hbefore⟩
  have hprev := hbefore (dr - 1) (by omega) (by omega)
  have hl := hlip (dr - 1) (by omega)
  rw [show dr - 1 + 1 = dr by omega, abs_le] at hl
  omega

/-- A maximum on a nonempty interval of times. -/
theorem max_on (f : ℕ → ℤ) {τ dr : ℕ} (h : τ < dr) :
    ∃ M, (∃ j0, τ ≤ j0 ∧ j0 < dr ∧ f j0 = M) ∧ ∀ j, τ ≤ j → j < dr → f j ≤ M := by
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image (Finset.Ico τ dr) f
    ⟨τ, Finset.mem_Ico.2 ⟨le_rfl, h⟩⟩
  rw [Finset.mem_Ico] at hj0
  exact ⟨f j0, ⟨j0, hj0.1, hj0.2, rfl⟩, fun j h1 h2 => hmax j (Finset.mem_Ico.2 ⟨h1, h2⟩)⟩

/-- **The transfer of one arm.** If every drop below `b - 1` is preceded by a visit to `t - 1`,
the arm either stays in `[b - 1, t - 2]` for good, or first reaches `t - 1` at a time `σ` before
which it stays in `[b - 1, t - 2]`. -/
theorem transfer {f : ℕ → ℤ} {m τ : ℕ} {b t : ℤ} (hlip : LipOn f m) (hbt : b + 3 ≤ t)
    (hfτ : f τ ≤ b + 1)
    (hreach : ∀ j, τ ≤ j → j < m → f j < b - 1 → ∃ j', τ ≤ j' ∧ j' < j ∧ t - 1 ≤ f j') :
    (∀ j, τ ≤ j → j < m → b - 1 ≤ f j ∧ f j ≤ t - 2) ∨
    (∃ σ, τ < σ ∧ σ < m ∧ f σ = t - 1 ∧ ∀ j, τ ≤ j → j < σ → b - 1 ≤ f j ∧ f j ≤ t - 2) := by
  classical
  by_cases hex : ∃ j, τ ≤ j ∧ j < m ∧ t - 1 ≤ f j
  · right
    set σ := Nat.find hex
    obtain ⟨h1, h2, h3⟩ : τ ≤ σ ∧ σ < m ∧ t - 1 ≤ f σ := Nat.find_spec hex
    have hmin : ∀ j, j < σ → ¬ (τ ≤ j ∧ j < m ∧ t - 1 ≤ f j) := fun j hj => Nat.find_min hex hj
    have hgt : τ < σ := by
      rcases Nat.lt_or_ge τ σ with h | h
      · exact h
      · have : σ = τ := le_antisymm h h1
        rw [this] at h3; omega
    have hbefore : ∀ j, τ ≤ j → j < σ → b - 1 ≤ f j ∧ f j ≤ t - 2 := by
      intro j hj1 hj2
      constructor
      · by_contra hc
        obtain ⟨j', hj'1, hj'2, hj'3⟩ := hreach j hj1 (by omega) (by omega)
        exact hmin j' (by omega) ⟨hj'1, by omega, hj'3⟩
      · by_contra hc
        exact hmin j hj2 ⟨hj1, by omega, by omega⟩
    refine ⟨σ, hgt, h2, ?_, hbefore⟩
    have hprev := hbefore (σ - 1) (by omega) (by omega)
    have hl := hlip (σ - 1) (by omega)
    rw [show σ - 1 + 1 = σ by omega, abs_le] at hl
    omega
  · left
    push_neg at hex
    intro j hj1 hj2
    refine ⟨?_, by have := hex j hj1 hj2; omega⟩
    by_contra hc
    obtain ⟨j', hj'1, hj'2, hj'3⟩ := hreach j hj1 hj2 (by omega)
    have := hex j' hj'1 (by omega)
    omega

/-- What one arm contributes to the choice of the next turning level. -/
def ArmVal (f : ℕ → ℤ) (m : ℕ) (st : Option ℕ) (a b big v : ℤ) : Prop :=
  a + 1 ≤ v ∧ v ≤ big ∧
  (∀ τ, st = some τ → ∀ j, τ ≤ j → j < m → f j < b - 1 →
      ∃ j', τ ≤ j' ∧ j' < j ∧ v - 1 ≤ f j') ∧
  (v < big → ∃ τ dr j0, st = some τ ∧ τ < dr ∧ dr < m ∧ f dr = b - 2 ∧
      (∀ j, τ ≤ j → j < dr → b - 1 ≤ f j ∧ f j ≤ v - 1) ∧ τ ≤ j0 ∧ j0 < dr ∧ f j0 = v - 1)

theorem exists_armVal {f : ℕ → ℤ} {m : ℕ} {st : Option ℕ} {a b Hb : ℤ} (hlip : LipOn f m)
    (hbd : ∀ j, j < m → f j ≤ Hb)
    (hst : ∀ τ, st = some τ → τ < m ∧ |f τ - b| ≤ 1)
    (hnf : ∀ τ, st = some τ → ∀ dr, τ ≤ dr → dr < m → f dr = b - 2 →
      (∀ j, τ ≤ j → j < dr → f j ≤ a - 1) → False) :
    ∃ v, ArmVal f m st a b (max (a + 1) (Hb + 2)) v := by
  set big := max (a + 1) (Hb + 2)
  have hbig : ∃ v, v = big := ⟨big, rfl⟩
  cases st with
  | none =>
    refine ⟨big, le_max_left _ _, le_rfl, ?_, ?_⟩
    · intro τ h; cases h
    · intro h; exact absurd h (lt_irrefl _)
  | some τ =>
    obtain ⟨hτm, hτb⟩ := hst τ rfl
    rw [abs_le] at hτb
    by_cases hd : ∃ j, τ ≤ j ∧ j < m ∧ f j < b - 1
    · obtain ⟨dr, hdr1, hdr2, hdr3, hdr4⟩ := first_drop hlip (by omega) hd
      obtain ⟨M, ⟨j0, hj01, hj02, hj03⟩, hM⟩ := max_on f hdr1
      have hMa : a ≤ M := by
        by_contra hc
        exact hnf τ rfl dr hdr1.le hdr2 hdr3 (fun j h1 h2 => by have := hM j h1 h2; omega)
      have hMH : M ≤ Hb := hj03 ▸ hbd j0 (by omega)
      refine ⟨M + 1, by omega, by omega, ?_, ?_⟩
      · intro τ' h j hj1 hj2 hj3
        cases h
        have : dr ≤ j := by
          by_contra hc
          have := hdr4 j hj1 (by omega)
          omega
        exact ⟨j0, hj01, by omega, by omega⟩
      · intro _
        exact ⟨τ, dr, j0, rfl, hdr1, hdr2, hdr3,
          fun j h1 h2 => ⟨hdr4 j h1 h2, by have := hM j h1 h2; omega⟩, hj01, hj02, by omega⟩
    · push_neg at hd
      refine ⟨big, le_max_left _ _, le_rfl, ?_, ?_⟩
      · intro τ' h j hj1 hj2 hj3
        cases h
        have := hd j hj1 hj2
        omega
      · intro h; exact absurd h (lt_irrefl _)

/-- **One up phase, two arms.** -/
theorem up_step (F : Bool → ℕ → ℤ) (M : Bool → ℕ) (st : Bool → Option ℕ) (a b Hb : ℤ)
    (hlip : ∀ e, LipOn (F e) (M e)) (hbd : ∀ e j, j < M e → F e j ≤ Hb) (hab : b + 2 ≤ a)
    (hst : ∀ e τ, st e = some τ → τ < M e ∧ |F e τ - b| ≤ 1)
    (hnf : ∀ e τ, st e = some τ → ∀ dr, τ ≤ dr → dr < M e → F e dr = b - 2 →
      (∀ j, τ ≤ j → j < dr → F e j ≤ a - 1) → False) :
    ∃ (t : ℤ) (nxt : Bool → Option ℕ), a + 1 ≤ t ∧
      (∀ e, st e = none → nxt e = none) ∧
      (∀ e τ, st e = some τ → nxt e = none →
        ∀ j, τ ≤ j → j < M e → b - 1 ≤ F e j ∧ F e j ≤ t - 2) ∧
      (∀ e τ σ, st e = some τ → nxt e = some σ →
        τ < σ ∧ σ < M e ∧ F e σ = t - 1 ∧ ∀ j, τ ≤ j → j < σ → b - 1 ≤ F e j ∧ F e j ≤ t - 2) ∧
      ((∀ e, nxt e = none) ∨
        (t ≤ Hb + 1 ∧ ∃ e τ σ dr, st e = some τ ∧ nxt e = some σ ∧ σ < dr ∧ dr < M e ∧
          F e dr = b - 2 ∧ ∀ j, τ ≤ j → j < dr → b - 1 ≤ F e j ∧ F e j ≤ t - 1)) := by
  classical
  set big := max (a + 1) (Hb + 2) with hbig
  have hv : ∀ e, ∃ v, ArmVal (F e) (M e) (st e) a b big v := fun e =>
    exists_armVal (hlip e) (hbd e) (hst e) (hnf e)
  choose v hvv using hv
  set t := min (v true) (v false) with ht
  have htv : ∀ e, t ≤ v e := by
    intro e; cases e
    · exact min_le_right _ _
    · exact min_le_left _ _
  have hta : a + 1 ≤ t := le_min (hvv true).1 (hvv false).1
  -- the reach condition for `t`
  have hreach : ∀ e τ, st e = some τ → ∀ j, τ ≤ j → j < M e → F e j < b - 1 →
      ∃ j', τ ≤ j' ∧ j' < j ∧ t - 1 ≤ F e j' := by
    intro e τ h j hj1 hj2 hj3
    obtain ⟨j', h1, h2, h3⟩ := (hvv e).2.2.1 τ h j hj1 hj2 hj3
    exact ⟨j', h1, h2, by have := htv e; omega⟩
  -- the per-arm transfer
  have harm : ∀ e, ∃ o : Option ℕ, (st e = none → o = none) ∧
      (∀ τ, st e = some τ → o = none → ∀ j, τ ≤ j → j < M e → b - 1 ≤ F e j ∧ F e j ≤ t - 2) ∧
      (∀ τ σ, st e = some τ → o = some σ →
        τ < σ ∧ σ < M e ∧ F e σ = t - 1 ∧ ∀ j, τ ≤ j → j < σ → b - 1 ≤ F e j ∧ F e j ≤ t - 2) := by
    intro e
    cases hse : st e with
    | none => exact ⟨none, fun _ => rfl, fun τ h => (by cases h), fun τ σ h => (by cases h)⟩
    | some τ =>
      obtain ⟨hτm, hτb⟩ := hst e τ hse
      rw [abs_le] at hτb
      rcases transfer (hlip e) (by omega) (by omega) (hreach e τ hse) with hfin | ⟨σ, hσ⟩
      · exact ⟨none, fun h => (by cases h), fun τ' h _ => (by cases h; exact hfin),
          fun τ' σ h h' => (by cases h')⟩
      · exact ⟨some σ, fun h => (by cases h), fun τ' h h' => (by cases h'),
          fun τ' σ' h h' => (by cases h; cases h'; exact hσ)⟩
  choose nxt hn1 hn2 hn3 using harm
  refine ⟨t, nxt, hta, hn1, hn2, hn3, ?_⟩
  by_cases hlt : t < big
  · right
    -- the arm realising the minimum
    have : ∃ e, v e = t := by
      rcases le_total (v true) (v false) with h | h
      · exact ⟨true, by rw [ht, min_eq_left h]⟩
      · exact ⟨false, by rw [ht, min_eq_right h]⟩
    obtain ⟨e, he⟩ := this
    obtain ⟨τ, dr, j0, hse, hdr1, hdr2, hdr3, hdr4, hj01, hj02, hj03⟩ :=
      (hvv e).2.2.2 (by rw [he]; exact hlt)
    rw [he] at hdr4 hj03
    have hdrb : F e dr < b - 1 := by omega
    cases hne : nxt e with
    | none =>
      have := hn2 e τ hse hne dr hdr1.le hdr2
      omega
    | some σ =>
      obtain ⟨hσ1, hσ2, hσ3, hσ4⟩ := hn3 e τ σ hse hne
      have hσdr : σ < dr := by
        by_contra hc
        have := hσ4 j0 hj01 (by omega)
        omega
      refine ⟨?_, e, τ, σ, dr, hse, hne, hσdr, hdr2, hdr3, hdr4⟩
      have := hbd e j0 (by omega)
      omega
  · left
    intro e
    cases hne : nxt e with
    | none => rfl
    | some σ =>
      cases hse : st e with
      | none => rw [hn1 e hse] at hne; cases hne
      | some τ =>
        obtain ⟨-, hσ2, hσ3, -⟩ := hn3 e τ σ hse hne
        have := hbd e σ hσ2
        have : big ≤ t := not_lt.1 hlt
        have : Hb + 2 ≤ big := le_max_right _ _
        omega

/-- **One down phase, two arms**: the reflection of `up_step`. -/
theorem down_step (F : Bool → ℕ → ℤ) (M : Bool → ℕ) (st : Bool → Option ℕ) (a b Lb : ℤ)
    (hlip : ∀ e, LipOn (F e) (M e)) (hbd : ∀ e j, j < M e → Lb ≤ F e j) (hab : b + 2 ≤ a)
    (hst : ∀ e τ, st e = some τ → τ < M e ∧ |F e τ - a| ≤ 1)
    (hnf : ∀ e τ, st e = some τ → ∀ dr, τ ≤ dr → dr < M e → F e dr = a + 2 →
      (∀ j, τ ≤ j → j < dr → b + 1 ≤ F e j) → False) :
    ∃ (t : ℤ) (nxt : Bool → Option ℕ), t ≤ b - 1 ∧
      (∀ e, st e = none → nxt e = none) ∧
      (∀ e τ, st e = some τ → nxt e = none →
        ∀ j, τ ≤ j → j < M e → t + 2 ≤ F e j ∧ F e j ≤ a + 1) ∧
      (∀ e τ σ, st e = some τ → nxt e = some σ →
        τ < σ ∧ σ < M e ∧ F e σ = t + 1 ∧ ∀ j, τ ≤ j → j < σ → t + 2 ≤ F e j ∧ F e j ≤ a + 1) ∧
      ((∀ e, nxt e = none) ∨
        (Lb - 1 ≤ t ∧ ∃ e τ σ dr, st e = some τ ∧ nxt e = some σ ∧ σ < dr ∧ dr < M e ∧
          F e dr = a + 2 ∧ ∀ j, τ ≤ j → j < dr → t + 1 ≤ F e j ∧ F e j ≤ a + 1)) := by
  obtain ⟨t, nxt, h1, h2, h3, h4, h5⟩ := up_step (fun e j => -F e j) M st (-b) (-a) (-Lb)
    (fun e => (hlip e).neg) (fun e j hj => by have := hbd e j hj; beta_reduce at *; omega) (by omega)
    (fun e τ h => by
      obtain ⟨p1, p2⟩ := hst e τ h
      refine ⟨p1, ?_⟩
      rw [show -F e τ - -a = -(F e τ - a) by ring, abs_neg]; exact p2)
    (fun e τ h dr hdr1 hdr2 hdr3 hdr4 => hnf e τ h dr hdr1 hdr2 (by beta_reduce at *; omega)
      (fun j hj1 hj2 => by have := hdr4 j hj1 hj2; beta_reduce at *; omega))
  refine ⟨-t, nxt, by omega, h2, ?_, ?_, ?_⟩
  · intro e τ h hn j hj1 hj2
    have := h3 e τ h hn j hj1 hj2
    beta_reduce at *; omega
  · intro e τ σ h hn
    obtain ⟨p1, p2, p3, p4⟩ := h4 e τ σ h hn
    exact ⟨p1, p2, by omega, fun j hj1 hj2 => by have := p4 j hj1 hj2; beta_reduce at *; omega⟩
  · rcases h5 with h5 | ⟨ht, e, τ, σ, dr, p1, p2, p3, p4, p5, p6⟩
    · exact Or.inl h5
    · exact Or.inr ⟨by omega, e, τ, σ, dr, p1, p2, p3, p4, by omega,
        fun j hj1 hj2 => by have := p6 j hj1 hj2; beta_reduce at *; omega⟩

end HPC.Fold.Z77
