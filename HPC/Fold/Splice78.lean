import HPC.Fold.Zig77Main
import HPC.Fold.Open

/-!
# Batch 78: the splice behind Bing's Theorem 4

`fold_low_end` is the greedy jump zigzag of batch 77 run on a sequence to which one *fake* link
at level `0` has been appended after its last link. The fake link is admissible for the
crookedness clause exactly when the last link of the arm meets the first link of the coarse
chain; its time `U` in the fold is a time whose block has every level at most `2`.
-/

namespace HPC.Fold.B78

open Z77

/-- **The fold with a fake low end.** From basepoint `0` of a sequence on `[-p, q]` whose
right end is at level at most `1` and which satisfies the crookedness clause with that end read
at level `0`, both arms fold onto one walk `c`, and a time `U` within one of the right end's
time has `c U ≤ 1`. -/
theorem fold_low_end (S : ℤ → ℤ) (p q : ℕ) (Hb : ℤ)
    (hcr : CrkOn S (-(p : ℤ)) q)
    (hlip : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → |S (x + 1) - S x| ≤ 1)
    (hnn : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → 0 ≤ S x)
    (hH : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → S x ≤ Hb)
    (hend : S q ≤ 1)
    (hmeet : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → 3 ≤ S x →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ S y ≤ 1 ∧ S x - 2 ≤ S y' ∧ S y' ≤ S x - 1) :
    ∃ (c : ℕ → ℤ) (βR βL : ℕ → ℕ) (U : ℕ),
      βR 0 = 0 ∧ βL 0 = 0 ∧
      (∀ j, j < q → |((βR (j + 1) : ℕ) : ℤ) - ((βR j : ℕ) : ℤ)| ≤ 1) ∧
      (∀ j, j < p → |((βL (j + 1) : ℕ) : ℤ) - ((βL j : ℕ) : ℤ)| ≤ 1) ∧
      (∀ j : ℕ, j ≤ q → |S j - c (βR j)| ≤ 1) ∧
      (∀ j : ℕ, j ≤ p → |S (-(j : ℤ)) - c (βL j)| ≤ 1) ∧
      |(U : ℤ) - ((βR q : ℕ) : ℤ)| ≤ 1 ∧ c U ≤ 1 := by
  classical
  set S' : ℤ → ℤ := fun x => if x = (q : ℤ) + 1 then 0 else S x with hS'
  have hS'eq : ∀ x : ℤ, x ≤ q → S' x = S x := by
    intro x hx; simp only [hS']; rw [if_neg (by omega)]
  have hS'q1 : S' ((q : ℤ) + 1) = 0 := by simp [hS']
  set M : Bool → ℕ := fun e => if e then q + 2 else p + 1 with hMdef
  have hcr' : CrkOn S' (1 - M false) (M true - 1) := by
    have e1 : (1 : ℤ) - ((M false : ℕ) : ℤ) = -(p : ℤ) := by simp [hMdef]
    have e2 : ((M true : ℕ) : ℤ) - 1 = (q : ℤ) + 1 := by simp [hMdef]; ring
    rw [e1, e2]
    intro s t hs hst ht
    rcases lt_or_eq_of_le ht with ht' | ht'
    · have ht'' : t ≤ q := by omega
      obtain ⟨h1, h2⟩ := hcr s t hs hst ht''
      rw [hS'eq s (by omega), hS'eq t ht'']
      constructor
      · intro h
        obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h1 h
        exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
          by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
          by rw [hS'eq r' (by omega)]; exact a7⟩
      · intro h
        obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h2 h
        exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
          by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
          by rw [hS'eq r' (by omega)]; exact a7⟩
    · subst ht'
      rw [hS'eq s (by omega), hS'q1]
      have hs0 := hnn s hs (by omega)
      constructor
      · intro h; omega
      · intro h
        have hsq : s < q := by
          rcases lt_or_eq_of_le (show s ≤ q by omega) with h' | h'
          · exact h'
          · subst h'; omega
        obtain ⟨y, y', a1, a2, a3, a4, a5, a6⟩ := hmeet s hs hsq (by omega)
        have hy0 := hnn y (by omega) (by omega)
        refine ⟨y, y', a1, a2, by omega, ?_, ?_, ?_, ?_⟩
        · rw [hS'eq y (by omega)]; exact hy0
        · rw [hS'eq y (by omega)]; omega
        · rw [hS'eq y' (by omega)]; exact a5
        · rw [hS'eq y' (by omega)]; exact a6
  have harmT : ∀ j : ℕ, arm S' true j = S' j := fun j => by simp [arm]
  have harmF : ∀ j : ℕ, arm S' false j = S' (-(j : ℤ)) := fun j => by simp [arm]
  have hlipA : ∀ e, LipOn (arm S' e) (M e) := by
    intro e j hj
    cases e
    · simp only [hMdef, Bool.false_eq_true, if_false] at hj
      rw [harmF, harmF, hS'eq _ (by omega), hS'eq _ (by omega), abs_sub_comm]
      have := hlip (-((j + 1 : ℕ) : ℤ)) (by push_cast; omega) (by push_cast; omega)
      push_cast at this ⊢
      rw [show -((j : ℤ) + 1) + 1 = -(j : ℤ) by ring] at this
      exact this
    · simp only [hMdef, if_true] at hj
      rw [harmT, harmT]
      rcases lt_or_eq_of_le (show j ≤ q by omega) with hjq | hjq
      · rw [hS'eq _ (by push_cast; omega), hS'eq _ (by omega)]
        have := hlip (j : ℤ) (by omega) (by exact_mod_cast hjq)
        push_cast; exact this
      · rw [hjq]
        push_cast
        rw [hS'q1, hS'eq _ le_rfl]
        have := hnn q (by omega) le_rfl
        rw [abs_le]; constructor <;> omega
  have hHb : 0 ≤ Hb := le_trans (hnn 0 (by omega) (by omega)) (hH 0 (by omega) (by omega))
  have hLA : ∀ e j, j < M e → (0 : ℤ) ≤ arm S' e j := by
    intro e j hj
    cases e
    · simp only [hMdef, Bool.false_eq_true, if_false] at hj
      rw [harmF, hS'eq _ (by omega)]; exact hnn _ (by omega) (by omega)
    · simp only [hMdef, if_true] at hj
      rw [harmT]
      rcases lt_or_eq_of_le (show j ≤ q + 1 by omega) with hjq | hjq
      · rw [hS'eq _ (by omega)]; exact hnn _ (by omega) (by omega)
      · rw [hjq]; push_cast; rw [hS'q1]
  have hHA : ∀ e j, j < M e → arm S' e j ≤ Hb := by
    intro e j hj
    cases e
    · simp only [hMdef, Bool.false_eq_true, if_false] at hj
      rw [harmF, hS'eq _ (by omega)]; exact hH _ (by omega) (by omega)
    · simp only [hMdef, if_true] at hj
      rw [harmT]
      rcases lt_or_eq_of_le (show j ≤ q + 1 by omega) with hjq | hjq
      · rw [hS'eq _ (by omega)]; exact hH _ (by omega) (by omega)
      · rw [hjq]; push_cast; rw [hS'q1]; exact hHb
  have hM : ∀ e, 0 < M e := by intro e; cases e <;> simp [hMdef]
  obtain ⟨T0, ts, hT0, hfit⟩ := greedy_fit hcr' hlipA hLA hHA hM
  have hfold : ∀ e, ∃ β : ℕ → ℕ, β 0 = 0 ∧ (∀ j, 0 ≤ j → j < M e → β j < jlen T0 ts) ∧
      (∀ j, 0 ≤ j → j + 1 < M e → |((β (j + 1) : ℕ) : ℤ) - ((β j : ℕ) : ℤ)| ≤ 1) ∧
      ∀ j, 0 ≤ j → j < M e → |arm S' e j - jwalk T0 ts (β j)| ≤ 1 := fun e =>
    fold_of_fit (hlipA e) ts 0 T0 (hfit e) (by rw [arm_zero]; exact hT0)
  obtain ⟨βT, a1, -, a3, a4⟩ := hfold true
  obtain ⟨βF, b1, -, b3, b4⟩ := hfold false
  refine ⟨jwalk T0 ts, βT, βF, βT (q + 1), a1, b1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; exact a3 j (Nat.zero_le _) (by simp [hMdef]; omega)
  · intro j hj; exact b3 j (Nat.zero_le _) (by simp [hMdef]; omega)
  · intro j hj
    have := a4 j (Nat.zero_le _) (by simp [hMdef]; omega)
    rwa [harmT, hS'eq _ (by exact_mod_cast hj)] at this
  · intro j hj
    have := b4 j (Nat.zero_le _) (by simp [hMdef]; omega)
    rwa [harmF, hS'eq _ (by omega)] at this
  · have := a3 q (Nat.zero_le _) (by simp [hMdef])
    exact this
  · have := a4 (q + 1) (Nat.zero_le _) (by simp [hMdef])
    rw [harmT] at this
    push_cast at this
    rw [hS'q1, abs_le] at this
    omega

/-- **The splice, on levels.** `ρ` and `σ` are the least and greatest coarse indices of the
links. The prefix fold `(cP, βP, U)` lives on `[0, a]`, the suffix fold `(cQ, βQ, V)` on
`[b, n)` and is read on the reversed levels `N - 1 - σ`. Kept prefix blocks come first, then
the remaining links grouped by level, then the kept suffix blocks in reverse order. -/
theorem splice_schedule {n : ℕ} (N : ℕ) (hN : 6 ≤ N) (ρ σ : Fin n → ℤ)
    (h0 : ∀ t, 0 ≤ ρ t) (hρσ : ∀ t, ρ t ≤ σ t) (hσN : ∀ t, σ t ≤ N - 1)
    (hlipρ : ∀ t t' : Fin n, t'.val = t.val + 1 → |ρ t' - ρ t| ≤ 1)
    (hlipσ : ∀ t t' : Fin n, t'.val = t.val + 1 → |σ t' - σ t| ≤ 1)
    (hcross : ∀ t t' : Fin n, t'.val = t.val + 1 → |σ t' - ρ t| ≤ 1)
    (r a b s : Fin n) (hra : r ≤ a) (hab : a < b) (hbs : b ≤ s)
    (ha : ρ a ≤ 1) (hb : (N : ℤ) - 2 ≤ σ b)
    (cP : ℕ → ℤ) (βP : Fin n → ℕ) (U : ℕ)
    (hP0 : βP r = 0)
    (hPlip : ∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(βP t' : ℤ) - βP t| ≤ 1)
    (hPw : ∀ t, t ≤ a → |ρ t - cP (βP t)| ≤ 1) (hPU : |(U : ℤ) - βP a| ≤ 1) (hcU : cP U ≤ 1)
    (cQ : ℕ → ℤ) (βQ : Fin n → ℕ) (V : ℕ)
    (hQ0 : βQ s = 0)
    (hQlip : ∀ t t' : Fin n, t'.val = t.val + 1 → b ≤ t → |(βQ t' : ℤ) - βQ t| ≤ 1)
    (hQw : ∀ t, b ≤ t → |((N : ℤ) - 1 - σ t) - cQ (βQ t)| ≤ 1)
    (hQV : |(V : ℤ) - βQ b| ≤ 1) (hcV : cQ V ≤ 1) :
    ∃ β : Fin n → ℕ, (∀ t t' : Fin n, t'.val = t.val + 1 → |(β t' : ℤ) - β t| ≤ 1) ∧
      β r = 0 ∧ (∀ t, β t ≤ β s) ∧
      ∀ v, ∃ w : ℕ, ∀ t, β t = v →
        ((w : ℤ) ≤ ρ t ∧ ρ t ≤ w + 2) ∨ ((w : ℤ) ≤ σ t ∧ σ t ≤ w + 2) := by
  classical
  have hra' : r.val ≤ a.val := hra
  have hab' : a.val < b.val := hab
  have hbs' : b.val ≤ s.val := hbs
  set G : ℕ := N - 5 with hG
  have hGpos : 1 ≤ G := by omega
  have hGN : (G : ℤ) = (N : ℤ) - 5 := by omega
  set gz : ℤ → ℕ := fun x => (max 0 (min (x - 2) (G : ℤ))).toNat with hgz
  set g : Fin n → ℕ := fun t => if t < b then gz (ρ t) else gz (σ t) with hg
  set KP : Fin n → Prop := fun t => t ≤ a ∧ βP t < U with hKP
  set KS : Fin n → Prop := fun t => b ≤ t ∧ βQ t < V with hKS
  set β : Fin n → ℕ := fun t => if KP t then βP t
      else if KS t then U + G + V - βQ t else U + g t with hβ
  have hab3 : a.val + 3 ≤ b.val := by
    by_contra hc
    rcases (show b.val = a.val + 1 ∨ b.val = a.val + 2 by omega) with h1 | h1
    · have := hcross a b h1; rw [abs_le] at this; omega
    · have hm : a.val + 1 < n := by have := b.isLt; omega
      have h2 := hcross ⟨a.val + 1, hm⟩ b (by simp only; omega)
      have h3 := hlipρ a ⟨a.val + 1, hm⟩ rfl
      rw [abs_le] at h2 h3; omega
  have vKP : ∀ t, KP t → β t = βP t := fun t h => by simp only [hβ]; rw [if_pos h]
  have vKS : ∀ t, ¬ KP t → KS t → β t = U + G + V - βQ t := fun t h1 h2 => by
    simp only [hβ]; rw [if_neg h1, if_pos h2]
  have vDS : ∀ t, ¬ KP t → ¬ KS t → β t = U + g t := fun t h1 h2 => by
    simp only [hβ]; rw [if_neg h1, if_neg h2]
  have gL : ∀ t : Fin n, t < b → g t = gz (ρ t) := fun t h => by simp only [hg]; rw [if_pos h]
  have gR : ∀ t : Fin n, b ≤ t → g t = gz (σ t) := fun t h => by
    simp only [hg]; rw [if_neg (not_lt.mpr h)]
  have KPle : ∀ t, KP t → t.val ≤ a.val := fun t h => h.1
  have KSge : ∀ t, KS t → b.val ≤ t.val := fun t h => h.1
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · -- Lipschitz
    intro t t' htt'
    by_cases p1 : KP t <;> by_cases p2 : KP t'
    · rw [vKP t p1, vKP t' p2]; exact hPlip t t' htt' p2.1
    · -- leaving the kept prefix
      have ht'b : ¬ KS t' := fun h => by have := KSge t' h; have := KPle t p1; omega
      rw [vKP t p1, vDS t' p2 ht'b, gL t' (by rw [Fin.lt_def]; have := KPle t p1; omega)]
      have hPt := p1.2
      by_cases ht'a : t' ≤ a
      · have hU : U ≤ βP t' := by
          by_contra hc; exact p2 ⟨ht'a, by omega⟩
        have hl := hPlip t t' htt' ht'a
        have hw := hPw t' ht'a
        have hβt' : βP t' = U := by rw [abs_le] at hl; omega
        rw [hβt'] at hw
        rw [abs_le] at hl hw ⊢
        simp only [hgz]; push_cast; omega
      · have hta : t = a := by
          apply Fin.ext; have := KPle t p1; rw [Fin.le_def] at ht'a; omega
        subst hta
        have hl := hlipρ t t' htt'
        rw [abs_le] at hl hPU ⊢
        simp only [hgz]; push_cast; omega
    · -- entering the kept prefix
      have htb : ¬ KS t := fun h => by have := KSge t h; have := KPle t' p2; omega
      have hta : t ≤ a := by rw [Fin.le_def]; have := KPle t' p2; omega
      rw [vKP t' p2, vDS t p1 htb, gL t (by rw [Fin.lt_def]; have := KPle t' p2; omega)]
      have hU : U ≤ βP t := by by_contra hc; exact p1 ⟨hta, by omega⟩
      have hl := hPlip t t' htt' p2.1
      have hPt' := p2.2
      have hw := hPw t hta
      have hβt : βP t = U := by rw [abs_le] at hl; omega
      rw [hβt] at hw
      rw [abs_le] at hl hw ⊢
      simp only [hgz]; push_cast; omega
    · by_cases q1 : KS t <;> by_cases q2 : KS t'
      · rw [vKS t p1 q1, vKS t' p2 q2]
        have hl := hQlip t t' htt' q1.1
        have := q1.2; have := q2.2
        rw [abs_le] at hl ⊢; push_cast [Nat.cast_sub (show βQ t ≤ U + G + V by omega),
          Nat.cast_sub (show βQ t' ≤ U + G + V by omega)]; omega
      · -- leaving the kept suffix upwards in index
        have ht'b : b ≤ t' := by rw [Fin.le_def]; have := KSge t q1; omega
        rw [vKS t p1 q1, vDS t' p2 q2, gR t' ht'b]
        have hV : V ≤ βQ t' := by by_contra hc; exact q2 ⟨ht'b, by omega⟩
        have hl := hQlip t t' htt' q1.1
        have hqt := q1.2
        have hw := hQw t' ht'b
        have hβt' : βQ t' = V := by rw [abs_le] at hl; omega
        rw [hβt'] at hw
        rw [abs_le] at hl hw ⊢
        push_cast [Nat.cast_sub (show βQ t ≤ U + G + V by omega)]
        simp only [hgz]; omega
      · -- entering the kept suffix
        rw [vKS t' p2 q2, vDS t p1 q1]
        have hqt' := q2.2
        by_cases htb : b ≤ t
        · rw [gR t htb]
          have hV : V ≤ βQ t := by by_contra hc; exact q1 ⟨htb, by omega⟩
          have hl := hQlip t t' htt' htb
          have hw := hQw t htb
          have hβt : βQ t = V := by rw [abs_le] at hl; omega
          rw [hβt] at hw
          rw [abs_le] at hl hw ⊢
          push_cast [Nat.cast_sub (show βQ t' ≤ U + G + V by omega)]
          simp only [hgz]; omega
        · have ht'b : t' = b := by
            apply Fin.ext; have := KSge t' q2; rw [Fin.le_def] at htb; omega
          subst ht'b
          rw [gL t (lt_of_not_ge htb)]
          have hc := hcross t t' htt'
          rw [abs_le] at hc hQV ⊢
          push_cast [Nat.cast_sub (show βQ t' ≤ U + G + V by omega)]
          simp only [hgz]; omega
      · rw [vDS t p1 q1, vDS t' p2 q2]
        by_cases h1 : t' < b
        · have h1' : t < b := by rw [Fin.lt_def] at h1 ⊢; omega
          rw [gL t h1', gL t' h1]
          have hl := hlipρ t t' htt'
          rw [abs_le] at hl ⊢; simp only [hgz]; push_cast; omega
        · by_cases h2 : b ≤ t
          · rw [gR t h2, gR t' (not_lt.mp h1)]
            have hl := hlipσ t t' htt'
            rw [abs_le] at hl ⊢; simp only [hgz]; push_cast; omega
          · rw [gL t (lt_of_not_ge h2), gR t' (not_lt.mp h1)]
            have hl := hcross t t' htt'
            rw [abs_le] at hl ⊢; simp only [hgz]; push_cast; omega
  · -- the basepoint `r` opens the first block
    by_cases hU : 0 < U
    · rw [vKP r ⟨hra, by omega⟩, hP0]
    · have hU0 : U = 0 := by omega
      have hnKP : ¬ KP r := fun h => by have := h.2; omega
      have hnKS : ¬ KS r := fun h => by have := KSge r h; omega
      rw [vDS r hnKP hnKS, gL r (by rw [Fin.lt_def]; omega)]
      have hw := hPw r hra
      rw [hP0, ← hU0] at hw
      rw [abs_le] at hw
      simp only [hgz]; omega
  · -- `s` closes the last block
    have hβle : ∀ t, β t ≤ U + G + V := by
      intro t
      by_cases p1 : KP t
      · rw [vKP t p1]; have := p1.2; omega
      · by_cases q1 : KS t
        · rw [vKS t p1 q1]; omega
        · rw [vDS t p1 q1]
          have : g t ≤ G := by
            simp only [hg, hgz]; split_ifs <;> omega
          omega
    have hnKPs : ¬ KP s := fun h => by have := KPle s h; omega
    by_cases hV : 0 < V
    · intro t
      rw [vKS s hnKPs ⟨hbs, by omega⟩, hQ0]
      have := hβle t; omega
    · have hV0 : V = 0 := by omega
      have hnKS : ∀ t, ¬ KS t := fun t h => by have := h.2; omega
      intro t
      rw [vDS s hnKPs (hnKS s), gR s hbs]
      have hw := hQw s hbs
      rw [hQ0, ← hV0] at hw
      rw [abs_le] at hw
      have hgs : gz (σ s) = G := by simp only [hgz]; omega
      rw [hgs]
      by_cases p1 : KP t
      · rw [vKP t p1]; have := p1.2; omega
      · rw [vDS t p1 (hnKS t)]
        have : g t ≤ G := by
          simp only [hg, hgz]; split_ifs <;> omega
        omega
  · -- every block lies in three consecutive levels
    intro v
    by_cases hv1 : v < U
    · refine ⟨(cP v - 1).toNat, fun t ht => Or.inl ?_⟩
      have p1 : KP t := by
        by_contra p1
        by_cases q1 : KS t
        · rw [vKS t p1 q1] at ht; have := q1.2; omega
        · rw [vDS t p1 q1] at ht; omega
      rw [vKP t p1] at ht
      have hw := hPw t p1.1
      rw [ht, abs_le] at hw
      have := h0 t
      omega
    · by_cases hv2 : v ≤ U + G
      · refine ⟨if v - U = G then G + 2 else v - U, fun t ht => ?_⟩
        have p1 : ¬ KP t := fun p1 => by rw [vKP t p1] at ht; have := p1.2; omega
        have q1 : ¬ KS t := fun q1 => by rw [vKS t p1 q1] at ht; have := q1.2; omega
        rw [vDS t p1 q1] at ht
        have hρ0 := h0 t
        have hσ1 := hσN t
        have hρσt := hρσ t
        by_cases htb : t < b
        · left
          rw [gL t htb] at ht
          simp only [hgz] at ht
          split_ifs with hj <;> push_cast <;> omega
        · right
          rw [gR t (not_lt.mp htb)] at ht
          simp only [hgz] at ht
          split_ifs with hj <;> push_cast <;> omega
      · refine ⟨((N : ℤ) - 2 - cQ (U + G + V - v)).toNat, fun t ht => Or.inr ?_⟩
        have p1 : ¬ KP t := fun p1 => by rw [vKP t p1] at ht; have := p1.2; omega
        have q1 : KS t := by
          by_contra q1
          rw [vDS t p1 q1] at ht
          have : g t ≤ G := by simp only [hg, hgz]; split_ifs <;> omega
          omega
        rw [vKS t p1 q1] at ht
        have hq := q1.2
        have hβQ : βQ t = U + G + V - v := by omega
        have hw := hQw t q1.1
        rw [hβQ, abs_le] at hw
        have hρ0 := h0 t
        have hρσt := hρσ t
        omega

/-! ## Chain-level pieces -/

section ChainLevel

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- The least index of a refinement depends only on the link. -/
theorem minIdx_congr {m m' N : ℕ} {E : Chain X m} {E' : Chain X m'} {D : Chain X N}
    (h : E.Refines D) (h' : E'.Refines D) (t : Fin m) (t' : Fin m')
    (heq : E.link t = E'.link t') : (h.minIdx t).val = (h'.minIdx t').val := by
  unfold Chain.Refines.minIdx
  simp only [heq]

/-- **The crookedness clause read at a link meeting the first coarse link.** Between a link at
least three levels up and a later link meeting `D.link 0`, the chain first comes down to level
at most `1` and then returns to one of the two levels just below the first. -/
theorem meet_low_before {n N : ℕ} {E : Chain X n} {D : Chain X N} (hcr : E.IsCrookedIn' D)
    (hN : 0 < N) (e t : Fin n) (he : (E.link e ∩ D.link ⟨0, hN⟩).Nonempty) (hte : t < e)
    (h3 : 3 ≤ (hcr.1.minIdx t).val) :
    ∃ y y' : Fin n, t < y ∧ y < y' ∧ y' < e ∧ (hcr.1.minIdx y).val ≤ 1 ∧
      (hcr.1.minIdx t).val ≤ (hcr.1.minIdx y').val + 2 ∧
      (hcr.1.minIdx y').val + 1 ≤ (hcr.1.minIdx t).val := by
  set k := hcr.1.minIdx t with hk
  have hkN := k.isLt
  obtain ⟨z, hz⟩ := E.link_nonempty t
  obtain ⟨r, s, hbtw, hr, hs⟩ := hcr.2 ⟨0, hN⟩ k (by simp only; omega) e t he
    ⟨z, hz, minIdx_subset hcr.1 t hz⟩
  have hte' : t.val < e.val := hte
  rcases hbtw with ⟨h1, h2, h3'⟩ | ⟨h1, h2, h3'⟩
  · exfalso
    have : e.val < t.val := lt_trans (lt_trans h1 h2) h3'
    omega
  · refine ⟨s, r, h3', h2, h1, ?_, ?_, ?_⟩
    · have := minIdx_le hcr.1 s hs
      rw [Fin.le_def] at this; simpa using this
    · have := subset_adjacent_of_subset hcr.1 r (minIdx_subset hcr.1 r) hr
      simp only at this; omega
    · have := minIdx_le hcr.1 r hr
      rw [Fin.le_def] at this; simp only at this; omega

/-- The re-indexed sequence at an index inside the range. -/
theorem reindex_eq {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (x : ℤ) (h1 : 0 ≤ (i : ℤ) + x)
    (h2 : (i : ℤ) + x < n) : Z77.reindex ρ i x = ρ ⟨((i : ℤ) + x).toNat, by omega⟩ := by
  unfold Z77.reindex
  rw [dif_pos ⟨h1, h2⟩]

/-- **The prefix fold.** For a basepoint `r` and a later link `a` meeting `D.link 0`, a common
fold of the chain on `[0, a]` from `r`, together with a time `U` within one of the time of `a`
whose centre is at most `1`. -/
theorem prefix_fold {n N : ℕ} {E : Chain X n} {D : Chain X N} (hcr : E.IsCrookedIn' D)
    (hN : 0 < N) (r a : Fin n) (hra : r ≤ a) (ha : (E.link a ∩ D.link ⟨0, hN⟩).Nonempty) :
    ∃ (c : ℕ → ℤ) (β : Fin n → ℕ) (U : ℕ), β r = 0 ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(β t' : ℤ) - β t| ≤ 1) ∧
      (∀ t : Fin n, t ≤ a → |((hcr.1.minIdx t : ℕ) : ℤ) - c (β t)| ≤ 1) ∧
      |(U : ℤ) - β a| ≤ 1 ∧ c U ≤ 1 := by
  classical
  set ρ : Fin n → ℤ := fun t => ((hcr.1.minIdx t : ℕ) : ℤ) with hρ
  set S := Z77.reindex ρ r with hS
  have hra' : r.val ≤ a.val := hra
  have han := a.isLt
  have hcrI : IsCrookedIvF ρ (fun t => ((hcr.1.maxIdx t : ℕ) : ℤ)) :=
    isCrookedIvF_minIdx_maxIdx hcr
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = a.val - r.val := ⟨_, rfl⟩
  have hqv : (q : ℤ) = (a.val : ℤ) - r.val := by omega
  have hCrk : Z77.CrkOn S (-(r.val : ℤ)) q := by
    have h := Z77.crkOn_of_isCrookedIvF hcrI r
    intro x y hx hxy hy
    exact h x y hx hxy (by omega)
  have hSval : ∀ (x : ℤ) (h1 : -(r.val : ℤ) ≤ x) (h2 : x ≤ q),
      S x = ρ ⟨((r : ℤ) + x).toNat, by omega⟩ :=
    fun x h1 h2 => reindex_eq ρ r x (by omega) (by omega)
  have hlipS : ∀ x : ℤ, -(r.val : ℤ) ≤ x → x < q → |S (x + 1) - S x| ≤ 1 := by
    intro x h1 h2
    rw [hSval (x + 1) (by omega) (by omega), hSval x h1 (by omega)]
    have := minIdx_lip hcr.1 ⟨((r : ℤ) + x).toNat, by omega⟩
      ⟨((r : ℤ) + (x + 1)).toNat, by omega⟩ (by simp only; omega)
    simp only [hρ]; rw [abs_le]; omega
  have hnn : ∀ x : ℤ, -(r.val : ℤ) ≤ x → x ≤ q → 0 ≤ S x := by
    intro x h1 h2
    rw [hSval x h1 h2]; simp only [hρ]; omega
  have hH : ∀ x : ℤ, -(r.val : ℤ) ≤ x → x ≤ q → S x ≤ N := by
    intro x h1 h2
    rw [hSval x h1 h2]; simp only [hρ]
    have := (hcr.1.minIdx ⟨((r : ℤ) + x).toNat, by omega⟩).isLt; omega
  have hend : S q ≤ 1 := by
    rw [hSval q (by omega) le_rfl]
    have h := minIdx_near_of_inter hcr.1 a ⟨0, hN⟩ ha
    have he : (⟨((r : ℤ) + q).toNat, by omega⟩ : Fin n) = a := Fin.ext (by simp only; omega)
    rw [he]; simp only [hρ] at h ⊢; omega
  have hmeet : ∀ x : ℤ, -(r.val : ℤ) ≤ x → x < q → 3 ≤ S x →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ S y ≤ 1 ∧ S x - 2 ≤ S y' ∧ S y' ≤ S x - 1 := by
    intro x h1 h2 h3
    rw [hSval x h1 (by omega)] at h3 ⊢
    set t : Fin n := ⟨((r : ℤ) + x).toNat, by omega⟩ with ht
    have htv : (t.val : ℤ) = r + x := by simp only [ht]; omega
    obtain ⟨y, y', a1, a2, a3, a4, a5, a6⟩ := meet_low_before hcr hN a t ha
      (by rw [Fin.lt_def]; omega) (by simp only [hρ] at h3; omega)
    rw [Fin.lt_def] at a1 a2 a3
    refine ⟨(y : ℤ) - r, (y' : ℤ) - r, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hSval _ (by omega) (by omega)]
      have : (⟨((r : ℤ) + ((y : ℤ) - r)).toNat, by omega⟩ : Fin n) = y :=
        Fin.ext (by simp only; omega)
      rw [this]; simp only [hρ]; omega
    · rw [hSval _ (by omega) (by omega)]
      have : (⟨((r : ℤ) + ((y' : ℤ) - r)).toNat, by omega⟩ : Fin n) = y' :=
        Fin.ext (by simp only; omega)
      rw [this]; simp only [hρ]; omega
    · rw [hSval _ (by omega) (by omega)]
      have : (⟨((r : ℤ) + ((y' : ℤ) - r)).toNat, by omega⟩ : Fin n) = y' :=
        Fin.ext (by simp only; omega)
      rw [this]; simp only [hρ]; omega
  obtain ⟨c, βR, βL, U, h0R, h0L, hlR, hlL, hwR, hwL, hU, hcU⟩ :=
    fold_low_end S r.val q N hCrk hlipS hnn hH hend hmeet
  have hSt : ∀ t : Fin n, t ≤ a → r ≤ t → S ((t.val - r.val : ℕ) : ℤ) = ρ t := by
    intro t hta hrt
    rw [Fin.le_def] at hta hrt
    rw [hSval _ (by omega) (by omega)]
    exact congrArg ρ (Fin.ext (by simp only; omega))
  have hSt' : ∀ t : Fin n, t < r → S (-((r.val - t.val : ℕ) : ℤ)) = ρ t := by
    intro t htr
    rw [Fin.lt_def] at htr
    rw [hSval _ (by omega) (by omega)]
    exact congrArg ρ (Fin.ext (by simp only; omega))
  refine ⟨c, fun t => if r ≤ t then βR (t.val - r.val) else βL (r.val - t.val), U, ?_, ?_, ?_,
    ?_, hcU⟩
  · simp only [le_refl, if_true, Nat.sub_self, h0R]
  · intro t t' htt' ht'a
    rw [Fin.le_def] at ht'a
    simp only []
    by_cases h1 : r ≤ t
    · have h1' : r ≤ t' := by rw [Fin.le_def] at h1 ⊢; omega
      rw [if_pos h1, if_pos h1']
      rw [Fin.le_def] at h1
      rw [show t'.val - r.val = (t.val - r.val) + 1 by omega]
      exact hlR _ (by omega)
    · rw [if_neg h1]
      rw [Fin.le_def] at h1
      by_cases h2 : r ≤ t'
      · rw [if_pos h2]
        rw [Fin.le_def] at h2
        rw [show t'.val - r.val = 0 by omega, h0R, show r.val - t.val = 0 + 1 by omega]
        have := hlL 0 (by omega)
        rw [h0L] at this
        rw [abs_sub_comm]; simpa using this
      · rw [if_neg h2]
        rw [Fin.le_def] at h2
        rw [show r.val - t.val = (r.val - t'.val) + 1 by omega, abs_sub_comm]
        exact hlL _ (by omega)
  · intro t hta
    simp only []
    by_cases h1 : r ≤ t
    · rw [if_pos h1]
      have := hwR (t.val - r.val) (by rw [Fin.le_def] at hta h1; omega)
      rw [hSt t hta h1] at this
      exact this
    · rw [if_neg h1]
      have h1' : t < r := lt_of_not_ge h1
      have := hwL (r.val - t.val) (by omega)
      rw [hSt' t h1'] at this
      exact this
  · simp only [hra, if_true]
    rw [← hq]
    exact hU

/-- **The suffix fold**: `prefix_fold` for the reversed chains. Levels are read as
`N - 1 - maxIdx`, the least index in the reversed coarse chain. -/
theorem suffix_fold {n N : ℕ} {E : Chain X n} {D : Chain X N} (hcr : E.IsCrookedIn' D)
    (hN : 0 < N) (b s : Fin n) (hbs : b ≤ s)
    (hb : (E.link b ∩ D.link ⟨N - 1, by omega⟩).Nonempty) :
    ∃ (c : ℕ → ℤ) (β : Fin n → ℕ) (V : ℕ), β s = 0 ∧
      (∀ t t' : Fin n, t'.val = t.val + 1 → b ≤ t → |(β t' : ℤ) - β t| ≤ 1) ∧
      (∀ t : Fin n, b ≤ t → |((N : ℤ) - 1 - ((hcr.1.maxIdx t : ℕ) : ℤ)) - c (β t)| ≤ 1) ∧
      |(V : ℤ) - β b| ≤ 1 ∧ c V ≤ 1 := by
  classical
  have hcr' : E.reverse.IsCrookedIn' D.reverse := hcr.reverse_left.reverse_right
  have hrs : Fin.rev s ≤ Fin.rev b := Fin.rev_le_rev.mpr hbs
  have hb' : (E.reverse.link (Fin.rev b) ∩ D.reverse.link ⟨0, hN⟩).Nonempty := by
    rw [reverse_link, reverse_link, Fin.rev_rev]
    have : Fin.rev (⟨0, hN⟩ : Fin N) = ⟨N - 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev])
    rw [this]; exact hb
  obtain ⟨c, β', U, h0, hlip, hw, hU, hcU⟩ :=
    prefix_fold hcr' hN (Fin.rev s) (Fin.rev b) hrs hb'
  refine ⟨c, fun t => β' (Fin.rev t), U, h0, ?_, ?_, hU, hcU⟩
  · intro t t' htt' hbt
    have h1 : (Fin.rev t).val = (Fin.rev t').val + 1 := by
      simp only [Fin.val_rev]; have := t'.isLt; omega
    have h2 : Fin.rev t ≤ Fin.rev b := Fin.rev_le_rev.mpr hbt
    have := hlip (Fin.rev t') (Fin.rev t) h1 h2
    rw [abs_sub_comm]; exact this
  · intro t hbt
    have h2 : Fin.rev t ≤ Fin.rev b := Fin.rev_le_rev.mpr hbt
    have := hw (Fin.rev t) h2
    have hc := minIdx_congr hcr'.1 hcr.1.reverse_right (Fin.rev t) t
      (by rw [reverse_link, Fin.rev_rev])
    have hm : (hcr.1.maxIdx t).val = N - 1 - (hcr.1.reverse_right.minIdx t).val := by
      unfold Chain.Refines.maxIdx; rw [Fin.val_rev]; omega
    have hlt := (hcr.1.reverse_right.minIdx t).isLt
    have e : ((hcr'.1.minIdx (Fin.rev t) : ℕ) : ℤ) = (N : ℤ) - 1 - ((hcr.1.maxIdx t : ℕ) : ℤ) := by
      rw [hc, hm]; omega
    rw [e] at this
    exact this

/-- **From a schedule to Theorem 4's conclusion.** A Lipschitz schedule, zero at `r`, largest
at `s`, whose fibres each lie in three consecutive coarse links. -/
theorem assemble {n N : ℕ} {E : Chain X n} {D : Chain X N} (r s : Fin n) (β : Fin n → ℕ)
    (hlip : ∀ t t' : Fin n, t'.val = t.val + 1 → |(β t' : ℤ) - β t| ≤ 1) (hr : β r = 0)
    (hs : ∀ t, β t ≤ β s) (hblk : ∀ v, ∃ w : ℕ, ∀ t, β t = v → E.link t ⊆ D.unionRange w 3) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  have hsch : IsSchedule β :=
    ⟨fun t t' h => by have := hlip t t' h; rw [abs_le] at this; omega, ⟨r, hr⟩⟩
  obtain ⟨p, β', hβ', hval⟩ := hsch.exists_blockMap
  refine ⟨p, β', hβ', by rw [hval, hr], ?_, ?_⟩
  · have hp : 0 < p := (β' r).pos
    obtain ⟨t0, ht0⟩ := hβ'.surj ⟨p - 1, by omega⟩
    have h1 := hs t0
    rw [← hval t0, ← hval s, ht0] at h1
    have h2 := (β' s).isLt
    simp only at h1
    omega
  · intro u
    obtain ⟨w, hw⟩ := hblk u.val
    refine ⟨w, ?_⟩
    rw [ofBlocks_link]
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact hw t (by rw [← hval t, ht]) hxt

/-- A link whose least or greatest coarse index lies in `[w, w + 2]` lies in the three coarse
links from `w`. -/
theorem link_sub_of_level {n N : ℕ} {E : Chain X n} {D : Chain X N} (h : E.Refines D)
    (t : Fin n) (w : ℕ)
    (hw : ((w : ℤ) ≤ ((h.minIdx t : ℕ) : ℤ) ∧ ((h.minIdx t : ℕ) : ℤ) ≤ w + 2) ∨
      ((w : ℤ) ≤ ((h.maxIdx t : ℕ) : ℤ) ∧ ((h.maxIdx t : ℕ) : ℤ) ≤ w + 2)) :
    E.link t ⊆ D.unionRange w 3 := by
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (minIdx_subset h t).trans (link_subset_unionRange D _ (by omega) (by omega))
  · exact (maxIdx_subset h t).trans (link_subset_unionRange D _ (by omega) (by omega))

/-- Three consecutive links of the reversed coarse chain are three consecutive links of the
coarse chain. -/
theorem unionRange_reverse {N : ℕ} (D : Chain X N) (j : ℕ) :
    D.reverse.unionRange j 3 ⊆ D.unionRange (N - 3 - j) 3 := by
  intro x hx
  rw [mem_unionRange] at hx ⊢
  obtain ⟨j', h1, h2, h3, h4⟩ := hx
  rw [reverse_link] at h4
  refine ⟨N - 1 - j', by omega, by omega, by omega, ?_⟩
  have : (⟨N - 1 - j', by omega⟩ : Fin N) = Fin.rev ⟨j', h3⟩ :=
    Fin.ext (by simp [Fin.val_rev]; omega)
  rw [this]; exact h4

/-- **Theorem 4, the main case**: at least six coarse links, a link `a` meeting the first coarse
link before a link `b` meeting the last, `r ≤ a < b ≤ s`. -/
theorem theorem4_core {n N : ℕ} {E : Chain X n} {D : Chain X N} (hN : 6 ≤ N)
    (hcr : E.IsCrookedIn' D) (r a b s : Fin n) (hra : r ≤ a) (hab : a < b) (hbs : b ≤ s)
    (ha : (E.link a ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hb : (E.link b ∩ D.link ⟨N - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  obtain ⟨cP, βP, U, hP0, hPlip, hPw, hPU, hcU⟩ := prefix_fold hcr (by omega) r a hra ha
  obtain ⟨cQ, βQ, V, hQ0, hQlip, hQw, hQV, hcV⟩ := suffix_fold hcr (by omega) b s hbs hb
  have href := hcr.1
  have hρσ : ∀ t, ((hcr.1.minIdx t : ℕ) : ℤ) ≤ ((hcr.1.maxIdx t : ℕ) : ℤ) := by
    intro t
    have := minIdx_le hcr.1 t (maxIdx_subset hcr.1 t)
    rw [Fin.le_def] at this; omega
  have hσN : ∀ t, ((hcr.1.maxIdx t : ℕ) : ℤ) ≤ (N : ℤ) - 1 := by
    intro t; have := (hcr.1.maxIdx t).isLt; omega
  have hlipρ : ∀ t t' : Fin n, t'.val = t.val + 1 →
      |((hcr.1.minIdx t' : ℕ) : ℤ) - ((hcr.1.minIdx t : ℕ) : ℤ)| ≤ 1 := by
    intro t t' h; have := minIdx_lip hcr.1 t t' h; rw [abs_le]; omega
  have hlipσ : ∀ t t' : Fin n, t'.val = t.val + 1 →
      |((hcr.1.maxIdx t' : ℕ) : ℤ) - ((hcr.1.maxIdx t : ℕ) : ℤ)| ≤ 1 := by
    intro t t' h; have := maxIdx_lip hcr.1 t t' h; rw [abs_le]; omega
  have hcross : ∀ t t' : Fin n, t'.val = t.val + 1 →
      |((hcr.1.maxIdx t' : ℕ) : ℤ) - ((hcr.1.minIdx t : ℕ) : ℤ)| ≤ 1 := by
    intro t t' h
    obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t' t).mpr (by omega)
    have := (D.adjacent _ _).mp ⟨z, maxIdx_subset hcr.1 t' hz1, minIdx_subset hcr.1 t hz2⟩
    rw [abs_le]; omega
  have ha' : ((hcr.1.minIdx a : ℕ) : ℤ) ≤ 1 := by
    have := minIdx_near_of_inter hcr.1 a ⟨0, by omega⟩ ha
    simp only at this; omega
  have hb' : (N : ℤ) - 2 ≤ ((hcr.1.maxIdx b : ℕ) : ℤ) := by
    have := minIdx_near_of_inter hcr.1 b ⟨N - 1, by omega⟩ hb
    have := hρσ b
    simp only at *; omega
  obtain ⟨β, hlip, hr, hs, hblk⟩ := splice_schedule N hN
    (fun t => ((hcr.1.minIdx t : ℕ) : ℤ)) (fun t => ((hcr.1.maxIdx t : ℕ) : ℤ))
    (fun t => by positivity) hρσ hσN hlipρ hlipσ hcross r a b s hra hab hbs ha' hb'
    cP βP U hP0 hPlip hPw hPU hcU cQ βQ V hQ0 hQlip hQw hQV hcV
  exact assemble r s β hlip hr hs (fun v => by
    obtain ⟨w, hw⟩ := hblk v
    exact ⟨w, fun t ht => link_sub_of_level hcr.1 t w (hw t ht)⟩)

/-- **Two windows suffice when every link lies in one of them** (used for at most six coarse
links, where every link lies in the first three or the last three). No crookedness. -/
theorem two_window {n N : ℕ} {E : Chain X n} {D : Chain X N} (P Q : Fin n → Prop) (wP wQ : ℕ)
    (hPQ : ∀ t, P t ∨ Q t) (hPw : ∀ t, P t → E.link t ⊆ D.unionRange wP 3)
    (hQw : ∀ t, Q t → E.link t ⊆ D.unionRange wQ 3) (r s : Fin n) (hrs : r < s) (hPr : P r)
    (hcase : Q s ∨ (P s ∧ ∃ c, r < c ∧ c < s ∧ Q c)) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have hrs' : r.val < s.val := hrs
  rcases hcase with hQs | ⟨hPs, c, hrc, hcs, hQc⟩
  · refine assemble r s (fun t => if t = s then 1 else if P t then 0 else 1) ?_ ?_ ?_ ?_
    · intro t t' _
      dsimp only; rw [abs_le]; split_ifs <;> omega
    · simp only [if_neg (ne_of_lt hrs), if_pos hPr]
    · intro t; simp only [if_true]; split_ifs <;> omega
    · intro v
      by_cases hv : v = 0
      · refine ⟨wP, fun t ht => hPw t ?_⟩
        simp only at ht
        split_ifs at ht with h1 h2
        · omega
        · exact h2
        · omega
      · refine ⟨wQ, fun t ht => hQw t ?_⟩
        simp only at ht
        split_ifs at ht with h1 h2
        · rw [h1]; exact hQs
        · omega
        · exact (hPQ t).resolve_left h2
  · have hrc' : r.val < c.val := hrc
    have hcs' : c.val < s.val := hcs
    refine assemble r s (fun t => if t.val < c.val then (if P t then 0 else 1)
      else if t.val = c.val then 1 else (if P t then 2 else 1)) ?_ ?_ ?_ ?_
    · intro t t' htt'
      dsimp only; rw [abs_le]; split_ifs <;> omega
    · simp only [if_pos hrc', if_pos hPr]
    · intro t
      simp only [show ¬ s.val < c.val by omega, show ¬ s.val = c.val by omega, if_false,
        if_pos hPs]
      split_ifs <;> omega
    · intro v
      by_cases hv : v = 1
      · refine ⟨wQ, fun t ht => hQw t ?_⟩
        simp only at ht
        split_ifs at ht with h1 h2 h3 h4
        · omega
        · exact (hPQ t).resolve_left h2
        · have : t = c := Fin.ext h3
          rw [this]; exact hQc
        · omega
        · exact (hPQ t).resolve_left h4
      · refine ⟨wP, fun t ht => hPw t ?_⟩
        simp only at ht
        split_ifs at ht with h1 h2 h3 h4
        · exact h2
        · omega
        · omega
        · exact h4
        · omega

end ChainLevel

end HPC.Fold.B78
