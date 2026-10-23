import HPC.Fold.Pair79Chain

/-!
# Batch 79: the splice for two-link basepoints

`splice_schedule_pair` is `B78.splice_schedule` with the prefix fold read on any levels `lP`
between the least and the greatest coarse indices (and likewise the suffix fold on `lQ`), and
which also reports which links go to the first and to the last block.
-/

namespace HPC.Fold.B79

theorem splice_schedule_pair {n : ℕ} (N : ℕ) (hN : 6 ≤ N) (ρ σ : Fin n → ℤ)
    (h0 : ∀ t, 0 ≤ ρ t) (hρσ : ∀ t, ρ t ≤ σ t) (hσN : ∀ t, σ t ≤ N - 1)
    (hwid : ∀ t, σ t ≤ ρ t + 1) (lP lQ : Fin n → ℤ) (hlP : ∀ t, ρ t ≤ lP t ∧ lP t ≤ σ t)
    (hlQ : ∀ t, ρ t ≤ lQ t ∧ lQ t ≤ σ t)
    (hlipρ : ∀ t t' : Fin n, t'.val = t.val + 1 → |ρ t' - ρ t| ≤ 1)
    (hlipσ : ∀ t t' : Fin n, t'.val = t.val + 1 → |σ t' - σ t| ≤ 1)
    (hcross : ∀ t t' : Fin n, t'.val = t.val + 1 → |σ t' - ρ t| ≤ 1)
    (r a b s : Fin n) (hra : r ≤ a) (hab : a < b) (hbs : b ≤ s)
    (ha : ρ a ≤ 1) (hb : (N : ℤ) - 2 ≤ σ b)
    (cP : ℕ → ℤ) (βP : Fin n → ℕ) (U : ℕ)
    (hP0 : βP r = 0)
    (hPlip : ∀ t t' : Fin n, t'.val = t.val + 1 → t' ≤ a → |(βP t' : ℤ) - βP t| ≤ 1)
    (hPw : ∀ t, t ≤ a → |lP t - cP (βP t)| ≤ 1) (hPU : |(U : ℤ) - βP a| ≤ 1) (hcU : cP U ≤ 1)
    (cQ : ℕ → ℤ) (βQ : Fin n → ℕ) (V : ℕ)
    (hQ0 : βQ s = 0)
    (hQlip : ∀ t t' : Fin n, t'.val = t.val + 1 → b ≤ t → |(βQ t' : ℤ) - βQ t| ≤ 1)
    (hQw : ∀ t, b ≤ t → |((N : ℤ) - 1 - lQ t) - cQ (βQ t)| ≤ 1)
    (hQV : |(V : ℤ) - βQ b| ≤ 1) (hcV : cQ V ≤ 1) :
    ∃ β : Fin n → ℕ, (∀ t t' : Fin n, t'.val = t.val + 1 → |(β t' : ℤ) - β t| ≤ 1) ∧
      β r = 0 ∧ (∀ t, β t ≤ β s) ∧
      (∀ v, ∃ w : ℕ, ∀ t, β t = v →
        ((w : ℤ) ≤ ρ t ∧ ρ t ≤ w + 2) ∨ ((w : ℤ) ≤ σ t ∧ σ t ≤ w + 2)) ∧
      (∀ t, t ≤ a → βP t = 0 → β t = 0) ∧
      (U = 0 → ∀ t, t < b → ρ t ≤ 2 → β t = 0) ∧
      (∀ t, b ≤ t → βQ t = 0 → β t = β s) ∧
      (V = 0 → ∀ t, a < t → (N : ℤ) - 3 ≤ ρ t → β t = β s) := by
  classical
  have hra' : r.val ≤ a.val := hra
  have hab' : a.val < b.val := hab
  have hlP1 := fun t => (hlP t).1
  have hlP2 := fun t => (hlP t).2
  have hlQ1 := fun t => (hlQ t).1
  have hlQ2 := fun t => (hlQ t).2
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
  have hnKPs0 : ¬ KP s := fun h => by have := KPle s h; omega
  have hβs : β s = U + G + V := by
    by_cases hV : 0 < V
    · rw [vKS s hnKPs0 ⟨hbs, by omega⟩, hQ0]; omega
    · have hV0 : V = 0 := by omega
      have hnKS : ¬ KS s := fun h => by have := h.2; omega
      rw [vDS s hnKPs0 hnKS, gR s hbs]
      have hw := hQw s hbs
      rw [hQ0, ← hV0] at hw; rw [abs_le] at hw
      have := hlQ s
      simp only [hgz]; omega
  refine ⟨β, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        have := hlP t'
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
      have := hlP t
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
        have := hlQ t'
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
          have := hlQ t
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
      have := hlP r
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
      have := hlQ s
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
    · refine ⟨(cP v - 1).toNat, fun t ht => ?_⟩
      have p1 : KP t := by
        by_contra p1
        by_cases q1 : KS t
        · rw [vKS t p1 q1] at ht; have := q1.2; omega
        · rw [vDS t p1 q1] at ht; omega
      rw [vKP t p1] at ht
      have hw := hPw t p1.1
      have := hlP t
      rw [ht, abs_le] at hw
      have := h0 t
      have := hwid t
      have := hρσ t
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
      · refine ⟨((N : ℤ) - 2 - cQ (U + G + V - v)).toNat, fun t ht => ?_⟩
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
        have := hlQ t
        rw [hβQ, abs_le] at hw
        have hρ0 := h0 t
        have hρσt := hρσ t
        have := hwid t
        omega
  · intro t hta h0t
    by_cases hU : 0 < U
    · rw [vKP t ⟨hta, by omega⟩]; exact h0t
    · have hU0 : U = 0 := by omega
      have hnKP : ¬ KP t := fun h => by have := h.2; omega
      have hnKS : ¬ KS t := fun h => by have := KSge t h; rw [Fin.le_def] at hta; omega
      rw [vDS t hnKP hnKS, gL t (by rw [Fin.lt_def]; rw [Fin.le_def] at hta; omega)]
      have hw := hPw t hta
      rw [h0t, ← hU0] at hw; rw [abs_le] at hw
      have := hlP t
      simp only [hgz]; omega
  · intro hU0 t htb hρt
    have hnKP : ¬ KP t := fun h => by have := h.2; omega
    have hnKS : ¬ KS t := fun h => by have := KSge t h; rw [Fin.lt_def] at htb; omega
    rw [vDS t hnKP hnKS, gL t htb]
    simp only [hgz]; omega
  · intro t hbt h0t
    rw [hβs]
    have hnKP : ¬ KP t := fun h => by have := KPle t h; rw [Fin.le_def] at hbt; omega
    by_cases hV : 0 < V
    · rw [vKS t hnKP ⟨hbt, by omega⟩, h0t]; omega
    · have hV0 : V = 0 := by omega
      have hnKS : ¬ KS t := fun h => by have := h.2; omega
      rw [vDS t hnKP hnKS, gR t hbt]
      have hw := hQw t hbt
      rw [h0t, ← hV0] at hw; rw [abs_le] at hw
      have := hlQ t
      simp only [hgz]; omega
  · intro hV0 t hat hρt
    rw [hβs]
    have hnKP : ¬ KP t := fun h => by have := KPle t h; rw [Fin.lt_def] at hat; omega
    have hnKS : ¬ KS t := fun h => by have := h.2; omega
    rw [vDS t hnKP hnKS]
    have := hρσ t
    by_cases htb : t < b
    · rw [gL t htb]; simp only [hgz]; omega
    · rw [gR t (not_lt.mp htb)]; simp only [hgz]; omega


end HPC.Fold.B79
