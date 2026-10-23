import HPC.Fold.Recon122Special

/-!
# Batch 122: the general case of Bing's induction, and the main theorem in the model

Bing's general case: `D(h, k)` maximal around `d_i` with no interior link meeting `e₁` or `e_r`,
`H` a consolidation of `D(h, k)` (from the induction hypothesis, or from the special case), cut at
the first block `h_u` of `H` containing a link that meets `e₁` or `e_r`; the remaining links are
grouped by level from the extreme `h_u` meets (`genF`, `genF_concl`). With the special case of
`HPC/Fold/Recon122Special.lean` this proves `bing_main`: Bing's Theorem 3 (block reading, two
adjacent links, \"or\" end clause) in the model.
-/

namespace HPC.Fold.Recon122

/-- The level groups of the general case, bottom-anchored (`0` = \"in `e₁ + e₂`\", `K − 3` = \"in
`e_{r−1} + e_r`\", the others by the least level). -/
def genG (K : ℕ) (ρ σ : ℕ → ℕ) (t : ℕ) : ℕ :=
  if ρ t ≤ 1 then 0 else if K - 2 ≤ σ t then K - 3 else ρ t - 1

theorem genG_lip {K : ℕ} {ρ σ : ℕ → ℕ} {t t' : ℕ} (hK : 5 ≤ K) (h1 : ρ t ≤ σ t)
    (h1' : ρ t' ≤ σ t') (hw : σ t ≤ ρ t + 1) (ha : σ t ≤ ρ t' + 1) (ha' : σ t' ≤ ρ t + 1) :
    genG K ρ σ t ≤ genG K ρ σ t' + 1 := by
  unfold genG; split_ifs <;> omega

/-- The window of a general-case group. -/
def genWin (K g : ℕ) : ℕ := if g = 0 then 0 else if g = K - 3 then K - 2 else g + 1

theorem genWin_spec {K : ℕ} {ρ σ : ℕ → ℕ} {t : ℕ} (hK : 5 ≤ K) (h1 : ρ t ≤ σ t)
    (hs : σ t < K) : genWin K (genG K ρ σ t) ≤ σ t ∧ ρ t ≤ genWin K (genG K ρ σ t) + 1 := by
  unfold genWin genG; split_ifs <;> omega

/-- **Bing's general-case construction**: keep the blocks of `H` before `a`, then the level groups
of all the other links, bottom group first. -/
def genF (K : ℕ) (ρ σ : ℕ → ℕ) (p q a : ℕ) (H : ℕ → ℕ) (t : ℕ) : ℕ :=
  if p ≤ t ∧ t ≤ q ∧ H t < a then H t else a + genG K ρ σ t

theorem genF_concl {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i : ℕ} (h : BHyp n K ρ σ T)
    (hK : 5 ≤ K) {p q : ℕ} (hpq : p ≤ q) (hq : q < n) (hpi : p ≤ i) (hiq : i ≤ q)
    (hleft : 0 < p → (T p 0 ∨ T p (K - 1))) (hright : q + 1 < n → (T q 0 ∨ T q (K - 1)))
    (H : ℕ → ℕ) (hH0 : H i = 0) (hHc : PCons p q ρ σ H) {e a : ℕ} (he : e = p ∨ e = q)
    (ha : a = H e)
    (hHe : ∀ t, p ≤ t → t ≤ q → H t = a → ρ t ≤ 1)
    (hmin : ∀ e', (e' = p ∨ e' = q) → (T e' 0 ∨ T e' (K - 1)) → a ≤ H e') :
    BConcl n K ρ σ T i := by
  have hA : ∀ t, p ≤ t → t ≤ q → H t < a → genF K ρ σ p q a H t = H t := by
    intro t h1 h2 h3; simp [genF, h1, h2, h3]
  have hD : ∀ t, ¬ (p ≤ t ∧ t ≤ q ∧ H t < a) → genF K ρ σ p q a H t = a + genG K ρ σ t := by
    intro t h1; simp only [genF, if_neg h1]
  have hg0 : ∀ t, t < n → (genG K ρ σ t = 0 ↔ ρ t ≤ 1) := by
    intro t ht; have := h.le t ht; unfold genG; split_ifs <;> omega
  have hgK : ∀ t, t < n → genG K ρ σ t = K - 3 → K - 2 ≤ σ t := by
    intro t ht; have := h.le t ht; unfold genG; split_ifs <;> omega
  have hea : p ≤ e ∧ e ≤ q := by omega
  refine ⟨genF K ρ σ p q a H, ?_, ⟨fun t _ ht => ?_, fun v => ?_⟩, fun e' he' hee' hT' => ?_⟩
  · by_cases hia : H i < a
    · rw [hA i hpi hiq hia, hH0]
    · rw [hD i (by omega), (hg0 i (by omega)).mpr (hHe i hpi hiq (by omega))]; omega
  · have hHl := hHc.1
    by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a <;> by_cases hAt' : p ≤ t + 1 ∧ t + 1 ≤ q ∧ H (t + 1) < a
    · rw [hA t hAt.1 hAt.2.1 hAt.2.2, hA _ hAt'.1 hAt'.2.1 hAt'.2.2]
      exact hHl t hAt.1 hAt'.2.1
    · have hq' : t + 1 ≤ q := by
        by_contra hc
        have e1 : t = q := by omega
        subst e1
        have := hmin t (Or.inr rfl) (hright (by omega)); omega
      have := hHl t hAt.1 hq'
      rw [hA t hAt.1 hAt.2.1 hAt.2.2, hD _ hAt',
        (hg0 _ (by omega)).mpr (hHe _ (by omega) hq' (by omega))]; omega
    · have hp' : p ≤ t := by
        by_contra hc
        have e1 : t + 1 = p := by omega
        have := hmin p (Or.inl rfl) (hleft (by omega)); rw [← e1] at this; omega
      have := hHl t hp' hAt'.2.1
      rw [hD t hAt, hA _ hAt'.1 hAt'.2.1 hAt'.2.2,
        (hg0 t (by omega)).mpr (hHe t hp' (by omega) (by omega))]; omega
    · rw [hD t hAt, hD _ hAt']
      have hadj := h.adj t (by omega)
      have := genG_lip (ρ := ρ) (σ := σ) (t := t) (t' := t + 1) hK (h.le t (by omega))
        (h.le (t + 1) (by omega)) (h.wid t (by omega)) hadj.1 hadj.2
      have := genG_lip (ρ := ρ) (σ := σ) (t := t + 1) (t' := t) hK (h.le (t + 1) (by omega))
        (h.le t (by omega)) (h.wid (t + 1) (by omega)) hadj.2 hadj.1
      omega
  · by_cases hv : v < a
    · obtain ⟨j, hj⟩ := hHc.2 v
      refine ⟨j, fun t _ ht hFt => ?_⟩
      by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
      · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; exact hj t hAt.1 hAt.2.1 hFt
      · rw [hD t hAt] at hFt; omega
    · refine ⟨genWin K (v - a), fun t _ ht hFt => ?_⟩
      by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
      · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; omega
      · rw [hD t hAt] at hFt
        rw [show v - a = genG K ρ σ t by omega]
        exact genWin_spec hK (h.le t (by omega)) (h.lt t (by omega))
  · -- the end clause
    have hnA : ¬ (p ≤ e' ∧ e' ≤ q ∧ H e' < a) := by
      rintro ⟨h1, h2, h3⟩
      have : e' = p ∨ e' = q := by omega
      have := hmin e' this hT'; omega
    rcases hT' with hT' | hT'
    · left
      have := h.poss e' he' 0 hT'; have := h.le e' he'
      intro t ht hFt
      rw [hD e' hnA, (hg0 e' he').mpr (by omega)] at hFt
      by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
      · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; omega
      · rw [hD t hAt] at hFt; exact (hg0 t ht).mp (by omega)
    · right
      have := h.poss e' he' _ hT'; have := h.le e' he'
      have hge : genG K ρ σ e' = K - 3 := by unfold genG; split_ifs <;> omega
      intro t ht hFt
      rw [hD e' hnA, hge] at hFt
      by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
      · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; omega
      · rw [hD t hAt] at hFt; exact hgK t ht (by omega)

theorem PCons.flip {K : ℕ} {ρ σ : ℕ → ℕ} {p q : ℕ} {H : ℕ → ℕ} (hH : PCons p q ρ σ H)
    (hb : ∀ t, p ≤ t → t ≤ q → ρ t ≤ σ t ∧ σ t < K) :
    PCons p q (fun t => K - 1 - σ t) (fun t => K - 1 - ρ t) H := by
  refine ⟨hH.1, fun v => ?_⟩
  obtain ⟨j, hj⟩ := hH.2 v
  refine ⟨K - 2 - j, fun t h1 h2 h3 => ?_⟩
  have := hj t h1 h2 h3; have := hb t h1 h2
  show K - 2 - j ≤ K - 1 - ρ t ∧ K - 1 - σ t ≤ K - 2 - j + 1
  omega

/-- Existence of the left end of the maximal subchain. -/
theorem exists_left_end (P : ℕ → Prop) : ∀ i : ℕ,
    ∃ hh, hh ≤ i ∧ (0 < hh → P hh) ∧ ∀ t, hh < t → t < i → ¬ P t
  | 0 => ⟨0, le_rfl, fun h => absurd h (lt_irrefl 0), fun t h1 h2 => absurd h2 (by omega)⟩
  | i + 1 => by
      by_cases hP : P i
      · exact ⟨i, by omega, fun _ => hP, fun t h1 h2 => absurd h2 (by omega)⟩
      · obtain ⟨hh, h1, h2, h3⟩ := exists_left_end P i
        refine ⟨hh, by omega, h2, fun t ht1 ht2 => ?_⟩
        rcases Nat.lt_or_ge t i with h | h
        · exact h3 t ht1 h
        · rwa [show t = i by omega]

/-- Existence of the right end of the maximal subchain. -/
theorem exists_right_end (P : ℕ → Prop) {i n : ℕ} (hi : i < n) :
    ∃ k, i ≤ k ∧ k < n ∧ (k + 1 < n → P k) ∧ ∀ t, i < t → t < k → ¬ P t := by
  classical
  by_cases hex : ∃ t, i < t ∧ t + 1 < n ∧ P t
  · refine ⟨Nat.find hex, (Nat.find_spec hex).1.le, by have := (Nat.find_spec hex).2.1; omega,
      fun _ => (Nat.find_spec hex).2.2, fun t h1 h2 hP => ?_⟩
    have := (Nat.find_spec hex).2.1
    exact Nat.find_min hex h2 ⟨h1, by omega, hP⟩
  · push_neg at hex
    refine ⟨n - 1, by omega, by omega, fun h => absurd h (by omega), fun t h1 h2 hP => ?_⟩
    exact hex t h1 (by omega) hP

/-- **The general case** (`d_i` in neither end group, `r ≥ 5`), given the theorem for fewer coarse
links. -/
theorem general_case {K : ℕ} (IH : ∀ K', K' < K → BingMain K') {n : ℕ} {ρ σ : ℕ → ℕ}
    {T : ℕ → ℕ → Prop} {i : ℕ} (h : BHyp n K ρ σ T) (hi : i < n) (hK : 5 ≤ K)
    (hρi : 2 ≤ ρ i) (hσi : σ i + 3 ≤ K) : BConcl n K ρ σ T i := by
  classical
  set ext : ℕ → Prop := fun t => T t 0 ∨ T t (K - 1) with hext
  have hiext : ¬ ext i := by
    rintro (hT | hT)
    · have := h.poss i hi 0 hT; have := h.le i hi; omega
    · have := h.poss i hi (K - 1) hT; have := h.le i hi; omega
  obtain ⟨hh, hh1, hh2, hh3⟩ := exists_left_end ext i
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_right_end ext hi
  have hint : ∀ t, hh < t → t < k → ¬ T t 0 ∧ ¬ T t (K - 1) := by
    intro t h1 h2
    have : ¬ ext t := by
      rcases Nat.lt_trichotomy t i with e | e | e
      · exact hh3 t h1 e
      · rw [e]; exact hiext
      · exact hk4 t e h2
    exact ⟨fun h' => this (Or.inl h'), fun h' => this (Or.inr h')⟩
  -- `H`: a consolidation of `D(h, k)` with the end clause at both of its ends
  obtain ⟨H, hH0, hHc, hHe0, hHe1⟩ : ∃ H : ℕ → ℕ, H i = 0 ∧ PCons hh k ρ σ H ∧
      (∀ e, (e = hh ∨ e = k) → T e 0 → ∀ t, hh ≤ t → t ≤ k → H t = H e → ρ t ≤ 1) ∧
      (∀ e, (e = hh ∨ e = k) → T e (K - 1) → ∀ t, hh ≤ t → t ≤ k → H t = H e →
        K - 2 ≤ σ t) := by
    by_cases hlow : ∀ t, hh ≤ t → t ≤ k → ¬ T t 0
    · have hin : ∀ t, hh ≤ t → t ≤ k → 1 ≤ ρ t ∧ σ t ≤ K - 1 := by
        intro t h1 h2
        refine ⟨?_, by have := h.lt t (by omega); omega⟩
        by_contra hc
        exact hlow t h1 h2 (h.cont t (by omega) 0 (by omega) (by omega))
      have hsub := h.sub (p := hh) (q := k) (lo := 1) (hi := K - 1) (by omega) hk2 hin
      have hc := IH (K - 1 - 1 + 1) (by omega) _ _ _ _ (i - hh) hsub (by omega)
      obtain ⟨H, hH0, hHc, hHe⟩ :=
        BConcl.sub_abs (by omega) hin (fun t _ ht => h.le t (by omega)) hc
      refine ⟨H, hH0, hHc, fun e he hT => absurd hT (hlow e (by omega) (by omega)), ?_⟩
      intro e he hT
      have := h.poss e (by omega) _ hT
      rcases hHe e he (Or.inr hT) with hb | hb
      · have := hb e (by omega) (by omega) rfl; omega
      · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
    · by_cases hhigh : ∀ t, hh ≤ t → t ≤ k → ¬ T t (K - 1)
      · have hin : ∀ t, hh ≤ t → t ≤ k → 0 ≤ ρ t ∧ σ t ≤ K - 2 := by
          intro t h1 h2
          refine ⟨Nat.zero_le _, ?_⟩
          by_contra hc
          have := h.lt t (by omega); have := h.le t (by omega)
          exact hhigh t h1 h2 (h.cont t (by omega) _ (by omega) (by omega))
        have hsub := h.sub (p := hh) (q := k) (lo := 0) (hi := K - 2) (by omega) hk2 hin
        have hc := IH (K - 2 - 0 + 1) (by omega) _ _ _ _ (i - hh) hsub (by omega)
        obtain ⟨H, hH0, hHc, hHe⟩ :=
          BConcl.sub_abs (by omega) hin (fun t _ ht => h.le t (by omega)) hc
        refine ⟨H, hH0, hHc, ?_, fun e he hT => absurd hT (hhigh e (by omega) (by omega))⟩
        intro e he hT
        have := h.poss e (by omega) _ hT
        rcases hHe e he (Or.inl hT) with hb | hb
        · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
        · have := hb e (by omega) (by omega) rfl; omega
      · -- both extremes are met, necessarily at the two ends: the special case
        push_neg at hlow hhigh
        obtain ⟨t0, ht0, ht0', hT0⟩ := hlow
        obtain ⟨t1, ht1, ht1', hT1⟩ := hhigh
        have hne : ∀ t, t < n → T t 0 → T t (K - 1) → False := by
          intro t ht a b
          have := h.poss t ht 0 a; have := h.poss t ht _ b; have := h.le t ht; omega
        have e0 : t0 = hh ∨ t0 = k := by
          by_contra hc
          exact (hint t0 (by omega) (by omega)).1 hT0
        have e1 : t1 = hh ∨ t1 = k := by
          by_contra hc
          exact (hint t1 (by omega) (by omega)).2 hT1
        have hin : ∀ t, hh ≤ t → t ≤ k → 0 ≤ ρ t ∧ σ t ≤ K - 1 :=
          fun t _ ht => ⟨Nat.zero_le _, by have := h.lt t (by omega); omega⟩
        have hsub := h.sub (p := hh) (q := k) (lo := 0) (hi := K - 1) (by omega) hk2 hin
        have hKK : K - 1 - 0 + 1 = K := by omega
        have hc : BConcl (k - hh + 1) (K - 1 - 0 + 1) (fun t => ρ (t + hh) - 0)
            (fun t => σ (t + hh) - 0) (fun t j => j + 0 ≤ K - 1 ∧ T (t + hh) (j + 0))
            (i - hh) := by
          have hIH : ∀ K', K' < K - 1 - 0 + 1 → BingMain K' := fun K' hK' => IH K' (by omega)
          have hint' : ∀ t, 0 < t → t + 1 < k - hh + 1 →
              ¬ (0 + 0 ≤ K - 1 ∧ T (t + hh) (0 + 0)) ∧
              ¬ (K - 1 - 0 + 1 - 1 + 0 ≤ K - 1 ∧ T (t + hh) (K - 1 - 0 + 1 - 1 + 0)) := by
            intro t h1 h2
            have := hint (t + hh) (by omega) (by omega)
            rw [show K - 1 - 0 + 1 - 1 + 0 = K - 1 by omega]
            exact ⟨fun h' => this.1 h'.2, fun h' => this.2 h'.2⟩
          rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1
          · subst e0; exact absurd hT1 (fun h' => hne _ (by omega) hT0 (e1 ▸ h'))
          · -- `d_h` meets `e₁`, `d_k` meets `e_r`
            subst e0; subst e1
            refine special_case hIH hsub ⟨by omega, by omega, ?_, ?_, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩,
              hint'⟩
            · simp only [show i - t0 + t0 = i by omega]; omega
            · simp only [show i - t0 + t0 = i by omega]; omega
            · simpa using hT0
            · rw [show t1 - t0 + 1 - 1 + t0 = t1 by omega, show K - 1 - 0 + 1 - 1 + 0 = K - 1 by omega]
              exact hT1
          · -- `d_h` meets `e_r`, `d_k` meets `e₁`: mirror
            subst e0; subst e1
            have hsubF := hsub.flip
            refine BConcl.of_flip hsub (by omega) (special_case hIH hsubF
              ⟨by omega, by omega, ?_, ?_, ⟨by omega, ⟨by omega, ?_⟩⟩, ⟨le_rfl, ⟨by omega, ?_⟩⟩,
                fun t h1 h2 => ⟨fun h' => ?_, fun h' => ?_⟩⟩)
            · simp only [show i - t1 + t1 = i by omega]; omega
            · simp only [show i - t1 + t1 = i by omega]; omega
            · rw [show K - 1 - 0 + 1 - 1 - 0 + 0 = K - 1 by omega, show 0 + t1 = t1 by omega]
              exact hT1
            · rw [show K - 1 - 0 + 1 - 1 - (K - 1 - 0 + 1 - 1) + 0 = 0 by omega,
                show t0 - t1 + 1 - 1 + t1 = t0 by omega]
              exact hT0
            · obtain ⟨_, _, h'⟩ := h'
              rw [show K - 1 - 0 + 1 - 1 - 0 + 0 = K - 1 by omega] at h'
              exact (hint (t + t1) (by omega) (by omega)).2 h'
            · obtain ⟨_, _, h'⟩ := h'
              rw [show K - 1 - 0 + 1 - 1 - (K - 1 - 0 + 1 - 1) + 0 = 0 by omega] at h'
              exact (hint (t + t1) (by omega) (by omega)).1 h'
          · subst e0; exact absurd hT1 (fun h' => hne _ (by omega) hT0 (e1 ▸ h'))
        obtain ⟨H, hH0, hHc, hHe⟩ :=
          BConcl.sub_abs (by omega) hin (fun t _ ht => h.le t (by omega)) hc
        refine ⟨H, hH0, hHc, fun e he hT => ?_, fun e he hT => ?_⟩
        · have := h.poss e (by omega) 0 hT
          rcases hHe e he (Or.inl hT) with hb | hb
          · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
          · have := hb e (by omega) (by omega) rfl; omega
        · have := h.poss e (by omega) _ hT
          rcases hHe e he (Or.inr hT) with hb | hb
          · have := hb e (by omega) (by omega) rfl; omega
          · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
  -- the construction
  by_cases hnone : ¬ ext hh ∧ ¬ ext k
  · -- `D(h, k) = D`: `H` itself
    have hh0 : hh = 0 := by
      by_contra hc; exact hnone.1 (hh2 (by omega))
    have hkn : k = n - 1 := by
      by_contra hc; exact hnone.2 (hk3 (by omega))
    subst hh0; subst hkn
    refine ⟨H, hH0, hHc, fun e he hee hT => ?_⟩
    have he' : e = 0 ∨ e = n - 1 := hee
    rcases hT with hT | hT
    · exact Or.inl (fun t ht hte => hHe0 e he' hT t (Nat.zero_le _) (by omega) hte)
    · exact Or.inr (fun t ht hte => hHe1 e he' hT t (Nat.zero_le _) (by omega) hte)
  · -- the first block of `H` meeting `e₁ + e_r`
    obtain ⟨e, he, hext_e, hmin⟩ : ∃ e, (e = hh ∨ e = k) ∧ ext e ∧
        ∀ e', (e' = hh ∨ e' = k) → ext e' → H e ≤ H e' := by
      by_cases ha : ext hh <;> by_cases hb : ext k
      · by_cases hab : H hh ≤ H k
        · exact ⟨hh, Or.inl rfl, ha, fun e' he' _ => by rcases he' with rfl | rfl <;> omega⟩
        · exact ⟨k, Or.inr rfl, hb, fun e' he' _ => by rcases he' with rfl | rfl <;> omega⟩
      · exact ⟨hh, Or.inl rfl, ha, fun e' he' he'x => by
          rcases he' with rfl | rfl
          · exact le_rfl
          · exact absurd he'x hb⟩
      · exact ⟨k, Or.inr rfl, hb, fun e' he' he'x => by
          rcases he' with rfl | rfl
          · exact absurd he'x ha
          · exact le_rfl⟩
      · exact absurd ⟨ha, hb⟩ hnone
    rcases hext_e with hTe | hTe
    · exact genF_concl h hK (by omega) hk2 hh1 hk1 hh2 hk3 H hH0 hHc he rfl
        (hHe0 e he hTe) hmin
    · -- mirror
      refine BConcl.of_flip h hi (genF_concl h.flip hK (by omega) hk2 hh1 hk1 (fun hp => ?_)
        (fun hq => ?_) H hH0 (hHc.flip (fun t _ ht => ⟨h.le t (by omega), h.lt t (by omega)⟩))
        he rfl
        (fun t h1 h2 h3 => ?_) (fun e' he' hT' => hmin e' he' ?_))
      · rcases hh2 hp with hT | hT
        · exact Or.inr ⟨le_rfl, by rwa [show K - 1 - (K - 1) = 0 by omega]⟩
        · exact Or.inl ⟨by omega, by rwa [show K - 1 - 0 = K - 1 by omega]⟩
      · rcases hk3 hq with hT | hT
        · exact Or.inr ⟨le_rfl, by rwa [show K - 1 - (K - 1) = 0 by omega]⟩
        · exact Or.inl ⟨by omega, by rwa [show K - 1 - 0 = K - 1 by omega]⟩
      · have := hHe1 e he hTe t h1 h2 h3; omega
      · rcases hT' with ⟨_, hT'⟩ | ⟨_, hT'⟩
        · exact Or.inr (by rwa [show K - 1 - 0 = K - 1 by omega] at hT')
        · exact Or.inl (by rwa [show K - 1 - (K - 1) = 0 by omega] at hT')

/-- **Bing 1948, Theorem 3, in the model** (block reading, every block in two adjacent coarse
links, Bing's \"or\" end clause read with the meeting table). Proved by Bing's induction on the
number of coarse links, with the seams of his special case closed. -/
theorem bing_main : ∀ K, BingMain K := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K IH =>
    intro n ρ σ T i h hi
    by_cases hK : K ≤ 4
    · exact bconcl_base h hi hK
    · by_cases hlo : ρ i ≤ 1
      · exact bconcl_low h hi (by omega) hlo
      · by_cases hhi : K ≤ σ i + 2
        · exact bconcl_high h hi (by omega) hhi
        · exact general_case IH h hi (by omega) (by omega) (by omega)

end HPC.Fold.Recon122
