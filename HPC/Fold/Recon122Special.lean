import HPC.Fold.Recon122Model

/-!
# Batch 122: the special case of Bing's induction, with the seams closed

The special case: only the end links of the fine chain meet the extreme coarse links, the first
meets `e₁` and the last `e_r`. Bing's construction, cut at a block `a` of `H` lying in the top
group, with the level groups read as `Cbot` (`cbotG`): `cutF_concl`. It covers Bing's branch
`d_i ∈ D(1, h)` (`H` on `D(1, h)` inside `E(1, r − 1)`) and the branch `d_i ∈ D(h, k)` (`H` on
`D(h, k)` inside `E(2, r − 1)`); the branch `d_i ∈ D(k, n)` is the mirror image. At `r = 5` the
construction is an explicit grouping (`special_five`).
-/

namespace HPC.Fold.Recon122

/-- The `Cbot` level groups of the special case (`0` = bottom group \"in `e₁ + e₂`\", `K − 4` = top
group \"in `e_{r−2} + e_{r−1}`\", the others by the least level). -/
def cbotG (K : ℕ) (ρ σ : ℕ → ℕ) (t : ℕ) : ℕ :=
  if ρ t ≤ 1 then 0 else if K - 3 ≤ σ t then K - 4 else ρ t - 1

theorem cbotG_le (K : ℕ) (ρ σ : ℕ → ℕ) (t : ℕ) (hK : 5 ≤ K) (hle : ρ t ≤ σ t) :
    cbotG K ρ σ t ≤ K - 4 := by
  unfold cbotG; split_ifs <;> omega

theorem cbotG_lip {K : ℕ} {ρ σ : ℕ → ℕ} {t t' : ℕ} (hK : 5 ≤ K) (h1 : ρ t ≤ σ t)
    (hw : σ t ≤ ρ t + 1) (ha : σ t ≤ ρ t' + 1) (hs : σ t + 2 ≤ K) :
    cbotG K ρ σ t ≤ cbotG K ρ σ t' + 1 := by
  unfold cbotG; split_ifs <;> omega

/-- The window of a `Cbot` group. -/
def cbotWin (K g : ℕ) : ℕ := if g = 0 then 0 else if g = K - 4 then K - 3 else g + 1

theorem cbotWin_spec {K : ℕ} {ρ σ : ℕ → ℕ} {t : ℕ} (hK : 5 ≤ K) (h1 : ρ t ≤ σ t)
    (hs : σ t + 2 ≤ K) : cbotWin K (cbotG K ρ σ t) ≤ σ t ∧ ρ t ≤ cbotWin K (cbotG K ρ σ t) + 1 := by
  unfold cbotWin cbotG; split_ifs <;> omega

/-- **Bing's special-case construction, cut at a top block** (reading `Cbot`). `H` is a
consolidation of the fine links `p … q` with `d_i` at time `0`; the links of `H` at time `a` lie in
the top group; `F` keeps the blocks of `H` before `a`, then the level groups of the remaining links
up to `d_k` from the top down, then the links after `d_k` one by one. -/
def cutF (K : ℕ) (ρ σ : ℕ → ℕ) (p q k a : ℕ) (H : ℕ → ℕ) (t : ℕ) : ℕ :=
  if p ≤ t ∧ t ≤ q ∧ H t < a then H t
  else if t ≤ k then a + (K - 4) - cbotG K ρ σ t
  else a + (K - 4) + (t - k)

/-- **The closed special-case construction works**: under the stated conditions on `H` (a
consolidation of `p … q` with `d_i` at time `0`, the links of time `a` in the top group, the block of
`d₀` in the bottom group when `p = 0`), `cutF` satisfies Bing's conclusion. -/
theorem cutF_spec {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i : ℕ} (h : BHyp n K ρ σ T)
    (hK : 5 ≤ K) (hin : ∀ t, t < n → 1 ≤ ρ t ∧ σ t + 2 ≤ K) (hρ0 : ρ 0 ≤ 1)
    (hn1 : K ≤ ρ (n - 1) + 2) {p q k a : ℕ} (H : ℕ → ℕ) (hpq : p ≤ q) (hqk : q ≤ k)
    (hk : k + 1 < n) (hρk : ρ k ≤ 1) (hpi : p ≤ i) (hiq : i ≤ q) (hHi : H i = 0)
    (hHc : PCons p q ρ σ H)
    (htop : ∀ t, p ≤ t → t ≤ q → H t = a → 2 ≤ ρ t ∧ K ≤ σ t + 3)
    (hp : 0 < p → a ≤ H p) (hq : a ≤ H q)
    (h0 : p = 0 → H 0 < a → ∀ t, p ≤ t → t ≤ q → H t = H 0 → ρ t ≤ 1) :
    cutF K ρ σ p q k a H i = 0 ∧ PCons 0 (n - 1) ρ σ (cutF K ρ σ p q k a H) ∧
      EndC n K ρ σ T (cutF K ρ σ p q k a H) := by
  have hg : ∀ t, t < n → cbotG K ρ σ t ≤ K - 4 := fun t ht =>
    cbotG_le K ρ σ t hK (h.le t ht)
  have htopg : ∀ t, p ≤ t → t ≤ q → H t = a → cbotG K ρ σ t = K - 4 := by
    intro t h1 h2 h3; have := htop t h1 h2 h3; unfold cbotG; split_ifs <;> omega
  have hg0 : ∀ t, t < n → (cbotG K ρ σ t = 0 ↔ ρ t ≤ 1) := by
    intro t ht; have := hin t ht; unfold cbotG; split_ifs <;> omega
  -- the three regimes of the values of `F`
  have hA : ∀ t, p ≤ t → t ≤ q → H t < a → cutF K ρ σ p q k a H t = H t := by
    intro t h1 h2 h3; simp [cutF, h1, h2, h3]
  have hD : ∀ t, ¬ (p ≤ t ∧ t ≤ q ∧ H t < a) → t ≤ k →
      cutF K ρ σ p q k a H t = a + (K - 4) - cbotG K ρ σ t := by
    intro t h1 h2; simp only [cutF, if_neg h1, if_pos h2]
  have hT : ∀ t, k < t → cutF K ρ σ p q k a H t = a + (K - 4) + (t - k) := by
    intro t h1
    have : ¬ (p ≤ t ∧ t ≤ q ∧ H t < a) := by omega
    simp only [cutF, if_neg this, if_neg (show ¬ t ≤ k by omega)]
  refine ⟨?_, ⟨fun t _ ht => ?_, fun v => ?_⟩, fun e he hee _ => ?_⟩
  · -- `d_i` is in the first link
    by_cases hia : H i < a
    · rw [hA i hpi hiq hia, hHi]
    · rw [hD i (by omega) (by omega), htopg i hpi hiq (by omega)]; omega
  · -- adjacent links get adjacent times
    have hHl := hHc.1
    by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a <;> by_cases hAt' : p ≤ t + 1 ∧ t + 1 ≤ q ∧ H (t + 1) < a
    · rw [hA t hAt.1 hAt.2.1 hAt.2.2, hA _ hAt'.1 hAt'.2.1 hAt'.2.2]
      exact hHl t hAt.1 hAt'.2.1
    · have hq' : t + 1 ≤ q := by
        by_contra hc
        have : t = q := by omega
        subst this; omega
      have := hHl t hAt.1 hq'
      have e1 : H (t + 1) = a := by omega
      rw [hA t hAt.1 hAt.2.1 hAt.2.2, hD _ hAt' (by omega), htopg _ (by omega) hq' e1]; omega
    · have hp' : p ≤ t := by
        by_contra hc
        have : t + 1 = p := by omega
        have := hp (by omega); rw [← ‹t + 1 = p›] at this; omega
      have hq' : t ≤ q := by omega
      have := hHl t hp' hAt'.2.1
      have e1 : H t = a := by omega
      rw [hD t hAt (by omega), hA _ hAt'.1 hAt'.2.1 hAt'.2.2, htopg t hp' hq' e1]; omega
    · by_cases htk : t + 1 ≤ k
      · rw [hD t hAt (by omega), hD _ hAt' htk]
        have hadj := h.adj t (by omega)
        have l1 := cbotG_lip (ρ := ρ) (σ := σ) (t := t) (t' := t + 1) hK (h.le t (by omega))
          (h.wid t (by omega)) hadj.1 (hin t (by omega)).2
        have l2 := cbotG_lip (ρ := ρ) (σ := σ) (t := t + 1) (t' := t) hK (h.le (t + 1) (by omega))
          (h.wid (t + 1) (by omega)) hadj.2 (hin (t + 1) (by omega)).2
        have := hg t (by omega); have := hg (t + 1) (by omega)
        omega
      · by_cases htk' : t = k
        · subst htk'
          rw [hD t hAt le_rfl, hT (t + 1) (by omega), (hg0 t (by omega)).mpr hρk]; omega
        · rw [hT t (by omega), hT (t + 1) (by omega)]; omega
  · -- each fibre lies in two adjacent coarse links
    by_cases hv : v < a
    · obtain ⟨j, hj⟩ := hHc.2 v
      refine ⟨j, fun t _ ht hFt => ?_⟩
      by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
      · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; exact hj t hAt.1 hAt.2.1 hFt
      · by_cases htk : t ≤ k
        · rw [hD t hAt htk] at hFt; have := hg t (by omega); omega
        · rw [hT t (by omega)] at hFt; omega
    · by_cases hv' : v ≤ a + (K - 4)
      · refine ⟨cbotWin K (a + (K - 4) - v), fun t _ ht hFt => ?_⟩
        by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
        · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; omega
        · by_cases htk : t ≤ k
          · rw [hD t hAt htk] at hFt
            have := hg t (by omega)
            have e : a + (K - 4) - v = cbotG K ρ σ t := by omega
            rw [e]; exact cbotWin_spec hK (h.le t (by omega)) (hin t (by omega)).2
          · rw [hT t (by omega)] at hFt; omega
      · refine ⟨ρ (v - a - (K - 4) + k), fun t _ ht hFt => ?_⟩
        by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
        · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; omega
        · by_cases htk : t ≤ k
          · rw [hD t hAt htk] at hFt; omega
          · rw [hT t (by omega)] at hFt
            rw [show v - a - (K - 4) + k = t by omega]
            exact ⟨h.le t (by omega), by omega⟩
  · -- the end clause
    rcases hee with rfl | rfl
    · left
      intro t ht hFt
      by_cases hA0 : p ≤ 0 ∧ 0 ≤ q ∧ H 0 < a
      · have hp0 : p = 0 := by omega
        rw [hA 0 hA0.1 hA0.2.1 hA0.2.2] at hFt
        by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
        · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt
          exact h0 hp0 hA0.2.2 t hAt.1 hAt.2.1 hFt
        · by_cases htk : t ≤ k
          · rw [hD t hAt htk] at hFt; have := hg t ht; omega
          · rw [hT t (by omega)] at hFt; omega
      · rw [hD 0 hA0 (by omega), (hg0 0 he).mpr hρ0] at hFt
        by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
        · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; omega
        · by_cases htk : t ≤ k
          · rw [hD t hAt htk] at hFt; have := hg t ht
            exact (hg0 t ht).mp (by omega)
          · rw [hT t (by omega)] at hFt; omega
    · right
      intro t ht hFt
      rw [hT (n - 1) (by omega)] at hFt
      by_cases hAt : p ≤ t ∧ t ≤ q ∧ H t < a
      · rw [hA t hAt.1 hAt.2.1 hAt.2.2] at hFt; omega
      · by_cases htk : t ≤ k
        · rw [hD t hAt htk] at hFt; omega
        · rw [hT t (by omega)] at hFt
          have : t = n - 1 := by omega
          subst this; have := h.le (n - 1) ht; omega

/-- `cutF_spec`, packaged as `BConcl`. -/
theorem cutF_concl {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i : ℕ} (h : BHyp n K ρ σ T)
    (hK : 5 ≤ K) (hin : ∀ t, t < n → 1 ≤ ρ t ∧ σ t + 2 ≤ K) (hρ0 : ρ 0 ≤ 1)
    (hn1 : K ≤ ρ (n - 1) + 2) {p q k a : ℕ} (H : ℕ → ℕ) (hpq : p ≤ q) (hqk : q ≤ k)
    (hk : k + 1 < n) (hρk : ρ k ≤ 1) (hpi : p ≤ i) (hiq : i ≤ q) (hHi : H i = 0)
    (hHc : PCons p q ρ σ H)
    (htop : ∀ t, p ≤ t → t ≤ q → H t = a → 2 ≤ ρ t ∧ K ≤ σ t + 3)
    (hp : 0 < p → a ≤ H p) (hq : a ≤ H q)
    (h0 : p = 0 → H 0 < a → ∀ t, p ≤ t → t ≤ q → H t = H 0 → ρ t ≤ 1) :
    BConcl n K ρ σ T i :=
  ⟨_, cutF_spec h hK hin hρ0 hn1 H hpq hqk hk hρk hpi hiq hHi hHc htop hp hq h0⟩

/-! ## Mirror-and-reverse -/

theorem BHyp.revflip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) :
    BHyp n K (fun t => K - 1 - σ (n - 1 - t)) (fun t => K - 1 - ρ (n - 1 - t))
      (fun t j => j ≤ K - 1 ∧ T (n - 1 - t) (K - 1 - j)) :=
  h.rev.flip

theorem BConcl.of_revflip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T)
    {i : ℕ} (hi : i < n)
    (hc : BConcl n K (fun t => K - 1 - σ (n - 1 - t)) (fun t => K - 1 - ρ (n - 1 - t))
      (fun t j => j ≤ K - 1 ∧ T (n - 1 - t) (K - 1 - j)) (n - 1 - i)) :
    BConcl n K ρ σ T i :=
  BConcl.of_rev hi (BConcl.of_flip h.rev (by omega) hc)

theorem PCons.revflip {n K : ℕ} {ρ σ : ℕ → ℕ} {p q : ℕ} {H : ℕ → ℕ} (hH : PCons p q ρ σ H)
    (hpq : p ≤ q) (hq : q < n) (hb : ∀ t, p ≤ t → t ≤ q → ρ t ≤ σ t ∧ σ t < K) :
    PCons (n - 1 - q) (n - 1 - p) (fun t => K - 1 - σ (n - 1 - t)) (fun t => K - 1 - ρ (n - 1 - t))
      (fun t => H (n - 1 - t)) := by
  refine ⟨fun t h1 h2 => ?_, fun v => ?_⟩
  · have := hH.1 (n - 1 - (t + 1)) (by omega) (by omega)
    rw [show n - 1 - (t + 1) + 1 = n - 1 - t by omega] at this
    exact ⟨this.2, this.1⟩
  · obtain ⟨j, hj⟩ := hH.2 v
    refine ⟨K - 2 - j, fun t h1 h2 h3 => ?_⟩
    have := hj (n - 1 - t) (by omega) (by omega) h3
    have := hb (n - 1 - t) (by omega) (by omega)
    simp only; omega

/-! ## The special case -/

/-- The universal statement at `K` coarse links. -/
def BingMain (K : ℕ) : Prop :=
  ∀ (n : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (i : ℕ), BHyp n K ρ σ T → i < n →
    BConcl n K ρ σ T i

/-- The hypotheses of the special case, with `d_i` in neither end group. -/
structure SpecialHyp (n K : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (i : ℕ) : Prop where
  hi : i < n
  hK : 5 ≤ K
  hρi : 2 ≤ ρ i
  hσi : σ i + 3 ≤ K
  h0 : T 0 0
  hl : T (n - 1) (K - 1)
  hint : ∀ t, 0 < t → t + 1 < n → ¬ T t 0 ∧ ¬ T t (K - 1)

theorem SpecialHyp.facts {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i : ℕ}
    (h : BHyp n K ρ σ T) (hs : SpecialHyp n K ρ σ T i) :
    0 < i ∧ i + 1 < n ∧ (∀ t, t < n → 1 ≤ ρ t ∧ σ t + 2 ≤ K) ∧ σ 0 ≤ 1 ∧
      K ≤ ρ (n - 1) + 2 := by
  obtain ⟨hi, hK, hρi, hσi, h0, hl, hint⟩ := hs
  have hn : 0 < n := by omega
  have hσ0 := (h.poss 0 hn 0 h0).1
  have hρl := (h.poss (n - 1) (by omega) _ hl).2
  have hii := h.le i hi
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with e | e
    · subst e; omega
    · exact e
  have hin : i + 1 < n := by
    by_contra hc
    have : i = n - 1 := by omega
    subst this; omega
  refine ⟨hi0, hin, fun t ht => ⟨?_, ?_⟩, hσ0, by omega⟩
  · by_contra hc
    have hT0 : T t 0 := h.cont t ht 0 (by omega) (by omega)
    rcases Nat.eq_zero_or_pos t with e | e
    · subst e
      have := h.bwd 0 (by omega) 0 (by omega) (by omega)
      exact (hint 1 (by omega) (by omega)).1 this
    · by_cases htl : t + 1 < n
      · exact (hint t e htl).1 hT0
      · have : t = n - 1 := by omega
        subst this; have := h.le (n - 1) ht; omega
  · by_contra hc
    have hlt := h.lt t ht
    have hT : T t (K - 1) := h.cont t ht _ (by have := h.le t ht; omega) (by omega)
    by_cases htl : t + 1 < n
    · rcases Nat.eq_zero_or_pos t with e | e
      · subst e; omega
      · exact (hint t e htl).2 hT
    · have e : t = n - 1 := by omega
      subst e
      have := h.fwd (n - 1 - 1) (by omega) (K - 1)
        (by rw [show n - 1 - 1 + 1 = n - 1 by omega]; have := h.le (n - 1) ht; omega)
        (by rw [show n - 1 - 1 + 1 = n - 1 by omega]; omega)
      exact (hint (n - 1 - 1) (by omega) (by omega)).2 this

/-- **The special case at `r = 5`**, by an explicit grouping: the links up to `d_k` in `e₁ + e₂`,
the other links up to `d_k` (first), then the links after `d_k` one by one. -/
theorem special_five {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i : ℕ} (h : BHyp n K ρ σ T)
    (hs : SpecialHyp n K ρ σ T i) (hK : K = 5) {k : ℕ} (hik : i < k) (hk : k < n)
    (hρk : ρ k ≤ 1) : BConcl n K ρ σ T i := by
  obtain ⟨hi0, hin, hlev, hσ0, hρl⟩ := hs.facts h
  have hkn : k + 1 < n := by
    by_contra hc
    have : k = n - 1 := by omega
    subst this; omega
  have hρi := hs.hρi
  refine ⟨fun t => if t ≤ k then (if ρ t ≤ 1 then 1 else 0) else t - k + 1, ?_,
    ⟨fun t _ ht => ?_, fun v => ?_⟩, fun e he hee _ => ?_⟩
  · simp [show i ≤ k by omega, show ¬ ρ i ≤ 1 by omega]
  · simp only
    by_cases htk : t = k
    · subst htk; simp [hρk]
    · split_ifs <;> omega
  · refine ⟨if v = 0 then 2 else if v = 1 then 0 else ρ (v + k - 1), fun t _ ht hv => ?_⟩
    have := h.le t (by omega); have := hlev t (by omega)
    simp only at hv
    split_ifs at hv ⊢ <;> try omega
    all_goals (subst hv; rw [show t - k + 1 + k - 1 = t by omega]; omega)
  · rcases hee with rfl | rfl
    · left; intro t ht hte
      have := h.le 0 he
      simp only [show (0 : ℕ) ≤ k by omega, if_true, show ρ 0 ≤ 1 by omega] at hte
      split_ifs at hte <;> omega
    · right; intro t ht hte
      simp only [show ¬ n - 1 ≤ k by omega, if_false] at hte
      have := h.le t ht
      split_ifs at hte <;> try omega
      have : t = n - 1 := by omega
      subst this; omega

theorem SpecialHyp.revflip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i : ℕ}
    (hs : SpecialHyp n K ρ σ T i) :
    SpecialHyp n K (fun t => K - 1 - σ (n - 1 - t)) (fun t => K - 1 - ρ (n - 1 - t))
      (fun t j => j ≤ K - 1 ∧ T (n - 1 - t) (K - 1 - j)) (n - 1 - i) := by
  obtain ⟨hi, hK, hρi, hσi, h0, hl, hint⟩ := hs
  refine ⟨by omega, hK, ?_, ?_, ⟨by omega, ?_⟩, ⟨le_rfl, ?_⟩, fun t h1 h2 => ⟨?_, ?_⟩⟩
  · simp only [show n - 1 - (n - 1 - i) = i by omega]; omega
  · simp only [show n - 1 - (n - 1 - i) = i by omega]; omega
  · simpa [show K - 1 - 0 = K - 1 by omega] using hl
  · simpa [show K - 1 - (K - 1) = 0 by omega] using h0
  · rintro ⟨_, hT⟩
    exact (hint (n - 1 - t) (by omega) (by omega)).2 (by simpa using hT)
  · rintro ⟨_, hT⟩
    exact (hint (n - 1 - t) (by omega) (by omega)).1 (by simpa [show K - 1 - (K - 1) = 0 by omega] using hT)

/-- **Branch `d_i ∈ D(1, h)` of the special case**, `r ≥ 6`: `H` from the induction hypothesis
on `D(1, h)` inside `E(1, r − 1)`; every `H` works. -/
theorem special_branch1 {K : ℕ} (IH : ∀ K', K' < K → BingMain K') {n : ℕ} {ρ σ : ℕ → ℕ}
    {T : ℕ → ℕ → Prop} {i : ℕ} (h : BHyp n K ρ σ T) (hs : SpecialHyp n K ρ σ T i) (hK : 6 ≤ K)
    {hh k : ℕ} (hih : i < hh) (hhk : hh < k) (hk : k < n) (hht : ρ hh ≤ K - 2 ∧ K - 2 ≤ σ hh)
    (hkb : ρ k ≤ 1) : BConcl n K ρ σ T i := by
  obtain ⟨hi0, hin, hlev, hσ0, hρl⟩ := hs.facts h
  have hkn : k + 1 < n := by
    by_contra hc
    have : k = n - 1 := by omega
    subst this; omega
  have hin' : ∀ t, 0 ≤ t → t ≤ hh → 0 ≤ ρ t ∧ σ t ≤ K - 2 :=
    fun t _ ht => ⟨Nat.zero_le _, by have := hlev t (by omega); omega⟩
  have hsub := h.sub (p := 0) (q := hh) (lo := 0) (hi := K - 2) (by omega) (by omega) hin'
  have hc := IH (K - 2 - 0 + 1) (by omega) _ _ _ _ (i - 0) hsub (by omega)
  obtain ⟨H, hH0, hHc, hHe⟩ := BConcl.sub_abs (by omega) hin' (fun t _ ht => h.le t (by omega)) hc
  have hHh : ∀ t, 0 ≤ t → t ≤ hh → H t = H hh → 2 ≤ ρ t ∧ K ≤ σ t + 3 := by
    rcases hHe hh (Or.inr rfl) (Or.inr (h.cont hh (by omega) _ hht.1 hht.2)) with hb | hb
    · have := hb hh (by omega) le_rfl rfl; have := h.wid hh (by omega); omega
    · intro t h1 h2 h3; have := hb t h1 h2 h3; have := h.wid t (by omega); omega
  have hH0b : ∀ t, 0 ≤ t → t ≤ hh → H t = H 0 → ρ t ≤ 1 := by
    rcases hHe 0 (Or.inl rfl) (Or.inl hs.h0) with hb | hb
    · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
    · have := hb 0 le_rfl (by omega) rfl; omega
  exact cutF_concl h (by omega) hlev (by have := h.le 0 (by omega); omega) hρl H (Nat.zero_le _) hhk.le
    hkn hkb (Nat.zero_le _) hih.le hH0 hHc hHh (fun h' => absurd h' (lt_irrefl 0)) le_rfl
    (fun _ _ => hH0b)

/-- **Branch `d_i ∈ D(h, k)` of the special case**, `r ≥ 6`: `H` from the induction hypothesis on
`D(h, k)` inside `E(2, r − 1)`, cut at the earlier of the blocks of `d_h` and `d_k`. -/
theorem special_middle {K : ℕ} (IH : ∀ K', K' < K → BingMain K') {n : ℕ} {ρ σ : ℕ → ℕ}
    {T : ℕ → ℕ → Prop} {i : ℕ} (h : BHyp n K ρ σ T) (hs : SpecialHyp n K ρ σ T i) (hK : 6 ≤ K)
    {hh k : ℕ} (hhi : hh < i) (hik : i < k) (hk : k < n) (hht : ρ hh ≤ K - 2 ∧ K - 2 ≤ σ hh)
    (hkb : ρ k ≤ 1 ∧ 1 ≤ σ k) : BConcl n K ρ σ T i := by
  obtain ⟨hi0, hin, hlev, hσ0, hρl⟩ := hs.facts h
  have hkn : k + 1 < n := by
    by_contra hc
    have : k = n - 1 := by omega
    subst this; omega
  have hh0 : 0 < hh := by
    by_contra hc
    have : hh = 0 := by omega
    subst this; omega
  have hin' : ∀ t, hh ≤ t → t ≤ k → 1 ≤ ρ t ∧ σ t ≤ K - 2 :=
    fun t _ ht => ⟨(hlev t (by omega)).1, by have := (hlev t (by omega)).2; omega⟩
  have hsub := h.sub (p := hh) (q := k) (lo := 1) (hi := K - 2) (by omega) (by omega) hin'
  have hc := IH (K - 2 - 1 + 1) (by omega) _ _ _ _ (i - hh) hsub (by omega)
  obtain ⟨H, hH0, hHc, hHe⟩ := BConcl.sub_abs (by omega) hin' (fun t _ ht => h.le t (by omega)) hc
  have hHh : ∀ t, hh ≤ t → t ≤ k → H t = H hh → 2 ≤ ρ t ∧ K ≤ σ t + 3 := by
    rcases hHe hh (Or.inl rfl) (Or.inr (h.cont hh (by omega) _ hht.1 hht.2)) with hb | hb
    · have := hb hh le_rfl (by omega) rfl; have := h.wid hh (by omega); omega
    · intro t h1 h2 h3; have := hb t h1 h2 h3; have := h.wid t (by omega); omega
  have hHk : ∀ t, hh ≤ t → t ≤ k → H t = H k → ρ t ≤ 2 := by
    rcases hHe k (Or.inr rfl) (Or.inl (h.cont k (by omega) _ hkb.1 hkb.2)) with hb | hb
    · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
    · have := hb k (by omega) le_rfl rfl; have := h.wid k (by omega); omega
  by_cases hab : H hh ≤ H k
  · exact cutF_concl h (by omega) hlev (by have := h.le 0 (by omega); omega) hρl H (by omega) le_rfl hkn
      hkb.1 hhi.le hik.le hH0 hHc hHh (fun _ => le_rfl) hab (fun h' => absurd h' (by omega))
  · apply BConcl.of_revflip h hs.hi
    refine cutF_concl h.revflip (by omega) (fun t ht => ?_) ?_ ?_ (fun t => H (n - 1 - t))
      (p := n - 1 - k) (q := n - 1 - hh) (k := n - 1 - hh) (a := H k) (by omega) le_rfl
      (by omega) ?_ (by omega) (by omega) ?_
      (PCons.revflip hHc (by omega) (by omega) (fun t _ ht => ⟨h.le t (by omega), h.lt t (by omega)⟩))
      (fun t h1 h2 h3 => ?_) (fun _ => ?_) ?_ (fun h' => absurd h' (by omega))
    · have := hlev (n - 1 - t) (by omega); have := h.le (n - 1 - t) (by omega)
      omega
    · have := h.le (n - 1) (by omega); show K - 1 - σ (n - 1) ≤ 1; omega
    · simp only [show n - 1 - (n - 1) = 0 by omega]; omega
    · simp only [show n - 1 - (n - 1 - hh) = hh by omega]; omega
    · simp only [show n - 1 - (n - 1 - i) = i by omega]; exact hH0
    · have := hHk (n - 1 - t) (by omega) (by omega) h3
      have := h.wid (n - 1 - t) (by omega)
      omega
    · show H k ≤ H (n - 1 - (n - 1 - k)); rw [show n - 1 - (n - 1 - k) = k by omega]
    · simp only [show n - 1 - (n - 1 - hh) = hh by omega]; omega

/-- **The special case** (no interior link meets `e₁` or `e_r`, `d₁` meets `e₁`, `d_n` meets
`e_r`, `d_i` in neither end group), given the theorem for fewer coarse links. -/
theorem special_case {K : ℕ} (IH : ∀ K', K' < K → BingMain K') {n : ℕ} {ρ σ : ℕ → ℕ}
    {T : ℕ → ℕ → Prop} {i : ℕ} (h : BHyp n K ρ σ T) (hs : SpecialHyp n K ρ σ T i) :
    BConcl n K ρ σ T i := by
  obtain ⟨hi0, hin, hlev, hσ0, hρl⟩ := hs.facts h
  have hK := hs.hK
  have hρi := hs.hρi
  have hσi := hs.hσi
  obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
    h.crk 0 (n - 1) (by omega) (by omega) 0 (K - 1) hs.h0 hs.hl (by omega)
  have hri : r ≠ i := by intro e; subst e; omega
  have hr'i : r' ≠ i := by intro e; subst e; omega
  have hsR := hs.revflip
  rcases Nat.lt_or_ge K 6 with hK5 | hK6
  · have hK5' : K = 5 := by omega
    by_cases hir' : i < r'
    · exact special_five h hs hK5' hir' (by omega) (by omega)
    · apply BConcl.of_revflip h hs.hi
      refine special_five h.revflip hsR hK5' (k := n - 1 - r) (by omega) (by omega) ?_
      simp only [show n - 1 - (n - 1 - r) = r by omega]; omega
  · by_cases hir : i < r
    · exact special_branch1 IH h hs hK6 hir h2 (by omega)
        ⟨by omega, by omega⟩ (by omega)
    · by_cases hr'i' : r' < i
      · apply BConcl.of_revflip h hs.hi
        refine special_branch1 IH h.revflip hsR hK6
          (hh := n - 1 - r') (k := n - 1 - r) (by omega) (by omega) (by omega) ?_ ?_
        · simp only [show n - 1 - (n - 1 - r') = r' by omega]
          have := h.le r' (by omega); omega
        · simp only [show n - 1 - (n - 1 - r) = r by omega]; omega
      · exact special_middle IH h hs hK6 (by omega : r < i)
          (by omega : i < r') (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

end HPC.Fold.Recon122
