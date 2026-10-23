import HPC.Fold.Recon122General

/-!
# Batch 123: Bing's Theorem 4 in his two-link form, in the model

COMMISSION-batch123.md, item 2. The model of batch 122 (`BHyp`, `PCons`,
`HPC/Fold/Recon122Model.lean`): fine links `t < n`, coarse levels `j < K`, `[ρ t, σ t]` the coarse
links containing the fine link `t`, `T` the meeting table.

`TwoConcl n ρ σ r s` is the conclusion of Bing's Theorem 4 in the block reading without the
only-clauses: a time function `β` (moving by at most one between adjacent links) with `β r = 0`,
`β s` the largest value, and every fibre inside two adjacent coarse links.

* `seg3`: Bing's Theorem 3 (`bing_main`) on a segment `p … q` of the fine chain, in absolute
  indices, with the end clause at both ends of the segment.
* `two_small`: the case of at most four coarse links ("the case of our theorem where `m ≤ 4` is
  easily established"), by an explicit grouping into at most three blocks. It needs `r < s` when
  `K = 3`: with `r = s` the statement is false (`HPC.Fold.not_theorem4Literal`).
* `two_core`: Bing's construction for `K ≥ 5`: `H` from Theorem 3 on `D(1, h)` with `d_r` first,
  `G` from Theorem 3 on `D(k, n)` with `d_s` first, `F = H(1, u − 1) ⌢ (level groups of `D′` from
  the bottom) ⌢ G(v − 1, 1)` reversed.
* `two_model`: the theorem in the model (the case `k < h` by mirroring the coarse chain).
-/

namespace HPC.Fold.Recon123

open HPC.Fold.Recon122

/-- **Bing's Theorem 4 in the model** (block reading, two adjacent links, no only-clauses): `β` with
`β r = 0`, `β s` maximal, moving by at most one, every fibre in two adjacent coarse links. -/
def TwoConcl (n : ℕ) (ρ σ : ℕ → ℕ) (r s : ℕ) : Prop :=
  ∃ β : ℕ → ℕ, β r = 0 ∧ (∀ t, t < n → β t ≤ β s) ∧ PCons 0 (n - 1) ρ σ β

/-- **Theorem 3 on a segment**: Bing's Theorem 3 (`bing_main`) for the fine links `p … q` with
basepoint `i`, in absolute indices, with the end clause at `p` and at `q`. -/
theorem seg3 {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {p q i : ℕ}
    (hpq : p ≤ q) (hq : q < n) (hpi : p ≤ i) (hiq : i ≤ q) :
    ∃ H : ℕ → ℕ, H i = 0 ∧ PCons p q ρ σ H ∧
      ∀ e, (e = p ∨ e = q) → (T e 0 ∨ T e (K - 1)) →
        (∀ t, p ≤ t → t ≤ q → H t = H e → ρ t ≤ 1) ∨
        (∀ t, p ≤ t → t ≤ q → H t = H e → K - 2 ≤ σ t) := by
  have hin : ∀ t, p ≤ t → t ≤ q → 0 ≤ ρ t ∧ σ t ≤ K - 1 :=
    fun t _ ht => ⟨Nat.zero_le _, by have := h.lt t (by omega); omega⟩
  have hB := h.sub hpq hq hin
  have hc := bing_main _ _ _ _ _ (i - p) hB (by omega)
  obtain ⟨H, h0, hHc, he⟩ := BConcl.sub_abs hpq hin (fun t _ ht => h.le t (by omega)) hc
  refine ⟨H, h0, hHc, fun e he' hT => ?_⟩
  rcases he e he' hT with h1 | h1
  · left; intro t a b c; have := h1 t a b c; omega
  · right; intro t a b c; have := h1 t a b c; omega

/-- **At most four coarse links** (Bing: "easily established"): at most three blocks, each in the
first two or in the last two coarse links. For `K = 3` this needs `r < s`. -/
theorem two_small {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) (hK : K ≤ 4)
    {r s : ℕ} (hrs : r ≤ s) (hs : s < n) (hl : ∃ t, r ≤ t ∧ t ≤ s ∧ T t 0)
    (hh : ∃ t, r ≤ t ∧ t ≤ s ∧ T t (K - 1)) (hdeg : r < s ∨ K ≠ 3) : TwoConcl n ρ σ r s := by
  classical
  by_cases hK2 : K ≤ 2
  · refine ⟨fun _ => 0, rfl, fun _ _ => le_rfl, ⟨fun _ _ _ => by simp, fun v => ⟨0, ?_⟩⟩⟩
    intro t _ ht _
    have := h.le t (by omega); have := h.lt t (by omega); omega
  obtain ⟨t0, hrt0, ht0s, hT0⟩ := hl
  obtain ⟨t1, hrt1, ht1s, hT1⟩ := hh
  have hσt0 := h.poss t0 (by omega) 0 hT0
  have hρt1 := h.poss t1 (by omega) _ hT1
  have hle : ∀ t, t < n → ρ t ≤ σ t := h.le
  have hlt : ∀ t, t < n → σ t < K := h.lt
  have hrs' : r < s := by
    rcases hdeg with hd | hd
    · exact hd
    · rcases Nat.lt_or_ge r s with h' | h'
      · exact h'
      · exfalso
        have e0 : t0 = r := by omega
        have e1 : t1 = r := by omega
        rw [e0] at hσt0; rw [e1] at hρt1
        have := hle r (by omega); omega
  -- the two windows: `0` (the first two coarse links) and `K - 2` (the last two)
  have hlow : ∀ t, t < n → ρ t ≤ 1 → 0 ≤ σ t ∧ ρ t ≤ 0 + 1 := fun t _ h1 => ⟨Nat.zero_le _, h1⟩
  have hhigh : ∀ t, t < n → K - 2 ≤ σ t → K - 2 ≤ σ t ∧ ρ t ≤ K - 2 + 1 := by
    intro t ht h1; have := hle t ht; have := hlt t ht; exact ⟨h1, by omega⟩
  have hcov : ∀ t, t < n → 2 ≤ ρ t → K - 2 ≤ σ t := by
    intro t ht h1; have := hle t ht; omega
  by_cases ha : ρ r ≤ 1 ∧ K - 2 ≤ σ s
  · -- (a) `d_r` low, `d_s` high: two blocks
    refine ⟨fun t => if t ≠ s ∧ ρ t ≤ 1 then 0 else 1, by simp [show r ≠ s by omega, ha.1],
      fun t _ => by
        dsimp only; split_ifs <;> omega,
      ⟨fun t _ _ => by dsimp only; constructor <;> split_ifs <;> omega, fun v => ?_⟩⟩
    by_cases hv : v = 0
    · refine ⟨0, fun t _ ht hFt => ?_⟩
      subst hv
      by_cases hc : t ≠ s ∧ ρ t ≤ 1
      · exact hlow t (by omega) hc.2
      · dsimp only at hFt; rw [if_neg hc] at hFt; omega
    · refine ⟨K - 2, fun t _ ht hFt => ?_⟩
      by_cases hc : t ≠ s ∧ ρ t ≤ 1
      · dsimp only at hFt; rw [if_pos hc] at hFt; omega
      · apply hhigh t (by omega)
        by_cases hts : t = s
        · rw [hts]; exact ha.2
        · exact hcov t (by omega) (by omega)
  by_cases hb : K - 2 ≤ σ r ∧ ρ s ≤ 1
  · -- (b) `d_r` high, `d_s` low: two blocks
    refine ⟨fun t => if t ≠ s ∧ K - 2 ≤ σ t then 0 else 1,
      by simp [show r ≠ s by omega, hb.1], fun t _ => by
        dsimp only; split_ifs <;> omega,
      ⟨fun t _ _ => by dsimp only; constructor <;> split_ifs <;> omega, fun v => ?_⟩⟩
    by_cases hv : v = 0
    · refine ⟨K - 2, fun t _ ht hFt => ?_⟩
      subst hv
      by_cases hc : t ≠ s ∧ K - 2 ≤ σ t
      · exact hhigh t (by omega) hc.2
      · dsimp only at hFt; rw [if_neg hc] at hFt; omega
    · refine ⟨0, fun t _ ht hFt => ?_⟩
      by_cases hc : t ≠ s ∧ K - 2 ≤ σ t
      · dsimp only at hFt; rw [if_pos hc] at hFt; omega
      · apply hlow t (by omega)
        by_cases hts : t = s
        · rw [hts]; exact hb.2
        · by_contra hc'
          exact hc ⟨hts, hcov t (by omega) (by omega)⟩
  by_cases hc1 : 2 ≤ ρ r
  · -- (c1) both high: split at the low link `t0`
    have hρs : 2 ≤ ρ s := by
      by_contra hc; exact hb ⟨hcov r (by omega) hc1, by omega⟩
    have h0r : r < t0 := by
      rcases Nat.lt_or_ge r t0 with h' | h'
      · exact h'
      · have : t0 = r := by omega
        subst this; have := hle t0 (by omega); omega
    have h0s : t0 < s := by
      rcases Nat.lt_or_ge t0 s with h' | h'
      · exact h'
      · have : t0 = s := by omega
        subst this; have := hle t0 (by omega); omega
    refine ⟨fun t => if ρ t ≤ 1 then 1 else if t < t0 then 0 else 2, ?_, fun t _ => ?_,
      ⟨fun t _ ht => ?_, fun v => ?_⟩⟩
    · simp only; rw [if_neg (by omega), if_pos h0r]
    · simp only; rw [if_neg (show ¬ ρ s ≤ 1 by omega), if_neg (show ¬ s < t0 by omega)]
      split_ifs <;> omega
    · simp only
      have hadj := h.adj t (by omega)
      have := hle t (by omega); have := hle (t + 1) (by omega)
      have hne : ¬ (2 ≤ ρ t ∧ 2 ≤ ρ (t + 1) ∧ t < t0 ∧ ¬ t + 1 < t0) := by
        rintro ⟨-, h2, h3, h4⟩
        have : t + 1 = t0 := by omega
        rw [this] at h2; have := hle t0 (by omega); omega
      constructor <;> split_ifs <;> omega
    · by_cases hv : v = 1
      · refine ⟨0, fun t _ ht hFt => ?_⟩
        simp only at hFt
        split_ifs at hFt <;> omega
      · refine ⟨K - 2, fun t _ ht hFt => ?_⟩
        simp only at hFt
        split_ifs at hFt with h1 h2 <;> first | omega | exact hhigh t (by omega) (hcov t (by omega) (by omega))
  · -- (c2) both low: split at the high link `t1`
    have hσr : σ r < K - 2 := by
      by_contra hc; exact ha ⟨by omega, by
        by_contra hc'
        exact hb ⟨by omega, by
          by_contra hc''; exact hc' (hcov s (by omega) (by omega))⟩⟩
    have hσs : σ s < K - 2 := by
      by_contra hc; exact ha ⟨by omega, by omega⟩
    have h1r : r < t1 := by
      rcases Nat.lt_or_ge r t1 with h' | h'
      · exact h'
      · have : t1 = r := by omega
        subst this; have := hle t1 (by omega); omega
    have h1s : t1 < s := by
      rcases Nat.lt_or_ge t1 s with h' | h'
      · exact h'
      · have : t1 = s := by omega
        subst this; have := hle t1 (by omega); omega
    refine ⟨fun t => if K - 2 ≤ σ t then 1 else if t < t1 then 0 else 2, ?_, fun t _ => ?_,
      ⟨fun t _ ht => ?_, fun v => ?_⟩⟩
    · simp only; rw [if_neg (by omega), if_pos h1r]
    · simp only; rw [if_neg (show ¬ K - 2 ≤ σ s by omega), if_neg (show ¬ s < t1 by omega)]
      split_ifs <;> omega
    · simp only
      have hne : ¬ (σ t < K - 2 ∧ σ (t + 1) < K - 2 ∧ t < t1 ∧ ¬ t + 1 < t1) := by
        rintro ⟨-, h2, h3, h4⟩
        have : t + 1 = t1 := by omega
        rw [this] at h2; have := hle t1 (by omega); omega
      constructor <;> split_ifs <;> omega
    · by_cases hv : v = 1
      · refine ⟨K - 2, fun t _ ht hFt => ?_⟩
        simp only at hFt
        split_ifs at hFt with h1 h2 <;> first | omega | exact hhigh t (by omega) h1
      · refine ⟨0, fun t _ ht hFt => ?_⟩
        simp only at hFt
        split_ifs at hFt with h1 h2 <;> first | omega |
          exact hlow t (by omega) (by
            by_contra hc; exact h1 (hcov t (by omega) (by omega)))

/-- **Bing's construction, `K ≥ 5`**, with `d_h` (meeting the first coarse link) before `d_k`
(meeting the last), `r ≤ h < k ≤ s`. -/
theorem two_core {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) (hK : 5 ≤ K)
    {r s hh kk : ℕ} (hr : r ≤ hh) (hhk : hh < kk) (hks : kk ≤ s) (hs : s < n) (hT0 : T hh 0)
    (hT1 : T kk (K - 1)) : TwoConcl n ρ σ r s := by
  classical
  obtain ⟨H, hH0, hHc, hHe⟩ := seg3 h (p := 0) (q := hh) (i := r) (Nat.zero_le _) (by omega)
    (Nat.zero_le _) hr
  obtain ⟨G, hG0, hGc, hGe⟩ := seg3 h (p := kk) (q := n - 1) (i := s) (by omega) (by omega) hks
    (by omega)
  have hHe' : ∀ t, t ≤ hh → H t = H hh → ρ t ≤ 1 := by
    rcases hHe hh (Or.inr rfl) (Or.inl hT0) with h1 | h1
    · exact fun t ht e => h1 t (Nat.zero_le _) ht e
    · exfalso
      have := h1 hh (Nat.zero_le _) le_rfl rfl; have := h.poss hh (by omega) 0 hT0; omega
  have hGe' : ∀ t, kk ≤ t → t ≤ n - 1 → G t = G kk → K - 2 ≤ σ t := by
    rcases hGe kk (Or.inl rfl) (Or.inr hT1) with h1 | h1
    · exfalso
      have := h1 kk le_rfl (by omega) rfl; have := h.poss kk (by omega) _ hT1
      have := h.le kk (by omega); omega
    · exact h1
  have hgle : ∀ t, t < n → genG K ρ σ t ≤ K - 3 := by
    intro t ht; have := h.le t ht; have := h.lt t ht; unfold genG; split_ifs <;> omega
  have hg0 : ∀ t, ρ t ≤ 1 → genG K ρ σ t = 0 := by
    intro t ht; unfold genG; rw [if_pos ht]
  have hgK : ∀ t, t < n → K - 2 ≤ σ t → genG K ρ σ t = K - 3 := by
    intro t ht h1; have := h.wid t ht; unfold genG; split_ifs <;> omega
  set a := H hh with ha
  set b := G kk with hb
  set F : ℕ → ℕ := fun t => if t ≤ hh ∧ H t < a then H t
    else if kk ≤ t ∧ G t < b then a + (K - 3) + (b - G t) else a + genG K ρ σ t with hF
  have hP : ∀ t, t ≤ hh → H t < a → F t = H t := by
    intro t h1 h2; simp only [hF]; rw [if_pos ⟨h1, h2⟩]
  have hQ : ∀ t, ¬ (t ≤ hh ∧ H t < a) → kk ≤ t → G t < b → F t = a + (K - 3) + (b - G t) := by
    intro t h1 h2 h3; simp only [hF]; rw [if_neg h1, if_pos ⟨h2, h3⟩]
  have hR : ∀ t, ¬ (t ≤ hh ∧ H t < a) → ¬ (kk ≤ t ∧ G t < b) → F t = a + genG K ρ σ t := by
    intro t h1 h2; simp only [hF]; rw [if_neg h1, if_neg h2]
  have hFs : F s = a + (K - 3) + b := by
    have hnP : ¬ (s ≤ hh ∧ H s < a) := by omega
    by_cases hGs : G s < b
    · rw [hQ s hnP hks hGs, hG0]; omega
    · rw [hR s hnP (by omega), hgK s hs (hGe' s hks (by omega) (by omega))]; omega
  refine ⟨F, ?_, fun t ht => ?_, ⟨fun t _ ht => ?_, fun v => ?_⟩⟩
  · by_cases hr' : H r < a
    · rw [hP r hr hr', hH0]
    · rw [hR r (by omega) (by omega), hg0 r (hHe' r hr (by omega))]; omega
  · rw [hFs]
    by_cases hPt : t ≤ hh ∧ H t < a
    · rw [hP t hPt.1 hPt.2]; omega
    · by_cases hQt : kk ≤ t ∧ G t < b
      · rw [hQ t hPt hQt.1 hQt.2]; omega
      · rw [hR t hPt hQt]; have := hgle t ht; omega
  · -- moving by at most one
    have hHl := hHc.1
    have hGl := hGc.1
    by_cases hPt : t ≤ hh ∧ H t < a <;> by_cases hPt' : t + 1 ≤ hh ∧ H (t + 1) < a
    · rw [hP t hPt.1 hPt.2, hP _ hPt'.1 hPt'.2]
      exact hHl t (Nat.zero_le _) hPt'.1
    · have ht1 : t + 1 ≤ hh := by
        by_contra hc
        have : t = hh := by omega
        rw [this] at hPt; exact absurd hPt.2 (lt_irrefl _)
      have := hHl t (Nat.zero_le _) ht1
      have e1 : H (t + 1) = a := by omega
      rw [hP t hPt.1 hPt.2, hR _ hPt' (by omega), hg0 _ (hHe' _ ht1 e1)]; omega
    · have := hHl t (Nat.zero_le _) hPt'.1
      have e1 : H t = a := by omega
      rw [hR t hPt (by omega), hP _ hPt'.1 hPt'.2, hg0 _ (hHe' _ (by omega) e1)]; omega
    · by_cases hQt : kk ≤ t ∧ G t < b <;> by_cases hQt' : kk ≤ t + 1 ∧ G (t + 1) < b
      · rw [hQ t hPt hQt.1 hQt.2, hQ _ hPt' hQt'.1 hQt'.2]
        have := hGl t hQt.1 (by omega); omega
      · have := hGl t hQt.1 (by omega)
        have e1 : G (t + 1) = b := by omega
        rw [hQ t hPt hQt.1 hQt.2, hR _ hPt' hQt',
          hgK _ (by omega) (hGe' _ (by omega) (by omega) e1)]; omega
      · have hkt : kk ≤ t := by
          by_contra hc
          have : t + 1 = kk := by omega
          rw [this] at hQt'; exact absurd hQt'.2 (lt_irrefl _)
        have := hGl t hkt (by omega)
        have e1 : G t = b := by omega
        rw [hR t hPt hQt, hQ _ hPt' hQt'.1 hQt'.2, hgK _ (by omega) (hGe' _ hkt (by omega) e1)]
        omega
      · rw [hR t hPt hQt, hR _ hPt' hQt']
        have hadj := h.adj t (by omega)
        have := genG_lip (ρ := ρ) (σ := σ) (t := t) (t' := t + 1) hK (h.le t (by omega))
          (h.le (t + 1) (by omega)) (h.wid t (by omega)) hadj.1 hadj.2
        have := genG_lip (ρ := ρ) (σ := σ) (t := t + 1) (t' := t) hK (h.le (t + 1) (by omega))
          (h.le t (by omega)) (h.wid (t + 1) (by omega)) hadj.2 hadj.1
        omega
  · -- every fibre in two adjacent coarse links
    by_cases hva : v < a
    · obtain ⟨j, hj⟩ := hHc.2 v
      refine ⟨j, fun t _ ht hFt => ?_⟩
      by_cases hPt : t ≤ hh ∧ H t < a
      · rw [hP t hPt.1 hPt.2] at hFt; exact hj t (Nat.zero_le _) hPt.1 hFt
      · by_cases hQt : kk ≤ t ∧ G t < b
        · rw [hQ t hPt hQt.1 hQt.2] at hFt; omega
        · rw [hR t hPt hQt] at hFt; omega
    · by_cases hvK : v ≤ a + (K - 3)
      · refine ⟨genWin K (v - a), fun t _ ht hFt => ?_⟩
        by_cases hPt : t ≤ hh ∧ H t < a
        · rw [hP t hPt.1 hPt.2] at hFt; omega
        · by_cases hQt : kk ≤ t ∧ G t < b
          · rw [hQ t hPt hQt.1 hQt.2] at hFt; omega
          · rw [hR t hPt hQt] at hFt
            rw [show v - a = genG K ρ σ t by omega]
            exact genWin_spec hK (h.le t (by omega)) (h.lt t (by omega))
      · obtain ⟨j, hj⟩ := hGc.2 (a + (K - 3) + b - v)
        refine ⟨j, fun t _ ht hFt => ?_⟩
        by_cases hPt : t ≤ hh ∧ H t < a
        · rw [hP t hPt.1 hPt.2] at hFt; omega
        · by_cases hQt : kk ≤ t ∧ G t < b
          · rw [hQ t hPt hQt.1 hQt.2] at hFt
            exact hj t hQt.1 ht (by omega)
          · rw [hR t hPt hQt] at hFt; have := hgle t (by omega); omega

/-- **Bing's Theorem 4 in the model** (block reading, two adjacent links, without the
only-clauses). The non-degeneracy hypothesis `r < s ∨ K ≠ 3` is needed
(`HPC.Fold.not_theorem4Literal`). -/
theorem two_model {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T)
    {r s : ℕ} (hrs : r ≤ s) (hs : s < n) (hl : ∃ t, r ≤ t ∧ t ≤ s ∧ T t 0)
    (hh : ∃ t, r ≤ t ∧ t ≤ s ∧ T t (K - 1)) (hdeg : r < s ∨ K ≠ 3) : TwoConcl n ρ σ r s := by
  by_cases hK : K ≤ 4
  · exact two_small h hK hrs hs hl hh hdeg
  obtain ⟨t0, hrt0, ht0s, hT0⟩ := hl
  obtain ⟨t1, hrt1, ht1s, hT1⟩ := hh
  have hp0 := h.poss t0 (by omega) 0 hT0
  have hp1 := h.poss t1 (by omega) _ hT1
  rcases Nat.lt_or_ge t0 t1 with h01 | h01
  · exact two_core h (by omega) hrt0 h01 ht1s hs hT0 hT1
  · have h10 : t1 < t0 := by
      rcases eq_or_lt_of_le h01 with e | e
      · rw [e] at hp1; have := h.le t0 (by omega); omega
      · exact e
    -- mirror the coarse chain
    obtain ⟨β, h0, hmax, hlip, hwid⟩ := two_core h.flip (by omega) hrt1 h10 ht0s hs
      (show flipT K T t1 0 from ⟨by omega, by rwa [show K - 1 - 0 = K - 1 by omega]⟩)
      (show flipT K T t0 (K - 1) from ⟨le_rfl, by rwa [show K - 1 - (K - 1) = 0 by omega]⟩)
    refine ⟨β, h0, hmax, hlip, fun v => ?_⟩
    obtain ⟨j, hj⟩ := hwid v
    refine ⟨K - 2 - j, fun t h1 h2 h3 => ?_⟩
    have := hj t h1 h2 h3; simp only at this
    have := h.lt t (by omega); have := h.le t (by omega); omega

end HPC.Fold.Recon123
