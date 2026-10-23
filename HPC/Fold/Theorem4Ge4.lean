import HPC.Fold.Theorem4Only

/-!
# Batch 125, item 2: Theorem 4 as printed with at least four coarse links

COMMISSION-batch125.md, item 2. The model of batch 122 (`BHyp`, `PCons`); the construction of
`two_core` (batch 123) with three changes:

* the two applications of Theorem 3 are the **pair form** (`seg3Z`, from `pair_main` of batch 124):
  `d_r` together with a companion `d_{r'}` (a neighbour sharing a coarse link) in the first block of
  `H`, `d_s` with a companion `d_{s'}` in the first block of `G`;
* the middle groups are `genG` except that the whole `G`-block of `d_k` is sent to the top group
  (`K − 3`). For `K ≥ 5` this changes nothing; for `K = 4` it is the new grouping that the report of
  batch 124 asked for (a link in `e₂ ∩ e₃`-position `[1, 2]` next to the `G`-part is sent up);
* when the companion would fall outside the segment of Theorem 3 (`r = h` and `r' = h + 1`, or
  `s = k` and `s' = k − 1`), no companion is needed: at `d_h` (which meets `e₁`) every neighbour
  outside the first block lies in no link of `D` that could meet `e₁` (`OnlyE`), and symmetrically
  at `d_k`.

`OnlyM` collects the three model conditions under which the only-clause holds for chains
(`HPC.Fold.onlyIn_of_onlyM`); `HPC.Fold.theorem4_literal_ge4_model` moves the model theorem
`two_modelZ` to chains (the commissioned `theorem4_literal_ge4` in `HPC/Plane/Jct1.lean` is this
theorem).

Nothing in this file is `sorry`.
-/

namespace HPC.Fold.Recon123

open HPC.Fold.Recon122

/-- **The meeting condition for the only-clause**: some coarse link `e_j` met by the fine link `i`
cannot be met by any neighbour of `i` lying in another block. -/
def OnlyE (n : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (β : ℕ → ℕ) (i : ℕ) : Prop :=
  ∃ j, T i j ∧ ∀ t, t < n → (t + 1 = i ∨ i + 1 = t) → β t ≠ β i → ¬ (σ t ≤ j + 1 ∧ j ≤ ρ t + 1)

/-- **The model conditions for the only-clause at `i`**: a neighbour in the block of `i`; or no
neighbour shares a coarse link with `i`; or `OnlyE`. -/
def OnlyM (n : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (β : ℕ → ℕ) (i : ℕ) : Prop :=
  (∃ t, t < n ∧ (t + 1 = i ∨ i + 1 = t) ∧ β t = β i) ∨
  (∀ t, t < n → (t + 1 = i ∨ i + 1 = t) → ¬ CommonC ρ σ i t) ∨
  OnlyE n ρ σ T β i

/-- **The pair form of Theorem 3 on a segment** (`seg3` with a pair of basepoints). -/
theorem seg3Z {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {p q i i' : ℕ}
    (hpq : p ≤ q) (hq : q < n) (hpi : p ≤ i) (hiq : i ≤ q) (hpi' : p ≤ i') (hiq' : i' ≤ q)
    (h1 : i ≤ i' + 1) (h2 : i' ≤ i + 1) (hc : CommonC ρ σ i i') :
    ∃ H : ℕ → ℕ, H i = 0 ∧ H i' = 0 ∧ PCons p q ρ σ H ∧
      ∀ e, (e = p ∨ e = q) → (T e 0 ∨ T e (K - 1)) →
        (∀ t, p ≤ t → t ≤ q → H t = H e → ρ t ≤ 1) ∨
        (∀ t, p ≤ t → t ≤ q → H t = H e → K - 2 ≤ σ t) := by
  have hin : ∀ t, p ≤ t → t ≤ q → 0 ≤ ρ t ∧ σ t ≤ K - 1 :=
    fun t _ ht => ⟨Nat.zero_le _, by have := h.lt t (by omega); omega⟩
  have hB := h.sub hpq hq hin
  obtain ⟨c, c1, c2, c3, c4⟩ := hc
  have hc' := pair_main _ _ _ _ _ (i - p) (i' - p) hB (by omega) (by omega) (by omega) (by omega)
    ⟨c, by simp only [show i - p + p = i by omega]; omega,
      by simp only [show i - p + p = i by omega]; omega,
      by simp only [show i' - p + p = i' by omega]; omega,
      by simp only [show i' - p + p = i' by omega]; omega⟩
  have hc'' := BConclZ.mono (Z' := fun t => pairZ i i' (t + p)) (fun x _ hx => by
    rcases hx with hx | hx
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)) hc'
  obtain ⟨H, h0, hHc, he⟩ := BConclZ.sub_abs hpq hin (fun t _ ht => h.le t (by omega)) hc''
  refine ⟨H, h0 i hpi hiq (Or.inl rfl), h0 i' hpi' hiq' (Or.inr rfl), hHc, fun e he' hT => ?_⟩
  rcases he e he' hT with h1 | h1
  · left; intro t a b c; have := h1 t a b c; omega
  · right; intro t a b c; have := h1 t a b c; omega

theorem genG_lip4 {K : ℕ} {ρ σ : ℕ → ℕ} {t t' : ℕ} (hK : 4 ≤ K) (h1 : ρ t ≤ σ t)
    (h1' : ρ t' ≤ σ t') (hw : σ t ≤ ρ t + 1) (ha : σ t ≤ ρ t' + 1) (ha' : σ t' ≤ ρ t + 1) :
    genG K ρ σ t ≤ genG K ρ σ t' + 1 := by
  unfold genG; split_ifs <;> omega

theorem genWin_spec4 {K : ℕ} {ρ σ : ℕ → ℕ} {t : ℕ} (hK : 4 ≤ K) (h1 : ρ t ≤ σ t)
    (hs : σ t < K) : genWin K (genG K ρ σ t) ≤ σ t ∧ ρ t ≤ genWin K (genG K ρ σ t) + 1 := by
  unfold genWin genG; split_ifs <;> omega

/-- **Bing's construction with companions, `K ≥ 4`**, `d_h` (meeting the first coarse link) before
`d_k` (meeting the last), `r ≤ h < k ≤ s`, companions `r' ≤ h` of `r` and `s' ≥ k` of `s` (equal
or adjacent, in a common coarse link; `r' = r`, `s' = s` allowed). At `r = h` and at `s = k` the
meeting condition `OnlyE` holds. -/
theorem two_coreZ {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) (hK : 4 ≤ K)
    {r r' s s' hh kk : ℕ} (hr : r ≤ hh) (hhk : hh < kk) (hks : kk ≤ s) (hs : s < n)
    (hT0 : T hh 0) (hT1 : T kk (K - 1))
    (hr'h : r' ≤ hh) (hr1 : r ≤ r' + 1) (hr2 : r' ≤ r + 1) (hcr : CommonC ρ σ r r')
    (hs'k : kk ≤ s') (hs'n : s' < n) (hs1 : s ≤ s' + 1) (hs2 : s' ≤ s + 1)
    (hcs : CommonC ρ σ s s') :
    ∃ β : ℕ → ℕ, β r = 0 ∧ β r' = 0 ∧ β s' = β s ∧ (∀ t, t < n → β t ≤ β s) ∧
      PCons 0 (n - 1) ρ σ β ∧ (r = hh → OnlyE n ρ σ T β r) ∧ (s = kk → OnlyE n ρ σ T β s) := by
  classical
  obtain ⟨H, hH0, hH0', hHc, hHe⟩ := seg3Z h (p := 0) (q := hh) (i := r) (i' := r')
    (Nat.zero_le _) (by omega) (Nat.zero_le _) hr (Nat.zero_le _) hr'h hr1 hr2 hcr
  obtain ⟨G, hG0, hG0', hGc, hGe⟩ := seg3Z h (p := kk) (q := n - 1) (i := s) (i' := s')
    (by omega) (by omega) hks (by omega) hs'k (by omega) hs1 hs2 hcs
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
  set a := H hh with ha
  set b := G kk with hb
  set g : ℕ → ℕ := fun t => if kk ≤ t ∧ G t = b then K - 3 else genG K ρ σ t with hg
  have hgle : ∀ t, t < n → g t ≤ K - 3 := by
    intro t ht; have := h.le t ht; have := h.lt t ht
    simp only [hg]; unfold genG; split_ifs <;> omega
  have hg0 : ∀ t, t < kk → ρ t ≤ 1 → g t = 0 := by
    intro t h1 h2; simp only [hg]; rw [if_neg (by omega)]; unfold genG; rw [if_pos h2]
  have hgK : ∀ t, kk ≤ t → G t = b → g t = K - 3 := by
    intro t h1 h2; simp only [hg]; rw [if_pos ⟨h1, h2⟩]
  have hgK' : ∀ t, t < n → K - 2 ≤ σ t → 2 ≤ ρ t → g t = K - 3 := by
    intro t ht h1 h2; have := h.wid t ht; simp only [hg]; unfold genG
    split_ifs <;> omega
  -- `g t ≠ 0` forces `σ t ≥ 2`; `g t ≠ K − 3` forces `ρ t < K − 2`
  have hgn0 : ∀ t, t < n → g t ≠ 0 → 2 ≤ σ t := by
    intro t ht h1
    have := h.le t ht
    simp only [hg] at h1
    split_ifs at h1 with h2
    · have := hGe' t h2.1 (by omega) h2.2; omega
    · unfold genG at h1; split_ifs at h1 <;> omega
  have hgnK : ∀ t, t < n → g t ≠ K - 3 → ρ t < K - 2 := by
    intro t ht h1
    have := h.le t ht
    simp only [hg] at h1
    split_ifs at h1 with h2
    · exact absurd rfl h1
    · unfold genG at h1; split_ifs at h1 <;> omega
  have hglip : ∀ t, t + 1 < n → g (t + 1) ≤ g t + 1 ∧ g t ≤ g (t + 1) + 1 := by
    intro t ht
    have hadj := h.adj t ht
    have l0 := h.le t (by omega); have l1 := h.le (t + 1) ht
    have w0 := h.wid t (by omega); have w1 := h.wid (t + 1) ht
    have k0 := h.lt t (by omega); have k1 := h.lt (t + 1) ht
    have e1 := genG_lip4 (ρ := ρ) (σ := σ) (t := t) (t' := t + 1) hK l0 l1 w0 hadj.1 hadj.2
    have e2 := genG_lip4 (ρ := ρ) (σ := σ) (t := t + 1) (t' := t) hK l1 l0 w1 hadj.2 hadj.1
    simp only [hg]
    by_cases c0 : kk ≤ t ∧ G t = b <;> by_cases c1 : kk ≤ t + 1 ∧ G (t + 1) = b
    · rw [if_pos c0, if_pos c1]; omega
    · rw [if_pos c0, if_neg c1]
      have := hGe' t c0.1 (by omega) c0.2
      unfold genG; split_ifs <;> omega
    · rw [if_neg c0, if_pos c1]
      have := hGe' (t + 1) c1.1 (by omega) c1.2
      unfold genG; split_ifs <;> omega
    · rw [if_neg c0, if_neg c1]; omega
  have hgwin : ∀ t, t < n → genWin K (g t) ≤ σ t ∧ ρ t ≤ genWin K (g t) + 1 := by
    intro t ht
    have := h.le t ht; have := h.lt t ht
    simp only [hg]
    split_ifs with c
    · have := hGe' t c.1 (by omega) c.2
      unfold genWin; split_ifs <;> omega
    · exact genWin_spec4 hK (h.le t ht) (h.lt t ht)
  set F : ℕ → ℕ := fun t => if t ≤ hh ∧ H t < a then H t
    else if kk ≤ t ∧ G t < b then a + (K - 3) + (b - G t) else a + g t with hF
  have hP : ∀ t, t ≤ hh → H t < a → F t = H t := by
    intro t h1 h2; simp only [hF]; rw [if_pos ⟨h1, h2⟩]
  have hQ : ∀ t, ¬ (t ≤ hh ∧ H t < a) → kk ≤ t → G t < b → F t = a + (K - 3) + (b - G t) := by
    intro t h1 h2 h3; simp only [hF]; rw [if_neg h1, if_pos ⟨h2, h3⟩]
  have hR : ∀ t, ¬ (t ≤ hh ∧ H t < a) → ¬ (kk ≤ t ∧ G t < b) → F t = a + g t := by
    intro t h1 h2; simp only [hF]; rw [if_neg h1, if_neg h2]
  have hlow : ∀ x, x ≤ hh → H x = 0 → F x = 0 := by
    intro x hx h0
    by_cases hx' : H x < a
    · rw [hP x hx hx', h0]
    · rw [hR x (by omega) (by omega), hg0 x (by omega) (hHe' x hx (by omega))]; omega
  have hhigh : ∀ x, kk ≤ x → x < n → G x = 0 → F x = a + (K - 3) + b := by
    intro x hx hxn h0
    have hnP : ¬ (x ≤ hh ∧ H x < a) := by omega
    by_cases hGx : G x < b
    · rw [hQ x hnP hx hGx, h0]; omega
    · rw [hR x hnP (by omega), hgK x hx (by omega)]; omega
  have hFr := hlow r hr hH0
  have hFs := hhigh s hks hs hG0
  refine ⟨F, hFr, hlow r' hr'h hH0', by rw [hhigh s' hs'k hs'n hG0', hFs], fun t ht => ?_,
    ⟨fun t _ ht => ?_, fun v => ?_⟩, fun hrh => ?_, fun hsk => ?_⟩
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
      rw [hP t hPt.1 hPt.2, hR _ hPt' (by omega), hg0 _ (by omega) (hHe' _ ht1 e1)]; omega
    · have := hHl t (Nat.zero_le _) hPt'.1
      have e1 : H t = a := by omega
      rw [hR t hPt (by omega), hP _ hPt'.1 hPt'.2, hg0 _ (by omega) (hHe' _ (by omega) e1)]
      omega
    · by_cases hQt : kk ≤ t ∧ G t < b <;> by_cases hQt' : kk ≤ t + 1 ∧ G (t + 1) < b
      · rw [hQ t hPt hQt.1 hQt.2, hQ _ hPt' hQt'.1 hQt'.2]
        have := hGl t hQt.1 (by omega); omega
      · have := hGl t hQt.1 (by omega)
        have e1 : G (t + 1) = b := by omega
        rw [hQ t hPt hQt.1 hQt.2, hR _ hPt' hQt', hgK _ (by omega) e1]; omega
      · have hkt : kk ≤ t := by
          by_contra hc
          have : t + 1 = kk := by omega
          rw [this] at hQt'; exact absurd hQt'.2 (lt_irrefl _)
        have := hGl t hkt (by omega)
        have e1 : G t = b := by omega
        rw [hR t hPt hQt, hQ _ hPt' hQt'.1 hQt'.2, hgK _ hkt e1]
        omega
      · rw [hR t hPt hQt, hR _ hPt' hQt']
        have := hglip t (by omega)
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
            rw [show v - a = g t by omega]
            exact hgwin t (by omega)
      · obtain ⟨j, hj⟩ := hGc.2 (a + (K - 3) + b - v)
        refine ⟨j, fun t _ ht hFt => ?_⟩
        by_cases hPt : t ≤ hh ∧ H t < a
        · rw [hP t hPt.1 hPt.2] at hFt; omega
        · by_cases hQt : kk ≤ t ∧ G t < b
          · rw [hQ t hPt hQt.1 hQt.2] at hFt
            exact hj t hQt.1 ht (by omega)
          · rw [hR t hPt hQt] at hFt; have := hgle t (by omega); omega
  · -- `r = h`: no neighbour outside the first block lies in a link that could meet `e₁`
    subst hrh
    have ha0 : a = 0 := hH0
    refine ⟨0, hT0, fun t ht hnb hne => ?_⟩
    have hnP : ¬ (t ≤ r ∧ H t < a) := by omega
    have hnQ : ¬ (kk ≤ t ∧ G t < b) := by
      rintro ⟨h1, h2⟩
      have : t = kk := by omega
      rw [this] at h2; exact lt_irrefl _ h2
    rw [hR t hnP hnQ, hFr, ha0] at hne
    have := hgn0 t ht (by omega)
    omega
  · -- `s = k`: symmetrically, with the last coarse link
    subst hsk
    have hb0 : b = 0 := hG0
    refine ⟨K - 1, hT1, fun t ht hnb hne => ?_⟩
    have hnP : ¬ (t ≤ hh ∧ H t < a) := by
      rintro ⟨h1, h2⟩
      have : t = hh := by omega
      rw [this] at h2; exact lt_irrefl _ h2
    have hnQ : ¬ (s ≤ t ∧ G t < b) := by omega
    rw [hR t hnP hnQ, hFs, hb0] at hne
    have := hgnK t ht (by omega)
    omega

/-- `two_coreZ` with the companions chosen: a neighbour sharing a coarse link if there is one (and
`r < h`, resp. `k < s`), the link itself otherwise. -/
theorem two_modelZ_lt {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T)
    (hK : 4 ≤ K) {r s hh kk : ℕ} (hr : r ≤ hh) (hhk : hh < kk) (hks : kk ≤ s) (hs : s < n)
    (hT0 : T hh 0) (hT1 : T kk (K - 1)) :
    ∃ β : ℕ → ℕ, β r = 0 ∧ (∀ t, t < n → β t ≤ β s) ∧ PCons 0 (n - 1) ρ σ β ∧
      OnlyM n ρ σ T β r ∧ OnlyM n ρ σ T β s := by
  classical
  have hself : ∀ x, x < n → CommonC ρ σ x x := fun x hx =>
    ⟨ρ x, le_rfl, h.le x hx, le_rfl, h.le x hx⟩
  obtain ⟨r', hr'h, hr1, hr2, hcr, hr'⟩ : ∃ r', r' ≤ hh ∧ r ≤ r' + 1 ∧ r' ≤ r + 1 ∧
      CommonC ρ σ r r' ∧ (r < hh → ((r' + 1 = r ∨ r + 1 = r') ∨
        ∀ t, t < n → (t + 1 = r ∨ r + 1 = t) → ¬ CommonC ρ σ r t)) := by
    by_cases hc : r < hh ∧ ∃ t, t < n ∧ (t + 1 = r ∨ r + 1 = t) ∧ CommonC ρ σ r t
    · obtain ⟨h1, t, ht, hnb, hct⟩ := hc
      exact ⟨t, by omega, by omega, by omega, hct, fun _ => Or.inl hnb⟩
    · refine ⟨r, hr, by omega, by omega, hself r (by omega), fun h1 => Or.inr ?_⟩
      intro t ht hnb hct
      exact hc ⟨h1, t, ht, hnb, hct⟩
  obtain ⟨s', hs'k, hs'n, hs1, hs2, hcs, hs'⟩ : ∃ s', kk ≤ s' ∧ s' < n ∧ s ≤ s' + 1 ∧
      s' ≤ s + 1 ∧ CommonC ρ σ s s' ∧ (kk < s → ((s' + 1 = s ∨ s + 1 = s') ∨
        ∀ t, t < n → (t + 1 = s ∨ s + 1 = t) → ¬ CommonC ρ σ s t)) := by
    by_cases hc : kk < s ∧ ∃ t, t < n ∧ (t + 1 = s ∨ s + 1 = t) ∧ CommonC ρ σ s t
    · obtain ⟨h1, t, ht, hnb, hct⟩ := hc
      exact ⟨t, by omega, ht, by omega, by omega, hct, fun _ => Or.inl hnb⟩
    · refine ⟨s, hks, hs, by omega, by omega, hself s hs, fun h1 => Or.inr ?_⟩
      intro t ht hnb hct
      exact hc ⟨h1, t, ht, hnb, hct⟩
  obtain ⟨β, hβr, hβr', hβs', hmax, hc, honr, hons⟩ :=
    two_coreZ h hK hr hhk hks hs hT0 hT1 hr'h hr1 hr2 hcr hs'k hs'n hs1 hs2 hcs
  refine ⟨β, hβr, hmax, hc, ?_, ?_⟩
  · by_cases hrh : r = hh
    · exact Or.inr (Or.inr (honr hrh))
    · rcases hr' (by omega) with hnb | hno
      · exact Or.inl ⟨r', by omega, hnb, by rw [hβr', hβr]⟩
      · exact Or.inr (Or.inl hno)
  · by_cases hsk : s = kk
    · exact Or.inr (Or.inr (hons hsk))
    · rcases hs' (by omega) with hnb | hno
      · exact Or.inl ⟨s', hs'n, hnb, hβs'⟩
      · exact Or.inr (Or.inl hno)

/-- The only-clause conditions are invariant under mirroring the coarse chain. -/
theorem OnlyM.of_flip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T)
    {β : ℕ → ℕ} {i : ℕ} (hi : i < n)
    (ho : OnlyM n (fun t => K - 1 - σ t) (fun t => K - 1 - ρ t) (flipT K T) β i) :
    OnlyM n ρ σ T β i := by
  rcases ho with ho | ho | ⟨j, ⟨hjK, hT⟩, ho⟩
  · exact Or.inl ho
  · refine Or.inr (Or.inl fun t ht hnb ⟨c, c1, c2, c3, c4⟩ => ho t ht hnb ⟨K - 1 - c, ?_⟩)
    have := h.lt i hi; have := h.lt t ht
    simp only
    omega
  · refine Or.inr (Or.inr ⟨K - 1 - j, hT, fun t ht hnb hne hpos => ho t ht hnb hne ?_⟩)
    have := h.lt t ht; have := h.le t ht
    simp only
    omega

/-- **Theorem 4 as printed in the model, `K ≥ 4`**: `β` with `β r = 0`, `β s` maximal, moving by
at most one, every fibre in two adjacent coarse links, and the only-clause conditions `OnlyM` at
`r` and at `s`. -/
theorem two_modelZ {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T)
    (hK : 4 ≤ K) {r s : ℕ} (hs : s < n) (hl : ∃ t, r ≤ t ∧ t ≤ s ∧ T t 0)
    (hh : ∃ t, r ≤ t ∧ t ≤ s ∧ T t (K - 1)) :
    ∃ β : ℕ → ℕ, β r = 0 ∧ (∀ t, t < n → β t ≤ β s) ∧ PCons 0 (n - 1) ρ σ β ∧
      OnlyM n ρ σ T β r ∧ OnlyM n ρ σ T β s := by
  obtain ⟨t0, hrt0, ht0s, hT0⟩ := hl
  obtain ⟨t1, hrt1, ht1s, hT1⟩ := hh
  have hp0 := h.poss t0 (by omega) 0 hT0
  have hp1 := h.poss t1 (by omega) _ hT1
  rcases Nat.lt_or_ge t0 t1 with h01 | h01
  · exact two_modelZ_lt h hK hrt0 h01 ht1s hs hT0 hT1
  · have h10 : t1 < t0 := by
      rcases eq_or_lt_of_le h01 with e | e
      · rw [e] at hp1; have := h.le t0 (by omega); omega
      · exact e
    obtain ⟨β, h0, hmax, ⟨hlip, hwid⟩, hor, hos⟩ := two_modelZ_lt h.flip hK hrt1 h10 ht0s hs
      (show flipT K T t1 0 from ⟨by omega, by rwa [show K - 1 - 0 = K - 1 by omega]⟩)
      (show flipT K T t0 (K - 1) from ⟨le_rfl, by rwa [show K - 1 - (K - 1) = 0 by omega]⟩)
    refine ⟨β, h0, hmax, ⟨hlip, fun v => ?_⟩, hor.of_flip h (by omega), hos.of_flip h hs⟩
    obtain ⟨j, hj⟩ := hwid v
    refine ⟨K - 2 - j, fun t h1 h2 h3 => ?_⟩
    have := hj t h1 h2 h3; simp only at this
    have := h.lt t (by omega); have := h.le t (by omega); omega

end HPC.Fold.Recon123

namespace HPC.Fold

open HPC HPC.Chain HPC.Fold.Recon122 HPC.Fold.Recon123

/-- **The only-clause from a meeting**: if `E.link i` meets `D.link j` and no neighbour of `i` in
another block meets `D.link j`, then `E.link i` lies in no other block. -/
theorem onlyIn_of_meet {X : Type*} [MetricSpace X] {n k q : ℕ} {E : Chain X n} {D : Chain X k}
    {β : Fin n → Fin q} (hβ : IsBlockMap β) {i : Fin n} {j : Fin k}
    (hm : (E.link i ∩ D.link j).Nonempty)
    (hnb : ∀ t : Fin n, ((t : ℤ) - (i : ℤ)).natAbs = 1 → β t ≠ β i →
      ¬ (E.link t ∩ D.link j).Nonempty) :
    OnlyIn E β hβ i := by
  intro v hv hsub
  obtain ⟨x, hxi, hxj⟩ := hm
  have hx := Recon121.link_subset_neighbours E hβ hv hsub hxi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
  obtain ⟨t, ⟨hβt, ht⟩, hxt⟩ := hx
  exact hnb t ht (by rw [hβt]; exact hv) ⟨x, hxt, hxj⟩

/-- **The model conditions give the only-clause** for the block map `natBlock b` of a solution
whose blocks lie in two adjacent links of `D`. -/
theorem onlyIn_of_onlyM {X : Type*} [MetricSpace X] {n k q : ℕ} {E : Chain X n} {D : Chain X k}
    (hcr : E.IsCrookedIn' D) {b : ℕ → ℕ} (hlt : ∀ t, t < n → b t < q)
    (hβ : IsBlockMap (natBlock b hlt))
    (hblk : ∀ v, ∃ j : ℕ, (E.ofBlocks _ hβ).link v ⊆ D.unionRange j 2) (i : Fin n)
    (ho : OnlyM n (chainRho hcr.1) (chainSig hcr.1) (chainT E D) b i) :
    OnlyIn E (natBlock b hlt) hβ i := by
  have hB := bHyp_of_crooked hcr
  rcases ho with ⟨t, ht, hnb, hbt⟩ | hno | ⟨j, ⟨hi, hj, hm⟩, hnb⟩
  · exact onlyIn_of_neighbour E hβ (t₀ := ⟨t, ht⟩) (by simp only; omega)
      (Fin.ext (by simp [natBlock, hbt]))
  · refine onlyIn_of_no_common hcr hβ hblk i fun t₀ ht₀ => ?_
    rintro ⟨⟨j, hj⟩, hj1, hj2⟩
    have c1 := (subset_link_iff hcr i j hj).mp hj1
    have c2 := (subset_link_iff hcr t₀ j hj).mp hj2
    exact hno t₀ t₀.isLt (by omega) ⟨j, c1.1, c1.2, c2.1, c2.2⟩
  · refine onlyIn_of_meet hβ (j := ⟨j, hj⟩) hm fun t ht hne hmt => ?_
    have hT : chainT E D t j := ⟨t.isLt, hj, hmt⟩
    have hne' : b t ≠ b i := fun e => hne (Fin.ext (by simp [natBlock, e]))
    exact hnb t t.isLt (by omega) hne' (hB.poss t t.isLt j hT)

/-- **Bing's Theorem 4 as printed, `k ≥ 4`** (the statement of `Theorem4LiteralGe4`). -/
theorem theorem4_literal_ge4_model {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 4 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β r).val = 0 ∧ (β s).val = q - 1 ∧ OnlyIn E β hβ r ∧ OnlyIn E β hβ s ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 2 := by
  have hB := bHyp_of_crooked hcr
  obtain ⟨hl, hrl, hls, hlm⟩ := hlow
  obtain ⟨hh, hrh, hhs, hhm⟩ := hhigh
  obtain ⟨b, hb0, hmax, ⟨hlip, hwid⟩, hor, hos⟩ := two_modelZ hB hk s.isLt
    ⟨hl.val, Fin.le_def.mp hrl, Fin.le_def.mp hls, hl.isLt, by omega, hlm⟩
    ⟨hh.val, Fin.le_def.mp hrh, Fin.le_def.mp hhs, hh.isLt, by omega, hhm⟩
  have hrs' : r.val ≤ s.val := Fin.le_def.mp hrs
  have hlt : ∀ t, t < n → b t < b s + 1 := fun t ht => Nat.lt_succ_of_le (hmax t ht)
  have hlip' : ∀ t, t + 1 < n → (b (t + 1) : ℤ) - b t ≤ 1 ∧ (b t : ℤ) - b (t + 1) ≤ 1 := by
    intro t ht; have := hlip t (Nat.zero_le _) (by omega); omega
  have hsurj : ∀ j, j < b s + 1 → ∃ t, t < n ∧ b t = j := by
    intro j hj
    obtain ⟨t, h1, h2, h3⟩ := nat_ivt b r.val (s.val - r.val)
      (fun t h1 h2 => hlip' t (by have := s.isLt; omega)) j
      (Or.inl ⟨by rw [hb0]; omega, by rw [show r.val + (s.val - r.val) = s.val by omega]; omega⟩)
    exact ⟨t, by have := s.isLt; omega, h3⟩
  have hβ := isBlockMap_natBlock b hlt hlip' hsurj
  have hblock : ∀ (v : Fin (b s + 1)) (S : Set X), (∀ t : Fin n, b t = v → E.link t ⊆ S) →
      (E.ofBlocks _ hβ).link v ⊆ S := by
    intro v S hS x hx
    rw [natBlock_link] at hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact hS t ht hxt
  have hρ : ∀ t : Fin n, chainRho hcr.1 t = (hcr.1.minIdx t : ℕ) := fun t => by simp [chainRho]
  have hσ : ∀ t : Fin n, chainSig hcr.1 t = (hcr.1.maxIdx t : ℕ) := fun t => by simp [chainSig]
  have hblk : ∀ v, ∃ j : ℕ, (E.ofBlocks _ hβ).link v ⊆ D.unionRange j 2 := by
    intro v
    obtain ⟨j, hj⟩ := hwid v.val
    refine ⟨j, hblock v _ fun t htv => ?_⟩
    obtain ⟨h1, h2⟩ := hj t (Nat.zero_le _) (by omega) htv
    have hw := hB.wid t t.isLt
    have e1 := hρ t
    have e2 := hσ t
    rw [e1, e2] at hw
    rw [e2] at h1
    rw [e1] at h2
    by_cases hjr : j ≤ (hcr.1.minIdx t : ℕ)
    · exact (minIdx_subset hcr.1 t).trans (link_subset_unionRange D _ (by omega) (by omega))
    · exact (maxIdx_subset hcr.1 t).trans (link_subset_unionRange D _ (by omega) (by omega))
  exact ⟨b s + 1, natBlock b hlt, hβ, by simp [natBlock, hb0], by simp [natBlock],
    onlyIn_of_onlyM hcr hlt hβ hblk r hor, onlyIn_of_onlyM hcr hlt hβ hblk s hos, hblk⟩

end HPC.Fold
