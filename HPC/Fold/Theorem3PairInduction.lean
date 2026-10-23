import HPC.Fold.Theorem3PairModel

/-!
# Batch 124, item 1: Bing's induction for the pair form (special case, general case, main theorem)

COMMISSION-batch124.md, Q1. Continuation of `HPC/Fold/Theorem3PairModel.lean`: the special case
for a pair (`special_caseZ`, with the second explicit grouping at `r = 5`, `special_fiveZ`), the
general case (`general_caseZ`) and the main theorem `pair_main`. Nothing here is `sorry`.
-/

namespace HPC.Fold.Recon122

/-! ## The special case with a pair -/

/-- The universal statement for pairs at `K` coarse links: two equal or adjacent fine links lying
in a common coarse link can both be put in the first block. -/
def PairMain (K : ℕ) : Prop :=
  ∀ (n : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (i i' : ℕ), BHyp n K ρ σ T → i < n → i' < n →
    i ≤ i' + 1 → i' ≤ i + 1 → CommonC ρ σ i i' → BConclZ n K ρ σ T (pairZ i i')

/-- The hypotheses of the special case for a pair: only the end links meet the extreme coarse
links, the first meets `e₁` and the last `e_r`, the pair is interior, and the pair is neither
entirely in `e₁ + e₂` nor entirely in `e_{r−1} + e_r`. -/
structure SpecialZ (n K : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (i i' : ℕ) : Prop where
  hK : 5 ≤ K
  h0 : T 0 0
  hl : T (n - 1) (K - 1)
  hint : ∀ t, 0 < t → t + 1 < n → ¬ T t 0 ∧ ¬ T t (K - 1)
  hi0 : 0 < i
  hi'0 : 0 < i'
  hin : i + 1 < n
  hin' : i' + 1 < n
  adj1 : i ≤ i' + 1
  adj2 : i' ≤ i + 1
  hc : CommonC ρ σ i i'
  mixlo : ¬ (ρ i ≤ 1 ∧ ρ i' ≤ 1)
  mixhi : ¬ (K ≤ σ i + 2 ∧ K ≤ σ i' + 2)

theorem SpecialZ.facts {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i i' : ℕ}
    (h : BHyp n K ρ σ T) (hs : SpecialZ n K ρ σ T i i') :
    (∀ t, t < n → 1 ≤ ρ t ∧ σ t + 2 ≤ K) ∧ σ 0 ≤ 1 ∧ K ≤ ρ (n - 1) + 2 ∧
      2 ≤ σ i ∧ 2 ≤ σ i' ∧ ρ i + 3 ≤ K ∧ ρ i' + 3 ≤ K := by
  have hK := hs.hK
  have hn : 2 < n := by have := hs.hi0; have := hs.hin; omega
  have hσ0 := (h.poss 0 (by omega) 0 hs.h0).1
  have hρl := (h.poss (n - 1) (by omega) _ hs.hl).2
  have hint := hs.hint
  have hlev : ∀ t, t < n → 1 ≤ ρ t ∧ σ t + 2 ≤ K := by
    intro t ht
    refine ⟨?_, ?_⟩
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
  obtain ⟨c, c1, c2, c3, c4⟩ := hs.hc
  have := hs.mixlo; have := hs.mixhi
  have := h.le i (by have := hs.hin; omega); have := h.le i' (by have := hs.hin'; omega)
  have := h.lt i (by have := hs.hin; omega); have := h.lt i' (by have := hs.hin'; omega)
  refine ⟨hlev, hσ0, by omega, by omega, by omega, by omega, by omega⟩

theorem SpecialZ.revflip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i i' : ℕ}
    (h : BHyp n K ρ σ T) (hs : SpecialZ n K ρ σ T i i') :
    SpecialZ n K (fun t => K - 1 - σ (n - 1 - t)) (fun t => K - 1 - ρ (n - 1 - t))
      (fun t j => j ≤ K - 1 ∧ T (n - 1 - t) (K - 1 - j)) (n - 1 - i) (n - 1 - i') := by
  obtain ⟨hK, h0, hl, hint, hi0, hi'0, hin, hin', adj1, adj2, hc, mixlo, mixhi⟩ := hs
  have hσi := h.lt i (by omega); have hσi' := h.lt i' (by omega)
  have := h.le i (by omega); have := h.le i' (by omega)
  refine ⟨hK, ⟨by omega, ?_⟩, ⟨le_rfl, ?_⟩, fun t h1 h2 => ⟨?_, ?_⟩, by omega, by omega,
    by omega, by omega, by omega, by omega,
    commonC_revflip ⟨_, hc.choose_spec⟩ hσi hσi' (by omega) (by omega), ?_, ?_⟩
  · simpa [show K - 1 - 0 = K - 1 by omega] using hl
  · simpa [show K - 1 - (K - 1) = 0 by omega] using h0
  · rintro ⟨_, hT⟩
    exact (hint (n - 1 - t) (by omega) (by omega)).2 (by simpa using hT)
  · rintro ⟨_, hT⟩
    exact (hint (n - 1 - t) (by omega) (by omega)).1
      (by simpa [show K - 1 - (K - 1) = 0 by omega] using hT)
  · simp only [show n - 1 - (n - 1 - i) = i by omega, show n - 1 - (n - 1 - i') = i' by omega]
    omega
  · simp only [show n - 1 - (n - 1 - i) = i by omega, show n - 1 - (n - 1 - i') = i' by omega]
    omega

/-- **The special case at `r = 5`, forward grouping**: given a link `d_k` after the pair, not the
last, in `e₁ + e₂`: up to `d_k` the links in `e₁ + e₂` other than the pair (second block) and the
rest (first block, in `e₃ + e₄`; the links of the pair lying in `e₂ ∩ e₃` go here), then the links
after `d_k` one by one. -/
theorem special_fiveZ_fwd {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i i' : ℕ}
    (h : BHyp n K ρ σ T) (hs : SpecialZ n K ρ σ T i i') (hK : K = 5) {k : ℕ} (hik : i < k)
    (hi'k : i' < k) (hk : k + 1 < n) (hρk : ρ k ≤ 1) : BConclZ n K ρ σ T (pairZ i i') := by
  classical
  obtain ⟨hlev, hσ0, hρl, hσi, hσi', hρi, hρi'⟩ := hs.facts h
  have hi0 := hs.hi0; have hi'0 := hs.hi'0
  refine ⟨fun t => if t ≤ k then (if ρ t ≤ 1 ∧ t ≠ i ∧ t ≠ i' then 1 else 0) else t - k + 1,
    fun x _ hx => ?_, ⟨fun t _ ht => ?_, fun v => ?_⟩, fun e he hee _ => ?_⟩
  · rcases hx with rfl | rfl
    · simp [show x ≤ k by omega]
    · simp [show x ≤ k by omega]
  · simp only
    by_cases htk : t = k
    · subst htk; simp [hρk, show t ≠ i by omega, show t ≠ i' by omega]
    · split_ifs <;> omega
  · refine ⟨if v = 0 then 2 else if v = 1 then 0 else ρ (v + k - 1), fun t _ ht hv => ?_⟩
    have := h.le t (by omega); have := hlev t (by omega)
    simp only at hv
    by_cases hti : t = i
    · subst hti; split_ifs at hv ⊢ <;> omega
    · by_cases hti' : t = i'
      · subst hti'; split_ifs at hv ⊢ <;> omega
      · split_ifs at hv ⊢ <;> try omega
        all_goals (subst hv; rw [show t - k + 1 + k - 1 = t by omega]; omega)
  · rcases hee with rfl | rfl
    · left; intro t ht hte
      have := h.le 0 he
      simp only [show (0 : ℕ) ≤ k by omega, if_true, show ρ 0 ≤ 1 by omega,
        show (0 : ℕ) ≠ i by omega, show (0 : ℕ) ≠ i' by omega, ne_eq, not_false_eq_true,
        and_self, if_true] at hte
      split_ifs at hte <;> omega
    · right; intro t ht hte
      simp only [show ¬ n - 1 ≤ k by omega, if_false] at hte
      have := h.le t ht
      split_ifs at hte <;> try omega
      have : t = n - 1 := by omega
      subst this; omega

/-- **The special case at `r = 5` with a pair**: the forward grouping if some link after the pair
lies in `e₂` (`d_{r'}` of crookedness), its mirror image if some link before the pair lies in `e₄`
(`d_r`); one of the two always happens, because `d_r` (in `e₄`) precedes `d_{r'}` (in `e₂`) and two
adjacent links cannot lie in `e₄` and in `e₂`. -/
theorem special_fiveZ {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {i i' : ℕ}
    (h : BHyp n K ρ σ T) (hs : SpecialZ n K ρ σ T i i') (hK : K = 5) :
    BConclZ n K ρ σ T (pairZ i i') := by
  obtain ⟨hlev, hσ0, hρl, hσi, hσi', hρi, hρi'⟩ := hs.facts h
  have hi0 := hs.hi0; have hi'0 := hs.hi'0; have hin := hs.hin; have hin' := hs.hin'
  have adj1 := hs.adj1; have adj2 := hs.adj2
  obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
    h.crk 0 (n - 1) (by omega) (by omega) 0 (K - 1) hs.h0 hs.hl (by omega)
  by_cases hfw : i < r' ∧ i' < r'
  · exact special_fiveZ_fwd h hs hK hfw.1 hfw.2 (by omega) (by omega)
  · by_cases hbw : r < i ∧ r < i'
    · apply BConclZ.of_revflip h (by omega)
      refine BConclZ.mono (fun x hx hZ => pairZ_rev hx hZ (by omega) (by omega))
        (special_fiveZ_fwd h.revflip (hs.revflip h) hK (k := n - 1 - r) (by omega) (by omega)
          (by omega) ?_)
      simp only [show n - 1 - (n - 1 - r) = r by omega]; omega
    · exfalso
      have hrr : r + 1 = r' := by omega
      have := h.adj r (by omega)
      rw [hrr] at this
      omega

/-- **Branch `d_i ∈ D(1, h)` of the special case for a pair** (`r ≥ 6`; the pair may contain
`d_h`). -/
theorem special_branch1Z {K : ℕ} (IH : ∀ K', K' < K → PairMain K') {n : ℕ} {ρ σ : ℕ → ℕ}
    {T : ℕ → ℕ → Prop} {i i' : ℕ} (h : BHyp n K ρ σ T) (hs : SpecialZ n K ρ σ T i i')
    (hK : 6 ≤ K) {hh k : ℕ} (hih : i ≤ hh) (hi'h : i' ≤ hh) (hhk : hh < k) (hk : k < n)
    (hht : ρ hh ≤ K - 2 ∧ K - 2 ≤ σ hh) (hkb : ρ k ≤ 1) : BConclZ n K ρ σ T (pairZ i i') := by
  obtain ⟨hlev, hσ0, hρl, -⟩ := hs.facts h
  have adj1 := hs.adj1; have adj2 := hs.adj2
  have hkn : k + 1 < n := by
    by_contra hc
    have : k = n - 1 := by omega
    subst this; omega
  have hin' : ∀ t, 0 ≤ t → t ≤ hh → 0 ≤ ρ t ∧ σ t ≤ K - 2 :=
    fun t _ ht => ⟨Nat.zero_le _, by have := hlev t (by omega); omega⟩
  have hsub := h.sub (p := 0) (q := hh) (lo := 0) (hi := K - 2) (by omega) (by omega) hin'
  have hc := IH (K - 2 - 0 + 1) (by omega) _ _ _ _ (i - 0) (i' - 0) hsub (by omega) (by omega)
    (by omega) (by omega) (commonC_sub hs.hc (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      (Nat.zero_le _))
  obtain ⟨H, hH0, hHc, hHe⟩ := BConclZ.sub_abs (Z := pairZ i i') (by omega) hin'
    (fun t _ ht => h.le t (by omega))
    (hc.mono (fun x _ hx => pairZ_shift (Nat.zero_le _) (Nat.zero_le _) hx))
  have hHh : ∀ t, 0 ≤ t → t ≤ hh → H t = H hh → 2 ≤ ρ t ∧ K ≤ σ t + 3 := by
    rcases hHe hh (Or.inr rfl) (Or.inr (h.cont hh (by omega) _ hht.1 hht.2)) with hb | hb
    · have := hb hh (by omega) le_rfl rfl; have := h.wid hh (by omega); omega
    · intro t h1 h2 h3; have := hb t h1 h2 h3; have := h.wid t (by omega); omega
  have hH0b : ∀ t, 0 ≤ t → t ≤ hh → H t = H 0 → ρ t ≤ 1 := by
    rcases hHe 0 (Or.inl rfl) (Or.inl hs.h0) with hb | hb
    · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
    · have := hb 0 le_rfl (by omega) rfl; omega
  refine cutF_conclZ h (by omega) hlev (by have := h.le 0 (by omega); omega) hρl H
    (Nat.zero_le _) hhk.le hkn hkb (fun x hx hZ => ?_) hHc hHh
    (fun h' => absurd h' (lt_irrefl 0)) le_rfl (fun _ _ => hH0b)
  have hxh : x ≤ hh := by unfold pairZ at hZ; omega
  exact ⟨Nat.zero_le _, hxh, hH0 x (Nat.zero_le _) hxh hZ⟩

/-- **Branch `d_i ∈ D(h, k)` of the special case for a pair** (`r ≥ 6`; the pair may contain `d_h`
or `d_k`). -/
theorem special_middleZ {K : ℕ} (IH : ∀ K', K' < K → PairMain K') {n : ℕ} {ρ σ : ℕ → ℕ}
    {T : ℕ → ℕ → Prop} {i i' : ℕ} (h : BHyp n K ρ σ T) (hs : SpecialZ n K ρ σ T i i')
    (hK : 6 ≤ K) {hh k : ℕ} (hhi : hh ≤ i) (hhi' : hh ≤ i') (hik : i ≤ k) (hi'k : i' ≤ k)
    (hhk : hh < k) (hk : k < n) (hht : ρ hh ≤ K - 2 ∧ K - 2 ≤ σ hh)
    (hkb : ρ k ≤ 1 ∧ 1 ≤ σ k) : BConclZ n K ρ σ T (pairZ i i') := by
  obtain ⟨hlev, hσ0, hρl, -⟩ := hs.facts h
  have adj1 := hs.adj1; have adj2 := hs.adj2
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
  have hc := IH (K - 2 - 1 + 1) (by omega) _ _ _ _ (i - hh) (i' - hh) hsub (by omega) (by omega)
    (by omega) (by omega) (commonC_sub hs.hc hhi hhi' (hlev i (by omega)).1 (hlev i' (by omega)).1)
  obtain ⟨H, hH0, hHc, hHe⟩ := BConclZ.sub_abs (Z := pairZ i i') (by omega) hin'
    (fun t _ ht => h.le t (by omega)) (hc.mono (fun x _ hx => pairZ_shift hhi hhi' hx))
  have hHh : ∀ t, hh ≤ t → t ≤ k → H t = H hh → 2 ≤ ρ t ∧ K ≤ σ t + 3 := by
    rcases hHe hh (Or.inl rfl) (Or.inr (h.cont hh (by omega) _ hht.1 hht.2)) with hb | hb
    · have := hb hh le_rfl (by omega) rfl; have := h.wid hh (by omega); omega
    · intro t h1 h2 h3; have := hb t h1 h2 h3; have := h.wid t (by omega); omega
  have hHk : ∀ t, hh ≤ t → t ≤ k → H t = H k → ρ t ≤ 2 := by
    rcases hHe k (Or.inr rfl) (Or.inl (h.cont k (by omega) _ hkb.1 hkb.2)) with hb | hb
    · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
    · have := hb k (by omega) le_rfl rfl; have := h.wid k (by omega); omega
  have hZin : ∀ x, x < n → pairZ i i' x → hh ≤ x ∧ x ≤ k ∧ H x = 0 := by
    intro x _ hZ
    have : hh ≤ x ∧ x ≤ k := by unfold pairZ at hZ; omega
    exact ⟨this.1, this.2, hH0 x this.1 this.2 hZ⟩
  by_cases hab : H hh ≤ H k
  · exact cutF_conclZ h (by omega) hlev (by have := h.le 0 (by omega); omega) hρl H (by omega)
      le_rfl hkn hkb.1 hZin hHc hHh (fun _ => le_rfl) hab (fun h' => absurd h' (by omega))
  · apply BConclZ.of_revflip h (by omega)
    refine cutF_conclZ h.revflip (by omega) (fun t ht => ?_) ?_ ?_ (fun t => H (n - 1 - t))
      (p := n - 1 - k) (q := n - 1 - hh) (k := n - 1 - hh) (a := H k) (by omega) le_rfl
      (by omega) ?_ (fun x hx hZ => ?_)
      (PCons.revflip hHc (by omega) (by omega)
        (fun t _ ht => ⟨h.le t (by omega), h.lt t (by omega)⟩))
      (fun t h1 h2 h3 => ?_) (fun _ => ?_) ?_ (fun h' => absurd h' (by omega))
    · have := hlev (n - 1 - t) (by omega); have := h.le (n - 1 - t) (by omega)
      omega
    · have := h.le (n - 1) (by omega); show K - 1 - σ (n - 1) ≤ 1; omega
    · simp only [show n - 1 - (n - 1) = 0 by omega]; omega
    · simp only [show n - 1 - (n - 1 - hh) = hh by omega]; omega
    · obtain ⟨h1, h2, h3⟩ := hZin (n - 1 - x) (by omega) hZ
      refine ⟨by omega, by omega, ?_⟩
      simpa using h3
    · have := hHk (n - 1 - t) (by omega) (by omega) h3
      have := h.wid (n - 1 - t) (by omega)
      omega
    · show H k ≤ H (n - 1 - (n - 1 - k)); rw [show n - 1 - (n - 1 - k) = k by omega]
    · simp only [show n - 1 - (n - 1 - hh) = hh by omega]; omega

/-- **The special case for a pair**, given the pair form for fewer coarse links. -/
theorem special_caseZ {K : ℕ} (IH : ∀ K', K' < K → PairMain K') {n : ℕ} {ρ σ : ℕ → ℕ}
    {T : ℕ → ℕ → Prop} {i i' : ℕ} (h : BHyp n K ρ σ T) (hs : SpecialZ n K ρ σ T i i') :
    BConclZ n K ρ σ T (pairZ i i') := by
  obtain ⟨hlev, hσ0, hρl, hσi, hσi', hρi, hρi'⟩ := hs.facts h
  have hK := hs.hK
  have hi0 := hs.hi0; have hi'0 := hs.hi'0; have hin := hs.hin; have hin' := hs.hin'
  have adj1 := hs.adj1; have adj2 := hs.adj2
  obtain ⟨r, r', h1, h2, h3, h4, h5, h6, h7⟩ :=
    h.crk 0 (n - 1) (by omega) (by omega) 0 (K - 1) hs.h0 hs.hl (by omega)
  have hsR := hs.revflip h
  rcases Nat.lt_or_ge K 6 with hK5 | hK6
  · exact special_fiveZ h hs (by omega)
  · by_cases hir : i ≤ r ∧ i' ≤ r
    · exact special_branch1Z IH h hs hK6 hir.1 hir.2 h2 (by omega) ⟨by omega, by omega⟩ (by omega)
    · by_cases hr'i : r' ≤ i ∧ r' ≤ i'
      · apply BConclZ.of_revflip h (by omega)
        refine BConclZ.mono (fun x hx hZ => pairZ_rev hx hZ (by omega) (by omega))
          (special_branch1Z IH h.revflip hsR hK6
            (hh := n - 1 - r') (k := n - 1 - r) (by omega) (by omega) (by omega) (by omega) ?_ ?_)
        · simp only [show n - 1 - (n - 1 - r') = r' by omega]
          have := h.le r' (by omega); omega
        · simp only [show n - 1 - (n - 1 - r) = r by omega]; omega
      · exact special_middleZ IH h hs hK6 (hh := r) (k := r') (by omega) (by omega) (by omega)
          (by omega) h2 (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

/-! ## The general case and the main theorem -/

/-- **The general case for a pair** (neither link meets `e₁` or `e_r`, `r ≥ 5`): Bing's `D(h, k)`
around `d_i` contains `d_{i'}`, `H` comes from the pair form for fewer coarse links or from the
special case, and `genF` keeps both links in the first block. -/
theorem general_caseZ {K : ℕ} (IH : ∀ K', K' < K → PairMain K') {n : ℕ} {ρ σ : ℕ → ℕ}
    {T : ℕ → ℕ → Prop} {i i' : ℕ} (h : BHyp n K ρ σ T) (hi : i < n) (hi' : i' < n)
    (adj1 : i ≤ i' + 1) (adj2 : i' ≤ i + 1) (hcc : CommonC ρ σ i i') (hK : 5 ≤ K)
    (hx : ¬ T i 0 ∧ ¬ T i (K - 1) ∧ ¬ T i' 0 ∧ ¬ T i' (K - 1))
    (mixlo : ¬ (ρ i ≤ 1 ∧ ρ i' ≤ 1)) (mixhi : ¬ (K ≤ σ i + 2 ∧ K ≤ σ i' + 2)) :
    BConclZ n K ρ σ T (pairZ i i') := by
  classical
  set ext : ℕ → Prop := fun t => T t 0 ∨ T t (K - 1) with hext
  have hiext : ¬ ext i := by
    rintro (hT | hT)
    · exact hx.1 hT
    · exact hx.2.1 hT
  have hi'ext : ¬ ext i' := by
    rintro (hT | hT)
    · exact hx.2.2.1 hT
    · exact hx.2.2.2 hT
  obtain ⟨hh, hh1, hh2, hh3⟩ := exists_left_end ext i
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_right_end ext hi
  have hhi' : hh ≤ i' := by
    by_contra hc
    have e : hh = i := by omega
    exact hiext (e ▸ hh2 (by omega))
  have hi'k : i' ≤ k := by
    by_contra hc
    have e : k = i := by omega
    exact hiext (e ▸ hk3 (by omega))
  have hint : ∀ t, hh < t → t < k → ¬ T t 0 ∧ ¬ T t (K - 1) := by
    intro t h1 h2
    have : ¬ ext t := by
      rcases Nat.lt_trichotomy t i with e | e | e
      · exact hh3 t h1 e
      · rw [e]; exact hiext
      · exact hk4 t e h2
    exact ⟨fun h' => this (Or.inl h'), fun h' => this (Or.inr h')⟩
  have hZin : ∀ x, x < n → pairZ i i' x → hh ≤ x ∧ x ≤ k := by
    intro x _ hZ; unfold pairZ at hZ; omega
  -- `H`: a consolidation of `D(h, k)` with both links of the pair in its first block
  obtain ⟨H, hH0, hHc, hHe0, hHe1⟩ : ∃ H : ℕ → ℕ,
      (∀ x, hh ≤ x → x ≤ k → pairZ i i' x → H x = 0) ∧ PCons hh k ρ σ H ∧
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
      have hc := IH (K - 1 - 1 + 1) (by omega) _ _ _ _ (i - hh) (i' - hh) hsub (by omega)
        (by omega) (by omega) (by omega)
        (commonC_sub hcc hh1 hhi' (hin i hh1 hk1).1 (hin i' hhi' hi'k).1)
      obtain ⟨H, hH0, hHc, hHe⟩ := BConclZ.sub_abs (Z := pairZ i i') (by omega) hin
        (fun t _ ht => h.le t (by omega)) (hc.mono (fun x _ hx => pairZ_shift hh1 hhi' hx))
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
        have hc := IH (K - 2 - 0 + 1) (by omega) _ _ _ _ (i - hh) (i' - hh) hsub (by omega)
          (by omega) (by omega) (by omega)
          (commonC_sub hcc hh1 hhi' (Nat.zero_le _) (Nat.zero_le _))
        obtain ⟨H, hH0, hHc, hHe⟩ := BConclZ.sub_abs (Z := pairZ i i') (by omega) hin
          (fun t _ ht => h.le t (by omega)) (hc.mono (fun x _ hx => pairZ_shift hh1 hhi' hx))
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
        -- the pair is interior to `D(h, k)`
        have hext_hh : ext hh := by
          rcases e0 with e | e
          · rw [← e]; exact Or.inl hT0
          · rcases e1 with e' | e'
            · rw [← e']; exact Or.inr hT1
            · exfalso; rw [← e'] at e; subst e; exact hne _ (by omega) hT0 hT1
        have hext_k : ext k := by
          rcases e0 with e | e
          · rcases e1 with e' | e'
            · exfalso; rw [← e'] at e; subst e; exact hne _ (by omega) hT0 hT1
            · rw [← e']; exact Or.inr hT1
          · rw [← e]; exact Or.inl hT0
        have hhi : hh < i := by
          by_contra hc
          have e : i = hh := by omega
          exact hiext (by rw [e]; exact hext_hh)
        have hhi'' : hh < i' := by
          by_contra hc
          have e : i' = hh := by omega
          exact hi'ext (by rw [e]; exact hext_hh)
        have hik : i < k := by
          by_contra hc
          have e : i = k := by omega
          exact hiext (by rw [e]; exact hext_k)
        have hi'k' : i' < k := by
          by_contra hc
          have e : i' = k := by omega
          exact hi'ext (by rw [e]; exact hext_k)
        have hin : ∀ t, hh ≤ t → t ≤ k → 0 ≤ ρ t ∧ σ t ≤ K - 1 :=
          fun t _ ht => ⟨Nat.zero_le _, by have := h.lt t (by omega); omega⟩
        have hsub := h.sub (p := hh) (q := k) (lo := 0) (hi := K - 1) (by omega) hk2 hin
        have hcs := commonC_sub hcc hh1 hhi' (lo := 0) (Nat.zero_le _) (Nat.zero_le _)
        have hli := h.lt i hi; have hli' := h.lt i' hi'
        have hle := h.le i hi; have hle' := h.le i' hi'
        have hc : BConclZ (k - hh + 1) (K - 1 - 0 + 1) (fun t => ρ (t + hh) - 0)
            (fun t => σ (t + hh) - 0) (fun t j => j + 0 ≤ K - 1 ∧ T (t + hh) (j + 0))
            (pairZ (i - hh) (i' - hh)) := by
          have hIH : ∀ K', K' < K - 1 - 0 + 1 → PairMain K' := fun K' hK' => IH K' (by omega)
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
            refine special_caseZ hIH hsub ⟨by omega, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, hint',
              by omega, by omega, by omega, by omega, by omega, by omega, hcs, ?_, ?_⟩
            · simpa using hT0
            · rw [show t1 - t0 + 1 - 1 + t0 = t1 by omega,
                show K - 1 - 0 + 1 - 1 + 0 = K - 1 by omega]
              exact hT1
            · simp only [Nat.sub_add_cancel hh1, Nat.sub_add_cancel hhi', Nat.sub_zero]
              exact mixlo
            · simp only [Nat.sub_add_cancel hh1, Nat.sub_add_cancel hhi', Nat.sub_zero]
              omega
          · -- `d_h` meets `e_r`, `d_k` meets `e₁`: mirror
            subst e0; subst e1
            have hsubF := hsub.flip
            refine BConclZ.of_flip hsub (by omega) (special_caseZ hIH hsubF
              ⟨by omega, ⟨by omega, ⟨by omega, ?_⟩⟩, ⟨le_rfl, ⟨by omega, ?_⟩⟩,
                fun t h1 h2 => ⟨fun h' => ?_, fun h' => ?_⟩, by omega, by omega, by omega,
                by omega, by omega, by omega,
                commonC_flip hcs (by simp only [Nat.sub_add_cancel hh1]; omega)
                  (by simp only [Nat.sub_add_cancel hhi']; omega), ?_, ?_⟩)
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
            · simp only [Nat.sub_add_cancel hh1, Nat.sub_add_cancel hhi', Nat.sub_zero]
              omega
            · simp only [Nat.sub_add_cancel hh1, Nat.sub_add_cancel hhi', Nat.sub_zero]
              omega
          · subst e0; exact absurd hT1 (fun h' => hne _ (by omega) hT0 (e1 ▸ h'))
        obtain ⟨H, hH0, hHc, hHe⟩ := BConclZ.sub_abs (Z := pairZ i i') (by omega) hin
          (fun t _ ht => h.le t (by omega)) (hc.mono (fun x _ hx => pairZ_shift hh1 hhi' hx))
        refine ⟨H, hH0, hHc, fun e he hT => ?_, fun e he hT => ?_⟩
        · have := h.poss e (by omega) 0 hT
          rcases hHe e he (Or.inl hT) with hb | hb
          · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
          · have := hb e (by omega) (by omega) rfl; omega
        · have := h.poss e (by omega) _ hT
          rcases hHe e he (Or.inr hT) with hb | hb
          · have := hb e (by omega) (by omega) rfl; omega
          · intro t h1 h2 h3; have := hb t h1 h2 h3; omega
  have hZ : ∀ x, x < n → pairZ i i' x → hh ≤ x ∧ x ≤ k ∧ H x = 0 := by
    intro x hx hZx
    obtain ⟨h1, h2⟩ := hZin x hx hZx
    exact ⟨h1, h2, hH0 x h1 h2 hZx⟩
  -- the construction
  by_cases hnone : ¬ ext hh ∧ ¬ ext k
  · -- `D(h, k) = D`: `H` itself
    have hh0 : hh = 0 := by
      by_contra hc; exact hnone.1 (hh2 (by omega))
    have hkn : k = n - 1 := by
      by_contra hc; exact hnone.2 (hk3 (by omega))
    subst hh0; subst hkn
    refine ⟨H, fun x hx hZx => (hZ x hx hZx).2.2, hHc, fun e he hee hT => ?_⟩
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
    · exact genF_conclZ h hK (by omega) hk2 hh2 hk3 H hZ hHc he rfl (hHe0 e he hTe) hmin
    · -- mirror
      refine BConclZ.of_flip h (by omega) (genF_conclZ h.flip hK (by omega) hk2 (fun hp => ?_)
        (fun hq => ?_) H hZ (hHc.flip (fun t _ ht => ⟨h.le t (by omega), h.lt t (by omega)⟩))
        he rfl (fun t h1 h2 h3 => ?_) (fun e' he' hT' => hmin e' he' ?_))
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

/-- **The pair form of Bing's Theorem 3, in the model**: two equal or adjacent fine links lying in
a common coarse link have a consolidation as in `bing_main` with both in the first block. -/
theorem pair_main : ∀ K, PairMain K := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K IH =>
    intro n ρ σ T i i' h hi hi' a1 a2 hc
    by_cases hK : K ≤ 4
    · exact zbase h hi hi' hK hc
    · by_cases hlo : ρ i ≤ 1 ∧ ρ i' ≤ 1
      · exact zlow h (by omega) (by omega) (fun x _ hx => by
          rcases hx with rfl | rfl
          exacts [hlo.1, hlo.2])
      · by_cases hhi : K ≤ σ i + 2 ∧ K ≤ σ i' + 2
        · exact zhigh h (by omega) (by omega) (fun x _ hx => by
            rcases hx with rfl | rfl
            exacts [hhi.1, hhi.2])
        · obtain ⟨c, c1, c2, c3, c4⟩ := hc
          have := h.le i hi; have := h.le i' hi'
          refine general_caseZ IH h hi hi' a1 a2 ⟨c, c1, c2, c3, c4⟩ (by omega)
            ⟨fun hT => ?_, fun hT => ?_, fun hT => ?_, fun hT => ?_⟩ hlo hhi
          · have := h.poss i hi 0 hT; omega
          · have := h.poss i hi _ hT; omega
          · have := h.poss i' hi' 0 hT; omega
          · have := h.poss i' hi' _ hT; omega

end HPC.Fold.Recon122
