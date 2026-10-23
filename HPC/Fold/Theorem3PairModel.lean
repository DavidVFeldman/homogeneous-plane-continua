import HPC.Fold.Recon122General

/-!
# Batch 124, item 1: the pair form of Bing's Theorem 3 in the model of batch 122

COMMISSION-batch124.md, Q1. Bing's induction (`bing_main`) with the basepoint `d_i` replaced by a
set `Z` of fine links that must all lie in the first block (`BConclZ`); for a pair of adjacent fine
links lying in a common coarse link this is `pair_main`.

What changes against batch 122:

* the base case `K ≤ 4` needs a second grouping (by `σ` instead of `ρ`) when the pair straddles the
  level `ρ = 1 | 2` (`zbase`);
* the cases "`d_i ⊆ e₁ + e₂`" / "`d_i ⊆ e_{m−1} + e_m`" are taken only when *both* links of the pair
  are there; otherwise neither link meets `e₁` or `e_m` and the general case applies (with either
  link as the anchor of `D(h, k)`);
* the constructions `genF`, `cutF` already send every link of the first block of `H` to `0`, so
  only the bookkeeping changes (`genF_conclZ`, `cutF_specZ`);
* the special case at `r = 5` needs a second explicit grouping (the mirror image of
  `special_five`, with the links "in `e_{m−1}`, not `e_{m−2}`" free), and a free choice for the
  links in `e₂ ∩ e₃` (`special_fiveZ`), which is exactly the place COMMISSION-batch124 Q1
  pointed at;
* in the special case for `r ≥ 6` the pair lies in `D(1, h)`, in `D(h, k)` or in `D(k, n)` (closed
  intervals: it may contain `d_h` or `d_k`), and Bing's three branches go through unchanged.

Nothing in this file is `sorry`.
-/

namespace HPC.Fold.Recon122

/-- **Bing's conclusion with a set of basepoints**: a time function with every fine link of `Z`
(below `n`) at time `0`, moving by at most one, every fibre inside two adjacent coarse links, and
Bing's end clause. `BConcl n K ρ σ T i` is the case `Z = {i}`. -/
def BConclZ (n K : ℕ) (ρ σ : ℕ → ℕ) (T : ℕ → ℕ → Prop) (Z : ℕ → Prop) : Prop :=
  ∃ β : ℕ → ℕ, (∀ x, x < n → Z x → β x = 0) ∧ PCons 0 (n - 1) ρ σ β ∧ EndC n K ρ σ T β

theorem BConclZ.mono {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {Z Z' : ℕ → Prop}
    (hZ : ∀ x, x < n → Z' x → Z x) (h : BConclZ n K ρ σ T Z) : BConclZ n K ρ σ T Z' := by
  obtain ⟨β, h0, hc, he⟩ := h
  exact ⟨β, fun x hx hx' => h0 x hx (hZ x hx hx'), hc, he⟩

theorem BConclZ.of_flip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T)
    {Z : ℕ → Prop} (hn : 0 < n)
    (hc : BConclZ n K (fun t => K - 1 - σ t) (fun t => K - 1 - ρ t) (flipT K T) Z) :
    BConclZ n K ρ σ T Z := by
  obtain ⟨β, h0, ⟨hlip, hwid⟩, hend⟩ := hc
  refine ⟨β, h0, ⟨hlip, fun v => ?_⟩, fun e he hee hT => ?_⟩
  · obtain ⟨j, hj⟩ := hwid v
    refine ⟨K - 2 - j, fun t h1 h2 h3 => ?_⟩
    have := hj t h1 h2 h3; simp only at this
    have := h.lt t (by omega); have := h.le t (by omega); omega
  · have hK : 1 ≤ K := by have := h.lt e he; omega
    have hT' : flipT K T e 0 ∨ flipT K T e (K - 1) := by
      rcases hT with hT | hT
      · exact Or.inr ⟨le_rfl, by rwa [show K - 1 - (K - 1) = 0 by omega]⟩
      · exact Or.inl ⟨by omega, by rwa [show K - 1 - 0 = K - 1 by omega]⟩
    rcases hend e he hee hT' with hb | hb
    · right; intro t ht hte; have := hb t ht hte; simp only at this; have := h.lt t ht; omega
    · left; intro t ht hte; have := hb t ht hte; simp only at this
      have := h.lt t ht; have := h.le t ht; omega

theorem BConclZ.of_rev {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {Z : ℕ → Prop}
    (hc : BConclZ n K (fun t => ρ (n - 1 - t)) (fun t => σ (n - 1 - t))
      (fun t j => T (n - 1 - t) j) (fun t => Z (n - 1 - t))) :
    BConclZ n K ρ σ T Z := by
  obtain ⟨β, h0, ⟨hlip, hwid⟩, hend⟩ := hc
  refine ⟨fun t => β (n - 1 - t), fun x hx hZ => ?_, ⟨fun t h1 h2 => ?_, fun v => ?_⟩,
    fun e he hee hT => ?_⟩
  · exact h0 (n - 1 - x) (by omega) (by simpa [show n - 1 - (n - 1 - x) = x by omega] using hZ)
  · have := hlip (n - 1 - (t + 1)) (by omega) (by omega)
    rw [show n - 1 - (t + 1) + 1 = n - 1 - t by omega] at this
    exact ⟨this.2, this.1⟩
  · obtain ⟨j, hj⟩ := hwid v
    refine ⟨j, fun t h1 h2 h3 => ?_⟩
    have := hj (n - 1 - t) (by omega) (by omega) h3
    simpa [show n - 1 - (n - 1 - t) = t by omega] using this
  · have hT' : T (n - 1 - (n - 1 - e)) 0 ∨ T (n - 1 - (n - 1 - e)) (K - 1) := by
      rwa [show n - 1 - (n - 1 - e) = e by omega]
    rcases hend (n - 1 - e) (by omega) (by omega) hT' with hb | hb
    · left; intro t ht hte
      have := hb (n - 1 - t) (by omega) (by simpa using hte)
      simpa [show n - 1 - (n - 1 - t) = t by omega] using this
    · right; intro t ht hte
      have := hb (n - 1 - t) (by omega) (by simpa using hte)
      simpa [show n - 1 - (n - 1 - t) = t by omega] using this

theorem BConclZ.of_revflip {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T)
    {Z : ℕ → Prop} (hn : 0 < n)
    (hc : BConclZ n K (fun t => K - 1 - σ (n - 1 - t)) (fun t => K - 1 - ρ (n - 1 - t))
      (fun t j => j ≤ K - 1 ∧ T (n - 1 - t) (K - 1 - j)) (fun t => Z (n - 1 - t))) :
    BConclZ n K ρ σ T Z :=
  BConclZ.of_rev (BConclZ.of_flip h.rev hn hc)

/-- What the conclusion for a sub-model says about the original links (absolute indices). -/
theorem BConclZ.sub_abs {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {p q lo hi : ℕ} {Z : ℕ → Prop}
    (hpq : p ≤ q)
    (hin : ∀ t, p ≤ t → t ≤ q → lo ≤ ρ t ∧ σ t ≤ hi) (hle : ∀ t, p ≤ t → t ≤ q → ρ t ≤ σ t)
    (hc : BConclZ (q - p + 1) (hi - lo + 1) (fun t => ρ (t + p) - lo) (fun t => σ (t + p) - lo)
      (fun t j => j + lo ≤ hi ∧ T (t + p) (j + lo)) (fun t => Z (t + p))) :
    ∃ H : ℕ → ℕ, (∀ x, p ≤ x → x ≤ q → Z x → H x = 0) ∧ PCons p q ρ σ H ∧
      ∀ e, (e = p ∨ e = q) → (T e lo ∨ T e hi) →
        (∀ t, p ≤ t → t ≤ q → H t = H e → ρ t ≤ lo + 1) ∨
        (∀ t, p ≤ t → t ≤ q → H t = H e → hi ≤ σ t + 1) := by
  obtain ⟨β, h0, ⟨hlip, hwid⟩, hend⟩ := hc
  refine ⟨fun t => β (t - p), fun x h1 h2 hZ => ?_, ⟨fun t h1 h2 => ?_, fun v => ?_⟩,
    fun e he hT => ?_⟩
  · exact h0 (x - p) (by omega) (by simpa [show x - p + p = x by omega] using hZ)
  · have := hlip (t - p) (by omega) (by omega)
    simpa [show t + 1 - p = t - p + 1 by omega] using this
  · obtain ⟨j, hj⟩ := hwid v
    refine ⟨j + lo, fun t h1 h2 h3 => ?_⟩
    have := hj (t - p) (by omega) (by omega) h3
    simp only [show t - p + p = t by omega] at this
    have := hin t h1 h2; have := hle t h1 h2; omega
  · have hlohi : lo ≤ hi := by have := hin p le_rfl hpq; have := hle p le_rfl hpq; omega
    have hT' : ((e - p) = 0 ∨ e - p = q - p + 1 - 1) := by omega
    have hT'' : ((0 + lo ≤ hi ∧ T (e - p + p) (0 + lo)) ∨
        (hi - lo + 1 - 1 + lo ≤ hi ∧ T (e - p + p) (hi - lo + 1 - 1 + lo))) := by
      rw [show e - p + p = e by omega, show 0 + lo = lo by omega,
        show hi - lo + 1 - 1 + lo = hi by omega]
      rcases hT with hT | hT
      · exact Or.inl ⟨hlohi, hT⟩
      · exact Or.inr ⟨le_rfl, hT⟩
    rcases hend (e - p) (by omega) hT' hT'' with hb | hb
    · left; intro t h1 h2 h3
      have := hb (t - p) (by omega) h3
      simp only [show t - p + p = t by omega] at this; omega
    · right; intro t h1 h2 h3
      have := hb (t - p) (by omega) h3
      simp only [show t - p + p = t by omega] at this; have := hle t h1 h2
      have := hin t h1 h2; omega

/-- The two links `i, i'` (equal or adjacent) lie in a common coarse link. -/
def CommonC (ρ σ : ℕ → ℕ) (i i' : ℕ) : Prop :=
  ∃ c, ρ i ≤ c ∧ c ≤ σ i ∧ ρ i' ≤ c ∧ c ≤ σ i'

/-- The pair as a set of basepoints. -/
def pairZ (i i' : ℕ) : ℕ → Prop := fun x => x = i ∨ x = i'

/-! ## The base case and the two end groups -/

/-- **Base case** `K ≤ 4` for a pair: the links in `e₁ + e₂` and the others (as in
`bconcl_base`), or, when the pair straddles, the links in `e₁` not `e₂` and the others. -/
theorem zbase {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {i i' : ℕ}
    (hi : i < n) (hi' : i' < n) (hK : K ≤ 4) (hc : CommonC ρ σ i i') :
    BConclZ n K ρ σ T (pairZ i i') := by
  classical
  obtain ⟨c, c1, c2, c3, c4⟩ := hc
  by_cases hρ : (ρ i ≤ 1 ↔ ρ i' ≤ 1)
  · refine ⟨fun t => if (ρ t ≤ 1 ↔ ρ i ≤ 1) then 0 else 1, fun x _ hx => ?_,
      ⟨fun t _ _ => ?_, fun v => ?_⟩, fun e he _ _ => ?_⟩
    · rcases hx with rfl | rfl
      · simp
      · simp only [ite_eq_left_iff]; intro h'; exact absurd hρ.symm h'
    · constructor <;> simp only <;> split_ifs <;> omega
    · refine ⟨if (v = 0 ↔ ρ i ≤ 1) then 0 else 2, fun t _ ht hv => ?_⟩
      have := h.le t (by omega); have := h.lt t (by omega)
      subst hv
      by_cases h1 : ρ t ≤ 1 <;> by_cases h2 : ρ i ≤ 1 <;> simp [h1, h2] <;> omega
    · by_cases he1 : ρ e ≤ 1
      · left; intro t ht hte
        by_contra hc
        by_cases h2 : ρ i ≤ 1 <;> simp [he1, hc, h2] at hte
      · right; intro t ht hte
        have := h.le t ht
        by_cases h1 : ρ t ≤ 1
        · by_cases h2 : ρ i ≤ 1 <;> simp [he1, h1, h2] at hte
        · omega
  · -- the pair straddles: both links have `σ ≥ 2`
    have hσi : 2 ≤ σ i := by
      have := h.le i hi; have := h.le i' hi'; have := h.wid i hi; have := h.wid i' hi'; omega
    have hσi' : 2 ≤ σ i' := by
      have := h.le i hi; have := h.le i' hi'; have := h.wid i hi; have := h.wid i' hi'; omega
    refine ⟨fun t => if σ t ≤ 1 then 1 else 0, fun x _ hx => ?_,
      ⟨fun t _ _ => ?_, fun v => ?_⟩, fun e he _ _ => ?_⟩
    · rcases hx with rfl | rfl
      · simp; omega
      · simp; omega
    · constructor <;> simp only <;> split_ifs <;> omega
    · refine ⟨if v = 1 then 0 else 2, fun t _ ht hv => ?_⟩
      have := h.le t (by omega); have := h.lt t (by omega)
      subst hv
      by_cases h1 : σ t ≤ 1 <;> simp [h1] <;> omega
    · by_cases he1 : σ e ≤ 1
      · left; intro t ht hte
        have := h.le t ht
        by_cases h1 : σ t ≤ 1
        · omega
        · simp [he1, h1] at hte
      · right; intro t ht hte
        by_cases h1 : σ t ≤ 1
        · simp [he1, h1] at hte
        · omega

/-- **Both links in `e₁ + e₂`**: the groups by the least level (`bconcl_low`). -/
theorem zlow {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {Z : ℕ → Prop}
    (hn : 0 < n) (hK : 4 ≤ K) (hZ : ∀ x, x < n → Z x → ρ x ≤ 1) : BConclZ n K ρ σ T Z := by
  refine ⟨fun t => min (ρ t - 1) (K - 3), fun x hx hZx => by have := hZ x hx hZx; simp; omega,
    ⟨fun t _ ht => ?_, fun v => ?_⟩, fun e he _ hT => ?_⟩
  · have := h.adj t (by omega); have := h.le t (by omega); have := h.le (t + 1) (by omega)
    simp only; omega
  · refine ⟨if v = 0 then 0 else if v < K - 3 then v + 1 else K - 2, fun t _ ht hv => ?_⟩
    have := h.le t (by omega); have := h.lt t (by omega)
    simp only at hv; subst hv
    split_ifs <;> omega
  · rcases hT with hT | hT
    · have := h.poss e he 0 hT; have := h.le e he
      left; intro t ht hte; simp only at hte; omega
    · have := h.poss e he _ hT; have := h.le e he
      right; intro t ht hte; simp only at hte; have := h.le t ht; omega

/-- **Both links in `e_{m−1} + e_m`**, by the mirror image. -/
theorem zhigh {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} (h : BHyp n K ρ σ T) {Z : ℕ → Prop}
    (hn : 0 < n) (hK : 4 ≤ K) (hZ : ∀ x, x < n → Z x → K ≤ σ x + 2) : BConclZ n K ρ σ T Z :=
  BConclZ.of_flip h hn (zlow h.flip hn hK (fun x hx hZx => by
    have := hZ x hx hZx; show K - 1 - σ x ≤ 1; omega))

/-! ## The two constructions of Bing's induction, with a set of basepoints -/

/-- `genF_concl` (batch 122) with a set of basepoints: every link of `Z` lies in the first block of
`H`. -/
theorem genF_conclZ {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {Z : ℕ → Prop}
    (h : BHyp n K ρ σ T)
    (hK : 5 ≤ K) {p q : ℕ} (hpq : p ≤ q) (hq : q < n)
    (hleft : 0 < p → (T p 0 ∨ T p (K - 1))) (hright : q + 1 < n → (T q 0 ∨ T q (K - 1)))
    (H : ℕ → ℕ) (hZ : ∀ x, x < n → Z x → p ≤ x ∧ x ≤ q ∧ H x = 0) (hHc : PCons p q ρ σ H)
    {e a : ℕ} (he : e = p ∨ e = q)
    (ha : a = H e)
    (hHe : ∀ t, p ≤ t → t ≤ q → H t = a → ρ t ≤ 1)
    (hmin : ∀ e', (e' = p ∨ e' = q) → (T e' 0 ∨ T e' (K - 1)) → a ≤ H e') :
    BConclZ n K ρ σ T Z := by
  have hA : ∀ t, p ≤ t → t ≤ q → H t < a → genF K ρ σ p q a H t = H t := by
    intro t h1 h2 h3; simp [genF, h1, h2, h3]
  have hD : ∀ t, ¬ (p ≤ t ∧ t ≤ q ∧ H t < a) → genF K ρ σ p q a H t = a + genG K ρ σ t := by
    intro t h1; simp only [genF, if_neg h1]
  have hg0 : ∀ t, t < n → (genG K ρ σ t = 0 ↔ ρ t ≤ 1) := by
    intro t ht; have := h.le t ht; unfold genG; split_ifs <;> omega
  have hgK : ∀ t, t < n → genG K ρ σ t = K - 3 → K - 2 ≤ σ t := by
    intro t ht; have := h.le t ht; unfold genG; split_ifs <;> omega
  have hea : p ≤ e ∧ e ≤ q := by omega
  refine ⟨genF K ρ σ p q a H, fun x hx hZx => ?_, ⟨fun t _ ht => ?_, fun v => ?_⟩,
    fun e' he' hee' hT' => ?_⟩
  · obtain ⟨hpi, hiq, hH0⟩ := hZ x hx hZx
    by_cases hia : H x < a
    · rw [hA x hpi hiq hia, hH0]
    · rw [hD x (by omega), (hg0 x (by omega)).mpr (hHe x hpi hiq (by omega))]; omega
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

/-- `cutF_spec` (batch 122) with a set of basepoints. -/
theorem cutF_specZ {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {Z : ℕ → Prop}
    (h : BHyp n K ρ σ T)
    (hK : 5 ≤ K) (hin : ∀ t, t < n → 1 ≤ ρ t ∧ σ t + 2 ≤ K) (hρ0 : ρ 0 ≤ 1)
    (hn1 : K ≤ ρ (n - 1) + 2) {p q k a : ℕ} (H : ℕ → ℕ) (hpq : p ≤ q) (hqk : q ≤ k)
    (hk : k + 1 < n) (hρk : ρ k ≤ 1) (hZ : ∀ x, x < n → Z x → p ≤ x ∧ x ≤ q ∧ H x = 0)
    (hHc : PCons p q ρ σ H)
    (htop : ∀ t, p ≤ t → t ≤ q → H t = a → 2 ≤ ρ t ∧ K ≤ σ t + 3)
    (hp : 0 < p → a ≤ H p) (hq : a ≤ H q)
    (h0 : p = 0 → H 0 < a → ∀ t, p ≤ t → t ≤ q → H t = H 0 → ρ t ≤ 1) :
    (∀ x, x < n → Z x → cutF K ρ σ p q k a H x = 0) ∧ PCons 0 (n - 1) ρ σ (cutF K ρ σ p q k a H) ∧
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
  refine ⟨fun x hx hZx => ?_, ⟨fun t _ ht => ?_, fun v => ?_⟩, fun e he hee _ => ?_⟩
  · -- the links of `Z` are in the first link
    obtain ⟨hpi, hiq, hHi⟩ := hZ x hx hZx
    by_cases hia : H x < a
    · rw [hA x hpi hiq hia, hHi]
    · rw [hD x (by omega) (by omega), htopg x hpi hiq (by omega)]; omega
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

/-- `cutF_specZ`, packaged as `BConclZ`. -/
theorem cutF_conclZ {n K : ℕ} {ρ σ : ℕ → ℕ} {T : ℕ → ℕ → Prop} {Z : ℕ → Prop}
    (h : BHyp n K ρ σ T)
    (hK : 5 ≤ K) (hin : ∀ t, t < n → 1 ≤ ρ t ∧ σ t + 2 ≤ K) (hρ0 : ρ 0 ≤ 1)
    (hn1 : K ≤ ρ (n - 1) + 2) {p q k a : ℕ} (H : ℕ → ℕ) (hpq : p ≤ q) (hqk : q ≤ k)
    (hk : k + 1 < n) (hρk : ρ k ≤ 1) (hZ : ∀ x, x < n → Z x → p ≤ x ∧ x ≤ q ∧ H x = 0)
    (hHc : PCons p q ρ σ H)
    (htop : ∀ t, p ≤ t → t ≤ q → H t = a → 2 ≤ ρ t ∧ K ≤ σ t + 3)
    (hp : 0 < p → a ≤ H p) (hq : a ≤ H q)
    (h0 : p = 0 → H 0 < a → ∀ t, p ≤ t → t ≤ q → H t = H 0 → ρ t ≤ 1) :
    BConclZ n K ρ σ T Z :=
  ⟨_, cutF_specZ h hK hin hρ0 hn1 H hpq hqk hk hρk hZ hHc htop hp hq h0⟩

/-! ## Bookkeeping for pairs -/

theorem commonC_sub {ρ σ : ℕ → ℕ} {i i' p lo : ℕ} (hc : CommonC ρ σ i i') (hpi : p ≤ i)
    (hpi' : p ≤ i') (hlo : lo ≤ ρ i) (hlo' : lo ≤ ρ i') :
    CommonC (fun t => ρ (t + p) - lo) (fun t => σ (t + p) - lo) (i - p) (i' - p) := by
  obtain ⟨c, c1, c2, c3, c4⟩ := hc
  refine ⟨c - lo, ?_⟩
  simp only [Nat.sub_add_cancel hpi, Nat.sub_add_cancel hpi']
  omega

theorem commonC_flip {ρ σ : ℕ → ℕ} {K i i' : ℕ} (hc : CommonC ρ σ i i') (hi : σ i < K)
    (hi' : σ i' < K) : CommonC (fun t => K - 1 - σ t) (fun t => K - 1 - ρ t) i i' := by
  obtain ⟨c, c1, c2, c3, c4⟩ := hc
  refine ⟨K - 1 - c, ?_, ?_, ?_, ?_⟩ <;> simp only <;> omega

theorem commonC_revflip {ρ σ : ℕ → ℕ} {K n i i' : ℕ} (hc : CommonC ρ σ i i') (hi : σ i < K)
    (hi' : σ i' < K) (hin : i < n) (hin' : i' < n) :
    CommonC (fun t => K - 1 - σ (n - 1 - t)) (fun t => K - 1 - ρ (n - 1 - t))
      (n - 1 - i) (n - 1 - i') := by
  obtain ⟨c, c1, c2, c3, c4⟩ := hc
  refine ⟨K - 1 - c, ?_⟩
  simp only [show n - 1 - (n - 1 - i) = i by omega, show n - 1 - (n - 1 - i') = i' by omega]
  omega

theorem pairZ_shift {i i' p x : ℕ} (hpi : p ≤ i) (hpi' : p ≤ i') (hx : pairZ i i' (x + p)) :
    pairZ (i - p) (i' - p) x := by
  unfold pairZ at hx ⊢; omega

theorem pairZ_rev {i i' n x : ℕ} (hx : x < n) (hZ : pairZ i i' (n - 1 - x)) (hi : i < n)
    (hi' : i' < n) : pairZ (n - 1 - i) (n - 1 - i') x := by
  unfold pairZ at hZ ⊢; omega

end HPC.Fold.Recon122
