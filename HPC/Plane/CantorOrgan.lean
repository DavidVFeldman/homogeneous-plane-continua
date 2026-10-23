import Mathlib

/-!
# Batch 97: the Cantor organ, part one — weighted digit sums and the embedding

The *Cantor organ* is `C × [0,1]` (`C` the Cantor set) with, for every gap `(a, b)` of `C`, the
points `(a, 1)`, `(b, 1)` identified when the gap has odd generation and `(a, 0)`, `(b, 0)`
identified when it has even generation. This file realises it as a compact subset of `ℝ × ℝ`:
Cantor space is `ℕ → Bool`; the point `(c, y)` goes to `(y P(c) + (1 - y) Q(c), y)`, where `P`
and `Q` are weighted digit sums chosen so that `P` identifies exactly the endpoints of the odd
gaps and `Q` exactly those of the even gaps (`psi_eq_psi_iff`).

Everything in this file is elementary analysis on digit sums; the topology of the organ is in
`HPC/Plane/CantorOrganLayers.lean`.
-/

namespace HPC.Plane.Org

open Set Filter Topology

/-- Cantor space. -/
abbrev Cs := ℕ → Bool

/-- `0/1` value of a digit. -/
noncomputable def ind (x : Bool) : ℝ := if x then 1 else 0

theorem ind_nonneg (x : Bool) : 0 ≤ ind x := by unfold ind; split_ifs <;> norm_num

theorem ind_le_one (x : Bool) : ind x ≤ 1 := by unfold ind; split_ifs <;> norm_num

/-! ## Weighted digit sums -/

/-- A weight sequence: `r` strictly decreasing to `0`; the digit weights are `r k - r (k+1)`. -/
structure Wt where
  r : ℕ → ℝ
  dec : ∀ k, r (k + 1) < r k
  lim : Tendsto r atTop (𝓝 0)

namespace Wt

variable (w : Wt)

/-- The weight of digit `k`. -/
def p (k : ℕ) : ℝ := w.r k - w.r (k + 1)

theorem p_pos (k : ℕ) : 0 < w.p k := sub_pos.mpr (w.dec k)

theorem r_nonneg (k : ℕ) : 0 ≤ w.r k := by
  have hanti : Antitone w.r := antitone_nat_of_succ_le fun n => (w.dec n).le
  exact le_of_tendsto w.lim (eventually_atTop.mpr ⟨k, fun n hn => hanti hn⟩)

/-- Tails telescope. -/
theorem hasSum_p_tail (n : ℕ) : HasSum (fun k => w.p (k + n)) (w.r n) := by
  have hnn : ∀ k, 0 ≤ w.p (k + n) := fun k => (w.p_pos _).le
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hsum : ∀ N, ∑ k ∈ Finset.range N, w.p (k + n) = w.r n - w.r (N + n) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [p]
      rw [show N + 1 + n = N + n + 1 by ring]
      ring
  simp_rw [hsum]
  have : Tendsto (fun N => w.r (N + n)) atTop (𝓝 0) :=
    w.lim.comp (tendsto_add_atTop_nat n)
  simpa using (tendsto_const_nhds (x := w.r n)).sub this

theorem summable_p : Summable w.p := by
  simpa using (w.hasSum_p_tail 0).summable

/-- The weighted digit sum. -/
noncomputable def sum (b : Cs) : ℝ := ∑' k, ind (b k) * w.p k

theorem summable_term (b : Cs) : Summable fun k => ind (b k) * w.p k :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (ind_nonneg _) (w.p_pos k).le)
    (fun k => by
      have := ind_le_one (b k); have := w.p_pos k
      nlinarith [ind_nonneg (b k)]) w.summable_p

theorem sum_nonneg (b : Cs) : 0 ≤ w.sum b :=
  tsum_nonneg fun k => mul_nonneg (ind_nonneg _) (w.p_pos k).le

theorem sum_le (b : Cs) : w.sum b ≤ w.r 0 := by
  have h0 := w.hasSum_p_tail 0
  simp only [add_zero] at h0
  exact hasSum_le (fun k => by
      have := ind_le_one (b k); have := w.p_pos k
      nlinarith [ind_nonneg (b k)]) (w.summable_term b).hasSum h0

theorem continuous_sum : Continuous w.sum := by
  apply continuous_tsum (u := w.p) _ w.summable_p
  · intro k b
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ind_nonneg _) (w.p_pos k).le)]
    have := ind_le_one (b k); have := w.p_pos k
    nlinarith [ind_nonneg (b k)]
  · intro k
    have : Continuous fun b : Cs => b k := continuous_apply k
    have hc : Continuous fun b : Cs => ind (b k) :=
      (continuous_of_discreteTopology (f := ind)).comp this
    exact hc.mul continuous_const

/-- The excess of digit `m` over the whole tail after it. -/
def gap (m : ℕ) : ℝ := w.p m - w.r (m + 1)

end Wt

/-! ## First differences and gap pairs -/

/-- `b` and `b'` first differ at `m`, with `b m = false`, `b' m = true`. -/
def FirstDiff (m : ℕ) (b b' : Cs) : Prop :=
  (∀ k < m, b k = b' k) ∧ b m = false ∧ b' m = true

/-- `b = w 0 1 1 1 …`, `b' = w 1 0 0 0 …`, with `|w| = m`: the two endpoints of a gap. -/
def Pair (m : ℕ) (b b' : Cs) : Prop :=
  FirstDiff m b b' ∧ ∀ k, m < k → b k = true ∧ b' k = false

theorem exists_firstDiff {b b' : Cs} (h : b ≠ b') :
    ∃ m, FirstDiff m b b' ∨ FirstDiff m b' b := by
  classical
  have hex : ∃ k, b k ≠ b' k := by
    by_contra hno; push_neg at hno; exact h (funext hno)
  refine ⟨Nat.find hex, ?_⟩
  have hm := Nat.find_spec hex
  have hlt : ∀ k < Nat.find hex, b k = b' k := fun k hk => by
    have := Nat.find_min hex hk; push_neg at this; exact this
  cases hb : b (Nat.find hex) <;> cases hb' : b' (Nat.find hex) <;> simp_all [FirstDiff]

namespace Wt

variable (w : Wt)

/-- **The difference formula.** If `b`, `b'` first differ at `m` (`b m = false`), then
`sum b' - sum b - p m` is the tail sum of `(ind b'_k - ind b_k) p_k` over `k > m`. -/
theorem hasSum_diff_tail {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') :
    HasSum (fun j => (ind (b' (j + (m + 1))) - ind (b (j + (m + 1)))) * w.p (j + (m + 1)))
      (w.sum b' - w.sum b - w.p m) := by
  have hd : HasSum (fun k => (ind (b' k) - ind (b k)) * w.p k) (w.sum b' - w.sum b) := by
    have := ((w.summable_term b').hasSum).sub ((w.summable_term b).hasSum)
    simpa [sub_mul] using this
  have hfin : ∑ k ∈ Finset.range (m + 1), (ind (b' k) - ind (b k)) * w.p k = w.p m := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [h.2.1, h.2.2, ind]
    · intro k hk
      rw [h.1 k (Finset.mem_range.mp hk)]; ring
  have := (hasSum_nat_add_iff' (m + 1)).mpr hd
  rwa [hfin] at this

theorem sum_sub_ge {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') :
    w.gap m ≤ w.sum b' - w.sum b := by
  have h1 := w.hasSum_diff_tail h
  have h2 : HasSum (fun j => -w.p (j + (m + 1))) (-w.r (m + 1)) := (w.hasSum_p_tail _).neg
  have := hasSum_le (fun j => by
      have := ind_le_one (b (j + (m + 1))); have := ind_nonneg (b' (j + (m + 1)))
      have := w.p_pos (j + (m + 1))
      nlinarith) h2 h1
  unfold gap; linarith

theorem sum_sub_gt {m : ℕ} {b b' : Cs} (h : FirstDiff m b b')
    (hk : ∃ k, m < k ∧ ¬ (b k = true ∧ b' k = false)) :
    w.gap m < w.sum b' - w.sum b := by
  obtain ⟨k, hmk, hnot⟩ := hk
  have h1 := w.hasSum_diff_tail h
  have h2 : HasSum (fun j => -w.p (j + (m + 1))) (-w.r (m + 1)) := (w.hasSum_p_tail _).neg
  obtain ⟨j, rfl⟩ : ∃ j, k = j + (m + 1) := ⟨k - (m + 1), by omega⟩
  have := hasSum_lt (f := fun j => -w.p (j + (m + 1))) (i := j) (fun j => by
      have := ind_le_one (b (j + (m + 1))); have := ind_nonneg (b' (j + (m + 1)))
      have := w.p_pos (j + (m + 1))
      show -w.p (j + (m + 1)) ≤ _
      nlinarith) (by
      show -w.p (j + (m + 1)) < _
      have hp := w.p_pos (j + (m + 1))
      cases hb : b (j + (m + 1)) <;> cases hb' : b' (j + (m + 1)) <;>
        simp_all [ind]) h2 h1
  unfold gap; linarith

theorem sum_sub_eq {m : ℕ} {b b' : Cs} (h : Pair m b b') : w.sum b' - w.sum b = w.gap m := by
  have h1 := w.hasSum_diff_tail h.1
  have h2 : HasSum (fun j => -w.p (j + (m + 1))) (-w.r (m + 1)) := (w.hasSum_p_tail _).neg
  have heq : (fun j => (ind (b' (j + (m + 1))) - ind (b (j + (m + 1)))) * w.p (j + (m + 1))) =
      fun j => -w.p (j + (m + 1)) := by
    funext j
    have := h.2 (j + (m + 1)) (by omega)
    simp [this.1, this.2, ind]
  rw [heq] at h1
  have := h1.unique h2
  unfold gap; linarith

/-- Monotonicity, when every gap is nonnegative. -/
theorem sum_le_sum {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') (hg : 0 ≤ w.gap m) :
    w.sum b ≤ w.sum b' := by
  have := w.sum_sub_ge h; linarith

theorem sum_eq_iff {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') (hg : 0 ≤ w.gap m) :
    w.sum b = w.sum b' ↔ w.gap m = 0 ∧ Pair m b b' := by
  constructor
  · intro he
    by_contra hno
    by_cases hp : Pair m b b'
    · have := w.sum_sub_eq hp
      exact hno ⟨by linarith, hp⟩
    · have hk : ∃ k, m < k ∧ ¬ (b k = true ∧ b' k = false) := by
        by_contra hk; push_neg at hk; exact hp ⟨h, hk⟩
      have := w.sum_sub_gt h hk
      linarith
  · rintro ⟨hg0, hp⟩
    have := w.sum_sub_eq hp
    linarith

end Wt

/-! ## The three weights -/

/-- Binary weights: `r k = 2^{-k}`, every gap is `0`. -/
noncomputable def wL : Wt where
  r k := (1 / 2 : ℝ) ^ k
  dec k := by
    rw [pow_succ]
    have : (0 : ℝ) < (1 / 2) ^ k := by positivity
    linarith
  lim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem wL_gap (m : ℕ) : wL.gap m = 0 := by
  simp only [Wt.gap, Wt.p, wL, pow_succ]; ring

/-- Ratio sequence: `r (k+1) = r k / 2` when `k` has parity `e`, `r k / 3` otherwise. -/
noncomputable def rr (e : Bool) : ℕ → ℝ
  | 0 => 1
  | k + 1 => rr e k / (if decide (Odd k) = e then 2 else 3)

theorem rr_pos (e : Bool) (k : ℕ) : 0 < rr e k := by
  induction k with
  | zero => simp [rr]
  | succ k ih => simp only [rr]; split_ifs <;> positivity

theorem rr_le (e : Bool) (k : ℕ) : rr e k ≤ (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp [rr]
  | succ k ih =>
    simp only [rr, pow_succ]
    have := rr_pos e k
    split_ifs
    · linarith
    · have : rr e k / 3 ≤ rr e k / 2 := by
        apply div_le_div_of_nonneg_left this.le (by norm_num) (by norm_num)
      linarith

noncomputable def wR (e : Bool) : Wt where
  r := rr e
  dec k := by
    simp only [rr]
    have := rr_pos e k
    split_ifs <;> linarith
  lim := by
    apply squeeze_zero (fun k => (rr_pos e k).le) (rr_le e)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem wR_gap_eq (e : Bool) {m : ℕ} (hm : decide (Odd m) = e) : (wR e).gap m = 0 := by
  simp only [Wt.gap, Wt.p, wR, rr, hm, if_true]; ring

theorem wR_gap_pos (e : Bool) {m : ℕ} (hm : decide (Odd m) ≠ e) : 0 < (wR e).gap m := by
  simp only [Wt.gap, Wt.p, wR, rr, hm, if_false]
  have := rr_pos e m
  linarith

theorem wR_gap_nonneg (e : Bool) (m : ℕ) : 0 ≤ (wR e).gap m := by
  by_cases hm : decide (Odd m) = e
  · rw [wR_gap_eq e hm]
  · exact (wR_gap_pos e hm).le

/-- The base map `λ` (binary value of the digits). -/
noncomputable def lam : Cs → ℝ := wL.sum
/-- `P` identifies exactly the endpoints of odd gaps. -/
noncomputable def PP : Cs → ℝ := (wR true).sum
/-- `Q` identifies exactly the endpoints of even gaps. -/
noncomputable def QQ : Cs → ℝ := (wR false).sum

theorem lam_le_of {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') : lam b ≤ lam b' :=
  wL.sum_le_sum h (wL_gap m).ge

theorem lam_eq_iff {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') : lam b = lam b' ↔ Pair m b b' := by
  rw [lam, wL.sum_eq_iff h (wL_gap m).ge]; simp [wL_gap]

theorem PP_le_of {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') : PP b ≤ PP b' :=
  (wR true).sum_le_sum h (wR_gap_nonneg _ m)

theorem QQ_le_of {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') : QQ b ≤ QQ b' :=
  (wR false).sum_le_sum h (wR_gap_nonneg _ m)

theorem PP_eq_iff {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') :
    PP b = PP b' ↔ Odd m ∧ Pair m b b' := by
  rw [PP, (wR true).sum_eq_iff h (wR_gap_nonneg _ m)]
  constructor
  · rintro ⟨hg, hp⟩
    refine ⟨?_, hp⟩
    by_contra ho
    have := wR_gap_pos true (m := m) (by simpa using ho)
    linarith
  · rintro ⟨ho, hp⟩
    exact ⟨wR_gap_eq true (by simpa using ho), hp⟩

theorem QQ_eq_iff {m : ℕ} {b b' : Cs} (h : FirstDiff m b b') :
    QQ b = QQ b' ↔ Even m ∧ Pair m b b' := by
  rw [QQ, (wR false).sum_eq_iff h (wR_gap_nonneg _ m)]
  constructor
  · rintro ⟨hg, hp⟩
    refine ⟨?_, hp⟩
    by_contra he
    have := wR_gap_pos false (m := m) (by simpa [Nat.not_even_iff_odd] using he)
    linarith
  · rintro ⟨he, hp⟩
    exact ⟨wR_gap_eq false (by simpa [Nat.not_odd_iff_even] using he), hp⟩

theorem continuous_lam : Continuous lam := wL.continuous_sum
theorem continuous_PP : Continuous PP := (wR true).continuous_sum
theorem continuous_QQ : Continuous QQ := (wR false).continuous_sum

theorem lam_nonneg (b : Cs) : 0 ≤ lam b := wL.sum_nonneg b
theorem lam_le_one (b : Cs) : lam b ≤ 1 :=
  (wL.sum_le b).trans (by simp [wL])
theorem PP_nonneg (b : Cs) : 0 ≤ PP b := (wR true).sum_nonneg b
theorem PP_le_one (b : Cs) : PP b ≤ 1 := by
  have := (wR true).sum_le b; simpa [wR, rr] using this
theorem QQ_nonneg (b : Cs) : 0 ≤ QQ b := (wR false).sum_nonneg b
theorem QQ_le_one (b : Cs) : QQ b ≤ 1 := by
  have := (wR false).sum_le b; simpa [wR, rr] using this

theorem lam_pair {m : ℕ} {b b' : Cs} (h : Pair m b b') : lam b = lam b' :=
  (lam_eq_iff h.1).mpr h

theorem lam_surj {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ∃ b : Cs, lam b = t := by
  obtain ⟨d, -, hd⟩ := Real.ofDigits_SurjOn (b := 2) (by norm_num) ht
  refine ⟨fun k => decide (d k = 1), ?_⟩
  rw [← hd, lam, Wt.sum, Real.ofDigits]
  congr 1
  funext k
  simp only [Real.ofDigitsTerm, Wt.p, wL, ind]
  have : (d k : ℕ) = 0 ∨ (d k : ℕ) = 1 := by have := (d k).isLt; omega
  rcases this with h | h
  · have : d k ≠ 1 := fun h' => by rw [h'] at h; simp at h
    simp [this, h, pow_succ]
  · have : d k = 1 := Fin.ext h
    simp [this, pow_succ]; ring

/-! ## The embedding -/

/-- The organ map: `(b, y) ↦ (y P(b) + (1 - y) Q(b), y)`. -/
noncomputable def psi (b : Cs) (y : ℝ) : ℝ × ℝ := (y * PP b + (1 - y) * QQ b, y)

theorem continuous_psi : Continuous fun d : Cs × ℝ => psi d.1 d.2 := by
  unfold psi
  have h1 : Continuous fun d : Cs × ℝ => PP d.1 := continuous_PP.comp continuous_fst
  have h2 : Continuous fun d : Cs × ℝ => QQ d.1 := continuous_QQ.comp continuous_fst
  refine Continuous.prodMk ?_ continuous_snd
  exact (continuous_snd.mul h1).add ((continuous_const.sub continuous_snd).mul h2)

@[simp] theorem psi_snd (b : Cs) (y : ℝ) : (psi b y).2 = y := rfl

/-- **The identifications.** For `y ∈ [0,1]`, `psi b y = psi b' y'` exactly when `y = y'` and
either `b = b'`, or `b, b'` are the endpoints of a gap of length `m` with `y = 1`, `m` odd, or
`y = 0`, `m` even. -/
theorem psi_eq_psi_iff {b b' : Cs} {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    psi b y = psi b' y' ↔ y = y' ∧ (b = b' ∨ ∃ m, (Pair m b b' ∨ Pair m b' b) ∧
      ((y = 1 ∧ Odd m) ∨ (y = 0 ∧ Even m))) := by
  constructor
  · intro h
    have hyy : y = y' := congrArg Prod.snd h
    subst hyy
    refine ⟨rfl, ?_⟩
    have hx : y * PP b + (1 - y) * QQ b = y * PP b' + (1 - y) * QQ b' := congrArg Prod.fst h
    by_cases hbb : b = b'
    · exact Or.inl hbb
    right
    obtain ⟨m, hm | hm⟩ := exists_firstDiff hbb
    · have hP := PP_le_of hm
      have hQ := QQ_le_of hm
      have hP0 : y * (PP b' - PP b) = 0 := by
        have := mul_nonneg hy.1 (sub_nonneg.mpr hP)
        have := mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hQ)
        nlinarith
      have hQ0 : (1 - y) * (QQ b' - QQ b) = 0 := by
        have := mul_nonneg hy.1 (sub_nonneg.mpr hP)
        have := mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hQ)
        nlinarith
      refine ⟨m, ?_⟩
      rcases mul_eq_zero.mp hP0 with h0 | hPe <;> rcases mul_eq_zero.mp hQ0 with h1 | hQe
      · exact absurd h1 (by rw [h0]; norm_num)
      · obtain ⟨he, hp⟩ := (QQ_eq_iff hm).mp (by linarith)
        exact ⟨Or.inl hp, Or.inr ⟨h0, he⟩⟩
      · obtain ⟨ho, hp⟩ := (PP_eq_iff hm).mp (by linarith)
        exact ⟨Or.inl hp, Or.inl ⟨by linarith, ho⟩⟩
      · obtain ⟨ho, -⟩ := (PP_eq_iff hm).mp (by linarith)
        obtain ⟨he, -⟩ := (QQ_eq_iff hm).mp (by linarith)
        exact absurd he (Nat.not_even_iff_odd.mpr ho)
    · have hP := PP_le_of hm
      have hQ := QQ_le_of hm
      have hP0 : y * (PP b - PP b') = 0 := by
        have := mul_nonneg hy.1 (sub_nonneg.mpr hP)
        have := mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hQ)
        nlinarith
      have hQ0 : (1 - y) * (QQ b - QQ b') = 0 := by
        have := mul_nonneg hy.1 (sub_nonneg.mpr hP)
        have := mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hQ)
        nlinarith
      refine ⟨m, ?_⟩
      rcases mul_eq_zero.mp hP0 with h0 | hPe <;> rcases mul_eq_zero.mp hQ0 with h1 | hQe
      · exact absurd h1 (by rw [h0]; norm_num)
      · obtain ⟨he, hp⟩ := (QQ_eq_iff hm).mp (by linarith)
        exact ⟨Or.inr hp, Or.inr ⟨h0, he⟩⟩
      · obtain ⟨ho, hp⟩ := (PP_eq_iff hm).mp (by linarith)
        exact ⟨Or.inr hp, Or.inl ⟨by linarith, ho⟩⟩
      · obtain ⟨ho, -⟩ := (PP_eq_iff hm).mp (by linarith)
        obtain ⟨he, -⟩ := (QQ_eq_iff hm).mp (by linarith)
        exact absurd he (Nat.not_even_iff_odd.mpr ho)
  · rintro ⟨rfl, h | ⟨m, hp, hyo⟩⟩
    · rw [h]
    · rcases hyo with ⟨rfl, ho⟩ | ⟨rfl, he⟩
      · simp only [psi, one_mul, sub_self, zero_mul, add_zero]
        rcases hp with hp | hp
        · rw [(PP_eq_iff hp.1).mpr ⟨ho, hp⟩]
        · rw [(PP_eq_iff hp.1).mpr ⟨ho, hp⟩]
      · simp only [psi, zero_mul, sub_zero, one_mul, zero_add]
        rcases hp with hp | hp
        · rw [(QQ_eq_iff hp.1).mpr ⟨he, hp⟩]
        · rw [(QQ_eq_iff hp.1).mpr ⟨he, hp⟩]

/-- Identified points have the same base value. -/
theorem lam_eq_of_psi_eq {b b' : Cs} {y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (h : psi b y = psi b' y') : lam b = lam b' := by
  obtain ⟨-, rfl | ⟨m, hp | hp, -⟩⟩ := (psi_eq_psi_iff hy).mp h
  · rfl
  · exact lam_pair hp
  · exact (lam_pair hp).symm

/-! ## The space -/

/-- The parameter space `C × [0,1]`. -/
abbrev Dom := Cs × Icc (0 : ℝ) 1

/-- **The Cantor organ**, as a subset of the plane. -/
def organ : Set (ℝ × ℝ) := Set.range fun d : Dom => psi d.1 d.2

theorem continuous_psiD : Continuous fun d : Dom => psi d.1 d.2 :=
  continuous_psi.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

theorem isCompact_organ : IsCompact organ := isCompact_range continuous_psiD

/-- The Cantor organ as a space. -/
abbrev Organ := ↥organ

instance : CompactSpace Organ := isCompact_iff_compactSpace.mp isCompact_organ

/-- The quotient map `C × [0,1] → Organ`. -/
noncomputable def Phi (d : Dom) : Organ := ⟨psi d.1 d.2, d, rfl⟩

theorem continuous_Phi : Continuous Phi := continuous_psiD.subtype_mk _

theorem surjective_Phi : Function.Surjective Phi := by
  rintro ⟨z, d, rfl⟩; exact ⟨d, rfl⟩

theorem isClosedMap_Phi : IsClosedMap Phi := continuous_Phi.isClosedMap

theorem isQuotientMap_Phi : Topology.IsQuotientMap Phi :=
  isClosedMap_Phi.isQuotientMap continuous_Phi surjective_Phi

theorem Phi_eq_iff {d d' : Dom} : Phi d = Phi d' ↔ psi d.1 d.2 = psi d'.1 d'.2 := Subtype.ext_iff

/-- The height of a point. -/
theorem Phi_height (d : Dom) : (Phi d : ℝ × ℝ).2 = d.2 := rfl

/-! ## The layer map -/

/-- A chosen parameter for each point. -/
noncomputable def rep (s : Organ) : Dom := Classical.choose (surjective_Phi s)

theorem Phi_rep (s : Organ) : Phi (rep s) = s := Classical.choose_spec (surjective_Phi s)

/-- **The layer map** `F : Organ → [0,1]`: the base value of a parameter. -/
noncomputable def F (s : Organ) : ℝ := lam (rep s).1

theorem F_Phi (d : Dom) : F (Phi d) = lam d.1 := by
  have h := Phi_rep (Phi d)
  rw [Phi_eq_iff] at h
  exact lam_eq_of_psi_eq (rep (Phi d)).2.2 h

theorem continuous_F : Continuous F := by
  rw [isQuotientMap_Phi.continuous_iff]
  have : F ∘ Phi = fun d => lam d.1 := funext F_Phi
  rw [this]
  exact continuous_lam.comp continuous_fst

theorem F_mem (s : Organ) : F s ∈ Icc (0 : ℝ) 1 := ⟨lam_nonneg _, lam_le_one _⟩

theorem F_surj {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ∃ s, F s = t := by
  obtain ⟨b, hb⟩ := lam_surj ht
  exact ⟨Phi (b, ⟨0, le_rfl, zero_le_one⟩), by rw [F_Phi, hb]⟩

theorem isClosedMap_F : IsClosedMap F := continuous_F.isClosedMap

end HPC.Plane.Org
