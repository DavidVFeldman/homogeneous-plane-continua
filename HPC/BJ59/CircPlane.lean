import HPC.BJ59.CircStep
import HPC.BJ59.CircDescr

/-!
# Batch 202, §6: the assembly (`exists_circDescr_plane`)

Commission 202 §6.1–6.2. A level is `(N, Φ, m, o)` with `4 ≤ N`, `5 ≤ m`, `m + 4 ≤ N`. Level 0 is
`(16, id, 5, 0)`. From level `i`, `circ_step Φ N (1/2^i) (m/2 − 1/4)` gives `S`,
`exists_sweepPattern m S` gives `x`, `Q = sweepQ m S`, `circ_step` with `y₀ = 1/4` gives `ψ`, and
level `i + 1` is `(Q N, ψ.trans Φ, Q/2, o + 1/(4N))`. The links of level `k` are
`Φ_k '' stdCircLink N_k t`, and the arcs have length `λ_k = m_k / N_k`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

namespace CircPlane

/-- A level of the construction. -/
structure Lvl where
  N : ℕ
  Φ : Pt ≃ₜ Pt
  m : ℕ
  o : ℝ
  hN : 4 ≤ N
  hm : 5 ≤ m
  hmN : m + 4 ≤ N

/-- Level 0: the standard circular chain of 16 polar rectangles. -/
noncomputable def L0 : Lvl := ⟨16, Homeomorph.refl Pt, 5, 0, by norm_num, le_rfl, by norm_num⟩

theorem eta_pos (i : ℕ) : (0 : ℝ) < 1 / 2 ^ i := by positivity

/-- The stutter multiplier of step `i`. -/
noncomputable def stepS (i : ℕ) (L : Lvl) : ℕ :=
  Classical.choose (circ_step L.Φ L.hN (eta_pos i) ((L.m : ℝ) / 2 - 1 / 4))

theorem stepS_ge (i : ℕ) (L : Lvl) : 12 ≤ stepS i L :=
  (Classical.choose_spec (circ_step L.Φ L.hN (eta_pos i) ((L.m : ℝ) / 2 - 1 / 4))).1

theorem stepS_one (i : ℕ) (L : Lvl) : 1 ≤ stepS i L := by have := stepS_ge i L; omega

/-- The sweep pattern of step `i`. -/
noncomputable def stepX (i : ℕ) (L : Lvl) : ℤ → ℤ :=
  Classical.choose (exists_sweepPattern L.m (stepS i L) L.hm (stepS_one i L))

/-- The number of new links per old link at step `i`. -/
noncomputable def stepQ (i : ℕ) (L : Lvl) : ℕ := sweepQ L.m (stepS i L)

theorem stepX_spec (i : ℕ) (L : Lvl) :
    (∀ t : ℤ, stepX i L (t + stepQ i L) = stepX i L t + 1) ∧
      (∀ t, |stepX i L (t + 1) - stepX i L t| ≤ 1) ∧
      (∀ s t, stepX i L s + 2 ≤ stepX i L t → (stepS i L : ℤ) ≤ |s - t|) ∧
      (∀ t, |(stepX i L t : ℝ) - (1 / 4 + (t : ℝ) / stepQ i L)| ≤ (L.m : ℝ) / 2 - 1 / 4) ∧
      (∀ (l : ℤ) (y : ℝ), |y - l| ≤ (L.m : ℝ) / 2 - 1 / 2 →
        ∃ t, stepX i L t = l ∧
          |y - (1 / 4 + (t : ℝ) / stepQ i L)| ≤ 1 / 4 - 1 / (2 * (stepQ i L : ℝ))) ∧
      (∀ a : ℤ, HPC.Fold.PatCrookedOn (fun u : ℕ => stepX i L (a + u)) 0 (stepQ i L / 2 + 3)) :=
  Classical.choose_spec (exists_sweepPattern L.m (stepS i L) L.hm (stepS_one i L))

theorem stepQ_eq (i : ℕ) (L : Lvl) : stepQ i L = 6 * sweepL L.m (stepS i L) := sweepQ_eq _ _

theorem stepQ_ge (i : ℕ) (L : Lvl) : 24 ≤ stepQ i L := by
  rw [stepQ_eq]; have := sweepL_ge L.hm (stepS_one i L); omega

theorem stepQ_half (i : ℕ) (L : Lvl) : ((stepQ i L / 2 : ℕ) : ℝ) = (stepQ i L : ℝ) / 2 := by
  rw [stepQ_eq, show 6 * sweepL L.m (stepS i L) / 2 = 3 * sweepL L.m (stepS i L) by omega]
  push_cast; ring

/-- The homeomorphism of step `i`. -/
noncomputable def stepψ (i : ℕ) (L : Lvl) : Pt ≃ₜ Pt :=
  Classical.choose
    ((Classical.choose_spec (circ_step L.Φ L.hN (eta_pos i) ((L.m : ℝ) / 2 - 1 / 4))).2
      (stepQ i L) (stepX i L) (1 / 4)
      (by have := stepQ_ge i L; omega) (stepX_spec i L).1 (stepX_spec i L).2.1
      (stepX_spec i L).2.2.1 (stepX_spec i L).2.2.2.1)

theorem stepψ_spec (i : ℕ) (L : Lvl) :
    (∀ t : ℤ, closure (((stepψ i L).trans L.Φ) '' stdCircLink (stepQ i L * L.N) t) ⊆
        L.Φ '' stdCircLink L.N (stepX i L t)) ∧
      (∀ t l : ℤ, (((stepψ i L).trans L.Φ) '' stdCircLink (stepQ i L * L.N) t ∩
          L.Φ '' stdCircLink L.N l).Nonempty →
        ∃ t' n : ℤ, |t' - t| ≤ 1 ∧ stepX i L t' = l + n * (L.N : ℤ)) ∧
      (∀ t : ℤ, diam (((stepψ i L).trans L.Φ) '' stdCircLink (stepQ i L * L.N) t) ≤ 1 / 2 ^ i ∨
        ∃ k : ℤ, ((stepψ i L).trans L.Φ) '' stdCircLink (stepQ i L * L.N) t ⊆
          L.Φ '' stdCircZone L.N k) ∧
      (∀ t : ℤ, diam (((stepψ i L).trans L.Φ) '' stdCircZone (stepQ i L * L.N) t) ≤ 1 / 2 ^ i) :=
  Classical.choose_spec
    ((Classical.choose_spec (circ_step L.Φ L.hN (eta_pos i) ((L.m : ℝ) / 2 - 1 / 4))).2
      (stepQ i L) (stepX i L) (1 / 4)
      (by have := stepQ_ge i L; omega) (stepX_spec i L).1 (stepX_spec i L).2.1
      (stepX_spec i L).2.2.1 (stepX_spec i L).2.2.2.1)

/-- The next level. -/
noncomputable def next (i : ℕ) (L : Lvl) : Lvl where
  N := stepQ i L * L.N
  Φ := (stepψ i L).trans L.Φ
  m := stepQ i L / 2
  o := L.o + 1 / (4 * L.N)
  hN := le_trans L.hN (Nat.le_mul_of_pos_left _ (by have := stepQ_ge i L; omega))
  hm := by have := stepQ_ge i L; omega
  hmN := by have := stepQ_ge i L; have := Nat.mul_le_mul_left (stepQ i L) L.hN; omega

/-- The levels. -/
noncomputable def lvl : ℕ → Lvl
  | 0 => L0
  | i + 1 => next i (lvl i)


/-! ### The fields of the description -/

/-- The links of level `k`. -/
noncomputable def link (k : ℕ) (t : ℤ) : Set Pt := (lvl k).Φ '' stdCircLink (lvl k).N t

/-- The arc lengths. -/
noncomputable def lam (k : ℕ) : ℝ := ((lvl k).m : ℝ) / (lvl k).N

theorem N_ne (k : ℕ) : (lvl k).N ≠ 0 := by have := (lvl k).hN; omega

theorem N_pos (k : ℕ) : (0 : ℝ) < (lvl k).N := by
  have := (lvl k).hN; exact_mod_cast (show 0 < (lvl k).N by omega)

theorem circExp_mem_ball (N : ℕ) {p : Pt} (h : p.2 ≤ 1) :
    circExp N p ∈ closedBall (0 : Pt) (Real.exp 1) := by
  rw [mem_closedBall, dist_zero_right, Prod.norm_def]
  simp only [circExp, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp p.2 ≤ Real.exp 1 := Real.exp_le_exp.mpr h
  have hp := Real.exp_pos p.2
  refine max_le ?_ ?_
  · nlinarith [Real.abs_cos_le_one (Real.pi * p.1 / N), abs_nonneg (Real.cos (Real.pi * p.1 / N))]
  · nlinarith [Real.abs_sin_le_one (Real.pi * p.1 / N), abs_nonneg (Real.sin (Real.pi * p.1 / N))]

theorem link_zero_sub (t : ℤ) : link 0 t ⊆ closedBall (0 : Pt) (Real.exp 1) := by
  rintro _ ⟨_, ⟨p, ⟨-, -, hp⟩, rfl⟩, rfl⟩
  exact circExp_mem_ball _ hp.le

theorem zone_zero_sub (t : ℤ) :
    (lvl 0).Φ '' stdCircZone (lvl 0).N t ⊆ closedBall (0 : Pt) (Real.exp 1) := by
  rintro _ ⟨_, ⟨p, ⟨-, -, hp⟩, rfl⟩, rfl⟩
  exact circExp_mem_ball _ hp

theorem link_sub_zero (k : ℕ) (t : ℤ) : ∃ s, link k t ⊆ link 0 s := by
  induction k generalizing t with
  | zero => exact ⟨t, le_rfl⟩
  | succ k ih =>
      obtain ⟨s, hs⟩ := ih (stepX k (lvl k) t)
      exact ⟨s, subset_closure.trans (((stepψ_spec k (lvl k)).1 t).trans hs)⟩

theorem isBounded_zone (k : ℕ) (t : ℤ) :
    Bornology.IsBounded ((lvl k).Φ '' stdCircZone (lvl k).N t) :=
  (((isCompact_Icc.prod isCompact_Icc).image (CircStd.continuous_circExp _)).image
    (lvl k).Φ.continuous).isBounded

theorem two_exp_lt : 2 * Real.exp 1 < 8 := by
  have := Real.exp_one_lt_d9; linarith

theorem zone_diam (k : ℕ) (t : ℤ) :
    diam ((lvl k).Φ '' stdCircZone (lvl k).N t) ≤ 8 / 2 ^ k := by
  cases k with
  | zero =>
      have := diam_le_of_subset_closedBall (Real.exp_pos 1).le (zone_zero_sub t)
      simp only [pow_zero, div_one]; linarith [two_exp_lt]
  | succ j =>
      refine ((stepψ_spec j (lvl j)).2.2.2 t).trans ?_
      rw [pow_succ]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos
        (by norm_num : (0 : ℝ) < 2) j]

theorem link_diam (k : ℕ) (t : ℤ) : diam (link k t) ≤ 16 / 2 ^ k := by
  cases k with
  | zero =>
      have := diam_le_of_subset_closedBall (Real.exp_pos 1).le (link_zero_sub t)
      simp only [pow_zero, div_one]; linarith [two_exp_lt]
  | succ i =>
      rcases (stepψ_spec i (lvl i)).2.2.1 t with h | ⟨k', hk'⟩
      · refine h.trans ?_
        rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) i]
      · refine (diam_mono hk' (isBounded_zone i k')).trans ((zone_diam i k').trans ?_)
        rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) i]

theorem N_ge (k : ℕ) : 2 ^ k ≤ (lvl k).N := by
  induction k with
  | zero => show 1 ≤ 16; norm_num
  | succ k ih =>
      show 2 ^ (k + 1) ≤ stepQ k (lvl k) * (lvl k).N
      have := stepQ_ge k (lvl k)
      rw [pow_succ]
      nlinarith

theorem lam_succ (k : ℕ) : lam (k + 1) = 1 / (2 * (lvl k).N) := by
  unfold lam
  show (((stepQ k (lvl k) / 2 : ℕ) : ℝ)) / ((stepQ k (lvl k) * (lvl k).N : ℕ) : ℝ) = _
  rw [stepQ_half]
  have := N_pos k
  have hQ : (0 : ℝ) < stepQ k (lvl k) := by
    have := stepQ_ge k (lvl k); exact_mod_cast (show 0 < stepQ k (lvl k) by omega)
  push_cast
  field_simp

theorem lam_mul (k : ℕ) : lam k * (lvl k).N = (lvl k).m := by
  unfold lam; have := N_pos k; field_simp

theorem lam_tendsto : Tendsto lam atTop (𝓝 0) := by
  have h2 : Tendsto (fun k : ℕ => 2 * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun k => ?_) (fun k => ?_)
  · unfold lam; have := N_pos k; positivity
  · cases k with
    | zero => show (5 : ℝ) / 16 ≤ 2 * (1 / 2) ^ 0; norm_num
    | succ k =>
        rw [lam_succ]
        have h := N_ge k
        have h' : (2 : ℝ) ^ k ≤ (lvl k).N := by exact_mod_cast h
        rw [div_le_iff₀ (by have := N_pos k; positivity)]
        have : (2 : ℝ) * (1 / 2) ^ (k + 1) * (2 ^ k) = 1 := by
          rw [pow_succ, one_div_pow]; field_simp
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (k + 1)]

theorem Q_pos (k : ℕ) : (0 : ℝ) < stepQ k (lvl k) := by
  have := stepQ_ge k (lvl k); exact_mod_cast (show 0 < stepQ k (lvl k) by omega)

theorem N_succ_real (k : ℕ) :
    ((lvl (k + 1)).N : ℝ) = (stepQ k (lvl k) : ℝ) * (lvl k).N := by
  show (((stepQ k (lvl k) * (lvl k).N : ℕ)) : ℝ) = _; push_cast; ring

theorem o_succ (k : ℕ) : (lvl (k + 1)).o = (lvl k).o + 1 / (4 * (lvl k).N) := rfl

theorem pat_period (k : ℕ) (t : ℤ) :
    stepX k (lvl k) (t + (lvl (k + 1)).N) = stepX k (lvl k) t + (lvl k).N := by
  have := CircJ.x_add_mul (stepQ k (lvl k)) (stepX_spec k (lvl k)).1 t ((lvl k).N)
  rw [show ((lvl (k + 1)).N : ℤ) = ((lvl k).N : ℤ) * (stepQ k (lvl k) : ℤ) by
    show (((stepQ k (lvl k) * (lvl k).N : ℕ)) : ℤ) = _; push_cast; ring]
  exact this

theorem arcNest (k : ℕ) (t : ℤ) :
    |((lvl (k + 1)).o + (t : ℝ) / (lvl (k + 1)).N) -
        ((lvl k).o + (stepX k (lvl k) t : ℝ) / (lvl k).N)| ≤ (lam k - lam (k + 1)) / 2 := by
  have hd := (stepX_spec k (lvl k)).2.2.2.1 t
  rw [lam_succ, o_succ, N_succ_real]
  unfold lam
  have hN := N_pos k
  have hQ := Q_pos k
  have e : (lvl k).o + 1 / (4 * ((lvl k).N : ℝ)) + (t : ℝ) / (stepQ k (lvl k) * (lvl k).N) -
      ((lvl k).o + (stepX k (lvl k) t : ℝ) / (lvl k).N) =
      -((stepX k (lvl k) t : ℝ) - (1 / 4 + (t : ℝ) / stepQ k (lvl k))) / (lvl k).N := by
    field_simp; ring
  have e2 : (((lvl k).m : ℝ) / (lvl k).N - 1 / (2 * (lvl k).N)) / 2 =
      ((lvl k).m / 2 - 1 / 4) / (lvl k).N := by field_simp; ring
  rw [e, e2, abs_div, abs_neg, abs_of_pos hN]
  exact div_le_div_of_nonneg_right hd hN.le

theorem surv (k : ℕ) (l : ℤ) (y : ℝ)
    (hy : |y - ((lvl k).o + (l : ℝ) / (lvl k).N)| ≤ lam k / 2 - 1 / (2 * (lvl k).N)) :
    ∃ t : ℤ, stepX k (lvl k) t = l ∧
      |y - ((lvl (k + 1)).o + (t : ℝ) / (lvl (k + 1)).N)| ≤
        lam (k + 1) / 2 - 1 / (2 * (lvl (k + 1)).N) := by
  have hN := N_pos k
  have hQ := Q_pos k
  unfold lam at hy
  set Y := ((lvl k).N : ℝ) * (y - (lvl k).o) with hY
  have h1 : |Y - l| ≤ ((lvl k).m : ℝ) / 2 - 1 / 2 := by
    have e : Y - l = (lvl k).N * (y - ((lvl k).o + (l : ℝ) / (lvl k).N)) := by
      rw [hY]; field_simp; ring
    have e2 : ((lvl k).m : ℝ) / 2 - 1 / 2 =
        (lvl k).N * (((lvl k).m : ℝ) / (lvl k).N / 2 - 1 / (2 * (lvl k).N)) := by
      field_simp
    rw [e, e2, abs_mul, abs_of_pos hN]
    exact mul_le_mul_of_nonneg_left hy hN.le
  obtain ⟨t, ht, hb⟩ := (stepX_spec k (lvl k)).2.2.2.2.1 l Y h1
  refine ⟨t, ht, ?_⟩
  rw [lam_succ, o_succ, N_succ_real]
  have e : y - ((lvl k).o + 1 / (4 * ((lvl k).N : ℝ)) + (t : ℝ) / (stepQ k (lvl k) * (lvl k).N)) =
      (Y - (1 / 4 + (t : ℝ) / stepQ k (lvl k))) / (lvl k).N := by
    rw [hY]; field_simp; ring
  have e2 : 1 / (2 * ((lvl k).N : ℝ)) / 2 - 1 / (2 * (stepQ k (lvl k) * (lvl k).N)) =
      (1 / 4 - 1 / (2 * (stepQ k (lvl k) : ℝ))) / (lvl k).N := by field_simp; ring
  rw [e, e2, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right hb hN.le

theorem crook (k : ℕ) (a : ℤ) :
    HPC.Fold.PatCrookedOn (fun u : ℕ => stepX k (lvl k) (a + u)) 0
      (⌈lam (k + 1) * (lvl (k + 1)).N⌉₊ + 3) := by
  rw [lam_mul, Nat.ceil_natCast]
  exact (stepX_spec k (lvl k)).2.2.2.2.2 a

end CircPlane

open CircPlane in
/-- **The circular description in the plane** (commission §6.2), as a definition. -/
noncomputable def planeDescr : CircDescr Pt where
  N k := (lvl k).N
  four_le k := (lvl k).hN
  L := link
  isOpen_L k t := (lvl k).Φ.isOpenMap _ (CircStd.isOpen_stdCircLink (N_ne k) t)
  periodic k t := by
    unfold link; rw [CircStd.stdCircLink_periodic (N_ne k)]
  meet_iff k s t := by
    unfold link
    rw [← image_inter (lvl k).Φ.injective, image_nonempty]
    exact stdCircLink_meet_iff (lvl k).hN s t
  preconn k t := (CircStd.isPreconnected_stdCircLink _ t).image _ (lvl k).Φ.continuous.continuousOn
  K := closedBall 0 (Real.exp 1)
  isCompact_K := isCompact_closedBall _ _
  L_subset k t := by
    obtain ⟨s, hs⟩ := link_sub_zero k t
    exact hs.trans (link_zero_sub s)
  ε k := 16 / 2 ^ k
  ε_tendsto := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 16
    simp only [mul_zero] at this
    refine this.congr fun k => ?_
    rw [one_div_pow]; ring
  diam_le := link_diam
  pat k := stepX k (lvl k)
  pat_period := pat_period
  pat_step k := (stepX_spec k (lvl k)).2.1
  nest k t := (stepψ_spec k (lvl k)).1 t
  tight k t l h := (stepψ_spec k (lvl k)).2.1 t l h
  o k := (lvl k).o
  lam := lam
  lam_tendsto := lam_tendsto
  five_le_lam k := by rw [lam_mul]; exact_mod_cast (lvl k).hm
  lam_add_four_le k := by rw [lam_mul]; exact_mod_cast (lvl k).hmN
  arcNest := arcNest
  surv := surv
  crook := crook

end HPC.BJ59
