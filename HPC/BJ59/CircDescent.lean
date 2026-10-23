import HPC.BJ59.CircCover

/-!
# Batch 202, §5: descent of an equivariant homeomorphism of the cover to the plane

`E N (u, v) = exp (v + i π u / N)` covers `ℂ ∖ {0}`, with deck translations `u ↦ u + 2N`. A
homeomorphism `G` of `ℝ × ℝ` with `G (u + 2N₁, v) = G (u, v) + (2N₂, 0)` descends to a map of
`ℂ ∖ {0}` (`E N₂ ∘ G = ψ ∘ E N₁`), continuous because `E` has continuous local sections (the
principal logarithm, and the logarithm of `−w` shifted by `π`). If the second coordinate of `G`
is at most `a v + K` with `a > 0`, the map extends continuously by `0 ↦ 0`; with the same
condition on `G⁻¹`, the extension is a homeomorphism of `ℂ` (`descHomeo`).
-/

namespace HPC.BJ59

open Set Topology Filter Complex

namespace Descent

/-- The covering map `(u, v) ↦ exp (v + i π u / N)`. -/
noncomputable def E (N : ℝ) (p : ℝ × ℝ) : ℂ := Complex.exp ((p.2 : ℂ) + ((Real.pi * p.1 / N : ℝ) : ℂ) * I)

/-- The principal lift. -/
noncomputable def lift (N : ℝ) (w : ℂ) : ℝ × ℝ := (N / Real.pi * arg w, Real.log ‖w‖)

/-- The lift through `−w`. -/
noncomputable def lift' (N : ℝ) (w : ℂ) : ℝ × ℝ := (N / Real.pi * (arg (-w) + Real.pi), Real.log ‖w‖)

variable {N : ℝ}

theorem continuous_E : Continuous (E N) := by unfold E; fun_prop

theorem E_ne_zero (p : ℝ × ℝ) : E N p ≠ 0 := Complex.exp_ne_zero _

theorem norm_E (p : ℝ × ℝ) : ‖E N p‖ = Real.exp p.2 := by
  unfold E; rw [Complex.norm_exp]; simp

theorem E_lift (hN : N ≠ 0) {w : ℂ} (hw : w ≠ 0) : E N (lift N w) = w := by
  unfold E lift
  have e : ((Real.log ‖w‖ : ℝ) : ℂ) + ((Real.pi * (N / Real.pi * arg w) / N : ℝ) : ℂ) * I =
      Complex.log w := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add, Complex.log_im]
      field_simp
  simp only
  rw [e, Complex.exp_log hw]

theorem E_lift' (hN : N ≠ 0) {w : ℂ} (hw : w ≠ 0) : E N (lift' N w) = w := by
  unfold E lift'
  have hw' : -w ≠ 0 := neg_ne_zero.mpr hw
  have e : ((Real.log ‖w‖ : ℝ) : ℂ) +
      ((Real.pi * (N / Real.pi * (arg (-w) + Real.pi)) / N : ℝ) : ℂ) * I =
      Complex.log (-w) + Real.pi * I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add, Complex.log_im]
      field_simp
  simp only
  rw [e, Complex.exp_add, Complex.exp_log hw', Complex.exp_pi_mul_I]; ring

theorem E_add_int (hN : N ≠ 0) (p : ℝ × ℝ) (k : ℤ) : E N (p.1 + 2 * N * k, p.2) = E N p := by
  unfold E
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only
  push_cast
  field_simp
  ring

theorem E_eq_imp (hN : N ≠ 0) {p q : ℝ × ℝ} (h : E N p = E N q) :
    ∃ k : ℤ, p = (q.1 + 2 * N * k, q.2) := by
  unfold E at h
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  have hre := congrArg Complex.re hk
  have him := congrArg Complex.im hk
  simp at hre him
  refine ⟨k, Prod.ext ?_ hre⟩
  simp only
  have hpi := Real.pi_pos
  field_simp at him
  nlinarith [him]

theorem continuousAt_lift {w : ℂ} (hw : w ∈ slitPlane) : ContinuousAt (lift N) w := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  unfold lift
  refine ContinuousAt.prodMk ((continuousAt_arg hw).const_mul _) ?_
  exact (Real.continuousAt_log (norm_ne_zero_iff.mpr hw0)).comp continuous_norm.continuousAt

theorem continuousAt_lift' {w : ℂ} (hw : -w ∈ slitPlane) : ContinuousAt (lift' N) w := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, neg_zero] at hw; exact slitPlane_ne_zero hw rfl
  unfold lift'
  refine ContinuousAt.prodMk ?_ ?_
  · exact (((continuousAt_arg hw).comp continuous_neg.continuousAt).add continuousAt_const).const_mul _
  · exact (Real.continuousAt_log (norm_ne_zero_iff.mpr hw0)).comp continuous_norm.continuousAt

/-! ### The descended map -/

section Desc

variable (G : ℝ × ℝ ≃ₜ ℝ × ℝ) {N₁ N₂ : ℝ}

/-- The descended map, extended by `0 ↦ 0`. -/
noncomputable def desc (N₁ N₂ : ℝ) (w : ℂ) : ℂ := if w = 0 then 0 else E N₂ (G (lift N₁ w))

variable {G}

theorem G_add_int (hG : ∀ p : ℝ × ℝ, G (p.1 + 2 * N₁, p.2) = G p + (2 * N₂, 0)) (p : ℝ × ℝ)
    (k : ℤ) : G (p.1 + 2 * N₁ * k, p.2) = G p + (2 * N₂ * k, 0) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
      push_cast at ih ⊢
      have := hG (p.1 + 2 * N₁ * k, p.2)
      simp only at this
      rw [show p.1 + 2 * N₁ * ((k : ℝ) + 1) = p.1 + 2 * N₁ * k + 2 * N₁ by ring, this, ih]
      ext <;> simp; ring
  | pred k ih =>
      push_cast at ih ⊢
      have := hG (p.1 + 2 * N₁ * (-(k : ℝ) - 1), p.2)
      simp only at this
      rw [show p.1 + 2 * N₁ * (-(k : ℝ) - 1) + 2 * N₁ = p.1 + 2 * N₁ * (-(k : ℝ)) by ring,
        ih] at this
      have h2 : G (p.1 + 2 * N₁ * (-(k : ℝ) - 1), p.2) = G p + (2 * N₂ * (-(k : ℝ)), 0) -
          (2 * N₂, 0) := by rw [this]; abel
      rw [h2]; ext <;> simp; ring

variable (hN₁ : N₁ ≠ 0) (hN₂ : N₂ ≠ 0)
  (hG : ∀ p : ℝ × ℝ, G (p.1 + 2 * N₁, p.2) = G p + (2 * N₂, 0))
include hN₁ hN₂ hG

theorem desc_E (p : ℝ × ℝ) : desc G N₁ N₂ (E N₁ p) = E N₂ (G p) := by
  unfold desc
  rw [if_neg (E_ne_zero p)]
  obtain ⟨k, hk⟩ := E_eq_imp hN₁ (E_lift hN₁ (E_ne_zero p))
  rw [hk, G_add_int hG]
  have := E_add_int hN₂ (G p) k
  rw [← this]; congr 1; ext <;> simp

theorem desc_of_E {w : ℂ} {q : ℝ × ℝ} (hq : E N₁ q = w) : desc G N₁ N₂ w = E N₂ (G q) := by
  rw [← hq, desc_E hN₁ hN₂ hG]

theorem continuousAt_desc {w : ℂ} (hw : w ≠ 0) : ContinuousAt (desc G N₁ N₂) w := by
  have hev : ∀ᶠ w' in 𝓝 w, w' ≠ 0 := isOpen_ne.mem_nhds hw
  by_cases hs : w ∈ slitPlane
  · refine ((((continuous_E (N := N₂)).comp G.continuous).continuousAt).comp
      (continuousAt_lift (N := N₁) hs)).congr ?_
    filter_upwards [hev] with w' hw'
    simp only [Function.comp, desc, if_neg hw']
  · have hs' : -w ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hs ⊢
      push_neg at hs
      left
      have : w.re ≠ 0 := by
        intro h; exact hw (Complex.ext h (by simpa using hs.2))
      simp only [neg_re]; exact neg_pos.mpr (lt_of_le_of_ne hs.1 this)
    refine ((((continuous_E (N := N₂)).comp G.continuous).continuousAt).comp
      (continuousAt_lift' (N := N₁) hs')).congr ?_
    filter_upwards [hev] with w' hw'
    exact (desc_of_E hN₁ hN₂ hG (E_lift' hN₁ hw')).symm

omit hN₁ hN₂ hG in
theorem desc_zero : desc G N₁ N₂ 0 = 0 := by simp [desc]

omit hN₂ hG in
theorem continuousAt_desc_zero (hb : ∃ a K : ℝ, 0 < a ∧ ∀ p, (G p).2 ≤ a * p.2 + K) :
    ContinuousAt (desc G N₁ N₂) 0 := by
  obtain ⟨a, K, ha, hb⟩ := hb
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨Real.exp ((Real.log ε - K) / a), Real.exp_pos _, fun w hw => ?_⟩
  rw [desc_zero, dist_zero_right]
  by_cases hw0 : w = 0
  · rw [hw0, desc_zero, norm_zero]; exact hε
  · rw [dist_zero_right] at hw
    simp only [desc, if_neg hw0]
    rw [norm_E]
    have hl : Real.log ‖w‖ < (Real.log ε - K) / a :=
      (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hw0)).mpr hw
    have h1 := hb (lift N₁ w)
    have h2 : a * Real.log ‖w‖ + K < Real.log ε := by
      rw [lt_div_iff₀ ha] at hl; linarith
    calc Real.exp (G (lift N₁ w)).2 ≤ Real.exp (a * Real.log ‖w‖ + K) :=
          Real.exp_le_exp.mpr (by simpa [lift] using h1)
      _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr h2
      _ = ε := Real.exp_log hε

theorem continuous_desc (hb : ∃ a K : ℝ, 0 < a ∧ ∀ p, (G p).2 ≤ a * p.2 + K) :
    Continuous (desc G N₁ N₂) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · rw [hw]; exact continuousAt_desc_zero hN₁ hb
  · exact continuousAt_desc hN₁ hN₂ hG hw

/-- **The descended homeomorphism** of `ℂ`: `descHomeo (E N₁ p) = E N₂ (G p)`. -/
noncomputable def descHomeo
    (hG' : ∀ q : ℝ × ℝ, G.symm (q.1 + 2 * N₂, q.2) = G.symm q + (2 * N₁, 0))
    (hb : ∃ a K : ℝ, 0 < a ∧ ∀ p, (G p).2 ≤ a * p.2 + K)
    (hb' : ∃ a K : ℝ, 0 < a ∧ ∀ q, (G.symm q).2 ≤ a * q.2 + K) : ℂ ≃ₜ ℂ where
  toFun := desc G N₁ N₂
  invFun := desc G.symm N₂ N₁
  left_inv w := by
    by_cases hw : w = 0
    · rw [hw, desc_zero, desc_zero]
    · simp only [desc, if_neg hw]
      rw [if_neg (E_ne_zero _)]
      have := desc_E (G := G.symm) hN₂ hN₁ hG' (G (lift N₁ w))
      simp only [desc, if_neg (E_ne_zero _)] at this
      rw [this, Homeomorph.symm_apply_apply, E_lift hN₁ hw]
  right_inv w := by
    by_cases hw : w = 0
    · rw [hw, desc_zero, desc_zero]
    · simp only [desc, if_neg hw]
      rw [if_neg (E_ne_zero _)]
      have := desc_E (G := G) hN₁ hN₂ hG (G.symm (lift N₂ w))
      simp only [desc, if_neg (E_ne_zero _)] at this
      rw [this, Homeomorph.apply_symm_apply, E_lift hN₂ hw]
  continuous_toFun := continuous_desc hN₁ hN₂ hG hb
  continuous_invFun := continuous_desc (G := G.symm) hN₂ hN₁ hG' hb'

theorem descHomeo_E
    (hG' : ∀ q : ℝ × ℝ, G.symm (q.1 + 2 * N₂, q.2) = G.symm q + (2 * N₁, 0))
    (hb : ∃ a K : ℝ, 0 < a ∧ ∀ p, (G p).2 ≤ a * p.2 + K)
    (hb' : ∃ a K : ℝ, 0 < a ∧ ∀ q, (G.symm q).2 ≤ a * q.2 + K) (p : ℝ × ℝ) :
    descHomeo hN₁ hN₂ hG hG' hb hb' (E N₁ p) = E N₂ (G p) := desc_E hN₁ hN₂ hG p

end Desc

end Descent

end HPC.BJ59
