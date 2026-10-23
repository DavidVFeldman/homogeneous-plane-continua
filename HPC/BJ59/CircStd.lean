import HPC.BJ59.CircDescent
import HPC.Plane.StdChain

/-!
# Batch 202: the standard circular chains

The definitions of commission 202 §5 (moved here from the skeleton `BJ59E.lean`, textually
unchanged): `stdRectZ`, `zoneZ`, `circExp`, `stdCircLink`, `stdCircZone`, and the facts about them
used by the circular planar step and the assembly. `circExp N` is read through the complex
exponential `Descent.E N` of `CircDescent.lean`.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane

/-- The standard rectangle `(2t, 2t + 3) × (0, 1)`, for an integer `t`. -/
def stdRectZ (t : ℤ) : Set Pt := Ioo (2 * (t : ℝ)) (2 * t + 3) ×ˢ Ioo 0 1

/-- The overlap zone of `stdRectZ t` and `stdRectZ (t + 1)`, widened as batch 84's `zone`. -/
def zoneZ (t : ℤ) : Set Pt := Icc (2 * (t : ℝ) + 8 / 5) (2 * t + 17 / 5) ×ˢ Icc 0 1

/-- The covering map of the plane minus the origin, of period `2N` in the first coordinate:
`(u, v) ↦ e^v (cos (π u / N), sin (π u / N))`. -/
noncomputable def circExp (N : ℕ) (p : Pt) : Pt :=
  (Real.exp p.2 * Real.cos (Real.pi * p.1 / N), Real.exp p.2 * Real.sin (Real.pi * p.1 / N))

/-- Link `t` of the standard circular chain of `N` links: a polar rectangle. -/
noncomputable def stdCircLink (N : ℕ) (t : ℤ) : Set Pt := circExp N '' stdRectZ t

/-- Zone `t` of the standard circular chain of `N` links. -/
noncomputable def stdCircZone (N : ℕ) (t : ℤ) : Set Pt := circExp N '' zoneZ t

namespace CircStd

/-- The identification of `ℂ` with the plane. -/
noncomputable def cpx : ℂ ≃ₜ Pt := Complex.equivRealProdCLM.toHomeomorph

theorem cpx_apply (z : ℂ) : cpx z = (z.re, z.im) := rfl

theorem circExp_eq (N : ℕ) (p : Pt) : circExp N p = cpx (Descent.E N p) := by
  rw [cpx_apply]
  unfold circExp Descent.E
  ext
  · simp only [Complex.exp_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im]
    ring_nf
  · simp only [Complex.exp_im, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im]
    ring_nf

theorem continuous_circExp (N : ℕ) : Continuous (circExp N) := by
  unfold circExp; fun_prop

theorem circExp_add_int {N : ℕ} (hN : N ≠ 0) (p : Pt) (k : ℤ) :
    circExp N (p.1 + 2 * N * k, p.2) = circExp N p := by
  rw [circExp_eq, circExp_eq, Descent.E_add_int (by exact_mod_cast hN)]

theorem circExp_eq_imp {N : ℕ} (hN : N ≠ 0) {p q : Pt} (h : circExp N p = circExp N q) :
    ∃ k : ℤ, p = (q.1 + 2 * N * k, q.2) := by
  rw [circExp_eq, circExp_eq] at h
  exact Descent.E_eq_imp (by exact_mod_cast hN) (cpx.injective h)

/-- The linear part of `E N`. -/
noncomputable def linE {N : ℕ} (hN : N ≠ 0) : Pt ≃ₜ ℂ where
  toFun p := (p.2 : ℂ) + ((Real.pi * p.1 / N : ℝ) : ℂ) * Complex.I
  invFun z := (N * z.im / Real.pi, z.re)
  left_inv p := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have := Real.pi_pos
    ext <;> simp; field_simp
  right_inv z := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have := Real.pi_pos
    apply Complex.ext <;> simp; field_simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isOpenMap_circExp {N : ℕ} (hN : N ≠ 0) : IsOpenMap (circExp N) := by
  have e : circExp N = cpx ∘ Complex.exp ∘ linE hN := by
    funext p; rw [circExp_eq]; rfl
  rw [e]
  exact cpx.isOpenMap.comp (Complex.isOpenMap_exp.comp (linE hN).isOpenMap)

theorem isOpen_stdRectZ (t : ℤ) : IsOpen (stdRectZ t) := isOpen_Ioo.prod isOpen_Ioo

theorem closure_stdRectZ (t : ℤ) :
    closure (stdRectZ t) = Icc (2 * (t : ℝ)) (2 * t + 3) ×ˢ Icc 0 1 := by
  rw [stdRectZ, closure_prod_eq, closure_Ioo (by linarith), closure_Ioo (by norm_num)]

theorem isPreconnected_stdRectZ (t : ℤ) : IsPreconnected (stdRectZ t) :=
  isPreconnected_Ioo.prod isPreconnected_Ioo

theorem isOpen_stdCircLink {N : ℕ} (hN : N ≠ 0) (t : ℤ) : IsOpen (stdCircLink N t) :=
  isOpenMap_circExp hN _ (isOpen_stdRectZ t)

theorem isPreconnected_stdCircLink (N : ℕ) (t : ℤ) : IsPreconnected (stdCircLink N t) :=
  (isPreconnected_stdRectZ t).image _ (continuous_circExp N).continuousOn

theorem stdCircLink_periodic {N : ℕ} (hN : N ≠ 0) (t : ℤ) :
    stdCircLink N (t + N) = stdCircLink N t := by
  ext q
  simp only [stdCircLink, mem_image, stdRectZ, mem_prod, mem_Ioo]
  constructor
  · rintro ⟨p, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    refine ⟨(p.1 + 2 * N * (-1 : ℤ), p.2), ⟨⟨?_, ?_⟩, h3⟩, circExp_add_int hN p (-1)⟩ <;>
      push_cast at h1 h2 ⊢ <;> linarith
  · rintro ⟨p, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    refine ⟨(p.1 + 2 * N * (1 : ℤ), p.2), ⟨⟨?_, ?_⟩, h3⟩, circExp_add_int hN p 1⟩ <;>
      push_cast at h1 h2 ⊢ <;> linarith

/-- `stdCircLink_meet_iff` for every `N > 0`. -/
theorem stdCircLink_meet_iff' {N : ℕ} (hN : N ≠ 0) (s t : ℤ) :
    (stdCircLink N s ∩ stdCircLink N t).Nonempty ↔ ∃ n : ℤ, |s - t - n * (N : ℤ)| ≤ 1 := by
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, ⟨p', hp', e⟩⟩
    obtain ⟨k, hk⟩ := circExp_eq_imp hN e.symm
    simp only [stdRectZ, mem_prod, mem_Ioo] at hp hp'
    rw [hk] at hp
    simp only at hp
    refine ⟨k, ?_⟩
    have a1 : ((s - t - k * N : ℤ) : ℝ) < 3 / 2 := by push_cast; linarith
    have a2 : (-3 / 2 : ℝ) < ((s - t - k * N : ℤ) : ℝ) := by push_cast; linarith
    have b1 : s - t - k * N < 2 := by exact_mod_cast (by linarith : ((s - t - k * N : ℤ) : ℝ) < 2)
    have b2 : -2 < s - t - k * N := by
      exact_mod_cast (by linarith : (-2 : ℝ) < ((s - t - k * N : ℤ) : ℝ))
    rw [abs_le]; constructor <;> omega
  · rintro ⟨n, hn⟩
    rw [abs_le] at hn
    have h1 : ((-1 : ℤ) : ℝ) ≤ ((s - t - n * N : ℤ) : ℝ) := by exact_mod_cast hn.1
    have h2 : ((s - t - n * N : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast hn.2
    push_cast at h1 h2
    set u : ℝ := s + (t + n * N) + 3 / 2
    refine ⟨circExp N (u, 1 / 2), ⟨(u, 1 / 2), ?_, rfl⟩, ⟨(u + 2 * N * (-n : ℤ), 1 / 2), ?_, ?_⟩⟩
    · simp only [stdRectZ, mem_prod, mem_Ioo, u]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · simp only [stdRectZ, mem_prod, mem_Ioo, u]; push_cast
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · exact circExp_add_int hN (u, 1 / 2) (-n)

end CircStd

/-- The standard circular chain is a circular chain. -/
theorem stdCircLink_meet_iff {N : ℕ} (hN : 4 ≤ N) (s t : ℤ) :
    (stdCircLink N s ∩ stdCircLink N t).Nonempty ↔ ∃ n : ℤ, |s - t - n * (N : ℤ)| ≤ 1 :=
  CircStd.stdCircLink_meet_iff' (by omega) s t

end HPC.BJ59
