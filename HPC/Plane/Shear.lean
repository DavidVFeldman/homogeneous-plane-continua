import Mathlib

/-!
# The folding homeomorphism: a composition of two shears

Batch 84. Given joint positions `P : ℕ → ℝ` for `n` fine links, a horizontal scale `β > 0` and a
vertical scale `C > 0`, the map

`Ψ (u, v) = (β u + h q, q)`,   `q = 1/4 + C u + (C/8) v`,

is a homeomorphism of the plane (a linear shear followed by the horizontal shear by the
continuous function `h`). The function `h` is piecewise linear in the height `q`: it is
constant, equal to `P t - 2βt`, while `u` runs over the overlap zone around joint `t`, and moves
linearly to the next value while `u` runs over the short window `[2t + 7/5, 2t + 8/5]` in the
middle of fine link `t`. Consequently the image of fine standard link `t` projects horizontally
into `[min (P t) (P (t+1)) - 2β, max (P t) (P (t+1)) + 3β]` and lies at heights in a band of
width about `3C`, and the image of the fine overlap zone around joint `t + 1` is a box of width
`2β` and height `2C` around `P (t+1)`.
-/

namespace HPC.Plane.Shear

open Finset

variable (n : ℕ) (P : ℕ → ℝ) (β C : ℝ)

/-- Value of the horizontal shift near joint `t`. -/
def Hh (t : ℕ) : ℝ := P t - 2 * β * t

/-- Start and end (in height) of the ramp inside fine link `t`. -/
noncomputable def σ (t : ℕ) : ℝ := 1 / 4 + C * (2 * t + 7 / 5) + C / 8
noncomputable def τ (t : ℕ) : ℝ := 1 / 4 + C * (2 * t + 8 / 5)

/-- The ramp of fine link `t`, from `0` to `1`. -/
noncomputable def θ (t : ℕ) (q : ℝ) : ℝ := max 0 (min 1 ((q - σ C t) / (τ C t - σ C t)))

/-- The horizontal shift, as a function of the height. -/
noncomputable def hfun (q : ℝ) : ℝ :=
  Hh P β 0 + ∑ s ∈ range n, (Hh P β (s + 1) - Hh P β s) * θ C s q

/-- The height coordinate. -/
noncomputable def hq (p : ℝ × ℝ) : ℝ := 1 / 4 + C * p.1 + C / 8 * p.2

theorem continuous_θ (t : ℕ) : Continuous (θ C t) := by
  unfold θ; fun_prop

theorem continuous_hfun : Continuous (hfun n P β C) := by
  unfold hfun
  refine continuous_const.add (continuous_finset_sum _ fun s _ => ?_)
  exact continuous_const.mul (continuous_θ C s)

variable {β C}

/-- The folding homeomorphism. -/
noncomputable def Ψ (hβ : β ≠ 0) (hC : C ≠ 0) : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun p := (β * p.1 + hfun n P β C (hq C p), hq C p)
  invFun p := ((p.1 - hfun n P β C p.2) / β,
    (p.2 - 1 / 4 - C * ((p.1 - hfun n P β C p.2) / β)) * 8 / C)
  left_inv p := by
    obtain ⟨u, v⟩ := p
    simp only [hq]
    ext
    · simp only; field_simp; ring
    · simp only; field_simp; ring
  right_inv p := by
    obtain ⟨X, Y⟩ := p
    have e : hq C ((X - hfun n P β C Y) / β,
        (Y - 1 / 4 - C * ((X - hfun n P β C Y) / β)) * 8 / C) = Y := by
      simp only [hq]; field_simp; ring
    ext
    · simp only [e]; field_simp; ring
    · simp only [e]
  continuous_toFun := by
    have hc := continuous_hfun n P β C
    unfold hq
    fun_prop
  continuous_invFun := by
    have hc := continuous_hfun n P β C
    fun_prop

theorem Ψ_apply (hβ : β ≠ 0) (hC : C ≠ 0) (p : ℝ × ℝ) :
    Ψ n P hβ hC p = (β * p.1 + hfun n P β C (hq C p), hq C p) := rfl

variable (hC : 0 < C)
include hC

theorem σ_lt_τ (t : ℕ) : σ C t < τ C t := by unfold σ τ; nlinarith

theorem θ_of_le {t : ℕ} {q : ℝ} (h : q ≤ σ C t) : θ C t q = 0 := by
  unfold θ
  have := σ_lt_τ hC t
  have : (q - σ C t) / (τ C t - σ C t) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [max_eq_left]; exact (min_le_right _ _).trans this

theorem θ_of_ge {t : ℕ} {q : ℝ} (h : τ C t ≤ q) : θ C t q = 1 := by
  unfold θ
  have := σ_lt_τ hC t
  have : 1 ≤ (q - σ C t) / (τ C t - σ C t) := by rw [le_div_iff₀ (by linarith)]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

omit hC in
theorem θ_mem (t : ℕ) (q : ℝ) : 0 ≤ θ C t q ∧ θ C t q ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

omit hC in
theorem τ_mono {s t : ℕ} (hC : 0 ≤ C) (h : s ≤ t) : τ C s ≤ τ C t := by
  unfold τ
  have : (s : ℝ) ≤ t := by exact_mod_cast h
  nlinarith

omit hC in
theorem σ_mono {s t : ℕ} (hC : 0 ≤ C) (h : s ≤ t) : σ C s ≤ σ C t := by
  unfold σ
  have : (s : ℝ) ≤ t := by exact_mod_cast h
  nlinarith

/-- Away from the other ramps, `h` is an interpolation between two consecutive values. -/
theorem hfun_eq {k : ℕ} (hk : k < n) {q : ℝ} (h1 : ∀ s < k, τ C s ≤ q) (h2 : ∀ s, k < s → q ≤ σ C s) :
    hfun n P β C q = Hh P β k + (Hh P β (k + 1) - Hh P β k) * θ C k q := by
  unfold hfun
  rw [← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ n by omega), Finset.sum_range_succ]
  have hI : ∑ s ∈ Finset.Ico (k + 1) n, (Hh P β (s + 1) - Hh P β s) * θ C s q = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [Finset.mem_Ico] at hs
    rw [θ_of_le hC (h2 s (by omega)), mul_zero]
  have hR : ∑ s ∈ Finset.range k, (Hh P β (s + 1) - Hh P β s) * θ C s q =
      ∑ s ∈ Finset.range k, (Hh P β (s + 1) - Hh P β s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [θ_of_ge hC (h1 s hs), mul_one]
  rw [hI, hR, Finset.sum_range_sub (fun s => Hh P β s)]
  ring

/-- The image of a point of (the closure of) fine standard link `t`. -/
theorem link_image {t : ℕ} (ht : t < n) (hβ : 0 < β) {u v : ℝ} (hu1 : 2 * (t : ℝ) ≤ u)
    (hu2 : u ≤ 2 * t + 3) (hv1 : 0 ≤ v) (hv2 : v ≤ 1) :
    min (P t) (P (t + 1)) - 2 * β ≤ β * u + hfun n P β C (hq C (u, v)) ∧
    β * u + hfun n P β C (hq C (u, v)) ≤ max (P t) (P (t + 1)) + 3 * β ∧
    1 / 4 + 2 * C * t ≤ hq C (u, v) ∧ hq C (u, v) ≤ 1 / 4 + C * (2 * t + 3) + C / 8 := by
  have hq1 : 1 / 4 + 2 * C * t ≤ hq C (u, v) := by unfold hq; simp only; nlinarith
  have hq2 : hq C (u, v) ≤ 1 / 4 + C * (2 * t + 3) + C / 8 := by unfold hq; simp only; nlinarith
  refine ⟨?_, ?_, hq1, hq2⟩ <;>
  · rw [hfun_eq n P hC ht (q := hq C (u, v))]
    rotate_left
    · intro s hs
      refine (τ_mono hC.le (show s ≤ t - 1 by omega)).trans ?_
      refine le_trans ?_ hq1
      unfold τ
      have : ((t - 1 : ℕ) : ℝ) = t - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; nlinarith
    · intro s hs
      refine le_trans ?_ (σ_mono hC.le (show t + 1 ≤ s by omega))
      refine hq2.trans ?_
      unfold σ; push_cast; nlinarith
    have hθ := θ_mem (C := C) t (hq C (u, v))
    unfold Hh
    push_cast
    set θ' := θ C t (hq C (u, v))
    have hmin1 := min_le_left (P t) (P (t + 1))
    have hmin2 := min_le_right (P t) (P (t + 1))
    have hmax1 := le_max_left (P t) (P (t + 1))
    have hmax2 := le_max_right (P t) (P (t + 1))
    nlinarith [mul_le_mul_of_nonneg_left hθ.1 hβ.le, mul_le_mul_of_nonneg_left hθ.2 hβ.le,
      mul_nonneg hθ.1 (sub_nonneg.mpr hmin1), mul_nonneg hθ.1 (sub_nonneg.mpr hmin2),
      mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hmin1),
      mul_nonneg hθ.1 (sub_nonneg.mpr hmax1), mul_nonneg hθ.1 (sub_nonneg.mpr hmax2),
      mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hmax1),
      mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hmin2),
      mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hmax2)]

/-- The image of a point of the fine overlap zone around joint `t + 1`. -/
theorem zone_image {t : ℕ} (ht : t < n) {u v : ℝ} (hu1 : 2 * (t : ℝ) + 8 / 5 ≤ u)
    (hu2 : u ≤ 2 * t + 17 / 5) (hv1 : 0 ≤ v) (hv2 : v ≤ 1) :
    β * u + hfun n P β C (hq C (u, v)) = P (t + 1) + β * (u - 2 * t - 2) ∧
    1 / 4 + C * (2 * t + 8 / 5) ≤ hq C (u, v) ∧ hq C (u, v) ≤ 1 / 4 + C * (2 * t + 17 / 5) + C / 8 := by
  have hq1 : 1 / 4 + C * (2 * t + 8 / 5) ≤ hq C (u, v) := by unfold hq; simp only; nlinarith
  have hq2 : hq C (u, v) ≤ 1 / 4 + C * (2 * t + 17 / 5) + C / 8 := by unfold hq; simp only; nlinarith
  refine ⟨?_, hq1, hq2⟩
  rw [hfun_eq n P hC ht (q := hq C (u, v)), θ_of_ge hC hq1]
  · unfold Hh; push_cast; ring
  · intro s hs
    exact (τ_mono hC.le (show s ≤ t by omega)).trans hq1
  · intro s hs
    refine le_trans ?_ (σ_mono hC.le (show t + 1 ≤ s by omega))
    refine hq2.trans ?_
    unfold σ; push_cast; nlinarith

end HPC.Plane.Shear
