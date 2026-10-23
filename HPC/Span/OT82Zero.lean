import HPC.Moore.Borsuk

/-!
# Batch 192, §4: a common zero on a rectangle (commission 192 §4)

`common_zero_rect`: two functions on `[0, 1] × [p, q]` with the boundary signs of the commission
have a common zero. Proof: otherwise `Φ = φ + iψ` has a continuous logarithm on the rectangle
(`HPC.Moore.exists_log_of_convex`); its imaginary part `θ` is a continuous argument, normalised by
`θ(0, q) = 0`. Going around the boundary (left side, top row, right side, bottom row), on each side
`Φ` avoids one ray, so `θ` stays in one open interval of length `2π`, and the corners pin the
interval of the next side:

* left side (`φ, ψ ≥ 0`, so `θ ≢ π`): `θ ∈ (−π, π)`, and at `(0, p)` (`φ = 0`, `ψ > 0`) `θ > 0`;
* top row (`ψ ≤ 0`, so `θ ≢ π/2`): `θ ∈ (−3π/2, π/2)`; at `(1, q)`, `φ ≤ 0` forces `θ ≤ −π/2`;
* right side (`φ ≤ 0`, so `θ ≢ π/4`): `θ ∈ (−7π/4, π/4)`; at `(1, p)`, `φ ≤ 0` forces `θ ≤ −π/2`;
* bottom row (`φ ≤ 0`, so `θ ≢ 0`): `θ ∈ (−2π, 0)`, contradicting `θ(0, p) > 0`.

This is the commission's argument with the integers `k₁, …, k₄` replaced by the normalisation and
the intervals.
-/

namespace HPC.Span

open Set Topology Metric Filter Real

/-- A continuous real function on a preconnected set that avoids both ends of an open interval and
takes one value inside it stays inside it. -/
theorem mem_Ioo_of_avoid {E : Type*} [TopologicalSpace E] {S : Set E} (hS : IsPreconnected S)
    {θ : E → ℝ} (hθ : ContinuousOn θ S) {lo hi : ℝ} (hlo : ∀ z ∈ S, θ z ≠ lo)
    (hhi : ∀ z ∈ S, θ z ≠ hi) {z₀ : E} (hz₀ : z₀ ∈ S) (h0 : θ z₀ ∈ Ioo lo hi) :
    ∀ z ∈ S, θ z ∈ Ioo lo hi := by
  have hI := hS.image θ hθ
  intro z hz
  by_contra hn
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hn
  rcases hn with h | h
  · obtain ⟨w, hw, hwe⟩ := hI.Icc_subset (mem_image_of_mem θ hz) (mem_image_of_mem θ hz₀)
      ⟨h, h0.1.le⟩
    exact hlo w hw hwe
  · obtain ⟨w, hw, hwe⟩ := hI.Icc_subset (mem_image_of_mem θ hz₀) (mem_image_of_mem θ hz)
      ⟨h0.2.le, h⟩
    exact hhi w hw hwe

/-- **§4**: two functions on `[0, 1] × [p, q]`, both `≥ 0` on the left side and `≤ 0` on the right
side, the first `≤ 0` on the bottom row and the second `≤ 0` on the top row, have a common zero. -/
theorem common_zero_rect {p q : ℝ} (hpq : p < q) {φ ψ : ℝ × ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 1 ×ˢ Icc p q)) (hψ : ContinuousOn ψ (Icc 0 1 ×ˢ Icc p q))
    (hl : ∀ u ∈ Icc p q, 0 ≤ φ (0, u) ∧ 0 ≤ ψ (0, u))
    (hr : ∀ u ∈ Icc p q, φ (1, u) ≤ 0 ∧ ψ (1, u) ≤ 0)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, φ (t, p) ≤ 0) (ht : ∀ t ∈ Icc (0 : ℝ) 1, ψ (t, q) ≤ 0) :
    ∃ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc p q, φ z = 0 ∧ ψ z = 0 := by
  by_contra hno
  push_neg at hno
  set R : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc p q
  set Φ : ℝ × ℝ → ℂ := fun z => (φ z : ℂ) + (ψ z : ℂ) * Complex.I
  have hΦre : ∀ z, (Φ z).re = φ z := fun z => by simp [Φ]
  have hΦim : ∀ z, (Φ z).im = ψ z := fun z => by simp [Φ]
  have hΦc : ContinuousOn Φ R :=
    (Complex.continuous_ofReal.comp_continuousOn hφ).add
      ((Complex.continuous_ofReal.comp_continuousOn hψ).mul continuousOn_const)
  have hΦne : ∀ z ∈ R, Φ z ≠ 0 := fun z hz h0 =>
    hno z hz (by rw [← hΦre, h0, Complex.zero_re]) (by rw [← hΦim, h0, Complex.zero_im])
  have hRc : Convex ℝ R := (convex_Icc _ _).prod (convex_Icc _ _)
  obtain ⟨g, hgc, hg⟩ := HPC.Moore.exists_log_of_convex hRc hΦc hΦne
  have hpq' : p ≤ q := hpq.le
  have c1 : ((0 : ℝ), p) ∈ R := ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hpq'⟩⟩
  have c2 : ((1 : ℝ), p) ∈ R := ⟨⟨zero_le_one, le_rfl⟩, ⟨le_rfl, hpq'⟩⟩
  have c3 : ((1 : ℝ), q) ∈ R := ⟨⟨zero_le_one, le_rfl⟩, ⟨hpq', le_rfl⟩⟩
  have c4 : ((0 : ℝ), q) ∈ R := ⟨⟨le_rfl, zero_le_one⟩, ⟨hpq', le_rfl⟩⟩
  -- the normalised logarithm
  have hφ4 : 0 < φ (0, q) := by
    have h1 := (hl q ⟨hpq', le_rfl⟩)
    have h2 := ht 0 ⟨le_rfl, zero_le_one⟩
    have hψ0 : ψ (0, q) = 0 := le_antisymm h2 h1.2
    exact lt_of_le_of_ne h1.1 (fun h => hno _ c4 h.symm hψ0)
  set g' : ℝ × ℝ → ℂ := fun z => g z - g (0, q) + Complex.log (Φ (0, q))
  have hg' : ∀ z ∈ R, Complex.exp (g' z) = Φ z := by
    intro z hz
    simp only [g', Complex.exp_add, Complex.exp_sub, hg z hz, hg _ c4,
      Complex.exp_log (hΦne _ c4)]
    field_simp [hΦne _ c4]
  set θ : ℝ × ℝ → ℝ := fun z => (g' z).im
  have hθc : ContinuousOn θ R :=
    Complex.continuous_im.comp_continuousOn ((hgc.sub continuousOn_const).add continuousOn_const)
  have hθ4 : θ (0, q) = 0 := by
    simp only [θ, g', sub_self, zero_add, Complex.log_im]
    have : Φ (0, q) = ((φ (0, q) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hΦre, hΦim]
      have h1 := (hl q ⟨hpq', le_rfl⟩)
      exact le_antisymm (ht 0 ⟨le_rfl, zero_le_one⟩) h1.2
    rw [this, Complex.arg_ofReal_of_nonneg hφ4.le]
  have hcos : ∀ z ∈ R, φ z = Real.exp (g' z).re * Real.cos (θ z) := fun z hz => by
    rw [← hΦre, ← hg' z hz, Complex.exp_re]
  have hsin : ∀ z ∈ R, ψ z = Real.exp (g' z).re * Real.sin (θ z) := fun z hz => by
    rw [← hΦim, ← hg' z hz, Complex.exp_im]
  have hcos_pos : ∀ z ∈ R, 0 < Real.cos (θ z) → 0 < φ z := fun z hz h => by
    rw [hcos z hz]; exact mul_pos (Real.exp_pos _) h
  have hcos_nonpos : ∀ z ∈ R, φ z ≤ 0 → Real.cos (θ z) ≤ 0 := fun z hz h => by
    by_contra h'; exact absurd h (not_le.2 (hcos_pos z hz (lt_of_not_ge h')))
  have hsin_pos : ∀ z ∈ R, 0 < Real.sin (θ z) → 0 < ψ z := fun z hz h => by
    rw [hsin z hz]; exact mul_pos (Real.exp_pos _) h
  -- the four sides
  have hsub : ∀ {A : Set ℝ} {B : Set ℝ}, A ⊆ Icc 0 1 → B ⊆ Icc p q → A ×ˢ B ⊆ R :=
    fun hA hB => prod_mono hA hB
  set L : Set (ℝ × ℝ) := {(0 : ℝ)} ×ˢ Icc p q
  set T : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ {q}
  set Rt : Set (ℝ × ℝ) := {(1 : ℝ)} ×ˢ Icc p q
  set Bo : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ {p}
  have hLR : L ⊆ R := hsub (singleton_subset_iff.2 ⟨le_rfl, zero_le_one⟩) subset_rfl
  have hTR : T ⊆ R := hsub subset_rfl (singleton_subset_iff.2 ⟨hpq', le_rfl⟩)
  have hRtR : Rt ⊆ R := hsub (singleton_subset_iff.2 ⟨zero_le_one, le_rfl⟩) subset_rfl
  have hBoR : Bo ⊆ R := hsub subset_rfl (singleton_subset_iff.2 ⟨le_rfl, hpq'⟩)
  have hLc : IsPreconnected L := isPreconnected_singleton.prod isPreconnected_Icc
  have hTc : IsPreconnected T := isPreconnected_Icc.prod isPreconnected_singleton
  have hRtc : IsPreconnected Rt := isPreconnected_singleton.prod isPreconnected_Icc
  have hBoc : IsPreconnected Bo := isPreconnected_Icc.prod isPreconnected_singleton
  -- left side: `θ ∈ (−π, π)`
  have hcosπ : ∀ k : ℤ, Real.cos (π + 2 * π * k) = -1 := fun k => by
    rw [show π + 2 * π * k = π + (k : ℝ) * (2 * π) by ring, Real.cos_add_int_mul_two_pi,
      Real.cos_pi]
  have hLavoid : ∀ z ∈ L, ∀ x : ℝ, Real.cos x = -1 → θ z ≠ x := by
    rintro ⟨z1, z2⟩ hz x hx hθ
    have hzR := hLR hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [mem_singleton_iff] at hz1 hz2
    have h1 := hcos _ hzR
    rw [hθ, hx] at h1
    have h2 := (hl z2 hz2).1
    rw [← hz1] at h2
    have := Real.exp_pos (g' (z1, z2)).re
    nlinarith
  have hL : ∀ z ∈ L, θ z ∈ Ioo (-π) π :=
    mem_Ioo_of_avoid hLc (hθc.mono hLR)
      (fun z hz => hLavoid z hz _ (by rw [Real.cos_neg, Real.cos_pi]))
      (fun z hz => hLavoid z hz _ Real.cos_pi) (z₀ := (0, q)) ⟨rfl, hpq', le_rfl⟩
      (by rw [hθ4]; exact ⟨neg_lt_zero.2 Real.pi_pos, Real.pi_pos⟩)
  have hθ1 : 0 < θ (0, p) := by
    have hφ1 : φ (0, p) = 0 := le_antisymm (hb 0 ⟨le_rfl, zero_le_one⟩) (hl p ⟨le_rfl, hpq'⟩).1
    have hψ1 : 0 < ψ (0, p) :=
      lt_of_le_of_ne (hl p ⟨le_rfl, hpq'⟩).2 (fun h => hno _ c1 hφ1 h.symm)
    have hI := hL (0, p) ⟨rfl, le_rfl, hpq'⟩
    by_contra hle
    push_neg at hle
    have : Real.sin (θ (0, p)) ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hle hI.1.le
    rw [hsin _ c1] at hψ1
    have := Real.exp_pos (g' (0, p)).re
    nlinarith
  -- top row: `θ ∈ (−3π/2, π/2)`
  have hTavoid : ∀ z ∈ T, ∀ x : ℝ, Real.sin x = 1 → θ z ≠ x := by
    rintro ⟨z1, z2⟩ hz x hx hθ
    have hzR := hTR hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [mem_singleton_iff] at hz1 hz2
    have h1 := hsin_pos _ hzR (by rw [hθ, hx]; exact one_pos)
    have h2 := ht z1 hz1
    rw [← hz2] at h2
    linarith
  have hT : ∀ z ∈ T, θ z ∈ Ioo (-(3 * π / 2)) (π / 2) :=
    mem_Ioo_of_avoid hTc (hθc.mono hTR)
      (fun z hz => hTavoid z hz _ (by
        rw [show -(3 * π / 2) = π / 2 + ((-1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
          Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]))
      (fun z hz => hTavoid z hz _ Real.sin_pi_div_two) (z₀ := (0, q))
      ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
      (by rw [hθ4]; constructor <;> linarith [Real.pi_pos])
  have hθ3 : θ (1, q) ∈ Ioo (-(3 * π / 2)) (-(π / 2) + π / 4) := by
    have hI := hT (1, q) ⟨⟨zero_le_one, le_rfl⟩, rfl⟩
    refine ⟨hI.1, ?_⟩
    by_contra h
    push_neg at h
    have hc := hcos_nonpos _ c3 (hr q ⟨hpq', le_rfl⟩).1
    have : 0 < Real.cos (θ (1, q)) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hI.2⟩
    linarith
  -- right side: `θ ∈ (−7π/4, π/4)`
  have hRtavoid : ∀ z ∈ Rt, ∀ k : ℤ, θ z ≠ π / 4 + k * (2 * π) := by
    rintro ⟨z1, z2⟩ hz k hθ
    have hzR := hRtR hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [mem_singleton_iff] at hz1 hz2
    have h1 := hcos_pos _ hzR (by
      rw [hθ, Real.cos_add_int_mul_two_pi, Real.cos_pi_div_four]; positivity)
    have h2 := (hr z2 hz2).1
    rw [← hz1] at h2
    linarith
  have hRt : ∀ z ∈ Rt, θ z ∈ Ioo (π / 4 + ((-1 : ℤ) : ℝ) * (2 * π)) (π / 4 + ((0 : ℤ) : ℝ) * (2 * π)) :=
    mem_Ioo_of_avoid hRtc (hθc.mono hRtR) (fun z hz => hRtavoid z hz (-1))
      (fun z hz => hRtavoid z hz 0) (z₀ := (1, q)) ⟨rfl, hpq', le_rfl⟩
      (by push_cast; constructor <;> linarith [hθ3.1, hθ3.2, Real.pi_pos])
  have hθ2 : θ (1, p) ∈ Ioo (-(2 * π)) (-(π / 2) + π / 4) := by
    have hI := hRt (1, p) ⟨rfl, le_rfl, hpq'⟩
    push_cast at hI
    refine ⟨by linarith [hI.1, Real.pi_pos], ?_⟩
    by_contra h
    push_neg at h
    have hc := hcos_nonpos _ c2 (hr p ⟨le_rfl, hpq'⟩).1
    have : 0 < Real.cos (θ (1, p)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hI.2, Real.pi_pos]⟩
    linarith
  -- bottom row: `θ ∈ (−2π, 0)`
  have hBoavoid : ∀ z ∈ Bo, ∀ k : ℤ, θ z ≠ k * (2 * π) := by
    rintro ⟨z1, z2⟩ hz k hθ
    have hzR := hBoR hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [mem_singleton_iff] at hz1 hz2
    have h1 := hcos_pos _ hzR (by rw [hθ, Real.cos_int_mul_two_pi]; exact one_pos)
    have h2 := hb z1 hz1
    rw [← hz2] at h2
    linarith
  have hBo : ∀ z ∈ Bo, θ z ∈ Ioo (((-1 : ℤ) : ℝ) * (2 * π)) (((0 : ℤ) : ℝ) * (2 * π)) :=
    mem_Ioo_of_avoid hBoc (hθc.mono hBoR) (fun z hz => hBoavoid z hz (-1))
      (fun z hz => hBoavoid z hz 0) (z₀ := (1, p)) ⟨⟨zero_le_one, le_rfl⟩, rfl⟩
      (by push_cast; constructor <;> linarith [hθ2.1, hθ2.2, Real.pi_pos])
  have := hBo (0, p) ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  push_cast at this
  linarith [this.2]

end HPC.Span
