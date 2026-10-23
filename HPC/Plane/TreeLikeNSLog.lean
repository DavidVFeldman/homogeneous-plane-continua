import HPC.Plane.Jct1

/-!
# Batch 133, helpers: logarithms of `z − p`

Helpers for `TreeLikeNS.lean`, items 2 and 3.

* `toCpx` (`Pt` as `ℂ`), moved here from the skeleton so that the helpers can use it.
* `sub_const_of_exp_eq`: two continuous logarithms of the same function on a preconnected set
  differ by a constant.
* `log_diff_edge`: along a segment `[a, b]` missing `p`, a continuous logarithm `L` of `z − p`
  changes by the principal logarithm `log ((p − b) / (p − a))`. The quotient
  `(p − γ t) / (p − a)` runs along the segment from `1` to `(p − b) / (p − a)`, which avoids the
  closed negative half-line (`slit_of_segment_ne_zero`).
* `arg_div_jump`: `arg (B / A) = arg B − arg A + 2π j`, `j ∈ {−1, 0, 1}`, and `j ≠ 0` exactly when
  `A`, `B` lie on opposite sides of the real axis in the half-open sense (`0 ≤ im` against
  `im < 0`) and the segment `[A, B]` crosses the *negative* real axis (sign of the cross product).
* `crossesEast_iff_cross`: with `A = p − a`, `B = p − b`, that condition is exactly
  `CrossesEast p a b` (the half-open conventions agree: `arg` takes values in `(−π, π]`, and
  `0 ≤ arg z ↔ 0 ≤ im z`).
-/

namespace HPC.Plane

open Set Real

/-- `Pt = ℝ × ℝ` as complex numbers. -/
def toCpx (z : Pt) : ℂ := ⟨z.1, z.2⟩

theorem continuous_toCpx : Continuous toCpx := by
  unfold toCpx
  exact Complex.equivRealProdCLM.symm.continuous.comp continuous_id |>.congr fun z => by
    apply Complex.ext <;> simp

theorem toCpx_injective : Function.Injective toCpx := fun a b h => by
  unfold toCpx at h
  exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)

theorem toCpx_lineMap (a b : Pt) (t : ℝ) :
    toCpx (AffineMap.lineMap a b t) = (1 - (t : ℂ)) * toCpx a + t * toCpx b := by
  rw [AffineMap.lineMap_apply_module]
  apply Complex.ext <;> simp [toCpx]

/-- **Two continuous logarithms differ by a constant** on a preconnected set: `f − g` is
continuous with values in `2πiℤ`. -/
theorem sub_const_of_exp_eq {α : Type*} [TopologicalSpace α] {S : Set α} (hS : IsPreconnected S)
    {f g : α → ℂ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (h : ∀ z ∈ S, Complex.exp (f z) = Complex.exp (g z)) {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    f x - g x = f y - g y := by
  have hk : ∀ z ∈ S, ∃ n : ℤ, f z - g z = n * (2 * π * Complex.I) := by
    intro z hz
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h z hz)
    exact ⟨n, by rw [hn]; ring⟩
  set k : α → ℝ := fun z => ((f z - g z) / (2 * π * Complex.I)).re
  have hkc : ContinuousOn k S :=
    Complex.continuous_re.comp_continuousOn ((hf.sub hg).div_const _)
  have hkint : ∀ z ∈ S, f z - g z = (k z : ℂ) * (2 * π * Complex.I) ∧ ∃ n : ℤ, k z = n := by
    intro z hz
    obtain ⟨n, hn⟩ := hk z hz
    have hne : (2 * π * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    have : k z = n := by simp only [k, hn, mul_div_assoc, div_self hne, mul_one]; simp
    exact ⟨by rw [this, hn]; push_cast; ring, n, this⟩
  suffices hkxy : k x = k y by rw [(hkint x hx).1, (hkint y hy).1, hkxy]
  have himg : IsPreconnected (k '' S) := hS.image k hkc
  have key : ∀ a ∈ S, ∀ b ∈ S, k a ≤ k b → k a = k b := by
    intro a ha b hb hab
    obtain ⟨m, hm⟩ := (hkint a ha).2
    obtain ⟨n, hn⟩ := (hkint b hb).2
    by_contra hne
    have hlt : m < n := by
      have : (m : ℝ) < n := by rw [← hm, ← hn]; exact lt_of_le_of_ne hab hne
      exact_mod_cast this
    have hmem : ((m : ℝ) + 1 / 2) ∈ k '' S := by
      refine himg.Icc_subset ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨by rw [hm]; linarith, ?_⟩
      rw [hn]; have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
      linarith
    obtain ⟨z, hz, hkz⟩ := hmem
    obtain ⟨l, hl⟩ := (hkint z hz).2
    rw [hl] at hkz
    have h1 : m < l := by
      have : (m : ℝ) < l := by linarith
      exact_mod_cast this
    have h2 : l < m + 1 := by
      have : (l : ℝ) < m + 1 := by linarith
      exact_mod_cast this
    omega
  rcases le_total (k x) (k y) with h | h
  · exact key x hx y hy h
  · exact (key y hy x hx h).symm

/-- The segment from `1` to `B / A` avoids the closed negative half-line when the segment from
`A` to `B` avoids `0`. -/
theorem slit_of_segment_ne_zero {A B : ℂ} (hA : A ≠ 0)
    (h : ∀ s ∈ Icc (0:ℝ) 1, (1 - (s:ℂ)) * A + s * B ≠ 0) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ((1 - (t:ℂ)) * A + t * B) / A ∈ Complex.slitPlane := by
  set u := B / A with hu
  have hw : ((1 - (t:ℂ)) * A + t * B) / A = (1 - t) + t * u := by
    rw [hu]; field_simp
  rw [hw, Complex.mem_slitPlane_iff]
  by_contra hc
  push_neg at hc
  obtain ⟨hre, him⟩ := hc
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.sub_im, Complex.one_im,
    Complex.mul_im, add_zero, zero_add] at hre him
  have ht0 : t ≠ 0 := by rintro rfl; linarith
  have huim : u.im = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact absurd h' ht0
    · exact h'
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hur : u.re ≤ 0 := by nlinarith [ht.2]
  set s := 1 / (1 - u.re) with hs
  have h1 : 0 < 1 - u.re := by linarith
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hs, div_le_one h1]; linarith
  apply h s ⟨hs0, hs1⟩
  have hB : B = u * A := by rw [hu]; field_simp
  have hu' : u = (u.re : ℂ) := by
    apply Complex.ext <;> simp [huim]
  rw [hB, hu']
  have : (1 - (s:ℂ)) + s * (u.re : ℂ) = 0 := by
    have : 1 - s + s * u.re = 0 := by rw [hs]; field_simp; ring
    exact_mod_cast this
  linear_combination A * this

theorem segment_ne_zero {a b p : Pt} (hp : p ∉ segment ℝ a b) :
    ∀ s ∈ Icc (0:ℝ) 1, (1 - (s:ℂ)) * (toCpx p - toCpx a) + s * (toCpx p - toCpx b) ≠ 0 := by
  intro s hs h0
  apply hp
  rw [segment_eq_image_lineMap]
  refine ⟨s, hs, toCpx_injective ?_⟩
  rw [toCpx_lineMap]
  linear_combination -h0

theorem toCpx_sub_ne_zero {a p : Pt} (h : p ≠ a) : toCpx p - toCpx a ≠ 0 := fun e =>
  h (toCpx_injective (sub_eq_zero.1 e))

/-- `(p − b) / (p − a)` is in the slit plane when `p ∉ [a, b]`. -/
theorem div_mem_slitPlane {a b p : Pt} (hp : p ∉ segment ℝ a b) :
    (toCpx p - toCpx b) / (toCpx p - toCpx a) ∈ Complex.slitPlane := by
  have hA : toCpx p - toCpx a ≠ 0 :=
    toCpx_sub_ne_zero fun e => hp (e ▸ left_mem_segment _ _ _)
  have := slit_of_segment_ne_zero hA (segment_ne_zero hp) (t := 1) ⟨zero_le_one, le_rfl⟩
  simpa using this

/-- **The change of a logarithm along an edge.** -/
theorem log_diff_edge {a b p : Pt} (hp : p ∉ segment ℝ a b) {L : Pt → ℂ}
    (hL : ContinuousOn L (segment ℝ a b))
    (hexp : ∀ z ∈ segment ℝ a b, Complex.exp (L z) = toCpx z - toCpx p) :
    L b - L a = Complex.log ((toCpx p - toCpx b) / (toCpx p - toCpx a)) := by
  set A := toCpx p - toCpx a with hAdef
  set B := toCpx p - toCpx b with hBdef
  have hA : A ≠ 0 := toCpx_sub_ne_zero fun e => hp (e ▸ left_mem_segment _ _ _)
  have hseg := segment_ne_zero hp
  set γ : ℝ → Pt := fun t => AffineMap.lineMap a b t with hγ
  have hγc : Continuous γ := AffineMap.lineMap_continuous
  have hγm : MapsTo γ (Icc 0 1) (segment ℝ a b) := by
    intro t ht; rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩
  have hγz : ∀ t, toCpx (γ t) - toCpx p = -((1 - (t:ℂ)) * A + t * B) := by
    intro t; simp only [hγ, toCpx_lineMap, hAdef, hBdef]; ring
  set f : ℝ → ℂ := fun t => L (γ t)
  set g : ℝ → ℂ := fun t => Complex.log (((1 - (t:ℂ)) * A + t * B) / A) + L a
  have hf : ContinuousOn f (Icc 0 1) := hL.comp hγc.continuousOn hγm
  have hg : ContinuousOn g (Icc 0 1) := by
    refine ContinuousOn.add (ContinuousOn.clog ?_ fun t ht => slit_of_segment_ne_zero hA hseg ht)
      continuousOn_const
    fun_prop
  have hfg : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (f t) = Complex.exp (g t) := by
    intro t ht
    simp only [f, g]
    rw [hexp _ (hγm ht), hγz, Complex.exp_add, Complex.exp_log
      (div_ne_zero (hseg t ht) hA), hexp a (left_mem_segment _ _ _)]
    field_simp
    simp only [hAdef]; ring
  have key := sub_const_of_exp_eq isPreconnected_Icc hf hg hfg (x := 1) (y := 0)
    ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
  simp only [f, g, hγ, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero] at key
  simp only [Complex.ofReal_one, Complex.ofReal_zero, sub_self, zero_mul, one_mul, zero_add,
    sub_zero] at key
  rw [add_zero, div_self hA, Complex.log_one] at key
  linear_combination key

/-- **The jump of the argument across the negative real axis.** -/
theorem arg_div_jump {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hs : B / A ∈ Complex.slitPlane) :
    ∃ j : ℤ, (B / A).arg = B.arg - A.arg + 2 * π * j ∧ (j = -1 ∨ j = 0 ∨ j = 1) ∧
      (j ≠ 0 ↔ ((0 ≤ A.im ∧ B.im < 0 ∧ 0 < B.im * A.re - B.re * A.im) ∨
        (0 ≤ B.im ∧ A.im < 0 ∧ B.im * A.re - B.re * A.im < 0))) := by
  have hcoe := Complex.arg_div_coe_angle hB hA
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hcoe
  obtain ⟨j, hj⟩ := hcoe
  have hπ := Real.pi_pos
  have hd := (Complex.mem_slitPlane_iff_arg.1 hs).1
  have h1 := Complex.arg_le_pi (B / A)
  have h2 := Complex.neg_pi_lt_arg (B / A)
  have h3 := Complex.arg_le_pi A
  have h4 := Complex.neg_pi_lt_arg A
  have h5 := Complex.arg_le_pi B
  have h6 := Complex.neg_pi_lt_arg B
  have h1' : (B / A).arg < π := lt_of_le_of_ne h1 hd
  have hjr : (-2 : ℝ) < j ∧ (j : ℝ) < 2 := by
    constructor <;> nlinarith
  have hj3 : j = -1 ∨ j = 0 ∨ j = 1 := by
    have : -2 < j ∧ j < 2 := ⟨by exact_mod_cast hjr.1, by exact_mod_cast hjr.2⟩
    omega
  refine ⟨j, by linarith, hj3, ?_⟩
  have hcross : ‖A‖ * ‖B‖ * Real.sin (B.arg - A.arg) = B.im * A.re - B.re * A.im := by
    rw [Real.sin_sub, ← Complex.norm_mul_sin_arg B, ← Complex.norm_mul_cos_arg A,
      ← Complex.norm_mul_cos_arg B, ← Complex.norm_mul_sin_arg A]
    ring
  have hAB : 0 < ‖A‖ * ‖B‖ := mul_pos (norm_pos_iff.2 hA) (norm_pos_iff.2 hB)
  have hsign_pos : 0 < B.im * A.re - B.re * A.im ↔ 0 < Real.sin (B.arg - A.arg) := by
    rw [← hcross]; exact ⟨fun h => pos_of_mul_pos_right h hAB.le, fun h => mul_pos hAB h⟩
  have hsign_neg : B.im * A.re - B.re * A.im < 0 ↔ Real.sin (B.arg - A.arg) < 0 := by
    rw [← hcross]
    exact ⟨fun h => neg_of_mul_neg_right h hAB.le, fun h => mul_neg_of_pos_of_neg hAB h⟩
  have hnpi : B.arg - A.arg ≠ π ∧ B.arg - A.arg ≠ -π := by
    constructor <;> intro he <;> rcases hj3 with h' | h' | h' <;> subst h' <;> push_cast at hj <;>
      linarith
  have hj0 : j = 0 ↔ (-π < B.arg - A.arg ∧ B.arg - A.arg < π) := by
    constructor
    · rintro rfl; push_cast at hj; constructor <;> linarith
    · rintro ⟨hl, hu⟩
      rcases hj3 with h | h | h
      · subst h; push_cast at hj; linarith
      · exact h
      · subst h; push_cast at hj; linarith
  rw [Ne, hj0]
  rcases le_or_gt 0 A.im with hAi | hAi <;> rcases le_or_gt 0 B.im with hBi | hBi
  · have ha := Complex.arg_nonneg_iff.2 hAi
    have hb := Complex.arg_nonneg_iff.2 hBi
    constructor
    · intro h; exfalso; apply h
      exact ⟨lt_of_le_of_ne (by linarith) (Ne.symm hnpi.2), lt_of_le_of_ne (by linarith) hnpi.1⟩
    · rintro (⟨-, h, -⟩ | ⟨-, h, -⟩) <;> linarith
  · have ha := Complex.arg_nonneg_iff.2 hAi
    have hb := Complex.arg_neg_iff.2 hBi
    constructor
    · intro h
      left
      refine ⟨hAi, hBi, hsign_pos.2 ?_⟩
      have hlt : B.arg - A.arg ≤ -π := by
        by_contra hc; push_neg at hc; exact h ⟨hc, by linarith⟩
      have hlt' := lt_of_le_of_ne hlt hnpi.2
      rw [← Real.sin_add_two_pi]
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    · rintro (⟨-, -, h⟩ | ⟨-, h, -⟩)
      · rintro ⟨hl, hu⟩
        have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith : B.arg - A.arg ≤ 0) hl.le
        linarith [hsign_pos.1 h]
      · linarith
  · have ha := Complex.arg_neg_iff.2 hAi
    have hb := Complex.arg_nonneg_iff.2 hBi
    constructor
    · intro h
      right
      refine ⟨hBi, hAi, hsign_neg.2 ?_⟩
      have hlt : π ≤ B.arg - A.arg := by
        by_contra hc; push_neg at hc; exact h ⟨by linarith, hc⟩
      have hlt' := lt_of_le_of_ne hlt (Ne.symm hnpi.1)
      rw [← Real.sin_sub_two_pi]
      exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    · rintro (⟨-, h, -⟩ | ⟨-, -, h⟩)
      · linarith
      · rintro ⟨hl, hu⟩
        have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ B.arg - A.arg) hu.le
        linarith [hsign_neg.1 h]
  · have ha := Complex.arg_neg_iff.2 hAi
    have hb := Complex.arg_neg_iff.2 hBi
    constructor
    · intro h; exfalso; exact h ⟨by linarith, by linarith⟩
    · rintro (⟨h, -, -⟩ | ⟨h, -, -⟩) <;> linarith

/-- `CrossesEast p a b` in terms of `A = p − a`, `B = p − b`: half-open straddle of the real axis
and the sign of the cross product. -/
theorem crossesEast_iff_cross (p a b : Pt) :
    CrossesEast p a b ↔
      ((0 ≤ (toCpx p - toCpx a).im ∧ (toCpx p - toCpx b).im < 0 ∧
          0 < (toCpx p - toCpx b).im * (toCpx p - toCpx a).re -
            (toCpx p - toCpx b).re * (toCpx p - toCpx a).im) ∨
        (0 ≤ (toCpx p - toCpx b).im ∧ (toCpx p - toCpx a).im < 0 ∧
          (toCpx p - toCpx b).im * (toCpx p - toCpx a).re -
            (toCpx p - toCpx b).re * (toCpx p - toCpx a).im < 0)) := by
  simp only [toCpx, Complex.sub_re, Complex.sub_im]
  unfold CrossesEast
  constructor
  · rintro ⟨h | h, hx⟩
    · have hD : 0 < b.2 - a.2 := by linarith
      rw [← sub_lt_iff_lt_add', lt_div_iff₀ hD] at hx
      left; refine ⟨by linarith, by linarith, by nlinarith⟩
    · have hD : b.2 - a.2 < 0 := by linarith
      rw [← sub_lt_iff_lt_add', lt_div_iff_of_neg hD] at hx
      right; refine ⟨by linarith, by linarith, by nlinarith⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · have hD : 0 < b.2 - a.2 := by linarith
      refine ⟨Or.inl ⟨by linarith, by linarith⟩, ?_⟩
      rw [← sub_lt_iff_lt_add', lt_div_iff₀ hD]; nlinarith
    · have hD : b.2 - a.2 < 0 := by linarith
      refine ⟨Or.inr ⟨by linarith, by linarith⟩, ?_⟩
      rw [← sub_lt_iff_lt_add', lt_div_iff_of_neg hD]; nlinarith

/-- **One edge**: the argument of `(p − b) / (p − a)` is `arg (p − b) − arg (p − a) + 2π j` with
`j ∈ {−1, 0, 1}`, and `j` is odd exactly when the edge crosses the east ray from `p`. -/
theorem edge_jump {a b p : Pt} (hp : p ∉ segment ℝ a b) :
    ∃ j : ℤ, ((toCpx p - toCpx b) / (toCpx p - toCpx a)).arg =
        (toCpx p - toCpx b).arg - (toCpx p - toCpx a).arg + 2 * π * j ∧
      (j : ZMod 2) = ceInd p a b := by
  have hA : toCpx p - toCpx a ≠ 0 :=
    toCpx_sub_ne_zero fun e => hp (e ▸ left_mem_segment _ _ _)
  have hB : toCpx p - toCpx b ≠ 0 :=
    toCpx_sub_ne_zero fun e => hp (e ▸ right_mem_segment _ _ _)
  obtain ⟨j, hj, hj3, hjc⟩ := arg_div_jump hA hB (div_mem_slitPlane hp)
  refine ⟨j, hj, ?_⟩
  rw [← crossesEast_iff_cross] at hjc
  unfold ceInd
  by_cases hc : CrossesEast p a b
  · rw [if_pos hc]
    rcases hj3 with h | h | h
    · subst h; decide
    · exact absurd h (hjc.2 hc)
    · subst h; decide
  · rw [if_neg hc]
    have : j = 0 := by by_contra h; exact hc (hjc.1 h)
    subst this; decide

end HPC.Plane
