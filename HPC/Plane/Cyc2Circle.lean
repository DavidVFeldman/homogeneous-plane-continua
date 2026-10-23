import HPC.Plane.StdChain

/-!
# Batch 128, auxiliary: jumps of a `ZMod 2`-valued function on an interval, and points of a
# Euclidean circle

Two self-contained tools for the even-degree step of `Cyc2` (`even_deg_oddSet`):

* `zmod2_jump_sum`: a function `F : ℝ → ZMod 2`, locally constant at the points of `[a, b]` off
  a finite set `T ⊆ (a, b)`, and jumping by `δ t` at each `t ∈ T` (constant `c` just left of `t`,
  constant `c + δ t` just right of it), satisfies `F b = F a + ∑ t ∈ T, δ t`;
* the circle `circPt w ρ θ = w + ρ (cos θ, sin θ)` (Euclidean, although `Pt` carries the sup
  metric) meets a segment `[w, v]` with `0 < ρ < |v − w|₂` exactly at the angles `θ` with
  `|v − w|₂ (cos θ, sin θ) = v − w` (`circPt_mem_segment_iff`); such an angle exists
  (`Complex.arg`, `exists_angle`) and is unique modulo `2π` (`angle_unique`, via
  `Real.Angle.cos_sin_inj`).
-/

namespace HPC.Plane

open Set Filter Topology Real

/-! ### Jumps of a `ZMod 2`-valued function on an interval -/

/-- A `ZMod 2`-valued function locally constant at every point of `[a, b]` is constant there. -/
theorem zmod2_const_of_loc {F : ℝ → ZMod 2} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ s ∈ Icc a b, ∀ᶠ s' in 𝓝 s, F s' = F s) : F b = F a := by
  have hc : ContinuousOn (fun z => (F z).val) (Icc a b) := fun z hz =>
    (continuousAt_const.congr (by
      filter_upwards [hloc z hz] with w hw
      rw [hw])).continuousWithinAt
  have := (isPreconnected_Icc (a := a) (b := b)).constant_of_mapsTo
    (T := (Set.univ : Set ℕ)) IsDiscrete.univ hc (Set.mapsTo_univ _ _)
    (right_mem_Icc.2 hab) (left_mem_Icc.2 hab)
  exact ZMod.val_injective _ this

/-- **The jump formula** (by induction on `#T`, cutting off the smallest jump). -/
theorem zmod2_jump_sum (F δ : ℝ → ZMod 2) : ∀ (n : ℕ) (a b : ℝ) (T : Finset ℝ), T.card = n →
    a ≤ b → (∀ t ∈ T, t ∈ Ioo a b) →
    (∀ s ∈ Icc a b, s ∉ T → ∀ᶠ s' in 𝓝 s, F s' = F s) →
    (∀ t ∈ T, ∃ c, (∀ᶠ s in 𝓝[<] t, F s = c) ∧ (∀ᶠ s in 𝓝[>] t, F s = c + δ t)) →
    F b = F a + ∑ t ∈ T, δ t := by
  intro n
  induction n with
  | zero =>
    intro a b T hT hab _ hloc _
    rw [Finset.card_eq_zero] at hT
    subst hT
    simp only [Finset.sum_empty, add_zero]
    exact zmod2_const_of_loc hab fun s hs => hloc s hs (Finset.notMem_empty s)
  | succ n ih =>
    intro a b T hT hab hTab hloc hjump
    have hne : T.Nonempty := Finset.card_pos.1 (by omega)
    set t := T.min' hne with ht_def
    have htT : t ∈ T := Finset.min'_mem T hne
    have htmin : ∀ t' ∈ T, t ≤ t' := fun t' h => Finset.min'_le T t' h
    obtain ⟨hat, htb⟩ := hTab t htT
    obtain ⟨c, hl, hr⟩ := hjump t htT
    obtain ⟨l, hl', hlsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hl
    obtain ⟨u, hu', husub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hr
    set T' := T.erase t with hT'
    set m := (insert b T').min' (Finset.insert_nonempty _ _) with hm
    have hmem : m ∈ insert b T' := Finset.min'_mem _ _
    have hmgt : t < m := by
      rcases Finset.mem_insert.1 hmem with h | h
      · rw [h]; exact htb
      · exact lt_of_le_of_ne (htmin _ (Finset.mem_of_mem_erase h))
          (fun h' => (Finset.ne_of_mem_erase h) h'.symm)
    have hmle : ∀ t' ∈ insert b T', m ≤ t' := fun t' h => Finset.min'_le _ t' h
    set s1 := (max l a + t) / 2 with hs1
    have hlt : max l a < t := max_lt (mem_Iio.1 hl') hat
    have hls1 : max l a < s1 := by rw [hs1]; linarith
    have hs1t : s1 < t := by rw [hs1]; linarith
    have hla := le_max_left l a
    have haa := le_max_right l a
    set s2 := (t + min u m) / 2 with hs2
    have htu : t < min u m := lt_min (mem_Ioi.1 hu') hmgt
    have hts2 : t < s2 := by rw [hs2]; linarith
    have hs2u : s2 < min u m := by rw [hs2]; linarith
    have hs2m : s2 < m := lt_of_lt_of_le hs2u (min_le_right _ _)
    have hs2u' : s2 < u := lt_of_lt_of_le hs2u (min_le_left _ _)
    have hs2b : s2 ≤ b := (hs2m.trans_le (hmle b (Finset.mem_insert_self _ _))).le
    have hFs1 : F s1 = c := hlsub ⟨by linarith, hs1t⟩
    have hFs2 : F s2 = c + δ t := husub ⟨hts2, hs2u'⟩
    have hleft : F s1 = F a := zmod2_const_of_loc (by linarith) fun s hs => hloc s
      ⟨hs.1, by linarith [hs.2]⟩ fun h => by linarith [htmin s h, hs.2]
    have hright : F b = F s2 + ∑ t ∈ T', δ t := by
      refine ih s2 b T' (by rw [Finset.card_erase_of_mem htT, hT]; rfl) hs2b ?_ ?_ ?_
      · intro t' ht'
        exact ⟨hs2m.trans_le (hmle t' (Finset.mem_insert_of_mem ht')),
          (hTab t' (Finset.mem_of_mem_erase ht')).2⟩
      · intro s hs hsT
        refine hloc s ⟨by linarith [hs.1], hs.2⟩ fun h => hsT (Finset.mem_erase.2 ⟨?_, h⟩)
        rintro rfl; linarith [hs.1]
      · intro t' ht'
        exact hjump t' (Finset.mem_of_mem_erase ht')
    rw [hright, hFs2, ← Finset.add_sum_erase T δ htT, ← hleft, hFs1]
    ring

/-! ### Points of a Euclidean circle -/

/-- The point at angle `θ` on the Euclidean circle of radius `ρ` about `w`. -/
noncomputable def circPt (w : Pt) (ρ θ : ℝ) : Pt := (w.1 + ρ * Real.cos θ, w.2 + ρ * Real.sin θ)

/-- The Euclidean norm of a vector of `ℝ × ℝ` (which itself carries the sup norm). -/
noncomputable def eNorm (u : Pt) : ℝ := Real.sqrt (u.1 ^ 2 + u.2 ^ 2)

theorem eNorm_sq (u : Pt) : eNorm u ^ 2 = u.1 ^ 2 + u.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem eNorm_pos {u : Pt} (hu : u ≠ 0) : 0 < eNorm u := by
  apply Real.sqrt_pos.2
  by_contra h
  push_neg at h
  apply hu
  have h1 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  have h2 : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  exact Prod.ext h1 h2

theorem continuous_circPt (w : Pt) (ρ : ℝ) : Continuous (circPt w ρ) := by
  unfold circPt; fun_prop

theorem circPt_add_two_pi (w : Pt) (ρ θ : ℝ) : circPt w ρ (θ + 2 * π) = circPt w ρ θ := by
  simp [circPt, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem circPt_add_int_mul_two_pi (w : Pt) (ρ θ : ℝ) (k : ℤ) :
    circPt w ρ (θ + k * (2 * π)) = circPt w ρ θ := by
  simp [circPt, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- The circle point lies within sup-distance `ρ` of the centre. -/
theorem dist_circPt_le (w : Pt) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) : dist (circPt w ρ θ) w ≤ ρ := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [circPt, add_sub_cancel_left, abs_mul, abs_of_nonneg hρ]
  exact max_le (mul_le_of_le_one_right hρ (Real.abs_cos_le_one θ))
    (mul_le_of_le_one_right hρ (Real.abs_sin_le_one θ))

/-- **The circle meets a segment from its centre** exactly in the direction of the segment. -/
theorem circPt_mem_segment_iff {w v : Pt} (hwv : w ≠ v) {ρ : ℝ} (hρ : 0 < ρ)
    (hρN : ρ < eNorm (v - w)) (θ : ℝ) :
    circPt w ρ θ ∈ segment ℝ w v ↔
      eNorm (v - w) * Real.cos θ = (v - w).1 ∧ eNorm (v - w) * Real.sin θ = (v - w).2 := by
  set u := v - w with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 hwv.symm
  have hN := eNorm_pos hu0
  have hN2 := eNorm_sq u
  have hcs := Real.cos_sq_add_sin_sq θ
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, ht⟩
    have e1 : ρ * Real.cos θ = t * u.1 := by
      have := congrArg Prod.fst ht; simp [circPt] at this; rw [hu]; simp; linarith
    have e2 : ρ * Real.sin θ = t * u.2 := by
      have := congrArg Prod.snd ht; simp [circPt] at this; rw [hu]; simp; linarith
    have hsq : ρ ^ 2 = t ^ 2 * eNorm u ^ 2 := by
      calc ρ ^ 2 = ρ ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by rw [hcs, mul_one]
        _ = (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 := by ring
        _ = t ^ 2 * eNorm u ^ 2 := by rw [e1, e2, hN2]; ring
    have ht' : t * eNorm u = ρ := by
      have : (t * eNorm u) ^ 2 = ρ ^ 2 := by rw [mul_pow]; linarith
      have hpos : 0 ≤ t * eNorm u := mul_nonneg ht0 hN.le
      nlinarith [sq_nonneg (t * eNorm u - ρ), sq_nonneg (t * eNorm u + ρ)]
    have ht0' : t ≠ 0 := by rintro rfl; simp at ht'; linarith
    constructor
    · exact mul_left_cancel₀ ht0' (by rw [← mul_assoc, ht']; exact e1)
    · exact mul_left_cancel₀ ht0' (by rw [← mul_assoc, ht']; exact e2)
  · rintro ⟨h1, h2⟩
    refine ⟨ρ / eNorm u, ⟨by positivity, (div_le_one hN).2 hρN.le⟩, ?_⟩
    ext
    · simp only [circPt, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [← h1]; field_simp
    · simp only [circPt, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [← h2]; field_simp

/-- The direction angle of a nonzero vector (`Complex.arg`). -/
noncomputable def dirAngle (u : Pt) : ℝ := Complex.arg ⟨u.1, u.2⟩

theorem dirAngle_mem_Ioc (u : Pt) : dirAngle u ∈ Ioc (-π) π :=
  ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

theorem exists_angle {u : Pt} (hu : u ≠ 0) :
    eNorm u * Real.cos (dirAngle u) = u.1 ∧ eNorm u * Real.sin (dirAngle u) = u.2 := by
  have hz : (⟨u.1, u.2⟩ : ℂ) ≠ 0 := by
    intro h; apply hu
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    simp at h1 h2; exact Prod.ext h1 h2
  have hn : ‖(⟨u.1, u.2⟩ : ℂ)‖ = eNorm u := by
    rw [Complex.norm_def, Complex.normSq_mk, eNorm]; ring_nf
  have hn0 : eNorm u ≠ 0 := (eNorm_pos hu).ne'
  unfold dirAngle
  rw [Complex.cos_arg hz, Complex.sin_arg, hn]
  constructor <;> field_simp

theorem angle_unique {N a b θ θ' : ℝ} (hN : 0 < N) (h1 : N * Real.cos θ = a)
    (h2 : N * Real.sin θ = b) (h1' : N * Real.cos θ' = a) (h2' : N * Real.sin θ' = b) :
    ∃ k : ℤ, θ - θ' = 2 * π * k := by
  have hc : Real.cos θ = Real.cos θ' := mul_left_cancel₀ hN.ne' (h1.trans h1'.symm)
  have hs : Real.sin θ = Real.sin θ' := mul_left_cancel₀ hN.ne' (h2.trans h2'.symm)
  exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs)

theorem eq_of_two_pi_mul {θ θ' a b : ℝ} (h : θ ∈ Ioo a b) (h' : θ' ∈ Ioo a b)
    (hab : b ≤ a + 2 * π) {k : ℤ} (hk : θ - θ' = 2 * π * k) : θ = θ' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by
    by_contra hc; push_neg at hc; nlinarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hc; push_neg at hc; nlinarith
  have : k = 0 := by
    have a1 : k < 1 := by exact_mod_cast hk1
    have a2 : -1 < k := by exact_mod_cast hk2
    omega
  subst this; simp at hk; linarith

end HPC.Plane
