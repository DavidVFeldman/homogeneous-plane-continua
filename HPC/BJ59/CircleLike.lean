import HPC.Plane.Ingram68

/-!
# Batch 199, library: the circle is circle-like; circle-likeness along homeomorphisms
(commission 199, §4)

* `isCircleLike_circle`: for `n ≥ 4`, the open arcs `p((k − 1/4, k + 5/4))`, where
  `p(t) = exp(2πit/n)`, form a circular chain of mesh `≤ 3π/n` covering the circle.
* `isCircleLike_univ_of_homeomorph`: pull the links back by a homeomorphism (uniform continuity of
  the inverse on the compact target).
-/

namespace HPC.BJ59

open Set Topology Metric Real HPC.Plane

/-- `exp` is `1`-Lipschitz from `ℝ` to the circle. -/
theorem dist_circle_exp_le (a b : ℝ) : dist (Circle.exp a) (Circle.exp b) ≤ |a - b| := by
  rw [Subtype.dist_eq, dist_eq_norm, Circle.coe_exp, Circle.coe_exp]
  have : Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I) =
      Complex.exp (↑b * Complex.I) * (Complex.exp (Complex.I * ↑(a - b)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact (norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq (Real.norm_eq_abs _))

theorem circle_exp_surjective : Function.Surjective Circle.exp := fun z => ⟨_, Circle.exp_arg z⟩

theorem isConnected_univ_circle : IsConnected (univ : Set Circle) := by
  rw [← circle_exp_surjective.range_eq]; exact isConnected_range Circle.exp.continuous

/-- The parametrization `t ↦ exp(2πit/n)`, of period `n`. -/
noncomputable def circP (n : ℕ) (t : ℝ) : Circle := Circle.exp (2 * π * t / n)

theorem circP_eq_iff {n : ℕ} (hn : 0 < n) (s t : ℝ) :
    circP n s = circP n t ↔ ∃ m : ℤ, s = t + m * n := by
  unfold circP
  rw [Circle.exp_eq_exp]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    field_simp at hm
    nlinarith [hm]
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    field_simp

/-- The `k`-th arc. -/
noncomputable def circArc (n : ℕ) (k : Fin n) : Set Circle :=
  circP n '' Ioo ((k : ℝ) - 1 / 4) (k + 5 / 4)

theorem isOpen_circArc {n : ℕ} (hn : 0 < n) (k : Fin n) : IsOpen (circArc n k) := by
  have hc : (2 * π / n : ℝ) ≠ 0 := by positivity
  have : circP n = Circle.exp ∘ (fun t => (2 * π / n) * t) := by
    funext t; simp only [circP, Function.comp]; congr 1; ring
  unfold circArc
  rw [this]
  exact (Circle.isCoveringMap_exp.isOpenMap.comp (Homeomorph.mulLeft₀ _ hc).isOpenMap) _ isOpen_Ioo

theorem circArc_adjacent {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    (circArc n i ∩ circArc n j).Nonempty ↔ cycDist i j ≤ 1 := by
  have hn0 : 0 < n := by omega
  have hi := i.2; have hj := j.2
  constructor
  · rintro ⟨z, ⟨s, hs, rfl⟩, ⟨t, ht, hst⟩⟩
    obtain ⟨m, hm⟩ := (circP_eq_iff hn0 s t).1 hst.symm
    simp only [mem_Ioo] at hs ht
    have h1 : ((m * n - ((i : ℤ) - j) : ℤ) : ℝ) < 3 / 2 := by
      push_cast; linarith
    have h2 : (-(3 / 2) : ℝ) < ((m * n - ((i : ℤ) - j) : ℤ) : ℝ) := by
      push_cast; linarith
    have a1 : m * n - ((i : ℤ) - j) ≤ 1 := by
      by_contra h; push_neg at h
      have h' : (2 : ℤ) ≤ m * n - ((i : ℤ) - j) := h
      have : ((2 : ℤ) : ℝ) ≤ ((m * n - ((i : ℤ) - j) : ℤ) : ℝ) := by exact_mod_cast h'
      push_cast at this h1; linarith
    have a2 : -1 ≤ m * n - ((i : ℤ) - j) := by
      by_contra h; push_neg at h
      have h' : m * n - ((i : ℤ) - j) ≤ -2 := by omega
      have : ((m * n - ((i : ℤ) - j) : ℤ) : ℝ) ≤ ((-2 : ℤ) : ℝ) := by exact_mod_cast h'
      push_cast at this h2; linarith
    unfold cycDist
    have hn4 : (4 : ℤ) ≤ n := by exact_mod_cast hn
    rcases lt_trichotomy m 0 with hm | hm | hm
    · have : m * n ≤ -n := by nlinarith
      have : -n ≤ m * n := by nlinarith
      omega
    · subst hm; omega
    · have : m * n ≥ n := by nlinarith
      have : m * n ≤ n := by nlinarith
      omega
  · intro h
    unfold cycDist at h
    obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, -1 ≤ m * n - ((i : ℤ) - j) ∧ m * n - ((i : ℤ) - j) ≤ 1 := by
      by_cases h0 : ((i : ℤ) - j).natAbs ≤ 1
      · exact ⟨0, by omega, by omega⟩
      · by_cases hij : (j : ℤ) < i
        · exact ⟨1, by omega, by omega⟩
        · exact ⟨-1, by omega, by omega⟩
    set e : ℤ := m * n - ((i : ℤ) - j) with he
    have he1 : (-1 : ℝ) ≤ e := by exact_mod_cast hm1
    have he2 : (e : ℝ) ≤ 1 := by exact_mod_cast hm2
    have hee : (e : ℝ) = m * n - ((i : ℝ) - j) := by simp [e]
    refine ⟨circP n (j + 1 / 2 - e / 2), ⟨j + 1 / 2 - e / 2 + m * n, ⟨?_, ?_⟩, ?_⟩,
      ⟨j + 1 / 2 - e / 2, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith
    · linarith
    · exact (circP_eq_iff hn0 _ _).2 ⟨m, rfl⟩
    · linarith
    · linarith

theorem circArc_cover {n : ℕ} (hn : 0 < n) (z : Circle) : ∃ k : Fin n, z ∈ circArc n k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨θ, rfl⟩ := circle_exp_surjective z
  set t0 : ℝ := θ * n / (2 * π)
  set t := toIcoMod hn' 0 t0
  have ht := toIcoMod_mem_Ico hn' 0 t0
  simp only [zero_add] at ht
  have hk : ⌊t⌋₊ < n := by
    have := (Nat.floor_lt ht.1).2 ht.2
    exact_mod_cast this
  refine ⟨⟨⌊t⌋₊, hk⟩, t, ⟨?_, ?_⟩, ?_⟩
  · have := Nat.floor_le ht.1; simp only; linarith
  · have := Nat.lt_floor_add_one t; simp only; linarith
  · have : t = t0 - toIcoDiv hn' 0 t0 • (n : ℝ) := rfl
    unfold circP
    rw [Circle.exp_eq_exp]
    refine ⟨-toIcoDiv hn' 0 t0, ?_⟩
    rw [this, zsmul_eq_mul]
    simp only [t0]
    field_simp
    push_cast
    ring

theorem diam_circArc_le {n : ℕ} (hn : 0 < n) (k : Fin n) :
    diam (circArc n k) ≤ 3 * π / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  refine diam_le_of_forall_dist_le (by positivity) ?_
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  simp only [mem_Ioo] at hs ht
  refine (dist_circle_exp_le _ _).trans ?_
  rw [show 2 * π * s / n - 2 * π * t / n = (2 * π / n) * (s - t) by ring, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π / n)]
  have : |s - t| ≤ 3 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  calc 2 * π / n * |s - t| ≤ 2 * π / n * (3 / 2) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 3 * π / n := by ring

/-- The circular chain of the `n` arcs (`n ≥ 4`). -/
noncomputable def circArcChain (n : ℕ) (hn : 4 ≤ n) : CircChain Circle n where
  link := circArc n
  isOpen := isOpen_circArc (by omega)
  adjacent := circArc_adjacent hn

/-- **The circle is circle-like.** -/
theorem isCircleLike_circle : IsCircleLike (univ : Set Circle) := by
  refine ⟨⟨isCompact_univ, isConnected_univ_circle⟩, fun ε hε => ?_⟩
  have hpi := Real.pi_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * π / ε)
  set n := N + 4
  have hn : 4 ≤ n := by omega
  have hn' : (0 : ℝ) < n := by positivity
  refine ⟨n, circArcChain n hn, fun k => ⟨isBounded_of_compactSpace, ?_⟩,
    fun z _ => mem_iUnion.2 (circArc_cover (by omega) z)⟩
  refine lt_of_le_of_lt (diam_circArc_le (by omega) k) ?_
  rw [div_lt_iff₀ hn']
  have : (N : ℝ) < n := by simp [n]
  rw [div_lt_iff₀ hε] at hN
  nlinarith

/-- **Circle-likeness passes along homeomorphisms** (pull back the links; uniform continuity). -/
theorem isCircleLike_univ_of_homeomorph {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] (e : X ≃ₜ Y) (h : IsCircleLike (univ : Set Y)) :
    IsCircleLike (univ : Set X) := by
  haveI : CompactSpace Y := isCompact_univ_iff.1 h.1.1
  have hconn : IsConnected (univ : Set X) := by
    have := h.1.2.image e.symm e.symm.continuous.continuousOn
    rwa [image_univ, e.symm.surjective.range_eq] at this
  refine ⟨⟨isCompact_univ, hconn⟩, fun ε hε => ?_⟩
  have huc : UniformContinuous e.symm := CompactSpace.uniformContinuous_of_continuous
    e.symm.continuous
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (by linarith)
  obtain ⟨n, D, hD, hcov⟩ := h.2 δ hδ
  refine ⟨n, ⟨fun i => e ⁻¹' D.link i, fun i => (D.isOpen i).preimage e.continuous,
    fun i j => ?_⟩, fun i => ⟨isBounded_of_compactSpace, ?_⟩, fun x _ => ?_⟩
  · rw [← D.adjacent i j, ← preimage_inter]
    exact e.surjective.nonempty_preimage
  · refine lt_of_le_of_lt (diam_le_of_forall_dist_le (by linarith) fun x hx y hy => ?_)
      (by linarith : ε / 2 < ε)
    have := hδε (lt_of_le_of_lt (dist_le_diam_of_mem (hD i).1 hx hy) (hD i).2)
    simp only [Homeomorph.symm_apply_apply] at this
    exact this.le
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov (mem_univ (e x)))
    exact mem_iUnion.2 ⟨i, hi⟩

end HPC.BJ59
