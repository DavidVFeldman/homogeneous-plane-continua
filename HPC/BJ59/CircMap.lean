import HPC.BJ59.CircFibre
import HPC.BJ59.Defs

/-!
# Batch 202, §3 (third part): the base map and the recognition theorem

(3.3)–(3.7) and (3.11): every point of `M` lies in a fibre, fibres over `y` and `y'` meet only if
`y − y'` is an integer, the map `p ↦ exp(2πi y)` is continuous, open and onto, `M` is
circle-like, and so `M` is a circle of pseudo-arcs (`CircDescr.isCircleOfPA`).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane Real

/-- `t ↦ exp(2πit)` is an open map. -/
theorem isOpenMap_circP_one : IsOpenMap (circP 1) := by
  have h1 : IsOpenMap (fun t : ℝ => 2 * π * t / ((1 : ℕ) : ℝ)) := by
    have : (fun t : ℝ => 2 * π * t / ((1 : ℕ) : ℝ)) = fun t => (2 * π) * t := by
      funext t; simp
    rw [this]
    exact (Homeomorph.mulLeft₀ (2 * π) (by positivity)).isOpenMap
  exact isLocalHomeomorph_circleExp.isOpenMap.comp h1

theorem dist_circP_one_le (a b : ℝ) (n : ℤ) :
    dist (circP 1 a) (circP 1 b) ≤ 2 * π * |a - b - n| := by
  have e : circP 1 a = circP 1 (a - n) := (circP_eq_iff one_pos _ _).mpr ⟨n, by simp⟩
  rw [e]
  unfold circP
  refine (dist_circle_exp_le _ _).trans (le_of_eq ?_)
  rw [show 2 * π * (a - n) / ((1 : ℕ) : ℝ) - 2 * π * b / ((1 : ℕ) : ℝ) = 2 * π * (a - b - n) by
    push_cast; ring, abs_mul, abs_of_pos (by positivity)]

namespace CircDescr

variable {X : Type*} [MetricSpace X] (Δ : CircDescr X)

theorem lam_lt_one (k : ℕ) : Δ.lam k < 1 := by
  have h := Δ.lam_add_four_le k
  have hN := Δ.N_pos' k
  by_contra hc; push_neg at hc; nlinarith

/-! ### (3.3) The base map -/

/-- Points in a common link have fibre parameters close modulo `1`. -/
theorem near_of_link {k : ℕ} {t : ℤ} {p q : X} {y y' : ℝ} (hp : p ∈ Δ.fib y) (hq : q ∈ Δ.fib y')
    (hpt : p ∈ Δ.L k t) (hqt : q ∈ Δ.L k t) :
    ∃ n : ℤ, |y - y' - n| ≤ Δ.lam k + 2 / Δ.N k := by
  obtain ⟨s, hs, hps⟩ := (Δ.mem_fib_iff.mp hp) k
  obtain ⟨s', hs', hqs'⟩ := (Δ.mem_fib_iff.mp hq) k
  obtain ⟨n1, h1⟩ := (Δ.meet_iff k s t).mp ⟨p, hps, hpt⟩
  obtain ⟨n2, h2⟩ := (Δ.meet_iff k s' t).mp ⟨q, hqs', hqt⟩
  refine ⟨n1 - n2, ?_⟩
  have hN := Δ.N_pos' k
  have e : Δ.c k s - Δ.c k s' - ((n1 - n2 : ℤ) : ℝ) =
      (((s - t - n1 * Δ.N k : ℤ) : ℝ) - ((s' - t - n2 * Δ.N k : ℤ) : ℝ)) / Δ.N k := by
    unfold c; push_cast; field_simp; ring
  have h1' : |((s - t - n1 * Δ.N k : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h1
  have h2' : |((s' - t - n2 * Δ.N k : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h2
  have h3 : |Δ.c k s - Δ.c k s' - ((n1 - n2 : ℤ) : ℝ)| ≤ 2 / Δ.N k := by
    rw [e, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by linarith)) hN.le
  have := abs_sub_le (y - y' - ((n1 - n2 : ℤ) : ℝ)) 0 0
  calc |y - y' - ((n1 - n2 : ℤ) : ℝ)|
      = |(y - Δ.c k s) - (y' - Δ.c k s') + (Δ.c k s - Δ.c k s' - ((n1 - n2 : ℤ) : ℝ))| := by
        ring_nf
    _ ≤ |y - Δ.c k s| + |y' - Δ.c k s'| + |Δ.c k s - Δ.c k s' - ((n1 - n2 : ℤ) : ℝ)| := by
        have := abs_add_le ((y - Δ.c k s) - (y' - Δ.c k s'))
          (Δ.c k s - Δ.c k s' - ((n1 - n2 : ℤ) : ℝ))
        have := abs_sub (y - Δ.c k s) (y' - Δ.c k s')
        linarith
    _ ≤ Δ.lam k + 2 / Δ.N k := by linarith

theorem small_tendsto : Tendsto (fun k => Δ.lam k + 2 / (Δ.N k : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun k => (7 / 5 : ℝ) * Δ.lam k) atTop (𝓝 0) := by
    simpa using Δ.lam_tendsto.const_mul (7 / 5 : ℝ)
  refine squeeze_zero (fun k => ?_) (fun k => ?_) h
  · have := Δ.N_pos' k; have := Δ.lam_pos k; positivity
  · have := Δ.inv_N_le k
    have e : 2 / (Δ.N k : ℝ) = 2 * (1 / Δ.N k) := by ring
    rw [e]; linarith

/-- Two integers within `1/4` of the same real number agree. -/
theorem int_eq_of_near {a : ℝ} {n n' : ℤ} (h : |a - n| < 1 / 4) (h' : |a - n'| < 1 / 4) :
    n = n' := by
  have : |((n - n' : ℤ) : ℝ)| < 1 := by
    push_cast
    have := abs_sub_le ((n : ℝ)) a (n' : ℝ)
    rw [abs_sub_comm ((n : ℝ)) a] at this
    linarith
  rw [← Int.cast_abs] at this
  have h2 : |n - n'| < 1 := by exact_mod_cast this
  rw [abs_lt] at h2; omega

/-- (3.3) Fibres over `y` and `y'` meet only if `y − y'` is an integer. -/
theorem eq_add_int_of_mem {p : X} {y y' : ℝ} (hp : p ∈ Δ.fib y) (hp' : p ∈ Δ.fib y') :
    ∃ n : ℤ, y = y' + n := by
  have hpM := Δ.fib_subset_M y hp
  have hk : ∀ k, ∃ n : ℤ, |y - y' - n| ≤ Δ.lam k + 2 / Δ.N k := by
    intro k
    obtain ⟨t, ht⟩ := mem_iUnion.mp (Δ.M_subset_U k hpM)
    exact Δ.near_of_link hp hp' ht ht
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (Δ.small_tendsto.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num))
  obtain ⟨n₀, hn₀⟩ := hk K
  refine ⟨n₀, ?_⟩
  have hall : ∀ k, K ≤ k → |y - y' - n₀| ≤ Δ.lam k + 2 / Δ.N k := by
    intro k hk'
    obtain ⟨n, hn⟩ := hk k
    have := int_eq_of_near (lt_of_le_of_lt hn (hK k hk')) (lt_of_le_of_lt hn₀ (hK K le_rfl))
    rw [← this]; exact hn
  have h0 : |y - y' - n₀| ≤ 0 :=
    ge_of_tendsto Δ.small_tendsto (eventually_atTop.mpr ⟨K, hall⟩)
  have := abs_nonneg (y - y' - n₀)
  have h00 : y - y' - n₀ = 0 := abs_eq_zero.mp (le_antisymm h0 this)
  linarith

theorem fib_add_int (y : ℝ) (n : ℤ) : Δ.fib (y + n) = Δ.fib y := by
  ext q
  simp only [Δ.mem_fib_iff]
  have key : ∀ k (t : ℤ) (m : ℤ), Δ.c k (t + m * Δ.N k) = Δ.c k t + m := fun k t m =>
    Δ.c_add_mul k t m
  constructor
  · intro h k
    obtain ⟨t, ht, hq⟩ := h k
    refine ⟨t + (-n) * Δ.N k, ?_, by rwa [Δ.L_add_mul]⟩
    rw [key]; push_cast
    rwa [show y - (Δ.c k t + -(n : ℝ)) = y + n - Δ.c k t by ring]
  · intro h k
    obtain ⟨t, ht, hq⟩ := h k
    refine ⟨t + n * Δ.N k, ?_, by rwa [Δ.L_add_mul]⟩
    rw [key]
    rwa [show y + n - (Δ.c k t + (n : ℝ)) = y - Δ.c k t by ring]

/-- The sets of parameters whose arcs at level `k` contain `p`, in `[0, 1]`. -/
def parSet (p : X) (k : ℕ) : Set ℝ :=
  {y | y ∈ Icc (0 : ℝ) 1 ∧ ∃ t, |y - Δ.c k t| ≤ Δ.lam k / 2 ∧ p ∈ Δ.L k t}

theorem isClosed_parSet (p : X) (k : ℕ) : IsClosed (Δ.parSet p k) := by
  classical
  have hN := Δ.N_pos' k
  have hl := Δ.lam_lt_one k
  have hl0 := Δ.lam_pos k
  set lo : ℤ := ⌊(Δ.N k : ℝ) * (-2 - Δ.o k)⌋
  set hi : ℤ := ⌈(Δ.N k : ℝ) * (2 - Δ.o k)⌉
  set S := (Finset.Icc lo hi).filter (fun t => p ∈ Δ.L k t)
  have e : Δ.parSet p k = Icc 0 1 ∩ ⋃ t ∈ S, closedBall (Δ.c k t) (Δ.lam k / 2) := by
    ext y
    simp only [parSet, mem_setOf_eq, mem_inter_iff, mem_iUnion, mem_closedBall, Real.dist_eq,
      exists_prop, S, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hy, t, ht, hp⟩
      refine ⟨hy, t, ⟨⟨?_, ?_⟩, hp⟩, ht⟩
      · have : (lo : ℝ) ≤ t := by
          have h1 := Int.floor_le ((Δ.N k : ℝ) * (-2 - Δ.o k))
          have h2 : (Δ.N k : ℝ) * (-2 - Δ.o k) ≤ t := by
            have e2 : (t : ℝ) = Δ.N k * (Δ.c k t - Δ.o k) := by unfold c; field_simp; ring
            rw [e2]; rw [abs_le] at ht
            apply mul_le_mul_of_nonneg_left _ hN.le
            linarith [hy.1, hy.2]
          linarith
        exact_mod_cast this
      · have : (t : ℝ) ≤ hi := by
          have h1 := Int.le_ceil ((Δ.N k : ℝ) * (2 - Δ.o k))
          have h2 : (t : ℝ) ≤ (Δ.N k : ℝ) * (2 - Δ.o k) := by
            have e2 : (t : ℝ) = Δ.N k * (Δ.c k t - Δ.o k) := by unfold c; field_simp; ring
            rw [e2]; rw [abs_le] at ht
            apply mul_le_mul_of_nonneg_left _ hN.le
            linarith [hy.1, hy.2]
          linarith
        exact_mod_cast this
    · rintro ⟨hy, t, ⟨-, hp⟩, ht⟩
      exact ⟨hy, t, ht, hp⟩
  rw [e]
  exact isClosed_Icc.inter (isClosed_biUnion_finset fun t _ => isClosed_closedBall)

/-- (3.3) Every point of `M` lies in a fibre. -/
theorem exists_fib {p : X} (hp : p ∈ Δ.M) : ∃ y, p ∈ Δ.fib y := by
  have hanti : ∀ k, Δ.parSet p (k + 1) ⊆ Δ.parSet p k := by
    rintro k y ⟨hy, t, ht, hpt⟩
    obtain ⟨h1, h2⟩ := Δ.down hpt ht
    exact ⟨hy, _, h2, h1⟩
  have hne : ∀ k, (Δ.parSet p k).Nonempty := by
    intro k
    obtain ⟨t, ht⟩ := mem_iUnion.mp (Δ.M_subset_U k hp)
    set n := ⌊Δ.c k t⌋
    refine ⟨Δ.c k (t + (-n) * Δ.N k), ⟨?_, ?_⟩, t + (-n) * Δ.N k,
      by rw [sub_self, abs_zero]; exact (half_pos (Δ.lam_pos k)).le, by rwa [Δ.L_add_mul]⟩
    · rw [Δ.c_add_mul]; push_cast; linarith [Int.floor_le (Δ.c k t)]
    · rw [Δ.c_add_mul]; push_cast; linarith [Int.lt_floor_add_one (Δ.c k t)]
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (Δ.parSet p) hanti hne (isCompact_Icc.of_isClosed_subset (Δ.isClosed_parSet p 0)
      (fun y hy => hy.1)) (Δ.isClosed_parSet p)
  refine ⟨y, Δ.mem_fib_iff.mpr fun k => ?_⟩
  obtain ⟨-, t, ht, hpt⟩ := mem_iInter.mp hy k
  exact ⟨t, ht, hpt⟩

/-- The fibre parameter of a point of `M`. -/
noncomputable def yOf (p : Δ.M) : ℝ := Classical.choose (Δ.exists_fib p.2)

theorem yOf_mem (p : Δ.M) : p.1 ∈ Δ.fib (Δ.yOf p) := Classical.choose_spec (Δ.exists_fib p.2)

/-- **The base map** `M → S¹`, `p ↦ exp(2πi y)` for `p` in the fibre over `y`. -/
noncomputable def fmap (p : Δ.M) : Circle := circP 1 (Δ.yOf p)

theorem fmap_eq_iff (p : Δ.M) (y : ℝ) : Δ.fmap p = circP 1 y ↔ p.1 ∈ Δ.fib y := by
  unfold fmap
  rw [circP_eq_iff one_pos]
  constructor
  · rintro ⟨m, hm⟩
    have := Δ.yOf_mem p
    rw [hm, show y + (m : ℝ) * ((1 : ℕ) : ℝ) = y + (m : ℤ) by push_cast; ring,
      Δ.fib_add_int] at this
    exact this
  · intro h
    obtain ⟨n, hn⟩ := Δ.eq_add_int_of_mem (Δ.yOf_mem p) h
    exact ⟨n, by rw [hn]; push_cast; ring⟩

/-- (3.6) The base map is continuous. -/
theorem continuous_fmap : Continuous Δ.fmap := by
  rw [Metric.continuous_iff]
  intro p ε hε
  obtain ⟨k, hk⟩ := (Δ.small_tendsto.eventually_lt_const
    (show (0 : ℝ) < ε / (2 * π) by positivity)).exists
  obtain ⟨t, ht⟩ := mem_iUnion.mp (Δ.M_subset_U k p.2)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (Δ.isOpen_L k t) p.1 ht
  refine ⟨δ, hδ, fun q hq => ?_⟩
  have hqt : q.1 ∈ Δ.L k t := hball (by simpa [Subtype.dist_eq] using hq)
  obtain ⟨n, hn⟩ := Δ.near_of_link (Δ.yOf_mem q) (Δ.yOf_mem p) hqt ht
  calc dist (Δ.fmap q) (Δ.fmap p) ≤ 2 * π * |Δ.yOf q - Δ.yOf p - n| := dist_circP_one_le _ _ n
    _ ≤ 2 * π * (Δ.lam k + 2 / Δ.N k) := by gcongr
    _ < 2 * π * (ε / (2 * π)) := by gcongr
    _ = ε := by field_simp

/-- (3.5) The base map is onto. -/
theorem surjective_fmap : Function.Surjective Δ.fmap := by
  intro z
  obtain ⟨θ, rfl⟩ := circle_exp_surjective z
  obtain ⟨q, hq⟩ := Δ.fib_nonempty (θ / (2 * π))
  refine ⟨⟨q, Δ.fib_subset_M _ hq⟩, ?_⟩
  rw [show Circle.exp θ = circP 1 (θ / (2 * π)) by
    unfold circP; congr 1; push_cast; field_simp]
  exact (Δ.fmap_eq_iff _ _).mpr hq

/-- (3.7) The base map is open. -/
theorem isOpenMap_fmap : IsOpenMap Δ.fmap := by
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨p, hpW, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW p hpW
  obtain ⟨k, hk⟩ := (Δ.ε_tendsto.eventually_lt_const (show (0 : ℝ) < r / 2 by positivity)).exists
  obtain ⟨s, hs, hps⟩ := (Δ.mem_fib_iff.mp (Δ.yOf_mem p)) k
  have hN := Δ.N_pos' k
  have h5 := Δ.five_le_lam k
  have hinv := Δ.inv_N_le k
  set yp := Δ.yOf p
  have hpos : 0 < 1 / (2 * (Δ.N k : ℝ)) := div_pos one_pos (by linarith)
  refine ⟨circP 1 '' Ioo (yp - 1 / (2 * Δ.N k)) (yp + 1 / (2 * Δ.N k)), ?_,
    isOpenMap_circP_one _ isOpen_Ioo, ⟨yp, ⟨by linarith [hpos], by linarith [hpos]⟩, rfl⟩⟩
  rintro _ ⟨y', hy', rfl⟩
  -- a link `s''` next to `s` whose shrunk arc contains `y'`
  have hcs : ∀ u : ℤ, Δ.c k (u + 1) = Δ.c k u + 1 / Δ.N k := Δ.c_succ k
  have hcs' : Δ.c k (s - 1) = Δ.c k s - 1 / Δ.N k := by
    have := hcs (s - 1); rw [show s - 1 + 1 = s by ring] at this; linarith
  obtain ⟨s'', hs''1, hs''2⟩ : ∃ s'' : ℤ, |s'' - s| ≤ 1 ∧
      |y' - (Δ.o k + (s'' : ℝ) / Δ.N k)| ≤ Δ.lam k / 2 - 1 / (2 * Δ.N k) := by
    have hy1 := hy'.1
    have hy2 := hy'.2
    rw [abs_le] at hs
    have e1 : 1 / (2 * (Δ.N k : ℝ)) = (1 / Δ.N k) / 2 := by field_simp
    have hl2 : 2 * (1 / (Δ.N k : ℝ)) ≤ Δ.lam k := by linarith
    rw [e1] at hy1 hy2 ⊢
    by_cases h1 : y' - Δ.c k s > Δ.lam k / 2 - (1 / Δ.N k) / 2
    · refine ⟨s + 1, by simp, ?_⟩
      rw [show Δ.o k + ((s + 1 : ℤ) : ℝ) / Δ.N k = Δ.c k s + 1 / Δ.N k from Δ.c_succ k s, abs_le]
      constructor <;> linarith
    · by_cases h2 : y' - Δ.c k s < -(Δ.lam k / 2 - (1 / Δ.N k) / 2)
      · refine ⟨s - 1, by simp, ?_⟩
        rw [show Δ.o k + ((s - 1 : ℤ) : ℝ) / Δ.N k = Δ.c k s - 1 / Δ.N k from hcs', abs_le]
        constructor <;> linarith
      · refine ⟨s, by simp, ?_⟩
        push_neg at h1 h2
        rw [abs_le]; exact ⟨h2, h1⟩
  obtain ⟨q, hq, hqs''⟩ := Δ.fib_meets k s'' y' hs''2
  refine ⟨⟨q, Δ.fib_subset_M _ hq⟩, hball ?_, (Δ.fmap_eq_iff _ _).mpr hq⟩
  obtain ⟨z, hz1, hz2⟩ := (Δ.meet_iff k s'' s).mpr ⟨0, by simpa using hs''1⟩
  rw [mem_ball, Subtype.dist_eq]
  have d1 := dist_le_diam_of_mem (Δ.L_bdd k s'') hqs'' hz1
  have d2 := dist_le_diam_of_mem (Δ.L_bdd k s) hz2 hps
  have := Δ.diam_le k s''
  have := Δ.diam_le k s
  have := dist_triangle q z p.1
  linarith

/-! ### (3.11) `M` is circle-like -/

/-- The traces of level `k` on `M`, as a circular chain of the space `M`. -/
noncomputable def traceChain (k : ℕ) : CircChain Δ.M (Δ.N k) where
  link i := Subtype.val ⁻¹' Δ.L k i
  isOpen i := (Δ.isOpen_L k _).preimage continuous_subtype_val
  adjacent i j := by
    have hN := Δ.four_le k
    have hi := i.isLt
    have hj := j.isLt
    unfold cycDist
    constructor
    · rintro ⟨z, h1, h2⟩
      obtain ⟨n, hn⟩ := (Δ.meet_iff k i j).mp ⟨z.1, h1, h2⟩
      have h4 : (4 : ℤ) ≤ Δ.N k := by exact_mod_cast hN
      rw [abs_le] at hn
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have : n = -1 := by
          by_contra hc
          have : n ≤ -2 := by omega
          have : n * (Δ.N k : ℤ) ≤ -2 * Δ.N k := by nlinarith
          omega
        subst this
        simp only [min_le_iff]; right; omega
      · subst hn0; simp only [min_le_iff]; left; omega
      · have : n = 1 := by
          by_contra hc
          have : 2 ≤ n := by omega
          have : 2 * (Δ.N k : ℤ) ≤ n * Δ.N k := by nlinarith
          omega
        subst this
        simp only [min_le_iff]; right; omega
    · intro h
      simp only [min_le_iff] at h
      rcases h with h | h
      · rcases (show (i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (j : ℕ) = i + 1 by omega) with e | e | e
        · obtain ⟨z, ⟨hz1, -⟩, hz⟩ := Δ.inter_M_nonempty k i
          refine ⟨⟨z, hz⟩, hz1, ?_⟩
          show z ∈ Δ.L k (j : ℕ)
          rw [← e]; exact hz1
        · obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := Δ.inter_M_nonempty k j
          refine ⟨⟨z, hz⟩, ?_, hz1⟩
          show z ∈ Δ.L k (i : ℕ)
          rw [e]; push_cast; exact hz2
        · obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := Δ.inter_M_nonempty k i
          refine ⟨⟨z, hz⟩, hz1, ?_⟩
          show z ∈ Δ.L k (j : ℕ)
          rw [e]; push_cast; exact hz2
      · -- the two ends `N − 1` and `0`
        have hend : ((i : ℕ) = Δ.N k - 1 ∧ (j : ℕ) = 0) ∨ ((j : ℕ) = Δ.N k - 1 ∧ (i : ℕ) = 0) := by
          omega
        obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := Δ.inter_M_nonempty k ((Δ.N k : ℤ) - 1)
        rw [show (Δ.N k : ℤ) - 1 + 1 = 0 + Δ.N k by ring, Δ.periodic] at hz2
        have e1 : ((Δ.N k - 1 : ℕ) : ℤ) = (Δ.N k : ℤ) - 1 := by omega
        rcases hend with ⟨ei, ej⟩ | ⟨ej, ei⟩
        · refine ⟨⟨z, hz⟩, ?_, ?_⟩
          · show z ∈ Δ.L k (i : ℕ); rw [ei, e1]; exact hz1
          · show z ∈ Δ.L k (j : ℕ); rw [ej]; exact hz2
        · refine ⟨⟨z, hz⟩, ?_, ?_⟩
          · show z ∈ Δ.L k (i : ℕ); rw [ei]; exact hz2
          · show z ∈ Δ.L k (j : ℕ); rw [ej, e1]; exact hz1

theorem isCircleLike_M : IsCircleLike (univ : Set Δ.M) := by
  haveI : CompactSpace Δ.M := isCompact_iff_compactSpace.mp Δ.isCompact_M
  haveI : ConnectedSpace Δ.M := isConnected_iff_connectedSpace.mp Δ.isConnected_M
  refine ⟨⟨isCompact_univ, isConnected_univ⟩, fun ε hε => ?_⟩
  obtain ⟨k, hk⟩ := (Δ.ε_tendsto.eventually_lt_const hε).exists
  refine ⟨Δ.N k, Δ.traceChain k, fun i => ⟨?_, ?_⟩, ?_⟩
  · exact (isometry_subtype_coe.antilipschitz).isBounded_preimage (Δ.L_bdd k i)
  · show diam (Subtype.val ⁻¹' Δ.L k i : Set Δ.M) < ε
    rw [← isometry_subtype_coe.diam_image]
    exact lt_of_le_of_lt ((diam_mono (image_preimage_subset _ _) (Δ.L_bdd k i)).trans
      (Δ.diam_le k i)) hk
  · intro p _
    have := Δ.M_subset_U k p.2
    rw [U_eq_fin] at this
    obtain ⟨i, hi⟩ := mem_iUnion.mp this
    exact mem_iUnion.mpr ⟨i, hi⟩

/-- **The recognition theorem** (commission §3): a circular description describes a circle of
pseudo-arcs. -/
theorem isCircleOfPA : IsCircleOfPA Δ.M := by
  haveI : CompactSpace Δ.M := isCompact_iff_compactSpace.mp Δ.isCompact_M
  refine ⟨Δ.isCircleLike_M, Δ.fmap, Δ.continuous_fmap, Δ.isOpenMap_fmap, Δ.surjective_fmap,
    fun z => ?_⟩
  obtain ⟨θ, rfl⟩ := circle_exp_surjective z
  have e : Circle.exp θ = circP 1 (θ / (2 * π)) := by
    unfold circP; congr 1; push_cast; field_simp
  have hpre : Δ.fmap ⁻¹' {Circle.exp θ} = Subtype.val ⁻¹' Δ.fib (θ / (2 * π)) := by
    ext p; simp only [mem_preimage, mem_singleton_iff]; rw [e, Δ.fmap_eq_iff]
  rw [hpre]
  apply isPseudoArc_subtype_of_image
  rw [Subtype.image_preimage_coe, inter_eq_right.mpr (Δ.fib_subset_M _)]
  exact Δ.isPseudoArc_fib _

end CircDescr

end HPC.BJ59
