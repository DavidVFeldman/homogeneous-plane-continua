import HPC.Span.Defs
import HPC.Plane.Tree67
import HPC.Moore.M25Plane
import HPC.Hagopian.H76Domain

/-!
# Batch 191, §6.1: re-embedding lemmas (E1)–(E3)

* `exists_homeomorph_unique_leftmost` (E1).
* `exists_homeomorph_ball_step`, `exists_homeomorph_push` (E2). The ball step is
  `w ↦ w + β(w)(z − c)` with `β(w) = max(1 − d(w, c)/r, 0)`; it is a homeomorphism by Mathlib's
  `ApproximatesLinearOn.toHomeomorph` (a Lipschitz perturbation of the identity with constant
  `d(z, c)/r < 1`), which replaces the commission's contraction-principle argument.
* `isConnected_rightHalf_diff` (E3), by Janiszewski (`HPC.Moore.janiszewski_compact`).
-/

namespace HPC.Span

open Set Topology Metric HPC.Plane

/-- **§6.1 (E1)**: a plane homeomorphism making a point of a compact set its unique leftmost point,
on the line `x = 0`: `Φ(u, v) = (u − u₀ + (v − v₀)², v)` for a leftmost `(u₀, v₀)`. -/
theorem exists_homeomorph_unique_leftmost {K : Set Pt} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ (Φ : Pt ≃ₜ Pt) (x₀ : Pt), x₀ ∈ K ∧ (Φ x₀).1 = 0 ∧ ∀ z ∈ K, z ≠ x₀ → 0 < (Φ z).1 := by
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
  let e : Pt ≃ Pt :=
    { toFun := fun w => (w.1 - x₀.1 + (w.2 - x₀.2) ^ 2, w.2)
      invFun := fun w => (w.1 + x₀.1 - (w.2 - x₀.2) ^ 2, w.2)
      left_inv := fun w => by ext <;> simp; ring
      right_inv := fun w => by ext <;> simp; ring }
  let Φ : Pt ≃ₜ Pt :=
    { toEquiv := e
      continuous_toFun := by
        show Continuous fun w : Pt => (w.1 - x₀.1 + (w.2 - x₀.2) ^ 2, w.2)
        fun_prop
      continuous_invFun := by
        show Continuous fun w : Pt => (w.1 + x₀.1 - (w.2 - x₀.2) ^ 2, w.2)
        fun_prop }
  refine ⟨Φ, x₀, hx₀, by simp [Φ, e], fun z hz hzx => ?_⟩
  show 0 < z.1 - x₀.1 + (z.2 - x₀.2) ^ 2
  have h1 : x₀.1 ≤ z.1 := hmin hz
  rcases eq_or_ne z.2 x₀.2 with h2 | h2
  · have : z.1 ≠ x₀.1 := fun h => hzx (Prod.ext h h2)
    have : x₀.1 < z.1 := lt_of_le_of_ne h1 (Ne.symm this)
    nlinarith
  · have : 0 < (z.2 - x₀.2) ^ 2 := by
      have : z.2 - x₀.2 ≠ 0 := sub_ne_zero.2 h2
      positivity
    linarith

/-- The ball step of (E2): a homeomorphism moving `c` to a point `z` with `d(z, c) < r` and fixing
every point at distance `≥ r` from `c`. -/
theorem exists_homeomorph_ball_step (c z : Pt) {r : ℝ} (hr : 0 < r) (hz : dist z c < r) :
    ∃ S : Pt ≃ₜ Pt, S c = z ∧ ∀ w, r ≤ dist w c → S w = w := by
  set v : Pt := z - c
  set β : Pt → ℝ := fun w => max (1 - dist w c / r) 0
  set f : Pt → Pt := fun w => w + β w • v
  have hv : ‖v‖ < r := by rw [← dist_eq_norm]; exact hz
  set K : NNReal := Real.toNNReal (‖v‖ / r)
  have hK : (K : ℝ) = ‖v‖ / r := Real.coe_toNNReal _ (div_nonneg (norm_nonneg _) hr.le)
  have hK1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hK, NNReal.coe_one, div_lt_one hr]; exact hv
  have happrox : ApproximatesLinearOn f
      ((ContinuousLinearEquiv.refl ℝ Pt : Pt ≃L[ℝ] Pt) : Pt →L[ℝ] Pt) univ K := by
    rintro x - y -
    have hβ : |β x - β y| ≤ dist x y / r := by
      calc |β x - β y| ≤ |(1 - dist x c / r) - (1 - dist y c / r)| := abs_max_sub_max_le_abs _ _ _
        _ = |dist x c - dist y c| / r := by
          rw [show (1 - dist x c / r) - (1 - dist y c / r) = (dist y c - dist x c) / r by ring,
            abs_div, abs_of_pos hr, abs_sub_comm]
        _ ≤ dist x y / r := div_le_div_of_nonneg_right (abs_dist_sub_le x y c) hr.le
    have : f x - f y - (ContinuousLinearEquiv.refl ℝ Pt : Pt →L[ℝ] Pt) (x - y) = (β x - β y) • v := by
      simp only [f, ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply, sub_smul]
      abel
    rw [this, norm_smul, Real.norm_eq_abs, hK, ← dist_eq_norm]
    calc |β x - β y| * ‖v‖ ≤ dist x y / r * ‖v‖ := mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
      _ = ‖v‖ / r * dist x y := by ring
  have hc : Subsingleton Pt ∨ K < ‖((ContinuousLinearEquiv.refl ℝ Pt).symm : Pt →L[ℝ] Pt)‖₊⁻¹ := by
    right
    simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id, inv_one]
    exact hK1
  refine ⟨happrox.toHomeomorph f hc, ?_, ?_⟩
  · show f c = z
    simp [f, β, v]
  · intro w hw
    show f w = w
    have : β w = 0 := by
      simp only [β]
      apply max_eq_right
      rw [sub_nonpos, le_div_iff₀ hr, one_mul]; exact hw
    simp [f, this]

/-- **§6.1 (E2), the finger move**: in a connected open set, any point can be carried to any other
by a plane homeomorphism fixing every point outside the set. -/
theorem exists_homeomorph_push {U : Set Pt} (hU : IsOpen U) (hUc : IsConnected U) {p q : Pt}
    (hp : p ∈ U) (hq : q ∈ U) : ∃ T : Pt ≃ₜ Pt, T p = q ∧ ∀ z ∉ U, T z = z := by
  set R : Set Pt := {q | ∃ T : Pt ≃ₜ Pt, T p = q ∧ ∀ z ∉ U, T z = z}
  have hRU : R ⊆ U := by
    rintro q ⟨T, hTq, hT⟩
    by_contra hqU
    have : T q = T p := by rw [hT q hqU, hTq]
    exact hqU (T.injective this ▸ hp)
  -- moving inside a ball inside `U`
  have hstep : ∀ q ∈ U, ∃ r > 0, ball q r ⊆ U ∧ ∀ q' ∈ ball q r, (q ∈ R ↔ q' ∈ R) := by
    intro q hqU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU q hqU
    refine ⟨r, hr, hball, fun q' hq' => ?_⟩
    obtain ⟨S, hSq, hS⟩ := exists_homeomorph_ball_step q q' hr hq'
    have hSU : ∀ z ∉ U, S z = z := fun z hz => hS z (by
      by_contra h
      exact hz (hball (mem_ball.2 (not_le.1 h))))
    constructor
    · rintro ⟨T, hTq, hT⟩
      exact ⟨T.trans S, by simp [hTq, hSq], fun z hz => by simp [hT z hz, hSU z hz]⟩
    · rintro ⟨T, hTq, hT⟩
      refine ⟨T.trans S.symm, by simp [hTq, ← hSq], fun z hz => ?_⟩
      have : S.symm z = z := by
        conv_lhs => rw [← hSU z hz]
        exact S.symm_apply_apply z
      simp [hT z hz, this]
  have hRo : IsOpen R := by
    refine Metric.isOpen_iff.2 fun q hq => ?_
    obtain ⟨r, hr, -, hiff⟩ := hstep q (hRU hq)
    exact ⟨r, hr, fun q' hq' => (hiff q' hq').1 hq⟩
  have hVo : IsOpen (U \ R) := by
    refine Metric.isOpen_iff.2 fun q hq => ?_
    obtain ⟨r, hr, hball, hiff⟩ := hstep q hq.1
    exact ⟨r, hr, fun q' hq' => ⟨hball hq', fun h => hq.2 ((hiff q' hq').2 h)⟩⟩
  have hpR : p ∈ R := ⟨Homeomorph.refl Pt, rfl, fun _ _ => rfl⟩
  have := hUc.isPreconnected.subset_left_of_subset_union hRo hVo disjoint_sdiff_right
    (fun z hz => by by_cases h : z ∈ R; exact Or.inl h; exact Or.inr ⟨hz, h⟩) ⟨p, hp, hpR⟩
  exact this hq

/-- A set with connected complement separates no two points. -/
theorem not_separatesPts_of_isConnected_compl {A : Set Pt} (h : IsConnected Aᶜ) (x y : Pt) :
    ¬ SeparatesPts A x y := by
  rintro ⟨hx, hy, hxy⟩
  exact hxy (h.isPreconnected.subset_connectedComponentIn hx subset_rfl hy)

/-- **§6.1 (E3)**: a non-separating continuum that meets the line `x = 0` at most in one point
leaves the open half-plane `x > 0` connected.

*Shape change (generalization):* the skeleton's hypothesis `∀ z ∈ A, 0 ≤ z.1` is not used and has
been removed. -/
theorem isConnected_rightHalf_diff {A : Set Pt} (hA : Fold.Q78.IsContinuum A)
    (hns : ¬ SeparatesPlane A) {x₀ : Pt}
    (hx₀ : ∀ z ∈ A, z.1 = 0 → z = x₀) : IsConnected ({z : Pt | 0 < z.1} \ A) := by
  have hAc : IsConnected Aᶜ := not_not.1 hns
  -- bounds for `A`
  obtain ⟨R, hR⟩ := hA.1.isBounded.subset_closedBall (0 : Pt)
  have hR0 : 0 ≤ R := by
    obtain ⟨z, hz⟩ := hA.2.nonempty
    exact dist_nonneg.trans (mem_closedBall.1 (hR hz))
  have hb : ∀ z ∈ A, |z.1| ≤ R ∧ |z.2| ≤ R := by
    intro z hz
    have h := mem_closedBall.1 (hR hz)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at h
    exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
  set J : Set Pt := Icc 0 0 ×ˢ Icc (-R) R with hJdef
  have hJc : IsCompact J := isCompact_Icc.prod isCompact_Icc
  -- `A ∪ J` does not separate the plane
  have hAJ : IsConnected (A ∩ J) ∨ A ∩ J = ∅ := by
    rcases (A ∩ J).eq_empty_or_nonempty with h | ⟨z, hzA, hzJ⟩
    · exact Or.inr h
    · left
      have hz0 : z.1 = 0 := le_antisymm hzJ.1.2 hzJ.1.1
      have : A ∩ J = {x₀} := by
        ext w
        refine ⟨fun hw => hx₀ w hw.1 (le_antisymm hw.2.1.2 hw.2.1.1), ?_⟩
        rintro rfl
        rw [← hx₀ z hzA hz0]; exact ⟨hzA, hzJ⟩
      rw [this]; exact isConnected_singleton
  set E : Set Pt := (A ∪ J)ᶜ with hEdef
  have hfar : ((R + 1 : ℝ), (0 : ℝ)) ∈ E := by
    rintro (h | h)
    · have := (hb _ h).1; rw [abs_of_pos (by linarith)] at this; linarith
    · have := h.1.2; simp only at this; linarith
  have hE : IsConnected E := by
    have hsub : E ⊆ connectedComponentIn E ((R + 1 : ℝ), (0 : ℝ)) := by
      intro y hy
      by_contra hcon
      exact HPC.Moore.janiszewski_compact hA.1 hJc hAJ
        (not_separatesPts_of_isConnected_compl hAc _ _)
        (not_separatesPts_of_isConnected_compl (HPC.Hagopian.isConnected_compl_rect _ _ _ _).1 _ _)
        ⟨hfar, hy, hcon⟩
    rw [Subset.antisymm hsub (connectedComponentIn_subset _ _)]
    exact isConnected_connectedComponentIn_iff.2 hfar
  -- the far part `F`
  set G : Set Pt := {z : Pt | 0 < z.1} \ A with hGdef
  have hGo : IsOpen G := (isOpen_lt continuous_const continuous_fst).sdiff hA.1.isClosed
  set F : Set Pt := (Ioi 0 ×ˢ Ioi R) ∪ (Ioi R ×ˢ univ) ∪ (Ioi 0 ×ˢ Iio (-R)) with hFdef
  have hFG : F ⊆ G := by
    rintro z ((⟨h1, h2⟩ | ⟨h1, -⟩) | ⟨h1, h2⟩)
    · have h1 : 0 < z.1 := h1
      have h2 : R < z.2 := h2
      exact ⟨h1, fun hz => by have := (hb z hz).2; rw [abs_le] at this; linarith⟩
    · have h1 : R < z.1 := h1
      exact ⟨by show 0 < z.1; linarith, fun hz => by
        have := (hb z hz).1; rw [abs_le] at this; linarith⟩
    · have h1 : 0 < z.1 := h1
      have h2 : z.2 < -R := h2
      exact ⟨h1, fun hz => by have := (hb z hz).2; rw [abs_le] at this; linarith⟩
  have hFc : IsPreconnected F := by
    have c1 : IsPreconnected (Ioi (0 : ℝ) ×ˢ Ioi R) :=
      ((convex_Ioi _).prod (convex_Ioi _)).isPreconnected
    have c2 : IsPreconnected (Ioi R ×ˢ (univ : Set ℝ)) :=
      ((convex_Ioi _).prod convex_univ).isPreconnected
    have c3 : IsPreconnected (Ioi (0 : ℝ) ×ˢ Iio (-R)) :=
      ((convex_Ioi _).prod (convex_Iio _)).isPreconnected
    have c12 := c1.union ((R + 1 : ℝ), (R + 1 : ℝ))
      (show ((R + 1 : ℝ), (R + 1 : ℝ)) ∈ Ioi (0 : ℝ) ×ˢ Ioi R from
        ⟨show (0 : ℝ) < R + 1 by linarith, show R < R + 1 by linarith⟩)
      (show ((R + 1 : ℝ), (R + 1 : ℝ)) ∈ Ioi R ×ˢ (univ : Set ℝ) from
        ⟨show R < R + 1 by linarith, mem_univ _⟩) c2
    exact c12.union ((R + 1 : ℝ), (-R - 1 : ℝ)) (Or.inr ⟨show R < R + 1 by linarith, mem_univ _⟩)
      (show ((R + 1 : ℝ), (-R - 1 : ℝ)) ∈ Ioi (0 : ℝ) ×ˢ Iio (-R) from
        ⟨show (0 : ℝ) < R + 1 by linarith, show -R - 1 < -R by linarith⟩) c3
  have hf₀ : ((R + 1 : ℝ), (0 : ℝ)) ∈ F := Or.inl (Or.inr ⟨show R < R + 1 by linarith, mem_univ _⟩)
  -- every component of `G` meets `F`
  have hmeet : ∀ a ∈ G, (connectedComponentIn G a ∩ F).Nonempty := by
    intro a ha
    by_contra hdisj
    rw [not_nonempty_iff_eq_empty] at hdisj
    set C := connectedComponentIn G a with hCdef
    have hCo : IsOpen C := hGo.connectedComponentIn
    have hCG : C ⊆ G := connectedComponentIn_subset _ _
    set Bx : Set Pt := Icc 0 R ×ˢ Icc (-R) R
    have hCB : C ⊆ Bx := by
      intro z hz
      have hzG := hCG hz
      have hzF : z ∉ F := fun h => (hdisj ▸ (⟨hz, h⟩ : z ∈ C ∩ F) : z ∈ (∅ : Set Pt))
      simp only [hFdef, mem_union, mem_prod, mem_Ioi, mem_Iio, mem_univ, and_true, not_or,
        not_and, not_lt] at hzF
      have h1 : 0 < z.1 := hzG.1
      exact ⟨⟨h1.le, hzF.1.2⟩, ⟨by linarith [hzF.2 h1], hzF.1.1 h1⟩⟩
    have hCE : C ⊆ E := by
      intro z hz
      rintro (h | h)
      · exact (hCG hz).2 h
      · have h1 : 0 < z.1 := (hCG hz).1
        have h2 : z.1 ≤ 0 := h.1.2
        linarith
    have hcl : closure C ∩ E ⊆ C := by
      rintro w ⟨hwc, hwE⟩
      have hwB : w ∈ Bx := closure_minimal hCB (isClosed_Icc.prod isClosed_Icc) hwc
      have hw1 : 0 < w.1 := by
        rcases hwB.1.1.lt_or_eq with h | h
        · exact h
        · exact absurd (Or.inr ⟨⟨h.le, h.symm.le⟩, hwB.2⟩ : w ∈ A ∪ J) hwE
      have hwG : w ∈ G := ⟨hw1, fun h => hwE (Or.inl h)⟩
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hGo w hwG
      obtain ⟨c, hcC, hcb⟩ := Metric.mem_closure_iff.1 hwc ρ hρ
      have hU : IsPreconnected (ball w ρ ∪ C) :=
        (convex_ball w ρ).isPreconnected.union c (mem_ball'.2 hcb) hcC
          (isConnected_connectedComponentIn_iff.2 ha).isPreconnected
      exact hU.subset_connectedComponentIn (Or.inr (mem_connectedComponentIn ha))
        (union_subset hball hCG) (Or.inl (mem_ball_self hρ))
    have := hE.isPreconnected.subset_of_closure_inter_subset hCo
      ⟨a, hCE (mem_connectedComponentIn ha), mem_connectedComponentIn ha⟩ hcl
    have := (hCB (this hfar)).1.2
    simp only at this; linarith
  refine ⟨⟨_, hFG hf₀⟩, isPreconnected_of_forall ((R + 1 : ℝ), (0 : ℝ)) fun y hy => ?_⟩
  obtain ⟨f, hfC, hfF⟩ := hmeet y hy
  refine ⟨connectedComponentIn G y ∪ F, union_subset (connectedComponentIn_subset _ _) hFG,
    Or.inr hf₀, Or.inl (mem_connectedComponentIn hy), ?_⟩
  exact (isConnected_connectedComponentIn_iff.2 hy).isPreconnected.union f hfC hfF hFc

end HPC.Span
