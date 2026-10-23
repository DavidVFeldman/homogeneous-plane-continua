import HPC.Moore.M25Plane
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Batch 146: Borsuk's theorem for the plane, the direction used by Mullikin's Theorem 5

`borsuk_exists_log`: if `K` is compact and `Kᶜ` is connected, every continuous nonvanishing
`f : K → ℂ` has a continuous logarithm.

**Proof** (smooth approximation and Sard's theorem, then the logarithms of `M25Plane.lean`).
1. Approximate `f` on `K` by a `C¹` map `G : Pt → Pt` (Stone–Weierstrass), and shift it by a small
   regular value `c` (Sard: the critical values form a null set, `addHaar_image_eq_zero_of_det_...`).
   Put `Φ z = G z − c` (as a complex number). On `K`, `|Φ − f| < |f|`, so `f` has a logarithm iff
   `Φ` has one.
2. Every zero `z₀` of `Φ` is *good*: `Φ z = σ (z − z₀) (γ + small)` near `z₀`, with `σ` the identity
   or complex conjugation (according to the sign of the Jacobian) and `|small| ≤ ρ < |γ|` — a
   real-linear `A w = α w + β w̄` with `det A = |α|² − |β|² ≠ 0`. Good zeros are isolated, so a
   closed ball `B ⊇ K` contains finitely many.
3. Remove the zeros one at a time: divide by `σ (z − z₀)` and modify on a small disc about `z₀`
   missing `K`. When none is left, `Φ` has a logarithm on the convex `B` (homotopy lifting).
4. Each factor `σ (z − z₀)`, `z₀ ∉ K`, has a logarithm on `K`: join `z₀` to a far point in the
   connected `Kᶜ` (`exists_log_of_mem_component`).
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Complex

/-- The identity (`true`) or complex conjugation (`false`). -/
def sgnConj (b : Bool) (w : ℂ) : ℂ := if b then w else (starRingEnd ℂ) w

theorem norm_sgnConj (b : Bool) (w : ℂ) : ‖sgnConj b w‖ = ‖w‖ := by
  cases b <;> simp [sgnConj]

theorem continuous_sgnConj (b : Bool) : Continuous (sgnConj b) := by
  cases b
  · exact Complex.continuous_conj
  · exact continuous_id

/-- A *good zero* of `Φ` at `z₀`: near `z₀`, `Φ z = σ (z − z₀) · (γ + e)` with `|e| ≤ ρ < |γ|`. -/
def IsGoodZero (Φ : Pt → ℂ) (z₀ : Pt) : Prop :=
  ∃ r > 0, ∃ b : Bool, ∃ γ : ℂ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < ‖γ‖ ∧ ∀ z, dist z z₀ < r →
    ‖Φ z - γ * sgnConj b (toCpx z - toCpx z₀)‖ ≤ ρ * ‖toCpx z - toCpx z₀‖

/-- A continuous nonvanishing function on a convex set has a continuous logarithm there. -/
theorem exists_log_of_convex {B : Set Pt} (hB : Convex ℝ B) {h : Pt → ℂ} (hc : ContinuousOn h B)
    (hne : ∀ z ∈ B, h z ≠ 0) :
    ∃ g : Pt → ℂ, ContinuousOn g B ∧ ∀ z ∈ B, Complex.exp (g z) = h z := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact ⟨0, continuousOn_empty _, fun z hz => hz.elim⟩
  have hmem : ∀ p : unitInterval × B, b₀ + (p.1 : ℝ) • ((p.2 : Pt) - b₀) ∈ B := fun p =>
    hB.add_smul_sub_mem hb₀ p.2.2 ⟨p.1.2.1, p.1.2.2⟩
  have hcont : Continuous fun p : unitInterval × B => b₀ + (p.1 : ℝ) • ((p.2 : Pt) - b₀) := by
    fun_prop
  have hne' : ∀ p : unitInterval × B, h (b₀ + (p.1 : ℝ) • ((p.2 : Pt) - b₀)) / h b₀ ≠ 0 :=
    fun p => div_ne_zero (hne _ (hmem p)) (hne b₀ hb₀)
  set Hg : C(unitInterval × B, {z : ℂ // z ≠ 0}) := ⟨fun p => ⟨_, hne' p⟩, by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.div_const ?_ _
    exact hc.comp_continuous hcont hmem⟩ with hHg
  have h0 : ∀ z : B, (Hg (0, z) : ℂ) = 1 := fun z => by
    simp only [hHg, ContinuousMap.coe_mk, Set.Icc.coe_zero, zero_smul, add_zero]
    exact div_self (hne b₀ hb₀)
  obtain ⟨G, hG⟩ := exists_exp_lift_of_homotopy Hg h0
  classical
  refine ⟨fun z => if hz : z ∈ B then G ⟨z, hz⟩ + Complex.log (h b₀) else 0, ?_, fun z hz => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    convert G.continuous.add (continuous_const (y := Complex.log (h b₀))) using 1
    ext ⟨z, hz⟩
    simp [hz]
  · simp only [hz, dite_true, Complex.exp_add, hG, Complex.exp_log (hne b₀ hb₀)]
    simp only [hHg, ContinuousMap.coe_mk, Set.Icc.coe_one, one_smul, add_sub_cancel]
    exact div_mul_cancel₀ _ (hne b₀ hb₀)

/-- If `Kᶜ` is connected, `σ (z − z₀)` has a continuous logarithm on `K` for `z₀ ∉ K`. -/
theorem exists_log_sgnConj {K : Set Pt} (hK : IsCompact K) (hKc : IsConnected Kᶜ) {z₀ : Pt}
    (hz₀ : z₀ ∉ K) (b : Bool) :
    ∃ g : Pt → ℂ, ContinuousOn g K ∧
      ∀ z ∈ K, Complex.exp (g z) = sgnConj b (toCpx z - toCpx z₀) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Pt)
  set y : Pt := (|R| + 1, 0)
  have hre : ∀ z ∈ K, 0 < (toCpx y - toCpx z).re := by
    intro z hz
    have h1 := hR hz
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : |z.1| ≤ ‖z‖ := by
      rw [Prod.norm_def]; exact le_trans (le_of_eq (Real.norm_eq_abs _).symm) (le_max_left _ _)
    have h3 := le_abs_self z.1
    have h4 := le_abs_self R
    show 0 < (|R| + 1) - z.1
    linarith
  have hyK : y ∉ K := fun hy => by
    have := hre y hy
    simp at this
  have hy : y ∈ connectedComponentIn Kᶜ z₀ :=
    hKc.isPreconnected.subset_connectedComponentIn hz₀ subset_rfl hyK
  obtain ⟨g₁, hg₁c, hg₁⟩ := exists_log_of_mem_component hK.isClosed hz₀ hy
  set g : Pt → ℂ := fun z => g₁ z + (Complex.log (toCpx y - toCpx z) + Real.pi * Complex.I)
  have hgc : ContinuousOn g K := by
    refine hg₁c.add (ContinuousOn.add ?_ continuousOn_const)
    intro z hz
    exact (continuousAt_clog (mem_slitPlane_iff.2 (Or.inl (hre z hz)))).comp_continuousWithinAt
      (f := fun z : Pt => toCpx y - toCpx z) (continuous_const.sub continuous_toCpx).continuousWithinAt
  have hge : ∀ z ∈ K, Complex.exp (g z) = toCpx z - toCpx z₀ := by
    intro z hz
    have hne : toCpx y - toCpx z ≠ 0 := fun h => by
      have := hre z hz; rw [h] at this; simp at this
    simp only [g, Complex.exp_add, hg₁ z hz, Complex.exp_log hne, Complex.exp_pi_mul_I]
    have hne' : toCpx z - toCpx y ≠ 0 := fun h => hne (by linear_combination -h)
    field_simp
    ring
  cases b
  · refine ⟨fun z => (starRingEnd ℂ) (g z), Complex.continuous_conj.comp_continuousOn hgc,
      fun z hz => ?_⟩
    simp only [Complex.exp_conj, hge z hz, sgnConj]
    rfl
  · exact ⟨g, hgc, fun z hz => by simp [hge z hz, sgnConj]⟩

/-- Good zeros survive multiplication by a function continuous and nonzero at the zero. -/
theorem IsGoodZero.mul {Φ Ψ m : Pt → ℂ} {z₀ : Pt} (h : IsGoodZero Φ z₀) (hm : ContinuousAt m z₀)
    (hm0 : m z₀ ≠ 0) (hΨ : ∀ᶠ z in 𝓝 z₀, Ψ z = Φ z * m z) : IsGoodZero Ψ z₀ := by
  obtain ⟨r, hr, b, γ, ρ, hρ0, hρ, hest⟩ := h
  set m₀ := m z₀
  have hm₀ : 0 < ‖m₀‖ := norm_pos_iff.2 hm0
  set δ := (‖γ‖ - ρ) * ‖m₀‖ / (2 * (ρ + ‖γ‖ + 1)) with hδ
  have hδ0 : 0 < δ := by
    apply div_pos (mul_pos (by linarith) hm₀); positivity
  have hδ' : (ρ + ‖γ‖) * δ < (‖γ‖ - ρ) * ‖m₀‖ := by
    have hpos : 0 < (‖γ‖ - ρ) * ‖m₀‖ := mul_pos (by linarith) hm₀
    have : (ρ + ‖γ‖ + 1) * δ = (‖γ‖ - ρ) * ‖m₀‖ / 2 := by
      rw [hδ]; field_simp
    nlinarith
  have hev : ∀ᶠ z in 𝓝 z₀, dist z z₀ < r ∧ ‖m z - m₀‖ < δ ∧ Ψ z = Φ z * m z := by
    refine (show ∀ᶠ z in 𝓝 z₀, dist z z₀ < r from ball_mem_nhds z₀ hr).and
      ((?_ : ∀ᶠ z in 𝓝 z₀, ‖m z - m₀‖ < δ).and hΨ)
    have := (Metric.tendsto_nhds.1 hm) δ hδ0
    simpa [dist_eq_norm] using this
  obtain ⟨r', hr', hr'P⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r', hr', b, γ * m₀, ρ * (‖m₀‖ + δ) + ‖γ‖ * δ, by positivity, ?_, fun z hz => ?_⟩
  · rw [norm_mul]; nlinarith
  obtain ⟨hzr, hzm, hzΨ⟩ := hr'P hz
  set w := toCpx z - toCpx z₀
  have hmz : ‖m z‖ ≤ ‖m₀‖ + δ := by
    have := norm_le_norm_add_norm_sub' (m z) m₀
    rw [norm_sub_rev] at this
    linarith [norm_sub_rev (m z) m₀]
  have e : Ψ z - γ * m₀ * sgnConj b w =
      (Φ z - γ * sgnConj b w) * m z + γ * sgnConj b w * (m z - m₀) := by
    rw [hzΨ]; ring
  rw [e]
  have h1 := hest z hzr
  calc ‖(Φ z - γ * sgnConj b w) * m z + γ * sgnConj b w * (m z - m₀)‖
      ≤ ‖(Φ z - γ * sgnConj b w) * m z‖ + ‖γ * sgnConj b w * (m z - m₀)‖ := norm_add_le _ _
    _ = ‖Φ z - γ * sgnConj b w‖ * ‖m z‖ + ‖γ‖ * ‖w‖ * ‖m z - m₀‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_sgnConj]
    _ ≤ (ρ * ‖w‖) * (‖m₀‖ + δ) + ‖γ‖ * ‖w‖ * δ := by
        gcongr
    _ = (ρ * (‖m₀‖ + δ) + ‖γ‖ * δ) * ‖w‖ := by ring

/-- A good zero is isolated: `Φ` does not vanish on a punctured ball about it. -/
theorem IsGoodZero.isolated {Φ : Pt → ℂ} {z₀ : Pt} (h : IsGoodZero Φ z₀) :
    ∃ r > 0, ∀ z, dist z z₀ < r → z ≠ z₀ → Φ z ≠ 0 := by
  obtain ⟨r, hr, b, γ, ρ, -, hρ, hest⟩ := h
  refine ⟨r, hr, fun z hz hne h0 => ?_⟩
  have hw : 0 < ‖toCpx z - toCpx z₀‖ := norm_pos_iff.2 (toCpx_sub_ne_zero hne)
  have h1 := hest z hz
  rw [h0, zero_sub, norm_neg, norm_mul, norm_sgnConj] at h1
  have : (‖γ‖ - ρ) * ‖toCpx z - toCpx z₀‖ ≤ 0 := by nlinarith
  have : 0 < (‖γ‖ - ρ) * ‖toCpx z - toCpx z₀‖ := mul_pos (by linarith) hw
  linarith

/-- **Removing one good zero.** -/
theorem IsGoodZero.remove {Φ : Pt → ℂ} (hΦ : Continuous Φ) {z₀ : Pt} (h : IsGoodZero Φ z₀)
    {r : ℝ} (hr : 0 < r) :
    ∃ b : Bool, ∃ Φ' : Pt → ℂ, Continuous Φ' ∧
      (∀ z, r ≤ dist z z₀ → Φ z = Φ' z * sgnConj b (toCpx z - toCpx z₀)) ∧
      (∀ z, Φ' z = 0 ↔ z ≠ z₀ ∧ Φ z = 0) ∧
      (∀ z, z ≠ z₀ → Φ z = 0 → IsGoodZero Φ z → IsGoodZero Φ' z) := by
  obtain ⟨r₀, hr₀, b, γ, ρ, hρ0, hρ, hest⟩ := h
  classical
  set r₁ := min r (r₀ / 2) with hr₁
  have hr₁0 : 0 < r₁ := lt_min hr (by positivity)
  have hr₁r : r₁ ≤ r := min_le_left _ _
  have hr₁r₀ : r₁ < r₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set ψ : Pt → ℝ := fun z => min 1 (dist z z₀ / r₁) with hψ
  have hψc : Continuous ψ := continuous_const.min ((continuous_id.dist continuous_const).div_const _)
  have hψ0 : ∀ z, 0 ≤ ψ z := fun z => le_min zero_le_one (by positivity)
  have hψ1 : ∀ z, ψ z ≤ 1 := fun z => min_le_left _ _
  have hψeq : ∀ z, r₁ ≤ dist z z₀ → ψ z = 1 := fun z hz =>
    min_eq_left ((one_le_div hr₁0).2 hz)
  set w : Pt → ℂ := fun z => toCpx z - toCpx z₀ with hw
  have hw0 : ∀ z, z ≠ z₀ → sgnConj b (w z) ≠ 0 := fun z hz => by
    rw [← norm_ne_zero_iff, norm_sgnConj, norm_ne_zero_iff]; exact toCpx_sub_ne_zero hz
  set F : Pt → ℂ := fun z => γ + ψ z * (Φ z / sgnConj b (w z) - γ) with hF
  set Φ' : Pt → ℂ := fun z => if z = z₀ then γ else F z with hΦ'
  have hγ0 : γ ≠ 0 := fun h => by rw [h, norm_zero] at hρ; linarith
  -- the estimate near `z₀`
  have hnear : ∀ z, z ≠ z₀ → dist z z₀ < r₀ → ‖Φ z / sgnConj b (w z) - γ‖ ≤ ρ := by
    intro z hz hzd
    have hwpos : 0 < ‖w z‖ := norm_pos_iff.2 (toCpx_sub_ne_zero hz)
    have e : Φ z / sgnConj b (w z) - γ = (Φ z - γ * sgnConj b (w z)) / sgnConj b (w z) := by
      field_simp [hw0 z hz]
    rw [e, norm_div, norm_sgnConj, div_le_iff₀ hwpos]
    exact hest z hzd
  have hFnear : ∀ z, z ≠ z₀ → dist z z₀ < r₀ → ‖F z - γ‖ ≤ ψ z * ρ := by
    intro z hz hzd
    simp only [hF, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hψ0 z)]
    exact mul_le_mul_of_nonneg_left (hnear z hz hzd) (hψ0 z)
  have hFfar : ∀ z, z ≠ z₀ → r₁ ≤ dist z z₀ → F z = Φ z / sgnConj b (w z) := by
    intro z hz hzd
    simp only [hF, hψeq z hzd, Complex.ofReal_one, one_mul, add_sub_cancel]
  refine ⟨b, Φ', ?_, ?_, ?_, ?_⟩
  · -- continuity
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = z₀
    · subst hz
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      rw [Metric.eventually_nhds_iff]
      refine ⟨min r₁ (ε * r₁ / (ρ + 1)), lt_min hr₁0 (by positivity), fun y hy => ?_⟩
      simp only [hΦ', if_pos rfl]
      by_cases hyz : y = z
      · simp [hyz, hε]
      simp only [if_neg hyz, dist_eq_norm]
      have hy1 : dist y z < r₁ := lt_of_lt_of_le hy (min_le_left _ _)
      have hy2 : dist y z < ε * r₁ / (ρ + 1) := lt_of_lt_of_le hy (min_le_right _ _)
      have h1 := hFnear y hyz (by linarith)
      have h2 : ψ y ≤ dist y z / r₁ := min_le_right _ _
      have h3 : dist y z / r₁ < ε / (ρ + 1) := by
        rw [div_lt_iff₀ hr₁0]; calc dist y z < ε * r₁ / (ρ + 1) := hy2
          _ = ε / (ρ + 1) * r₁ := by ring
      calc ‖F y - γ‖ ≤ ψ y * ρ := h1
        _ ≤ ε / (ρ + 1) * ρ := by
            apply mul_le_mul_of_nonneg_right (by linarith) hρ0
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
    · have hev : Φ' =ᶠ[𝓝 z] F := by
        filter_upwards [isOpen_ne.mem_nhds hz] with y hy
        simp [hΦ', hy]
      refine ContinuousAt.congr ?_ hev.symm
      refine continuousAt_const.add (ContinuousAt.mul ?_ ?_)
      · exact (Complex.continuous_ofReal.comp hψc).continuousAt
      · refine ContinuousAt.sub (ContinuousAt.div hΦ.continuousAt ?_ (hw0 z hz)) continuousAt_const
        exact ((continuous_sgnConj b).comp (continuous_toCpx.sub continuous_const)).continuousAt
  · intro z hz
    have hzz : z ≠ z₀ := fun e => by rw [e, dist_self] at hz; linarith
    simp only [hΦ', if_neg hzz, hFfar z hzz (le_trans hr₁r hz)]
    exact (div_mul_cancel₀ _ (hw0 z hzz)).symm
  · intro z
    by_cases hz : z = z₀
    · simp [hΦ', hz, hγ0]
    simp only [hΦ', if_neg hz, ne_eq, hz, not_false_eq_true, true_and]
    by_cases hzd : r₁ ≤ dist z z₀
    · rw [hFfar z hz hzd, div_eq_zero_iff]
      exact ⟨fun h => h.resolve_right (hw0 z hz), Or.inl⟩
    · push_neg at hzd
      have h1 := hFnear z hz (by linarith)
      have h2 : ψ z * ρ < ‖γ‖ := lt_of_le_of_lt (mul_le_of_le_one_left hρ0 (hψ1 z)) hρ
      constructor
      · intro h0
        rw [h0, zero_sub, norm_neg] at h1
        linarith
      · intro h0
        have := hnear z hz (by linarith)
        rw [h0, zero_div, zero_sub, norm_neg] at this
        linarith
  · intro z hz hΦz hgood
    have hzd : r₀ ≤ dist z z₀ := by
      by_contra hlt
      push_neg at hlt
      have := hnear z hz hlt
      rw [hΦz, zero_div, zero_sub, norm_neg] at this
      linarith
    refine hgood.mul (m := fun y => 1 / sgnConj b (w y)) ?_ (one_div_ne_zero (hw0 z hz)) ?_
    · refine continuousAt_const.div ?_ (hw0 z hz)
      exact ((continuous_sgnConj b).comp (continuous_toCpx.sub continuous_const)).continuousAt
    · have hU : ∀ᶠ y in 𝓝 z, r₁ < dist y z₀ :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
          (lt_of_lt_of_le hr₁r₀ hzd)
      filter_upwards [hU] with y hy
      have hyz : y ≠ z₀ := fun e => by rw [e, dist_self] at hy; linarith
      simp only [hΦ', if_neg hyz, hFfar y hyz hy.le]
      ring

/-- **Induction on the zeros.** -/
theorem exists_log_of_goodZeros {K B : Set Pt} (hK : IsCompact K) (hKc : IsConnected Kᶜ)
    (hB : Convex ℝ B) (hKB : K ⊆ B) :
    ∀ n : ℕ, ∀ Φ : Pt → ℂ, Continuous Φ → (∀ z ∈ K, Φ z ≠ 0) →
      {z ∈ B | Φ z = 0}.Finite → {z ∈ B | Φ z = 0}.ncard = n →
      (∀ z ∈ B, Φ z = 0 → IsGoodZero Φ z) →
      ∃ g : Pt → ℂ, ContinuousOn g K ∧ ∀ z ∈ K, Complex.exp (g z) = Φ z := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact fun _ _ _ _ _ _ _ => ⟨0, continuousOn_empty _, fun z hz => hz.elim⟩
  intro n
  induction n with
  | zero =>
    intro Φ hΦ _ hfin hcard _
    have hZ : {z ∈ B | Φ z = 0} = ∅ := (Set.ncard_eq_zero hfin).1 hcard
    obtain ⟨g, hgc, hge⟩ := exists_log_of_convex hB hΦ.continuousOn (fun z hz h0 =>
      (Set.eq_empty_iff_forall_notMem.1 hZ) z (show z ∈ {z ∈ B | Φ z = 0} from ⟨hz, h0⟩))
    exact ⟨g, hgc.mono hKB, fun z hz => hge z (hKB hz)⟩
  | succ n ih =>
    intro Φ hΦ hΦK hfin hcard hgood
    have hne : {z ∈ B | Φ z = 0}.ncard ≠ 0 := by omega
    obtain ⟨z₀, hz₀B, hz₀⟩ := Set.nonempty_of_ncard_ne_zero hne
    have hz₀K : z₀ ∉ K := fun h => hΦK z₀ h hz₀
    have hr : 0 < infDist z₀ K := (hK.isClosed.notMem_iff_infDist_pos hKne).1 hz₀K
    obtain ⟨b, Φ', hΦ'c, hΦeq, hzero, hgood'⟩ := (hgood z₀ hz₀B hz₀).remove hΦ hr
    have hZ' : {z ∈ B | Φ' z = 0} = {z ∈ B | Φ z = 0} \ {z₀} := by
      ext z
      simp only [mem_setOf_eq, mem_diff, mem_singleton_iff, hzero z]
      tauto
    obtain ⟨g', hg'c, hg'e⟩ := ih Φ' hΦ'c
      (fun z hz h0 => hΦK z hz ((hzero z).1 h0).2)
      (by rw [hZ']; exact hfin.diff)
      (by rw [hZ', Set.ncard_diff_singleton_of_mem
        (show z₀ ∈ {z ∈ B | Φ z = 0} from ⟨hz₀B, hz₀⟩), hcard]; simp)
      (fun z hzB h0 => hgood' z ((hzero z).1 h0).1 ((hzero z).1 h0).2
        (hgood z hzB ((hzero z).1 h0).2))
    obtain ⟨g₀, hg₀c, hg₀e⟩ := exists_log_sgnConj hK hKc hz₀K b
    refine ⟨fun z => g' z + g₀ z, hg'c.add hg₀c, fun z hz => ?_⟩
    rw [Complex.exp_add, hg'e z hz, hg₀e z hz]
    exact (hΦeq z (by rw [dist_comm]; exact infDist_le_dist_of_mem hz)).symm

theorem toCpx_add (u v : Pt) : toCpx (u + v) = toCpx u + toCpx v := by
  apply Complex.ext <;> simp [toCpx]

theorem toCpx_sub (u v : Pt) : toCpx (u - v) = toCpx u - toCpx v := by
  apply Complex.ext <;> simp [toCpx]

theorem norm_toCpx_le (u : Pt) : ‖toCpx u‖ ≤ 2 * ‖u‖ := by
  have := norm_toCpx_sub_le u 0
  have h0 : toCpx 0 = 0 := rfl
  rwa [h0, sub_zero, dist_zero_right] at this

/-- A zero with invertible derivative is good. -/
theorem isGoodZero_of_hasFDerivAt {G : Pt → Pt} {A : Pt →L[ℝ] Pt} {z₀ c : Pt}
    (hG : HasFDerivAt G A z₀) (hz₀ : G z₀ = c) (hA : A.det ≠ 0) :
    IsGoodZero (fun z => toCpx (G z) - toCpx c) z₀ := by
  set a := (A (1, 0)).1
  set c' := (A (1, 0)).2
  set b' := (A (0, 1)).1
  set d := (A (0, 1)).2
  set α : ℂ := ⟨(a + d) / 2, (c' - b') / 2⟩
  set β : ℂ := ⟨(a - d) / 2, (c' + b') / 2⟩
  have hAu : ∀ u : Pt, A u = u.1 • A (1, 0) + u.2 • A (0, 1) := by
    intro u
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hlin : ∀ u : Pt, toCpx (A u) = α * toCpx u + β * (starRingEnd ℂ) (toCpx u) := by
    intro u
    rw [hAu u]
    apply Complex.ext <;> simp [toCpx, α, β, a, b', c', d] <;> ring
  have hdet : A.det = ‖α‖ ^ 2 - ‖β‖ ^ 2 := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
      Matrix.det_fin_two, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp [LinearMap.toMatrix_apply, α, β, a, b', c', d]
    ring
  have hne : ‖α‖ ≠ ‖β‖ := fun h => hA (by rw [hdet, h, sub_self])
  -- the error term
  have hsmall : ∀ η > 0, ∃ r > 0, ∀ z, dist z z₀ < r →
      ‖toCpx (G z) - toCpx c - toCpx (A (z - z₀))‖ ≤ 2 * η * ‖toCpx z - toCpx z₀‖ := by
    intro η hη
    obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff.1 (hG.isLittleO.def hη)
    refine ⟨r, hr, fun z hz => ?_⟩
    have h1 := hrP hz
    have e : toCpx (G z) - toCpx c - toCpx (A (z - z₀)) = toCpx (G z - G z₀ - A (z - z₀)) := by
      rw [toCpx_sub, toCpx_sub, hz₀]
    rw [e]
    calc ‖toCpx (G z - G z₀ - A (z - z₀))‖ ≤ 2 * ‖G z - G z₀ - A (z - z₀)‖ := norm_toCpx_le _
      _ ≤ 2 * (η * ‖z - z₀‖) := by linarith
      _ ≤ 2 * η * ‖toCpx z - toCpx z₀‖ := by
          rw [← dist_eq_norm, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (dist_le_norm_toCpx_sub z z₀) hη.le) zero_le_two
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `|α| < |β|`: conjugate
    obtain ⟨r, hr, hrP⟩ := hsmall ((‖β‖ - ‖α‖) / 4) (by linarith)
    refine ⟨r, hr, false, β, ‖α‖ + 2 * ((‖β‖ - ‖α‖) / 4), by linarith [norm_nonneg α],
      by linarith, fun z hz => ?_⟩
    have h1 := hrP z hz
    rw [hlin, toCpx_sub] at h1
    set w := toCpx z - toCpx z₀
    have e : toCpx (G z) - toCpx c - β * sgnConj false w =
        (toCpx (G z) - toCpx c - (α * w + β * (starRingEnd ℂ) w)) + α * w := by
      rw [show sgnConj false w = (starRingEnd ℂ) w from rfl]; ring
    rw [e]
    calc _ ≤ ‖toCpx (G z) - toCpx c - (α * w + β * (starRingEnd ℂ) w)‖ + ‖α * w‖ :=
          norm_add_le _ _
      _ ≤ 2 * ((‖β‖ - ‖α‖) / 4) * ‖w‖ + ‖α‖ * ‖w‖ := by rw [norm_mul]; linarith
      _ = _ := by ring
  · obtain ⟨r, hr, hrP⟩ := hsmall ((‖α‖ - ‖β‖) / 4) (by linarith)
    refine ⟨r, hr, true, α, ‖β‖ + 2 * ((‖α‖ - ‖β‖) / 4), by linarith [norm_nonneg β],
      by linarith, fun z hz => ?_⟩
    have h1 := hrP z hz
    rw [hlin, toCpx_sub] at h1
    set w := toCpx z - toCpx z₀
    have e : toCpx (G z) - toCpx c - α * sgnConj true w =
        (toCpx (G z) - toCpx c - (α * w + β * (starRingEnd ℂ) w)) + β * (starRingEnd ℂ) w := by
      rw [show sgnConj true w = w from rfl]; ring
    rw [e]
    calc _ ≤ ‖toCpx (G z) - toCpx c - (α * w + β * (starRingEnd ℂ) w)‖ +
          ‖β * (starRingEnd ℂ) w‖ := norm_add_le _ _
      _ ≤ 2 * ((‖α‖ - ‖β‖) / 4) * ‖w‖ + ‖β‖ * ‖w‖ := by
          rw [norm_mul, Complex.norm_conj]; linarith
      _ = _ := by ring

/-- Finitely many good zeros in a compact set. -/
theorem finite_zeros_of_goodZeros {B : Set Pt} (hB : IsCompact B) {Φ : Pt → ℂ}
    (hΦ : Continuous Φ) (hgood : ∀ z ∈ B, Φ z = 0 → IsGoodZero Φ z) :
    {z ∈ B | Φ z = 0}.Finite := by
  by_contra hinf
  have hZc : IsCompact {z ∈ B | Φ z = 0} :=
    hB.of_isClosed_subset (hB.isClosed.inter (isClosed_singleton.preimage hΦ))
      (fun z hz => hz.1)
  obtain ⟨x, hx, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hZc subset_rfl
  obtain ⟨r, hr, hiso⟩ := (hgood x hx.1 hx.2).isolated
  obtain ⟨y, ⟨hy, hyZ⟩, hyx⟩ := accPt_iff_nhds.1 hacc (ball x r) (ball_mem_nhds x hr)
  exact hiso y hy hyx hyZ.2

/-- The real `C¹` functions on the plane, as a subalgebra of `C(Pt, ℝ)`. -/
def smoothSub : Subalgebra ℝ C(Pt, ℝ) where
  carrier := {g | ContDiff ℝ 1 (g : Pt → ℝ)}
  mul_mem' {a b} ha hb := by
    show ContDiff ℝ 1 (fun x => a x * b x)
    exact ContDiff.mul ha hb
  add_mem' {a b} ha hb := by
    show ContDiff ℝ 1 (fun x => a x + b x)
    exact ContDiff.add ha hb
  algebraMap_mem' r := by
    show ContDiff ℝ 1 (fun _ => r)
    exact contDiff_const

theorem smoothSub_separatesPoints : smoothSub.SeparatesPoints := by
  intro x y hxy
  by_cases h1 : x.1 = y.1
  · have h2 : x.2 ≠ y.2 := fun h2 => hxy (Prod.ext h1 h2)
    exact ⟨_, ⟨⟨Prod.snd, continuous_snd⟩, (contDiff_snd : ContDiff ℝ 1 (Prod.snd : Pt → ℝ)), rfl⟩,
      h2⟩
  · exact ⟨_, ⟨⟨Prod.fst, continuous_fst⟩, (contDiff_fst : ContDiff ℝ 1 (Prod.fst : Pt → ℝ)), rfl⟩,
      h1⟩

/-- Uniform approximation on a compact set by `C¹` maps. -/
theorem exists_contDiff_near {K : Set Pt} (hK : IsCompact K) {f : Pt → ℂ} (hf : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Pt → Pt, ContDiff ℝ 1 G ∧ ∀ z ∈ K, ‖toCpx (G z) - f z‖ < ε := by
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hK.isClosed ⟨K.restrict f, hf.restrict⟩
  have hFf : ∀ z ∈ K, F z = f z := fun z hz => by
    have := congrArg (fun F : C(K, ℂ) => F ⟨z, hz⟩) hF
    simpa using this
  obtain ⟨u, hu, hu'⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    smoothSub_separatesPoints ⟨fun z => (F z).re, Complex.continuous_re.comp F.continuous⟩ hK
    (ε := ε / 2) (by positivity)
  obtain ⟨v, hv, hv'⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    smoothSub_separatesPoints ⟨fun z => (F z).im, Complex.continuous_im.comp F.continuous⟩ hK
    (ε := ε / 2) (by positivity)
  refine ⟨fun z => (u z, v z), ContDiff.prodMk hu hv, fun z hz => ?_⟩
  have h1 := hu' z hz
  have h2 := hv' z hz
  rw [← hFf z hz]
  refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
  simp only [Real.norm_eq_abs, ContinuousMap.coe_mk] at h1 h2
  simp only [Complex.sub_re, Complex.sub_im, toCpx]
  linarith

/-- Sard (equal dimensions): small regular values exist. -/
theorem exists_small_regular_value {G : Pt → Pt} (hG : ContDiff ℝ 1 G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : Pt, ‖c‖ < δ ∧ ∀ z, G z = c → (fderiv ℝ G z).det ≠ 0 := by
  set S := {z | (fderiv ℝ G z).det = 0}
  have hS : MeasureTheory.volume (G '' S) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero MeasureTheory.volume
      (fun x _ => ?_) (fun x hx => hx)
    exact ((hG.differentiable one_ne_zero) x).hasFDerivAt.hasFDerivWithinAt
  have hb : ¬ ball (0 : Pt) δ ⊆ G '' S := by
    intro h
    have := MeasureTheory.measure_mono (μ := MeasureTheory.volume) h
    rw [hS] at this
    exact (measure_ball_pos MeasureTheory.volume (0 : Pt) hδ).ne' (le_antisymm this (zero_le _))
  obtain ⟨c, hc, hcS⟩ := not_subset.1 hb
  exact ⟨c, by simpa using hc, fun z hz hdet => hcS ⟨z, hdet, hz⟩⟩

/-- A logarithm passes to a function close to `Φ`. -/
theorem exists_log_of_near {K : Set Pt} {f Φ : Pt → ℂ} (hf : ContinuousOn f K)
    (hΦ : ContinuousOn Φ K) (hnear : ∀ z ∈ K, ‖Φ z - f z‖ < ‖f z‖)
    (hlog : ∃ g : Pt → ℂ, ContinuousOn g K ∧ ∀ z ∈ K, Complex.exp (g z) = Φ z) :
    ∃ g : Pt → ℂ, ContinuousOn g K ∧ ∀ z ∈ K, Complex.exp (g z) = f z := by
  obtain ⟨g, hgc, hge⟩ := hlog
  have hf0 : ∀ z ∈ K, f z ≠ 0 := fun z hz h0 => by
    have := hnear z hz
    rw [h0, norm_zero] at this
    exact (norm_nonneg _).not_gt this
  have hslit : ∀ z ∈ K, Φ z / f z ∈ slitPlane := by
    intro z hz
    have h1 : Φ z / f z = 1 + (Φ z - f z) / f z := by
      field_simp [hf0 z hz]; ring
    rw [h1]
    refine mem_slitPlane_of_norm_lt_one ?_
    rw [norm_div, div_lt_one (norm_pos_iff.2 (hf0 z hz))]
    exact hnear z hz
  refine ⟨fun z => g z - Complex.log (Φ z / f z), hgc.sub ?_, fun z hz => ?_⟩
  · intro z hz
    exact (continuousAt_clog (hslit z hz)).comp_continuousWithinAt
      (f := fun z => Φ z / f z) ((hΦ z hz).div (hf z hz) (hf0 z hz))
  · have hΦ0 : Φ z ≠ 0 := by
      intro h0
      have := hslit z hz
      rw [h0, zero_div] at this
      exact slitPlane_ne_zero this rfl
    rw [Complex.exp_sub, hge z hz, Complex.exp_log (div_ne_zero hΦ0 (hf0 z hz))]
    field_simp

/-- **Borsuk's theorem (plane, the direction used here).** If `K` is compact and its complement is
connected, every continuous nonvanishing function on `K` has a continuous logarithm. -/
theorem borsuk_exists_log {K : Set Pt} (hK : IsCompact K) (hKc : IsConnected Kᶜ) {f : Pt → ℂ}
    (hf : ContinuousOn f K) (hne : ∀ z ∈ K, f z ≠ 0) :
    ∃ g : Pt → ℂ, ContinuousOn g K ∧ ∀ z ∈ K, Complex.exp (g z) = f z := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuousOn_empty _, fun z hz => hz.elim⟩
  -- the minimum of `|f|`
  obtain ⟨z₁, hz₁, hmin⟩ := hK.exists_isMinOn hKne (continuous_norm.comp_continuousOn hf)
  set m := ‖f z₁‖
  have hm : 0 < m := norm_pos_iff.2 (hne z₁ hz₁)
  have hmK : ∀ z ∈ K, m ≤ ‖f z‖ := fun z hz => hmin hz
  obtain ⟨G, hGc, hGf⟩ := exists_contDiff_near hK hf (ε := m / 4) (by positivity)
  obtain ⟨c, hc, hreg⟩ := exists_small_regular_value hGc (δ := m / 8) (by positivity)
  set Φ : Pt → ℂ := fun z => toCpx (G z) - toCpx c
  have hΦc : Continuous Φ := (continuous_toCpx.comp hGc.continuous).sub continuous_const
  have hcn : ‖toCpx c‖ < m / 4 := by
    have := norm_toCpx_sub_le c 0
    have h0 : toCpx 0 = 0 := rfl
    rw [h0, sub_zero, dist_zero_right] at this
    linarith
  have hnear : ∀ z ∈ K, ‖Φ z - f z‖ < ‖f z‖ := by
    intro z hz
    have h1 := hGf z hz
    have h2 := hmK z hz
    calc ‖Φ z - f z‖ = ‖(toCpx (G z) - f z) - toCpx c‖ := by congr 1; ring
      _ ≤ ‖toCpx (G z) - f z‖ + ‖toCpx c‖ := norm_sub_le _ _
      _ < ‖f z‖ := by linarith
  have hΦK : ∀ z ∈ K, Φ z ≠ 0 := by
    intro z hz h0
    have := hnear z hz
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  -- a closed ball containing `K`
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Pt)
  have hgood : ∀ z ∈ closedBall (0 : Pt) R, Φ z = 0 → IsGoodZero Φ z := by
    intro z _ hz
    have hGz : G z = c := toCpx_injective (sub_eq_zero.1 hz)
    exact isGoodZero_of_hasFDerivAt ((hGc.differentiable one_ne_zero) z).hasFDerivAt hGz
      (hreg z hGz)
  have hfin := finite_zeros_of_goodZeros (isCompact_closedBall _ _) hΦc hgood
  exact exists_log_of_near hf hΦc.continuousOn hnear
    (exists_log_of_goodZeros hK hKc (convex_closedBall _ _) hR _ Φ hΦc hΦK hfin rfl hgood)

end HPC.Moore
