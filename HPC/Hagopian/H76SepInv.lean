import HPC.Plane.TreeLikeNS
import HPC.Plane.Enc2

/-!
# Batch 157, item E: plane separation is carried over by homeomorphisms (up to subcontinua)

Hagopian 1976, p. 344, cites [5, Lemma 1 (second paragraph of proof)] for "no proper subcontinuum
of `M` separates `R²`". The 1975 paragraph needs, for a separating proper subcontinuum `K`, a
separating continuum in *every* composant; homogeneity gives homeomorphic copies `h[K]`, and the
step "`h[K]` separates the plane" is the topological invariance of plane separation (Borsuk's
theorem), which neither paper states. Here a form sufficient for the argument is proved without
Borsuk, from logarithms and Bing's Theorem 6 (`theorem6_1951`, batch 132–133):

1. `no_log_of_separates`: if a compact `K` separates the plane, then for some `p ∉ K` the function
   `z ↦ z − p` has no continuous logarithm on `K` (a logarithm on `K` extends to a neighbourhood `W`
   by Tietze and a principal-branch correction; a polygon in `W` around `p` carries none,
   `no_log_on_polygon`).
2. `exists_log_of_isTreeLike`: on a tree-like plane continuum every continuous nonvanishing
   function has a continuous logarithm (local branches `log (f z / f a) + log (f a)` glued along a
   fine tree chain, removing leaves; the overlap constants come from `log (u v) = log u + log v`
   near `1`).
3. `exists_separating_subcontinuum_of_homeomorph`: if `K` separates the plane and `K'` is a plane
   continuum homeomorphic to `K`, then some subcontinuum of `K'` separates the plane (otherwise `K'`
   is tree-like by Theorem 6, and a logarithm of `g⁻¹(z) − p` on `K'` would give one of `z − p` on
   `K`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane

/-! ### 1. A separating compactum carries a function without logarithm -/

/-- **A separating compactum.** If the compact set `K` separates the plane, some `p ∉ K` has the
property that `z ↦ z − p` has no continuous logarithm on `K`. -/
theorem no_log_of_separates {K : Set Pt} (hK : IsCompact K) (hs : SeparatesPlane K) :
    ∃ p, p ∉ K ∧ ¬ ∃ L : Pt → ℂ, ContinuousOn L K ∧
      ∀ z ∈ K, Complex.exp (L z) = toCpx z - toCpx p := by
  obtain ⟨p, hpK, hpb⟩ := exists_bounded_component_of_separates hK hs
  refine ⟨p, hpK, ?_⟩
  rintro ⟨L, hLc, hLe⟩
  -- extend `L` to the plane (Tietze)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨Lt, hLt⟩ := ContinuousMap.exists_restrict_eq hK.isClosed
    ⟨K.restrict L, hLc.restrict⟩
  have hLtK : ∀ z ∈ K, Lt z = L z := fun z hz => by
    have := congrArg (fun g : C(K, ℂ) => g ⟨z, hz⟩) hLt
    simpa using this
  -- the correction factor `q z = (z − p) exp (−Lt z)`, equal to `1` on `K`
  set q : Pt → ℂ := fun z => (toCpx z - toCpx p) * Complex.exp (-Lt z) with hq
  have hqc : Continuous q :=
    (continuous_toCpx.sub continuous_const).mul (Complex.continuous_exp.comp Lt.continuous.neg)
  have hqK : ∀ z ∈ K, q z = 1 := fun z hz => by
    simp only [hq, hLtK z hz, ← hLe z hz, Complex.exp_neg]
    exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
  set W : Set Pt := q ⁻¹' ball 1 1 with hW
  have hWo : IsOpen W := isOpen_ball.preimage hqc
  have hKW : K ⊆ W := fun z hz => by
    simp only [hW, mem_preimage, hqK z hz, mem_ball, dist_self, zero_lt_one]
  have hpW : p ∉ W := by
    simp [hW, hq]
  have hslit : ∀ z ∈ W, q z ∈ Complex.slitPlane := by
    intro z hz
    refine Or.inl ?_
    have h1 : dist (q z) 1 < 1 := hz
    rw [Complex.dist_eq] at h1
    have h2 := Complex.abs_re_le_norm (q z - 1)
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith [neg_abs_le ((q z).re - 1)]
  -- a logarithm on `W`
  set L' : Pt → ℂ := fun z => Lt z + Complex.log (q z) with hL'
  have hL'c : ContinuousOn L' W :=
    Lt.continuous.continuousOn.add (hqc.continuousOn.clog hslit)
  have hL'e : ∀ z ∈ W, Complex.exp (L' z) = toCpx z - toCpx p := by
    intro z hz
    have hq0 : q z ≠ 0 := Complex.slitPlane_ne_zero (hslit z hz)
    simp only [hL']
    rw [Complex.exp_add, Complex.exp_log hq0]
    simp only [hq, Complex.exp_neg]
    field_simp
  have hb : Bornology.IsBounded (connectedComponentIn Wᶜ p) :=
    hpb.subset (connectedComponentIn_mono _ (compl_subset_compl.2 hKW))
  obtain ⟨J, hJ, hJW, hpJ⟩ := exists_polygon_around hWo hpW hb
  obtain ⟨n, v, hv, rfl⟩ := isSimpleClosedPolygon_iff.1 hJ
  exact no_log_on_polygon hv hpJ ⟨L', hL'c.mono hJW, fun z hz => hL'e z (hJW hz)⟩

/-! ### 2. Logarithms on tree-like continua -/

/-- Near `1`, the principal logarithm is additive. -/
theorem log_mul_near_one {u v : ℂ} (hu : ‖u - 1‖ < 1 / 2) (hv : ‖v - 1‖ < 1 / 2) :
    Complex.log (u * v) = Complex.log u + Complex.log v := by
  have hre : ∀ w : ℂ, ‖w - 1‖ < 1 / 2 → 0 < w.re := fun w hw => by
    have h2 := Complex.abs_re_le_norm (w - 1)
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith [neg_abs_le (w.re - 1)]
  have hne : ∀ w : ℂ, ‖w - 1‖ < 1 / 2 → w ≠ 0 := fun w hw h => by
    have := hre w hw; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this
  have harg : ∀ w : ℂ, ‖w - 1‖ < 1 / 2 → |w.arg| < Real.pi / 2 := fun w hw =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre w hw))
  refine Complex.log_mul (hne u hu) (hne v hv) ⟨?_, ?_⟩
  · have := harg u hu; have := harg v hv
    linarith [neg_abs_le u.arg, neg_abs_le v.arg]
  · have := harg u hu; have := harg v hv
    linarith [le_abs_self u.arg, le_abs_self v.arg]

section TreeLog

variable {K : Set Pt} {f : Pt → ℂ} {δ m : ℝ}

/-- The local branch of `log f` centred at `a`. -/
noncomputable def branchAt (f : Pt → ℂ) (a : Pt) (z : Pt) : ℂ :=
  Complex.log (f z / f a) + Complex.log (f a)

/-- The standing hypotheses of the gluing: `‖f‖ ≥ m > 0` on `K`, and `f` varies by less than `m/2`
on `δ`-close points of `K`. -/
structure LogData (K : Set Pt) (f : Pt → ℂ) (δ m : ℝ) : Prop where
  pos : 0 < m
  low : ∀ z ∈ K, m ≤ ‖f z‖
  unif : ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → ‖f x - f y‖ < m / 2

theorem LogData.ne_zero (hD : LogData K f δ m) {z : Pt} (hz : z ∈ K) : f z ≠ 0 := fun h => by
  have := hD.low z hz; rw [h, norm_zero] at this; linarith [hD.pos]

theorem LogData.ratio (hD : LogData K f δ m) {x y : Pt} (hx : x ∈ K) (hy : y ∈ K)
    (hxy : dist x y < δ) : ‖f x / f y - 1‖ < 1 / 2 := by
  have hy0 := hD.ne_zero hy
  rw [show f x / f y - 1 = (f x - f y) / f y by field_simp, norm_div,
    div_lt_iff₀ (norm_pos_iff.2 hy0)]
  have h1 := hD.unif x hx y hy hxy
  have h2 := hD.low y hy
  linarith

theorem LogData.exp_branch (hD : LogData K f δ m) {a z : Pt} (ha : a ∈ K) (hz : z ∈ K)
    (hza : dist z a < δ) : Complex.exp (branchAt f a z) = f z := by
  have hr := hD.ratio hz ha hza
  have hr0 : f z / f a ≠ 0 := fun h => by
    rw [h, zero_sub, norm_neg, norm_one] at hr; linarith
  simp only [branchAt, Complex.exp_add, Complex.exp_log hr0, Complex.exp_log (hD.ne_zero ha)]
  field_simp [hD.ne_zero ha]

theorem LogData.continuousOn_branch (hD : LogData K f δ m) (hf : ContinuousOn f K) {a : Pt}
    (ha : a ∈ K) : ContinuousOn (branchAt f a) (K ∩ ball a δ) := by
  refine ContinuousOn.add (ContinuousOn.clog ((hf.mono inter_subset_left).div_const _)
    fun z hz => Or.inl ?_) continuousOn_const
  have hr := hD.ratio hz.1 ha (mem_ball.1 hz.2)
  have h2 := Complex.abs_re_le_norm (f z / f a - 1)
  rw [Complex.sub_re, Complex.one_re] at h2
  linarith [neg_abs_le ((f z / f a).re - 1)]

/-- **The overlap constant.** Two branches centred at `δ`-close points of `K` differ by a constant
(with exponential `1`) at the points of `K` close to both. -/
theorem LogData.branch_sub (hD : LogData K f δ m) {a b z : Pt} (ha : a ∈ K) (hb : b ∈ K)
    (hz : z ∈ K) (hzb : dist z b < δ) (hab : dist b a < δ) :
    branchAt f b z - branchAt f a z =
      Complex.log (f b) - Complex.log (f a) - Complex.log (f b / f a) := by
  have h1 := hD.ratio hz hb hzb
  have h2 := hD.ratio hb ha hab
  have heq : f z / f a = f z / f b * (f b / f a) := by
    field_simp [hD.ne_zero hb, hD.ne_zero ha]
  simp only [branchAt]
  rw [heq, log_mul_near_one h1 h2]
  ring

theorem LogData.exp_const (hD : LogData K f δ m) {a b : Pt} (ha : a ∈ K) (hb : b ∈ K) :
    Complex.exp (Complex.log (f b) - Complex.log (f a) - Complex.log (f b / f a)) = 1 := by
  have ha0 := hD.ne_zero ha
  have hb0 := hD.ne_zero hb
  rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hb0, Complex.exp_log ha0,
    Complex.exp_log (div_ne_zero hb0 ha0)]
  field_simp

/-- **The gluing induction** (the pattern of `exists_log_inv`, batch 133): on a tree chain of links
of diameter `< δ / 2`, each meeting `K`, there is one function agreeing on each link (within `K`)
with a branch centred at a point of that link, up to a constant with exponential `1`. -/
theorem LogData.exists_glue (hLD : LogData K f δ m) :
    ∀ N, ∀ G : Finset (Set Pt), G.card = N → IsTreeChain G →
      (∀ A ∈ G, Bornology.IsBounded A ∧ diam A < δ / 2) → (∀ A ∈ G, (A ∩ K).Nonempty) →
      ∃ L : Pt → ℂ, ∀ A ∈ G, ∃ a ∈ A ∩ K, ∃ κ : ℂ, Complex.exp κ = 1 ∧
        ∀ z ∈ A ∩ K, L z = branchAt f a z + κ := by
  classical
  intro N
  induction N with
  | zero =>
    intro G hG _ _ _
    refine ⟨0, fun A hA => ?_⟩
    rw [Finset.card_eq_zero.1 hG] at hA
    exact absurd hA (Finset.notMem_empty _)
  | succ N ih =>
    intro G hcard hG hdiam hmeet
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      obtain ⟨A, rfl⟩ := Finset.card_eq_one.1 hcard
      obtain ⟨a, ha⟩ := hmeet A (Finset.mem_singleton_self _)
      refine ⟨branchAt f a, fun A' hA' => ?_⟩
      rw [Finset.mem_singleton.1 hA']
      exact ⟨a, ha, 0, Complex.exp_zero, fun z _ => by ring⟩
    · obtain ⟨A, hA, B, hB, hAB, -, hdisj, hGe⟩ := exists_leaf hG (by omega)
      obtain ⟨L₀, hL₀⟩ := ih (G.erase A) (by rw [Finset.card_erase_of_mem hA, hcard]; rfl) hGe
        (fun D hD => hdiam D (Finset.mem_of_mem_erase hD))
        (fun D hD => hmeet D (Finset.mem_of_mem_erase hD))
      have hBe : B ∈ G.erase A := Finset.mem_erase.2 ⟨Ne.symm hAB, hB⟩
      obtain ⟨b, hb, κB, hκB, hL₀B⟩ := hL₀ B hBe
      obtain ⟨a, ha⟩ := hmeet A hA
      set c := Complex.log (f b) - Complex.log (f a) - Complex.log (f b / f a)
      refine ⟨fun z => if z ∈ A then branchAt f a z + (c + κB) else L₀ z, fun D hD => ?_⟩
      by_cases hDA : D = A
      · subst hDA
        refine ⟨a, ha, c + κB, ?_, fun z hz => by simp only [hz.1, if_true]⟩
        rw [Complex.exp_add, hLD.exp_const ha.2 hb.2, hκB, mul_one]
      · have hDe : D ∈ G.erase A := Finset.mem_erase.2 ⟨hDA, hD⟩
        by_cases hDB : D = B
        · subst hDB
          refine ⟨b, hb, κB, hκB, fun z hz => ?_⟩
          by_cases hzA : z ∈ A
          · simp only [hzA, if_true]
            have hdA := hdiam A hA
            have hdB := hdiam D hD
            have hzb : dist z b < δ / 2 :=
              lt_of_le_of_lt (dist_le_diam_of_mem hdB.1 hz.1 hb.1) hdB.2
            have hza : dist z a < δ / 2 :=
              lt_of_le_of_lt (dist_le_diam_of_mem hdA.1 hzA ha.1) hdA.2
            have hab : dist b a < δ := by
              have := dist_triangle b z a
              rw [dist_comm b z] at this; linarith
            have := hLD.branch_sub ha.2 hb.2 hz.2 (by linarith [dist_nonneg (x := z) (y := b)]) hab
            linear_combination -this
          · simp only [hzA, if_false]; exact hL₀B z hz
        · obtain ⟨d, hd, κ, hκ, hL₀D⟩ := hL₀ D hDe
          refine ⟨d, hd, κ, hκ, fun z hz => ?_⟩
          have hzA : z ∉ A := fun hzA => Set.disjoint_left.1 (hdisj D hD hDA hDB) hzA hz.1
          simp only [hzA, if_false]; exact hL₀D z hz

end TreeLog

/-- **Logarithms on tree-like continua.** On a tree-like plane continuum `K`, every function
continuous and nonvanishing on `K` has a continuous logarithm on `K`. -/
theorem exists_log_of_isTreeLike {K : Set Pt} (hK : IsTreeLike K) {f : Pt → ℂ}
    (hf : ContinuousOn f K) (hf0 : ∀ z ∈ K, f z ≠ 0) :
    ∃ L : Pt → ℂ, ContinuousOn L K ∧ ∀ z ∈ K, Complex.exp (L z) = f z := by
  classical
  have hKc := hK.1.1
  have hKne := hK.1.2.nonempty
  -- the lower bound `m`
  obtain ⟨z₀, hz₀K, hz₀⟩ := hKc.exists_isMinOn hKne (continuous_norm.comp_continuousOn hf)
  set m := ‖f z₀‖
  have hm : 0 < m := norm_pos_iff.2 (hf0 z₀ hz₀K)
  have hlow : ∀ z ∈ K, m ≤ ‖f z‖ := fun z hz => hz₀ hz
  -- uniform continuity
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hf) (m / 2) (by positivity)
  have hD : LogData K f δ m := ⟨hm, hlow, fun x hx y hy hxy => by
    have := hδu x hx y hy hxy; rwa [dist_eq_norm] at this⟩
  -- a fine tree chain, filtered to the links meeting `K`
  obtain ⟨G, hG, hGd, hGK⟩ := hK.2 (δ / 2) (by positivity)
  set G' := G.filter fun A => (A ∩ K).Nonempty
  have hG' : IsTreeChain G' := isTreeChain_filter_meet hG hK.1.2 hGK
  obtain ⟨L, hL⟩ := hD.exists_glue G'.card G' rfl hG'
    (fun A hA => hGd A (Finset.mem_filter.1 hA).1) (fun A hA => (Finset.mem_filter.1 hA).2)
  have hcover : ∀ z ∈ K, ∃ A ∈ G', z ∈ A := fun z hz => by
    obtain ⟨A, hA, hzA⟩ := mem_iUnion₂.1 (hGK hz)
    exact ⟨A, Finset.mem_filter.2 ⟨hA, z, hzA, hz⟩, hzA⟩
  have hclose : ∀ A ∈ G', ∀ a ∈ A, ∀ z ∈ A, dist z a < δ := fun A hA a ha z hz => by
    have hd := hGd A (Finset.mem_filter.1 hA).1
    have := lt_of_le_of_lt (dist_le_diam_of_mem hd.1 hz ha) hd.2
    linarith
  refine ⟨L, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨A, hA, hzA⟩ := hcover z hz
    obtain ⟨a, ha, κ, -, hLa⟩ := hL A hA
    have hAo : IsOpen A := hG'.1 A hA
    have hc : ContinuousWithinAt (fun w => branchAt f a w + κ) K z := by
      have h1 := ((hD.continuousOn_branch hf ha.2).add (continuousOn_const (c := κ))) z
        ⟨hz, mem_ball.2 (hclose A hA a ha.1 z hzA)⟩
      refine h1.mono_of_mem_nhdsWithin ?_
      exact inter_mem_nhdsWithin K (isOpen_ball.mem_nhds (mem_ball.2 (hclose A hA a ha.1 z hzA)))
    refine hc.congr_of_eventuallyEq ?_ (hLa z ⟨hzA, hz⟩)
    filter_upwards [inter_mem_nhdsWithin K (hAo.mem_nhds hzA)] with w hw
    exact hLa w ⟨hw.2, hw.1⟩
  · obtain ⟨A, hA, hzA⟩ := hcover z hz
    obtain ⟨a, ha, κ, hκ, hLa⟩ := hL A hA
    rw [hLa z ⟨hzA, hz⟩, Complex.exp_add, hκ, mul_one,
      hD.exp_branch ha.2 hz (hclose A hA a ha.1 z hzA)]

/-! ### 3. Transport of separation -/

/-- **Separation up to subcontinua is a topological invariant.** If the compact set `K` separates
the plane and the plane continuum `K'` is homeomorphic to `K`, then some subcontinuum of `K'`
separates the plane. -/
theorem exists_separating_subcontinuum_of_homeomorph {K K' : Set Pt} (hK : IsCompact K)
    (hs : SeparatesPlane K) (hK' : Fold.Q78.IsContinuum K') (g : K ≃ₜ K') :
    ∃ C ⊆ K', Fold.Q78.IsContinuum C ∧ SeparatesPlane C := by
  by_contra hcon
  push_neg at hcon
  have hT : IsTreeLike K' := theorem6_1951 hK' hcon
  obtain ⟨p, hpK, hnolog⟩ := no_log_of_separates hK hs
  classical
  -- `f z = g⁻¹(z) − p` on `K'`
  set f : Pt → ℂ := fun z => if h : z ∈ K' then toCpx (g.symm ⟨z, h⟩ : Pt) - toCpx p else 1
    with hf
  have hfK : ∀ z (h : z ∈ K'), f z = toCpx (g.symm ⟨z, h⟩ : Pt) - toCpx p := fun z h => by
    simp only [hf, dif_pos h]
  have hfc : ContinuousOn f K' := by
    rw [continuousOn_iff_continuous_restrict]
    have : K'.restrict f = fun w : K' => toCpx (g.symm w : Pt) - toCpx p := by
      funext w; simp only [restrict_apply, hfK w w.2]
    rw [this]
    exact (continuous_toCpx.comp (continuous_subtype_val.comp g.symm.continuous)).sub
      continuous_const
  have hf0 : ∀ z ∈ K', f z ≠ 0 := fun z hz => by
    rw [hfK z hz]
    refine toCpx_sub_ne_zero fun e => hpK ?_
    rw [← e]; exact (g.symm ⟨z, hz⟩).2
  obtain ⟨L, hLc, hLe⟩ := exists_log_of_isTreeLike hT hfc hf0
  apply hnolog
  -- pull back along `g`
  set L₀ : Pt → ℂ := fun z => if h : z ∈ K then L (g ⟨z, h⟩ : Pt) else 0 with hL₀
  have hL₀K : ∀ z (h : z ∈ K), L₀ z = L (g ⟨z, h⟩ : Pt) := fun z h => by
    simp only [hL₀, dif_pos h]
  refine ⟨L₀, ?_, fun z hz => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : K.restrict L₀ = fun w : K => L (g w : Pt) := by
      funext w; simp only [restrict_apply, hL₀K w w.2]
    rw [this]
    exact hLc.restrict.comp g.continuous
  · rw [hL₀K z hz, hLe _ (g ⟨z, hz⟩).2, hfK _ (g ⟨z, hz⟩).2]
    simp

end HPC.Hagopian
