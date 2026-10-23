import HPC.Plane.TreeLikeNS
import HPC.Plane.Fugate66BMiller

/-!
# Batch 145, item C: two plane facts (Brouwer's boundary theorem, Janiszewski's theorem)

Both are proved with logarithms (Eilenberg's method), with no Jordan curve theorem.

* `exists_log_pt`: every continuous nonvanishing `g : Pt → ℂ` has a continuous logarithm (the plane
  is contractible; homotopy lifting through `exp`, `exists_exp_lift` of batch 101).
* `plane_unicoherent`: if `Pt = A ∪ B` with `A`, `B` closed and preconnected (not necessarily
  bounded), then `A ∩ B` is preconnected (the argument of `isUnicoherent_univ_of_contraction`,
  batch 101, without compactness).
* `brouwer_boundary`: the frontier of a component of the complement of a closed connected set is
  connected (from `plane_unicoherent`: `Pt = D̄ ∪ (Pt − D)`).
* Borsuk's criterion, in the two directions used:
  `exists_log_of_mem_component` (if `y` is in the component of `x` in `Kᶜ`, then
  `(z − x)/(z − y)` has a continuous logarithm on `K`; homotopy lifting along a path from `y` to
  `x`) and `no_log_of_bounded_component` (if the component `U` of `x` is bounded and misses `y`,
  there is none: extend the logarithm by Tietze, glue `exp G · (z − y)` on `U` with `z − x` off `U`,
  take a logarithm on the whole plane, and read it on a large circle about `x`).
* `janiszewski_compact`: glue the two logarithms along the connected `A ∩ B`.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane unitInterval

/-! ### Logarithms -/

/-- The contraction `(t, z) ↦ t z` of the plane. -/
noncomputable def ptContraction : C(I × Pt, Pt) where
  toFun p := (p.1 : ℝ) • p.2
  continuous_toFun := by fun_prop

/-- **Every continuous nonvanishing map of the plane to `ℂ` has a continuous logarithm.** -/
theorem exists_log_pt {g : Pt → ℂ} (hg : Continuous g) (hne : ∀ z, g z ≠ 0) :
    ∃ L : Pt → ℂ, Continuous L ∧ ∀ z, Complex.exp (L z) = g z := by
  obtain ⟨G, hG⟩ := exists_exp_lift ptContraction 0 (fun x => by simp [ptContraction])
    (fun x => by simp [ptContraction]) ⟨fun z => ⟨g z, hne z⟩, hg.subtype_mk _⟩
  exact ⟨G, G.continuous, hG⟩

/-- **Homotopy lifting from the constant `1`.** If `Hg` is a homotopy of nonvanishing maps with
`Hg (0, ·) = 1`, then `Hg (1, ·)` has a continuous logarithm. -/
theorem exists_exp_lift_of_homotopy {X : Type*} [TopologicalSpace X]
    (Hg : C(I × X, {z : ℂ // z ≠ 0})) (h0 : ∀ x, (Hg (0, x) : ℂ) = 1) :
    ∃ G : C(X, ℂ), ∀ x, Complex.exp (G x) = Hg (1, x) := by
  have H_0 : ∀ a, Hg (0, a) = (fun z : ℂ => (⟨_, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
      (ContinuousMap.const X 0 a) := by
    intro a; apply Subtype.ext; simp [h0]
  have hcov := Complex.isCoveringMap_exp
  refine ⟨(hcov.liftHomotopy Hg (ContinuousMap.const X 0) H_0).comp
    ((ContinuousMap.const X (1 : I)).prodMk (ContinuousMap.id X)), fun x => ?_⟩
  have := congr_fun (hcov.liftHomotopy_lifts Hg _ H_0) (1, x)
  have := congrArg Subtype.val this
  simpa using this

/-! ### Unicoherence of the plane and Brouwer's theorem -/

/-- **The plane is unicoherent** (for closed preconnected sets, bounded or not): if
`A ∪ B = Pt`, then `A ∩ B` is preconnected. Eilenberg's argument (`isUnicoherent_univ_of_contraction`). -/
theorem plane_unicoherent {A B : Set Pt} (hA : IsClosed A) (hB : IsClosed B)
    (hAc : IsPreconnected A) (hBc : IsPreconnected B) (hAB : A ∪ B = univ) :
    IsPreconnected (A ∩ B) := by
  by_contra hcon
  obtain ⟨P, Q, hP, hQ, hPQ, hdisj, ⟨p, hp⟩, ⟨q, hq⟩⟩ :=
    exists_closed_pieces_of_not_isPreconnected (hA.inter hB) hcon
  obtain ⟨φ, hφP, hφQ, -⟩ := exists_continuous_zero_one_of_isClosed hP hQ hdisj
  have hHKPQ : ∀ x, x ∈ A → x ∈ B → x ∈ P ∪ Q := fun x hxH hxK => by rw [hPQ]; exact ⟨hxH, hxK⟩
  set e : Pt → ℂ := fun x => Complex.exp (2 * Real.pi * Complex.I * (φ x : ℂ)) with he
  have he1 : ∀ x, x ∈ A → x ∈ B → e x = 1 := fun x hxH hxK => by
    rcases hHKPQ x hxH hxK with h | h
    · simp [he, hφP h]
    · simp only [he, hφQ h, Pi.one_apply, Complex.ofReal_one, mul_one]
      exact Complex.exp_two_pi_mul_I
  classical
  set g0 : Pt → ℂ := A.piecewise e (fun _ => 1) with hg0
  have hHcK : Aᶜ ⊆ B := fun x hx => by
    have : x ∈ A ∪ B := hAB ▸ trivial
    exact this.resolve_left hx
  have hg0c : Continuous g0 := by
    refine Continuous.piecewise (fun a ha => ?_) (by fun_prop) continuous_const
    rw [frontier_eq_closure_inter_closure] at ha
    exact he1 a (hA.closure_subset ha.1) (closure_minimal hHcK hB ha.2)
  have hg0K : ∀ x ∈ B, g0 x = 1 := fun x hx => by
    by_cases hxH : x ∈ A
    · rw [hg0, Set.piecewise_eq_of_mem _ _ _ hxH]; exact he1 x hxH hx
    · rw [hg0, Set.piecewise_eq_of_notMem _ _ _ hxH]
  have hg0H : ∀ x ∈ A, g0 x = e x := fun x hx => by
    rw [hg0, Set.piecewise_eq_of_mem _ _ _ hx]
  have hg0ne : ∀ x, g0 x ≠ 0 := fun x => by
    by_cases hxH : x ∈ A
    · rw [hg0H x hxH]; exact Complex.exp_ne_zero _
    · rw [hg0K x (hHcK hxH)]; exact one_ne_zero
  obtain ⟨G, hGc, hG'⟩ := exists_log_pt hg0c hg0ne
  set u : Pt → ℝ := fun x => (G x).im / (2 * Real.pi) with hu
  have huc : Continuous u := (Complex.continuous_im.comp hGc).div_const _
  have hK_int : ∀ x ∈ B, ∃ n : ℤ, u x = n := by
    intro x hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ((hG' x).trans (hg0K x hx))
    refine ⟨n, ?_⟩
    simp only [hu, hn, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    ring
  have hH_int : ∀ x ∈ A, ∃ n : ℤ, u x - φ x = n := by
    intro x hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp ((hG' x).trans (hg0H x hx))
    refine ⟨n, ?_⟩
    simp only [hu, hn, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    ring
  have hpHK : p ∈ A ∩ B := by rw [← hPQ]; exact Or.inl hp
  have hqHK : q ∈ A ∩ B := by rw [← hPQ]; exact Or.inr hq
  have e1 := eq_of_isPreconnected_int_valued hBc huc.continuousOn hK_int hpHK.2 hqHK.2
  have e2 := eq_of_isPreconnected_int_valued (f := fun x => u x - φ x) hAc
    (huc.sub φ.continuous).continuousOn hH_int hpHK.1 hqHK.1
  simp only [hφP hp, hφQ hq, Pi.zero_apply, Pi.one_apply] at e2
  linarith

/-- The frontier of a component of an open set `W` lies outside `W` (locally connected space). -/
theorem frontier_connectedComponentIn_subset {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {W : Set X} (hW : IsOpen W) (x : X) :
    frontier (connectedComponentIn W x) ⊆ Wᶜ := by
  intro a ha haW
  have hUo : IsOpen (connectedComponentIn W x) := hW.connectedComponentIn
  have hVo : IsOpen (connectedComponentIn W a) := hW.connectedComponentIn
  rw [hUo.frontier_eq] at ha
  obtain ⟨b, hbV, hbU⟩ := mem_closure_iff.1 ha.1 _ hVo (mem_connectedComponentIn haW)
  have h1 := connectedComponentIn_eq hbV
  have h2 := connectedComponentIn_eq hbU
  exact ha.2 (h2 ▸ h1 ▸ mem_connectedComponentIn haW)

/-- **Brouwer's theorem** (Math. Ann. 69; used in Moore's Theorem 3): the frontier of a
complementary domain of a closed connected plane set is connected. `M` need not be bounded.
*Shape change:* the skeleton's `hG : MooreDecomp r` (included by the section) is not a hypothesis
here; the statement is about the plane only. -/
theorem brouwer_boundary {M : Set Pt} (hM : IsClosed M) (hMc : IsConnected M) {D : Set Pt}
    (hD : ∃ x ∈ Mᶜ, D = connectedComponentIn Mᶜ x) : IsConnected (frontier D) := by
  obtain ⟨x, hx, rfl⟩ := hD
  set D := connectedComponentIn Mᶜ x with hDdef
  have hDo : IsOpen D := hM.isOpen_compl.connectedComponentIn
  have hDc : IsConnected D := isConnected_connectedComponentIn_iff.2 hx
  have hDM : D ⊆ Mᶜ := connectedComponentIn_subset _ _
  -- `E = Pt − D` is connected: `M` together with the closures of the other components.
  have hEc : IsPreconnected Dᶜ := by
    obtain ⟨m, hm⟩ := hMc.nonempty
    have hmD : m ∈ Dᶜ := fun h => hDM h hm
    have hMD : M ⊆ Dᶜ := fun z hz h => hDM h hz
    refine isPreconnected_of_forall m fun y hy => ?_
    by_cases hyM : y ∈ M
    · exact ⟨M, hMD, hm, hyM, hMc.isPreconnected⟩
    set C := connectedComponentIn Mᶜ y
    have hCo : IsOpen C := hM.isOpen_compl.connectedComponentIn
    have hCc : IsPreconnected (closure C) := isPreconnected_connectedComponentIn.closure
    have hCD : closure C ⊆ Dᶜ := by
      intro z hz hzD
      obtain ⟨w, hwD, hwC⟩ := mem_closure_iff.1 hz D hDo hzD
      have h1 := connectedComponentIn_eq hwD
      have h2 := connectedComponentIn_eq hwC
      exact hy (by rw [hDdef, h1, ← h2]; exact mem_connectedComponentIn hyM)
    -- `closure C` meets `M` (else `C` would be clopen in the plane).
    have hmeet : (M ∩ closure C).Nonempty := by
      by_contra hno
      rw [not_nonempty_iff_eq_empty] at hno
      have hsub : closure C ⊆ C := by
        intro z hz
        have hzM : z ∈ Mᶜ := fun h => (eq_empty_iff_forall_notMem.1 hno) z ⟨h, hz⟩
        by_contra hzC
        exact frontier_connectedComponentIn_subset hM.isOpen_compl y
          ⟨hz, by rw [hCo.interior_eq]; exact hzC⟩ hzM
      have hclopen : IsClopen C := ⟨closure_subset_iff_isClosed.1 hsub, hCo⟩
      rcases isClopen_iff.1 hclopen with h | h
      · exact (h ▸ mem_connectedComponentIn hyM : y ∈ (∅ : Set Pt))
      · exact (connectedComponentIn_subset _ _ (h ▸ mem_univ m : m ∈ C)) hm
    obtain ⟨z, hzM, hzC⟩ := hmeet
    exact ⟨M ∪ closure C, union_subset hMD hCD, Or.inl hm,
      Or.inr (subset_closure (mem_connectedComponentIn hyM)),
      hMc.isPreconnected.union z hzM hzC hCc⟩
  have hcl : IsPreconnected (closure D ∩ Dᶜ) :=
    plane_unicoherent isClosed_closure hDo.isClosed_compl hDc.isPreconnected.closure hEc
      (by rw [eq_univ_iff_forall]; intro z; by_cases h : z ∈ D
          · exact Or.inl (subset_closure h)
          · exact Or.inr h)
  have hfr : frontier D = closure D ∩ Dᶜ := by
    rw [hDo.frontier_eq, diff_eq]
  refine ⟨?_, hfr ▸ hcl⟩
  -- the frontier is nonempty: `D` is a nonempty open proper subset of the plane.
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hclopen : IsClopen D := by
    refine ⟨?_, hDo⟩
    rw [← closure_subset_iff_isClosed]
    intro z hz
    by_contra hzD
    have : z ∈ frontier D := ⟨hz, by rw [hDo.interior_eq]; exact hzD⟩
    rw [hne] at this; exact this
  rcases isClopen_iff.1 hclopen with h | h
  · exact (h ▸ mem_connectedComponentIn hx : x ∈ (∅ : Set Pt))
  · obtain ⟨m, hm⟩ := hMc.nonempty
    exact hDM (h ▸ mem_univ m) hm

/-! ### Borsuk's criterion and Janiszewski's theorem -/

/-- **Same component ⇒ logarithm.** If `y` lies in the component of `x` in `Kᶜ` (`K` closed),
then `(z − x)/(z − y)` has a continuous logarithm on `K`: lift the homotopy
`(t, z) ↦ (z − γ t)/(z − y)` along a path `γ` from `y` to `x` in that component. -/
theorem exists_log_of_mem_component {K : Set Pt} (hK : IsClosed K) {x y : Pt} (hx : x ∉ K)
    (hy : y ∈ connectedComponentIn Kᶜ x) :
    ∃ g : Pt → ℂ, ContinuousOn g K ∧
      ∀ z ∈ K, Complex.exp (g z) = (toCpx z - toCpx x) / (toCpx z - toCpx y) := by
  set C := connectedComponentIn Kᶜ x
  have hCo : IsOpen C := hK.isOpen_compl.connectedComponentIn
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.2 hx
  have hCp : IsPathConnected C := (hCo.isConnected_iff_isPathConnected).1 hCc
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hj := hCp.joinedIn y hy x hxC
  set γ := hj.somePath
  have hγ : ∀ t, γ t ∈ C := hj.somePath_mem
  have hγK : ∀ t, γ t ∉ K := fun t h => connectedComponentIn_subset _ _ (hγ t) h
  have hyK : y ∉ K := fun h => connectedComponentIn_subset _ _ hy h
  have hne : ∀ p : I × K, (toCpx (p.2 : Pt) - toCpx (γ p.1)) / (toCpx (p.2 : Pt) - toCpx y) ≠ 0 := by
    rintro ⟨t, z, hz⟩
    refine div_ne_zero ?_ ?_
    · exact toCpx_sub_ne_zero (fun h => hγK t (h ▸ hz))
    · exact toCpx_sub_ne_zero (fun h => hyK (h ▸ hz))
  set Hg : C(I × K, {z : ℂ // z ≠ 0}) :=
    ⟨fun p => ⟨_, hne p⟩, by
      refine Continuous.subtype_mk ?_ _
      refine Continuous.div ?_ ?_ fun p => ?_
      · exact (continuous_toCpx.comp (continuous_subtype_val.comp continuous_snd)).sub
          (continuous_toCpx.comp (γ.continuous.comp continuous_fst))
      · exact (continuous_toCpx.comp (continuous_subtype_val.comp continuous_snd)).sub
          continuous_const
      · obtain ⟨t, z, hz⟩ := p
        exact toCpx_sub_ne_zero (fun h => hyK (h ▸ hz))⟩ with hHg
  have h0 : ∀ z : K, (Hg (0, z) : ℂ) = 1 := by
    rintro ⟨z, hz⟩
    simp only [hHg, ContinuousMap.coe_mk, Path.source, γ]
    exact div_self (toCpx_sub_ne_zero (fun h => hyK (h ▸ hz)))
  obtain ⟨G, hG⟩ := exists_exp_lift_of_homotopy Hg h0
  classical
  refine ⟨fun z => if h : z ∈ K then G ⟨z, h⟩ else 0, ?_, fun z hz => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    convert G.continuous using 1
    ext ⟨z, hz⟩
    simp [hz]
  · simp only [hz, dite_true, hG]
    simp [hHg, γ]

/-- The complement of a compact set has at most one unbounded component. -/
theorem mem_component_of_unbounded {K : Set Pt} (hK : IsCompact K) {x y : Pt} (hx : x ∉ K)
    (hy : y ∉ K) (hxb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x))
    (hyb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ y)) :
    y ∈ connectedComponentIn Kᶜ x := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Pt)
  have hUK : (closedBall (0 : Pt) R)ᶜ ⊆ Kᶜ := compl_subset_compl.2 hR
  have key : ∀ w, w ∉ K → ¬ Bornology.IsBounded (connectedComponentIn Kᶜ w) →
      (closedBall (0 : Pt) R)ᶜ ⊆ connectedComponentIn Kᶜ w := by
    intro w hw hwb
    have : ¬ connectedComponentIn Kᶜ w ⊆ closedBall 0 R := fun h =>
      hwb (isBounded_closedBall.subset h)
    obtain ⟨v, hv, hvU⟩ := Set.not_subset.1 this
    have hUv := (isPreconnected_compl_closedBall R).subset_connectedComponentIn hvU hUK
    rwa [← connectedComponentIn_eq hv] at hUv
  have h1 := key x hx hxb
  have h2 := key y hy hyb
  set u : Pt := (|R| + 1, 0)
  have huU : u ∈ (closedBall (0 : Pt) R)ᶜ := by
    simp only [u, mem_compl_iff, mem_closedBall, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, norm_zero, not_le]
    rw [abs_of_pos (by positivity : (0:ℝ) < |R| + 1)]
    exact lt_of_lt_of_le (by linarith [le_abs_self R]) (le_max_left _ _)
  have e1 := connectedComponentIn_eq (h1 huU)
  have e2 := connectedComponentIn_eq (h2 huU)
  rw [e1, ← e2]
  exact mem_connectedComponentIn hy

/-- A point of the circle of (euclidean) radius `R` about `x` is at sup-distance `≥ R / 2`. -/
theorem half_le_dist_circle (x : Pt) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    R / 2 ≤ dist (x + (R * Real.cos t, R * Real.sin t)) x := by
  rw [dist_eq_norm, add_sub_cancel_left, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_nonneg hR]
  have hc := Real.cos_sq_add_sin_sq t
  by_contra h
  push_neg at h
  have h1 : R * |Real.cos t| < R / 2 := lt_of_le_of_lt (le_max_left _ _) h
  have h2 : R * |Real.sin t| < R / 2 := lt_of_le_of_lt (le_max_right _ _) h
  have hRp : 0 < R := by
    rcases hR.lt_or_eq with h | h
    · exact h
    · subst h; simp at h
  have h1' : |Real.cos t| < 1 / 2 := by
    by_contra h'; push_neg at h'; nlinarith
  have h2' : |Real.sin t| < 1 / 2 := by
    by_contra h'; push_neg at h'; nlinarith
  have a1 : Real.cos t ^ 2 < 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (Real.cos t)]
  have a2 : Real.sin t ^ 2 < 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (Real.sin t)]
  linarith

/-- **Bounded component ⇒ no logarithm.** If the component `U` of `x` in `Kᶜ` is bounded and
does not contain `y`, then `(z − x)/(z − y)` has no continuous logarithm on `K`. -/
theorem no_log_of_bounded_component {K : Set Pt} (hK : IsCompact K) {x y : Pt}
    (hy : y ∉ K) (hb : Bornology.IsBounded (connectedComponentIn Kᶜ x))
    (hxy : y ∉ connectedComponentIn Kᶜ x) :
    ¬ ∃ g : Pt → ℂ, ContinuousOn g K ∧
      ∀ z ∈ K, Complex.exp (g z) = (toCpx z - toCpx x) / (toCpx z - toCpx y) := by
  rintro ⟨g, hgc, hge⟩
  classical
  have hx : x ∉ K := fun hx => by
    have := hge x hx
    simp at this
  set U := connectedComponentIn Kᶜ x with hU
  have hxU : x ∈ U := mem_connectedComponentIn hx
  have hUo : IsOpen U := hK.isClosed.isOpen_compl.connectedComponentIn
  have hfrU : frontier U ⊆ K := fun a ha => by
    simpa using frontier_connectedComponentIn_subset hK.isClosed.isOpen_compl x ha
  -- Tietze
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hK.isClosed ⟨K.restrict g, hgc.restrict⟩
  have hGg : ∀ z ∈ K, G z = g z := fun z hz => by
    have := congrArg (fun F : C(K, ℂ) => F ⟨z, hz⟩) hG
    simpa using this
  set Ψ : Pt → ℂ := fun z => if z ∈ U then Complex.exp (G z) * (toCpx z - toCpx y)
    else toCpx z - toCpx x with hΨ
  have hΨc : Continuous Ψ := by
    refine Continuous.if (fun a ha => ?_) ?_ ?_
    · have haK := hfrU ha
      rw [hGg a haK, hge a haK]
      have : toCpx a - toCpx y ≠ 0 := toCpx_sub_ne_zero (fun h => hy (h ▸ haK))
      field_simp
    · exact (Complex.continuous_exp.comp G.continuous).mul
        (continuous_toCpx.sub continuous_const)
    · exact continuous_toCpx.sub continuous_const
  have hΨne : ∀ z, Ψ z ≠ 0 := by
    intro z
    by_cases hz : z ∈ U
    · simp only [hΨ, hz, if_true]
      refine mul_ne_zero (Complex.exp_ne_zero _) (toCpx_sub_ne_zero ?_)
      rintro rfl; exact hxy hz
    · simp only [hΨ, hz, if_false]
      refine toCpx_sub_ne_zero ?_
      rintro rfl
      exact hz hxU
  obtain ⟨L, hLc, hLe⟩ := exists_log_pt hΨc hΨne
  obtain ⟨R0, hR0⟩ := hb.subset_closedBall x
  set R : ℝ := 2 * |R0| + 2 with hR
  have hRpos : 0 < R := by positivity
  set c : ℝ → Pt := fun t => x + (R * Real.cos t, R * Real.sin t) with hc
  have hcc : Continuous c := by fun_prop
  have hcU : ∀ t, c t ∉ U := by
    intro t ht
    have h1 := hR0 ht
    rw [mem_closedBall] at h1
    have h2 := half_le_dist_circle x hRpos.le t
    have : R0 ≤ |R0| := le_abs_self R0
    linarith
  have hΨc' : ∀ t : ℝ, Ψ (c t) = Complex.exp (Real.log R + t * Complex.I) := by
    intro t
    simp only [hΨ, hcU t, if_false]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hRpos, Complex.exp_mul_I]
    apply Complex.ext <;> simp [toCpx, hc, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hkey := sub_const_of_exp_eq (S := Icc 0 (2 * Real.pi)) isPreconnected_Icc
    (f := fun t : ℝ => L (c t)) (g := fun t : ℝ => (Real.log R : ℂ) + t * Complex.I)
    (hLc.comp hcc).continuousOn (by fun_prop) (fun t _ => by simp only [hLe, hΨc'])
    (x := 0) (y := 2 * Real.pi) ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩
  have hc0 : c (2 * Real.pi) = c 0 := by simp [hc]
  simp only [hc0] at hkey
  have : (2 * Real.pi : ℂ) * Complex.I = 0 := by
    push_cast at hkey; linear_combination hkey
  simp [Real.pi_ne_zero] at this

/-- **Janiszewski's theorem** (1913; used in Moore's Theorems 2 and 13): if `A`, `B` are compact,
`A ∩ B` is connected or empty, and neither separates `x` from `y`, then `A ∪ B` does not.
Logarithms of `(z − x)/(z − y)` on `A` and on `B` (`exists_log_of_mem_component`) differ by a
constant on the connected `A ∩ B`; glued, they give one on `A ∪ B`, which excludes a bounded
component of `x` or of `y` missing the other (`no_log_of_bounded_component`), and two unbounded
components coincide (`mem_component_of_unbounded`).
*Shape change:* the skeleton's `hG : MooreDecomp r` (included by the section) is not a hypothesis
here. -/
theorem janiszewski_compact {A B : Set Pt} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : IsConnected (A ∩ B) ∨ A ∩ B = ∅) {x y : Pt} (hxA : ¬ SeparatesPts A x y)
    (hxB : ¬ SeparatesPts B x y) : ¬ SeparatesPts (A ∪ B) x y := by
  rintro ⟨hxAB, hyAB, hsep⟩
  have hxA' : x ∉ A := fun h => hxAB (Or.inl h)
  have hxB' : x ∉ B := fun h => hxAB (Or.inr h)
  have hyA' : y ∉ A := fun h => hyAB (Or.inl h)
  have hyB' : y ∉ B := fun h => hyAB (Or.inr h)
  have hyA : y ∈ connectedComponentIn Aᶜ x := by
    by_contra h; exact hxA ⟨hxA', hyA', h⟩
  have hyB : y ∈ connectedComponentIn Bᶜ x := by
    by_contra h; exact hxB ⟨hxB', hyB', h⟩
  obtain ⟨gA, hgAc, hgAe⟩ := exists_log_of_mem_component hA.isClosed hxA' hyA
  obtain ⟨gB, hgBc, hgBe⟩ := exists_log_of_mem_component hB.isClosed hxB' hyB
  obtain ⟨c, hc1, hc⟩ : ∃ c : ℂ, Complex.exp c = 1 ∧ ∀ z ∈ A ∩ B, gA z = gB z + c := by
    rcases hAB with h | h
    · obtain ⟨z0, hz0⟩ := h.nonempty
      refine ⟨gA z0 - gB z0, ?_, fun z hz => ?_⟩
      · rw [Complex.exp_sub, hgAe z0 hz0.1, hgBe z0 hz0.2]
        refine div_self (div_ne_zero ?_ ?_)
        · exact toCpx_sub_ne_zero (fun e => hxA' (e ▸ hz0.1))
        · exact toCpx_sub_ne_zero (fun e => hyA' (e ▸ hz0.1))
      · have := sub_const_of_exp_eq h.isPreconnected (hgAc.mono inter_subset_left)
          (hgBc.mono inter_subset_right) (fun w hw => by rw [hgAe w hw.1, hgBe w hw.2]) hz hz0
        linear_combination this
    · exact ⟨0, Complex.exp_zero, fun z hz => by rw [h] at hz; exact hz.elim⟩
  classical
  set g : Pt → ℂ := fun z => if z ∈ A then gA z else gB z + c with hg
  have hgc : ContinuousOn g (A ∪ B) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ hA.isClosed hB.isClosed
    · exact hgAc.congr (fun z hz => by simp [hg, hz])
    · refine (hgBc.add (continuousOn_const (c := c))).congr (fun z hz => ?_)
      by_cases hzA : z ∈ A
      · simp [hg, hzA, hc z ⟨hzA, hz⟩]
      · simp [hg, hzA]
  have hge : ∀ z ∈ A ∪ B, Complex.exp (g z) = (toCpx z - toCpx x) / (toCpx z - toCpx y) := by
    intro z hz
    by_cases hzA : z ∈ A
    · simp only [hg, hzA, if_true]; exact hgAe z hzA
    · simp only [hg, hzA, if_false]
      rw [Complex.exp_add, hc1, mul_one]
      exact hgBe z (hz.resolve_left hzA)
  have hK : IsCompact (A ∪ B) := hA.union hB
  by_cases hbx : Bornology.IsBounded (connectedComponentIn (A ∪ B)ᶜ x)
  · exact no_log_of_bounded_component hK hyAB hbx hsep ⟨g, hgc, hge⟩
  by_cases hby : Bornology.IsBounded (connectedComponentIn (A ∪ B)ᶜ y)
  · refine no_log_of_bounded_component hK hxAB hby (fun hx => hsep ?_) ⟨fun z => -g z,
      hgc.neg, fun z hz => ?_⟩
    · rw [← connectedComponentIn_eq hx]; exact mem_connectedComponentIn hyAB
    · rw [Complex.exp_neg, hge z hz, inv_div]
  exact hsep (mem_component_of_unbounded hK hxAB hyAB hbx hby)

end HPC.Moore
