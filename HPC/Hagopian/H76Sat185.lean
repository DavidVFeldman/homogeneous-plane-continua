import HPC.Hagopian.H84Lemma7

/-!
# Batch 185, §4: saturation (2e) by the 1984 Lemma 7

Commission 185 §4.

* `Thm1Setup.kminus_not_subset_O`, `Thm1Setup.kplus_not_subset_O` (§4.2): neither half
  `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` nor `K⁺ = F ∩ h[k⁻¹[[k(e), 1]]]` lies in `π⁻¹[D]`. The tip layer
  meets `d⁻¹(1)` (`tip_meets_end_layer`), Lemma 7 makes it equal to `d⁻¹(1)`, and then `d⁻¹(1)`
  would lie over `D` (`T12Data.end_layer_not_subset`).
* `Thm1Setup.isCrossingPiece_of_crossingComponent_G`: a crossing component of `F ∩ π⁻¹[D]` is a
  crossing piece (as `isCrossingPiece_of_crossingComponent`, with `closure_G_diff_E` for the points
  of `E` in the closure).
* `Thm1Setup.innerComponentsCross_aux` (§4.1, §4.3): saturation.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Sat185

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- S0 over `D`: a point `h(z)` over `D` has `k(z)` within `2/n` of the abscissa, which lies in
`(3/22, 19/22)`. -/
theorem Thm1Setup.fine_over_D (S : Thm1Setup M) (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < S.θ / 4)
    (z : S.E) (hz : S.π (h z : Pt) ∈ S.F '' S.D') :
    ∃ w ∈ S.D', |(S.k z : ℝ) - w.1| < 2 / S.n ∧ w.1 ∈ Ioo (3 / 22 : ℝ) (19 / 22) := by
  obtain ⟨w, hw, hFw⟩ := hz
  have hwR := S.hR.sub hw
  refine ⟨w, hw, S.hS.fine h hh z w ⟨⟨by linarith [hwR.1.1], by linarith [hwR.1.2]⟩,
    by linarith [hwR.2.1, S.hS.c_pos], by linarith [hwR.2.2, S.hc₁]⟩ hFw.symm, hwR.1⟩

theorem Thm1Setup.two_div_n_le (S : Thm1Setup M) : 2 / (S.n : ℝ) ≤ 1 / 20 := by
  have hn' : (40 : ℝ) ≤ S.n := by exact_mod_cast S.hn
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **§4.2, the tip by Lemma 7**: `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` does not lie in `π⁻¹[D]` (for
`h(e) ∈ F`, `k(e) > 2/n`). Steps 1–6 of commission 185 §4.2. -/
theorem Thm1Setup.kminus_not_subset_O (S : Thm1Setup M) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < S.θ / 4) (e : S.E) (he : h e ∈ S.D.G)
    (hke : 2 / (S.n : ℝ) < S.k e) :
    ¬ S.D.G ∩ h '' layerSet S.k (Icc 0 (S.k e)) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'} := by
  intro hsub
  haveI : CompactSpace S.E := isCompact_iff_compactSpace.mp S.hE.isCompact
  have h2n := S.two_div_n_le
  have hmemK : ∀ e' : S.E, S.k e' ≤ S.k e → h e' ∈ S.D.G → S.π (h e' : Pt) ∈ S.F '' S.D' :=
    fun e' h1 h2 => hsub ⟨h2, (e' : M), ⟨e', ⟨unitInterval.nonneg', h1⟩, rfl⟩, rfl⟩
  -- step 1: the tip
  set T : Set S.E := {e' | S.k e' ≤ S.k e} ∩ {e' | h e' ∈ S.D.G} with hT
  have hTc : IsClosed T := (isClosed_le S.hE.2.1.1 continuous_const).inter
    (S.D.hG.isCompact.isClosed.preimage (h.continuous.comp continuous_subtype_val))
  obtain ⟨e₀, he₀T, he₀min⟩ := hTc.isCompact.exists_isMinOn ⟨e, show S.k e ≤ S.k e from le_rfl, he⟩
    S.hE.2.1.1.continuousOn
  have hmin : ∀ e' : S.E, S.k e' ≤ S.k e → h e' ∈ S.D.G → S.k e₀ ≤ S.k e' :=
    fun e' h1 h2 => isMinOn_iff.1 he₀min e' ⟨h1, h2⟩
  -- step 2: the tip meets the end layer
  obtain ⟨e', hke', he'1⟩ := tip_meets_end_layer S.hX S.hi S.hE S.hγπ S.hF S.hS S.hn S.hc₁ S.hR
    S.D.hG S.D.hX0 h hh (S.k e) ⟨e₀, rfl, he₀T.1, he₀T.2, hmemK e₀ he₀T.1 he₀T.2⟩ hmin
  -- the translate as a type λ continuum
  obtain ⟨b, hbE, hblay⟩ := exists_image_map h S.hE
  have hbl : ∀ t, layer b t = h '' layer S.k t := fun t => hblay {t}
  -- step 3: `h[E] ⊄ F`
  have hEG : ((h '' S.E) \ S.D.G).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hne
    obtain ⟨z, hz⟩ := S.hE.2.1.2.1 0
    have hzG : h z ∈ S.D.G := hne ⟨z, z.2, rfl⟩
    obtain ⟨w, -, hw, hw1⟩ := S.fine_over_D h hh z
      (hmemK z (by rw [hz]; exact unitInterval.nonneg') hzG)
    rw [hz] at hw
    simp only [Set.Icc.coe_zero, zero_sub, abs_neg] at hw
    have := (abs_lt.1 hw).2
    linarith [hw1.1]
  -- step 4: `F ⊄ h[E]`
  have hGE : (S.D.G \ h '' S.E).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hne
    obtain ⟨z, hz⟩ := S.hE.2.1.2.1 0
    obtain ⟨z', hz'E, hz'z⟩ := hne (S.D.hEG z.2)
    have hzz : h (⟨z', hz'E⟩ : S.E) = (z : M) := hz'z
    have hπz := pi_E_eq S.hγπ S.hF z
    rw [hz] at hπz
    have hfine := S.hS.fine h hh ⟨z', hz'E⟩ ((0 : ℝ), 0)
      ⟨⟨le_rfl, zero_le_one⟩, by linarith [S.hS.c_pos], S.hS.c_pos.le⟩
      (by rw [hzz]; simpa using hπz)
    simp only [sub_zero] at hfine
    have hk' : S.k ⟨z', hz'E⟩ ≤ S.k e := by
      have h0 := (abs_lt.1 hfine).2
      show (S.k ⟨z', hz'E⟩ : ℝ) ≤ S.k e
      linarith
    have hO := hmemK ⟨z', hz'E⟩ hk' (by rw [hzz]; exact S.D.hEG z.2)
    rw [hzz] at hO
    exact disjoint_left.1 S.disjoint_O_E hO ⟨z, z.2, rfl⟩
  -- step 5: Lemma 7
  obtain ⟨u, hu⟩ := hagopian84_lemma7_aux S.hX S.hi hbE S.D.hG hEG hGE (r := S.k e₀)
    ⟨h e₀, he₀T.2, by rw [hbl]; exact ⟨e₀, ⟨e₀, rfl, rfl⟩, rfl⟩⟩
  have he'b : (h e' : M) ∈ layer b (S.k e₀) := by
    rw [hbl]; exact ⟨e', ⟨e', hke', rfl⟩, rfl⟩
  have hu1 : u = 1 := layer_param_eq (hu ▸ he'b) he'1
  rw [hu1] at hu
  -- step 6: `d⁻¹(1) ⊆ K⁻ ⊆ O`
  apply T12Data.end_layer_not_subset S.hX S.hi S.hE S.hπ S.hπS S.hγπ S.hF S.c₁_le_one S.hR S.hI
    S.hIR S.hFDf S.D
  rintro _ ⟨x, hx, rfl⟩
  have hxG := layer_subset' S.D.d 1 hx
  rw [← hu, hbl] at hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
  have hkz : S.k z = S.k e₀ := hz
  exact hmemK z (hkz ▸ he₀T.1) hxG

/-- **§4.2, the mirror**: `K⁺ = F ∩ h[k⁻¹[[k(e), 1]]]` does not lie in `π⁻¹[D]` (for `h(e) ∈ F`,
`2/n < k(e) < 1 − 2/n`). The tip is the largest parameter (`tip_meets_end_layer_mirror_rel`);
steps 3–4 use `k⁻¹(1)`. -/
theorem Thm1Setup.kplus_not_subset_O (S : Thm1Setup M) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < S.θ / 4) (e : S.E) (he : h e ∈ S.D.G)
    (hke : 2 / (S.n : ℝ) < S.k e) (hke1 : (S.k e : ℝ) < 1 - 2 / S.n) :
    ¬ S.D.G ∩ h '' layerSet S.k (Icc (S.k e) 1) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'} := by
  intro hsub
  haveI : CompactSpace S.E := isCompact_iff_compactSpace.mp S.hE.isCompact
  have h2n := S.two_div_n_le
  have hmemK : ∀ e' : S.E, S.k e ≤ S.k e' → h e' ∈ S.D.G → S.π (h e' : Pt) ∈ S.F '' S.D' :=
    fun e' h1 h2 => hsub ⟨h2, (e' : M), ⟨e', ⟨h1, unitInterval.le_one'⟩, rfl⟩, rfl⟩
  set T : Set S.E := {e' | S.k e ≤ S.k e'} ∩ {e' | h e' ∈ S.D.G} with hT
  have hTc : IsClosed T := (isClosed_le continuous_const S.hE.2.1.1).inter
    (S.D.hG.isCompact.isClosed.preimage (h.continuous.comp continuous_subtype_val))
  obtain ⟨e₀, he₀T, he₀max⟩ := hTc.isCompact.exists_isMaxOn ⟨e, show S.k e ≤ S.k e from le_rfl, he⟩
    S.hE.2.1.1.continuousOn
  have hmax : ∀ e' : S.E, S.k e ≤ S.k e' → h e' ∈ S.D.G → S.k e' ≤ S.k e₀ :=
    fun e' h1 h2 => isMaxOn_iff.1 he₀max e' ⟨h1, h2⟩
  have hσl : 2 / (S.n : ℝ) < S.k e₀ := lt_of_lt_of_le hke he₀T.1
  have hσ1 : (S.k e₀ : ℝ) < 1 := by
    obtain ⟨w, -, hw, hw1⟩ := S.fine_over_D h hh e₀ (hmemK e₀ he₀T.1 he₀T.2)
    have := (abs_lt.1 hw).2
    by_contra h1
    have : (S.k e₀ : ℝ) ≤ 1 := (S.k e₀).2.2
    linarith [hw1.2]
  obtain ⟨e', hke', he'1⟩ := tip_meets_end_layer_mirror_rel S.hX S.hi S.hE S.hγπ S.hF S.hS
    S.D.hG S.D.hX0 h hh (S.k e) ⟨e₀, rfl, he₀T.1, he₀T.2⟩ hσl hσ1 hmax
  obtain ⟨b, hbE, hblay⟩ := exists_image_map h S.hE
  have hbl : ∀ t, layer b t = h '' layer S.k t := fun t => hblay {t}
  have hEG : ((h '' S.E) \ S.D.G).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hne
    obtain ⟨z, hz⟩ := S.hE.2.1.2.1 1
    have hzG : h z ∈ S.D.G := hne ⟨z, z.2, rfl⟩
    obtain ⟨w, -, hw, hw1⟩ := S.fine_over_D h hh z
      (hmemK z (by rw [hz]; exact unitInterval.le_one') hzG)
    rw [hz] at hw
    simp only [Set.Icc.coe_one] at hw
    have := (abs_lt.1 hw).2
    linarith [hw1.2]
  have hGE : (S.D.G \ h '' S.E).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at hne
    obtain ⟨z, hz⟩ := S.hE.2.1.2.1 1
    obtain ⟨z', hz'E, hz'z⟩ := hne (S.D.hEG z.2)
    have hzz : h (⟨z', hz'E⟩ : S.E) = (z : M) := hz'z
    have hπz := pi_E_eq S.hγπ S.hF z
    rw [hz] at hπz
    have hfine := S.hS.fine h hh ⟨z', hz'E⟩ ((1 : ℝ), 0)
      ⟨⟨zero_le_one, le_rfl⟩, by linarith [S.hS.c_pos], S.hS.c_pos.le⟩
      (by rw [hzz]; simpa using hπz)
    have hk' : S.k e ≤ S.k ⟨z', hz'E⟩ := by
      have h0 := (abs_lt.1 hfine).1
      show (S.k e : ℝ) ≤ S.k ⟨z', hz'E⟩
      linarith
    have hO := hmemK ⟨z', hz'E⟩ hk' (by rw [hzz]; exact S.D.hEG z.2)
    rw [hzz] at hO
    exact disjoint_left.1 S.disjoint_O_E hO ⟨z, z.2, rfl⟩
  obtain ⟨u, hu⟩ := hagopian84_lemma7_aux S.hX S.hi hbE S.D.hG hEG hGE (r := S.k e₀)
    ⟨h e₀, he₀T.2, by rw [hbl]; exact ⟨e₀, ⟨e₀, rfl, rfl⟩, rfl⟩⟩
  have he'b : (h e' : M) ∈ layer b (S.k e₀) := by
    rw [hbl]; exact ⟨e', ⟨e', hke', rfl⟩, rfl⟩
  have hu1 : u = 1 := layer_param_eq (hu ▸ he'b) he'1
  rw [hu1] at hu
  apply T12Data.end_layer_not_subset S.hX S.hi S.hE S.hπ S.hπS S.hγπ S.hF S.c₁_le_one S.hR S.hI
    S.hIR S.hFDf S.D
  rintro _ ⟨x, hx, rfl⟩
  have hxG := layer_subset' S.D.d 1 hx
  rw [← hu, hbl] at hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
  have hkz : S.k z = S.k e₀ := hz
  exact hmemK z (hkz ▸ he₀T.1) hxG

/-- A point of `E` in the closure of a subset of `F ∩ π⁻¹[D]` lies over `F(1, 0)`
(`closure_G_diff_E`). -/
theorem Thm1Setup.closure_crossSet_mem_E (S : Thm1Setup M) {C : Set M}
    (hC : C ⊆ crossSet S.D.G S.π S.F S.D') {w : M} (hw : w ∈ closure C) (hwE : w ∈ S.E) :
    S.π (w : Pt) = S.F (1, 0) := by
  have hqGE : (w : Pt) ∈ closure (toPt S.D.G \ toPt S.E) :=
    map_mem_closure continuous_subtype_val hw fun c hc =>
      ⟨⟨c, (hC hc).1, rfl⟩, fun hcE => disjoint_left.1 S.disjoint_O_E (hC hc).2 hcE⟩
  have h1 := closure_G_diff_E S ⟨hqGE, ⟨w, hwE, rfl⟩⟩
  have hF1 : S.F (((1 : unitInterval) : ℝ), 0) = S.γ 1 := S.hF.2.1 1
  rw [S.hγπ 1 _ h1, ← hF1]
  simp

/-- `F(a, s) ≠ F(1, 0)` for `a ≤ 19/22` in the rectangle. -/
theorem Thm1Setup.F_ne_F10 (S : Thm1Setup M) {a s : ℝ} (ha : a ∈ Icc (3 / 22 : ℝ) (19 / 22))
    (hs : s ∈ Icc 0 S.c₁) : S.F (a, s) ≠ S.F (1, 0) := by
  intro h
  have := collar_injOn S.hF (z := (a, s)) (w := (1, 0))
    ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩, by linarith [hs.1], by linarith [hs.2, S.c₁_le_one]⟩
    ⟨⟨by norm_num, le_rfl⟩, by norm_num, by norm_num⟩ h
  have h1 := congrArg Prod.fst this
  simp only at h1
  linarith [ha.2]

/-- **A crossing component of `F ∩ π⁻¹[D]` is a crossing piece** (as
`isCrossingPiece_of_crossingComponent`, for components of `F ∩ π⁻¹[D]`: the points of `E` in the
closure lie over `F(1, 0)`, on neither the bottom edge nor a side segment). -/
theorem Thm1Setup.isCrossingPiece_of_crossingComponent_G (S : Thm1Setup M) {C : Set M}
    (hC : IsCrossingComponent S.D.G S.π S.F S.c₁ S.D' C) :
    IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ (toPt C) := by
  have hCs := hC.subset
  have hclD : ∀ w ∈ closure C, S.π (w : Pt) ∈ closure (S.F '' S.D') := fun w hw =>
    (closure_minimal (s := C) (t := {m : M | S.π (m : Pt) ∈ closure (S.F '' S.D')})
      (fun m hm => subset_closure (hCs hm).2)
      (isClosed_closure.preimage (S.hπ.continuous.comp continuous_subtype_val))) hw
  have hclG : closure C ⊆ S.D.G :=
    closure_minimal (fun m hm => (hCs hm).1) S.D.hG.isCompact.isClosed
  have hside : ∀ w ∈ closure C, ∀ a s : ℝ, (a = 3 / 22 ∨ a = 19 / 22) → s ∈ Icc 0 S.c₁ →
      S.π (w : Pt) = S.F (a, s) → w ∉ S.E := by
    intro w hw a s ha hs hws hwE
    have := S.closure_crossSet_mem_E hCs hw hwE
    exact S.F_ne_F10 (by rcases ha with rfl | rfl <;> constructor <;> norm_num) hs
      (hws.symm.trans this)
  obtain ⟨⟨z, hz, rfl⟩, ⟨xl, hxl, hxlF⟩, ⟨xr, hxr, hxrF⟩⟩ := hC
  refine ⟨isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact (connectedComponentIn_subset _ _ hm).2
  · rw [closure_toPt]
    rintro _ ⟨⟨m, hmc, rfl⟩, hmO⟩
    exact ⟨m, mem_component_of_mem_closure_in hz ⟨hclG hmc, hmO⟩ hmc, rfl⟩
  · rw [closure_toPt]
    exact (isClosed_closure.isCompact).image continuous_subtype_val
  · rw [closure_toPt, disjoint_left]
    rintro _ ⟨m, hmc, rfl⟩ (hI | ⟨⟨x, y⟩, ⟨hx, hy⟩, hFxy⟩)
    · exact disjoint_left.1 S.hI2M hI ⟨m, m.2, rfl⟩
    · simp only [mem_singleton_iff] at hy
      subst hy
      have hmE := mem_E_of_axis S.hE S.hπS S.hγπ S.hF (q := m) (t := x)
        ⟨by linarith [hx.1], by linarith [hx.2]⟩ hFxy.symm
      have := S.closure_crossSet_mem_E (connectedComponentIn_subset _ _) hmc hmE
      exact S.F_ne_F10 hx ⟨le_rfl, S.c₁_pos.le⟩ (hFxy.trans this)
  · obtain ⟨⟨a, s⟩, ⟨ha, hs⟩, hFas⟩ := hxlF
    simp only [mem_singleton_iff] at ha
    subst ha
    have := (side_point_open S.hE S.hπS S.hγπ S.hF S.c₁_le_one S.hR S.hIs S.hFDf S.hI2M
      (hclD xl hxl) (hside xl hxl _ _ (Or.inl rfl) hs hFas.symm) (Or.inl rfl) hs hFas.symm).1 rfl
    rw [closure_toPt]
    exact ⟨xl, ⟨xl, hxl, rfl⟩, ⟨(3 / 22, s), ⟨rfl, this⟩, hFas⟩⟩
  · obtain ⟨⟨a, s⟩, ⟨ha, hs⟩, hFas⟩ := hxrF
    simp only [mem_singleton_iff] at ha
    subst ha
    have := (side_point_open S.hE S.hπS S.hγπ S.hF S.c₁_le_one S.hR S.hIs S.hFDf S.hI2M
      (hclD xr hxr) (hside xr hxr _ _ (Or.inr rfl) hs hFas.symm) (Or.inr rfl) hs hFas.symm).2 rfl
    rw [closure_toPt]
    exact ⟨xr, ⟨xr, hxr, rfl⟩, ⟨(19 / 22, s), ⟨rfl, this⟩, hFas⟩⟩

/-- **§4.1, steps 4–5 of `noncrossing_half_in_O`**: for `y = h(e) ∈ F ∩ π⁻¹[D]` with
`3/22 + 2/n < k(e) < 19/22 − 2/n`, if neither `K⁻` nor `K⁺` lies in `π⁻¹[D]`, the component of `y`
in `F ∩ π⁻¹[D]` is a crossing piece. The components of `K∓ ∩ π⁻¹[D]` through `y` reach side segments
(`half_bump_side`), on the left for `K⁻` and on the right for `K⁺` (S0: a point `h(z)` over the side
`a` has `|k(z) − a| < 2/n`); so the component is a crossing component
(`isCrossingPiece_of_crossingComponent_G`). -/
theorem Thm1Setup.crossing_of_halves (S : Thm1Setup M) {zM : M} (hzG : zM ∈ S.D.G)
    (hzO : (zM : Pt) ∈ S.π ⁻¹' (S.F '' S.D')) (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < S.θ / 4)
    (e : S.E) (hez : h e = zM) (hkl : 3 / 22 + 2 / (S.n : ℝ) < S.k e)
    (hkr : (S.k e : ℝ) < 19 / 22 - 2 / S.n)
    (hm : ¬ S.D.G ∩ h '' layerSet S.k (Icc 0 (S.k e)) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'})
    (hp : ¬ S.D.G ∩ h '' layerSet S.k (Icc (S.k e) 1) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'}) :
    IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) (zM : Pt)) := by
  have he : h e ∈ S.D.G := hez ▸ hzG
  have hzKm : zM ∈ S.D.G ∩ h '' layerSet S.k (Icc 0 (S.k e)) :=
    ⟨hzG, e, ⟨e, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, hez⟩
  have hzKp : zM ∈ S.D.G ∩ h '' layerSet S.k (Icc (S.k e) 1) :=
    ⟨hzG, e, ⟨e, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, hez⟩
  obtain ⟨qm, hqmK, hqmcl, hqmside⟩ := S.half_bump_side (S.kminus_isContinuum h e he)
    inter_subset_left hzKm hzO hm
  obtain ⟨qp, hqpK, hqpcl, hqpside⟩ := S.half_bump_side (S.kplus_isContinuum h e he)
    inter_subset_left hzKp hzO hp
  -- the sides: `K⁻` on the left, `K⁺` on the right (S0)
  have hfine_side : ∀ z : S.E, ∀ a s : ℝ, (a = 3 / 22 ∨ a = 19 / 22) → s ∈ Icc 0 S.c₁ →
      S.π (h z : Pt) = S.F (a, s) → |(S.k z : ℝ) - a| < 2 / S.n := by
    intro z a s ha hs hF
    have := S.hS.fine h hh z (a, s)
      ⟨⟨by rcases ha with rfl | rfl <;> norm_num, by rcases ha with rfl | rfl <;> norm_num⟩,
        by linarith [hs.1, S.hS.c_pos], by linarith [hs.2, S.hc₁]⟩ hF
    simpa using this
  have hqmL : S.π (qm : Pt) ∈ S.F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 S.c₁) := by
    rcases hqmside with ⟨⟨a, s⟩, ⟨ha, hs⟩, hF⟩ | ⟨⟨a, s⟩, ⟨ha, hs⟩, hF⟩
    · exact ⟨⟨a, s⟩, ⟨ha, hs.1, hs.2.trans S.r₂_le⟩, hF⟩
    · exfalso
      simp only [mem_singleton_iff] at ha
      subst ha
      obtain ⟨_, ⟨z, hz, rfl⟩, hzq⟩ := hqmK.2
      have hzk : S.k z ≤ S.k e := hz.2
      have := hfine_side z _ s (Or.inr rfl) ⟨hs.1, hs.2.trans S.s₂_le⟩ (by rw [hzq]; exact hF.symm)
      have h3 := (abs_lt.1 this).1
      have h4 : (S.k z : ℝ) ≤ S.k e := hzk
      linarith
  have hqpR : S.π (qp : Pt) ∈ S.F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 S.c₁) := by
    rcases hqpside with ⟨⟨a, s⟩, ⟨ha, hs⟩, hF⟩ | ⟨⟨a, s⟩, ⟨ha, hs⟩, hF⟩
    · exfalso
      simp only [mem_singleton_iff] at ha
      subst ha
      obtain ⟨_, ⟨z, hz, rfl⟩, hzq⟩ := hqpK.2
      have hzk : S.k e ≤ S.k z := hz.1
      have := hfine_side z _ s (Or.inl rfl) ⟨hs.1, hs.2.trans S.r₂_le⟩ (by rw [hzq]; exact hF.symm)
      have h3 := (abs_lt.1 this).2
      have h4 : (S.k e : ℝ) ≤ S.k z := hzk
      linarith
    · exact ⟨⟨a, s⟩, ⟨ha, hs.1, hs.2.trans S.s₂_le⟩, hF⟩
  -- the component of `y` in `F ∩ π⁻¹[D]` is a crossing component
  have hsub : ∀ K : Set M, K ⊆ S.D.G → zM ∈ K →
      connectedComponentIn (K ∩ Subtype.val ⁻¹' (S.π ⁻¹' (S.F '' S.D'))) zM ⊆
        connectedComponentIn (crossSet S.D.G S.π S.F S.D') zM := by
    intro K hKG hzK
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hzK, hzO⟩)
      ((connectedComponentIn_subset _ _).trans fun m hm => ⟨hKG hm.1, hm.2⟩)
  have hCC : IsCrossingComponent S.D.G S.π S.F S.c₁ S.D'
      (connectedComponentIn (crossSet S.D.G S.π S.F S.D') zM) :=
    ⟨⟨zM, ⟨hzG, hzO⟩, rfl⟩,
      ⟨qm, closure_mono (hsub _ inter_subset_left hzKm) hqmcl, hqmL⟩,
      ⟨qp, closure_mono (hsub _ inter_subset_left hzKp) hqpcl, hqpR⟩⟩
  have heq : toPt (connectedComponentIn (crossSet S.D.G S.π S.F S.D') zM) =
      connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) (zM : Pt) := by
    rw [← toPt_crossSet]; exact image_val_connectedComponentIn _ _
  rw [← heq]
  exact S.isCrossingPiece_of_crossingComponent_G hCC

/-- **§4.3, saturation (2e)** for Hagopian's `F` on `(3/22 + 8/n, 19/22 − 8/n)`. For `y` over that
interval, S1 gives `y = h(e)` with `|k(e) − abscissa| < 1/n`; neither half `K∓` lies in `π⁻¹[D]`
(§4.2, `kminus_not_subset_O`, `kplus_not_subset_O`); then `crossing_of_halves`. -/
theorem Thm1Setup.innerComponentsCross_aux (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) := by
  rintro _ ⟨⟨zM, hzG, rfl⟩, hzO⟩ ⟨q, hqD, hπq, hq1⟩
  have hqR := S.hR.sub hqD
  obtain ⟨h, hh, e, hez, hke⟩ := S.hS.translate zM q
    ⟨⟨by linarith [hqR.1.1], by linarith [hqR.1.2]⟩, by linarith [hqR.2.1, S.hS.c_pos],
      by linarith [hqR.2.2, S.hc₁]⟩ hπq
  have hn' : (40 : ℝ) ≤ S.n := by exact_mod_cast S.hn
  have hnpos : (0 : ℝ) < S.n := by linarith
  have h1n : 1 / (S.n : ℝ) ≤ 1 / 40 := one_div_le_one_div_of_le (by norm_num) hn'
  have e8 : 8 / (S.n : ℝ) = 8 * (1 / S.n) := by ring
  have e2 : 2 / (S.n : ℝ) = 2 * (1 / S.n) := by ring
  have hke' := abs_lt.1 hke
  rw [e8] at hq1
  have hk1 : 2 / (S.n : ℝ) < S.k e := by rw [e2]; linarith [hq1.1, hke'.1]
  have hk2 : (S.k e : ℝ) < 1 - 2 / S.n := by rw [e2]; linarith [hq1.2, hke'.2]
  have hkl : 3 / 22 + 2 / (S.n : ℝ) < S.k e := by rw [e2]; linarith [hq1.1, hke'.1]
  have hkr : (S.k e : ℝ) < 19 / 22 - 2 / S.n := by rw [e2]; linarith [hq1.2, hke'.2]
  have he : h e ∈ S.D.G := hez ▸ hzG
  exact S.crossing_of_halves hzG hzO h hh e hez hkl hkr (S.kminus_not_subset_O h hh e he hk1)
    (S.kplus_not_subset_O h hh e he hk1 hk2)

end Sat185

end HPC.Hagopian
