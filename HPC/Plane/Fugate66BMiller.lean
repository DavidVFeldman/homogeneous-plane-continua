import HPC.Plane.Fugate66BHU

/-!
# Batch 101: the transcribed Miller Theorem 1.5 is false (two half-disks)

The closed unit disk `Disk` of `ℂ` is unicoherent (`isUnicoherent_disk`: a space contractible by an
explicit homotopy is unicoherent, via lifting through `exp` — Eilenberg's argument). It is the union
of the closed half-disks `A = {im ≥ 0}`, `B = {im ≤ 0}`, and its boundary circle is a
non-unicoherent subcontinuum lying in neither half (`miller_1_5_false`).
-/

namespace HPC.Plane

open Set Topology Metric unitInterval

/-- **Lifting through `exp`** on a space contracted to a point by a homotopy `Hc`: every continuous
map to `ℂ ∖ {0}` has a continuous logarithm (homotopy lifting for the covering `exp`). -/
theorem exists_exp_lift {X : Type*} [TopologicalSpace X] (Hc : C(I × X, X)) (x₀ : X)
    (h0 : ∀ x, Hc (0, x) = x₀) (h1 : ∀ x, Hc (1, x) = x)
    (g : C(X, {z : ℂ // z ≠ 0})) : ∃ G : C(X, ℂ), ∀ x, Complex.exp (G x) = g x := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, Complex.exp c = g x₀ := ⟨Complex.log (g x₀), Complex.exp_log (g x₀).2⟩
  set Hg : C(I × X, {z : ℂ // z ≠ 0}) := g.comp Hc with hHg
  have H_0 : ∀ a, Hg (0, a) = (fun z : ℂ => (⟨_, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
      (ContinuousMap.const X c a) := by
    intro a; apply Subtype.ext; simp [Hg, h0, hc]
  have hcov := Complex.isCoveringMap_exp
  refine ⟨(hcov.liftHomotopy Hg (ContinuousMap.const X c) H_0).comp
    ((ContinuousMap.const X (1 : I)).prodMk (ContinuousMap.id X)), fun x => ?_⟩
  have := congr_fun (hcov.liftHomotopy_lifts Hg _ H_0) (1, x)
  have := congrArg Subtype.val this
  simpa [Hg, h1] using this

/-- An integer-valued continuous real function on a preconnected set is constant. -/
theorem eq_of_isPreconnected_int_valued {X : Type*} [TopologicalSpace X] {Z : Set X}
    (hZ : IsPreconnected Z) {f : X → ℝ} (hf : ContinuousOn f Z) (hint : ∀ x ∈ Z, ∃ n : ℤ, f x = n)
    {x y : X} (hx : x ∈ Z) (hy : y ∈ Z) : f x = f y := by
  wlog hxy : f x ≤ f y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  obtain ⟨n, hn⟩ := hint x hx
  obtain ⟨n', hn'⟩ := hint y hy
  by_contra hne
  have hlt : n < n' := by
    have := lt_of_le_of_ne hxy hne
    rw [hn, hn'] at this
    exact_mod_cast this
  have hlt' : (n : ℝ) + 1 ≤ n' := by exact_mod_cast hlt
  obtain ⟨z, hz, hfz⟩ := hZ.intermediate_value hx hy hf
    (show (n : ℝ) + 1 / 2 ∈ Icc (f x) (f y) from ⟨by rw [hn]; linarith, by rw [hn']; linarith⟩)
  obtain ⟨m, hm⟩ := hint z hz
  rw [hm] at hfz
  have h2 : ((2 * m : ℤ) : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by push_cast; linarith
  have h3 : 2 * m = 2 * n + 1 := by exact_mod_cast h2
  omega

/-- **A compact metric space contractible by an explicit homotopy is unicoherent.** If
`X = H ∪ K` with `H ∩ K = P ⊔ Q`, take Urysohn `φ` (`0` on `P`, `1` on `Q`) and the map `g` equal to
`exp (2πiφ)` on `H` and to `1` on `K`; its logarithm `G` has `Im G / 2π` integer-valued on `K` and
`Im G / 2π − φ` integer-valued on `H`, so both are constant, which is impossible at `p ∈ P`,
`q ∈ Q`. -/
theorem isUnicoherent_univ_of_contraction {X : Type*} [MetricSpace X] [ConnectedSpace X]
    (Hc : C(I × X, X)) (x₀ : X) (h0 : ∀ x, Hc (0, x) = x₀) (h1 : ∀ x, Hc (1, x) = x) :
    IsUnicoherent (univ : Set X) := by
  intro H K hH hK hHK
  have hne : (H ∩ K).Nonempty := by
    obtain ⟨z, -, hz⟩ := inter_nonempty_of_cover isPreconnected_univ hH.1.isClosed hK.1.isClosed
      hHK.symm.subset (by obtain ⟨x, hx⟩ := hH.2.nonempty; exact ⟨x, trivial, hx⟩)
      (by obtain ⟨x, hx⟩ := hK.2.nonempty; exact ⟨x, trivial, hx⟩)
    exact ⟨z, hz⟩
  refine ⟨hne, ?_⟩
  by_contra hcon
  obtain ⟨P, Q, hP, hQ, hPQ, hdisj, ⟨p, hp⟩, ⟨q, hq⟩⟩ :=
    exists_closed_pieces_of_not_isPreconnected (hH.1.isClosed.inter hK.1.isClosed) hcon
  obtain ⟨φ, hφP, hφQ, -⟩ := exists_continuous_zero_one_of_isClosed hP hQ hdisj
  have hHKPQ : ∀ x, x ∈ H → x ∈ K → x ∈ P ∪ Q := fun x hxH hxK => by rw [hPQ]; exact ⟨hxH, hxK⟩
  set e : X → ℂ := fun x => Complex.exp (2 * Real.pi * Complex.I * (φ x : ℂ)) with he
  have he1 : ∀ x, x ∈ H → x ∈ K → e x = 1 := fun x hxH hxK => by
    rcases hHKPQ x hxH hxK with h | h
    · simp [he, hφP h]
    · simp only [he, hφQ h, Pi.one_apply, Complex.ofReal_one, mul_one]
      exact Complex.exp_two_pi_mul_I
  classical
  set g0 : X → ℂ := H.piecewise e (fun _ => 1) with hg0
  have hHcK : Hᶜ ⊆ K := fun x hx => by
    have : x ∈ H ∪ K := hHK ▸ trivial
    exact this.resolve_left hx
  have hg0c : Continuous g0 := by
    refine Continuous.piecewise (fun a ha => ?_) (by fun_prop) continuous_const
    rw [frontier_eq_closure_inter_closure] at ha
    exact he1 a (hH.1.isClosed.closure_subset ha.1)
      (closure_minimal hHcK hK.1.isClosed ha.2)
  have hg0K : ∀ x ∈ K, g0 x = 1 := fun x hx => by
    by_cases hxH : x ∈ H
    · rw [hg0, Set.piecewise_eq_of_mem _ _ _ hxH]; exact he1 x hxH hx
    · rw [hg0, Set.piecewise_eq_of_notMem _ _ _ hxH]
  have hg0H : ∀ x ∈ H, g0 x = e x := fun x hx => by
    rw [hg0, Set.piecewise_eq_of_mem _ _ _ hx]
  have hg0ne : ∀ x, g0 x ≠ 0 := fun x => by
    by_cases hxH : x ∈ H
    · rw [hg0H x hxH]; exact Complex.exp_ne_zero _
    · rw [hg0K x (hHcK hxH)]; exact one_ne_zero
  set g : C(X, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨g0 x, hg0ne x⟩, hg0c.subtype_mk _⟩ with hg
  obtain ⟨G, hG⟩ := exists_exp_lift Hc x₀ h0 h1 g
  have hG' : ∀ x, Complex.exp (G x) = g0 x := fun x => hG x
  set u : X → ℝ := fun x => (G x).im / (2 * Real.pi) with hu
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have huc : Continuous u := (Complex.continuous_im.comp G.continuous).div_const _
  have hK_int : ∀ x ∈ K, ∃ n : ℤ, u x = n := by
    intro x hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ((hG' x).trans (hg0K x hx))
    refine ⟨n, ?_⟩
    simp only [hu, hn, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    ring
  have hH_int : ∀ x ∈ H, ∃ n : ℤ, u x - φ x = n := by
    intro x hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp ((hG' x).trans (hg0H x hx))
    refine ⟨n, ?_⟩
    simp only [hu, hn, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    ring
  have hpHK : p ∈ H ∩ K := by rw [← hPQ]; exact Or.inl hp
  have hqHK : q ∈ H ∩ K := by rw [← hPQ]; exact Or.inr hq
  have e1 := eq_of_isPreconnected_int_valued hK.2.isPreconnected huc.continuousOn hK_int
    hpHK.2 hqHK.2
  have e2 := eq_of_isPreconnected_int_valued (f := fun x => u x - φ x) hH.2.isPreconnected
    (huc.sub φ.continuous).continuousOn hH_int hpHK.1 hqHK.1
  simp only [hφP hp, hφQ hq, Pi.zero_apply, Pi.one_apply] at e2
  linarith

/-! ## The disk -/

/-- The closed unit disk of `ℂ`, a compact metric space. -/
abbrev Disk : Type := Metric.closedBall (0 : ℂ) 1

instance : ConnectedSpace Disk :=
  isConnected_iff_connectedSpace.mp
    ⟨⟨0, mem_closedBall_self zero_le_one⟩, (convex_closedBall (0 : ℂ) 1).isPreconnected⟩

/-- The contraction `(t, z) ↦ t z` of the disk. -/
noncomputable def diskContraction : C(I × Disk, Disk) where
  toFun p := ⟨((p.1 : ℝ) : ℂ) * (p.2 : ℂ), by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg p.1.2.1]
    exact mul_le_one₀ p.1.2.2 (norm_nonneg _) (mem_closedBall_zero_iff.mp p.2.2)⟩
  continuous_toFun := by fun_prop

/-- **The closed disk is unicoherent.** -/
theorem isUnicoherent_disk : IsUnicoherent (univ : Set Disk) :=
  isUnicoherent_univ_of_contraction diskContraction ⟨0, mem_closedBall_self zero_le_one⟩
    (fun x => by ext; simp [diskContraction]) (fun x => by ext; simp [diskContraction])

theorem isPreconnected_disk_iff (s : Set Disk) :
    IsPreconnected s ↔ IsPreconnected ((↑) '' s : Set ℂ) :=
  (Topology.IsInducing.subtypeVal.isPreconnected_image).symm

/-- The closed upper half-disk. -/
def diskA : Set Disk := {z | 0 ≤ (z : ℂ).im}
/-- The closed lower half-disk. -/
def diskB : Set Disk := {z | (z : ℂ).im ≤ 0}
/-- The boundary circle. -/
def diskD : Set Disk := {z | ‖(z : ℂ)‖ = 1}

theorem norm_eq_one_iff' (z : ℂ) : ‖z‖ = 1 ↔ z.re * z.re + z.im * z.im = 1 := by
  rw [← Complex.normSq_apply, ← Complex.sq_norm]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have := norm_nonneg z
    nlinarith [sq_nonneg (‖z‖ - 1), sq_nonneg (‖z‖ + 1)]

/-- The upper (`s = 1`) or lower (`s = -1`) semicircle is the image of `[-1, 1]`. -/
theorem semicircle_eq_image (s : ℝ) (hs : s = 1 ∨ s = -1) :
    {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ s * z.im} =
      (fun x : ℝ => (⟨x, s * √(1 - x ^ 2)⟩ : ℂ)) '' Icc (-1) 1 := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  ext z
  simp only [mem_setOf_eq, mem_image, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    rw [norm_eq_one_iff'] at h1
    have hre : z.re ^ 2 ≤ 1 := by nlinarith [mul_self_nonneg z.im]
    refine ⟨z.re, ⟨by nlinarith [sq_nonneg (z.re + 1)], by nlinarith [sq_nonneg (z.re - 1)]⟩, ?_⟩
    apply Complex.ext
    · simp
    · simp only []
      have : 1 - z.re ^ 2 = (s * z.im) ^ 2 := by nlinarith
      rw [this, Real.sqrt_sq h2, ← mul_assoc, hs2, one_mul]
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have h0 : 0 ≤ 1 - x ^ 2 := by nlinarith
    refine ⟨?_, ?_⟩
    · rw [norm_eq_one_iff']
      simp only []
      have := Real.sq_sqrt h0
      nlinarith
    · simp only []
      rw [← mul_assoc, hs2, one_mul]
      exact Real.sqrt_nonneg _

theorem isContinuum_semicircle (s : ℝ) (hs : s = 1 ∨ s = -1) :
    Fold.Q78.IsContinuum (diskD ∩ {z : Disk | 0 ≤ s * (z : ℂ).im}) := by
  refine ⟨(isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const).inter
    (isClosed_le continuous_const (continuous_const.mul
      (Complex.continuous_im.comp continuous_subtype_val))) |>.isCompact, ?_, ?_⟩
  · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
    · show ‖(1 : ℂ)‖ = 1; simp
    · show 0 ≤ s * (1 : ℂ).im; simp
  · rw [isPreconnected_disk_iff]
    have : ((↑) '' (diskD ∩ {z : Disk | 0 ≤ s * (z : ℂ).im}) : Set ℂ) =
        {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ s * z.im} := by
      ext z
      constructor
      · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩; exact ⟨hw1, hw2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨z, mem_closedBall_zero_iff.mpr h1.le⟩, ⟨h1, h2⟩, rfl⟩
    rw [this, semicircle_eq_image s hs]
    have hfun : (fun x : ℝ => (⟨x, s * √(1 - x ^ 2)⟩ : ℂ)) =
        fun x : ℝ => (x : ℂ) + ((s * √(1 - x ^ 2) : ℝ) : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [hfun]
    exact isPreconnected_Icc.image _ (by fun_prop)

/-- **The transcribed `miller_1_5` is false**: in the closed unit disk, `A` (upper half), `B`
(lower half) are continua with `A ∪ B` the whole (unicoherent) disk; the boundary circle `D` is a
non-unicoherent subcontinuum contained in neither half. -/
theorem miller_1_5_false : ¬ ∀ (S : Type) [MetricSpace S] [CompactSpace S] (A B D : Set S),
    Fold.Q78.IsContinuum A → Fold.Q78.IsContinuum B → IsUnicoherent (A ∪ B) →
    Fold.Q78.IsContinuum D → D ⊆ A ∪ B → ¬ IsUnicoherent D → D ⊆ A ∨ D ⊆ B := by
  intro h
  have hAB : diskA ∪ diskB = univ := by
    ext z; simp only [diskA, diskB, mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact le_total _ _
  have halfc : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      Fold.Q78.IsContinuum {z : Disk | 0 ≤ s * (z : ℂ).im} := by
    intro s hs
    refine ⟨(isClosed_le continuous_const (continuous_const.mul
      (Complex.continuous_im.comp continuous_subtype_val))).isCompact,
      ⟨⟨0, mem_closedBall_self zero_le_one⟩, by simp⟩, ?_⟩
    rw [isPreconnected_disk_iff]
    have : ((↑) '' {z : Disk | 0 ≤ s * (z : ℂ).im} : Set ℂ) =
        closedBall 0 1 ∩ {z : ℂ | 0 ≤ s * z.im} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨z, h1⟩, h2, rfl⟩
    rw [this]
    refine ((convex_closedBall 0 1).inter ?_).isPreconnected
    rcases hs with rfl | rfl
    · simpa using convex_halfSpace_im_ge 0
    · simpa using convex_halfSpace_im_le 0
  have hA : Fold.Q78.IsContinuum diskA := by simpa [diskA] using halfc 1 (Or.inl rfl)
  have hB : Fold.Q78.IsContinuum diskB := by
    have := halfc (-1) (Or.inr rfl)
    simpa [diskB, neg_mul, neg_nonneg] using this
  have hD : Fold.Q78.IsContinuum diskD := by
    refine ⟨(isClosed_eq (continuous_norm.comp continuous_subtype_val)
      continuous_const).isCompact, ⟨⟨1, by simp⟩, show ‖(1 : ℂ)‖ = 1 by simp⟩, ?_⟩
    rw [isPreconnected_disk_iff]
    have : ((↑) '' diskD : Set ℂ) = sphere 0 1 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; exact mem_sphere_zero_iff_norm.mpr hw
      · intro hz
        exact ⟨⟨z, mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp hz).le⟩,
          mem_sphere_zero_iff_norm.mp hz, rfl⟩
    rw [this]
    exact isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 1
  -- `D` is not unicoherent
  have hnu : ¬ IsUnicoherent diskD := by
    intro hu
    have hH := isContinuum_semicircle 1 (Or.inl rfl)
    have hK := isContinuum_semicircle (-1) (Or.inr rfl)
    have hHK : diskD ∩ {z : Disk | 0 ≤ (1 : ℝ) * (z : ℂ).im} ∪
        diskD ∩ {z : Disk | 0 ≤ (-1 : ℝ) * (z : ℂ).im} = diskD := by
      ext z
      simp only [mem_union, mem_inter_iff, mem_setOf_eq, one_mul, neg_one_mul, neg_nonneg]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        rcases le_total 0 (z : ℂ).im with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
    have hc := hu _ _ hH hK hHK
    set one : Disk := ⟨1, by simp⟩
    set mone : Disk := ⟨-1, by simp⟩
    have hmem : ∀ w : Disk, ‖(w : ℂ)‖ = 1 → (w : ℂ).im = 0 →
        w ∈ (diskD ∩ {z : Disk | 0 ≤ (1 : ℝ) * (z : ℂ).im}) ∩
          (diskD ∩ {z : Disk | 0 ≤ (-1 : ℝ) * (z : ℂ).im}) := fun w h1 h2 =>
      ⟨⟨h1, by simp [h2]⟩, ⟨h1, by simp [h2]⟩⟩
    obtain ⟨z, hz, hz0⟩ := hc.2.intermediate_value (f := fun w : Disk => (w : ℂ).re)
      (hmem mone (by simp [mone]) (by simp [mone])) (hmem one (by simp [one]) (by simp [one]))
      (Complex.continuous_re.comp continuous_subtype_val).continuousOn
      (show (0 : ℝ) ∈ Icc ((mone : ℂ).re) ((one : ℂ).re) by simp [one, mone])
    have him : (z : ℂ).im = 0 := by
      have h1 := hz.1.2; have h2 := hz.2.2
      simp only [mem_setOf_eq] at h1 h2
      linarith
    have hn := hz.1.1
    have hz0' : (z : ℂ).re = 0 := hz0
    simp only [diskD, mem_setOf_eq] at hn
    rw [norm_eq_one_iff', hz0', him] at hn
    norm_num at hn
  have hDA : ¬ diskD ⊆ diskA := fun hsub => by
    have := hsub (show (⟨-Complex.I, by simp⟩ : Disk) ∈ diskD by simp [diskD])
    norm_num [diskA] at this
  have hDB : ¬ diskD ⊆ diskB := fun hsub => by
    have := hsub (show (⟨Complex.I, by simp⟩ : Disk) ∈ diskD by simp [diskD])
    norm_num [diskB] at this
  rcases h Disk diskA diskB diskD hA hB (by rw [hAB]; exact isUnicoherent_disk) hD
    (by rw [hAB]; exact subset_univ _) hnu with h' | h'
  · exact hDA h'
  · exact hDB h'

end HPC.Plane
