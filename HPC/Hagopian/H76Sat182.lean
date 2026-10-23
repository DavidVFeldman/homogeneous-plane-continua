import HPC.Hagopian.H76Orient

/-!
# Batch 182, §1.3, §3.1 and §4.1: the weaker split at `i = 2`; `K⁻` is a continuum; `L ∩ F = ∅`

Commission 182.

* §1.3: `Thm1Setup.LayerMeetsRegion` (the weaker split: a layer meets `π⁻¹` of the left region
  `F[[0, 3/22] × [0, c₁]]` or of the right region `F[[19/22, 1] × [0, c₁]]`), and
  `Thm1Setup.IsBlocks.layer_x2_meets_right`: `d⁻¹(x₂) = k⁻¹(1)` meets the right region.
* §3.1, step 1 (commission 178 §3b.1): `Thm1Setup.kminus_isContinuum`,
  `Thm1Setup.kplus_isContinuum` (`K∓ = F ∩ h[k⁻¹[[0, k(e)]]]`, `F ∩ h[k⁻¹[[k(e), 1]]]` are continua:
  hereditary unicoherence), and `Thm1Setup.half_bump` (boundary bumping in a half: if the half is
  not inside `π⁻¹[D]`, the component through `y` of its part in `π⁻¹[D]` has a point of the half
  off `π⁻¹[D]` in its closure); §3.1, step 2: `Thm1Setup.half_bump_side` (for `K ⊆ F`, that point lies
  over a closed side segment: not over `I₂`, and not over the bottom edge by `closure_G_diff_E`), with
  `Thm1Setup.mem_toPt_E_of_pi_eq`.
* §4.1, step 4: `Thm1Setup.continuum_misses_G_of_h_Rset` (a proper subcontinuum of `M` through a
  point of `h[R(E)]` misses `F`; the composant choice `hcomp`); `minimalAdmissible_ne_univ`,
  `Thm1Setup.admissible_misses_G_of_h_Rset`, `Thm1Setup.extension_misses_G` (an extension through a
  good point misses `F`); `Thm1Setup.closure_comp_continuum`, `Thm1Setup.comp_disjoint_G`,
  `Thm1Setup.comp_disjoint_G_of_ess`, `Thm1Setup.comp_f_disjoint_G` (the components through
  `h[R(E)]` and `h₁[R(E)]` miss `F`: the field `miss` of `GoodPoint` is automatic).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section B182Sat

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1.3: the weaker split -/

/-- **The weaker split** (commission 182 §1.3): the layer `d⁻¹(u)` meets `π⁻¹` of the region
`F[[lo, hi] × [0, c₁]]` (left region: `[0, 3/22]`; right region: `[19/22, 1]`). -/
def Thm1Setup.LayerMeetsRegion (S : Thm1Setup M) (u : unitInterval) (lo hi : ℝ) : Prop :=
  (toPt (layer S.D.d u) ∩ S.π ⁻¹' (S.F '' (Icc lo hi ×ˢ Icc 0 S.c₁))).Nonempty

/-- **§1.3, the weaker split at `i = 2`**: `d⁻¹(x₂) = k⁻¹(1)` lies over `F(1, 0)`, in the right
region. -/
theorem Thm1Setup.IsBlocks.layer_x2_meets_right (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) : S.LayerMeetsRegion (x 2) (19 / 22) 1 := by
  obtain ⟨e, he⟩ := S.hE.2.1.2.1 1
  have hz : ((e : M) : Pt) ∈ toPt (layer S.D.d (x 2)) := by
    rw [Thm1Setup.IsBlocks.layer_x2_eq S hx]
    exact ⟨e, ⟨e, he, rfl⟩, rfl⟩
  refine ⟨_, hz, ((1 : ℝ), (0 : ℝ)), ⟨⟨by norm_num, le_rfl⟩, le_rfl, S.c₁_pos.le⟩, ?_⟩
  rw [Thm1Setup.IsBlocks.layer_x2_eq S hx] at hz
  have h1 := S.hF.2.1 1
  rw [S.hγπ 1 _ hz]
  exact h1

/-! ## §3.1: the halves `K⁻`, `K⁺` -/

/-- **§3.1, step 1** (commission 178 §3b.1, commission 182 §0): `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` is a
continuum when it contains `h(e)` (the intersection of two continua in the hereditarily unicoherent
`M`). -/
theorem Thm1Setup.kminus_isContinuum (S : Thm1Setup M) (h : M ≃ₜ M) (e : S.E)
    (he : h e ∈ S.D.G) :
    Fold.Q78.IsContinuum (S.D.G ∩ h '' layerSet S.k (Icc 0 (S.k e))) := by
  have hHU := hereditarilyUnicoherent_of_homogeneous_indecomposable S.hX S.hi
  have himg : ∀ {P : Set M}, Fold.Q78.IsContinuum P → Fold.Q78.IsContinuum (h '' P) :=
    fun hP => ⟨hP.1.image h.continuous, hP.2.image _ h.continuous.continuousOn⟩
  exact isContinuum_inter_of_HU hHU (isContinuum_of_minimalAdmissible S.D.hG)
    (himg (isContinuum_img S.hE.isCompact S.hE.2.1 isClosed_Icc isPreconnected_Icc
      ⟨0, le_rfl, unitInterval.nonneg'⟩))
    ⟨h e, he, e, ⟨e, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, rfl⟩

/-- **§3.1, step 1, the other half**: `K⁺ = F ∩ h[k⁻¹[[k(e), 1]]]` is a continuum. -/
theorem Thm1Setup.kplus_isContinuum (S : Thm1Setup M) (h : M ≃ₜ M) (e : S.E)
    (he : h e ∈ S.D.G) :
    Fold.Q78.IsContinuum (S.D.G ∩ h '' layerSet S.k (Icc (S.k e) 1)) := by
  have hHU := hereditarilyUnicoherent_of_homogeneous_indecomposable S.hX S.hi
  have himg : ∀ {P : Set M}, Fold.Q78.IsContinuum P → Fold.Q78.IsContinuum (h '' P) :=
    fun hP => ⟨hP.1.image h.continuous, hP.2.image _ h.continuous.continuousOn⟩
  exact isContinuum_inter_of_HU hHU (isContinuum_of_minimalAdmissible S.D.hG)
    (himg (isContinuum_img S.hE.isCompact S.hE.2.1 isClosed_Icc isPreconnected_Icc
      ⟨1, unitInterval.le_one', le_rfl⟩))
    ⟨h e, he, e, ⟨e, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, rfl⟩

/-- **§3.1, step 1, boundary bumping in a half** (commission 182 §3.1): let `K` be a continuum in
`M` (for instance `K⁻` or `K⁺`) through `y ∈ π⁻¹[D]`. If `K ⊄ π⁻¹[D]`, the component of
`K ∩ π⁻¹[D]` through `y` has in its closure a point of `K` off `π⁻¹[D]`
(`exists_mem_closure_component_notMem`). -/
theorem Thm1Setup.half_bump (S : Thm1Setup M) {K : Set M} (hK : Fold.Q78.IsContinuum K) {y : M}
    (hyK : y ∈ K) (hyO : (y : Pt) ∈ S.π ⁻¹' (S.F '' S.D'))
    (hKO : ¬ K ⊆ Subtype.val ⁻¹' (S.π ⁻¹' (S.F '' S.D'))) :
    ∃ q ∈ K, (q : Pt) ∉ S.π ⁻¹' (S.F '' S.D') ∧
      q ∈ closure (connectedComponentIn (K ∩ Subtype.val ⁻¹' (S.π ⁻¹' (S.F '' S.D'))) y) :=
  exists_mem_closure_component_notMem hK.1 hK.2.isPreconnected
    ((S.hR.isOpen.preimage S.hπ.continuous).preimage continuous_subtype_val) hyK hyO hKO

/-- A point over `γ(t)` is a point of `E` (the relation `S` identifies only points of `E`). -/
theorem Thm1Setup.mem_toPt_E_of_pi_eq (S : Thm1Setup M) {q : Pt} (t : unitInterval)
    (hq : S.π q = S.γ t) : q ∈ toPt S.E := by
  by_contra hqE
  obtain ⟨e, he⟩ := S.hE.2.1.2.1 t
  have h1 : S.π ((e : M) : Pt) = S.γ t := S.hγπ t _ ⟨e, ⟨e, he, rfl⟩, rfl⟩
  have hrel : layerKey S.k q = layerKey S.k ((e : M) : Pt) := (S.hπS q _).1 (hq.trans h1.symm)
  rw [layerKey_of_notMem S.k hqE, layerKey_of_mem] at hrel
  exact Sum.inr_ne_inl hrel

/-- **§3.1, step 2, the frontier point lies over a side segment** (commission 178 §3b, step 2, with
`closure_G_diff_E`): for a continuum `K ⊆ F` through `y ∈ π⁻¹[D]` not inside `π⁻¹[D]` (for
instance `K⁻` or `K⁺`), the closure of the component of `K ∩ π⁻¹[D]` through `y` has a point of `K`
over one of the closed side segments `F[{3/22} × [0, r₂]]`, `F[{19/22} × [0, s₂]]`.

*Proof:* `half_bump` gives `q` off `π⁻¹[D]` in the closure, so `π(q) ∈ Fr D`. Not over `I₂`
(`hI2M`). Not over the bottom edge: then `q ∈ E` (`mem_toPt_E_of_pi_eq`) and `q` is in the closure of
`F − E` (the component lies in `F ∩ π⁻¹[D]`, which misses `E`), so `q ∈ k⁻¹(1)`
(`closure_G_diff_E`), over `F(1, 0)`, which is not on the bottom edge `F[[3/22, 19/22] × {0}]`. -/
theorem Thm1Setup.half_bump_side (S : Thm1Setup M) {K : Set M} (hK : Fold.Q78.IsContinuum K)
    (hKG : K ⊆ S.D.G) {y : M} (hyK : y ∈ K) (hyO : (y : Pt) ∈ S.π ⁻¹' (S.F '' S.D'))
    (hKO : ¬ K ⊆ Subtype.val ⁻¹' (S.π ⁻¹' (S.F '' S.D'))) :
    ∃ q ∈ K,
      q ∈ closure (connectedComponentIn (K ∩ Subtype.val ⁻¹' (S.π ⁻¹' (S.F '' S.D'))) y) ∧
      S.π (q : Pt) ∈ S.F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 S.r₂) ∪
        S.F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 S.s₂) := by
  obtain ⟨q, hqK, hqO, hqcl⟩ := S.half_bump hK hyK hyO hKO
  refine ⟨q, hqK, hqcl, ?_⟩
  set Cm := connectedComponentIn (K ∩ Subtype.val ⁻¹' (S.π ⁻¹' (S.F '' S.D'))) y with hCm
  have hCO : Cm ⊆ Subtype.val ⁻¹' (S.π ⁻¹' (S.F '' S.D')) :=
    (connectedComponentIn_subset _ _).trans inter_subset_right
  have hqPt : (q : Pt) ∈ closure (S.π ⁻¹' (S.F '' S.D')) :=
    map_mem_closure continuous_subtype_val hqcl fun c hc => hCO hc
  have hπq : S.π q ∈ closure (S.F '' S.D') :=
    map_mem_closure S.hπ.continuous hqPt fun x hx => hx
  have hfr : S.π q ∈ frontier (S.F '' S.D') := by
    refine ⟨hπq, ?_⟩
    rw [S.hR.isOpen.interior_eq]
    exact hqO
  rw [S.hFDf] at hfr
  rcases hfr with ((hI | ⟨⟨t, s⟩, ⟨ht, hs⟩, hFt⟩) | hl) | hr
  · exact absurd ⟨(q : Pt), q.2, rfl⟩ (disjoint_left.1 S.hI2M hI)
  · exfalso
    rw [mem_singleton_iff] at hs
    subst hs
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hF0 : S.F (t, 0) = S.γ ⟨t, ht01⟩ := S.hF.2.1 ⟨t, ht01⟩
    have hqE : (q : Pt) ∈ toPt S.E := S.mem_toPt_E_of_pi_eq ⟨t, ht01⟩ (hFt.symm.trans hF0)
    have hqGE : (q : Pt) ∈ closure (toPt S.D.G \ toPt S.E) := by
      refine map_mem_closure continuous_subtype_val hqcl fun c hc => ⟨⟨c, hKG ?_, rfl⟩, ?_⟩
      · exact ((connectedComponentIn_subset _ _) hc).1
      · exact disjoint_left.1 S.disjoint_O_E (hCO hc)
    have hq1 := closure_G_diff_E S ⟨hqGE, hqE⟩
    have hπ1 : S.π q = S.γ 1 := S.hγπ 1 _ hq1
    have hF1 : S.F (((1 : unitInterval) : ℝ), 0) = S.γ 1 := S.hF.2.1 1
    have hR1 : ((t, (0 : ℝ)) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨ht01, by norm_num, by norm_num⟩
    have hR2 : ((((1 : unitInterval) : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
    have he := collar_injOn S.hF hR1 hR2 (by rw [hFt, hπ1, hF1])
    have : t = 1 := congrArg Prod.fst he
    linarith [ht.2]
  · exact Or.inl hl
  · exact Or.inr hr

/-! ## §4.1, step 4: `L ∩ F = ∅` -/

/-- **§4.1, step 4** (p. 348: `L ∩ F = ∅`): a proper subcontinuum of `M` through a point of
`h[R(E)]` misses `F` (`hcomp`: `h(x₀)` is not in the composant of `x₀`, while `F ⊆ R(E)` lies in
it; `strand_misses_of_composant`). -/
theorem Thm1Setup.continuum_misses_G_of_h_Rset (S : Thm1Setup M) {L : Set M}
    (hL : Fold.Q78.IsContinuum L) (hLu : L ≠ univ) {z : M} (hz : z ∈ S.D.h '' Rset S.k)
    (hzL : z ∈ L) : Disjoint L S.D.G := by
  obtain ⟨x₀, -, -, hpC, -⟩ := S.hcomp
  have hGext : IsExtensionAway S.E (layer S.k 0) S.D.G := ⟨S.D.hEG, S.D.d, S.D.hG, S.D.hX0⟩
  exact strand_misses_of_composant S.hX S.hi S.hE x₀.2 S.D.h hpC hGext hz hL hLu hzL

/-- The closure of a component of `M ∩ π⁻¹[D]`, as a subset of `M`, is a proper subcontinuum of `M`
(it lies over `F[[3/22, 19/22] × [0, c₁]]`, which misses `γ(0) = F(0, 0)`, the image of
`k⁻¹(0)`). -/
theorem Thm1Setup.closure_comp_continuum (S : Thm1Setup M) {z : M}
    (hz : (z : Pt) ∈ S.π ⁻¹' (S.F '' S.D')) :
    Fold.Q78.IsContinuum (Subtype.val ⁻¹' closure (S.comp z) : Set M) ∧
      (Subtype.val ⁻¹' closure (S.comp z) : Set M) ≠ univ := by
  set C := S.comp z with hC
  have hzC : (z : Pt) ∈ C := mem_connectedComponentIn ⟨z.2, hz⟩
  have hCM : closure C ⊆ M := closure_minimal
    ((connectedComponentIn_subset _ _).trans inter_subset_left) isClosed_M_of_compact
  refine ⟨⟨(isClosed_closure.preimage continuous_subtype_val).isCompact,
    ⟨z, subset_closure hzC⟩, ?_⟩, ?_⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.1
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hCM]
    exact isPreconnected_connectedComponentIn.closure
  · intro hu
    obtain ⟨e0, he0⟩ := S.hE.2.1.2.1 0
    have hmem : ((e0 : M) : M) ∈ (Subtype.val ⁻¹' closure C : Set M) := by rw [hu]; trivial
    set R : Set (ℝ × ℝ) := Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 S.c₁ with hRdef
    have hRr : R ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun q hq =>
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, by linarith [hq.2.1],
        hq.2.2.trans S.c₁_le_one⟩
    have hRc : IsClosed (S.π ⁻¹' (S.F '' R)) :=
      (isCompact_collar_image S.hF (isCompact_Icc.prod isCompact_Icc) hRr).isClosed.preimage
        S.hπ.continuous
    have hCR : C ⊆ S.π ⁻¹' (S.F '' R) := by
      intro p hp
      obtain ⟨q, hq, hqp⟩ := ((connectedComponentIn_subset _ _) hp).2
      have h := S.hR.sub hq
      exact ⟨q, ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.1.le, h.2.2.le⟩, hqp⟩
    obtain ⟨q, hqR, hq⟩ := closure_minimal hCR hRc hmem
    have h0 : S.π ((e0 : M) : Pt) = S.γ 0 := S.hγπ 0 _ ⟨e0, ⟨e0, he0, rfl⟩, rfl⟩
    have hF0 : S.F (((0 : unitInterval) : ℝ), 0) = S.γ 0 := S.hF.2.1 0
    have h00 : ((((0 : unitInterval) : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
    have hqe := collar_injOn S.hF (hRr hqR) h00 (by rw [hq, h0, hF0])
    have : q.1 = 0 := by rw [hqe]; rfl
    have := hqR.1.1
    linarith

/-- **The components through `h[R(E)]` and `h₁[R(E)]` miss `F`** (§4.1 step 4 in the form used by
`GoodPoint.miss` and by `StepFrame`): if `z ∈ h[R(E)]` or `z ∈ h₁[R(E)]`, the component of `z` in
`M ∩ π⁻¹[D]` misses `F` (its closure is a proper subcontinuum through `z`; the composant choice). -/
theorem Thm1Setup.comp_disjoint_G (S : Thm1Setup M) {z : M}
    (hz : z ∈ S.D.h '' Rset S.k ∨ z ∈ S.D.h₁ '' Rset S.k) :
    Disjoint (S.comp z) (toPt S.D.G) := by
  rw [disjoint_left]
  intro p hpC ⟨g, hgG, hgp⟩
  have hzO : (z : Pt) ∈ M ∩ S.π ⁻¹' (S.F '' S.D') :=
    connectedComponentIn_nonempty_iff.1 ⟨p, hpC⟩
  obtain ⟨hLc, hLu⟩ := S.closure_comp_continuum hzO.2
  have hzL : z ∈ (Subtype.val ⁻¹' closure (S.comp z) : Set M) :=
    subset_closure (mem_connectedComponentIn hzO)
  have hgL : g ∈ (Subtype.val ⁻¹' closure (S.comp z) : Set M) := by
    show (g : Pt) ∈ closure (S.comp z)
    rw [hgp]; exact subset_closure hpC
  have hdisj : Disjoint (Subtype.val ⁻¹' closure (S.comp z) : Set M) S.D.G := by
    rcases hz with hz | hz
    · exact S.continuum_misses_G_of_h_Rset hLc hLu hz hzL
    · obtain ⟨x₀, -, -, -, hqC⟩ := S.hcomp
      have hGext : IsExtensionAway S.E (layer S.k 0) S.D.G := ⟨S.D.hEG, S.D.d, S.D.hG, S.D.hX0⟩
      exact strand_misses_of_composant S.hX S.hi S.hE x₀.2 S.D.h₁ hqC hGext hz hLc hLu hzL
  exact disjoint_left.1 hdisj hgL hgG

/-- **`GoodPoint.miss` is automatic** for a point whose component has closure essential to
`h[R(E)]` (as for every point of Property 4): the component misses `F`. -/
theorem Thm1Setup.comp_disjoint_G_of_ess (S : Thm1Setup M) {y : M}
    (hess : IsEssential S.k (S.D.h ⁻¹' (Subtype.val ⁻¹' closure (S.comp y)))) :
    Disjoint (S.comp y) (toPt S.D.G) := by
  by_cases hyO : (y : Pt) ∈ S.π ⁻¹' (S.F '' S.D')
  · refine S.comp_disjoint_G (Or.inl ⟨S.D.h.symm y, hess.1 ?_, S.D.h.apply_symm_apply y⟩)
    show ((S.D.h (S.D.h.symm y) : M) : Pt) ∈ closure (S.comp y)
    rw [S.D.h.apply_symm_apply]
    exact subset_closure (mem_connectedComponentIn ⟨y.2, hyO⟩)
  · have : S.comp y = ∅ := connectedComponentIn_eq_empty fun h => hyO h.2
    rw [this]; exact empty_disjoint _

/-- **The component of `f(y)` misses `F`** for `h⁻¹(y) ∈ R(E)` (`f(y) ∈ h₁[R(E)]`). -/
theorem Thm1Setup.comp_f_disjoint_G (S : Thm1Setup M) {y : M} (hyR : S.D.h.symm y ∈ Rset S.k) :
    Disjoint (S.comp (S.D.f y)) (toPt S.D.G) :=
  S.comp_disjoint_G (Or.inr ⟨S.D.h.symm y, hyR, rfl⟩)

omit [CompactSpace M] [ConnectedSpace M] in
/-- A continuum with an admissible decomposition is not all of an indecomposable `M` (it is the union
of the two proper subcontinua `d⁻¹[[0, 1/2]]` and `d⁻¹[[1/2, 1]]`). -/
theorem minimalAdmissible_ne_univ (hi : ¬ IsDecomposableSpace M) {L : Set M}
    {d : L → unitInterval} (hL : IsMinimalAdmissible L d) : L ≠ univ := by
  intro hLu
  set c : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩ with hc
  have hc0 : (0 : unitInterval) < c := by show (0 : ℝ) < 1 / 2; norm_num
  have hc1 : c < 1 := by show (1 / 2 : ℝ) < 1; norm_num
  have hsurj := hL.2.1.2.1
  have hne : ∀ a b : unitInterval, ∀ t : unitInterval, t ∉ Icc a b →
      layerSet d (Icc a b) ≠ univ := by
    intro a b t ht hu
    obtain ⟨g, hg⟩ := hsurj t
    have hmem : (g : M) ∈ layerSet d (Icc a b) := by rw [hu]; trivial
    obtain ⟨g', hg', hgg⟩ := hmem
    have h2 : d g ∈ Icc a b := Subtype.ext hgg ▸ hg'
    rw [hg] at h2
    exact ht h2
  refine hi ⟨layerSet d (Icc 0 c), layerSet d (Icc c 1),
    isContinuum_img hL.isCompact hL.2.1 isClosed_Icc isPreconnected_Icc
      ⟨0, le_rfl, unitInterval.nonneg'⟩,
    isContinuum_img hL.isCompact hL.2.1 isClosed_Icc isPreconnected_Icc
      ⟨1, unitInterval.le_one', le_rfl⟩,
    hne 0 c 1 fun h => absurd h.2 (not_le.2 hc1),
    hne c 1 0 fun h => absurd h.1 (not_le.2 hc0), ?_⟩
  apply eq_univ_of_forall
  intro z
  have hz : z ∈ L := by rw [hLu]; trivial
  rcases le_total (d ⟨z, hz⟩) c with h | h
  · exact Or.inl ⟨⟨z, hz⟩, ⟨unitInterval.nonneg', h⟩, rfl⟩
  · exact Or.inr ⟨⟨z, hz⟩, ⟨h, unitInterval.le_one'⟩, rfl⟩

/-- **§4.1, step 4, for extensions** (p. 348: `L ∩ F = ∅`): a continuum `L` with an admissible
decomposition (an extension) through a point of `h[R(E)]` misses `F`. -/
theorem Thm1Setup.admissible_misses_G_of_h_Rset (S : Thm1Setup M) {L : Set M}
    {d : L → unitInterval} (hL : IsMinimalAdmissible L d) {z : M}
    (hz : z ∈ S.D.h '' Rset S.k) (hzL : z ∈ L) : Disjoint L S.D.G :=
  S.continuum_misses_G_of_h_Rset (isContinuum_of_minimalAdmissible hL)
    (minimalAdmissible_ne_univ S.hi hL) hz hzL

/-- **§4.1, step 4, as printed**: an extension `L` of `Cl Cᵢ` (it contains `yᵢ`, whose component has
closure essential to `h[R(E)]`) misses `F`. The commission's check "`L` passes through a point of
`h[R(E)]` for the package's `h`" holds at `yᵢ` itself (`GoodPoint.rset`). -/
theorem Thm1Setup.extension_misses_G (S : Thm1Setup M) {L : Set M} {d : L → unitInterval}
    (hL : IsMinimalAdmissible L d) {y : M} (hy : S.GoodPoint y) (hyL : y ∈ L) :
    Disjoint L S.D.G :=
  S.admissible_misses_G_of_h_Rset hL ⟨S.D.h.symm y, hy.rset, S.D.h.apply_symm_apply y⟩ hyL

end B182Sat

end HPC.Hagopian
