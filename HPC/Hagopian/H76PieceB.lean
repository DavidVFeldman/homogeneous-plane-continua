import HPC.Hagopian.Hagopian76W

/-!
# Batch 179, §3.2 (4.B): crossing components whose closure misses `E` are crossing pieces

`isCrossingPiece_of_crossingComponent`: in the set-up of Hagopian's domain `D = F[D′]`, with
`I₂ ∩ π[M] = ∅` (T7, `hagopian76_T7`), a crossing component `C` of `M ∩ π⁻¹[D]` whose closure misses
`E` gives a crossing piece `toPt C` (commission 178 §1):
* `C` is closed in `M ∩ π⁻¹[D]` (`mem_component_of_mem_closure_in`), and `M` is closed in the plane;
* the closure misses `π⁻¹[I₂]` (it lies in `M`) and `π⁻¹` of the bottom edge (that is `E`,
  `mem_E_of_axis`);
* a point of the closure over the left side segment is a frontier point of `D`, so it lies over
  `F({3/22} × [0, r₂])`; it is not at height `0` (bottom edge) nor at `r₂` (`F(3/22, r₂) ∈ I₂`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section PieceB

variable {M : Set Pt} [CompactSpace M]

theorem isClosed_M_of_compact : IsClosed M :=
  (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace M)).isClosed

theorem closure_toPt (C : Set M) : closure (toPt C) = toPt (closure C) :=
  (isClosed_M_of_compact (M := M)).isClosedEmbedding_subtypeVal.closure_image_eq C

omit [CompactSpace M] in
/-- A point of `M` over the closure of `D` at abscissa `a ∈ {3/22, 19/22}`, off `E` and off `I₂`,
lies over the open side segment `{a} × (0, r)`, where `r` is the height of the end of `I₂` on that
side. Stated for the left side; the right side is symmetric. -/
theorem side_point_open {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D')
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hIs : (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)})
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂))
    (hI2M : Disjoint I₂ (π '' M)) {w : M} (hwD : π (w : Pt) ∈ closure (F '' D')) (hwE : w ∉ E)
    {a s : ℝ} (ha : a = 3 / 22 ∨ a = 19 / 22) (hs : s ∈ Icc 0 c₁) (hws : π (w : Pt) = F (a, s)) :
    (a = 3 / 22 → s ∈ Ioo 0 r₂) ∧ (a = 19 / 22 → s ∈ Ioo 0 s₂) := by
  have hrect : ∀ {x y : ℝ}, x ∈ Icc (3 / 22 : ℝ) (19 / 22) → y ∈ Icc 0 c₁ →
      (x, y) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun hx hy =>
    ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, by linarith [hy.1], by linarith [hy.2]⟩
  have haI : a ∈ Icc (3 / 22 : ℝ) (19 / 22) := by
    rcases ha with rfl | rfl <;> constructor <;> norm_num
  have hwI : π (w : Pt) ∉ I₂ := fun h => disjoint_left.1 hI2M h ⟨w, w.2, rfl⟩
  -- `π w` is not in `F[D′]`: abscissa `a` is not in the open interval
  have hnD : π (w : Pt) ∉ F '' D' := by
    rintro ⟨z, hz, hFz⟩
    have hzR := hR.sub hz
    have := collar_injOn hF (hrect ⟨hzR.1.1.le, hzR.1.2.le⟩ ⟨hzR.2.1.le, hzR.2.2.le⟩)
      (hrect haI hs) (hFz.trans hws)
    have h1 : z.1 = a := congrArg Prod.fst this
    rcases ha with rfl | rfl
    · linarith [hzR.1.1]
    · linarith [hzR.1.2]
  have hfr : π (w : Pt) ∈ frontier (F '' D') := by
    rw [hR.isOpen.frontier_eq]; exact ⟨hwD, hnD⟩
  rw [hFDf] at hfr
  -- the height is positive (else `w ∈ E`)
  have hs0 : 0 < s := by
    rcases lt_or_eq_of_le hs.1 with h | h
    · exact h
    · exfalso; apply hwE
      exact mem_E_of_axis hE hπS hγπ hF (t := a) ⟨by linarith [haI.1], by linarith [haI.2]⟩
        (by rw [hws, ← h])
  have hr₂ : F (3 / 22, r₂) ∈ I₂ := by
    have : ((3 / 22 : ℝ), r₂) ∈ (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
        (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) := by rw [hIs]; simp
    exact this.1.2
  have hs₂ : F (19 / 22, s₂) ∈ I₂ := by
    have : ((19 / 22 : ℝ), s₂) ∈ (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
        (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) := by rw [hIs]; simp
    exact this.1.2
  have hr₂R : r₂ ∈ Icc 0 c₁ := by
    have : ((3 / 22 : ℝ), r₂) ∈ (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
        (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) := by rw [hIs]; simp
    exact this.2.2
  have hs₂R : s₂ ∈ Icc 0 c₁ := by
    have : ((19 / 22 : ℝ), s₂) ∈ (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
        (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) := by rw [hIs]; simp
    exact this.2.2
  rcases hfr with ((hI | ⟨⟨x, y⟩, ⟨hx, hy⟩, hFxy⟩) | ⟨⟨x, y⟩, ⟨hx, hy⟩, hFxy⟩) |
      ⟨⟨x, y⟩, ⟨hx, hy⟩, hFxy⟩
  · exact absurd hI hwI
  · exfalso
    simp only [mem_singleton_iff] at hy
    have := collar_injOn hF (hrect hx (by rw [hy]; exact ⟨le_rfl, by linarith [hs.2, hs0]⟩))
      (hrect haI hs) (hFxy.trans hws)
    have h2 : y = s := congrArg Prod.snd this
    linarith
  · simp only [mem_singleton_iff] at hx
    subst hx
    have hy' : y ∈ Icc 0 c₁ := ⟨hy.1, hy.2.trans hr₂R.2⟩
    have := collar_injOn hF (hrect ⟨le_rfl, by norm_num⟩ hy') (hrect haI hs) (hFxy.trans hws)
    have h1 : (3 / 22 : ℝ) = a := congrArg Prod.fst this
    have h2 : y = s := congrArg Prod.snd this
    subst h2
    refine ⟨fun _ => ⟨hs0, lt_of_le_of_ne hy.2 fun hyr => hwI ?_⟩, fun h => ?_⟩
    · rw [hws, ← h1, hyr]; exact hr₂
    · rw [← h1] at h; norm_num at h
  · simp only [mem_singleton_iff] at hx
    subst hx
    have hy' : y ∈ Icc 0 c₁ := ⟨hy.1, hy.2.trans hs₂R.2⟩
    have := collar_injOn hF (hrect ⟨by norm_num, le_rfl⟩ hy') (hrect haI hs) (hFxy.trans hws)
    have h1 : (19 / 22 : ℝ) = a := congrArg Prod.fst this
    have h2 : y = s := congrArg Prod.snd this
    subst h2
    refine ⟨fun h => ?_, fun _ => ⟨hs0, lt_of_le_of_ne hy.2 fun hyr => hwI ?_⟩⟩
    · rw [← h1] at h; norm_num at h
    · rw [hws, ← h1, hyr]; exact hs₂

/-- **4.B, the general step**: a crossing component `C` of `M ∩ π⁻¹[D]` whose closure misses `E`
is a crossing piece, when `I₂ ∩ π[M] = ∅` (T7). -/
theorem isCrossingPiece_of_crossingComponent {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D')
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hIs : (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)})
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂))
    (hI2M : Disjoint I₂ (π '' M)) {C : Set M}
    (hC : IsCrossingComponent univ π F c₁ D' C) (hCE : Disjoint (closure C) E) :
    IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ (toPt C) := by
  have hclD : ∀ w ∈ closure C, π (w : Pt) ∈ closure (F '' D') := fun w hw =>
    (closure_minimal (s := C) (t := {m : M | π (m : Pt) ∈ closure (F '' D')})
      (fun m hm => subset_closure (hC.subset hm).2)
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))) hw
  have hwE : ∀ w ∈ closure C, w ∉ E := fun w hw hwE => disjoint_left.1 hCE hw hwE
  obtain ⟨⟨z, hz, rfl⟩, ⟨xl, hxl, hxlF⟩, ⟨xr, hxr, hxrF⟩⟩ := hC
  set C := connectedComponentIn (crossSet univ π F D') z with hCdef
  refine ⟨isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact (connectedComponentIn_subset _ _ hm).2
  · rw [closure_toPt]
    rintro _ ⟨⟨m, hmc, rfl⟩, hmO⟩
    exact ⟨m, mem_component_of_mem_closure_in hz ⟨mem_univ _, hmO⟩ hmc, rfl⟩
  · rw [closure_toPt]
    exact (isClosed_closure.isCompact).image continuous_subtype_val
  · rw [closure_toPt, disjoint_left]
    rintro _ ⟨m, hmc, rfl⟩ (hI | ⟨⟨x, y⟩, ⟨hx, hy⟩, hFxy⟩)
    · exact disjoint_left.1 hI2M hI ⟨m, m.2, rfl⟩
    · simp only [mem_singleton_iff] at hy
      subst hy
      exact hwE m hmc (mem_E_of_axis hE hπS hγπ hF (t := x)
        ⟨by linarith [hx.1], by linarith [hx.2]⟩ hFxy.symm)
  · obtain ⟨⟨a, s⟩, ⟨ha, hs⟩, hFas⟩ := hxlF
    simp only [mem_singleton_iff] at ha
    subst ha
    have := (side_point_open hE hπS hγπ hF hc₁ hR hIs hFDf hI2M (hclD xl hxl) (hwE xl hxl)
      (Or.inl rfl) hs hFas.symm).1 rfl
    rw [closure_toPt]
    exact ⟨xl, ⟨xl, hxl, rfl⟩, ⟨(3 / 22, s), ⟨rfl, this⟩, hFas⟩⟩
  · obtain ⟨⟨a, s⟩, ⟨ha, hs⟩, hFas⟩ := hxrF
    simp only [mem_singleton_iff] at ha
    subst ha
    have := (side_point_open hE hπS hγπ hF hc₁ hR hIs hFDf hI2M (hclD xr hxr) (hwE xr hxr)
      (Or.inr rfl) hs hFas.symm).2 rfl
    rw [closure_toPt]
    exact ⟨xr, ⟨xr, hxr, rfl⟩, ⟨(19 / 22, s), ⟨rfl, this⟩, hFas⟩⟩

/-- A `T12Data` package for a smaller constant is one for a larger constant (only the smallness
of `h`, `h₁` mentions it). -/
def T12Data.mono {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {F : ℝ × ℝ → Pt}
    {D' : Set (ℝ × ℝ)} {ε ε' : ℝ} (D : T12Data E k π F D' ε) (h : ε ≤ ε') :
    T12Data E k π F D' ε' :=
  { D with
    h_small := fun v => (D.h_small v).trans_le (by linarith)
    h₁_small := fun v => (D.h₁_small v).trans_le (by linarith) }

omit [CompactSpace M] in
/-- The closure of a subset of `M ∩ π⁻¹[D]` is a proper subset of `M`: the points of `k⁻¹(0)` lie
over `F(0, 0)`, which is not over `Cl D`. -/
theorem closure_ne_univ_of_crossSet {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {C : Set M}
    (hC : C ⊆ crossSet univ π F D') : closure C ≠ univ := by
  intro hCu
  obtain ⟨e, he⟩ := hE.2.1.2.1 0
  have hcl : (e : M) ∈ closure C := by rw [hCu]; exact mem_univ _
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  have hclD : closure (F '' D') ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    closure_minimal hDsub (isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc)
      (rect_sub (by norm_num) (by norm_num) hc₁)).isClosed
  have hmem : π ((e : M) : Pt) ∈ closure (F '' D') :=
    (closure_minimal (s := C) (t := {m : M | π (m : Pt) ∈ closure (F '' D')})
      (fun m hm => subset_closure (hC hm).2)
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))) hcl
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hFxy⟩ := hclD hmem
  rw [pi_E_eq hγπ hF e, he] at hFxy
  have := collar_injOn hF ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, by linarith [hy.1],
    by linarith [hy.2]⟩ ⟨⟨le_refl _, zero_le_one⟩, by norm_num, by norm_num⟩ hFxy
  have h1 : x = ((0 : unitInterval) : ℝ) := congrArg Prod.fst this
  simp at h1
  linarith [hx.1]

variable [ConnectedSpace M]

/-- **4.B** (commission 179 §3.2): in the set-up of `strand_misses_F_of_composant`, with
`I₂ ∩ π[M] = ∅` (T7), there is a `T12Data` package `D` (with `D.K = K₀ ∪ {D.p}`) such that `p` and
`f(p)` lie on crossing pieces `X`, `Y` missing `F = D.G`, equal or disjoint.

*Proof:* the package of `exists_T12Data_strands` for the constant `min ε₃ (θ/2)`, so that `h`, `h₁`
are `θ/4`-small; `p = h x₀`, `f(p) = h₁ x₀` with `k(x₀) = t₀` in the core range; their strands are
crossing components (`strand_crossing`), proper subcontinua through points of `h[R(E)]`,
`h₁[R(E)]`, hence miss `F ⊇ E` (4.A); `isCrossingPiece_of_crossingComponent`; two components are
equal or disjoint. -/
theorem p_on_crossing_piece (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D')
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hIs : (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)})
    (hIR : I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁)) (hDo : IsOpen D')
    (hDf : frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∪
        Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
        ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂))
    (hI2M : Disjoint I₂ (π '' M))
    {t₀ w₂ : ℝ} (ht₀1 : 3 / 22 + 2 / (n : ℝ) ≤ t₀) (ht₀2 : t₀ ≤ 19 / 22 - 2 / (n : ℝ))
    (hw₂ : w₂ ∈ Ioc 0 c₁) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (K₀ : Set M) {ε₃ : ℝ} (hε₃ : 0 < ε₃) :
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧
      ∃ X Y : Set Pt, IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ X ∧
        IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ Y ∧
        (D.p : Pt) ∈ X ∧ ((D.f D.p : M) : Pt) ∈ Y ∧ (X = Y ∨ Disjoint X Y) ∧
        Disjoint X (toPt D.G) ∧ Disjoint Y (toPt D.G) := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hθ := hS.θ_pos
  have hε : 0 < min ε₃ (θ / 2) := lt_min hε₃ (by linarith)
  obtain ⟨D0, hDK, x, hkx, hpx, hmiss⟩ := exists_T12Data_strands hX hi hE hπ hπS hγπ hF hS hn
    hc₁ hR hbelow hI hIs hIR hDo hDf hFDf ht₀1 ht₀2 hw₂ hFw hseg K₀ hε
  have hsmall : ∀ v, dist (D0.h v) v < θ / 4 := fun v =>
    (D0.h_small v).trans_le (by linarith [min_le_right ε₃ (θ / 2)])
  have hsmall₁ : ∀ v, dist (D0.h₁ v) v < θ / 4 := fun v =>
    (D0.h₁_small v).trans_le (by linarith [min_le_right ε₃ (θ / 2)])
  set D : T12Data E k π F D' ε₃ := D0.mono (min_le_left _ _) with hDdef
  have hq : (D0.h.symm.trans D0.h₁) D0.p = D0.h₁ x := by rw [hpx]; simp
  have hsep := D0.sep
  rw [hq] at hsep
  have hyp : D0.h x ∈ crossSet univ π F D' := ⟨mem_univ _, by rw [← hpx]; exact hsep.1.1⟩
  have hyq : D0.h₁ x ∈ crossSet univ π F D' := ⟨mem_univ _, hsep.2.1.1⟩
  have hk1 : 3 / 22 + 2 / (n : ℝ) ≤ (k x : ℝ) := by rw [hkx]; exact ht₀1
  have hk2 : (k x : ℝ) ≤ 19 / 22 - 2 / (n : ℝ) := by rw [hkx]; exact ht₀2
  have hCp := (strand_crossing hX hi hE hπ.continuous hπS hγπ hF hS hn hc₁ hR D0.h hsmall x hyp
    hk1 hk2).1
  have hCq := (strand_crossing hX hi hE hπ.continuous hπS hγπ hF hS hn hc₁ hR D0.h₁ hsmall₁ x
    hyq hk1 hk2).1
  set Cp := connectedComponentIn (crossSet univ π F D') (D0.h x) with hCpdef
  set Cq := connectedComponentIn (crossSet univ π F D') (D0.h₁ x) with hCqdef
  have hxR : (x : M) ∈ Rset k := subset_Rset hE x.2
  have hmissC : ∀ (C : Set M) (z : M), IsCrossingComponent univ π F c₁ D' C → z ∈ C →
      z ∈ D0.h '' Rset k ∪ D0.h₁ '' Rset k → Disjoint (closure C) D0.G := fun C z hC hzC hz =>
    hmiss z hz (closure C) ⟨isClosed_closure.isCompact, hC.isConnected.closure⟩
      (closure_ne_univ_of_crossSet hE hπ.continuous hγπ hF hc1 hR hC.subset)
      (subset_closure hzC)
  have hdp := hmissC Cp _ hCp (mem_connectedComponentIn hyp) (Or.inl ⟨x, hxR, rfl⟩)
  have hdq := hmissC Cq _ hCq (mem_connectedComponentIn hyq) (Or.inr ⟨x, hxR, rfl⟩)
  have hEp : Disjoint (closure Cp) E := hdp.mono_right D0.hEG
  have hEq : Disjoint (closure Cq) E := hdq.mono_right D0.hEG
  have htoPt : ∀ C : Set M, Disjoint (closure C) D0.G → Disjoint (toPt C) (toPt D0.G) := by
    intro C hC
    rw [disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ ⟨m', hm', hmm'⟩
    have : m' = m := Subtype.ext hmm'
    subst this
    exact disjoint_left.1 hC (subset_closure hm) hm'
  refine ⟨D, hDK, toPt Cp, toPt Cq,
    isCrossingPiece_of_crossingComponent hE hπ.continuous hπS hγπ hF hc1 hR hIs hFDf hI2M hCp hEp,
    isCrossingPiece_of_crossingComponent hE hπ.continuous hπS hγπ hF hc1 hR hIs hFDf hI2M hCq hEq,
    ?_, ?_, ?_, htoPt Cp hdp, htoPt Cq hdq⟩
  · show ((D0.p : M) : Pt) ∈ toPt Cp
    rw [hpx]; exact ⟨_, mem_connectedComponentIn hyp, rfl⟩
  · show (((D0.h.symm.trans D0.h₁) D0.p : M) : Pt) ∈ toPt Cq
    rw [hq]; exact ⟨_, mem_connectedComponentIn hyq, rfl⟩
  · by_cases hmem : D0.h₁ x ∈ Cp
    · left
      rw [hCpdef, connectedComponentIn_eq hmem]
    · right
      rw [disjoint_left]
      rintro _ ⟨m, hm, rfl⟩ ⟨m', hm', hmm'⟩
      have : m' = m := Subtype.ext hmm'
      subst this
      apply hmem
      rw [hCpdef, connectedComponentIn_eq hm, ← connectedComponentIn_eq hm']
      exact mem_connectedComponentIn hyq

end PieceB

end HPC.Hagopian
