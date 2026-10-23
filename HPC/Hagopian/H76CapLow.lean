import HPC.Hagopian.H76Cap

/-!
# Batch 181, §3.1 and §3.2: `f(y) ∈ π⁻¹[D]`, and the cap lemma in the low frame

Commission 181 §3.1 (consequence of `hε₃O`) and §3.2.

* `Thm1Setup.K_subset_mid`: `K ⊆ Mid` (the points of `K₀` are over `1/2`; `p = h(x₀)` with
  `k(x₀) = 1/2` is over `[1/2 − 2/n, 1/2 + 2/n]` by S0).
* `f_mem_O_of_mem_K` (§3.1, p. 348 "Note that `f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`"): for `y ∈ K`
  with `h⁻¹(y) ∈ R(E)`, `f(y) ∈ π⁻¹[D]`.
* `above_closure_misses_bottom` (§3.2.1): for a set `W` with compact closure missing `π⁻¹` of the
  bottom edge, the closure of the region `B(W)` above `W` in the low frame misses `π⁻¹` of the open
  bottom edge.
* `cross_strand_near` (§3.2.2, the cap lemma): `a ∈ Mid` below a crossing piece `W`, `b` above it,
  `ρ(a, b) < ε₃` imply `ρ(a, Cl W) < ε₃`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section CapLow

variable {M : Set Pt}

/-- **§3.2.1, `above_closure_misses_bottom`.** In the low frame over `t₀ ∈ (a, b)`, let `W` have
compact closure missing `π⁻¹` of the bottom edge. Then the closure of `B(W)` misses `π⁻¹` of the
open bottom edge `F[(a, b) × {0}]`.

*Proof* (commission 181 §3.2.1): `D′` contains a low rectangle `(a, b) × (0, c₀)`; `π[Cl W]` stays
above some height `c_W > 0`; the points of `π⁻¹[D]` over `(a, b) × (0, min(c₀, c_W))` form a
connected set missing `Cl W` and containing the foot of `σ`, so they lie in `A(W)`; a point over
the open bottom edge has a neighbourhood whose part in `π⁻¹[D]` lies there, and `A(W) ∩ B(W) = ∅`
(`B(W)` is not needed to be a piece: `A(W)` is open). -/
theorem above_closure_misses_bottom {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hb : b < 1) (hc1 : c ≤ 1) {D' : Set (ℝ × ℝ)}
    (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hlow : ∃ c₀ > 0, Ioo a b ×ˢ Ioo 0 c₀ ⊆ D') {t₀ w₂ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 1)
    (hOo : IsOpen (π ⁻¹' (F '' D'))) (hOc : IsPreconnected (π ⁻¹' (F '' D')))
    (hsub : ({t₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D') (hinj : InjOn π (π ⁻¹' (F '' D')))
    (hsurj : Function.Surjective π)
    (hseg : ∀ J : Set ℝ, IsPreconnected J →
      IsPreconnected (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ (J ∩ Ioo 0 w₂)))))
    {W : Set Pt} (hWc : IsCompact (closure W))
    (hWb : Disjoint (closure W) (π ⁻¹' (F '' (Icc a b ×ˢ {0}))))
    (hWs : Disjoint ((lowFrame π F D' t₀ w₂ hOo hOc hsub hinj hsurj hseg).below W)
      ((lowFrame π F D' t₀ w₂ hOo hOc hsub hinj hsurj hseg).above W)) :
    Disjoint (closure ((lowFrame π F D' t₀ w₂ hOo hOc hsub hinj hsurj hseg).above W))
      (π ⁻¹' (F '' (Ioo a b ×ˢ {0}))) := by
  set V := lowFrame π F D' t₀ w₂ hOo hOc hsub hinj hsurj hseg with hV
  obtain ⟨c₀, hc₀, hc₀D⟩ := hlow
  set Z := closure W with hZ
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hF.1.continuous
  have hR1c : IsCompact R1 := isCompact_Icc.prod isCompact_Icc
  have hπc := hπ.continuous
  -- the height of `Z` above the bottom edge
  set Q : Set (ℝ × ℝ) := (Icc a b ×ˢ Icc 0 1) ∩ F ⁻¹' (π '' Z) with hQ
  have hQR : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ R1 := fun z hz =>
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1], hz.2.2⟩
  have hQc : IsCompact Q := by
    have hcl : IsClosed (Icc a b ×ˢ Icc (0 : ℝ) 1) := isClosed_Icc.prod isClosed_Icc
    have h1 : IsClosed (R1 ∩ F ⁻¹' (π '' Z)) :=
      hFc.preimage_isClosed_of_isClosed hR1c.isClosed (hWc.image hπc).isClosed
    have : Q = (Icc a b ×ˢ Icc (0 : ℝ) 1) ∩ (R1 ∩ F ⁻¹' (π '' Z)) := by
      ext z; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hQR h1, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    rw [this]
    exact (hR1c.of_isClosed_subset h1 inter_subset_left).inter_left hcl
  have hQ0 : ∀ z ∈ Q, 0 < z.2 := by
    rintro z ⟨⟨hz1, hz2, -⟩, w, hwZ, hw⟩
    rcases hz2.lt_or_eq with h | h
    · exact h
    · exfalso
      refine disjoint_left.1 hWb hwZ ⟨z, ⟨hz1, ?_⟩, hw.symm⟩
      exact mem_singleton_iff.2 h.symm
  obtain ⟨cK, hcK, hcK1, hcKQ⟩ := exists_height_below hQc hQ0
  set c' := min c₀ cK with hc'
  have hc'0 : 0 < c' := lt_min hc₀ hcK
  have hc'c₀ : c' ≤ c₀ := min_le_left _ _
  have hc'K : c' ≤ cK := min_le_right _ _
  set S' : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo 0 c' with hS'
  have hS'D : S' ⊆ D' := fun z hz => hc₀D ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hc'c₀⟩
  have hS'R : S' ⊆ R1 := fun z hz =>
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1],
      by linarith [hz.2.2, hcK1]⟩
  set G := F '' S' with hG
  have hDR1 : D' ⊆ R1 := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hz
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hGo : IsOpen G := isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo)
    (fun z hz => ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1],
      by linarith [hz.2.2, hcK1]⟩)
  have hGc : IsPreconnected G :=
    (((convex_Ioo a b).prod (convex_Ioo 0 c')).isPreconnected).image F (hFc.mono hS'R)
  have hGE : Disjoint (π ⁻¹' G) (toPt E) := by
    rw [disjoint_left]
    rintro x ⟨z, hz, hzx⟩ hxE
    obtain ⟨t, ht⟩ := pi_mem_range_of_mem hγπ hxE
    have h0 : ((t : ℝ), (0 : ℝ)) ∈ R1 := ⟨⟨t.2.1, t.2.2⟩, by norm_num, by norm_num⟩
    have : z = ((t : ℝ), (0 : ℝ)) := collar_injOn hF (hS'R hz) h0
      (by rw [hzx, ← ht, hF.2.1 t])
    have := hz.2.1
    rw [‹z = _›] at this
    exact lt_irrefl _ this
  have hGZ : Disjoint (π ⁻¹' G) Z := by
    rw [disjoint_left]
    rintro x ⟨z, hz, hzx⟩ hxZ
    have hzQ : z ∈ Q := ⟨⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le,
      by linarith [hz.2.2, hcK1]⟩, x, hxZ, hzx.symm⟩
    have := hcKQ z hzQ
    linarith [hz.2.2]
  have hGpre := isPreconnected_preimage_off hπ hπS hGo hGc hGE
  have hGD : π ⁻¹' G ⊆ V.O \ closure W := fun x hx =>
    ⟨image_mono hS'D hx, disjoint_left.1 hGZ hx⟩
  -- the foot of `σ` is in `π⁻¹[G]`, below every height of `W`
  set v := min (c' / 2) (w₂ / 2) with hv
  have hv0 : 0 < v := lt_min (by linarith) (by linarith [hw₂.1])
  have hvc : v < c' := (min_le_left _ _).trans_lt (by linarith)
  have hvw : v < w₂ := (min_le_right _ _).trans_lt (by linarith [hw₂.1])
  obtain ⟨P₀, hP₀⟩ := hsurj (F (t₀, v))
  have hP₀lev : V.lev P₀ v := ⟨⟨hv0, hvw⟩, hP₀⟩
  have hP₀G : P₀ ∈ π ⁻¹' G := ⟨(t₀, v), ⟨ht₀, hv0, hvc⟩, hP₀.symm⟩
  have hvu : ∀ u ∈ V.hts W, v < u := by
    rintro u ⟨P, hPZ, ⟨hu0, huw⟩, hPu⟩
    have huQ : ((t₀, u) : ℝ × ℝ) ∈ Q :=
      ⟨⟨⟨ht₀.1.le, ht₀.2.le⟩, hu0.le, by linarith [hw₂.2]⟩, P, hPZ, hPu⟩
    have := hcKQ _ huQ
    simp only at this
    linarith
  have hGbelow : π ⁻¹' G ⊆ V.below W := V.subset_below_of_lev hGpre hGD hP₀G hP₀lev hvu
  -- a point over the open bottom edge
  rw [disjoint_left]
  rintro x hx ⟨⟨t, y⟩, ⟨ht, hy⟩, hFt⟩
  rw [mem_singleton_iff] at hy
  subst hy
  set B : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-(1 / 2)) c' with hB
  have hBR : B ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := fun z hz =>
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1],
      by linarith [hz.2.2, hcK1]⟩
  have hNo : IsOpen (π ⁻¹' (F '' B)) :=
    (isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo) hBR).preimage hπc
  have hxN : x ∈ π ⁻¹' (F '' B) := ⟨(t, 0), ⟨ht, by norm_num, hc'0⟩, hFt⟩
  obtain ⟨P, hPN, hPa⟩ := mem_closure_iff.1 hx _ hNo hxN
  have hPO : P ∈ V.O := (VFrame.above_subset W hPa).1
  obtain ⟨q, hqD, hqP⟩ := hPO
  obtain ⟨q', hq'B, hq'P⟩ := hPN
  have hqq : q = q' := collar_injOn hF (hDR1 hqD) (openRect_subset_rect (hBR hq'B))
    (hqP.trans hq'P.symm)
  have hqS : q ∈ S' := ⟨(hDR hqD).1, (hDR hqD).2.1, by rw [hqq]; exact hq'B.2.2⟩
  exact disjoint_left.1 hWs (hGbelow ⟨q, hqS, hqP⟩) hPa

variable [CompactSpace M] [ConnectedSpace M]

/-! ### The low frame of a set-up -/

theorem Thm1Setup.c₁_le_one (S : Thm1Setup M) : S.c₁ ≤ 1 := S.hc₁.trans S.hS.c_le

theorem Thm1Setup.c₁_pos (S : Thm1Setup M) : 0 < S.c₁ := S.hw₂.1.trans_le S.hw₂.2

theorem Thm1Setup.disjoint_O_E (S : Thm1Setup M) :
    Disjoint (S.π ⁻¹' (S.F '' S.D')) (toPt S.E) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨m, hmE, rfl⟩
  exact Set.disjoint_left.1 (crossSet_disjoint_E S.hγπ S.hF S.c₁_le_one S.hR.sub S.E) ⟨hmE, hx⟩ hmE

theorem Thm1Setup.D'_sub_rect (S : Thm1Setup M) : S.D' ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
  fun z hz => ⟨⟨by linarith [(S.hR.sub hz).1.1], by linarith [(S.hR.sub hz).1.2]⟩,
    by linarith [(S.hR.sub hz).2.1], by linarith [(S.hR.sub hz).2.2, S.c₁_le_one]⟩

theorem Thm1Setup.lowFrame_hyps (S : Thm1Setup M) :
    IsPreconnected (S.π ⁻¹' (S.F '' S.D')) ∧
      ∀ J : Set ℝ, IsPreconnected J →
        IsPreconnected (S.π ⁻¹' (S.F '' (({(1 / 2 : ℝ)} : Set ℝ) ×ˢ (J ∩ Ioo 0 S.w₂)))) :=
  HPC.Hagopian.lowFrame_hyps S.hE S.hπ S.hπS S.hF S.D'_sub_rect S.hD'c S.hR.isOpen S.disjoint_O_E
    S.hsub

theorem Thm1Setup.injOn_O (S : Thm1Setup M) : InjOn S.π (S.π ⁻¹' (S.F '' S.D')) :=
  injOn_pi_preimage S.hπS S.hγπ S.hF fun d hd => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := S.hR.sub hd
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith [S.c₁_le_one]⟩, h3⟩

/-- **The low frame of a set-up**: `O = π⁻¹[D]` with the vertical `σ` over `1/2` up to `I₂`. -/
noncomputable def Thm1Setup.V (S : Thm1Setup M) : VFrame :=
  lowFrame S.π S.F S.D' (1 / 2) S.w₂ (S.hR.isOpen.preimage S.hπ.continuous) S.lowFrame_hyps.1
    S.hsub S.injOn_O S.hπ.surjective S.lowFrame_hyps.2

theorem Thm1Setup.V_O (S : Thm1Setup M) : S.V.O = S.π ⁻¹' (S.F '' S.D') := rfl

/-- The low rectangle `(3/22, 19/22) × (0, c₀) ⊆ D′`. -/
theorem Thm1Setup.exists_low (S : Thm1Setup M) :
    ∃ c₀ > 0, Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ Ioo 0 c₀ ⊆ S.D' := by
  obtain ⟨c₀, hc₀, -, hc₀I⟩ := exists_height_below S.hI.isCompact fun z hz => hz.1.2.1
  exact ⟨c₀, hc₀, rect_domain_low (r := ((3 / 22 : ℝ), S.r₂)) (s := ((19 / 22 : ℝ), S.s₂))
    (by norm_num) S.hR.sub S.hDf hc₀ fun z hz => (hc₀I z hz).le⟩

/-! ### §3.1: `K ⊆ Mid` and `f(y) ∈ π⁻¹[D]` -/

/-- **`K ⊆ Mid`** (commission 181 §3.1): the points of `K₀` lie over `1/2`, and `p = h(x₀)` with
`k(x₀) = 1/2` lies in `π⁻¹[D]` (it is separated by `F`) over `[1/2 − 2/n, 1/2 + 2/n]` (S0). -/
theorem Thm1Setup.K_subset_mid (S : Thm1Setup M) :
    toPt S.D.K ⊆ midSet M S.π S.F S.D' S.n := by
  have hn0 : (0 : ℝ) < 2 / (S.n : ℝ) := by
    have : (40 : ℝ) ≤ S.n := by exact_mod_cast S.hn
    positivity
  rintro _ ⟨y, hyK, rfl⟩
  rw [S.hK] at hyK
  rcases hyK with rfl | hy
  · obtain ⟨q, hqD, hq⟩ := S.D.sep.1.1
    obtain ⟨x₀, hkx, hpx, -, -⟩ := S.hcomp
    have hqR : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-S.c) S.c := by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := S.hR.sub hqD
      exact ⟨⟨by linarith, by linarith⟩, by linarith [S.hS.c_pos], by linarith [S.hc₁]⟩
    have hfine := S.hS.fine S.D.h S.h_small_θ x₀ q hqR (by rw [← hpx]; exact hq.symm)
    rw [hkx, abs_lt] at hfine
    exact ⟨S.D.p.2, q, hqD, hq.symm, by constructor <;> linarith [hfine.1, hfine.2]⟩
  · obtain ⟨q, ⟨hq1, hq2⟩, hq⟩ := hy
    rw [mem_singleton_iff] at hq1
    exact ⟨y.2, q, S.hsub ⟨hq1, hq2⟩, hq.symm, by rw [hq1]; constructor <;> linarith⟩

/-- `h₁[R(E)]` misses `F` (the composant choice `hcomp`, `strand_misses_of_composant`). -/
theorem Thm1Setup.h₁_Rset_notMem_G (S : Thm1Setup M) {z : M} (hz : z ∈ S.D.h₁ '' Rset S.k) :
    z ∉ S.D.G := by
  obtain ⟨x₀, -, -, -, hqC⟩ := S.hcomp
  have hGext : IsExtensionAway S.E (layer S.k 0) S.D.G := ⟨S.D.hEG, S.D.d, S.D.hG, S.D.hX0⟩
  have hne : ({z} : Set M) ≠ univ := by
    intro h
    obtain ⟨e0, he0⟩ := S.hE.2.1.2.1 0
    obtain ⟨e1, he1⟩ := S.hE.2.1.2.1 1
    have h0 : (e0 : M) ∈ ({z} : Set M) := by rw [h]; exact mem_univ _
    have h1 : (e1 : M) ∈ ({z} : Set M) := by rw [h]; exact mem_univ _
    have : e0 = e1 := Subtype.ext (h0.trans h1.symm)
    rw [this, he1] at he0
    exact one_ne_zero he0
  have := strand_misses_of_composant S.hX S.hi S.hE x₀.2 S.D.h₁ hqC hGext hz
    ⟨isCompact_singleton, isConnected_singleton⟩ hne (mem_singleton z)
  exact disjoint_left.1 this (mem_singleton z)

/-- **§3.1, `f(y) ∈ π⁻¹[D]`** (p. 348: "Note that `f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`"). For
`y ∈ K` with `h⁻¹(y) ∈ R(E)` (as for the point of Property 4, whose component has closure essential
to `h[R(E)]`), `f(y) = h₁h⁻¹(y)` lies in `π⁻¹[D]`.

*Proof:* `f(y) ∈ h₁[R(E)]` misses `F ⊇ E` (`hcomp`), `y ∈ Mid` (`K_subset_mid`) and
`ρ(y, f(y)) < ε₃`, so `hε₃O` applies. -/
theorem f_mem_O_of_mem_K (S : Thm1Setup M) {y : M} (hyK : y ∈ S.D.K)
    (hyR : S.D.h.symm y ∈ Rset S.k) : ((S.D.f y : M) : Pt) ∈ S.π ⁻¹' (S.F '' S.D') := by
  have hfR : S.D.f y ∈ S.D.h₁ '' Rset S.k := ⟨S.D.h.symm y, hyR, rfl⟩
  have hfG := S.h₁_Rset_notMem_G hfR
  have hfE : ((S.D.f y : M) : Pt) ∉ toPt S.E := by
    rintro ⟨e, he, hef⟩
    exact hfG (Subtype.ext hef ▸ S.D.hEG he)
  refine S.hε₃O _ (S.D.f y).2 hfE _ (S.K_subset_mid ⟨y, hyK, rfl⟩) ?_
  have := S.D.f_small y
  rwa [Subtype.dist_eq] at this

/-- **`f(y)` is off `F`** for `y` with `h⁻¹(y) ∈ R(E)`. -/
theorem f_notMem_G_of_Rset (S : Thm1Setup M) {y : M} (hyR : S.D.h.symm y ∈ Rset S.k) :
    S.D.f y ∉ S.D.G :=
  S.h₁_Rset_notMem_G ⟨S.D.h.symm y, hyR, rfl⟩

/-! ### §3.2.2: the cap lemma -/

/-- **§3.2.2, the cap lemma `cross_strand_near`.** Let `W` be a crossing piece with disjoint
sides in the low frame `S.V`, `a ∈ Mid` below `W`, `b` above `W`, and `ρ(a, b) < ε₃`. Then
`ρ(a, Cl W) < ε₃`.

*Proof:* by the abstract cap (`VFrame.infDist_le_of_segment`) it suffices that the segment
`[a, b]` misses `Cl(B(W)) − O`. A point `c` there is within `ε₃` of `a` and lies over `Fr D`:
over `I₂` it is `ε₂`-far from `a ∈ M` (`hε₂I`, `ε₃ < ε₂`); over a closed side segment, or over an
end of the bottom edge, it is `ε₃`-far from `a ∈ Mid` (`hε₃S`); over the open bottom edge it is
not in `Cl B(W)` (`above_closure_misses_bottom`). -/
theorem cross_strand_near (S : Thm1Setup M) {W : Set Pt}
    (hW : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ W)
    (hWs : Disjoint (S.V.below W) (S.V.above W)) {a b : Pt} (ha : a ∈ midSet M S.π S.F S.D' S.n)
    (haW : a ∈ S.V.below W) (hbW : b ∈ S.V.above W) (hab : dist a b < S.ε₃) :
    infDist a (closure W) < S.ε₃ := by
  refine (VFrame.infDist_le_of_segment hWs haW hbW ?_).trans_lt hab
  rw [disjoint_left]
  rintro c hc ⟨hcl, hcO⟩
  have hca : dist a c < S.ε₃ := (VFrame.dist_le_of_mem_segment hc).trans_lt hab
  have hcfr : c ∈ frontier (S.π ⁻¹' (S.F '' S.D')) := by
    refine ⟨closure_mono (fun P hP => (VFrame.above_subset W hP).1) hcl, ?_⟩
    rw [(S.hR.isOpen.preimage S.hπ.continuous).interior_eq]
    exact hcO
  have hcf := S.hπ.continuous.frontier_preimage_subset _ hcfr
  rw [mem_preimage, S.hFDf] at hcf
  have hside : ∀ q : ℝ × ℝ, q ∈ (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 S.c₁) →
      S.π c = S.F q → False := fun q hq hcq => by
    have := S.hε₃S a ha c ⟨q, hq, hcq.symm⟩
    linarith
  rcases hcf with ((hI | ⟨⟨t, y⟩, ⟨ht, hy⟩, hFt⟩) | ⟨q, ⟨hq1, hq2⟩, hFq⟩) | ⟨q, ⟨hq1, hq2⟩, hFq⟩
  · have := S.hε₂I a ha.1 c (Or.inr hI)
    linarith [S.hε₂₃]
  · rw [mem_singleton_iff] at hy
    subst hy
    rcases eq_or_lt_of_le ht.1 with h1 | h1
    · exact hside (t, 0) ⟨Or.inl h1.symm, le_rfl, S.c₁_pos.le⟩ hFt.symm
    rcases eq_or_lt_of_le ht.2 with h2 | h2
    · exact hside (t, 0) ⟨Or.inr h2, le_rfl, S.c₁_pos.le⟩ hFt.symm
    have hmiss := above_closure_misses_bottom S.hπ S.hπS S.hγπ S.hF (by norm_num : (0 : ℝ) < 3 / 22)
      (by norm_num : (19 / 22 : ℝ) < 1) S.c₁_le_one S.hR.sub S.exists_low
      (t₀ := 1 / 2) ⟨by norm_num, by norm_num⟩ ⟨S.hw₂.1, S.hw₂.2.trans S.c₁_le_one⟩
      (S.hR.isOpen.preimage S.hπ.continuous) S.lowFrame_hyps.1 S.hsub S.injOn_O S.hπ.surjective
      S.lowFrame_hyps.2 hW.compact
      (hW.miss.mono_right (preimage_mono subset_union_right)) hWs
    exact disjoint_left.1 hmiss hcl ⟨(t, 0), ⟨⟨h1, h2⟩, rfl⟩, hFt⟩
  · exact hside q ⟨Or.inl hq1, hq2.1, hq2.2.trans S.r₂_le⟩ hFq.symm
  · exact hside q ⟨Or.inr hq1, hq2.1, hq2.2.trans S.s₂_le⟩ hFq.symm

/-- **§3.2.3, the mirror of the cap lemma** (commission 181 §2.2: "the cap lemma of §3.2 needs its
mirror"). Let `W` have disjoint sides in `S.V`, `a ∈ Mid` above `W`, `b` below `W`, `ρ(a, b) < ε₃`.
If `a` is at distance `≥ ε₃` from `π⁻¹` of the bottom edge, then `ρ(a, Cl W) < ε₃`.

The extra hypothesis is what the asymmetry of the frame costs: the region below `W` reaches the
bottom edge, which lies over `E`, and a point of `Mid` (for instance of `K₀`) can be arbitrarily
close to `E`. Over `I₂` and over the sides the argument is that of `cross_strand_near` (`hε₂I`,
`hε₃S`); no analogue of `above_closure_misses_bottom` is needed. -/
theorem cross_strand_near_mirror (S : Thm1Setup M) {W : Set Pt}
    (hWs : Disjoint (S.V.below W) (S.V.above W)) {a b : Pt} (ha : a ∈ midSet M S.π S.F S.D' S.n)
    (haW : a ∈ S.V.above W) (hbW : b ∈ S.V.below W) (hab : dist a b < S.ε₃)
    (hbot : ∀ z : Pt, S.π z ∈ S.F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ {0}) → S.ε₃ ≤ dist a z) :
    infDist a (closure W) < S.ε₃ := by
  refine (VFrame.infDist_le_of_segment_mirror hWs haW hbW ?_).trans_lt hab
  rw [disjoint_left]
  rintro c hc ⟨hcl, hcO⟩
  have hca : dist a c < S.ε₃ := (VFrame.dist_le_of_mem_segment hc).trans_lt hab
  have hcfr : c ∈ frontier (S.π ⁻¹' (S.F '' S.D')) := by
    refine ⟨closure_mono (fun P hP => (VFrame.below_subset W hP).1) hcl, ?_⟩
    rw [(S.hR.isOpen.preimage S.hπ.continuous).interior_eq]
    exact hcO
  have hcf := S.hπ.continuous.frontier_preimage_subset _ hcfr
  rw [mem_preimage, S.hFDf] at hcf
  have hside : ∀ q : ℝ × ℝ, q ∈ (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 S.c₁) →
      S.π c = S.F q → False := fun q hq hcq => by
    have := S.hε₃S a ha c ⟨q, hq, hcq.symm⟩
    linarith
  rcases hcf with ((hI | hB) | ⟨q, ⟨hq1, hq2⟩, hFq⟩) | ⟨q, ⟨hq1, hq2⟩, hFq⟩
  · have := S.hε₂I a ha.1 c (Or.inr hI)
    linarith [S.hε₂₃]
  · have := hbot c hB
    linarith
  · exact hside q ⟨Or.inl hq1, hq2.1, hq2.2.trans S.r₂_le⟩ hFq.symm
  · exact hside q ⟨Or.inr hq1, hq2.1, hq2.2.trans S.s₂_le⟩ hFq.symm

end CapLow

end HPC.Hagopian
