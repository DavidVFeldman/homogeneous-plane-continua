import HPC.Hagopian.H76Mid

/-!
# Batch 179, §5 (repaired in batch 180, §1.2–§1.3): `Thm1Setup` and Theorem 1 from saturation
# and the step

`Thm1Setup M` bundles Hagopian's set-up for Theorem 1 (T1–T13): the type A′ continuum `E` with its
decomposition `k`, the quotient map `π` and the arc `γ`, the collar `F`, `ε₁` with end control, the
refinement `L` with Property 1, the strand constants, the domain `D = F[D′]` (T7, T8) with its
height `c₁` and the low vertical over `t₀ = 1/2`, Property 2 at `(ε₂, ε₃)`, and a `T12Data`
package `D` (T12, T13). It also records Property 3 as printed and the finiteness of `I` for
`F = D.G` (the heights of §4 enter before `D`).

Batch 180 (commission 180 §1.2) adds: `n ≥ 40`; the strip depth `cs` and `I₁`; `ε₂` as printed
(`ε₂ ≤ ε₁`, `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])`, and the E2.2 margin); `ε₃ ≤ θ/2` and the position clause of
`eps3_positions_middle`; `K = {p} ∪ K₀` with `K₀` the points of `M` over the open low vertical
`F[{1/2} × (0, w₂)]`; the low vertical over `15/22` (E2.3, E2.5); and the composant data of the
package. Batch 181 (commission 181 §3.1) adds the two bounds `hε₃O`, `hε₃S` on `ε₃` relative to
the middle set `Mid` (`midSet`, `H76Mid.lean`). With batch 179's `K = {p}`, Property 4
fails for every block below the top (`property4_lower_false_of_K_eq`, `Hagopian76Y.lean`).

`exists_thm1Setup`: if `M` is not hereditarily indecomposable, there is a set-up for which
`InnerComponentsCross` (on `(3/22 + 8/n, 19/22 − 8/n)`, commission 180 §2.2) and the induction step
give `False` (T1–T11 assembled, then `hagopian76_T15_T17_cond4`).

`hagopian76_theorem1_of_step`: Theorem 1 from `InnerComponentsCross` and `Property4Step`, both for
every set-up.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **Hagopian's set-up for Theorem 1** (commission 179 §5; T1–T13). -/
structure Thm1Setup (M : Set Pt) [CompactSpace M] [ConnectedSpace M] where
  hX : IsHomogeneous M
  hi : ¬ IsDecomposableSpace M
  E : Set M
  k : E → unitInterval
  hE : IsMinimalAdmissible E k
  π : Pt → Pt
  γ : unitInterval → Pt
  hπ : IsQuotientMap π
  hπS : ∀ p q, π p = π q ↔ layerSetoid k p q
  hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t
  F : ℝ × ℝ → Pt
  hF : IsCollar γ F
  ε₁ : ℝ
  he : IsEps1 k ε₁
  hend : EndCtl k ε₁
  L : Fin 11 → Set Pt
  hLch : IsPlaneChain L
  hEL : toPt E ⊆ ⋃ j, L j
  hLG : ∀ j, L j ⊆ chainG k ε₁ j
  hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
    ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
      ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j
  n : ℕ
  θ : ℝ
  c : ℝ
  hS : StrandConst E k π F n θ c
  /-- §1.2.5 (commission 180): `n ≥ 40`, so that the saturation interval
  `(3/22 + 8/n, 19/22 − 8/n)` contains `(3/8, 5/8)` (§2.2) and `3/22 > 4/n + δ` (§2.1, step 2). -/
  hn : 40 ≤ n
  c₁ : ℝ
  hc₁ : c₁ ≤ c
  D' : Set (ℝ × ℝ)
  hR : IsCrossRegion M π F c₁ D'
  hD'c : IsPreconnected D'
  hbelow : ∃ c' > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c') 0)) (π '' M)
  /-- §1.2.3: the depth of the strip below `γ([3/22, 19/22])` missing `π[M]` (`hagopian76_I1`). -/
  cs : ℝ
  hcs : 0 < cs
  hcs1 : cs ≤ 1
  hstrip : Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-cs) 0)) (π '' M)
  /-- §1.2.3: Hagopian's interval `I₁` below `⟨p₁, p₅⟩`, the side of the strip at height `−cs/2`
  (used, with `I₂`, in the choice of `ε₂`). -/
  I₁ : Set Pt
  hI₁ : I₁ = F '' (Icc (3 / 22) (19 / 22) ×ˢ {-(cs / 2)})
  r₂ : ℝ
  s₂ : ℝ
  I₂ : Set Pt
  hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
    (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂)
  hIs : (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
    (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)}
  hIR : I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁)
  hDo : IsOpen D'
  hDf : frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∪
    Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
    ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂
  hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
    F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂)
  hI2M : Disjoint I₂ (π '' M)
  w₂ : ℝ
  hw₂ : w₂ ∈ Ioc 0 c₁
  hFw : F ((1 / 2 : ℝ), w₂) ∈ I₂
  hseg : Disjoint (({(1 / 2 : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂)
    (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂)
  hsub : ({(1 / 2 : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D'
  /-- §1.2.6 (field audit; E2.3, E2.5): the low vertical `V` over `15/22`, from its foot on the
  axis to the first point `F(15/22, w₃)` of `I₂` (`hagopian76_K0` at `t₀ = 15/22`). -/
  w₃ : ℝ
  hw₃ : w₃ ∈ Ioc 0 c₁
  hFw₃ : F ((15 / 22 : ℝ), w₃) ∈ I₂
  hseg₃ : Disjoint (({(15 / 22 : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₃)
    (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂)
  hsub₃ : ({(15 / 22 : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₃ ⊆ D'
  ε₂ : ℝ
  /-- §1.2.3: `ε₂` as printed (p. 346): positive, at most `ε₁`, at most `ρ(M, π⁻¹[I₁ ∪ I₂])`. -/
  hε₂ : 0 < ε₂
  hε₂₁ : ε₂ ≤ ε₁
  hε₂I : ∀ m ∈ M, ∀ z : Pt, π z ∈ I₁ ∪ I₂ → ε₂ ≤ dist m z
  /-- §1.2.6 (E2.2): the margin keeping `N` `ε₂` away from the vertical over `15/22`. -/
  hε₂V : 5 / (n : ℝ) + ε₂ < 15 / 22 - 3 / 22
  ε₃ : ℝ
  hε₃ : 0 < ε₃
  hε₂₃ : ε₃ < ε₂
  hP2 : Property2At k ε₂ ε₃
  /-- §1.2.2/§1.2.4: `ε₃ ≤ θ/2`, so `h`, `h₁` are `θ/4`-homeomorphisms (`Thm1Setup.h_small_θ`). -/
  hε₃θ : ε₃ ≤ θ / 2
  /-- §1.2.4: the position clause of `eps3_positions_middle` at `ε₃`. -/
  hpos : ∀ (y w : M) (z z' : ℝ × ℝ), z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 →
    z' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → z.1 = 1 / 2 → π (y : Pt) = F z →
    π (w : Pt) = F z' → dist (y : Pt) w < ε₃ → z'.1 ∈ Ioo (3 / 8 : ℝ) (5 / 8)
  /-- §3.1.1 (commission 181): every point of `M − E` within `ε₃` of a point of
  `Mid = midSet M π F D' n` lies in `π⁻¹[D]` (`exists_eps_mid_O`). -/
  hε₃O : ∀ m ∈ M, m ∉ toPt E → ∀ a ∈ midSet M π F D' n, dist m a < ε₃ → π m ∈ F '' D'
  /-- §3.1.2 (commission 181): every point of `Mid` is at distance `≥ ε₃` from
  `π⁻¹F[{3/22, 19/22} × [0, c₁]]` (`exists_eps_mid_sides`). -/
  hε₃S : ∀ a ∈ midSet M π F D' n, ∀ z : Pt,
    π z ∈ F '' (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) → ε₃ ≤ dist a z
  D : T12Data E k π F D' ε₃
  /-- §1.2.1: `K = {p} ∪ K₀`, `K₀` the points of `M` over the open low vertical
  `F[{1/2} × (0, w₂)]` (Hagopian's component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]`, `hagopian76_K0`). -/
  hK : D.K = insert D.p {m : M | π (m : Pt) ∈ F '' (({(1 / 2 : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂)}
  /-- §1.2.2: the composant data of `exists_T12Data_comp`. -/
  hcomp : ∃ x₀ : E, (k x₀ : ℝ) = 1 / 2 ∧ D.p = D.h x₀ ∧
    D.h (x₀ : M) ∉ Jones.composant (x₀ : M) ∧ D.h₁ (x₀ : M) ∉ Jones.composant (x₀ : M)
  hP3 : ∀ C : Set M, IsCrossingComponent D.G π F c₁ D' C → ∀ v : unitInterval,
    ¬ C ⊆ layer D.d v
  hfin : (crossingIntervals D.d π F c₁ D').Finite

/-- The block hypotheses of the induction (`hagopian76_T15_T17_cond2`): `x₁ < ⋯ < x₂ₘ`, `x₁ = 0`,
`d⁻¹[[0, x₂]] = E`, every member of `I` inside a block, `x₂ₘ = 1`. -/
def Thm1Setup.IsBlocks {M : Set Pt} [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M)
    (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  2 ≤ m ∧ StrictMonoOn x (Icc 1 (2 * m)) ∧ x 1 = 0 ∧ layerSet S.D.d (Icc 0 (x 2)) = S.E ∧
    (∀ r ∈ crossingIntervals S.D.d S.π S.F S.c₁ S.D', ∃ i, 1 ≤ i ∧ i ≤ m ∧
      x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) ∧ x (2 * m) = 1

section Assembly179

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- `h` is a `θ/4`-homeomorphism (from `ε₃ ≤ θ/2`). -/
theorem Thm1Setup.h_small_θ (S : Thm1Setup M) (v : M) : dist (S.D.h v) v < S.θ / 4 :=
  (S.D.h_small v).trans_le (by linarith [S.hε₃θ])

/-- `h₁` is a `θ/4`-homeomorphism (from `ε₃ ≤ θ/2`). -/
theorem Thm1Setup.h₁_small_θ (S : Thm1Setup M) (v : M) : dist (S.D.h₁ v) v < S.θ / 4 :=
  (S.D.h₁_small v).trans_le (by linarith [S.hε₃θ])

omit [ConnectedSpace M] in
/-- `I₂` is compact: it is the image under `F` of an arc of the rectangle. -/
theorem isCompact_I₂_aux {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {c₁ : ℝ}
    (hc₁ : c₁ ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁)) : IsCompact I₂ := by
  obtain ⟨-, f, hf, hfr, -, -⟩ := hI
  have hK : IsCompact (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) := by
    rw [← hfr]; exact isCompact_range hf.continuous
  have hsub : Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂ ⊆
      Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun z hz =>
    ⟨⟨by linarith [hz.1.1.1], by linarith [hz.1.1.2]⟩, by linarith [hz.1.2.1],
      by linarith [hz.1.2.2]⟩
  have heq : F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) = I₂ := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact hz.2
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hIR hy
      exact ⟨z, ⟨hz, hy⟩, rfl⟩
  rw [← heq]; exact isCompact_collar_image hF hK hsub

/-- **T1–T13 assembled, repaired** (commission 180 §1.2–§1.3). If `M` is a homogeneous
indecomposable plane continuum with a decomposable subcontinuum `A`, there is a set-up
`S : Thm1Setup M` (with the batch-180 fields) such that `InnerComponentsCross` for `F = S.D.G` on
`(3/22 + 8/n, 19/22 − 8/n)` and the induction step for every block sequence give `False`.

*Route:* as in batch 179, with `n = 40`; the strip depth `cs = min c' 1` and `I₁` from
`hagopian76_I1`; `ε₂ = min (min ε₁ δ) (1/4)` with `δ = ρ(M, π⁻¹[I₁ ∪ I₂])`
(`hagopian76_eps2_pos`); `ε₃ = min (min ε₃' (θ/2)) (min δS δO)` with `ε₃'` from
`eps3_positions_middle` at `ε₂` and `δS`, `δO` from `exists_eps_mid_sides`, `exists_eps_mid_O`
(commission 181 §3.1); and
the package of `hagopian76_T15_T17_cond4` with `K₀ = π⁻¹F[{1/2} × (0, w₂)] ∩ M`. -/
theorem exists_thm1Setup (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {A : Set M}
    (hA : Fold.Q78.IsContinuum A) (hAd : ¬ Fold.Q78.IsIndecomposable A) :
    ∃ S : Thm1Setup M,
      (InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) →
      (∀ x m, S.IsBlocks x m → Property4Step S.D x m) → False) := by
  obtain ⟨E₀, -, hirr, k₀, hadm, hvoid⟩ := hagopian75_exists_typeA' hX hi hA hAd
  have hE₀ : IsMinimalAdmissible E₀ k₀ := ⟨hirr, hadm, hvoid⟩
  obtain ⟨E, k₁, -, -, hE₁, p, ⟨q, hq, rfl⟩, hacc⟩ := exists_accessible_typeA' hX hE₀
  obtain ⟨π, γ₁, hπ, hπS₁, hγ₁, hγπ₁, -⟩ := exists_quotient_plane' hX hi hE₁
  obtain ⟨k, γ, hE, hπS, -, hγπ, -, F, hF, cb, hcb, hstrip₀⟩ := hagopian76_I1 hX hi hE₁ hπ hπS₁
    hγ₁ hγπ₁ (y := k₁ q) hq.1 hq.2 ⟨(q : M), ⟨q, rfl, rfl⟩, hacc⟩
  have hbelow : ∃ c' > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c') 0)) (π '' M) :=
    ⟨cb, hcb, hstrip₀⟩
  set cs := min cb 1 with hcsdef
  have hcs : 0 < cs := lt_min hcb one_pos
  have hcs1 : cs ≤ 1 := min_le_right _ _
  have hstrip : Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-cs) 0)) (π '' M) :=
    hstrip₀.mono_left (image_mono (prod_mono subset_rfl
      (Ico_subset_Ico (by linarith [min_le_left cb 1]) le_rfl)))
  obtain ⟨ε₁, he, hend⟩ := exists_isEps1_endCtl hE
  obtain ⟨L, -, -, -, -, -, -, ⟨hLch, hLG⟩, hfol, -, hP1'⟩ := hagopian76_property1 hX hi hE he
  have hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j := fun y i h1 h2 hy => by
    obtain ⟨h, hh, hyh, hpc, -⟩ := hP1' y i h1 h2 hy
    exact ⟨h, hh, hyh, hpc⟩
  obtain ⟨θ, c, hS⟩ := strand_fine_translate hX hE hπ.continuous hπS hγπ hF 40 (by norm_num)
  obtain ⟨cU, hcU, -, hmain⟩ := hagopian76_T15_T17_cond4 hX hi hE he hend hπ hπS hγπ hF hLch
    hfol.1 hLG hP1 hS (by norm_num)
  obtain ⟨cP, hcP, -, hP3⟩ := hagopian76_property3_components_unif hX hi hE he hend hπ hπS hγπ hF
    hLch hfol.1 hLG hP1
  obtain ⟨cI, hcI, -, hfin⟩ := hagopian76_I_finite_unif hX hi hE he hend hπ hπS hγπ hF hLch
    hfol.1 hLG hP1
  obtain ⟨c₇, hc₇, hc₇1, -, hT7⟩ := hagopian76_T7 hX hi hE hπ hπS hγπ hF (a := 3 / 22)
    (b := 19 / 22) (by norm_num) (by norm_num) (by norm_num) isOpen_univ (subset_univ _)
  set c' := min (min c cU) (min (min cP cI) c₇) with hc'
  have hc'0 : 0 < c' := lt_min (lt_min hS.c_pos hcU) (lt_min (lt_min hcP hcI) hc₇)
  have hc'c : c' ≤ c := (min_le_left _ _).trans (min_le_left _ _)
  have hc'U : c' ≤ cU := (min_le_left _ _).trans (min_le_right _ _)
  have hc'P : c' ≤ cP := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hc'I : c' ≤ cI := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hc'7 : c' ≤ c₇ := (min_le_right _ _).trans (min_le_right _ _)
  have hc'1 : c' ≤ 1 := hc'7.trans hc₇1
  obtain ⟨r, s, I₂, hI, hIR, hIM, hIs, hr, hs⟩ := hT7 c' hc'0 hc'7
  obtain ⟨r₂, s₂, D', hr₂, hs₂, -, -, hIarc, hIends, hDo, hDc, hDR, hDf, hFDo, -, -, -, hFDf, -,
    -⟩ := hagopian76_D hi hE hπ hπS hγπ hF (by norm_num : (0 : ℝ) < 3 / 22)
      (by norm_num : (3 / 22 : ℝ) < 19 / 22) (by norm_num : (19 / 22 : ℝ) < 1) hc'0 hc'1 hbelow
      hI hIR hIs hr hs
  have hR : IsCrossRegion M π F c' D' := isCrossRegion_of_D hDR hFDo hFDf hIM hr₂.2 hs₂.2
  obtain ⟨w₂, hw₂, hFw, hseg, hsub, -⟩ := hagopian76_K0 hE hπ hπS hγπ hF
    (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (3 / 22 : ℝ) < 19 / 22)
    (by norm_num : (19 / 22 : ℝ) < 1) hc'1 hIarc hDo hDR hDf ⟨1 / 2, by norm_num, by norm_num⟩
    (by constructor <;> norm_num)
  obtain ⟨w₃, hw₃, hFw₃, hseg₃, hsub₃, -⟩ := hagopian76_K0 hE hπ hπS hγπ hF
    (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (3 / 22 : ℝ) < 19 / 22)
    (by norm_num : (19 / 22 : ℝ) < 1) hc'1 hIarc hDo hDR hDf ⟨15 / 22, by norm_num, by norm_num⟩
    (by constructor <;> norm_num)
  -- `I₁` and `ε₂` (p. 346)
  set I₁ : Set Pt := F '' (Icc (3 / 22) (19 / 22) ×ˢ {-(cs / 2)}) with hI₁
  have hI₁c : IsCompact I₁ := isCompact_collar_image hF (isCompact_Icc.prod isCompact_singleton)
    (fun z hz => by
      obtain ⟨⟨h1, h2⟩, h3⟩ := hz
      rw [mem_singleton_iff] at h3
      exact ⟨⟨by linarith, by linarith⟩, by rw [h3]; linarith, by rw [h3]; linarith⟩)
  have hI₁M : Disjoint I₁ (π '' M) := hstrip.mono_left (image_mono (prod_mono subset_rfl
    (fun u hu => by rw [mem_singleton_iff] at hu; rw [hu]; constructor <;> linarith)))
  have hI₂c : IsCompact I₂ := isCompact_I₂_aux hF hc'1 hIarc
    (fun z hz => by
      obtain ⟨w, hw, rfl⟩ := hIR hz
      exact ⟨w, hw, rfl⟩)
  obtain ⟨δ, hδ, hδI⟩ := hagopian76_eps2_pos (M := M) hπ.continuous
    (hI₁c.union hI₂c).isClosed (disjoint_union_left.2 ⟨hI₁M, hIM⟩)
  set ε₂ := min (min ε₁ δ) (1 / 4) with hε₂def
  have hε₂ : 0 < ε₂ := lt_min (lt_min he.pos hδ) (by norm_num)
  have hε₂₁ : ε₂ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂δ : ε₂ ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hε₂4 : ε₂ ≤ 1 / 4 := min_le_right _ _
  -- `ε₃`
  obtain ⟨ε₃', hε₃', hε₃'₂, hP2', hpos'⟩ := eps3_positions_middle hX hi hE hπ.continuous hF hε₂
  -- the two bounds of commission 181 §3.1 (`Mid`)
  obtain ⟨c₀, hc₀, hc₀1, hc₀I⟩ := exists_height_below hIarc.isCompact fun z hz => hz.1.2.1
  have hlow : Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ Ioo 0 c₀ ⊆ D' :=
    rect_domain_low (r := ((3 / 22 : ℝ), r₂)) (s := ((19 / 22 : ℝ), s₂)) (by norm_num) hR.sub hDf
      hc₀ fun z hz => (hc₀I z hz).le
  obtain ⟨δS, hδS, hδSd⟩ := exists_eps_mid_sides (M := M) hπ.continuous hF hc'1 hR.sub
    (n := 40) le_rfl
  obtain ⟨δO, hδO, hδOd⟩ := exists_eps_mid_O hE hπ.continuous hπS hγπ hF hc'1 hR (n := 40) le_rfl
    hcs hcs1 hstrip hc₀ hc₀1 hlow
  set ε₃ := min (min ε₃' (θ / 2)) (min δS δO) with hε₃def
  have hε₃ : 0 < ε₃ := lt_min (lt_min hε₃' (by linarith [hS.θ_pos])) (lt_min hδS hδO)
  have hε₃₃ : ε₃ ≤ ε₃' := (min_le_left _ _).trans (min_le_left _ _)
  have hε₃S : ε₃ ≤ δS := (min_le_right _ _).trans (min_le_left _ _)
  have hε₃O : ε₃ ≤ δO := (min_le_right _ _).trans (min_le_right _ _)
  have h40 : ((40 : ℕ) : ℝ) = 40 := by norm_num
  set K₀ : Set M := {m : M | π (m : Pt) ∈ F '' (({(1 / 2 : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂)} with hK₀
  obtain ⟨D, hDK, hcomp, hD⟩ := hmain (c₁ := c') (D' := D') (t₀ := (1 / 2 : ℝ)) hc'c hc'U hR
    hDc.2 hbelow hIarc hIends hIR hDo hDf hFDf hIM (by rw [h40]; norm_num)
    (by rw [h40]; norm_num) hw₂ hFw hseg hsub K₀ hε₃
  let S : Thm1Setup M :=
    { hX := hX
      hi := hi
      E := E
      k := k
      hE := hE
      π := π
      γ := γ
      hπ := hπ
      hπS := hπS
      hγπ := hγπ
      F := F
      hF := hF
      ε₁ := ε₁
      he := he
      hend := hend
      L := L
      hLch := hLch
      hEL := hfol.1
      hLG := hLG
      hP1 := hP1
      n := 40
      θ := θ
      c := c
      hS := hS
      hn := le_rfl
      c₁ := c'
      hc₁ := hc'c
      D' := D'
      hR := hR
      hD'c := hDc.2
      hbelow := hbelow
      cs := cs
      hcs := hcs
      hcs1 := hcs1
      hstrip := hstrip
      I₁ := I₁
      hI₁ := rfl
      r₂ := r₂
      s₂ := s₂
      I₂ := I₂
      hI := hIarc
      hIs := hIends
      hIR := hIR
      hDo := hDo
      hDf := hDf
      hFDf := hFDf
      hI2M := hIM
      w₂ := w₂
      hw₂ := hw₂
      hFw := hFw
      hseg := hseg
      hsub := hsub
      w₃ := w₃
      hw₃ := hw₃
      hFw₃ := hFw₃
      hseg₃ := hseg₃
      hsub₃ := hsub₃
      ε₂ := ε₂
      hε₂ := hε₂
      hε₂₁ := hε₂₁
      hε₂I := fun m hm z hz => hε₂δ.trans (hδI m hm z hz)
      hε₂V := by rw [h40]; linarith
      ε₃ := ε₃
      hε₃ := hε₃
      hε₂₃ := hε₃₃.trans_lt hε₃'₂
      hP2 := hP2'.mono hε₃₃
      hε₃θ := (min_le_left _ _).trans (min_le_right _ _)
      hpos := fun y w z z' hz hz' hz1 hy hw hd => hpos' y w z z' hz hz' hz1 hy hw
        (hd.trans_le hε₃₃)
      hε₃O := fun m hm hmE a ha hd => hδOd m hm hmE a ha (hd.trans_le hε₃O)
      hε₃S := fun a ha z hz => hε₃S.trans (hδSd a ha z hz)
      D := D
      hK := hDK
      hcomp := hcomp
      hP3 := hP3 D.G D.d D.hG D.hEG D.hX0 c' D' hc'P hR
      hfin := hfin D.G D.d D.hG D.hEG D.hX0 c' D' hc'I hR }
  refine ⟨S, fun hICC hstep => ?_⟩
  exact hD (3 / 22 + 8 / ((40 : ℕ) : ℝ)) (19 / 22 - 8 / ((40 : ℕ) : ℝ))
    (by rw [h40]; norm_num) (by rw [h40]; norm_num) hICC
    (fun x m hm hx hx1 hx2 hbl hxn => hstep x m ⟨hm, hx, hx1, hx2, hbl, hxn⟩)

end Assembly179

/-- **§5: Theorem 1 from saturation and the step** (commission 179 §5; restated in batch 180 §1.3
for the repaired set-up). If, for every set-up `S : Thm1Setup M`,
* `InnerComponentsCross` holds for `F = S.D.G` on `(3/22 + 8/n, 19/22 − 8/n)` (item 2e, with the
  margin of commission 180 §2.2), and
* the induction step `Property4Step S.D x m` holds for every block sequence (item §4),

then every homogeneous indecomposable plane continuum is hereditarily indecomposable. -/
theorem hagopian76_theorem1_of_step
    (hICC : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M),
      InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)))
    (hstep : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M) x m,
      S.IsBlocks x m → Property4Step S.D x m) :
    Hagopian76Thm1 := by
  intro M _ _ hX hi K _ hK
  by_contra hKi
  obtain ⟨S, hS⟩ := exists_thm1Setup hX hi hK hKi
  exact hS (hICC M S) (hstep M S)

end HPC.Hagopian
