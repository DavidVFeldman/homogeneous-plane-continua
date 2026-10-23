import HPC.Hagopian.H76Sat182

/-!
# Batch 182, report §2.4: tight block sequences

The reduction `hagopian76_theorem1_of_step` (batch 179) asks for the induction step for *every*
block sequence `S.IsBlocks x m`. `IsBlocks` dropped two clauses that `exists_blocks_uncond` provides:
every parameter of a block is `≤ x₂` or in a member of `I`, and no member of `I` straddles a gap.
Without them a block sequence may be *padded*: a block `[u, v]` inside a gap `(x₂ᵢ, x₂ᵢ₊₁)` contains
no member of `I`, so (with saturation) `d⁻¹[[u, v]]` has no block strand, and the step into that
block cannot be argued as printed (report §2.4, non-vacuity note on `StepFrame`).

* `Thm1Setup.IsTightBlocks`: `IsBlocks` with the two clauses.
* `hagopian76_T15_T17_cond5`, `exists_thm1Setup_tight`, `hagopian76_theorem1_of_step_tight`: the
  batch-179/180 theorems with the step asked only for tight block sequences (proofs copied, with the
  two clauses passed on).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **Tight block sequences**: `IsBlocks`, and the two clauses of `exists_blocks_uncond`: every
parameter of a block is `≤ x₂` or lies in a member of `I`; no member of `I` straddles a gap. -/
def Thm1Setup.IsTightBlocks {M : Set Pt} [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M)
    (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  S.IsBlocks x m ∧
    (∀ i, 1 ≤ i → i ≤ m → ∀ t ∈ Icc (x (2 * i - 1)) (x (2 * i)),
      t ≤ x 2 ∨ ∃ r ∈ crossingIntervals S.D.d S.π S.F S.c₁ S.D', t ∈ Icc r.1 r.2) ∧
    (∀ i, 1 ≤ i → i < m → ∀ r ∈ crossingIntervals S.D.d S.π S.F S.c₁ S.D',
      r.2 ≤ x (2 * i) ∨ x (2 * i + 1) ≤ r.1)

section Tight

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **`hagopian76_T15_T17_cond4` with tight blocks** (batch 182, report §2.4): the same package;
the induction step is needed only for block sequences that are *tight*, i.e. that also carry the two
clauses of `exists_blocks_uncond` which `IsBlocks` dropped: every parameter of a block is `≤ x₂` or
lies in a member of `I`, and no member of `I` straddles a gap. The proof is that of
`hagopian76_T15_T17_cond4`, with the two clauses passed on (and `e = x₂` by
`layerSet_Icc_zero_inj`). -/
theorem hagopian76_T15_T17_cond5 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) :
    ∃ cU > 0, cU ≤ 1 ∧ ∀ {c₁ : ℝ} {D' : Set (ℝ × ℝ)} {r₂ s₂ : ℝ} {I₂ : Set Pt} {t₀ w₂ : ℝ},
      c₁ ≤ c → c₁ ≤ cU → IsCrossRegion M π F c₁ D' → IsPreconnected D' →
      (∃ c' > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c') 0)) (π '' M)) →
      TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
        (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) →
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
        (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)} →
      I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁) → IsOpen D' →
      frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∪
        Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
        ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂ →
      frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂) →
      Disjoint I₂ (π '' M) →
      3 / 22 + 2 / (n : ℝ) ≤ t₀ → t₀ ≤ 19 / 22 - 2 / (n : ℝ) → w₂ ∈ Ioc 0 c₁ → F (t₀, w₂) ∈ I₂ →
      Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) →
      ({t₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D' →
      ∀ (K₀ : Set M) {ε₃ : ℝ}, 0 < ε₃ →
      ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧
        (∃ x₀ : E, (k x₀ : ℝ) = t₀ ∧ D.p = D.h x₀ ∧ D.h (x₀ : M) ∉ Jones.composant (x₀ : M) ∧
          D.h₁ (x₀ : M) ∉ Jones.composant (x₀ : M)) ∧
        ∀ lo hi : ℝ, lo < t₀ → t₀ < hi →
        InnerComponentsCross D.G π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ lo hi →
        (∀ (x : ℕ → unitInterval) (m : ℕ), 2 ≤ m → StrictMonoOn x (Icc 1 (2 * m)) →
          x 1 = 0 → layerSet D.d (Icc 0 (x 2)) = E →
          (∀ r ∈ crossingIntervals D.d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ m ∧
            x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) →
          x (2 * m) = 1 →
          (∀ i, 1 ≤ i → i ≤ m → ∀ t ∈ Icc (x (2 * i - 1)) (x (2 * i)),
            t ≤ x 2 ∨ ∃ r ∈ crossingIntervals D.d π F c₁ D', t ∈ Icc r.1 r.2) →
          (∀ i, 1 ≤ i → i < m → ∀ r ∈ crossingIntervals D.d π F c₁ D',
            r.2 ≤ x (2 * i) ∨ x (2 * i + 1) ≤ r.1) → Property4Step D x m) → False := by
  obtain ⟨cx, hcx, hcx1, hx2n⟩ := hagopian76_x2n_eq_one_unif hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1
  obtain ⟨cb, hcb, -, hblk⟩ := exists_blocks_uncond hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨min cx cb, lt_min hcx hcb, (min_le_left _ _).trans hcx1, ?_⟩
  intro c₁ D' r₂ s₂ I₂ t₀ w₂ hc₁ hcU hR hD'c hbelow hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw
    hseg hsub K₀ ε₃ hε₃
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  obtain ⟨D, hDK, hcomp, hSBC⟩ := sep_by_crossing_uncond_comp hX hi hE hπ hπS hγπ hF hS hn hc₁ hR hD'c hbelow
    hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw hseg hsub K₀ hε₃
  refine ⟨D, hDK, hcomp, fun lo hi' hlo hhi hICC hstep => ?_⟩
  have hSBC := hSBC lo hi' hlo hhi hICC
  -- `F ≠ E`: `E` separates nothing
  obtain ⟨e, -, hEe, -⟩ := hagopian76_J_xs hX hi hE hπ.continuous hγπ hF D.hG D.hEG D.hX0 hc1 hR
  have hne : D.G ≠ E := by
    intro hGE
    have hsep := D.sep
    rw [show toPt D.G = toPt (layerSet D.d (Icc 0 e)) by rw [hEe, hGE]] at hsep
    exact hagopian76_property4_base hπ hπS hγπ hF hc1 hR hD'c hEe _ _ hsep
  have hlast := hx2n D.G D.d D.hG D.hEG D.hX0 hne (π ⁻¹' (F '' D')) D.p (D.f D.p) D.sep D.irr
    c₁ D' (hcU.trans (min_le_left _ _)) hR hSBC
  obtain ⟨e', -, he'E, x, m, hm, hx, hx1, hx2, hblocks, hxn, hcov, hgap⟩ :=
    hblk D.G D.d D.hG D.hEG D.hX0 c₁ D' (hcU.trans (min_le_right _ _)) hR hlast
  obtain ⟨hYk, hYc, hYO, hfr⟩ := pi_preimage_frontier_D_aux hE hπ hπS hF (by norm_num)
    (by norm_num) (by norm_num) hc1 hI hIR hR.isOpen hFDf
  exact hagopian76_T15_T17_cond_fix hX hi hπ hπS hγπ hF hc1 hR hD'c D hYk hYc hYO hfr hSBC x m
    hm hx hx1 hx2 hblocks hxn (hstep x m hm hx hx1 hx2 hblocks hxn
      (by rw [← layerSet_Icc_zero_inj D.hG.2.1.2.1 (he'E.trans hx2.symm)]; exact hcov) hgap)

/-- **`exists_thm1Setup` with tight blocks** (batch 182): as `exists_thm1Setup`, with the induction
step asked only for tight block sequences. The proof is that of `exists_thm1Setup`, through
`hagopian76_T15_T17_cond5`. -/
theorem exists_thm1Setup_tight (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {A : Set M}
    (hA : Fold.Q78.IsContinuum A) (hAd : ¬ Fold.Q78.IsIndecomposable A) :
    ∃ S : Thm1Setup M,
      (InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) →
      (∀ x m, S.IsTightBlocks x m → Property4Step S.D x m) → False) := by
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
  obtain ⟨cU, hcU, -, hmain⟩ := hagopian76_T15_T17_cond5 hX hi hE he hend hπ hπS hγπ hF hLch
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
    (fun x m hm hx hx1 hx2 hbl hxn hcov hgap => hstep x m ⟨⟨hm, hx, hx1, hx2, hbl, hxn⟩, hcov, hgap⟩)


end Tight

/-- **Theorem 1 from saturation and the step for tight block sequences** (batch 182): as
`hagopian76_theorem1_of_step`, with the step asked only for `S.IsTightBlocks x m`. -/
theorem hagopian76_theorem1_of_step_tight
    (hICC : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M),
      InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)))
    (hstep : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M) x m,
      S.IsTightBlocks x m → Property4Step S.D x m) :
    Hagopian76Thm1 := by
  intro M _ _ hX hi K _ hK
  by_contra hKi
  obtain ⟨S, hS⟩ := exists_thm1Setup_tight hX hi hK hKi
  exact hS (hICC M S) (hstep M S)

end HPC.Hagopian
