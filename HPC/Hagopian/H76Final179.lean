import HPC.Hagopian.H76PieceB
import HPC.Hagopian.H76Uniform2

/-!
# Batch 179, §3 and §5: `SepByCrossing` from saturation alone; the blocks; T15–T17 with
# `InnerComponentsCross` and the step as the only open inputs

* `sep_by_crossing_uncond`: in Hagopian's set-up, with `I₂ ∩ π[M] = ∅` (T7), `D′` connected and the
  low vertical inside `D′`, there is a `T12Data` package for which `InnerComponentsCross` (on an
  interval around `t₀`) gives `SepByCrossing` for `p`, `f(p)`. 4.B is discharged
  (`p_on_crossing_piece`).
* `exists_blocks_uncond`: the blocks, with `e`, the finiteness and the nondegeneracy of `I`
  discharged (uniform height); only `x₂ₙ = 1` is a hypothesis.
* `hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`: `x₂ₙ = 1` and Property 4 for the
  top block, conditional on `InnerComponentsCross` only.
* `hagopian76_T15_T17_cond3`: the contradiction of T15–T17 from `InnerComponentsCross` and
  `Property4Step`; everything else (the package, `SepByCrossing`, `x₂ₙ = 1`, the blocks, `Y`) is
  built inside, with the heights chosen before `D` (§4).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Final179

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§3.3: `SepByCrossing` for `(F, p, f(p))`, from saturation alone.** In the set-up of
`strand_misses_F_of_composant`, with `I₂ ∩ π[M] = ∅` (T7), `D′` connected and the low vertical
`{t₀} × (0, w₂)` inside `D′`: there is a `T12Data` package `D` such that `InnerComponentsCross` for
`F = D.G` on any interval `(lo, hi) ∋ t₀` gives `SepByCrossing D.G … p f(p)`.

*Proof:* `p_on_crossing_piece` (4.B) and `sep_by_crossing` (batch 178); the frame hypotheses from
`lowFrame_hyps` and `injOn_pi_preimage`. -/
theorem sep_by_crossing_uncond (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (hD'c : IsPreconnected D')
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
    (hsub : ({t₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D')
    (K₀ : Set M) {ε₃ : ℝ} (hε₃ : 0 < ε₃) :
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧
      ∀ lo hi : ℝ, lo < t₀ → t₀ < hi →
        InnerComponentsCross D.G π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ lo hi →
        SepByCrossing D.G π F c₁ D' (π ⁻¹' (F '' D')) D.p (D.f D.p) := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hn0 : (0 : ℝ) < 2 / (n : ℝ) := by
    have : (15 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  obtain ⟨D, hDK, X, Y, hX', hY', hpX, hqY, hXY, hXG, hYG⟩ := p_on_crossing_piece hX hi hE hπ hπS
    hγπ hF hS hn hc₁ hR hbelow hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw hseg K₀ hε₃
  refine ⟨D, hDK, fun lo hi hlo hhi hICC => ?_⟩
  have hdisj : Disjoint (π ⁻¹' (F '' D')) (toPt E) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨m, hmE, rfl⟩
    exact Set.disjoint_left.1 (crossSet_disjoint_E hγπ hF hc1 hR.sub E) ⟨hmE, hx⟩ hmE
  have hD'R : D' ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun z hz =>
    ⟨⟨by linarith [(hR.sub hz).1.1], by linarith [(hR.sub hz).1.2]⟩,
      by linarith [(hR.sub hz).2.1], by linarith [(hR.sub hz).2.2]⟩
  obtain ⟨hOc, hsegc⟩ := lowFrame_hyps hE hπ hπS hF hD'R hD'c hR.isOpen hdisj hsub
  have hπinj : InjOn π (π ⁻¹' (F '' D')) := injOn_pi_preimage hπS hγπ hF fun d hd => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hR.sub hd
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, h3⟩
  exact sep_by_crossing hπ.continuous hF hc1 hI hIs hDo hR.sub hDf
    ⟨by linarith, by linarith⟩ hw₂ hFw hseg (hR.isOpen.preimage hπ.continuous) hOc hsub hπinj
    hπ.surjective hsegc D.hG.isCompact.isClosed hlo hhi hICC hX' hY' hXY hXG hYG hpX hqY

/-- **§3.4: the blocks, without the batch-178 conditions** (uniform height). There is `c > 0`
such that for every extension `G` of `E` away from `k⁻¹(0)` and every domain of height `c₁ ≤ c`:
if some member of `I` ends at `1` (`x₂ₙ = 1`), the blocks of `St J` exist with the clauses of
`exists_blocks`. `e` comes from `hagopian76_J_xs`, finiteness from `hagopian76_I_finite_unif`, and
nondegeneracy from `crossingIntervals_nondegenerate` (Property 3 as printed). -/
theorem exists_blocks_uncond (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c →
      IsCrossRegion M π F c₁ D' → LastIntervalReachesOne d π F c₁ D' →
      ∃ e : unitInterval, 0 < e ∧ layerSet d (Icc 0 e) = E ∧
      ∃ (x : ℕ → unitInterval) (n : ℕ), 2 ≤ n ∧ StrictMonoOn x (Icc 1 (2 * n)) ∧ x 1 = 0 ∧
        layerSet d (Icc 0 (x 2)) = E ∧
        (∀ r ∈ crossingIntervals d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ n ∧
          x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) ∧
        x (2 * n) = 1 ∧
        (∀ i, 1 ≤ i → i ≤ n → ∀ t ∈ Icc (x (2 * i - 1)) (x (2 * i)),
          t ≤ e ∨ ∃ r ∈ crossingIntervals d π F c₁ D', t ∈ Icc r.1 r.2) ∧
        (∀ i, 1 ≤ i → i < n → ∀ r ∈ crossingIntervals d π F c₁ D',
          r.2 ≤ x (2 * i) ∨ x (2 * i + 1) ≤ r.1) := by
  obtain ⟨c, hc, hc1, hfin⟩ := hagopian76_I_finite_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL
    hLG hP1
  obtain ⟨c', hc', -, hnd⟩ := crossingIntervals_nondegenerate hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1
  refine ⟨min c c', lt_min hc hc', (min_le_left _ _).trans hc1,
    fun G d hG hEG hX0 c₁ D' hc₁ hR hlast => ?_⟩
  have hcc : c₁ ≤ c := hc₁.trans (min_le_left _ _)
  have hcc' : c₁ ≤ c' := hc₁.trans (min_le_right _ _)
  obtain ⟨e, he0, hEe, hlt⟩ := hagopian76_J_xs hX hi hE hπ.continuous hγπ hF hG hEG hX0
    (hcc.trans hc1) hR
  exact ⟨e, he0, hEe, exists_blocks he0 hEe hlt (hfin G d hG hEG hX0 c₁ D' hcc hR)
    (hnd G d hG hEG hX0 c₁ D' hcc' hR) hlast⟩

/-- **§5: T15–T17 with saturation and the step as the only open inputs.** Set-up of Property 3
(`hagopian76_property3`) and the strand constants. There is a height `cU > 0` (chosen before `D`,
§4) such that for every domain `D = F[D′]` of height `c₁ ≤ min c cU` with Hagopian's hypotheses
(T7's `I₂ ∩ π[M] = ∅`, `D′` connected, the low vertical over `t₀` in `D′`), there is a `T12Data`
package `D` with: if `InnerComponentsCross` holds for `F = D.G` on an interval around `t₀`, and the
induction step `Property4Step D x m` holds for every block sequence `x` of `St J` (the clauses of
`hagopian76_T15_T17_cond2`), then `False`.

Built inside: the package and 4.B (`p_on_crossing_piece`), `SepByCrossing`
(`sep_by_crossing_uncond`), `F ≠ E` (`hagopian76_property4_base`), `x₂ₙ = 1`
(`hagopian76_x2n_eq_one_unif`), the blocks (`exists_blocks`, with `e`, finiteness and
nondegeneracy), `Y = π⁻¹[Fr D]`, and the closing argument `hagopian76_T15_T17_cond_fix`. -/
theorem hagopian76_T15_T17_cond3 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
        ∀ lo hi : ℝ, lo < t₀ → t₀ < hi →
        InnerComponentsCross D.G π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ lo hi →
        (∀ (x : ℕ → unitInterval) (m : ℕ), 2 ≤ m → StrictMonoOn x (Icc 1 (2 * m)) →
          x 1 = 0 → layerSet D.d (Icc 0 (x 2)) = E →
          (∀ r ∈ crossingIntervals D.d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ m ∧
            x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) →
          x (2 * m) = 1 → Property4Step D x m) → False := by
  obtain ⟨cx, hcx, hcx1, hx2n⟩ := hagopian76_x2n_eq_one_unif hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1
  obtain ⟨cb, hcb, -, hblk⟩ := exists_blocks_uncond hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨min cx cb, lt_min hcx hcb, (min_le_left _ _).trans hcx1, ?_⟩
  intro c₁ D' r₂ s₂ I₂ t₀ w₂ hc₁ hcU hR hD'c hbelow hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw
    hseg hsub K₀ ε₃ hε₃
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  obtain ⟨D, hDK, hSBC⟩ := sep_by_crossing_uncond hX hi hE hπ hπS hγπ hF hS hn hc₁ hR hD'c hbelow
    hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw hseg hsub K₀ hε₃
  refine ⟨D, hDK, fun lo hi' hlo hhi hICC hstep => ?_⟩
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
  obtain ⟨-, -, -, x, m, hm, hx, hx1, hx2, hblocks, hxn, -, -⟩ :=
    hblk D.G D.d D.hG D.hEG D.hX0 c₁ D' (hcU.trans (min_le_right _ _)) hR hlast
  obtain ⟨hYk, hYc, hYO, hfr⟩ := pi_preimage_frontier_D_aux hE hπ hπS hF (by norm_num)
    (by norm_num) (by norm_num) hc1 hI hIR hR.isOpen hFDf
  exact hagopian76_T15_T17_cond_fix hX hi hπ hπS hγπ hF hc1 hR hD'c D hYk hYc hYO hfr hSBC x m
    hm hx hx1 hx2 hblocks hxn (hstep x m hm hx hx1 hx2 hblocks hxn)

/-- **§3.3: "Note that `x₂ₙ = 1`" (p. 348), conditional on saturation only.** Set-up and heights as
in `hagopian76_T15_T17_cond3`: there is a `T12Data` package `D` such that `InnerComponentsCross`
for `F = D.G` on an interval around `t₀` gives `LastIntervalReachesOne` (some member of `I` ends at
`1`). -/
theorem hagopian76_x2n_eq_one_final (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
        ∀ lo hi : ℝ, lo < t₀ → t₀ < hi →
        InnerComponentsCross D.G π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ lo hi →
        LastIntervalReachesOne D.d π F c₁ D' := by
  obtain ⟨cx, hcx, hcx1, hx2n⟩ := hagopian76_x2n_eq_one_unif hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1
  obtain ⟨cb, hcb, -, hblk⟩ := exists_blocks_uncond hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨min cx cb, lt_min hcx hcb, (min_le_left _ _).trans hcx1, ?_⟩
  intro c₁ D' r₂ s₂ I₂ t₀ w₂ hc₁ hcU hR hD'c hbelow hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw
    hseg hsub K₀ ε₃ hε₃
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  obtain ⟨D, hDK, hSBC⟩ := sep_by_crossing_uncond hX hi hE hπ hπS hγπ hF hS hn hc₁ hR hD'c hbelow
    hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw hseg hsub K₀ hε₃
  refine ⟨D, hDK, fun lo hi' hlo hhi hICC => ?_⟩
  have hSBC := hSBC lo hi' hlo hhi hICC
  obtain ⟨e, -, hEe, -⟩ := hagopian76_J_xs hX hi hE hπ.continuous hγπ hF D.hG D.hEG D.hX0 hc1 hR
  have hne : D.G ≠ E := by
    intro hGE
    have hsep := D.sep
    rw [show toPt D.G = toPt (layerSet D.d (Icc 0 e)) by rw [hEe, hGE]] at hsep
    exact hagopian76_property4_base hπ hπS hγπ hF hc1 hR hD'c hEe _ _ hsep
  have hlast := hx2n D.G D.d D.hG D.hEG D.hX0 hne (π ⁻¹' (F '' D')) D.p (D.f D.p) D.sep D.irr
    c₁ D' (hcU.trans (min_le_left _ _)) hR hSBC
  exact hlast

/-- **§3.3: Property 4 for the top block (p. 348), conditional on saturation only.** Set-up and
heights as in `hagopian76_T15_T17_cond3`: there is a `T12Data` package `D` such that
`InnerComponentsCross` for `F = D.G` on an interval around `t₀` gives the blocks `x₁ < ⋯ < x₂ₘ` of
`St J` (with the clauses of `hagopian76_T15_T17_cond2`) and Property 4 for `[x₂ₘ₋₁, x₂ₘ]`. -/
theorem hagopian76_property4_top_final (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
        ∀ lo hi : ℝ, lo < t₀ → t₀ < hi →
        InnerComponentsCross D.G π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ lo hi →
        ∃ (x : ℕ → unitInterval) (m : ℕ), 2 ≤ m ∧ StrictMonoOn x (Icc 1 (2 * m)) ∧ x 1 = 0 ∧
          layerSet D.d (Icc 0 (x 2)) = E ∧
          (∀ r ∈ crossingIntervals D.d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ m ∧
            x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) ∧
          x (2 * m) = 1 ∧ Property4 D (x (2 * m - 1)) (x (2 * m)) := by
  obtain ⟨cx, hcx, hcx1, hx2n⟩ := hagopian76_x2n_eq_one_unif hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1
  obtain ⟨cb, hcb, -, hblk⟩ := exists_blocks_uncond hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨min cx cb, lt_min hcx hcb, (min_le_left _ _).trans hcx1, ?_⟩
  intro c₁ D' r₂ s₂ I₂ t₀ w₂ hc₁ hcU hR hD'c hbelow hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw
    hseg hsub K₀ ε₃ hε₃
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  obtain ⟨D, hDK, hSBC⟩ := sep_by_crossing_uncond hX hi hE hπ hπS hγπ hF hS hn hc₁ hR hD'c hbelow
    hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw hseg hsub K₀ hε₃
  refine ⟨D, hDK, fun lo hi' hlo hhi hICC => ?_⟩
  have hSBC := hSBC lo hi' hlo hhi hICC
  obtain ⟨e, -, hEe, -⟩ := hagopian76_J_xs hX hi hE hπ.continuous hγπ hF D.hG D.hEG D.hX0 hc1 hR
  have hne : D.G ≠ E := by
    intro hGE
    have hsep := D.sep
    rw [show toPt D.G = toPt (layerSet D.d (Icc 0 e)) by rw [hEe, hGE]] at hsep
    exact hagopian76_property4_base hπ hπS hγπ hF hc1 hR hD'c hEe _ _ hsep
  have hlast := hx2n D.G D.d D.hG D.hEG D.hX0 hne (π ⁻¹' (F '' D')) D.p (D.f D.p) D.sep D.irr
    c₁ D' (hcU.trans (min_le_left _ _)) hR hSBC
  obtain ⟨-, -, -, x, m, hm, hx, hx1, hx2, hblocks, hxn, -, -⟩ :=
    hblk D.G D.d D.hG D.hEG D.hX0 c₁ D' (hcU.trans (min_le_right _ _)) hR hlast
  obtain ⟨hYk, hYc, hYO, hfr⟩ := pi_preimage_frontier_D_aux hE hπ hπS hF (by norm_num)
    (by norm_num) (by norm_num) hc1 hI hIR hR.isOpen hFDf
  have hlt : ∀ i j, 1 ≤ i → i < j → j ≤ 2 * m → x i < x j := fun i j hi hij hj =>
    hx ⟨hi, by omega⟩ ⟨by omega, hj⟩ hij
  have hle : ∀ i j, 1 ≤ i → i ≤ j → j ≤ 2 * m → x i ≤ x j := fun i j hi hij hj => by
    rcases eq_or_lt_of_le hij with rfl | h
    · exact le_rfl
    · exact (hlt i j hi h hj).le
  have h0 : 0 < x (2 * m - 2) := by
    rw [← hx1]; exact hlt 1 _ le_rfl (by omega) (by omega)
  have h12 : x (2 * m - 2) < x (2 * m - 1) := hlt _ _ (by omega) (by omega) (by omega)
  have hEs : E ⊆ layerSet D.d (Icc 0 (x (2 * m - 2))) :=
    hx2.symm.subset.trans (layerSet_mono D.d (Icc_subset_Icc le_rfl
      (hle 2 _ (by omega) (by omega) (by omega))))
  have hgap : ∀ r ∈ crossingIntervals D.d π F c₁ D',
      r.2 ≤ x (2 * m - 2) ∨ x (2 * m - 1) ≤ r.1 := by
    intro r hr
    obtain ⟨i, hi1, hin, h1, h2⟩ := hblocks r hr
    rcases lt_or_eq_of_le hin with hlt' | rfl
    · exact Or.inl (h2.trans (hle _ _ (by omega) (by omega) (by omega)))
    · exact Or.inr h1
  have htop := hagopian76_property4_top hX hi D hYk hYc hYO hfr hSBC h0 h12 hEs hgap
  exact ⟨x, m, hm, hx, hx1, hx2, hblocks, hxn, by rw [hxn]; exact htop⟩

end Final179

end HPC.Hagopian
