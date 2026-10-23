import HPC.Hagopian.H76IFinite

/-!
# Batch 174, item C: the point `e`, and `x₂ = e`

Hagopian 1976, pp. 347–348: "Let `e` be the point of `[0, 1]` such that `d⁻¹[[0, e]] = E`. Let
`J = I ∪ {[0, e]}`. Define `{xᵢ : 1 ≤ i ≤ 2n}` to be the finite increasing sequence in `[0, 1]`
such that `St J = ⋃{[x₂ᵢ₋₁, x₂ᵢ] : i ≤ n}`. Note that `x₁ = 0`, `x₂ = e`, and `x₂ₙ = 1`."

* `crossSet_disjoint_E`: no point of `E` lies over `D` (a point of `E` lies over the axis).
* `hagopian76_J_xs`: `e` exists, and every interval `[x, y]` of `I` has `e < x`. So `[0, e]` is a
  block of `St J` by itself: `x₁ = 0` and `x₂ = e`.

`x₂ₙ = 1` (some interval of `I` ends at `1`) is not proved; see `LastIntervalReachesOne` in
`Hagopian76S.lean` and `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section JXs

variable {M : Set Pt}

/-- **No point of `E` lies over Hagopian's domain** `D = F[D′]` (`D′` in the open strip of positive
heights): a point of `E` lies over the axis `F[[0, 1] × {0}]`, and `F` is injective on the
rectangle. -/
theorem crossSet_disjoint_E {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)}
    (hD : D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c₁) (G : Set M) :
    Disjoint (crossSet G π F D') E := by
  rw [Set.disjoint_left]
  rintro m ⟨-, ⟨a, b⟩, hab, hFab⟩ hmE
  have hπm := pi_E_eq hγπ hF ⟨m, hmE⟩
  obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hD hab
  have := collar_injOn hF (z := (a, b)) (w := ((k ⟨m, hmE⟩ : ℝ), 0))
    ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    ⟨⟨(k ⟨m, hmE⟩).2.1, (k ⟨m, hmE⟩).2.2⟩, by norm_num, by norm_num⟩ (hFab.trans hπm)
  have hb0 : b = 0 := congrArg Prod.snd this
  linarith

variable [CompactSpace M] [ConnectedSpace M]

/-- **C. `e`, and `x₂ = e`** (pp. 347–348). For an extension `G` of `E` away from `k⁻¹(0)` (Hagopian's
`F`) and a domain `D = F[D′]` in the open strip `(3/22, 19/22) × (0, c₁)`: there is `e > 0` with
`d⁻¹[[0, e]] = E`, and every interval `[x, y]` of Hagopian's `I` has `e < x`.

*Shape (left to me):* the sequence `xᵢ` is not constructed; the statement gives what "Note that
`x₁ = 0`, `x₂ = e`" needs: `[0, e]` is disjoint from every member of `I`, so `[0, e]` is a block of
`St J` (`x₁ = 0`, `x₂ = e`). The strict inequality answers the commission's question "Is `x > e`
needed, and true?": it is true, and it is what keeps `[0, e]` from merging with a block of `I`.

*Proof:* if `G = E`, then `e = 1` and `I` is empty (no point of `E` lies over `D`,
`crossSet_disjoint_E`). Otherwise `ext_layers` gives `e < 1` with `d⁻¹[[0, e]] = E` and
`d⁻¹(e) = k⁻¹(1)`. A crossing component `C` misses `E`, so `C ⊆ d⁻¹((e, 1])` and, by irreducibility,
`e ≤ x`. If `x = e`, the closure of `C` meets `d⁻¹(e) = k⁻¹(1)`, which lies over `F(1, 0)`; but the
closure of `C` lies over `Cl D ⊆ F[[3/22, 19/22] × [0, c₁]]`, which misses `F(1, 0)`. -/
theorem J_xs_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    (hπc : Continuous π) {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G) (hX0 : layer d 0 = layer k 0) {c₁ : ℝ}
    (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hD : D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c₁) :
    ∃ e : unitInterval, 0 < e ∧ layerSet d (Icc 0 e) = E ∧
      ∀ p ∈ crossingIntervals d π F c₁ D', e < p.1 := by
  have hdisj := crossSet_disjoint_E hγπ hF hc₁ hD G
  by_cases hGE : G = E
  · subst hGE
    refine ⟨1, by norm_num [← Subtype.coe_lt_coe], ?_, ?_⟩
    · ext m
      constructor
      · rintro ⟨w, -, rfl⟩; exact w.2
      · intro hm; exact ⟨⟨m, hm⟩, ⟨unitInterval.nonneg', unitInterval.le_one'⟩, rfl⟩
    · rintro p ⟨C, ⟨⟨z, hz, -⟩, -, -⟩, -⟩
      exact absurd hz.1 (Set.disjoint_left.1 hdisj hz)
  obtain ⟨e, he0, -, he, hseg, -, -⟩ := ext_layers hX hi hE hG hEG hX0 hGE
  refine ⟨e, he0, hseg, fun p ⟨C, hC, hI⟩ => ?_⟩
  have hCG : C ⊆ G := fun m hm => (hC.subset hm).1
  /- `e ≤ x`. -/
  have hle : e ≤ p.1 := by
    have hsub : C ⊆ layerSet d (Icc (max p.1 e) p.2) := by
      intro m hm
      obtain ⟨w, hw, rfl⟩ := hI.1 hm
      refine ⟨w, ⟨max_le hw.1 ?_, hw.2⟩, rfl⟩
      by_contra hlt
      push_neg at hlt
      have hwE : (w : M) ∈ E := hseg ▸ ⟨w, ⟨unitInterval.nonneg', hlt.le⟩, rfl⟩
      exact Set.disjoint_left.1 hdisj (hC.subset hm) hwE
    exact (le_max_right _ _).trans (hI.2 _ _ hsub).1
  refine lt_of_le_of_ne hle fun heq => ?_
  /- `x = e` is impossible. -/
  obtain ⟨⟨w, hwcl, hwl⟩, -⟩ := hI.closure_meets hG hCG hC.isConnected.nonempty
  rw [← heq, he] at hwl
  obtain ⟨e', he'1, rfl⟩ := hwl
  have hπw := pi_E_eq hγπ hF e'
  rw [show k e' = 1 from he'1] at hπw
  have hR : Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    rect_sub (by norm_num) (by norm_num) hc₁
  have hK : IsClosed (F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁)) :=
    (isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc) hR).isClosed
  have hDK : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono (hD.trans (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
  have hWc : IsClosed {m : M | π (m : Pt) ∈ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁)} :=
    hK.preimage (hπc.comp continuous_subtype_val)
  have hwK : π ((e' : M) : Pt) ∈ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    (closure_minimal (s := C)
      (t := {m : M | π (m : Pt) ∈ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁)})
      (fun m hm => hDK (hC.subset hm).2) hWc) hwcl
  obtain ⟨⟨a, b⟩, hab, hFab⟩ := hwK
  have := collar_injOn hF (z := (a, b)) (w := (((1 : unitInterval) : ℝ), 0)) (hR hab)
    ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩ (hFab.trans hπw)
  have ha : a = 1 := congrArg Prod.fst this
  linarith [hab.1.2]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **D, base case: "Note that `[x₁, x₂]` does not have Property 4"** (p. 348). For any `e` with
`d⁻¹[[0, e]] = E` (`hagopian76_J_xs`), the block `d⁻¹[[x₁, x₂]] = d⁻¹[[0, e]] = E` separates no point
from any other in `π⁻¹[D]`: `E` misses `π⁻¹[D]` (`crossSet_disjoint_E`), and `π⁻¹[D]` is connected
(`isPreconnected_preimage_off`, since `π` is injective off `E` and `D = F[D′]` is connected). So
clause (2) of Property 4 fails for every `y`.

*Shape (left to me):* the connectedness of `D′` is a hypothesis; for Hagopian's domain it is
`rect_frontier_domain` (batch 172). Only clause (2) of Property 4 is involved. -/
theorem property4_base_aux {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)}
    (hR : IsCrossRegion M π F c₁ D') (hD'c : IsPreconnected D')
    {G : Set M} {d : G → unitInterval} {e : unitInterval} (he : layerSet d (Icc 0 e) = E)
    (y z : Pt) : ¬ SepIn (π ⁻¹' (F '' D')) (toPt (layerSet d (Icc 0 e))) y z := by
  rintro ⟨hy, hz, hsep⟩
  rw [he] at hy hz hsep
  have hdisj : Disjoint (π ⁻¹' (F '' D')) (toPt E) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨m, hmE, rfl⟩
    exact Set.disjoint_left.1 (crossSet_disjoint_E hγπ hF hc₁ hR.sub E) ⟨hmE, hx⟩ hmE
  have hD'R : D' ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun w hw => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hR.sub hw
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hFc : IsPreconnected (F '' D') :=
    hD'c.image F ((continuousOn_iff_continuous_restrict.2 hF.1.continuous).mono hD'R)
  have hpre := isPreconnected_preimage_off hπ hπS hR.isOpen hFc hdisj
  exact hsep _ hpre (fun x hx => ⟨hx, Set.disjoint_left.1 hdisj hx⟩) hy.1 hz.1

end JXs

end HPC.Hagopian
