import HPC.Hagopian.Hagopian76R

/-!
# Batch 174, item A: Property 3 at the end element `d⁻¹(1)` (supporting file)

Commission 174 §1.6. The end layer `d⁻¹(1)` of an extension `G` of `E` away from `k⁻¹(0)` is an
interior layer of a proper extension `G′ ⊋ G` (Lemma 4, `exists_proper_extension`): by the strong
form (`ext_layers`), `d⁻¹(1) = d′⁻¹(s′)` with `s′ < 1`. Since `G′` is again an extension of `E` away
from `k⁻¹(0)`, Property 3 for `G′` (`property3_layer_aux`, `hagopian76_property3`) excludes a
crossing in `d⁻¹(1)`.

* `exists_end_extension`: the proper extension, with `d⁻¹(1)` as an interior layer.
* `layerCrossing_congr`: `LayerCrossing` depends only on the layer as a set.
* `property3_layer_all`: no layer `d⁻¹(v)`, `v ∈ [0, 1]`, contains a layer crossing.
* `crossing_length_pos_of_forall`, `crossing_length_pos_all`: the length bound of batch 173 with the
  restriction `y ≤ v₀ < 1` removed.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section EndElement

variable {M : Set Pt}

/-- A layer crossing depends only on the layer, as a subset of `M`. -/
theorem layerCrossing_congr {G G' : Set M} {d : G → unitInterval} {d' : G' → unitInterval}
    {π : Pt → Pt} {F : ℝ × ℝ → Pt} {c₁ : ℝ} {D' : Set (ℝ × ℝ)} {u u' : unitInterval}
    (h : layer d u = layer d' u') :
    LayerCrossing d π F c₁ D' u ↔ LayerCrossing d' π F c₁ D' u' := by
  unfold LayerCrossing; rw [h]

variable [CompactSpace M] [ConnectedSpace M]

/-- **The end element is an interior layer of a proper extension** (commission 174 §1.6). For an
extension `G` of `E` away from `k⁻¹(0)`, there is an extension `G′ ⊋ G` of `E` away from `k⁻¹(0)`
(Lemma 4) and `s′ < 1` with `d′⁻¹(s′) = d⁻¹(1)` (the strong form, `ext_layers`). -/
theorem exists_end_extension (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G) (hX0 : layer d 0 = layer k 0) :
    ∃ (G' : Set M) (d' : G' → unitInterval), IsMinimalAdmissible G' d' ∧ G ⊂ G' ∧ E ⊆ G' ∧
      layer d' 0 = layer k 0 ∧ ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ layer d' s = layer d 1 ∧
        layerSet d' (Icc 0 s) = G := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  obtain ⟨G', hGG', d', hd', hd'0⟩ := exists_proper_extension hX hHU hAT hG
  obtain ⟨s, hs0, hs1, hs, hseg, -⟩ := ext_layers hX hi hG hd' hGG'.1 hd'0 hGG'.ne.symm
  exact ⟨G', d', hd', hGG', hEG.trans hGG'.1, hd'0.trans hX0, s, hs0, hs1, hs, hseg⟩

/-- **Property 3 for every layer, the end element included** (commission 174 §1.6, in the
layer-crossing form). Set-up of `property3_layer_aux`. There is `c > 0` such that for every domain
`D = F[D′]` of height `c₁ ≤ c` no layer `d⁻¹(v)`, `v ∈ [0, 1]`, contains a layer crossing.

*Proof:* for `v < 1`, `property3_layer_aux`; for `v = 1`, `property3_layer_aux` for the proper
extension `G′` of `exists_end_extension`, at its interior layer `d′⁻¹(s′) = d⁻¹(1)`. -/
theorem property3_layer_all (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ v : unitInterval, ¬ LayerCrossing d π F c₁ D' v := by
  obtain ⟨c, hc, hc1, hP⟩ := property3_layer_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
    hG hEG hX0
  obtain ⟨G', d', hG', -, hEG', hX0', s, -, hs1, hs, -⟩ := exists_end_extension hX hi hG hEG hX0
  obtain ⟨c', hc', -, hP'⟩ := property3_layer_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
    hG' hEG' hX0'
  refine ⟨min c c', lt_min hc hc', (min_le_left _ _).trans hc1, fun c₁ D' hc₁ hR v => ?_⟩
  rcases lt_or_eq_of_le (unitInterval.le_one' : v ≤ 1) with hv | rfl
  · exact hP c₁ D' (hc₁.trans (min_le_left _ _)) hR v hv
  · rw [layerCrossing_congr hs.symm]
    exact hP' c₁ D' (hc₁.trans (min_le_right _ _)) hR s hs1

/-- **A. Property 3 for the end element** (commission 174 §1.6; p. 347, "no element of the
decomposition of `F`"), in the thin-strip form of `hagopian76_property3`, now for **every** layer
`d⁻¹(v)`, `v ∈ [0, 1]`: there is `c > 0` such that no connected `B` over
`F[[3/22, 19/22] × (0, c]]` whose closure meets both open side edges has its closure in a layer of
`G`.

*Proof:* `hagopian76_property3` for `G` (layers `v < 1`) and for the proper extension `G′` of
`exists_end_extension` (the layer `d′⁻¹(s′) = d⁻¹(1)`, `s′ < 1`); the smaller of the two heights. -/
theorem property3_end_element_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, ¬ closure B ⊆ layer d v := by
  obtain ⟨c, hc, hc1, hP⟩ := hagopian76_property3 hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
    hG hEG hX0
  obtain ⟨G', d', hG', -, hEG', hX0', s, -, hs1, hs, -⟩ := exists_end_extension hX hi hG hEG hX0
  obtain ⟨c', hc', -, hP'⟩ := hagopian76_property3 hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
    hG' hEG' hX0'
  have hmono : ∀ {a b : ℝ} (S : Set ℝ), a ≤ b → F '' (S ×ˢ Ioc 0 a) ⊆ F '' (S ×ˢ Ioc 0 b) :=
    fun S hab => image_mono (Set.prod_mono le_rfl (Ioc_subset_Ioc_right hab))
  refine ⟨min c c', lt_min hc hc', (min_le_left _ _).trans hc1,
    fun B hB hin hl hr v hBv => ?_⟩
  obtain ⟨xl, hxl, hxlF⟩ := hl
  obtain ⟨xr, hxr, hxrF⟩ := hr
  rcases lt_or_eq_of_le (unitInterval.le_one' : v ≤ 1) with hv | rfl
  · exact hP B hB (fun x hx => hmono _ (min_le_left _ _) (hin x hx))
      ⟨xl, hxl, hmono _ (min_le_left _ _) hxlF⟩ ⟨xr, hxr, hmono _ (min_le_left _ _) hxrF⟩ v hv hBv
  · exact hP' B hB (fun x hx => hmono _ (min_le_right _ _) (hin x hx))
      ⟨xl, hxl, hmono _ (min_le_right _ _) hxlF⟩ ⟨xr, hxr, hmono _ (min_le_right _ _) hxrF⟩ s hs1
      (hs ▸ hBv)

omit [ConnectedSpace M] in
/-- **The length bound from Property 3 in every layer.** If no layer `d⁻¹(u)` contains a layer
crossing, there is `λ > 0` such that every connected `Z ⊆ d⁻¹[[x, y]]` over `Cl D` meeting both
closed side segments has `y − x ≥ λ`. The proof of `crossing_length_pos_aux` (an upper limit of
crossings with `y − x → 0` is a layer crossing), without the bound `y ≤ v₀`. -/
theorem crossing_length_pos_of_forall {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) {π : Pt → Pt} (hπc : Continuous π) {γ : unitInterval → Pt}
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {c₁ : ℝ} (hc₁1 : c₁ ≤ 1) {D' : Set (ℝ × ℝ)}
    (hP3 : ∀ u : unitInterval, ¬ LayerCrossing d π F c₁ D' u) :
    ∃ lam > 0, ∀ (x y : unitInterval) (Z : Set M),
      IsPreconnected Z → Z ⊆ layerSet d (Icc x y) →
      (∀ z ∈ Z, π (z : Pt) ∈ closure (F '' D')) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      lam ≤ (y : ℝ) - x := by
  by_contra hcon
  push_neg at hcon
  choose x y Z hZc hZl hZW hZa hZb hlen using fun n : ℕ => hcon (1 / ((n : ℝ) + 1))
    (by positivity)
  choose a haZ haA using hZa
  choose b hbZ hbB using hZb
  obtain ⟨⟨u, p⟩, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq
    (x := fun n => (x n, a n)) (fun _ => mem_univ _)
  have hxu : Tendsto (fun n => x (φ n)) atTop (𝓝 u) := (continuous_fst.tendsto _).comp hlim
  have hap : Tendsto (fun n => a (φ n)) atTop (𝓝 p) := (continuous_snd.tendsto _).comp hlim
  have hxy : ∀ n, x n ≤ y n := fun n => by
    obtain ⟨w, hw, -⟩ := hZl n (haZ n)
    exact hw.1.trans hw.2
  have hlen0 : Tendsto (fun n => ((y (φ n) : ℝ) - x (φ n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    refine squeeze_zero (fun n => ?_) (fun n => (hlen (φ n)).le) h1
    have := hxy (φ n)
    exact sub_nonneg.2 (Subtype.coe_le_coe.2 this)
  set Lim := ⋂ N, closure (⋃ m ≥ N, Z (φ m)) with hLim
  have hGc : IsClosed G := hG.isCompact.isClosed
  have hband : ∀ ε > 0, ∀ᶠ n in atTop, Z (φ n) ⊆ layerSet d {t | dist t u ≤ ε} := by
    intro ε hε
    have h1 := (Metric.tendsto_nhds.1 hxu) (ε / 2) (by linarith)
    have h2 := (Metric.tendsto_nhds.1 hlen0) (ε / 2) (by linarith)
    filter_upwards [h1, h2] with n hn1 hn2
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hZl _ hz
    refine ⟨w, ?_, rfl⟩
    show dist (d w) u ≤ ε
    rw [Real.dist_eq, abs_lt] at hn2
    have hd1 : dist (d w) u ≤ dist (d w) (x (φ n)) + dist (x (φ n)) u := dist_triangle _ _ _
    have hd2 : dist (d w) (x (φ n)) ≤ (y (φ n) : ℝ) - x (φ n) := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith [Subtype.coe_le_coe.2 hw.1])]
      linarith [Subtype.coe_le_coe.2 hw.2]
    linarith [hn1.le]
  have hLimL : Lim ⊆ layer d u := by
    intro z hz
    have hzG : z ∈ G := by
      refine limsup_subset_of_eventually hGc (Eventually.of_forall fun n => ?_) hz
      intro w hw
      obtain ⟨w', -, rfl⟩ := hZl _ hw
      exact w'.2
    refine ⟨⟨z, hzG⟩, ?_, rfl⟩
    refine mem_singleton_iff.2 (eq_of_forall_dist_le fun ε hε => ?_)
    have := limsup_subset_of_eventually (isCompact_img hG.isCompact hG.2.1.1
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)).isClosed
      (hband ε hε) hz
    obtain ⟨w, hw, hwz⟩ := this
    have : w = ⟨z, hzG⟩ := Subtype.ext hwz
    subst this
    exact hw
  have hA : IsClosed {m : M | π (m : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)} :=
    (isCompact_collar_image hF (isCompact_singleton.prod isCompact_Icc)
      ((Set.prod_mono (by simp) le_rfl).trans (rect_sub (a := 3 / 22) (b := 3 / 22)
        (by norm_num) (by norm_num) hc₁1))).isClosed.preimage
      (hπc.comp continuous_subtype_val)
  obtain ⟨⟨q, q'⟩, -, ψ, hψ, hlim2⟩ := isCompact_univ.tendsto_subseq
    (x := fun n => (b (φ n), a (φ n))) (fun _ => mem_univ _)
  have hbq : Tendsto (fun n => b (φ (ψ n))) atTop (𝓝 q) := (continuous_fst.tendsto _).comp hlim2
  refine hP3 u ⟨Lim, ?_, hLimL, ?_, ⟨p, ?_, ?_⟩, ⟨q, ?_, ?_⟩⟩
  · exact limsup_isPreconnected (fun n => hZc (φ n)) (fun n => haZ (φ n)) hap
  · exact fun z hz => limsup_subset_of_eventually
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))
      (Eventually.of_forall fun n => fun w hw => hZW _ w hw) hz
  · exact limsup_mem_of_tendsto (fun n => haZ (φ n)) hap
  · exact hA.mem_of_tendsto hap (Eventually.of_forall fun n => haA (φ n))
  · have hsub : ⋂ N, closure (⋃ m ≥ N, Z (φ (ψ m))) ⊆ Lim := by
      refine subset_iInter fun N => ?_
      refine (iInter_subset _ N).trans (closure_mono (iUnion₂_subset fun m hm => ?_))
      exact subset_biUnion_of_mem (u := fun i => Z (φ i)) (le_trans hm (hψ.id_le m))
    exact hsub (limsup_mem_of_tendsto (fun n => hbZ (φ (ψ n))) hbq)
  · have hB : IsClosed {m : M | π (m : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)} :=
      (isCompact_collar_image hF (isCompact_singleton.prod isCompact_Icc)
        ((Set.prod_mono (by simp) le_rfl).trans (rect_sub (a := 19 / 22) (b := 19 / 22)
          (by norm_num) (by norm_num) hc₁1))).isClosed.preimage
        (hπc.comp continuous_subtype_val)
    exact hB.mem_of_tendsto hbq (Eventually.of_forall fun n => hbB (φ (ψ n)))

/-- **Crossings need parameter length, in every layer** (`crossing_length_pos` without `y ≤ v₀ < 1`;
commission 174 §1.5–1.6). Set-up of `property3_layer_all`. There are `c > 0` and, for every domain
`D = F[D′]` of height `c₁ ≤ c`, a `λ > 0` such that every connected `Z ⊆ d⁻¹[[x, y]]` over `Cl D`
meeting both closed side segments has `y − x ≥ λ`. -/
theorem crossing_length_pos_all (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∃ lam > 0, ∀ (x y : unitInterval) (Z : Set M),
      IsPreconnected Z → Z ⊆ layerSet d (Icc x y) →
      (∀ z ∈ Z, π (z : Pt) ∈ closure (F '' D')) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      (∃ z ∈ Z, π (z : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 c₁)) →
      lam ≤ (y : ℝ) - x := by
  obtain ⟨c, hc, hc1, hP3⟩ := property3_layer_all hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
    hG hEG hX0
  exact ⟨c, hc, hc1, fun c₁ D' hc₁ hR =>
    crossing_length_pos_of_forall hG hπ.continuous hF (hc₁.trans hc1) (hP3 c₁ D' hc₁ hR)⟩

end EndElement

end HPC.Hagopian
