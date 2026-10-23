import HPC.Hagopian.H76T12Sides
import HPC.Hagopian.H76Sides
import HPC.Hagopian.H76Meagre
import HPC.Hagopian.H76ChainSep
import HPC.Hagopian.Hagopian76L

/-!
# Batch 169, item B: generic `p`, `q` (`exists_generic_pq_aux`)

Route (commission 169 §1.1, without `K`): take the points `p₀ = h₀(x)` below and `q₀ = h₁(x)`
above the crossing continuum `Z = Cl B ⊆ H − E` given by `T12_sides_aux`. The sets below and above
`Z` are open in `R²` (`belowSet_isOpen`), so their traces on `M` near `p₀` and `q₀` are nonempty
open subsets of `M`, and contain points `p`, `q` off the meagre set `R(E)` (`exists_notMem_Rset`).
Near `x` these are `p = h(x)`, `q = h₁(x)` for small `h`, `h₁` (Lemma 2). They are separated by
`Z` (`crossing_sides_aux`), hence by `H ⊇ Z` and by `R(E) ⊇ H`, since they lie off `R(E)`. Their
components in `M ∩ π⁻¹[D]` cross (Lemma T, `crossing_translate`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- Enlarging a separator by a set missing the two points keeps the separation. -/
theorem SepIn.mono {O A A' : Set Pt} {p q : Pt} (h : SepIn O A p q) (hAA' : A ⊆ A')
    (hp : p ∉ A') (hq : q ∉ A') : SepIn O A' p q :=
  ⟨⟨h.1.1, hp⟩, ⟨h.2.1.1, hq⟩, fun S hS hSO hpS hqS =>
    h.2.2 S hS (fun _ hz => ⟨(hSO hz).1, fun h' => (hSO hz).2 (hAA' h')⟩) hpS hqS⟩

section Generic

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
theorem subset_Rset_self {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    E ⊆ Rset k :=
  fun _ hz => Or.inl ⟨E, ⟨subset_rfl, k, hE, rfl⟩, hz⟩

omit [CompactSpace M] [ConnectedSpace M] in
theorem val_mem_toPt_iff {A : Set M} {z : M} : (z : Pt) ∈ toPt A ↔ z ∈ A :=
  ⟨fun ⟨_, hw, hwz⟩ => (Subtype.ext hwz) ▸ hw, fun h => ⟨z, h, rfl⟩⟩

set_option maxHeartbeats 800000 in
/-- **B. Generic `p`, `q`** (commission 169 §2.B). See `exists_generic_pq` in
`Hagopian76N.lean` for the statement in words. -/
theorem exists_generic_pq_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDo : IsOpen D')
    (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ w₂ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂)) :
    ∃ x : E, (k x : ℝ) = t₀ ∧ ∀ ε > 0, ∃ (h h₁ : M ≃ₜ M) (u₁ u₂ : ℝ) (H : Set M) (B : Set Pt),
      (∀ v, dist (h v) v < ε) ∧ (∀ v, dist (h₁ v) v < ε) ∧
      h (x : M) ∉ Rset k ∧ h₁ (x : M) ∉ Rset k ∧
      0 < u₁ ∧ u₁ < u₂ ∧ u₂ < w₂ ∧
      IsExtensionAway E (layer k 0) H ∧
      IsPreconnected B ∧ B ⊆ π ⁻¹' (F '' D') ∧ closure B ⊆ toPt (H \ E) ∧
      IsCompact (closure B) ∧
      (closure B ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure B ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty ∧
      Disjoint (closure B) (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ioc 0 u₁))) ∧
      Disjoint (closure B) (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ico u₂ w₂))) ∧
      (h (x : M) : Pt) ∈ belowSet π F D' t₀ u₁ (closure B) ∧
      (h₁ (x : M) : Pt) ∈ aboveSet π F D' t₀ u₂ w₂ (closure B) ∧
      SepIn (π ⁻¹' (F '' D')) (toPt H) (h (x : M)) (h₁ (x : M)) ∧
      SepIn (π ⁻¹' (F '' D')) (toPt (Rset k)) (h (x : M)) (h₁ (x : M)) ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h₁ (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h₁ (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty := by
  obtain ⟨c₀, -, -, -, -, hT⟩ := crossing_translate (a' := a / 2) (b' := (b + 1) / 2)
    hX hi hE hπc hπS hγπ hF hab hc1 hI hIR hDR hDf hFDo hFDf (by linarith) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨x, hkx, hmain⟩ := T12_sides_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1 hbelow hI hIs
    hIR hDo hDR hDf hFDo hFDf ht₀ hw₂
  refine ⟨x, hkx, fun ε hε => ?_⟩
  set ζ := min (t₀ - a) (b - t₀) / 2 with hζdef
  have hζ0 : 0 < ζ := by
    have := lt_min (sub_pos.2 ht₀.1) (sub_pos.2 ht₀.2); linarith
  have hxζ : (k x : ℝ) ∈ Icc (a + ζ) (b - ζ) := by
    rw [hkx]
    have h1 := min_le_left (t₀ - a) (b - t₀)
    have h2 := min_le_right (t₀ - a) (b - t₀)
    have h3 := lt_min (sub_pos.2 ht₀.1) (sub_pos.2 ht₀.2)
    constructor <;> linarith
  obtain ⟨δ, hδ, hδT⟩ := hT ζ hζ0 1 one_pos
  set ε₁ := min ε δ with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε hδ
  obtain ⟨hWo, hxW⟩ := hagopian76_lemma2 hX hε₁0 (x : M)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hWo (x : M) hxW
  have hW : ∀ y : M, dist y (x : M) < ρ →
      ∃ g : M ≃ₜ M, g (x : M) = y ∧ ∀ v, dist (g v) v < ε₁ := by
    intro y hy
    obtain ⟨g, hg, hgv⟩ := hball (show y ∈ ball (x : M) ρ from hy)
    exact ⟨g, hg, fun v => by rw [dist_comm]; exact hgv v⟩
  obtain ⟨h₀, h₁', u₁, u₂, hh₀, hh₁, hu₁, hu₁₂, hu₂w, hπp, hπq, H, B, hH, hB, hBO, hZH, hZc,
    hZL, hZR, hBe, hlo, hhi⟩ := hmain (ρ / 2) (half_pos hρ)
  set O := π ⁻¹' (F '' D') with hOdef
  have hπinj : InjOn π O := injOn_pi_preimage hπS hγπ hF fun d hd => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hd
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, h3⟩
  have hsegD : ({t₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D' :=
    seg_subset_rect_domain (r := ((a, r₂) : ℝ × ℝ)) (s := ((b, s₂) : ℝ × ℝ)) hab hI
      inter_subset_left hDo hDR hDf ht₀ hw₂.1 hseg
  have hdisj := crossing_sides_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf ht₀ hw₂ hFw hseg hπinj
    hB hBO hZc hBe hZL hZR hu₁₂ hlo hhi
  have hEH : E ⊆ H := hH.1
  have hHR : H ⊆ Rset k := fun z hz => Or.inl ⟨H, hH, hz⟩
  -- `p₀` and `q₀`
  have hp₀O : ((h₀ x : M) : Pt) ∈ O \ closure B := by
    refine ⟨⟨(t₀, u₁), hsegD ⟨rfl, hu₁, hu₁₂.trans hu₂w⟩, hπp.symm⟩, fun hz => ?_⟩
    exact disjoint_left.1 hlo hz ⟨(t₀, u₁), ⟨rfl, hu₁, le_rfl⟩, hπp.symm⟩
  have hq₀O : ((h₁' x : M) : Pt) ∈ O \ closure B := by
    refine ⟨⟨(t₀, u₂), hsegD ⟨rfl, hu₁.trans hu₁₂, hu₂w⟩, hπq.symm⟩, fun hz => ?_⟩
    exact disjoint_left.1 hhi hz ⟨(t₀, u₂), ⟨rfl, le_rfl, hu₂w⟩, hπq.symm⟩
  have hp₀b : ((h₀ x : M) : Pt) ∈ belowSet π F D' t₀ u₁ (closure B) :=
    mem_belowSet hp₀O ⟨(t₀, u₁), ⟨rfl, hu₁, le_rfl⟩, hπp.symm⟩
  have hq₀a : ((h₁' x : M) : Pt) ∈ aboveSet π F D' t₀ u₂ w₂ (closure B) :=
    mem_aboveSet hq₀O ⟨(t₀, u₂), ⟨rfl, le_rfl, hu₂w⟩, hπq.symm⟩
  -- generic points near `p₀` and `q₀`
  have hpick : ∀ (z₀ : M) (T : Set Pt), IsOpen T → (z₀ : Pt) ∈ T → dist z₀ (x : M) < ρ / 2 →
      ∃ g : M ≃ₜ M, (∀ v, dist (g v) v < ε₁) ∧ g (x : M) ∉ Rset k ∧ ((g (x : M)) : Pt) ∈ T := by
    intro z₀ T hT hz₀ hz₀x
    have hVo : IsOpen ((Subtype.val : M → Pt) ⁻¹' (T ∩ ball (z₀ : Pt) (ρ / 2))) :=
      (hT.inter isOpen_ball).preimage continuous_subtype_val
    obtain ⟨p, ⟨hpT, hpb⟩, hpR⟩ := exists_notMem_Rset hX hi hE hVo
      ⟨z₀, hz₀, mem_ball_self (half_pos hρ)⟩
    have hpx : dist p (x : M) < ρ := by
      have h1 : dist p z₀ < ρ / 2 := hpb
      linarith [dist_triangle p z₀ (x : M)]
    obtain ⟨g, hgx, hg⟩ := hW p hpx
    exact ⟨g, hg, hgx ▸ hpR, hgx ▸ hpT⟩
  obtain ⟨g, hg, hgR, hgT⟩ := hpick (h₀ x) _ (belowSet_isOpen hπc hFDo isClosed_closure t₀ u₁)
    hp₀b (hh₀ x)
  obtain ⟨g₁, hg₁, hg₁R, hg₁T⟩ := hpick (h₁' x) _
    (aboveSet_isOpen hπc hFDo isClosed_closure t₀ u₂ w₂) hq₀a (hh₁ x)
  have hgO : ((g x : M) : Pt) ∈ O \ closure B := by
    obtain ⟨S, -, hSO, hPS, -⟩ := hgT; exact hSO hPS
  have hg₁O : ((g₁ x : M) : Pt) ∈ O \ closure B := by
    obtain ⟨S, -, hSO, hPS, -⟩ := hg₁T; exact hSO hPS
  have hsepH : SepIn O (toPt H) (g x) (g₁ x) := by
    refine ⟨⟨hgO.1, fun h' => hgR (hHR (val_mem_toPt_iff.1 h'))⟩,
      ⟨hg₁O.1, fun h' => hg₁R (hHR (val_mem_toPt_iff.1 h'))⟩, fun S hS hSO hpS hqS => ?_⟩
    have hSO' : S ⊆ O \ closure B := fun z hz =>
      ⟨(hSO hz).1, fun h' => (hSO hz).2 (image_mono diff_subset (hZH h'))⟩
    exact disjoint_left.1 hdisj (belowSet_of_preconnected hS hSO' hpS hqS hgT) hg₁T
  have hsepR : SepIn O (toPt (Rset k)) (g x) (g₁ x) :=
    hsepH.mono (image_mono hHR) (fun h' => hgR (val_mem_toPt_iff.1 h'))
      (fun h' => hg₁R (val_mem_toPt_iff.1 h'))
  -- crossing (Lemma T)
  have hcross : ∀ g' : M ≃ₜ M, (∀ v, dist (g' v) v < ε₁) → g' (x : M) ∉ Rset k →
      ((g' x : M) : Pt) ∈ O →
      (closure (connectedComponentIn (M ∩ O) (g' (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ O) (g' (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty := by
    intro g' hg' hg'R hg'O
    have hsmall : ∀ v, dist (g' v) v < δ := fun v => lt_of_lt_of_le (hg' v) (min_le_right _ _)
    have hnE : g' (x : M) ∉ E := fun h' => hg'R (subset_Rset_self hE h')
    have hπ : π (g' (x : M) : Pt) ∈ F '' (Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
      obtain ⟨d, hd, hFd⟩ := hg'O
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hd
      exact ⟨d, ⟨⟨by linarith, by linarith⟩, h3, by linarith⟩, hFd⟩
    obtain ⟨-, -, -, hL', hR'⟩ := hδT x hxζ g' hsmall hnE hπ
    exact ⟨hL', hR'⟩
  obtain ⟨hcL, hcR⟩ := hcross g hg hgR hgO.1
  obtain ⟨hcL₁, hcR₁⟩ := hcross g₁ hg₁ hg₁R hg₁O.1
  have hε₁ε : ∀ g' : M ≃ₜ M, (∀ v, dist (g' v) v < ε₁) → ∀ v, dist (g' v) v < ε :=
    fun g' hg' v => lt_of_lt_of_le (hg' v) (min_le_left _ _)
  exact ⟨g, g₁, u₁, u₂, H, B, hε₁ε g hg, hε₁ε g₁ hg₁, hgR, hg₁R, hu₁, hu₁₂, hu₂w, hH, hB, hBO,
    hZH, hZc, hZL, hZR, hlo, hhi, hgT, hg₁T, hsepH, hsepR, hcL, hcR, hcL₁, hcR₁⟩

end Generic

end HPC.Hagopian
