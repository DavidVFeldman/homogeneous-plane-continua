import HPC.Hagopian.Hagopian76L
import HPC.Hagopian.H76TranslateIn

/-!
# Batch 168, item B: Lemma R (`crossing_piece_of_R_aux`)

Commission 168 §1. Crossing pieces of `R(E)`, disjoint from `E`, through points of `R(E) − E`
arbitrarily close to a point `x` of `E` over the middle range:
1. `x` is a limit of points of `R(X, E) − E` (`mem_closure_extUnion_diff`): `E` is a proper
   subcontinuum of the indecomposable continuum `Cl R(X, E)` (Lemmas 4 and 6), so it has empty
   interior there.
2. Such points `y` near `x` lie above the axis (no point of `π[M]` just below `γ`; `y ∉ E`).
3. Lemma 2 at `x` gives a small `h` with `h(x) = y`.
4. `Q = h[k⁻¹[[a′, b′]]]` misses `E` (Lemma T) and meets the extension of `E` containing `y`, so
   `Q ⊆ R(E)` by absorption (`subset_extUnion_of_meets`, with `k` or `σ ∘ k`).
5. Lemma T relative to `A = Q` and to `A = R(E)` (`crossing_translate_in_aux`): the components
   through `y` cross.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section RPiece

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **`E` is nowhere dense in `Cl R(E)`**, in the form used: every point of `E` is a limit of
points of `R(X, E) − E` (`X = k⁻¹(0)`). `E` is a proper subcontinuum of the indecomposable continuum
`Cl R(E) = Cl R(X, E)` (Lemmas 4 and 6), so it has empty interior there. -/
theorem mem_closure_extUnion_diff (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) (x : E) :
    (x : M) ∈ closure (extUnion E (layer k 0) \ E) := by
  by_contra hx
  have hK := hagopian76_lemma6_X hX hi hE
  have hEc : Fold.Q78.IsContinuum E := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE; exact hab.1
  have hEE : IsExtensionAway E (layer k 0) E := ⟨subset_rfl, k, hE, rfl⟩
  have hER : E ⊆ extUnion E (layer k 0) := fun e he => ⟨E, hEE, he⟩
  have hEK : E ≠ closure (extUnion E (layer k 0)) := by
    intro heq
    obtain ⟨H, hH, hEH⟩ := (hagopian76_lemma4 hX hi hE).2 E hEE
    have hHK : H ⊆ closure (extUnion E (layer k 0)) :=
      fun v hv => subset_closure ⟨H, hH, hv⟩
    rw [← heq] at hHK
    exact hEH.2 hHK
  have hOK : (closure (extUnion E (layer k 0) \ E))ᶜ ∩ closure (extUnion E (layer k 0)) ⊆ E := by
    rintro z ⟨hzO, hzK⟩
    by_contra hzE
    obtain ⟨w, ⟨hwO, hwE⟩, hwR⟩ := mem_closure_iff.1 hzK _
      (isClosed_closure.isOpen_compl.inter hE.isCompact.isClosed.isOpen_compl) ⟨hzO, hzE⟩
    exact hwO (subset_closure ⟨hwR, hwE⟩)
  exact HPC.T13.false_of_interior hK hEc (hER.trans subset_closure) hEK
    isClosed_closure.isOpen_compl ⟨(x : M), hx, subset_closure (hER x.2)⟩ hOK

set_option maxHeartbeats 800000 in
/-- **Lemma R** (commission 168 §1), in the coordinates of `hagopian76_D`. See
`crossing_piece_of_R` in `Hagopian76M.lean` for the statement in words. -/
theorem crossing_piece_of_R_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (hab : a < b) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {a' b' : ℝ} (ha' : 0 < a') (ha'a : a' < a) (hbb' : b < b') (hb' : b' < 1) :
    ∃ c₀ > 0, Ioo a b ×ˢ Ioo 0 c₀ ⊆ D' ∧ c₀ < r₂ ∧ c₀ < s₂ ∧
    ∀ ζ > 0, ∀ x : E, (k x : ℝ) ∈ Icc (a + ζ) (b - ζ) → ∀ ε > 0,
      ∃ h : M ≃ₜ M, (∀ v, dist (h v) v < ε) ∧
      h (x : M) ∈ extUnion E (layer k 0) ∧ h (x : M) ∉ E ∧
      h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'} ⊆ extUnion E (layer k 0) ∧
      Disjoint (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) E ∧
      (∀ y : E, (k y : ℝ) ∈ Icc a' b' → ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
        F z = π (h (y : M) : Pt) ∧ dist z ((k y : ℝ), 0) < ε) ∧
      (∀ A : Set Pt, toPt (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) ⊆ A →
        toPt (h '' layerSet k {t | a + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ b - ζ / 2}) ⊆
          connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt) ∧
        (closure (connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
          π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
        (closure (connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
          π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty) ∧
      ∃ H : Set M, IsExtensionAway E (layer k 0) H ∧
        closure (connectedComponentIn
          (toPt (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) ∩ π ⁻¹' (F '' D'))
          (h (x : M) : Pt)) ⊆ toPt (H \ E) := by
  obtain ⟨c₀, hc₀, hlow, hr, hs, hT⟩ := crossing_translate_in_aux hX hi hE hπc hπS hγπ hF hab
    hc1 hI hIR hDR hDf hFDo hFDf ha' ha'a hbb' hb'
  refine ⟨c₀, hc₀, hlow, hr, hs, fun ζ hζ x hx ε hε => ?_⟩
  set η := min ε (min (a - a') (b' - b)) with hηdef
  have hη0 : 0 < η := lt_min hε (lt_min (by linarith) (by linarith))
  have hηε : η ≤ ε := min_le_left _ _
  have hηa : η ≤ a - a' := (min_le_right _ _).trans (min_le_left _ _)
  have hηb : η ≤ b' - b := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ, hδ, hTδ⟩ := hT ζ hζ η hη0
  set δ' := min δ ε with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ hε
  obtain ⟨hWo, -⟩ := hagopian76_lemma2 hX hδ'0 (x : M)
  obtain ⟨c', hc', hdisj⟩ := hbelow
  set c'' := min c' 1 with hc''def
  have hc''0 : 0 < c'' := lt_min hc' one_pos
  have hc''1 : c'' ≤ 1 := min_le_right _ _
  have hc''c' : c'' ≤ c' := min_le_left _ _
  have ha0 : 0 < a := ha'.trans ha'a
  have hb1 : b < 1 := hbb'.trans hb'
  set U := F '' (Ioo a b ×ˢ Ioo (-c'') c'') with hUdef
  have hUo : IsOpen U := isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo)
    (prod_mono (Ioo_subset_Ioo ha0.le hb1.le) (Ioo_subset_Ioo (by linarith) hc''1))
  have hxU : π ((x : M) : Pt) ∈ U := by
    rw [hγπ (k x) _ ⟨(x : M), ⟨x, Set.mem_singleton _, rfl⟩, rfl⟩, ← hF.2.1 (k x)]
    exact ⟨((k x : ℝ), 0), ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, by linarith, hc''0⟩, rfl⟩
  set N : Set M := Subtype.val ⁻¹' (π ⁻¹' U) ∩
    {y : M | ∃ h : M ≃ₜ M, h (x : M) = y ∧ ∀ v, dist v (h v) < δ'} with hNdef
  have hNo : IsOpen N :=
    ((hUo.preimage hπc).preimage continuous_subtype_val).inter hWo
  have hxN : (x : M) ∈ N := ⟨hxU, (hagopian76_lemma2 hX hδ'0 (x : M)).2⟩
  obtain ⟨y, ⟨hyU, h, hhx, hhmove⟩, hyR, hyE⟩ :=
    mem_closure_iff.1 (mem_closure_extUnion_diff hX hi hE x) N hNo hxN
  -- `π(y)` lies above the axis
  have hup : π (h (x : M) : Pt) ∈ F '' (Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    rw [hhx]
    obtain ⟨z, hz, hFz⟩ := hyU
    rcases lt_trichotomy z.2 0 with h2 | h2 | h2
    · exfalso
      refine disjoint_left.1 hdisj ⟨z, ⟨⟨hz.1.1.le, hz.1.2.le⟩, ?_, h2⟩, rfl⟩
        ⟨(y : Pt), y.2, hFz.symm⟩
      linarith [hz.2.1]
    · exfalso
      set t : unitInterval := ⟨z.1, by linarith [hz.1.1], by linarith [hz.1.2]⟩
      have h1 : π (y : Pt) = γ t := by
        rw [← hFz, ← hF.2.1 t]
        exact congrArg F (Prod.ext rfl h2)
      obtain ⟨y', hy', -⟩ := mem_layer_of_pi_eq_gamma hE hπS hγπ h1
      exact hyE (hy' ▸ y'.2)
    · exact ⟨z, ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, h2, by linarith [hz.2.2]⟩, hFz⟩
  have hmove : ∀ v, dist (h v) v < δ := fun v => by
    rw [dist_comm]; exact lt_of_lt_of_le (hhmove v) (min_le_left _ _)
  have hmove' : ∀ v, dist (h v) v < ε := fun v => by
    rw [dist_comm]; exact lt_of_lt_of_le (hhmove v) (min_le_right _ _)
  obtain ⟨hQE, hband, hA⟩ := hTδ x hx h hmove (by rw [hhx]; exact hyE) hup
  have hband' : ∀ y : E, (k y : ℝ) ∈ Icc a' b' → ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
      F z = π (h (y : M) : Pt) ∧ dist z ((k y : ℝ), 0) < ε := fun y hy => by
    obtain ⟨z, hz, hFz, hd⟩ := hband y hy
    exact ⟨z, hz, hFz, lt_of_lt_of_le hd hηε⟩
  -- absorption: `Q ⊆ R(X, E)`
  set S := {t : unitInterval | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'} with hSdef
  have hkxS : k x ∈ S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hQc : Fold.Q78.IsContinuum (h '' layerSet k S) :=
    isContinuum_homeo_image h (isContinuum_img hE.isCompact hE.2.1 (isClosed_interval_set a' b')
      (isPreconnected_interval_set a' b') ⟨_, hkxS⟩)
  have hyQ : y ∈ h '' layerSet k S := ⟨(x : M), ⟨x, hkxS, rfl⟩, hhx⟩
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  obtain ⟨Fx, hFx, hyF⟩ := hyR
  have hQX : Disjoint (h '' layerSet k S) (layer k 0) := hQE.mono_right (img_subset _)
  have hQR : h '' layerSet k S ⊆ extUnion E (layer k 0) :=
    subset_extUnion_of_meets hX hHU hAT hFx hQc hQX ⟨y, hyQ, hyF⟩
  -- one extension `H` contains the end points `g₀ ∈ h[k⁻¹(a′)]`, `g₁ ∈ h[k⁻¹(b′)]`
  obtain ⟨hEF, d, hd, hdX⟩ := hFx
  obtain ⟨e₀, he₀⟩ := hE.2.1.2.1 ⟨a', ha'.le, by linarith⟩
  obtain ⟨e₁, he₁⟩ := hE.2.1.2.1 ⟨b', by linarith, hb'.le⟩
  have hk₀ : (k e₀ : ℝ) = a' := by rw [he₀]
  have hk₁ : (k e₁ : ℝ) = b' := by rw [he₁]
  have he₀S : k e₀ ∈ S := ⟨hk₀.ge, by rw [hk₀]; linarith⟩
  have he₁S : k e₁ ∈ S := ⟨by rw [hk₁]; linarith, hk₁.le⟩
  have hg : ∀ e : E, k e ∈ S → ∃ H : Set M, IsExtensionAway E (layer k 0) H ∧ h (e : M) ∈ H := by
    intro e he
    obtain ⟨H, hFH, hgH, D, hD, hDX⟩ := absorb_point hX hHU hAT hd hQc (hdX ▸ hQX)
      ⟨y, hyQ, hyF⟩ (⟨(e : M), ⟨e, he, rfl⟩, rfl⟩ : h (e : M) ∈ h '' layerSet k S)
    exact ⟨H, ⟨hEF.trans hFH, D, hD, hDX.trans hdX⟩, hgH⟩
  obtain ⟨H₀, hH₀, hg₀⟩ := hg e₀ he₀S
  obtain ⟨H₁, hH₁, hg₁⟩ := hg e₁ he₁S
  obtain ⟨H, hH, hg₀H, hg₁H⟩ : ∃ H : Set M, IsExtensionAway E (layer k 0) H ∧
      h (e₀ : M) ∈ H ∧ h (e₁ : M) ∈ H := by
    rcases (hagopian76_lemma4 hX hi hE).1.total hH₀ hH₁ with h01 | h10
    · exact ⟨H₁, hH₁, h01 hg₀, hg₁⟩
    · exact ⟨H₀, hH₀, hg₀, h10 hg₁⟩
  have hHc := hH.isContinuum
  have hHQ := isContinuum_inter_of_HU hHU hHc hQc ⟨_, hg₀H, ⟨(e₀ : M), ⟨e₀, he₀S, rfl⟩, rfl⟩⟩
  set K := h.symm '' (H ∩ h '' layerSet k S) with hKdef
  have hKc : Fold.Q78.IsContinuum K := isContinuum_homeo_image h.symm hHQ
  have hKE : K ⊆ E := by
    rintro _ ⟨_, ⟨-, _, ⟨e, -, rfl⟩, rfl⟩, rfl⟩
    rw [Homeomorph.symm_apply_apply]; exact e.2
  have hKmem : ∀ e : E, k e ∈ S → h (e : M) ∈ H → (e : M) ∈ K := fun e he heH =>
    ⟨h (e : M), ⟨heH, ⟨(e : M), ⟨e, he, rfl⟩, rfl⟩⟩, Homeomorph.symm_apply_apply _ _⟩
  have hIoo := layerSet_Ioo_subset hE hKE hKc
    ⟨(e₀ : M), hKmem e₀ he₀S hg₀H, ⟨e₀, he₀, rfl⟩⟩ ⟨(e₁ : M), hKmem e₁ he₁S hg₁H, ⟨e₁, he₁, rfl⟩⟩
  -- the part of `Q` over `D` lies in `h[k⁻¹((a′, b′))] ⊆ H`
  set O := π ⁻¹' (F '' D') with hOdef
  have hQO : toPt (h '' layerSet k S) ∩ O ⊆ toPt (H \ E) := by
    rintro _ ⟨⟨_, ⟨_, ⟨e, he, rfl⟩, rfl⟩, rfl⟩, hO⟩
    obtain ⟨dd, hdd, hFdd⟩ := hO
    obtain ⟨z, hz, hFz, hdz⟩ := hband e he
    have hzR : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨⟨hz.1.1.le, hz.1.2.le⟩, by linarith [hz.2.1], by linarith [hz.2.2, hr, hI.left_mem.1.2.2, hc1]⟩
    have hddR : dd ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hdd
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have hzd := collar_injOn hF hddR hzR (hFdd.trans hFz.symm)
    have hz1 := (dist_prod_lt hdz).1
    have hdd1 := (hDR hdd).1
    rw [hzd] at hdd1
    have h1 := abs_lt.1 hz1
    have hlt0 : k e₀ < k e := by
      rw [← Subtype.coe_lt_coe, hk₀]; linarith [hdd1.1]
    have hlt1 : k e < k e₁ := by
      rw [← Subtype.coe_lt_coe, hk₁]; linarith [hdd1.2]
    have heK : (e : M) ∈ K := hIoo ⟨e, ⟨by rw [he₀] at hlt0; exact hlt0,
      by rw [he₁] at hlt1; exact hlt1⟩, rfl⟩
    obtain ⟨_, ⟨hmH, -⟩, hm⟩ := heK
    refine ⟨h (e : M), ⟨?_, disjoint_left.1 hQE ⟨(e : M), ⟨e, he, rfl⟩, rfl⟩⟩, rfl⟩
    have : h (h.symm _) = h (e : M) := congrArg h hm
    rw [Homeomorph.apply_symm_apply] at this
    rw [← this]; exact hmH
  have hHEc : IsClosed (toPt (H ∩ h '' layerSet k S)) :=
    (isContinuum_val_image hHQ).1.isClosed
  have hcl : closure (connectedComponentIn (toPt (h '' layerSet k S) ∩ O) (h (x : M) : Pt)) ⊆
      toPt (H \ E) := by
    have hsub : connectedComponentIn (toPt (h '' layerSet k S) ∩ O) (h (x : M) : Pt) ⊆
        toPt (H ∩ h '' layerSet k S) := by
      intro v hv
      have hv' := connectedComponentIn_subset _ _ hv
      obtain ⟨m, ⟨hmH, -⟩, rfl⟩ := hQO hv'
      exact ⟨m, ⟨hmH, by obtain ⟨_, hmQ, hmv⟩ := hv'.1; exact (Subtype.ext hmv) ▸ hmQ⟩, rfl⟩
    refine (closure_minimal hsub hHEc).trans ?_
    rintro _ ⟨m, ⟨hmH, hmQ⟩, rfl⟩
    exact ⟨m, ⟨hmH, disjoint_left.1 hQE hmQ⟩, rfl⟩
  exact ⟨h, hmove', hhx ▸ ⟨Fx, ⟨hEF, d, hd, hdX⟩, hyF⟩, hhx ▸ hyE, hQR, hQE, hband', hA, H, hH,
    hcl⟩

end RPiece

end HPC.Hagopian
