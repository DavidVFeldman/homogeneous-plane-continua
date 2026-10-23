import HPC.Hagopian.H76StrandUse

/-!
# Batch 177: the existence of `T12Data`; `π⁻¹[Fr D]`; the assembly, conditionally

* `exists_T12Data_aux` (item A): with the strand constants, Hagopian's T12/T13 output exists as a
  `T12Data` package; T12 (2) (the essential closure) now holds for the same `h` as T12 (3), by the
  strand lemma (`strand_essential`).
* `pi_fibre`, `pi_preimage_continuum` (item B): `π` is a proper map with connected fibres, so it
  pulls continua back to continua; `frontier_D_continuum`: `Fr D` is a continuum for Hagopian's
  domain; hence `π⁻¹[Fr D]` is compact and connected.
* `hagopian76_T15_T17_cond2` (item F): the conditional contradiction with the existence of
  `T12Data` and of `Y = π⁻¹[Fr D]` discharged.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section T12Exists

variable {M : Set Pt}

/-- **The fibres of `π`** are compact and connected: a layer of `E`, or a point. -/
theorem pi_fibre {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (y : Pt) :
    IsCompact (π ⁻¹' {y}) ∧ IsPreconnected (π ⁻¹' {y}) := by
  obtain ⟨z, rfl⟩ := hπ.surjective y
  by_cases hz : z ∈ toPt E
  · obtain ⟨e, rfl⟩ := mem_toPt_iff.1 hz
    have heq : π ⁻¹' {π ((e : M) : Pt)} = toPt (layer k (k e)) := by
      rw [← elt_layerSetoid_of_mem]
      ext w
      rw [mem_preimage, mem_singleton_iff, hπS]
      rfl
    rw [heq]
    refine ⟨isCompact_toPt (isCompact_img hE.isCompact hE.2.1.1 isClosed_singleton), ?_⟩
    exact ((hE.2.1.2.2 (k e)).isPreconnected.image _ continuous_subtype_val.continuousOn).image _
      continuous_subtype_val.continuousOn
  · have heq : π ⁻¹' {π z} = {z} := by
      ext w
      constructor
      · intro hw; exact eq_of_pi_eq_off hπS hz hw
      · rintro rfl; rfl
    rw [heq]
    exact ⟨isCompact_singleton, isPreconnected_singleton⟩

/-- **`π` pulls continua back to continua** (commission 177 §3.B: "`π` is a monotone perfect map").
For a compact connected `V ⊆ R²`, `π⁻¹[V]` is compact and connected. -/
theorem pi_preimage_continuum {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {V : Set Pt} (hV : IsCompact V) (hVc : IsConnected V) :
    IsCompact (π ⁻¹' V) ∧ IsConnected (π ⁻¹' V) := by
  have hprop : IsProperMap π := isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hπ.continuous, pi_isClosedMap hE hπ hπS, fun y => (pi_fibre hE hπ hπS y).1⟩
  have hK := hprop.isCompact_preimage hV
  refine ⟨hK, ?_⟩
  haveI : CompactSpace (π ⁻¹' V) := isCompact_iff_compactSpace.mp hK
  set f : (π ⁻¹' V) → Pt := fun x => π x with hfdef
  have hf : Continuous f := hπ.continuous.comp continuous_subtype_val
  have hVr : V ⊆ range f := fun v hv => by
    obtain ⟨z, rfl⟩ := hπ.surjective v
    exact ⟨⟨z, hv⟩, rfl⟩
  have hfib : ∀ y ∈ V, IsPreconnected (f ⁻¹' {y}) := by
    intro y hy
    have h1 : Subtype.val '' (f ⁻¹' {y}) = π ⁻¹' {y} := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hw
        have hw' : π w = y := hw
        exact ⟨⟨w, show π w ∈ V by rw [hw']; exact hy⟩, hw', rfl⟩
    rw [← IsInducing.subtypeVal.isPreconnected_image, h1]
    exact (pi_fibre hE hπ hπS y).2
  have hpre := isPreconnected_preimage_of_fibres hf hV.isClosed hVc.isPreconnected hVr hfib
  have huniv : f ⁻¹' V = univ := eq_univ_of_forall fun x => x.2
  rw [huniv] at hpre
  have himg := hpre.image Subtype.val continuous_subtype_val.continuousOn
  rw [image_univ, Subtype.range_coe] at himg
  obtain ⟨v, hv⟩ := hVc.nonempty
  obtain ⟨z, rfl⟩ := hπ.surjective v
  exact ⟨⟨z, hv⟩, himg⟩

/-- **`Fr D` is a continuum** for Hagopian's domain `D = F[D′]` (bounded by the arc `I₂`, the
bottom edge and the two side segments). -/
theorem frontier_D_continuum {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)}
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂)) :
    IsCompact (frontier (F '' D')) ∧ IsConnected (frontier (F '' D')) := by
  set A := Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂ with hA
  obtain ⟨-, g, hg, hgr, hg0, hg1⟩ := hI
  have hR : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_restrict.2 hF.1.continuous
  have hAR : A ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun z hz =>
    ⟨⟨by linarith [hz.1.1.1], by linarith [hz.1.1.2]⟩, by linarith [hz.1.2.1],
      by linarith [hz.1.2.2]⟩
  have hr₂ : (a, r₂) ∈ A := by rw [← hgr, ← hg0]; exact mem_range_self _
  have hs₂ : (b, s₂) ∈ A := by rw [← hgr, ← hg1]; exact mem_range_self _
  have hI₂ : I₂ = F '' A := by
    apply Subset.antisymm
    · intro p hp
      obtain ⟨z, hz, rfl⟩ := hIR hp
      exact ⟨z, ⟨hz, hp⟩, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩; exact hz.2
  have hAc : IsCompact A := by rw [← hgr]; exact isCompact_range hg.continuous
  have hAconn : IsConnected A := by rw [← hgr]; exact isConnected_range hg.continuous
  have hr0 : 0 ≤ r₂ := hr₂.1.2.1.le
  have hs0 : 0 ≤ s₂ := hs₂.1.2.1.le
  have hr1 : r₂ ≤ 1 := hr₂.1.2.2.trans hc1
  have hs1 : s₂ ≤ 1 := hs₂.1.2.2.trans hc1
  set P2 := Icc a b ×ˢ ({0} : Set ℝ)
  set P3 := ({a} : Set ℝ) ×ˢ Icc 0 r₂
  set P4 := ({b} : Set ℝ) ×ˢ Icc 0 s₂
  have h2R : P2 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun z ⟨⟨h1, h2⟩, h3⟩ => by
    rw [mem_singleton_iff] at h3
    exact ⟨⟨by linarith, by linarith⟩, by rw [h3]; norm_num, by rw [h3]; norm_num⟩
  have h3R : P3 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun z ⟨h1, h2, h3⟩ => by
    rw [mem_singleton_iff] at h1
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have h4R : P4 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun z ⟨h1, h2, h3⟩ => by
    rw [mem_singleton_iff] at h1
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have c2 : IsConnected (F '' P2) :=
    ((isConnected_Icc hab.le).prod isConnected_singleton).image _ (hR.mono h2R)
  have c3 : IsConnected (F '' P3) :=
    (isConnected_singleton.prod (isConnected_Icc hr0)).image _ (hR.mono h3R)
  have c4 : IsConnected (F '' P4) :=
    (isConnected_singleton.prod (isConnected_Icc hs0)).image _ (hR.mono h4R)
  have c1 : IsConnected (F '' A) := hAconn.image _ (hR.mono hAR)
  have k2 : IsCompact (F '' P2) := (isCompact_Icc.prod isCompact_singleton).image_of_continuousOn
    (hR.mono h2R)
  have k3 : IsCompact (F '' P3) := (isCompact_singleton.prod isCompact_Icc).image_of_continuousOn
    (hR.mono h3R)
  have k4 : IsCompact (F '' P4) := (isCompact_singleton.prod isCompact_Icc).image_of_continuousOn
    (hR.mono h4R)
  have k1 : IsCompact (F '' A) := hAc.image_of_continuousOn (hR.mono hAR)
  have heq : frontier (F '' D') = F '' A ∪ ((F '' P2 ∪ F '' P3) ∪ F '' P4) := by
    rw [hFDf, hI₂]; ext p; simp only [mem_union]; tauto
  rw [heq]
  refine ⟨k1.union ((k2.union k3).union k4), ?_⟩
  have e23 : F (a, 0) ∈ F '' P2 ∩ F '' P3 :=
    ⟨⟨(a, 0), ⟨⟨le_rfl, hab.le⟩, rfl⟩, rfl⟩, ⟨(a, 0), ⟨rfl, le_rfl, hr0⟩, rfl⟩⟩
  have e4 : F (b, 0) ∈ (F '' P2 ∪ F '' P3) ∩ F '' P4 :=
    ⟨Or.inl ⟨(b, 0), ⟨⟨hab.le, le_rfl⟩, rfl⟩, rfl⟩, ⟨(b, 0), ⟨rfl, le_rfl, hs0⟩, rfl⟩⟩
  have e1 : F (a, r₂) ∈ F '' A ∩ ((F '' P2 ∪ F '' P3) ∪ F '' P4) :=
    ⟨⟨_, hr₂, rfl⟩, Or.inl (Or.inr ⟨(a, r₂), ⟨rfl, hr0, le_rfl⟩, rfl⟩)⟩
  exact IsConnected.union ⟨_, e1⟩ c1 (IsConnected.union ⟨_, e4⟩
    (IsConnected.union ⟨_, e23⟩ c2 c3) c4)

/-- **`Y = π⁻¹[Fr D]`** (commission 177 §3.B) is compact and connected, misses `π⁻¹[D]`, and contains
the frontier of `π⁻¹[D]`: the hypotheses on `Y` of `hagopian76_property4_top` and
`hagopian76_T15_T17_cond`. -/
theorem pi_preimage_frontier_D_aux {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂)) :
    IsCompact (π ⁻¹' frontier (F '' D')) ∧ IsConnected (π ⁻¹' frontier (F '' D')) ∧
      Disjoint (π ⁻¹' frontier (F '' D')) (π ⁻¹' (F '' D')) ∧
      frontier (π ⁻¹' (F '' D')) ⊆ π ⁻¹' frontier (F '' D') := by
  obtain ⟨hK, hC⟩ := frontier_D_continuum hF ha hab hb hc1 hI hIR hFDf
  obtain ⟨hK', hC'⟩ := pi_preimage_continuum hE hπ hπS hK hC
  refine ⟨hK', hC', ?_, hπ.continuous.frontier_preimage_subset _⟩
  rw [disjoint_iff_inter_eq_empty, ← preimage_inter, inter_comm, hFDo.inter_frontier_eq,
    preimage_empty]

variable [CompactSpace M] [ConnectedSpace M]

/-- **A. `T12Data` exists** (commission 177 §3.A). Set-up of `hagopian76_T12_uncond` for
`[a, b] = [3/22, 19/22]` and the domain `D = F[D′]` of height `c₁ ≤ c` (`IsCrossRegion`), with the
strand constants (`n ≥ 15`) and `t₀` with `3/22 + 2/n ≤ t₀ ≤ 19/22 − 2/n`. For every `ε₃ > 0` and
every `K₀ ⊆ M` there is a `T12Data` package `D` with `D.p = D.h(x)`, `k(x) = t₀`, and
`D.K = K₀ ∪ {D.p}`.

The new field is `ess` (T12 (2)) **for the same `h` as T12 (3)**: the `ε`-homeomorphisms of
`hagopian76_T12_uncond` are taken with `ε = min(ε₃/2, θ/4)`, and `strand_essential` applies to
`p = h(x)`. -/
theorem exists_T12Data_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
    {t₀ w₂ : ℝ} (ht₀1 : 3 / 22 + 2 / (n : ℝ) ≤ t₀) (ht₀2 : t₀ ≤ 19 / 22 - 2 / (n : ℝ))
    (hw₂ : w₂ ∈ Ioc 0 c₁) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (K₀ : Set M) {ε₃ : ℝ} (hε₃ : 0 < ε₃) :
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧ ∃ x : E, (k x : ℝ) = t₀ ∧ D.p = D.h x := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hn0 : (0 : ℝ) < 2 / (n : ℝ) := by
    have : (15 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  obtain ⟨x, hkx, hmain⟩ := hagopian76_T12_uncond hX hi hE hπ.continuous hπS hγπ hF
    (by norm_num) (by norm_num) (by norm_num) hc1 hbelow hI hIs hIR hDo hR.sub hDf hR.isOpen hFDf
    ⟨by linarith, by linarith⟩ hw₂ hFw hseg
  have hε : 0 < min (ε₃ / 2) (θ / 4) := lt_min (by linarith) (by linarith [hS.θ_pos])
  obtain ⟨h, h₁, H, hh, hh₁, -, -, hH, hsep, -, -, hne, -⟩ := hmain _ hε
  have hhθ : ∀ v, dist (h v) v < θ / 4 := fun v => (hh v).trans_le (min_le_right _ _)
  have hpD : π (h x : Pt) ∈ F '' D' := by
    have h1 := (closure_nonempty_iff.1 (hne.mono inter_subset_left))
    exact (connectedComponentIn_nonempty_iff.1 h1).2
  obtain ⟨G, -, ⟨hEG, d, hG, hX0⟩, hGsep, hirr⟩ :=
    hagopian76_T13_uncond hX hi hE (hR.isOpen.preimage hπ.continuous) hH hsep
  have hq : ((h.symm.trans h₁) (h x) : Pt) = (h₁ x : Pt) := by simp
  refine ⟨T12Data.mk (insert (h x) K₀) h h₁ (h x) (mem_insert _ _)
    (fun v => (hh v).trans_le (min_le_left _ _)) (fun v => (hh₁ v).trans_le (min_le_left _ _))
    (strand_essential hX hi hE hπ.continuous hπS hγπ hF hS hn hc₁ hR h hhθ x hpD
      (by rw [hkx]; exact ht₀1) (by rw [hkx]; exact ht₀2))
    G d hG hEG hX0 (by rw [hq]; exact hGsep) (by rw [hq]; exact hirr), rfl, x, hkx, rfl⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **The hypotheses of `hagopian76_T15_T17_cond` (batch 176) are inconsistent**: a strictly
increasing `x : ℕ → [0, 1]` cannot take the value `1` (`x (2n) < x (2n + 1) ≤ 1`). The batch-176
conditional form is therefore vacuous; `hagopian76_T15_T17_cond_fix` is the corrected statement,
with `x` strictly increasing on the indices `1, …, 2n` only. -/
theorem T15_T17_cond_hyps_inconsistent (x : ℕ → unitInterval) (n : ℕ) (hx : StrictMono x)
    (hxn : x (2 * n) = 1) : False := by
  have h1 := hx (Nat.lt_succ_self (2 * n))
  rw [hxn] at h1
  exact absurd unitInterval.le_one' (not_le.2 h1)

/-- **E/F. T15–T17, conditional, corrected** (p. 348). The statement of
`hagopian76_T15_T17_cond` (batch 176) with `StrictMono x` replaced by strict monotonicity on the
indices `1, …, 2n` (`StrictMonoOn x (Icc 1 (2 * n))`); with `StrictMono x` the hypotheses are
inconsistent (`T15_T17_cond_hyps_inconsistent`). The proof is the batch-176 proof. -/
theorem hagopian76_T15_T17_cond_fix (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {c₁ : ℝ} (hc₁ : c₁ ≤ 1) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D')
    (hD'c : IsPreconnected D') {ε₃ : ℝ} (D : T12Data E k π F D' ε₃) {Y : Set Pt}
    (hY : IsCompact Y) (hYc : IsConnected Y) (hYO : Disjoint Y (π ⁻¹' (F '' D')))
    (hfr : frontier (π ⁻¹' (F '' D')) ⊆ Y)
    (hSBC : SepByCrossing D.G π F c₁ D' (π ⁻¹' (F '' D')) D.p (D.f D.p))
    (x : ℕ → unitInterval) (n : ℕ) (hn : 2 ≤ n) (hx : StrictMonoOn x (Icc 1 (2 * n)))
    (hx1 : x 1 = 0) (hx2 : layerSet D.d (Icc 0 (x 2)) = E)
    (hblocks : ∀ r ∈ crossingIntervals D.d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ n ∧
      x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i))
    (hxn : x (2 * n) = 1) (hstep : Property4Step D x n) : False := by
  have hlt : ∀ i j, 1 ≤ i → i < j → j ≤ 2 * n → x i < x j := fun i j hi hij hj =>
    hx ⟨hi, by omega⟩ ⟨by omega, hj⟩ hij
  have hle : ∀ i j, 1 ≤ i → i ≤ j → j ≤ 2 * n → x i ≤ x j := fun i j hi hij hj => by
    rcases eq_or_lt_of_le hij with rfl | h
    · exact le_rfl
    · exact (hlt i j hi h hj).le
  have h0 : 0 < x (2 * n - 2) := by
    rw [← hx1]; exact hlt 1 _ le_rfl (by omega) (by omega)
  have h12 : x (2 * n - 2) < x (2 * n - 1) := hlt _ _ (by omega) (by omega) (by omega)
  have hEs : E ⊆ layerSet D.d (Icc 0 (x (2 * n - 2))) :=
    hx2.symm.subset.trans (layerSet_mono D.d (Icc_subset_Icc le_rfl
      (hle 2 _ (by omega) (by omega) (by omega))))
  have hgap : ∀ r ∈ crossingIntervals D.d π F c₁ D',
      r.2 ≤ x (2 * n - 2) ∨ x (2 * n - 1) ≤ r.1 := by
    intro r hr
    obtain ⟨i, hi1, hin, h1, h2⟩ := hblocks r hr
    rcases lt_or_eq_of_le hin with hlt' | rfl
    · exact Or.inl (h2.trans (hle _ _ (by omega) (by omega) (by omega)))
    · exact Or.inr h1
  have htop := hagopian76_property4_top hX hi D hY hYc hYO hfr hSBC h0 h12 hEs hgap
  refine false_of_property4_chain D x n (by omega)
    (by obtain ⟨y, hy, hess, hsep⟩ := htop; exact ⟨y, hy, hess, by rw [hxn]; exact hsep⟩) hstep ?_
  rw [hx1]
  exact not_property4_E hπ hπS hγπ hF hc₁ hR hD'c D hx2

/-- **F. The assembly, conditionally** (commission 177 §3.F). Set-up of `exists_T12Data_aux`, with
`D′` connected. For every `ε₃ > 0` and `K₀ ⊆ M` there is a `T12Data` package `D` (with
`D.K = K₀ ∪ {D.p}`) such that `SepByCrossing` for `D.p`, `f(D.p)`, the blocks `x₁ < ⋯ < x₂ₙ` of
`St J` (`n ≥ 2`, `x₁ = 0`, `d⁻¹[[0, x₂]] = E`, every member of `I` inside a block, `x₂ₙ = 1`) and
`Property4Step` give `False`.

Compared with `hagopian76_T15_T17_cond` (batch 176), the existence of the package and the set `Y`
(`π⁻¹[Fr D]`) are no longer hypotheses. -/
theorem hagopian76_T15_T17_cond2 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n₀ : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n₀ θ c) (hn₀ : 15 ≤ n₀) {c₁ : ℝ}
    (hc₁ : c₁ ≤ c) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (hD'c : IsPreconnected D')
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
    {t₀ w₂ : ℝ} (ht₀1 : 3 / 22 + 2 / (n₀ : ℝ) ≤ t₀) (ht₀2 : t₀ ≤ 19 / 22 - 2 / (n₀ : ℝ))
    (hw₂ : w₂ ∈ Ioc 0 c₁) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (K₀ : Set M) {ε₃ : ℝ} (hε₃ : 0 < ε₃) :
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧
      (SepByCrossing D.G π F c₁ D' (π ⁻¹' (F '' D')) D.p (D.f D.p) →
        ∀ (x : ℕ → unitInterval) (n : ℕ), 2 ≤ n → StrictMonoOn x (Icc 1 (2 * n)) → x 1 = 0 →
        layerSet D.d (Icc 0 (x 2)) = E →
        (∀ r ∈ crossingIntervals D.d π F c₁ D', ∃ i, 1 ≤ i ∧ i ≤ n ∧
          x (2 * i - 1) ≤ r.1 ∧ r.2 ≤ x (2 * i)) →
        x (2 * n) = 1 → Property4Step D x n → False) := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  obtain ⟨D, hDK, -⟩ := exists_T12Data_aux hX hi hE hπ hπS hγπ hF hS hn₀ hc₁ hR hbelow hI hIs
    hIR hDo hDf hFDf ht₀1 ht₀2 hw₂ hFw hseg K₀ hε₃
  obtain ⟨hYk, hYc, hYO, hfr⟩ := pi_preimage_frontier_D_aux hE hπ hπS hF (by norm_num)
    (by norm_num) (by norm_num) hc1 hI hIR hR.isOpen hFDf
  exact ⟨D, hDK, fun hSBC x n hn hx hx1 hx2 hblocks hxn hstep =>
    hagopian76_T15_T17_cond_fix hX hi hπ hπS hγπ hF hc1 hR hD'c D hYk hYc hYO hfr hSBC x n hn hx
      hx1 hx2 hblocks hxn hstep⟩

end T12Exists

end HPC.Hagopian
