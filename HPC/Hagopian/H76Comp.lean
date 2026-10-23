import HPC.Hagopian.Hagopian76V

/-!
# Batch 178, §4.A: the strands that matter miss `F` (by composants)

* `strand_misses_of_composant`: if `x₀ ∈ E`, `h x₀ ∉ composant x₀`, `G` is an extension of `E` away
  from `k⁻¹(0)`, and `K` is a proper subcontinuum of `M` through a point of `h[R(E)]` (for example
  the closure of the strand through it, `strand_lemma`), then `K ∩ G = ∅`.
* `hagopian76_T12_comp`: `hagopian76_T12_uncond` with the composant conditions `h x, h₁ x ∉
  composant x` exported (they are produced by `exists_generic_pq_comp_aux`).
* `exists_T12Data_comp`: `exists_T12Data_aux` with the base point `x₀` (`D.p = D.h x₀`) and both
  composant conditions; this is the companion `exists_T12Data'` of commission 178 §4.A (no field is
  added to `T12Data`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Comp

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **4.A, the composant argument** (commission 178 §4.A). -/
theorem strand_misses_of_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x₀ : M} (hx₀ : x₀ ∈ E)
    (h : M ≃ₜ M) (hhx : h x₀ ∉ Jones.composant x₀) {G : Set M}
    (hG : IsExtensionAway E (layer k 0) G) {z : M} (hz : z ∈ h '' Rset k) {K : Set M}
    (hK : Fold.Q78.IsContinuum K) (hKu : K ≠ univ) (hzK : z ∈ K) : Disjoint K G := by
  have hR := Rset_subset_composant hX hi hE hx₀
  have hGc : G ⊆ Jones.composant x₀ := fun g hg => hR (Or.inl ⟨G, hG, hg⟩)
  have hzc : z ∈ Jones.composant (h x₀) := by
    rw [← image_composant]; exact image_mono hR hz
  have hKc : K ⊆ Jones.composant (h x₀) :=
    (subset_composant hK hKu hzK).trans (composant_eq_of_mem hi hzc).subset
  have hnt : Nontrivial M := by
    obtain ⟨y₀, hy₀⟩ := hE.2.1.2.1 0
    obtain ⟨y₁, hy₁⟩ := hE.2.1.2.1 1
    refine ⟨⟨(y₀ : M), (y₁ : M), fun h => ?_⟩⟩
    have : y₀ = y₁ := Subtype.ext h
    rw [this, hy₁] at hy₀
    exact one_ne_zero hy₀
  rcases composant_eq_or_disjoint' hi (h x₀) x₀ with heq | hdis
  · exact absurd (heq ▸ mem_composant_self (h x₀)) hhx
  · exact disjoint_of_subset hKc hGc hdis

/-- `hagopian76_T12_uncond` with the composant conditions `h x, h₁ x ∉ composant x` exported. -/
theorem hagopian76_T12_comp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
    ∃ x : E, (k x : ℝ) = t₀ ∧ ∀ ε > 0, ∃ (h h₁ : M ≃ₜ M) (H : Set M),
      (∀ v, dist (h v) v < ε) ∧ (∀ v, dist (h₁ v) v < ε) ∧
      (∀ v, dist ((h.symm.trans h₁) v) v < 2 * ε) ∧ (h.symm.trans h₁) (h (x : M)) = h₁ (x : M) ∧
      IsExtensionAway E (layer k 0) H ∧
      SepIn (π ⁻¹' (F '' D')) (toPt H) (h (x : M)) (h₁ (x : M)) ∧
      Disjoint (h '' Rset k) (Rset k) ∧ Disjoint (h₁ '' Rset k) (Rset k) ∧
      h (x : M) ∉ Jones.composant (x : M) ∧ h₁ (x : M) ∉ Jones.composant (x : M) ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty := by
  obtain ⟨x, hkx, hmain⟩ := exists_generic_pq_comp_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1
    hbelow hI hIs hIR hDo hDR hDf hFDo hFDf ht₀ hw₂ hFw hseg
  refine ⟨x, hkx, fun ε hε => ?_⟩
  obtain ⟨h, h₁, -, -, H, -, hh, hh₁, -, -, hpC, hqC, -, -, -, hH, -, -, -, -, -, -, -, -, -, -,
    hsep, -, hcL, hcR, -, -⟩ := hmain ε hε
  refine ⟨h, h₁, H, hh, hh₁, fun v => ?_, by simp, hH, hsep,
    translate_Rset_disjoint hX hi hE x.2 h hpC, translate_Rset_disjoint hX hi hE x.2 h₁ hqC,
    hpC, hqC, hcL, hcR⟩
  have h1 := hh₁ (h.symm v)
  have h2 := hh (h.symm v)
  rw [h.apply_symm_apply] at h2
  calc dist ((h.symm.trans h₁) v) v ≤ dist (h₁ (h.symm v)) (h.symm v) + dist (h.symm v) v :=
        dist_triangle _ _ _
    _ < ε + ε := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = 2 * ε := by ring

/-- `exists_T12Data_aux` with the base point and both composant conditions (commission 178 §4.A,
`exists_T12Data'`). -/
theorem exists_T12Data_comp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧ ∃ x : E, (k x : ℝ) = t₀ ∧ D.p = D.h x ∧
      D.h (x : M) ∉ Jones.composant (x : M) ∧ D.h₁ (x : M) ∉ Jones.composant (x : M) := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hn0 : (0 : ℝ) < 2 / (n : ℝ) := by
    have : (15 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  obtain ⟨x, hkx, hmain⟩ := hagopian76_T12_comp hX hi hE hπ.continuous hπS hγπ hF
    (by norm_num) (by norm_num) (by norm_num) hc1 hbelow hI hIs hIR hDo hR.sub hDf hR.isOpen hFDf
    ⟨by linarith, by linarith⟩ hw₂ hFw hseg
  have hε : 0 < min (ε₃ / 2) (θ / 4) := lt_min (by linarith) (by linarith [hS.θ_pos])
  obtain ⟨h, h₁, H, hh, hh₁, -, -, hH, hsep, -, -, hpC, hqC, hne, -⟩ := hmain _ hε
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
    G d hG hEG hX0 (by rw [hq]; exact hGsep) (by rw [hq]; exact hirr), rfl, x, hkx, rfl, hpC, hqC⟩

/-- **4.A** (commission 178 §4.A): a `T12Data` package with base point `x₀` (`p = h x₀`) such that
every proper subcontinuum of `M` through a point of `h[R(E)] ∪ h₁[R(E)]` misses `F = D.G`. In
particular (`strand_lemma`: the closure of a strand is a proper subcontinuum) the strand of every
such point, e.g. `p`, `f(p) = h₁ x₀`, misses `F`. -/
theorem exists_T12Data_strands (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧ ∃ x : E, (k x : ℝ) = t₀ ∧ D.p = D.h x ∧
      ∀ z ∈ D.h '' Rset k ∪ D.h₁ '' Rset k, ∀ K : Set M, Fold.Q78.IsContinuum K → K ≠ univ →
        z ∈ K → Disjoint K D.G  := by
  obtain ⟨D, hDK, x, hkx, hpx, hpC, hqC⟩ := exists_T12Data_comp hX hi hE hπ hπS hγπ hF hS hn hc₁ hR
    hbelow hI hIs hIR hDo hDf hFDf ht₀1 ht₀2 hw₂ hFw hseg K₀ hε₃
  have hGext : IsExtensionAway E (layer k 0) D.G := ⟨D.hEG, D.d, D.hG, D.hX0⟩
  refine ⟨D, hDK, x, hkx, hpx, fun z hz K hK hKu hzK => ?_⟩
  rcases hz with hz | hz
  · exact strand_misses_of_composant hX hi hE x.2 D.h hpC hGext hz hK hKu hzK
  · exact strand_misses_of_composant hX hi hE x.2 D.h₁ hqC hGext hz hK hKu hzK

end Comp

end HPC.Hagopian
