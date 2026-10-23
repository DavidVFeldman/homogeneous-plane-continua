import HPC.Hagopian.H76Final179

/-!
# Batch 180, §1.2.2: the T15–T17 package with its composant data exposed

`hagopian76_T15_T17_cond3` builds its `T12Data` package from `exists_T12Data_strands`, which hides
the base point and the composant conditions. The three theorems below are the batch-179 theorems
with these clauses exported (commission 180 §1.2.2):

* `p_on_crossing_piece_comp`: `p_on_crossing_piece` (4.B), built directly on `exists_T12Data_comp`;
* `sep_by_crossing_uncond_comp`: `sep_by_crossing_uncond`;
* `hagopian76_T15_T17_cond4`: `hagopian76_T15_T17_cond3`.

The extra clause is: there is `x₀ ∈ E` with `k(x₀) = t₀`, `p = h(x₀)`, and `h(x₀)`, `h₁(x₀)` not in
the composant of `x₀`. The proofs are those of batch 179 with this clause carried along.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Cond4

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **4.B with the composant data** (commission 180 §1.2.2): `p_on_crossing_piece`, with the base
point `x₀` over `t₀`, `p = h x₀`, and `h x₀`, `h₁ x₀` off the composant of `x₀`. -/
theorem p_on_crossing_piece_comp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M}
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
    (hI2M : Disjoint I₂ (π '' M))
    {t₀ w₂ : ℝ} (ht₀1 : 3 / 22 + 2 / (n : ℝ) ≤ t₀) (ht₀2 : t₀ ≤ 19 / 22 - 2 / (n : ℝ))
    (hw₂ : w₂ ∈ Ioc 0 c₁) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (K₀ : Set M) {ε₃ : ℝ} (hε₃ : 0 < ε₃) :
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧
      (∃ x₀ : E, (k x₀ : ℝ) = t₀ ∧ D.p = D.h x₀ ∧ D.h (x₀ : M) ∉ Jones.composant (x₀ : M) ∧
        D.h₁ (x₀ : M) ∉ Jones.composant (x₀ : M)) ∧
      ∃ X Y : Set Pt, IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ X ∧
        IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ Y ∧
        (D.p : Pt) ∈ X ∧ ((D.f D.p : M) : Pt) ∈ Y ∧ (X = Y ∨ Disjoint X Y) ∧
        Disjoint X (toPt D.G) ∧ Disjoint Y (toPt D.G) := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hθ := hS.θ_pos
  have hε : 0 < min ε₃ (θ / 2) := lt_min hε₃ (by linarith)
  obtain ⟨D0, hDK, x, hkx, hpx, hpC, hqC⟩ := exists_T12Data_comp hX hi hE hπ hπS hγπ hF hS hn
    hc₁ hR hbelow hI hIs hIR hDo hDf hFDf ht₀1 ht₀2 hw₂ hFw hseg K₀ hε
  have hGext : IsExtensionAway E (layer k 0) D0.G := ⟨D0.hEG, D0.d, D0.hG, D0.hX0⟩
  have hmiss : ∀ z ∈ D0.h '' Rset k ∪ D0.h₁ '' Rset k, ∀ K : Set M, Fold.Q78.IsContinuum K →
      K ≠ univ → z ∈ K → Disjoint K D0.G := by
    intro z hz K hK hKu hzK
    rcases hz with hz | hz
    · exact strand_misses_of_composant hX hi hE x.2 D0.h hpC hGext hz hK hKu hzK
    · exact strand_misses_of_composant hX hi hE x.2 D0.h₁ hqC hGext hz hK hKu hzK
  have hsmall : ∀ v, dist (D0.h v) v < θ / 4 := fun v =>
    (D0.h_small v).trans_le (by linarith [min_le_right ε₃ (θ / 2)])
  have hsmall₁ : ∀ v, dist (D0.h₁ v) v < θ / 4 := fun v =>
    (D0.h₁_small v).trans_le (by linarith [min_le_right ε₃ (θ / 2)])
  set D : T12Data E k π F D' ε₃ := D0.mono (min_le_left _ _) with hDdef
  have hq : (D0.h.symm.trans D0.h₁) D0.p = D0.h₁ x := by rw [hpx]; simp
  have hsep := D0.sep
  rw [hq] at hsep
  have hyp : D0.h x ∈ crossSet univ π F D' := ⟨mem_univ _, by rw [← hpx]; exact hsep.1.1⟩
  have hyq : D0.h₁ x ∈ crossSet univ π F D' := ⟨mem_univ _, hsep.2.1.1⟩
  have hk1 : 3 / 22 + 2 / (n : ℝ) ≤ (k x : ℝ) := by rw [hkx]; exact ht₀1
  have hk2 : (k x : ℝ) ≤ 19 / 22 - 2 / (n : ℝ) := by rw [hkx]; exact ht₀2
  have hCp := (strand_crossing hX hi hE hπ.continuous hπS hγπ hF hS hn hc₁ hR D0.h hsmall x hyp
    hk1 hk2).1
  have hCq := (strand_crossing hX hi hE hπ.continuous hπS hγπ hF hS hn hc₁ hR D0.h₁ hsmall₁ x
    hyq hk1 hk2).1
  set Cp := connectedComponentIn (crossSet univ π F D') (D0.h x) with hCpdef
  set Cq := connectedComponentIn (crossSet univ π F D') (D0.h₁ x) with hCqdef
  have hxR : (x : M) ∈ Rset k := subset_Rset hE x.2
  have hmissC : ∀ (C : Set M) (z : M), IsCrossingComponent univ π F c₁ D' C → z ∈ C →
      z ∈ D0.h '' Rset k ∪ D0.h₁ '' Rset k → Disjoint (closure C) D0.G := fun C z hC hzC hz =>
    hmiss z hz (closure C) ⟨isClosed_closure.isCompact, hC.isConnected.closure⟩
      (closure_ne_univ_of_crossSet hE hπ.continuous hγπ hF hc1 hR hC.subset)
      (subset_closure hzC)
  have hdp := hmissC Cp _ hCp (mem_connectedComponentIn hyp) (Or.inl ⟨x, hxR, rfl⟩)
  have hdq := hmissC Cq _ hCq (mem_connectedComponentIn hyq) (Or.inr ⟨x, hxR, rfl⟩)
  have hEp : Disjoint (closure Cp) E := hdp.mono_right D0.hEG
  have hEq : Disjoint (closure Cq) E := hdq.mono_right D0.hEG
  have htoPt : ∀ C : Set M, Disjoint (closure C) D0.G → Disjoint (toPt C) (toPt D0.G) := by
    intro C hC
    rw [disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ ⟨m', hm', hmm'⟩
    have : m' = m := Subtype.ext hmm'
    subst this
    exact disjoint_left.1 hC (subset_closure hm) hm'
  refine ⟨D, hDK, ⟨x, hkx, hpx, hpC, hqC⟩, toPt Cp, toPt Cq,
    isCrossingPiece_of_crossingComponent hE hπ.continuous hπS hγπ hF hc1 hR hIs hFDf hI2M hCp hEp,
    isCrossingPiece_of_crossingComponent hE hπ.continuous hπS hγπ hF hc1 hR hIs hFDf hI2M hCq hEq,
    ?_, ?_, ?_, htoPt Cp hdp, htoPt Cq hdq⟩
  · show ((D0.p : M) : Pt) ∈ toPt Cp
    rw [hpx]; exact ⟨_, mem_connectedComponentIn hyp, rfl⟩
  · show (((D0.h.symm.trans D0.h₁) D0.p : M) : Pt) ∈ toPt Cq
    rw [hq]; exact ⟨_, mem_connectedComponentIn hyq, rfl⟩
  · by_cases hmem : D0.h₁ x ∈ Cp
    · left
      rw [hCpdef, connectedComponentIn_eq hmem]
    · right
      rw [disjoint_left]
      rintro _ ⟨m, hm, rfl⟩ ⟨m', hm', hmm'⟩
      have : m' = m := Subtype.ext hmm'
      subst this
      apply hmem
      rw [hCpdef, connectedComponentIn_eq hm, ← connectedComponentIn_eq hm']
      exact mem_connectedComponentIn hyq

/-- **`sep_by_crossing_uncond` with the composant data** (commission 180 §1.2.2). -/
theorem sep_by_crossing_uncond_comp (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
      (∃ x₀ : E, (k x₀ : ℝ) = t₀ ∧ D.p = D.h x₀ ∧ D.h (x₀ : M) ∉ Jones.composant (x₀ : M) ∧
        D.h₁ (x₀ : M) ∉ Jones.composant (x₀ : M)) ∧
      ∀ lo hi : ℝ, lo < t₀ → t₀ < hi →
        InnerComponentsCross D.G π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ lo hi →
        SepByCrossing D.G π F c₁ D' (π ⁻¹' (F '' D')) D.p (D.f D.p) := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hn0 : (0 : ℝ) < 2 / (n : ℝ) := by
    have : (15 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  obtain ⟨D, hDK, hcomp, X, Y, hX', hY', hpX, hqY, hXY, hXG, hYG⟩ := p_on_crossing_piece_comp hX hi hE hπ hπS
    hγπ hF hS hn hc₁ hR hbelow hI hIs hIR hDo hDf hFDf hI2M ht₀1 ht₀2 hw₂ hFw hseg K₀ hε₃
  refine ⟨D, hDK, hcomp, fun lo hi hlo hhi hICC => ?_⟩
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

/-- **§1.2.2: T15–T17 with the composant data exposed** (commission 180 §1.2.2; the shape left
open in the skeleton). `hagopian76_T15_T17_cond3`, whose package also carries: a base point
`x₀ ∈ E` over `t₀` with `p = h x₀`, and `h x₀`, `h₁ x₀` outside the composant of `x₀`. -/
theorem hagopian76_T15_T17_cond4 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
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
          x (2 * m) = 1 → Property4Step D x m) → False := by
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
  obtain ⟨-, -, -, x, m, hm, hx, hx1, hx2, hblocks, hxn, -, -⟩ :=
    hblk D.G D.d D.hG D.hEG D.hX0 c₁ D' (hcU.trans (min_le_right _ _)) hR hlast
  obtain ⟨hYk, hYc, hYO, hfr⟩ := pi_preimage_frontier_D_aux hE hπ hπS hF (by norm_num)
    (by norm_num) (by norm_num) hc1 hI hIR hR.isOpen hFDf
  exact hagopian76_T15_T17_cond_fix hX hi hπ hπS hγπ hF hc1 hR hD'c D hYk hYc hYO hfr hSBC x m
    hm hx hx1 hx2 hblocks hxn (hstep x m hm hx hx1 hx2 hblocks hxn)

end Cond4

end HPC.Hagopian
