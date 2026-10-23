import HPC.Hagopian.H76Strand

/-!
# Batch 177: uses of the strand lemma (commission 177 §2 S1+S3, S5, S6; §3 A, B)

* `strand_inner_middle`: every point of `M` over the inner middle `[3/22 + 3/n, 19/22 − 3/n]` of `D`
  lies on a strand: a crossing component whose closure is in a `θ/4`-translate `h[E]` and contains
  `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`.
* `strand_fine_positions_aux` (S6), `typeA'_strand_aux` (S5, the whole-strand part).
* `val_preimage_connectedComponentIn`: components in the plane and in `M` agree.
* `strand_essential`: `h⁻¹[Cl C]` is essential to `R(E)` (Hagopian's "by Lemma 5", p. 347).
* `exists_T12Data_aux`: a `T12Data` exists (item A).
* `pi_preimage_continuum`, `frontier_D_continuum`: `π⁻¹[Fr D]` is compact and connected (item B).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section StrandUse

variable {M : Set Pt}

theorem crossSet_univ_eq (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) :
    crossSet (univ : Set M) π F D' = {m : M | π (m : Pt) ∈ F '' D'} := by
  ext m; simp [crossSet]

/-- **Components in the plane and in `M` agree**: the trace on `M` of the component of
`M ∩ π⁻¹[A]` through `y` is the component of `{m ∈ M | π(m) ∈ A}` through `y`. -/
theorem val_preimage_connectedComponentIn (π : Pt → Pt) (A : Set Pt) (y : M) :
    Subtype.val ⁻¹' connectedComponentIn (M ∩ π ⁻¹' A) (y : Pt) =
      connectedComponentIn {m : M | π (m : Pt) ∈ A} y := by
  by_cases hy : π (y : Pt) ∈ A
  · apply Subset.antisymm
    · set X := Subtype.val ⁻¹' connectedComponentIn (M ∩ π ⁻¹' A) (y : Pt) with hX
      have hsubM : connectedComponentIn (M ∩ π ⁻¹' A) (y : Pt) ⊆ M :=
        (connectedComponentIn_subset _ _).trans inter_subset_left
      have himg : Subtype.val '' X = connectedComponentIn (M ∩ π ⁻¹' A) (y : Pt) := by
        rw [hX, Subtype.image_preimage_coe, inter_eq_right.2 hsubM]
      have hXc : IsPreconnected X := by
        rw [← IsInducing.subtypeVal.isPreconnected_image, himg]
        exact isPreconnected_connectedComponentIn
      refine hXc.subset_connectedComponentIn (mem_connectedComponentIn ⟨y.2, hy⟩) ?_
      intro m hm
      exact (connectedComponentIn_subset _ _ hm).2
    · intro m hm
      have hc : IsPreconnected (Subtype.val '' connectedComponentIn {m : M | π (m : Pt) ∈ A} y) :=
        isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
      refine hc.subset_connectedComponentIn ⟨y, mem_connectedComponentIn hy, rfl⟩ ?_
        ⟨m, hm, rfl⟩
      rintro _ ⟨m', hm', rfl⟩
      exact ⟨m'.2, (connectedComponentIn_subset {m : M | π (m : Pt) ∈ A} y hm' :)⟩
  · rw [connectedComponentIn_eq_empty (F := {m : M | π (m : Pt) ∈ A}) hy,
      connectedComponentIn_eq_empty (F := M ∩ π ⁻¹' A) (x := (y : Pt)) (fun h => hy h.2),
      preimage_empty]

/-- The closure version of `val_preimage_connectedComponentIn`. -/
theorem val_preimage_closure_connectedComponentIn (π : Pt → Pt) (A : Set Pt) (y : M) :
    Subtype.val ⁻¹' closure (connectedComponentIn (M ∩ π ⁻¹' A) (y : Pt)) =
      closure (connectedComponentIn {m : M | π (m : Pt) ∈ A} y) := by
  have hsubM : connectedComponentIn (M ∩ π ⁻¹' A) (y : Pt) ⊆ M :=
    (connectedComponentIn_subset _ _).trans inter_subset_left
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, ← val_preimage_connectedComponentIn,
    Subtype.image_preimage_coe, inter_eq_right.2 hsubM]

variable [CompactSpace M] [ConnectedSpace M]

/-- **S1 + S3 over the inner middle** (commission 177 §2). Set-up of `strand_crossing`. Every
`y ∈ M` over a point `z ∈ D′` with `3/22 + 3/n ≤ z₁ ≤ 19/22 − 3/n` is `h(e)` for a
`θ/4`-homeomorphism `h`; the component `C` of `M ∩ π⁻¹[D]` through `y` is a crossing component (a
**strand**), `Cl C ⊆ h[E]`, and `Cl C ⊇ h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`. -/
theorem strand_inner_middle (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (y : M) (z : ℝ × ℝ) (hzD : z ∈ D')
    (hyz : π (y : Pt) = F z) (hz1 : 3 / 22 + 3 / (n : ℝ) ≤ z.1)
    (hz2 : z.1 ≤ 19 / 22 - 3 / (n : ℝ)) :
    ∃ h : M ≃ₜ M, (∀ v, dist (h v) v < θ / 4) ∧ ∃ e : E, h e = y ∧
      closure (connectedComponentIn (crossSet univ π F D') y) ⊆ h '' E ∧
      IsCrossingComponent univ π F c₁ D' (connectedComponentIn (crossSet univ π F D') y) ∧
      h '' layerSet k {t | 3 / 22 + 2 / (n : ℝ) < (t : ℝ) ∧ (t : ℝ) < 19 / 22 - 2 / (n : ℝ)} ⊆
        closure (connectedComponentIn (crossSet univ π F D') y) := by
  have hzS := hR.sub hzD
  obtain ⟨h, hh, e, rfl, hke⟩ := hS.translate y z
    ⟨⟨hzS.1.1.le.trans' (by norm_num), hzS.1.2.le.trans (by norm_num)⟩,
      by linarith [hzS.2.1, hS.c_pos], by linarith [hzS.2.2]⟩ hyz
  obtain ⟨hk1, hk2⟩ := abs_lt.1 hke
  have h3 : (3 : ℝ) / n = 2 / n + 1 / n := by ring
  have hy : h e ∈ crossSet univ π F D' := ⟨trivial, z, hzD, hyz.symm⟩
  have he1 : 3 / 22 + 2 / (n : ℝ) ≤ (k e : ℝ) := by linarith
  have he2 : (k e : ℝ) ≤ 19 / 22 - 2 / (n : ℝ) := by linarith
  obtain ⟨hcr, yL, yR, -, -, hL, hR', -, -, hmid⟩ := strand_crossing hX hi hE hπc hπS hγπ hF hS hn
    hc₁ hR h hh e hy he1 he2
  refine ⟨h, hh, e, rfl, strand_closure_subset hX hi hE hπc hF hS hn hc₁ hR h hh e, hcr,
    (image_mono (layerSet_mono k fun t ht => ?_)).trans hmid⟩
  obtain ⟨-, hL1⟩ := abs_lt.1 hL
  obtain ⟨hR2, -⟩ := abs_lt.1 hR'
  exact ⟨by show (k yL : ℝ) < t; linarith [ht.1], by show (t : ℝ) < k yR; linarith [ht.2]⟩

/-- **S6: fine positions** (commission 177 §2, S6). Set-up of `strand_closure_subset`. Every point
`q` of the closure of the component of `M ∩ π⁻¹[D]` through `h(e)`, over the thin strip at abscissa
`s`, is `h(t)` with `|k(t) − s| < 2/n`. -/
theorem strand_fine_positions_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    (hπc : Continuous π) {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {n : ℕ}
    {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (e : E) (q : M)
    (hq : q ∈ closure (connectedComponentIn (crossSet univ π F D') (h e))) (w : ℝ × ℝ)
    (hw : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-c) c) (hqw : π (q : Pt) = F w) :
    ∃ t : E, h t = q ∧ |(k t : ℝ) - w.1| < 2 / (n : ℝ) := by
  obtain ⟨t, ht, rfl⟩ := strand_closure_subset hX hi hE hπc hF hS hn hc₁ hR h hh e hq
  exact ⟨⟨t, ht⟩, rfl, hS.fine h hh ⟨t, ht⟩ w hw hqw⟩

/-- **S5, the whole-strand part** (commission 177 §2, S5). Let `G ⊆ M` be type A′ (minimal
admissible `d`), `y ∈ G`, and let `S` be the component of `M ∩ π⁻¹[D]` through `y`, with `Cl S`
missing the end sets `d⁻¹(0)`, `d⁻¹(1)`. Then `Cl S ⊆ G` (no hair for `G`), and `S` is the component
of `G ∩ π⁻¹[D]` through `y`. -/
theorem typeA'_strand_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) {π : Pt → Pt} {F : ℝ × ℝ → Pt}
    {D' : Set (ℝ × ℝ)} (y : M) (hyG : y ∈ G)
    (h0 : Disjoint (closure (connectedComponentIn (crossSet univ π F D') y)) (layer d 0))
    (h1 : Disjoint (closure (connectedComponentIn (crossSet univ π F D') y)) (layer d 1)) :
    closure (connectedComponentIn (crossSet univ π F D') y) ⊆ G ∧
      connectedComponentIn (crossSet G π F D') y =
        connectedComponentIn (crossSet univ π F D') y := by
  have hGU : crossSet G π F D' ⊆ crossSet univ π F D' := fun m hm => ⟨trivial, hm.2⟩
  by_cases hy : y ∈ crossSet univ π F D'
  · have hQ : Fold.Q78.IsContinuum (closure (connectedComponentIn (crossSet univ π F D') y)) :=
      ⟨isClosed_closure.isCompact, ⟨y, subset_closure (mem_connectedComponentIn hy)⟩,
        isPreconnected_connectedComponentIn.closure⟩
    have hsub := hagopian76_no_hair hX hi hG hQ
      ⟨y, subset_closure (mem_connectedComponentIn hy), hyG⟩ h0 h1
    refine ⟨hsub, Subset.antisymm (connectedComponentIn_mono _ hGU) ?_⟩
    refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hy) fun m hm => ⟨hsub (subset_closure hm), ?_⟩
    exact (connectedComponentIn_subset _ _ hm).2
  · rw [connectedComponentIn_eq_empty hy, connectedComponentIn_eq_empty (fun h => hy (hGU h)),
      closure_empty]
    exact ⟨empty_subset _, rfl⟩

/-- **S5 for an extension of `E` away from `k⁻¹(0)`** (commission 177 §2, S5: "For Hagopian's `F`,
`d⁻¹(0) = k⁻¹(0)` is not over `Cl D`, so only `d⁻¹(1)` can produce an end strand"). Set-up of
`strand_inner_middle`; `G` type A′ with `d⁻¹(0) = k⁻¹(0)`. If `y ∈ G` is over the inner middle and
the closure of its strand misses `d⁻¹(1)`, then the component of `G ∩ π⁻¹[D]` through `y` is that
strand, and it is a crossing component of `G`. -/
theorem typeA'_inner_crossing (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0) (y : M) (hyG : y ∈ G)
    (z : ℝ × ℝ) (hzD : z ∈ D') (hyz : π (y : Pt) = F z) (hz1 : 3 / 22 + 3 / (n : ℝ) ≤ z.1)
    (hz2 : z.1 ≤ 19 / 22 - 3 / (n : ℝ))
    (h1 : Disjoint (closure (connectedComponentIn (crossSet univ π F D') y)) (layer d 1)) :
    connectedComponentIn (crossSet G π F D') y = connectedComponentIn (crossSet univ π F D') y ∧
      IsCrossingComponent G π F c₁ D' (connectedComponentIn (crossSet G π F D') y) := by
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  obtain ⟨h, hh, e, rfl, -, hcr, -⟩ := strand_inner_middle hX hi hE hπc hπS hγπ hF hS hn hc₁ hR
    y z hzD hyz hz1 hz2
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  have hclD : closure (F '' D') ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    closure_minimal hDsub (isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc)
      (rect_sub (by norm_num) (by norm_num) hc1)).isClosed
  have h0 : Disjoint (closure (connectedComponentIn (crossSet univ π F D') (h e))) (layer d 0) := by
    rw [hX0, disjoint_left]
    rintro q hq ⟨e', he', rfl⟩
    have hke : (k e' : ℝ) = 0 := by
      rw [mem_preimage, mem_singleton_iff] at he'; rw [he']; rfl
    have hcl : π ((e' : M) : Pt) ∈ closure (F '' D') :=
      closure_minimal (s := connectedComponentIn (crossSet univ π F D') (h e))
        (t := {m : M | π (m : Pt) ∈ closure (F '' D')})
        (fun m hm => subset_closure (connectedComponentIn_subset (crossSet univ π F D') _ hm).2)
        (isClosed_closure.preimage (hπc.comp continuous_subtype_val)) hq
    obtain ⟨w, hw, hFw⟩ := hclD hcl
    have := collar_injOn hF ⟨⟨(k e').2.1, (k e').2.2⟩, by norm_num, by norm_num⟩
      ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      ((pi_E_eq hγπ hF e').symm.trans hFw.symm)
    have : (k e' : ℝ) = w.1 := congrArg Prod.fst this
    linarith [hw.1.1]
  obtain ⟨-, heq⟩ := typeA'_strand_aux hX hi hG (h e) hyG h0 h1
  refine ⟨heq, ?_⟩
  rw [heq]
  obtain ⟨-, h3, h19⟩ := hcr
  exact ⟨⟨h e, ⟨hyG, z, hzD, hyz.symm⟩, heq.symm⟩, h3, h19⟩

/-- **Strands are essential** (p. 347, "by Lemma 5, `h⁻¹[Cl C]` is essential to `R(E)`";
commission 177 §3.A). Set-up of `strand_crossing`: if `h(e)` is over `D` with
`3/22 + 2/n ≤ k(e) ≤ 19/22 − 2/n`, then `h⁻¹` of the closure of the component of `M ∩ π⁻¹[D]` (in
the plane) through `h(e)` is essential to `R(E)`. -/
theorem strand_essential (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (e : E) (hy : π (h e : Pt) ∈ F '' D')
    (he1 : 3 / 22 + 2 / (n : ℝ) ≤ (k e : ℝ)) (he2 : (k e : ℝ) ≤ 19 / 22 - 2 / (n : ℝ)) :
    IsEssential k (h ⁻¹' (Subtype.val ⁻¹'
      closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h e : Pt)))) := by
  have hn' : (2 : ℝ) / n ≤ 2 / 15 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (15 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [val_preimage_closure_connectedComponentIn, ← crossSet_univ_eq]
  have hyc : h e ∈ crossSet univ π F D' := ⟨trivial, hy⟩
  set C := connectedComponentIn (crossSet univ π F D') (h e) with hCdef
  have hsub := strand_closure_subset hX hi hE hπc hF hS hn hc₁ hR h hh e
  obtain ⟨-, yL, yR, -, -, hL, hR', hyL, hyR, -⟩ := strand_crossing hX hi hE hπc hπS hγπ hF hS hn
    hc₁ hR h hh e hyc he1 he2
  have hHE : h ⁻¹' closure C ⊆ E := by
    intro x hx
    obtain ⟨x', hx', hxx'⟩ := hsub hx
    rw [h.injective hxx'] at hx'
    exact hx'
  refine ⟨hHE.trans (subset_Rset hE), ?_, E, k, subset_rfl, hE, Or.inl rfl, k yL, k yR, ?_,
    ⟨yL, hyL, ⟨yL, rfl, rfl⟩⟩, ⟨yR, hyR, ⟨yR, rfl, rfl⟩⟩⟩
  · rw [← h.image_symm]
    exact isContinuum_homeo_image h.symm ⟨isClosed_closure.isCompact,
      ⟨h e, subset_closure (mem_connectedComponentIn hyc)⟩,
      isPreconnected_connectedComponentIn.closure⟩
  · intro heq
    obtain ⟨hL1, -⟩ := abs_lt.1 hL
    obtain ⟨hR1, -⟩ := abs_lt.1 hR'
    have : (k yL : ℝ) = k yR := congrArg Subtype.val heq
    obtain ⟨-, hL2⟩ := abs_lt.1 hL
    linarith

end StrandUse

end HPC.Hagopian
