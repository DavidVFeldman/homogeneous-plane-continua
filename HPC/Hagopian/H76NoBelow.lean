import HPC.Hagopian.Hagopian76G
import HPC.Hagopian.H76AdaptMain

/-!
# Batch 163, item B: no point of `π[M]` just below `π[E]` (the argument of Lemma 9, made general)

The route of commission 163 §1, with three changes recorded in the report:
* the point `z ∈ M − E` below `π[E]` is reached by a sequence: if no strip works, points `zₙ` of `M`
  with `π(zₙ)` below `γ[[a, b]]` at heights `→ 0` accumulate at a point `u` of some layer
  `U = k⁻¹(a′)`, `a ≤ a′ ≤ b`, and Lemma 2 at `u` gives `h(u) = zₙ` (no compactness over `a′`);
* Hagopian's unargued "`G₂ ∩ E` and `G₂ ∩ h[E]` are disjoint" is replaced by what the argument uses,
  `h[D] ∩ C = ∅`, proved from the 1975 ¶9 lemma (`subset_of_meets_avoids`) applied to the piece
  `h[k⁻¹[[a′, s]]]`, `s < 1`, which meets `E`, contains `h(u) ∉ E` and avoids the end sets;
* the links of the chain at the ends are collar rectangles together with a small disc about
  `γ 0` (resp. `γ 1`), so that they are open in the plane.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section NoBelow

variable {M : Set Pt}

/-- A point of `M` over `γ t` lies in the layer `k⁻¹(t)`. -/
theorem mem_layer_of_pi_eq {E : Set M} {k : E → unitInterval} (hk : Function.Surjective k)
    {π : Pt → Pt} {γ : unitInterval → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {m : M} {t : unitInterval}
    (h : π m = γ t) : m ∈ layer k t := by
  obtain ⟨e, he⟩ := hk t
  have hx : ((e : M) : Pt) ∈ toPt (layer k t) := ⟨e, ⟨e, he, rfl⟩, rfl⟩
  have hrel := (hπS m e).1 (h.trans (hγπ t _ hx).symm)
  change layerKey k (m : Pt) = layerKey k ((e : M) : Pt) at hrel
  rw [layerKey_of_mem] at hrel
  by_cases hm : (m : Pt) ∈ toPt E
  · obtain ⟨e', he'⟩ := mem_toPt_iff.1 hm
    have hme : (e' : M) = m := Subtype.ext he'
    rw [← he', layerKey_of_mem] at hrel
    have : k e' = t := by rw [← he]; exact Sum.inl_injective hrel
    exact ⟨e', this, hme⟩
  · rw [layerKey_of_notMem k hm] at hrel
    exact absurd hrel Sum.inr_ne_inl

/-- Layer sets over disjoint parameter sets are disjoint. -/
theorem disjoint_toPt_layerSet {E : Set M} (k : E → unitInterval) {S T : Set unitInterval}
    (h : Disjoint S T) : Disjoint (toPt (layerSet k S)) (toPt (layerSet k T)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩ ⟨_, ⟨e', he', rfl⟩, h'⟩
  have : e' = e := Subtype.ext (Subtype.ext h')
  subst this
  exact Set.disjoint_left.1 h he he'

/-- **Points of `M` whose image is near `γ[T]` are near `k⁻¹[T]`** (upper semicontinuity of the
decomposition, through `π`). -/
theorem layer_close_of_pi_close [CompactSpace M] {E : Set M} {k : E → unitInterval}
    (hk : Function.Surjective k) {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    (hγc : Continuous γ) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {T : Set unitInterval} (hT : IsClosed T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ m : M, ∀ t ∈ T, dist (π m) (γ t) < η →
      (m : Pt) ∈ thickening ε (toPt (layerSet k T)) := by
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · exact ⟨1, one_pos, fun m t ht => by rw [hT0] at ht; exact absurd ht (notMem_empty t)⟩
  set S := {m : M | (m : Pt) ∉ thickening ε (toPt (layerSet k T))} with hS
  have hSc : IsClosed S :=
    (isOpen_thickening.preimage continuous_subtype_val).isClosed_compl
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · refine ⟨1, one_pos, fun m t _ _ => ?_⟩
    by_contra h
    have : m ∈ S := h
    rw [hS0] at this; exact this
  have hγT : IsCompact (γ '' T) := hT.isCompact.image hγc
  set f : M → ℝ := fun m => infDist (π m) (γ '' T) with hf
  have hfc : Continuous f := (continuous_infDist_pt _).comp (hπc.comp continuous_subtype_val)
  obtain ⟨m₀, hm₀S, hm₀⟩ := hSc.isCompact.exists_isMinOn hSne hfc.continuousOn
  have hpos : 0 < f m₀ := by
    rcases (infDist_nonneg : 0 ≤ f m₀).lt_or_eq with h | h
    · exact h
    exfalso
    have hmem : π m₀ ∈ γ '' T := by
      rw [hγT.isClosed.mem_iff_infDist_zero (hTne.image γ)]
      exact h.symm
    obtain ⟨t, ht, hte⟩ := hmem
    have hl := mem_layer_of_pi_eq hk hπS hγπ hte.symm
    apply hm₀S
    obtain ⟨e, he, hee⟩ := hl
    refine self_subset_thickening hε _ ⟨m₀, ⟨e, ?_, hee⟩, rfl⟩
    show k e ∈ T
    rw [show k e = t from he]; exact ht
  refine ⟨f m₀, hpos, fun m t ht hd => ?_⟩
  by_contra h
  have hmS : m ∈ S := h
  have := hm₀ hmS
  have h2 : f m ≤ dist (π m) (γ t) := infDist_le_dist_of_mem (mem_image_of_mem γ ht)
  simp only [mem_setOf_eq] at this
  linarith

/-- Images of open subsets of the open rectangle under a collar are open. -/
theorem IsCollar.isOpen_image {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hWO : W ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) :
    IsOpen (F '' W) := by
  obtain ⟨hemb, -, hopen⟩ := hF
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hOK : Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hW' : IsOpen {q : K | (q : ℝ × ℝ) ∈ W} := hW.preimage continuous_subtype_val
  obtain ⟨T, hT, hTe⟩ := hemb.isInducing.isOpen_iff.1 hW'
  have : F '' W = F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ∩ T := by
    apply Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨⟨q, hWO hq, rfl⟩, ?_⟩
      have : (⟨q, hOK (hWO hq)⟩ : K) ∈ K.restrict F ⁻¹' T := by rw [hTe]; exact hq
      exact this
    · rintro _ ⟨⟨q, hq, rfl⟩, hT'⟩
      have : (⟨q, hOK hq⟩ : K) ∈ K.restrict F ⁻¹' T := hT'
      rw [hTe] at this
      exact ⟨q, this, rfl⟩
  rw [this]; exact hopen.inter hT

/-- A collar moves the axis uniformly little at small heights. -/
theorem IsCollar.uniform_height {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {η : ℝ} (hη : 0 < η) :
    ∃ c > 0, c ≤ 1 ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ s, |s| ≤ c → dist (F (x, s)) (F (x, 0)) < η := by
  obtain ⟨hemb, -, -⟩ := hF
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hFc : ContinuousOn F K := continuousOn_iff_continuous_restrict.2 hemb.continuous
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hFc
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.1 hu η hη
  refine ⟨min (δ / 2) 1, lt_min (half_pos hδ) one_pos, min_le_right _ _, fun x hx s hs => ?_⟩
  have hs1 : |s| ≤ 1 := hs.trans (min_le_right _ _)
  refine hδF (x, s) ⟨hx, ?_⟩ (x, 0) ⟨hx, by norm_num⟩ ?_
  · rw [abs_le] at hs1; exact ⟨hs1.1, hs1.2⟩
  · rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
    have : |s| < δ := lt_of_le_of_lt (hs.trans (min_le_left _ _)) (by linarith)
    simpa using this

/-- A closed ball about a point off a closed set, missing it. -/
theorem exists_closedBall_disjoint {A : Set Pt} (hA : IsClosed A) {p : Pt} (hp : p ∉ A) :
    ∃ r > 0, Disjoint (closedBall p r) A := by
  obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 hA.isOpen_compl p hp
  refine ⟨r / 2, half_pos hr, Set.disjoint_left.2 fun q hq hqA => hrA ?_ hqA⟩
  rw [mem_ball]; rw [mem_closedBall] at hq; linarith

/-- **The three-link chain of collar rectangles** (Hagopian p. 344: "Let `G = {G₁, G₂, G₃}` be a
chain in `R²` that follows `E` such that … `π[Gᵢ]` is an open disk"). The end links are collar
rectangles with a small disc about `γ 0` (resp. `γ 1`) added, so that they are open. -/
theorem chain3_follows {E : Set M} {k : E → unitInterval} (hk : Function.Surjective k)
    {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {α β₁ ζ₃ ζ₂ : ℝ} (hα : 0 < α) (hαβ : α < β₁) (hβζ : β₁ < ζ₃) (hζζ : ζ₃ < ζ₂) (hζ1 : ζ₂ < 1)
    {c₁ c' r₀ r₂ : ℝ} (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc' : 0 < c') (hc'1 : c' ≤ 1)
    (hr₀ : 0 < r₀) (hr₂ : 0 < r₂)
    (hr₀F : Disjoint (closedBall (γ 0) r₀) (F '' (Icc β₁ 1 ×ˢ Icc (-1) 1)))
    (hr₂F : Disjoint (closedBall (γ 1) r₂) (F '' (Icc 0 ζ₃ ×ˢ Icc (-1) 1)))
    (hr : r₀ + r₂ < dist (γ 0) (γ 1)) (G : Fin 3 → Set Pt)
    (hG : G = ![π ⁻¹' (F '' (Ioo 0 β₁ ×ˢ Ioo (-c₁) c₁) ∪ ball (γ 0) r₀),
      π ⁻¹' (F '' (Ioo α ζ₂ ×ˢ Ioo (-c') c')),
      π ⁻¹' (F '' (Ioo ζ₃ 1 ×ˢ Ioo (-c₁) c₁) ∪ ball (γ 1) r₂)]) :
    IsPlaneChain G ∧ Follows G k := by
  have hF' := hF
  obtain ⟨hemb, h0, -⟩ := hF'
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hFinj : InjOn F K := fun p hp q hq e =>
    congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) e)
  set R0 := F '' (Ioo 0 β₁ ×ˢ Ioo (-c₁) c₁) ∪ ball (γ 0) r₀ with hR0
  set R1 := F '' (Ioo α ζ₂ ×ˢ Ioo (-c') c') with hR1
  set R2 := F '' (Ioo ζ₃ 1 ×ˢ Ioo (-c₁) c₁) ∪ ball (γ 1) r₂ with hR2
  have hG0 : G 0 = π ⁻¹' R0 := by rw [hG]; rfl
  have hG1 : G 1 = π ⁻¹' R1 := by rw [hG]; rfl
  have hG2 : G 2 = π ⁻¹' R2 := by rw [hG]; rfl
  have hGl : G (Fin.last 2) = π ⁻¹' R2 := hG2
  have hKmem : ∀ {x s : ℝ}, x ∈ Icc (0 : ℝ) 1 → |s| ≤ 1 → (x, s) ∈ K := fun hx hs =>
    ⟨hx, (abs_le.1 hs).1, (abs_le.1 hs).2⟩
  have hγF : ∀ t : unitInterval, γ t = F ((t : ℝ), 0) := fun t => (h0 t).symm
  have hγK : ∀ t : unitInterval, ((t : ℝ), (0 : ℝ)) ∈ K := fun t => hKmem t.2 (by simp)
  -- where `γ t` lies
  have g0 : ∀ t : unitInterval, (t : ℝ) < β₁ → γ t ∈ R0 := by
    intro t ht
    rcases eq_or_lt_of_le t.2.1 with h | h
    · right
      have : t = 0 := Subtype.ext h.symm
      rw [this]; exact mem_ball_self hr₀
    · left
      exact ⟨((t : ℝ), 0), ⟨⟨h, ht⟩, by linarith, hc₁⟩, (hγF t).symm⟩
  have g0' : ∀ t : unitInterval, γ t ∈ R0 → (t : ℝ) < β₁ := by
    intro t ht
    by_contra hc
    push_neg at hc
    rcases ht with ⟨q, ⟨⟨hq1, hq2⟩, hq3, hq4⟩, hqe⟩ | hb
    · rw [hγF] at hqe
      have := hFinj (hKmem ⟨hq1.le, by linarith⟩ (abs_le.2 ⟨by linarith, by linarith⟩))
        (hγK t) hqe
      have := congrArg Prod.fst this
      simp only at this
      linarith
    · exact Set.disjoint_left.1 hr₀F (ball_subset_closedBall hb)
        ⟨((t : ℝ), 0), ⟨⟨hc, t.2.2⟩, by norm_num, by norm_num⟩, (hγF t).symm⟩
  have g1 : ∀ t : unitInterval, α < (t : ℝ) → (t : ℝ) < ζ₂ → γ t ∈ R1 := fun t h1 h2 =>
    ⟨((t : ℝ), 0), ⟨⟨h1, h2⟩, by linarith, hc'⟩, (hγF t).symm⟩
  have g2 : ∀ t : unitInterval, ζ₃ < (t : ℝ) → γ t ∈ R2 := by
    intro t ht
    rcases eq_or_lt_of_le t.2.2 with h | h
    · right
      have : t = 1 := Subtype.ext h
      rw [this]; exact mem_ball_self hr₂
    · left
      exact ⟨((t : ℝ), 0), ⟨⟨ht, h⟩, by linarith, hc₁⟩, (hγF t).symm⟩
  have g2' : ∀ t : unitInterval, γ t ∈ R2 → ζ₃ < (t : ℝ) := by
    intro t ht
    by_contra hc
    push_neg at hc
    rcases ht with ⟨q, ⟨⟨hq1, hq2⟩, hq3, hq4⟩, hqe⟩ | hb
    · rw [hγF] at hqe
      have := hFinj (hKmem ⟨by linarith, hq2.le⟩ (abs_le.2 ⟨by linarith, by linarith⟩))
        (hγK t) hqe
      have := congrArg Prod.fst this
      simp only at this
      linarith
    · exact Set.disjoint_left.1 hr₂F (ball_subset_closedBall hb)
        ⟨((t : ℝ), 0), ⟨⟨t.2.1, hc⟩, by norm_num, by norm_num⟩, (hγF t).symm⟩
  have R02 : Disjoint R0 R2 := by
    rw [Set.disjoint_left]
    rintro p (⟨q, ⟨⟨hq1, hq2⟩, hq3, hq4⟩, rfl⟩ | hp0) (⟨q', ⟨⟨hq1', hq2'⟩, hq3', hq4'⟩, hqe⟩ | hp2)
    · have := hFinj (hKmem ⟨by linarith, hq2'.le⟩ (abs_le.2 ⟨by linarith, by linarith⟩))
        (hKmem ⟨hq1.le, by linarith⟩ (abs_le.2 ⟨by linarith, by linarith⟩)) hqe
      have := congrArg Prod.fst this
      simp only at this
      linarith
    · exact Set.disjoint_left.1 hr₂F (ball_subset_closedBall hp2)
        ⟨q, ⟨⟨hq1.le, by linarith⟩, by linarith, by linarith⟩, rfl⟩
    · exact Set.disjoint_left.1 hr₀F (ball_subset_closedBall hp0)
        ⟨q', ⟨⟨by linarith, hq2'.le⟩, by linarith, by linarith⟩, hqe⟩
    · have h1 := mem_ball.1 hp0
      have h2 := mem_ball.1 hp2
      have := dist_triangle_left (γ 0) (γ 1) p
      linarith
  have hπe : ∀ e : E, π ((e : M) : Pt) = γ (k e) := fun e => hγπ (k e) _ ⟨e, ⟨e, rfl, rfl⟩, rfl⟩
  have hlay : ∀ t : unitInterval, ∀ p ∈ toPt (layer k t), π p = γ t := hγπ
  have hne : ∀ t : unitInterval, ∃ p, p ∈ toPt (layer k t) := fun t => by
    obtain ⟨e, he⟩ := hk t
    exact ⟨_, ⟨e, ⟨e, he, rfl⟩, rfl⟩⟩
  -- every parameter lies in a link
  have hin : ∀ t : unitInterval, ∃ i : Fin 3, ∀ p, π p = γ t → p ∈ G i := by
    intro t
    by_cases h1 : (t : ℝ) < β₁
    · exact ⟨0, fun p hp => by rw [hG0]; show π p ∈ R0; rw [hp]; exact g0 t h1⟩
    by_cases h2 : (t : ℝ) ≤ ζ₃
    · exact ⟨1, fun p hp => by
        rw [hG1]; show π p ∈ R1; rw [hp]; exact g1 t (by linarith) (by linarith)⟩
    · exact ⟨2, fun p hp => by rw [hG2]; show π p ∈ R2; rw [hp]; exact g2 t (by linarith)⟩
  have hopenR : ∀ i, IsOpen (G i) := by
    have o0 : IsOpen R0 := (hF.isOpen_image (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono (Ioo_subset_Ioo_right (by linarith)) (Ioo_subset_Ioo (by linarith) hc₁1))).union
      isOpen_ball
    have o1 : IsOpen R1 := hF.isOpen_image (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono (Ioo_subset_Ioo (by linarith) (by linarith)) (Ioo_subset_Ioo (by linarith) hc'1))
    have o2 : IsOpen R2 := (hF.isOpen_image (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono (Ioo_subset_Ioo_left (by linarith)) (Ioo_subset_Ioo (by linarith) hc₁1))).union
      isOpen_ball
    intro i
    fin_cases i
    · show IsOpen (G 0); rw [hG0]; exact o0.preimage hπc
    · show IsOpen (G 1); rw [hG1]; exact o1.preimage hπc
    · show IsOpen (G 2); rw [hG2]; exact o2.preimage hπc
  -- a layer gives a point of a link
  have hpt : ∀ (t : unitInterval) (i : Fin 3), (∀ p, π p = γ t → p ∈ G i) → (G i).Nonempty :=
    fun t i h => by obtain ⟨p, hp⟩ := hne t; exact ⟨p, h p (hlay t p hp)⟩
  have hmid : ∀ t : unitInterval, ∀ p, π p = γ t → (α < t ∧ (t : ℝ) < ζ₂) → p ∈ G 1 :=
    fun t p hp ht => by rw [hG1]; show π p ∈ R1; rw [hp]; exact g1 t ht.1 ht.2
  have hmeet01 : (G 0 ∩ G 1).Nonempty := by
    set t : unitInterval := ⟨(α + β₁) / 2, by linarith, by linarith⟩
    obtain ⟨p, hp⟩ := hne t
    refine ⟨p, ?_, hmid t p (hlay t p hp) ⟨by simp [t]; linarith, by simp [t]; linarith⟩⟩
    rw [hG0]; show π p ∈ R0; rw [hlay t p hp]; exact g0 t (by simp [t]; linarith)
  have hmeet12 : (G 1 ∩ G 2).Nonempty := by
    set t : unitInterval := ⟨(ζ₃ + ζ₂) / 2, by linarith, by linarith⟩
    obtain ⟨p, hp⟩ := hne t
    refine ⟨p, hmid t p (hlay t p hp) ⟨by simp [t]; linarith, by simp [t]; linarith⟩, ?_⟩
    rw [hG2]; show π p ∈ R2; rw [hlay t p hp]; exact g2 t (by simp [t]; linarith)
  have hself : ∀ i : Fin 3, (G i).Nonempty := by
    intro i
    fin_cases i
    · exact hpt 0 0 fun p hp => by
        rw [hG0]; show π p ∈ R0; rw [hp]; exact g0 0 (by simp; linarith)
    · exact (hmeet01.mono inter_subset_right)
    · exact hpt 1 2 fun p hp => by
        rw [hG2]; show π p ∈ R2; rw [hp]; exact g2 1 (by simp; linarith)
  have h02 : G 0 ∩ G 2 = ∅ := by
    rw [hG0, hG2, ← preimage_inter, Set.disjoint_iff_inter_eq_empty.1 R02, preimage_empty]
  have hchain : IsPlaneChain G := by
    refine ⟨hopenR, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp
    · exact hself 0
    · exact hmeet01
    · rw [h02]; simp
    · rw [inter_comm]; exact hmeet01
    · simpa using hself 1
    · exact hmeet12
    · rw [inter_comm, h02]; simp
    · rw [inter_comm]; exact hmeet12
    · simpa using hself 2
  refine ⟨hchain, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨i, hi⟩ := hin (k ⟨m, hm⟩)
    exact mem_iUnion.2 ⟨i, hi _ (hπe ⟨m, hm⟩)⟩
  · intro p hp
    rw [hG0]; show π p ∈ R0; rw [hlay 0 p hp]; exact g0 0 (by simp; linarith)
  · intro p hp
    rw [hGl]; show π p ∈ R2; rw [hlay 1 p hp]; exact g2 1 (by simp; linarith)
  · intro t
    obtain ⟨i, hi⟩ := hin t
    exact ⟨i, fun p hp => hi p (hlay t p hp)⟩
  · intro r s hrs i hi
    obtain ⟨pr, hpr⟩ := hne r
    obtain ⟨ps, hps⟩ := hne s
    have hr' : pr ∈ G i := hi (by rw [toPt, image_union]; exact Or.inl hpr)
    have hs' : ps ∈ G i := hi (by rw [toPt, image_union]; exact Or.inr hps)
    rintro _ ⟨m, ⟨e, he, rfl⟩, rfl⟩
    have hke : r ≤ k e ∧ k e ≤ s := he
    fin_cases i
    · -- the first link
      have hs0 : (s : ℝ) < β₁ := by
        change ps ∈ G 0 at hs'
        rw [hG0] at hs'
        have : π ps ∈ R0 := hs'
        rw [hlay s ps hps] at this
        exact g0' s this
      refine mem_iUnion₂.2 ⟨0, ?_, ?_⟩
      · show (G 0 ∩ G 0).Nonempty; rw [inter_self]; exact hself 0
      · rw [hG0]; show π _ ∈ R0; rw [hπe e]
        exact g0 _ (lt_of_le_of_lt (show ((k e : unitInterval) : ℝ) ≤ s from hke.2) hs0)
    · obtain ⟨j, hj⟩ := hin (k e)
      refine mem_iUnion₂.2 ⟨j, ?_, hj _ (hπe e)⟩
      show (G j ∩ G _).Nonempty
      fin_cases j
      · exact hmeet01
      · simpa using hself 1
      · rw [inter_comm]; exact hmeet12
    · have hr2 : ζ₃ < (r : ℝ) := by
        change pr ∈ G 2 at hr'
        rw [hG2] at hr'
        have : π pr ∈ R2 := hr'
        rw [hlay r pr hpr] at this
        exact g2' r this
      refine mem_iUnion₂.2 ⟨2, ?_, ?_⟩
      · show (G 2 ∩ G _).Nonempty
        change (G 2 ∩ G 2).Nonempty
        rw [inter_self]; exact hself 2
      · rw [hG2]; show π _ ∈ R2; rw [hπe e]
        exact g2 _ (lt_of_lt_of_le hr2 (show (r : ℝ) ≤ ((k e : unitInterval) : ℝ) from hke.1))

end NoBelow

end HPC.Hagopian
