import HPC.Hagopian.H76NoBelow

/-!
# Batch 163, item B: the core contradiction

`no_M_below_core`: near a point `u` of an interior layer `U = k⁻¹(a′)` with `a′ < y`, no point `z`
of `M` has `π(z)` just below `γ(a′)` in collar coordinates. This is the argument of Hagopian's
Lemma 9 (pp. 344–345) in the form of commission 163 §1 (see `H76NoBelow.lean` for the changes).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Core

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

set_option maxHeartbeats 1600000 in
/-- **The core of Lemma 9.** -/
theorem no_M_below_core (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    (hFc : Continuous F) {y : unitInterval} (hy1 : y < 1) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hvert : F '' ({(y : ℝ)} ×ˢ Ico (-c₀) 0) ∩ π '' M = ∅)
    {a' : unitInterval} (ha'0 : 0 < a') (ha'y : a' < y) {u : M} (hu : u ∈ layer k a') :
    ∃ ζ > 0, ∀ z : M, dist z u < ζ → ∀ x s : ℝ, |x - a'| < ζ → -ζ < s → s < 0 →
      π z ≠ F (x, s) := by
  classical
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  have hk : Function.Surjective k := hE.2.1.2.1
  have hkc : Continuous k := hE.2.1.1
  have hπc : Continuous π := hπ.continuous
  have hγc : Continuous γ := hγ.continuous
  obtain ⟨ea, eb, hirr⟩ := hE.1
  have hEcont : Fold.Q78.IsContinuum E := hirr.1
  have hEcpt : IsCompact E := hE.isCompact
  have hF' := hF
  obtain ⟨hemb, h0, -⟩ := hF'
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hFinj : InjOn F K := fun p hp q hq e =>
    congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) e)
  have hKmem : ∀ {x s : ℝ}, x ∈ Icc (0 : ℝ) 1 → |s| ≤ 1 → (x, s) ∈ K := fun hx hs =>
    ⟨hx, (abs_le.1 hs).1, (abs_le.1 hs).2⟩
  have hγF : ∀ t : unitInterval, γ t = F ((t : ℝ), 0) := fun t => (h0 t).symm
  have hπe : ∀ e : E, π ((e : M) : Pt) = γ (k e) := fun e => hγπ (k e) _ ⟨e, ⟨e, rfl, rfl⟩, rfl⟩
  -- abscissae
  set A : ℝ := (a' : ℝ) with hAdef
  set Y : ℝ := (y : ℝ) with hYdef
  have hA0 : 0 < A := ha'0
  have hAY : A < Y := ha'y
  have hY1 : Y < 1 := hy1
  set α : ℝ := A / 3 with hα
  set β₁ : ℝ := 2 * A / 3 with hβ₁
  set ζ₃ : ℝ := Y + (1 - Y) / 3 with hζ₃
  set ζ₂ : ℝ := Y + 2 * (1 - Y) / 3 with hζ₂
  set b₁ : unitInterval := ⟨β₁, by linarith, by linarith⟩ with hb₁
  set z₃ : unitInterval := ⟨ζ₃, by linarith, by linarith⟩ with hz₃
  -- the layer sets
  set Cs := toPt (layerSet k (Icc 0 y)) with hCs
  set Ds := toPt (layerSet k (Icc a' 1)) with hDs
  set H1 := toPt (layerSet k (Icc 0 b₁)) with hH1
  set Far := toPt (layerSet k (Icc z₃ 1)) with hFar
  set Mid := toPt (layerSet k (Icc a' z₃)) with hMid
  set Ends := toPt (layerSet k {0, 1}) with hEnds
  set Zs := toPt (layerSet k {1}) with hZs
  have hcpt : ∀ S : Set unitInterval, IsClosed S → IsCompact (toPt (layerSet k S)) :=
    fun S hS => isCompact_toPt (isCompact_img hEcpt hkc hS)
  have hlt : ∀ {r s : unitInterval}, (r : ℝ) < s → r < s := fun h => h
  have hD1 : Disjoint (Icc a' 1) (Icc 0 b₁) := Set.disjoint_left.2 fun t h1 h2 => by
    have : (a' : ℝ) ≤ t := h1.1
    have : (t : ℝ) ≤ β₁ := h2.2
    linarith
  have hD2 : Disjoint (Icc z₃ 1) (Icc 0 y) := Set.disjoint_left.2 fun t h1 h2 => by
    have : ζ₃ ≤ (t : ℝ) := h1.1
    have : (t : ℝ) ≤ y := h2.2
    linarith
  have hD3 : Disjoint (Icc a' z₃) {0, 1} := Set.disjoint_left.2 fun t h1 h2 => by
    have e1 : (a' : ℝ) ≤ t := h1.1
    have e2 : (t : ℝ) ≤ ζ₃ := h1.2
    rcases h2 with h | h
    · rw [h] at e1; simp at e1; linarith
    · rw [h] at e2; simp at e2; linarith
  have hD4 : Disjoint ({1} : Set unitInterval) (Icc 0 y) := Set.disjoint_left.2 fun t h1 h2 => by
    rw [mem_singleton_iff] at h1
    have : (t : ℝ) ≤ y := h2.2
    rw [h1] at this; simp at this; linarith
  obtain ⟨δ₁, hδ₁, hδ₁d⟩ := (disjoint_toPt_layerSet k hD1).exists_thickenings
    (hcpt _ isClosed_Icc) (hcpt _ isClosed_Icc).isClosed
  obtain ⟨δ₂, hδ₂, hδ₂d⟩ := (disjoint_toPt_layerSet k hD2).exists_thickenings
    (hcpt _ isClosed_Icc) (hcpt _ isClosed_Icc).isClosed
  obtain ⟨δ₃, hδ₃, hδ₃d⟩ := (disjoint_toPt_layerSet k hD3).exists_thickenings
    (hcpt _ isClosed_Icc) (hcpt _ (Set.toFinite _).isClosed).isClosed
  obtain ⟨δ₄, hδ₄, hδ₄d⟩ := (disjoint_toPt_layerSet k hD4).exists_thickenings
    (hcpt _ isClosed_singleton) (hcpt _ isClosed_Icc).isClosed
  set ε := min (min δ₁ δ₂) (min δ₃ δ₄) with hεdef
  have hε : 0 < ε := lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄)
  have hε₁ : ε ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂ : ε ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hε₃ : ε ≤ δ₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₄ : ε ≤ δ₄ := (min_le_right _ _).trans (min_le_right _ _)
  have U1 : Disjoint (thickening ε Ds) (thickening ε H1) :=
    hδ₁d.mono (thickening_mono hε₁ _) (thickening_mono hε₁ _)
  have U2a : Disjoint (thickening ε Far) Cs :=
    hδ₂d.mono (thickening_mono hε₂ _) (self_subset_thickening hδ₂ _)
  have U2b : Disjoint (thickening ε Mid) Ends :=
    hδ₃d.mono (thickening_mono hε₃ _) (self_subset_thickening hδ₃ _)
  have U3 : Disjoint (thickening ε Zs) (thickening ε Cs) :=
    hδ₄d.mono (thickening_mono hε₄ _) (thickening_mono hε₄ _)
  -- closeness through `π`
  obtain ⟨η₀, hη₀, hη₀c⟩ := layer_close_of_pi_close hk hπc hγc hπS hγπ
    (isClosed_Icc : IsClosed (Icc (0 : unitInterval) b₁)) hε
  obtain ⟨ηC, hηC, hηCc⟩ := layer_close_of_pi_close hk hπc hγc hπS hγπ
    (isClosed_Icc : IsClosed (Icc (0 : unitInterval) y)) hε
  obtain ⟨cs, hcs, hcs1, hcsF⟩ := hF.uniform_height (lt_min hη₀ hηC)
  -- discs about the ends
  have hγ01 : γ 0 ≠ γ 1 := fun h => zero_ne_one (hγ.injective h)
  have hdγ : 0 < dist (γ 0) (γ 1) := dist_pos.2 hγ01
  have hA0c : IsCompact (F '' (Icc β₁ 1 ×ˢ Icc (-1) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image hFc
  have hA2c : IsCompact (F '' (Icc 0 ζ₃ ×ˢ Icc (-1) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image hFc
  have hγ0A : γ 0 ∉ F '' (Icc β₁ 1 ×ˢ Icc (-1) 1) := by
    rintro ⟨q, ⟨hq1, hq2⟩, hqe⟩
    rw [hγF] at hqe
    have := hFinj ⟨⟨by linarith [hq1.1], hq1.2⟩, hq2⟩ (hKmem (0 : unitInterval).2 (by simp)) hqe
    have := congrArg Prod.fst this
    simp only [Set.Icc.coe_zero] at this
    linarith [hq1.1]
  have hγ1A : γ 1 ∉ F '' (Icc 0 ζ₃ ×ˢ Icc (-1) 1) := by
    rintro ⟨q, ⟨hq1, hq2⟩, hqe⟩
    rw [hγF] at hqe
    have := hFinj ⟨⟨hq1.1, by linarith [hq1.2]⟩, hq2⟩ (hKmem (1 : unitInterval).2 (by simp)) hqe
    have := congrArg Prod.fst this
    simp only [Set.Icc.coe_one] at this
    linarith [hq1.2]
  obtain ⟨r₀', hr₀', hr₀'d⟩ := exists_closedBall_disjoint hA0c.isClosed hγ0A
  obtain ⟨r₂', hr₂', hr₂'d⟩ := exists_closedBall_disjoint hA2c.isClosed hγ1A
  set r₀ := min (min r₀' (η₀ / 2)) (dist (γ 0) (γ 1) / 3) with hr₀def
  set r₂ := min r₂' (dist (γ 0) (γ 1) / 3) with hr₂def
  have hr₀ : 0 < r₀ := lt_min (lt_min hr₀' (half_pos hη₀)) (by linarith)
  have hr₂ : 0 < r₂ := lt_min hr₂' (by linarith)
  have hr₀F : Disjoint (closedBall (γ 0) r₀) (F '' (Icc β₁ 1 ×ˢ Icc (-1) 1)) :=
    hr₀'d.mono_left (closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_left _ _)))
  have hr₂F : Disjoint (closedBall (γ 1) r₂) (F '' (Icc 0 ζ₃ ×ˢ Icc (-1) 1)) :=
    hr₂'d.mono_left (closedBall_subset_closedBall (min_le_left _ _))
  have hr₀η : r₀ < η₀ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _))
    (half_lt_self hη₀)
  have hrr : r₀ + r₂ < dist (γ 0) (γ 1) := by
    have := min_le_right (min r₀' (η₀ / 2)) (dist (γ 0) (γ 1) / 3)
    have := min_le_right r₂' (dist (γ 0) (γ 1) / 3)
    linarith
  obtain ⟨cr, hcr, -, hcrF⟩ := hF.uniform_height hr₀
  -- heights
  set c := min (min (cs / 2) c₀) cr with hcdef
  have hc : 0 < c := lt_min (lt_min (half_pos hcs) hc₀) hcr
  have hccs : c < cs := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _))
    (half_lt_self hcs)
  have hcc₀ : c ≤ c₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hccr : c ≤ cr := min_le_right _ _
  have hc1 : c ≤ 1 := hccs.le.trans hcs1
  set c' := c / 2 with hc'def
  have hc' : 0 < c' := half_pos hc
  -- the chain
  set G : Fin 3 → Set Pt := ![π ⁻¹' (F '' (Ioo 0 β₁ ×ˢ Ioo (-cs) cs) ∪ ball (γ 0) r₀),
      π ⁻¹' (F '' (Ioo α ζ₂ ×ˢ Ioo (-c') c')),
      π ⁻¹' (F '' (Ioo ζ₃ 1 ×ˢ Ioo (-cs) cs) ∪ ball (γ 1) r₂)] with hGdef
  obtain ⟨hG, hGE⟩ := chain3_follows hk hπc hγπ hF (α := α) (β₁ := β₁) (ζ₃ := ζ₃) (ζ₂ := ζ₂)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hcs hcs1 hc'
    (by linarith) hr₀ hr₂ hr₀F hr₂F hrr G hGdef
  set R0 := F '' (Ioo 0 β₁ ×ˢ Ioo (-cs) cs) ∪ ball (γ 0) r₀ with hR0
  set R1 := F '' (Ioo α ζ₂ ×ˢ Ioo (-c') c') with hR1
  set R2 := F '' (Ioo ζ₃ 1 ×ˢ Ioo (-cs) cs) ∪ ball (γ 1) r₂ with hR2
  have hG0 : G 0 = π ⁻¹' R0 := rfl
  have hG1 : G 1 = π ⁻¹' R1 := rfl
  have hG2 : G (Fin.last 2) = π ⁻¹' R2 := rfl
  have hGo0 : IsOpen (G 0) := hG.isOpen 0
  have hGo2 : IsOpen (G (Fin.last 2)) := hG.isOpen _
  obtain ⟨L, C', D', hC'o, hD'o, hC'D', hMCD, hEC', hL0, hLn, hLi, hLG, hLE, hLfree⟩ :=
    lemma8_caps_sep hHU hAT hE G hG hGE hGo0 hGo2 hGE.2.1 hGE.2.2.1 subset_rfl subset_rfl
  -- Lemma 2 at `u`
  obtain ⟨hSo, huS⟩ := hagopian76_lemma2 hX hε u
  obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.1 hSo u huS
  have huE' : u ∈ E := by obtain ⟨e, -, he⟩ := hu; rw [← he]; exact e.2
  have hka : k ⟨u, huE'⟩ = a' := by
    obtain ⟨e, he, heu⟩ := hu
    have : e = ⟨u, huE'⟩ := Subtype.ext heu
    rw [← this]; exact he
  have huE : (u : Pt) ∈ toPt E := ⟨u, huE', rfl⟩
  obtain ⟨δ', hδ', hδ'C⟩ := Metric.isOpen_iff.1 hC'o _ (hEC' huE)
  set ζ := min (min δ δ') (min (min (A - α) (Y - A)) c') with hζdef
  have hζ : 0 < ζ := lt_min (lt_min hδ hδ') (lt_min (lt_min (by linarith) (by linarith)) hc')
  have hζδ : ζ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hζδ' : ζ ≤ δ' := (min_le_left _ _).trans (min_le_right _ _)
  have hζα : ζ ≤ A - α := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hζY : ζ ≤ Y - A := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hζc' : ζ ≤ c' := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ζ, hζ, fun z hz x s hx hs1 hs2 hzF => ?_⟩
  rw [abs_lt] at hx
  have hx0 : α < x := by linarith
  have hxY : x < Y := by linarith
  have hcc' : c' < c := half_lt_self hc
  -- the homeomorphism
  obtain ⟨h, hhu, hh⟩ := hδS (show z ∈ ball u δ from lt_of_lt_of_le hz hζδ)
  have hmove : ∀ (v : M) (S : Set unitInterval), v ∈ layerSet k S →
      ((h v : M) : Pt) ∈ thickening ε (toPt (layerSet k S)) := fun v S hv =>
    mem_thickening_iff.2 ⟨v, ⟨v, hv, rfl⟩, by rw [dist_comm]; exact hh v⟩
  -- `z` is not in `E`
  have hzE : (z : Pt) ∉ toPt E := by
    rintro ⟨m, hm, hmz⟩
    have h1 := hπe ⟨m, hm⟩
    rw [show ((⟨m, hm⟩ : E) : M) = z from Subtype.ext hmz, hzF, hγF] at h1
    have := hFinj (hKmem ⟨by linarith, by linarith⟩ (abs_le.2 ⟨by linarith, by linarith⟩))
      (hKmem (k ⟨m, hm⟩).2 (by simp)) h1
    have := congrArg Prod.snd this
    simp only at this
    linarith
  -- the continuum `h[D]`
  set Dm := layerSet k (Icc a' 1) with hDm
  have hDmc : Fold.Q78.IsContinuum Dm :=
    isContinuum_img hEcpt hE.2.1 isClosed_Icc isPreconnected_Icc ⟨a', le_rfl, a'.2.2⟩
  have huD : u ∈ Dm := ⟨⟨u, huE'⟩, ⟨hka ▸ le_rfl, (k _).2.2⟩, rfl⟩
  set Ys := toPt (h '' Dm) with hYs
  have hYc : Fold.Q78.IsContinuum (h '' Dm) := isContinuum_image_homeomorph h hDmc
  have hYcpt : IsCompact Ys := hYc.1.image continuous_subtype_val
  have hYpc : IsPreconnected Ys := hYc.2.isPreconnected.image _ continuous_subtype_val.continuousOn
  have hzY : (z : Pt) ∈ Ys := ⟨h u, ⟨u, huD, rfl⟩, by rw [hhu]⟩
  -- `h[D]` misses `C`
  have YC : Disjoint Ys Cs := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨v, hvD, rfl⟩, rfl⟩ hwC
    obtain ⟨e, he, rfl⟩ := hvD
    have hke : k e < z₃ := by
      by_contra hc
      push_neg at hc
      exact Set.disjoint_left.1 U2a (hmove _ _ ⟨e, ⟨hc, he.2⟩, rfl⟩) hwC
    set P := h '' layerSet k (Icc a' (k e)) with hP
    have hPc : Fold.Q78.IsContinuum P := isContinuum_image_homeomorph h
      (isContinuum_img hEcpt hE.2.1 isClosed_Icc isPreconnected_Icc ⟨a', le_rfl, he.1⟩)
    have hhvE : h e ∈ E := by
      obtain ⟨_, ⟨e', -, rfl⟩, hee'⟩ := hwC
      rw [← Subtype.ext hee']; exact e'.2
    have hmeet : (E ∩ P).Nonempty := ⟨h e, hhvE, ⟨e, ⟨e, ⟨he.1, le_rfl⟩, rfl⟩, rfl⟩⟩
    have havoid : Disjoint P (layer k 0 ∪ layer k 1) := by
      rw [Set.disjoint_left]
      rintro _ ⟨q, hq, rfl⟩ hq01
      obtain ⟨e', he', rfl⟩ := hq
      have h1 := hmove _ (Icc a' z₃) ⟨e', ⟨he'.1, he'.2.trans hke.le⟩, rfl⟩
      have h2 : ((h e' : M) : Pt) ∈ Ends := by
        rcases hq01 with ⟨e'', he'', hee⟩ | ⟨e'', he'', hee⟩
        · exact ⟨_, ⟨e'', Or.inl he'', hee⟩, rfl⟩
        · exact ⟨_, ⟨e'', Or.inr he'', hee⟩, rfl⟩
      exact Set.disjoint_left.1 U2b h1 h2
    have hPE := subset_of_meets_avoids hHU hAT hEcont hE.2.1 hPc hmeet havoid
    have hzP : z ∈ P := by
      rw [← hhu]
      exact ⟨u, ⟨⟨u, huE'⟩, ⟨by rw [hka], by rw [hka]; exact he.1⟩, rfl⟩, rfl⟩
    exact hzE ⟨z, hPE hzP, rfl⟩
  -- `h[D]` misses the vertical
  have YV : ∀ p ∈ Ys, π p ∉ F '' ({(y : ℝ)} ×ˢ Ico (-c₀) 0) := by
    rintro _ ⟨m, -, rfl⟩ hm
    have : π m ∈ F '' ({(y : ℝ)} ×ˢ Ico (-c₀) 0) ∩ π '' M := ⟨hm, ⟨m, m.2, rfl⟩⟩
    rw [hvert] at this; exact this
  -- `h[D]` misses `Cl G₀`
  have hb₁0 : (0 : unitInterval) ≤ b₁ := b₁.2.1
  have hclR0 : ∀ p ∈ closure R0, ∃ t ∈ Icc (0 : unitInterval) b₁, dist p (γ t) < η₀ := by
    have hsub : closure R0 ⊆ F '' (Icc 0 β₁ ×ˢ Icc (-cs) cs) ∪ closedBall (γ 0) r₀ := by
      rw [hR0, closure_union]
      exact union_subset_union (closure_minimal
        (image_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
        ((isCompact_Icc.prod isCompact_Icc).image hFc).isClosed) closure_ball_subset_closedBall
    intro p hp
    rcases hsub hp with ⟨⟨x', s'⟩, ⟨hx', hs'⟩, rfl⟩ | hp'
    · have hx'I : x' ∈ Icc (0 : ℝ) 1 := ⟨hx'.1, by linarith [hx'.2]⟩
      refine ⟨⟨x', hx'I⟩, ⟨unitInterval.nonneg', hx'.2⟩, ?_⟩
      rw [hγF]
      exact lt_of_lt_of_le (hcsF x' hx'I s' (abs_le.2 hs')) (min_le_left _ _)
    · exact ⟨0, ⟨le_rfl, hb₁0⟩, lt_of_le_of_lt (mem_closedBall.1 hp') hr₀η⟩
  have YG0 : Disjoint Ys (closure (G 0)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨v, hvD, rfl⟩, rfl⟩ hp
    have hp' : π ((h v : M) : Pt) ∈ closure R0 := hπc.closure_preimage_subset R0 hp
    obtain ⟨t, ht, hdt⟩ := hclR0 _ hp'
    exact Set.disjoint_left.1 U1 (hmove v _ hvD) (hη₀c (h v) t ht hdt)
  -- the region `O`
  set O := F '' (Ioo 0 (y : ℝ) ×ˢ Ioo (-c) 0) with hO
  have hOo : IsOpen O := hF.isOpen_image (isOpen_Ioo.prod isOpen_Ioo)
    (prod_mono (Ioo_subset_Ioo_right hY1.le) (Ioo_subset_Ioo (by linarith) (by norm_num)))
  have hclO : closure O ⊆ F '' (Icc 0 (y : ℝ) ×ˢ Icc (-c) 0) :=
    closure_minimal (image_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
      ((isCompact_Icc.prod isCompact_Icc).image hFc).isClosed
  have hclOC : ∀ m : M, π m ∈ closure O → (m : Pt) ∈ thickening ε Cs := by
    intro m hm
    obtain ⟨⟨x', s'⟩, ⟨hx', hs'⟩, he⟩ := hclO hm
    have hx'I : x' ∈ Icc (0 : ℝ) 1 := ⟨hx'.1, hx'.2.trans hY1.le⟩
    refine hηCc m ⟨x', hx'I⟩ ⟨unitInterval.nonneg', hx'.2⟩ ?_
    rw [← he, hγF]
    exact lt_of_lt_of_le (hcsF x' hx'I s' (abs_le.2 ⟨by linarith [hs'.1], by linarith [hs'.2]⟩))
      (min_le_right _ _)
  have hYnot : Ys ∩ π ⁻¹' closure O ≠ Ys := by
    intro heq
    obtain ⟨e1, he1⟩ := hk 1
    have hv : (e1 : M) ∈ Dm := ⟨e1, ⟨by rw [he1]; exact a'.2.2, by rw [he1]⟩, rfl⟩
    have hp : ((h e1 : M) : Pt) ∈ Ys := ⟨_, ⟨_, hv, rfl⟩, rfl⟩
    rw [← heq] at hp
    exact Set.disjoint_left.1 U3 (hmove (e1 : M) {1} ⟨e1, he1, rfl⟩) (hclOC (h e1) hp.2)
  have hzO : π z ∈ O := by
    rw [hzF]; exact ⟨(x, s), ⟨⟨by linarith, hxY⟩, by linarith, hs2⟩, rfl⟩
  -- boundary bumping
  have hFcpt : IsCompact (Ys ∩ π ⁻¹' closure O) := hYcpt.inter_right (isClosed_closure.preimage hπc)
  obtain ⟨Q, -, hQconn, hQsub, hzQ, w, hwQ, hwcl⟩ := exists_continuum_bump_compact hYpc hFcpt
    inter_subset_left hYnot ⟨hzY, subset_closure hzO⟩
  have hwO : π w ∉ O := by
    intro hwO
    have h1 : π w ∈ closure (closure O)ᶜ := by
      refine closure_mono ?_ (image_closure_subset_closure_image hπc ⟨w, hwcl, rfl⟩)
      rintro _ ⟨q, ⟨hqY, hq⟩, rfl⟩; exact fun h => hq ⟨hqY, h⟩
    rw [closure_compl] at h1
    exact h1 (interior_maximal subset_closure hOo hwO)
  have hwclO : π w ∈ closure O := (hQsub hwQ).2
  have hwY : w ∈ Ys := (hQsub hwQ).1
  obtain ⟨⟨q₁, q₂⟩, ⟨hq₁, hq₂⟩, hqe⟩ := hclO hwclO
  obtain ⟨mw, -, hmw⟩ := id hwY
  have hπmw : π (mw : Pt) = F (q₁, q₂) := by rw [hmw, hqe]
  have hwG0 : w ∉ G 0 := fun hw => Set.disjoint_left.1 YG0 hwY (subset_closure hw)
  have hq₁I : q₁ ∈ Icc (0 : ℝ) 1 := ⟨hq₁.1, hq₁.2.trans hY1.le⟩
  have hq₂1 : |q₂| ≤ c := abs_le.2 ⟨hq₂.1, by linarith [hq₂.2]⟩
  -- the point `w` is outside `St G`
  have hwL : w ∉ ⋃ i, L i := by
    by_cases hq20 : q₂ = 0
    · exfalso
      subst hq20
      have hl := mem_layer_of_pi_eq hk hπS hγπ (hπmw.trans (hγF ⟨q₁, hq₁I⟩).symm)
      obtain ⟨e, he, hee⟩ := hl
      refine Set.disjoint_left.1 YC hwY ⟨mw, ⟨e, ?_, hee⟩, hmw⟩
      show k e ∈ Icc 0 y
      rw [show k e = ⟨q₁, hq₁I⟩ from he]
      exact ⟨unitInterval.nonneg', hq₁.2⟩
    have hq2n : q₂ < 0 := lt_of_le_of_ne hq₂.2 hq20
    by_cases hq1y : q₁ = y
    · exfalso
      exact YV w hwY ⟨(q₁, q₂), ⟨hq1y, ⟨by linarith [hq₂.1], hq2n⟩⟩, hqe⟩
    by_cases hq10 : q₁ = 0
    · exfalso
      apply hwG0
      show π w ∈ R0
      right
      rw [← hqe, hq10, mem_ball, hγF]
      have := hcrF 0 ⟨le_rfl, zero_le_one⟩ q₂ (hq₂1.trans hccr)
      simpa using this
    have hq1pos : 0 < q₁ := lt_of_le_of_ne hq₁.1 (Ne.symm hq10)
    have hq1y' : q₁ < y := lt_of_le_of_ne hq₁.2 hq1y
    have hq2c : q₂ = -c := by
      by_contra hne
      exact hwO (hqe ▸ ⟨(q₁, q₂), ⟨⟨hq1pos, hq1y'⟩, lt_of_le_of_ne hq₂.1 (Ne.symm hne), hq2n⟩, rfl⟩)
    subst hq2c
    by_cases hqβ : q₁ < β₁
    · exfalso
      apply hwG0
      show π w ∈ R0
      left
      exact ⟨(q₁, -c), ⟨⟨hq1pos, hqβ⟩, by linarith, by linarith⟩, hqe⟩
    push_neg at hqβ
    have hwK : (q₁, -c) ∈ K := hKmem hq₁I (by rw [abs_neg, abs_of_pos hc]; exact hc1)
    have hwA0 : π w ∈ F '' (Icc β₁ 1 ×ˢ Icc (-1) 1) :=
      ⟨(q₁, -c), ⟨⟨hqβ, hq₁I.2⟩, by linarith, by linarith⟩, hqe⟩
    have hwA2 : π w ∈ F '' (Icc 0 ζ₃ ×ˢ Icc (-1) 1) :=
      ⟨(q₁, -c), ⟨⟨hq₁.1, by linarith⟩, by linarith, by linarith⟩, hqe⟩
    rw [mem_iUnion]
    rintro ⟨i, hi⟩
    have hiG := hLG.2 i hi
    fin_cases i
    · show False
      have : π w ∈ R0 := hiG
      rcases this with ⟨⟨x'', s''⟩, ⟨⟨hx1, hx2⟩, hs1', hs2'⟩, he⟩ | hb
      · rw [← hqe] at he
        have := hFinj (hKmem ⟨hx1.le, by linarith⟩ (abs_le.2 ⟨by linarith, by linarith⟩)) hwK he
        have := congrArg Prod.fst this
        simp only at this
        linarith
      · exact Set.disjoint_left.1 hr₀F (ball_subset_closedBall hb) hwA0
    · show False
      have : π w ∈ R1 := hiG
      obtain ⟨⟨x'', s''⟩, ⟨⟨hx1, hx2⟩, hs1', hs2'⟩, he⟩ := this
      rw [← hqe] at he
      have := hFinj (hKmem ⟨by linarith, by linarith⟩ (abs_le.2 ⟨by linarith, by linarith⟩)) hwK he
      have := congrArg Prod.snd this
      simp only at this
      linarith
    · show False
      have : π w ∈ R2 := hiG
      rcases this with ⟨⟨x'', s''⟩, ⟨⟨hx1, hx2⟩, hs1', hs2'⟩, he⟩ | hb
      · rw [← hqe] at he
        have := hFinj (hKmem ⟨by linarith, hx2.le⟩ (abs_le.2 ⟨by linarith, by linarith⟩)) hwK he
        have := congrArg Prod.fst this
        simp only at this
        linarith
      · exact Set.disjoint_left.1 hr₂F (ball_subset_closedBall hb) hwA2
  -- `z` is in `L₂ = C′ ∩ G₂`
  have hzL : (z : Pt) ∈ ⋃ i, L i := by
    refine mem_iUnion.2 ⟨1, ?_⟩
    rw [hLi 1 (by decide) (by decide)]
    refine ⟨hδ'C (lt_of_lt_of_le hz hζδ'), ?_⟩
    show π z ∈ R1
    rw [hzF]
    exact ⟨(x, s), ⟨⟨hx0, by linarith⟩, by linarith, by linarith⟩, rfl⟩
  -- freeness
  obtain ⟨p, hpQ, hpfr⟩ := meets_frontier_of_isPreconnected hQconn.isPreconnected hzQ hzL hwQ hwL
  have hpY : p ∈ Ys := (hQsub hpQ).1
  have hpM : p ∈ M := by obtain ⟨m, -, rfl⟩ := hpY; exact m.2
  have hp2 := hLfree ⟨hpM, hpfr⟩
  rw [hL0, hLn] at hp2
  have hp3 : p ∈ closure (G 0) ∪ closure (G (Fin.last 2)) := by
    rw [← closure_union]; exact frontier_subset_closure hp2
  rcases hp3 with hp3 | hp3
  · exact Set.disjoint_left.1 YG0 hpY hp3
  · have h1 : π p ∈ closure R2 := hπc.closure_preimage_subset R2 hp3
    have h2 : π p ∈ closure O := (hQsub hpQ).2
    have hsub : closure R2 ⊆ F '' (Icc ζ₃ 1 ×ˢ Icc (-cs) cs) ∪ closedBall (γ 1) r₂ := by
      rw [hR2, closure_union]
      exact union_subset_union (closure_minimal
        (image_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
        ((isCompact_Icc.prod isCompact_Icc).image hFc).isClosed) closure_ball_subset_closedBall
    obtain ⟨⟨o₁, o₂⟩, ⟨ho₁, ho₂⟩, hoe⟩ := hclO h2
    have hoK : (o₁, o₂) ∈ K := hKmem ⟨ho₁.1, ho₁.2.trans hY1.le⟩
      (abs_le.2 ⟨by linarith [ho₂.1], by linarith [ho₂.2]⟩)
    rcases hsub h1 with ⟨⟨x'', s''⟩, ⟨⟨hx1, hx2⟩, hs1', hs2'⟩, he⟩ | hb
    · rw [← hoe] at he
      have := hFinj (hKmem ⟨by linarith, hx2⟩ (abs_le.2 ⟨by linarith, by linarith⟩)) hoK he
      have := congrArg Prod.fst this
      simp only at this
      linarith [ho₁.2]
    · exact Set.disjoint_left.1 hr₂F hb
        ⟨(o₁, o₂), ⟨⟨ho₁.1, by linarith [ho₁.2]⟩, by linarith [ho₂.1], by linarith [ho₂.2]⟩, hoe⟩

end Core

end HPC.Hagopian
