import HPC.Hagopian.Hagopian76W

/-!
# Batch 179, §4: uniform heights (I) — Property 3 and the descent, with the height chosen before `G`

Commission 179 §4: in the batch 171–175 statements the height `c` is introduced after the extension
`G` (`∀ G d, … → ∃ c > 0, …`). Hagopian's order needs it before `F = G` (T13 builds `F` from `D`).
Checked: every height in the chain comes from `follows_crossing` (through
`hagopian76_property3_reduced`) and from `pi_thin_near_layer`, neither of which mentions `G`. The
statements below are the originals with `∀ G d, IsMinimalAdmissible G d → E ⊆ G →
d⁻¹(0) = k⁻¹(0) →` moved after `∃ c`; the proofs are the original proofs, with the inner heights
taken from the uniform versions. The old names remain, and follow as corollaries.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Uniform

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§4, uniform height.** `hagopian76_property3_reduced` with the height chosen before `G` (it comes from `follows_crossing`, which does not mention `G`). The proof is the original one. -/
theorem property3_reduced_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, 0 < v → v < 1 → closure B ⊆ layer d v →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧
        h '' layerSet k {t | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} ⊆ closure B ∧
        ((∀ t : unitInterval, (t : ℝ) ≤ 6 / 11 → (layer d v ∩ h '' layer k t).Nonempty) ∨
          (∀ t : unitInterval, 5 / 11 ≤ (t : ℝ) → (layer d v ∩ h '' layer k t).Nonempty)) ∧
        ((∀ j : Fin 11, (j : ℕ) ≤ 5 → (toPt (layer d v) ∩ L j).Nonempty) ∨
          (∀ j : Fin 11, 5 ≤ (j : ℕ) → (toPt (layer d v) ∩ L j).Nonempty)) := by
  obtain ⟨c, hc, hc1, hB⟩ := follows_crossing hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨c, hc, hc1, fun G d hG B hBc hBin hBl hBr v hv0 hv1 hBv => ?_⟩
  obtain ⟨-, h, hh, -, -, -, hlink, hmid⟩ := hB B hBc hBin hBl hBr
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  -- two translated layers inside the layer
  have hmeet : ∀ t : unitInterval, 4 / 11 < (t : ℝ) → (t : ℝ) < 7 / 11 →
      (layer d v ∩ h '' layer k t).Nonempty := by
    intro t ht1 ht2
    obtain ⟨y, hy⟩ := hE.2.1.2.1 t
    have hy' : h y ∈ h '' layerSet k {t | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} :=
      ⟨y, ⟨y, by rw [mem_preimage, hy]; exact ⟨ht1, ht2⟩, rfl⟩, rfl⟩
    exact ⟨h y, hBv (hmid hy'), y, ⟨y, hy, rfl⟩, rfl⟩
  set α : unitInterval := ⟨5 / 11, by norm_num, by norm_num⟩
  set β : unitInterval := ⟨6 / 11, by norm_num, by norm_num⟩
  have hαβ : α < β := by show (5 / 11 : ℝ) < 6 / 11; norm_num
  have hcases := layer_meets_translate_initial hHU hAT hE hG hv0 hv1 h hαβ
    (hmeet α (by show (4 / 11 : ℝ) < 5 / 11; norm_num) (by show (5 / 11 : ℝ) < 7 / 11; norm_num))
    (hmeet β (by show (4 / 11 : ℝ) < 6 / 11; norm_num) (by show (6 / 11 : ℝ) < 7 / 11; norm_num))
  have hcases' : (∀ t : unitInterval, (t : ℝ) ≤ 6 / 11 → (layer d v ∩ h '' layer k t).Nonempty) ∨
      (∀ t : unitInterval, 5 / 11 ≤ (t : ℝ) → (layer d v ∩ h '' layer k t).Nonempty) := by
    rcases hcases with h1 | h1
    · exact Or.inl fun t ht => h1 t ht
    · exact Or.inr fun t ht => h1 t ht
  refine ⟨h, hh, hmid, hcases', ?_⟩
  -- a translated layer in `piece (j + 1)` gives a point of the layer in `L j`
  have hlinkpt : ∀ (j : Fin 11) (t : unitInterval), (j : ℝ) / 11 ≤ (t : ℝ) →
      (t : ℝ) ≤ ((j : ℝ) + 1) / 11 → (layer d v ∩ h '' layer k t).Nonempty →
      (toPt (layer d v) ∩ L j).Nonempty := by
    rintro j t ht1 ht2 ⟨_, hxv, y, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨(h e : Pt), ⟨h e, hxv, rfl⟩, hlink j ⟨h e, ⟨e, ⟨e, ?_, rfl⟩, rfl⟩, rfl⟩⟩
    rw [mem_preimage, mem_singleton_iff.1 he]
    push_cast
    constructor <;> linarith
  rcases hcases' with h1 | h1
  · left
    intro j hj
    have hj' : ((j : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hj
    set t : unitInterval := ⟨(j : ℝ) / 11, by positivity, by
      rw [div_le_one (by norm_num)]; linarith⟩
    exact hlinkpt j t le_rfl (by show (j : ℝ) / 11 ≤ ((j : ℝ) + 1) / 11; linarith)
      (h1 t (by show (j : ℝ) / 11 ≤ 6 / 11; linarith))
  · right
    intro j hj
    have hj' : (5 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj
    have hj10 : ((j : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (Nat.lt_succ_iff.1 j.2)
    set t : unitInterval := ⟨((j : ℝ) + 1) / 11, by positivity, by
      rw [div_le_one (by norm_num)]; linarith⟩
    exact hlinkpt j t (by show (j : ℝ) / 11 ≤ ((j : ℝ) + 1) / 11; linarith) le_rfl
      (h1 t (by show (5 / 11 : ℝ) ≤ ((j : ℝ) + 1) / 11; linarith))


/-- **§4, uniform height.** `hagopian76_property3_translate` with the height chosen before `G` (from `property3_reduced_unif`). -/
theorem property3_translate_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, 0 < v → v < 1 → closure B ⊆ layer d v →
      Disjoint (layer d v) E ∧ ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧
        h '' layerSet k {t | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} ⊆ closure B ∧
        h '' G ⊆ layer d v := by
  obtain ⟨c, hc, hc1, hB⟩ := property3_reduced_unif hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1
  refine ⟨c, hc, hc1, fun G d hG hEG hX0 B hBc hBin hBl hBr v hv0 hv1 hBv => ?_⟩
  have hB := hB G d hG
  obtain ⟨h, hh, hmid, -, -⟩ := hB B hBc hBin hBl hBr v hv0 hv1 hBv
  obtain ⟨s, -, hseg, -⟩ := hagopian76_initial_segment hX hi hE hG hEG hX0
  have hdisjB := closure_disjoint_E_of_above hX hi hE hπ.continuous hγπ hF
    (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (19 / 22 : ℝ) < 1) hc1 hBc hBin
  obtain ⟨x, hxB, -⟩ := hBl
  have hdisj : Disjoint (layer d v) E := by
    refine layer_disjoint_of_not_subset hseg fun hsub => ?_
    exact disjoint_left.1 hdisjB hxB (hsub (hBv hxB))
  have hopen : IsOpen {t : unitInterval | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} :=
    (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)
  have hne : ({t : unitInterval | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11}).Nonempty :=
    ⟨⟨1 / 2, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  have hhE := translate_subset_layer hX hi hE hG hv0 hv1 h hopen hne (hmid.trans hBv)
  exact ⟨hdisj, h, hh, hmid, translate_extension_subset_layer hX hi hE hG hEG hX0 hv0 hv1 h hhE⟩


/-- **§4, uniform height.** `crossing_from_layer_translate_aux` (D1) with the height chosen before `G` (it comes from `pi_thin_near_layer`). -/
theorem crossing_from_layer_translate_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ ψ : M → M, Continuous ψ → (∀ v, dist v (ψ v) < 2 * ε₁) →
      ∀ u : unitInterval, ψ '' E ⊆ layer d u →
      ∀ x : E, 4 / 11 ≤ (k x : ℝ) → (k x : ℝ) ≤ 7 / 11 → π (ψ x : Pt) ∈ F '' D' →
      Disjoint (layer d u) E ∧ LayerCrossing d π F c₁ D' u := by
  have hε := he.pos
  set η := min ε₁ (1 / 22) with hη
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε₁ := min_le_left _ _
  have hη22 : η ≤ 1 / 22 := min_le_right _ _
  obtain ⟨c, hc, hc1, hthin⟩ := pi_thin_near_layer hE hπc hπS hγπ hF (a := 3 / 22) (b := 19 / 22)
    (by norm_num) (by norm_num) hη0
  refine ⟨c, hc, hc1, fun G d hG hEG hX0 c₁ D' hc₁ hR ψ hψc hψ u hψu x hx1 hx2 hψx => ?_⟩
  have hnear : ∀ (q : M) (z : ℝ × ℝ), z ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁ →
      π (q : Pt) = F z →
      ∃ e : E, (k e : ℝ) ∈ Icc (3 / 22 : ℝ) (19 / 22) ∧ |(k e : ℝ) - z.1| < η ∧
        dist q (e : M) < η := by
    intro q z hz hqz
    obtain ⟨e, he1, he2, he3⟩ :=
      hthin q z ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩ hqz
    exact ⟨e, he1, he2, by rw [Subtype.dist_eq]; exact he3⟩
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  obtain ⟨y₀, hy₀⟩ := hE.2.1.2.1 0
  obtain ⟨y₁, hy₁⟩ := hE.2.1.2.1 1
  have hk₀ : (k y₀ : ℝ) = 0 := by rw [hy₀]; rfl
  have hk₁ : (k y₁ : ℝ) = 1 := by rw [hy₁]; rfl
  /- (1) The layer misses `E`. -/
  have hdisj : Disjoint (layer d u) E := by
    rw [disjoint_left]
    intro e' he'u he'E
    obtain ⟨w₀, hw₀, hkw₀⟩ := layer_mem_E_same hX hi hE hG hEG hX0 (e := ⟨e', he'E⟩) he'u
      (hψu (mem_image_of_mem ψ y₀.2))
    obtain ⟨w₁, hw₁, hkw₁⟩ := layer_mem_E_same hX hi hE hG hEG hX0 (e := ⟨e', he'E⟩) he'u
      (hψu (mem_image_of_mem ψ y₁.2))
    by_cases ht : (3 / 22 : ℝ) ≤ (k ⟨e', he'E⟩ : ℝ)
    · have := hend.1 (y₀ : M) ⟨y₀, by show (k y₀ : ℝ) ≤ 2 / 22; rw [hk₀]; norm_num, rfl⟩ (w₀ : M)
        ⟨w₀, by show (3 / 22 : ℝ) ≤ (k w₀ : ℝ); rw [hkw₀]; exact ht, rfl⟩
      rw [hw₀] at this
      linarith [hψ y₀]
    · push_neg at ht
      have := hend.2 (y₁ : M) ⟨y₁, by show (20 / 22 : ℝ) ≤ (k y₁ : ℝ); rw [hk₁]; norm_num, rfl⟩
        (w₁ : M) ⟨w₁, by show (k w₁ : ℝ) ≤ 19 / 22; rw [hkw₁]; linarith, rfl⟩
      rw [hw₁] at this
      linarith [hψ y₁]
  /- The open set over `D`. -/
  set O : Set M := {m | π (m : Pt) ∈ F '' D'} with hOdef
  have hOo : IsOpen O := hR.isOpen.preimage (hπc.comp continuous_subtype_val)
  have hclO : ∀ C ⊆ O, closure C ⊆ {m : M | π (m : Pt) ∈ closure (F '' D')} := fun C hC =>
    closure_minimal (fun m hm => subset_closure (hC hm))
      (isClosed_closure.preimage (hπc.comp continuous_subtype_val))
  have hfr : ∀ q : M, π (q : Pt) ∈ closure (F '' D') → q ∉ O →
      (∃ t ∈ Icc (3 / 22 : ℝ) (19 / 22), π (q : Pt) = F (t, 0)) ∨
      (∃ w ∈ Icc 0 c₁, π (q : Pt) = F (3 / 22, w)) ∨
      (∃ w ∈ Icc 0 c₁, π (q : Pt) = F (19 / 22, w)) := by
    intro q hq hqO
    have hfront : π (q : Pt) ∈ frontier (F '' D') := by
      rw [hR.isOpen.frontier_eq]; exact ⟨hq, hqO⟩
    rcases hR.frontier_sub ⟨hfront, ⟨q, q.2, rfl⟩⟩ with
      (⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩ | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩) | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩
    · simp only [mem_singleton_iff] at hz2
      subst hz2
      exact Or.inl ⟨z₁, hz1, hFz.symm⟩
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      exact Or.inr (Or.inl ⟨z₂, hz2, hFz.symm⟩)
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      exact Or.inr (Or.inr ⟨z₂, hz2, hFz.symm⟩)
  /- Coarse monotonicity. -/
  have hnotb : ∀ y : E, (k y : ℝ) ≤ 7 / 11 → ∀ w ∈ Icc 0 c₁,
      π (ψ y : Pt) ≠ F (19 / 22, w) := by
    intro y hy w hw hq
    obtain ⟨e, -, he2, he3⟩ := hnear (ψ y) (19 / 22, w) ⟨⟨by norm_num, le_rfl⟩, hw⟩ hq
    have h2 := (abs_lt.1 he2).1
    have := he.sep_of_gap (m := 7) (by norm_num) (x := y) (y := e) (by push_cast; linarith)
      (by push_cast; linarith)
    linarith [dist_triangle (y : M) (ψ y) (e : M), hψ y]
  have hnota : ∀ y : E, 4 / 11 ≤ (k y : ℝ) → ∀ w ∈ Icc 0 c₁,
      π (ψ y : Pt) ≠ F (3 / 22, w) := by
    intro y hy w hw hq
    obtain ⟨e, -, he2, he3⟩ := hnear (ψ y) (3 / 22, w) ⟨⟨le_rfl, by norm_num⟩, hw⟩ hq
    have h2 := (abs_lt.1 he2).2
    have := he.sep_of_gap (m := 2) (by norm_num) (x := e) (y := y) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [dist_comm] at he3
    linarith [dist_triangle (e : M) (ψ y) (y : M), hψ y, dist_comm (y : M) (ψ y)]
  /- The ends are not over `D`. -/
  have hy₀O : ψ y₀ ∉ O := by
    intro hO
    obtain ⟨z, hz, hFz⟩ := hDsub hO
    obtain ⟨e, he1, -, he3⟩ := hnear (ψ y₀) z hz hFz.symm
    have := hend.1 (y₀ : M) ⟨y₀, by show (k y₀ : ℝ) ≤ 2 / 22; rw [hk₀]; norm_num, rfl⟩ (e : M)
      ⟨e, he1.1, rfl⟩
    linarith [dist_triangle (y₀ : M) (ψ y₀) (e : M), hψ y₀]
  have hy₁O : ψ y₁ ∉ O := by
    intro hO
    obtain ⟨z, hz, hFz⟩ := hDsub hO
    obtain ⟨e, he1, -, he3⟩ := hnear (ψ y₁) z hz hFz.symm
    have := hend.2 (y₁ : M) ⟨y₁, by show (20 / 22 : ℝ) ≤ (k y₁ : ℝ); rw [hk₁]; norm_num, rfl⟩
      (e : M) ⟨e, he1.2, rfl⟩
    linarith [dist_triangle (y₁ : M) (ψ y₁) (e : M), hψ y₁]
  /- Boundary bumping. -/
  have hbump : ∀ S : Set unitInterval, IsClosed S → IsPreconnected S → k x ∈ S →
      ∀ y' : E, k y' ∈ S → ψ y' ∉ O → ∃ q ∈ ψ '' layerSet k S, q ∉ O ∧
        q ∈ closure (connectedComponentIn (ψ '' layerSet k S ∩ O) (ψ x)) := by
    intro S hS hSp hxS y' hy'S hy'O
    have hZc : Fold.Q78.IsContinuum (layerSet k S) :=
      isContinuum_img hE.isCompact hE.2.1 hS hSp ⟨_, hxS⟩
    exact exists_mem_closure_component_notMem (hZc.1.image hψc)
      (hZc.2.isPreconnected.image _ hψc.continuousOn) hOo ⟨(x : M), ⟨x, hxS, rfl⟩, rfl⟩ hψx
      (fun hsub => hy'O (hsub ⟨(y' : M), ⟨y', hy'S, rfl⟩, rfl⟩))
  have hlayc := isClosed_layer hG.isCompact hG.2.1.1 u
  have hcomp : ∀ S : Set unitInterval,
      closure (connectedComponentIn (ψ '' layerSet k S ∩ O) (ψ x)) ⊆ layer d u :=
    fun S => closure_minimal ((connectedComponentIn_subset _ _).trans
      (inter_subset_left.trans ((image_mono (img_subset S)).trans hψu))) hlayc
  have hcompO : ∀ S : Set unitInterval, connectedComponentIn (ψ '' layerSet k S ∩ O) (ψ x) ⊆ O :=
    fun S => (connectedComponentIn_subset _ _).trans inter_subset_right
  have haxis : ∀ q ∈ layer d u, ∀ t ∈ Icc (3 / 22 : ℝ) (19 / 22), π (q : Pt) ≠ F (t, 0) :=
    fun q hq t ht hqt => disjoint_left.1 hdisj hq
      (mem_E_of_axis hE hπS hγπ hF ⟨by linarith [ht.1], by linarith [ht.2]⟩ hqt)
  obtain ⟨qL, ⟨_, ⟨yL, hyL, rfl⟩, rfl⟩, hqLO, hqLcl⟩ :=
    hbump (Iic (k x)) isClosed_Iic isPreconnected_Iic (mem_Iic.2 le_rfl) y₀
      (show k y₀ ≤ k x by rw [hy₀]; exact unitInterval.nonneg') hy₀O
  obtain ⟨qR, ⟨_, ⟨yR, hyR, rfl⟩, rfl⟩, hqRO, hqRcl⟩ :=
    hbump (Ici (k x)) isClosed_Ici isPreconnected_Ici (mem_Ici.2 le_rfl) y₁
      (show k x ≤ k y₁ by rw [hy₁]; exact unitInterval.le_one') hy₁O
  have hkyL : (k yL : ℝ) ≤ 7 / 11 := le_trans (Subtype.coe_le_coe.2 hyL) hx2
  have hkyR : 4 / 11 ≤ (k yR : ℝ) := le_trans hx1 (Subtype.coe_le_coe.2 hyR)
  have hqLW := hclO _ (hcompO _) hqLcl
  have hqRW := hclO _ (hcompO _) hqRcl
  have hL : ∃ w ∈ Icc 0 c₁, π (ψ yL : Pt) = F (3 / 22, w) := by
    rcases hfr _ hqLW hqLO with ⟨t, ht, h⟩ | h | ⟨w, hw, h⟩
    · exact absurd h (haxis _ (hcomp _ hqLcl) t ht)
    · exact h
    · exact absurd h (hnotb yL hkyL w hw)
  have hRt : ∃ w ∈ Icc 0 c₁, π (ψ yR : Pt) = F (19 / 22, w) := by
    rcases hfr _ hqRW hqRO with ⟨t, ht, h⟩ | ⟨w, hw, h⟩ | h
    · exact absurd h (haxis _ (hcomp _ hqRcl) t ht)
    · exact absurd h (hnota yR hkyR w hw)
    · exact h
  have hxmem : ∀ S : Set unitInterval, k x ∈ S →
      ψ x ∈ connectedComponentIn (ψ '' layerSet k S ∩ O) (ψ x) := fun S hxS =>
    mem_connectedComponentIn ⟨⟨(x : M), ⟨x, hxS, rfl⟩, rfl⟩, hψx⟩
  refine ⟨hdisj, closure (connectedComponentIn (ψ '' layerSet k (Iic (k x)) ∩ O) (ψ x)) ∪
    closure (connectedComponentIn (ψ '' layerSet k (Ici (k x)) ∩ O) (ψ x)), ?_, ?_, ?_, ?_, ?_⟩
  · exact IsPreconnected.union (ψ x) (subset_closure (hxmem (Iic (k x)) (mem_Iic.2 le_rfl)))
      (subset_closure (hxmem (Ici (k x)) (mem_Ici.2 le_rfl)))
      isPreconnected_connectedComponentIn.closure isPreconnected_connectedComponentIn.closure
  · exact union_subset (hcomp _) (hcomp _)
  · rintro z (hz | hz)
    · exact hclO _ (hcompO _) hz
    · exact hclO _ (hcompO _) hz
  · obtain ⟨w, hw, h⟩ := hL
    exact ⟨_, Or.inl hqLcl, ⟨(3 / 22, w), ⟨rfl, hw⟩, h.symm⟩⟩
  · obtain ⟨w, hw, h⟩ := hRt
    exact ⟨_, Or.inr hqRcl, ⟨(19 / 22, w), ⟨rfl, hw⟩, h.symm⟩⟩

/-- **§4, uniform height.** `crossing_descends_aux` (D2) with the height chosen before `G`. -/
theorem crossing_descends_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ v : unitInterval, 0 < v → v < 1 → LayerCrossing d π F c₁ D' v →
      ∃ u : unitInterval, 0 < u ∧ u < v ∧ LayerCrossing d π F c₁ D' u := by
  have hε := he.pos
  have hπc := hπ.continuous
  set η := min ε₁ (1 / 22) with hη
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε₁ := min_le_left _ _
  have hη22 : η ≤ 1 / 22 := min_le_right _ _
  obtain ⟨cP, hcP, hcP1, hP⟩ := property3_translate_unif hX hi hE he hend hπ hπS hγπ hF
    hLch hEL hLG hP1
  obtain ⟨cD, hcD, hcD1, hD1⟩ := crossing_from_layer_translate_unif hX hi hE he hend hπc hπS hγπ hF
  obtain ⟨cT, hcT, hcT1, hthin⟩ := pi_thin_near_layer hE hπc hπS hγπ hF (a := 3 / 22)
    (b := 19 / 22) (by norm_num) (by norm_num) hη0
  refine ⟨min cP (min cD cT), lt_min hcP (lt_min hcD hcT), (min_le_left _ _).trans hcP1,
    fun G d hG hEG hX0 c₁ D' hc₁ hR v hv0 hv1 hv => ?_⟩
  have hP := hP G d hG hEG hX0
  have hD1 := hD1 G d hG hEG hX0
  have hc₁P : c₁ ≤ cP := hc₁.trans (min_le_left _ _)
  have hc₁D : c₁ ≤ cD := hc₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc₁T : c₁ ≤ cT := hc₁.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc₁1 : c₁ ≤ 1 := hc₁P.trans hcP1
  have hdisj := layerCrossing_disjoint hX hi hE hγπ hF hG hEG hX0 hc₁1 hv
  obtain ⟨Z, hZc, hZl, hZW, ⟨za, hza, hzaA⟩, ⟨zb, hzb, hzbB⟩⟩ := hv
  have hDsub : F '' D' ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    image_mono fun z hz => ⟨⟨(hR.sub hz).1.1.le, (hR.sub hz).1.2.le⟩, (hR.sub hz).2.1.le,
      (hR.sub hz).2.2.le⟩
  have hclD : closure (F '' D') ⊆ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁) :=
    closure_minimal hDsub (isCompact_collar_image hF (isCompact_Icc.prod isCompact_Icc)
      (rect_sub (by norm_num) (by norm_num) hc₁1)).isClosed
  have hlayc := isClosed_layer hG.isCompact hG.2.1.1 v
  have hWc : IsClosed {m : M | π (m : Pt) ∈ closure (F '' D')} :=
    isClosed_closure.preimage (hπc.comp continuous_subtype_val)
  have hBl : closure Z ⊆ layer d v := closure_minimal hZl hlayc
  have hBW : closure Z ⊆ {m : M | π (m : Pt) ∈ closure (F '' D')} := closure_minimal hZW hWc
  /- Heights: points of the layer over the closed strip are off the axis. -/
  have hpos : ∀ q ∈ layer d v, ∀ z ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁,
      π (q : Pt) = F z → 0 < z.2 := by
    rintro q hq ⟨z₁, z₂⟩ ⟨hz1, hz2⟩ hqz
    rcases hz2.1.lt_or_eq with h | h
    · exact h
    · exfalso
      simp only at h
      subst h
      exact disjoint_left.1 hdisj hq
        (mem_E_of_axis hE hπS hγπ hF ⟨by linarith [hz1.1], by linarith [hz1.2]⟩ hqz)
  /- (a) `Cl Z` is a crossing in the form of `hagopian76_property3_translate`. -/
  have hstrip : ∀ x ∈ closure Z, π (x : Pt) ∈ F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Ioc 0 cP) := by
    intro x hx
    obtain ⟨z, hz, hFz⟩ := hclD (hBW hx)
    exact ⟨z, ⟨hz.1, hpos x (hBl hx) z hz hFz.symm, hz.2.2.trans hc₁P⟩, hFz⟩
  have hside : ∀ {a' : ℝ}, a' ∈ Icc (3 / 22 : ℝ) (19 / 22) → ∀ q ∈ Z,
      π (q : Pt) ∈ F '' (({a'} : Set ℝ) ×ˢ Icc 0 c₁) →
      π (q : Pt) ∈ F '' (({a'} : Set ℝ) ×ˢ Ioc 0 cP) := by
    rintro a' ha' q hq ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩
    simp only [mem_singleton_iff] at hz1
    subst hz1
    have := hpos q (hZl hq) (z₁, z₂) ⟨ha', hz2⟩ hFz.symm
    exact ⟨(z₁, z₂), ⟨rfl, this, hz2.2.trans hc₁P⟩, hFz⟩
  obtain ⟨-, h, hh, hmid, hhG⟩ := hP (closure Z) hZc.closure hstrip
    ⟨za, subset_closure (subset_closure hza),
      hside ⟨le_rfl, by norm_num⟩ za hza hzaA⟩
    ⟨zb, subset_closure (subset_closure hzb),
      hside ⟨by norm_num, le_rfl⟩ zb hzb hzbB⟩ v hv0 hv1 (by rw [closure_closure]; exact hBl)
  /- (b) The point `p = h(x)`, `k(x) = 1/2`, lies over `D`. -/
  obtain ⟨x, hx⟩ := hE.2.1.2.1 ⟨1 / 2, by norm_num, by norm_num⟩
  have hkx : (k x : ℝ) = 1 / 2 := by rw [hx]
  have hpB : h x ∈ closure Z := by
    have := hmid ⟨(x : M), ⟨x, show (4 / 11 : ℝ) < (k x : ℝ) ∧ (k x : ℝ) < 7 / 11 by
      rw [hkx]; norm_num, rfl⟩, rfl⟩
    rwa [closure_closure] at this
  have hnear : ∀ (q : M) (z : ℝ × ℝ), z ∈ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁ →
      π (q : Pt) = F z → ∃ e : E, |(k e : ℝ) - z.1| < η ∧ dist q (e : M) < η := by
    intro q z hz hqz
    obtain ⟨e, -, he2, he3⟩ :=
      hthin q z ⟨hz.1, by linarith [hz.2.1, hc₁T], by linarith [hz.2.2, hc₁T]⟩ hqz
    exact ⟨e, he2, by rw [Subtype.dist_eq]; exact he3⟩
  have hpO : π (h x : Pt) ∈ F '' D' := by
    by_contra hpO
    have hfront : π (h x : Pt) ∈ frontier (F '' D') := by
      rw [hR.isOpen.frontier_eq]; exact ⟨hBW hpB, hpO⟩
    have hhx := hh x
    rcases hR.frontier_sub ⟨hfront, ⟨_, (h x).2, rfl⟩⟩ with
      (⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩ | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩) | ⟨⟨z₁, z₂⟩, ⟨hz1, hz2⟩, hFz⟩
    · simp only [mem_singleton_iff] at hz2
      subst hz2
      exact disjoint_left.1 hdisj (hBl hpB)
        (mem_E_of_axis hE hπS hγπ hF ⟨by linarith [hz1.1], by linarith [hz1.2]⟩ hFz.symm)
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      obtain ⟨e, he2, he3⟩ := hnear (h x) (3 / 22, z₂) ⟨⟨le_rfl, by norm_num⟩, hz2⟩ hFz.symm
      have h2 := (abs_lt.1 he2).2
      have := he.sep_of_gap (m := 2) (by norm_num) (x := e) (y := x) (by push_cast; linarith)
        (by push_cast; rw [hkx]; norm_num)
      linarith [dist_triangle (e : M) (h x) (x : M), dist_comm (e : M) (h x),
        dist_comm (x : M) (h x)]
    · simp only [mem_singleton_iff] at hz1
      subst hz1
      obtain ⟨e, he2, he3⟩ := hnear (h x) (19 / 22, z₂) ⟨⟨by norm_num, le_rfl⟩, hz2⟩ hFz.symm
      have h2 := (abs_lt.1 he2).1
      have hx7 : (k x : ℝ) ≤ ((7 : ℕ) : ℝ) / 11 := by rw [hkx]; norm_num
      have := he.sep_of_gap (m := 7) (by norm_num) (x := x) (y := e) hx7 (by push_cast; linarith)
      linarith [dist_triangle (x : M) (h x) (e : M)]
  /- (c) The shift. -/
  have hOo : IsOpen {m : M | π (m : Pt) ∈ F '' D'} :=
    hR.isOpen.preimage (hπc.comp continuous_subtype_val)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hOo (h x) hpO
  obtain ⟨u, hu0, huv, g, hg, hgv⟩ := hagopian76_property3_shift hX hi hG hv0 hv1
    (lt_min hδ₀ hε : 0 < min δ₀ ε₁)
  refine ⟨u, hu0, huv, ?_⟩
  have hψc : Continuous (fun m => g (h m)) := g.continuous.comp h.continuous
  have hψ : ∀ m : M, dist m (g (h m)) < 2 * ε₁ := fun m => by
    linarith [dist_triangle m (h m) (g (h m)), hh m, hg (h m), min_le_right δ₀ ε₁]
  have hψu : (fun m => g (h m)) '' E ⊆ layer d u := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← hgv]
    exact ⟨h m, hhG ⟨m, hEG hm, rfl⟩, rfl⟩
  have hψx : π (g (h x) : Pt) ∈ F '' D' := by
    have : g (h x) ∈ ball (h x) δ₀ := by
      rw [mem_ball, dist_comm]
      exact lt_of_lt_of_le (hg (h x)) (min_le_left _ _)
    exact hball this
  exact (hD1 c₁ D' hc₁D hR (fun m => g (h m)) hψc hψ u hψu x (by rw [hkx]; norm_num)
    (by rw [hkx]; norm_num) hψx).2

/-- **§4, uniform height.** `property3_layer_aux` with the height chosen before `G`. -/
theorem property3_layer_unif (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (G : Set M) (d : G → unitInterval), IsMinimalAdmissible G d → E ⊆ G →
      layer d 0 = layer k 0 → ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ v : unitInterval, v < 1 → ¬ LayerCrossing d π F c₁ D' v := by
  obtain ⟨c, hc, hc1, hD2⟩ := crossing_descends_unif hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG
    hP1
  refine ⟨c, hc, hc1, fun G d hG hEG hX0 c₁ D' hc₁ hR v hv1 hv => ?_⟩
  have hD2 := hD2 G d hG hEG hX0
  have hc₁1 : c₁ ≤ 1 := hc₁.trans hc1
  set T := {u | LayerCrossing d π F c₁ D' u} ∩ Iic v with hT
  have hTc : IsClosed T :=
    (isClosed_layerCrossing hG.isCompact hG.2.1.1 hπ.continuous hF hc₁1 D').inter isClosed_Iic
  obtain ⟨u, ⟨huT, huv⟩, hleast⟩ := hTc.isCompact.exists_isLeast ⟨v, hv, mem_Iic.2 le_rfl⟩
  have hu0 : 0 < u := by
    rcases eq_or_lt_of_le (unitInterval.nonneg' : (0 : unitInterval) ≤ u) with h | h
    · exfalso
      have hdisj := layerCrossing_disjoint hX hi hE hγπ hF hG hEG hX0 hc₁1 huT
      rw [← h, hX0] at hdisj
      obtain ⟨e, he⟩ := layer_nonempty hE.2.1.2.1 0
      exact disjoint_left.1 hdisj he (by obtain ⟨y, -, rfl⟩ := he; exact y.2)
    · exact h
  obtain ⟨u', -, hu'u, hu'⟩ := hD2 c₁ D' hc₁ hR u hu0 (lt_of_le_of_lt huv hv1) huT
  exact absurd (hleast ⟨hu', hu'u.le.trans huv⟩) (not_le.2 hu'u)

end Uniform

end HPC.Hagopian
