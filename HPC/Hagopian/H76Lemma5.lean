import HPC.Hagopian.Hagopian76A

/-!
# Batch 157, item B.1: Lemma 5 at the layers other than the end sets

Hagopian 1976, Lemma 5 (p. 341): "The decomposition of `E` is continuous." At a layer
`Y = k⁻¹(c)`, `0 < c < 1`, lower semicontinuity follows from Lemmas 2 and 3 with `F := E`, without
Hagopian's continuum `F` and without the first paragraph of Lemma 4 (D1):

* fix `y ∈ Y` and an open `V ∋ y`, with `ball y η ⊆ V`; choose `γ` with `[c − γ, c + γ] ⊂ (0, 1)`, and
  `ε < η` below the distance from `k⁻¹[[c − γ, c + γ]]` to `X ∪ Z`;
* `W` is the set of points `z` with `k z ∈ (c − γ, c + γ)` that are images of points of `Y` under
  `ε`-homeomorphisms of `M`; it is open (Lemma 2) and contains `Y`;
* for `z ∈ W`, `z = h(y')`, Lemma 3 (`T = X`, `V = Z`, `U = k⁻¹(k z)`) gives `h[Y] = k⁻¹(k z)`; so
  `h(y)` is a point of the layer of `z` within `ε < η` of `y`, hence in `V`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Lemma5

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Lemma 5 at the layers other than the end sets** (lower semicontinuity). -/
theorem lemma5_interior_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k) (x : E)
    (hx0 : 0 < k x) (hx1 : k x < 1) : LSCAt (Setoid.ker k) x := by
  have hk : Continuous k := hE.2.1.1
  have hks : Function.Surjective k := hE.2.1.2.1
  set c := k x with hc
  intro y hy V hV hyV
  have hyc : k y = c := hy
  obtain ⟨η, hη, hηV⟩ := Metric.isOpen_iff.1 hV y hyV
  -- `γ`
  set γ : ℝ := min (c : ℝ) (1 - c) / 2 with hγ
  have hc0 : (0 : ℝ) < c := hx0
  have hc1 : (c : ℝ) < 1 := hx1
  have hγ0 : 0 < γ := by
    have : 0 < min (c : ℝ) (1 - c) := lt_min hc0 (by linarith)
    positivity
  have hγlo : 0 < (c : ℝ) - γ := by
    have := min_le_left (c : ℝ) (1 - c); linarith
  have hγhi : (c : ℝ) + γ < 1 := by
    have := min_le_right (c : ℝ) (1 - c); linarith
  -- the compact `K = k⁻¹[[c − γ, c + γ]]` and the end sets `Z01`
  set K : Set E := {z | (c : ℝ) - γ ≤ k z ∧ (k z : ℝ) ≤ c + γ} with hK
  set Z01 : Set E := {z | k z = 0 ∨ k z = 1} with hZ01
  have hKc : IsCompact K := by
    refine IsClosed.isCompact ?_
    exact (isClosed_le continuous_const (continuous_subtype_val.comp hk)).inter
      (isClosed_le (continuous_subtype_val.comp hk) continuous_const)
  have hZc : IsClosed Z01 :=
    (isClosed_singleton.preimage hk).union (isClosed_singleton.preimage hk)
  obtain ⟨z0, hz0⟩ := hks 0
  have hZne : Z01.Nonempty := ⟨z0, Or.inl hz0⟩
  have hKZ : ∀ z ∈ K, z ∉ Z01 := by
    rintro z ⟨h1, h2⟩ (h | h)
    · rw [h] at h1; simp at h1; linarith
    · rw [h] at h2; simp at h2; linarith
  have hxK : x ∈ K := ⟨by linarith, by linarith⟩
  obtain ⟨z₁, hz₁K, hmin⟩ := hKc.exists_isMinOn ⟨x, hxK⟩ (continuous_infDist_pt Z01).continuousOn
  set δ₀ := infDist z₁ Z01
  have hδ₀ : 0 < δ₀ := (hZc.notMem_iff_infDist_pos hZne).1 (hKZ z₁ hz₁K)
  have hsep : ∀ z ∈ K, ∀ w ∈ Z01, δ₀ ≤ dist z w := fun z hz w hw =>
    (hmin hz).trans (infDist_le_dist_of_mem hw)
  set ε := min η δ₀ / 2 with hε
  have hε0 : 0 < ε := by have := lt_min hη hδ₀; positivity
  have hεη : ε < η := by have := min_le_left η δ₀; linarith
  have hεδ : ε < δ₀ := by have := min_le_right η δ₀; linarith
  -- the open set `W`
  set O : M → Set M := fun y' => {w : M | ∃ h : M ≃ₜ M, h y' = w ∧ ∀ v, dist v (h v) < ε}
  set W : Set E := {z | (k z : ℝ) ∈ Ioo ((c : ℝ) - γ) (c + γ)} ∩
    ⋃ y' ∈ {y' : E | k y' = c}, Subtype.val ⁻¹' O (y' : M) with hW
  refine ⟨W, ?_, ?_, ?_⟩
  · refine IsOpen.inter (isOpen_Ioo.preimage (continuous_subtype_val.comp hk)) ?_
    exact isOpen_biUnion fun y' _ => ((hagopian76_lemma2 hX hε0 (y' : M)).1).preimage
      continuous_subtype_val
  · intro z hz
    have hzc : k z = c := hz
    refine ⟨?_, mem_iUnion₂.2 ⟨z, hzc, (hagopian76_lemma2 hX hε0 (z : M)).2⟩⟩
    show (k z : ℝ) ∈ Ioo ((c : ℝ) - γ) (c + γ)
    rw [hzc]; exact ⟨by linarith, by linarith⟩
  · rintro z ⟨hzI, hzO⟩
    obtain ⟨y', hy'c, h, hhy', hhε⟩ := mem_iUnion₂.1 hzO
    have hy'c : k y' = c := hy'c
    have hzK : z ∈ K := ⟨hzI.1.le, hzI.2.le⟩
    -- Lemma 3
    have hL3 : h '' layer k c = layer k (k z) := by
      refine hagopian76_lemma3 hX hi hE hE hx0 hx1 h ⟨(z : M), ⟨z, rfl, rfl⟩, ⟨(y' : M),
        ⟨y', hy'c, rfl⟩, hhy'⟩⟩ ?_ ?_
      · rw [Set.disjoint_iff]
        rintro w ⟨⟨w', hw', rfl⟩, ⟨_, ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩, hvw⟩⟩
        · have hw'K : w' ∈ K := by
            have : k w' = k z := hw'
            exact ⟨this ▸ hzK.1, this ▸ hzK.2⟩
          have h1 := hsep w' hw'K v (Or.inl hv)
          have h2 := hhε (v : M)
          rw [hvw] at h2
          have : dist w' v = dist (v : M) (w' : M) := by rw [dist_comm]; rfl
          linarith
        · have hw'K : w' ∈ K := by
            have : k w' = k z := hw'
            exact ⟨this ▸ hzK.1, this ▸ hzK.2⟩
          have h1 := hsep w' hw'K v (Or.inr hv)
          have h2 := hhε (v : M)
          rw [hvw] at h2
          have : dist w' v = dist (v : M) (w' : M) := by rw [dist_comm]; rfl
          linarith
      · rw [Set.disjoint_iff]
        rintro w ⟨⟨_, ⟨v, hv, rfl⟩, rfl⟩, ⟨w', hw', hw'w⟩ | ⟨w', hw', hw'w⟩⟩
        · have hvK : v ∈ K := by
            have : k v = c := hv
            rw [hK, mem_setOf_eq, this]; exact ⟨by linarith, by linarith⟩
          have h1 := hsep v hvK w' (Or.inl hw')
          have h2 := hhε (v : M)
          rw [← hw'w] at h2
          have : dist v w' = dist (v : M) (w' : M) := rfl
          linarith
        · have hvK : v ∈ K := by
            have : k v = c := hv
            rw [hK, mem_setOf_eq, this]; exact ⟨by linarith, by linarith⟩
          have h1 := hsep v hvK w' (Or.inr hw')
          have h2 := hhε (v : M)
          rw [← hw'w] at h2
          have : dist v w' = dist (v : M) (w' : M) := rfl
          linarith
    -- `h(y)` is in the layer of `z`, close to `y`
    have hhy : h (y : M) ∈ layer k (k z) := hL3 ▸ ⟨(y : M), ⟨y, hyc, rfl⟩, rfl⟩
    obtain ⟨e', he', he'y⟩ := hhy
    refine ⟨e', he', hηV ?_⟩
    rw [mem_ball]
    have h2 := hhε (y : M)
    rw [← he'y] at h2
    have : dist e' y = dist (y : M) (e' : M) := by rw [dist_comm]; rfl
    linarith

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Upper semicontinuity** of the decomposition into the fibres of a continuous map on a compact
space (the first half of Lemma 5; Hagopian: "Since `A` is upper semicontinuous"). -/
theorem isUSCDecomp_ker {X : Type*} [MetricSpace X] [CompactSpace X] {k : X → unitInterval}
    (hk : Continuous k) : IsUSCDecomp (Setoid.ker k) := by
  refine ⟨fun x => isClosed_singleton.preimage hk, fun x U hU hxU => ?_⟩
  have hC : IsClosed (k '' Uᶜ) := (hU.isClosed_compl.isCompact.image hk).isClosed
  refine ⟨k ⁻¹' (k '' Uᶜ)ᶜ, hC.isOpen_compl.preimage hk, fun z hz => ?_, fun z hz w hw => ?_⟩
  · rintro ⟨w, hwU, hwz⟩
    exact hwU (hxU (show k w = k x from hwz.trans hz))
  · by_contra hwU
    exact hz ⟨w, hwU, hw⟩

/-- **Lemma 5, reduced to the end sets.** With `lemma5_interior_aux` and `isUSCDecomp_ker`, the
decomposition of `E` is continuous as soon as it is lower semicontinuous at the two end sets. -/
theorem lemma5_of_ends_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} [CompactSpace E] {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hends : ∀ x, (k x = 0 ∨ k x = 1) → LSCAt (Setoid.ker k) x) :
    IsContinuousDecomp (Setoid.ker k) := by
  refine ⟨isUSCDecomp_ker hE.2.1.1, fun x => ?_⟩
  by_cases h0 : k x = 0
  · exact hends x (Or.inl h0)
  by_cases h1 : k x = 1
  · exact hends x (Or.inr h1)
  exact lemma5_interior_aux hX hi hE x (lt_of_le_of_ne unitInterval.nonneg' (Ne.symm h0))
    (lt_of_le_of_ne unitInterval.le_one' h1)

end Lemma5

end HPC.Hagopian
