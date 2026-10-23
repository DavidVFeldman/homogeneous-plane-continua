import HPC.Hagopian.H76D1
import HPC.Hagopian.H76Lemma5
import HPC.Hagopian.H76Lemma4Ext

/-!
# Batch 158, item A: D1 by lower semicontinuity of the larger continuum

Hagopian 1976, Lemma 4, first paragraph (p. 341), in the strong form of commission 158 §1. For an
extension `F` of `E` away from `X = k⁻¹(0)`, with map `d` and `s = max d|E`:

* if `s = 1`, then `E` meets both end sets of `F` and `E = F` (`end_sets_aux`);
* if `s < 1`, then `W = d⁻¹(s)` is a layer of `F` that is not an end set, so the decomposition of `F`
  is lower semicontinuous at `W` (`lemma5_interior_aux` applied to `F`); some `y ∈ W` is a limit of
  points of `d⁻¹([0, s))` (connectedness of `d⁻¹[[0, s]]`); the layers of `F` below `s` are layers of
  `E` (`lemma4_layers_aux`); so every `w ∈ W` is a limit of points `z` of `E` whose parameters
  `k z` tend to `k y` (continuity of `k` at `y`), and `W ⊆ k⁻¹(k y)`. Since `k⁻¹(1) ⊆ W`, `k y = 1`
  and `W = k⁻¹(1)`.

The commission's step 5 invokes the upper semicontinuity of `E`; the continuity of `k` (which is
what upper semicontinuity of the decomposition into the fibres of `k` amounts to) is what is used.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Far

variable {M : Set Pt}

/-- `lemma4_layers_aux`, with the supplied step `k⁻¹(1) ⊆ d⁻¹(s)` (batch 157, in the proof of
`lemma4_layers_of_no_swallowed`). -/
theorem lemma4_layers_far {E F : Set M} {k : E → unitInterval} {d : F → unitInterval}
    (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F)
    (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ layerSet d (Ico 0 s) ⊆ E ∧ E ⊆ layerSet d (Icc 0 s) ∧
      (∀ t, ∃ u, layer k t ⊆ layer d u) ∧
      (∀ t u, u < s → layer k t ⊆ layer d u → layer k t = layer d u) ∧
      (∀ t u, layer k t ⊆ layer d u → u ≤ s) ∧ layer k 1 ⊆ layer d s := by
  obtain ⟨s, hs0, hlow, hup, hin, heq⟩ := lemma4_layers_aux hE hF hEF hX0
  have hks := hE.2.1.2.1
  have hds := hF.2.1.2.1
  have hle : ∀ t u, layer k t ⊆ layer d u → u ≤ s := fun t u htu => by
    obtain ⟨x, hx⟩ := layer_nonempty hks t
    obtain ⟨y, hy, hyx⟩ := hup (img_subset _ hx)
    have h1 : (x : M) ∈ layer d (d y) := ⟨y, rfl, hyx⟩
    rw [layer_param_eq (htu hx) h1]
    exact hy.2
  refine ⟨s, hs0, hlow, hup, hin, heq, hle, ?_⟩
  obtain ⟨u, hu⟩ := hin 1
  rcases (hle 1 u hu).lt_or_eq with hus | rfl
  · exfalso
    have hZu := heq 1 u hus hu
    set C := layerSet d (Icc 0 u)
    have hC : Fold.Q78.IsContinuum C :=
      isContinuum_img hF.isCompact hF.2.1 isClosed_Icc isPreconnected_Icc
        ⟨0, unitInterval.nonneg', unitInterval.nonneg'⟩
    have hCE : C ⊆ E := by
      rintro _ ⟨y, hy, rfl⟩
      exact hlow ⟨y, ⟨hy.1, lt_of_le_of_lt hy.2 hus⟩, rfl⟩
    have h0 : (C ∩ layer k 0).Nonempty := by
      obtain ⟨x, hx⟩ := layer_nonempty hks 0
      refine ⟨x, ?_, hx⟩
      rw [← hX0] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy) ▸ unitInterval.nonneg'⟩, rfl⟩
    have h1 : (C ∩ layer k 1).Nonempty := by
      obtain ⟨x, hx⟩ := layer_nonempty hks 1
      refine ⟨x, ?_, hx⟩
      rw [hZu] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, ⟨unitInterval.nonneg', (mem_singleton_iff.1 hy).le⟩, rfl⟩
    have hCeq := end_sets_aux hE hCE hC h0 h1
    obtain ⟨v, huv, hvs⟩ := exists_between hus
    obtain ⟨y, hy⟩ := hds v
    have hyE : (y : M) ∈ E := hlow ⟨y, ⟨unitInterval.nonneg', hy ▸ hvs⟩, rfl⟩
    rw [← hCeq] at hyE
    obtain ⟨y', hy', hyy⟩ := hyE
    have : y' = y := Subtype.ext hyy
    rw [this] at hy'
    have h2 : d y ≤ u := hy'.2
    rw [hy] at h2
    exact absurd h2 (not_le.2 huv)
  · exact hu

/-- In a continuum `C = A ∪ B` with `A`, `B` disjoint and nonempty and `B` closed, `B` meets the
closure of `A`. -/
theorem closure_inter_of_preconnected {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hC : IsPreconnected (A ∪ B)) (hB : IsClosed B) (hA : A.Nonempty) (hBn : B.Nonempty) :
    (closure A ∩ B).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hcov : A ∪ B ⊆ Bᶜ ∪ (closure A)ᶜ := by
    intro x hx
    by_cases hxB : x ∈ B
    · right
      intro hxA
      have : x ∈ closure A ∩ B := ⟨hxA, hxB⟩
      rw [hne] at this
      exact this
    · exact Or.inl hxB
  have hdisj : (A ∪ B) ∩ (Bᶜ ∩ (closure A)ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro x ⟨hx | hx, h1, h2⟩
    · exact h2 (subset_closure hx)
    · exact h1 hx
  rcases isPreconnected_iff_subset_of_disjoint.1 hC Bᶜ (closure A)ᶜ hB.isOpen_compl
      isClosed_closure.isOpen_compl hcov hdisj with h | h
  · obtain ⟨b, hb⟩ := hBn
    exact h (Or.inr hb) hb
  · obtain ⟨a, ha⟩ := hA
    exact h (Or.inl ha) (subset_closure ha)

theorem layer_subset_dom {X : Type*} {E : Set X} (k : E → unitInterval) (t : unitInterval) :
    layer k t ⊆ E := by
  rintro _ ⟨e, -, rfl⟩
  exact e.2

/-- **Item A, the far layer** (commission 158 §1), with all the bookkeeping of
`lemma4_layers_far`: if `s = 1` then `F = E`; if `s < 1` then `d⁻¹(s) = k⁻¹(1)`. -/
theorem far_layer_aux [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {E F : Set M} {k : E → unitInterval} {d : F → unitInterval}
    (hE : IsMinimalAdmissible E k) (hF : IsMinimalAdmissible F d) (hEF : E ⊆ F)
    (hX0 : layer d 0 = layer k 0) :
    ∃ s : unitInterval, 0 < s ∧ layerSet d (Ico 0 s) ⊆ E ∧ E ⊆ layerSet d (Icc 0 s) ∧
      (∀ t, ∃ u, layer k t ⊆ layer d u) ∧
      (∀ t u, u < s → layer k t ⊆ layer d u → layer k t = layer d u) ∧
      (∀ t u, layer k t ⊆ layer d u → u ≤ s) ∧ layer k 1 ⊆ layer d s ∧
      (s = 1 → F = E) ∧ (s < 1 → layer d s = layer k 1) := by
  obtain ⟨s, hs0, hlow, hup, hin, heq, hle, hZ⟩ := lemma4_layers_far hE hF hEF hX0
  have hks := hE.2.1.2.1
  have hds := hF.2.1.2.1
  refine ⟨s, hs0, hlow, hup, hin, heq, hle, hZ, ?_, ?_⟩
  · rintro rfl
    have hEc : Fold.Q78.IsContinuum E := by
      obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE
      exact hab.1
    obtain ⟨x0, hx0⟩ := layer_nonempty hks 0
    obtain ⟨x1, hx1⟩ := layer_nonempty hks 1
    exact (end_sets_aux hF hEF hEc ⟨x0, layer_subset_dom k 0 hx0, hX0 ▸ hx0⟩
      ⟨x1, layer_subset_dom k 1 hx1, hZ hx1⟩).symm
  · intro hs1
    haveI : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
    have hEcl : IsClosed E := hE.isCompact.isClosed
    set A := layerSet d (Ico 0 s) with hA
    set B := layer d s with hB
    have hAB : A ∪ B = layerSet d (Icc 0 s) := by
      ext x
      simp only [hA, hB, layerSet, layer, mem_union, mem_image, mem_preimage, mem_Ico, mem_Icc,
        mem_singleton_iff]
      constructor
      · rintro (⟨y, ⟨h1, h2⟩, rfl⟩ | ⟨y, h, rfl⟩)
        · exact ⟨y, ⟨h1, h2.le⟩, rfl⟩
        · exact ⟨y, ⟨h ▸ unitInterval.nonneg', h.le⟩, rfl⟩
      · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
        rcases h2.lt_or_eq with h | h
        · exact Or.inl ⟨y, ⟨h1, h⟩, rfl⟩
        · exact Or.inr ⟨y, h, rfl⟩
    have hCpc : IsPreconnected (A ∪ B) := by
      rw [hAB]
      exact (isContinuum_img hF.isCompact hF.2.1 isClosed_Icc isPreconnected_Icc
        ⟨0, unitInterval.nonneg', unitInterval.nonneg'⟩).2.isPreconnected
    have hBc : IsClosed B := (isCompact_img hF.isCompact hF.2.1.1 isClosed_singleton).isClosed
    have hAn : A.Nonempty := by
      obtain ⟨y, hy⟩ := hds 0
      exact ⟨y, y, ⟨by rw [hy], by rw [hy]; exact hs0⟩, rfl⟩
    obtain ⟨y, hyA, hyB⟩ := closure_inter_of_preconnected hCpc hBc hAn (layer_nonempty hds s)
    have hyE : y ∈ E := hEcl.closure_subset_iff.2 hlow hyA
    obtain ⟨y', hy's, rfl⟩ := hyB
    have hy's' : d y' = s := hy's
    set c := k ⟨y', hyE⟩ with hc
    have hLSC := lemma5_interior_aux hX hi hF y' (by rw [hy's']; exact hs0)
      (by rw [hy's']; exact hs1)
    -- every point of `d⁻¹(s)` is a limit of points of `E` with parameters near `c`
    have hclaim : ∀ w' : F, d w' = s → ∃ hwE : (w' : M) ∈ E, k ⟨w', hwE⟩ = c := by
      intro w' hw's
      have happrox : ∀ ε > 0, ∃ z : E, dist (z : M) (w' : M) < ε ∧ dist (k z) c < ε := by
        intro ε hε
        obtain ⟨δ₁, hδ₁, hk1⟩ :=
          Metric.continuousAt_iff.1 (hE.2.1.1.continuousAt (x := ⟨y', hyE⟩)) ε hε
        obtain ⟨W, hWo, hWc, hWz⟩ := hLSC w' (show d w' = d y' by rw [hw's, hy's'])
          (ball w' ε) isOpen_ball (mem_ball_self hε)
        obtain ⟨δ₂, hδ₂, hball⟩ := Metric.isOpen_iff.1 hWo y' (hWc (mem_cls_self y'))
        obtain ⟨a, haA, hay⟩ := Metric.mem_closure_iff.1 hyA (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
        obtain ⟨a', ha's, rfl⟩ := haA
        have haE : (a' : M) ∈ E := hlow ⟨a', ha's, rfl⟩
        have ha'W : a' ∈ W := hball (by
          rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hay (min_le_right _ _))
        obtain ⟨z', hz'cls, hz'V⟩ := hWz a' ha'W
        have hz'cls' : d z' = d a' := hz'cls
        obtain ⟨u, hu⟩ := hin (k ⟨a', haE⟩)
        have hau : (a' : M) ∈ layer d u := hu ⟨⟨a', haE⟩, rfl, rfl⟩
        have hua : u = d a' := layer_param_eq hau ⟨a', rfl, rfl⟩
        have hus : u < s := hua ▸ ha's.2
        have hlay := heq _ u hus hu
        have hz'u : (z' : M) ∈ layer d u := ⟨z', by rw [hua]; exact hz'cls', rfl⟩
        rw [← hlay] at hz'u
        obtain ⟨z, hzk, hzz⟩ := hz'u
        refine ⟨z, ?_, ?_⟩
        · rw [hzz]; exact hz'V
        · have hzk' : k z = k ⟨a', haE⟩ := hzk
          rw [hzk']
          apply hk1
          show dist (a' : M) (y' : M) < δ₁
          rw [dist_comm]; exact lt_of_lt_of_le hay (min_le_left _ _)
      have hwE : (w' : M) ∈ E := hEcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => by
        obtain ⟨z, h1, -⟩ := happrox ε hε
        exact ⟨z, z.2, by rw [dist_comm]; exact h1⟩)
      refine ⟨hwE, eq_of_forall_dist_le fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hkw⟩ := Metric.continuousAt_iff.1
        (hE.2.1.1.continuousAt (x := ⟨w', hwE⟩)) (ε / 2) (half_pos hε)
      obtain ⟨z, h1, h2⟩ := happrox (min δ (ε / 2)) (lt_min hδ (half_pos hε))
      have h3 : dist (k z) (k ⟨w', hwE⟩) < ε / 2 :=
        hkw (show dist (z : M) (w' : M) < δ from lt_of_lt_of_le h1 (min_le_left _ _))
      calc dist (k ⟨w', hwE⟩) c ≤ dist (k ⟨w', hwE⟩) (k z) + dist (k z) c := dist_triangle _ _ _
        _ ≤ ε / 2 + ε / 2 := by
          rw [dist_comm] at h3
          have := lt_of_lt_of_le h2 (min_le_right _ _)
          linarith
        _ = ε := by ring
    -- `c = 1`
    have hc1 : c = 1 := by
      obtain ⟨x1, hx1⟩ := layer_nonempty hks 1
      obtain ⟨e, he1, rfl⟩ := hx1
      obtain ⟨w'', hw''s, hw''e⟩ := hZ ⟨e, he1, rfl⟩
      obtain ⟨hwE, hkw⟩ := hclaim w'' hw''s
      have : (⟨w'', hwE⟩ : E) = e := Subtype.ext hw''e
      rw [← hkw, this]; exact he1
    refine Subset.antisymm ?_ hZ
    rintro _ ⟨w', hw's, rfl⟩
    obtain ⟨hwE, hkw⟩ := hclaim w' hw's
    exact ⟨⟨w', hwE⟩, show k _ = 1 by rw [hkw, hc1], rfl⟩

end Far

end HPC.Hagopian
