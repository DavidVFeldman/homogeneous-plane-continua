import HPC.Hagopian.H76Prop1

/-!
# Batch 161, item T14 (Property 3): the step "By Lemmas 2 and 3"

Hagopian 1976, p. 347, proof of Property 3: "By Lemmas 2 and 3, a homeomorphism `g` of `M` onto `M`
and a point `u` of `[0, v)` exist such that `gd⁻¹(v) = d⁻¹(u)` …"

`layer_shift`: for a type A′ continuum `F` of `M` (map `d`), an interior layer `d⁻¹(v)` and `δ > 0`,
there are `u ∈ (0, v)` and a `δ`-homeomorphism `g` with `g[d⁻¹(v)] = d⁻¹(u)`. Proof: Lemma 5 (the
decomposition is continuous) puts a layer `d⁻¹(u)`, `u < v`, through every neighbourhood of a point
`z ∈ d⁻¹(v)` (the continuum `d⁻¹[[v/2, v]]` is not the layer `d⁻¹(v)`), Lemma 2 gives a `δ`-homeomorphism
`g` taking `z` into that layer, and Lemma 3 (`lemma3_aux`) gives `g[d⁻¹(v)] = d⁻¹(u)` once `δ` is
below half the distance from `d⁻¹[[v/2, v]]` to the end sets.

The remaining part of Property 3 — that `d⁻¹(u)` again contains a component of `F ∩ π⁻¹[D]` whose
closure meets both verticals — is open (`Hagopian76F.lean`, `OPEN.md`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Prop3

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Lemmas 2 and 3 in the proof of Property 3**: an interior layer is carried onto an earlier
layer by an arbitrarily small homeomorphism. -/
theorem layer_shift (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {F : Set M}
    {d : F → unitInterval} (hF : IsMinimalAdmissible F d) {v : unitInterval} (hv0 : 0 < v)
    (hv1 : v < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : unitInterval, 0 < u ∧ u < v ∧ ∃ g : M ≃ₜ M, (∀ x, dist x (g x) < δ) ∧
      g '' layer d v = layer d u := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  have hcont := hagopian76_lemma5 hX hi hF
  have hFc := hF.isCompact
  have hd := hF.2.1
  -- the parameter `a = v/2`
  set a : unitInterval := ⟨(v : ℝ) / 2, by have := v.2.1; positivity,
    by have := v.2.2; linarith⟩ with ha
  have hv0' : (0 : ℝ) < v := hv0
  have hv1' : (v : ℝ) < 1 := hv1
  have ha0 : (0 : ℝ) < a := by simp only [a]; positivity
  have hav : a < v := by show (v : ℝ) / 2 < v; linarith
  -- distance from `d⁻¹[[a, v]]` to the end sets
  have hdisj : Disjoint (layerSet d (Icc a v)) (layer d 0 ∪ layer d 1) := by
    rw [disjoint_left]
    rintro _ ⟨e, he, rfl⟩ hx
    rcases hx with ⟨e', he', hee'⟩ | ⟨e', he', hee'⟩
    · have := Subtype.val_injective hee'
      subst this
      have h1 : d e' = 0 := he'
      have h2 : a ≤ d e' := he.1
      rw [h1] at h2
      have : (a : ℝ) ≤ 0 := h2
      linarith
    · have := Subtype.val_injective hee'
      subst this
      have h1 : d e' = 1 := he'
      have h2 : d e' ≤ v := he.2
      rw [h1] at h2
      have : (1 : ℝ) ≤ v := h2
      linarith
  have hends : IsCompact (layer d 0 ∪ layer d 1) :=
    (isCompact_img hFc hd.1 isClosed_singleton).union (isCompact_img hFc hd.1 isClosed_singleton)
  obtain ⟨c, hc, hcd⟩ := exists_pos_le_dist (isCompact_img hFc hd.1 isClosed_Icc)
    hends.isClosed hdisj
  set η := min δ (c / 2)
  have hη : 0 < η := lt_min hδ (by positivity)
  -- a point of `d⁻¹(v)`
  obtain ⟨z, hz⟩ := hd.2.1 v
  obtain ⟨hWo, hzW⟩ := lemma2_aux hX hη (z : M)
  set W := {y : M | ∃ g : M ≃ₜ M, g z = y ∧ ∀ w, dist w (g w) < η}
  -- lower semicontinuity at `z`
  obtain ⟨O, hO, hzO, hOW⟩ := hcont.2 z z (Setoid.ker_iff_mem_preimage.2 rfl)
    (Subtype.val ⁻¹' W) (hWo.preimage continuous_subtype_val) hzW
  obtain ⟨O₁, hO₁, hO₁O⟩ := isOpen_induced_iff.1 hO
  -- a point of `O` in `d⁻¹[[a, v)]`
  set S := layerSet d (Icc a v)
  have hS : IsPreconnected S :=
    (isContinuum_img hFc hd isClosed_Icc isPreconnected_Icc ⟨a, le_rfl, hav.le⟩).2.2
  have hlayv : IsClosed (layer d v) := (isCompact_img hFc hd.1 isClosed_singleton).isClosed
  have hlayO : layer d v ⊆ O₁ := by
    rintro _ ⟨e, he, rfl⟩
    have : e ∈ cls (Setoid.ker d) z := by
      show d e = d z
      rw [hz]; exact he
    have := hzO this
    rw [← hO₁O] at this
    exact this
  obtain ⟨x, hxS, hxO₁, hxv⟩ : (S ∩ (O₁ ∩ (layer d v)ᶜ)).Nonempty := by
    refine hS O₁ (layer d v)ᶜ hO₁ hlayv.isOpen_compl ?_ ?_ ?_
    · intro x hx
      by_cases hxv : x ∈ layer d v
      · exact Or.inl (hlayO hxv)
      · exact Or.inr hxv
    · exact ⟨z, ⟨z, ⟨by rw [hz]; exact hav.le, by rw [hz]⟩, rfl⟩, hlayO ⟨z, hz, rfl⟩⟩
    · obtain ⟨w, hw⟩ := hd.2.1 a
      refine ⟨w, ⟨w, ⟨by rw [hw], by rw [hw]; exact hav.le⟩, rfl⟩, ?_⟩
      rintro ⟨w', hw', hww'⟩
      have := Subtype.val_injective hww'
      subst this
      have h1 : d w' = v := hw'
      rw [hw] at h1
      exact (ne_of_lt hav) h1
  obtain ⟨w, hwI, rfl⟩ := hxS
  have hwO : w ∈ O := by
    have : w ∈ Subtype.val ⁻¹' O₁ := hxO₁
    rw [hO₁O] at this
    exact this
  set u := d w with hu
  have huv : u ≠ v := fun h => hxv ⟨w, h, rfl⟩
  obtain ⟨w', hw'cls, hw'W⟩ := hOW w hwO
  have hw'u : d w' = u := hw'cls
  obtain ⟨g, hgz, hg⟩ := hw'W
  have hgδ : ∀ x, dist x (g x) < δ := fun x => (hg x).trans_le (min_le_left _ _)
  have hgc : ∀ x, dist x (g x) < c / 2 := fun x => (hg x).trans_le (min_le_right _ _)
  refine ⟨u, lt_of_lt_of_le (show (0 : unitInterval) < a from ha0) hwI.1,
    lt_of_le_of_ne hwI.2 huv, g, hgδ, ?_⟩
  -- Lemma 3
  have hlayu : layer d u ⊆ S := fun _ ⟨e, he, hex⟩ =>
    ⟨e, by rw [mem_preimage, mem_singleton_iff.1 he]; exact hwI, hex⟩
  have hlayvS : layer d v ⊆ S := fun _ ⟨e, he, hex⟩ =>
    ⟨e, by rw [mem_preimage, mem_singleton_iff.1 he]; exact ⟨hav.le, le_rfl⟩, hex⟩
  have hfar : ∀ p ∈ S, ∀ q ∈ layer d 0 ∪ layer d 1, dist p q < c → False :=
    fun p hp q hq hpq => by have := hcd p hp q hq; linarith
  refine lemma3_aux hHU hAT hF hF hv0 hv1 g ⟨g z, ⟨w', hw'u, hgz.symm⟩,
    ⟨z, ⟨z, hz, rfl⟩, rfl⟩⟩ ?_ ?_
  · rw [disjoint_left]
    rintro p hp ⟨q, hq, rfl⟩
    have := hgc q
    rw [dist_comm] at this
    exact hfar _ (hlayu hp) q hq (by linarith)
  · rw [disjoint_left]
    rintro _ ⟨q, hq, rfl⟩ hq'
    exact hfar q (hlayvS hq) _ hq' (by have := hgc q; linarith)

end Prop3

end HPC.Hagopian
