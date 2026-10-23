import HPC.Hagopian.H76Defs

/-!
# Batch 160, item C: upper semicontinuity of the decomposition, in metric form

`layer_nbhd_small_aux`: for a minimal admissible map `k` of `E` and a layer `k⁻¹(s)`, the layers
`k⁻¹(t)` with `t` near `s` lie in the `ε`-neighbourhood of `k⁻¹(s)`. Proof: the points of `E`
outside the (open) `ε`-neighbourhood form a compact set; its image under `k` is compact and misses
`s`, so it misses an interval around `s`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

/-- **Layers near a layer are near it** (item C). -/
theorem layer_nbhd_small_aux {M : Set Pt} {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) (s : unitInterval) :
    ∃ δ > 0, ∀ t : unitInterval, dist t s < δ →
      toPt (layer k t) ⊆ Metric.thickening ε (toPt (layer k s)) := by
  obtain ⟨⟨a, b, hab⟩, hk, -⟩ := hE
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hab.1.1
  set T := Metric.thickening ε (toPt (layer k s))
  set K : Set E := {x | ((x : M) : Pt) ∉ T}
  have hKc : IsClosed K :=
    (isOpen_thickening.preimage (continuous_subtype_val.comp continuous_subtype_val)).isClosed_compl
  have hkK : IsCompact (k '' K) := hKc.isCompact.image hk.1
  have hs : s ∉ k '' K := by
    rintro ⟨x, hxK, hxs⟩
    apply hxK
    apply Metric.self_subset_thickening hε
    exact ⟨(x : M), ⟨x, mem_singleton_iff.2 hxs, rfl⟩, rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hkK.isClosed.isOpen_compl s hs
  refine ⟨δ, hδ, fun t ht => ?_⟩
  rintro _ ⟨_, ⟨x, hxt, rfl⟩, rfl⟩
  by_contra hxT
  exact hball (mem_ball.2 ht) ⟨x, hxT, mem_singleton_iff.1 hxt⟩

end HPC.Hagopian
