import HPC.Plane.PseudoArc51
import HPC.Plane.Monotone51Comb

/-!
# Bing, *Concerning hereditarily indecomposable continua*, §4: monotone decompositions

Skeleton for batch 89 (save as `HPC/Plane/Monotone51.lean`; add `import HPC.Plane.Monotone51` to
the root `HPC.lean`). The skeleton's proofs were all `sorry` work items. Shapes may be adjusted
with the change recorded; `theorem3_HIC` and `theorem4_HIC` keep their conclusions.

A monotone decomposition of `M` is given by a continuous surjection with connected fibres
(COMMISSION-batch89.md §3.1). `IsSnakeLike`, `IsHereditarilyIndecomposable`, `IsPseudoArc` are
from `Snake51.lean`, `EndPoints51.lean`, `PseudoArc51.lean`.

**Batch 89 delivery.** All five statements are proved as stated (no shape changes). Theorem 3 uses
the combinatorial lemma `Mono.exists_chain_of_intervals` (`HPC/Plane/Monotone51Comb.lean`): Bing's
windows `D(n_{3k+1}, n_{3k+5})`, with his `n_i` replaced by strictly increasing block boundaries
(see that file and `REPORT-batch89.md`). The chain obtained in the space `M'` is lifted to `Y` by
`PA51.liftChain` (batch 88). The monotone image of a hereditarily indecomposable continuum is
hereditarily indecomposable because preimages of connected subsets of `M'` are connected
(`isConnected_inter_preimage`, a direct argument with the closed sets `f '' (M ∩ u)`).
-/

namespace HPC.Plane

open Set

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `f` is a **monotone map** of `M` onto `M'`: continuous on `M`, with image `M'`, and with every
fibre `M ∩ f ⁻¹' {y}` (for `y ∈ M'`) connected. Bing's "upper semi-continuous collection of
continua filling `M`" is the collection of fibres. -/
def IsMonotoneMap (f : X → Y) (M : Set X) (M' : Set Y) : Prop :=
  ContinuousOn f M ∧ f '' M = M' ∧ ∀ y ∈ M', IsConnected (M ∩ f ⁻¹' {y})

namespace Mono

omit [MetricSpace X] [MetricSpace Y] in
/-- The full preimage (inside `M`) of a subset of `M'` maps onto it. -/
theorem image_inter_preimage {f : X → Y} {M : Set X} {M' : Set Y} (hfM : f '' M = M')
    {S : Set Y} (hS : S ⊆ M') : f '' (M ∩ f ⁻¹' S) = S := by
  ext y
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (hfM ▸ hS hy : y ∈ f '' M)
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

/-- **The preimage of a connected set under a monotone map of a compact set is connected.**
For closed `u`, `v` covering the preimage `K` and both meeting it, the compact (hence closed)
images `f '' (M ∩ u)` and `f '' (M ∩ v)` cover `K'` and both meet it, so they share a point `y` of
`K'`; the connected fibre over `y` lies in `K ⊆ u ∪ v` and meets both, hence meets `u ∩ v`. -/
theorem isConnected_inter_preimage {f : X → Y} {M : Set X} {M' : Set Y} (hMc : IsCompact M)
    (hf : IsMonotoneMap f M M') {K' : Set Y} (hK' : IsConnected K') (hKM : K' ⊆ M') :
    IsConnected (M ∩ f ⁻¹' K') := by
  obtain ⟨hfc, hfM, hfib⟩ := hf
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := hK'.nonempty
    obtain ⟨x, hx, rfl⟩ := (hfM ▸ hKM hy : y ∈ f '' M)
    exact ⟨x, hx, hy⟩
  rw [isPreconnected_closed_iff]
  intro u v hu hv hcov hKu hKv
  have hA : IsClosed (f '' (M ∩ u)) :=
    ((hMc.inter_right hu).image_of_continuousOn (hfc.mono inter_subset_left)).isClosed
  have hB : IsClosed (f '' (M ∩ v)) :=
    ((hMc.inter_right hv).image_of_continuousOn (hfc.mono inter_subset_left)).isClosed
  have hcov' : K' ⊆ f '' (M ∩ u) ∪ f '' (M ∩ v) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hfM ▸ hKM hy : y ∈ f '' M)
    rcases hcov ⟨hx, hy⟩ with h | h
    · exact Or.inl ⟨x, ⟨hx, h⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hx, h⟩, rfl⟩
  have hK'u : (K' ∩ f '' (M ∩ u)).Nonempty := by
    obtain ⟨x, ⟨hxM, hxK⟩, hxu⟩ := hKu
    exact ⟨f x, hxK, x, ⟨hxM, hxu⟩, rfl⟩
  have hK'v : (K' ∩ f '' (M ∩ v)).Nonempty := by
    obtain ⟨x, ⟨hxM, hxK⟩, hxv⟩ := hKv
    exact ⟨f x, hxK, x, ⟨hxM, hxv⟩, rfl⟩
  obtain ⟨y, hyK, ⟨x₁, ⟨hx₁M, hx₁u⟩, hx₁⟩, ⟨x₂, ⟨hx₂M, hx₂v⟩, hx₂⟩⟩ :=
    isPreconnected_closed_iff.mp hK'.isPreconnected _ _ hA hB hcov' hK'u hK'v
  have hF := (hfib y (hKM hyK)).isPreconnected
  have hFK : M ∩ f ⁻¹' {y} ⊆ M ∩ f ⁻¹' K' := fun x hx =>
    ⟨hx.1, by rw [mem_preimage, show f x = y from hx.2]; exact hyK⟩
  obtain ⟨x, hxF, hxu, hxv⟩ := isPreconnected_closed_iff.mp hF u v hu hv (hFK.trans hcov)
    ⟨x₁, ⟨hx₁M, hx₁⟩, hx₁u⟩ ⟨x₂, ⟨hx₂M, hx₂⟩, hx₂v⟩
  exact ⟨x, hFK hxF, hxu, hxv⟩

/-- The full preimage (inside `M`) of a continuum in `M'` is a continuum. -/
theorem isContinuum_inter_preimage {f : X → Y} {M : Set X} {M' : Set Y} (hMc : IsCompact M)
    (hf : IsMonotoneMap f M M') {K' : Set Y} (hK' : Fold.Q78.IsContinuum K') (hKM : K' ⊆ M') :
    Fold.Q78.IsContinuum (M ∩ f ⁻¹' K') :=
  ⟨hMc.of_isClosed_subset (hf.1.preimage_isClosed_of_isClosed hMc.isClosed hK'.1.isClosed)
      inter_subset_left,
    isConnected_inter_preimage hMc hf hK'.2 hKM⟩

end Mono

/-- **Bing 1951 (Pacific J. Math.), Theorem 3.** The monotone image of a chainable (compact)
continuum is chainable. (Bing's chain of `D(n_{3k+1}, n_{3k+5})`'s; COMMISSION-batch89.md §3.4 asks
whether consecutive links meet as he has them.) -/
theorem theorem3_HIC {f : X → Y} {M : Set X} {M' : Set Y} (hM : IsSnakeLike M)
    (hf : IsMonotoneMap f M M') : IsSnakeLike M' := by
  classical
  obtain ⟨hfc, hfM, hfib⟩ := hf
  have hMc : IsCompact M := hM.1.1
  have hM'c : IsCompact M' := hfM ▸ hMc.image_of_continuousOn hfc
  have hM'conn : IsConnected M' := hfM ▸ hM.1.2.image f hfc
  refine ⟨⟨hM'c, hM'conn⟩, fun ε hε => ?_⟩
  haveI : Nonempty M' := hM'conn.nonempty.to_subtype
  set η := ε / 9 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hunif⟩ : ∃ δ > 0, ∀ x ∈ M, ∀ x' ∈ M, dist x x' < δ → dist (f x) (f x') < η :=
    Metric.uniformContinuousOn_iff.mp (hMc.uniformContinuousOn_of_continuous hfc) η hη
  obtain ⟨n, C, hCε, hMC, hCmeet⟩ :=
    exists_cover_meeting hM.1.2.isPreconnected hM.1.2.nonempty hM.2 (half_pos hδ)
  -- fibres, the links they meet, and Bing's sets `D(p, q)`
  set F : M' → Set X := fun y => M ∩ f ⁻¹' {(y : Y)} with hF_def
  set R : M' → ℕ → Prop := fun y i => ∃ h : i < n, (C.link ⟨i, h⟩ ∩ F y).Nonempty with hR_def
  set U : ℕ → ℕ → Set X := fun p q => ⋃ (i : Fin n) (_ : p ≤ i.val ∧ i.val ≤ q), C.link i
    with hU_def
  set G : ℕ → ℕ → Set M' := fun p q => {y | F y ⊆ U p q} with hG_def
  have hFne : ∀ y : M', (F y).Nonempty := fun y => (hfib y y.2).nonempty
  have hFC : ∀ y : M', F y ⊆ C.union := fun y => inter_subset_left.trans hMC
  have hlink : ∀ x ∈ C.union, ∃ i : Fin n, x ∈ C.link i := fun x hx => mem_iUnion.mp hx
  have hUo : ∀ p q, IsOpen (U p q) := fun p q => isOpen_biUnion fun i _ => C.isOpen i
  obtain ⟨m, D, hDcov, hDdiam⟩ := Mono.exists_chain_of_intervals (n := n) (η := η) R G
    (fun y i h => h.1)
    (fun y => by
      obtain ⟨x, hx⟩ := hFne y
      obtain ⟨i, hi⟩ := hlink x (hFC y hx)
      exact ⟨i.val, i.isLt, x, hi, hx⟩)
    (fun y i j k ⟨hi, hxi⟩ ⟨hk, hxk⟩ hij hjk => by
      refine ⟨by omega, ?_⟩
      exact Chain.meet_ordConnected C (hfib y y.2).isPreconnected (hFC y)
        (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) (Fin.mk_le_mk.mpr hij) (Fin.mk_le_mk.mpr hjk) hxi hxk)
    (fun i hi => by
      obtain ⟨x, hxC, hxM⟩ := hCmeet ⟨i, hi⟩
      have hy : f x ∈ M' := hfM ▸ mem_image_of_mem f hxM
      exact ⟨⟨f x, hy⟩, hi, x, hxC, hxM, rfl⟩)
    (fun y y' i i' ⟨hi, x, hxC, hxM, hxy⟩ ⟨hi', x', hxC', hxM', hxy'⟩ h1 h2 => by
      obtain ⟨w, hw, hw'⟩ := (C.adjacent_iff ⟨i, hi⟩ ⟨i', hi'⟩).mpr ⟨h1, h2⟩
      have d1 : dist x w ≤ Metric.diam (C.link ⟨i, hi⟩) :=
        Metric.dist_le_diam_of_mem (hCε _).1 hxC hw
      have d2 : dist w x' ≤ Metric.diam (C.link ⟨i', hi'⟩) :=
        Metric.dist_le_diam_of_mem (hCε _).1 hw' hxC'
      have e1 := (hCε ⟨i, hi⟩).2
      have e2 := (hCε ⟨i', hi'⟩).2
      have hxx' : dist x x' < δ := by
        linarith [dist_triangle x w x']
      have := hunif x hxM x' hxM' hxx'
      rw [Subtype.dist_eq]
      rw [mem_preimage, mem_singleton_iff] at hxy hxy'
      rwa [← hxy, ← hxy'])
    (fun p q => by
      have hK : IsCompact (M \ U p q) := hMc.diff (hUo p q)
      have hKc : IsClosed (f '' (M \ U p q)) :=
        (hK.image_of_continuousOn (hfc.mono diff_subset)).isClosed
      have : G p q = (Subtype.val ⁻¹' (f '' (M \ U p q)))ᶜ := by
        ext y
        simp only [hG_def, hF_def, mem_setOf_eq, mem_compl_iff, mem_preimage, mem_image,
          mem_diff, not_exists, not_and, subset_def, mem_inter_iff, mem_singleton_iff]
        constructor
        · intro h x ⟨hxM, hxU⟩ hxy
          exact hxU (h x ⟨hxM, hxy⟩)
        · intro h x ⟨hxM, hxy⟩
          by_contra hxU
          exact h x ⟨hxM, hxU⟩ hxy
      rw [this]
      exact (hKc.preimage continuous_subtype_val).isOpen_compl)
    (fun y p q h x hx => by
      obtain ⟨i, hi⟩ := hlink x (hFC y hx)
      exact mem_biUnion (x := i) (h i.val ⟨i.isLt, x, hi, hx⟩) hi)
    (fun y p q hy => by
      obtain ⟨x, hx⟩ := hFne y
      obtain ⟨i, hpq, hxi⟩ := mem_iUnion₂.mp (hy hx)
      exact ⟨i.val, ⟨i.isLt, x, hxi, hx⟩, hpq⟩)
    (fun y p q p' q' hy hy' hqp => by
      obtain ⟨x, hx⟩ := hFne y
      obtain ⟨i, hpq, hxi⟩ := mem_iUnion₂.mp (hy hx)
      obtain ⟨i', hpq', hxi'⟩ := mem_iUnion₂.mp (hy' hx)
      have := (C.adjacent_iff i i').mp ⟨x, hxi, hxi'⟩
      omega)
  -- lift the chain of the space `M'` to `Y`
  have hM'cl : IsClosed M' := hM'c.isClosed
  refine ⟨m, PA51.liftChain hM'cl D η hη, fun j => ?_, fun y hy => ?_⟩
  · refine ⟨PA51.isBounded_ext M' η (hDdiam j).1, ?_⟩
    calc Metric.diam ((PA51.liftChain hM'cl D η hη).link j)
        ≤ Metric.diam (D.link j) + 2 * η := PA51.diam_ext_le M' hη.le (hDdiam j).1
      _ ≤ 6 * η + 2 * η := by linarith [(hDdiam j).2]
      _ < ε := by rw [hη_def]; linarith
  · obtain ⟨j, hj⟩ := mem_iUnion.mp (hDcov (mem_univ (⟨y, hy⟩ : M')))
    exact mem_iUnion.mpr ⟨j, (PA51.mem_ext_iff hM'cl (D.isOpen j) hη ⟨y, hy⟩).mpr hj⟩

/-- The monotone image of a hereditarily indecomposable continuum is hereditarily
indecomposable. -/
theorem isHereditarilyIndecomposable_image {f : X → Y} {M : Set X} {M' : Set Y}
    (hM : Fold.Q78.IsContinuum M) (hHI : IsHereditarilyIndecomposable M)
    (hf : IsMonotoneMap f M M') : IsHereditarilyIndecomposable M' := by
  intro K' hK'M hK'
  refine ⟨hK', fun A' B' hA' hB' hA'K hB'K hAB => ?_⟩
  have hK := Mono.isContinuum_inter_preimage hM.1 hf hK' hK'M
  have hA := Mono.isContinuum_inter_preimage hM.1 hf hA' (hA'K.trans hK'M)
  have hB := Mono.isContinuum_inter_preimage hM.1 hf hB' (hB'K.trans hK'M)
  have hunion : M ∩ f ⁻¹' A' ∪ M ∩ f ⁻¹' B' = M ∩ f ⁻¹' K' := by
    rw [← inter_union_distrib_left, ← preimage_union, hAB]
  rcases (hHI _ inter_subset_left hK).2 _ _ hA hB
      (inter_subset_inter_right _ (preimage_mono hA'K))
      (inter_subset_inter_right _ (preimage_mono hB'K)) hunion with h | h
  · left
    have := congrArg (f '' ·) h
    simpa only [Mono.image_inter_preimage hf.2.1 (hA'K.trans hK'M),
      Mono.image_inter_preimage hf.2.1 hK'M] using this
  · right
    have := congrArg (f '' ·) h
    simpa only [Mono.image_inter_preimage hf.2.1 (hB'K.trans hK'M),
      Mono.image_inter_preimage hf.2.1 hK'M] using this

/-- The monotone image of a chainable continuum is a (compact) continuum and chainable; recorded
separately from `theorem3_HIC` only to name the continuum part. -/
theorem isContinuum_image {f : X → Y} {M : Set X} {M' : Set Y} (hM : Fold.Q78.IsContinuum M)
    (hf : IsMonotoneMap f M M') : Fold.Q78.IsContinuum M' :=
  hf.2.1 ▸ ⟨hM.1.image_of_continuousOn hf.1, hM.2.image f hf.1⟩

/-- **Bing 1951 (Pacific J. Math.), Theorem 4.** If `M` is a pseudo-arc and every fibre of the
monotone map `f` is a proper subcontinuum of `M`, the image `M'` is a pseudo-arc, hence
homeomorphic to `M`. -/
theorem theorem4_HIC {f : X → Y} {M : Set X} {M' : Set Y} (hM : IsPseudoArc M)
    (hf : IsMonotoneMap f M M') (hproper : ∀ y ∈ M', M ∩ f ⁻¹' {y} ≠ M) :
    IsPseudoArc M' ∧ Nonempty (M ≃ₜ M') := by
  obtain ⟨hs, hh, hnd⟩ := hM
  have hs' : IsSnakeLike M' := theorem3_HIC hs hf
  have hh' : IsHereditarilyIndecomposable M' := isHereditarilyIndecomposable_image hs.1 hh hf
  have hnd' : M'.Nontrivial := by
    obtain ⟨y, hy⟩ := hs'.1.2.nonempty
    by_contra hcon
    rw [not_nontrivial_iff] at hcon
    apply hproper y hy
    ext x
    refine ⟨fun h => h.1, fun hx => ⟨hx, ?_⟩⟩
    exact hcon (hf.2.1 ▸ mem_image_of_mem f hx) hy
  have hP : IsPseudoArc M' := ⟨hs', hh', hnd'⟩
  exact ⟨hP, theorem1_HIC' ⟨hs, hh, hnd⟩ hP⟩

end HPC.Plane
