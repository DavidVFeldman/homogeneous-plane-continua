import HPC.HO16.FoldDefs
import HPC.HO16.Subdiv

/-!
# Batch 194, §3: a library for PL graphs

The nine skeleton lemmas of commission 194, §3, derived from the common subdivision
(`Subdiv.exists_common_subdivision`) through the refinement lemma §3.0, together with the
reusable facts the later batches will need:

* `isPLGraph_biUnion_filter`: a subfamily of a decomposition is a PL graph;
* `closure_diff_eq_of_refined`: in a decomposition refining `A`, `cl (G \ A)` is the union of
  the edges not contained in `A`;
* `relFrontier_subset_vertices`: the frontier of a subgraph consists of vertices;
* `connectedComponentIn_eq_biUnion`: a component is the union of the edges it contains;
* `IsPLGraph.mem_closure_diff_finite`: a PL graph has no isolated points, even after removing a
  finite set.
-/

namespace HPC.HO16

open Set Topology Metric Filter

section Library

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pairwise condition of a decomposition (as in `IsPLGraph`). -/
def PairwiseEndpoints (S : Finset (E × E)) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
    segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2 ⊆ ({s.1, s.2} : Set E) ∩ {s'.1, s'.2}

/-- A subfamily of a decomposition is a PL graph. -/
theorem isPLGraph_biUnion_filter {S : Finset (E × E)} (hne : ∀ s ∈ S, s.1 ≠ s.2)
    (hdis : PairwiseEndpoints S) (p : E × E → Prop) [DecidablePred p] :
    IsPLGraph (⋃ s ∈ S.filter p, segment ℝ s.1 s.2) :=
  ⟨S.filter p, fun s hs => hne s (Finset.mem_filter.1 hs).1, rfl,
    fun s hs s' hs' => hdis s (Finset.mem_filter.1 hs).1 s' (Finset.mem_filter.1 hs').1⟩

theorem isClosed_biUnion_segment (S : Finset (E × E)) :
    IsClosed (⋃ s ∈ S, segment ℝ s.1 s.2) :=
  isClosed_biUnion_finset fun s _ => Subdiv.isClosed_segment' s.1 s.2

/-- **§3.1**: a finite union of nondegenerate segments is a PL graph (common subdivision). -/
theorem isPLGraph_biUnion {T : Finset (E × E)} (hT : ∀ t ∈ T, t.1 ≠ t.2) :
    IsPLGraph (⋃ t ∈ T, segment ℝ t.1 t.2) := by
  obtain ⟨S, hSne, hST, hSdis, hcov, -⟩ := Subdiv.exists_common_subdivision T hT ∅
  refine ⟨S, hSne, Subset.antisymm ?_ ?_, hSdis⟩
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hx
    obtain ⟨s, hs, hxs, -⟩ := hcov t ht x hxt
    exact mem_biUnion hs hxs
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
    obtain ⟨t, ht, hst⟩ := hST s hs
    exact mem_biUnion ht (hst hxs)

/-- **§3.0, refinement**: a decomposition of `G` in which each of finitely many PL subgraphs
`A i` is the union of the edges it contains, every other edge meets `A i` only at its endpoints,
and every point of a finite `P ⊆ G` is a vertex. -/
theorem IsPLGraph.exists_refinement {G : Set E} (hG : IsPLGraph G) {k : ℕ} (A : Fin k → Set E)
    (hA : ∀ i, IsPLGraph (A i)) (hAG : ∀ i, A i ⊆ G) (P : Finset E) (hP : ∀ p ∈ P, p ∈ G) :
    ∃ S : Finset (E × E), (∀ s ∈ S, s.1 ≠ s.2) ∧ G = ⋃ s ∈ S, segment ℝ s.1 s.2 ∧
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
        segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2 ⊆ ({s.1, s.2} : Set E) ∩ {s'.1, s'.2}) ∧
      (∀ i, ∀ x ∈ A i, ∃ s ∈ S, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ A i) ∧
      (∀ i, ∀ s ∈ S, ¬ segment ℝ s.1 s.2 ⊆ A i → segment ℝ s.1 s.2 ∩ A i ⊆ {s.1, s.2}) ∧
      (∀ p ∈ P, ∃ s ∈ S, p = s.1 ∨ p = s.2) := by
  classical
  obtain ⟨SG, hSGne, rfl, -⟩ := hG
  choose SA hSAne hSAeq _ using hA
  set T := SG ∪ Finset.univ.biUnion SA with hTdef
  have hT : ∀ t ∈ T, t.1 ≠ t.2 := by
    intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · exact hSGne t h
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
      exact hSAne i t hi
  obtain ⟨S, hSne, hST, hSdis, hcov, hvert⟩ := Subdiv.exists_common_subdivision T hT P
  have hTsub : ∀ t ∈ T, segment ℝ t.1 t.2 ⊆ ⋃ s ∈ SG, segment ℝ s.1 s.2 := by
    intro t ht x hx
    rcases Finset.mem_union.1 ht with h | h
    · exact mem_biUnion h hx
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
      apply hAG i
      rw [hSAeq i]
      exact mem_biUnion hi hx
  have hUnion : (⋃ s ∈ SG, segment ℝ s.1 s.2) = ⋃ s ∈ S, segment ℝ s.1 s.2 := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hx
      obtain ⟨s, hs, hxs, -⟩ := hcov t (Finset.mem_union_left _ ht) x hxt
      exact mem_biUnion hs hxs
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
      obtain ⟨t, ht, hst⟩ := hST s hs
      exact hTsub t ht (hst hxs)
  have hcovA : ∀ i, ∀ x ∈ A i, ∃ s ∈ S, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ A i := by
    intro i x hx
    rw [hSAeq i] at hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hx
    have htT : t ∈ T := Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩)
    obtain ⟨s, hs, hxs, hst⟩ := hcov t htT x hxt
    refine ⟨s, hs, hxs, fun y hy => ?_⟩
    rw [hSAeq i]
    exact mem_biUnion ht (hst hy)
  refine ⟨S, hSne, hUnion, hSdis, hcovA, ?_, ?_⟩
  · intro i s hs hsub y ⟨hys, hyA⟩
    obtain ⟨s', hs', hys', hs'A⟩ := hcovA i y hyA
    have hne : s ≠ s' := by rintro rfl; exact hsub hs'A
    exact (hSdis s hs s' hs' hne ⟨hys, hys'⟩).1
  · intro p hp
    obtain ⟨t, ht, hpt⟩ := mem_iUnion₂.1 (hP p hp)
    exact hvert p hp t (Finset.mem_union_left _ ht) hpt

/-- Refinement for a single subgraph. -/
theorem IsPLGraph.exists_refinement_one {G A : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hAG : A ⊆ G) :
    ∃ S : Finset (E × E), (∀ s ∈ S, s.1 ≠ s.2) ∧ G = ⋃ s ∈ S, segment ℝ s.1 s.2 ∧
      PairwiseEndpoints S ∧
      (∀ x ∈ A, ∃ s ∈ S, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ A) ∧
      (∀ s ∈ S, ¬ segment ℝ s.1 s.2 ⊆ A → segment ℝ s.1 s.2 ∩ A ⊆ {s.1, s.2}) := by
  obtain ⟨S, h1, h2, h3, h4, h5, -⟩ :=
    hG.exists_refinement (k := 1) (fun _ => A) (fun _ => hA) (fun _ => hAG) ∅ (by simp)
  exact ⟨S, h1, h2, h3, h4 0, h5 0⟩

/-- A nondegenerate edge of `G` meeting `A` at most in its endpoints lies in `closure (G \ A)`:
its inner points lie in `G \ A`. -/
theorem segment_subset_closure_diff {G A : Set E} {a b : E} (hab : a ≠ b)
    (hsG : segment ℝ a b ⊆ G) (hsA : segment ℝ a b ∩ A ⊆ {a, b}) :
    segment ℝ a b ⊆ closure (G \ A) := by
  refine (segment_subset_closure_openSegment).trans (closure_mono ?_)
  intro y hy
  refine ⟨hsG (openSegment_subset_segment ℝ a b hy), fun hyA => ?_⟩
  rcases hsA ⟨openSegment_subset_segment ℝ a b hy, hyA⟩ with h | h
  · subst h
    exact hab (left_mem_openSegment_iff.1 hy)
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact hab (right_mem_openSegment_iff.1 hy)

/-- In a decomposition refining `A`, `cl (G \ A)` is the union of the edges not in `A`. -/
theorem closure_diff_eq_of_refined {G A : Set E} {S : Finset (E × E)}
    (hne : ∀ s ∈ S, s.1 ≠ s.2) (hG : G = ⋃ s ∈ S, segment ℝ s.1 s.2)
    (hout : ∀ s ∈ S, ¬ segment ℝ s.1 s.2 ⊆ A → segment ℝ s.1 s.2 ∩ A ⊆ {s.1, s.2})
    [DecidablePred fun s : E × E => ¬ segment ℝ s.1 s.2 ⊆ A] :
    closure (G \ A) = ⋃ s ∈ S.filter (fun s => ¬ segment ℝ s.1 s.2 ⊆ A), segment ℝ s.1 s.2 := by
  apply Subset.antisymm
  · refine closure_minimal ?_ (isClosed_biUnion_segment _)
    rintro x ⟨hxG, hxA⟩
    rw [hG] at hxG
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hxG
    exact mem_biUnion (Finset.mem_filter.2 ⟨hs, fun h => hxA (h hxs)⟩) hxs
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
    obtain ⟨hs, hsA⟩ := Finset.mem_filter.1 hs
    refine segment_subset_closure_diff (hne s hs) ?_ (hout s hs hsA) hxs
    rw [hG]
    exact subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2) hs

/-- **§3.2** -/
theorem IsPLGraph.union {A B : Set E} (hA : IsPLGraph A) (hB : IsPLGraph B) :
    IsPLGraph (A ∪ B) := by
  classical
  obtain ⟨SA, hSA, rfl, -⟩ := hA
  obtain ⟨SB, hSB, rfl, -⟩ := hB
  have := isPLGraph_biUnion (T := SA ∪ SB) (by
    intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · exact hSA t h
    · exact hSB t h)
  rwa [Finset.set_biUnion_union] at this

/-- **§3.3** -/
theorem IsPLGraph.closure_diff {G A : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hAG : A ⊆ G) : IsPLGraph (closure (G \ A)) := by
  classical
  obtain ⟨S, hne, hGS, hdis, -, hout⟩ := hG.exists_refinement_one hA hAG
  rw [closure_diff_eq_of_refined hne hGS hout]
  exact isPLGraph_biUnion_filter hne hdis _

/-- The frontier of a refined subgraph consists of vertices. -/
theorem relFrontier_subset_vertices {G A : Set E} {S : Finset (E × E)} (hAc : IsClosed A)
    (hne : ∀ s ∈ S, s.1 ≠ s.2) (hG : G = ⋃ s ∈ S, segment ℝ s.1 s.2)
    (hout : ∀ s ∈ S, ¬ segment ℝ s.1 s.2 ⊆ A → segment ℝ s.1 s.2 ∩ A ⊆ {s.1, s.2}) :
    relFrontier G A ⊆ ⋃ s ∈ S, ({s.1, s.2} : Set E) := by
  classical
  rintro x ⟨hxA, hxc⟩
  rw [hAc.closure_eq] at hxA
  rw [closure_diff_eq_of_refined hne hG hout] at hxc
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hxc
  obtain ⟨hs, hsA⟩ := Finset.mem_filter.1 hs
  exact mem_biUnion hs (hout s hs hsA ⟨hxs, hxA⟩)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem finite_vertices (S : Finset (E × E)) : (⋃ s ∈ S, ({s.1, s.2} : Set E)).Finite :=
  S.finite_toSet.biUnion fun _ _ => (Set.finite_singleton _).insert _

/-- **§3.4**: a PL subgraph has finite frontier (H–O p. 184: "a regular set always has finite
boundary"). -/
theorem IsPLGraph.relFrontier_finite {G A : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hAG : A ⊆ G) : (relFrontier G A).Finite := by
  obtain ⟨S, hne, hGS, -, -, hout⟩ := hG.exists_refinement_one hA hAG
  exact (finite_vertices S).subset
    (relFrontier_subset_vertices hA.isCompact.isClosed hne hGS hout)

/-- A component of `⋃ S` is the union of the edges it contains. -/
theorem connectedComponentIn_eq_biUnion {G : Set E} {S : Finset (E × E)}
    (hG : G = ⋃ s ∈ S, segment ℝ s.1 s.2) (p : E)
    [DecidablePred fun s : E × E => segment ℝ s.1 s.2 ⊆ connectedComponentIn G p] :
    connectedComponentIn G p =
      ⋃ s ∈ S.filter (fun s => segment ℝ s.1 s.2 ⊆ connectedComponentIn G p),
        segment ℝ s.1 s.2 := by
  apply Subset.antisymm
  · intro x hx
    have hxG := connectedComponentIn_subset G p hx
    rw [hG] at hxG
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hxG
    refine mem_biUnion (Finset.mem_filter.2 ⟨hs, ?_⟩) hxs
    rw [connectedComponentIn_eq hx]
    refine (convex_segment _ _).isPreconnected.subset_connectedComponentIn hxs ?_
    rw [hG]
    exact subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2) hs
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
    exact (Finset.mem_filter.1 hs).2 hxs

/-- **§3.5**: components of a PL graph are PL graphs, ... -/
theorem IsPLGraph.connectedComponentIn {G : Set E} (hG : IsPLGraph G) (p : E) :
    IsPLGraph (connectedComponentIn G p) := by
  classical
  obtain ⟨S, hne, hGS, hdis⟩ := hG
  rw [connectedComponentIn_eq_biUnion hGS p]
  exact isPLGraph_biUnion_filter hne hdis _

/-- **§3.5**: ... there are finitely many of them, ...

*Shape change (batch 194):* the skeleton writes `connectedComponentIn`; inside `IsPLGraph.…` that
name resolves to the theorem `IsPLGraph.connectedComponentIn` and the statement does not elaborate,
so Mathlib's function is written `_root_.connectedComponentIn`. Nothing else changes. -/
theorem IsPLGraph.finite_components {G : Set E} (hG : IsPLGraph G) :
    {C : Set E | ∃ p ∈ G, C = _root_.connectedComponentIn G p}.Finite := by
  classical
  obtain ⟨S, -, hGS, -⟩ := hG
  refine ((S.powerset.finite_toSet).image (fun S' => ⋃ s ∈ S', segment ℝ s.1 s.2)).subset ?_
  rintro C ⟨p, -, rfl⟩
  refine ⟨S.filter (fun s => segment ℝ s.1 s.2 ⊆ _root_.connectedComponentIn G p), ?_, ?_⟩
  · exact Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))
  · exact (connectedComponentIn_eq_biUnion hGS p).symm

/-- **§3.5**: ... and a PL subgraph meets each in a PL graph.

*Shape change (batch 194):* the skeleton writes `connectedComponentIn`; inside `IsPLGraph.…` that
name resolves to the theorem `IsPLGraph.connectedComponentIn` and the statement does not elaborate,
so Mathlib's function is written `_root_.connectedComponentIn`. Nothing else changes. -/
theorem IsPLGraph.inter_connectedComponentIn {G A : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hAG : A ⊆ G) (p : E) : IsPLGraph (A ∩ _root_.connectedComponentIn G p) := by
  classical
  obtain ⟨S, hne, hGS, hdis, hin, -⟩ := hG.exists_refinement_one hA hAG
  have : A ∩ _root_.connectedComponentIn G p = ⋃ s ∈ S.filter (fun s => segment ℝ s.1 s.2 ⊆ A ∧
      segment ℝ s.1 s.2 ⊆ _root_.connectedComponentIn G p), segment ℝ s.1 s.2 := by
    apply Subset.antisymm
    · rintro x ⟨hxA, hxC⟩
      obtain ⟨s, hs, hxs, hsA⟩ := hin x hxA
      refine mem_biUnion (Finset.mem_filter.2 ⟨hs, hsA, ?_⟩) hxs
      rw [connectedComponentIn_eq hxC]
      refine (convex_segment _ _).isPreconnected.subset_connectedComponentIn hxs ?_
      rw [hGS]
      exact subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2) hs
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hs
      exact ⟨h1 hxs, h2 hxs⟩
  rw [this]
  exact isPLGraph_biUnion_filter hne hdis _

/-- **§3.6**: the projection of a PL graph in `E × ℝ` on which `Prod.fst` is injective. -/
theorem IsPLGraph.image_fst {F : Set (E × ℝ)} (hF : IsPLGraph F) (hinj : InjOn Prod.fst F) :
    IsPLGraph (Prod.fst '' F) := by
  classical
  obtain ⟨S, hne, rfl, hdis⟩ := hF
  have hseg : ∀ s : (E × ℝ) × (E × ℝ),
      Prod.fst '' segment ℝ s.1 s.2 = segment ℝ s.1.1 s.2.1 := fun s =>
    image_segment ℝ (LinearMap.fst ℝ E ℝ).toAffineMap s.1 s.2
  have hmem : ∀ s ∈ S, ∀ x ∈ segment ℝ s.1 s.2, x ∈ ⋃ s ∈ S, segment ℝ s.1 s.2 :=
    fun s hs x hx => mem_biUnion hs hx
  refine ⟨S.image (fun s => (s.1.1, s.2.1)), ?_, ?_, ?_⟩
  · simp only [Finset.mem_image]
    rintro _ ⟨s, hs, rfl⟩ h
    exact hne s hs (hinj (hmem s hs _ (left_mem_segment ℝ _ _))
      (hmem s hs _ (right_mem_segment ℝ _ _)) h)
  · rw [image_iUnion₂]
    simp only [hseg]
    ext x
    simp only [mem_iUnion, Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hx⟩; exact ⟨_, ⟨s, hs, rfl⟩, hx⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩; exact ⟨s, hs, hx⟩
  · simp only [Finset.mem_image]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hne' y ⟨hy, hy'⟩
    rw [← hseg] at hy
    rw [← hseg] at hy'
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨x', hx', hxx⟩ := hy'
    have hxe : x' = x := hinj (hmem s' hs' x' hx') (hmem s hs x hx) hxx
    subst hxe
    have hss : s ≠ s' := by rintro rfl; exact hne' rfl
    obtain ⟨h1, h2⟩ := hdis s hs s' hs' hss ⟨hx, hx'⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | h
      · rw [h]; exact Or.inl rfl
      · rw [Set.mem_singleton_iff.1 h]; exact Or.inr rfl
    · rcases h2 with h | h
      · rw [h]; exact Or.inl rfl
      · rw [Set.mem_singleton_iff.1 h]; exact Or.inr rfl

/-- A point of a PL graph is a limit of points of the graph outside any finite set. -/
theorem IsPLGraph.mem_closure_diff_finite {G : Set E} (hG : IsPLGraph G) {x : E} (hx : x ∈ G)
    {K : Set E} (hK : K.Finite) : x ∈ closure (G \ K) := by
  obtain ⟨S, hne, rfl, -⟩ := hG
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
  -- an endpoint `e ≠ x` of the edge; `x` is a limit of the open segment `(x, e)`
  obtain ⟨e, he, hex⟩ : ∃ e, e ∈ segment ℝ s.1 s.2 ∧ e ≠ x := by
    by_cases h : s.1 = x
    · exact ⟨s.2, right_mem_segment ℝ _ _, fun h' => hne s hs (h.trans h'.symm)⟩
    · exact ⟨s.1, left_mem_segment ℝ _ _, h⟩
  have hsub : openSegment ℝ x e ⊆ segment ℝ s.1 s.2 :=
    (openSegment_subset_segment ℝ _ _).trans ((convex_segment _ _).segment_subset hxs he)
  have hxT : x ∉ openSegment ℝ x e := fun h => hex (left_mem_openSegment_iff.1 h).symm
  have hcl : x ∈ closure (openSegment ℝ x e) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ x e)
  have hKc : IsClosed (K \ {x}) := (hK.diff).isClosed
  rw [mem_closure_iff_nhds] at hcl ⊢
  intro N hN
  have hN' : N ∩ (K \ {x})ᶜ ∈ 𝓝 x :=
    Filter.inter_mem hN (hKc.isOpen_compl.mem_nhds (fun h => h.2 rfl))
  obtain ⟨y, ⟨hyN, hyK⟩, hyo⟩ := hcl _ hN'
  have hyx : y ≠ x := by rintro rfl; exact hxT hyo
  exact ⟨y, hyN, mem_biUnion hs (hsub hyo), fun hyK' => hyK ⟨hyK', hyx⟩⟩

end Library

end HPC.HO16
