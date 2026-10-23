import HPC.HO16.StairDefs

/-!
# Batch 195, §2: library additions (components of complements, ordinary points, intersections)

Part of the batch-195 skeleton `HO16C.lean` (commission 195), split under `HPC/HO16/`.

* §2.1: `G \ (K ∪ P)` is a finite union of preconnected *pieces* `s \ (K ∪ P)` (`s` an edge of a
  refinement not in `K`; `IsPLGraph.exists_pieces`), whence its components are finitely many,
  relatively open (`IsPLGraph.connectedComponentIn_inter_mem_nhdsWithin`, via small fans), with
  PL closures and frontiers in `∂(K ∪ P)`.
* §2.2: ordinary points (`isOrdinaryPt_iff_order`, `IsPLGraph.finite_not_ordinary`).
* §2.3: intersections.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ### Components of a finite union of preconnected pieces -/

section Cover

variable {α ι : Type*} [TopologicalSpace α]

/-- In a finite union of preconnected pieces, each point of a component lies in a piece
contained in that component. -/
theorem mem_piece_of_mem_connectedComponentIn {X : Set α} {I : Finset ι} {Y : ι → Set α}
    (hY : ∀ i ∈ I, IsPreconnected (Y i)) (hX : X = ⋃ i ∈ I, Y i) {x z : α}
    (hz : z ∈ connectedComponentIn X x) :
    ∃ i ∈ I, z ∈ Y i ∧ Y i ⊆ connectedComponentIn X x := by
  have hzX := connectedComponentIn_subset X x hz
  rw [hX] at hzX
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hzX
  refine ⟨i, hi, hzi, ?_⟩
  rw [connectedComponentIn_eq hz]
  refine (hY i hi).subset_connectedComponentIn hzi ?_
  rw [hX]
  exact subset_biUnion_of_mem (u := Y) hi

/-- A component of a finite union of preconnected pieces is the union of the pieces it
contains. -/
theorem connectedComponentIn_eq_biUnion_pieces {X : Set α} {I : Finset ι} {Y : ι → Set α}
    (hY : ∀ i ∈ I, IsPreconnected (Y i)) (hX : X = ⋃ i ∈ I, Y i) (x : α)
    [DecidablePred fun i => Y i ⊆ connectedComponentIn X x] :
    connectedComponentIn X x =
      ⋃ i ∈ I.filter (fun i => Y i ⊆ connectedComponentIn X x), Y i := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨i, hi, hzi, hsub⟩ := mem_piece_of_mem_connectedComponentIn hY hX hz
    exact mem_biUnion (Finset.mem_filter.2 ⟨hi, hsub⟩) hzi
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz
    exact (Finset.mem_filter.1 hi).2 hzi

/-- A finite union of preconnected pieces has finitely many components. -/
theorem finite_components_of_pieces {X : Set α} {I : Finset ι} {Y : ι → Set α}
    (hY : ∀ i ∈ I, IsPreconnected (Y i)) (hX : X = ⋃ i ∈ I, Y i) :
    {C : Set α | ∃ x ∈ X, C = connectedComponentIn X x}.Finite := by
  classical
  refine ((I.powerset.finite_toSet).image (fun J => ⋃ i ∈ J, Y i)).subset ?_
  rintro C ⟨x, -, rfl⟩
  exact ⟨I.filter (fun i => Y i ⊆ connectedComponentIn X x),
    Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)),
    (connectedComponentIn_eq_biUnion_pieces hY hX x).symm⟩

end Cover

/-! ## §2. Library additions (commission §2) -/

section Library

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The empty set is a PL graph. -/
theorem isPLGraph_empty : IsPLGraph (∅ : Set E) :=
  ⟨∅, by simp, by simp, by simp⟩

/-- A finite union of PL graphs is a PL graph. -/
theorem IsPLGraph.biUnion_finite {ι : Type*} {s : Set ι} (hs : s.Finite) {f : ι → Set E}
    (h : ∀ i ∈ s, IsPLGraph (f i)) : IsPLGraph (⋃ i ∈ s, f i) := by
  classical
  have key : ∀ t : Finset ι, (∀ i ∈ t, IsPLGraph (f i)) → IsPLGraph (⋃ i ∈ t, f i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simpa using isPLGraph_empty
    | insert a t hat ih =>
      intro h'
      rw [Finset.set_biUnion_insert]
      exact (h' a (Finset.mem_insert_self _ _)).union
        (ih fun i hi => h' i (Finset.mem_insert_of_mem hi))
  have hs' : (⋃ i ∈ s, f i) = ⋃ i ∈ hs.toFinset, f i := by simp
  rw [hs']
  exact key _ fun i hi => h i (hs.mem_toFinset.1 hi)

/-- **§2.1, the pieces**: in a refinement in which `K` is a union of edges and `P` consists of
vertices, `G \ (K ∪ P)` is the union, over the edges `s` not in `K`, of `s \ (K ∪ P)`; each of
these contains the open edge, so it is preconnected with closure `s`. -/
theorem IsPLGraph.exists_pieces {G K P : Set E} (hG : IsPLGraph G) (hK : IsPLGraph K)
    (hKG : K ⊆ G) (hP : P.Finite) (hPG : P ⊆ G) :
    ∃ S : Finset (E × E), (∀ s ∈ S, s.1 ≠ s.2) ∧ PairwiseEndpoints S ∧
      (∀ s ∈ S, segment ℝ s.1 s.2 ⊆ G) ∧
      (∀ s ∈ S, IsPreconnected (segment ℝ s.1 s.2 \ (K ∪ P))) ∧
      (∀ s ∈ S, closure (segment ℝ s.1 s.2 \ (K ∪ P)) = segment ℝ s.1 s.2) ∧
      G \ (K ∪ P) = ⋃ s ∈ S, (segment ℝ s.1 s.2 \ (K ∪ P)) := by
  classical
  obtain ⟨S₀, hne, hGS, hdis, -, hout, hvert⟩ :=
    hG.exists_refinement (k := 1) (fun _ => K) (fun _ => hK) (fun _ => hKG) hP.toFinset
      (fun p hp => hPG (hP.mem_toFinset.1 hp))
  set S := S₀.filter (fun s => ¬ segment ℝ s.1 s.2 ⊆ K) with hSdef
  have hS0 : ∀ s ∈ S, s ∈ S₀ ∧ ¬ segment ℝ s.1 s.2 ⊆ K := fun s hs => Finset.mem_filter.1 hs
  have hsG : ∀ s ∈ S₀, segment ℝ s.1 s.2 ⊆ G := fun s hs => by
    rw [hGS]; exact subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2) hs
  have hopen : ∀ s ∈ S, openSegment ℝ s.1 s.2 ⊆ segment ℝ s.1 s.2 \ (K ∪ P) := by
    intro s hs y hy
    obtain ⟨hs0, hsK⟩ := hS0 s hs
    have hyseg := openSegment_subset_segment ℝ _ _ hy
    have hy1 : y ≠ s.1 := by
      rintro rfl; exact hne s hs0 (left_mem_openSegment_iff.1 hy)
    have hy2 : y ≠ s.2 := by
      rintro rfl; exact hne s hs0 (right_mem_openSegment_iff.1 hy)
    refine ⟨hyseg, ?_⟩
    rintro (hyK | hyP)
    · rcases hout 0 s hs0 hsK ⟨hyseg, hyK⟩ with h | h
      · exact hy1 h
      · exact hy2 h
    · obtain ⟨s', hs', hps'⟩ := hvert y (hP.mem_toFinset.2 hyP)
      by_cases hss : s = s'
      · subst hss
        rcases hps' with h | h
        · exact hy1 h
        · exact hy2 h
      · have hys' : y ∈ segment ℝ s'.1 s'.2 := by
          rcases hps' with h | h
          · rw [h]; exact left_mem_segment ℝ _ _
          · rw [h]; exact right_mem_segment ℝ _ _
        rcases (hdis s hs0 s' hs' hss ⟨hyseg, hys'⟩).1 with h | h
        · exact hy1 h
        · exact hy2 (Set.mem_singleton_iff.1 h)
  refine ⟨S, fun s hs => hne s (hS0 s hs).1,
    fun s hs s' hs' => hdis s (hS0 s hs).1 s' (hS0 s' hs').1,
    fun s hs => hsG s (hS0 s hs).1, ?_, ?_, ?_⟩
  · intro s hs
    exact (convex_openSegment _ _).isPreconnected.subset_closure (hopen s hs)
      (diff_subset.trans segment_subset_closure_openSegment)
  · intro s hs
    apply Subset.antisymm
    · exact closure_minimal diff_subset (Subdiv.isClosed_segment' _ _)
    · exact segment_subset_closure_openSegment.trans (closure_mono (hopen s hs))
  · ext z
    constructor
    · rintro ⟨hzG, hzKP⟩
      have hzG' := hzG
      rw [hGS] at hzG'
      obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hzG'
      exact mem_biUnion (Finset.mem_filter.2 ⟨hs, fun h => hzKP (Or.inl (h hzs))⟩) ⟨hzs, hzKP⟩
    · intro hz
      obtain ⟨s, hs, hzs, hzKP⟩ := mem_iUnion₂.1 hz
      exact ⟨hsG s (hS0 s hs).1 hzs, hzKP⟩

/-- Components of a relatively open subset of a PL graph are relative neighbourhoods of their
points (a small fan at the point is connected and lies in the open set). -/
theorem IsPLGraph.connectedComponentIn_inter_mem_nhdsWithin {G O : Set E} (hG : IsPLGraph G)
    (hO : IsOpen O) {x y : E} (hy : y ∈ _root_.connectedComponentIn (G ∩ O) x) :
    _root_.connectedComponentIn (G ∩ O) x ∈ 𝓝[G] y := by
  have hyGO := connectedComponentIn_subset _ _ hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO y hyGO.2
  obtain ⟨Y, n, z, -, rfl, hYG, -, hYn, hdiam⟩ := hG.exists_fan hyGO.1 hr
  have hbdd : Bornology.IsBounded (insert y (⋃ k, segment ℝ y (z k))) :=
    (Bornology.isBounded_iUnion.2 fun k =>
      (Subdiv.isCompact_segment' y (z k)).isBounded).insert y
  have hYball : insert y (⋃ k, segment ℝ y (z k)) ⊆ ball y r := fun w hw =>
    mem_ball.2 (lt_of_le_of_lt (dist_le_diam_of_mem hbdd hw (mem_insert _ _)) hdiam)
  have hpre : IsPreconnected (insert y (⋃ k, segment ℝ y (z k))) := by
    refine isPreconnected_of_forall y fun w hw => ?_
    rcases hw with rfl | hw
    · exact ⟨{w}, singleton_subset_iff.2 (mem_insert _ _), rfl, rfl, isPreconnected_singleton⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hw
      exact ⟨segment ℝ y (z k), fun v hv => mem_insert_of_mem _ (mem_iUnion.2 ⟨k, hv⟩),
        left_mem_segment ℝ _ _, hk, (convex_segment _ _).isPreconnected⟩
  rw [connectedComponentIn_eq hy]
  exact Filter.mem_of_superset hYn
    (hpre.subset_connectedComponentIn (mem_insert _ _) fun w hw => ⟨hYG hw, hball (hYball hw)⟩)

/-- **§2.1**: `G \ (K ∪ P)` has finitely many components (`K` a PL graph, `P` finite). -/
theorem IsPLGraph.finite_components_diff {G K P : Set E} (hG : IsPLGraph G) (hK : IsPLGraph K)
    (hKG : K ⊆ G) (hP : P.Finite) (hPG : P ⊆ G) :
    {C : Set E | ∃ x ∈ G \ (K ∪ P), C = _root_.connectedComponentIn (G \ (K ∪ P)) x}.Finite := by
  obtain ⟨S, -, -, -, hpc, -, hU⟩ := hG.exists_pieces hK hKG hP hPG
  exact finite_components_of_pieces hpc hU

/-- **§2.1**: a component of `G \ (K ∪ P)` is a relative neighbourhood of each of its points.

Shape change (batch 195): the skeleton's hypotheses `K ⊆ G` and `P ⊆ G` are not needed and
have been dropped. -/
theorem IsPLGraph.comp_diff_mem_nhdsWithin {G K P : Set E} (hG : IsPLGraph G)
    (hK : IsPLGraph K) (hP : P.Finite) {x y : E}
    (hy : y ∈ _root_.connectedComponentIn (G \ (K ∪ P)) x) :
    _root_.connectedComponentIn (G \ (K ∪ P)) x ∈ 𝓝[G] y := by
  have hc : IsClosed (K ∪ P) := hK.isCompact.isClosed.union hP.isClosed
  rw [diff_eq] at hy ⊢
  exact hG.connectedComponentIn_inter_mem_nhdsWithin hc.isOpen_compl hy

/-- **§2.1**: the closure of a component of `G \ (K ∪ P)` is a PL graph. -/
theorem IsPLGraph.closure_comp_diff {G K P : Set E} (hG : IsPLGraph G) (hK : IsPLGraph K)
    (hKG : K ⊆ G) (hP : P.Finite) (hPG : P ⊆ G) (x : E) :
    IsPLGraph (closure (_root_.connectedComponentIn (G \ (K ∪ P)) x)) := by
  classical
  obtain ⟨S, hne, hdis, -, hpc, hcl, hU⟩ := hG.exists_pieces hK hKG hP hPG
  rw [connectedComponentIn_eq_biUnion_pieces hpc hU x, Finset.closure_biUnion]
  rw [iUnion₂_congr fun s hs => hcl s (Finset.mem_filter.1 hs).1]
  exact isPLGraph_biUnion_filter hne hdis _

/-- **§2.1**: the frontier of a component of `G \ (K ∪ P)` lies in the frontier of `K ∪ P`.

Shape change (batch 195): the skeleton's hypotheses `K ⊆ G` and `P ⊆ G` are not needed and
have been dropped. -/
theorem IsPLGraph.relFrontier_comp_diff {G K P : Set E} (hG : IsPLGraph G) (hK : IsPLGraph K)
    (hP : P.Finite) (x : E) :
    relFrontier G (_root_.connectedComponentIn (G \ (K ∪ P)) x) ⊆ relFrontier G (K ∪ P) := by
  rintro z ⟨hzC, hzD⟩
  have hGc : IsClosed G := hG.isCompact.isClosed
  have hCG : _root_.connectedComponentIn (G \ (K ∪ P)) x ⊆ G :=
    (connectedComponentIn_subset _ _).trans diff_subset
  have hzG : z ∈ G := closure_minimal hCG hGc hzC
  by_cases hz : z ∈ K ∪ P
  · exact ⟨subset_closure hz, closure_mono (connectedComponentIn_subset _ _) hzC⟩
  · exfalso
    have hz' : z ∈ _root_.connectedComponentIn (G \ (K ∪ P)) z := mem_connectedComponentIn ⟨hzG, hz⟩
    obtain ⟨u, hu, hzu, hut⟩ := mem_nhdsWithin.1 (hG.comp_diff_mem_nhdsWithin hK hP hz')
    obtain ⟨w, hwu, hwC⟩ := mem_closure_iff.1 hzC u hu hzu
    have hwz := hut ⟨hwu, hCG hwC⟩
    have hCeq : _root_.connectedComponentIn (G \ (K ∪ P)) x =
        _root_.connectedComponentIn (G \ (K ∪ P)) z :=
      (connectedComponentIn_eq hwC).trans (connectedComponentIn_eq hwz).symm
    obtain ⟨v, hvu, hvG, hvC⟩ := mem_closure_iff.1 hzD u hu hzu
    exact hvC (hCeq ▸ hut ⟨hvu, hvG⟩)

/-- A point inside an edge of a decomposition is ordinary: the edge is a neighbourhood. -/
theorem isOrdinaryPt_of_mem_openSegment {G : Set E} {S : Finset (E × E)}
    (hne : ∀ s ∈ S, s.1 ≠ s.2) (hGS : G = ⋃ s ∈ S, segment ℝ s.1 s.2)
    (hdis : PairwiseEndpoints S) {s : E × E} (hs : s ∈ S) {x : E}
    (hx : x ∈ openSegment ℝ s.1 s.2) : IsOrdinaryPt G x := by
  classical
  have hxs := openSegment_subset_segment ℝ _ _ hx
  have hx1 : x ≠ s.1 := by rintro rfl; exact hne s hs (left_mem_openSegment_iff.1 hx)
  have hx2 : x ≠ s.2 := by rintro rfl; exact hne s hs (right_mem_openSegment_iff.1 hx)
  have hunion : segment ℝ s.1 x ∪ segment ℝ x s.2 = segment ℝ s.1 s.2 := by
    apply Subset.antisymm
    · exact union_subset ((convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) hxs)
        ((convex_segment _ _).segment_subset hxs (right_mem_segment ℝ _ _))
    · intro p hp
      rcases segment_subset_union_of_mem hxs hp with h | h
      · left; rw [segment_symm]; exact h
      · exact Or.inr h
  refine ⟨s.1, s.2, hx1.symm, hx2.symm, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro p ⟨hp1, hp2⟩
      rw [segment_symm] at hp1
      exact eq_of_mem_segment_halves hxs hx1 hx2 hp1 hp2
    · rintro p rfl; exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  · rw [hunion, hGS]; exact subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2) hs
  · rw [hunion]
    have hRc : IsClosed (⋃ s' ∈ S.erase s, segment ℝ s'.1 s'.2) := isClosed_biUnion_segment _
    have hxR : x ∉ ⋃ s' ∈ S.erase s, segment ℝ s'.1 s'.2 := by
      intro h
      obtain ⟨s', hs', hxs'⟩ := mem_iUnion₂.1 h
      rcases (hdis s hs s' (Finset.mem_of_mem_erase hs') (Finset.ne_of_mem_erase hs').symm
        ⟨hxs, hxs'⟩).1 with h | h
      · exact hx1 h
      · exact hx2 (Set.mem_singleton_iff.1 h)
    refine mem_nhdsWithin.2 ⟨_, hRc.isOpen_compl, hxR, ?_⟩
    rintro p ⟨hpR, hpG⟩
    rw [hGS] at hpG
    obtain ⟨s', hs', hps'⟩ := mem_iUnion₂.1 hpG
    by_cases h : s' = s
    · subst h; exact hps'
    · exact absurd (mem_iUnion₂.2 ⟨s', Finset.mem_erase.2 ⟨h, hs'⟩, hps'⟩) hpR

/-- A point `x + t • d` (`t > 0`, `d ≠ 0`) of a segment `[x, c]` makes `c - x` a positive
multiple of `d`. -/
theorem posPar_of_mem_segment {x c d : E} {t : ℝ} (ht : 0 < t) (hd : d ≠ 0)
    (h : x + t • d ∈ segment ℝ x c) : ∃ μ : ℝ, 0 < μ ∧ c - x = μ • d := by
  rw [segment_eq_image'] at h
  obtain ⟨s, ⟨hs0, -⟩, hs⟩ := h
  have hs' : s • (c - x) = t • d := add_left_cancel hs
  have hs0' : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hs'
    exact smul_ne_zero ht.ne' hd hs'.symm
  refine ⟨t / s, div_pos ht (lt_of_le_of_ne hs0 (Ne.symm hs0')), ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← hs', smul_smul, inv_mul_cancel₀ hs0', one_smul]

/-- Two segments from `x` in positively parallel directions share a point other than `x` and
their far endpoints. -/
theorem exists_common_of_posPar {x c c' : E} {μ : ℝ} (hc : c ≠ x) (hμ : 0 < μ)
    (h : c' - x = μ • (c - x)) :
    ∃ p ∈ segment ℝ x c ∩ segment ℝ x c', p ≠ x ∧ p ≠ c ∧ p ≠ c' := by
  set ν : ℝ := min 1 μ / 2 with hν
  have hν0 : 0 < ν := by positivity
  have hν1 : ν < 1 := by have := min_le_left 1 μ; linarith
  have hνμ : ν < μ := by have := min_le_right 1 μ; linarith
  have hcx : c - x ≠ 0 := sub_ne_zero.2 hc
  refine ⟨x + ν • (c - x), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [segment_eq_image']; exact ⟨ν, ⟨hν0.le, hν1.le⟩, rfl⟩
  · rw [segment_eq_image']
    refine ⟨ν / μ, ⟨(div_pos hν0 hμ).le, (div_le_one hμ).2 hνμ.le⟩, ?_⟩
    simp only
    rw [h, smul_smul, div_mul_cancel₀ _ hμ.ne']
  · intro h'
    have : ν • (c - x) = 0 := by
      have := congrArg (· - x) h'; simpa using this
    exact smul_ne_zero hν0.ne' hcx this
  · intro h'
    have : (ν - 1) • (c - x) = 0 := by
      rw [sub_smul, one_smul]
      have := congrArg (· - x) h'
      simp only [add_sub_cancel_left] at this
      rw [this, sub_self]
    exact smul_ne_zero (by linarith) hcx this
  · intro h'
    have : (ν - μ) • (c - x) = 0 := by
      rw [sub_smul, ← h]
      have := congrArg (· - x) h'
      simp only [add_sub_cancel_left] at this
      rw [this, sub_self]
    exact smul_ne_zero (by linarith) hcx this

/-- Small steps from `x` in direction `d` stay in a neighbourhood of `x`. -/
theorem exists_small_step {x : E} {V : Set E} (hV : V ∈ 𝓝 x) (d : E) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ x + t • d ∈ V := by
  have hc : Continuous fun t : ℝ => x + t • d := by fun_prop
  have h0 : (fun t : ℝ => x + t • d) ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h0
  refine ⟨min (ε / 2) 1, by positivity, min_le_right _ _, hball ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)


/-- Rescaling two positive multiples of the same vector. -/
theorem smul_rescale {u v w : E} {μ ν : ℝ} (hν : ν ≠ 0) (hu : u = μ • w) (hv : v = ν • w) :
    u = (μ / ν) • v := by
  rw [hv, smul_smul, div_mul_cancel₀ _ hν]; exact hu

/-- **§2.2**: ordinary points are the points of order 2 of any decomposition.

Shape change (batch 195): the skeleton's hypothesis `x ∈ G` is not needed (both sides force it)
and has been dropped. -/
theorem isOrdinaryPt_iff_order {G : Set E} {S : Finset (E × E)} (hne : ∀ s ∈ S, s.1 ≠ s.2)
    (hGS : G = ⋃ s ∈ S, segment ℝ s.1 s.2) (hdis : PairwiseEndpoints S) {x : E} :
    IsOrdinaryPt G x ↔
      (∃ s ∈ S, x ∈ openSegment ℝ s.1 s.2) ∨
        {s : E × E | s ∈ S ∧ (s.1 = x ∨ s.2 = x)}.ncard = 2 := by
  classical
  by_cases hint : ∃ s ∈ S, x ∈ openSegment ℝ s.1 s.2
  · obtain ⟨s, hs, hxs⟩ := hint
    exact iff_of_true (isOrdinaryPt_of_mem_openSegment hne hGS hdis hs hxs) (Or.inl ⟨s, hs, hxs⟩)
  simp only [hint, false_or]
  set Ex := S.filter (fun s => s.1 = x ∨ s.2 = x) with hEx
  have hset : {s : E × E | s ∈ S ∧ (s.1 = x ∨ s.2 = x)} = ↑Ex := by ext s; simp [hEx]
  rw [hset, Set.ncard_coe_finset]
  set o : E × E → E := fun s => if s.1 = x then s.2 else s.1 with ho
  have ho_ne : ∀ e ∈ Ex, o e ≠ x := by
    intro e he
    obtain ⟨heS, he'⟩ := Finset.mem_filter.1 he
    simp only [ho]
    split_ifs with h
    · rw [← h]; exact (hne e heS).symm
    · rcases he' with h' | h'
      · exact absurd h' h
      · rw [← h']; exact hne e heS
  have hoseg : ∀ e ∈ Ex, segment ℝ e.1 e.2 = segment ℝ x (o e) := by
    intro e he
    obtain ⟨heS, he'⟩ := Finset.mem_filter.1 he
    simp only [ho]
    split_ifs with h
    · rw [h]
    · rcases he' with h' | h'
      · exact absurd h' h
      · rw [h', segment_symm]
  have hends : ∀ e ∈ Ex, ∀ y, y ∈ ({e.1, e.2} : Set E) → y = x ∨ y = o e := by
    intro e he y hy
    obtain ⟨-, he'⟩ := Finset.mem_filter.1 he
    simp only [ho]
    rcases hy with h1 | h2
    · split_ifs with h
      · exact Or.inl (h1.trans h)
      · exact Or.inr h1
    · rw [Set.mem_singleton_iff] at h2
      split_ifs with h
      · exact Or.inr h2
      · rcases he' with h' | h'
        · exact absurd h' h
        · exact Or.inl (h2.trans h')
  have hGe : ∀ e ∈ Ex, segment ℝ x (o e) ⊆ G := by
    intro e he
    rw [← hoseg e he, hGS]
    exact subset_biUnion_of_mem (u := fun s : E × E => segment ℝ s.1 s.2)
      (Finset.mem_filter.1 he).1
  have hpair : ∀ e ∈ Ex, ∀ e' ∈ Ex, e ≠ e' → ∀ y ∈ segment ℝ x (o e) ∩ segment ℝ x (o e'),
      y = x ∨ (y = o e ∧ y = o e') := by
    intro e he e' he' hee' y hy
    have h := hdis e (Finset.mem_filter.1 he).1 e' (Finset.mem_filter.1 he').1 hee'
      (by rw [hoseg e he, hoseg e' he']; exact hy)
    rcases hends e he y h.1 with h1 | h1
    · exact Or.inl h1
    · rcases hends e' he' y h.2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨h1, h2⟩
  have noPar : ∀ e ∈ Ex, ∀ e' ∈ Ex, e ≠ e' → ∀ μ : ℝ, 0 < μ →
      o e' - x ≠ μ • (o e - x) := by
    intro e he e' he' hee' μ hμ h
    obtain ⟨p, hp, hpx, hpe, -⟩ := exists_common_of_posPar (ho_ne e he) hμ h
    rcases hpair e he e' he' hee' p hp with h1 | h1
    · exact hpx h1
    · exact hpe h1.1
  obtain ⟨U, hU, hxU, hUsub⟩ :
      ∃ U, IsOpen U ∧ x ∈ U ∧ G ∩ U ⊆ ⋃ e ∈ Ex, segment ℝ x (o e) := by
    have hRc : IsClosed (⋃ s ∈ S \ Ex, segment ℝ s.1 s.2) := isClosed_biUnion_segment (S \ Ex)
    refine ⟨(⋃ s ∈ S \ Ex, segment ℝ s.1 s.2)ᶜ, hRc.isOpen_compl, ?_, ?_⟩
    · intro h
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 h
      obtain ⟨hsS, hs'⟩ := Finset.mem_sdiff.1 hs
      rw [← insert_endpoints_openSegment] at hxs
      rcases hxs with h1 | h2 | h3
      · exact hs' (Finset.mem_filter.2 ⟨hsS, Or.inl h1.symm⟩)
      · exact hs' (Finset.mem_filter.2 ⟨hsS, Or.inr h2.symm⟩)
      · exact hint ⟨s, hsS, h3⟩
    · rintro z ⟨hzG, hzU⟩
      rw [hGS] at hzG
      obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hzG
      by_cases hsE : s ∈ Ex
      · exact mem_iUnion₂.2 ⟨s, hsE, hoseg s hsE ▸ hzs⟩
      · exact absurd (mem_iUnion₂.2 ⟨s, Finset.mem_sdiff.2 ⟨hs, hsE⟩, hzs⟩) hzU
  constructor
  · rintro ⟨a, b, hax, hbx, hab, hsub, hN⟩
    obtain ⟨V, hV, hxV, hVsub⟩ := mem_nhdsWithin.1 hN
    have hW : U ∩ V ∈ 𝓝 x := (hU.inter hV).mem_nhds ⟨hxU, hxV⟩
    have hdir : ∀ e ∈ Ex, (∃ μ : ℝ, 0 < μ ∧ o e - x = μ • (a - x)) ∨
        (∃ μ : ℝ, 0 < μ ∧ o e - x = μ • (b - x)) := by
      intro e he
      obtain ⟨t, ht0, ht1, htW⟩ := exists_small_step hW (o e - x)
      have hpe : x + t • (o e - x) ∈ segment ℝ x (o e) := by
        rw [segment_eq_image']; exact ⟨t, ⟨ht0.le, ht1⟩, rfl⟩
      have hpN := hVsub ⟨htW.2, hGe e he hpe⟩
      rcases hpN with h | h
      · rw [segment_symm] at h
        obtain ⟨μ, hμ, hμe⟩ := posPar_of_mem_segment ht0 (sub_ne_zero.2 (ho_ne e he)) h
        refine Or.inl ⟨μ⁻¹, inv_pos.2 hμ, ?_⟩
        rw [hμe, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
      · obtain ⟨μ, hμ, hμe⟩ := posPar_of_mem_segment ht0 (sub_ne_zero.2 (ho_ne e he)) h
        refine Or.inr ⟨μ⁻¹, inv_pos.2 hμ, ?_⟩
        rw [hμe, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
    have hexists : ∀ c : E, c ≠ x → segment ℝ x c ⊆ G →
        ∃ e ∈ Ex, ∃ μ : ℝ, 0 < μ ∧ o e - x = μ • (c - x) := by
      intro c hcx hcG
      obtain ⟨t, ht0, ht1, htW⟩ := exists_small_step hW (c - x)
      have hpc : x + t • (c - x) ∈ segment ℝ x c := by
        rw [segment_eq_image']; exact ⟨t, ⟨ht0.le, ht1⟩, rfl⟩
      obtain ⟨e, he, hpe⟩ := mem_iUnion₂.1 (hUsub ⟨hcG hpc, htW.1⟩)
      exact ⟨e, he, posPar_of_mem_segment ht0 (sub_ne_zero.2 hcx) hpe⟩
    have hsubG : segment ℝ a x ∪ segment ℝ x b ⊆ G := hsub
    obtain ⟨ea, hea, μa, hμa, hμea⟩ := hexists a hax
      (by rw [segment_symm]; exact subset_union_left.trans hsubG)
    obtain ⟨eb, heb, μb, hμb, hμeb⟩ := hexists b hbx (subset_union_right.trans hsubG)
    have hnab : ∀ μ : ℝ, 0 < μ → b - x ≠ μ • (a - x) := by
      intro μ hμ h
      obtain ⟨p, ⟨hpa, hpb⟩, hpx, -⟩ := exists_common_of_posPar hax hμ h
      have : p ∈ segment ℝ a x ∩ segment ℝ x b := ⟨by rw [segment_symm]; exact hpa, hpb⟩
      rw [hab] at this
      exact hpx this
    have hab' : ea ≠ eb := by
      rintro rfl
      refine hnab (μa / μb) (div_pos hμa hμb) ?_
      rw [div_eq_inv_mul, mul_smul, ← hμea, hμeb, smul_smul, inv_mul_cancel₀ hμb.ne', one_smul]
    rw [Finset.card_eq_two]
    refine ⟨ea, eb, hab', ?_⟩
    ext e
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro he
      rcases hdir e he with ⟨μ, hμ, h⟩ | ⟨μ, hμ, h⟩
      · left
        by_contra hne'
        exact noPar ea hea e he (Ne.symm hne') (μ / μa) (div_pos hμ hμa)
          (smul_rescale hμa.ne' h hμea)
      · right
        by_contra hne'
        exact noPar eb heb e he (Ne.symm hne') (μ / μb) (div_pos hμ hμb)
          (smul_rescale hμb.ne' h hμeb)
    · rintro (rfl | rfl)
      · exact hea
      · exact heb
  · intro hcard
    obtain ⟨e₁, e₂, h12, hE⟩ := Finset.card_eq_two.1 hcard
    have he₁ : e₁ ∈ Ex := by rw [hE]; simp
    have he₂ : e₂ ∈ Ex := by rw [hE]; simp
    refine ⟨o e₁, o e₂, ho_ne e₁ he₁, ho_ne e₂ he₂, ?_, ?_, ?_⟩
    · apply Subset.antisymm
      · intro y hy
        rw [segment_symm] at hy
        rcases hpair e₁ he₁ e₂ he₂ h12 y ⟨hy.1, hy.2⟩ with h | ⟨h1, h2⟩
        · exact h
        · exact absurd (by rw [one_smul, ← h1, ← h2])
            (noPar e₁ he₁ e₂ he₂ h12 1 one_pos)
      · rintro y rfl
        exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
    · rw [segment_symm]
      exact union_subset (hGe e₁ he₁) (hGe e₂ he₂)
    · refine mem_nhdsWithin.2 ⟨U, hU, hxU, ?_⟩
      rintro z ⟨hzU, hzG⟩
      obtain ⟨e, he, hze⟩ := mem_iUnion₂.1 (hUsub ⟨hzG, hzU⟩)
      rw [hE, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · left; rw [segment_symm]; exact hze
      · exact Or.inr hze

/-- **§2.2**: a PL graph has finitely many branch points and endpoints. -/
theorem IsPLGraph.finite_not_ordinary {G : Set E} (hG : IsPLGraph G) :
    {x ∈ G | ¬ IsOrdinaryPt G x}.Finite := by
  obtain ⟨S, hne, hGS, hdis⟩ := hG
  refine (finite_vertices S).subset ?_
  rintro x ⟨hxG, hxo⟩
  have hxG' := hxG
  rw [hGS] at hxG'
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hxG'
  by_cases h : x ∈ openSegment ℝ s.1 s.2
  · exact absurd (isOrdinaryPt_of_mem_openSegment hne hGS hdis hs h) hxo
  · refine mem_biUnion hs ?_
    rw [← insert_endpoints_openSegment] at hxs
    rcases hxs with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd h3 h

/-- **§2.3**: the intersection of two PL graphs is a PL graph plus finitely many points. -/
theorem IsPLGraph.inter_eq_union_finite {A B : Set E} (hA : IsPLGraph A) (hB : IsPLGraph B) :
    ∃ K P : Set E, IsPLGraph K ∧ P.Finite ∧ A ∩ B = K ∪ P := by
  classical
  have hA' : ∀ i : Fin 2, IsPLGraph (![A, B] i) := by
    intro i; fin_cases i
    · exact hA
    · exact hB
  have hAG' : ∀ i : Fin 2, ![A, B] i ⊆ A ∪ B := by
    intro i; fin_cases i
    · exact subset_union_left
    · exact subset_union_right
  obtain ⟨S, hne, -, hdis, hin, -, -⟩ :=
    (hA.union hB).exists_refinement (k := 2) ![A, B] hA' hAG' ∅ (by simp)
  have hinA : ∀ x ∈ A, ∃ s ∈ S, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ A := hin 0
  have hinB : ∀ x ∈ B, ∃ s ∈ S, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ B := hin 1
  clear hin hA' hAG'
  have hK := isPLGraph_biUnion_filter hne hdis
    (fun s => segment ℝ s.1 s.2 ⊆ A ∧ segment ℝ s.1 s.2 ⊆ B)
  refine ⟨_, A ∩ B ∩ ⋃ s ∈ S, ({s.1, s.2} : Set E), hK,
    (finite_vertices S).subset inter_subset_right, ?_⟩
  apply Subset.antisymm
  · rintro z ⟨hzA, hzB⟩
    obtain ⟨s, hs, hzs, hsA⟩ := hinA z hzA
    obtain ⟨s', hs', hzs', hsB⟩ := hinB z hzB
    by_cases hss : s = s'
    · subst hss
      exact Or.inl (mem_iUnion₂.2 ⟨s, Finset.mem_filter.2 ⟨hs, hsA, hsB⟩, hzs⟩)
    · exact Or.inr ⟨⟨hzA, hzB⟩, mem_iUnion₂.2 ⟨s, hs, (hdis s hs s' hs' hss ⟨hzs, hzs'⟩).1⟩⟩
  · rintro z (hz | ⟨hz, -⟩)
    · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hz
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hs
      exact ⟨h1 hzs, h2 hzs⟩
    · exact hz

/-- A single nondegenerate segment is a PL graph. -/
theorem isPLGraph_segment {a b : E} (h : a ≠ b) : IsPLGraph (segment ℝ a b) :=
  ⟨{(a, b)}, by simp [h], by simp, by simp⟩

omit [NormedSpace ℝ E] in
theorem image_fst_segment (p q : E × ℝ) [NormedSpace ℝ E] :
    Prod.fst '' segment ℝ p q = segment ℝ p.1 q.1 :=
  image_segment ℝ (LinearMap.fst ℝ E ℝ).toAffineMap p q

omit [NormedSpace ℝ E] in
/-- `π` is injective on a segment whose endpoints have different first coordinates. -/
theorem injOn_fst_segment [NormedSpace ℝ E] {p q : E × ℝ} (h : p.1 ≠ q.1) :
    InjOn Prod.fst (segment ℝ p q) := by
  intro x hx y hy hxy
  obtain ⟨t, -, rfl⟩ := mem_segment_iff_param.1 hx
  obtain ⟨u, -, rfl⟩ := mem_segment_iff_param.1 hy
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub] at hxy
  have h2 : t • (q.1 - p.1) = u • (q.1 - p.1) := add_left_cancel hxy
  have h3 : (t - u) • (q.1 - p.1) = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.1 h3 with h4 | h4
  · rw [sub_eq_zero.1 h4]
  · exact absurd (sub_eq_zero.1 h4).symm h

/-- A PL graph plus finitely many points. -/
def IsPLPlusFinite (X : Set E) : Prop := ∃ K P : Set E, IsPLGraph K ∧ P.Finite ∧ X = K ∪ P

theorem IsPLPlusFinite.union {X Y : Set E} (hX : IsPLPlusFinite X) (hY : IsPLPlusFinite Y) :
    IsPLPlusFinite (X ∪ Y) := by
  obtain ⟨K, P, hK, hP, rfl⟩ := hX
  obtain ⟨K', P', hK', hP', rfl⟩ := hY
  exact ⟨K ∪ K', P ∪ P', hK.union hK', hP.union hP', union_union_union_comm K P K' P'⟩

theorem isPLPlusFinite_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set E)
    (h : ∀ i ∈ s, IsPLPlusFinite (f i)) : IsPLPlusFinite (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, ∅, isPLGraph_empty, finite_empty, by simp⟩
  | insert a t _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self _ _)).union
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- One edge of `F`: `[p, q] ∩ π⁻¹(A)` is a PL graph plus finitely many points. -/
theorem segment_inter_preimage_fst {p q : E × ℝ} (hpq : p ≠ q) {A : Set E} (hA : IsPLGraph A) :
    IsPLPlusFinite (segment ℝ p q ∩ Prod.fst ⁻¹' A) := by
  have himg := image_fst_segment p q
  have hmem : ∀ z ∈ segment ℝ p q, z.1 ∈ segment ℝ p.1 q.1 := fun z hz => by
    rw [← himg]; exact mem_image_of_mem _ hz
  by_cases h1 : p.1 = q.1
  · have hz1 : ∀ z ∈ segment ℝ p q, z.1 = p.1 := fun z hz => by
      have := hmem z hz
      rwa [← h1, segment_same, mem_singleton_iff] at this
    by_cases hA1 : p.1 ∈ A
    · refine ⟨segment ℝ p q, ∅, isPLGraph_segment hpq, finite_empty, ?_⟩
      rw [union_empty]
      refine inter_eq_left.2 fun z hz => ?_
      show z.1 ∈ A
      rw [hz1 z hz]
      exact hA1
    · refine ⟨∅, ∅, isPLGraph_empty, finite_empty, ?_⟩
      rw [union_empty]
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
      intro hz hzA
      rw [hz1 z hz] at hzA
      exact hA1 hzA
  · have hinj := injOn_fst_segment h1
    obtain ⟨K, P, hK, hP, hKP⟩ := (isPLGraph_segment h1).inter_eq_union_finite hA
    have hKseg : K ⊆ segment ℝ p.1 q.1 := fun y hy => by
      have : y ∈ segment ℝ p.1 q.1 ∩ A := by rw [hKP]; exact Or.inl hy
      exact this.1
    have hψ : ∀ y ∈ segment ℝ p.1 q.1, Function.invFunOn Prod.fst (segment ℝ p q) y ∈
        segment ℝ p q ∧ (Function.invFunOn Prod.fst (segment ℝ p q) y).1 = y := by
      intro y hy
      have hex : ∃ a ∈ segment ℝ p q, a.1 = y := by rw [← himg] at hy; exact hy
      exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
    set ψ := Function.invFunOn Prod.fst (segment ℝ p q) with hψdef
    have hlift : ∀ c ∈ segment ℝ p.1 q.1, ∀ d ∈ segment ℝ p.1 q.1,
        segment ℝ p q ∩ Prod.fst ⁻¹' segment ℝ c d = segment ℝ (ψ c) (ψ d) := by
      intro c hc d hd
      have himg' := image_fst_segment (ψ c) (ψ d)
      rw [(hψ c hc).2, (hψ d hd).2] at himg'
      have hsub : segment ℝ (ψ c) (ψ d) ⊆ segment ℝ p q :=
        (convex_segment p q).segment_subset (hψ c hc).1 (hψ d hd).1
      apply Subset.antisymm
      · rintro z ⟨hz, hzcd⟩
        rw [mem_preimage, ← himg'] at hzcd
        obtain ⟨w, hw, hwz⟩ := hzcd
        rwa [hinj (hsub hw) hz hwz] at hw
      · intro z hz
        refine ⟨hsub hz, ?_⟩
        rw [mem_preimage, ← himg']
        exact mem_image_of_mem _ hz
    obtain ⟨T, hTne, hKT, -⟩ := hK
    have hTseg : ∀ t ∈ T, t.1 ∈ segment ℝ p.1 q.1 ∧ t.2 ∈ segment ℝ p.1 q.1 := fun t ht =>
      ⟨hKseg (hKT ▸ mem_biUnion ht (left_mem_segment ℝ _ _)),
        hKseg (hKT ▸ mem_biUnion ht (right_mem_segment ℝ _ _))⟩
    refine ⟨⋃ t ∈ T, segment ℝ (ψ t.1) (ψ t.2), segment ℝ p q ∩ Prod.fst ⁻¹' P, ?_, ?_, ?_⟩
    · classical
      have : (⋃ t ∈ T, segment ℝ (ψ t.1) (ψ t.2)) =
          ⋃ t ∈ T.image (fun t => (ψ t.1, ψ t.2)), segment ℝ t.1 t.2 := by
        ext z
        simp only [mem_iUnion, Finset.mem_image, exists_prop]
        constructor
        · rintro ⟨t, ht, hz⟩; exact ⟨_, ⟨t, ht, rfl⟩, hz⟩
        · rintro ⟨_, ⟨t, ht, rfl⟩, hz⟩; exact ⟨t, ht, hz⟩
      rw [this]
      refine isPLGraph_biUnion ?_
      simp only [Finset.mem_image]
      rintro _ ⟨t, ht, rfl⟩ heq
      apply hTne t ht
      rw [← (hψ _ (hTseg t ht).1).2, ← (hψ _ (hTseg t ht).2).2]
      exact congrArg Prod.fst heq
    · refine Finite.of_finite_image (hP.subset ?_) (hinj.mono inter_subset_left)
      rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
      exact hz
    · have hA' : segment ℝ p q ∩ Prod.fst ⁻¹' A =
          segment ℝ p q ∩ Prod.fst ⁻¹' (segment ℝ p.1 q.1 ∩ A) := by
        ext z
        constructor
        · rintro ⟨hz, hzA⟩; exact ⟨hz, hmem z hz, hzA⟩
        · rintro ⟨hz, -, hzA⟩; exact ⟨hz, hzA⟩
      rw [hA', hKP, preimage_union, inter_union_distrib_left, hKT, preimage_iUnion₂,
        inter_iUnion₂]
      congr 1
      exact iUnion₂_congr fun t ht => hlift _ (hTseg t ht).1 _ (hTseg t ht).2

/-- **§2.3**: `F ∩ π⁻¹(A)` is a PL graph plus finitely many points. -/
theorem IsPLGraph.inter_preimage_fst {F : Set (E × ℝ)} {A : Set E} (hF : IsPLGraph F)
    (hA : IsPLGraph A) :
    ∃ K P : Set (E × ℝ), IsPLGraph K ∧ P.Finite ∧ F ∩ Prod.fst ⁻¹' A = K ∪ P := by
  obtain ⟨S, hne, rfl, -⟩ := hF
  rw [iUnion₂_inter]
  exact isPLPlusFinite_biUnion S _ fun s hs => segment_inter_preimage_fst (hne s hs) hA

/-- **§2.3**: a PL graph plus finitely many points, none of them isolated, is a PL graph. -/
theorem isPLGraph_union_finite {K P : Set E} (hK : IsPLGraph K) (hP : P.Finite)
    (h : ∀ p ∈ P, p ∈ closure ((K ∪ P) \ {p})) : IsPLGraph (K ∪ P) := by
  have hPK : P ⊆ K := by
    intro p hp
    have hsub : (K ∪ P) \ {p} ⊆ K ∪ (P \ {p}) := by
      rintro z ⟨hz | hz, hzp⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hz, hzp⟩
    have h2 := closure_mono hsub (h p hp)
    rw [closure_union, hK.isCompact.isClosed.closure_eq,
      (hP.subset diff_subset).isClosed.closure_eq] at h2
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd rfl h2.2
  rwa [union_eq_left.2 hPK]

end Library

end HPC.HO16
