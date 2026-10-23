import HPC.Hagopian.H76Cover

/-!
# Batch 170, item D (part): `crossing_set_closed` (commission 170 §2.D, report 167 §5)

"Let `v` be the first point of `[0, 1]` such that …" (p. 347): the set of parameters `v` whose layer
contains a connected set inside a closed region `W` meeting two closed sets `A`, `B` (the side edges
with margins) is closed, so it has a least element when nonempty. Proof by the topological upper
limit `⋂ N, Cl ⋃_{m ≥ N} Zₘ` of a subsequence: it is connected (`limsup_isPreconnected`, the
classical "lim inf ≠ ∅ ⇒ lim sup connected" for compact Hausdorff spaces), lies in `W` and in the
limit layer, and meets `A` and `B`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane

theorem limsup_mem_of_tendsto {X : Type*} [TopologicalSpace X] {Z : ℕ → Set X} {a : X}
    {s : ℕ → X} (hs : ∀ n, s n ∈ Z n) (ha : Tendsto s atTop (𝓝 a)) :
    a ∈ ⋂ N, closure (⋃ m ≥ N, Z m) :=
  mem_iInter.2 fun N => mem_closure_of_tendsto ha
    (eventually_atTop.2 ⟨N, fun m hm => mem_biUnion hm (hs m)⟩)

theorem limsup_subset_of_eventually {X : Type*} [TopologicalSpace X] {Z : ℕ → Set X} {C : Set X}
    (hC : IsClosed C) (h : ∀ᶠ n in atTop, Z n ⊆ C) : ⋂ N, closure (⋃ m ≥ N, Z m) ⊆ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact (iInter_subset _ N).trans (closure_minimal (iUnion₂_subset fun m hm => hN m hm) hC)

/-- **The upper limit of connected sets with a convergent selection is connected** (compact
Hausdorff spaces). -/
theorem limsup_isPreconnected {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Z : ℕ → Set X} (hZ : ∀ n, IsPreconnected (Z n)) {a : X} {s : ℕ → X}
    (hs : ∀ n, s n ∈ Z n) (ha : Tendsto s atTop (𝓝 a)) :
    IsPreconnected (⋂ N, closure (⋃ m ≥ N, Z m)) := by
  set L := ⋂ N, closure (⋃ m ≥ N, Z m) with hL
  have hLc : IsClosed L := isClosed_iInter fun _ => isClosed_closure
  have haL : a ∈ L := limsup_mem_of_tendsto hs ha
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  suffices key : ∀ u v : Set X, IsClosed u → IsClosed v → L ⊆ u ∪ v → L ∩ (u ∩ v) = ∅ →
      a ∈ u → L ⊆ u by
    intro u v hu hv huv hLuv
    rcases huv haL with h | h
    · exact Or.inl (key u v hu hv huv hLuv h)
    · exact Or.inr (key v u hv hu (by rwa [union_comm]) (by rw [inter_comm v u]; exact hLuv) h)
  intro u v hu hv huv hLuv hau
  obtain ⟨U, V, hUo, hVo, hLU, hLV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (hLc.inter hu).isCompact (hLc.inter hv).isCompact (by
      rw [disjoint_iff_inter_eq_empty, ← hLuv]; ext x; simp only [mem_inter_iff]; tauto)
  have hLUV : L ⊆ U ∪ V := fun x hx => (huv hx).elim (fun h => Or.inl (hLU ⟨hx, h⟩))
    (fun h => Or.inr (hLV ⟨hx, h⟩))
  set t : ℕ → Set X := fun N => closure (⋃ m ≥ N, Z m) \ (U ∪ V) with ht
  have htc : ∀ N, IsClosed (t N) := fun N => isClosed_closure.sdiff (hUo.union hVo)
  have hmono : Antitone (fun N => closure (⋃ m ≥ N, Z m)) := fun N₁ N₂ h12 =>
    closure_mono (biUnion_subset_biUnion_left fun m hm => le_trans h12 hm)
  have htd : Directed (fun x1 x2 => x1 ⊇ x2) t := by
    have : Antitone t := fun N₁ N₂ h12 => diff_subset_diff_left (hmono h12)
    exact this.directed_ge
  have hint : univ ∩ ⋂ N, t N = ∅ := by
    rw [univ_inter, eq_empty_iff_forall_notMem]
    intro x hx
    have hxL : x ∈ L := mem_iInter.2 fun N => (mem_iInter.1 hx N).1
    exact (mem_iInter.1 hx 0).2 (hLUV hxL)
  obtain ⟨N, hN⟩ := isCompact_univ.elim_directed_family_closed t htc hint htd
  rw [univ_inter] at hN
  have hZUV : ∀ m ≥ N, Z m ⊆ U ∪ V := by
    intro m hm x hx
    by_contra hxUV
    have : x ∈ t N := ⟨subset_closure (mem_biUnion hm hx), hxUV⟩
    rw [hN] at this
    exact this
  obtain ⟨N', hN'⟩ := eventually_atTop.1 (ha (hUo.mem_nhds (hLU ⟨haL, hau⟩)))
  have hZU : ∀ m ≥ max N N', Z m ⊆ U := fun m hm =>
    (hZ m).subset_left_of_subset_union hUo hVo hUV (hZUV m (le_of_max_le_left hm))
      ⟨s m, hs m, hN' m (le_of_max_le_right hm)⟩
  have hLclU : L ⊆ closure U := by
    intro x hx
    have := mem_iInter.1 hx (max N N')
    exact closure_mono (iUnion₂_subset fun m hm => hZU m hm) this
  intro x hx
  rcases huv hx with h | h
  · exact h
  · exact absurd (hLV ⟨hx, h⟩) (disjoint_left.1 (hUV.closure_left hVo) (hLclU hx))

/-- **`crossing_set_closed`, abstract form.** For a continuous real function `d` on a compact metric
space and closed sets `A`, `B`, `W`, the set of `v` such that `W ∩ d⁻¹(v)` contains a connected set
meeting `A` and `B` is closed. -/
theorem isClosed_crossing_params {X : Type*} [MetricSpace X] [CompactSpace X] {d : X → ℝ}
    (hd : Continuous d) {A B W : Set X} (hA : IsClosed A) (hB : IsClosed B) (hW : IsClosed W) :
    IsClosed {v : ℝ | ∃ Z : Set X, IsPreconnected Z ∧ Z ⊆ W ∩ d ⁻¹' {v} ∧ (Z ∩ A).Nonempty ∧
      (Z ∩ B).Nonempty} := by
  refine isClosed_of_closure_subset fun v hv => ?_
  obtain ⟨w, hwS, hwv⟩ := mem_closure_iff_seq_limit.1 hv
  choose Z hZc hZW hZA hZB using hwS
  choose a haZ using hZA
  choose b hbZ using hZB
  obtain ⟨p, -, φ, hφ, hp⟩ := isCompact_univ.tendsto_subseq (x := fun n => (a n, b n))
    (fun _ => mem_univ _)
  have hpa : Tendsto (fun n => a (φ n)) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hp
  have hpb : Tendsto (fun n => b (φ n)) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hp
  have hwφ : Tendsto (fun n => w (φ n)) atTop (𝓝 v) := hwv.comp hφ.tendsto_atTop
  refine ⟨⋂ N, closure (⋃ m ≥ N, Z (φ m)), ?_, fun x hx => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact limsup_isPreconnected (fun n => hZc (φ n)) (fun n => (haZ (φ n)).1) hpa
  · exact limsup_subset_of_eventually hW
      (Eventually.of_forall fun n => fun z hz => (hZW _ hz).1) hx
  · show d x = v
    refine eq_of_forall_dist_le fun ε hε => ?_
    have hev : ∀ᶠ n in atTop, Z (φ n) ⊆ d ⁻¹' closedBall v ε := by
      filter_upwards [hwφ (closedBall_mem_nhds v hε)] with n hn
      intro z hz
      have := (hZW _ hz).2
      rw [mem_preimage, mem_singleton_iff] at this
      rw [mem_preimage, this]
      exact hn
    exact limsup_subset_of_eventually (isClosed_closedBall.preimage hd) hev hx
  · exact ⟨p.1, limsup_mem_of_tendsto (fun n => (haZ (φ n)).1) hpa,
      hA.mem_of_tendsto hpa (Eventually.of_forall fun n => (haZ (φ n)).2)⟩
  · exact ⟨p.2, limsup_mem_of_tendsto (fun n => (hbZ (φ n)).1) hpb,
      hB.mem_of_tendsto hpb (Eventually.of_forall fun n => (hbZ (φ n)).2)⟩

/-- **`crossing_set_closed`, for the layers of a continuum `F ⊆ M`** (map `d`): for closed sets
`A`, `B`, `W` of the plane (Hagopian's side edges and the region over `Cl D`, with margins), the set
of `v ∈ [0, 1]` such that the layer `d⁻¹(v)` contains a connected set inside `W` meeting `A` and `B`
is closed in `[0, 1]`; so, if nonempty, it has a least element ("Let `v` be the first point"). -/
theorem crossing_set_closed {M : Set Pt} {F : Set M} (hFc : IsCompact F) {d : F → unitInterval}
    (hd : Continuous d) {A B W : Set Pt} (hA : IsClosed A) (hB : IsClosed B) (hW : IsClosed W) :
    IsClosed {v : unitInterval | ∃ Z : Set F, IsPreconnected Z ∧ Z ⊆ d ⁻¹' {v} ∧
      (∀ z ∈ Z, ((z : M) : Pt) ∈ W) ∧ (∃ z ∈ Z, ((z : M) : Pt) ∈ A) ∧
      ∃ z ∈ Z, ((z : M) : Pt) ∈ B} := by
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc
  have hι : Continuous (fun z : F => ((z : M) : Pt)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have key := isClosed_crossing_params (continuous_subtype_val.comp hd) (hA.preimage hι)
    (hB.preimage hι) (hW.preimage hι)
  convert key.preimage continuous_subtype_val using 1
  ext v
  constructor
  · rintro ⟨Z, hZ, hZd, hZW, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩
    refine ⟨Z, hZ, fun z hz => ⟨hZW z hz, ?_⟩, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩
    show ((d z : unitInterval) : ℝ) = (v : ℝ)
    rw [show d z = v from hZd hz]
  · rintro ⟨Z, hZ, hZd, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩
    exact ⟨Z, hZ, fun z hz => Subtype.ext (hZd hz).2, fun z hz => (hZd hz).1, ⟨a, ha, haA⟩,
      ⟨b, hb, hbB⟩⟩

end HPC.Hagopian
