import Mathlib
import HPC.Plane.PseudoArc51
import HPC.Plane.Monotone51
import HPC.Plane.DescrM

/-!
# Bing, *Concerning hereditarily indecomposable continua*, §3: most compact continua are pseudo-arcs

Skeleton for batch 90 (save as `HPC/Plane/Most51.lean`; add `import HPC.Plane.Most51` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded; `theorem2_HIC` keeps its conclusion (if `exists_tame_chain_near` stays open,
`theorem2_HIC` is proved from it and the dependence is recorded).

`IsPseudoArc`, `IsSnakeLike`, `IsEpsChain`, `IsHereditarilyIndecomposable` are from
`Snake51.lean`, `EndPoints51.lean`, `PseudoArc51.lean`.

**Batch 90 delivery.** All statements keep their skeleton shapes. Proved: `isClosed_cont`, the
`CompleteSpace` instance, `isClosed_notCoverable`, `isClosed_separated`, `isClosed_degenerate`,
`isGδ_pseudoArcs`, `exists_pseudoArc_in_tameChain`, `dense_pseudoArcs_of` and `theorem2_HIC_of`.
The hyperspace arguments use Mathlib's Vietoris description of the Hausdorff-metric topology on
`NonemptyCompacts` (`isOpen_subsets_of_isOpen`, `isOpen_inter_nonempty_of_isOpen`,
`isCompact_subsets_of_isCompact`, `isCompact_biUnion_coe_of_isCompact`). The pseudo-arc in a tame
chain is batch 84's planar construction started from `m` standard rectangles
(`HPC/Plane/DescrM.lean`), placed in the `(e₁, e₂)`-plane of `E` and carried by the homeomorphism
of the tame chain (the plane route of COMMISSION-batch90.md §3.6, not a generalisation of
`real_step`). Completeness of `E` is not used by any of the proofs.

**What is now proved, and where (batch 111).** The batch-90 open geometric lemma
`exists_tame_chain_near` (a tame chain near every continuum, i.e. a *homeomorphism of `E`* carrying
the standard boxes onto the links) and its two consequences `dense_pseudoArcs`, `theorem2_HIC` of
this file were deleted in batch 111 (`LEDGER.md` §2): the homeomorphism is more than
`exists_pseudoArc_in_tameChain` uses, and the batch-90 obstruction was an obstruction to that
excess. `GeomLemma E` (that conclusion as a hypothesis), `dense_pseudoArcs_of` and
`theorem2_HIC_of` stay here, proved. The weaker threaded form `GeomLemma'` is in `Band.lean`
(batch 109, with `dense_pseudoArcs_of'`, `theorem2_HIC_of'`).
* *Plane*: `GeomLemma'` is proved for `finrank ℝ E = 2` (`geomLemma'_of_finrank_two`), hence
  Pacific Theorem 2 (`theorem2_HIC_plane`) and Duke Theorem 2 (`theorem2_1951_plane`) in the plane,
  all in `HPC/Plane/LatticeCycle.lean` (batches 109–110).
* *General `E`*: `geomLemma'_of_two_le_rank` (every real inner product space of dimension `≥ 2`)
  is proved in batch 113 in `HPC/Plane/CubeCycle.lean`, together with `dense_pseudoArcs`,
  `theorem2_HIC` (same statements as before) and `theorem2_1951`. (Batch 116 note: it was open
  from batch 111 to batch 113.)
Partial batch-90 results towards the former statement (tame chains in `E`, shears, the tube around
an unbent arc, the case of points and segments, Bing's broken line) are in the archive,
`HPC/Archive/Most51Geom.lean`.
-/

namespace HPC.Plane

open Set TopologicalSpace Metric Filter Topology

/-! ### The hyperspace of compact continua -/

variable {S : Type*} [MetricSpace S]

/-- **The space of compact continua** `C(S)`: nonempty compact connected subsets of `S`, with the
Hausdorff metric inherited from `NonemptyCompacts S`. -/
def Cont (S : Type*) [MetricSpace S] : Type _ :=
  {K : NonemptyCompacts S // IsConnected (K : Set S)}

noncomputable instance : MetricSpace (Cont S) := Subtype.metricSpace

namespace Most

/-- A nonempty compact set that is not connected lies in the union of two disjoint open sets,
each meeting it. -/
theorem exists_open_separation {K : Set S} (hK : IsCompact K) (hne : K.Nonempty)
    (hc : ¬ IsConnected K) :
    ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ K ⊆ U ∪ V ∧ (K ∩ U).Nonempty ∧
      (K ∩ V).Nonempty := by
  have hpc : ¬ IsPreconnected K := fun h => hc ⟨hne, h⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hpc
  push_neg at hpc
  obtain ⟨u, v, hu, hv, hcov, hdisj, hnu, hnv⟩ := hpc
  have hd : Disjoint (K ∩ u) (K ∩ v) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← hdisj]
    ext z; simp only [mem_inter_iff]; tauto
  obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ :=
    normal_separation (hK.isClosed.inter hu) (hK.isClosed.inter hv) hd
  refine ⟨U, V, hU, hV, hUV, fun z hz => ?_, ?_, ?_⟩
  · rcases hcov hz with h | h
    · exact Or.inl (hKU ⟨hz, h⟩)
    · exact Or.inr (hKV ⟨hz, h⟩)
  · obtain ⟨z, hz, hzv⟩ := not_subset.mp hnv
    have hzu : z ∈ u := (hcov hz).resolve_right hzv
    exact ⟨z, hz, hKU ⟨hz, hzu⟩⟩
  · obtain ⟨z, hz, hzu⟩ := not_subset.mp hnu
    have hzv : z ∈ v := (hcov hz).resolve_left hzu
    exact ⟨z, hz, hKV ⟨hz, hzv⟩⟩

end Most

/-- The continua form a closed subset of the hyperspace (a Hausdorff limit of connected compacta
is connected); hence `Cont S` is complete when `S` is. -/
theorem isClosed_cont : IsClosed {K : NonemptyCompacts S | IsConnected (K : Set S)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro K hK
  obtain ⟨U, V, hU, hV, hUV, hcov, hKU, hKV⟩ :=
    Most.exists_open_separation K.isCompact K.nonempty hK
  refine ⟨{L | (L : Set S) ⊆ U ∪ V} ∩ {L | ((L : Set S) ∩ U).Nonempty} ∩
    {L | ((L : Set S) ∩ V).Nonempty}, ?_, ?_, ⟨⟨hcov, hKU⟩, hKV⟩⟩
  · rintro L ⟨⟨hLcov, hLU⟩, hLV⟩ hLc
    obtain ⟨z, -, hzU, hzV⟩ := hLc.isPreconnected U V hU hV hLcov hLU hLV
    exact Set.disjoint_left.mp hUV hzU hzV
  · exact ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU)).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV)

instance [CompleteSpace S] : CompleteSpace (Cont S) :=
  isClosed_cont.completeSpace_coe

namespace Most

/-- A Hausdorff limit of connected compacta is connected. -/
theorem isConnected_of_tendsto {P : ℕ → NonemptyCompacts S} {P₀ : NonemptyCompacts S}
    (hP : Tendsto P atTop (𝓝 P₀)) (h : ∀ n, IsConnected (P n : Set S)) :
    IsConnected (P₀ : Set S) :=
  isClosed_cont.mem_of_tendsto hP (Eventually.of_forall h)

/-- The distance from a point to a set is jointly continuous for the Hausdorff metric. -/
theorem tendsto_infDist {z : ℕ → S} {z₀ : S} {P : ℕ → NonemptyCompacts S}
    {P₀ : NonemptyCompacts S} (hz : Tendsto z atTop (𝓝 z₀)) (hP : Tendsto P atTop (𝓝 P₀)) :
    Tendsto (fun n => infDist (z n) (P n : Set S)) atTop (𝓝 (infDist z₀ (P₀ : Set S))) := by
  set F : S × NonemptyCompacts S → ℝ := fun p => infDist p.1 (p.2 : Set S) with hF
  have hc : Continuous F := lipschitz_infDist.continuous
  have h2 : Tendsto (fun n => (z n, P n)) atTop (𝓝 (z₀, P₀)) := hz.prodMk_nhds hP
  have h3 : Tendsto (F ∘ fun n => (z n, P n)) atTop (𝓝 (F (z₀, P₀))) :=
    (hc.tendsto (z₀, P₀)).comp h2
  exact h3

/-- A limit of points of converging compacta lies in the limit compactum. -/
theorem mem_of_tendsto {z : ℕ → S} {z₀ : S} {P : ℕ → NonemptyCompacts S}
    {P₀ : NonemptyCompacts S} (hz : Tendsto z atTop (𝓝 z₀)) (hP : Tendsto P atTop (𝓝 P₀))
    (h : ∀ n, z n ∈ (P n : Set S)) : z₀ ∈ (P₀ : Set S) := by
  have hc := tendsto_infDist hz hP
  have h0 : (fun n => infDist (z n) (P n : Set S)) = fun _ => 0 :=
    funext fun n => infDist_zero_of_mem (h n)
  rw [h0] at hc
  have : infDist z₀ (P₀ : Set S) = 0 := tendsto_nhds_unique hc tendsto_const_nhds
  rw [← P₀.isCompact.isClosed.closure_eq, mem_closure_iff_infDist_zero P₀.nonempty]
  exact this

/-- Inclusion passes to Hausdorff limits. -/
theorem subset_of_tendsto {P Q : ℕ → NonemptyCompacts S} {P₀ Q₀ : NonemptyCompacts S}
    (hP : Tendsto P atTop (𝓝 P₀)) (hQ : Tendsto Q atTop (𝓝 Q₀))
    (h : ∀ n, (P n : Set S) ⊆ Q n) : (P₀ : Set S) ⊆ Q₀ := by
  intro z hz
  have key : ∀ n, infDist z (Q₀ : Set S) ≤ dist P₀ (P n) + dist (Q n) Q₀ := by
    intro n
    rw [NonemptyCompacts.dist_eq, NonemptyCompacts.dist_eq]
    calc infDist z (Q₀ : Set S) ≤ infDist z (Q n : Set S) + hausdorffDist (Q n : Set S) Q₀ :=
          infDist_le_infDist_add_hausdorffDist (edist_ne_top (Q n) Q₀)
      _ ≤ infDist z (P n : Set S) + hausdorffDist (Q n : Set S) Q₀ := by
          gcongr; exact infDist_le_infDist_of_subset (h n) (P n).nonempty
      _ ≤ hausdorffDist (P₀ : Set S) (P n) + hausdorffDist (Q n : Set S) Q₀ := by
          gcongr; exact infDist_le_hausdorffDist_of_mem hz (edist_ne_top P₀ (P n))
  have ht : Tendsto (fun n => dist P₀ (P n) + dist (Q n) Q₀) atTop (𝓝 (0 + 0)) := by
    refine Tendsto.add ?_ ?_
    · have := (tendsto_iff_dist_tendsto_zero.mp hP)
      simpa only [dist_comm] using this
    · exact tendsto_iff_dist_tendsto_zero.mp hQ
  rw [add_zero] at ht
  have hle : infDist z (Q₀ : Set S) ≤ 0 := ge_of_tendsto' ht key
  rw [← Q₀.isCompact.isClosed.closure_eq, mem_closure_iff_infDist_zero Q₀.nonempty]
  exact le_antisymm hle infDist_nonneg

end Most

/-- `F_i`: the continua that cannot be covered by a chain of mesh below `1/(i+1)`. Closed. -/
theorem isClosed_notCoverable (i : ℕ) :
    IsClosed {K : Cont S | ¬ ∃ (n : ℕ) (D : Chain S n), IsEpsChain D (1 / ((i : ℝ) + 1)) ∧
      (K.1 : Set S) ⊆ D.union} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro K hK
  simp only [mem_compl_iff, mem_setOf_eq, not_not] at hK
  obtain ⟨n, D, hD, hKD⟩ := hK
  refine ⟨{L : Cont S | (L.1 : Set S) ⊆ D.union}, ?_, ?_, hKD⟩
  · intro L hL
    simp only [mem_compl_iff, mem_setOf_eq, not_not]
    exact ⟨n, D, hD, hL⟩
  · exact (NonemptyCompacts.isOpen_subsets_of_isOpen
      (isOpen_iUnion D.isOpen)).preimage continuous_subtype_val

/-- `G_i`: the continua containing a subcontinuum `K₁ ∪ K₂` (connected, `K₁`, `K₂` continua) with
a point of `K₁` at distance `≥ 1/(i+1)` from `K₂` and a point of `K₂` at distance `≥ 1/(i+1)`
from `K₁`. Closed. -/
theorem isClosed_separated (i : ℕ) :
    IsClosed {K : Cont S | ∃ K₁ K₂ : Set S, K₁ ⊆ K.1 ∧ K₂ ⊆ K.1 ∧
      Fold.Q78.IsContinuum K₁ ∧ Fold.Q78.IsContinuum K₂ ∧ IsConnected (K₁ ∪ K₂) ∧
      (∃ x ∈ K₁, 1 / ((i : ℝ) + 1) ≤ infDist x K₂) ∧ (∃ y ∈ K₂, 1 / ((i : ℝ) + 1) ≤ infDist y K₁)} := by
  apply IsSeqClosed.isClosed
  intro Kseq K hmem hlim
  simp only [mem_setOf_eq] at hmem ⊢
  choose A B hA hB hAc hBc hABc hx hy using hmem
  choose x hxA hxB using hx
  choose y hyB hyA using hy
  set k : ℕ → NonemptyCompacts S := fun n => (Kseq n).1 with hk_def
  have hk : Tendsto k atTop (𝓝 K.1) := (continuous_subtype_val.tendsto K).comp hlim
  let A' : ℕ → NonemptyCompacts S := fun n => ⟨⟨A n, (hAc n).1⟩, (hAc n).2.nonempty⟩
  let B' : ℕ → NonemptyCompacts S := fun n => ⟨⟨B n, (hBc n).1⟩, (hBc n).2.nonempty⟩
  set T : Set S := ⋃ L ∈ insert K.1 (range k), (L : Set S) with hT_def
  have hT : IsCompact T :=
    NonemptyCompacts.isCompact_biUnion_coe_of_isCompact hk.isCompact_insert_range
  have hkT : ∀ n, (k n : Set S) ⊆ T := fun n =>
    subset_biUnion_of_mem (u := fun L : NonemptyCompacts S => (L : Set S))
      (mem_insert_of_mem _ (mem_range_self n))
  set 𝒯 : Set (NonemptyCompacts S) := {L | (L : Set S) ⊆ T}
  have h𝒯 : IsCompact 𝒯 := NonemptyCompacts.isCompact_subsets_of_isCompact hT
  have hall : ∀ n, (A' n, B' n, x n, y n) ∈ 𝒯 ×ˢ 𝒯 ×ˢ T ×ˢ T := fun n =>
    ⟨(hA n).trans (hkT n), (hB n).trans (hkT n), hkT n (hA n (hxA n)), hkT n (hB n (hyB n))⟩
  obtain ⟨⟨A₀, B₀, x₀, y₀⟩, -, φ, hφ, hlim'⟩ :=
    (h𝒯.prod (h𝒯.prod (hT.prod hT))).tendsto_subseq hall
  have hA₀ : Tendsto (fun n => A' (φ n)) atTop (𝓝 A₀) := (continuous_fst.tendsto _).comp hlim'
  have hB₀ : Tendsto (fun n => B' (φ n)) atTop (𝓝 B₀) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim'
  have hx₀ : Tendsto (fun n => x (φ n)) atTop (𝓝 x₀) :=
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim'
  have hy₀ : Tendsto (fun n => y (φ n)) atTop (𝓝 y₀) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim'
  have hkφ : Tendsto (fun n => k (φ n)) atTop (𝓝 K.1) := hk.comp hφ.tendsto_atTop
  have hU : Tendsto (fun n => A' (φ n) ⊔ B' (φ n)) atTop (𝓝 (A₀ ⊔ B₀)) :=
    (NonemptyCompacts.lipschitz_sup.continuous.tendsto (A₀, B₀)).comp (hA₀.prodMk_nhds hB₀)
  have hUc : IsConnected ((A₀ ⊔ B₀ : NonemptyCompacts S) : Set S) :=
    Most.isConnected_of_tendsto hU fun n => by
      rw [NonemptyCompacts.coe_sup]; exact hABc (φ n)
  rw [NonemptyCompacts.coe_sup] at hUc
  refine ⟨A₀, B₀, Most.subset_of_tendsto hA₀ hkφ (fun n => hA (φ n)),
    Most.subset_of_tendsto hB₀ hkφ (fun n => hB (φ n)),
    ⟨A₀.isCompact, Most.isConnected_of_tendsto hA₀ fun n => (hAc (φ n)).2⟩,
    ⟨B₀.isCompact, Most.isConnected_of_tendsto hB₀ fun n => (hBc (φ n)).2⟩, hUc,
    ⟨x₀, Most.mem_of_tendsto hx₀ hA₀ (fun n => hxA (φ n)),
      ge_of_tendsto' (Most.tendsto_infDist hx₀ hB₀) (fun n => hxB (φ n))⟩,
    ⟨y₀, Most.mem_of_tendsto hy₀ hB₀ (fun n => hyB (φ n)),
      ge_of_tendsto' (Most.tendsto_infDist hy₀ hA₀) (fun n => hyA (φ n))⟩⟩

/-- The degenerate continua form a closed set. -/
theorem isClosed_degenerate : IsClosed {K : Cont S | ∃ x, (K.1 : Set S) = {x}} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro K hK
  simp only [mem_compl_iff, mem_setOf_eq, not_exists] at hK
  obtain ⟨a, ha⟩ := K.1.nonempty
  obtain ⟨b, hb, hab⟩ : ∃ b ∈ (K.1 : Set S), b ≠ a := by
    by_contra h
    push_neg at h
    exact hK a (Set.eq_singleton_iff_unique_mem.mpr ⟨ha, h⟩)
  obtain ⟨d, hdd⟩ : ∃ d, d = dist a b := ⟨_, rfl⟩
  have hd : 0 < d := hdd ▸ dist_pos.mpr hab.symm
  refine ⟨{L : Cont S | ((L.1 : Set S) ∩ ball a (d / 2)).Nonempty ∧
    ((L.1 : Set S) ∩ ball b (d / 2)).Nonempty}, ?_, ?_, ?_⟩
  · rintro L ⟨⟨u, hu, hua⟩, ⟨v, hv, hvb⟩⟩ ⟨x, hx⟩
    rw [hx] at hu hv
    rw [mem_singleton_iff] at hu hv
    rw [hu] at hua
    rw [hv] at hvb
    rw [mem_ball] at hua hvb
    have h1 := dist_triangle_right a b x
    rw [dist_comm b x, ← hdd] at h1
    linarith [dist_comm a x]
  · exact ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen isOpen_ball).preimage
      continuous_subtype_val).inter
      ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen isOpen_ball).preimage
      continuous_subtype_val)
  · exact ⟨⟨a, ha, mem_ball_self (half_pos hd)⟩, ⟨b, hb, mem_ball_self (half_pos hd)⟩⟩

namespace Most

/-- Not in any `F_i` ⇔ chainable. -/
theorem isSnakeLike_iff (K : Cont S) :
    IsSnakeLike (K.1 : Set S) ↔ ∀ i : ℕ, ∃ (n : ℕ) (D : Chain S n),
      IsEpsChain D (1 / ((i : ℝ) + 1)) ∧ (K.1 : Set S) ⊆ D.union := by
  constructor
  · intro h i
    exact h.2 _ (by positivity)
  · intro h
    refine ⟨⟨K.1.isCompact, K.2⟩, fun ε hε => ?_⟩
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
    obtain ⟨n, D, hD, hKD⟩ := h i
    exact ⟨n, D, fun t => ⟨(hD t).1, (hD t).2.trans hi⟩, hKD⟩

/-- Not in any `G_i` ⇔ hereditarily indecomposable. -/
theorem isHI_iff (K : Cont S) :
    IsHereditarilyIndecomposable (K.1 : Set S) ↔ ∀ i : ℕ, ¬ ∃ K₁ K₂ : Set S, K₁ ⊆ K.1 ∧
      K₂ ⊆ K.1 ∧ Fold.Q78.IsContinuum K₁ ∧ Fold.Q78.IsContinuum K₂ ∧ IsConnected (K₁ ∪ K₂) ∧
      (∃ x ∈ K₁, 1 / ((i : ℝ) + 1) ≤ infDist x K₂) ∧
      (∃ y ∈ K₂, 1 / ((i : ℝ) + 1) ≤ infDist y K₁) := by
  constructor
  · rintro hHI i ⟨K₁, K₂, h₁, h₂, hc₁, hc₂, hc, ⟨x, hx, hxd⟩, ⟨y, hy, hyd⟩⟩
    have hpos : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    have hL : Fold.Q78.IsContinuum (K₁ ∪ K₂) := ⟨hc₁.1.union hc₂.1, hc⟩
    rcases (hHI _ (union_subset h₁ h₂) hL).2 K₁ K₂ hc₁ hc₂ subset_union_left subset_union_right
      rfl with e | e
    · have : y ∈ K₁ := e ▸ Or.inr hy
      rw [infDist_zero_of_mem this] at hyd
      linarith
    · have : x ∈ K₂ := e ▸ Or.inl hx
      rw [infDist_zero_of_mem this] at hxd
      linarith
  · intro h L hLK hL
    refine ⟨hL, fun A B hA hB hAL hBL hAB => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨x, hxA, hxB⟩ : ∃ x ∈ A, x ∉ B := by
      by_contra h'
      push_neg at h'
      exact hne.2 (Subset.antisymm hBL (hAB ▸ union_subset h' le_rfl))
    obtain ⟨y, hyB, hyA⟩ : ∃ y ∈ B, y ∉ A := by
      by_contra h'
      push_neg at h'
      exact hne.1 (Subset.antisymm hAL (hAB ▸ union_subset le_rfl h'))
    have hx := (hB.1.isClosed.notMem_iff_infDist_pos hB.2.nonempty).mp hxB
    have hy := (hA.1.isClosed.notMem_iff_infDist_pos hA.2.nonempty).mp hyA
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt (lt_min hx hy)
    refine h i ⟨A, B, hAL.trans hLK, hBL.trans hLK, hA, hB, hAB ▸ hL.2,
      ⟨x, hxA, (hi.trans_le (min_le_left _ _)).le⟩, ⟨y, hyB, (hi.trans_le (min_le_right _ _)).le⟩⟩

/-- Not degenerate ⇔ nontrivial. -/
theorem nontrivial_iff (K : Cont S) :
    (K.1 : Set S).Nontrivial ↔ ¬ ∃ x, (K.1 : Set S) = {x} := by
  constructor
  · rintro hnt ⟨x, hx⟩
    rw [hx] at hnt
    exact hnt.not_subsingleton subsingleton_singleton
  · intro h
    by_contra hnt
    rw [not_nontrivial_iff] at hnt
    obtain ⟨a, ha⟩ := K.1.nonempty
    exact h ⟨a, hnt.eq_singleton_of_mem ha⟩

end Most

/-- **The pseudo-arcs form a `G_δ`** in `C(S)` (unconditional): the complement of the union of the
closed sets above. -/
theorem isGδ_pseudoArcs : IsGδ {K : Cont S | IsPseudoArc (K.1 : Set S)} := by
  have e : {K : Cont S | IsPseudoArc (K.1 : Set S)} =
      (⋂ i : ℕ, {K : Cont S | ¬ ∃ (n : ℕ) (D : Chain S n), IsEpsChain D (1 / ((i : ℝ) + 1)) ∧
        (K.1 : Set S) ⊆ D.union}ᶜ) ∩
      ((⋂ i : ℕ, {K : Cont S | ∃ K₁ K₂ : Set S, K₁ ⊆ K.1 ∧ K₂ ⊆ K.1 ∧
        Fold.Q78.IsContinuum K₁ ∧ Fold.Q78.IsContinuum K₂ ∧ IsConnected (K₁ ∪ K₂) ∧
        (∃ x ∈ K₁, 1 / ((i : ℝ) + 1) ≤ infDist x K₂) ∧
        (∃ y ∈ K₂, 1 / ((i : ℝ) + 1) ≤ infDist y K₁)}ᶜ) ∩
      {K : Cont S | ∃ x, (K.1 : Set S) = {x}}ᶜ) := by
    ext K
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, mem_compl_iff, not_not]
    rw [IsPseudoArc, Most.isSnakeLike_iff, Most.isHI_iff, Most.nontrivial_iff]
  rw [e]
  refine (IsGδ.iInter fun i => (isClosed_notCoverable i).isOpen_compl.isGδ).inter
    ((IsGδ.iInter fun i => (isClosed_separated i).isOpen_compl.isGδ).inter
      isClosed_degenerate.isOpen_compl.isGδ)

/-! ### Density: a pseudo-arc near every continuum -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The standard box chain in `E`, along an orthonormal pair `e₁, e₂`: box `j` is
`2j < ⟪x,e₁⟫ < 2j+3`, `0 < ⟪x,e₂⟫ < 1`, and the component orthogonal to `e₁, e₂` of norm `< 1`.
(In the plane this is `stdRect j`.) -/
def stdBox (e₁ e₂ : E) (j : ℕ) : Set E :=
  {x | 2 * (j : ℝ) < inner ℝ x e₁ ∧ inner ℝ x e₁ < 2 * j + 3 ∧ 0 < inner ℝ x e₂ ∧ inner ℝ x e₂ < 1 ∧
    ‖x - (inner ℝ x e₁) • e₁ - (inner ℝ x e₂) • e₂‖ < 1}

/-- A **tame chain** in `E`: the image of the standard box chain under a homeomorphism of `E`
(batch 84's `IsTame`, in `E`). The report may weaken the homeomorphism to an open embedding of
a neighbourhood of the standard strip, recording the change. -/
def IsTameChain {m : ℕ} (D : Chain E m) : Prop :=
  ∃ (e₁ e₂ : E) (_ : Orthonormal ℝ ![e₁, e₂]) (Φ : E ≃ₜ E), ∀ j, D.link j = Φ '' stdBox e₁ e₂ j

namespace Most

/-- The `(e₁, e₂)`-plane of `E`: `(a, b) ↦ a e₁ + b e₂`. -/
def planeMap (e₁ e₂ : E) (p : Pt) : E := p.1 • e₁ + p.2 • e₂

theorem continuous_planeMap (e₁ e₂ : E) : Continuous (planeMap e₁ e₂) :=
  (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

theorem inner_planeMap {e₁ e₂ : E} (h : Orthonormal ℝ ![e₁, e₂]) (p : Pt) :
    inner ℝ (planeMap e₁ e₂ p) e₁ = p.1 ∧ inner ℝ (planeMap e₁ e₂ p) e₂ = p.2 := by
  have h1 : ‖e₁‖ = 1 := by simpa using h.1 0
  have h2 : ‖e₂‖ = 1 := by simpa using h.1 1
  have h12 : inner ℝ e₁ e₂ = 0 := by simpa using h.2 (show (0 : Fin 2) ≠ 1 by decide)
  have h21 : inner ℝ e₂ e₁ = 0 := by rw [real_inner_comm]; exact h12
  have h11 : inner ℝ e₁ e₁ = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have h22 : inner ℝ e₂ e₂ = 1 := by rw [real_inner_self_eq_norm_sq, h2]; norm_num
  simp only [planeMap, inner_add_left, real_inner_smul_left, h11, h12, h21, h22]
  constructor <;> ring

theorem planeMap_injective {e₁ e₂ : E} (h : Orthonormal ℝ ![e₁, e₂]) :
    Function.Injective (planeMap e₁ e₂) := by
  intro p q hpq
  have hp := inner_planeMap h p
  have hq := inner_planeMap h q
  rw [hpq] at hp
  exact Prod.ext (hp.1.symm.trans hq.1) (hp.2.symm.trans hq.2)

theorem planeMap_stdRect {e₁ e₂ : E} (h : Orthonormal ℝ ![e₁, e₂]) (j : ℕ) :
    planeMap e₁ e₂ '' stdRect j ⊆ stdBox e₁ e₂ j := by
  rintro _ ⟨p, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
  obtain ⟨i1, i2⟩ := inner_planeMap h p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [i1]; exact h1
  · rw [i1]; exact h2
  · rw [i2]; exact h3
  · rw [i2]; exact h4
  · rw [i1, i2]
    simp [planeMap]

end Most

/-- **A pseudo-arc inside a tame chain** (batch 84's construction in `E`): a pseudo-arc contained
in the union of the links and meeting every link. (Reshaped: the skeleton's `[CompleteSpace E]`
is dropped, as the proof does not use it.) -/
theorem exists_pseudoArc_in_tameChain {m : ℕ} (hm : 3 ≤ m) (D : Chain E m)
    (hD : IsTameChain D) :
    ∃ h : Set E, IsPseudoArc h ∧ h ⊆ D.union ∧ ∀ j, (h ∩ D.link j).Nonempty := by
  obtain ⟨e₁, e₂, hon, Φ, hΦ⟩ := hD
  obtain ⟨M, hM, hMsub, hMmeet⟩ := exists_pseudoArc_stdRect hm
  set f : Pt → E := fun p => Φ (Most.planeMap e₁ e₂ p) with hf
  have hfc : Continuous f := Φ.continuous.comp (Most.continuous_planeMap e₁ e₂)
  have hfi : Function.Injective f := Φ.injective.comp (Most.planeMap_injective hon)
  have hfib : ∀ x ∈ M, M ∩ f ⁻¹' {f x} = {x} := by
    intro x hx
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => hfi h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
  have hmono : IsMonotoneMap f M (f '' M) := by
    refine ⟨hfc.continuousOn, rfl, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hfib x hx]
    exact isConnected_singleton
  have hproper : ∀ y ∈ f '' M, M ∩ f ⁻¹' {y} ≠ M := by
    rintro _ ⟨x, hx, rfl⟩ e
    rw [hfib x hx] at e
    obtain ⟨a, ha, b, hb, hab⟩ := hM.2.2
    rw [← e] at ha hb
    exact hab (ha.trans hb.symm)
  have himg : ∀ j : Fin m, f '' stdRect j ⊆ D.link j := by
    rintro j _ ⟨p, hp, rfl⟩
    rw [hΦ j]
    exact ⟨_, Most.planeMap_stdRect hon j ⟨p, hp, rfl⟩, rfl⟩
  refine ⟨f '' M, (theorem4_HIC hM hmono hproper).1, ?_, fun j => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hMsub hp)
    exact mem_iUnion.mpr ⟨j, himg j ⟨p, hj, rfl⟩⟩
  · obtain ⟨p, hpM, hpj⟩ := hMmeet j
    exact ⟨f p, ⟨p, hpM, rfl⟩, himg j ⟨p, hpj, rfl⟩⟩

/-- **The geometric lemma** (Bing's broken line and chain of spheres), as a hypothesis: near every
compact continuum `g` of `E` there is a tame chain of small links whose union is within `ε` of `g`
and within `ε` of which `g` lies. (The batch-90 open statement `exists_tame_chain_near`, which
asserted this for `dim E ≥ 2`, was deleted in batch 111; see `LEDGER.md` §2. The weaker form
actually needed is `GeomLemma'` of `Band.lean`; its general case `geomLemma'_of_two_le_rank` is
proved in batch 113, `HPC/Plane/CubeCycle.lean`.) -/
def GeomLemma (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Prop :=
  ∀ g : Set E, Fold.Q78.IsContinuum g → ∀ ε : ℝ, 0 < ε →
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsTameChain D ∧ (∀ j, diam (D.link j) < ε) ∧
      D.union ⊆ thickening ε g ∧ g ⊆ thickening ε D.union

/-- **Density, conditional form** (no open dependency): if the geometric lemma holds in `E`,
every compact continuum is a Hausdorff limit of pseudo-arcs. -/
theorem dense_pseudoArcs_of (hgeo : GeomLemma E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} := by
  rw [Metric.dense_iff]
  intro K r hr
  obtain ⟨m, D, hm, hD, hdiam, hDg, hgD⟩ :=
    hgeo _ ⟨K.1.isCompact, K.2⟩ (r / 3) (by positivity)
  obtain ⟨h, hpa, hhD, hmeet⟩ := exists_pseudoArc_in_tameChain hm D hD
  have hbdd : Bornology.IsBounded D.union := K.1.isCompact.isBounded.thickening.subset hDg
  let H : Cont E := ⟨⟨⟨h, hpa.1.1.1⟩, hpa.1.1.2.nonempty⟩, hpa.1.1.2⟩
  refine ⟨H, ?_, hpa⟩
  rw [mem_ball]
  change hausdorffDist h (K.1 : Set E) < r
  have hle : hausdorffDist h (K.1 : Set E) ≤ 2 * (r / 3) := by
    refine hausdorffDist_le_of_mem_dist (by positivity) (fun x hx => ?_) (fun y hy => ?_)
    · obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp (hDg (hhD hx))
      exact ⟨z, hz, by linarith⟩
    · obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp (hgD hy)
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      obtain ⟨w, hwh, hwj⟩ := hmeet j
      have hlb : Bornology.IsBounded (D.link j) := hbdd.subset (subset_iUnion _ j)
      have hzw : dist z w ≤ diam (D.link j) := dist_le_diam_of_mem hlb hj hwj
      refine ⟨w, hwh, ?_⟩
      calc dist y w ≤ dist y z + dist z w := dist_triangle _ _ _
        _ ≤ 2 * (r / 3) := by linarith [hdiam j]
  linarith

/-- **Theorem 2, conditional form** (no open dependency): if the geometric lemma holds in `E`,
the pseudo-arcs form a dense `G_δ` in `C(E)`. -/
theorem theorem2_HIC_of (hgeo : GeomLemma E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsPseudoArc (K.1 : Set E)} :=
  ⟨dense_pseudoArcs_of hgeo, isGδ_pseudoArcs⟩

end HPC.Plane
