import HPC.Hagopian.Hagopian76AC

/-!
# Batch 186, §4.1 and §4.4: `Δ(𝒫)` is a partition, its distance to `M ∖ ⋃𝒫′`, an interval of layers

Commission 186 §4.1 and §4.4 (Hagopian 1984, p. 341 and p. 344).

* `layer_subset_link`: a layer of a continuum running straight through a chain that meets a
  link lies in it (condition (4) of "runs straight", and connectedness of the layer).
* `layer_disjoint_closure_of_mem`: a layer through a point outside `Cl Pᵢ` misses `Cl Pᵢ`.
* `delta_subset_component`: a member of `Δ(𝒫)` coming from a component `K` lies in `K` (`K ∪ Z` lies
  between `K` and `Cl K`).
* `delta5_partition_aux`, `delta5_dist_pos_aux`, `exists_interval_in_delta_aux`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section LayerBasics

variable {X : Type*} [MetricSpace X]

theorem layer_isPreconnected' {G : Set X} {d : G → unitInterval} (hd : IsAdmissibleMap G d)
    (t : unitInterval) : IsPreconnected (layer d t) :=
  (hd.2.2 t).isPreconnected.image _ continuous_subtype_val.continuousOn

theorem layer_nonempty' {G : Set X} {d : G → unitInterval} (hd : IsAdmissibleMap G d)
    (t : unitInterval) : (layer d t).Nonempty := by
  obtain ⟨x, hx⟩ := hd.2.1 t
  exact ⟨x.1, x, hx, rfl⟩

omit [MetricSpace X] in
theorem layer_subset_set {G : Set X} (d : G → unitInterval) (t : unitInterval) :
    layer d t ⊆ G := by
  rintro _ ⟨w, -, rfl⟩
  exact w.2

omit [MetricSpace X] in
theorem mem_layer_self84 {G : Set X} (d : G → unitInterval) (w : G) : w.1 ∈ layer d (d w) :=
  ⟨w, rfl, rfl⟩

/-- **Uniqueness, layer form**: every layer of one minimal admissible map of `G` is a layer of any
other. -/
theorem exists_layer_eq_of_minimal {G : Set X} {d d' : G → unitInterval}
    (hd : IsMinimalAdmissible G d) (hd' : IsMinimalAdmissible G d') (t : unitInterval) :
    ∃ t', layer d t = layer d' t' := by
  obtain ⟨x, hx⟩ := hd.2.1.2.1 t
  have hu := hagopian75_lemma3_unique hd.1 hd.2.1 hd.2.2 hd'.2.1 hd'.2.2
  refine ⟨d' x, ?_⟩
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hw ⊢
    exact (hu w x).1 (hw.trans hx.symm)
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hw ⊢
    rw [← hx]
    exact (hu w x).2 hw

/-- Two layers of minimal admissible maps of the same set that share a point are equal. -/
theorem layer_eq_of_common_point {G G' : Set X} (hGG' : G = G') {d : G → unitInterval}
    {d' : G' → unitInterval} (hd : IsMinimalAdmissible G d) (hd' : IsMinimalAdmissible G' d')
    {t t' : unitInterval} {z : X} (hz : z ∈ layer d t) (hz' : z ∈ layer d' t') :
    layer d t = layer d' t' := by
  subst hGG'
  obtain ⟨s, hs⟩ := exists_layer_eq_of_minimal hd hd' t
  rw [hs] at hz ⊢
  rw [layer_param_eq hz hz']

end LayerBasics

section Runs

variable {M : Set Pt}

/-- A connected set missing the frontier of an open set `U` and meeting `U` lies in `U`. -/
theorem subset_of_preconnected_meets_open {S U : Set M} (hS : IsPreconnected S) (hU : IsOpen U)
    (hmeet : (S ∩ U).Nonempty) (hfr : Disjoint S (frontier U)) : S ⊆ U := by
  have hcov : S ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · right
      intro hzc
      exact disjoint_left.1 hfr hz ⟨hzc, by rwa [hU.interior_eq]⟩
  rcases hS.subset_or_subset hU isClosed_closure.isOpen_compl
      (disjoint_left.2 fun z hz hz' => hz' (subset_closure hz)) hcov with h | h
  · exact h
  · obtain ⟨z, hzS, hzU⟩ := hmeet
    exact absurd (subset_closure hzU) (h hzS)

/-- **A layer meeting a link lies in it** (running straight, condition (4)). -/
theorem layer_subset_link {G : Set M} {d : G → unitInterval} (hd : IsAdmissibleMap G d)
    {P : Fin 5 → Set M} (hP : ∀ i, IsOpen (P i)) (hrs : RunsStraight d P) {i : Fin 5}
    {t : unitInterval} (h : (layer d t ∩ P i).Nonempty) : layer d t ⊆ P i := by
  by_cases hf : (layer d t ∩ frontier (P i)).Nonempty
  · obtain ⟨z, hzl, hzP⟩ := h
    have := hrs.2.2.2.1 t i hf hzl
    exact absurd (show z ∈ P i ∩ frontier (P i) from ⟨hzP, this⟩)
      (by rw [(hP i).inter_frontier_eq]; exact notMem_empty z)
  · exact subset_of_preconnected_meets_open (layer_isPreconnected' hd t) (hP i) h
      (disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 hf))

/-- **A layer through a point outside `Cl Pᵢ` misses `Cl Pᵢ`.** -/
theorem layer_disjoint_closure_of_mem {G : Set M} {d : G → unitInterval}
    (hd : IsAdmissibleMap G d) {P : Fin 5 → Set M} (hP : ∀ i, IsOpen (P i))
    (hrs : RunsStraight d P) {i : Fin 5} {t : unitInterval} {y : M} (hy : y ∈ layer d t)
    (hyc : y ∉ closure (P i)) : Disjoint (layer d t) (closure (P i)) := by
  rw [disjoint_left]
  intro z hz hzc
  rw [closure_eq_self_union_frontier] at hzc
  rcases hzc with hzP | hzf
  · exact hyc (subset_closure (layer_subset_link hd hP hrs ⟨z, hz, hzP⟩ hy))
  · exact hyc (frontier_subset_closure (hrs.2.2.2.1 t i ⟨z, hz, hzf⟩ hy))

/-- The two outer pairs of links of a chain are disjoint. -/
theorem chain5_disjoint {P : Fin 5 → Set M} (hP : IsChain5 P) (i j : Fin 5)
    (hij : (i : ℕ) + 1 < j) : Disjoint (P i) (P j) := by
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty, hP.inter_iff]
  omega

end Runs

section Delta

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **A member of `Δ(𝒫)` lies in the component it comes from.** Commission 186 §4.1: `K ∪ Z` lies
between `K` and `Cl K`, so it is connected, and it lies in `⋃𝒫′`. -/
theorem delta_subset_component {P : Fin 5 → Set M} (hr : IsRegular5 P) {x : M}
    (hx : x ∈ midUnion P) {Z : Set M} (hZK : Z ⊆ closure (connectedComponentIn (midUnion P) x))
    (hZd : Disjoint Z (closure (P 0 ∪ P 4))) : Z ⊆ connectedComponentIn (midUnion P) x := by
  obtain ⟨d', -, hrs'⟩ := hr x hx
  have hZU : Z ⊆ midUnion P := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hrs'.1 (hZK hz))
    have h04 : z ∉ P 0 ∪ P 4 := fun h => disjoint_left.1 hZd hz (subset_closure h)
    fin_cases i
    · exact absurd (Or.inl hi) h04
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
    · exact absurd (Or.inr hi) h04
  have hpc : IsPreconnected (connectedComponentIn (midUnion P) x ∪ Z) :=
    isPreconnected_connectedComponentIn.subset_closure subset_union_left
      (union_subset subset_closure hZK)
  have := hpc.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hx))
    (union_subset (connectedComponentIn_subset _ _) hZU)
  exact subset_union_right.trans this

omit [CompactSpace M] [ConnectedSpace M] in
/-- Members of `Δ(𝒫)` lie in `(⋃𝒫) ∖ Cl(P 0 ∪ P 4)`. -/
theorem delta_subset_diff {P : Fin 5 → Set M} (hr : IsRegular5 P) {Z : Set M}
    (hZ : Z ∈ Delta5 P) : Z ⊆ (⋃ i, P i) \ closure (P 0 ∪ P 4) := by
  obtain ⟨⟨x, hx, d, hd, t, rfl⟩, hZd⟩ := hZ
  intro z hz
  refine ⟨?_, fun h => disjoint_left.1 hZd hz h⟩
  obtain ⟨d', -, hrs'⟩ := hr x hx
  exact hrs'.1 (layer_subset_set d t hz)

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§4.1** (p. 341): `Δ(𝒫)` is a decomposition of `(⋃𝒫) ∖ Cl(P 0 ∪ P 4)`. Only openness of the
links and regularity are used. -/
theorem delta5_partition_aux {P : Fin 5 → Set M} (hP : ∀ i, IsOpen (P i)) (hr : IsRegular5 P) :
    ⋃₀ Delta5 P = (⋃ i, P i) \ closure (P 0 ∪ P 4) ∧
      ∀ Z ∈ Delta5 P, ∀ Z' ∈ Delta5 P, (Z ∩ Z').Nonempty → Z = Z' := by
  refine ⟨Subset.antisymm (sUnion_subset fun Z hZ => delta_subset_diff hr hZ) ?_, ?_⟩
  · rintro y ⟨hyU, hyc⟩
    have hy0 : y ∉ closure (P 0) := fun h =>
      hyc (closure_mono (subset_union_left (s := P 0) (t := P 4)) h)
    have hy4 : y ∉ closure (P 4) := fun h =>
      hyc (closure_mono (subset_union_right (s := P 0) (t := P 4)) h)
    have hyM : y ∈ midUnion P := by
      obtain ⟨i, hi⟩ := mem_iUnion.1 hyU
      fin_cases i
      · exact absurd (subset_closure hi) hy0
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
      · exact absurd (subset_closure hi) hy4
    obtain ⟨d, hd, hrs⟩ := hr y hyM
    have hyK : y ∈ closure (connectedComponentIn (midUnion P) y) :=
      subset_closure (mem_connectedComponentIn hyM)
    set w : closure (connectedComponentIn (midUnion P) y) := ⟨y, hyK⟩
    refine ⟨layer d (d w), ⟨⟨y, hyM, d, hd, d w, rfl⟩, ?_⟩, mem_layer_self84 d w⟩
    rw [closure_union, disjoint_union_right]
    exact ⟨layer_disjoint_closure_of_mem hd.2.1 hP hrs (mem_layer_self84 d w) hy0,
      layer_disjoint_closure_of_mem hd.2.1 hP hrs (mem_layer_self84 d w) hy4⟩
  · rintro Z ⟨⟨x, hx, d, hd, t, rfl⟩, hZd⟩ Z' ⟨⟨x', hx', d', hd', t', rfl⟩, hZd'⟩ ⟨z, hz, hz'⟩
    have h1 := delta_subset_component hr hx (layer_subset_set d t) hZd hz
    have h2 := delta_subset_component hr hx' (layer_subset_set d' t') hZd' hz'
    have hKK : connectedComponentIn (midUnion P) x = connectedComponentIn (midUnion P) x' := by
      rw [connectedComponentIn_eq h1, connectedComponentIn_eq h2]
    exact layer_eq_of_common_point (congrArg closure hKK) hd hd' hz hz'

omit [CompactSpace M] [ConnectedSpace M] in
/-- `Cl ⋃Δ(𝒫) ⊆ ⋃𝒫′` (commission 186 §4.1, by freeness). -/
theorem closure_delta_subset_mid {P : Fin 5 → Set M} (hP : ∀ i, IsOpen (P i))
    (hf : IsFree5 P) (hr : IsRegular5 P) : closure (⋃₀ Delta5 P) ⊆ midUnion P := by
  have hS := (delta5_partition_aux hP hr).1
  have hSM : ⋃₀ Delta5 P ⊆ midUnion P := by
    rw [hS]
    rintro y ⟨hyU, hyc⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hyU
    fin_cases i
    · exact absurd (subset_closure (show y ∈ P 0 ∪ P 4 from Or.inl hi)) hyc
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
    · exact absurd (subset_closure (show y ∈ P 0 ∪ P 4 from Or.inr hi)) hyc
  intro y hy
  by_cases hyU : y ∈ ⋃ i, P i
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hyU
    have hout : y ∉ P 0 ∪ P 4 := by
      intro h04
      have hO : IsOpen (P 0 ∪ P 4) := (hP 0).union (hP 4)
      obtain ⟨z, hzO, hzS⟩ := mem_closure_iff.1 hy _ hO h04
      rw [hS] at hzS
      exact hzS.2 (subset_closure hzO)
    fin_cases i
    · exact absurd (Or.inl hi) hout
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
    · exact absurd (Or.inr hi) hout
  · exfalso
    have hUo : IsOpen (⋃ i, P i) := isOpen_iUnion hP
    have hfr : y ∈ frontier (⋃ i, P i) := by
      refine ⟨closure_mono (hSM.trans fun z hz => ?_) hy, by rwa [hUo.interior_eq]⟩
      rcases hz with (hz | hz) | hz
      · exact mem_iUnion.2 ⟨1, hz⟩
      · exact mem_iUnion.2 ⟨2, hz⟩
      · exact mem_iUnion.2 ⟨3, hz⟩
    exact (hf hfr).2 (closure_mono hSM hy)

omit [ConnectedSpace M] in
/-- **§4.1, positivity**: the distance from `⋃Δ(𝒫)` to `M ∖ ⋃𝒫′` is positive. Normality is not
used. -/
theorem delta5_dist_pos_aux {P : Fin 5 → Set M} (hP : ∀ i, IsOpen (P i)) (hf : IsFree5 P)
    (hr : IsRegular5 P) :
    ∃ η > 0, ∀ z ∈ ⋃₀ Delta5 P, ∀ y : M, y ∉ midUnion P → η ≤ dist z y := by
  have hcl := closure_delta_subset_mid hP hf hr
  have hMo : IsOpen (midUnion P) := ((hP 1).union (hP 2)).union (hP 3)
  by_cases hc : (midUnion P)ᶜ.Nonempty
  · by_cases hS : (closure (⋃₀ Delta5 P)).Nonempty
    · obtain ⟨z₀, hz₀, hmin⟩ := isClosed_closure.isCompact.exists_isMinOn hS
        (continuous_infDist_pt ((midUnion P)ᶜ)).continuousOn
      refine ⟨infDist z₀ (midUnion P)ᶜ, ?_, fun z hz y hy => ?_⟩
      · show 0 < _
        rw [← infDist_pos_iff_notMem_closure hc, hMo.isClosed_compl.closure_eq]
        exact fun h => h (hcl hz₀)
      · exact (hmin (subset_closure hz)).trans (infDist_le_dist_of_mem hy)
    · refine ⟨1, one_pos, fun z hz => absurd ⟨z, subset_closure hz⟩ hS⟩
  · exact ⟨1, one_pos, fun z _ y hy => absurd ⟨y, hy⟩ hc⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§4.4, an interval of layers inside `P 2`.** A continuum `G` with a minimal admissible map `c`
running straight through the normal chain `𝒫` meets `P 2`; the layer through such a point lies in
`P 2`, so misses `Cl(P 0 ∪ P 4)`; the parameters of the layers inside `P 2` form an open set. -/
theorem exists_interval_in_P2 {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    {G : Set M} {c : G → unitInterval} (hc : IsMinimalAdmissible G c) (hcs : RunsStraight c P) :
    ∃ a b : unitInterval, a < b ∧ ∀ t ∈ Icc a b, layer c t ⊆ P 2 ∧
      Disjoint (layer c t) (closure (P 0 ∪ P 4)) := by
  have hPo := hP.isOpen
  have hd24 := chain5_disjoint hP 2 4 (by decide)
  -- `G` meets `P 2`
  have hG2 : (G ∩ P 2).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hcov : G ⊆ (P 0 ∪ P 1) ∪ (P 3 ∪ P 4) := by
      intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcs.1 hz)
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact absurd (show z ∈ G ∩ P 2 from ⟨hz, hi⟩) (by rw [hne]; exact notMem_empty z)
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr hi)
    have hdisj : Disjoint (P 0 ∪ P 1) (P 3 ∪ P 4) := by
      rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
      exact ⟨⟨chain5_disjoint hP 0 3 (by decide), chain5_disjoint hP 0 4 (by decide)⟩,
        chain5_disjoint hP 1 3 (by decide), chain5_disjoint hP 1 4 (by decide)⟩
    obtain ⟨z0, hz0⟩ := layer_nonempty' hc.2.1 0
    obtain ⟨z1, hz1⟩ := layer_nonempty' hc.2.1 1
    have hz0P : z0 ∈ P 0 := (hcs.2.1 hz0).1
    have hz1P : z1 ∈ P 4 := (hcs.2.2.1 hz1).1
    rcases hc.1.choose_spec.choose_spec.1.2.isPreconnected.subset_or_subset
        ((hPo 0).union (hPo 1)) ((hPo 3).union (hPo 4)) hdisj hcov with h | h
    · exact disjoint_left.1 hdisj (h (layer_subset_set c 1 hz1)) (Or.inr hz1P)
    · exact disjoint_left.1 hdisj (Or.inl hz0P) (h (layer_subset_set c 0 hz0))
  obtain ⟨z, hzG, hz2⟩ := hG2
  -- the set of parameters whose layer lies in `P 2`
  set T : Set unitInterval := {t | layer c t ⊆ P 2} with hT
  have hTo : IsOpen T := by
    haveI : CompactSpace G := isCompact_iff_compactSpace.mp hc.isCompact
    have hcl : IsClosed (c '' {v : G | v.1 ∉ P 2}) :=
      ((isClosed_compl_iff.2 ((hPo 2).preimage continuous_subtype_val)).isCompact.image
        hc.2.1.1).isClosed
    convert hcl.isOpen_compl using 1
    ext t
    simp only [hT, mem_setOf_eq, mem_compl_iff, mem_image, not_exists, not_and]
    constructor
    · intro ht v hv hvt
      exact hv (ht ⟨v, hvt, rfl⟩)
    · rintro ht _ ⟨v, hv, rfl⟩
      by_contra hvP
      exact ht v hvP hv
  have hwT : c ⟨z, hzG⟩ ∈ T :=
    layer_subset_link hc.2.1 hPo hcs ⟨z, mem_layer_self84 c ⟨z, hzG⟩, hz2⟩
  have hw1 : c ⟨z, hzG⟩ < 1 := by
    refine lt_of_le_of_ne unitInterval.le_one' fun h => ?_
    obtain ⟨z1, hz1⟩ := layer_nonempty' hc.2.1 1
    rw [h] at hwT
    exact disjoint_left.1 hd24 (hwT hz1) (hcs.2.2.1 hz1).1
  obtain ⟨l, hl, hsub⟩ := exists_Ico_subset_of_mem_nhds (hTo.mem_nhds hwT) ⟨1, hw1⟩
  obtain ⟨b, hb1, hb2⟩ := exists_between hl
  refine ⟨c ⟨z, hzG⟩, b, hb1, fun t ht => ?_⟩
  have htT : layer c t ⊆ P 2 := hsub ⟨ht.1, ht.2.trans_lt hb2⟩
  refine ⟨htT, ?_⟩
  rw [closure_union, disjoint_union_right]
  exact ⟨(hn 0 2 (by decide)).symm.mono_left (htT.trans subset_closure),
    (hn 2 4 (by decide)).mono_left (htT.trans subset_closure)⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§4.4, the arc** (p. 344): the closure of a component of `⋃𝒫′`, running straight through the
normal chain `𝒫`, has a closed interval of layers in `Δ(𝒫)`. -/
theorem exists_interval_in_delta_aux {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    {x : M} (hx : x ∈ midUnion P)
    {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c)
    (hcs : RunsStraight c P) :
    ∃ a b : unitInterval, a < b ∧ ∀ t ∈ Icc a b, layer c t ∈ Delta5 P := by
  obtain ⟨a, b, hab, h⟩ := exists_interval_in_P2 hP hn hc hcs
  exact ⟨a, b, hab, fun t ht => ⟨⟨x, hx, c, hc, t, rfl⟩, (h t ht).2⟩⟩

end Delta

end HPC.Hagopian
