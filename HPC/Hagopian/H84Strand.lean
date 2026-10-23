import HPC.Hagopian.Hagopian84B

/-!
# Batch 187, §3: Lemma 16′ (what Theorem 1 uses of Lemma 16)

Commission 187 §3 (Hagopian 1984, p. 343: "By Lemmas 7 and 16, each element of the decomposition of
`F(Z)` that intersects `⋃𝒫′` is an element of the decomposition of the closure of a component of
`⋃𝒫′`").

* `isOpen_params_meeting`: for an open `V`, the parameters whose layer meets `V` form an open set
  (lower semicontinuity, `lsc_of_minimalAdmissible`).
* `isOpen_params_disjoint`: for a closed `C`, the parameters whose layer misses `C` form an open set
  (compactness).
* `strand_meets_P2_P0`: every strand meets `P 2` and `P 0`.
* `strand_dichotomy`: §3.3.
* `strand_layer_mem_delta_aux`, `not_strand_subset_extension_layer_aux`,
  `strand_layer_of_extension_aux`: §3.2, §3.4, §3.1.
* `strand_end_layer_not_mid`, `hagopian84_lemma16_aux`: the printed Lemma 16 from Lemma 16′
  (commission 187 §3.5).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Params

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- For an open `V`, the parameters whose layer meets `V` form an open set (Lemma 5, lower
semicontinuity). -/
theorem isOpen_params_meeting (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {F : Set M} {d : F → unitInterval} (hd : IsMinimalAdmissible F d) {V : Set M}
    (hV : IsOpen V) : IsOpen {u | (layer d u ∩ V).Nonempty} := by
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hd.isCompact
  have hL := lsc_of_minimalAdmissible hX hi hd
  rw [isOpen_iff_mem_nhds]
  rintro u ⟨_, ⟨w, hw, rfl⟩, hwV⟩
  have hw' : d w = u := hw
  obtain ⟨W, hWo, hWc, hW⟩ := hL w w (show d w = d w from rfl) (Subtype.val ⁻¹' V)
    (hV.preimage continuous_subtype_val) hwV
  have hcl : IsClosed (d '' Wᶜ) := (hWo.isClosed_compl.isCompact.image hd.2.1.1).isClosed
  have hu : u ∉ d '' Wᶜ := by
    rintro ⟨z, hz, hzu⟩
    exact hz (hWc (show d z = d w by rw [hzu, hw']))
  filter_upwards [hcl.isOpen_compl.mem_nhds hu] with u' hu'
  obtain ⟨z, hz⟩ := hd.2.1.2.1 u'
  have hzW : z ∈ W := by
    by_contra h
    exact hu' ⟨z, h, hz⟩
  obtain ⟨v, hv1, hv2⟩ := hW z hzW
  have hv1' : d v = d z := hv1
  exact ⟨v.1, ⟨v, show d v = u' by rw [hv1', hz], rfl⟩, hv2⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- For a closed `C`, the parameters whose layer misses `C` form an open set. -/
theorem isOpen_params_disjoint {F : Set M} {d : F → unitInterval} (hd : IsMinimalAdmissible F d)
    {C : Set M} (hC : IsClosed C) : IsOpen {u | Disjoint (layer d u) C} := by
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hd.isCompact
  have hcl : IsClosed (d '' {v : F | v.1 ∈ C}) :=
    ((hC.preimage continuous_subtype_val).isCompact.image hd.2.1.1).isClosed
  convert hcl.isOpen_compl using 1
  ext u
  simp only [mem_setOf_eq, mem_compl_iff, mem_image, not_exists, not_and]
  constructor
  · intro h v hv hvu
    exact disjoint_left.1 h ⟨v, hvu, rfl⟩ hv
  · intro h
    rw [disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ hvC
    exact h v hvC hv

omit [CompactSpace M] [ConnectedSpace M] in
/-- For a closed `C`, the parameters whose layer meets `C` form a closed set. -/
theorem isClosed_params_meeting {F : Set M} {d : F → unitInterval} (hd : IsMinimalAdmissible F d)
    {C : Set M} (hC : IsClosed C) : IsClosed {u | (layer d u ∩ C).Nonempty} := by
  convert (isOpen_params_disjoint hd hC).isClosed_compl using 1
  ext u
  simp only [mem_setOf_eq, mem_compl_iff, not_disjoint_iff_nonempty_inter]

end Params

section Strand

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- Every strand meets `P 2` and `P 0`. -/
theorem strand_meets_P2_P0 {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hr : IsRegular5 P) {z : M} (hz : z ∈ midUnion P) :
    (closure (connectedComponentIn (midUnion P) z) ∩ P 2).Nonempty ∧
      (closure (connectedComponentIn (midUnion P) z) ∩ P 0).Nonempty := by
  obtain ⟨c, hc, hcs⟩ := hr z hz
  obtain ⟨a, b, hab, h⟩ := exists_interval_in_P2 hP hn hc hcs
  obtain ⟨p, hp⟩ := layer_nonempty' hc.2.1 a
  obtain ⟨q, hq⟩ := layer_nonempty' hc.2.1 0
  exact ⟨⟨p, layer_subset_set c a hp, (h a ⟨le_rfl, hab.le⟩).1 hp⟩,
    ⟨q, layer_subset_set c 0 hq, (hcs.2.1 hq).1⟩⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- A layer of a strand through a point of `midUnion P` lies in `midUnion P`. -/
theorem strand_layer_subset_mid {P : Fin 5 → Set M} (hP : IsChain5 P) {G : Set M}
    {c : G → unitInterval} (hc : IsMinimalAdmissible G c) (hcs : RunsStraight c P)
    {t : unitInterval} {y : M} (hy : y ∈ layer c t) (hym : y ∈ midUnion P) :
    layer c t ⊆ midUnion P := by
  rcases hym with (h | h) | h
  · exact (layer_subset_link hc.2.1 hP.isOpen hcs ⟨y, hy, h⟩).trans
      fun z hz => Or.inl (Or.inl hz)
  · exact (layer_subset_link hc.2.1 hP.isOpen hcs ⟨y, hy, h⟩).trans
      fun z hz => Or.inl (Or.inr hz)
  · exact (layer_subset_link hc.2.1 hP.isOpen hcs ⟨y, hy, h⟩).trans fun z hz => Or.inr hz

/-- **§3.3, the dichotomy.** `(F, d)` type λ with `d⁻¹(0)` missing `midUnion P`; `y ∈ d⁻¹(u)` a
point of `midUnion P`; `c` a minimal admissible map of the strand through `y` running straight
through `𝒫`.
Then `d⁻¹(u)` is a layer of `c`, or the strand lies in `d⁻¹(u)`. -/
theorem strand_dichotomy (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) {F : Set M} {d : F → unitInterval}
    (hd : IsMinimalAdmissible F d) (hd0 : Disjoint (layer d 0) (midUnion P)) {u : unitInterval}
    {y : M} (hy : y ∈ layer d u) (hym : y ∈ midUnion P)
    {c : closure (connectedComponentIn (midUnion P) y) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) y)) c)
    (hcs : RunsStraight c P) :
    (∃ t, layer d u = layer c t) ∨ closure (connectedComponentIn (midUnion P) y) ⊆ layer d u := by
  have hyG : y ∈ closure (connectedComponentIn (midUnion P) y) :=
    subset_closure (mem_connectedComponentIn hym)
  let w : closure (connectedComponentIn (midUnion P) y) := ⟨y, hyG⟩
  let s := c w
  have hys : y ∈ layer c s := mem_layer_self84 c w
  have hs0 : 0 < s := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h => ?_
    exact endlayers_not_mid hP hcs (Or.inl (h ▸ hys)) hym
  have hs1 : s < 1 := by
    refine lt_of_le_of_ne unitInterval.le_one' fun h => ?_
    exact endlayers_not_mid hP hcs (Or.inr (h ▸ hys)) hym
  have hYm : layer c s ⊆ midUnion P := strand_layer_subset_mid hP hc hcs hys hym
  have hFc : Fold.Q78.IsContinuum F := hd.1.choose_spec.choose_spec.1
  have hyF : y ∈ F := layer_subset_set d u hy
  by_cases h2 : ∃ p ∈ F ∩ closure (connectedComponentIn (midUnion P) y), p ∉ layer c s
  · obtain ⟨p, ⟨hpF, hpG⟩, hps⟩ := h2
    have h2' : ∃ t₁ t₂, t₁ ≠ t₂ ∧
        ((closure (connectedComponentIn (midUnion P) y) ∩ F) ∩ layer c t₁).Nonempty ∧
        ((closure (connectedComponentIn (midUnion P) y) ∩ F) ∩ layer c t₂).Nonempty :=
      ⟨s, c ⟨p, hpG⟩, fun h => hps (h ▸ mem_layer_self84 c ⟨p, hpG⟩), ⟨y, ⟨hyG, hyF⟩, hys⟩,
        ⟨p, ⟨hpG, hpF⟩, mem_layer_self84 _ _⟩⟩
    rcases layers_agree hX hi hc hd h2' with ⟨v, hv⟩ | ⟨-, -, hag⟩
    · right
      have : v = u := layer_param_eq (hv hyG) hy
      rw [← this]
      exact hv
    · left
      obtain ⟨r, hr'⟩ := hag u ⟨y, hyG, hy⟩
      exact ⟨r, hr'⟩
  · exfalso
    push_neg at h2
    obtain ⟨v, hv⟩ := layer_nonempty' hd.2.1 0
    refine no_arm_at_interior_layer hX hi hc hs0 hs1 hFc (fun p hp => h2 p hp) ⟨y, hyF, hyG⟩
      fun hFY => ?_
    exact disjoint_left.1 hd0 hv (hYm (hFY (layer_subset_set d 0 hv)))

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§3.2, identification.** For `x ∈ midUnion P ∖ Cl(P 0 ∪ P 4)`, the layer through `x` of the
strand through `x` is a member of `Δ(𝒫)`. Normality is not used. -/
theorem strand_layer_mem_delta_aux {P : Fin 5 → Set M} (hP : IsChain5 P) (hr : IsRegular5 P)
    {x : M} (hx : x ∈ midUnion P) (hx0 : x ∉ closure (P 0 ∪ P 4))
    {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c)
    {t : unitInterval} (hxt : x ∈ layer c t) : layer c t ∈ Delta5 P := by
  refine ⟨⟨x, hx, c, hc, t, rfl⟩, ?_⟩
  obtain ⟨d, hd, hrs⟩ := hr x hx
  obtain ⟨s, hs⟩ := exists_layer_eq_of_minimal hc hd t
  rw [hs] at hxt ⊢
  rw [closure_union, disjoint_union_right]
  exact ⟨layer_disjoint_closure_of_mem hd.2.1 hP.isOpen hrs hxt
      fun h => hx0 (closure_mono subset_union_left h),
    layer_disjoint_closure_of_mem hd.2.1 hP.isOpen hrs hxt
      fun h => hx0 (closure_mono subset_union_right h)⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- By freeness and normality, `Cl P 2 ⊆ midUnion P ∖ Cl(P 0 ∪ P 4)`. -/
theorem closure_P2_subset {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hf : IsFree5 P) {z : M} (hz2 : z ∈ closure (P 2)) :
    z ∈ midUnion P ∧ z ∉ closure (P 0 ∪ P 4) := by
  have hz04 : z ∉ closure (P 0 ∪ P 4) := by
    rw [closure_union]
    rintro (h | h)
    · exact disjoint_left.1 (hn 0 2 (by decide)) h hz2
    · exact disjoint_left.1 (hn 2 4 (by decide)) hz2 h
  refine ⟨?_, hz04⟩
  have hzU : z ∈ ⋃ i, P i := by
    by_contra hzU
    have hfr : z ∈ frontier (⋃ i, P i) :=
      ⟨closure_mono (subset_iUnion P 2) hz2, by rwa [(isOpen_iUnion hP.isOpen).interior_eq]⟩
    exact (hf hfr).2 (closure_mono (fun w hw => Or.inl (Or.inr hw)) hz2)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hzU
  fin_cases i
  · exact absurd (subset_closure (show z ∈ P 0 ∪ P 4 from Or.inl hi)) hz04
  · exact Or.inl (Or.inl hi)
  · exact Or.inl (Or.inr hi)
  · exact Or.inr hi
  · exact absurd (subset_closure (show z ∈ P 0 ∪ P 4 from Or.inr hi)) hz04

/-- **§3.4, the degenerate alternative is impossible.** Route of commission 187 §3.4, with one
simplification: step 3 needs only one point `z` of `d⁻¹(α) ∩ Cl P 2` (a limit of the points `pₙ`,
here obtained from the closedness of the set of parameters whose layer meets `Cl P 2`), not the
Hausdorff limit of the `Zₙ`; Lemma 14 is not used. -/
theorem not_strand_subset_extension_layer_aux (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hf : IsFree5 P) (hr : IsRegular5 P) {F : Set M} {d : F → unitInterval}
    (hd : IsMinimalAdmissible F d) (hd0 : Disjoint (layer d 0) (midUnion P)) {y : M}
    (hy : y ∈ midUnion P) (u₀ : unitInterval) :
    ¬ closure (connectedComponentIn (midUnion P) y) ⊆ layer d u₀ := by
  intro hsub
  have hPo := hP.isOpen
  -- the set `T` of parameters whose layer meets `P 2`
  set T : Set unitInterval := {u | (layer d u ∩ P 2).Nonempty} with hT
  have hTo : IsOpen T := isOpen_params_meeting hX hi hd (hPo 2)
  have hu₀T : u₀ ∈ T := by
    obtain ⟨p, hpG, hp2⟩ := (strand_meets_P2_P0 hP hn hr hy).1
    exact ⟨p, hsub hpG, hp2⟩
  have h0T : (0 : unitInterval) ∉ T := by
    rintro ⟨p, hp, hp2⟩
    exact disjoint_left.1 hd0 hp (Or.inl (Or.inr hp2))
  -- `α = max([0, u₀] ∖ T)`
  set S : Set unitInterval := Icc 0 u₀ \ T with hS
  have hSc : IsCompact S := (isClosed_Icc.sdiff hTo).isCompact
  have hSne : S.Nonempty := ⟨0, ⟨le_rfl, unitInterval.nonneg'⟩, h0T⟩
  obtain ⟨α, hαS, hαmax⟩ := hSc.exists_isGreatest hSne
  have hαT : α ∉ T := hαS.2
  have hαu : α < u₀ := lt_of_le_of_ne hαS.1.2 fun h => hαT (h ▸ hu₀T)
  have hIoc : Ioc α u₀ ⊆ T := fun u hu => by
    by_contra h
    exact not_le.2 hu.1 (hαmax ⟨⟨unitInterval.nonneg', hu.2⟩, h⟩)
  -- thin and spanning parameters
  set Th : Set unitInterval := {u | Disjoint (layer d u) (closure (P 0))} with hTh
  set Sp : Set unitInterval := {u | (layer d u ∩ P 0).Nonempty} with hSp
  have hTho : IsOpen Th := isOpen_params_disjoint hd isClosed_closure
  have hSpo : IsOpen Sp := isOpen_params_meeting hX hi hd (hPo 0)
  have hcov : Ioc α u₀ ⊆ Th ∪ Sp := by
    intro u hu
    obtain ⟨p, hp, hp2⟩ := hIoc hu
    have hpm : p ∈ midUnion P := Or.inl (Or.inr hp2)
    obtain ⟨c, hc, hcs⟩ := hr p hpm
    rcases strand_dichotomy hX hi hP hd hd0 hp hpm hc hcs with ⟨t, ht⟩ | hs
    · left
      show Disjoint _ _
      rw [ht]
      have : layer c t ⊆ P 2 := layer_subset_link hc.2.1 hPo hcs ⟨p, ht ▸ hp, hp2⟩
      exact (hn 0 2 (by decide)).symm.mono_left (this.trans subset_closure)
    · right
      obtain ⟨q, hqG, hq0⟩ := (strand_meets_P2_P0 hP hn hr hpm).2
      exact ⟨q, hs hqG, hq0⟩
  have hdisj : Disjoint Th Sp := by
    rw [disjoint_left]
    rintro u hu ⟨q, hq, hq0⟩
    exact disjoint_left.1 hu hq (subset_closure hq0)
  have hu₀Sp : u₀ ∈ Sp := by
    obtain ⟨q, hqG, hq0⟩ := (strand_meets_P2_P0 hP hn hr hy).2
    exact ⟨q, hsub hqG, hq0⟩
  have hspan : Ioc α u₀ ⊆ Sp :=
    IsPreconnected.subset_right_of_subset_union hTho hSpo hdisj hcov
      ⟨u₀, ⟨hαu, le_rfl⟩, hu₀Sp⟩ isPreconnected_Ioc
  -- passing to the limit `α`
  have hαcl : α ∈ closure (Ioc α u₀) := by
    rw [closure_Ioc hαu.ne]
    exact ⟨le_rfl, hαu.le⟩
  obtain ⟨q, hq, hq0⟩ : (layer d α ∩ closure (P 0)).Nonempty :=
    closure_minimal (fun u hu => by
      obtain ⟨q, hq, hq0⟩ := hspan hu
      exact ⟨q, hq, subset_closure hq0⟩) (isClosed_params_meeting hd isClosed_closure) hαcl
  obtain ⟨z, hz, hz2⟩ : (layer d α ∩ closure (P 2)).Nonempty :=
    closure_minimal (fun u hu => by
      obtain ⟨q, hq, hq0⟩ := hIoc hu
      exact ⟨q, hq, subset_closure hq0⟩) (isClosed_params_meeting hd isClosed_closure) hαcl
  obtain ⟨hzm, hz04⟩ := closure_P2_subset hP hn hf hz2
  -- step 4
  obtain ⟨c, hc, hcs⟩ := hr z hzm
  rcases strand_dichotomy hX hi hP hd hd0 hz hzm hc hcs with ⟨t, ht⟩ | hs
  · rw [ht] at hz hq
    exact disjoint_left.1 (layer_disjoint_closure_of_mem hc.2.1 hPo hcs hz
      fun h => hz04 (closure_mono subset_union_left h)) hq hq0
  · obtain ⟨p, hpG, hp2⟩ := (strand_meets_P2_P0 hP hn hr hzm).1
    exact hαT ⟨p, hs hpG, hp2⟩

/-- **§3.1, Lemma 16′.** -/
theorem strand_layer_of_extension_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {F : Set M} {d : F → unitInterval} (hd : IsMinimalAdmissible F d)
    (hd0 : Disjoint (layer d 0) (midUnion P)) {u : unitInterval} {y : M} (hy : y ∈ layer d u)
    (hym : y ∈ midUnion P) :
    ∃ c' : closure (connectedComponentIn (midUnion P) y) → unitInterval,
      IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) y)) c' ∧
        RunsStraight c' P ∧ ∃ t, layer d u = layer c' t := by
  obtain ⟨c, hc, hcs⟩ := hr y hym
  rcases strand_dichotomy hX hi hP hd hd0 hy hym hc hcs with h | h
  · exact ⟨c, hc, hcs, h⟩
  · exact absurd h (not_strand_subset_extension_layer_aux hX hi hP hn hf hr hd hd0 hym u)

end Strand

end HPC.Hagopian

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Lemma16

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- The end layer `c⁻¹(0)` of any minimal admissible map `c` of a strand misses `midUnion P` (it is
an end layer of the map given by regularity, `piece_end_layers`). -/
theorem strand_end_layer_not_mid (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hr : IsRegular5 P) {x : M} (hx : x ∈ midUnion P)
    {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c) :
    Disjoint (layer c 0) (midUnion P) := by
  obtain ⟨c', hc', hcs'⟩ := hr x hx
  haveI : CompactSpace (closure (connectedComponentIn (midUnion P) x)) :=
    isCompact_iff_compactSpace.mp hc'.isCompact
  rcases piece_end_layers hc' (lsc_of_minimalAdmissible hX hi hc') zero_lt_one
      (layerSet_Icc_zero_one c').symm hc with ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [h0, disjoint_left]
    exact fun v hv => endlayers_not_mid hP hcs' (Or.inl hv)
  · rw [h0, disjoint_left]
    exact fun v hv => endlayers_not_mid hP hcs' (Or.inr hv)

/-- **Lemma 16 as printed** (pp. 341–342), from Lemma 16′ (commission 187 §3.5): a layer of `F`
meeting three consecutive links meets `midUnion P`, so it is a layer of a strand running straight
through `𝒫`; such a layer cannot meet both `P i` and `P (i + 2)`. -/
theorem hagopian84_lemma16_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {x : M} (hx : x ∈ midUnion P)
    {c : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (hc : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) c) {F : Set M}
    {d : F → unitInterval} (hd : IsMinimalAdmissible F d) (hd0 : layer d 0 = layer c 0)
    (t : unitInterval) (i : ℕ) (hi3 : i + 2 < 5) :
    ¬ ((layer d t ∩ P ⟨i, by omega⟩).Nonempty ∧ (layer d t ∩ P ⟨i + 1, by omega⟩).Nonempty ∧
      (layer d t ∩ P ⟨i + 2, hi3⟩).Nonempty) := by
  rintro ⟨h₀, ⟨y, hy, hy1⟩, h₂⟩
  have hd0' : Disjoint (layer d 0) (midUnion P) := hd0 ▸ strand_end_layer_not_mid hX hi hP hr hx hc
  have hym : y ∈ midUnion P := by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl (Or.inl hy1)
    · exact Or.inl (Or.inr hy1)
    · exact Or.inr hy1
  obtain ⟨c'', hc'', hcs'', s, hs⟩ :=
    strand_layer_of_extension_aux hX hi hP hn hf hr hd hd0' hy hym
  rw [hs] at h₀ h₂
  have hA := layer_subset_link hc''.2.1 hP.isOpen hcs'' h₀
  have hB := layer_subset_link hc''.2.1 hP.isOpen hcs'' h₂
  obtain ⟨z, hz, -⟩ := h₀
  exact disjoint_left.1 (chain5_disjoint hP ⟨i, by omega⟩ ⟨i + 2, hi3⟩ (by simp)) (hA hz) (hB hz)

end Lemma16

end HPC.Hagopian
