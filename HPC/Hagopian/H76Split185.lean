import HPC.Hagopian.Hagopian84A

/-!
# Batch 185, §5: the case split for `i ≥ 3`

Commission 185 §5 (Hagopian 1976, p. 348: "The proof now breaks down into two cases"). For tight
blocks and `3 ≤ i ≤ m`, the layers `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` each meet a closed side segment.
The route is the commission's, steps 1–6; it does not use the 1984 Lemma 7.

* `layer_nhds_subset_open`: upper semicontinuity of the layers (compactness of `G`).
* `left_layer_not_subset`, `right_layer_not_subset`: step 3 and its mirror.
* `Thm1Setup.layerMeetsSide_of_end`: steps 4–5 (the frontier point is over a side segment).
* `Thm1Setup.IsTightBlocks.left_end_crossing`, `Thm1Setup.IsTightBlocks.right_end_crossing`: step 1
  and its mirror.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Split185

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **Upper semicontinuity of the layers**: if a layer of a minimal admissible `(G, d)` lies in an
open set `U`, so do the layers over an open neighbourhood of its parameter. -/
theorem layer_nhds_subset_open {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    {U : Set M} (hU : IsOpen U) {t : unitInterval} (ht : layer d t ⊆ U) :
    ∃ V : Set unitInterval, IsOpen V ∧ t ∈ V ∧ ∀ s ∈ V, layer d s ⊆ U := by
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hG.isCompact
  set K : Set G := Subtype.val ⁻¹' Uᶜ with hK
  have hKc : IsCompact K := (hU.isClosed_compl.preimage continuous_subtype_val).isCompact
  have hdK : IsClosed (d '' K) := (hKc.image hG.2.1.1).isClosed
  refine ⟨(d '' K)ᶜ, hdK.isOpen_compl, ?_, ?_⟩
  · rintro ⟨g, hg, hgt⟩
    exact hg (ht ⟨g, hgt, rfl⟩)
  · rintro s hs _ ⟨g, hg, rfl⟩
    by_contra hU'
    exact hs ⟨g, hU', hg⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- A component `C` of `G ∩ O` (`O` open) whose irreducible interval is `[u, v]` with `u > 0`: the
layer `d⁻¹(u)` met by `Cl C` does not lie in `O` (commission 185 §5, step 3). Otherwise `d⁻¹[[s, u]]`
lies in `O` for some `s < u` (upper semicontinuity), is a continuum meeting `C`, so lies in `C`,
against `C ⊆ d⁻¹[[u, v]]`. -/
theorem left_layer_not_subset {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    {O : Set M} (hO : IsOpen O) {z : M} (hz : z ∈ G ∩ O) {u v : unitInterval}
    (hCuv : connectedComponentIn (G ∩ O) z ⊆ layerSet d (Icc u v))
    (hmeet : (closure (connectedComponentIn (G ∩ O) z) ∩ layer d u).Nonempty) (hu : 0 < u) :
    ¬ layer d u ⊆ O := by
  intro hsub
  obtain ⟨V, hVo, huV, hV⟩ := layer_nhds_subset_open hG hO hsub
  obtain ⟨l, hlu, hl⟩ := exists_Ioc_subset_of_mem_nhds (hVo.mem_nhds huV) ⟨0, hu⟩
  obtain ⟨s, hls, hsu⟩ := exists_between hlu
  have hsub2 : layerSet d (Icc s u) ⊆ G ∩ O := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g.2, hV (d g) (hl ⟨hls.trans_le hg.1, hg.2⟩) ⟨g, rfl, rfl⟩⟩
  have hcont := isContinuum_img hG.isCompact hG.2.1 isClosed_Icc isPreconnected_Icc
    ⟨u, hsu.le, le_rfl⟩
  obtain ⟨w, hwC, ⟨gw, hgw, rfl⟩⟩ := hmeet
  have hwO : (gw : M) ∈ G ∩ O := ⟨gw.2, hsub ⟨gw, hgw, rfl⟩⟩
  have hwCC : (gw : M) ∈ connectedComponentIn (G ∩ O) z :=
    mem_component_of_mem_closure_in hz hwO hwC
  have hwL : (gw : M) ∈ layerSet d (Icc s u) := by
    refine ⟨gw, ?_, rfl⟩
    have : d gw = u := hgw
    rw [mem_preimage, this]; exact ⟨hsu.le, le_rfl⟩
  have hLC : layerSet d (Icc s u) ⊆ connectedComponentIn (G ∩ O) z := by
    rw [connectedComponentIn_eq hwCC]
    exact hcont.2.isPreconnected.subset_connectedComponentIn hwL hsub2
  obtain ⟨g, hg⟩ := hG.2.1.2.1 s
  have hgL : (g : M) ∈ layerSet d (Icc s u) := ⟨g, by rw [mem_preimage, hg]; exact ⟨le_rfl, hsu.le⟩,
    rfl⟩
  obtain ⟨g', hg', hgg⟩ := hCuv (hLC hgL)
  have : g' = g := Subtype.ext hgg
  rw [this, mem_preimage, hg] at hg'
  exact absurd hg'.1 (not_le.2 hsu)

omit [CompactSpace M] [ConnectedSpace M] in
/-- **The mirror of step 3**: the layer `d⁻¹(v)` at the right end `v < 1` does not lie in `O`. -/
theorem right_layer_not_subset {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    {O : Set M} (hO : IsOpen O) {z : M} (hz : z ∈ G ∩ O) {u v : unitInterval}
    (hCuv : connectedComponentIn (G ∩ O) z ⊆ layerSet d (Icc u v))
    (hmeet : (closure (connectedComponentIn (G ∩ O) z) ∩ layer d v).Nonempty) (hv : v < 1) :
    ¬ layer d v ⊆ O := by
  intro hsub
  obtain ⟨V, hVo, hvV, hV⟩ := layer_nhds_subset_open hG hO hsub
  obtain ⟨l, hvl, hl⟩ := exists_Ico_subset_of_mem_nhds (hVo.mem_nhds hvV) ⟨1, hv⟩
  obtain ⟨s, hvs, hsl⟩ := exists_between hvl
  have hsub2 : layerSet d (Icc v s) ⊆ G ∩ O := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g.2, hV (d g) (hl ⟨hg.1, hg.2.trans_lt hsl⟩) ⟨g, rfl, rfl⟩⟩
  have hcont := isContinuum_img hG.isCompact hG.2.1 isClosed_Icc isPreconnected_Icc
    ⟨v, le_rfl, hvs.le⟩
  obtain ⟨w, hwC, ⟨gw, hgw, rfl⟩⟩ := hmeet
  have hwO : (gw : M) ∈ G ∩ O := ⟨gw.2, hsub ⟨gw, hgw, rfl⟩⟩
  have hwCC : (gw : M) ∈ connectedComponentIn (G ∩ O) z :=
    mem_component_of_mem_closure_in hz hwO hwC
  have hwL : (gw : M) ∈ layerSet d (Icc v s) := by
    refine ⟨gw, ?_, rfl⟩
    have : d gw = v := hgw
    rw [mem_preimage, this]; exact ⟨le_rfl, hvs.le⟩
  have hLC : layerSet d (Icc v s) ⊆ connectedComponentIn (G ∩ O) z := by
    rw [connectedComponentIn_eq hwCC]
    exact hcont.2.isPreconnected.subset_connectedComponentIn hwL hsub2
  obtain ⟨g, hg⟩ := hG.2.1.2.1 s
  have hgL : (g : M) ∈ layerSet d (Icc v s) := ⟨g, by rw [mem_preimage, hg]; exact ⟨hvs.le, le_rfl⟩,
    rfl⟩
  obtain ⟨g', hg', hgg⟩ := hCuv (hLC hgL)
  have : g' = g := Subtype.ext hgg
  rw [this, mem_preimage, hg] at hg'
  exact absurd hg'.2 (not_le.2 hvs)

/-- The set `O = M ∩ π⁻¹[D]`, as a subset of `M`; `crossSet G π F D' = G ∩ O`. -/
theorem Thm1Setup.isOpen_O (S : Thm1Setup M) :
    IsOpen {m : M | S.π (m : Pt) ∈ S.F '' S.D'} :=
  S.hR.isOpen.preimage (S.hπ.continuous.comp continuous_subtype_val)

/-- **Steps 4–5** (commission 185 §5): a layer `d⁻¹(t)` met by the closure of a crossing component,
not inside `π⁻¹[D]`, and missing `E`, meets a closed side segment. It meets `Fr O` (connectedness);
`Fr D` over `M` lies over the bottom edge or a side segment (`IsCrossRegion.frontier_sub`, which
excludes `I₂`); a point over the bottom edge is in `E` (`mem_E_of_axis`). -/
theorem Thm1Setup.layerMeetsSide_of_end (S : Thm1Setup M) {C : Set M}
    (hC : IsCrossingComponent S.D.G S.π S.F S.c₁ S.D' C) {t : unitInterval}
    (hmeet : (closure C ∩ layer S.D.d t).Nonempty)
    (hnot : ¬ layer S.D.d t ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'})
    (hE : Disjoint (layer S.D.d t) S.E) :
    ∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide t a := by
  set f : M → Pt := fun m => S.π (m : Pt) with hf
  have hfc : Continuous f := S.hπ.continuous.comp continuous_subtype_val
  set D := S.F '' S.D' with hD
  have hDo : IsOpen D := S.hR.isOpen
  -- the layer is connected
  have hLc : IsPreconnected (layer S.D.d t) :=
    (S.D.hG.2.1.2.2 t).isPreconnected.image _ continuous_subtype_val.continuousOn
  -- a point of the layer over `Fr D`
  have hfr : ∃ p ∈ layer S.D.d t, f p ∈ frontier D := by
    obtain ⟨w, hwC, hwL⟩ := hmeet
    have hCD : C ⊆ f ⁻¹' D := fun m hm => (hC.subset hm).2
    have hwcl : f w ∈ closure D :=
      closure_minimal (hCD.trans (preimage_mono subset_closure))
        (isClosed_closure.preimage hfc) hwC
    by_cases hwD : f w ∈ D
    · obtain ⟨z, hzL, hzO⟩ := not_subset.1 hnot
      by_cases hzc : f z ∈ closure D
      · refine ⟨z, hzL, ?_⟩
        rw [frontier, hDo.interior_eq]; exact ⟨hzc, hzO⟩
      by_contra hno
      push_neg at hno
      have hpc : IsPreconnected (f '' layer S.D.d t) := hLc.image _ hfc.continuousOn
      obtain ⟨y, -, hyD, hyc⟩ := hpc D (closure D)ᶜ hDo isClosed_closure.isOpen_compl
        (by
          rintro _ ⟨p, hpL, rfl⟩
          by_cases hp : f p ∈ D
          · exact Or.inl hp
          · right
            intro hc
            apply hno p hpL
            rw [frontier, hDo.interior_eq]; exact ⟨hc, hp⟩)
        ⟨f w, ⟨w, hwL, rfl⟩, hwD⟩ ⟨f z, ⟨z, hzL, rfl⟩, hzc⟩
      exact hyc (subset_closure hyD)
    · refine ⟨w, hwL, ?_⟩
      rw [frontier, hDo.interior_eq]
      exact ⟨hwcl, hwD⟩
  obtain ⟨p, hpL, hpf⟩ := hfr
  have hpM : f p ∈ S.π '' M := ⟨(p : Pt), p.2, rfl⟩
  rcases S.hR.frontier_sub ⟨hpf, hpM⟩ with (hb | h3) | h19
  · exfalso
    obtain ⟨q, ⟨hq1, hq2⟩, hqp⟩ := hb
    have hq0 : q = (q.1, 0) := Prod.ext rfl hq2
    rw [hq0] at hqp
    have hpE := mem_E_of_axis S.hE S.hπS S.hγπ S.hF
      (⟨by linarith [hq1.1], by linarith [hq1.2]⟩ : q.1 ∈ Icc (0 : ℝ) 1) hqp.symm
    exact disjoint_left.1 hE hpL hpE
  · exact ⟨3 / 22, Or.inl rfl, (p : Pt), ⟨p, hpL, rfl⟩, h3⟩
  · exact ⟨19 / 22, Or.inr rfl, (p : Pt), ⟨p, hpL, rfl⟩, h19⟩

/-- For a block sequence, a layer `d⁻¹(t)` with `t > x₂` misses `E = d⁻¹[[0, x₂]]`. -/
theorem Thm1Setup.IsBlocks.layer_disjoint_E (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) {t : unitInterval} (ht : x 2 < t) : Disjoint (layer S.D.d t) S.E := by
  rw [disjoint_left]
  rintro _ ⟨g, hg, rfl⟩ hgE
  have hgE' : (g : M) ∈ layerSet S.D.d (Icc 0 (x 2)) := by rw [hx.2.2.2.1]; exact hgE
  obtain ⟨g', hg', hgg⟩ := hgE'
  have : g' = g := Subtype.ext hgg
  rw [this, mem_preimage] at hg'
  have hgt : S.D.d g = t := hg
  rw [hgt] at hg'
  exact absurd hg'.2 (not_le.2 ht)

/-- **Step 1** (commission 185 §5): for tight blocks and `2 ≤ i ≤ m`, the left end `x₂ᵢ₋₁` of the
block is the left end of a member of `I`. -/
theorem Thm1Setup.IsTightBlocks.left_end_crossing (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsTightBlocks x m) {i : ℕ} (hi : 2 ≤ i) (him : i ≤ m) :
    ∃ r ∈ crossingIntervals S.D.d S.π S.F S.c₁ S.D', r.1 = x (2 * i - 1) := by
  obtain ⟨hb, ht2, -⟩ := hx
  have hmono := hb.2.1
  have hmem : ∀ j, 1 ≤ j → j ≤ 2 * m → j ∈ Icc 1 (2 * m) := fun j h1 h2 => ⟨h1, h2⟩
  have hle : ∀ a b, 1 ≤ a → b ≤ 2 * m → a ≤ b → x a ≤ x b := fun a b ha hb' hab =>
    (hmono.le_iff_le (hmem a ha (by omega)) (hmem b (by omega) hb')).2 hab
  have hlt : ∀ a b, 1 ≤ a → b ≤ 2 * m → a < b → x a < x b := fun a b ha hb' hab =>
    hmono (hmem a ha (by omega)) (hmem b (by omega) hb') hab
  rcases ht2 i (by omega) him (x (2 * i - 1)) ⟨le_rfl, hle _ _ (by omega) (by omega) (by omega)⟩ with
    h | ⟨r, hr, hr1, hr2⟩
  · exact absurd h (not_le.2 (hlt 2 (2 * i - 1) (by omega) (by omega) (by omega)))
  refine ⟨r, hr, le_antisymm hr1 ?_⟩
  obtain ⟨j, hj1, hjm, hjl, hjr⟩ := hb.2.2.2.2.1 r hr
  rcases Nat.lt_or_ge j i with hji | hji
  · exact absurd (hr2.trans hjr) (not_le.2 (hlt (2 * j) (2 * i - 1) (by omega) (by omega)
      (by omega)))
  · exact (hle (2 * i - 1) (2 * j - 1) (by omega) (by omega) (by omega)).trans hjl

/-- **Step 6, the mirror of step 1**: for tight blocks and `3 ≤ i ≤ m`, the right end `x₂ᵢ₋₂` of the
block `J` is the right end of a member of `I`. -/
theorem Thm1Setup.IsTightBlocks.right_end_crossing (S : Thm1Setup M) {x : ℕ → unitInterval}
    {m : ℕ} (hx : S.IsTightBlocks x m) {i : ℕ} (hi : 3 ≤ i) (him : i ≤ m) :
    ∃ r ∈ crossingIntervals S.D.d S.π S.F S.c₁ S.D', r.2 = x (2 * i - 2) := by
  obtain ⟨hb, ht2, -⟩ := hx
  have hmono := hb.2.1
  have hmem : ∀ j, 1 ≤ j → j ≤ 2 * m → j ∈ Icc 1 (2 * m) := fun j h1 h2 => ⟨h1, h2⟩
  have hle : ∀ a b, 1 ≤ a → b ≤ 2 * m → a ≤ b → x a ≤ x b := fun a b ha hb' hab =>
    (hmono.le_iff_le (hmem a ha (by omega)) (hmem b (by omega) hb')).2 hab
  have hlt : ∀ a b, 1 ≤ a → b ≤ 2 * m → a < b → x a < x b := fun a b ha hb' hab =>
    hmono (hmem a ha (by omega)) (hmem b (by omega) hb') hab
  have e1 : 2 * (i - 1) = 2 * i - 2 := by omega
  have e2 : 2 * (i - 1) - 1 = 2 * i - 3 := by omega
  have h := ht2 (i - 1) (by omega) (by omega) (x (2 * i - 2))
    (by rw [e2, e1]; exact ⟨hle _ _ (by omega) (by omega) (by omega), le_rfl⟩)
  rcases h with h | ⟨r, hr, hr1, hr2⟩
  · exact absurd h (not_le.2 (hlt 2 (2 * i - 2) (by omega) (by omega) (by omega)))
  refine ⟨r, hr, le_antisymm ?_ hr2⟩
  obtain ⟨j, hj1, hjm, hjl, hjr⟩ := hb.2.2.2.2.1 r hr
  rcases Nat.lt_or_ge j i with hji | hji
  · exact hjr.trans (hle (2 * j) (2 * i - 2) (by omega) (by omega) (by omega))
  · exact absurd (hjl.trans hr1) (not_le.2 (hlt (2 * i - 2) (2 * j - 1) (by omega) (by omega)
      (by omega)))

/-- **Steps 2–5 at the left end** (commission 185 §5): for tight blocks and `2 ≤ i ≤ m`,
`d⁻¹(x₂ᵢ₋₁)` meets a closed side segment. -/
theorem Thm1Setup.leftEndLayerMeetsSide (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsTightBlocks x m) {i : ℕ} (hi : 2 ≤ i) (him : i ≤ m) :
    ∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x (2 * i - 1)) a := by
  have hb := hx.1
  have hmono := hb.2.1
  have hlt : ∀ a b, 1 ≤ a → b ≤ 2 * m → a < b → x a < x b := fun a b ha hb' hab =>
    hmono ⟨ha, by omega⟩ ⟨by omega, hb'⟩ hab
  have hO := S.isOpen_O
  have hcs : crossSet S.D.G S.π S.F S.D' = S.D.G ∩ {m : M | S.π (m : Pt) ∈ S.F '' S.D'} := rfl
  obtain ⟨r, ⟨C, hC, hirr⟩, hr1⟩ := Thm1Setup.IsTightBlocks.left_end_crossing S hx hi him
  have hCG : C ⊆ S.D.G := fun c hc => (hC.subset hc).1
  have hmeet := (hirr.closure_meets S.D.hG hCG hC.isConnected.nonempty).1
  rw [hr1] at hmeet hirr
  have hu0 : 0 < x (2 * i - 1) := by
    rw [← hb.2.2.1]; exact hlt 1 (2 * i - 1) le_rfl (by omega) (by omega)
  have hnot : ¬ layer S.D.d (x (2 * i - 1)) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'} := by
    obtain ⟨⟨z, hz, rfl⟩, -, -⟩ := hC
    rw [hcs] at hz hirr hmeet
    exact left_layer_not_subset S.D.hG hO hz hirr.1 hmeet hu0
  exact S.layerMeetsSide_of_end hC hmeet hnot
    (Thm1Setup.IsBlocks.layer_disjoint_E S hb (hlt 2 (2 * i - 1) (by omega) (by omega) (by omega)))

/-- **`d⁻¹(x₃)` located** (notes E3; commission 185 §5): for tight blocks with `m ≥ 2`, the layer
`d⁻¹(x₃)` meets a closed side segment. -/
theorem Thm1Setup.layer_x3_meets_side (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsTightBlocks x m) (hm : 2 ≤ m) :
    ∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x 3) a :=
  S.leftEndLayerMeetsSide hx le_rfl hm

/-- **§5, the case split for `i ≥ 3`** (commission 185 §5): for tight blocks, `d⁻¹(x₂ᵢ₋₁)` and
`d⁻¹(x₂ᵢ₋₂)` each meet a closed side segment, for `3 ≤ i ≤ m`. -/
theorem Thm1Setup.blockLayersMeetSides3_aux (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsTightBlocks x m) : BlockLayersMeetSides3 S x m := by
  intro i hi3 him
  have hb := hx.1
  have hmono := hb.2.1
  have hlt : ∀ a b, 1 ≤ a → b ≤ 2 * m → a < b → x a < x b := fun a b ha hb' hab =>
    hmono ⟨ha, by omega⟩ ⟨by omega, hb'⟩ hab
  have hO := S.isOpen_O
  have hcs : crossSet S.D.G S.π S.F S.D' = S.D.G ∩ {m : M | S.π (m : Pt) ∈ S.F '' S.D'} := rfl
  constructor
  · exact S.leftEndLayerMeetsSide hx (by omega) him
  · obtain ⟨r, ⟨C, hC, hirr⟩, hr2⟩ := Thm1Setup.IsTightBlocks.right_end_crossing S hx hi3 him
    have hCG : C ⊆ S.D.G := fun c hc => (hC.subset hc).1
    have hmeet := (hirr.closure_meets S.D.hG hCG hC.isConnected.nonempty).2
    rw [hr2] at hmeet hirr
    have hv1 : x (2 * i - 2) < 1 := by
      rw [← hb.2.2.2.2.2]; exact hlt (2 * i - 2) (2 * m) (by omega) le_rfl (by omega)
    have hnot : ¬ layer S.D.d (x (2 * i - 2)) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'} := by
      obtain ⟨⟨z, hz, rfl⟩, -, -⟩ := hC
      rw [hcs] at hz hirr hmeet
      exact right_layer_not_subset S.D.hG hO hz hirr.1 hmeet hv1
    exact S.layerMeetsSide_of_end hC hmeet hnot
      (Thm1Setup.IsBlocks.layer_disjoint_E S hb (hlt 2 (2 * i - 2) (by omega) (by omega) (by omega)))

end Split185

end HPC.Hagopian
