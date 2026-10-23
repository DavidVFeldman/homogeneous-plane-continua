import HPC.Hagopian.H84Strand

/-!
# Batch 187, §4: the bridge `J(Z)` (Hagopian 1984, p. 343)

Commission 187 §4.

* `layer_subset_closure_link`: a layer of a continuum running straight through `𝒫` that meets
  `Cl P i` lies in `Cl P i`.
* `omega_not_delta_side_aux` (§4.2): a member of `Ω(𝒫) ∖ Δ(𝒫)` lies in `Cl P 0` or in `Cl P 4`, and
  misses `Cl P 2`.
* `meets_P2_of_connects`: a connected subset of `⋃𝒫` meeting `P 0 ∪ P 1` and `P 3 ∪ P 4` meets
  `P 2`.
* `bridge_setup` (§4.1–§4.2): the strand `Cl K(Z)` with `Z` as a layer, oriented so that the end
  layer `X(Z)` over `0` is on the far side of `P 2` from `Z`.
* `exists_ext_meeting_P2` (§4.3): an extension of `Cl K(Z)` away from `X(Z)` meets `P 2 ∖ K(Z)`.
* `exists_bridge84_aux` (§4.4): the bridge.
* `mem_delta_of_bridge_chain_aux` (§5.1): `Z ∈ Δ(𝒫(Z))` for any chain `𝒫(Z)` with Hagopian's (3).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Side

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- A layer of a continuum running straight through `𝒫` that meets `Cl P i` lies in `Cl P i`
(it meets `P i` and lies in it, or meets `Bd P i` and lies in it). -/
theorem layer_subset_closure_link {G : Set M} {d : G → unitInterval} (hd : IsAdmissibleMap G d)
    {P : Fin 5 → Set M} (hP : ∀ i, IsOpen (P i)) (hrs : RunsStraight d P) {i : Fin 5}
    {t : unitInterval} (h : (layer d t ∩ closure (P i)).Nonempty) :
    layer d t ⊆ closure (P i) := by
  obtain ⟨q, hq, hqc⟩ := h
  rw [closure_eq_self_union_frontier] at hqc
  rcases hqc with hqP | hqf
  · exact (layer_subset_link hd hP hrs ⟨q, hq, hqP⟩).trans subset_closure
  · exact (hrs.2.2.2.1 t i ⟨q, hq, hqf⟩).trans frontier_subset_closure

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§4.2**: a member of `Ω(𝒫) ∖ Δ(𝒫)` lies in `Cl P 0` or in `Cl P 4`, and misses `Cl P 2`. -/
theorem omega_not_delta_side_aux {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hr : IsRegular5 P) {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) :
    (Z ⊆ closure (P 0) ∨ Z ⊆ closure (P 4)) ∧ Disjoint Z (closure (P 2)) := by
  obtain ⟨x, hx, d₀, hd₀, t, rfl⟩ := hZ
  obtain ⟨c, hc, hcs⟩ := hr x hx
  obtain ⟨s, hs⟩ := exists_layer_eq_of_minimal hd₀ hc t
  have hmeet : ¬ Disjoint (layer d₀ t) (closure (P 0 ∪ P 4)) := fun h =>
    hZd ⟨⟨x, hx, d₀, hd₀, t, rfl⟩, h⟩
  rw [hs] at hmeet ⊢
  rw [not_disjoint_iff_nonempty_inter, closure_union, inter_union_distrib_left] at hmeet
  have hside : layer c s ⊆ closure (P 0) ∨ layer c s ⊆ closure (P 4) := by
    rcases union_nonempty.1 hmeet with h | h
    · exact Or.inl (layer_subset_closure_link hc.2.1 hP.isOpen hcs h)
    · exact Or.inr (layer_subset_closure_link hc.2.1 hP.isOpen hcs h)
  refine ⟨hside, ?_⟩
  rcases hside with h | h
  · exact (hn 0 2 (by decide)).mono_left h
  · exact (hn 2 4 (by decide)).symm.mono_left h

omit [CompactSpace M] [ConnectedSpace M] in
/-- A connected subset of `⋃𝒫` meeting `P 0 ∪ P 1` and `P 3 ∪ P 4` meets `P 2`. -/
theorem meets_P2_of_connects {P : Fin 5 → Set M} (hP : IsChain5 P) {C : Set M}
    (hC : IsPreconnected C) (hCU : C ⊆ ⋃ i, P i) (h01 : (C ∩ (P 0 ∪ P 1)).Nonempty)
    (h34 : (C ∩ (P 3 ∪ P 4)).Nonempty) : (C ∩ P 2).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hcov : C ⊆ (P 0 ∪ P 1) ∪ (P 3 ∪ P 4) := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hCU hz)
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact absurd (show z ∈ C ∩ P 2 from ⟨hz, hi⟩) (by rw [hne]; exact notMem_empty z)
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  have hdisj : Disjoint (P 0 ∪ P 1) (P 3 ∪ P 4) := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨chain5_disjoint hP 0 3 (by decide), chain5_disjoint hP 0 4 (by decide)⟩,
      chain5_disjoint hP 1 3 (by decide), chain5_disjoint hP 1 4 (by decide)⟩
  have hPo := hP.isOpen
  rcases hC.subset_or_subset ((hPo 0).union (hPo 1)) ((hPo 3).union (hPo 4)) hdisj hcov with
    h | h
  · obtain ⟨z, hzC, hz⟩ := h34
    exact disjoint_left.1 hdisj (h hzC) hz
  · obtain ⟨z, hzC, hz⟩ := h01
    exact disjoint_left.1 hdisj hz (h hzC)

omit [CompactSpace M] [ConnectedSpace M] in
/-- **§4.1–§4.2, the set-up of the bridge.** For `Z ∈ Ω(𝒫) ∖ Δ(𝒫)`: a strand `Cl K` having `Z` as a
layer (§4.1: the component "whose closure has `Z` as a layer"), with a minimal admissible map `e`
whose end layer `X = e⁻¹(0)` misses `midUnion P` and lies on the far side of `P 2` from `Z`: every
connected subset of `⋃𝒫` meeting `X` and `Z` meets `P 2` (§4.2: `X(Z)` is the end layer on the
other side). -/
theorem bridge_setup {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P)
    (hr : IsRegular5 P) {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) :
    ∃ x ∈ midUnion P, ∃ e : closure (connectedComponentIn (midUnion P) x) → unitInterval,
      IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) e ∧
      Disjoint (layer e 0) (midUnion P) ∧ (∃ z, Z = layer e z) ∧
      ∀ C, IsPreconnected C → C ⊆ ⋃ i, P i → (C ∩ layer e 0).Nonempty → (C ∩ Z).Nonempty →
        (C ∩ P 2).Nonempty := by
  obtain ⟨hside, -⟩ := omega_not_delta_side_aux hP hn hr hZ hZd
  obtain ⟨x, hx, d₀, hd₀, t, rfl⟩ := hZ
  obtain ⟨c, hc, hcs⟩ := hr x hx
  obtain ⟨s, hs⟩ := exists_layer_eq_of_minimal hd₀ hc t
  rw [hs] at hside ⊢
  have hZU : layer c s ⊆ ⋃ i, P i := (layer_subset_set c s).trans hcs.1
  rcases hside with h0 | h4
  · -- `Z` near `P 0`: reverse `c`, so that `X = c⁻¹(1) ⊆ P 4`
    refine ⟨x, hx, unitInterval.symm ∘ c, hc.symm_comp, ?_,
      ⟨unitInterval.symm s, by rw [layer_symm_comp, unitInterval.symm_symm]⟩, ?_⟩
    · rw [layer_symm_comp, unitInterval.symm_zero, disjoint_left]
      intro v hv
      exact endlayers_not_mid hP hcs (Or.inr hv)
    · intro C hC hCU hXC hZC
      rw [layer_symm_comp, unitInterval.symm_zero] at hXC
      refine meets_P2_of_connects hP hC hCU ?_ ?_
      · obtain ⟨z, hzC, hz⟩ := hZC
        refine ⟨z, hzC, ?_⟩
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hZU hz)
        have hz0 := h0 hz
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr hi
        · exact absurd (subset_closure hi) (disjoint_left.1 (hn 0 2 (by decide)) hz0)
        · exact absurd (subset_closure hi) (disjoint_left.1 (hn 0 3 (by decide)) hz0)
        · exact absurd (subset_closure hi) (disjoint_left.1 (hn 0 4 (by decide)) hz0)
      · obtain ⟨z, hzC, hz⟩ := hXC
        exact ⟨z, hzC, Or.inr (hcs.2.2.1 hz).1⟩
  · -- `Z` near `P 4`: keep `c`, so that `X = c⁻¹(0) ⊆ P 0`
    refine ⟨x, hx, c, hc, ?_, ⟨s, rfl⟩, ?_⟩
    · rw [disjoint_left]
      intro v hv
      exact endlayers_not_mid hP hcs (Or.inl hv)
    · intro C hC hCU hXC hZC
      refine meets_P2_of_connects hP hC hCU ?_ ?_
      · obtain ⟨z, hzC, hz⟩ := hXC
        exact ⟨z, hzC, Or.inl (hcs.2.1 hz).1⟩
      · obtain ⟨z, hzC, hz⟩ := hZC
        refine ⟨z, hzC, ?_⟩
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hZU hz)
        have hz4 := h4 hz
        fin_cases i
        · exact absurd (subset_closure hi) (disjoint_left.1 (hn 0 4 (by decide)) · hz4)
        · exact absurd (subset_closure hi) (disjoint_left.1 (hn 1 4 (by decide)) · hz4)
        · exact absurd (subset_closure hi) (disjoint_left.1 (hn 2 4 (by decide)) · hz4)
        · exact Or.inl hi
        · exact Or.inr hi

end Side

section Bridge

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§4.3** ("Thus `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`. Hence there is an element `F(Z)` of
`𝔖(X(Z), Cl K(Z))` that intersects `P₃∖K(Z)`"). Route of commission 187 §4.3: otherwise
`P 2 ∩ Cl R` is a nonempty open subset of the indecomposable `Cl R` (Lemma 11) inside its proper
subcontinuum `Cl K` (Lemma 4 makes extensions strict). -/
theorem exists_ext_meeting_P2 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P) {x : M}
    (hx : x ∈ midUnion P) {e : closure (connectedComponentIn (midUnion P) x) → unitInterval}
    (he : IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) x)) e) :
    ∃ F, IsExtensionAway (closure (connectedComponentIn (midUnion P) x)) (layer e 0) F ∧
      (F ∩ (P 2 \ connectedComponentIn (midUnion P) x)).Nonempty := by
  by_contra hno
  push_neg at hno
  set R := extUnion (closure (connectedComponentIn (midUnion P) x)) (layer e 0) with hR
  have hind := hagopian84_lemma11 hX hi he
  have hRP : R ∩ P 2 ⊆ connectedComponentIn (midUnion P) x := by
    rintro p ⟨⟨F, hF, hpF⟩, hp2⟩
    by_contra hpK
    have := hno F hF
    rw [← not_nonempty_iff_eq_empty] at this
    exact this ⟨p, hpF, hp2, hpK⟩
  have hGR : closure (connectedComponentIn (midUnion P) x) ⊆ R := fun p hp =>
    ⟨closure (connectedComponentIn (midUnion P) x), ⟨subset_rfl, e, he, rfl⟩, hp⟩
  obtain ⟨H, hH, hGH⟩ :=
    (hagopian76_lemma4 hX hi he).2 (closure (connectedComponentIn (midUnion P) x))
      ⟨subset_rfl, e, he, rfl⟩
  have hne : closure (connectedComponentIn (midUnion P) x) ≠ closure R := by
    intro h
    obtain ⟨p, hpH, hpG⟩ := exists_of_ssubset hGH
    exact hpG (h ▸ subset_closure ⟨H, hH, hpH⟩)
  obtain ⟨p, hpG, hp2⟩ := (strand_meets_P2_P0 hP hn hr hx).1
  exact HPC.T13.false_of_interior hind he.1.choose_spec.choose_spec.1
    (hGR.trans subset_closure) hne (hP.isOpen 2) ⟨p, hp2, subset_closure (hGR hpG)⟩
    fun q hq => closure_mono (fun w hw => hRP ⟨hw.2, hw.1⟩) ((hP.isOpen 2).inter_closure hq)

/-- **§4.4, the bridge.** Route of commission 187 §4.4, with two simplifications.
* The right end: `u*` is the least parameter `≥ z₀` (not `> c₀`) whose layer meets `Cl P 2`. So the
  added clause "the two end layers lie in different components" is not claimed.
* The layers near `m₂` and `u*` are in `Δ(𝒫)` by Lemma 16′ and the openness of the parameters whose
  layer lies in `midUnion P` and misses `Cl(P 0 ∪ P 4)` (upper semicontinuity); `translate_run` is
  not needed. -/
theorem exists_bridge84_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hf : IsFree5 P) (hr : IsRegular5 P)
    {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) :
    ∃ (J : Set M) (j : J → unitInterval), IsMinimalAdmissible J j ∧ (∃ t, Z = layer j t) ∧
      Disjoint J (closure (P 2)) ∧ layer j 0 ∈ Delta5 P ∧ layer j 1 ∈ Delta5 P ∧
      ∀ u, (layer j u ∩ midUnion P).Nonempty → ∃ y ∈ midUnion P,
        ∃ c' : closure (connectedComponentIn (midUnion P) y) → unitInterval,
          IsMinimalAdmissible (closure (connectedComponentIn (midUnion P) y)) c' ∧
            ∃ t, layer j u = layer c' t := by
  have hPo := hP.isOpen
  have hZcl2 : Disjoint Z (closure (P 2)) := (omega_not_delta_side_aux hP hn hr hZ hZd).2
  obtain ⟨x, hx, e, he, he0, ⟨z, rfl⟩, hsep⟩ := bridge_setup hP hn hr hZ hZd
  obtain ⟨c, hc, hcs⟩ := hr x hx
  have hGU : closure (connectedComponentIn (midUnion P) x) ⊆ ⋃ i, P i := hcs.1
  -- §4.3: the extension `F`
  obtain ⟨F, ⟨hGF, d, hd, hdX⟩, hFP⟩ := exists_ext_meeting_P2 hX hi hP hn hr hx he
  have hd0 : Disjoint (layer d 0) (midUnion P) := hdX ▸ he0
  -- every layer of `e` is a layer of `d`
  have hlay : ∀ r, ∃ u, layer e r = layer d u := by
    obtain ⟨p, hp⟩ := layer_nonempty' he.2.1 0
    obtain ⟨q, hq⟩ := layer_nonempty' he.2.1 1
    have h2 : ∃ t₁ t₂, t₁ ≠ t₂ ∧
        ((closure (connectedComponentIn (midUnion P) x) ∩ F) ∩ layer e t₁).Nonempty ∧
        ((closure (connectedComponentIn (midUnion P) x) ∩ F) ∩ layer e t₂).Nonempty :=
      ⟨0, 1, zero_ne_one, ⟨p, ⟨layer_subset_set e 0 hp, hGF (layer_subset_set e 0 hp)⟩, hp⟩,
        ⟨q, ⟨layer_subset_set e 1 hq, hGF (layer_subset_set e 1 hq)⟩, hq⟩⟩
    rcases layers_agree hX hi he hd h2 with ⟨v, hv⟩ | ⟨-, hag, -⟩
    · exfalso
      have hp' : p ∈ layer d 0 := by rw [hdX]; exact hp
      have hv0 : v = 0 := layer_param_eq (hv (layer_subset_set e 0 hp)) hp'
      have hq0 : q ∈ layer e 0 := by
        rw [← hdX, ← hv0]
        exact hv (layer_subset_set e 1 hq)
      exact zero_ne_one (layer_param_eq hq0 hq)
    · intro r
      obtain ⟨p, hp⟩ := layer_nonempty' he.2.1 r
      exact hag r ⟨p, hGF (layer_subset_set e r hp), hp⟩
  obtain ⟨z₀, hz₀⟩ := hlay z
  -- the strand inside `d⁻¹[0, s]`, `d⁻¹[0, s) ⊆` the strand
  obtain ⟨s, -, hsG, hGs, -, -⟩ := lemma4_layers_aux he hd hGF hdX
  have hparG : ∀ w : F, d w < s → w.1 ∈ closure (connectedComponentIn (midUnion P) x) := fun w hw =>
    hsG ⟨w, ⟨unitInterval.nonneg', hw⟩, rfl⟩
  have hGpar : ∀ w : F, w.1 ∈ closure (connectedComponentIn (midUnion P) x) → d w ≤ s := by
    intro w hw
    obtain ⟨w', hw', hww'⟩ := hGs hw
    have : w' = w := Subtype.ext hww'
    subst this
    exact hw'.2
  have hz₀s : z₀ ≤ s := by
    obtain ⟨p, hp⟩ := layer_nonempty' hd.2.1 z₀
    have hpG : p ∈ closure (connectedComponentIn (midUnion P) x) :=
      layer_subset_set e z (by rw [hz₀]; exact hp)
    obtain ⟨w, hw, rfl⟩ := hp
    have hw' : d w = z₀ := hw
    rw [← hw']
    exact hGpar w hpG
  have hleG : ∀ w : F, d w ≤ z₀ → w.1 ∈ closure (connectedComponentIn (midUnion P) x) := by
    intro w hw
    rcases lt_or_eq_of_le (hw.trans hz₀s) with h | h
    · exact hparG w h
    · have hwz : d w = z₀ := le_antisymm hw (h ▸ hz₀s)
      exact layer_subset_set e z (by rw [hz₀]; exact ⟨w, hwz, rfl⟩)
  have hZcl2' : Disjoint (layer d z₀) (closure (P 2)) := hz₀ ▸ hZcl2
  -- the parameters whose layer meets `Cl P 2`
  have hCl2 : IsClosed {u | (layer d u ∩ closure (P 2)).Nonempty} :=
    isClosed_params_meeting hd isClosed_closure
  -- the left side: `m₂`
  set A : Set unitInterval := Iic z₀ ∩ {u | (layer d u ∩ closure (P 2)).Nonempty} with hA
  have hAc : IsCompact A := (isClosed_Iic.inter hCl2).isCompact
  have hAne : A.Nonempty := by
    set C := layerSet d (Icc 0 z₀) with hC
    have hCc : Fold.Q78.IsContinuum C :=
      isContinuum_img hd.isCompact hd.2.1 isClosed_Icc isPreconnected_Icc
        ⟨0, le_rfl, unitInterval.nonneg'⟩
    have hCG : C ⊆ closure (connectedComponentIn (midUnion P) x) := by
      rintro _ ⟨w, hw, rfl⟩
      exact hleG w hw.2
    obtain ⟨p, hp⟩ := layer_nonempty' hd.2.1 0
    obtain ⟨q, hq⟩ := layer_nonempty' hd.2.1 z₀
    have hpC : p ∈ C := by
      obtain ⟨w, hw, rfl⟩ := hp
      have hw' : d w = 0 := hw
      exact ⟨w, ⟨hw'.ge, by rw [hw']; exact unitInterval.nonneg'⟩, rfl⟩
    have hqC : q ∈ C := by
      obtain ⟨w, hw, rfl⟩ := hq
      have hw' : d w = z₀ := hw
      exact ⟨w, ⟨unitInterval.nonneg', hw'.le⟩, rfl⟩
    obtain ⟨y, ⟨w, hw, rfl⟩, hy2⟩ := hsep C hCc.2.isPreconnected (hCG.trans hGU)
      ⟨p, hpC, by rw [← hdX]; exact hp⟩ ⟨q, hqC, by rw [hz₀]; exact hq⟩
    exact ⟨d w, hw.2, w.1, mem_layer_self84 d w, subset_closure hy2⟩
  obtain ⟨m₂, hm₂A, hm₂max⟩ := hAc.exists_isGreatest hAne
  have hm₂z : m₂ < z₀ := by
    refine lt_of_le_of_ne hm₂A.1 fun h => ?_
    obtain ⟨y, hy, hy2⟩ := hm₂A.2
    rw [h] at hy
    exact disjoint_left.1 hZcl2' hy hy2
  -- the right side: `u*`
  set B : Set unitInterval := Ici z₀ ∩ {u | (layer d u ∩ closure (P 2)).Nonempty} with hB
  have hBc : IsCompact B := (isClosed_Ici.inter hCl2).isCompact
  have hBne : B.Nonempty := by
    obtain ⟨p, hpF, hp2, hpK⟩ := hFP
    set w : F := ⟨p, hpF⟩
    refine ⟨d w, ?_, w.1, mem_layer_self84 d w, subset_closure hp2⟩
    by_contra hlt
    rw [mem_Ici, not_le] at hlt
    have hwG : w.1 ∈ closure (connectedComponentIn (midUnion P) x) := hleG w hlt.le
    set v : closure (connectedComponentIn (midUnion P) x) := ⟨w.1, hwG⟩
    have hl2 : layer c (c v) ⊆ P 2 :=
      layer_subset_link hc.2.1 hPo hcs ⟨w.1, mem_layer_self84 c v, hp2⟩
    have hdisj : Disjoint (layer c (c v)) (closure (P 0 ∪ P 4)) := by
      rw [closure_union, disjoint_union_right]
      exact ⟨(hn 0 2 (by decide)).symm.mono_left (hl2.trans subset_closure),
        (hn 2 4 (by decide)).mono_left (hl2.trans subset_closure)⟩
    exact hpK (delta_subset_component hr hx (layer_subset_set c (c v)) hdisj
      (mem_layer_self84 c v))
  obtain ⟨us, husB, husmin⟩ := hBc.exists_isLeast hBne
  have hzus : z₀ < us := by
    refine lt_of_le_of_ne husB.1 fun h => ?_
    obtain ⟨y, hy, hy2⟩ := husB.2
    rw [← h] at hy
    exact disjoint_left.1 hZcl2' hy hy2
  -- the good parameters
  set Gd : Set unitInterval := {u | Disjoint (layer d u) (midUnion P)ᶜ} ∩
    {u | Disjoint (layer d u) (closure (P 0 ∪ P 4))} with hGd
  have hMo : IsOpen (midUnion P) := ((hPo 1).union (hPo 2)).union (hPo 3)
  have hGdo : IsOpen Gd :=
    (isOpen_params_disjoint hd hMo.isClosed_compl).inter
      (isOpen_params_disjoint hd isClosed_closure)
  have hGd_of : ∀ u, (layer d u ∩ closure (P 2)).Nonempty → u ∈ Gd := by
    rintro u ⟨w, hw, hw2⟩
    obtain ⟨hwm, hw04⟩ := closure_P2_subset hP hn hf hw2
    obtain ⟨c', hc', hcs', t, ht⟩ := strand_layer_of_extension_aux hX hi hP hn hf hr hd hd0 hw hwm
    rw [ht] at hw
    refine ⟨?_, ?_⟩
    · show Disjoint _ _
      rw [ht, disjoint_compl_right_iff_subset]
      exact strand_layer_subset_mid hP hc' hcs' hw hwm
    · show Disjoint _ _
      rw [ht, closure_union, disjoint_union_right]
      exact ⟨layer_disjoint_closure_of_mem hc'.2.1 hPo hcs' hw
          fun h => hw04 (closure_mono subset_union_left h),
        layer_disjoint_closure_of_mem hc'.2.1 hPo hcs' hw
          fun h => hw04 (closure_mono subset_union_right h)⟩
  have hΔ : ∀ u ∈ Gd, layer d u ∈ Delta5 P := by
    rintro u ⟨hu1, hu2⟩
    obtain ⟨p, hp⟩ := layer_nonempty' hd.2.1 u
    have hpm : p ∈ midUnion P := by
      by_contra h
      exact disjoint_left.1 hu1 hp h
    obtain ⟨c', hc', -, t, ht⟩ := strand_layer_of_extension_aux hX hi hP hn hf hr hd hd0 hp hpm
    exact ⟨⟨p, hpm, c', hc', t, ht⟩, hu2⟩
  -- the parameters `a` and `b`
  obtain ⟨l, hl, hlsub⟩ := exists_Ico_subset_of_mem_nhds
    (hGdo.mem_nhds (hGd_of m₂ hm₂A.2)) ⟨z₀, hm₂z⟩
  obtain ⟨a, hma, haz⟩ := exists_between (lt_min hl hm₂z)
  have haGd : a ∈ Gd := hlsub ⟨hma.le, haz.trans_le (min_le_left _ _)⟩
  have haz₀ : a < z₀ := haz.trans_le (min_le_right _ _)
  obtain ⟨l', hl', hl'sub⟩ := exists_Ioc_subset_of_mem_nhds
    (hGdo.mem_nhds (hGd_of us husB.2)) ⟨z₀, hzus⟩
  obtain ⟨b, hmb, hbu⟩ := exists_between (max_lt hl' hzus)
  have hbGd : b ∈ Gd := hl'sub ⟨(le_max_left _ _).trans_lt hmb, hbu.le⟩
  have hz₀b : z₀ < b := (le_max_right _ _).trans_lt hmb
  have hab : a < b := haz₀.trans hz₀b
  -- the bridge
  obtain ⟨j, hj, hjl⟩ := minimalAdmissible_restrict hX hi hd hab
  obtain ⟨t₀, ht₀⟩ := exists_restrictParam_eq hab ⟨haz₀.le, hz₀b.le⟩
  refine ⟨layerSet d (Icc a b), j, hj, ⟨t₀, by rw [hjl, ht₀, hz₀]⟩, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hw2
    have hmem : (layer d (d w) ∩ closure (P 2)).Nonempty := ⟨w.1, mem_layer_self84 d w, hw2⟩
    rcases le_total (d w) z₀ with h | h
    · exact not_lt.2 (hm₂max ⟨h, hmem⟩) (hma.trans_le hw.1)
    · exact not_lt.2 (husmin ⟨h, hmem⟩) (hw.2.trans_lt hbu)
  · rw [hjl, restrictParam_zero]
    exact hΔ a haGd
  · rw [hjl, restrictParam_one]
    exact hΔ b hbGd
  · rintro u ⟨y, hy, hym⟩
    rw [hjl] at hy ⊢
    obtain ⟨c', hc', -, t, ht⟩ := strand_layer_of_extension_aux hX hi hP hn hf hr hd hd0 hy hym
    exact ⟨y, hym, c', hc', t, ht⟩

/-- **§5.1, `Z ∈ Δ(𝒫(Z))`.** If `Q` is a free normal regular chain through which the bridge `(J, j)`
of `Z` runs straight, with `Cl(Q 0 ∪ Q 4) ⊆ ⋃Δ(𝒫)` (Hagopian's (3)), then `Z ∈ Δ(Q)`: `Z` misses
`⋃Δ(𝒫)` (it lies in `Cl P 0` or `Cl P 4`), hence `Cl(Q 0 ∪ Q 4)`, so `Z ⊆ midUnion Q`; the end layer
`j⁻¹(0)` misses `midUnion Q`, and Lemma 16′ for `Q` makes `Z` a layer of a strand of `Q`. -/
theorem mem_delta_of_bridge_chain_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {P Q : Fin 5 → Set M} (hP : IsChain5 P) (hn : IsNormal5 P) (hr : IsRegular5 P)
    (hQ : IsChain5 Q) (hQn : IsNormal5 Q) (hQf : IsFree5 Q) (hQr : IsRegular5 Q)
    {Z : Set M} (hZ : Z ∈ Omega5 P) (hZd : Z ∉ Delta5 P) {J : Set M} {j : J → unitInterval}
    (hj : IsMinimalAdmissible J j) {t : unitInterval} (hZt : Z = layer j t)
    (hjs : RunsStraight j Q) (hB : closure (Q 0 ∪ Q 4) ⊆ ⋃₀ Delta5 P) : Z ∈ Delta5 Q := by
  obtain ⟨hside, -⟩ := omega_not_delta_side_aux hP hn hr hZ hZd
  have hZΔ : Disjoint Z (⋃₀ Delta5 P) := by
    rw [disjoint_left]
    rintro z hz ⟨Z', ⟨-, hZ'd⟩, hzZ'⟩
    rw [closure_union] at hZ'd
    rcases hside with h | h
    · exact disjoint_left.1 hZ'd hzZ' (Or.inl (h hz))
    · exact disjoint_left.1 hZ'd hzZ' (Or.inr (h hz))
  have hZQ : Disjoint Z (closure (Q 0 ∪ Q 4)) := hZΔ.mono_right hB
  obtain ⟨z, hz⟩ := layer_nonempty' hj.2.1 t
  have hzZ : z ∈ Z := hZt ▸ hz
  have hzm : z ∈ midUnion Q := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hjs.1 (layer_subset_set j t hz))
    have h04 : z ∉ Q 0 ∪ Q 4 := fun h => disjoint_left.1 hZQ hzZ (subset_closure h)
    fin_cases i
    · exact absurd (Or.inl hi) h04
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
    · exact absurd (Or.inr hi) h04
  have hj0 : Disjoint (layer j 0) (midUnion Q) := by
    rw [disjoint_left]
    exact fun v hv => endlayers_not_mid hQ hjs (Or.inl hv)
  obtain ⟨c', hc', -, s, hs⟩ := strand_layer_of_extension_aux hX hi hQ hQn hQf hQr hj hj0 hz hzm
  exact ⟨⟨z, hzm, c', hc', s, by rw [hZt, hs]⟩, hZQ⟩

end Bridge

end HPC.Hagopian
