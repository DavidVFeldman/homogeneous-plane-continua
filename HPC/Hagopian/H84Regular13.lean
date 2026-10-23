import HPC.Hagopian.H84Runs13

/-!
# Batch 187, §2: Lemma 13, regularity

Commission 186 §3.1.5 / 187 §2: "Let `K` be a component of `⋃𝔏′`. Let `h` be a `δ`-homeomorphism
of `M` onto `M` such that `K ∩ h[E] ≠ ∅`. Since `M` is atriodic, it follows from (6) and Lemma 6
that `Cl K` is an essential subcontinuum of `h[E]` that runs straight through `𝔏`."

* `strand_of_runsStraight84`: the general form. If `(G, b)` is type λ and runs straight through a
  normal chain `𝔏` with its end layers in `L 0 ∖ Cl L 1` and `L 4 ∖ Cl L 3`, then for every
  component `K` of `⋃𝔏′` meeting `G`, `Cl K` is an essential subcontinuum of `G` and runs straight
  through `𝔏` (with the restricted map).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Params

theorem mem_layerSet_iff84 {X : Type*} {G : Set X} (b : G → unitInterval) (S : Set unitInterval)
    (w : G) : w.1 ∈ layerSet b S ↔ b w ∈ S := by
  constructor
  · rintro ⟨w', hw', hww'⟩
    have : w' = w := Subtype.ext hww'
    subst this
    exact hw'
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem restrictParam_le84 {a c : unitInterval} (hac : a ≤ c) {r t : unitInterval} (hrt : r ≤ t) :
    restrictParam a c hac r ≤ restrictParam a c hac t := by
  show (a : ℝ) + r * (c - a) ≤ a + t * (c - a)
  have : (0 : ℝ) ≤ c - a := sub_nonneg.2 hac
  have : (r : ℝ) ≤ t := hrt
  nlinarith

theorem restrictParam_lt84 {a c : unitInterval} (hac : a < c) {r t : unitInterval} (hrt : r < t) :
    restrictParam a c hac.le r < restrictParam a c hac.le t := by
  show (a : ℝ) + r * (c - a) < a + t * (c - a)
  have : (0 : ℝ) < c - a := sub_pos.2 hac
  have : (r : ℝ) < t := hrt
  nlinarith

/-- Five open sets of `[0, 1]` with non-adjacent ones disjoint, covering, `0 ∈ V 0`, `1 ∈ V 4`:
consecutive ones meet. -/
theorem params_adjacent_meet84 {V : Fin 5 → Set unitInterval} (hV : ∀ i, IsOpen (V i))
    (hcov : ∀ u, ∃ i, u ∈ V i) (hdisj : ∀ i j : Fin 5, (i : ℕ) + 1 < j → Disjoint (V i) (V j))
    (h0 : (0 : unitInterval) ∈ V 0) (h1 : (1 : unitInterval) ∈ V 4) (m : ℕ) (hm : m + 1 < 5)
    (hmm : Disjoint (V ⟨m, by omega⟩) (V ⟨m + 1, hm⟩)) : False := by
  set U₁ := ⋃ (j : Fin 5) (_ : (j : ℕ) ≤ m), V j
  set U₂ := ⋃ (j : Fin 5) (_ : m < (j : ℕ)), V j
  have hU₁ : IsOpen U₁ := isOpen_biUnion fun j _ => hV j
  have hU₂ : IsOpen U₂ := isOpen_biUnion fun j _ => hV j
  have hd : Disjoint U₁ U₂ := by
    rw [disjoint_left]
    intro u hu hu'
    simp only [U₁, U₂, mem_iUnion] at hu hu'
    obtain ⟨j, hj, hju⟩ := hu
    obtain ⟨j', hj', hju'⟩ := hu'
    by_cases hadj : (j : ℕ) + 1 < j'
    · exact disjoint_left.1 (hdisj j j' hadj) hju hju'
    · have hjm : j = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
      have hj'm : j' = ⟨m + 1, hm⟩ := Fin.ext (by simp; omega)
      rw [hjm] at hju
      rw [hj'm] at hju'
      exact disjoint_left.1 hmm hju hju'
  have hc : (univ : Set unitInterval) ⊆ U₁ ∪ U₂ := by
    intro u _
    obtain ⟨j, hj⟩ := hcov u
    by_cases hjm : (j : ℕ) ≤ m
    · exact Or.inl (mem_iUnion₂.2 ⟨j, hjm, hj⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨j, by omega, hj⟩)
  rcases isPreconnected_univ.subset_or_subset hU₁ hU₂ hd hc with hs | hs
  · obtain ⟨j, hj, hju⟩ := mem_iUnion₂.1 (hs (mem_univ (1 : unitInterval)))
    by_cases hj4 : (j : ℕ) + 1 < 4
    · exact disjoint_left.1 (hdisj j 4 (by simpa using hj4)) hju h1
    · have hjm : j = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
      have h4 : (4 : Fin 5) = ⟨m + 1, hm⟩ := Fin.ext (by simp; omega)
      rw [hjm] at hju
      rw [h4] at h1
      exact disjoint_left.1 hmm hju h1
  · obtain ⟨j, hj, hju⟩ := mem_iUnion₂.1 (hs (mem_univ (0 : unitInterval)))
    by_cases hj1 : 1 < (j : ℕ)
    · exact disjoint_left.1 (hdisj 0 j (by simpa using hj1)) h0 hju
    · have hjm : j = ⟨m + 1, hm⟩ := Fin.ext (by simp; omega)
      have h00 : (0 : Fin 5) = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
      rw [hjm] at hju
      rw [h00] at h0
      exact disjoint_left.1 hmm h0 hju

/-- A neighbourhood of `u < 1` in `[0, 1]` contains some `[u, u₁]` with `u < u₁`. -/
theorem exists_right_Icc84 {W : Set unitInterval} {u : unitInterval} (hW : W ∈ 𝓝 u) (hu : u < 1) :
    ∃ u₁, u < u₁ ∧ Icc u u₁ ⊆ W := by
  obtain ⟨u', hu', hsub⟩ := exists_Ico_subset_of_mem_nhds' hW hu
  obtain ⟨u₁, h1, h2⟩ := exists_between hu'.1
  exact ⟨u₁, h1, fun v hv => hsub ⟨hv.1, hv.2.trans_lt h2⟩⟩

/-- A neighbourhood of `0 < u` in `[0, 1]` contains some `[u₁, u]` with `u₁ < u`. -/
theorem exists_left_Icc84 {W : Set unitInterval} {u : unitInterval} (hW : W ∈ 𝓝 u) (hu : 0 < u) :
    ∃ u₁, u₁ < u ∧ Icc u₁ u ⊆ W := by
  obtain ⟨l', hl', hsub⟩ := exists_Ioc_subset_of_mem_nhds' hW hu
  obtain ⟨u₁, h1, h2⟩ := exists_between hl'.2
  exact ⟨u₁, h2, fun v hv => hsub ⟨h1.trans_le hv.1, hv.2⟩⟩

theorem layer_subset_layerSet84 {X : Type*} {G : Set X} (b : G → unitInterval) {u : unitInterval}
    {S : Set unitInterval} (hu : u ∈ S) : layer b u ⊆ layerSet b S := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, by rw [mem_preimage, show b w = u from hw]; exact hu, rfl⟩

end Params

section Strand

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Regularity, general form** (p. 340: "Since `M` is atriodic, it follows from (6) and Lemma 6
that `Cl K` is an essential subcontinuum of `h[E]` that runs straight through `𝔏`").

*Proof*: `Cl K` is a continuum meeting `G` and missing the end layers of `G` (they lie in
`L 0 ∖ Cl L 1` and `L 4 ∖ Cl L 3`, which miss `Cl ⋃𝔏′` by normality), so `Cl K ⊆ G` by atriodicity
(`subset_of_meets_avoids`). The parameters `V j = {u : b⁻¹(u) ⊆ L j}` are open intervals (runs
straight), and the layers through a short parameter interval at `y` form a connected subset of
`⋃𝔏′`, so `Cl K` is essential, hence `b⁻¹[[a, c]]` (Lemma 6). The end parameters `a`, `c` are not
in `V 1 ∪ V 2 ∪ V 3` (else `K` would extend beyond them), so they lie in `V 0 ∪ V 4`; `a ∈ V 4` or
`c ∈ V 0` would make two consecutive `V j` disjoint (`params_adjacent_meet84`). So `b⁻¹(a)` lies
in `L 0 ∖ L 1` and `b⁻¹(c)` in `L 4 ∖ L 3`, and the restricted map runs straight. -/
theorem strand_of_runsStraight84 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {L : Fin 5 → Set M} (hL : IsChain5 L) (hn : IsNormal5 L) {G : Set M} {b : G → unitInterval}
    (hb : IsMinimalAdmissible G b) (hrs : RunsStraight b L)
    (h0 : layer b 0 ⊆ L 0 \ closure (L 1)) (h1 : layer b 1 ⊆ L 4 \ closure (L 3)) {y : M}
    (hyG : y ∈ G) (hy : y ∈ midUnion L) :
    IsEssential84 b (closure (connectedComponentIn (midUnion L) y)) ∧
      ∃ d : closure (connectedComponentIn (midUnion L) y) → unitInterval,
        IsMinimalAdmissible (closure (connectedComponentIn (midUnion L) y)) d ∧
          RunsStraight d L := by
  have hk := hb.2.1
  set K := connectedComponentIn (midUnion L) y with hKdef
  have hmo : IsOpen (midUnion L) := ((hL.isOpen 1).union (hL.isOpen 2)).union (hL.isOpen 3)
  -- the parameter sets
  set V : Fin 5 → Set unitInterval := fun j => {u | layer b u ⊆ L j} with hVdef
  have hmeetV : ∀ j u, (layer b u ∩ L j).Nonempty → u ∈ V j :=
    fun j u h => layer_subset_link hk hL.isOpen hrs h
  have hVeq : ∀ j, V j = {u | (layer b u ∩ L j).Nonempty} := by
    intro j; ext u
    refine ⟨fun hu => ?_, hmeetV j u⟩
    obtain ⟨z, hz⟩ := layer_nonempty' hk u
    exact ⟨z, hz, hu hz⟩
  have hVo : ∀ j, IsOpen (V j) := fun j => by
    rw [hVeq]; exact isOpen_params_meeting hX hi hb (hL.isOpen j)
  have hVord : ∀ j, (V j).OrdConnected := by
    intro j
    refine ⟨fun r hr t ht u hu => ?_⟩
    rcases eq_or_lt_of_le (hu.1.trans hu.2) with hrt | hrt
    · have : u = r := le_antisymm (hrt ▸ hu.2) hu.1
      rw [this]; exact hr
    · have hsub := hrs.2.2.2.2 r t j hrt (union_subset hr ht)
      rintro _ ⟨w, hw, rfl⟩
      have hw' : b w = u := hw
      exact hsub ⟨w, show b w ∈ Icc r t by rw [hw']; exact hu, rfl⟩
  have hcovV : ∀ u, ∃ j, u ∈ V j := by
    intro u
    obtain ⟨z, hz⟩ := layer_nonempty' hk u
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hrs.1 (layer_subset_set b u hz))
    exact ⟨j, hmeetV j u ⟨z, hz, hj⟩⟩
  have hdisjV : ∀ i j : Fin 5, (i : ℕ) + 1 < j → Disjoint (V i) (V j) := by
    intro i j hij
    rw [disjoint_left]
    intro u hu hu'
    obtain ⟨z, hz⟩ := layer_nonempty' hk u
    exact disjoint_left.1 (chain5_disjoint hL i j hij) (hu hz) (hu' hz)
  have h0V : (0 : unitInterval) ∈ V 0 := fun z hz => (h0 hz).1
  have h1V : (1 : unitInterval) ∈ V 4 := fun z hz => (h1 hz).1
  have h0V1 : (0 : unitInterval) ∉ V 1 := by
    intro hs
    obtain ⟨z, hz⟩ := layer_nonempty' hk 0
    exact (h0 hz).2 (subset_closure (hs hz))
  have h1V3 : (1 : unitInterval) ∉ V 3 := by
    intro hs
    obtain ⟨z, hz⟩ := layer_nonempty' hk 1
    exact (h1 hz).2 (subset_closure (hs hz))
  -- the parameters of the layers inside `⋃𝔏′`
  set W : Set unitInterval := {u | (layer b u ∩ midUnion L).Nonempty} with hWdef
  have hWo : IsOpen W := isOpen_params_meeting hX hi hb hmo
  have hWV : ∀ u, u ∈ W ↔ u ∈ V 1 ∨ u ∈ V 2 ∨ u ∈ V 3 := by
    intro u
    constructor
    · rintro ⟨z, hz, hzm⟩
      rcases hzm with (hzm | hzm) | hzm
      · exact Or.inl (hmeetV 1 u ⟨z, hz, hzm⟩)
      · exact Or.inr (Or.inl (hmeetV 2 u ⟨z, hz, hzm⟩))
      · exact Or.inr (Or.inr (hmeetV 3 u ⟨z, hz, hzm⟩))
    · intro hu
      obtain ⟨z, hz⟩ := layer_nonempty' hk u
      rcases hu with hu | hu | hu
      · exact ⟨z, hz, Or.inl (Or.inl (hu hz))⟩
      · exact ⟨z, hz, Or.inl (Or.inr (hu hz))⟩
      · exact ⟨z, hz, Or.inr (hu hz)⟩
  have hWsub : ∀ u ∈ W, layer b u ⊆ midUnion L := by
    intro u hu z hz
    rcases (hWV u).1 hu with hu | hu | hu
    · exact Or.inl (Or.inl (hu hz))
    · exact Or.inl (Or.inr (hu hz))
    · exact Or.inr (hu hz)
  have h0W : (0 : unitInterval) ∉ W := by
    intro h
    rcases (hWV 0).1 h with h | h | h
    · exact h0V1 h
    · exact disjoint_left.1 (hdisjV 0 2 (by simp)) h0V h
    · exact disjoint_left.1 (hdisjV 0 3 (by simp)) h0V h
  have h1W : (1 : unitInterval) ∉ W := by
    intro h
    rcases (hWV 1).1 h with h | h | h
    · exact disjoint_left.1 (hdisjV 1 4 (by simp)) h h1V
    · exact disjoint_left.1 (hdisjV 2 4 (by simp)) h h1V
    · exact h1V3 h
  -- layers over an interval of `W` through a point of `K` lie in `K`
  have hlayK : ∀ u₁ u₂ : unitInterval, u₁ ≤ u₂ → Icc u₁ u₂ ⊆ W →
      (layerSet b (Icc u₁ u₂) ∩ K).Nonempty → layerSet b (Icc u₁ u₂) ⊆ K := by
    intro u₁ u₂ hu hW ⟨p, hpT, hpK⟩
    have hT : IsPreconnected (layerSet b (Icc u₁ u₂)) :=
      (isContinuum_img hb.isCompact hk isClosed_Icc isPreconnected_Icc
        ⟨u₁, left_mem_Icc.2 hu⟩).2.isPreconnected
    have hTm : layerSet b (Icc u₁ u₂) ⊆ midUnion L := by
      rintro _ ⟨w, hw, rfl⟩
      exact hWsub (b w) (hW hw) (mem_layer_self84 b w)
    rw [hKdef, connectedComponentIn_eq hpK]
    exact hT.subset_connectedComponentIn hpT hTm
  -- Step 1: `Cl K ⊆ G`
  have hKc : Fold.Q78.IsContinuum (closure K) :=
    ⟨isClosed_closure.isCompact, (isConnected_connectedComponentIn_iff.2 hy).closure⟩
  obtain ⟨a₀, b₀, hab₀⟩ := hb.1
  have hKG : closure K ⊆ G := by
    refine subset_of_meets_avoids (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1
      hab₀.1 hk hKc ⟨y, hyG, subset_closure (mem_connectedComponentIn hy)⟩ ?_
    have hcl : closure K ⊆ closure (L 1) ∪ closure (L 2) ∪ closure (L 3) := by
      rw [← closure_union, ← closure_union]
      exact closure_mono (connectedComponentIn_subset _ _)
    rw [disjoint_left]
    intro z hzK hz
    rcases hcl hzK with (hz1 | hz2) | hz3
    · rcases hz with hz | hz
      · exact (h0 hz).2 hz1
      · exact disjoint_left.1 (hn 1 4 (by simp)) hz1 (subset_closure (h1 hz).1)
    · rcases hz with hz | hz
      · exact disjoint_left.1 (hn 0 2 (by simp)) (subset_closure (h0 hz).1) hz2
      · exact disjoint_left.1 (hn 2 4 (by simp)) hz2 (subset_closure (h1 hz).1)
    · rcases hz with hz | hz
      · exact disjoint_left.1 (hn 0 3 (by simp)) (subset_closure (h0 hz).1) hz3
      · exact (h1 hz).2 hz3
  -- Step 2: `Cl K` is essential
  set y' : G := ⟨y, hyG⟩ with hy'def
  have hu₀W : b y' ∈ W := ⟨y, mem_layer_self84 b y', hy⟩
  have hu₀1 : b y' < 1 := lt_of_le_of_ne unitInterval.le_one' (fun h => h1W (h ▸ hu₀W))
  obtain ⟨u₁, hu₁, hu₁W⟩ := exists_right_Icc84 (hWo.mem_nhds hu₀W) hu₀1
  have hyK : y ∈ K := mem_connectedComponentIn hy
  have hTK := hlayK (b y') u₁ hu₁.le hu₁W
    ⟨y, (mem_layerSet_iff84 b _ y').2 (left_mem_Icc.2 hu₁.le), hyK⟩
  obtain ⟨z₁, hz₁⟩ := layer_nonempty' hk u₁
  have hess : IsEssential84 b (closure K) :=
    ⟨hKG, hKc, b y', u₁, hu₁.ne, ⟨y, subset_closure hyK, mem_layer_self84 b y'⟩,
      ⟨z₁, subset_closure (hTK (layer_subset_layerSet84 b (right_mem_Icc.2 hu₁.le) hz₁)), hz₁⟩⟩
  -- Step 3: Lemma 6
  obtain ⟨⟨a, c, hac, hKeq⟩, -, -⟩ := hagopian84_lemma6 hX hi hb hess
  have hparam : ∀ w : G, w.1 ∈ closure K → b w ∈ Icc a c := fun w hw =>
    (mem_layerSet_iff84 b _ w).1 (hKeq ▸ hw)
  -- Step 4: the end parameters are not in `W`
  have hendK : ∀ v ∈ W, v ∈ Icc a c → layer b v ⊆ K := by
    intro v hvW hv
    have hS : IsPreconnected (K ∪ layer b v) :=
      isPreconnected_connectedComponentIn.subset_closure subset_union_left
        (union_subset subset_closure (hKeq ▸ layer_subset_layerSet84 b hv))
    have := hS.subset_connectedComponentIn (Or.inl hyK)
      (union_subset (connectedComponentIn_subset _ _) (hWsub v hvW))
    exact subset_union_right.trans this
  have haW : a ∉ W := by
    intro haW
    have ha0 : 0 < a := lt_of_le_of_ne unitInterval.nonneg' (fun h => h0W (h ▸ haW))
    obtain ⟨a', ha', ha'W⟩ := exists_left_Icc84 (hWo.mem_nhds haW) ha0
    have hlaK := hendK a haW (left_mem_Icc.2 hac.le)
    obtain ⟨p, hp⟩ := layer_nonempty' hk a
    have hT := hlayK a' a ha'.le ha'W
      ⟨p, layer_subset_layerSet84 b (right_mem_Icc.2 ha'.le) hp, hlaK hp⟩
    obtain ⟨_, ⟨w, hw, rfl⟩⟩ := layer_nonempty' hk a'
    have := hparam w (subset_closure
      (hT (layer_subset_layerSet84 b (left_mem_Icc.2 ha'.le) ⟨w, hw, rfl⟩)))
    exact absurd this.1 (not_le.2 ((show b w = a' from hw) ▸ ha'))
  have hcW : c ∉ W := by
    intro hcW
    have hc1 : c < 1 := lt_of_le_of_ne unitInterval.le_one' (fun h => h1W (h ▸ hcW))
    obtain ⟨c', hc', hc'W⟩ := exists_right_Icc84 (hWo.mem_nhds hcW) hc1
    have hlcK := hendK c hcW (right_mem_Icc.2 hac.le)
    obtain ⟨p, hp⟩ := layer_nonempty' hk c
    have hT := hlayK c c' hc'.le hc'W
      ⟨p, layer_subset_layerSet84 b (left_mem_Icc.2 hc'.le) hp, hlcK hp⟩
    obtain ⟨_, ⟨w, hw, rfl⟩⟩ := layer_nonempty' hk c'
    have := hparam w (subset_closure
      (hT (layer_subset_layerSet84 b (right_mem_Icc.2 hc'.le) ⟨w, hw, rfl⟩)))
    exact absurd this.2 (not_le.2 ((show b w = c' from hw) ▸ hc'))
  -- Step 5: orientation
  have hu₀ac : b y' ∈ Icc a c := hparam y' (subset_closure hyK)
  have hend04 : ∀ v, v ∉ W → v ∈ V 0 ∨ v ∈ V 4 := by
    intro v hv
    obtain ⟨j, hj⟩ := hcovV v
    fin_cases j
    · exact Or.inl hj
    · exact absurd ((hWV v).2 (Or.inl hj)) hv
    · exact absurd ((hWV v).2 (Or.inr (Or.inl hj))) hv
    · exact absurd ((hWV v).2 (Or.inr (Or.inr hj))) hv
    · exact Or.inr hj
  have haV0 : a ∈ V 0 := by
    rcases hend04 a haW with h | h
    · exact h
    exfalso
    have hI : Icc a 1 ⊆ V 4 := (hVord 4).out h h1V
    have hu₀3 : b y' ∈ V 3 := by
      rcases (hWV _).1 hu₀W with h' | h' | h'
      · exact absurd (hI ⟨hu₀ac.1, unitInterval.le_one'⟩)
          (disjoint_left.1 (hdisjV 1 4 (by simp)) h')
      · exact absurd (hI ⟨hu₀ac.1, unitInterval.le_one'⟩)
          (disjoint_left.1 (hdisjV 2 4 (by simp)) h')
      · exact h'
    have hV3 : ∀ v ∈ V 3, v ∈ V 4 := by
      intro v hv
      by_cases hva : v ≤ a
      · exact absurd ((hWV a).2 (Or.inr (Or.inr ((hVord 3).out hv hu₀3 ⟨hva, hu₀ac.1⟩)))) haW
      by_cases hvc : c ≤ v
      · exact absurd ((hWV c).2 (Or.inr (Or.inr ((hVord 3).out hu₀3 hv ⟨hu₀ac.2, hvc⟩)))) hcW
      exact hI ⟨(not_le.1 hva).le, unitInterval.le_one'⟩
    refine params_adjacent_meet84 hVo hcovV hdisjV h0V h1V 2 (by omega) ?_
    rw [disjoint_left]
    intro v hv2 hv3
    exact disjoint_left.1 (hdisjV 2 4 (by simp)) hv2 (hV3 v hv3)
  have hcV4 : c ∈ V 4 := by
    rcases hend04 c hcW with h | h
    swap
    · exact h
    exfalso
    have hI : Icc 0 c ⊆ V 0 := (hVord 0).out h0V h
    have hu₀1' : b y' ∈ V 1 := by
      rcases (hWV _).1 hu₀W with h' | h' | h'
      · exact h'
      · exact absurd h' (disjoint_left.1 (hdisjV 0 2 (by simp))
          (hI ⟨unitInterval.nonneg', hu₀ac.2⟩))
      · exact absurd h' (disjoint_left.1 (hdisjV 0 3 (by simp))
          (hI ⟨unitInterval.nonneg', hu₀ac.2⟩))
    have hV1 : ∀ v ∈ V 1, v ∈ V 0 := by
      intro v hv
      by_cases hva : v ≤ a
      · exact absurd ((hWV a).2 (Or.inl ((hVord 1).out hv hu₀1' ⟨hva, hu₀ac.1⟩))) haW
      by_cases hvc : c ≤ v
      · exact absurd ((hWV c).2 (Or.inl ((hVord 1).out hu₀1' hv ⟨hu₀ac.2, hvc⟩))) hcW
      exact hI ⟨unitInterval.nonneg', (not_le.1 hvc).le⟩
    refine params_adjacent_meet84 hVo hcovV hdisjV h0V h1V 1 (by omega) ?_
    rw [disjoint_left]
    intro v hv1 hv2
    exact disjoint_left.1 (hdisjV 0 2 (by simp)) (hV1 v hv1) hv2
  -- Step 6: the restricted map runs straight
  obtain ⟨e, he, hlay⟩ := minimalAdmissible_restrict hX hi hb hac
  refine ⟨hess, ?_⟩
  rw [hKeq]
  refine ⟨e, he, (layerSet_subset' b _).trans hrs.1, ?_, ?_, ?_, ?_⟩
  · rw [hlay, restrictParam_zero]
    exact fun z hz => ⟨haV0 hz, fun hz1 => haW ((hWV a).2 (Or.inl (hmeetV 1 a ⟨z, hz, hz1⟩)))⟩
  · rw [hlay, restrictParam_one]
    exact fun z hz => ⟨hcV4 hz,
      fun hz3 => hcW ((hWV c).2 (Or.inr (Or.inr (hmeetV 3 c ⟨z, hz, hz3⟩))))⟩
  · intro r i hr
    rw [hlay] at hr ⊢
    exact hrs.2.2.2.1 _ i hr
  · intro r t i hrt hsub
    rw [hlay, hlay] at hsub
    have hsub' := hrs.2.2.2.2 _ _ i (restrictParam_lt84 hac hrt) hsub
    rintro _ ⟨w, hw, rfl⟩
    have hwl : w.1 ∈ layer e (e w) := mem_layer_self84 e w
    rw [hlay] at hwl
    exact hsub' (layer_subset_layerSet84 b (show restrictParam a c hac.le (e w) ∈
      Icc (restrictParam a c hac.le r) (restrictParam a c hac.le t) from
      ⟨restrictParam_le84 hac.le hw.1, restrictParam_le84 hac.le hw.2⟩) hwl)

end Strand

end HPC.Hagopian
