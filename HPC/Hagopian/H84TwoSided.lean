import HPC.Hagopian.Hagopian84A

/-!
# Batch 185, §1: the two-sided extension

Commission 185 §1 (Hagopian 1984, p. 336, in the proof of Lemma 7: "By Lemma 4, there is a continuum
`H` of type λ in `M` such that (1) `E` is an essential subcontinuum of `H` that misses both end sets
of `H`").

* `glue_minimalAdmissible`: two minimal admissible `(A, a)`, `(B, b)` with `A ∩ B = a⁻¹(0) = b⁻¹(0)`
  glue to a minimal admissible `(A ∪ B, c)` (the layers of `B` reversed, then those of `A`).
  Irreducibility uses hereditary unicoherence.
* `ext_inter_ext_subset`: an extension `F₁` of `E` away from `X = k⁻¹(0)` and an extension `F₂` away
  from `Z = k⁻¹(1)` meet only in `E` (commission 185 §1, step 2).
* `hagopian84_two_sided_aux`: the two-sided extension (`H = F₁ ∪ F₂`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section TwoSided

variable {M : Set Pt}

/-- Membership in `layerSet` for a point of `G`. -/
theorem mem_layerSet_iff' {G : Set M} {g : G → unitInterval} {S : Set unitInterval} {m : M}
    (hm : m ∈ G) : m ∈ layerSet g S ↔ g ⟨m, hm⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro h; exact ⟨⟨m, hm⟩, h, rfl⟩

/-- Membership in a layer for a point of `G`. -/
theorem mem_layer_iff' {G : Set M} {g : G → unitInterval} {t : unitInterval} {m : M}
    (hm : m ∈ G) : m ∈ layer g t ↔ g ⟨m, hm⟩ = t := by
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro h; exact ⟨⟨m, hm⟩, h, rfl⟩

theorem layer_subset' {G : Set M} (g : G → unitInterval) (t : unitInterval) : layer g t ⊆ G := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

theorem layerSet_subset' {G : Set M} (g : G → unitInterval) (S : Set unitInterval) :
    layerSet g S ⊆ G := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

/-- `g⁻¹[[a, s]] ∩ g⁻¹[[s, b]] ⊆ g⁻¹(s)`. -/
theorem layerSet_Icc_inter_subset {G : Set M} {g : G → unitInterval} (a s b : unitInterval) :
    layerSet g (Icc a s) ∩ layerSet g (Icc s b) ⊆ layer g s := by
  rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  have : y = x := Subtype.ext hxy
  subst this
  exact ⟨y, le_antisymm hx.2 hy.1, rfl⟩

theorem layerSet_Icc_zero_one {G : Set M} (g : G → unitInterval) : layerSet g (Icc 0 1) = G := by
  apply Subset.antisymm (layerSet_subset' g _)
  intro m hm
  exact ⟨⟨m, hm⟩, ⟨unitInterval.nonneg', unitInterval.le_one'⟩, rfl⟩

variable [CompactSpace M] [ConnectedSpace M]

/-- **A subcontinuum meeting both end layers is everything** (irreducibility of a type λ continuum
between its end sets, point to point). -/
theorem eq_of_meets_end_layers (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {G : Set M}
    {g : G → unitInterval} (hG : IsMinimalAdmissible G g) {K : Set M}
    (hK : Fold.Q78.IsContinuum K) (hKG : K ⊆ G) (h0 : (K ∩ layer g 0).Nonempty)
    (h1 : (K ∩ layer g 1).Nonempty) : K = G := by
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hG.isCompact
  obtain ⟨a, b, -, rfl, -⟩ := isTypeA'_of_subcontinuum hG (lsc_of_minimalAdmissible hX hi hG) hKG hK
    zero_ne_one h0 h1
  obtain ⟨p, hpK, hp0⟩ := h0
  obtain ⟨q, hqK, hq1⟩ := h1
  have ha : a = 0 := by
    obtain ⟨x, hx, rfl⟩ := hpK
    have := (mem_layer_iff' x.2).1 hp0
    exact le_antisymm (by simpa [this] using hx.1) unitInterval.nonneg'
  have hb : b = 1 := by
    obtain ⟨x, hx, rfl⟩ := hqK
    have := (mem_layer_iff' x.2).1 hq1
    exact le_antisymm unitInterval.le_one' (by simpa [this] using hx.2)
  rw [ha, hb, layerSet_Icc_zero_one]

open scoped Classical in
/-- The glued function on `M` (values in `ℝ`): `(1 + a)/2` on `A`, `(1 − b)/2` on `B∖A`. -/
noncomputable def layerGlueFun (A B : Set M) (a : A → unitInterval) (b : B → unitInterval) (m : M) : ℝ :=
  if h : m ∈ A then (1 + (a ⟨m, h⟩ : ℝ)) / 2 else if h' : m ∈ B then (1 - (b ⟨m, h'⟩ : ℝ)) / 2
  else 0

omit [CompactSpace M] [ConnectedSpace M] in
theorem layerGlueFun_mem (A B : Set M) (a : A → unitInterval) (b : B → unitInterval) (m : M) :
    layerGlueFun A B a b m ∈ Icc (0 : ℝ) 1 := by
  unfold layerGlueFun
  split_ifs with h h'
  · have h0 := (a ⟨m, h⟩).2.1; have h1 := (a ⟨m, h⟩).2.2
    constructor <;> linarith
  · have h0 := (b ⟨m, h'⟩).2.1; have h1 := (b ⟨m, h'⟩).2.2
    constructor <;> linarith
  · exact ⟨le_rfl, zero_le_one⟩

/-- The glued map `c : A ∪ B → [0, 1]`. -/
noncomputable def layerGlueMap (A B : Set M) (a : A → unitInterval) (b : B → unitInterval) :
    (A ∪ B : Set M) → unitInterval :=
  fun p => ⟨layerGlueFun A B a b p, layerGlueFun_mem A B a b p⟩

omit [CompactSpace M] [ConnectedSpace M] in
theorem layerGlueFun_of_memA {A B : Set M} {a : A → unitInterval} {b : B → unitInterval} {m : M}
    (h : m ∈ A) : layerGlueFun A B a b m = (1 + (a ⟨m, h⟩ : ℝ)) / 2 := by
  unfold layerGlueFun; rw [dif_pos h]

omit [CompactSpace M] [ConnectedSpace M] in
/-- On `B` the glued function is `(1 − b)/2` (on `A ∩ B` both formulas give `1/2`). -/
theorem layerGlueFun_of_memB {A B : Set M} {a : A → unitInterval} {b : B → unitInterval}
    (hAB : A ∩ B = layer a 0) (hBA : A ∩ B = layer b 0) {m : M} (h : m ∈ B) :
    layerGlueFun A B a b m = (1 - (b ⟨m, h⟩ : ℝ)) / 2 := by
  unfold layerGlueFun
  by_cases hA : m ∈ A
  · rw [dif_pos hA]
    have ha : a ⟨m, hA⟩ = 0 := (mem_layer_iff' hA).1 (hAB ▸ ⟨hA, h⟩)
    have hb : b ⟨m, h⟩ = 0 := (mem_layer_iff' h).1 (hBA ▸ ⟨hA, h⟩)
    rw [ha, hb]; simp
  · rw [dif_neg hA, dif_pos h]

/-- The parameter on the `A` side: `t ↦ (1 + t)/2`. -/
noncomputable def layerGlueA (t : unitInterval) : unitInterval :=
  ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- The parameter on the `B` side: `t ↦ (1 − t)/2`. -/
noncomputable def layerGlueB (t : unitInterval) : unitInterval :=
  ⟨(1 - (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

theorem layerGlueA_injective : Function.Injective layerGlueA := by
  intro s t h
  have := congrArg Subtype.val h
  simp only [layerGlueA] at this
  exact Subtype.ext (by linarith)

theorem layerGlueB_injective : Function.Injective layerGlueB := by
  intro s t h
  have := congrArg Subtype.val h
  simp only [layerGlueB] at this
  exact Subtype.ext (by linarith)

omit [CompactSpace M] [ConnectedSpace M] in
/-- The layers of `A` are layers of the glued map. -/
theorem layer_glue_A {A B : Set M} {a : A → unitInterval} {b : B → unitInterval}
    (hAB : A ∩ B = layer a 0) (hBA : A ∩ B = layer b 0) (t : unitInterval) :
    layer (layerGlueMap A B a b) (layerGlueA t) = layer a t := by
  ext m
  constructor
  · rintro ⟨⟨m, hm⟩, hmt, rfl⟩
    have hv : layerGlueFun A B a b m = (1 + (t : ℝ)) / 2 := congrArg Subtype.val hmt
    rcases hm with hmA | hmB
    · rw [layerGlueFun_of_memA hmA] at hv
      exact ⟨⟨m, hmA⟩, Subtype.ext (by linarith), rfl⟩
    · rw [layerGlueFun_of_memB hAB hBA hmB] at hv
      have hb0 := (b ⟨m, hmB⟩).2.1
      have ht0 : (t : ℝ) = 0 := le_antisymm (by linarith) t.2.1
      have hbm : (b ⟨m, hmB⟩ : ℝ) = 0 := by linarith
      have hm0 : m ∈ layer b 0 := (mem_layer_iff' hmB).2 (Subtype.ext hbm)
      rw [← hBA, hAB] at hm0
      obtain ⟨y, hy, hym⟩ := hm0
      refine ⟨y, ?_, hym⟩
      rw [mem_preimage, mem_singleton_iff] at hy ⊢
      rw [hy]; exact Subtype.ext ht0.symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, Or.inl y.2⟩, ?_, rfl⟩
    rw [mem_preimage, mem_singleton_iff]
    apply Subtype.ext
    change layerGlueFun A B a b y = (1 + (t : ℝ)) / 2
    rw [layerGlueFun_of_memA y.2]
    have : a y = t := hy
    rw [← this]

omit [CompactSpace M] [ConnectedSpace M] in
/-- The layers of `B` are layers of the glued map. -/
theorem layer_glue_B {A B : Set M} {a : A → unitInterval} {b : B → unitInterval}
    (hAB : A ∩ B = layer a 0) (hBA : A ∩ B = layer b 0) (t : unitInterval) :
    layer (layerGlueMap A B a b) (layerGlueB t) = layer b t := by
  ext m
  constructor
  · rintro ⟨⟨m, hm⟩, hmt, rfl⟩
    have hv : layerGlueFun A B a b m = (1 - (t : ℝ)) / 2 := congrArg Subtype.val hmt
    rcases hm with hmA | hmB
    · rw [layerGlueFun_of_memA hmA] at hv
      have ha0 := (a ⟨m, hmA⟩).2.1
      have ht0 : (t : ℝ) = 0 := le_antisymm (by linarith) t.2.1
      have ham : (a ⟨m, hmA⟩ : ℝ) = 0 := by linarith
      have hm0 : m ∈ layer a 0 := (mem_layer_iff' hmA).2 (Subtype.ext ham)
      rw [← hAB, hBA] at hm0
      obtain ⟨y, hy, hym⟩ := hm0
      refine ⟨y, ?_, hym⟩
      rw [mem_preimage, mem_singleton_iff] at hy ⊢
      rw [hy]; exact Subtype.ext ht0.symm
    · rw [layerGlueFun_of_memB hAB hBA hmB] at hv
      exact ⟨⟨m, hmB⟩, Subtype.ext (by linarith), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, Or.inr y.2⟩, ?_, rfl⟩
    rw [mem_preimage, mem_singleton_iff]
    apply Subtype.ext
    change layerGlueFun A B a b y = (1 - (t : ℝ)) / 2
    rw [layerGlueFun_of_memB hAB hBA y.2]
    have : b y = t := hy
    rw [← this]

/-- Every parameter is `layerGlueA s` or `layerGlueB s`. -/
theorem layerGlue_cases (t : unitInterval) : (∃ s, t = layerGlueA s) ∨ ∃ s, t = layerGlueB s := by
  rcases le_total (1 / 2 : ℝ) t with h | h
  · refine Or.inl ⟨⟨2 * t - 1, by constructor <;> linarith [t.2.2]⟩, Subtype.ext ?_⟩
    simp only [layerGlueA]; ring
  · refine Or.inr ⟨⟨1 - 2 * t, by constructor <;> linarith [t.2.1]⟩, Subtype.ext ?_⟩
    simp only [layerGlueB]; ring

theorem layerGlueA_one : layerGlueA 1 = 1 := Subtype.ext (by norm_num [layerGlueA])

theorem layerGlueB_one : layerGlueB 1 = 0 := Subtype.ext (by simp [layerGlueB])

omit [CompactSpace M] [ConnectedSpace M] in
/-- An open subset of `G` inside a layer `a⁻¹(s)` of a set `A ⊆ G` is empty when `a` has layers of
void interior in `A` (void interiors pass to a larger set). -/
theorem interior_layer_of_subset_empty {G A : Set M} (hAG : A ⊆ G) (c : G → unitInterval)
    {a : A → unitInterval} (ha : ∀ s, interior (a ⁻¹' {s}) = ∅) {t : unitInterval} {s : unitInterval}
    (hts : layer c t = layer a s) : interior (c ⁻¹' {t}) = ∅ := by
  by_contra hne
  obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.2 hne
  set U := interior (c ⁻¹' {t})
  set ι : A → G := Set.inclusion hAG
  have hιc : Continuous ι := continuous_inclusion _
  have hV : IsOpen (ι ⁻¹' U) := isOpen_interior.preimage hιc
  have hVsub : ι ⁻¹' U ⊆ a ⁻¹' {s} := by
    intro x hx
    have hxc : (ι x) ∈ c ⁻¹' {t} := interior_subset hx
    have hxl : ((ι x : M)) ∈ layer c t := ⟨ι x, hxc, rfl⟩
    rw [hts] at hxl
    obtain ⟨y, hy, hyx⟩ := hxl
    have : y = x := Subtype.ext hyx
    rw [← this]; exact hy
  have huA : (u : M) ∈ A := by
    have : (u : M) ∈ layer c t := ⟨u, interior_subset hu, rfl⟩
    rw [hts] at this
    exact layer_subset' a s this
  have hmem : (⟨u, huA⟩ : A) ∈ ι ⁻¹' U := by
    show ι ⟨u, huA⟩ ∈ U
    have : ι ⟨u, huA⟩ = u := rfl
    rw [this]; exact hu
  have := interior_maximal hVsub hV hmem
  rw [ha s] at this
  exact this

/-- **Gluing** (commission 185 §1, step 3): two minimal admissible `(A, a)`, `(B, b)` meeting exactly
in `a⁻¹(0) = b⁻¹(0)` glue to a minimal admissible `(A ∪ B, c)`, with `c⁻¹((1 + t)/2) = a⁻¹(t)` and
`c⁻¹((1 − t)/2) = b⁻¹(t)`. Irreducibility (step 4) uses hereditary unicoherence and
`eq_of_meets_end_layers`. -/
theorem glue_minimalAdmissible (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {A B : Set M}
    {a : A → unitInterval} {b : B → unitInterval} (hA : IsMinimalAdmissible A a)
    (hB : IsMinimalAdmissible B b) (hAB : A ∩ B = layer a 0) (hBA : A ∩ B = layer b 0) :
    IsMinimalAdmissible (A ∪ B) (layerGlueMap A B a b) ∧
      (∀ t, layer (layerGlueMap A B a b) (layerGlueA t) = layer a t) ∧
      ∀ t, layer (layerGlueMap A B a b) (layerGlueB t) = layer b t := by
  set c := layerGlueMap A B a b with hc
  have hLA := layer_glue_A (b := b) hAB hBA
  have hLB := layer_glue_B (b := b) hAB hBA
  have hAc : IsCompact A := hA.isCompact
  have hBc : IsCompact B := hB.isCompact
  obtain ⟨-, -, hAirr⟩ := hA.1
  obtain ⟨-, -, hBirr⟩ := hB.1
  have hAcont : Fold.Q78.IsContinuum A := by obtain ⟨_, _, h⟩ := hA.1; exact h.1
  have hBcont : Fold.Q78.IsContinuum B := by obtain ⟨_, _, h⟩ := hB.1; exact h.1
  have hABne : (A ∩ B).Nonempty := by rw [hAB]; exact layer_nonempty hA.2.1.2.1 0
  -- continuity
  have hcont : Continuous c := by
    have hon : ContinuousOn (layerGlueFun A B a b) (A ∪ B) := by
      have h1 : ContinuousOn (layerGlueFun A B a b) A := by
        rw [continuousOn_iff_continuous_restrict]
        have : A.restrict (layerGlueFun A B a b) = fun x => (1 + (a x : ℝ)) / 2 := by
          funext x; simp only [Set.restrict_apply]; rw [layerGlueFun_of_memA x.2]
        rw [this]
        exact ((continuous_const.add (continuous_subtype_val.comp hA.2.1.1)).div_const _)
      have h2 : ContinuousOn (layerGlueFun A B a b) B := by
        rw [continuousOn_iff_continuous_restrict]
        have : B.restrict (layerGlueFun A B a b) = fun x => (1 - (b x : ℝ)) / 2 := by
          funext x; simp only [Set.restrict_apply]; rw [layerGlueFun_of_memB hAB hBA x.2]
        rw [this]
        exact ((continuous_const.sub (continuous_subtype_val.comp hB.2.1.1)).div_const _)
      exact h1.union_of_isClosed h2 hAc.isClosed hBc.isClosed
    rw [continuousOn_iff_continuous_restrict] at hon
    exact hon.subtype_mk _
  -- every layer is a layer of `a` or of `b`
  have hlay : ∀ t, (∃ s, layer c t = layer a s) ∨ ∃ s, layer c t = layer b s := by
    intro t
    rcases layerGlue_cases t with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact Or.inl ⟨s, hLA s⟩
    · exact Or.inr ⟨s, hLB s⟩
  have hsurj : Function.Surjective c := by
    intro t
    have hne : (layer c t).Nonempty := by
      rcases hlay t with ⟨s, hs⟩ | ⟨s, hs⟩
      · rw [hs]; exact layer_nonempty hA.2.1.2.1 s
      · rw [hs]; exact layer_nonempty hB.2.1.2.1 s
    obtain ⟨_, ⟨x, hx, rfl⟩⟩ := hne
    exact ⟨x, hx⟩
  have hconn : ∀ t, IsConnected (c ⁻¹' {t}) := by
    intro t
    obtain ⟨x₀, hx₀⟩ := hsurj t
    refine ⟨⟨x₀, hx₀⟩, ?_⟩
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    change IsPreconnected (layer c t)
    rcases hlay t with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [hs]
      exact ((hA.2.1.2.2 s).image _ continuous_subtype_val.continuousOn).isPreconnected
    · rw [hs]
      exact ((hB.2.1.2.2 s).image _ continuous_subtype_val.continuousOn).isPreconnected
  have hint : ∀ t, interior (c ⁻¹' {t}) = ∅ := by
    intro t
    rcases hlay t with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact interior_layer_of_subset_empty subset_union_left c hA.2.2 hs
    · exact interior_layer_of_subset_empty subset_union_right c hB.2.2 hs
  -- irreducibility
  have hHU := hagopian75_lemma1_hu hX hi
  obtain ⟨α, hα⟩ := layer_nonempty hB.2.1.2.1 1
  obtain ⟨β, hβ⟩ := layer_nonempty hA.2.1.2.1 1
  have hUc : Fold.Q78.IsContinuum (A ∪ B) :=
    ⟨hAc.union hBc, IsConnected.union hABne hAcont.2 hBcont.2⟩
  have hαB : α ∈ B := layer_subset' b 1 hα
  have hβA : β ∈ A := layer_subset' a 1 hβ
  have hirr : IsIrreducibleBetween (A ∪ B) α β := by
    refine ⟨hUc, Or.inr hαB, Or.inl hβA, fun K hK hKU hαK hβK => ?_⟩
    -- `K` meets `A ∩ B`
    have hKAB : (K ∩ (A ∩ B)).Nonempty := by
      have := isPreconnected_closed_iff.1 hK.2.isPreconnected A B hAc.isClosed hBc.isClosed hKU
        ⟨β, hβK, hβA⟩ ⟨α, hαK, hαB⟩
      obtain ⟨x, hxK, hxA, hxB⟩ := this
      exact ⟨x, hxK, hxA, hxB⟩
    obtain ⟨x, hxK, hxAB⟩ := hKAB
    have hKA : Fold.Q78.IsContinuum (K ∩ A) :=
      isContinuum_inter_of_hu hHU hK hAcont ⟨β, hβK, hβA⟩
    have hKB : Fold.Q78.IsContinuum (K ∩ B) :=
      isContinuum_inter_of_hu hHU hK hBcont ⟨α, hαK, hαB⟩
    have hx0a : x ∈ layer a 0 := hAB ▸ hxAB
    have hx0b : x ∈ layer b 0 := hBA ▸ hxAB
    have hKAeq := eq_of_meets_end_layers hX hi hA hKA inter_subset_right
      ⟨x, ⟨hxK, hxAB.1⟩, hx0a⟩ ⟨β, ⟨hβK, hβA⟩, hβ⟩
    have hKBeq := eq_of_meets_end_layers hX hi hB hKB inter_subset_right
      ⟨x, ⟨hxK, hxAB.2⟩, hx0b⟩ ⟨α, ⟨hαK, hαB⟩, hα⟩
    apply Subset.antisymm hKU
    rintro y (hy | hy)
    · rw [← hKAeq] at hy; exact hy.1
    · rw [← hKBeq] at hy; exact hy.1
  exact ⟨⟨⟨α, β, hirr⟩, ⟨hcont, hsurj, hconn⟩, hint⟩, hLA, hLB⟩

/-- **Step 2** (commission 185 §1): an extension `F₁` of `E` away from `X = k⁻¹(0)` and an extension
`F₂` away from `Z = k⁻¹(1)` meet only in `E`. With `F₁ = E ∪ T₁`, `F₂ = E ∪ T₂`, where
`E ∩ T₁ ⊆ Z` and `E ∩ T₂ ⊆ X` (the tails beyond the end layers), `F₁ ∩ F₂` is a continuum
(hereditary unicoherence) inside `E ∪ (T₁ ∩ T₂)`, and `E ∩ T₁ ∩ T₂ ⊆ Z ∩ X = ∅`. -/
theorem ext_inter_ext_subset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {F₁ F₂ T₁ T₂ : Set M}
    (hF₁ : Fold.Q78.IsContinuum F₁) (hF₂ : Fold.Q78.IsContinuum F₂) (hEF₁ : E ⊆ F₁)
    (hEF₂ : E ⊆ F₂) (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) (hF₁T : F₁ ⊆ E ∪ T₁)
    (hF₂T : F₂ ⊆ E ∪ T₂) (hET₁ : E ∩ T₁ ⊆ layer k 1) (hET₂ : E ∩ T₂ ⊆ layer k 0) :
    F₁ ∩ F₂ ⊆ E := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hEne : E.Nonempty := by
    obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 0
    exact ⟨x, layer_subset' k 0 hx⟩
  obtain ⟨e, he⟩ := hEne
  have hK := isContinuum_inter_of_hu hHU hF₁ hF₂ ⟨e, hEF₁ he, hEF₂ he⟩
  intro p hp
  by_contra hpE
  have hEc : IsClosed E := hE.isCompact.isClosed
  have hcov : F₁ ∩ F₂ ⊆ E ∪ (T₁ ∩ T₂) := by
    intro q hq
    by_cases hqE : q ∈ E
    · exact Or.inl hqE
    · refine Or.inr ⟨?_, ?_⟩
      · rcases hF₁T hq.1 with h | h
        · exact absurd h hqE
        · exact h
      · rcases hF₂T hq.2 with h | h
        · exact absurd h hqE
        · exact h
  obtain ⟨q, -, hqE, hq1, hq2⟩ := isPreconnected_closed_iff.1 hK.2.isPreconnected E (T₁ ∩ T₂)
    hEc (hT₁.inter hT₂) hcov ⟨e, ⟨hEF₁ he, hEF₂ he⟩, he⟩
    ⟨p, hp, (hcov hp).resolve_left hpE⟩
  have h1 := hET₁ ⟨hqE, hq1⟩
  have h0 := hET₂ ⟨hqE, hq2⟩
  exact zero_ne_one (layer_param_eq h0 h1)

omit [CompactSpace M] [ConnectedSpace M] in
/-- A layer above `s` misses `g⁻¹[[0, s]]`. -/
theorem disjoint_layerSet_layer {G : Set M} {g : G → unitInterval} {s t : unitInterval}
    (hst : s < t) : Disjoint (layerSet g (Icc 0 s)) (layer g t) := by
  rw [disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have : y = x := Subtype.ext hyx
  subst this
  have h1 : g y = t := hy
  exact absurd (h1 ▸ hx.2) (not_le.2 hst)

/-- **§1, the two-sided extension** (commission 185 §1; report 184 §11). `F₁` an extension of `E`
away from `X = k⁻¹(0)`, `F₂` one away from `Z = k⁻¹(1)` (Lemma 4, no maximal element), `E` an
initial segment of each (`ext_layers`); `F₁ ∩ F₂ = E` (`ext_inter_ext_subset`); `H = F₁ ∪ T₂` with
`T₂ = d₂⁻¹[[s₂, 1]]` the tail of `F₂` beyond `X` (`piece_map`), glued along `X`
(`glue_minimalAdmissible`). -/
theorem hagopian84_two_sided_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (H : Set M) (d : H → unitInterval), IsMinimalAdmissible H d ∧ IsEssential84 d E ∧
      Disjoint E (layer d 0) ∧ Disjoint E (layer d 1) := by
  -- `F₁`, away from `X`
  obtain ⟨F₁, ⟨hEF₁, d₁, hd₁, hX₁⟩, hEF₁'⟩ :=
    (hagopian76_lemma4 hX hi hE).2 E ⟨subset_rfl, k, hE, rfl⟩
  have hne₁ : F₁ ≠ E := fun h => (ssubset_iff_subset_ne.1 hEF₁').2 h.symm
  obtain ⟨s₁, hs₁0, hs₁1, hZ₁, hE₁, -, -⟩ := ext_layers hX hi hE hd₁ hEF₁ hX₁ hne₁
  -- `F₂`, away from `Z`
  have hE' := hE.symm_comp
  obtain ⟨F₂, ⟨hEF₂, d₂, hd₂, hX₂⟩, hEF₂'⟩ :=
    (hagopian76_lemma4 hX hi hE').2 E ⟨subset_rfl, _, hE', rfl⟩
  have hne₂ : F₂ ≠ E := fun h => (ssubset_iff_subset_ne.1 hEF₂').2 h.symm
  obtain ⟨s₂, hs₂0, hs₂1, hZ₂, hE₂, -, -⟩ := ext_layers hX hi hE' hd₂ hEF₂ hX₂ hne₂
  rw [layer_symm_comp, unitInterval.symm_one] at hZ₂
  -- the tails
  set T₁ := layerSet d₁ (Icc s₁ 1) with hT₁
  set T₂ := layerSet d₂ (Icc s₂ 1) with hT₂
  have hF₁T : F₁ ⊆ E ∪ T₁ := by
    intro m hm
    by_cases h : d₁ ⟨m, hm⟩ ≤ s₁
    · left; rw [← hE₁]; exact (mem_layerSet_iff' hm).2 ⟨unitInterval.nonneg', h⟩
    · right; exact (mem_layerSet_iff' hm).2 ⟨(not_le.1 h).le, unitInterval.le_one'⟩
  have hF₂T : F₂ ⊆ E ∪ T₂ := by
    intro m hm
    by_cases h : d₂ ⟨m, hm⟩ ≤ s₂
    · left; rw [← hE₂]; exact (mem_layerSet_iff' hm).2 ⟨unitInterval.nonneg', h⟩
    · right; exact (mem_layerSet_iff' hm).2 ⟨(not_le.1 h).le, unitInterval.le_one'⟩
  have hET₁ : E ∩ T₁ ⊆ layer k 1 := by
    rw [← hZ₁]; conv_lhs => rw [← hE₁]
    exact layerSet_Icc_inter_subset 0 s₁ 1
  have hET₂ : E ∩ T₂ ⊆ layer k 0 := by
    rw [← hZ₂]; conv_lhs => rw [← hE₂]
    exact layerSet_Icc_inter_subset 0 s₂ 1
  have hF₁c : Fold.Q78.IsContinuum F₁ := by obtain ⟨_, _, h⟩ := hd₁.1; exact h.1
  have hF₂c : Fold.Q78.IsContinuum F₂ := by obtain ⟨_, _, h⟩ := hd₂.1; exact h.1
  have hF12 := ext_inter_ext_subset hX hi hE hF₁c hF₂c hEF₁ hEF₂
    (isClosed_layerSet_Icc hd₁ s₁ 1) (isClosed_layerSet_Icc hd₂ s₂ 1) hF₁T hF₂T hET₁ hET₂
  -- the tail of `F₂` as a type λ continuum
  haveI : CompactSpace F₂ := isCompact_iff_compactSpace.mp hd₂.isCompact
  obtain ⟨p₂, hp₂, hp₂0, hp₂1⟩ :=
    piece_map hd₂ (lsc_of_minimalAdmissible hX hi hd₂) hs₂1 (P := T₂) rfl
  have hT₂F₂ : T₂ ⊆ F₂ := layerSet_subset' d₂ _
  have hAB : F₁ ∩ T₂ = layer d₁ 0 := by
    rw [hX₁]
    apply Subset.antisymm
    · intro m hm
      exact hET₂ ⟨hF12 ⟨hm.1, hT₂F₂ hm.2⟩, hm.2⟩
    · intro m hm
      refine ⟨hEF₁ (layer_subset' k 0 hm), ?_⟩
      rw [← hZ₂] at hm
      obtain ⟨y, hy, rfl⟩ := hm
      exact ⟨y, ⟨le_of_eq hy.symm, unitInterval.le_one'⟩, rfl⟩
  have hBA : F₁ ∩ T₂ = layer p₂ 0 := by rw [hAB, hp₂0, hX₁, hZ₂]
  obtain ⟨hH, hLA, hLB⟩ := glue_minimalAdmissible hX hi hd₁ hp₂ hAB hBA
  refine ⟨F₁ ∪ T₂, layerGlueMap F₁ T₂ d₁ p₂, hH, ⟨hEF₁.trans subset_union_left, ?_, layerGlueA 0, layerGlueA s₁,
    fun h => hs₁0.ne (layerGlueA_injective h), ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨_, _, h⟩ := hE.1; exact h.1
  · rw [hLA, hX₁]
    obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 0
    exact ⟨x, layer_subset' k 0 hx, hx⟩
  · rw [hLA, hZ₁]
    obtain ⟨x, hx⟩ := layer_nonempty hE.2.1.2.1 1
    exact ⟨x, layer_subset' k 1 hx, hx⟩
  · rw [← layerGlueB_one, hLB, hp₂1, ← hE₂]
    exact disjoint_layerSet_layer hs₂1
  · rw [← layerGlueA_one, hLA, ← hE₁]
    exact disjoint_layerSet_layer hs₁1

end TwoSided

end HPC.Hagopian
