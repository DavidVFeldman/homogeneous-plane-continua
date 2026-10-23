import HPC.Moore.M19Defs

/-!
# Moore 1919, Theorem A (batch 140, item C)
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

namespace Gen

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **The crossing lemma** behind Theorem A. `L` is the union of two arcs `D₁ = h₁[0,1]`,
`D₂ = h₂[0,1]` from `a` to `b` meeting only in `a`, `b`. There are neighbourhoods `Vₐ` of `a` and
`V_b` of `b` and two nondegenerate arcs `P₁ = h₁[⅓, ⅔]`, `P₂ = h₂[⅓, ⅔]` of `L` such that every
connected subset of `L` meeting both `Vₐ` and `V_b` contains `P₁` or `P₂`. (Moore's points
`C, D, E, F` in the order `ECADFB` are `h₂(⅓), h₁(⅓), h₂(⅔), h₁(⅔)`.) -/
theorem crossing {a b : X} {h₁ h₂ : unitInterval → X} (hh₁ : IsEmbedding h₁)
    (hh₂ : IsEmbedding h₂) (h₁0 : h₁ 0 = a) (h₁1 : h₁ 1 = b) (h₂0 : h₂ 0 = a) (h₂1 : h₂ 1 = b)
    (hi : range h₁ ∩ range h₂ = {a, b}) :
    ∃ Va ∈ 𝓝 a, ∃ Vb ∈ 𝓝 b, ∃ s t : unitInterval, s < t ∧
      ∀ F : Set X, IsPreconnected F → F ⊆ range h₁ ∪ range h₂ → (F ∩ Va).Nonempty →
        (F ∩ Vb).Nonempty → h₁ '' Icc s t ⊆ F ∨ h₂ '' Icc s t ⊆ F := by
  set s : unitInterval := ⟨1 / 3, by norm_num, by norm_num⟩ with hs
  set t : unitInterval := ⟨2 / 3, by norm_num, by norm_num⟩ with ht
  have h0s : (0 : unitInterval) < s := by rw [hs]; exact Subtype.mk_lt_mk.mpr (by norm_num)
  have hst : s < t := by rw [hs, ht]; exact Subtype.mk_lt_mk.mpr (by norm_num)
  have ht1 : t < 1 := by rw [ht]; exact Subtype.mk_lt_mk.mpr (by norm_num)
  have hinj₁ := hh₁.injective
  have hinj₂ := hh₂.injective
  have hcl : ∀ (h : unitInterval → X), IsEmbedding h → ∀ u v : unitInterval,
      IsClosed (h '' Icc u v) := fun h hh u v =>
    (isCompact_Icc.image hh.continuous).isClosed
  -- a point of both arcs is `a` or `b`
  have hboth : ∀ v w, h₁ v = h₂ w → (v = 0 ∧ w = 0) ∨ (v = 1 ∧ w = 1) := by
    intro v w e
    have : h₁ v ∈ range h₁ ∩ range h₂ := ⟨mem_range_self v, e ▸ mem_range_self w⟩
    rw [hi] at this
    rcases this with h | h
    · left
      exact ⟨hinj₁ (h.trans h₁0.symm), hinj₂ ((e.symm.trans h).trans h₂0.symm)⟩
    · right
      have h : h₁ v = b := h
      exact ⟨hinj₁ (h.trans h₁1.symm), hinj₂ ((e.symm.trans h).trans h₂1.symm)⟩
  -- the general separation: for `u₁, u₂ ∈ (0, 1)`, the two sides
  have sep : ∀ u₁ u₂ : unitInterval, 0 < u₁ → u₁ < 1 → 0 < u₂ → u₂ < 1 →
      ∀ F : Set X, IsPreconnected F → F ⊆ range h₁ ∪ range h₂ → h₁ u₁ ∉ F → h₂ u₂ ∉ F →
      (F ∩ (h₁ '' Icc u₁ 1 ∪ h₂ '' Icc u₂ 1)ᶜ).Nonempty →
      (F ∩ (h₁ '' Icc 0 u₁ ∪ h₂ '' Icc 0 u₂)ᶜ).Nonempty → False := by
    intro u₁ u₂ hu₁0 hu₁1 hu₂0 hu₂1 F hF hFL hq₁ hq₂ hx hy
    have hO₁ : IsOpen (h₁ '' Icc u₁ 1 ∪ h₂ '' Icc u₂ 1)ᶜ :=
      ((hcl h₁ hh₁ _ _).union (hcl h₂ hh₂ _ _)).isOpen_compl
    have hO₂ : IsOpen (h₁ '' Icc 0 u₁ ∪ h₂ '' Icc 0 u₂)ᶜ :=
      ((hcl h₁ hh₁ _ _).union (hcl h₂ hh₂ _ _)).isOpen_compl
    have hcov : F ⊆ (h₁ '' Icc u₁ 1 ∪ h₂ '' Icc u₂ 1)ᶜ ∪ (h₁ '' Icc 0 u₁ ∪ h₂ '' Icc 0 u₂)ᶜ := by
      intro z hz
      rcases hFL hz with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · have hv : v ≠ u₁ := fun e => hq₁ (e ▸ hz)
        rcases lt_or_gt_of_ne hv with hlt | hlt
        · left
          rintro (⟨w, hw, e⟩ | ⟨w, hw, e⟩)
          · exact absurd (hinj₁ e ▸ hw.1) (not_le.mpr hlt)
          · rcases hboth v w e.symm with ⟨-, rfl⟩ | ⟨rfl, -⟩
            · exact absurd hw.1 (not_le.mpr hu₂0)
            · exact absurd hlt (not_lt.mpr le_one')
        · right
          rintro (⟨w, hw, e⟩ | ⟨w, hw, e⟩)
          · exact absurd (hinj₁ e ▸ hw.2) (not_le.mpr hlt)
          · rcases hboth v w e.symm with ⟨rfl, -⟩ | ⟨-, rfl⟩
            · exact absurd hlt (not_lt.mpr nonneg')
            · exact absurd hw.2 (not_le.mpr hu₂1)
      · have hv : v ≠ u₂ := fun e => hq₂ (e ▸ hz)
        rcases lt_or_gt_of_ne hv with hlt | hlt
        · left
          rintro (⟨w, hw, e⟩ | ⟨w, hw, e⟩)
          · rcases hboth w v e with ⟨rfl, -⟩ | ⟨-, rfl⟩
            · exact absurd hw.1 (not_le.mpr hu₁0)
            · exact absurd hlt (not_lt.mpr le_one')
          · exact absurd (hinj₂ e ▸ hw.1) (not_le.mpr hlt)
        · right
          rintro (⟨w, hw, e⟩ | ⟨w, hw, e⟩)
          · rcases hboth w v e with ⟨-, rfl⟩ | ⟨rfl, -⟩
            · exact absurd hlt (not_lt.mpr nonneg')
            · exact absurd hw.2 (not_le.mpr hu₁1)
          · exact absurd (hinj₂ e ▸ hw.2) (not_le.mpr hlt)
    obtain ⟨z, hzF, hz1, hz2⟩ := hF _ _ hO₁ hO₂ hcov hx hy
    apply hz1
    rcases hFL hzF with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rcases le_total v u₁ with h | h
      · exact absurd (Or.inl ⟨v, ⟨nonneg', h⟩, rfl⟩) hz2
      · exact Or.inl ⟨v, ⟨h, le_one'⟩, rfl⟩
    · rcases le_total v u₂ with h | h
      · exact absurd (Or.inr ⟨v, ⟨nonneg', h⟩, rfl⟩) hz2
      · exact Or.inr ⟨v, ⟨h, le_one'⟩, rfl⟩
  refine ⟨(h₁ '' Icc s 1 ∪ h₂ '' Icc s 1)ᶜ, ?_, (h₁ '' Icc 0 t ∪ h₂ '' Icc 0 t)ᶜ, ?_, s, t, hst,
    ?_⟩
  · refine ((hcl h₁ hh₁ _ _).union (hcl h₂ hh₂ _ _)).isOpen_compl.mem_nhds ?_
    rintro (⟨w, hw, e⟩ | ⟨w, hw, e⟩)
    · exact absurd ((hinj₁ (e.trans h₁0.symm)) ▸ hw.1) (not_le.mpr h0s)
    · exact absurd ((hinj₂ (e.trans h₂0.symm)) ▸ hw.1) (not_le.mpr h0s)
  · refine ((hcl h₁ hh₁ _ _).union (hcl h₂ hh₂ _ _)).isOpen_compl.mem_nhds ?_
    rintro (⟨w, hw, e⟩ | ⟨w, hw, e⟩)
    · exact absurd ((hinj₁ (e.trans h₁1.symm)) ▸ hw.2) (not_le.mpr ht1)
    · exact absurd ((hinj₂ (e.trans h₂1.symm)) ▸ hw.2) (not_le.mpr ht1)
  · intro F hF hFL ⟨x, hxF, hxV⟩ ⟨y, hyF, hyV⟩
    by_contra hno
    simp only [not_or, subset_def, not_forall, exists_prop] at hno
    obtain ⟨⟨_, ⟨u₁, hu₁, rfl⟩, hq₁⟩, ⟨_, ⟨u₂, hu₂, rfl⟩, hq₂⟩⟩ := hno
    refine sep u₁ u₂ (lt_of_lt_of_le h0s hu₁.1) (lt_of_le_of_lt hu₁.2 ht1)
      (lt_of_lt_of_le h0s hu₂.1) (lt_of_le_of_lt hu₂.2 ht1) F hF hFL hq₁ hq₂ ⟨x, hxF, ?_⟩
      ⟨y, hyF, ?_⟩
    · intro hx; apply hxV
      rcases hx with ⟨w, hw, e⟩ | ⟨w, hw, e⟩
      · exact Or.inl ⟨w, ⟨hu₁.1.trans hw.1, hw.2⟩, e⟩
      · exact Or.inr ⟨w, ⟨hu₂.1.trans hw.1, hw.2⟩, e⟩
    · intro hy; apply hyV
      rcases hy with ⟨w, hw, e⟩ | ⟨w, hw, e⟩
      · exact Or.inl ⟨w, ⟨hw.1, hw.2.trans hu₁.2⟩, e⟩
      · exact Or.inr ⟨w, ⟨hw.1, hw.2.trans hu₂.2⟩, e⟩

end Gen

variable {S : Type*} {σ : Space S}

/-- **Theorem A** (p. 170). If `L` is a simple closed curve and `M`, `N` are disjoint closed sets,
there is no infinite set of arcs `G` such that (1) each lies on `L`, (2) each contains a point of
`M` and a point of `N`, (3) no two have a segment in common. *Axioms used: 1, 3, 4, 5₁.*
Moore's proof: the limit points `A ∈ M`, `B ∈ N` of a subsequence, the points `C, D, E, F` in the
order `ECADFB` (`Gen.crossing`), and three arcs of which two share the interval `DF` or `EC`.
**Shape changes:** the axioms are made explicit; "infinite set" is an `ℕ`-indexed family, and the
skeleton's injectivity of the family is dropped (the proof does not use it: three indices are
enough, so the statement is stronger without it). -/
theorem m19_theoremA (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S))
    {L : Set S} (hL : σ.IsSCC L) {M N : Set S} (hM : σ.IsClosedM M)
    (hN : σ.IsClosedM N) (hMN : Disjoint M N) :
    ¬ ∃ f : ℕ → Set S,
      (∀ n, (∃ a b, σ.IsArc a b (f n)) ∧ f n ⊆ L ∧ (f n ∩ M).Nonempty ∧ (f n ∩ N).Nonempty) ∧
      ∀ i j, i ≠ j → ¬ σ.ShareSegment (f i) (f j) := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := metrizable h1 h3 h51
  rintro ⟨f, hf, hns⟩
  rw [isClosedM_iff h1] at hM hN
  have hLc : IsCompact L := by
    obtain ⟨A, B, C₁, C₂, hC₁, hC₂, -, rfl⟩ := (isSCC_iff_tscc h1 h3 h4 h51).mp hL
    exact hC₁.isCompact.union hC₂.isCompact
  choose m hm using fun n => (hf n).2.2.1
  choose p hp using fun n => (hf n).2.2.2
  obtain ⟨a, haL, φ, hφ, hma⟩ := hLc.tendsto_subseq (x := m) fun n => (hf n).2.1 (hm n).1
  obtain ⟨b, hbL, ψ, hψ, hpb⟩ := hLc.tendsto_subseq (x := p ∘ φ) fun n => (hf _).2.1 (hp _).1
  set θ := φ ∘ ψ with hθ
  have hθm : StrictMono θ := hφ.comp hψ
  have hma' : Filter.Tendsto (m ∘ θ) Filter.atTop (𝓝 a) := hma.comp hψ.tendsto_atTop
  have hpb' : Filter.Tendsto (p ∘ θ) Filter.atTop (𝓝 b) := hpb
  have haM : a ∈ M := hM.mem_of_tendsto hma' (Filter.Eventually.of_forall fun n => (hm _).2)
  have hbN : b ∈ N := hN.mem_of_tendsto hpb' (Filter.Eventually.of_forall fun n => (hp _).2)
  have hab : a ≠ b := fun e => disjoint_left.mp hMN haM (e ▸ hbN)
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hL haL hbL hab
  obtain ⟨-, h₁, hh₁, rfl, h₁0, h₁1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hD₁
  obtain ⟨-, h₂, hh₂, rfl, h₂0, h₂1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp hD₂
  obtain ⟨Va, hVa, Vb, hVb, s, t, hst, key⟩ := Gen.crossing hh₁ hh₂ h₁0 h₁1 h₂0 h₂1 hDi
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((hma'.eventually hVa).and (hpb'.eventually hVb))
  have side : ∀ n, n₀ ≤ n → h₁ '' Icc s t ⊆ f (θ n) ∨ h₂ '' Icc s t ⊆ f (θ n) := by
    intro n hn
    obtain ⟨a', b', hab'⟩ := (hf (θ n)).1
    refine key _ ((isArc_iff_tarc h1 h3 h4 h51).mp hab').isPreconnected
      (hDu ▸ (hf (θ n)).2.1) ⟨m (θ n), (hm _).1, (hn₀ n hn).1⟩ ⟨p (θ n), (hp _).1, (hn₀ n hn).2⟩
  have share : ∀ (h : unitInterval → S), IsEmbedding h → ∀ i j, i ≠ j →
      h '' Icc s t ⊆ f (θ i) → h '' Icc s t ⊆ f (θ j) → False := by
    intro h hh i j hij hi hj
    refine hns (θ i) (θ j) (hθm.injective.ne hij) ⟨h s, h t, h '' Icc s t,
      (isArc_iff_tarc h1 h3 h4 h51).mpr (TArc.image_Icc hh hst), ?_⟩
    exact fun x hx => ⟨hi hx.1, hj hx.1⟩
  rcases side n₀ le_rfl with h0 | h0 <;> rcases side (n₀ + 1) (by omega) with h1' | h1'
  · exact share h₁ hh₁ n₀ (n₀ + 1) (by omega) h0 h1'
  · rcases side (n₀ + 2) (by omega) with h2' | h2'
    · exact share h₁ hh₁ n₀ (n₀ + 2) (by omega) h0 h2'
    · exact share h₂ hh₂ (n₀ + 1) (n₀ + 2) (by omega) h1' h2'
  · rcases side (n₀ + 2) (by omega) with h2' | h2'
    · exact share h₁ hh₁ (n₀ + 1) (n₀ + 2) (by omega) h1' h2'
    · exact share h₂ hh₂ n₀ (n₀ + 2) (by omega) h0 h2'
  · exact share h₂ hh₂ n₀ (n₀ + 1) (by omega) h0 h1'

end HPC.Moore
