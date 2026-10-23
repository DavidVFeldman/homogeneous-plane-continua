import HPC.Moore.M19EMesh

/-!
# Moore 1919, Theorem E: the Schoenflies form (batch 143, item B)

The nested double rulings `β₁, β₂, …` of Theorem E (`nested_rulings`), with the `k`-th ruling's
subdivisions inside regions of diameter less than `2/(k+1)` (for a metric of the space, which is
metrizable), give two families of cross-cuts: `ᾱ₁` (all arcs from `AB` to `CD` of all `βₖ`) and
`ᾱ₂` (all arcs from `BC` to `DA`). With the sides they form a grid (`preGrid`) whose mesh tends to
`0` (`preGrid_box_sub_cell`), and a compact set carrying such a grid is a square
(`HPC.Sq.Grid.exists_square`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- Arcs of earlier rulings persist. -/
theorem stage_mono {T : ℕ → Type*} {F : ∀ k, T k → Set S}
    (h : ∀ k i, ∃ i', F (k + 1) i' = F k i) {a b : ℕ} (hab : a ≤ b) :
    range (F a) ⊆ range (F b) := by
  induction b, hab using Nat.le_induction with
  | base => exact subset_rfl
  | succ b _ ih =>
    refine ih.trans ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨i', hi'⟩ := h b i
    exact ⟨i', hi'⟩

section Schoenflies

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **The Schoenflies form of Theorem E.** `ABCDA` together with its interior is homeomorphic to
the closed unit square, with `AB`, `BC`, `CD`, `DA` going to the sides `p.1 = 0`, `p.2 = 1`,
`p.1 = 1`, `p.2 = 0`. *Axioms used: 1–8.* -/
theorem m19_schoenflies_proof (q : σ.Quad J I A B C D sAB sBC sCD sDA) :
    ∃ f : unitInterval × unitInterval → S, @IsEmbedding _ _ _ σ.topology f ∧ range f = J ∪ I ∧
      f (0, 0) = A ∧ f (0, 1) = B ∧ f (1, 1) = C ∧ f (1, 0) = D ∧
      f '' {p | p.1 = 0} = sAB ∧ f '' {p | p.2 = 1} = sBC ∧ f '' {p | p.1 = 1} = sCD ∧
      f '' {p | p.2 = 0} = sDA := by
  letI τ := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  haveI hmet := metrizable h1 h3 h51
  obtain ⟨-, fA, hfA, hfAr, hfA0, hfA1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp q.ab
  obtain ⟨-, fB, hfB, hfBr, hfB0, hfB1⟩ := (isArc_iff_tarc h1 h3 h4 h51).mp q.bc
  obtain ⟨-, -, -, -, -, -, -, -, hclI, hIJ, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  have hcpt : IsCompact (J ∪ I) := by
    rw [union_comm, ← hclI]; exact isCompact_closure_region h1 h4 q.interior.2.1
  letI M : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  -- the covers by small regions
  let 𝒢 : ℕ → Set (Set S) := fun k =>
    {V | V ∈ σ.region ∧ ∃ c, V ⊆ Metric.ball c (1 / ((k : ℝ) + 1))}
  have hcov : ∀ k (P : S), ∃ V ∈ 𝒢 k, P ∈ V := by
    intro k P
    have hb : Metric.ball P (1 / ((k : ℝ) + 1)) ∈ @nhds S τ P :=
      Metric.ball_mem_nhds P (by positivity)
    obtain ⟨V, hV, hPV, hVb⟩ := (mem_nhds_iff_region h1).mp hb
    exact ⟨V, ⟨hV, P, hVb⟩, hPV⟩
  obtain ⟨R, hRc, hRX, hRY, -⟩ := nested_rulings h1 h2 h3 h4 h5 h6 h7 h8 q 𝒢
    (fun k V hV => hV.1) hcov
  have monoX : ∀ {a b}, a ≤ b → range (R a).2.2.arcX ⊆ range (R b).2.2.arcX := fun hab =>
    stage_mono (F := fun k => (R k).2.2.arcX) hRX hab
  have monoY : ∀ {a b}, a ≤ b → range (R a).2.2.arcY ⊆ range (R b).2.2.arcY := fun hab =>
    stage_mono (F := fun k => (R k).2.2.arcY) hRY hab
  let 𝒜X : Set (Set S) := ⋃ k, range (R k).2.2.arcX
  let 𝒜Y : Set (Set S) := ⋃ k, range (R k).2.2.arcY
  have AR : ∀ k, σ.ArcRuling I sAB sBC sCD sDA A B C D (range (R k).2.2.arcX)
      (range (R k).2.2.arcY) := fun k => (R k).2.2.toArcRuling h1 h3 h4 h5
  have h𝒜X : ∀ x ∈ 𝒜X, σ.XArc I sAB sCD A B C D x := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact (AR k).arcX x hk
  have h𝒜Y : ∀ y ∈ 𝒜Y, σ.XArc I sBC sDA B C D A y := by
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    exact (AR k).arcY y hk
  have hdX : 𝒜X.Pairwise Disjoint := by
    intro x hx y hy hxy
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    exact (AR (max a b)).disjX (monoX (le_max_left a b) ha) (monoX (le_max_right a b) hb) hxy
  have hdY : 𝒜Y.Pairwise Disjoint := by
    intro x hx y hy hxy
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    exact (AR (max a b)).disjY (monoY (le_max_left a b) ha) (monoY (le_max_right a b) hb) hxy
  have hcross : ∀ x ∈ 𝒜X, ∀ y ∈ 𝒜Y, ∃! P, P ∈ x ∩ y := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    exact (AR (max a b)).cross x (monoX (le_max_left a b) ha) y (monoY (le_max_right a b) hb)
  set pg := preGrid h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 hfB hfBr hfB0 hfB1 𝒜X h𝒜X hdX
    𝒜Y h𝒜Y hdY hcross with hpg
  have lX : ∀ i, pg.FX.line i = lfLine sDA sBC 𝒜X i :=
    lineFam_line h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 𝒜X h𝒜X hdX
  have lY : ∀ k, pg.FY.line k = lfLine sAB sCD 𝒜Y k :=
    lineFam_line h1 h2 h3 h4 h5 h7 h8 q.rot hfB hfBr hfB0 hfB1 𝒜Y h𝒜Y hdY
  have hproj : ∀ s ∈ Icc (0 : ℝ) 1, ((projIcc (0 : ℝ) 1 zero_le_one s : unitInterval) : ℝ) = s :=
    fun s hs => by rw [projIcc_of_mem _ hs]
  have injP : ∀ {h : unitInterval → S}, Function.Injective h →
      InjOn (fun s => h (projIcc 0 1 zero_le_one s)) (Icc 0 1) := by
    intro h hh s hs s' hs' e
    have := congrArg Subtype.val (hh e)
    rwa [hproj s hs, hproj s' hs'] at this
  have stX : ∀ i : Option (Option 𝒜X), ∃ a, ∀ b, a ≤ b → i = none ∨ i = some none ∨
      ∃ i', i = some (some ⟨(R b).2.2.arcX i', mem_iUnion.mpr ⟨b, i', rfl⟩⟩) := by
    intro i
    match i with
    | none => exact ⟨0, fun _ _ => Or.inl rfl⟩
    | some none => exact ⟨0, fun _ _ => Or.inr (Or.inl rfl)⟩
    | some (some ⟨x, hx⟩) =>
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      refine ⟨a, fun b hab => Or.inr (Or.inr ?_)⟩
      obtain ⟨i', hi'⟩ := monoX hab ha
      exact ⟨i', by subst hi'; rfl⟩
  have stY : ∀ k : Option (Option 𝒜Y), ∃ a, ∀ b, a ≤ b → k = none ∨ k = some none ∨
      ∃ j', k = some (some ⟨(R b).2.2.arcY j', mem_iUnion.mpr ⟨b, j', rfl⟩⟩) := by
    intro k
    match k with
    | none => exact ⟨0, fun _ _ => Or.inl rfl⟩
    | some none => exact ⟨0, fun _ _ => Or.inr (Or.inl rfl)⟩
    | some (some ⟨y, hy⟩) =>
      obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      refine ⟨a, fun b hab => Or.inr (Or.inr ?_)⟩
      obtain ⟨j', hj'⟩ := monoY hab ha
      exact ⟨j', by subst hj'; rfl⟩
  let g : HPC.Sq.Grid (Option (Option 𝒜X)) (Option (Option 𝒜Y)) (J ∪ I) :=
    { toPreGrid := pg
      φ := fun s => fA (projIcc 0 1 zero_le_one s)
      kφ := none
      φ_inj := injP hfA.injective
      φ_line := fun s _ => by rw [lY]; exact hfAr ▸ mem_range_self _
      φ_L := fun s hs i => by
        have := lineFam_fL h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 𝒜X h𝒜X
          (projIcc 0 1 zero_le_one s) i
        rw [hproj s hs] at this; exact this
      φ_R := fun s hs i => by
        have := lineFam_fR h1 h2 h3 h4 h5 h7 h8 q hfA hfAr hfA0 hfA1 𝒜X h𝒜X
          (projIcc 0 1 zero_le_one s) i
        rw [hproj s hs] at this; exact this
      ψ := fun s => fB (projIcc 0 1 zero_le_one s)
      iψ := some none
      ψ_inj := injP hfB.injective
      ψ_line := fun s _ => by rw [lX]; exact hfBr ▸ mem_range_self _
      ψ_L := fun s hs k => by
        have := lineFam_fL h1 h2 h3 h4 h5 h7 h8 q.rot hfB hfBr hfB0 hfB1 𝒜Y h𝒜Y
          (projIcc 0 1 zero_le_one s) k
        rw [hproj s hs] at this; exact this
      ψ_R := fun s hs k => by
        have := lineFam_fR h1 h2 h3 h4 h5 h7 h8 q.rot hfB hfBr hfB0 hfB1 𝒜Y h𝒜Y
          (projIcc 0 1 zero_le_one s) k
        rw [hproj s hs] at this; exact this
      mesh := by
        intro ε hε i k
        obtain ⟨N0, hN0⟩ := exists_nat_gt (2 / ε)
        obtain ⟨a, ha⟩ := stX i
        obtain ⟨b, hb⟩ := stY k
        set N := max (max a b) N0
        obtain ⟨G, H, hG0, hG1, hGX, hH0, hH1, hHY, hbox⟩ := preGrid_box_sub_cell h1 h2 h3 h4 h5
          h7 h8 q hfA hfAr hfA0 hfA1 hfB hfBr hfB0 hfB1 𝒜X h𝒜X hdX 𝒜Y h𝒜Y hdY hcross (R N).2.2
          (fun i => mem_iUnion.mpr ⟨N, i, rfl⟩) (fun j => mem_iUnion.mpr ⟨N, j, rfl⟩)
        have hiG : i ∈ G := by
          rcases ha N (le_trans (le_max_left a b) (le_max_left _ _)) with rfl | rfl | ⟨i', rfl⟩
          · exact hG0
          · exact hG1
          · exact hGX i'
        have hkH : k ∈ H := by
          rcases hb N (le_trans (le_max_right a b) (le_max_left _ _)) with rfl | rfl | ⟨j', rfl⟩
          · exact hH0
          · exact hH1
          · exact hHY j'
        refine ⟨G, H, hiG, hG0, hG1, hkH, hH0, hH1, fun j j' hc m m' hc' z hz w hw => ?_⟩
        obtain ⟨U, hU, hbU⟩ := hbox j j' hc m m' hc'
        obtain ⟨V, ⟨-, c, hVc⟩, hUV⟩ := hRc N U hU
        have hsub : closure (HPC.Sq.box pg.FX pg.FY j j' m m') ⊆
            Metric.closedBall c (1 / ((N : ℝ) + 1)) :=
          (closure_mono (hbU.trans (hUV.trans hVc))).trans Metric.closure_ball_subset_closedBall
        have hz' := hsub hz
        have hw' := hsub hw
        rw [Metric.mem_closedBall] at hz' hw'
        have hN1 : (0 : ℝ) < N + 1 := by positivity
        have hNN : (N0 : ℝ) ≤ N := by exact_mod_cast le_max_right _ _
        have h2 : 2 < ((N : ℝ) + 1) * ε := by
          rw [div_lt_iff₀ hε] at hN0; nlinarith
        calc dist z w ≤ dist z c + dist w c := dist_triangle_right z w c
          _ ≤ 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := add_le_add hz' hw'
          _ = 2 / ((N : ℝ) + 1) := by ring
          _ ≤ ε := by rw [div_le_iff₀ hN1]; linarith }
  obtain ⟨f, hf, hfr, hside⟩ := g.exists_square hcpt
  have s1 : ∀ p, p.1 = 0 ↔ f p ∈ sAB := fun p => Set.Icc.coe_eq_zero.symm.trans (hside p).1
  have s2 : ∀ p, p.1 = 1 ↔ f p ∈ sCD := fun p => Set.Icc.coe_eq_one.symm.trans (hside p).2.1
  have s3 : ∀ p, p.2 = 0 ↔ f p ∈ sDA := fun p =>
    Set.Icc.coe_eq_zero.symm.trans (hside p).2.2.1
  have s4 : ∀ p, p.2 = 1 ↔ f p ∈ sBC := fun p =>
    Set.Icc.coe_eq_one.symm.trans (hside p).2.2.2
  have hK : ∀ z ∈ J, z ∈ range f := fun z hz => hfr ▸ Or.inl hz
  have side : ∀ {s : Set S} {P : unitInterval × unitInterval → Prop}, s ⊆ J →
      (∀ p, P p ↔ f p ∈ s) → f '' {p | P p} = s := by
    intro s P hs hP
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩; exact (hP p).mp hp
    · intro hz
      obtain ⟨p, rfl⟩ := hK z (hs hz)
      exact ⟨p, (hP p).mpr hz, rfl⟩
  have corner : ∀ {s t : Set S} {P : S} (p : unitInterval × unitInterval), s ∩ t = {P} →
      f p ∈ s → f p ∈ t → f p = P := by
    intro s t P p h hs ht
    have : f p ∈ s ∩ t := ⟨hs, ht⟩
    rw [h] at this; exact this
  refine ⟨f, hf, hfr, ?_, ?_, ?_, ?_, side q.sAB_sub s1, side q.sBC_sub s4, side q.sCD_sub s2,
    side q.sDA_sub s3⟩
  · exact corner _ q.da_ab ((s3 _).mp rfl) ((s1 _).mp rfl)
  · exact corner _ q.ab_bc ((s1 _).mp rfl) ((s4 _).mp rfl)
  · exact corner _ q.bc_cd ((s4 _).mp rfl) ((s2 _).mp rfl)
  · exact corner _ q.cd_da ((s2 _).mp rfl) ((s3 _).mp rfl)

end Schoenflies

end HPC.Moore
