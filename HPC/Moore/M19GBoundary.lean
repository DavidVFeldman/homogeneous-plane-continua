import HPC.Moore.M19ESchoenflies
import HPC.Moore.M19GSquare

/-!
# Moore 1919: Schoenflies with prescribed boundary (batch 144, item A)

`m19_schoenflies_param`: the construction of batch 143 (`m19_schoenflies_proof`), run with given
parametrizations `fA` of `AB` and `fB` of `BC`, restricts to them on the two sides: by
`HPC.Sq.Grid.exists_square_param`. The proof is that of batch 143 with its last step replaced.

`m19_schoenflies_boundary_proof`: all four sides prescribed, by composing with a homeomorphism of
the square fixing the sides `p.1 = 0` and `p.2 = 1` pointwise (`HPC.Sq.exists_square_reparam`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

section Boundary

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Schoenflies with two sides prescribed.** As `m19_schoenflies_proof`, for given
parametrizations `fA` of `AB` (from `A` to `B`) and `fB` of `BC` (from `B` to `C`), with
`f (0, y) = fA y` and `f (x, 1) = fB x`. *Axioms used: 1–8.* -/
theorem m19_schoenflies_param (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    {fA fB : unitInterval → S}
    (hfA : @IsEmbedding _ _ _ σ.topology fA) (hfAr : range fA = sAB) (hfA0 : fA 0 = A)
    (hfA1 : fA 1 = B)
    (hfB : @IsEmbedding _ _ _ σ.topology fB) (hfBr : range fB = sBC) (hfB0 : fB 0 = B)
    (hfB1 : fB 1 = C) :
    ∃ f : unitInterval × unitInterval → S, @IsEmbedding _ _ _ σ.topology f ∧ range f = J ∪ I ∧
      (∀ y, f (0, y) = fA y) ∧ (∀ x, f (x, 1) = fB x) ∧
      ∀ p, ((p.1 = 0 ↔ f p ∈ sAB) ∧ (p.1 = 1 ↔ f p ∈ sCD) ∧ (p.2 = 0 ↔ f p ∈ sDA) ∧
        (p.2 = 1 ↔ f p ∈ sBC)) := by
  letI τ := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  haveI hmet := metrizable h1 h3 h51
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
  obtain ⟨f, hf, hfr, hside, hφ, hψ⟩ := g.exists_square_param hcpt
  have s1 : ∀ p, p.1 = 0 ↔ f p ∈ sAB := fun p => Set.Icc.coe_eq_zero.symm.trans (hside p).1
  have s2 : ∀ p, p.1 = 1 ↔ f p ∈ sCD := fun p => Set.Icc.coe_eq_one.symm.trans (hside p).2.1
  have s3 : ∀ p, p.2 = 0 ↔ f p ∈ sDA := fun p =>
    Set.Icc.coe_eq_zero.symm.trans (hside p).2.2.1
  have s4 : ∀ p, p.2 = 1 ↔ f p ∈ sBC := fun p =>
    Set.Icc.coe_eq_one.symm.trans (hside p).2.2.2
  have tφ : g.FY.t g.kφ = 0 := g.FY.t_i0
  have tψ : g.FX.t g.iψ = 1 := g.FX.t_i1
  refine ⟨f, hf, hfr, fun y => ?_, fun x => ?_, fun p => ⟨s1 p, s2 p, s3 p, s4 p⟩⟩
  · have := hφ (0, y) (by rw [tφ]; rfl)
    rw [this]
    show fA (projIcc 0 1 zero_le_one (y : ℝ)) = fA y
    rw [projIcc_val]
  · have := hψ (x, 1) (by rw [tψ]; rfl)
    rw [this]
    show fB (projIcc 0 1 zero_le_one (x : ℝ)) = fB x
    rw [projIcc_val]

/-- **Schoenflies with prescribed boundary** (item A). Given parametrizations of the four sides
(`φAB` from `A` to `B`, `φBC` from `B` to `C`, `φDC` from `D` to `C`, `φAD` from `A` to `D`), the
embedding of the square restricts to them: `f (0, y) = φAB y`, `f (x, 1) = φBC x`,
`f (1, y) = φDC y`, `f (x, 0) = φAD x`. *Axioms used: 1–8.* -/
theorem m19_schoenflies_boundary_proof (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (φAB φBC φDC φAD : unitInterval → S)
    (hAB : @IsEmbedding _ _ _ σ.topology φAB ∧ range φAB = sAB ∧ φAB 0 = A ∧ φAB 1 = B)
    (hBC : @IsEmbedding _ _ _ σ.topology φBC ∧ range φBC = sBC ∧ φBC 0 = B ∧ φBC 1 = C)
    (hDC : @IsEmbedding _ _ _ σ.topology φDC ∧ range φDC = sCD ∧ φDC 0 = D ∧ φDC 1 = C)
    (hAD : @IsEmbedding _ _ _ σ.topology φAD ∧ range φAD = sDA ∧ φAD 0 = A ∧ φAD 1 = D) :
    ∃ f : unitInterval × unitInterval → S, @IsEmbedding _ _ _ σ.topology f ∧ range f = J ∪ I ∧
      (∀ y, f (0, y) = φAB y) ∧ (∀ x, f (x, 1) = φBC x) ∧ (∀ y, f (1, y) = φDC y) ∧
      (∀ x, f (x, 0) = φAD x) := by
  letI := σ.topology
  obtain ⟨f, hf, hfr, hf0, hf1, hside⟩ := m19_schoenflies_param h1 h2 h3 h4 h5 h6 h7 h8 q
    hAB.1 hAB.2.1 hAB.2.2.1 hAB.2.2.2 hBC.1 hBC.2.1 hBC.2.2.1 hBC.2.2.2
  set e := hf.toHomeomorph with he
  -- lifting a parametrization of a part of `J ∪ I` through `f`
  have lift : ∀ φ : unitInterval → S, Continuous φ → (∀ y, φ y ∈ J ∪ I) →
      ∃ g : unitInterval → unitInterval × unitInterval, Continuous g ∧ ∀ y, f (g y) = φ y := by
    intro φ hφ hmem
    refine ⟨fun y => e.symm ⟨φ y, hfr ▸ hmem y⟩, e.symm.continuous.comp
      (hφ.subtype_mk _), fun y => ?_⟩
    have := congrArg Subtype.val (e.apply_symm_apply ⟨φ y, hfr ▸ hmem y⟩)
    exact this
  have hJ : ∀ {s : Set S}, s ⊆ J → ∀ φ : unitInterval → S, range φ = s → ∀ y, φ y ∈ J ∪ I :=
    fun hs φ hr y => Or.inl (hs (hr ▸ mem_range_self y))
  obtain ⟨gC, hgC, hgCe⟩ := lift φDC hDC.1.continuous (hJ q.sCD_sub φDC hDC.2.1)
  obtain ⟨gD, hgD, hgDe⟩ := lift φAD hAD.1.continuous (hJ q.sDA_sub φAD hAD.2.1)
  have gC1 : ∀ y, (gC y).1 = 1 := fun y =>
    (hside _).2.1.mpr (by rw [hgCe]; exact hDC.2.1 ▸ mem_range_self y)
  have gD2 : ∀ x, (gD x).2 = 0 := fun x =>
    (hside _).2.2.1.mpr (by rw [hgDe]; exact hAD.2.1 ▸ mem_range_self x)
  set a : unitInterval → unitInterval := fun y => (gC y).2
  set b : unitInterval → unitInterval := fun x => (gD x).1
  have ea : ∀ y, gC y = (1, a y) := fun y => Prod.ext (gC1 y) rfl
  have eb : ∀ x, gD x = (b x, 0) := fun x => Prod.ext rfl (gD2 x)
  have corner : ∀ {s t : Set S} {P : S} {p : unitInterval × unitInterval}, s ∩ t = {P} →
      f p ∈ s → f p ∈ t → f p = P := by
    intro s t P p h hs ht
    have : f p ∈ s ∩ t := ⟨hs, ht⟩
    rw [h] at this; exact this
  have fD : f (1, 0) = D := corner q.cd_da ((hside _).2.1.mp rfl) ((hside _).2.2.1.mp rfl)
  have fC : f (1, 1) = C := corner q.bc_cd ((hside _).2.2.2.mp rfl) ((hside _).2.1.mp rfl)
  have fA' : f (0, 0) = A := corner q.da_ab ((hside _).2.2.1.mp rfl) ((hside _).1.mp rfl)
  have ha0 : a 0 = 0 := by
    have : f (gC 0) = f (1, 0) := by rw [hgCe, fD, hDC.2.2.1]
    have := hf.injective this; rw [ea] at this; exact (Prod.ext_iff.mp this).2
  have ha1 : a 1 = 1 := by
    have : f (gC 1) = f (1, 1) := by rw [hgCe, fC, hDC.2.2.2]
    have := hf.injective this; rw [ea] at this; exact (Prod.ext_iff.mp this).2
  have hb0 : b 0 = 0 := by
    have : f (gD 0) = f (0, 0) := by rw [hgDe, fA', hAD.2.2.1]
    have := hf.injective this; rw [eb] at this; exact (Prod.ext_iff.mp this).1
  have hb1 : b 1 = 1 := by
    have : f (gD 1) = f (1, 0) := by rw [hgDe, fD, hAD.2.2.2]
    have := hf.injective this; rw [eb] at this; exact (Prod.ext_iff.mp this).1
  have hainj : Function.Injective a := by
    intro y y' h
    apply hDC.1.injective
    rw [← hgCe, ← hgCe, ea, ea, h]
  have hbinj : Function.Injective b := by
    intro x x' h
    apply hAD.1.injective
    rw [← hgDe, ← hgDe, eb, eb, h]
  obtain ⟨H, H0, H1, Ha, Hb⟩ := HPC.Sq.exists_square_reparam (continuous_snd.comp hgC) hainj
    ha0 ha1 (continuous_fst.comp hgD) hbinj hb0 hb1
  refine ⟨f ∘ H, hf.comp H.isEmbedding, by rw [range_comp, H.range_coe, image_univ, hfr],
    fun y => ?_, fun x => ?_, fun y => ?_, fun x => ?_⟩
  · simp only [Function.comp_apply, H0, hf0]
  · simp only [Function.comp_apply, H1, hf1]
  · show f (H (1, y)) = φDC y
    rw [Ha, ← hgCe y, ea y]; rfl
  · show f (H (x, 0)) = φAD x
    rw [Hb, ← hgDe x, eb x]; rfl

end Boundary

end HPC.Moore
