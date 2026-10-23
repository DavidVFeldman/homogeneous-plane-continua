import HPC.Moore.GridSquare

/-!
# A compact grid is a square, with the parametrized lines going to sides (batch 144, item A)

Pure topology. `HPC.Sq.Grid.exists_square` (batch 143) gives an embedding of the unit square onto a
compact set carrying a grid, sending positions to coordinates. Here the same embedding is shown to
restrict to the grid's two parametrizations: `f (t_{kφ}, s) = φ s` and `f (s, t_{iψ}) = ψ s`
(`Grid.exists_square_param`). Starting point: `Grid.mem_L_of_pos_eq`, through the position of
`φ s`, which is `s` (`Grid.pos_phi`).

Also: homeomorphisms of the square fixing two opposite sides pointwise
(`exists_square_reparam`), used to prescribe the two remaining sides.
-/

namespace HPC.Sq

open Set Topology Metric Filter

section Met

variable {X : Type*} [MetricSpace X]

namespace Grid

variable {ιX ιY : Type*} {K : Set X} (g : Grid ιX ιY K)

/-- The position of `φ s` in the first family is `s`. -/
theorem pos_phi {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : g.FX.pos (g.φ s) = s := by
  have hK : g.φ s ∈ K := g.FY.L_sub _ (g.φ_line s hs).1
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨i, hi1, hi2⟩ := g.dense_t (g.FX.pos_nonneg _) h hs.2
    have := g.FX.le_pos hK ((g.φ_R s hs i).mpr hi2.le)
    linarith
  · obtain ⟨i, hi1, hi2⟩ := g.dense_t hs.1 h (g.FX.pos_le_one hK)
    have := g.FX.pos_le ((g.φ_L s hs i).mpr hi1.le)
    linarith

/-- The position of `ψ s` in the second family is `s`. -/
theorem pos_psi {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : g.FY.pos (g.ψ s) = s :=
  g.swap.pos_phi hs

end Grid

/-- **A compact grid is a square, with prescribed parametrizations on two lines.** As
`Grid.exists_square`, and moreover `f p = φ p.2` when `p.1` is the position of the line `kφ`, and
`f p = ψ p.1` when `p.2` is the position of the line `iψ`. -/
theorem Grid.exists_square_param {ιX ιY : Type*} {K : Set X} (g : Grid ιX ιY K)
    (hK : IsCompact K) :
    ∃ f : unitInterval × unitInterval → X, IsEmbedding f ∧ range f = K ∧
      (∀ p, (((p.1 : ℝ) = 0 ↔ f p ∈ g.FY.L g.FY.i0) ∧ ((p.1 : ℝ) = 1 ↔ f p ∈ g.FY.R g.FY.i1) ∧
        ((p.2 : ℝ) = 0 ↔ f p ∈ g.FX.L g.FX.i0) ∧ ((p.2 : ℝ) = 1 ↔ f p ∈ g.FX.R g.FX.i1))) ∧
      (∀ p : unitInterval × unitInterval, (p.1 : ℝ) = g.FY.t g.kφ → f p = g.φ p.2) ∧
      (∀ p : unitInterval × unitInterval, (p.2 : ℝ) = g.FX.t g.iψ → f p = g.ψ p.1) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Φ : K → unitInterval × unitInterval := fun z =>
    (⟨g.FY.pos z, g.FY.pos_nonneg z, g.FY.pos_le_one z.2⟩,
      ⟨g.FX.pos z, g.FX.pos_nonneg z, g.FX.pos_le_one z.2⟩)
  have hΦc : Continuous Φ := by
    refine Continuous.prodMk ?_ ?_
    · exact (g.swap.continuousOn_pos.restrict).subtype_mk _
    · exact (g.continuousOn_pos.restrict).subtype_mk _
  have hΦi : Function.Injective Φ := by
    rintro ⟨z, hz⟩ ⟨w, hw⟩ h
    simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (g.eq_of_pos_eq hz hw h.2 h.1)
  have hΦs : Function.Surjective Φ := by
    rintro ⟨u, s⟩
    obtain ⟨z, hz, hzp⟩ : ((u : ℝ), (s : ℝ)) ∈ (fun z => (g.FY.pos z, g.FX.pos z)) '' K := by
      rw [g.image_pos hK]; exact ⟨u.2, s.2⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    simp only [Prod.mk.injEq] at hzp
    simp only [Φ]
    ext
    · exact hzp.1
    · exact hzp.2
  let h := hΦc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective Φ ⟨hΦi, hΦs⟩)
  have hh : ∀ z, h z = Φ z := fun z => rfl
  have key : ∀ (p : unitInterval × unitInterval) (z : K), Φ z = p → (h.symm p : X) = z := by
    intro p z hz
    rw [← hz, ← hh, h.symm_apply_apply]
  refine ⟨Subtype.val ∘ h.symm, IsEmbedding.subtypeVal.comp h.symm.isEmbedding, ?_, fun p => ?_,
    fun p hp => ?_, fun p hp => ?_⟩
  · rw [range_comp, h.symm.range_coe, image_univ, Subtype.range_coe]
  · have hp : Φ (h.symm p) = p := h.apply_symm_apply p
    set z := h.symm p
    have h1 : g.FY.pos z = p.1 := congrArg (fun q : unitInterval × unitInterval => (q.1 : ℝ)) hp
    have h2 : g.FX.pos z = p.2 := congrArg (fun q : unitInterval × unitInterval => (q.2 : ℝ)) hp
    simp only [Function.comp_apply]
    refine ⟨⟨fun e => ?_, fun e => ?_⟩, ⟨fun e => ?_, fun e => ?_⟩, ⟨fun e => ?_, fun e => ?_⟩,
      ⟨fun e => ?_, fun e => ?_⟩⟩
    · exact g.swap.mem_L_of_pos_eq z.2 (show g.FY.pos z = g.FY.t g.FY.i0 by rw [h1, e, g.FY.t_i0])
    · have := g.FY.pos_le e; rw [g.FY.t_i0] at this
      rw [← h1]; exact le_antisymm this (g.FY.pos_nonneg _)
    · exact g.swap.mem_R_of_pos_eq z.2 (show g.FY.pos z = g.FY.t g.FY.i1 by rw [h1, e, g.FY.t_i1])
    · have := g.FY.le_pos z.2 e; rw [g.FY.t_i1] at this
      rw [← h1]; exact le_antisymm (g.FY.pos_le_one z.2) this
    · exact g.mem_L_of_pos_eq z.2 (show g.FX.pos z = g.FX.t g.FX.i0 by rw [h2, e, g.FX.t_i0])
    · have := g.FX.pos_le e; rw [g.FX.t_i0] at this
      rw [← h2]; exact le_antisymm this (g.FX.pos_nonneg _)
    · exact g.mem_R_of_pos_eq z.2 (show g.FX.pos z = g.FX.t g.FX.i1 by rw [h2, e, g.FX.t_i1])
    · have := g.FX.le_pos z.2 e; rw [g.FX.t_i1] at this
      rw [← h2]; exact le_antisymm (g.FX.pos_le_one z.2) this
  · have hs : (p.2 : ℝ) ∈ Icc (0 : ℝ) 1 := p.2.2
    have hl := g.φ_line _ hs
    have hK : g.φ p.2 ∈ K := g.FY.L_sub _ hl.1
    refine key p ⟨_, hK⟩ ?_
    ext
    · exact (g.FY.pos_eq_of_mem_line hK hl).trans hp.symm
    · exact g.pos_phi hs
  · have hs : (p.1 : ℝ) ∈ Icc (0 : ℝ) 1 := p.1.2
    have hl := g.ψ_line _ hs
    have hK : g.ψ p.1 ∈ K := g.FX.L_sub _ hl.1
    refine key p ⟨_, hK⟩ ?_
    ext
    · exact g.pos_psi hs
    · exact (g.FX.pos_eq_of_mem_line hK hl).trans hp.symm

end Met

end HPC.Sq

namespace HPC.Sq

open Set Topology unitInterval

/-- The fibrewise interpolation `(x, y) ↦ (x, (1 - w x) y + w x · a y)` between the identity and a
homeomorphism `a` of `[0, 1]` fixing `0` and `1`. -/
noncomputable def interp (w a : I → I) (p : I × I) : I × I :=
  (p.1, ⟨(1 - (w p.1 : ℝ)) * p.2 + w p.1 * a p.2, by
    have := (w p.1).2; have := p.2.2; have := (a p.2).2
    obtain ⟨h1, h2⟩ := (w p.1).2; obtain ⟨h3, h4⟩ := p.2.2; obtain ⟨h5, h6⟩ := (a p.2).2
    constructor <;> nlinarith⟩)

theorem interp_continuous {w a : I → I} (hw : Continuous w) (ha : Continuous a) :
    Continuous (interp w a) := by
  refine continuous_fst.prodMk (Continuous.subtype_mk ?_ _)
  have h1 : Continuous fun p : I × I => (w p.1 : ℝ) := continuous_subtype_val.comp
    (hw.comp continuous_fst)
  have h2 : Continuous fun p : I × I => (p.2 : ℝ) := continuous_subtype_val.comp continuous_snd
  have h3 : Continuous fun p : I × I => (a p.2 : ℝ) := continuous_subtype_val.comp
    (ha.comp continuous_snd)
  exact ((continuous_const.sub h1).mul h2).add (h1.mul h3)

theorem interp_bijective {w a : I → I} (ha : Continuous a) (hmono : StrictMono a)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1) : Function.Bijective (interp w a) := by
  have smono : ∀ x : I, StrictMono fun y : I => (1 - (w x : ℝ)) * y + w x * a y := by
    intro x y y' hyy'
    have hy : (y : ℝ) < y' := hyy'
    have hay : (a y : ℝ) < a y' := hmono hyy'
    obtain ⟨h1, h2⟩ := (w x).2
    rcases h2.lt_or_eq with h | h
    · nlinarith
    · simp only [h]; nlinarith
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [interp, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact Prod.ext rfl ((smono x).injective h)
  · rintro ⟨x, v⟩
    have hc : ContinuousOn (fun y : I => (1 - (w x : ℝ)) * y + w x * a y) (Icc 0 1) :=
      (((continuous_const.mul continuous_subtype_val).add
        (continuous_const.mul (continuous_subtype_val.comp ha)))).continuousOn
    have hv : (v : ℝ) ∈ Icc ((1 - (w x : ℝ)) * (0 : I) + w x * a 0)
        ((1 - (w x : ℝ)) * (1 : I) + w x * a 1) := by
      rw [ha0, ha1]; simp only [Icc.coe_zero, Icc.coe_one]; constructor <;> nlinarith [v.2.1, v.2.2]
    obtain ⟨y, -, hy⟩ := intermediate_value_Icc (zero_le_one' I) hc hv
    exact ⟨(x, y), Prod.ext rfl (Subtype.ext hy)⟩

theorem interp_fst (w a : I → I) (p : I × I) : (interp w a p).1 = p.1 := rfl

theorem interp_of_w0 {w a : I → I} {p : I × I} (h : w p.1 = 0) : interp w a p = p := by
  ext <;> simp [interp, h]

theorem interp_of_w1 {w a : I → I} {p : I × I} (h : w p.1 = 1) : interp w a p = (p.1, a p.2) := by
  ext <;> simp [interp, h]

theorem interp_of_y0 {w a : I → I} (ha0 : a 0 = 0) (x : I) : interp w a (x, 0) = (x, 0) := by
  ext <;> simp [interp, ha0]

theorem interp_of_y1 {w a : I → I} (ha1 : a 1 = 1) (x : I) : interp w a (x, 1) = (x, 1) := by
  ext <;> simp [interp, ha1]

/-- **Homeomorphisms of the square fixing two sides.** Given homeomorphisms `a`, `b` of `[0, 1]`
fixing `0` and `1` (continuous injective maps), there is a homeomorphism `H` of the square with
`H (0, y) = (0, y)`, `H (x, 1) = (x, 1)`, `H (1, y) = (1, a y)` and `H (x, 0) = (b x, 0)`. -/
theorem exists_square_reparam {a b : I → I} (ha : Continuous a) (ha' : Function.Injective a)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1) (hb : Continuous b) (hb' : Function.Injective b)
    (hb0 : b 0 = 0) (hb1 : b 1 = 1) :
    ∃ H : I × I ≃ₜ I × I, (∀ y, H (0, y) = (0, y)) ∧ (∀ x, H (x, 1) = (x, 1)) ∧
      (∀ y, H (1, y) = (1, a y)) ∧ (∀ x, H (x, 0) = (b x, 0)) := by
  have hma : StrictMono a := ha.strictMono_of_inj_boundedOrder (by
    change a 0 ≤ a 1; rw [ha0, ha1]; exact zero_le_one) ha'
  have hmb : StrictMono b := hb.strictMono_of_inj_boundedOrder (by
    change b 0 ≤ b 1; rw [hb0, hb1]; exact zero_le_one) hb'
  -- `h₁ (x, y) = (x, (1 - x) y + x a y)`
  set h₁ := interp id a with hh₁
  -- `h₂ (x, y) = (y x + (1 - y) b x, y)`
  set h₂ : I × I → I × I := Prod.swap ∘ interp σ b ∘ Prod.swap with hh₂
  have c₁ : Continuous h₁ := interp_continuous continuous_id ha
  have c₂ : Continuous h₂ := continuous_swap.comp
    ((interp_continuous continuous_symm hb).comp continuous_swap)
  have b₁ : Function.Bijective h₁ := interp_bijective ha hma ha0 ha1
  have b₂ : Function.Bijective h₂ := Prod.swap_bijective.comp
    ((interp_bijective hb hmb hb0 hb1).comp Prod.swap_bijective)
  let H := (c₁.comp c₂).homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (b₁.comp b₂))
  have hH : ∀ p, H p = h₁ (h₂ p) := fun p => rfl
  have e₂0 : ∀ y : I, h₂ (0, y) = (0, y) := by
    intro y
    simp only [hh₂, Function.comp_apply, Prod.swap_prod_mk]
    by_cases hy : y = 1
    · subst hy; rw [interp_of_w0 (by simp)]; rfl
    · rw [interp_of_y0 hb0]; rfl
  have e₂1 : ∀ y : I, h₂ (1, y) = (1, y) := by
    intro y
    simp only [hh₂, Function.comp_apply, Prod.swap_prod_mk]
    rw [interp_of_y1 hb1]; rfl
  refine ⟨H, fun y => ?_, fun x => ?_, fun y => ?_, fun x => ?_⟩
  · rw [hH, e₂0, hh₁, interp_of_w0 rfl]
  · rw [hH]
    have : h₂ (x, 1) = (x, 1) := by
      simp only [hh₂, Function.comp_apply, Prod.swap_prod_mk]
      rw [interp_of_w0 (by simp)]; rfl
    rw [this, hh₁, interp_of_y1 ha1]
  · rw [hH, e₂1, hh₁, interp_of_w1 rfl]
  · rw [hH]
    have : h₂ (x, 0) = (b x, 0) := by
      simp only [hh₂, Function.comp_apply, Prod.swap_prod_mk]
      rw [interp_of_w1 (by simp)]; rfl
    rw [this, hh₁, interp_of_y0 ha0]

end HPC.Sq
