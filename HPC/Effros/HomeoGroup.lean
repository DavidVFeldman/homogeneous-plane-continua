import Mathlib

/-!
# Batch 134, §C: the homeomorphism group of a compact metric space

Mathlib (at the pinned version) has no group structure and no topology on `Y ≃ₜ Y`. We supply:

* C.1 `Group (Y ≃ₜ Y)` with `(f * g) y = f (g y)`, `1 = Homeomorph.refl`, `f⁻¹ = f.symm`, for
  any topological space `Y`; the topology induced by `h ↦ (h, h⁻¹)` into
  `C(Y, Y) × C(Y, Y)` (compact-open topology; for compact metric `Y` this is uniform
  convergence); `IsTopologicalGroup` for locally compact `Y`.
* C.2 `PolishSpace (Y ≃ₜ Y)` for compact metric `Y`: the embedding has closed range
  `{(f, g) | f ∘ g = id ∧ g ∘ f = id}`, and `C(Y, Y)` is Polish (Mathlib).
* C.3 `MulAction (Y ≃ₜ Y) Y` by evaluation, `ContinuousSMul`, and the `supMove`-balls form a
  basis of `𝓝 1` (`hasBasis_supMove`).
-/

namespace HPC.Effros

open Set Topology Filter Metric

section GroupStructure

variable {Y : Type*} [TopologicalSpace Y]

/-- **C.1.** The group of self-homeomorphisms; multiplication is composition. -/
instance homeoGroup : Group (Y ≃ₜ Y) where
  mul f g := g.trans f
  one := Homeomorph.refl Y
  inv f := f.symm
  mul_assoc _ _ _ := Homeomorph.ext fun _ => rfl
  one_mul _ := Homeomorph.ext fun _ => rfl
  mul_one _ := Homeomorph.ext fun _ => rfl
  inv_mul_cancel f := Homeomorph.ext fun y => f.symm_apply_apply y

@[simp] theorem homeo_mul_apply (f g : Y ≃ₜ Y) (y : Y) : (f * g) y = f (g y) := rfl

@[simp] theorem homeo_one_apply (y : Y) : (1 : Y ≃ₜ Y) y = y := rfl

theorem homeo_inv_def (f : Y ≃ₜ Y) : f⁻¹ = f.symm := rfl

/-- **C.3.** The evaluation action. -/
instance homeoMulAction : MulAction (Y ≃ₜ Y) Y where
  smul f y := f y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem homeo_smul_def (f : Y ≃ₜ Y) (y : Y) : f • y = f y := rfl

/-- A homeomorphism as a continuous map. -/
def homeoCM (h : Y ≃ₜ Y) : C(Y, Y) := ⟨h, h.continuous⟩

@[simp] theorem homeoCM_apply (h : Y ≃ₜ Y) (y : Y) : homeoCM h y = h y := rfl

/-- The embedding `h ↦ (h, h⁻¹)` of the homeomorphism group into `C(Y, Y) × C(Y, Y)`. -/
def homeoEmb (h : Y ≃ₜ Y) : C(Y, Y) × C(Y, Y) := (homeoCM h, homeoCM h.symm)

/-- **C.1.** The topology of the homeomorphism group: induced by `homeoEmb` (Arens). -/
instance homeoTopology : TopologicalSpace (Y ≃ₜ Y) :=
  TopologicalSpace.induced homeoEmb inferInstance

theorem isInducing_homeoEmb : IsInducing (homeoEmb : (Y ≃ₜ Y) → C(Y, Y) × C(Y, Y)) := ⟨rfl⟩

theorem homeoEmb_injective : Function.Injective (homeoEmb : (Y ≃ₜ Y) → C(Y, Y) × C(Y, Y)) := by
  intro f g hfg
  ext y
  have := congrArg (fun p : C(Y, Y) × C(Y, Y) => p.1 y) hfg
  simpa [homeoEmb] using this

theorem continuous_homeoEmb : Continuous (homeoEmb : (Y ≃ₜ Y) → C(Y, Y) × C(Y, Y)) :=
  isInducing_homeoEmb.continuous

/-- **C.1.** For locally compact `Y` the homeomorphism group is a topological group. -/
instance homeo_isTopologicalGroup [LocallyCompactSpace Y] : IsTopologicalGroup (Y ≃ₜ Y) where
  continuous_mul := by
    rw [isInducing_homeoEmb.continuous_iff]
    have h1 : Continuous fun p : (Y ≃ₜ Y) × (Y ≃ₜ Y) => (homeoEmb p.1, homeoEmb p.2) :=
      (continuous_homeoEmb.comp continuous_fst).prodMk (continuous_homeoEmb.comp continuous_snd)
    have hc := (ContinuousMap.continuous_comp' (X := Y) (Y := Y) (Z := Y))
    have e : (homeoEmb ∘ fun p : (Y ≃ₜ Y) × (Y ≃ₜ Y) => p.1 * p.2) =
        fun p => (((homeoEmb p.2).1, (homeoEmb p.1).1).2.comp ((homeoEmb p.2).1, (homeoEmb p.1).1).1,
          ((homeoEmb p.1).2, (homeoEmb p.2).2).2.comp ((homeoEmb p.1).2, (homeoEmb p.2).2).1) := by
      funext p
      exact Prod.ext (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl)
    rw [e]
    refine (hc.comp ?_).prodMk (hc.comp ?_)
    · exact ((continuous_fst.comp continuous_homeoEmb).comp continuous_snd).prodMk
        ((continuous_fst.comp continuous_homeoEmb).comp continuous_fst)
    · exact ((continuous_snd.comp continuous_homeoEmb).comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_homeoEmb).comp continuous_snd)
  continuous_inv := by
    rw [isInducing_homeoEmb.continuous_iff]
    have e : (homeoEmb ∘ fun f : Y ≃ₜ Y => f⁻¹) = Prod.swap ∘ homeoEmb := by
      funext f
      exact Prod.ext (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl)
    rw [e]
    exact continuous_swap.comp continuous_homeoEmb

/-- **C.3.** The evaluation action is continuous (locally compact `Y`). -/
instance homeo_continuousSMul [LocallyCompactSpace Y] : ContinuousSMul (Y ≃ₜ Y) Y where
  continuous_smul := by
    have : (fun p : (Y ≃ₜ Y) × Y => p.1 • p.2) =
        (fun q : C(Y, Y) × Y => q.1 q.2) ∘ fun p : (Y ≃ₜ Y) × Y => ((homeoEmb p.1).1, p.2) := by
      funext p
      rfl
    rw [this]
    exact continuous_eval.comp
      (((continuous_fst.comp continuous_homeoEmb).comp continuous_fst).prodMk continuous_snd)

end GroupStructure

section Polish

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

omit [CompactSpace Y] in
theorem range_homeoEmb : range (homeoEmb : (Y ≃ₜ Y) → C(Y, Y) × C(Y, Y)) =
    {p | p.1.comp p.2 = ContinuousMap.id Y ∧ p.2.comp p.1 = ContinuousMap.id Y} := by
  ext ⟨f, g⟩
  constructor
  · rintro ⟨h, hh⟩
    simp only [homeoEmb, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    constructor <;> ext y <;> simp
  · rintro ⟨h1, h2⟩
    have hl : Function.LeftInverse g f := fun y => congrArg (fun k : C(Y, Y) => k y) h2
    have hr : Function.RightInverse g f := fun y => congrArg (fun k : C(Y, Y) => k y) h1
    exact ⟨Homeomorph.mk ⟨f, g, hl, hr⟩ f.continuous g.continuous, rfl⟩

theorem isClosed_range_homeoEmb :
    IsClosed (range (homeoEmb : (Y ≃ₜ Y) → C(Y, Y) × C(Y, Y))) := by
  rw [range_homeoEmb]
  have hc := (ContinuousMap.continuous_comp' (X := Y) (Y := Y) (Z := Y))
  refine (isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)
  · exact hc.comp (continuous_snd.prodMk continuous_fst)
  · exact hc

theorem isClosedEmbedding_homeoEmb :
    IsClosedEmbedding (homeoEmb : (Y ≃ₜ Y) → C(Y, Y) × C(Y, Y)) :=
  ⟨⟨isInducing_homeoEmb, homeoEmb_injective⟩, isClosed_range_homeoEmb⟩

/-- **C.2.** The homeomorphism group of a compact metric space is Polish. -/
instance homeo_polishSpace : PolishSpace (Y ≃ₜ Y) :=
  isClosedEmbedding_homeoEmb.polishSpace

end Polish

section Homeo

variable (Y : Type*) [MetricSpace Y] [CompactSpace Y]

/-- The sup-distance of a homeomorphism from the identity. -/
noncomputable def supMove (h : Y ≃ₜ Y) : ℝ := ⨆ z : Y, dist (h z) z

variable {Y}

/-- The supremum in `supMove` is over a set bounded above (a continuous function on a compact
space), so the pointwise bound holds. -/
theorem bddAbove_move (h : Y ≃ₜ Y) : BddAbove (range fun z : Y => dist (h z) z) :=
  (isCompact_range (h.continuous.dist continuous_id)).bddAbove

theorem dist_le_supMove (h : Y ≃ₜ Y) (z : Y) : dist (h z) z ≤ supMove Y h :=
  le_ciSup (bddAbove_move h) z

omit [CompactSpace Y] in
theorem supMove_nonneg (h : Y ≃ₜ Y) : 0 ≤ supMove Y h :=
  Real.iSup_nonneg fun _ => dist_nonneg

omit [CompactSpace Y] in
theorem supMove_le {h : Y ≃ₜ Y} {a : ℝ} (ha : 0 ≤ a) (hh : ∀ z, dist (h z) z ≤ a) :
    supMove Y h ≤ a :=
  Real.iSup_le hh ha

/-- `supMove` is the uniform distance of `h` from the identity. -/
theorem supMove_eq_dist (h : Y ≃ₜ Y) :
    supMove Y h = dist (homeoCM h) (ContinuousMap.id Y) := by
  rw [ContinuousMap.dist_eq_iSup]
  rfl

omit [CompactSpace Y] in
theorem supMove_symm (h : Y ≃ₜ Y) : supMove Y h.symm = supMove Y h := by
  unfold supMove
  rw [← h.surjective.iSup_comp]
  simp only [Homeomorph.symm_apply_apply]
  exact iSup_congr fun z => dist_comm _ _

omit [CompactSpace Y] in
theorem supMove_inv (h : Y ≃ₜ Y) : supMove Y h⁻¹ = supMove Y h := supMove_symm h

/-- `supMove (h⁻¹ ∘ g) ≤ supMove h + supMove g`. -/
theorem supMove_symm_trans_le (g h : Y ≃ₜ Y) :
    supMove Y (g.trans h.symm) ≤ supMove Y h + supMove Y g := by
  refine supMove_le (add_nonneg (supMove_nonneg h) (supMove_nonneg g)) fun z => ?_
  calc dist ((g.trans h.symm) z) z ≤ dist (h.symm (g z)) (g z) + dist (g z) z :=
        dist_triangle _ _ _
    _ ≤ supMove Y h.symm + supMove Y g :=
        add_le_add (dist_le_supMove h.symm (g z)) (dist_le_supMove g z)
    _ = supMove Y h + supMove Y g := by rw [supMove_symm]

theorem supMove_mul_le (g h : Y ≃ₜ Y) : supMove Y (g * h) ≤ supMove Y g + supMove Y h := by
  refine supMove_le (add_nonneg (supMove_nonneg g) (supMove_nonneg h)) fun z => ?_
  calc dist ((g * h) z) z ≤ dist (g (h z)) (h z) + dist (h z) z := dist_triangle _ _ _
    _ ≤ supMove Y g + supMove Y h := add_le_add (dist_le_supMove g _) (dist_le_supMove h z)

/-- **C.3.** The `supMove`-balls form a basis of the neighbourhoods of `1`. -/
theorem hasBasis_supMove :
    (𝓝 (1 : Y ≃ₜ Y)).HasBasis (fun r : ℝ => 0 < r) fun r => {h | supMove Y h < r} := by
  rw [isInducing_homeoEmb.nhds_eq_comap]
  have hb := (Metric.nhds_basis_ball (x := homeoEmb (1 : Y ≃ₜ Y))).comap homeoEmb
  convert hb using 2 with r hr
  ext h
  simp only [mem_setOf_eq, mem_preimage]
  rw [← ball_prod_same, mem_prod, mem_ball, mem_ball]
  change supMove Y h < r ↔ dist (homeoCM h) (ContinuousMap.id Y) < r ∧
    dist (homeoCM h.symm) (ContinuousMap.id Y) < r
  rw [← supMove_eq_dist, ← supMove_eq_dist, supMove_symm, and_self]

/-- **C.3.** `{h | supMove h < r}` is a neighbourhood of `1` for `r > 0`. -/
theorem supMove_ball_mem_nhds {r : ℝ} (hr : 0 < r) : {h : Y ≃ₜ Y | supMove Y h < r} ∈ 𝓝 1 :=
  hasBasis_supMove.mem_of_mem hr

end Homeo

end HPC.Effros
