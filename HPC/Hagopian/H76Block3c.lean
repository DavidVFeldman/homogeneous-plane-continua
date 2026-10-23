import HPC.Hagopian.Hagopian76Y

/-!
# Batch 181, §2.1: 3c by the irreducible interval

Commission 181 §2.1. With saturation (`InnerComponentsCross`) as a hypothesis, the component of
`F ∩ π⁻¹[D]` through a point over the saturation interval is a crossing component; its irreducible
interval is a member of `I`, so it lies in one block (`IsBlocks`), and that block is the block of
the point (the blocks are pairwise disjoint).

* `Thm1Setup.inner_component_in_block`: the component lies in `d⁻¹` of one block, which contains
  the parameter of the point.
* `Thm1Setup.inner_point_in_block` (corollary): the gap layers miss the points over the interval.
* `block_components_cross` (3c): the component of the point in `d⁻¹[B] ∩ π⁻¹[D]` is its component in
  `F ∩ π⁻¹[D]`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Block3c

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- The end of `I₂` on the left side has height `r₂ ≤ c₁` (from `hIs`). -/
theorem Thm1Setup.r₂_le (S : Thm1Setup M) : S.r₂ ≤ S.c₁ := by
  have h : ((3 / 22 : ℝ), S.r₂) ∈ (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 S.c₁ ∩ S.F ⁻¹' S.I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 S.c₁) := by
    rw [S.hIs]; exact mem_insert _ _
  exact h.1.1.2.2

/-- The end of `I₂` on the right side has height `s₂ ≤ c₁` (from `hIs`). -/
theorem Thm1Setup.s₂_le (S : Thm1Setup M) : S.s₂ ≤ S.c₁ := by
  have h : ((19 / 22 : ℝ), S.s₂) ∈ (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 S.c₁ ∩ S.F ⁻¹' S.I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 S.c₁) := by
    rw [S.hIs]; exact mem_insert_of_mem _ rfl
  exact h.1.1.2.2

/-- **A crossing piece that is a component of `F ∩ π⁻¹[D]` is a crossing component** (commission
181 §2.1, step 1: the open side segments of a crossing piece lie in the closed ones of
`IsCrossingComponent`, since `r₂, s₂ ≤ c₁`). -/
theorem Thm1Setup.isCrossingComponent_of_piece (S : Thm1Setup M) {zM : M} (hzM : zM ∈ S.D.G)
    (hzO : S.π (zM : Pt) ∈ S.F '' S.D')
    (hC : IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) (zM : Pt))) :
    IsCrossingComponent S.D.G S.π S.F S.c₁ S.D'
      (connectedComponentIn (crossSet S.D.G S.π S.F S.D') zM) := by
  have heq : toPt (connectedComponentIn (crossSet S.D.G S.π S.F S.D') zM) =
      connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) (zM : Pt) := by
    rw [← toPt_crossSet]; exact image_val_connectedComponentIn _ _
  rw [← heq] at hC
  have hl := hC.left
  have hr := hC.right
  rw [closure_toPt] at hl hr
  refine ⟨⟨zM, ⟨hzM, hzO⟩, rfl⟩, ?_, ?_⟩
  · obtain ⟨_, ⟨w, hw, rfl⟩, ⟨q, ⟨hq1, hq2⟩, hq⟩⟩ := hl
    exact ⟨w, hw, q, ⟨hq1, hq2.1.le, hq2.2.le.trans S.r₂_le⟩, hq⟩
  · obtain ⟨_, ⟨w, hw, rfl⟩, ⟨q, ⟨hq1, hq2⟩, hq⟩⟩ := hr
    exact ⟨w, hw, q, ⟨hq1, hq2.1.le, hq2.2.le.trans S.s₂_le⟩, hq⟩

/-- **The blocks are pairwise disjoint** (strict monotonicity on `[1, 2m]`). -/
theorem Thm1Setup.IsBlocks.block_eq (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) {i j : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) (hj1 : 1 ≤ j) (hjm : j ≤ m)
    {t : unitInterval} (hti : t ∈ Icc (x (2 * i - 1)) (x (2 * i)))
    (htj : t ∈ Icc (x (2 * j - 1)) (x (2 * j))) : i = j := by
  have hmono := hx.2.1
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : x (2 * i) < x (2 * j - 1) :=
      hmono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
    exact absurd (hti.2.trans_lt (this.trans_le htj.1)) (lt_irrefl _)
  · have : x (2 * j) < x (2 * i - 1) :=
      hmono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
    exact absurd (htj.2.trans_lt (this.trans_le hti.1)) (lt_irrefl _)

/-- **The component of an inner point lies in one block** (commission 181 §2.1, steps 1–3): for
`z ∈ F ∩ π⁻¹[D]` over `(lo, hi)`, with saturation on `(lo, hi)`, there is a block
`B = [x₂ᵢ₋₁, x₂ᵢ]` such that the component of `z` in `F ∩ π⁻¹[D]` lies in `d⁻¹[B]`. -/
theorem Thm1Setup.inner_component_in_block (S : Thm1Setup M) {lo hi : ℝ}
    (hICC : InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ lo hi)
    {x : ℕ → unitInterval} {m : ℕ} (hx : S.IsBlocks x m) {z : Pt}
    (hz : z ∈ toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D'))
    (hzm : ∃ q ∈ S.D', S.π z = S.F q ∧ q.1 ∈ Ioo lo hi) :
    ∃ i, 1 ≤ i ∧ i ≤ m ∧ connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) z ⊆
      toPt (layerSet S.D.d (Icc (x (2 * i - 1)) (x (2 * i)))) := by
  have hC := hICC z hz hzm
  obtain ⟨⟨zM, hzM, rfl⟩, hzO⟩ := hz
  have hCC := S.isCrossingComponent_of_piece hzM hzO hC
  set CM := connectedComponentIn (crossSet S.D.G S.π S.F S.D') zM with hCM
  have heq : toPt CM =
      connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) (zM : Pt) := by
    rw [← toPt_crossSet]; exact image_val_connectedComponentIn _ _
  have hCG : CM ⊆ S.D.G := fun w hw => (connectedComponentIn_subset _ _ hw).1
  obtain ⟨u, v, hirr, -, -⟩ := exists_irreducibleInterval S.D.hG hCG
    ⟨zM, mem_connectedComponentIn ⟨hzM, hzO⟩⟩
  obtain ⟨i, hi1, him, hu, hv⟩ := hx.2.2.2.2.1 (u, v) ⟨CM, hCC, hirr⟩
  refine ⟨i, hi1, him, ?_⟩
  rw [← heq]
  exact image_mono (hirr.1.trans (layerSet_mono S.D.d (Icc_subset_Icc hu hv)))

/-- **Corollary of 3c: the gap layers miss the points over the interval** (commission 181 §2.1):
every point of `F ∩ π⁻¹[D]` over `(lo, hi)` lies in `d⁻¹` of some block. -/
theorem Thm1Setup.inner_point_in_block (S : Thm1Setup M) {lo hi : ℝ}
    (hICC : InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ lo hi)
    {x : ℕ → unitInterval} {m : ℕ} (hx : S.IsBlocks x m) {z : Pt}
    (hz : z ∈ toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D'))
    (hzm : ∃ q ∈ S.D', S.π z = S.F q ∧ q.1 ∈ Ioo lo hi) :
    ∃ i, 1 ≤ i ∧ i ≤ m ∧ z ∈ toPt (layerSet S.D.d (Icc (x (2 * i - 1)) (x (2 * i)))) := by
  obtain ⟨i, hi1, him, hsub⟩ := S.inner_component_in_block hICC hx hz hzm
  exact ⟨i, hi1, him, hsub (mem_connectedComponentIn hz)⟩

/-- **3c** (commission 181 §2.1, by the irreducible interval): with saturation on `(lo, hi)`, for
a block `B = [x₂ᵢ₋₁, x₂ᵢ]` and `z ∈ d⁻¹[B] ∩ π⁻¹[D]` over `(lo, hi)`, the component of `z` in
`d⁻¹[B] ∩ π⁻¹[D]` is its component in `F ∩ π⁻¹[D]` (a crossing piece, by saturation).

*Shape:* the open block of `Hagopian76Y.lean`, with the saturation interval generalized to any
`(lo, hi)`; `lemma3_half` is not used. -/
theorem block_components_cross (S : Thm1Setup M) {lo hi : ℝ}
    (hICC : InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂ lo hi)
    (x : ℕ → unitInterval) (m : ℕ) (hx : S.IsBlocks x m) (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m)
    (z : Pt) (hz : z ∈ toPt (layerSet S.D.d (Icc (x (2 * i - 1)) (x (2 * i)))) ∩
      S.π ⁻¹' (S.F '' S.D'))
    (hzm : ∃ q ∈ S.D', S.π z = S.F q ∧ q.1 ∈ Ioo lo hi) :
    connectedComponentIn (toPt (layerSet S.D.d (Icc (x (2 * i - 1)) (x (2 * i)))) ∩
      S.π ⁻¹' (S.F '' S.D')) z = connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) z := by
  have hBG : toPt (layerSet S.D.d (Icc (x (2 * i - 1)) (x (2 * i)))) ⊆ toPt S.D.G :=
    image_mono (layerSet_subset _ _)
  have hzG : z ∈ toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D') := ⟨hBG hz.1, hz.2⟩
  obtain ⟨j, hj1, hjm, hsub⟩ := S.inner_component_in_block hICC hx hzG hzm
  -- the block of the component is the block of `z`
  have hij : i = j := by
    obtain ⟨g, ⟨a, ha, rfl⟩, hgz⟩ := hz.1
    obtain ⟨g', ⟨b, hb, rfl⟩, hg'z⟩ := hsub (mem_connectedComponentIn hzG)
    have hab : a = b := Subtype.ext (Subtype.ext (hgz.trans hg'z.symm))
    subst hab
    exact Thm1Setup.IsBlocks.block_eq S hx hi1 him hj1 hjm ha hb
  subst hij
  refine Subset.antisymm (connectedComponentIn_mono _ (inter_subset_inter_left _ hBG)) ?_
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hzG)
    (subset_inter hsub (fun w hw => (connectedComponentIn_subset _ _ hw).2))

end Block3c

end HPC.Hagopian
