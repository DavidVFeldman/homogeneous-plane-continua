import HPC.Plane.Enc1
import HPC.Plane.JanPoly
import HPC.Plane.Tree7Comp

/-!
# Batch 131: `enclose`, part II — the uniform path argument, `enclose_holds`, `planeFacts_holds`,
# Theorems 6 and 7 of Bing 1951 (Duke) unconditional

COMMISSION-batch131.md. The skeleton of the commission with every `sorry` replaced by a proof.
The edits to existing files (the renaming of the three relative theorems of `Tree7Comp.lean`, the
audit, `OPEN.md`, `README.md`) are described in COMMISSION-batch131.md §2.

Changes of shape (recorded in REPORT-batch131):

* `import HPC.Plane.Tree7Comp` added (the relative theorems `theorem7_1951_rel` etc. live there and
  are not reachable from `Enc1`/`JanPoly`).
* The unused hypothesis `hMne : M.Nonempty` is dropped from `not_mem_graphSet_bdryGraph_of_far`
  and `subset_component_of_far` (the inclusion `cthickening (2δ) M ⊆ {p | infDist p M ≤ 2δ}`
  holds for every `M`).
* Two small helpers added: `one_le_infDist_of_far_coord` (a point with a coordinate of absolute
  value `≥ R + 1` is at distance `≥ 1` from `M ⊆ ball 0 R`; used for the ray and for the four
  half-planes) and `pos_of_subset_ball` (`0 < R` when `M` is nonempty).
* `planeFacts_holds` and the three theorems of Bing 1951 are exactly as in the skeleton.

## The argument

Fix a continuum `M` that does not separate the plane, an open `G ⊇ M`, and `R` with
`M ⊆ ball 0 R`. Write `K δ := connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)`.
`exists_enclosing_polygon` (batch 130) gives, for every mesh `δ > 0`, a simple closed polygon `J`
with `M ⊆ polyInterior J` and `polyInterior J ∩ K δ = ∅`. So `polyInterior J ⊆ (K δ)ᶜ`, and
`enclose` follows once `(K δ)ᶜ ⊆ G`, i.e. `Gᶜ ⊆ K δ`, for one `δ`.

Membership in `K δ`, uniformly: a preconnected set `S` all of whose points are at distance
`> 2δ` from `M` misses `cthickening (2δ) M ⊇ gridUnion M δ ⊇ graphSet (bdryGraph M δ)`, so if `S`
meets `K δ` then `S ⊆ K δ` (`subset_component_of_far`). The eastern half-plane
`Ioi (gridR M δ) ×ˢ univ` lies in `K δ` (`halfPlane_subset_component`, batch 130).

The far point `f₀ := (R + 1, 0)` and the ray `Ray R := {(t, 0) | R + 1 ≤ t}` are at distance
`≥ 1` from `M` (sup metric: `dist (t, 0) m ≥ t - m.1 > t - R`). The ray is preconnected and meets
the eastern half-plane, so `Ray R ⊆ K δ` whenever `2δ < 1`.

`Mᶜ` is open and connected (`¬ SeparatesPlane M`), hence path-connected
(`IsOpen.isConnected_iff_isPathConnected`). For `x ∈ Gᶜ ∩ closedBall 0 (R + 1)` (compact, inside
`Mᶜ` since `M ⊆ G`) choose a path `γₓ` in `Mᶜ` from `x` to `f₀`; its range is compact and disjoint
from the compact `M`, so `dₓ := infDist`-gap `> 0`; put `rₓ := dₓ / 2`. The set
`Pₓ := closedBall x rₓ ∪ range γₓ` is compact, preconnected, contains `f₀`, and every point of it
is at distance `≥ rₓ` from `M` (triangle inequality on the ball). The balls `ball x rₓ` cover the
compact `Gᶜ ∩ closedBall 0 (R + 1)`; take a finite subcover `x₁, …, xₙ`, and
`d := min (1, r₁, …, rₙ) > 0`, `δ := d / 3`. Then `2δ < d`, so each `Pᵢ` and the ray lie in
`K δ`; hence `Gᶜ ∩ closedBall 0 (R + 1) ⊆ ⋃ ball xᵢ rᵢ ⊆ K δ`.

Points `x` with `‖x‖ > R + 1` (sup norm) are at distance `> 1` from `M` and lie in one of the four
open half-planes `{x.1 > R + 1}`, `{x.1 < -(R + 1)}`, `{x.2 > R + 1}`, `{x.2 < -(R + 1)}`, each
preconnected and at distance `> 1` from `M`; the first meets the eastern half-plane, and each of
the others meets the first at a corner `(T, ±T)` / `(±T, T)` with `T > R + 1`. So all four are in
`K δ` (`compl_closedBall_subset_component`). Hence `Gᶜ ⊆ K δ`.

Non-separation is used once: for the paths `γₓ`. `IsContinuum M` gives `M` compact, connected,
nonempty (`exists_enclosing_polygon` needs it; `infDist` to `M` needs nonemptiness).
-/

namespace HPC.Plane

open Set Metric

/-- The outer component of mesh `δ`, abbreviated. -/
def outerComp (M : Set Pt) (δ : ℝ) : Set Pt :=
  connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)

/-! ### Uniform membership in the outer component -/

/-- A point at distance `> 2δ` from `M` is off the boundary graph of mesh `δ`
(`graphSet_bdryGraph_subset`, `gridUnion_subset_cthickening`; `cthickening (2δ) M` is
`{p | infEdist p M ≤ 2δ}`). -/
theorem not_mem_graphSet_bdryGraph_of_far {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) {p : Pt} (hp : 2 * δ < infDist p M) :
    p ∉ graphSet (bdryGraph M δ) := by
  intro hpG
  have hc := gridUnion_subset_cthickening hM hδ (graphSet_bdryGraph_subset M hδ hpG)
  rw [mem_cthickening_iff] at hc
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  exact absurd hp (not_lt.2 this)

/-- A preconnected set at distance `> 2δ` from `M` that meets the outer component lies in it. -/
theorem subset_component_of_far {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ)
    {S : Set Pt} (hS : IsPreconnected S)
    (hfar : ∀ p ∈ S, 2 * δ < infDist p M) (hmeet : (S ∩ outerComp M δ).Nonempty) :
    S ⊆ outerComp M δ := by
  obtain ⟨x, hxS, hxK⟩ := hmeet
  unfold outerComp at hxK ⊢
  rw [connectedComponentIn_eq hxK]
  exact hS.subset_connectedComponentIn hxS fun p hp =>
    not_mem_graphSet_bdryGraph_of_far hM hδ (hfar p hp)

/-- The eastern ray from `(R + 1, 0)`. -/
def eastRay (R : ℝ) : Set Pt := (fun t : ℝ => ((t, 0) : Pt)) '' Ici (R + 1)

theorem isPreconnected_eastRay (R : ℝ) : IsPreconnected (eastRay R) := by
  exact isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => ((t, 0) : Pt)).continuousOn

/-- A point one of whose coordinates is at least `R + 1` in absolute value is at distance `≥ 1`
from `M ⊆ ball 0 R` (sup metric). -/
theorem one_le_infDist_of_far_coord {M : Set Pt} (hMne : M.Nonempty) {R : ℝ} (hMR : M ⊆ ball 0 R)
    {p : Pt} (hp : R + 1 ≤ |p.1| ∨ R + 1 ≤ |p.2|) : 1 ≤ infDist p M := by
  refine (le_infDist hMne).2 fun m hm => ?_
  have hm' := mem_ball.1 (hMR hm)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hm'
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, max_lt_iff] at hm'
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have h1 := abs_sub_abs_le_abs_sub p.1 m.1
  have h2 := abs_sub_abs_le_abs_sub p.2 m.2
  rcases hp with hp | hp
  · exact le_max_of_le_left (by linarith)
  · exact le_max_of_le_right (by linarith)

theorem pos_of_subset_ball {M : Set Pt} (hMne : M.Nonempty) {R : ℝ} (hMR : M ⊆ ball 0 R) : 0 < R := by
  obtain ⟨m, hm⟩ := hMne
  exact lt_of_le_of_lt dist_nonneg (mem_ball.1 (hMR hm))

/-- If `M ⊆ ball 0 R` then every point of `eastRay R` is at distance `≥ 1` from `M` (sup metric,
first coordinates). -/
theorem one_le_infDist_eastRay {M : Set Pt} (hMne : M.Nonempty) {R : ℝ} (hMR : M ⊆ ball 0 R)
    {p : Pt} (hp : p ∈ eastRay R) : 1 ≤ infDist p M := by
  obtain ⟨t, ht, rfl⟩ := hp
  exact one_le_infDist_of_far_coord hMne hMR (Or.inl (le_trans ht (le_abs_self t)))

/-- The ray meets the eastern half-plane `Ioi (gridR M δ) ×ˢ univ ⊆ outerComp M δ`
(`halfPlane_subset_component`), so it lies in the outer component for `2δ < 1`. -/
theorem eastRay_subset_component {M : Set Pt} (hM : Bornology.IsBounded M) (hMne : M.Nonempty)
    {R : ℝ} (hMR : M ⊆ ball 0 R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : 2 * δ < 1) :
    eastRay R ⊆ outerComp M δ := by
  have hR := pos_of_subset_ball hMne hMR
  refine subset_component_of_far hM hδ (isPreconnected_eastRay R)
    (fun p hp => by linarith [one_le_infDist_eastRay hMne hMR hp]) ?_
  refine ⟨(max (R + 1) (gridR M δ + 1), 0), ⟨_, mem_Ici.2 (le_max_left _ _), rfl⟩, ?_⟩
  have h := le_max_right (R + 1) (gridR M δ + 1)
  exact halfPlane_subset_component M hδ ⟨by simp only [mem_Ioi]; linarith, mem_univ _⟩

/-- The outside of the closed sup-norm ball of radius `R + 1` lies in the outer component for
`2δ < 1` (four open half-planes, each preconnected, each at distance `> 1` from `M`; the eastern
one meets `Ioi (gridR M δ) ×ˢ univ`; the others meet it at corners). -/
theorem compl_closedBall_subset_component {M : Set Pt} (hM : Bornology.IsBounded M)
    (hMne : M.Nonempty) {R : ℝ} (hMR : M ⊆ ball 0 R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : 2 * δ < 1) :
    (closedBall (0 : Pt) (R + 1))ᶜ ⊆ outerComp M δ := by
  have hR := pos_of_subset_ball hMne hMR
  have key : ∀ S : Set Pt, IsPreconnected S → (∀ p ∈ S, R + 1 ≤ |p.1| ∨ R + 1 ≤ |p.2|) →
      (S ∩ outerComp M δ).Nonempty → S ⊆ outerComp M δ := fun S hS hSf hSm =>
    subset_component_of_far hM hδ hS
      (fun p hp => by linarith [one_le_infDist_of_far_coord hMne hMR (hSf p hp)]) hSm
  set T : ℝ := max (R + 2) (gridR M δ + 1) with hT
  have hT1 : R + 2 ≤ T := le_max_left _ _
  have hT2 : gridR M δ + 1 ≤ T := le_max_right _ _
  have hH1 : Ioi (R + 1) ×ˢ (univ : Set ℝ) ⊆ outerComp M δ := by
    refine key _ (isPreconnected_Ioi.prod isPreconnected_univ)
      (fun p hp => Or.inl (le_trans (le_of_lt hp.1) (le_abs_self _)))
      ⟨(T, 0), ⟨by simp only [mem_Ioi]; linarith, mem_univ _⟩, ?_⟩
    exact halfPlane_subset_component M hδ ⟨by simp only [mem_Ioi]; linarith, mem_univ _⟩
  have hH2 : (univ : Set ℝ) ×ˢ Ioi (R + 1) ⊆ outerComp M δ :=
    key _ (isPreconnected_univ.prod isPreconnected_Ioi)
      (fun p hp => Or.inr (le_trans (le_of_lt hp.2) (le_abs_self _)))
      ⟨(T, T), ⟨mem_univ _, by simp only [mem_Ioi]; linarith⟩,
        hH1 ⟨by simp only [mem_Ioi]; linarith, mem_univ _⟩⟩
  have hH3 : (univ : Set ℝ) ×ˢ Iio (-(R + 1)) ⊆ outerComp M δ :=
    key _ (isPreconnected_univ.prod isPreconnected_Iio)
      (fun p hp => Or.inr (le_trans (by have := hp.2; simp only [mem_Iio] at this; linarith)
        (neg_le_abs _)))
      ⟨(T, -T), ⟨mem_univ _, by simp only [mem_Iio]; linarith⟩,
        hH1 ⟨by simp only [mem_Ioi]; linarith, mem_univ _⟩⟩
  have hH4 : Iio (-(R + 1)) ×ˢ (univ : Set ℝ) ⊆ outerComp M δ :=
    key _ (isPreconnected_Iio.prod isPreconnected_univ)
      (fun p hp => Or.inl (le_trans (by have := hp.1; simp only [mem_Iio] at this; linarith)
        (neg_le_abs _)))
      ⟨(-T, T), ⟨by simp only [mem_Iio]; linarith, mem_univ _⟩,
        hH2 ⟨mem_univ _, by simp only [mem_Ioi]; linarith⟩⟩
  intro x hx
  rw [mem_compl_iff, mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, not_le] at hx
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, lt_max_iff] at hx
  rcases hx with hx | hx
  · rcases lt_abs.1 hx with h | h
    · exact hH1 ⟨h, mem_univ _⟩
    · exact hH4 ⟨by simp only [mem_Iio]; linarith, mem_univ _⟩
  · rcases lt_abs.1 hx with h | h
    · exact hH2 ⟨mem_univ _, h⟩
    · exact hH3 ⟨mem_univ _, by simp only [mem_Iio]; linarith⟩

/-! ### Paths in `Mᶜ` and their distance from `M` -/

/-- An open connected set in the plane is path-connected
(`IsOpen.isConnected_iff_isPathConnected`; `ℝ × ℝ` is a `LocPathConnectedSpace` as a normed
space — check the instance; otherwise `Convex.isPathConnected` on balls and the open-set argument). -/
theorem joinedIn_compl_of_not_separates {M : Set Pt} (hMc : IsClosed M) (hns : ¬ SeparatesPlane M)
    {x y : Pt} (hx : x ∉ M) (hy : y ∉ M) : JoinedIn Mᶜ x y := by
  have hc : IsConnected Mᶜ := by
    unfold SeparatesPlane at hns
    exact not_not.1 hns
  exact ((hMc.isOpen_compl.isConnected_iff_isPathConnected).1 hc).joinedIn x hx y hy

/-- A compact set disjoint from the compact nonempty `M` is at positive distance from it:
there is `d > 0` with `d ≤ infDist p M` for all its points. -/
theorem exists_pos_infDist_le_of_disjoint {M P : Set Pt} (hM : IsCompact M) (hMne : M.Nonempty)
    (hP : IsCompact P) (hPM : Disjoint P M) : ∃ d > 0, ∀ p ∈ P, d ≤ infDist p M := by
  rcases P.eq_empty_or_nonempty with rfl | hPne
  · exact ⟨1, one_pos, fun p hp => hp.elim⟩
  obtain ⟨q, hq, hmin⟩ := hP.exists_isMinOn hPne (continuous_infDist_pt M).continuousOn
  refine ⟨infDist q M, (hM.isClosed.notMem_iff_infDist_pos hMne).1
    (Set.disjoint_left.1 hPM hq), fun p hp => hmin hp⟩

/-- **The local piece.** For `x ∉ M` and `f₀ ∉ M`, with `Mᶜ` connected: a radius `r > 0` and a
preconnected set `P ∋ x, f₀` containing `closedBall x r`, every point of which is at distance
`≥ r` from `M`. (`P := closedBall x r ∪ range γ` with `γ` a path in `Mᶜ` from `x` to `f₀` and
`r := d / 2`, `d` the gap of `range γ`; on the ball, `infDist p M ≥ infDist x M - dist p x ≥ d - r`.) -/
theorem exists_far_piece {M : Set Pt} (hM : IsCompact M) (hMne : M.Nonempty)
    (hns : ¬ SeparatesPlane M) {x f₀ : Pt} (hx : x ∉ M) (hf : f₀ ∉ M) :
    ∃ r > 0, ∃ P : Set Pt, IsPreconnected P ∧ x ∈ P ∧ f₀ ∈ P ∧ closedBall x r ⊆ P ∧
      ∀ p ∈ P, r ≤ infDist p M := by
  set γ := (joinedIn_compl_of_not_separates hM.isClosed hns hx hf).somePath
  have hγ : ∀ t, γ t ∈ Mᶜ := (joinedIn_compl_of_not_separates hM.isClosed hns hx hf).somePath_mem
  obtain ⟨d, hd, hdle⟩ := exists_pos_infDist_le_of_disjoint hM hMne (isCompact_range γ.continuous)
    (Set.disjoint_left.2 fun p ⟨t, ht⟩ => ht ▸ hγ t)
  have hxr : x ∈ range γ := ⟨0, γ.source⟩
  refine ⟨d / 2, by linarith, closedBall x (d / 2) ∪ range γ, ?_, Or.inl (mem_closedBall_self
    (by linarith)), Or.inr ⟨1, γ.target⟩, subset_union_left, ?_⟩
  · exact (convex_closedBall x (d / 2)).isPreconnected.union x (mem_closedBall_self (by linarith))
      hxr (isPreconnected_range γ.continuous)
  · rintro p (hp | hp)
    · have h1 := hdle x hxr
      have h2 := infDist_le_infDist_add_dist (s := M) (x := x) (y := p)
      rw [dist_comm] at h2
      have h3 := mem_closedBall.1 hp
      linarith
    · linarith [hdle p hp]

/-- **The uniform constant.** For a compact `C ⊆ Mᶜ` and `f₀ ∉ M`: a `d > 0` and finitely many
pieces `Pᵢ` (preconnected, containing `f₀`, at distance `≥ d` from `M`) whose interiors cover `C`
(finite subcover of `C` by the balls `ball xᵢ rᵢ`, `exists_far_piece`; `d := min rᵢ`, or `1` if
there are none). -/
theorem exists_uniform_pieces {M : Set Pt} (hM : IsCompact M) (hMne : M.Nonempty)
    (hns : ¬ SeparatesPlane M) {C : Set Pt} (hC : IsCompact C) (hCM : Disjoint C M) {f₀ : Pt}
    (hf : f₀ ∉ M) :
    ∃ d > 0, ∃ F : Finset (Set Pt), (∀ P ∈ F, IsPreconnected P ∧ f₀ ∈ P ∧
      ∀ p ∈ P, d ≤ infDist p M) ∧ C ⊆ ⋃ P ∈ F, P := by
  classical
  have hxM : ∀ x : C, (x : Pt) ∉ M := fun x => Set.disjoint_left.1 hCM x.2
  choose r hr P hP using fun x : C => exists_far_piece hM hMne hns (hxM x) hf
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => ball (x : Pt) (r x))
    (fun _ => isOpen_ball) fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩
  set S : Finset ℝ := insert 1 (t.image r)
  have hSne : S.Nonempty := Finset.insert_nonempty _ _
  refine ⟨S.min' hSne, ?_, t.image P, ?_, ?_⟩
  · obtain h | h := Finset.mem_insert.1 (S.min'_mem hSne)
    · rw [h]; exact one_pos
    · obtain ⟨x, -, hx⟩ := Finset.mem_image.1 h
      rw [← hx]; exact hr x
  · intro Q hQ
    obtain ⟨x, hxt, rfl⟩ := Finset.mem_image.1 hQ
    obtain ⟨hpc, -, hf0, -, hfar⟩ := hP x
    refine ⟨hpc, hf0, fun p hp => le_trans ?_ (hfar p hp)⟩
    exact S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hxt))
  · intro z hz
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (ht hz)
    exact mem_iUnion₂.2 ⟨P x, Finset.mem_image_of_mem _ hxt,
      (hP x).2.2.2.1 (ball_subset_closedBall hzx)⟩

/-! ### `enclose` -/

/-- **The complement of `G` lies in the outer component for small mesh.** `R` with `M ⊆ ball 0 R`;
`C := Gᶜ ∩ closedBall 0 (R + 1)`; `f₀ := (R + 1, 0) ∈ eastRay R`; `exists_uniform_pieces` gives `d`
and `F`; `δ := min d 1 / 3`. Each `P ∈ F` meets `outerComp M δ` at `f₀` (`eastRay_subset_component`)
and is at distance `≥ d > 2δ` from `M`, so `P ⊆ outerComp M δ` (`subset_component_of_far`); the
outside of the closed ball by `compl_closedBall_subset_component`. -/
theorem exists_mesh_compl_subset {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ¬ SeparatesPlane M) {G : Set Pt} (hG : IsOpen G) (hMG : M ⊆ G) :
    ∃ δ > 0, Gᶜ ⊆ outerComp M δ := by
  obtain ⟨hMc, hMconn⟩ := hM
  have hMne := hMconn.nonempty
  have hMb := hMc.isBounded
  obtain ⟨R, hMR⟩ := hMb.subset_ball (0 : Pt)
  have hR := pos_of_subset_ball hMne hMR
  set f₀ : Pt := (R + 1, 0)
  have hf₀ : f₀ ∈ eastRay R := ⟨R + 1, self_mem_Ici, rfl⟩
  have hf₀M : f₀ ∉ M := fun h => by
    have := one_le_infDist_eastRay hMne hMR hf₀
    rw [infDist_zero_of_mem h] at this
    linarith
  obtain ⟨d, hd, F, hF, hCF⟩ := exists_uniform_pieces hMc hMne hns
    ((isCompact_closedBall (0 : Pt) (R + 1)).inter_left hG.isClosed_compl)
    (Set.disjoint_left.2 fun x hx hxM => hx.1 (hMG hxM)) hf₀M
  set δ := min d 1 / 3 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : 2 * δ < 1 := by have := min_le_right d 1; rw [hδdef]; linarith
  have hδd : 2 * δ < d := by have := min_le_left d 1; rw [hδdef]; linarith [lt_min hd one_pos]
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_cases hxB : x ∈ closedBall (0 : Pt) (R + 1)
  · obtain ⟨Q, hQF, hxQ⟩ := mem_iUnion₂.1 (hCF ⟨hx, hxB⟩)
    obtain ⟨hQc, hQf, hQd⟩ := hF Q hQF
    exact subset_component_of_far hMb hδ hQc (fun p hp => lt_of_lt_of_le hδd (hQd p hp))
      ⟨f₀, hQf, eastRay_subset_component hMb hMne hMR hδ hδ1 hf₀⟩ hxQ
  · exact compl_closedBall_subset_component hMb hMne hMR hδ hδ1 hxB

/-- **The field `enclose` of `PlaneFacts` holds**: a continuum that does not separate the plane,
inside an open set `G`, is enclosed by a simple closed polygon whose interior lies in `G`
(`exists_mesh_compl_subset` and `exists_enclosing_polygon`: `polyInterior J ⊆ (outerComp M δ)ᶜ ⊆ G`). -/
theorem enclose_holds : ∀ M : Set Pt, Fold.Q78.IsContinuum M → ¬ SeparatesPlane M →
    ∀ G : Set Pt, IsOpen G → M ⊆ G →
      ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ Disjoint J M ∧ M ⊆ polyInterior J ∧
        polyInterior J ⊆ G := by
  intro M hM hns G hG hMG
  obtain ⟨δ, hδ, hGK⟩ := exists_mesh_compl_subset hM hns hG hMG
  obtain ⟨J, hJ, -, hJM, hMJ, hJK⟩ := exists_enclosing_polygon hM hδ
  refine ⟨J, hJ, hJM, hMJ, fun z hz => ?_⟩
  by_contra hzG
  exact Set.disjoint_left.1 hJK hz (hGK hzG)

/-- **`PlaneFacts` holds.** All three fields proved: `jct_polygon` (batch 126),
`enclose_holds` (batches 130–131), `janiszewski_polygonal` (batches 127–129). -/
theorem planeFacts_holds : PlaneFacts := planeFacts_of_enclose enclose_holds

/-! ### Bing 1951 (Duke), Theorems 6 and 7, unconditional

The relative forms (`theorem7_1951_rel`, `theorem6_1951_rel`, `theorem7_weak_rel` after the
renaming of COMMISSION-batch131.md §2) are specialised at `planeFacts_holds`. Statements otherwise
verbatim. -/

/-- **Bing 1951 (Duke), Theorem 7** (with the hypothesis "no subcontinuum of `M` separates the
plane" in place of "tree-like", as in batches 120–130): a bounded plane continuum no subcontinuum
of which separates the plane is covered, for every `ε > 0`, by a tree chain whose links are
interiors of simple closed polygons of diameter `< ε`. No interface, no hypothesis beyond the
theorem's own. -/
theorem theorem7_1951 {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧
      (∀ h ∈ G, ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ) ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h :=
  theorem7_1951_rel planeFacts_holds hM hns hε

/-- **Bing 1951 (Duke), Theorem 6**: a bounded plane continuum containing no continuum that
separates the plane is tree-like. No interface. -/
theorem theorem6_1951 {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) : IsTreeLike M :=
  theorem6_1951_rel planeFacts_holds hM hns

/-- **Theorem 7, weak form**, unconditional. -/
theorem theorem7_weak {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧ (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h ∧
      ∀ h ∈ G, IsOpen h ∧ IsConnected h ∧ Bornology.IsBounded h ∧
        interior (closure h) = h ∧ ¬ SeparatesPlane h :=
  theorem7_weak_rel planeFacts_holds hM hns hε

end HPC.Plane
