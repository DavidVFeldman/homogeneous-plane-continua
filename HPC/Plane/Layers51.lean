import HPC.Plane.Theorem11
import HPC.Plane.CantorOrganBing

/-!
# Batch 97: degenerate elements of Bing's decomposition (Q-deg)

Skeleton of the batch-97 commission, saved as `HPC/Plane/Layers51.lean` and imported at the end
of the root `HPC.lean`. Hausdorff distance is Mathlib's `Metric.hausdorffDist`; "element" means
`bingElt`.

**Outcome.**
* **Refuted** (the commented-out statements were removed in batch 103, see `LEDGER.md`;
  refutations proved):
  `bingElt_degenerate_of_isContPt` (Q3) and `exists_degenerate_interior_elt'` (Q-deg). The
  counterexample is the *Cantor organ* `Org.Organ` (`HPC/Plane/CantorOrgan*.lean`): the Cantor set
  times `[0,1]`, with the two endpoints of every removed interval of odd generation glued at the
  top and those of even generation glued at the bottom. It satisfies `BingS`
  (`Org.organ_bingS`); its elements are its layers (`Org.organ_bingElt`), each a nondegenerate
  arc (`Org.organ_bingElt_ne_singleton`); interior layers are not end elements
  (`Org.organ_not_isEndElt`); the points of a layer over a non-dyadic ("good") parameter are
  continuity points (`organ_isContPt`). So **no element is degenerate**
  (`exists_degenerate_interior_elt_refuted`), and the hypothesis `hdeg` of
  `theorem11_1951_of_T10` fails in universe `0` (`theorem11_hdeg_refuted`).
* **Proved:** Fort's theorem for the element map (`isMeagre_not_isContPt`, Q1, second half) and
  the existence of a continuity point outside the end elements (`exists_contPt_not_endElt`, Q2).
* **Removed (batch 105):** the three open statements `isContPt_congr`,
  `subcontinuum_of_isContPt`, `theorem11_1951_of_T10'` were deleted once Theorem 11 was proved
  without them (`theorem11_1951`, `Theorem11B.lean`); their obstructions are in `REPORT-batch97.md`.

**Shape changes.** `bingElt_degenerate_of_isContPt` and `exists_degenerate_interior_elt'` are
false (their commented-out text was removed in batch 103); their negations are stated, over `Type`, as
`bingElt_degenerate_of_isContPt_refuted` and `exists_degenerate_interior_elt_refuted`. No
existing file was edited in batch 97 (`exists_degenerate_interior_elt` in `Theorem11.lean`, false and
refuted here, was removed in batch 103).
-/

namespace HPC.Plane

open Set Topology Metric Filter

section General

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Continuity point of the element map.** `x` is a continuity point when every element near
`x` is Hausdorff-close to `bingElt x`: for every `ε > 0` there is an open `W ∋ x` such that every
`y ∈ W` has `hausdorffDist (bingElt y) (bingElt x) < ε`. (Upper semicontinuity gives one half
automatically; the content is lower semicontinuity.) -/
def IsContPt (x : S) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ W : Set S, IsOpen W ∧ x ∈ W ∧
    ∀ y ∈ W, hausdorffDist (bingElt y) (bingElt x) < ε

-- `isContPt_congr` (open) removed in batch 105: a step of the route closed in batch 97.

/-! ### Fort's theorem -/

/-- Points whose element meets the closed ball `closedBall z r`. -/
def MeetSet (z : S) (r : ℝ) : Set S := {x | (bingElt x ∩ closedBall z r).Nonempty}

/-- Upper semicontinuity, neighbourhood form. -/
theorem bingElt_eventually_subset (hS : BingS S) {U : Set S} (hU : IsOpen U) {x : S}
    (hx : bingElt x ⊆ U) : ∀ᶠ y in 𝓝 x, bingElt y ⊆ U := by
  have hO := bingElt_usc hS U hU
  have hxO : x ∈ ⋃ q ∈ {q | bingElt q ⊆ U}, bingElt q :=
    mem_iUnion₂.mpr ⟨x, hx, mem_bingElt x⟩
  filter_upwards [hO.mem_nhds hxO] with y hy
  obtain ⟨q, hqU, hyq⟩ := mem_iUnion₂.mp hy
  exact (bingElt_partition hS q y hyq) ▸ hqU

theorem isClosed_meetSet (hS : BingS S) (z : S) (r : ℝ) : IsClosed (MeetSet z r) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : bingElt x ⊆ (closedBall z r)ᶜ := by
    intro w hw hwb
    exact hx ⟨w, hw, hwb⟩
  filter_upwards [bingElt_eventually_subset hS isClosed_closedBall.isOpen_compl hx'] with y hy
  rintro ⟨w, hw, hwb⟩
  exact hy hw hwb

omit [CompactSpace S] in
/-- The boundary part `C \ interior C` of a closed set is nowhere dense. -/
theorem isNowhereDense_diff_interior {C : Set S} (hC : IsClosed C) :
    IsNowhereDense (C \ interior C) := by
  rw [(hC.sdiff isOpen_interior).isNowhereDense_iff, eq_empty_iff_forall_notMem]
  intro x hx
  have h1 : interior (C \ interior C) ⊆ interior C :=
    interior_maximal (interior_subset.trans diff_subset) isOpen_interior
  exact (interior_subset hx).2 (h1 hx)

/-- **Fort's theorem for the element map** (M. K. Fort, Jr., *Points of continuity of
semi-continuous functions*, Publ. Math. Debrecen 2 (1951), 100–102): the continuity points of an
upper semicontinuous compact-valued map on a Baire space are residual. Here: the set of
non-continuity points is meagre in `S`.

Proof: for each `n` cover `S` by finitely many balls `ball z (1/(n+1))`; every non-continuity
point lies on the boundary `C \ interior C` of one of the closed sets
`C = MeetSet z (1/(n+1))` (closed by upper semicontinuity), and these countably many boundaries
are nowhere dense. -/
theorem isMeagre_not_isContPt (hS : BingS S) : IsMeagre {x : S | ¬ IsContPt x} := by
  have hcov : ∀ n : ℕ, ∃ t : Set S, t.Finite ∧
      (univ : Set S) ⊆ ⋃ z ∈ t, ball z (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ (X := S))
      (e := 1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨t, ht, hcov⟩
  choose t ht hcovt using hcov
  set B : Set S := ⋃ n : ℕ, ⋃ z ∈ t n,
    (MeetSet z (1 / ((n : ℝ) + 1)) \ interior (MeetSet z (1 / ((n : ℝ) + 1))))
  have hB : IsMeagre B := by
    refine isMeagre_iUnion fun n => isMeagre_biUnion (ht n).countable fun z _ => ?_
    exact (isNowhereDense_diff_interior (isClosed_meetSet hS z _)).isMeagre
  refine hB.mono fun x hx => ?_
  by_contra hxB
  apply hx
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by linarith)
  set r : ℝ := 1 / ((n : ℝ) + 1)
  have hr : 0 < r := by positivity
  have hint : ∀ z ∈ t n, x ∈ MeetSet z r → x ∈ interior (MeetSet z r) := by
    intro z hz hxz
    by_contra hxi
    exact hxB (mem_iUnion.mpr ⟨n, mem_iUnion₂.mpr ⟨z, hz, hxz, hxi⟩⟩)
  have hev1 : ∀ᶠ y in 𝓝 x, bingElt y ⊆ thickening r (bingElt x) :=
    bingElt_eventually_subset hS isOpen_thickening (self_subset_thickening hr _)
  have hev2 : ∀ᶠ y in 𝓝 x, ∀ z ∈ t n, x ∈ MeetSet z r → y ∈ MeetSet z r := by
    rw [(ht n).eventually_all]
    intro z hz
    by_cases hxz : x ∈ MeetSet z r
    · filter_upwards [mem_interior_iff_mem_nhds.mp (hint z hz hxz)] with y hy _ using hy
    · exact Eventually.of_forall fun y h => absurd h hxz
  obtain ⟨W, hWsub, hW, hxW⟩ := _root_.mem_nhds_iff.mp (hev1.and hev2)
  refine ⟨W, hW, hxW, fun y hy => ?_⟩
  obtain ⟨hy1, hy2⟩ := hWsub hy
  refine lt_of_le_of_lt (hausdorffDist_le_of_mem_dist (r := 2 * r) (by linarith) ?_ ?_)
    (by linarith)
  · intro w hw
    obtain ⟨v, hv, hwv⟩ := mem_thickening_iff.mp (hy1 hw)
    exact ⟨v, hv, by linarith⟩
  · intro w hw
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp (hcovt n (mem_univ w))
    have hxz : x ∈ MeetSet z r := ⟨w, hw, ball_subset_closedBall hwz⟩
    obtain ⟨v, hv, hvz⟩ := hy2 z hz hxz
    refine ⟨v, hv, ?_⟩
    have h1 : dist w z < r := hwz
    have h2 : dist v z ≤ r := hvz
    calc dist w v ≤ dist w z + dist z v := dist_triangle _ _ _
      _ ≤ 2 * r := by rw [dist_comm z v]; linarith

/-- A continuity point outside both end elements exists (Baire: `S` is a complete metric space,
the two end elements are closed with empty interior, so their union is meagre). -/
theorem exists_contPt_not_endElt (hS : BingS S) : ∃ x : S, IsContPt x ∧ ¬ IsEndElt x := by
  haveI := hS.connected
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_endElts hS
  have hnd : ∀ p : S, IsMeagre (bingElt p) := fun p =>
    ((bingElt_isContinuum hS p).1.isClosed.isNowhereDense_iff.mpr
      (bingElt_interior_eq_empty hS p)).isMeagre
  have hM : IsMeagre ({x : S | ¬ IsContPt x} ∪ (bingElt a ∪ bingElt b)) :=
    (isMeagre_not_isContPt hS).union ((hnd a).union (hnd b))
  by_contra hno
  push_neg at hno
  refine not_isMeagre_of_isOpen isOpen_univ univ_nonempty (hM.mono fun x _ => ?_)
  by_cases hx : IsContPt x
  · have hxe := hno x hx
    right
    rcases at_most_two_endElts hS ha hb hxe hab with h | h
    · left; rw [← h]; exact mem_bingElt x
    · right; rw [← h]; exact mem_bingElt x
  · exact Or.inl hx

-- Commented-out statement `bingElt_degenerate_of_isContPt` removed in batch 103; see `LEDGER.md`.

-- `subcontinuum_of_isContPt` (open) removed in batch 105: a step of the route closed in batch 97.

-- Commented-out statement `exists_degenerate_interior_elt'` removed in batch 103; see `LEDGER.md`.

-- `theorem11_1951_of_T10'` (open) removed in batch 105: superseded by `theorem11_1951`.

end General

/-! ## The counterexample: the Cantor organ -/

section Organ

open Org

/-- The points of the layer over the good parameter `goodC` are continuity points. -/
theorem organ_isContPt {x : Organ} (hx : F x = lam goodC) : IsContPt x := by
  intro ε hε
  obtain ⟨η, hη, h⟩ := organ_layer_hausdorff goodC_good hε
  refine ⟨F ⁻¹' ball (lam goodC) η, isOpen_ball.preimage continuous_F, ?_, fun y hy => ?_⟩
  · show F x ∈ ball (lam goodC) η
    rw [hx]; exact mem_ball_self hη
  · rw [organ_bingElt, organ_bingElt, hx]
    exact h y (by have : dist (F y) (lam goodC) < η := hy; rwa [Real.dist_eq] at this)

/-- A continuity point of the organ that is not an end element, with a nondegenerate element. -/
theorem organ_contPt_nondegenerate :
    ∃ x : Organ, IsContPt x ∧ ¬ IsEndElt x ∧ bingElt x ≠ {x} := by
  refine ⟨pt goodC 0, organ_isContPt (F_pt _ _), organ_not_isEndElt ?_ ?_,
    organ_bingElt_ne_singleton _⟩
  · rw [F_pt]; exact lam_goodC_pos
  · rw [F_pt]; exact lam_goodC_lt_one

/-- **Q3 refuted.** A continuity point that is not an end element need not have a degenerate
element. -/
theorem bingElt_degenerate_of_isContPt_refuted :
    ¬ ∀ (S : Type) [MetricSpace S] [CompactSpace S], BingS S →
      ∀ x : S, IsContPt x → ¬ IsEndElt x → bingElt x = {x} := by
  intro h
  obtain ⟨x, hx, hxe, hne⟩ := organ_contPt_nondegenerate
  exact hne (h Organ organ_bingS x hx hxe)

/-- **Q-deg refuted.** A `BingS` space need not have a degenerate interior element: in the
Cantor organ no element at all is degenerate. -/
theorem exists_degenerate_interior_elt_refuted :
    ¬ ∀ (S : Type) [MetricSpace S] [CompactSpace S], BingS S →
      ∃ p : S, bingElt p = {p} ∧ ¬ IsEndElt p := by
  intro h
  obtain ⟨p, hp, -⟩ := h Organ organ_bingS
  exact organ_bingElt_ne_singleton p hp

/-- **The hypothesis `hdeg` of `theorem11_1951_of_T10` is false** (in universe `0`): it is
exactly the statement refuted by `exists_degenerate_interior_elt_refuted`. So
`theorem11_1951_of_T10`, instantiated at a space `S : Type`, has an unsatisfiable hypothesis. -/
theorem theorem11_hdeg_refuted :
    ¬ (∀ (T : Type) [MetricSpace T] [CompactSpace T], BingS T →
      ∃ p : T, bingElt p = {p} ∧ ¬ IsEndElt p) :=
  exists_degenerate_interior_elt_refuted

end Organ

end HPC.Plane
