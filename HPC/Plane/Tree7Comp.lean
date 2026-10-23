import HPC.Plane.Tree7

/-!
# Batch 120: Bing 1951 (Duke), Theorem 7 — the components are polygon interiors; `theorem7_1951`

Installed skeleton (`doc/batches/skeletons/Tree7Comp.lean` is the uploaded copy). Every item is
proved; the changes of shape are recorded in the docstrings concerned and in
`doc/batches/REPORT-batch120.md`:

* `IsCrosscut.of_side`: the hypothesis `hside` is now `c' \ J ⊆ polyInterior (α ∪ c)` (no ends
  quantified: for a cross-cut, `c' \ J` *is* `c'` minus its ends, `c' ∩ J = {a, b}`); the unused
  hypothesis `hΓ` was dropped.
* `PlaneFacts.connectedComponentIn_inter_eq`: the unused hypothesis `hU : IsOpen U` was dropped.
* The clause `Γ ⊆ J ∪ ⋃ C` of `components_of_crosscuts` cost nothing and is kept.

**Theorem 7 (p. 657).** *If `M` is a tree-like plane continuum and `ε` is a positive number, there is
a tree-chain covering `M` whose links are the interiors of simple closed curves of diameters less
than `ε`.* Stated here with the hypothesis the proof of Theorem 6 uses (no subcontinuum of `M`
separates the plane); the implication from "tree-like" is open relative to `PlaneFacts`
(batch 119, item 5).

**The main theorem of this batch** (`PlaneFacts.component_inter_eq_polyInterior`): if `J` and `P` are
simple closed polygons whose intersection is **finite**, every component of
`polyInterior J ∩ polyInterior P` is the interior of a simple closed polygon. Transversality is not
used; general position (batch 119) enters only through `finite_inter_of_gp`. Plan:

1. **Cross-cut families and the induction.** A cross-cut family of `J` is a finite set of cross-cuts
   (as in `PlaneFacts.crosscut`) any two of which meet only in points of `J`, i.e. only at common
   ends. Splitting `polyInterior J` along one of them (`crosscut`) and distributing the others to
   the two sides, induction on the number of cross-cuts shows that every component of
   `polyInterior J \ ⋃ C` is a polygon interior.
2. **Decomposing `P` at a finite set of its points** into simple arcs meeting only at those points
   (`split_two` at two of them, then `IsSimplePolyArc.split` at the rest, by induction).
3. **The cross-cut family of `P` in `J`**: the pieces of `P` between consecutive points of
   `X = P ∩ J` which run inside `polyInterior J`; `polyInterior J \ P = polyInterior J \ ⋃ C`.
4. **Identification**: a component of `U ∩ N` (`U = polyInterior J`, `N = polyInterior P`) is a
   component of `U \ P` (a connected set missing `frontier N = P` and meeting `N` lies in `N`).
   The degenerate cases (`P ∩ U = ∅`; `P ∩ J = ∅`; `P ∩ J` a single point) give `U ∩ N ∈ {∅, U, N}`
   by connectedness alone.
5. **Theorem 7** from `exists_gp_cover`, `treeChain_of_cover`, `notched_eq_polyInterior`.
-/

namespace HPC.Plane

open Set Metric

open scoped Classical

/-! ### 0. Auxiliary facts about arcs and polygons -/

/-- In a preconnected plane set containing two distinct points `a`, `b`, the point `a` is a limit of
points of the set other than `a` and `b`. -/
theorem mem_closure_diff_pair_of_isPreconnected {α : Set Pt} (hα : IsPreconnected α) {a b : Pt}
    (ha : a ∈ α) (hb : b ∈ α) (hab : a ≠ b) : a ∈ closure (α \ {a, b}) := by
  by_contra hcl
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ y ∈ α \ {a, b}, ε ≤ dist a y := by
    rw [Metric.mem_closure_iff] at hcl
    push_neg at hcl
    exact hcl
  set r := min ε (dist a b) with hr_def
  have hr : 0 < r := lt_min hε (dist_pos.2 hab)
  have key : ∀ y ∈ α, y = a ∨ r ≤ dist a y := by
    intro y hy
    by_cases hya : y = a
    · exact Or.inl hya
    right
    by_cases hyb : y = b
    · subst hyb; exact min_le_right _ _
    · exact (min_le_left _ _).trans (hball y ⟨hy, by
        rintro (h | h)
        · exact hya h
        · exact hyb h⟩)
  obtain ⟨y, hy, hy1, hy2⟩ := hα (ball a r) (closedBall a (r / 2))ᶜ isOpen_ball
    isClosed_closedBall.isOpen_compl
    (by
      intro y hy
      rcases key y hy with rfl | h
      · exact Or.inl (mem_ball_self hr)
      · right
        simp only [mem_compl_iff, mem_closedBall, not_le]
        rw [dist_comm]; linarith)
    ⟨a, ha, mem_ball_self hr⟩
    ⟨b, hb, by
      simp only [mem_compl_iff, mem_closedBall, not_le]
      rw [dist_comm]
      have := min_le_right ε (dist a b)
      linarith⟩
  rcases key y hy with rfl | h
  · exact hy2 (mem_closedBall_self (by linarith))
  · rw [mem_ball'] at hy1; linarith

theorem IsSimplePolyArc.left_mem_closure_diff {α : Set Pt} {a b : Pt}
    (h : IsSimplePolyArc α a b) : a ∈ closure (α \ {a, b}) :=
  mem_closure_diff_pair_of_isPreconnected h.isContinuum.2.isPreconnected h.left_mem h.right_mem
    h.ne

theorem IsSimplePolyArc.right_mem_closure_diff {α : Set Pt} {a b : Pt}
    (h : IsSimplePolyArc α a b) : b ∈ closure (α \ {a, b}) := by
  have := mem_closure_diff_pair_of_isPreconnected h.isContinuum.2.isPreconnected h.right_mem
    h.left_mem h.ne.symm
  rwa [pair_comm] at this

/-- An arc minus its first end is connected. -/
theorem IsSimplePolyArc.isConnected_diff_left {α : Set Pt} {a b : Pt}
    (h : IsSimplePolyArc α a b) : IsConnected (α \ {a}) := by
  refine h.isConnected_diff_ends.subset_closure
    (diff_subset_diff_right (singleton_subset_iff.2 (mem_insert _ _))) ?_
  rintro y ⟨hy, hya⟩
  by_cases hyb : y = b
  · subst hyb; exact h.right_mem_closure_diff
  · refine subset_closure ⟨hy, ?_⟩
    rintro (h' | h')
    · exact hya h'
    · exact hyb h'

/-- A simple closed polygon has a point other than any given point. -/
theorem IsSimpleClosedPolygon.exists_ne {P : Set Pt} (hP : IsSimpleClosedPolygon P) (a : Pt) :
    ∃ b ∈ P, b ≠ a := by
  obtain ⟨n, hn, v, rfl, hinj, -⟩ := hP
  have h0 : v ⟨0, by omega⟩ ∈ polygonOf v := mem_iUnion.2 ⟨⟨0, by omega⟩, left_mem_segment _ _ _⟩
  have h1 : v ⟨1, by omega⟩ ∈ polygonOf v := mem_iUnion.2 ⟨⟨1, by omega⟩, left_mem_segment _ _ _⟩
  have hne : v ⟨0, by omega⟩ ≠ v ⟨1, by omega⟩ := fun h =>
    absurd (congrArg Fin.val (hinj h)) (by simp)
  by_cases h : v ⟨0, by omega⟩ = a
  · exact ⟨_, h1, fun h' => hne (h.trans h'.symm)⟩
  · exact ⟨_, h0, h⟩

/-- A simple closed polygon minus one of its points is connected. -/
theorem IsSimpleClosedPolygon.isConnected_diff_singleton {P : Set Pt}
    (hP : IsSimpleClosedPolygon P) {a : Pt} (ha : a ∈ P) : IsConnected (P \ {a}) := by
  obtain ⟨b, hb, hba⟩ := hP.exists_ne a
  obtain ⟨α₁, α₂, h₁, h₂, hU, -⟩ := hP.split_two ha hb hba.symm
  rw [← hU, union_diff_distrib]
  exact IsConnected.union ⟨b, ⟨h₁.right_mem, hba⟩, ⟨h₂.right_mem, hba⟩⟩ h₁.isConnected_diff_left
    h₂.isConnected_diff_left

/-- A simple closed polygon is connected. -/
theorem IsSimpleClosedPolygon.isConnected {P : Set Pt} (hP : IsSimpleClosedPolygon P) :
    IsConnected P := by
  obtain ⟨a, ha, -⟩ := hP.exists_ne 0
  obtain ⟨b, hb, hba⟩ := hP.exists_ne a
  obtain ⟨α₁, α₂, h₁, h₂, hU, -⟩ := hP.split_two ha hb hba.symm
  rw [← hU]
  exact IsConnected.union ⟨a, h₁.left_mem, h₂.left_mem⟩ h₁.isContinuum.2 h₂.isContinuum.2

/-- If `c ∩ J = s` then `c \ s = c \ J`. -/
theorem diff_eq_diff_of_inter_eq {c J s : Set Pt} (h : c ∩ J = s) : c \ s = c \ J := by
  subst h; ext y; simp only [mem_diff, mem_inter_iff, not_and]; tauto

/-! ### 1. Cross-cut families and the induction -/

/-- A **cross-cut** of the simple closed polygon `J`: a simple polygonal arc meeting `J` exactly in
its two (distinct) ends, with its interior inside `polyInterior J`. -/
def IsCrosscut (J c : Set Pt) : Prop :=
  ∃ a b : Pt, a ≠ b ∧ IsSimplePolyArc c a b ∧ c ∩ J = {a, b} ∧ c \ {a, b} ⊆ polyInterior J

/-- A **cross-cut family** of `J`: finitely many cross-cuts, any two of which meet only in `J`
(hence only at common ends). -/
def IsCrosscutFamily (J : Set Pt) (C : Finset (Set Pt)) : Prop :=
  (∀ c ∈ C, IsCrosscut J c) ∧ ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → c ∩ c' ⊆ J

/-- For a cross-cut, `c \ J` is the arc minus its ends: connected, inside `polyInterior J`. -/
theorem IsCrosscut.diff_props {J c : Set Pt} (hc : IsCrosscut J c) :
    IsConnected (c \ J) ∧ c \ J ⊆ polyInterior J := by
  obtain ⟨a, b, -, harc, hJ, hint⟩ := hc
  rw [← diff_eq_diff_of_inter_eq hJ]
  exact ⟨harc.isConnected_diff_ends, hint⟩

/-- The component of a point of `A` in the union of two disjoint open sets `A`, `B` is its
component in `A`. -/
theorem connectedComponentIn_union_of_disjoint_open {A B : Set Pt} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : Disjoint A B) {x : Pt} (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x = connectedComponentIn A x := by
  apply subset_antisymm
  · have hsub : connectedComponentIn (A ∪ B) x ⊆ A ∪ B := connectedComponentIn_subset _ _
    rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn A B hA hB
      hsub (by rw [hAB.inter_eq, inter_empty]) with h | h
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (Or.inl hx)) h
    · exact absurd (h (mem_connectedComponentIn (Or.inl hx))) (hAB.notMem_of_mem_left hx)
  · exact connectedComponentIn_mono _ subset_union_left

/-- The points where a cross-cut of `J` lying (off `J`) in a set `S` meets `J` lie in
`closure S ∩ J`. -/
theorem IsCrosscut.inter_subset_side {J c' S α : Set Pt} (hc' : IsCrosscut J c')
    (hside : c' \ J ⊆ S) (hcl : closure S ∩ J = α) : c' ∩ J ⊆ α := by
  obtain ⟨a, b, -, harc, hJ', -⟩ := hc'
  have hside' : c' \ {a, b} ⊆ S := (diff_eq_diff_of_inter_eq hJ').symm ▸ hside
  rintro y ⟨hy, hyJ⟩
  have hyab : y ∈ ({a, b} : Set Pt) := by rw [← hJ']; exact ⟨hy, hyJ⟩
  rw [← hcl]
  refine ⟨?_, hyJ⟩
  rcases hyab with rfl | rfl
  · exact closure_mono hside' harc.left_mem_closure_diff
  · exact closure_mono hside' harc.right_mem_closure_diff

/-- A cross-cut of `J` whose part off `J` lies in `polyInterior (α ∪ c)` (one side of the cross-cut
`c`, `crosscut`) and which meets `c` only in `J` is a cross-cut of `α ∪ c`. (Its ends are in
`closure (polyInterior (α ∪ c)) ∩ J = α`, the closure clause of `crosscut`; it meets `c` only in
its ends, as `c' ∩ c ⊆ J ∩ c' = ends`.)

**Change of shape.** The skeleton's `hside : ∀ a b, IsSimplePolyArc c' a b → c' \ {a, b} ⊆ …` is
replaced by `hside : c' \ J ⊆ polyInterior (α ∪ c)`; for a cross-cut, `c' ∩ J = {a, b}`, so
`c' \ J = c' \ {a, b}` and no ends need to be named. The skeleton's hypothesis `hΓ` (that `α ∪ c` is a
simple closed polygon) is not used and was dropped. -/
theorem IsCrosscut.of_side {J c c' α : Set Pt} (hc' : IsCrosscut J c') (hα : α ⊆ J)
    (hcl : closure (polyInterior (α ∪ c)) ∩ J = α) (hcc : c' ∩ c ⊆ J)
    (hside : c' \ J ⊆ polyInterior (α ∪ c)) :
    IsCrosscut (α ∪ c) c' := by
  have hends := hc'.inter_subset_side hside hcl
  obtain ⟨a, b, hab, harc, hJ', hint⟩ := hc'
  have hdiff := diff_eq_diff_of_inter_eq hJ'
  refine ⟨a, b, hab, harc, ?_, hdiff ▸ hside⟩
  ext y
  constructor
  · rintro ⟨hy, hyΓ⟩
    have hyJ : y ∈ J := hyΓ.elim (fun h => hα h) (fun h => hcc ⟨hy, h⟩)
    rw [← hJ']; exact ⟨hy, hyJ⟩
  · intro hy
    have hy' : y ∈ c' ∩ J := by rw [hJ']; exact hy
    exact ⟨hy'.1, Or.inl (hends hy')⟩

/-- **The cross-cut induction.** For a cross-cut family `C` of `J`, every component of
`polyInterior J \ ⋃ C` is the interior of a simple closed polygon contained in `J ∪ ⋃ C`.

Induction on `C.card`. `C = ∅`: the component is `polyInterior J` (connected, `polyInterior_eq`).
Otherwise pick `c ∈ C`, `crosscut` gives `α₁`, `α₂`, `Γᵢ = αᵢ ∪ c`, `Uᵢ = polyInterior Γᵢ` with
`polyInterior J \ c = U₁ ⊔ U₂`. For `c' ∈ C.erase c`, `c' \ J` (the arc minus its ends) is connected
(`isConnected_diff_ends`), lies in `polyInterior J \ c` (`c' ∩ c ⊆ J`), so lies in `U₁` or in `U₂`;
let `Cᵢ` be those with `c' \ J ⊆ Uᵢ`. Each `Cᵢ` is a cross-cut family of `Γᵢ` (`IsCrosscut.of_side`;
pairwise: `c' ∩ c'' ⊆ c' ∩ J ⊆ αᵢ`, `IsCrosscut.inter_subset_side`). Then
`polyInterior J \ ⋃ C = (U₁ \ ⋃ C₁) ⊔ (U₂ \ ⋃ C₂)` — a point of `U₁` off `J` lying on a cross-cut of
`C₂` would lie in `U₂` — both pieces open, so the component of `x ∈ U₁ \ ⋃ C₁` in the union is its
component in `U₁ \ ⋃ C₁` (`connectedComponentIn_union_of_disjoint_open`), a polygon interior by
induction (`C₁.card < C.card`), with polygon `⊆ Γ₁ ∪ ⋃ C₁ ⊆ J ∪ ⋃ C`. -/
theorem PlaneFacts.components_of_crosscuts (hPF : PlaneFacts) {J : Set Pt}
    (hJ : IsSimpleClosedPolygon J) {C : Finset (Set Pt)} (hC : IsCrosscutFamily J C) {x : Pt}
    (hx : x ∈ polyInterior J \ ⋃ c ∈ C, c) :
    ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧ Γ ⊆ J ∪ ⋃ c ∈ C, c ∧
      connectedComponentIn (polyInterior J \ ⋃ c ∈ C, c) x = polyInterior Γ := by
  obtain ⟨n, hn⟩ : ∃ n, C.card = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing J C x with
  | _ n ih =>
  rcases C.eq_empty_or_nonempty with rfl | ⟨c, hcC⟩
  · refine ⟨J, hJ, subset_union_left, ?_⟩
    have h0 : (⋃ c ∈ (∅ : Finset (Set Pt)), c) = ∅ := by simp
    rw [h0, diff_empty] at hx ⊢
    exact (hPF.polyInterior_eq hJ).2.1.isPreconnected.connectedComponentIn hx
  obtain ⟨a, b, hab, hcarc, hcJ, hcU⟩ := hC.1 c hcC
  obtain ⟨α₁, α₂, -, -, hαU, -, hΓ₁, hΓ₂, hsplit, hdisj, hcl₁, hcl₂⟩ :=
    hPF.crosscut hJ hab hcarc hcJ hcU
  have hα₁J : α₁ ⊆ J := hαU ▸ subset_union_left
  have hα₂J : α₂ ⊆ J := hαU ▸ subset_union_right
  have hU₁o : IsOpen (polyInterior (α₁ ∪ c)) := (hPF.polyInterior_eq hΓ₁).1
  have hU₂o : IsOpen (polyInterior (α₂ ∪ c)) := (hPF.polyInterior_eq hΓ₂).1
  -- the other cross-cuts lie, off `J`, on one side of `c`
  have hother : ∀ c' ∈ C.erase c,
      c' \ J ⊆ polyInterior (α₁ ∪ c) ∨ c' \ J ⊆ polyInterior (α₂ ∪ c) := by
    intro c' hc'
    obtain ⟨hne, hc'C⟩ := Finset.mem_erase.1 hc'
    obtain ⟨hconn, hint⟩ := (hC.1 c' hc'C).diff_props
    refine isPreconnected_iff_subset_of_disjoint.1 hconn.isPreconnected _ _ hU₁o hU₂o ?_
      (by rw [hdisj.inter_eq, inter_empty])
    intro y hy
    rw [← hsplit]
    exact ⟨hint hy, fun hyc => hy.2 (hC.2 c' hc'C c hcC hne ⟨hy.1, hyc⟩)⟩
  -- each side carries a cross-cut family
  have hfam : ∀ α : Set Pt, α ⊆ J → closure (polyInterior (α ∪ c)) ∩ J = α →
      IsCrosscutFamily (α ∪ c) ((C.erase c).filter fun c' => c' \ J ⊆ polyInterior (α ∪ c)) := by
    intro α hαJ hcl
    have hmem : ∀ c' ∈ (C.erase c).filter (fun c' => c' \ J ⊆ polyInterior (α ∪ c)),
        c' ∈ C ∧ c' ≠ c ∧ c' \ J ⊆ polyInterior (α ∪ c) := fun c' hc' => by
      obtain ⟨hc'e, hside⟩ := Finset.mem_filter.1 hc'
      obtain ⟨hne, hc'C⟩ := Finset.mem_erase.1 hc'e
      exact ⟨hc'C, hne, hside⟩
    refine ⟨fun c' hc' => ?_, fun c' hc' c'' hc'' hne y hy => ?_⟩
    · obtain ⟨hc'C, hne, hside⟩ := hmem c' hc'
      exact (hC.1 c' hc'C).of_side hαJ hcl (hC.2 c' hc'C c hcC hne) hside
    · obtain ⟨hc'C, -, hside⟩ := hmem c' hc'
      obtain ⟨hc''C, -, -⟩ := hmem c'' hc''
      have hyJ : y ∈ J := hC.2 c' hc'C c'' hc''C hne hy
      exact Or.inl ((hC.1 c' hc'C).inter_subset_side hside hcl ⟨hy.1, hyJ⟩)
  set C₁ := (C.erase c).filter fun c' => c' \ J ⊆ polyInterior (α₁ ∪ c) with hC₁
  set C₂ := (C.erase c).filter fun c' => c' \ J ⊆ polyInterior (α₂ ∪ c) with hC₂
  have hC₁C : ∀ c' ∈ C₁, c' ∈ C := fun c' hc' =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ hc')
  have hC₂C : ∀ c' ∈ C₂, c' ∈ C := fun c' hc' =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ hc')
  -- the decomposition of `polyInterior J \ ⋃ C`
  have hdec : polyInterior J \ ⋃ c' ∈ C, c' =
      (polyInterior (α₁ ∪ c) \ ⋃ c' ∈ C₁, c') ∪ (polyInterior (α₂ ∪ c) \ ⋃ c' ∈ C₂, c') := by
    ext y
    simp only [mem_diff, mem_union, mem_iUnion, exists_prop, not_exists, not_and]
    constructor
    · rintro ⟨hyU, hyC⟩
      have : y ∈ polyInterior (α₁ ∪ c) ∪ polyInterior (α₂ ∪ c) := by
        rw [← hsplit]; exact ⟨hyU, hyC c hcC⟩
      rcases this with h | h
      · exact Or.inl ⟨h, fun c' hc' => hyC c' (hC₁C c' hc')⟩
      · exact Or.inr ⟨h, fun c' hc' => hyC c' (hC₂C c' hc')⟩
    · have side : ∀ (V W : Set Pt) (D : Finset (Set Pt)), (V = polyInterior (α₁ ∪ c) ∧
          W = polyInterior (α₂ ∪ c) ∨ V = polyInterior (α₂ ∪ c) ∧ W = polyInterior (α₁ ∪ c)) →
          (∀ c' ∈ C.erase c, c' \ J ⊆ V ∨ c' \ J ⊆ W) →
          (∀ c' ∈ C.erase c, c' \ J ⊆ V → c' ∈ D) →
          y ∈ V → (∀ c' ∈ D, y ∉ c') → y ∈ polyInterior J ∧ ∀ c' ∈ C, y ∉ c' := by
        intro V W D hVW hVW' hD hyV hyD
        have hVsub : V ⊆ polyInterior J \ c := by
          rw [hsplit]; rcases hVW with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact subset_union_left
          · exact subset_union_right
        have hVWd : Disjoint V W := by
          rcases hVW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hdisj
          · exact hdisj.symm
        have hyU := hVsub hyV
        refine ⟨hyU.1, fun c' hc' hyc' => ?_⟩
        by_cases hcc' : c' = c
        · subst hcc'; exact hyU.2 hyc'
        · have hc'e : c' ∈ C.erase c := Finset.mem_erase.2 ⟨hcc', hc'⟩
          rcases hVW' c' hc'e with h1 | h2
          · exact hyD c' (hD c' hc'e h1) hyc'
          · exact hVWd.notMem_of_mem_left hyV (h2 ⟨hyc', hyU.1.1⟩)
      rintro (⟨h, hyC⟩ | ⟨h, hyC⟩)
      · exact side _ _ C₁ (Or.inl ⟨rfl, rfl⟩) hother
          (fun c' hc' h' => Finset.mem_filter.2 ⟨hc', h'⟩) h hyC
      · exact side _ _ C₂ (Or.inr ⟨rfl, rfl⟩) (fun c' hc' => (hother c' hc').symm)
          (fun c' hc' h' => Finset.mem_filter.2 ⟨hc', h'⟩) h hyC
  have hclosed : ∀ D : Finset (Set Pt), (∀ c' ∈ D, c' ∈ C) → IsClosed (⋃ c' ∈ D, c') :=
    fun D hD => isClosed_biUnion_finset fun c' hc' => by
      obtain ⟨a', b', -, harc', -⟩ := hC.1 c' (hD c' hc')
      exact harc'.isContinuum.1.isClosed
  have hO₁ : IsOpen (polyInterior (α₁ ∪ c) \ ⋃ c' ∈ C₁, c') := hU₁o.sdiff (hclosed C₁ hC₁C)
  have hO₂ : IsOpen (polyInterior (α₂ ∪ c) \ ⋃ c' ∈ C₂, c') := hU₂o.sdiff (hclosed C₂ hC₂C)
  have hD : Disjoint (polyInterior (α₁ ∪ c) \ ⋃ c' ∈ C₁, c')
      (polyInterior (α₂ ∪ c) \ ⋃ c' ∈ C₂, c') := hdisj.mono diff_subset diff_subset
  have hcard : ∀ D : Finset (Set Pt), D = C₁ ∨ D = C₂ → D.card < n := by
    rintro D (rfl | rfl) <;>
    exact hn ▸ lt_of_le_of_lt (Finset.card_filter_le _ _) (Finset.card_erase_lt_of_mem hcC)
  have hsubU : ∀ (α : Set Pt) (D : Finset (Set Pt)), α ⊆ J → (∀ c' ∈ D, c' ∈ C) →
      α ∪ c ∪ (⋃ c' ∈ D, c') ⊆ J ∪ ⋃ c' ∈ C, c' := by
    rintro α D hαJ hDC y ((hy | hy) | hy)
    · exact Or.inl (hαJ hy)
    · exact Or.inr (mem_iUnion₂.2 ⟨c, hcC, hy⟩)
    · obtain ⟨c', hc', hyc'⟩ := mem_iUnion₂.1 hy
      exact Or.inr (mem_iUnion₂.2 ⟨c', hDC c' hc', hyc'⟩)
  rw [hdec] at hx ⊢
  rcases hx with hx₁ | hx₂
  · rw [connectedComponentIn_union_of_disjoint_open hO₁ hO₂ hD hx₁]
    obtain ⟨Γ, hΓ, hΓsub, heq⟩ := ih _ (hcard C₁ (Or.inl rfl)) hΓ₁ (hfam α₁ hα₁J hcl₁) hx₁ rfl
    exact ⟨Γ, hΓ, hΓsub.trans (hsubU α₁ C₁ hα₁J hC₁C), heq⟩
  · rw [union_comm (polyInterior (α₁ ∪ c) \ ⋃ c' ∈ C₁, c'),
      connectedComponentIn_union_of_disjoint_open hO₂ hO₁ hD.symm hx₂]
    obtain ⟨Γ, hΓ, hΓsub, heq⟩ := ih _ (hcard C₂ (Or.inr rfl)) hΓ₂ (hfam α₂ hα₂J hcl₂) hx₂ rfl
    exact ⟨Γ, hΓ, hΓsub.trans (hsubU α₂ C₂ hα₂J hC₂C), heq⟩

/-! ### 2. Decomposing an arc and a polygon at finitely many points -/

/-- **Decomposing a simple arc at a finite set `X` of interior points**: finitely many simple
sub-arcs with ends in `X ∪ {p, q}`, covering the arc, meeting each other and `X ∪ {p, q}` only at
their ends. Induction on `X` (`Finset.induction`): remove `x ∈ X`, decompose, and split the piece
containing `x` at `x` (`IsSimplePolyArc.split`). -/
theorem exists_arc_decomposition {β : Set Pt} {p q : Pt} (hβ : IsSimplePolyArc β p q)
    (X : Finset Pt) (hX : ∀ x ∈ X, x ∈ β ∧ x ≠ p ∧ x ≠ q) :
    ∃ A : Finset (Set Pt), (⋃ γ ∈ A, γ) = β ∧
      (∀ γ ∈ A, ∃ s t : Pt, IsSimplePolyArc γ s t ∧ s ∈ insert p (insert q (X : Set Pt)) ∧
        t ∈ insert p (insert q (X : Set Pt)) ∧ γ ∩ insert p (insert q (X : Set Pt)) = {s, t}) ∧
      ∀ γ ∈ A, ∀ γ' ∈ A, γ ≠ γ' → γ ∩ γ' ⊆ insert p (insert q (X : Set Pt)) := by
  induction X using Finset.induction_on with
  | empty =>
    refine ⟨{β}, by simp, ?_, ?_⟩
    · intro γ hγ
      rw [Finset.mem_singleton] at hγ
      subst hγ
      refine ⟨p, q, hβ, by simp, by simp, ?_⟩
      rw [Finset.coe_empty, insert_empty_eq, inter_eq_right]
      rintro y (rfl | rfl)
      · exact hβ.left_mem
      · exact hβ.right_mem
    · intro γ hγ γ' hγ' hne
      rw [Finset.mem_singleton] at hγ hγ'
      exact absurd (hγ.trans hγ'.symm) hne
  | insert x X hxX ih =>
    obtain ⟨A, hAU, hApc, hApw⟩ := ih (fun y hy => hX y (Finset.mem_insert_of_mem hy))
    obtain ⟨hxβ, hxp, hxq⟩ := hX x (Finset.mem_insert_self x X)
    set Y : Set Pt := insert p (insert q (X : Set Pt)) with hY
    have hY' : insert p (insert q ((insert x X : Finset Pt) : Set Pt)) = insert x Y := by
      rw [Finset.coe_insert, hY, insert_comm q x, insert_comm p x]
    rw [hY']
    have hxY : x ∉ Y := by
      rintro (h | h | h)
      · exact hxp h
      · exact hxq h
      · exact hxX h
    obtain ⟨γ₀, hγ₀A, hxγ₀⟩ := mem_iUnion₂.1 (show x ∈ ⋃ γ ∈ A, γ by rw [hAU]; exact hxβ)
    obtain ⟨s, t, harc, hs, ht, hγ₀Y⟩ := hApc γ₀ hγ₀A
    have hxs : x ≠ s := fun h => hxY (h ▸ hs)
    have hxt : x ≠ t := fun h => hxY (h ▸ ht)
    obtain ⟨γ₁, γ₂, h₁, h₂, h12U, h12I⟩ := harc.split hxγ₀ hxs hxt
    have hγ₁ : γ₁ ⊆ γ₀ := h12U ▸ subset_union_left
    have hγ₂ : γ₂ ⊆ γ₀ := h12U ▸ subset_union_right
    have hxA : ∀ γ ∈ A, γ ≠ γ₀ → x ∉ γ := fun γ hγ hne hxγ =>
      hxY (hApw γ hγ γ₀ hγ₀A hne ⟨hxγ, hxγ₀⟩)
    have hsY : ∀ y ∈ γ₀, y ∈ Y → y = s ∨ y = t := fun y hy hyY => by
      have : y ∈ γ₀ ∩ Y := ⟨hy, hyY⟩
      rw [hγ₀Y] at this
      exact this
    refine ⟨insert γ₁ (insert γ₂ (A.erase γ₀)), ?_, ?_, ?_⟩
    · rw [← hAU]
      ext y
      simp only [Finset.mem_insert, Finset.mem_erase, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨γ, hγ, hy⟩
        rcases hγ with h | h | ⟨-, hγ⟩
        · rw [h] at hy; exact ⟨γ₀, hγ₀A, hγ₁ hy⟩
        · rw [h] at hy; exact ⟨γ₀, hγ₀A, hγ₂ hy⟩
        · exact ⟨γ, hγ, hy⟩
      · rintro ⟨γ, hγ, hy⟩
        by_cases h : γ = γ₀
        · rw [h, ← h12U] at hy
          rcases hy with hy | hy
          · exact ⟨_, Or.inl rfl, hy⟩
          · exact ⟨_, Or.inr (Or.inl rfl), hy⟩
        · exact ⟨γ, Or.inr (Or.inr ⟨h, hγ⟩), hy⟩
    · intro γ hγ
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hγ
      rcases hγ with h | h | ⟨hne, hγA⟩
      · rw [h]
        refine ⟨s, x, h₁, mem_insert_of_mem _ hs, mem_insert _ _, ?_⟩
        ext y
        constructor
        · rintro ⟨hy, hyY⟩
          rcases hyY with hyx | hyY
          · exact Or.inr hyx
          · rcases hsY y (hγ₁ hy) hyY with hys | hyt
            · exact Or.inl hys
            · exfalso
              have : y ∈ γ₁ ∩ γ₂ := ⟨hy, hyt ▸ h₂.right_mem⟩
              rw [h12I] at this
              exact hxt (hyt ▸ this.symm)
        · rintro (hy | hy) <;> rw [hy]
          · exact ⟨h₁.left_mem, mem_insert_of_mem _ hs⟩
          · exact ⟨h₁.right_mem, mem_insert _ _⟩
      · rw [h]
        refine ⟨x, t, h₂, mem_insert _ _, mem_insert_of_mem _ ht, ?_⟩
        ext y
        constructor
        · rintro ⟨hy, hyY⟩
          rcases hyY with hyx | hyY
          · exact Or.inl hyx
          · rcases hsY y (hγ₂ hy) hyY with hys | hyt
            · exfalso
              have : y ∈ γ₁ ∩ γ₂ := ⟨hys ▸ h₁.left_mem, hy⟩
              rw [h12I] at this
              exact hxs (hys ▸ this.symm)
            · exact Or.inr hyt
        · rintro (hy | hy) <;> rw [hy]
          · exact ⟨h₂.left_mem, mem_insert _ _⟩
          · exact ⟨h₂.right_mem, mem_insert_of_mem _ ht⟩
      · obtain ⟨s', t', harc', hs', ht', hY'⟩ := hApc γ hγA
        refine ⟨s', t', harc', mem_insert_of_mem _ hs', mem_insert_of_mem _ ht', ?_⟩
        rw [← hY']
        ext y
        constructor
        · rintro ⟨hy, hyx | hyY⟩
          · exact absurd (hyx ▸ hy) (hxA _ hγA hne)
          · exact ⟨hy, hyY⟩
        · rintro ⟨hy, hyY⟩
          exact ⟨hy, mem_insert_of_mem _ hyY⟩
    · intro γ hγ γ' hγ' hne y hy
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hγ hγ'
      have h12 : ∀ y ∈ γ₁, y ∈ γ₂ → y ∈ insert x Y := fun y hy1 hy2 => by
        have : y ∈ γ₁ ∩ γ₂ := ⟨hy1, hy2⟩
        rw [h12I] at this
        exact Or.inl this
      have h0A : ∀ y ∈ γ₀, ∀ δ ∈ A, δ ≠ γ₀ → y ∈ δ → y ∈ insert x Y := fun y hy δ hδ hne hyδ =>
        mem_insert_of_mem _ (hApw γ₀ hγ₀A δ hδ hne.symm ⟨hy, hyδ⟩)
      rcases hγ with h | h | ⟨hne1, hA1⟩ <;> rcases hγ' with h' | h' | ⟨hne2, hA2⟩
      · exact absurd (h.trans h'.symm) hne
      · rw [h, h'] at hy; exact h12 y hy.1 hy.2
      · rw [h] at hy; exact h0A y (hγ₁ hy.1) γ' hA2 hne2 hy.2
      · rw [h, h'] at hy; exact h12 y hy.2 hy.1
      · exact absurd (h.trans h'.symm) hne
      · rw [h] at hy; exact h0A y (hγ₂ hy.1) γ' hA2 hne2 hy.2
      · rw [h'] at hy; exact h0A y (hγ₁ hy.2) γ hA1 hne1 hy.1
      · rw [h'] at hy; exact h0A y (hγ₂ hy.2) γ hA1 hne1 hy.1
      · exact mem_insert_of_mem _ (hApw γ hA1 γ' hA2 hne hy)

/-- **Decomposing a simple closed polygon at a finite set `X ⊆ P` with at least two points** into
simple arcs with ends in `X`, covering `P`, meeting each other and `X` only at their ends.
(`split_two` at two points of `X`, then `exists_arc_decomposition` on each arc with the remaining
points of `X` on it.) -/
theorem exists_polygon_decomposition {P : Set Pt} (hP : IsSimpleClosedPolygon P) (X : Finset Pt)
    (hXP : (X : Set Pt) ⊆ P) (hX2 : 2 ≤ X.card) :
    ∃ A : Finset (Set Pt), (⋃ γ ∈ A, γ) = P ∧
      (∀ γ ∈ A, ∃ s t : Pt, IsSimplePolyArc γ s t ∧ s ∈ X ∧ t ∈ X ∧ γ ∩ X = {s, t}) ∧
      ∀ γ ∈ A, ∀ γ' ∈ A, γ ≠ γ' → γ ∩ γ' ⊆ X := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hX2
  obtain ⟨α₁, α₂, h₁, h₂, hU, hI⟩ := hP.split_two (hXP ha) (hXP hb) hab
  have side : ∀ α : Set Pt, IsSimplePolyArc α a b → ∃ A : Finset (Set Pt), (⋃ γ ∈ A, γ) = α ∧
      (∀ γ ∈ A, ∃ s t : Pt, IsSimplePolyArc γ s t ∧ s ∈ X ∧ t ∈ X ∧ γ ∩ X = {s, t}) ∧
      ∀ γ ∈ A, ∀ γ' ∈ A, γ ≠ γ' → γ ∩ γ' ⊆ X := by
    intro α hα
    set X' := ((X.erase a).erase b).filter (· ∈ α) with hX'
    have hmem : ∀ y, y ∈ X' ↔ (y ≠ b ∧ y ≠ a ∧ y ∈ X) ∧ y ∈ α := fun y => by
      rw [hX', Finset.mem_filter, Finset.mem_erase, Finset.mem_erase]
    obtain ⟨A, hAU, hAp, hAw⟩ := exists_arc_decomposition hα X' (fun y hy => by
      rw [hmem] at hy; exact ⟨hy.2, hy.1.2.1, hy.1.1⟩)
    have hYX : insert a (insert b (X' : Set Pt)) ⊆ X := by
      rintro y (rfl | rfl | hy)
      · exact ha
      · exact hb
      · rw [Finset.mem_coe, hmem] at hy; exact hy.1.2.2
    have hXY : ∀ y ∈ α, y ∈ X → y ∈ insert a (insert b (X' : Set Pt)) := by
      intro y hyα hyX
      by_cases hya : y = a
      · exact Or.inl hya
      by_cases hyb : y = b
      · exact Or.inr (Or.inl hyb)
      exact Or.inr (Or.inr (by rw [Finset.mem_coe, hmem]; exact ⟨⟨hyb, hya, hyX⟩, hyα⟩))
    have hγα : ∀ γ ∈ A, γ ⊆ α := fun γ hγ y hy => by
      rw [← hAU]; exact mem_iUnion₂.2 ⟨γ, hγ, hy⟩
    refine ⟨A, hAU, fun γ hγ => ?_, fun γ hγ γ' hγ' hne => (hAw γ hγ γ' hγ' hne).trans hYX⟩
    obtain ⟨s, t, harc, hs, ht, hγY⟩ := hAp γ hγ
    refine ⟨s, t, harc, hYX hs, hYX ht, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hyX⟩
      rw [← hγY]
      exact ⟨hy, hXY y (hγα γ hγ hy) hyX⟩
    · intro hy
      rw [← hγY] at hy
      exact ⟨hy.1, hYX hy.2⟩
  obtain ⟨A₁, hA₁U, hA₁p, hA₁w⟩ := side α₁ h₁
  obtain ⟨A₂, hA₂U, hA₂p, hA₂w⟩ := side α₂ h₂
  have hγα : ∀ (A : Finset (Set Pt)) (α : Set Pt), (⋃ γ ∈ A, γ) = α → ∀ γ ∈ A, γ ⊆ α :=
    fun A α hAU γ hγ y hy => by rw [← hAU]; exact mem_iUnion₂.2 ⟨γ, hγ, hy⟩
  have hab' : α₁ ∩ α₂ ⊆ X := by
    rw [hI]; rintro y (rfl | rfl)
    · exact ha
    · exact hb
  refine ⟨A₁ ∪ A₂, ?_, ?_, ?_⟩
  · rw [Finset.set_biUnion_union, hA₁U, hA₂U, hU]
  · intro γ hγ
    rcases Finset.mem_union.1 hγ with h | h
    · exact hA₁p γ h
    · exact hA₂p γ h
  · intro γ hγ γ' hγ' hne
    rcases Finset.mem_union.1 hγ with h | h <;> rcases Finset.mem_union.1 hγ' with h' | h'
    · exact hA₁w γ h γ' h' hne
    · exact (inter_subset_inter (hγα A₁ α₁ hA₁U γ h) (hγα A₂ α₂ hA₂U γ' h')).trans hab'
    · exact (inter_subset_inter (hγα A₂ α₂ hA₂U γ h) (hγα A₁ α₁ hA₁U γ' h')).trans
        (by rw [inter_comm]; exact hab')
    · exact hA₂w γ h γ' h' hne

/-! ### 3. The cross-cut family of `P` in `J` -/

/-- A connected set missing the frontier of `S` and meeting `S` lies in `S`. -/
theorem subset_of_isConnected_of_disjoint_frontier {S T : Set Pt} (hT : IsConnected T)
    (hfr : Disjoint T (frontier S)) (hne : (T ∩ S).Nonempty) : T ⊆ S := by
  rcases isPreconnected_iff_subset_of_disjoint.1 hT.isPreconnected (interior S) (closure S)ᶜ
    isOpen_interior isClosed_closure.isOpen_compl (fun y hy => by
      by_cases hyi : y ∈ interior S
      · exact Or.inl hyi
      · exact Or.inr fun hyc => hfr.notMem_of_mem_left hy ⟨hyc, hyi⟩)
    (by
      rw [eq_empty_iff_forall_notMem]
      rintro y ⟨-, hyi, hyc⟩
      exact hyc (interior_subset_closure hyi)) with h | h
  · exact h.trans interior_subset
  · obtain ⟨y, hyT, hyS⟩ := hne
    exact absurd (subset_closure hyS) (h hyT)

/-- **The pieces of `P` inside `polyInterior J`.** If `J`, `P` are simple closed polygons with
`X = J ∩ P` finite of cardinality `≥ 2`, the pieces of `P` between consecutive points of `X`
(`exists_polygon_decomposition`) whose interiors lie in `polyInterior J` form a cross-cut family
`C` of `J` with `polyInterior J \ P = polyInterior J \ ⋃ C`. (A piece minus its ends is connected
and misses `J` — `γ ∩ J = γ ∩ P ∩ J = γ ∩ X = ends` — so if it meets `polyInterior J` it lies in it
(`subset_of_isConnected_of_disjoint_frontier`); pairwise `γ ∩ γ' ⊆ X ⊆ J`.) -/
theorem PlaneFacts.exists_crosscutFamily (hPF : PlaneFacts) {J P : Set Pt}
    (hJ : IsSimpleClosedPolygon J) (hP : IsSimpleClosedPolygon P) (hfin : (J ∩ P).Finite)
    (h2 : 2 ≤ hfin.toFinset.card) :
    ∃ C : Finset (Set Pt), IsCrosscutFamily J C ∧ (∀ c ∈ C, c ⊆ P) ∧
      polyInterior J \ P = polyInterior J \ ⋃ c ∈ C, c := by
  set X := hfin.toFinset with hX
  have hXJ : (X : Set Pt) = J ∩ P := hfin.coe_toFinset
  obtain ⟨A, hAU, hAp, hAw⟩ :=
    exists_polygon_decomposition hP X (by rw [hXJ]; exact inter_subset_right) h2
  have hfr : frontier (polyInterior J) = J := (hPF.polyInterior_eq hJ).2.2.2.1
  have hγP : ∀ γ ∈ A, γ ⊆ P := fun γ hγ y hy => by rw [← hAU]; exact mem_iUnion₂.2 ⟨γ, hγ, hy⟩
  refine ⟨A.filter (fun γ => (γ ∩ polyInterior J).Nonempty), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hγA, ⟨z, hzγ, hzU⟩⟩ := Finset.mem_filter.1 hγ
    obtain ⟨s, t, harc, -, -, hγX⟩ := hAp γ hγA
    have hγJ : γ ∩ J = {s, t} := by
      rw [← hγX, hXJ]
      ext y
      constructor
      · rintro ⟨hy, hyJ⟩; exact ⟨hy, hyJ, hγP γ hγA hy⟩
      · rintro ⟨hy, hyJ, -⟩; exact ⟨hy, hyJ⟩
    refine ⟨s, t, harc.ne, harc, hγJ, ?_⟩
    refine subset_of_isConnected_of_disjoint_frontier harc.isConnected_diff_ends ?_
      ⟨z, ⟨hzγ, ?_⟩, hzU⟩
    · rw [hfr, disjoint_left]
      rintro y ⟨hy, hyst⟩ hyJ
      exact hyst (by rw [← hγJ]; exact ⟨hy, hyJ⟩)
    · intro hz
      rw [← hγJ] at hz
      exact hzU.1 hz.2
  · intro γ hγ γ' hγ' hne
    exact (hAw γ (Finset.mem_filter.1 hγ).1 γ' (Finset.mem_filter.1 hγ').1 hne).trans
      (by rw [hXJ]; exact inter_subset_left)
  · intro γ hγ
    exact hγP γ (Finset.mem_filter.1 hγ).1
  · ext y
    simp only [mem_diff, mem_iUnion, exists_prop, Finset.mem_filter, not_exists, not_and]
    constructor
    · rintro ⟨hyU, hyP⟩
      exact ⟨hyU, fun γ hγ hyγ => hyP (hγP γ hγ.1 hyγ)⟩
    · rintro ⟨hyU, h⟩
      refine ⟨hyU, fun hyP => ?_⟩
      rw [← hAU] at hyP
      obtain ⟨γ, hγA, hyγ⟩ := mem_iUnion₂.1 hyP
      exact h γ ⟨hγA, ⟨y, hyγ, hyU⟩⟩ hyγ

/-! ### 4. Identification of the components; the degenerate cases -/

/-- The component of `x ∈ U ∩ N` in `U ∩ N` is its component in `U \ P`, where
`N = polyInterior P` and `P = frontier N` (`PlaneFacts.polyInterior_eq`). The skeleton's hypothesis
`hU : IsOpen U` is not used and was dropped. -/
theorem PlaneFacts.connectedComponentIn_inter_eq (hPF : PlaneFacts) {P : Set Pt}
    (hP : IsSimpleClosedPolygon P) {U : Set Pt} {x : Pt}
    (hx : x ∈ U ∩ polyInterior P) :
    connectedComponentIn (U ∩ polyInterior P) x = connectedComponentIn (U \ P) x := by
  have hfr := (hPF.polyInterior_eq hP).2.2.2.1
  have hxUP : x ∈ U \ P := ⟨hx.1, hx.2.1⟩
  apply subset_antisymm
  · exact connectedComponentIn_mono _ (fun y hy => ⟨hy.1, hy.2.1⟩)
  · have hsubN : connectedComponentIn (U \ P) x ⊆ polyInterior P := by
      refine subset_of_isConnected_of_disjoint_frontier
        (isConnected_connectedComponentIn_iff.2 hxUP) ?_
        ⟨x, mem_connectedComponentIn hxUP, hx.2⟩
      rw [hfr, disjoint_left]
      intro y hy hyP
      exact (connectedComponentIn_subset _ _ hy).2 hyP
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxUP)
      (fun y hy => ⟨(connectedComponentIn_subset _ _ hy).1, hsubN hy⟩)

/-- If the polygon `P` lies in `polyInterior J ∪ J`, then `polyInterior P ⊆ polyInterior J`. (The
exterior `V` of `J` is connected, unbounded and misses `P`, so it misses the bounded
`polyInterior P`; as `polyInterior P` is open and `J ⊆ closure V`, it misses `J` too.) -/
theorem PlaneFacts.polyInterior_subset_of_subset (hPF : PlaneFacts) {J P : Set Pt}
    (hJ : IsSimpleClosedPolygon J) (hP : IsSimpleClosedPolygon P)
    (hPJ : P ⊆ polyInterior J ∪ J) : polyInterior P ⊆ polyInterior J := by
  obtain ⟨V, -, -, hJV, hd, -, -, -, hfV, hVc, hVb⟩ := hPF.split hJ
  obtain ⟨hNo, -, hNb, hNfr, -⟩ := hPF.polyInterior_eq hP
  have hVJ : ∀ y ∈ V, y ∉ J := fun y hyV => by
    have : y ∈ Jᶜ := by rw [hJV]; exact Or.inr hyV
    exact this
  have hVP : Disjoint V (frontier (polyInterior P)) := by
    rw [hNfr, disjoint_left]
    intro y hyV hyP
    rcases hPJ hyP with h | h
    · exact hd.notMem_of_mem_left h hyV
    · exact hVJ y hyV h
  have hVN : Disjoint V (polyInterior P) := by
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne
    exact hVb (hNb.subset
      (subset_of_isConnected_of_disjoint_frontier hVc hVP (nonempty_iff_ne_empty.2 hne)))
  intro y hy
  have hyJ : y ∉ J := fun hyJ => by
    obtain ⟨z, hz⟩ := _root_.mem_closure_iff.1 (hfV y hyJ) _ hNo hy
    exact hVN.notMem_of_mem_left hz.2 hz.1
  have : y ∈ polyInterior J ∪ V := by rw [← hJV]; exact hyJ
  rcases this with h | h
  · exact h
  · exact absurd hy (hVN.notMem_of_mem_left h)

/-- **The main theorem: components of the intersection of two polygon interiors whose boundaries
meet in finitely many points are polygon interiors.** With `U = polyInterior J`, `N = polyInterior
P`, `X = J ∩ P`:
* `|X| ≥ 2`: `exists_crosscutFamily`, `connectedComponentIn_inter_eq`, `components_of_crosscuts`.
* `|X| ≤ 1`: then `P \ J = P \ X` is connected (`P`, or `P` minus one point).
  - `P ∩ U = ∅`: `U` is connected and misses `P = frontier N`, and `x ∈ U ∩ N`, so `U ⊆ N` and the
    component is `U = polyInterior J`.
  - `P ∩ U ≠ ∅`: `P \ J` is connected, misses `J = frontier U` and meets `U`, so `P \ J ⊆ U`, i.e.
    `P ⊆ U ∪ J`; then `N ⊆ U` (`polyInterior_subset_of_subset`) and the component is
    `N = polyInterior P`.

(This replaces the skeleton's case analysis, whose `X = ∅` and `X = {a}` arguments contain a false
step: in the `X = ∅` case `closure U = U ∪ J` does **not** miss `P`, since `P ⊆ U` there; in the
`X = {a}` case `U ∪ (J \ {a})` does not miss `P`, since `P ∩ U ≠ ∅`. The statement is unaffected.) -/
theorem PlaneFacts.component_inter_eq_polyInterior (hPF : PlaneFacts) {J P : Set Pt}
    (hJ : IsSimpleClosedPolygon J) (hP : IsSimpleClosedPolygon P) (hfin : (J ∩ P).Finite)
    {x : Pt} (hx : x ∈ polyInterior J ∩ polyInterior P) :
    ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧
      connectedComponentIn (polyInterior J ∩ polyInterior P) x = polyInterior Γ := by
  obtain ⟨-, hUc, -, hUfr, -⟩ := hPF.polyInterior_eq hJ
  obtain ⟨-, hNc, -, hNfr, -⟩ := hPF.polyInterior_eq hP
  by_cases h2 : 2 ≤ hfin.toFinset.card
  · obtain ⟨C, hC, -, heq⟩ := hPF.exists_crosscutFamily hJ hP hfin h2
    have hxC : x ∈ polyInterior J \ ⋃ c ∈ C, c := by rw [← heq]; exact ⟨hx.1, hx.2.1⟩
    obtain ⟨Γ, hΓ, -, hcomp⟩ := hPF.components_of_crosscuts hJ hC hxC
    exact ⟨Γ, hΓ, by rw [hPF.connectedComponentIn_inter_eq hP hx, heq, hcomp]⟩
  have hPJc : IsConnected (P \ J) := by
    rw [← diff_inter_self_eq_diff, ← hfin.coe_toFinset]
    rcases Nat.lt_or_ge hfin.toFinset.card 1 with h0 | h1
    · rw [Finset.card_eq_zero.1 (show hfin.toFinset.card = 0 by omega), Finset.coe_empty, diff_empty]
      exact hP.isConnected
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (show hfin.toFinset.card = 1 by omega)
      have haJP : a ∈ J ∩ P := by
        rw [← hfin.coe_toFinset, ha, Finset.coe_singleton]; exact mem_singleton a
      rw [ha, Finset.coe_singleton]
      exact hP.isConnected_diff_singleton haJP.2
  by_cases hPU : (P ∩ polyInterior J).Nonempty
  · obtain ⟨z, hzP, hzU⟩ := hPU
    have hsub : P \ J ⊆ polyInterior J :=
      subset_of_isConnected_of_disjoint_frontier hPJc (by rw [hUfr]; exact disjoint_sdiff_left)
        ⟨z, ⟨hzP, hzU.1⟩, hzU⟩
    have hNU : polyInterior P ⊆ polyInterior J :=
      hPF.polyInterior_subset_of_subset hJ hP (fun y hy => by
        by_cases hyJ : y ∈ J
        · exact Or.inr hyJ
        · exact Or.inl (hsub ⟨hy, hyJ⟩))
    refine ⟨P, hP, ?_⟩
    rw [inter_eq_right.2 hNU]
    exact hNc.isPreconnected.connectedComponentIn hx.2
  · have hUP : Disjoint (polyInterior J) P := by
      rw [disjoint_iff_inter_eq_empty, inter_comm]
      exact not_nonempty_iff_eq_empty.1 hPU
    have hUN : polyInterior J ⊆ polyInterior P :=
      subset_of_isConnected_of_disjoint_frontier hUc (by rw [hNfr]; exact hUP) ⟨x, hx.1, hx.2⟩
    refine ⟨J, hJ, ?_⟩
    rw [inter_eq_left.2 hUN]
    exact hUc.isPreconnected.connectedComponentIn hx.1

/-! ### 5. Theorem 7 -/

/-- The vertex function of the 20-gon satisfies the vertex-level predicate (the content of
`isSimpleClosedPolygon_notchedPoly`, batch 119: `notchedVertices_injective` and
`notchedVertices_edges` of `Tree7Notched`; there was no lemma of this exact name). -/
theorem isSimpleVertices_notchedVertices (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : IsSimpleVertices (notchedVertices o δ η r a b) :=
  ⟨by norm_num, notchedVertices_injective o hη hr h4 a b, notchedVertices_edges o hη hr h4 a b⟩

/-- In general position the boundaries of the polygon `polygonOf v` and of a notched square meet
in a finite set (`finite_inter_of_gp`, `notchedPoly = polygonOf notchedVertices`). -/
theorem finite_inter_notchedPoly_of_gp {n : ℕ} {v : Fin n → Pt} (o : Pt) (δ η r : ℝ) (a b : ℤ)
    (hgp : InGeneralPosition v (notchedVertices o δ η r a b)) :
    (polygonOf v ∩ notchedPoly o δ η r a b).Finite :=
  finite_inter_of_gp hgp

/-- **Theorem 7 (Bing 1951, Duke, p. 657)**, with the hypothesis its proof uses: a bounded plane
continuum no subcontinuum of which separates the plane is covered, for every `ε > 0`, by a tree
chain whose links are interiors of simple closed polygons of diameter `< ε`. (`exists_gp_cover`
gives `v`, `o δ η r I`; `J = polygonOf v`; `treeChain_of_cover` gives `G ⊆ compFamily (polyInterior J)
(notchedFamily o δ η r I)`; a member is `connectedComponentIn (polyInterior J ∩ notched …) x`, and
`notched … = polyInterior (notchedPoly …)` (`notched_eq_polyInterior`) with `notchedPoly` simple
and `J ∩ notchedPoly` finite (`finite_inter_notchedPoly_of_gp`), so
`component_inter_eq_polyInterior` applies.)

Relative form; the unconditional theorem is `HPC.Plane.theorem7_1951` in `Enc2.lean` (batch 131). -/
theorem theorem7_1951_rel (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧
      (∀ h ∈ G, ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ) ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h := by
  obtain ⟨n, v, o, δ, η, r, I, hv, hMJ, -, hη, hηr, h4, -, hcov, hdiam, htriple, hgp⟩ :=
    hPF.exists_gp_cover hM hns hε
  have hr : 0 < r := hη.trans hηr
  have hJ : IsSimpleClosedPolygon (polygonOf v) := isSimpleClosedPolygon_iff.2 ⟨n, v, hv, rfl⟩
  have hpoly : ∀ h ∈ compFamily (polyInterior (polygonOf v)) (notchedFamily o δ η r I),
      ∃ Γ, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ := by
    rintro h ⟨d, hd, y, hy, rfl⟩
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 hd
    rw [notched_eq_polyInterior o hη hr h4] at hy ⊢
    exact hPF.component_inter_eq_polyInterior hJ (isSimpleClosedPolygon_notchedPoly o hη hr h4 _ _)
      (finite_inter_notchedPoly_of_gp o δ η r _ _ (hgp ab hab)) hy
  obtain ⟨G, hGc, hG, hGd, hGM, -⟩ := treeChain_of_cover hPF hM hJ hMJ
    (D := notchedFamily o δ η r I)
    (fun d hd => by obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hd; exact isOpen_notched _ _ _ _ _ _)
    (fun d hd => by obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hd; exact isBounded_notched o hη hr _ _)
    hdiam hcov htriple hpoly
  exact ⟨G, hG, fun h hh => hpoly h (hGc h hh), hGd, hGM⟩

/-- **Bing 1951 (Duke), Theorem 6**, relative to `PlaneFacts`: a bounded plane continuum
containing no continuum that separates the plane is tree-like. Statement unchanged since batch 118.

Since batch 129 Theorem 6 is a **corollary of Theorem 7** in the repository — the reverse of Bing's
order, where Theorem 7 is extracted from the proof of Theorem 6. The reason: `janiszewski` is now
only asserted for polygonal sets, so the circular-chain argument (`compFamily_no_circular`,
`exists_theta_point`) needs the links to be interiors of simple closed polygons. The notched-square
cover of the batch-118 proof does not guarantee that (components of `polyInterior J ∩ notched …`
need not be polygon interiors when `J` meets a notched square in infinitely many points); the
general-position cover of `theorem7_1951` does. A tree chain of polygon interiors of mesh `< ε` is
in particular a tree chain of mesh `< ε`. (The batch-118 proof, from `exists_notched_cover_bdd`,
`enclose`, `compFamily_no_triple` and `compFamily_no_circular`, is recorded in
`doc/batches/REPORT-batch129.md`.)

Relative form; the unconditional theorem is `HPC.Plane.theorem6_1951` in `Enc2.lean` (batch 131).

Batch 133: `IsTreeLike` now also asks the links to be bounded; the links here are polygon
interiors, bounded by `PlaneFacts.polyInterior_eq`. Statement unchanged. -/
theorem theorem6_1951_rel (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) : IsTreeLike M := by
  refine ⟨hM, fun ε hε => ?_⟩
  obtain ⟨G, hG, hpoly, hGd, hGM⟩ := theorem7_1951_rel hPF hM hns hε
  refine ⟨G, hG, fun h hh => ⟨?_, hGd h hh⟩, hGM⟩
  obtain ⟨Γ, hΓ, rfl⟩ := hpoly h hh
  exact (hPF.polyInterior_eq hΓ).2.2.1

/-- **Theorem 7, weak form** (batch 119; moved here and re-proved from `theorem7_1951` in batch 129):
the links of the tree chain are bounded, open, connected, regular open, and do not separate the
plane — as interiors of simple closed polygons (`polyInterior_eq`, `polyInterior_regular`,
`compl_polyInterior`). Statement unchanged.

Relative form; the unconditional theorem is `HPC.Plane.theorem7_weak` in `Enc2.lean` (batch 131). -/
theorem theorem7_weak_rel (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧ (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h ∧
      ∀ h ∈ G, IsOpen h ∧ IsConnected h ∧ Bornology.IsBounded h ∧
        interior (closure h) = h ∧ ¬ SeparatesPlane h := by
  obtain ⟨G, hG, hpoly, hGd, hGM⟩ := theorem7_1951_rel hPF hM hns hε
  refine ⟨G, hG, hGd, hGM, fun h hh => ?_⟩
  obtain ⟨Γ, hΓ, rfl⟩ := hpoly h hh
  obtain ⟨ho, hc, hb, -, -⟩ := hPF.polyInterior_eq hΓ
  exact ⟨ho, hc, hb, hPF.polyInterior_regular hΓ, fun hs => hs (hPF.compl_polyInterior hΓ).1⟩

end HPC.Plane
