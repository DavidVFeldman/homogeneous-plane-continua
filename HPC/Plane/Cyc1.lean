import HPC.Plane.Jct2

/-!
# Batch 127: polygonal Janiszewski, part I — straight-line graphs, mod-2 cycles, their parity,
# and Mayer–Vietoris for cycles

COMMISSION-batch127.md. The skeleton of the commission (`doc/batches/skeletons/Cyc1.lean`) with
every `sorry` replaced by a proof. Nothing in this file is `sorry`. Changes of shape (recorded in
REPORT-batch127):

* **Refutation.** `sum_vJump_even` as stated in the skeleton (no nondegeneracy) is false:
  `not_sum_vJump_even_skeleton` (`G = {(a, a), (a, b), (b, b)}` has all degrees even, since a
  degenerate segment is counted once in `deg` but its jump twice in the sum). The hypothesis
  `hnd : ∀ s ∈ G, s.1 ≠ s.2` is added to `sum_vJump_even`, `cycParity_locallyConstant`,
  `cycParity_eq_of_isPreconnected` and `separatesPts_of_cycParity_ne` (for the last three the
  degenerate example also breaks the conclusion: with only the edge `(a, b)` contributing, the
  parity jumps across the height of `a` to the left of `a`). Cycles (`IsCycle`) are nondegenerate,
  so the later batches are unaffected.
* `vertices` is marked `noncomputable` (`Finset.image` on `ℝ × ℝ` uses `Real.decidableEq`); the
  statement of `exists_proper_subdivision` is prefixed by `open Classical in` (the filter
  `segSet t ⊆ segSet s` is not decidable). Nothing else in the statements changes.
* **Representation.** A segment is an ordered pair (`Seg := Pt × Pt`), as in the skeleton. The
  subdivision produced by `exists_proper_subdivision` (`subdiv`) is normalised by the
  lexicographic order: its pieces `(u, v)` have `toLex u < toLex v`, and two such pieces with the
  same point set are equal (`eq_of_segment_eq_lex`). The pieces are *intrinsic*: the pairs of cut
  points spanning a subsegment of a segment of `S` with no cut point inside, where the cut points
  (`cutSet`) are the end points of `S` and the points which are the whole intersection of two
  segments of `S`. No sorting along segments is needed; collinear overlaps are handled by a
  parameter comparison on the common line (`subdiv_inter`, `real_pair_eq`).
* `graph_connected_of_isConnected` is kept in the skeleton's form; the decomposition uses its
  `ZMod 2` form `exists_path_zmod` and the observation `inter_subset_graphSet_inter`: if
  `graphSet A ∩ graphSet B` is preconnected and has two points, it is `graphSet (A ∩ B)` (an
  isolated common vertex would be clopen). When the intersection is a single point there is at
  most one odd vertex of `Z ∩ A`, hence none, and no walk is needed.

## The plan for `janiszewski` (batches 127–129)

The field asks: `A`, `B` compact, `A ∩ B` connected or empty, neither separates `x` from `y` ⇒
`A ∪ B` does not. It will be **weakened to polygonal compacta** (finite unions of closed segments;
batch 129) and proved by mod-2 cycles:

* (i) **this batch**: straight-line graphs in proper position, subdivision, mod-2 cycles, their
  east-ray parity, local constancy, additivity, the flip across an edge, "different parity ⇒
  separated", Mayer–Vietoris, and the conditional `janiszewskiPoly_of_oddCycle`;
* (ii) **batch 128**: `SeparatingGraphHasOddCycle`;
* (iii) **batch 129**: assembly, the polygonal field, the two uses.
-/

namespace HPC.Plane

open Set Filter Topology

/-! ### Straight-line graphs -/

/-- A segment: an ordered pair of points, meant distinct. -/
abbrev Seg := Pt × Pt

/-- The point set of a segment. -/
def segSet (s : Seg) : Set Pt := segment ℝ s.1 s.2

/-- The point set of a finite set of segments. -/
def graphSet (G : Finset Seg) : Set Pt := ⋃ s ∈ G, segSet s

/-- The end points of the segments of `G`. -/
noncomputable def vertices (G : Finset Seg) : Finset Pt := G.image Prod.fst ∪ G.image Prod.snd

/-- **Proper position**: every segment nondegenerate, two distinct segments have distinct point
sets and meet at most in a common end point. -/
def IsProper (G : Finset Seg) : Prop :=
  (∀ s ∈ G, s.1 ≠ s.2) ∧
  (∀ s ∈ G, ∀ t ∈ G, s ≠ t → segSet s ≠ segSet t) ∧
  ∀ s ∈ G, ∀ t ∈ G, segSet s ≠ segSet t →
    segSet s ∩ segSet t ⊆ ({s.1, s.2} : Set Pt) ∩ ({t.1, t.2} : Set Pt)

/-- The degree of a point in `G`: the number of segments having it as an end point. -/
noncomputable def deg (G : Finset Seg) (w : Pt) : ℕ :=
  (G.filter fun s => w = s.1 ∨ w = s.2).card

/-- A **mod-2 cycle**: a proper graph with every degree even. -/
def IsCycle (G : Finset Seg) : Prop := IsProper G ∧ ∀ w, Even (deg G w)

/-! #### Elementary geometry of segments -/

/-- Along a lexicographically increasing segment the lexicographic order is monotone. -/
theorem lex_le_of_mem_segment {a b z : Pt} (hab : toLex a ≤ toLex b) (hz : z ∈ segment ℝ a b) :
    toLex a ≤ toLex z ∧ toLex z ≤ toLex b := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  obtain rfl : s = 1 - t := by linarith
  simp only [Prod.Lex.le_iff, ofLex_toLex, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hab ⊢
  rcases hab with h | ⟨h1, h2⟩
  · constructor
    · rcases ht.eq_or_lt with rfl | ht'
      · right; constructor <;> norm_num
      · left; nlinarith
    · rcases hs.eq_or_lt with h0 | hs'
      · right; obtain rfl : t = 1 := by linarith
        constructor <;> norm_num
      · left; nlinarith
  · constructor
    · right; constructor
      · rw [← h1]; ring
      · nlinarith
    · right; constructor
      · rw [← h1]; ring
      · nlinarith

/-- A lexicographically oriented segment is determined by its point set. -/
theorem eq_of_segment_eq_lex {a b c d : Pt} (h1 : toLex a < toLex b) (h2 : toLex c < toLex d)
    (h : segment ℝ a b = segment ℝ c d) : a = c ∧ b = d := by
  have ha := lex_le_of_mem_segment h2.le (h ▸ left_mem_segment ℝ a b)
  have hb := lex_le_of_mem_segment h2.le (h ▸ right_mem_segment ℝ a b)
  have hc := lex_le_of_mem_segment h1.le (h.symm ▸ left_mem_segment ℝ c d)
  have hd := lex_le_of_mem_segment h1.le (h.symm ▸ right_mem_segment ℝ c d)
  exact ⟨toLex.injective (le_antisymm hc.1 ha.1), toLex.injective (le_antisymm hb.2 hd.2)⟩

/-- Three points of a segment, two of them distinct: the third is on their line. -/
theorem exists_lineMap_of_mem_segment {p q a b c : Pt} (ha : a ∈ segment ℝ p q)
    (hb : b ∈ segment ℝ p q) (hc : c ∈ segment ℝ p q) (hab : a ≠ b) :
    ∃ r : ℝ, c = AffineMap.lineMap a b r := by
  rw [segment_eq_image_lineMap] at ha hb hc
  obtain ⟨α, -, rfl⟩ := ha
  obtain ⟨β, -, rfl⟩ := hb
  obtain ⟨γ, -, rfl⟩ := hc
  have hne : β - α ≠ 0 := fun h => hab (by rw [show β = α by linarith])
  refine ⟨(γ - α) / (β - α), ?_⟩
  simp only [AffineMap.lineMap_apply_module']
  ext <;> simp <;> field_simp <;> ring

theorem real_pair_eq_aux {a b a' b' : ℝ} (ha : a < 0) (hb : 0 < b) (ha' : a' < 0) (hb' : 0 < b')
    (h1 : a' ∈ uIcc a b → a' = a ∨ a' = b) (h2 : b' ∈ uIcc a b → b' = a ∨ b' = b)
    (h3 : a ∈ uIcc a' b' → a = a' ∨ a = b') (h4 : b ∈ uIcc a' b' → b = a' ∨ b = b') :
    a = a' ∧ b = b' := by
  have hab : a ≤ b := by linarith
  have hab' : a' ≤ b' := by linarith
  simp only [uIcc_of_le hab, uIcc_of_le hab', mem_Icc] at h1 h2 h3 h4
  constructor
  · rcases lt_trichotomy a a' with h | h | h
    · rcases h1 ⟨h.le, by linarith⟩ with h' | h' <;> linarith
    · exact h
    · rcases h3 ⟨h.le, by linarith⟩ with h' | h' <;> linarith
  · rcases lt_trichotomy b b' with h | h | h
    · rcases h4 ⟨by linarith, h.le⟩ with h' | h' <;> linarith
    · exact h
    · rcases h2 ⟨by linarith, h.le⟩ with h' | h' <;> linarith

/-- Two parameter intervals on a line, both containing `0` in their interior, neither containing
an end point of the other in its interior, coincide. -/
theorem real_pair_eq {a b a' b' : ℝ} (h0 : (0:ℝ) ∈ uIcc a b) (h0' : (0:ℝ) ∈ uIcc a' b')
    (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (h1 : a' ∈ uIcc a b → a' = a ∨ a' = b) (h2 : b' ∈ uIcc a b → b' = a ∨ b' = b)
    (h3 : a ∈ uIcc a' b' → a = a' ∨ a = b') (h4 : b ∈ uIcc a' b' → b = a' ∨ b = b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  rw [mem_uIcc] at h0 h0'
  rcases h0 with ⟨h0a, h0b⟩ | ⟨h0a, h0b⟩ <;> rcases h0' with ⟨h0a', h0b'⟩ | ⟨h0a', h0b'⟩
  · exact Or.inl (real_pair_eq_aux (lt_of_le_of_ne h0a ha) (lt_of_le_of_ne h0b hb.symm)
      (lt_of_le_of_ne h0a' ha') (lt_of_le_of_ne h0b' hb'.symm) h1 h2 h3 h4)
  · rw [uIcc_comm a' b'] at h3 h4
    have := real_pair_eq_aux (lt_of_le_of_ne h0a ha) (lt_of_le_of_ne h0b hb.symm)
      (lt_of_le_of_ne h0a' hb') (lt_of_le_of_ne h0b' ha'.symm) h2 h1
      (fun h => (h3 h).symm) (fun h => (h4 h).symm)
    exact Or.inr this
  · rw [uIcc_comm a b] at h1 h2
    have := real_pair_eq_aux (lt_of_le_of_ne h0a hb) (lt_of_le_of_ne h0b ha.symm)
      (lt_of_le_of_ne h0a' ha') (lt_of_le_of_ne h0b' hb'.symm)
      (fun h => (h1 h).symm) (fun h => (h2 h).symm) h4 h3
    exact Or.inr ⟨this.2, this.1⟩
  · rw [uIcc_comm a b] at h1 h2
    rw [uIcc_comm a' b'] at h3 h4
    have := real_pair_eq_aux (lt_of_le_of_ne h0a hb) (lt_of_le_of_ne h0b ha.symm)
      (lt_of_le_of_ne h0a' hb') (lt_of_le_of_ne h0b' ha'.symm)
      (fun h => (h2 h).symm) (fun h => (h1 h).symm) (fun h => (h4 h).symm) (fun h => (h3 h).symm)
    exact Or.inl ⟨this.2, this.1⟩

/-! #### Graphs: basic facts; degrees mod 2 -/

theorem mem_vertices {G : Finset Seg} {w : Pt} : w ∈ vertices G ↔ ∃ s ∈ G, w = s.1 ∨ w = s.2 := by
  simp only [vertices, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inr rfl⟩
  · rintro ⟨s, hs, rfl | rfl⟩
    · exact Or.inl ⟨s, hs, rfl⟩
    · exact Or.inr ⟨s, hs, rfl⟩

/-- A subset of a proper graph is proper. -/
theorem IsProper.subset {G H : Finset Seg} (hG : IsProper G) (hHG : H ⊆ G) : IsProper H :=
  ⟨fun s hs => hG.1 s (hHG hs), fun s hs t ht => hG.2.1 s (hHG hs) t (hHG ht),
    fun s hs t ht => hG.2.2 s (hHG hs) t (hHG ht)⟩

/-- `graphSet` is closed (a finite union of segments). -/
theorem isClosed_graphSet (G : Finset Seg) : IsClosed (graphSet G) :=
  isClosed_biUnion_finset fun s _ => (isCompact_segment' s.1 s.2).isClosed

theorem mem_graphSet {G : Finset Seg} {z : Pt} : z ∈ graphSet G ↔ ∃ s ∈ G, z ∈ segSet s := by
  simp [graphSet]

theorem graphSet_mono {G H : Finset Seg} (h : G ⊆ H) : graphSet G ⊆ graphSet H := fun z hz => by
  obtain ⟨s, hs, hzs⟩ := mem_graphSet.1 hz
  exact mem_graphSet.2 ⟨s, h hs, hzs⟩

theorem end_mem_graphSet {G : Finset Seg} {s : Seg} (hs : s ∈ G) {w : Pt} (hw : w = s.1 ∨ w = s.2) :
    w ∈ graphSet G :=
  mem_graphSet.2 ⟨s, hs, by rcases hw with rfl | rfl
                            · exact left_mem_segment _ _ _
                            · exact right_mem_segment _ _ _⟩

/-! #### Sums mod 2 over symmetric differences; degrees mod 2 -/

theorem sum_symmDiff_zmod2 {α : Type*} [DecidableEq α] (G H : Finset α) (f : α → ZMod 2) :
    ∑ x ∈ symmDiff G H, f x = ∑ x ∈ G, f x + ∑ x ∈ H, f x := by
  have hG : ∑ x ∈ G, f x = ∑ x ∈ G \ H, f x + ∑ x ∈ G ∩ H, f x := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter G H), Finset.sdiff_union_inter]
  have hH : ∑ x ∈ H, f x = ∑ x ∈ H \ G, f x + ∑ x ∈ G ∩ H, f x := by
    rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter H G),
      Finset.sdiff_union_inter]
  rw [symmDiff_def, Finset.sup_eq_union, Finset.sum_union disjoint_sdiff_sdiff, hG, hH]
  rw [add_add_add_comm, zmod2_add_self, add_zero]

theorem symmDiff_subset_of {α : Type*} [DecidableEq α] {G H E : Finset α} (hG : G ⊆ E)
    (hH : H ⊆ E) : symmDiff G H ⊆ E := by
  rw [symmDiff_def, Finset.sup_eq_union]
  exact Finset.union_subset (Finset.sdiff_subset.trans hG) (Finset.sdiff_subset.trans hH)

theorem deg_cast (G : Finset Seg) (w : Pt) :
    (deg G w : ZMod 2) = ∑ s ∈ G, if w = s.1 ∨ w = s.2 then 1 else 0 := by
  unfold deg; rw [Finset.natCast_card_filter]

theorem deg_symmDiff (G H : Finset Seg) (w : Pt) :
    (deg (symmDiff G H) w : ZMod 2) = deg G w + deg H w := by
  simp only [deg_cast]; exact sum_symmDiff_zmod2 _ _ _

theorem deg_singleton {e : Seg} (he : e.1 ≠ e.2) (w : Pt) :
    (deg {e} w : ZMod 2) = (if w = e.1 then 1 else 0) + (if w = e.2 then 1 else 0) := by
  rw [deg_cast, Finset.sum_singleton]
  by_cases h1 : w = e.1 <;> by_cases h2 : w = e.2
  · exact absurd (h1.symm.trans h2) he
  all_goals simp [h1, h2, he, Ne.symm he]

theorem deg_empty (w : Pt) : deg ∅ w = 0 := by simp [deg]

theorem exists_of_deg_ne_zero {G : Finset Seg} {w : Pt} (h : (deg G w : ZMod 2) ≠ 0) :
    ∃ s ∈ G, w = s.1 ∨ w = s.2 := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [deg_cast]
  exact Finset.sum_eq_zero fun s hs => by simp [hcon s hs]

theorem even_iff_deg_cast {G : Finset Seg} {w : Pt} : Even (deg G w) ↔ (deg G w : ZMod 2) = 0 :=
  ZMod.natCast_eq_zero_iff_even.symm

/-- The degrees of a graph without degenerate segments sum to `0` mod 2 over its vertices. -/
theorem sum_deg_vertices {G : Finset Seg} (hnd : ∀ s ∈ G, s.1 ≠ s.2) :
    ∑ w ∈ vertices G, (deg G w : ZMod 2) = 0 := by
  simp only [deg_cast]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun s hs => ?_
  have h12 := hnd s hs
  have : ∀ w : Pt, (if w = s.1 ∨ w = s.2 then (1 : ZMod 2) else 0) =
      (if w = s.1 then 1 else 0) + (if w = s.2 then 1 else 0) := fun w => by
    by_cases h1 : w = s.1 <;> by_cases h2 : w = s.2
    · exact absurd (h1.symm.trans h2) h12
    all_goals simp [h1, h2, h12, Ne.symm h12]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_vertices.2 ⟨s, hs, Or.inl rfl⟩,
    mem_vertices.2 ⟨s, hs, Or.inr rfl⟩, if_true]
  decide

theorem zmod2_eq_zero_or_one : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

/-- The set of odd vertices has even cardinality. -/
theorem card_odd_vertices {G : Finset Seg} (hnd : ∀ s ∈ G, s.1 ≠ s.2) :
    (((vertices G).filter fun w => (deg G w : ZMod 2) = 1).card : ZMod 2) = 0 := by
  rw [← sum_deg_vertices hnd, ← Finset.sum_filter_add_sum_filter_not (vertices G)
    (fun w => (deg G w : ZMod 2) = 1)]
  rw [Finset.sum_congr rfl (fun w hw => (Finset.mem_filter.1 hw).2),
    Finset.sum_eq_zero (s := (vertices G).filter fun w => ¬ (deg G w : ZMod 2) = 1)
      (fun w hw => ((zmod2_eq_zero_or_one _).resolve_right (Finset.mem_filter.1 hw).2))]
  simp


/-! #### Subdivision -/

open Classical in
/-- The **cut set** of a finite family of segments: all end points, and every point which is the
whole intersection of two segments of the family. -/
def cutSet (S : Finset Seg) : Set Pt :=
  (⋃ s ∈ S, ({s.1, s.2} : Set Pt)) ∪ {q | ∃ s ∈ S, ∃ u ∈ S, segSet s ∩ segSet u = {q}}

theorem cutSet_finite (S : Finset Seg) : (cutSet S).Finite := by
  refine Set.Finite.union (Set.Finite.biUnion S.finite_toSet fun _ _ => Set.toFinite _) ?_
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun s _ =>
    Set.Finite.biUnion S.finite_toSet fun u _ =>
      (show ({q | segSet s ∩ segSet u = {q}} : Set Pt).Subsingleton from
        fun q hq q' hq' => Set.singleton_eq_singleton_iff.1 (hq.symm.trans hq')).finite) ?_
  rintro q ⟨s, hs, u, hu, h⟩
  exact Set.mem_biUnion hs (Set.mem_biUnion hu h)

theorem mem_cutSet_of_end {S : Finset Seg} {s : Seg} (hs : s ∈ S) : s.1 ∈ cutSet S ∧ s.2 ∈ cutSet S :=
  ⟨Or.inl (Set.mem_biUnion hs (by simp)), Or.inl (Set.mem_biUnion hs (by simp))⟩

open Classical in
/-- **The canonical subdivision**: the pairs `(u, v)` of cut points, ordered lexicographically,
spanning a segment inside a segment of `S` which contains no other cut point. -/
noncomputable def subdiv (S : Finset Seg) : Finset Seg :=
  ((cutSet_finite S).toFinset ×ˢ (cutSet_finite S).toFinset).filter fun t =>
    toLex t.1 < toLex t.2 ∧ (∃ s ∈ S, segSet t ⊆ segSet s) ∧
      ∀ z ∈ segSet t, z ∈ cutSet S → z = t.1 ∨ z = t.2

theorem mem_subdiv {S : Finset Seg} {t : Seg} :
    t ∈ subdiv S ↔ (t.1 ∈ cutSet S ∧ t.2 ∈ cutSet S) ∧ toLex t.1 < toLex t.2 ∧
      (∃ s ∈ S, segSet t ⊆ segSet s) ∧ ∀ z ∈ segSet t, z ∈ cutSet S → z = t.1 ∨ z = t.2 := by
  unfold subdiv
  simp [Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset]

/-- Two pieces of the subdivision meet at most in common end points (or coincide). -/
theorem subdiv_inter {S : Finset Seg} {P Q : Seg} (hP : P ∈ subdiv S) (hQ : Q ∈ subdiv S)
    (hPQ : segSet P ≠ segSet Q) : segSet P ∩ segSet Q ⊆ ({P.1, P.2} : Set Pt) ∩ {Q.1, Q.2} := by
  rintro z ⟨hzP, hzQ⟩
  rw [mem_subdiv] at hP hQ
  obtain ⟨⟨hu, hv⟩, hlt, ⟨s, hs, hPs⟩, hfP⟩ := hP
  obtain ⟨⟨hu', hv'⟩, hlt', ⟨s', hs', hQs'⟩, hfQ⟩ := hQ
  by_cases hz : z ∈ cutSet S
  · exact ⟨hfP z hzP hz, hfQ z hzQ hz⟩
  exfalso
  have hzs : z ∈ segSet s ∩ segSet s' := ⟨hPs hzP, hQs' hzQ⟩
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ segSet s ∩ segSet s', w ≠ z := by
    by_contra hcon
    push_neg at hcon
    exact hz (Or.inr ⟨s, hs, s', hs', Set.eq_singleton_iff_unique_mem.2 ⟨hzs, hcon⟩⟩)
  have hzw : z ≠ w := hwz.symm
  set F := AffineMap.lineMap (k := ℝ) z w with hF
  have hFinj : Function.Injective F := AffineMap.lineMap_injective ℝ hzw
  have hF0 : F 0 = z := AffineMap.lineMap_apply_zero _ _
  have hPu : P.1 ∈ segSet s := hPs (left_mem_segment _ _ _)
  have hPv : P.2 ∈ segSet s := hPs (right_mem_segment _ _ _)
  have hQu : Q.1 ∈ segSet s' := hQs' (left_mem_segment _ _ _)
  have hQv : Q.2 ∈ segSet s' := hQs' (right_mem_segment _ _ _)
  obtain ⟨α, hα⟩ := exists_lineMap_of_mem_segment hzs.1 hw.1 hPu hzw
  obtain ⟨β, hβ⟩ := exists_lineMap_of_mem_segment hzs.1 hw.1 hPv hzw
  obtain ⟨α', hα'⟩ := exists_lineMap_of_mem_segment hzs.2 hw.2 hQu hzw
  obtain ⟨β', hβ'⟩ := exists_lineMap_of_mem_segment hzs.2 hw.2 hQv hzw
  -- segments of the line in terms of parameters
  have hseg : ∀ a b : ℝ, segment ℝ (F a) (F b) = F '' uIcc a b := fun a b => by
    rw [← image_segment, segment_eq_uIcc]
  have hmem : ∀ a b r : ℝ, F r ∈ segment ℝ (F a) (F b) ↔ r ∈ uIcc a b := fun a b r => by
    rw [hseg]; exact hFinj.mem_set_image
  have hSP : segSet P = segment ℝ (F α) (F β) := by
    unfold segSet; rw [← hα, ← hβ]
  have hSQ : segSet Q = segment ℝ (F α') (F β') := by
    unfold segSet; rw [← hα', ← hβ']
  have hne : ∀ r : ℝ, F r ∈ cutSet S → r ≠ 0 := fun r hr h0 => by
    rw [h0, hF0] at hr; exact hz hr
  have h0P : (0 : ℝ) ∈ uIcc α β := by rw [← hmem, hF0, ← hSP]; exact hzP
  have h0Q : (0 : ℝ) ∈ uIcc α' β' := by rw [← hmem, hF0, ← hSQ]; exact hzQ
  have hfP' : ∀ r, r ∈ uIcc α β → F r ∈ cutSet S → r = α ∨ r = β := fun r hr hc => by
    rcases hfP (F r) (by rw [hSP, hmem]; exact hr) hc with h | h
    · left; apply hFinj; rw [h, hα]
    · right; apply hFinj; rw [h, hβ]
  have hfQ' : ∀ r, r ∈ uIcc α' β' → F r ∈ cutSet S → r = α' ∨ r = β' := fun r hr hc => by
    rcases hfQ (F r) (by rw [hSQ, hmem]; exact hr) hc with h | h
    · left; apply hFinj; rw [h, hα']
    · right; apply hFinj; rw [h, hβ']
  rw [hα] at hu; rw [hβ] at hv; rw [hα'] at hu'; rw [hβ'] at hv'
  rcases real_pair_eq h0P h0Q (hne _ hu) (hne _ hv) (hne _ hu') (hne _ hv')
      (fun h => hfP' _ h hu') (fun h => hfP' _ h hv') (fun h => hfQ' _ h hu)
      (fun h => hfQ' _ h hv) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hPQ (by rw [hSP, hSQ, h1, h2])
  · exact hPQ (by rw [hSP, hSQ, h1, h2, segment_symm])

/-- In a finite set of reals containing `0` and `1`, every `ρ ∈ [0, 1]` lies in a gap
`[a, b]` (`a < b` consecutive elements). -/
theorem exists_gap {T : Set ℝ} (hT : T.Finite) (h0 : (0 : ℝ) ∈ T) (h1 : (1 : ℝ) ∈ T) {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    ∃ a ∈ T, ∃ b ∈ T, a < b ∧ a ≤ ρ ∧ ρ ≤ b ∧ ∀ r ∈ T, r ≤ a ∨ b ≤ r := by
  rcases hρ.2.lt_or_eq with hρ1 | hρ1
  · obtain ⟨a, ⟨haT, haρ⟩, ha⟩ := Set.exists_max_image {r ∈ T | r ≤ ρ} id
      (hT.subset fun _ h => h.1) ⟨0, h0, hρ.1⟩
    obtain ⟨b, ⟨hbT, hbρ⟩, hb⟩ := Set.exists_min_image {r ∈ T | ρ < r} id
      (hT.subset fun _ h => h.1) ⟨1, h1, hρ1⟩
    refine ⟨a, haT, b, hbT, by simp only [mem_setOf_eq] at *; linarith, haρ, hbρ.le, fun r hr => ?_⟩
    rcases le_or_gt r ρ with h | h
    · exact Or.inl (ha r ⟨hr, h⟩)
    · exact Or.inr (hb r ⟨hr, h⟩)
  · subst hρ1
    obtain ⟨a, ⟨haT, ha1⟩, ha⟩ := Set.exists_max_image {r ∈ T | r < 1} id
      (hT.subset fun _ h => h.1) ⟨0, h0, one_pos⟩
    refine ⟨a, haT, 1, h1, ha1, ha1.le, le_rfl, fun r hr => ?_⟩
    rcases lt_or_ge r 1 with h | h
    · exact Or.inl (ha r ⟨hr, h⟩)
    · exact Or.inr h

/-- Every point of a segment of `S` lies in a piece of the subdivision inside that segment. -/
theorem exists_piece {S : Finset Seg} {s : Seg} (hs : s ∈ S) (hs12 : s.1 ≠ s.2) {p : Pt}
    (hp : p ∈ segSet s) : ∃ t ∈ subdiv S, p ∈ segSet t ∧ segSet t ⊆ segSet s := by
  set L := AffineMap.lineMap (k := ℝ) s.1 s.2 with hL
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ hs12
  have hseg : ∀ a b : ℝ, segment ℝ (L a) (L b) = L '' uIcc a b := fun a b => by
    rw [← image_segment, segment_eq_uIcc]
  have hss : segSet s = L '' Icc 0 1 := segment_eq_image_lineMap ℝ _ _
  set T := {r ∈ Icc (0 : ℝ) 1 | L r ∈ cutSet S} with hT
  have hTfin : T.Finite := ((cutSet_finite S).preimage hLinj.injOn).subset fun r hr => hr.2
  have h0 : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, by
    rw [hL, AffineMap.lineMap_apply_zero]; exact (mem_cutSet_of_end hs).1⟩
  have h1 : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by
    rw [hL, AffineMap.lineMap_apply_one]; exact (mem_cutSet_of_end hs).2⟩
  rw [hss] at hp
  obtain ⟨ρ, hρ, rfl⟩ := hp
  obtain ⟨a, haT, b, hbT, hab, haρ, hρb, hgap⟩ := exists_gap hTfin h0 h1 hρ
  have hLab : L a ≠ L b := fun h => hab.ne (hLinj h)
  have huv : segment ℝ (L a) (L b) = L '' Icc a b := by rw [hseg, uIcc_of_le hab.le]
  -- the oriented piece
  obtain ⟨t, ht12, htseg⟩ : ∃ t : Seg, toLex t.1 < toLex t.2 ∧
      ((t.1 = L a ∧ t.2 = L b) ∨ (t.1 = L b ∧ t.2 = L a)) := by
    rcases lt_or_gt_of_ne (show toLex (L a) ≠ toLex (L b) from fun h => hLab (toLex.injective h))
      with h | h
    · exact ⟨(L a, L b), h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(L b, L a), h, Or.inr ⟨rfl, rfl⟩⟩
  have hts : segSet t = L '' Icc a b := by
    unfold segSet
    rcases htseg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, huv]
    · rw [h1, h2, segment_symm, huv]
  have hsub : segSet t ⊆ segSet s := by
    rw [hts, hss]
    exact Set.image_mono fun r hr => ⟨haT.1.1.trans hr.1, hr.2.trans hbT.1.2⟩
  refine ⟨t, ?_, by rw [hts]; exact ⟨ρ, ⟨haρ, hρb⟩, rfl⟩, hsub⟩
  rw [mem_subdiv]
  refine ⟨?_, ht12, ⟨s, hs, hsub⟩, ?_⟩
  · rcases htseg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨haT.2, hbT.2⟩
    · rw [h1, h2]; exact ⟨hbT.2, haT.2⟩
  · intro z hz hzc
    rw [hts] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    have hrT : r ∈ T := ⟨⟨haT.1.1.trans hr.1, hr.2.trans hbT.1.2⟩, hzc⟩
    have hr' : r = a ∨ r = b := by
      rcases hgap r hrT with h | h
      · exact Or.inl (le_antisymm h hr.1)
      · exact Or.inr (le_antisymm hr.2 h)
    rcases htseg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hr' with rfl | rfl <;> simp [h1, h2]

open Classical in
/-- **Subdivision.** Every finite set of nondegenerate segments has a proper refinement with the
same point set, every piece lying in a segment of the original, and every original segment a union
of pieces. -/
theorem exists_proper_subdivision (S : Finset Seg) (hS : ∀ s ∈ S, s.1 ≠ s.2) :
    ∃ G : Finset Seg, IsProper G ∧ graphSet G = graphSet S ∧
      (∀ t ∈ G, ∃ s ∈ S, segSet t ⊆ segSet s) ∧
      (∀ s ∈ S, segSet s = ⋃ t ∈ G.filter (fun t => segSet t ⊆ segSet s), segSet t) := by
  refine ⟨subdiv S, ⟨fun t ht => ?_, fun t ht t' ht' hne h => ?_, fun t ht t' ht' h =>
    subdiv_inter ht ht' h⟩, ?_, fun t ht => (mem_subdiv.1 ht).2.2.1, fun s hs => ?_⟩
  · exact fun h => (mem_subdiv.1 ht).2.1.ne (congrArg toLex h)
  · have := eq_of_segment_eq_lex (mem_subdiv.1 ht).2.1 (mem_subdiv.1 ht').2.1 h
    exact hne (Prod.ext this.1 this.2)
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 hz
      obtain ⟨s, hs, hts⟩ := (mem_subdiv.1 ht).2.2.1
      exact Set.mem_biUnion hs (hts hzt)
    · intro z hz
      obtain ⟨s, hs, hzs⟩ := Set.mem_iUnion₂.1 hz
      obtain ⟨t, ht, hzt, -⟩ := exists_piece hs (hS s hs) hzs
      exact Set.mem_biUnion ht hzt
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨t, ht, hzt, hts⟩ := exists_piece hs (hS s hs) hz
      exact Set.mem_biUnion (Finset.mem_filter.2 ⟨ht, hts⟩) hzt
    · intro z hz
      obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 hz
      exact (Finset.mem_filter.1 ht).2 hzt

/-! ### Parity of a cycle -/

/-- The east-ray crossing parity of a finite set of segments (`ceInd` from `Jct1`). -/
noncomputable def cycParity (G : Finset Seg) (x : Pt) : ZMod 2 := ∑ s ∈ G, ceInd x s.1 s.2

/-- Additivity: parity of a symmetric difference is the sum of the parities (edges in both cancel
mod 2). No properness needed. -/
theorem cycParity_symmDiff (G H : Finset Seg) (x : Pt) :
    cycParity (symmDiff G H) x = cycParity G x + cycParity H x :=
  sum_symmDiff_zmod2 G H _

/- The skeleton's statement, without nondegeneracy, is false (`not_sum_vJump_even_skeleton`):
`theorem sum_vJump_even (G : Finset Seg) (heven : ∀ w, Even (deg G w)) (x : Pt) :
    ∑ s ∈ G, (vJump x s.1 + vJump x s.2) = 0` -/

/-- **The skeleton's `sum_vJump_even` is false as stated** (it has no nondegeneracy hypothesis):
for `G = {(a, a), (a, b), (b, b)}` with `a = (1, 0)`, `b = (2, 1)` every degree is even (`deg a =
deg b = 2`: a degenerate segment is counted once in `deg` but its jump twice in the sum), and at
`x = (0, 0)` the sum is `1`. -/
theorem not_sum_vJump_even_skeleton :
    ¬ ∀ (G : Finset Seg), (∀ w, Even (deg G w)) → ∀ x : Pt,
      ∑ s ∈ G, (vJump x s.1 + vJump x s.2) = 0 := by
  intro h
  have hab : ((1, 0) : Pt) ≠ (2, 1) := fun h => by simp [Prod.ext_iff] at h
  have h1 : ((((1, 0) : Pt), ((1, 0) : Pt)) : Seg) ≠ ((1, 0), (2, 1)) :=
    fun h' => hab (congrArg Prod.snd h')
  have h2 : ((((1, 0) : Pt), ((1, 0) : Pt)) : Seg) ≠ ((2, 1), (2, 1)) :=
    fun h' => hab (congrArg Prod.fst h')
  have h3 : ((((1, 0) : Pt), ((2, 1) : Pt)) : Seg) ≠ ((2, 1), (2, 1)) :=
    fun h' => hab (congrArg Prod.fst h')
  have hdeg : ∀ w, Even (deg {((1, 0), (1, 0)), ((1, 0), (2, 1)), ((2, 1), (2, 1))} w) := by
    intro w
    by_cases hwa : w = (1, 0)
    · rw [hwa]
      have : deg {((1, 0), (1, 0)), ((1, 0), (2, 1)), ((2, 1), (2, 1))} (1, 0) = 2 := by
        simp [deg, Finset.filter_insert, Finset.filter_singleton]
      rw [this]; exact even_two
    by_cases hwb : w = (2, 1)
    · rw [hwb]
      have : deg {((1, 0), (1, 0)), ((1, 0), (2, 1)), ((2, 1), (2, 1))} (2, 1) = 2 := by
        simp [deg, Finset.filter_insert, Finset.filter_singleton]
      rw [this]; exact even_two
    have : deg {((1, 0), (1, 0)), ((1, 0), (2, 1)), ((2, 1), (2, 1))} w = 0 := by
      simp [deg, Finset.filter_insert, Finset.filter_singleton, hwa, hwb]
    rw [this]; exact Even.zero
  have := h _ hdeg (0, 0)
  rw [Finset.sum_insert (by simp [h1, h2]), Finset.sum_insert (by simp [h3])] at this
  simp [vJump] at this
  revert this; decide

/-- **The telescoping of vertex jumps over an even-degree graph** (the generalisation of
`sum_vJump_telescope`): `∑ s ∈ G, (vJump x s.1 + vJump x s.2) = 0` when every segment is
nondegenerate and every degree is even. (The nondegeneracy hypothesis `hnd` is added to the
skeleton's statement, which is false without it: `not_sum_vJump_even_skeleton`.) -/
theorem sum_vJump_even (G : Finset Seg) (hnd : ∀ s ∈ G, s.1 ≠ s.2) (heven : ∀ w, Even (deg G w))
    (x : Pt) : ∑ s ∈ G, (vJump x s.1 + vJump x s.2) = 0 := by
  have hs : ∀ s ∈ G, vJump x s.1 + vJump x s.2 =
      ∑ w ∈ vertices G, if w = s.1 ∨ w = s.2 then vJump x w else 0 := by
    intro s hs
    have h12 := hnd s hs
    have : ∀ w : Pt, (if w = s.1 ∨ w = s.2 then vJump x w else 0) =
        (if w = s.1 then vJump x w else 0) + (if w = s.2 then vJump x w else 0) := fun w => by
      by_cases h1 : w = s.1 <;> by_cases h2 : w = s.2
      · exact absurd (h1.symm.trans h2) h12
      all_goals simp [h1, h2, h12, Ne.symm h12]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq',
      mem_vertices.2 ⟨s, hs, Or.inl rfl⟩, mem_vertices.2 ⟨s, hs, Or.inr rfl⟩, if_true]
  rw [Finset.sum_congr rfl hs, Finset.sum_comm]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  change (deg G w : ZMod 2) * _ = 0
  rw [even_iff_deg_cast.1 (heven w), zero_mul]

theorem not_mem_segSet_of_not_mem_graphSet {G : Finset Seg} {x : Pt} (hx : x ∉ graphSet G)
    {s : Seg} (hs : s ∈ G) : x ∉ segment ℝ s.1 s.2 := fun h => hx (mem_graphSet.2 ⟨s, hs, h⟩)

/-- Local constancy, eventually form. -/
theorem cycParity_eventually_eq {G : Finset Seg} (hnd : ∀ s ∈ G, s.1 ≠ s.2)
    (hG : ∀ w, Even (deg G w)) {x : Pt} (hx : x ∉ graphSet G) :
    ∀ᶠ y in 𝓝 x, cycParity G y = cycParity G x := by
  have hall := (Filter.eventually_all_finset G).2 fun s hs =>
    crossesEast_jump (not_mem_segSet_of_not_mem_graphSet hx hs)
  filter_upwards [hall] with y hy
  unfold cycParity
  rcases le_or_gt x.2 y.2 with h | h
  · exact Finset.sum_congr rfl fun s hs => ceInd_congr ((hy s hs).1 h)
  · apply zmod2_eq_of_add_eq_zero
    rw [← Finset.sum_add_distrib, ← sum_vJump_even G hnd hG x]
    exact Finset.sum_congr rfl fun s hs => (hy s hs).2 h

/-- **Local constancy of the parity of a cycle** off its point set (`crossesEast_jump` per edge,
`sum_vJump_even` for the jumps). (Hypothesis `hnd` added; see `sum_vJump_even`.) -/
theorem cycParity_locallyConstant {G : Finset Seg} (hnd : ∀ s ∈ G, s.1 ≠ s.2)
    (hG : ∀ w, Even (deg G w)) {x : Pt} (hx : x ∉ graphSet G) :
    ∃ ε > 0, ∀ y, dist y x < ε → cycParity G y = cycParity G x := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (cycParity_eventually_eq hnd hG hx)
  exact ⟨ε, hε, fun y hy => h hy⟩

/-- Parity of a cycle is constant on preconnected subsets of the complement. (Hypothesis `hnd`
added; see `sum_vJump_even`.) -/
theorem cycParity_eq_of_isPreconnected {G : Finset Seg} (hnd : ∀ s ∈ G, s.1 ≠ s.2)
    (hG : ∀ w, Even (deg G w)) {S : Set Pt}
    (hS : IsPreconnected S) (hSG : S ⊆ (graphSet G)ᶜ) {x y : Pt} (hx : x ∈ S) (hy : y ∈ S) :
    cycParity G x = cycParity G y := by
  have hc : ContinuousOn (fun z => (cycParity G z).val) S := fun z hz =>
    (continuousAt_const.congr (by
      filter_upwards [cycParity_eventually_eq hnd hG (hSG hz)] with w hw
      rw [hw])).continuousWithinAt
  have := hS.constant_of_mapsTo (T := (Set.univ : Set ℕ)) IsDiscrete.univ hc
    (Set.mapsTo_univ _ _) hx hy
  exact ZMod.val_injective _ this

theorem cycParity_far (G : Finset Seg) : ∃ R : ℝ, ∀ x : Pt, R < x.1 → cycParity G x = 0 := by
  refine ⟨∑ s ∈ G, (|s.1.1| + |s.2.1|), fun x hx => ?_⟩
  have hle : ∀ s ∈ G, |s.1.1| + |s.2.1| ≤ ∑ s ∈ G, (|s.1.1| + |s.2.1|) := fun s hs =>
    Finset.single_le_sum (f := fun s : Seg => |s.1.1| + |s.2.1|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hs
  unfold cycParity
  refine Finset.sum_eq_zero fun s hs => ?_
  have hno : ¬ CrossesEast x s.1 s.2 := by
    rintro ⟨hst, hlt⟩
    have hm := fst_le_max_of_mem_segment (mem_segment_of_straddle hst)
    have h1 := le_abs_self s.1.1
    have h2 := le_abs_self s.2.1
    have h3 := abs_nonneg s.1.1
    have h4 := abs_nonneg s.2.1
    have h5 := hle s hs
    have h6 : max s.1.1 s.2.1 ≤ ∑ s ∈ G, (|s.1.1| + |s.2.1|) := max_le (by linarith) (by linarith)
    simp only at hm
    linarith
  simp [ceInd, hno]

/-- **Different parity ⇒ separated**: if `cycParity G x ≠ cycParity G y` (with `G` of even degrees
and `x, y ∉ graphSet G`), then `graphSet G` separates `x` from `y`. (Hypothesis `hnd` added; see
`sum_vJump_even`.) -/
theorem separatesPts_of_cycParity_ne {G : Finset Seg} (hnd : ∀ s ∈ G, s.1 ≠ s.2)
    (hG : ∀ w, Even (deg G w)) {x y : Pt}
    (hx : x ∉ graphSet G) (hy : y ∉ graphSet G) (hne : cycParity G x ≠ cycParity G y) :
    SeparatesPts (graphSet G) x y :=
  ⟨hx, hy, fun hyc => hne (cycParity_eq_of_isPreconnected hnd hG isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) (mem_connectedComponentIn (show x ∈ (graphSet G)ᶜ from hx))
    hyc)⟩

/-- The flip across a non-horizontal edge at a point of generic height. -/
theorem cycParity_flip_horizontal_shift {G : Finset Seg} {s : Seg} (hs : s ∈ G) {p : Pt}
    (hp : p ∈ segSet s) (hother : ∀ t ∈ G, t ≠ s → p ∉ segSet t)
    (hne : s.1.2 ≠ s.2.2) (hcv : ∀ w ∈ vertices G, w.2 ≠ p.2) :
    ∀ ε > 0, ∃ z₁ z₂ : Pt, dist z₁ p < ε ∧ dist z₂ p < ε ∧ z₁ ∉ graphSet G ∧ z₂ ∉ graphSet G ∧
      cycParity G z₁ ≠ cycParity G z₂ := by
  classical
  intro ε hε
  set a := s.1 with ha
  set b := s.2 with hb
  have hca : a.2 ≠ p.2 := hcv a (mem_vertices.2 ⟨s, hs, Or.inl rfl⟩)
  have hcb : b.2 ≠ p.2 := hcv b (mem_vertices.2 ⟨s, hs, Or.inr rfl⟩)
  have hpX : p.1 = a.1 + (p.2 - a.2) * (b.1 - a.1) / (b.2 - a.2) := fst_eq_of_mem_segment hp hne
  have hstr' : (a.2 ≤ p.2 ∧ p.2 < b.2) ∨ (b.2 ≤ p.2 ∧ p.2 < a.2) := by
    obtain ⟨u, t, hu, ht, hut, hpe⟩ := hp
    obtain rfl : u = 1 - t := by linarith
    have h2 : p.2 - a.2 = t * (b.2 - a.2) := by rw [← hpe]; simp [ha, hb]; ring
    have h2' : b.2 - p.2 = (1 - t) * (b.2 - a.2) := by rw [← hpe]; simp [ha, hb]; ring
    rcases lt_or_gt_of_ne hne with h | h
    · have h3 : a.2 ≤ p.2 := by have := mul_nonneg ht (sub_pos.2 h).le; linarith
      have h4 : p.2 ≤ b.2 := by have := mul_nonneg hu (sub_pos.2 h).le; linarith
      exact Or.inl ⟨h3, lt_of_le_of_ne h4 hcb.symm⟩
    · have h3 : b.2 ≤ p.2 := by have := mul_nonneg ht (sub_pos.2 h).le; nlinarith
      have h4 : p.2 ≤ a.2 := by have := mul_nonneg hu (sub_pos.2 h).le; nlinarith
      exact Or.inr ⟨h3, lt_of_le_of_ne h4 hca.symm⟩
  have hE : ∀ᶠ y in 𝓝 p, ∀ t ∈ G, t ≠ s → y ∉ segSet t ∧ ceInd y t.1 t.2 = ceInd p t.1 t.2 := by
    refine (Filter.eventually_all_finset G).2 fun t ht => ?_
    by_cases hts : t = s
    · exact Filter.Eventually.of_forall fun _ h => absurd hts h
    · have h1 : ∀ᶠ y in 𝓝 p, y ∉ segSet t :=
        (isCompact_segment' _ _).isClosed.isOpen_compl.mem_nhds (hother t ht hts)
      have h2 := ceInd_eventually_eq (hother t ht hts)
        (Ne.symm (hcv t.1 (mem_vertices.2 ⟨t, ht, Or.inl rfl⟩)))
        (Ne.symm (hcv t.2 (mem_vertices.2 ⟨t, ht, Or.inr rfl⟩)))
      filter_upwards [h1, h2] with y hy1 hy2 _ using ⟨hy1, hy2⟩
  obtain ⟨ε₀, hε₀, hεE⟩ := Metric.eventually_nhds_iff.1 hE
  set δ := min ε ε₀ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε := by have := min_le_left ε ε₀; linarith
  have hδε₀ : δ < ε₀ := by have := min_le_right ε ε₀; linarith
  have hdist : ∀ r : ℝ, |r| = δ → dist ((p.1 + r, p.2) : Pt) p = δ := fun r hr => by
    rw [Prod.dist_eq]; simp [hr, hδ0.le]
  have hdm : dist ((p.1 + -δ, p.2) : Pt) p = δ := hdist _ (by rw [abs_neg, abs_of_pos hδ0])
  have hdp : dist ((p.1 + δ, p.2) : Pt) p = δ := hdist _ (abs_of_pos hδ0)
  have hm := hεE (hdm.trans_lt hδε₀)
  have hpl := hεE (hdp.trans_lt hδε₀)
  have hoffs : ∀ r : ℝ, r ≠ 0 → ((p.1 + r, p.2) : Pt) ∉ segSet s := fun r hr h => by
    have := fst_eq_of_mem_segment h hne
    simp only at this
    exact hr (by linarith)
  have hnot : ∀ r : ℝ, r ≠ 0 → (∀ t ∈ G, t ≠ s → ((p.1 + r, p.2) : Pt) ∉ segSet t) →
      ((p.1 + r, p.2) : Pt) ∉ graphSet G := fun r hr hj h => by
    obtain ⟨t, ht, ht'⟩ := mem_graphSet.1 h
    by_cases hts : t = s
    · subst hts; exact hoffs r hr ht'
    · exact hj t ht hts ht'
  have hcrossm : ceInd ((p.1 + -δ, p.2) : Pt) a b = 1 := by
    simp only [ceInd, CrossesEast]; rw [if_pos]
    exact ⟨hstr', by linarith⟩
  have hcrossp : ceInd ((p.1 + δ, p.2) : Pt) a b = 0 := by
    simp only [ceInd, CrossesEast]; rw [if_neg]
    rintro ⟨_, h⟩; linarith
  refine ⟨(p.1 + -δ, p.2), (p.1 + δ, p.2), hdm.trans_lt hδε, hdp.trans_lt hδε,
    hnot _ (neg_ne_zero.2 hδ0.ne') fun t ht hts => (hm t ht hts).1,
    hnot _ hδ0.ne' fun t ht hts => (hpl t ht hts).1, ?_⟩
  unfold cycParity
  rw [← Finset.add_sum_erase _ _ hs, ← Finset.add_sum_erase _ _ hs]
  have hrest : ∀ q : Pt, (∀ t ∈ G, t ≠ s → q ∉ segSet t ∧ ceInd q t.1 t.2 = ceInd p t.1 t.2) →
      ∑ t ∈ G.erase s, ceInd q t.1 t.2 = ∑ t ∈ G.erase s, ceInd p t.1 t.2 := fun q hq =>
    Finset.sum_congr rfl fun t ht =>
      (hq t (Finset.mem_of_mem_erase ht) (Finset.ne_of_mem_erase ht)).2
  rw [hrest _ hm, hrest _ hpl]
  change ceInd _ a b + _ ≠ ceInd _ a b + _
  rw [hcrossm, hcrossp, zero_add]
  intro h
  have := congrArg (· - ∑ t ∈ G.erase s, ceInd p t.1 t.2) h
  simp only [add_sub_cancel_right, sub_self] at this
  exact one_ne_zero this

/-- The flip across a horizontal edge at a non-vertex point. -/
theorem cycParity_flip_vertical_shift {G : Finset Seg} (hG : IsCycle G) {s : Seg} (hs : s ∈ G)
    {p : Pt} (hp : p ∈ segSet s) (hother : ∀ t ∈ G, t ≠ s → p ∉ segSet t)
    (hpv : p ∉ vertices G) (hhor : s.1.2 = s.2.2) :
    ∀ ε > 0, ∃ z₁ z₂ : Pt, dist z₁ p < ε ∧ dist z₂ p < ε ∧ z₁ ∉ graphSet G ∧ z₂ ∉ graphSet G ∧
      cycParity G z₁ ≠ cycParity G z₂ := by
  classical
  intro ε hε
  set a := s.1 with ha
  set b := s.2 with hb
  have hpa' : p ≠ a := fun h => hpv (h ▸ mem_vertices.2 ⟨s, hs, Or.inl rfl⟩)
  have hpb' : p ≠ b := fun h => hpv (h ▸ mem_vertices.2 ⟨s, hs, Or.inr rfl⟩)
  have hedge2 : ∀ z ∈ segSet s, z.2 = a.2 := by
    rintro z ⟨u, t, hu, ht, hut, rfl⟩
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [← ha, ← hb, ← hhor]; linear_combination a.2 * hut
  have hpa : p.2 = a.2 := hedge2 p hp
  have hA : a.2 = p.2 := hpa.symm
  have hB : b.2 = p.2 := hhor.symm.trans hpa.symm
  have hbetw : (a.1 < p.1 ∧ p.1 < b.1) ∨ (b.1 < p.1 ∧ p.1 < a.1) := by
    obtain ⟨u, t, hu, ht, hut, hpe⟩ := hp
    obtain rfl : u = 1 - t := by linarith
    have h1 : p.1 - a.1 = t * (b.1 - a.1) := by rw [← hpe]; simp [ha, hb]; ring
    have h1' : b.1 - p.1 = (1 - t) * (b.1 - a.1) := by rw [← hpe]; simp [ha, hb]; ring
    have hpa1 : p.1 ≠ a.1 := fun h => hpa' (Prod.ext h hpa)
    have hpb1 : p.1 ≠ b.1 := fun h => hpb' (Prod.ext h (hpa.trans hhor))
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · left; constructor
      · have := mul_nonneg ht (sub_pos.2 h).le
        exact lt_of_le_of_ne (by linarith) (Ne.symm hpa1)
      · have := mul_nonneg hu (sub_pos.2 h).le
        exact lt_of_le_of_ne (by linarith) hpb1
    · exfalso; apply hpa1; rw [h, sub_self, mul_zero] at h1; linarith
    · right; constructor
      · have := mul_nonneg ht (sub_pos.2 h).le
        exact lt_of_le_of_ne (by nlinarith) (Ne.symm hpb1)
      · have := mul_nonneg hu (sub_pos.2 h).le
        exact lt_of_le_of_ne (by nlinarith) hpa1
  have hJi : vJump p a + vJump p b = 1 := by
    rcases hbetw with h | h
    · simp [vJump, hA, hB, h.2, not_lt.2 h.1.le]
    · simp [vJump, hA, hB, h.2, not_lt.2 h.1.le]
  have hno : ∀ z : Pt, ceInd z a b = 0 := by
    intro z
    unfold ceInd; rw [if_neg]
    rintro ⟨h | h, -⟩ <;> linarith [h.1, h.2]
  have hE : ∀ᶠ y in 𝓝 p, ∀ t ∈ G, t ≠ s → y ∉ segSet t ∧
      (p.2 ≤ y.2 → ceInd y t.1 t.2 = ceInd p t.1 t.2) ∧
      (y.2 < p.2 → ceInd y t.1 t.2 + ceInd p t.1 t.2 = vJump p t.1 + vJump p t.2) := by
    refine (Filter.eventually_all_finset G).2 fun t ht => ?_
    by_cases hts : t = s
    · exact Filter.Eventually.of_forall fun _ h => absurd hts h
    · have h1 : ∀ᶠ y in 𝓝 p, y ∉ segSet t :=
        (isCompact_segment' _ _).isClosed.isOpen_compl.mem_nhds (hother t ht hts)
      filter_upwards [h1, crossesEast_jump (hother t ht hts)] with y hy1 hy2 _ using
        ⟨hy1, fun h => ceInd_congr (hy2.1 h), hy2.2⟩
  obtain ⟨ε₀, hε₀, hεE⟩ := Metric.eventually_nhds_iff.1 hE
  set δ := min ε ε₀ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε := by have := min_le_left ε ε₀; linarith
  have hδε₀ : δ < ε₀ := by have := min_le_right ε ε₀; linarith
  have hdp : dist ((p.1, p.2 + δ) : Pt) p = δ := by rw [dist_shift_snd, abs_of_pos hδ0]
  have hdm : dist ((p.1, p.2 + -δ) : Pt) p = δ := by
    rw [dist_shift_snd, abs_neg, abs_of_pos hδ0]
  have hm := hεE (hdm.trans_lt hδε₀)
  have hpl := hεE (hdp.trans_lt hδε₀)
  have hnot : ∀ z : Pt, z.2 ≠ p.2 → (∀ t ∈ G, t ≠ s → z ∉ segSet t) →
      z ∉ graphSet G := fun z hz hj h => by
    obtain ⟨t, ht, ht'⟩ := mem_graphSet.1 h
    by_cases hts : t = s
    · subst hts; exact hz ((hedge2 z ht').trans hA)
    · exact hj t ht hts ht'
  refine ⟨(p.1, p.2 + δ), (p.1, p.2 + -δ), hdp.trans_lt hδε, hdm.trans_lt hδε,
    hnot _ (by simp only; linarith) fun t ht hts => (hpl t ht hts).1,
    hnot _ (by simp only; linarith) fun t ht hts => (hm t ht hts).1, ?_⟩
  have hsum : cycParity G (p.1, p.2 + δ) + cycParity G (p.1, p.2 + -δ) = 1 := by
    unfold cycParity
    rw [← Finset.sum_add_distrib]
    calc _ = ∑ t ∈ G, ((vJump p t.1 + vJump p t.2) + if t = s then 1 else 0) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          by_cases hts : t = s
          · subst hts
            rw [if_pos rfl, hno, hno, hJi]; decide
          · rw [if_neg hts, add_zero, (hpl t ht hts).2.1 (by simp only; linarith), add_comm]
            exact (hm t ht hts).2.2 (by simp only; linarith)
      _ = 1 := by
          rw [Finset.sum_add_distrib, sum_vJump_even G hG.1.1 hG.2, zero_add,
            Finset.sum_ite_eq' G s (fun _ => (1 : ZMod 2)), if_pos hs]
  intro h
  rw [h, zmod2_add_self] at hsum
  exact zero_ne_one hsum

/-- **The flip across an edge of a cycle**, at a point `p` of `segSet s` (`s ∈ G`) lying on no other
segment of `G` and at the height of no vertex (`Jct2`'s `parity_flip_at` for non-horizontal `s`,
`parity_flip_vertical` for horizontal `s`, with the hypotheses the report of batch 126 lists):
there are points arbitrarily close to `p` on the two sides of `s` with different parities. -/
theorem cycParity_flip {G : Finset Seg} (hG : IsCycle G) {s : Seg} (hs : s ∈ G) {p : Pt}
    (hp : p ∈ segSet s) (hother : ∀ t ∈ G, t ≠ s → p ∉ segSet t) (hpv : p ∉ vertices G)
    (hgen : s.1.2 ≠ s.2.2 → ∀ w ∈ vertices G, w.2 ≠ p.2) :
    ∀ ε > 0, ∃ z₁ z₂ : Pt, dist z₁ p < ε ∧ dist z₂ p < ε ∧ z₁ ∉ graphSet G ∧ z₂ ∉ graphSet G ∧
      cycParity G z₁ ≠ cycParity G z₂ := by
  by_cases hhor : s.1.2 = s.2.2
  · exact cycParity_flip_vertical_shift hG hs hp hother hpv hhor
  · exact cycParity_flip_horizontal_shift hs hp hother hhor (hgen hhor)

/-! ### Mayer–Vietoris for cycles -/

/-! #### Reachability in a connected proper graph -/

/-- The internal form of `graph_connected_of_isConnected`, in `ZMod 2`. -/
theorem exists_path_zmod {G : Finset Seg} (hG : IsProper G) (hc : IsPreconnected (graphSet G))
    {a b : Pt} (ha : a ∈ vertices G) (hb : b ∈ vertices G) :
    ∃ P ⊆ G, ∀ w, (deg P w : ZMod 2) = (if w = a then 1 else 0) + (if w = b then 1 else 0) := by
  classical
  set W : Set Pt := {c | ∃ P ⊆ G, ∀ w, (deg P w : ZMod 2) =
    (if w = a then 1 else 0) + (if w = c then 1 else 0)} with hW
  have haW : a ∈ W := ⟨∅, Finset.empty_subset _, fun w => by
    rw [deg_empty, Nat.cast_zero, zmod2_add_self]⟩
  have hstep : ∀ e ∈ G, ∀ c ∈ W, (c = e.1 ∨ c = e.2) → e.1 ∈ W ∧ e.2 ∈ W := by
    intro e he c ⟨P, hPG, hP⟩ hce
    have hnd := hG.1 e he
    have hnew : ∀ d, (c = e.1 ∧ d = e.2 ∨ c = e.2 ∧ d = e.1) → d ∈ W := by
      intro d hd
      refine ⟨symmDiff P {e}, symmDiff_subset_of hPG (Finset.singleton_subset_iff.2 he),
        fun w => ?_⟩
      rw [deg_symmDiff, hP, deg_singleton hnd]
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · linear_combination zmod2_add_self (if w = e.1 then (1 : ZMod 2) else 0)
      · linear_combination zmod2_add_self (if w = e.2 then (1 : ZMod 2) else 0)
    rcases hce with rfl | rfl
    · exact ⟨⟨P, hPG, hP⟩, hnew _ (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨hnew _ (Or.inr ⟨rfl, rfl⟩), ⟨P, hPG, hP⟩⟩
  by_contra hbW
  change b ∉ W at hbW
  set E1 := G.filter fun e => e.1 ∈ W
  set E2 := G.filter fun e => e.1 ∉ W
  have hE1 : ∀ e ∈ E1, e ∈ G ∧ e.1 ∈ W ∧ e.2 ∈ W := fun e he => by
    obtain ⟨heG, he1⟩ := Finset.mem_filter.1 he
    exact ⟨heG, he1, (hstep e heG _ he1 (Or.inl rfl)).2⟩
  have hcov : graphSet G ⊆ graphSet E1 ∪ graphSet E2 := fun z hz => by
    obtain ⟨e, he, hze⟩ := mem_graphSet.1 hz
    by_cases h : e.1 ∈ W
    · exact Or.inl (mem_graphSet.2 ⟨e, Finset.mem_filter.2 ⟨he, h⟩, hze⟩)
    · exact Or.inr (mem_graphSet.2 ⟨e, Finset.mem_filter.2 ⟨he, h⟩, hze⟩)
  obtain ⟨e, he, hae⟩ := mem_vertices.1 ha
  have heW : e.1 ∈ W := (hstep e he a haW hae).1
  obtain ⟨f, hf, hbf⟩ := mem_vertices.1 hb
  have hfW : f.1 ∉ W := fun h => hbW (by
    have := hstep f hf _ h (Or.inl rfl)
    rcases hbf with rfl | rfl
    · exact this.1
    · exact this.2)
  obtain ⟨z, hzG, hz1, hz2⟩ := isPreconnected_closed_iff.1 hc _ _ (isClosed_graphSet E1)
    (isClosed_graphSet E2) hcov
    ⟨a, end_mem_graphSet he hae, end_mem_graphSet (Finset.mem_filter.2 ⟨he, heW⟩) hae⟩
    ⟨b, end_mem_graphSet hf hbf, end_mem_graphSet (Finset.mem_filter.2 ⟨hf, hfW⟩) hbf⟩
  obtain ⟨e', he', hze'⟩ := mem_graphSet.1 hz1
  obtain ⟨f', hf', hzf'⟩ := mem_graphSet.1 hz2
  obtain ⟨he'G, he'1, he'2⟩ := hE1 e' he'
  obtain ⟨hf'G, hf'1⟩ := Finset.mem_filter.1 hf'
  have hne : e' ≠ f' := fun h => hf'1 (h ▸ he'1)
  have hzz := hG.2.2 e' he'G f' hf'G (hG.2.1 e' he'G f' hf'G hne) ⟨hze', hzf'⟩
  have hzW : z ∈ W := by
    rcases hzz.1 with rfl | rfl
    · exact he'1
    · exact he'2
  exact hf'1 (hstep f' hf'G z hzW (by rcases hzz.2 with rfl | rfl <;> simp)).1

/-- A finite union of segments that is connected and has two points is **graph-connected**: any
two of its vertices are joined by a walk along its segments. -/
theorem graph_connected_of_isConnected {G : Finset Seg} (hG : IsProper G)
    (hc : IsConnected (graphSet G)) {a b : Pt} (ha : a ∈ vertices G) (hb : b ∈ vertices G)
    (hab : a ≠ b) :
    ∃ P : Finset Seg, P ⊆ G ∧ ∀ w, Odd (deg P w) ↔ (w = a ∨ w = b) := by
  obtain ⟨P, hPG, hP⟩ := exists_path_zmod hG hc.isPreconnected ha hb
  refine ⟨P, hPG, fun w => ?_⟩
  rw [← ZMod.natCast_eq_one_iff_odd, hP]
  by_cases h1 : w = a <;> by_cases h2 : w = b
  · exact absurd (h1.symm.trans h2) hab
  all_goals simp [h1, h2, hab, Ne.symm hab]

/-! #### Mayer–Vietoris -/

/-- Pairing: if any two points of `O` are joined in `E` and `|O|` is even, there is `P ⊆ E` whose
odd vertices are exactly `O`. -/
theorem exists_join_all {E : Finset Seg} (O : Finset Pt)
    (hjoin : ∀ u ∈ O, ∀ v ∈ O, u ≠ v → ∃ P ⊆ E, ∀ w, (deg P w : ZMod 2) =
      (if w = u then 1 else 0) + (if w = v then 1 else 0))
    (heven : (O.card : ZMod 2) = 0) :
    ∃ P ⊆ E, ∀ w, (deg P w : ZMod 2) = if w ∈ O then 1 else 0 := by
  classical
  induction O using Finset.strongInduction with
  | H O ih =>
    rcases O.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · exact ⟨∅, Finset.empty_subset _, fun w => by simp [deg_empty]⟩
    have hne : (O.erase u).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hu]
      by_contra h
      have h1 : O.card = 1 := by have := Finset.card_pos.2 ⟨u, hu⟩; omega
      rw [h1] at heven; exact absurd heven (by decide)
    obtain ⟨v, hv⟩ := hne
    have huv : v ≠ u := Finset.ne_of_mem_erase hv
    have hvO : v ∈ O := Finset.mem_of_mem_erase hv
    set O' := (O.erase u).erase v with hO'
    have hO'sub : O' ⊂ O :=
      Finset.ssubset_of_ssubset_of_subset (Finset.erase_ssubset hv) (Finset.erase_subset u O)
    have hcard : O.card = O'.card + 2 := by
      rw [hO', Finset.card_erase_of_mem hv, Finset.card_erase_of_mem hu]
      have := Finset.card_pos.2 ⟨u, hu⟩
      have := Finset.card_pos.2 ⟨v, hv⟩
      rw [Finset.card_erase_of_mem hu] at this
      omega
    have heven' : (O'.card : ZMod 2) = 0 := by
      rw [hcard, Nat.cast_add] at heven
      have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
      rw [h2, add_zero] at heven; exact heven
    obtain ⟨P', hP'E, hP'⟩ := ih O' hO'sub
      (fun a ha b hb hab => hjoin a (hO'sub.subset ha) b (hO'sub.subset hb) hab) heven'
    obtain ⟨Q, hQE, hQ⟩ := hjoin u hu v hvO huv.symm
    refine ⟨symmDiff P' Q, symmDiff_subset_of hP'E hQE, fun w => ?_⟩
    rw [deg_symmDiff, hP', hQ]
    by_cases h1 : w = u
    · subst h1
      have : w ∉ O' := fun h => (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h)) rfl
      simp [this, hu, Ne.symm huv]
    by_cases h2 : w = v
    · subst h2
      have : w ∉ O' := fun h => (Finset.ne_of_mem_erase h) rfl
      simp [this, hvO, huv]
    have : w ∈ O' ↔ w ∈ O := by simp [hO', Finset.mem_erase, h1, h2]
    simp [this, h1, h2]

/-- In a connected intersection with two points, every common point lies on a common segment. -/
theorem inter_subset_graphSet_inter {K A B : Finset Seg} (hK : IsProper K) (hA : A ⊆ K)
    (hB : B ⊆ K) (hI : IsPreconnected (graphSet A ∩ graphSet B)) {u v : Pt}
    (hu : u ∈ graphSet A ∩ graphSet B) (hv : v ∈ graphSet A ∩ graphSet B) (huv : u ≠ v) :
    graphSet A ∩ graphSet B ⊆ graphSet (A ∩ B) := by
  classical
  have hvert : ∀ y ∈ graphSet A ∩ graphSet B, y ∉ graphSet (A ∩ B) → y ∈ vertices K := by
    rintro y ⟨hyA, hyB⟩ hy
    obtain ⟨e, he, hye⟩ := mem_graphSet.1 hyA
    obtain ⟨f, hf, hyf⟩ := mem_graphSet.1 hyB
    have hef : e ≠ f := fun h => hy (mem_graphSet.2 ⟨e, Finset.mem_inter.2 ⟨he, h ▸ hf⟩, hye⟩)
    have := hK.2.2 e (hA he) f (hB hf) (hK.2.1 e (hA he) f (hB hf) hef) ⟨hye, hyf⟩
    exact mem_vertices.2 ⟨e, hA he, this.1⟩
  intro x hx
  by_contra hxn
  set t' : Set Pt := graphSet (A ∩ B) ∪ ((vertices K : Set Pt) \ {x})
  have ht' : IsClosed t' := (isClosed_graphSet _).union
    ((vertices K).finite_toSet.subset Set.diff_subset).isClosed
  have hcov : graphSet A ∩ graphSet B ⊆ {x} ∪ t' := fun y hy => by
    by_cases h1 : y ∈ graphSet (A ∩ B)
    · exact Or.inr (Or.inl h1)
    by_cases h2 : y = x
    · exact Or.inl h2
    · exact Or.inr (Or.inr ⟨hvert y hy h1, h2⟩)
  have hy : ∃ y ∈ graphSet A ∩ graphSet B, y ≠ x := by
    by_cases h : u = x
    · exact ⟨v, hv, fun h' => huv (h.trans h'.symm)⟩
    · exact ⟨u, hu, h⟩
  obtain ⟨y, hyI, hyx⟩ := hy
  obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.1 hI _ _ isClosed_singleton ht' hcov
    ⟨x, hx, rfl⟩ ⟨y, hyI, by
      by_cases h1 : y ∈ graphSet (A ∩ B)
      · exact Or.inl h1
      · exact Or.inr ⟨hvert y hyI h1, hyx⟩⟩
  rw [Set.mem_singleton_iff] at hz1
  subst hz1
  rcases hz2 with h | h
  · exact hxn h
  · exact h.2 rfl

/-- **Mayer–Vietoris.** `K` proper; `A, B ⊆ K`; `Z ⊆ A ∪ B` a cycle; `graphSet A ∩ graphSet B`
connected or empty. Then `Z = Z_A Δ Z_B` with `Z_A ⊆ A`, `Z_B ⊆ B` cycles. -/
theorem exists_cycle_decomposition {K A B Z : Finset Seg} (hK : IsProper K) (hA : A ⊆ K)
    (hB : B ⊆ K) (hZ : IsCycle Z) (hZAB : Z ⊆ A ∪ B)
    (hAB : IsConnected (graphSet A ∩ graphSet B) ∨ graphSet A ∩ graphSet B = ∅) :
    ∃ ZA ZB : Finset Seg, ZA ⊆ A ∧ ZB ⊆ B ∧ IsCycle ZA ∧ IsCycle ZB ∧ Z = symmDiff ZA ZB := by
  classical
  have hZnd := hZ.1.1
  set X := Z ∩ A with hX
  set Y := Z \ A with hY
  have hXA : X ⊆ A := Finset.inter_subset_right
  have hYB : Y ⊆ B := fun e he => by
    obtain ⟨heZ, heA⟩ := Finset.mem_sdiff.1 he
    rcases Finset.mem_union.1 (hZAB heZ) with h | h
    · exact absurd h heA
    · exact h
  have hXY : ∀ w, (deg X w : ZMod 2) + deg Y w = deg Z w := fun w => by
    simp only [deg_cast]; exact Finset.sum_inter_add_sum_diff _ _ _
  have hZev : ∀ w, (deg Z w : ZMod 2) = 0 := fun w => even_iff_deg_cast.1 (hZ.2 w)
  set O := (vertices X).filter fun w => (deg X w : ZMod 2) = 1 with hO
  have hdegX : ∀ w, (deg X w : ZMod 2) = if w ∈ O then 1 else 0 := fun w => by
    by_cases hw : w ∈ O
    · rw [if_pos hw]; exact (Finset.mem_filter.1 hw).2
    · rw [if_neg hw]
      by_contra h
      apply hw
      refine Finset.mem_filter.2 ⟨mem_vertices.2 (exists_of_deg_ne_zero h), ?_⟩
      exact (zmod2_eq_zero_or_one _).resolve_left h
  have hOcard : (O.card : ZMod 2) = 0 :=
    card_odd_vertices fun s hs => hZnd s (Finset.mem_of_mem_inter_left hs)
  -- the odd vertices lie in both graphs, at an end of a segment of `A`
  have hOI : ∀ w ∈ O, w ∈ graphSet A ∩ graphSet B ∧ ∃ e ∈ A, w = e.1 ∨ w = e.2 := by
    intro w hw
    have h1 : (deg X w : ZMod 2) = 1 := (Finset.mem_filter.1 hw).2
    have h2 : (deg Y w : ZMod 2) ≠ 0 := by
      intro h; have := hXY w; rw [h1, h, hZev, add_zero] at this; exact one_ne_zero this
    obtain ⟨e, he, hwe⟩ := exists_of_deg_ne_zero (h1.symm ▸ one_ne_zero : (deg X w : ZMod 2) ≠ 0)
    obtain ⟨f, hf, hwf⟩ := exists_of_deg_ne_zero h2
    exact ⟨⟨end_mem_graphSet (hXA he) hwe, end_mem_graphSet (hYB hf) hwf⟩, e, hXA he, hwe⟩
  have hjoin : ∀ u ∈ O, ∀ v ∈ O, u ≠ v → ∃ P ⊆ A ∩ B, ∀ w, (deg P w : ZMod 2) =
      (if w = u then 1 else 0) + (if w = v then 1 else 0) := by
    intro u hu v hv huv
    obtain ⟨huI, e, he, hue⟩ := hOI u hu
    obtain ⟨hvI, f, hf, hvf⟩ := hOI v hv
    have hI : IsConnected (graphSet A ∩ graphSet B) :=
      hAB.resolve_right fun h => by rw [h] at huI; exact huI
    have hsub := inter_subset_graphSet_inter hK hA hB hI.isPreconnected huI hvI huv
    have heq : graphSet (A ∩ B) = graphSet A ∩ graphSet B :=
      Set.Subset.antisymm (Set.subset_inter (graphSet_mono Finset.inter_subset_left)
        (graphSet_mono Finset.inter_subset_right)) hsub
    have hABK : A ∩ B ⊆ K := Finset.inter_subset_left.trans hA
    have hvertAB : ∀ w ∈ graphSet A ∩ graphSet B, ∀ e ∈ A, (w = e.1 ∨ w = e.2) →
        w ∈ vertices (A ∩ B) := by
      intro w hw e he hwe
      obtain ⟨g, hg, hwg⟩ := mem_graphSet.1 (hsub hw)
      by_cases hge : g = e
      · subst hge; exact mem_vertices.2 ⟨g, hg, hwe⟩
      · have := hK.2.2 g (hABK hg) e (hA he) (hK.2.1 g (hABK hg) e (hA he) hge)
          ⟨hwg, by rcases hwe with rfl | rfl
                   · exact left_mem_segment _ _ _
                   · exact right_mem_segment _ _ _⟩
        exact mem_vertices.2 ⟨g, hg, this.1⟩
    exact exists_path_zmod (hK.subset hABK) (heq ▸ hI.isPreconnected)
      (hvertAB u huI e he hue) (hvertAB v hvI f hf hvf)
  obtain ⟨P, hPAB, hP⟩ := exists_join_all O hjoin hOcard
  refine ⟨symmDiff X P, symmDiff Y P, symmDiff_subset_of hXA (hPAB.trans
    Finset.inter_subset_left), symmDiff_subset_of hYB (hPAB.trans Finset.inter_subset_right),
    ⟨hK.subset (symmDiff_subset_of (hXA.trans hA) (hPAB.trans (Finset.inter_subset_left.trans hA))),
      fun w => even_iff_deg_cast.2 (by rw [deg_symmDiff, hdegX, hP, zmod2_add_self])⟩,
    ⟨hK.subset (symmDiff_subset_of (hYB.trans hB) (hPAB.trans (Finset.inter_subset_right.trans hB))),
      fun w => even_iff_deg_cast.2 (by
        rw [deg_symmDiff, hP]
        have := hXY w
        rw [hZev, hdegX] at this
        linear_combination this)⟩, ?_⟩
  rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, symmDiff_bot,
    Disjoint.symmDiff_eq_sup (Finset.disjoint_of_subset_left Finset.inter_subset_right
      Finset.disjoint_sdiff), Finset.sup_eq_union, Finset.union_comm, Finset.sdiff_union_inter]

/-! ### What batch 128 will add (statements only, as `Prop`s; no `sorry`) -/

/-- **A separating graph contains an odd cycle** (batch 128): if the proper graph `G` separates
`x` from `y`, some cycle `Z ⊆ G` has `cycParity Z x ≠ cycParity Z y`. -/
def SeparatingGraphHasOddCycle : Prop :=
  ∀ (G : Finset Seg), IsProper G → ∀ x y : Pt, SeparatesPts (graphSet G) x y →
    ∃ Z : Finset Seg, Z ⊆ G ∧ IsCycle Z ∧ cycParity Z x ≠ cycParity Z y

/-- **Janiszewski for polygonal compacta** (the weakened field, batch 129): `A`, `B` finite unions
of segments, `A ∩ B` connected or empty, neither separating `x` from `y` ⇒ `A ∪ B` does not. -/
def JaniszewskiPoly : Prop :=
  ∀ (SA SB : Finset Seg), (∀ s ∈ SA, s.1 ≠ s.2) → (∀ s ∈ SB, s.1 ≠ s.2) →
    (IsConnected (graphSet SA ∩ graphSet SB) ∨ graphSet SA ∩ graphSet SB = ∅) →
    ∀ x y : Pt, ¬ SeparatesPts (graphSet SA) x y → ¬ SeparatesPts (graphSet SB) x y →
      ¬ SeparatesPts (graphSet SA ∪ graphSet SB) x y

/-- Separation passes to a larger set not containing the two points. -/
theorem separatesPts_mono {C D : Set Pt} {x y : Pt} (h : SeparatesPts C x y) (hCD : C ⊆ D)
    (hx : x ∉ D) (hy : y ∉ D) : SeparatesPts D x y :=
  ⟨hx, hy, fun hyD => h.2.2 (connectedComponentIn_mono x (Set.compl_subset_compl.2 hCD) hyD)⟩

open Classical in
/-- The pieces of the subdivision lying in `graphSet S'` (for `S' ⊆ S`) cover `graphSet S'`. -/
theorem graphSet_filter_subdivision {S S' K : Finset Seg} (hS' : S' ⊆ S)
    (hKcov : ∀ s ∈ S, segSet s = ⋃ t ∈ K.filter (fun t => segSet t ⊆ segSet s), segSet t) :
    graphSet (K.filter fun t => segSet t ⊆ graphSet S') = graphSet S' := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_graphSet.1 hz
    exact (Finset.mem_filter.1 ht).2 hzt
  · intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_graphSet.1 hz
    rw [hKcov s (hS' hs)] at hzs
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 hzs
    obtain ⟨htK, hts⟩ := Finset.mem_filter.1 ht
    exact mem_graphSet.2 ⟨t, Finset.mem_filter.2 ⟨htK,
      hts.trans fun w hw => mem_graphSet.2 ⟨s, hs, hw⟩⟩, hzt⟩

/-- **Janiszewski from the odd cycle** (this batch, given the batch-128 statement as a hypothesis):
subdivide `SA ∪ SB` to a proper `K` (`exists_proper_subdivision`), take the pieces inside
`graphSet SA` as `A` and inside `graphSet SB` as `B`; if `A ∪ B` separates, an odd cycle `Z`
exists; decompose `Z = Z_A Δ Z_B`; by additivity one of them has different parities at `x`, `y`;
`separatesPts_of_cycParity_ne` then contradicts the hypothesis for `SA` or `SB`. -/
theorem janiszewskiPoly_of_oddCycle (h : SeparatingGraphHasOddCycle) : JaniszewskiPoly := by
  classical
  intro SA SB hSA hSB hAB x y hnA hnB hsep
  obtain ⟨K, hK, hKS, hKsub, hKcov⟩ := exists_proper_subdivision (SA ∪ SB)
    (fun s hs => (Finset.mem_union.1 hs).elim (hSA s) (hSB s))
  set A := K.filter fun t => segSet t ⊆ graphSet SA with hA
  set B := K.filter fun t => segSet t ⊆ graphSet SB with hB
  have hgA : graphSet A = graphSet SA := graphSet_filter_subdivision Finset.subset_union_left hKcov
  have hgB : graphSet B = graphSet SB :=
    graphSet_filter_subdivision Finset.subset_union_right hKcov
  have hgK : graphSet K = graphSet SA ∪ graphSet SB := by
    rw [hKS]; simp only [graphSet, Finset.set_biUnion_union]
  have hKAB : K ⊆ A ∪ B := fun t ht => by
    obtain ⟨s, hs, hts⟩ := hKsub t ht
    rcases Finset.mem_union.1 hs with hs' | hs'
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ht,
        hts.trans fun w hw => mem_graphSet.2 ⟨s, hs', hw⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ht,
        hts.trans fun w hw => mem_graphSet.2 ⟨s, hs', hw⟩⟩)
  obtain ⟨Z, hZK, hZ, hZodd⟩ := h K hK x y (hgK ▸ hsep)
  obtain ⟨ZA, ZB, hZA, hZB, hcA, hcB, rfl⟩ := exists_cycle_decomposition hK
    (Finset.filter_subset _ K) (Finset.filter_subset _ K) hZ (hZK.trans hKAB)
    (by rw [hgA, hgB]; exact hAB)
  rw [cycParity_symmDiff, cycParity_symmDiff] at hZodd
  have hxA : x ∉ graphSet SA := fun h' => hsep.1 (Or.inl h')
  have hyA : y ∉ graphSet SA := fun h' => hsep.2.1 (Or.inl h')
  have hxB : x ∉ graphSet SB := fun h' => hsep.1 (Or.inr h')
  have hyB : y ∉ graphSet SB := fun h' => hsep.2.1 (Or.inr h')
  have hZAs : graphSet ZA ⊆ graphSet SA := hgA ▸ graphSet_mono hZA
  have hZBs : graphSet ZB ⊆ graphSet SB := hgB ▸ graphSet_mono hZB
  by_cases hA' : cycParity ZA x = cycParity ZA y
  · have hne : cycParity ZB x ≠ cycParity ZB y := fun h' => hZodd (by rw [hA', h'])
    exact hnB (separatesPts_mono (separatesPts_of_cycParity_ne hcB.1.1 hcB.2
      (fun h' => hxB (hZBs h')) (fun h' => hyB (hZBs h')) hne) hZBs hxB hyB)
  · exact hnA (separatesPts_mono (separatesPts_of_cycParity_ne hcA.1.1 hcA.2
      (fun h' => hxA (hZAs h')) (fun h' => hyA (hZAs h')) hA') hZAs hxA hyA)

end HPC.Plane
