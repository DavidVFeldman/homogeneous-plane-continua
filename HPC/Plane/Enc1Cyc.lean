import HPC.Plane.JanPoly

/-!
# Batch 130, cycle part: the polygon interior as the odd parity set; simple cycles

* `polyInterior_eq_oddSet`: for simple vertices `v`, `polyInterior (polygonOf v)` is the set of
  points off the polygon with crossing parity `1`;
* `polyEdges`, `cycParity_polyEdges`, `graphSet_polyEdges`: a simple closed polygon as a cycle of
  segments;
* `IsSimpleCycle`, `exists_simpleCycle_decomposition`, `cycParity_foldr`: every mod-2 cycle is an
  edge-disjoint union of simple cycles, and parity is additive over such a union.

The decomposition: a nonempty cycle contains a simple cycle (`exists_cycle_vertices`: a path of
distinct vertices is extended at its end along a second edge, which exists by evenness and
properness, until the new end is already on the path; the path cannot grow beyond the number of
vertices), every degree of a simple cycle is even (`simpleCycle_of_vertices`), so removing it leaves
a cycle; strong induction on the number of edges.
-/

namespace HPC.Plane

open Set Metric

/-- For a simple closed polygon `polygonOf v`, `polyInterior (polygonOf v)` is the set of points
off the polygon with crossing parity `1` (from the proof of `jct_polygon`:
`polyInterior_eq_of_split` with the two parity classes). -/
theorem polyInterior_eq_oddSet {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) :
    polyInterior (polygonOf v) = {x | x ∉ polygonOf v ∧ parity v x = 1} := by
  obtain ⟨-, -, -, hbdd, -, R, hR⟩ := polygon_separates hv
  refine polyInterior_eq_of_split (isOpen_parity_set v 1) (isOpen_parity_set v 0) ?_ ?_
    (isConnected_parity_set hv 1) (isConnected_parity_set hv 0) hbdd ?_
  · rw [compl_eq_union_parity_sets v 0, zero_add, union_comm]
  · have := (disjoint_parity_sets v 0).symm
    rwa [zero_add] at this
  · intro hb
    obtain ⟨C, hC⟩ := hb.subset_closedBall (0 : Pt)
    set x : Pt := (max R C + 1, 0)
    have h1 : max R C + 1 ≤ dist x 0 := by
      rw [Prod.dist_eq]
      refine le_trans ?_ (le_max_left _ _)
      rw [Real.dist_eq]
      simp only [x, Prod.fst_zero, sub_zero]
      exact le_abs_self _
    have := hC (hR x (by linarith [le_max_left R C]))
    rw [mem_closedBall] at this
    linarith [le_max_right R C]

/-- The edges of the closed polygon `v` as segments, `v i — v (i+1)`. -/
noncomputable def polyEdges {n : ℕ} (v : Fin n → Pt) : Finset Seg :=
  Finset.univ.image fun i : Fin n => (v i, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)

/-- The parity of a simple closed polygon as a cycle of segments equals its `parity` as a vertex
list (the edge map is injective for injective `v`, so the sums agree term by term). -/
theorem cycParity_polyEdges {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (x : Pt) :
    cycParity (polyEdges v) x = parity v x := by
  unfold cycParity polyEdges
  rw [Finset.sum_image (fun i _ j _ h => hv.2.1 (congrArg Prod.fst h))]
  classical
  simp only [ceInd, parity, crossCount]
  rw [Finset.sum_boole]

theorem graphSet_polyEdges {n : ℕ} (v : Fin n → Pt) : graphSet (polyEdges v) = polygonOf v := by
  classical
  simp [graphSet, polyEdges, polygonOf, segSet]

/-! ### Simple cycles in a proper graph -/

/-- A finite set of segments `C` is a **simple cycle** if its point set is the simple closed
polygon of simple vertices `v` and its parity is the crossing parity of `v`. -/
def IsSimpleCycle (C : Finset Seg) : Prop :=
  ∃ (n : ℕ) (v : Fin n → Pt), IsSimpleVertices v ∧ graphSet C = polygonOf v ∧
    ∀ x, cycParity C x = parity v x

/-- The cyclic successor of an index. -/
def fnxt {n : ℕ} (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩

theorem fnxt_val {n : ℕ} (i : Fin n) :
    (fnxt i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  unfold fnxt
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

theorem fnxt_injective {n : ℕ} : Function.Injective (fnxt : Fin n → Fin n) := by
  intro i j h
  have := congrArg Fin.val h
  rw [fnxt_val, fnxt_val] at this
  have hi := i.isLt
  have hj := j.isLt
  ext
  split_ifs at this <;> omega

theorem fnxt_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : fnxt i ≠ i := by
  intro h
  have := congrArg Fin.val h
  rw [fnxt_val] at this
  have hi := i.isLt
  split_ifs at this <;> omega

theorem fnxt_fnxt_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : fnxt (fnxt i) ≠ i := by
  intro h
  have := congrArg Fin.val h
  rw [fnxt_val, fnxt_val] at this
  have hi := i.isLt
  split_ifs at this <;> omega

/-- Adjacency in a graph of segments. -/
def SAdj (Z : Finset Seg) (a b : Pt) : Prop := (a, b) ∈ Z ∨ (b, a) ∈ Z

theorem SAdj.symm {Z : Finset Seg} {a b : Pt} (h : SAdj Z a b) : SAdj Z b a := Or.symm h

theorem SAdj.ne {Z : Finset Seg} (hZ : IsProper Z) {a b : Pt} (h : SAdj Z a b) : a ≠ b := by
  rcases h with h | h
  · exact hZ.1 _ h
  · exact fun e => hZ.1 _ h e.symm

theorem SAdj.mem_vertices {Z : Finset Seg} {a b : Pt} (h : SAdj Z a b) : a ∈ vertices Z := by
  rcases h with h | h
  · exact HPC.Plane.mem_vertices.2 ⟨_, h, Or.inl rfl⟩
  · exact HPC.Plane.mem_vertices.2 ⟨_, h, Or.inr rfl⟩

/-- In a cycle, a vertex adjacent to `q` has a second neighbour. -/
theorem exists_other_nbr {Z : Finset Seg} (hZ : IsCycle Z) {p q : Pt} (h : SAdj Z p q) :
    ∃ r, SAdj Z p r ∧ r ≠ q := by
  classical
  obtain ⟨s0, hs0, hs0p, hs0q⟩ : ∃ s0 ∈ Z, (p = s0.1 ∨ p = s0.2) ∧ (s0 = (p, q) ∨ s0 = (q, p)) := by
    rcases h with h | h
    · exact ⟨_, h, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl, Or.inr rfl⟩
  have hpq : p ≠ q := h.ne hZ.1
  have hpos : 0 < deg Z p := Finset.card_pos.2 ⟨s0, Finset.mem_filter.2 ⟨hs0, hs0p⟩⟩
  have h2 : 1 < deg Z p := by
    obtain ⟨k, hk⟩ := hZ.2 p
    omega
  obtain ⟨t, ht, hts⟩ := Finset.exists_mem_ne h2 s0
  rw [Finset.mem_filter] at ht
  obtain ⟨htZ, htp⟩ := ht
  have key : ∀ r, (t = (p, r) ∨ t = (r, p)) → ∃ r, SAdj Z p r ∧ r ≠ q := by
    intro r hr
    refine ⟨r, ?_, ?_⟩
    · rcases hr with rfl | rfl
      · exact Or.inl htZ
      · exact Or.inr htZ
    · rintro rfl
      have hne : ((p, r) : Seg) ≠ (r, p) := fun e => hpq (congrArg Prod.fst e)
      have hseg : segSet (p, r) = segSet (r, p) := segment_symm ℝ p r
      rcases hr with rfl | rfl <;> rcases hs0q with rfl | rfl
      · exact hts rfl
      · exact hZ.1.2.1 _ htZ _ hs0 hne hseg
      · exact hZ.1.2.1 _ hs0 _ htZ hne hseg
      · exact hts rfl
  rcases htp with h1 | h1
  · exact key t.2 (Or.inl (by rw [h1]))
  · exact key t.1 (Or.inr (by rw [h1]))

/-- A path of `k` distinct points, consecutive ones adjacent. -/
def IsSPath (Z : Finset Seg) (f : ℕ → Pt) (k : ℕ) : Prop :=
  (∀ a < k, ∀ b < k, f a = f b → a = b) ∧ (∀ a, a + 1 < k → SAdj Z (f a) (f (a + 1)))

theorem cycle_or_extend {Z : Finset Seg} (hZ : IsCycle Z) {f : ℕ → Pt} {k : ℕ}
    (hf : IsSPath Z f k) (hk : 2 ≤ k) :
    (∃ (n : ℕ) (w : Fin n → Pt), 3 ≤ n ∧ Function.Injective w ∧
      ∀ i : Fin n, SAdj Z (w i) (w (fnxt i))) ∨ ∃ g, IsSPath Z g (k + 1) := by
  have hqp : SAdj Z (f (k - 1)) (f (k - 2)) := by
    have := hf.2 (k - 2) (by omega)
    rw [show k - 2 + 1 = k - 1 by omega] at this
    exact this.symm
  obtain ⟨r, hr, hrq⟩ := exists_other_nbr hZ hqp
  by_cases hex : ∃ i < k, f i = r
  · left
    obtain ⟨i, hik, rfl⟩ := hex
    have hi1 : i ≠ k - 1 := fun h => (hr.ne hZ.1) (by rw [h])
    have hi2 : i ≠ k - 2 := fun h => hrq (by rw [h])
    refine ⟨k - i, fun j => f (i + j), by omega, ?_, ?_⟩
    · intro a b h
      have := hf.1 (i + a) (by omega) (i + b) (by omega) h
      exact Fin.ext (by omega)
    · intro j
      have hj := j.isLt
      have hv := fnxt_val j
      by_cases hj' : j.val + 1 = k - i
      · rw [if_pos hj'] at hv
        simp only [hv, add_zero]
        rw [show i + j.val = k - 1 by omega]
        exact hr
      · rw [if_neg hj'] at hv
        simp only [hv]
        rw [← add_assoc]
        exact hf.2 (i + j) (by omega)
  · right
    push_neg at hex
    refine ⟨fun a => if a = k then r else f a, ?_, ?_⟩
    · intro a ha b hb h
      by_cases hak : a = k <;> by_cases hbk : b = k
      · rw [hak, hbk]
      · simp only [hak, hbk, if_true, if_false] at h
        exact absurd h.symm (hex b (by omega))
      · simp only [hak, hbk, if_true, if_false] at h
        exact absurd h (hex a (by omega))
      · simp only [hak, hbk, if_false] at h
        exact hf.1 a (by omega) b (by omega) h
    · intro a ha
      by_cases ha' : a + 1 = k
      · simp only [ha', if_true, show a ≠ k by omega, if_false]
        rw [show a = k - 1 by omega]
        exact hr
      · simp only [ha', show a ≠ k by omega, if_false]
        exact hf.2 a (by omega)

/-- **A nonempty cycle contains a simple cycle**, as a cyclic sequence of at least three distinct
vertices, consecutive ones adjacent. -/
theorem exists_cycle_vertices {Z : Finset Seg} (hZ : IsCycle Z) (hne : Z.Nonempty) :
    ∃ (n : ℕ) (w : Fin n → Pt), 3 ≤ n ∧ Function.Injective w ∧
      ∀ i : Fin n, SAdj Z (w i) (w (fnxt i)) := by
  classical
  obtain ⟨s, hs⟩ := hne
  have bound : ∀ g k, IsSPath Z g k → 2 ≤ k → k ≤ (vertices Z).card := by
    intro g k hg hk
    have hmem : ∀ a ∈ Finset.range k, g a ∈ vertices Z := by
      intro a ha
      rw [Finset.mem_range] at ha
      by_cases h : a + 1 < k
      · exact (hg.2 a h).mem_vertices
      · have := hg.2 (a - 1) (by omega)
        rw [show a - 1 + 1 = a by omega] at this
        exact this.symm.mem_vertices
    have := Finset.card_le_card_of_injOn g (fun a ha => hmem a ha) (fun a ha b hb h =>
      hg.1 a (Finset.mem_range.1 (Finset.mem_coe.1 ha)) b
        (Finset.mem_range.1 (Finset.mem_coe.1 hb)) h)
    simpa using this
  have main : ∀ m g k, IsSPath Z g k → 2 ≤ k → k + m = (vertices Z).card →
      ∃ (n : ℕ) (w : Fin n → Pt), 3 ≤ n ∧ Function.Injective w ∧
        ∀ i : Fin n, SAdj Z (w i) (w (fnxt i)) := by
    intro m
    induction m with
    | zero =>
      intro g k hg hk hkm
      rcases cycle_or_extend hZ hg hk with h | ⟨g', hg'⟩
      · exact h
      · have := bound g' (k + 1) hg' (by omega)
        omega
    | succ m ih =>
      intro g k hg hk hkm
      rcases cycle_or_extend hZ hg hk with h | ⟨g', hg'⟩
      · exact h
      · exact ih g' (k + 1) hg' (by omega) (by omega)
  have h12 : s.1 ≠ s.2 := hZ.1.1 s hs
  have hg : IsSPath Z (fun a => if a = 0 then s.1 else s.2) 2 := by
    refine ⟨fun a ha b hb h => ?_, fun a ha => ?_⟩
    · by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> simp [ha0, hb0] at h <;> try omega
      · exact absurd h h12
      · exact absurd h.symm h12
    · obtain rfl : a = 0 := by omega
      simp only [if_true, show (0 : ℕ) + 1 ≠ 0 by omega, if_false]
      exact Or.inl hs
  have := bound _ 2 hg le_rfl
  exact main ((vertices Z).card - 2) _ 2 hg le_rfl (by omega)

/-- A cyclic sequence of distinct adjacent vertices of a proper graph spans a simple cycle, all
of whose degrees are even. -/
theorem simpleCycle_of_vertices {Z : Finset Seg} (hZ : IsProper Z) {n : ℕ} {w : Fin n → Pt}
    (hn : 3 ≤ n) (hw : Function.Injective w) (hadj : ∀ i, SAdj Z (w i) (w (fnxt i))) :
    ∃ C ⊆ Z, C.Nonempty ∧ IsSimpleCycle C ∧ ∀ p, Even (deg C p) := by
  classical
  set seg : Fin n → Seg := fun i =>
    if (w i, w (fnxt i)) ∈ Z then (w i, w (fnxt i)) else (w (fnxt i), w i) with hseg_def
  have hsegZ : ∀ i, seg i ∈ Z := by
    intro i
    simp only [hseg_def]
    split_ifs with h
    · exact h
    · exact (hadj i).resolve_left h
  have hsegSet : ∀ i, segSet (seg i) = polyEdge w i := by
    intro i
    simp only [hseg_def]
    split_ifs
    · rfl
    · exact segment_symm ℝ _ _
  have hends : ∀ i p, (p = (seg i).1 ∨ p = (seg i).2) ↔ (p = w i ∨ p = w (fnxt i)) := by
    intro i p
    simp only [hseg_def]
    split_ifs
    · rfl
    · exact or_comm
  have hpos : 0 < n := by omega
  have hseginj : Function.Injective seg := by
    intro i j h
    have h1 := (hends j (w i)).1 (h ▸ (hends i (w i)).2 (Or.inl rfl))
    have h2 := (hends j (w (fnxt i))).1 (h ▸ (hends i (w (fnxt i))).2 (Or.inr rfl))
    rcases h1 with h1 | h1
    · exact hw h1
    · have hij : i = fnxt j := hw h1
      rcases h2 with h2 | h2
      · exact absurd (by rw [hij] at h2; exact hw h2) (fnxt_fnxt_ne hn j)
      · exact fnxt_injective (hw h2)
  set C : Finset Seg := Finset.univ.image seg with hC
  have hv : IsSimpleVertices w := by
    refine ⟨hn, hw, fun i j hij => ?_⟩
    have hne : segSet (seg i) ≠ segSet (seg j) :=
      hZ.2.1 _ (hsegZ i) _ (hsegZ j) (fun h => hij (hseginj h))
    have hint := hZ.2.2 _ (hsegZ i) _ (hsegZ j) hne
    rw [hsegSet, hsegSet] at hint
    refine ⟨fun _ p hp => ?_, fun hna => ?_⟩
    · obtain ⟨h1, -⟩ := hint hp
      have := (hends i p).1 h1
      simp only [mem_insert_iff, mem_singleton_iff]
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rw [Set.disjoint_left]
      intro p hp1 hp2
      obtain ⟨h1, h2⟩ := hint ⟨hp1, hp2⟩
      have e1 := (hends i p).1 h1
      have e2 := (hends j p).1 h2
      have hna' : fnxt i ≠ j ∧ fnxt j ≠ i := by
        constructor
        · intro h; exact hna (Or.inl (congrArg Fin.val h))
        · intro h; exact hna (Or.inr (congrArg Fin.val h))
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · exact hij (hw (e1.symm.trans e2))
      · exact hna'.2 (hw (e1.symm.trans e2)).symm
      · exact hna'.1 (hw (e1.symm.trans e2))
      · exact hij (fnxt_injective (hw (e1.symm.trans e2)))
  refine ⟨C, ?_, ⟨seg ⟨0, hpos⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ⟨n, w, hv, ?_, ?_⟩, ?_⟩
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    exact hsegZ i
  · ext p
    simp only [graphSet, hC, Finset.set_biUnion_finset_image, hsegSet, polygonOf, polyEdge]
    simp
  · intro x
    rw [← cycParity_polyEdges hv]
    unfold cycParity polyEdges
    rw [hC, Finset.sum_image (fun i _ j _ h => hseginj h),
      Finset.sum_image (fun i _ j _ h => hw (congrArg Prod.fst h))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hseg_def]
    split_ifs
    · rfl
    · exact ceInd_comm _ _ _
  · intro p
    have hdeg : deg C p = (Finset.univ.filter fun i => p = w i ∨ p = w (fnxt i)).card := by
      unfold deg
      rw [hC, Finset.filter_image, Finset.card_image_of_injective _ hseginj]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hends i p
    rw [hdeg, Finset.filter_or, Finset.card_union_of_disjoint]
    · have : (Finset.univ.filter fun i => p = w (fnxt i)).card =
          (Finset.univ.filter fun i => p = w i).card := by
        refine Finset.card_bij (fun i _ => fnxt i) ?_ ?_ ?_
        · intro i hi
          simpa using hi
        · intro i _ j _ h
          exact fnxt_injective h
        · intro b hb
          obtain ⟨a, rfl⟩ := (Finite.injective_iff_surjective.1 fnxt_injective) b
          exact ⟨a, by simpa using hb, rfl⟩
      rw [this]
      exact ⟨_, rfl⟩
    · rw [Finset.disjoint_filter]
      intro i _ h1 h2
      exact fnxt_ne (by omega) i (hw (h2.symm.trans h1))

/-- **Every cycle is an edge-disjoint union of simple cycles.** -/
theorem exists_simpleCycle_decomposition {Z : Finset Seg} (hZ : IsCycle Z) :
    ∃ L : List (Finset Seg), (∀ C ∈ L, IsSimpleCycle C) ∧ (∀ C ∈ L, C ⊆ Z) ∧
      L.Pairwise Disjoint ∧ Z = L.foldr (· ∪ ·) ∅ := by
  classical
  induction h : Z.card using Nat.strong_induction_on generalizing Z with
  | _ k ih =>
  rcases Z.eq_empty_or_nonempty with rfl | hne
  · exact ⟨[], by simp, by simp, List.Pairwise.nil, rfl⟩
  obtain ⟨n, w, hn, hw, hadj⟩ := exists_cycle_vertices hZ hne
  obtain ⟨C, hCZ, hCne, hCs, hCe⟩ := simpleCycle_of_vertices hZ.1 hn hw hadj
  have hZ' : IsCycle (Z \ C) := by
    refine ⟨hZ.1.subset Finset.sdiff_subset, fun p => ?_⟩
    have hsplit : deg Z p = deg C p + deg (Z \ C) p := by
      unfold deg
      conv_lhs => rw [← Finset.union_sdiff_of_subset hCZ]
      rw [Finset.filter_union, Finset.card_union_of_disjoint]
      exact Finset.disjoint_filter_filter Finset.disjoint_sdiff
    have := hZ.2 p
    rw [hsplit] at this
    exact (Nat.even_add.1 this).1 (hCe p)
  have hlt : (Z \ C).card < k := by
    rw [← h]
    exact Finset.card_lt_card (Finset.sdiff_ssubset hCZ hCne)
  obtain ⟨L, h1, h2, h3, h4⟩ := ih _ hlt hZ' rfl
  refine ⟨C :: L, ?_, ?_, ?_, ?_⟩
  · intro D hD
    rcases List.mem_cons.1 hD with rfl | hD
    · exact hCs
    · exact h1 D hD
  · intro D hD
    rcases List.mem_cons.1 hD with rfl | hD
    · exact hCZ
    · exact (h2 D hD).trans Finset.sdiff_subset
  · exact List.pairwise_cons.2 ⟨fun D hD =>
      Finset.disjoint_of_subset_right (h2 D hD) Finset.disjoint_sdiff, h3⟩
  · simp only [List.foldr_cons]
    rw [← h4]
    exact (Finset.union_sdiff_of_subset hCZ).symm

theorem mem_foldr_union {L : List (Finset Seg)} {s : Seg} :
    s ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ D ∈ L, s ∈ D := by
  induction L with
  | nil => simp
  | cons C L ih => simp [ih]

/-- Parity of an edge-disjoint union is the sum of the parities. -/
theorem cycParity_foldr {L : List (Finset Seg)} (hL : L.Pairwise Disjoint) (x : Pt) :
    cycParity (L.foldr (· ∪ ·) ∅) x = (L.map fun C => cycParity C x).sum := by
  classical
  induction L with
  | nil => simp [cycParity]
  | cons C L ih =>
    rw [List.pairwise_cons] at hL
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [← ih hL.2]
    unfold cycParity
    rw [Finset.sum_union]
    rw [Finset.disjoint_left]
    intro s hsC hsL
    obtain ⟨D, hD, hsD⟩ := mem_foldr_union.1 hsL
    exact Finset.disjoint_left.1 (hL.1 D hD) hsC hsD

end HPC.Plane
