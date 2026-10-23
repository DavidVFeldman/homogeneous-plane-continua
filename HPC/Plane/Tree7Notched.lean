import HPC.Plane.Tree6

/-!
# Batch 119, auxiliary: the notched square as a 20-gon (finite checks)

The vertex list `notchedVertices` and the polygon `notchedPoly` of `HPC/Plane/Tree7.lean` §2 (moved
here so that the expensive finite checks are compiled once), axis-parallel segments as boxes
(`segment_vert`, `segment_horiz`), the closure of a notched square, the frontier of a notched
square (`frontier_notched'`), injectivity of the vertex list and the edge conditions of
`IsSimpleClosedPolygon` (`notchedVertices_edges`: 400 ordered pairs of edges, each reduced to linear
arithmetic).
-/

namespace HPC.Plane

open Set Metric

/-- The twenty vertices of the boundary of `notched o δ η r a b`, counterclockwise from the
bottom-left corner `(x₀, y₀)` of the square (see `HPC/Plane/Tree7.lean`, §2). -/
def notchedVertices (o : Pt) (δ η r : ℝ) (a b : ℤ) : Fin 20 → Pt :=
  let x₀ : ℝ := o.1 + δ * a
  let x₁ : ℝ := o.1 + δ * (a + 1)
  let y₀ : ℝ := o.2 + δ * b
  let y₁ : ℝ := o.2 + δ * (b + 1)
  ![(x₀, y₀), (x₀ + r, y₀), (x₀ + r, y₀ - η), (x₁ - r, y₀ - η), (x₁ - r, y₀), (x₁, y₀),
    (x₁, y₀ + r), (x₁ + η, y₀ + r), (x₁ + η, y₁ - r), (x₁, y₁ - r), (x₁, y₁),
    (x₁ - r, y₁), (x₁ - r, y₁ + η), (x₀ + r, y₁ + η), (x₀ + r, y₁), (x₀, y₁),
    (x₀, y₁ - r), (x₀ - η, y₁ - r), (x₀ - η, y₀ + r), (x₀, y₀ + r)]

theorem segment_vert (x y y' : ℝ) :
    segment ℝ ((x, y) : Pt) (x, y') = {p : Pt | p.1 = x ∧ p.2 ∈ uIcc y y'} := by
  rw [← Prod.image_mk_segment_right, segment_eq_uIcc]
  ext p; simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨rfl, hz⟩
  · rintro ⟨h1, h2⟩; exact ⟨p.2, h2, by rw [← h1]⟩

theorem segment_horiz (x x' y : ℝ) :
    segment ℝ ((x, y) : Pt) (x', y) = {p : Pt | p.1 ∈ uIcc x x' ∧ p.2 = y} := by
  rw [← Prod.image_mk_segment_left, segment_eq_uIcc]
  ext p; simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨hz, rfl⟩
  · rintro ⟨h1, h2⟩; exact ⟨p.1, h1, by rw [← h2]⟩

/-- The boundary polygon of a notched square. -/
def notchedPoly (o : Pt) (δ η r : ℝ) (a b : ℤ) : Set Pt :=
  polygonOf (notchedVertices o δ η r a b)

theorem closure_notched (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    closure (notched o δ η r a b) =
      Icc (o.1 + δ * a) (o.1 + δ * (a + 1)) ×ˢ Icc (o.2 + δ * b) (o.2 + δ * (b + 1)) ∪
      Icc (o.1 + δ * a + r) (o.1 + δ * (a + 1) - r) ×ˢ
        Icc (o.2 + δ * b - η) (o.2 + δ * (b + 1) + η) ∪
      Icc (o.1 + δ * a - η) (o.1 + δ * (a + 1) + η) ×ˢ
        Icc (o.2 + δ * b + r) (o.2 + δ * (b + 1) - r) := by
  have ha : δ * ((a : ℝ) + 1) = δ * a + δ := by ring
  have hb : δ * ((b : ℝ) + 1) = δ * b + δ := by ring
  simp only [notched, closure_union, closure_prod_eq]
  rw [closure_Ioo (by linarith), closure_Ioo (by linarith), closure_Ioo (by linarith),
    closure_Ioo (by linarith), closure_Ioo (by linarith), closure_Ioo (by linarith)]

macro "edge_tac" : tactic => `(tactic| (refine ⟨?_, ?_⟩ <;>
  first | linarith | (left; constructor <;> linarith) | (right; constructor <;> linarith)))

set_option maxHeartbeats 2000000 in
theorem notchedPoly_subset_frontier (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    notchedPoly o δ η r a b ⊆ closure (notched o δ η r a b) \ notched o δ η r a b := by
  have ha : δ * ((a : ℝ) + 1) = δ * a + δ := by ring
  have hb : δ * ((b : ℝ) + 1) = δ * b + δ := by ring
  intro p hp
  obtain ⟨j, hj⟩ := mem_iUnion.1 hp
  rw [closure_notched o hη hr h4]
  fin_cases j <;> simp [notchedVertices, segment_vert, segment_horiz, Set.mem_uIcc] at hj <;>
    casesm* _ ∧ _, _ ∨ _ <;>
    refine ⟨?_, ?_⟩ <;>
    first
    | (rintro ((⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) | ⟨⟨h1, h2⟩, h3, h4⟩) <;> linarith)
    | exact Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)
    | exact Or.inl (Or.inr ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)
    | exact Or.inr ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem frontier_notched' (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : frontier (notched o δ η r a b) = notchedPoly o δ η r a b := by
  have ha : δ * ((a : ℝ) + 1) = δ * a + δ := by ring
  have hb : δ * ((b : ℝ) + 1) = δ * b + δ := by ring
  rw [(isOpen_notched _ _ _ _ _ _).frontier_eq]
  ext p
  constructor
  · rintro ⟨hcl, hN⟩
    rw [closure_notched o hη hr h4] at hcl
    have e : ∀ k : Fin 20, p ∈ segment ℝ (notchedVertices o δ η r a b k)
        (notchedVertices o δ η r a b ⟨(k.val + 1) % 20, Nat.mod_lt _ (Fin.pos k)⟩) →
        p ∈ notchedPoly o δ η r a b := fun k hk => mem_iUnion.2 ⟨k, hk⟩
    rcases hcl with (⟨⟨hX0, hX1⟩, hY0, hY1⟩ | ⟨⟨hX0, hX1⟩, hY0, hY1⟩) | ⟨⟨hX0, hX1⟩, hY0, hY1⟩
    · by_cases c1 : o.1 + δ * a < p.1
      · by_cases c2 : p.1 < o.1 + δ * (a + 1)
        · by_cases c3 : o.2 + δ * b < p.2
          · by_cases c4 : p.2 < o.2 + δ * (b + 1)
            · exact absurd (Or.inl (Or.inl ⟨⟨c1, c2⟩, c3, c4⟩)) hN
            · by_cases d1 : o.1 + δ * (a + 1) - r ≤ p.1
              · apply e 10; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
                edge_tac
              · by_cases d2 : p.1 ≤ o.1 + δ * a + r
                · apply e 14; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
                  edge_tac
                · exact absurd (Or.inl (Or.inr ⟨⟨by linarith, by linarith⟩, by linarith,
                    by linarith⟩)) hN
          · by_cases d1 : p.1 ≤ o.1 + δ * a + r
            · apply e 0; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
              edge_tac
            · by_cases d2 : o.1 + δ * (a + 1) - r ≤ p.1
              · apply e 4; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
                edge_tac
              · exact absurd (Or.inl (Or.inr ⟨⟨by linarith, by linarith⟩, by linarith,
                  by linarith⟩)) hN
        · by_cases d1 : p.2 ≤ o.2 + δ * b + r
          · apply e 5; simp [notchedVertices, segment_vert, Set.mem_uIcc]
            edge_tac
          · by_cases d2 : o.2 + δ * (b + 1) - r ≤ p.2
            · apply e 9; simp [notchedVertices, segment_vert, Set.mem_uIcc]
              edge_tac
            · exact absurd (Or.inr ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩) hN
      · by_cases d1 : p.2 ≤ o.2 + δ * b + r
        · apply e 19; simp [notchedVertices, segment_vert, Set.mem_uIcc]
          edge_tac
        · by_cases d2 : o.2 + δ * (b + 1) - r ≤ p.2
          · apply e 15; simp [notchedVertices, segment_vert, Set.mem_uIcc]
            edge_tac
          · exact absurd (Or.inr ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩) hN
    · by_cases c1 : o.2 + δ * b - η < p.2
      · by_cases c2 : p.2 < o.2 + δ * (b + 1) + η
        · by_cases c3 : o.1 + δ * a + r < p.1
          · by_cases c4 : p.1 < o.1 + δ * (a + 1) - r
            · exact absurd (Or.inl (Or.inr ⟨⟨c3, c4⟩, c1, c2⟩)) hN
            · by_cases d1 : p.2 ≤ o.2 + δ * b
              · apply e 3; simp [notchedVertices, segment_vert, Set.mem_uIcc]
                edge_tac
              · by_cases d2 : o.2 + δ * (b + 1) ≤ p.2
                · apply e 11; simp [notchedVertices, segment_vert, Set.mem_uIcc]
                  edge_tac
                · exact absurd (Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, by linarith,
                    by linarith⟩)) hN
          · by_cases d1 : p.2 ≤ o.2 + δ * b
            · apply e 1; simp [notchedVertices, segment_vert, Set.mem_uIcc]
              edge_tac
            · by_cases d2 : o.2 + δ * (b + 1) ≤ p.2
              · apply e 13; simp [notchedVertices, segment_vert, Set.mem_uIcc]
                edge_tac
              · exact absurd (Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, by linarith,
                  by linarith⟩)) hN
        · apply e 12; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
          edge_tac
      · apply e 2; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
        edge_tac
    · by_cases c1 : o.1 + δ * a - η < p.1
      · by_cases c2 : p.1 < o.1 + δ * (a + 1) + η
        · by_cases c3 : o.2 + δ * b + r < p.2
          · by_cases c4 : p.2 < o.2 + δ * (b + 1) - r
            · exact absurd (Or.inr ⟨⟨c1, c2⟩, c3, c4⟩) hN
            · by_cases d1 : p.1 ≤ o.1 + δ * a
              · apply e 16; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
                edge_tac
              · by_cases d2 : o.1 + δ * (a + 1) ≤ p.1
                · apply e 8; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
                  edge_tac
                · exact absurd (Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, by linarith,
                    by linarith⟩)) hN
          · by_cases d1 : p.1 ≤ o.1 + δ * a
            · apply e 18; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
              edge_tac
            · by_cases d2 : o.1 + δ * (a + 1) ≤ p.1
              · apply e 6; simp [notchedVertices, segment_horiz, Set.mem_uIcc]
                edge_tac
              · exact absurd (Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, by linarith,
                  by linarith⟩)) hN
        · apply e 7; simp [notchedVertices, segment_vert, Set.mem_uIcc]
          edge_tac
      · apply e 17; simp [notchedVertices, segment_vert, Set.mem_uIcc]
        edge_tac
  · exact fun hp => notchedPoly_subset_frontier o hη hr h4 a b hp

set_option maxHeartbeats 4000000 in
theorem notchedVertices_injective (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : Function.Injective (notchedVertices o δ η r a b) := by
  have ha : δ * ((a : ℝ) + 1) = δ * a + δ := by ring
  have hb : δ * ((b : ℝ) + 1) = δ * b + δ := by ring
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (exfalso
       simp [notchedVertices, Prod.ext_iff] at h
       try casesm* _ ∧ _
       linarith)


set_option maxHeartbeats 8000000 in
theorem notchedVertices_edges (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : ∀ i j : Fin 20, i ≠ j →
      (((i.val + 1) % 20 = j.val ∨ (j.val + 1) % 20 = i.val) →
        segment ℝ (notchedVertices o δ η r a b i)
          (notchedVertices o δ η r a b ⟨(i.val + 1) % 20, Nat.mod_lt _ (Fin.pos i)⟩) ∩
          segment ℝ (notchedVertices o δ η r a b j)
            (notchedVertices o δ η r a b ⟨(j.val + 1) % 20, Nat.mod_lt _ (Fin.pos j)⟩) ⊆
            {notchedVertices o δ η r a b i, notchedVertices o δ η r a b j,
              notchedVertices o δ η r a b ⟨(i.val + 1) % 20, Nat.mod_lt _ (Fin.pos i)⟩}) ∧
      (¬ ((i.val + 1) % 20 = j.val ∨ (j.val + 1) % 20 = i.val) →
        Disjoint (segment ℝ (notchedVertices o δ η r a b i)
          (notchedVertices o δ η r a b ⟨(i.val + 1) % 20, Nat.mod_lt _ (Fin.pos i)⟩))
          (segment ℝ (notchedVertices o δ η r a b j)
            (notchedVertices o δ η r a b ⟨(j.val + 1) % 20, Nat.mod_lt _ (Fin.pos j)⟩))) := by
  have ha : δ * ((a : ℝ) + 1) = δ * a + δ := by ring
  have hb : δ * ((b : ℝ) + 1) = δ * b + δ := by ring
  intro i j hij
  refine ⟨fun hadj => ?_, fun hnadj => ?_⟩
  · rintro p ⟨h1, h2⟩
    fin_cases i <;> fin_cases j <;> simp at hadj hij <;>
      simp [notchedVertices, segment_vert, segment_horiz, Set.mem_uIcc, Prod.ext_iff] at h1 h2 ⊢ <;>
      casesm* _ ∧ _, _ ∨ _ <;>
      first
      | linarith
      | (left; constructor <;> linarith)
      | (right; constructor <;> linarith)
  · rw [Set.disjoint_left]
    intro p h1 h2
    fin_cases i <;> fin_cases j <;> simp at hnadj hij <;>
      simp [notchedVertices, segment_vert, segment_horiz, Set.mem_uIcc] at h1 h2 <;>
      casesm* _ ∧ _, _ ∨ _ <;> linarith

end HPC.Plane
