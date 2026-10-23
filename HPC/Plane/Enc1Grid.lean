import HPC.Plane.JanPoly

/-!
# Batch 130, grid part: unions of closed grid squares, their boundary edges, and the frontier

For an arbitrary finite index set `S` of grid squares of mesh `δ > 0` (offset `0`):
`sqUnion δ S` is the union of the squares, `bdryOf δ S` the set of grid edges belonging to exactly
one square of `S`, oriented lexicographically. The main facts:

* `isProper_bdryOf`: `bdryOf δ S` is a proper graph;
* `mem_frontier_sqUnion_iff`, `mem_graphSet_bdryOf_iff`: a point is in the frontier of the union,
  resp. on a boundary edge, iff it lies in a square of `S` and in a square not in `S`; hence
  `frontier_sqUnion : frontier (sqUnion δ S) = graphSet (bdryOf δ S)`;
* `mem_interior_sqUnion`: a point all of whose squares are in `S` is interior.
-/

namespace HPC.Plane

open Set Metric

/-- The closed grid square of index `(a, b)` and mesh `δ` (offset `0`): `gridSq 0 δ a b`. -/
abbrev gsq (δ : ℝ) (a b : ℤ) : Set Pt := gridSq 0 δ a b

theorem mem_gsq {δ : ℝ} {a b : ℤ} {z : Pt} :
    z ∈ gsq δ a b ↔ (δ * a ≤ z.1 ∧ z.1 ≤ δ * (a + 1)) ∧ (δ * b ≤ z.2 ∧ z.2 ≤ δ * (b + 1)) := by
  simp only [gsq, gridSq, Set.mem_prod, Set.mem_Icc, Prod.fst_zero, Prod.snd_zero, zero_add]

theorem isCompact_gsq (δ : ℝ) (a b : ℤ) : IsCompact (gsq δ a b) := by
  unfold gsq gridSq
  exact isCompact_Icc.prod isCompact_Icc

/-! #### Integer bookkeeping -/

theorem int_le_of_mul_le {δ : ℝ} (hδ : 0 < δ) {m n : ℤ} (h : δ * m ≤ δ * n) : m ≤ n := by
  have : (m : ℝ) ≤ n := le_of_mul_le_mul_left h hδ
  exact_mod_cast this

theorem int_lt_of_mul_lt {δ : ℝ} (hδ : 0 < δ) {m n : ℤ} (h : δ * m < δ * n) : m < n := by
  have : (m : ℝ) < n := lt_of_mul_lt_mul_left h hδ.le
  exact_mod_cast this

/-- Two grid intervals containing a common point have indices differing by at most one. -/
theorem idx_close {δ : ℝ} (hδ : 0 < δ) {a a' : ℤ} {t : ℝ} (h1 : δ * a ≤ t) (h2 : t ≤ δ * (a + 1))
    (h3 : δ * a' ≤ t) (h4 : t ≤ δ * (a' + 1)) : a ≤ a' + 1 ∧ a' ≤ a + 1 :=
  ⟨int_le_of_mul_le hδ (by push_cast; linarith), int_le_of_mul_le hδ (by push_cast; linarith)⟩

/-- A point strictly inside a grid interval lies in no other closed grid interval. -/
theorem idx_eq_of_strict {δ : ℝ} (hδ : 0 < δ) {a a' : ℤ} {t : ℝ} (h1 : δ * a < t)
    (h2 : t < δ * (a + 1)) (h3 : δ * a' ≤ t) (h4 : t ≤ δ * (a' + 1)) : a' = a := by
  have k1 : a' < a + 1 := int_lt_of_mul_lt hδ (by push_cast; linarith)
  have k2 : a < a' + 1 := int_lt_of_mul_lt hδ (by push_cast; linarith)
  omega

/-! #### The union of a finite set of squares -/

/-- The union of the grid squares with indices in `S`. -/
def sqUnion (δ : ℝ) (S : Finset (ℤ × ℤ)) : Set Pt := ⋃ ab ∈ S, gsq δ ab.1 ab.2

theorem mem_sqUnion {δ : ℝ} {S : Finset (ℤ × ℤ)} {z : Pt} :
    z ∈ sqUnion δ S ↔ ∃ a b : ℤ, (a, b) ∈ S ∧ z ∈ gsq δ a b := by
  simp [sqUnion]

theorem isCompact_sqUnion (δ : ℝ) (S : Finset (ℤ × ℤ)) : IsCompact (sqUnion δ S) :=
  S.isCompact_biUnion fun ab _ => isCompact_gsq δ ab.1 ab.2

/-- **Covering**: a neighbourhood of `z` is covered by the squares containing `z` (1-D form). -/
theorem exists_nbhd_cover_1d {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ r > 0, ∀ s : ℝ, |s - t| < r → ∃ a : ℤ, (δ * a ≤ t ∧ t ≤ δ * (a + 1)) ∧
      (δ * a ≤ s ∧ s ≤ δ * (a + 1)) := by
  set a0 := ⌊t / δ⌋
  have k1 : δ * a0 ≤ t := by
    have := Int.floor_le (t / δ)
    rw [le_div_iff₀ hδ] at this
    linarith
  have k2 : t < δ * (a0 + 1) := by
    have := Int.lt_floor_add_one (t / δ)
    rw [div_lt_iff₀ hδ] at this
    linarith
  rcases k1.lt_or_eq with k1 | k1
  · refine ⟨min (t - δ * a0) (δ * (a0 + 1) - t), lt_min (by linarith) (by linarith),
      fun s hs => ⟨a0, ⟨k1.le, k2.le⟩, ?_⟩⟩
    rw [abs_lt] at hs
    have := min_le_left (t - δ * a0) (δ * (a0 + 1) - t)
    have := min_le_right (t - δ * a0) (δ * (a0 + 1) - t)
    constructor <;> linarith
  · refine ⟨δ, hδ, fun s hs => ?_⟩
    rw [abs_lt] at hs
    rcases le_or_gt t s with h | h
    · exact ⟨a0, ⟨k1.le, k2.le⟩, by constructor <;> linarith⟩
    · refine ⟨a0 - 1, ?_, ?_⟩ <;> push_cast <;> constructor <;> linarith

theorem exists_nbhd_cover {δ : ℝ} (hδ : 0 < δ) (z : Pt) :
    ∃ r > 0, ∀ p ∈ ball z r, ∃ a b : ℤ, z ∈ gsq δ a b ∧ p ∈ gsq δ a b := by
  obtain ⟨r1, hr1, h1⟩ := exists_nbhd_cover_1d hδ z.1
  obtain ⟨r2, hr2, h2⟩ := exists_nbhd_cover_1d hδ z.2
  refine ⟨min r1 r2, lt_min hr1 hr2, fun p hp => ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hp
  obtain ⟨a, ha1, ha2⟩ := h1 p.1 (lt_of_lt_of_le hp.1 (min_le_left _ _))
  obtain ⟨b, hb1, hb2⟩ := h2 p.2 (lt_of_lt_of_le hp.2 (min_le_right _ _))
  exact ⟨a, b, mem_gsq.2 ⟨ha1, hb1⟩, mem_gsq.2 ⟨ha2, hb2⟩⟩

/-- A point all of whose squares are in `S` is interior to the union. -/
theorem mem_interior_sqUnion {δ : ℝ} (hδ : 0 < δ) {S : Finset (ℤ × ℤ)} {z : Pt}
    (h : ∀ a b : ℤ, z ∈ gsq δ a b → (a, b) ∈ S) : z ∈ interior (sqUnion δ S) := by
  obtain ⟨r, hr, hcov⟩ := exists_nbhd_cover hδ z
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨r, hr, fun p hp => ?_⟩
  obtain ⟨a, b, hz, hp⟩ := hcov p hp
  exact mem_sqUnion.2 ⟨a, b, h a b hz, hp⟩

/-- Points strictly inside a square of index not in `S`, arbitrarily close to any point of the
closed square, lie outside the union. -/
theorem exists_near_not_mem {δ : ℝ} (hδ : 0 < δ) {S : Finset (ℤ × ℤ)} {a b : ℤ}
    (hab : (a, b) ∉ S) {z : Pt} (hz : z ∈ gsq δ a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ ball z ε, p ∉ sqUnion δ S := by
  rw [mem_gsq] at hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  set t := min (1 / 2) (ε / (2 * δ)) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have ht2 : t * δ ≤ ε / 2 := by
    have := min_le_right (1 / 2 : ℝ) (ε / (2 * δ))
    calc t * δ ≤ ε / (2 * δ) * δ := by gcongr
      _ = ε / 2 := by field_simp
  set c : Pt := (δ * (a + 1 / 2), δ * (b + 1 / 2))
  set p : Pt := ((1 - t) * z.1 + t * c.1, (1 - t) * z.2 + t * c.2)
  have hp1 : δ * a < p.1 ∧ p.1 < δ * (a + 1) := by
    simp only [p, c]; constructor <;> nlinarith
  have hp2 : δ * b < p.2 ∧ p.2 < δ * (b + 1) := by
    simp only [p, c]; constructor <;> nlinarith
  refine ⟨p, ?_, ?_⟩
  · rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    simp only [p, c]
    constructor
    · rw [abs_lt]; constructor <;> nlinarith
    · rw [abs_lt]; constructor <;> nlinarith
  · intro hpQ
    obtain ⟨a', b', hS, hp⟩ := mem_sqUnion.1 hpQ
    rw [mem_gsq] at hp
    obtain rfl := idx_eq_of_strict hδ hp1.1 hp1.2 hp.1.1 hp.1.2
    obtain rfl := idx_eq_of_strict hδ hp2.1 hp2.2 hp.2.1 hp.2.2
    exact hab hS

/-- **The frontier of a union of squares**: the points lying in a square of `S` and in a square
not in `S`. -/
theorem mem_frontier_sqUnion_iff {δ : ℝ} (hδ : 0 < δ) {S : Finset (ℤ × ℤ)} {z : Pt} :
    z ∈ frontier (sqUnion δ S) ↔ ∃ a b a' b' : ℤ, (a, b) ∈ S ∧ (a', b') ∉ S ∧
      z ∈ gsq δ a b ∧ z ∈ gsq δ a' b' := by
  rw [frontier, (isCompact_sqUnion δ S).isClosed.closure_eq]
  constructor
  · rintro ⟨hzQ, hzi⟩
    obtain ⟨a, b, hab, hz⟩ := mem_sqUnion.1 hzQ
    by_contra hcon
    push_neg at hcon
    exact hzi (mem_interior_sqUnion hδ fun a' b' hz' => by
      by_contra h'
      exact hcon a b a' b' hab h' hz hz')
  · rintro ⟨a, b, a', b', hab, hab', hz, hz'⟩
    refine ⟨mem_sqUnion.2 ⟨a, b, hab, hz⟩, fun hint => ?_⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨ε, hε, hball⟩ := hint
    obtain ⟨p, hp, hpQ⟩ := exists_near_not_mem hδ hab' hz' hε
    exact hpQ (hball hp)

/-! #### Grid edges -/

/-- The horizontal grid edge from `(δa, δb)` to `(δ(a+1), δb)`. -/
def hseg (δ : ℝ) (a b : ℤ) : Seg := ((δ * a, δ * b), (δ * (a + 1), δ * b))

/-- The vertical grid edge from `(δa, δb)` to `(δa, δ(b+1))`. -/
def vseg (δ : ℝ) (a b : ℤ) : Seg := ((δ * a, δ * b), (δ * a, δ * (b + 1)))

theorem mem_segSet_hseg {δ : ℝ} (hδ : 0 < δ) {a b : ℤ} {z : Pt} :
    z ∈ segSet (hseg δ a b) ↔ (δ * a ≤ z.1 ∧ z.1 ≤ δ * (a + 1)) ∧ z.2 = δ * b := by
  unfold segSet hseg
  rw [← Prod.image_mk_segment_left, segment_eq_Icc (by nlinarith)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, h2⟩
    exact ⟨z.1, hx, by ext <;> simp [h2]⟩

theorem mem_segSet_vseg {δ : ℝ} (hδ : 0 < δ) {a b : ℤ} {z : Pt} :
    z ∈ segSet (vseg δ a b) ↔ z.1 = δ * a ∧ (δ * b ≤ z.2 ∧ z.2 ≤ δ * (b + 1)) := by
  unfold segSet vseg
  rw [← Prod.image_mk_segment_right, segment_eq_Icc (by nlinarith)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩
  · rintro ⟨h1, hx⟩
    exact ⟨z.2, hx, by ext <;> simp [h1]⟩

/-- A grid segment: horizontal or vertical. -/
def IsGridSeg (δ : ℝ) (s : Seg) : Prop := (∃ a b : ℤ, s = hseg δ a b) ∨ ∃ a b : ℤ, s = vseg δ a b

theorem IsGridSeg.lex_lt {δ : ℝ} (hδ : 0 < δ) {s : Seg} (hs : IsGridSeg δ s) :
    toLex s.1 < toLex s.2 := by
  rcases hs with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · rw [Prod.Lex.lt_iff]
    left
    simp only [hseg, ofLex_toLex]
    linarith
  · rw [Prod.Lex.lt_iff]
    right
    simp only [vseg, ofLex_toLex]
    refine ⟨by simp, ?_⟩
    linarith

/-- Intersections of two grid edges. -/
theorem gridSeg_inter {δ : ℝ} (hδ : 0 < δ) {s t : Seg} (hs : IsGridSeg δ s) (ht : IsGridSeg δ t)
    (hst : s ≠ t) : segSet s ∩ segSet t ⊆ ({s.1, s.2} : Set Pt) ∩ ({t.1, t.2} : Set Pt) := by
  rintro z ⟨hzs, hzt⟩
  rcases hs with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ <;> rcases ht with ⟨a', b', rfl⟩ | ⟨a', b', rfl⟩
  · rw [mem_segSet_hseg hδ] at hzs hzt
    have hb : b = b' := le_antisymm (int_le_of_mul_le hδ (by linarith)) (int_le_of_mul_le hδ
      (by linarith))
    subst hb
    have hab := idx_close hδ hzs.1.1 hzs.1.2 hzt.1.1 hzt.1.2
    have hne : a ≠ a' := fun h => hst (by rw [h])
    rcases lt_or_gt_of_ne hne with h | h
    · have e : a' = a + 1 := by omega
      subst e
      have : z.1 = δ * ((a : ℝ) + 1) := by push_cast at hzt; linarith [hzs.1.2, hzt.1.1]
      have hz : z = (δ * ((a : ℝ) + 1), δ * b) := Prod.ext this hzs.2
      simp [hseg, hz]
    · have e : a = a' + 1 := by omega
      subst e
      have : z.1 = δ * ((a' : ℝ) + 1) := by push_cast at hzs; linarith [hzs.1.1, hzt.1.2]
      have hz : z = (δ * ((a' : ℝ) + 1), δ * b) := Prod.ext this hzs.2
      simp [hseg, hz]
  · rw [mem_segSet_hseg hδ] at hzs
    rw [mem_segSet_vseg hδ] at hzt
    have h1 := idx_close hδ (t := z.1) hzs.1.1 hzs.1.2 (by rw [hzt.1]) (by rw [hzt.1]; linarith)
    have h2 := idx_close hδ (t := z.2) hzt.2.1 hzt.2.2 (by rw [hzs.2]) (by rw [hzs.2]; linarith)
    have hz : z = (δ * a', δ * b) := Prod.ext hzt.1 hzs.2
    have ha : a' = a ∨ a' = a + 1 := by
      rcases (show a' = a ∨ a' = a + 1 ∨ a' + 1 = a by omega) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; have := hzs.1.1; rw [hzt.1] at this
        have : a ≤ a' := int_le_of_mul_le hδ this
        omega
    have hb : b = b' ∨ b = b' + 1 := by
      rcases (show b = b' ∨ b = b' + 1 ∨ b + 1 = b' by omega) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; have := hzt.2.1; rw [hzs.2] at this
        have : b' ≤ b := int_le_of_mul_le hδ this
        omega
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hseg, vseg, hz]
  · rw [mem_segSet_vseg hδ] at hzs
    rw [mem_segSet_hseg hδ] at hzt
    have hz : z = (δ * a, δ * b') := Prod.ext hzs.1 hzt.2
    have ha : a = a' ∨ a = a' + 1 := by
      have := idx_close hδ (t := z.1) hzt.1.1 hzt.1.2 (by rw [hzs.1]) (by rw [hzs.1]; linarith)
      rcases (show a = a' ∨ a = a' + 1 ∨ a + 1 = a' by omega) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; have := hzt.1.1; rw [hzs.1] at this
        have : a' ≤ a := int_le_of_mul_le hδ this
        omega
    have hb : b' = b ∨ b' = b + 1 := by
      have := idx_close hδ (t := z.2) hzs.2.1 hzs.2.2 (by rw [hzt.2]) (by rw [hzt.2]; linarith)
      rcases (show b' = b ∨ b' = b + 1 ∨ b' + 1 = b by omega) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; have := hzs.2.1; rw [hzt.2] at this
        have : b ≤ b' := int_le_of_mul_le hδ this
        omega
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hseg, vseg, hz]
  · rw [mem_segSet_vseg hδ] at hzs hzt
    have ha : a = a' := le_antisymm (int_le_of_mul_le hδ (by linarith)) (int_le_of_mul_le hδ
      (by linarith))
    subst ha
    have hab := idx_close hδ hzs.2.1 hzs.2.2 hzt.2.1 hzt.2.2
    have hne : b ≠ b' := fun h => hst (by rw [h])
    rcases lt_or_gt_of_ne hne with h | h
    · have e : b' = b + 1 := by omega
      subst e
      have : z.2 = δ * ((b : ℝ) + 1) := by push_cast at hzt; linarith [hzs.2.2, hzt.2.1]
      have hz : z = (δ * a, δ * ((b : ℝ) + 1)) := Prod.ext hzs.1 this
      simp [vseg, hz]
    · have e : b = b' + 1 := by omega
      subst e
      have : z.2 = δ * ((b' : ℝ) + 1) := by push_cast at hzs; linarith [hzs.2.1, hzt.2.2]
      have hz : z = (δ * a, δ * ((b' : ℝ) + 1)) := Prod.ext hzs.1 this
      simp [vseg, hz]

/-- **Any finite set of grid edges of one mesh is a proper graph.** -/
theorem isProper_of_gridSeg {δ : ℝ} (hδ : 0 < δ) {G : Finset Seg} (hG : ∀ s ∈ G, IsGridSeg δ s) :
    IsProper G := by
  refine ⟨fun s hs h => ?_, fun s hs t ht hne h => ?_, fun s hs t ht hne => ?_⟩
  · have := (hG s hs).lex_lt hδ
    rw [h] at this
    exact lt_irrefl _ this
  · have := eq_of_segment_eq_lex ((hG s hs).lex_lt hδ) ((hG t ht).lex_lt hδ) h
    exact hne (Prod.ext this.1 this.2)
  · exact gridSeg_inter hδ (hG s hs) (hG t ht) (fun h => hne (by rw [h]))

/-! #### The boundary edges -/

open Classical in
/-- **The boundary graph of a union of squares**: the grid edges belonging to exactly one square
of `S` (a horizontal edge `hseg δ a b` belongs to the squares `(a, b)` and `(a, b - 1)`, a
vertical edge `vseg δ a b` to `(a, b)` and `(a - 1, b)`). -/
noncomputable def bdryOf (δ : ℝ) (S : Finset (ℤ × ℤ)) : Finset Seg :=
  ((S ∪ S.image fun ab => (ab.1, ab.2 + 1)).filter
      (fun ab => Xor' (ab ∈ S) ((ab.1, ab.2 - 1) ∈ S))).image (fun ab => hseg δ ab.1 ab.2) ∪
  ((S ∪ S.image fun ab => (ab.1 + 1, ab.2)).filter
      (fun ab => Xor' (ab ∈ S) ((ab.1 - 1, ab.2) ∈ S))).image (fun ab => vseg δ ab.1 ab.2)

theorem mem_bdryOf {δ : ℝ} {S : Finset (ℤ × ℤ)} {s : Seg} :
    s ∈ bdryOf δ S ↔ (∃ a b : ℤ, Xor' ((a, b) ∈ S) ((a, b - 1) ∈ S) ∧ s = hseg δ a b) ∨
      (∃ a b : ℤ, Xor' ((a, b) ∈ S) ((a - 1, b) ∈ S) ∧ s = vseg δ a b) := by
  classical
  unfold bdryOf
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro (⟨a, b, ⟨-, hx⟩, rfl⟩ | ⟨a, b, ⟨-, hx⟩, rfl⟩)
    · exact Or.inl ⟨a, b, hx, rfl⟩
    · exact Or.inr ⟨a, b, hx, rfl⟩
  · rintro (⟨a, b, hx, rfl⟩ | ⟨a, b, hx, rfl⟩)
    · refine Or.inl ⟨a, b, ⟨?_, hx⟩, rfl⟩
      rcases hx with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, b - 1, h, by simp⟩
    · refine Or.inr ⟨a, b, ⟨?_, hx⟩, rfl⟩
      rcases hx with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨a - 1, b, h, by simp⟩

theorem isProper_bdryOf {δ : ℝ} (hδ : 0 < δ) (S : Finset (ℤ × ℤ)) : IsProper (bdryOf δ S) :=
  isProper_of_gridSeg hδ fun s hs => by
    rcases mem_bdryOf.1 hs with ⟨a, b, -, rfl⟩ | ⟨a, b, -, rfl⟩
    · exact Or.inl ⟨a, b, rfl⟩
    · exact Or.inr ⟨a, b, rfl⟩

/-- Two squares of one column containing `z`, one in `S`, one not: `z` is on a boundary edge. -/
theorem mem_graphSet_bdryOf_col {δ : ℝ} (hδ : 0 < δ) {S : Finset (ℤ × ℤ)} {a b b' : ℤ} {z : Pt}
    (hz : z ∈ gsq δ a b) (hz' : z ∈ gsq δ a b') (hb : (a, b) ∈ S) (hb' : (a, b') ∉ S) :
    z ∈ graphSet (bdryOf δ S) := by
  rw [mem_gsq] at hz hz'
  have hne : b ≠ b' := fun h => hb' (h ▸ hb)
  have hc := idx_close hδ hz.2.1 hz.2.2 hz'.2.1 hz'.2.2
  rcases lt_or_gt_of_ne hne with h | h
  · obtain rfl : b' = b + 1 := by omega
    refine mem_graphSet.2 ⟨hseg δ a (b + 1), mem_bdryOf.2 (Or.inl ⟨a, b + 1, ?_, rfl⟩), ?_⟩
    · simp only [add_sub_cancel_right]
      exact Or.inr ⟨hb, hb'⟩
    · rw [mem_segSet_hseg hδ]
      refine ⟨hz.1, ?_⟩
      push_cast at hz' ⊢
      linarith [hz.2.2, hz'.2.1]
  · obtain rfl : b = b' + 1 := by omega
    refine mem_graphSet.2 ⟨hseg δ a (b' + 1), mem_bdryOf.2 (Or.inl ⟨a, b' + 1, ?_, rfl⟩), ?_⟩
    · simp only [add_sub_cancel_right]
      exact Or.inl ⟨hb, hb'⟩
    · rw [mem_segSet_hseg hδ]
      refine ⟨hz.1, ?_⟩
      push_cast at hz ⊢
      linarith [hz.2.1, hz'.2.2]

/-- Two squares of one row containing `z`, one in `S`, one not: `z` is on a boundary edge. -/
theorem mem_graphSet_bdryOf_row {δ : ℝ} (hδ : 0 < δ) {S : Finset (ℤ × ℤ)} {a a' b : ℤ} {z : Pt}
    (hz : z ∈ gsq δ a b) (hz' : z ∈ gsq δ a' b) (ha : (a, b) ∈ S) (ha' : (a', b) ∉ S) :
    z ∈ graphSet (bdryOf δ S) := by
  rw [mem_gsq] at hz hz'
  have hne : a ≠ a' := fun h => ha' (h ▸ ha)
  have hc := idx_close hδ hz.1.1 hz.1.2 hz'.1.1 hz'.1.2
  rcases lt_or_gt_of_ne hne with h | h
  · obtain rfl : a' = a + 1 := by omega
    refine mem_graphSet.2 ⟨vseg δ (a + 1) b, mem_bdryOf.2 (Or.inr ⟨a + 1, b, ?_, rfl⟩), ?_⟩
    · simp only [add_sub_cancel_right]
      exact Or.inr ⟨ha, ha'⟩
    · rw [mem_segSet_vseg hδ]
      refine ⟨?_, hz.2⟩
      push_cast at hz' ⊢
      linarith [hz.1.2, hz'.1.1]
  · obtain rfl : a = a' + 1 := by omega
    refine mem_graphSet.2 ⟨vseg δ (a' + 1) b, mem_bdryOf.2 (Or.inr ⟨a' + 1, b, ?_, rfl⟩), ?_⟩
    · simp only [add_sub_cancel_right]
      exact Or.inl ⟨ha, ha'⟩
    · rw [mem_segSet_vseg hδ]
      refine ⟨?_, hz.2⟩
      push_cast at hz ⊢
      linarith [hz.1.1, hz'.1.2]

/-- **Boundary edges** carry exactly the points lying in a square of `S` and in a square not in
`S`. -/
theorem mem_graphSet_bdryOf_iff {δ : ℝ} (hδ : 0 < δ) {S : Finset (ℤ × ℤ)} {z : Pt} :
    z ∈ graphSet (bdryOf δ S) ↔ ∃ a b a' b' : ℤ, (a, b) ∈ S ∧ (a', b') ∉ S ∧
      z ∈ gsq δ a b ∧ z ∈ gsq δ a' b' := by
  constructor
  · intro hz
    obtain ⟨s, hs, hzs⟩ := mem_graphSet.1 hz
    rcases mem_bdryOf.1 hs with ⟨a, b, hx, rfl⟩ | ⟨a, b, hx, rfl⟩
    · rw [mem_segSet_hseg hδ] at hzs
      have h1 : z ∈ gsq δ a b := mem_gsq.2 ⟨hzs.1, by rw [hzs.2], by rw [hzs.2]; linarith⟩
      have h2 : z ∈ gsq δ a (b - 1) := mem_gsq.2 ⟨hzs.1, by rw [hzs.2]; push_cast; linarith,
        by rw [hzs.2]; push_cast; linarith⟩
      rcases hx with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact ⟨a, b, a, b - 1, hx, hy, h1, h2⟩
      · exact ⟨a, b - 1, a, b, hx, hy, h2, h1⟩
    · rw [mem_segSet_vseg hδ] at hzs
      have h1 : z ∈ gsq δ a b := mem_gsq.2 ⟨⟨by rw [hzs.1], by rw [hzs.1]; linarith⟩, hzs.2⟩
      have h2 : z ∈ gsq δ (a - 1) b := mem_gsq.2 ⟨⟨by rw [hzs.1]; push_cast; linarith,
        by rw [hzs.1]; push_cast; linarith⟩, hzs.2⟩
      rcases hx with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact ⟨a, b, a - 1, b, hx, hy, h1, h2⟩
      · exact ⟨a - 1, b, a, b, hx, hy, h2, h1⟩
  · rintro ⟨a, b, a', b', hab, hab', hz, hz'⟩
    have hmid : z ∈ gsq δ a' b := mem_gsq.2 ⟨(mem_gsq.1 hz').1, (mem_gsq.1 hz).2⟩
    by_cases hm : (a', b) ∈ S
    · exact mem_graphSet_bdryOf_col hδ hmid hz' hm hab'
    · exact mem_graphSet_bdryOf_row hδ hz hmid hab hm

/-- **The frontier of a union of squares is its boundary graph.** -/
theorem frontier_sqUnion {δ : ℝ} (hδ : 0 < δ) (S : Finset (ℤ × ℤ)) :
    frontier (sqUnion δ S) = graphSet (bdryOf δ S) := by
  ext z
  rw [mem_frontier_sqUnion_iff hδ, mem_graphSet_bdryOf_iff hδ]

end HPC.Plane
