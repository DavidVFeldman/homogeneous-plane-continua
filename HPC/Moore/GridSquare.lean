import Mathlib

/-!
# A compact set with two families of grid lines of vanishing mesh is a square

Pure topology, used for the Schoenflies form of Moore 1919, Theorem E (batch 143, item B).

A *family of lines* in a compact set `K` of a metric space: indices `i` with positions
`t i ∈ [0, 1]`, and for each index two closed "half-planes" `L i` (the side towards position `0`)
and `R i` (the side towards position `1`) covering `K`, whose common part `L i ∩ R i` is the line.
Lines at smaller positions lie on the `L`-side of lines at larger positions.

A *grid* is two such families, crossing in single points, with the mesh of the boxes cut out by
finite subfamilies tending to `0`, and with one line of each family carrying an injective
parametrization compatible with the other family's positions. The theorem (`Grid.exists_square`):
`K` is homeomorphic to the closed unit square by a map sending positions to coordinates.
-/

namespace HPC.Sq

open Set Topology Metric Filter

section Top

variable {X : Type*} [TopologicalSpace X]

/-- A family of lines in `K`. -/
structure Family (ι : Type*) (K : Set X) where
  t : ι → ℝ
  L : ι → Set X
  R : ι → Set X
  i0 : ι
  i1 : ι
  t_mem : ∀ i, t i ∈ Icc (0 : ℝ) 1
  t_i0 : t i0 = 0
  t_i1 : t i1 = 1
  closedL : ∀ i, IsClosed (L i)
  closedR : ∀ i, IsClosed (R i)
  union : ∀ i, L i ∪ R i = K
  L_one : ∀ i, t i = 1 → L i = K
  R_zero : ∀ i, t i = 0 → R i = K
  mono : ∀ i j, t i < t j → L i ⊆ L j ∧ R j ⊆ R i ∧ Disjoint (L i) (R j)
  frontL : ∀ i, t i < 1 → L i ∩ R i ⊆ closure (K \ L i)
  frontR : ∀ i, 0 < t i → L i ∩ R i ⊆ closure (K \ R i)
  conn : ∀ i, IsPreconnected (L i ∩ R i)

namespace Family

variable {ι : Type*} {K : Set X} (F : Family ι K)

/-- The line of index `i`. -/
def line (i : ι) : Set X := F.L i ∩ F.R i

theorem L_sub (i : ι) : F.L i ⊆ K := fun _ h => F.union i ▸ Or.inl h
theorem R_sub (i : ι) : F.R i ⊆ K := fun _ h => F.union i ▸ Or.inr h

theorem mem_L_or_R {z : X} (hz : z ∈ K) (i : ι) : z ∈ F.L i ∨ z ∈ F.R i := by
  rw [← F.union i] at hz; exact hz

/-- Consecutive members of a finite set of indices. -/
def Consec (G : Finset ι) (j j' : ι) : Prop :=
  j ∈ G ∧ j' ∈ G ∧ F.t j < F.t j' ∧ ∀ l ∈ G, F.t l ≤ F.t j ∨ F.t j' ≤ F.t l

/-- Consecutive members around a value (strict on the right). -/
theorem exists_consec_lt (G : Finset ι) {a b : ι} (ha : a ∈ G) (hb : b ∈ G) {s : ℝ}
    (has : F.t a ≤ s) (hsb : s < F.t b) :
    ∃ j j', F.Consec G j j' ∧ F.t j ≤ s ∧ s < F.t j' := by
  classical
  obtain ⟨j, hj, hjmax⟩ := (G.filter fun l => F.t l ≤ s).exists_max_image F.t
    ⟨a, Finset.mem_filter.mpr ⟨ha, has⟩⟩
  obtain ⟨j', hj', hjmin⟩ := (G.filter fun l => s < F.t l).exists_min_image F.t
    ⟨b, Finset.mem_filter.mpr ⟨hb, hsb⟩⟩
  rw [Finset.mem_filter] at hj hj'
  refine ⟨j, j', ⟨hj.1, hj'.1, lt_of_le_of_lt hj.2 hj'.2, fun l hl => ?_⟩, hj.2, hj'.2⟩
  by_cases hls : F.t l ≤ s
  · exact Or.inl (hjmax l (Finset.mem_filter.mpr ⟨hl, hls⟩))
  · exact Or.inr (hjmin l (Finset.mem_filter.mpr ⟨hl, lt_of_not_ge hls⟩))

/-- Consecutive members around a value (strict on the left). -/
theorem exists_consec_lt' (G : Finset ι) {a b : ι} (ha : a ∈ G) (hb : b ∈ G) {s : ℝ}
    (has : F.t a < s) (hsb : s ≤ F.t b) :
    ∃ j j', F.Consec G j j' ∧ F.t j < s ∧ s ≤ F.t j' := by
  classical
  obtain ⟨j, hj, hjmax⟩ := (G.filter fun l => F.t l < s).exists_max_image F.t
    ⟨a, Finset.mem_filter.mpr ⟨ha, has⟩⟩
  obtain ⟨j', hj', hjmin⟩ := (G.filter fun l => s ≤ F.t l).exists_min_image F.t
    ⟨b, Finset.mem_filter.mpr ⟨hb, hsb⟩⟩
  rw [Finset.mem_filter] at hj hj'
  refine ⟨j, j', ⟨hj.1, hj'.1, lt_of_lt_of_le hj.2 hj'.2, fun l hl => ?_⟩, hj.2, hj'.2⟩
  by_cases hls : F.t l < s
  · exact Or.inl (hjmax l (Finset.mem_filter.mpr ⟨hl, hls⟩))
  · exact Or.inr (hjmin l (Finset.mem_filter.mpr ⟨hl, le_of_not_gt hls⟩))

/-- A point lies between two consecutive lines of any finite subfamily containing the two
extreme positions. -/
theorem exists_consec_mem (G : Finset ι) {a b : ι} (ha : a ∈ G) (hb : b ∈ G) (ha0 : F.t a = 0)
    (hb1 : F.t b = 1) {z : X} (hz : z ∈ K) :
    ∃ j j', F.Consec G j j' ∧ z ∈ F.R j ∧ z ∈ F.L j' := by
  classical
  obtain ⟨m', hm', hmin⟩ := (G.filter fun l => z ∈ F.L l).exists_min_image F.t
    ⟨b, Finset.mem_filter.mpr ⟨hb, (F.L_one b hb1).symm ▸ hz⟩⟩
  rw [Finset.mem_filter] at hm'
  rcases (F.t_mem m').1.eq_or_lt with h0 | hpos
  · -- `t m' = 0`: take `m'` and the next line
    obtain ⟨j, j', hc, hj, hj'⟩ := F.exists_consec_lt G hm'.1 hb (le_of_eq h0.symm)
      (show (0 : ℝ) < F.t b by rw [hb1]; exact one_pos)
    refine ⟨j, j', hc, ?_, ?_⟩
    · have : F.t j = 0 := le_antisymm (h0 ▸ hj) (F.t_mem j).1
      rw [F.R_zero j this]; exact hz
    · have hm'j' : F.t m' < F.t j' := h0 ▸ hj'
      exact (F.mono m' j' hm'j').1 hm'.2
  · obtain ⟨j, hj, hjmax⟩ := (G.filter fun l => F.t l < F.t m').exists_max_image F.t
      ⟨a, Finset.mem_filter.mpr ⟨ha, ha0 ▸ hpos⟩⟩
    rw [Finset.mem_filter] at hj
    refine ⟨j, m', ⟨hj.1, hm'.1, hj.2, fun l hl => ?_⟩, ?_, hm'.2⟩
    · by_cases hlt : F.t l < F.t m'
      · exact Or.inl (hjmax l (Finset.mem_filter.mpr ⟨hl, hlt⟩))
      · exact Or.inr (le_of_not_gt hlt)
    · rcases F.mem_L_or_R hz j with h | h
      · exact absurd (hmin j (Finset.mem_filter.mpr ⟨hj.1, h⟩)) (not_le.mpr hj.2)
      · exact h


/-- The predecessor of a member of a finite set of indices. -/
theorem exists_pred (G : Finset ι) {a i : ι} (ha : a ∈ G) (hi : i ∈ G) (hai : F.t a < F.t i) :
    ∃ j, F.Consec G j i := by
  classical
  obtain ⟨j, hj, hjmax⟩ := (G.filter fun l => F.t l < F.t i).exists_max_image F.t
    ⟨a, Finset.mem_filter.mpr ⟨ha, hai⟩⟩
  rw [Finset.mem_filter] at hj
  refine ⟨j, hj.1, hi, hj.2, fun l hl => ?_⟩
  by_cases hlt : F.t l < F.t i
  · exact Or.inl (hjmax l (Finset.mem_filter.mpr ⟨hl, hlt⟩))
  · exact Or.inr (le_of_not_gt hlt)

/-- The successor of a member of a finite set of indices. -/
theorem exists_succ (G : Finset ι) {b i : ι} (hb : b ∈ G) (hi : i ∈ G) (hib : F.t i < F.t b) :
    ∃ j, F.Consec G i j := by
  classical
  obtain ⟨j, hj, hjmin⟩ := (G.filter fun l => F.t i < F.t l).exists_min_image F.t
    ⟨b, Finset.mem_filter.mpr ⟨hb, hib⟩⟩
  rw [Finset.mem_filter] at hj
  refine ⟨j, hi, hj.1, hj.2, fun l hl => ?_⟩
  by_cases hlt : F.t i < F.t l
  · exact Or.inr (hjmin l (Finset.mem_filter.mpr ⟨hl, hlt⟩))
  · exact Or.inl (le_of_not_gt hlt)

theorem line_nonempty_of {ι' : Type*} (F' : Family ι' K)
    (hc : ∀ i k, (F.line i ∩ F'.line k).Nonempty) (i : ι) : (F.line i).Nonempty :=
  by obtain ⟨p, hp, -⟩ := hc i F'.i0; exact ⟨p, hp⟩


/-- Consecutive members around a value in `[0, 1]`. -/
theorem exists_consec_le (G : Finset ι) {a b : ι} (ha : a ∈ G) (hb : b ∈ G) (ha0 : F.t a = 0)
    (hb1 : F.t b = 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ j j', F.Consec G j j' ∧ F.t j ≤ s ∧ s ≤ F.t j' := by
  rcases hs.2.lt_or_eq with h | h
  · obtain ⟨j, j', hc, h1, h2⟩ := F.exists_consec_lt G ha hb (ha0 ▸ hs.1) (hb1 ▸ h)
    exact ⟨j, j', hc, h1, h2.le⟩
  · obtain ⟨j, j', hc, h1, h2⟩ := F.exists_consec_lt' G ha hb (by rw [ha0, h]; exact one_pos)
      (hb1 ▸ h.le)
    exact ⟨j, j', hc, h1.le, h2⟩

/-- Consecutive members around a given line. -/
theorem exists_consec_line (G : Finset ι) {a b k : ι} (ha : a ∈ G) (hb : b ∈ G) (hk : k ∈ G)
    (ha0 : F.t a = 0) (hb1 : F.t b = 1) :
    ∃ m m', F.Consec G m m' ∧ ∀ z ∈ F.line k, z ∈ F.R m ∧ z ∈ F.L m' := by
  rcases (F.t_mem k).2.lt_or_eq with h | h
  · obtain ⟨m', hc⟩ := F.exists_succ G hb hk (hb1 ▸ h)
    exact ⟨k, m', hc, fun z hz => ⟨hz.2, (F.mono k m' hc.2.2.1).1 hz.1⟩⟩
  · obtain ⟨m, hc⟩ := F.exists_pred G ha hk (by rw [ha0, h]; exact one_pos)
    exact ⟨m, k, hc, fun z hz => ⟨(F.mono m k hc.2.2.1).2.1 hz.2, hz.1⟩⟩

/-- The position of a point: the least position of a line on whose `R`-side... more precisely,
the infimum of the positions of the lines having the point on their `L`-side. -/
noncomputable def pos (z : X) : ℝ := sInf (F.t '' {i | z ∈ F.L i})

theorem mem_L_of_one {z : X} (hz : z ∈ K) {i : ι} (hi : F.t i = 1) : z ∈ F.L i := by
  rw [F.L_one i hi]; exact hz

theorem mem_R_of_zero {z : X} (hz : z ∈ K) {i : ι} (hi : F.t i = 0) : z ∈ F.R i := by
  rw [F.R_zero i hi]; exact hz

theorem pos_le {z : X} {i : ι} (h : z ∈ F.L i) : F.pos z ≤ F.t i :=
  csInf_le ⟨0, by rintro _ ⟨j, -, rfl⟩; exact (F.t_mem j).1⟩ ⟨i, h, rfl⟩

theorem le_pos {z : X} (hz : z ∈ K) {i : ι} (h : z ∈ F.R i) : F.t i ≤ F.pos z := by
  refine le_csInf ⟨1, F.i1, F.mem_L_of_one hz F.t_i1, F.t_i1⟩ ?_
  rintro _ ⟨j, hj, rfl⟩
  by_contra hlt
  exact disjoint_left.mp (F.mono j i (lt_of_not_ge hlt)).2.2 hj h

theorem pos_nonneg (z : X) : 0 ≤ F.pos z := by
  by_cases hne : (F.t '' {i | z ∈ F.L i}).Nonempty
  · exact le_csInf hne (by rintro _ ⟨j, -, rfl⟩; exact (F.t_mem j).1)
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [pos, hne, Real.sInf_empty]

theorem pos_le_one {z : X} (hz : z ∈ K) : F.pos z ≤ 1 := by
  have := F.pos_le (F.mem_L_of_one hz F.t_i1)
  rwa [F.t_i1] at this

theorem pos_eq_of_mem_line {z : X} (hz : z ∈ K) {i : ι} (h : z ∈ F.line i) : F.pos z = F.t i :=
  le_antisymm (F.pos_le h.1) (F.le_pos hz h.2)

end Family

/-- A point of the closure of `K − A` missing a closed set `B` is in the closure of
`K − (A ∪ B)`. -/
theorem mem_closure_diff_union {K A B : Set X} (hB : IsClosed B) {z : X} (hz : z ∈ closure (K \ A))
    (hzB : z ∉ B) : z ∈ closure (K \ (A ∪ B)) := by
  have := hB.isOpen_compl.inter_closure ⟨hzB, hz⟩
  refine closure_mono ?_ this
  rintro w ⟨hwB, hwK, hwA⟩
  exact ⟨hwK, fun h => h.elim hwA hwB⟩

/-- The open box cut out of `K` by two lines of each family. -/
def box {ιX ιY : Type*} {K : Set X} (FX : Family ιX K) (FY : Family ιY K) (j j' : ιX)
    (m m' : ιY) : Set X :=
  K \ (FX.L j ∪ FX.R j' ∪ FY.L m ∪ FY.R m')

/-- Two families of lines crossing in single points. -/
structure PreGrid (ιX ιY : Type*) (K : Set X) where
  FX : Family ιX K
  FY : Family ιY K
  cross_ne : ∀ i k, (FX.line i ∩ FY.line k).Nonempty
  cross_sub : ∀ i k, (FX.line i ∩ FY.line k).Subsingleton

namespace PreGrid

variable {ιX ιY : Type*} {K : Set X} (g : PreGrid ιX ιY K)

theorem box_swap (j j' : ιX) (m m' : ιY) : box g.FY g.FX m m' j j' = box g.FX g.FY j j' m m' := by
  ext z; simp only [box, mem_diff, mem_union]; tauto

/-- The pre-grid with the two families exchanged. -/
def swap : PreGrid ιY ιX K where
  FX := g.FY
  FY := g.FX
  cross_ne i k := by rw [inter_comm]; exact g.cross_ne k i
  cross_sub i k := by rw [inter_comm]; exact g.cross_sub k i

/-- **Localization.** A point between two consecutive lines of each family, not at a crossing of
the four, is in the closure of the box. -/
theorem mem_closure_box {j j' : ιX} {m m' : ιY} (hj : g.FX.t j < g.FX.t j')
    (hm : g.FY.t m < g.FY.t m') {z : X} (hz : z ∈ K) (h₁ : z ∈ g.FX.R j) (h₂ : z ∈ g.FX.L j')
    (h₃ : z ∈ g.FY.R m) (h₄ : z ∈ g.FY.L m')
    (hnc : (z ∉ g.FX.L j ∧ z ∉ g.FX.R j') ∨ (z ∉ g.FY.L m ∧ z ∉ g.FY.R m')) :
    z ∈ closure (box g.FX g.FY j j' m m') := by
  have hdX := (g.FX.mono j j' hj).2.2
  have hdY := (g.FY.mono m m' hm).2.2
  have hj1 : g.FX.t j < 1 := lt_of_lt_of_le hj (g.FX.t_mem j').2
  have hj0 : 0 < g.FX.t j' := lt_of_le_of_lt (g.FX.t_mem j).1 hj
  have hm1 : g.FY.t m < 1 := lt_of_lt_of_le hm (g.FY.t_mem m').2
  have hm0 : 0 < g.FY.t m' := lt_of_le_of_lt (g.FY.t_mem m).1 hm
  have cL := g.FX.closedL; have cR := g.FX.closedR
  have cL' := g.FY.closedL; have cR' := g.FY.closedR
  -- the four ways of reaching the box
  have e1 : ∀ A B C D : Set X, K \ (A ∪ B ∪ C ∪ D) = K \ (A ∪ B ∪ C ∪ D) := fun _ _ _ _ => rfl
  clear e1
  by_cases a₁ : z ∈ g.FX.L j
  · -- on the line `j`; then strictly between in the other family
    have hnY := hnc.resolve_left (fun h => h.1 a₁)
    have hzc := g.FX.frontL j hj1 ⟨a₁, h₁⟩
    have hR : z ∉ g.FX.R j' := fun h => disjoint_left.mp hdX a₁ h
    have := mem_closure_diff_union (cR j') hzc hR
    have := mem_closure_diff_union (cL' m) this hnY.1
    have := mem_closure_diff_union (cR' m') this hnY.2
    exact this
  by_cases a₂ : z ∈ g.FX.R j'
  · have hnY := hnc.resolve_left (fun h => h.2 a₂)
    have hzc := g.FX.frontR j' hj0 ⟨h₂, a₂⟩
    have := mem_closure_diff_union (cL j) hzc a₁
    have := mem_closure_diff_union (cL' m) this hnY.1
    have := mem_closure_diff_union (cR' m') this hnY.2
    refine closure_mono ?_ this
    intro w hw; simp only [box, mem_diff, mem_union] at hw ⊢; tauto
  by_cases a₃ : z ∈ g.FY.L m
  · have hzc := g.FY.frontL m hm1 ⟨a₃, h₃⟩
    have hR : z ∉ g.FY.R m' := fun h => disjoint_left.mp hdY a₃ h
    have := mem_closure_diff_union (cL j) hzc a₁
    have := mem_closure_diff_union (cR j') this a₂
    have := mem_closure_diff_union (cR' m') this hR
    refine closure_mono ?_ this
    intro w hw; simp only [box, mem_diff, mem_union] at hw ⊢; tauto
  by_cases a₄ : z ∈ g.FY.R m'
  · have hzc := g.FY.frontR m' hm0 ⟨h₄, a₄⟩
    have := mem_closure_diff_union (cL j) hzc a₁
    have := mem_closure_diff_union (cR j') this a₂
    have := mem_closure_diff_union (cL' m) this a₃
    refine closure_mono ?_ this
    intro w hw; simp only [box, mem_diff, mem_union] at hw ⊢; tauto
  refine subset_closure ⟨hz, ?_⟩
  simp only [mem_union]; tauto

/-- Each line of the first family has a point strictly between any two lines of the second. -/
theorem exists_line_between (i : ιX) {m m' : ιY} (hm : g.FY.t m < g.FY.t m') :
    ∃ p ∈ g.FX.line i, p ∉ g.FY.L m ∧ p ∉ g.FY.R m' := by
  by_contra h
  push_neg at h
  have hsub : g.FX.line i ⊆ g.FY.L m ∪ g.FY.R m' := fun p hp => by
    by_cases hpm : p ∈ g.FY.L m
    · exact Or.inl hpm
    · exact Or.inr (h p hp hpm)
  have hd := (g.FY.mono m m' hm).2.2
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp (g.FX.conn i) _ _ (g.FY.closedL m)
    (g.FY.closedR m') hsub (by
      rw [disjoint_iff_inter_eq_empty.mp hd, inter_empty]) with h' | h'
  · obtain ⟨p, hp, hp'⟩ := g.cross_ne i m'
    exact disjoint_left.mp hd (h' hp) hp'.2
  · obtain ⟨p, hp, hp'⟩ := g.cross_ne i m
    exact disjoint_left.mp hd hp'.1 (h' hp)

/-- The box between two lines of each family is nonempty. -/
theorem box_nonempty {j j' : ιX} {m m' : ιY} (hj : g.FX.t j < g.FX.t j')
    (hm : g.FY.t m < g.FY.t m') : (box g.FX g.FY j j' m m').Nonempty := by
  obtain ⟨p, hp, hpm, hpm'⟩ := g.exists_line_between j hm
  have hpK : p ∈ K := g.FX.L_sub j hp.1
  have := g.mem_closure_box hj hm hpK hp.2 ((g.FX.mono j j' hj).1 hp.1)
    ((g.FY.mem_L_or_R hpK m).resolve_left hpm) ((g.FY.mem_L_or_R hpK m').resolve_right hpm')
    (Or.inr ⟨hpm, hpm'⟩)
  exact closure_nonempty_iff.mp ⟨p, this⟩

end PreGrid

end Top

section Met

variable {X : Type*} [MetricSpace X]

/-- A *grid* in `K`: two families of lines crossing in single points, with parametrized lines and
mesh tending to `0`. -/
structure Grid (ιX ιY : Type*) (K : Set X) extends PreGrid ιX ιY K where
  φ : ℝ → X
  kφ : ιY
  φ_inj : InjOn φ (Icc 0 1)
  φ_line : ∀ s ∈ Icc (0 : ℝ) 1, φ s ∈ FY.line kφ
  φ_L : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, φ s ∈ FX.L i ↔ s ≤ FX.t i
  φ_R : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, φ s ∈ FX.R i ↔ FX.t i ≤ s
  ψ : ℝ → X
  iψ : ιX
  ψ_inj : InjOn ψ (Icc 0 1)
  ψ_line : ∀ s ∈ Icc (0 : ℝ) 1, ψ s ∈ FX.line iψ
  ψ_L : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, ψ s ∈ FY.L k ↔ s ≤ FY.t k
  ψ_R : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, ψ s ∈ FY.R k ↔ FY.t k ≤ s
  mesh : ∀ ε > 0, ∀ (i : ιX) (k : ιY), ∃ (G : Finset ιX) (H : Finset ιY), i ∈ G ∧ FX.i0 ∈ G ∧
    FX.i1 ∈ G ∧ k ∈ H ∧ FY.i0 ∈ H ∧ FY.i1 ∈ H ∧ ∀ j j', FX.Consec G j j' → ∀ m m',
      FY.Consec H m m' → ∀ z ∈ closure (box FX FY j j' m m'),
        ∀ w ∈ closure (box FX FY j j' m m'), dist z w ≤ ε

namespace Grid

variable {ιX ιY : Type*} {K : Set X} (g : Grid ιX ιY K)

/-- The grid with the two families exchanged. -/
def swap : Grid ιY ιX K where
  toPreGrid := g.toPreGrid.swap
  φ := g.ψ
  kφ := g.iψ
  φ_inj := g.ψ_inj
  φ_line := g.ψ_line
  φ_L := g.ψ_L
  φ_R := g.ψ_R
  ψ := g.φ
  iψ := g.kφ
  ψ_inj := g.φ_inj
  ψ_line := g.φ_line
  ψ_L := g.φ_L
  ψ_R := g.φ_R
  mesh ε hε i k := by
    obtain ⟨G, H, h1, h2, h3, h4, h5, h6, h⟩ := g.mesh ε hε k i
    refine ⟨H, G, h4, h5, h6, h1, h2, h3, fun j j' hj m m' hm z hz w hw => ?_⟩
    have hz' : z ∈ closure (box g.FX g.FY m m' j j') := by rw [← g.toPreGrid.box_swap]; exact hz
    have hw' : w ∈ closure (box g.FX g.FY m m' j j') := by rw [← g.toPreGrid.box_swap]; exact hw
    exact h m m' hm j j' hj z hz' w hw'

/-- **The limit lemma**, `R`-side: a point at the position of a line is on its `R`-side. -/
theorem mem_R_of_pos_eq {z : X} (hz : z ∈ K) {i : ιX} (h : g.FX.pos z = g.FX.t i) :
    z ∈ g.FX.R i := by
  by_contra hR
  have hL : z ∈ g.FX.L i := (g.FX.mem_L_or_R hz i).resolve_right hR
  have ht0 : 0 < g.FX.t i := by
    rcases (g.FX.t_mem i).1.eq_or_lt with e | e
    · exact absurd (g.FX.mem_R_of_zero hz e.symm) hR
    · exact e
  obtain ⟨p₀, hp₀⟩ := g.FX.line_nonempty_of g.FY g.cross_ne i
  have hd := (IsClosed.notMem_iff_infDist_pos (g.FX.closedR i) ⟨p₀, hp₀.2⟩).mp hR
  obtain ⟨G, H, hiG, h0G, -, -, h0H, h1H, hmesh⟩ := g.mesh _ (half_pos hd) i g.FY.i0
  obtain ⟨j, hc⟩ := g.FX.exists_pred G h0G hiG (by rw [g.FX.t_i0]; exact ht0)
  have hLj : z ∉ g.FX.L j := fun h' => by
    have := g.FX.pos_le h'; linarith [hc.2.2.1]
  have hRj : z ∈ g.FX.R j := (g.FX.mem_L_or_R hz j).resolve_left hLj
  obtain ⟨m, m', hcm, hzm, hzm'⟩ := g.FY.exists_consec_mem H h0H h1H g.FY.t_i0 g.FY.t_i1 hz
  have hzb := g.mem_closure_box hc.2.2.1 hcm.2.2.1 hz hRj hL hzm hzm' (Or.inl ⟨hLj, hR⟩)
  obtain ⟨p, hp, hpm, hpm'⟩ := g.exists_line_between i hcm.2.2.1
  have hpK : p ∈ K := g.FX.L_sub i hp.1
  have hpb := g.mem_closure_box hc.2.2.1 hcm.2.2.1 hpK ((g.FX.mono j i hc.2.2.1).2.1 hp.2) hp.1
    ((g.FY.mem_L_or_R hpK m).resolve_left hpm) ((g.FY.mem_L_or_R hpK m').resolve_right hpm')
    (Or.inr ⟨hpm, hpm'⟩)
  have h1 := hmesh j i hc m m' hcm z hzb p hpb
  have h2 := infDist_le_dist_of_mem (x := z) hp.2
  linarith

/-- **The limit lemma**, `L`-side. -/
theorem mem_L_of_pos_eq {z : X} (hz : z ∈ K) {i : ιX} (h : g.FX.pos z = g.FX.t i) :
    z ∈ g.FX.L i := by
  by_contra hL
  have hR : z ∈ g.FX.R i := (g.FX.mem_L_or_R hz i).resolve_left hL
  have ht1 : g.FX.t i < 1 := by
    rcases (g.FX.t_mem i).2.eq_or_lt with e | e
    · exact absurd (g.FX.mem_L_of_one hz e) hL
    · exact e
  obtain ⟨p₀, hp₀⟩ := g.FX.line_nonempty_of g.FY g.cross_ne i
  have hd := (IsClosed.notMem_iff_infDist_pos (g.FX.closedL i) ⟨p₀, hp₀.1⟩).mp hL
  obtain ⟨G, H, hiG, -, h1G, -, h0H, h1H, hmesh⟩ := g.mesh _ (half_pos hd) i g.FY.i0
  obtain ⟨j', hc⟩ := g.FX.exists_succ G h1G hiG (by rw [g.FX.t_i1]; exact ht1)
  have hRj : z ∉ g.FX.R j' := fun h' => by
    have := g.FX.le_pos hz h'; linarith [hc.2.2.1]
  have hLj : z ∈ g.FX.L j' := (g.FX.mem_L_or_R hz j').resolve_right hRj
  obtain ⟨m, m', hcm, hzm, hzm'⟩ := g.FY.exists_consec_mem H h0H h1H g.FY.t_i0 g.FY.t_i1 hz
  have hzb := g.mem_closure_box hc.2.2.1 hcm.2.2.1 hz hR hLj hzm hzm' (Or.inl ⟨hL, hRj⟩)
  obtain ⟨p, hp, hpm, hpm'⟩ := g.exists_line_between i hcm.2.2.1
  have hpK : p ∈ K := g.FX.L_sub i hp.1
  have hpb := g.mem_closure_box hc.2.2.1 hcm.2.2.1 hpK hp.2 ((g.FX.mono i j' hc.2.2.1).1 hp.1)
    ((g.FY.mem_L_or_R hpK m).resolve_left hpm) ((g.FY.mem_L_or_R hpK m').resolve_right hpm')
    (Or.inr ⟨hpm, hpm'⟩)
  have h1 := hmesh i j' hc m m' hcm z hzb p hpb
  have h2 := infDist_le_dist_of_mem (x := z) hp.1
  linarith

/-- **Density** of the positions of the lines. -/
theorem dense_t {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ i, a < g.FX.t i ∧ g.FX.t i < b := by
  by_contra h
  push_neg at h
  set s₁ := (2 * a + b) / 3
  set s₂ := (a + 2 * b) / 3
  have hs₁ : s₁ ∈ Icc (0 : ℝ) 1 := ⟨by simp only [s₁]; linarith, by simp only [s₁]; linarith⟩
  have hs₂ : s₂ ∈ Icc (0 : ℝ) 1 := ⟨by simp only [s₂]; linarith, by simp only [s₂]; linarith⟩
  have hne : g.φ s₁ ≠ g.φ s₂ := fun e => by
    have := g.φ_inj hs₁ hs₂ e; simp only [s₁, s₂] at this; linarith
  have hd : 0 < dist (g.φ s₁) (g.φ s₂) := dist_pos.mpr hne
  obtain ⟨G, H, -, h0G, h1G, hkH, h0H, h1H, hmesh⟩ := g.mesh _ (half_pos hd) g.FX.i0 g.kφ
  obtain ⟨j, j', hc, hj, hj'⟩ := g.FX.exists_consec_lt G h0G h1G (s := s₁)
    (by rw [g.FX.t_i0]; exact hs₁.1) (by rw [g.FX.t_i1]; simp only [s₁]; linarith)
  have hja : g.FX.t j ≤ a := by
    by_contra h'; have := h j (lt_of_not_ge h'); simp only [s₁] at hj; linarith
  have hjb : b ≤ g.FX.t j' := h j' (by simp only [s₁] at hj'; linarith)
  obtain ⟨m, m', hcm, hm⟩ := g.FY.exists_consec_line H h0H h1H hkH g.FY.t_i0 g.FY.t_i1
  have key : ∀ s ∈ Icc (0 : ℝ) 1, a < s → s < b →
      g.φ s ∈ closure (box g.FX g.FY j j' m m') := fun s hs has hsb => by
    have hK : g.φ s ∈ K := g.FY.L_sub _ (g.φ_line s hs).1
    have hl := hm _ (g.φ_line s hs)
    refine g.mem_closure_box hc.2.2.1 hcm.2.2.1 hK ((g.φ_R s hs j).mpr (by linarith))
      ((g.φ_L s hs j').mpr (by linarith)) hl.1 hl.2 (Or.inl ⟨fun h' => ?_, fun h' => ?_⟩)
    · have := (g.φ_L s hs j).mp h'; linarith
    · have := (g.φ_R s hs j').mp h'; linarith
  have := hmesh j j' hc m m' hcm _ (key s₁ hs₁ (by simp only [s₁]; linarith)
    (by simp only [s₁]; linarith)) _ (key s₂ hs₂ (by simp only [s₂]; linarith)
    (by simp only [s₂]; linarith))
  linarith

/-- Positions of lines approximate every point of `[0, 1]`. -/
theorem exists_t_near {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ i, |g.FX.t i - s| < ε := by
  obtain ⟨i, h1, h2⟩ := g.dense_t (a := max 0 (s - ε / 2)) (b := min 1 (s + ε / 2))
    (le_max_left _ _) (by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      refine ⟨⟨one_pos, by linarith [hs.1]⟩, by linarith [hs.2], by linarith⟩)
    (min_le_left _ _)
  refine ⟨i, abs_lt.mpr ⟨?_, ?_⟩⟩
  · have := le_max_right 0 (s - ε / 2); linarith
  · have := min_le_right 1 (s + ε / 2); linarith

/-- **Continuity** of the position on `K`. -/
theorem continuousOn_pos : ContinuousOn g.FX.pos K := by
  intro z hz
  rw [ContinuousWithinAt, tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact eventually_nhdsWithin_of_forall fun w _ => lt_of_lt_of_le ha0 (g.FX.pos_nonneg w)
    obtain ⟨j, hj1, hj2⟩ := g.dense_t (le_of_not_gt ha0) ha (g.FX.pos_le_one hz)
    have hzL : z ∉ g.FX.L j := fun h => by have := g.FX.pos_le h; linarith
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((g.FX.closedL j).isOpen_compl.mem_nhds hzL),
      self_mem_nhdsWithin] with w hw hwK
    have := g.FX.le_pos hwK ((g.FX.mem_L_or_R hwK j).resolve_left hw)
    linarith
  · intro a ha
    by_cases ha1 : 1 < a
    · exact eventually_nhdsWithin_of_forall fun w hw => lt_of_le_of_lt (g.FX.pos_le_one hw) ha1
    have hne : (g.FX.t '' {i | z ∈ g.FX.L i}).Nonempty :=
      ⟨_, g.FX.i1, g.FX.mem_L_of_one hz g.FX.t_i1, rfl⟩
    obtain ⟨_, ⟨i, hi, rfl⟩, hia⟩ := exists_lt_of_csInf_lt hne ha
    obtain ⟨j, hj1, hj2⟩ := g.dense_t (g.FX.t_mem i).1 hia (le_of_not_gt ha1)
    have hzR : z ∉ g.FX.R j := fun h => disjoint_left.mp (g.FX.mono i j hj1).2.2 hi h
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((g.FX.closedR j).isOpen_compl.mem_nhds hzR),
      self_mem_nhdsWithin] with w hw hwK
    have := g.FX.pos_le ((g.FX.mem_L_or_R hwK j).resolve_right hw)
    linarith

/-- A point of `K` lies between the consecutive lines around its position. -/
theorem mem_between {j j' : ιX} {z : X} (hz : z ∈ K)
    (hj : g.FX.t j ≤ g.FX.pos z) (hj' : g.FX.pos z ≤ g.FX.t j') :
    z ∈ g.FX.R j ∧ z ∈ g.FX.L j' := by
  constructor
  · by_contra h
    have hL := (g.FX.mem_L_or_R hz j).resolve_right h
    exact h (g.mem_R_of_pos_eq hz (le_antisymm (g.FX.pos_le hL) hj))
  · by_contra h
    have hR := (g.FX.mem_L_or_R hz j').resolve_left h
    exact h (g.mem_L_of_pos_eq hz (le_antisymm hj' (g.FX.le_pos hz hR)))

/-- Off the positions of lines, a point is strictly between the lines around it. -/
theorem strict_between {j j' : ιX} {z : X} (hz : z ∈ K) (hn : ∀ i, g.FX.t i ≠ g.FX.pos z)
    (hR : z ∈ g.FX.R j) (hL : z ∈ g.FX.L j') : z ∉ g.FX.L j ∧ z ∉ g.FX.R j' :=
  ⟨fun h => hn j (g.FX.pos_eq_of_mem_line hz ⟨h, hR⟩).symm,
    fun h => hn j' (g.FX.pos_eq_of_mem_line hz ⟨hL, h⟩).symm⟩

/-- **Injectivity** of the pair of positions. -/
theorem eq_of_pos_eq {z w : X} (hz : z ∈ K) (hw : w ∈ K) (hX : g.FX.pos z = g.FX.pos w)
    (hY : g.FY.pos z = g.FY.pos w) : z = w := by
  by_cases hA : (∃ i, g.FX.t i = g.FX.pos z) ∧ ∃ k, g.FY.t k = g.FY.pos z
  · obtain ⟨⟨i, hi⟩, ⟨k, hk⟩⟩ := hA
    exact g.cross_sub i k
      ⟨⟨g.mem_L_of_pos_eq hz hi.symm, g.mem_R_of_pos_eq hz hi.symm⟩,
        ⟨g.swap.mem_L_of_pos_eq hz hk.symm, g.swap.mem_R_of_pos_eq hz hk.symm⟩⟩
      ⟨⟨g.mem_L_of_pos_eq hw (hX ▸ hi.symm), g.mem_R_of_pos_eq hw (hX ▸ hi.symm)⟩,
        ⟨g.swap.mem_L_of_pos_eq hw (hY ▸ hk.symm), g.swap.mem_R_of_pos_eq hw (hY ▸ hk.symm)⟩⟩
  by_contra hne
  have hd : 0 < dist z w := dist_pos.mpr hne
  obtain ⟨G, H, -, h0G, h1G, -, h0H, h1H, hmesh⟩ := g.mesh _ (half_pos hd) g.FX.i0 g.FY.i0
  obtain ⟨j, j', hc, hj, hj'⟩ := g.FX.exists_consec_le G h0G h1G g.FX.t_i0 g.FX.t_i1
    ⟨g.FX.pos_nonneg z, g.FX.pos_le_one hz⟩
  obtain ⟨m, m', hcm, hm, hm'⟩ := g.FY.exists_consec_le H h0H h1H g.FY.t_i0 g.FY.t_i1
    ⟨g.FY.pos_nonneg z, g.FY.pos_le_one hz⟩
  have bz := g.mem_between hz hj hj'
  have bw := g.mem_between hw (hX ▸ hj) (hX ▸ hj')
  have bz' := g.swap.mem_between hz hm hm'
  have bw' := g.swap.mem_between hw (hY ▸ hm) (hY ▸ hm')
  have hnc : ∀ u ∈ K, g.FX.pos u = g.FX.pos z → g.FY.pos u = g.FY.pos z →
      u ∈ g.FX.R j → u ∈ g.FX.L j' → u ∈ g.FY.R m → u ∈ g.FY.L m' →
      (u ∉ g.FX.L j ∧ u ∉ g.FX.R j') ∨ (u ∉ g.FY.L m ∧ u ∉ g.FY.R m') := by
    intro u hu hux huy h1 h2 h3 h4
    rw [not_and_or, not_exists, not_exists] at hA
    rcases hA with hA | hA
    · exact Or.inl (g.strict_between hu (fun i e => hA i (e.trans hux)) h1 h2)
    · exact Or.inr (g.swap.strict_between hu (fun k e => hA k (e.trans huy)) h3 h4)
  have hzb := g.mem_closure_box hc.2.2.1 hcm.2.2.1 hz bz.1 bz.2 bz'.1 bz'.2
    (hnc z hz rfl rfl bz.1 bz.2 bz'.1 bz'.2)
  have hwb := g.mem_closure_box hc.2.2.1 hcm.2.2.1 hw bw.1 bw.2 bw'.1 bw'.2
    (hnc w hw hX.symm hY.symm bw.1 bw.2 bw'.1 bw'.2)
  have := hmesh j j' hc m m' hcm z hzb w hwb
  linarith

/-- The image of `K` under the pair of positions is the square. -/
theorem image_pos (hK : IsCompact K) :
    (fun z => (g.FY.pos z, g.FX.pos z)) '' K = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  apply subset_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨g.FY.pos_nonneg z, g.FY.pos_le_one hz⟩, ⟨g.FX.pos_nonneg z, g.FX.pos_le_one hz⟩⟩
  have hc : IsClosed ((fun z => (g.FY.pos z, g.FX.pos z)) '' K) :=
    (hK.image_of_continuousOn (g.swap.continuousOn_pos.prodMk g.continuousOn_pos)).isClosed
  rintro ⟨u, s⟩ ⟨hu, hs⟩
  refine hc.closure_subset_iff.mpr subset_rfl (Metric.mem_closure_iff.mpr fun ε hε => ?_)
  obtain ⟨k, hk⟩ := g.swap.exists_t_near hu hε
  obtain ⟨i, hi⟩ := g.exists_t_near hs hε
  obtain ⟨c, hci, hck⟩ := g.cross_ne i k
  have hcK : c ∈ K := g.FX.L_sub i hci.1
  refine ⟨_, ⟨c, hcK, rfl⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  dsimp only
  rw [g.FY.pos_eq_of_mem_line hcK hck, g.FX.pos_eq_of_mem_line hcK hci, abs_sub_comm u,
    abs_sub_comm s]
  exact ⟨hk, hi⟩

end Grid

/-- **A compact grid is a square.** If `K` is compact and carries a grid, there is an embedding of
the closed unit square onto `K` sending the side `p.1 = 0` onto the first line of the second
family, `p.1 = 1` onto its last line, `p.2 = 0` onto the first line of the first family and
`p.2 = 1` onto its last line. -/
theorem Grid.exists_square {ιX ιY : Type*} {K : Set X} (g : Grid ιX ιY K) (hK : IsCompact K) :
    ∃ f : unitInterval × unitInterval → X, IsEmbedding f ∧ range f = K ∧
      ∀ p, (((p.1 : ℝ) = 0 ↔ f p ∈ g.FY.L g.FY.i0) ∧ ((p.1 : ℝ) = 1 ↔ f p ∈ g.FY.R g.FY.i1) ∧
        ((p.2 : ℝ) = 0 ↔ f p ∈ g.FX.L g.FX.i0) ∧ ((p.2 : ℝ) = 1 ↔ f p ∈ g.FX.R g.FX.i1)) := by
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
  refine ⟨Subtype.val ∘ h.symm, IsEmbedding.subtypeVal.comp h.symm.isEmbedding, ?_, fun p => ?_⟩
  · rw [range_comp, h.symm.range_coe, image_univ, Subtype.range_coe]
  have hp : Φ (h.symm p) = p := h.apply_symm_apply p
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

end Met

end HPC.Sq
