import Mathlib

/-!
# Matching covers give a homeomorphism (Bing 1948, Theorem 11)

Two compact sets in metric spaces, each equipped with a sequence of finite indexed open
covers with summable mesh, such that "intersection at consecutive levels on one side forces
closeness on the other", are homeomorphic. Moreover the homeomorphism carries any point
tracked by a common index sequence on one side to the point tracked by it on the other.

No chains appear. This is the engine of Bing's uniqueness theorem for the pseudo-arc and of
Bing–Jones's uniqueness of the circle of pseudo-arcs.

English proof: COMMISSION.md §3 of the batch-2 commission. All statements are proved; the
file contains no `sorry`.
-/

namespace HPC

open Set Metric

section Fattening

variable {X : Type*} [MetricSpace X]

/-- The tail sum `ε i + ε (i+1) + ⋯`. -/
noncomputable def tail (ε : ℕ → ℝ) (i : ℕ) : ℝ := ∑' l, ε (i + l)

/-- Bing's fattening radius at level `i`: `ε i + 2 (ε (i+1) + ε (i+2) + ⋯)`. -/
noncomputable def rad (ε : ℕ → ℝ) (i : ℕ) : ℝ := ε i + 2 * tail ε (i + 1)

/-- The open `δ`-thickening of `S`, written `y` in Bing. -/
def fat (S : Set X) (δ : ℝ) : Set X := Metric.thickening δ S

/-- The shifted sequence `l ↦ ε (i + l)` is summable. -/
theorem summable_shift (ε : ℕ → ℝ) (hsum : Summable ε) (i : ℕ) :
    Summable fun l => ε (i + l) := by
  have := (summable_nat_add_iff (f := ε) i).mpr hsum
  simpa [Nat.add_comm] using this

/-- Splitting the first term off a tail sum. -/
theorem tail_succ (ε : ℕ → ℝ) (hsum : Summable ε) (i : ℕ) :
    tail ε i = ε i + tail ε (i + 1) := by
  have h := (summable_shift ε hsum i).tsum_eq_zero_add
  simp only [tail]
  rw [h]
  simp [Nat.add_comm, Nat.add_left_comm]

theorem tail_nonneg (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (i : ℕ) : 0 ≤ tail ε i :=
  tsum_nonneg fun _ => (hε _).le

theorem tail_tendsto_zero (ε : ℕ → ℝ) :
    Filter.Tendsto (tail ε) Filter.atTop (nhds 0) := by
  simpa [tail, Nat.add_comm] using tendsto_sum_nat_add ε

theorem rad_eq (ε : ℕ → ℝ) (hsum : Summable ε) (i : ℕ) :
    rad ε i = ε i + 2 * ε (i + 1) + 2 * tail ε (i + 2) := by
  rw [rad, tail_succ ε hsum (i + 1)]
  ring

/-- Positivity of the radius. (The summability hypothesis of the commissioned statement is
not needed and is named with a leading underscore.) -/
theorem rad_pos (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (_hsum : Summable ε) (i : ℕ) : 0 < rad ε i := by
  have := tail_nonneg ε hε (i + 1)
  have := hε i
  simp only [rad]
  linarith

theorem rad_nonneg (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hsum : Summable ε) (i : ℕ) : 0 ≤ rad ε i :=
  (rad_pos ε hε hsum i).le

/-- The radius tends to zero. (Positivity of `ε` is not needed and is named with a leading
underscore.) -/
theorem rad_tendsto_zero (ε : ℕ → ℝ) (_hε : ∀ i, 0 < ε i) (hsum : Summable ε) :
    Filter.Tendsto (rad ε) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto ε Filter.atTop (nhds 0) := hsum.tendsto_atTop_zero
  have h2 : Filter.Tendsto (fun i => tail ε (i + 1)) Filter.atTop (nhds 0) :=
    (tail_tendsto_zero ε).comp (Filter.tendsto_add_atTop_nat 1)
  have := h1.add (h2.const_mul (2 : ℝ))
  simpa [rad] using this

theorem subset_fat (S : Set X) {δ : ℝ} (hδ : 0 < δ) : S ⊆ fat S δ :=
  Metric.self_subset_thickening hδ S

theorem isOpen_fat (S : Set X) (δ : ℝ) : IsOpen (fat S δ) := Metric.isOpen_thickening

theorem isBounded_fat {S : Set X} (hS : Bornology.IsBounded S) (δ : ℝ) :
    Bornology.IsBounded (fat S δ) := hS.thickening

theorem mem_fat_iff {S : Set X} {δ : ℝ} {x : X} : x ∈ fat S δ ↔ ∃ z ∈ S, dist x z < δ :=
  Metric.mem_thickening_iff

/-- `diam (fat S δ) ≤ diam S + 2δ`. (The boundedness hypothesis of the commissioned statement
turns out to be unnecessary and is named with a leading underscore.) -/
theorem diam_fat_le (S : Set X) (_hS : Bornology.IsBounded S) {δ : ℝ} (hδ : 0 ≤ δ) :
    Metric.diam (fat S δ) ≤ Metric.diam S + 2 * δ :=
  Metric.diam_thickening_le S hδ

/-- **The nesting lemma.** If `B` has diameter `≤ ε (i+1)`, and some point of `B` is within
`ε i` of some point of `A`, then the closure of `fat B (rad ε (i+1))` lies in
`fat A (rad ε i)`. This is the one computation in Bing's proof. -/
theorem closure_fat_subset_fat (ε : ℕ → ℝ) (_hε : ∀ i, 0 < ε i) (hsum : Summable ε) (i : ℕ)
    {A B : Set X} (hB : Bornology.IsBounded B) (hdiam : Metric.diam B ≤ ε (i + 1))
    (hclose : ∃ p ∈ B, ∃ q ∈ A, dist p q < ε i) :
    closure (fat B (rad ε (i + 1))) ⊆ fat A (rad ε i) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hclose
  intro z hz
  -- the slack in `dist p q < ε i`
  set η : ℝ := ε i - dist p q with hηdef
  have hη : 0 < η := by simp only [hηdef]; linarith
  obtain ⟨z', hz', hzz'⟩ := Metric.mem_closure_iff.mp hz η hη
  obtain ⟨b', hb', hz'b'⟩ := mem_fat_iff.mp hz'
  have hb'p : dist b' p ≤ ε (i + 1) :=
    le_trans (Metric.dist_le_diam_of_mem hB hb' hp) hdiam
  have hkey : rad ε (i + 1) + ε (i + 1) + ε i = rad ε i := by
    rw [rad_eq ε hsum i, rad]
    ring
  have : dist z q ≤ dist z z' + dist z' b' + dist b' p + dist p q := by
    calc dist z q ≤ dist z b' + dist b' q := dist_triangle _ _ _
      _ ≤ (dist z z' + dist z' b') + (dist b' p + dist p q) := by
          gcongr <;> [exact dist_triangle _ _ _; exact dist_triangle _ _ _]
      _ = dist z z' + dist z' b' + dist b' p + dist p q := by ring
  refine mem_fat_iff.mpr ⟨q, hq, ?_⟩
  have : dist z q < η + rad ε (i + 1) + ε (i + 1) + dist p q := by linarith
  simp only [hηdef] at this
  linarith

/-- The mesh bound at level `i`: every fattened element of level `i` has diameter at most
`mesh ε i`, and `mesh ε i → 0`. -/
noncomputable def mesh (ε : ℕ → ℝ) (i : ℕ) : ℝ := ε i + 2 * rad ε i

theorem diam_fat_le_mesh {S : Set X} (hS : Bornology.IsBounded S) (ε : ℕ → ℝ)
    (hε : ∀ i, 0 < ε i) (hsum : Summable ε) {i : ℕ} (hdiam : Metric.diam S ≤ ε i) :
    Metric.diam (fat S (rad ε i)) ≤ mesh ε i :=
  le_trans (diam_fat_le S hS (rad_nonneg ε hε hsum i)) (by simp only [mesh]; linarith)

theorem mesh_tendsto_zero (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hsum : Summable ε) :
    Filter.Tendsto (mesh ε) Filter.atTop (nhds 0) := by
  have := hsum.tendsto_atTop_zero.add ((rad_tendsto_zero ε hε hsum).const_mul (2 : ℝ))
  simpa [mesh] using this

/-- For every `δ > 0` there are arbitrarily late levels with mesh below `δ`. -/
theorem exists_mesh_lt (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hsum : Summable ε) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) : ∃ j, m < j ∧ mesh ε j < δ := by
  have h := (mesh_tendsto_zero ε hε hsum).eventually (eventually_lt_nhds hδ)
  obtain ⟨j, hj, hjm⟩ := ((h.and (Filter.eventually_gt_atTop m)).exists)
  exact ⟨j, hjm, hj⟩

/-- Two points at mutual distance at most every mesh coincide. -/
theorem eq_of_forall_dist_le_mesh (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    {q q' : X} (h : ∀ i, dist q q' ≤ mesh ε i) : q = q' := by
  by_contra hne
  obtain ⟨j, -, hj⟩ := exists_mesh_lt ε hε hsum (dist_pos.mpr hne) 0
  exact absurd (h j) (not_le.mpr hj)

end Fattening

section Matching

variable {X₁ X₂ : Type*} [MetricSpace X₁] [MetricSpace X₂]

/-- The data of Bing's Theorem 11: for `n = 1, 2`, a sequence of finite indexed open covers
of `Mₙ`, both sides indexed by `Fin (N i)` at level `i`, with the four conditions. -/
structure MatchingCovers (M₁ : Set X₁) (M₂ : Set X₂) (ε : ℕ → ℝ) where
  N : ℕ → ℕ
  x₁ : (i : ℕ) → Fin (N i) → Set X₁
  x₂ : (i : ℕ) → Fin (N i) → Set X₂
  open₁ : ∀ i k, IsOpen (x₁ i k)
  open₂ : ∀ i k, IsOpen (x₂ i k)
  /-- (1) each level covers. -/
  cover₁ : ∀ i, M₁ ⊆ ⋃ k, x₁ i k
  cover₂ : ∀ i, M₂ ⊆ ⋃ k, x₂ i k
  /-- (2) each element meets the space. -/
  meet₁ : ∀ i k, (x₁ i k ∩ M₁).Nonempty
  meet₂ : ∀ i k, (x₂ i k ∩ M₂).Nonempty
  /-- (3) elements are bounded with diameter at most `ε i`. Boundedness is stated separately
  because `Metric.diam` of an unbounded set is `0`. -/
  bdd₁ : ∀ i k, Bornology.IsBounded (x₁ i k)
  bdd₂ : ∀ i k, Bornology.IsBounded (x₂ i k)
  diam₁ : ∀ i k, Metric.diam (x₁ i k) ≤ ε i
  diam₂ : ∀ i k, Metric.diam (x₂ i k) ≤ ε i
  /-- (4) if the `j`-th element of level `i+1` meets the `k`-th element of level `i` on one
  side, the corresponding elements on the other side are within `ε i`. Both directions. -/
  match₁ : ∀ i (j : Fin (N (i + 1))) (k : Fin (N i)),
    (x₁ (i + 1) j ∩ x₁ i k).Nonempty → ∃ p ∈ x₂ (i + 1) j, ∃ q ∈ x₂ i k, dist p q < ε i
  match₂ : ∀ i (j : Fin (N (i + 1))) (k : Fin (N i)),
    (x₂ (i + 1) j ∩ x₂ i k).Nonempty → ∃ p ∈ x₁ (i + 1) j, ∃ q ∈ x₁ i k, dist p q < ε i

variable {M₁ : Set X₁} {M₂ : Set X₂} {ε : ℕ → ℝ}

/-- An index sequence `a` *tracks* a point `p` on side 1 if `p ∈ x₁ i (a i)` for every `i`. -/
def MatchingCovers.Tracks₁ (C : MatchingCovers M₁ M₂ ε) (a : (i : ℕ) → Fin (C.N i)) (p : X₁) :
    Prop := ∀ i, p ∈ C.x₁ i (a i)

def MatchingCovers.Tracks₂ (C : MatchingCovers M₁ M₂ ε) (a : (i : ℕ) → Fin (C.N i)) (q : X₂) :
    Prop := ∀ i, q ∈ C.x₂ i (a i)

namespace MatchingCovers

/-- Exchanging the roles of the two sides. All side-1 statements below are obtained from the
side-2 ones by applying them to `C.swap`. -/
def swap (C : MatchingCovers M₁ M₂ ε) : MatchingCovers M₂ M₁ ε where
  N := C.N
  x₁ := C.x₂
  x₂ := C.x₁
  open₁ := C.open₂
  open₂ := C.open₁
  cover₁ := C.cover₂
  cover₂ := C.cover₁
  meet₁ := C.meet₂
  meet₂ := C.meet₁
  bdd₁ := C.bdd₂
  bdd₂ := C.bdd₁
  diam₁ := C.diam₂
  diam₂ := C.diam₁
  match₁ := C.match₂
  match₂ := C.match₁

/-- Bing's `y(1,i)_k`: the cover element `x₁ i k` fattened by `rad ε i`. -/
noncomputable def y₁ (C : MatchingCovers M₁ M₂ ε) (i : ℕ) (k : Fin (C.N i)) : Set X₁ :=
  fat (C.x₁ i k) (rad ε i)

/-- Bing's `y(2,i)_k`: the cover element `x₂ i k` fattened by `rad ε i`. -/
noncomputable def y₂ (C : MatchingCovers M₁ M₂ ε) (i : ℕ) (k : Fin (C.N i)) : Set X₂ :=
  fat (C.x₂ i k) (rad ε i)

theorem x₂_subset_y₂ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (i : ℕ) (k : Fin (C.N i)) : C.x₂ i k ⊆ C.y₂ i k :=
  subset_fat _ (rad_pos ε hε hsum i)

theorem x₁_subset_y₁ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (i : ℕ) (k : Fin (C.N i)) : C.x₁ i k ⊆ C.y₁ i k :=
  C.swap.x₂_subset_y₂ hε hsum i k

/-- Any two points in the closure of a fattened element of level `i` are at distance at most
`mesh ε i`. -/
theorem dist_le_mesh₂ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    {i : ℕ} {k : Fin (C.N i)} {q q' : X₂}
    (hq : q ∈ closure (C.y₂ i k)) (hq' : q' ∈ closure (C.y₂ i k)) : dist q q' ≤ mesh ε i := by
  have hb : Bornology.IsBounded (closure (C.y₂ i k)) :=
    (isBounded_fat (C.bdd₂ i k) (rad ε i)).closure
  have h := Metric.dist_le_diam_of_mem hb hq hq'
  rw [Metric.diam_closure] at h
  exact h.trans (diam_fat_le_mesh (C.bdd₂ i k) ε hε hsum (C.diam₂ i k))

theorem dist_le_mesh₁ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    {i : ℕ} {k : Fin (C.N i)} {p p' : X₁}
    (hp : p ∈ closure (C.y₁ i k)) (hp' : p' ∈ closure (C.y₁ i k)) : dist p p' ≤ mesh ε i :=
  C.swap.dist_le_mesh₂ hε hsum hp hp'

/-- **Step 1.** If two elements of consecutive levels meet on side 1, the corresponding
fattened elements on side 2 are nested: the closure of the later one lies in the earlier one. -/
theorem step1₂ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    {i : ℕ} {s : Fin (C.N (i + 1))} {r : Fin (C.N i)}
    (h : (C.x₁ (i + 1) s ∩ C.x₁ i r).Nonempty) : closure (C.y₂ (i + 1) s) ⊆ C.y₂ i r :=
  closure_fat_subset_fat ε hε hsum i (C.bdd₂ _ _) (C.diam₂ _ _) (C.match₁ i s r h)

theorem step1₁ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    {i : ℕ} {s : Fin (C.N (i + 1))} {r : Fin (C.N i)}
    (h : (C.x₂ (i + 1) s ∩ C.x₂ i r).Nonempty) : closure (C.y₁ (i + 1) s) ⊆ C.y₁ i r :=
  C.swap.step1₂ hε hsum h

/-- **Step 2.** If an element of level `i` and one of a later level `j` meet in a point of `M₁`,
the corresponding fattened elements on side 2 are nested. -/
theorem step2₂ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε) (i j : ℕ) :
    ∀ (_ : i < j) (r : Fin (C.N i)) (s : Fin (C.N j)),
      (C.x₁ i r ∩ C.x₁ j s ∩ M₁).Nonempty → closure (C.y₂ j s) ⊆ C.y₂ i r := by
  induction j with
  | zero => intro hij; omega
  | succ m ih =>
    intro hij r s hne
    obtain ⟨c, ⟨hcr, hcs⟩, hcM⟩ := hne
    rcases Nat.lt_or_ge i m with him | him
    · obtain ⟨t, ht⟩ : ∃ t, c ∈ C.x₁ m t := Set.mem_iUnion.mp (C.cover₁ m hcM)
      have h1 : closure (C.y₂ (m + 1) s) ⊆ C.y₂ m t := C.step1₂ hε hsum ⟨c, hcs, ht⟩
      have h2 : closure (C.y₂ m t) ⊆ C.y₂ i r := ih him r t ⟨c, ⟨hcr, ht⟩, hcM⟩
      exact h1.trans (subset_closure.trans h2)
    · have him' : i = m := by omega
      subst him'
      exact C.step1₂ hε hsum ⟨c, hcs, hcr⟩

theorem step2₁ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (i j : ℕ) (hij : i < j) (r : Fin (C.N i)) (s : Fin (C.N j))
    (h : (C.x₂ i r ∩ C.x₂ j s ∩ M₂).Nonempty) : closure (C.y₁ j s) ⊆ C.y₁ i r :=
  C.swap.step2₂ hε hsum i j hij r s h

/-- A choice of index sequence tracking a given point of `M₁`. -/
noncomputable def trackSeq (C : MatchingCovers M₁ M₂ ε) {p : X₁} (hp : p ∈ M₁) (i : ℕ) :
    Fin (C.N i) :=
  (Set.mem_iUnion.mp (C.cover₁ i hp)).choose

theorem mem_trackSeq (C : MatchingCovers M₁ M₂ ε) {p : X₁} (hp : p ∈ M₁) (i : ℕ) :
    p ∈ C.x₁ i (C.trackSeq hp i) :=
  (Set.mem_iUnion.mp (C.cover₁ i hp)).choose_spec

/-- **Step 4.** For an index sequence whose consecutive elements meet, the nested sequence of
closed sets `closure (y₂ i (a i)) ∩ M₂` has a point in common. -/
theorem exists_limit_point (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₂ : IsCompact M₂) (a : (i : ℕ) → Fin (C.N i))
    (ha : ∀ i, (C.x₁ (i + 1) (a (i + 1)) ∩ C.x₁ i (a i)).Nonempty) :
    ∃ q, q ∈ M₂ ∧ ∀ i, q ∈ closure (C.y₂ i (a i)) := by
  set t : ℕ → Set X₂ := fun i => closure (C.y₂ i (a i)) ∩ M₂
  have hsub : ∀ i, t (i + 1) ⊆ t i := by
    intro i
    exact Set.inter_subset_inter_left _
      ((C.step1₂ hε hsum (ha i)).trans subset_closure)
  have hne : ∀ i, (t i).Nonempty := by
    intro i
    obtain ⟨c, hc1, hc2⟩ := C.meet₂ i (a i)
    exact ⟨c, subset_closure (C.x₂_subset_y₂ hε hsum i (a i) hc1), hc2⟩
  have hclosed : ∀ i, IsClosed (t i) := fun i => isClosed_closure.inter hM₂.isClosed
  have hcpt : IsCompact (t 0) := hM₂.inter_left isClosed_closure
  obtain ⟨q, hq⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hsub hne hcpt hclosed
  have hq' : ∀ i, q ∈ t i := Set.mem_iInter.mp hq
  exact ⟨q, (hq' 0).2, fun i => (hq' i).1⟩

/-- **Steps 4 and 5.** Bing's map `T`, defined on points of `M₁` via a chosen tracking
sequence. -/
noncomputable def toFun (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₂ : IsCompact M₂) (p : M₁) : X₂ :=
  (C.exists_limit_point hε hsum hM₂ (C.trackSeq p.2)
    (fun i => ⟨p.1, C.mem_trackSeq p.2 (i + 1), C.mem_trackSeq p.2 i⟩)).choose

theorem toFun_mem (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₂ : IsCompact M₂) (p : M₁) : C.toFun hε hsum hM₂ p ∈ M₂ :=
  (C.exists_limit_point hε hsum hM₂ (C.trackSeq p.2)
    (fun i => ⟨p.1, C.mem_trackSeq p.2 (i + 1), C.mem_trackSeq p.2 i⟩)).choose_spec.1

theorem toFun_spec (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₂ : IsCompact M₂) (p : M₁) (i : ℕ) :
    C.toFun hε hsum hM₂ p ∈ closure (C.y₂ i (C.trackSeq p.2 i)) :=
  (C.exists_limit_point hε hsum hM₂ (C.trackSeq p.2)
    (fun i => ⟨p.1, C.mem_trackSeq p.2 (i + 1), C.mem_trackSeq p.2 i⟩)).choose_spec.2 i

/-- **Step 5.** The value of `T` at `p` lies in *every* fattened element containing `p`, not
just in those of the chosen tracking sequence. This is the independence of the choice. -/
theorem toFun_mem_y₂ (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₂ : IsCompact M₂) (p : M₁) (j : ℕ) (r : Fin (C.N j))
    (hr : (p : X₁) ∈ C.x₁ j r) : C.toFun hε hsum hM₂ p ∈ C.y₂ j r :=
  C.step1₂ hε hsum ⟨p.1, C.mem_trackSeq p.2 (j + 1), hr⟩ (C.toFun_spec hε hsum hM₂ p (j + 1))

/-- Bing's map `T` as a map of subtypes. -/
noncomputable def toMap (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₂ : IsCompact M₂) (p : M₁) : M₂ :=
  ⟨C.toFun hε hsum hM₂ p, C.toFun_mem hε hsum hM₂ p⟩

/-- **Step 6.** `T` is continuous. -/
theorem continuous_toMap (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₂ : IsCompact M₂) : Continuous (C.toMap hε hsum hM₂) := by
  rw [Metric.continuous_iff]
  rintro ⟨p, hp⟩ ρ hρ
  obtain ⟨j, -, hj⟩ := exists_mesh_lt ε hε hsum hρ 0
  obtain ⟨r, hr⟩ : ∃ r, p ∈ C.x₁ j r := Set.mem_iUnion.mp (C.cover₁ j hp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (C.open₁ j r) p hr
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨p', hp'⟩ hlt
  have hp'r : p' ∈ C.x₁ j r := hball (by simpa [Subtype.dist_eq] using hlt)
  have h1 := C.toFun_mem_y₂ hε hsum hM₂ ⟨p', hp'⟩ j r hp'r
  have h2 := C.toFun_mem_y₂ hε hsum hM₂ ⟨p, hp⟩ j r hr
  have h3 := C.dist_le_mesh₂ hε hsum (subset_closure h1) (subset_closure h2)
  simpa [toMap, Subtype.dist_eq] using lt_of_le_of_lt h3 hj

/-- **Step 8.** `T` is injective. -/
theorem injective_toMap (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₂ : IsCompact M₂) : Function.Injective (C.toMap hε hsum hM₂) := by
  rintro ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ hT
  by_contra hne
  have hne' : p₁ ≠ p₂ := fun h => hne (Subtype.ext h)
  have hd : 0 < dist p₁ p₂ := dist_pos.mpr hne'
  obtain ⟨k, -, hk⟩ := exists_mesh_lt ε hε hsum hd 0
  have hTeq : C.toFun hε hsum hM₂ ⟨p₂, h₂⟩ = C.toFun hε hsum hM₂ ⟨p₁, h₁⟩ := by
    simpa [toMap, eq_comm] using congrArg Subtype.val hT
  set Q := C.toFun hε hsum hM₂ ⟨p₁, h₁⟩
  have hQM : Q ∈ M₂ := C.toFun_mem hε hsum hM₂ ⟨p₁, h₁⟩
  obtain ⟨r, hrQ⟩ : ∃ r, Q ∈ C.x₂ k r := Set.mem_iUnion.mp (C.cover₂ k hQM)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (C.open₂ k r) Q hrQ
  obtain ⟨j, hjk, hj⟩ := exists_mesh_lt ε hε hsum hρ k
  obtain ⟨u, hu⟩ : ∃ u, p₁ ∈ C.x₁ j u := Set.mem_iUnion.mp (C.cover₁ j h₁)
  obtain ⟨v, hv⟩ : ∃ v, p₂ ∈ C.x₁ j v := Set.mem_iUnion.mp (C.cover₁ j h₂)
  have hQu : Q ∈ C.y₂ j u := C.toFun_mem_y₂ hε hsum hM₂ ⟨p₁, h₁⟩ j u hu
  have hQv : Q ∈ C.y₂ j v := by
    have := C.toFun_mem_y₂ hε hsum hM₂ ⟨p₂, h₂⟩ j v hv
    rwa [hTeq] at this
  -- both `x₂ j u` and `x₂ j v` meet `x₂ k r` in a point of `M₂`
  have key : ∀ (w : Fin (C.N j)), Q ∈ C.y₂ j w → closure (C.y₁ j w) ⊆ C.y₁ k r := by
    intro w hQw
    obtain ⟨c, hcw, hcM⟩ := C.meet₂ j w
    have hcy : c ∈ C.y₂ j w := C.x₂_subset_y₂ hε hsum j w hcw
    have hcQ : dist c Q ≤ mesh ε j :=
      C.dist_le_mesh₂ hε hsum (subset_closure hcy) (subset_closure hQw)
    have hckr : c ∈ C.x₂ k r := hball (by simp only [Metric.mem_ball]; linarith)
    exact C.step2₁ hε hsum k j hjk r w ⟨c, ⟨hckr, hcw⟩, hcM⟩
  have hp₁ : p₁ ∈ C.y₁ k r :=
    key u hQu (subset_closure (C.x₁_subset_y₁ hε hsum j u hu))
  have hp₂ : p₂ ∈ C.y₁ k r :=
    key v hQv (subset_closure (C.x₁_subset_y₁ hε hsum j v hv))
  have := C.dist_le_mesh₁ hε hsum (subset_closure hp₁) (subset_closure hp₂)
  linarith

/-- **Step 7.** `T` is surjective. -/
theorem surjective_toMap (C : MatchingCovers M₁ M₂ ε) (hε : ∀ i, 0 < ε i) (hsum : Summable ε)
    (hM₁ : IsCompact M₁) (hM₂ : IsCompact M₂) : Function.Surjective (C.toMap hε hsum hM₂) := by
  haveI : CompactSpace M₁ := isCompact_iff_compactSpace.mp hM₁
  have hcont := C.continuous_toMap hε hsum hM₂
  have hrange : IsCompact (Set.range (C.toMap hε hsum hM₂)) := isCompact_range hcont
  have hdense : Dense (Set.range (C.toMap hε hsum hM₂)) := by
    intro q
    rw [Metric.mem_closure_iff]
    intro ρ hρ
    obtain ⟨j, -, hj⟩ := exists_mesh_lt ε hε hsum hρ 0
    obtain ⟨r, hr⟩ : ∃ r, (q : X₂) ∈ C.x₂ j r := Set.mem_iUnion.mp (C.cover₂ j q.2)
    obtain ⟨p, hpx, hpM⟩ := C.meet₁ j r
    refine ⟨C.toMap hε hsum hM₂ ⟨p, hpM⟩, Set.mem_range_self _, ?_⟩
    have h1 : C.toFun hε hsum hM₂ ⟨p, hpM⟩ ∈ C.y₂ j r :=
      C.toFun_mem_y₂ hε hsum hM₂ ⟨p, hpM⟩ j r hpx
    have h2 : (q : X₂) ∈ C.y₂ j r := C.x₂_subset_y₂ hε hsum j r hr
    have h3 := C.dist_le_mesh₂ hε hsum (subset_closure h2) (subset_closure h1)
    simpa [toMap, Subtype.dist_eq] using lt_of_le_of_lt h3 hj
  have hu : Set.range (C.toMap hε hsum hM₂) = Set.univ := by
    rw [← hrange.isClosed.closure_eq, hdense.closure_eq]
  exact Set.range_eq_univ.mp hu

end MatchingCovers

/-- **Bing 1948, Theorem 11**, with the point-tracking clause Theorem 12 needs.
Under summable positive `ε` and compact `M₁, M₂`, there is a homeomorphism `T : M₁ ≃ₜ M₂`
such that whenever one index sequence tracks `p ∈ M₁` and `q ∈ M₂`, `T p = q`. -/
theorem MatchingCovers.exists_homeomorph (C : MatchingCovers M₁ M₂ ε)
    (hM₁ : IsCompact M₁) (hM₂ : IsCompact M₂)
    (hε : ∀ i, 0 < ε i) (hsum : Summable ε) :
    ∃ T : M₁ ≃ₜ M₂, ∀ (a : (i : ℕ) → Fin (C.N i)) (p : M₁) (q : M₂),
      C.Tracks₁ a p.1 → C.Tracks₂ a q.1 → T p = q := by
  haveI : CompactSpace M₁ := isCompact_iff_compactSpace.mp hM₁
  have hcont := C.continuous_toMap hε hsum hM₂
  have hbij : Function.Bijective (C.toMap hε hsum hM₂) :=
    ⟨C.injective_toMap hε hsum hM₂, C.surjective_toMap hε hsum hM₁ hM₂⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij) hcont, ?_⟩
  intro a p q hp hq
  have hdist : ∀ i, dist (C.toFun hε hsum hM₂ p) (q : X₂) ≤ mesh ε i := by
    intro i
    have h1 : C.toFun hε hsum hM₂ p ∈ C.y₂ i (a i) :=
      C.toFun_mem_y₂ hε hsum hM₂ p i (a i) (hp i)
    have h2 : (q : X₂) ∈ C.y₂ i (a i) := C.x₂_subset_y₂ hε hsum i (a i) (hq i)
    exact C.dist_le_mesh₂ hε hsum (subset_closure h1) (subset_closure h2)
  exact Subtype.ext (eq_of_forall_dist_le_mesh ε hε hsum hdist)

end Matching

end HPC
