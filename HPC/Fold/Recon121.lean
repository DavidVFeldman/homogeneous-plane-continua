import HPC.Fold.Theorem4
import HPC.Fold.Faithful
import HPC.Fold.ClosureF

/-!
# Batch 121: reconnaissance on `theorem3_end` and on Bing's Theorem 3 as printed

COMMISSION-batch121.md. Conventions as in `HPC.Fold.Theorem4`: `E` is the fine chain (Bing's
`D`), `D` the coarse chain (Bing's `E`), a consolidation is a block consolidation
`E.ofBlocks β hβ`, and "in the sum of `w` adjacent links of `D`" is `⊆ D.unionRange j w`.

Open statements are recorded as `def … : Prop`; nothing in this file is `sorry`.
-/

namespace HPC.Fold.Recon121

open HPC HPC.Chain

universe u

/-! ## Q1. The statements -/

/-- **Bing 1948, Theorem 3 as printed, in the block reading, end clause read respectively**
(the reading of COMMISSION-batch121 Q1(a)): a block consolidation with `E.link i` in its first
block and in no other block, every block in two adjacent links of `D`, and: a block containing an
end link of `E` that meets the first link of `D` lies in the first two links of `D`; one
containing an end link that meets the last link of `D` lies in the last two.

Refuted for `k = 3` by `not_theorem3Literal`; see `Theorem3LiteralOr` for Bing's wording. -/
def Theorem3Literal : Prop :=
  ∀ (X : Type u) [MetricSpace X] (n k : ℕ) (hk : 0 < k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ i : Fin n,
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧
      (∀ v, v ≠ β i → ¬ E.link i ⊆ (E.ofBlocks β hβ).link v) ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2))

/-- **Bing 1948, Theorem 3 as printed, with Bing's own wording of the end clause**: "any link of
`F` containing an end link of `D` which intersects `e₁` or `e_m` is a subset of `e₁ + e₂` or
`e_{m−1} + e_m`". For `k ≥ 4` the two readings agree (`endClause_or_iff`); for `k = 3` this one is
implied by the main clause. -/
def Theorem3LiteralOr : Prop :=
  ∀ (X : Type u) [MetricSpace X] (n k : ℕ) (hk : 0 < k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ i : Fin n,
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧
      (∀ v, v ≠ β i → ¬ E.link i ⊆ (E.ofBlocks β hβ).link v) ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 2) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty ∨ (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2 ∨
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2)

/-- **The three-link main clause (`theorem3`) with the two-link end clause** (COMMISSION-batch121
Q1(b)). -/
def Theorem3EndTwo : Prop :=
  ∀ (X : Type u) [MetricSpace X] (n k : ℕ) (hk : 0 < k) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ i : Fin n,
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 2) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - 2) 2))

/-- **The statement of `HPC.Fold.theorem3_end`** (open, `HPC/Fold/Theorem4.lean`), as a `Prop`. -/
def Theorem3EndStmt : Prop :=
  ∀ (X : Type u) [MetricSpace X] (n k : ℕ) (_hn : 0 < n) (hk : 3 ≤ k) (E : Chain X n)
    (D : Chain X k), E.IsCrookedIn' D → ∀ i : Fin n,
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β' hβ').link v ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3))

/-- **The statement of `HPC.Fold.theorem3`** (proved), as a `Prop`. -/
def Theorem3Stmt : Prop :=
  ∀ (X : Type u) [MetricSpace X] (n k : ℕ) (_hn : 0 < n) (E : Chain X n) (D : Chain X k),
    E.IsCrookedIn' D → ∀ i : Fin n,
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ v, ∃ j : ℕ, (E.ofBlocks β' hβ').link v ⊆ D.unionRange j 3

/-! ## Q1(c). The implications -/

theorem unionRange_mono {X : Type*} [MetricSpace X] {k : ℕ} (D : Chain X k) {j j' w w' : ℕ}
    (h1 : j' ≤ j) (h2 : j + w ≤ j' + w') : D.unionRange j w ⊆ D.unionRange j' w' := by
  intro x hx
  rw [mem_unionRange] at hx ⊢
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := hx
  exact ⟨a, by omega, by omega, ha3, ha4⟩

/-- `Theorem3Literal → Theorem3EndTwo`: two adjacent links are inside three. -/
theorem theorem3EndTwo_of_literal : Theorem3Literal.{u} → Theorem3EndTwo.{u} := by
  intro h X _ n k hk E D hcr i
  obtain ⟨q, β, hβ, h0, -, hmain, hend⟩ := h X n k hk E D hcr i
  refine ⟨q, β, hβ, h0, fun v => ?_, hend⟩
  obtain ⟨j, hj⟩ := hmain v
  exact ⟨j, hj.trans (unionRange_mono D le_rfl (by omega))⟩

/-- `Theorem3LiteralOr → Theorem3EndStmt`. (For `k = 3` the three-link end clause is automatic;
for `k ≥ 4` Bing's disjunctive end clause is the respective one, `endClause_or_iff`.) -/
theorem theorem3EndStmt_of_literalOr : Theorem3LiteralOr.{u} → Theorem3EndStmt.{u} := by
  intro h X _ n k _hn hk E D hcr i
  obtain ⟨q, β, hβ, h0, -, hmain, hend⟩ := h X n k (by omega) E D hcr i
  refine ⟨q, β, hβ, h0, fun v => ?_, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · obtain ⟨j, hj⟩ := hmain v
    exact ⟨j, hj.trans (unionRange_mono D le_rfl (by omega))⟩
  · by_cases hk3 : k = 3
    · subst hk3
      intro x hx
      obtain ⟨t', ht'⟩ := (show x ∈ E.union from by
        simp only [ofBlocks_link, Set.mem_iUnion] at hx
        obtain ⟨t', -, hx'⟩ := hx
        exact Set.mem_iUnion.mpr ⟨t', hx'⟩) |> Set.mem_iUnion.mp
      obtain ⟨j, hj⟩ := hcr.1 t'
      exact link_subset_unionRange D j (by omega) (by have := j.isLt; omega) (hj ht')
    · rcases hend t ht (Or.inl hm) with h1 | h1
      · exact h1.trans (unionRange_mono D le_rfl (by omega))
      · -- an end link meeting `D.link 0` inside the last two links: impossible for `k ≥ 4`
        exfalso
        obtain ⟨z, hz1, hz2⟩ := hm
        have hzb : z ∈ (E.ofBlocks β hβ).link (β t) := by
          rw [ofBlocks_link]; exact Set.mem_biUnion (show β t = β t from rfl) hz1
        obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (h1 hzb)
        have := (D.adjacent_iff ⟨a, ha3⟩ ⟨0, by omega⟩).mp ⟨z, ha4, hz2⟩
        simp only at this; omega
  · by_cases hk3 : k = 3
    · subst hk3
      intro x hx
      obtain ⟨t', ht'⟩ := (show x ∈ E.union from by
        simp only [ofBlocks_link, Set.mem_iUnion] at hx
        obtain ⟨t', -, hx'⟩ := hx
        exact Set.mem_iUnion.mpr ⟨t', hx'⟩) |> Set.mem_iUnion.mp
      obtain ⟨j, hj⟩ := hcr.1 t'
      exact link_subset_unionRange D j (by omega) (by have := j.isLt; omega) (hj ht')
    · rcases hend t ht (Or.inr hm) with h1 | h1
      · exfalso
        obtain ⟨z, hz1, hz2⟩ := hm
        have hzb : z ∈ (E.ofBlocks β hβ).link (β t) := by
          rw [ofBlocks_link]; exact Set.mem_biUnion (show β t = β t from rfl) hz1
        obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (h1 hzb)
        have := (D.adjacent_iff ⟨a, ha3⟩ ⟨k - 1, by omega⟩).mp ⟨z, ha4, hz2⟩
        simp only at this; omega
      · exact h1.trans (unionRange_mono D (by omega) (by omega))

/-- The respective end clause implies Bing's disjunctive one, for any `k`. -/
theorem theorem3LiteralOr_of_literal : Theorem3Literal.{u} → Theorem3LiteralOr.{u} := by
  intro h X _ n k hk E D hcr i
  obtain ⟨q, β, hβ, h0, honly, hmain, hend⟩ := h X n k hk E D hcr i
  refine ⟨q, β, hβ, h0, honly, hmain, fun t ht hm => ?_⟩
  rcases hm with hm | hm
  · exact Or.inl ((hend t ht).1 hm)
  · exact Or.inr ((hend t ht).2 hm)

/-- **The two readings of the end clause agree for `k ≥ 4`**: for a set `A` (an end link) inside
a set `B` (its block), "meets the first link ⇒ `B` in the first two, and meets the last link ⇒
`B` in the last two" is equivalent to Bing's "meets the first or the last link ⇒ `B` in the first
two or in the last two". -/
theorem endClause_or_iff {X : Type*} [MetricSpace X] {k : ℕ} (hk : 4 ≤ k) (D : Chain X k)
    {A B : Set X} (hAB : A ⊆ B) :
    (((A ∩ D.link ⟨0, by omega⟩).Nonempty → B ⊆ D.unionRange 0 2) ∧
      ((A ∩ D.link ⟨k - 1, by omega⟩).Nonempty → B ⊆ D.unionRange (k - 2) 2)) ↔
    ((A ∩ D.link ⟨0, by omega⟩).Nonempty ∨ (A ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
      B ⊆ D.unionRange 0 2 ∨ B ⊆ D.unionRange (k - 2) 2) := by
  constructor
  · rintro ⟨h1, h2⟩ (hm | hm)
    · exact Or.inl (h1 hm)
    · exact Or.inr (h2 hm)
  · intro h
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rcases h (Or.inl hm) with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨z, hz1, hz2⟩ := hm
        obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (h1 (hAB hz1))
        have := (D.adjacent_iff ⟨a, ha3⟩ ⟨0, by omega⟩).mp ⟨z, ha4, hz2⟩
        simp only at this; omega
    · rcases h (Or.inr hm) with h1 | h1
      · exfalso
        obtain ⟨z, hz1, hz2⟩ := hm
        obtain ⟨a, ha1, ha2, ha3, ha4⟩ := mem_unionRange.mp (h1 (hAB hz1))
        have := (D.adjacent_iff ⟨a, ha3⟩ ⟨k - 1, by omega⟩).mp ⟨z, ha4, hz2⟩
        simp only at this; omega
      · exact h1

/-- `Theorem3EndTwo → Theorem3EndStmt`: the two-link end clause implies the three-link one. -/
theorem theorem3EndStmt_of_endTwo : Theorem3EndTwo.{u} → Theorem3EndStmt.{u} := by
  intro h X _ n k _hn hk E D hcr i
  obtain ⟨q, β, hβ, h0, hmain, hend⟩ := h X n k (by omega) E D hcr i
  refine ⟨q, β, hβ, h0, hmain, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · exact ((hend t ht).1 hm).trans (unionRange_mono D le_rfl (by omega))
  · exact ((hend t ht).2 hm).trans (unionRange_mono D (by omega) (by omega))

/-- `Theorem3EndStmt → Theorem3Stmt`. (With fewer than three coarse links one block suffices.) -/
theorem theorem3Stmt_of_endStmt : Theorem3EndStmt.{u} → Theorem3Stmt.{u} := by
  intro h X _ n k hn E D hcr i
  by_cases hk : 3 ≤ k
  · obtain ⟨q, β, hβ, h0, hmain, -⟩ := h X n k hn hk E D hcr i
    exact ⟨q, β, hβ, h0, hmain⟩
  · -- one block: everything lies in the first three links
    refine ⟨1, fun _ => 0, ⟨fun v => ⟨i, Subsingleton.elim _ _⟩, fun _ _ _ => by simp⟩,
      rfl, fun v => ⟨0, ?_⟩⟩
    intro x hx
    simp only [ofBlocks_link, Set.mem_iUnion] at hx
    obtain ⟨t', -, hx'⟩ := hx
    obtain ⟨j, hj⟩ := hcr.1 t'
    exact link_subset_unionRange D j (by omega) (by have := j.isLt; omega) (hj hx')

/-- `Theorem3Stmt` holds: it is `HPC.Fold.theorem3`. -/
theorem theorem3Stmt_holds : Theorem3Stmt.{u} :=
  fun _ _ _ _ hn _ _ hcr i => theorem3 hn hcr i


/-! ## Q1(a). Bing's end clause read respectively fails for three coarse links

Five open rectangles in `ℝ × ℝ` at heights `(t, t + 3/2)` and three strips `strip 0, 1, 2`. The
end links `0` and `4` lie in the middle strip and reach into both outer strips; links `1` and `3`
lie only in the outer strips `0` and `2`. With the respective end clause, the block of each end
link lies in `D_0 ∪ D_1` and in `D_1 ∪ D_2`, hence in `D_1`, so it contains neither link `1` nor
link `3`; and links `1` and `3` cannot share a two-link block. A block map from basepoint `2`
cannot satisfy all four separations (`omega`). Crookedness is vacuous for three coarse links. -/

/-- Left ends of the five rectangles. -/
noncomputable def k3ax : Fin 5 → ℝ := ![11/10, 1/5, 6/5, 21/10, 11/10]
/-- Right ends of the five rectangles. -/
noncomputable def k3bx : Fin 5 → ℝ := ![12/5, 7/5, 23/10, 17/5, 12/5]

/-- The five rectangles. -/
noncomputable def k3Rect (t : Fin 5) : Set (ℝ × ℝ) :=
  Set.Ioo (k3ax t) (k3bx t) ×ˢ Set.Ioo (t : ℝ) ((t : ℝ) + 3/2)

theorem k3Rect_inter (s t : Fin 5) : (k3Rect s ∩ k3Rect t).Nonempty ↔
    ((s : ℤ) - (t : ℤ)).natAbs ≤ 1 := by
  rw [k3Rect, k3Rect, Set.prod_inter_prod, Set.prod_nonempty_iff, Set.Ioo_inter_Ioo,
    Set.Ioo_inter_Ioo, Set.nonempty_Ioo, Set.nonempty_Ioo]
  fin_cases s <;> fin_cases t <;> norm_num [k3ax, k3bx, max_def, min_def]

/-- The fine chain of the `k = 3` counterexample. -/
noncomputable def k3Chain : Chain (ℝ × ℝ) 5 where
  link := k3Rect
  isOpen _ := isOpen_Ioo.prod isOpen_Ioo
  adjacent := k3Rect_inter

theorem k3_refines (t : Fin 5) : ∃ j, k3Chain.link t ⊆ (stripChain 3).link j := by
  have key : ∀ (a b : ℝ) (j : ℕ) (y0 y1 : ℝ), (j : ℝ) ≤ a → b ≤ (j : ℝ) + 3/2 →
      Set.Ioo a b ×ˢ Set.Ioo y0 y1 ⊆ strip (j : ℤ) := by
    intro a b j y0 y1 h1 h2
    unfold strip
    refine Set.prod_mono (Set.Ioo_subset_Ioo ?_ ?_) (Set.subset_univ _) <;> push_cast <;> linarith
  fin_cases t
  · exact ⟨1, key _ _ 1 _ _ (by norm_num [k3ax]) (by norm_num [k3bx])⟩
  · exact ⟨0, key _ _ 0 _ _ (by norm_num [k3ax]) (by norm_num [k3bx])⟩
  · exact ⟨1, key _ _ 1 _ _ (by norm_num [k3ax]) (by norm_num [k3bx])⟩
  · exact ⟨2, key _ _ 2 _ _ (by norm_num [k3ax]) (by norm_num [k3bx])⟩
  · exact ⟨1, key _ _ 1 _ _ (by norm_num [k3ax]) (by norm_num [k3bx])⟩

/-- The chain is crooked in the three strips (vacuously: no two coarse links are three apart). -/
theorem k3_crooked : k3Chain.IsCrookedIn' (stripChain 3) :=
  ⟨k3_refines, fun _ k hk => absurd hk (by have := k.isLt; omega)⟩

theorem k3_mem (t : Fin 5) (x y : ℝ) (hx1 : k3ax t < x) (hx2 : x < k3bx t) (hy1 : (t : ℝ) < y)
    (hy2 : y < (t : ℝ) + 3/2) : (x, y) ∈ k3Chain.link t := ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩

theorem strip_unionRange_fst {M j w : ℕ} {p : ℝ × ℝ} (h : p ∈ (stripChain M).unionRange j w) :
    ∃ a : ℕ, j ≤ a ∧ a < j + w ∧ (a : ℝ) < p.1 ∧ p.1 < (a : ℝ) + 3/2 := by
  obtain ⟨a, h1, h2, _, h4⟩ := mem_unionRange.mp h
  refine ⟨a, h1, h2, ?_, ?_⟩
  · have := h4.1.1; simpa using this
  · have := h4.1.2; simpa using this

theorem mem_ofBlocks_self {X : Type*} [MetricSpace X] {n q : ℕ} (E : Chain X n)
    {β : Fin n → Fin q} (hβ : IsBlockMap β) (t : Fin n) {x : X} (hx : x ∈ E.link t) :
    x ∈ (E.ofBlocks β hβ).link (β t) := by
  rw [ofBlocks_link]; exact Set.mem_biUnion (show β t = β t from rfl) hx

/-- **`Theorem3Literal` is false** (at `k = 3`, basepoint `2`, the chain `k3Chain`). Bing's own
wording ("… meets `e₁` or `e_m` … is a subset of `e₁ + e₂` or `e_{m−1} + e_m`",
`Theorem3LiteralOr`) is not refuted by this example: for `k = 3` it is implied by the main
clause, and for `k ≥ 4` the two readings coincide (`endClause_or_iff`). -/
theorem not_theorem3Literal : ¬ Theorem3Literal.{0} := by
  intro h
  obtain ⟨q, β, hβ, h0, -, hmain, hend⟩ :=
    h (ℝ × ℝ) 5 3 (by norm_num) k3Chain (stripChain 3) k3_crooked 2
  have p1 : ((1/2 : ℝ), (7/4 : ℝ)) ∈ k3Chain.link 1 :=
    k3_mem 1 _ _ (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num) (by norm_num)
      (by norm_num)
  have p3 : ((3 : ℝ), (15/4 : ℝ)) ∈ k3Chain.link 3 :=
    k3_mem 3 _ _ (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num) (by norm_num)
      (by norm_num)
  have hm : ∀ t : Fin 5, t = 0 ∨ t = 4 →
      (k3Chain.link t ∩ (stripChain 3).link ⟨0, by norm_num⟩).Nonempty ∧
      (k3Chain.link t ∩ (stripChain 3).link ⟨3 - 1, by norm_num⟩).Nonempty := by
    rintro t (rfl | rfl)
    · exact ⟨⟨(6/5, 3/4), k3_mem 0 _ _ (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num)
        (by norm_num) (by norm_num), ⟨by norm_num [stripChain, strip], trivial⟩⟩,
        ⟨(23/10, 3/4), k3_mem 0 _ _ (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num)
        (by norm_num) (by norm_num), ⟨by norm_num [stripChain, strip], trivial⟩⟩⟩
    · exact ⟨⟨(6/5, 19/4), k3_mem 4 _ _ (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num)
        (by norm_num) (by norm_num), ⟨by norm_num [stripChain, strip], trivial⟩⟩,
        ⟨(23/10, 19/4), k3_mem 4 _ _ (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num)
        (by norm_num) (by norm_num), ⟨by norm_num [stripChain, strip], trivial⟩⟩⟩
  have hlo := fun t ht => (hend t (by rcases ht with rfl | rfl <;> simp)).1 (hm t ht).1
  have hhi := fun t ht => (hend t (by rcases ht with rfl | rfl <;> simp)).2 (hm t ht).2
  have n1 : ∀ t : Fin 5, t = 0 ∨ t = 4 → (β t).val ≠ (β 1).val := by
    intro t ht he
    have he' : β 1 = β t := Fin.ext he.symm
    have := hhi t ht (he' ▸ mem_ofBlocks_self k3Chain hβ 1 p1)
    obtain ⟨a, h1, h2, h3, h4⟩ := strip_unionRange_fst this
    have : (1 : ℝ) ≤ a := by exact_mod_cast h1
    norm_num at h3; linarith
  have n3 : ∀ t : Fin 5, t = 0 ∨ t = 4 → (β t).val ≠ (β 3).val := by
    intro t ht he
    have he' : β 3 = β t := Fin.ext he.symm
    have := hlo t ht (he' ▸ mem_ofBlocks_self k3Chain hβ 3 p3)
    obtain ⟨a, h1, h2, h3, h4⟩ := strip_unionRange_fst this
    have : (a : ℝ) ≤ 1 := by exact_mod_cast (by omega : a ≤ 1)
    norm_num at h4; linarith
  have n13 : (β 1).val ≠ (β 3).val := by
    intro he
    have he' : β 3 = β 1 := Fin.ext he.symm
    obtain ⟨j, hj⟩ := hmain (β 1)
    obtain ⟨a, h1, h2, h3, h4⟩ := strip_unionRange_fst (hj (mem_ofBlocks_self k3Chain hβ 1 p1))
    obtain ⟨b, g1, g2, g3, g4⟩ :=
      strip_unionRange_fst (hj (he' ▸ mem_ofBlocks_self k3Chain hβ 3 p3))
    have ha : a = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ a := by exact_mod_cast (by omega : 1 ≤ a)
      norm_num at h3; linarith
    have hb : (b : ℝ) ≤ 1 := by exact_mod_cast (by omega : b ≤ 1)
    norm_num at g4; linarith
  have l01 := hβ.lip 0 1 rfl
  have l12 := hβ.lip 1 2 rfl
  have l23 := hβ.lip 2 3 rfl
  have l34 := hβ.lip 3 4 rfl
  have a0 := n1 0 (Or.inl rfl)
  have a4 := n1 4 (Or.inr rfl)
  have b0 := n3 0 (Or.inl rfl)
  have b4 := n3 4 (Or.inr rfl)
  omega

/-- The end link `0` of `k3Chain` meets the last strip although neither it nor its neighbour lies
in that strip: an *unforced* meeting, invisible to the meeting table of the faithful model
(`linkRect_meet_strip_iff`). This is the Q2 gap, realized. -/
theorem k3_unforced_meeting :
    (k3Chain.link 0 ∩ (stripChain 3).link 2).Nonempty ∧
      ¬ k3Chain.link 0 ⊆ (stripChain 3).link 2 ∧ ¬ k3Chain.link 1 ⊆ (stripChain 3).link 2 := by
  refine ⟨⟨(23/10, 3/4), k3_mem 0 _ _ (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num)
      (by norm_num) (by norm_num), ⟨by norm_num [stripChain, strip], trivial⟩⟩, ?_, ?_⟩
  · intro hs
    have := (hs (k3_mem 0 (6/5) (3/4) (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num)
      (by norm_num) (by norm_num))).1.1
    norm_num [stripChain, strip] at this
  · intro hs
    have := (hs (k3_mem 1 (1/2) (7/4) (by simp [k3ax]; norm_num) (by simp [k3bx]; norm_num)
      (by norm_num) (by norm_num))).1.1
    norm_num [stripChain, strip] at this

/-! ## Q1(a). The clause "`d_i` is contained in only the first link of `F`"

For a block consolidation the clause can fail only through the neighbours of `E.link i`
(`link_subset_neighbours`): a link meets no link but its two neighbours, so if it is covered by
a block it does not belong to, it is covered by its neighbours in that block. This needs a link
contained in the union of its neighbours, which a chain allows (links are not assumed connected,
nor is a link barred from lying inside its neighbour): `only_clause_not_automatic`. In the
realized chains of the faithful model it never happens (`linkChain_only`), so the census needs no
extra check for it. -/

/-- A link covered by a block it does not belong to is covered by its neighbours in that block. -/
theorem link_subset_neighbours {X : Type*} [MetricSpace X] {n q : ℕ} (E : Chain X n)
    {β : Fin n → Fin q} (hβ : IsBlockMap β) {i : Fin n} {v : Fin q} (hv : v ≠ β i)
    (h : E.link i ⊆ (E.ofBlocks β hβ).link v) :
    E.link i ⊆ ⋃ t ∈ {t : Fin n | β t = v ∧ ((t : ℤ) - (i : ℤ)).natAbs = 1}, E.link t := by
  intro x hx
  have hx' := h hx
  rw [ofBlocks_link] at hx'
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx' ⊢
  obtain ⟨t, ht, hxt⟩ := hx'
  have hne : t ≠ i := fun e => hv (e ▸ ht.symm)
  have hadj := (E.adjacent t i).mp ⟨x, hxt, hx⟩
  have hne' : (t : ℤ) ≠ (i : ℤ) := fun e => hne (Fin.ext (by exact_mod_cast e))
  exact ⟨t, ⟨ht, by omega⟩, hxt⟩

/-- The `only`-clause holds for every block map on a chain whose links are distinct link
rectangles of a realized chain (the point at height `f s + 3/4` lies in no other rectangle). -/
theorem only_of_linkRect {m N : ℕ} {ρ σ : Fin N → ℤ} (hf : IsCrookedIvF ρ σ)
    (C : Chain (ℝ × ℝ) m) (f : Fin m → Fin N) (hfi : Function.Injective f)
    (hC : ∀ s, C.link s = linkRect ρ σ (f s)) {q : ℕ} {β : Fin m → Fin q} (hβ : IsBlockMap β)
    (i : Fin m) (v : Fin q) (hv : v ≠ β i) : ¬ C.link i ⊆ (C.ofBlocks β hβ).link v := by
  intro h
  have hlt : ((lxN ρ σ (f i) : ℝ) / 8) < ((rxN ρ σ (f i) : ℝ) / 8) := by
    have := lxN_lt_rxN hf (f i)
    have : (lxN ρ σ (f i) : ℝ) < rxN ρ σ (f i) := by exact_mod_cast this
    linarith
  set x : ℝ := ((lxN ρ σ (f i) : ℝ) / 8 + (rxN ρ σ (f i) : ℝ) / 8) / 2
  have hx : (x, ((f i : ℕ) : ℝ) + 3/4) ∈ C.link i := by
    rw [hC]
    exact ⟨⟨by simp only [x]; linarith, by simp only [x]; linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hx' := h hx
  rw [ofBlocks_link] at hx'
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx'
  obtain ⟨t, ht, hxt⟩ := hx'
  rw [hC] at hxt
  have hy := hxt.2
  simp only [Set.mem_Ioo] at hy
  have hti : f t = f i := by
    apply Fin.ext
    have a1 : ((f t).val : ℝ) < (f i).val + 1 := by linarith [hy.1]
    have a2 : ((f i).val : ℝ) < (f t).val + 1 := by linarith [hy.2]
    have b1 : (f t).val < (f i).val + 1 := by exact_mod_cast a1
    have b2 : (f i).val < (f t).val + 1 := by exact_mod_cast a2
    omega
  exact hv (hfi hti ▸ ht.symm)

/-- **In a realized chain the clause is automatic**: the point of link `i` at height `i + 3/4`
lies in no other link. -/
theorem linkChain_only {n : ℕ} {ρ σ : Fin n → ℤ} (hf : IsCrookedIvF ρ σ) {q : ℕ}
    {β : Fin n → Fin q} (hβ : IsBlockMap β) (i : Fin n) (v : Fin q) (hv : v ≠ β i) :
    ¬ (linkChain ρ σ hf).link i ⊆ ((linkChain ρ σ hf).ofBlocks β hβ).link v :=
  only_of_linkRect hf _ id Function.injective_id (fun _ => rfl) hβ i v hv

/-- The three intervals of `only_clause_not_automatic`. -/
noncomputable def onlyLink : Fin 3 → Set ℝ := ![Set.Ioo 0 1, Set.Ioo 0 2, Set.Ioo (3/2) 3]

/-- A three-link chain in `ℝ` whose first link lies inside its second. -/
noncomputable def onlyChain : Chain ℝ 3 where
  link := onlyLink
  isOpen t := by fin_cases t <;> simp [onlyLink, isOpen_Ioo]
  adjacent s t := by
    fin_cases s <;> fin_cases t <;>
      simp [onlyLink, Set.Ioo_inter_Ioo, Set.nonempty_Ioo, max_def, min_def] <;> norm_num

/-- **The clause is not automatic**: for the identity block map on `onlyChain`, the first link
lies in the second block. -/
theorem only_clause_not_automatic :
    ∃ (E : Chain ℝ 3) (β : Fin 3 → Fin 3) (hβ : IsBlockMap β),
      (β 0).val = 0 ∧ E.link 0 ⊆ (E.ofBlocks β hβ).link 1 := by
  refine ⟨onlyChain, id, ⟨Function.surjective_id, fun t t' h => by simp [h]⟩, rfl, ?_⟩
  intro x hx
  rw [ofBlocks_link]
  refine Set.mem_biUnion (x := (1 : Fin 3)) rfl ?_
  have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := hx
  show x ∈ Set.Ioo (0 : ℝ) 2
  exact ⟨hx'.1, by linarith [hx'.2]⟩

/-! ## Q2. The model and general chains

A general chain `E` crooked in `D` determines the pair `(minIdx, maxIdx)`, which lies in the
faithful model (`isCrookedIvF_minIdx_maxIdx`); conversely every member of the model is the pair of
a realized chain (`realization`). So the class of pairs is *exactly* the faithful model: unforced
meetings impose no constraint on `(ρ, σ)` beyond `IsCrookedIvF` (the realized chain has none).
What they do is enlarge the meeting table seen by the end clause. In a general chain the forced
meetings are real (`meets_of_forced`), and every real meeting with an extreme coarse link is
*possible* in the sense `σ t ≤ 1` / `ρ t ≥ k − 2` (`maxIdx_le_one_of_meets_first`,
`le_minIdx_of_meets_last`); an unforced one occurs (`k3_unforced_meeting`). The census of batches
86–87 read the hypothesis through the forced table only, so it under-covers. The model statement
`ModelEndP` reads it through the possible table; it implies the chain statement for every chain
(`chain_of_modelEndP`, `theorem3_end_of_model`). -/

section Q2

variable {X : Type*} [MetricSpace X] {n k : ℕ}

/-- A link meeting the first coarse link lies in a coarse link of index at most `1`. -/
theorem maxIdx_le_one_of_meets_first {E : Chain X n} {D : Chain X k} (h : E.Refines D)
    (t : Fin n) (hk : 0 < k) (hm : (E.link t ∩ D.link ⟨0, hk⟩).Nonempty) :
    (h.maxIdx t).val ≤ 1 := by
  obtain ⟨z, hz1, hz2⟩ := hm
  have := (D.adjacent_iff (h.maxIdx t) ⟨0, hk⟩).mp ⟨z, maxIdx_subset h t hz1, hz2⟩
  simp only at this; omega

/-- A link meeting the last coarse link lies in coarse links of index at least `k − 2`. -/
theorem le_minIdx_of_meets_last {E : Chain X n} {D : Chain X k} (h : E.Refines D)
    (t : Fin n) (hk : 0 < k) (hm : (E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    k - 2 ≤ (h.minIdx t).val := by
  obtain ⟨z, hz1, hz2⟩ := hm
  have := (D.adjacent_iff (h.minIdx t) ⟨k - 1, by omega⟩).mp ⟨z, minIdx_subset h t hz1, hz2⟩
  simp only at this; omega

/-- A link with index between `minIdx u` and `maxIdx u` contains `E.link u`. -/
theorem link_subset_of_between {E : Chain X n} {D : Chain X k} (h : E.Refines D) (u : Fin n)
    (j : Fin k) (h1 : h.minIdx u ≤ j) (h2 : j ≤ h.maxIdx u) : E.link u ⊆ D.link j := by
  have hw := subset_adjacent_of_subset h u (minIdx_subset h u) (maxIdx_subset h u)
  have h1' := Fin.le_def.mp h1
  have h2' := Fin.le_def.mp h2
  rcases (by omega : j.val = (h.minIdx u).val ∨ j.val = (h.maxIdx u).val) with e | e
  · rw [show j = h.minIdx u from Fin.ext e]; exact minIdx_subset h u
  · rw [show j = h.maxIdx u from Fin.ext e]; exact maxIdx_subset h u

/-- **Forced meetings are real** in every chain. -/
theorem meets_of_forced {E : Chain X n} {D : Chain X k} (h : E.Refines D) {t u : Fin n}
    (hu : ((u : ℤ) - (t : ℤ)).natAbs ≤ 1) (j : Fin k) (h1 : h.minIdx u ≤ j)
    (h2 : j ≤ h.maxIdx u) : (E.link t ∩ D.link j).Nonempty := by
  obtain ⟨z, hz1, hz2⟩ := (E.adjacent u t).mpr hu
  exact ⟨z, hz2, link_subset_of_between h u j h1 h2 hz1⟩

/-- **The model statement with the possible meeting table**, width `w`: a block map with
basepoint `i` at time `0`, every block meeting a common window of `w` coarse levels, and for each
end link `t`: if `σ t ≤ 1` (it may meet level `0`) its block has all `ρ ≤ w − 1`; if
`ρ t ≥ K − 2` (it may meet level `K − 1`) its block has all `σ ≥ K − w`. For `w = 3` this is the
census class `T3ENDP`, for `w = 2` the class `LITP` (census-batch121.c). -/
def ModelEndP {m : ℕ} (ρ σ : Fin m → ℤ) (K : ℤ) (w : ℕ) (i : Fin m) : Prop :=
  ∃ q, ∃ β : Fin m → Fin q, IsBlockMap β ∧ (β i).val = 0 ∧
    (∀ v, ∃ j : ℤ, ∀ t, β t = v → j ≤ σ t ∧ ρ t ≤ j + ((w - 1 : ℕ) : ℤ)) ∧
    ∀ t : Fin m, (t.val = 0 ∨ t.val = m - 1) →
      (σ t ≤ 1 → ∀ t', β t' = β t → ρ t' ≤ ((w - 1 : ℕ) : ℤ)) ∧
      (K - 2 ≤ ρ t → ∀ t', β t' = β t → K - (w : ℤ) ≤ σ t')

/-- **Transfer from the model to an arbitrary chain.** If the pair `(minIdx, maxIdx)` of a chain
`E` crooked in `D` satisfies `ModelEndP` at width `w`, then `E` has a block consolidation with
basepoint `i` first, every block in `w` adjacent links of `D`, and the end clause of width `w`
read with the true meetings. -/
theorem chain_of_modelEndP {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D)
    (hk : 0 < k) {w : ℕ} (hw : 1 ≤ w) (i : Fin n)
    (hm : ModelEndP (fun t => ((hcr.1.minIdx t : ℕ) : ℤ)) (fun t => ((hcr.1.maxIdx t : ℕ) : ℤ))
      k w i) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β),
      (β i).val = 0 ∧
      (∀ v, ∃ j : ℕ, (E.ofBlocks β hβ).link v ⊆ D.unionRange j w) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, hk⟩).Nonempty →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange 0 w) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β hβ).link (β t) ⊆ D.unionRange (k - w) w)) := by
  have href := hcr.1
  obtain ⟨q, β, hβ, h0, hmain, hend⟩ := hm
  have hle : ∀ t, (href.minIdx t).val ≤ (href.maxIdx t).val := fun t =>
    Fin.le_def.mp (minIdx_le href t (maxIdx_subset href t))
  have hwid : ∀ t, (href.maxIdx t).val ≤ (href.minIdx t).val + 1 := by
    intro t
    have := subset_adjacent_of_subset href t (minIdx_subset href t) (maxIdx_subset href t)
    omega
  have hlt : ∀ t, (href.maxIdx t).val < k := fun t => (href.maxIdx t).isLt
  -- a block lies in the union of its links
  have hblock : ∀ (v : Fin q) (S : Set X), (∀ t, β t = v → E.link t ⊆ S) →
      (E.ofBlocks β hβ).link v ⊆ S := by
    intro v S hS x hx
    rw [ofBlocks_link] at hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact hS t ht hxt
  refine ⟨q, β, hβ, h0, fun v => ?_, fun t ht => ⟨fun hmt => ?_, fun hmt => ?_⟩⟩
  · obtain ⟨j, hj⟩ := hmain v
    refine ⟨j.toNat, hblock v _ fun t htv => ?_⟩
    obtain ⟨h1, h2⟩ := hj t htv
    simp only at h1 h2
    rw [Nat.cast_sub hw, Nat.cast_one] at h2
    have := hle t; have := hwid t
    by_cases hjr : j ≤ ((href.minIdx t : ℕ) : ℤ)
    · exact (minIdx_subset href t).trans
        (link_subset_unionRange D _ (by omega) (by omega))
    · exact (maxIdx_subset href t).trans
        (link_subset_unionRange D _ (by omega) (by omega))
  · have hs := maxIdx_le_one_of_meets_first href t hk hmt
    have hb := (hend t ht).1 (by simp only; omega)
    refine hblock (β t) _ fun t' ht' => ?_
    have := hb t' ht'
    simp only at this
    rw [Nat.cast_sub hw, Nat.cast_one] at this
    exact (minIdx_subset href t').trans (link_subset_unionRange D _ (by omega) (by omega))
  · have hs := le_minIdx_of_meets_last href t hk hmt
    have hb := (hend t ht).2 (by simp only; omega)
    refine hblock (β t) _ fun t' ht' => ?_
    have := hb t' ht'
    simp only at this
    have := hlt t'
    exact (maxIdx_subset href t').trans (link_subset_unionRange D _ (by omega) (by omega))

/-- **Q2(b): the general-chain class projects exactly onto the faithful model.** A pair `(ρ, σ)`
with values in `[0, M)` is the `(minIdx, maxIdx)` pair of some chain in some metric space crooked
in some `M`-link chain iff it is in the faithful model; the realized chain of open rectangles has
only forced meetings. So unforced meetings constrain nothing beyond `IsCrookedIvF`; they only add
hypotheses to the end clause (`k3_unforced_meeting`). -/
theorem exists_chain_iff_isCrookedIvF {m M : ℕ} (ρ σ : Fin m → ℤ) :
    (∃ (Y : Type) (_ : MetricSpace Y) (E : Chain Y m) (D : Chain Y M) (h : E.IsCrookedIn' D),
        (∀ t, ((h.1.minIdx t : ℕ) : ℤ) = ρ t) ∧ (∀ t, ((h.1.maxIdx t : ℕ) : ℤ) = σ t)) ↔
      IsCrookedIvF ρ σ ∧ (∀ t, 0 ≤ ρ t) ∧ (∀ t, σ t < M) := by
  constructor
  · rintro ⟨Y, _, E, D, h, hρ, hσ⟩
    have hf := isCrookedIvF_minIdx_maxIdx h
    refine ⟨?_, fun t => by rw [← hρ]; positivity, fun t => by
      rw [← hσ]; have := (h.1.maxIdx t).isLt; omega⟩
    have e1 : (fun t => ((h.1.minIdx t : ℕ) : ℤ)) = ρ := funext hρ
    have e2 : (fun t => ((h.1.maxIdx t : ℕ) : ℤ)) = σ := funext hσ
    rw [e1, e2] at hf
    exact hf
  · rintro ⟨hf, hlo, hhi⟩
    obtain ⟨h, hρ, hσ⟩ := realization ρ σ hf hlo hhi
    exact ⟨ℝ × ℝ, inferInstance, linkChain ρ σ hf, stripChain M, h, hρ, hσ⟩

/-- **`theorem3_end` follows from the model statement with the possible meeting table**
(COMMISSION-batch121 Q2(a)). The census class `T3ENDP` (census-batch121.c) decides the
hypothesis on a finite corpus; no failure was found (REPORT-batch121.md). -/
theorem theorem3_end_of_model
    (hM : ∀ (m K : ℕ) (ρ σ : Fin m → ℤ), 0 < m → 3 ≤ K → IsCrookedIvF ρ σ →
      (∀ t, 0 ≤ ρ t) → (∀ t, σ t < K) → ∀ i, ModelEndP ρ σ K 3 i) :
    Theorem3EndStmt.{u} := by
  intro Y _ m K hm hK E D hcr i
  have hf := isCrookedIvF_minIdx_maxIdx hcr
  have hmod := hM m K _ _ hm hK hf (fun t => by positivity)
    (fun t => by have := (hcr.1.maxIdx t).isLt; omega) i
  obtain ⟨q, β, hβ, h0, hmain, hend⟩ := chain_of_modelEndP hcr (by omega) (by norm_num) i hmod
  exact ⟨q, β, hβ, h0, hmain, hend⟩

end Q2

/-! ## Q4. Bing's special case, executed literally

The special case of Bing's proof needs a fine chain `D` (here: `E`) whose end links meet the
extreme coarse links while no interior link does. In a realized chain of the faithful model this
never happens for the whole chain (a link inside `e₁` forces its neighbour to meet `e₁`), but it
does for a *subchain*: `seamD` is the subchain `1 … 11` of the realized chain of the thirteen-term
faithful sequence `seamRho`/`seamSig` (five coarse links). Its end links meet `e₁` and `e₅`
through the links `0` and `12` of the big chain; no interior link meets `e₁` or `e₅`
(`seamD_special`). Crookedness gives exactly one admissible pair `(h, k) = (4, 6)`
(`seamD_hk`; `d_h ⊆ e₄`, `d_k ⊆ e₂`).

Bing's construction: `H` from the induction hypothesis on `D(1, h)` (`seamC`, five links) inside
`E(1, r − 1)` (`seamE'`, four strips), `h_u` the link of `H` containing `d_h`, and
`F = H(1, u − 1) ⌢ (level groups of D′, top to bottom) ⌢ D(k + 1, n)`. The level groups are read
by `ρ` ("in `e₁ + e₂`", "in `e₃` but not in `e₂`", …): `bingSpecialF`. Its links form a chain with
`d_i` first iff the time function is `1`-Lipschitz along the fine chain with value `0` at `i`.

* `seam_every_H_fails`: for **every** basepoint `i ≤ h` and **every** `H` with `H i = 0`
  (no other property of `H` is used), `bingSpecialF` fails. The top group "in `e₄` but not in
  `e₃`" of `D′` is empty, so the time `u` is skipped: either `u = 0` and `d_i` is not in the first
  link, or the last link of `H(1, u − 1)` before `d_h` is followed by a link of time `≥ u + 1`.
* `seamIH_H0`: an `H` satisfying the induction hypothesis exists (so the construction is reached).
* `seam_Cbot_fails`: under the alternative reading in which a link of `D′` that is both in
  `e₁ + e₂` and in `e_{r−2} + e_{r−1}` goes to the bottom group and the top group absorbs every
  other link of `D′` in `e_{r−2} + e_{r−1}` (`bingSpecialFCbot`), some `H` satisfying the
  induction hypothesis still makes `F` fail (the seam at `h_{u−1}`). -/

/-- The thirteen lower ends of the big chain. -/
def seamRho : Fin 13 → ℤ := ![0, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4]
/-- The thirteen upper ends of the big chain. -/
def seamSig : Fin 13 → ℤ := ![0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4]

theorem seam_isCrookedIvF : IsCrookedIvF seamRho seamSig :=
  isCrookedIvF_of_check2 (by unfold IsCrookedIvFCheck2 ivEnd clampIdx; decide +kernel)

/-- The realized big chain (thirteen rectangles). -/
noncomputable def seamBig : Chain (ℝ × ℝ) 13 := linkChain seamRho seamSig seam_isCrookedIvF

theorem seamBig_crooked : seamBig.IsCrookedIn' (stripChain 5) :=
  (realization seamRho seamSig seam_isCrookedIvF (by decide) (by decide)).1

/-- **The chain of Bing's special case**: links `1 … 11` of the big chain. -/
noncomputable def seamD : Chain (ℝ × ℝ) 11 :=
  seamBig.sub ⟨1, by norm_num⟩ ⟨11, by norm_num⟩ (by decide)

theorem seamD_crooked : seamD.IsCrookedIn' (stripChain 5) :=
  seamBig_crooked.sub _ _ _

theorem seamD_link (s : Fin 11) :
    seamD.link s = linkRect seamRho seamSig ⟨1 + s.val, by omega⟩ := rfl

theorem seamD_meet_iff (s : Fin 11) (j : Fin 5) :
    (seamD.link s ∩ (stripChain 5).link j).Nonempty ↔
      ∃ u : Fin 13, ((u : ℤ) - ((1 + s.val : ℕ) : ℤ)).natAbs ≤ 1 ∧ seamRho u ≤ (j.val : ℤ) ∧
        (j.val : ℤ) ≤ seamSig u := by
  rw [seamD_link]
  exact linkRect_meet_strip_iff seam_isCrookedIvF _ _

theorem seamD_subset_iff (s : Fin 11) (j : Fin 5) :
    seamD.link s ⊆ (stripChain 5).link j ↔
      seamRho ⟨1 + s.val, by omega⟩ ≤ (j.val : ℤ) ∧ (j.val : ℤ) ≤ seamSig ⟨1 + s.val, by omega⟩ := by
  rw [seamD_link]
  exact linkRect_subset_strip_iff seam_isCrookedIvF _ _

/-- **The hypotheses of Bing's special case hold**: the end links meet `e₁` and `e₅`, no interior
link meets either. -/
theorem seamD_special :
    (seamD.link 0 ∩ (stripChain 5).link 0).Nonempty ∧
      (seamD.link 10 ∩ (stripChain 5).link 4).Nonempty ∧
      ∀ s : Fin 11, 0 < s.val → s.val < 10 →
        ¬ (seamD.link s ∩ (stripChain 5).link 0).Nonempty ∧
          ¬ (seamD.link s ∩ (stripChain 5).link 4).Nonempty := by
  simp only [seamD_meet_iff]
  decide

/-- **Bing's `h` and `k` are forced**: the only `0 < h < k < n − 1` with `d_h ⊆ e_{r−1}` and
`d_k ⊆ e₂` are `h = 4`, `k = 6`. -/
theorem seamD_hk :
    (seamD.link 4 ⊆ (stripChain 5).link 3 ∧ seamD.link 6 ⊆ (stripChain 5).link 1) ∧
      ∀ h k : Fin 11, 0 < h.val → h < k → k.val < 10 → seamD.link h ⊆ (stripChain 5).link 3 →
        seamD.link k ⊆ (stripChain 5).link 1 → h.val = 4 ∧ k.val = 6 := by
  simp only [seamD_subset_iff]
  decide

/-- The coarse levels `minIdx` of the links of `seamD`. -/
def seamLev : ℕ → ℕ := fun s => [1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3].getD s 0
/-- The coarse levels `maxIdx` of the links of `seamD`. -/
def seamLevHi : ℕ → ℕ := fun s => [1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3].getD s 0

theorem seamD_minIdx_maxIdx (s : Fin 11) :
    (seamD_crooked.1.minIdx s).val = seamLev s ∧ (seamD_crooked.1.maxIdx s).val = seamLevHi s := by
  have href := seamD_crooked.1
  have hval : ∀ s : Fin 11, 0 ≤ seamRho ⟨1 + s.val, by omega⟩ ∧
      seamRho ⟨1 + s.val, by omega⟩ = (seamLev s : ℤ) ∧
      seamSig ⟨1 + s.val, by omega⟩ = (seamLevHi s : ℤ) ∧ seamLevHi s < 5 := by decide
  obtain ⟨h0, h1, h2, h3⟩ := hval s
  have hle := seamD_subset_iff s
  have hlo : seamLev s ≤ seamLevHi s := by
    have := seam_isCrookedIvF.le ⟨1 + s.val, by omega⟩; omega
  constructor
  · have a := Fin.le_def.mp (minIdx_le href s ((hle ⟨seamLev s, by omega⟩).mpr
      ⟨by simp only; omega, by simp only; omega⟩))
    have b := ((hle (href.minIdx s)).mp (minIdx_subset href s)).1
    simp only at a; omega
  · have a := Fin.le_def.mp (le_maxIdx href s ((hle ⟨seamLevHi s, by omega⟩).mpr
      ⟨by simp only; omega, by simp only; omega⟩))
    have b := ((hle (href.maxIdx s)).mp (maxIdx_subset href s)).2
    simp only at a; omega

/-- **Bing's special-case construction**, reading A (level groups by the least coarse level `ρ`):
the time of fine link `t` in `F`, from the times `H` of `D(1, h)`, for `K = r` coarse links. -/
def bingSpecialF (K : ℕ) (ρ : ℕ → ℕ) (h k : ℕ) (H : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t ≤ h ∧ H t < H h then H t
  else if t ≤ k then H h + (K - 3) - (max (ρ t) 1 - 1)
  else H h + (K - 3) + (t - k)

/-- Reading `Cbot`: bottom group "in `e₁ + e₂`" first, then a top group absorbing every other link
of `D′` in `e_{r−2} + e_{r−1}`, the groups between by `ρ`. -/
def bingSpecialFCbot (K : ℕ) (ρ σ : ℕ → ℕ) (h k : ℕ) (H : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t ≤ h ∧ H t < H h then H t
  else if t ≤ k then
    H h + (K - 4) - (if ρ t ≤ 1 then 0 else if K - 3 ≤ σ t then K - 4 else ρ t - 1)
  else H h + (K - 4) + (t - k)

theorem exists_switch (P : ℕ → Prop) {a b : ℕ} (hab : a ≤ b) (ha : P a) (hb : ¬ P b) :
    ∃ t, a ≤ t ∧ t < b ∧ P t ∧ ¬ P (t + 1) := by
  induction b with
  | zero => exact absurd (by rwa [Nat.le_zero.mp hab] at ha) hb
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · exact absurd (h ▸ ha) hb
    · by_cases hP : P b
      · exact ⟨b, by omega, by omega, hP, hb⟩
      · obtain ⟨t, h1, h2, h3, h4⟩ := ih (by omega) hP
        exact ⟨t, h1, by omega, h3, h4⟩

/-- **Bing's special-case construction fails on `seamD` for every basepoint and every `H`**
(reading A, `h = 4`, `k = 6`, the levels of `seamD`): two consecutive fine links get times at
least two apart (their links of `F` meet, so `F` is not a chain), or `d_i` is not in the first
link of `F`. Nothing about `H` beyond `H i = 0` is used, so this holds in particular for every
`H` given by the induction hypothesis. -/
theorem seam_every_H_fails (i : ℕ) (hi : i ≤ 4) (H : ℕ → ℕ) (hH : H i = 0) :
    (∃ t, t + 1 < 11 ∧ (bingSpecialF 5 seamLev 4 6 H t + 2 ≤ bingSpecialF 5 seamLev 4 6 H (t + 1) ∨
        bingSpecialF 5 seamLev 4 6 H (t + 1) + 2 ≤ bingSpecialF 5 seamLev 4 6 H t)) ∨
      bingSpecialF 5 seamLev 4 6 H i ≠ 0 := by
  have hlev : ∀ s, s ≤ 6 → seamLev s ≤ 2 := by
    intro s hs; interval_cases s <;> decide
  by_cases hu : H 4 = 0
  · right
    have hnot : ¬ (i ≤ 4 ∧ H i < H 4) := by omega
    have := hlev i (by omega)
    simp only [bingSpecialF, hnot, if_false, show i ≤ 6 by omega, if_true]
    omega
  · left
    obtain ⟨t, h1, h2, h3, h4⟩ := exists_switch (fun s => s ≤ 4 ∧ H s < H 4) hi
      ⟨hi, by omega⟩ (by simp)
    refine ⟨t, by omega, Or.inl ?_⟩
    have := hlev (t + 1) (by omega)
    simp only [bingSpecialF, h3, h4, and_self, if_true, if_false, show t + 1 ≤ 6 by omega]
    omega

/-! ### The induction hypothesis is satisfiable -/

/-- `D(1, h)`: the first five links of `seamD`. -/
noncomputable def seamC : Chain (ℝ × ℝ) 5 := seamD.sub ⟨0, by norm_num⟩ ⟨4, by norm_num⟩ (by decide)

/-- `E(1, r − 1)`: the first four strips. -/
noncomputable def seamE' : Chain (ℝ × ℝ) 4 :=
  (stripChain 5).sub ⟨0, by norm_num⟩ ⟨3, by norm_num⟩ (by decide)

/-- Crookedness passes to an initial segment of the coarse chain that still contains every link. -/
theorem IsCrookedIn'.sub_right {X : Type*} [MetricSpace X] {n N : ℕ} {E : Chain X n}
    {D : Chain X N} (hcr : E.IsCrookedIn' D) (m : Fin N)
    (hin : ∀ t, ∃ j : Fin N, j ≤ m ∧ E.link t ⊆ D.link j) :
    E.IsCrookedIn' (D.sub ⟨0, m.pos⟩ m (Nat.zero_le m.val)) := by
  have hl : ∀ (a : ℕ) (ha : a < m.val - 0 + 1),
      (D.sub ⟨0, m.pos⟩ m (Nat.zero_le m.val)).link ⟨a, ha⟩ = D.link ⟨a, by omega⟩ := by
    intro a ha
    show D.link ⟨0 + a, _⟩ = _
    congr 1; exact Fin.ext (by simp)
  refine ⟨fun t => ?_, fun h k hk i j hi hj => ?_⟩
  · obtain ⟨j, hj, hsub⟩ := hin t
    refine ⟨⟨j.val, by have := Fin.le_def.mp hj; show j.val < m.val - 0 + 1; omega⟩, ?_⟩
    rw [hl]; exact hsub
  · have hkl := k.isLt
    rw [show h = ⟨h.val, h.isLt⟩ from rfl, hl] at hi
    rw [show k = ⟨k.val, k.isLt⟩ from rfl, hl] at hj
    obtain ⟨r, s, hb, hr, hs⟩ := hcr.2 ⟨h.val, by omega⟩ ⟨k.val, by omega⟩ hk i j hi hj
    refine ⟨r, s, hb, ?_, ?_⟩
    · rw [hl]; exact hr
    · rw [hl]; exact hs

theorem seamC_link (s : Fin 5) : seamC.link s = seamD.link ⟨s.val, by omega⟩ := by
  show seamD.link ⟨0 + s.val, _⟩ = _
  congr 1; exact Fin.ext (by simp)

theorem seamE'_link (j : Fin 4) : seamE'.link j = (stripChain 5).link ⟨j.val, by omega⟩ := by
  show (stripChain 5).link ⟨0 + j.val, _⟩ = _
  congr 1; exact Fin.ext (by simp)

/-- **The induction hypothesis applies**: `D(1, h)` is crooked in `E(1, r − 1)`. -/
theorem seamC_crooked : seamC.IsCrookedIn' seamE' := by
  have h1 : seamC.IsCrookedIn' (stripChain 5) := seamD_crooked.sub _ _ _
  refine IsCrookedIn'.sub_right h1 ⟨3, by norm_num⟩ fun t => ?_
  have hv : ∀ s : Fin 5, seamRho ⟨1 + s.val, by omega⟩ ≤ 3 ∧ 0 ≤ seamRho ⟨1 + s.val, by omega⟩ ∧
      seamRho ⟨1 + s.val, by omega⟩ ≤ seamSig ⟨1 + s.val, by omega⟩ := by decide
  obtain ⟨a, b, c⟩ := hv t
  refine ⟨⟨(seamRho ⟨1 + t.val, by omega⟩).toNat, by omega⟩, Fin.le_def.mpr (by simp; omega), ?_⟩
  rw [seamC_link]
  exact (seamD_subset_iff ⟨t.val, by omega⟩ _).mpr ⟨by simp, by simp; omega⟩

/-- **Bing's induction hypothesis on `D(1, h)` inside `E(1, r − 1)`**, as given by the theorem
being proved (`Theorem3LiteralOr`'s conclusion; for four coarse links its end clause is the
respective one, `endClause_or_iff`): basepoint `i` in the first block and in no other, every
block in two adjacent links of `E(1, r − 1)`, and the end clause for `d_1`, `d_h`. -/
def SeamIH (i : Fin 5) {q : ℕ} (H : Fin 5 → Fin q) (hH : IsBlockMap H) : Prop :=
  (H i).val = 0 ∧
    (∀ v, v ≠ H i → ¬ seamC.link i ⊆ (seamC.ofBlocks H hH).link v) ∧
    (∀ v, ∃ j : ℕ, (seamC.ofBlocks H hH).link v ⊆ seamE'.unionRange j 2) ∧
    (∀ t : Fin 5, (t.val = 0 ∨ t.val = 4) →
      ((seamC.link t ∩ seamE'.link 0).Nonempty ∨ (seamC.link t ∩ seamE'.link 3).Nonempty) →
      (seamC.ofBlocks H hH).link (H t) ⊆ seamE'.unionRange 0 2 ∨
        (seamC.ofBlocks H hH).link (H t) ⊆ seamE'.unionRange 2 2)

/-- Membership of a link of `seamC` in a union of two strips of `seamE'`. -/
theorem seamC_link_subset (s : Fin 5) (j : ℕ) (a : ℕ) (ha : j ≤ a ∧ a < j + 2 ∧ a < 4)
    (hs : seamRho ⟨1 + s.val, by omega⟩ ≤ (a : ℤ) ∧ (a : ℤ) ≤ seamSig ⟨1 + s.val, by omega⟩) :
    seamC.link s ⊆ seamE'.unionRange j 2 := by
  rw [seamC_link]
  refine ((seamD_subset_iff ⟨s.val, by omega⟩ ⟨a, by omega⟩).mpr hs).trans ?_
  rw [← seamE'_link ⟨a, ha.2.2⟩]
  exact link_subset_unionRange seamE' ⟨a, ha.2.2⟩ ha.1 ha.2.1

theorem ofBlocks_subset_of {X : Type*} [MetricSpace X] {n q : ℕ} (E : Chain X n)
    {β : Fin n → Fin q} (hβ : IsBlockMap β) (v : Fin q) (S : Set X)
    (hS : ∀ t, β t = v → E.link t ⊆ S) : (E.ofBlocks β hβ).link v ⊆ S := by
  intro x hx
  rw [ofBlocks_link] at hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact hS t ht hxt

/-- The times `0, 0, 0, 1, 1` on `D(1, h)`. -/
def seamH0 : Fin 5 → Fin 2 := ![0, 0, 0, 1, 1]
/-- The times `0, 1, 0, 1, 1` on `D(1, h)`. -/
def seamH1 : Fin 5 → Fin 2 := ![0, 1, 0, 1, 1]

theorem seamH0_isBlockMap : IsBlockMap seamH0 :=
  ⟨by decide, by decide⟩

theorem seamH1_isBlockMap : IsBlockMap seamH1 :=
  ⟨by decide, by decide⟩

theorem seamC_only {q : ℕ} {β : Fin 5 → Fin q} (hβ : IsBlockMap β) (i : Fin 5) (v : Fin q)
    (hv : v ≠ β i) : ¬ seamC.link i ⊆ (seamC.ofBlocks β hβ).link v :=
  only_of_linkRect seam_isCrookedIvF seamC (fun s => ⟨1 + s.val, by omega⟩)
    (fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega))
    (fun s => by rw [seamC_link, seamD_link]) hβ i v hv

/-- **An `H` satisfying the induction hypothesis**: `0, 0, 0, 1, 1`, for the basepoints
`i = 0, 1, 2`. -/
theorem seamIH_H0 (i : Fin 5) (hi : i.val ≤ 2) : SeamIH i seamH0 seamH0_isBlockMap := by
  have hblk0 : (seamC.ofBlocks seamH0 seamH0_isBlockMap).link 0 ⊆ seamE'.unionRange 0 2 :=
    ofBlocks_subset_of seamC _ 0 _ fun t ht => by
      fin_cases t <;> simp [seamH0] at ht <;> exact seamC_link_subset _ 0 1 (by norm_num) (by decide)
  have hblk1 : (seamC.ofBlocks seamH0 seamH0_isBlockMap).link 1 ⊆ seamE'.unionRange 2 2 :=
    ofBlocks_subset_of seamC _ 1 _ fun t ht => by
      fin_cases t <;> simp [seamH0] at ht <;> exact seamC_link_subset _ 2 2 (by norm_num) (by decide)
  refine ⟨by fin_cases i <;> simp_all [seamH0], fun v hv => seamC_only _ i v hv, fun v => ?_,
    fun t ht _ => ?_⟩
  · fin_cases v
    · exact ⟨0, hblk0⟩
    · exact ⟨2, hblk1⟩
  · rcases ht with ht | ht
    · rw [show t = 0 from Fin.ext ht]; exact Or.inl hblk0
    · rw [show t = 4 from Fin.ext ht]; exact Or.inr hblk1

/-- **An `H` satisfying the induction hypothesis**: `0, 1, 0, 1, 1`, basepoint `0`. -/
theorem seamIH_H1 : SeamIH 0 seamH1 seamH1_isBlockMap := by
  have hblk0 : (seamC.ofBlocks seamH1 seamH1_isBlockMap).link 0 ⊆ seamE'.unionRange 0 2 :=
    ofBlocks_subset_of seamC _ 0 _ fun t ht => by
      fin_cases t <;> simp [seamH1] at ht <;> exact seamC_link_subset _ 0 1 (by norm_num) (by decide)
  have hblk1 : (seamC.ofBlocks seamH1 seamH1_isBlockMap).link 1 ⊆ seamE'.unionRange 2 2 :=
    ofBlocks_subset_of seamC _ 1 _ fun t ht => by
      fin_cases t <;> simp [seamH1] at ht <;> exact seamC_link_subset _ 2 2 (by norm_num) (by decide)
  refine ⟨rfl, fun v hv => seamC_only _ 0 v hv, fun v => ?_, fun t ht _ => ?_⟩
  · fin_cases v
    · exact ⟨0, hblk0⟩
    · exact ⟨2, hblk1⟩
  · rcases ht with ht | ht
    · rw [show t = 0 from Fin.ext ht]; exact Or.inl hblk0
    · rw [show t = 4 from Fin.ext ht]; exact Or.inr hblk1

/-- **Reading `Cbot` fails too**, for the `H` of `seamIH_H1` (basepoint `0`): `d_1` gets time `0`
and its neighbour `d_2`, in `h_u` but in the bottom group, gets time `2`. -/
theorem seam_Cbot_fails :
    bingSpecialFCbot 5 seamLev seamLevHi 4 6 (fun s => (seamH1 ⟨s % 5, Nat.mod_lt _ (by norm_num)⟩).val) 0 = 0 ∧
      bingSpecialFCbot 5 seamLev seamLevHi 4 6
        (fun s => (seamH1 ⟨s % 5, Nat.mod_lt _ (by norm_num)⟩).val) 1 = 2 := by
  decide

end HPC.Fold.Recon121
