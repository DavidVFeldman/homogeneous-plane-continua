import HPC.Plane.Thm12B

/-!
# Batch 107: Bing 1951 (Duke) Theorem 5 — uncountably many disjoint plane copies of a snake-like
# continuum

Skeleton (save as `HPC/Plane/Thm5.lean`; add `import HPC.Plane.Thm5` to the root `HPC.lean`).
Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the change
recorded. No existing file is to be edited, except the audit (`Axioms.lean`, `axioms.txt`).

Bing (p. 655): *If `M` is a snake-like continuum, there is an uncountable collection `W` of
mutually exclusive continua in the plane such that each element of `W` is homeomorphic with
`M`.* His proof cites Theorem 1 of Moore [10]. Here instead: the construction of Theorem 4
(`T4.lean`: a sequence of `TStage`s, `tN = ⋂ D_i^*`, `exists_homeomorph_tN`) is run along a
binary tree. At each level the tame chain `Φ(stdRect j)` is first squeezed into two disjoint
sub-strips of itself — lower, `y ↦ (y + 1/2)/3`, and upper, `y ↦ (y + 7/4)/3`, both affine
homeomorphisms of the plane carrying `stdRect j` into `stdRect j` with closure inside — and the
step of Theorem 4 (`t4_step`) is then taken inside each. A branch `b : ℕ → Bool` selects a strip at
each level; its intersection `tN b` is homeomorphic to `M` by the argument of
`exists_homeomorph_tN`, and two branches that differ first at level `i` have level-`(i+1)` chains
with disjoint unions, so their continua are disjoint.
-/

namespace HPC.Plane

open Set Topology Metric

variable {X : Type*} [MetricSpace X]

/-- The lower squeeze `(x, y) ↦ (x, (y + 1/2)/3)` and the upper squeeze
`(x, y) ↦ (x, (y + 7/4)/3)`, as homeomorphisms of the plane. -/
noncomputable def squeeze (b : Bool) : Pt ≃ₜ Pt := sorry

theorem squeeze_stdRect_subset (b : Bool) (j : ℕ) :
    closure (squeeze b '' stdRect j) ⊆ stdRect j := by
  sorry

theorem squeeze_disjoint (j j' : ℕ) :
    Disjoint (squeeze false '' stdRect j) (squeeze true '' stdRect j') := by
  sorry

/-- **One branching step.** From a stage `S` and a bit `b`, a stage `S'` with the properties of
`t4_step` (refinement of `S.C` and of the tame chain, surjective block map, mesh `< ε`, the
slowness/zone clause) and in addition: every link of the new tame chain lies in
`S.Φ '' (squeeze b '' stdRect (x t))`. The two choices of `b` give tame chains with disjoint
unions. -/
theorem t4_step_branch {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (S : TStage M) (b : Bool) {ε : ℝ} (hε : 0 < ε) :
    ∃ S' : TStage M, ∃ x : Fin S'.m → Fin S.m,
      (∀ t, S'.C.link t ⊆ S.C.link (x t)) ∧
      (∀ t, closure ((tameChain S'.Φ S'.m).link t) ⊆ S.Φ '' (squeeze b '' stdRect (x t))) ∧
      Function.Surjective x ∧
      (∀ t, Bornology.IsBounded (S'.C.link t) ∧ diam (S'.C.link t) < ε) ∧
      (∀ k : ℕ, k < S'.m → Bornology.IsBounded (S'.Φ '' zone k) ∧ diam (S'.Φ '' zone k) ≤ ε) := by
  sorry

/-- **The tree of stages**: `tstageTree b i` is the stage reached after following the first `i`
bits of `b`; it depends only on those bits. -/
noncomputable def tstageTree {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b : ℕ → Bool) : ℕ → TStage M := sorry

theorem tstageTree_prefix {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b b' : ℕ → Bool) (i : ℕ) (h : ∀ k < i, b k = b' k) :
    tstageTree hMc hMconn hsnake b i = tstageTree hMc hMconn hsnake b' i := by
  sorry

/-- The plane continuum of the branch `b`. -/
def tNb {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b : ℕ → Bool) : Set Pt :=
  ⋂ i, (tameChain (tstageTree hMc hMconn hsnake b i).Φ (tstageTree hMc hMconn hsnake b i).m).union

theorem isContinuum_tNb {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b : ℕ → Bool) : Fold.Q78.IsContinuum (tNb hMc hMconn hsnake b) := by
  sorry

/-- Each branch is homeomorphic to `M` (the argument of `exists_homeomorph_tN`, which should be
factored so that it applies to any sequence of stages with the `t4_step` properties). -/
theorem exists_homeomorph_tNb {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    (b : ℕ → Bool) : Nonempty (M ≃ₜ tNb hMc hMconn hsnake b) := by
  sorry

/-- Branches differing at some bit give disjoint continua. -/
theorem tNb_disjoint {M : Set X} (hMc : IsCompact M) (hMconn : IsConnected M)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n),
      (∀ i, Bornology.IsBounded (D.link i) ∧ diam (D.link i) < ε) ∧ M ⊆ D.union)
    {b b' : ℕ → Bool} (h : b ≠ b') : Disjoint (tNb hMc hMconn hsnake b) (tNb hMc hMconn hsnake b') := by
  sorry

/-- **Bing 1951, Theorem 5.** A family of pairwise disjoint plane continua indexed by `ℕ → Bool`
(hence of the cardinality of the continuum), each homeomorphic to `M`. -/
theorem theorem5_1951 {M : Set X} (hM : IsSnakeLike M) :
    ∃ W : (ℕ → Bool) → Set Pt, (∀ b, Fold.Q78.IsContinuum (W b) ∧ Nonempty (M ≃ₜ W b)) ∧
      ∀ b b', b ≠ b' → Disjoint (W b) (W b') := by
  sorry

/-- The collection is uncountable. -/
theorem theorem5_1951_uncountable {M : Set X} (hM : IsSnakeLike M) :
    ∃ 𝒲 : Set (Set Pt), ¬ 𝒲.Countable ∧ (∀ N ∈ 𝒲, Fold.Q78.IsContinuum N ∧ Nonempty (M ≃ₜ N)) ∧
      𝒲.PairwiseDisjoint id := by
  sorry

end HPC.Plane
