import HPC.PseudoArc.Theorem13
import HPC.Fold.Theorem7

/-!
# Bing 1951, *Snake-like continua*: Theorem 4, and a description in the plane

Skeleton for batch 84 (save as `HPC/Plane/Snake51.lean`; add `import HPC.Plane.Snake51` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. The definitions of rectangle
chains (`IsOpenRect`, `HasRoom`) and the auxiliary statement `exists_rect_chain_following` may be
reshaped with the change recorded; `theorem4`, `exists_description_plane` and `pseudoArc_exists`
keep their conclusions.

The plane is `ℝ × ℝ` with its product (sup) metric; this changes no topology. If Euclidean
distance is preferred, record the change.
-/

namespace HPC.Plane

open Set

/-- The plane. -/
abbrev Pt := ℝ × ℝ

/-- An open axis-parallel rectangle of positive size. -/
def IsOpenRect (S : Set Pt) : Prop :=
  ∃ a b c d : ℝ, a < b ∧ c < d ∧ S = Ioo a b ×ˢ Ioo c d

/-- A chain *has room* if every link contains a point outside the closures of all other links.
(Invariant of the construction; may be replaced, COMMISSION-batch84.md §3.2.) -/
def HasRoom {n : ℕ} (D : Chain Pt n) : Prop :=
  ∀ i, (D.link i \ ⋃ j ∈ ({j | j ≠ i} : Set (Fin n)), closure (D.link j)).Nonempty

/-- A chain of open rectangles with room. -/
def IsRectChain {n : ℕ} (D : Chain Pt n) : Prop :=
  (∀ i, IsOpenRect (D.link i)) ∧ HasRoom D

/-- **The planar step** (Bing p. 654, "it can be shown that in the plane there is a sequence of
chains …", one level). Given a rectangle chain `D` of `m` links, a pattern `x : Fin n → Fin m`
onto and with unit steps, and `ε > 0`, there is a rectangle chain `D'` of `n` links, of mesh
`< ε`, with the closure of `D'_t` inside `D_{x t}`, and *tight*: `D'_t` meets `D_l` only for
`l = x t'` with `t'` within one of `t`. -/
theorem exists_rect_chain_following {m : ℕ} (D : Chain Pt m) (hD : IsRectChain D)
    {n : ℕ} (x : Fin n → Fin m) (hsurj : Function.Surjective x)
    (hlip : ∀ t t' : Fin n, t'.val = t.val + 1 → ((x t' : ℤ) - (x t : ℤ)).natAbs ≤ 1)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ D' : Chain Pt n, IsRectChain D' ∧
      (∀ t, Metric.diam (D'.link t) < ε) ∧
      (∀ t, closure (D'.link t) ⊆ D.link (x t)) ∧
      (∀ (t : Fin n) (l : Fin m), (D'.link t ∩ D.link l).Nonempty →
        ∃ t' : Fin n, (t'.val ≤ t.val + 1 ∧ t.val ≤ t'.val + 1) ∧ l = x t') := by
  sorry

/-- An `ε`-chain: bounded links of diameter less than `ε` (Bing 1951, §1). -/
def IsEpsChain {X : Type*} [MetricSpace X] {n : ℕ} (D : Chain X n) (ε : ℝ) : Prop :=
  ∀ i, Bornology.IsBounded (D.link i) ∧ Metric.diam (D.link i) < ε

/-- **Snake-like** (Bing 1951, §1): a (compact) continuum that is covered by an `ε`-chain for every
`ε > 0`. -/
def IsSnakeLike {X : Type*} [MetricSpace X] (M : Set X) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union

/-- **Bing 1951, Theorem 4.** Each snake-like continuum is homeomorphic with a plane continuum.
Proof: COMMISSION-batch84.md §2 and §3.5 (Bing 1948 Theorem 11, `MatchingCovers.exists_homeomorph`,
applied to a sequence of covering chains of `M` and a sequence of rectangle chains in the plane
following the same patterns). -/
theorem theorem4 {X : Type*} [MetricSpace X] {M : Set X} (hM : IsSnakeLike M) :
    ∃ N : Set Pt, Fold.Q78.IsContinuum N ∧ Nonempty (M ≃ₜ N) := by
  sorry

/-- **A description exists in the plane** (COMMISSION-batch84.md §3.4): rectangle chains following
Bing's crooked patterns `bingPattern`, crooked by `crooked_of_tight`. -/
theorem exists_description_plane :
    ∃ (P Q : Pt), P ≠ Q ∧ Nonempty (Description Pt P Q) := by
  sorry

/-- **The pseudo-arc is a homogeneous hereditarily indecomposable nondegenerate plane continuum.**
From `exists_description_plane` with `Description.isContinuum_M`, `theorem10`, `theorem13`. -/
theorem pseudoArc_exists :
    ∃ M : Set Pt, Fold.Q78.IsContinuum M ∧ M.Nontrivial ∧
      (∀ K : Set Pt, K ⊆ M → Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K) ∧
      ∀ (p q : Pt) (hp : p ∈ M) (hq : q ∈ M), ∃ T : M ≃ₜ M, T ⟨p, hp⟩ = ⟨q, hq⟩ := by
  sorry

end HPC.Plane
