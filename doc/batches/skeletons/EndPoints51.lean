import HPC.Plane.Snake51
import HPC.PseudoArc.Theorem14

/-!
# Bing 1951, §4 Theorem 10 and §5 (end points of snake-like continua)

Skeleton for batch 85 (save as `HPC/Plane/EndPoints51.lean`; add `import HPC.Plane.EndPoints51` to
the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted
with the change recorded.

`IsSnakeLike`, `IsEpsChain` are from `Snake51.lean`; `IsIrreducibleBetween` from
`PseudoArc/Theorem14.lean`; `Fold.Q78.IsContinuum`, `IsIndecomposable` from `Fold/Questions78.lean`.
Bing's "chain from `p` to `q`" is `Chain.IsFrom p q`. Conditions A, B, C are stated for a point
`p` of a set `M`.
-/

namespace HPC.Plane

open Set

variable {X : Type*} [MetricSpace X]

/-- **Condition A** (Bing 1951, p. 659): each nondegenerate subcontinuum of `M` containing `p` is
irreducible from `p` to some other point. -/
def CondA (M : Set X) (p : X) : Prop :=
  p ∈ M ∧ ∀ W : Set X, W ⊆ M → Fold.Q78.IsContinuum W → W.Nontrivial → p ∈ W →
    ∃ q, q ≠ p ∧ IsIrreducibleBetween W p q

/-- **Condition B**: of two subcontinua of `M` containing `p`, one contains the other. -/
def CondB (M : Set X) (p : X) : Prop :=
  p ∈ M ∧ ∀ H K : Set X, H ⊆ M → K ⊆ M → Fold.Q78.IsContinuum H → Fold.Q78.IsContinuum K →
    p ∈ H → p ∈ K → H ⊆ K ∨ K ⊆ H

/-- **Condition C — end point**: for every `ε > 0` there is an `ε`-chain covering `M` in which
only the first link contains `p`. -/
def IsEndPoint (M : Set X) (p : X) : Prop :=
  p ∈ M ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), IsEpsChain E ε ∧ M ⊆ E.union ∧
    p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ E.link j

/-- **Opposite end points**: for every `ε > 0` there is an `ε`-chain from `p` to `q` covering `M`. -/
def OppositeEndPoints (M : Set X) (p q : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (E : Chain X n), IsEpsChain E ε ∧ M ⊆ E.union ∧ E.IsFrom p q

/-- Hereditarily indecomposable: every subcontinuum is indecomposable. -/
def IsHereditarilyIndecomposable (M : Set X) : Prop :=
  ∀ K : Set X, K ⊆ M → Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K

/-- **Bing 1951, Theorem 10.** If `D` covers the compact continuum `M` and `p ∈ M` satisfies
condition A, some refinement `E` of `D` covers `M` with `p` in its first link and in the closure
of no other link. Proof: COMMISSION-batch85.md §2, with the claims of §3.6 to be checked. -/
theorem theorem10_1951 {M : Set X} (hM : Fold.Q78.IsContinuum M) {m : ℕ} (D : Chain X m)
    (hD : M ⊆ D.union) {p : X} (hp : CondA M p) :
    ∃ (n : ℕ) (E : Chain X n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
      p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j) := by
  sorry

/-- **Theorem 12, direction A ⇒ B** (the other direction rests on an external result). -/
theorem condB_of_condA {M : Set X} (hM : Fold.Q78.IsContinuum M) {p : X} (hp : CondA M p) :
    CondB M p := by
  sorry

/-- **Theorem 13, sufficiency for condition A** (via Theorem 10): in a snake-like continuum a
point satisfying condition A is an end point. -/
theorem endPoint_of_condA {M : Set X} (hM : IsSnakeLike M) {p : X} (hp : CondA M p) :
    IsEndPoint M p := by
  sorry

/-- **Theorem 13, necessity**: an end point satisfies condition B. (COMMISSION-batch85.md §3.4.) -/
theorem condB_of_endPoint {M : Set X} (hM : Fold.Q78.IsContinuum M) {p : X} (hp : IsEndPoint M p) :
    CondB M p := by
  sorry

/-- **Bing 1951, Theorem 14.** A snake-like continuum irreducible between two of its end points
has them as opposite end points. -/
theorem theorem14_1951 {M : Set X} (hM : IsSnakeLike M) {p q : X} (hp : IsEndPoint M p)
    (hq : IsEndPoint M q) (hirr : IsIrreducibleBetween M p q) : OppositeEndPoints M p q := by
  sorry

/-- **Bing 1951, Theorem 15**, with the nondegeneracy implicit in Bing's construction made
explicit: a nondegenerate snake-like continuum contains a nondegenerate snake-like continuum with
two distinct opposite end points. -/
theorem theorem15_1951 {M : Set X} (hM : IsSnakeLike M) (hnd : M.Nontrivial) :
    ∃ N : Set X, N ⊆ M ∧ IsSnakeLike N ∧ N.Nontrivial ∧
      ∃ p q : X, p ≠ q ∧ OppositeEndPoints N p q := by
  sorry

/-- **Theorem 16, the self-contained half of sufficiency**: if the continuum `M` is not
hereditarily indecomposable, some point of `M` is not an end point of `M`. (With Theorem 1 of
Bing's *Concerning hereditarily indecomposable continua* — external — this gives Bing's
Theorem 16.) -/
theorem exists_not_endPoint_of_not_HI {M : Set X} (hM : Fold.Q78.IsContinuum M)
    (h : ¬ IsHereditarilyIndecomposable M) : ∃ p ∈ M, ¬ IsEndPoint M p := by
  sorry

end HPC.Plane
