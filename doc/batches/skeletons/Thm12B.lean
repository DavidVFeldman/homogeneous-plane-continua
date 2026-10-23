import HPC.Plane.Theorem11B

/-!
# Batch 106: Bing 1951 (Duke) Theorem 12 (B ⇒ A), Theorem 13 in full, and the unnumbered
# "two end points" claim of §5

Skeleton (save as `HPC/Plane/Thm12B.lean`; add `import HPC.Plane.Thm12B` to the root `HPC.lean`).
Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the change
recorded. No existing file is to be edited.

Bing's proof of B ⇒ A cites "Theorem 5 of [4]" (his arcs paper, not available). The repository
has what replaces it: condition B at `p` says `{p}` is a terminal subcontinuum of `M'`
(`isTerminalSub_singleton_iff`), and Fugate's Lemma 3 (⇒) (`isTerminalSub_iff_irreducible`, for
atriodic hereditarily unicoherent `M'`) makes `M' = {p} ∪ M'` irreducible between a point of `{p}`
and another point. Snake-like continua are atriodic and hereditarily unicoherent (batch 96), and
subcontinua of snake-like continua are snake-like.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Theorem 12, B ⇒ A** (Bing 1951, p. 661), for snake-like `M`. -/
theorem condA_of_condB {M : Set S} (hM : IsSnakeLike M) {p : S} (hp : CondB M p) : CondA M p := by
  sorry

/-- **Theorem 12** (both directions; A ⇒ B is batch 85's `condB_of_condA`). -/
theorem theorem12_1951 {M : Set S} (hM : IsSnakeLike M) (p : S) : CondA M p ↔ CondB M p := by
  sorry

/-- **Theorem 13** (Bing 1951, p. 661): a point of a snake-like continuum is an end point iff it
satisfies condition A iff it satisfies condition B. Necessity is batch 85's `condB_of_endPoint`;
sufficiency for A is `endPoint_of_condA` (batch 99); B via Theorem 12. -/
theorem theorem13_1951 {M : Set S} (hM : IsSnakeLike M) (p : S) :
    IsEndPoint M p ↔ CondA M p := by
  sorry

theorem theorem13_1951' {M : Set S} (hM : IsSnakeLike M) (p : S) :
    IsEndPoint M p ↔ CondB M p := by
  sorry

/-- **The unnumbered claim after Theorem 13** (p. 661): "We find from Theorems 8, 9, and 13 that
each hereditarily decomposable snake-like continuum contains two end points between which it is
irreducible." For the whole space: `S` snake-like and hereditarily decomposable (hence `BingS`),
there are end points `p ≠ q` with `S` irreducible between them. (Route: two end elements
(`exists_two_endElts`), a condition-A point in each (`theorem9_1951`), end points by Theorem 13,
irreducibility by Theorem 8 (c) (`bingElt_irreducible`).) -/
theorem exists_two_endPoints_irreducible [ConnectedSpace S] [Nontrivial S]
    (hsn : IsSnakeLike (univ : Set S)) (hd : IsHereditarilyDecomposable (univ : Set S)) :
    ∃ p q : S, p ≠ q ∧ IsEndPoint (univ : Set S) p ∧ IsEndPoint (univ : Set S) q ∧
      IsIrreducibleBetween (univ : Set S) p q := by
  sorry

/-- With Theorem 14 (batch 85, `theorem14_1951`): such `p`, `q` are opposite end points. -/
theorem exists_oppositeEndPoints_of_hd [ConnectedSpace S] [Nontrivial S]
    (hsn : IsSnakeLike (univ : Set S)) (hd : IsHereditarilyDecomposable (univ : Set S)) :
    ∃ p q : S, p ≠ q ∧ OppositeEndPoints (univ : Set S) p q := by
  sorry

end HPC.Plane
