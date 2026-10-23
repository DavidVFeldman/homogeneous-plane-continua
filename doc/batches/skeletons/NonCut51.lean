import HPC.Plane.Atriodic51B

/-!
# Batch 94: Moore's non-cut-point theorem; the two end elements of Bing's decomposition

Skeleton (save as `HPC/Plane/NonCut51.lean`; add `import HPC.Plane.NonCut51` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded.

§1 is general topology (Nadler, *Continuum Theory*, 6.3, 6.4, 6.6, 6.7), stated for compact
connected `T₁` spaces — no metric. §2 applies it to Bing's decomposition `G = {bingElt p}` of a
space satisfying `BingS`: an element is an *end element* (`IsEndElt`, batch 93: it separates no
two other elements) if and only if it is a non-cut element, and there are two of them. §3 is
reconnaissance: hereditary transfer of `BingS` to a subcontinuum, and the elements of a
subcontinuum.
-/

namespace HPC.Plane

open Set Topology

/-! ## §1. Non-cut points (Nadler Ch. VI) -/

section NonCut

variable {X : Type*} [TopologicalSpace X]

/-- `Y = P | Q` in Nadler's notation: `P`, `Q` nonempty, disjoint, open in `Y`, with union `Y`.
Stated for subsets of `X` with openness relative to `Y`. -/
def IsSeparation (Y P Q : Set X) : Prop :=
  P.Nonempty ∧ Q.Nonempty ∧ Disjoint P Q ∧ P ∪ Q = Y ∧ IsOpen (Y := Y) ((↑) ⁻¹' P) ∧
    IsOpen (Y := Y) ((↑) ⁻¹' Q)

/-- A *cut point* of the space: its complement is disconnected. -/
def IsCutPoint (x : X) : Prop := ¬ IsConnected ({x}ᶜ : Set X)

/-- **Nadler 6.3.** If `S` is connected, `C ⊆ S` connected and `S ∖ C = A | B`, then `A ∪ C` is
connected. -/
theorem isConnected_union_of_separation [ConnectedSpace X] {C A B : Set X} (hC : IsConnected C)
    (hAB : IsSeparation Cᶜ A B) : IsConnected (A ∪ C) := by
  sorry

/-- **Nadler 6.4.** If `S ∖ {x} = K | L`, `S ∖ {y} = M | N`, `x ∈ M`, `y ∈ K`, then
`N ∪ {y} ⊆ K`. -/
theorem nadler_6_4 [ConnectedSpace X] {x y : X} {K L M N : Set X}
    (hx : IsSeparation {x}ᶜ K L) (hy : IsSeparation {y}ᶜ M N) (hxM : x ∈ M) (hyK : y ∈ K) :
    N ∪ {y} ⊆ K := by
  sorry

/-- **Nadler 6.6 (Moore's non-cut-point existence theorem).** In a nondegenerate compact connected
`T₁` space with a cut point `c`, `S ∖ {c} = U | V`, there is a non-cut point in `U` and one in
`V`. -/
theorem exists_nonCutPoint_of_cut [CompactSpace X] [ConnectedSpace X] [T1Space X] [Nontrivial X]
    {c : X} {U V : Set X} (h : IsSeparation {c}ᶜ U V) :
    (∃ u ∈ U, ¬ IsCutPoint u) ∧ (∃ v ∈ V, ¬ IsCutPoint v) := by
  sorry

/-- **Nadler 6.6, second clause**: a nondegenerate compact connected `T₁` space has two non-cut
points. -/
theorem exists_two_nonCutPoints [CompactSpace X] [ConnectedSpace X] [T1Space X] [Nontrivial X] :
    ∃ a b : X, a ≠ b ∧ ¬ IsCutPoint a ∧ ¬ IsCutPoint b := by
  sorry

/-- **Nadler 6.7.** No proper connected subset contains all the non-cut points. -/
theorem not_subset_of_nonCutPoints [CompactSpace X] [ConnectedSpace X] [T1Space X] [Nontrivial X]
    {Z : Set X} (hZ : IsConnected Z) (hne : Z ≠ univ) : ¬ {x | ¬ IsCutPoint x} ⊆ Z := by
  sorry

end NonCut

/-! ## §2. End elements of Bing's decomposition -/

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- An element is a *cut element* when its complement is disconnected. -/
def IsCutElt (r : S) : Prop := ¬ IsConnected ((bingElt r)ᶜ)

/-- **End element ⇔ non-cut element.** (⇒: a separation of `S ∖ g_r` contains a whole element on
each side, since elements are connected and disjoint from `g_r`; those two elements are then
separated by `g_r` in the sense of `Separates`. ⇐: `Separates` exhibits the separation.) -/
theorem isEndElt_iff_not_isCutElt (hS : BingS S) (r : S) : IsEndElt r ↔ ¬ IsCutElt r := by
  sorry

/-- **The decomposition space** `S / G`, with the quotient topology, is compact, connected, `T₁`
and nondegenerate. (`T₁`: a class is closed in the quotient iff its preimage, the element, is
closed in `S`. Nondegenerate: by Theorem 8 (b), no element is all of `S`.) The space may be
replaced by a saturated-set argument inside `S` if that is shorter; then this statement is
dropped and the change recorded. -/
theorem decompositionSpace_props (hS : BingS S) :
    CompactSpace (Quotient (Setoid.ker (bingElt (S := S)))) ∧
    ConnectedSpace (Quotient (Setoid.ker (bingElt (S := S)))) ∧
    T1Space (Quotient (Setoid.ker (bingElt (S := S)))) ∧
    Nontrivial (Quotient (Setoid.ker (bingElt (S := S)))) := by
  sorry

/-- A cut element of `S` is a cut point of the decomposition space, and conversely. -/
theorem isCutElt_iff_isCutPoint_quot (hS : BingS S) (r : S) :
    IsCutElt r ↔ IsCutPoint (Quotient.mk (Setoid.ker (bingElt (S := S))) r) := by
  sorry

/-- **Two end elements** (Bing, Theorem 11: "`g_1` and `g_2` are the end elements of `G`"; the
existence is Moore's theorem applied to the decomposition space). -/
theorem exists_two_endElts (hS : BingS S) :
    ∃ a b : S, bingElt a ≠ bingElt b ∧ IsEndElt a ∧ IsEndElt b := by
  sorry

/-- **Nadler 6.7 for elements**: no proper subcontinuum of `S` meets every end element — the form
in which Theorem 8 (c) is used in Theorem 11. -/
theorem not_subset_of_endElts (hS : BingS S) {Z : Set S} (hZ : Fold.Q78.IsContinuum Z)
    (hne : Z ≠ univ) : ∃ r : S, IsEndElt r ∧ Disjoint (bingElt r) Z := by
  sorry

/-! ## §3. Reconnaissance: `BingS` on a subcontinuum; the elements of a subcontinuum -/

/-- **Hereditary transfer.** A nondegenerate subcontinuum `S'` of `S`, as a subtype, satisfies
Bing's standing hypothesis. (Atriodic, hereditarily unicoherent and hereditarily decomposable are
hereditary by definition; what has to be checked is the passage between subsets of the subtype and
subsets of `S`: continua of `S'` are the continua of `S` inside `S'`, and `IsTriod` transfers.) -/
theorem bingS_subcontinuum (hS : BingS S) {S' : Set S} (hS' : Fold.Q78.IsContinuum S')
    (hnd : S'.Nontrivial) : BingS S' := by
  sorry

/-- **Elements of a subcontinuum lie in elements of `S`** (report 93, §3, route 1: "a continuum
containing `x` doubly interiorly in `S`, intersected with `S'`, does the same in `S'`, by
unicoherence"). Prove or refute. -/
theorem bingElt_subtype_subset (hS : BingS S) {S' : Set S} (hS' : Fold.Q78.IsContinuum S')
    (hnd : S'.Nontrivial) (x : S') :
    ((↑) : S' → S) '' bingElt x ⊆ bingElt (x : S) := by
  sorry

end HPC.Plane
