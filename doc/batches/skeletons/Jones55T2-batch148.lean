import HPC.Jones.Jones55
import HPC.Moore.M25C

/-!
# Batch 148 skeleton: Jones 1955 Theorem 2, modulo Jones 1949 Theorem 1

Save as `HPC/Jones/Jones55T2.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones55T2` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Sources: F. B. Jones, *On a certain type of homogeneous plane continuum*, Proc. AMS 6 (1955),
735–740, Theorem 2 and the closing remarks, pp. 739–740 (`doc/sources/jones1955.pdf`); F. B. Jones,
*Note on homogeneous plane continua*, Bull. AMS 55 (1949), 113–114 (`doc/sources/jones1949.pdf`).
Transcribed from page images at 200 dpi.

**Theorem 2** (p. 739). "Suppose that `M` is a homogeneous, decomposable, bounded, plane continuum.
Let `G` denote the collection of all subsets `g` of `M` such that for some point `x` of `M`, `g` is
`L_x`. Then `G` is a continuous collection of mutually exclusive continua filling up `M` such that
(1) with respect to its elements (as points), `G` is a simple closed curve, and (2) each element of
`G` is a homogeneous, bounded, plane continuum which does not separate the plane."

**Modelling.** `M : Set Pt` with `CompactSpace M`, `ConnectedSpace M` (bounded plane continuum),
so batch 136's `Lset`, `lSetoid`, `jones55_*` apply to the subtype. Elements are pushed to the plane
by `Subtype.val`. A simple closed curve is a space homeomorphic to `Circle`.

**Scope.** Everything except Jones 1949 Theorem 1, which enters as the hypothesis `Jones49Thm1`
(batches 149– prove it). The final theorem, `jones55_theorem2`, discharges nothing it cannot.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane HPC.Moore

/-! ## Jones 1949 Theorem 1, as a statement -/

/-- **Jones 1949, Theorem 1** (p. 113): "If a compact, plane continuum `M` is both homogeneous and
aposyndetic, then `M` is a simple closed curve." With `M` nondegenerate (see
`not_jones49_theorem1_point`). -/
def Jones49Thm1 : Prop :=
  ∀ K : Set Pt, IsCompact K → IsConnected K → K.Nontrivial → IsHomogeneous K → IsAposyndetic K →
    Nonempty (K ≃ₜ Circle)

/-- Jones 1949 Theorem 1 **as printed** is false for a one-point continuum (vacuously homogeneous and
aposyndetic, not a simple closed curve) — unless "continuum" excludes points in the convention of
the books Jones's footnote 3 refers to (Moore 1932, Whyburn 1942). Record the convention. -/
theorem not_jones49_theorem1_point :
    ¬ ∀ K : Set Pt, IsCompact K → IsConnected K → IsHomogeneous K → IsAposyndetic K →
      Nonempty (K ≃ₜ Circle) := by
  sorry

/-! ## The Jordan curve theorem in the plane, from Moore 1925 Theorem 11 -/

/-- **The Jordan curve theorem**, from `m25_theorem11` for the decomposition into points and the
equivalence of `IsSCCElt` with topological circles (batch 147). Needed by Jones 1949 (Case 1, Case 2)
and convenient for the exposition. -/
theorem jordan_curve_theorem {J : Set Pt} (hJ : Nonempty (J ≃ₜ Circle)) :
    ∃ I E : Set Pt, IsOpen I ∧ IsConnected I ∧ IsOpen E ∧ IsConnected E ∧ Disjoint I E ∧
      I ∪ E = Jᶜ ∧ Bornology.IsBounded I ∧ ¬ Bornology.IsBounded E ∧ frontier I = J ∧
      frontier E = J := by
  sorry

/-! ## Plane separation is a topological invariant of plane compacta -/

/-- **Borsuk-type invariance** ("Since each two elements of `G` are homeomorphic, it follows that if
one element of `G` were to separate `S`, then each of them would separate `S`"): for compact plane
sets, separating the plane depends only on the homeomorphism type. -/
theorem separatesPlane_of_homeomorph {A B : Set Pt} (hA : IsCompact A) (hB : IsCompact B)
    (h : Nonempty (A ≃ₜ B)) (hsep : SeparatesPlane A) : SeparatesPlane B := by
  sorry

/-- The plane does not contain uncountably many mutually exclusive nonempty open sets. -/
theorem countable_of_pairwiseDisjoint_open {ι : Type*} {U : ι → Set Pt} (hU : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) (hd : Pairwise (Disjoint on U)) : Countable ι := by
  sorry

section T2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- The collection `G` is uncountable when `M` is homogeneous and decomposable (a nondegenerate
compact metric continuum of elements, `jones55_a`). -/
theorem uncountable_quotient (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Uncountable (Quotient (lSetoid M)) := by
  sorry

/-- "It is clear that for each `g` of `G`, `M − g` is connected." -/
theorem jones55_compl_connected (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) (x : M) :
    IsConnected (Lset x)ᶜ := by
  sorry

/-- **Theorem 2 (2), non-separation**: no element of `G` separates the plane. -/
theorem jones55_elt_not_separates (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) (x : M) :
    ¬ SeparatesPlane (Subtype.val '' Lset x) := by
  sorry

/-! ## The decomposition `G′` of the plane -/

/-- The relation of `G′`: `G` together with the singletons of `S − M`. -/
def gPrimeRel (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (x y : Pt) : Prop :=
  x = y ∨ ∃ (hx : x ∈ M) (hy : y ∈ M), (lSetoid M) ⟨x, hx⟩ ⟨y, hy⟩

theorem gPrimeRel_equivalence (M : Set Pt) [CompactSpace M] [ConnectedSpace M] :
    Equivalence (gPrimeRel M) := by
  sorry

/-- `G′` as a setoid on the plane. -/
def gPrime (M : Set Pt) [CompactSpace M] [ConnectedSpace M] : Setoid Pt :=
  ⟨gPrimeRel M, gPrimeRel_equivalence M⟩

/-- "Let `G′` denote the upper semi-continuous collection consisting of `G` together with each
degenerate subset of `S − M`": `G′` satisfies Moore's hypothesis (compact, connected,
non-separating elements; Moore's u.s.c.). -/
theorem mooreDecomp_gPrime (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    MooreDecomp (gPrime M) := by
  sorry

/-- "With respect to its elements (as points), `G′` is a plane [13]" — Moore 1925 Theorem 22. -/
theorem jones55_plane (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (Quotient (gPrime M) ≃ₜ ℝ × ℝ) := by
  sorry

/-- "… and `G` is a compact subcontinuum of `G′`": `M/G` is homeomorphic to a compact connected
plane set. -/
theorem jones55_embedding (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    ∃ K : Set Pt, IsCompact K ∧ IsConnected K ∧ Nonempty (Quotient (lSetoid M) ≃ₜ K) := by
  sorry

/-- Topological and metric aposyndesis agree (to move `jones55_a`'s `IsAposyndeticT` to the plane
copy of `M/G`, where Jones 1949 is stated with `IsAposyndetic`). -/
theorem isAposyndetic_iff_T {Y : Type*} [MetricSpace Y] : IsAposyndetic Y ↔ IsAposyndeticT Y := by
  sorry

/-! ## Theorem 2 -/

/-- **Jones 1955, Theorem 2**, assuming Jones 1949 Theorem 1. `G` is a continuous decomposition of
`M`; (1) `M/G` is a simple closed curve; (2) each element is a homogeneous plane continuum not
separating the plane. (Boundedness of the elements is that of `M`.) -/
theorem jones55_theorem2 (h49 : Jones49Thm1) (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    IsContinuousDecomp (lSetoid M) ∧ Nonempty (Quotient (lSetoid M) ≃ₜ Circle) ∧
      ∀ x : M, IsConnected (Lset x) ∧ IsHomogeneous (Lset x) ∧
        ¬ SeparatesPlane (Subtype.val '' Lset x) := by
  sorry

/-! ## The closing remarks (pp. 739–740): unnumbered claims -/

/-- p. 740: "every decomposable, homogeneous, bounded continuum in the plane must have exactly two
complementary domains (this follows from Theorem 2)". -/
theorem jones55_two_domains (h49 : Jones49Thm1) (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    ∃ U V : Set Pt, IsOpen U ∧ IsConnected U ∧ IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = Mᶜ := by
  sorry

/-- p. 739, Remarks: "Because each element of `G` in Theorem 2 is homogeneous and does not separate
the plane, each such element is indecomposable." -/
theorem jones55_elements_indecomposable (h49 : Jones49Thm1) (hX : IsHomogeneous M)
    (hd : IsDecomposableSpace M) (x : M) : ¬ IsDecomposableSpace (Lset x) := by
  sorry

/-- p. 740: "every homogeneous, bounded continuum in the plane having more than two complementary
domains is indecomposable and of Type 3" (Type 3, p. 735: "Those which separate the plane but are
indecomposable"). Stated: three pairwise distinct complementary components force indecomposability
(separation is then automatic). -/
theorem jones55_three_domains (h49 : Jones49Thm1) (hX : IsHomogeneous M)
    {a b c : Pt} (ha : a ∉ M) (hb : b ∉ M) (hc : c ∉ M)
    (hab : connectedComponentIn Mᶜ a ≠ connectedComponentIn Mᶜ b)
    (hac : connectedComponentIn Mᶜ a ≠ connectedComponentIn Mᶜ c)
    (hbc : connectedComponentIn Mᶜ b ≠ connectedComponentIn Mᶜ c) :
    ¬ IsDecomposableSpace M := by
  sorry

end T2

end HPC.Jones
