import HPC.Hagopian.Hagopian76AB

/-!
# Batch 184 skeleton: Hagopian 1976, Theorem 1 by Jones's plan (Hagopian 1984)

Save as `HPC/Hagopian/Hagopian84A.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian84A` at the end of `HPC.lean`. Every `sorry` is a work item. Items
stated as `True` are *shape left to you*; quote the printed sentence each renders, and record each
shape in the report. Unproved items are commented out with an `OPEN` note, as before. Every theorem
with a named `Prop` among its hypotheses gets a non-vacuity note.

Source: C. L. Hagopian, *Atriodic homogeneous continua*, Pacific J. Math. 113 (1984), 333–347
(`doc/sources/hagopian1984.pdf`; journal page = PDF page + 331). Route: commission 184 §1.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §3. The named `Prop`s and the assembly -/

/-- **The arc step** (Bing 1960, the indecomposable case; F. B. Jones, Houston J. Math. 1 (1975)):
no indecomposable homogeneous plane continuum contains an arc. Named `Prop`; its source is decided
later (commission 184 §1, step 5). -/
def NoArcIndecHomPlane : Prop :=
  ∀ (Q : Set Pt) [CompactSpace Q] [ConnectedSpace Q], IsHomogeneous Q →
    ¬ IsDecomposableSpace Q → ∀ α : Set Q, ¬ Nonempty (α ≃ₜ unitInterval)

/-- **Jones's decomposition** (Hagopian 1984, p. 346: "Find a monotone decomposition `𝔇` of `M`
such that `M/𝔇` is a homogeneous plane continuum that contains an arc"), from Theorem 1 (p. 342)
with `N = M`, for a plane `M`. The quotient is given as a map `q`: continuous, onto, with connected
fibres, each fibre a proper subset of `M`; the quotient is homogeneous and contains an arc.
Planarity of the quotient is not asked here: it is proved in the assembly (Moore 1925).
*The shape may be adjusted* (commission 184 §3). -/
def Hagopian84Decomp : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M →
    ¬ IsDecomposableSpace M → ¬ IsHereditarilyIndecomposable (univ : Set M) →
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompactSpace Y) (q : M → Y),
      Continuous q ∧ Function.Surjective q ∧ (∀ y, IsConnected (q ⁻¹' {y})) ∧
        (∀ y, q ⁻¹' {y} ≠ univ) ∧ IsHomogeneous Y ∧ ∃ α : Set Y, Nonempty (α ≃ₜ unitInterval)

/-- **§3, the plane quotient** (Moore 1925 Theorem 22, as in `exists_quotient_plane`): for `q` as
in `Hagopian84Decomp`, some compact plane continuum is homeomorphic to `Y`. *Shape left to you.* -/
theorem exists_plane_quotient_of_monotone : True := by
  sorry

/-- **§3, monotone images**: a monotone image of an indecomposable continuum is indecomposable.
*Shape left to you.* -/
theorem indecomposable_of_monotone_image : True := by
  sorry

/-- **§3, the assembly** (Hagopian 1984, p. 346, Corollary 3 by Jones's plan): Theorem 1 of 1976
from Jones's decomposition and the arc step. -/
theorem hagopian76_theorem1_of_jones (hD : Hagopian84Decomp) (hA : NoArcIndecHomPlane) :
    Hagopian76Thm1 := by
  sorry

/-- **§3, Hagopian 1975 Theorem 1, paragraph 4 supplied** ("for otherwise, `E` would contain an arc
… and `M` would be a simple closed curve"): `hagopian75_theorem1_of_layer` without `hnd`, from
`NoArcIndecHomPlane` and `exists_arc_of_degenerate_layers`. *Shape left to you.* -/
theorem hagopian75_theorem1_of_noArc : True := by
  sorry

/-! ## §4. Lemmas 6–8, 10, 12–16 (setting: commission 184 §4) -/

/-- **Lemma 6** (p. 336): "If `H` is an essential subcontinuum of `E`, then `H` is a continuum of
type λ and every element of the decomposition of `H` is an element of the decomposition of `E`."
*Shape left to you.* -/
theorem hagopian84_lemma6 : True := by
  sorry

/-- **Lemma 7** (p. 336). *Shape left to you.* -/
theorem hagopian84_lemma7 : True := by
  sorry

/-- **Lemma 8** (p. 337). *Shape left to you.* -/
theorem hagopian84_lemma8 : True := by
  sorry

/-- **Lemma 10** (p. 338), if cheap (not needed with `N = M`). *Shape left to you.* -/
theorem hagopian84_lemma10 : True := by
  sorry

/-- **Lemma 12** (p. 339; Moore 1962 Theorem 44, p. 15). *Shape left to you.* -/
theorem hagopian84_lemma12 : True := by
  sorry

/-- **Lemma 13** (pp. 339–341). *Shape left to you.* -/
theorem hagopian84_lemma13 : True := by
  sorry

/-- **Lemma 14** (p. 341): the decomposition `Δ(𝒫)` of `(⋃𝒫)∖Cl(P₁ ∪ P₅)` is continuous.
*Shape left to you.* -/
theorem hagopian84_lemma14 : True := by
  sorry

/-- **Lemma 15** (p. 341). *Shape left to you.* -/
theorem hagopian84_lemma15 : True := by
  sorry

/-- **Lemma 16** (pp. 341–342): no element of the decomposition of an extension of `Cl K` away
from `X` meets three consecutive links. *Shape left to you.* -/
theorem hagopian84_lemma16 : True := by
  sorry

/-! ## §5. Theorem 1 with `N = M` -/

/-- **§5.7, an arc in `M/𝔇`** (p. 344: "Since `M/𝔇` is an atriodic homogeneous continuum that
contains an arc", unargued). *Shape left to you.* -/
theorem hagopian84_quotient_arc : True := by
  sorry

/-- **Theorem 1 with `N = M`** (pp. 342–345), in the plane: Jones's decomposition. -/
theorem hagopian84_decomp : Hagopian84Decomp := by
  sorry

/-- **Theorem 1 of 1976 by Jones's plan**, the strongest conditional form of this batch. -/
theorem hagopian76_theorem1_jones (hA : NoArcIndecHomPlane) : Hagopian76Thm1 :=
  hagopian76_theorem1_of_jones hagopian84_decomp hA

end HPC.Hagopian
