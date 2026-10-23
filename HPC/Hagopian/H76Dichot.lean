import HPC.Hagopian.Hagopian76E
import HPC.Jones.Basic

/-!
# Batch 169, item C: the dichotomy for `R(E)`

* `RsetDichotomy k`: if a homeomorphism `g` of `M` carries `R(E)` onto a set meeting `R(E)`, then
  `g[R(E)] = R(E)`. Hagopian uses it tacitly on pp. 347–349 (report 168 §1.A). Stated as a `Prop`
  (commission 169 §2.C.3).
* `image_composant`: a homeomorphism carries composants onto composants.
* `Rset_dichotomy_of_closure_aux` (commission 169 §1.2): if `Cl R(E) = M`, then `R(E)` is a
  composant of `M` (`hagopian76_Rset_composant`), so is `g[R(E)]`, and composants sharing a point
  are equal — the dichotomy holds.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

variable {M : Set Pt}

/-- **The dichotomy for `R(E)`** (used tacitly on pp. 347–349), as a `Prop`. -/
def RsetDichotomy {E : Set M} (k : E → unitInterval) : Prop :=
  ∀ g : M ≃ₜ M, (g '' Rset k ∩ Rset k).Nonempty → g '' Rset k = Rset k

/-- A homeomorphism of `M` carries the composant of `x` onto the composant of `g x`. -/
theorem image_composant (g : M ≃ₜ M) (x : M) :
    g '' Jones.composant x = Jones.composant (g x) := by
  have key : ∀ (g : M ≃ₜ M) (x : M), g '' Jones.composant x ⊆ Jones.composant (g x) := by
    rintro g x _ ⟨y, ⟨K, hK, hKu, hxK, hyK⟩, rfl⟩
    refine ⟨g '' K, isContinuum_homeo_image g hK, fun h => hKu ?_, mem_image_of_mem g hxK,
      mem_image_of_mem g hyK⟩
    have : g.symm '' (g '' K) = K := g.symm_image_image K
    rw [← this, h, image_univ, g.symm.range_coe]
  refine Subset.antisymm (key g x) ?_
  intro z hz
  have h1 := key g.symm (g x) (mem_image_of_mem g.symm hz)
  rw [g.symm_apply_apply] at h1
  exact ⟨g.symm z, h1, g.apply_symm_apply z⟩

/-- **Under the dichotomy, a translate through a point off `R(E)` misses `R(E)`** (report 168
§1.A, condition 3 of the weakest T12): if `x ∈ R(E)` and `g(x) ∉ R(E)`, then
`g[R(E)] ∩ R(E) = ∅`. -/
theorem disjoint_image_Rset {E : Set M} {k : E → unitInterval} (hD : RsetDichotomy k)
    (g : M ≃ₜ M) {x : M} (hx : x ∈ Rset k) (hgx : g x ∉ Rset k) :
    Disjoint (g '' Rset k) (Rset k) := by
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro hne
  exact hgx (hD g hne ▸ mem_image_of_mem g hx)

variable [CompactSpace M] [ConnectedSpace M]

/-- **The dichotomy, if `Cl R(E) = M`** (commission 169 §1.2, route C.1). -/
theorem Rset_dichotomy_of_closure_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hcl : closure (Rset k) = univ) : RsetDichotomy k := by
  have hcomp : ∀ y ∈ Rset k, Rset k = Jones.composant y := fun y hy => by
    rw [hagopian76_Rset_composant hX hi hE hy, hcl, composant_eq_composant_univ]
  rintro g ⟨z, ⟨y, hy, rfl⟩, hz⟩
  calc g '' Rset k = g '' Jones.composant y := by rw [← hcomp y hy]
    _ = Jones.composant (g y) := image_composant g y
    _ = Rset k := (hcomp (g y) hz).symm

end HPC.Hagopian
