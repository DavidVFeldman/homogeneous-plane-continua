import HPC.Moore.M25C6

/-!
# Batch 147: Moore 1925 §I, part 3 (Theorems 13–22): the space of elements is a plane

Delivery of the skeleton `doc/batches/skeletons/Moore1925III.lean` (commission
`doc/batches/COMMISSION-batch147.md`, report `doc/batches/REPORT-batch147.md`). The skeleton is split:

* `M25CDefs.lean`: the skeleton's definitions, verbatim;
* `TSCCCut.lean`: two arcs with only their ends in common are cut by any two points;
* `M25CInt.lean` (item A): `sccInterior_spec`, `isSCCElt_union`, `mooreRegion_of_restricted`,
  `isArcElt_iff_tarc`, `isSCCElt_iff_tscc`, and the hypotheses of the topological F.A. 24–27;
* `M25C13.lean` (item B): Theorems 13, 14;
* `M25C15.lean` (item C): Theorems 15–18;
* `M25C19.lean` (item D): Theorem 19;
* `M25C20.lean` (item E, part of F): Theorem 20, `spaceRestricted_topology`, Axioms 1–5, 8, 6′, 7′;
* `M25C6.lean` (item F): Axioms 6, 7, proved directly;
* this file (items F, G): Theorems 21, 22.

All statements are the skeleton's, verbatim.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Filter

variable {r : Setoid Pt}

/-- Homeomorphisms preserve accumulation points. -/
theorem accPt_iff_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (g : X ≃ₜ Y)
    (P : X) (M : Set X) : AccPt P (𝓟 M) ↔ AccPt (g P) (𝓟 (g '' M)) := by
  rw [accPt_iff_frequently, accPt_iff_frequently, ← g.map_nhds_eq, Filter.frequently_map]
  refine Filter.frequently_congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [ne_eq, g.injective.eq_iff, g.injective.mem_set_image]

section M25C

variable (hG : MooreDecomp r)
include hG

/-- **Theorem 21** (pp. 424–425). With the restricted regions, the space of elements satisfies
F.A.'s Axioms 1–8; along the way, Axioms 6′ and 7′ of Σ₂ (Moore's route to 6 and 7). -/
theorem m25_theorem21 :
    (spaceRestricted r).Axiom1 ∧ (spaceRestricted r).Axiom2 ∧ (spaceRestricted r).Axiom3 ∧
      (spaceRestricted r).Axiom4 ∧ (spaceRestricted r).Axiom5 ∧ (spaceRestricted r).Axiom6 ∧
      (spaceRestricted r).Axiom7 ∧ (spaceRestricted r).Axiom8 :=
  ⟨m25r_axiom1 hG, m25r_axiom2 hG, m25r_axiom3 hG, m25r_axiom4 hG, m25r_axiom5 hG,
    m25r_axiom6 hG, m25r_axiom7 hG, m25r_axiom8 hG⟩

/-- **Theorem 22** (p. 425), topological form: the space of elements is homeomorphic to the plane.
Moore 1919's main theorem (`m19_plane`, for Σ₁ = Axioms 1–8) applied to `spaceRestricted r`
(Theorem 21), transported along `spaceRestricted_topology`. -/
theorem m25_theorem22 : Nonempty (Quotient r ≃ₜ ℝ × ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m25_theorem21 hG
  have := m19_plane h1 h2 h3 h4 h5 h6 h7 h8
  rwa [spaceRestricted_topology hG] at this

/-- **Theorem 22**, Moore's form: a one-to-one correspondence between the elements of `G` and the
points of the plane such that a point `P` is a limit point of a point set `M` iff the corresponding
element is a limit element (in Moore's sense) of the set of elements corresponding to `M`. -/
theorem m25_theorem22_moore :
    ∃ e : Quotient r ≃ ℝ × ℝ, ∀ (P : ℝ × ℝ) (M : Set (ℝ × ℝ)),
      AccPt P (Filter.principal M) ↔ IsLimitElt (e.symm P) (e.symm '' M) := by
  obtain ⟨h⟩ := m25_theorem22 hG
  refine ⟨h.toEquiv, fun P M => ?_⟩
  rw [isLimitElt_iff hG]
  exact accPt_iff_homeomorph h.symm P M

end M25C

end HPC.Moore
