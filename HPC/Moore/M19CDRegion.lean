import HPC.Moore.M19CDMain

/-!
# Moore 1919, Theorem D: the curve form gives the region form (batch 141, ledger check 5)

In Theorem E (p. 176) Moore applies Theorem D to a set of *regions* (the fundamental regions), not
of closed curves. `m19_theoremD_regions_of_curves` shows that the curve form of Theorem D (as in the
skeleton) suffices for that use: if every set of closed curves whose interiors cover `ABCDA` and its
interior gives a double ruling of the interior of `ABCDA` with each subdivision within one of the
curves, then the same holds for every set of regions covering `ABCDA` and its interior. Each point
of a region is within a closed curve whose interior lies in the region (Theorem 36, in the form
`fa_theorem36_interior_subset`).

Theorem D itself is open in this batch (see `HPC/Moore/M19CD.lean` and `OPEN.md`), so this is a
relative result.
-/

namespace HPC.Moore

open Set

variable {S : Type*} {σ : Space S}

section Region

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Theorem D, region form, from the curve form.** If the conclusion of Theorem D holds for every
set `G` of closed curves (given as (curve, interior) pairs) whose interiors cover `ABCDA` and its
interior, then it holds for every set `𝒢` of regions covering `ABCDA` and its interior: the interior
of `ABCDA` has a double ruling each of whose subdivisions lies in some region of `𝒢`.
*Axioms used: 1–8.* -/
theorem m19_theoremD_regions_of_curves (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (hD : ∀ G : Set (Set S × Set S), (∀ p ∈ G, σ.IsInteriorOf p.1 p.2) →
      (∀ P ∈ J ∪ I, ∃ p ∈ G, P ∈ p.2) →
      ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∃ p ∈ G, U ⊆ p.2)
    (𝒢 : Set (Set S)) (h𝒢 : 𝒢 ⊆ σ.region) (hcov : ∀ P ∈ J ∪ I, ∃ V ∈ 𝒢, P ∈ V) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∃ V ∈ 𝒢, U ⊆ V := by
  let G : Set (Set S × Set S) := {p | σ.IsInteriorOf p.1 p.2 ∧ ∃ V ∈ 𝒢, p.2 ⊆ V}
  obtain ⟨n, m, R, hR⟩ := hD G (fun p hp => hp.1) (fun P hP => by
    obtain ⟨V, hV, hPV⟩ := hcov P hP
    obtain ⟨K, -, IK, hK, hPK, hKV⟩ :=
      fa_theorem36_interior_subset h1 h2 h3 h4 h5 h6 h7 h8 (h𝒢 hV) hPV
    exact ⟨(K, IK), ⟨hK, V, hV, hKV⟩, hPK⟩)
  refine ⟨n, m, R, fun U hU => ?_⟩
  obtain ⟨p, ⟨-, V, hV, hpV⟩, hUp⟩ := hR U hU
  exact ⟨V, hV, hUp.trans hpV⟩

end Region

end HPC.Moore
