import HPC.Moore.M19CD
import HPC.Moore.M19DThm

/-!
# Batch 142: Moore 1919, Theorem C corrected; Theorem D

The batch-142 skeleton (kept verbatim at `doc/batches/skeletons/Moore1919CD2.lean`) is split as
follows.

| skeleton item | file | outcome |
|---|---|---|
| `Space.IsCrossCut` | this file | verbatim |
| `m19_theoremC_crosscuts` | this file, from `chords_rulable` (`M19DChords.lean`) | proved |
| `m19_theoremC_within` | this file, from `inside_rulable` (`M19DInside.lean`) | proved |
| `m19_theoremC_corrected` | this file, from `curve_rulable` (`M19DThm.lean`) | proved |
| `m19_theoremD` | `M19DThm.lean` | proved |
| (added) `m19_theoremD_regions` | this file, from `m19_theoremD_regions_of_curves` | proved |

The supporting files, in import order: `M19DGlue`, `M19DDefs`, `M19DPocket`, `M19DOuter`,
`M19DWeight`, `M19DCorner`, `M19DChords` (a ruling missing finitely many disjoint chords),
`M19DInside` (a closed curve within `ABCDA`), `M19DExtract` (the chords of a closed curve),
`M19DLens` (lenses about the points of `J`), `M19DNice` (a curve about a compact set crossing `J`
at each common point), `M19DThm` (Theorem D).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- A *cross-cut* of the quadrilateral: an arc whose open part lies within `ABCDA` and whose ends lie
on `ABCDA`, distinct from `A, B, C, D`. -/
def Space.IsCrossCut (σ : Space S) (J I : Set S) (A B C D : S) (P Q : S) (K : Set S) : Prop :=
  σ.IsArc P Q K ∧ openArc P Q K ⊆ I ∧ P ∈ J ∧ Q ∈ J ∧ P ∉ ({A, B, C, D} : Set S) ∧
    Q ∉ ({A, B, C, D} : Set S)

section M19CD2

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- From a ruling given by its arcs to a double ruling: every subdivision is good and connected. -/
theorem Space.Rulable.toDoubleRuling (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) {Good : Set S → Prop}
    (H : σ.Rulable Good I sAB sBC sCD sDA A B C D) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, Good U ∧ @IsPreconnected S σ.topology U := by
  letI := σ.topology
  obtain ⟨𝒳, 𝒴, R, hR⟩ := H
  obtain ⟨R', hr₁, hr₂⟩ := R.toDoubleRuling h1 h2 h3 h4 h5 h7 h8 q
  refine ⟨_, _, R', fun U hU => ?_⟩
  rw [R'.cells_eq_cellsOf, R'.carrier_eq, hr₁, hr₂] at hU
  refine ⟨hR U hU, ?_⟩
  obtain ⟨z, -, rfl⟩ := hU
  exact isPreconnected_connectedComponentIn

/-- A connected set missing a closed curve lies within it or without it. -/
theorem side_of_disjoint (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h7 : σ.Axiom7) {g Ig U : Set S} (hg : σ.IsInteriorOf g Ig)
    (hU : @IsPreconnected S σ.topology U) (hUg : Disjoint U g) : U ⊆ Ig ∨ U ⊆ σ.ext Ig := by
  letI := σ.topology
  obtain ⟨hIo, -, -, -, hEo, -, -, -, -, -, -, hgc, -, -⟩ :=
    jordan h1 h2 h3 h4 (axiom5₁_of_axiom5 h5) h7 hg
  rw [ext_eq_compl_closure h1]
  exact hU.subset_or_subset hIo hEo (disjoint_compl_right.mono_left subset_closure)
    (by rw [← hgc]; exact fun z hz hzg => disjoint_left.mp hUg hz hzg)

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Theorem C, cross-cut form** (the core of the correction). A finite system of pairwise disjoint
cross-cuts (so with pairwise distinct ends) can be absorbed into a double ruling: there is a double
ruling whose subdivisions meet none of the cross-cuts. *Axioms used: 1–8.* -/
theorem m19_theoremC_crosscuts (q : σ.Quad J I A B C D sAB sBC sCD sDA) {k : ℕ}
    (P Q : Fin k → S) (K : Fin k → Set S) (hK : ∀ i, σ.IsCrossCut J I A B C D (P i) (Q i) (K i))
    (hdisj : ∀ i i', i ≠ i' → Disjoint (K i) (K i')) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∀ i, Disjoint U (K i) := by
  have h51 := axiom5₁_of_axiom5 h5
  have hc : ∀ t ∈ range K, σ.IsChord J I A B C D t := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨hKa, hKo, hP, hQ, hPn, hQn⟩ := hK i
    exact ⟨P i, Q i, ⟨hP, hPn⟩, ⟨hQ, hQn⟩, (isArc_iff_tarc h1 h3 h4 h51).mp hKa, hKo⟩
  have hd : (range K).Pairwise Disjoint := by
    rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩ hne
    exact hdisj i i' fun e => hne (e ▸ rfl)
  obtain ⟨n, m, R, hR⟩ := (chords_rulable h1 h2 h3 h4 h5 h6 h7 h8 q (finite_range K) hc
    hd).toDoubleRuling h1 h2 h3 h4 h5 h7 h8 q
  exact ⟨n, m, R, fun U hU i => (hR U hU).1.mono_right
    (subset_sUnion_of_mem (mem_range_self i))⟩

/-- **Theorem C, closed-curve-within form** (used in Theorem G, Fig. 3). A closed curve lying within
`ABCDA` can be absorbed into a double ruling. *Axioms used: 1–8.* The nine-cell form is not stated
(see the report). -/
theorem m19_theoremC_within (q : σ.Quad J I A B C D sAB sBC sCD sDA) {g Ig : Set S}
    (hg : σ.IsInteriorOf g Ig) (hgI : g ⊆ I) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, U ⊆ Ig ∨ U ⊆ σ.ext Ig := by
  obtain ⟨n, m, R, hR⟩ := (inside_rulable h1 h2 h3 h4 h5 h6 h7 h8 q hg hgI).toDoubleRuling
    h1 h2 h3 h4 h5 h7 h8 q
  exact ⟨n, m, R, fun U hU => side_of_disjoint h1 h2 h3 h4 h5 h7 hg (hR U hU).2 (hR U hU).1⟩

/-- **Theorem C, corrected.** As printed, with the touching configuration excluded: no point of
`g ∩ J` is a common end of two arcs of `g` whose open parts lie within `ABCDA`. Touching from
without is allowed. *Axioms used: 1–8.* The hypothesis `hfin` is used by the proof. -/
theorem m19_theoremC_corrected (q : σ.Quad J I A B C D sAB sBC sCD sDA) {g Ig : Set S}
    (hg : σ.IsInteriorOf g Ig) (hfin : (g ∩ J).Finite) (hA : A ∉ g) (hB : B ∉ g) (hC : C ∉ g)
    (hD : D ∉ g)
    (hnotouch : ∀ P ∈ g ∩ J, ∀ Q₁ Q₂ : S, ∀ K₁ K₂ : Set S, σ.IsArc P Q₁ K₁ → σ.IsArc P Q₂ K₂ →
      K₁ ⊆ g → K₂ ⊆ g → K₁ \ {P} ⊆ I → K₂ \ {P} ⊆ I → K₁ ∩ K₂ = {P} → False) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, U ⊆ Ig ∨ U ⊆ σ.ext Ig := by
  have h51 := axiom5₁_of_axiom5 h5
  have hcor : Disjoint g {A, B, C, D} := by
    rw [disjoint_left]
    intro z hz hzc
    simp only [mem_insert_iff, mem_singleton_iff] at hzc
    rcases hzc with rfl | rfl | rfl | rfl
    exacts [hA hz, hB hz, hC hz, hD hz]
  have H := curve_rulable h1 h2 h3 h4 h5 h6 h7 h8 q hg hfin hcor
    fun p hp m₁ m₂ M₁ M₂ hM₁ hM₂ h12 hMg hs₁ hs₂ =>
      hnotouch p hp m₁ m₂ M₁ M₂ ((isArc_iff_tarc h1 h3 h4 h51).mpr hM₁)
        ((isArc_iff_tarc h1 h3 h4 h51).mpr hM₂) (subset_union_left.trans hMg)
        (subset_union_right.trans hMg) hs₁ hs₂ h12
  obtain ⟨n, m, R, hR⟩ := H.toDoubleRuling h1 h2 h3 h4 h5 h7 h8 q
  exact ⟨n, m, R, fun U hU => side_of_disjoint h1 h2 h3 h4 h5 h7 hg (hR U hU).2 (hR U hU).1⟩

end M19CD2

section Regions

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Theorem D, region form** (as used in Theorem E): if each point on or within `ABCDA` lies in a
region of `𝒢`, the interior of `ABCDA` has a double ruling each of whose subdivisions lies in some
region of `𝒢`. From `m19_theoremD` and `m19_theoremD_regions_of_curves`. *Axioms used: 1–8.* -/
theorem m19_theoremD_regions (q : σ.Quad J I A B C D sAB sBC sCD sDA) (𝒢 : Set (Set S))
    (h𝒢 : 𝒢 ⊆ σ.region) (hcov : ∀ P ∈ J ∪ I, ∃ V ∈ 𝒢, P ∈ V) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∃ V ∈ 𝒢, U ⊆ V :=
  m19_theoremD_regions_of_curves h1 h2 h3 h4 h5 h6 h7 h8 q
    (fun G hG hc => m19_theoremD h1 h2 h3 h4 h5 h6 h7 h8 q G hG hc) 𝒢 h𝒢 hcov

end Regions


end HPC.Moore
