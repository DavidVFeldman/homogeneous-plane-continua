import HPC.Moore.M19DGlue

/-!
# Moore 1919, Theorem D: chords and crossings (definitions)
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- `t` is a *chord* of the closed curve `J` with interior `I`, relative to the points `A, B, C, D`:
an arc whose ends are points of `J` other than `A, B, C, D` and whose open arc lies in `I`. -/
def Space.IsChord (σ : Space S) (J I : Set S) (A B C D : S) (t : Set S) : Prop :=
  ∃ a b, a ∈ J \ {A, B, C, D} ∧ b ∈ J \ {A, B, C, D} ∧ @TArc S σ.topology a b t ∧ t \ {a, b} ⊆ I

/-- The set `h` *crosses* the boundary of `I` at `p`: near `p`, `h` lies on two arcs ending at `p`,
the first within `I`, the second without `I` (except for `p`). -/
def Space.Crosses (σ : Space S) (I h : Set S) (p : S) : Prop :=
  ∃ N ∈ @nhds S σ.topology p, ∃ u v : S, ∃ t t' : Set S, @TArc S σ.topology u p t ∧
    @TArc S σ.topology p v t' ∧ t \ {p} ⊆ I ∧ t' \ {p} ⊆ (@closure S σ.topology I)ᶜ ∧
      h ∩ N ⊆ t ∪ t'

section Basic

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S} {Good Good' : Set S → Prop}

theorem Space.cellsOf_subset {U G V : Set S} (hV : V ∈ σ.cellsOf U G) : V ⊆ U := by
  letI := σ.topology
  obtain ⟨z, -, rfl⟩ := hV
  exact (connectedComponentIn_subset _ _).trans diff_subset

theorem Space.Rulable.mono {I sAB sBC sCD sDA : Set S} {A B C D : S}
    (H : σ.Rulable Good I sAB sBC sCD sDA A B C D) (h : ∀ U, U ⊆ I → Good U → Good' U) :
    σ.Rulable Good' I sAB sBC sCD sDA A B C D := by
  obtain ⟨𝒳, 𝒴, R, hG⟩ := H
  exact ⟨𝒳, 𝒴, R, fun U hU => h U (Space.cellsOf_subset hU) (hG U hU)⟩

theorem Space.Quad.rulable_of_good (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3)
    (h4 : σ.Axiom4) (h5 : σ.Axiom5) (h7 : σ.Axiom7) (q : σ.Quad J I A B C D sAB sBC sCD sDA)
    (hI : Good I) : σ.Rulable Good I sAB sBC sCD sDA A B C D := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, hIc, ⟨z, hz⟩, -⟩ := jordan h1 h2 h3 h4 h51 h7 q.interior
  refine ⟨∅, ∅, Space.ArcRuling.empty, ?_⟩
  rintro U ⟨w, hw, rfl⟩
  simp only [sUnion_empty, union_empty, diff_empty] at hw ⊢
  rw [hIc.connectedComponentIn hw]; exact hI

end Basic

end HPC.Moore
