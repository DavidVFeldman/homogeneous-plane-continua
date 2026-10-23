import HPC.Moore.M43Pocket

/-!
# Theorem 43: the component of an intersection adjacent to a point (batch 140, item B)

`dual_component`: if `O` is a point of the closed curve `J` (interior `I`) within the closed curve
`J'` (interior `I'`), `U` is `I` or the exterior of `J` (in the second case `I ⊄ I'`), and `J ∩ J'`
has two points, then the component `W` of `U ∩ I'` adjacent to `O` is the interior of a closed curve
on `J + J'` through `O`. This is the statement dual to Theorem 41 for intersections, which the
proof of Theorem 43 needs (`OPEN.md`, batch 139). The proof is that of Theorem 41, Case II, with
`W` for the unbounded component: the chords of `J'` lying in `U` and in `W'` replace arcs of `J`
(`half_replace_gen`, with `pocket_int` / `pocket_ext`), and `W` is the interior of the resulting
curve because it lies within `J'`.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

section Dual

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **A piece adjacent to `O`** (Theorem 28): a connected open set within `J'`, on the side `U` of
`J`, having `O` as a limit point. *Axioms used: 1–8.* -/
theorem adjacent_piece {J I J' I' U : Set S} (hI : σ.IsInteriorOf J I)
    (hI' : σ.IsInteriorOf J' I')
    (hU : U = I ∨ (U = (@closure S σ.topology I)ᶜ ∧ ¬ I ⊆ I')) {O : S} (hO : O ∈ J)
    (hOI' : O ∈ I') :
    ∃ P, @IsOpen S σ.topology P ∧ @IsPreconnected S σ.topology P ∧ P ⊆ U ∩ I' ∧
      O ∈ @closure S σ.topology P := by
  letI := σ.topology
  haveI := t2Space h1
  haveI := locallyConnectedSpace h1 h2
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨hIo, hIc, -, hfr, -, -, -, -, hcl, hdisIJ, hdisEJ, hcompl, -, -⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨hI'o, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI'
  obtain ⟨R', hR', hOR', hR'I'⟩ :=
    (isTopologicalBasis_region h1).exists_subset_of_mem_open hOI' hI'o
  have hM : U = I ∨ U = σ.ext I := by
    rcases hU with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (by rw [ext_eq_compl_closure h1]; exact h)
  obtain ⟨A, B, X, C₁, C₂, hX, hXU, hC₁, hC₂, hC12, hCJ, hOC₁, hC₁R'⟩ :=
    fa_theorem28 h1 h2 h3 h4 h51 h6 h7 hI hO hR' hOR' hM
  rw [isArc_iff_tarc h1 h3 h4 h51] at hX hC₁ hC₂
  have hUJ : Disjoint U J := by
    rcases hU with h | ⟨h, -⟩
    · rw [h]; exact hdisIJ
    · rw [h]; exact hdisEJ
  have hXJ : ∀ x ∈ X \ {A, B}, x ∉ J := fun x hx hxJ => disjoint_left.mp hUJ (hXU hx).1 hxJ
  have hC₁J : C₁ ⊆ J := hCJ ▸ subset_union_left
  obtain ⟨C', P₁, P₂, hC', hC₁C', hC₁C'u, hP₁, hP₂⟩ :=
    chord_pockets h1 h3 h4 h5 h8 hI hX hXJ hC₁ hC₁J
  have hP₁o : IsOpen P₁ := hopen_region P₁ hP₁.2.1
  have hP₂o : IsOpen P₂ := hopen_region P₂ hP₂.2.1
  have hXR' : X ⊆ R' := fun x hx => by
    by_cases hxAB : x ∈ ({A, B} : Set S)
    · rcases hxAB with h | h
      · rw [h]; exact hC₁R' hC₁.left_mem
      · rw [mem_singleton_iff.mp h]; exact hC₁R' hC₁.right_mem
    · exact (hXU ⟨hx, hxAB⟩).2
  have hP₁R' : P₁ ⊆ R' := th21Prop h1 h3 h4 h5 h7 R' hR' P₁ hP₁.2.1
    (by rw [hP₁.2.2]; exact (union_subset hXR' hC₁R').trans subset_closure)
  have hOP₁ : O ∈ closure P₁ := frontier_subset_closure (hP₁.2.2 ▸ Or.inr hOC₁.1)
  have hR : TInt σ.region J I := (isInteriorOf_iff h1 h3 h4 h51).mp hI
  have hP₁U : P₁ ⊆ U := by
    rcases hU with hU | ⟨hU, hnot⟩
    · rw [hU]
      exact th24_sub (th21Prop h1 h3 h4 h5 h7) hR (hC₁J hC₁.left_mem) (hC₁J hC₁.right_mem) hC₁J
        (fun x hx => hU ▸ (hXU hx).1) hP₁
    · rw [hU]
      have hXE : X \ {A, B} ⊆ (closure I)ᶜ := fun x hx => hU ▸ (hXU hx).1
      obtain ⟨d₀, hd₀⟩ := hC'.nonempty_diff
      rcases th27_dich hopen_region (hpc_region h1 h2) (th21Prop h1 h3 h4 h5 h7)
          (arcConn h1 h3 h4 h51 h2) (ax8Prop h1 h3 h4 h51 h8) (hext_region h1 h3)
          (fun R hR => isCompact_closure_region h1 h4 hR) (not_isCompact_univ h1 h5) hR hC₁ hC'
          hC₁C' hC₁C'u hOC₁ hd₀ hX hXE hP₁ hP₂ with h | h
      · have hP₁P₂ : P₁ ⊆ P₂ := fun x hx => by rw [h]; exact Or.inr hx
        have hP₁J : P₁ ⊆ Jᶜ := by
          intro x hx hxJ
          rw [← hC₁C'u] at hxJ
          rcases hxJ with h' | h'
          · exact notMem_of_mem_frontier hP₁o (hP₁.2.2 ▸ Or.inr h') hx
          · exact notMem_of_mem_frontier hP₂o (hP₂.2.2 ▸ Or.inr h') (hP₁P₂ hx)
        rw [hcompl] at hP₁J
        rcases (hpc_region h1 h2 P₁ hP₁.2.1).subset_or_subset hIo isClosed_closure.isOpen_compl
          (disjoint_compl_right.mono_left subset_closure) hP₁J with h' | h'
        · exfalso
          obtain ⟨x₀, hx₀⟩ := hX.nonempty_diff
          have : x₀ ∈ closure I :=
            closure_mono h' (frontier_subset_closure (hP₁.2.2 ▸ Or.inl hx₀.1))
          exact hXE hx₀ this
        · exact h'
      · exfalso
        apply hnot
        intro x hx
        have : x ∈ P₁ := by rw [h]; exact Or.inl (Or.inr hx)
        exact hR'I' (hP₁R' this)
  exact ⟨P₁, hP₁o, hpc_region h1 h2 P₁ hP₁.2.1, fun x hx => ⟨hP₁U hx, hR'I' (hP₁R' hx)⟩, hOP₁⟩

end Dual

end HPC.Moore
