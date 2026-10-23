import HPC.Moore.FA6

/-!
# Moore, F.A. (1916), §7: Jordan structure, Theorems 35, 39, 40 and the footnote of p. 152
(batch 139)

* `jordan`: the facts about a closed curve `J`, its interior `I` and its exterior `E = S − I'` that
  §7 uses throughout: `I`, `E` are connected open sets, `S − J = I + E`, and `J` is the boundary of
  both (Theorem 20).
* **Theorem 35** (`fa_theorem35`), with the printed form refuted (`not_fa_theorem35_printed`).
* **Footnote, p. 152** (`fa_arcs_of_scc_meet`).
* **Theorem 39** (`fa_theorem39`) and **Theorem 40** (`fa_theorem40`), both from `access`: every
  point of `J` is reached from every point of `I` (of `E`) by an arc lying, except for its end, in
  `I` (in `E`). This is batch 138's `accessible` (the lemma behind Theorem 32) applied to an arc of
  `J`; it replaces Moore's construction of the curves `J̄ₙ` in the proof of Theorem 39.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-! ### Jordan structure of a closed curve and its interior -/

section Jordan

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
  (h51 : Space.Axiom5₁ (S := S)) (h7 : σ.Axiom7)
include h1 h2 h3 h4 h51 h7

/-- The structure of a closed curve `J` with interior `I` and exterior `E = S − I'`.
*Axioms used: 1, 2, 3, 4, 5₁, 7.* -/
theorem jordan {J I : Set S} (hI : σ.IsInteriorOf J I) :
    letI := σ.topology
    IsOpen I ∧ IsPreconnected I ∧ I.Nonempty ∧ frontier I = J ∧ IsOpen (closure I)ᶜ ∧
      IsPreconnected (closure I)ᶜ ∧ ((closure I)ᶜ).Nonempty ∧ frontier (closure I)ᶜ = J ∧
      closure I = I ∪ J ∧ Disjoint I J ∧ Disjoint (closure I)ᶜ J ∧ Jᶜ = I ∪ (closure I)ᶜ ∧
      IsCompact J ∧ TSCC J := by
  letI := σ.topology
  obtain ⟨hJ, hIr, hIJ⟩ := hI
  rw [bdry_eq_frontier h1] at hIJ
  have hJt : TSCC J := (isSCC_iff_tscc h1 h3 h4 h51).mp hJ
  have hIo : IsOpen I := isOpen_region hIr
  have hIc : IsPreconnected I := hpc_region h1 h2 I hIr
  have hEc : IsPreconnected (closure I)ᶜ := hext_region h1 h3 I hIr
  have hJcpt : IsCompact J := by
    obtain ⟨A, B, C₁, C₂, hC₁, hC₂, -, rfl⟩ := hJt
    exact hC₁.isCompact.union hC₂.isCompact
  have hJne : J.Nonempty := by
    obtain ⟨A, B, C₁, C₂, hC₁, -, -, rfl⟩ := hJt
    exact ⟨A, Or.inl hC₁.left_mem⟩
  have hcl : closure I = I ∪ J := hIJ ▸ closure_eq_union_frontier hIo
  have hdis : Disjoint I J := hIJ ▸ disjoint_frontier hIo
  have hJE : J ⊆ closure (closure I)ᶜ := hIJ ▸ frontier_subset_closure_ext h1 h7 hIr
  have hEJ : Disjoint (closure I)ᶜ J := by
    rw [disjoint_left]; intro x hx hxJ; exact hx (hcl ▸ Or.inr hxJ)
  have hIne : I.Nonempty := by
    obtain ⟨x, hx⟩ := hJne
    have := hIJ ▸ hx
    exact nonempty_of_mem_frontier this
  have hEne : ((closure I)ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := hJne
    obtain ⟨y, hy⟩ := mem_closure_iff_nhds.mp (hJE hx) univ Filter.univ_mem
    exact ⟨y, hy.2⟩
  have hfrE : frontier (closure I)ᶜ = J := by
    apply subset_antisymm
    · rw [frontier_compl]
      exact (frontier_closure_subset).trans hIJ.subset
    · intro x hx
      refine mem_frontier_of_mem_closure isClosed_closure.isOpen_compl (hJE hx) ?_
      simp only [mem_compl_iff, not_not]
      rw [hcl]; exact Or.inr hx
  refine ⟨hIo, hIc, hIne, hIJ, isClosed_closure.isOpen_compl, hEc, hEne, hfrE, hcl, hdis, hEJ,
    ?_, hJcpt, hJt⟩
  ext x
  simp only [mem_compl_iff, mem_union, hcl, not_or]
  constructor
  · intro hx; by_cases hxI : x ∈ I
    · exact Or.inl hxI
    · exact Or.inr ⟨hxI, hx⟩
  · rintro (hx | ⟨-, hx⟩)
    · exact fun h => disjoint_left.mp hdis hx h
    · exact hx

/-- The component of `S − J` containing a point of `I` (of `E`) is `I` (is `E`). -/
theorem component_eq {J I M : Set S} (hI : σ.IsInteriorOf J I)
    (hM : M = I ∨ M = (@closure S σ.topology I)ᶜ) {P : S} (hP : P ∈ M) :
    @connectedComponentIn S σ.topology Jᶜ P = M := by
  letI := σ.topology
  obtain ⟨hIo, hIc, -, -, hEo, hEc, -, -, -, hdis, hEJ, hcomp, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI
  have hMo : IsOpen M := by rcases hM with rfl | rfl <;> assumption
  have hMc : IsPreconnected M := by rcases hM with rfl | rfl <;> assumption
  have hMJ : M ⊆ Jᶜ := by
    rcases hM with rfl | rfl
    · exact fun x hx hxJ => disjoint_left.mp hdis hx hxJ
    · exact fun x hx hxJ => disjoint_left.mp hEJ hx hxJ
  obtain ⟨M', hM'o, hMM', hcov⟩ : ∃ M', IsOpen M' ∧ Disjoint M M' ∧ Jᶜ ⊆ M ∪ M' := by
    rcases hM with rfl | rfl
    · exact ⟨_, hEo, disjoint_compl_right.mono_left subset_closure, hcomp.subset⟩
    · refine ⟨I, hIo, (disjoint_compl_right.mono_left subset_closure).symm, ?_⟩
      rw [hcomp, union_comm]
  apply subset_antisymm
  · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hMo hM'o hMM'
      ((connectedComponentIn_subset _ _).trans hcov)
      ⟨P, mem_connectedComponentIn (hMJ hP), hP⟩
  · exact hMc.subset_connectedComponentIn hP hMJ

end Jordan

/-! ### Accessibility; Theorems 39 and 40 -/

section Access

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **Accessibility of a closed curve.** If `M` is the interior `I` or the exterior `S − I'` of the
closed curve `J`, every point `O` of `J` is joined to every point `P` of `M` by an arc lying in
`M + O`. This is batch 138's `accessible` applied to an arc of `J` ending at `O`.
*Axioms used: 1–8.* -/
theorem access {J I M : Set S} (hI : σ.IsInteriorOf J I)
    (hM : M = I ∨ M = (@closure S σ.topology I)ᶜ) {O P : S} (hO : O ∈ J) (hP : P ∈ M) :
    ∃ τ, @TArc S σ.topology P O τ ∧ τ ⊆ insert O M := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, -, hfrI, -, -, -, hfrE, hcl, hdis, hEJ, hcomp, -, hJt⟩ :=
    jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨B, hBJ, hBO⟩ : ∃ B ∈ J, B ≠ O := by
    obtain ⟨A, B, C₁, C₂, hC₁, -, -, rfl⟩ := hJt
    by_cases hA : A = O
    · exact ⟨B, Or.inl hC₁.right_mem, fun h => hC₁.ne (hA.trans h.symm)⟩
    · exact ⟨A, Or.inl hC₁.left_mem, hA⟩
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu⟩ :=
    exists_two_arcs_of_isSCC h1 h3 h4 h51 hI.1 hO hBJ hBO.symm
  rw [isArc_iff_tarc h1 h3 h4 h51] at hD₁ hD₂
  obtain ⟨-, f, hf, hfr, hf0, hf1⟩ := hD₁.symm
  have hW : IsOpen D₂ᶜ := hD₂.isClosed.isOpen_compl
  have hfW : ∀ u ∈ Ioo (0 : unitInterval) 1, f u ∈ D₂ᶜ := by
    intro u hu hu2
    have : f u ∈ D₁ ∩ D₂ := ⟨hfr ▸ mem_range_self u, hu2⟩
    rw [hDi] at this
    rcases this with h | h
    · exact hu.2.ne (hf.injective (h.trans hf1.symm))
    · exact hu.1.ne' (hf.injective ((h : f u = B).trans hf0.symm))
  have hWJ : D₂ᶜ \ range f = Jᶜ := by
    rw [hfr, ← hDu]; ext x; simp only [mem_diff, mem_compl_iff, mem_union, not_or]; tauto
  have hPJ : P ∉ J := by
    rcases hM with rfl | rfl
    · exact fun h => disjoint_left.mp hdis hP h
    · exact fun h => disjoint_left.mp hEJ hP h
  have hcM := component_eq h1 h2 h3 h4 h51 h7 hI hM hP
  have hJM : J ⊆ closure M := by
    rcases hM with rfl | rfl
    · rw [hcl]; exact subset_union_right
    · rw [← hfrE]; exact frontier_subset_closure
  obtain ⟨b, hb0, hb1⟩ := exists_between (zero_lt_one' unitInterval)
  obtain ⟨τ, hτ, hτsub⟩ := accessible h1 h2 h3 h4 h5 h6 h7 h8 hf hW (t₀ := 0)
    (zero_lt_one' unitInterval) hfW (x₀ := P) (by rw [hWJ]; exact hPJ)
    ⟨b, ⟨hb0, hb1⟩, by rw [hWJ, hcM]; exact hJM (hDu ▸ Or.inl (hfr ▸ mem_range_self b))⟩
  rw [hWJ, hcM, hf1] at hτsub
  rw [hf1] at hτ
  exact ⟨τ, hτ, hτsub⟩

/-- **Theorem 39.** If `O` is a point on the closed curve `J`, every point not on `J` can be joined
to `O` by an arc having no point except `O` in common with `J`. *Axioms used: 1–8.*
**Proof replaced** (commission check 5): the point lies in the interior or the exterior of `J`
(Axiom 8, `jordan`), and `access` reaches `O` from it. Moore's sequence of curves `Jₙ`, the curves
`J̄ₙ` and the limit arc `P₁O` are not needed; the work they do is done by batch 138's
`accessible`, whose limit arc (`Gen.exists_tarc_of_seq`) plays the part of Moore's
`O + P₁Pₙ₂ + Pₙ₂Pₙ₃ + ⋯`. **Shape change:** the axioms are made explicit. -/
theorem fa_theorem39 {J : Set S} (hJ : σ.IsSCC J) {O P : S} (hO : O ∈ J) (hP : P ∉ J) :
    ∃ K, σ.IsArc P O K ∧ K ∩ J = {O} := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨I, hIr, hIJ⟩ := h8 J hJ
  have hI : σ.IsInteriorOf J I := ⟨hJ, hIr, hIJ⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hdis, hEJ, hcomp, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨M, hM, hPM⟩ : ∃ M, (M = I ∨ M = (closure I)ᶜ) ∧ P ∈ M := by
    have : P ∈ Jᶜ := hP
    rw [hcomp] at this
    rcases this with h | h
    · exact ⟨I, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have hMJ : Disjoint M J := by rcases hM with rfl | rfl <;> assumption
  obtain ⟨τ, hτ, hτsub⟩ := access h1 h2 h3 h4 h5 h6 h7 h8 hI hM hO hPM
  refine ⟨τ, (isArc_iff_tarc h1 h3 h4 h51).mpr hτ, ?_⟩
  apply subset_antisymm
  · rintro x ⟨hxτ, hxJ⟩
    rcases hτsub hxτ with h | h
    · exact h
    · exact absurd hxJ (disjoint_left.mp hMJ h)
  · rintro x rfl; exact ⟨hτ.right_mem, hO⟩

/-- An arc from `A` to `B` (two points of `J`) whose open part lies in `M`, the interior or the
exterior of `J`. -/
theorem exists_arc_through {J I M : Set S} (hI : σ.IsInteriorOf J I)
    (hM : M = I ∨ M = (@closure S σ.topology I)ᶜ) {A B : S} (hA : A ∈ J) (hB : B ∈ J)
    (hAB : A ≠ B) : ∃ X, @TArc S σ.topology A B X ∧ X \ {A, B} ⊆ M := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨-, -, hIne, -, -, -, hEne, -⟩ := jordan h1 h2 h3 h4 h51 h7 hI
  obtain ⟨P, hP⟩ : M.Nonempty := by rcases hM with rfl | rfl <;> assumption
  obtain ⟨τA, hτA, hτAM⟩ := access h1 h2 h3 h4 h5 h6 h7 h8 hI hM hA hP
  obtain ⟨τB, hτB, hτBM⟩ := access h1 h2 h3 h4 h5 h6 h7 h8 hI hM hB hP
  obtain ⟨γ, hγ, hγa⟩ := hτA.symm.join hτB.symm ⟨P, hτA.left_mem, hτB.left_mem⟩ hAB
  refine ⟨γ, hγa, fun x ⟨hx, hxAB⟩ => ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hxAB
  rcases hγ hx with h | h
  · exact (hτAM h).resolve_left hxAB.1
  · exact (hτBM h).resolve_left hxAB.2

/-- **Theorem 40.** If `A`, `B` are two points of a closed curve `J`, they can be joined by arcs
`AXB` and `AYB` with the open arc `AXB` within `J` and the open arc `AYB` without `J`.
*Axioms used: 1–8.* **No proof printed**; supplied: `P` in the interior (exterior) is joined to `A`
and to `B` by `access`, and the union of the two arcs contains an arc from `A` to `B`.
**Shape change:** the axioms are made explicit. -/
theorem fa_theorem40 {J I : Set S} (hJ : σ.IsInteriorOf J I) {A B : S} (hA : A ∈ J) (hB : B ∈ J)
    (hAB : A ≠ B) :
    ∃ X Y : Set S, σ.IsArc A B X ∧ σ.IsArc A B Y ∧ openArc A B X ⊆ I ∧
      openArc A B Y ⊆ σ.ext I := by
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨X, hX, hXI⟩ := exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 hJ (Or.inl rfl) hA hB hAB
  obtain ⟨Y, hY, hYE⟩ := exists_arc_through h1 h2 h3 h4 h5 h6 h7 h8 hJ (Or.inr rfl) hA hB hAB
  refine ⟨X, Y, (isArc_iff_tarc h1 h3 h4 h51).mpr hX, (isArc_iff_tarc h1 h3 h4 h51).mpr hY,
    hXI, ?_⟩
  rw [ext_eq_compl_closure h1]; exact hYE

/-- **Theorem 35.** Every (nonempty) region contains a simple closed curve. *Axioms used: 1–8.*
Proof (replacing Moore's): an arc in `R` (Theorem 16) and, about one of its interior points,
the closed curve `F₁ + P` of batch 138's `th31_pocket` (the construction of Theorem 31), which lies
in `R`. **Shape change:** `R.Nonempty` added (the empty region refutes the printed form,
`not_fa_theorem35_printed`); the axioms are made explicit. -/
theorem fa_theorem35 {R : Set S} (hR : R ∈ σ.region) (hne : R.Nonempty) :
    ∃ J ⊆ R, σ.IsSCC J := by
  letI := σ.topology
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hyx⟩ := exists_ne_of_region h1 h3 h51 hR hx
  obtain ⟨C, hCR, hC⟩ := (fa_theorem16 h1 h2 h3 h4 h51 hR).1 x hx y hy hyx.symm
  rw [isArc_iff_tarc h1 h3 h4 h51] at hC
  obtain ⟨-, f, hf, hfr, -, -⟩ := hC
  obtain ⟨b, hb0, hb1⟩ := exists_between (zero_lt_one' unitInterval)
  obtain ⟨e₁, s₁, e₂, s₂, F₁, P, F₂, Pb, I₁, I₂, R₃, -, -, -, -, -, -, -, hF₁R, -, -, -, -,
    hPR, hI₁, -⟩ := th31_pocket h1 h2 h3 h4 h5 h6 h7 h8 hf hb0 hb1 hR (hCR (hfr ▸ mem_range_self b))
  exact ⟨F₁ ∪ P, union_subset hF₁R hPR, (isSCC_iff_tscc h1 h3 h4 h51).mpr hI₁.1⟩

/-- **Theorem 35 as printed is not a consequence of Axioms 1–8** (unless they have no model): in
the space with `∅` added to the regions (batch 137, `withEmpty`), which satisfies Axioms 1–8, the
region `∅` contains no simple closed curve. -/
theorem not_fa_theorem35_printed :
    σ.withEmpty.Axiom1 ∧ σ.withEmpty.Axiom2 ∧ σ.withEmpty.Axiom3 ∧ σ.withEmpty.Axiom4 ∧
      σ.withEmpty.Axiom5 ∧ σ.withEmpty.Axiom6 ∧ σ.withEmpty.Axiom7 ∧ σ.withEmpty.Axiom8 ∧
      ¬ ∀ R ∈ σ.withEmpty.region, ∃ J ⊆ R, σ.withEmpty.IsSCC J := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -⟩ := not_fa_theorem4_printed h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun h => ?_⟩
  obtain ⟨J, hJ, A, B, C₁, C₂, hC₁, -, -, rfl⟩ := h ∅ (mem_insert _ _)
  exact hJ (Or.inl hC₁.left_mem)

end Access

/-! ### The footnote of p. 152 -/

/-- **Footnote to the proof of Theorem 37** (p. 152): two arcs of a closed curve can have no point
in common unless one of them contains an endpoint of the other one. *Axioms used: 1, 3, 4, 5₁.*
Proof: `A`, `B` split `C` into `K` and a second arc `D` (p. 140, `fa_scc_two_arcs`); if `K'`
contained neither `A` nor `B`, the connected set `K'` would lie in `(K − A − B) + (D − A − B)`,
two separated sets, and meet both (`K` at the common point, `D` at `A'`). -/
theorem fa_arcs_of_scc_meet (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) {C : Set S} (hC : σ.IsSCC C) {A B A' B' : S} {K K' : Set S}
    (hK : σ.IsArc A B K) (hKC : K ⊆ C) (hK' : σ.IsArc A' B' K') (hK'C : K' ⊆ C)
    (hmeet : (K ∩ K').Nonempty) : A ∈ K' ∨ B ∈ K' ∨ A' ∈ K ∨ B' ∈ K := by
  letI := σ.topology
  haveI := t2Space h1
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hAK', hBK', hA'K, -⟩ := hcon
  obtain ⟨C₁, C₂, hC₁, hC₂, hCi, hCu, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hC (hKC hK.left_mem) (hKC hK.right_mem) hK.1
  obtain ⟨D, hD, hKD, hKDu⟩ : ∃ D, σ.IsArc A B D ∧ K ∩ D = {A, B} ∧ K ∪ D = C := by
    rcases huniq K hKC hK with rfl | rfl
    · exact ⟨C₂, hC₂, hCi, hCu⟩
    · exact ⟨C₁, hC₁, by rw [inter_comm, hCi], by rw [union_comm, hCu]⟩
  have hKc : IsClosed K := ((isArc_iff_topological h1 h4).mp hK).2.1.isClosed
  have hDc : IsClosed D := ((isArc_iff_topological h1 h4).mp hD).2.1.isClosed
  have hK'p : IsPreconnected K' := ((isArc_iff_topological h1 h4).mp hK').2.2.1.isPreconnected
  have hcov : K' ⊆ Dᶜ ∪ Kᶜ := by
    intro z hz
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    have : z ∈ K ∩ D := ⟨h.2, h.1⟩
    rw [hKD] at this
    rcases this with rfl | rfl
    · exact hAK' hz
    · exact hBK' hz
  have hdisj : K' ∩ (Dᶜ ∩ Kᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hz hzD hzK
    rcases hKDu ▸ hK'C hz with h | h
    · exact hzK h
    · exact hzD h
  rcases isPreconnected_iff_subset_of_disjoint.mp hK'p _ _ hDc.isOpen_compl hKc.isOpen_compl
      hcov hdisj with h | h
  · rcases hKDu ▸ hK'C hK'.left_mem with h' | h'
    · exact hA'K h'
    · exact h hK'.left_mem h'
  · obtain ⟨z, hzK, hzK'⟩ := hmeet
    exact h hzK' hzK

end HPC.Moore
