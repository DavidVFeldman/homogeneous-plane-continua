import HPC.Moore.Sec4

/-!
# Moore, F.A. (1916): the axioms do not exclude `∅` as a region (batch 137, items B and E)

Theorem 4 ("every region contains infinitely many points") and Theorem 19 ("every region has at
least one boundary point") are printed without the hypothesis that the region is nonempty; Moore's
proofs begin "There exists in `R` at least one point `O`" and "Let `P` denote a point of `R`".

Adding `∅` to the regions of a space (`Space.withEmpty`) changes none of Moore's derived notions
(limit point, boundary, `M'`, connected, Heine–Borel, bounded, arc, simple closed curve), and
preserves each of Axioms 1–8 (Axiom 3 for `R = ∅` says that the whole space is connected, which
follows from Axioms 1, 3, 4, 5: `isConn_univ`). In the enlarged space the printed Theorems 4 and
19 fail at `R = ∅` (`not_fa_theorem4_printed`, `not_fa_theorem19_printed`). So the printed forms
are consequences of Axioms 1–8 only if those axioms have no model.
-/

namespace HPC.Moore

open Set Topology Space

variable {S : Type*}

/-- The space with `∅` added to the regions. -/
def Space.withEmpty (σ : Space S) : Space S := ⟨insert ∅ σ.region⟩

variable {σ : Space S}

namespace Space

theorem mem_withEmpty_region {R : Set S} : R ∈ σ.withEmpty.region ↔ R = ∅ ∨ R ∈ σ.region :=
  mem_insert_iff

theorem isLimitPt_withEmpty {P : S} {M : Set S} :
    σ.withEmpty.IsLimitPt P M ↔ σ.IsLimitPt P M := by
  simp only [IsLimitPt, mem_withEmpty_region]
  constructor
  · exact fun h R hR hP => h R (Or.inr hR) hP
  · rintro h R (rfl | hR) hP
    · exact absurd hP (notMem_empty P)
    · exact h R hR hP

theorem bdry_withEmpty (M : Set S) : σ.withEmpty.bdry M = σ.bdry M := by
  ext X
  simp only [bdry, mem_setOf_eq, mem_withEmpty_region]
  constructor
  · exact fun h R hR hX => h R (Or.inr hR) hX
  · rintro h R (rfl | hR) hX
    · exact absurd hX (notMem_empty X)
    · exact h R hR hX

theorem cl_withEmpty (M : Set S) : σ.withEmpty.cl M = σ.cl M := by
  simp only [cl, bdry_withEmpty]

theorem ext_withEmpty (M : Set S) : σ.withEmpty.ext M = σ.ext M := by
  simp only [ext, cl_withEmpty]

theorem isConn_withEmpty {M : Set S} : σ.withEmpty.IsConn M ↔ σ.IsConn M := by
  simp only [IsConn, isLimitPt_withEmpty]

theorem heineBorel_withEmpty {M : Set S} : σ.withEmpty.HeineBorel M ↔ σ.HeineBorel M := by
  classical
  constructor
  · intro h K ⟨hK, hMK⟩
    exact h K ⟨hK.trans (subset_insert _ _), hMK⟩
  · intro h K ⟨hK, hMK⟩
    obtain ⟨F, hFK, hMF⟩ := h (K \ {∅}) ⟨fun R ⟨hRK, hR⟩ => (mem_withEmpty_region.mp
      (hK hRK)).resolve_left hR, fun x hx => by
        obtain ⟨R, hRK, hxR⟩ := hMK hx
        exact ⟨R, ⟨hRK, fun h => by rw [mem_singleton_iff.mp h] at hxR; exact hxR⟩, hxR⟩⟩
    exact ⟨F, hFK.trans diff_subset, hMF⟩

theorem isBoundedM_withEmpty {M : Set S} : σ.withEmpty.IsBoundedM M ↔ σ.IsBoundedM M := by
  classical
  constructor
  · rintro ⟨F, hF, hMF⟩
    refine ⟨F.erase ∅, fun R hR => ?_, ?_⟩
    · obtain ⟨hR0, hRF⟩ := Finset.mem_erase.mp hR
      exact (mem_withEmpty_region.mp (hF hRF)).resolve_left hR0
    · rw [cl_withEmpty] at hMF
      convert hMF using 2
      ext x
      simp only [Finset.coe_erase, mem_sUnion, mem_diff, Finset.mem_coe, mem_singleton_iff]
      constructor
      · rintro ⟨R, ⟨hRF, -⟩, hxR⟩; exact ⟨R, hRF, hxR⟩
      · rintro ⟨R, hRF, hxR⟩
        exact ⟨R, ⟨hRF, fun h => by rw [h] at hxR; exact hxR⟩, hxR⟩
  · rintro ⟨F, hF, hMF⟩
    exact ⟨F, hF.trans (subset_insert _ _), by rwa [cl_withEmpty]⟩

theorem isClosedM_withEmpty {M : Set S} : σ.withEmpty.IsClosedM M ↔ σ.IsClosedM M := by
  simp only [IsClosedM, isLimitPt_withEmpty]

theorem isArc_withEmpty {A B : S} {C : Set S} : σ.withEmpty.IsArc A B C ↔ σ.IsArc A B C := by
  simp only [IsArc, isBoundedM_withEmpty, isClosedM_withEmpty, isConn_withEmpty]

theorem isSCC_withEmpty {J : Set S} : σ.withEmpty.IsSCC J ↔ σ.IsSCC J := by
  simp only [IsSCC, isArc_withEmpty]

end Space

/-- **The whole space is connected** (Axioms 1, 3, 4, 5). If `S = U ⊔ V` with `U`, `V` closed
and nonempty, a region `R ⊆ U` has connected exterior (Axiom 3) containing `V`, hence `U ⊆ R'`
and `U` is compact (Axiom 4); likewise `V`; so `S` is compact, against Axiom 5. -/
theorem isConn_univ (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5) :
    σ.IsConn univ := by
  rw [isConn_iff h1]
  letI := σ.topology
  have hcpt : ∀ U : Set S, IsClopen U → U.Nonempty → Uᶜ.Nonempty → IsCompact U := by
    intro U hU ⟨P, hP⟩ hUc
    obtain ⟨R, hR, hPR, hRU⟩ := (isOpen_iff_region h1).mp hU.isOpen P hP
    have hclR : closure R ⊆ U := closure_minimal hRU hU.isClosed
    have hext : IsPreconnected (closure R)ᶜ := by
      have := (isConn_iff h1).mp (h3 R hR)
      rwa [Space.ext, cl_eq_closure h1] at this
    have hsub : U ⊆ closure R := by
      by_contra hns
      obtain ⟨x, hxU, hxR⟩ := not_subset.mp hns
      obtain ⟨y, hy⟩ := hUc
      obtain ⟨z, -, hzU, hzUc⟩ := hext U Uᶜ hU.isOpen hU.isClosed.isOpen_compl
        (fun w _ => by by_cases hw : w ∈ U; exacts [Or.inl hw, Or.inr hw]) ⟨x, hxR, hxU⟩
        ⟨y, fun h => hy (hclR h), hy⟩
      exact hzUc hzU
    exact (isCompact_closure_region h1 h4 hR).of_isClosed_subset hU.isClosed hsub
  by_contra hnc
  have : ¬ PreconnectedSpace S := fun h => hnc isPreconnected_univ
  rw [preconnectedSpace_iff_clopen] at this
  push_neg at this
  obtain ⟨U, hU, hU0, hU1⟩ := this
  have hUc : Uᶜ.Nonempty := by
    rw [nonempty_compl]; exact hU1
  have hUn : U.Nonempty := hU0
  have hK : IsCompact (univ : Set S) := by
    rw [← union_compl_self U]
    exact (hcpt U hU hUn hUc).union (hcpt Uᶜ hU.compl hUc (by rwa [compl_compl]))
  obtain ⟨M, hM, hlim⟩ := h5
  obtain ⟨x, -, hx⟩ := hM.exists_accPt_of_subset_isCompact hK (subset_univ M)
  exact hlim x ((isLimitPt_iff h1).mpr hx)

section Preserve

variable (h1 : σ.Axiom1)
include h1

theorem withEmpty_axiom1 : σ.withEmpty.Axiom1 := by
  obtain ⟨K, hK, hK1, hK2⟩ := h1
  refine ⟨K, fun n => Or.inr (hK n), hK1, ?_⟩
  rintro R (rfl | hR) P hP
  · exact absurd hP (notMem_empty P)
  · intro P' hP' hne
    obtain ⟨δ, hδ⟩ := hK2 R hR P hP P' hP' hne
    exact ⟨δ, fun n hn hPn => by rw [cl_withEmpty]; exact hδ n hn hPn⟩

omit h1 in
theorem withEmpty_axiom2 (h2 : σ.Axiom2) : σ.withEmpty.Axiom2 := by
  rintro R (rfl | hR)
  · intro A B hAB _ hA _
    obtain ⟨x, hx⟩ := hA
    have : x ∈ A ∪ B := Or.inl hx
    rw [hAB] at this; exact absurd this (notMem_empty x)
  · exact isConn_withEmpty.mpr (h2 R hR)

theorem withEmpty_axiom3 (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5) :
    σ.withEmpty.Axiom3 := by
  rintro R (rfl | hR)
  · rw [ext_withEmpty, isConn_withEmpty]
    have hcl : σ.cl (∅ : Set S) = ∅ := by
      rw [cl_eq_closure h1]; exact @closure_empty S σ.topology
    rw [Space.ext, hcl, compl_empty]
    exact isConn_univ h1 h3 h4 h5
  · rw [ext_withEmpty, isConn_withEmpty]; exact h3 R hR

theorem withEmpty_axiom4 (h4 : σ.Axiom4) : σ.withEmpty.Axiom4 := by
  rintro R (rfl | hR)
  · rw [heineBorel_withEmpty, cl_withEmpty]
    intro K _
    refine ⟨∅, by simp, ?_⟩
    rw [cl_eq_closure h1, @closure_empty S σ.topology]
    exact empty_subset _
  · rw [heineBorel_withEmpty, cl_withEmpty]; exact h4 R hR

omit h1 in
theorem withEmpty_axiom5 (h5 : σ.Axiom5) : σ.withEmpty.Axiom5 := by
  obtain ⟨M, hM, hlim⟩ := h5
  exact ⟨M, hM, fun P h => hlim P (isLimitPt_withEmpty.mp h)⟩

omit h1 in
theorem withEmpty_axiom6 (h6 : σ.Axiom6) : σ.withEmpty.Axiom6 := by
  rintro R hR R' hR' P hP hPb
  rcases hR' with rfl | hR'
  · exact absurd hP (notMem_empty P)
  rcases hR with rfl | hR
  · rw [bdry_withEmpty] at hPb
    obtain ⟨x, -, hx⟩ := (hPb R' hR' hP).1
    exact absurd hx (notMem_empty _)
  · rw [bdry_withEmpty] at hPb
    obtain ⟨K, hK, K', hK', h1', h2', h3', h4', h5'⟩ := h6 R hR R' hR' P hP hPb
    exact ⟨K, Or.inr hK, K', Or.inr hK', h1', h2', h3', h4', by
      rw [bdry_withEmpty, bdry_withEmpty]; exact h5'⟩

omit h1 in
theorem withEmpty_axiom7 (h7 : σ.Axiom7) : σ.withEmpty.Axiom7 := by
  rintro R hR R' hR' P hP hPb
  rcases hR' with rfl | hR'
  · exact absurd hP (notMem_empty P)
  rcases hR with rfl | hR
  · rw [bdry_withEmpty] at hPb
    obtain ⟨x, -, hx⟩ := (hPb R' hR' hP).1
    exact absurd hx (notMem_empty _)
  · rw [bdry_withEmpty] at hPb
    obtain ⟨L, hL, L', hL', h1', h2', h3', h4', h5'⟩ := h7 R hR R' hR' P hP hPb
    exact ⟨L, Or.inr hL, L', Or.inr hL', h1', h2', h3', by rwa [ext_withEmpty], by
      rw [bdry_withEmpty, bdry_withEmpty]; exact h5'⟩

omit h1 in
theorem withEmpty_axiom8 (h8 : σ.Axiom8) : σ.withEmpty.Axiom8 := by
  intro J hJ
  obtain ⟨R, hR, hRJ⟩ := h8 J (isSCC_withEmpty.mp hJ)
  exact ⟨R, Or.inr hR, by rw [bdry_withEmpty]; exact hRJ⟩

/-- **Theorem 4 as printed is not a consequence of Axioms 1–8** (unless they have no model): from
any space satisfying Axioms 1–8, adding `∅` to the regions gives a space satisfying Axioms 1–8 in
which the region `∅` is finite. -/
theorem not_fa_theorem4_printed (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) :
    σ.withEmpty.Axiom1 ∧ σ.withEmpty.Axiom2 ∧ σ.withEmpty.Axiom3 ∧ σ.withEmpty.Axiom4 ∧
      σ.withEmpty.Axiom5 ∧ σ.withEmpty.Axiom6 ∧ σ.withEmpty.Axiom7 ∧ σ.withEmpty.Axiom8 ∧
      ¬ ∀ R ∈ σ.withEmpty.region, R.Infinite :=
  ⟨withEmpty_axiom1 h1, withEmpty_axiom2 h2, withEmpty_axiom3 h1 h3 h4 h5,
    withEmpty_axiom4 h1 h4, withEmpty_axiom5 h5, withEmpty_axiom6 h6,
    withEmpty_axiom7 h7, withEmpty_axiom8 h8,
    fun h => (h ∅ (mem_insert _ _)) finite_empty⟩

/-- **Theorem 19 as printed is not a consequence of Axioms 1–8** (unless they have no model): in
the same space the region `∅` has no boundary point. -/
theorem not_fa_theorem19_printed (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) :
    σ.withEmpty.Axiom1 ∧ σ.withEmpty.Axiom2 ∧ σ.withEmpty.Axiom3 ∧ σ.withEmpty.Axiom4 ∧
      σ.withEmpty.Axiom5 ∧ σ.withEmpty.Axiom6 ∧ σ.withEmpty.Axiom7 ∧ σ.withEmpty.Axiom8 ∧
      ¬ ∀ R ∈ σ.withEmpty.region, (σ.withEmpty.bdry R).Nonempty := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -⟩ := not_fa_theorem4_printed h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun h => ?_⟩
  obtain ⟨X, hX⟩ := h ∅ (mem_insert _ _)
  rw [bdry_withEmpty] at hX
  obtain ⟨R, hR, hXR⟩ := Space.exists_region_mem h1 X
  obtain ⟨x, -, hx⟩ := (hX R hR hXR).1
  exact hx

end Preserve

end HPC.Moore
