import HPC.Moore.M25Ax

/-!
# Batch 145, item G (corollary): F.A. Theorems for the space of elements

Moore 1925, p. 420: "consequently Theorems 1–15 of that paper all hold true" for the space of
elements. The batch 137–138 theorems that use only Axioms 1, 2, 4, 5 apply to `spaceOfElts r`
through `m25_axioms1245`. Representative instances: F.A. Theorems 3, 6, 13, 14 and 15.

F.A. Theorem 15 (and 16) is proved in batch 137 from Axioms 1, 2, 4 together with metrizability,
which batch 137 obtains from Axioms 3 and 5₁ (`metrizable`). For the space of elements Axiom 3 is not
yet available (batch 147), but the region topology is the quotient topology
(`spaceOfElts_topology`), which is metrizable (`quotient_metrizable_plane`); so batch 137's core
construction (`exists_irreducible`) applies as it stands.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

section hG

variable (hG : MooreDecomp r)
include hG

/-- **F.A. Theorem 15 for the space of elements.** Two distinct elements of a domain of elements
(in Moore's F.A. sense, for Moore's regions) are joined by a simple continuous arc of elements in
the domain. Batch 137's proof, with metrizability supplied by the quotient (not by Axiom 3). -/
theorem m25_fa_theorem15 {M : Set (Quotient r)} (hM : (spaceOfElts r).IsDomain M)
    {A B : Quotient r} (hA : A ∈ M) (hB : B ∈ M) (hAB : A ≠ B) :
    ∃ C ⊆ M, (spaceOfElts r).IsArc A B C := by
  have h1 := m25_axiom1 hG
  have h2 := m25_axiom2 hG
  have h4 := m25_axiom4 hG
  obtain ⟨hMo, hMc⟩ := (isDomain_iff h1).mp hM
  have hmet : @TopologicalSpace.MetrizableSpace (Quotient r) (spaceOfElts r).topology := by
    rw [spaceOfElts_topology hG]; exact quotient_metrizable_plane hG
  letI := (spaceOfElts r).topology
  haveI := hmet
  letI := TopologicalSpace.metrizableSpaceMetric (Quotient r)
  have hsmall : ∀ U : Set (Quotient r), IsOpen U → ∀ x ∈ U, ∀ ε > 0,
      ∃ R ∈ (spaceOfElts r).region, x ∈ R ∧ closure R ⊆ U ∧ R ⊆ ball x ε := by
    intro U hU x hx ε hε
    obtain ⟨R₀, hR₀, hxR₀, hR₀U⟩ := (isOpen_iff_region h1).mp (hU.inter isOpen_ball) x
      ⟨hx, mem_ball_self hε⟩
    obtain ⟨R, hR, hxR, hcl⟩ := exists_region_cl_subset h1 hR₀ hxR₀
    rw [cl_eq_closure h1] at hcl
    exact ⟨R, hR, hxR, hcl.trans (hR₀U.trans inter_subset_left),
      subset_closure.trans (hcl.trans (hR₀U.trans inter_subset_right))⟩
  obtain ⟨C, hCM, hCc, hCp, hAC, hBC, hirr⟩ := exists_irreducible (σ := spaceOfElts r)
    (fun R hR => isOpen_region hR) (fun R hR => (isConn_iff h1).mp (h2 R hR))
    (fun R hR => isCompact_closure_region h1 h4 hR) hsmall hMo hMc hA hB hAB
  refine ⟨C, hCM, (isArc_iff_topological h1 h4).mpr ⟨hAB, hCc, ⟨⟨A, hAC⟩, hCp⟩, hAC, hBC,
    fun H hHC hne hAH hBH hH => hne (hirr H hHC hH.isPreconnected hAH hBH)⟩⟩

/-- **Moore's "consequently Theorems 1–15 of that paper all hold true"** (p. 420), by
representative instances of the batch 137–138 theorems: F.A. Theorem 3 (Axiom 1), Theorem 6
(Axiom 1), Theorem 13 (Axioms 1, 4), Theorem 14 (Axioms 1, 4; with the nonemptiness hypothesis of
batch 137) and Theorem 15 (Axioms 1, 2, 4 and metrizability). -/
theorem m25_FA_1_15 :
    -- Theorem 3
    (∀ (P : Quotient r) (M : Set (Quotient r)), M.Finite → P ∉ M →
      ∃ R ∈ (spaceOfElts r).region, P ∈ R ∧ Disjoint R M) ∧
    -- Theorem 6
    (∀ K ∈ (spaceOfElts r).region, ∀ L ∈ (spaceOfElts r).region, ∀ P ∈ K, P ∈ L →
      ∃ R ∈ (spaceOfElts r).region, P ∈ R ∧ R ⊆ K ∩ L) ∧
    -- Theorem 13
    (∀ M : Set (Quotient r), M.Infinite → (spaceOfElts r).IsBoundedM M →
      ∃ P, (spaceOfElts r).IsLimitPt P M) ∧
    -- Theorem 14
    (∀ M : ℕ → Set (Quotient r), (∀ n, (spaceOfElts r).IsBoundedM (M n)) →
      (∀ n, (spaceOfElts r).cl (M (n + 1)) ⊆ M n) → (∀ n, (M n).Nonempty) →
      (⋂ n, M n).Nonempty ∧ (spaceOfElts r).IsClosedM (⋂ n, M n)) ∧
    -- Theorem 15
    (∀ M : Set (Quotient r), (spaceOfElts r).IsDomain M → ∀ A ∈ M, ∀ B ∈ M, A ≠ B →
      ∃ C ⊆ M, (spaceOfElts r).IsArc A B C) := by
  obtain ⟨h1, -, h4, -, -⟩ := m25_axioms1245 hG
  exact ⟨fun P M hM hPM => fa_theorem3 h1 hM hPM,
    fun K hK L hL P hPK hPL => fa_theorem6 h1 hK hL hPK hPL,
    fun M hi hb => fa_theorem13 h1 h4 hi hb,
    fun M hb hsub hne => fa_theorem14 h1 h4 hb hsub hne,
    fun M hM A hA B hB hAB => m25_fa_theorem15 hG hM hA hB hAB⟩

end hG

end HPC.Moore
