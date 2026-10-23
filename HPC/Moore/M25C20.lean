import HPC.Moore.M25C19

/-!
# Batch 147, item E and part of F: Theorem 20, the topology, and Axioms 1–5, 8, 6′, 7′

* **Theorem 20**: Moore's proof (Theorems 4 and 19; restricted regions are regions in the original
  sense, `mooreRegion_of_restricted`, and open). It says that the restricted regions form a basis of
  the quotient topology (`isTopologicalBasis_restricted`), so the region topology of
  `spaceRestricted r` is the quotient topology (`spaceRestricted_topology`).
* **Axioms 1, 2, 4, 5** (\"With the help of Theorems 19 and 20 it is easy to see that these axioms
  continue to hold\"): Axiom 1 as for Moore's regions (`m25_axiom1`), with restricted regions in small
  balls (Theorem 19); Axioms 2 and 4 from Theorem 11 (connected, closures compact) through the
  bridge; Axiom 5 from `m25_axiom5`, since by Theorems 4 and 20 the limit elements are the same for
  both systems of regions.
* **Axiom 3** (\"can easily be seen with the help of Theorem 11\"): `S − R'` is the exterior.
* **Axiom 8**: Theorem 11, with `σ.IsSCC J ↔ IsSCCElt J` (`isSCC_iff_tscc` and
  `isSCCElt_iff_tscc`).
* **Axioms 6′ and 7′** (\"a consequence of Theorems 11 and 13\"): 6′ is Theorem 13 for an arc with one
  end on the boundary; 7′ holds since `J` is also the boundary of the exterior (Theorem 11).
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane Gen TopologicalSpace

variable {r : Setoid Pt}

section M25C20

variable (hG : MooreDecomp r)
include hG

/-- Restricted regions about `p` inside any neighbourhood of `p` (Theorem 19). -/
theorem exists_restricted_subset {p : Quotient r} {V : Set (Quotient r)} (hV : V ∈ 𝓝 p) :
    ∃ R, restrictedRegion R ∧ p ∈ R ∧ R ⊆ V := by
  obtain ⟨R, hR, hpR, hRV⟩ := exists_region_subset hG hV
  obtain ⟨J, hJ, -, hpJ, hJR⟩ := m25_theorem19 hG hR hpR
  exact ⟨sccInterior J, ⟨J, hJ, rfl⟩, hpJ, hJR.trans hRV⟩

/-- **The restricted regions form a basis of the quotient topology.** -/
theorem isTopologicalBasis_restricted : IsTopologicalBasis (restrictedRegions r) :=
  isTopologicalBasis_of_isOpen_of_nhds (fun R hR => isOpen_restricted hG R hR)
    fun _ _ hpV hV => exists_restricted_subset hG (hV.mem_nhds hpV)

/-- **Theorem 20** (p. 424). `p` is a limit element of `H` iff every region in the restricted sense
containing `p` contains an element of `H` other than `p`. -/
theorem m25_theorem20 {p : Quotient r} {H : Set (Quotient r)} :
    IsLimitElt p H ↔ (spaceRestricted r).IsLimitPt p H := by
  rw [isLimitElt_iff hG, accPt_iff_nhds]
  constructor
  · intro h R hR hpR
    obtain ⟨y, ⟨hyR, hyK⟩, hyp⟩ := h R ((isOpen_restricted hG R hR).mem_nhds hpR)
    exact ⟨y, hyK, hyR, hyp⟩
  · intro h V hV
    obtain ⟨R, hR, hpR, hRV⟩ := exists_restricted_subset hG hV
    obtain ⟨y, hyK, hyR, hyp⟩ := h R hR hpR
    exact ⟨y, ⟨hRV hyR, hyK⟩, hyp⟩

/-- The topology of the restricted regions is the quotient topology. -/
theorem spaceRestricted_topology :
    (spaceRestricted r).topology = (inferInstance : TopologicalSpace (Quotient r)) :=
  (isTopologicalBasis_restricted hG).eq_generateFrom.symm

/-- Moore's `M'` for the restricted regions is the quotient closure. -/
theorem cl_eq_closure_restricted (M : Set (Quotient r)) :
    (spaceRestricted r).cl M = closure M := by
  ext X
  rw [(isTopologicalBasis_restricted hG).mem_closure_iff]
  constructor
  · rintro (hX | hX) R hR hXR
    · exact ⟨X, hXR, hX⟩
    · exact (hX R hR hXR).1
  · intro h
    by_cases hXM : X ∈ M
    · exact Or.inl hXM
    · exact Or.inr fun R hR hXR => ⟨h R hR hXR, ⟨X, hXR, hXM⟩⟩

/-- **Axiom 1** for the restricted regions (as `m25_axiom1`, with Theorem 19). -/
theorem m25r_axiom1 : (spaceRestricted r).Axiom1 := by
  haveI := quotient_metrizable_plane hG
  letI := TopologicalSpace.metrizableSpaceMetric (Quotient r)
  have hreg : ∀ (k : ℕ) (q : Quotient r), ∃ R, restrictedRegion R ∧ q ∈ R ∧
      R ⊆ ball q (1 / ((k : ℝ) + 1)) := fun k q =>
    exists_restricted_subset hG (ball_mem_nhds q (by positivity))
  choose Rg hRg hqR hRball using hreg
  have hcov : ∀ k : ℕ, ∃ t : Finset (Quotient r),
      Quotient.mk r '' closedBall (0 : Pt) k ⊆ ⋃ q ∈ t, Rg k q := fun k =>
    (isCompact_closedBall (0 : Pt) k).image continuous_mk |>.elim_finite_subcover
      (fun q => Rg k q) (fun q => isOpen_restricted hG _ (hRg k q))
      (fun x _ => mem_iUnion.2 ⟨x, hqR k x⟩)
  choose t ht using hcov
  set q0 : Quotient r := Quotient.mk r 0
  set l : ℕ → List (Quotient r) := fun k => q0 :: (t k).toList with hl
  have hlen : ∀ k, 1 ≤ (l k).length := fun k => by simp [hl]
  set lev := levelOf hlen with hlev
  set K : ℕ → Set (Quotient r) := fun n =>
    Rg (lev n) ((l (lev n)).getD (n - blockStart (fun k => (l k).length) (lev n)) q0) with hK
  refine ⟨K, fun n => hRg _ _, ?_, ?_⟩
  · intro m P
    obtain ⟨X, rfl⟩ := Quotient.mk_surjective P
    obtain ⟨k, hk⟩ := exists_nat_gt (max (m : ℝ) ‖X‖)
    have hXk : X ∈ closedBall (0 : Pt) k := by
      rw [mem_closedBall, dist_zero_right]; exact (le_max_right _ _).trans hk.le
    obtain ⟨q, hq, hPq⟩ := mem_iUnion₂.1 (ht k (mem_image_of_mem _ hXk))
    have hql : q ∈ l k := by simp [hl, hq]
    obtain ⟨i, hi, hqi⟩ := List.getElem_of_mem hql
    set n := blockStart (fun k => (l k).length) k + i
    have hb1 : blockStart (fun k => (l k).length) k ≤ n := Nat.le_add_right _ _
    have hb2 : n < blockStart (fun k => (l k).length) (k + 1) := by
      simp only [n, blockStart, Finset.sum_range_succ]; omega
    have hlevn : lev n = k := levelOf_eq hlen hb1 hb2
    have hmk : m < k := by exact_mod_cast (le_max_left _ _).trans_lt hk
    refine ⟨n, ?_, ?_⟩
    · exact lt_of_lt_of_le hmk ((le_blockStart hlen k).trans hb1)
    · simp only [hK, hlevn]
      rw [show n - blockStart (fun k => (l k).length) k = i by omega, List.getD_eq_getElem _ _ hi,
        hqi]
      exact hPq
  · intro R hR P hPR P' hP'R hPP'
    obtain ⟨ε, hε, hεR⟩ := Metric.isOpen_iff.1 (isOpen_restricted hG R hR) P hPR
    have hd : 0 < dist P P' := dist_pos.2 hPP'
    set ε' := min ε (dist P P')
    have hε' : 0 < ε' := lt_min hε hd
    obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt (half_pos hε')
    refine ⟨blockStart (fun k => (l k).length) k0, fun n hn hPn => ?_⟩
    have hlevn : k0 ≤ lev n := le_levelOf hlen hn.le
    rw [cl_eq_closure_restricted hG]
    set q := (l (lev n)).getD (n - blockStart (fun k => (l k).length) (lev n)) q0
    have hsub : closure (K n) ⊆ closedBall q (1 / ((lev n : ℝ) + 1)) :=
      (closure_mono (hRball _ _)).trans closure_ball_subset_closedBall
    have hsmall : 1 / ((lev n : ℝ) + 1) ≤ 1 / ((k0 : ℝ) + 1) := by
      gcongr
    have hPq : dist P q < 1 / ((lev n : ℝ) + 1) := mem_ball.1 (hRball _ _ hPn)
    intro z hz
    have hzq : dist z q ≤ 1 / ((lev n : ℝ) + 1) := mem_closedBall.1 (hsub hz)
    have hzP : dist z P < ε' := by
      have := dist_triangle_right z P q
      linarith
    refine ⟨hεR (mem_ball.2 (hzP.trans_le (min_le_left _ _))), fun hzP' => ?_⟩
    rw [mem_singleton_iff] at hzP'
    subst hzP'
    rw [dist_comm] at hzP
    exact absurd (hzP.trans_le (min_le_right _ _)) (lt_irrefl _)

/-- **Axiom 2** for the restricted regions. -/
theorem m25r_axiom2 : (spaceRestricted r).Axiom2 := by
  intro R hR
  rw [isConn_iff (m25r_axiom1 hG), spaceRestricted_topology hG]
  exact isPreconnected_restricted hG R hR

/-- **Axiom 3** for the restricted regions (Theorem 11: `S − R'` is the exterior). -/
theorem m25r_axiom3 : (spaceRestricted r).Axiom3 := by
  intro R hR
  rw [isConn_iff (m25r_axiom1 hG), Space.ext, cl_eq_closure_restricted hG,
    spaceRestricted_topology hG]
  exact ext_restricted hG R hR

/-- **Axiom 4** for the restricted regions. -/
theorem m25r_axiom4 : (spaceRestricted r).Axiom4 := by
  intro R hR
  rw [heineBorel_iff, spaceRestricted_topology hG, cl_eq_closure_restricted hG]
  exact isCompact_closure_restricted hG R hR

/-- Limit points for the two systems of regions coincide (Theorems 4 and 20). -/
theorem isLimitPt_restricted_iff {p : Quotient r} {H : Set (Quotient r)} :
    (spaceRestricted r).IsLimitPt p H ↔ (spaceOfElts r).IsLimitPt p H := by
  rw [← m25_theorem20 hG, m25_theorem4 hG]

/-- **Axiom 5** for the restricted regions. -/
theorem m25r_axiom5 : (spaceRestricted r).Axiom5 := by
  obtain ⟨M, hM, hlim⟩ := m25_axiom5 hG
  exact ⟨M, hM, fun P hP => hlim P ((isLimitPt_restricted_iff hG).1 hP)⟩

/-- Moore's boundary for the restricted regions is the frontier. -/
theorem bdry_restricted (M : Set (Quotient r)) : (spaceRestricted r).bdry M = frontier M := by
  rw [bdry_eq_frontier (m25r_axiom1 hG), spaceRestricted_topology hG]

/-- Moore's arcs for the restricted regions are the arcs of elements. -/
theorem isArc_restricted_iff {A B : Quotient r} {C : Set (Quotient r)} :
    (spaceRestricted r).IsArc A B C ↔ IsArcElt A B C := by
  rw [isArc_iff_tarc (m25r_axiom1 hG) (m25r_axiom3 hG) (m25r_axiom4 hG)
    (axiom5₁_of_axiom5 (m25r_axiom5 hG)), spaceRestricted_topology hG, isArcElt_iff_tarc hG]

/-- Moore's simple closed curves for the restricted regions are the simple closed curves of
elements. -/
theorem isSCC_restricted_iff {J : Set (Quotient r)} :
    (spaceRestricted r).IsSCC J ↔ IsSCCElt J := by
  rw [isSCC_iff_tscc (m25r_axiom1 hG) (m25r_axiom3 hG) (m25r_axiom4 hG)
    (axiom5₁_of_axiom5 (m25r_axiom5 hG)), spaceRestricted_topology hG, isSCCElt_iff_tscc hG]

/-- **Axiom 8** for the restricted regions (Theorem 11). -/
theorem m25r_axiom8 : (spaceRestricted r).Axiom8 := by
  intro J hJ
  rw [isSCC_restricted_iff hG] at hJ
  refine ⟨sccInterior J, ⟨J, hJ, rfl⟩, ?_⟩
  rw [bdry_restricted hG]
  exact (sccInterior_spec hG hJ).2.2.2.1

/-- Axioms 6′ and 7′ for the restricted regions (\"a consequence of Theorems 11 and 13\", p. 425). -/
theorem m25_axioms6'7' : (spaceRestricted r).Axiom6' ∧ (spaceRestricted r).Axiom7' := by
  have h1 := m25r_axiom1 hG
  constructor
  · intro R hR A B C hC hCR
    rw [isArc_restricted_iff hG] at hC
    have hAC : A ∈ C := hC.2.2.2.2.1
    have heq : (R ∪ {A}) \ C = R \ C := by
      ext x
      simp only [mem_diff, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨hx | rfl, hxC⟩
        · exact ⟨hx, hxC⟩
        · exact absurd hAC hxC
      · rintro ⟨hx, hxC⟩; exact ⟨Or.inl hx, hxC⟩
    rw [heq, isConn_iff h1, spaceRestricted_topology hG]
    exact (m25_theorem13 hG (mooreRegion_of_restricted hG hR)
      (Or.inr ⟨A, B, hC, Or.inl hCR⟩)).2.isPreconnected
  · rintro R ⟨J, hJ, rfl⟩ P hP
    rw [bdry_restricted hG, (sccInterior_spec hG hJ).2.2.2.1] at hP
    rw [isLimitPt_iff h1, Space.ext, cl_eq_closure_restricted hG, spaceRestricted_topology hG,
      compl_closure_sccInterior hG hJ, accPt_iff_nhds]
    intro U hU
    have hPE : P ∈ frontier (sccExterior J) := by rw [(sccInterior_spec hG hJ).2.2.2.2.2.2.2.1]; exact hP
    obtain ⟨y, hyU, hyE⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hPE) U hU
    exact ⟨y, ⟨hyU, hyE⟩, fun h => hyE.1 (h ▸ hP)⟩

end M25C20

end HPC.Moore
