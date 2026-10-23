import HPC.Moore.M25Quot

/-!
# Batch 145, items E and F: Moore 1925 §I, Theorems 3 and 4

* `m25_theorem3` (with `exists_region_in_tube`): Moore's construction — a polygon `J` enclosing
  `p̄` inside the tube, `H` the elements meeting `J`, `R` the component of `Hᶜ` containing `p`;
  `R̄` is the component of `H̄ᶜ` containing `p̄` (`ptsOf_connectedComponentIn`), so it lies inside
  `J`, and `∂R` is connected by Brouwer (`quot_brouwer`).
* `m25_theorem4`, `isTopologicalBasis_mooreRegion`, `spaceOfElts_topology`, `cl_eq_closure_quot`.
* `m25_boundary_iff`: Moore's boundary (p. 417), with "limit element of `G`" in the second
  clause, is the quotient frontier.
* `m25_unbounded_unique`.

Theorem 2 is in `M25Thm2.lean`; the claim of p. 420 in `M25Ax.lean` and `M25FA.lean`.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

/-- A preconnected set that meets an open set `E` and misses its frontier lies in `E`. -/
theorem subset_of_preconnected_of_disjoint_frontier {X : Type*} [TopologicalSpace X]
    {C E : Set X} (hC : IsPreconnected C) (hE : IsOpen E) (hCE : (C ∩ E).Nonempty)
    (hCf : Disjoint C (frontier E)) : C ⊆ E := by
  have hsub : C ⊆ E ∪ (closure E)ᶜ := by
    intro z hz
    by_cases hzE : z ∈ E
    · exact Or.inl hzE
    · refine Or.inr fun hzc => disjoint_left.1 hCf hz ⟨hzc, ?_⟩
      rw [hE.interior_eq]; exact hzE
  rcases isPreconnected_iff_subset_of_disjoint.1 hC _ _ hE isClosed_closure.isOpen_compl hsub
    (by
      refine eq_empty_of_forall_notMem fun z ⟨_, hzE, hzc⟩ => hzc (subset_closure hzE)) with h | h
  · exact h
  · obtain ⟨z, hzC, hzE⟩ := hCE
    exact absurd (subset_closure hzE) (h hzC)

section hG

variable (hG : MooreDecomp r)
include hG

/-! ### Theorem 3 -/

/-- **Theorem 3, tube form.** Every element `p` lies in a Moore region contained in the tube of
the `e`-thickening of `p̄`. -/
theorem exists_region_in_tube (p : Quotient r) {e : ℝ} (he : 0 < e) :
    ∃ R, mooreRegion R ∧ p ∈ R ∧ R ⊆ tube r (thickening e (ptsOf r {p})) := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective p
  rw [ptsOf_singleton]
  set P := elt r x with hPdef
  set T := tube r (thickening e P) with hTdef
  have hTo : IsOpen T := isOpen_tube hG isOpen_thickening
  have hPT : P ⊆ ptsOf r T := by
    intro z hz
    show ptsOf r {Quotient.mk r z} ⊆ thickening e P
    rw [ptsOf_singleton, show elt r z = P by
      rw [← ptsOf_singleton, Quotient.sound hz, ptsOf_singleton]]
    exact self_subset_thickening he _
  obtain ⟨J, hJ, hJP, hPJ, hJT⟩ := planeFacts_holds.enclose P ⟨hG.compact x, hG.connected x⟩
    (hG.nonsep x) (ptsOf r T) (isOpen_iff_ptsOf.1 hTo) hPT
  set H := Quotient.mk r '' J with hHdef
  have hJc : IsCompact J := planeFacts_holds.isCompact_poly hJ
  have hHc : IsClosed H := isClosedMap_mk_plane hG J hJc.isClosed
  have hHconn : IsConnected H := hJ.isConnected.image _ continuous_mk.continuousOn
  have hpH : Quotient.mk r x ∉ H := by
    rintro ⟨z, hzJ, hz⟩
    exact disjoint_left.1 hJP hzJ (Quotient.exact hz)
  set R := connectedComponentIn Hᶜ (Quotient.mk r x) with hRdef
  have hRpts : ptsOf r R = connectedComponentIn (ptsOf r H)ᶜ x :=
    ptsOf_connectedComponentIn hG x
  have hJH : J ⊆ ptsOf r H := fun z hz => ⟨z, hz, rfl⟩
  have hxJ : x ∈ polyInterior J := hPJ (mem_elt_self x)
  have hRJ' : ptsOf r R ⊆ connectedComponentIn Jᶜ x := by
    rw [hRpts]; exact connectedComponentIn_mono _ (compl_subset_compl.2 hJH)
  have hRJ : ptsOf r R ⊆ polyInterior J := by
    intro w hw
    have hw' := hRJ' hw
    refine ⟨connectedComponentIn_subset _ _ hw', ?_⟩
    rw [← connectedComponentIn_eq hw']; exact hxJ.2
  refine ⟨R, ⟨isOpen_connectedComponentIn_quot hG hHc.isOpen_compl _,
    isConnected_connectedComponentIn_iff.2 hpH, hxJ.2.subset hRJ',
    quot_brouwer hG hHc hHconn hpH⟩, mem_connectedComponentIn hpH, fun q hq => ?_⟩
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective q
  exact hJT (hRJ hq)

/-- **Theorem 3** (p. 419). For each element `p` and `e > 0` there is a region every element of
which is at upper distance `< e` from `p`. *The printed statement does not say that the region
contains `p`; the proof gives it and Theorem 4 needs it, so `p ∈ R` is added (skeleton).* -/
theorem m25_theorem3 (p : Quotient r) {e : ℝ} (he : 0 < e) :
    ∃ R, mooreRegion R ∧ p ∈ R ∧ ∀ k ∈ R, ∀ y, Quotient.mk r y = k → ∀ z ∈ elt r y,
      ∀ x, Quotient.mk r x = p → infDist z (elt r x) < e := by
  obtain ⟨R, hR, hpR, hRT⟩ := exists_region_in_tube hG p he
  exact ⟨R, hR, hpR, fun k hk => upper_iff_mem_tube.2 (hRT hk)⟩

/-- Moore regions about `p` inside any neighbourhood of `p`. -/
theorem exists_region_subset {p : Quotient r} {V : Set (Quotient r)} (hV : V ∈ 𝓝 p) :
    ∃ R, mooreRegion R ∧ p ∈ R ∧ R ⊆ V := by
  obtain ⟨e, he, heV⟩ := (mem_nhds_iff_tube hG).1 hV
  obtain ⟨R, hR, hpR, hRT⟩ := exists_region_in_tube hG p he
  exact ⟨R, hR, hpR, hRT.trans heV⟩

/-- **Moore's regions form a basis of the quotient topology.** -/
theorem isTopologicalBasis_mooreRegion :
    TopologicalSpace.IsTopologicalBasis {R : Set (Quotient r) | mooreRegion R} :=
  TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun _ hR => hR.1)
    fun _ _ hpV hV => exists_region_subset hG (hV.mem_nhds hpV)

/-- **The region topology of `spaceOfElts r` is the quotient topology.** -/
theorem spaceOfElts_topology :
    (spaceOfElts r).topology = (inferInstance : TopologicalSpace (Quotient r)) :=
  (isTopologicalBasis_mooreRegion hG).eq_generateFrom.symm

/-- **Theorem 4** (p. 420). `p` is a limit element of `K` iff every region containing `p` contains
an element of `K` other than `p`. Proof: Theorem 3 (regions inside every tube) and the openness of
regions, through `isLimitElt_iff`. -/
theorem m25_theorem4 {p : Quotient r} {K : Set (Quotient r)} :
    IsLimitElt p K ↔ (spaceOfElts r).IsLimitPt p K := by
  rw [isLimitElt_iff hG, accPt_iff_nhds]
  constructor
  · intro h R hR hpR
    obtain ⟨y, ⟨hyR, hyK⟩, hyp⟩ := h R (hR.1.mem_nhds hpR)
    exact ⟨y, hyK, hyR, hyp⟩
  · intro h V hV
    obtain ⟨R, hR, hpR, hRV⟩ := exists_region_subset hG hV
    obtain ⟨y, hyK, hyR, hyp⟩ := h R hR hpR
    exact ⟨y, ⟨hRV hyR, hyK⟩, hyp⟩

/-- Moore's `M'` (for the regions of `spaceOfElts r`) is the quotient closure. -/
theorem cl_eq_closure_quot (M : Set (Quotient r)) : (spaceOfElts r).cl M = closure M := by
  ext X
  rw [(isTopologicalBasis_mooreRegion hG).mem_closure_iff]
  constructor
  · rintro (hX | hX) R hR hXR
    · exact ⟨X, hXR, hX⟩
    · exact (hX R hR hXR).1
  · intro h
    by_cases hXM : X ∈ M
    · exact Or.inl hXM
    · exact Or.inr fun R hR hXR => ⟨h R hR hXR, ⟨X, hXR, hXM⟩⟩

/-- **Moore's boundary** (p. 417), read with "a limit element of `G`" in its second clause (as
printed, "of `H`", that clause would be empty): the elements of `H` that are limit elements of
`G − H`, together with the elements not in `H` that are limit elements of `H`. So read, it is the
frontier of `H` in the quotient topology. -/
theorem m25_boundary_iff {H : Set (Quotient r)} {p : Quotient r} :
    ((p ∈ H ∧ IsLimitElt p Hᶜ) ∨ (p ∉ H ∧ IsLimitElt p H)) ↔ p ∈ frontier H := by
  have key : ∀ C : Set (Quotient r), p ∉ C → (AccPt p (Filter.principal C) ↔ p ∈ closure C) :=
    fun C hC => by
      rw [accPt_principal_iff_clusterPt, mem_closure_iff_clusterPt, diff_singleton_eq_self hC]
  rw [isLimitElt_iff hG, isLimitElt_iff hG, frontier_eq_closure_inter_closure]
  by_cases hp : p ∈ H
  · rw [key Hᶜ (not_not_intro hp)]
    exact ⟨fun h => ⟨subset_closure hp, h.elim And.right (fun h' => absurd hp h'.1)⟩,
      fun h => Or.inl ⟨hp, h.2⟩⟩
  · rw [key H hp]
    exact ⟨fun h => ⟨h.elim (fun h' => absurd h'.1 hp) And.right,
      subset_closure (show p ∈ Hᶜ from hp)⟩, fun h => Or.inr ⟨hp, h.1⟩⟩

end hG

/-! ### "The" unbounded complementary domain -/

/-- "**The** unbounded complementary domain" (pp. 417, 418): a set of elements `H` with
`ptsOf r H` bounded has exactly one complementary component whose point set is unbounded.
*Shape change:* the skeleton's `hH : IsClosed H` and the section hypothesis `hG` are not used
and are dropped: the complement of a large ball is connected and lies in one component. -/
theorem m25_unbounded_unique {H : Set (Quotient r)}
    (hHb : Bornology.IsBounded (ptsOf r H)) :
    ∃ y ∉ H, ¬ Bornology.IsBounded (ptsOf r (connectedComponentIn Hᶜ y)) ∧
      ∀ z ∉ H, ¬ Bornology.IsBounded (ptsOf r (connectedComponentIn Hᶜ z)) →
        connectedComponentIn Hᶜ z = connectedComponentIn Hᶜ y := by
  obtain ⟨R, hR⟩ := hHb.subset_closedBall (0 : Pt)
  set U := (closedBall (0 : Pt) R)ᶜ with hU
  have hUH : Quotient.mk r '' U ⊆ Hᶜ := by
    rintro _ ⟨u, hu, rfl⟩ hmem
    exact hu (hR hmem)
  have hUc : IsPreconnected (Quotient.mk r '' U) :=
    (isPreconnected_compl_closedBall R).image _ continuous_mk.continuousOn
  set u : Pt := (|R| + 1, 0)
  have huU : u ∈ U := by
    simp only [U, u, mem_compl_iff, mem_closedBall, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, norm_zero, not_le]
    rw [abs_of_pos (by positivity : (0:ℝ) < |R| + 1)]
    exact lt_of_lt_of_le (by linarith [le_abs_self R]) (le_max_left _ _)
  have huH : Quotient.mk r u ∉ H := hUH ⟨u, huU, rfl⟩
  have hsub : Quotient.mk r '' U ⊆ connectedComponentIn Hᶜ (Quotient.mk r u) :=
    hUc.subset_connectedComponentIn ⟨u, huU, rfl⟩ hUH
  refine ⟨Quotient.mk r u, huH, fun hb => ?_, fun z hz hzb => ?_⟩
  · have : U ⊆ ptsOf r (connectedComponentIn Hᶜ (Quotient.mk r u)) := fun w hw => hsub ⟨w, hw, rfl⟩
    exact NormedSpace.unbounded_univ ℝ Pt (by
      rw [← union_compl_self (closedBall (0 : Pt) R)]
      exact isBounded_closedBall.union (hb.subset this))
  · have : ¬ ptsOf r (connectedComponentIn Hᶜ z) ⊆ closedBall 0 R := fun h =>
      hzb (isBounded_closedBall.subset h)
    obtain ⟨w, hw, hwU⟩ := Set.not_subset.1 this
    have h1 := connectedComponentIn_eq hw
    have h2 := connectedComponentIn_eq (hsub ⟨w, hwU, rfl⟩)
    rw [h1, ← h2]

end HPC.Moore
