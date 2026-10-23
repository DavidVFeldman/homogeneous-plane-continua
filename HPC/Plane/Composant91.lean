import HPC.Plane.EndPoints51
import HPC.PseudoArc.T13Topo

/-!
# Batch 91: composants are dense, and the step of Bing's proof of Theorem 10

* `exists_subcontinuum_meeting_closedBall` — **boundary bumping**: in a continuum `M`, the
  component of `p` in `M ∖ B(x, s)` meets the closed ball `B̄(x, s)` (when `p ∉ B(x, s)`). Proof:
  in the compact space `M ∖ B(x, s)` a component is the intersection of the clopen sets containing
  it; by compactness one clopen set misses the compact set of points adherent to `M ∩ B(x, s)`,
  and the clopen form of boundary bumping (`T13.clopen_meets_closure_diff`) forbids this.
* `exists_proper_subcontinuum_meeting` — **the composant of `p` is dense**: every open set meeting
  a nondegenerate continuum `M` meets a proper subcontinuum of `M` through `p`.
* `exists_proper_meeting_all_links'` — the step of Bing's proof of Theorem 10 (p. 659): if `p`
  satisfies condition B (in particular condition A), some proper subcontinuum through `p` meets every
  link of a chain each of whose links meets `M`. (The subcontinua through `p` are nested, so the
  largest of finitely many, one per link, does.)
-/

namespace HPC.Plane

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- **Boundary bumping** (metric form). If `M` is a continuum, `p, x ∈ M` and `p ∉ B(x, s)`, some
subcontinuum of `M ∖ B(x, s)` contains `p` and meets the closed ball `B̄(x, s)`. -/
theorem exists_subcontinuum_meeting_closedBall {M : Set X} (hM : Fold.Q78.IsContinuum M)
    {p x : X} (hp : p ∈ M) (hx : x ∈ M) {s : ℝ} (hs : 0 < s) (hpx : s ≤ dist p x) :
    ∃ K : Set X, Fold.Q78.IsContinuum K ∧ K ⊆ M \ ball x s ∧ p ∈ K ∧
      (K ∩ closedBall x s).Nonempty := by
  classical
  set F := M \ ball x s with hF_def
  have hFc : IsCompact F := hM.1.diff isOpen_ball
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc
  have hpF : p ∈ F := ⟨hp, fun h => by rw [mem_ball] at h; linarith⟩
  set p' : F := ⟨p, hpF⟩
  set C := connectedComponent p' with hC_def
  set K : Set X := Subtype.val '' C with hK_def
  have hKc : IsCompact K := (isClosed_connectedComponent.isCompact).image continuous_subtype_val
  have hKconn : IsConnected K := isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have hKF : K ⊆ F := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have hpK : p ∈ K := ⟨p', mem_connectedComponent, rfl⟩
  refine ⟨K, ⟨hKc, hKconn⟩, hKF, hpK, ?_⟩
  -- the closure of `M ∩ B(x, s)` lies in the closed ball
  have hcl : closure (M \ F) ⊆ closedBall x s := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    have : z ∈ ball x s := by
      by_contra h
      exact hz.2 ⟨hz.1, h⟩
    exact ball_subset_closedBall this
  suffices h : (K ∩ closure (M \ F)).Nonempty by
    obtain ⟨z, hzK, hz⟩ := h
    exact ⟨z, hzK, hcl hz⟩
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  -- the points of `F` adherent to `M \ F`
  set H : Set F := Subtype.val ⁻¹' closure (M \ F) with hH_def
  have hHc : IsCompact H := (isClosed_closure.preimage continuous_subtype_val).isCompact
  have hCH : H ∩ ⋂ s : { s : Set F // IsClopen s ∧ p' ∈ s }, (s : Set F) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzH hzC
    have : (z : X) ∈ K ∩ closure (M \ F) := ⟨⟨z, hzC, rfl⟩, hzH⟩
    rw [hcon] at this
    exact this
  obtain ⟨u, hu⟩ := hHc.elim_finite_subfamily_closed
    (fun s : { s : Set F // IsClopen s ∧ p' ∈ s } => (s : Set F)) (fun s => s.2.1.isClosed) hCH
  set W' : Set F := ⋂ i ∈ u, (i : Set F) with hW'_def
  have hW'clopen : IsClopen W' := isClopen_biInter_finset fun i _ => i.2.1
  have hpW' : p' ∈ W' := mem_iInter₂.mpr fun i _ => i.2.2
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW'clopen.isOpen
  set W : Set X := Subtype.val '' W' with hW_def
  have hWcl : IsClosed W := (hW'clopen.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hWF : W ⊆ F := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have hWO : W = F ∩ O := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      refine ⟨z'.2, ?_⟩
      have : z' ∈ Subtype.val ⁻¹' O := by rw [hOW]; exact hz'
      exact this
    · rintro ⟨hzF, hzO⟩
      refine ⟨⟨z, hzF⟩, ?_, rfl⟩
      rw [← hOW]; exact hzO
  have hFne : F ≠ M := by
    intro h
    have : x ∈ F := h ▸ hx
    exact this.2 (mem_ball_self hs)
  obtain ⟨w, hwW, hwcl⟩ := T13.clopen_meets_closure_diff hM.2.isPreconnected diff_subset hFne
    hWF hWcl hO hWO ⟨p, p', hpW', rfl⟩
  obtain ⟨w', hw', rfl⟩ := hwW
  have : w' ∈ H ∩ W' := ⟨hwcl, hw'⟩
  rw [hu] at this
  exact this

/-- **The composant of `p` is dense.** Every open set meeting a nondegenerate continuum `M` meets
some proper subcontinuum of `M` containing `p`. -/
theorem exists_proper_subcontinuum_meeting {M : Set X} (hM : Fold.Q78.IsContinuum M)
    (hnd : M.Nontrivial) {p : X} (hp : p ∈ M) {O : Set X} (hO : IsOpen O) (hOM : (O ∩ M).Nonempty) :
    ∃ K : Set X, K ⊆ M ∧ K ≠ M ∧ Fold.Q78.IsContinuum K ∧ p ∈ K ∧ (K ∩ O).Nonempty := by
  have hsing : {p} ≠ M := fun h => by
    obtain ⟨a, ha, b, hb, hab⟩ := hnd
    rw [← h] at ha hb
    exact hab (ha.trans hb.symm)
  by_cases hpO : p ∈ O
  · exact ⟨{p}, singleton_subset_iff.mpr hp, hsing, ⟨isCompact_singleton, isConnected_singleton⟩,
      rfl, ⟨p, rfl, hpO⟩⟩
  obtain ⟨x, hxO, hxM⟩ := hOM
  have hpx : p ≠ x := fun h => hpO (h ▸ hxO)
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO x hxO
  set s := min (r / 2) (dist p x) with hs_def
  have hs : 0 < s := lt_min (half_pos hr) (dist_pos.mpr hpx)
  obtain ⟨K, hK, hKF, hpK, z, hzK, hz⟩ :=
    exists_subcontinuum_meeting_closedBall hM hp hxM hs (min_le_right _ _)
  refine ⟨K, fun w hw => (hKF hw).1, fun h => ?_, hK, hpK, z, hzK, hrO ?_⟩
  · have : x ∈ K := h ▸ hxM
    exact (hKF this).2 (mem_ball_self hs)
  · rw [mem_closedBall] at hz
    rw [mem_ball]
    have : s ≤ r / 2 := min_le_left _ _
    linarith

/-- **The step of Bing's proof of Theorem 10, under condition B**: a proper subcontinuum through `p`
meets every link of `D`. -/
theorem exists_proper_meeting_all_links_of_condB {M : Set X} (hM : Fold.Q78.IsContinuum M)
    (hnd : M.Nontrivial) {p : X} (hp : CondB M p) {m : ℕ} (D : Chain X m)
    (hmeet : ∀ i, (D.link i ∩ M).Nonempty) :
    ∃ K : Set X, K ⊆ M ∧ K ≠ M ∧ Fold.Q78.IsContinuum K ∧ p ∈ K ∧
      ∀ i, (D.link i ∩ K).Nonempty := by
  classical
  have hK : ∀ i, ∃ K : Set X, K ⊆ M ∧ K ≠ M ∧ Fold.Q78.IsContinuum K ∧ p ∈ K ∧
      (K ∩ D.link i).Nonempty := fun i =>
    exists_proper_subcontinuum_meeting hM hnd hp.1 (D.isOpen i)
      (by obtain ⟨z, h1, h2⟩ := hmeet i; exact ⟨z, h1, h2⟩)
  choose K hKM hKne hKc hpK hKi using hK
  have hsing : {p} ≠ M := fun h => by
    obtain ⟨a, ha, b, hb, hab⟩ := hnd
    rw [← h] at ha hb
    exact hab (ha.trans hb.symm)
  -- the largest of the `K i`, `i ∈ s`
  have hmax : ∀ s : Finset (Fin m), ∃ L : Set X, L ⊆ M ∧ L ≠ M ∧ Fold.Q78.IsContinuum L ∧
      p ∈ L ∧ ∀ i ∈ s, K i ⊆ L := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨{p}, singleton_subset_iff.mpr hp.1, hsing,
        ⟨isCompact_singleton, isConnected_singleton⟩, rfl, fun i hi => absurd hi (by simp)⟩
    | insert j s hj ih =>
      obtain ⟨L, hLM, hLne, hLc, hpL, hL⟩ := ih
      rcases hp.2 (K j) L (hKM j) hLM (hKc j) hLc (hpK j) hpL with h | h
      · refine ⟨L, hLM, hLne, hLc, hpL, fun i hi => ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h
        · exact hL i hi
      · refine ⟨K j, hKM j, hKne j, hKc j, hpK j, fun i hi => ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact le_rfl
        · exact (hL i hi).trans h
  obtain ⟨L, hLM, hLne, hLc, hpL, hL⟩ := hmax Finset.univ
  refine ⟨L, hLM, hLne, hLc, hpL, fun i => ?_⟩
  obtain ⟨z, hzK, hzD⟩ := hKi i
  exact ⟨z, hzD, hL i (Finset.mem_univ i) hzK⟩

end HPC.Plane
