import HPC.Jones.Jones49Order
import HPC.PseudoArc.T13Topo

/-!
# Batch 149, item D: Whyburn's local separating points, (9.1)

The two definitions of the skeleton (`IsSepPointOf`, `IsLocalSepPoint`, verbatim) and Whyburn's
(9.1): a separating point of an open set `R` separates every open `U` with `p ∈ U ⊆ R`.

Proof (Whyburn's, with the step "[I, (10.2)] … the components … are nondegenerate" supplied by a
boundary-bumping argument in the locally compact setting, `exists_continuum_bump_compact`): with
`Q` the component of `R` containing `p` and `R − p ⊆ A ∪ B`, the set `D = Q − (B − p)`
(= `Q·R_a + p`) is connected (`isPreconnected_side`) and closed in `R`. For a compact neighbourhood
`K ⊆ U` of `p`, either `D ⊆ K` or a continuum through `p` inside `D ∩ K` reaches the frontier of
`K`; either way the component of `U` containing `p` meets `A − p`. The same separation `A, B`
then works for `U`.
-/

namespace HPC.Jones

open Set Topology Metric

section Whyburn

variable {X : Type*} [MetricSpace X]

/-- Whyburn's *separating point of an open set `R`* (p. 61, as used in the proof of (9.1)): there is
a separation `R − p = R_a + R_b` (disjoint, relatively open in `R − p`) with `a ∈ R_a`, `b ∈ R_b`
both in the component of `R` containing `p`. Record the reading. -/
def IsSepPointOf (p : X) (R : Set X) : Prop :=
  p ∈ R ∧ ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ R \ {p} ⊆ A ∪ B ∧
    Disjoint (A ∩ (R \ {p})) (B ∩ (R \ {p})) ∧
    (A ∩ (connectedComponentIn R p \ {p})).Nonempty ∧
    (B ∩ (connectedComponentIn R p \ {p})).Nonempty

/-- Whyburn's *local separating point* (p. 61): "a separating point of some open set in `L`". -/
def IsLocalSepPoint (p : X) : Prop := ∃ R, IsOpen R ∧ IsSepPointOf p R

/-- **Boundary bumping for a compact piece of a connected set.** If `F` is a compact proper subset
of a preconnected set `M` and `p ∈ F`, a continuum through `p` inside `F` meets the closure of
`M − F`. (The proof of batch 133's `exists_continuum_bump_closed`, with compactness of `F` assumed
instead of that of the space.) -/
theorem exists_continuum_bump_compact {M F : Set X} (hM : IsPreconnected M) (hFc : IsCompact F)
    (hFM : F ⊆ M) (hFne : F ≠ M) {p : X} (hpF : p ∈ F) :
    ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ⊆ F ∧ p ∈ K ∧
      (K ∩ closure (M \ F)).Nonempty := by
  classical
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc
  set p' : F := ⟨p, hpF⟩
  set C := connectedComponent p'
  set K : Set X := Subtype.val '' C
  have hKc : IsCompact K := (isClosed_connectedComponent.isCompact).image continuous_subtype_val
  have hKconn : IsConnected K :=
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have hKF : K ⊆ F := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have hpK : p ∈ K := ⟨p', mem_connectedComponent, rfl⟩
  refine ⟨K, hKc, hKconn, hKF, hpK, ?_⟩
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  set H : Set F := Subtype.val ⁻¹' closure (M \ F)
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
  set W' : Set F := ⋂ i ∈ u, (i : Set F)
  have hW'clopen : IsClopen W' := isClopen_biInter_finset fun i _ => i.2.1
  have hpW' : p' ∈ W' := mem_iInter₂.mpr fun i _ => i.2.2
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW'clopen.isOpen
  set W : Set X := Subtype.val '' W'
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
  obtain ⟨w, hwW, hwcl⟩ := HPC.T13.clopen_meets_closure_diff hM hFM hFne hWF hWcl hO hWO
    ⟨p, p', hpW', rfl⟩
  obtain ⟨w', hw', rfl⟩ := hwW
  have : w' ∈ H ∩ W' := ⟨hwcl, hw'⟩
  rw [hu] at this
  exact this

/-- One side of a separation of `Q − p`, together with `p`, is preconnected: `Q − (B − p)`. -/
theorem isPreconnected_side {Q A B : Set X} {p : X} (hQ : IsPreconnected Q) (hpQ : p ∈ Q)
    (hA : IsOpen A) (hB : IsOpen B) (hcov : Q \ {p} ⊆ A ∪ B)
    (hdisj : ∀ z ∈ Q \ {p}, z ∈ A → z ∉ B) : IsPreconnected (Q \ (B \ {p})) := by
  have main : ∀ {u v : Set X}, IsOpen u → IsOpen v → Q \ (B \ {p}) ⊆ u ∪ v →
      Q \ (B \ {p}) ∩ (u ∩ v) = ∅ → p ∈ u → Q \ (B \ {p}) ⊆ u := by
    intro u v hu hv hc hd hpu
    have hc' : Q ⊆ (u ∪ (B \ {p})) ∪ (v ∩ (A \ {p})) := by
      intro z hz
      by_cases hzp : z = p
      · exact Or.inl (Or.inl (hzp ▸ hpu))
      by_cases hzB : z ∈ B
      · exact Or.inl (Or.inr ⟨hzB, hzp⟩)
      have hzD : z ∈ Q \ (B \ {p}) := ⟨hz, fun h => hzB h.1⟩
      have hzA : z ∈ A := (hcov ⟨hz, hzp⟩).resolve_right hzB
      rcases hc hzD with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨h, hzA, hzp⟩
    have hd' : Q ∩ ((u ∪ (B \ {p})) ∩ (v ∩ (A \ {p}))) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun z ⟨hzQ, hzuB, hzv, hzA, hzp⟩ => ?_
      have hzB : z ∉ B := hdisj z ⟨hzQ, hzp⟩ hzA
      have hzu : z ∈ u := hzuB.resolve_right fun h => hzB h.1
      exact (eq_empty_iff_forall_notMem.1 hd) z ⟨⟨hzQ, fun h => hzB h.1⟩, hzu, hzv⟩
    rcases isPreconnected_iff_subset_of_disjoint.1 hQ _ _ (hu.union (hB.sdiff isClosed_singleton))
      (hv.inter (hA.sdiff isClosed_singleton)) hc' hd' with h | h
    · rintro z ⟨hzQ, hzB⟩
      exact (h hzQ).resolve_right hzB
    · exact absurd rfl (h hpQ).2.2
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hc hd
  have hpD : p ∈ Q \ (B \ {p}) := ⟨hpQ, fun h => h.2 rfl⟩
  rcases hc hpD with hpu | hpv
  · exact Or.inl (main hu hv hc hd hpu)
  · exact Or.inr (main hv hu (by rwa [union_comm]) (by rwa [inter_comm v]) hpv)

/-- The component of a point in an open set `R` is closed in `R`. -/
theorem closure_inter_connectedComponentIn_subset {R : Set X} {p : X} (hpR : p ∈ R) :
    closure (connectedComponentIn R p) ∩ R ⊆ connectedComponentIn R p := by
  have hsub : connectedComponentIn R p ⊆ closure (connectedComponentIn R p) ∩ R :=
    subset_inter subset_closure (connectedComponentIn_subset _ _)
  exact (isPreconnected_connectedComponentIn.subset_closure hsub inter_subset_left
    ).subset_connectedComponentIn (hsub (mem_connectedComponentIn hpR)) inter_subset_right

/-- The side lemma used twice in (9.1): the component of `U` containing `p` meets `A − p`. -/
theorem whyburn_9_1_side [LocallyCompactSpace X] {p : X} {R U A B : Set X}
    (hU : IsOpen U) (hpU : p ∈ U) (hUR : U ⊆ R) (hpR : p ∈ R) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : R \ {p} ⊆ A ∪ B) (hdisj : Disjoint (A ∩ (R \ {p})) (B ∩ (R \ {p})))
    (hAQ : (A ∩ (connectedComponentIn R p \ {p})).Nonempty) :
    (A ∩ (connectedComponentIn U p \ {p})).Nonempty := by
  set Q := connectedComponentIn R p
  have hQR : Q ⊆ R := connectedComponentIn_subset _ _
  have hpQ : p ∈ Q := mem_connectedComponentIn hpR
  have hdisj' : ∀ z ∈ Q \ {p}, z ∈ A → z ∉ B := fun z hz hzA hzB =>
    disjoint_left.1 hdisj ⟨hzA, hQR hz.1, hz.2⟩ ⟨hzB, hQR hz.1, hz.2⟩
  set D := Q \ (B \ {p})
  have hD : IsPreconnected D := isPreconnected_side isPreconnected_connectedComponentIn hpQ hA hB
    (fun z hz => hcov ⟨hQR hz.1, hz.2⟩) hdisj'
  have hpD : p ∈ D := ⟨hpQ, fun h => h.2 rfl⟩
  -- points of `D − p` lie in `A`
  have hDA : ∀ z ∈ D, z ≠ p → z ∈ A := fun z hz hzp =>
    (hcov ⟨hQR hz.1, hzp⟩).resolve_right fun hzB => hz.2 ⟨hzB, hzp⟩
  obtain ⟨K, hKc, hpK, hKU⟩ := exists_compact_subset hU hpU
  -- `D ∩ K` is compact
  have hDK : IsCompact (D ∩ K) := by
    refine hKc.of_isClosed_subset ?_ inter_subset_right
    have : D ∩ K = closure D ∩ K := by
      refine Subset.antisymm (inter_subset_inter_left _ subset_closure) ?_
      rintro z ⟨hzD, hzK⟩
      have hzR : z ∈ R := hUR (hKU hzK)
      have hzQ : z ∈ Q := closure_inter_connectedComponentIn_subset hpR
        ⟨closure_mono diff_subset hzD, hzR⟩
      refine ⟨⟨hzQ, fun hzB => ?_⟩, hzK⟩
      -- `B − p` is open and disjoint from `D`
      have hO : IsOpen (B \ {p}) := hB.sdiff isClosed_singleton
      obtain ⟨w, hwB, hwD⟩ := mem_closure_iff.1 hzD _ hO hzB
      exact hwD.2 hwB
    rw [this]; exact isClosed_closure.inter hKc.isClosed
  obtain ⟨a, haA, haQ, hap⟩ := hAQ
  have haD : a ∈ D := ⟨haQ, fun h => disjoint_left.1 hdisj ⟨haA, hQR haQ, hap⟩
    ⟨h.1, hQR haQ, hap⟩⟩
  by_cases hDK' : D ∩ K = D
  · -- `D ⊆ K ⊆ U`
    have hDU : D ⊆ U := fun z hz => by
      have hz' : z ∈ D ∩ K := by rw [hDK']; exact hz
      exact hKU hz'.2
    exact ⟨a, haA, hD.subset_connectedComponentIn hpD hDU haD, hap⟩
  · obtain ⟨L, -, hLconn, hLDK, hpL, w, hwL, hwcl⟩ :=
      exists_continuum_bump_compact hD hDK inter_subset_left hDK' ⟨hpD, interior_subset hpK⟩
    have hwp : w ≠ p := by
      intro hwp
      rw [hwp] at hwcl
      have : p ∈ closure (Kᶜ) :=
        closure_mono (show D \ (D ∩ K) ⊆ Kᶜ from fun z hz h => hz.2 ⟨hz.1, h⟩) hwcl
      rw [closure_compl] at this
      exact this hpK
    have hLU : L ⊆ U := fun z hz => hKU (hLDK hz).2
    exact ⟨w, hDA w (hLDK hwL).1 hwp,
      hLconn.isPreconnected.subset_connectedComponentIn hpL hLU hwL, hwp⟩

/-- **Whyburn (9.1).** "If `p` is a separating point of an open set `R` in `L` then it is also of
every open set `U` such that `p ⊂ U ⊂ R`."

*Shape change (batch 149):* the skeleton's hypothesis `(hR : IsOpen R)` is dropped; the proof does
not use it (the component of `p` in any set `R` is closed in `R`, and only `U` needs to be open). -/
theorem whyburn_9_1 [LocallyCompactSpace X] {p : X} {R U : Set X}
    (hU : IsOpen U) (hpU : p ∈ U) (hUR : U ⊆ R) (h : IsSepPointOf p R) : IsSepPointOf p U := by
  obtain ⟨hpR, A, B, hA, hB, hcov, hdisj, hAQ, hBQ⟩ := h
  refine ⟨hpU, A, B, hA, hB, fun z hz => hcov ⟨hUR hz.1, hz.2⟩, ?_,
    whyburn_9_1_side hU hpU hUR hpR hA hB hcov hdisj hAQ,
    whyburn_9_1_side hU hpU hUR hpR hB hA (by rwa [union_comm]) hdisj.symm hBQ⟩
  exact hdisj.mono (inter_subset_inter_right _ (diff_subset_diff_left hUR))
    (inter_subset_inter_right _ (diff_subset_diff_left hUR))

end Whyburn

end HPC.Jones
