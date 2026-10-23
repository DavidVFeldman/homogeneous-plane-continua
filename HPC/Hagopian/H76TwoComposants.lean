import HPC.Hagopian.H75Composants

/-!
# Batch 166, item E (part): two further composants in every open set

T12 (p. 347) picks `p`, `q ∈ K ∩ (W − R(E))` "that belong to distinct inaccessible composants [10]
of the indecomposable continuum `Cl R(E)`". After that choice, accessibility is never used (report
166 §1.E); what is used is that `p`, `q` lie outside the composant `R(E)` and in distinct composants.
Inside an open set `W` this needs no Mazurkiewicz: composants are meagre (`composant_isMeagre'`), and
a nonempty open subset of a compact metric space is not (Baire).
-/

namespace HPC.Hagopian

open Set Topology HPC.Jones

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Two points of an open set, off a given composant and in distinct composants.** In an
indecomposable compact connected metric space, every nonempty open set `U` contains points `p`, `q`
with `p`, `q` outside the composant of `z` and `q` outside the composant of `p`. -/
theorem exists_two_composants_in_open (hi : ¬ IsDecomposableSpace X) {U : Set X} (hU : IsOpen U)
    (hne : U.Nonempty) (z : X) :
    ∃ p ∈ U, ∃ q ∈ U, p ∉ Jones.composant z ∧ q ∉ Jones.composant z ∧ q ∉ Jones.composant p := by
  have hU' : ¬ IsMeagre U := not_isMeagre_of_isOpen hU hne
  obtain ⟨p, hpU, hpz⟩ : (U \ Jones.composant z).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at h
    exact hU' ((composant_isMeagre' hi z).mono h)
  obtain ⟨q, hqU, hq⟩ : (U \ (Jones.composant z ∪ Jones.composant p)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, diff_eq_empty] at h
    exact hU' (((composant_isMeagre' hi z).union (composant_isMeagre' hi p)).mono h)
  exact ⟨p, hpU, q, hqU, hpz, fun h => hq (Or.inl h), fun h => hq (Or.inr h)⟩

end HPC.Hagopian
