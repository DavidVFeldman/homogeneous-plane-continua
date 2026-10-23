import HPC.Plane.SorgenfreyMain

/-!
# Batch 102: Sorgenfrey's theorem (Nadler 11.23–11.35)

Source: S. B. Nadler, *Continuum Theory* (1992), Chapter XI §§4–5: 11.22–11.35. Nadler's "triod"
(11.22) is batch 92's `IsTriod`; "unicoherent" is `IsUnicoherent`. Everything here is for a compact
metric space `S` and continua `X ⊆ S` (`Fold.Q78.IsContinuum`).

## Layout (shape change: the skeleton is split over four files)

* `SorgenfreyDefs.lean` — the skeleton's definitions `IsEssentialSum₃`, `IsEssentialSum₂`,
  `IsWeakTriod` (11.23–11.24) and `IrrFromTo` (11.29), unchanged, and general topology
  (Nadler 5.4/5.7 boundary bumping, 6.2, 6.3).
* `SorgenfreyLemmas.lean` — 11.25–11.33, under the skeleton's names. **11.28 as transcribed is
  false** (`isConnected_diff_of_superset_false`: `H = Ū` gives `U ∖ H = ∅`); the corrected
  `isConnected_diff_of_superset'` adds Nadler's tacit `U ∖ H ≠ ∅`. In 11.31 the unused hypothesis
  `B ⊆ Ū` is dropped; in 11.32 the hypothesis `A ≠ Ū` is dropped (it follows from `W̄ = E ⊕ F`).
* `SorgenfreyMain.lean` — the core of 11.34: part (a), `exists_irrFromTo_point`.
* this file — 11.34 (`sorgenfrey`), 11.35, and the two Fugate consequences.

Batch 103 (pruning): batch 100's sorried `exists_irreducibleBetween_of_atriodic` and
`isTerminalSub_iff_irreducible` (formerly in `Fugate66.lean`) were deleted; their statements now live
here, proved, under those names. The batch-102 names `sorgenfrey_irreducible_of_atriodic_hu` and
`isTerminalSub_iff_irreducible'` are kept as aliases.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Nadler 11.15.1** (the case used in 11.34): a nondegenerate indecomposable continuum is
irreducible between two of its points — a point `p` and a point outside the composant of `p`. -/
theorem exists_irreducible_of_indecomposable {X : Set S} (hI : Fold.Q78.IsIndecomposable X)
    (hnd : X.Nontrivial) : ∃ p q : S, p ≠ q ∧ IsIrreducibleBetween X p q := by
  obtain ⟨p, hp⟩ := hnd.nonempty
  obtain ⟨q, hq, hpq⟩ := T13.exists_not_mem_proper_subcontinua (M := X) hI hp
  refine ⟨p, q, fun he => ?_, hI.1, hp, hq, fun K hK hKX hpK hqK => ?_⟩
  · subst he
    refine hpq {p} ⟨isCompact_singleton, isConnected_singleton⟩ (singleton_subset_iff.mpr hp)
      (fun h' => ?_) rfl rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hnd
    rw [← h'] at ha hb
    exact hab (ha.trans hb.symm)
  · by_contra hne
    exact hpq K hK hKX hne hpK hqK

/-- **Sorgenfrey's theorem (Nadler 11.34).** A nondegenerate unicoherent continuum which is not a
triod is irreducible between two of its points. -/
theorem sorgenfrey {X : Set S} (hX : Fold.Q78.IsContinuum X) (hnd : X.Nontrivial)
    (hu : IsUnicoherent X) (hnt : ¬ IsTriod X) : ∃ p q : S, p ≠ q ∧ IsIrreducibleBetween X p q := by
  by_cases hI : Fold.Q78.IsIndecomposable X
  · exact exists_irreducible_of_indecomposable hI hnd
  have hdec : ∃ Y Z : Set S, IsEssentialSum₂ X Y Z := by
    by_contra hc
    push_neg at hc
    refine hI ⟨hX, fun A B hA hB _ _ hAB => ?_⟩
    by_contra hne
    push_neg at hne
    exact hc A B ⟨hX, hA, hB, hAB.symm, hne.1, hne.2⟩
  obtain ⟨Y, Z, h⟩ := hdec
  have hnt' : ¬ IsWeakTriod X := fun hw => hnt ((isTriod_iff_isWeakTriod hX hu).mpr hw)
  obtain ⟨p, hp, hU⟩ := exists_irrFromTo_point h hu hnt'
  obtain ⟨q, hq, hV⟩ := exists_irrFromTo_point h.symm hu hnt'
  exact ⟨p, q, fun he => hp.2 (he ▸ h.symm.diff_subset_left hq),
    nadler_11_33 h hu hnt' hp hq hU hV⟩

/-- **11.35.** A nondegenerate unicoherent continuum is irreducible iff it is not a triod. -/
theorem irreducible_iff_not_isTriod {X : Set S} (hX : Fold.Q78.IsContinuum X) (hnd : X.Nontrivial)
    (hu : IsUnicoherent X) :
    (∃ p q : S, p ≠ q ∧ IsIrreducibleBetween X p q) ↔ ¬ IsTriod X :=
  ⟨fun ⟨p, q, _, hirr⟩ ht => not_irreducible_of_isWeakTriod (isWeakTriod_of_isTriod ht) p q hirr,
    sorgenfrey hX hnd hu⟩

/-- **Sorgenfrey: an atriodic hereditarily unicoherent continuum is irreducible** between two of
its points (used in Fugate's Lemma 3). Batch 100's statement, proved from `sorgenfrey`. -/
theorem exists_irreducibleBetween_of_atriodic {M : Set S} (hM : Fold.Q78.IsContinuum M)
    (hnd : M.Nontrivial) (hat : IsAtriodic M) (hhu : IsHereditarilyUnicoherent M) :
    ∃ p q : S, p ≠ q ∧ IsIrreducibleBetween M p q :=
  sorgenfrey hM hnd (hhu M Subset.rfl hM hnd) (hat M Subset.rfl)

alias sorgenfrey_irreducible_of_atriodic_hu := exists_irreducibleBetween_of_atriodic

/-- **Fugate, Lemma 3.** In an atriodic hereditarily unicoherent continuum `M`, a subcontinuum `A`
is terminal iff for every subcontinuum `B` meeting `A`, `A ∪ B` is irreducible between two points
one of which lies in `A` (batch 100's `irreducible_of_isTerminalSub` and
`isTerminalSub_of_irreducible`, with `exists_irreducibleBetween_of_atriodic` discharging the
irreducibility hypothesis). -/
theorem isTerminalSub_iff_irreducible {M A : Set S} (hat : IsAtriodic M)
    (hhu : IsHereditarilyUnicoherent M) (hA : Fold.Q78.IsContinuum A) (hAM : A ⊆ M) :
    IsTerminalSub M A ↔ ∀ B : Set S, Fold.Q78.IsContinuum B → B ⊆ M → (B ∩ A).Nonempty →
      ∃ p q : S, p ∈ A ∧ IsIrreducibleBetween (A ∪ B) p q := by
  refine ⟨irreducible_of_isTerminalSub fun W hWM hW hnt => ?_, isTerminalSub_of_irreducible hA hAM⟩
  obtain ⟨p, q, -, h⟩ := exists_irreducibleBetween_of_atriodic hW hnt
    (fun T hT => hat T (hT.trans hWM)) (fun K hK => hhu K (hK.trans hWM))
  exact ⟨p, q, h⟩

alias isTerminalSub_iff_irreducible' := isTerminalSub_iff_irreducible

end HPC.Plane
