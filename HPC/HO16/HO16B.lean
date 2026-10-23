import HPC.HO16.FoldDefs
import HPC.HO16.Subdiv
import HPC.HO16.PLLib
import HPC.HO16.Lemma6
import HPC.HO16.FoldExists
import HPC.HO16.Thm8Fold
import HPC.HO16.Prop7
import HPC.HO16.FoldExample

/-!
# Batch 194: Hoehn–Oversteegen Theorem 1, II — PL graphs, simple folds, Theorem 8

The batch-194 skeleton (`doc/batches/skeletons/HO16B.lean`), split under `HPC/HO16/`:

* `FoldDefs` (§2): `relFrontier`, `IsFoldTriple`, `IsSimpleFoldOf`;
* `Subdiv` and `PLLib` (§3): the common subdivision and the PL-graph library;
* `FoldExists` (§4): `exists_simpleFold`;
* `Lemma6` (§5): `ho16_lemma6`;
* `Thm8Fold` (§6): `ho16_theorem8`;
* `Prop7` (§7): `ho16_prop7`;
* `FoldExample`: a concrete fold triple on `[0, 3]` (non-vacuity of `IsFoldTriple`,
  `IsSimpleFoldOf` and the hypotheses of `ho16_prop7`);
* this file (§8): the certificates for Theorem 1 as restated on p. 211 and Theorem 1′.

Source: Hoehn–Oversteegen 2016 (`doc/sources/hoehn-oversteegen2016.pdf`), §4: Definition 5,
Lemma 6, the construction on pp. 185–186, Proposition 7, Theorem 8. "Regular" (H–O p. 184) is
read as "PL graph" throughout. Route: commission 194.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ## §8. Theorem 1 and Theorem 1′ as printed (commission §8) -/

/-- H–O p. 212: **surjective semispan zero**: every subcontinuum `Z ⊆ X × X` with `π₂(Z) = X`
meets the diagonal. -/
def SurjSemiSpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ Z : Set (X × X), Fold.Q78.IsContinuum Z → Prod.snd '' Z = univ → ∃ p ∈ Z, p.1 = p.2

/-- A one-point space is hereditarily indecomposable (H–O p. 178: "every non-degenerate
subcontinuum is indecomposable"; here: every subcontinuum). -/
theorem isHereditarilyIndecomposable_unit :
    IsHereditarilyIndecomposable (univ : Set Unit) := by
  intro K _ hK
  refine ⟨hK, fun A B hA _ _ _ _ => Or.inl ?_⟩
  rw [hA.2.nonempty.eq_univ, hK.2.nonempty.eq_univ]

/-- A one-point space has span zero in H–O's sense. -/
theorem hoSpanZero_unit : HOSpanZero Unit := by
  intro Z hZ _
  obtain ⟨p, hp⟩ := hZ.2.nonempty
  exact ⟨p, hp, Subsingleton.elim _ _⟩

/-- A one-point space has surjective semispan zero. -/
theorem surjSemiSpanZero_unit : SurjSemiSpanZero Unit := by
  intro Z hZ _
  obtain ⟨p, hp⟩ := hZ.2.nonempty
  exact ⟨p, hp, Subsingleton.elim _ _⟩

/-- A one-point space is not homeomorphic to a pseudo-arc (pseudo-arcs are non-degenerate). -/
theorem not_homeomorph_pseudoArc_unit :
    ¬ ∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (Unit ≃ₜ M₀) := by
  rintro ⟨M₀, hPA, ⟨e⟩⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hPA.2.2
  apply hab
  have h1 : e (e.symm ⟨a, ha⟩) = ⟨a, ha⟩ := e.apply_symm_apply _
  have h2 : e (e.symm ⟨b, hb⟩) = ⟨b, hb⟩ := e.apply_symm_apply _
  have h3 : e.symm ⟨a, ha⟩ = e.symm ⟨b, hb⟩ := Subsingleton.elim _ _
  rw [h3] at h1
  exact congrArg Subtype.val (h1.symm.trans h2)

/-- **Theorem 1 as restated on p. 211** ("A continuum X is homeomorphic to the pseudo-arc if and
only if X is hereditarily indecomposable and has span zero") fails for a one-point continuum. -/
theorem ho16_theorem1_printed_false :
    ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X],
      (∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (X ≃ₜ M₀)) ↔
        (IsHereditarilyIndecomposable (univ : Set X) ∧ HOSpanZero X) := by
  intro H
  exact not_homeomorph_pseudoArc_unit
    ((H Unit).2 ⟨isHereditarilyIndecomposable_unit, hoSpanZero_unit⟩)

/-- **Theorem 1′ as printed on p. 212** ("A continuum X is homeomorphic to the pseudo-arc if and
only if X is hereditarily indecomposable and has surjective semispan zero") fails for a one-point
continuum. -/
theorem ho16_theorem1prime_printed_false :
    ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X],
      (∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (X ≃ₜ M₀)) ↔
        (IsHereditarilyIndecomposable (univ : Set X) ∧ SurjSemiSpanZero X) := by
  intro H
  exact not_homeomorph_pseudoArc_unit
    ((H Unit).2 ⟨isHereditarilyIndecomposable_unit, surjSemiSpanZero_unit⟩)

end HPC.HO16
