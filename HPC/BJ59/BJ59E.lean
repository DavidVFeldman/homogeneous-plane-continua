import HPC.BJ59.BJ59D
import HPC.Plane.Descr
import HPC.PseudoArc.Theorem10
import HPC.BJ59.CircMap
import HPC.BJ59.CircPlane

/-!
# Batch 202: Part G, V — a plane circle of pseudo-arcs

The skeleton of commission 202 (`doc/batches/COMMISSION-batch202.md`,
`doc/batches/skeletons/BJ59E.lean`). Bing–Jones §7 (pp. 189–191) asserts a plane circle of
pseudo-arcs without constructing it. This batch constructs one by a route that is not
Bing–Jones's (commission §1):

* §2 circular descriptions: nested circular chains whose links carry arcs of the base circle;
* §3 the recognition theorem: a circular description describes a circle of pseudo-arcs;
* §4 sweep patterns: explicit patterns satisfying the conditions of §2;
* §5 the circular planar step: tame circular chains in the plane realize those patterns;
* §6 the assembly, `BJPlaneExample`, and the classification with no named hypothesis.

The skeleton was split (commission: "You may split it under `HPC/BJ59/`"). Declarations of the
skeleton that live in other files, textually unchanged:

* §2 `CircDescr`, `CircDescr.M`, `CircDescr.fib` and §3 `CircDescr.isCompact_M`,
  `CircDescr.inter_M_nonempty`, `CircDescr.fib_meets`: `HPC/BJ59/CircDescr.lean`;
* §3 `CircDescr.isCircleOfPA`: `HPC/BJ59/CircMap.lean`;
* §4 `sweepQ`, `exists_sweepPattern`: `HPC/BJ59/SweepPattern.lean`;
* §5 `stdRectZ`, `zoneZ`, `circExp`, `stdCircLink`, `stdCircZone`, `stdCircLink_meet_iff`:
  `HPC/BJ59/CircStd.lean`;
* §5 `circ_step`: `HPC/BJ59/CircStep.lean`.

This file keeps §6. The description itself is `planeDescr` (`HPC/BJ59/CircPlane.lean`).

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
§7, pp. 189–191 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §6. The assembly and the classification -/

/-- **A circular description in the plane** (commission §6.1–6.2): levels built alternately by
`exists_sweepPattern` and `circ_step`, from the standard circular chain of 16 links. -/
theorem exists_circDescr_plane : Nonempty (CircDescr Pt) := ⟨planeDescr⟩

/-- **A plane circle of pseudo-arcs** (Bing–Jones §7, by the construction of this batch). -/
theorem bjPlaneExample : BJPlaneExample := by
  obtain ⟨Δ⟩ := exists_circDescr_plane
  exact ⟨Δ.M, Δ.isCircleOfPA⟩

/-- **The classification of homogeneous plane continua with Bing–Jones's third class**, with no
named hypothesis. -/
theorem ho16_classification₄ (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M :=
  ho16_classification₃ bjPlaneExample M hnt

/-- **The plane form of the classification**, with no named hypothesis. -/
theorem ho16_classification_plane₄ :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) :=
  ho16_classification_plane₃ bjPlaneExample

/-- **Domokos–Prajs, Theorem 6.1, "if"**, with no named hypothesis. -/
theorem dp22_theorem61' {X Y : Type} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    {f : X → Circle} (hf : IsAtomicCircPAMap f) (hY : IsCircleOfPA Y) : Nonempty (X ≃ₜ Y) :=
  dp22_theorem61 bjThm10 hf hY

/-- **Domokos–Prajs, Theorem 6.1, both directions**, with no named hypothesis. -/
theorem dp22_theorem61_iff' {X : Type} [MetricSpace X] [CompactSpace X] :
    IsCircleOfPA X ↔ ∃ f : X → Circle, IsAtomicCircPAMap f :=
  dp22_theorem61_iff bjThm10 bjPlaneExample

/-- **The circle-likeness step**, with no named hypothesis. -/
theorem hoCircleLike' : HOCircleLike := hoCircleLike bjThm10 bjPlaneExample

end HPC.BJ59
