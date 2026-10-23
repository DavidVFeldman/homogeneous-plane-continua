import HPC.BJ59.BJ59C
import HPC.BJ59.Thm10Defs
import HPC.BJ59.Thm10Lib
import HPC.BJ59.Thm10Pattern
import HPC.BJ59.Thm10Window
import HPC.BJ59.Thm10Sub
import HPC.BJ59.Thm10Runs
import HPC.BJ59.Thm10Glue
import HPC.BJ59.Thm10Pieces
import HPC.BJ59.Thm10Induct
import HPC.BJ59.Thm10Step
import HPC.BJ59.NonVac201
import HPC.BJ59.NonVac201b

/-!
# Batch 201: Part G, IV — Bing–Jones Theorem 10

The skeleton of commission 201 (`doc/batches/skeletons/BJ59D.lean`), split under `HPC/BJ59/`.
Every declaration of the skeleton is delivered, with its statement as in the skeleton except
`exists_pattern` (clause 2 strengthened, see `LEDGER.md`):

* §2 `HasPrivatePoints`, `IsFibreChainMap`, `EndCompat`, `IsFibreFine`: `Thm10Defs.lean`;
* §3 `exists_point_only_of_minimal`, `adjacent_of_properCover`, `isFibreFine_of_isEpsChain`:
  `Thm10Defs.lean`; `exists_pattern`: `Thm10Pattern.lean`; `bj_theorem8_cor_sub`:
  `Thm10Sub.lean`; `bj_theorem5_window`, `exists_window_set`: `Thm10Window.lean`;
* §4 `BJStep`: `Thm10Induct.lean`; `bj_step`: `Thm10Step.lean` (gluing in `Thm10Glue.lean`, the
  pieces in `Thm10Pieces.lean`, runs in `Thm10Runs.lean`);
* §5 `bjThm10_of_step`: `Thm10Induct.lean`; `bjThm10` and the corollaries: this file;
* §7 `nonvac_conditions`: `NonVac201.lean`; the tests of the tools of §3: `NonVac201b.lean`.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
§6, pp. 181–189 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
Route: commission 201.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §5. Theorem 10 and the classification -/

/-- **Bing–Jones, Theorem 10** (pp. 181–189), fibre-preserving form. -/
theorem bjThm10 : BJThm10 := bjThm10_of_step bj_step

/-- **The classification of homogeneous plane continua with Domokos–Prajs's third class**, with
no named hypothesis. -/
theorem ho16_classification_atomic' (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨
      ∃ f : M → Circle, IsAtomicCircPAMap f :=
  ho16_classification_atomic bjThm10 M hnt

/-- **Each circle of pseudo-arcs is homogeneous** (Bing–Jones pp. 173, 189). -/
theorem isHomogeneous_of_isCircleOfPA' {X : Type} [MetricSpace X] (hX : IsCircleOfPA X) :
    IsHomogeneous X :=
  isHomogeneous_of_isCircleOfPA bjThm10 hX

/-- **Any two circles of pseudo-arcs are homeomorphic** (Bing–Jones pp. 173, 189). -/
theorem homeomorph_of_isCircleOfPA' {X Y : Type} [MetricSpace X] [MetricSpace Y]
    (hX : IsCircleOfPA X) (hY : IsCircleOfPA Y) : Nonempty (X ≃ₜ Y) :=
  homeomorph_of_isCircleOfPA bjThm10 hX hY

/-- **The classification with Bing–Jones's third class**, given only the plane example. -/
theorem ho16_classification₃ (hEx : BJPlaneExample) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M :=
  ho16_classification₂ bjThm10 hEx M hnt

/-- **The plane form of the classification**, given only the plane example. -/
theorem ho16_classification_plane₃ (hEx : BJPlaneExample) :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) :=
  ho16_classification_plane₂ bjThm10 hEx

end HPC.BJ59
