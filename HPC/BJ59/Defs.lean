import HPC.Plane.Ingram68
import HPC.Jones.Jones49F

/-!
# Batch 198: Bing–Jones 1959, definitions and named inputs

§§2–3 of the batch-198 skeleton (`doc/batches/skeletons/BJ59A.lean`), verbatim: the skeleton file is
split under `HPC/BJ59/`, and these declarations are moved here so that the library files of the
batch can use them. `HPC/BJ59/BJ59A.lean` contains the theorems of §§4–6.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
171–192 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! ## §2. Definitions -/

section Defs

variable {X : Type*} [MetricSpace X]

/-- **An arc of continua** (Bing–Jones p. 173): the fibres of a continuous map of `X` onto
`[0, 1]`, each a continuum. `G(a, b)` is `f ⁻¹' Icc a b`; the end elements are `f ⁻¹' {0}` and
`f ⁻¹' {1}`. -/
def IsArcOfContinua (f : X → unitInterval) : Prop :=
  Continuous f ∧ Function.Surjective f ∧ ∀ t, Fold.Q78.IsContinuum (f ⁻¹' {t})

/-- **A continuous arc of pseudo-arcs** (Bing–Jones p. 173): a continuous open map of `X` onto
`[0, 1]` whose fibres are pseudo-arcs. Bing–Jones's "snake-like" is a separate hypothesis. -/
def IsContArcPA (f : X → unitInterval) : Prop :=
  Continuous f ∧ IsOpenMap f ∧ Function.Surjective f ∧ ∀ t, IsPseudoArc (f ⁻¹' {t})

end Defs

/-- **A circle of pseudo-arcs** (Bing–Jones p. 173): "a circle-like continuum `M` such that there
is a continuous decomposition of `M` into pseudo-arcs such that the decomposition space is a simple
closed curve", i.e. an open continuous map onto the circle with pseudo-arc fibres. Bing–Jones's
"circle-like" also excludes snake-like continua; here that is a consequence (commission §2). -/
def IsCircleOfPA (X : Type*) [MetricSpace X] : Prop :=
  IsCircleLike (univ : Set X) ∧ ∃ f : X → Circle, Continuous f ∧ IsOpenMap f ∧
    Function.Surjective f ∧ ∀ z, IsPseudoArc (f ⁻¹' {z})

/-- **A chain map** (Bing–Jones p. 173), on indices: images of adjacent links are adjacent. -/
def IsChainMap {m n : ℕ} (H : Fin m → Fin n) : Prop :=
  ∀ i j : Fin m, ((i : ℤ) - j).natAbs ≤ 1 → ((H i : ℤ) - H j).natAbs ≤ 1

/-! ## §3. The three named inputs -/

/-- **Bing–Jones, Theorem 10** (pp. 181–182), fibre-preserving form: between two continuous
snake-like arcs of pseudo-arcs, homeomorphisms of the end fibres extend to a homeomorphism that
carries each fibre onto the fibre over the same point. Named `Prop`; to be proved in later
batches. -/
def BJThm10 : Prop :=
  ∀ (X Y : Type) [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]
    (f : X → unitInterval) (g : Y → unitInterval), IsContArcPA f → IsContArcPA g →
    IsSnakeLike (univ : Set X) → IsSnakeLike (univ : Set Y) →
    ∀ (h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0}) (h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}),
      ∃ H : X ≃ₜ Y, (∀ x, g (H x) = f x) ∧ (∀ x (hx : x ∈ f ⁻¹' {0}), H x = (h₀ ⟨x, hx⟩ : Y)) ∧
        ∀ x (hx : x ∈ f ⁻¹' {1}), H x = (h₁ ⟨x, hx⟩ : Y)

/-- **The circle-likeness step** (not in Bing–Jones; commission 198 §1): a decomposable
homogeneous plane continuum is circle-like. Named `Prop`; to be proved in later batches. -/
def HOCircleLike : Prop :=
  ∀ M : Set Pt, CompactSpace M → ConnectedSpace M → IsHomogeneous M → IsDecomposableSpace M →
    IsCircleLike (univ : Set M)

/-- **A plane circle of pseudo-arcs** (Bing–Jones §7, pp. 189–191). Named `Prop`; to be proved
in later batches. -/
def BJPlaneExample : Prop :=
  ∃ C : Set Pt, IsCircleOfPA C

end HPC.BJ59
