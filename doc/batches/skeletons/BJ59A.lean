import HPC.HO16.HO16E
import HPC.Plane.Ingram68
import HPC.Jones.Jones49F

/-!
# Batch 198 skeleton: Part G, I — the circle of pseudo-arcs (Bing–Jones 1959), top down

Save as `HPC/BJ59/BJ59A.lean` (splitting under `HPC/BJ59/` is expected); add
`import HPC.BJ59.BJ59A` at the end of `HPC.lean`. Every `sorry` is a work item. Unproved items are
commented out with an `OPEN` note, as before. Library lemmas beyond those stated here are shape
left to you; so are the imports.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
171–192 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
Route: commission 198.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16 HPC.Span

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

/-! ## §4. From Theorem 10: homogeneity and uniqueness of circles of pseudo-arcs -/

/-- **Each circle of pseudo-arcs is homogeneous** (Bing–Jones pp. 173, 189, "It follows from
Theorem 10"; the step is supplied by commission §4). -/
theorem isHomogeneous_of_isCircleOfPA (h10 : BJThm10) {X : Type} [MetricSpace X]
    (hX : IsCircleOfPA X) : IsHomogeneous X := by
  sorry

/-- **Any two circles of pseudo-arcs are homeomorphic** (Bing–Jones pp. 173, 189). -/
theorem homeomorph_of_isCircleOfPA (h10 : BJThm10) {X Y : Type} [MetricSpace X] [MetricSpace Y]
    (hX : IsCircleOfPA X) (hY : IsCircleOfPA Y) : Nonempty (X ≃ₜ Y) := by
  sorry

/-! ## §5. The decomposable case and the classification -/

/-- The circle is homogeneous. -/
theorem isHomogeneous_circle : IsHomogeneous Circle := by
  sorry

/-- **Jones's elements are pseudo-arcs** (Jones 1955 Theorem 2 with Part F), unconditional: in a
decomposable homogeneous plane continuum, each non-degenerate element of Jones's decomposition is
a pseudo-arc. -/
theorem isPseudoArc_Lset {M : Set Pt} [CompactSpace M] [ConnectedSpace M] (hX : IsHomogeneous M)
    (hd : IsDecomposableSpace M) (x : M) (hnt : (Lset x).Nontrivial) : IsPseudoArc (Lset x) := by
  sorry

/-- **The decomposable case**: a decomposable homogeneous plane continuum is a simple closed curve
or a circle of pseudo-arcs. -/
theorem circle_or_circleOfPA_of_decomposable (hCL : HOCircleLike) {M : Set Pt} [CompactSpace M]
    [ConnectedSpace M] (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (M ≃ₜ Circle) ∨ IsCircleOfPA M := by
  sorry

/-- **The classification, both directions** (H–O p. 180, with Bing–Jones for the third class). -/
theorem ho16_classification (h10 : BJThm10) (hCL : HOCircleLike) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M := by
  sorry

/-- **The classification of homogeneous plane continua**: there are three plane continua, the
circle, the pseudo-arc and a circle of pseudo-arcs, each homogeneous, no two homeomorphic, and
every non-degenerate plane continuum is homogeneous iff it is homeomorphic to one of them. -/
theorem ho16_classification_plane (h10 : BJThm10) (hCL : HOCircleLike) (hEx : BJPlaneExample) :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) := by
  sorry

/-! ## §6. Bing–Jones §§3–4: snake-like arcs of continua; chain maps -/

section Section3

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Bing–Jones, Theorem 2** (p. 174). -/
theorem bj_theorem2 {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hS : IsSnakeLike (univ : Set X)) {a b c d : unitInterval} (h0a : 0 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hd1 : d < 1) :
    ∃ ε > 0, ∀ (n : ℕ) (D : Chain X n), IsEpsChain D ε → univ ⊆ D.union →
      ∀ i j k : Fin n, (D.link i ∩ f ⁻¹' Icc 0 a).Nonempty →
        (D.link j ∩ f ⁻¹' Icc b c).Nonempty → (D.link k ∩ f ⁻¹' Icc d 1).Nonempty →
          (i < j ∧ j < k) ∨ (k < j ∧ j < i) := by
  sorry

/-- **Bing–Jones, Theorem 3** (pp. 174–175): an `ε`-chain from `g₀` to `g₁`. -/
theorem bj_theorem3 {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hS : IsSnakeLike (univ : Set X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (D : Chain X (m + 1)), IsEpsChain D ε ∧ univ ⊆ D.union ∧
      (D.link 0 ∩ f ⁻¹' {0}).Nonempty ∧ (D.link (Fin.last m) ∩ f ⁻¹' {1}).Nonempty := by
  sorry

/-- **Bing–Jones, Theorem 4** (p. 175): a non-empty open set missing the end elements separates
them. -/
theorem bj_theorem4 {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hS : IsSnakeLike (univ : Set X)) {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (hU01 : Disjoint U (f ⁻¹' {0, 1})) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B := by
  sorry

/-- **Bing–Jones, Theorem 5, repaired** (pp. 175–176; stretch). Changed hypotheses (commission
§6): `f` open, and no fibre meets a link only inside `Ū` (`hEU`, which implies Bing–Jones's
"E properly covers each g_x"). -/
theorem bj_theorem5 {f : X → unitInterval} (hf : IsArcOfContinua f) (hfo : IsOpenMap f)
    (hS : IsSnakeLike (univ : Set X)) (hind : ∀ t, Fold.Q78.IsIndecomposable (f ⁻¹' {t}))
    {n : ℕ} (E : Chain X n) (hE : univ ⊆ E.union)
    {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty) (hU01 : Disjoint U (f ⁻¹' {0, 1}))
    (hUE : ∃ i, closure U ⊆ E.link i) (hEU : ∀ t i, ¬ E.link i ∩ f ⁻¹' {t} ⊆ closure U) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B ∧ ∀ t, (∀ i, (E.link i ∩ (A ∩ f ⁻¹' {t})).Nonempty) ∨
        (∀ i, (E.link i ∩ (B ∩ f ⁻¹' {t})).Nonempty) := by
  sorry

/-- **Bing–Jones's Theorem 5 as printed is false** (commission §6): its hypotheses (a chain
properly covering each fibre, `Ū` in a link) do not give its conclusion. -/
theorem bj_theorem5_printed_false : ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X]
    (f : X → unitInterval), IsArcOfContinua f → IsSnakeLike (univ : Set X) →
    (∀ t, Fold.Q78.IsIndecomposable (f ⁻¹' {t})) → ∀ (n : ℕ) (E : Chain X n), univ ⊆ E.union →
    (∀ t i, (E.link i ∩ f ⁻¹' {t}).Nonempty) → ∀ U : Set X, IsOpen U → U.Nonempty →
    Disjoint U (f ⁻¹' {0, 1}) → (∃ i, closure U ⊆ E.link i) →
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B ∧ ∀ t, (∀ i, (E.link i ∩ (A ∩ f ⁻¹' {t})).Nonempty) ∨
        (∀ i, (E.link i ∩ (B ∩ f ⁻¹' {t})).Nonempty) := by
  sorry

end Section3

/-- **Bing–Jones, Theorem 6** (p. 176), on indices: two chain maps of `D` into `E` that each take
a link into `e_{m−1}` (index `m − 2`) agree up to adjacency at some link. -/
theorem bj_theorem6 {n m : ℕ} {H₁ H₂ : Fin n → Fin m} (h₁ : IsChainMap H₁) (h₂ : IsChainMap H₂)
    (h₁e : ∃ i, (H₁ i : ℕ) + 2 = m) (h₂e : ∃ i, (H₂ i : ℕ) + 2 = m) :
    ∃ i, ((H₁ i : ℤ) - H₂ i).natAbs ≤ 1 := by
  sorry

end HPC.BJ59
