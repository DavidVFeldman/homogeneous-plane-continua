import HPC.BJ59.BJ59C

/-!
# Batch 201 skeleton: Part G, IV — Bing–Jones Theorem 10

Save as `HPC/BJ59/BJ59D.lean` (splitting under `HPC/BJ59/` is expected); add
`import HPC.BJ59.BJ59D` at the end of `HPC.lean`. Adjust the imports as needed. Every `sorry` is a
work item. Unproved items are commented out with an `OPEN` note, as before. Library lemmas beyond
those stated here are left to you. Section numbers follow commission 201.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
§6, pp. 181–189 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
Route: commission 201.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §2. The conditions carried through the induction -/

section Conditions

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Every link has a point outside the closures of the other links. -/
def HasPrivatePoints {n : ℕ} (D : Chain X n) : Prop :=
  ∀ j, ∃ p ∈ D.link j, ∀ j', j' ≠ j → p ∉ closure (D.link j')

/-- **Condition A of p. 188, in the form carried through the induction.** `H` is a chain map of
`D` onto `E`; a link meeting a fibre of `f` goes to a link meeting the fibre of `g` over the same
point; and a run of links of `D` that properly covers a fibre of `f` goes to links whose union
covers the fibre of `g` over the same point. -/
def IsFibreChainMap (f : X → unitInterval) (g : Y → unitInterval) {n m : ℕ} (D : Chain X n)
    (E : Chain Y m) (H : Fin n → Fin m) : Prop :=
  IsChainMap H ∧ Function.Surjective H ∧
    (∀ t j, (D.link j ∩ f ⁻¹' {t}).Nonempty → (E.link (H j) ∩ g ⁻¹' {t}).Nonempty) ∧
    ∀ t (u v : ℕ), (∀ j : Fin n, u ≤ j.val → j.val ≤ v → (D.link j ∩ f ⁻¹' {t}).Nonempty) →
      f ⁻¹' {t} ⊆ ⋃ (j : Fin n) (_ : u ≤ j.val ∧ j.val ≤ v), D.link j →
      g ⁻¹' {t} ⊆ ⋃ (j : Fin n) (_ : u ≤ j.val ∧ j.val ≤ v), E.link (H j)

/-- **Condition C of p. 188**: agreement with the given homeomorphisms of the end fibres. -/
def EndCompat (f : X → unitInterval) (g : Y → unitInterval) (h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0})
    (h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}) {n m : ℕ} (D : Chain X n) (E : Chain Y m)
    (H : Fin n → Fin m) : Prop :=
  (∀ j (x : f ⁻¹' {0}), (x : X) ∈ D.link j → (h₀ x : Y) ∈ E.link (H j)) ∧
    ∀ j (x : f ⁻¹' {1}), (x : X) ∈ D.link j → (h₁ x : Y) ∈ E.link (H j)

/-- One link, or every run of links covering a fibre has at least three links. -/
def IsFibreFine (g : Y → unitInterval) {m : ℕ} (E : Chain Y m) : Prop :=
  m = 1 ∨ ∀ t (u v : ℕ), g ⁻¹' {t} ⊆ ⋃ (k : Fin m) (_ : u ≤ k.val ∧ k.val ≤ v), E.link k →
    u + 2 ≤ v

end Conditions

/-! ## §3. Tools -/

section Tools

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- In a run covering a preconnected set from which neither end link can be dropped, every link
contains a point of the set that lies in no other link of the run. -/
theorem exists_point_only_of_minimal {n : ℕ} (D : Chain X n) {C : Set X} (hC : IsPreconnected C)
    {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) (hw₂ : w₂ < n)
    (hcov : C ⊆ ⋃ (j : Fin n) (_ : w₁ ≤ j.val ∧ j.val ≤ w₂), D.link j)
    (hl : ¬ C ⊆ ⋃ (j : Fin n) (_ : w₁ + 1 ≤ j.val ∧ j.val ≤ w₂), D.link j)
    (hr : ¬ C ⊆ ⋃ (j : Fin n) (_ : w₁ ≤ j.val ∧ j.val + 1 ≤ w₂), D.link j)
    (j : Fin n) (hj₁ : w₁ ≤ j.val) (hj₂ : j.val ≤ w₂) :
    ∃ z ∈ C ∩ D.link j, ∀ j' : Fin n, w₁ ≤ j'.val → j'.val ≤ w₂ → j' ≠ j → z ∉ D.link j' := by
  sorry

/-- **Theorem 6 in the form Step 2(c) uses** (p. 185): two chain maps that carry a run onto
families of links each properly covering the same set agree up to adjacency somewhere on the
run. -/
theorem adjacent_of_properCover {N n : ℕ} (D : Chain X n) {C : Set X} {R R' : Fin N → Fin n}
    (hR : IsChainMap R) (hR' : IsChainMap R') {t u : ℕ} (htu : t ≤ u) (hu : u < N)
    (hRC : ∀ a : Fin N, t ≤ a.val → a.val ≤ u → (D.link (R a) ∩ C).Nonempty)
    (hR'C : ∀ a : Fin N, t ≤ a.val → a.val ≤ u → (D.link (R' a) ∩ C).Nonempty)
    (hCR : C ⊆ ⋃ (a : Fin N) (_ : t ≤ a.val ∧ a.val ≤ u), D.link (R a))
    (hCR' : C ⊆ ⋃ (a : Fin N) (_ : t ≤ a.val ∧ a.val ≤ u), D.link (R' a)) :
    ∃ a : Fin N, t ≤ a.val ∧ a.val ≤ u ∧ ((R a : ℤ) - R' a).natAbs ≤ 1 := by
  sorry

/-- **The pattern of a map of a fibre** (Step 2(b), p. 184): a fine chain covering `Q` maps into
a run of `D` covering `φ(Q)`, following `φ` on closures, with each link of the run the image of
three consecutive links meeting `Q`. -/
theorem exists_pattern {Q : Set Y} (hQ : IsCompact Q) (hQc : IsPreconnected Q)
    (hQn : Q.Nontrivial) (φ : Q → X) (hφ : Continuous φ) {n : ℕ} (D : Chain X n)
    {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) (hw₂ : w₂ < n)
    (hcov : ∀ z, φ z ∈ ⋃ (j : Fin n) (_ : w₁ ≤ j.val ∧ j.val ≤ w₂), D.link j)
    (hpriv : ∀ j : Fin n, w₁ ≤ j.val → j.val ≤ w₂ → ∃ z, φ z ∈ D.link j ∧
      ∀ j' : Fin n, w₁ ≤ j'.val → j'.val ≤ w₂ → j' ≠ j → φ z ∉ D.link j') :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → Q ⊆ F.union →
      ∃ R : Fin N → Fin n, IsChainMap R ∧
        (∀ a : Fin N, (F.link a ∩ Q).Nonempty → w₁ ≤ (R a).val ∧ (R a).val ≤ w₂ ∧
          ∀ z : Q, (z : Y) ∈ closure (F.link a) → φ z ∈ D.link (R a)) ∧
        ∀ j : Fin n, w₁ ≤ j.val → j.val ≤ w₂ → ∃ a : ℕ, ∃ ha : a + 2 < N,
          ∀ (c : ℕ) (hc : c ≤ 2), (F.link ⟨a + c, by omega⟩ ∩ Q).Nonempty ∧
            R ⟨a + c, by omega⟩ = j := by
  sorry

/-- Chains finer than a third of the spread of the fibres are fibre-fine. -/
theorem isFibreFine_of_isEpsChain {g : Y → unitInterval} {κ : ℝ}
    (hκ : ∀ t, ∃ p ∈ g ⁻¹' {t}, ∃ q ∈ g ⁻¹' {t}, κ ≤ dist p q) {m : ℕ} (E : Chain Y m)
    (hE : IsEpsChain E (κ / 3)) : IsFibreFine g E := by
  sorry

end Tools

section SubArc

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-- **The corollary to Theorem 8 on a sub-arc** `Q(a, b)` (pp. 178, 187), for a chain of one link
or of at least three. -/
theorem bj_theorem8_cor_sub {g : Y → unitInterval} (hg : IsContArcPA g)
    (hS : IsSnakeLike (univ : Set Y)) {a b : unitInterval} (hab : a < b) {n ℓ : ℕ}
    (hn : n = 1 ∨ 3 ≤ n) (E : Chain Y n) (hE : g ⁻¹' Icc a b ⊆ E.union)
    (hEf : ∀ t ∈ Icc a b, ∀ j, (E.link j ∩ g ⁻¹' {t}).Nonempty)
    (H₁ : Fin ℓ → Fin n) (hH₁ : IsChainMap H₁) (hH₁s : Function.Surjective H₁) :
    ∃ ε > 0, ∀ (N : ℕ) (F : Chain Y N), IsEpsChain F ε → g ⁻¹' Icc a b ⊆ F.union →
      ∃ R : Fin N → Fin ℓ, IsChainMap R ∧
        (∀ k, F.link k ∩ g ⁻¹' Icc a b ⊆ E.link (H₁ (R k))) ∧
        ∀ t ∈ Icc a b, ∀ (v w : ℕ) (hw : w < N), v ≤ w →
          g ⁻¹' {t} ⊆ ⋃ (k : Fin N) (_ : v ≤ k.val ∧ k.val ≤ w), F.link k →
          ∀ d : Fin ℓ, ∃ k : ℕ, ∃ hk : k + 2 ≤ w, v ≤ k ∧
            ∀ (c : ℕ) (hc : c ≤ 2), R ⟨k + c, by omega⟩ = d := by
  sorry

/-- **Theorem 5 (repaired) on a window** `[a, b]`, extended to the whole space (Step 2(c),
p. 185). -/
theorem bj_theorem5_window {g : Y → unitInterval} (hg : IsContArcPA g)
    (hS : IsSnakeLike (univ : Set Y)) {a b : unitInterval} (hab : a < b) {N : ℕ}
    (F : Chain Y N) {t u : ℕ} (htu : t ≤ u)
    (hTf : ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ g ⁻¹' {s}).Nonempty)
    (hTc : g ⁻¹' Icc a b ⊆ ⋃ (k : Fin N) (_ : t ≤ k.val ∧ k.val ≤ u), F.link k)
    {U : Set Y} (hU : IsOpen U) (hUne : U.Nonempty) (hUab : U ⊆ g ⁻¹' Ioo a b)
    (hUF : ∃ k : Fin N, t ≤ k.val ∧ k.val ≤ u ∧ closure U ⊆ F.link k)
    (hFU : ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u →
      ¬ F.link k ∩ g ⁻¹' {s} ⊆ closure U) :
    ∃ A B : Set Y, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧
      g ⁻¹' Icc 0 a ⊆ A ∧ g ⁻¹' Icc b 1 ⊆ B ∧ ∀ s ∈ Icc a b,
        (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ (A ∩ g ⁻¹' {s})).Nonempty) ∨
          (∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ (B ∩ g ⁻¹' {s})).Nonempty) := by
  sorry

/-- A transition set for `bj_theorem5_window`: inside a given link of the run, over the open
window, and too small to contain the part of any link of the run in any fibre of the window. -/
theorem exists_window_set {g : Y → unitInterval} (hg : IsContArcPA g) {a b : unitInterval}
    (hab : a < b) {N : ℕ} (F : Chain Y N) {t u : ℕ}
    (hTf : ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u → (F.link k ∩ g ⁻¹' {s}).Nonempty)
    {y : Fin N} (hty : t ≤ y.val) (hyu : y.val ≤ u) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧ U ⊆ g ⁻¹' Ioo a b ∧ closure U ⊆ F.link y ∧
      ∀ s ∈ Icc a b, ∀ k : Fin N, t ≤ k.val → k.val ≤ u →
        ¬ F.link k ∩ g ⁻¹' {s} ⊆ closure U := by
  sorry

end SubArc

/-! ## §4. The step of the induction (Steps 2 and 3, pp. 183–188) -/

/-- **One step of Bing–Jones's induction** (Steps 2, 3, 4, ⋯ of the proof of Theorem 10): from a
chain map `H` of `D` (on `X`) onto `E` (on `Y`) with Conditions A and C, a fine chain `E′` on `Y`
and a chain map `K` of `E′` onto `D` with Conditions A′, B′ and C′. Applied with `X` and `Y`
exchanged it gives Conditions A, B and C. -/
def BJStep : Prop :=
  ∀ (X Y : Type) [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]
    (f : X → unitInterval) (g : Y → unitInterval), IsContArcPA f → IsContArcPA g →
    IsSnakeLike (univ : Set X) → IsSnakeLike (univ : Set Y) →
    ∀ (h₀ : f ⁻¹' {0} ≃ₜ g ⁻¹' {0}) (h₁ : f ⁻¹' {1} ≃ₜ g ⁻¹' {1}) (n m : ℕ) (D : Chain X n)
      (E : Chain Y m) (H : Fin n → Fin m), univ ⊆ D.union → univ ⊆ E.union →
      HasPrivatePoints D → IsFibreFine g E → IsFibreChainMap f g D E H →
      EndCompat f g h₀ h₁ D E H → ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (E' : Chain Y N) (K : Fin N → Fin n), univ ⊆ E'.union ∧ IsBJChain E' ∧
        IsEpsChain E' δ ∧ HasPrivatePoints E' ∧ IsFibreChainMap g f E' D K ∧
        EndCompat g f h₀.symm h₁.symm E' D K ∧ ∀ k, E'.link k ⊆ E.link (H (K k))

/-- **The step lemma** (main item). -/
theorem bj_step : BJStep := by
  sorry

/-! ## §5. Theorem 10 and the classification -/

/-- **Theorem 10 from the step lemma**: alternate the step, starting from one-link chains, and
apply `zigzag_homeomorph` and `zigzag_fibre`. -/
theorem bjThm10_of_step (hs : BJStep) : BJThm10 := by
  sorry

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

/-! ## §7. Non-vacuity -/

/-- The conditions of §2 on a non-degenerate input: `[0, 1]` with the identity, a chain of at
least three links in Bing–Jones's sense with private points, and the identity chain map. -/
theorem nonvac_conditions : ∃ (n : ℕ) (D : Chain unitInterval n), 3 ≤ n ∧ univ ⊆ D.union ∧
    IsBJChain D ∧ HasPrivatePoints D ∧ IsFibreChainMap id id D D id := by
  sorry

end HPC.BJ59
