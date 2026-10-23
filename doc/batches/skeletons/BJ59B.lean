import HPC.BJ59.BJ59A

/-!
# Batch 199 skeleton: Part G, II — the circle-likeness step (Domokos–Prajs 2022, Theorem 6.1);
# Bing–Jones Theorems 7 and 9

Save as `HPC/BJ59/BJ59B.lean` (splitting under `HPC/BJ59/` is expected); add
`import HPC.BJ59.BJ59B` at the end of `HPC.lean`. Adjust the imports as needed. Every `sorry` is a
work item. Unproved items are commented out with an `OPEN` note, as before. Library lemmas beyond
those stated here are left to you.

Sources: A. Domokos and J. R. Prajs, *The Planck boundary within the hyperspace of the circle of
pseudo-arcs*, arXiv:2203.15906v1 (2022), §6 (`doc/sources/domokos-prajs2022.pdf`); R. H. Bing and
F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959), §§4–5
(`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`). Route: commission 199.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §2. Atomic maps -/

section Atomic

variable {X Y : Type*} [MetricSpace X]

/-- **Atomic** (Domokos–Prajs p. 13): every fibre is terminal, i.e. a continuum that meets a fibre
lies in it or contains it. Domokos–Prajs also ask the fibres to be continua; that is a separate
hypothesis wherever it is used. -/
def IsAtomicMap (f : X → Y) : Prop :=
  ∀ (y : Y) (L : Set X), Fold.Q78.IsContinuum L → (L ∩ f ⁻¹' {y}).Nonempty →
    L ⊆ f ⁻¹' {y} ∨ f ⁻¹' {y} ⊆ L

/-- **An open atomic map onto the circle with pseudo-arc fibres** (the right-hand side of
Domokos–Prajs Theorem 6.1): `IsCircPAMap` with atomicity in place of circle-likeness. -/
structure IsAtomicCircPAMap (f : X → Circle) : Prop where
  cont : Continuous f
  isOpenMap : IsOpenMap f
  surj : Function.Surjective f
  fib : ∀ z, IsPseudoArc (f ⁻¹' {z})
  atomic : IsAtomicMap f

/-- **The saturation lemma**: a continuum lies in a fibre of an atomic map, or it is the full
preimage of its image. -/
theorem subset_fibre_or_saturated {f : X → Y} (hf : IsAtomicMap f) {L : Set X}
    (hL : Fold.Q78.IsContinuum L) : (∃ y, L ⊆ f ⁻¹' {y}) ∨ f ⁻¹' (f '' L) = L := by
  sorry

/-- Test: the identity is atomic. -/
theorem isAtomicMap_id : IsAtomicMap (id : X → X) := by
  sorry

/-- Test: a product projection is not atomic. -/
theorem not_isAtomicMap_snd :
    ¬ IsAtomicMap (Prod.snd : unitInterval × unitInterval → unitInterval) := by
  sorry

end Atomic

/-! ## §3. Atomic arcs are snake-like -/

section Arc

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Terminal points.** A point of an end fibre of `f ⁻¹' [a, b]` satisfies Bing's condition B
there. -/
theorem condB_preimage_Icc {f : X → unitInterval} (hc : Continuous f)
    (hHI : ∀ t, IsHereditarilyIndecomposable (f ⁻¹' {t})) (ha : IsAtomicMap f)
    {a b : unitInterval} (hab : a ≤ b) {μ : X} (hμ : f μ = a ∨ f μ = b) :
    CondB (f ⁻¹' Icc a b) μ := by
  sorry

/-- **Hereditary unicoherence.** -/
theorem isHereditarilyUnicoherent_of_atomic {f : X → unitInterval} (hc : Continuous f)
    (hfib : ∀ t, IsSnakeLike (f ⁻¹' {t})) (ha : IsAtomicMap f) :
    IsHereditarilyUnicoherent (univ : Set X) := by
  sorry

/-- **An atomic arc of snake-like hereditarily indecomposable continua is snake-like**, by Bing's
proof of 1951 Theorem 11 (`exists_minimal_notCoverable`, `fugate_lemma1`,
`epsCoverable_of_halves`). Openness is not needed. -/
theorem isSnakeLike_of_atomic' {f : X → unitInterval} (hc : Continuous f)
    (hfib : ∀ t, IsSnakeLike (f ⁻¹' {t}) ∧ IsHereditarilyIndecomposable (f ⁻¹' {t}))
    (ha : IsAtomicMap f) : IsSnakeLike (univ : Set X) := by
  sorry

/-- The case of pseudo-arc fibres (the step Domokos–Prajs take from Hagopian–Marsh–Prajs,
Proposition 6). -/
theorem isSnakeLike_of_atomic {f : X → unitInterval} (hc : Continuous f)
    (hfib : ∀ t, IsPseudoArc (f ⁻¹' {t})) (ha : IsAtomicMap f) :
    IsSnakeLike (univ : Set X) := by
  sorry

end Arc

/-- Non-vacuity of `isSnakeLike_of_atomic'` and `isHereditarilyUnicoherent_of_atomic`: the identity
of `[0, 1]`. -/
theorem nonvac_isSnakeLike_of_atomic' :
    Continuous (id : unitInterval → unitInterval) ∧
      (∀ t : unitInterval, IsSnakeLike ((id : unitInterval → unitInterval) ⁻¹' {t}) ∧
        IsHereditarilyIndecomposable ((id : unitInterval → unitInterval) ⁻¹' {t})) ∧
      IsAtomicMap (id : unitInterval → unitInterval) := by
  sorry

/-! ## §4. Atomic circle maps: halves, uniqueness, homogeneity, circle-likeness -/

/-- The half map of an atomic map is atomic. -/
theorem isAtomicMap_halfMap {X : Type*} [MetricSpace X] {f : X → Circle} (hf : IsAtomicMap f)
    {s : ℝ} (hs : s = 1 ∨ s = -1) : IsAtomicMap (halfMap f hs) := by
  sorry

section CircleMaps

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem isContArcPA_halfMap_of_atomic {f : X → Circle} (hf : IsAtomicCircPAMap f) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : IsContArcPA (halfMap f hs) := by
  sorry

/-- **The halves are snake-like**, without circle-likeness (compare `isSnakeLike_halfSet`). -/
theorem isSnakeLike_halfSet_of_atomic {f : X → Circle} (hf : IsAtomicCircPAMap f) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : IsSnakeLike (univ : Set (halfSet f s)) := by
  sorry

/-- **Domokos–Prajs (optional)**, p. 14: "one can easily show that X is atriodic". -/
theorem isAtriodic_of_atomic {f : X → Circle} (hf : IsAtomicCircPAMap f) :
    IsAtriodic (univ : Set X) := by
  sorry

end CircleMaps

/-- **Domokos–Prajs, Theorem 6.1, "if"** (p. 14), given Bing–Jones Theorem 10: a compact space with
an open atomic map onto the circle with pseudo-arc fibres is homeomorphic to every circle of
pseudo-arcs. -/
theorem dp22_theorem61 (h10 : BJThm10) {X Y : Type} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] {f : X → Circle} (hf : IsAtomicCircPAMap f) (hY : IsCircleOfPA Y) :
    Nonempty (X ≃ₜ Y) := by
  sorry

/-- Two compact spaces with open atomic maps onto the circle with pseudo-arc fibres are
homeomorphic (given Theorem 10). -/
theorem homeomorph_of_atomic (h10 : BJThm10) {X Y : Type} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y] {f : X → Circle} {g : Y → Circle}
    (hf : IsAtomicCircPAMap f) (hg : IsAtomicCircPAMap g) : Nonempty (X ≃ₜ Y) := by
  sorry

/-- **Homogeneity** (given Theorem 10), by rotating the map, as in
`isHomogeneous_of_isCircPAMap`. -/
theorem isHomogeneous_of_atomic (h10 : BJThm10) {X : Type} [MetricSpace X] [CompactSpace X]
    {f : X → Circle} (hf : IsAtomicCircPAMap f) : IsHomogeneous X := by
  sorry

/-- The circle is circle-like. -/
theorem isCircleLike_circle : IsCircleLike (univ : Set Circle) := by
  sorry

/-- Circle-likeness passes along homeomorphisms (pull back the links; uniform continuity). -/
theorem isCircleLike_univ_of_homeomorph {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] (e : X ≃ₜ Y) (h : IsCircleLike (univ : Set Y)) :
    IsCircleLike (univ : Set X) := by
  sorry

/-- A compact space with an open atomic map onto the circle with pseudo-arc fibres is a circle of
pseudo-arcs in Bing–Jones's sense, if there is one (given Theorem 10). -/
theorem isCircleOfPA_of_atomic (h10 : BJThm10) {X Y : Type} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] {f : X → Circle} (hf : IsAtomicCircPAMap f) (hY : IsCircleOfPA Y) :
    IsCircleOfPA X := by
  sorry

/-! ## §5. The decomposable case and the classification -/

/-- **The decomposable case without circle-likeness**: a decomposable homogeneous plane continuum
is a simple closed curve or has an open atomic map onto the circle with pseudo-arc fibres. -/
theorem circle_or_atomic_of_decomposable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]
    (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (M ≃ₜ Circle) ∨ ∃ f : M → Circle, IsAtomicCircPAMap f := by
  sorry

/-- **`HOCircleLike`**, from Bing–Jones Theorem 10 and a plane circle of pseudo-arcs. -/
theorem hoCircleLike (h10 : BJThm10) (hEx : BJPlaneExample) : HOCircleLike := by
  sorry

/-- **The classification, with Domokos–Prajs's third class**; Theorem 10 is the only named input. -/
theorem ho16_classification_atomic (h10 : BJThm10) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨
      ∃ f : M → Circle, IsAtomicCircPAMap f := by
  sorry

/-- **The classification with Bing–Jones's third class**, from Theorem 10 and §7. -/
theorem ho16_classification₂ (h10 : BJThm10) (hEx : BJPlaneExample) (M : Set Pt)
    [CompactSpace M] [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M := by
  sorry

/-- **The classification of homogeneous plane continua**, from Theorem 10 and §7. -/
theorem ho16_classification_plane₂ (h10 : BJThm10) (hEx : BJPlaneExample) :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) := by
  sorry

/-- Non-vacuity of §4: under the two named inputs, the plane circle of pseudo-arcs carries an open
atomic map onto the circle with pseudo-arc fibres. -/
theorem nonvac_atomic (h10 : BJThm10) (hEx : BJPlaneExample) :
    ∃ C : Set Pt, ∃ f : C → Circle, IsAtomicCircPAMap f := by
  sorry

/-! ## §6. Chains in Bing–Jones's sense; Theorems 7 and 9 -/

section Chains

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- **A chain in Bing–Jones's sense** (p. 172): nonadjacent links are at positive distance. -/
def IsBJChain {n : ℕ} (D : Chain X n) : Prop :=
  ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs →
    ∃ δ > 0, ∀ x ∈ D.link i, ∀ y ∈ D.link j, δ ≤ dist x y

/-- **Shrinking to a chain in Bing–Jones's sense** (Barrett's argument, as in
`exists_taut_epsChain`), keeping given compact sets inside given links. -/
theorem exists_bjChain_shrink {K : Set X} (hK : Fold.Q78.IsContinuum K) {n : ℕ} (D : Chain X n)
    (hKD : K ⊆ D.union) (hDK : ∀ i, (D.link i ∩ K).Nonempty) (C : Fin n → Set X)
    (hC : ∀ i, IsCompact (C i) ∧ C i ⊆ D.link i) :
    ∃ D' : Chain X n, IsBJChain D' ∧ K ⊆ D'.union ∧ (∀ i, (D'.link i ∩ K).Nonempty) ∧
      ∀ i, closure (D'.link i) ⊆ D.link i ∧ C i ⊆ D'.link i := by
  sorry

/-- **Bing–Jones, Theorem 7** (pp. 176–177), first sentence. The hypothesis on `D` is the library's
(weaker) notion of chain; the conclusion is a chain in Bing–Jones's sense. -/
theorem bj_theorem7 {P : Set X} (hP : IsPseudoArc P) {n m : ℕ} (D : Chain X n)
    (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty) (H : Fin m → Fin n)
    (hH : IsChainMap H) (hHs : Function.Surjective H) :
    ∃ E : Chain X m, IsBJChain E ∧ P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
      ∀ i, E.link i ⊆ D.link (H i) := by
  sorry

/-- **Bing–Jones, Theorem 7, second sentence**, for chains of at least three links, reading
"closed sets in P·d₁" as subsets of `P·d₁` closed in the space (commission 199 §6). -/
theorem bj_theorem7_ends {P : Set X} (hP : IsPseudoArc P) {n m : ℕ} (hn : 3 ≤ n) (D : Chain X n)
    (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty) (H : Fin m → Fin n)
    (hH : IsChainMap H) (hHs : Function.Surjective H) {r s : Fin m} (hr : (H r).val = 0)
    (hs : (H s).val = n - 1) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAP : A ⊆ P ∩ D.link (H r)) (hBP : B ⊆ P ∩ D.link (H s)) :
    ∃ E : Chain X m, IsBJChain E ∧ P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
      (∀ i, E.link i ⊆ D.link (H i)) ∧ A ⊆ E.link r ∧ B ⊆ E.link s := by
  sorry

/-- **Bing–Jones, Theorem 9** (p. 179). -/
theorem bj_theorem9 {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {n m : ℕ}
    (D : Chain X n) (E : Chain Y m) (hD : IsBJChain D) (hE : IsBJChain E)
    (hDP : P ⊆ D.union) (hDp : ∀ i, (D.link i ∩ P).Nonempty)
    (hEQ : Q ⊆ E.union) (hEq : ∀ j, (E.link j ∩ Q).Nonempty)
    (H : Fin n → Fin m) (hH : IsChainMap H)
    (hHo : ∀ j, ∃ i, H i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i')) :
    ∃ h : P ≃ₜ Q, ∀ (i : Fin n) (p : P), (p : X) ∈ D.link i → (h p : Y) ∈ E.link (H i) := by
  sorry

end Chains

/-- **The second sentence of Theorem 7 as printed fails for a chain of one link**: a plane
pseudo-arc `P`, `D` one link, `X` three links mapped onto it, `A = B = {p}`, `r = 1`, `s = 3`
(Bing–Jones's indices). -/
theorem bj_theorem7_ends_printed_false : ¬ ∀ (P : Set Pt), IsPseudoArc P → ∀ (n m : ℕ)
    (D : Chain Pt n), P ⊆ D.union → (∀ j, (D.link j ∩ P).Nonempty) →
    ∀ H : Fin m → Fin n, IsChainMap H → Function.Surjective H →
    ∀ r s : Fin m, (H r).val = 0 → (H s).val = n - 1 → ∀ A B : Set Pt, IsClosed A → IsClosed B →
      A ⊆ P ∩ D.link (H r) → B ⊆ P ∩ D.link (H s) →
      ∃ E : Chain Pt m, P ⊆ E.union ∧ (∀ i, (E.link i ∩ P).Nonempty) ∧
        (∀ i, E.link i ⊆ D.link (H i)) ∧ A ⊆ E.link r ∧ B ⊆ E.link s := by
  sorry

/-- Non-vacuity of §6: a plane pseudo-arc with a chain of at least three links properly covering
it, in Bing–Jones's sense. -/
theorem nonvac_bj_chains : ∃ P : Set Pt, IsPseudoArc P ∧ ∃ n, 3 ≤ n ∧ ∃ D : Chain Pt n,
    IsBJChain D ∧ P ⊆ D.union ∧ ∀ j, (D.link j ∩ P).Nonempty := by
  sorry

end HPC.BJ59
