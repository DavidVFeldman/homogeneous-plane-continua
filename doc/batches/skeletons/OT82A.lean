import HPC.Jones.Jones75B

/-!
# Batch 191 skeleton: Theorem C I — span; Cook 1967; Oversteegen–Tymchatyn 1982, Theorem 3.6 and
# Corollary 3.5 from the strip theorem

Save as `HPC/Span/OT82A.lean` (splitting under `HPC/Span/` is expected); add
`import HPC.Span.OT82A` at the end of `HPC.lean`. Every `sorry` is a work item. Items stated as
`True` are *shape left to you*; record each shape in the report. Unproved items are commented out
with an `OPEN` note, as before.

Sources: L. G. Oversteegen and E. D. Tymchatyn, *Plane strips and the span of continua, (I)*,
Houston J. Math. 8 (1982), 129–142 (`doc/sources/oversteegen-tymchatyn1982.pdf`); H. Cook,
*Continua which admit only the identity mapping onto non-degenerate subcontinua*, Fund. Math. 60
(1967), 241–249 (`doc/sources/cook1967.pdf`). Route: commission 191.
-/

namespace HPC.Span

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Hagopian

/-! ## §2. Span (commission §2) -/

section Defs

variable {X : Type*} [MetricSpace X]

/-- The off-diagonal condition. -/
def OffDiag (Z : Set (X × X)) : Prop := ∀ p ∈ Z, p.1 ≠ p.2

/-- **Positive surjective span** of `A` (O–T p. 129, `σ*(A) > 0`), topological form: a continuum
`Z ⊆ A × A` missing the diagonal, with both projections onto `A`. -/
def SurjSpanPos (A : Set X) : Prop :=
  ∃ Z ⊆ A ×ˢ A, Fold.Q78.IsContinuum Z ∧ OffDiag Z ∧ Prod.fst '' Z = A ∧ Prod.snd '' Z = A

/-- **Positive surjective semi-span** of `A` (`σ₀*(A) > 0`): the first projection onto `A`. -/
def SurjSemiSpanPos (A : Set X) : Prop :=
  ∃ Z ⊆ A ×ˢ A, Fold.Q78.IsContinuum Z ∧ OffDiag Z ∧ Prod.fst '' Z = A

/-- **Span zero** (`σ(X) = 0`). -/
def SpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ A : Set X, Fold.Q78.IsContinuum A → ¬ SurjSpanPos A

/-- **Semi-span zero** (`σ₀(X) = 0`). -/
def SemiSpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ A : Set X, Fold.Q78.IsContinuum A → ¬ SurjSemiSpanPos A

/-- **Span zero in the sense of Hoehn–Oversteegen** (2016, p. 184): every subcontinuum
`Z ⊆ X × X` with `π₁(Z) ⊆ π₂(Z)` meets the diagonal. -/
def HOSpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ Z : Set (X × X), Fold.Q78.IsContinuum Z → Prod.fst '' Z ⊆ Prod.snd '' Z → ∃ p ∈ Z, p.1 = p.2

/-- O–T's definition of `σ₀(X) > 0`, read literally (p. 129): a nonempty connected `A ⊆ X`, a
connected `C ⊆ A × A` and `α > 0` with `d(x, y) ≥ α` on `C` and `π₁(C) = A`. -/
def OTSemiSpanPos (X : Type*) [MetricSpace X] : Prop :=
  ∃ A : Set X, A.Nonempty ∧ IsConnected A ∧ ∃ C ⊆ A ×ˢ A, IsConnected C ∧ ∃ α > 0,
    (∀ p ∈ C, α ≤ dist p.1 p.2) ∧ Prod.fst '' C = A

/-- O–T's definition of `σ(X) > 0`, read literally. -/
def OTSpanPos (X : Type*) [MetricSpace X] : Prop :=
  ∃ A : Set X, A.Nonempty ∧ IsConnected A ∧ ∃ C ⊆ A ×ˢ A, IsConnected C ∧ ∃ α > 0,
    (∀ p ∈ C, α ≤ dist p.1 p.2) ∧ Prod.fst '' C = A ∧ Prod.snd '' C = A

end Defs

section SpanLemmas

variable {X : Type*} [MetricSpace X]

/-- **§2.1**: the literal definition agrees with the continuum form (closures). -/
theorem otSemiSpanPos_iff [CompactSpace X] :
    OTSemiSpanPos X ↔ ∃ A : Set X, Fold.Q78.IsContinuum A ∧ SurjSemiSpanPos A := by
  sorry

/-- **§2.1**, for span. -/
theorem otSpanPos_iff [CompactSpace X] :
    OTSpanPos X ↔ ∃ A : Set X, Fold.Q78.IsContinuum A ∧ SurjSpanPos A := by
  sorry

/-- **§2.2**. -/
theorem SurjSpanPos.surjSemiSpanPos {A : Set X} (h : SurjSpanPos A) : SurjSemiSpanPos A := by
  sorry

/-- **§2.2**: positivity is carried by maps injective on `A`. -/
theorem SurjSpanPos.image {Y : Type*} [MetricSpace Y] {A : Set X} (h : SurjSpanPos A)
    {f : X → Y} (hf : Continuous f) (hinj : InjOn f A) : SurjSpanPos (f '' A) := by
  sorry

/-- **§2.2**. -/
theorem SurjSemiSpanPos.image {Y : Type*} [MetricSpace Y] {A : Set X} (h : SurjSemiSpanPos A)
    {f : X → Y} (hf : Continuous f) (hinj : InjOn f A) : SurjSemiSpanPos (f '' A) := by
  sorry

/-- **§2.3**: O–T's semi-span zero is H–O's span zero. -/
theorem semiSpanZero_iff_hoSpanZero [CompactSpace X] : SemiSpanZero X ↔ HOSpanZero X := by
  sorry

end SpanLemmas

/-- **§2.4**: H–O's definition with maps of continua (p. 184, first sentence). -/
theorem hoSpanZero_iff_maps {X : Type} [MetricSpace X] [CompactSpace X] :
    HOSpanZero X ↔ ∀ (C : Type) [MetricSpace C] [CompactSpace C] [ConnectedSpace C] (f g : C → X),
      Continuous f → Continuous g → range f ⊆ range g → ∃ c, f c = g c := by
  sorry

/-! ## §3. Cook 1967, Theorem 4 -/

/-- **Cook 1967, Theorem 4** (p. 243): "If `f` is a mapping of the compact metric continuum `X`
onto the hereditarily indecomposable continuum `Y`, then `f` is confluent." Here `Y` is the set
`S = range f` in a metric space `E`. -/
theorem cook67_theorem4 {X E : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [MetricSpace E] {f : X → E} (hf : Continuous f) {S : Set E} (hS : range f = S)
    (hHI : IsHereditarilyIndecomposable S) {Q : Set E} (hQ : Fold.Q78.IsContinuum Q)
    (hQS : Q ⊆ S) {x : X} (hx : f x ∈ Q) : f '' connectedComponentIn (f ⁻¹' Q) x = Q := by
  sorry

/-! ## §4. Brouwer reduction; Davis's Theorem 1.1 for hereditarily indecomposable continua -/

section Davis

variable {X : Type*} [MetricSpace X]

/-- **§4.1, helper**: the intersection of a nonempty chain of continua is a continuum, and
continuous images commute with it. -/
theorem isContinuum_sInter_chain {c : Set (Set X)} (hne : c.Nonempty) (hch : IsChain (· ⊆ ·) c)
    (hc : ∀ W ∈ c, Fold.Q78.IsContinuum W) :
    Fold.Q78.IsContinuum (⋂₀ c) ∧ ∀ {E : Type*} [MetricSpace E] {φ : X → E}, Continuous φ →
      φ '' (⋂₀ c) = ⋂ W ∈ c, φ '' W := by
  sorry

/-- **§4.1, Brouwer reduction.** A property of subcontinua of `Z` that passes to intersections of
nonempty chains has a minimal instance. -/
theorem brouwer_reduction {Z : Set X} (hZ : Fold.Q78.IsContinuum Z) (P : Set X → Prop) (hPZ : P Z)
    (hch : ∀ c : Set (Set X), c.Nonempty → IsChain (· ⊆ ·) c →
      (∀ W ∈ c, Fold.Q78.IsContinuum W ∧ W ⊆ Z ∧ P W) → P (⋂₀ c)) :
    ∃ Z₀ ⊆ Z, Fold.Q78.IsContinuum Z₀ ∧ P Z₀ ∧
      ∀ W ⊆ Z₀, Fold.Q78.IsContinuum W → P W → W = Z₀ := by
  sorry

/-- **§4.2, Davis 1984 (O–T Theorem 1.1) for hereditarily indecomposable `A`**: positive
semi-span gives a subcontinuum of positive span. -/
theorem exists_surjSpanPos_of_surjSemiSpanPos {A : Set X} (hHI : IsHereditarilyIndecomposable A)
    (h : SurjSemiSpanPos A) : ∃ B ⊆ A, Fold.Q78.IsContinuum B ∧ SurjSpanPos B := by
  sorry

/-- **§4.2, corollary.** -/
theorem semiSpanZero_of_spanZero (hHI : IsHereditarilyIndecomposable (univ : Set X))
    (h : SpanZero X) : SemiSpanZero X := by
  sorry

end Davis

/-! ## §5. Theorem 3.6 (indecomposable case) from Corollary 3.5 -/

/-- **O–T Corollary 3.5** (p. 139), as a named claim: "If `X` is an indecomposable, homogeneous
plane continuum, then every proper subcontinuum of `X` has surjective semi-span equal to zero." -/
def OTCor35 : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M → ¬ IsDecomposableSpace M →
    ∀ A : Set M, Fold.Q78.IsContinuum A → A ≠ univ → ¬ SurjSemiSpanPos A

/-- **Theorem C** (Hoehn–Oversteegen 2016, p. 180): "Every homogeneous indecomposable plane
continuum has span zero." -/
def TheoremC : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M → ¬ IsDecomposableSpace M →
    HOSpanZero M

/-- **O–T Theorem 3.6, second sentence** (p. 140), from Corollary 3.5. -/
theorem ot82_theorem36_of_cor35 (h35 : OTCor35) (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) : SemiSpanZero M := by
  sorry

/-- **§5.9**: Theorem C from Corollary 3.5. -/
theorem theoremC_of_cor35 (h35 : OTCor35) : TheoremC := by
  sorry

/-! ## §6. Corollary 3.5 from Theorem 3.2 (strip form) -/

/-- **§6.1 (E1)**: a plane homeomorphism making a point of a compact set its unique leftmost point,
on the line `x = 0`. -/
theorem exists_homeomorph_unique_leftmost {K : Set Pt} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ (Φ : Pt ≃ₜ Pt) (x₀ : Pt), x₀ ∈ K ∧ (Φ x₀).1 = 0 ∧ ∀ z ∈ K, z ≠ x₀ → 0 < (Φ z).1 := by
  sorry

/-- **§6.1 (E2), the finger move**: in a connected open set, any point can be carried to any other
by a plane homeomorphism fixing every point outside the set. -/
theorem exists_homeomorph_push {U : Set Pt} (hU : IsOpen U) (hUc : IsConnected U) {p q : Pt}
    (hp : p ∈ U) (hq : q ∈ U) : ∃ T : Pt ≃ₜ Pt, T p = q ∧ ∀ z ∉ U, T z = z := by
  sorry

/-- **§6.1 (E3)**: a non-separating continuum that meets the line `x = 0` only at one point and
lies in `x ≥ 0` leaves the open half-plane `x > 0` connected. -/
theorem isConnected_rightHalf_diff {A : Set Pt} (hA : Fold.Q78.IsContinuum A)
    (hns : ¬ SeparatesPlane A) (hA0 : ∀ z ∈ A, 0 ≤ z.1) {x₀ : Pt}
    (hx₀ : ∀ z ∈ A, z.1 = 0 → z = x₀) : IsConnected ({z : Pt | 0 < z.1} \ A) := by
  sorry

/-- **§6.2 (cut wire)**: a continuum with points left of `x = a` and right of `x = b` contains a
subcontinuum of the closed strip meeting both lines. -/
theorem exists_crossing_subcontinuum {P : Set Pt} (hP : Fold.Q78.IsContinuum P) {a b : ℝ}
    (hab : a < b) (hl : ∃ z ∈ P, z.1 < a) (hr : ∃ z ∈ P, b < z.1) :
    ∃ K ⊆ P ∩ (Icc a b ×ˢ univ), Fold.Q78.IsContinuum K ∧ (∃ z ∈ K, z.1 = a) ∧
      ∃ z ∈ K, z.1 = b := by
  sorry

/-- **§6.2**: an indecomposable plane continuum with points on both sides of a closed strip contains
uncountably many pairwise disjoint continua crossing the strip (one in each composant). -/
theorem exists_uncountable_crossing (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hi : ¬ IsDecomposableSpace M) {a b : ℝ} (hab : a < b) (hl : ∃ z ∈ M, z.1 < a)
    (hr : ∃ z ∈ M, b < z.1) :
    ∃ 𝒦 : Set (Set Pt), ¬ 𝒦.Countable ∧ 𝒦.PairwiseDisjoint id ∧
      ∀ K ∈ 𝒦, K ⊆ M ∩ (Icc a b ×ˢ univ) ∧ Fold.Q78.IsContinuum K ∧ (∃ z ∈ K, z.1 = a) ∧
        ∃ z ∈ K, z.1 = b := by
  sorry

/-- **O–T Theorem 3.2, strip form** (commission §6.3), as a named claim: copies of `Y` hanging from
the left line of the strip `[0, 1] × ℝ`, inside pairwise disjoint crossing continua, with `y`
beyond `X`; only countably many copies of `X` have positive surjective span. -/
def OTThm32 : Prop :=
  ∀ {Y : Type} [MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y] (X : Set Y) (x y : Y),
    Fold.Q78.IsContinuum X → x ∈ X →
    ∀ {ι : Type} (K : ι → Set Pt) (h : ι → Y → Pt),
      (∀ i, Fold.Q78.IsContinuum (K i) ∧ K i ⊆ Icc (0 : ℝ) 1 ×ˢ univ ∧
        (∃ z ∈ K i, z.1 = 0) ∧ ∃ z ∈ K i, z.1 = 1) →
      Pairwise (fun i j => Disjoint (K i) (K j)) →
      (∀ i, Continuous (h i) ∧ range (h i) ⊆ K i ∧ (h i x).1 = 0 ∧
        ∀ z ∈ X, (h i z).1 < (h i y).1) →
      {i | SurjSpanPos (h i '' X)}.Countable

/-- **O–T Corollary 3.5** from Theorem 3.2 (commission §6.4). -/
theorem ot82_cor35_of_thm32 (h32 : OTThm32) : OTCor35 := by
  sorry

/-- **Theorem C from Theorem 3.2.** -/
theorem theoremC_of_thm32 (h32 : OTThm32) : TheoremC :=
  theoremC_of_cor35 (ot82_cor35_of_thm32 h32)

/-! ## §7. For Theorem 3.2: disjoint crossing continua are ordered -/

/-- **§7**: two disjoint continua crossing the closed strip `[a, b] × ℝ` meet the line `x = a`
in sets one of which lies strictly below the other. -/
theorem crossing_traces_separated {a b : ℝ} (hab : a < b) {K K' : Set Pt}
    (hK : Fold.Q78.IsContinuum K) (hK' : Fold.Q78.IsContinuum K')
    (hKS : K ⊆ Icc a b ×ˢ univ) (hK'S : K' ⊆ Icc a b ×ˢ univ)
    (hKa : ∃ z ∈ K, z.1 = a) (hKb : ∃ z ∈ K, z.1 = b)
    (hK'a : ∃ z ∈ K', z.1 = a) (hK'b : ∃ z ∈ K', z.1 = b) (hdisj : Disjoint K K') :
    (∀ z ∈ K, ∀ z' ∈ K', z.1 = a → z'.1 = a → z.2 < z'.2) ∨
      (∀ z ∈ K, ∀ z' ∈ K', z.1 = a → z'.1 = a → z'.2 < z.2) := by
  sorry

end HPC.Span
