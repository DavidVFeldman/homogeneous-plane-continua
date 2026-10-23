import HPC.Span.OT82B
import HPC.Plane.PseudoArc51
import HPC.Plane.EpsMap98
import HPC.Plane.Ingram68Star
import HPC.Plane.Most51

/-!
# Batch 193 skeleton: Hoehn–Oversteegen Theorem 1, I

Save as `HPC/HO16/HO16A.lean` (a new directory; splitting under `HPC/HO16/` is expected); add
`import HPC.HO16.HO16A` at the end of `HPC.lean`. Every `sorry` is a work item. Unproved items are
commented out with an `OPEN` note, as before.

Sources: Hoehn–Oversteegen 2016 (`doc/sources/hoehn-oversteegen2016.pdf`), Theorems 1, 4, 8 and
20; Krasinkiewicz–Minc 1977 (`doc/sources/krasinkiewicz-minc1977.pdf`), Lemma 2. Route:
commission 193. The target is `homeomorph_pseudoArc_of_indec_homogeneous`, whose only open input
should be the named `Prop` `HOThm20` (H–O Theorem 20, forward direction, for PL graphs).
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ## §2. Definitions (commission §2) -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **PL graph** (H–O p. 183, "graph", in piecewise linear form): a finite union of
nondegenerate segments, two different ones meeting at most in common endpoints. -/
def IsPLGraph (G : Set E) : Prop :=
  ∃ S : Finset (E × E), (∀ s ∈ S, s.1 ≠ s.2) ∧ G = ⋃ s ∈ S, segment ℝ s.1 s.2 ∧
    ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
      segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2 ⊆ ({s.1, s.2} : Set E) ∩ {s'.1, s'.2}

/-- **A fan at `y` in `A` of diameter `< r`** (H–O p. 187): finitely many segments `[y, z k]`,
pairwise meeting only at `y`, whose union with `{y}` lies in `A`, is a neighbourhood of `y` in
`A`, and has diameter `< r`. -/
def IsFanAt (A : Set E) (y : E) (r : ℝ) (Y : Set E) : Prop :=
  ∃ (n : ℕ) (z : Fin n → E), (∀ k, z k ≠ y) ∧ Y = insert y (⋃ k, segment ℝ y (z k)) ∧ Y ⊆ A ∧
    (∀ k l, k ≠ l → segment ℝ y (z k) ∩ segment ℝ y (z l) = {y}) ∧ Y ∈ 𝓝[A] y ∧
    Metric.diam Y < r

end Defs

/-- **`M` separates `P` from `Q` in `Y`**: two open sets cover `Y \ M`, are disjoint on `Y \ M`,
and contain `P` and `Q` respectively. -/
def SeparatesIn {α : Type*} [TopologicalSpace α] (Y M P Q : Set α) : Prop :=
  ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ Y \ M ⊆ U ∪ V ∧ U ∩ V ∩ (Y \ M) = ∅ ∧ P ⊆ U ∧ Q ⊆ V

/-- **H–O Theorem 20, forward direction ("only if"), for PL graphs** (p. 209). A map `f` of a
hereditarily indecomposable compactum to a PL graph `G` is approximated by the first coordinate
of a map into any open `U` containing a separator `M ⊆ G × (0, 1)` of `G × {0}` from `G × {1}`.
The open input of this batch's assembly; to be proved in later batches. -/
def HOThm20 : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X], IsHereditarilyIndecomposable (univ : Set X) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set E), IsPLGraph G →
    ∀ f : X → E, Continuous f → (∀ x, f x ∈ G) →
    ∀ M : Set (E × ℝ), M ⊆ G ×ˢ Ioo (0 : ℝ) 1 →
      SeparatesIn (G ×ˢ Icc (0 : ℝ) 1) M (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ)) →
    ∀ U : Set (E × ℝ), IsOpen U → M ⊆ U →
    ∀ ε : ℝ, 0 < ε → ∃ h : X → E × ℝ, Continuous h ∧ (∀ x, h x ∈ U ∩ (G ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ x, dist (f x) (h x).1 < ε

section Lemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A PL graph is compact. -/
theorem IsPLGraph.isCompact {G : Set E} (hG : IsPLGraph G) : IsCompact G := by
  sorry

/-- Every point of a PL graph has fans of every diameter (commission §2). -/
theorem IsPLGraph.exists_fan {G : Set E} (hG : IsPLGraph G) {y : E} (hy : y ∈ G) {r : ℝ}
    (hr : 0 < r) : ∃ Y, IsFanAt G y r Y := by
  sorry

end Lemmas

/-- Separation from a closed splitting (take `U = R₁ᶜ`, `V = R₀ᶜ`). -/
theorem separatesIn_of_closed {α : Type*} [TopologicalSpace α] {Y M P Q R₀ R₁ : Set α}
    (h₀ : IsClosed R₀) (h₁ : IsClosed R₁) (hdisj : Disjoint R₀ R₁) (hcov : Y \ M ⊆ R₀ ∪ R₁)
    (hP : P ⊆ R₀) (hQ : Q ⊆ R₁) : SeparatesIn Y M P Q := by
  sorry

/-! ## §3. Krasinkiewicz–Minc, Lemma 2 (commission §3) -/

/-- **Krasinkiewicz–Minc 1977, Lemma 2**, for hereditarily indecomposable compacta, in the form
quoted by H–O on p. 187 (K–M's `F₀, F₁, F₂` are `X₁, X₂, X₃`). -/
theorem km77_lemma2 {X : Type*} [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X)) {A B U V : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hBV : B ⊆ V) :
    ∃ X₁ X₂ X₃ : Set X, IsClosed X₁ ∧ IsClosed X₂ ∧ IsClosed X₃ ∧ X₁ ∪ X₂ ∪ X₃ = univ ∧
      A ⊆ X₁ ∧ B ⊆ X₃ ∧ Disjoint X₁ X₃ ∧ X₁ ∩ X₂ ⊆ V ∧ X₂ ∩ X₃ ⊆ U := by
  sorry

/-! ## §4. H–O Theorem 8, (1) ⇒ (2): the core (commission §4) -/

/-- **H–O Theorem 8, (1) ⇒ (2), before lifting to a fold** (pp. 187–189). From `f : X → G` and
sets `G₁, G₂, G₃` satisfying H–O's (F2), (F3), with finite frontiers `B₁ = cl(G₁ \ G₂) ∩ G₂`,
`B₃ = cl(G₃ \ G₂) ∩ G₂` that have fans in `G₂`: a map `h` close to `f` and a closed cover
`X₁, X₂, X₃` with `h(Xᵢ) ⊆ Gᵢ`, `h(X₁ ∩ X₂) ⊆ B₃`, `h(X₂ ∩ X₃) ⊆ B₁`, `X₁ ∩ X₃ = ∅`. -/
theorem ho16_theorem8_core {X : Type*} [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G G₁ G₂ G₃ : Set E}
    (hG₁ : IsClosed G₁) (hG₃ : IsClosed G₃) (hcov : G₁ ∪ G₃ = G) (hG₂ : G₂ = G₁ ∩ G₃)
    (hF3 : Disjoint (closure (G₁ \ G₂)) (closure (G₃ \ G₂)))
    (hfin₁ : (closure (G₁ \ G₂) ∩ G₂).Finite) (hfin₃ : (closure (G₃ \ G₂) ∩ G₂).Finite)
    (hfan : ∀ y ∈ (closure (G₁ \ G₂) ∪ closure (G₃ \ G₂)) ∩ G₂, ∀ r : ℝ, 0 < r →
      ∃ Y, IsFanAt G₂ y r Y)
    {f : X → E} (hf : Continuous f) (hfG : ∀ x, f x ∈ G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : X → E) (X₁ X₂ X₃ : Set X), Continuous h ∧ (∀ x, dist (f x) (h x) < ε) ∧
      IsClosed X₁ ∧ IsClosed X₂ ∧ IsClosed X₃ ∧ X₁ ∪ X₂ ∪ X₃ = univ ∧ Disjoint X₁ X₃ ∧
      (∀ x ∈ X₁, h x ∈ G₁) ∧ (∀ x ∈ X₂, h x ∈ G₂) ∧ (∀ x ∈ X₃, h x ∈ G₃) ∧
      (∀ x ∈ X₁ ∩ X₂, h x ∈ closure (G₃ \ G₂) ∩ G₂) ∧
      (∀ x ∈ X₂ ∩ X₃, h x ∈ closure (G₁ \ G₂) ∩ G₂) := by
  sorry

/-! ## §5. H–O Theorem 4, path form (commission §5) -/

/-- **H–O Theorem 4** (p. 184), with the arc `I` replaced by a path `γ` on `[0, 1]` and
`I \ {p, q}` by `(0, 1)`; of `G` only `G ⊆ thickening δ X` is assumed; `X` need not be connected,
and `E` is any proper metric space. -/
theorem ho16_theorem4 {E : Type*} [MetricSpace E] [ProperSpace E] {X : Set E} (hX : IsCompact X)
    (hspan : HOSpanZero X) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ G : Set E, IsCompact G → G ⊆ thickening δ X →
      ∀ γ : ℝ → E, Continuous γ → γ '' Icc (0 : ℝ) 1 ⊆ thickening δ X →
        X ⊆ thickening δ (γ '' Icc (0 : ℝ) 1) →
        SeparatesIn (G ×ˢ Icc (0 : ℝ) 1)
          {p : E × ℝ | p.1 ∈ G ∧ p.2 ∈ Ioo (0 : ℝ) 1 ∧ dist p.1 (γ p.2) < ε}
          (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ)) := by
  sorry

/-! ## §6. Plane approximations (commission §6) -/

/-- **§6.1**: a hereditarily indecomposable plane set has empty interior. -/
theorem interior_eq_empty_of_hi {M : Set Pt} (hHI : IsHereditarilyIndecomposable (univ : Set M)) :
    interior M = ∅ := by
  sorry

/-- **§6.2, grid graphs**: radial projections in the squares of a fine grid map a compact plane
set with empty interior into a nearby PL graph. -/
theorem exists_plGraph_approx {X : Set Pt} (hX : IsCompact X) (hint : interior X = ∅) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ G : Set Pt, IsPLGraph G ∧ G ⊆ thickening δ X ∧
      ∃ f : Pt → Pt, ContinuousOn f X ∧ ∀ x ∈ X, f x ∈ G ∧ dist (f x) x < δ := by
  sorry

/-- **§6.3**: a path close to a plane continuum. -/
theorem exists_path_approx {X : Set Pt} (hX : IsCompact X) (hXc : IsConnected X) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ γ : ℝ → Pt, Continuous γ ∧ γ '' Icc (0 : ℝ) 1 ⊆ thickening δ X ∧
      X ⊆ thickening δ (γ '' Icc (0 : ℝ) 1) := by
  sorry

/-! ## §7. The assembly (commission §7) -/

/-- **H–O Theorem 1, "if" direction, for plane continua**, from `HOThm20`: a hereditarily
indecomposable plane continuum with span zero is snake-like. -/
theorem ho16_theorem1_plane (h20 : HOThm20) (M : Set Pt) [CompactSpace M] [ConnectedSpace M]
    (hHI : IsHereditarilyIndecomposable (univ : Set M)) (hspan : HOSpanZero M) :
    IsSnakeLike (univ : Set M) := by
  sorry

/-- H–O p. 180: "every indecomposable non-degenerate homogeneous plane continuum is a
pseudo-arc", from Theorems B and C and `HOThm20`. -/
theorem isPseudoArc_of_indec_homogeneous (h20 : HOThm20) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hhom : IsHomogeneous M) (hind : ¬ IsDecomposableSpace M)
    (hnt : (univ : Set M).Nontrivial) : IsPseudoArc (univ : Set M) := by
  sorry

/-- The same, as a homeomorphism onto a plane pseudo-arc (`pseudoArc_unique`). -/
theorem homeomorph_pseudoArc_of_indec_homogeneous (h20 : HOThm20) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hhom : IsHomogeneous M) (hind : ¬ IsDecomposableSpace M)
    (hnt : (univ : Set M).Nontrivial) :
    ∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (M ≃ₜ M₀) := by
  sorry

end HPC.HO16
