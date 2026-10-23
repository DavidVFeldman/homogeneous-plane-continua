import HPC.HO16.HO16A

/-!
# Batch 194 skeleton: Hoehn–Oversteegen Theorem 1, II — PL graphs, simple folds, Theorem 8

Save as `HPC/HO16/HO16B.lean` (splitting under `HPC/HO16/` is expected); add
`import HPC.HO16.HO16B` at the end of `HPC.lean`. Every `sorry` is a work item. Unproved items are
commented out with an `OPEN` note, as before. Library lemmas beyond those stated here are shape
left to you.

Source: Hoehn–Oversteegen 2016 (`doc/sources/hoehn-oversteegen2016.pdf`), §4: Definition 5,
Lemma 6, the construction on pp. 185–186, Proposition 7, Theorem 8. "Regular" (H–O p. 184) is
read as "PL graph" throughout. Route: commission 194.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-! ## §2. Definitions (commission §2) -/

/-- The frontier of `A` relative to `G`, `cl A ∩ cl (G \ A)` (H–O's `∂A` for `A ⊆ G`; also used
for `A` not closed, as in Lemma 6 (2)). -/
def relFrontier {α : Type*} [TopologicalSpace α] (G A : Set α) : Set α :=
  closure A ∩ closure (G \ A)

section Fold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **H–O Definition 5, (F1)–(F3)**, with "regular" read as "PL graph": the sets `G₁, G₂, G₃` of
a simple fold on `G`. -/
def IsFoldTriple (G G₁ G₂ G₃ : Set E) : Prop :=
  G₁.Nonempty ∧ G₂.Nonempty ∧ G₃.Nonempty ∧ IsPLGraph G₁ ∧ IsPLGraph G₂ ∧ IsPLGraph G₃ ∧
    G₁ ∪ G₃ = G ∧ G₂ = G₁ ∩ G₃ ∧ Disjoint (closure (G₁ \ G₂)) (closure (G₃ \ G₂))

/-- **H–O Definition 5: a simple fold on `G`**, realized inside `E × ℝ` with projection
`φ = Prod.fst`: (F1)–(F3) for the `Gᵢ`; each `Fᵢ` a PL graph mapped injectively onto `Gᵢ` (F4);
`φ(F₁ ∩ F₂) = ∂G₁`, `φ(F₂ ∩ F₃) = ∂G₃`, `F₁ ∩ F₃ = ∅` (F5). -/
def IsSimpleFoldOf (G G₁ G₂ G₃ : Set E) (F₁ F₂ F₃ : Set (E × ℝ)) : Prop :=
  IsFoldTriple G G₁ G₂ G₃ ∧ IsPLGraph F₁ ∧ IsPLGraph F₂ ∧ IsPLGraph F₃ ∧
    InjOn Prod.fst F₁ ∧ Prod.fst '' F₁ = G₁ ∧ InjOn Prod.fst F₂ ∧ Prod.fst '' F₂ = G₂ ∧
    InjOn Prod.fst F₃ ∧ Prod.fst '' F₃ = G₃ ∧
    Prod.fst '' (F₁ ∩ F₂) = relFrontier G G₁ ∧ Prod.fst '' (F₂ ∩ F₃) = relFrontier G G₃ ∧
    Disjoint F₁ F₃

end Fold

/-! ## §3. PL graphs: the library (commission §3) -/

section Library

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **§3.0, refinement**: a decomposition of `G` in which each of finitely many PL subgraphs
`A i` is the union of the edges it contains, every other edge meets `A i` only at its endpoints,
and every point of a finite `P ⊆ G` is a vertex. -/
theorem IsPLGraph.exists_refinement {G : Set E} (hG : IsPLGraph G) {k : ℕ} (A : Fin k → Set E)
    (hA : ∀ i, IsPLGraph (A i)) (hAG : ∀ i, A i ⊆ G) (P : Finset E) (hP : ∀ p ∈ P, p ∈ G) :
    ∃ S : Finset (E × E), (∀ s ∈ S, s.1 ≠ s.2) ∧ G = ⋃ s ∈ S, segment ℝ s.1 s.2 ∧
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
        segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2 ⊆ ({s.1, s.2} : Set E) ∩ {s'.1, s'.2}) ∧
      (∀ i, ∀ x ∈ A i, ∃ s ∈ S, x ∈ segment ℝ s.1 s.2 ∧ segment ℝ s.1 s.2 ⊆ A i) ∧
      (∀ i, ∀ s ∈ S, ¬ segment ℝ s.1 s.2 ⊆ A i → segment ℝ s.1 s.2 ∩ A i ⊆ {s.1, s.2}) ∧
      (∀ p ∈ P, ∃ s ∈ S, p = s.1 ∨ p = s.2) := by
  sorry

/-- **§3.1**: a finite union of nondegenerate segments is a PL graph (common subdivision). -/
theorem isPLGraph_biUnion {T : Finset (E × E)} (hT : ∀ t ∈ T, t.1 ≠ t.2) :
    IsPLGraph (⋃ t ∈ T, segment ℝ t.1 t.2) := by
  sorry

/-- **§3.2** -/
theorem IsPLGraph.union {A B : Set E} (hA : IsPLGraph A) (hB : IsPLGraph B) :
    IsPLGraph (A ∪ B) := by
  sorry

/-- **§3.3** -/
theorem IsPLGraph.closure_diff {G A : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hAG : A ⊆ G) : IsPLGraph (closure (G \ A)) := by
  sorry

/-- **§3.4**: a PL subgraph has finite frontier (H–O p. 184: "a regular set always has finite
boundary"). -/
theorem IsPLGraph.relFrontier_finite {G A : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hAG : A ⊆ G) : (relFrontier G A).Finite := by
  sorry

/-- **§3.5**: components of a PL graph are PL graphs, ... -/
theorem IsPLGraph.connectedComponentIn {G : Set E} (hG : IsPLGraph G) (p : E) :
    IsPLGraph (connectedComponentIn G p) := by
  sorry

/-- **§3.5**: ... there are finitely many of them, ... -/
theorem IsPLGraph.finite_components {G : Set E} (hG : IsPLGraph G) :
    {C : Set E | ∃ p ∈ G, C = connectedComponentIn G p}.Finite := by
  sorry

/-- **§3.5**: ... and a PL subgraph meets each in a PL graph. -/
theorem IsPLGraph.inter_connectedComponentIn {G A : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hAG : A ⊆ G) (p : E) : IsPLGraph (A ∩ connectedComponentIn G p) := by
  sorry

/-- **§3.6**: the projection of a PL graph in `E × ℝ` on which `Prod.fst` is injective. -/
theorem IsPLGraph.image_fst {F : Set (E × ℝ)} (hF : IsPLGraph F) (hinj : InjOn Prod.fst F) :
    IsPLGraph (Prod.fst '' F) := by
  sorry

end Library

/-! ## §4. Simple folds exist (commission §4; H–O pp. 185–186) -/

/-- **The construction of pp. 185–186**, inside `E × ℝ`: every triple satisfying (F1)–(F3) is
the triple of a simple fold. (H–O: "It is straightforward to see that this is a well defined
simple fold".) -/
theorem exists_simpleFold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G G₁ G₂ G₃ : Set E} (h : IsFoldTriple G G₁ G₂ G₃) :
    ∃ F₁ F₂ F₃ : Set (E × ℝ), IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃ := by
  sorry

/-! ## §5. Lemma 6 (commission §5; H–O p. 185, "left to the reader") -/

/-- **H–O Lemma 6**, items (1), (2), (4), (5), (6), (7); item (3) is part of `IsSimpleFoldOf`
(each `Fᵢ` is a PL graph). -/
theorem ho16_lemma6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)} (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) :
    -- (1)
    relFrontier G G₂ = relFrontier G G₁ ∪ relFrontier G G₃ ∧
    Disjoint (relFrontier G G₁) (relFrontier G G₃) ∧
    -- (2)
    relFrontier G (G₁ \ G₂) = relFrontier G G₃ ∧ relFrontier G (G₃ \ G₂) = relFrontier G G₁ ∧
    -- (4)
    (F₁ ∩ F₂).Finite ∧ (F₂ ∩ F₃).Finite ∧
    -- (5)
    relFrontier (F₁ ∪ F₂ ∪ F₃) F₁ = F₁ ∩ F₂ ∧ relFrontier (F₁ ∪ F₂ ∪ F₃) F₃ = F₂ ∩ F₃ ∧
    relFrontier (F₁ ∪ F₂ ∪ F₃) F₂ = (F₁ ∩ F₂) ∪ (F₂ ∩ F₃) ∧
    -- (6)
    SeparatesIn (F₁ ∪ F₂ ∪ F₃) (F₁ ∩ F₂) (F₁ \ F₂) ((F₂ ∪ F₃) \ F₁) ∧
    SeparatesIn (F₁ ∪ F₂ ∪ F₃) (F₂ ∩ F₃) (F₃ \ F₂) ((F₁ ∪ F₂) \ F₃) ∧
    -- (7)
    (∀ p ∈ F₁ \ F₂, ∀ N ∈ 𝓝 p, Prod.fst '' (N ∩ F₁) ∈ 𝓝[G] p.1) ∧
    (∀ p ∈ F₂ \ (F₁ ∪ F₃), ∀ N ∈ 𝓝 p, Prod.fst '' (N ∩ F₂) ∈ 𝓝[G] p.1) ∧
    (∀ p ∈ F₃ \ F₂, ∀ N ∈ 𝓝 p, Prod.fst '' (N ∩ F₃) ∈ 𝓝[G] p.1) := by
  sorry

/-! ## §6. Theorem 8, (1) ⇒ (2), for simple folds (commission §6) -/

/-- **H–O Theorem 8, (1) ⇒ (2)** (pp. 187–189): a map of a hereditarily indecomposable compactum
to `G` lifts, up to `ε`, through any simple fold on `G`. -/
theorem ho16_theorem8 {X : Type*} [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G G₁ G₂ G₃ : Set E}
    {F₁ F₂ F₃ : Set (E × ℝ)} (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃)
    {f : X → E} (hf : Continuous f) (hfG : ∀ x, f x ∈ G) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → E × ℝ, Continuous g ∧ (∀ x, g x ∈ F₁ ∪ F₂ ∪ F₃) ∧ ∀ x, dist (f x) (g x).1 < ε := by
  sorry

/-! ## §7. Proposition 7 (commission §7) -/

/-- **H–O Proposition 7** (pp. 186–187): for connected `G` with `∂G₁ ≠ ∅ ≠ ∂G₃`, some component
`C` of `F` has `φ(C)` meeting `∂G₁` and `∂G₃`; for every such component, `φ(C) = G` and the
pieces `Fᵢ ∩ C` form a simple fold on `G`. -/
theorem ho16_prop7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)} (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃)
    (hG : IsConnected G) (h₁ : (relFrontier G G₁).Nonempty) (h₃ : (relFrontier G G₃).Nonempty) :
    (∃ p ∈ F₁ ∪ F₂ ∪ F₃,
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₁).Nonempty ∧
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₃).Nonempty) ∧
    ∀ p ∈ F₁ ∪ F₂ ∪ F₃,
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₁).Nonempty →
      (Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p ∩ relFrontier G G₃).Nonempty →
      Prod.fst '' connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p = G ∧
      IsSimpleFoldOf G (Prod.fst '' (F₁ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p))
        (Prod.fst '' (F₂ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p))
        (Prod.fst '' (F₃ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p))
        (F₁ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p)
        (F₂ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p)
        (F₃ ∩ connectedComponentIn (F₁ ∪ F₂ ∪ F₃) p) := by
  sorry

/-! ## §8. Theorem 1 and Theorem 1′ as printed (commission §8) -/

/-- H–O p. 212: **surjective semispan zero**: every subcontinuum `Z ⊆ X × X` with `π₂(Z) = X`
meets the diagonal. -/
def SurjSemiSpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ Z : Set (X × X), Fold.Q78.IsContinuum Z → Prod.snd '' Z = univ → ∃ p ∈ Z, p.1 = p.2

/-- **Theorem 1 as restated on p. 211** ("A continuum X is homeomorphic to the pseudo-arc if and
only if X is hereditarily indecomposable and has span zero") fails for a one-point continuum. -/
theorem ho16_theorem1_printed_false :
    ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X],
      (∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (X ≃ₜ M₀)) ↔
        (IsHereditarilyIndecomposable (univ : Set X) ∧ HOSpanZero X) := by
  sorry

/-- **Theorem 1′ as printed on p. 212** ("A continuum X is homeomorphic to the pseudo-arc if and
only if X is hereditarily indecomposable and has surjective semispan zero") fails for a one-point
continuum. -/
theorem ho16_theorem1prime_printed_false :
    ¬ ∀ (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X],
      (∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (X ≃ₜ M₀)) ↔
        (IsHereditarilyIndecomposable (univ : Set X) ∧ SurjSemiSpanZero X) := by
  sorry

end HPC.HO16
