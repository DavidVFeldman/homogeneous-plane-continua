import HPC.HO16.HO16A

/-!
# Batch 194, §2: relative frontier, fold triples, simple folds

Part of the batch-194 skeleton `HO16B.lean` (commission 194, §2), split off unchanged.
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

end HPC.HO16
