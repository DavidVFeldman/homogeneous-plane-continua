import HPC.HO16.HO16B

/-!
# Batch 195, definitions: sides, ordinary points, straight sets, stairwells (commission §§3–6)

Part of the batch-195 skeleton `HO16C.lean` (commission 195), split under `HPC/HO16/`.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Definitions (commission §§3–6) -/

/-- **H–O Definition 9, first bullet** (p. 189): `A` has consistent complement relative to `B` if
for each component `C` of `G \ A`, either `∂C ⊆ B` or `∂C ∩ B = ∅`. (H–O's standing hypotheses
"`A ⊆ G` regular, `B ⊆ ∂A`" are hypotheses of the theorems below, not part of the definition.) -/
def HasConsCompl (G A B : Set E) : Prop :=
  ∀ x ∈ G \ A, relFrontier G (connectedComponentIn (G \ A) x) ⊆ B ∨
    Disjoint (relFrontier G (connectedComponentIn (G \ A) x)) B

/-- **H–O Definition 9, second bullet** (p. 190): the `A` side of `B`, `σ_B(A)`, the closure of
the union of all components of `G \ B` meeting `A`. -/
def sideOf (G B A : Set E) : Set E :=
  closure (⋃ x ∈ G \ B, ⋃ (_ : (connectedComponentIn (G \ B) x ∩ A).Nonempty),
    connectedComponentIn (G \ B) x)

/-- A point of `G` which is neither a branch point nor an endpoint of `G` (H–O p. 183), in PL
form: `x` has a neighbourhood in `G` which is the union of two segments meeting only at `x`.
For PL graphs this is "order 2" (`isOrdinaryPt_iff_order`). -/
def IsOrdinaryPt (G : Set E) (x : E) : Prop :=
  ∃ a b : E, a ≠ x ∧ b ≠ x ∧ segment ℝ a x ∩ segment ℝ x b = {x} ∧
    segment ℝ a x ∪ segment ℝ x b ⊆ G ∧ segment ℝ a x ∪ segment ℝ x b ∈ 𝓝[G] x

/-- **H–O Definition 12 (1)** (p. 192): a collection `⟨B₁, …, Bₙ⟩` of finite subsets of `G` is
generic if each `Bᵢ` misses the branch points and endpoints of `G` and `Bᵢ ∩ Bⱼ = ∅` for
`i ≠ j`. -/
def IsGeneric (G : Set E) (L : List (Set E)) : Prop :=
  (∀ B ∈ L, B.Finite ∧ B ⊆ G ∧ ∀ x ∈ B, IsOrdinaryPt G x) ∧ L.Pairwise Disjoint

/-- **H–O Definition 12 (2)** (p. 192): `S ⊆ G⋆` is straight if `S` is closed, `π` is one-to-one
on `S`, and `π(S)` is regular. -/
def IsStraight (G : Set E) (S : Set (E × ℝ)) : Prop :=
  S ⊆ G ×ˢ Icc (0 : ℝ) 1 ∧ IsClosed S ∧ InjOn Prod.fst S ∧ IsPLGraph (Prod.fst '' S)

/-- **H–O Definition 12 (2)**: the end set `𝓔(S) = S ∩ π⁻¹(∂π(S))`. -/
def endSet (G : Set E) (S : Set (E × ℝ)) : Set (E × ℝ) :=
  S ∩ Prod.fst ⁻¹' relFrontier G (Prod.fst '' S)

/-- **H–O Definition 13** (p. 192): `⟨T 1, …, T k⟩` is a stairwell structure of height `k` for
`S`, with `αᵢ = α i` and `βᵢ = α (i + 1)` (so `βᵢ = αᵢ₊₁` holds by construction, and
`β_k = ∅` is `α (k + 1) = ∅`). -/
def IsStairwellStr (G : Set E) (S : Set (E × ℝ)) (k : ℕ) (T α : ℕ → Set (E × ℝ)) : Prop :=
  1 ≤ k ∧
  -- (S1)
  (∀ i ∈ Icc 1 k, (T i).Nonempty ∧ IsStraight G (T i)) ∧ (S = ⋃ i ∈ Icc 1 k, T i) ∧
  -- (S2)
  (∀ i ∈ Icc 1 k, endSet G (T i) = α i ∪ α (i + 1) ∧ Disjoint (α i) (α (i + 1)) ∧
    (α i).Finite ∧ (α (i + 1)).Finite) ∧
  α 1 = ∅ ∧ α (k + 1) = ∅ ∧
  -- (S3)
  (∀ i ∈ Ico 1 k, ∃ V ∈ 𝓝ˢ (Prod.fst '' α (i + 1)),
    Prod.fst '' T i ∩ V = Prod.fst '' T (i + 1) ∩ V) ∧
  -- (S4)
  (∀ i ∈ Icc 1 k, HasConsCompl G (Prod.fst '' T i) (Prod.fst '' α i) ∧
    HasConsCompl G (Prod.fst '' T i) (Prod.fst '' α (i + 1))) ∧
  -- (S5): the family `⟨π(α₂), …, π(α_k)⟩`
  IsGeneric G ((List.range' 2 (k - 1)).map fun i => Prod.fst '' α i)

/-- `S` has a stairwell structure of height `k`. -/
def HasStairwell (G : Set E) (S : Set (E × ℝ)) (k : ℕ) : Prop :=
  ∃ T α : ℕ → Set (E × ℝ), IsStairwellStr G S k T α

/-- **H–O Definition 16** (pp. 199–200): `⟨T 1, …, T k; P₁, P₂⟩` is a broken stairwell structure
of height `k` with a pit at level `i₀`; `αᵢ = α i`, `βᵢ = α (i + 1)`, `γ_{i₀} = γ`. -/
def IsBrokenStairwellStr (G : Set E) (S : Set (E × ℝ)) (k i₀ : ℕ) (T α : ℕ → Set (E × ℝ))
    (γ P₁ P₂ : Set (E × ℝ)) : Prop :=
  1 ≤ i₀ ∧ i₀ ≤ k ∧
  -- (S1′)
  (∀ i ∈ Icc 1 k, (T i).Nonempty ∧ IsStraight G (T i)) ∧
  P₁.Nonempty ∧ IsStraight G P₁ ∧ P₂.Nonempty ∧ IsStraight G P₂ ∧
  (S = (⋃ i ∈ Icc 1 k, T i) ∪ P₁ ∪ P₂) ∧
  -- (S2′)
  (∀ i ∈ Icc 1 k, i ≠ i₀ → endSet G (T i) = α i ∪ α (i + 1) ∧ Disjoint (α i) (α (i + 1))) ∧
  endSet G (T i₀) = α i₀ ∪ α (i₀ + 1) ∪ γ ∧ Disjoint (α i₀) (α (i₀ + 1)) ∧
  Disjoint (α i₀) γ ∧ Disjoint (α (i₀ + 1)) γ ∧
  (∀ i ∈ Icc 1 (k + 1), (α i).Finite) ∧ γ.Finite ∧ α 1 = ∅ ∧ α (k + 1) = ∅ ∧
  endSet G P₂ = endSet G P₁ ∪ γ ∧ Disjoint (endSet G P₁) γ ∧
  -- (S3′)
  (∀ i ∈ Ico 1 k, ∃ V ∈ 𝓝ˢ (Prod.fst '' α (i + 1)),
    Prod.fst '' T i ∩ V = Prod.fst '' T (i + 1) ∩ V) ∧
  (∃ V ∈ 𝓝ˢ (Prod.fst '' endSet G P₁), Prod.fst '' P₁ ∩ V = Prod.fst '' P₂ ∩ V) ∧
  (∃ W ∈ 𝓝ˢ (Prod.fst '' γ), Prod.fst '' P₂ ∩ W = Prod.fst '' T i₀ ∩ W) ∧
  -- (S4′)
  (∀ i ∈ Icc 1 k, HasConsCompl G (Prod.fst '' T i) (Prod.fst '' α i) ∧
    HasConsCompl G (Prod.fst '' T i) (Prod.fst '' α (i + 1))) ∧
  HasConsCompl G (Prod.fst '' T i₀) (Prod.fst '' γ) ∧
  HasConsCompl G (Prod.fst '' P₂) (Prod.fst '' endSet G P₁) ∧
  HasConsCompl G (Prod.fst '' P₂) (Prod.fst '' γ) ∧
  -- (S5′): the family `⟨π(α₂), …, π(α_k), π(𝓔(P₁)), π(γ_{i₀})⟩`
  IsGeneric G (((List.range' 2 (k - 1)).map fun i => Prod.fst '' α i) ++
    [Prod.fst '' endSet G P₁, Prod.fst '' γ]) ∧
  -- (S6′)
  Disjoint (Prod.fst '' α i₀) (Prod.fst '' (P₁ ∪ P₂))

/-- `S` has a broken stairwell structure of height `k` with a pit at level `i₀`. -/
def HasBrokenStairwell (G : Set E) (S : Set (E × ℝ)) (k i₀ : ℕ) : Prop :=
  ∃ (T α : ℕ → Set (E × ℝ)) (γ P₁ P₂ : Set (E × ℝ)), IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂

/-- H–O p. 192: `φ⋆(x, t) = (φ(x), t)` for the fold projection `φ = Prod.fst`. -/
def phiStar (q : (E × ℝ) × ℝ) : E × ℝ := (q.1.1, q.2)

/-- `φ⋆⁻¹(S)` inside `F⋆ = F × [0, 1]`. -/
def foldPre (F S : Set (E × ℝ)) : Set ((E × ℝ) × ℝ) :=
  F ×ˢ Icc (0 : ℝ) 1 ∩ phiStar ⁻¹' S

end Defs

end HPC.HO16
