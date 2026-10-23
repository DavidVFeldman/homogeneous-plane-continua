import HPC.HO16.HO16C

/-!
# Batch 196, definitions: the sets of p. 203, Theorem 15, Proposition 19 as a `Prop`

Part of the batch-196 skeleton `HO16D.lean` (commission 196), split under `HPC/HO16/`.
`p19T`, `p19α` and `HOThm15` are the skeleton's. `HOProp19` (new, batch 196) is the statement of
the skeleton's `ho16_prop19`, quantified over `E : Type`, recorded as a named `Prop` so that
Theorem 20 can be derived from it (commission §5); it is proved in `Prop19Conn.lean`
(`hoProp19_holds`).
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

section Prop19

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## §3. The sets of p. 203 -/

/-- H–O p. 203: `S'ᵢ = φ⋆⁻¹(Sᵢ)` for `i ≠ i₀`, and
`S'_{i₀} = [φ⋆⁻¹(P₁) ∩ (F₁)⋆] ∪ [φ⋆⁻¹(P₂) ∩ (F₂)⋆] ∪ [φ⋆⁻¹(S_{i₀}) ∩ (F₃)⋆]`. -/
def p19T (F₁ F₂ F₃ : Set (E × ℝ)) (T : ℕ → Set (E × ℝ)) (P₁ P₂ : Set (E × ℝ)) (i₀ i : ℕ) :
    Set ((E × ℝ) × ℝ) :=
  if i = i₀ then
    foldPre (F₁ ∪ F₂ ∪ F₃) P₁ ∩ F₁ ×ˢ Icc (0 : ℝ) 1 ∪
      foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ F₂ ×ˢ Icc (0 : ℝ) 1 ∪
      foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ F₃ ×ˢ Icc (0 : ℝ) 1
  else foldPre (F₁ ∪ F₂ ∪ F₃) (T i)

/-- H–O p. 203 in the one-`α` encoding: `α'ᵢ = φ⋆⁻¹(αᵢ)` for `i ≠ i₀ + 1`, and
`α'_{i₀+1} = φ⋆⁻¹(α_{i₀+1}) ∩ (F₃)⋆` (`= β'_{i₀}`). -/
def p19α (F₁ F₂ F₃ : Set (E × ℝ)) (α : ℕ → Set (E × ℝ)) (i₀ i : ℕ) : Set ((E × ℝ) × ℝ) :=
  if i = i₀ + 1 then foldPre (F₁ ∪ F₂ ∪ F₃) (α i) ∩ F₃ ×ˢ Icc (0 : ℝ) 1
  else foldPre (F₁ ∪ F₂ ∪ F₃) (α i)

end Prop19

/-! ## §5. Theorem 15 and Proposition 19 as named `Prop`s -/

/-- **H–O Theorem 15** (p. 194), for PL graphs: "For any set M⊆G×(0,1) which separates G×{0}
from G×{1} in G⋆, and any open set U⊆G×(0,1) with M⊆U, there exists a set S⊂U with a stairwell
structure of odd height." Named `Prop`; to be proved in a later batch. Stated for connected `G`
(nonempty: H–O's graphs are unions of arcs; with `G = ∅` the statement would be false), the only
case Theorem 20 uses after its reduction to components. -/
def HOThm15 : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set E), IsPLGraph G →
    IsConnected G → ∀ M : Set (E × ℝ), M ⊆ G ×ˢ Ioo (0 : ℝ) 1 →
      SeparatesIn (G ×ˢ Icc (0 : ℝ) 1) M (G ×ˢ ({0} : Set ℝ)) (G ×ˢ ({1} : Set ℝ)) →
    ∀ U : Set (E × ℝ), IsOpen U → M ⊆ U →
      ∃ (S : Set (E × ℝ)) (k : ℕ), S ⊆ U ∩ G ×ˢ Ioo (0 : ℝ) 1 ∧ Odd k ∧ HasStairwell G S k

/-- **H–O Proposition 19** (p. 202), the statement of the skeleton's `ho16_prop19` quantified over
`E : Type`: "Let G be a connected graph, and let S⊂G⋆ have a broken stairwell structure
⟨S₁, ..., S_k; P₁, P₂⟩ of height k with a pit at level i₀⩽k, in which γ_{i₀}≠∅ and 𝓔(P₁)≠∅.
Then there exists a simple fold φ: F→G such that F is connected, and φ⋆⁻¹(S) contains a set S′
with a broken stairwell structure of height k with a pit at level i₀+1 if i₀<k, or simply a
stairwell structure of height k if i₀=k." New in batch 196 (shape change): a named `Prop`, the
hypothesis of `ho16_theorem20_of_thm15_prop19`, discharged by `hoProp19_holds`
(`Prop19Conn.lean`). -/
def HOProp19 : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set E) (S : Set (E × ℝ))
    (k i₀ : ℕ) (T α : ℕ → Set (E × ℝ)) (γ P₁ P₂ : Set (E × ℝ)), IsPLGraph G → IsConnected G →
    IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂ → γ.Nonempty → (endSet G P₁).Nonempty →
    ∃ (G₁ G₂ G₃ : Set E) (F₁ F₂ F₃ : Set (E × ℝ)), IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃ ∧
      IsConnected (F₁ ∪ F₂ ∪ F₃) ∧
      ∃ S' : Set ((E × ℝ) × ℝ), S' ⊆ foldPre (F₁ ∪ F₂ ∪ F₃) S ∧
        (i₀ < k → HasBrokenStairwell (F₁ ∪ F₂ ∪ F₃) S' k (i₀ + 1)) ∧
        (i₀ = k → HasStairwell (F₁ ∪ F₂ ∪ F₃) S' k)

end HPC.HO16
