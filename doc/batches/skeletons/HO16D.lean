import HPC.HO16.HO16C

/-!
# Batch 196 skeleton: Hoehn–Oversteegen Theorem 1, IV — Proposition 19; Theorem 20 from Theorem 15

Save as `HPC/HO16/HO16D.lean` (splitting under `HPC/HO16/` is expected); add
`import HPC.HO16.HO16D` at the end of `HPC.lean`. Every `sorry` is a work item. Unproved items are
commented out with an `OPEN` note, as before. Library lemmas beyond those stated here are shape
left to you.

Source: Hoehn–Oversteegen 2016 (`doc/sources/hoehn-oversteegen2016.pdf`): Proposition 19 and its
proof (pp. 202–209); Theorem 15 (statement only, p. 194); Theorem 20 and its proof (pp. 209–210).
"Regular" is read as "PL graph"; `π = Prod.fst`; `G⋆ = G ×ˢ Icc 0 1`; for a fold `F ⊆ E × ℝ`,
`φ⋆⁻¹(X)` inside `F⋆` is `foldPre F X` (batch 195). Route: commission 196.
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

/-! ## §2. Library -/

/-- **p. 208**: "Since ∂π(P₂) is disjoint from the set Z of branch points and endpoints of G, we
have that the set of branch points and endpoints of F is φ⁻¹(Z)". -/
theorem IsSimpleFoldOf.isOrdinaryPt_iff {G G₁ G₂ G₃ : Set E} {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃) (hZ : ∀ y ∈ relFrontier G G₂, IsOrdinaryPt G y)
    {z : E × ℝ} (hz : z ∈ F₁ ∪ F₂ ∪ F₃) :
    IsOrdinaryPt (F₁ ∪ F₂ ∪ F₃) z ↔ IsOrdinaryPt G z.1 := by
  sorry

/-! ## §3. Proposition 19 -/

/-- **H–O Proposition 19 in the full fold** (pp. 202–208): for any simple fold with the
`Gᵢ` of p. 202 (`ho16_prop19_fold`), the sets of p. 203 form a broken stairwell structure of height
`k` with a pit at level `i₀ + 1` in `F⋆` if `i₀ < k`, and a stairwell structure of height `k` if
`i₀ = k`; all lie in `φ⋆⁻¹(S)`. `F` need not be connected. -/
theorem ho16_prop19_full {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
    {γ P₁ P₂ : Set (E × ℝ)} (hG : IsPLGraph G) (hconn : IsConnected G)
    (h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂) (hγ : γ.Nonempty)
    (hE : (endSet G P₁).Nonempty) {F₁ F₂ F₃ : Set (E × ℝ)}
    (hF : IsSimpleFoldOf G (Prod.fst '' P₁) (Prod.fst '' P₂)
      (sideOf G (Prod.fst '' γ) (Prod.fst '' T i₀)) F₁ F₂ F₃) :
    (⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ⊆
      foldPre (F₁ ∪ F₂ ∪ F₃) S ∧
    (i₀ < k → IsBrokenStairwellStr (F₁ ∪ F₂ ∪ F₃)
      ((⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1 ∪
        foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      k (i₀ + 1) (p19T F₁ F₂ F₃ T P₁ P₂ i₀) (p19α F₁ F₂ F₃ α i₀)
      (foldPre (F₁ ∪ F₂ ∪ F₃) (α (i₀ + 1)) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      (foldPre (F₁ ∪ F₂ ∪ F₃) P₂ ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)
      (foldPre (F₁ ∪ F₂ ∪ F₃) (T i₀) ∩ (F₁ ∪ F₂) ×ˢ Icc (0 : ℝ) 1)) ∧
    (i₀ = k → IsStairwellStr (F₁ ∪ F₂ ∪ F₃) (⋃ i ∈ Icc 1 k, p19T F₁ F₂ F₃ T P₁ P₂ i₀ i) k
      (p19T F₁ F₂ F₃ T P₁ P₂ i₀) (p19α F₁ F₂ F₃ α i₀)) := by
  sorry

/-- **H–O Proposition 19** (p. 202): "Then there exists a simple fold φ: F→G such that F is
connected, and φ⋆⁻¹(S) contains a set S′ with a broken stairwell structure of height k with a pit
at level i₀+1 if i₀<k, or simply a stairwell structure of height k if i₀=k." -/
theorem ho16_prop19 {G : Set E} {S : Set (E × ℝ)} {k i₀ : ℕ} {T α : ℕ → Set (E × ℝ)}
    {γ P₁ P₂ : Set (E × ℝ)} (hG : IsPLGraph G) (hconn : IsConnected G)
    (h : IsBrokenStairwellStr G S k i₀ T α γ P₁ P₂) (hγ : γ.Nonempty)
    (hE : (endSet G P₁).Nonempty) :
    ∃ (G₁ G₂ G₃ : Set E) (F₁ F₂ F₃ : Set (E × ℝ)), IsSimpleFoldOf G G₁ G₂ G₃ F₁ F₂ F₃ ∧
      IsConnected (F₁ ∪ F₂ ∪ F₃) ∧
      ∃ S' : Set ((E × ℝ) × ℝ), S' ⊆ foldPre (F₁ ∪ F₂ ∪ F₃) S ∧
        (i₀ < k → HasBrokenStairwell (F₁ ∪ F₂ ∪ F₃) S' k (i₀ + 1)) ∧
        (i₀ = k → HasStairwell (F₁ ∪ F₂ ∪ F₃) S' k) := by
  sorry

end Prop19

/-! ## §4. A sentence of p. 208 (in `ℝ`) -/

/-- **p. 208**: "Moreover, φ(D)⊂π(P₁∪P₂), so ∂D̃∩π(α_{i₀})=∅ by (S6′) for S" fails: a broken
stairwell structure of height 3 with a pit at level 2 on `G = [0, 10]` and a point `x` of
`π(P₂) \ π(S₂)` whose component in `G \ π(S₂)` has a frontier point in `π(α₂)` (commission §4). -/
theorem ho16_p208_false :
    ∃ (G : Set ℝ) (S : Set (ℝ × ℝ)) (T α : ℕ → Set (ℝ × ℝ)) (γ P₁ P₂ : Set (ℝ × ℝ)) (x : ℝ),
      IsPLGraph G ∧ IsConnected G ∧ IsBrokenStairwellStr G S 3 2 T α γ P₁ P₂ ∧ γ.Nonempty ∧
      (endSet G P₁).Nonempty ∧ x ∈ Prod.fst '' P₂ \ Prod.fst '' T 2 ∧
      (relFrontier G (connectedComponentIn (G \ Prod.fst '' T 2) x) ∩
        Prod.fst '' α 2).Nonempty := by
  sorry

/-! ## §5. Stretch: Theorem 20 from Theorem 15 -/

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

/-- **The induction of Theorem 20** (pp. 209–210): a map of a hereditarily indecomposable
compactum to a connected PL graph `G` is approximated by the first coordinate of a map into any
set with a stairwell structure of odd height. -/
theorem ho16_lift_stairwell (k : ℕ) (hk : Odd k) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : Set E) (hG : IsPLGraph G) (hconn : IsConnected G) (S : Set (E × ℝ))
    (hS : HasStairwell G S k) (X : Type) [MetricSpace X] [CompactSpace X]
    (hHI : IsHereditarilyIndecomposable (univ : Set X)) (f : X → E) (hf : Continuous f)
    (hfG : ∀ x, f x ∈ G) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : X → E × ℝ, Continuous h ∧ (∀ x, h x ∈ S) ∧ ∀ x, dist (f x) (h x).1 < ε := by
  sorry

/-- **H–O Theorem 20, forward direction**, from Theorem 15. -/
theorem ho16_theorem20_of_thm15 (h15 : HOThm15) : HOThm20 := by
  sorry

/-- The classification step of batch 193 with `HOThm15` as the only open input. -/
theorem homeomorph_pseudoArc_of_indec_homogeneous_of_thm15 (h15 : HOThm15) (M : Set Pt)
    [CompactSpace M] [ConnectedSpace M] (hhom : IsHomogeneous M)
    (hind : ¬ IsDecomposableSpace M) (hnt : (univ : Set M).Nontrivial) :
    ∃ M₀ : Set Pt, IsPseudoArc M₀ ∧ Nonempty (M ≃ₜ M₀) := by
  sorry

end HPC.HO16
