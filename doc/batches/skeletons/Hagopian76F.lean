import HPC.Hagopian.Hagopian76E

/-!
# Batch 161 skeleton: Hagopian 1976, Theorem 1 set-up (T4–T9, T11, T14: `ε₁`, the chain of
# elevenths, Property 1, Property 3); Lemma 7; Lemma 9

Save as `HPC/Hagopian/Hagopian76F.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76F` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report. When an item here proves
a statement left commented out in `Hagopian76D.lean` or `Hagopian76E.lean`, delete the
commented-out copies (allowed).

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 343–347. Shapes follow report 160 §5.
Items marked *shape left to you* are internal steps of Theorem 1's proof; their statements depend on
the construction, and the report must quote the printed sentence each one renders.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- The `i`-th eleventh of `E` (p. 345: `k⁻¹[[(i − 1)/11, i/11]]`). -/
def piece {E : Set M} (k : E → unitInterval) (i : ℕ) : Set M :=
  layerSet k {t | ((i : ℝ) - 1) / 11 ≤ (t : ℝ) ∧ (t : ℝ) ≤ (i : ℝ) / 11}

/-- **T4, `ε₁`** (pp. 345–346). Of the four families in Hagopian's minimum, the skeleton keeps the
one that the chain needs: non-adjacent elevenths stay apart under `ε₁`-homeomorphisms. Add the
others (`ρ(Aᵢ, Bᵢ)`, `ρ(E, π⁻¹(qᵢ))`, `ρ(k⁻¹(0) ∪ k⁻¹(1), k⁻¹[[1/11, 10/11]])`) as the later steps
require them, and record it. -/
theorem hagopian76_eps1 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ ε₁ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) →
      ∀ i ∈ Finset.Icc 1 11, ∀ j ∈ Finset.Icc 1 11, i + 1 < j →
        Disjoint (Metric.thickening ε₁ (toPt (h '' piece k i)))
                 (Metric.thickening ε₁ (toPt (h '' piece k j))) := by
  sorry

/-- **T5, `Wₓ`** (p. 346): "`Wₓ` the open set `{y ∈ M : an ε₁-homeomorphism of M onto M takes x to
y}` (Lemma 2)". -/
def Wset (M : Set Pt) (ε : ℝ) (x : M) : Set M :=
  {y | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε}

/-- **T5, `Gₓ`** (p. 346): "an open set in `{z ∈ R² : ρ(x, z) < ε₁}` such that `Wₓ = M ∩ Gₓ`". -/
theorem exists_Gset (hX : IsHomogeneous M) {ε : ℝ} (hε : 0 < ε) (x : M) :
    ∃ G : Set Pt, IsOpen G ∧ G ⊆ Metric.ball (x : Pt) ε ∧ toPt (Wset M ε x) = M ∩ G := by
  sorry

/-- **T5, the chain `{Gᵢ}` and its refinement `L`; Property 1** (p. 346). "For each `i`
(`1 ≤ i ≤ 11`), let `Gᵢ = ⋃{Gₓ : x ∈ k⁻¹[[(i − 1)/11, i/11]]}`. Using the method described in the
proof of Lemma 8, we define an ordered refinement `L = {Lᵢ : 1 ≤ i ≤ 11}` of the chain
`{Gᵢ : 1 ≤ i ≤ 11}` that follows `E` and is free relative to `M` having the following property:
PROPERTY 1. For each point `y` of `M ∩ ⋃{Lᵢ : 2 ≤ i ≤ 10}`, there exists an `ε₁`-homeomorphism `h` of
`M` onto `M` such that `y` belongs to `h[E]` and `L` follows `h[E]`. (Here the open sets `A` and `B`
in the proof of Lemma 8 are in `G₁ − G₂` and `G₁₁ − G₁₀` respectively.)" *Shape left to you*: the
chain, `L` (from `hagopian76_lemma8_caps`), and Property 1 as printed (with `h[E]` carrying the
transported map, `exists_image_map`). Hagopian's `Gᵢ` are not chosen in collar coordinates; if the
later steps need `π[Gᵢ]` to be collar rectangles, intersect, and record it. -/
theorem hagopian76_property1 : True := by
  sorry

/-- **T9** (p. 346). "Suppose `B` is a component of `M ∩ π⁻¹[D]` that intersects
`⋃{Lᵢ : 4 ≤ i ≤ 8}`. Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is
the image of a subcontinuum of `E` (essential to `R(E)`) under an `ε₁`-homeomorphism. Note that the
chain `L − {L₁, L₁₁}` follows `Cl B`." *Shape left to you*; it needs `D` (T8), so state it for any
open `D` with the properties T8 provides, and record which. -/
theorem hagopian76_T9 : True := by
  sorry

/-- **T11** (p. 347). "Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets both
`π⁻¹(p₃)` and `π⁻¹[I₂]`. Note that `K` separates `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]` in
`π⁻¹[D]`." *Shape left to you.* -/
theorem hagopian76_T11 : True := by
  sorry

/-- **Property 3** (p. 347). "No component of `F ∩ π⁻¹[D]` whose closure meets both
`π⁻¹[⟨p₁, r⟩]` and `π⁻¹[⟨p₅, s⟩]` is contained in an element of the decomposition of `F`." Its proof
uses Lemma 1, Property 1, and Lemmas 2 and 3; `F` is the continuum of T13 (irreducible with respect
to being an extension of `E` away from `k⁻¹(0)` that separates `p` from `f(p)` in `π⁻¹[D]`).
*Shape left to you*: state it for any extension `F` of `E` away from `k⁻¹(0)` with the property it
actually uses, and record what that is. -/
theorem hagopian76_property3 : True := by
  sorry

/-! ## Lemma 7 (restated from `Hagopian76E.lean`) -/

/-- **Lemma 7** (p. 343). -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry

/-- **Lemma 9** (p. 344), collar form (restated from `Hagopian76E.lean`). -/
theorem hagopian76_lemma9 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {u y : unitInterval} (hu0 : 0 < u) (hu1 : u < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (huy : u ≠ y)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    DecompAccessibleC (π '' M) γ u y := by
  sorry

end Thm1

end HPC.Hagopian
