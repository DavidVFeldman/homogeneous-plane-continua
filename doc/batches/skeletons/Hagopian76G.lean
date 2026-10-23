import HPC.Hagopian.Hagopian76F

/-!
# Batch 162 skeleton: Hagopian 1976, Lemma 7 by half-ray density; Lemma 9's proof in collar
# rectangles; T6–T8 (`I₁`, `I₂`, `D`); T9 in full; T11; Property 3

Save as `HPC/Hagopian/Hagopian76G.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76G` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report. When an item here proves
a statement left commented out in `Hagopian76D.lean`, `Hagopian76E.lean` or `Hagopian76F.lean`,
delete the commented-out copies (allowed).

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 343–347. Items marked *shape left to
you* follow report 161 §5; the report must quote the printed sentence each one renders.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Lemma 7 -/

/-- **Half-ray density at any layer.** For a continuum `G` essential to `R(E)`, with its minimal
map `d` and an interior layer `d⁻¹(u)`, each of the two "half-rays" of the composant `R(E)` from
`d⁻¹(u)` is dense in `Cl R(E)`: the union of the extensions of `d⁻¹[[u, 1]]` away from `d⁻¹(u)`,
and that of the extensions of `d⁻¹[[0, u]]` away from `d⁻¹(u)`. For `G = E` this is
`hagopian76_closure_extUnion` and `closure_extUnion_one`. -/
theorem halfray_dense (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hGE : IsEssential k G) {u : unitInterval} (hu0 : 0 < u)
    (hu1 : u < 1) :
    closure (extUnion (layerSet d (Icc u 1)) (layer d u)) = closure (Rset k) ∧
      closure (extUnion (layerSet d (Icc 0 u)) (layer d u)) = closure (Rset k) := by
  sorry

/-- **Lemma 7** (p. 343), restated. Route (commission §1): Hagopian's `F` taken inside the
translate `f hᵢ[R(E)]`, on the side of the layer `f[Uᵢ]` that does not contain `t`, by
`halfray_dense`; then `hagopian76_lemma7_triod`. -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry

/-! ## B. Lemma 9 and the collar geometry -/

/-- **Lemma 9** (p. 344), collar form, restated. -/
theorem hagopian76_lemma9 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {u y : unitInterval} (hu0 : 0 < u) (hu1 : u < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (huy : u ≠ y)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    DecompAccessibleC (π '' M) γ u y := by
  sorry

/-- **T3, T6** (pp. 345–346). "Assume without loss of generality … that each point of `π[E]` is an
end point of an arc segment in `R² − π[M]` below `π[E]` (Lemma 9)"; "It follows from the proof of
Lemma 9 that there exists a horizontal interval `I₁` below `⟨p₁, p₅⟩` in `R² − π[M]` such that the
end points of `I₁` are in `⟨o₁, p₁⟩ ∪ ⟨o₅, p₅⟩` and no point of `π[M]` lies between `I₁` and
`⟨p₁, p₅⟩`." *Shape left to you* (report 161 §5, `hagopian76_lemma9_below`). -/
theorem hagopian76_T6 : True := by
  sorry

/-- **T7** (p. 346). "Let `I₂` be an arc above `⟨p₁, p₅⟩` in `π[(St L) − M]` that is irreducible
between `⟨p₁, q₁⟩` and `⟨p₅, q₅⟩` such that every point of `R²` between `I₂` and `⟨p₁, p₅⟩` is in
`π[St L]`." With the construction that follows ("Let `y` be a point of `M ∩ L₆` that is accessible
from `R² − M` such that `π(y)` is above `π[E]` …"). *Shape left to you.* -/
theorem hagopian76_T7 : True := by
  sorry

/-- **T8** (p. 346). "Let `D` be the bounded complementary domain of
`I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩` in `R²`." With property (D) of `hagopian76_T9` for
`O = π⁻¹[D]`. *Shape left to you.* -/
theorem hagopian76_T8 : True := by
  sorry

/-- **T9 in full** (p. 346): `hagopian76_T9` with (D) supplied by T8, "`Cl B` is the image of a
subcontinuum of `E` (essential to `R(E)`)", and "Note that the chain `L − {L₁, L₁₁}` follows
`Cl B`". *Shape left to you.* -/
theorem hagopian76_T9_full : True := by
  sorry

/-- **T11** (p. 347). "Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets both
`π⁻¹(p₃)` and `π⁻¹[I₂]`. Note that `K` separates `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]` in
`π⁻¹[D]`." *Shape left to you* (the comment in `Hagopian76F.lean`). -/
theorem hagopian76_T11 : True := by
  sorry

/-- **Property 3** (p. 347), in full, with `hagopian76_property3_shift`. *Shape left to you.* -/
theorem hagopian76_property3 : True := by
  sorry

end Thm1

end HPC.Hagopian
