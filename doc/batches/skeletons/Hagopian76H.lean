import HPC.Hagopian.Hagopian76G

/-!
# Batch 163 skeleton: Hagopian 1976, the collar geometry — an adapted collar; "no `π[M]` just
# below `π[E]`" (the core of Lemma 9's proof); Lemma 9; T3 and T6

Save as `HPC/Hagopian/Hagopian76H.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76H` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes
may be adjusted, each change recorded at the statement and in the report. When an item here proves
a statement left commented out in an earlier `Hagopian76*.lean`, delete the commented-out copy.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 344–346. The route is commission 163 §1:
Lemma 9's argument run for an arbitrary point of `M − E` just below `π[E]`, with the collar in place
of "`π[E]` horizontal" and an open rectangle of the collar in place of Theorem 28's simple domain.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## A. An adapted collar -/

/-- **A collar in which a given transverse arc is vertical** (Hagopian p. 345: "We assume without
loss of generality that `π[E]` is lying on a horizontal line `B` in `R²` and `π[I − {y}]` is below
`B` on a vertical line"). `β` is an arc ending at the interior point `γ y` and meeting `range γ` only
there. From `plane_schoenflies₂` and the construction of `exists_collar`. -/
theorem exists_collar_adapted {γ : unitInterval → Pt} (hγ : IsEmbedding γ) {y : unitInterval}
    (hy0 : 0 < y) (hy1 : y < 1) {b : Pt} {β : Set Pt} (hβ : TArc b (γ y) β)
    (hβγ : β ∩ range γ = {γ y}) :
    ∃ F : ℝ × ℝ → Pt, IsCollar γ F ∧ ∃ c > 0, F '' ({(y : ℝ)} ×ˢ Icc (-c) 0) ⊆ β := by
  sorry

section Core

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## B. The core of Lemma 9 -/

/-- **No point of `π[M]` just below `π[E]`, away from the accessing vertical** (the argument of
pp. 344–345, run for an arbitrary point; commission 163 §1). Let `F` be a collar of `γ` in which the
vertical below `γ y` (`0 < y < 1`) meets `π[M]` only at its foot. Then for every closed interval
`[a, b] ⊆ (0, 1)` not containing `y`, some open strip below `γ([a, b])` in collar coordinates misses
`π[M]`. -/
theorem no_M_below (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1)
    (hvert : ∃ c > 0, F '' ({(y : ℝ)} ×ˢ Ico (-c) 0) ∩ π '' M = ∅)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hy : (y : ℝ) ∉ Icc a b) :
    ∃ c > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c) 0)) (π '' M) := by
  sorry

/-! ## C. Lemma 9 -/

/-- **Lemma 9** (p. 344), collar form (restated from `Hagopian76G.lean`). From `exists_collar_adapted`
applied to `π[I]` (`π` is injective on `I`, which meets `E` only at its end) and `no_M_below` on a
small interval about `u`. -/
theorem hagopian76_lemma9 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {u y : unitInterval} (hu0 : 0 < u) (hu1 : u < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (huy : u ≠ y)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    DecompAccessibleC (π '' M) γ u y := by
  sorry

/-! ## D. T3 and T6 -/

/-- **T3, T6** (pp. 345–346): "each point of `π[E]` is an end point of an arc segment in
`R² − π[M]` below `π[E]` (Lemma 9)"; "It follows from the proof of Lemma 9 that there exists a
horizontal interval `I₁` below `⟨p₁, p₅⟩` in `R² − π[M]` such that the end points of `I₁` are in
`⟨o₁, p₁⟩ ∪ ⟨o₅, p₅⟩` and no point of `π[M]` lies between `I₁` and `⟨p₁, p₅⟩`." In collar
coordinates: given an accessible interior layer `k⁻¹(y)`, there is a collar and, for every
`[a, b] ⊆ (0, 1)` avoiding `y`, a strip below `γ([a, b])` free of `π[M]`. Hagopian's
`⟨p₁, p₅⟩` is to be placed away from the accessible layer (reparametrize `k` if necessary; record
it). -/
theorem hagopian76_T6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    ∃ F : ℝ × ℝ → Pt, IsCollar γ F ∧ ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 → (y : ℝ) ∉ Icc a b →
      ∃ c > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c) 0)) (π '' M) := by
  sorry

end Core

end HPC.Hagopian
