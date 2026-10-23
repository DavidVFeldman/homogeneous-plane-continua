import HPC.Hagopian.Hagopian76I

/-!
# Batch 165 skeleton: Hagopian 1976, Theorem 1 — T7 (`I₂`) by a crossing argument; link control;
# T8 (`D`); T9 in full; T11; Property 3; then T12–T17 and the assembly

Save as `HPC/Hagopian/Hagopian76J.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian76J` at the end of `HPC.lean`. Add imports if a lemma cited below is
not in the import closure of `Hagopian76I`. Every `sorry` is a work item. Shapes may be adjusted,
each change recorded at the statement and in the report. Items stated as `True` are *shape left to
you*. Unproved items are commented out with an `OPEN` note, as before.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 345–349. Hagopian's points are
`oᵢ = (4i − 1, −1)`, `pᵢ = (4i − 1, 0)`, `qᵢ = (4i − 1, 1)` (`1 ≤ i ≤ 5`), so in the parameter of
`hagopian76_T6_placed` the abscissae of `p₁, …, p₅` are `3/22, 7/22, 11/22, 15/22, 19/22`.
The route for T7 is commission 165 §1.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## A.3 The crossing lemma (plane topology, in collar coordinates) -/

/-- **A thin rectangle is crossed from left to right** when no connected part of `K` joins its
bottom to its top. `K` is closed, lies in the rectangle `[a, b] × [0, c]` and contains its bottom
edge. Then there is an arc in the rectangle, missing `K`, from the left edge to the right edge and
meeting the two side edges only at its ends. (The dual of "a connected subset of `K` joins top and
bottom"; commission 165 §1, step 3, has two routes.) -/
theorem rect_crossing {a b c : ℝ} (hab : a < b) (hc : 0 < c) {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hKR : K ⊆ Icc a b ×ˢ Icc 0 c) (hbot : Icc a b ×ˢ {0} ⊆ K)
    (hno : ∀ C ⊆ K, IsConnected C → (C ∩ Icc a b ×ˢ {c}).Nonempty →
      (C ∩ Icc a b ×ˢ {0}).Nonempty → False) :
    ∃ (r s : ℝ × ℝ) (I : Set (ℝ × ℝ)), TArc r s I ∧ I ⊆ (Icc a b ×ˢ Ioc 0 c) \ K ∧
      r.1 = a ∧ s.1 = b ∧ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s} := by
  sorry

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A.1 No hair on `E` -/

/-- **No continuum leaves `E` through its middle.** A continuum of `M` that meets `E` and misses
both end sets of `E` lies in `E`. From absorption (`subset_extUnion_of_meets`, once with `k` and
once with `σ ∘ k`; `E` is an extension of itself away from either end set) and
`ext_inter_subset`. -/
theorem hagopian76_no_hair (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {Q : Set M}
    (hQ : Fold.Q78.IsContinuum Q) (hQE : (Q ∩ E).Nonempty) (h0 : Disjoint Q (layer k 0))
    (h1 : Disjoint Q (layer k 1)) : Q ⊆ E := by
  sorry

/-! ## A.2 Preimages of continua under `π` -/

/-- **`π` pulls continua of `π[M]` back to continua of `M`.** `π` restricted to `M` is a closed map
(compactness) with connected fibres (layers and points). Mathlib:
`IsPreconnected.preimage_of_isClosedMap`. -/
theorem preimage_pi_isContinuum {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {C : Set Pt} (hC : Fold.Q78.IsContinuum C) (hCM : C ⊆ π '' M) :
    Fold.Q78.IsContinuum {x : M | π (x : Pt) ∈ C} := by
  sorry

/-! ## A.4 T7 -/

/-- **T7** (p. 346). "Let `I₂` be an arc above `⟨p₁, p₅⟩` in `π[(St L) − M]` that is irreducible
between `⟨p₁, q₁⟩` and `⟨p₅, q₅⟩` such that every point of `R²` between `I₂` and `⟨p₁, p₅⟩` is in
`π[St L]`." Collar form, for any open `U ⊇ E` (to be used with `U = St L`) and any `[a, b] ⊆ (0, 1)`:
a thin closed collar rectangle over `[a, b]` lies in `π[U]`, and for every smaller height `c'` an arc
`I₂` in the rectangle of height `c'`, missing `π[M]`, joins the two side edges above the axis and
meets them only at its ends. Neither `h[E]` nor accessibility is used (commission 165 §1). -/
theorem hagopian76_T7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) {U : Set Pt} (hU : IsOpen U)
    (hEU : toPt E ⊆ U) :
    ∃ c > 0, c ≤ 1 ∧ F '' (Icc a b ×ˢ Icc 0 c) ⊆ π '' U ∧
      ∀ c', 0 < c' → c' ≤ c → ∃ (r s : Pt) (I₂ : Set Pt), TArc r s I₂ ∧
        I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c') ∧ Disjoint I₂ (π '' M) ∧
        I₂ ∩ F '' (({a, b} : Set ℝ) ×ˢ Icc 0 c') = {r, s} ∧
        r ∈ F '' (({a} : Set ℝ) ×ˢ Ioc 0 c') ∧ s ∈ F '' (({b} : Set ℝ) ×ˢ Ioc 0 c') := by
  sorry

/-! ## B. Link control -/

/-- **End control for `ε₁`** (commission 165 §1, item B): the end links `L₁`, `L₁₁` stay away from
the parameters over `⟨p₁, p₅⟩`. A further term of the minimum defining `ε₁`. -/
def EndCtl {E : Set M} (k : E → unitInterval) (ε₁ : ℝ) : Prop :=
  (∀ x ∈ layerSet k {t : unitInterval | (t : ℝ) ≤ 2 / 22},
    ∀ y ∈ layerSet k {t : unitInterval | 3 / 22 ≤ (t : ℝ)}, 4 * ε₁ ≤ dist x y) ∧
  (∀ x ∈ layerSet k {t : unitInterval | 20 / 22 ≤ (t : ℝ)},
    ∀ y ∈ layerSet k {t : unitInterval | (t : ℝ) ≤ 19 / 22}, 4 * ε₁ ≤ dist x y)

/-- **`ε₁` with end control exists** (as `exists_isEps1`, with two more compact pairs). -/
theorem exists_isEps1_endCtl {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ ε₁, IsEps1 k ε₁ ∧ EndCtl k ε₁ := by
  sorry

/-- **Link control in a thin strip** (shape left to you). For the chain `L` of
`hagopian76_property1` at an `ε₁` with `EndCtl`, and a thin enough closed collar rectangle `R` over
`[3/22, 19/22]`: every point of `M` with `π`-image in `R` lies in one of `L₂, …, L₁₀`; and a point
of `Lⱼ` with `π`-image in `R` has abscissa within the parameters of the pieces adjacent to piece
`j` (from `IsEps1.sep`). Used for property (D) and for T11. -/
theorem hagopian76_link_control : True := by
  sorry

/-! ## C. T8, T9 -/

/-- **T8** (p. 346). "Define `r` and `s` to be the end points of `I₂` belonging to `⟨p₁, q₁⟩` and
`⟨p₅, q₅⟩` respectively. Let `D` be the bounded complementary domain of
`I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩` in `R²`." With `D` inside the collar rectangle, and property
(D) of `hagopian76_T9`. *Shape left to you.* -/
theorem hagopian76_T8 : True := by
  sorry

/-- **T9 in full** (p. 346). "Suppose `B` is a component of `M ∩ π⁻¹[D]` that intersects
`⋃{Lᵢ : 4 ≤ i ≤ 8}`. Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is
the image of a subcontinuum of `E` (essential to `R(E)`) under an `ε₁`-homeomorphism. Note that the
chain `L − {L₁, L₁₁}` follows `Cl B`." With `ε₂` (p. 346) and Property 2 at `ε₂`.
*Shape left to you.* -/
theorem hagopian76_T9_full : True := by
  sorry

/-! ## D, E. T11, Property 3 -/

/-- **T11** (p. 347). "Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets both
`π⁻¹(p₃)` and `π⁻¹[I₂]`. Note that `K` separates `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]` in
`π⁻¹[D]`." `p₃` is at abscissa `11/22`. *Shape left to you.* -/
theorem hagopian76_T11 : True := by
  sorry

/-- **Property 3** (p. 347), in full, for any extension `F` of `E` away from `k⁻¹(0)`, with
`hagopian76_property3_shift`. *Shape left to you.* -/
theorem hagopian76_property3 : True := by
  sorry

/-! ## F. T12–T17 and the assembly (if reached; shapes of report 164 §5) -/

/-- **T12, T13** (p. 347). *Shape left to you.* -/
theorem hagopian76_T12_T13 : True := by
  sorry

/-- **T15, T16 (Property 4), T17** (pp. 347–349). *Shape left to you.* -/
theorem hagopian76_T15_T17 : True := by
  sorry

end Thm1

/-- **Theorem 1** (p. 345). The assembly. -/
theorem hagopian76_theorem1 : Hagopian76Thm1 := by
  sorry

end HPC.Hagopian
