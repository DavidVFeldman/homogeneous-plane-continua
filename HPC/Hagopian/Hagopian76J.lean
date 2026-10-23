import HPC.Hagopian.H76T9Full

/-!
# Batch 165 skeleton: Hagopian 1976, Theorem 1 — T7 (`I₂`) by a crossing argument; link control;
# T8 (`D`); T9 in full; T11; Property 3; then T12–T17 and the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 345–349. Hagopian's points are
`oᵢ = (4i − 1, −1)`, `pᵢ = (4i − 1, 0)`, `qᵢ = (4i − 1, 1)` (`1 ≤ i ≤ 5`), so in the parameter of
`hagopian76_T6_placed` the abscissae of `p₁, …, p₅` are `3/22, 7/22, 11/22, 15/22, 19/22`.
The route for T7 is commission 165 §1. Skeleton as delivered: `doc/batches/skeletons/Hagopian76J.lean`.

Supporting files: `H76Crossing` (A.3), `H76NoHair` (A.1, A.2), `H76T7` (A.4), `H76Thin` (B),
`H76T9Full` (C, D). Shape changes are recorded at each statement and in
`doc/batches/REPORT-batch165.md`. Property 3, T12–T17 and the assembly are open (commented out at
the end, obstructions in `OPEN.md`).

Lean indices of links: Hagopian's `Lᵢ` (`1 ≤ i ≤ 11`) is `L (i − 1)`; so `L₂`, `L₁₀` are `L 1`, `L 9`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## A.3 The crossing lemma (plane topology, in collar coordinates) -/

/-- **A thin rectangle is crossed from left to right** when no connected part of `K` joins its
bottom to its top. `K` is closed, lies in the rectangle `[a, b] × [0, c]` and contains its bottom
edge. Then there is an arc in the rectangle, missing `K`, from the left edge to the right edge and
meeting the two side edges only at its ends. (Commission 165 §1, step 3, first route: clopen split,
Janiszewski for `K_b ∪` lower frame and `K_t ∪` upper frame, an arc in the complement, cut at the
last visit to the left edge and the next visit to the right edge. Statement unchanged.) -/
theorem rect_crossing {a b c : ℝ} (hab : a < b) (hc : 0 < c) {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hKR : K ⊆ Icc a b ×ˢ Icc 0 c) (hbot : Icc a b ×ˢ {0} ⊆ K)
    (hno : ∀ C ⊆ K, IsConnected C → (C ∩ Icc a b ×ˢ {c}).Nonempty →
      (C ∩ Icc a b ×ˢ {0}).Nonempty → False) :
    ∃ (r s : ℝ × ℝ) (I : Set (ℝ × ℝ)), TArc r s I ∧ I ⊆ (Icc a b ×ˢ Ioc 0 c) \ K ∧
      r.1 = a ∧ s.1 = b ∧ I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s} :=
  rect_crossing_aux hab hc hK hKR hbot hno

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A.1 No hair on `E` -/

/-- **No continuum leaves `E` through its middle.** A continuum of `M` that meets `E` and misses
both end sets of `E` lies in `E`. From absorption (`subset_extUnion_of_meets`, once with `k` and
once with `σ ∘ k`; `E` is an extension of itself away from either end set) and
`ext_inter_subset`. (Statement unchanged.) -/
theorem hagopian76_no_hair (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {Q : Set M}
    (hQ : Fold.Q78.IsContinuum Q) (hQE : (Q ∩ E).Nonempty) (h0 : Disjoint Q (layer k 0))
    (h1 : Disjoint Q (layer k 1)) : Q ⊆ E :=
  no_hair_aux hX hi hE hQ hQE h0 h1

/-! ## A.2 Preimages of continua under `π` -/

omit [ConnectedSpace M] in
/-- **`π` pulls continua of `π[M]` back to continua of `M`.** `π` restricted to `M` is a closed map
(compactness) with connected fibres (layers and points). Mathlib's
`IsPreconnected.preimage_of_isClosedMap` needs an injective map, so the fibre version is proved
here (`isPreconnected_preimage_of_fibres`). (Statement unchanged.) -/
theorem preimage_pi_isContinuum {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    {C : Set Pt} (hC : Fold.Q78.IsContinuum C) (hCM : C ⊆ π '' M) :
    Fold.Q78.IsContinuum {x : M | π (x : Pt) ∈ C} :=
  preimage_pi_isContinuum_aux hE hπ.continuous hπS hC hCM

/-! ## A.4 T7 -/

/-- **T7** (p. 346). "Let `I₂` be an arc above `⟨p₁, p₅⟩` in `π[(St L) − M]` that is irreducible
between `⟨p₁, q₁⟩` and `⟨p₅, q₅⟩` such that every point of `R²` between `I₂` and `⟨p₁, p₅⟩` is in
`π[St L]`." Collar form, for any open `U ⊇ E` (to be used with `U = St L`) and any `[a, b] ⊆ (0, 1)`:
a thin closed collar rectangle over `[a, b]` lies in `π[U]`, and for every smaller height `c'` an arc
`I₂` in the rectangle of height `c'`, missing `π[M]`, joins the two side edges above the axis and
meets them only at its ends. Neither `h[E]` nor accessibility is used (commission 165 §1).

*Shape change:* the skeleton's hypothesis `hγ : IsEmbedding γ` is dropped (unused; `IsCollar γ F`
already makes `γ` an embedding). -/
theorem hagopian76_T7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) {U : Set Pt} (hU : IsOpen U)
    (hEU : toPt E ⊆ U) :
    ∃ c > 0, c ≤ 1 ∧ F '' (Icc a b ×ˢ Icc 0 c) ⊆ π '' U ∧
      ∀ c', 0 < c' → c' ≤ c → ∃ (r s : Pt) (I₂ : Set Pt), TArc r s I₂ ∧
        I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c') ∧ Disjoint I₂ (π '' M) ∧
        I₂ ∩ F '' (({a, b} : Set ℝ) ×ˢ Icc 0 c') = {r, s} ∧
        r ∈ F '' (({a} : Set ℝ) ×ˢ Ioc 0 c') ∧ s ∈ F '' (({b} : Set ℝ) ×ˢ Ioc 0 c') :=
  hagopian76_T7_aux hX hi hE hπ hπS hγπ hF ha hab hb hU hEU

/-! ## B. Link control -/

/- `EndCtl` (the skeleton's definition) is moved unchanged to `H76Thin.lean`, so that
`link_control_aux` can use it. -/

omit [CompactSpace M] [ConnectedSpace M] in
/-- **`ε₁` with end control exists** (as `exists_isEps1`, with two more compact pairs; `ε₁` is the
minimum of the old `ε₁` and a quarter of the two new distances). (Statement unchanged.) -/
theorem exists_isEps1_endCtl {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ ε₁, IsEps1 k ε₁ ∧ EndCtl k ε₁ :=
  exists_isEps1_endCtl_aux hE

/-- **Link control in a thin strip** (shape left to the batch). For an ordered refinement `L` of
`chainG k ε₁` (the chain `G` of T5) covering `E`, at an `ε₁` with `EndCtl`, and any `0 < η ≤ ε₁`: a
thin enough closed collar strip `R` over `[3/22, 19/22]` lies in `π[St L]`; every point `x` of `M`
with `π(x) ∈ R` lies in some link, only in links `L₂, …, L₁₀`, and if `x ∈ Lⱼ` (Lean index `j`) the
abscissa of `π(x)` lies in `((j − 1)/11 − η, (j + 2)/11 + η)`. (`L₁`, `L₁₁` are excluded by
`EndCtl`, the abscissa bound comes from `IsEps1.sep`; both through `pi_thin_near_layer`.) -/
theorem hagopian76_link_control (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLo : ∀ j, IsOpen (L j))
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j) {η : ℝ} (hη : 0 < η)
    (hηε : η ≤ ε₁) :
    ∃ c > 0, c ≤ 1 ∧ F '' (Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c) ⊆ π '' (⋃ j, L j) ∧
      ∀ x : M, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c) →
        ∃ z ∈ Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c, π (x : Pt) = F z ∧
          (∃ j : Fin 11, (x : Pt) ∈ L j) ∧
          ∀ j : Fin 11, (x : Pt) ∈ L j → 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧
            ((j : ℝ) - 1) / 11 - η < z.1 ∧ z.1 < ((j : ℝ) + 2) / 11 + η :=
  strip_in_links hX hi hE he hend hπ hπS hγπ hF hLo hEL hLG hη hηε

/-! ## C. T8, T9 -/

/-- **T8, property (D)** (p. 346). "Define `r` and `s` to be the end points of `I₂` belonging to
`⟨p₁, q₁⟩` and `⟨p₅, q₅⟩` respectively. Let `D` be the bounded complementary domain of
`I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩` in `R²`."

*Shape (left to the batch):* the property of `D` that T9 uses, property (D) of `hagopian76_T9`
("every point of `M ∩ Cl π⁻¹[D]` lies in one of `L₂, …, L₁₀`"), for **every** `O ⊆ π⁻¹[R]`, where
`R` is a thin closed collar strip over `[3/22, 19/22]` lying in `π[St L]`. Hagopian's `D`, built
from an `I₂` of `hagopian76_T7` of height at most that of `R`, lies in `R` (it is the bounded
domain of a Jordan curve in `R`); that last inclusion, and `D` itself as a Jordan domain, are not
formalized (the Jordan curve theorem for this curve is not used anywhere below). -/
theorem hagopian76_T8 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLo : ∀ j, IsOpen (L j))
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j) :
    ∃ c > 0, c ≤ 1 ∧ F '' (Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c) ⊆ π '' (⋃ j, L j) ∧
      ∀ O : Set Pt, O ⊆ π ⁻¹' (F '' (Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c)) →
        ∀ x : M, (x : Pt) ∈ closure O →
          ∃ j : Fin 11, 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧ (x : Pt) ∈ L j := by
  obtain ⟨c, hc, hc1, hU, hlink⟩ :=
    hagopian76_link_control hX hi hE he hend hπ hπS hγπ hF hLo hEL hLG he.pos le_rfl
  refine ⟨c, hc, hc1, hU, fun O hO x hx => ?_⟩
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_restrict.2 hF.1.continuous
  have hcomp : IsCompact (F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c)) :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn (hFc.mono
      fun z ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)
  have hxR : (x : Pt) ∈ π ⁻¹' (F '' (Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c)) :=
    closure_minimal hO (hcomp.isClosed.preimage hπ.continuous) hx
  obtain ⟨_z, _hz, _hxz, ⟨j, hj⟩, hb⟩ := hlink x hxR
  obtain ⟨h1, h9, -⟩ := hb j hj
  exact ⟨j, h1, h9, hj⟩

/-- **T9 in full** (p. 346). "Suppose `B` is a component of `M ∩ π⁻¹[D]` that intersects
`⋃{Lᵢ : 4 ≤ i ≤ 8}`. Since `M` is atriodic, it follows from Property 1 and Lemma 5 that `Cl B` is
the image of a subcontinuum of `E` (essential to `R(E)`) under an `ε₁`-homeomorphism."

*Shape (left to the batch):* for the chain `L` of `hagopian76_property1` at an `ε₁` with `EndCtl`,
there is a thin open collar strip `R` over `[3/22, 19/22]` such that for every connected `B ⊆ M` with
`π[B] ⊆ R` (in particular a component of `M ∩ π⁻¹[D]` for any `D ⊆ R` above the axis) through a
point of one of `L₂, …, L₁₀`: `Cl B` misses `E` (`hagopian76_no_hair`), and the conclusions of
`hagopian76_T9` hold — `Cl B ⊆ h[E]` for an `ε₁`-homeomorphism `h`, `h⁻¹[Cl B]` is a subcontinuum of
`E`, essential to `R(E)` whenever `Cl B` meets links `Lₐ`, `L_c` with `c ≥ a + 3`. Open: "the chain
`L − {L₁, L₁₁}` follows `Cl B`" (not needed by the later steps in the form stated here, see
report 165 §2.C). -/
theorem hagopian76_T9_full (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      ∀ y ∈ B, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
        Disjoint (closure B) E ∧
        ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ closure B ⊆ h '' E ∧
          Fold.Q78.IsContinuum (h ⁻¹' closure B) ∧ h ⁻¹' closure B ⊆ E ∧
          ∀ a c : Fin 11, (a : ℕ) + 3 ≤ c → (toPt (closure B) ∩ L a).Nonempty →
            (toPt (closure B) ∩ L c).Nonempty → IsEssential k (h ⁻¹' closure B) := by
  obtain ⟨c, hc, hc1, -, hD⟩ :=
    hagopian76_T8 hX hi hE he hend hπ hπS hγπ hF hLch.isOpen hEL hLG
  refine ⟨c, hc, hc1, fun B hBc hB y hyB i hi1 hi9 hyL => ⟨?_, ?_⟩⟩
  · exact closure_disjoint_E_of_above hX hi hE hπ.continuous hγπ hF
      (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (19 / 22 : ℝ) < 1) hc1 hBc hB
  · set O : Set Pt := π ⁻¹' (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) with hOd
    have hOR : O ⊆ π ⁻¹' (F '' (Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c)) :=
      preimage_mono (image_mono (Set.prod_mono subset_rfl Ioc_subset_Icc_self))
    have hBO : toPt B ⊆ O := by
      rintro _ ⟨x, hx, rfl⟩; exact hB x hx
    exact hagopian76_T9 hX hi hE he hLch hLG hP1 (fun x hx => hD O hOR x hx) hBc hBO hyB hi1 hi9
      hyL

/-! ## D. T11 -/

/-- **T11** (p. 347). "Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets both
`π⁻¹(p₃)` and `π⁻¹[I₂]`. Note that `K` separates `L₂ ∩ M ∩ π⁻¹[D]` from `L₁₀ ∩ M ∩ π⁻¹[D]` in
`π⁻¹[D]`." `p₃` is at abscissa `11/22`.

*Shape (left to the batch), with one change:* `K` is replaced by the whole of
`π⁻¹[D ∩ ⟨p₃, q₃⟩]`, for every `D` in a thin open collar strip over `[3/22, 19/22]` (in particular
Hagopian's `D`): no connected subset of `π⁻¹[D]` missing `π⁻¹[⟨p₃, q₃⟩]` contains a point of
`M ∩ L₂` and a point of `M ∩ L₁₀` (Lean `L 1`, `L 9`). Whether the single component `K` separates
is left open: if `I₂` doubles back over `p₃`, a region of `D` above the first crossing of the
vertical can reach both sides (report 165 §2.D, ledger check 165.5). -/
theorem hagopian76_T11 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLo : ∀ j, IsOpen (L j))
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ D : Set Pt, D ⊆ F '' (Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c) →
      ∀ S ⊆ π ⁻¹' D \ π ⁻¹' (F '' (({11 / 22} : Set ℝ) ×ˢ Ioo 0 c)), IsPreconnected S →
        ∀ x ∈ S, ∀ y ∈ S, x ∈ M → y ∈ M → x ∈ L 1 → y ∈ L 9 → False := by
  obtain ⟨c, hc, hc1, h⟩ := T11_aux hX hi hE he hend hπ hπS hγπ hF hLo hEL hLG
  refine ⟨c, hc, hc1, fun D hD S hS hSc => h S hSc (fun p hp => hD (hS hp).1) ?_⟩
  exact disjoint_left.2 fun p hp => (hS hp).2

end Thm1

/-! ## E, F. Property 3, T12–T17 and the assembly (open)

The obstructions are in `OPEN.md` (batch 165) and in `doc/batches/REPORT-batch165.md` §2.E–F.

-- `hagopian76_property3` (Property 3, this shape): proved in batch 174, `Hagopian76S.lean` (`hagopian76_property3_components`).

**OPEN (T12, T13; T15, T16 = Property 4, T17; `hagopian76_theorem1 : Hagopian76Thm1`).** Wait on
Property 3. Shapes of report 164 §5 stand; with this batch the hypotheses `hI₂` (T7), `hDL`
(property (D), T8) and `hL2`, `hL10` (link control) are theorems, `hD` (the Jordan domain) is not.
Pointer (batch 166): `hD` is now `hagopian76_D` (`Hagopian76K.lean`).
-/

end HPC.Hagopian
