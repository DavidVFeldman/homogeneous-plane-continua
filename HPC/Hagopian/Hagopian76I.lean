import HPC.Hagopian.H76AboveAcc

/-!
# Batch 164: Hagopian 1976, Theorem 1 — the reparametrization; T7 (first part); the positivity in
# `ε₂`. T7 (rest), T8, T9 in full, T11 and Property 3 are open.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 345–347. Skeleton:
`doc/batches/skeletons/Hagopian76I.lean`. The supporting proofs are in `H76Reparam` (item A),
`H76Above` and `H76AboveAcc` (item B, first part). Shape choices (the skeleton left every shape to
us) are recorded at each statement and in `doc/batches/REPORT-batch164.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. The reparametrization -/

omit [CompactSpace M] [ConnectedSpace M] in
/-- **The reparametrization** (p. 345: "Since `M` is homogeneous, we can assume … that
`π[k⁻¹(i/22)] = (i, 0)` for each integer `i`"; OPEN.md, batch 163). For interior parameters `y`,
`z`, an increasing homeomorphism `θ` of `[0, 1]` with `θ y = z` turns `k` into `θ ∘ k`: still minimal
admissible, with the same layers (`θ ∘ k` over `θ t` is `k` over `t`; in particular the same end
sets), the same relation `S` (so the same `π`), `γ ∘ θ⁻¹` in place of `γ` (same range), the
accessible layer over `z`, and every collar `F` of `γ` transported to a collar of `γ ∘ θ⁻¹` with the
same open rectangle. (`θ` is piecewise linear, `plrI`; the collar is `F ∘ (θ⁻¹ × id)`.) -/
theorem hagopian76_reparam {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} {γ : unitInterval → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγ : IsEmbedding γ) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {y z : unitInterval}
    (hy0 : 0 < y) (hy1 : y < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    ∃ θ : unitInterval ≃ₜ unitInterval, StrictMono θ ∧ θ 0 = 0 ∧ θ 1 = 1 ∧ θ y = z ∧
      IsMinimalAdmissible E (fun e => θ (k e)) ∧
      (∀ p q, π p = π q ↔ layerSetoid (fun e => θ (k e)) p q) ∧
      IsEmbedding (fun t => γ (θ.symm t)) ∧
      (∀ t, ∀ x ∈ toPt (layer (fun e => θ (k e)) t), π x = γ (θ.symm t)) ∧
      range (fun t => γ (θ.symm t)) = range γ ∧
      (∀ t, layer (fun e => θ (k e)) (θ t) = layer k t) ∧
      ((∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) →
        ∃ p ∈ layer (fun e => θ (k e)) z, IsAccessibleFrom M (p : Pt)) ∧
      ∀ F : ℝ × ℝ → Pt, IsCollar γ F → ∃ F' : ℝ × ℝ → Pt, IsCollar (fun t => γ (θ.symm t)) F' ∧
        F' '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) = F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
  have hy0' : (0 : ℝ) < y := hy0
  have hy1' : (y : ℝ) < 1 := hy1
  have hz0' : (0 : ℝ) < z := hz0
  have hz1' : (z : ℝ) < 1 := hz1
  set θ := plrI hy0' hy1' hz0' hz1' with hθ
  obtain ⟨h1, h2, h3, h4, h5⟩ := setup_homeo hE hπS hγ hγπ θ
  have hθy : θ y = z := Subtype.ext (plr_self hy0')
  refine ⟨θ, fun s t hst => plr_strictMono hy0' hy1' hz0' hz1' hst,
    Subtype.ext (plr_zero hy0'.le), Subtype.ext (plr_one hy1'), hθy, h1, h2, h3, h4, h5,
    layer_homeo_apply k θ, ?_, fun F hF => ⟨_, hF.plrTransport hy0' hy1' hz0' hz1',
      image_plr_rect hy0' hy1' hz0' hz1'⟩⟩
  rintro ⟨p, hp, hpa⟩
  exact ⟨p, by rw [← hθy, layer_homeo_apply]; exact hp, hpa⟩

/-- **T6 at Hagopian's abscissae** (p. 346, with the reparametrization of p. 345). From an accessible
interior layer, a reparametrized set-up `k'`, `γ'` (same `E`, same `π`, same layers, same end sets,
`range γ' = range γ`) whose accessible layer lies over `1/22`, and a collar `F` of `γ'` such that for
every `[a, b]` with `1/22 < a`, `b < 1` some strip below `γ'([a, b])` misses `π[M]`. Hagopian's `I₁`
below `⟨p₁, p₅⟩` is the case `[a, b] = [3/22, 19/22]` (`hagopian76_I1`). -/
theorem hagopian76_T6_placed (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    ∃ (k' : E → unitInterval) (γ' : unitInterval → Pt),
      IsMinimalAdmissible E k' ∧ (∀ p q, π p = π q ↔ layerSetoid k' p q) ∧ IsEmbedding γ' ∧
      (∀ t, ∀ x ∈ toPt (layer k' t), π x = γ' t) ∧ range γ' = range γ ∧
      (∀ t, ∃ t', layer k' t' = layer k t) ∧ layer k' 0 = layer k 0 ∧ layer k' 1 = layer k 1 ∧
      (∃ p ∈ layer k' ⟨1 / 22, by norm_num, by norm_num⟩, IsAccessibleFrom M (p : Pt)) ∧
      ∃ F : ℝ × ℝ → Pt, IsCollar γ' F ∧ ∀ a b : ℝ, 1 / 22 < a → b < 1 →
        ∃ c > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c) 0)) (π '' M) := by
  set z : unitInterval := ⟨1 / 22, by norm_num, by norm_num⟩ with hz
  have hz0 : 0 < z := by show (0 : ℝ) < 1 / 22; norm_num
  have hz1 : z < 1 := by show (1 / 22 : ℝ) < 1; norm_num
  obtain ⟨θ, -, hθ0, hθ1, -, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    hagopian76_reparam hE hπS hγ hγπ hy0 hy1 hz0 hz1
  obtain ⟨F, hF, hstrip⟩ := hagopian76_T6 hX hi h1 hπ h2 h3 h4 hz0 hz1 (h7 hacc)
  refine ⟨_, _, h1, h2, h3, h4, h5, fun t => ⟨θ t, h6 t⟩, by rw [← h6 0, hθ0],
    by rw [← h6 1, hθ1], h7 hacc, F, hF, fun a b ha hb => hstrip a b (by linarith) hb ?_⟩
  rintro ⟨h, -⟩
  have h' : a ≤ 1 / 22 := h
  linarith

/-- **Hagopian's `I₁`** (p. 346, T6: "there exists a horizontal interval `I₁` below `⟨p₁, p₅⟩` in
`R² − π[M]` such that the end points of `I₁` are in `⟨o₁, p₁⟩ ∪ ⟨o₅, p₅⟩` and no point of `π[M]` lies
between `I₁` and `⟨p₁, p₅⟩`"), in the collar of `hagopian76_T6_placed`, with `pᵢ = γ'((2i + 1)/22)`:
the strip below `γ'([3/22, 19/22])` misses `π[M]`; `I₁` is its side at height `−c/2`. -/
theorem hagopian76_I1 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγ : IsEmbedding γ)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {y : unitInterval} (hy0 : 0 < y) (hy1 : y < 1)
    (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    ∃ (k' : E → unitInterval) (γ' : unitInterval → Pt),
      IsMinimalAdmissible E k' ∧ (∀ p q, π p = π q ↔ layerSetoid k' p q) ∧ IsEmbedding γ' ∧
      (∀ t, ∀ x ∈ toPt (layer k' t), π x = γ' t) ∧ range γ' = range γ ∧
      ∃ F : ℝ × ℝ → Pt, IsCollar γ' F ∧
        ∃ c > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c) 0)) (π '' M) := by
  obtain ⟨k', γ', h1, h2, h3, h4, h5, -, -, -, -, F, hF, hs⟩ :=
    hagopian76_T6_placed hX hi hE hπ hπS hγ hγπ hy0 hy1 hacc
  exact ⟨k', γ', h1, h2, h3, h4, h5, F, hF, hs _ _ (by norm_num) (by norm_num)⟩

/-! ## B. T7, first part: `π[M]` above, and an accessible point above -/

/-- **T7, the accessible point above** (p. 346: "Let `y` be a point of `M ∩ L₆` that is accessible
from `R² − M` such that `π(y)` is above `π[E]`"; commission 164 §1 B.1). In the collar of T6: for
every `[a, b] ⊆ (0, 1)` (`a < b`) avoiding the accessible parameter and every height `c > 0`, the
window `F((a, b) × (0, c))` above `γ((a, b))` meets `π[M]`, and contains `π(x)` for some point `x` of
`M − E` accessible from `R² − M`. (Shape: the window replaces "`M ∩ L₆`"; any link of a chain
following `E` contains such a window over a subinterval of its parameters.) -/
theorem hagopian76_T7_accessible (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγ : IsEmbedding γ) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {y : unitInterval}
    (hy0 : 0 < y) (hy1 : y < 1) (hacc : ∃ p ∈ layer k y, IsAccessibleFrom M (p : Pt)) :
    ∃ F : ℝ × ℝ → Pt, IsCollar γ F ∧
      (∀ a b : ℝ, 0 < a → b < 1 → (y : ℝ) ∉ Icc a b →
        ∃ c > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c) 0)) (π '' M)) ∧
      ∀ a b : ℝ, 0 < a → a < b → b < 1 → (y : ℝ) ∉ Icc a b → ∀ c > 0,
        (F '' (Ioo a b ×ˢ Ioo 0 c) ∩ π '' M).Nonempty ∧
        ∃ x ∈ M, x ∉ toPt E ∧ IsAccessibleFrom M x ∧ π x ∈ F '' (Ioo a b ×ˢ Ioo 0 c) := by
  obtain ⟨F, hF, hstrip⟩ := hagopian76_T6 hX hi hE hπ hπS hγ hγπ hy0 hy1 hacc
  refine ⟨F, hF, hstrip, fun a b ha hab hb hy c hc => ⟨?_, ?_⟩⟩
  · exact M_meets_above hi hE hπ.continuous hπS hγπ hF ha hab hb (hstrip a b ha hb hy) hc
  · exact exists_accessible_above hi hE hπ hπS hγπ hF ha hab hb (hstrip a b ha hb hy) hc

/-! ## D (part). The positivity in `ε₂` -/

omit [ConnectedSpace M] in
/-- **`ρ(M, π⁻¹[I]) > 0`** for a closed `I` missing `π[M]` (p. 346: "Define `ε₂` to be the minimum
of `ε₁` and `ρ(M, π⁻¹[I₁ ∪ I₂])`"; commission §3 check 5). Applies to `I₁` (closed, and missing
`π[M]` by `hagopian76_I1`), and to `I₁ ∪ I₂` once `I₂` is constructed. -/
theorem hagopian76_eps2_pos {π : Pt → Pt} (hπc : Continuous π) {I : Set Pt} (hI : IsClosed I)
    (hIM : Disjoint I (π '' M)) : ∃ δ > 0, ∀ m ∈ M, ∀ z, π z ∈ I → δ ≤ dist m z :=
  exists_pos_dist_preimage hπc hI hIM

/-! ## Open items (commission 164 §1 B–F)

The following are open; the obstructions are in `OPEN.md` (batch 164) and in
`doc/batches/REPORT-batch164.md` §1.

* T7, T8, T9 in full, T11: proved in batch 165 (`Hagopian76J.lean`: `hagopian76_T7`, `hagopian76_T8`,
  `hagopian76_T9_full`, `hagopian76_T11`).

* `hagopian76_property3` (Property 3): proved in batch 173, `Hagopian76R.lean`.
-/

end Thm1

end HPC.Hagopian
