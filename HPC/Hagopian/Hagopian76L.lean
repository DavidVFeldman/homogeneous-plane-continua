import HPC.Hagopian.H76CrossEss

/-!
# Batch 167 skeleton: Hagopian 1976, Theorem 1 — crossing translates; T12; Property 3; T13; then
# T15–T17 and the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 167 §1.
Set-up: `hagopian76_D` over `[a, b]` (Hagopian: `[3/22, 19/22]`; `D = F[D′]`, low strip of height
`c₀`), `hagopian76_K0` over `t₀` (Hagopian: `11/22`); `0 < a′ < a`, `b < b′ < 1`. Skeleton as
delivered: `doc/batches/skeletons/Hagopian76L.lean`.

Supporting files: `H76Translate` (boundary bumping for components, uniform collar coordinates),
`H76TranslateMain` (Lemma T), `H76K0Dense` (Lemma T′, the crossing `p`-components of T12),
`H76CrossEss` (crossing continua over the thin strip are essential; T12 (1)–(2)). Shape changes are
recorded at each statement and in `doc/batches/REPORT-batch167.md`. Items left open are commented
out at the end, with the obstructions in `OPEN.md`.

The hypotheses on `I₂`, `D′`, `F[D′]` below are exactly the conclusions of `hagopian76_D` (with
`I₂` from `hagopian76_T7`); the hypothesis `hbelow` is the one `hagopian76_D` takes.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Crossing translates -/

/-- **Lemma T** (commission 167 §1). `D = F[D′]` over `[a, b]`, `0 < a′ < a`, `b < b′ < 1`.
There is a height `c₀ > 0` with the low strip `(a, b) × (0, c₀)` inside `D′` and below the ends
`r₂`, `s₂` of `I₂`, and for every `ζ > 0` and `η > 0` a `δ > 0` such that for every `x ∈ E` with
`k(x) ∈ [a + ζ, b − ζ]` and every `δ`-homeomorphism `h` of `M` with `h(x) ∉ E` and `π(h(x))` above
the axis (in `F[[0, 1] × (0, 1]]`):
1. `Q = h[k⁻¹[[a′, b′]]]` misses `E`;
2. for each `y ∈ k⁻¹[[a′, b′]]`, `π(h(y)) = F(z)` with `z` in the band `(0, 1) × (0, c₀)` above
   the axis and `|z − (k(y), 0)| < η` (layer by layer, uniformly);
3. `h[k⁻¹[[a + ζ/2, b − ζ/2]]]` lies in the component `C` of `M ∩ π⁻¹[D]` containing `h(x)` (in
   particular in `π⁻¹[D]`);
4. `Cl C` meets `π⁻¹F[{a} × (0, r₂)]` and `π⁻¹F[{b} × (0, s₂)]`: `C` is crossing.

*Shape:* the skeleton's `True`. Step 1 is commission 167's (no hair); step 2 uses uniform
continuity of `π` on `M` and of the inverse collar instead of `pi_thin_near_layer`; the side of the
axis comes from connectedness of `π[Q]` (it misses the axis by step 1); step 4 uses boundary bumping
for components of an open subset of a continuum (`exists_mem_closure_component_notMem`) applied to
`h[k⁻¹[[a′, a + ζ/2]]]` and `h[k⁻¹[[b − ζ/2, b′]]]`, and the frontier of `F[D′]`. The hypotheses
`0 < a`, `b < 1` of the set-up are not needed (they follow from `0 < a′ < a`, `b < b′ < 1`). -/
theorem crossing_translate (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (hab : a < b) (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {a' b' : ℝ} (ha' : 0 < a') (ha'a : a' < a) (hbb' : b < b') (hb' : b' < 1) :
    ∃ c₀ > 0, Ioo a b ×ˢ Ioo 0 c₀ ⊆ D' ∧ c₀ < r₂ ∧ c₀ < s₂ ∧
    ∀ ζ > 0, ∀ η > 0, ∃ δ > 0, ∀ x : E, (k x : ℝ) ∈ Icc (a + ζ) (b - ζ) →
      ∀ h : M ≃ₜ M, (∀ v, dist (h v) v < δ) → h (x : M) ∉ E →
      π (h (x : M) : Pt) ∈ F '' (Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) →
      Disjoint (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) E ∧
      (∀ y : E, (k y : ℝ) ∈ Icc a' b' → ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
        F z = π (h (y : M) : Pt) ∧ dist z ((k y : ℝ), 0) < η) ∧
      toPt (h '' layerSet k {t | a + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ b - ζ / 2}) ⊆
        connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt) ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty :=
  crossing_translate_aux hX hi hE hπc hπS hγπ hF hab hc1 hI hIR hDR hDf hFDo hFDf ha' ha'a hbb' hb'

/-- **Lemma T′** (commission 167 §1). For `t₀ ∈ (a, b)` there is a point `x` of the layer
`k⁻¹(t₀)` such that, within any `ε > 0` of `x`, some point `q ∈ M` lies on the vertical over `t₀`
at a height in `(0, ε)`: `π(q) = F(t₀, u)`, `0 < u < ε`. In particular `x` lies in the closure of
`M ∩ K₀` for every `K₀ = π⁻¹F[{t₀} × (0, w₂)]` (`hagopian76_K0`), so every neighbourhood of `x`
meets `M ∩ K₀`. This is Hagopian's `x` ("let `x` be a point of `k⁻¹(p₃) ∩ Cl K`", p. 347).

*Shape:* the skeleton's `True`. *Proof as in the commission*, with two changes: the points `y ∈ M`
above the axis come from `M_meets_above` near the vertical, the point of `E` near `y` from
`pi_thin_near_layer`, and the small homeomorphism carrying it to `y` from Effros (uniform form of
Lemma 2), rather than Lemma 2 at a fixed `x₀`; the crossing of the vertical is the separation of the
connected set `π[h[k⁻¹[[a + ζ/2, b − ζ/2]]]]` by the open left and right halves of the collar
band. The limit `x` is taken by compactness of `M`. -/
theorem K0_dense_low (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ x : E, (k x : ℝ) = t₀ ∧
      (∀ ε > 0, ∃ q ∈ M, dist q ((x : M) : Pt) < ε ∧ ∃ u ∈ Ioo 0 ε, π q = F (t₀, u)) ∧
      ∀ w₂ > 0, ((x : M) : Pt) ∈ closure (M ∩ π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂))) := by
  obtain ⟨x, hkx, hx⟩ := K0_dense_low_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1 hbelow hI hIR
    hDR hDf hFDo hFDf ht₀
  refine ⟨x, hkx, hx, fun w₂ hw₂ => Metric.mem_closure_iff.2 fun ε hε => ?_⟩
  obtain ⟨q, hqM, hqx, u, hu, hπq⟩ := hx (min ε w₂) (lt_min hε hw₂)
  refine ⟨q, ⟨hqM, (t₀, u), ⟨rfl, hu.1, lt_of_lt_of_le hu.2 (min_le_right _ _)⟩, hπq.symm⟩, ?_⟩
  rw [dist_comm]
  exact lt_of_lt_of_le hqx (min_le_left _ _)

/-! ## B. T12 -/

/-- **Crossing continua over the thin strip are essential** (commission 167 §2.B; Hagopian's T12
(2) "the closure of the `p`-component `C` of `M ∩ π⁻¹[D]` is essential to `h[R(E)]`", in the form
T9 provides). There is a height `c > 0` such that every connected `B ⊆ M` lying over
`F[[3/22, 19/22] × (0, c]]` whose closure meets `π⁻¹F[{3/22} × (0, c]]` and
`π⁻¹F[{19/22} × (0, c]]` has closure disjoint from `E`, and for some `ε₁`-homeomorphism `h`:
`Cl B ⊆ h[E]`, `h⁻¹[Cl B] ⊆ E`, and `h⁻¹[Cl B]` is essential to `R(E)`.

*Shape (added):* from `hagopian76_T9_full` and `hagopian76_link_control`: the closure meets a link
of index `≤ 2` at the left edge and a link of index `≥ 8` at the right edge, so T9's essential
clause applies. The homeomorphism is T9's, not Hagopian's `h` with `h(x) = p`. -/
theorem crossing_essential (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      Disjoint (closure B) E ∧ ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ closure B ⊆ h '' E ∧
        h ⁻¹' closure B ⊆ E ∧ IsEssential k (h ⁻¹' closure B) :=
  crossing_essential_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1

/-- **T12, parts (1) and (2)** (p. 347): "A point `p` of `K` and three `ε₃`-homeomorphisms `f`,
`h`, and `h₁` of `M` onto `M` exist such that (1) `f = h₁h⁻¹`, (2) the closure of the `p`-component
`C` of `M ∩ π⁻¹[D]` is essential to `h[R(E)]`, and (3) `R(E)` separates `p` from `f(p)` in
`π⁻¹[D]`."

*Shape (partial; (3) open):* for `D` built (by `hagopian76_T7` at a height `c ≤ c₉`, then
`hagopian76_D`) over `[3/22, 19/22]` and `t₀ ∈ (3/22, 19/22)`, there are `x ∈ k⁻¹(t₀)` and `ζ > 0`
such that for every `ε > 0` (Hagopian: `ε = ε₃/2`) some `ε`-homeomorphism `h` takes `x` to a point
`p = h(x)` within `ε` of `x`, off `E`, on the vertical over `t₀` at height `< ε` (so `p ∈ M ∩ K₀`
when `ε ≤ w₂`), and the `p`-component `C` of `M ∩ π⁻¹[D]`
* contains `h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]` (so `L − {L₁, L₁₁}` follows it, in the sense used in
  T12 and T17, for `h` small: Property 1's `h[piece (j + 1)] ⊆ L j`);
* is crossing;
* has closure inside a translate `h′[E]` by an `ε₁`-homeomorphism, with `h′⁻¹[Cl C]` essential to
  `R(E)` (T12 (2), with T9's `h′` in place of `h`).
(1) is the definition `f = h₁h⁻¹`; it needs the second point `q` of (3). -/
theorem hagopian76_T12_parts12 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j) :
    ∃ c₉ > 0, c₉ ≤ 1 ∧ ∀ (c r₂ s₂ : ℝ) (I₂ : Set Pt) (D' : Set (ℝ × ℝ)), c ≤ c₉ →
      (∃ c' > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c') 0)) (π '' M)) →
      TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂) (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) →
      I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c) →
      D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c →
      frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪
        Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
        ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂ →
      IsOpen (F '' D') →
      frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂) →
      ∀ t₀ ∈ Ioo (3 / 22 : ℝ) (19 / 22),
      ∃ x : E, (k x : ℝ) = t₀ ∧ ∃ ζ > 0, ∀ ε > 0, ∃ h : M ≃ₜ M, (∀ v, dist (h v) v < ε) ∧
        dist (h (x : M) : Pt) ((x : M) : Pt) < ε ∧
        (∃ u ∈ Ioo 0 ε, π (h (x : M) : Pt) = F (t₀, u)) ∧ h (x : M) ∉ E ∧
        toPt (h '' layerSet k {t | 3 / 22 + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 19 / 22 - ζ / 2}) ⊆
          connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt) ∧
        (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
          π ⁻¹' (F '' (({3 / 22} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
        (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
          π ⁻¹' (F '' (({19 / 22} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty ∧
        ∃ h' : M ≃ₜ M, (∀ v, dist v (h' v) < ε₁) ∧
          closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ⊆
            toPt (h' '' E) ∧
          IsEssential k (h' ⁻¹' (Subtype.val ⁻¹'
            closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)))) :=
  T12_parts12_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1

end Thm1

/-! ## B (rest), C–E. T12 (3), Property 3, T13, T15–T17 and the assembly (open)

The obstructions are in `OPEN.md` (batch 167) and in `doc/batches/REPORT-batch167.md` §1.B–E.

-- `hagopian76_T12` (part (3)): proved in batch 168 in a changed shape, `Hagopian76M.lean`.

**OPEN (C, `crossing_set_closed`, `hagopian76_property3`).** The hyperspace limit (attainment of
the least `v`) and the shift `g` with the margin; not reached in this batch.

theorem crossing_set_closed … : IsClosed {v : unitInterval | ∃ Z ⊆ layer d v,
    Fold.Q78.IsContinuum Z ∧ Disjoint Z E ∧ Crossing Z} := by sorry
theorem hagopian76_property3 … : ∀ v Z, Z ⊆ layer d v → Fold.Q78.IsContinuum Z →
    toPt Z ⊆ π⁻¹ (closure (F '' D')) → Disjoint Z E → ¬ Crossing Z := by sorry

**OPEN (D, `hagopian76_T13`).** Waits on T12 (3) (the separation of `p` from `f(p)`).

**OPEN (E, `hagopian76_T15_T17`, `hagopian76_theorem1 : Hagopian76Thm1`).** Wait on B–D.
-/

end HPC.Hagopian
