import HPC.Hagopian.H76T12

/-!
# Batch 168 skeleton: Hagopian 1976, Theorem 1 — crossing pieces of `R(E)`; the requirements of
# T13–T17 on `p`, `q`; T12 (3); Property 3; T13; then T15–T17 and the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Route: commission 168 §1.
Set-up as in `Hagopian76L.lean` (`hagopian76_D`, `hagopian76_K0`, `crossing_translate`). Skeleton as
delivered: `doc/batches/skeletons/Hagopian76M.lean`.

Supporting files:
* `H76TranslateIn` — Lemma T relative to any ambient set containing the translate;
* `H76RPiece` — Lemma R (`mem_closure_extUnion_diff`, `crossing_piece_of_R_aux`);
* `H76PairSep` — the planar separation (`rect_domain_crosscut_arc`, `seg_subset_rect_domain`,
  `rect_domain_crossing_separates`);
* `H76CrossSep` — the separation in `π⁻¹[D]` (`injOn_pi_preimage`, `crossing_separates_aux`);
* `H76T12` — T12 (3) in the shape of commission 168 §2.C (`T12_part3_aux`).
Shapes are recorded at each statement and in `doc/batches/REPORT-batch168.md`. Item A (what T13–T17
use of `p`, `q`, `h`, `h₁`, `f`, `C`) is in the report, §1.A. Items left open are commented out at
the end, with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## B. Crossing pieces of `R(E)`; crossing continua cut `D` -/

/-- **Lemma R** (commission 168 §1). `D = F[D′]` over `[a, b]` as in `hagopian76_D`,
`0 < a′ < a`, `b < b′ < 1`. There is a height `c₀ > 0` (the low strip `(a, b) × (0, c₀)` lies in
`D′` and below the ends of `I₂`) such that for every `ζ > 0`, every `x ∈ E` with
`k(x) ∈ [a + ζ, b − ζ]` and every `ε > 0` there is an `ε`-homeomorphism `h` of `M` with
1. `h(x) ∈ R(X, E) − E` (`X = k⁻¹(0)`);
2. `Q = h[k⁻¹[[a′, b′]]] ⊆ R(X, E)` and `Q ∩ E = ∅`;
3. layer by layer, `π(h(y)) = F(z)` with `z` in the band `(0, 1) × (0, c₀)` and
   `|z − (k(y), 0)| < ε`;
4. for every `A ⊇ Q` (in particular `A = Q` and `A = R(E)`), the component of `A ∩ π⁻¹[D]` through
   `h(x)` contains `h[k⁻¹[[a + ζ/2, b − ζ/2]]]` and its closure meets both open side edges;
5. the closure of the component of `Q ∩ π⁻¹[D]` through `h(x)` lies in `H − E` for one extension
   `H` of `E` away from `X`.

*Shape:* the skeleton's `True`. *Proof as in the commission*, with these changes: step 1 takes `y`
in `R(X, E) − E` (Lemma 6 for `Cl R(X, E)`, Lemma 4 for `E ≠ Cl R(X, E)`), so only absorption away
from `X` is needed; step 3 uses Lemma 2 at `x`; step 5 is Lemma T relative to `A`
(`crossing_translate_in_aux`). Item 5 is added: two extensions containing the end points
`h[k⁻¹(a′)]`, `h[k⁻¹(b′)]` are nested (Lemma 4), the larger one meets `Q` in a continuum (hereditary
unicoherence), and that continuum contains `h[k⁻¹((a′, b′))]` (`layerSet_Ioo_subset`), which
contains the part of `Q` over `D`. -/
theorem crossing_piece_of_R (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (hab : a < b) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {a' b' : ℝ} (ha' : 0 < a') (ha'a : a' < a) (hbb' : b < b') (hb' : b' < 1) :
    ∃ c₀ > 0, Ioo a b ×ˢ Ioo 0 c₀ ⊆ D' ∧ c₀ < r₂ ∧ c₀ < s₂ ∧
    ∀ ζ > 0, ∀ x : E, (k x : ℝ) ∈ Icc (a + ζ) (b - ζ) → ∀ ε > 0,
      ∃ h : M ≃ₜ M, (∀ v, dist (h v) v < ε) ∧
      h (x : M) ∈ extUnion E (layer k 0) ∧ h (x : M) ∉ E ∧
      h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'} ⊆ extUnion E (layer k 0) ∧
      Disjoint (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) E ∧
      (∀ y : E, (k y : ℝ) ∈ Icc a' b' → ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
        F z = π (h (y : M) : Pt) ∧ dist z ((k y : ℝ), 0) < ε) ∧
      (∀ A : Set Pt, toPt (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) ⊆ A →
        toPt (h '' layerSet k {t | a + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ b - ζ / 2}) ⊆
          connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt) ∧
        (closure (connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
          π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
        (closure (connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
          π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty) ∧
      ∃ H : Set M, IsExtensionAway E (layer k 0) H ∧
        closure (connectedComponentIn
          (toPt (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) ∩ π ⁻¹' (F '' D'))
          (h (x : M) : Pt)) ⊆ toPt (H \ E) :=
  crossing_piece_of_R_aux hX hi hE hπc hπS hγπ hF hab hc1 hbelow hI hIR hDR hDf hFDo hFDf ha' ha'a hbb' hb'

/-- **A crossing set separates `π⁻¹[D]` along `K₀`** (commission 168 §2.B, single-continuum form).
For `D = F[D′]` and the vertical over `t₀` up to the lowest point `F(t₀, w₂)` of `I₂` (as in
`hagopian76_K0`): let `B ⊆ π⁻¹[D]` be connected with compact closure, `Cl B` missing `π⁻¹[I₂]` and
the points over the axis and meeting both open side edges `π⁻¹F[{a} × (0, r₂)]`,
`π⁻¹F[{b} × (0, s₂)]`. If `Cl B` misses the points of `K₀` at heights in `(0, u₁]` and in
`[u₂, w₂)`, then no connected subset of `π⁻¹[D] − Cl B` contains a point over `F(t₀, u₁)` and a
point over `F(t₀, u₂)`. `π` is assumed injective on `π⁻¹[D]` (`injOn_pi_preimage`).

*Shape (left to me):* proof by the Jordan curve theorem in collar coordinates, as in
`hagopian76_K0_crosscut`: a connected set through both points gives (polygonal arc, loop erasure)
an arc from the bottom to `I₂` through `D′` missing `Cl B`, and an arc from the bottom to `I₂` is a
cross-cut (`rect_domain_crosscut_arc`). -/
theorem crossing_separates {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (x₀, w₂) ∈ I₂)
    (hseg : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hπinj : InjOn π (π ⁻¹' (F '' D')))
    {B : Set Pt} (hB : IsPreconnected B) (hBD : B ⊆ π ⁻¹' (F '' D'))
    (hBc : IsCompact (closure B))
    (hBe : Disjoint (closure B) (π ⁻¹' (I₂ ∪ F '' (Icc a b ×ˢ {0}))))
    (hL : (closure B ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty)
    (hR : (closure B ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty)
    {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hu₁₂ : u₁ < u₂) (hu₂ : u₂ < w₂)
    (hlo : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioc 0 u₁))))
    (hhi : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico u₂ w₂))))
    {S : Set Pt} (hS : IsPreconnected S) (hSB : S ⊆ π ⁻¹' (F '' D') \ closure B)
    {P Q : Pt} (hP : P ∈ S) (hQ : Q ∈ S) (hπP : π P = F (x₀, u₁)) (hπQ : π Q = F (x₀, u₂)) :
    False :=
  crossing_separates_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg hπinj hB hBD hBc hBe hL hR hu₁ hu₁₂ hu₂
    hlo hhi hS hSB hP hQ hπP hπQ

/-- **Two crossing continua cut `π⁻¹[D]` in three along `K₀`** (commission 168 §2.B). With `B₁`
between heights `u₁` and `u₂` on `K₀` and `B₂` between `u₂` and `u₃` (in the sense of
`crossing_separates`), no connected subset of `π⁻¹[D] − (Cl B₁ ∪ Cl B₂)` contains two of the points
over `F(t₀, u₁)`, `F(t₀, u₂)`, `F(t₀, u₃)`. *Shape:* three applications of `crossing_separates`;
disjointness of `B₁` and `B₂` is not needed. -/
theorem crossing_pair_separates {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (x₀, w₂) ∈ I₂)
    (hseg : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hπinj : InjOn π (π ⁻¹' (F '' D')))
    {B₁ B₂ : Set Pt} (hB₁ : IsPreconnected B₁) (hB₂ : IsPreconnected B₂)
    (hB₁D : B₁ ⊆ π ⁻¹' (F '' D')) (hB₂D : B₂ ⊆ π ⁻¹' (F '' D'))
    (hB₁c : IsCompact (closure B₁)) (hB₂c : IsCompact (closure B₂))
    (hB₁e : Disjoint (closure B₁) (π ⁻¹' (I₂ ∪ F '' (Icc a b ×ˢ {0}))))
    (hB₂e : Disjoint (closure B₂) (π ⁻¹' (I₂ ∪ F '' (Icc a b ×ˢ {0}))))
    (hL₁ : (closure B₁ ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty)
    (hR₁ : (closure B₁ ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty)
    (hL₂ : (closure B₂ ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty)
    (hR₂ : (closure B₂ ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty)
    {u₁ u₂ u₃ : ℝ} (hu₁ : 0 < u₁) (hu₁₂ : u₁ < u₂) (hu₂₃ : u₂ < u₃) (hu₃ : u₃ < w₂)
    (hlo₁ : Disjoint (closure B₁) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioc 0 u₁))))
    (hhi₁ : Disjoint (closure B₁) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico u₂ w₂))))
    (hlo₂ : Disjoint (closure B₂) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioc 0 u₂))))
    (hhi₂ : Disjoint (closure B₂) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico u₃ w₂))))
    {S : Set Pt} (hS : IsPreconnected S) (hSB : S ⊆ π ⁻¹' (F '' D') \ (closure B₁ ∪ closure B₂))
    {P₁ P₂ P₃ : Pt} (hπ₁ : π P₁ = F (x₀, u₁)) (hπ₂ : π P₂ = F (x₀, u₂))
    (hπ₃ : π P₃ = F (x₀, u₃)) :
    (P₁ ∈ S → P₂ ∉ S) ∧ (P₂ ∈ S → P₃ ∉ S) ∧ (P₁ ∈ S → P₃ ∉ S) := by
  have hS₁ : S ⊆ π ⁻¹' (F '' D') \ closure B₁ := fun z hz =>
    ⟨(hSB hz).1, fun h => (hSB hz).2 (Or.inl h)⟩
  have hS₂ : S ⊆ π ⁻¹' (F '' D') \ closure B₂ := fun z hz =>
    ⟨(hSB hz).1, fun h => (hSB hz).2 (Or.inr h)⟩
  have hhi₁' : Disjoint (closure B₁) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico u₃ w₂))) :=
    hhi₁.mono_right (preimage_mono (image_mono (prod_mono subset_rfl
      (Ico_subset_Ico_left hu₂₃.le))))
  refine ⟨fun h1 h2 => ?_, fun h2 h3 => ?_, fun h1 h3 => ?_⟩
  · exact crossing_separates_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg hπinj
      hB₁ hB₁D hB₁c hB₁e hL₁ hR₁ hu₁ hu₁₂ (hu₂₃.trans hu₃) hlo₁ hhi₁ hS hS₁ h1 h2 hπ₁ hπ₂
  · exact crossing_separates_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg hπinj
      hB₂ hB₂D hB₂c hB₂e hL₂ hR₂ (hu₁.trans hu₁₂) hu₂₃ hu₃ hlo₂ hhi₂ hS hS₂ h2 h3 hπ₂ hπ₃
  · exact crossing_separates_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg hπinj
      hB₁ hB₁D hB₁c hB₁e hL₁ hR₁ hu₁ (hu₁₂.trans hu₂₃) hu₃ hlo₁ hhi₁' hS hS₁ h1 h3 hπ₁ hπ₃

/-! ## C. T12 -/

/-- **T12 (3)** (p. 347) in the shape of commission 168 §2.C: "`R(E)` separates `p` from `f(p)` in
`π⁻¹[D]`". For `D` as in `hagopian76_D` over `[a, b]`, `t₀ ∈ (a, b)` and `K₀` up to `F(t₀, w₂)`
(`hagopian76_K0`), there is `x ∈ k⁻¹(t₀)` (Hagopian's `x`, Lemma T′) such that for every `ε > 0`
(Hagopian: `ε₃/2`) there are `ε`-homeomorphisms `h₀`, `h₁` with `p = h₀(x)`, `q = h₁(x)` on `K₀`
at heights `0 < u₁ < u₂ < w₂`, an extension `H` of `E` away from `X = k⁻¹(0)` and a connected
`B ⊆ π⁻¹[D]` with
* `Cl B` compact, inside `H − E`, meeting both open side edges (a crossing continuum of
  `R(X, E)`, from Lemma R);
* `Cl B` separates `p` from `q` in `π⁻¹[D]`.
So `f = h₁h₀⁻¹` is a `2ε`-homeomorphism with `f(p) = q`.

*Shape difference (recorded in the report):* the separating set is the crossing continuum
`Cl B ⊆ R(X, E)`, not `R(E)`; `p`, `q` are not shown to lie off `H` or off `R(E)`, nor in distinct
composants of `Cl R(E)`; T12 (2) for Hagopian's `h` (here `h₀`) is not included (report §1.A says
which of these T13–T17 use). -/
theorem hagopian76_T12 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDo : IsOpen D')
    (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ w₂ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂)) :
    ∃ x : E, (k x : ℝ) = t₀ ∧ ∀ ε > 0, ∃ (h₀ h₁ : M ≃ₜ M) (u₁ u₂ : ℝ),
      (∀ v, dist (h₀ v) v < ε) ∧ (∀ v, dist (h₁ v) v < ε) ∧
      0 < u₁ ∧ u₁ < u₂ ∧ u₂ < w₂ ∧
      π (h₀ (x : M) : Pt) = F (t₀, u₁) ∧ π (h₁ (x : M) : Pt) = F (t₀, u₂) ∧
      ∃ (H : Set M) (B : Set Pt), IsExtensionAway E (layer k 0) H ∧
        IsPreconnected B ∧ B ⊆ π ⁻¹' (F '' D') ∧ closure B ⊆ toPt (H \ E) ∧
        IsCompact (closure B) ∧
        (closure B ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
        (closure B ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty ∧
        ∀ S : Set Pt, IsPreconnected S → S ⊆ π ⁻¹' (F '' D') \ closure B →
          (h₀ (x : M) : Pt) ∈ S → (h₁ (x : M) : Pt) ∉ S :=
  T12_part3_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1 hbelow hI hIs hIR hDo hDR hDf hFDo hFDf ht₀ hw₂ hFw hseg

end Thm1

/-! ## D–E. Property 3, T13, T15–T17 and the assembly (open)

The obstructions are in `OPEN.md` (batch 168) and in `doc/batches/REPORT-batch168.md` §1.D–E.

**OPEN (D, `crossing_set_closed`, `hagopian76_property3`).** "Let `v` be the first point of `[0, 1]`
such that `d⁻¹(v)` contains a component of `F ∩ π⁻¹[D]` whose closure meets `π⁻¹[⟨p₁, r⟩]` and
`π⁻¹[⟨p₅, s⟩]`." Needs the hyperspace limit of crossing continua in the layers `d⁻¹(vₙ)` (a limit
continuum in `d⁻¹(v)` that still meets both open side edges, i.e. a margin away from the ends `r`,
`s` and from `I₂`), and the shift `g` of Lemmas 2–3 with a margin. Not attempted in this batch.

theorem crossing_set_closed … : IsClosed {v : unitInterval | ∃ Z ⊆ layer d v,
    Fold.Q78.IsContinuum Z ∧ Disjoint Z E ∧ Disjoint (toPt Z) (π ⁻¹' I₂) ∧ Crossing Z} := by sorry
theorem hagopian76_property3 … : ∀ v Z, Z ⊆ layer d v → Fold.Q78.IsContinuum Z →
    Disjoint Z E → Disjoint (toPt Z) (π ⁻¹' I₂) → ¬ Crossing Z := by sorry

**OPEN (E, `hagopian76_T13`).** "Let `F` be a continuum that is irreducible with respect to …
1. `F` is an extension of `E` in `M` away from `k⁻¹(0)`. 2. `F` separates `p` from `f(p)` in
`π⁻¹[D]`." `hagopian76_T12` gives the extension `H ⊇ Cl B` with `Cl B` separating `p` from
`f(p) = q`; missing: `p, q ∉ H` (so that `H` itself separates), and the irreducible element (the
intersection of a chain of separating extensions need not be an extension).

**OPEN (E, `hagopian76_T15_T17`, `hagopian76_theorem1 : Hagopian76Thm1`).** Wait on D and T13; the
missing statements are listed in report §1.A and §5.
-/

end HPC.Hagopian
