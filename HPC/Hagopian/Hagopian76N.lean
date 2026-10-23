import HPC.Hagopian.H76Generic
import HPC.Hagopian.H76Dichot

/-!
# Batch 169: Hagopian 1976, Theorem 1 — above and below a crossing continuum; generic `p`, `q`;
# the dichotomy for `R(E)`; T13; Property 3; then T15–T17 and the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Route: commission 169 §1.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76N.lean`.

Supporting files:
* `H76Meagre` — `R(E)` lies in a composant of `M`, hence is meagre; points off `R(E)` in every
  nonempty open set;
* `H76Sides` — the sets below and above a crossing continuum (`belowSet`, `aboveSet`), open and
  disjoint (`crossing_sides_aux`);
* `H76T12Sides` — the construction of T12 (3) (batch 168) with the position data exposed;
* `H76Generic` — generic `p`, `q` (`exists_generic_pq_aux`), `SepIn.mono`;
* `H76Dichot` — `RsetDichotomy` (the dichotomy as a `Prop`), `image_composant`, the dichotomy from
  `Cl R(E) = M`, and its consequence `h[R(E)] ∩ R(E) = ∅`;
* `H76ChainSep` — `SepIn`; a directed intersection of compact separators separates; the
  intersection of a chain of extensions is a continuum; `ExtChainInter` (a `Prop`) and T13 under it.

Shapes are recorded at each statement and in `doc/batches/REPORT-batch169.md`. Items left open are
commented out at the end, with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **`R(E)` is meagre in `M`** (commission 169 §1.1): a countable union of proper subcontinua of
the indecomposable continuum `M`.

*Proof (shorter than the commission's):* every extension of `E`, away from either end set, is a
proper subcontinuum of `M` (it has a proper extension, Lemma 4 for `k` or for `σ ∘ k`) containing
a fixed point `e ∈ E`. So `R(E)` lies in the composant of `e` in `M`, which is meagre (Moore
136–137, `composant_isMeagre`). -/
theorem isMeagre_Rset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) : IsMeagre (Rset k) :=
  isMeagre_Rset_aux hX hi hE

/-- **A. Above and below a crossing continuum** (commission 169 §1.1, §2.A).

*Shape (left to me):* `belowSet π F D′ t₀ u₁ Z` is the set of points of `π⁻¹[D] − Z` joined by a
connected subset of `π⁻¹[D] − Z` to a point over `F(t₀, v)`, `0 < v ≤ u₁`; `aboveSet … u₂ w₂ Z` the
same with `u₂ ≤ v < w₂` (`F(t₀, w₂)` the lowest point of `I₂` over `t₀`). Both are open in `R²`
(`belowSet_isOpen`, `aboveSet_isOpen`). For a crossing continuum `Z = Cl B` (the hypotheses of
`crossing_separates`) missing the vertical at heights `(0, u₁]` and `[u₂, w₂)`, they are
**disjoint** (this theorem).

*Not proved:* that they cover `π⁻¹[D] − Z` (every component of `π⁻¹[D] − Z` reaches the
neighbourhood of one of the two edges). The reference to the vertical over `t₀` is kept: the
bottom-edge and `I₂` neighbourhoods are reached through it. -/
theorem crossing_sides {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
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
    {u₁ u₂ : ℝ} (hu₁₂ : u₁ < u₂)
    (hlo : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioc 0 u₁))))
    (hhi : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico u₂ w₂)))) :
    Disjoint (belowSet π F D' x₀ u₁ (closure B)) (aboveSet π F D' x₀ u₂ w₂ (closure B)) :=
  crossing_sides_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf hx₀ hw₂ hFw hseg hπinj hB hBD hBc
    hBe hL hR hu₁₂ hlo hhi

/-- **B. Generic `p`, `q`** (commission 169 §2.B). Set-up of `hagopian76_T12`. There is
`x ∈ k⁻¹(t₀)` such that for every `ε > 0` there are `ε`-homeomorphisms `h`, `h₁`, heights
`0 < u₁ < u₂ < w₂`, an extension `H` of `E` away from `X = k⁻¹(0)` and a connected `B ⊆ π⁻¹[D]`
with:
1. `p = h(x)` and `q = h₁(x)` lie **off `R(E)`**;
2. `Z = Cl B` is compact, lies in `H − E`, meets both open side edges, and misses the vertical
   over `t₀` at the heights `(0, u₁]` and `[u₂, w₂)`;
3. `p` is **below** `Z` and `q` is **above** `Z` (`belowSet`, `aboveSet`);
4. **`H` separates `p` from `q` in `π⁻¹[D]`**, and so does `R(E)` (`SepIn`, which includes
   `p`, `q ∈ π⁻¹[D] − H`);
5. the `p`-component and the `q`-component of `M ∩ π⁻¹[D]` **cross**: their closures meet both
   open side edges.

*Shape:* the commission's, with "below/above `Z`" taken relative to the vertical over `t₀`
(item A). *Route changed:* `p`, `q` are not on `K₀`. `T12_sides_aux` gives `p₀ = h₀(x)` below and
`q₀ = h₁′(x)` above `Z` on `K₀`; the sets below and above `Z` are open in `R²`, so their traces on
`M` near `p₀`, `q₀` are nonempty open subsets of `M`, and contain points off the meagre `R(E)`
(`exists_notMem_Rset`); near `x` these are `h(x)`, `h₁(x)` (Lemma 2). Separation: by
`crossing_sides`, since `Z ⊆ H ⊆ R(E)` and `p`, `q ∉ R(E)`. Crossing: Lemma T
(`crossing_translate`), since `p`, `q` are `h(x)`, `h₁(x)` with `h`, `h₁` small, off `E` and over
`D`. -/
theorem exists_generic_pq (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
    ∃ x : E, (k x : ℝ) = t₀ ∧ ∀ ε > 0, ∃ (h h₁ : M ≃ₜ M) (u₁ u₂ : ℝ) (H : Set M) (B : Set Pt),
      (∀ v, dist (h v) v < ε) ∧ (∀ v, dist (h₁ v) v < ε) ∧
      h (x : M) ∉ Rset k ∧ h₁ (x : M) ∉ Rset k ∧
      0 < u₁ ∧ u₁ < u₂ ∧ u₂ < w₂ ∧
      IsExtensionAway E (layer k 0) H ∧
      IsPreconnected B ∧ B ⊆ π ⁻¹' (F '' D') ∧ closure B ⊆ toPt (H \ E) ∧
      IsCompact (closure B) ∧
      (closure B ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure B ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty ∧
      Disjoint (closure B) (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ioc 0 u₁))) ∧
      Disjoint (closure B) (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ico u₂ w₂))) ∧
      (h (x : M) : Pt) ∈ belowSet π F D' t₀ u₁ (closure B) ∧
      (h₁ (x : M) : Pt) ∈ aboveSet π F D' t₀ u₂ w₂ (closure B) ∧
      SepIn (π ⁻¹' (F '' D')) (toPt H) (h (x : M)) (h₁ (x : M)) ∧
      SepIn (π ⁻¹' (F '' D')) (toPt (Rset k)) (h (x : M)) (h₁ (x : M)) ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h₁ (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h₁ (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty :=
  exists_generic_pq_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1 hbelow hI hIs hIR hDo hDR hDf hFDo hFDf ht₀ hw₂ hFw hseg

/-- **T12 in the weakest form of report 168 §1.A, conditions 2–3, under the dichotomy**
(commission 169 §2.C.3). If `RsetDichotomy k` holds, then in the set-up of `hagopian76_T12`
there is `x ∈ k⁻¹(t₀)` such that for every `ε > 0` there are `ε`-homeomorphisms `h`, `h₁`
(`p = h(x)`, `f = h₁h⁻¹` a `2ε`-homeomorphism with `f(p) = h₁(x)`) and an extension `H` of `E` away
from `k⁻¹(0)` with
* `H` separates `p` from `f(p)` in `π⁻¹[D]` (condition 2);
* `h[R(E)] ∩ R(E) = ∅` and `h₁[R(E)] ∩ R(E) = ∅` (condition 3);
* the `p`-component of `M ∩ π⁻¹[D]` crosses. -/
theorem hagopian76_T12_of_dichotomy (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hD : RsetDichotomy k) :
    ∃ x : E, (k x : ℝ) = t₀ ∧ ∀ ε > 0, ∃ (h h₁ : M ≃ₜ M) (H : Set M),
      (∀ v, dist (h v) v < ε) ∧ (∀ v, dist (h₁ v) v < ε) ∧
      (∀ v, dist ((h.symm.trans h₁) v) v < 2 * ε) ∧ (h.symm.trans h₁) (h (x : M)) = h₁ (x : M) ∧
      IsExtensionAway E (layer k 0) H ∧
      SepIn (π ⁻¹' (F '' D')) (toPt H) (h (x : M)) (h₁ (x : M)) ∧
      Disjoint (h '' Rset k) (Rset k) ∧ Disjoint (h₁ '' Rset k) (Rset k) ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty := by
  obtain ⟨x, hkx, hmain⟩ := exists_generic_pq_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1 hbelow hI hIs hIR hDo hDR hDf hFDo hFDf ht₀ hw₂ hFw hseg
  refine ⟨x, hkx, fun ε hε => ?_⟩
  obtain ⟨h, h₁, -, -, H, -, hh, hh₁, hpR, hqR, -, -, -, hH, -, -, -, -, -, -, -, -, -, -, hsep,
    -, hcL, hcR, -, -⟩ := hmain ε hε
  have hxR : (x : M) ∈ Rset k := subset_Rset_self hE x.2
  refine ⟨h, h₁, H, hh, hh₁, fun v => ?_, by simp, hH, hsep,
    disjoint_image_Rset hD h hxR hpR, disjoint_image_Rset hD h₁ hxR hqR, hcL, hcR⟩
  have h1 := hh₁ (h.symm v)
  have h2 := hh (h.symm v)
  rw [h.apply_symm_apply] at h2
  calc dist ((h.symm.trans h₁) v) v ≤ dist (h₁ (h.symm v)) (h.symm v) + dist (h.symm v) v :=
        dist_triangle _ _ _
    _ < ε + ε := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = 2 * ε := by ring

/-- **C. The dichotomy, if `Cl R(E) = M`** (commission 169 §1.2, route C.1): `R(E)` and `g[R(E)]`
are then composants of `M` (`hagopian76_Rset_composant`, `image_composant`), and composants sharing
a point are equal. The hypothesis `Cl R(E) = M` (C.1, `closure_Rset_eq_univ`) is open. -/
theorem Rset_homeo_dichotomy_of_closure (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (hcl : closure (Rset k) = univ) (g : M ≃ₜ M) (hg : (g '' Rset k ∩ Rset k).Nonempty) :
    g '' Rset k = Rset k :=
  Rset_dichotomy_of_closure_aux hX hi hE hcl g hg

omit [ConnectedSpace M] in
/-- **D. T13, the separation and continuum halves of `iInter_chain_extension`** (commission 169
§2.D). For a nonempty chain `c` of extensions of `E` away from `X₀`, each separating `p` from `q`
in the open set `O ⊆ R²`, the intersection `⋂ c` contains `E`, is a continuum, and separates `p`
from `q` in `O`. *Open:* that `⋂ c` is an extension away from `X₀` (`ExtChainInter`). -/
theorem iInter_chain_extension {E X₀ : Set M} (hEne : E.Nonempty) {O : Set Pt} (hO : IsOpen O)
    {p q : Pt} {c : Set (Set M)} (hne : c.Nonempty) (hch : IsChain (· ⊆ ·) c)
    (hc : ∀ F ∈ c, IsExtensionAway E X₀ F ∧ SepIn O (toPt F) p q) :
    E ⊆ ⋂₀ c ∧ Fold.Q78.IsContinuum (⋂₀ c) ∧ SepIn O (toPt (⋂₀ c)) p q := by
  obtain ⟨hE, hcont⟩ := iInter_chain_isContinuum hEne hne hch fun F hF => (hc F hF).1
  refine ⟨hE, hcont, sepIn_sInter_chain hO hne hch (fun F hF => ?_) fun F hF => (hc F hF).2⟩
  obtain ⟨⟨-, d, hd, -⟩, -⟩ := hc F hF
  exact hd.isCompact

omit [CompactSpace M] [ConnectedSpace M] in
/-- **D. T13** (p. 347), conditional on `ExtChainInter` (commission 169 §2.D): "Let `F` be a
continuum that is irreducible with respect to the following properties: 1. `F` is an extension of
`E` in `M` away from `k⁻¹(0)`. 2. `F` separates `p` from `f(p)` in `π⁻¹[D]`."

*Shape:* given one extension `H` away from `X₀` separating `p` from `q` in the open set `O`
(`exists_generic_pq` supplies it, with `O = π⁻¹[D]`, `X₀ = k⁻¹(0)`, `q = f(p)`), and
`ExtChainInter E X₀ O p q`, there is a separating extension `F ⊆ H` containing no other separating
extension (Zorn, with `iInter_chain_extension` for the lower bounds). -/
theorem hagopian76_T13 {E X₀ : Set M} {O : Set Pt} (hO : IsOpen O) {p q : Pt}
    (hci : ExtChainInter E X₀ O p q) {H : Set M} (hH : IsExtensionAway E X₀ H)
    (hHs : SepIn O (toPt H) p q) :
    ∃ F ⊆ H, IsExtensionAway E X₀ F ∧ SepIn O (toPt F) p q ∧
      ∀ F', IsExtensionAway E X₀ F' → SepIn O (toPt F') p q → F' ⊆ F → F' = F :=
  T13_of_chainInter hO hci hH hHs

end Thm1

/-! ## Open items

The obstructions are in `OPEN.md` (batch 169) and in `doc/batches/REPORT-batch169.md`.

**OPEN (C, `Rset_homeo_dichotomy`).** Proved from `Cl R(E) = M`
(`Rset_homeo_dichotomy_of_closure`); used as the hypothesis `RsetDichotomy k` in
`hagopian76_T12_of_dichotomy` (C.3). Route C.2 (re-centring at a piece `E″` with an end set
missing `g[F]`) needs a layer of the line `R(E)` that the compact set `g[F]` misses; not proved.

theorem Rset_homeo_dichotomy (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) (g : M ≃ₜ M)
    (hg : (g '' Rset k ∩ Rset k).Nonempty) : g '' Rset k = Rset k := by
  sorry

**OPEN (C.1, `closure_Rset_eq_univ`).** No argument either way.

theorem closure_Rset_eq_univ (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) : closure (Rset k) = univ := by
  sorry

**`ExtChainInter`**: proved in batch 170 (`extChainInter`, `Hagopian76O.lean`).

**OPEN (E, `crossing_set_closed`, `hagopian76_property3`).** Not attempted; unchanged from batch
168.

**OPEN (F, `follows_essential_crossing`).** The component `Cᵢ₋₁` of T17 is determined by `Cl Cᵢ`
(the first crossing component met when extending `Cl Cᵢ` away from `X`); its points cannot be
chosen generically, so Lemma T does not apply unless `Cᵢ₋₁` is shown to contain a point
`h′(x′)` low over the middle range.

**OPEN (G, `hagopian76_T15_T17`, `hagopian76_theorem1 : Hagopian76Thm1`).** Wait on A (covering
half), C, D, E and F; skeleton proposal in report §5.
-/

end HPC.Hagopian
