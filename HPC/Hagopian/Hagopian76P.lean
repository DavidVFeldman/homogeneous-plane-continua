import HPC.Hagopian.H76Bottom
import HPC.Hagopian.H76GenericComp

/-!
# Batch 171: Hagopian 1976, Theorem 1 — Property 3 without margins; positions through the side
# edges; the ends of crossing components; T15–T17 and the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 171 §1.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76P.lean`.

Supporting files:
* `H76Prop3L3` — Lemma 3 against two translated layers (`layer_meets_translate_end_aux`); the
  parameters met by a layer form an interval (`translate_params_ordConnected`); the reduction of
  Property 3 to the end case (`layer_meets_translate_initial`);
* `H76Bottom` — the preimage under `π` of an open connected set off `π[E]` is connected
  (`isPreconnected_preimage_off`); the bottom case of the covering half
  (`bottom_component_below_aux`).

Shapes are recorded at each statement and in `doc/batches/REPORT-batch171.md`. Items left open are
commented out at the end, with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A. Lemma 3 against two translated layers** (a third route to Property 3, found in this
batch; commission 171 §1.A asked for A.1 or A.2). An interior layer `d⁻¹(v)` (`0 < v < 1`) of a
type A′ continuum `G` that meets two distinct layers `h[k⁻¹(α)]`, `h[k⁻¹(β)]` of a translate
`h[E]` (any homeomorphism `h`, no smallness) meets `h[k⁻¹(0)]` or `h[k⁻¹(1)]`.

*Proof:* otherwise `h⁻¹[d⁻¹(v)]` meets `k⁻¹(α)` and misses the end sets of `E`, so by Lemma 3
(`lemma3_half`, with the roles of `E` and `G` exchanged and `h⁻¹`) it lies in `k⁻¹(α)`; likewise in
`k⁻¹(β)`, which is disjoint from `k⁻¹(α)`. -/
theorem layer_meets_translate_end (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E G : Set M} {k : E → unitInterval} {d : G → unitInterval} (hE : IsMinimalAdmissible E k)
    (hG : IsMinimalAdmissible G d) {v : unitInterval} (hv0 : 0 < v) (hv1 : v < 1) (h : M ≃ₜ M)
    {α β : unitInterval} (hαβ : α ≠ β) (hα : (layer d v ∩ h '' layer k α).Nonempty)
    (hβ : (layer d v ∩ h '' layer k β).Nonempty) :
    (layer d v ∩ h '' (layer k 0 ∪ layer k 1)).Nonempty :=
  layer_meets_translate_end_aux (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hG
    hv0 hv1 h hαβ hα hβ

/-- **A. Property 3, reduced to the end case** (p. 347: "Let `v` be the first point of `[0, 1]`
such that `d⁻¹(v)` contains a component of `F ∩ π⁻¹[D]` whose closure meets `π⁻¹[(p₁, r)]` and
`π⁻¹[(p₅, s)]`" … "This contradicts the definition of `v`").

Set-up of `follows_crossing`, and a type A′ continuum `G` of `M` with map `d` (the `F` of T13). If
a crossing `B` (as in `follows_crossing`) has its closure in one interior layer `d⁻¹(v)`,
`0 < v < 1`, then for the `ε₁`-homeomorphism `h` of `follows_crossing` (with Property 1's link
condition and `Cl B ⊇ h[k⁻¹((4/11, 7/11))]`) the layer **reaches an end link of the chain through
every link on one side**: it meets `L₀, …, L₅`, or it meets `L₅, …, L₁₀`.

*Shape (left to me):* no least `v` and no margins. The printed contradiction is not reached: what is
excluded is a layer containing a middle translate and missing both translated end sets. The
remaining configuration (the layer meets every `h[k⁻¹(t)]`, `t ≤ 6/11`, or every one with
`t ≥ 5/11`) is open (report 171 §1.A). -/
theorem hagopian76_property3_reduced (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, 0 < v → v < 1 → closure B ⊆ layer d v →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧
        h '' layerSet k {t | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} ⊆ closure B ∧
        ((∀ t : unitInterval, (t : ℝ) ≤ 6 / 11 → (layer d v ∩ h '' layer k t).Nonempty) ∨
          (∀ t : unitInterval, 5 / 11 ≤ (t : ℝ) → (layer d v ∩ h '' layer k t).Nonempty)) ∧
        ((∀ j : Fin 11, (j : ℕ) ≤ 5 → (toPt (layer d v) ∩ L j).Nonempty) ∨
          (∀ j : Fin 11, 5 ≤ (j : ℕ) → (toPt (layer d v) ∩ L j).Nonempty)) := by
  obtain ⟨c, hc, hc1, hB⟩ := follows_crossing hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1
  refine ⟨c, hc, hc1, fun B hBc hBin hBl hBr v hv0 hv1 hBv => ?_⟩
  obtain ⟨-, h, hh, -, -, -, hlink, hmid⟩ := hB B hBc hBin hBl hBr
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  -- two translated layers inside the layer
  have hmeet : ∀ t : unitInterval, 4 / 11 < (t : ℝ) → (t : ℝ) < 7 / 11 →
      (layer d v ∩ h '' layer k t).Nonempty := by
    intro t ht1 ht2
    obtain ⟨y, hy⟩ := hE.2.1.2.1 t
    have hy' : h y ∈ h '' layerSet k {t | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} :=
      ⟨y, ⟨y, by rw [mem_preimage, hy]; exact ⟨ht1, ht2⟩, rfl⟩, rfl⟩
    exact ⟨h y, hBv (hmid hy'), y, ⟨y, hy, rfl⟩, rfl⟩
  set α : unitInterval := ⟨5 / 11, by norm_num, by norm_num⟩
  set β : unitInterval := ⟨6 / 11, by norm_num, by norm_num⟩
  have hαβ : α < β := by show (5 / 11 : ℝ) < 6 / 11; norm_num
  have hcases := layer_meets_translate_initial hHU hAT hE hG hv0 hv1 h hαβ
    (hmeet α (by show (4 / 11 : ℝ) < 5 / 11; norm_num) (by show (5 / 11 : ℝ) < 7 / 11; norm_num))
    (hmeet β (by show (4 / 11 : ℝ) < 6 / 11; norm_num) (by show (6 / 11 : ℝ) < 7 / 11; norm_num))
  have hcases' : (∀ t : unitInterval, (t : ℝ) ≤ 6 / 11 → (layer d v ∩ h '' layer k t).Nonempty) ∨
      (∀ t : unitInterval, 5 / 11 ≤ (t : ℝ) → (layer d v ∩ h '' layer k t).Nonempty) := by
    rcases hcases with h1 | h1
    · exact Or.inl fun t ht => h1 t ht
    · exact Or.inr fun t ht => h1 t ht
  refine ⟨h, hh, hmid, hcases', ?_⟩
  -- a translated layer in `piece (j + 1)` gives a point of the layer in `L j`
  have hlinkpt : ∀ (j : Fin 11) (t : unitInterval), (j : ℝ) / 11 ≤ (t : ℝ) →
      (t : ℝ) ≤ ((j : ℝ) + 1) / 11 → (layer d v ∩ h '' layer k t).Nonempty →
      (toPt (layer d v) ∩ L j).Nonempty := by
    rintro j t ht1 ht2 ⟨_, hxv, y, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨(h e : Pt), ⟨h e, hxv, rfl⟩, hlink j ⟨h e, ⟨e, ⟨e, ?_, rfl⟩, rfl⟩, rfl⟩⟩
    rw [mem_preimage, mem_singleton_iff.1 he]
    push_cast
    constructor <;> linarith
  rcases hcases' with h1 | h1
  · left
    intro j hj
    have hj' : ((j : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hj
    set t : unitInterval := ⟨(j : ℝ) / 11, by positivity, by
      rw [div_le_one (by norm_num)]; linarith⟩
    exact hlinkpt j t le_rfl (by show (j : ℝ) / 11 ≤ ((j : ℝ) + 1) / 11; linarith)
      (h1 t (by show (j : ℝ) / 11 ≤ 6 / 11; linarith))
  · right
    intro j hj
    have hj' : (5 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj
    have hj10 : ((j : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (Nat.lt_succ_iff.1 j.2)
    set t : unitInterval := ⟨((j : ℝ) + 1) / 11, by positivity, by
      rw [div_le_one (by norm_num)]; linarith⟩
    exact hlinkpt j t (by show (j : ℝ) / 11 ≤ ((j : ℝ) + 1) / 11; linarith) le_rfl
      (h1 t (by show (5 / 11 : ℝ) ≤ ((j : ℝ) + 1) / 11; linarith))

omit [CompactSpace M] [ConnectedSpace M] in
/-- **B. The bottom case of the covering half** (commission 171 §1.B, bottom case; p. 349:
"Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`"). Set-up of `crossing_sides`, with
`π` a quotient map and a low strip `(a, b) × (0, c₀) ⊆ D′`. For a compact `Z` (e.g. `toPt K` for a
subcontinuum `K` of `M` missing `E`) missing `π⁻¹` of the bottom edge, there is a height `u > 0`
such that every point of `π⁻¹[D] − Z` whose component in `π⁻¹[D] − Z` has closure meeting `π⁻¹` of
the bottom edge is **below** `Z` relative to the vertical over `t₀`.

*Shape:* the conclusion uses the batch-169 `belowSet` (vertical anchor) with the height `u`
supplied; it is the same for every `t₀ ∈ (a, b)`. The two other cases (the `I₂` case and the side
edges) are open. -/
theorem crossing_bottom_below {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hb : b < 1) (hc1 : c ≤ 1) {D' : Set (ℝ × ℝ)}
    (hDo : IsOpen (F '' D')) (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hlow : ∃ c₀ > 0, Ioo a b ×ˢ Ioo 0 c₀ ⊆ D') {Z : Set Pt} (hZc : IsCompact Z)
    (hZb : Disjoint Z (π ⁻¹' (F '' (Icc a b ×ˢ {0})))) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ u > 0, ∀ P ∈ π ⁻¹' (F '' D') \ Z,
      (closure (connectedComponentIn (π ⁻¹' (F '' D') \ Z) P) ∩
        π ⁻¹' (F '' (Icc a b ×ˢ {0}))).Nonempty →
      P ∈ belowSet π F D' t₀ u Z :=
  bottom_component_below_aux hπ hπS hγπ hF ha hb hc1 hDo hDR hlow hZc hZb ht₀

/-- **E. T12 without the dichotomy** (report 168 §1.A, conditions 2–3; commission 171 §1.E). In the
set-up of `hagopian76_T12` there is `x ∈ k⁻¹(t₀)` such that for every `ε > 0` there are
`ε`-homeomorphisms `h`, `h₁` (`p = h(x)`, `f = h₁h⁻¹` a `2ε`-homeomorphism with `f(p) = h₁(x)`) and an
extension `H` of `E` away from `k⁻¹(0)` with
* `H` separates `p` from `f(p)` in `π⁻¹[D]` (condition 2);
* `h[R(E)] ∩ R(E) = ∅` and `h₁[R(E)] ∩ R(E) = ∅` (condition 3);
* the `p`-component of `M ∩ π⁻¹[D]` crosses.

*Shape:* that of `hagopian76_T12_of_dichotomy` (batch 169) with the hypothesis `RsetDichotomy k`
removed. *Proof:* `p`, `q` are taken off the composant `κ` of `x` (meagre), not merely off
`R(E) ⊆ κ` (`exists_generic_pq_comp_aux`); then `translate_Rset_disjoint`. -/
theorem hagopian76_T12_uncond (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
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
  obtain ⟨x, hkx, hmain⟩ := exists_generic_pq_comp_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1
    hbelow hI hIs hIR hDo hDR hDf hFDo hFDf ht₀ hw₂ hFw hseg
  refine ⟨x, hkx, fun ε hε => ?_⟩
  obtain ⟨h, h₁, -, -, H, -, hh, hh₁, -, -, hpC, hqC, -, -, -, hH, -, -, -, -, -, -, -, -, -, -,
    hsep, -, hcL, hcR, -, -⟩ := hmain ε hε
  refine ⟨h, h₁, H, hh, hh₁, fun v => ?_, by simp, hH, hsep,
    translate_Rset_disjoint hX hi hE x.2 h hpC, translate_Rset_disjoint hX hi hE x.2 h₁ hqC,
    hcL, hcR⟩
  have h1 := hh₁ (h.symm v)
  have h2 := hh (h.symm v)
  rw [h.apply_symm_apply] at h2
  calc dist ((h.symm.trans h₁) v) v ≤ dist (h₁ (h.symm v)) (h.symm v) + dist (h.symm v) v :=
        dist_triangle _ _ _
    _ < ε + ε := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = 2 * ε := by ring

end Thm1

/-! ## Open items

The obstructions are in `OPEN.md` (batch 171) and in `doc/batches/REPORT-batch171.md`.

-- `hagopian76_property3` (A): proved in batch 173, `Hagopian76R.lean`.

**OPEN (B, side edges; `belowSet′`, `aboveSet′`).** The bottom case is proved
(`crossing_bottom_below`). The `I₂` case needs the thin neighbourhood of the arc `I` in `D′` to be
connected (a collar of `I` from inside `D′`; no such lemma exists yet), and the side-edge
definitions need a version of `rect_domain_crossing_separates` with anchors on the frontier.

theorem crossing_sides_cover' … :
    π ⁻¹' (F '' D') \ toPt K ⊆ belowSet' … (toPt K) ∪ aboveSet' … (toPt K) := by
  sorry

**OPEN (C, the ends of a crossing component).** Not proved. In the end case of A the ends of
`Cl Cᵢ₋₁` are exactly what is not controlled.

theorem crossing_component_ends … :
    (toPt (closure B) ∩ L 1).Nonempty ∧ (toPt (closure B) ∩ L 9).Nonempty := by
  sorry

**OPEN (D, T15–T17 and the assembly).** Wait on A (end case), B (`I₂`, side edges) and C. Since
`hagopian76_T12_uncond` removes the need for `RsetDichotomy`, the target is now unconditional.

-- `hagopian76_theorem1`: proved in batch 190, `Jones75B.lean`.

**E (generic translates): closed** by `translate_Rset_disjoint` and `hagopian76_T12_uncond`; the
dichotomy itself is not proved and is no longer used.
-/

end HPC.Hagopian
