import HPC.Hagopian.H76Swallow
import HPC.Hagopian.H76InnerCollar

/-!
# Batch 172: Hagopian 1976, Theorem 1 — the end case of Property 3; the `I₂` case and the side
# edges by Schoenflies; the ends of crossing components; T15–T17 and the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 172 §1.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76Q.lean`.

Supporting files:
* `H76Swallow` — the swallowing lemma (`continuum_subset_layer_of_open`): a subcontinuum of a type
  A′ continuum with a nonempty relatively open part inside one layer lies in that layer (lower
  semicontinuity, Lemma 5); hence a layer containing an open piece of a translate `h[E]` contains
  `h[E]` (`translate_subset_layer`), and, for an extension `F`, `h[F]`
  (`translate_extension_subset_layer`);
* `H76InnerCollar` — the inner collar of an arc of a Jordan curve (`jordan_inner_collar`, from the
  square Schoenflies theorem), the domain `D′` as a Jordan domain (`rect_frontier_domain`), and the
  `I₂` case of the covering half (`top_component_above_aux`).

Shapes are recorded at each statement and in `doc/batches/REPORT-batch172.md`. Items left open are
commented out at the end, with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A. Property 3, reduced to one configuration** (commission 172 §1.A; p. 347: "Let `v` be the
first point of `[0, 1]` such that `d⁻¹(v)` contains a component of `F ∩ π⁻¹[D]` whose closure
meets `π⁻¹[(p₁, r)]` and `π⁻¹[(p₅, s)]`" … "This contradicts the definition of `v`").

Set-up of `follows_crossing`, and an extension `G` of `E` away from `k⁻¹(0)` with map `d` (the `F`
of T13). If a crossing `B` has its closure in an interior layer `d⁻¹(v)` (`0 < v < 1`), then
* `d⁻¹(v)` misses `E` (commission §1.A.1: `v` lies beyond `E`);
* for the `ε₁`-homeomorphism `h` of `follows_crossing` (with `h[k⁻¹((4/11, 7/11))] ⊆ Cl B`), the
  layer contains **the whole translate `h[G]`** of the extension (in particular `h[E]`).

*Shape (left to me):* the end case of batch 171 does not occur separately: the middle translate is
an open piece of `h[E]`, so the swallowing lemma puts all of `h[E] ∩ G`, then `h[E]`, then `h[G]`
in the layer, whatever happens at the ends (cases (a) and (b) of the commission are not needed).
What is left is the configuration `h[G] ⊆ d⁻¹(v)` (`Property3End`). -/
theorem hagopian76_property3_translate (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, 0 < v → v < 1 → closure B ⊆ layer d v →
      Disjoint (layer d v) E ∧ ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧
        h '' layerSet k {t | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} ⊆ closure B ∧
        h '' G ⊆ layer d v := by
  obtain ⟨c, hc, hc1, hB⟩ := hagopian76_property3_reduced hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1 hG
  refine ⟨c, hc, hc1, fun B hBc hBin hBl hBr v hv0 hv1 hBv => ?_⟩
  obtain ⟨h, hh, hmid, -, -⟩ := hB B hBc hBin hBl hBr v hv0 hv1 hBv
  obtain ⟨s, -, hseg, -⟩ := hagopian76_initial_segment hX hi hE hG hEG hX0
  have hdisjB := closure_disjoint_E_of_above hX hi hE hπ.continuous hγπ hF
    (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (19 / 22 : ℝ) < 1) hc1 hBc hBin
  obtain ⟨x, hxB, -⟩ := hBl
  have hdisj : Disjoint (layer d v) E := by
    refine layer_disjoint_of_not_subset hseg fun hsub => ?_
    exact disjoint_left.1 hdisjB hxB (hsub (hBv hxB))
  have hopen : IsOpen {t : unitInterval | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11} :=
    (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)
  have hne : ({t : unitInterval | 4 / 11 < (t : ℝ) ∧ (t : ℝ) < 7 / 11}).Nonempty :=
    ⟨⟨1 / 2, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  have hhE := translate_subset_layer hX hi hE hG hv0 hv1 h hopen hne (hmid.trans hBv)
  exact ⟨hdisj, h, hh, hmid, translate_extension_subset_layer hX hi hE hG hEG hX0 hv0 hv1 h hhE⟩

/-- **The configuration left by item A** (a named `Prop`, commission 172 §1.D): no
`ε₁`-homeomorphism carries the extension `G` into one of its interior layers. -/
def Property3End {G : Set M} (d : G → unitInterval) (ε₁ : ℝ) : Prop :=
  ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) → ∀ v : unitInterval, 0 < v → v < 1 →
    ¬ h '' G ⊆ layer d v

/-- **A. Property 3, conditional on `Property3End`** (p. 347, Property 3: no layer `d⁻¹(v)`,
`0 < v < 1`, of the extension contains the closure of a crossing). -/
theorem hagopian76_property3_of_end (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) (hP3 : Property3End d ε₁) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, 0 < v → v < 1 → ¬ closure B ⊆ layer d v := by
  obtain ⟨c, hc, hc1, hB⟩ := hagopian76_property3_translate hX hi hE he hend hπ hπS hγπ hF hLch
    hEL hLG hP1 hG hEG hX0
  refine ⟨c, hc, hc1, fun B hBc hBin hBl hBr v hv0 hv1 hBv => ?_⟩
  obtain ⟨-, h, hh, -, hhG⟩ := hB B hBc hBin hBl hBr v hv0 hv1 hBv
  exact hP3 h hh v hv0 hv1 hhG

/-- **A. A translate of `G` inside one of its layers swallows `Cl R(E)`.** If `E ⊆ G` and an
interior layer `d⁻¹(v)` (`0 < v < 1`) contains `h[G]`, then `Cl R(E) ⊆ h⁻¹[d⁻¹(v)]`.

*Proof:* `G ⊆ U = h⁻¹[d⁻¹(v)]`, an interior layer of the type A′ continuum `h⁻¹[G]`. Every extension
`F′` of `E` away from `k⁻¹(0)` has the relatively open initial piece `d_{F′}⁻¹[[0, s))` inside
`E ⊆ U`, so by the swallowing lemma `F′ ∩ h⁻¹[G] ⊆ U`; then `F′` meets `h⁻¹[G]` and misses its end
sets, so `F′ ⊆ h⁻¹[G]` and `F′ ⊆ U`. Hence `R(k⁻¹(0), E) ⊆ U`, and `Cl R(E) = Cl R(k⁻¹(0), E) ⊆ U`
(Lemma 6, step 8). -/
theorem closure_Rset_subset_of_translate (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G) (h : M ≃ₜ M)
    {v : unitInterval} (hv0 : 0 < v) (hv1 : v < 1) (hhG : h '' G ⊆ layer d v) :
    closure (Rset k) ⊆ h.symm '' layer d v := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hAT := (hagopian75_lemma1 hX hi).1
  obtain ⟨b, hb, hbS⟩ := exists_image_map h.symm hG
  set U := layer b v with hU
  have hUeq : U = h.symm '' layer d v := hbS {v}
  rw [← hUeq]
  have hUG' : U ⊆ h.symm '' G := fun _ ⟨y, _, hy⟩ => hy ▸ y.2
  have hGU : G ⊆ U := by
    intro x hx
    rw [hUeq]
    exact ⟨h x, hhG ⟨x, hx, rfl⟩, h.symm_apply_apply x⟩
  have hG'c : Fold.Q78.IsContinuum (h.symm '' G) := by
    obtain ⟨a', b', hab'⟩ := hb.1; exact hab'.1
  have hUc : IsClosed U := (isCompact_img hb.isCompact hb.2.1.1 isClosed_singleton).isClosed
  -- every extension away from `k⁻¹(0)` lies in `U`
  have hext : ∀ F', IsExtensionAway E (layer k 0) F' → F' ⊆ U := by
    rintro F' ⟨hEF', dF, hdF, hdF0⟩
    have hF'c : Fold.Q78.IsContinuum F' := by obtain ⟨a', b', hab'⟩ := hdF.1; exact hab'.1
    obtain ⟨s, hs0, hseg, -⟩ := hagopian76_initial_segment hX hi hE hdF hEF' hdF0
    obtain ⟨V₀, hV₀, hV₀e⟩ := layerSet_eq_inter_open hdF.2.1.1 (isOpen_Iio (a := s))
    have hOE : layerSet dF (Iio s) ⊆ E := by
      rw [← hseg]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, ⟨unitInterval.nonneg', le_of_lt hy⟩, rfl⟩
    obtain ⟨x0, hx0⟩ := layer_nonempty hdF.2.1.2.1 0
    have hx0O : x0 ∈ layerSet dF (Iio s) := by
      obtain ⟨y, hy, rfl⟩ := hx0
      exact ⟨y, by rw [mem_preimage, mem_singleton_iff.1 hy]; exact hs0, rfl⟩
    have hx0E := hOE hx0O
    have hx0G' : x0 ∈ h.symm '' G := hUG' (hGU (hEG hx0E))
    have hWc := isContinuum_inter_of_HU hHU hF'c hG'c ⟨x0, hEF' hx0E, hx0G'⟩
    have hx0V : x0 ∈ V₀ := by rw [hV₀e] at hx0O; exact hx0O.2
    have hW := continuum_subset_layer_of_open hX hi hb hWc inter_subset_right hV₀
      ⟨x0, ⟨hEF' hx0E, hx0G'⟩, hx0V⟩ (by
        rintro p ⟨⟨hpF, -⟩, hpV⟩
        exact hGU (hEG (hOE (by rw [hV₀e]; exact ⟨hpF, hpV⟩))))
    have hFG' : F' ⊆ h.symm '' G := by
      refine subset_of_meets_avoids hHU hAT hG'c hb.2.1 hF'c ⟨x0, hx0G', hEF' hx0E⟩ ?_
      rw [disjoint_left]
      rintro p hpF hpX
      have hpG : p ∈ h.symm '' G := by
        rcases hpX with ⟨y, -, rfl⟩ | ⟨y, -, rfl⟩ <;> exact y.2
      have hpU := hW ⟨hpF, hpG⟩
      rcases hpX with hp0 | hp1
      · exact absurd (layer_param_eq hp0 hpU) (ne_of_lt hv0)
      · exact absurd (layer_param_eq hp1 hpU) (ne_of_gt hv1)
    exact fun p hp => hW ⟨hp, hFG' hp⟩
  have hRU : extUnion E (layer k 0) ⊆ U := by
    rintro x ⟨F', hF', hx⟩; exact hext F' hF' hx
  rw [← hagopian76_closure_extUnion hX hi hE]
  exact closure_minimal hRU hUc

/-- **A. `Property3End` from `Cl R(E) = M`** (the batch-169 open item C.1,
`closure_Rset_eq_univ`): `Cl R(E)` would lie in a layer of `h⁻¹[G]`, a proper subset of `M`. -/
theorem property3End_of_closure_Rset (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hcl : closure (Rset k) = univ) (ε₁ : ℝ) : Property3End d ε₁ := by
  intro h _ v hv0 hv1 hhG
  have hsub := closure_Rset_subset_of_translate hX hi hE hG hEG h hv0 hv1 hhG
  rw [hcl] at hsub
  obtain ⟨p, hp⟩ := layer_nonempty hG.2.1.2.1 0
  obtain ⟨q, hq, hqp⟩ := hsub (mem_univ (h.symm p))
  have : q = p := h.symm.injective hqp
  subst this
  exact absurd (layer_param_eq hp hq) (ne_of_lt hv0)

/-- **A. `Property3End` from the dichotomy** (`RsetDichotomy`, batch 169: a translate of `R(E)`
meeting `R(E)` equals it). For an extension `G` of `E` away from `k⁻¹(0)`: `h[R(E)] ⊆ h[Cl R(E)] ⊆
d⁻¹(v) ⊆ G ⊆ R(E)`, so the dichotomy gives `R(E) ⊆ G`, against Lemma 4 (`G` has a proper
extension). -/
theorem property3End_of_dichotomy (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) (hD : RsetDichotomy k) (ε₁ : ℝ) : Property3End d ε₁ := by
  intro h _ v hv0 hv1 hhG
  have hsub := closure_Rset_subset_of_translate hX hi hE hG hEG h hv0 hv1 hhG
  have hGext : IsExtensionAway E (layer k 0) G := ⟨hEG, d, hG, hX0⟩
  have hGR : G ⊆ Rset k := fun x hx => Or.inl ⟨G, hGext, hx⟩
  have hCG : layer d v ⊆ G := fun _ ⟨y, _, hy⟩ => hy ▸ y.2
  have hhR : h '' Rset k ⊆ G := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hsub (subset_closure hx)
    have : y = h x := by rw [← hyx, Homeomorph.apply_symm_apply]
    exact hCG (this ▸ hy)
  obtain ⟨e, he⟩ := layer_nonempty hE.2.1.2.1 0
  have heR : (e : M) ∈ Rset k := hGR (hEG (show e ∈ E from by obtain ⟨y, -, rfl⟩ := he; exact y.2))
  have hRG : Rset k ⊆ G := by
    rw [← hD h ⟨h e, mem_image_of_mem h heR, hGR (hhR (mem_image_of_mem h heR))⟩]
    exact hhR
  obtain ⟨H, hH, hGH⟩ := (hagopian76_lemma4 hX hi hE).2 G hGext
  exact hGH.2 (fun x hx => hRG (Or.inl ⟨H, hH, hx⟩))

/-- **A. Property 3 from `Cl R(E) = M`.** -/
theorem hagopian76_property3_of_closure (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) (hcl : closure (Rset k) = univ) :
    ∃ c > 0, c ≤ 1 ∧ ∀ B : Set M, IsPreconnected B →
      (∀ x ∈ B, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({3 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      (∃ x ∈ closure B, π (x : Pt) ∈ F '' (({19 / 22} : Set ℝ) ×ˢ Ioc 0 c)) →
      ∀ v : unitInterval, 0 < v → v < 1 → ¬ closure B ⊆ layer d v :=
  hagopian76_property3_of_end hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hEG hX0
    (property3End_of_closure_Rset hX hi hE hG hEG hcl ε₁)

omit [CompactSpace M] [ConnectedSpace M] in
/-- **B. Positions through the bottom edge and through `I₂`** (commission 172 §1.B; p. 349:
"Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`"). Set-up of `crossing_sides`, with `π`
a quotient map. For a compact `Z` (e.g. `Cl B`, or `toPt K` for a subcontinuum `K` missing `E`)
missing `π⁻¹` of the bottom edge and `π⁻¹[I₂]`, there are heights `u₁ > 0` and `u₂ ∈ (0, w₂)` such
that every point `P` of `π⁻¹[D] − Z`
* whose component in `π⁻¹[D] − Z` has closure meeting `π⁻¹` of the bottom edge is **below** `Z`;
* whose component has closure meeting `π⁻¹[I₂]` is **above** `Z`.

*Shape (left to me):* the two edge cases of the covering, together; the low strip of
`crossing_bottom_below` is derived (`rect_domain_low`), not assumed. The `I₂` case is new
(`top_component_above_aux`, by the inner collar from Schoenflies). Components whose closure meets
`π⁻¹[J]` only in the side segments (the side edges and pockets) are not covered: open. -/
theorem crossing_sides_cover_schoenflies {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDo : IsOpen D')
    (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D')) {Z : Set Pt} (hZc : IsCompact Z)
    (hZb : Disjoint Z (π ⁻¹' (F '' (Icc a b ×ˢ {0})))) (hZI : Disjoint Z (π ⁻¹' I₂))
    {t₀ w₂ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂)) :
    ∃ u₁ > 0, ∃ u₂ ∈ Ioo 0 w₂, ∀ P ∈ π ⁻¹' (F '' D') \ Z,
      ((closure (connectedComponentIn (π ⁻¹' (F '' D') \ Z) P) ∩
          π ⁻¹' (F '' (Icc a b ×ˢ {0}))).Nonempty → P ∈ belowSet π F D' t₀ u₁ Z) ∧
      ((closure (connectedComponentIn (π ⁻¹' (F '' D') \ Z) P) ∩ π ⁻¹' I₂).Nonempty →
          P ∈ aboveSet π F D' t₀ u₂ w₂ Z) := by
  -- the low strip
  have hIc : IsCompact (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) := by
    obtain ⟨-, φ, hφ, hφr, -, -⟩ := hI
    rw [← hφr]; exact isCompact_range hφ.continuous
  obtain ⟨c₀, hc₀, -, hc₀I⟩ := exists_height_below hIc fun z hz => hz.1.2.1
  have hlow : ∃ c₀ > 0, Ioo a b ×ˢ Ioo 0 c₀ ⊆ D' :=
    ⟨c₀, hc₀, rect_domain_low (r := ((a, r₂) : ℝ × ℝ)) (s := ((b, s₂) : ℝ × ℝ)) hab hDR hDf hc₀
      fun z hz => (hc₀I z hz).le⟩
  obtain ⟨u₁, hu₁, hbot⟩ := crossing_bottom_below hπ hπS hγπ hF ha hb hc1 hFDo hDR hlow hZc hZb
    ht₀
  obtain ⟨u₂, hu₂, htop⟩ := top_component_above_aux hπ hπS hγπ hF ha hab hb hc1 hI hIs hIR hDo hDR
    hDf hFDo hZc hZI ht₀ hw₂ hFw hseg
  exact ⟨u₁, hu₁, u₂, hu₂, fun P hP => ⟨hbot P hP, htop P hP⟩⟩

end Thm1

/-! ## Open items

The obstructions are in `OPEN.md` (batch 172) and in `doc/batches/REPORT-batch172.md`.

**OPEN (A, `Property3End`).** `hagopian76_property3_translate` reduces Property 3 to excluding an
`ε₁`-homeomorphism `h` with `h[G] ⊆ d⁻¹(v)`, `0 < v < 1` (`hagopian76_property3_of_end`). Such an
`h` puts `Cl R(E)` inside the layer `h⁻¹[d⁻¹(v)]` of `h⁻¹[G]` (`closure_Rset_subset_of_translate`),
so `Property3End` follows from `Cl R(E) = M` (`property3End_of_closure_Rset`) and from the
dichotomy (`property3End_of_dichotomy`); both of these are open (batch 169, C.1). Without them
nothing available excludes a proper indecomposable `Cl R(E)` with `h[Cl R(E)] ⊆ d⁻¹(v) ⊆ G`.

theorem property3_end … : Property3End d ε₁ := by
  sorry

**OPEN (B, side edges and pockets).** Components of `π⁻¹[D] − Z` whose closure meets `π⁻¹[J]` only
in the side segments `{a} × [0, r₂]`, `{b} × [0, s₂]` are not classified. For a pocket (a component
of `D′ − Z′` whose closure meets `J − Z′` only between two points of `Z′` on one side) neither
`belowSet` nor `aboveSet` is reached by any argument available here.

theorem crossing_sides_cover' … :
    π ⁻¹' (F '' D') \ Z ⊆ belowSet π F D' t₀ u₁ Z ∪ aboveSet π F D' t₀ u₂ w₂ Z := by
  sorry

**OPEN (C, the ends of a crossing component).** Not proved.

theorem crossing_component_ends … :
    (toPt (closure B) ∩ L 1).Nonempty ∧ (toPt (closure B) ∩ L 9).Nonempty := by
  sorry

**OPEN (D, T15–T17 and the assembly).** Not reached: "`I` is finite" (from Property 3), Property 4
(the induction), Bing's lemma and the first-component argument are not formalized.

theorem hagopian76_T15_T17 … : False := by
  sorry

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
