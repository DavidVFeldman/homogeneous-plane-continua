import HPC.Hagopian.H76X2n

/-!
# Batch 175: Hagopian 1976, Theorem 1 — components through the middle; no deep pockets;
# `x₂ₙ = 1`; Property 4; the induction; the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–349. Routes: commission 175 §1.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76T.lean`.

Supporting files:
* `H76Pocket` — boundary bumping inside an extension; every component of `G ∩ π⁻¹[D]` through a
  point over the middle is crossing or meets `d⁻¹(1)` (P3 by the shortcut of its last bullet); P2;
  no deep pockets; the tail beyond the last crossing interval;
* `H76X2n` — the named `Prop` `TailCutKeepsSep` and `x₂ₙ = 1` from it.

"The middle" is the abscissa range `[3/8, 5/8]` (shape change: the commission's
`[3/22 + 2/11, 19/22 − 2/11] = [7/22, 15/22]` is too wide for coarse monotonicity at one eleventh,
see `component_over_middle_crossing`). Shapes are recorded at each statement and in
`doc/batches/REPORT-batch175.md`. Items left open are commented out at the end, with the
obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **P2. A translate through a point over the middle, inside `F`** (commission 175 §1 P2). Set-up
of `hagopian76_property3` (without `E ⊆ G`). There is `c > 0` such that every `y ∈ M` over
`F[[3/8, 5/8] × [0, c]]` is `h(x)` for an `ε₁`-homeomorphism `h` (Property 1, after link control)
and `x ∈ E` with `k(x) ∈ (3/11, 8/11]`; and if `y ∈ G`, every piece `h[k⁻¹[S]]` (`S ∋ k(x)` a closed
interval of parameters `≥ 3/22`) missing the far end set `d⁻¹(1)` lies in `G`.

*Shape (left to me):* the far end set is a hypothesis on the piece, not removed. It cannot be removed
in general: an extension can end over the middle (cut a longer extension at a layer there). The
commission's repeated-extension idea (P2, "the delicate case") is not needed for P3. -/
theorem translate_through_point_in_F (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (y : M) (z : ℝ × ℝ), z ∈ Icc (3 / 8 : ℝ) (5 / 8) ×ˢ Icc 0 c →
      π (y : Pt) = F z → ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ ∃ x : E, h x = y ∧
        3 / 11 < (k x : ℝ) ∧ (k x : ℝ) ≤ 8 / 11 ∧
        ∀ S : Set unitInterval, IsClosed S → IsPreconnected S → k x ∈ S →
          (∀ s ∈ S, (3 / 22 : ℝ) ≤ s) → y ∈ G → Disjoint (h '' layerSet k S) (layer d 1) →
          h '' layerSet k S ⊆ G :=
  translate_through_middle_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hX0

/-- **P3. Every component of `F ∩ π⁻¹[D]` through a point over the middle is crossing, or meets the
far end set** (commission 175 §1, P3 by the shortcut of its last bullet). Set-up of
`hagopian76_property3` (without `E ⊆ G`). There is `c > 0` such that for every domain `D = F[D′]`
of height `c₁ ≤ c` (`IsCrossRegion`) and every `y ∈ G` over `D` at abscissa in `[3/8, 5/8]`, the
component `C` of `G ∩ π⁻¹[D]` through `y` meets `d⁻¹(1)` or is a crossing component.

*Shape (left to me):*
* the exception "`C` meets `d⁻¹(1)`" is needed (an extension may end over the middle);
* the middle is `[3/8, 5/8]`: `y = h(x)` only gives `k(x)` within two elevenths of the abscissa of
  `y`, and the halves of `h[E]` must stay one eleventh clear of the opposite side;
* P1 (the layers of `F` along a translate) is not used.

*Proof:* the two halves `h[k⁻¹[[0, k(x)]]]`, `h[k⁻¹[[k(x), 1]]]` of the translate are bumped inside
`G` (`bump_in_extension`: in `K ∩ G`, a continuum by hereditary unicoherence; if `K ∩ G ⊆ π⁻¹[D]`,
no hair for `G` makes it meet `d⁻¹(1)`). The frontier point is not over the axis (no hair for `E`
would put the closure, and so `y`, in `E`) and not over the far side (coarse monotonicity). -/
theorem component_over_middle_crossing (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ y ∈ crossSet G π F D', (∃ z ∈ D', z.1 ∈ Icc (3 / 8 : ℝ) (5 / 8) ∧ π (y : Pt) = F z) →
      (connectedComponentIn (crossSet G π F D') y ∩ layer d 1).Nonempty ∨
        IsCrossingComponent G π F c₁ D' (connectedComponentIn (crossSet G π F D') y) :=
  component_over_middle_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hX0

/-- **P3′. When the far end set is not over `D`, every component through the middle crosses.** -/
theorem component_over_middle_crossing_of_end (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      Disjoint (layer d 1) (crossSet G π F D') →
      ∀ y ∈ crossSet G π F D', (∃ z ∈ D', z.1 ∈ Icc (3 / 8 : ℝ) (5 / 8) ∧ π (y : Pt) = F z) →
        IsCrossingComponent G π F c₁ D' (connectedComponentIn (crossSet G π F D') y) :=
  component_over_middle_crossing_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hX0

/-- **A. `cover_pocket_middle`: no deep pockets** (commission 175 §1 P3–P4). Set-up of
`component_over_middle_crossing`. A component of `G ∩ π⁻¹[D]` that is not crossing and misses the
far end set `d⁻¹(1)` has no point over `D` at abscissa in `[3/8, 5/8]`.

*Shape (left to me):* "pocket" is read as "non-crossing component"; the exception for components
meeting `d⁻¹(1)` is the one of P3. The induction's `L₆` (abscissae `(5/11 − η, 8/11 + η)`) is not
inside `[3/8, 5/8]`; see the report. -/
theorem cover_pocket_middle (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ w ∈ crossSet G π F D', ¬ IsCrossingComponent G π F c₁ D'
        (connectedComponentIn (crossSet G π F D') w) →
      Disjoint (connectedComponentIn (crossSet G π F D') w) (layer d 1) →
      ∀ y ∈ connectedComponentIn (crossSet G π F D') w,
        ¬ ∃ z ∈ D', z.1 ∈ Icc (3 / 8 : ℝ) (5 / 8) ∧ π (y : Pt) = F z :=
  cover_pocket_middle_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hX0

/-- **B, first step: the tail beyond the last crossing interval** (commission 175 §1 P4: "Then
`d⁻¹((t, 1])` meets `π⁻¹[D]` only in non-crossing components, which by P3 avoid the middle").
Set-up of `component_over_middle_crossing`. If every `[x, y] ∈ I` has `y < t`, every point of `G`
over `D` at abscissa in `[3/8, 5/8]` with parameter `> t` lies in a component of `G ∩ π⁻¹[D]` that
meets `d⁻¹(1)`.

*Shape (added):* with the exception of P3, the tail components reaching the middle are exactly
those that meet the far end set. -/
theorem hagopian76_tail_middle (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    (hX0 : layer d 0 = layer k 0) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      ∀ t : unitInterval, (∀ p ∈ crossingIntervals d π F c₁ D', p.2 < t) →
      ∀ (y : M) (hy : y ∈ crossSet G π F D'), t < d ⟨y, hy.1⟩ →
      (∃ z ∈ D', z.1 ∈ Icc (3 / 8 : ℝ) (5 / 8) ∧ π (y : Pt) = F z) →
        (connectedComponentIn (crossSet G π F D') y ∩ layer d 1).Nonempty :=
  tail_middle_reaches_end_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hX0

/-- **B. `x₂ₙ = 1` for Hagopian's `F`, conditional on the cutting step** (p. 348: "Note that …
`x₂ₙ = 1`"). Set-up of `hagopian76_property3`, with `G ≠ E` separating `p` from `q` in `O` and
irreducible with respect to that among extensions of `E` away from `k⁻¹(0)` (T13,
`hagopian76_T13_uncond`). There is `c > 0` such that for every domain of height `c₁ ≤ c`:
`TailCutKeepsSep` implies `LastIntervalReachesOne`.

*Shape (left to me):* conditional; the named `Prop` `TailCutKeepsSep` is exactly what remains (the
plane-topology step of P4). `G ≠ E` holds for Hagopian's `F`, since `E` separates nothing
(`hagopian76_property4_base`). -/
theorem hagopian76_x2n_eq_one_of_cut (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLch : IsPlaneChain L)
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j)
    (hP1 : ∀ y : M, ∀ i : Fin 11, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 9 → (y : Pt) ∈ L i →
      ∃ h : M ≃ₜ M, (∀ v, dist v (h v) < ε₁) ∧ y ∈ h '' E ∧
        ∀ j : Fin 11, toPt (h '' piece k ((j : ℕ) + 1)) ⊆ L j)
    {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hEG : E ⊆ G)
    (hX0 : layer d 0 = layer k 0) (hne : G ≠ E) {O : Set Pt} {p q : Pt}
    (hsep : SepIn O (toPt G) p q)
    (hirr : ∀ F', IsExtensionAway E (layer k 0) F' → SepIn O (toPt F') p q → F' ⊆ G → F' = G) :
    ∃ c > 0, c ≤ 1 ∧ ∀ (c₁ : ℝ) (D' : Set (ℝ × ℝ)), c₁ ≤ c → IsCrossRegion M π F c₁ D' →
      TailCutKeepsSep E d π F c₁ D' O p q → LastIntervalReachesOne d π F c₁ D' := by
  obtain ⟨c, hc, hc1, hfin⟩ := I_finite_aux hX hi hE he hend hπ hπS hγπ hF hLch hEL hLG hP1 hG hEG
    hX0
  exact ⟨c, hc, hc1, fun c₁ D' hc₁ hR hcut =>
    x2n_eq_one_of_cut hX hi hE hG hEG hX0 hne (hfin c₁ D' hc₁ hR) hsep hirr hcut⟩

end Thm1

/-! ## Open items

The obstructions are in `OPEN.md` (batch 175) and in `doc/batches/REPORT-batch175.md`.

**P1 (`layer_eq_translate_layer`): not formalized, not needed.** P3 is proved by the shortcut of its
last bullet, which uses neither the layer function `φ` nor the triod argument. Hagopian 1975
Lemma 1 (atriodicity) enters P3 only through `subset_of_meets_avoids` (no hair for `G`).

theorem layer_eq_translate_layer … : layer d (φ t) = h '' layer k t := by
  sorry

**OPEN (B, the cutting step `TailCutKeepsSep`).** If `G` separates `p` from `q` in `O = π⁻¹[D]`, so
does `d⁻¹[[0, t]]` for `t < 1` beyond every interval of `I`. `hagopian76_tail_middle` shows that the
tail `d⁻¹((t, 1])` meets the middle only in components reaching `d⁻¹(1)`; it does not show that the
tail is not needed for the separation:
* a tail component reaching `d⁻¹(1)` may reach the middle;
* a shallow tail component (off the middle) can still meet a side segment, and whether it can be
  part of a barrier between `p` and `q` is a question about plane separation (Janiszewski, compact
  form), which the project has only for polygonal sets (`janiszewski_polygonal`).

theorem tailCutKeepsSep … : TailCutKeepsSep E d π F c₁ D' (π ⁻¹' (F '' D')) p (f p) := by
  sorry

**OPEN (C, Property 4 for `[x₂ₙ₋₁, x₂ₙ]`).** Clause (2), only the last block separates, is the
cutting step for the gaps between blocks as well as the tail (same obstruction as B). Clause (1)
needs the point `yₙ ∈ K` and the essential-continuum set-up of T12.

theorem hagopian76_property4_top … : ∃ yₙ ∈ K, IsEssential (closure Cₙ) (h '' Rset E) ∧
    SepIn (π ⁻¹' (F '' D')) (toPt (layerSet d (Icc x₂ₙ₋₁ x₂ₙ))) yₙ (f yₙ) := by
  sorry

**OPEN (D, the induction, Cases 1–2).**
* Pockets: `cover_pocket_middle` covers the abscissae `[3/8, 5/8]` for components missing `d⁻¹(1)`.
  The induction needs `f(yᵢ₋₁) ∈ L₆` (abscissae up to `8/11 + η`), and blocks `d⁻¹[[x, y]]` that are
  not whole extensions; both are outside what is proved.
* `N` and `ε₂`: `N` lies in the extension `L` of `Cl Cᵢ`, not of `E`; P2 places points of `L` over
  the middle on translates of `E`, but "`L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and `Cl Cᵢ`" still needs
  Property 3 for `L` and the first-component argument.

theorem hagopian76_property4_step … (hI : Property4 … i) : Property4 … (i - 1) := by
  sorry

**OPEN (E, the assembly).** Needs B–D. No conditional form is stated beyond
`hagopian76_x2n_eq_one_of_cut`: Property 4 and its step are not formalized as named `Prop`s with
the T12 set-up.

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
