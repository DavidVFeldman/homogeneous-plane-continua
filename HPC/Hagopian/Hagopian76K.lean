import HPC.Hagopian.H76Crosscut
import HPC.Hagopian.H76TwoComposants

/-!
# Batch 166 skeleton: Hagopian 1976, Theorem 1 — `D` as a Jordan domain; the low part `K₀` of
# `K`; "`L − {L₁, L₁₁}` follows `Cl B`"; Property 3; T12, T13; then T15–T17 and the assembly

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349; Mazurkiewicz 1929
(`doc/sources/mazurkiewicz1929.pdf`) for T12. Abscissae of `p₁, …, p₅`: `3/22, 7/22, 11/22, 15/22,
19/22`. Lean index of Hagopian's `Lᵢ` is `i − 1`. Skeleton as delivered:
`doc/batches/skeletons/Hagopian76K.lean`.

Supporting files: `H76Domain` (A, plane topology), `H76DCollar` (A in the plane through the collar,
B), `H76Crosscut` (B: `K₀` is a cross-cut of `D`), `H76TwoComposants` (E, part). Shape changes are recorded at each statement and in `doc/batches/REPORT-batch166.md`. Items C–F
are open (commented out at the end, obstructions in `OPEN.md`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## A. `D` as a Jordan domain (plane topology, in collar coordinates) -/

/-- **The domain under a crossing arc.** For an arc `I` as produced by `rect_crossing`, the simple
closed curve `I ∪ (bottom edge) ∪ (left edge up to r) ∪ (right edge up to s)` bounds an open
connected bounded set inside the open rectangle, with that curve as frontier (`jordan_curve_theorem`;
the complement of the closed rectangle is connected and unbounded and misses the curve). Hagopian's
`D` (p. 346) is the image of this set under the collar `F`. (Statement unchanged.) -/
theorem rect_domain {a b c : ℝ} (hab : a < b) (hc : 0 < c) {r s : ℝ × ℝ} {I : Set (ℝ × ℝ)}
    (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hr : r.1 = a) (hs : s.1 = b)
    (hIs : I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s}) :
    ∃ D : Set (ℝ × ℝ), IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      D ⊆ Ioo a b ×ˢ Ioo 0 c ∧
      frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
        ({b} : Set ℝ) ×ˢ Icc 0 s.2 :=
  rect_domain_aux hab hc hI hIR hr hs hIs

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **T8, the domain** (p. 346): "Let `D` be the bounded complementary domain of
`I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩` in `R²`."

*Shape (left to the batch):* for any arc `I₂` with the properties that `hagopian76_T7` gives (over
`[a, b] ⊆ (0, 1)`, at height `c ≤ 1`), with `r = F(a, r₂)`, `s = F(b, s₂)`:
* in collar coordinates, `I₂` pulls back to an arc `I` from `(a, r₂)` to `(b, s₂)`, and `D′` is the
  bounded complementary domain of `I ∪ [a, b] × {0} ∪ {a} × [0, r₂] ∪ {b} × [0, s₂]`
  (`rect_domain`): open, connected, inside the open rectangle, with that curve as frontier;
* `D = F[D′]` is open, connected and bounded, lies in `F[(a, b) × (0, c)]`, and its frontier is
  `I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩` (`= I₂ ∪ F[[a, b] × {0}] ∪ F[{a} × [0, r₂]] ∪ F[{b} × [0, s₂]]`);
  so `D` is Hagopian's "bounded complementary domain of `I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩`";
* `π⁻¹[D]` is open, and `D` meets `π[M]` (`M_meets_above`, which needs a strip below `γ([a, b])`
  missing `π[M]`: hypothesis `hbelow`, given by `hagopian76_T6_placed` / `hagopian76_I1`). -/
theorem hagopian76_D (hi : ¬ IsDecomposableSpace M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r s : Pt} {I₂ : Set Pt} (hI : TArc r s I₂) (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c))
    (hIs : I₂ ∩ F '' (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s})
    (hr : r ∈ F '' (({a} : Set ℝ) ×ˢ Ioc 0 c)) (hs : s ∈ F '' (({b} : Set ℝ) ×ˢ Ioc 0 c)) :
    ∃ (r₂ s₂ : ℝ) (D' : Set (ℝ × ℝ)), r₂ ∈ Ioc 0 c ∧ s₂ ∈ Ioc 0 c ∧ F (a, r₂) = r ∧
      F (b, s₂) = s ∧ TArc (a, r₂) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∧
      (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {(a, r₂), (b, s₂)} ∧
      IsOpen D' ∧ IsConnected D' ∧ D' ⊆ Ioo a b ×ˢ Ioo 0 c ∧
      frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂ ∧
      IsOpen (F '' D') ∧ IsConnected (F '' D') ∧ Bornology.IsBounded (F '' D') ∧
      F '' D' ⊆ F '' (Ioo a b ×ˢ Ioo 0 c) ∧
      frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂) ∧
      IsOpen (π ⁻¹' (F '' D')) ∧ (F '' D' ∩ π '' M).Nonempty := by
  obtain ⟨r₂, s₂, D', hr₂, hs₂, hFr, hFs, hIarc, hIends, hDo, hDc, hDR, hDf, hFDo, hFDc, hFDb, hFDR,
    hFDf⟩ := hagopian76_D_aux hF ha hab hb hc hc1 hI hIR hIs hr hs
  refine ⟨r₂, s₂, D', hr₂, hs₂, hFr, hFs, hIarc, hIends, hDo, hDc, hDR, hDf, hFDo, hFDc, hFDb, hFDR,
    hFDf, hFDo.preimage hπ.continuous, ?_⟩
  obtain ⟨c₀, hc₀, -, hc₀I⟩ := exists_height_below hIarc.isCompact fun z hz => hz.1.2.1
  have hlow := rect_domain_low (r := ((a, r₂) : ℝ × ℝ)) (s := ((b, s₂) : ℝ × ℝ)) hab hDR hDf hc₀
    fun z hz => (hc₀I z hz).le
  obtain ⟨p, ⟨z, hz, rfl⟩, hpM⟩ :=
    M_meets_above hi hE hπ.continuous hπS hγπ hF ha hab hb hbelow hc₀
  exact ⟨F z, ⟨z, hlow hz, rfl⟩, hpM⟩

/-! ## B. The low part of `K` -/

omit [CompactSpace M] [ConnectedSpace M] in
/-- **`K₀`** (p. 347: "Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets both
`π⁻¹(p₃)` and `π⁻¹[I₂]`"). With `w` the lowest point of `I₂` on the vertical over `t₀` (Hagopian:
`t₀ = 11/22`), `K₀ = π⁻¹F[{t₀} × (0, w₂)]`.

*Shape (left to the batch):* for `D = F[D′]` as in `hagopian76_D` (only the coordinate properties of
`D′` are used) and any `t₀ ∈ (a, b)`, there is `w₂ ∈ (0, c]` with `F(t₀, w₂) ∈ I₂`, the open
segment `{t₀} × (0, w₂)` misses the pull-back of `I₂` and lies in `D′`, and `K₀`
* lies in `π⁻¹[D ∩ F[{t₀} × (0, c)]]` (Hagopian's `π⁻¹[D ∩ ⟨p₃, q₃⟩]`) and is a connected
  component of it: connected, and every connected subset of `π⁻¹[D ∩ F[{t₀} × (0, c)]]` meeting it
  lies in it;
* misses `E` (so it lies in `R² − E`; `π` maps it homeomorphically onto an open arc);
* has closure meeting `π⁻¹(p₃) = k⁻¹(t₀)` and `π⁻¹[I₂]`.
Wherever a separation by `K` is used, use `hagopian76_T11` for the whole section. -/
theorem hagopian76_K0 {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt} (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (t₀ : unitInterval) (ht₀ : (t₀ : ℝ) ∈ Ioo a b) :
    ∃ w₂ ∈ Ioc 0 c, F ((t₀ : ℝ), w₂) ∈ I₂ ∧
      Disjoint (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∧
      ({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D' ∧
      π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂)) ⊆
        π ⁻¹' (F '' D' ∩ F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 c)) ∧
      (∀ S ⊆ π ⁻¹' (F '' D' ∩ F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 c)), IsPreconnected S →
        (S ∩ π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))).Nonempty →
        S ⊆ π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) ∧
      IsPreconnected (π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) ∧
      Disjoint (π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) (toPt E) ∧
      (closure (π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) ∩ toPt (layer k t₀)).Nonempty ∧
      (closure (π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) ∩ π ⁻¹' I₂).Nonempty :=
  K0_aux hE hπ hπS hγπ hF ha hab hb hc1 hI hDo hDR hDf t₀ ht₀

omit [CompactSpace M] [ConnectedSpace M] in
/-- **`K₀` is a cross-cut of `D`** (addition to item B; used in T12 and T17 in the form "a component
of `M ∩ π⁻¹[D]` whose closure meets both side edges meets `K`"). For `D = F[D′]` as in
`hagopian76_D` and `K₀ = π⁻¹F[{t₀} × (0, w₂)]` as in `hagopian76_K0`: no connected subset of
`π⁻¹[D] − K₀` has closure meeting both `π⁻¹F[{a} × (0, r₂)]` and `π⁻¹F[{b} × (0, s₂)]` (Hagopian's
`π⁻¹[⟨p₁, r⟩]`, `π⁻¹[⟨p₅, s⟩]` without their two ends). This is the separation that the single
component `K` does provide; the separation of `L₂` from `L₁₀` (T11) is still carried by the whole
section (`hagopian76_T11`). -/
theorem hagopian76_K0_crosscut {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    {t₀ w₂ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    {S : Set Pt} (hS : IsPreconnected S)
    (hSD : S ⊆ π ⁻¹' (F '' D') \ π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂)))
    (hL : (closure S ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty)
    (hR : (closure S ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty) : False :=
  K0_crosscut_aux hπ.continuous hF ha hab hb hc1 hI hIs hDo hDR hDf ht₀ hw₂ hFw hseg hS hSD hL hR

end Thm1

/-! ## C–F. "Follows `Cl B`", Property 3, T12, T13, T15–T17 and the assembly (open)

The obstructions are in `OPEN.md` (batch 166) and in `doc/batches/REPORT-batch166.md` §1.C–F.

**OPEN (C, `hagopian76_T9_follows`).** "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`" (p. 346).
Step 2 of the route of commission 166 §1.C does not go through as stated. Write
`G = h⁻¹[Cl B] ⊆ E` and `u = min k[G]`. The end of `Cl B` is `h[G ∩ k⁻¹(u)]`, part of a layer and not
a whole layer. Take a point `x` of it in `π⁻¹[D]`. Boundary bumping in `h[k⁻¹[0, u]]` gives a
continuum through `x` inside `M ∩ π⁻¹[D]`, hence inside `B ⊆ h[G]`, hence inside the layer
`h[k⁻¹(u)]`. That is no contradiction unless `x` is a limit of `h[k⁻¹[0, u)]`, and a point of a
layer need not be such a limit. Shape proposal:

theorem hagopian76_T9_follows … (B : Set M) (hB : B ∈ components (M ∩ π⁻¹ D)) (hB48 : …) :
    ∃ (H : Set M) (dH : H → unitInterval), closure B = H ∧ IsMinimalAdmissible H dH ∧
      Follows (fun j : Fin 9 => L (j.succ.castSucc)) dH := by sorry

**OPEN (D, `hagopian76_property3`).** Shape of report 165 §5, with `D = F[D′]` of `hagopian76_D`.
Missing: the least `v` (the hyperspace limit) and the crossing property under the shift `g`.

(Batch 167: Hagopian's `x` and T12 (1)–(2) are proved in `Hagopian76L.lean`; T12 (3) stays open.)

**OPEN (E, `hagopian76_T12`).** "Inaccessible" is used nowhere after the choice of `p`, `q` (report
§1.E); what is used is: `p`, `q ∈ K ∩ W`, not in `R(E)`, in distinct composants of `Cl R(E)`. In `W`
alone such points exist without Mazurkiewicz (`exists_two_composants_in_open`). On `K` they need
points of `Cl R(E)` on `K₀` arbitrarily close to `x`: a component of `M ∩ π⁻¹[D]` reaching both side
edges meets `K₀` (`hagopian76_K0_crosscut`), but that such components exist near `x` is item C, and
that they meet `K₀` near `x` (rather than high up on `K₀`) is not argued. "By Property 1, `R(E)`
intersects an arc in `K` that is irreducible between `C` and the `q`-component …" is unargued.

**OPEN (F, `hagopian76_T13`, `hagopian76_T15_T17`, `hagopian76_theorem1 : Hagopian76Thm1`).**
Wait on C, D, E.
-/

end HPC.Hagopian
