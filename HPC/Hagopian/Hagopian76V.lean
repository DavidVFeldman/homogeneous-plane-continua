import HPC.Hagopian.H76T12Exists

/-!
# Batch 177: Hagopian 1976, Theorem 1 — the strand lemma, and the endgame rebuilt on it

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 346–349. Route: commission 177 §2–§3.
Skeleton as delivered: `doc/batches/skeletons/Hagopian76V.lean`.
The constants are chosen in the order `n → θ(n) → δ′ (Effros) → η → c(n) → D → ε₂ → ε₃`.

Supporting files:
* `H76Strand` — `θ(n)`; the structure `StrandConst` (S0–S1); S2 (`strand_closure_subset`); S3
  (`strand_crossing`);
* `H76StrandUse` — the inner middle (`strand_inner_middle`); S5; S6; components in `M` and in the
  plane; strands are essential (`strand_essential`);
* `H76T12Exists` — `π` pulls continua back to continua; `Fr D` is a continuum; `T12Data` exists; the
  batch-176 conditional form corrected (`hagopian76_T15_T17_cond_fix`) and with the package and `Y`
  discharged (`hagopian76_T15_T17_cond2`).

Items stated as `True` in the skeleton were *shape left to me*; the shapes are recorded at each
statement and in `doc/batches/REPORT-batch177.md`. Items left open are commented out at the end,
with the obstructions in `OPEN.md`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Thm1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [CompactSpace M] [ConnectedSpace M] in
/-- **θ(n)**: points of `E` whose parameters differ by at least `1/n` are at least `θ` apart.
(Statement unchanged.) *Proof:* the set of such pairs is compact and misses the diagonal. -/
theorem exists_param_sep {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    (n : ℕ) (hn : 0 < n) :
    ∃ θ > 0, ∀ a b : E, 1 / (n : ℝ) ≤ |(k a : ℝ) - (k b : ℝ)| →
      θ ≤ dist ((a : M) : Pt) ((b : M) : Pt) :=
  exists_param_sep_aux hE n hn

omit [ConnectedSpace M] in
/-- **S0–S1** (commission 177 §2): fine monotonicity of small translates, and every point of `M`
over a thin enough strip is `h(e)` for a `θ/4`-homeomorphism `h` with `k(e)` within `1/n` of its
abscissa.

*Shape (left to me):* the conclusion is the structure `StrandConst E k π F n θ c`: `θ > 0`,
`c ∈ (0, 1]`, and for the thin strip `F[[0, 1] × [−c, c]]`
* (S0) every `θ/4`-homeomorphism `h` and `z ∈ E` with `h(z)` over the strip at abscissa `s` have
  `|k(z) − s| < 2/n`;
* (S1) every `y ∈ M` over the strip at abscissa `s` is `h(e)` with `h` a `θ/4`-homeomorphism and
  `|k(e) − s| < 1/n`.
No constant depends on `D`. -/
theorem strand_fine_translate (hX : IsHomogeneous M) {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    (n : ℕ) (hn : 0 < n) : ∃ θ c, StrandConst E k π F n θ c :=
  strand_fine_translate_aux hX hE hπc hπS hγπ hF n hn

/-- **S2–S3, the strand lemma**: for `D` of height `≤ c(n)`, the component of `M ∩ π⁻¹[D]` through
a point over the inner middle `[3/22 + 3/n, 19/22 − 3/n]` is crossing, and its closure lies in a
`θ/4`-translate `h[E]` and contains `h[k⁻¹((3/22 + 2/n, 19/22 − 2/n))]`.

*Shape (left to me):* `n ≥ 15` (the commission's `n ≥ 100` is not needed: S0 needs `2/n < 3/22`);
`D = F[D′]` is any `IsCrossRegion` of height `c₁ ≤ c`; the point is `y ∈ M` with `π(y) = F(z)`,
`z ∈ D′`. The general form, for any `θ/4`-translate `h(e)` with `3/22 + 2/n ≤ k(e) ≤ 19/22 − 2/n`,
is `strand_crossing` (with `strand_closure_subset` for S2 alone). -/
theorem strand_lemma (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (y : M) (z : ℝ × ℝ) (hzD : z ∈ D')
    (hyz : π (y : Pt) = F z) (hz1 : 3 / 22 + 3 / (n : ℝ) ≤ z.1)
    (hz2 : z.1 ≤ 19 / 22 - 3 / (n : ℝ)) :
    ∃ h : M ≃ₜ M, (∀ v, dist (h v) v < θ / 4) ∧ ∃ e : E, h e = y ∧
      closure (connectedComponentIn (crossSet univ π F D') y) ⊆ h '' E ∧
      IsCrossingComponent univ π F c₁ D' (connectedComponentIn (crossSet univ π F D') y) ∧
      h '' layerSet k {t | 3 / 22 + 2 / (n : ℝ) < (t : ℝ) ∧ (t : ℝ) < 19 / 22 - 2 / (n : ℝ)} ⊆
        closure (connectedComponentIn (crossSet univ π F D') y) :=
  strand_inner_middle hX hi hE hπc hπS hγπ hF hS hn hc₁ hR y z hzD hyz hz1 hz2

/-- **S6, fine positions**: every point of the closure of the component through `h(e)`, over the
thin strip at abscissa `s`, is `h(t)` with `|k(t) − s| < 2/n`. *Shape (left to me):* as stated. -/
theorem strand_fine_positions (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    (hπc : Continuous π) {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {n : ℕ}
    {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (e : E) (q : M)
    (hq : q ∈ closure (connectedComponentIn (crossSet univ π F D') (h e))) (w : ℝ × ℝ)
    (hw : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-c) c) (hqw : π (q : Pt) = F w) :
    ∃ t : E, h t = q ∧ |(k t : ℝ) - w.1| < 2 / (n : ℝ) :=
  strand_fine_positions_aux hX hi hE hπc hF hS hn hc₁ hR h hh e q hq w hw hqw

/-- **S5**: a type A′ continuum meets the inner middle in whole strands, except at its end sets.

*Shape (left to me):* for `G` with `d⁻¹(0) = k⁻¹(0)` (Hagopian's `F`, so only `d⁻¹(1)` can give an
end strand): if `y ∈ G` is over the inner middle and the closure of its strand misses `d⁻¹(1)`, the
component of `G ∩ π⁻¹[D]` through `y` is the strand, and it is a crossing component of `G`. The
general form (any end sets) is `typeA'_strand_aux`. The \"hair\" description of end strands is open. -/
theorem typeA'_inner_strands (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπc : Continuous π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0) (y : M) (hyG : y ∈ G)
    (z : ℝ × ℝ) (hzD : z ∈ D') (hyz : π (y : Pt) = F z) (hz1 : 3 / 22 + 3 / (n : ℝ) ≤ z.1)
    (hz2 : z.1 ≤ 19 / 22 - 3 / (n : ℝ))
    (h1 : Disjoint (closure (connectedComponentIn (crossSet univ π F D') y)) (layer d 1)) :
    connectedComponentIn (crossSet G π F D') y = connectedComponentIn (crossSet univ π F D') y ∧
      IsCrossingComponent G π F c₁ D' (connectedComponentIn (crossSet G π F D') y) :=
  typeA'_inner_crossing hX hi hE hπc hπS hγπ hF hS hn hc₁ hR hG hX0 y hyG z hzD hyz hz1 hz2 h1

/-- **A.** `T12Data` exists.

*Shape (left to me):* set-up of `hagopian76_T12_uncond` with `[a, b] = [3/22, 19/22]`, the domain
of height `c₁ ≤ c(n)` an `IsCrossRegion`, the strand constants with `n ≥ 15`, and `t₀` in
`[3/22 + 2/n, 19/22 − 2/n]`. For every `ε₃ > 0` and `K₀ ⊆ M` there is a package `D` with
`D.p = D.h(x)`, `k(x) = t₀`, and `D.K = K₀ ∪ {D.p}` (`T12Data.K` is an arbitrary set containing `p`;
Hagopian's arc component is not constructed). T12 (2) holds for the `h` of T12 (3): \"by Lemma 5\"
is `strand_essential`. -/
theorem exists_T12Data (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D')
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc (3 / 22) (19 / 22) ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hIs : (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)})
    (hIR : I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁)) (hDo : IsOpen D')
    (hDf : frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∪
        Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
        ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ w₂ : ℝ} (ht₀1 : 3 / 22 + 2 / (n : ℝ) ≤ t₀) (ht₀2 : t₀ ≤ 19 / 22 - 2 / (n : ℝ))
    (hw₂ : w₂ ∈ Ioc 0 c₁) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (K₀ : Set M) {ε₃ : ℝ} (hε₃ : 0 < ε₃) :
    ∃ D : T12Data E k π F D' ε₃, D.K = insert D.p K₀ ∧ ∃ x : E, (k x : ℝ) = t₀ ∧ D.p = D.h x :=
  exists_T12Data_aux hX hi hE hπ hπS hγπ hF hS hn hc₁ hR hbelow hI hIs hIR hDo hDf hFDf ht₀1 ht₀2
    hw₂ hFw hseg K₀ hε₃

omit [CompactSpace M] [ConnectedSpace M] in
/-- **B.** `π⁻¹[Fr D]` is compact and connected.

*Shape (left to me):* for Hagopian's domain (frontier `I₂ ∪` bottom edge `∪` two side segments,
`I₂` an arc), `Y = π⁻¹[Fr D]` is compact and connected, misses `π⁻¹[D]`, and contains
`Fr π⁻¹[D]`: exactly the hypotheses on `Y` in `hagopian76_property4_top`. The general fact is
`pi_preimage_continuum` (`π` is proper with connected fibres). -/
theorem pi_preimage_frontier_D {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂)) :
    IsCompact (π ⁻¹' frontier (F '' D')) ∧ IsConnected (π ⁻¹' frontier (F '' D')) ∧
      Disjoint (π ⁻¹' frontier (F '' D')) (π ⁻¹' (F '' D')) ∧
      frontier (π ⁻¹' (F '' D')) ⊆ π ⁻¹' frontier (F '' D') :=
  pi_preimage_frontier_D_aux hE hπ hπS hF ha hab hb hc1 hI hIR hFDo hFDf

end Thm1

/-! ## Open items

The obstructions are in `OPEN.md` (batch 177) and in `doc/batches/REPORT-batch177.md`.

-- `strand_order` (S4): proved in batch 178 without Schoenflies, as S4a–S4e (`Hagopian76W.lean`).

**OPEN (C, `exists_blocks`).** Merge the finitely many members of `I` with `[0, e]` and sort: finite
combinatorics on closed intervals (`hagopian76_I_finite`, `hagopian76_J_xs` give the input); not
formalized this batch.

theorem exists_blocks … := by
  sorry

**OPEN (D, `sep_by_crossing`).** Rests on S4 (the order of strands) and on the description of end
strands as hairs (S5, last bullet).

theorem sep_by_crossing … : SepByCrossing G π F c₁ D' (π ⁻¹' (F '' D')) p (f p) := by
  sorry

**OPEN (E, `hagopian76_property4_step`).** Rests on S4 and on the cap `Λ` (§3.E.3), both unformalized.

theorem hagopian76_property4_step … : Property4Step D x n := by
  sorry

**OPEN (F, `hagopian76_theorem1_final`).** The strongest conditional form is
`hagopian76_T15_T17_cond2`: the package and `Y` are discharged; `SepByCrossing`, the blocks and
`Property4Step` remain.

-- `hagopian76_theorem1_final`: proved in batch 190 as `hagopian76_theorem1`, `Jones75B.lean`.
-/

end HPC.Hagopian
