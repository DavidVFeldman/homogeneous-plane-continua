import HPC.Hagopian.Hagopian84A
import HPC.Hagopian.H76Split185
import HPC.Hagopian.H84Rigid
import HPC.Hagopian.H76Sat185

/-!
# Batch 185: Hagopian 1976, Theorem 1 — Lemma 7 of 1984; saturation; the case split

Sources: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–348; Hagopian 1984
(`doc/sources/hagopian1984.pdf`), pp. 336–337. Route: commission 185. The skeleton is
`doc/batches/skeletons/Hagopian76AC.lean`; the proofs are split under `HPC/Hagopian/`:

* `H84TwoSided.lean` (§1): gluing of two type λ continua along a common end layer; the two-sided
  extension.
* `H84Lemma7.lean` (§2): the triod at an interior layer; Lemma 7.
* `H84Rigid.lean` (§3.1–§3.2): rigidity; runs.
* `H76Sat185.lean` (§4): the tip by Lemma 7; saturation.
* `H76Split185.lean` (§5): the case split for `i ≥ 3`.

| item | status | declaration |
|---|---|---|
| §0 `Wset84 = Wset` | proved | `wset84_eq_wset` |
| §1 two-sided extension | proved | `hagopian84_two_sided` |
| §2 Lemma 7 of 1984 | proved | `hagopian84_lemma7`, `hagopian84Lemma7_holds` |
| §3.1 rigidity | proved (shape below) | `layers_agree` |
| §3.2 runs | proved (shape below) | `translate_run`, `translate_run_right` |
| §3.3 runs of `F` along a translate | open | comment block below |
| §4.1 steps 4–5 | proved | `noncrossing_half_in_O_steps45` |
| §4.2 the tip by Lemma 7 | proved | `half_in_O_false` |
| §4.3 saturation | proved | `innerComponentsCross_hagopian` |
| §5 case split for `i ≥ 3` | proved | `blockLayersMeetSides3`, `layer_x3_meets_side` |
| §6 "between" with runs | open | comment block below |
| §7 Theorem 1, conditional | proved | `hagopian76_theorem1_of_cases4` |

Shape changes against the skeleton (report §1–§7): the items stated as `True` are given shapes; the
conditional form `innerComponentsCross_hagopian_of_lemma7` is not stated, since §2 is proved and
`innerComponentsCross_hagopian` is unconditional (report §0).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §0. `W(x, ε)` -/

/-- **§0**: the 1984 `W(x, ε)` (`Wset84`) is the 1976 `Wₓ` (`Wset`). -/
theorem wset84_eq_wset {M : Set Pt} (x : M) (ε : ℝ) : Wset84 x ε = Wset M ε x := by
  ext y
  exact ⟨fun ⟨h, h1, h2⟩ => ⟨h, h2, h1⟩, fun ⟨h, h2, h1⟩ => ⟨h, h1, h2⟩⟩

section Rigidity

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. The two-sided extension -/

/-- **§1** (Hagopian 1984, p. 336, in the proof of Lemma 7: "By Lemma 4, there is a continuum `H` of
type λ in `M` such that (1) `E` is an essential subcontinuum of `H` that misses both end sets of
`H`"). Shape: report 184 §11, unchanged.

*Proof* (`hagopian84_two_sided_aux`, `H84TwoSided.lean`; commission 185 §1, steps 1–5): extensions
`F₁` away from `k⁻¹(0)` and `F₂` away from `k⁻¹(1)` (Lemma 4); `F₁ ∩ F₂ = E`; `H = F₁ ∪ T₂` with
`T₂` the tail of `F₂` beyond `k⁻¹(0)`, glued along `k⁻¹(0)`; irreducibility by hereditary
unicoherence. -/
theorem hagopian84_two_sided (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (H : Set M) (d : H → unitInterval), IsMinimalAdmissible H d ∧ IsEssential84 d E ∧
      Disjoint E (layer d 0) ∧ Disjoint E (layer d 1) :=
  hagopian84_two_sided_aux hX hi hE

/-! ## §2. Lemma 7 of 1984 -/

/-- **§2, Lemma 7** (p. 336): "Suppose `F` is a continuum of type λ in `M` such that
`E∖F ≠ ∅ ≠ F∖E`. Suppose `F ∩ k⁻¹(r) ≠ ∅` for some number `r` (`0 ≤ r ≤ 1`). Then `k⁻¹(r)` is an
element of the decomposition of `F`." Shape: the commented-out block of `Hagopian84A.lean`.

*Proof* (`hagopian84_lemma7_aux`, `H84Lemma7.lean`): not the printed one. With `H ⊇ E`, `I ⊇ F` the
two-sided extensions, a case split on `H ∩ F`: inside one layer of `H` (then `F` is an arm of a
triod at `k⁻¹(r)`), meeting two layers of `H` and of `F` (Lemma 6 twice), or meeting two layers of
`H` inside one layer `Y` of `F` (then `H ∩ I ⊆ Y` and `H` is an arm of a triod at `Y`). -/
theorem hagopian84_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E F : Set M}
    {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : (E \ F).Nonempty) (hFE : (F \ E).Nonempty)
    {r : unitInterval} (hr : (F ∩ layer k r).Nonempty) : ∃ u, layer k r = layer d u :=
  hagopian84_lemma7_aux hX hi hE hF hEF hFE hr

end Rigidity

/-- **§2, Lemma 7 as a named `Prop`** (kept from the skeleton; proved by `hagopian84Lemma7_holds`). -/
def Hagopian84Lemma7 : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M → ¬ IsDecomposableSpace M →
    ∀ (E F : Set M) (k : E → unitInterval) (d : F → unitInterval), IsMinimalAdmissible E k →
      IsMinimalAdmissible F d → (E \ F).Nonempty → (F \ E).Nonempty →
        ∀ r : unitInterval, (F ∩ layer k r).Nonempty → ∃ u, layer k r = layer d u

/-- **§2**: the named `Prop` holds. -/
theorem hagopian84Lemma7_holds : Hagopian84Lemma7 :=
  fun _ _ _ hX hi _ _ _ _ hE hF hEF hFE _ hr => hagopian84_lemma7 hX hi hE hF hEF hFE hr

section Runs

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §3. Rigidity and translate runs -/

/-- **§3.1, rigidity**. *Shape:* `(E, k)`, `(G, d)` minimal admissible, `E ∩ G` meeting two layers
of `E`. Then either `E` lies in a single layer of `G` (the only degenerate case; it forces `E ⊆ G`),
or `E ∩ G = k⁻¹[[a, b]] = d⁻¹[[a', b']]` (`a < b`, `a' < b'`), every layer of `k` meeting `G` is a
layer of `d`, and every layer of `d` meeting `E` is a layer of `k`.

The degenerate case "`G` inside a single layer of `E`" is excluded by the hypothesis; "`E` inside a
single layer of `G`" with `E ⊄ G` or `G ⊄ E` is excluded inside the proof (Lemma 7, and the
surjectivity of `d` when `G ⊆ E`). -/
theorem layers_agree (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E G : Set M}
    {k : E → unitInterval} {d : G → unitInterval} (hE : IsMinimalAdmissible E k)
    (hG : IsMinimalAdmissible G d)
    (h2 : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((E ∩ G) ∩ layer k t₁).Nonempty ∧ ((E ∩ G) ∩ layer k t₂).Nonempty) :
    (∃ v, E ⊆ layer d v) ∨
      ((∃ a b a' b' : unitInterval, a < b ∧ a' < b' ∧ E ∩ G = layerSet k (Icc a b) ∧
          E ∩ G = layerSet d (Icc a' b')) ∧
        (∀ r, (G ∩ layer k r).Nonempty → ∃ u, layer k r = layer d u) ∧
        ∀ u, (E ∩ layer d u).Nonempty → ∃ r, layer d u = layer k r) :=
  layers_agree_aux hX hi hE hG h2

/-- **§3.2, runs** (left end). *Shape:* `(E, k)` a type λ continuum (for the commission's translate,
`h[E]` with the map of `exists_image_map`), `(G, d)` another, `G ∩ E ⊆ k⁻¹[[a, 1]]` with `0 < a`
(the common segment starts at `a`), and `k⁻¹(a) = d⁻¹(a')`. Then `d⁻¹(a')` is an end layer of `G`
(`a' = 0` or `a' = 1`). Proof by atriodicity: otherwise `k⁻¹[[0, a]]` is a third arm at the interior
layer `d⁻¹(a')`. -/
theorem translate_run (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E G : Set M}
    {k : E → unitInterval} {d : G → unitInterval} (hE : IsMinimalAdmissible E k)
    (hG : IsMinimalAdmissible G d) {a a' : unitInterval} (ha : 0 < a)
    (hGE : G ∩ E ⊆ layerSet k (Icc a 1)) (hL : layer k a = layer d a') : a' = 0 ∨ a' = 1 :=
  translate_run_left_aux hX hi hE hG ha hGE hL

/-- **§3.2, runs** (right end): the mirror of `translate_run`. -/
theorem translate_run_right (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E G : Set M}
    {k : E → unitInterval} {d : G → unitInterval} (hE : IsMinimalAdmissible E k)
    (hG : IsMinimalAdmissible G d) {b b' : unitInterval} (hb : b < 1)
    (hGE : G ∩ E ⊆ layerSet k (Icc 0 b)) (hL : layer k b = layer d b') : b' = 0 ∨ b' = 1 :=
  translate_run_right_aux hX hi hE hG hb hGE hL

end Runs

section Sat

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §4. Saturation (2e) -/

/-- **§4.1, steps 4–5 of `noncrossing_half_in_O`**. *Shape:* `y = h(e) ∈ F ∩ π⁻¹[D]`, `h` a
`θ/4`-homeomorphism, `3/22 + 2/n < k(e) < 19/22 − 2/n`; if neither `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` nor
`K⁺ = F ∩ h[k⁻¹[[k(e), 1]]]` lies in `π⁻¹[D]`, the component of `y` in `F ∩ π⁻¹[D]` is a crossing
piece. -/
theorem noncrossing_half_in_O_steps45 (S : Thm1Setup M) {y : M} (hyG : y ∈ S.D.G)
    (hyO : (y : Pt) ∈ S.π ⁻¹' (S.F '' S.D')) (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < S.θ / 4)
    (e : S.E) (hey : h e = y) (hkl : 3 / 22 + 2 / (S.n : ℝ) < S.k e)
    (hkr : (S.k e : ℝ) < 19 / 22 - 2 / S.n)
    (hm : ¬ S.D.G ∩ h '' layerSet S.k (Icc 0 (S.k e)) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'})
    (hp : ¬ S.D.G ∩ h '' layerSet S.k (Icc (S.k e) 1) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'}) :
    IsCrossingPiece S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) (y : Pt)) :=
  S.crossing_of_halves hyG hyO h hh e hey hkl hkr hm hp

/-- **§4.2, the tip by Lemma 7**. *Shape:* for `h(e) ∈ F`, `h` a `θ/4`-homeomorphism and
`2/n < k(e) < 1 − 2/n`, neither `K⁻` nor `K⁺` lies in `π⁻¹[D]`. -/
theorem half_in_O_false (S : Thm1Setup M) (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < S.θ / 4)
    (e : S.E) (he : h e ∈ S.D.G) (hke : 2 / (S.n : ℝ) < S.k e)
    (hke1 : (S.k e : ℝ) < 1 - 2 / S.n) :
    ¬ S.D.G ∩ h '' layerSet S.k (Icc 0 (S.k e)) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'} ∧
      ¬ S.D.G ∩ h '' layerSet S.k (Icc (S.k e) 1) ⊆ {m : M | S.π (m : Pt) ∈ S.F '' S.D'} :=
  ⟨S.kminus_not_subset_O h hh e he hke, S.kplus_not_subset_O h hh e he hke hke1⟩

/-- **§4.3, saturation** (2e for Hagopian's `F` on `(3/22 + 8/n, 19/22 − 8/n)`), unconditional. -/
theorem innerComponentsCross_hagopian (S : Thm1Setup M) :
    InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)) :=
  S.innerComponentsCross_aux

/-! ## §5. The case split for `i ≥ 3` -/

/-- **§5** (p. 348: "The proof now breaks down into two cases"): for tight blocks and `3 ≤ i ≤ m`,
`d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` each meet a closed side segment. Route of commission 185 §5
(`Thm1Setup.blockLayersMeetSides3_aux`, `H76Split185.lean`); Lemma 7 is not used. -/
theorem blockLayersMeetSides3 (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsTightBlocks x m) : BlockLayersMeetSides3 S x m :=
  S.blockLayersMeetSides3_aux hx

/-- **§5, `d⁻¹(x₃)` located** (notes E3: "not located by anything proved"): for tight blocks with
`m ≥ 2`, `d⁻¹(x₃)` meets a closed side segment (steps 2–5 of §5 at the left end of the block
`[x₃, x₄]`). Which side is not determined. -/
theorem layer_x3_meets_side (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsTightBlocks x m) (hm : 2 ≤ m) :
    ∃ a ∈ ({3 / 22, 19 / 22} : Set ℝ), S.LayerMeetsSide (x 3) a :=
  S.layer_x3_meets_side hx hm

end Sat

/-- **§7, Theorem 1, the strongest conditional form of this batch**. *Shape:* from `StepFrame`,
`LastStepClaims`, `Case1ClaimsE24` and `Case2ClaimsE24` for every set-up and tight block sequence;
saturation (`innerComponentsCross_hagopian`) and the case split (`blockLayersMeetSides3`) are
discharged, and `Hagopian84Lemma7` is not needed (it is proved). Non-vacuity notes: report §7. -/
theorem hagopian76_theorem1_of_cases4
    (hcases : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M) x m,
      S.IsTightBlocks x m → StepFrame S x m ∧ LastStepClaims S x ∧ Case1ClaimsE24 S x m ∧
        Case2ClaimsE24 S x m) :
    Hagopian76Thm1 :=
  hagopian76_theorem1_of_cases3 (fun _ _ _ S => innerComponentsCross_hagopian S)
    fun M _ _ S x m hx => by
      obtain ⟨hf, hl, h1, h2⟩ := hcases M S x m hx
      exact ⟨hf, hl, blockLayersMeetSides3 S hx, h1, h2⟩

/-! ## Open items (commission 185; obstructions in `OPEN.md`, batch 185, and the report)

**OPEN (§3.3, `crossing_component_run`).** For a crossing component `C` of `F ∩ π⁻¹[D]` and the
translate `h[E]` of `strand_lemma` through a point of `C` over the middle: `F ∩ h[E]` is a common
segment containing `C` running to within `2/n` of a translate end or to `d⁻¹(1)`. The first part is
available (`C` lies in the strand through that point, so `Cl C ⊆ h[E]`; `F ∩ h[E]` is a continuum;
`layers_agree` applies). Obstruction: (i) the degenerate alternative of `layers_agree`, `h[E]` inside
one layer of `F`, is not excluded; (ii) `translate_run` allows the end layer `d⁻¹(0)` as well as
`d⁻¹(1)`, and `d⁻¹(0)` is not excluded; (iii) no shape was found that is both provable this way and
strong enough for §6 (report §3.3).

theorem crossing_component_run : True := by
  sorry

**OPEN (§6, `case1_between_runs`).** As batch 183 §3, with §3.3 (open) as the missing input
(report §6).

theorem case1_between_runs : True := by
  sorry
-/

end HPC.Hagopian
