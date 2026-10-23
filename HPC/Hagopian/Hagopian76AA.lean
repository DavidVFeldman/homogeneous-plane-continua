import HPC.Hagopian.H76Tight

/-!
# Batch 182: Hagopian 1976, Theorem 1 — the last step; honest claims; saturation; E2.1 and E2.4

Commission 182 (`doc/batches/COMMISSION-batch182.md`; skeleton
`doc/batches/skeletons/Hagopian76AA.lean`). The skeleton is split under `HPC/Hagopian/`:

| Item | Status | Lean name (file) |
| --- | --- | --- |
| §1.1 certificate | proved | `blockLayersMeetSides_false`, `Thm1Setup.IsBlocks.layer_x2_eq`, `Thm1Setup.IsBlocks.G_ne_E` (`H76Last.lean`) |
| §1.2 last step | proved (ending); claims named | `LastStepWitness`, `last_step_ending`, `LastStepClaims`, `not_property4_x3x4` (`H76Orient.lean`) |
| §1.3 case split, `i ≥ 3` | stated, open | `BlockLayersMeetSides3` (`H76Orient.lean`); weaker split at `i = 2`: `Thm1Setup.IsBlocks.layer_x2_meets_right` (`H76Sat182.lean`) |
| §2.1 mirror cap | proved | `cross_strand_near_above`, `Thm1Setup.segment_misses_closure_above` (`H76Last.lean`) |
| §2.2 orientation | proved | `Thm1Setup.up`, `Thm1Setup.dn`, `cross_strand_near_o`, `property4_step_unless_o`, `case1_ending_oriented`, `case2_ending_oriented` (`H76Orient.lean`) |
| §2.3 honest claims | stated | `StepCase`, `Case1WitnessO`, `Case2WitnessO`, `Case1Claims'`, `Case2Claims'` (`H76Orient.lean`) |
| §2.4 reduction | proved, conditional | `StepStrands`, `hagopian76_property4_step_cond2` (`H76Orient.lean`); `StepFrame`, `stepStrands_of_frame`, `hagopian76_theorem1_of_cases2` (here) |
| §3.1 steps 1–2 | proved | `Thm1Setup.kminus_isContinuum`, `Thm1Setup.kplus_isContinuum`, `Thm1Setup.half_bump`, `Thm1Setup.half_bump_side` (`H76Sat182.lean`) |
| §3.1 `noncrossing_half_in_O` | open | comment block below |
| §3.2 | proved | `closure_G_diff_E` (`H76Last.lean`) |
| §3.3, §3.4, 2e | open | comment block below |
| §4.1 step 4 | proved | `Thm1Setup.extension_misses_G`, `Thm1Setup.admissible_misses_G_of_h_Rset`, `minimalAdmissible_ne_univ`, `Thm1Setup.continuum_misses_G_of_h_Rset`, `Thm1Setup.comp_disjoint_G`, `Thm1Setup.comp_disjoint_G_of_ess`, `Thm1Setup.comp_f_disjoint_G` (`H76Sat182.lean`) |
| §4.1 steps 1–3, 5 | open | comment block below |
| §4.1 step 6 | available | `Thm1Setup.K_meets_crossing` (batch 180) |
| §4.2 E2.4 | open | comment block below |
| §5 Case 2 (e) | open | field `claim_e` of `Case2WitnessO` |
| tight blocks | proved | `Thm1Setup.IsTightBlocks`, `hagopian76_T15_T17_cond5`, `exists_thm1Setup_tight`, `hagopian76_theorem1_of_step_tight` (`H76Tight.lean`) |
| Theorem 1 | conditional | `hagopian76_theorem1_of_cases2` (here) |

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 348–349. Route: commission 182.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section B182Frame

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Named `Prop`: what E0 and E1 still need** (the open part of `StepStrands`, commission 182
§2.4): for `3 ≤ i ≤ m`, if `I` has Property 4, it has it at a point `yᵢ` (`yᵢ ∈ K`, `Cl Cᵢ`
essential to `h[R(E)]`, `d⁻¹[I]` separating `yᵢ` from `f(yᵢ)`) such that
* the component `Cᵢ` of `yᵢ` and the component of `f(yᵢ)` in `M ∩ π⁻¹[D]` are pieces of the low
  frame (that they miss `F` is proved: `Thm1Setup.comp_disjoint_G_of_ess`,
  `Thm1Setup.comp_f_disjoint_G`);
* for every `I`-strand `S_I` with `yᵢ`, `f(yᵢ)` on opposite sides there is a `J`-strand on the
  side of `yᵢ` (p. 348: "For convenience we suppose `d⁻¹[J]` is below `d⁻¹[I]` and `f(yᵢ)` is above
  `d⁻¹[I]`", with the orientation chosen by the side of `yᵢ`). -/
def StepFrame (S : Thm1Setup M) (x : ℕ → unitInterval) (m : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ m → Property4 S.D (x (2 * i - 1)) (x (2 * i)) →
    ∃ yi ∈ S.D.K, IsEssential S.k (S.D.h ⁻¹' (Subtype.val ⁻¹' closure (S.comp yi))) ∧
      SepIn (S.π ⁻¹' (S.F '' S.D')) (toPt (layerSet S.D.d (Icc (x (2 * i - 1)) (x (2 * i)))))
        (yi : Pt) ((S.D.f yi : M) : Pt) ∧
      S.V.IsPiece (S.comp yi) ∧ S.V.IsPiece (S.comp (S.D.f yi)) ∧
      ∀ SI, S.IsBlockStrand (x (2 * i - 1)) (x (2 * i)) SI →
        (((yi : Pt) ∈ S.V.below SI ∧ ((S.D.f yi : M) : Pt) ∈ S.V.above SI) ∨
          ((yi : Pt) ∈ S.V.above SI ∧ ((S.D.f yi : M) : Pt) ∈ S.V.below SI)) →
        ∃ SJ, S.IsBlockStrand (x (2 * i - 3)) (x (2 * i - 2)) SJ ∧
          ((SJ ⊆ S.V.below SI ∧ (yi : Pt) ∈ S.V.below SI) ∨
            (SJ ⊆ S.V.above SI ∧ (yi : Pt) ∈ S.V.above SI))

/-- The saturation interval `(3/22 + 8/n, 19/22 − 8/n)` contains `1/2` (`n ≥ 40`). -/
theorem Thm1Setup.half_mem_sat (S : Thm1Setup M) :
    3 / 22 + 8 / (S.n : ℝ) < 1 / 2 ∧ 1 / 2 < 19 / 22 - 8 / (S.n : ℝ) := by
  have hn : (40 : ℝ) ≤ S.n := by exact_mod_cast S.hn
  have h8 : 8 / (S.n : ℝ) ≤ 8 / 40 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
  constructor <;> linarith

/-- **`StepStrands` from `StepFrame`** (commission 182 §2.4): with saturation, E0
(`property4_strand`) gives an `I`-strand with `yᵢ`, `f(yᵢ)` on opposite sides; `StepFrame` gives a
`J`-strand on the side of `yᵢ`; E1 (`property4_step_unless_o`, orientation = the side of `yᵢ`)
gives Property 4 for `J` or the printed case hypothesis `StepCase`. The good point is assembled
from `StepFrame` and `Thm1Setup.comp_disjoint_G_of_ess`. -/
theorem stepStrands_of_frame (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hICC : InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
      (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)))
    (hx : S.IsBlocks x m) (hF : StepFrame S x m) : StepStrands S x m := by
  intro i hi3 him hI
  obtain ⟨y, hyK, hess, hsep, hyP, hfP, hJ⟩ := hF i hi3 him hI
  have hy : S.GoodPoint y := ⟨hyK, hess, hyP, S.comp_disjoint_G_of_ess hess⟩
  have hfG := S.comp_f_disjoint_G hy.rset
  obtain ⟨SI, hSI, hpos⟩ := property4_strand S hICC S.half_mem_sat.1 S.half_mem_sat.2 hx
    (by omega) him hy hfP hfG hsep
  obtain ⟨SJ, hSJ, hside⟩ := hJ SI hSI hpos
  have hds := hSI.piece.sides_disjoint
  rcases hpos with ⟨hyb, hfa⟩ | ⟨hya, hfb⟩
  · rcases hside with ⟨hJI, -⟩ | ⟨-, hya⟩
    · rcases property4_step_unless_o S false hSI hSJ hJI hy hfa with h | h
      · exact Or.inl h
      · exact Or.inr ⟨false, y, SI, SJ, ⟨hy, hSI, hSJ, hJI, hyb, hfa, h⟩⟩
    · exact (disjoint_left.1 hds hyb hya).elim
  · rcases hside with ⟨-, hyb⟩ | ⟨hJI, -⟩
    · exact (disjoint_left.1 hds hyb hya).elim
    · rcases property4_step_unless_o S true hSI hSJ hJI hy hfb with h | h
      · exact Or.inl h
      · exact Or.inr ⟨true, y, SI, SJ, ⟨hy, hSI, hSJ, hJI, hya, hfb, h⟩⟩

end B182Frame

/-- **§2.4, Theorem 1 from saturation and the restated claims** (commission 182 §2.4): if, for every
set-up, `InnerComponentsCross` holds (2e) and, for every *tight* block sequence
(`Thm1Setup.IsTightBlocks`, `H76Tight.lean`: padded block sequences are excluded), the named `Prop`s
`StepFrame` (what E0 and E1 still need), `LastStepClaims` (`i = 2`), `BlockLayersMeetSides3` (the
case split for `i ≥ 3`), `Case1Claims'` and `Case2Claims'` hold, then every homogeneous
indecomposable plane continuum is hereditarily indecomposable. Non-vacuity notes: report §2.4. -/
theorem hagopian76_theorem1_of_cases2
    (hICC : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M),
      InnerComponentsCross S.D.G S.π S.F S.D' (3 / 22) (19 / 22) S.r₂ S.s₂ S.I₂
        (3 / 22 + 8 / (S.n : ℝ)) (19 / 22 - 8 / (S.n : ℝ)))
    (hcases : ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M] (S : Thm1Setup M) x m,
      S.IsTightBlocks x m → StepFrame S x m ∧ LastStepClaims S x ∧ BlockLayersMeetSides3 S x m ∧
        Case1Claims' S x m ∧ Case2Claims' S x m) :
    Hagopian76Thm1 :=
  hagopian76_theorem1_of_step_tight hICC fun M _ _ S x m hx => by
    obtain ⟨hf, hl, hs, h1, h2⟩ := hcases M S x m hx
    exact hagopian76_property4_step_cond2 S x m (stepStrands_of_frame S (hICC M S) hx.1 hf) hl hs
      h1 h2

/-! ## Open items (commission 182; obstructions in `OPEN.md`, batch 182, and the report)

**OPEN (§1.3, `blockLayersMeetSides_ge_three`).** The case split for `3 ≤ i ≤ m`
(`BlockLayersMeetSides3`). The route of §1.3 ("on `Cl C`, `d` attains its least value only over the
side segments") is not established: `lemma3_half` orders the layers of a crossing component *inside
one translate* `h[E]`, but `Cl C` may cross several translates, and the least value of `d` on `Cl C`
can be attained at an interior point of `D` where `Cl C` turns back (report §1.3). The weaker split
(left or right region) holds for `d⁻¹(x₂)` (`Thm1Setup.IsBlocks.layer_x2_meets_right`) and is open for
`i ≥ 3`.

theorem blockLayersMeetSides_ge_three (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsBlocks x m) : BlockLayersMeetSides3 S x m := by
  sorry

**OPEN (§3.1, `noncrossing_half_in_O`).** Steps 1–3 are now proved (`kminus_isContinuum`,
`kplus_isContinuum`, `half_bump`, `half_bump_side`: the component of `K∓ ∩ π⁻¹[D]` through `y` has a
point over a closed side segment in its closure; `closure_G_diff_E`). Open: steps 4–5 of commission
178 §3b (if neither half lies in `π⁻¹[D]`, the two components reach the side segments; that they
reach *different* side segments, so that `W` crosses, needs S0 and the margin `8/n`).

theorem noncrossing_half_in_O (S : Thm1Setup M) (y : M) (e : S.E) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < S.θ / 4) (hye : h e = y) (hy : (y : Pt) ∈ toPt S.D.G)
    (hym : ∃ q ∈ S.D', S.π y = S.F q ∧ q.1 ∈ Ioo (3/22 + 8/S.n) (19/22 - 8/S.n))
    (hW : ¬ IsCrossingPiece S.π S.F S.D' (3/22) (19/22) S.r₂ S.s₂ S.I₂
      (connectedComponentIn (toPt S.D.G ∩ S.π ⁻¹' (S.F '' S.D')) y)) :
    (∀ e', S.k e' ≤ S.k e → h e' ∈ S.D.G → S.π (h e') ∈ S.F '' S.D') ∨
    (∀ e', S.k e ≤ S.k e' → h e' ∈ S.D.G → S.π (h e') ∈ S.F '' S.D') := by
  sorry

**OPEN (§3.3 `chunk_points`, §3.4 `chunk_edge_case_full`, 2e `innerComponentsCross_hagopian`).**
As in batch 181 (`Hagopian76Z.lean`): the points `zⱼ`, (iii) at `zⱼ`; §1.4 step 2 and step 4
(`τ₁ = 1`, configuration in the report §3.4).

**OPEN (§4.1, `first_strand`).** Steps 1–3 (the first crossing component `Cᵢ₋₁` met by an extension
of `Cl Cᵢ` away from `X`, and the shortest such extension `L`) and step 5 (`Cl Cᵢ₋₁` essential to
`h[R(E)]`). Step 4 (`L ∩ F = ∅`) is proved for any extension through a good point
(`Thm1Setup.extension_misses_G`); step 6 is `Thm1Setup.K_meets_crossing`.

**OPEN (§4.2, `property2_far_from_I`).** E2.4: the field `far` of `Case1WitnessO` /
`LastStepWitness`. The hypothesis "`H` has a minimal admissible decomposition" of `Property2At`
cannot be checked without identifying `H ⊆ L` as a continuum of type A′ (report §4.2).

**OPEN (§5, `case2_claim_e`).** The field `claim_e` of `Case2WitnessO`; neither suggested idea
decides it (report §5).
-/

end HPC.Hagopian
