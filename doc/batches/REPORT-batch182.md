Commission read: `doc/batches/COMMISSION-batch182.md` ("Commission: batch 182 — Part E, Hagopian 1976 XXVII: Theorem 1 — the last step; honest claims; saturation; E2.1 and E2.4").

# Report, batch 182

## 0. Summary, omissions

All new declarations compile without `sorry` and use only `propext`, `Classical.choice`,
`Quot.sound` (§7). `axioms.txt` has 2160 lines; `sorryAx` occurs in none.

```
STATUS: §1.1 blockLayersMeetSides_false proved
STATUS: §1.2 last_step_ending proved; LastStepClaims named (proof by contradiction); not_property4_x3x4 proved
STATUS: §1.2 gap continuum: starts in the right region (proved); its other end open
STATUS: §1.3 case split for i ≥ 3 stated (BlockLayersMeetSides3), open (d monotone along Cl C not available across translates)
STATUS: §1.3 weaker split at i = 2 proved for d⁻¹(x₂) (layer_x2_meets_right)
STATUS: §2.1 cross_strand_near_above proved (no bottom-edge hypothesis)
STATUS: §2.2 case1_ending_oriented, case2_ending_oriented proved
STATUS: §2.3 Case1Claims', Case2Claims' stated (antecedent StepCase, no ¬ Property4 J)
STATUS: §2.4 hagopian76_property4_step_cond2, hagopian76_theorem1_of_cases2 proved, conditional
STATUS: §2.4 (found) padded block sequences: reduction moved to tight block sequences (exists_thm1Setup_tight) proved
STATUS: §3.1 steps 1–2 proved (kminus_isContinuum, kplus_isContinuum, half_bump, half_bump_side); steps 4–5 open
STATUS: §3.2 closure_G_diff_E proved
STATUS: §3.3 points zⱼ, (iii) at zⱼ open (as batch 181)
STATUS: §3.4 §1.4 step 2 open; τ₁ = 1 open (absorption gives nothing new)
STATUS: 2e innerComponentsCross_hagopian open
STATUS: §4.1 step 4 proved (extension_misses_G; GoodPoint.miss automatic: comp_disjoint_G_of_ess); steps 1–3, 5 open; step 6 available
STATUS: §4.2 E2.4 open (end sets within ε₃ not implied)
STATUS: §5 Case 2 (e) open (neither idea decides it)
```

**Omissions (§0 rule).**
* `noncrossing_half_in_O`, `chunk_points`, `chunk_edge_case_full`, `innerComponentsCross_hagopian`,
  `blockLayersMeetSides_ge_three`, `first_strand`, `property2_far_from_I`, `case2_claim_e`,
  `hagopian76_theorem1_final` of the skeleton: open; commented out at the end of
  `HPC/Hagopian/Hagopian76AA.lean`, obstructions in §1.3, §3, §4, §5 below and in `OPEN.md`.
* `cross_strand_near_mirror` (`H76CapLow.lean`) is not replaced in place: the new
  `cross_strand_near_above` (`H76Last.lean`) has the skeleton's statement; the old theorem is unchanged.
* No commented-out statement of the earlier `Hagopian76*.lean` files is proved here, so none was
  replaced by a pointer (the files are unchanged).

**Shape changes** (recorded at each statement).
* `cross_strand_near_above` has the hypothesis `hW` (crossing piece) of the skeleton; nothing else.
* `last_step_ending`: `LastStepWitness` carries an orientation `o` (more permissive than "below").
* `blockLayersMeetSides_ge_three` is stated through the named `Prop` `BlockLayersMeetSides3`.
* `case1_ending_oriented`, `case2_ending_oriented`: the orientation is a `Bool` exchanging `V.above`
  and `V.below` (`Thm1Setup.up`, `Thm1Setup.dn`).
* `hagopian76_property4_step_cond2` uses the named `Prop` `StepStrands` (the output of E0 + E1);
  `hagopian76_theorem1_of_cases2` uses `StepFrame` (what E0 + E1 still need) and quantifies over
  **tight** block sequences (§2.4).
* `noncrossing_half_in_O` (steps 1–2): `kminus_isContinuum`, `kplus_isContinuum`, `half_bump`,
  `half_bump_side`.
* `first_strand` (step 4): `Thm1Setup.extension_misses_G`.

## 1. The last step and the case split

### 1.1 Certificate (proved)

`blockLayersMeetSides_false (hx : S.IsBlocks x m) : ¬ BlockLayersMeetSides S x m` (`H76Last.lean`).
Steps as in the commission: `Thm1Setup.IsBlocks.G_ne_E` (`F ≠ E`, else `d⁻¹(1) = ∅` since `x₂ < x₄ ≤ 1`),
`Thm1Setup.IsBlocks.layer_x2_eq` (`d⁻¹(x₂) = k⁻¹(1)`, by `ext_layers` and `layerSet_Icc_zero_inj`),
`Thm1Setup.not_layerMeetsSide_of_layer_eq_one` (`k⁻¹(1)` lies over `F(1, 0)`; `F` is injective on the
rectangle). So `hagopian76_theorem1_of_cases` (batch 181) is a vacuous reduction, as the commission says.

### 1.2 The last step (proved, conditional on a proof by contradiction)

`LastStepWitness S x` (orientation `o`, good point `y`, `I`-strand `S_I` of `[x₃, x₄]`, `y ∈ dn o S_I`,
`ρ(y, Cl S_I) ≥ ε₃`, `f(y) ∈ up o S_I`); `last_step_ending : LastStepWitness S x → False` (the oriented
cap against `far`); `LastStepClaims S x := Property4 [x₃, x₄] → Nonempty (LastStepWitness S x)`;
`not_property4_x3x4 : LastStepClaims S x → ¬ Property4 [x₃, x₄]` (`H76Orient.lean`).

**Where the gap continuum closes the band.** `d⁻¹[[x₂, x₃]]` contains `d⁻¹(x₂) = k⁻¹(1)`, which lies in
the right region `π⁻¹F[[19/22, 1] × [0, c₁]]` (`Thm1Setup.IsBlocks.layer_x2_meets_right`), to the right
of `D` and outside `π⁻¹[D]`. Its other end `d⁻¹(x₃)`: `x₃` is the left end of the second block, so
(tight blocks) the left end of a member `[u, v]` of `I`, and `d⁻¹(u)` meets the closure of the crossing
component with irreducible interval `[u, v]`; where on that closure is not determined by anything
proved. If it is over the right side segment, the band `P = d⁻¹[[x₁, x₄]] ∪ Q` is closed on the right
as in Case 1; if over the left one, the configuration is that of Case 2 (the gap continuum meets both
side segments); otherwise not decided. Note also that `E` misses `π⁻¹[D]` (`Thm1Setup.disjoint_O_E`):
inside the frame, "below `E`" is empty and "between `E` and `S_I`" is "below `S_I`".

### 1.3 The case split for `i ≥ 3` (stated, open)

`BlockLayersMeetSides3 S x m` (`H76Orient.lean`): the batch-181 split for `3 ≤ i ≤ m` only.

*Route of the commission.* `x₂ᵢ₋₁` is the left end `u` of a member `[u, v]` of `I`, `C` the crossing
component with irreducible interval `[u, v]`, and `d⁻¹(u)` meets `Cl C`. The claim "on `Cl C`, `d`
attains its least value only over the side segments" is **not established**. What is available:
`lemma3_half` orders by parameter the layers of a translate `h[E]` through the points over the
middle, and S0 says these layers are nearly vertical. To conclude, one needs that the layers of `F`
through the points of `Cl C` over `D` are layers of these translates, with `d` increasing with the
`k`-parameter of the translate. `ext_layers` gives this only for `E ⊆ F` itself; for a translate
`h[E] ⊄ F` the layers of `F` meeting `h[E]` are not related to those of `h[E]`. *Configuration:* `Cl C`
covered by two translates `h₁[E]`, `h₂[E]` whose parameters run in opposite directions, with `d` along
`Cl C` decreasing on the first and increasing on the second; then the minimum of `d` on `Cl C` is over
the interior of `D`. Nothing proved excludes it.

*Weaker split.* "`d⁻¹(u)` meets the left region `π⁻¹F[[0, 3/22] × [0, c₁]]` or the right region
`π⁻¹F[[19/22, 1] × [0, c₁]]`" (`Thm1Setup.LayerMeetsRegion`). It holds for `d⁻¹(x₂)` (right region,
`Thm1Setup.IsBlocks.layer_x2_meets_right`); for `i ≥ 3` it is open for the same reason. The band
arguments use the side segments only through the position of the gap continuum relative to the two
strands `S_J`, `S_I`; with the regions in place of the segments, the gap continuum may reach the
region outside `π⁻¹[D]` without meeting `Cl S_J` or `Cl S_I` on that side, which is what Case 1 needs to
close `P`. So the band arguments survive the weaker split only when the region point lies on the
same side of the strands' end points as the segment would, which is not given.

## 2. Honest claims, and the reduction

### 2.1 The mirror cap (proved)

`Thm1Setup.segment_misses_closure_above`: the exclusions of `cross_strand_near` (over `I₂` by `hε₂I`,
over the sides by `hε₃S`, over the open bottom edge by `above_closure_misses_bottom`) use only
`a ∈ Mid` and `ρ(a, b) < ε₃`. `cross_strand_near_above`: with `a` above `W`, `b` below,
`VFrame.exists_mem_closure_of_preconnected` applied with the endpoints exchanged gives a point of
`Cl W` on `[a, b]`. No bottom-edge hypothesis.

### 2.2 Orientation (proved)

`Thm1Setup.up`, `Thm1Setup.dn` (pattern matching on `o : Bool`); `cross_strand_near_o`,
`property4_of_strand_sep_o`, `Thm1Setup.up_subset_up`, `Thm1Setup.piece_sides_o`,
`property4_step_unless_o`; `Case1WitnessO`, `case1_ending_oriented`; `Case2WitnessO`,
`case2_ending_oriented`.

*Coverage.* The `Bool` covers the configurations with `d⁻¹[J]` on the side of `yᵢ` (the printed one and
its mirror). In the two others, `d⁻¹[J]` is on the side of `f(yᵢ)`; E1 then leaves "`f(yᵢ)` between the
strands", and the band argument would have to be run for `f(yᵢ)`, which is not a point of `K`. Not
treated; `StepFrame` asks for a `J`-strand on the side of `yᵢ`.

### 2.3 Claims without `¬ Property4 J` (stated)

`StepCase S x i o yᵢ S_I S_J` (the printed hypothesis left by E1: good point, the two strands,
`S_J ⊆ dn o S_I`, `yᵢ ∈ dn o S_I`, `f(yᵢ) ∈ up o S_I`, `Cᵢ ⊆ up o S_J`). `Case1Claims'`, `Case2Claims'`:
for `3 ≤ i ≤ m`, the case configuration and `StepCase` give a witness (`Case1WitnessO`,
`Case2WitnessO`) in the same orientation. The witness fields are those of batch 181, oriented.

### 2.4 The reduction (proved, conditional)

* `StepStrands S x m` (named): for `3 ≤ i ≤ m`, `Property4 I → Property4 J ∨ ∃ o yᵢ S_I S_J, StepCase …`
  (the printed sentence "`J` has Property 4 unless `yᵢ` is above `d⁻¹[J]`").
* `hagopian76_property4_step_cond2 : StepStrands → LastStepClaims → BlockLayersMeetSides3 →
  Case1Claims' → Case2Claims' → Property4Step S.D x m`. At `i = 2` the antecedent fails
  (`not_property4_x3x4`); for `i ≥ 3`, E1's alternatives, the split and the claims.
* `StepFrame S x m` (named, `Hagopian76AA.lean`): if `I` has Property 4, it has it at a `yᵢ` whose
  component and the component of `f(yᵢ)` are pieces of the low frame, and every `I`-strand with `yᵢ`,
  `f(yᵢ)` opposite has a `J`-strand on the side of `yᵢ`. (That both components miss `F` is proved:
  `Thm1Setup.comp_disjoint_G_of_ess`, `Thm1Setup.comp_f_disjoint_G`.)
* `stepStrands_of_frame : InnerComponentsCross → IsBlocks → StepFrame → StepStrands` (E0 + E1).
* `hagopian76_theorem1_of_cases2`: `InnerComponentsCross` for every set-up and, for every **tight**
  block sequence, `StepFrame ∧ LastStepClaims ∧ BlockLayersMeetSides3 ∧ Case1Claims' ∧ Case2Claims'`
  give `Hagopian76Thm1`.

**Found while checking non-vacuity: padded block sequences.** `hagopian76_theorem1_of_step` (batch 179)
asks for the step for every `S.IsBlocks x m`. `IsBlocks` does not contain the two clauses of
`exists_blocks_uncond` (every parameter of a block is `≤ x₂` or in a member of `I`; no member straddles
a gap). Without them one may insert a block `[u, v]` inside a gap: `IsBlocks` still holds, and
`d⁻¹[[u, v]]` contains no part of a crossing component (the irreducible interval of the component lies
in an original block). With saturation, `d⁻¹[[u, v]]` then has no block strand, so `StepFrame` fails for
such a sequence as soon as the block above has Property 4, and the printed step cannot reach
Property 4 for `[u, v]`. I did not prove that `Property4Step` fails for padded sequences, but the
reduction should not depend on them. `H76Tight.lean` defines `Thm1Setup.IsTightBlocks` (`IsBlocks`
with the two clauses) and re-proves the assembly with the step asked only for tight sequences:
`hagopian76_T15_T17_cond5`, `exists_thm1Setup_tight`, `hagopian76_theorem1_of_step_tight` (the proofs of
`hagopian76_T15_T17_cond4` and `exists_thm1Setup`, copied, with the clauses passed on; `e = x₂` by
`layerSet_Icc_zero_inj`).

### Named `Prop`s and structures, with non-vacuity notes

| Name | Kind | Check 1 (not refuted by a short argument) | Check 2 (not equivalent to the conclusion) |
| --- | --- | --- | --- |
| `LastStepClaims` | named `Prop` | Refuting it means proving `Property4 [x₃, x₄]`, which is what the whole induction from the top would produce; no short argument. | **Equivalent to `¬ Property4 [x₃, x₄]` by design** (`last_step_ending` refutes every witness). The printed step is a proof by contradiction ("The resulting contradiction will complete our proof"). |
| `StepStrands` | named `Prop` | Holds whenever `J` has Property 4. For padded sequences it can fail (no `J`-strand); `hagopian76_theorem1_of_cases2` therefore uses tight sequences. | Implied by the step's conclusion, but it does not imply it: its second disjunct is the configuration Cases 1–2 treat. |
| `StepFrame` | named `Prop` | For tight sequences each block `J` with `i ≥ 3` contains its left end `x₂ᵢ₋₃ > x₂`, which lies in a member of `I`, so `d⁻¹[J]` contains part of a crossing component; that the strand is on the side of `yᵢ` and that `Cᵢ` is a piece (its closure meets the vertical) are the open content. No short refutation. | Says nothing about Property 4 for `J`. |
| `BlockLayersMeetSides3` | named `Prop` | The §1.1 refutation uses `x₂ = e`; for `i ≥ 3`, `x₂ᵢ₋₂, x₂ᵢ₋₁ > x₂` (strict monotonicity), so the layers are not `k⁻¹(1)`. Undecided (§1.3). | A statement about layers, not about Property 4. |
| `Case1Claims'` | named `Prop` | The antecedent `StepCase` and the configuration are not refuted by a short argument; the witness fields are the printed claims. | No `¬ Property4 J`. From `Property4 J` one gets (E0) a `J`-strand with the point and its image opposite, but not the fields `between` (relative to `S_I`), `far` and `band`; the converse is not a short argument. |
| `Case2Claims'` | named `Prop` | As `Case1Claims'`; `claim_e` is unsupported by the text (§5), which is an obstruction, not a refutation. | As `Case1Claims'`. |
| `InnerComponentsCross` (2e) | named `Prop` (batch 180) | Not refuted (batch 180, margin `8/n`). | About the components of `F`, not about Property 4. |
| `LastStepWitness`, `Case1WitnessO`, `Case2WitnessO`, `StepCase` | structures | `LastStepWitness` is contradictory by design (proof by contradiction). In `Case1WitnessO` the first disjunct of `band` is contradictory with `far` (that is the ending); the second is consistent. | — |

## 3. Saturation: 2e

* **§3.1, step 1 (proved).** `Thm1Setup.kminus_isContinuum`, `Thm1Setup.kplus_isContinuum`:
  `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` and `K⁺` are continua when they contain `h(e)`
  (`isContinuum_inter_of_HU`, `hereditarilyUnicoherent_of_homogeneous_indecomposable`).
  `Thm1Setup.half_bump`: for a continuum `K ∋ y` not inside `π⁻¹[D]`, the component of `K ∩ π⁻¹[D]`
  through `y` has a point of `K` off `π⁻¹[D]` in its closure (`exists_mem_closure_component_notMem`).
* **§3.1, step 2 (proved).** `Thm1Setup.half_bump_side`: for a continuum `K ⊆ F` (e.g. `K⁻`, `K⁺`)
  through `y ∈ π⁻¹[D]` and not inside `π⁻¹[D]`, the closure of the component of `K ∩ π⁻¹[D]` through
  `y` contains a point `q ∈ K` over a closed side segment. `π(q) ∈ Fr D`; not over `I₂` (`hI2M`); not
  over the bottom edge, since then `q ∈ E` (`Thm1Setup.mem_toPt_E_of_pi_eq`) and `q` lies in the closure
  of `F − E`, hence in `k⁻¹(1)` (`closure_G_diff_E`), over `F(1, 0)`.
* **§3.1, steps 4–5 (open).** From "the components of `K⁻ ∩ π⁻¹[D]` and `K⁺ ∩ π⁻¹[D]` through `y`
  reach side segments" (when neither half lies in `π⁻¹[D]`) to "they reach different side segments,
  so `W` is a crossing piece": needs S0 (the halves of the translate run in opposite horizontal
  directions from `y`, by at least `8/n − 2/n`) and is not formalized.
* **§3.2 (proved).** `closure_G_diff_E`.
* **§3.3 (open).** The points `zⱼ` and (iii) at `zⱼ`: as batch 181.
* **§3.4.** Step 2 (`F ∩ hⱼ[E]` in the tip layer): open, needs §3.3. Step 4 (`τ₁ = 1`): open. The
  absorption form of Lemma 6 applied to `d⁻¹(1)` gives `d⁻¹(1) ⊆ R(X, E)`, already known from
  `d⁻¹(1) ⊆ F`; Lemma 4 would need the end piece `F ∩ hⱼ[k⁻¹((τ, 1])]` to be open in `F`, which is not
  known. Configuration as in batch 181: `d⁻¹(1) ⊇ F ∩ hⱼ[k⁻¹((τ, 1])]` with `F ∩ hⱼ[k⁻¹(1)] ≠ ∅`.
* **2e (open).**

## 4. E2.1 and E2.4

### 4.1 E2.1

1. *An extension of `Cl Cᵢ` away from `X` meets another crossing component* — open. The pointer
   (Lemma 6 (proof): `Cl R(X, Cl Cᵢ)` is indecomposable; the "follows" argument of Property 3) gives that
   the extensions are not all contained in a small neighbourhood of `Cl Cᵢ`, but the Property 3
   argument concerns crossing components of `F` (finitely many, `crossing_components_finite`), while
   `Cᵢ₋₁` is a component of `M ∩ π⁻¹[D]`; that an extension returns over `D` and crosses is not shown.
2. *A first one* (`ExtChainInter`, batch 170) — open; needs 1.
3. *`L`, the shortest extension containing `Cᵢ₋₁`* — open; needs 2.
4. *`L ∩ F = ∅`* — **proved**: `Thm1Setup.extension_misses_G` (an extension containing a good point;
   `L ≠ M` since `M` is indecomposable, `minimalAdmissible_ne_univ`; then the composant choice). The
   commission's check: `L` passes through `yᵢ ∈ h[R(E)]` (`GoodPoint.rset`).
5. *`Cᵢ₋₁` a crossing piece, `Cl Cᵢ₋₁` essential to `h[R(E)]`* — open.
6. *`yᵢ₋₁ ∈ K ∩ Cᵢ₋₁`* — available (`Thm1Setup.K_meets_crossing`); `GoodPoint yᵢ₋₁` then needs 5 and
   "`Cᵢ₋₁` is a piece"; the field `miss` is automatic (`Thm1Setup.comp_disjoint_G_of_ess`).

### 4.2 E2.4 (open)

`H` = the subcontinuum `N` of `L` with `yᵢ` in one end set and `yᵢ₋₁` in the other (the only candidate
the text names). The hypotheses of `Property2At`:
* *essential to `h[R(E)]`*: printed for `N`; `h⁻¹[N] ⊆ R(E)` holds since `N ⊆ L` and `L` is an extension
  of an essential set — not formalized;
* *minimal admissible decomposition*: needs the restriction of the decomposition of `L` to a
  sub-interval (`d_L⁻¹[[a, b]]` reparametrized) — not formalized;
* *end sets within `ε₃`*: **not implied.** The assumption is `ρ(yᵢ₋₁, d⁻¹[I]) < ε₃`, and Property 4 with
  the cap gives `ρ(yᵢ, Cl S_I) < ε₃`. *Configuration:* `yᵢ` and `yᵢ₋₁` within `ε₃` of `S_I` at heights
  differing by more than `3ε₃`; then the end sets of `N` are not within `ε₃`, and since `L ∩ F = ∅` no
  end set of a subcontinuum of `L` is attached to the point of `d⁻¹[I]` near `yᵢ₋₁`;
* *a layer farther than `ε₂` from the first end set*: needs the passage of `L` around a strand end —
  not formalized.

The conclusion of Property 2 (`H` comes within `ε₂` of every point of `R(E)`) would be contradicted
by `N` not coming within `ε₂` of `π⁻¹(p₄)` (printed: "the continuum `N` does not come within `ε₂` of
`π⁻¹(p₄)`"), once a point of `R(E)` over `p₄` is exhibited. Not formalized.

## 5. Case 2, claim (e) (open)

* *Extending `Cl Cᵢ` away from `Z`.* In print, `Z` is the end set at the side of `d⁻¹(x₂ᵢ₋₁)` in both
  cases (Case 1: "`π⁻¹[⟨p₁, r⟩]` meets `Z`, `d⁻¹(x₂ᵢ₋₁)`, and `d⁻¹(x₂ᵢ₋₂)`"; Case 2: "`π⁻¹[⟨p₅, s⟩]`
  meets `Z`, `d⁻¹(x₂ᵢ₋₁)`, and `d⁻¹(x₂ᵢ₋₃)`"), and both cases extend away from `X`. Extending away from
  `Z` changes the side at which `L` leaves `Cl Cᵢ`, but not the gap continuum `d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]`,
  which in Case 2 meets both side segments and so cuts the region between `S_J` and `S_I`. The band
  `P` of Case 1 needs that region closed on one side by the gap continuum and open on the other for
  `Q`; the change of direction does not produce this. Not a reduction to Case 1.
* *Property 2 for `f[N]`.* `f[N]` is essential to `h₁[R(E)]`, and Property 2 (for `h₁`, an
  `ε₃`-homeomorphism) gives: if the end sets of `f[N]` are within `ε₃` and a layer is `ε₂`-far, `f[N]`
  comes within `ε₂` of every point of `R(E)`. This bounds how far `f[N]` reaches, not on which side of
  `S_J` the point `f(yᵢ₋₁)` lies.

(e) stays the field `claim_e` of `Case2WitnessO`. *Configuration:* `yᵢ₋₁` and `f(yᵢ₋₁)` both below
`S_J` (as batch 181).

## 6. Ledger entries

`LEDGER.md` §6, subsection "Hagopian 1976 XXVII … (batch 182)", six checks:
1. p. 348, "The proof now breaks down into two cases": fails at `i = 2` (`blockLayersMeetSides_false`);
   the last step read separately (`last_step_ending`); unargued for `i ≥ 3`.
2. p. 348, "(Other cases are handled with similar arguments …)": symmetric where the cap is used
   (`cross_strand_near_above`), correcting batch-181 check 5; two configurations not treated.
3. p. 348, "The existence of `Cᵢ₋₁` follows from …": open; `L ∩ F = ∅` closed.
4. p. 348, "for otherwise, a subcontinuum of `L` would violate Property 2": open; "end sets within `ε₃`"
   not implied.
5. p. 349, Case 2 (e): unsupported, open; neither idea decides it.
6. The end layer of `F`: `closure_G_diff_E`, `K∓` continua; `τ₁ = 1` undecided.

No statement of Hagopian's is refuted; the count of defective proofs stays at fourteen.

## 7. Axioms

Every theorem of the group *Hagopian 1976 XXVII (batch 182)* of `Axioms.lean` (45 declarations)
uses exactly `propext`, `Classical.choice`, `Quot.sound`. The output is in
`doc/batches/audits/axioms-batch182.txt`. `axioms.txt`: 2160 lines (2115 + 45 added, none
removed), `sorryAx` in none.

## 8. Dependency map of Theorem 1 (updated)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_cases2                       [proved]
   ├─ hagopian76_theorem1_of_step_tight                [proved]
   │  └─ exists_thm1Setup_tight                        [proved]
   │     └─ hagopian76_T15_T17_cond5                   [proved]
   ├─ hICC: InnerComponentsCross on (3/22+8/n, 19/22−8/n)       [OPEN, 2e]
   │  ├─ §3.1 noncrossing_half_in_O                    [open]
   │  │  ├─ step 1 kminus/kplus_isContinuum, half_bump [proved]
   │  │  ├─ step 2 half_bump_side                      [proved]
   │  │  ├─ step 3 closure_G_diff_E                    [proved]
   │  │  └─ steps 4–5                                  [open]
   │  ├─ 2a–2c                                         [proved]
   │  └─ 2d: zⱼ, (iii) [open]; τ₁ < 1 [proved]; step 2, τ₁ = 1 [open]
   ├─ stepStrands_of_frame (E0 + E1)                   [proved]
   │  └─ StepFrame                                     [OPEN]
   │     └─ GoodPoint.miss, comp f(y) misses F         [proved: comp_disjoint_G_of_ess, comp_f_disjoint_G]
   └─ hagopian76_property4_step_cond2                  [proved]
      ├─ i = 2: not_property4_x3x4                     [proved]
      │  ├─ last_step_ending                           [proved]
      │  └─ LastStepClaims (proof by contradiction)    [OPEN]
      ├─ BlockLayersMeetSides3 (i ≥ 3)                 [OPEN]
      ├─ case1_ending_oriented                         [proved]
      │  └─ cross_strand_near_o (cap, both sides)      [proved]
      ├─ Case1Claims' (first, between, far, band)      [OPEN]
      │  ├─ first: L ∩ F = ∅ extension_misses_G        [proved]; Cᵢ₋₁, L [open]; K_meets_crossing [available]
      │  └─ far (E2.4)                                 [open]
      ├─ case2_ending_oriented ((c))                   [proved]
      └─ Case2Claims' ((a), (b), (d), (e))             [OPEN]
```

## 9. Skeleton proposal for what remains

```lean
/-- §1.3: along a crossing component, `d` is monotone in the horizontal coordinate over `D`. -/
theorem d_monotone_on_crossing (S : Thm1Setup M) {C : Set Pt} (hC : IsCrossingPiece …) :
    ∀ p q ∈ closure C ∩ O, … → (S.D.d p ≤ S.D.d q ↔ horiz p ≤ horiz q) ∨ (… ≥ …) := by sorry

/-- §3.1 steps 4–5: the components of `K⁻ ∩ O` and `K⁺ ∩ O` through `y` reach opposite sides. -/
theorem half_components_cross (S : Thm1Setup M) … : IsCrossingPiece … ∨ … := by sorry

/-- §4.1 steps 1–3: the first crossing component met by an extension, and the shortest `L`. -/
theorem exists_first_crossing (S : Thm1Setup M) {y : M} (hy : S.GoodPoint y) … :
    ∃ (L : Set M) (d : L → unitInterval) (y' : M), IsMinimalAdmissible L d ∧ y ∈ L ∧ y' ∈ L ∧
      S.GoodPoint y' ∧ IsCrossingPiece … (S.comp y') := by sorry

/-- §4.2: the subcontinuum of `L` between two layers has a minimal admissible decomposition. -/
theorem minimalAdmissible_restrict {L : Set M} {d : L → unitInterval}
    (hL : IsMinimalAdmissible L d) {a b : unitInterval} (hab : a < b) :
    ∃ e, IsMinimalAdmissible (layerSet d (Icc a b)) e := by sorry

/-- The two configurations with `d⁻¹[J]` on the side of `f(yᵢ)` (§2.2). -/
theorem step_f_between (S : Thm1Setup M) … : Property4 S.D uJ vJ := by sorry
```

## 10. Delivery

* `doc/batches/batch182-MANIFEST.txt`: `git diff --name-status` against the run's initial commit
  (`8e3fe46`), plus uncommitted changes (none), plus the manifest itself and the file the report names
  that this run did not change (`HPC/Hagopian/H76CapLow.lean`).
* `doc/batches/batch182-files.tar.gz`: every file of the manifest at its final content (the two
  uploads, moved from the root, at their new places in `doc/batches/` and `doc/batches/skeletons/`).
