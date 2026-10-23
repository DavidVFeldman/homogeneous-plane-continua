Commission read: `doc/batches/COMMISSION-batch181.md` ("Commission: batch 181 — Part E, Hagopian 1976 XXVI: Theorem 1 — saturation; 3c; Case 1 strand by strand; Case 2 sentence by sentence").

# Report, batch 181

## 0. Summary, omissions

All new declarations compile without `sorry` and use only `propext`, `Classical.choice`,
`Quot.sound` (§7). `axioms.txt` has 2115 lines; `sorryAx` occurs in none.

```
STATUS: §3.1 hε₃O, hε₃S proved (fields of Thm1Setup; exists_thm1Setup restated)
STATUS: §3.1 f(y) ∈ π⁻¹[D] for y ∈ K proved (f_mem_O_of_mem_K)
STATUS: §3.2.1 above_closure_misses_bottom proved
STATUS: §3.2.2 cross_strand_near proved
STATUS: §3.2.3 mirror proved with an extra hypothesis (cross_strand_near_mirror)
STATUS: §1.1 noncrossing_half_in_O open (component of K⁻ ∩ O through y; closure of F − E meets E only in d⁻¹(e))
STATUS: §1.2–§1.3 open (points zⱼ; non-crossing of Wⱼ; (iii) at zⱼ)
STATUS: §1.4 step 3 proved (tip_triod_mirror_rel, chunk_edge_case_mirror)
STATUS: §1.4 steps 1, 2 open (need §1.2–§1.3); step 4 (τ₁ = 1) open (configuration stated, §1.4)
STATUS: §1.5 2e innerComponentsCross_hagopian open (needs §1.1–§1.4)
STATUS: §2.1 3c block_components_cross proved (InnerComponentsCross as hypothesis)
STATUS: §2.2 E0, E1 proved (property4_strand, property4_step_unless_setup)
STATUS: §3.3–§3.6 open (named fields of Case1Witness)
STATUS: §3.7 ending proved (case1_ending)
STATUS: §3.8 case1 proved, conditional on Case1Claims
STATUS: §4 (c) proved (inside case2_ending); (a), (b), (d) open; (e) open, unsupported by the text
STATUS: §4 case2 proved, conditional on Case2Claims
STATUS: §5 hagopian76_property4_step_cond proved, conditional; hagopian76_theorem1_of_cases proved, conditional
```

**Omitted, with reason (§0 of the rules).**
* `H76Tip.lean` is not edited. §1.4 asked to relax the hypothesis of `tip_triod_mirror` "or add a
  variant": the variant is `H76TipRel.lean` (`tip_meets_end_layer_mirror_rel`, `tip_triod_mirror_rel`).
* §1.1–§1.4 (except step 3) and 2e are not formalized; they are recorded in the comment block at the end
  of `Hagopian76Z.lean` and in `OPEN.md`. Their skeleton statements are kept there, commented out.
* §3.3 items 1–6 and §3.4–§3.6 are not proved: they are fields of the structure `Case1Witness`
  (see §3). §4 (a), (b), (d), (e) are fields of `Case2Witness`.
* The corollary of §2.1 ("the gap layers miss the points over the interval") is not stated separately;
  the claim of commission 178 §3c on the end layers of blocks is dropped: E0 and E1, as formalized,
  do not need it.
* `hagopian76_theorem1_of_step` is not restated; the new reduction is the separate theorem
  `hagopian76_theorem1_of_cases`.

**Shape changes** (each also recorded at the statement):
1. `block_components_cross` takes a general interval `(lo, hi)` and `InnerComponentsCross` on it
   as a hypothesis, instead of the fixed `(3/22 + 8/n, 19/22 − 8/n)`.
2. `hε₃O` is stated for points `m ∈ M − E` within `ε₃` of a point of `Mid`, with conclusion
   `π m ∈ F[D′]` (membership in `O`); `hε₃S` with the closed side segments `{3/22, 19/22} × [0, c₁]`.
3. `cross_strand_near_mirror` carries the hypothesis that `a` is `ε₃`-far from `π⁻¹` of the bottom
   edge (§2.2 below explains why).
4. The open claims of Cases 1–2 are packaged as structures (`Case1Witness`, `Case2Witness`), and the
   named `Prop`s `Case1Claims`, `Case2Claims` ask for a witness only when `I` has Property 4 and `J`
   does **not** (the antecedent `¬ Property4 J` makes the claims weaker, hence the conditional
   theorems stronger).
5. `Case1Witness.far` uses `Cl S_I` in place of `d⁻¹[I]` (`ρ(y, Cl S_I) ≥ ε₃` is weaker than
   `ρ(y, d⁻¹[I]) ≥ ε₃`).
6. The case split itself (both end layers meet a side segment) is a named `Prop`,
   `BlockLayersMeetSides`.

## 1. Saturation (§1)

### 1.1 `noncrossing_half_in_O` (open)

The statement is in the comment block of `Hagopian76Z.lean`. Steps 2, 4, 6, 7 of the route are
available (T7, S0, `isCrossingPiece_of_crossingComponent`). The obstruction:
* step 1 applies boundary bumping to the half `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]`, which need not be
  connected. The route needs a continuum in `K⁻` through `y` that is not contained in `O`, and the
  component of its intersection with `O` through `y`; this is not formalized;
* step 3 needs "the closure of `F − E` meets `E` only in `d⁻¹(e)`", which is not formalized.

### 1.2–1.3 The points `zⱼ`, (iii) at `zⱼ` (open)

Not formalized. The pieces used would be: the void interior of `d⁻¹(1)` in `F` (available) transported
to `F ∩ U`; `crossing_components_finite` (available) together with the closedness of crossing
components in `O`; the strand lemma at `zⱼ` for (iii).

### 1.4 The edge case

* **Step 3 (proved, `τ₁ < 1`).** The mirror tip lemmas use the extreme point over `D` only to obtain
  `σ < 1` and `σ > 2/n`. `tip_meets_end_layer_mirror_rel` and `tip_triod_mirror_rel` take these two
  bounds as hypotheses. `chunk_edge_case_mirror` is step 3: with `zⱼ = h(e₁)`, `k(e₁) = τ > 2/n`, off
  `d⁻¹(1)`, `τ₁ > τ` attained in `F ∩ h[E]`, every point of `F ∩ h[k⁻¹[[τ, 1]]]` of parameter `≤ τ₁`,
  and `τ₁ < 1`, (iii) leads to a contradiction. The bound the proof needs is `2/n < τ₁ < 1`; the first
  follows from `τ > 2/n`.
* **Steps 1, 2 (open).** Need §1.2–§1.3.
* **Step 4, `τ₁ = 1` (open).** The configuration: `F ∩ hⱼ[k⁻¹((τ, 1])] ⊆ d⁻¹(1)` and
  `F ∩ hⱼ[k⁻¹(1)] ≠ ∅`, with `zⱼ = hⱼ(e₁)`, `k(e₁) = τ`, off `d⁻¹(1)`. Neither 3a nor the void interior
  of `d⁻¹(1)` in `F` excludes it directly: the set `F ∩ hⱼ[k⁻¹((τ, 1])]` need not be open in `F`. Not
  decided.

### 1.5 2e (open)

Case tree (for `c` over `(3/22 + 4/n, 19/22 − 4/n)` on a non-crossing component `W`):
1. `W` non-crossing ⇒ one half in `O` (§1.1) [open];
2. `d(c) < 1`, (iii) at `c`: `tip_triod` / `tip_triod_mirror` / `tip_triod_on_tip_layer` [proved];
3. `d(c) = 1`: points `zⱼ` (§1.2) with (iii) (§1.3) [open];
   * `zⱼ` off its tip layer: `tip_triod` with `b = 1` [proved];
   * `F ∩ hⱼ[E] ⊆ Tⱼ`: §1.4 step 2 [open];
   * `τ < τ₁ < 1`: `chunk_edge_case_mirror` [proved];
   * `τ₁ = 1`: §1.4 step 4 [open];
4. degenerate chunk: `degenerate_chunk_iii` [proved].

## 2. 3c, E0, E1 (§2)

### 2.1 3c (proved)

`block_components_cross` (`H76Block3c.lean`): with `InnerComponentsCross` on `(lo, hi)`, a point `z`
of `d⁻¹[B] ∩ O` over `(lo, hi)`, `B = [x₂ᵢ₋₁, x₂ᵢ]`, has the same component in `d⁻¹[B] ∩ O` as in
`F ∩ O`. Route as commissioned: `isCrossingComponent_of_piece` (closed side segments, using
`r₂ ≤ c₁`, `s₂ ≤ c₁`), the irreducible interval contains `d(z)`, `IsBlocks.block_eq`
(pairwise disjoint blocks), `inner_component_in_block`. `lemma3_half` is not used.

The end-layer claim of commission 178 §3c is dropped: `property4_strand` uses only 3c.

### 2.2 E0, E1 (proved), the parenthesis

* `property4_strand` (E0, ⇒): if `B` separates a good point `y` from `f(y)` in `O` and the component
  of `f(y)` is a piece missing `F`, some `B`-strand `S_B` has `y` and `f(y)` on opposite sides.
  (Uses 3c, `sepByCrossing_of_inner_crossing`, `VFrame.opposite_of_sepIn`.)
* `property4_step_unless_setup` (E1): with `y` below `S_I`, `f(y)` above, `S_J ≺ S_I`: `J` has
  Property 4 at `y`, or `y`'s component is above `S_J` and `y` below `S_I` ("between").
* `property4_of_strand_sep`: opposite sides of a block strand ⇒ Property 4 at a good point.

**The parenthesis.** The four configurations: `f(yᵢ)` above or below `S_I`; `d⁻¹[J]` below or above
`d⁻¹[I]`. Exchanging "above" and "below" exchanges the bottom edge (over `E`) and `I₂`. E0 and E1 are
symmetric (both orders are in `property4_strand`; `sepIn_of_below_below` and its use in
`property4_of_strand_sep` cover both). The cap lemma is not: in the mirror, the region below a
crossing piece reaches the bottom edge, which lies over `E`. `cross_strand_near_mirror` therefore
needs `a` to be `ε₃`-far from `π⁻¹` of the bottom edge; this is not uniform on `Mid` (a point of
`K₀` can be arbitrarily close to `E`). The other ingredients of the mirror (no exit through `I₂`, no
exit through the sides) hold as before; `notMem_closure_below_of_above` is the abstract mirror of
`above_closure_misses_bottom` in the frame, but over the bottom edge the closure of the region below
does reach `π⁻¹` of the edge.

## 3. Case 1 (§3)

### 3.1 The fields (proved)

`Thm1Setup.hε₃O`, `Thm1Setup.hε₃S` (`H76Thm1Setup.lean`), chosen after `D′` and before `F`
(`exists_eps_mid_O`, `exists_eps_mid_sides`, `H76Mid.lean`; `ε₃ = min(min(ε₃′, θ/2), min(δS, δO))`).
`Mid = midSet` ⊇ `K` (`Thm1Setup.K_subset_mid`). `f_mem_O_of_mem_K`: for `y ∈ K` with
`h⁻¹(y) ∈ R(E)`, `f(y) ∈ π⁻¹[D]` (via `f(y) ∉ E`, from `hcomp`).

### 3.2 The cap lemma (proved)

`above_closure_misses_bottom` and `cross_strand_near` as commissioned (`H76CapLow.lean`);
mirror `cross_strand_near_mirror` with the hypothesis above.

### 3.3–3.6 (open; fields of `Case1Witness`)

| Field | Printed sentence | Obstruction |
| --- | --- | --- |
| `first` (`GoodPoint y`) | E2.1, "Let `Cᵢ₋₁` be the first component … essential … `yᵢ₋₁`" | existence of a first crossing component met by an extension (items 1–3), `L ∩ F = ∅` (item 6) not formalized; item 4 is `K_meets_crossing` (available); item 5 is the field `ess` |
| `strandI`, `strandJ` | (β), the adjacent strands | follow from 3c once `yᵢ₋₁` is placed; not formalized |
| `between` | §3.4, "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` …" | the configuration of report 180 §4.5 (`L` leaves `D` through a side segment and re-enters on the other side of a strand's end) is not excluded by the Case 1 hypothesis, the minimality of `L` or `L ∩ F = ∅` |
| `far` | §3.5, E2.4 | `H` = the subcontinuum of `L` from `Cl Cᵢ` to `Cᵢ₋₁`, end sets `Cl Cᵢ ∩ H` and `Cl Cᵢ₋₁ ∩ H`; essential: from `ess`; minimal admissible decomposition: not formalized for subcontinua of extensions; end sets within `ε₃`: from `ρ(yᵢ₋₁, d⁻¹[I]) < ε₃` and Property 4 for `I`; far layer: from the passage of `L` around the strand; none formalized |
| `band` | §3.6 | `Q` (segment of the vertical over `15/22`), `P`, `f[N] ∩ d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] = ∅` (available: `f_notMem_G_of_Rset`); `f[N] ∩ Q = ∅` needs "`N` is `ε₂`-far from `Q`", argued in the text only for `π⁻¹(p₄)` |

### 3.7 The ending (proved)

`case1_ending`: a good point `y` between `S_J` and `S_I`, `ρ(y, Cl S_I) ≥ ε₃`, `f(y)` above `S_I` or
below `S_J` ⇒ `J` has Property 4. Above `S_I` is excluded by `cross_strand_near`.

### 3.8 `case1` (proved, conditional)

`case1 : Case1Claims S x m → … → Property4 I → Case1Config S x i → Property4 J`.

## 4. Case 2 (§4)

* **(a)** field `claim_a`; open, as §3.4.
* **(b)** field `claim_b`, in the form left after the good case (if `f(yᵢ₋₁)` is below `S_J`, `J`
  separates at once; this split is proved inside `case2_ending`). The band of Case 1 uses an arc `Q`
  joining `d⁻¹[I]` and `d⁻¹[J]` on the side where the gap continuum `d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]` does not
  reach; in Case 2 the gap continuum meets both side segments, so the region between `S_J` and `S_I`
  is already cut, and `Q` would have to be chosen inside one of the two pieces. Not decided.
* **(c)** proved: from (b), `cross_strand_near` gives `ρ(yᵢ₋₁, Cl S_I) < ε₃` (in `case2_ending`).
  For `yᵢ` the same follows from Property 4 for `I`.
* **(d)** field `claim_d`; open, as §3.5, with both end sets of `N` near `d⁻¹[I]`.
* **(e)** field `claim_e`; open. **Configuration:** `yᵢ₋₁` below `S_J`, `f(yᵢ₋₁)` below `S_J` too.
  Property 2 applied to `N` and `f[N]` gives a lower bound on how far `N` reaches, not a side; the
  Case 2 configuration constrains the ends of `d⁻¹(x₂ᵢ₋₁)`, `d⁻¹(x₂ᵢ₋₂)`, not `f`; another choice
  of `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁` moves `f(yᵢ₋₁)` by less than `ε₃`, and nothing printed fixes its side. Not
  excluded.
* **`x₂ᵢ₋₃`.** Reading it as `x₂ᵢ₋₂` would contradict the case hypothesis (unless a layer meets both
  side segments). As printed it is an extra assumption on `d⁻¹(x₂ᵢ₋₃)`; `case2` does not use it.

`case2_ending` (proved) and `case2 : Case2Claims S x m → … → Property4 J` (proved, conditional).

## 5. The step

`hagopian76_property4_step_cond : BlockLayersMeetSides S x m → Case1Claims S x m →
Case2Claims S x m → Property4Step S.D x m` (`case1_or_case2` gives the split; `IsBlocks` not used).
`hagopian76_theorem1_of_cases`: `InnerComponentsCross` for every set-up and the three named `Prop`s
for every block sequence ⇒ `Hagopian76Thm1`.

### Named `Prop`s and structures

| Name | Kind | Content |
| --- | --- | --- |
| `Thm1Setup.comp` | def | component of `y` in `M ∩ π⁻¹[D]` |
| `Thm1Setup.GoodPoint` | structure | `y ∈ K`, `Cl C_y` essential, `C_y` a piece missing `F` |
| `Thm1Setup.IsBlockStrand` | structure | crossing piece, piece, inside `d⁻¹[[u, v]]` |
| `Thm1Setup.LayerMeetsSide` | def | `d⁻¹(u)` meets the closed side segment over `a` |
| `Case1Config`, `Case2Config` | def | the two printed cases |
| `Case1Witness` | structure | §3.3–§3.6 |
| `Case1Claims` | named `Prop` | a `Case1Witness` whenever `I` has Property 4, `J` not, Case 1 |
| `Case2Witness` | structure | §4 (a), (b), (d), (e) |
| `Case2Claims` | named `Prop` | a `Case2Witness` likewise |
| `BlockLayersMeetSides` | named `Prop` | the case split |
| `midSet` | def | `Mid` of §3.1 |

## 6. Ledger entries

`LEDGER.md` §6, subsection "Hagopian 1976 XXVI … (batch 181)", seven checks:
1. p. 348, "Note that `f(yᵢ₋₁)` belongs to `L₆ ∩ π⁻¹[D]`": correct with a bound not stated (`hε₃O`).
2. p. 349, "It is not above `d⁻¹[I]` because …": gap in exposition, closed (`cross_strand_near`).
3. pp. 348–349, `N` and `π⁻¹(p₄)` versus `Q`: gap, open.
4. p. 348, "By considering the position …": gap, open (configuration of report 180 §4.5).
5. p. 348, "(Other cases …)": the cases are not mirror images; mirror cap needs a hypothesis.
6. p. 349, Case 2: (c) proved from (b); (a), (b), (d) unargued; (e) unsupported; `x₂ᵢ₋₃` probably not
   a misprint for `x₂ᵢ₋₂`.
7. The end layer of `F`: partly closed (`τ₁ < 1`); `τ₁ = 1` undecided.

No statement is refuted; the count of defective proofs stays at fourteen.

## 7. Axioms

Every theorem of the group *Hagopian 1976 XXVI (batch 181)* of `Axioms.lean` (62 declarations, 64 lines of output, plus
the restated `exists_thm1Setup`) uses exactly `propext`, `Classical.choice`, `Quot.sound`. The output
is in `doc/batches/audits/axioms-batch181.txt`. `axioms.txt`: 2115 lines (2051 + 64 added, none removed), `sorryAx` in none.

## 8. Dependency map of Theorem 1 (updated)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_cases                    [proved]
   ├─ hagopian76_theorem1_of_step                  [proved]
   │  └─ exists_thm1Setup (with hε₃O, hε₃S)        [proved]
   ├─ hICC: InnerComponentsCross on (3/22+8/n, 19/22−8/n)     [OPEN, 2e]
   │  ├─ §1.1 noncrossing_half_in_O                [open]
   │  ├─ 2a tip_triod, tip_triod_mirror            [proved]
   │  ├─ 2b tip_triod_on_tip_layer                 [proved]
   │  ├─ 2c degenerate_chunk_iii                   [proved]
   │  └─ 2d: §1.2–§1.3 [open]; §1.4 step 3 chunk_edge_case_mirror [proved];
   │         steps 1, 2, 4 [open]
   └─ hagopian76_property4_step_cond               [proved]
      ├─ BlockLayersMeetSides                      [OPEN]
      ├─ case1                                     [proved]
      │  ├─ case1_ending                           [proved]
      │  │  ├─ cross_strand_near                   [proved]
      │  │  │  ├─ above_closure_misses_bottom      [proved]
      │  │  │  └─ hε₃S, hε₂I                       [fields]
      │  │  └─ property4_of_strand_sep             [proved]
      │  └─ Case1Claims (first, between, far, band)  [OPEN]
      │     ├─ f_mem_O_of_mem_K, K_meets_crossing  [proved, available]
      │     └─ 3c block_components_cross, E0, E1   [proved, available]
      └─ case2                                     [proved]
         ├─ case2_ending ((c))                     [proved]
         └─ Case2Claims ((a), (b), (d), (e))       [OPEN]
```

## 9. Skeleton proposal for what remains

```lean
/-- §1.1 with the half as a continuum: the component of `K⁻ ∩ O` through `y`. -/
theorem half_component_bumps (S : Thm1Setup M) … : (closure (connectedComponentIn (K⁻ ∩ O) y) ∩
    frontier O).Nonempty := by sorry

/-- §1.1 step 3: the closure of `F − E` meets `E` only in `d⁻¹(e)`. -/
theorem closure_G_diff_E (S : Thm1Setup M) : closure (toPt S.D.G \ toPt S.E) ∩ toPt S.E ⊆
    toPt (layer S.k 1) := by sorry

/-- §1.4 step 4: `τ₁ = 1` is impossible. -/
theorem chunk_edge_case_full (S : Thm1Setup M) … (hτ₁ : τ₁ = 1) : False := by sorry

/-- E2.1: the first crossing component met by an extension of `Cl Cᵢ` away from `X`. -/
theorem exists_first_crossing (S : Thm1Setup M) … : ∃ L C, IsShortestExtension L C ∧
    Disjoint L (toPt S.D.G) := by sorry

/-- E2.4 / Case 2 (d): the subcontinuum of `L` violating Property 2. -/
theorem property2_violation_of_near (S : Thm1Setup M) … : False := by sorry

/-- §3.6: `N` is `ε₂`-far from `Q` (possibly with `ε₂` small relative to a modulus of `π`). -/
theorem N_far_from_Q (S : Thm1Setup M) … : ∀ z ∈ N, S.ε₂ ≤ infDist z Q := by sorry

/-- The case split: both end layers meet a side segment. -/
theorem blockLayersMeetSides (S : Thm1Setup M) (hx : S.IsBlocks x m) :
    BlockLayersMeetSides S x m := by sorry
```

## 10. Delivery

* `doc/batches/batch181-MANIFEST.txt`: `git diff --name-status` against the run's initial commit
  (`b191dbc`), plus any uncommitted change.
* `doc/batches/batch181-files.tar.gz`: every file of the manifest, at its final content.
