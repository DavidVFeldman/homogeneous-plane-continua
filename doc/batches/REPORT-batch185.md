Commission read: `doc/batches/COMMISSION-batch185.md` ("Commission: batch 185 — Part E, Hagopian 1976 XXX: Lemma 7 of 1984; saturation; the case split").

# Report, batch 185

## 0. Summary, omissions

The two-sided extension and **Lemma 7 of Hagopian 1984 are proved** (Lemma 7 by a route other than the
printed one). With them, **saturation (2e) for Hagopian's `F` is proved unconditionally**
(`innerComponentsCross_hagopian`), by the commission's tip argument (§4.2) and steps 4–5 (§4.1). **The
case split for `i ≥ 3` is proved** by the commission's route (§5), without Lemma 7, and the same
argument locates `d⁻¹(x₃)` (it meets a closed side segment). Rigidity (§3.1) and runs (§3.2) are
proved. Theorem 1 now follows from the four named `Prop`s `StepFrame`, `LastStepClaims`,
`Case1ClaimsE24`, `Case2ClaimsE24` alone (`hagopian76_theorem1_of_cases4`): `hICC` and
`BlockLayersMeetSides3` are discharged and `Hagopian84Lemma7` is not needed. §3.3 and §6 are open.
No `sorry` in any declaration; nothing refuted.

Status lines:
* STATUS: §0 `wset84_eq_wset` proved
* STATUS: §1 `hagopian84_two_sided` proved
* STATUS: §2 `hagopian84_lemma7` proved; `Hagopian84Lemma7` stated and proved (`hagopian84Lemma7_holds`)
* STATUS: §3.1 `layers_agree` proved
* STATUS: §3.2 `translate_run`, `translate_run_right` proved
* STATUS: §3.3 `crossing_component_run` open (degenerate case of `layers_agree` and the end layer
  `d⁻¹(0)` not excluded; no shape usable for §6)
* STATUS: §4.1 `noncrossing_half_in_O_steps45` proved
* STATUS: §4.2 `half_in_O_false` proved
* STATUS: §4.3 `innerComponentsCross_hagopian` proved (unconditional)
* STATUS: §5 `blockLayersMeetSides3` proved; `layer_x3_meets_side` proved
* STATUS: §6 `case1_between_runs` open (§3.3)
* STATUS: §7 `hagopian76_theorem1_of_cases4` proved

**Omissions** (asked for, not done):
* `innerComponentsCross_hagopian_of_lemma7` (§4.3) is not stated: §2 is proved, so the conditional
  form would only restate `innerComponentsCross_hagopian` with an extra hypothesis that holds.
* §3.3 and §6 are not proved; their statements are commented out at the end of
  `HPC/Hagopian/Hagopian76AC.lean` with the obstruction (§3.3, §6 below; `OPEN.md`).
* §5, "record which side each layer meets": the argument does not determine the side; only that one
  of the two closed side segments is met (§5 below).
* `Hagopian76AA.lean` is unchanged: its commented-out `noncrossing_half_in_O` is not proved here in
  that shape (it is superseded: under its hypotheses, `half_in_O_false` refutes both disjuncts and
  `innerComponentsCross_hagopian` refutes `hW`), so it is not a copy of a statement proved here.

**Shape changes** (each also recorded at the statement):
* `layers_agree`, `translate_run`, `translate_run_right`, `noncrossing_half_in_O_steps45`,
  `half_in_O_false`, `blockLayersMeetSides3`: the skeleton left the shape open (`True`); shapes in
  §3–§5 below.
* `hagopian84_two_sided`, `hagopian84_lemma7`, `Hagopian84Lemma7`, `wset84_eq_wset`,
  `innerComponentsCross_hagopian`: unchanged.
* `hagopian76_theorem1_of_cases4`: the `Hagopian84Lemma7` hypothesis is dropped (proved).
* New: `layer_x3_meets_side` (§5).

## 1. The two-sided extension (`hagopian84_two_sided`, proved)

The commission's route, steps 1–5, holds, with one change in step 3. File `H84TwoSided.lean`.
1. Lemma 4 gives `F₁` away from `X = k⁻¹(0)` and `F₂` away from `Z = k⁻¹(1)`.
2. `F₁ ∩ F₂ = E` (`ext_inter_ext_subset`). Writing `F₁ = E ∪ T₁`, `F₂ = E ∪ T₂` with the tails
   meeting `E` only in `Z`, resp. `X`, the intersection is a continuum (hereditary unicoherence) inside
   `E ∪ (T₁ ∩ T₂)`; a point of `T₁ ∩ T₂` off `E` leads, as in the commission, to `X ∩ Z ≠ ∅`.
3. *Change:* instead of re-parametrizing three pieces, `H = F₁ ∪ T₂` is obtained by a general gluing
   lemma (`glue_minimalAdmissible`): two minimal admissible `(A, a)`, `(B, b)` meeting exactly in
   `a⁻¹(0) = b⁻¹(0)` glue to a minimal admissible `(A ∪ B, c)` with `c⁻¹((1 + t)/2) = a⁻¹(t)`,
   `c⁻¹((1 − t)/2) = b⁻¹(t)`. Continuity by the pasting lemma on the two closed pieces; void
   interiors pass to the union (`interior_layer_of_subset_empty`).
4. Irreducibility: a continuum meeting both end layers of a type λ continuum is all of it
   (`eq_of_meets_end_layers`), applied on each side, with hereditary unicoherence for `K ∩ A`.
5. `E` is essential in `H` (it meets more than one layer, and its layers are layers of `H`) and misses
   both end sets.

## 2. Lemma 7 of 1984 (`hagopian84_lemma7`, proved)

Shape of the batch-184 commented block. File `H84Lemma7.lean`. Not the printed proof: with `H ⊇ E` and
`I ⊇ F` the two-sided extensions, `k⁻¹(r)` is an interior layer `u` of `H` (Lemma 6), and
`K = H ∩ F` is a continuum through a point of `F ∩ k⁻¹(r)`. Case split (`two_layers_or_subset`):
* `K` inside the `H`-layer `u`: `F ⊄ H` (else `F ⊆ k⁻¹(r) ⊆ E`), so `F` is a third arm of a triod with
  core `k⁻¹(r)` (`no_arm_at_interior_layer`: `G ∪ A` with arms `g⁻¹[0, u)`, `g⁻¹(u, 1]`,
  `A∖g⁻¹(u)`). Impossible.
* `K` meets two `H`-layers and two `F`-layers: Lemma 6 twice (`layer_common_of_essential`) gives
  `k⁻¹(r) = d⁻¹(v)`.
* `K` meets two `H`-layers and lies in one `F`-layer `Y`: `Y` is an interior `I`-layer. If `H ∩ I`
  met two `I`-layers, two distinct `H`-layers in `K ⊆ Y` would both equal the `I`-layer `Y`; so
  `H ∩ I ⊆ Y` and `H` is a third arm at `Y` (a point of `E∖F` lies off `Y`). Impossible.

The steps of H84.4 (the point `x`, `k⁻¹(r) ⊂ F`, the point `y`) are not used. The named `Prop`
`Hagopian84Lemma7` is stated as in the skeleton and proved (`hagopian84Lemma7_holds`).

## 3. Rigidity and runs

**3.1 `layers_agree` (proved).** *Shape:* `(E, k)`, `(G, d)` minimal admissible, `E ∩ G` meeting two
layers of `E`. Then either `E ⊆ d⁻¹(v)` for some `v`, or
`E ∩ G = k⁻¹[[a, b]] = d⁻¹[[a′, b′]]` (`a < b`, `a′ < b′`), each `k`-layer meeting `G` is a `d`-layer
and each `d`-layer meeting `E` is a `k`-layer. Proof: Lemma 7 when neither contains the other, Lemma 6
when one contains the other, hereditary unicoherence for the connectedness of `E ∩ G`.

*Degenerate cases.* "`G` inside one layer of `E`" is excluded by the hypothesis. "`E` inside one layer
of `G`" with `E ⊄ G` or `G ⊄ E` is excluded inside the proof (by Lemma 7; when `G ⊆ E` by the
surjectivity of `d`); so the only remaining degenerate case is `E ⊆ d⁻¹(v) ⊆ G`. Whether a type λ
continuum can lie in a single layer of another is not decided. In §4 it does not arise (Lemma 7 is
applied directly, with `h[E] ⊄ F` and `F ⊄ h[E]`); §5 does not use rigidity; §6 would need it for
`F` against a translate, where it can arise only if `h[E]` lies in one layer of `F`.

**3.2 `translate_run`, `translate_run_right` (proved).** *Shape:* `(E, k)` a type λ continuum (the
translate `h[E]` is one, with the map of `exists_image_map`), `(G, d)` another, `G ∩ E ⊆ k⁻¹[[a, 1]]`
with `0 < a`, `k⁻¹(a) = d⁻¹(a′)`. Then `a′ ∈ {0, 1}`. Mirror: `G ∩ E ⊆ k⁻¹[[0, b]]`, `b < 1`. Proof by
atriodicity as in the commission (`no_arm_at_interior_layer` with `A = k⁻¹[[0, a]]`).

**3.3 `crossing_component_run` (open).** What holds:
* A crossing component `C` of `F ∩ π⁻¹[D]` is connected and lies in `M ∩ π⁻¹[D]`, so it lies in the
  strand `S` through any of its points; taking a point over the inner middle, `strand_lemma` gives a
  `θ/4`-translate with `Cl C ⊆ Cl S ⊆ h[E]`.
* `F ∩ h[E]` is a continuum (hereditary unicoherence). It meets two layers of `h[E]`: `C` crosses
  `D` while each layer of `h[E]` projects into a `θ/4`-neighbourhood of one point of `γ` (S0).
* So `layers_agree` applies: either `h[E]` lies in one layer of `F`, or
  `F ∩ h[E] = h[k⁻¹[[a, b]]] = d⁻¹[[a′, b′]]`. In the second case `translate_run` gives: `a = 0` or
  `d⁻¹(a′)` is an end layer of `F`; likewise at `b`. At a translate end, S0 puts the end layer at
  abscissa `< 2/n` or `> 1 − 2/n`, outside `D`'s abscissae.

What is missing (why the item is open):
1. The degenerate alternative, `h[E]` inside one layer of `F` (then `h[E] ⊆ F`), is not excluded.
2. `translate_run` allows the end layer `d⁻¹(0)` of `F` as well as `d⁻¹(1)`; the commission's
   statement has only `d⁻¹(1)`, and `d⁻¹(0)` (which lies in `E`, at the far left) is not excluded.
3. "`F` leaves `D` along the same translate … within the window of S0" needs, in addition, that the
   part of the common segment between `C` and the translate end stays within the S0 window when it
   crosses a side segment; I found no shape that is provable this way and strong enough for §6, and did
   not state one in Lean (proposal in §11).

## 4. Saturation (2e)

**4.1 `noncrossing_half_in_O_steps45` (proved).** *Shape:* `y = h(e) ∈ F` over `D`, `h` a
`θ/4`-homeomorphism, `3/22 + 2/n < k(e) < 19/22 − 2/n`; if neither `K⁻` nor `K⁺` lies over `D`, the
component of `y` in `F ∩ π⁻¹[D]` is a crossing piece. The commission's steps 1–4; the bound `2/n`
(not `8/n`) suffices for step 2. Step 4 uses `closure_crossSet_mem_E` (bottom edge),
T7 (`I₂`) and `isCrossingPiece_of_crossingComponent_G`. File `H76Sat185.lean`.

**4.2 `half_in_O_false` (proved).** *Shape:* for `h(e) ∈ F`, `h` a `θ/4`-homeomorphism and
`2/n < k(e) < 1 − 2/n`, neither `K⁻` nor `K⁺` lies over `D`. The commission's steps 1–7 all hold:
the tip by compactness; `tip_meets_end_layer`; `h[E] ⊄ F` and `F ⊄ h[E]` by S0 (`fine_over_D`,
`two_div_n_le`); Lemma 7 with `h[E]` and `F`; `d⁻¹(1) ⊆ O` against `T12Data.end_layer_not_subset`.
`K⁺` by the mirror (`kplus_not_subset_O`, through `tip_meets_end_layer_mirror`).

**4.3 `innerComponentsCross_hagopian` (proved, unconditional).** Case tree for `y` over
`(3/22 + 8/n, 19/22 − 8/n)` in `F`:
```
y ∈ F ∩ O, choose e, h with h(e) = y, h a θ/4-homeomorphism (Effros / S0)
├─ k(e) ∈ (3/22 + 2/n, 19/22 − 2/n)                     (S0, from the abscissa window of y)
├─ K⁻ ⊄ O   ← half_in_O_false (tip, Lemma 7, end layer not over D)
├─ K⁺ ⊄ O   ← half_in_O_false (mirror)
└─ component of y crosses ← noncrossing_half_in_O_steps45
```
The points `zⱼ`, the chunk, the edge case `F ∩ hⱼ[E] ⊆ Tⱼ` and `τ₁ = 1` (batches 179–183) are no
longer needed: the proof does not use them. The earlier tip results are left as they are.

## 5. The case split for `i ≥ 3` (`blockLayersMeetSides3`, proved)

The commission's route holds as written, without Lemma 7. File `H76Split185.lean`:
* step 1: `IsTightBlocks.left_end_crossing` (for `2 ≤ i ≤ m`), `IsTightBlocks.right_end_crossing`
  (for `3 ≤ i ≤ m`);
* steps 2–3: `left_layer_not_subset`, `right_layer_not_subset`, with upper semicontinuity of the
  layers (`layer_nhds_subset_open`);
* steps 4–5: `layerMeetsSide_of_end` (frontier of `O`, `IsCrossRegion.frontier_sub` excluding `I₂`,
  `mem_E_of_axis` for the bottom edge) and `IsBlocks.layer_disjoint_E`.

**Which side.** The argument gives "one of the two closed side segments" and nothing more; the side is
not recorded because it is not determined.

**`d⁻¹(x₃)` (new, `layer_x3_meets_side`).** The left-end argument works already at `i = 2`
(`x₃ > x₂`), so for tight blocks with `m ≥ 2`, `d⁻¹(x₃)` meets a closed side segment. Only the
right end `x₂` fails at `i = 2` (`blockLayersMeetSides_false`). Notes E3 are updated.

## 6. "Between" with runs (`case1_between_runs`, open)

`translate_run` applies to any type λ continuum against `F`, so in particular to `L` (type λ,
`L ∩ F = ∅`) against the translate of `Cᵢ`: an end of `L ∩ h[E]` that is not a translate end is an end
layer of `L`. But the obstruction of report 183 §3 is about `F` near the side segment: a strand that
only touches the side segment, with `F` having no points outside `D` near its end. §3.3 would exclude
this except at `d⁻¹(1)`, and §3.3 is open (§3.3 above). With §3.3 the remaining step is Bing's
"the arcs end on the side lines" in the form: the common segment of `F` and the strand's translate
reaches the S0 window of a translate end; this is what the open statement asks.

## 7. Theorem 1 (`hagopian76_theorem1_of_cases4`, proved)

*Shape:* `Hagopian76Thm1` from: for every set-up `S` and tight block sequence `x, m`,
`StepFrame S x m ∧ LastStepClaims S x ∧ Case1ClaimsE24 S x m ∧ Case2ClaimsE24 S x m`. Proof:
`hagopian76_theorem1_of_cases3` with `innerComponentsCross_hagopian` and `blockLayersMeetSides3`.

### Non-vacuity notes

The two checks: (1) not refuted by a short argument from the set-up; (2) not equivalent to the
conclusion it is used for, unless the printed argument is a proof by contradiction.

* **`StepFrame`** (hypothesis of `hagopian76_theorem1_of_cases4`).
  1. Unchanged from batch 182 (report 182 §7): it states Hagopian's E0 frame (strands through good
     points in the printed orientation); no short refutation. Saturation, which batch 182 listed as an
     input that might fail, is now proved, so one possible source of refutation is removed.
  2. The conclusion is `Hagopian76Thm1`; `StepFrame` says nothing about decomposable subcontinua of
     `M` and does not imply it alone (the other three are needed).
* **`LastStepClaims`**.
  1. As batch 182: a witness for the last step if `[x₃, x₄]` has Property 4. `layer_x3_meets_side`
     (new) is consistent with it: it locates `d⁻¹(x₃)` on a side segment, as the witness needs.
  2. By design it is equivalent to `¬ Property4 [x₃, x₄]` (via `last_step_ending`); the printed step
     is a proof by contradiction, so this is allowed. It is not `Hagopian76Thm1`.
* **`Case1ClaimsE24`, `Case2ClaimsE24`**.
  1. As batch 183 (report 183 §7): the batch-182 witnesses with E2.4 replaced by `E24Data`; no short
     refutation. The new results (saturation, the case split) are inputs these claims assumed, now
     proved, so they remove rather than create conflicts.
  2. Each describes a configuration at one step `i ≥ 3`; the conclusion `Hagopian76Thm1` is not a
     field, and the step is a proof by contradiction (Property 4 of `J` refuted).
* **`Hagopian84Lemma7`**: proved (`hagopian84Lemma7_holds`); no longer a hypothesis anywhere.
* **`InnerComponentsCross`, `BlockLayersMeetSides3`**: no longer hypotheses of Theorem 1 (proved for
  every set-up, resp. every tight block sequence).

## 8. Ledger entries

`LEDGER.md` §6, new subsection "Hagopian 1976 XXX … (batch 185)", three checks, printed sentences
quoted:
1. p. 347, the collection `I` and the end layer of `F` (A.23 of the commissioner's ledger, open
   since batch 178): **closed** by Lemma 7 of 1984 through §4.2. No sentence of the 1976 text is
   replaced (the step is not printed); the repository's chunk argument of batches 179–183 is no longer
   needed.
2. p. 348, "The proof now breaks down into two cases": the presupposition is **true for `i ≥ 3`**
   (`blockLayersMeetSides3`) and false at `i = 2` (`blockLayersMeetSides_false`); `d⁻¹(x₃)` located.
3. p. 348, "between": **open**; runs proved, §3.3 open.

`LEDGER.md`, Hagopian 1984 section, new subsection "Hagopian 1984 II … (batch 185)":
* H84.15, Lemma 7 (pp. 336–337), "By Lemma 4, there is a continuum `H`…" and "it follows from (2)
  that `k⁻¹(r) ⊂ F`…": Lemma true; the two-sided `H` needs `F₁ ∩ F₂ = E` and a glued decomposition,
  not stated (both proved); the printed proof's gaps (H84.4) avoided by another route.
* H84.16, rigidity and its degenerate case: true; one degenerate case, not arising in §4.

No statement of Hagopian's is refuted; the count of defective proofs stays at fourteen.

## 9. Axioms

Every theorem of the group *Hagopian 1976 XXX (batch 185)* of `Axioms.lean` (62 declarations) uses
exactly `propext`, `Classical.choice`, `Quot.sound`. The output is in
`doc/batches/audits/axioms-batch185.txt`.

| File | Theorems |
| --- | --- |
| `H84TwoSided.lean` | `mem_layerSet_iff'`, `mem_layer_iff'`, `layer_subset'`, `layerSet_subset'`, `layerSet_Icc_inter_subset`, `layerSet_Icc_zero_one`, `eq_of_meets_end_layers`, `layerGlueFun_mem`, `layerGlueFun_of_memA`, `layerGlueFun_of_memB`, `layerGlueA_injective`, `layerGlueB_injective`, `layer_glue_A`, `layer_glue_B`, `layerGlue_cases`, `layerGlueA_one`, `layerGlueB_one`, `interior_layer_of_subset_empty`, `glue_minimalAdmissible`, `ext_inter_ext_subset`, `disjoint_layerSet_layer`, `hagopian84_two_sided_aux` |
| `H84Lemma7.lean` | `no_arm_at_interior_layer`, `two_layers_or_subset`, `layer_common_of_essential`, `hagopian84_lemma7_aux` |
| `H84Rigid.lean` | `layers_agree_aux`, `translate_run_left_aux`, `translate_run_right_aux` |
| `H76Sat185.lean` | `Thm1Setup.fine_over_D`, `Thm1Setup.two_div_n_le`, `Thm1Setup.kminus_not_subset_O`, `Thm1Setup.kplus_not_subset_O`, `Thm1Setup.closure_crossSet_mem_E`, `Thm1Setup.F_ne_F10`, `Thm1Setup.isCrossingPiece_of_crossingComponent_G`, `Thm1Setup.crossing_of_halves`, `Thm1Setup.innerComponentsCross_aux` |
| `H76Split185.lean` | `layer_nhds_subset_open`, `left_layer_not_subset`, `right_layer_not_subset`, `Thm1Setup.isOpen_O`, `Thm1Setup.layerMeetsSide_of_end`, `Thm1Setup.IsBlocks.layer_disjoint_E`, `Thm1Setup.IsTightBlocks.left_end_crossing`, `Thm1Setup.IsTightBlocks.right_end_crossing`, `Thm1Setup.leftEndLayerMeetsSide`, `Thm1Setup.layer_x3_meets_side`, `Thm1Setup.blockLayersMeetSides3_aux` |
| `Hagopian76AC.lean` | `wset84_eq_wset`, `hagopian84_two_sided`, `hagopian84_lemma7`, `hagopian84Lemma7_holds`, `layers_agree`, `translate_run`, `translate_run_right`, `noncrossing_half_in_O_steps45`, `half_in_O_false`, `innerComponentsCross_hagopian`, `blockLayersMeetSides3`, `layer_x3_meets_side`, `hagopian76_theorem1_of_cases4` |

`axioms.txt`: 2261 lines (2197 + 64 added, none removed: 62 declarations, of which the output for
`Thm1Setup.isCrossingPiece_of_crossingComponent_G` is wrapped over three lines), `sorryAx` in none.

## 10. Dependency maps of Theorem 1

### 10.1 The 1976 route

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_cases4                       [proved, batch 185]
   └─ hagopian76_theorem1_of_cases3                    [proved]
      └─ hagopian76_theorem1_of_cases2                 [proved]
         ├─ hagopian76_theorem1_of_step_tight          [proved]
         ├─ hICC: innerComponentsCross_hagopian (2e)   [proved, batch 185]
         │  ├─ half_in_O_false                         [proved]
         │  │  ├─ tip_meets_end_layer(_mirror)         [proved, earlier]
         │  │  ├─ hagopian84_lemma7                    [proved]
         │  │  │  └─ hagopian84_two_sided              [proved]
         │  │  └─ T12Data.end_layer_not_subset         [proved, earlier]
         │  └─ noncrossing_half_in_O_steps45           [proved]
         ├─ stepStrands_of_frame (E0 + E1)             [proved]
         │  └─ StepFrame                               [OPEN]  (other orientations: open)
         └─ hagopian76_property4_step_cond2            [proved]
            ├─ i = 2: not_property4_x3x4               [proved]
            │  └─ LastStepClaims                       [OPEN]  (d⁻¹(x₃) located: layer_x3_meets_side)
            ├─ BlockLayersMeetSides3 (i ≥ 3)           [proved, batch 185: blockLayersMeetSides3]
            ├─ Case1ClaimsE24 → Case1Claims'           [proved: claims']
            │  ├─ first (E2.1)                         [open]
            │  ├─ between                              [open]  (runs proved; §3.3 open)
            │  ├─ far (E2.4) ← E24Data.far             [proved, from E24Claims (OPEN)]
            │  └─ band                                 [open]
            └─ Case2ClaimsE24 → Case2Claims'           [proved: claims']
               ├─ (a), (b), (e)                        [open]
               └─ (d) ← E24Data.far with π⁻¹(p₂)       [proved, from E24Claims]
```

### 10.2 The 1984 route (Jones's plan)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_jones                         [proved, batch 184]
   ├─ exists_plane_quotient_of_monotone                 [proved]
   ├─ indecomposable_of_monotone_image                  [proved]
   ├─ NoArcIndecHomPlane (Bing 1960 / Jones 1975)       [OPEN, named Prop]
   └─ Hagopian84Decomp (Theorem 1, N = M)               [OPEN, named Prop]
      ├─ Lemma 13 (chain 𝒫)                             [open]
      │  ├─ Lemmas 1, 3, 6                              [proved]
      │  └─ Lemma 12                                    [open]
      ├─ K(Z), X(Z), F(Z), J(Z), 𝒫(Z)                    [open]
      │  ├─ Lemma 11, N = M                             [proved]
      │  ├─ Lemma 7 (hagopian84_lemma7)                 [proved, batch 185]
      │  │  └─ two-sided extension                      [proved, batch 185]
      │  └─ Lemma 16                                    [open]
      ├─ cover 𝔅, disjointness of 𝔇 (Lemmas 3, 7)       [open; Lemma 7 now available]
      ├─ continuity of 𝔇 (Lemma 14)                     [open]
      ├─ homogeneity of M/𝔇 (Lemma 15)                  [open]
      └─ arc in M/𝔇                                     [open]
   (not needed with N = M: Lemma 10, claim (4), Lemma 8)
```

## 11. Skeleton proposal for what remains

```lean
/-- §3.3, in a usable form: the common segment of `F` and the strand's translate, from a crossing
component `C`, reaches a translate end outside `D` (S0 window) or the end layer `d⁻¹(1)`. -/
theorem crossing_component_run (S : Thm1Setup M) {C : Set M}
    (hC : IsCrossingComponent S.D.G S.π S.F S.c₁ S.D' C) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < S.θ / 4) (hCh : closure C ⊆ h '' S.E) :
    ∃ a b : unitInterval, a < b ∧ S.D.G ∩ h '' S.E = h '' layerSet S.k (Icc a b) ∧
      ((a : ℝ) < 2 / S.n ∨ h '' layer S.k a = layer S.D.d 1) ∧
      (1 - 2 / (S.n : ℝ) < b ∨ h '' layer S.k b = layer S.D.d 1) := by sorry

/-- §6: "between" from runs. -/
theorem case1_between_runs (S : Thm1Setup M) {x : ℕ → unitInterval} {m : ℕ}
    (hx : S.IsTightBlocks x m) : ∀ i, 3 ≤ i → i ≤ m → (Case1Between S x i) := by sorry

/-- `StepFrame` for the other orientations, and `E24Claims` (E2.4 steps 4–6): unchanged from
report 184 §11. -/

/-- 1984 route, next: Lemma 8 (now unblocked by Lemma 7), then Lemma 12 (atriodicity steps), 13. -/
theorem hagopian84_lemma8 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E F : Set M}
    {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) (hEF : (E ∩ F).Nonempty) :
    ∃ (c : (E ∪ F : Set M) → unitInterval), IsMinimalAdmissible (E ∪ F) c := by sorry
```
(`Case1Between` is a placeholder name for the "between" field of `Case1Claims'`; the shapes are
proposals, not checked.)

## 12. Files

New: `HPC/Hagopian/Hagopian76AC.lean`, `HPC/Hagopian/H84TwoSided.lean`, `HPC/Hagopian/H84Lemma7.lean`,
`HPC/Hagopian/H84Rigid.lean`, `HPC/Hagopian/H76Sat185.lean`, `HPC/Hagopian/H76Split185.lean`,
`doc/batches/REPORT-batch185.md`, `doc/batches/audits/axioms-batch185.txt`,
`doc/batches/batch185-MANIFEST.txt`. Moved: `doc/batches/COMMISSION-batch185.md`,
`doc/batches/skeletons/Hagopian76AC.lean`. Changed: `HPC.lean`, `Axioms.lean`, `axioms.txt`,
`README.md`, `LEDGER.md`, `OPEN.md`, `doc/notes/hagopian76-cases.md`, `doc/notes/hagopian84.md`,
`HPC/Hagopian/Hagopian76AB.lean`, `HPC/Hagopian/Hagopian84A.lean` (pointers only). Delivery:
`doc/batches/batch185-files.tar.gz` (every file above except the tarball itself).
