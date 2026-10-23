Commission read: `doc/batches/COMMISSION-batch183.md` ("Commission: batch 183 — Part E, Hagopian 1976 XXVIII: Theorem 1 — Bing's reasons for Cases 1–2; E2.4; the orientation; saturation").

# Report, batch 183

## 0. Summary, omissions

All new declarations compile without `sorry` and use only `propext`, `Classical.choice`,
`Quot.sound` (§8). `axioms.txt` has 2180 lines (2160 + 20 added, none removed); `sorryAx` occurs in
none.

```
STATUS: §1 Bing pp. 224–228 read from 200 dpi page images; dictionary confirmed; routes recorded
STATUS: §2 steps 1–2 (the pair a, b) proved: e24_pair_between, e24_pair_below
STATUS: §2 step 3 minimalAdmissible_restrict proved (layers kept; LSC from Lemma 5)
STATUS: §2 steps 4–6 named (E24Claims, Thm1Setup.FarFrom); open (far layer, essential, T17 sentence)
STATUS: §2 property2_violation proved, conditional on steps 4–6
STATUS: §2 assembly E24Data.far, hagopian76_theorem1_of_cases3 proved, conditional
STATUS: §2.2 printed form (all of d⁻¹[I]) not decided; the argument reaches only the adjacent strand
STATUS: §3 "between" open (outer component may pass around a strand end)
STATUS: §4 (a) open (as §3); (b), (e) open (no parity argument for the continuum P)
STATUS: §4.3 E-side route of Γ: not a gap in Bing (crossing parity); open for continua
STATUS: §4.4 (d) reduced (E24Data with π⁻¹(p₂), Case2WitnessE24)
STATUS: §5 proposal fails as stated (f(yᵢ) need not lie in Mid; essentiality not transferred)
STATUS: §6.1 E2.1 items 1–3, 5 open (as batch 182)
STATUS: §6.2 saturation open (as batch 182)
STATUS: §6.3 split by Γ stated; exhaustiveness open
```

**Omissions (§0 rule).**
* `case1_between_bing`, `case2_bing_a`, `case2_curve`, `case2_gap_side`, `property4_symm`,
  `exists_first_crossing`, `half_components_cross`, `chunk_points`, `gap_side_split`,
  `innerComponentsCross_hagopian`, `hagopian76_theorem1_final` of the skeleton: open; commented out at
  the end of `HPC/Hagopian/Hagopian76AB.lean` with their obstructions (§3–§6 below, `OPEN.md`).
* No commented-out statement of the earlier `Hagopian76*.lean` files is proved here, so none was
  replaced by a pointer (those files are unchanged).
* The commission's §2 step 4 invites adding a bound on `ε₂` to the set-up. None was added: the far
  layer is a hypothesis (part of `E24Claims`), so no bound is used.

**Shape changes** (recorded at each statement).
* The skeleton's `property2_violation : True` is stated as a theorem about a minimal admissible
  `(L, d)`, two layers `d⁻¹(s) ∋ a`, `d⁻¹(t) ∋ b` with `ρ(a, b) < ε₃`, and the three claims of steps
  4–6 as hypotheses. The far layer may be measured from either end set (the reversed case uses
  `unitInterval.symm ∘ e`).
* `minimalAdmissible_restrict` (batch-182 proposal: "∃ some `e`") records the layers:
  `layer e t = layer d (restrictParam a b _ t)`. The general form `minimalAdmissible_restrict_of_lsc`
  carries lower semicontinuity as a hypothesis (§2.3).
* The second configuration of §2 (`e24_pair_below`, `e24_below_far`) is stated for the adjacent
  `I`-strand `S_I`, as the commission asked.
* Case 2 (d) uses `π⁻¹(p₂)` (`r = 7/22`), after Bing's `a₂`; `FarFrom` is stated for any `r ∈ [0, 1]`.

## 1. Bing 1960 as the model

Bing 1960 journal pp. 224–228 (PDF pages 16–20) were read from page images at 200 dpi. The
dictionary of commission §1 agrees with the pages; it is recorded with the routes in
`doc/notes/hagopian76-cases.md`, E5. The commission's transcriptions agree with the pages. One small
inconsistency is Bing's own (p. 227): he supposes "`ρ(q, x₂ᵢ₋₁x₂ᵢ) ≥ ε₄`" and then writes "It is not
above `x₂ᵢ₋₁x₂ᵢ` because `ρ(q, x₂ᵢ₋₁x₂ᵢ) > ε₄` and `ρ(q, h(q)) < ε₄`"; the weak inequality suffices.
Bing's `M′` has every proper subcontinuum an arc, and `x₁x₂…x₂ₙ` is an arc in `A`. His strands are
arcs ending on the side lines at the points where the gap arc starts. Most of the differences below
come from this.

## 2. E2.4 by Bing's arc `ab` (`HPC/Hagopian/H76E24.lean`, `H76Restrict.lean`)

**Steps 1–2: proved.**
* `Thm1Setup.cap_point_o` is the cap lemma returning the point: `a ∈ Mid` down from a crossing piece
  `W`, `b` up from it, `ρ(a, b) < ε₃`. Then `[a, b]` meets `Cl W` at a point within `ε₃` of `a`.
* `Thm1Setup.near_strand_cross_o`: the same with `b` replaced by a set `X` up from `W` with
  `ρ(a, Cl X) < ε₃`.
* `e24_pair_between` covers Bing's "`q` above `tu`". `yᵢ` is a good point down from `S_I` with `f(yᵢ)`
  up from it, and `Cᵢ₋₁` lies between. Then some `b ∈ Cl Cᵢ₋₁` has `ρ(yᵢ, b) < ε₃`, via
  `cross_strand_near_o` and the cap.
* `e24_pair_below` covers Bing's second case. `yᵢ₋₁ ∈ Mid` is down from `Cᵢ`, `S_I` is up from `Cᵢ`,
  and `ρ(yᵢ₋₁, Cl S_I) < ε₃`. Then some `a ∈ Cl Cᵢ` has `ρ(yᵢ₋₁, a) < ε₃`.
* **The printed form (`d⁻¹[I]`).** For an `I`-strand below `Cᵢ`, the segment from `yᵢ₋₁` to it need
  not meet `Cl Cᵢ`, so this argument does not reach the printed claim. It is not refuted either: not
  decided.

**Step 3: proved.**
* `minimalAdmissible_restrict_of_lsc`: in a metric space, let `d` be minimal admissible on `G` with a
  lower semicontinuous decomposition, and let `a < b`. Then `d⁻¹[[a, b]]` with `(d − a)/(b − a)` is
  minimal admissible, and its layers are `d⁻¹(a + t(b − a))`.
* `minimalAdmissible_restrict`: in Hagopian's `M` the hypothesis comes from Lemma 5
  (`lsc_of_minimalAdmissible`).
* **§2.3, why the hypothesis.** The batch-182 proposal (∃ some `e`) is not refuted. The layer-keeping
  version needs lower semicontinuity in general. Informal example, not formalized: two `sin(1/x)`
  curves approach a common limit bar from the two sides, the right one only to the upper half. Cut at
  the bar, and the lower half of the bar is open in `d⁻¹[[a, 1]]`. That set is of type A′, but only
  under another decomposition, whose first end set is a point.

**Steps 4–6: named.**
* `Thm1Setup.FarFrom r H` says `H` does not come within `ε₂` of `π⁻¹F(r, 0)`.
* `E24Claims S d y₀ B`: for every `b ∈ B ∩ L` within `ε₃` of `y₀`, there are layers `d⁻¹(s)` and
  `d⁻¹(t)` of `L` holding `y₀` and `b`, and `H = d⁻¹[[s, t]]` satisfies three claims:
  * `h⁻¹[H]` is essential to `R(E)`;
  * some layer of `H` is farther than `ε₂` from an end set;
  * `FarFrom r H` holds for some `r`.
* `Thm1Setup.exists_Rset_over` gives a point of `R(E)` over `F(r, 0)`.

**`property2_violation`: proved, conditional.** Given the three claims, `S.hP2` (Property 2 for `h`)
gives a point of `H` within `ε₂` of the point of `R(E)` over `F(r, 0)`. This contradicts `FarFrom`.

**Assembly: proved, conditional.**
* `E24Claims.false`, `e24_between_false` (the first configuration is impossible), `e24_below_far`
  (`ρ(yᵢ₋₁, Cl S_I) ≥ ε₃`).
* `E24Data` (structure: `L`, both crossing pieces in `L`, one of the two positions with its claims),
  and `E24Data.far`.
* `Case1WitnessE24` (`far` replaced by `E24Data`) and `Case2WitnessE24` (`claim_d` derived from
  `E24Data`), with `.toO`.
* `Case1ClaimsE24`, `Case2ClaimsE24`, and `hagopian76_theorem1_of_cases3`.

**Steps 4–6, obstructions.**
* *Far layer:* `H` runs from near `S_I`, around the end of a strand, and back. This needs the route of
  `L` outside `D` (§3).
* *Essential:* `H` must contain a piece of `Cl Cᵢ` that is essential to `h[R(E)]` (E2.1, open).
* *T17:* "Since `L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and `Cl Cᵢ`, the continuum `N` does not come within
  `ε₂` of `π⁻¹(p₄)`." `L` follows the components only inside `π⁻¹[D]`. Outside `D`, `L` may enter a
  pocket of the complement near `p₄` from the far side. Bing's "no point of the arc `pq` in `M` is
  within `ε₄` of this vertical part of `J`" is unargued too.

## 3. "Between" (Case 1): open

* Let `A = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]` and let `σ` be the part of the left side segment between the points where
  `Cl S_J` and `Cl S_I` meet it.
* At the exit point `u ∉ A`, the two sides of `σ` lie in different components of the complement of
  `A ∪ σ`. This is a parity/Jordan argument by unicoherence (`separatesPlane_union_of_inter_disconnected`),
  not formalized.
* `L ∩ F = ∅` (`extension_misses_G`), so `L` stays in the outer component until it meets `π⁻¹[D]`.
* **Obstruction:** that the outer component meets `π⁻¹[D]` only through `σ`.
  * Suppose `F ∩ B(j_L, δ) ⊆ Cl D` near an end `j_L` of a strand, so the strand only touches the side
    segment there.
  * Then the outer component passes around `j_L`, and the batch-180 configuration ("re-enters on the
    other side of a strand's end") is not excluded.
  * `Γ` closes the region only where it reaches the side segment between the strands. The case
    hypothesis ("`d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` meet the same side") places `Γ` at that side, but not
    between the strand ends.
* Bing's arcs end exactly at `x₂ᵢ`, `x₂ᵢ₊₁` on the side line, where the gap arc starts. That is what is
  missing for continua.

## 4. Case 2 by Bing's closed curve: open; (d) reduced

1. **(a)** As §3 at the right side segment; open for the same reason.
2. **(b), (e).**
   * In Bing, `J` is a simple closed curve that meets the vertical through `a₃` near `p` only in
     `x₂ᵢ₋₁x₂ᵢ`.
   * The side of `h(q)` follows from the parity of crossings, whatever route the gap arc takes. This
     was checked by hand on toy polygons with the gap arc over the top and underneath; not formalized.
   * For the continuum `P` there is no parity argument. The Janiszewski form
     (`sepIn_iff_separatesPts_union`) separates the two sides of `Q`, not the two sides of `S_I`.
3. **The open point (§4.3).**
   * Nothing proved excludes `Γ` passing outside `D` on the `E` side, around an end of `π[E]`.
   * In Bing's setting this does not break the argument, by the parity above. So it is not a gap in
     Bing, except that the gap arc might enter `K`, which Bing does not discuss.
   * For continua it is open.
4. **(d)** As §2 with `r = 7/22`: `Case2WitnessE24`, field `e24`; `claim_d` is derived in
   `Case2WitnessE24.toO`.

## 5. The two other orientations: the proposal fails as stated

* `f(yᵢ)` need not lie in `Mid`. E1's position clause gives abscissae in `(3/8, 5/8)` only, while
  `Mid` asks for `[1/2 − 2/n, 1/2 + 2/n]`.
* The cap from `f(yᵢ)` uses `hε₃S` and `hε₃O`, which are stated on `Mid`.
* *Possible repair, not carried out:* choose `ε₃` so that the `ε₃`-neighbours of `Mid` have abscissae
  within `4/n` of `1/2`, and state the two `ε₃` fields on that wider set.
* The closure of the component of `f(yᵢ)` being essential to `h₁[R(E)]` does not follow from `Cl Cᵢ`
  being essential to `h[R(E)]`. This would be needed for the step run with `f⁻¹`.
* The endgame checks were not reached.

## 6. Smaller items

1. **E2.1 items 1–3, 5:** open, as batch 182. The Property 3 argument is about crossing components of
   `F`.
2. **Saturation:** open, as batch 182.
   * Steps 4–5 of `noncrossing_half_in_O` need S0 and the margin `8/n`.
   * The points `zⱼ`, and the two edge cases.
3. **The split by `Γ`.**
   * Proposed: `Γ` meets the left side segment between `S_J` and `S_I`, or the right one, or both.
   * Conjectured exhaustive for `i ≥ 3`:
     * `Γ ∩ E = ∅`, so it misses the bottom edge;
     * `Γ` misses `I₂`;
     * `Γ` cannot join the strands inside the closed region between them without cutting `Cᵢ`, a
       crossing piece missing `F`.
   * Not formalized.

## 7. Non-vacuity notes

The two checks of commission 182: (1) not refuted by a short argument from the set-up; (2) not
equivalent to the conclusion it is used for, unless the printed argument is a proof by contradiction.

* **`Thm1Setup.FarFrom`** (hypothesis of `property2_violation`).
  1. Not refuted by a short argument: `H ⊆ L` with `L ∩ F = ∅`, and the points over `p₄` include
     points of `E`. It is Hagopian's T17 sentence for `H`.
  2. Not the conclusion: the conclusion of `property2_violation` is `False`, reached through
     Property 2, which is a field of `S`.
* **`E24Claims`** (hypothesis of `E24Claims.false`, `e24_between_false`, `e24_below_far`).
  1. It is stated for the specific point `y₀`, not for all pairs. The all-pairs version is probably
     false: `Cl Cᵢ` and `Cl Cᵢ₋₁` may come close near the right side, where `H` passes over `p₄`.
     No short refutation of the pointwise form is known.
  2. Under Property 2 (`S.hP2`), `E24Claims S d y₀ B` is equivalent to "no point of `B ∩ L` lies
     within `ε₃` of `y₀`". That makes it a proof by contradiction, which is the printed argument's
     form: "for otherwise, a subcontinuum of `L` would violate Property 2". Its three parts (essential,
     far layer, `FarFrom`) are each separate printed claims. With `B = Cl Cᵢ`, the conclusion of
     `e24_below_far` is strictly weaker (`ρ(yᵢ₋₁, Cl S_I) ≥ ε₃`), so the hypothesis is not the
     conclusion restated.
* **`E24Data`** (hypothesis of `E24Data.far`; field of the witnesses).
  1. Its fields are E2.1's `L` and `Cᵢ₋₁` (crossing pieces in `L`) and one of Bing's two positions.
     Bing's case analysis says one of them holds. No short refutation is known.
  2. The first position contradicts itself (`e24_between_false`); the second gives the bound. The
     conclusion `ρ(yᵢ₋₁, Cl S_I) ≥ ε₃` is not a field.
* **`Case1WitnessE24`, `Case2WitnessE24`, `Case1ClaimsE24`, `Case2ClaimsE24`** (hypothesis of
  `hagopian76_theorem1_of_cases3`).
  1. They are the batch-182 witnesses with `far` (or `claim_d`) replaced by `E24Data`, which is
     weaker as the batch-182 field follows (`.toO`). The batch-182 checks apply unchanged.
  2. The conclusion is `Hagopian76Thm1`, not a hypothesis.
* **`StepFrame`, `LastStepClaims`, `BlockLayersMeetSides3`, `InnerComponentsCross`:** unchanged from
  batch 182; the notes of `doc/batches/REPORT-batch182.md` apply.

## 8. Ledger entries

`LEDGER.md` §6, subsection "Hagopian 1976 XXVIII … (batch 183)", six checks, with the sentences of
Hagopian and of Bing quoted:
1. pp. 348–349 against Bing pp. 225–227: Bing is the model. The arc `ab`, the subarc, and in part the
   side separation carry over. The strand ends on the side lines and the parity argument do not.
2. p. 348, E2.4: the subcontinuum is Bing's `ab`. Steps 1–3 closed; steps 4–6 named.
3. p. 348, "`N` does not come within `ε₂` of `π⁻¹(p₄)`", with Bing's "no point of the arc `pq` …":
   unargued in both; open.
4. p. 348, "between": open; Bing's reason carries over in part.
5. p. 349, Case 2 (a), (b), (e): open. (d) reduced, with `p₂` (Bing's `a₂`).
6. p. 348, "(Other cases …)": Bing's disc against Hagopian's arc; the proposal fails as stated.

No statement of Hagopian's is refuted; the count of defective proofs stays at fourteen.

## 9. Axioms

Every theorem of the group *Hagopian 1976 XXVIII (batch 183)* of `Axioms.lean` (20 declarations)
uses exactly `propext`, `Classical.choice`, `Quot.sound`. The output is in
`doc/batches/audits/axioms-batch183.txt`.

| File | Theorems |
| --- | --- |
| `H76Restrict.lean` | `restrictParam_mem`, `restrictParam_zero`, `restrictParam_one`, `minimalAdmissible_restrict_of_lsc`, `minimalAdmissible_restrict` |
| `H76E24.lean` | `Thm1Setup.cap_point_o`, `Thm1Setup.near_strand_cross_o`, `Thm1Setup.piece_nonempty`, `e24_pair_between`, `e24_pair_below`, `Thm1Setup.exists_Rset_over`, `exists_restrictParam_eq`, `property2_violation`, `E24Claims.false`, `e24_between_false`, `e24_below_far` |
| `Hagopian76AB.lean` | `E24Data.far`, `Case1ClaimsE24.claims'`, `Case2ClaimsE24.claims'`, `hagopian76_theorem1_of_cases3` |

`axioms.txt`: 2180 lines (2160 + 20 added, none removed), `sorryAx` in none.

## 10. Dependency map of Theorem 1 (updated)

```
Hagopian76Thm1
└─ hagopian76_theorem1_of_cases3                       [proved]
   └─ hagopian76_theorem1_of_cases2                    [proved]
      ├─ hagopian76_theorem1_of_step_tight             [proved]
      ├─ hICC: InnerComponentsCross (2e)               [OPEN]
      │  └─ §3.1 steps 4–5; zⱼ, (iii); τ₁ = 1          [open]
      ├─ stepStrands_of_frame (E0 + E1)                [proved]
      │  └─ StepFrame                                  [OPEN]  (other orientations: §5, open)
      └─ hagopian76_property4_step_cond2               [proved]
         ├─ i = 2: not_property4_x3x4                  [proved]
         │  └─ LastStepClaims                          [OPEN]
         ├─ BlockLayersMeetSides3 (i ≥ 3)              [OPEN]  (replacement split by Γ: §6.3)
         ├─ Case1ClaimsE24 → Case1Claims'              [proved: claims']
         │  ├─ first (E2.1)                            [open]
         │  ├─ between (§3)                            [open]
         │  ├─ far (E2.4) ← E24Data.far                [proved]
         │  │  ├─ e24_pair_between, e24_pair_below     [proved]
         │  │  ├─ minimalAdmissible_restrict           [proved]
         │  │  ├─ property2_violation                  [proved]
         │  │  └─ E24Claims (essential, far layer, FarFrom)  [OPEN]
         │  └─ band                                    [open]
         └─ Case2ClaimsE24 → Case2Claims'              [proved: claims']
            ├─ (a) (§4.1)                              [open]
            ├─ (b), (e) (§4.2)                         [open]
            └─ (d) ← E24Data.far with π⁻¹(p₂)          [proved, from E24Claims]
```

## 11. Skeleton proposal for what remains

```lean
/-- §3: the strands reach the side segment at their ends: near each end point of `Cl S` on the side
segment there are points of `F` outside `D` (or the configuration of §3). -/
theorem strand_end_outside (S : Thm1Setup M) {u v : unitInterval} {SI : Set Pt}
    (hSI : S.IsBlockStrand u v SI) : … := by sorry

/-- §3: with the above, an extension leaving `Cl Cᵢ` through `σ` re-enters `π⁻¹[D]` through `σ`. -/
theorem reenter_between (S : Thm1Setup M) … : … := by sorry

/-- §2 step 6: `H ⊆ L` does not come within `ε₂` of `π⁻¹(p₄)` when `L` meets `π⁻¹[D]` only in
crossing pieces between `S_J` and `S_I`. -/
theorem farFrom_of_between (S : Thm1Setup M) … : S.FarFrom (15 / 22) H := by sorry

/-- §5: the `ε₃` fields on the `4/n`-neighbourhood of `1/2` (the wider `Mid`). -/
theorem exists_eps_mid_wide … := by sorry

/-- §6.3: the split by `Γ` is exhaustive for `i ≥ 3`. -/
theorem gap_side_split (S : Thm1Setup M) … : GammaLeft S x i ∨ GammaRight S x i := by sorry
```

## 12. Delivery

* `doc/batches/batch183-MANIFEST.txt` lists `git diff --name-status` against the run's initial commit
  (`92a5288`), plus any uncommitted change, plus the manifest itself.
* `doc/batches/batch183-files.tar.gz` holds every file of the manifest at its final content. The two
  uploads, moved from the root, are at their new places in `doc/batches/` and
  `doc/batches/skeletons/`. It also holds `doc/batches/REPORT-batch182.md`, which this report names and
  this run did not change. The tarball does not contain itself.
