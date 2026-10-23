# Commission: batch 180 — Part E, Hagopian 1976 XXV: Theorem 1 — the set-up repaired; saturation; 3c; the step

**Go!** This batch runs on top of the batch-179 work. Two files come with it, as separate uploads:

* `COMMISSION-batch180.md`: this text, also pasted into the prompt.
* `Hagopian76Y.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76Y.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76Y` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXV (batch 180)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers;
  * `H76Thm1Setup.lean` and `H76Final179.lean` (batch 179), where §1 asks for a restatement.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 179

* **Delivery.** The project download was stale again. The work arrived through the published
  `doc/batches/batch179-files.tar.gz`, and the manifest from `git diff` against the initial commit
  is exactly what I needed. Thank you. Keep doing it (§7.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2032 lines (2000 + 32 added, none removed), with `sorryAx` in none.
  All 32 new declarations use only the standard three axioms (`axioms-batch179.txt`).

**Accepted:**
* the uniform heights, including the use of the proper extension `G′` at the same height in
  `property3_layer_all_unif`;
* `crossingIntervals_nondegenerate` and `crossing_components_finite`;
* 4.B (`p_on_crossing_piece`), and the choice of the package inside the statements that need it;
* `sep_by_crossing_uncond`, `hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`,
  `exists_blocks_uncond`, `hagopian76_T15_T17_cond3`;
* the restriction of the step hypothesis to block sequences;
* your two points on saturation. They are answered in §2.

**Not accepted: `Thm1Setup` as assembled.** See §1. `hagopian76_theorem1_of_step` is a correct
theorem, but its step hypothesis cannot be discharged by Hagopian's argument. Part of the fault is
mine: commission 179 §5 did not say what `K` must be.

## 1. The set-up (do this first)

### 1.1 The failure

`exists_thm1Setup` passes `K₀ = ∅` to `hagopian76_T15_T17_cond3`. So the package has `D.K = {D.p}`.

Now take a block sequence `x` and `2 ≤ i ≤ m`, and suppose Property 4 holds for
`J = [x₂ᵢ₋₃, x₂ᵢ₋₂]`. Then `yₙ = p`, and:
1. `d⁻¹[J]` separates `p` from `f(p)` in `π⁻¹[D]`;
2. so does `A := d⁻¹[[0, x₂ᵢ₋₂]] ⊇ d⁻¹[J]`, because `p, f(p) ∉ D.G` (`D.sep`), and separation
   by a set passes to any larger set that still misses both points;
3. `A` is an extension of `E` away from `k⁻¹(0)`. It contains `E = d⁻¹[[0, x₂]]`, and `piece_map`
   with `lsc_of_minimalAdmissible` gives its decomposition, as in
   `T12Data.end_layer_not_subset_aux`;
4. `A ≠ D.G`, since `x₂ᵢ₋₂ < x₂ₘ = 1` and `d⁻¹(1)` is nonempty;
5. this contradicts `D.irr`.

So for this set-up `Property4Step` at `i = m` holds only if Property 4 *fails* for the top block,
which is the opposite of what the endgame proves. The hypothesis `hstep` can then be met only by
showing that no set-up exists, which is Theorem 1 itself.

In Hagopian, `K` is the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` (p. 347). In the project it is
`K₀ = π⁻¹F[{t₀} × (0, w₂)]` (`hagopian76_K0`), and Case 1 chooses a new point `yᵢ₋₁ ∈ K` on a new
strand.

**Certificate.** Prove `property4_lower_false_of_K_eq` (skeleton): for a package with
`D.K = {D.p}`, Property 4 fails for every block below the top. If the argument above has a hole,
say where.

### 1.2 The repair: fields of `Thm1Setup`

Restate `Thm1Setup` in place (same name) with the following, and record each new field with the
step that uses it.
1. **`K`.** `hK : D.K = insert D.p K₀`, where `K₀` is the set of points of `M` over the open low
   vertical `F[{1/2} × (0, w₂)]`. In `exists_thm1Setup`, pass this set to the package lemma.
2. **The composant data.** The clauses of `exists_T12Data_comp`:
   * `∃ x₀ : E, (k x₀ : ℝ) = 1/2 ∧ D.p = D.h x₀ ∧ D.h x₀ ∉ composant x₀ ∧ D.h₁ x₀ ∉ composant x₀`;
   * `h` and `h₁` are `θ/4`-homeomorphisms. A field `ε₃ ≤ θ/2` gives this from `D.h_small`.

   `hagopian76_T15_T17_cond3` builds such a package but does not expose these clauses. Add a
   version (new name, e.g. `hagopian76_T15_T17_cond4`) whose package carries them.
3. **`ε₂` as printed** (p. 346: "Define `ε₂` to be the minimum of `ε₁` and
   `ρ(M, π⁻¹[I₁ ∪ I₂])`"):
   * a field `I₁`, Hagopian's interval below `⟨p₁, p₅⟩`, from `hagopian76_I1`: the side of the
     strip at height `−c′/2`;
   * `0 < ε₂`, `ε₂ ≤ ε₁`, and `ε₂ ≤ dist m z` for `m ∈ M`, `π z ∈ I₁ ∪ I₂` (`hagopian76_eps2_pos`).

   You may take `ε₂` smaller if a step needs it. Property 2 holds at every `ε₂ > 0`, and `ε₃` is
   chosen after `ε₂`. Example: E2.2 needs `N` to stay `ε₂` away from the vertical over `15/22`.
4. **`ε₃`.** Choose it by `eps3_positions_middle` at this `ε₂`, so that the set-up also carries:
   * the position clause: points of `M` within `ε₃` of a point over `1/2` lie over `(3/8, 5/8)`;
   * `ε₃ < ε₂`;
   * `ε₃ ≤ θ/2`.
5. **`n`.** Take `n = 40`, with a field `40 ≤ n`. §2.2 needs the saturation interval
   `(3/22 + 8/n, 19/22 − 8/n)` to contain `(3/8, 5/8)`, so `n ≥ 34`.
6. **A field audit.** Read `doc/notes/hagopian76-cases.md`, E2.1–E2.6. List, for each step, the
   facts about the set-up it uses. Add any that are missing. An example is the bound on `ε₃` in
   E2.5.2: the segment `[yᵢ₋₁, f(yᵢ₋₁)]` should stay in `π⁻¹[D]`.

### 1.3 Restatements

* `exists_thm1Setup` and `hagopian76_theorem1_of_step`: in place, with the repaired set-up. In
  `hICC`, use the interval of §2.2.
* **Positive check** (`Thm1Setup.K_meets_crossing`): every crossing piece inside `M` meets `D.K`.
  This is S4a with the new `K₀`, and it is what E2.1 uses to choose `yᵢ₋₁`.
* **Non-vacuity note.** For each hypothesis of `hagopian76_theorem1_of_step`, say in the report why
  the set-up does not refute it in the way of §1.1.

## 2. Saturation: `InnerComponentsCross`

Route: commission 179 §2 (2a–2e), with the two answers below. Target:
`innerComponentsCross_hagopian (S : Thm1Setup M)` on `(3/22 + 8/n, 19/22 − 8/n)`.

### 2.1 Your point on the triod: `Z` is a continuum

This is step 3.1 of commission 178 §3b: **`d⁻¹(1)` meets the tip layer.** State it as a lemma
(`tip_meets_end_layer`), for `K⁻ ⊆ O` with tip `τ`, in the form 2a and 2d.5 need. That is, for any
`θ/4`-homeomorphism `h` and any point `y = h(e)` over the inner middle (S1). Proof:
1. `τ > 3/22 − 2/n > 0`, by S0.
2. For small `δ`, `Q_δ := h[k⁻¹[[τ − δ, τ + δ]]]` is a continuum. It meets `F` at the tip layer. It
   misses `d⁻¹(0) = k⁻¹(0)`: by S0, a point of `Q_δ` in `k⁻¹(0)` would have parameter `< 2/n`,
   while every parameter of `Q_δ` exceeds `3/22 − 2/n − δ`. This needs `3/22 > 4/n + δ`, which
   fails for `n = 15` and holds for `n = 40`.
3. If `Q_δ` missed `d⁻¹(1)`, then no hair for `F` (`hagopian76_no_hair` with `D.hG`, as in
   `H76StrandUse.lean`) would give `Q_δ ⊆ F`. Then `F` would meet `h[k⁻¹(τ − δ/2)]`, a point of
   `K⁻` with parameter below `τ`.
4. So `Q_δ ∩ d⁻¹(1) ≠ ∅` for every small `δ`. By compactness, `d⁻¹(1)` meets `h[k⁻¹(τ)]`.

Consequences:
* `Λ₁ = d⁻¹(1) ∩ h[E]` is nonempty, and it is a continuum (`isContinuum_inter_of_HU`).
* `Λ₁` meets the tip layer, so `Z = Λ₁ ∪ h[k⁻¹(τ)]` is a continuum.
* `T` is connected: `d⁻¹(1)` meets `K⁻` at the tip layer.

So the triod of 2a stands as written (`IsTriod` asks for a continuum `Z`). Your alternative, the
core `h[k⁻¹(τ)]` alone with `Λ₁` in an arm, does not work in general. If `Λ₁` has parameters in
`(τ, k(e)]`, the arms `K⁻ − Z` and `d⁻¹(1) − Z` meet.

### 2.2 Your point on 2d.5: the margin

You are right: `c ∈ hⱼ[E]` gives `c ∈ Sⱼ` only if `c` lies over `(3/22 + 4/n, 19/22 − 4/n)`. Fix it
by narrowing saturation to points `y` over `(3/22 + 8/n, 19/22 − 8/n)`, and by choosing `c` near
`y`, as follows.
* In 2d, the chunk `h[k⁻¹((τ, τ₁))] ⊆ Λ₁` has `τ ≤ k(e) ≤ τ₁` and `τ < τ₁`.
* Choose `t_c` in the chunk's parameter interval with `|t_c − k(e)| < η < 1/n`, and `c` any point
  of `h[k⁻¹(t_c)]`.
* Then `|a(c) − a(y)| < 2/n + η + 1/n < 4/n`. The three terms are S0 for `c`, the choice of `t_c`,
  and S1 for `y`. So `a(c) ∈ (3/22 + 4/n, 19/22 − 4/n)`.
* `c ∈ W`:
  * if `t_c ≤ k(e)`, then `c ∈ K⁻ ⊆ W`, because `K⁻ ⊆ O` is a continuum through `y`;
  * if the chunk lies to the right (`τ = k(e)`, the case 2b sends to 2d), take `t_c > τ`. The
    continuum `Λ₁ ∩ h[k⁻¹[[τ, t_c]]]` contains `c` and meets `K⁻` at the tip layer. It lies in `O`
    for `t_c` close to `τ`, by compactness, since `Λ₁ ∩ h[k⁻¹(τ)] ⊆ K⁻ ⊆ O`.
* With `c = hⱼ(e′)`, S0 gives `k(e′) ∈ (3/22 + 2/n, 19/22 − 2/n)`. So `c ∈ Sⱼ` by the strand lemma.

The uses of saturation fit the narrower interval:
* `sep_by_crossing_uncond` needs only `t₀ = 1/2 ∈ (lo, hi)`;
* 3c and E2.5.2 need `(3/8, 5/8)`, since `eps3_positions_middle` puts the points of `M` near
  `[yᵢ₋₁, f(yᵢ₋₁)]` there. Hence `n ≥ 34` (§1.2.5).

If a still larger margin turns up, change `n`, not the route.

### 2.3 The rest of the route

As commission 179 §2:
* 2a with 2.1;
* 2b and its edge case;
* 2c (3a gives (iii));
* 2d with `crossing_components_finite` and 2.2;
* 2e.

`tip_meets_end_layer` applies verbatim at the nearby points `zⱼ` of 2d.5 (with `hⱼ`). If an edge
case resists, describe it exactly and keep `InnerComponentsCross` as a named hypothesis.

## 3. 3c, then E0 and E1

1. **3c** (`block_components_cross`): commission 179 §3.1. State it on the interval of §2.2.
2. **E0, E1** (`property4_step_unless`): commission 179 §6.1, in the frame `lowFrame`, with SSL and
   its converse, 4.B, 3c and the new `K`.

If 2e stays open, prove 3c and E0/E1 with `InnerComponentsCross` as a hypothesis, so that the step
does not wait for saturation.

## 4. The induction step

Hagopian pp. 348–349; commission 179 §6; `doc/notes/hagopian76-cases.md`. Target:
`hagopian76_property4_step (S : Thm1Setup M) x m (hx : S.IsBlocks x m) : Property4Step S.D x m`.
1. **E2.1, the first strand.**
   * `L` is the shortest extension of `Cl Cᵢ` away from `X` in `h[R(E)]` that contains a strand
     other than `Cᵢ`. For its existence, use `ExtChainInter` (batch 170) or Zorn's lemma.
   * `L ∩ F = ∅`, by 4.A with the composant data (§1.2.2).
   * `Cl Cᵢ₋₁` is essential to `h[R(E)]` (`strand_essential`).
   * `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁`, by `Thm1Setup.K_meets_crossing`.
2. **E2.4.** Identify `H ⊆ L` and its end sets in "for otherwise, a subcontinuum of `L` would
   violate Property 2". Prove `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃` from `Property2At` at the printed `ε₂`.
3. **The cap, Case 1.**
   * `Q` is the segment of the vertical over `15/22` that `Cᵢ` meets first from the left.
   * Prove that `P := d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q` separates `yᵢ` from `f(yᵢ)`. Use
     `separatesPlane_union_of_inter_disconnected` and the order of strands.
   * Two points need care: where `L` re-enters `D`, and the reading of "between" in (β).
4. **Local to global** (E2.5): Janiszewski with `A := d⁻¹[J] ∪ V ∪ Y` and
   `B := d⁻¹[I] ∪ Γ ∪ V ∪ Y`, then SSL in `O_L` (a second `VFrame`).
5. **Case 2.** Decide whether "`Cᵢ₋₁` is above `d⁻¹[I]`" follows from:
   * the minimality of `L`;
   * `L ∩ F = ∅`;
   * Property 2;
   * the order.

   If it does not, give the configuration that blocks it.

For every step that stays open, give a named `Prop` and the configuration that blocks it.

## 5. Order

1. §1: the certificate, the repaired set-up, the restatements, the positive check.
2. §2.1, then §2.2, then the rest of §2.
3. §3.
4. §4: E2.1 and E2.4 first, then the cap, then the rest.

## 6. Places to check (candidate ledger entries)

1. **p. 347, `K`** ("Let `K` be the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` …"): which properties of `K`
   the induction uses. The batch-179 set-up with `K = {p}` is a project error, not a defect of the
   text; record it as such, with the certificate of §1.1.
2. **p. 346, `ε₂`**: where Cases 1–2 use `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])` and `ε₂ ≤ ε₁`.
3. **The end layer of `F`** (§2): the two points of report 179 §1.2, now answered.
4. **pp. 348–349**, Cases 1–2: E0, E1, the cap, Case 2.

## 7. Deliverables

1. The items of §1–§4.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch180.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the fields of the repaired `Thm1Setup`, each with the step that uses it;
   * the non-vacuity notes (§1.3);
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
4. **Publish the changes, as in batch 179.** At the end of the run:
   * create `doc/batches/batch180-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch180-MANIFEST.txt`;
   * publish both, as you published the report.
5. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
