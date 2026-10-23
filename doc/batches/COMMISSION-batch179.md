# Commission: batch 179 — Part E, Hagopian 1976 XXIV: Theorem 1 — the end layer of `F`; `SepByCrossing` without conditions; uniform heights; the assembly; the step

**Go!** This batch runs on top of the batch-178 work. Two files come with it, as separate uploads:

* `COMMISSION-batch179.md`: this text, also pasted into the prompt.
* `Hagopian76X.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76X.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76X` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXIV (batch 179)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers;
  * the batch-178 files, where §3 and §4 ask for a restatement.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 178

Audited and accepted. All of it.
* **Delivery.** The project download for batch 178 did not contain the committed work. Two downloads
  held only the old tree and the files you had published. The work arrived through the published
  `doc/batches/batch178-files.tar.gz`, which I overlaid on the batch-177 tree. Thank you for the
  manifest. The remedy for the future is in §9.4.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2000 lines (1929 + 71 added, none removed), with `sorryAx` in none.
  All 71 new declarations use only the standard three axioms (`axioms-batch178.txt`).

**Accepted:**
* the frame `VFrame` and `lowFrame`, and `IsCrossingPiece`;
* the reading of "below `m(X)`" as "below every height of `Cl X`";
* the choice of closest points in SSL, and `Z` arbitrary;
* the companion `exists_T12Data_comp` in place of new `T12Data` fields;
* the Urysohn function in the unicoherence proof;
* the decisions in the cases note: (α) `Q` is the segment that `Cᵢ` meets first from the left, and
  `V` serves the local-to-global step; (β) "between" means between adjacent strands in the order.

**The two "problems with the commission" are settled by theorems already proved.** My commission
should have cited both.
1. **Nondegeneracy of `I`** (report §1.6). This is Property 3 as printed:
   `hagopian76_property3_components` (batch 174) says no crossing component lies in a layer
   `d⁻¹(v)`, `v ∈ [0, 1]`. A member `[u, u]` of `I` would be the irreducible interval of a crossing
   component `C ⊆ layerSet d (Icc u u) = layer d u`. So every member `[x, y]` has `x < y`. It needs
   `c₁ ≤` Property 3's height; see §4.
2. **4.B, "`I₂ ∩ π[M] = ∅` is not available"** (report §1.4). `hagopian76_T7` concludes
   `Disjoint I₂ (π '' M)`. Add this hypothesis to the set-up wherever `I₂` enters. It holds for
   Hagopian's `I₂` by T7.

## 1. The interval in `InnerComponentsCross`

`sep_by_crossing` needs `InnerComponentsCross` only on an interval `(lo, hi)` containing the
abscissa `x₀` of the vertical. Prove it for `(lo, hi) = (3/22 + 3/n, 19/22 − 3/n)`, the inner
middle, where S1 applies: points there are `h(e)` with `k(e)` in the core range. Take `x₀ = 1/2`.
The open shape in `Hagopian76W.lean` uses `(3/22 + 2/n, 19/22 − 2/n)`; narrow it, or justify the
wider interval.

## 2. Saturation: `InnerComponentsCross`

Report 178 §1.3b finds that steps 1, 2, 3.1 and 3.2 are sound, and that configuration 3.3 survives
the three named tools. Here is a route that closes 3.3. It needs only one more tool, the
finiteness of the crossing components.

Notation as in commission 178 §3b:
* `y` is over the inner middle, with `y = h(e)` (S1), and `W` is the component of `F ∩ O` through
  `y`;
* `K⁻ := F ∩ h[k⁻¹[[0, k(e)]]]` and `K⁺ := F ∩ h[k⁻¹[[k(e), 1]]]`;
* `W` is non-crossing, so by step 2 one half lies in `O`; say `K⁻ ⊆ O`;
* `τ` is the least parameter of `K⁻`, and the tip layer is `h[k⁻¹(τ)]`;
* `Λ₁ := d⁻¹(1) ∩ h[E]`.

**2a. The tip triod (a lemma).** Assume `K⁻ ⊆ O`, with tip `τ`, and:
* (i) some point of `K⁻` lies off `d⁻¹(1)` and off the tip layer `h[k⁻¹(τ)]`;
* (iii) `d⁻¹(1) ⊄ h[E]`.

Then `T := d⁻¹(1) ∪ K⁻ ∪ h[k⁻¹[[τ − δ, τ]]]` (for small `δ > 0`) is a triod over
`Z := Λ₁ ∪ h[k⁻¹(τ)]`. The three mutually separated nonempty parts of `T − Z` are:
* `K⁻ − Z`. It lies in `F − d⁻¹(1)`, because `K⁻ ∩ d⁻¹(1) ⊆ Λ₁ ⊆ Z`.
* `h[k⁻¹([τ − δ, τ))]`. It misses `F`, by the choice of `τ`.
* `d⁻¹(1) − h[E]`.

So the lemma contradicts atriodicity. Note that the relation between `τ₁` and `k(e)` (step 3.2
versus 3.3) plays no role: hypothesis (i) is what matters. State the mirror form for `K⁺ ⊆ O`.

**2b. A point on its own tip layer.** Suppose `K⁻ ⊆ h[k⁻¹(τ)]` (that is, `k(e) = τ`), and that
(iii) holds. Use instead `K⁺_δ := F ∩ h[k⁻¹[[τ, τ + δ]]]` (a continuum, by hereditary
unicoherence) and the triod `T := d⁻¹(1) ∪ h[k⁻¹[[τ − δ, τ]]] ∪ K⁺_δ` over `Z := h[k⁻¹(τ)] ∪ Λ₁`.
Its arms are:
* `d⁻¹(1) − h[E]`;
* `h[k⁻¹([τ − δ, τ))]`;
* `K⁺_δ − h[k⁻¹(τ)] − d⁻¹(1)`.

The last arm is nonempty. If `F ∩ h[E]` lay in the tip layer, then `W` would be a compact subset
of `O`, which is impossible by boundary bumping in `F`. If instead `F ∩ h[k⁻¹((τ, τ + δ])] ⊆ d⁻¹(1)`
for every `δ`, go to 2d with a chunk to the right of `y`.

**2c. Degenerate chunk.** If `Λ₁` lies in one translated layer of the core, then `Λ₁ ⊆ O`. Hence
`d⁻¹(1) ⊄ h[E]` by 3a (`T12Data.end_layer_not_subset`). This is (iii), and 2a or 2b applies.

**2d. Nondegenerate chunk (configuration 3.3): void interior and finiteness.** Suppose `Λ₁`
contains `h[k⁻¹((s, t))]` with `s < t`, and that this chunk meets `W` over the inner middle (this
holds in 3.3).
1. Choose `c ∈ W ∩ h[k⁻¹(t_c)]` with `s < t_c < t`, over the inner middle.
2. **Local structure.** There is a neighbourhood `U` of `c` in `M` with
   `U ∩ h[E] ⊆ h[k⁻¹((t_c − η, t_c + η))] ⊆ d⁻¹(1)`, since `h⁻¹` is continuous and so is `k`. Take
   `U ⊆ O`, over the inner middle.
3. **Void interior.** `d⁻¹(1)` has empty interior in `F` (`IsMinimalAdmissible`). So there are
   `zⱼ ∈ F ∩ U` with `zⱼ → c` and `d(zⱼ) < 1`. By step 2, `zⱼ ∉ h[E]`.
4. **Finitely many crossing components.**
   * `crossingIntervals_disjoint` and `IsCrossingComponent.eq_of_mem_closure`: a member of `I`
     determines its component. With `hagopian76_I_finite`, there are finitely many crossing
     components.
   * Each is closed in `O`, and none contains `c` (which lies in the non-crossing `W`).
   * So for large `j`, the component `Wⱼ` of `zⱼ` is non-crossing.
5. **The triod at `zⱼ`.** Write `zⱼ = hⱼ(eⱼ)` (S1).
   * `zⱼ ∉ h[E] ⊇ S`, where `S` is the strand of `y` and `c`. So the strand `Sⱼ` of `zⱼ` differs
     from `S`.
   * `hⱼ[E]` meets `O` over the inner middle only inside `Sⱼ`: points there have core parameters,
     and core translated layers lie in the strand. So `c ∉ hⱼ[E]`, and `c ∈ d⁻¹(1)`. This is (iii)
     for `zⱼ`.
   * `zⱼ` itself gives (i), since `d(zⱼ) < 1`. Then 2a for `zⱼ` gives a triod. Contradiction.
   * **Edge case.** `zⱼ` may lie on its own tip layer. Then use 2b. If 2b's third arm is empty
     there, the strand `Sⱼ` carries its own chunk of `d⁻¹(1)` next to `zⱼ`. In that case show that
     the `zⱼ` can be chosen off their tip layers: the set `(F ∩ U) − d⁻¹(1)` is relatively open in
     `F` and nonempty, and the tip layers are single translated layers. Or report the
     configuration exactly.

**2e. Conclusion.** Every component of `F ∩ O` through a point over the inner middle is crossing.
This is `InnerComponentsCross` for Hagopian's `F`, in the shape of report 178. If an edge case
resists, describe it exactly and keep `InnerComponentsCross` as a named hypothesis.

## 3. `SepByCrossing`, `x₂ₙ = 1`, the top block and the blocks, without conditions

1. **3c** (`block_components_cross`): every component of `d⁻¹[B] ∩ O` meeting the inner middle is a
   crossing component of `F ∩ O`. Gap layers and the end layers of blocks miss the inner middle of
   `O`. Route: commission 178 §3c, with `lemma3_half` both ways along a crossing component.
2. **4.B** (`p_on_crossing_piece`):
   * a component of `M ∩ O` is closed in `O`;
   * with `Disjoint I₂ (π '' M)` (T7) the closures of the strands of `p` and `f(p)` miss
     `π⁻¹[I₂]`;
   * 4.A gives the bottom edge;
   * "equal or disjoint" holds because these are components.
3. **`SepByCrossing` for `(F, p, f(p))`** from `sep_by_crossing` (batch 178), 2e and 4.B. Then:
   * `x₂ₙ = 1` (`hagopian76_x2n_eq_one`);
   * Property 4 for the top block (`hagopian76_property4_top`).
4. **The blocks** (`exists_blocks`, batch 178) with the nondegeneracy hypothesis discharged by
   `hagopian76_property3_components` (§0.1).
5. Feed all of it to `hagopian76_T15_T17_cond2`, so that `Property4Step` is its only remaining
   hypothesis besides the set-up.

## 4. Uniform heights

The heights `c` of these theorems are introduced after `G`: their statements read
`∀ G d, … → ∃ c > 0, …`. They are:
* `hagopian76_property3`, `hagopian76_property3_domain`, `hagopian76_property3_components`;
* `hagopian76_I_finite`;
* `component_over_middle_aux`, `cover_pocket_middle_aux`;
* `hagopian76_x2n_eq_one`;
* the descent lemmas behind them (`crossing_descends_aux`, `property3_layer_aux`,
  `hagopian76_property3_translate`, `crossing_from_layer_translate_aux`).

In Hagopian's order, `D` (with its height `c₁`) comes **before** `F = G` (T13 builds `F` from `D`,
`p`, `f(p)`). So these statements, as they stand, cannot be used in the assembly: it would be
circular.

The constants appear to come from `hagopian76_property3_reduced`, link control and
`pi_thin_near_layer`, none of which uses `G` in substance. Check this, and restate each with the
height chosen before `G`: `∃ c > 0, c ≤ 1 ∧ ∀ G d, … → ∀ c₁ D', c₁ ≤ c → …`. Keep the old names as
corollaries.

If some height genuinely depends on `G`, say exactly which, and why. That would be a gap in the
order of Hagopian's constants, and the place to repair it is before T13.

## 5. The assembly: Theorem 1 from the step

As commission 178 §7 and report 178 §5.4. Write `Thm1Setup` and prove
`hagopian76_theorem1_of_step : (∀ S : Thm1Setup, Property4Step S.D S.x S.n) → Hagopian76Thm1`.
* With §2 and §3, `InnerComponentsCross` and nondegeneracy are not hypotheses.
* The heights of §4 enter `Thm1Setup` before `D`.
* `Thm1Setup` should carry everything the step will use:
  * Property 2 at `(ε₂, ε₃)` (`Property2At`);
  * the strand constants;
  * the composant data of `exists_T12Data_comp`;
  * `Disjoint I₂ (π '' M)`;
  * the blocks with their extra clauses;
  * `ε₂ ≤ ρ(M, π⁻¹[I₁ ∪ I₂])`.

This isolates the induction step as the only open input of Theorem 1.

## 6. The induction step

Hagopian pp. 348–349; commission 178 §8 and `doc/notes/hagopian76-cases.md`.
1. **E0 and E1** (`property4_step_unless`). These are now within reach: SSL and its converse, with
   3c and 4.B. Prove them.
2. **E2.1, the first strand.**
   * The shortest extension `L` of `Cl Cᵢ` away from `X` in `h[R(E)]` that contains a strand other
     than `Cᵢ`. For its existence, use a chain-intersection argument (`ExtChainInter`, batch 170)
     or Zorn's lemma.
   * `L ∩ F = ∅`, by 4.A.
   * `Cl Cᵢ₋₁` is essential to `h[R(E)]`.
   * The choice of `yᵢ₋₁ ∈ K ∩ Cᵢ₋₁`: `K` is the low vertical, and every strand meets it (S4a).
3. **E2.4.** Identify the subcontinuum `H ⊆ L` and its end sets in "for otherwise, a subcontinuum of
   `L` would violate Property 2". Prove `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃` from `Property2At`.
4. **The cap, Case 1.** With `Q` the segment of the low vertical over `15/22` that `Cᵢ` meets first
   from the left, prove that `P := d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q` separates `yᵢ` from `f(yᵢ)`. Use
   `separatesPlane_union_of_inter_disconnected` (`d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∩ Q` is the two ends of `Q`) and
   the order of strands. Two points need care:
   * where `L` re-enters `D` after leaving through `Z`;
   * the reading of "between" in (β).
5. **Local to global** (E2.5): Janiszewski with `A := d⁻¹[J] ∪ V ∪ Y` and
   `B := d⁻¹[I] ∪ Γ ∪ V ∪ Y`, then SSL in `O_L` (a second `VFrame`).
6. **Case 2.** Decide whether "`Cᵢ₋₁` is above `d⁻¹[I]`" can be proved from the minimality of `L`,
   `L ∩ F = ∅`, Property 2 and the order. If it cannot, give the configuration that blocks it.

For every step that stays open, give a named `Prop` and the configuration that blocks it. An honest
statement that the printed argument does not work, with the configuration, is as useful as a proof.

## 7. Order

1. §1 and §2, then §3.
2. §4, then §5.
3. §6: E0, E1, E2.1, E2.4 first; then the cap; then the rest.

## 8. Places to check (candidate ledger entries)

1. **The end layer of `F`** (§2): not in the text; it is needed for "`x₂ₙ = 1`" and the top block.
2. **p. 348**, "Note that `x₂ₙ = 1`": unconditional through §3.
3. **p. 347**, Property 3, used for the nondegeneracy of `I` (§0.1).
4. **The order of the constants** (§4): whether Property 3's and T15's heights can be fixed before
   `F`.
5. **pp. 348–349**, Cases 1–2: E0, E1, the cap, Case 2.

## 9. Deliverables

1. The items of §1–§6.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch179.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
4. **Publish the changes, as in batch 178.** The project download may again miss committed work.
   At the end of the run:
   * create `doc/batches/batch179-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch179-MANIFEST.txt`;
   * publish both, as you published the report.
5. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
