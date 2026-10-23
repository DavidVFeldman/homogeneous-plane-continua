Commission read: `doc/batches/COMMISSION-batch134.md` (batch 134 — the Effros theorem (van Mill's proof) and Ungar's corollary; Part C of the classification project).

# Report, batch 134

`lake build HPC` succeeds with `import HPC.Effros.Effros` added to `HPC.lean`. The four new files
`HPC/Effros/{Fat,OpenMapping,HomeoGroup,Effros}.lean` contain no `sorry`. `axioms.txt` is
regenerated: it has 717 lines, 25 of them new (the group "Effros theorem (batch 134)"), and
`sorryAx` occurs in no line. The per-batch audit `doc/batches/audits/axioms-batch134.{lean,txt}`
lists every theorem and instance of the four files, 52 entries:
* 46 show exactly `[propext, Classical.choice, Quot.sound]`;
* 5 show a proper subset of it;
* `mem_orbitPart` uses no axioms. The previous `axioms.txt` is saved as
`doc/batches/audits/axioms-before-batch134.txt`.

**Every item is proved.** Nothing is left open, so `OPEN.md` is unchanged. One refutation
candidate is confirmed: Proposition 2.2 fails without `Nonempty`. The other two do not fail.

Housekeeping:
* the commission is at `doc/batches/COMMISSION-batch134.md`;
* the skeleton is at `doc/batches/skeletons/Effros.lean`, verbatim;
* the paper is at `doc/sources/vanmill2004.pdf`. It is git-ignored like the other PDFs there.

Edited files:
* `HPC.lean` (one import);
* `Axioms.lean` and `axioms.txt` (new group);
* `README.md` (a Part C entry, the `HPC/Effros` row, the batch count 134, and the source);
* `LEDGER.md` (new §6, as deliverable 2 asks).

No other existing file is edited.

## Files

| file | content |
|---|---|
| `HPC/Effros/Fat.lean` | §A: `NowhereMeagre`, `IsFat`, Lemma 2.1, Proposition 2.2 (relative and skeleton forms), the nested construction |
| `HPC/Effros/OpenMapping.lean` | §B: the basis, `orbitPart`, Lemmas 3.1–3.4, Proposition 3.5, the open mapping principle |
| `HPC/Effros/HomeoGroup.lean` | §C: the homeomorphism group as a Polish topological group acting continuously, `supMove` |
| `HPC/Effros/Effros.lean` | §D: Ungar's corollary; the module docstring indexes the items and records the shape changes |

## A. Meager and fat sets

All proved: `NowhereMeagre`, `IsFat` (verbatim), `IsFat.mono`, `IsFat.diff_meagre` (Lemma 2.1),
`nonempty_interior_closure_of_not_meagre`, `inter_nonempty_of_isFat` (Proposition 2.2, the
skeleton's statement).

**Proposition 2.2, relative form.** `inter_nonempty_of_nowhereMeagre` assumes, in a metric space:
* `S` and `T` are analytic and nowhere meager (in the ambient space);
* `S` is nonempty;
* `S ⊆ closure T`.

Then `S ∩ T` is nonempty. The skeleton's statement is the special case where both sets are dense
in a nonempty space. The relative form is what Proposition 3.5 uses (see "refutation candidates").

The proof follows van Mill in three steps:
1. **Reduction** (`exists_reduced_param`). Write `S = range f` with `f : (ℕ → ℕ) → Y`, which is
   Mathlib's `AnalyticSet`. Remove the union `O` of the open sets whose image is meager. `f(O)` is
   meager, by second countability of `ℕ → ℕ` (Lindelöf). `C = Oᶜ` is closed, hence Polish. The image
   of every nonempty relatively open subset of `C` is not meager. Continuity of `f` is not needed
   for this step.
2. **Nested construction** (`CoreGood`, `coreGood_step`, `exists_eq_of_core`). This is in complete
   metric spaces `P` and `Q` (upgraded from Polish by `upgradeIsCompletelyMetrizable`). The
   invariant is `β(V) ⊆ W ∧ α(U) ⊆ closure β(V)`, which is the commission's reconstruction (3).
   Steps 1–5 are as in §3.1 of the commission, including its supplement `W ⊆ Wₙ`. The sequence comes
   from dependent choice (`exists_seq_of_step`), with radii `(1/2)ⁿ`.
3. **Conclusion.** `p` and `q` come from `Metric.nonempty_iInter_of_nonempty_biInter` applied to
   the closures. Then `dist (α p) (β q) ≤ diam (closure Wₙ₊₁) → 0`.

## B. The open mapping principle

Hypotheses as in the skeleton:
* `G` is a Polish topological group;
* `X` is a metric space;
* `ContinuousSMul G X`;
* the action is transitive, and `X` is a nonempty Baire space.

Separate continuity (Remark 5) was not pursued. All proved:
* `exists_vanMill_basis`: verbatim. It is built by dependent choice from an antitone basis. Each
  step takes `S` open with `S * S ⊆ Uₙ ∩ Bₙ` and symmetrizes it to `S ∩ S⁻¹`.
* `orbitPart`: verbatim.
* `vanMill_3_1`: the unused hypothesis `U 0 = univ` is dropped.
* `vanMill_3_2`: verbatim. It uses only `U ∈ 𝓝 1`, as the commission expected.
* `vanMill_3_3`: the unused hypothesis `U 0 = univ` is dropped.
* `vanMill_3_4`: the unused hypotheses `U 0 = univ` and "basis" are dropped.
* `vanMill_3_4_dense`: new. It is the first sentence of Lemma 3.4 as printed.
* `vanMill_3_5`: the unused hypothesis `U 0 = univ` is dropped.
* `effros_open_mapping`: verbatim.
* `isOpenMap_smul_left`: verbatim.
* `isOpen_orbitPart`: new. It is the remark after Corollary 3.6: `U • x` is open for open `U`.

`effros_open_mapping` is assembled from `x ∈ interior (closure (U (n+2) • x))` (3.4 at level
`n+1`) and `⊆ U (n+1) • x` (3.5 at level `n`).

## C. The homeomorphism group of a compact metric space

**What Mathlib provided.** It has no `Group (Y ≃ₜ Y)`, no `MulAction (Y ≃ₜ Y) Y` and no topology
on `Y ≃ₜ Y`; all three were checked with `#synth`. What it did provide:
* the compact-open topology on `C(Y, Y)`, and its metric for compact `Y`
  (`ContinuousMap.dist_eq_iSup`);
* `PolishSpace C(Y, Y)` for compact metric `Y`, found by instance search (complete and separable);
* continuity of composition (`ContinuousMap.continuous_comp'`) and of evaluation
  (`continuous_eval`), for locally compact `Y`;
* `IsClosedEmbedding.polishSpace`;
* `Homeomorph.smul`, and `IsInducing.isMeagre_image`.

**Construction** (the skeleton header's suggestion). All of the following are proved.
* **C.1.** `homeoGroup` is the group, with `(f * g) y = f (g y)`, `1 = refl` and `f⁻¹ = f.symm`;
  it is defined for any topological `Y`. `homeoTopology` is the topology induced by
  `homeoEmb h = (h, h⁻¹) ∈ C(Y, Y) × C(Y, Y)`. `homeo_isTopologicalGroup` holds for locally compact
  `Y`.
* **C.2.** `homeo_polishSpace`: `homeoEmb` is a closed embedding (`isClosedEmbedding_homeoEmb`),
  with range `{(f, g) | f ∘ g = id ∧ g ∘ f = id}` (`range_homeoEmb`).
* **C.3.** `homeoMulAction` is the action (by evaluation). `homeo_continuousSMul` holds. For the
  neighbourhoods:
  * `hasBasis_supMove`: the sets `{h | supMove h < r}` with `r > 0` form a basis of `𝓝 1`;
  * `supMove_ball_mem_nhds` follows.
* **`supMove`.** It is defined verbatim, as the `⨆`. As the commission asked, I checked that the
  `⨆` behaves as intended:
  * `bddAbove_move`: the range is bounded above (a continuous function on a compact space);
  * `dist_le_supMove`: the pointwise bound;
  * `supMove_eq_dist`: `supMove h` is the uniform distance from `id`.

  If `Y` is empty, `supMove = 0` (`Real.iSup` of the empty family). `supMove_symm` and
  `supMove_symm_trans_le` are proved verbatim. Also proved: `supMove_inv` and `supMove_mul_le`.

## D. Ungar's corollary

`effros_homogeneous` and `effros_homogeneous_set` are proved, verbatim. Transitivity of the action
comes from `hom`; an empty `Y` is a trivial case. The proof:
1. `N = {h | supMove h < ε/2} ∈ 𝓝 1`.
2. `orbitPart N z ∈ 𝓝 z` by `effros_open_mapping`.
3. **Lebesgue-number step:** `lebesgue_number_lemma_of_metric` on the cover by the interiors.
4. If `x = g z` and `y = h z`, then `h * g⁻¹` sends `x` to `y` and moves each point by at most
   `supMove h + supMove g⁻¹ < ε`.

`effros_homogeneous_set` applies this to the compact subtype `M`.

## Refutation candidates

* **`vanMill_3_2` needs only `U ∈ 𝓝 1`.** Confirmed: the statement is exactly that. The Lindelöf
  step uses second countability of `G`, which is automatic for a Polish group
  (`TopologicalSpace.isOpen_iUnion_countable`), and translates of `interior U`.
* **`inter_nonempty_of_isFat` needs `Nonempty Y`.** Confirmed: `isFat_empty_of_isEmpty`. In an empty
  space, `∅` is analytic and fat, and `∅ ∩ ∅ = ∅`.
* **Meager in `E` versus meager in `X` (in `vanMill_3_5`).** No failure, and the issue does not
  arise in the formalization. Proposition 2.2 is used in the relative form, inside `X`, with:
  * `S = U (n+1) • x ∩ E` and `T = U (n+1) • z ∩ E`;
  * nowhere meager in `X`, from Corollary 3.3 applied to the open sets `V ∩ E`;
  * `S ≠ ∅` and `S ⊆ closure T`, because `E` is open and `E ⊆ closure (U (n+1) • z)`.

  (Mathlib does have `IsMeagre.image_val`: a set meager in a subspace is meager in the whole
  space. It was not needed.)

## Proposition 2.2 invariant (3), and Lemma 3.4

The uploaded scan is legible at these places once the pages are rendered at 200 dpi. Text
extraction drops the overlines, and that is presumably how the transcription lost them.

* **Invariant (3).** It is printed as `cl Wₙ₊₁ ⊆ cl α(Uₙ) ⊆ cl β(Vₙ) ⊆ Wₙ`; (2) reads
  `cl Uₙ₊₁ ⊆ Uₙ`, `cl Vₙ₊₁ ⊆ Vₙ`, `cl Wₙ₊₁ ⊆ Wₙ`. The commission's reconstruction
  (`β(Vₙ) ⊆ Wₙ`, `α(Uₙ) ⊆ cl β(Vₙ)`) is not what is printed. It is a weaker invariant that also
  carries the proof, and it is the one formalized. With it, the supplement in step 2 (`W ⊆ Wₙ`) is
  necessary. Under the printed (3) the supplement is automatic, since
  `W ⊆ cl α(Uₙ) ⊆ cl β(Vₙ) ⊆ Wₙ`. The reconstruction is therefore correct as a proof, and the
  supplement is a correct and needed repair of it. The printed version is also correct.
* **Lemma 3.4.** The gap is not real; it comes from the transcription. The printed lemma reads:
  "the interior of the set `cl(Uₙx)` is dense in `cl(Uₙx)`. In addition, `x` belongs to the
  interior of `cl(Uₙx)`". The proof says "Hence `cl(V ∩ Uₙx)` is not nowhere dense". The overview
  paragraph on p. 803 and Proposition 3.5 also carry the bars: "the interior of `cl(Uₙ₊₁x)` is
  contained in `Uₙx`". So the commission's 3.4′ and 3.5′ are van Mill's printed statements.
  * The first sentence, with the bars, is proved by van Mill's own argument: `vanMill_3_4_dense`.
  * The second sentence is `vanMill_3_4`.
  * Without the bars the first sentence is still true a posteriori, since `Uₙx` is open
    (`isOpen_orbitPart`), but the printed proof does not show that.

## Defects found in van Mill's text (`LEDGER.md` §6)

* Proposition 2.2 tacitly assumes `X ≠ ∅` (`isFat_empty_of_isEmpty`). This is trivial.
* In Proposition 3.5, applying 2.2 "in `E`" leaves implicit that "nowhere meager in `X`" gives
  "nowhere meager in `E`" for subsets of the open set `E`. This is an implicit step, not a false
  one.

No false statement was found. Lemmas 2.1, 3.1–3.4, Propositions 2.2 and 3.5, and Corollary 3.6
hold as printed: 2.2 with `X ≠ ∅`, and 3.6 via `effros_open_mapping`.
