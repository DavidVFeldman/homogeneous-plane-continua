# Commission: batch 169 — Part E, Hagopian 1976 XIV: Theorem 1 — above and below a crossing continuum; generic `p`, `q`; the dichotomy for `R(E)`; T13; Property 3

**Go!** This batch runs on top of the batch-168 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch169.md`: this text, also pasted into the prompt.
* `Hagopian76N.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76N.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76N` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XIV (batch 169)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

## 0. On batch 168

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1736 lines, with `sorryAx` in none, all on standard axioms.

**Accepted.**
* Your §1.A analysis of what T13–T17 use. It is the most useful single result of the last three
  batches.
* `crossing_piece_of_R`, including the addition that the crossing piece lies in one extension `H`.
* `crossing_separates` and `crossing_pair_separates`.
* `hagopian76_T12` in its shape.

## 1. Two observations

**1. Points off `R(E)` are generic, if we do not insist that they lie on `K`.**
* `R(E)` is meagre in `M`. It is the union of countably many extensions (an increasing chain in each
  direction; or use second countability), and each extension is a proper subcontinuum of the
  indecomposable `M`, hence nowhere dense.
* So every nonempty open subset of `M` contains points off `R(E)`. The batch-168 obstruction came
  only from requiring `p` and `q` on the arc `K₀`, which can be a meagre set.
* **Question for A below: is `K` needed?** In T17, `K` serves as the reference arc for "above" and
  "below" ("`f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`"), and as the place where `yᵢ` is
  picked. A crossing continuum `Z` (closure meeting both open side edges, missing `π⁻¹[I₂]` and
  `E`) has its own *below* and *above*:
  * **below:** the points of `π⁻¹[D] − Z` joined to points just over the bottom edge by a connected
    set missing `Z`;
  * **above:** the same with `I₂` in place of the bottom edge.
  `crossing_separates` shows these sets are disjoint along `K₀`. The general statement is that they
  are disjoint and cover `π⁻¹[D] − Z`, with every component of `π⁻¹[D] − Z` meeting the
  neighbourhood of one of the two edges. This is the Jordan curve argument of
  `rect_domain_crossing_separates`, without the vertical.
* With that, `p` and `q` are chosen as follows:
  * Take `Z` from Lemma R, near `x`.
  * Take `p` in the open set `W ∩ (below Z)` and `q` in `W ∩ (above Z)`, both off `R(E)`, by
    meagreness.
  * Both sets are nonempty open subsets of `M`. Points of `M` above the axis accumulate at `x` at
    every height (`M_meets_above`), and `Z` stays above a positive height near `x`. The part above
    `Z` near `x` is nonempty for the same reason, applied above `Z`'s lowest point near `x`. Check
    this, or replace it by Lemma T′ relative to `Z`.
  * Then `p = h(x)` and `q = h₁(x)` by Lemma 2.
  * The `p`-component crosses: Lemma T applies to every point of `M` low over the middle range
    (report 167 §1.E: `pi_thin_near_layer` and Effros).

**2. The dichotomy follows from `Cl R(E) = M`.** If `Cl R(E) = M`, then `R(E)` and `g[R(E)]` are
both composants of `M` (`hagopian76_Rset_composant`, transported by `g`). Composants of a continuum
are equal or disjoint. So batch 168's question F now bears directly on T17.

## 2. Items

**A. Above and below** (`crossing_sides`), as in §1.1, in collar coordinates and then in
`π⁻¹[D]`. Then **check whether T15–T17 can use "above/below `Z`" in place of positions on `K`**.
Read p. 348 again for every use of `K` and of `yᵢ ∈ K`. If `K` is essential somewhere, say where.

**B. Generic `p`, `q`** (`exists_generic_pq`):
* `p`, `q ∉ R(E)`;
* `p = h(x)` and `q = h₁(x)` with `h`, `h₁` `ε`-small;
* `p` below and `q` above a crossing piece `Z ⊆ H − E` of one extension `H` away from `X`;
* the `p`-component crosses;
* `H` separates `p` from `q` in `π⁻¹[D]`. This should follow from `p`, `q ∉ H ⊆ R(E)` and the
  separation by `Z ⊆ H`.

**C. The dichotomy for `R(E)`** (`Rset_homeo_dichotomy`): if `g[R(E)] ∩ R(E) ≠ ∅` then
`g[R(E)] = R(E)`. Three routes, in order of preference:
1. **`Cl R(E) = M`**, then composants. A possible argument: `Cl R(E)` contains `E`, and Lemma R gives
   crossing pieces of `R(X, E)` through points arbitrarily close to every middle point of `E`.
   Translate this by Effros to every point of `M`, using homogeneity and the fact that
   `Cl R(g[E]) = g[Cl R(E)]`. Look for a contradiction with `Cl R(E)` being a proper, hence nowhere
   dense, subcontinuum. I do not have one.
2. **Directly, by no hair and absorption.** Let `z ∈ g[F] ∩ F′` for extensions `F`, `F′`.
   * Re-centre at a type A′ piece `E″` of the line, chosen so that one end set of `E″` misses the
     compact set `g[F]`, with `z` on the correct side.
   * Absorption relative to `E″` then gives `g[F] ⊆ R(E″) = R(E)`.
   * The existence of such an end set is the point to check. `g[F]` meets only those layers of the
     line that it meets, and a proper subcontinuum need not meet all of them. Is that provable?
   * `R(E″) = R(E)` for a piece `E″` essential to `R(E)` should follow from
     `extUnion_eq_of_subset` and `closure_Rset_essential`.
3. **Otherwise** state the dichotomy as a `Prop`, prove T13–T17 with it as a hypothesis, and record
   that Hagopian uses it tacitly.

**D. T13: the irreducible separating extension** (`iInter_chain_extension`, report 168 §5).
Extensions away from `X` form a chain. The intersection of a decreasing chain of separating ones
still separates, by compactness. That it is an extension is the point to prove: use Lemma 4 and the
end-set property.

**E. Property 3**, continuum form, with margins (`crossing_set_closed`, `hagopian76_property3`, the
shift `g`).

**F. T17's missing statement** (`follows_essential_crossing`, report 168 §1.E), in the form A needs.
If A lets T17 pick its points `yᵢ` generically (low, near `E`), then Lemma T may cover it, as it
does for `p`. Say so.

**G. T15–T17 and `hagopian76_theorem1`**, if reached; conditional on C.3 if necessary.

## 3. Order

A, B, C, D, E, F, G. If C resists, take C.3 and go on.

## 4. Places to check (candidate ledger entries)

1. **p. 347, T12:** whether `K` is needed at all (A).
2. **p. 347–349:** the tacit dichotomy "`h[R(E)] ∩ R(E) = ∅` from `p ∉ R(E)`".
3. **p. 347, T13:** "Let `F` be a continuum that is irreducible with respect to the following
   properties"; the existence sentence.
4. **p. 347, Property 3:** the three sentences.
5. **pp. 347–349, T15–T17**, if reached.
6. **`Cl R(E) = M`?**

## 5. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch169.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * A hypothesis-as-`Prop` (C.3), if used, is a `def … : Prop` and is named in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * if G is not finished, a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
