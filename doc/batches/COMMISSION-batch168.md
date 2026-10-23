# Commission: batch 168 — Part E, Hagopian 1976 XIII: Theorem 1 — crossing pieces of `R(E)`; what T13–T17 need of `p`, `q`; Property 3; T12 (3), T13

**Go!** This batch runs on top of the batch-167 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch168.md`: this text, also pasted into the prompt.
* `Hagopian76M.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76M.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76M` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XIII (batch 168)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before (`STATUS:`, and `STATUS: need help` with the obstruction in one
sentence).

## 0. On batch 167

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1722 lines, with `sorryAx` in none, all on standard axioms.

**Accepted.**
* `crossing_translate`, including your improvements:
  * the end sets avoided through injectivity of the collar;
  * the band by uniform continuity;
  * the new lemma `exists_mem_closure_component_notMem`.
* `K0_dense_low`, with Effros' theorem in place of Lemma 2 at a fixed point.
* `crossing_essential` and `hagopian76_T12_parts12`.
* **Your Cantor-comb objection.** My countability suggestion in §2.B was wrong as stated; the
  ledger records it as my error.

## 1. Crossing pieces of `R(E)`: absorption does it

You note that the translates `h[E]` of Lemma T are not known to lie in `R(E)`. Their middles do,
whenever they meet `R(E)`. Check this argument.

**Lemma R (`crossing_piece_of_R`).**
1. **Points of `R(E) − E` near `x`.** Let `x ∈ E` with `k(x)` in the middle range.
   * `E` is a proper subcontinuum of the indecomposable continuum `Cl R(E)` (Lemma 6), so `E` is
     nowhere dense in `Cl R(E)`. Hence `x` is a limit of points of `Cl R(E) − E`.
   * `R(E)` is dense in `Cl R(E)`, and `E` is closed. So `x` is a limit of points `y ∈ R(E) − E`.
   * Each such `y` lies in an extension `F` of `E`, away from `k⁻¹(0)` or away from `k⁻¹(1)`.
     Treat the first case; the second is the same with `σ ∘ k`.
2. **`π(y)` is above the axis** for `y` near `x`. This follows from `no_M_below`/T6: no point of
   `π[M]` lies just below `γ` over the middle range.
3. **A small translate through `y`.** Lemma 2 at `x` gives an `ε`-homeomorphism `h` with
   `h(x) = y`, for `y` close enough to `x`.
4. **Its middle lies in `R(E)`.** Let `G = h[k⁻¹[[a′, b′]]]`. It is a continuum that meets `F` (at
   `y`) and misses `k⁻¹(0)` (since `h` is small and `a′ > 0`). By absorption
   (`subset_extUnion_of_meets`), `G ⊆ R(k⁻¹(0), E) ⊆ R(E)`.
5. **It crosses.** By Lemma T, `G` misses `E`, and the `y`-component of `M ∩ π⁻¹[D]` crosses and
   contains `h[k⁻¹[[3/22 + ζ/2, 19/22 − ζ/2]]]`. Moreover, the component of `R(E) ∩ π⁻¹[D]`
   through `y` contains that middle set and has closure meeting both side preimages. The argument
   is the same as Lemma T step 4, run inside `G ⊆ R(E)`.

So `R(E)` has crossing pieces, disjoint from `E`, through points arbitrarily close to `x`. They
cross `K₀` low down, at heights going to `0` with `ε` (as in Lemma T′). This is `crossing_piece_of_R`
of report 167 §5, with `Z = G ∩ π⁻¹[Cl D]`, or the component of it you need.

## 2. Items

**A. What T13–T17 need of `p`, `q`, `h`, `h₁`, `f`, `C`.** Before building T12 (3), read
pp. 347–349 and list exactly what is used. Batch 166 did this for "inaccessible": the word was never
used. Check in particular:
* whether `p ∉ R(E)` is used, and where;
* whether "distinct composants of `Cl R(E)`" is used beyond making `C` and the `q`-component
  different, and `h[R(E)] ≠ h₁[R(E)]`;
* whether `p`, `q ∈ Cl R(E)` is used;
* exactly which separation statements are used: "R(E) separates `p` from `f(p)` in `π⁻¹[D]`" in
  T12; "`F` separates `p` from `f(p)`" in T13; Property 4's "`d⁻¹[[x₂ₙ₋₁, x₂ₙ]]` separates `yₙ` from
  `f(yₙ)`".

Then state the weakest T12 that T13–T17 can use. The aim is a choice of `p`, `q` that avoids
counting composants on the arc `K₀`.

**B. Lemma R** (§1), and the planar `crossing_pair_separates` of report 167 §5. Two disjoint
crossing continua `Z₁`, `Z₂` in `π⁻¹[Cl D] − E − π⁻¹[I₂]` cut `π⁻¹[D]` into three parts along
`K₀`. Use the Jordan curve theorem in collar coordinates, as in `hagopian76_K0_crosscut`.

**C. T12 (3)**, in the form A finds sufficient. One candidate, to check against A:
* Take `p = h(x)` and `q = h₁(x)` with `h`, `h₁` small and `p`, `q ∈ M ∩ K₀`, on either side of a
  crossing piece `Z ⊆ R(E)` given by Lemma R.
* By `crossing_pair_separates` (or the single-continuum form), `Z` separates `p` from `q` in
  `π⁻¹[D]`, provided the components `C ∋ p` and `C′ ∋ q` miss `Z`. They do if `p`, `q ∉ R(E)`:
  a component of `M ∩ π⁻¹[D]` meeting `Z` ⊆ `R(E)` lies in `R(E)`, by absorption again (check this:
  the component's closure is a continuum missing `k⁻¹(0)`, and it meets an extension).
* So what is needed is points `h(x)` on `K₀` off `R(E)`, on both sides of some `Z`.
* Points off `R(E)`: if every small translate through `x` landing on `K₀` near `x` were in `R(E)`,
  then the open set `W` (Lemma 2 at `x`) would meet `K₀` only in `R(E)`. Check whether this
  contradicts the composant `R(E)` being meagre in `Cl R(E)`. It does not, if `W ∩ K₀` is small.
  Say what is needed. One alternative is Effros applied to a point `x′` of `E` chosen off the
  countably many continua `Fₙ ∩ K₀`, with `R(E) = ⋃ Fₙ` an increasing union of extensions.

**D. Property 3** in the continuum form of report 167 §5:
* `crossing_set_closed` (hyperspace limit);
* `hagopian76_property3`;
* the shift `g` with a margin.

**E. T13**, then **T15–T17** and **`hagopian76_theorem1`**, if reached. For T17's low point of
`Cᵢ₋₁` (report 167 §1.E), say whether Lemma R together with Property 3 gives it. If not, state the
missing statement.

**F. `Cl R(E) = M`?** Optional. Record any argument either way.

## 3. Order

A first; it may change C. Then B, C, D, E, F.

## 4. Places to check (candidate ledger entries)

1. **p. 347, T12:** the choice of `p`, `q`; "By Property 1, `R(E)` intersects an arc in `K` …".
   After A, say which of Hagopian's conditions on `p`, `q` are used.
2. **p. 347, Property 3:** the three sentences.
3. **p. 347, T13:** the existence sentence.
4. **pp. 347–349, T15–T17:** "It follows from Property 3 that `I` is finite"; Property 4; "Following
   Bing [2, p. 225]".

## 5. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch168.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order, with A's list in full;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * if E is not finished, a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
