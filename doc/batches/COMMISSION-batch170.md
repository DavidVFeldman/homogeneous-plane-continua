# Commission: batch 170 — Part E, Hagopian 1976 XV: Theorem 1 — `ExtChainInter`; the covering half; "follows" for crossing components; Property 3; T15–T17 under `RsetDichotomy`

**Go!** This batch runs on top of the batch-169 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch170.md`: this text, also pasted into the prompt.
* `Hagopian76O.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76O.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76O` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XV (batch 170)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

**The aim of this batch is a complete Theorem 1, conditional on `RsetDichotomy` if necessary.**
Property 3 has been carried for four batches without an attempt. It comes first after A–C.

## 0. On batch 169

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1769 lines, with `sorryAx` in none, all on standard axioms.

**Accepted.**
* `isMeagre_Rset`, by your shorter route.
* `crossing_sides`, the disjointness half.
* `exists_generic_pq`.
* `Rset_homeo_dichotomy_of_closure`, and `RsetDichotomy` as the carried hypothesis.
* `iInter_chain_extension` and `hagopian76_T13` under `ExtChainInter`.
* Your reading of p. 348 for `K`.

## 1. Three short routes

**A. `ExtChainInter` holds, by Lemma 4 (strong form) and `piece_map`.** In the Zorn argument, all
members of the chain lie in the starting extension `H` (map `d`, `layer d 0 = k⁻¹(0)`). For each
member `Fᵢ` (map `dᵢ`, `layer dᵢ 0 = k⁻¹(0) = layer d 0`), `hagopian76_initial_segment` with
`E := Fᵢ` and `F := H` gives `Fᵢ = d⁻¹[[0, sᵢ]]` with `sᵢ > 0`.
* Then `⋂ Fᵢ = d⁻¹[[0, s*]]` with `s* = inf sᵢ`: a point lies in every `Fᵢ` if and only if
  `d(x) ≤ sᵢ` for all `i`, if and only if `d(x) ≤ s*`.
* `s* > 0`, since `E ⊆ ⋂ Fᵢ` and `E = d⁻¹[[0, s_E]]` with `s_E > 0` (Lemma 4 again).
* `piece_map` with `a = 0` and `b = s*` gives a minimal admissible map on `d⁻¹[[0, s*]]` whose layer
  over `0` is `layer d 0 = k⁻¹(0)`. (`piece_map` needs lower semicontinuity: `lsc_of_minimalAdmissible`.)
* So the intersection is an extension of `E` away from `k⁻¹(0)`. Your worry about the last layer does
  not arise: the members are full initial segments of one decomposition, `d`.
* State `ExtChainInter` for chains inside a given `H`, or prove it in that form and use it in
  `hagopian76_T13`.

**B. The covering half, for the separators T17 uses.** These separators are `d⁻¹[I]`, `d⁻¹[J]` and
`P`: subcontinua of `F ⊆ M`, hence proper subcontinua of `M`. **No proper subcontinuum of `M`
separates the plane** (`no_proper_subcontinuum_separates`, batch 158). So your bubble cannot occur
for them.
* Let `U` be a component of `π⁻¹[D] − Z` that reaches neither the vertical below `Z` nor the
  vertical above it.
* If `Fr U ⊆ Z`, then `Z` separates the plane, which is impossible.
* So `U` meets the frontier of `π⁻¹[D]`. There are three cases:
  * **near the bottom:** connect to the low strip below `min height(Z) > 0`, which meets the vertical
    low down. So `U` is below.
  * **near `I₂`:** connect through a thin neighbourhood of `I₂` inside `D`, which reaches the
    vertical just below `w`. So `U` is above. Check that this neighbourhood minus `Z` is connected;
    `Z` misses `I₂` at a positive distance.
  * **at an open side edge, between two points where `Z` meets that edge:** a pocket bounded by `Z`
    and a segment of the side. This case is not excluded by non-separation.
* Find out whether T17 ever needs positions of points in such a pocket. If it does, the points in
  question (`f(yᵢ₋₁)` and the like) are within `ε₃` of points known to be below or above. Positions
  could then be defined through the side edges as well as the vertical. In that version, "below `Z`"
  means joined to the part of either side edge below the lowest point of `Z` on that edge. State
  what you need.

**C. "Follows" for crossing components** (`follows_essential_crossing`, weaker form). For a crossing
component `C`, `crossing_essential` gives `Cl C ⊆ h′[E]` with `h′⁻¹[Cl C] = G` a subcontinuum of
`E`.
* `Cl C` meets the left edge and the right edge.
* By link control and Property 1 (`h′[piece (j + 1)] ⊆ L j`), `G` meets a layer in pieces `≤ 3` and
  a layer in pieces `≥ 9`.
* By `layerSet_Ioo_subset`, `G` contains every layer strictly between. So `Cl C ⊇ h′[k⁻¹[(3/11, 8/11)]]`,
  and `L₂, …, L₁₀` all meet `Cl C`. This is the "follows" of T9. The crossing is now a hypothesis,
  not a conclusion; that was the step that failed in batch 166.
* Check whether this weaker form suffices for T17, where `Cᵢ₋₁` is a crossing component essential to
  `h[R(E)]`, in place of "`C` contains the middle of a small translate". If T17 needs the translate
  to be small, say where.

## 2. Items

**A. `ExtChainInter`** (§1.A); then `hagopian76_T13` unconditionally.

**B. The covering half** (§1.B), for proper subcontinua of `M`, in the form T17 needs.

**C. "Follows" for crossing components** (§1.C).

**D. Property 3** (report 167 §5, continuum form, with margins):
* `crossing_set_closed` (the least `v`, by the hyperspace limit);
* the shift `g`;
* `hagopian76_property3`.

**E. T15–T17 and `hagopian76_theorem1`**, under `RsetDichotomy` if necessary:
* "It follows from Property 3 that `I` is finite";
* `J`, the `xᵢ`;
* Property 4 and its base case ("only the last block separates", unargued);
* the induction "Following Bing [2, p. 225]", Cases 1 and 2.

If the assembly is reached under `RsetDichotomy`, state the result as
`RsetDichotomy-for-every-E → Hagopian76Thm1`, quantified as needed.

**F. The dichotomy**, optional, if time remains. Report 169 §1.C's case C.2 is a continuum `G` with
`E ⊆ G ⊆ g[R(E)]`. A question that may help: is `E` then essential in `g[F]` for an extension `g[F]`
containing it, or inside one of its layers? If it is essential, `R(E) = R(g[F]) = g[R(E)]` by
`closure_Rset_essential` and the composant characterization.

## 3. Order

A, B, C, D, E, F.

## 4. Places to check (candidate ledger entries)

1. **p. 347, T13:** "Let `F` be a continuum that is irreducible with respect to the following
   properties"; the existence sentence.
2. **p. 347, Property 3:** "Let `v` be the first point …"; "By Lemma 1 and Property 1, `L` follows a
   type A′ continuum in `d⁻¹(v)` …"; "This contradicts the definition of `v`".
3. **p. 347:** "It follows from Property 3 that `I` is finite".
4. **p. 348, Property 4:** the base case.
5. **pp. 348–349, the induction:** each "Hence …" and "It is not above …"; the use of positions.
6. **The tacit dichotomy:** its final status, and whether Theorem 1 is verified only conditionally.

## 5. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch170.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * if E is not finished, a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
