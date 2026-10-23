# Commission: batch 172 — Part E, Hagopian 1976 XVII: Theorem 1 — the end case of Property 3; the `I₂` case and the side edges by Schoenflies; the ends of crossing components; T15–T17

**Go!** This batch runs on top of the batch-171 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch172.md`: this text, also pasted into the prompt.
* `Hagopian76Q.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76Q.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76Q` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XVII (batch 172)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines** as before.

## 0. On batch 171

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1799 lines, with `sorryAx` in none, all on standard axioms.

**Accepted, with thanks.**
* **`translate_Rset_disjoint` and `hagopian76_T12_uncond`.** Choosing `h(x)` off the composant of
  `x` settles what the dichotomy was needed for, with no Baire argument in `Homeo(M)`. T12 is now
  unconditional, and `RsetDichotomy` is no longer used anywhere. The ledger records that Hagopian's
  tacit step is supplied by a different argument, and that the dichotomy itself is not decided.
* `layer_meets_translate_end`, `layer_meets_translate_initial`, `hagopian76_property3_reduced`.
* `crossing_bottom_below`.
* Your checks of routes A.1 and A.2.

## 1. Notes

**A. The end case of Property 3.** Configuration: `C = d⁻¹(v)`, `0 < v < 1`, is a layer of the
extension `F` (with `d⁻¹(0) = k⁻¹(0)`). It contains a crossing `B`, and it meets `h[k⁻¹(t)]` for every
`t ≤ 6/11`; the case `t ≥ 5/11` is symmetric. Some observations; check each.

1. **`v` lies beyond `E`.** By Lemma 4's strong form, `E = d⁻¹[[0, s]]` and the layers of `E` are
   layers of `F`. If `v ≤ s`, then `C` is a layer of `E`, so `B ⊆ C ⊆ E`. But `Cl B ∩ E = ∅`
   (`hagopian76_T9_full`). So `v > s`.
2. **Where the initial segment of `h[E]` goes.** By `lemma3_half`, every `h[k⁻¹(t)]`, `t ≤ 6/11`,
   that misses `d⁻¹(0) ∪ d⁻¹(1)` lies in `C`. There are two cases.
   * (a) None of these layers meets `d⁻¹(0) ∪ d⁻¹(1)`. Then `C ⊇ h[k⁻¹((0, 6/11]])`, and since `C`
     is closed, `C ⊇ h[k⁻¹[[0, 6/11]]]`, end set included.
   * (b) Some `h[k⁻¹(t)]` meets `d⁻¹(0) = k⁻¹(0)` (or `d⁻¹(1)`).
3. **Case (a).** Let `Q = h[E] ∩ F`. If `Q ⊆ C`, your triod (report 171 §1.A, A.2) applies, since
   `0 < v < 1`. Otherwise `h[E]` continues from `C` into another layer of `F`.
   * Then `h[k⁻¹[[6/11, 1]]]` meets `F` outside `E` and misses `k⁻¹(0)`. By absorption it lies in
     `R(k⁻¹(0), E)`, and so `h[E] ⊆ R(E)`.
   * `h[E]` is then a type A′ continuum inside the line. Its layers over `[0, 6/11]` lie in the single
     line layer `C`, and some of its later layers lie in other line layers.
   * **Is `h[E]` then essential to `R(E)`?** If it is, Lemma 5 (essential continua are of type A′)
     together with the layer agreement of Lemma 4 should say that its layers are layers of the line.
     That contradicts several of its layers sitting inside `C`.
   * Find out which statement in the repository gives "the layers of an essential type A′
     subcontinuum of the line are layers of the line". `hagopian76_initial_segment` needs a common
     end set, but `extUnion_eq_of_subset` and re-centring may supply one.
4. **Case (b).** `h[E]` meets `k⁻¹(0)`, so `h[E] ∩ E ≠ ∅`.
   * The continuum `h[k⁻¹[[t, 6/11]]]` runs from `k⁻¹(0) = d⁻¹(0)` to `C = d⁻¹(v)`. If it lies in `F`,
     it contains `d⁻¹((0, v))` by `layerSet_Ioo_subset`, and in particular all of `E` beyond
     `k⁻¹(0)`. Then `E` lies in the small translate piece `h[k⁻¹[[t, 6/11]]]`. Check whether this
     contradicts `EndCtl` (the piece stays near `k⁻¹[[0, 6/11]]`, but `E` reaches `k⁻¹(1)`). I
     expect it does, but verify.
   * If it leaves `F`, apply the triod or absorption as in 3.

**B. The `I₂` case and the side edges, by Schoenflies.** `D′` is the bounded domain of a simple
closed curve `J`. By `plane_schoenflies` (batch 159) there is a homeomorphism of the plane taking `J`
to the unit circle and `D′` to the open disc.
* In disc coordinates, the points of the disc within `δ` of an arc of the circle form a connected
  set. Pull this back to get the inner collar of `I` (the `I₂` case). Choose `δ` below the distance
  from `I` to the compact `Z′`.
* **Side edges.** In disc coordinates, `J − Z′` consists of open arcs:
  * the top arc, which contains `I`;
  * the bottom arc, which contains the bottom edge;
  * pocket arcs on the sides, between points of `Z′`.

  Every component of `D′ − Z′` has closure meeting `J − Z′` (by `component_frontier_meets`, since
  `Z′` does not separate). If that frontier lies in the top or bottom arc, use the inner collars.
* **Pockets.** For T17, check whether the points whose positions are needed (`f(yᵢ₋₁)` in `L₆`)
  can lie in a pocket. A pocket component meets the circle only in a side arc. In the plane, it is
  bounded by `Z ∪` (a side segment), and it lies at abscissae reachable from the side.
  * Link control puts `L₆` far from the sides, but a pocket can reach in.
  * Nothing joins `f(yᵢ₋₁)` to `yᵢ₋₁` by a path off `Z` that is known in advance. State what T17
    needs, and whether Hagopian's own argument has this gap.

**C. The ends of crossing components.** Report 171 §1.C finds this tied to item A: the
uncontrolled configuration is a crossing continuum that runs out along the chain to an end link.
Once A is settled, revisit. In particular, check whether Property 3 itself, together with the
first-component argument of T17, makes C unnecessary.

**D. T15–T17 and `hagopian76_theorem1`.** No dichotomy is needed any more. Proceed as far as A–C
allow, and state the final shape as `Hagopian76Thm1` itself, or as conditional on named `Prop`s for
whatever remains open (for example `Property3End`, `CoverPocket`, `CrossingEnds`).

## 2. Order

A, B, C, D.

## 3. Places to check (candidate ledger entries)

1. **p. 347, Property 3:** the four sentences, as in batch 171.
2. **p. 347:** "It follows from Property 3 that `I` is finite".
3. **p. 348:** "Note that `[x₁, x₂]` does not have Property 4".
4. **pp. 348–349:** the induction; "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`"; "the
   continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`"; "Let `Cᵢ₋₁` be the first component …".

## 4. Deliverables

1. The items of §1.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch172.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s for open steps (D) are `def … : Prop`, listed in the report.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
