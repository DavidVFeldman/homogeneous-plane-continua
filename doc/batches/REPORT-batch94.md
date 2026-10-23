Commission read: `COMMISSION-batch94.md` (batch 94: Moore's non-cut-point theorem; the two end elements of Bing's decomposition), with its skeleton `NonCut51.lean`, saved as `HPC/Plane/NonCut51.lean`; `import HPC.Plane.NonCut51` (and its two companions) is added at the end of `HPC.lean`.

# Report, batch 94

## Summary

* **Refutations.** One, of the reverse inclusion asked about in §3 Q2 (not a skeleton statement):
  `Counter92.bingElt_subtype_reverse_false`, proved in Lean (§3 below). No skeleton statement is
  false.
* **Item 1 (Nadler 6.3, 6.4, 6.6, 6.7):** all proved.
* **Item 2:** `isEndElt_iff_not_isCutElt`, `decompositionSpace_props`,
  `isCutElt_iff_isCutPoint_quot`, `exists_two_endElts` are proved. `not_subset_of_endElts` is
  proved **exactly as stated**, so the obstruction the commission anticipated does not arise
  (§2.3). Route (a), the quotient space, was used.
* **Item 3:** Q1 (`bingS_subcontinuum`) is **proved**. Q2 (`bingElt_subtype_subset`) is **proved**.
  The reverse inclusion is **refuted** in Lean on `S₀`.
* **Build and axioms.** `lake build HPC` passes. The four batch-94 files contain no `sorry`.
  `Axioms94.lean` writes `axioms-batch94.txt`. Every batch-94 result uses only `propext`,
  `Classical.choice`, `Quot.sound`.

**Files.**

| File | Contents |
| --- | --- |
| `HPC/Plane/NonCut51Gen.lean` | §1: `IsSeparation`, `IsCutPoint`, 6.3, 6.4, 6.6, 6.7 and the separated-set lemmas. Imports only Mathlib. |
| `HPC/Plane/NonCut51.lean` | §2 and §3 of the skeleton. |
| `HPC/Plane/NonCut51Counter.lean` | The refutation of the reverse inclusion in Q2. |
| `Axioms94.lean`, `axioms-batch94.txt` | `#print axioms` for the batch-94 results. |

**Shape changes (all recorded in the docstrings).**

1. §1 is moved, unchanged in meaning, from `NonCut51.lean` to `NonCut51Gen.lean`, so that the
   general theorem depends on Mathlib only (`NonCut51.lean` imports it).
2. `IsSeparation`: the skeleton's `IsOpen (Y := Y) ((↑) ⁻¹' P)` does not elaborate, because `Y` is
   not an argument name of `IsOpen`. It is written `IsOpen ((↑) ⁻¹' P : Set Y)`, which is the
   intended relative openness.
3. `[Nontrivial X]` is dropped from `exists_nonCutPoint_of_cut` (6.6) and
   `not_subset_of_nonCutPoints` (6.7), since the proofs don't use it: a separation already
   provides two points. It is kept on `exists_two_nonCutPoints`, where it is needed.
4. §3: a subtype `S'` has no `CompactSpace` instance of its own, so as written `BingS S'` and
   `bingElt x` (for `x : S'`) do not elaborate. Both statements install the instance from `hS'` via
   `haveI : CompactSpace S' := isCompact_iff_compactSpace.mp hS'.1` inside the statement.
5. `bingElt_subtype_subset`: the hypothesis `hnd : S'.Nontrivial` is unused and is dropped.

## Refutation: the reverse inclusion of §3 Q2

`Counter92.bingElt_subtype_reverse_false`. Take batch 92's `S₀` (which satisfies `BingS`, by
`bingS_S₀`), its bar `S' = [0, 2] × {0}` (`barSet`, a subcontinuum by `isContinuum_barSet`), and
`x = p₀ = (1/2, 0)`. Then

    ¬ (bingElt p₀ ∩ S' ⊆ (↑) '' (element of p₀ computed in S')).

The reason:
* In `S₀`, `bingElt p₀` is the whole bar (batch 93, `bingElt_bar`), so it contains `q₀ = (1, 0)`.
* In the arc `S'`, the continuum `[0, 3/4] × {0}` contains `[0, 5/8] × {0}` interiorly (relative
  to `S'`), and that contains `p₀` interiorly. So the element of `p₀` computed in `S'` lies in
  `[0, 3/4] × {0}` and misses `q₀` (`q₀_notMem_bingElt_bar`).

**The commission's example.** `S' = cl C₁ ∪ [1, 3/2] × {0}`, `x = (1/2, 0)`. I worked this out by
hand and did not check it in Lean. The element of `x` computed in `S'` is `[0, 1] × {0}`, not
`[0, 3/2] × {0}`.
* `⊆`: for small `ε, δ > 0`, the continuum `{0 < height ≤ ε} ∪ [0, 1 + δ] × {0}` contains the
  continuum `{0 < height ≤ ε/2} ∪ [0, 1 + δ/2] × {0}` interiorly in `S'`, and that contains `x`
  interiorly.
* `⊇`: a continuum containing `x` interiorly in `S'` contains curve points of arbitrarily small
  height. Hence it contains a whole tail of `C₁`, hence `[0, 1] × {0}`.

So `bingElt (x : S₀) ∩ S' = [0, 3/2] × {0}` is strictly larger than the element in `S'`. This is the
data route 1 for Theorem 9 Q1 has to handle: the elements of `S'` refine the traces of the elements
of `S` and can be strictly smaller.

## Item 1: Nadler Chapter VI

All proved in `NonCut51Gen.lean`, for an arbitrary topological space (no metric).

**A reformulation used throughout.** `Y = P | Q` is the same as `Y = P ∪ Q` with `P`, `Q`
nonempty and *separated* (`closure P ∩ Q = ∅ = P ∩ closure Q`): `IsSeparation.disjoint_closure_left`
and `_right` give one direction, `IsSeparation.of_separated` the other. The basic fact Nadler uses
without comment is `subset_side_of_isPreconnected`: a preconnected subset of `P ∪ Q`, with `P`, `Q`
separated, lies in `P` or in `Q`. Its specialisation `IsSeparation.subset_or_subset` is used in
6.4, 6.6 and 6.7. Also `exists_separation_of_not_isConnected`: a nonempty disconnected set has a
separation, with any chosen point on the right.

**6.3 (`isConnected_union_of_separation`). What needed more than the text.**
* Nadler's one-line argument is that "`A ∪ C = E | F` with `C ⊆ E` gives the separation
  `S = F | (E ∪ B)`". To check that `F` and `E ∪ B` are separated, two facts are needed:
  * `F` and `B` are separated because `A` and `B` are. This uses the relative openness of `A` and
    `B` in `S ∖ C`, through the reformulation above.
  * `F` and `E` are separated *in `S`*, not only in `A ∪ C`. This holds because the pieces come
    from open sets `u ⊇ E` and `v ⊇ F` of `S` that meet `A ∪ C` disjointly. That is how the proof
    is organised (`union_subset_of_separation_aux`).
* Connectedness of `S` enters only as "`S` is not a union of two nonempty separated sets"
  (`eq_empty_of_separated_cover`).

**6.4 (`nadler_6_4`). What needed more than the text.** Three steps are implicit:
* `x ≠ y`, from `x ∈ M ⊆ S ∖ {y}`;
* `x ∉ N ∪ {y}`, because `M ∩ N = ∅`, so `N ∪ {y} ⊆ S ∖ {x}`;
* "a connected subset of `K ∪ L` lies in `K` or in `L`" (the separated-set lemma).

6.3 is applied with `C = {y}` and the separation `S ∖ {y} = N | M`, with the order swapped. No
compactness or `T₁` is used.

**6.6 (`exists_nonCutPoint_of_cut`), following Nadler's four steps** (`exists_nonCutPoint_left`).
* (1) For every `x ∈ U` a separation `S ∖ {x} = U_x | V_x` with `c ∈ V_x` is chosen once, by
  `choose`.
* (2) `U_x ∪ {x} ⊆ U` is 6.4 with `(x, y) := (c, x)`. `U_x ∪ {x}` is closed because its complement
  `V_x` is open in the open set `S ∖ {x}`. This is where `T₁` is used.
* (3) `y ∈ U_x ⇒ U_y ∪ {y} ⊆ U_x`. Here `x ∈ S ∖ {y} = U_y ∪ V_y`.
  * If `x ∈ V_y`, it is 6.4 directly.
  * If `x ∈ U_y`, then 6.4 (with the roles of `x`, `y` swapped) gives `V_x ∪ {x} ⊆ U_y`. So
    `c ∈ U_y ∩ V_y`, which is impossible.
  * Consequently `x ∉ U_y ∪ {y}`.
* (4) The maximal principle is used as `zorn_superset` on `{U_x ∪ {x} : x ∈ U}`, which gives a
  minimal member rather than a maximal nest. A nonempty chain has nonempty intersection (closed
  sets in a compact space, directed by the chain property). A point `p` of the intersection lies
  in `U`, and `U_p ∪ {p}` is a lower bound, by (3). For a minimal `U_x ∪ {x}` and any `q ∈ U_x`,
  (3) gives `U_q ∪ {q} ⊆ U_x ∪ {x}`. Minimality then forces `x ∈ U_q ∪ {q}`, which (3) excludes.

The `V`-side is the same lemma applied to the symmetric separation.

**`exists_two_nonCutPoints`**: if there is no cut point, any two distinct points serve; otherwise
6.6. **6.7 (`not_subset_of_nonCutPoints`)**, as in the commission: a point `c ∉ Z` is a cut point;
`Z` lies on one side of `S ∖ {c} = U | V`, and the non-cut point that 6.6 provides on the other side
is not in `Z`.

## Item 2: end elements

**Route chosen: (a)**, the quotient `Quotient (Setoid.ker bingElt)`.

* **`isEndElt_iff_not_isCutElt`**, proved as in the commission.
  * ⇒: a separation of `S ∖ g_r` has open pieces, because `g_r` is closed. Take points `q`, `q'`,
    one in each piece. Their elements are connected and disjoint from `g_r` (the partition), so
    each lies wholly in its piece. That exhibits `Separates g_r g_q g_{q'}`.
  * ⇐: a `Separates` witness covers `S ∖ g_r` by two disjoint open sets, each containing a point
    of `S ∖ g_r`.
  * The only extra fact is `bingElt_ne_univ` (from Theorem 8 (b)), which makes `S ∖ g_r` nonempty.
* **`decompositionSpace_props`.**
  * Compact and connected: Mathlib instances for quotients.
  * `T₁`: the preimage of `{[r]}` is `bingElt r` (`preimage_mk_singleton`, from the partition),
    which is closed.
  * Nontrivial: `bingElt_ne_univ`.
* **`isCutElt_iff_isCutPoint_quot`.**
  * ⇒ (connected `S ∖ g_r` gives connected `(S/G) ∖ {[r]}`): continuous image under a surjection.
  * ⇐: given open `u`, `v` covering `S ∖ g_r` disjointly there, the traces `u ∖ g_r`, `v ∖ g_r`
    are saturated. Each element is connected and disjoint from `g_r`, so it lies in one trace.
    Their images are therefore open in the quotient, cover `(S/G) ∖ {[r]}`, and are disjoint
    there. Connectedness of the quotient complement then puts all of `S ∖ g_r` in `u` or in `v`.
* **`exists_two_endElts`**: Item 1 on the quotient gives two non-cut points. Representatives of
  them are two distinct non-cut elements, i.e. two end elements.

**2.3, `not_subset_of_endElts`: proved as stated.** The commission expected an obstruction through
the quotient, but none arises if one argues directly.
* Take the two end elements `g_a ≠ g_b` from `exists_two_endElts`.
* If the proper subcontinuum `Z` met both, at `x ∈ g_a` and `y ∈ g_b`, then `g_x = g_a` and
  `g_y = g_b`. `IsEndElt` depends only on the element (`IsEndElt.of_eq`).
* So Theorem 8 (c) (`bingElt_irreducible`) gives `Z = S`, a contradiction.

The quotient enters only through `exists_two_endElts`. Nadler 6.7 on the quotient is not needed.

## Item 3: reconnaissance

**Q1 (`bingS_subcontinuum`): proved.** No transfer lemma was missing from Mathlib. The passage
between `Set S'` and `Set S` uses:
* `IsInducing.subtypeVal.isCompact_iff` and `.isPreconnected_image`: a subset of `S'` is compact
  or preconnected iff its image is;
* `Subtype.image_preimage_coe` and `preimage_image_eq` (injectivity);
* `IsInducing.closure_eq_preimage_closure_image`, for the closure-disjointness clauses of
  `IsTriod`.

The four clauses:
* Atriodic: a triod in `S'` maps to a triod in `S` (`isTriod_image_val`).
* Hereditarily unicoherent: images, then pull the connected intersection back.
* Hereditarily decomposable: pull back the two proper subcontinua of `S` given by `hS.hd`. They
  lie in `S'` because their union is the image of a subset of `S'`.
* Connected and nontrivial: directly from `hS'` and `hnd`.

**Q2 (`bingElt_subtype_subset`): proved**, by the report's argument. Let `H ⊇ int H' ∋ x` be
doubly interior in `S`.
* `H ∩ S'` and `H' ∩ S'` are continua by hereditary unicoherence of `S` (`BingS.inter_two`; both
  contain `x`).
* Their preimages in `S'` are therefore continua (`isContinuum_preimage_val`).
* Interiors pull back into interiors (`preimage_interior_subset_interior_preimage`).

So `H ∩ S'` contains `x` doubly interiorly in `S'`, and the element of `x` in `S'` lies in `H`.
`BingS S'` is not needed.

**The reverse inclusion is false**; see the refutation section at the top.

## Not attempted

As instructed: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
`theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`, and Q1/Q3 of Theorem 9.
Their earlier `sorry`s are unchanged.

## Next

The commission's §5 stands.
* For Theorem 9 Q1 by route 1, the pieces now available are:
  * `BingS S'` for a subcontinuum (Q1 here), so Theorem 8 and `exists_two_endElts` apply to `S'`;
  * the inclusion of the elements of `S'` into those of `S` (Q2).
* The refutation above shows that the step "an end element of `S` meeting `S'` meets an end
  element of `S'`" has to be argued with elements of `S'` that may be strictly smaller than the
  traces of the elements of `S`.
