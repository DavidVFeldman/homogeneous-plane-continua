Commission read: `COMMISSION-batch95.md` (batch 95: Theorem 9 (Duke 1951), the two open steps), with its skeleton `Theorem9B.lean`, saved as `HPC/Plane/Theorem9B.lean`; `import HPC.Plane.Theorem9B` is added at the end of `HPC.lean`.

# Report, batch 95

## Summary

* **Refutations.** None. No skeleton statement is false, and no counterexample to the descent
  turned up: the descent is proved.
* **QA (`elt_between_subset`):** proved.
* **QB (`endElt_contains_endElt_sub`): proved.** The proof uses Theorem 8 (a) for `S` and for
  `S'`, Nadler 6.3, and the batch-94 inclusion of elements. QA and atriodicity are not used
  directly. The general form `endElt_inter_contains_endElt` only needs `S'` to *meet* `g`.
* **QC (`endElt_mem_bingH'`, = Q1):** proved, unconditionally.
* **Q3′ (`endElt_of_bingH_mem_bingH`, the descent):** proved. **Q3
  (`bingH_irreducible_singleton'`):** proved from it.
* **Assembly (`theorem9_1951'`): Theorem 9 is proved unconditionally.**
* **Batch 93's `theorem9_1951`** still depends on `sorryAx`. Its two `sorry`s
  (`endElt_mem_bingH`, `bingH_irreducible_singleton` in `HPC/Plane/Atriodic51B.lean`) cannot be
  replaced by references to the new results: `Theorem9B.lean` imports `Atriodic51B.lean` (through
  `NonCut51.lean`), so such a reference would create an import cycle. `Atriodic51B.lean` is
  therefore **not edited**. `theorem9_1951'` has the same statement as `theorem9_1951` and is
  `sorry`-free.
* **Build and axioms.** `HPC.Plane.Theorem9BGen`, `HPC.Plane.Theorem9B` and the root `HPC` build.
  The two new files contain no `sorry`. `Axioms95.lean` writes `axioms-batch95.txt`. Every
  batch-95 result uses only `propext`, `Classical.choice`, `Quot.sound`; `theorem9_1951`
  (batch 93) is listed there with its `sorryAx` for the record.

**Files.**

| File | Contents |
| --- | --- |
| `HPC/Plane/Theorem9BGen.lean` | General facts about end elements of a `BingS` space (below). |
| `HPC/Plane/Theorem9B.lean` | The skeleton, all items proved, and the descent steps G1, G2. |
| `Axioms95.lean`, `axioms-batch95.txt` | `#print axioms` for the batch-95 results. |

**Shape changes (recorded in the docstrings).**
1. `endElt_contains_endElt_sub` (QB): the hypotheses `hnd : S'.Nontrivial` and
   `hne : bingElt r ≠ S'` are unused and are dropped.
2. No other statement is changed.

## General facts (`Theorem9BGen.lean`)

Throughout, `S` satisfies `BingS`, and "element" means `bingElt` computed in the space in question.

* **`isContinuum_side` (Nadler 6.3, closed form).** Let `C` be closed and connected, and let `Cᶜ`
  be covered by disjoint open `U`, `V`, both meeting `Cᶜ`. Then `(Cᶜ ∩ U) ∪ C` is a continuum, and
  its complement is `Cᶜ ∩ V`. This is batch 94's `isConnected_union_of_separation` with the
  separation built from `U`, `V`.
* **`endElt_no_two_paths`.** Let `g_r`, `g_a`, `g_b` be distinct elements with `g_r` an end element.
  There cannot be both
  * a connected set that misses `g_a` and meets `g_r` and `g_b`, and
  * a connected set that misses `g_b` and meets `g_r` and `g_a`.

  Proof: by Theorem 8 (a) one of the three elements separates the other two. `g_r` does not, since
  it is an end element. Each of the two connected sets rules out one of the other two cases.
* **`at_most_two_endElts`.** Three distinct end elements would contradict Theorem 8 (a).
* **`irred_disjoint`, `irred_isEndElt`, `irred_meets_endElt`.** Suppose `S` is irreducible from a
  proper subcontinuum `A` to a point `x`. Then:
  1. `A` misses `g_x`. Otherwise `A ∪ g_x = S`, so the nonempty open set `S ∖ A` lies in `g_x`,
     which has empty interior.
  2. `g_x` is an end element. If `g_x` separated `g_q` from `g_{q'}`, then the connected set `A`
     would lie on one side, say the side of `g_q`. That side together with `g_x` is a continuum
     (6.3) containing `A` and `x` but not `q'`.
  3. `A` meets every end element `g_f ≠ g_x`. If `A ∩ g_f = ∅`, take `a ∈ A`. Then `g_a` separates
     `g_f` from `g_x` (Theorem 8 (a); both are end elements). The `g_x`-side of `g_a`, together
     with `g_a` and `A`, is a continuum containing `A` and `x` and missing `f`.
* **`endElt_inter_contains_endElt` (QB, general form).** See QB below.
* **Transport.**
  * `bingElt_homeo` and `isEndElt_homeo`: homeomorphisms carry elements to elements and end
    elements to end elements.
  * `nestHomeo`: for `h ⊆ W`, the subtype of `W` cut out by `h` is homeomorphic to `h`.
  * `endElt_nested`: QB for a subcontinuum `h` of a subcontinuum `W`, with the answer stated in
    terms of the elements of `h` itself.
* **`bingElt_nested_subset`.** For continua `h ⊆ W`, the element of `y` computed in `h` lies in the
  element of `y` computed in `W`. This is the batch-94 inclusion one level down, proved directly by
  the same unicoherence argument.
* **`irredFromSet_iff`.** Batch 93's `IrredFromSet W A p` is the same as irreducibility of the
  space `W` from `A` to `p`.

## QA (`elt_between_subset`): proved

Write `g = bingElt r`, and let `e''` separate `e` from `e'` in `S'`.
1. If some point `z` of `e''` lies in `g`, then `e''` is the element of `z` in `S'`. That element
   lies in the element of `z` in `S`, which is `g` (batch 94). So `e'' ⊆ g`.
2. Otherwise `e''` misses `g`. Now `g ∩ S'` is a continuum (property 1), it misses `e''`, and it
   meets both `e` and `e'`. So `e''` does not separate them (`not_separates_of_preconnected`), a
   contradiction.

## QB (`endElt_contains_endElt_sub`): proved

**Statement proved** (`endElt_inter_contains_endElt`): if an end element `g` of `S` meets a
subcontinuum `Y`, then `g` contains an end element of `Y`. QB is the case `g ⊆ Y`.

**Argument.**
* If `Y` is a point, its only element is an end element, vacuously.
* Otherwise `Y` satisfies `BingS` (batch 94). As in QA, every element of `Y` through a point of `g`
  lies in `g`.
* Suppose no end element of `Y` lies in `g`. Take the two end elements `e₁`, `e₂` of `Y` (batch 94).
  Neither meets `g`.
* Take `y₀ ∈ g ∩ Y` and its element `e` in `Y`. Then `e ⊆ g`, so `e` is neither `e₁` nor `e₂`. By
  Theorem 8 (a) for `Y`, `e` separates `e₁` from `e₂` in `Y`: there are disjoint open sets `U ⊇ e₁`
  and `V ⊇ e₂` covering `Y ∖ e`.
* Put `C = g ∩ Y`, which is connected (property 1). Then `Y ∖ C ⊆ Y ∖ e ⊆ U ∪ V`. By 6.3,
  `T₁ = (V ∖ C) ∪ C` and `T₂ = (U ∖ C) ∪ C` are connected.
* Take `a ∈ e₁` and `b ∈ e₂`, and let `g_a`, `g_b` be their elements **in `S`**.
  * `g_a ∩ Y` is connected (property 1). It misses `C`, since `a ∉ g` and elements of `S` are
    disjoint. It lies in `U ∪ V` and contains `a ∈ U`, so it lies in `U`. Hence `T₁` misses `g_a`.
  * Symmetrically, `T₂` misses `g_b`.
  * This also shows `g_a ≠ g_b`, and both differ from `g`.
* In `S`, `T₁` meets `g` and `g_b`, and `T₂` meets `g` and `g_a`. Since `g` is an end element of
  `S`, this contradicts `endElt_no_two_paths`.

**Remarks.**
* The commission's route went through the interval structure (QA) and a separation of `S' ∖ g`
  justified from Theorem 8 (a). The proof above separates by the single element `e` of `S'` rather
  than by `g`, which makes the two sides immediate.
* `S ∖ g` connected is replaced by its consequence for elements: an end element separates no two
  elements.
* Atriodicity enters only through Theorem 8 (a).

## QC (`endElt_mem_bingH'`, Q1): proved, unconditionally

Let `S' ⊋ g`. Then `S'` is nondegenerate. QB gives an end element `e ⊆ g` of `S'`. Let `e'` be an end
element of `S'` distinct from `e` (two exist by batch 94). For `p ∈ e'`, a subcontinuum `K ⊆ S'`
containing `g ∪ {p}` meets both `e` and `e'`, so `K = S'` by Theorem 8 (c) for `S'`
(`bingElt_irreducible`). Together with `g ≠ S` (`bingElt_ne_univ`), this gives `g ∈ H`.

## Q3′ (`endElt_of_bingH_mem_bingH`): proved

Let `h ∈ H` be nondegenerate. Then `h` satisfies `BingS`, and it has exactly two end elements `e₁`,
`e₂` (batch 94 and `at_most_two_endElts`). Call an element `e` of `h` *good for* `W` if `W` is
irreducible from `e` to some point.

**G1 (`exists_endElt_good`).** If `W ⊋ h`, then some end element of `h` is good for `W`.
* Since `h ∈ H`, `W` is irreducible from `h` to some `x`.
* In the space `W`: `g_x` is an end element of `W` and misses `h`, and `h` meets the other end
  element `F` (the three facts on irreducibility above).
* By QB in nested form (`endElt_nested`), `F ∩ h` contains an end element `e` of `h`.
* A continuum in `W` containing `e` and `x` meets both end elements `F` and `g_x` of `W`, so it is
  `W` (Theorem 8 (c) for `W`). Hence `e` is good for `W`.

**G2 (`good_mono`).** If `h ⊊ W₁ ⊆ W₂` and `e` is good for `W₁`, then `e` is good for `W₂`.
* Take `x`, `F` for `W₂` as in G1, and let `w₀ ∈ h ∩ F`.
* If `e` lies in `F`, then `e` is good for `W₂` with the point `x`, as in G1.
* Otherwise let `m` be the element of `W₂` containing `e` (`bingElt_nested_subset`). It is neither
  `F` (by assumption) nor `g_x` (which misses `h`). So `m` separates `F` from `g_x` in `W₂`, with
  open sides `U ⊇ F` and `V ∋ x`.
* `K = (V ∖ m) ∪ m` is a continuum (6.3) containing `x`. The continuum `K ∪ h` contains `h` and `x`,
  so it is `W₂`. Hence `U ∖ m ⊆ h`.
* Let `W₁` be irreducible from `e` to `p₁`.
  * If `p₁ ∈ K`, then `W₁ ∩ K` is a continuum (property 1) containing `e` and `p₁`. So it is
    `W₁`, and `h ⊆ K`. But `w₀ ∈ h` lies in `U ∖ m`, which misses `K`.
  * If `p₁ ∉ K`, then `p₁ ∈ U ∖ m ⊆ h`. So `h` contains `e` and `p₁`, which forces `h = W₁`.
  * Both cases are contradictions.

**Intersection (`bingH_inter_super`).** If `W₁, W₂ ⊋ h`, then `W₁ ∩ W₂` is a continuum and
`W₁ ∩ W₂ ⊋ h`. Suppose `W₁ ∩ W₂ = h`. Then `W₁ ∪ W₂ ⊋ h` is irreducible from `h` to some `z`. If
`z ∈ W₁`, then `W₁ = W₁ ∪ W₂`, so `W₂ ⊆ W₁`, which gives `W₂ = W₁ ∩ W₂ = h`, a contradiction. The case
`z ∈ W₂` is symmetric.

**Choice of `e`.** One of `e₁`, `e₂` is good for every `W ⊋ h`. Otherwise `e₁` fails for some `W₁`
and `e₂` fails for some `W₂`. Then `W₃ = W₁ ∩ W₂ ⊋ h`. G1 gives an end element of `h`, which is `e₁`
or `e₂`, that is good for `W₃`. G2 then makes it good for both `W₁` and `W₂`, a contradiction.

**`e ∈ H`.** Clearly `e` is a continuum and `e ≠ S`. Let `S'' ⊋ e`.
* **`S'' ⊆ h`.** QC for the space `h` (`e` is an end element of `h`) gives a far point, which
  transfers back to `S`.
* **`S'' ⊋ h`.** `e` is good for `S''` by the choice of `e`.
* **Neither.** This case cannot occur. `W = S'' ∪ h ⊋ h` is irreducible from `e` to some `p`.
  * If `p ∈ h`, then `h = W`, so `S'' ⊆ h`.
  * If `p ∈ S''`, then `S'' = W`, so `h ⊆ S''`.

  Both contradict the case assumption.

**On the commission's two cases.**
* The case `S'' ⊉ h` is not answered by passing a far point from `h` to `e`. It is excluded
  altogether once `e` is chosen good for all `W ⊋ h`.
* The real content is the consistency of that choice, which is G2 plus the intersection lemma.
* The far-point transfer from batch 93 is not needed.

## Q3 (`bingH_irreducible_singleton'`): proved

Let `h` be a minimal member of `H`. If `h` were nondegenerate, Q3′ would give a member
`e ⊆ h` with `e ≠ h` (Theorem 8 (b) for `h`: `bingElt_ne_univ`), contradicting minimality. A
degenerate continuum is a point.

## Assembly (`theorem9_1951'`): Theorem 9 unconditional

`theorem9_1951' := theorem9_1951_of_steps hS endElt_mem_bingH' bingH_irreducible_singleton'`.
It uses only the standard axioms.

**Status of `theorem9_1951` (batch 93) after this batch.** It is unchanged and still depends on the
two batch-93 `sorry`s, for the import-order reason above. It could be closed by moving
`theorem9_1951`, `endElt_mem_bingH` and `bingH_irreducible_singleton` out of `Atriodic51B.lean`
into a file that imports `Theorem9B.lean`. That would edit an existing file beyond what the
commission permits, so it was not done.

## Not attempted

As instructed: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
`theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`.

## Next

For Theorem 11, the following are now available:
* the two end elements and their properties under irreducibility (`irred_*`);
* QB for subcontinua meeting an end element;
* transport of elements along homeomorphisms and nested subcontinua (`bingElt_homeo`,
  `endElt_nested`), which is what applying Theorem 9 to a nondegenerate element `g'` as a space
  requires;
* Theorem 9 itself, for any `BingS` space, so in particular for a nondegenerate element by
  batch 94's `bingS_subcontinuum`.

The order on `G` ("infinitely many … separate `g'` from `g₁`") is still not built as an order.
