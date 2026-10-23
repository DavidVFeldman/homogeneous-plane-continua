Commission read: `COMMISSION-batch93.md` (batch 93: Theorem 8 (Duke 1951) with Bing's own elements; Theorem 9), with its skeleton `Atriodic51B.lean`, saved as `HPC/Plane/Atriodic51B.lean`; `import HPC.Plane.Atriodic51B` is added at the end of `HPC.lean`.

# Report, batch 93

## Summary

* **No refutations this batch.** With Bing's two-layer definition (`bingElt`), Theorem 8 holds
  exactly as stated: `theorem8_1951'` is proved with all seven clauses. On the batch-92 continuum
  `S₀` the elements are the curve points and the bar (`Counter92.bingElt_curve`,
  `Counter92.bingElt_bar`, both proved). The batch-92 counterexample is answered.
* `gElt_subset_bingElt` is proved.
* **Theorem 9.**
  * Q2 (`bingH_iInter`, inductiveness): **proved**.
  * Q1 (`endElt_mem_bingH`) and Q3 (`bingH_irreducible_singleton`): **open**, obstructions in
    §3.
  * Q4: `theorem9_1951_of_steps` proves Theorem 9 with Q1 and Q3 as hypotheses. It uses the
    Brouwer reduction (`exists_minimal_of_seq`, proved) and `condA_of_bingH_singleton` (proved).
    `theorem9_1951` is derived from it and still depends on the two open steps.
  * Also proved: Q3 is equivalent to "every member of `H` contains a condition-A point"
    (`bingH_step3_iff`).
* **Item 4.** The ledger note is prepended to `HPC/Plane/Atriodic51Counter.lean`.
* **Build and axioms.** `lake build HPC` passes. In the batch-93 files the only `sorry`s are the
  bodies of `endElt_mem_bingH` and `bingH_irreducible_singleton`. `Axioms93.lean` writes
  `axioms-batch93.txt`:
  * every proved batch-93 result uses only `propext`, `Classical.choice`, `Quot.sound`;
  * `endElt_mem_bingH`, `bingH_irreducible_singleton` and `theorem9_1951` also show `sorryAx`.

**Files.**

| File | Contents |
| --- | --- |
| `HPC/Plane/Atriodic51BElt.lean` | `ContainsNested`, `bingElt` (moved from the skeleton, unchanged), `gElt_subset_bingElt`; the partition and the other clauses of Theorem 8 |
| `HPC/Plane/Atriodic51BNine.lean` | the Brouwer reduction (`exists_antitone_of_chain`, `exists_minimal_of_seq`) |
| `HPC/Plane/Atriodic51BCounter.lean` | windows of `S₀`, `barR_subset_of_interior` |
| `HPC/Plane/Atriodic51B.lean` | the skeleton: `theorem8_1951'`, `Counter92.bingElt_bar`, `bingElt_curve`, Theorem 9 |

**Shape changes.**
* `ContainsNested`, `bingElt` and `gElt_subset_bingElt` are moved into
  `HPC/Plane/Atriodic51BElt.lean`, statements unchanged. The supporting files need them, and the
  skeleton imports that file.
* `IsEndElt` loses its unused argument `hS : BingS S`, so `IsEndElt hS r` becomes `IsEndElt r` in
  the statements of `endElt_mem_bingH` and `theorem9_1951`.
* `condA_of_bingH_singleton` loses its unused hypothesis `hS`.
* New:
  * `theorem9_1951_of_steps`, the conditional form required by §2 Q4;
  * `bingH_singleton_of_condA`, the converse of `condA_of_bingH_singleton`;
  * `bingH_step3_iff`.
* `bingH_iInter` keeps Bing's sequence form. The chains needed by Zorn are reduced to sequences
  separately, in `exists_antitone_of_chain`.

## 1. Item 1: Theorem 8 with `bingElt`

### 1.1 Continuum, membership, neighbourhood form

* The family defining `bingElt p` contains `S`, which contains itself interiorly and contains `p`
  interiorly.
* It is closed under finite intersections (`BingS.nested_inter`). `H₁ ∩ H₂` and `H₁' ∩ H₂'` are
  continua by property 1, `H₁' ∩ H₂' ⊆ int H₁ ∩ int H₂ = int (H₁ ∩ H₂)`, and
  `p ∈ int (H₁' ∩ H₂')`.
* Property 1 then gives `bingElt_isContinuum`.
* Compactness gives the neighbourhood form `BingS.exists_nested_subset`: every open `U ⊇ bingElt p`
  contains a continuum `H` with `ContainsNested H p`.

### 1.2 Partition: the two flags

The core is `not_mem_bingElt_of`: if `H₂ ⊆ int H₄` are continua, `q ∈ int H₂` and `p ∉ H₄`, then
`q ∉ bingElt p`. Let `C_i` be the component of `S − H_i` through `p`. It is open by batch 92's
`isOpen_component_compl`. Then:

* **Flag 1 (`K₄ ⊆ int K₂`): Bing's `K_i` work as stated, and the gap closes with something stronger,
  `cl C₄ ⊆ C₂`.**
  * Let `y ∈ cl C₄`. First, `y ∉ H₂`: the open set `int H₄ ⊇ H₂` misses `C₄ ⊆ S − H₄`, so it
    contains no point of `cl C₄`.
  * Second, the component of `S − H₂` through `y` is open, contains `y`, and `y ∈ cl C₂`. So it
    meets `C₂`, hence equals `C₂`, and `y ∈ C₂`.
  * Since `C₂` is open, `K₄ = cl C₄ ⊆ C₂ ⊆ int K₂`.
  * Nothing about `H₃ ∖ H₂` is needed, so no fifth continuum is used. The commission's candidate
    `H₃ ∖ H₂ ⊆ C₂` is not used either.
* **`K₂ ∌ q`.** `int H₂` is an open set containing `q` and disjoint from `C₂`, so `q ∉ cl C₂`.
* So `K₂ = cl C₂` is a continuum that contains `K₄ = cl C₄` interiorly. `K₄` contains `p`
  interiorly, since `p ∈ C₄`, which is open. This gives `bingElt p ⊆ K₂ ∌ q`.

`bingElt_mem_imp` then proves, for `q ∈ g_p`:
* **`p ∈ g_q`.** If not, unpacking gives `H₁ ∌ p` with `H₂ ⊆ int H₁` and `q ∈ int H₂`.
  `not_mem_bingElt_of` with `H₄ := H₁` gives `q ∉ g_p`. Property 6 is not needed here.
* **`g_p ⊆ g_q`.** This is Bing's paragraph. For `p' ∈ g_p ∖ g_q`, property 6 applied twice gives
  `H₁ ⊇ int H₃ ⊇ H₃ ⊇ int H₄ ⊇ H₄ ⊇ int H₂ ⊇ H₂`.
  * If `p ∈ H₄`, then `H₁` contains interiorly `H₃`, which contains `p` interiorly. So
    `g_p ⊆ H₁ ∌ p'`.
  * Otherwise `not_mem_bingElt_of` gives `q ∉ g_p`.
* **Flag 2 (Bing's "similarly").** The reverse inclusion `g_q ⊆ g_p` is the inclusion above with
  `p` and `q` exchanged. Its hypothesis is now `p ∈ g_q`, which is the first bullet. So the same
  argument applies, and the order matters: `p ∈ g_q` has to be proved first.

`bingElt_partition` combines the two.

### 1.3 Upper semicontinuity, (a), (b), (c): which lemmas needed more than a renaming

* **Upper semicontinuity** (`bingElt_usc`): the open set around `x` is now `int H'` for the inner
  continuum `H'`, not `int H`. That is a one-line change.
* **(b)** (`bingElt_interior_eq_empty`): the batch-92 argument goes through. The side continuum `Z`
  contains `K₁` interiorly, and `K₁` contains `x₁` interiorly. That is exactly the two layers, so
  `bingElt x₁ ⊆ Z`.
* **(a)** (`bingElt_separates_triple`): this needed a new lemma, `separates_enlarge`. If `A`
  separates `B` from `C` and `A ⊆ A'` with `A'` closed and disjoint from `B` and `C`, then `A'`
  separates `B` from `C`.
  * Batch 92's `gElt_separates_of` is reused unchanged. It gives separation by `gElt p`, and since
    `gElt p ⊆ bingElt p ⊆ H₁` this enlarges to separation by `bingElt p`
    (`bingElt_separates_of`).
* **(c)** (`bingElt_irreducible`): a renaming only.
* `two_disjoint_with_interior`, property 4 and property 5 are reused as they are.

### 1.4 Item 5: the elements on `S₀`

* **`Counter92.bingElt_bar`**: every bar point `b` has `bingElt b = [0,2] × {0}`.
  * `⊆`: for `ε > 0`, the window `{|y| ≤ ε}` contains interiorly the window `{|y| ≤ ε/2}`, which
    contains `b` interiorly. Both are continua by batch 92's closure property `Crit`.
  * `⊇`: the inner continuum `H'` contains a half-bar, by batch 92's `barL_subset_of_interior` or
    its new mirror `barR_subset_of_interior`. So `(1, 0) ∈ H' ⊆ int H`, and the other half-bar lies
    in `H`.
* **`Counter92.bingElt_curve`**: a curve point `c` has `bingElt c = {c}`. For `z ≠ c`, `z` has a
  different height, and a thin window around the height of `c` misses `z`. The windows replace the
  "closed arc neighbourhood" of the commission.

## 2. Item 3 (arc): not set up

The separation order on `G` was not built in reusable form. The proof of (a) goes through
property 4 and `gElt_separates_of` and does not produce an order.

## 3. Theorem 9

### Q1 (`endElt_mem_bingH`): open

**What makes it hard.** The irreducibility point sometimes has to lie inside an element that `S'`
contains only in part. In `S₀`:
* `g = {e₁}` is an end element, where `e₁` is the free end of the upper curve `C₁`.
* Let `S' = cl C₁ ∪ [1, 3/2] × {0}`.
* A subcontinuum containing `e₁` and a bar point `(x, 0)` contains all of `C₁`, hence
  `[0,1] × {0}`, hence `[0, x] × {0}`.
* So `S'` is irreducible from `g` to `p` only for `p = (3/2, 0)`. That point lies in the last
  element met (the bar), and `S'` contains only `[0, 3/2] × {0}` of it.

So "take a point in the farthest element" does not work: `p` must be a terminal point of the part
of the last element that lies in `S'`. That is a relative form of Theorem 9 itself.

**Two routes that would close it** (neither is available yet):
1. **Through Theorem 8 applied to `S'`.** `S'` again satisfies Bing's hypothesis. Its elements lie
   inside elements of `S`: a continuum containing `x` doubly interiorly in `S`, intersected with
   `S'`, does the same in `S'` (by unicoherence). Two further facts are needed:
   * `S'` has two end elements. This is Moore's non-cut-point theorem for the decomposition space,
     the missing piece of the parked arc item.
   * `g` meets one of those end elements.

   With both, (c) for `S'` gives `S'` irreducible from `g` to any point of the other end element.
2. **Through a layer theorem** (Kuratowski): a subcontinuum meeting both sides of an element
   contains it. That would also make the subcontinua containing an end element nested, which is
   the condition-B-like statement suggested by the commission.

**Facts checked informally** while looking for a proof (not formalized):
* An end element `g` has `S − g` connected.
* A far point transfers from a larger member to a smaller one: if `S'` is irreducible from
  `A ⊊ S'` to `x`, the continuum `B ⊆ A` is nonempty, and `S'` is irreducible from `B` to some
  point, then `S'` is irreducible from `B` to `x`.

With these, Q1 reduces to: `S'` is irreducible from `S' ∩ H` to some point, for the continua `H`
containing `r` doubly interiorly. That reduced statement was not proved.

### Q2 (`bingH_iInter`): proved

Let `h = ⋂ h_n`. It is a continuum (property 1) and proper, since `h ⊆ h₀`. Let `S' ⊋ h`.
1. Some `N` has `S' ⊄ h_N`, hence `S' ⊄ h_m` for all `m ≥ N`. So `S' ∪ h_m ⊋ h_m`, and it is
   irreducible from `h_m` to some `p_m ∉ h_m`.
2. **Key step: the single point `x := p_N` works for every `m ≥ N`.** Let `J ⊆ S' ∪ h_m` be a
   continuum containing `h_m` and `x`.
   * `J ∪ h_N ⊆ S' ∪ h_N` contains `h_N` and `x`, so it equals `S' ∪ h_N`.
   * If `p_m ∉ J`, then `p_m ∈ h_N`. Then the continuum `h_N ∩ (S' ∪ h_m)` contains `h_m` and
     `p_m`, so it equals `S' ∪ h_m`. That puts `x ∈ S' ⊆ h_N`, a contradiction.
   * So `p_m ∈ J`, and `J = S' ∪ h_m`.
3. Now let `K ⊆ S'` be a continuum containing `h` and `x`. For every `m ≥ N`, `K ∪ h_m = S' ∪ h_m`.
   So `S' ⊆ ⋂_m (K ∪ h_m) = K ∪ h = K`.

So the obvious attempt the commission mentions (irreducibility for `S' ∪ h_n` rather than for `S'`)
does work, once one point is fixed for all `n`. The proof keeps the sequence form.

### Q3 (`bingH_irreducible_singleton`): open, reformulated

**Proved reformulation.** `bingH_singleton_of_condA` shows that a condition-A point `p` gives
`{p} ∈ H`. With Q2 and the Brouwer reduction this yields `bingH_step3_iff`: Q3 holds if and only if
every member of `H` contains a point satisfying condition A for `S`. So Q3 is Theorem 9 for every
member of `H`, not just for end elements.

**Why the natural candidates fail.**
* A member need not be an element, so Theorem 8 says nothing about its inside.
* In a decomposition `h = A ∪ B`, neither piece is in `H` in general.
* Minimality with respect to one far point `e` (`S` irreducible from `A` to `e`) is inductive, but
  it selects the wrong sets. In the `sin(1/x)` continuum, take `h` the limit bar and `e` the free
  end of the curve. Every subcontinuum `A` of the bar has `S` irreducible from `A` to `e`. Yet a
  subarc in the middle of the bar is not in `H`, since the bar itself is not irreducible from it.

### Q4 (`theorem9_1951`): conditional form proved

* **Brouwer reduction** (`exists_minimal_of_seq`): for a property of closed sets that passes to
  intersections of decreasing sequences, every member contains a minimal member.
  * A nonempty chain of closed sets has the same intersection as some decreasing sequence of its
    members (`exists_antitone_of_chain`). This uses the Lindelöf property of the compact metric
    space.
* **`theorem9_1951_of_steps`** runs this reduction on `H` inside `bingElt r`. It then applies Q3 to
  the minimal member and `condA_of_bingH_singleton` to the resulting point.
* `theorem9_1951` is this with the two open lemmas filled in, so it depends on them.

## 4. Item 4: the ledger

A `-- Note (batch 93)` block is prepended to the module docstring of
`HPC/Plane/Atriodic51Counter.lean`. It says that the refuted one-layer `gElt` is the batch-92
commission's transcription rather than Bing's definition (p. 658), and that Bing's elements are
`bingElt`, which on `S₀` are the curve points and the bar (`Counter92.bingElt_curve`,
`Counter92.bingElt_bar`). No other existing file is edited, apart from the import line in `HPC.lean`.

## 5. Not attempted

As instructed: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
`theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`.

## 6. Next

Q1 and Q3 both need the global structure of the decomposition: two end elements, or Kuratowski's
layer theorem. The first is the non-cut-point half of the parked arc item. Proving that every space
satisfying Bing's hypothesis has two end elements would be a natural next commission. It would
unblock Q1 through route 1, and it would also be needed for Theorem 11.
