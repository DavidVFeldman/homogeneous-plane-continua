Commission read: `COMMISSION-batch92.md` (batch 92 — Bing 1951, *Snake-like continua*, §4 part one: the six properties and Theorem 8), with its skeleton `Atriodic51.lean`, saved as `HPC/Plane/Atriodic51.lean`; `import HPC.Plane.Atriodic51` is added at the end of `HPC.lean`.

# Report, batch 92

## Summary

* **Counterexample, proved in Lean.** `theorem8_1951` is **false as stated**, and so is
  `isArc_of_separatesPairs`. There is a planar continuum `S₀` that satisfies Bing's standing
  hypothesis (`bingS_S₀`, proved), yet Bing's sets `g p` do not partition it:
  `q ∈ g p` but `g p ≠ g q`. Its decomposition space is not Hausdorff. See §1.
  * `Counter92.theorem8_1951_false` proves the negation of the skeleton's statement, with the
    conclusion copied verbatim.
  * `Counter92.isArc_of_separatesPairs_false` does the same for `isArc_of_separatesPairs`.
* **Properties 1–6: all proved**, in the skeleton's shapes (§2).
* **Theorem 8: every clause except the partition clause follows from the partition clause.**
  This is `theorem8_1951_of_partition`, proved; it covers u.s.c., (a), (b) and (c). The partition
  clause itself is the false one. Bing's proof of it fails at one identifiable sentence (§3.2).
* No `sorry` in the batch-92 files. The two false skeleton statements are kept, commented out
  with the reason, in `HPC/Plane/Atriodic51.lean`.
* `lake build HPC` passes. The `sorry` warnings in the build are the parked items only.
* Axioms (`Axioms92.lean` → `axioms-batch92.txt`): every batch-92 result depends only on
  `propext`, `Classical.choice` and `Quot.sound`.

**Files.**

| File | Contents |
| --- | --- |
| `HPC/Plane/Atriodic51Defs.lean` | the skeleton's definitions, unchanged, plus general topology |
| `HPC/Plane/Atriodic51Props.lean` | properties 1–6 |
| `HPC/Plane/Atriodic51.lean` | `gElt` and Theorem 8 (the skeleton's file) |
| `HPC/Plane/Atriodic51Counter.lean` | `S₀`; `q ∈ g p`, `g p ≠ g q` |
| `HPC/Plane/Atriodic51CounterBing.lean` | `BingS S₀`; `theorem8_1951_false` |
| `HPC/Plane/Atriodic51CounterArc.lean` | `g` on the left half-bar; quotient not T2; `isArc_of_separatesPairs_false` |

The skeleton was split into the first three files. The project's files do not use the `module`
keyword, so the new files do not either.

**Shape changes.**
* `theorem8_1951`:
  * As uploaded, it did not elaborate: in the binders `∀ p, …` the type of `p` could not be
    inferred (typeclass problem `MetricSpace ?m` stuck). The working copy annotated `p : S`, and
    likewise `q`, `r`, `s`, `q'`.
  * It is false, so it is now commented out. `theorem8_1951_false` restates its conclusion
    verbatim, for every `S : Type` (universe 0, which contains the counterexample).
* `isArc_of_separatesPairs`: false; commented out. `isArc_of_separatesPairs_false` restates it.
* All other skeleton statements are unchanged.

## 1. Counterexamples

### 1.1 The continuum `S₀`

Let `c(t) = (1 + sin(1/t))/2 ∈ [0,1]`. Then `S₀ ⊆ ℝ × ℝ` is the union of three pieces:

* `C₁ = {(c(t), t) : 0 < t ≤ 1}`, a sine curve above the axis. Its limit set is `[0,1] × {0}`.
* `B = [0,2] × {0}`, the bar.
* `C₂ = {(1 + c(t), −t) : 0 < t ≤ 1}`, a sine curve below the axis. Its limit set is
  `[1,2] × {0}`.

Put `p = (1/2, 0)`, `q = (1, 0)` and `x = (3/2, 0)`.

* **`x ∉ g p`.** `closure C₁ = C₁ ∪ [0,1] × {0}` is a continuum, it contains `p` interiorly, and
  it misses `x` (`x₀_not_mem_gElt_p₀`).
* **`q ∈ g p`.** Let `Z` be a continuum containing `p` interiorly. Then `Z` contains a point of
  `C₁` at some height `t₁`. Height is continuous and `Z` is connected, so `Z` contains a point at
  every height in `(0, t₁]`. A point of `S₀` at nonzero height is unique, so `Z` contains the whole
  tail of `C₁` below `t₁`, and its closure contains `q` (`q₀_mem_gElt_p₀`).
* **`x ∈ g q`.** The same argument with the tail of `C₂` (`x₀_mem_gElt_q₀`).

So `q ∈ g p` and `g p ≠ g q` (`gElt_not_partition_S₀`). This is the third conjunct of the
conclusion of `theorem8_1951`.

In fact `g b = [0,1] × {0}` for every bar point `b = (s, 0)` with `0 ≤ s < 1` (`gElt_bar`), while
`g q ⊇ [0,2] × {0}`.

### 1.2 `S₀` satisfies `BingS` (`bingS_S₀`)

It is compact (closed and bounded), connected and nondegenerate. The proof of the three hereditary
properties rests on one closure property `Crit W` of subsets `W ⊆ S₀`:

1. every point at a nonzero height lying between two heights of `W` is in `W`;
2. if `W` has heights `≤ 0` and `≥ 0`, it meets `B`;
3. `W ∩ B` is convex;
4. if `W` has a height `≤ 0` and one `> 0`, then `W ⊇ [0,1] × {0}`; if it has a height `≥ 0` and
   one `< 0`, then `W ⊇ [1,2] × {0}`.

Three facts about `Crit`:

* every closed connected `W` has it (`crit_of`; for item 4, the tail argument of §1.1);
* it is closed under intersection (`Crit.inter`);
* every set with it is connected (`Crit.isPreconnected`). The proof joins any two points by an
  arc of a curve, a segment of the bar, or a curve tail together with the part of the bar it
  accumulates on.

The three hereditary properties then follow.

* **Hereditarily unicoherent.** If `H ∪ L = K` with `H`, `L` subcontinua, then `H ∩ L` is
  nonempty and has `Crit`, so it is connected.
* **Hereditarily decomposable.** Cut a nondegenerate subcontinuum at a middle height, or, if it
  lies in the bar, at a middle abscissa. Both halves have `Crit` and are proper subcontinua.
* **Atriodic** (`not_isTriod`). Suppose `T ∖ N = A ∪ B ∪ C` with the pieces mutually separated.
  * Each `N ∪ A`, `N ∪ B`, `N ∪ C` is a continuum (`union_piece`), so each has `Crit`.
  * A point outside `N` is of one of four kinds: above every height of `N`, below every height of
    `N`, on the bar left of `N ∩ B`, or on the bar right of `N ∩ B` (`kind`).
  * Points of two different pieces cannot have the same kind. Nor can one be "above" and the other
    "left", or one "below" and the other "right". In each case `Crit` forces a point outside `N`
    into both pieces (`no_pair`).
  * With three pieces and these exclusions, a pigeonhole argument gives a contradiction.

Informally, `S₀` is also snake-like (chainable). By Bing's own Theorem 11 that already implies
`BingS`, but the Lean proof does not use it.

### 1.3 The decomposition space is not an arc (`quotient_not_t2`)

In the quotient of `S₀` by `p ~ q ⇔ g p = g q`, take the classes of `p` and `q`. Every
neighbourhood of `q` contains bar points `(s, 0)` with `s < 1`, and these lie in the class of `p`.
So the two classes have no disjoint neighbourhoods. The quotient is not Hausdorff, hence not
homeomorphic to `[0,1]`.

### 1.4 What the counterexample says about Bing's text

* **Theorem 8 itself is not refuted.** Its statement is "there is an u.s.c. collection `G` …".
  For `S₀`, the collection of the points of `C₁ ∪ C₂` together with the bar `B` does the job
  (checked informally, not in Lean).
* **What is refuted is Bing's choice** `G = {g_p}`, which the skeleton hard-codes, together with
  the step of his proof that claims these sets partition `S`.
* A correct `G` presumably needs a coarser element, for instance the layers of the irreducible
  continuum `S`. That is not attempted here; it is the natural next item for Theorem 8.

## 2. Properties 1–6 (all proved, `HPC/Plane/Atriodic51Props.lean`)

**Property 1** (`prop1_inter_continuum`). The statement keeps the hypothesis, added in the
skeleton, that the intersection is nonempty.
* For two continua: apply unicoherence of `H ∪ K` (`BingS.inter_two`).
* Finite intersections: by induction.
* Arbitrary families: compactness. A decomposition of the intersection into two disjoint closed
  sets would separate some finite subintersection.

**Property 2** (`prop2_components`). Bing writes only "follows from atriodicity". With `M = S` and
`N = H`, the statement is literally the definition of a triod. The skeleton states the claim
"`S − H` has at most two components" as "`S − H` is not the union of three nonempty mutually
separated sets", and in that form nothing is left to prove.
* *Second clause* ("`S − (H + K)` has at most three components"). This is not formalized.
  * When `H ∩ K ≠ ∅` it is the first clause applied to `H ∪ K`.
  * When `H ∩ K = ∅`, `H + K` is not a continuum, and the commission's question is what is true.
  * It is never needed. Property 5 works with the region `C = Xᶜ ∩ Yᶜ` between two "filled"
    continua (§2, property 5), not with the components of `S − (H₁ + H₂)`.
* From property 2 the build also derives that the components of `S − H` are open
  (`BingS.isOpen_component_compl`), which property 6 needs.

**Property 3** (`prop3_one_in_union`). As Bing argues:
* the three continua have a common point (unicoherence of `H₁ ∪ H₂ ∪ H₃`);
* `H₀` is connected (property 1);
* the last step, which the commission flagged, holds: if every `H_i ⊄ H_j ∪ H_k`, then the three
  sets `H_i ∖ (H_j ∪ H_k)` are nonempty, pairwise disjoint and open in `H₁ ∪ H₂ ∪ H₃`. Together
  with `N = H₀` they form a triod.

**Property 4** (`prop4_separates`). Bing does not say how to obtain his `K_i`; the construction is
supplied. If `H_j` does not separate `H_i` from `H_k`, then some continuum meets both and avoids
the interior of `H_j` (`connector_of_not_separates`). It is a component of
`S ∖ (int H_j ∪ int H_k)`, or else a clopen splitting shows that `H_j` separates. Bing's `K_i` is
`H_i` together with two such connectors, and property 3 is violated by `K₁`, `K₂`, `K₃`, exactly
as Bing says.

**Property 5** (`prop5_exists_separating`).
* *Bing's `C`.* Existence of "the component with limit points on both" needs an argument. It is
  replaced by the region `C = Xᶜ ∩ Yᶜ`, where `X ⊇ H₁` and `Y ⊇ H₂` are the continua obtained by
  adding the far sides (`BingS.fill`). `C` is open and connected by unicoherence
  (`BingS.compl_inter_preconnected`), and `C̄` meets both `X` and `Y` (`BingS.exists_between`).
* *The three continua `K₁, K₂, K₃`.* Each must have an interior point in neither of the others;
  the text does not show they exist. They come from a decomposition `A ∪ B` of `C̄` and a
  decomposition of a Zorn-minimal `B' ⊆ B` with `A ∪ B' = C̄` (`prop5_core`).
* *Bing's case analysis.* His list "`H₁ + K₁ + K₂`, `H₂ + K₁ + K₂`, `C̄`" does not match his own
  hypotheses (`H₂` meets `K₂` and `K₃`). The working version is: no subcontinuum of `C̄` meets both
  `H₁` and `H₂` (`no_crossing`, from property 3). So one `K_i` misses `H₁ ∪ H₂` and separates them
  by property 4.

**Property 6** (`prop6_between`). Bing's three cases, with one gap filled. "`H(C)` = `K` plus the
component of `S − K` containing `H₂`" needs that component to be open; this is the openness
consequence of property 2. The intersection `H(C₁) · H(C₂)` is a continuum by property 1
(`BingS.side_continuum`, `BingS.split_piece_preconnected`).

## 3. Theorem 8

### 3.1 The elements (`gElt`, `HPC/Plane/Atriodic51.lean`)

* `g p` is a continuum (`gElt_isContinuum`): the family of continua containing `p` interiorly is
  nonempty (`S` itself) and closed under finite intersections; then apply property 1.
* Compactness gives a neighbourhood form (`BingS.exists_nbhd_subset`): every open `U ⊇ g p`
  contains a continuum that contains `p` interiorly.

### 3.2 "`g_p` contains `q` ⇒ `g_p = g_q`" — false (§1)

Bing's proof begins: "there is a continuum `H₁` in `S − p'` which contains interiorly a continuum
`H₂` which contains `q` interiorly".

* As written, this cannot hold. If `p' ∈ g_q`, every continuum containing `q` interiorly contains
  `p'`. The roles must be `p` in place of `q`.
* With that correction, the claim needs an `H₂` with `p ∈ int H₂` and `H₂ ⊆ int H₁`, where
  `p' ∉ H₁`. In `S₀`, with `p = (1/2,0)` and `p' = (3/2,0)`, no such pair exists. Every continuum
  `H₂` containing `p` interiorly contains `q = (1,0)`. A continuum `H₁` containing such an `H₂`
  interiorly then contains `q` interiorly, so it contains `[1,2] × {0}` and therefore `p'`.
* Property 6 cannot repair this. It needs `H₂ ⊆ int H₁` to begin with, and that is exactly what
  fails.
* The rest of Bing's paragraph (the `K_i` as closures of components containing `p`) is therefore
  never reached.

### 3.3 Everything else follows from the partition clause (`theorem8_1951_of_partition`)

These are proved in a section with the hypothesis `∀ p q, q ∈ g p → g p = g q`.

* **Disjointness** (`gElt_disjoint`): immediate from the hypothesis.
* **Upper semicontinuity** (`gElt_usc`). For `x` in an element inside `U`: `g x ⊆ U`, so some
  continuum `H` with `x ∈ int H` lies in `U` (§3.1). Every element through a point of `int H` lies
  in `H`, which gives openness. This replaces Bing's limit-superior sentence; the batch-81
  `limSup` machinery is not needed.
* **(a)** (`gElt_separates_triple`).
  * Three distinct elements are disjoint compact sets. Pick pairwise disjoint continua containing
    them interiorly (§3.1), and apply property 4 to these.
  * Then pass from the separating neighbourhood continuum down to the element. This is
    `gElt_separates_of`: if `H₁ ∋ p` interiorly separates two continua with interior, then so does
    every smaller such continuum (property 4 and the side continua, `BingS.side_of_separates`),
    hence so does their intersection `g p`.
  * This step is what Bing's "using conditions (2) and (4)" leaves out. It does not need the
    partition clause.
* **(b)** (`gElt_interior_eq_empty`).
  * Bing: `g` is the sum of three continua, each with a private interior point; one pair is
    disjoint by property 3. This is proved as `BingS.two_disjoint_with_interior` (decompose a
    minimal continuum containing the open set, then decompose a minimal piece again).
  * Then property 5 and a side continuum show that the two pieces lie in different elements.
  * Property 6, which Bing also cites here, is not needed.
* **(c)** (`gElt_irreducible`). The commission's route through "`G` is uncountable" is not needed.
  * Let `M ≠ S` be a continuum meeting two different end elements `g_r`, `g_s`.
  * By (b), `S ∖ M` is a nonempty open set that meets three different elements.
  * An element disjoint from `M` would, by (a), be separated by `g_r` or `g_s` from another
    element, contradicting the end property.
  * Otherwise all three meet `M`, and `M` together with them is a triod.

### 3.4 "Arc with respect to its elements" (`isArc_of_separatesPairs`)

False in general (§1.3).

* Under the partition clause, (a) gives the separation form that the skeleton uses.
* The arc characterization via non-cut points (Nadler 6.16–6.17) is not in Mathlib and was not
  attempted. With the partition clause refuted for `gElt`, it has to wait for a corrected `G`.

### 3.5 Implicit hypotheses (commission §3.8)

* The ones the skeleton states are the ones used: compactness, nondegeneracy, and `S` as the
  whole space.
* Property 1 needs a nonempty intersection.
* For `G = {g_p}`, any extra hypothesis that rescued the partition clause would have to exclude
  `S₀`, a planar, hereditarily decomposable continuum which (informally) is arc-like.

## 4. Not attempted

The parked items: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
`theorem10_1951`, and `exists_tame_chain_near`. They are unchanged.

## 5. Next

* A corrected Theorem 8 with a coarser `G` (layers of `S`). With it, (a)–(c) should transfer
  through `theorem8_1951_of_partition`-style arguments.
* Then Theorems 9 and 11, as the commission plans.
