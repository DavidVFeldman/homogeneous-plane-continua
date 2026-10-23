# Commission: batch 85 — Bing 1951, part two: Theorem 10 and the end-point theorems of §5

**Go!** Runs on top of the batch-84 delivery, in the existing workspace. Two files accompany this
commission as separate uploads, not an archive:

* `COMMISSION-batch85.md` — this text (also pasted into the prompt);
* `EndPoints51.lean` — a skeleton of five definitions and seven statements, all `sorry`, all
  work items. Save it as `HPC/Plane/EndPoints51.lean` and add `import HPC.Plane.EndPoints51` at
  the end of the root `HPC.lean`. Nothing else is to be replaced. Shapes may be adjusted with the
  change recorded.

The report names the commission read in its first line.

## 0. On batch 84

Audited: `theorem4`, `exists_description_plane`, `pseudoArc_exists` proved with conclusions
unchanged; the skeleton's planar step refuted (`rectStepSkeleton_false`: a pattern that steps at
every index forces a fine link to bridge a coarse overlap) and replaced by the tame-chain step with
an `N`-slowness hypothesis — Bing's "nine links" clause, with `N` growing with the level; stuttered
Bing patterns for the description; the compact-ambient-space hypotheses of `isContinuum_M` and
`theorem13` removed by restriction (`Transfer.lean`); standard axioms throughout; the only `sorry`s
are the three parked ones. Recorded: Bing's "interiors of rectangles" is not reproduced (the links
are homeomorphic images of rectangles); whether the constant `9` suffices is not determined.

With batch 84 the sentence *the pseudo-arc is a homogeneous, hereditarily indecomposable,
nondegenerate plane continuum* is machine-checked end to end (`Plane.pseudoArc_exists`).

## 1. The rest of the 1951 paper, and what this batch takes from it

* **§3, Theorems 6–7** (tree-like plane continua) use the Jordan curve theorem and the components
  of the complement of a plane continuum. Mathlib has neither. Not in this batch; likely not
  feasible without a large independent development.
* **Theorem 5** rests on Roberts [10]; **Theorem 12, direction B ⇒ A** rests on Theorem 5 of Bing's
  *Some characterizations of arcs and simple closed curves* [4]; **Theorem 16, necessity**, and the
  last step of its sufficiency rest on Theorem 1 of Bing's *Concerning hereditarily indecomposable
  continua* [3]. Those papers are not available to the commission. Not in this batch.
* **§4, Theorems 8, 9, 11** (upper semicontinuous decompositions of atriodic hereditarily
  unicoherent hereditarily decomposable continua) are a separate development in continuum theory.
  Deferred; §4's **Theorem 10** is self-contained and is in this batch.
* **§5** apart from the external steps above: Theorem 12 (A ⇒ B), Theorem 13 (both directions,
  sufficiency through Theorem 10), Theorem 14, Theorem 15, and the self-contained half of
  Theorem 16. In this batch.

## 2. Bing's text (pp. 659–662), transcribed

[Quotation moved to doc/sources/transcriptions/bing51duke.md, §doc/batches/COMMISSION-batch85.md, 2. Bing's text (pp. 659–662) (passage 1); batch 204.]

[Suppose `M'` is a nondegenerate subcontinuum of `M` containing `p`. By Theorem 5 of [4] there is
a point `q` of `M' − p` such that the sum of all continua in `M' − q` containing `p` is dense in
`M'`. Condition B implies condition A because if `p` satisfies condition B, `M'` is irreducible
from `p` to `q`. If `M'` were a proper subcontinuum of `M'` containing `p + q`, there would be a
continuum `K` in `M − q` such that `K` contains `p` but is not a subset of `H`. But neither `H` nor
`K` would contain the other. — External; not in this batch.] ∎

[Quotation moved to doc/sources/transcriptions/bing51duke.md, §doc/batches/COMMISSION-batch85.md, 2. Bing's text (pp. 659–662) (passage 2); batch 204.]

## 3. Facts about the text, and what the skeleton does with them

1. **Chains from `p` to `q`.** Bing's "`d_1 − d_2` contains `p` and `d_n − d_{n−1}` contains `q`" is
   the repository's `Chain.IsFrom p q` (`p` in the first link and in no other: a point of `d_1`
   lies in no `d_j` with `j ≥ 3`). The skeleton uses `IsFrom`.
2. **Condition C** is stated as: `p` lies in the first link and in no other link
   (`IsEndPoint`). Theorem 10's conclusion "`e_1 − ē_2` contains `p`" is stated as `p ∈ e_1` and
   `p ∉ closure e_j` for every `j ≠ 1`; for `j ≥ 3` this follows from `p ∈ e_1` (an open set
   disjoint from `e_j`), so the two forms agree.
3. **Theorem 13, sufficiency.** Bing cites Theorems 10, 11, 12. For condition A the route is
   Theorem 10 alone: an `ε`-chain covering `M` refined to one with `p` in the first link only,
   still an `ε`-chain (`endPoint_of_condA`). For condition B the route is B ⇒ A (Theorem 12,
   external) and then the same. The skeleton states `endPoint_of_condA` and
   `condB_of_endPoint` (necessity); Theorem 13 in Bing's form follows from these together with
   the external direction of Theorem 12 and is not stated.
4. **Theorem 13, necessity** (`condB_of_endPoint`), Bing's text repaired: let `H`, `K` be
   subcontinua through `p` with neither containing the other; pick `h ∈ H ∖ K`, `k ∈ K ∖ H`, and
   `ε` less than `dist(h, K)` and `dist(k, H)` (positive, `H`, `K` compact). Take an `ε`-chain
   covering `M` with `p` in the first link only. Let `d_i` be the last link meeting `H ∪ K`; say it
   meets `H` (the other case is symmetric). `H` is connected, contains `p ∈ d_1` and a point of
   `d_i`, so `H` meets every `d_1, …, d_i` (`Chain.inter_link_nonempty_between`). The point `k`
   lies in some `d_j`, `j ≤ i`, which meets `H`; so `dist(k, H) < ε`, a contradiction. This is
   what "no point of `H` is farther than `ε` from `H`" must mean. **This same argument is the
   self-contained half of Theorem 16** (`exists_not_endPoint_of_not_HI`): a decomposable
   subcontinuum `N = H ∪ K` of `M` (both proper subcontinua of `N`) has `H ∩ K ≠ ∅` (`N` connected)
   and neither contains the other; a point of `H ∩ K` fails condition B, hence condition C.
5. **Theorem 12, A ⇒ B** (`condB_of_condA`): if `H`, `K` are subcontinua through `p` with neither
   containing the other, `H ∪ K` is a nondegenerate subcontinuum through `p`; condition A gives
   `q ≠ p` with `H ∪ K` irreducible between `p` and `q`; but `q` lies in `H` or in `K`, a proper
   subcontinuum of `H ∪ K` containing `p` and `q`.
6. **Theorem 10.** Bing's proof is by a minimal counterexample (`M'` irreducible with respect to
   the theorem failing for the fixed `D`): the family of subcontinua of `M` through `p` for which
   no refinement `E` exists is closed under nested intersections (a chain that works for the
   intersection works for a nearby member? — **no**: the argument needs the opposite, that a
   refinement covering the intersection covers some member; by compactness, a chain covering
   `⋂ M_i` covers `M_i` for large `i`, since `⋂ M_i ⊆ E^*` open). So Zorn (as in
   `exists_irreducible`) gives a minimal `M'`. The surgery then produces `E` for `M'` from a
   minimal-length `F` for a proper `M'' ∋ p` meeting every link of `D`, contradicting minimality.
   Points to check: existence of `M''` (if some link of `D` misses `M'`, drop it — but dropping a
   middle link breaks the chain; Bing's "suppose each element of `D` intersects `M`" leaves the
   other case to the reader, presumably by passing to the minimal covering subchain, as in
   batch 84's `MinCover`); the choice of `N` inside `d_1 ∩ f_j ∖ {p}` meeting `M''`; that the
   component of `M ∖ N` containing `p` lies in `M''` (condition A for `M`: `M` is irreducible from
   `p` to some `q`; the component `H` of `p` in the compact `M ∖ N` is a proper subcontinuum
   through `p`, so misses `q`; why is it inside `M''`? — the report supplies the argument or the
   missing hypothesis); the separation `M ∖ N = H ∪ K` with `H` the component of `p` needs
   `M ∖ N` to have `H` as a union of components that is clopen in `M ∖ N`, which is where
   compactness (`H` is a component of a compact metric space, hence an intersection of clopen
   sets) enters; and that the displayed `E` is a chain (adjacency of consecutive links, and
   non-adjacent links disjoint) that covers `M` and refines `D`. Each of these is a claim to be
   proved or corrected; the report lists them.
7. **Theorem 14.** The `δ` in Bing's proof — every `δ`-chain covering `M` has a link inside `d_1`
   between the links of `p` and the links of `q` — comes from irreducibility: otherwise a
   sequence of `1/i`-chains would give (by the limit argument of batch 81, `T13.limSup`) a
   subcontinuum of `M` through `p` and `q` missing an open set meeting `M` ... the report
   reconstructs it. The skeleton takes `p`, `q` end points (condition C) and `M` irreducible
   between them; the case `p = q` is degenerate (`M = {p}`) and the statement holds with a
   one-link chain.
8. **Theorem 15.** The conclusion is stated with the subcontinuum **nondegenerate** and the two
   opposite end points distinct — implicit in Bing's construction (`C_1` has more than two links,
   so its end links are disjoint, and the nested closures put a point of the limit in each). The
   sequence `C_i` with "each link contains the closure of a link of `C_{i+1}`" is the `C`-side of
   batch 84 (`refine_step`, `MinCover`, onto patterns). The subchains `D_i` are chosen so that end
   links nest: this needs a fine chain whose *end* links have closures in the coarse end links —
   trim the fine chain to a subchain `D_{i+1}` starting at a link whose closure lies in the first
   link of `D_i` and ending at one whose closure lies in the last; the limit is then a chain from
   `p` to `q` at every level for suitable `p`, `q` (nested closed end links, as in batch 84's end
   boxes).
9. **Implicit hypotheses recorded:** nondegeneracy in Theorem 15's conclusion (item 8);
   `p ≠ q` in "opposite end points" for the nontrivial case (item 7); Theorem 16's sufficiency
   uses only "not hereditarily indecomposable ⇒ some point is not an end point", stated as such.

## 4. Deliverables

1. The seven statements of `EndPoints51.lean`, `sorry`-free where achieved, with `#print axioms`
   in `axioms-batch85.txt`; reshaped statements recorded; any counterexample in Lean.
2. Report: first line names the commission read; counterexamples first; then the targets in
   order; then §3 items 4, 6, 7, 8 claim by claim.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`.

## 5. Not in this batch

Bing 1951 §3 (Theorems 6, 7); Theorem 5; Theorems 8, 9, 11 and the two corollaries; Theorem 12
B ⇒ A; Theorem 16's external steps. See §1.
