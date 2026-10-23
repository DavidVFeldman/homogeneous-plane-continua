# Commission: batch 96 — closing Theorem 9's record; Theorem 11 (Duke 1951), necessity and reconnaissance on sufficiency

**Go!** Runs on top of the batch-95 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch96.md` — this text (also pasted into the prompt);
* `Theorem11.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Theorem11.lean` and add `import HPC.Plane.Theorem11` at the end of the root
  `HPC.lean`. Shapes may be adjusted with the change recorded.

One edit to an existing file is permitted and requested (item 0). The report names the commission
read in its first line.

## 0. Housekeeping: close `theorem9_1951`

Batch 95 proved Theorem 9 as `theorem9_1951'`; batch 93's `theorem9_1951` keeps its `sorryAx`
only because of import order. Resolve it: delete `endElt_mem_bingH`, `bingH_irreducible_singleton`
and `theorem9_1951` (the three `sorry` declarations) from `HPC/Plane/Atriodic51B.lean`, leaving
`theorem9_1951_of_steps` and everything else there untouched; in `HPC/Plane/Theorem9B.lean`
rename `endElt_mem_bingH'` → `endElt_mem_bingH`, `bingH_irreducible_singleton'` →
`bingH_irreducible_singleton`, `theorem9_1951'` → `theorem9_1951`, keeping the primed names as
`alias`es if anything refers to them. Record the edit in the report and confirm with
`#print axioms theorem9_1951` in `axioms-batch96.txt`. No other existing file is to be edited.

## 1. Necessity (`isSnakeLike_of_subcontinuum`, `isUnicoherent_of_isSnakeLike`, `isHereditarilyUnicoherent_of_isSnakeLike`, `isAtriodic_of_isSnakeLike`)

Bing: "it is easy to see that a snake-like continuum is atriodic and hereditarily unicoherent."
Nadler 12.1–12.5 gives the arguments for arc-like continua with chains:

* 12.5 (subcontinua): a chain covering `M` restricts to the links meeting `K`, which form a chain
  after dropping links that miss `K` — careful: dropping a middle link that misses `K` splits
  the chain, but then `K` lies in one of the pieces (`K` connected,
  `Chain.inter_link_nonempty_between`). State the lemma used.
* 12.2 (unicoherent): if `M = H ∪ K` with `H ∩ K` disconnected, choose `ε` smaller than the
  distance between two closed pieces of `H ∩ K` and a chain of mesh `ε`; the links through the
  pieces and the connectedness of `H`, `K` produce a contradiction with the linear order of
  links (Nadler's argument). Report where compactness of `M` is used (`Fold.Q78.IsContinuum`
  gives it).
* 12.4 (atriodic): a triod `T` with core `N` and arms `A, B, C`; a chain of small mesh covering `T`
  has the links meeting `N` in a block; each arm, being connected and reaching outside the
  `N`-block's neighbourhood (arms have points at positive distance from `N`), leaves the block in
  a definite direction; three arms, two directions, two arms on the same side meet a common
  link — contradiction with the arms being separated requires more care (links are open; the
  arms' points in a common link need not be close in `T`). Follow Nadler; state the exact
  lemma proved if the triod definition (`IsTriod`, batch 92: `M ∖ N = A ∪ B ∪ C` mutually
  separated) needs a reformulation to run it.

Report which of these were "easy" in the sense of needing nothing beyond chain combinatorics
already in the repository.

## 2. Sufficiency: the structure of Bing's proof, and what is wrong in it

Bing's text (p. 660, verbatim):

[Quotation moved to doc/sources/transcriptions/bing51duke.md, §doc/batches/COMMISSION-batch96.md, Bing's text (p. 660); batch 204.]

Observations to be tested (each is a skeleton statement):

1. **The separation sentence fails for nondegenerate `g'`** (`not_separation_of_accumulates`,
   pure point-set topology). `H ∩ K = g'`, so `(H − N) ∩ (K − N) = g' − N`. A separation
   `H' | K'` of `S − N` with `H' ⊇ H − N` forces `K' ⊆ K − g' − N` to be separated from
   `g' − N ⊆ H'`; if `K − g'` accumulates at every point of `g'` — which is what "a sequence of
   elements converging to `g'`" from the `K`-side gives when the convergence is in the Hausdorff
   sense — this needs `g' ⊆ N`, impossible for a nondegenerate `g'` and an `N` of diameter `< ε`
   once `ε < diam g'`. Prove the point-set statement as stated.
2. **For degenerate `g' = {p'}` the sentence is immediate** (`separation_of_degenerate`): `H − N`
   and `K − N` are disjoint closed sets.
3. **So the proof needs a degenerate interior element** (`exists_degenerate_interior_elt`).
   Bing's "uncountable `G'`" sentence is unjustified and, as used, insufficient; what the
   argument needs is one element that is a point and not an end element. Expected route: the
   elements are the fibres of the quotient map `S → S/G` (batch 94); nondegenerate fibres have
   empty interior (Theorem 8 (b)) but there may be uncountably many; the classical fact
   (Kuratowski, for layers of an irreducible hereditarily decomposable continuum) is that the
   union of the nondegenerate layers is of first category, whence by Baire the degenerate ones
   are dense. Prove, by that route or another (for instance: every nonempty open set of `S`
   contains a degenerate element — argue with the u.s.c. and Theorem 8), or state the
   obstruction. **Q-deg** in the report. Note that for a degenerate interior element the
   two-sided Hausdorff convergence in Bing's sentence is automatic from u.s.c., so his sentence
   is satisfied by it; only its uncountability is beside the point.
4. **The two sides** (`exists_two_sides`, `sides_continua`): property 2 (at most two components
   of `S − g`) and (a) (an interior element separates two others) give exactly two components,
   both open (batch 92's `isOpen_component_compl`) and connected; `U ∪ g'`, `V ∪ g'` are continua
   (Nadler 6.3, batch 94), proper, with union `S` and intersection `g'`. Bing's `H`, `K` are
   these (every element lies on one side, by connectedness).
5. **Condition A on a side** (`condA_side`): with `g' = {p'}`, a nondegenerate subcontinuum
   `L ⊆ H = U ∪ {p'}` containing `p'` is irreducible from `p'` to some point. Expected argument:
   `L ∖ {p'} ⊆ U`; elements of `S` meeting `L` are linearly ordered by separation on the
   `U`-side; `L` meets a farthest element `g_a` (compactness of the quotient order — or: by
   Theorem 8 (c) applied to `L` as a space, `L` is irreducible between its two end elements; show
   `{p'}` is one of them, using `endElt_inter_contains_endElt` from batch 95 with `g' = {p'}`
   an… — careful: `{p'}` is not an end element of `S`, so batch 95's lemma does not apply
   directly; what is available is that `{p'}` is an end element of the *space* `H`, if that can
   be shown: `H ∖ {p'} = U` is connected, so `{p'}` is a non-cut point of `H`, and the elements
   of `H` through `p'` lie in `{p'}` (batch 94), so `{p'}` is an element of `H` and a non-cut
   element, i.e. an end element of `H`; then batch 95's `endElt_inter_contains_endElt` in the
   space `H` with `Y = L` gives `{p'}` an end element of `L`, and Theorem 8 (c) for `L` gives
   irreducibility from `p'` to any point of the other end element). Prove or state the gap.
   **Q-A** in the report. For nondegenerate `g'` the claim can fail on one side (on `S₀` with
   `g'` the bar and `p' = (0,0)`: fails for `H = bar ∪ C₁`, holds for `K`); no Lean refutation
   is asked, a remark suffices.
6. **Theorem 10 is applied to both `H` and `K`** ("either" must mean "each"); it is open. So
   sufficiency is proved **conditionally** (`theorem11_1951_of_T10`), with the exact statement of
   `theorem10_1951` as a hypothesis; when the last-link claim closes, the theorem follows.
7. **Amalgamation** (`epsCoverable_amalgam`): the displayed chain. Links must be open: `H − N`
   and `K − N` are closed, so `H'·h_i` is not open as written; take instead open neighbourhoods
   (`S − N` is compact, split into two disjoint closed sets, which have disjoint open
   neighbourhoods `O_H`, `O_K`; use `O_H ∩ h_i` and `O_K ∩ k_j`, and `N` small enough that the
   middle link has diameter `< ε` — adjust `N` and the chains' mesh, e.g. mesh `ε/3`). Check that
   `O_H ∩ h_i` meets `O_H ∩ h_{i+1}` (they both meet `H`, where `h` is a chain, provided
   `h_i ∩ h_{i+1} ∩ H ≠ ∅` — is that given? a chain covering `H` has consecutive links meeting,
   but not necessarily inside `H`; use the fact that a chain *covering a connected set* can be
   trimmed so that consecutive links meet inside it, or thicken; state what is used). Record the
   mesh bookkeeping.
8. **Minimal counterexample** (`exists_minimal_notCoverable`): Zorn on non-`ε`-coverable
   subcontinua; closedness under decreasing intersections because a chain covering the
   intersection covers some member (compactness; batch 90's `isClosed_notCoverable` is the
   hyperspace form). Then in the proof of `theorem11_1951_of_T10`, `S'` satisfies `BingS`
   (batch 94), has a degenerate interior element (item 3), sides (4), condition A (5), Theorem 10
   chains (6), amalgamation (7) — a contradiction with non-coverability.

Report items 1–8 each as *proved / refuted / open with the obstruction stated*; refutations first.
If `exists_degenerate_interior_elt` is open, prove `theorem11_1951_of_T10` with it as a further
hypothesis and say so.

## 3. Deliverables

1. Item 0 (`theorem9_1951` sorry-free); §1 four lemmas; §2–3 as above; `#print axioms` in
   `axioms-batch96.txt`.
2. Report: first line names the commission read; refutations first; item 0; §1; items 1–8.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
   `theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`.

## 4. Next

Corollaries 1 and 2 of Theorem 11 (tree-like + atriodic ⇒ snake-like; atriodic hereditarily
decomposable non-separating plane continua are snake-like — Corollary 2 needs plane topology and
is not planned); then a return to the last-link claim of Theorem 10 with the §4 structure in hand.
