# Commission: batch 89 — Bing, *Concerning hereditarily indecomposable continua*, §4: monotone decompositions (Theorems 3 and 4)

**Go!** Runs on top of the batch-88 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch89.md` — this text (also pasted into the prompt);
* `Monotone51.lean` — a skeleton of one definition and four statements (plus one naming lemma), all `sorry`, all work
  items. Save it as `HPC/Plane/Monotone51.lean` and add `import HPC.Plane.Monotone51` at the end
  of the root `HPC.lean`. Nothing else is to be replaced. Shapes may be adjusted with the change
  recorded; `theorem3_HIC` and `theorem4_HIC` keep their conclusions.

The report names the commission read in its first line.

## 0. On batch 88

Audited: Theorem 1 in both forms, `pseudoArc_unique`, `isPseudoArc_iff_endPoints` and the rest
proved as stated; the crookedness-eventually lemma (`PA51.eventually_crookedIn`) proved in the
meet sense, with the flagged closure step repaired by arguing about open links and joining the
two spans through a common limit point rather than a shared link; standard axioms throughout.
Two skeleton statements refuted and corrected: for a *description*, compactness of `Δ.M` does not
replace a compact ambient space (`exists_description_compact_disconnected`: the plane description
restricted to the plane minus `M₀ ∖ {P, Q}` describes `{P, Q}`). Recorded as a lesson alongside
`P ≠ Q`: the definition `Description` is weaker than Bing's chains in a compact space, and
statements about `Δ.M` need the ambient compactness, or links inside a compact set.

## 1. What this batch is

Bing's §4 says the pseudo-arc is "topologically equivalent to itself under a nontrivial monotone
decomposition". In the repository's terms a monotone decomposition of a compact continuum `M` is a
continuous surjection `f : M → M'` onto a compact metric space with connected fibres (Bing 1951,
*Snake-like continua*, p. 654 says "monotone" means exactly this). Theorem 3: the image of a
chainable continuum is chainable. Theorem 4: if `M` is a pseudo-arc and every fibre is a proper
subcontinuum, the image is a pseudo-arc (so homeomorphic to `M` by Theorem 1). *Snake-like
continua* quotes Theorem 3 as its Theorem 3.

## 2. Bing's text (p. 47), transcribed

[Quotation moved to doc/sources/transcriptions/bing51pacific.md, §doc/batches/COMMISSION-batch89.md, 2. Bing's text (p. 47); batch 204.]

## 3. Facts about the text, and what the skeleton does with them

1. **Decompositions as maps.** The skeleton's `IsMonotoneMap f M` is: `f` continuous on `M`
   (as a map of the subspace), `f '' M = M'`, and every fibre `M ∩ f⁻¹ {y}` connected. Upper
   semicontinuity of the collection of fibres is automatic for a continuous map from a compact
   space to a Hausdorff space (the map is closed), and the "metric on the decomposition space" is
   the given metric of the codomain. Bing's `δ` is uniform continuity of `f` on the compact `M`:
   points of `M` within `δ` have images within `ε/5`.
2. **`D(i, j)` is open.** `D(i, j) = {y : fibre y ⊆ c(i) ∪ ⋯ ∪ c(j)}` is the complement of the image
   of the closed set `M ∖ (c(i) ∪ ⋯ ∪ c(j))`, and `f` is a closed map. The skeleton uses sets of this
   form, so the links are open as `Chain` requires.
3. **Bing's `n_i`.** `n_{i+1}` is the largest index such that some fibre meets both `c(n_i)` and
   `c(n_{i+1})`. A fibre is connected, so the links it meets form an index interval (Bing 1948
   batch 79, `Chain.inter_link_nonempty_between`; batch 86, `Chain.meet_ordConnected`). From the
   definition: a fibre meeting `c(n_i)` meets no `c(l)` with `l > n_{i+1}`; so a fibre meeting
   `c(n_i)` lies in `c(l)` for `l ≤ n_{i+1}`, and a fibre meeting `c(n_{i+1})` meets no `c(l)` with
   `l ≤ n_{i−1}` (it would then meet `c(n_{i−1})` and `c(n_{i+1}) ⊇ c(n_i + 1)`'s index range —
   precisely, `n_{i+1} ≥ n_i + 1`, so a fibre meeting `c(n_{i−1})` and `c(n_{i+1})` meets
   `c(n_i + 1)`, which the definition forbids).
4. **Is Bing's chain a chain? — a question.** Consecutive links `D(n_{3k+1}, n_{3k+5})` and
   `D(n_{3k+4}, n_{3k+8})` must meet: some fibre must lie inside `c(n_{3k+4}) ∪ ⋯ ∪ c(n_{3k+5})`. The
   fibres meeting `c(n_{3k+4})` and `c(n_{3k+5})`, which exist by the definition of the `n_i`, lie in
   `c(n_{3k+3} + 1) ∪ ⋯ ∪ c(n_{3k+5})` by item 3 — a range that starts *before* `n_{3k+4}` in
   general. The commission did not find, in Bing's text, the reason why some fibre lies in the
   narrower range, and did not look for one. The report either supplies it, or replaces Bing's
   windows by ones that work (overlapping on three consecutive `n`'s, or defined from the fibres
   through `c(n_{3k+4})` directly), recording the change. Non-adjacent links are disjoint as Bing
   has them: `D(n_1, n_5) ∩ D(n_7, n_{11}) = ∅` because `c(n_5)` and `c(n_7)` are non-adjacent
   (`n_7 ≥ n_5 + 2`) and a fibre inside both ranges would be empty. Covering: every fibre meets some
   `c(n_i)`-range of length at most two steps and so lies in one window — check against item 3.
   Mesh: a window's fibres lie in `c(n_{3k+1}) ∪ ⋯ ∪ c(n_{3k+5})`; two fibres there are joined by a
   chain of at most four further fibres each within `δ` of the next (one per `n`-step, since
   consecutive `c(n_i)`, `c(n_{i+1})` are joined by a fibre), so their images are within `5 · ε/5`.
   This is Bing's `ε/5`; the report confirms the count.
5. **Theorem 4.** Bing says "follows from Theorems 1 and 3"; what is needed:
   * **the image is hereditarily indecomposable**: for a monotone closed surjection, the preimage
     of a connected set is connected (standard; the proof uses that fibres are connected and the
     map is closed — Mathlib has `IsClosedMap` and `isPreconnected` results for quotient maps;
     the report says which route), so the preimage of a subcontinuum `K'` of `M'` is a subcontinuum
     `K` of `M`; if `K' = A' ∪ B'` with `A'`, `B'` proper subcontinua, then `K = f⁻¹A' ∪ f⁻¹B'` with
     both proper (a point of `K' ∖ A'` has a nonempty fibre outside `f⁻¹A'`), contradicting the
     indecomposability of `K`;
   * **the image is chainable**: Theorem 3;
   * **the image is nondegenerate**: if `M'` were a point its one fibre would be `M`, not a proper
     subcontinuum;
   * **compact continuum**: image of a compact connected set;
   then `theorem1_HIC'` (batch 88).
6. **Implicit hypotheses.** Theorem 3 needs `M` compact (Bing: "compact continuum") and
   nothing on `M'` beyond being a metric space (compactness of `M'` follows). Theorem 4 needs the
   fibres *proper* (stated) and `M` nondegenerate (in `IsPseudoArc`). "Upper semi-continuous
   collection of continua filling `M`" is exactly the fibres of a continuous surjection with
   connected fibres onto a Hausdorff space; the skeleton does not formalize the collection side
   of that equivalence.

## 4. Deliverables

1. `IsMonotoneMap`, `theorem3_HIC`, `theorem4_HIC`, `isHereditarilyIndecomposable_image`,
   `isContinuum_image`, `sorry`-free where achieved, with `#print axioms` in `axioms-batch89.txt`;
   reshaped statements recorded; any counterexample in Lean.
2. Report: first line names the commission read; counterexamples first; then the targets; then
   §3 item 4 (Bing's windows: confirmed or replaced) and item 5 (which connectedness-of-preimage
   argument) in detail.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `theorem10_1951`.

## 5. Not in this batch

§3 Theorem 2 (most continua are pseudo-arcs; hyperspace, Baire; a pseudo-arc inside a chain of
balls along a broken line in `ℝⁿ`) — the candidate for batch 90. §5 (plane topology; Moore's
theorem) — not planned.
