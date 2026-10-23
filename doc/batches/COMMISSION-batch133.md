# Commission: batch 133 — tree-like continua do not contain separating continua; Bing 1951 (Duke), Theorem 7 as printed; the definition of tree-like repaired

**Go!** Runs on top of the batch-132 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch133.md` — this text (also pasted into the prompt);
* `TreeLikeNS.lean` — a skeleton, `sorry`s as work items. Save it as `HPC/Plane/TreeLikeNS.lean`
  and add `import HPC.Plane.TreeLikeNS` at the end of the root `HPC.lean`.

Shapes may be adjusted, with each change recorded. The report names the commission read in its
first line; each item is reported as *proved*, *refuted*, or *open with the obstruction stated*.

## 0. On batch 132

Audited and accepted. Fugate's Corollary 1 is proved by the direct route, (U) holds, my hand
proof had no error, and the build has no `sorry` (`sorryAx` in no line, 675 lines). The
`fugate_cor1` docstring still says "(∗) rests on Ingram 1968". Reword it to "rests on Ingram's
Lemmas 1–2 and the direct route (`Ingram68Core`, `Ingram68Star`)". That is the only edit to
`Ingram68.lean`.

## 1. A defect in the repository's definition of tree-like (found in audit; my commission slip)

`IsTreeLike` (`Tree67.lean`, batch 117) asks `diam A < ε` of each link of the tree chain, but not
that the link be bounded. Mathlib's `Metric.diam` of an unbounded set is `0`. So:
* `{univ}` is a tree chain of every mesh: coherent and triple-free vacuously, with no circular
  subcollection.
* Every continuum satisfies `IsTreeLike`, a circle included.
* The formal `theorem6_1951` (conclusion `IsTreeLike M`) is therefore vacuous.
* The open question `treeLike_nonseparating` was false as stated.

`theorem7_1951` and `theorem7_weak` are not affected: their links are polygon interiors, hence
bounded. `IsSnakeLike` is not affected either: `IsEpsChain` requires boundedness.

**Edits.**

1. `HPC/Plane/Tree67.lean`: change `IsTreeLike` to require
   `Bornology.IsBounded A ∧ diam A < ε`, matching `IsEpsChain`. Keep a comment recording the old
   form and this batch's finding.
2. Re-check `theorem6_1951` (`Tree7Comp.lean` `theorem6_1951_rel`, `Enc2.lean` `theorem6_1951`).
   It is derived from `theorem7_1951`, whose links are polygon interiors and so bounded
   (`polyInterior` of a simple closed polygon is bounded: `jct_polygon`). The proof should need
   only the added boundedness. Report.
3. In `TreeLikeNS.lean` (item 0 of the skeleton): `IsTreeLikeOld` (the old definition, verbatim)
   and `isTreeLikeOld_of_isContinuum` (every continuum satisfies it). This is the certificate for
   the ledger.

Grep for every other use of `IsTreeLike` and `IsTreeChain`, and report any statement whose meaning
changes. There should be none beyond `theorem6_1951`'s conclusion.

## 2. Items (`TreeLikeNS.lean`)

The skeleton header has the full argument. It uses no Borsuk theorem and no Brouwer theorem: a
logarithm on a fine tree cover, the batch-125 crossing parity, and the batch-130 grid.

1. **The definition** (§1 above): `IsTreeLikeOld`, `isTreeLikeOld_of_isContinuum`.
2. **A logarithm on a fine tree cover** (`toCpx`, `continuous_toCpx`, `exists_log_on_ball`,
   `exists_leaf`, `exists_log_on_treeChain`).
   * `exists_leaf` is graph theory. A chordless cycle in the nerve is a circular subcollection, so
     the nerve is a forest. Coherence makes it connected. Removing a leaf keeps all four clauses of
     `IsTreeChain`.
   * The induction carries the *ball invariant*: on each link, the logarithm is the restriction of
     a branch defined on the whole ball `D_A`. This handles disconnected links and disconnected
     pairwise intersections. That is why the hypothesis is "far from `p`" rather than anything
     about connectedness.
3. **No logarithm on a polygon around `p`** (`no_log_on_polygon`).
   * Along an edge missing `p`, the change in `Im L` is the signed angle `αᵢ ∈ (−π, π)`.
   * Telescoping around the polygon gives `Σ αᵢ = 0`.
   * With `θ = arg (p − z)`, whose cut is the east ray, `αᵢ = Δθ + 2π jᵢ` with `jᵢ` odd exactly
     when `CrossesEast p vᵢ vᵢ₊₁`.
   * So `Σ jᵢ = 0` but `Σ jᵢ ≡ parity v p = 1` (`polyInterior_eq_oddSet`). Contradiction.
   * Reuse `crossesEast_jump`, `vJump` and `sum_vJump_telescope` (`Jct1.lean`) and
     `dirAngle`/`exists_angle` (`Cyc2Circle.lean`) where they fit. Vertices of the polygon lying
     on the east ray are the delicate case; the half-open convention of `CrossesEast` is what
     makes the parity count right.
4. **A polygon in an open set around a point** (`exists_enclosing_polygon_pt`,
   `exists_polygon_around`).
   * The first is batch 130's `exists_enclosing_polygon` for a point of a bounded set; only
     boundedness is used.
   * The second applies the cut-wire theorem (`exists_split_of_no_continuum`, batch 132, stated in
     a compact metric space). Use it on the compact subspace `Wᶜ ∩ closedBall 0 R`, or re-derive
     it for closed bounded subsets of `Pt`.
   * Then take the grid at a mesh below a third of the distance from `F₁` to
     `F₂ ∪ (ball 0 R)ᶜ`, and use `frontier_gridUnion`.
5. **Assembly** (`exists_bounded_component_of_separates`, `isTreeChain_filter_meet`,
   `treeLike_nonseparating`), then the two corollaries (bodies given):
   * `theorem7_1951_treeLike`: **Bing's Theorem 7 as printed**;
   * `isTreeLike_iff_nonseparating`: Theorem 6 and its converse.

**Refutation candidates.**
* `exists_log_on_ball`'s constant `4`. In the sup metric a ball is a square, and `toCpx` changes
  distances by up to `√2`; adjust the constants as needed.
* `exists_leaf`'s claim that `G.erase A` is coherent.
* `no_log_on_polygon` at vertices on the east ray.
* `exists_bounded_component_of_separates`, which needs "the complement of a big closed ball is
  connected" (`Enc2.lean` has the four-half-planes argument).

## 3. Edits to existing files (exhaustive)

1. `Tree67.lean`: `IsTreeLike` (§1).
2. `Tree7.lean`: replace the comment on `treeLike_nonseparating` with a pointer to
   `TreeLikeNS.lean` (batch 133).
3. `Tree7Comp.lean` and `Enc2.lean`: only if the boundedness change forces a change to
   `theorem6_1951_rel` or `theorem6_1951`.
4. `Ingram68.lean`: the `fugate_cor1` docstring (§0).
5. `Axioms.lean`: add a group "Tree-like continua do not separate; Duke Theorem 7 as printed;
   `IsTreeLike` repaired (batch 133)". Regenerate `axioms.txt`; `sorryAx` should still appear in
   no line.
6. `OPEN.md`: `treeLike_nonseparating` closed. Record that it was false under the old definition
   and is proved under the repaired one.
7. `LEDGER.md`, three rows:
   * "Bing 1951 (Duke), Theorem 7: stated for tree-like continua, proved by reference to the proof
     of Theorem 6, which assumes no subcontinuum separates the plane. The implication 'tree-like ⇒
     no subcontinuum separates the plane' is not stated or proved in the paper (classical).
     Proved: `treeLike_nonseparating` (batch 133)."
   * "Repository definition `IsTreeLike` (batch 117) omitted boundedness of links; every continuum
     satisfied it (`isTreeLikeOld_of_isContinuum`); `theorem6_1951` was vacuous until batch 133.
     Commission slip."
   * Any defect found while doing the above.
8. `README.md`: the Duke line ("Theorems 1–16 as printed, Theorem 6 with its converse"), and
   batch count 133.

## 4. Deliverables

1. Items 1–5 and edits 1–8. Write `#print axioms` output to
   `doc/batches/audits/axioms-batch133.txt`, and regenerate `axioms.txt`.
2. The report. Its first line names the commission read. It covers:
   * items in order;
   * the result of the `IsTreeLike` grep;
   * how `no_log_on_polygon` handled vertices on the ray.
3. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing at the root.
4. Not attempted: the optional Ingram items (Sorgenfrey 1.8, Lemma 3, Theorems 1 and 2(2)).
