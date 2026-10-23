# Commission: batch 118 — Bing 1951 (Duke), Theorem 6 relative to `PlaneFacts`

**Go!** Runs on top of the batch-117 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch118.md` — this text (also pasted into the prompt);
* `Tree6.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/Tree6.lean` and
  add `import HPC.Plane.Tree6` at the end of the root `HPC.lean`. Shapes may be adjusted with
  the change recorded. No existing file is to be edited, except `Axioms.lean`/`axioms.txt` (the
  §3 group), and — only if item 4 below ends in the fallback — `HPC/Plane/Tree67.lean`, where
  `PlaneFacts` may gain a field (see item 4).

The report names the commission read in its first line.

## 0. On batch 117

Audited: two refutations of my skeleton, both accepted — `janiszewski` for closed sets is
false in the plane (the two rays meeting at infinity; compact form adopted), and
`inter_gridSq_subset_notched` needs `r < dist`, not `≤` (open strips). Everything else proved;
the grid cover is unconditional; 362 declarations; `sorryAx` in two.

## 1. The task

The second and third paragraphs of Bing's proof (COMMISSION-batch117.md §1), giving
`theorem6_1951 (hPF : PlaneFacts)`. The skeleton header lists the five parts; the docstring of
`exists_theta_point` gives the Janiszewski argument for Bing's unproved sentence "There is a
point `q` on the interior of this simple closed curve which is a boundary point of `h_1`, a
boundary point of `h_2`, and a boundary point of `h_1·h_2`" — the one place where the interface
does real work besides `enclose`.

## 2. Items

1. **Polygonal arcs** (`polyPathOf`, `IsSimplePolyArc`, `exists_polyPath_of_isConnected`,
   `exists_simplePolyArc_of_polyPath`, `IsSimplePolyArc.isContinuum`, `.split`,
   `.exists_first_mem`). Polygonal connectivity: the set of points of `h` reachable from `p` by a
   polygonal path in `h` is open (a ball in `h` is convex) and relatively closed in `h`; `h`
   connected. Loop erasure: induction on the list length — if two segments of the path meet, cut
   out the loop between the first such pair; or any other finite argument. The representation of
   arcs as vertex lists is a suggestion; change it if a `Fin n → Pt` or a `Path`-based
   representation is easier, recording the change (all later statements only use the
   *predicates*).
2. **Threading** (`IsThreaded`, `IsThreaded.isSimpleClosedPolygon`, `exists_threaded`) as in the
   docstring. The trimming order: for `i = 0, …, m−1` in turn, cut `α i` at its first point on
   `α (i+1)` (`exists_first_mem` with `K = α (i+1)`, closed; the start `p i` of `α i` is not on
   `α (i+1)` because `p i ∈ d (i−1) ∩ d i` and `d (i−1) ∩ d (i+1) = ∅` for `m ≥ 3`… check `m = 3`,
   where `d (i−1) ∩ d (i+1) ≠ ∅` — there use instead that `p i ∉ d (i+1)` can be arranged by
   choosing `p i ∈ d (i−1) ∩ d i ∖ d (i+1)`, possible since no point is in three links… that is
   not a hypothesis of `exists_threaded`; add "no three links share a point" if needed and
   record), and restart `α (i+1)` there (`split`). At the last step the start of `α 0` is cut;
   its end `p 1'` survives because `α (m−1) ⊆ d (m−1)` cannot contain `p 1' ∈ d 0 ∩ d 1` (for
   `m ≥ 3` that would be a point of three links — again the no-triple hypothesis). State the
   hypotheses actually needed.
3. **Consequences of `jct`** (`polyInterior_disjoint_of_unbounded` — no `jct` needed;
   `PlaneFacts.local_side`; `PlaneFacts.sides`). `local_side` is the geometric heart: a small ball
   about `w ∈ Γ` meets only the edge(s) through `w`; the ball minus those segments has two
   connected pieces (a disk cut by a chord, or by two segments from a common point; the sup-metric
   ball is a square — say what is proved); each piece is connected and avoids `Γ`, so lies in `U`
   or in the exterior `V`; `w ∈ frontier U ∩ frontier V` (`jct`) puts one piece in each. Then
   `U ∩ ball w r` is that one piece (for `r` small), nonempty and connected.
4. **The point `q`** (`PlaneFacts.exists_theta_point`), by the docstring's argument. If
   `local_side` resists, the fallback is to add it to the interface: a structure `PlaneFacts'`
   extending `PlaneFacts` with the field `local_side`, every later theorem taking `PlaneFacts'`,
   and a note in the report; `PlaneFacts` itself is not weakened. Do not add `exists_theta_point`
   itself as a field unless `janiszewski` turns out not to suffice — then say exactly where.
5. **Theorem 6** (`compFamily`, `compFamily_no_triple`, `compFamily_no_circular`,
   `theorem6_1951`). Assembly: `exists_notched_cover` for `ε`; `enclose` with `G = ⋃ d`;
   `d₀ = polyInterior J`; `H' :=` a finite subfamily of `compFamily d₀ D` covering `M` (for each
   `x ∈ M`, the component of `x` in `d₀ ∩ d` for a `d ∋ x`; these are open,
   `isOpen_connectedComponentIn_of_isOpen`; compactness of `M`), all members meeting `M`;
   `IsTreeChain H'`: open; coherent (`isCoherent_of_minimal_cover`); no triple
   (`compFamily_no_triple`); no circular subchain (`compFamily_no_circular`, with the members'
   connectedness for `exists_threaded`); diameters `< ε` since each member lies in a `d`.

Report each item *proved / refuted / open with the obstruction stated*; refutations first (the
candidates: `IsThreaded`'s clauses; the hypotheses of `exists_threaded`; the shape of
`exists_theta_point`). `PlaneFacts` is a hypothesis, so `sorryAx` stays at two whatever happens,
unless an item is left `sorry`.

## 3. Deliverables

1. Items 1–5; `#print axioms` in `axioms-batch118.txt`; `axioms.txt` regenerated.
2. Report: first line names the commission read; items in order; whether `PlaneFacts'` was
   needed; a ledger note on each sentence of Bing's two paragraphs that needed more than it says
   (the coherence of `H'`; the connectedness of the `h_i` used for threading; the point `q`; the
   use of `W`).
3. Not attempted: Theorem 7 (batch 119); `theorem3_end`, `fugate_cor1`.

## 4. Next

Batch 119: Theorem 7 — the links as interiors of simple closed polygons (components of the
intersection of two polygon interiors; the notched squares as star-shaped polygons), and the
hypothesis question (tree-like vs. no separating subcontinuum).
