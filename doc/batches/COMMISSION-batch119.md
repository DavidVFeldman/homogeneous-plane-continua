# Commission: batch 119 — Bing 1951 (Duke), Theorem 7, part I: the links, general position, cross-cuts

**Go!** Runs on top of the batch-118 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch119.md` — this text (also pasted into the prompt);
* `Tree7.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/Tree7.lean` and
  add `import HPC.Plane.Tree7` at the end of the root `HPC.lean`. Shapes may be adjusted with the
  change recorded. No existing file is to be edited except `Axioms.lean`/`axioms.txt` (new group
  "Bing 1951 (Duke) §3, Theorem 7 — relative to `PlaneFacts` (batch 119)"; the unconditional items
  2 and the geometric parts of 1 and 3 may go in the same group with a note).

The report names the commission read in its first line.

## 0. On batch 118

Audited: everything proved, nothing refuted, `PlaneFacts'` not needed; 376 declarations, `sorryAx`
in two. The shape changes (hypotheses dropped from `sides`, `exists_theta_point`,
`exists_threaded`) are recorded in my notes with the report's ledger notes.

## 1. The task

Theorem 7 (p. 657): "If `M` is a tree-like plane continuum and `ε` is a positive number, there is a
tree-chain covering `M` whose links are the interiors of simple closed curves of diameters less than
`ε`." Bing: "In the proof of Theorem 6 we establish the following result." Two things in that proof
carry Theorem 7 and neither is argued there:

(a) "Let `H` be the collection of all interiors `h` of simple closed curves such that `h` is a
component of the intersection of `d_0` and one of the `d_i`'s." That every component of
`d₀ ∩ dᵢ` is the interior of a simple closed curve is asserted. I believe it is true in general
(a pinch point — a component occupying two opposite sectors at a point of `∂d₀ ∩ ∂dᵢ` — is
excluded by the Jordan theorem applied to a polygon through the pinch inside the component, and a
Jordan curve has its interior on one side only, so no slits), but the general proof needs the
classification of compact polygonal 1-manifolds (the frontier of a component is a closed subset of
the graph `J ∪ ∂dᵢ` which is locally two rays). The repository proves it instead under **general
position**, which is free: after `J` is chosen the whole notched cover is translated by a small
vector (item 3), and then `∂dᵢ` meets `J` transversally in finitely many points, the pieces of
`∂dᵢ` inside `polyInterior J` are **cross-cuts**, and the cross-cut theorem (item 4) plus an
induction (batch 120) gives the components as polygon interiors.

(b) The hypothesis "tree-like", where the proof uses "no subcontinuum separates the plane". The
repository will state `theorem7_1951` with the latter (what the proof proves). The implication is
item 5.

This batch does the elementary part — including Theorem 7 in a weak form that is already a
theorem — and the two tools; batch 120 assembles Theorem 7 in Bing's form.

## 2. Items

1. **The links of Theorem 6** (`notchedFamily`, `exists_notched_cover_param`, `isBounded_notched`,
   `isConnected_notched`, `isConnected_compl_notched`, `regular_notched`,
   `PlaneFacts.polyInterior_regular`, `compFamily_isBounded`, `compFamily_regular`,
   `compFamily_compl_connected`, `treeChain_of_cover`, `theorem7_weak`). The docstrings carry the
   proofs; the star-shapedness of a notched square (three convex open rectangles containing the
   centre of the square) does the geometric work. `treeChain_of_cover` is the tail of the proof of
   `theorem6_1951`, factored so that batch 120 can feed it the general-position cover; copy the
   proof, do not edit `Tree6.lean`. `theorem7_weak` is Theorem 7 with "interiors of simple closed
   curves" weakened to "bounded, open, connected, regular open, not separating the plane".
2. **The 20-gon** (`notchedVertices`, `notchedPoly`, `isSimpleClosedPolygon_notchedPoly`,
   `frontier_notched`, `notched_eq_polyInterior`). Unconditional: `polyInterior_eq_of_split`
   (batch 117) with `U = notched`, `V = (closure notched)ᶜ`, so no `jct`. Check the vertex list
   against the definition of `notched` (strip ends at `x₀ + r`, `x₁ − r`, strip width `η`); if the
   orientation or the starting vertex is inconvenient, change it and record. The simplicity check
   is finite but has 20 × 19 / 2 pairs; a lemma "axis-parallel segments with these coordinates
   are disjoint / meet only at the shared vertex" should reduce it.
3. **General position by translation** (`polyEdge`, `IsSimpleVertices`,
   `isSimpleClosedPolygon_iff`, `InGeneralPosition`, `finite_inter_of_gp`, `notched_translate`,
   `notchedVertices_translate`, `subset_translate_of_compact`, `exists_gp_translation`,
   `PlaneFacts.exists_gp_cover`). `exists_gp_translation` is the Baire-type step; the docstring
   lists the three kinds of bad translation. If a different, equivalent definition of general
   position makes batch 120's crossing analysis easier (for instance: every point of
   `polygonOf v ∩ polygonOf w` is interior to exactly one edge of each and those edges are not
   parallel), say so in the report — the definition is the one place in this batch where I most
   want your judgement, since batch 120 will live with it.
4. **Cross-cuts** (`IsSimpleClosedPolygon.split_two`, `isSimpleClosedPolygon_of_arcs`,
   `IsSimplePolyArc.isConnected_diff_ends`, `PlaneFacts.crosscut`). The docstring of `crosscut`
   gives the proof from `PlaneFacts.split`, `local_side`, and `janiszewski` (compact form). The
   arc lemmas are list bookkeeping in the style of `Tree6Arcs`; `IsThreaded.isSimpleClosedPolygon`
   (batch 118) may already give `isSimpleClosedPolygon_of_arcs` after splitting one arc at an
   interior vertex to reach three arcs — if `m = 2` is excluded there, say so.
5. **The hypothesis** (reconnaissance, no `sorry`, no new field). Can

       treeLike_nonseparating (hPF : PlaneFacts) {M} (hM : IsTreeLike M) :
           ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K

   be proved from `PlaneFacts`? Report *proved / refuted / open with the obstruction stated*. (It is
   a classical theorem; the proofs I know go through Borsuk's criterion for separating the plane
   by an essential map to the circle, or through Čech cohomology, neither of which is in the
   repository or in `PlaneFacts`. A refutation would mean the interface or the definitions are
   wrong, so a refutation would be the most important possible outcome.) Do not spend the batch
   on it: a clear statement of what a proof would need is the expected answer.

Report each item *proved / refuted / open with the obstruction stated*; refutations first (the
candidates: the vertex list of item 2; `InGeneralPosition`; the hypotheses of `crosscut` — in
particular whether `hcU` is needed given `hcJ`; the closure clauses of `crosscut`). `PlaneFacts` is
a hypothesis, so `sorryAx` stays at two unless an item is left `sorry`; prefer leaving a stated
`sorry` in the "Open targets" group of `Axioms.lean` to deleting a statement, and say so.

## 3. Deliverables

1. Items 1–4; item 5 in the report; `#print axioms` in `axioms-batch119.txt`; `axioms.txt`
   regenerated.
2. Report: first line names the commission read; items in order; the ledger notes — for (a) above,
   whether you agree that Bing's "interiors of simple closed curves" is true in general and
   unargued, or see a counterexample (a Lean certificate of a counterexample would be a
   refutation of my analysis and goes to the ledger with the batch); for (b), the finding of
   item 5.
3. Not attempted: batch 120 (below); `theorem3_end`, `fugate_cor1`.

## 4. Next

Batch 120: (i) the cross-cut induction — for `polyInterior J` and a finite family of pairwise
disjoint cross-cuts (each as in `crosscut`, closures pairwise disjoint), every component of
`polyInterior J \ ⋃ c̄` is `polyInterior Γ` for a simple closed polygon `Γ ⊆ J ∪ ⋃ c̄` (induction on
the number of cross-cuts via `crosscut`; the other cross-cuts fall into one side, with ends on
`closure (polyInterior (αᵢ ∪ c)) ∩ J = αᵢ`); (ii) in general position, the components of
`notchedPoly ∩ polyInterior J` are such a family (the crossing points are interior to edges of both,
finitely many, and `notchedPoly` crosses from the interior to the exterior at each — so there are
at least two, and the arcs of `notchedPoly` between consecutive crossings are the cross-cuts);
(iii) the components of `polyInterior J ∩ notched` are the components of
`polyInterior J \ notchedPoly` contained in `notched`; (iv) `theorem7_1951 (hPF) (hM) (hns) (ε) :
∃ G, IsTreeChain G ∧ (∀ h ∈ G, ∃ Γ, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ) ∧ (∀ h ∈ G,
diam h < ε) ∧ M ⊆ ⋃ G` from `exists_gp_cover` and `treeChain_of_cover`. Say in the report which of
this batch's shapes should change for (i)–(iii).
