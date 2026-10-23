# Commission: batch 90 — Bing, *Concerning hereditarily indecomposable continua*, §3: most compact continua are pseudo-arcs (Theorem 2)

**Go!** Runs on top of the batch-89 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch90.md` — this text (also pasted into the prompt);
* `Most51.lean` — a skeleton of three definitions, one instance and nine statements, all `sorry`, all work
  items. Save it as `HPC/Plane/Most51.lean` and add `import HPC.Plane.Most51` at the end of the
  root `HPC.lean`. Nothing else is to be replaced. Shapes may be adjusted with the change
  recorded; `theorem2_HIC` keeps its conclusion.

The report names the commission read in its first line.

## 0. On batch 89

Audited: Theorems 3 and 4 proved as stated, standard axioms, no new `sorry`. Recorded: Bing's
windows `D(n_{3k+1}, n_{3k+5})` are not shown by his text to form a chain (consecutive windows
need a fibre inside an overlap that the interval data do not guarantee; a hand example with
intervals `[2m, 2m+3]` has no room in the overlap), and his `n_{i+1}` can equal `n_i`; replaced
by blocks with a `+1` and windows of five blocks overlapping on two, with mesh `6η` in place of
`5 · ε/5`. The preimage-of-connected argument is the closed-set one. Third text gap of this
paper's set (after the crookedness-eventually closures and 1951's Theorem 10), each repaired.

## 1. What this batch is, and what is expected to resist

Theorem 2: in a Euclidean space of dimension `> 1`, or in Hilbert space, the pseudo-arcs form a
dense `G_δ` in the space `C(S)` of compact continua with the Hausdorff metric. The skeleton states
it for a complete real inner product space of dimension at least two, which covers both.

Its proof has two halves of very different cost.

* **The `G_δ` half** is bookkeeping about closed sets in the hyperspace: the continua that cannot
  be covered by a `1/i`-chain form a closed set; the continua containing a decomposable
  subcontinuum with a `1/i`-separation form a closed set; the degenerate continua form a closed
  set. Mathlib has the Hausdorff metric on `TopologicalSpace.NonemptyCompacts` and its
  completeness, so Baire's theorem is available once the continua are shown closed in it. This
  half is expected to go through (items 1–5).
* **The density half** — every compact continuum `g` is within `ε` of a pseudo-arc — is where
  Bing writes three sentences ("There is a broken line `ab` whose distance from `g` is less than
  `ε/2`. Let `D` be an `ε/2`-chain from `a` to `b` covering `ab` such that each element of `D` is
  the interior of a sphere. There is a pseudo-arc `h` containing `a + b` which is covered by
  `D`.") that stand for: (i) a *simple* polygonal arc near any continuum (a chain of balls cannot
  cover a self-intersecting path: non-adjacent balls must be disjoint), which in the plane is a
  plane-topology fact and in higher dimension is general position; (ii) a chain of balls along it;
  (iii) a pseudo-arc inside a chain of balls — the batch-84 construction with the planar strip
  bent along the arc. Item 7 isolates (i)–(ii) as one geometric statement, `exists_tame_chain_near`,
  and item 6 does (iii) given it. The report says how far each got; `theorem2_HIC` is to be proved
  conditionally on whatever remains open, with the dependence explicit in the statement if the
  skeleton's form cannot be reached.

## 2. Bing's text (p. 46), transcribed

[Quotation moved to doc/sources/transcriptions/bing51pacific.md, §doc/batches/COMMISSION-batch90.md, 2. Bing's text (p. 46); batch 204.]

## 3. The targets, in order, with the facts behind them

1. **`Cont S`**, the hyperspace of compact continua: the subtype of `NonemptyCompacts S` whose
   carrier is connected, with the induced Hausdorff metric. **`isClosed_cont`**: it is closed in
   `NonemptyCompacts S` (a Hausdorff limit of connected compacta is connected: if the limit `K` is
   covered by two disjoint closed sets each meeting it, thicken them to disjoint open sets; the
   `K_m` eventually lie in the union and each meets both thickenings — the batch-81 limit argument
   `T13.isPreconnected_limSup` in Hausdorff-metric form). Hence `Cont S` is complete when `S` is,
   and a Baire space.
2. **`isClosed_notCoverable i`**: `{K : Cont S | ¬ ∃ chain of mesh < 1/i covering K}` is closed. A
   chain covering `K` is an open set containing `K`, and the Hausdorff ball about `K` of radius a
   Lebesgue-type margin lies inside it (`IsCompact.exists_thickening_subset_open`).
3. **`isClosed_separated i`**: `{K | ∃ K₁ K₂ ⊆ K continua, K₁ ∪ K₂ connected, ∃ x ∈ K₁, infDist x K₂
   ≥ 1/i, ∃ y ∈ K₂, infDist y K₁ ≥ 1/i}` is closed. A convergent sequence `K^m → K` in the
   Hausdorff metric has compact union `⋃ K^m ∪ K`; the witnesses `K₁^m, K₂^m` live in the compact
   hyperspace of that union (`NonemptyCompacts` of a compact space is compact — Mathlib has this
   for `Closeds`/`NonemptyCompacts`; check), so a subsequence converges to `K₁, K₂ ⊆ K`, continua
   by item 1, with `K₁ ∪ K₂` connected (limit of the connected `K₁^m ∪ K₂^m`) and the separation
   points surviving (`infDist` is continuous in both arguments for the Hausdorff metric). Bing's
   "`K'` is the sum of two continua" is the connectedness of `K₁ ∪ K₂`.
4. **`isClosed_degenerate`**: `{K | ∃ x, (K : Set S) = {x}}` is closed (diameter `0`).
5. **`isGδ_pseudoArcs`**: `{K : Cont S | IsPseudoArc (K : Set S)}` is the complement of the
   countable union of the closed sets of items 2–4, hence `G_δ`. The identification: not in any
   `F_i` ⇔ chainable (`IsSnakeLike`, with the continuum part automatic); not in any `G_i` ⇔
   hereditarily indecomposable (a decomposable subcontinuum `K' = A ∪ B` with neither containing
   the other gives points of `A ∖ B` and `B ∖ A` at positive distance from the other, hence some
   `i`; conversely a witness for `G_i` is a decomposable subcontinuum); not degenerate ⇔
   nontrivial.
6. **`exists_pseudoArc_in_tameChain`**: a pseudo-arc inside a tame chain of a real inner product
   space `E` of dimension `≥ 2`. `IsTameChain` is batch 84's `IsTame` with the plane replaced by
   `E`: a tame chain is the image of the standard *box* chain under a homeomorphism of `E`, where
   the standard box `j` is `{x : 2j < ⟪x, e₁⟫ < 2j + 3, 0 < ⟪x, e₂⟫ < 1, ‖x − ⟪x,e₁⟫e₁ − ⟪x,e₂⟫e₂‖ < 1}`
   for a fixed orthonormal pair `e₁, e₂` (in the plane, with `n = 2`, the last condition is empty
   and this is `stdRect`). The batch-84 step `real_step` transfers: its shear `Ψ` acts on the
   `(e₁, e₂)`-coordinates and the identity on the orthogonal complement is replaced by a
   contraction `v ↦ v/2` there, so that boxes shrink in every direction; the orthogonal complement
   of a two-dimensional subspace is a topological complement in any inner product space. Then
   `exists_description_plane`'s construction (stuttered Bing patterns, nested end boxes) gives a
   description inside the tame chain whose continuum lies in the chain's union and meets every
   link, and `isPseudoArc_of_description'`/`theorem10`/`theorem13_of` make it a pseudo-arc. If
   generalizing `real_step` to `E` is heavier than redoing it, a route through the plane —
   isometrically embedding the `(e₁, e₂)`-plane and taking products — is acceptable; the report
   records which.
7. **`exists_tame_chain_near`** — *the geometric lemma, expected to be the hard part*: for a compact
   continuum `g ⊆ E` (`dim E ≥ 2`) and `ε > 0`, a tame chain `D` with every link of diameter `< ε`,
   `D^* ⊆` the `ε`-neighbourhood of `g`, and every link meeting the `ε`-neighbourhood of … —
   precisely: `g ⊆ thickening ε D^*` and `D^* ⊆ thickening ε g`. (Then any continuum inside `D^*`
   meeting every link is within `2ε` of `g` in the Hausdorff metric.) This is Bing's broken line
   and chain of spheres with the global homeomorphism of batch 84's tameness attached. What is
   known: in dimension `≥ 3` a simple polygonal arc within `ε` of `g` exists by general position
   (connect an `ε`-net of `g` along a walk on a spanning tree of its `ε`-adjacency graph, then
   perturb to an embedding); in the plane the walk around a spanning tree must be drawn as a
   simple curve (the boundary of a thin neighbourhood of the tree), which is explicit but is
   plane geometry; in either case the tube around a polygonal arc has to be the image of the
   standard box chain under a homeomorphism of `E`, which means bending a straight tube at the
   corners by a homeomorphism — PL maps supported near each corner. Whether `IsTameChain` should
   be weakened to "image under an open embedding of a neighbourhood of the standard strip"
   (which is all `real_step` uses: uniform continuity on the compact coarse region, openness of
   images) is for the report to decide; it would remove the global-homeomorphism requirement
   from the geometric lemma without changing item 6. **If this lemma is not reached, leave it
   `sorry` with the obstruction stated and the partial constructions (the arc, the tube, the
   plane case, the `n ≥ 3` case) as proved lemmas; prove everything else from it.**
8. **`dense_pseudoArcs`** from 6–7, and **`theorem2_HIC`**: the pseudo-arcs are a dense `G_δ` in
   `Cont E`. The `G_δ` is unconditional (item 5); density depends on item 7.

Implicit hypotheses: `dim ≥ 2` (Bing: `n > 1`; in a line no nondegenerate continuum is a
pseudo-arc, so density fails); completeness of `S` for Baire (Bing's spaces are complete). The
skeleton assumes `[CompleteSpace E]` and `2 ≤ Module.rank ℝ E` (or `Module.finrank ≥ 2 ∨ infinite`;
state as is convenient, recording the form).

## 4. Deliverables

1. The statements of `Most51.lean`, `sorry`-free where achieved, with `#print axioms` in
   `axioms-batch90.txt`; reshaped statements recorded; any counterexample in Lean; for item 7,
   if open, the obstruction and the partial results.
2. Report: first line names the commission read; counterexamples first; then items 1–8 in
   order; item 7 in detail (which of the arc / chain-of-balls / tube-homeomorphism steps are
   done, in which dimensions).
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `theorem10_1951`.

## 5. Not in this batch

§5 of the paper (plane topology). With this batch the paper's §§1–4 are either machine-checked
or reduced to the geometric lemma of item 7.
