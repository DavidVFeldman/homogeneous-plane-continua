Commission read: COMMISSION-batch127.md (batch 127 — polygonal Janiszewski, part I: straight-line graphs, mod-2 cycles, parity, Mayer–Vietoris).

# Report, batch 127

**Outcome.** One refutation (of a skeleton statement as written, repaired by adding a hypothesis
that every later use already has); every item is **proved**. Nothing is open.

| item | verdict |
|---|---|
| refutation: `sum_vJump_even` without nondegeneracy | **refuted** (`not_sum_vJump_even_skeleton`); proved with `hnd : ∀ s ∈ G, s.1 ≠ s.2` |
| 1. graphs (`Seg`, `segSet`, `graphSet`, `vertices`, `IsProper`, `deg`, `IsCycle`, `exists_proper_subdivision`, `IsProper.subset`, `isClosed_graphSet`) | **proved**; `exists_proper_subdivision` as stated |
| 2. parity of a cycle (`cycParity`, `cycParity_symmDiff`, `sum_vJump_even`, `cycParity_locallyConstant`, `cycParity_eq_of_isPreconnected`, `cycParity_far`, `separatesPts_of_cycParity_ne`, `cycParity_flip`) | **proved**; `hnd` added to four statements (below); `cycParity_flip` as stated |
| 3. Mayer–Vietoris (`graph_connected_of_isConnected`, `exists_cycle_decomposition`) | **proved**, both as stated |
| 4. the conditional Janiszewski (`janiszewskiPoly_of_oddCycle`) | **proved**, as stated; the two `Prop`s `SeparatingGraphHasOddCycle`, `JaniszewskiPoly` unchanged |

Build: `lake build HPC` succeeds. No `sorry` in `HPC/Plane/Cyc1.lean`. `axioms.txt` regenerated (531 lines, 14 new);
`sorryAx` occurs in **one line**, `HPC.Plane.fugate_cor1` (unchanged). Per-batch audit:
`doc/batches/audits/axioms-batch127.{lean,txt}` (all 49 theorems of `HPC/Plane/Cyc1.lean`, plus
`fugate_cor1`; every theorem of the file shows exactly `[propext, Classical.choice, Quot.sound]`); the previous `axioms.txt` is saved as `doc/batches/audits/axioms-before-batch127.txt`.

Files:

* `HPC/Plane/Cyc1.lean` — new: the skeleton with every `sorry` replaced by a proof, plus the
  auxiliary statements listed below;
* edited as allowed: `HPC.lean` (`import HPC.Plane.Cyc1` at the end), `Axioms.lean` (group
  "Polygonal Janiszewski (batch 127)"), `axioms.txt`, `README.md` (batch count 127);
* housekeeping: the commission is `doc/batches/COMMISSION-batch127.md`, the skeleton
  `doc/batches/skeletons/Cyc1.lean`; `theorems-3-4-scheduling(33).md` contains all of
  `doc/theorems-3-4-scheduling.md` (it is a strict extension) and replaces it. Nothing is left at
  the root.

## Refutations first

The candidates named in the commission, in order:

1. **`IsProper`'s third clause with ordered pairs** — not refuted. With ordered pairs, `(a, b)` and
   `(b, a)` are distinct segments with the same point set; the second clause forbids both in a
   proper graph, and the third clause is then only invoked for distinct point sets. The subdivision
   normalises orientation lexicographically, so this never arises (below).
2. **`exists_proper_subdivision`'s last clause** — not refuted; proved as stated.
3. **`cycParity_flip`'s hypotheses** — not refuted; proved as stated. For a non-horizontal `s`,
   `hgen` makes the horizontal displacement work (no other segment meets a small horizontal
   segment through `p`, no vertex is at the height of `p`). For a horizontal `s`, only `hother` and
   `hpv` are needed: the vertical displacement and the vertex-jump calculus, with the even degrees
   killing the total jump and `s` contributing the extra `1` (it has exactly one end strictly right
   of `p` at the height of `p`). `hpv` is redundant in the non-horizontal case (implied by `hgen`).
4. **The form of `graph_connected_of_isConnected`** — kept as stated. The decomposition uses its
   `ZMod 2` form `exists_path_zmod` (which only needs `IsPreconnected`) and needs in addition
   `inter_subset_graphSet_inter`: *if `graphSet A ∩ graphSet B` is preconnected and has two
   distinct points, then it equals `graphSet (A ∩ B)`* (`A, B ⊆ K`, `K` proper). Proof: a common
   point on no common segment lies on distinct segments `e ∈ A`, `f ∈ B` of `K`, hence is a vertex
   of `K`; such a point `x` gives the closed cover `{x}`, `graphSet (A ∩ B) ∪ (vertices K \ {x})` of
   the intersection, both parts met, disjoint — contradiction. So isolated common vertices occur
   only when the intersection is a single point, as the commission expected.
5. **`exists_cycle_decomposition` when `graphSet A ∩ graphSet B` is a single point** — not
   refuted. The odd vertices of `Z ∩ A` lie in `graphSet A ∩ graphSet B` and are evenly many; at
   most one, hence none, and `Z_A = Z ∩ A`, `Z_B = Z \ A` work. In the proof this case needs no
   separate treatment: the walks are only requested for two *distinct* odd vertices.

**The actual refutation: `sum_vJump_even` as stated.** The skeleton's statement has no
nondegeneracy hypothesis, and it is false: `not_sum_vJump_even_skeleton` proves
`¬ ∀ G, (∀ w, Even (deg G w)) → ∀ x, ∑ s ∈ G, (vJump x s.1 + vJump x s.2) = 0` with
`G = {(a, a), (a, b), (b, b)}`, `a = (1, 0)`, `b = (2, 1)`, `x = (0, 0)`: `deg a = deg b = 2` (a
degenerate segment is counted *once* by `deg` but its jump *twice* in the sum, so it hides an odd
degree), and the sum is `vJump x a + vJump x b = 1`. The same graph breaks local constancy (only
`(a, b)` is ever crossed, so the parity jumps across the horizontal line through `a` to the left of
`a`), hence also `cycParity_eq_of_isPreconnected` and `separatesPts_of_cycParity_ne` in the
skeleton's form. **Repair:** `hnd : ∀ s ∈ G, s.1 ≠ s.2` is added to `sum_vJump_even`,
`cycParity_locallyConstant`, `cycParity_eq_of_isPreconnected`, `separatesPts_of_cycParity_ne`. A
cycle is proper, hence nondegenerate (`hZ.1.1`), so every use in this batch and the planned uses
in batches 128–129 supply it for free.

## Other changes of shape

* `vertices` is now `noncomputable def` (as written it fails to compile: `Finset.image` on
  `ℝ × ℝ` uses `Real.decidableEq`).
* `exists_proper_subdivision` is stated under `open Classical in` (the filter predicate
  `segSet t ⊆ segSet s` is not decidable); nothing else changes in its statement.

## Item 1: graphs and subdivision — the representation adopted

Segments stay **ordered pairs** (`Seg := Pt × Pt`), as in the skeleton. The subdivision is a
canonical, *intrinsic* one (`subdiv S`), with no sorting along segments:

* **cut points** `cutSet S`: the end points of the segments of `S`, and every point `q` such that
  `segSet s ∩ segSet u = {q}` for some `s, u ∈ S` (finite: each pair contributes at most one point,
  `cutSet_finite`);
* **pieces**: the pairs `(u, v)` of cut points with `toLex u < toLex v`, `segSet (u, v)` inside
  some `segSet s` (`s ∈ S`), and no cut point of `segSet (u, v)` other than `u`, `v`.

Then:

* *distinct pieces have distinct point sets* — a lexicographically increasing segment is
  determined by its point set (`lex_le_of_mem_segment`, `eq_of_segment_eq_lex`: the lex order is
  monotone along such a segment, so its lex-minimum and -maximum are its ends);
* *pieces meet only in common end points* (`subdiv_inter`): a common point which is a cut point is
  an end of both by the cut-point-free clause; a common point `z` which is not a cut point lies on
  `s ∩ s'` with `s ∩ s' ≠ {z}`, so there is a second common point `w`; all four ends are then on the
  line through `z`, `w` (`exists_lineMap_of_mem_segment`), and with parameters on that line the
  two pieces are parameter intervals containing `0` inside, none containing an end of the other
  inside, hence equal (`real_pair_eq`) — contradicting distinct point sets;
* *every point of `segSet s` lies on a piece inside `segSet s`* (`exists_piece`): parametrise
  `segSet s` by `[0, 1]`; the parameters of cut points form a finite set containing `0`, `1`; the
  point lies in a gap `[a, b]` between consecutive ones (`exists_gap`), and the oriented pair of
  the two cut points is a piece.

The last two clauses of `exists_proper_subdivision` and `graphSet G = graphSet S` follow from the
last fact. Collinear overlaps need no separate case.

## Item 2: parity of a cycle

`cycParity_symmDiff` is the general `sum_symmDiff_zmod2`. `sum_vJump_even` groups the sum by vertex:
`∑ s (vJump x s.1 + vJump x s.2) = ∑ w ∈ vertices G, deg G w • vJump x w` (nondegeneracy is what
makes the two sides agree), and each `deg G w` is even. `cycParity_locallyConstant`,
`cycParity_eq_of_isPreconnected`, `cycParity_far` are the `Jct1` proofs with `Fin n` replaced by
`G`; `separatesPts_of_cycParity_ne` applies `cycParity_eq_of_isPreconnected` to the component of
`x` in the complement. `cycParity_flip` is split into `cycParity_flip_horizontal_shift`
(non-horizontal `s`; `Jct2`'s `parity_flip_at`) and `cycParity_flip_vertical_shift` (horizontal
`s`; `Jct2`'s `parity_flip_vertical`, with `sum_vJump_even` in place of the telescoping).

## Item 3: Mayer–Vietoris

* `exists_path_zmod` (the content of `graph_connected_of_isConnected`): the set `W` of vertices
  `c` for which some `P ⊆ G` has odd set `{a} Δ {c}` contains `a` and is closed under edges
  (`P Δ {e}`); the segments with an end in `W` and the rest give two closed sets covering
  `graphSet G`, disjoint by properness (a common point is a common end); connectedness puts `b` in
  `W`.
* `exists_cycle_decomposition`: `X = Z ∩ A`, `Y = Z \ A ⊆ B`; the odd set `O` of `X` is even in
  size (`card_odd_vertices`), every `w ∈ O` is an end of a segment of `X ⊆ A` and of `Y ⊆ B`
  (since `deg X + deg Y = deg Z` is even); for two distinct points of `O`, the intersection is
  connected with two points, so it is `graphSet (A ∩ B)` (`inter_subset_graphSet_inter`), both
  points are vertices of `A ∩ B` (properness of `K`), and `exists_path_zmod` joins them in `A ∩ B`;
  `exists_join_all` sums such walks (strong induction on `O`, removing two points at a time) to a
  `P ⊆ A ∩ B` with odd set `O`; `Z_A = X Δ P`, `Z_B = Y Δ P`, and `Z_A Δ Z_B = X Δ Y = Z`.

## Item 4: `janiszewskiPoly_of_oddCycle`

As in the docstring: `K` the subdivision of `SA ∪ SB`; `A`, `B` the pieces inside `graphSet SA`,
`graphSet SB`; `graphSet A = graphSet SA`, `graphSet B = graphSet SB`
(`graphSet_filter_subdivision`, from the last clause of `exists_proper_subdivision`); `K ⊆ A ∪ B`;
the odd cycle `Z ⊆ K`; `Z = Z_A Δ Z_B`; by `cycParity_symmDiff` one of `Z_A`, `Z_B` has different
parities at `x`, `y`; `separatesPts_of_cycParity_ne` and monotonicity of separation
(`separatesPts_mono`) contradict the hypothesis on `SA` or `SB`. No change of shape of
`exists_cycle_decomposition` or `exists_proper_subdivision` was needed for this.

## Auxiliary statements added

`lex_le_of_mem_segment`, `eq_of_segment_eq_lex`, `exists_lineMap_of_mem_segment`,
`real_pair_eq(_aux)`, `mem_vertices`, `mem_graphSet`, `graphSet_mono`, `end_mem_graphSet`,
`sum_symmDiff_zmod2`, `symmDiff_subset_of`, `deg_cast`, `deg_symmDiff`, `deg_singleton`,
`deg_empty`, `exists_of_deg_ne_zero`, `even_iff_deg_cast`, `sum_deg_vertices`,
`zmod2_eq_zero_or_one`, `card_odd_vertices`, `cutSet`, `cutSet_finite`, `mem_cutSet_of_end`,
`subdiv`, `mem_subdiv`, `subdiv_inter`, `exists_gap`, `exists_piece`,
`not_mem_segSet_of_not_mem_graphSet`, `cycParity_eventually_eq`,
`cycParity_flip_horizontal_shift`, `cycParity_flip_vertical_shift`, `exists_path_zmod`,
`exists_join_all`, `inter_subset_graphSet_inter`, `separatesPts_mono`,
`graphSet_filter_subdivision`; and the refutation `not_sum_vJump_even_skeleton`.

## For batch 128 (the odd cycle of a separating graph)

* **Use `subdiv` / `exists_proper_subdivision` freely**; pieces are lex-oriented, so "the segment
  with point set `σ`" is unique in a proper graph, and `deg` counts each geometric edge once.
* **Nondegeneracy** is part of `IsProper`; every parity lemma here takes it as `hnd` (pass
  `hG.1.1` / `hZ.1.1`).
* **The candidate cycle** `Z = {e ∈ G | the component C of x in (graphSet G)ᶜ lies on exactly one
  side of e}` needs, at a non-vertex interior point `p` of `e`, the *two sides* of `e`: a small ball
  around `p` meets `graphSet G` only in `e` (other segments are closed and miss `p`; for that, `p`
  must avoid the finitely many vertices — the ball minus `e` is then two convex half-disks, as in
  `Jct2`'s `halfDisk`). Whether `C` meets a half-disk does not depend on `p ∈ e` (the half-disks
  at nearby points overlap), so "`C` on exactly one side of `e`" is well defined.
* **Even degree at a vertex `w`**: the segments at `w` cut a small ball around `w` into sectors
  (`Jct2`'s `polygon_local_rays` / `ball_diff_rays` handle two rays; the general case is `deg w`
  rays sorted by angle); each sector is preconnected and lies in a single component; going around
  `w`, membership in `C` changes exactly at the edges of `Z`, so their number is even. This is
  where most of the work of batch 128 will be; a cheaper route may be to *count* instead: the
  edges at `w` in `Z` are those whose two adjacent sectors differ in `C`-membership, and a cyclic
  sequence of booleans changes an even number of times.
* **Odd parity**: the parity of `Z` is locally constant off `graphSet Z` and *flips exactly across
  the edges of `Z`* (`cycParity_flip`); on a polygonal path from `x` to `y` in general position
  (crossing `graphSet G` at finitely many non-vertex points, never at a vertex height when the
  edge is not horizontal — exactly `cycParity_flip`'s hypotheses), `cycParity Z` changes at the
  crossings of `Z`-edges and only there, and the `C`-membership changes exactly at the same
  crossings (by the definition of `Z`); `x ∈ C`, `y ∉ C` gives an odd number of changes. A
  cleaner variant: show `{z ∉ graphSet G | cycParity Z z = cycParity Z x}` is *equal* to `C` near
  each edge, and conclude by connectedness, avoiding paths altogether.
* `graphSet` is closed (`isClosed_graphSet`), so its complement is open and its components are
  open — useful for the "component on a side" arguments.
