# Commission: batch 127 — polygonal Janiszewski, part I: straight-line graphs, mod-2 cycles, parity, Mayer–Vietoris

**Go!** Runs on top of the batch-126 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch127.md` — this text (also pasted into the prompt);
* `Cyc1.lean` — a skeleton, `sorry`s as work items, two `def … : Prop` for later batches. Save it
  as `HPC/Plane/Cyc1.lean`, add `import HPC.Plane.Cyc1` at the end of the root `HPC.lean`. Shapes
  may be adjusted with the change recorded — in particular the representation of segments and
  graphs is yours to choose (see the header). No existing file is to be edited except `HPC.lean`,
  `Axioms.lean`/`axioms.txt` (group "Polygonal Janiszewski (batch 127)"), `README.md` (batch
  count).

The report names the commission read in its first line; items *proved / refuted / open with the
obstruction stated*.

## 0. On batch 126

Audited and accepted: `jct_polygon` verbatim, `planeFacts_of_enclose_janiszewski`, 517
declarations, `sorryAx` in one line, root tidy. The design simplification is noted with
appreciation: `local_side_of_split` applied to the parity split makes the vertex pieces and the
chord-ball chaining unnecessary — the local connectedness comes pointwise and the chaining from
the connectedness of Γ. The notes for part III are adopted; this skeleton follows them (parity as
an edge sum; the telescoping needs only even degrees; the flips at generic points with exactly the
hypotheses listed).

## 1. The plan and the change to the interface (announced now, executed in batch 129)

The field `janiszewski` will be weakened to **polygonal compacta** (`JaniszewskiPoly` in the
skeleton: `A`, `B` finite unions of closed segments). Its two uses are polygonal: `crosscut'`
(two simple closed polygons) directly; `exists_theta_point` after replacing `closure C ∩
frontier hᵢ` by `closure (h₁ ∩ h₂) ∩ frontier hᵢ` — the proof of batch 118 goes through verbatim
with these (a common point in `U` is a `q` with `q ∈ closure (h₁ ∩ h₂)`, which is the conclusion;
`frontier C ∩ U ⊆ A ∪ B` still holds; `S₂` misses `B ⊆ frontier h₂`; `S_V` misses
`A ⊆ closure (h₁ ∩ h₂)`), and at the only call `h₁`, `h₂` are polygon interiors
(`compFamily_no_circular`, members of `compFamily (polyInterior J) D` with `D` notched squares:
`component_inter_eq_polyInterior`), whose frontiers are simple closed polygons, so the two sets are
finite unions of segments (edge ∩ closure of an open polygonal region = finitely many closed
subsegments). Batch 129 does that re-proof and the field change; batches 127–128 prove
`JaniszewskiPoly`.

## 2. Items (this batch)

1. **Graphs** (`Seg`, `segSet`, `graphSet`, `vertices`, `IsProper`, `deg`, `IsCycle`,
   `exists_proper_subdivision`, `IsProper.subset`, `isClosed_graphSet`). The subdivision lemma is
   the one place with real bookkeeping: cut each segment at the finitely many points where it meets
   another segment's point set in a point or an end point lies on it; collinear overlaps are cut at
   all end points. If ordered pairs make "distinct segments have distinct point sets" awkward, use
   `Sym2 Pt` or normalise the orientation; record the choice.
2. **Parity of a cycle** (`cycParity`, `cycParity_symmDiff`, `sum_vJump_even`,
   `cycParity_locallyConstant`, `cycParity_eq_of_isPreconnected`, `cycParity_far`,
   `separatesPts_of_cycParity_ne`, `cycParity_flip`). All of it is `Jct1`/`Jct2` with the polygon
   replaced by an even-degree graph: `crossesEast_jump` is per edge; the only polygon-specific step
   was `sum_vJump_telescope`, whose generalisation is `sum_vJump_even` (group the sum by vertex:
   each vertex `w` at height `x.2` right of `x` contributes `deg G w` ones). The flip at a generic
   point: your `parity_flip_at` / `parity_flip_vertical` with `not_mem_polyEdge_of_ne` replaced by
   the hypothesis `hother`.
3. **Mayer–Vietoris** (`graph_connected_of_isConnected`, `exists_cycle_decomposition`). The
   docstrings carry the argument. The subtle point is that the segments of the proper `K` lying
   inside `graphSet A ∩ graphSet B` are exactly those of `A ∩ B` (a segment cannot be covered by
   finitely many others meeting it only at end points), so a connected `graphSet A ∩ graphSet B`
   with two points is `graphSet (A ∩ B)` possibly with… check whether isolated common vertices can
   occur in a connected intersection (they cannot, unless the intersection is a single point) and
   state `graph_connected_of_isConnected` in the form the decomposition needs.
4. **The conditional Janiszewski** (`janiszewskiPoly_of_oddCycle`), from the batch-128 statement
   `SeparatingGraphHasOddCycle` taken as a hypothesis. This fixes the interfaces between the three
   batches; if its proof wants a different shape of `exists_cycle_decomposition` or of
   `exists_proper_subdivision`, change them now.

Report each item; refutations first (candidates: `IsProper`'s third clause with ordered pairs;
`exists_proper_subdivision`'s last clause; `cycParity_flip`'s hypotheses; the form of
`graph_connected_of_isConnected`; `exists_cycle_decomposition` when `graphSet A ∩ graphSet B` is a
single point).

## 3. Deliverables

1. Items 1–4; `#print axioms` in `doc/batches/audits/axioms-batch127.txt`; `axioms.txt`
   regenerated (`sorryAx` in one line).
2. Report: first line names the commission read; items in order; the representation adopted;
   what batch 128 (the odd cycle of a separating graph: the sector structure at a vertex of a
   proper graph, the two sides of an edge, the general-position path from `x` to `y`) should know.
3. Housekeeping: uploads to `doc/batches/`, `doc/batches/skeletons/`; notes to `doc/`; nothing at
   the root.
4. Not attempted: batch 128's statement, batch 129's field change, `enclose`, `fugate_cor1`,
   `treeLike_nonseparating`.
