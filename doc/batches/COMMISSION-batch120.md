# Commission: batch 120 — Bing 1951 (Duke), Theorem 7, part II: the components are polygon interiors; `theorem7_1951`

**Go!** Runs on top of the batch-119 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch120.md` — this text (also pasted into the prompt);
* `Tree7Comp.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/Tree7Comp.lean` and add `import HPC.Plane.Tree7Comp` at the end of the root `HPC.lean`.
  Shapes may be adjusted with the change recorded. No existing file is to be edited except
  `Axioms.lean`/`axioms.txt` (group "Bing 1951 (Duke) §3, Theorem 7 — relative to `PlaneFacts`
  (batch 120)").

The report names the commission read in its first line. Housekeeping, this batch: delete the stray
`theorems-3-4-scheduling(23).md`, `(24).md`, `(25).md` at the repository root (my notes file is not
part of the repository; its current copy goes to `doc/theorems-3-4-scheduling.md`, replacing the one
there, if the file is uploaded with the run — otherwise just delete the strays).

## 0. On batch 119

Audited: items 1–4 proved, nothing refuted, item 5 open with the obstruction stated — accepted, and
the obstruction (no separation tool in `PlaneFacts` that applies to unions of non-connected open
links) is recorded in my notes with the Borsuk/Čech remark. The corrections to my outline
(`enclose` applied to a thickening of `M`; bad translations on lines; `local_side` not needed in
`crosscut`) are recorded. 401 declarations, `sorryAx` in two.

## 1. The task, and a simplification

`theorem7_1951`: links `polyInterior Γ` with `Γ` a simple closed polygon. The plan of batch 119 §4
asked for the crossing structure of `notchedPoly` against `J` in general position — transversal
crossings, `notchedPoly` passing from inside to outside at each. **None of that is needed.** The
cross-cut induction goes through for cross-cuts that meet only at common ends (the condition
`c ∩ c' ⊆ J` in `IsCrosscutFamily`): when `polyInterior J` is split along `c₁`, a cross-cut `c₂`
sharing an end `a` with `c₁` still has `c₂ \ ends` connected inside `polyInterior J \ c₁`, hence on
one side; it meets `α₁ ∪ c₁` only in `(c₂ ∩ J) ∪ (c₂ ∩ c₁) ⊆ ends`; `a ∈ c₁` and the other end lies
in `closure U₁ ∩ J = α₁` (the closure clause of `crosscut`, which is why it was asked for). The
pieces of `P` between consecutive points of the finite set `X = J ∩ P` meet pairwise in `X ⊆ J`, so
they form such a family without any analysis of what happens at a shared point. The three
degenerate cases (`P ∩ U = ∅`; `X = ∅`; `X` a single point) are settled by connectedness alone, as
in the docstring of `component_inter_eq_polyInterior`. General position therefore enters only as
`finite_inter_of_gp`, and the main theorem is stated for two simple closed polygons `J`, `P` with
`(J ∩ P).Finite`.

Ledger consequence: Bing's "interiors of simple closed curves" is established for any two polygons
whose boundaries meet in finitely many points, which the translation of batch 119 arranges.

## 2. Items

1. **Cross-cut families and the induction** (`IsCrosscut`, `IsCrosscutFamily`,
   `connectedComponentIn_union_of_disjoint_open`, `IsCrosscut.of_side`,
   `PlaneFacts.components_of_crosscuts`). The docstring of `components_of_crosscuts` is the proof;
   the induction is on `C.card` (strong induction, or `Finset.strongInduction`), splitting by any
   `c ∈ C`. The clause `Γ ⊆ J ∪ ⋃ C` is not used later; keep it if it costs nothing, drop it with a
   note otherwise. The shape of `IsCrosscut.of_side` is a suggestion (its `hside` is awkward: the
   ends of `c'` are determined by `c'` up to order, but the predicate carries them existentially);
   restate it as convenient.
2. **Decompositions** (`exists_arc_decomposition`, `exists_polygon_decomposition`). Induction on
   the finset of cut points with `IsSimplePolyArc.split` (batch 118) and `split_two` (batch 119).
   The clause `γ ∩ (X ∪ {p, q}) = {s, t}` is what makes a piece minus its ends miss the cut points.
3. **The cross-cut family of `P` in `J`** (`PlaneFacts.exists_crosscutFamily`): as in the docstring.
   `hfin.toFinset.card` is one way to say `|X| ≥ 2`; use whatever form the case split of item 4
   produces.
4. **Identification and the main theorem** (`subset_of_isConnected_of_disjoint_frontier`,
   `PlaneFacts.connectedComponentIn_inter_eq`, `PlaneFacts.component_inter_eq_polyInterior`). The
   degenerate cases are written out in the docstring; the `|X| = 1` case needs "a simple closed
   polygon minus one point is connected" (split at that point and another; an arc minus one end is
   connected, e.g. from `isConnected_diff_ends` and `IsPreconnected.subset_closure`).
5. **Theorem 7** (`isSimpleVertices_notchedVertices`, `finite_inter_notchedPoly_of_gp`,
   `theorem7_1951`). Assembly as in the docstring. If `isSimpleVertices_notchedVertices` is already
   in `Tree7Notched` under another name, use it and say so.

Report each item *proved / refuted / open with the obstruction stated*; refutations first (the
candidates: the `c ∩ c' ⊆ J` clause — I believe the induction needs nothing more; the degenerate
cases; the `X = ∅` argument in the docstring). `PlaneFacts` is a hypothesis, so `sorryAx` stays at
two unless an item is left `sorry`; if `theorem7_1951` cannot be finished, leave it as a stated
`sorry` in the "Open targets" group and say exactly which lemma is missing.

## 3. Deliverables

1. Items 1–5; `#print axioms` in `axioms-batch120.txt`; `axioms.txt` regenerated.
2. Report: first line names the commission read; items in order; the ledger note for Theorem 7 in
   final form — (a) the assertion "components of `d₀ · dᵢ` are interiors of simple closed curves"
   is unargued by Bing, true in general (informal), and established here for boundaries meeting
   finitely often, which a translation arranges; (b) the hypothesis "tree-like" versus
   "no separating subcontinuum", open relative to `PlaneFacts`, `theorem7_1951` stated with the
   latter; (c) with Theorem 7 the §3 of the Duke paper is checked relative to `PlaneFacts`.
3. `README.md`: Duke "Theorems 1–16" with the note that 6 and 7 are relative to the interface
   `PlaneFacts` (jct for polygons, enclosing polygon, Janiszewski for compacta), and the batch
   count; `OPEN.md`: the two live items unchanged, and a line under the closed-items table or a
   new section "Relative results" listing `theorem6_1951`, `theorem7_1951` and the interface. If
   `README.md`/`OPEN.md` edits are out of scope for this run, say so and I will commission them.
4. Not attempted: `theorem3_end`, `fugate_cor1`, `treeLike_nonseparating`.

## 4. Next

To be decided (David): discharging `PlaneFacts` (proof or import), Fugate Cor 1, `theorem3_end`
reconnaissance, or the Pacific paper's §5.
