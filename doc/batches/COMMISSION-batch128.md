# Commission: batch 128 — polygonal Janiszewski, part II: a separating graph contains an odd cycle; `JaniszewskiPoly` proved

**Go!** Runs on top of the batch-127 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch128.md` — this text (also pasted into the prompt);
* `Cyc2.lean` — a skeleton, `sorry`s as work items (including the body of `sideRadius`, a `def`
  for you to design, and the marker `vertex_sectors_placeholder`, to be replaced by the sector
  lemma in the form you need). Save it as `HPC/Plane/Cyc2.lean`, add `import HPC.Plane.Cyc2` at
  the end of the root `HPC.lean`. Shapes may be adjusted with the change recorded. No existing
  file is to be edited except `HPC.lean`, `Axioms.lean`/`axioms.txt` (group "Polygonal
  Janiszewski (batch 128)"), `README.md` (batch count), `OPEN.md` (*Relative results*: note that
  `JaniszewskiPoly` is proved and that the field change is batch 129).

The report names the commission read in its first line; items *proved / refuted / open with the
obstruction stated*.

## 0. On batch 127

Audited and accepted: every item proved; my `sum_vJump_even` without nondegeneracy refuted
(`not_sum_vJump_even_skeleton` — a degenerate segment counted once by `deg` and twice in the jump
sum) and repaired with `hnd`, which every cycle supplies; the intrinsic lex-oriented subdivision;
`inter_subset_graphSet_inter` for the single-common-point case. 531 declarations, `sorryAx` in one
line, root tidy. Your notes for this batch are followed, including the path-free variant of the
odd-parity step.

## 1. Items

1. **Local structure at an edge** (`segDir`, `edge_local`, `sideRadius` — design —, `sideStrip`,
   `sideStrip_subset_compl`, `sideStrip_nonempty`, `sideStrip_isPreconnected`,
   `subset_or_disjoint_component`). `edge_local` is `Jct2`'s `polygon_local_chord` +
   `ball_diff_chord` with "other edges of the polygon" replaced by "other segments of `G`" (closed,
   missing `p` by properness and `hpv`). The side strip's radius function is yours; it must keep
   the half-disks inside `(graphSet G)ᶜ` and make the half-disks at nearby points of the open
   segment overlap, so that `isPreconnected_biUnion_of_local_meet` applies over the open segment.
2. **The odd set and its cycle property** (`oddSet`, `oddSet_subset`, the sector lemma replacing
   `vertex_sectors_placeholder`, `even_deg_oddSet`, `isCycle_oddSet`). This is the work of the
   batch. State the sector lemma in the form the counting needs; a cyclic enumeration of the edges
   at `w` by angle, sectors between consecutive ones, each sector preconnected and in
   `(graphSet G)ᶜ`, and the adjacency "the side strip of `eᵢ` on the appropriate side meets `σᵢ`"
   (and the other side meets `σ_{i−1}`). Then membership in `C` is a cyclic boolean sequence over
   the sectors, `eᵢ ∈ oddSet` iff the sequence changes between `σ_{i−1}` and `σᵢ`, and the number
   of changes around a cycle is even. Degree one: both sides of the single edge are in the one
   sector. Say in the report which angle machinery you used (`Complex.arg`, `Real.Angle`, or an
   ad-hoc ordering by cross products, which may be simpler for finitely many rays).
3. **The parity step, path-free** (`gFun`, `gFun_eq_across_edge`, `gFun_locallyConstant`,
   `gFun_const`, `cycParity_oddSet_ne`, `separatingGraphHasOddCycle`, `janiszewskiPoly_holds`).
   `gFun_const` needs the connectedness of the plane minus a finite set; Mathlib's
   `Set.Countable.isPathConnected_compl_of_one_lt_rank` is for a normed space of rank > 1, which
   `ℝ × ℝ` is (check the instance path; otherwise a direct argument: two points off a finite set
   are joined by a two-segment path through a third point avoiding the finitely many lines).

Report each item; refutations first (candidates: `edge_local`'s `∀ ρ' ≤ ρ` form; `oddSet`'s
definition via `⊆ C` of the whole strip — it relies on `subset_or_disjoint_component`, so a strip
that is not preconnected would break it; `gFun_eq_across_edge` at points where `cycParity_flip`'s
generic-point hypotheses fail — the docstring says how to avoid them).

## 2. Deliverables

1. Items 1–3; `#print axioms` in `doc/batches/audits/axioms-batch128.txt`; `axioms.txt`
   regenerated (`sorryAx` in one line).
2. Report: first line names the commission read; items in order; the sector lemma as proved; what
   batch 129 (the field change: `PlaneFacts.janiszewski` → polygonal compacta; the re-proof of
   `exists_theta_point` with `closure (h₁ ∩ h₂) ∩ frontier hᵢ`; `crosscut'`; the polygonality of
   those sets at the only call) should know — in particular the form in which "finite union of
   segments" should be stated so that `JaniszewskiPoly` applies directly (a `Finset Seg` with
   nondegenerate segments; degenerate ones, i.e. isolated points, can be dropped or doubled).
3. Housekeeping: uploads to `doc/batches/`, `doc/batches/skeletons/`; notes to `doc/`; nothing at
   the root.
4. Not attempted: batch 129, `enclose`, `fugate_cor1`, `treeLike_nonseparating`.
