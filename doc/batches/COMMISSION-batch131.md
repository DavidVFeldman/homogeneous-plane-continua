# Commission: batch 131 — `enclose`, part II: the uniform path argument, `enclose_holds`, `planeFacts_holds`; Theorems 6 and 7 of Bing 1951 (Duke) unconditional; the interface retired

**Go!** Runs on top of the batch-130 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch131.md` — this text (also pasted into the prompt);
* `Enc2.lean` — a skeleton, `sorry`s as work items. Save it as `HPC/Plane/Enc2.lean`, add
  `import HPC.Plane.Enc2` at the end of the root `HPC.lean`. Shapes may be adjusted with the change
  recorded.

This batch **edits existing files** — the list in §2 is exhaustive: `HPC/Plane/Tree7Comp.lean`
(three renamings), `HPC/Plane/Tree67.lean` (one docstring), `HPC/Plane/Tree7.lean` (one comment),
`HPC.lean`, `Axioms.lean`/`axioms.txt`, `OPEN.md`, `README.md`, `LEDGER.md` (one line).

The report names the commission read in its first line; items *proved / refuted / open with the
obstruction stated*.

## 0. On batch 130

Audited and accepted: every item proved, no refutation; the three-file layout
(`Enc1Cyc`, `Enc1Grid`, `Enc1`); `bdryOf` by exclusive-or indexing with the skeleton's description
recovered as `mem_bdryGraph_iff_card`; the single characterisation
`mem_frontier_sqUnion_iff`/`mem_graphSet_bdryOf_iff` that makes the diagonal vertices a non-case;
`exists_enclosing_polygon` exactly as stated and needing only `IsContinuum M`. 611 declarations,
`sorryAx` in one line. Your "For batch 131" notes are followed to the letter: `Kᶜ ⊆ G` via
preconnected sets at distance `> 2δ` from `M` meeting the eastern half-plane. One housekeeping
slip: a copy of my notes, `theorems-3-4-scheduling(36).md`, sits at the repository root (it came
with the batch-130 upload) — move it to `doc/notes/` in this batch.

## 1. The argument (`Enc2.lean`)

The skeleton header has it in full. In short: `exists_enclosing_polygon` gives, for every mesh
`δ`, a polygon `J` with `M ⊆ polyInterior J ⊆ (outerComp M δ)ᶜ`, so `enclose` follows from
`Gᶜ ⊆ outerComp M δ` for one `δ`. A preconnected set at distance `> 2δ` from `M` is off the
boundary graph, so it lies in the outer component as soon as it meets it
(`subset_component_of_far`); the eastern half-plane is in it (`halfPlane_subset_component`, batch
130). With `M ⊆ ball 0 R`: the ray `eastRay R` and the outside of `closedBall 0 (R + 1)` are at
distance `≥ 1` from `M` and reach the half-plane; for the compact `Gᶜ ∩ closedBall 0 (R + 1)`
(inside `Mᶜ`, which is open and connected, hence path-connected — the one use of
`¬ SeparatesPlane M`), paths to `f₀ := (R + 1, 0)` thickened by half their gap to `M` give
finitely many preconnected pieces at a uniform distance `d > 0` from `M`, covering it
(`exists_far_piece`, `exists_uniform_pieces`); `δ := min d 1 / 3`.

Items:

1. **Uniform membership** (`outerComp`, `not_mem_graphSet_bdryGraph_of_far`,
   `subset_component_of_far`, `eastRay`, `isPreconnected_eastRay`, `one_le_infDist_eastRay`,
   `eastRay_subset_component`, `compl_closedBall_subset_component`). Sup metric throughout
   (`Prod.dist_eq`); `cthickening (2δ) M = {p | infEdist p M ≤ 2δ}` with `M` nonempty.
2. **Paths and their distance from `M`** (`joinedIn_compl_of_not_separates`,
   `exists_pos_infDist_le_of_disjoint`, `exists_far_piece`, `exists_uniform_pieces`). The first
   is Mathlib (`IsOpen.isConnected_iff_isPathConnected` in a `LocPathConnectedSpace`; a normed
   space is one — check the instance path for `ℝ × ℝ`; if it is missing, the direct argument on
   balls). `exists_uniform_pieces` is a finite subcover; the degenerate case `C = ∅` gives any
   `d`.
3. **`enclose`** (`exists_mesh_compl_subset`, `enclose_holds`, `planeFacts_holds`). Then the three
   unconditional theorems `theorem7_1951`, `theorem6_1951`, `theorem7_weak`, statements verbatim
   from `Tree7Comp.lean` minus `(hPF : PlaneFacts)`.

Report each item; refutations first (candidates: `compl_closedBall_subset_component` — the four
half-planes must each meet the eastern one *inside* `(graphSet (bdryGraph M δ))ᶜ`, which the
corners at `T > R + 1` guarantee; `exists_far_piece`'s `closedBall x r ⊆ P` with the bound
`r ≤ infDist p M` on the ball — the triangle inequality gives `infDist p M ≥ d - r = r` exactly,
so the bound is sharp and `≤` is the right inequality; `eastRay_subset_component` needs the ray to
meet `Ioi (gridR M δ) ×ˢ univ`, which it does at any `t > max (R + 1) (gridR M δ)`).

## 2. The edits

1. **`HPC/Plane/Tree7Comp.lean`**: rename `theorem7_1951 → theorem7_1951_rel`,
   `theorem6_1951 → theorem6_1951_rel`, `theorem7_weak → theorem7_weak_rel` (statements and proofs
   unchanged; docstrings gain the line "relative form; the unconditional theorem is
   `HPC.Plane.theorem7_1951` in `Enc2.lean` (batch 131)"). Fix the references (`HPCCensus.lean`,
   `HPCArchive.lean` if any; `Axioms.lean`). The internal `PlaneFacts.*` lemmas of `Tree6`, `Tree7`,
   `Tree7Comp`, `Tree7Cross` are **left relative** — `planeFacts_holds` instantiates them wherever
   needed; duplicating thirty statements buys nothing. Record this decision in the report.
2. **`HPC/Plane/Tree67.lean`**: the module docstring's "every theorem of §3 is proved relative to"
   gains "— discharged in batch 131: `planeFacts_holds` (`Enc2.lean`)". The structure itself stays
   (it is the honest record of what the §3 proofs use).
3. **`HPC/Plane/Tree7.lean`**, the comment on `treeLike_nonseparating`: add that `PlaneFacts` is
   now proved, so the question is unconditional; still open; not attempted.
4. **`Axioms.lean`**: new group "Enclosing polygon, part II; `PlaneFacts` discharged; Duke
   Theorems 6–7 unconditional (batch 131)" with every new theorem, in particular
   `planeFacts_holds`, `theorem6_1951`, `theorem7_1951`, `theorem7_weak`. The Duke §3 groups' notes
   ("relative to `PlaneFacts` …") replaced by "`PlaneFacts` proved in batch 131 (`planeFacts_holds`);
   the relative forms below are instantiated in `Enc2.lean`". `axioms.txt` regenerated (`sorryAx`
   in one line, `fugate_cor1`).
5. **`OPEN.md`**: the *Relative results* section emptied — keep the heading with one line: "None
   since batch 131: `PlaneFacts` is proved (`planeFacts_holds`); Theorems 6 and 7 of Bing 1951
   (Duke) are unconditional (`theorem6_1951`, `theorem7_1951`, `HPC/Plane/Enc2.lean`)". Item 2
   (`treeLike_nonseparating`) reworded: no longer relative to an interface.
6. **`README.md`**: the Duke paragraph: Theorems 6 and 7 proved outright (the Jordan curve theorem
   for polygons, the enclosing polygon and polygonal Janiszewski all proved in the repository,
   batches 125–131); batch count 131.
7. **`LEDGER.md`**: if any row mentions the interface as a caveat on Theorems 6–7, update it; else
   nothing.
8. Housekeeping: `theorems-3-4-scheduling(36).md` from the root to `doc/notes/`.

## 3. Deliverables

1. Items 1–3 and edits 1–8; `#print axioms` in `doc/batches/audits/axioms-batch131.txt`;
   `axioms.txt` regenerated.
2. Report: first line names the commission read; items and edits in order; the Mathlib lemmas
   used for path-connectedness and for the positive gap; the complete list of declarations that
   still take `(hPF : PlaneFacts)` (so that my notes can record which are internal).
3. Housekeeping: uploads to `doc/batches/`, `doc/batches/skeletons/`; notes to `doc/`; nothing at
   the root.
4. Not attempted: `fugate_cor1`, `treeLike_nonseparating`.
