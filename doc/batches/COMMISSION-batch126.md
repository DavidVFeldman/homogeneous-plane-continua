# Commission: batch 126 — `jct` part II: the two sides are connected; the field discharged

**Go!** Runs on top of the batch-125 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch126.md` — this text (also pasted into the prompt);
* `Jct2.lean` — a skeleton, `sorry`s as work items (including the body of `sideNbhd`, a `def` you
  are to design). Save it as `HPC/Plane/Jct2.lean`, add `import HPC.Plane.Jct2` at the end of the
  root `HPC.lean`. Shapes may be adjusted with the change recorded. No existing file is to be
  edited except `HPC.lean`, `Axioms.lean`/`axioms.txt` (group "Jordan curve theorem for polygons
  (batch 126)"), `OPEN.md`/`README.md` (§3).

The report names the commission read in its first line; items *proved / refuted / open with the
obstruction stated*.

## 0. On batch 125

Audited and accepted: part I complete, with the vertex rule in the form `crossesEast_jump` +
`sum_vJump_telescope` (cleaner than my horizontal-runs formulation), simplicity dropped where not
needed; Theorem 4 as printed proved for `m ≥ 4` — so Bing 1948 is now settled as printed in every
theorem, with Theorem 4's `m = 3` cases false. 498 declarations, `sorryAx` in one line.
Housekeeping below: the run left copies of `COMMISSION-batch125.md`, `Jct1.lean`,
`axioms-batch125.txt` and `theorems-3-4-scheduling(31).md` at the repository root.

## 1. The design (skeleton header)

Parity does the side-consistency, so no orientation of the polygon is needed: at a non-vertex point
of an edge the two half-disks have different parities (`parity_flip_edge`, every edge — your
"Notes for part II" give the horizontal case); at a vertex the two pieces of `ball_diff_rays` have
constant parity and contain the two half-disks of either edge, so they have different parities and
the odd piece contains the odd half-disk of both edges (`vertex_two_pieces`). The odd half-strips
and odd vertex pieces form a cyclic chain of connected sets with consecutive members meeting, so
their union `sideNbhd v 1` is connected; likewise for `0`. Every `x ∉ Γ` reaches a local piece of
its own parity by the segment towards `Γ` stopped at the first hit (`exists_first_hit`,
`exists_segment_to_boundary`). Hence each parity class is connected, its frontier is `Γ`, and
`jct_polygon` is the field verbatim.

## 2. Items

1. **Local structure at an edge** (`polygon_local_chord`, `halfDisk`, `halfDisk_convex`,
   `halfDisk_nonempty`, `ball_diff_chord`). `polygon_local_rays` (batch 118) at a non-vertex point
   gives two opposite rays; here the statement is the chord form. Use whichever is easier to
   derive from the other.
2. **The flip across every edge** (`parity_flip_edge`). Non-horizontal: as in `exists_parity_flip`
   but at the given `p` (or at a nearby point of the edge, then within the convex half-disks).
   Horizontal: your vertex-jump argument; state the lemma it needs on `crossesEast_jump` for a
   point lying on exactly one edge.
3. **The vertex** (`vertex_two_pieces`), from `polygon_local_rays`, `ball_diff_rays`,
   `parity_eq_of_isPreconnected` and item 2.
4. **First hit and the neighbourhood** (`exists_first_hit`, `exists_segment_to_boundary`,
   `sideNbhd` — design it —, `sideNbhd_subset`, `sideNbhd_isConnected`, `sideNbhd_near`,
   `exists_segment_to_sideNbhd`). The finite cover of the compact part of each edge outside the
   vertex balls by chord balls, and the chaining of consecutive convex half-disks, is the
   bookkeeping of the batch; `isPreconnected_biUnion_of_local_meet` (batch 118) may serve.
5. **The theorem** (`isConnected_parity_set`, `frontier_parity_set`, `jct_polygon`,
   `planeFacts_of_enclose_janiszewski`). `jct_polygon` must be the field's statement verbatim, so
   that `⟨jct_polygon, henc, hjan⟩ : PlaneFacts` typechecks as written.

Report each item; refutations first (candidates: the shape of `halfDisk` with the sup-metric ball;
`ball_diff_chord`'s radius quantification; `exists_segment_to_sideNbhd`'s reliance on how
`sideNbhd` is cut).

## 3. Housekeeping

* Move the stray root files of batch 125 to their places (`doc/batches/COMMISSION-batch125.md`,
  `doc/batches/skeletons/Jct1.lean`, `doc/batches/audits/axioms-batch125.txt`; the notes to
  `doc/theorems-3-4-scheduling.md`, replacing the older copy), and this batch's uploads likewise.
* `README.md`: "Theorems 6 and 7 are proved relative to the interface `PlaneFacts`" → add "whose
  field `jct` (the Jordan curve theorem for simple closed polygons) is proved in batch 126
  (`jct_polygon`); the fields `enclose` and `janiszewski` remain hypotheses
  (`planeFacts_of_enclose_janiszewski`)". Batch count 126. Bing 1948 line: Theorem 4 as printed
  proved for `m ≥ 4`, false for `m = 3`.
* `OPEN.md` "Relative results": the same note on `jct`.

## 4. Deliverables

1. Items 1–5; `#print axioms` in `doc/batches/audits/axioms-batch126.txt`; `axioms.txt`
   regenerated (`sorryAx` in one line).
2. Report: first line names the commission read; items in order; the definition of `sideNbhd`
   adopted; anything part III (polygonal Janiszewski by mod-2 cycles, batches 127–129) should
   know about the parity machinery as built.
3. Not attempted: `enclose`, `janiszewski`, `fugate_cor1`, `treeLike_nonseparating`.
