Commission read: `COMMISSION-batch111.md` — batch 111, housekeeping after the density lemma.

# Report, batch 111

Nothing new was proved or refuted. The batch-90 open statement `exists_tame_chain_near` and its two
consequences were deleted from `HPC/Plane/Most51.lean`. The open target is now the weaker statement
`geomLemma'_of_two_le_rank` in `HPC/Plane/LatticeCycle.lean`. `dense_pseudoArcs` and `theorem2_HIC`
were added back there with their old statements, and `theorem2_1951` (Duke Theorem 2, general `E`)
is new; all three are proved from the new open target. The audit groups, the ledger, `OPEN.md`,
the README and the notes were updated.

* `lake build HPC` succeeds (8293 jobs). It gives exactly five `declaration uses sorry` warnings:
  `theorem3_end` (`HPC/Fold/Theorem4.lean`), `covering_step` and `theorem14`
  (`HPC/PseudoArc/Theorem14.lean`), `geomLemma'_of_two_le_rank` (`HPC/Plane/LatticeCycle.lean`)
  and `fugate_cor1` (`HPC/Plane/Fugate66.lean`).
* `lake build HPCArchive HPCCensus` succeeds (8242 jobs). Nothing broke. `HPC/Archive/Most51Geom.lean`
  never used the deleted theorem in Lean code; only its header was changed.

## 1. Edits

### Item 1(a): deletions in `HPC/Plane/Most51.lean`

* The following were deleted: `exists_tame_chain_near` (open, `-- OPEN`), `dense_pseudoArcs` and
  `theorem2_HIC` (both proved from it).
* The following stay, proved: `IsTameChain`, `GeomLemma`, `exists_pseudoArc_in_tameChain`,
  `dense_pseudoArcs_of`, `theorem2_HIC_of`. In `Band.lean`, `geomLemma'_of_geomLemma` and the
  primed forms are unchanged.
* The docstring of `GeomLemma` used to point to the deleted theorem. It now states the hypothesis
  directly and refers to `LEDGER.md` §2 and to `geomLemma'_of_two_le_rank`.
* The archive file `HPC/Archive/Most51Geom.lean` stays. Its header named the deleted theorem as
  "stays open". It now says that the statement was deleted in batch 111 and replaced by
  `geomLemma'_of_two_le_rank`, and that the archive names containing `exists_tame_chain_near`
  refer to the conclusion of `GeomLemma`.

### Item 1(b): additions in `HPC/Plane/LatticeCycle.lean`

These were added after the plane theorems, in a new section *General `E`*:

* `geomLemma'_of_two_le_rank`: the statement and docstring exactly as commissioned, marked
  `-- OPEN (see OPEN.md)`, with proof `sorry`.
* `dense_pseudoArcs` and `theorem2_HIC`: the same statements as the deleted ones, now proved from
  `geomLemma'_of_two_le_rank` through `dense_pseudoArcs_of'` and `theorem2_HIC_of'`.
* `theorem2_1951`: the commission left its proof as `...`. The proof used is
  `⟨(dense_pseudoArcs hdim).mono fun _ hK => hK.1, isGδ_snakeLike⟩`, the same as for
  `theorem2_1951_plane`.

The module docstring gained a short *Batch 111* paragraph.

### Item 1(c): `OPEN.md` item 4

Item 4 was rewritten for `geomLemma'_of_two_le_rank`. It contains:
* the statement;
* what depends on it: `dense_pseudoArcs`, `theorem2_HIC`, `theorem2_1951`;
* what is known: the plane case (`geomLemma'_of_finrank_two`, batches 109–110), the route of 1(b)
  for dimension `≥ 3` and for Hilbert space, the batch-90 partial results in the archive, and the
  deletion of the former statement (`LEDGER.md` §2).

### §2: audit groups (`Axioms.lean`)

* *Open targets*: `exists_tame_chain_near` was replaced by `geomLemma'_of_two_le_rank`.
* *Consequences of open targets*: `dense_pseudoArcs`, `theorem2_HIC` and `theorem2_1951`, each
  marked "from geomLemma'_of_two_le_rank".
* *Refutations (ledger certificates)*: four skeleton refutations were added, under comments
  marking them as commission slips:
  * `not_squeeze_stdRect_subset` (batch 107). It was not listed anywhere in `Axioms.lean` before,
    so it is a new line.
  * `stripSet_zero_ne`, `stretchTri_subset_ball_false`, `stretchTri_subset_thickening_false`
    (batch 109). These were moved here from the *Bing 1951 (Pacific)* group.

### §2: `LEDGER.md`

* §1 has a new table, *Commission slips: skeleton refutations (batches 107, 109)*. It has four
  rows, each giving the skeleton claim, why it is false and the Lean certificate. The corrected
  forms are `squeeze_image_stdRect_subset`, `stripSet_eq` (with `0 < m`), `stretchTri_subset_ball`
  (with `k ≤ n`) and `stretchTri_subset_thickening` (with `0 < n`).
* §2 is retitled *Deleted statements that are not refuted (batches 103 and 111)*. A new table,
  *Statements deleted in batch 111*, covers the three deletions of item 1(a). The introductory
  paragraph of the ledger was adjusted to match.

### §3: documentation

* `README.md`: the paper list was updated:
  * Pacific: "including Theorem 2 in the plane";
  * new line for Bing 1948 (Amer. J. Math.), *Some characterizations of arcs and simple closed
    curves*: Theorem 5 and Corollary 2;
  * Duke 1951: "including Theorem 2 in the plane and Theorem 5".

  The batch count changed from 105 to 111. The `doc/sources/` row now mentions the arcs paper. The
  sentence saying that `axioms.txt` is the only claim is unchanged.
* `doc/theorems-3-4-scheduling.md` was replaced by the copy uploaded with this commission,
  `theorems-3-4-scheduling(17).md` (3796 lines; the newest of the three root copies). The stray
  root copies `theorems-3-4-scheduling(15).md` and `(16).md` were deleted. `(17).md` was also
  removed from the root once copied, so that no stray copy is left.
* `HPC/Plane/Most51.lean` header: the batch-90 paragraph now lists only what is still in the file.
  A new paragraph, *What is now proved, and where (batch 111)*, covers:
  * the plane: `geomLemma'_of_finrank_two`, `theorem2_HIC_plane`, `theorem2_1951_plane`, all in
    `LatticeCycle.lean`;
  * general `E`: open, as `geomLemma'_of_two_le_rank`;
  * the archive file of partial results.

  The old header also gave the wrong path for `Most51Geom.lean` (it is in the archive); this was
  corrected.
* `COMMISSION-batch111.md` was moved to `doc/batches/`, like the earlier commissions.

## 2. Audit

* `axioms.txt` was regenerated (`lake env lean Axioms.lean > axioms.txt`). It has **282 lines**,
  one per declaration, up from 280 before this batch. The difference:
  * +1 `theorem2_1951`;
  * +1 `not_squeeze_stdRect_subset`, newly listed;
  * `exists_tame_chain_near` replaced by `geomLemma'_of_two_le_rank`;
  * the three batch-109 refutations moved, not added.
* `sorryAx` occurs in exactly **10** lines, not 9. The commission expected the count to stay at 9,
  but its own arithmetic gives 10: one open target replaced by one, and three consequences instead
  of two. The ten are:
  * Open targets (5): `HPC.Fold.theorem3_end`, `HPC.Description.covering_step`,
    `HPC.Description.theorem14`, `HPC.Plane.geomLemma'_of_two_le_rank`, `HPC.Plane.fugate_cor1`.
  * Consequences (5): `HPC.Description.theorem15`, `HPC.Description.exists_description_covering`,
    `HPC.Plane.dense_pseudoArcs`, `HPC.Plane.theorem2_HIC`, `HPC.Plane.theorem2_1951`.

  Every other line shows `[propext, Classical.choice, Quot.sound]` or a subset of it.
* `doc/batches/audits/Axioms111.lean` / `axioms-batch111.txt` cover every touched declaration:
  * the four declarations of item 1(b), with `sorryAx`;
  * `GeomLemma`, `dense_pseudoArcs_of`, `theorem2_HIC_of`, which stay in `Most51.lean`, with
    standard axioms;
  * the four moved refutations, with standard axioms.

## 3. Files touched (line counts after the batch)

| file | lines | change |
|---|---|---|
| `HPC/Plane/Most51.lean` | 490 | deletions of item 1(a); header |
| `HPC/Plane/LatticeCycle.lean` | 449 | additions of item 1(b); module doc |
| `HPC/Archive/Most51Geom.lean` | 526 | header only |
| `Axioms.lean` | 372 | groups (§2) |
| `axioms.txt` | 282 | regenerated |
| `LEDGER.md` | 197 | §1 four entries, §2 three entries |
| `OPEN.md` | 86 | item 4 rewritten |
| `README.md` | 81 | paper list, batch count, layout |
| `doc/theorems-3-4-scheduling.md` | 3796 | replaced by the newest upload |
| `doc/batches/audits/Axioms111.lean` | 15 | new |
| `doc/batches/audits/axioms-batch111.txt` | 11 | new |
| `doc/batches/REPORT-batch111.md` | — | this report (new) |
| `doc/batches/COMMISSION-batch111.md` | 105 | moved from the root |
| `theorems-3-4-scheduling(15).md`, `(16).md`, `(17).md` | — | deleted from the root |
