Commission read: `COMMISSION-batch116.md` (batch 116 — housekeeping after Theorem 14).

# Report, batch 116

**Outcome.** Housekeeping only: nothing new was proved or refuted, and no Lean statement changed.
Every edit to a `.lean` file is to a comment or module docstring, apart from `Axioms.lean`, which
gained `#print axioms` lines. `lake build HPC HPCArchive HPCCensus` succeeds; the only
`declaration uses sorry` warnings are the two open targets `theorem3_end` and `fugate_cor1`.
`axioms.txt` is regenerated: 349 lines (316 before), with `sorryAx` in exactly two lines,
`HPC.Fold.theorem3_end` and `HPC.Plane.fugate_cor1`.

## Files touched

* `OPEN.md` (item 1.1)
* `LEDGER.md` (item 1.2)
* `README.md` (item 1.3)
* `Axioms.lean`, `axioms.txt` (item 1.4)
* `HPC/Plane/BandN.lean`, `HPC/Plane/Most51.lean`, `HPC/Archive/Most51Geom.lean`,
  `HPC/PseudoArc/Theorem14.lean`, `HPC/PseudoArc/Recon86.lean` (item 1.5; prose only)
* `doc/theorems-3-4-scheduling.md` replaced by the uploaded copy; the root copies
  `theorems-3-4-scheduling(20).md`, `(21).md` and `(22).md` deleted (item 1.6; see below)
* filed: `doc/batches/COMMISSION-batch116.md` (moved from the root),
  `doc/batches/audits/axioms-before-batch116.txt` (the previous `axioms.txt`),
  `doc/batches/audits/axioms-batch116.txt` (this batch's audit), this report.

## 1.1 `OPEN.md`

The two live items are now `1` (`HPC.Fold.theorem3_end`) and `2` (`HPC.Plane.fugate_cor1`); their
text is unchanged. The three "closed in batch …" stubs are replaced by a section *Closed items* at
the end: a table giving the former statement, its former item number, the batch that closed it and
the theorem that now proves it (`covering_step` by `HPC.lehner_lemma3_two`, batch 114; `theorem14`
by `HPC.Description.theorem14` in `Thm14.lean`, batch 115; `geomLemma'_of_two_le_rank` in
`CubeCycle.lean`, batch 113), plus one sentence on the former consequences. The header paragraph
now says the group *Consequences of open targets* is empty and that the items were renumbered in
batch 116.

Two source comments cited the old numbers: `HPC/PseudoArc/Theorem14.lean` ("OPEN.md item 3") now
says "item 3 of OPEN.md before batch 116"; `HPC/Plane/BandN.lean` ("OPEN.md item 4") is rewritten
under item 1.5. `HPC/Plane/CubeCycle.lean` ("That closes OPEN.md item 4") is a historical statement
of batch 113 and is left as it is.

## 1.2 `LEDGER.md`: the new section, as written

The header paragraph gains a clause naming section 5. §1 (refuted statements) has no new entry;
§2–§4 keep their numbers. The new section, verbatim:

> ## 5. Bing 1948, Theorems 9 and 14, and Lehner 1961
>
> Batch 116 (COMMISSION-batch116.md §1.2); the proofs are those of batches 114 and 115
> (REPORT-batch114.md, REPORT-batch115.md). Nothing in this section is a refutation, and §1 has no
> new entry.
>
> **The covering descriptions.** Theorem 14 says: "That there exist such sequences follows as a
> consequence of Theorem 9." This is not a proof. The sequences (descriptions whose levels cover `W`
> from `P'` to `R`) are supplied by Lehner's Lemma 3 for `n = 2` (G. R. Lehner, *Extending
> homeomorphisms on the pseudo-arc*, Trans. AMS 98 (1961), pp. 375–376), proved in batch 114 as
> `HPC.lehner_lemma3_two` (`PseudoArc/Lehner.lean`): one level is crooked in the previous one, and
> Lehner's chain counting is carried out on that. The batch-86/87 reformulations through folds
> (`Description.coveringStep_of_folds`, `Description.coveringStep_of_folds₃`, and the end-time lemma)
> are not the route. Their refutations (`model_covering_fold_refuted`, `model_covering_fold₃_refuted`,
> `model_end_time_refuted`, §1 *Models of the open items*) stand as refutations of those
> reformulations and say nothing against Theorem 14.
>
> **Two further assertions of the sketch.** Two of the sketch's assertions are **not established for
> an arbitrary covering description**:
> 1. there is a point `A` with `X_{1,j}(P_1, A)` inside `Y_{1,1}(P_1, R_1)`, and the closure of
>    `x(1,j)_A` lies inside `y(1,1)_{P_1}`;
> 2. the finer covering part lies inside the coarser one (`Y_{2,2}(P_2, R_2) ⊆ Y_{2,1}(P_2, R_2)`).
>
> They are established for the description that Lehner's construction gives, which also keeps its
> covering part within `1/(i+1)` of `W` and has a return point (`CoversUpToA`,
> `Description.exists_description_coveringA`, `PseudoArc/Thm14.lean`, batch 115). No refutation of
> either assertion for arbitrary covering descriptions was proved, so they are recorded here as "not
> established", not as false.
>
> **Steps of the three-piece assembly that the sketch leaves out** (REPORT-batch115.md, *Ledger*,
> list 1–9, in brief):
> 1. on the stretch `R → A` Theorem 5 is needed with a decreasing pattern; it is obtained by
>    reversing the coarse chain, since the proof of Theorem 5 does not need that chain to be a level
>    or to run from `P` to `Q` (`Description.theorem5_gen`, `PseudoArc/T5Gen.lean`);
> 2. the three applications of Theorem 5 must land at one level; Theorem 5 holds at every deep
>    enough level;
> 3. the fine links meeting a junction link land in the correct end link of each piece (a clause of
>    Theorem 5's construction, not of its statement; added to `T5.assemble`);
> 4. the glued chain is a chain: cross-intersections only at the junction links, and the stretches
>    `P → R` and `A → Q` are disjoint (`Chain.threePiece`, `PseudoArc/T14Glue.lean`);
> 5. the glued chain runs from `P` to `Q` with `P`, `R` only in the links `0` and `ρ'` of its first
>    part (uses `R ∉ c_0`, `P ∉ c_ρ`, `Q ∉ c_0`);
> 6. `W` lies in that first part;
> 7. the junction links of the deep level satisfy `ρ_a ≥ 1`, `ρ_a + 2 ≤ α < n_a − 1`, with closures
>    in the right coarse links, once the mesh is small compared with `dist P R`, `dist P Q` and the
>    radii of balls about `P`, `R`, `Q`;
> 8. the base rung needs a pattern tracking the `R`-indices from a fine level of one description to
>    a coarse level of the other (uses `P₁ ≠ R₁ ≠ Q₁`);
> 9. the new `R`-index of every rung is positive (mesh below `dist P R`).
>
> **Theorem 9 and Lehner's Theorem 1.** Lehner's Theorem 1 is Bing's Theorem 9, re-proved "at the
> request of Professor Bing" because the original "has presented some readers with difficulty"
> (Lehner, p. 370). The repository's `HPC.Fold.theorem9` (`Fold/Theorem7.lean`, batch 82) is proved as
> Bing states it, without Lehner's end clause.

## 1.3 `README.md`

* Paper list: Bing 1948 now reads "Theorems 1–15 (Theorem 3 without its end-link clause)"; a new
  entry for G. R. Lehner, *Extending homeomorphisms on the pseudo-arc* (Trans. AMS 98, 1961):
  Lemma 3 for `n = 2`.
* After the Theorem 11 sentence, the commissioned sentence on Theorem 14
  (`HPC.Description.theorem14`, `HPC/PseudoArc/Thm14.lean`).
* Layout table: "the 111 batches" → "the 116 batches". The `doc/sources/` row is unchanged (the
  Lehner scan is not in the repository).

## 1.4 `Axioms.lean` and `axioms.txt`

The group *Consequences of open targets* keeps its header and its "(none …)" line.

Check of batches 113–115: for every name in backticks in `REPORT-batch113.md`,
`REPORT-batch114.md` and `REPORT-batch115.md` that is a theorem of the repository, I checked whether
it has a `#print axioms` line. Theorems that were new in those batches and were missing are now
listed (33 lines):

* **Batch 113** (in the group *density lemma, batch 113*): `HPC.Plane.CubeLoopAux.fwd_edge`,
  `CubeLoopAux.exists_isOpenedLoop`, `CubeLoopAux.exists_two_free_edges`,
  `HPC.Plane.exists_cubeLoop_ge`, `HPC.Plane.CCyc.side_eq`, `CCyc.pair_eq`, `CCyc.A_tr_opp`,
  `CCyc.B_tr_opp`, `CCyc.inv_rot`, `CCyc.inv_splice`, `CCyc.inv_base`, `CCyc.inv_grow`,
  `CCyc.exists_inv_sub`, `CCyc.exists_inv`, `HPC.Plane.exists_latticeCycleN_of_loop`.
* **Batch 114** (Bing 1948 group, after `exists_description_covering`): `HPC.lehner_lemma3_two`,
  `HPC.isPseudoArc_of_subcontinuum`, `HPC.not_mem_composant_of_irreducible`,
  `HPC.exists_epsChain_of_irreducible`, `HPC.Chain.IsConsolidationOf.trans`,
  `HPC.exists_description_consolidating`, `HPC.Lehner.exists_eq_of_lip`,
  `HPC.Lehner.dist_le_of_near`, `HPC.Lehner.blocks`, `HPC.Lehner.indices`, `HPC.Lehner.core`.
  (`lehner_lemma3_two` itself, the main result of batch 114, was missing.)
* **Batch 115** (Bing 1948 group, after `exists_homeomorph_tracked`): `HPC.lehner_lemma3_twoA`,
  `HPC.Description.exists_description_of_steps'`, `HPC.Chain.exists_link_le_of_subset_span`,
  `HPC.Carries.pos_of_lt`, `HPC.exists_tracked_refinement`, `HPC.TRung.exists_base`,
  `HPC.TRung.exists_next`.

Not added: theorems of earlier batches that these reports merely cite (for example
`Description.link_inter_M_nonempty`, `ne_M_and_not_mem`, `Chain.meet_ordConnected`,
`IsSchedule.exists_blockMap`, `exists_description_of_steps`, `theorem5_of`, `exists_irreducible`,
the `L_*` lemmas of `LatticeCycleAux.lean`), and `T5.assemble`, a batch-79 theorem whose
conclusion batch 115 extended.

`axioms.txt` is regenerated with `lake env lean Axioms.lean > axioms.txt`: 349 lines (316 + 33).
`sorryAx` occurs in exactly two lines: `HPC.Fold.theorem3_end` and `HPC.Plane.fugate_cor1`. Every
other line shows `[propext, Classical.choice, Quot.sound]` or a subset of it.

## 1.5 Module docs

Prose only; no statement changed.

* `HPC/Plane/BandN.lean`: "Towards the open `geomLemma'_of_two_le_rank` (OPEN.md item 4)" now says
  "(then open)", with a batch-116 note: the lemma is proved in every dimension `≥ 2` in batch 113
  (`CubeCycle.lean`), and both halves of this file are used there (`CubeLoop.lean` imports this file;
  `CubeCycle.lean` uses `exists_threadedChain_of_latticePathN` and `geomLemma'_of_subspaces`).
* `HPC/Plane/Most51.lean`: the bullet *General `E`* (formerly "open, as `geomLemma'_of_two_le_rank`
  in `LatticeCycle.lean`") now says it is proved in batch 113 in `CubeCycle.lean`, together with
  `dense_pseudoArcs`, `theorem2_HIC` and `theorem2_1951`. The docstring of `GeomLemma` ("its open
  case is …") now says the general case is proved in batch 113.
* `HPC/Archive/Most51Geom.lean`: "replaced by the weaker open `geomLemma'_of_two_le_rank`
  (`LatticeCycle.lean`; …)" now says it is proved in every dimension `≥ 2` (batch 113,
  `CubeCycle.lean`).
* `HPC/PseudoArc/Theorem14.lean`: the title now reads "Theorems 14 and 15: preliminaries;
  irreducible subcontinua", and a new opening paragraph says that Theorems 14 and 15 are proved in
  `Thm14.lean` (batch 115), with the covering descriptions from Lehner's Lemma 3 (`Lehner.lean`,
  batch 114). The batch-83 status sentence is put in the past tense. The note at the end of the
  file cites the old OPEN.md number as "before batch 116".
* `HPC/PseudoArc/Recon86.lean`: its header said `covering_step` "stays open". It now says "(then
  in `Theorem14.lean` and open)", followed by the commissioned line: closed in batch 114 by
  Lehner's route; this file's results stand as results about the fold reformulations.
* `Recon86Chain.lean`, `Recon86Model.lean`, `Recon87Model.lean` (in `HPC/PseudoArc/`) and
  `HPC/Archive/Recon87.lean`, `HPC/Archive/Recon86End.lean`: their headers do not say that the
  covering step is open, so they are not edited. (`Recon86End.lean` says that `theorem3_end` stays
  open, which is still true.)

## 1.6 Notes

`doc/theorems-3-4-scheduling.md` is replaced by the uploaded copy, which ends with §136 (the audit of
batch 115). Three copies were at the root: `theorems-3-4-scheduling(20).md`, `(21).md` and
`(22).md`. `(22)` is the uploaded copy. `(20)` and `(21)` are earlier versions, and each is a prefix
of `(22)` (checked with `diff`: the only difference is lines appended at the end). All three root
copies are deleted. The commission names only `(21)`, but `(20)` is a stray copy in the same way.

## 2. Deliverables

1. `lake build HPC HPCArchive HPCCensus`: succeeds (8335 jobs). The only `declaration uses sorry`
   warnings are `HPC.Fold.theorem3_end` (`HPC/Fold/Theorem4.lean`) and `HPC.Plane.fugate_cor1`
   (`HPC/Plane/Fugate66.lean`).
2. `axioms.txt`: 349 lines; `sorryAx` in exactly two lines (`theorem3_end`, `fugate_cor1`).
   `doc/batches/audits/axioms-batch116.txt` lists `collectAxioms` for every theorem and definition
   (not internal or auxiliary declarations) of the five `.lean` files touched under item 1.5:
   86 declarations (`BandN` 17, `Most51` 27, `Most51Geom` 19, `Theorem14` 12, `Recon86` 11), all with exactly `[Classical.choice, Quot.sound, propext]`; none shows `sorryAx`. The script that produced it is `doc/batches/audits/axioms-batch116.lean`. Prose edits do not change axioms, and the audit confirms it.
3. This report.
