# Commission: batch 116 — housekeeping after Theorem 14

**Go!** Runs on top of the batch-115 delivery. Files uploaded with this commission:
`COMMISSION-batch116.md` (this text, also pasted into the prompt) and
`theorems-3-4-scheduling.md` (the notes; it replaces `doc/theorems-3-4-scheduling.md`). No
skeleton; no new mathematics. A housekeeping batch like 103, 105 and 111: existing files are to
be edited exactly as listed. The report names the commission read in its first line and lists
every file touched.

## 0. On batch 115

Audited: every item proved, no refutation; `sorryAx` in exactly two lines (`theorem3_end`,
`fugate_cor1`). The extensions of `T5.assemble`, `LehnerCore.indices/blocks/core` and the
derivation of `lehner_lemma3_two` from `lehner_lemma3_twoA` (statements of existing results
unchanged) are accepted; `theorem5_gen` with an arbitrary coarse chain in place of the thinned
description is accepted and welcome. Bing 1948 is now checked in full except the end-link clause
of Theorem 3.

## 1. Documentation of the closed items

1. **`OPEN.md`.** Keep the two live items, renumbered `1` (`theorem3_end`) and `2`
   (`fugate_cor1`); replace the three "closed in batch …" stubs by one short section *Closed
   items* at the end listing, for each, the former statement name, the batch that closed it and
   the theorem that now proves it (`covering_step` by `lehner_lemma3_two`, batch 114;
   `theorem14` by `Thm14.lean`, batch 115; `geomLemma'_of_two_le_rank` by `CubeCycle.lean`,
   batch 113). Update the header paragraph (no consequences group any more).
2. **`LEDGER.md`.** New section *§5. Bing 1948, Theorems 9 and 14, and Lehner 1961* with:
   * Theorem 14's "That there exist such sequences follows as a consequence of Theorem 9": not a
     proof; the sequences are supplied by Lehner's Lemma 3 (n = 2), proved in batch 114 by
     crookedness of one level in the previous one (`lehner_lemma3_two`); the batch-86/87
     reformulations through folds (`coveringStep_of_folds₃`, the end-time lemma) are not the
     route and their refutations stand as refutations of those reformulations;
   * the two further assertions of Theorem 14's sketch (the point `A` with `X_{1,j}(P_1, A)` inside
     `Y_{1,1}(P_1, R_1)` and the closure of `x(1,j)_A` inside `y(1,1)_{P_1}`; the finer covering
     part inside the coarser) are not established for an arbitrary covering description and are
     established for the description Lehner's construction gives (`CoversUpToA`, batch 115); say
     "not established", not "false" — no refutation was proved;
   * the steps of the three-piece assembly the sketch leaves out (REPORT-batch115.md, ledger
     list 1–9), in brief;
   * Lehner's Theorem 1 is Bing's Theorem 9 re-proved "at the request of Professor Bing" because
     the original "has presented some readers with difficulty" (Lehner, p. 370); the repository's
     `theorem9` (batch 82) is proved as Bing states it, without Lehner's end clause.
   Also in §1 (refuted statements): nothing new. Keep the §2–§4 numbering.
3. **`README.md`.** The paper list: Bing 1948 "Theorems 1–15 (Theorem 3 without its end-link
   clause)"; add Lehner 1961 (*Extending homeomorphisms on the pseudo-arc*, Trans. AMS 98):
   Lemma 3 for `n = 2`; the batch count "111 batches" → "116"; the layout table's `doc/sources/`
   row: the Lehner scan is not in the repository (not uploaded; PDFs are git-ignored anyway), so
   no change there. One sentence after the Theorem 11 sentence: "Bing's Theorem 14 is proved by
   his own alternating construction, with the covering descriptions supplied by Lehner's Lemma 3
   (`HPC.Description.theorem14`, `HPC/PseudoArc/Thm14.lean`)."
4. **`Axioms.lean`.** The empty group *Consequences of open targets*: keep the header with its
   "(none …)" line, as it is. Check that every theorem of batches 113–115 named in the reports is
   listed; add any that is not. Regenerate `axioms.txt`; report the line count and the two
   `sorryAx` names.
5. **Module docs still describing the old open status**: `HPC/Plane/BandN.lean`,
   `HPC/Plane/Most51.lean`, `HPC/Archive/Most51Geom.lean` (the geometric lemma: now proved in
   every dimension, `geomLemma'_of_two_le_rank`, `CubeCycle.lean`); `HPC/PseudoArc/Theorem14.lean`
   (its header still says Theorem 14 is open — update to point to `Thm14.lean`);
   `HPC/PseudoArc/Recon86.lean`, `Recon87*.lean` headers if they say the covering step is open
   (one line each: "closed in batch 114 by Lehner's route; this file's results stand as results
   about the fold reformulations"). Prose only; no statement changes.
6. **Notes.** Replace `doc/theorems-3-4-scheduling.md` by the uploaded copy; delete the stray root
   copy `theorems-3-4-scheduling(21).md`.

## 2. Deliverables

1. `lake build HPC HPCArchive HPCCensus` clean except the two `sorry` warnings.
2. `axioms.txt` regenerated; `axioms-batch116.txt` for every declaration whose file was touched
   (prose edits do not change axioms, but the audit should show it).
3. Report: files touched; the ledger section as written.

## 3. Next

To be decided with David: Fugate's Corollary 1 in his form; a reconnaissance on
`theorem3_end`; Duke Theorems 6–7 on the polygonal interface.
