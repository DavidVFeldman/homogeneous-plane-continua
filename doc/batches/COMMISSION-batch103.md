# Commission: batch 103 — the pruning pass

**Go!** Runs on top of the batch-102 delivery. One file accompanies this commission:
`COMMISSION-batch103.md` (this text, also pasted into the prompt). No skeleton: this batch
changes the shape of the repository, not its mathematics. Every rule below is to be applied
mechanically; where a rule does not decide a case, the report lists the case and leaves it as is.

The report names the commission read in its first line. **No theorem is to be proved, weakened,
or re-proved in this batch; no statement's meaning changes.** The test at the end is that every
declaration in the main audit list (§5) has the same axiom profile before and after.

## 0. Why

The delivery folder has grown over 102 batches into 284 Lean files (93 602 lines), ~500
census programs, logs and witness files, 70 archived tarballs, 100 commissions and reports, and
ten copies of the project notes. It will go to a public repository. The repository should let a
reader find (i) the verified theorems with their axiom audit, (ii) the refutations that are the
certificates of the ledger, (iii) the open items, and (iv) the provenance of every finite
computation — and nothing else in the build.

## 1. Layout

Create this layout (moves are `git mv`-style: content unchanged unless a rule below says
otherwise).

```
HPC.lean                   root: imports the verified main line + open targets (see §2)
HPC/Chains, Covers, Fold, PseudoArc, Plane   as now, minus what moves out
HPC/Census/                the native_decide census theorems (Fold/Census87, Census87Checks,
                           Fold/Audit72) with a module docstring stating the axiom profile
                           (Lean.ofReduceBool, Lean.trustCompiler) and that nothing depends on them
HPCCensus.lean             root for HPC/Census (built separately; not imported by HPC.lean)
HPC/Archive/               exploratory files of the Theorem-3 campaign that no main-line theorem
                           depends on (§3, class D), kept compiling
HPCArchive.lean            root for HPC/Archive (built separately; not imported by HPC.lean)
Axioms.lean                the single audit (§5), producing axioms.txt
OPEN.md                    the open items (§3, class C), one entry each: statement, file, what
                           depends on it, what is known (one paragraph from the reports)
LEDGER.md                  the refutation certificates (§3, class A and the *_false/*_refuted
                           theorems): Bing's / Fugate's / Nadler's / the commissions' statement,
                           the Lean name of the refutation, one line of explanation
doc/batches/               all COMMISSION-batch*.md and REPORT-batch*.md, PROBE-*, inventory-*,
                           ARISTOTLE_SUMMARY.md, README.md (old)
doc/census/                every census/check/probe/witness/seed/search/engine/seam/gap/min/break
                           .c/.py/.log/.txt/.csv file, with a README listing which report cites
                           which file (grep the reports for the file names)
doc/exposition/            pseudoarc-bing-exposition.pdf, Theorem3-formalized-proof.{tex,pdf}
doc/sources/               nadler-11-22-to-11-35.pdf, nadler-11-26-to-11-35.txt
README.md                  new (§6)
```

Delete: the `hpc-batch*.tar.gz` archives, `__pycache__`, `Audit76Long` (after checking that
its content is reproduced by `HPC/Census` or a report — if not, move it to `doc/census/`),
`RequestProject` (say what it is first), the root-level duplicate `.lean` skeletons
(`Atriodic51.lean`, `Theorem13.lean`, … at the top level: they are the uploaded skeletons, whose
content is in `HPC/`; move to `doc/batches/skeletons/`), the copies
`theorems-3-4-scheduling(*).md` (keep the newest `theorems-3-4-scheduling.md` in `doc/`).

## 2. The root `HPC.lean`

Keep the imports of every file that contains at least one declaration of class B or C of §3, or
that is imported by such a file. Everything else goes to `HPC/Archive` (class D) or `HPC/Census`.
Keep the current order of the remaining imports.

## 3. Every `sorry`, classified

List every declaration whose body is `sorry` (not inside a comment block). Each is in exactly one
class:

* **A — known false.** The statement is refuted by a theorem in the repository (e.g.
  `exists_degenerate_interior_elt` by `exists_degenerate_interior_elt_refuted`;
  `theorem11_1951_of_T10'` is not false but its only route was; see C). Action: delete the
  sorried declaration; keep the refutation; add the pair to `LEDGER.md`. Commented-out
  statements (`Atriodic51.lean`, `Organ98.lean`, `Snake51.lean`, `Theorem5.lean`,
  `SorgenfreyLemmas.lean`, `Fugate66.lean`'s `isFugateTriod_iff_isTriod`, `miller_1_5`, …) are
  class A too: delete the comment block, keep its explanation as one line in `LEDGER.md`.
* **B — superseded.** A sorry-free theorem with the same statement exists under another name
  (`theorem10_1951'`-style). Current list: `Fugate66.lean`: `exists_irreducibleBetween_of_atriodic`
  (← `sorgenfrey_irreducible_of_atriodic_hu`), `isTerminalSub_iff_irreducible` (←
  `isTerminalSub_iff_irreducible'`), `fugate_theorem1_sufficiency`, `fugate_theorem1`,
  `fugate_cor1` (← `fugate_cor1'`/`fugate_cor1_iff`, note the stronger hypothesis: this one is
  **not** superseded; it is class C unless the statements agree), `fugate_cor2`; `Fugate66B.lean`:
  `fugate_cor1'`? (check); `Theorem11.lean`: `theorem11_1951_of_T10` (proved but vacuous: class
  A-adjacent — delete and record). Action: delete the sorried declaration, rename the proved one to
  the canonical (unprimed) name, keep the primed name as an `alias`, and fix the import order by
  moving the statement if needed (a statement may move to the file that proves it; the old file
  keeps a one-line pointer). Build.
* **C — open target.** Not refuted, not superseded. Expected: `theorem3_end` (Fold),
  `covering_step` and `theorem14` (PseudoArc/Theorem14), `exists_tame_chain_near` (Most51),
  `isContPt_congr`, `subcontinuum_of_isContPt`, `theorem11_1951_of_T10'` (Layers51),
  `fugate_cor1` (Fugate's hypothesis). Action: keep in place; add `-- OPEN (see OPEN.md)` above
  the declaration; write the `OPEN.md` entry.
* **D — exploratory.** A sorried statement of the Theorem-3 campaign (`HPC/Fold/*`: `General`,
  `ZigFree`, `Minimal2`, `ClosureTight`, `Interior`, `Theorem4`, `OffCenter`, `Theorem7`, `Span`,
  `Closure`, `Choice`, `Mixed`, `ClosureF`, `Zigzag`, `CutRoute`, `Step`, `Dichotomy`, …) on which
  no class-B/C declaration and no clean main-line theorem depends. Decide dependence by the
  import graph and by `#print axioms` of the main list (§5): a main theorem whose profile is
  standard depends on no sorried declaration. Action: if the whole file is exploratory, move it to
  `HPC/Archive/` (adjust imports); if the file mixes exploratory sorried statements with used
  declarations, split: used declarations stay, the sorried statements and their private helpers
  go to `HPC/Archive/<File>Open.lean`. A sorried statement that a report records as **false** with
  a witness (e.g. `Fold/Dichotomy.lean:270`, witness `DichotomyWitness.lean`) is class A, not D.

The report lists every sorried declaration with its class, file before/after, and the action
taken. If a case does not fit, leave it and list it.

## 4. Primed and `_of`/`_aux` names

Do **not** rename anything beyond class B. Do not delete `_of` forms (conditional theorems whose
hypothesis is a named open lemma): they are part of the record.

## 5. The single audit (`Axioms.lean` → `axioms.txt`)

One file that `#print axioms` for the main list, grouped by paper, in this order (names as in the
repository after §3):

* **1948**: `theorem1` … `theorem13` (with `theorem3` and its end-clause variant), `theorem4_pair`,
  `theorem5`, `theorem7`, `theorem7_minimal`, `theorem8` (corrected) and `not_theorem8_literal`,
  `theorem15_of_theorem14`, `exists_description_from`, `pseudoArc_exists`,
  `MatchingCovers.exists_homeomorph`;
* **Duke 1951**: `theorem1_snake`, `theorem4` (Duke), `theorem8_1951'`, `theorem9_1951`,
  `theorem10_1951`, `isSnakeLike_of_subcontinuum`, `isAtriodic_of_isSnakeLike`,
  `isHereditarilyUnicoherent_of_isSnakeLike`, `theorem11_1951_of_T10` (if kept) /
  `theorem11_1951_of_T10'`, `theorem12` A ⇒ B (name it), `theorem13` necessity and
  `endPoint_of_condA`, `theorem14_1951`, `theorem15_1951`, `isPseudoArc_iff_endPoints`,
  `exists_two_endElts`, `organ_isSnakeLike`;
* **Pacific 1951**: `theorem1_HIC`, `pseudoArc_unique`, `homogeneous_of_isPseudoArc`,
  `isGδ_pseudoArcs`, `dense_pseudoArcs_of`, `theorem2_HIC_of`, `theorem3_HIC`,
  `theorem3_HIC_bing`, `theorem4_HIC`;
* **Fugate 1966**: `fugate_lemma1`, `fugate_lemma2'`, `fugate_lemma4`, `fugate_theorem1'`,
  `fugate_cor1_iff`, `fugate_cor2'`, `isTerminalSub_iff_irreducible'`;
* **Nadler**: `exists_two_nonCutPoints`, `not_subset_of_nonCutPoints`, `sorgenfrey`,
  `irreducible_iff_not_isTriod`, `isHereditarilyUnicoherent_union`,
  `isUnicoherent_univ_of_contraction`;
* **Refutations** (class A certificates): every `*_false`, `*_refuted`, `not_*_literal`,
  `Counter92.*`, `two_organs_counterexample`, `arcs_counterexample`, `miller_1_5_false`, …;
* **Open**: the class-C declarations, so that `sorryAx` shows exactly there.

Where a name in this list does not exist, find the declaration meant (the reports say) and use
its name; list the substitutions. `axioms.txt` before and after the pruning must agree line for
line on the declarations present in both.

## 6. README.md

One page: what the repository is (machine-checked verification of Bing 1948, Bing 1951 (Duke),
Bing 1951 (Pacific), Fugate 1966 and the supporting theorems of Nadler, in Lean 4 / Mathlib,
toolchain as in `lean-toolchain`); how to build (`lake build HPC`; `lake build HPCCensus`,
`HPCArchive` optional); where things are (the layout of §1); the axiom policy (standard axioms
for everything in `HPC.lean`; `native_decide` only under `HPC/Census`); pointers to `OPEN.md`,
`LEDGER.md`, `doc/exposition`; the convention for names (`'`, `_of`, `_false`). No claims beyond
`axioms.txt`.

## 7. Deliverables

1. The restructured tree; `axioms.txt`; `OPEN.md`; `LEDGER.md`; `README.md`; `doc/`.
2. Report: first line names the commission read; the classification table of §3; the list of
   files moved to `Archive`/`Census`; the substitutions of §5; the before/after comparison of the
   audit; anything left undecided.
3. Nothing is proved or refuted in this batch.
