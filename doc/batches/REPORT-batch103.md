Commission read: `COMMISSION-batch103.md` — batch 103, the pruning pass.

# Report, batch 103

Nothing was proved, refuted, weakened or re-proved. The repository was restructured. Five proved
theorems took their canonical (unprimed) names, with the old names kept as aliases (class B). One
false `sorry` was deleted (class A), and 43 commented-out statements were deleted, each replaced by
a one-line pointer to `LEDGER.md`. `lake build HPC`, `lake build HPCArchive` and
`lake build HPCCensus` all succeed. The audit before and after the pruning agrees line for line on
all 226 declarations of the main list (§5 below).

## 1. Layout (§1)

The root now contains `HPC.lean`, `HPCArchive.lean`, `HPCCensus.lean`, `Axioms.lean`,
`axioms.txt`, `OPEN.md`, `LEDGER.md`, `README.md` (new), `doc/`, and the Lake files. The
`lakefile.toml` now has three libraries, each with a single root: `HPC` (the default target),
`HPCCensus` and `HPCArchive`. The `RequestProject` and `Audit76Long` libraries were removed.

* `doc/batches/`: all `COMMISSION*.md`, `REPORT*.md`, `PROBE-batch68.md`, `inventory-batch73.md`,
  and the old `README.md`.
  * `doc/batches/skeletons/` holds the 23 root-level uploaded skeletons (`Atriodic51.lean`,
    `Atriodic51B.lean`, `EndPoints51.lean`, `Fugate66.lean`, `Fugate66B.lean`, `LastLink99.lean`,
    `Layers51.lean`, `Monotone51.lean`, `Most51.lean`, `NonCut51.lean`, `Organ98.lean`,
    `PseudoArc51.lean`, `Recon91.lean`, `Snake51.lean`, `Sorgenfrey.lean`, `Theorem11.lean`,
    `Theorem13.lean`, `Theorem14.lean`, `Theorem4.lean`, `Theorem4Pair.lean`, `Theorem5.lean`,
    `Theorem7.lean`, `Theorem9B.lean`).
  * `doc/batches/audits/` holds the 25 per-batch `Axioms*.lean` and their 35 `axioms-batch*.txt`
    outputs. It also holds this batch's pre-pruning audit: `AxiomsBefore103.lean` and
    `axioms-before-batch103.txt`.
* `doc/census/`: every census, check, probe, witness, seed, search, engine, seam, gap, min and break
  file (`.c`, `.py`, `.log`, `.txt`, `.csv`, `.h`). The other computational scripts went there
  too: `anneal-batch23.py`, `explore-auto*.py`, `ext76.py`, `gen-audit*.py`, `greedy-batch39.py`,
  `greedy77.c`, `invariant-batch39.py`, `mk59.py`, `parametric-batch74.*`, `zig77.py`. So did
  `Audit76Long/` (see below). `doc/census/README.md` lists, for each file, the reports and
  commissions that cite it by name. 81 of the 359 entries are cited by none.
* `doc/exposition/`: `pseudoarc-bing-exposition.pdf`, `Theorem3-formalized-proof.{tex,pdf}`.
* `doc/sources/`: `nadler-11-22-to-11-35.pdf`, `nadler-11-26-to-11-35.txt`.
* `doc/theorems-3-4-scheduling.md`: the newest copy of the notes. Each numbered copy extends the
  previous one, and the unsuffixed `theorems-3-4-scheduling.md` was the **oldest** (234 750 bytes, a
  prefix of the others). The commission says to keep the newest, so the content kept is that of
  `theorems-3-4-scheduling(10).md` (266 794 bytes, up to the batch-103 entry). All eleven copies
  were deleted from the root.

**Deleted:**
* the `hpc-batch*.tar.gz` archives (they were git-ignored);
* `__pycache__`;
* `RequestProject/`. It contained only `Main.lean`, the 24-line template header (imports, `open`s
  and `set_option`s) with no declarations, and the `RequestProject` library that built it.

`Audit76Long/` holds the batch-76 kernel checks of the extension law at six long stored witnesses
(`P5815B946`, `P5742aB343`, `P5742bB5099`, `P13861B2027`, `P13861B343`, `P14000B1586`, with their
data files). They import `HPC.Fold.Target76` and were built with `--tstack=4000000`. Their content
is **not** reproduced by `HPC/Census` or by a report: REPORT-batch76.md cites them but does not
contain them. As the commission instructs, the directory was moved to `doc/census/Audit76Long/`.
It is no longer built.

`ARISTOTLE_SUMMARY.md` stays at the root, unchanged: the project's working instructions forbid
editing that file. This is the one deviation from §1, which lists it under `doc/batches/`.

## 2. The root `HPC.lean` (§2)

The rule applied: keep every file containing a declaration of class B or C, or a declaration of the
§5 main list (the main theorems, the refutation certificates and the open targets), together with
everything such a file imports. This keeps 255 of the 284 modules. The current order of imports is
kept. One import was added, `HPC.Fold.ExitReachFWitness`, placed after `HPC.Fold.ClosureF`: it
contains the ledger certificates `not_exitReachF` and `not_f2PrimeF`, but it was not imported by
`HPC.lean` (it had been built only through the old glob).

**Moved to `HPC/Archive/`** (built by `HPCArchive`; `HPC.Fold.X` became `HPC.Archive.X`, and the
imports between these files were adjusted). No file imported by `HPC.lean` imports any of them,
and none contains a live `sorry`.

| file | content (from its header) |
|---|---|
| `Fold/Audit50`, `Audit51`, `Audit55` | kernel audits of census rows (batches 50–55) |
| `Fold/CeilNarrow`, `ValleyNarrow`, `FloorFar`, `CrossValley`, `CrossServed`, `CoverL5`, `CoverL5Low`, `LinkFold`, `Reflect`, `MixedThin`, `ThinSpan9`, `ThreeWalksThin`, `DecideWitness` | span-nine branch lemmas and witnesses of the Theorem-3 campaign (batches 40–60) |
| `Fold/Descent73`, `Target73`, `Target74`, `Target75` | the batch-73 close of span nine (`s3_span_nine`, `s3_span_nine_mid5`, `s3_span_nine'`) and its packaging (`s3_span_le_nine`, `theorem3_ten_links`). Superseded by `HPC.Fold.theorem3` |
| `Fold/ClosureFWitness` | refutation of `AttainsMinBeforeExceedF` (was built only through the glob) |
| `Fold/Glue76` | the batch-76 gluing question (was built only through the glob) |
| `Fold/Recon86End` | the end-link clause of `theorem3_end` in the settled cases (batch 86) |
| `PseudoArc/Recon87` | reconnaissance on `covering_step`: folds that give a covering step (batch 87) |
| `Plane/Most51Geom` | partial results towards `exists_tame_chain_near` (batch 90) |

Of these, `Recon86End`, `Recon87` and `Most51Geom` are not files of the Theorem-3 campaign. They
are partial results on open items 1, 2 and 4, and `OPEN.md` points to them. They were moved because
the §2 rule decides the case.

**Moved to `HPC/Census/`** (built by `HPCCensus`): `Fold/Census87` (the checker and its soundness
proof) and `Fold/Census87Checks` (the `native_decide` census theorems). The axiom profile is stated
in the docstring of `HPCCensus.lean` and was checked: for example, `HPC.Fold.Census87.checkT3_4_1`
depends on `propext`, `Classical.choice`, `Lean.ofReduceBool`, `Lean.trustCompiler` and
`Quot.sound`.

**Not moved, contrary to the commission's list:** `Fold/Audit72`. It contains no `native_decide`
(its header says so), and `Fold/Audit76`, which stays in the main build, imports it. It stays in
`HPC/Fold`.

## 3. Every `sorry`, classified (§3)

The census of live `sorry`s was taken from the compiled environment: every constant of an `HPC`
module whose value or type mentions `sorryAx`. There were 11, plus 7 theorems depending on them.
Commented-out statements were found by parsing comment blocks.

### 3.1 Live sorried declarations and their dependents

| declaration | class | file before | file after | action |
|---|---|---|---|---|
| `HPC.Plane.exists_irreducibleBetween_of_atriodic` | B | `Plane/Fugate66` (sorry) | `Plane/Sorgenfrey` (proved) | sorried version deleted; `sorgenfrey_irreducible_of_atriodic_hu` renamed to the canonical name, old name kept as alias; pointer left in `Fugate66` |
| `HPC.Plane.isTerminalSub_iff_irreducible` | B (depended on the previous one) | `Plane/Fugate66` | `Plane/Sorgenfrey` | sorried version deleted; `isTerminalSub_iff_irreducible'` renamed, alias kept |
| `HPC.Plane.fugate_theorem1_sufficiency` | B | `Plane/Fugate66` | `Plane/Fugate66B` | sorried version deleted; `fugate_theorem1_sufficiency'` renamed, alias kept |
| `HPC.Plane.fugate_theorem1` | B (dependent) | `Plane/Fugate66` | `Plane/Fugate66B` | sorried version deleted; `fugate_theorem1'` renamed, alias kept |
| `HPC.Plane.fugate_cor2` | B (dependent) | `Plane/Fugate66` | `Plane/Fugate66B` | sorried version deleted; `fugate_cor2'` renamed, alias kept |
| `HPC.Plane.fugate_cor1` | **C** | `Plane/Fugate66` | same | kept, `-- OPEN`; not superseded, since `fugate_cor1'` assumes the union *hereditarily* unicoherent |
| `HPC.Plane.exists_degenerate_interior_elt` | **A** | `Plane/Theorem11` | — | deleted (refuted by `exists_degenerate_interior_elt_refuted`); pointer left; `LEDGER.md` |
| `HPC.Fold.theorem3_end` | C | `Fold/Theorem4` | same | kept, `-- OPEN` |
| `HPC.Description.covering_step` | C | `PseudoArc/Theorem14` | same | kept, `-- OPEN` |
| `HPC.Description.theorem14` | C | `PseudoArc/Theorem14` | same | kept, `-- OPEN` |
| `HPC.Plane.exists_tame_chain_near` | C | `Plane/Most51` | same | kept, `-- OPEN` |
| `HPC.Plane.isContPt_congr` | C | `Plane/Layers51` | same | kept, `-- OPEN` |
| `HPC.Plane.subcontinuum_of_isContPt` | C | `Plane/Layers51` | same | kept, `-- OPEN` |
| `HPC.Plane.theorem11_1951_of_T10'` | C | `Plane/Layers51` | same | kept, `-- OPEN` |
| `HPC.Description.exists_description_covering`, `HPC.Description.theorem15`, `HPC.Plane.dense_pseudoArcs`, `HPC.Plane.theorem2_HIC` | consequences of C (their own proofs contain no `sorry`) | unchanged | unchanged | kept; listed in `OPEN.md` and in the audit group *Consequences of open targets* |

For each class-B pair, the type of the deleted declaration was checked to be definitionally equal
to the type of the proved one, by elaboration with a common universe:
`example : type_of% @A.{u} = type_of% @B.{u} := rfl` succeeds for all five pairs, and fails for
`fugate_cor1` against `fugate_cor1'`. No statement had to move between files: each proved version
already lived in the file that proves it, and the old file (`Fugate66.lean`) keeps one-line
pointers. Module docstrings that said "keeps its `sorry`" were updated in `Fugate66B.lean`,
`Sorgenfrey.lean`, `Theorem11.lean` and `Layers51.lean`.

**Class D: empty.** Apart from `theorem3_end`, no file under `HPC/Fold` contains a live sorried
declaration. Every `sorry` of the campaign files (`General`, `ZigFree`, `Minimal2`, `ClosureTight`,
`Interior`, `OffCenter`, `Span`, `Closure`, `Choice`, `Mixed`, `ClosureF`, `Zigzag`, `CutRoute`,
`Step`, `Dichotomy`, …) sat inside a comment block. Those blocks are commented-out statements and
were treated as class A (§3.2). The files themselves were archived or kept by the import rule of §2.

**Left undecided: `HPC.Plane.theorem11_1951_of_T10`** (`Plane/Theorem11`). The commission says to
delete it as "proved but vacuous". It is kept, together with `theorem11_1951_iff_of_T10`, for two
reasons:

1. `theorem11_1951_iff_of_T10` (proved, not mentioned in the commission) uses it, so deleting it
   would delete a second theorem.
2. Its hypothesis `hdeg` quantifies over `Type u`. The repository refutes it only in universe 0
   (`theorem11_hdeg_refuted`), so the theorem is vacuous at `u = 0` but not provably so in general.

Also, §4 protects `_of` forms. The case is recorded in `LEDGER.md` §3, and both theorems stay in the
audit.

### 3.2 Commented-out statements (class A by §3): 43 blocks deleted

Each block was replaced by one line,
`-- Commented-out statement `…` removed in batch 103; see `LEDGER.md`.`. Two prefatory comment
blocks, the "Relocated in batch 73" notes in `General` and `Mixed`, were deleted with the code they
introduced. `LEDGER.md` §1 gives the refutation of each one that is refuted, and §2 the status of
each one that is not.

| file | statements | ledger entry |
|---|---|---|
| `Fold/Choice` | `s3ZigFreeInterior`, `s3ZigFree`, `s3` | §2 (`s3` proved; others moot) |
| `Fold/Closure` | `exitReach`, `highExitValleyOpen`, `lowExitPeak`, `highExitValley`, `f2Prime`, `theorem3` | §1 (`not_exitReach`, …) |
| `Fold/ClosureF` (2 blocks) | `exitReachF`, `highExitValleyF`, `lowExitPeakF`; `f2PrimeF`, `theorem3` | §1 |
| `Fold/ClosureTight` | `exitReachTight`, `highExitValleyOpenTight`, `lowExitPeakTight`, `highExitValleyTight`, `f2PrimeTight`, `theorem3` | §1 |
| `Fold/CutRoute` (3) | `exists_cutData`; `s3ZigFreeInterior_of_cutWalk`; `cutWalk'` | §1; §2; §2 |
| `Fold/Dichotomy` | `offDichotomy`, `f2PrimeOff`, `theorem3` | §1 (`f2PrimeOff`: conditional refutation) |
| `Fold/General` (2) | relocation note; `s3_span_nine` | §2 (proved in `Archive/Target73`) |
| `Fold/Interior` (2) | `arm_timing`; `s3ZigFreeInterior`, `s3ZigFree`, `s3`, `theorem3` | §1; §2 |
| `Fold/Minimal2` | `ExtendStepMin`, `extendStepMin` | §1 |
| `Fold/Mixed` (6) | `unserved_high8`; `unserved_ceiling`, `unserved_valley`; `cross_ceil_profile`; `unserved_profile`, `unserved_leg3deep`; relocation note; `s3_span_nine_mid5`, `s3_span_nine'` | §1 ×4; §2 |
| `Fold/OffCenter` | `f2PrimeOff`, `theorem3` | §1 / §2 |
| `Fold/Span` | `s3`, `theorem3` (with the `⌊S/2⌋` census conjecture of batch 76, recorded in REPORT-batch76.md) | §2 |
| `Fold/Step` | `extendStep` | §2 |
| `Fold/Theorem7` | `theorem8` (skeleton form) | §1 (`theorem8_skeleton_false`) |
| `Fold/Witnesses` | `hStarArm_eq_of_peak_on_T'` | §2 |
| `Fold/ZigFree` | `s3ZigFree`, `s3`, `theorem3` | §2 |
| `Fold/Zigzag` | `s3Zig` | §1 (`not_s3Zig`) |
| `Plane/Atriodic51` | `theorem8_1951`, `isArc_of_separatesPairs` | §1 (`Counter92.*_false`) |
| `Plane/Fugate66` (2) | `isFugateTriod_iff_isTriod`; `isTriod_union_of_three` | §1 (informal counterexamples only, REPORT-batch100.md) |
| `Plane/Fugate66B` | `miller_1_5` | §1 (`miller_1_5_false`) |
| `Plane/Layers51` (2) | `bingElt_degenerate_of_isContPt`; `exists_degenerate_interior_elt'` | §1 |
| `Plane/Organ98` | `isSnakeLike_union_of_terminal` | §1 |
| `Plane/PseudoArc51` (2) | `theorem12_of`; `isPseudoArc_of_description` (skeleton forms) | §1 |
| `Plane/Recon91` | `theorem10_1951_of_step` | §2 |
| `Plane/Snake51` | `exists_rect_chain_following` (skeleton form) | §1 (`rectStepSkeleton_false`) |
| `Plane/SorgenfreyLemmas` | `isConnected_diff_of_superset` | §1 |
| `Plane/Theorem11` | `not_separation_of_accumulates` | §1 |
| `PseudoArc/Theorem5` (2) | `theorem6Pos_shift`; `patternFollowing` | §1 |

**Did not fit cleanly:** about a dozen of these commented-out statements are not known to be false:
`s3ZigFree`, `s3ZigFreeInterior`, `cutWalk'`, `s3ZigFreeInterior_of_cutWalk`, `extendStep`,
`hStarArm_eq_of_peak_on_T'`, `theorem10_1951_of_step`, and the relocated `s3_span_nine*`. §3 calls
every commented-out statement class A, so they were deleted. They are recorded separately in
`LEDGER.md` §2 with their actual status: proved elsewhere, superseded, or open and no longer needed.
None is a live declaration, so `OPEN.md` does not list them.

After the deletions, the remaining occurrences of the word `sorry` outside the eight open targets
are prose in comments and docstrings, such as "no `sorry` remains" and "Every `sorry` is a work
item".

## 4. Names (§4)

Only the five class-B renames were made (§3.1). No `_of`, `_aux` or other primed form was renamed
or deleted.

## 5. The single audit (§5)

`Axioms.lean` prints the axioms of 226 declarations, grouped as the commission asks. Its output is
`axioms.txt`.

**Substitutions**, where a name in the commission's list does not exist as such:

* **1948:**
  * `theorem1` → `HPC.Chain.isCrookedIn'_of_isConsolidationOf` (docstring "Bing 1948, Theorem 1").
  * `theorem2` → `HPC.Chain.isCrookedIn'_of_refines`.
  * `theorem3` → `HPC.Fold.theorem3`. Its end-clause variant `HPC.Fold.theorem3_end` is listed under
    *Open targets*.
  * `theorem4` → `HPC.Fold.theorem4`.
  * `theorem5`, `theorem6` → `HPC.Description.theorem5`, `theorem6`.
  * `theorem7`, `theorem7_minimal`, `theorem8` (corrected), `theorem9`, `not_theorem8_literal` →
    `HPC.Fold.*`.
  * `theorem10` → `HPC.Description.theorem10`.
  * `theorem11` → `HPC.MatchingCovers.exists_homeomorph`, which is also the commission's last 1948
    item.
  * `theorem12` → `HPC.theorem12`, with `HPC.Description.exists_homeomorph`.
  * `theorem13` → `HPC.Description.theorem13`.
  * `exists_description_from`, `theorem15_of_theorem14` → `HPC.Description.*`.
  * `pseudoArc_exists` → `HPC.Plane.pseudoArc_exists`.
* **Duke:**
  * `theorem4` (Duke) → `HPC.Plane.theorem4`.
  * `theorem12` A ⇒ B → `HPC.Plane.condB_of_condA`.
  * `theorem13` necessity → `HPC.Plane.condB_of_endPoint`.
  * `theorem11_1951_of_T10` is kept (§3.1), and `theorem11_1951_iff_of_T10` was added.
  * `theorem11_1951_of_T10'` is listed under *Open targets*.
* **Fugate:** `fugate_theorem1'`, `fugate_cor2'` and `isTerminalSub_iff_irreducible'` are audited
  under their canonical names `fugate_theorem1`, `fugate_cor2` and `isTerminalSub_iff_irreducible`.
  `fugate_theorem1_sufficiency` was added.
* **Nadler:** `exists_irreducibleBetween_of_atriodic` was added (formerly
  `sorgenfrey_irreducible_of_atriodic_hu`).
* **Refutations:** the ledger certificates of the Theorem-3 campaign (30 `not_*` theorems), plus
  `HPC.isCrookedIn_ne_isCrookedIn'` (T3). The rest of the group is every theorem whose name matches
  `*_false`, `*_refuted`, `not_*_literal`, `*counterexample*` or `Counter92.*` (equation lemmas and
  instances excluded).
* **Helper lemmas.** Nine names match `*_false` but are helper lemmas about the Boolean `false` or
  steps inside a proof, not refutations: `Org.frequently_false`, `Org.isLeftEnd_of_last_false`,
  `Org.lam_const_false`, `Org.lam_flip1_false`, `Org.lastF_succ_false`, `Org.lastT_succ_false`,
  `Org.zz_le_of_conf_false`, `PA51.limit_false`, `preconnected_closed_split_false`. They are listed
  in a separate group.
* **Open and consequences:** the eight class-C declarations, then the four theorems that inherit
  `sorryAx` from them.

**Before/after comparison.** The pre-pruning audit was run on the batch-102 tree with the same list
and the pre-rename names (`doc/batches/audits/AxiomsBefore103.lean`, which imports `HPC` and
`HPC.Fold.ExitReachFWitness`). Its output is `doc/batches/audits/axioms-before-batch103.txt`.
After mapping the five renamed names, the two outputs agree on all 226 declarations. 226 of 226
are identical, none differs, and none is present in only one of them.

* `sorryAx` appears in exactly 12 lines: the 8 open targets and the 4 consequences.
* Every other line shows `[propext, Classical.choice, Quot.sound]` or a subset of it.
* No axiom outside `{propext, Classical.choice, Quot.sound, sorryAx}` occurs.

`lake build HPC` reports `declaration uses 'sorry'` exactly eight times, once for each open target.

## 6. README (§6)

`README.md` was rewritten, and the old one is `doc/batches/README.md`. The new one covers:

* what the repository is, and how to build it;
* the layout;
* the axiom policy (standard axioms in `HPC.lean`, `native_decide` only under `HPC/Census`);
* pointers to `OPEN.md`, `LEDGER.md` and `doc/exposition`;
* the naming conventions (`'`, `_of`, `_false`/`_refuted`/`not_`).

It makes no claim beyond `axioms.txt`.

## 7. Left undecided, or decided against the letter of the commission

1. `theorem11_1951_of_T10` was kept (§3.1).
2. `Fold/Audit72` stays in `HPC/Fold`: it uses no `native_decide`, and `Audit76` imports it (§2).
3. `ARISTOTLE_SUMMARY.md` stays at the root (§1).
4. The "newest" notes file is `theorems-3-4-scheduling(10).md`, not the unsuffixed one (§1).
5. Commented-out statements that are not refuted were deleted as class A, but are listed in
   `LEDGER.md` §2 rather than §1 (§3.2).
6. `isFugateTriod_iff_isTriod` and `isTriod_union_of_three` have only informal refutations
   (REPORT-batch100.md). They are in the ledger without a Lean name.
7. `f2PrimeOff` has only a conditional Lean refutation (`not_f2PrimeOff_of_faithful`); the ledger
   says so.
8. `Recon86End`, `Recon87` and `Most51Geom` went to the Archive by the §2 rule, although they are
   not Theorem-3 campaign files (§2).
9. The compiled PDFs (`doc/exposition/*.pdf`, `doc/sources/*.pdf`) are moved but are excluded from
   git by the existing `.gitignore` rule `*.pdf`. The same holds for the deleted tarballs, which were
   never tracked.
