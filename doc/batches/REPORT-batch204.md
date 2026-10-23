Commission read: `doc/batches/COMMISSION-batch204.md` (batch 204, house cleaning for a public repository).

# Report, batch 204

## §0. Omissions and deviations

**Nothing could be built in this run.** The run had no Lean toolchain (no `lake`, no `elan`) in the
workspace that holds this repository, so every step of the commission that needs a build was left
out. David asked for the batch to be done with those steps skipped and listed here. They are:

1. `lake exe cache get` (§1): not run; its outcome is unknown.
2. `lake build HPC`, `lake build HPCExtra`, `lake build HPCArchive`, `lake build HPCCensus` (§1, §6):
   not run. No build times; no size of `.lake/build` (there is no `.lake`). The machine had 8 cores
   (`nproc`) and 64 GB of memory, for whoever reruns this on the same kind of machine.
   **Consequence:** the commission's rule "if a file fails to build, stop the batch" could not be
   applied; the edits of §1 and §5 are unchecked by Lean. The Lean edits are: the root files
   `HPC.lean`, `HPCExtra.lean` (new), `Axioms.lean`; docstrings only in the five files of §5; and
   `scripts/DepCensus.lean`, `scripts/HPCModules.lean` (new), comments of `scripts/Replay.lean`.
3. Timing of `lake env lean Axioms.lean` and **the regeneration of `axioms.txt`** (§1, §6): not done.
   `axioms.txt` is unchanged (the received file, 4030 lines; `cmp` with `/tmp/axioms-203.txt`:
   identical). It therefore lacks the output of the five `#print axioms` lines of the new group.
4. `scripts/split.py` **check 2** (§1): `scripts/HPCModules.lean` is written but was not run, so the
   comparison with `(← getEnv).header.moduleNames` is not made. Check 1 passed (§1 below).
5. **The census rerun** (§6: `DepCensus.lean`, `closure.py`, `Replay.lean`, `headlines_by_paper.py`,
   `report_tables.py`) and `scripts/rootfiles.sh` (which reads the census): not run. `doc/depcensus/`
   is the batch-203 census, unchanged except for its `README.md`; `/tmp/depcensus-203` was saved but
   not compared with anything. No `edges-external.tsv` was generated, so none had to be deleted.
   The root listing that `rootfiles.sh` would give is replaced by the hand count in §6.
6. **`lake-manifest.json`**: Lake did not run, so it did not rewrite the file. It is unchanged and
   still has `"name": "RequestProject"` (line 94), the package's old name; `lakefile.toml` now says
   `hpc`. The first `lake build` will probably rewrite that line; per §1, keep the rewrite.
7. `README.md`, section 3 (Building) says that build times have not been measured; section 4 uses
   the batch-203 Table 2 (the census was not rerun), with a note.

Other deviations:

* **Received files.** The three copies of §"Before any change" were made: `/tmp/start-tree.txt`
  (2272 files), `/tmp/depcensus-203`, `/tmp/axioms-203.txt`. They were not lost.
* `doc/census/__pycache__/seam-batch121.cpython-311.pyc` (received) was deleted by mistake during
  the work and restored with its received content (same sha256). It is not published (§4).
* Transcriptions: the commission names commissions 79–90, 92, 101, 106, 107, 132, 134, 178–194 and
  `REPORT-batch184.md` §2. In 86, 87, 106, 107, 178–182, 184–190, 192–194 and `REPORT-batch184.md` §2
  no passage reaches 150 words (details in §2). Long quotations were also found and moved in
  commissions 96, 99, 100, 104, 108, 114, 117, 121, 200 and in one statement skeleton.

**Git.** The workspace keeps the repository under a local git repository whose only commit
("User workspace baseline") is the tree as received. Before this report, the manifest and the
listing were written, `git status --porcelain --ignored` showed: 23 files deleted, 45 modified, one
renamed (`COMMISSION-batch78(1).md` → `COMMISSION-batch78.md`), 8 untracked paths (`HPCExtra.lean`,
`doc/HISTORY.md`, `doc/batches/COMMISSION-batch204.md`, `doc/defects/`, `doc/sources/README.md`,
`doc/sources/transcriptions/`, `scripts/HPCModules.lean`, `scripts/split.py`), nothing ignored;
nothing committed since the baseline. The `.git` directory is excluded from the listing and the
tarball, as §7 says.

## §1. The library split

* `HPC.lean` imports exactly `HPC.BJ59.BJ59E`, with a module docstring (the original imported every
  module of the main line).
* `scripts/split.py` reads the `import` lines of the files under `HPC/`, computes the import closure
  of `HPC.BJ59.BJ59E` and writes `HPCExtra.lean` (125 imports, `LC_ALL=C` order, and a module
  docstring). **Check 1 passed:** 861 modules under `HPC/` = 709 (closure of `HPC.lean`) + 125
  (`HPCExtra.lean`) + 25 (`HPC/Archive`) + 2 (`HPC/Census`), each in exactly one part. The 125 by
  directory: `HPC/Fold` 94, `HPC/Plane` 14, `HPC/BJ59` 8, `HPC/Hagopian` 4, `HPC/HO16` 2,
  `HPC/PseudoArc` 2, `HPC/Chains` 1, as the commission counts. **Check 2: not run** (§0.4); the Lean
  side is `scripts/HPCModules.lean`, run as
  `lake env lean scripts/HPCModules.lean > /tmp/hpc-env-modules.txt` and then
  `python3 scripts/split.py --no-write --env /tmp/hpc-env-modules.txt`.
* `lakefile.toml`: package name `hpc`; new `lean_lib` `HPCExtra` with `name` and `roots` on the two
  lines after `[[lean_lib]]` and a comment (modules outside the classification's import closure);
  the comment of `HPC` now says it is the classification, the import closure of `HPC.BJ59.BJ59E`;
  `defaultTargets = ["HPC"]` and the Mathlib requirement unchanged.
* `lake exe cache get`, build times, timing of `Axioms.lean`: not done (§0).
* `lake-manifest.json`: no diff (§0.6).
* **Windows check** over the 2315 paths of the tree (files and directories, `.git` excluded): no
  component is a reserved device name (with or without extension), none contains `<>:"|?*`, none
  ends in a dot or a space, and no two paths differ only in case. No `.lean` file imports
  `HPC.Chains.Aux`. Nothing renamed.
* **`Axioms.lean`** imports `HPC` and `HPCExtra`. About 177 of the names its `#print axioms` lines
  name are declared in modules that now belong to `HPCExtra`, so the second import is needed; that
  every name resolves is unchecked (no build). The new group
  `-- ## Bing 1951 (Duke), Theorem 6 by the compact Janiszewski theorem` stands just before
  `-- ## Open targets (class C)`, with `#print axioms` lines for
  `HPC.Plane.janiszewski_polygonal_of_compact`, `HPC.Plane.exists_theta_point_open`,
  `HPC.Plane.compFamily_no_circular_open`, `HPC.Plane.treeChain_of_cover_open`,
  `HPC.Plane.theorem6_direct` (all five declared in `HPC/Plane/Theorem6Direct.lean`, namespace
  `HPC.Plane`). What they show is unknown (§0.3). The module docstring now describes the two
  imports, the groups, and the two empty last groups; nothing else in the file changed.

## §2. The root and the documents

**Root as received** (33 files): `Axioms.lean`, `BJ59A(1).lean`, `BJ59B.lean`, `BJ59C.lean`,
`BJ59D.lean`, `BJ59E.lean`, `COMMISSION-batch196.md` … `COMMISSION-batch203.md` (8),
`COMMISSION-batch198(1).md`, `COMMISSION-batch204.md`, `DEFECTS-LEDGER.md`, `HO16D.lean`,
`HO16E.lean`, `HPC.lean`, `HPCArchive.lean`, `HPCCensus.lean`, `LEDGER.md`, `LICENSE`, `OPEN.md`,
`README.md`, `axioms.txt`, `bingjones1959-1.pdf`, `defects-by-severity.pdf`,
`defects-by-severity.tex`, `domokos-prajs2022.pdf`, `lake-manifest.json`, `lakefile.toml`,
`lean-toolchain`; and `ARISTOTLE_SUMMARY.md`.

**Root after:** `README.md`, `LICENSE`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
`HPC.lean`, `HPCExtra.lean`, `HPCArchive.lean`, `HPCCensus.lean`, `Axioms.lean`, `axioms.txt`,
`LEDGER.md`, `OPEN.md`, `HPC/`, `doc/`, `scripts/`, and `ARISTOTLE_SUMMARY.md`.

**Moved or deleted:**

| file | what was done |
|---|---|
| `COMMISSION-batch204.md` | copied to `doc/batches/COMMISSION-batch204.md`, root copy deleted |
| `DEFECTS-LEDGER.md`, `defects-by-severity.tex`, `defects-by-severity.pdf` | moved to `doc/defects/` unchanged |
| `BJ59A(1).lean`, `BJ59B.lean` … `BJ59E.lean`, `HO16D.lean`, `HO16E.lean` | deleted: identical to `doc/batches/skeletons/BJ59A.lean`, `BJ59B.lean` … `BJ59E.lean`, `HO16D.lean`, `HO16E.lean` |
| `COMMISSION-batch196.md` … `COMMISSION-batch203.md`, `COMMISSION-batch198(1).md` | deleted: identical to the copies in `doc/batches/` (`198(1)` to `COMMISSION-batch198.md`) |
| `bingjones1959-1.pdf` | deleted: same sha256 as `doc/sources/bing-jones1959.pdf` |
| `domokos-prajs2022.pdf` | deleted: same sha256 as `doc/sources/domokos-prajs2022.pdf` |
| `doc/batches/COMMISSION-batch78(1).md` | renamed `doc/batches/COMMISSION-batch78.md` |
| `doc/theorems-3-4-scheduling.md` | deleted |
| `doc/batches/DEFECTS-LEDGER.md` | deleted |
| `README.md` (received) | copied to `doc/HISTORY.md` with a first line; long quotations: none |

No root copy differed from its partner, so no `-root` file was made. No `Hagopian76*.lean` was at
the root.

**Transcriptions moved.** 49 passages, 28905 words, from 30 files, into 15 files of
`doc/sources/transcriptions/`. Each passage is under a heading naming the file and section it came
from; in its place there is one line `[Quotation moved to doc/sources/transcriptions/<source>.md,
§<file>, <section>; batch 204.]`.

| file changed | passages | words | into |
|---|---:|---:|---|
| `doc/notes/hagopian84.md` ("A. Transcription", §§2–4) | 4 | 4720 | `hagopian84.md` |
| `doc/notes/ot82.md` (pp. 129, 130, 136–140) | 7 | 2913 | `ot82.md` |
| `doc/notes/jones75.md` ("1. Transcription") | 1 | 1843 | `jones75.md` |
| `doc/batches/COMMISSION-batch78.md` | 1 | 236 | `bing48.md` |
| `doc/batches/COMMISSION-batch79.md` | 2 | 652 | `bing48.md` |
| `doc/batches/COMMISSION-batch80.md` | 2 | 1377 | `bing48.md` |
| `doc/batches/COMMISSION-batch81.md` | 1 | 481 | `bing48.md` |
| `doc/batches/COMMISSION-batch82.md` | 2 | 1157 | `bing48.md` |
| `doc/batches/COMMISSION-batch83.md` | 1 | 788 | `bing48.md` |
| `doc/batches/COMMISSION-batch84.md` | 1 | 331 | `bing51duke.md` |
| `doc/batches/COMMISSION-batch85.md` | 2 | 1066 | `bing51duke.md` |
| `doc/batches/COMMISSION-batch88.md` | 1 | 952 | `bing51pacific.md` |
| `doc/batches/COMMISSION-batch89.md` | 1 | 241 | `bing51pacific.md` |
| `doc/batches/COMMISSION-batch90.md` | 1 | 472 | `bing51pacific.md` |
| `doc/batches/COMMISSION-batch92.md` | 1 | 1114 | `bing51duke.md` |
| `doc/batches/COMMISSION-batch96.md` | 1 | 303 | `bing51duke.md` |
| `doc/batches/COMMISSION-batch99.md` | 1 | 196 | `fugate66.md` |
| `doc/batches/COMMISSION-batch100.md` | 1 | 534 | `fugate66.md` |
| `doc/batches/COMMISSION-batch101.md` | 1 | 1554 | `fugate66.md` |
| `doc/batches/COMMISSION-batch104.md` | 1 | 1359 | `fugate69.md` |
| `doc/batches/COMMISSION-batch108.md` | 1 | 539 | `bing48arcs.md` |
| `doc/batches/COMMISSION-batch114.md` | 1 | 698 | `lehner61.md` |
| `doc/batches/COMMISSION-batch117.md` | 1 | 364 | `bing51duke.md` |
| `doc/batches/COMMISSION-batch121.md` | 1 | 920 | `bing48.md` |
| `doc/batches/COMMISSION-batch132.md` | 5 | 2061 | `ingram68.md` |
| `doc/batches/COMMISSION-batch134.md` | 2 | 788 | `vanmill04.md` |
| `doc/batches/COMMISSION-batch183.md` | 1 | 250 | `bing1960.md` |
| `doc/batches/COMMISSION-batch191.md` | 2 | 686 | `ot82.md` |
| `doc/batches/COMMISSION-batch200.md` | 1 | 153 | `bingjones59.md` |
| `doc/batches/skeletons/Hagopian76I.lean` (docstring of `hagopian76_T7`) | 1 | 157 | `hagopian76.md` |

What stayed, and why: quotations of 150 words or fewer between text of ours (for example
`doc/notes/hagopian84.md` §1, 138 words; the Cook 1967 theorem in `doc/notes/ot82.md`, 129 words;
O–T p. 129 and Cook p. 243 in commission 191, 116 and 137 words; van Mill's conventions and
Lemma 2.1, 121 words, and Proposition 3.5 with Corollary 3.6, 131 words, in commission 134); our
own analysis between the quotations (the "Suspected gap" and "Repair" of commission 134, the
bracketed glosses of commissions 82, 84, 85, the notes of commission 132); dictionaries, routes and
"places to check" lists, whose items are short quotations each followed by our text (commissions 137,
144–150, 155, 162). In commissions 86, 87, 93 (149 words), 106, 107, 178–182, 184–190, 192–194,
`REPORT-batch184.md` §2 (a summary), `REPORT-batch70.md` and `REPORT-batch116.md` (they quote our
own earlier text), `LEDGER.md` (longest quotation 96 words), `OPEN.md`, `doc/HISTORY.md`, the
lecture notes and `doc/exposition/classification-path.md` and `.tex`, no long quotation was found.
The search combined a scan for runs of quoted text (double quotes, blockquotes, LaTeX quotes and
quote environments) over 150 words with reading the passages it found and the files the commission
names; italic paraphrases of ours were left. `doc/defects/` was not touched.

**Long quotations in public files not edited here** (to be dealt with by David):

| file | line or page | source | words |
|---|---|---|---:|
| `HPC/Hagopian/H76Prop1.lean` | module docstring, lines 8–15 | Hagopian 1976, p. 346 | 153 |

No other docstring or comment under `HPC/` has a quoted run over 150 words (the next longest:
`HPC/Jones/Jones49F.lean` line 76, Jones 1949, 113 words). The PDFs of `doc/exposition/`
(`Theorem3-formalized-proof.pdf`, 9 pages; `pseudoarc-bing-exposition.pdf`, 41 pages) have no
quotation over 36 words.

## §3. Documentation

* `LICENSE`: the received file, unchanged at the root.
* `doc/defects/`: `DEFECTS-LEDGER.md`, `defects-by-severity.tex`, `defects-by-severity.pdf` (received,
  unchanged) and a new `README.md` (what the two documents are, Appendix B with the Lean names,
  the counts 23 and 18, and that both cite Lean names and file paths of this repository).
* `doc/sources/README.md`: one entry per file of `doc/sources/` (36 papers and book excerpts) with author, title,
  journal, volume, year and pages as printed on the first page (JSTOR cover sheets for the JSTOR
  files; missing fields marked "not printed on the first page"); the transcriptions (the 15 files of
  `transcriptions/`, `nadler-11-26-to-11-35.txt`, `moore1922-transcription.pdf`) with the source each
  transcribes; and the sentence that nothing in `doc/sources/` except the `README.md` is public.
* `doc/depcensus/README.md`: the build line names the four libraries; the definition of the nodes
  names the four `lean_lib`s and says the files are those of batch 203; the row of
  `edges-external.tsv` says that `scripts/DepCensus.lean` regenerates it and that neither it nor its
  `.gz` is in the repository.
* `README.md`: rewritten in the nine sections of §3 (152 lines). The two statements are copied from
  `HPC/BJ59/BJ59E.lean`. Status claims checked as reported in §6. The build times are not given
  (§0). Table 2 is the batch-203 table, with the papers per directory taken from the census's
  assignment of headlines to papers (`headlines-by-paper.tsv`). The credits draft keeps the citation
  lines for Aristotle from the received `README.md`.
* `doc/HISTORY.md`: the received `README.md` with a first line saying what it is. It contains no
  relative links (its only link is absolute) and no long quotation, so nothing else changed.

## §5. Corrections

* `LEDGER.md`, "Bing 1951 (Duke) and its commissions": the row of `theorem8_1951` is rewritten:
  `theorem8_1951` is the batch-92 commission's one-layer reading of `g_p`; Bing's `g_p` (p. 658) is
  quoted; with it the theorem holds (`theorem8_1951'`, batch 93); the refutation and the failure of
  the proof step are for the reading. No other place in `LEDGER.md` or `OPEN.md` calls Bing 1951
  Theorem 8 false.
* `LEDGER.md`, "Theorem 9 and Lehner's Theorem 1": the sentence is replaced as the commission says
  (three consecutive links of `D`, Bing's `E`; Bing's two-link clause, p. 737; the two-link form not
  formalized; no end clause), with the naming convention in one sentence.
* `OPEN.md`: new section `## Open items not scheduled` at the top with Bing 1948 Theorem 9 as printed
  (the two-link form).
* Docstrings (the only Lean edits of this batch under `HPC/`):
  * `HPC/Plane/Atriodic51CounterBing.lean`: docstring of `theorem8_1951_false`, and the module
    docstring after "refutes the partition clause of `theorem8_1951`".
  * `HPC/Plane/Atriodic51Counter.lean`: module title; docstring of `theorem8_1951_false_of_bingS`;
    docstring of `gElt_not_partition_S₀`.
  * `HPC/Plane/Atriodic51.lean`: docstring of `gElt` (with the sentence on `bingElt`,
    `Atriodic51BElt.lean`) and the heading "## The one-layer elements `g p`".
  * `HPC/Moore/M25BRefute.lean`: docstring of `not_moore1920_theorem4_singleton`, p. 340 → p. 342.
  * `HPC/Fold/Theorem7.lean`: docstring of `theorem9`, the sentence on Bing's `D` and `E` and the
    two-link mesh clause.
* **Other places that call the one-layer `g p` Bing's elements** (not edited):
  `HPC/Plane/Atriodic51CounterArc.lean` line 103, docstring "**Bing's element of a point of
  `[0,1) × {0}`** is `[0,1] × {0}`", on a lemma about the one-layer element. Borderline:
  `HPC/Plane/Atriodic51.lean` line 346, "Bing's proof of Theorem 8 has two parts: (i)
  `q ∈ g p → g p = g q` …", where `g p` is the one-layer element. The comment at the top of
  `HPC/Plane/Atriodic51Counter.lean` (lines 3–7) already says that the elements there are the
  commission's, not Bing's.

## §6. Checks

* Builds, `split.py` check 2, the regeneration of `axioms.txt`, the census and `rootfiles.sh`: not
  run (§0). `split.py` check 1: passed (§1).
* `axioms.txt` (received, unchanged): 4030 lines, 4016 entries (4009 with an axiom list, 7 with
  none); the axioms occurring are `propext` (4008 entries), `Quot.sound` (4000) and
  `Classical.choice` (3937), and no other.
* Census scripts: `scripts/DepCensus.lean` now imports `HPCExtra` and lists it in `libRoots` (and its
  docstring names four libraries); `scripts/report_tables.py` names `HPCExtra.lean` among the root
  files and says "four"; the comments of `scripts/Replay.lean` and `scripts/rootfiles.sh` name
  `HPCExtra` too (`Replay.lean` reads the module list from `modules.tsv`, so its code needed no
  change). `doc/depcensus/README.md` updated (§3).
* **Libraries, by reading the files** (comments and string literals removed): `HPC` (709 modules
  and `HPC.lean`), `HPCExtra` (125 and `HPCExtra.lean`), `HPCArchive` (25 and its root),
  `HPCCensus` (2 and its root): no `sorry`, no `admit`, no `axiom` declaration, no
  `implemented_by`. `native_decide` occurs 14 times, all in `HPC/Census/Census87Checks.lean`;
  `ofReduceBool` occurs nowhere.
* **Root files** (the count `rootfiles.sh` makes, by hand: the word `sorry` anywhere, comments
  included): `Axioms.lean` 0, `HPC.lean` 0, `HPCArchive.lean` 0, `HPCCensus.lean` 0,
  `HPCExtra.lean` 0. Libraries: `HPC.lean` → `HPC`, `HPCExtra.lean` → `HPCExtra`, `HPCArchive.lean`
  → `HPCArchive`, `HPCCensus.lean` → `HPCCensus`; `Axioms.lean` → none.
* **Public files** (2219 files: the tree minus `doc/sources/` except its `README.md`, `.tar.gz`
  files, `edges-external.tsv*`, `ARISTOTLE_SUMMARY.md`, `.git/`, `__pycache__/`, `.gitignore`):
  * `sorry` outside comments and string literals in the 869 Lean files outside `doc/` (861 under
    `HPC/`, 5 at the root, 3 in `scripts/`): none. (`scripts/Replay.lean` has the word once, in the
    string `" sorry\n"`.)
  * `RequestProject`: outside `doc/batches/` one hit, `lake-manifest.json` line 94 (§0.6); inside
    `doc/batches/` 22 hits in 19 files (old reports, commissions 103 and 204, one audit file).
  * `/home/` and `/Users/`: no hit outside `doc/batches/`; inside it one hit each, both in
    `COMMISSION-batch204.md` (the commission's own text).
  * No public PDF outside `doc/exposition/` and `doc/defects/`; no file over 50 MB; no public file
    with the content of a file in `doc/sources/`.
* **The ten largest public files:**

| file | bytes |
|---|---:|
| `doc/depcensus/edges.tsv` | 7718606 |
| `doc/depcensus/nodes.tsv` | 5393431 |
| `doc/census/census-batch49d.log` | 2313309 |
| `doc/census/census-batch49c.log` | 950229 |
| `doc/census/census-batch49b.log` | 946852 |
| `doc/depcensus/closure.tsv` | 744276 |
| `doc/census/seeds-batch72.txt` | 730718 |
| `doc/depcensus/headlines-by-paper.tsv` | 602322 |
| `LEDGER.md` | 542271 |
| `doc/depcensus/headlines.tsv` | 510157 |

## §7. The listing and the tarball

`doc/batches/batch204-MANIFEST.txt` lists every file added (A), modified (M) or deleted (D) relative
to `/tmp/start-tree.txt`, with the destination of every moved file. The listing
`doc/batches/batch204-TREE.txt` and the tarball `doc/batches/batch204-files.tar.gz` were made last,
with the commission's commands; their counts are in the last `STATUS` line of the run, not here.

STATUS: §1 split done / builds, check 2, axiom regeneration open (no Lean toolchain in this run)
STATUS: §2 root and transcriptions done
STATUS: §3 documentation done
STATUS: §5 corrections done
STATUS: §6 checks done by reading files / census rerun open (no Lean toolchain in this run)
