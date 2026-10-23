# Commission: batch 204 — house cleaning for a public repository

**Go!** This batch starts a new project. The previous project can no longer run, so this one
starts from the repository as §0 describes it: the state after batch 203 and the runs that wrote
the lecture notes, reassembled from what the previous project delivered. There is no `.git` and
no `.lake`: nothing is built yet (§1 says how to build). Five files come with this commission,
at the root:
* `COMMISSION-batch204.md`, this text;
* `DEFECTS-LEDGER.md`, the project's defects ledger, sorted by source (my file; the edition for
  the public repository);
* `defects-by-severity.tex` and `defects-by-severity.pdf`, the same defects ordered by severity
  (my file; the `.tex` compiles on its own with XeLaTeX);
* `LICENSE`, the Apache License 2.0, copied from Mathlib's repository.

**Before any change**, record the starting point, since there is no git history to compare
with. From the root:
```
find . \( -path ./.git -o -path ./.lake \) -prune -o -type f ! -path ./ARISTOTLE_SUMMARY.md \
  -print | sed 's|^\./||' | LC_ALL=C sort | xargs -d '\n' sha256sum > /tmp/start-tree.txt
rm -rf /tmp/depcensus-203 && cp -a doc/depcensus /tmp/depcensus-203
cp axioms.txt /tmp/axioms-203.txt
```
The comparisons of §6, the manifest of §7 and the root as received (report §2) are relative to
these: the folder as received, the five files that came with this commission included. In this
commission, "the received `axioms.txt`" means `/tmp/axioms-203.txt` (the batch-203 file). If
these copies are lost (for example by a restart), say so in the report.

Then save a copy of this commission as `doc/batches/COMMISSION-batch204.md`, put the other files
where §3 says, and delete the root copies of all five except `LICENSE`.

The repository is to be made public on GitHub under the Apache License 2.0. This batch prepares
it. It proves nothing new.

**Rules.**
* The first line of the report names the commission it read.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **No declaration changes.** No statement, proof, declaration name or namespace changes. Inside
  `HPC/` the only edits allowed are the docstrings named in §5. No file under `HPC/` is renamed
  or moved (the one rename of §1 is already made): the ledgers, the severity document and the
  census cite file paths and names.
* `axioms.txt` changes only at its end, by the lines of the new group of §1 (`Axioms.lean`).
  Regenerate it to a temporary file; its first 4030 lines must equal the received `axioms.txt`
  (`cmp` on `head -n 4030`); only then replace `axioms.txt` by it. Report the result.
* Do not add a `.gitignore` at the root, a `.gitattributes` or a `.github/` directory: David's
  publishing script writes them, and it publishes no `.gitignore` or `.gitattributes` from your
  tree (`doc/census/.gitignore` stays in your tree but is not published).
* Progress lines: `STATUS: <item> done / open (<obstruction>)`.

## 0. On batch 203

* **Delivery.** Batch 203 left `axioms.txt` at 4030 lines and changed no file under `HPC/`. I
  recomputed the closure of its census myself, by breadth-first search over
  `nodes.tsv`, `edges.tsv` and `edges-external.tsv.gz` from the two targets with the used rule
  of commission 203 §2.2: 17643 constants, equal to `closure.tsv`; 4689 used, equal to
  `used.txt`; every per-module count of `modules.tsv` agrees.
* **Since batch 203.** The runs after batch 203 added the lecture notes (`doc/lecture-notes/`, eight
  volumes), `doc/exposition/classification-path.md` and `.tex`, `scripts/md2tex_classification.py`,
  and one Lean file, `HPC/Plane/Theorem6Direct.lean`, which `HPC.lean` imports. `axioms.txt` does
  not cover it yet; §1 adds it.
* **How this tree was assembled.** The download David received from the previous project was not its
  whole tree. Compared with that tree as the tarballs reconstruct it, the download lacked about 120
  files: the 72 Lean files under `HPC/Hagopian/`, `HPC/Jones/` and `HPC/Span/`;
  `doc/notes/hagopian84.md` and `doc/notes/hagopian76-cases.md`; `COMMISSION-batch178.md` …
  `COMMISSION-batch194.md` and `COMMISSION-batch199.md` in `doc/batches/`; ten of the audits
  `doc/batches/audits/axioms-batch178.txt` … `axioms-batch188.txt`; and 18 skeletons in
  `doc/batches/skeletons/` (`BJ59B`, `HO16A`, `HO16B`, `Hagopian76W` … `Hagopian76AC`, `Hagopian84A`
  … `Hagopian84D`, `Jones75A`, `Jones75B`, `OT82A`, `OT82B`); possibly also some root copies of
  commissions and skeletons. This project's tree is the latest download with those files added from
  the batch tarballs `doc/batches/batch178-files.tar.gz` … `batch203-files.tar.gz` (only files the
  download lacked; nothing it had was replaced). Fourteen root files were in no tarball and are
  absent: `COMMISSION-batch178.md` … `COMMISSION-batch183.md` and `Hagopian76W.lean` …
  `Hagopian76AB.lean`, whose content `doc/batches/` and `HPC/Hagopian/` hold, and `Scratch.lean` and
  `Scratch2.lean`, which nothing imports; §2 would have deleted all fourteen. Two things are left
  out of this project to keep the upload small: the batch tarballs themselves (every file they
  carried is in the tree, and David keeps them), and `doc/depcensus/edges-external.tsv.gz`; §6
  regenerates `edges-external.tsv` uncompressed and then deletes it. If the build or the census
  needs a file that is missing, stop and report it; do not recreate it. The public repository is
  assembled from your download and this batch's tarball, so this batch's tarball carries the whole
  tree (§7), and a listing with checksums lets David's script check that what it assembles is your
  tree. If your system keeps the project under git, run `git status --porcelain --ignored` at the
  end and summarize it in the report (untracked, ignored, committed).
* **What the census showed.** The import closure of `HPC/BJ59/BJ59E.lean` has 709 of the 861
  modules now under `HPC/` (860 at batch 203, and `Theorem6Direct`). Of these, 446 have a used
  declaration and 263 are imported only. The other 152 are 25 in `HPC/Archive`, 2 in
  `HPC/Census`, and 125 outside the closure (94 in `HPC/Fold`, 14 in `HPC/Plane`, among them
  `Theorem6Direct`, 8 in `HPC/BJ59`, 4 in `HPC/Hagopian`, 2 each in `HPC/HO16` and
  `HPC/PseudoArc`, 1 in `HPC/Chains`). Several counterexamples the ledgers cite live there
  (`Fold.Theorem8Counter`, `Chains.Counterexample`, `Plane.NonCut51Counter`), so nothing is to be
  deleted.
* **Two corrections to the ledgers** (§5). Bing 1951 (Duke) Theorem 8 is true as printed. The
  refutation in `Plane/Atriodic51CounterBing.lean` is of the one-layer reading of `g_p` that my
  batch-92 commission introduced; Bing's two-layer `g_p` gives `theorem8_1951'`. And Bing 1948
  Theorem 9 is proved in a three-link form (`Fold.theorem9`, "three-link form for the mesh
  clause"), while Bing prints "each link of F is a subset of the sum of two adjacent links of E"
  (p. 737).

## 1. The library split

* **`HPC`**: the classification and everything its files import. Rewrite `HPC.lean` so that it
  imports exactly `HPC.BJ59.BJ59E` (which contains `ho16_classification₄`,
  `ho16_classification_plane₄`, `dp22_theorem61'`, `dp22_theorem61_iff'` and `hoCircleLike'`, and
  imports `HPC.BJ59.BJ59D`, which contains `ho16_classification_atomic'`). Its build is then the
  import closure of that module, 709 modules by my count.
* **`HPCExtra`** (new `lean_lib`, new root file `HPCExtra.lean`): imports, one line each in sorted
  order (`LC_ALL=C`), every module under `HPC/` that is outside `HPC`'s import closure and outside
  `HPC/Archive` and `HPC/Census` (125 by my count). These are mostly working files of the Theorem
  3–4 campaign (`HPC/Fold`, 94 modules), the `NonVac` and certificate files of batches 196–202, the
  band and cube models of `HPC/Plane`, `Plane.Theorem6Direct`, and the counterexamples named in §0.
  Its `lakefile.toml` comment says that: modules outside the classification's import closure.
* **`HPCArchive`** and **`HPCCensus`** stay as they are.
* **The one rename, already made.** `HPC/Chains/Aux.lean` is now `HPC/Chains/Auxiliary.lean` (module
  `HPC.Chains.Auxiliary`), and the import lines that named it in `HPC/Chains/Basic.lean`,
  `HPC/Chains/Consolidation.lean`, `HPC/PseudoArc/Description.lean` and `HPC.lean` name the new
  module; nothing else in those files changed. I made the rename before this project started,
  because `AUX` is a reserved device name on Windows, where David works: Windows will not unpack a
  file `…/Aux.lean`, and Git for Windows refuses to check one out. Check that no `.lean` file still
  imports `HPC.Chains.Aux`, and that no other path in the tree has a component that Windows rejects
  (the names `CON`, `PRN`, `AUX`, `NUL`, `CONIN$`, `CONOUT$`, `COM0`–`COM9`, `LPT0`–`LPT9`, also
  with any extension; the characters `<>:"|?*`; a trailing dot or space) and that no two paths
  differ only in case. Report what you find, and rename nothing.
* Generate `HPCExtra.lean` with a script, `scripts/split.py`, which reads the `import` lines of
  the files under `HPC/`, computes the import closure of `HPC.BJ59.BJ59E`, and writes the root
  file. Two checks, reported with their counts:
  1. every module under `HPC/` is in exactly one of: the closure of `HPC.lean`, the imports of
     `HPCExtra.lean`, `HPC/Archive`, `HPC/Census`;
  2. the closure computed by `split.py` equals, as a set, the `HPC.*` modules (not counting the
     root module `HPC` itself) of the environment that imports `HPC`
     (`(← getEnv).header.moduleNames`, in a few lines of Lean in `scripts/`).
* `Axioms.lean`: import `HPC` and `HPCExtra` (every name its `#print axioms` lines name must still
  resolve). Add one group, `-- ## Bing 1951 (Duke), Theorem 6 by the compact Janiszewski
  theorem`, just before `-- ## Open targets (class C)`, with a `#print axioms` line for each of
  the five theorems of `HPC/Plane/Theorem6Direct.lean`: `janiszewski_polygonal_of_compact`,
  `exists_theta_point_open`, `compFamily_no_circular_open`, `treeChain_of_cover_open`,
  `theorem6_direct` (namespace `HPC.Plane`). Each must show the three standard axioms or fewer;
  report what they show. Update the module docstring to describe the imports and the groups as
  they are now (the present one mentions open-target groups with `sorryAx` that no longer exist).
  Change nothing else in it.
* `lakefile.toml`: the package name `RequestProject` becomes `hpc`; add the `lean_lib` `HPCExtra`
  with a comment as for the others, and with `name` and `roots` on the two lines after
  `[[lean_lib]]`, as in the others (`scripts/rootfiles.sh` reads them there); replace the comment of
  `HPC` ("The verified main line and the open targets") by one saying what it now is;
  `defaultTargets` stays `["HPC"]`. The Mathlib requirement does not change. Do not run
  `lake update`. If Lake rewrites `lake-manifest.json` because of the new name, keep its rewrite and
  report the diff; otherwise leave the file unchanged.
* **Building, and build times.** Nothing is built when the project starts. First run
  `lake exe cache get` for Mathlib (if it cannot fetch the cache, build Mathlib and report that and
  its time). Then, after the edits of this section and the Lean edits of §5 (so that one build
  covers them all), run `lake build HPC`, `lake build HPCExtra`, `lake build HPCArchive`,
  `lake build HPCCensus` in that order; each later build reuses the earlier ones. Report the
  wall-clock time of each, the number of cores (`nproc`), the memory of the machine and the size of
  `.lake/build` afterwards (`du -sh`). Then time `lake env lean Axioms.lean > /tmp/axioms.txt`. If a
  file fails to build, stop the batch there: change nothing to make it build, write
  `doc/batches/REPORT-batch204.md` with the file, the error and what was done before, and skip the
  rest, including §7's listing and tarball.

## 2. The root and the documents

Afterwards the root holds only: `README.md`, `LICENSE`, `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `HPC.lean`, `HPCExtra.lean`, `HPCArchive.lean`, `HPCCensus.lean`, `Axioms.lean`,
`axioms.txt`, `LEDGER.md`, `OPEN.md`, and the directories `HPC/`, `doc/`, `scripts/`, plus
`ARISTOTLE_SUMMARY.md` (the one received is the previous project's summary of its last run;
leave it, or let your system overwrite it; it is not published). In particular:
* **Skeleton copies**: every `.lean` file at the root besides the five `.lean` files of that list
  (`BJ59A(1).lean`, `BJ59B.lean` … `BJ59E.lean`, `HO16D.lean`, `HO16E.lean`, `Hagopian76W.lean` …
  `Hagopian76AB.lean` if present, …). If `doc/batches/skeletons/` holds a file of the same name
  (without `(1)`) with identical content, delete the root copy. If it holds one with different
  content, move the root copy there as `<name>-root.lean` and report it. Otherwise move it there
  under its own name, without `(1)`.
* **Commission copies at the root**: every `COMMISSION-batch*.md` there (for example
  `COMMISSION-batch196.md` … `COMMISSION-batch203.md`, `COMMISSION-batch198(1).md`). Compare each
  with `doc/batches/COMMISSION-batchNNN.md`. Delete identical root copies. If `doc/batches/`
  has no copy, move the root copy there. If the two differ, move the root copy to `doc/batches/`
  with the suffix `-root` and report it. In `doc/batches/`, `COMMISSION-batch78(1).md` has no
  partner without `(1)`: rename it `COMMISSION-batch78.md`.
* **PDF files at the root** (`bingjones1959-1.pdf`, `domokos-prajs2022.pdf`): move to
  `doc/sources/` unless a file with the same content (sha256), under any name, is there already,
  in which case delete the root copy (`bingjones1959-1.pdf` has the content of
  `doc/sources/bing-jones1959.pdf`).
* `doc/theorems-3-4-scheduling.md` is an old copy of my private working notes: delete it. Delete
  `doc/batches/DEFECTS-LEDGER.md`, an old copy of the defects ledger (the current one goes to
  `doc/defects/`, §3).
* **Transcriptions.** Most of the sources are under copyright, and so are long verbatim
  transcriptions of them. A *long quotation* here is a passage of more than 150 words quoted
  continuously, or a run of quotations from one source with no text of ours between them that
  together exceed 150 words. Move every long quotation in any file under `doc/` or at the root
  into `doc/sources/transcriptions/<source>.md` (one file per source: `hagopian84.md`, `ot82.md`,
  `jones75.md`, …; each passage under a heading naming the file and section it came from), and
  leave in its place one line: `[Quotation moved to doc/sources/transcriptions/<source>.md,
  §<heading>; batch 204.]`. Keep everything else: dictionaries, routes, analysis, and quotations
  of a sentence or two. Files known to hold long quotations: `doc/notes/hagopian84.md` (its "## A.
  Transcription"), `doc/notes/ot82.md` (its page-by-page quotations), `doc/notes/jones75.md`; my
  commissions 79–90, 92, 101, 106, 107, 132, 134 and 178–194, and `REPORT-batch184.md` §2 in
  `doc/batches/`. Check every other file under `doc/` too, the lecture notes and
  `doc/exposition/classification-path.md` and `.tex` among them (the two files of `doc/defects/` are
  exempt: I checked them, and no quotation there exceeds 100 words). Report every file changed,
  with the number of passages and words moved. Docstrings and comments under `HPC/` and the PDFs
  in `doc/exposition/` are public too but are not to be edited here: list every long quotation
  in them (file, line or page, source, words), and I will deal with them.

## 3. Documentation

* **`LICENSE`** at the root: the file that came with this commission, unchanged.
* **`doc/defects/`**: `DEFECTS-LEDGER.md`, `defects-by-severity.tex`, `defects-by-severity.pdf` (the
  files that came with this commission, unchanged), and a short `README.md`. The `README.md` says
  what the two documents are (the ledger by source; the same defects ordered by severity, with every
  Lean name cited listed in its Appendix B), gives the counts (23 printed statements false, 18
  printed proofs defective with the statement true), and says that both cite Lean names and file
  paths of this repository.
* **`doc/sources/README.md`**: the bibliography of the files in `doc/sources/`, one entry per
  file: file name, author, title, journal, volume, year, pages, as printed on the first page (read
  the first page of each file); the transcriptions of §2 and `nadler-11-26-to-11-35.txt` listed
  with the source each transcribes. Add one sentence: nothing in `doc/sources/` except this
  `README.md` is part of the public repository.
* **`doc/depcensus/README.md`**: where it says to take `edges-external.tsv.gz` from a tarball, say
  instead that `scripts/DepCensus.lean` regenerates `edges-external.tsv` and that neither file is
  in the repository.
* **`README.md`**, rewritten for an outside reader, in this order:
  1. Title (`Homogeneous plane continua in Lean`) and one paragraph: the classification of
     homogeneous plane continua (Hoehn and Oversteegen, Acta Math. 216 (2016)) is formalized,
     together with the results from earlier papers that its proof uses. Then the two final
     theorems, `HPC.BJ59.ho16_classification₄` and `HPC.BJ59.ho16_classification_plane₄`, copied
     verbatim from `HPC/BJ59/BJ59E.lean` (statements only, in a `lean` code block), each with one
     sentence in words.
  2. Status: no `sorry` in the four libraries; the statement skeletons in
     `doc/batches/skeletons/` contain `sorry` and belong to no library. Every theorem of
     `axioms.txt` (say how many lines and entries) on `propext`, `Classical.choice`, `Quot.sound`
     or fewer; `native_decide`, and with it `Lean.ofReduceBool`, occurs only in `HPCCensus` (check
     both claims and state what you found). The kernel replay of the classification's closure
     (`doc/depcensus/replay.txt`), in two sentences.
  3. Building: the toolchain, the Mathlib version, `lake exe cache get`, `lake build`, `lake build
     HPCExtra HPCArchive HPCCensus`, the axiom audit command, and the times of §1 with the
     machine they were measured on.
  4. Layout: the four libraries (one sentence each; `HPCExtra` as described in §1), then a table
     of the directories under `HPC/` with the papers each formalizes and, from the census, its
     used share (Table 2 of `doc/depcensus/report-tables.md` as the census of §6 rewrites it).
  5. What the classification uses: three sentences from the census, and a pointer to
     `doc/depcensus/`.
  6. The published proofs: one paragraph pointing to `doc/defects/` with the two counts, and the
     two items the severity document puts first: the step from Jones's decomposition to the circle
     of pseudo-arcs, used without proof in Hoehn–Oversteegen's Theorem 2, whose first proof we
     found is Domokos and Prajs's 2022 preprint (Theorem 6.1); and Bing and Jones's sketch of a
     plane circle of pseudo-arcs, replaced here by another construction. Quote nothing beyond what
     those documents quote.
  7. Records: `doc/batches/` (the commissions and reports, batch by batch), `LEDGER.md`,
     `OPEN.md`, `doc/notes/`, `doc/exposition/`, `doc/HISTORY.md`; and the lecture notes,
     `doc/lecture-notes/` (eight volumes of LaTeX following the formal proof, with
     `doc/lecture-notes/README.md`), in one sentence.
  8. Credits, as a draft for David to edit: the project was directed by David V. Feldman
     (University of New Hampshire); the Lean code was written by Aristotle (Harmonic) from
     commissions, and in many places statement skeletons, written by Claude (Anthropic), which
     also wrote the defects ledger and the severity document. Keep your system's citation lines
     for Aristotle in this section.
  9. License: Apache License 2.0, `LICENSE`. Add: the quotations from published papers in the
     documentation remain under their publishers' copyright and are not covered by this license.

  Keep it under 250 lines. Write plainly: no adjectives about the result. Sections 1–6 describe
  the repository as it is; batch numbers, dates and the order in which things were done belong in
  section 7 and in the records it lists.
* **`doc/HISTORY.md`**: `README.md` as it stands at the start of this batch, unchanged except
  for a first line saying what it is (the batch-by-batch record kept in `README.md` until batch
  203), for relative links, which you adjust so that they resolve from `doc/`, and for long
  quotations, which §2 moves like any other.

## 4. What stays out of the public repository

Nothing to do here except to know it. David's script publishes the download overlaid with this
batch's tarball, leaving out: everything in `doc/sources/` except its `README.md` (so the
transcriptions of §2 stay private), `doc/batches/*.tar.gz`, `doc/depcensus/edges-external.tsv`
and its `.gz`, `ARISTOTLE_SUMMARY.md`, `.lake/` and `.git/` at any depth, `__pycache__/`. Do not
rely on those files from any file that will be public (the README may mention that the census
regenerates `edges-external.tsv`, and the notes may cite a transcription by its path). The
script stops if: a file at the root is not in the list of §2; a PDF lies outside
`doc/exposition/` and `doc/defects/`; a file exceeds 50 MB; an import of a local module does
not resolve; a module under `HPC/` belongs to no library; `sorry`, `admit` or an `axiom`
declaration occurs in a Lean file outside `doc/`; an entry of `axioms.txt` has an axiom other
than the three; a path is invalid on Windows or two paths differ only in case; a public file has
the content of a file in `doc/sources/`; or the assembled files differ from the listing of §7.

## 5. Corrections

* **`LEDGER.md`, "Bing 1951 (Duke) and its commissions"**: the row for `theorem8_1951` says
  "(Bing's Theorem 8, as stated)" and "Bing's proof breaks at `H_1` contains `H_2` interiorly".
  Rewrite it: `theorem8_1951` is the batch-92 commission's one-layer reading of `g_p` ("the
  intersection of all continua containing `p` interiorly"); Bing (p. 658) defines `g_p` as "the
  intersection of all continua which contain interiorly a continuum that contains p interiorly",
  and with that definition the theorem holds (`theorem8_1951'`, batch 93). The refutation, and
  the failure of the proof step, are for the reading, not for Bing. Check the other places in
  `LEDGER.md` and `OPEN.md` that call Theorem 8 false; correct them and report them.
* **Docstrings in `HPC/Plane/`** (with the docstrings of `not_moore1920_theorem4_singleton` and
  `theorem9` below, the only Lean edits of this section; the text between the quotation marks is
  what is there now):
  * `Atriodic51CounterBing.lean`, docstring of `theorem8_1951_false`: replace
    "**`theorem8_1951` is false.**" by a sentence saying that the one-layer reading of Bing's
    Theorem 8 is false, and that Bing's own statement is `theorem8_1951'`.
  * `Atriodic51CounterBing.lean`, module docstring: after "refutes the partition
    clause of `theorem8_1951`" add "(the one-layer reading of Bing's Theorem 8; Bing's own
    statement is `theorem8_1951'`)".
  * `Atriodic51Counter.lean`, module title (`# Batch 92: Bing's elements …`): "Bing's elements
    `g p` need not partition" becomes "The one-layer elements `g p` need not partition";
    docstring of `theorem8_1951_false_of_bingS`: after "**`theorem8_1951`" add " (the one-layer
    reading)"; docstring of `gElt_not_partition_S₀`: "**Bing's elements do not partition `S₀`**"
    becomes "**The one-layer elements do not partition `S₀`**".
  * `Atriodic51.lean`, docstring of `gElt`: "**The elements of Bing's decomposition**" becomes
    "**The one-layer elements**", followed by one sentence: Bing's own elements (p. 658) are
    `bingElt` (`Atriodic51BElt.lean`). The heading "## Bing's elements `g p`" becomes "## The
    one-layer elements `g p`".
  * Any other docstring or comment under `HPC/` that calls the one-layer `g p` Bing's elements:
    list it in the report; do not edit it.
* **Docstring of `not_moore1920_theorem4_singleton`** (`HPC/Moore/M25BRefute.lean`): Definition 4
  of Moore 1920 is on p. 342, not p. 340.
* **Bing 1948 Theorem 9.** In `Fold.theorem9` the chains are named the other way round from Bing:
  Bing's `D` (crooked in `E`, and consolidated into `F`) is `E` in the Lean statement, and Bing's
  `E` is `D`.
  * `LEDGER.md`, the paragraph "Theorem 9 and Lehner's Theorem 1": replace "is proved as Bing
    states it, without Lehner's end clause" by: it is proved with every block of `F` in three
    consecutive links of `D` (Bing's `E`), while Bing prints "each link of F is a subset of the
    sum of two adjacent links of E" (p. 737); the printed two-link form is not formalized; the
    statement has no end clause (Lehner's). State the naming convention there in one sentence.
  * `HPC/Fold/Theorem7.lean`, docstring of `theorem9`: after "Batch 82: proved as stated." add
    one sentence: Bing's chains `D` and `E` are this statement's `E` and `D`; Bing's mesh clause
    has two adjacent links, and that form is not formalized.
  * **`OPEN.md`**: add Bing 1948 Theorem 9 as printed (the two-link form) as an open item, at the
    top under a heading `## Open items not scheduled` (not to be attempted in this batch).

## 6. Checks

* All four libraries build. `scripts/split.py` reports the partition of §1 and the comparison
  with the environment's module list; both agree.
* `axioms.txt`: regenerated to a temporary file; its first 4030 lines identical to the received
  `axioms.txt` (`cmp`), followed by the lines of the new group, each on the three standard axioms
  or fewer.
* **The census.** Add `HPCExtra` to `scripts/DepCensus.lean` wherever it names the libraries (its
  imports and its list of library roots), so that the nodes still cover every module; update
  `doc/depcensus/README.md` (four libraries) and `scripts/report_tables.py` if it names them. Then
  run the whole sequence of `doc/depcensus/README.md` again ("Regenerating": `DepCensus.lean`,
  `closure.py`, `Replay.lean`, `headlines_by_paper.py`, `report_tables.py`). Required: the primary
  closure is unchanged (17643 constants, 4689 used, 446 modules with a used declaration);
  `closure.tsv` and `used.txt` are identical to the files in `/tmp/depcensus-203/` after the
  substitution `s/HPC\.Chains\.Aux\b/HPC.Chains.Auxiliary/g` in the old files; so is `edges.tsv`
  except for lines whose source is a declaration of `HPC.Plane.Theorem6Direct`; so is `nodes.tsv`
  except for those declarations and for the line numbers of declarations in the five files whose
  docstrings §5 edits; `modules.tsv` changes only by the rename, the root files, the row of
  `HPC.Plane.Theorem6Direct` and the line counts of those five files. Report every other difference,
  and whether `import-only.txt` changed. When the sequence has finished, delete the regenerated
  `edges-external.tsv` (about 170 MB): it goes into neither the listing nor the download.
* Root listing after the cleaning (`scripts/rootfiles.sh`): every `.lean` file at the root, with
  its library and its `sorry` count. None of them may contain `sorry`; `rootfiles.sh` counts the
  word in comments too, so the docstrings you write in `Axioms.lean`, `HPC.lean` and
  `HPCExtra.lean` must not use it.
* `grep` the files that will be public (§4) for `sorry` outside comments and string literals in Lean
  files outside `doc/` (the string `" sorry\n"` in `scripts/Replay.lean` does not count; David's
  script skips string literals too), and for the strings `RequestProject`, `/home/` and `/Users/`;
  report each hit outside `doc/batches/` and the number of hits inside it. List the ten largest
  public files with their sizes.

## 7. The report, the listing and the tarball

`doc/batches/REPORT-batch204.md`, first line naming this commission, then: §0 omissions and
deviations, and the `git status` summary of §0 if there is one; §1 the split (the two checks;
the outcome of `lake exe cache get`; the build times and the timing of `Axioms.lean`; the
`lake-manifest.json` diff, if any; the Windows check; the new axiom group); §2 the root as
received and after, every file moved or deleted, with where it went, every transcription moved,
and the list of long quotations in docstrings under `HPC/` and in the PDFs of `doc/exposition/`;
§3 the documentation written; §5 the corrections, with every place found; §6 the checks.

`doc/batches/batch204-MANIFEST.txt`: every file added (A), modified (M) or deleted (D) relative
to `/tmp/start-tree.txt`, with the destination of every moved file.

**Last, after everything else is final**, in this order, from the root:
1. **The listing** `doc/batches/batch204-TREE.txt`: the sha256 of every file of the tree except
   `.git/`, `.lake/`, the tarballs and `ARISTOTLE_SUMMARY.md` (it includes the sources, the report
   and the manifest):
   ```
   find . \( -path ./.git -o -path ./.lake \) -prune -o -type f \
     ! -path './doc/batches/*.tar.gz' ! -path ./doc/batches/batch204-TREE.txt \
     ! -path ./ARISTOTLE_SUMMARY.md -print | sed 's|^\./||' | LC_ALL=C sort \
     | xargs -d '\n' sha256sum > doc/batches/batch204-TREE.txt
   ```
2. **The tarball** `doc/batches/batch204-files.tar.gz`. It carries the whole tree, not only the
   changes: every file of the listing except the sources in `doc/sources/` and
   `doc/depcensus/edges-external.tsv*`, plus `doc/sources/README.md`, the transcriptions and the
   listing itself:
   ```
   sed 's/^[0-9a-f]\{64\}  //' doc/batches/batch204-TREE.txt \
     | grep -v -i -e '^doc/sources/' -e '^doc/depcensus/edges-external\.tsv' \
     > /tmp/batch204-list.txt
   { echo doc/sources/README.md; find doc/sources/transcriptions -type f | LC_ALL=C sort; \
     echo doc/batches/batch204-TREE.txt; } >> /tmp/batch204-list.txt
   tar -czf doc/batches/batch204-files.tar.gz -T /tmp/batch204-list.txt
   ```
3. Check: `tar -tzf doc/batches/batch204-files.tar.gz | wc -l` equals `wc -l <
   /tmp/batch204-list.txt`. The report cannot carry these numbers, because the listing covers
   the report. Put them in the last `STATUS` line instead: the two counts, the number of lines
   of the listing, and the size of the tarball.

Change no file after step 1 except by steps 2–3.
