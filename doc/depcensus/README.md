# `doc/depcensus/` — the dependency census of the classification (batch 203)

What the classification of homogeneous plane continua uses, computed from the Lean environment.
The report is `doc/batches/REPORT-batch203.md`. (`doc/census/` is a different thing: the
`native_decide` census of batch 87.)

## Regenerating

From the repository root:

```
lake build HPC HPCExtra HPCArchive HPCCensus
lake env lean scripts/DepCensus.lean        # writes every census file below (about 1.5 min)
python3 scripts/closure.py                  # second computation; writes closure-check.txt
lake env lean scripts/Replay.lean           # kernel replay; writes replay.txt (about 2.5 min)
python3 scripts/headlines_by_paper.py       # writes headlines-by-paper.tsv, papers.tsv
bash scripts/rootfiles.sh                   # writes root-files.tsv, unbuilt-files.txt
python3 scripts/report_tables.py > doc/depcensus/report-tables.md
```

`scripts/` is imported by no library. The order matters only in that every step after the first
reads files the first writes.

## Definitions (as in `scripts/DepCensus.lean`)

* **Nodes**: every constant whose module belongs to one of the four `lean_lib`s of
  `lakefile.toml` (`HPC`, `HPCExtra`, `HPCArchive`, `HPCCensus`). (The census files of this folder
  are those of batch 203, when there were three libraries and 863 modules; batch 204 split `HPC`
  into `HPC` and `HPCExtra` and could not rerun the census.)
* **Declaration** of a constant: the declaration a reader sees. Constructors, recursors,
  projections, `casesOn`/`recOn`/`brecOn`/`below` (auxiliary recursors), `noConfusion`,
  `noConfusionType`, `ctorIdx`, `inj`, `injEq`, `sizeOf_spec` belong to their inductive type or
  structure; matchers (`match_n`), `proof_n`, `_simp_n`, `eq_n`, `eq_def`, `induct` and every
  other component beginning with `_` belong to the declaration they were generated for. A
  `_private` name is read through `privateToUserName?`.
* **Counted declaration**: a theorem, definition, structure, inductive type, instance or
  abbreviation written in a source file: its kind is one of these, it is its own declaration, it
  has a declaration range, and its name (after the private prefix) has no internal component.
  Syntax, macro and notation constants (`kind = syntax`) are not counted.
* **Edges** of a node `c`: the constants occurring in its type or value
  (`ConstantInfo.getUsedConstantsAsSet`); for an inductive type also its constructors and
  recursor.
* **Raw closure** of targets: the constants reachable from them along the edges (external
  constants are reached but have no outgoing edges here).
* **Used**: a counted declaration that is itself in the raw closure, or a structure (inductive
  type) one of whose projections or constructors is. A declaration is not marked used because one
  of its auxiliary constants is.
* **Primary targets**: `HPC.BJ59.ho16_classification_plane₄`, `HPC.BJ59.ho16_classification₄`.
* **Lines covered** by used declarations: per module, the union of their declaration ranges, each
  extended upwards over its docstring (Lean's declaration ranges already include the docstring of
  a counted declaration, so the extension is a safeguard).

## Files

| file | content | written by |
|---|---|---|
| `nodes.tsv` | every node: name, user name, module, kind, declaration, counted (0/1), start and end line of its declaration range, start line extended over the docstring, headline (docstring begins with `**`) | `DepCensus.lean` |
| `edges.tsv` | edges whose target is a node | `DepCensus.lean` |
| `edges-external.tsv` | edges whose target is external, with the target's package and module (Init, Batteries and Mathlib occur; no Aesop, Lean or Std constant is a target). **About 172 MB.** `scripts/DepCensus.lean` regenerates it; neither `edges-external.tsv` nor `edges-external.tsv.gz` is in the repository | `DepCensus.lean` |
| `closure.tsv` | the primary raw closure: each constant, with `node` or its external module | `DepCensus.lean` |
| `used.txt` | the used counted declarations of the primary closure, with their modules | `DepCensus.lean` |
| `modules.tsv` | per module: directory, counted declarations, used, source lines, lines covered | `DepCensus.lean` |
| `directories.tsv` | the same per directory, with the number of modules and of modules with a used declaration | `DepCensus.lean` |
| `unused-modules.txt` | modules with no used declaration | `DepCensus.lean` |
| `import-only.txt` | unused modules in the import closure of a module with a used declaration | `DepCensus.lean` |
| `headlines.tsv` | every counted declaration whose docstring begins with `**`: module, used, first line of the docstring | `DepCensus.lean` |
| `spine.tsv` | the used headlines in a dependency order (postorder of a depth-first search from the targets), with directory, `dependents` (used headlines whose closure contains it) and `depends_on` | `DepCensus.lean` |
| `external.tsv` | the external constants of the primary closure: package, module, number of nodes of the closure using each | `DepCensus.lean` |
| `external-modules.tsv` | the external modules of those constants, grouped by package: constants, and the sum of their use counts | `DepCensus.lean` |
| `summary.tsv` | per target set (primary and the four comparison targets): raw closure, used declarations, modules with a used declaration, lines covered, and the library totals | `DepCensus.lean` |
| `sanity.tsv` | the checks of commission §2.4 | `DepCensus.lean` |
| `closure-check.txt` | the second computation and its comparison with the files above | `closure.py` |
| `replay.txt` | the kernel replay of the primary closure from Mathlib alone | `Replay.lean` |
| `headlines-by-paper.tsv`, `papers.tsv` | the headlines assigned to source papers (a heuristic reading of the docstrings; the column `how` says what decided) | `headlines_by_paper.py` |
| `root-files.tsv`, `unbuilt-files.txt` | the `.lean` files at the repository root (built by a `lean_lib`? number of `sorry`), and the files under `HPC/` built by no `lean_lib` | `rootfiles.sh` |
| `report-tables.md` | the tables of the report | `report_tables.py` |
