#!/usr/bin/env python3
"""Tables of the batch-203 report, generated from `doc/depcensus/`.

Run from the repository root after the census (`lake env lean scripts/DepCensus.lean`),
`python3 scripts/headlines_by_paper.py` and `bash scripts/rootfiles.sh`:

    python3 scripts/report_tables.py > doc/depcensus/report-tables.md

Every number of the tables is read from the files of `doc/depcensus/`; nothing is computed
here except sums, shares and sorting.
"""

import collections

D = "doc/depcensus/"


def tsv(name, header=True):
    rows = [l.rstrip("\n").split("\t") for l in open(D + name, encoding="utf-8") if l.strip()]
    return rows[1:] if header else rows


def pct(a, b):
    return f"{100.0 * a / b:.1f} %" if b else "–"


out = []
p = out.append

# ---------------------------------------------------------------- 1. summary
p("### Table 1. Closures\n")
p("| target | raw closure (constants) | used declarations | share | modules with a used declaration | share | lines covered | share |")
p("|---|---:|---:|---:|---:|---:|---:|---:|")
for r in tsv("summary.tsv"):
    label, raw, used, decls, mods, libmods, lines, modlines, liblines = r
    name = "**primary** (`ho16_classification_plane₄`, `ho16_classification₄`)" if label == "primary" else f"`{label}`"
    p(f"| {name} | {raw} | {used} | {pct(int(used), int(decls))} | {mods} | {pct(int(mods), int(libmods))} | {lines} | {pct(int(lines), int(liblines))} |")
r = tsv("summary.tsv")[0]
p(f"\nThe library (the four `lean_lib`s): {r[3]} counted declarations, {r[5]} modules, {r[8]} source lines.\n")

# ---------------------------------------------------------------- 2. by directory
p("### Table 2. By directory (primary closure)\n")
p("| directory | modules | with a used declaration | declarations | used | share | lines | lines covered | share |")
p("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
tot = [0] * 6
for d, mm, mu, c, u, l, ul in tsv("directories.tsv"):
    vals = list(map(int, (mm, mu, c, u, l, ul)))
    tot = [a + b for a, b in zip(tot, vals)]
    label = "root files (`HPC.lean`, `HPCExtra.lean`, `HPCArchive.lean`, `HPCCensus.lean`)" if d == "." else f"`{d}`"
    p(f"| {label} | {mm} | {mu} | {c} | {u} | {pct(vals[3], vals[2])} | {l} | {ul} | {pct(vals[5], vals[4])} |")
p(f"| **total** | {tot[0]} | {tot[1]} | {tot[2]} | {tot[3]} | {pct(tot[3], tot[2])} | {tot[4]} | {tot[5]} | {pct(tot[5], tot[4])} |\n")

# ---------------------------------------------------------------- 3. unused modules
mods = {r[0]: r for r in tsv("modules.tsv")}
unused = [l.strip() for l in open(D + "unused-modules.txt", encoding="utf-8") if l.strip()]
importonly = {l.strip() for l in open(D + "import-only.txt", encoding="utf-8") if l.strip()}
by = collections.defaultdict(list)
for m in unused:
    by[mods[m][1]].append(m)
p("### Table 3. Unused modules by directory\n")
p("| directory | unused modules | of which import-only | their declarations | their lines |")
p("|---|---:|---:|---:|---:|")
for d in sorted(by):
    ms = by[d]
    p(f"| `{d}` | {len(ms)} | {sum(1 for m in ms if m in importonly)} | "
      f"{sum(int(mods[m][2]) for m in ms)} | {sum(int(mods[m][4]) for m in ms)} |")
p(f"| **total** | {len(unused)} | {len(importonly)} | {sum(int(mods[m][2]) for m in unused)} | "
  f"{sum(int(mods[m][4]) for m in unused)} |\n")
p("Module lists (import-only modules marked †):\n")
for d in sorted(by):
    names = ", ".join(("`" + m.split(".")[-1] + "`" + ("†" if m in importonly else "")) for m in by[d])
    p(f"* `{d}`: {names}")
p("")

# ---------------------------------------------------------------- 4. partly used
p("### Table 4. Partly used modules (fewer than half of the declarations used)\n")
p("| module | used / declarations | fraction |")
p("|---|---:|---:|")
partly = [(m, int(r[2]), int(r[3])) for m, r in mods.items() if int(r[3]) > 0 and 2 * int(r[3]) < int(r[2])]
for m, c, u in sorted(partly):
    p(f"| `{m}` | {u} / {c} | {pct(u, c)} |")
p(f"\n{len(partly)} modules.\n")

# ---------------------------------------------------------------- 5. papers
p("### Table 5. Headlines by source paper\n")
p("| paper | headlines | used | numbered theorems named in used headlines | numbered theorems named only in unused headlines |")
p("|---|---:|---:|---|---|")
for paper, n, u, tu, tn in [r + [""] * (5 - len(r)) for r in tsv("papers.tsv")]:
    p(f"| {paper} | {n} | {u} | {tu} | {tn} |")
p("")

# ---------------------------------------------------------------- 6. spine
spine = tsv("spine.tsv")
bydir = collections.defaultdict(list)
for r in spine:
    bydir[r[3]].append(r)
p("### Table 6. The spine: used headlines per directory, and the ten most depended upon\n")
p("The number before each name is the number of used headlines whose closure contains it.\n")
for d in sorted(bydir):
    rs = sorted(bydir[d], key=lambda r: (-int(r[4]), int(r[0])))
    p(f"* **`{d}`** — {len(rs)} used headlines:")
    for r in rs[:10]:
        doc = r[6]
        if len(doc) > 110:
            doc = doc[:107] + "…"
        p(f"  * {r[4]} — `{r[1]}`: {doc}")
p("")
print("\n".join(out))
