#!/usr/bin/env python3
"""Headline results grouped by source paper (batch 203, report section 5).

Run from the repository root, after `lake env lean scripts/DepCensus.lean`:

    python3 scripts/headlines_by_paper.py

Reads `doc/depcensus/headlines.tsv` and the module docstrings of the source files, and assigns
each headline (a counted declaration whose docstring begins with `**`) to a source paper:

1. by the first line of its own docstring, if it names a paper (first matching rule below);
2. otherwise by the first lines of its module's docstring (`/-! ... -/`);
3. otherwise by the directory (and, for Hagopian and Jones, the year in the module name).

This is a heuristic reading of the docstrings, not a computation from the environment; the
column `how` says which of the three steps decided. Writes
`doc/depcensus/headlines-by-paper.tsv` (one row per headline) and
`doc/depcensus/papers.tsv` (per paper: headlines, used, and the numbered theorems used and not
used, read from the docstrings with the pattern "Theorem <number>").
"""

import collections
import re

D = "doc/depcensus/"

# (pattern, paper); the first match wins
RULES = [
    (r"Bing[–-]Jones", "Bing–Jones 1959"),
    (r"Domokos[–-]Prajs|\bD[–-]P\b", "Domokos–Prajs 2022"),
    (r"Hoehn[–-]Oversteegen|\bH[–-]O\b", "Hoehn–Oversteegen 2016"),
    (r"Krasinkiewicz[–-]Minc|\bK[–-]M\b", "Krasinkiewicz–Minc 1977"),
    (r"Oversteegen[–-]Tymchatyn|\bO[–-]T\b", "Oversteegen–Tymchatyn 1982"),
    (r"\bCook\b", "Cook 1967"),
    (r"\bLelek\b", "Lelek 1979"),
    (r"Hagopian 1975|Hagopian's 1975", "Hagopian 1975"),
    (r"Hagopian 1976|Hagopian's 1976|Hagopian76", "Hagopian 1976"),
    (r"Hagopian 1984", "Hagopian 1984"),
    (r"Jones 1941", "Jones 1941"),
    (r"Jones 1948", "Jones 1948"),
    (r"Jones 1949", "Jones 1949"),
    (r"Jones 1951", "Jones 1951"),
    (r"Jones 1955", "Jones 1955"),
    (r"Jones 1975", "Jones 1975"),
    (r"Mullikin", "Mullikin 1922"),
    (r"Moore 1916|F\.A\.|foundations of plane analysis situs", "Moore 1916"),
    (r"Moore 1919", "Moore 1919"),
    (r"Moore 1920", "Moore 1920"),
    (r"Moore 1922", "Moore 1922"),
    (r"Moore 1924", "Moore 1924"),
    (r"Moore 1925", "Moore 1925"),
    (r"Moore 1962|Moore's book", "Moore 1962"),
    (r"Whyburn", "Whyburn 1939/1942"),
    (r"Menger", "Menger (Kurventheorie)"),
    (r"Wilder", "Wilder 1938"),
    (r"Fugate", "Fugate 1966/1969"),
    (r"Lehner", "Lehner"),
    (r"Ingram", "Ingram 1968"),
    (r"Sorgenfrey|Nadler", "Sorgenfrey (Nadler)"),
    (r"Effros", "Effros 1965"),
    (r"Bing 1960", "Bing 1960"),
    (r"Bing 1948|arcs paper|Bing's 1948", "Bing 1948"),
    (r"Bing 1951|Bing's 1951|Snake-like continua|Concerning hereditarily indecomposable",
     "Bing 1951"),
]


def by_rules(text):
    for pat, paper in RULES:
        if re.search(pat, text):
            return paper
    return None


def by_directory(module):
    parts = module.split(".")
    d = parts[1] if len(parts) > 2 else ""
    last = parts[-1]
    if d == "Hagopian":
        if last.startswith(("H75", "Hagopian75")):
            return "Hagopian 1975"
        if last.startswith(("H76", "Hagopian76")):
            return "Hagopian 1976"
        if last.startswith(("H84", "Hagopian84")):
            return "Hagopian 1984"
        return "Hagopian"
    if d == "Jones":
        m = re.search(r"(\d\d)", last)
        if m:
            return "Jones 19" + m.group(1)
        return "Jones"
    return {
        "Fold": "Bing 1948", "PseudoArc": "Bing 1948", "Chains": "Bing 1948",
        "Covers": "Bing 1948", "Plane": "Bing 1951", "Moore": "Moore",
        "HO16": "Hoehn–Oversteegen 2016", "BJ59": "Bing–Jones 1959",
        "Span": "Oversteegen–Tymchatyn 1982", "Effros": "Effros 1965",
    }.get(d, "other")


module_doc_cache = {}


def module_doc(module):
    if module not in module_doc_cache:
        with open(module.replace(".", "/") + ".lean", encoding="utf-8") as f:
            text = f.read()
        m = re.search(r"/-!(.*?)-/", text, re.S)
        lines = []
        if m:
            lines = [l.strip() for l in m.group(1).split("\n") if l.strip()][:3]
        module_doc_cache[module] = " ".join(lines)
    return module_doc_cache[module]


rows = [l.rstrip("\n").split("\t") for l in open(D + "headlines.tsv", encoding="utf-8")][1:]
out = ["name\tmodule\tused\tpaper\thow\tdocstring_first_line"]
papers = collections.defaultdict(lambda: {"n": 0, "used": 0, "thm_used": set(), "thm_unused": set()})
for name, module, used, first in rows:
    paper = by_rules(first)
    how = "docstring"
    if paper is None:
        paper = by_rules(module_doc(module))
        how = "module docstring"
    if paper is None:
        paper = by_directory(module)
        how = "directory"
    out.append("\t".join([name, module, used, paper, how, first]))
    p = papers[paper]
    p["n"] += 1
    p["used"] += used == "1"
    for t in re.findall(r"Theorem\s+(\d+[A-Za-z]?)", first):
        (p["thm_used"] if used == "1" else p["thm_unused"]).add(t)

with open(D + "headlines-by-paper.tsv", "w", encoding="utf-8") as f:
    f.write("\n".join(out) + "\n")


def key(t):
    m = re.match(r"(\d+)(.*)", t)
    return (int(m.group(1)), m.group(2)) if m else (10 ** 6, t)


lines = ["paper\theadlines\tused\ttheorems_used\ttheorems_never_used"]
for paper in sorted(papers):
    p = papers[paper]
    never = p["thm_unused"] - p["thm_used"]
    lines.append("\t".join([paper, str(p["n"]), str(p["used"]),
                            " ".join(sorted(p["thm_used"], key=key)),
                            " ".join(sorted(never, key=key))]))
with open(D + "papers.tsv", "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
print("\n".join(lines))
