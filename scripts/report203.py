#!/usr/bin/env python3
"""Fill `scripts/report203-template.md` with the generated tables and check outputs.

Run from the repository root after the steps of `doc/depcensus/README.md`, with the regenerated
audit in `/tmp/axioms203.txt`:

    python3 scripts/report203.py > doc/batches/REPORT-batch203.md
"""
import re

D = "doc/depcensus/"
tmpl = open("scripts/report203-template.md", encoding="utf-8").read()
tables = open(D + "report-tables.md", encoding="utf-8").read()
parts = re.split(r"^### (Table \d+)\. .*$", tables, flags=re.M)
for i in range(1, len(parts), 2):
    tmpl = tmpl.replace("{{" + parts[i] + "}}", parts[i + 1].strip())
tmpl = tmpl.replace("{{replay}}", open(D + "replay.txt", encoding="utf-8").read().rstrip())
tmpl = tmpl.replace("{{closurecheck}}", open(D + "closure-check.txt", encoding="utf-8").read().rstrip())
rows = [l.rstrip("\n").split("\t") for l in open(D + "root-files.tsv", encoding="utf-8") if l.strip()]
rf = ["| file | built by a `lean_lib` | `sorry` |", "|---|---|---:|"]
rf += [f"| `{a}` | {b} | {c} |" for a, b, c in rows[1:]]
tmpl = tmpl.replace("{{rootfiles}}", "\n".join(rf))
n = sum(1 for _ in open("axioms.txt", encoding="utf-8"))
tmpl = tmpl.replace("{{axlines}}", str(n))
assert "{{" not in tmpl, re.findall(r"\{\{.*?\}\}", tmpl)
print(tmpl, end="")
