#!/usr/bin/env python3
"""Second computation of the dependency census (batch 203).

Run from the repository root, after `lake env lean scripts/DepCensus.lean`:

    python3 scripts/closure.py

Reads `doc/depcensus/nodes.tsv`, `doc/depcensus/edges.tsv` and
`doc/depcensus/edges-external.tsv` only (no Lean), and recomputes independently

* the raw closure of the primary targets (breadth-first search) and the used declarations
  (the rule of commission section 2.2), compared with `doc/depcensus/used.txt`;
* the per-module counts of `doc/depcensus/modules.tsv`: declarations, used declarations,
  source lines (counted here from the files) and covered lines (the union of the ranges of the
  used declarations, each extended upwards over its docstring by a scan of the file made here);
* the counts of `doc/depcensus/external.tsv`;
* the rows of `doc/depcensus/summary.tsv` (primary and comparison targets);
* the dependents counts of `doc/depcensus/spine.tsv`;

and prints (without comparison) the used declarations of the primary closure that the atomic
form `ho16_classification_atomic'` does not use, by module.

Prints agreement or every difference, and writes the same text to
`doc/depcensus/closure-check.txt`.
"""

import collections
import csv
import sys

D = "doc/depcensus/"
PRIMARY = ["HPC.BJ59.ho16_classification_plane₄", "HPC.BJ59.ho16_classification₄"]
COMPARISON = ["HPC.BJ59.ho16_classification_atomic'", "HPC.BJ59.bjThm10",
              "HPC.BJ59.bjPlaneExample", "HPC.Plane.isPseudoArc_plane"]

out_lines = []


def say(s=""):
    print(s)
    out_lines.append(s)


def read_tsv(path, header=True):
    with open(path, encoding="utf-8", newline="") as f:
        rows = [line.rstrip("\n").split("\t") for line in f if line.strip("\n") != ""]
    return rows[1:] if header else rows


# ---------------------------------------------------------------- input
nodes = {}
for r in read_tsv(D + "nodes.tsv"):
    name, user, module, kind, decl, counted, start, end, docstart, headline = r
    nodes[name] = dict(user=user, module=module, kind=kind, decl=decl,
                       counted=counted == "1", start=int(start), end=int(end),
                       headline=headline == "1")
edges = collections.defaultdict(list)
for s, t in read_tsv(D + "edges.tsv"):
    edges[s].append(t)
ext_edges = collections.defaultdict(list)
ext_info = {}
for s, t, pkg, mod in read_tsv(D + "edges-external.tsv"):
    ext_edges[s].append(t)
    ext_info[t] = (pkg, mod)

modules = sorted({n["module"] for n in nodes.values()})
# modules of modules.tsv (a module with no constant, such as a root file, has no node)
modules_tsv = {r[0]: r for r in read_tsv(D + "modules.tsv")}
all_modules = sorted(set(modules) | set(modules_tsv))


def module_file(m):
    return m.replace(".", "/") + ".lean"


file_lines = {}
for m in all_modules:
    with open(module_file(m), encoding="utf-8") as f:
        text = f.read()
    ls = text.split("\n")
    if ls and ls[-1] == "":
        ls = ls[:-1]
    file_lines[m] = ls


# ---------------------------------------------------------------- closure and used
def closure(targets):
    seen = set(targets)
    queue = collections.deque(targets)
    while queue:
        c = queue.popleft()
        for d in edges.get(c, []) + ext_edges.get(c, []):
            if d not in seen:
                seen.add(d)
                queue.append(d)
    return seen


def used_of(raw):
    used = set()
    for c in raw:
        n = nodes.get(c)
        if n is None:
            continue
        if n["counted"]:
            used.add(c)
        elif n["kind"] in ("constructor", "projection"):
            d = nodes.get(n["decl"])
            if d is not None and d["counted"]:
                used.add(n["decl"])
    return used


def doc_start(m, start):
    """Extend a range upwards over its docstring, scanning the file."""
    ls = file_lines[m]

    def line(i):
        return ls[i - 1].strip() if 1 <= i <= len(ls) else ""

    if start <= 0 or line(start).startswith("/--"):
        return start
    i = start - 1
    while i > 0 and (line(i).startswith("@[") or line(i) == ""):
        i -= 1
    if i == 0 or not line(i).endswith("-/"):
        return start
    # the line that opens the comment closed on line i: the first line upwards containing "/-"
    j = i
    while j > 0 and "/-" not in line(j):
        j -= 1
    return j if j > 0 and line(j).startswith("/--") else start


def union_length(ranges):
    total = 0
    cur = None
    for a, b in sorted(ranges):
        if cur is None:
            cur = [a, b]
        elif a <= cur[1] + 1:
            cur[1] = max(cur[1], b)
        else:
            total += cur[1] - cur[0] + 1
            cur = [a, b]
    if cur is not None:
        total += cur[1] - cur[0] + 1
    return total


def module_stats(used):
    cnt = collections.Counter()
    ucnt = collections.Counter()
    rngs = collections.defaultdict(list)
    for name, n in nodes.items():
        if n["counted"]:
            cnt[n["module"]] += 1
            if name in used:
                ucnt[n["module"]] += 1
                rngs[n["module"]].append((doc_start(n["module"], n["start"]), n["end"]))
    return {m: (cnt[m], ucnt[m], len(file_lines[m]), union_length(rngs[m])) for m in all_modules}


differences = 0


def diff(label, a, b):
    global differences
    if a != b:
        differences += 1
        say(f"DIFFERENCE {label}: census {a!r}, here {b!r}")


raw = closure(PRIMARY)
used = used_of(raw)
say(f"raw closure: {len(raw)} constants; used declarations: {len(used)}")

census_closure = {r[0] for r in read_tsv(D + "closure.tsv", header=False)}
diff("raw closure size", len(census_closure), len(raw))
for c in sorted(census_closure - raw):
    diff("closure member", c, None)
for c in sorted(raw - census_closure):
    diff("closure member", None, c)

census_used = {r[0]: r[1] for r in read_tsv(D + "used.txt", header=False)}
diff("used.txt size", len(census_used), len(used))
for c in sorted(set(census_used) - used):
    diff("used declaration", c, None)
for c in sorted(used - set(census_used)):
    diff("used declaration", None, c)
for c in sorted(set(census_used) & used):
    diff(f"module of {c}", census_used[c], nodes[c]["module"])

# ---------------------------------------------------------------- modules.tsv
stats = module_stats(used)
diff("modules.tsv rows", sorted(modules_tsv), all_modules)
for m in all_modules:
    r = modules_tsv.get(m)
    if r is None:
        continue
    mine = stats[m]
    theirs = (int(r[2]), int(r[3]), int(r[4]), int(r[5]))
    names = ("declarations", "used", "lines", "used_lines")
    for k in range(4):
        diff(f"{m} {names[k]}", theirs[k], mine[k])
say(f"modules: {len(all_modules)}; with a used declaration: "
    f"{sum(1 for m in all_modules if stats[m][1] > 0)}")

# ---------------------------------------------------------------- external.tsv
ext_users = collections.Counter()
for c in raw:
    if c in nodes:
        for t in set(ext_edges.get(c, [])):
            ext_users[t] += 1
census_ext = {r[0]: (r[1], r[2], int(r[3])) for r in read_tsv(D + "external.tsv")}
diff("external.tsv size", len(census_ext), len(ext_users))
for t in sorted(set(census_ext) | set(ext_users)):
    a = census_ext.get(t)
    b = (ext_info[t][0], ext_info[t][1], ext_users[t]) if t in ext_users else None
    diff(f"external {t}", a, b)
say(f"external constants: {len(ext_users)}")

# ---------------------------------------------------------------- summary.tsv
total_decls = sum(1 for n in nodes.values() if n["counted"])
total_lines = sum(len(file_lines[m]) for m in all_modules)
census_summary = {r[0]: r for r in read_tsv(D + "summary.tsv")}
for label, targets in [("primary", PRIMARY)] + [(t, [t]) for t in COMPARISON]:
    raw_t = closure(targets)
    used_t = used_of(raw_t)
    st = module_stats(used_t)
    mods = [m for m in all_modules if st[m][1] > 0]
    mine = [label, str(len(raw_t)), str(len(used_t)), str(total_decls), str(len(mods)),
            str(len(all_modules)), str(sum(st[m][3] for m in all_modules)),
            str(sum(st[m][2] for m in mods)), str(total_lines)]
    diff(f"summary row {label}", census_summary.get(label), mine)
    say("summary\t" + "\t".join(mine))

# ---------------------------------------------------------------- primary against the atomic form
used_atomic = used_of(closure(["HPC.BJ59.ho16_classification_atomic'"]))
say(f"atomic form: {len(used_atomic)} used declarations; also used by the primary closure: "
    f"{len(used_atomic & used)}; used by the primary closure only: {len(used - used_atomic)}")
only = collections.Counter(nodes[c]["module"] for c in used - used_atomic)
say("used by the primary closure only, by module: " +
    ", ".join(f"{m} {k}" for m, k in only.most_common()))

# ---------------------------------------------------------------- spine.tsv
spine = read_tsv(D + "spine.tsv")
user_to_name = {n["user"]: k for k, n in nodes.items() if n["headline"]}
spine_names = [user_to_name[r[1]] for r in spine]
used_headlines = {c for c in used if nodes[c]["headline"]}
diff("spine members", sorted(used_headlines), sorted(spine_names))
# the order is a dependency order: nothing depends on a later headline
position = {c: i for i, c in enumerate(spine_names)}
dependents = collections.Counter()
order_ok = True
for h in spine_names:
    cl = closure([h])
    for b in spine_names:
        if b != h and b in cl:
            dependents[b] += 1
            if position[b] > position[h]:
                order_ok = False
say(f"spine: {len(spine_names)} used headlines; dependency order respected: {order_ok}")
if not order_ok:
    differences += 1
for r, h in zip(spine, spine_names):
    diff(f"dependents of {h}", int(r[4]), dependents[h])

say(f"differences: {differences}")
with open(D + "closure-check.txt", "w", encoding="utf-8") as f:
    f.write("\n".join(out_lines) + "\n")
sys.exit(0 if differences == 0 else 1)
