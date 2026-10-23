"""Census for batch 17 — how often the cap in hStar binds, and what the
non-vacuous ("open") basepoints look like.

Exploratory computation, in the down form `IsCrookedSeq`.  Not a Lean-checked
claim; recorded as evidence for `HighExitValleyOpen`, exactly as the corpus
figures of earlier batches are.

Usage: python3 census-batch17.py [maxlen] [levels]

Reported per run:
  * basepoints examined (those with L + 3 <= H, L/H the sequence min/max);
  * basepoints where the cap binds, i.e. hStar = max(H-1, p) — there the valley
    clause is vacuous (`valleyBefore_of_cap`);
  * open basepoints, hStar < max(H-1, p) — the non-vacuous core;
  * for open basepoints: whether the demands and p are all < H-1
    (`demands_lt_of_open`);
  * arm-instances with bite: (arm, s) admissible for HighExitValley at which
    some index actually exceeds hStar + 1, with shape
    (hStar - p, H - 1 - hStar, L - (p - 2));
  * failures of HighExitValley / HighExitValleyOpen (expected: none).
"""

import sys
from itertools import product


def crooked(f):
    n = len(f)
    for s in range(n):
        for t in range(s + 1, n):
            if abs(f[t] - f[s]) >= 3:
                ok = False
                for r in range(s + 1, t):
                    for r2 in range(r + 1, t):
                        c = True
                        if f[s] < f[t]:
                            c = (f[t] - 2 <= f[r] <= f[t] - 1) and (f[s] <= f[r2] <= f[s] + 1)
                        if c and f[t] < f[s]:
                            c = (f[t] <= f[r] <= f[t] + 1) and (f[s] - 2 <= f[r2] <= f[s] - 1)
                        if c:
                            ok = True
                            break
                    if ok:
                        break
                if not ok:
                    return False
    return True


def phases(A):
    n = len(A)
    ph = [0] * n
    cur = 0
    for j in range(n):
        if j > 0 and A[j] <= A[j - 1]:
            cur = 1
        ph[j] = cur
    return ph


def hStarArm(A, p):
    best = None
    for j in range(len(A)):
        if all(A[jp] >= p - 1 for jp in range(j + 1)):
            v = A[j]
            if best is None or v > best:
                best = v
    return best


def valleyBefore(A, L, h, s):
    n = len(A)
    for u in range(s, n):
        if A[u] > h + 1:
            if not any(A[j] <= L + 1 for j in range(s, u)):
                return False
    return True


def has_bite(A, h, s):
    return any(A[u] > h + 1 for u in range(s, len(A)))


def checkseq(f, stats, report):
    n = len(f)
    H = max(f)
    L = min(f)
    if L + 3 > H:
        return
    for i in range(n):
        p = f[i]
        G = f[i:]
        T = f[i::-1]
        hG = hStarArm(G, p)
        hT = hStarArm(T, p)
        hStar = min(max(max(hG, hT), max(p, L + 1)), max(H - 1, p))
        stats['basepoints'] += 1
        if hStar >= max(H - 1, p):
            stats['capped'] += 1
        else:
            stats['open'] += 1
            if not (hG < H - 1 and hT < H - 1 and p < H - 1):
                report.setdefault('demands_lt_of_open', []).append((f, i))
        for A in (G, T):
            ph = phases(A)
            for s in range(len(A) + 1):
                if all(A[j] + ph[j] < hStar for j in range(s)):
                    if has_bite(A, hStar, s):
                        stats['bite'] += 1
                        shape = (hStar - p, H - 1 - hStar, L - (p - 2))
                        stats.setdefault('shapes', {})
                        stats['shapes'][shape] = stats['shapes'].get(shape, 0) + 1
                    if not valleyBefore(A, L, hStar, s):
                        report.setdefault('HighExitValley', []).append((f, i, s))


def gen(n, levels):
    for start in range(levels):
        stack = [[start]]
        while stack:
            cur = stack.pop()
            if len(cur) == n:
                yield cur
            else:
                for d in (-1, 0, 1):
                    v = cur[-1] + d
                    if 0 <= v < levels:
                        stack.append(cur + [v])


stats = {'basepoints': 0, 'capped': 0, 'open': 0, 'bite': 0}
report = {}
maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 11
levels = int(sys.argv[2]) if len(sys.argv) > 2 else 6
total = 0
for n in range(4, maxn + 1):
    c = 0
    for f in gen(n, levels):
        if crooked(f):
            c += 1
            checkseq(f, stats, report)
    total += c
    print("len", n, "crooked", c, "stats",
          {k: v for k, v in stats.items() if k != 'shapes'}, flush=True)
print("total crooked", total)
print("basepoints", stats['basepoints'], "capped", stats['capped'], "open", stats['open'])
print("arm-instances with bite", stats['bite'])
print("shapes (hStar-p, H-1-hStar, L-(p-2)):",
      sorted(stats.get('shapes', {}).items(), key=lambda kv: -kv[1]))
for k, v in report.items():
    print(k, "failures", len(v), v[:3])
if not report:
    print("no failures")
